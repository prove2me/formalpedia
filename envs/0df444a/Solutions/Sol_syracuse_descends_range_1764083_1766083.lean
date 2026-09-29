-- Prove2me | solution 1 for syracuse_descends_range_1764083_1766083
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:40:02.925616+00:00
-- url     : https://prove2.me/submissions/9af8a532-964c-4fd5-9174-27a7cb67453c

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


theorem B1884169 : Blo 1764083 1884169 := bbase (se 2 (by rfl) ⟨706563, by rfl⟩ : syracuseStep 1884169 = 1413127) (by norm_num)
theorem B5955605 : Blo 1764083 5955605 := bbase (se 6 (by rfl) ⟨139584, by rfl⟩ : syracuseStep 5955605 = 279169) (by norm_num)
theorem B3973157 : Blo 1764083 3973157 := bbase (se 4 (by rfl) ⟨372483, by rfl⟩ : syracuseStep 3973157 = 744967) (by norm_num)
theorem B3350621 : Blo 1764083 3350621 := bbase (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) (by norm_num)
theorem B2646125 : Blo 1764083 2646125 := bbase (se 3 (by rfl) ⟨496148, by rfl⟩ : syracuseStep 2646125 = 992297) (by norm_num)
theorem B3973229 : Blo 1764083 3973229 := bbase (se 3 (by rfl) ⟨744980, by rfl⟩ : syracuseStep 3973229 = 1489961) (by norm_num)
theorem B14311541 : Blo 1764083 14311541 := bbase (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) (by norm_num)
theorem B11313269 : Blo 1764083 11313269 := bbase (se 5 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 11313269 = 1060619) (by norm_num)
theorem B2646149 : Blo 1764083 2646149 := bbase (se 4 (by rfl) ⟨248076, by rfl⟩ : syracuseStep 2646149 = 496153) (by norm_num)
theorem B2646173 : Blo 1764083 2646173 := bbase (se 3 (by rfl) ⟨496157, by rfl⟩ : syracuseStep 2646173 = 992315) (by norm_num)
theorem B2646197 : Blo 1764083 2646197 := bbase (se 5 (by rfl) ⟨124040, by rfl⟩ : syracuseStep 2646197 = 248081) (by norm_num)
theorem B5652661 : Blo 1764083 5652661 := bbase (se 5 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 5652661 = 529937) (by norm_num)
theorem B3973301 : Blo 1764083 3973301 := bbase (se 5 (by rfl) ⟨186248, by rfl⟩ : syracuseStep 3973301 = 372497) (by norm_num)
theorem B2646221 : Blo 1764083 2646221 := bbase (se 3 (by rfl) ⟨496166, by rfl⟩ : syracuseStep 2646221 = 992333) (by norm_num)
theorem B2646245 : Blo 1764083 2646245 := bbase (se 4 (by rfl) ⟨248085, by rfl⟩ : syracuseStep 2646245 = 496171) (by norm_num)
theorem B8937701 : Blo 1764083 8937701 := bbase (se 4 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 8937701 = 1675819) (by norm_num)
theorem B2826485 : Blo 1764083 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B2646269 : Blo 1764083 2646269 := bbase (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) (by norm_num)
theorem B3973373 : Blo 1764083 3973373 := bbase (se 3 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 3973373 = 1490015) (by norm_num)
theorem B2646293 : Blo 1764083 2646293 := bbase (se 6 (by rfl) ⟨62022, by rfl⟩ : syracuseStep 2646293 = 124045) (by norm_num)
theorem B2646317 : Blo 1764083 2646317 := bbase (se 3 (by rfl) ⟨496184, by rfl⟩ : syracuseStep 2646317 = 992369) (by norm_num)
theorem B13402421 : Blo 1764083 13402421 := bbase (se 5 (by rfl) ⟨628238, by rfl⟩ : syracuseStep 13402421 = 1256477) (by norm_num)
theorem B2646341 : Blo 1764083 2646341 := bbase (se 4 (by rfl) ⟨248094, by rfl⟩ : syracuseStep 2646341 = 496189) (by norm_num)
theorem B3973445 : Blo 1764083 3973445 := bbase (se 4 (by rfl) ⟨372510, by rfl⟩ : syracuseStep 3973445 = 745021) (by norm_num)
theorem B2646365 : Blo 1764083 2646365 := bbase (se 3 (by rfl) ⟨496193, by rfl⟩ : syracuseStep 2646365 = 992387) (by norm_num)
theorem B2646389 : Blo 1764083 2646389 := bbase (se 5 (by rfl) ⟨124049, by rfl⟩ : syracuseStep 2646389 = 248099) (by norm_num)
theorem B1884541 : Blo 1764083 1884541 := bbase (se 3 (by rfl) ⟨353351, by rfl⟩ : syracuseStep 1884541 = 706703) (by norm_num)
theorem B3350909 : Blo 1764083 3350909 := bbase (se 3 (by rfl) ⟨628295, by rfl⟩ : syracuseStep 3350909 = 1256591) (by norm_num)
theorem B2646413 : Blo 1764083 2646413 := bbase (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) (by norm_num)
theorem B3973517 : Blo 1764083 3973517 := bbase (se 3 (by rfl) ⟨745034, by rfl⟩ : syracuseStep 3973517 = 1490069) (by norm_num)
theorem B2548117 : Blo 1764083 2548117 := bbase (se 6 (by rfl) ⟨59721, by rfl⟩ : syracuseStep 2548117 = 119443) (by norm_num)
theorem B2646437 : Blo 1764083 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B5652917 : Blo 1764083 5652917 := bbase (se 5 (by rfl) ⟨264980, by rfl⟩ : syracuseStep 5652917 = 529961) (by norm_num)
theorem B2826677 : Blo 1764083 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B10887605 : Blo 1764083 10887605 := bbase (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) (by norm_num)
theorem B2646461 : Blo 1764083 2646461 := bbase (se 3 (by rfl) ⟨496211, by rfl⟩ : syracuseStep 2646461 = 992423) (by norm_num)
theorem B5956037 : Blo 1764083 5956037 := bbase (se 4 (by rfl) ⟨558378, by rfl⟩ : syracuseStep 5956037 = 1116757) (by norm_num)
theorem B2646485 : Blo 1764083 2646485 := bbase (se 7 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 2646485 = 62027) (by norm_num)
theorem B3973589 : Blo 1764083 3973589 := bbase (se 7 (by rfl) ⟨46565, by rfl⟩ : syracuseStep 3973589 = 93131) (by norm_num)
theorem B8479205 : Blo 1764083 8479205 := bbase (se 4 (by rfl) ⟨794925, by rfl⟩ : syracuseStep 8479205 = 1589851) (by norm_num)
theorem B5366245 : Blo 1764083 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B2646509 : Blo 1764083 2646509 := bbase (se 3 (by rfl) ⟨496220, by rfl⟩ : syracuseStep 2646509 = 992441) (by norm_num)
theorem B2646533 : Blo 1764083 2646533 := bbase (se 4 (by rfl) ⟨248112, by rfl⟩ : syracuseStep 2646533 = 496225) (by norm_num)
theorem B3351061 : Blo 1764083 3351061 := bbase (se 6 (by rfl) ⟨78540, by rfl⟩ : syracuseStep 3351061 = 157081) (by norm_num)
theorem B2646557 : Blo 1764083 2646557 := bbase (se 3 (by rfl) ⟨496229, by rfl⟩ : syracuseStep 2646557 = 992459) (by norm_num)
theorem B3973661 : Blo 1764083 3973661 := bbase (se 3 (by rfl) ⟨745061, by rfl⟩ : syracuseStep 3973661 = 1490123) (by norm_num)
theorem B2646581 : Blo 1764083 2646581 := bbase (se 5 (by rfl) ⟨124058, by rfl⟩ : syracuseStep 2646581 = 248117) (by norm_num)
theorem B2646605 : Blo 1764083 2646605 := bbase (se 3 (by rfl) ⟨496238, by rfl⟩ : syracuseStep 2646605 = 992477) (by norm_num)
theorem B2646629 : Blo 1764083 2646629 := bbase (se 4 (by rfl) ⟨248121, by rfl⟩ : syracuseStep 2646629 = 496243) (by norm_num)
theorem B2646653 : Blo 1764083 2646653 := bbase (se 3 (by rfl) ⟨496247, by rfl⟩ : syracuseStep 2646653 = 992495) (by norm_num)
theorem B2646677 : Blo 1764083 2646677 := bbase (se 6 (by rfl) ⟨62031, by rfl⟩ : syracuseStep 2646677 = 124063) (by norm_num)
theorem B13591189 : Blo 1764083 13591189 := bbase (se 6 (by rfl) ⟨318543, by rfl⟩ : syracuseStep 13591189 = 637087) (by norm_num)
theorem B2646701 : Blo 1764083 2646701 := bbase (se 3 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 2646701 = 992513) (by norm_num)
theorem B3769021 : Blo 1764083 3769021 := bbase (se 3 (by rfl) ⟨706691, by rfl⟩ : syracuseStep 3769021 = 1413383) (by norm_num)
theorem B2646725 : Blo 1764083 2646725 := bbase (se 4 (by rfl) ⟨248130, by rfl⟩ : syracuseStep 2646725 = 496261) (by norm_num)
theorem B2646749 : Blo 1764083 2646749 := bbase (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) (by norm_num)
theorem B2646773 : Blo 1764083 2646773 := bbase (se 5 (by rfl) ⟨124067, by rfl⟩ : syracuseStep 2646773 = 248135) (by norm_num)
theorem B1884917 : Blo 1764083 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B2646797 : Blo 1764083 2646797 := bbase (se 3 (by rfl) ⟨496274, by rfl⟩ : syracuseStep 2646797 = 992549) (by norm_num)
theorem B2646821 : Blo 1764083 2646821 := bbase (se 4 (by rfl) ⟨248139, by rfl⟩ : syracuseStep 2646821 = 496279) (by norm_num)
theorem B4465469 : Blo 1764083 4465469 := bbase (se 3 (by rfl) ⟨837275, by rfl⟩ : syracuseStep 4465469 = 1674551) (by norm_num)
theorem B2646845 : Blo 1764083 2646845 := bbase (se 3 (by rfl) ⟨496283, by rfl⟩ : syracuseStep 2646845 = 992567) (by norm_num)
theorem B1884989 : Blo 1764083 1884989 := bbase (se 3 (by rfl) ⟨353435, by rfl⟩ : syracuseStep 1884989 = 706871) (by norm_num)
theorem B3351365 : Blo 1764083 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B2646869 : Blo 1764083 2646869 := bbase (se 9 (by rfl) ⟨7754, by rfl⟩ : syracuseStep 2646869 = 15509) (by norm_num)
theorem B2646893 : Blo 1764083 2646893 := bbase (se 3 (by rfl) ⟨496292, by rfl⟩ : syracuseStep 2646893 = 992585) (by norm_num)
theorem B5956469 : Blo 1764083 5956469 := bbase (se 5 (by rfl) ⟨279209, by rfl⟩ : syracuseStep 5956469 = 558419) (by norm_num)
theorem B2646917 : Blo 1764083 2646917 := bbase (se 4 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 2646917 = 496297) (by norm_num)
theorem B2646941 : Blo 1764083 2646941 := bbase (se 3 (by rfl) ⟨496301, by rfl⟩ : syracuseStep 2646941 = 992603) (by norm_num)
theorem B2646965 : Blo 1764083 2646965 := bbase (se 5 (by rfl) ⟨124076, by rfl⟩ : syracuseStep 2646965 = 248153) (by norm_num)
theorem B2646989 : Blo 1764083 2646989 := bbase (se 3 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 2646989 = 992621) (by norm_num)
theorem B14320597 : Blo 1764083 14320597 := bbase (se 7 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 14320597 = 335639) (by norm_num)
theorem B2647013 : Blo 1764083 2647013 := bbase (se 4 (by rfl) ⟨248157, by rfl⟩ : syracuseStep 2647013 = 496315) (by norm_num)
theorem B1885177 : Blo 1764083 1885177 := bbase (se 2 (by rfl) ⟨706941, by rfl⟩ : syracuseStep 1885177 = 1413883) (by norm_num)
theorem B2647037 : Blo 1764083 2647037 := bbase (se 3 (by rfl) ⟨496319, by rfl⟩ : syracuseStep 2647037 = 992639) (by norm_num)
theorem B2647061 : Blo 1764083 2647061 := bbase (se 6 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 2647061 = 124081) (by norm_num)
theorem B2647085 : Blo 1764083 2647085 := bbase (se 3 (by rfl) ⟨496328, by rfl⟩ : syracuseStep 2647085 = 992657) (by norm_num)
theorem B2647109 : Blo 1764083 2647109 := bbase (se 4 (by rfl) ⟨248166, by rfl⟩ : syracuseStep 2647109 = 496333) (by norm_num)
theorem B2647133 : Blo 1764083 2647133 := bbase (se 3 (by rfl) ⟨496337, by rfl⟩ : syracuseStep 2647133 = 992675) (by norm_num)
theorem B2647157 : Blo 1764083 2647157 := bbase (se 5 (by rfl) ⟨124085, by rfl⟩ : syracuseStep 2647157 = 248171) (by norm_num)
theorem B2647181 : Blo 1764083 2647181 := bbase (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) (by norm_num)
theorem B4023445 : Blo 1764083 4023445 := bbase (se 6 (by rfl) ⟨94299, by rfl⟩ : syracuseStep 4023445 = 188599) (by norm_num)
theorem B4465813 : Blo 1764083 4465813 := bbase (se 6 (by rfl) ⟨104667, by rfl⟩ : syracuseStep 4465813 = 209335) (by norm_num)
theorem B15082645 : Blo 1764083 15082645 := bbase (se 6 (by rfl) ⟨353499, by rfl⟩ : syracuseStep 15082645 = 706999) (by norm_num)
theorem B2647205 : Blo 1764083 2647205 := bbase (se 4 (by rfl) ⟨248175, by rfl⟩ : syracuseStep 2647205 = 496351) (by norm_num)
theorem B3769517 : Blo 1764083 3769517 := bbase (se 3 (by rfl) ⟨706784, by rfl⟩ : syracuseStep 3769517 = 1413569) (by norm_num)
theorem B1885361 : Blo 1764083 1885361 := bbase (se 2 (by rfl) ⟨707010, by rfl⟩ : syracuseStep 1885361 = 1414021) (by norm_num)
theorem B2647229 : Blo 1764083 2647229 := bbase (se 3 (by rfl) ⟨496355, by rfl⟩ : syracuseStep 2647229 = 992711) (by norm_num)
theorem B2647253 : Blo 1764083 2647253 := bbase (se 7 (by rfl) ⟨31022, by rfl⟩ : syracuseStep 2647253 = 62045) (by norm_num)
theorem B2647277 : Blo 1764083 2647277 := bbase (se 3 (by rfl) ⟨496364, by rfl⟩ : syracuseStep 2647277 = 992729) (by norm_num)
theorem B4465925 : Blo 1764083 4465925 := bbase (se 4 (by rfl) ⟨418680, by rfl⟩ : syracuseStep 4465925 = 837361) (by norm_num)
theorem B2647301 : Blo 1764083 2647301 := bbase (se 4 (by rfl) ⟨248184, by rfl⟩ : syracuseStep 2647301 = 496369) (by norm_num)
theorem B2647325 : Blo 1764083 2647325 := bbase (se 3 (by rfl) ⟨496373, by rfl⟩ : syracuseStep 2647325 = 992747) (by norm_num)
theorem B5956901 : Blo 1764083 5956901 := bbase (se 4 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 5956901 = 1116919) (by norm_num)
theorem B2647349 : Blo 1764083 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B2647373 : Blo 1764083 2647373 := bbase (se 3 (by rfl) ⟨496382, by rfl⟩ : syracuseStep 2647373 = 992765) (by norm_num)
theorem B2647397 : Blo 1764083 2647397 := bbase (se 4 (by rfl) ⟨248193, by rfl⟩ : syracuseStep 2647397 = 496387) (by norm_num)
theorem B2647421 : Blo 1764083 2647421 := bbase (se 3 (by rfl) ⟨496391, by rfl⟩ : syracuseStep 2647421 = 992783) (by norm_num)
theorem B2385301 : Blo 1764083 2385301 := bbase (se 6 (by rfl) ⟨55905, by rfl⟩ : syracuseStep 2385301 = 111811) (by norm_num)
theorem B2647445 : Blo 1764083 2647445 := bbase (se 6 (by rfl) ⟨62049, by rfl⟩ : syracuseStep 2647445 = 124099) (by norm_num)
theorem B2647469 : Blo 1764083 2647469 := bbase (se 3 (by rfl) ⟨496400, by rfl⟩ : syracuseStep 2647469 = 992801) (by norm_num)
theorem B4466117 : Blo 1764083 4466117 := bbase (se 4 (by rfl) ⟨418698, by rfl⟩ : syracuseStep 4466117 = 837397) (by norm_num)
theorem B2647493 : Blo 1764083 2647493 := bbase (se 4 (by rfl) ⟨248202, by rfl⟩ : syracuseStep 2647493 = 496405) (by norm_num)
theorem B6702533 : Blo 1764083 6702533 := bbase (se 4 (by rfl) ⟨628362, by rfl⟩ : syracuseStep 6702533 = 1256725) (by norm_num)
theorem B2647517 : Blo 1764083 2647517 := bbase (se 3 (by rfl) ⟨496409, by rfl⟩ : syracuseStep 2647517 = 992819) (by norm_num)
theorem B2647541 : Blo 1764083 2647541 := bbase (se 5 (by rfl) ⟨124103, by rfl⟩ : syracuseStep 2647541 = 248207) (by norm_num)
theorem B8938997 : Blo 1764083 8938997 := bbase (se 5 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 8938997 = 838031) (by norm_num)
theorem B3311101 : Blo 1764083 3311101 := bbase (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) (by norm_num)
theorem B2647565 : Blo 1764083 2647565 := bbase (se 3 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 2647565 = 992837) (by norm_num)
theorem B2647589 : Blo 1764083 2647589 := bbase (se 4 (by rfl) ⟨248211, by rfl⟩ : syracuseStep 2647589 = 496423) (by norm_num)
theorem B3352117 : Blo 1764083 3352117 := bbase (se 5 (by rfl) ⟨157130, by rfl⟩ : syracuseStep 3352117 = 314261) (by norm_num)
theorem B2647613 : Blo 1764083 2647613 := bbase (se 3 (by rfl) ⟨496427, by rfl⟩ : syracuseStep 2647613 = 992855) (by norm_num)
theorem B2647637 : Blo 1764083 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B4769381 : Blo 1764083 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B2385517 : Blo 1764083 2385517 := bbase (se 3 (by rfl) ⟨447284, by rfl⟩ : syracuseStep 2385517 = 894569) (by norm_num)
theorem B2647661 : Blo 1764083 2647661 := bbase (se 3 (by rfl) ⟨496436, by rfl⟩ : syracuseStep 2647661 = 992873) (by norm_num)
theorem B2647685 : Blo 1764083 2647685 := bbase (se 4 (by rfl) ⟨248220, by rfl⟩ : syracuseStep 2647685 = 496441) (by norm_num)
theorem B2647709 : Blo 1764083 2647709 := bbase (se 3 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 2647709 = 992891) (by norm_num)
theorem B2647733 : Blo 1764083 2647733 := bbase (se 5 (by rfl) ⟨124112, by rfl⟩ : syracuseStep 2647733 = 248225) (by norm_num)
theorem B3352261 : Blo 1764083 3352261 := bbase (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) (by norm_num)
theorem B2647757 : Blo 1764083 2647757 := bbase (se 3 (by rfl) ⟨496454, by rfl⟩ : syracuseStep 2647757 = 992909) (by norm_num)
theorem B5957333 : Blo 1764083 5957333 := bbase (se 7 (by rfl) ⟨69812, by rfl⟩ : syracuseStep 5957333 = 139625) (by norm_num)
theorem B20113109 : Blo 1764083 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B2647781 : Blo 1764083 2647781 := bbase (se 4 (by rfl) ⟨248229, by rfl⟩ : syracuseStep 2647781 = 496459) (by norm_num)
theorem B6702821 : Blo 1764083 6702821 := bbase (se 4 (by rfl) ⟨628389, by rfl⟩ : syracuseStep 6702821 = 1256779) (by norm_num)
theorem B2647805 : Blo 1764083 2647805 := bbase (se 3 (by rfl) ⟨496463, by rfl⟩ : syracuseStep 2647805 = 992927) (by norm_num)
theorem B7538453 : Blo 1764083 7538453 := bbase (se 6 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 7538453 = 353365) (by norm_num)
theorem B2647829 : Blo 1764083 2647829 := bbase (se 6 (by rfl) ⟨62058, by rfl⟩ : syracuseStep 2647829 = 124117) (by norm_num)
theorem B4466461 : Blo 1764083 4466461 := bbase (se 3 (by rfl) ⟨837461, by rfl⟩ : syracuseStep 4466461 = 1674923) (by norm_num)
theorem B6792997 : Blo 1764083 6792997 := bbase (se 4 (by rfl) ⟨636843, by rfl⟩ : syracuseStep 6792997 = 1273687) (by norm_num)
theorem B2647853 : Blo 1764083 2647853 := bbase (se 3 (by rfl) ⟨496472, by rfl⟩ : syracuseStep 2647853 = 992945) (by norm_num)
theorem B2647877 : Blo 1764083 2647877 := bbase (se 4 (by rfl) ⟨248238, by rfl⟩ : syracuseStep 2647877 = 496477) (by norm_num)
theorem B1910621 : Blo 1764083 1910621 := bbase (se 3 (by rfl) ⟨358241, by rfl⟩ : syracuseStep 1910621 = 716483) (by norm_num)
theorem B2647901 : Blo 1764083 2647901 := bbase (se 3 (by rfl) ⟨496481, by rfl⟩ : syracuseStep 2647901 = 992963) (by norm_num)
theorem B2828125 : Blo 1764083 2828125 := bbase (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) (by norm_num)
theorem B3352421 : Blo 1764083 3352421 := bbase (se 4 (by rfl) ⟨314289, by rfl⟩ : syracuseStep 3352421 = 628579) (by norm_num)
theorem B2647925 : Blo 1764083 2647925 := bbase (se 5 (by rfl) ⟨124121, by rfl⟩ : syracuseStep 2647925 = 248243) (by norm_num)
theorem B4466573 : Blo 1764083 4466573 := bbase (se 3 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 4466573 = 1674965) (by norm_num)
theorem B2647949 : Blo 1764083 2647949 := bbase (se 3 (by rfl) ⟨496490, by rfl⟩ : syracuseStep 2647949 = 992981) (by norm_num)
theorem B8931221 : Blo 1764083 8931221 := bbase (se 6 (by rfl) ⟨209325, by rfl⟩ : syracuseStep 8931221 = 418651) (by norm_num)
theorem B2647973 : Blo 1764083 2647973 := bbase (se 4 (by rfl) ⟨248247, by rfl⟩ : syracuseStep 2647973 = 496495) (by norm_num)
theorem B2647997 : Blo 1764083 2647997 := bbase (se 3 (by rfl) ⟨496499, by rfl⟩ : syracuseStep 2647997 = 992999) (by norm_num)
theorem B19335125 : Blo 1764083 19335125 := bbase (se 7 (by rfl) ⟨226583, by rfl⟩ : syracuseStep 19335125 = 453167) (by norm_num)
theorem B2648021 : Blo 1764083 2648021 := bbase (se 7 (by rfl) ⟨31031, by rfl⟩ : syracuseStep 2648021 = 62063) (by norm_num)
theorem B2648045 : Blo 1764083 2648045 := bbase (se 3 (by rfl) ⟨496508, by rfl⟩ : syracuseStep 2648045 = 993017) (by norm_num)
theorem B3352565 : Blo 1764083 3352565 := bbase (se 5 (by rfl) ⟨157151, by rfl⟩ : syracuseStep 3352565 = 314303) (by norm_num)
theorem B2648069 : Blo 1764083 2648069 := bbase (se 4 (by rfl) ⟨248256, by rfl⟩ : syracuseStep 2648069 = 496513) (by norm_num)
theorem B3770381 : Blo 1764083 3770381 := bbase (se 3 (by rfl) ⟨706946, by rfl⟩ : syracuseStep 3770381 = 1413893) (by norm_num)
theorem B4769813 : Blo 1764083 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B2648093 : Blo 1764083 2648093 := bbase (se 3 (by rfl) ⟨496517, by rfl⟩ : syracuseStep 2648093 = 993035) (by norm_num)
theorem B2648117 : Blo 1764083 2648117 := bbase (se 5 (by rfl) ⟨124130, by rfl⟩ : syracuseStep 2648117 = 248261) (by norm_num)
theorem B2721853 : Blo 1764083 2721853 := bbase (se 3 (by rfl) ⟨510347, by rfl⟩ : syracuseStep 2721853 = 1020695) (by norm_num)
theorem B8480837 : Blo 1764083 8480837 := bbase (se 4 (by rfl) ⟨795078, by rfl⟩ : syracuseStep 8480837 = 1590157) (by norm_num)
theorem B4466765 : Blo 1764083 4466765 := bbase (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) (by norm_num)
theorem B2648141 : Blo 1764083 2648141 := bbase (se 3 (by rfl) ⟨496526, by rfl⟩ : syracuseStep 2648141 = 993053) (by norm_num)
theorem B2648165 : Blo 1764083 2648165 := bbase (se 4 (by rfl) ⟨248265, by rfl⟩ : syracuseStep 2648165 = 496531) (by norm_num)
theorem B1984621 : Blo 1764083 1984621 := bbase (se 3 (by rfl) ⟨372116, by rfl⟩ : syracuseStep 1984621 = 744233) (by norm_num)
theorem B2648189 : Blo 1764083 2648189 := bbase (se 3 (by rfl) ⟨496535, by rfl⟩ : syracuseStep 2648189 = 993071) (by norm_num)
theorem B5957765 : Blo 1764083 5957765 := bbase (se 4 (by rfl) ⟨558540, by rfl⟩ : syracuseStep 5957765 = 1117081) (by norm_num)
theorem B1984657 : Blo 1764083 1984657 := bbase (se 2 (by rfl) ⟨744246, by rfl⟩ : syracuseStep 1984657 = 1488493) (by norm_num)
theorem B2648213 : Blo 1764083 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B3770525 : Blo 1764083 3770525 := bbase (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) (by norm_num)
theorem B2418853 : Blo 1764083 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B2648237 : Blo 1764083 2648237 := bbase (se 3 (by rfl) ⟨496544, by rfl⟩ : syracuseStep 2648237 = 993089) (by norm_num)
theorem B1984693 : Blo 1764083 1984693 := bbase (se 5 (by rfl) ⟨93032, by rfl⟩ : syracuseStep 1984693 = 186065) (by norm_num)
theorem B2648261 : Blo 1764083 2648261 := bbase (se 4 (by rfl) ⟨248274, by rfl⟩ : syracuseStep 2648261 = 496549) (by norm_num)
theorem B1984729 : Blo 1764083 1984729 := bbase (se 2 (by rfl) ⟨744273, by rfl⟩ : syracuseStep 1984729 = 1488547) (by norm_num)
theorem B2648285 : Blo 1764083 2648285 := bbase (se 3 (by rfl) ⟨496553, by rfl⟩ : syracuseStep 2648285 = 993107) (by norm_num)
theorem B2648309 : Blo 1764083 2648309 := bbase (se 5 (by rfl) ⟨124139, by rfl⟩ : syracuseStep 2648309 = 248279) (by norm_num)
theorem B1984765 : Blo 1764083 1984765 := bbase (se 3 (by rfl) ⟨372143, by rfl⟩ : syracuseStep 1984765 = 744287) (by norm_num)
theorem B1788161 : Blo 1764083 1788161 := bbase (se 2 (by rfl) ⟨670560, by rfl⟩ : syracuseStep 1788161 = 1341121) (by norm_num)
theorem B2648333 : Blo 1764083 2648333 := bbase (se 3 (by rfl) ⟨496562, by rfl⟩ : syracuseStep 2648333 = 993125) (by norm_num)
theorem B1788193 : Blo 1764083 1788193 := bbase (se 2 (by rfl) ⟨670572, by rfl⟩ : syracuseStep 1788193 = 1341145) (by norm_num)
theorem B1984801 : Blo 1764083 1984801 := bbase (se 2 (by rfl) ⟨744300, by rfl⟩ : syracuseStep 1984801 = 1488601) (by norm_num)
theorem B2648357 : Blo 1764083 2648357 := bbase (se 4 (by rfl) ⟨248283, by rfl⟩ : syracuseStep 2648357 = 496567) (by norm_num)
theorem B2648381 : Blo 1764083 2648381 := bbase (se 3 (by rfl) ⟨496571, by rfl⟩ : syracuseStep 2648381 = 993143) (by norm_num)
theorem B1984837 : Blo 1764083 1984837 := bbase (se 4 (by rfl) ⟨186078, by rfl⟩ : syracuseStep 1984837 = 372157) (by norm_num)
theorem B2648405 : Blo 1764083 2648405 := bbase (se 10 (by rfl) ⟨3879, by rfl⟩ : syracuseStep 2648405 = 7759) (by norm_num)
theorem B2263393 : Blo 1764083 2263393 := bbase (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) (by norm_num)
theorem B1984873 : Blo 1764083 1984873 := bbase (se 2 (by rfl) ⟨744327, by rfl⟩ : syracuseStep 1984873 = 1488655) (by norm_num)
theorem B2648429 : Blo 1764083 2648429 := bbase (se 3 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 2648429 = 993161) (by norm_num)
theorem B2648453 : Blo 1764083 2648453 := bbase (se 4 (by rfl) ⟨248292, by rfl⟩ : syracuseStep 2648453 = 496585) (by norm_num)
theorem B1984909 : Blo 1764083 1984909 := bbase (se 3 (by rfl) ⟨372170, by rfl⟩ : syracuseStep 1984909 = 744341) (by norm_num)
theorem B2648477 : Blo 1764083 2648477 := bbase (se 3 (by rfl) ⟨496589, by rfl⟩ : syracuseStep 2648477 = 993179) (by norm_num)
theorem B4467109 : Blo 1764083 4467109 := bbase (se 4 (by rfl) ⟨418791, by rfl⟩ : syracuseStep 4467109 = 837583) (by norm_num)
theorem B1984945 : Blo 1764083 1984945 := bbase (se 2 (by rfl) ⟨744354, by rfl⟩ : syracuseStep 1984945 = 1488709) (by norm_num)
theorem B2648501 : Blo 1764083 2648501 := bbase (se 5 (by rfl) ⟨124148, by rfl⟩ : syracuseStep 2648501 = 248297) (by norm_num)
theorem B2648525 : Blo 1764083 2648525 := bbase (se 3 (by rfl) ⟨496598, by rfl⟩ : syracuseStep 2648525 = 993197) (by norm_num)
theorem B1984981 : Blo 1764083 1984981 := bbase (se 7 (by rfl) ⟨23261, by rfl⟩ : syracuseStep 1984981 = 46523) (by norm_num)
theorem B2648549 : Blo 1764083 2648549 := bbase (se 4 (by rfl) ⟨248301, by rfl⟩ : syracuseStep 2648549 = 496603) (by norm_num)
theorem B1985017 : Blo 1764083 1985017 := bbase (se 2 (by rfl) ⟨744381, by rfl⟩ : syracuseStep 1985017 = 1488763) (by norm_num)
theorem B2648573 : Blo 1764083 2648573 := bbase (se 3 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 2648573 = 993215) (by norm_num)
theorem B4467221 : Blo 1764083 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B2648597 : Blo 1764083 2648597 := bbase (se 6 (by rfl) ⟨62076, by rfl⟩ : syracuseStep 2648597 = 124153) (by norm_num)
theorem B1985053 : Blo 1764083 1985053 := bbase (se 3 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 1985053 = 744395) (by norm_num)
theorem B4770341 : Blo 1764083 4770341 := bbase (se 4 (by rfl) ⟨447219, by rfl⟩ : syracuseStep 4770341 = 894439) (by norm_num)
theorem B2648621 : Blo 1764083 2648621 := bbase (se 3 (by rfl) ⟨496616, by rfl⟩ : syracuseStep 2648621 = 993233) (by norm_num)
theorem B5958197 : Blo 1764083 5958197 := bbase (se 5 (by rfl) ⟨279290, by rfl⟩ : syracuseStep 5958197 = 558581) (by norm_num)
theorem B1985089 : Blo 1764083 1985089 := bbase (se 2 (by rfl) ⟨744408, by rfl⟩ : syracuseStep 1985089 = 1488817) (by norm_num)
theorem B2648645 : Blo 1764083 2648645 := bbase (se 4 (by rfl) ⟨248310, by rfl⟩ : syracuseStep 2648645 = 496621) (by norm_num)
theorem B3820117 : Blo 1764083 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B2648669 : Blo 1764083 2648669 := bbase (se 3 (by rfl) ⟨496625, by rfl⟩ : syracuseStep 2648669 = 993251) (by norm_num)
theorem B1985125 : Blo 1764083 1985125 := bbase (se 4 (by rfl) ⟨186105, by rfl⟩ : syracuseStep 1985125 = 372211) (by norm_num)
theorem B2648693 : Blo 1764083 2648693 := bbase (se 5 (by rfl) ⟨124157, by rfl⟩ : syracuseStep 2648693 = 248315) (by norm_num)
theorem B1985161 : Blo 1764083 1985161 := bbase (se 2 (by rfl) ⟨744435, by rfl⟩ : syracuseStep 1985161 = 1488871) (by norm_num)
theorem B2648717 : Blo 1764083 2648717 := bbase (se 3 (by rfl) ⟨496634, by rfl⟩ : syracuseStep 2648717 = 993269) (by norm_num)
theorem B5024405 : Blo 1764083 5024405 := bbase (se 6 (by rfl) ⟨117759, by rfl⟩ : syracuseStep 5024405 = 235519) (by norm_num)
theorem B2648741 : Blo 1764083 2648741 := bbase (se 4 (by rfl) ⟨248319, by rfl⟩ : syracuseStep 2648741 = 496639) (by norm_num)
theorem B1985197 : Blo 1764083 1985197 := bbase (se 3 (by rfl) ⟨372224, by rfl⟩ : syracuseStep 1985197 = 744449) (by norm_num)
theorem B2648765 : Blo 1764083 2648765 := bbase (se 3 (by rfl) ⟨496643, by rfl⟩ : syracuseStep 2648765 = 993287) (by norm_num)
theorem B1985233 : Blo 1764083 1985233 := bbase (se 2 (by rfl) ⟨744462, by rfl⟩ : syracuseStep 1985233 = 1488925) (by norm_num)
theorem B4467413 : Blo 1764083 4467413 := bbase (se 7 (by rfl) ⟨52352, by rfl⟩ : syracuseStep 4467413 = 104705) (by norm_num)
theorem B2648789 : Blo 1764083 2648789 := bbase (se 7 (by rfl) ⟨31040, by rfl⟩ : syracuseStep 2648789 = 62081) (by norm_num)
theorem B2648813 : Blo 1764083 2648813 := bbase (se 3 (by rfl) ⟨496652, by rfl⟩ : syracuseStep 2648813 = 993305) (by norm_num)
theorem B1985269 : Blo 1764083 1985269 := bbase (se 5 (by rfl) ⟨93059, by rfl⟩ : syracuseStep 1985269 = 186119) (by norm_num)
theorem B2386685 : Blo 1764083 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B2648837 : Blo 1764083 2648837 := bbase (se 4 (by rfl) ⟨248328, by rfl⟩ : syracuseStep 2648837 = 496657) (by norm_num)
theorem B8940293 : Blo 1764083 8940293 := bbase (se 4 (by rfl) ⟨838152, by rfl⟩ : syracuseStep 8940293 = 1676305) (by norm_num)
theorem B1985305 : Blo 1764083 1985305 := bbase (se 2 (by rfl) ⟨744489, by rfl⟩ : syracuseStep 1985305 = 1488979) (by norm_num)
theorem B2648861 : Blo 1764083 2648861 := bbase (se 3 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 2648861 = 993323) (by norm_num)
theorem B2648885 : Blo 1764083 2648885 := bbase (se 5 (by rfl) ⟨124166, by rfl⟩ : syracuseStep 2648885 = 248333) (by norm_num)
theorem B1788733 : Blo 1764083 1788733 := bbase (se 3 (by rfl) ⟨335387, by rfl⟩ : syracuseStep 1788733 = 670775) (by norm_num)
theorem B1985341 : Blo 1764083 1985341 := bbase (se 3 (by rfl) ⟨372251, by rfl⟩ : syracuseStep 1985341 = 744503) (by norm_num)
theorem B2648909 : Blo 1764083 2648909 := bbase (se 3 (by rfl) ⟨496670, by rfl⟩ : syracuseStep 2648909 = 993341) (by norm_num)
theorem B1985377 : Blo 1764083 1985377 := bbase (se 2 (by rfl) ⟨744516, by rfl⟩ : syracuseStep 1985377 = 1489033) (by norm_num)
theorem B2648933 : Blo 1764083 2648933 := bbase (se 4 (by rfl) ⟨248337, by rfl⟩ : syracuseStep 2648933 = 496675) (by norm_num)
theorem B2648957 : Blo 1764083 2648957 := bbase (se 3 (by rfl) ⟨496679, by rfl⟩ : syracuseStep 2648957 = 993359) (by norm_num)
theorem B1985413 : Blo 1764083 1985413 := bbase (se 4 (by rfl) ⟨186132, by rfl⟩ : syracuseStep 1985413 = 372265) (by norm_num)
theorem B6704005 : Blo 1764083 6704005 := bbase (se 4 (by rfl) ⟨628500, by rfl⟩ : syracuseStep 6704005 = 1257001) (by norm_num)
theorem B3771269 : Blo 1764083 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B2648981 : Blo 1764083 2648981 := bbase (se 6 (by rfl) ⟨62085, by rfl⟩ : syracuseStep 2648981 = 124171) (by norm_num)
theorem B1985449 : Blo 1764083 1985449 := bbase (se 2 (by rfl) ⟨744543, by rfl⟩ : syracuseStep 1985449 = 1489087) (by norm_num)
theorem B2649005 : Blo 1764083 2649005 := bbase (se 3 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 2649005 = 993377) (by norm_num)
theorem B2649029 : Blo 1764083 2649029 := bbase (se 4 (by rfl) ⟨248346, by rfl⟩ : syracuseStep 2649029 = 496693) (by norm_num)
theorem B1985485 : Blo 1764083 1985485 := bbase (se 3 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 1985485 = 744557) (by norm_num)
theorem B2649053 : Blo 1764083 2649053 := bbase (se 3 (by rfl) ⟨496697, by rfl⟩ : syracuseStep 2649053 = 993395) (by norm_num)
theorem B5958629 : Blo 1764083 5958629 := bbase (se 4 (by rfl) ⟨558621, by rfl⟩ : syracuseStep 5958629 = 1117243) (by norm_num)
theorem B1985521 : Blo 1764083 1985521 := bbase (se 2 (by rfl) ⟨744570, by rfl⟩ : syracuseStep 1985521 = 1489141) (by norm_num)
theorem B2649077 : Blo 1764083 2649077 := bbase (se 5 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 2649077 = 248351) (by norm_num)
theorem B2649101 : Blo 1764083 2649101 := bbase (se 3 (by rfl) ⟨496706, by rfl⟩ : syracuseStep 2649101 = 993413) (by norm_num)
theorem B1985557 : Blo 1764083 1985557 := bbase (se 6 (by rfl) ⟨46536, by rfl⟩ : syracuseStep 1985557 = 93073) (by norm_num)
theorem B2649125 : Blo 1764083 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B4467757 : Blo 1764083 4467757 := bbase (se 3 (by rfl) ⟨837704, by rfl⟩ : syracuseStep 4467757 = 1675409) (by norm_num)
theorem B13593653 : Blo 1764083 13593653 := bbase (se 5 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 13593653 = 1274405) (by norm_num)
theorem B1985593 : Blo 1764083 1985593 := bbase (se 2 (by rfl) ⟨744597, by rfl⟩ : syracuseStep 1985593 = 1489195) (by norm_num)
theorem B3820621 : Blo 1764083 3820621 := bbase (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) (by norm_num)
theorem B15084629 : Blo 1764083 15084629 := bbase (se 8 (by rfl) ⟨88386, by rfl⟩ : syracuseStep 15084629 = 176773) (by norm_num)
theorem B1985629 : Blo 1764083 1985629 := bbase (se 3 (by rfl) ⟨372305, by rfl⟩ : syracuseStep 1985629 = 744611) (by norm_num)
theorem B1789057 : Blo 1764083 1789057 := bbase (se 2 (by rfl) ⟨670896, by rfl⟩ : syracuseStep 1789057 = 1341793) (by norm_num)
theorem B1985665 : Blo 1764083 1985665 := bbase (se 2 (by rfl) ⟨744624, by rfl⟩ : syracuseStep 1985665 = 1489249) (by norm_num)
theorem B5655685 : Blo 1764083 5655685 := bbase (se 4 (by rfl) ⟨530220, by rfl⟩ : syracuseStep 5655685 = 1060441) (by norm_num)
theorem B2976925 : Blo 1764083 2976925 := bbase (se 3 (by rfl) ⟨558173, by rfl⟩ : syracuseStep 2976925 = 1116347) (by norm_num)
theorem B4467869 : Blo 1764083 4467869 := bbase (se 3 (by rfl) ⟨837725, by rfl⟩ : syracuseStep 4467869 = 1675451) (by norm_num)
theorem B8932517 : Blo 1764083 8932517 := bbase (se 4 (by rfl) ⟨837423, by rfl⟩ : syracuseStep 8932517 = 1674847) (by norm_num)
theorem B1985701 : Blo 1764083 1985701 := bbase (se 4 (by rfl) ⟨186159, by rfl⟩ : syracuseStep 1985701 = 372319) (by norm_num)
theorem B6704309 : Blo 1764083 6704309 := bbase (se 5 (by rfl) ⟨314264, by rfl⟩ : syracuseStep 6704309 = 628529) (by norm_num)
theorem B1985737 : Blo 1764083 1985737 := bbase (se 2 (by rfl) ⟨744651, by rfl⟩ : syracuseStep 1985737 = 1489303) (by norm_num)
theorem B3017965 : Blo 1764083 3017965 := bbase (se 3 (by rfl) ⟨565868, by rfl⟩ : syracuseStep 3017965 = 1131737) (by norm_num)
theorem B1985773 : Blo 1764083 1985773 := bbase (se 3 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 1985773 = 744665) (by norm_num)
theorem B2977013 : Blo 1764083 2977013 := bbase (se 5 (by rfl) ⟨139547, by rfl⟩ : syracuseStep 2977013 = 279095) (by norm_num)
theorem B5729525 : Blo 1764083 5729525 := bbase (se 5 (by rfl) ⟨268571, by rfl⟩ : syracuseStep 5729525 = 537143) (by norm_num)
theorem B1985809 : Blo 1764083 1985809 := bbase (se 2 (by rfl) ⟨744678, by rfl⟩ : syracuseStep 1985809 = 1489357) (by norm_num)
theorem B1985845 : Blo 1764083 1985845 := bbase (se 5 (by rfl) ⟨93086, by rfl⟩ : syracuseStep 1985845 = 186173) (by norm_num)
theorem B1985881 : Blo 1764083 1985881 := bbase (se 2 (by rfl) ⟨744705, by rfl⟩ : syracuseStep 1985881 = 1489411) (by norm_num)
theorem B4468061 : Blo 1764083 4468061 := bbase (se 3 (by rfl) ⟨837761, by rfl⟩ : syracuseStep 4468061 = 1675523) (by norm_num)
theorem B2977141 : Blo 1764083 2977141 := bbase (se 5 (by rfl) ⟨139553, by rfl⟩ : syracuseStep 2977141 = 279107) (by norm_num)
theorem B1985917 : Blo 1764083 1985917 := bbase (se 3 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 1985917 = 744719) (by norm_num)
theorem B5959061 : Blo 1764083 5959061 := bbase (se 6 (by rfl) ⟨139665, by rfl⟩ : syracuseStep 5959061 = 279331) (by norm_num)
theorem B1985953 : Blo 1764083 1985953 := bbase (se 2 (by rfl) ⟨744732, by rfl⟩ : syracuseStep 1985953 = 1489465) (by norm_num)
theorem B1985989 : Blo 1764083 1985989 := bbase (se 4 (by rfl) ⟨186186, by rfl⟩ : syracuseStep 1985989 = 372373) (by norm_num)
theorem B2977229 : Blo 1764083 2977229 := bbase (se 3 (by rfl) ⟨558230, by rfl⟩ : syracuseStep 2977229 = 1116461) (by norm_num)
theorem B1986025 : Blo 1764083 1986025 := bbase (se 2 (by rfl) ⟨744759, by rfl⟩ : syracuseStep 1986025 = 1489519) (by norm_num)
theorem B7540229 : Blo 1764083 7540229 := bbase (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) (by norm_num)
theorem B1986061 : Blo 1764083 1986061 := bbase (se 3 (by rfl) ⟨372386, by rfl⟩ : syracuseStep 1986061 = 744773) (by norm_num)
theorem B1986097 : Blo 1764083 1986097 := bbase (se 2 (by rfl) ⟨744786, by rfl⟩ : syracuseStep 1986097 = 1489573) (by norm_num)
theorem B2977357 : Blo 1764083 2977357 := bbase (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) (by norm_num)
theorem B1986133 : Blo 1764083 1986133 := bbase (se 8 (by rfl) ⟨11637, by rfl⟩ : syracuseStep 1986133 = 23275) (by norm_num)
theorem B1986169 : Blo 1764083 1986169 := bbase (se 2 (by rfl) ⟨744813, by rfl⟩ : syracuseStep 1986169 = 1489627) (by norm_num)
theorem B12070549 : Blo 1764083 12070549 := bbase (se 6 (by rfl) ⟨282903, by rfl⟩ : syracuseStep 12070549 = 565807) (by norm_num)
theorem B1986205 : Blo 1764083 1986205 := bbase (se 3 (by rfl) ⟨372413, by rfl⟩ : syracuseStep 1986205 = 744827) (by norm_num)
theorem B2977445 : Blo 1764083 2977445 := bbase (se 4 (by rfl) ⟨279135, by rfl⟩ : syracuseStep 2977445 = 558271) (by norm_num)
theorem B4468405 : Blo 1764083 4468405 := bbase (se 5 (by rfl) ⟨209456, by rfl⟩ : syracuseStep 4468405 = 418913) (by norm_num)
theorem B1986241 : Blo 1764083 1986241 := bbase (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) (by norm_num)
theorem B1986277 : Blo 1764083 1986277 := bbase (se 4 (by rfl) ⟨186213, by rfl⟩ : syracuseStep 1986277 = 372427) (by norm_num)
theorem B1986313 : Blo 1764083 1986313 := bbase (se 2 (by rfl) ⟨744867, by rfl⟩ : syracuseStep 1986313 = 1489735) (by norm_num)
theorem B2977573 : Blo 1764083 2977573 := bbase (se 4 (by rfl) ⟨279147, by rfl⟩ : syracuseStep 2977573 = 558295) (by norm_num)
theorem B4468517 : Blo 1764083 4468517 := bbase (se 4 (by rfl) ⟨418923, by rfl⟩ : syracuseStep 4468517 = 837847) (by norm_num)
theorem B1986349 : Blo 1764083 1986349 := bbase (se 3 (by rfl) ⟨372440, by rfl⟩ : syracuseStep 1986349 = 744881) (by norm_num)
theorem B5959493 : Blo 1764083 5959493 := bbase (se 4 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 5959493 = 1117405) (by norm_num)
theorem B1986385 : Blo 1764083 1986385 := bbase (se 2 (by rfl) ⟨744894, by rfl⟩ : syracuseStep 1986385 = 1489789) (by norm_num)
theorem B1986421 : Blo 1764083 1986421 := bbase (se 5 (by rfl) ⟨93113, by rfl⟩ : syracuseStep 1986421 = 186227) (by norm_num)
theorem B2977661 : Blo 1764083 2977661 := bbase (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) (by norm_num)
theorem B1986457 : Blo 1764083 1986457 := bbase (se 2 (by rfl) ⟨744921, by rfl⟩ : syracuseStep 1986457 = 1489843) (by norm_num)
theorem B3821501 : Blo 1764083 3821501 := bbase (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) (by norm_num)
theorem B1986493 : Blo 1764083 1986493 := bbase (se 3 (by rfl) ⟨372467, by rfl⟩ : syracuseStep 1986493 = 744935) (by norm_num)
theorem B1986529 : Blo 1764083 1986529 := bbase (se 2 (by rfl) ⟨744948, by rfl⟩ : syracuseStep 1986529 = 1489897) (by norm_num)
theorem B4468709 : Blo 1764083 4468709 := bbase (se 4 (by rfl) ⟨418941, by rfl⟩ : syracuseStep 4468709 = 837883) (by norm_num)
theorem B6041573 : Blo 1764083 6041573 := bbase (se 4 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 6041573 = 1132795) (by norm_num)
theorem B2977789 : Blo 1764083 2977789 := bbase (se 3 (by rfl) ⟨558335, by rfl⟩ : syracuseStep 2977789 = 1116671) (by norm_num)
theorem B1986565 : Blo 1764083 1986565 := bbase (se 4 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 1986565 = 372481) (by norm_num)
theorem B1789957 : Blo 1764083 1789957 := bbase (se 4 (by rfl) ⟨167808, by rfl⟩ : syracuseStep 1789957 = 335617) (by norm_num)
theorem B1986601 : Blo 1764083 1986601 := bbase (se 2 (by rfl) ⟨744975, by rfl⟩ : syracuseStep 1986601 = 1489951) (by norm_num)
theorem B1986637 : Blo 1764083 1986637 := bbase (se 3 (by rfl) ⟨372494, by rfl⟩ : syracuseStep 1986637 = 744989) (by norm_num)
theorem B2977877 : Blo 1764083 2977877 := bbase (se 8 (by rfl) ⟨17448, by rfl⟩ : syracuseStep 2977877 = 34897) (by norm_num)
theorem B1986673 : Blo 1764083 1986673 := bbase (se 2 (by rfl) ⟨745002, by rfl⟩ : syracuseStep 1986673 = 1490005) (by norm_num)
theorem B4296853 : Blo 1764083 4296853 := bbase (se 6 (by rfl) ⟨100707, by rfl⟩ : syracuseStep 4296853 = 201415) (by norm_num)
theorem B1986709 : Blo 1764083 1986709 := bbase (se 6 (by rfl) ⟨46563, by rfl⟩ : syracuseStep 1986709 = 93127) (by norm_num)
theorem B3969197 : Blo 1764083 3969197 := bbase (se 3 (by rfl) ⟨744224, by rfl⟩ : syracuseStep 3969197 = 1488449) (by norm_num)
theorem B1986745 : Blo 1764083 1986745 := bbase (se 2 (by rfl) ⟨745029, by rfl⟩ : syracuseStep 1986745 = 1490059) (by norm_num)
theorem B5025989 : Blo 1764083 5025989 := bbase (se 4 (by rfl) ⟨471186, by rfl⟩ : syracuseStep 5025989 = 942373) (by norm_num)
theorem B4526293 : Blo 1764083 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B9539797 : Blo 1764083 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B2978005 : Blo 1764083 2978005 := bbase (se 7 (by rfl) ⟨34898, by rfl⟩ : syracuseStep 2978005 = 69797) (by norm_num)
theorem B1986781 : Blo 1764083 1986781 := bbase (se 3 (by rfl) ⟨372521, by rfl⟩ : syracuseStep 1986781 = 745043) (by norm_num)
theorem B3969269 : Blo 1764083 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B5959925 : Blo 1764083 5959925 := bbase (se 5 (by rfl) ⟨279371, by rfl⟩ : syracuseStep 5959925 = 558743) (by norm_num)
theorem B1986817 : Blo 1764083 1986817 := bbase (se 2 (by rfl) ⟨745056, by rfl⟩ : syracuseStep 1986817 = 1490113) (by norm_num)
theorem B2978093 : Blo 1764083 2978093 := bbase (se 3 (by rfl) ⟨558392, by rfl⟩ : syracuseStep 2978093 = 1116785) (by norm_num)
theorem B3969341 : Blo 1764083 3969341 := bbase (se 3 (by rfl) ⟨744251, by rfl⟩ : syracuseStep 3969341 = 1488503) (by norm_num)
theorem B4469053 : Blo 1764083 4469053 := bbase (se 3 (by rfl) ⟨837947, by rfl⟩ : syracuseStep 4469053 = 1675895) (by norm_num)
theorem B48329045 : Blo 1764083 48329045 := bbase (se 10 (by rfl) ⟨70794, by rfl⟩ : syracuseStep 48329045 = 141589) (by norm_num)
theorem B2265445 : Blo 1764083 2265445 := bbase (se 4 (by rfl) ⟨212385, by rfl⟩ : syracuseStep 2265445 = 424771) (by norm_num)
theorem B3969413 : Blo 1764083 3969413 := bbase (se 4 (by rfl) ⟨372132, by rfl⟩ : syracuseStep 3969413 = 744265) (by norm_num)
theorem B2978221 : Blo 1764083 2978221 := bbase (se 3 (by rfl) ⟨558416, by rfl⟩ : syracuseStep 2978221 = 1116833) (by norm_num)
theorem B4469165 : Blo 1764083 4469165 := bbase (se 3 (by rfl) ⟨837968, by rfl⟩ : syracuseStep 4469165 = 1675937) (by norm_num)
theorem B8049077 : Blo 1764083 8049077 := bbase (se 5 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 8049077 = 754601) (by norm_num)
theorem B8933813 : Blo 1764083 8933813 := bbase (se 5 (by rfl) ⟨418772, by rfl⟩ : syracuseStep 8933813 = 837545) (by norm_num)
theorem B3969485 : Blo 1764083 3969485 := bbase (se 3 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 3969485 = 1488557) (by norm_num)
theorem B2232785 : Blo 1764083 2232785 := bbase (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) (by norm_num)
theorem B7541221 : Blo 1764083 7541221 := bbase (se 4 (by rfl) ⟨706989, by rfl⟩ : syracuseStep 7541221 = 1413979) (by norm_num)
theorem B10047989 : Blo 1764083 10047989 := bbase (se 5 (by rfl) ⟨470999, by rfl⟩ : syracuseStep 10047989 = 941999) (by norm_num)
theorem B2978309 : Blo 1764083 2978309 := bbase (se 4 (by rfl) ⟨279216, by rfl⟩ : syracuseStep 2978309 = 558433) (by norm_num)
theorem B2232841 : Blo 1764083 2232841 := bbase (se 2 (by rfl) ⟨837315, by rfl⟩ : syracuseStep 2232841 = 1674631) (by norm_num)
theorem B3969557 : Blo 1764083 3969557 := bbase (se 6 (by rfl) ⟨93036, by rfl⟩ : syracuseStep 3969557 = 186073) (by norm_num)
theorem B12079637 : Blo 1764083 12079637 := bbase (se 6 (by rfl) ⟨283116, by rfl⟩ : syracuseStep 12079637 = 566233) (by norm_num)
theorem B3969629 : Blo 1764083 3969629 := bbase (se 3 (by rfl) ⟨744305, by rfl⟩ : syracuseStep 3969629 = 1488611) (by norm_num)
theorem B2232937 : Blo 1764083 2232937 := bbase (se 2 (by rfl) ⟨837351, by rfl⟩ : syracuseStep 2232937 = 1674703) (by norm_num)
theorem B4469357 : Blo 1764083 4469357 := bbase (se 3 (by rfl) ⟨838004, by rfl⟩ : syracuseStep 4469357 = 1676009) (by norm_num)
theorem B2978437 : Blo 1764083 2978437 := bbase (se 4 (by rfl) ⟨279228, by rfl⟩ : syracuseStep 2978437 = 558457) (by norm_num)
theorem B3969701 : Blo 1764083 3969701 := bbase (se 4 (by rfl) ⟨372159, by rfl⟩ : syracuseStep 3969701 = 744319) (by norm_num)
theorem B5960357 : Blo 1764083 5960357 := bbase (se 4 (by rfl) ⟨558783, by rfl⟩ : syracuseStep 5960357 = 1117567) (by norm_num)
theorem B7156421 : Blo 1764083 7156421 := bbase (se 4 (by rfl) ⟨670914, by rfl⟩ : syracuseStep 7156421 = 1341829) (by norm_num)
theorem B2978525 : Blo 1764083 2978525 := bbase (se 3 (by rfl) ⟨558473, by rfl⟩ : syracuseStep 2978525 = 1116947) (by norm_num)
theorem B3969773 : Blo 1764083 3969773 := bbase (se 3 (by rfl) ⟨744332, by rfl⟩ : syracuseStep 3969773 = 1488665) (by norm_num)
theorem B2233109 : Blo 1764083 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B3969845 : Blo 1764083 3969845 := bbase (se 5 (by rfl) ⟨186086, by rfl⟩ : syracuseStep 3969845 = 372173) (by norm_num)
theorem B2233165 : Blo 1764083 2233165 := bbase (se 3 (by rfl) ⟨418718, by rfl⟩ : syracuseStep 2233165 = 837437) (by norm_num)
theorem B2978653 : Blo 1764083 2978653 := bbase (se 3 (by rfl) ⟨558497, by rfl⟩ : syracuseStep 2978653 = 1116995) (by norm_num)
theorem B5026661 : Blo 1764083 5026661 := bbase (se 4 (by rfl) ⟨471249, by rfl⟩ : syracuseStep 5026661 = 942499) (by norm_num)
theorem B5305205 : Blo 1764083 5305205 := bbase (se 5 (by rfl) ⟨248681, by rfl⟩ : syracuseStep 5305205 = 497363) (by norm_num)
theorem B3969917 : Blo 1764083 3969917 := bbase (se 3 (by rfl) ⟨744359, by rfl⟩ : syracuseStep 3969917 = 1488719) (by norm_num)
theorem B2233261 : Blo 1764083 2233261 := bbase (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) (by norm_num)
theorem B2978741 : Blo 1764083 2978741 := bbase (se 5 (by rfl) ⟨139628, by rfl⟩ : syracuseStep 2978741 = 279257) (by norm_num)
theorem B3969989 : Blo 1764083 3969989 := bbase (se 4 (by rfl) ⟨372186, by rfl⟩ : syracuseStep 3969989 = 744373) (by norm_num)
theorem B4469701 : Blo 1764083 4469701 := bbase (se 4 (by rfl) ⟨419034, by rfl⟩ : syracuseStep 4469701 = 838069) (by norm_num)
theorem B3970061 : Blo 1764083 3970061 := bbase (se 3 (by rfl) ⟨744386, by rfl⟩ : syracuseStep 3970061 = 1488773) (by norm_num)
theorem B2511901 : Blo 1764083 2511901 := bbase (se 3 (by rfl) ⟨470981, by rfl⟩ : syracuseStep 2511901 = 941963) (by norm_num)
theorem B2978869 : Blo 1764083 2978869 := bbase (se 5 (by rfl) ⟨139634, by rfl⟩ : syracuseStep 2978869 = 279269) (by norm_num)
theorem B4469813 : Blo 1764083 4469813 := bbase (se 5 (by rfl) ⟨209522, by rfl⟩ : syracuseStep 4469813 = 419045) (by norm_num)
theorem B3970133 : Blo 1764083 3970133 := bbase (se 8 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 3970133 = 46525) (by norm_num)
theorem B2233433 : Blo 1764083 2233433 := bbase (se 2 (by rfl) ⟨837537, by rfl⟩ : syracuseStep 2233433 = 1675075) (by norm_num)
theorem B4240525 : Blo 1764083 4240525 := bbase (se 3 (by rfl) ⟨795098, by rfl⟩ : syracuseStep 4240525 = 1590197) (by norm_num)
theorem B2978957 : Blo 1764083 2978957 := bbase (se 3 (by rfl) ⟨558554, by rfl⟩ : syracuseStep 2978957 = 1117109) (by norm_num)
theorem B2233489 : Blo 1764083 2233489 := bbase (se 2 (by rfl) ⟨837558, by rfl⟩ : syracuseStep 2233489 = 1675117) (by norm_num)
theorem B3970205 : Blo 1764083 3970205 := bbase (se 3 (by rfl) ⟨744413, by rfl⟩ : syracuseStep 3970205 = 1488827) (by norm_num)
theorem B3970277 : Blo 1764083 3970277 := bbase (se 4 (by rfl) ⟨372213, by rfl⟩ : syracuseStep 3970277 = 744427) (by norm_num)
theorem B2233585 : Blo 1764083 2233585 := bbase (se 2 (by rfl) ⟨837594, by rfl⟩ : syracuseStep 2233585 = 1675189) (by norm_num)
theorem B4773109 : Blo 1764083 4773109 := bbase (se 5 (by rfl) ⟨223739, by rfl⟩ : syracuseStep 4773109 = 447479) (by norm_num)
theorem B4470005 : Blo 1764083 4470005 := bbase (se 5 (by rfl) ⟨209531, by rfl⟩ : syracuseStep 4470005 = 419063) (by norm_num)
theorem B2979085 : Blo 1764083 2979085 := bbase (se 3 (by rfl) ⟨558578, by rfl⟩ : syracuseStep 2979085 = 1117157) (by norm_num)
theorem B5027093 : Blo 1764083 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B3970349 : Blo 1764083 3970349 := bbase (se 3 (by rfl) ⟨744440, by rfl⟩ : syracuseStep 3970349 = 1488881) (by norm_num)
theorem B2979173 : Blo 1764083 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B2512237 : Blo 1764083 2512237 := bbase (se 3 (by rfl) ⟨471044, by rfl⟩ : syracuseStep 2512237 = 942089) (by norm_num)
theorem B3970421 : Blo 1764083 3970421 := bbase (se 5 (by rfl) ⟨186113, by rfl⟩ : syracuseStep 3970421 = 372227) (by norm_num)
theorem B3020149 : Blo 1764083 3020149 := bbase (se 5 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 3020149 = 283139) (by norm_num)
theorem B14308757 : Blo 1764083 14308757 := bbase (se 6 (by rfl) ⟨335361, by rfl⟩ : syracuseStep 14308757 = 670723) (by norm_num)
theorem B2233757 : Blo 1764083 2233757 := bbase (se 3 (by rfl) ⟨418829, by rfl⟩ : syracuseStep 2233757 = 837659) (by norm_num)
theorem B3970493 : Blo 1764083 3970493 := bbase (se 3 (by rfl) ⟨744467, by rfl⟩ : syracuseStep 3970493 = 1488935) (by norm_num)
theorem B2233813 : Blo 1764083 2233813 := bbase (se 7 (by rfl) ⟨26177, by rfl⟩ : syracuseStep 2233813 = 52355) (by norm_num)
theorem B2979301 : Blo 1764083 2979301 := bbase (se 4 (by rfl) ⟨279309, by rfl⟩ : syracuseStep 2979301 = 558619) (by norm_num)
theorem B3970565 : Blo 1764083 3970565 := bbase (se 4 (by rfl) ⟨372240, by rfl⟩ : syracuseStep 3970565 = 744481) (by norm_num)
theorem B5092901 : Blo 1764083 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B4773413 : Blo 1764083 4773413 := bbase (se 4 (by rfl) ⟨447507, by rfl⟩ : syracuseStep 4773413 = 895015) (by norm_num)
theorem B2233909 : Blo 1764083 2233909 := bbase (se 5 (by rfl) ⟨104714, by rfl⟩ : syracuseStep 2233909 = 209429) (by norm_num)
theorem B2979389 : Blo 1764083 2979389 := bbase (se 3 (by rfl) ⟨558635, by rfl⟩ : syracuseStep 2979389 = 1117271) (by norm_num)
theorem B4355653 : Blo 1764083 4355653 := bbase (se 4 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 4355653 = 816685) (by norm_num)
theorem B2512453 : Blo 1764083 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B3970637 : Blo 1764083 3970637 := bbase (se 3 (by rfl) ⟨744494, by rfl⟩ : syracuseStep 3970637 = 1488989) (by norm_num)
theorem B4470349 : Blo 1764083 4470349 := bbase (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) (by norm_num)
theorem B6698645 : Blo 1764083 6698645 := bbase (se 6 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 6698645 = 313999) (by norm_num)
theorem B3970709 : Blo 1764083 3970709 := bbase (se 6 (by rfl) ⟨93063, by rfl⟩ : syracuseStep 3970709 = 186127) (by norm_num)
theorem B3397277 : Blo 1764083 3397277 := bbase (se 3 (by rfl) ⟨636989, by rfl⟩ : syracuseStep 3397277 = 1273979) (by norm_num)
theorem B5732021 : Blo 1764083 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B4298429 : Blo 1764083 4298429 := bbase (se 3 (by rfl) ⟨805955, by rfl⟩ : syracuseStep 4298429 = 1611911) (by norm_num)
theorem B2979517 : Blo 1764083 2979517 := bbase (se 3 (by rfl) ⟨558659, by rfl⟩ : syracuseStep 2979517 = 1117319) (by norm_num)
theorem B8935109 : Blo 1764083 8935109 := bbase (se 4 (by rfl) ⟨837666, by rfl⟩ : syracuseStep 8935109 = 1675333) (by norm_num)
theorem B3970781 : Blo 1764083 3970781 := bbase (se 3 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 3970781 = 1489043) (by norm_num)
theorem B2119393 : Blo 1764083 2119393 := bbase (se 2 (by rfl) ⟨794772, by rfl⟩ : syracuseStep 2119393 = 1589545) (by norm_num)
theorem B2234081 : Blo 1764083 2234081 := bbase (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) (by norm_num)
theorem B2119441 : Blo 1764083 2119441 := bbase (se 2 (by rfl) ⟨794790, by rfl⟩ : syracuseStep 2119441 = 1589581) (by norm_num)
theorem B2979605 : Blo 1764083 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B2234137 : Blo 1764083 2234137 := bbase (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) (by norm_num)
theorem B3970853 : Blo 1764083 3970853 := bbase (se 4 (by rfl) ⟨372267, by rfl⟩ : syracuseStep 3970853 = 744535) (by norm_num)
theorem B3970925 : Blo 1764083 3970925 := bbase (se 3 (by rfl) ⟨744548, by rfl⟩ : syracuseStep 3970925 = 1489097) (by norm_num)
theorem B2234233 : Blo 1764083 2234233 := bbase (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) (by norm_num)
theorem B2979733 : Blo 1764083 2979733 := bbase (se 6 (by rfl) ⟨69837, by rfl⟩ : syracuseStep 2979733 = 139675) (by norm_num)
theorem B6698933 : Blo 1764083 6698933 := bbase (se 5 (by rfl) ⟨314012, by rfl⟩ : syracuseStep 6698933 = 628025) (by norm_num)
theorem B3970997 : Blo 1764083 3970997 := bbase (se 5 (by rfl) ⟨186140, by rfl⟩ : syracuseStep 3970997 = 372281) (by norm_num)
theorem B2512829 : Blo 1764083 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B21755861 : Blo 1764083 21755861 := bbase (se 7 (by rfl) ⟨254951, by rfl⟩ : syracuseStep 21755861 = 509903) (by norm_num)
theorem B2979821 : Blo 1764083 2979821 := bbase (se 3 (by rfl) ⟨558716, by rfl⟩ : syracuseStep 2979821 = 1117433) (by norm_num)
theorem B3971069 : Blo 1764083 3971069 := bbase (se 3 (by rfl) ⟨744575, by rfl⟩ : syracuseStep 3971069 = 1489151) (by norm_num)
theorem B5027845 : Blo 1764083 5027845 := bbase (se 4 (by rfl) ⟨471360, by rfl⟩ : syracuseStep 5027845 = 942721) (by norm_num)
theorem B2234405 : Blo 1764083 2234405 := bbase (se 4 (by rfl) ⟨209475, by rfl⟩ : syracuseStep 2234405 = 418951) (by norm_num)
theorem B3020861 : Blo 1764083 3020861 := bbase (se 3 (by rfl) ⟨566411, by rfl⟩ : syracuseStep 3020861 = 1132823) (by norm_num)
theorem B3971141 : Blo 1764083 3971141 := bbase (se 4 (by rfl) ⟨372294, by rfl⟩ : syracuseStep 3971141 = 744589) (by norm_num)
theorem B4241477 : Blo 1764083 4241477 := bbase (se 4 (by rfl) ⟨397638, by rfl⟩ : syracuseStep 4241477 = 795277) (by norm_num)
theorem B2234461 : Blo 1764083 2234461 := bbase (se 3 (by rfl) ⟨418961, by rfl⟩ : syracuseStep 2234461 = 837923) (by norm_num)
theorem B2979949 : Blo 1764083 2979949 := bbase (se 3 (by rfl) ⟨558740, by rfl⟩ : syracuseStep 2979949 = 1117481) (by norm_num)
theorem B4241533 : Blo 1764083 4241533 := bbase (se 3 (by rfl) ⟨795287, by rfl⟩ : syracuseStep 4241533 = 1590575) (by norm_num)
theorem B3971213 : Blo 1764083 3971213 := bbase (se 3 (by rfl) ⟨744602, by rfl⟩ : syracuseStep 3971213 = 1489205) (by norm_num)
theorem B10057877 : Blo 1764083 10057877 := bbase (se 6 (by rfl) ⟨235731, by rfl⟩ : syracuseStep 10057877 = 471463) (by norm_num)
theorem B2013337 : Blo 1764083 2013337 := bbase (se 2 (by rfl) ⟨755001, by rfl⟩ : syracuseStep 2013337 = 1510003) (by norm_num)
theorem B2234557 : Blo 1764083 2234557 := bbase (se 3 (by rfl) ⟨418979, by rfl⟩ : syracuseStep 2234557 = 837959) (by norm_num)
theorem B2980037 : Blo 1764083 2980037 := bbase (se 4 (by rfl) ⟨279378, by rfl⟩ : syracuseStep 2980037 = 558757) (by norm_num)
theorem B3971285 : Blo 1764083 3971285 := bbase (se 7 (by rfl) ⟨46538, by rfl⟩ : syracuseStep 3971285 = 93077) (by norm_num)
theorem B16963829 : Blo 1764083 16963829 := bbase (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) (by norm_num)
theorem B3971357 : Blo 1764083 3971357 := bbase (se 3 (by rfl) ⟨744629, by rfl⟩ : syracuseStep 3971357 = 1489259) (by norm_num)
theorem B2013493 : Blo 1764083 2013493 := bbase (se 5 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 2013493 = 188765) (by norm_num)
theorem B2980165 : Blo 1764083 2980165 := bbase (se 4 (by rfl) ⟨279390, by rfl⟩ : syracuseStep 2980165 = 558781) (by norm_num)
theorem B5953877 : Blo 1764083 5953877 := bbase (se 10 (by rfl) ⟨8721, by rfl⟩ : syracuseStep 5953877 = 17443) (by norm_num)
theorem B3971429 : Blo 1764083 3971429 := bbase (se 4 (by rfl) ⟨372321, by rfl⟩ : syracuseStep 3971429 = 744643) (by norm_num)
theorem B9058661 : Blo 1764083 9058661 := bbase (se 4 (by rfl) ⟨849249, by rfl⟩ : syracuseStep 9058661 = 1698499) (by norm_num)
theorem B2234729 : Blo 1764083 2234729 := bbase (se 2 (by rfl) ⟨838023, by rfl⟩ : syracuseStep 2234729 = 1676047) (by norm_num)
theorem B2980253 : Blo 1764083 2980253 := bbase (se 3 (by rfl) ⟨558797, by rfl⟩ : syracuseStep 2980253 = 1117595) (by norm_num)
theorem B2234785 : Blo 1764083 2234785 := bbase (se 2 (by rfl) ⟨838044, by rfl⟩ : syracuseStep 2234785 = 1676089) (by norm_num)
theorem B3971501 : Blo 1764083 3971501 := bbase (se 3 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 3971501 = 1489313) (by norm_num)
theorem B2120113 : Blo 1764083 2120113 := bbase (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) (by norm_num)
theorem B3578357 : Blo 1764083 3578357 := bbase (se 5 (by rfl) ⟨167735, by rfl⟩ : syracuseStep 3578357 = 335471) (by norm_num)
theorem B3971573 : Blo 1764083 3971573 := bbase (se 5 (by rfl) ⟨186167, by rfl⟩ : syracuseStep 3971573 = 372335) (by norm_num)
theorem B4241909 : Blo 1764083 4241909 := bbase (se 5 (by rfl) ⟨198839, by rfl⟩ : syracuseStep 4241909 = 397679) (by norm_num)
theorem B2234881 : Blo 1764083 2234881 := bbase (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) (by norm_num)
theorem B3971645 : Blo 1764083 3971645 := bbase (se 3 (by rfl) ⟨744683, by rfl⟩ : syracuseStep 3971645 = 1489367) (by norm_num)
theorem B3349117 : Blo 1764083 3349117 := bbase (se 3 (by rfl) ⟨627959, by rfl⟩ : syracuseStep 3349117 = 1255919) (by norm_num)
theorem B3971717 : Blo 1764083 3971717 := bbase (se 4 (by rfl) ⟨372348, by rfl⟩ : syracuseStep 3971717 = 744697) (by norm_num)
theorem B22928021 : Blo 1764083 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B2235053 : Blo 1764083 2235053 := bbase (se 3 (by rfl) ⟨419072, by rfl⟩ : syracuseStep 2235053 = 838145) (by norm_num)
theorem B3971789 : Blo 1764083 3971789 := bbase (se 3 (by rfl) ⟨744710, by rfl⟩ : syracuseStep 3971789 = 1489421) (by norm_num)
theorem B4242149 : Blo 1764083 4242149 := bbase (se 4 (by rfl) ⟨397701, by rfl⟩ : syracuseStep 4242149 = 795403) (by norm_num)
theorem B2235109 : Blo 1764083 2235109 := bbase (se 4 (by rfl) ⟨209541, by rfl⟩ : syracuseStep 2235109 = 419083) (by norm_num)
theorem B5954309 : Blo 1764083 5954309 := bbase (se 4 (by rfl) ⟨558216, by rfl⟩ : syracuseStep 5954309 = 1116433) (by norm_num)
theorem B3971861 : Blo 1764083 3971861 := bbase (se 6 (by rfl) ⟨93090, by rfl⟩ : syracuseStep 3971861 = 186181) (by norm_num)
theorem B3971933 : Blo 1764083 3971933 := bbase (se 3 (by rfl) ⟨744737, by rfl⟩ : syracuseStep 3971933 = 1489475) (by norm_num)
theorem B3972005 : Blo 1764083 3972005 := bbase (se 4 (by rfl) ⟨372375, by rfl⟩ : syracuseStep 3972005 = 744751) (by norm_num)
theorem B3349421 : Blo 1764083 3349421 := bbase (se 3 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 3349421 = 1256033) (by norm_num)
theorem B2866109 : Blo 1764083 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B8936405 : Blo 1764083 8936405 := bbase (se 7 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 8936405 = 209447) (by norm_num)
theorem B2866141 : Blo 1764083 2866141 := bbase (se 3 (by rfl) ⟨537401, by rfl⟩ : syracuseStep 2866141 = 1074803) (by norm_num)
theorem B3972077 : Blo 1764083 3972077 := bbase (se 3 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 3972077 = 1489529) (by norm_num)
theorem B3972149 : Blo 1764083 3972149 := bbase (se 5 (by rfl) ⟨186194, by rfl⟩ : syracuseStep 3972149 = 372389) (by norm_num)
theorem B6700117 : Blo 1764083 6700117 := bbase (se 8 (by rfl) ⟨39258, by rfl⟩ : syracuseStep 6700117 = 78517) (by norm_num)
theorem B6364261 : Blo 1764083 6364261 := bbase (se 4 (by rfl) ⟨596649, by rfl⟩ : syracuseStep 6364261 = 1193299) (by norm_num)
theorem B3972221 : Blo 1764083 3972221 := bbase (se 3 (by rfl) ⟨744791, by rfl⟩ : syracuseStep 3972221 = 1489583) (by norm_num)
theorem B5954741 : Blo 1764083 5954741 := bbase (se 5 (by rfl) ⟨279128, by rfl⟩ : syracuseStep 5954741 = 558257) (by norm_num)
theorem B3972293 : Blo 1764083 3972293 := bbase (se 4 (by rfl) ⟨372402, by rfl⟩ : syracuseStep 3972293 = 744805) (by norm_num)
theorem B72457429 : Blo 1764083 72457429 := bbase (se 7 (by rfl) ⟨849110, by rfl⟩ : syracuseStep 72457429 = 1698221) (by norm_num)
theorem B4357373 : Blo 1764083 4357373 := bbase (se 3 (by rfl) ⟨817007, by rfl⟩ : syracuseStep 4357373 = 1634015) (by norm_num)
theorem B3972365 : Blo 1764083 3972365 := bbase (se 3 (by rfl) ⟨744818, by rfl⟩ : syracuseStep 3972365 = 1489637) (by norm_num)
theorem B9674005 : Blo 1764083 9674005 := bbase (se 6 (by rfl) ⟨226734, by rfl⟩ : syracuseStep 9674005 = 453469) (by norm_num)
theorem B2514253 : Blo 1764083 2514253 := bbase (se 3 (by rfl) ⟨471422, by rfl⟩ : syracuseStep 2514253 = 942845) (by norm_num)
theorem B3874133 : Blo 1764083 3874133 := bbase (se 11 (by rfl) ⟨2837, by rfl⟩ : syracuseStep 3874133 = 5675) (by norm_num)
theorem B3972437 : Blo 1764083 3972437 := bbase (se 11 (by rfl) ⟨2909, by rfl⟩ : syracuseStep 3972437 = 5819) (by norm_num)
theorem B12901717 : Blo 1764083 12901717 := bbase (se 11 (by rfl) ⟨9449, by rfl⟩ : syracuseStep 12901717 = 18899) (by norm_num)
theorem B6700421 : Blo 1764083 6700421 := bbase (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) (by norm_num)
theorem B2121113 : Blo 1764083 2121113 := bbase (se 2 (by rfl) ⟨795417, by rfl⟩ : syracuseStep 2121113 = 1590835) (by norm_num)
theorem B3972509 : Blo 1764083 3972509 := bbase (se 3 (by rfl) ⟨744845, by rfl⟩ : syracuseStep 3972509 = 1489691) (by norm_num)
theorem B2121185 : Blo 1764083 2121185 := bbase (se 2 (by rfl) ⟨795444, by rfl⟩ : syracuseStep 2121185 = 1590889) (by norm_num)
theorem B3972581 : Blo 1764083 3972581 := bbase (se 4 (by rfl) ⟨372429, by rfl⟩ : syracuseStep 3972581 = 744859) (by norm_num)
theorem B5307925 : Blo 1764083 5307925 := bbase (se 6 (by rfl) ⟨124404, by rfl⟩ : syracuseStep 5307925 = 248809) (by norm_num)
theorem B3972653 : Blo 1764083 3972653 := bbase (se 3 (by rfl) ⟨744872, by rfl⟩ : syracuseStep 3972653 = 1489745) (by norm_num)
theorem B5955173 : Blo 1764083 5955173 := bbase (se 4 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 5955173 = 1116595) (by norm_num)
theorem B3972725 : Blo 1764083 3972725 := bbase (se 5 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 3972725 = 372443) (by norm_num)
theorem B3350173 : Blo 1764083 3350173 := bbase (se 3 (by rfl) ⟨628157, by rfl⟩ : syracuseStep 3350173 = 1256315) (by norm_num)
theorem B2719397 : Blo 1764083 2719397 := bbase (se 4 (by rfl) ⟨254943, by rfl⟩ : syracuseStep 2719397 = 509887) (by norm_num)
theorem B3972797 : Blo 1764083 3972797 := bbase (se 3 (by rfl) ⟨744899, by rfl⟩ : syracuseStep 3972797 = 1489799) (by norm_num)
theorem B16096981 : Blo 1764083 16096981 := bbase (se 7 (by rfl) ⟨188636, by rfl⟩ : syracuseStep 16096981 = 377273) (by norm_num)
theorem B3972869 : Blo 1764083 3972869 := bbase (se 4 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 3972869 = 744913) (by norm_num)
theorem B2121493 : Blo 1764083 2121493 := bbase (se 6 (by rfl) ⟨49722, by rfl⟩ : syracuseStep 2121493 = 99445) (by norm_num)
theorem B3350317 : Blo 1764083 3350317 := bbase (se 3 (by rfl) ⟨628184, by rfl⟩ : syracuseStep 3350317 = 1256369) (by norm_num)
theorem B4079413 : Blo 1764083 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B2547517 : Blo 1764083 2547517 := bbase (se 3 (by rfl) ⟨477659, by rfl⟩ : syracuseStep 2547517 = 955319) (by norm_num)
theorem B3768133 : Blo 1764083 3768133 := bbase (se 4 (by rfl) ⟨353262, by rfl⟩ : syracuseStep 3768133 = 706525) (by norm_num)
theorem B3972941 : Blo 1764083 3972941 := bbase (se 3 (by rfl) ⟨744926, by rfl⟩ : syracuseStep 3972941 = 1489853) (by norm_num)
theorem B3973013 : Blo 1764083 3973013 := bbase (se 6 (by rfl) ⟨93117, by rfl⟩ : syracuseStep 3973013 = 186235) (by norm_num)
theorem B13410197 : Blo 1764083 13410197 := bbase (se 6 (by rfl) ⟨314301, by rfl⟩ : syracuseStep 13410197 = 628603) (by norm_num)
theorem B2121661 : Blo 1764083 2121661 := bbase (se 3 (by rfl) ⟨397811, by rfl⟩ : syracuseStep 2121661 = 795623) (by norm_num)
theorem B1884097 : Blo 1764083 1884097 := bbase (se 2 (by rfl) ⟨706536, by rfl⟩ : syracuseStep 1884097 = 1413073) (by norm_num)
theorem B3350477 : Blo 1764083 3350477 := bbase (se 3 (by rfl) ⟨628214, by rfl⟩ : syracuseStep 3350477 = 1256429) (by norm_num)
theorem B3973085 : Blo 1764083 3973085 := bbase (se 3 (by rfl) ⟨744953, by rfl⟩ : syracuseStep 3973085 = 1489907) (by norm_num)
theorem B8052709 : Blo 1764083 8052709 := bbase (se 4 (by rfl) ⟨754941, by rfl⟩ : syracuseStep 8052709 = 1509883) (by norm_num)
theorem B3629137 : Blo 1764083 3629137 := bstep (se 2 (by rfl) ⟨1360926, by rfl⟩ : syracuseStep 3629137 = 2721853) B2721853
theorem B2646131 : Blo 1764083 2646131 := bstep (se 1 (by rfl) ⟨1984598, by rfl⟩ : syracuseStep 2646131 = 3969197) B3969197
theorem B3350659 : Blo 1764083 3350659 := bstep (se 1 (by rfl) ⟨2512994, by rfl⟩ : syracuseStep 3350659 = 5025989) B5025989
theorem B2646161 : Blo 1764083 2646161 := bstep (se 2 (by rfl) ⟨992310, by rfl⟩ : syracuseStep 2646161 = 1984621) B1984621
theorem B3973265 : Blo 1764083 3973265 := bstep (se 2 (by rfl) ⟨1489974, by rfl⟩ : syracuseStep 3973265 = 2979949) B2979949
theorem B2646179 : Blo 1764083 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B1884323 : Blo 1764083 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B3973283 : Blo 1764083 3973283 := bstep (se 1 (by rfl) ⟨2979962, by rfl⟩ : syracuseStep 3973283 = 5959925) B5959925
theorem B2646209 : Blo 1764083 2646209 := bstep (se 2 (by rfl) ⟨992328, by rfl⟩ : syracuseStep 2646209 = 1984657) B1984657
theorem B2646227 : Blo 1764083 2646227 := bstep (se 1 (by rfl) ⟨1984670, by rfl⟩ : syracuseStep 2646227 = 3969341) B3969341
theorem B32219363 : Blo 1764083 32219363 := bstep (se 1 (by rfl) ⟨24164522, by rfl⟩ : syracuseStep 32219363 = 48329045) B48329045
theorem B5955821 : Blo 1764083 5955821 := bstep (se 3 (by rfl) ⟨1116716, by rfl⟩ : syracuseStep 5955821 = 2233433) B2233433
theorem B2646257 : Blo 1764083 2646257 := bstep (se 2 (by rfl) ⟨992346, by rfl⟩ : syracuseStep 2646257 = 1984693) B1984693
theorem B7536881 : Blo 1764083 7536881 := bstep (se 2 (by rfl) ⟨2826330, by rfl⟩ : syracuseStep 7536881 = 5652661) B5652661
theorem B2646275 : Blo 1764083 2646275 := bstep (se 1 (by rfl) ⟨1984706, by rfl⟩ : syracuseStep 2646275 = 3969413) B3969413
theorem B2646305 : Blo 1764083 2646305 := bstep (se 2 (by rfl) ⟨992364, by rfl⟩ : syracuseStep 2646305 = 1984729) B1984729
theorem B3768611 : Blo 1764083 3768611 := bstep (se 1 (by rfl) ⟨2826458, by rfl⟩ : syracuseStep 3768611 = 5652917) B5652917
theorem B5366051 : Blo 1764083 5366051 := bstep (se 1 (by rfl) ⟨4024538, by rfl⟩ : syracuseStep 5366051 = 8049077) B8049077
theorem B5955875 : Blo 1764083 5955875 := bstep (se 1 (by rfl) ⟨4466906, by rfl⟩ : syracuseStep 5955875 = 8933813) B8933813
theorem B7258403 : Blo 1764083 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B2646323 : Blo 1764083 2646323 := bstep (se 1 (by rfl) ⟨1984742, by rfl⟩ : syracuseStep 2646323 = 3969485) B3969485
theorem B5652803 : Blo 1764083 5652803 := bstep (se 1 (by rfl) ⟨4239602, by rfl⟩ : syracuseStep 5652803 = 8479205) B8479205
theorem B2646353 : Blo 1764083 2646353 := bstep (se 2 (by rfl) ⟨992382, by rfl⟩ : syracuseStep 2646353 = 1984765) B1984765
theorem B2646371 : Blo 1764083 2646371 := bstep (se 1 (by rfl) ⟨1984778, by rfl⟩ : syracuseStep 2646371 = 3969557) B3969557
theorem B8053091 : Blo 1764083 8053091 := bstep (se 1 (by rfl) ⟨6039818, by rfl⟩ : syracuseStep 8053091 = 12079637) B12079637
theorem B2646401 : Blo 1764083 2646401 := bstep (se 2 (by rfl) ⟨992400, by rfl⟩ : syracuseStep 2646401 = 1984801) B1984801
theorem B2646419 : Blo 1764083 2646419 := bstep (se 1 (by rfl) ⟨1984814, by rfl⟩ : syracuseStep 2646419 = 3969629) B3969629
theorem B2646449 : Blo 1764083 2646449 := bstep (se 2 (by rfl) ⟨992418, by rfl⟩ : syracuseStep 2646449 = 1984837) B1984837
theorem B3973553 : Blo 1764083 3973553 := bstep (se 2 (by rfl) ⟨1490082, by rfl⟩ : syracuseStep 3973553 = 2980165) B2980165
theorem B2646467 : Blo 1764083 2646467 := bstep (se 1 (by rfl) ⟨1984850, by rfl⟩ : syracuseStep 2646467 = 3969701) B3969701
theorem B3973571 : Blo 1764083 3973571 := bstep (se 1 (by rfl) ⟨2980178, by rfl⟩ : syracuseStep 3973571 = 5960357) B5960357
theorem B10052045 : Blo 1764083 10052045 := bstep (se 3 (by rfl) ⟨1884758, by rfl⟩ : syracuseStep 10052045 = 3769517) B3769517
theorem B2646497 : Blo 1764083 2646497 := bstep (se 2 (by rfl) ⟨992436, by rfl⟩ : syracuseStep 2646497 = 1984873) B1984873
theorem B2646515 : Blo 1764083 2646515 := bstep (se 1 (by rfl) ⟨1984886, by rfl⟩ : syracuseStep 2646515 = 3969773) B3969773
theorem B2646545 : Blo 1764083 2646545 := bstep (se 2 (by rfl) ⟨992454, by rfl⟩ : syracuseStep 2646545 = 1984909) B1984909
theorem B2646563 : Blo 1764083 2646563 := bstep (se 1 (by rfl) ⟨1984922, by rfl⟩ : syracuseStep 2646563 = 3969845) B3969845
theorem B5956145 : Blo 1764083 5956145 := bstep (se 2 (by rfl) ⟨2233554, by rfl⟩ : syracuseStep 5956145 = 4467109) B4467109
theorem B2646593 : Blo 1764083 2646593 := bstep (se 2 (by rfl) ⟨992472, by rfl⟩ : syracuseStep 2646593 = 1984945) B1984945
theorem B3351107 : Blo 1764083 3351107 := bstep (se 1 (by rfl) ⟨2513330, by rfl⟩ : syracuseStep 3351107 = 5026661) B5026661
theorem B2646611 : Blo 1764083 2646611 := bstep (se 1 (by rfl) ⟨1984958, by rfl⟩ : syracuseStep 2646611 = 3969917) B3969917
theorem B2646641 : Blo 1764083 2646641 := bstep (se 2 (by rfl) ⟨992490, by rfl⟩ : syracuseStep 2646641 = 1984981) B1984981
theorem B2646659 : Blo 1764083 2646659 := bstep (se 1 (by rfl) ⟨1984994, by rfl⟩ : syracuseStep 2646659 = 3969989) B3969989
theorem B2646689 : Blo 1764083 2646689 := bstep (se 2 (by rfl) ⟨992508, by rfl⟩ : syracuseStep 2646689 = 1985017) B1985017
theorem B2646707 : Blo 1764083 2646707 := bstep (se 1 (by rfl) ⟨1985030, by rfl⟩ : syracuseStep 2646707 = 3970061) B3970061
theorem B2646737 : Blo 1764083 2646737 := bstep (se 2 (by rfl) ⟨992526, by rfl⟩ : syracuseStep 2646737 = 1985053) B1985053
theorem B2646755 : Blo 1764083 2646755 := bstep (se 1 (by rfl) ⟨1985066, by rfl⟩ : syracuseStep 2646755 = 3970133) B3970133
theorem B2646785 : Blo 1764083 2646785 := bstep (se 2 (by rfl) ⟨992544, by rfl⟩ : syracuseStep 2646785 = 1985089) B1985089
theorem B2646803 : Blo 1764083 2646803 := bstep (se 1 (by rfl) ⟨1985102, by rfl⟩ : syracuseStep 2646803 = 3970205) B3970205
theorem B51602197 : Blo 1764083 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B2646833 : Blo 1764083 2646833 := bstep (se 2 (by rfl) ⟨992562, by rfl⟩ : syracuseStep 2646833 = 1985125) B1985125
theorem B2646851 : Blo 1764083 2646851 := bstep (se 1 (by rfl) ⟨1985138, by rfl⟩ : syracuseStep 2646851 = 3970277) B3970277
theorem B4465489 : Blo 1764083 4465489 := bstep (se 2 (by rfl) ⟨1674558, by rfl⟩ : syracuseStep 4465489 = 3349117) B3349117
theorem B2646881 : Blo 1764083 2646881 := bstep (se 2 (by rfl) ⟨992580, by rfl⟩ : syracuseStep 2646881 = 1985161) B1985161
theorem B3351395 : Blo 1764083 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B18121585 : Blo 1764083 18121585 := bstep (se 2 (by rfl) ⟨6795594, by rfl⟩ : syracuseStep 18121585 = 13591189) B13591189
theorem B2646899 : Blo 1764083 2646899 := bstep (se 1 (by rfl) ⟨1985174, by rfl⟩ : syracuseStep 2646899 = 3970349) B3970349
theorem B10331021 : Blo 1764083 10331021 := bstep (se 3 (by rfl) ⟨1937066, by rfl⟩ : syracuseStep 10331021 = 3874133) B3874133
theorem B2646929 : Blo 1764083 2646929 := bstep (se 2 (by rfl) ⟨992598, by rfl⟩ : syracuseStep 2646929 = 1985197) B1985197
theorem B2646947 : Blo 1764083 2646947 := bstep (se 1 (by rfl) ⟨1985210, by rfl⟩ : syracuseStep 2646947 = 3970421) B3970421
theorem B2646977 : Blo 1764083 2646977 := bstep (se 2 (by rfl) ⟨992616, by rfl⟩ : syracuseStep 2646977 = 1985233) B1985233
theorem B2646995 : Blo 1764083 2646995 := bstep (se 1 (by rfl) ⟨1985246, by rfl⟩ : syracuseStep 2646995 = 3970493) B3970493
theorem B2647025 : Blo 1764083 2647025 := bstep (se 2 (by rfl) ⟨992634, by rfl⟩ : syracuseStep 2647025 = 1985269) B1985269
theorem B2647043 : Blo 1764083 2647043 := bstep (se 1 (by rfl) ⟨1985282, by rfl⟩ : syracuseStep 2647043 = 3970565) B3970565
theorem B2647073 : Blo 1764083 2647073 := bstep (se 2 (by rfl) ⟨992652, by rfl⟩ : syracuseStep 2647073 = 1985305) B1985305
theorem B2647091 : Blo 1764083 2647091 := bstep (se 1 (by rfl) ⟨1985318, by rfl⟩ : syracuseStep 2647091 = 3970637) B3970637
theorem B3179587 : Blo 1764083 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B5956685 : Blo 1764083 5956685 := bstep (se 3 (by rfl) ⟨1116878, by rfl⟩ : syracuseStep 5956685 = 2233757) B2233757
theorem B2384977 : Blo 1764083 2384977 := bstep (se 2 (by rfl) ⟨894366, by rfl⟩ : syracuseStep 2384977 = 1788733) B1788733
theorem B2647121 : Blo 1764083 2647121 := bstep (se 2 (by rfl) ⟨992670, by rfl⟩ : syracuseStep 2647121 = 1985341) B1985341
theorem B4465763 : Blo 1764083 4465763 := bstep (se 1 (by rfl) ⟨3349322, by rfl⟩ : syracuseStep 4465763 = 6698645) B6698645
theorem B2647139 : Blo 1764083 2647139 := bstep (se 1 (by rfl) ⟨1985354, by rfl⟩ : syracuseStep 2647139 = 3970709) B3970709
theorem B2647169 : Blo 1764083 2647169 := bstep (se 2 (by rfl) ⟨992688, by rfl⟩ : syracuseStep 2647169 = 1985377) B1985377
theorem B5956739 : Blo 1764083 5956739 := bstep (se 1 (by rfl) ⟨4467554, by rfl⟩ : syracuseStep 5956739 = 8935109) B8935109
theorem B7537805 : Blo 1764083 7537805 := bstep (se 3 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 7537805 = 2826677) B2826677
theorem B2647187 : Blo 1764083 2647187 := bstep (se 1 (by rfl) ⟨1985390, by rfl⟩ : syracuseStep 2647187 = 3970781) B3970781
theorem B2647217 : Blo 1764083 2647217 := bstep (se 2 (by rfl) ⟨992706, by rfl⟩ : syracuseStep 2647217 = 1985413) B1985413
theorem B8938673 : Blo 1764083 8938673 := bstep (se 2 (by rfl) ⟨3352002, by rfl⟩ : syracuseStep 8938673 = 6704005) B6704005
theorem B2647235 : Blo 1764083 2647235 := bstep (se 1 (by rfl) ⟨1985426, by rfl⟩ : syracuseStep 2647235 = 3970853) B3970853
theorem B2647265 : Blo 1764083 2647265 := bstep (se 2 (by rfl) ⟨992724, by rfl⟩ : syracuseStep 2647265 = 1985449) B1985449
theorem B2647283 : Blo 1764083 2647283 := bstep (se 1 (by rfl) ⟨1985462, by rfl⟩ : syracuseStep 2647283 = 3970925) B3970925
theorem B2647313 : Blo 1764083 2647313 := bstep (se 2 (by rfl) ⟨992742, by rfl⟩ : syracuseStep 2647313 = 1985485) B1985485
theorem B4465955 : Blo 1764083 4465955 := bstep (se 1 (by rfl) ⟨3349466, by rfl⟩ : syracuseStep 4465955 = 6698933) B6698933
theorem B2647331 : Blo 1764083 2647331 := bstep (se 1 (by rfl) ⟨1985498, by rfl⟩ : syracuseStep 2647331 = 3970997) B3970997
theorem B2647361 : Blo 1764083 2647361 := bstep (se 2 (by rfl) ⟨992760, by rfl⟩ : syracuseStep 2647361 = 1985521) B1985521
theorem B2647379 : Blo 1764083 2647379 := bstep (se 1 (by rfl) ⟨1985534, by rfl⟩ : syracuseStep 2647379 = 3971069) B3971069
theorem B2647409 : Blo 1764083 2647409 := bstep (se 2 (by rfl) ⟨992778, by rfl⟩ : syracuseStep 2647409 = 1985557) B1985557
theorem B5653891 : Blo 1764083 5653891 := bstep (se 1 (by rfl) ⟨4240418, by rfl⟩ : syracuseStep 5653891 = 8480837) B8480837
theorem B2647427 : Blo 1764083 2647427 := bstep (se 1 (by rfl) ⟨1985570, by rfl⟩ : syracuseStep 2647427 = 3971141) B3971141
theorem B2827651 : Blo 1764083 2827651 := bstep (se 1 (by rfl) ⟨2120738, by rfl⟩ : syracuseStep 2827651 = 4241477) B4241477
theorem B5957009 : Blo 1764083 5957009 := bstep (se 2 (by rfl) ⟨2233878, by rfl⟩ : syracuseStep 5957009 = 4467757) B4467757
theorem B2647457 : Blo 1764083 2647457 := bstep (se 2 (by rfl) ⟨992796, by rfl⟩ : syracuseStep 2647457 = 1985593) B1985593
theorem B2647475 : Blo 1764083 2647475 := bstep (se 1 (by rfl) ⟨1985606, by rfl⟩ : syracuseStep 2647475 = 3971213) B3971213
theorem B2647505 : Blo 1764083 2647505 := bstep (se 2 (by rfl) ⟨992814, by rfl⟩ : syracuseStep 2647505 = 1985629) B1985629
theorem B2647523 : Blo 1764083 2647523 := bstep (se 1 (by rfl) ⟨1985642, by rfl⟩ : syracuseStep 2647523 = 3971285) B3971285
theorem B2647553 : Blo 1764083 2647553 := bstep (se 2 (by rfl) ⟨992832, by rfl⟩ : syracuseStep 2647553 = 1985665) B1985665
theorem B9537029 : Blo 1764083 9537029 := bstep (se 4 (by rfl) ⟨894096, by rfl⟩ : syracuseStep 9537029 = 1788193) B1788193
theorem B5654033 : Blo 1764083 5654033 := bstep (se 2 (by rfl) ⟨2120262, by rfl⟩ : syracuseStep 5654033 = 4240525) B4240525
theorem B2647571 : Blo 1764083 2647571 := bstep (se 1 (by rfl) ⟨1985678, by rfl⟩ : syracuseStep 2647571 = 3971357) B3971357
theorem B2647601 : Blo 1764083 2647601 := bstep (se 2 (by rfl) ⟨992850, by rfl⟩ : syracuseStep 2647601 = 1985701) B1985701
theorem B2647619 : Blo 1764083 2647619 := bstep (se 1 (by rfl) ⟨1985714, by rfl⟩ : syracuseStep 2647619 = 3971429) B3971429
theorem B6039107 : Blo 1764083 6039107 := bstep (se 1 (by rfl) ⟨4529330, by rfl⟩ : syracuseStep 6039107 = 9058661) B9058661
theorem B2647649 : Blo 1764083 2647649 := bstep (se 2 (by rfl) ⟨992868, by rfl⟩ : syracuseStep 2647649 = 1985737) B1985737
theorem B96609905 : Blo 1764083 96609905 := bstep (se 2 (by rfl) ⟨36228714, by rfl⟩ : syracuseStep 96609905 = 72457429) B72457429
theorem B2647667 : Blo 1764083 2647667 := bstep (se 1 (by rfl) ⟨1985750, by rfl⟩ : syracuseStep 2647667 = 3971501) B3971501
theorem B4023953 : Blo 1764083 4023953 := bstep (se 2 (by rfl) ⟨1508982, by rfl⟩ : syracuseStep 4023953 = 3017965) B3017965
theorem B2647697 : Blo 1764083 2647697 := bstep (se 2 (by rfl) ⟨992886, by rfl⟩ : syracuseStep 2647697 = 1985773) B1985773
theorem B2647715 : Blo 1764083 2647715 := bstep (se 1 (by rfl) ⟨1985786, by rfl⟩ : syracuseStep 2647715 = 3971573) B3971573
theorem B2647745 : Blo 1764083 2647745 := bstep (se 2 (by rfl) ⟨992904, by rfl⟩ : syracuseStep 2647745 = 1985809) B1985809
theorem B3180227 : Blo 1764083 3180227 := bstep (se 1 (by rfl) ⟨2385170, by rfl⟩ : syracuseStep 3180227 = 4770341) B4770341
theorem B2647763 : Blo 1764083 2647763 := bstep (se 1 (by rfl) ⟨1985822, by rfl⟩ : syracuseStep 2647763 = 3971645) B3971645
theorem B2647793 : Blo 1764083 2647793 := bstep (se 2 (by rfl) ⟨992922, by rfl⟩ : syracuseStep 2647793 = 1985845) B1985845
theorem B2647811 : Blo 1764083 2647811 := bstep (se 1 (by rfl) ⟨1985858, by rfl⟩ : syracuseStep 2647811 = 3971717) B3971717
theorem B7251725 : Blo 1764083 7251725 := bstep (se 3 (by rfl) ⟨1359698, by rfl⟩ : syracuseStep 7251725 = 2719397) B2719397
theorem B3352337 : Blo 1764083 3352337 := bstep (se 2 (by rfl) ⟨1257126, by rfl⟩ : syracuseStep 3352337 = 2514253) B2514253
theorem B2647841 : Blo 1764083 2647841 := bstep (se 2 (by rfl) ⟨992940, by rfl⟩ : syracuseStep 2647841 = 1985881) B1985881
theorem B2647859 : Blo 1764083 2647859 := bstep (se 1 (by rfl) ⟨1985894, by rfl⟩ : syracuseStep 2647859 = 3971789) B3971789
theorem B2828099 : Blo 1764083 2828099 := bstep (se 1 (by rfl) ⟨2121074, by rfl⟩ : syracuseStep 2828099 = 4242149) B4242149
theorem B11462477 : Blo 1764083 11462477 := bstep (se 3 (by rfl) ⟨2149214, by rfl⟩ : syracuseStep 11462477 = 4298429) B4298429
theorem B2647889 : Blo 1764083 2647889 := bstep (se 2 (by rfl) ⟨992958, by rfl⟩ : syracuseStep 2647889 = 1985917) B1985917
theorem B2647907 : Blo 1764083 2647907 := bstep (se 1 (by rfl) ⟨1985930, by rfl⟩ : syracuseStep 2647907 = 3971861) B3971861
theorem B3180401 : Blo 1764083 3180401 := bstep (se 2 (by rfl) ⟨1192650, by rfl⟩ : syracuseStep 3180401 = 2385301) B2385301
theorem B2647937 : Blo 1764083 2647937 := bstep (se 2 (by rfl) ⟨992976, by rfl⟩ : syracuseStep 2647937 = 1985953) B1985953
theorem B2647955 : Blo 1764083 2647955 := bstep (se 1 (by rfl) ⟨1985966, by rfl⟩ : syracuseStep 2647955 = 3971933) B3971933
theorem B5957549 : Blo 1764083 5957549 := bstep (se 3 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 5957549 = 2234081) B2234081
theorem B2647985 : Blo 1764083 2647985 := bstep (se 2 (by rfl) ⟨992994, by rfl⟩ : syracuseStep 2647985 = 1985989) B1985989
theorem B2648003 : Blo 1764083 2648003 := bstep (se 1 (by rfl) ⟨1986002, by rfl⟩ : syracuseStep 2648003 = 3972005) B3972005
theorem B16107461 : Blo 1764083 16107461 := bstep (se 4 (by rfl) ⟨1510074, by rfl⟩ : syracuseStep 16107461 = 3020149) B3020149
theorem B2648033 : Blo 1764083 2648033 := bstep (se 2 (by rfl) ⟨993012, by rfl⟩ : syracuseStep 2648033 = 1986025) B1986025
theorem B5957603 : Blo 1764083 5957603 := bstep (se 1 (by rfl) ⟨4468202, by rfl⟩ : syracuseStep 5957603 = 8936405) B8936405
theorem B2648051 : Blo 1764083 2648051 := bstep (se 1 (by rfl) ⟨1986038, by rfl⟩ : syracuseStep 2648051 = 3972077) B3972077
theorem B2648081 : Blo 1764083 2648081 := bstep (se 2 (by rfl) ⟨993030, by rfl⟩ : syracuseStep 2648081 = 1986061) B1986061
theorem B2648099 : Blo 1764083 2648099 := bstep (se 1 (by rfl) ⟨1986074, by rfl⟩ : syracuseStep 2648099 = 3972149) B3972149
theorem B9062435 : Blo 1764083 9062435 := bstep (se 1 (by rfl) ⟨6796826, by rfl⟩ : syracuseStep 9062435 = 13593653) B13593653
theorem B2648129 : Blo 1764083 2648129 := bstep (se 2 (by rfl) ⟨993048, by rfl⟩ : syracuseStep 2648129 = 1986097) B1986097
theorem B2648147 : Blo 1764083 2648147 := bstep (se 1 (by rfl) ⟨1986110, by rfl⟩ : syracuseStep 2648147 = 3972221) B3972221
theorem B2648177 : Blo 1764083 2648177 := bstep (se 2 (by rfl) ⟨993066, by rfl⟩ : syracuseStep 2648177 = 1986133) B1986133
theorem B2648195 : Blo 1764083 2648195 := bstep (se 1 (by rfl) ⟨1986146, by rfl⟩ : syracuseStep 2648195 = 3972293) B3972293
theorem B3180689 : Blo 1764083 3180689 := bstep (se 2 (by rfl) ⟨1192758, by rfl⟩ : syracuseStep 3180689 = 2385517) B2385517
theorem B2648225 : Blo 1764083 2648225 := bstep (se 2 (by rfl) ⟨993084, by rfl⟩ : syracuseStep 2648225 = 1986169) B1986169
theorem B1984675 : Blo 1764083 1984675 := bstep (se 1 (by rfl) ⟨1488506, by rfl⟩ : syracuseStep 1984675 = 2977013) B2977013
theorem B3819683 : Blo 1764083 3819683 := bstep (se 1 (by rfl) ⟨2864762, by rfl⟩ : syracuseStep 3819683 = 5729525) B5729525
theorem B2648243 : Blo 1764083 2648243 := bstep (se 1 (by rfl) ⟨1986182, by rfl⟩ : syracuseStep 2648243 = 3972365) B3972365
theorem B4466897 : Blo 1764083 4466897 := bstep (se 2 (by rfl) ⟨1675086, by rfl⟩ : syracuseStep 4466897 = 3350173) B3350173
theorem B2648273 : Blo 1764083 2648273 := bstep (se 2 (by rfl) ⟨993102, by rfl⟩ : syracuseStep 2648273 = 1986205) B1986205
theorem B2648291 : Blo 1764083 2648291 := bstep (se 1 (by rfl) ⟨1986218, by rfl⟩ : syracuseStep 2648291 = 3972437) B3972437
theorem B5957873 : Blo 1764083 5957873 := bstep (se 2 (by rfl) ⟨2234202, by rfl⟩ : syracuseStep 5957873 = 4468405) B4468405
theorem B2648321 : Blo 1764083 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B4466947 : Blo 1764083 4466947 := bstep (se 1 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 4466947 = 6700421) B6700421
theorem B11307269 : Blo 1764083 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B2648339 : Blo 1764083 2648339 := bstep (se 1 (by rfl) ⟨1986254, by rfl⟩ : syracuseStep 2648339 = 3972509) B3972509
theorem B2648369 : Blo 1764083 2648369 := bstep (se 2 (by rfl) ⟨993138, by rfl⟩ : syracuseStep 2648369 = 1986277) B1986277
theorem B1984819 : Blo 1764083 1984819 := bstep (se 1 (by rfl) ⟨1488614, by rfl⟩ : syracuseStep 1984819 = 2977229) B2977229
theorem B2648387 : Blo 1764083 2648387 := bstep (se 1 (by rfl) ⟨1986290, by rfl⟩ : syracuseStep 2648387 = 3972581) B3972581
theorem B2648417 : Blo 1764083 2648417 := bstep (se 2 (by rfl) ⟨993156, by rfl⟩ : syracuseStep 2648417 = 1986313) B1986313
theorem B2828657 : Blo 1764083 2828657 := bstep (se 2 (by rfl) ⟨1060746, by rfl⟩ : syracuseStep 2828657 = 2121493) B2121493
theorem B2648435 : Blo 1764083 2648435 := bstep (se 1 (by rfl) ⟨1986326, by rfl⟩ : syracuseStep 2648435 = 3972653) B3972653
theorem B4467089 : Blo 1764083 4467089 := bstep (se 2 (by rfl) ⟨1675158, by rfl⟩ : syracuseStep 4467089 = 3350317) B3350317
theorem B2648465 : Blo 1764083 2648465 := bstep (se 2 (by rfl) ⟨993174, by rfl⟩ : syracuseStep 2648465 = 1986349) B1986349
theorem B2648483 : Blo 1764083 2648483 := bstep (se 1 (by rfl) ⟨1986362, by rfl⟩ : syracuseStep 2648483 = 3972725) B3972725
theorem B5024177 : Blo 1764083 5024177 := bstep (se 2 (by rfl) ⟨1884066, by rfl⟩ : syracuseStep 5024177 = 3768133) B3768133
theorem B2648513 : Blo 1764083 2648513 := bstep (se 2 (by rfl) ⟨993192, by rfl⟩ : syracuseStep 2648513 = 1986385) B1986385
theorem B1984963 : Blo 1764083 1984963 := bstep (se 1 (by rfl) ⟨1488722, by rfl⟩ : syracuseStep 1984963 = 2977445) B2977445
theorem B3770833 : Blo 1764083 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B2648531 : Blo 1764083 2648531 := bstep (se 1 (by rfl) ⟨1986398, by rfl⟩ : syracuseStep 2648531 = 3972797) B3972797
theorem B2648561 : Blo 1764083 2648561 := bstep (se 2 (by rfl) ⟨993210, by rfl⟩ : syracuseStep 2648561 = 1986421) B1986421
theorem B2648579 : Blo 1764083 2648579 := bstep (se 1 (by rfl) ⟨1986434, by rfl⟩ : syracuseStep 2648579 = 3972869) B3972869
theorem B2648609 : Blo 1764083 2648609 := bstep (se 2 (by rfl) ⟨993228, by rfl⟩ : syracuseStep 2648609 = 1986457) B1986457
theorem B2648627 : Blo 1764083 2648627 := bstep (se 1 (by rfl) ⟨1986470, by rfl⟩ : syracuseStep 2648627 = 3972941) B3972941
theorem B2648657 : Blo 1764083 2648657 := bstep (se 2 (by rfl) ⟨993246, by rfl⟩ : syracuseStep 2648657 = 1986493) B1986493
theorem B2828881 : Blo 1764083 2828881 := bstep (se 2 (by rfl) ⟨1060830, by rfl⟩ : syracuseStep 2828881 = 2121661) B2121661
theorem B1985107 : Blo 1764083 1985107 := bstep (se 1 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 1985107 = 2977661) B2977661
theorem B2648675 : Blo 1764083 2648675 := bstep (se 1 (by rfl) ⟨1986506, by rfl⟩ : syracuseStep 2648675 = 3973013) B3973013
theorem B8940131 : Blo 1764083 8940131 := bstep (se 1 (by rfl) ⟨6705098, by rfl⟩ : syracuseStep 8940131 = 13410197) B13410197
theorem B2648705 : Blo 1764083 2648705 := bstep (se 2 (by rfl) ⟨993264, by rfl⟩ : syracuseStep 2648705 = 1986529) B1986529
theorem B10054277 : Blo 1764083 10054277 := bstep (se 4 (by rfl) ⟨942588, by rfl⟩ : syracuseStep 10054277 = 1885177) B1885177
theorem B2648723 : Blo 1764083 2648723 := bstep (se 1 (by rfl) ⟨1986542, by rfl⟩ : syracuseStep 2648723 = 3973085) B3973085
theorem B6703793 : Blo 1764083 6703793 := bstep (se 2 (by rfl) ⟨2513922, by rfl⟩ : syracuseStep 6703793 = 5027845) B5027845
theorem B2648753 : Blo 1764083 2648753 := bstep (se 2 (by rfl) ⟨993282, by rfl⟩ : syracuseStep 2648753 = 1986565) B1986565
theorem B19073717 : Blo 1764083 19073717 := bstep (se 5 (by rfl) ⟨894080, by rfl⟩ : syracuseStep 19073717 = 1788161) B1788161
theorem B2648771 : Blo 1764083 2648771 := bstep (se 1 (by rfl) ⟨1986578, by rfl⟩ : syracuseStep 2648771 = 3973157) B3973157
theorem B9546437 : Blo 1764083 9546437 := bstep (se 4 (by rfl) ⟨894978, by rfl⟩ : syracuseStep 9546437 = 1789957) B1789957
theorem B2648801 : Blo 1764083 2648801 := bstep (se 2 (by rfl) ⟨993300, by rfl⟩ : syracuseStep 2648801 = 1986601) B1986601
theorem B1985251 : Blo 1764083 1985251 := bstep (se 1 (by rfl) ⟨1488938, by rfl⟩ : syracuseStep 1985251 = 2977877) B2977877
theorem B1764083 : Blo 1764083 1764083 := bstep (se 1 (by rfl) ⟨1323062, by rfl⟩ : syracuseStep 1764083 = 2646125) B2646125
theorem B2648819 : Blo 1764083 2648819 := bstep (se 1 (by rfl) ⟨1986614, by rfl⟩ : syracuseStep 2648819 = 3973229) B3973229
theorem B1764099 : Blo 1764083 1764099 := bstep (se 1 (by rfl) ⟨1323074, by rfl⟩ : syracuseStep 1764099 = 2646149) B2646149
theorem B5958413 : Blo 1764083 5958413 := bstep (se 3 (by rfl) ⟨1117202, by rfl⟩ : syracuseStep 5958413 = 2234405) B2234405
theorem B2648849 : Blo 1764083 2648849 := bstep (se 2 (by rfl) ⟨993318, by rfl⟩ : syracuseStep 2648849 = 1986637) B1986637
theorem B1764115 : Blo 1764083 1764115 := bstep (se 1 (by rfl) ⟨1323086, by rfl⟩ : syracuseStep 1764115 = 2646173) B2646173
theorem B1764131 : Blo 1764083 1764131 := bstep (se 1 (by rfl) ⟨1323098, by rfl⟩ : syracuseStep 1764131 = 2646197) B2646197
theorem B2648867 : Blo 1764083 2648867 := bstep (se 1 (by rfl) ⟨1986650, by rfl⟩ : syracuseStep 2648867 = 3973301) B3973301
theorem B1764147 : Blo 1764083 1764147 := bstep (se 1 (by rfl) ⟨1323110, by rfl⟩ : syracuseStep 1764147 = 2646221) B2646221
theorem B2648897 : Blo 1764083 2648897 := bstep (se 2 (by rfl) ⟨993336, by rfl⟩ : syracuseStep 2648897 = 1986673) B1986673
theorem B1764163 : Blo 1764083 1764163 := bstep (se 1 (by rfl) ⟨1323122, by rfl⟩ : syracuseStep 1764163 = 2646245) B2646245
theorem B5958467 : Blo 1764083 5958467 := bstep (se 1 (by rfl) ⟨4468850, by rfl⟩ : syracuseStep 5958467 = 8937701) B8937701
theorem B5655377 : Blo 1764083 5655377 := bstep (se 2 (by rfl) ⟨2120766, by rfl⟩ : syracuseStep 5655377 = 4241533) B4241533
theorem B1764179 : Blo 1764083 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B2648915 : Blo 1764083 2648915 := bstep (se 1 (by rfl) ⟨1986686, by rfl⟩ : syracuseStep 2648915 = 3973373) B3973373
theorem B1764195 : Blo 1764083 1764195 := bstep (se 1 (by rfl) ⟨1323146, by rfl⟩ : syracuseStep 1764195 = 2646293) B2646293
theorem B5729137 : Blo 1764083 5729137 := bstep (se 2 (by rfl) ⟨2148426, by rfl⟩ : syracuseStep 5729137 = 4296853) B4296853
theorem B1764211 : Blo 1764083 1764211 := bstep (se 1 (by rfl) ⟨1323158, by rfl⟩ : syracuseStep 1764211 = 2646317) B2646317
theorem B1985395 : Blo 1764083 1985395 := bstep (se 1 (by rfl) ⟨1489046, by rfl⟩ : syracuseStep 1985395 = 2978093) B2978093
theorem B2648945 : Blo 1764083 2648945 := bstep (se 2 (by rfl) ⟨993354, by rfl⟩ : syracuseStep 2648945 = 1986709) B1986709
theorem B1764227 : Blo 1764083 1764227 := bstep (se 1 (by rfl) ⟨1323170, by rfl⟩ : syracuseStep 1764227 = 2646341) B2646341
theorem B2648963 : Blo 1764083 2648963 := bstep (se 1 (by rfl) ⟨1986722, by rfl⟩ : syracuseStep 2648963 = 3973445) B3973445
theorem B1764243 : Blo 1764083 1764243 := bstep (se 1 (by rfl) ⟨1323182, by rfl⟩ : syracuseStep 1764243 = 2646365) B2646365
theorem B2648993 : Blo 1764083 2648993 := bstep (se 2 (by rfl) ⟨993372, by rfl⟩ : syracuseStep 2648993 = 1986745) B1986745
theorem B1764259 : Blo 1764083 1764259 := bstep (se 1 (by rfl) ⟨1323194, by rfl⟩ : syracuseStep 1764259 = 2646389) B2646389
theorem B1764275 : Blo 1764083 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B2649011 : Blo 1764083 2649011 := bstep (se 1 (by rfl) ⟨1986758, by rfl⟩ : syracuseStep 2649011 = 3973517) B3973517
theorem B1764291 : Blo 1764083 1764291 := bstep (se 1 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 1764291 = 2646437) B2646437
theorem B2649041 : Blo 1764083 2649041 := bstep (se 2 (by rfl) ⟨993390, by rfl⟩ : syracuseStep 2649041 = 1986781) B1986781
theorem B1764307 : Blo 1764083 1764307 := bstep (se 1 (by rfl) ⟨1323230, by rfl⟩ : syracuseStep 1764307 = 2646461) B2646461
theorem B1764323 : Blo 1764083 1764323 := bstep (se 1 (by rfl) ⟨1323242, by rfl⟩ : syracuseStep 1764323 = 2646485) B2646485
theorem B2649059 : Blo 1764083 2649059 := bstep (se 1 (by rfl) ⟨1986794, by rfl⟩ : syracuseStep 2649059 = 3973589) B3973589
theorem B1764339 : Blo 1764083 1764339 := bstep (se 1 (by rfl) ⟨1323254, by rfl⟩ : syracuseStep 1764339 = 2646509) B2646509
theorem B2649089 : Blo 1764083 2649089 := bstep (se 2 (by rfl) ⟨993408, by rfl⟩ : syracuseStep 2649089 = 1986817) B1986817
theorem B1764355 : Blo 1764083 1764355 := bstep (se 1 (by rfl) ⟨1323266, by rfl⟩ : syracuseStep 1764355 = 2646533) B2646533
theorem B1985539 : Blo 1764083 1985539 := bstep (se 1 (by rfl) ⟨1489154, by rfl⟩ : syracuseStep 1985539 = 2978309) B2978309
theorem B1764371 : Blo 1764083 1764371 := bstep (se 1 (by rfl) ⟨1323278, by rfl⟩ : syracuseStep 1764371 = 2646557) B2646557
theorem B2649107 : Blo 1764083 2649107 := bstep (se 1 (by rfl) ⟨1986830, by rfl⟩ : syracuseStep 2649107 = 3973661) B3973661
theorem B1764387 : Blo 1764083 1764387 := bstep (se 1 (by rfl) ⟨1323290, by rfl⟩ : syracuseStep 1764387 = 2646581) B2646581
theorem B1764403 : Blo 1764083 1764403 := bstep (se 1 (by rfl) ⟨1323302, by rfl⟩ : syracuseStep 1764403 = 2646605) B2646605
theorem B1764419 : Blo 1764083 1764419 := bstep (se 1 (by rfl) ⟨1323314, by rfl⟩ : syracuseStep 1764419 = 2646629) B2646629
theorem B5958737 : Blo 1764083 5958737 := bstep (se 2 (by rfl) ⟨2234526, by rfl⟩ : syracuseStep 5958737 = 4469053) B4469053
theorem B1764435 : Blo 1764083 1764435 := bstep (se 1 (by rfl) ⟨1323326, by rfl⟩ : syracuseStep 1764435 = 2646653) B2646653
theorem B1764451 : Blo 1764083 1764451 := bstep (se 1 (by rfl) ⟨1323338, by rfl⟩ : syracuseStep 1764451 = 2646677) B2646677
theorem B1764467 : Blo 1764083 1764467 := bstep (se 1 (by rfl) ⟨1323350, by rfl⟩ : syracuseStep 1764467 = 2646701) B2646701
theorem B3017857 : Blo 1764083 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B1764483 : Blo 1764083 1764483 := bstep (se 1 (by rfl) ⟨1323362, by rfl⟩ : syracuseStep 1764483 = 2646725) B2646725
theorem B4770947 : Blo 1764083 4770947 := bstep (se 1 (by rfl) ⟨3578210, by rfl⟩ : syracuseStep 4770947 = 7156421) B7156421
theorem B1764499 : Blo 1764083 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B1985683 : Blo 1764083 1985683 := bstep (se 1 (by rfl) ⟨1489262, by rfl⟩ : syracuseStep 1985683 = 2978525) B2978525
theorem B1764515 : Blo 1764083 1764515 := bstep (se 1 (by rfl) ⟨1323386, by rfl⟩ : syracuseStep 1764515 = 2646773) B2646773
theorem B1764531 : Blo 1764083 1764531 := bstep (se 1 (by rfl) ⟨1323398, by rfl⟩ : syracuseStep 1764531 = 2646797) B2646797
theorem B1764547 : Blo 1764083 1764547 := bstep (se 1 (by rfl) ⟨1323410, by rfl⟩ : syracuseStep 1764547 = 2646821) B2646821
theorem B2976979 : Blo 1764083 2976979 := bstep (se 1 (by rfl) ⟨2232734, by rfl⟩ : syracuseStep 2976979 = 4465469) B4465469
theorem B1764563 : Blo 1764083 1764563 := bstep (se 1 (by rfl) ⟨1323422, by rfl⟩ : syracuseStep 1764563 = 2646845) B2646845
theorem B1764579 : Blo 1764083 1764579 := bstep (se 1 (by rfl) ⟨1323434, by rfl⟩ : syracuseStep 1764579 = 2646869) B2646869
theorem B1764595 : Blo 1764083 1764595 := bstep (se 1 (by rfl) ⟨1323446, by rfl⟩ : syracuseStep 1764595 = 2646893) B2646893
theorem B1764611 : Blo 1764083 1764611 := bstep (se 1 (by rfl) ⟨1323458, by rfl⟩ : syracuseStep 1764611 = 2646917) B2646917
theorem B1764627 : Blo 1764083 1764627 := bstep (se 1 (by rfl) ⟨1323470, by rfl⟩ : syracuseStep 1764627 = 2646941) B2646941
theorem B1764643 : Blo 1764083 1764643 := bstep (se 1 (by rfl) ⟨1323482, by rfl⟩ : syracuseStep 1764643 = 2646965) B2646965
theorem B1985827 : Blo 1764083 1985827 := bstep (se 1 (by rfl) ⟨1489370, by rfl⟩ : syracuseStep 1985827 = 2978741) B2978741
theorem B7154993 : Blo 1764083 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B10054961 : Blo 1764083 10054961 := bstep (se 2 (by rfl) ⟨3770610, by rfl⟩ : syracuseStep 10054961 = 7541221) B7541221
theorem B1764659 : Blo 1764083 1764659 := bstep (se 1 (by rfl) ⟨1323494, by rfl⟩ : syracuseStep 1764659 = 2646989) B2646989
theorem B1764675 : Blo 1764083 1764675 := bstep (se 1 (by rfl) ⟨1323506, by rfl⟩ : syracuseStep 1764675 = 2647013) B2647013
theorem B11619661 : Blo 1764083 11619661 := bstep (se 3 (by rfl) ⟨2178686, by rfl⟩ : syracuseStep 11619661 = 4357373) B4357373
theorem B1764691 : Blo 1764083 1764691 := bstep (se 1 (by rfl) ⟨1323518, by rfl⟩ : syracuseStep 1764691 = 2647037) B2647037
theorem B2977121 : Blo 1764083 2977121 := bstep (se 2 (by rfl) ⟨1116420, by rfl⟩ : syracuseStep 2977121 = 2232841) B2232841
theorem B1764707 : Blo 1764083 1764707 := bstep (se 1 (by rfl) ⟨1323530, by rfl⟩ : syracuseStep 1764707 = 2647061) B2647061
theorem B4468081 : Blo 1764083 4468081 := bstep (se 2 (by rfl) ⟨1675530, by rfl⟩ : syracuseStep 4468081 = 3351061) B3351061
theorem B1764723 : Blo 1764083 1764723 := bstep (se 1 (by rfl) ⟨1323542, by rfl⟩ : syracuseStep 1764723 = 2647085) B2647085
theorem B1764739 : Blo 1764083 1764739 := bstep (se 1 (by rfl) ⟨1323554, by rfl⟩ : syracuseStep 1764739 = 2647109) B2647109
theorem B1764755 : Blo 1764083 1764755 := bstep (se 1 (by rfl) ⟨1323566, by rfl⟩ : syracuseStep 1764755 = 2647133) B2647133
theorem B1764771 : Blo 1764083 1764771 := bstep (se 1 (by rfl) ⟨1323578, by rfl⟩ : syracuseStep 1764771 = 2647157) B2647157
theorem B1764787 : Blo 1764083 1764787 := bstep (se 1 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 1764787 = 2647181) B2647181
theorem B1985971 : Blo 1764083 1985971 := bstep (se 1 (by rfl) ⟨1489478, by rfl⟩ : syracuseStep 1985971 = 2978957) B2978957
theorem B1764803 : Blo 1764083 1764803 := bstep (se 1 (by rfl) ⟨1323602, by rfl⟩ : syracuseStep 1764803 = 2647205) B2647205
theorem B1764819 : Blo 1764083 1764819 := bstep (se 1 (by rfl) ⟨1323614, by rfl⟩ : syracuseStep 1764819 = 2647229) B2647229
theorem B2977249 : Blo 1764083 2977249 := bstep (se 2 (by rfl) ⟨1116468, by rfl⟩ : syracuseStep 2977249 = 2232937) B2232937
theorem B1764835 : Blo 1764083 1764835 := bstep (se 1 (by rfl) ⟨1323626, by rfl⟩ : syracuseStep 1764835 = 2647253) B2647253
theorem B1764851 : Blo 1764083 1764851 := bstep (se 1 (by rfl) ⟨1323638, by rfl⟩ : syracuseStep 1764851 = 2647277) B2647277
theorem B2977283 : Blo 1764083 2977283 := bstep (se 1 (by rfl) ⟨2232962, by rfl⟩ : syracuseStep 2977283 = 4465925) B4465925
theorem B1764867 : Blo 1764083 1764867 := bstep (se 1 (by rfl) ⟨1323650, by rfl⟩ : syracuseStep 1764867 = 2647301) B2647301
theorem B1764883 : Blo 1764083 1764883 := bstep (se 1 (by rfl) ⟨1323662, by rfl⟩ : syracuseStep 1764883 = 2647325) B2647325
theorem B1764899 : Blo 1764083 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B1764915 : Blo 1764083 1764915 := bstep (se 1 (by rfl) ⟨1323686, by rfl⟩ : syracuseStep 1764915 = 2647373) B2647373
theorem B1764931 : Blo 1764083 1764931 := bstep (se 1 (by rfl) ⟨1323698, by rfl⟩ : syracuseStep 1764931 = 2647397) B2647397
theorem B1986115 : Blo 1764083 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B1764947 : Blo 1764083 1764947 := bstep (se 1 (by rfl) ⟨1323710, by rfl⟩ : syracuseStep 1764947 = 2647421) B2647421
theorem B9539171 : Blo 1764083 9539171 := bstep (se 1 (by rfl) ⟨7154378, by rfl⟩ : syracuseStep 9539171 = 14308757) B14308757
theorem B1764963 : Blo 1764083 1764963 := bstep (se 1 (by rfl) ⟨1323722, by rfl⟩ : syracuseStep 1764963 = 2647445) B2647445
theorem B5959277 : Blo 1764083 5959277 := bstep (se 3 (by rfl) ⟨1117364, by rfl⟩ : syracuseStep 5959277 = 2234729) B2234729
theorem B1764979 : Blo 1764083 1764979 := bstep (se 1 (by rfl) ⟨1323734, by rfl⟩ : syracuseStep 1764979 = 2647469) B2647469
theorem B2977411 : Blo 1764083 2977411 := bstep (se 1 (by rfl) ⟨2233058, by rfl⟩ : syracuseStep 2977411 = 4466117) B4466117
theorem B1764995 : Blo 1764083 1764995 := bstep (se 1 (by rfl) ⟨1323746, by rfl⟩ : syracuseStep 1764995 = 2647493) B2647493
theorem B4468355 : Blo 1764083 4468355 := bstep (se 1 (by rfl) ⟨3351266, by rfl⟩ : syracuseStep 4468355 = 6702533) B6702533
theorem B1765011 : Blo 1764083 1765011 := bstep (se 1 (by rfl) ⟨1323758, by rfl⟩ : syracuseStep 1765011 = 2647517) B2647517
theorem B1765027 : Blo 1764083 1765027 := bstep (se 1 (by rfl) ⟨1323770, by rfl⟩ : syracuseStep 1765027 = 2647541) B2647541
theorem B5959331 : Blo 1764083 5959331 := bstep (se 1 (by rfl) ⟨4469498, by rfl⟩ : syracuseStep 5959331 = 8938997) B8938997
theorem B1765043 : Blo 1764083 1765043 := bstep (se 1 (by rfl) ⟨1323782, by rfl⟩ : syracuseStep 1765043 = 2647565) B2647565
theorem B3395267 : Blo 1764083 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B1765059 : Blo 1764083 1765059 := bstep (se 1 (by rfl) ⟨1323794, by rfl⟩ : syracuseStep 1765059 = 2647589) B2647589
theorem B3182275 : Blo 1764083 3182275 := bstep (se 1 (by rfl) ⟨2386706, by rfl⟩ : syracuseStep 3182275 = 4773413) B4773413
theorem B1765075 : Blo 1764083 1765075 := bstep (se 1 (by rfl) ⟨1323806, by rfl⟩ : syracuseStep 1765075 = 2647613) B2647613
theorem B1986259 : Blo 1764083 1986259 := bstep (se 1 (by rfl) ⟨1489694, by rfl⟩ : syracuseStep 1986259 = 2979389) B2979389
theorem B1765091 : Blo 1764083 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B5656301 : Blo 1764083 5656301 := bstep (se 3 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 5656301 = 2121113) B2121113
theorem B1765107 : Blo 1764083 1765107 := bstep (se 1 (by rfl) ⟨1323830, by rfl⟩ : syracuseStep 1765107 = 2647661) B2647661
theorem B1765123 : Blo 1764083 1765123 := bstep (se 1 (by rfl) ⟨1323842, by rfl⟩ : syracuseStep 1765123 = 2647685) B2647685
theorem B2977553 : Blo 1764083 2977553 := bstep (se 2 (by rfl) ⟨1116582, by rfl⟩ : syracuseStep 2977553 = 2233165) B2233165
theorem B1765139 : Blo 1764083 1765139 := bstep (se 1 (by rfl) ⟨1323854, by rfl⟩ : syracuseStep 1765139 = 2647709) B2647709
theorem B2264851 : Blo 1764083 2264851 := bstep (se 1 (by rfl) ⟨1698638, by rfl⟩ : syracuseStep 2264851 = 3397277) B3397277
theorem B3821347 : Blo 1764083 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B1765155 : Blo 1764083 1765155 := bstep (se 1 (by rfl) ⟨1323866, by rfl⟩ : syracuseStep 1765155 = 2647733) B2647733
theorem B1765171 : Blo 1764083 1765171 := bstep (se 1 (by rfl) ⟨1323878, by rfl⟩ : syracuseStep 1765171 = 2647757) B2647757
theorem B1765187 : Blo 1764083 1765187 := bstep (se 1 (by rfl) ⟨1323890, by rfl⟩ : syracuseStep 1765187 = 2647781) B2647781
theorem B4468547 : Blo 1764083 4468547 := bstep (se 1 (by rfl) ⟨3351410, by rfl⟩ : syracuseStep 4468547 = 6702821) B6702821
theorem B1765203 : Blo 1764083 1765203 := bstep (se 1 (by rfl) ⟨1323902, by rfl⟩ : syracuseStep 1765203 = 2647805) B2647805
theorem B5025635 : Blo 1764083 5025635 := bstep (se 1 (by rfl) ⟨3769226, by rfl⟩ : syracuseStep 5025635 = 7538453) B7538453
theorem B1765219 : Blo 1764083 1765219 := bstep (se 1 (by rfl) ⟨1323914, by rfl⟩ : syracuseStep 1765219 = 2647829) B2647829
theorem B1986403 : Blo 1764083 1986403 := bstep (se 1 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 1986403 = 2979605) B2979605
theorem B1765235 : Blo 1764083 1765235 := bstep (se 1 (by rfl) ⟨1323926, by rfl⟩ : syracuseStep 1765235 = 2647853) B2647853
theorem B1765251 : Blo 1764083 1765251 := bstep (se 1 (by rfl) ⟨1323938, by rfl⟩ : syracuseStep 1765251 = 2647877) B2647877
theorem B2977681 : Blo 1764083 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1765267 : Blo 1764083 1765267 := bstep (se 1 (by rfl) ⟨1323950, by rfl⟩ : syracuseStep 1765267 = 2647901) B2647901
theorem B1765283 : Blo 1764083 1765283 := bstep (se 1 (by rfl) ⟨1323962, by rfl⟩ : syracuseStep 1765283 = 2647925) B2647925
theorem B5656493 : Blo 1764083 5656493 := bstep (se 3 (by rfl) ⟨1060592, by rfl⟩ : syracuseStep 5656493 = 2121185) B2121185
theorem B5959601 : Blo 1764083 5959601 := bstep (se 2 (by rfl) ⟨2234850, by rfl⟩ : syracuseStep 5959601 = 4469701) B4469701
theorem B2977715 : Blo 1764083 2977715 := bstep (se 1 (by rfl) ⟨2233286, by rfl⟩ : syracuseStep 2977715 = 4466573) B4466573
theorem B1765299 : Blo 1764083 1765299 := bstep (se 1 (by rfl) ⟨1323974, by rfl⟩ : syracuseStep 1765299 = 2647949) B2647949
theorem B1765315 : Blo 1764083 1765315 := bstep (se 1 (by rfl) ⟨1323986, by rfl⟩ : syracuseStep 1765315 = 2647973) B2647973
theorem B3821521 : Blo 1764083 3821521 := bstep (se 2 (by rfl) ⟨1433070, by rfl⟩ : syracuseStep 3821521 = 2866141) B2866141
theorem B1765331 : Blo 1764083 1765331 := bstep (se 1 (by rfl) ⟨1323998, by rfl⟩ : syracuseStep 1765331 = 2647997) B2647997
theorem B14503907 : Blo 1764083 14503907 := bstep (se 1 (by rfl) ⟨10877930, by rfl⟩ : syracuseStep 14503907 = 21755861) B21755861
theorem B1765347 : Blo 1764083 1765347 := bstep (se 1 (by rfl) ⟨1324010, by rfl⟩ : syracuseStep 1765347 = 2648021) B2648021
theorem B1765363 : Blo 1764083 1765363 := bstep (se 1 (by rfl) ⟨1324022, by rfl⟩ : syracuseStep 1765363 = 2648045) B2648045
theorem B1986547 : Blo 1764083 1986547 := bstep (se 1 (by rfl) ⟨1489910, by rfl⟩ : syracuseStep 1986547 = 2979821) B2979821
theorem B1765379 : Blo 1764083 1765379 := bstep (se 1 (by rfl) ⟨1324034, by rfl⟩ : syracuseStep 1765379 = 2648069) B2648069
theorem B20107277 : Blo 1764083 20107277 := bstep (se 3 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 20107277 = 7540229) B7540229
theorem B1765395 : Blo 1764083 1765395 := bstep (se 1 (by rfl) ⟨1324046, by rfl⟩ : syracuseStep 1765395 = 2648093) B2648093
theorem B1765411 : Blo 1764083 1765411 := bstep (se 1 (by rfl) ⟨1324058, by rfl⟩ : syracuseStep 1765411 = 2648117) B2648117
theorem B2977843 : Blo 1764083 2977843 := bstep (se 1 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 2977843 = 4466765) B4466765
theorem B1765427 : Blo 1764083 1765427 := bstep (se 1 (by rfl) ⟨1324070, by rfl⟩ : syracuseStep 1765427 = 2648141) B2648141
theorem B1765443 : Blo 1764083 1765443 := bstep (se 1 (by rfl) ⟨1324082, by rfl⟩ : syracuseStep 1765443 = 2648165) B2648165
theorem B1765459 : Blo 1764083 1765459 := bstep (se 1 (by rfl) ⟨1324094, by rfl⟩ : syracuseStep 1765459 = 2648189) B2648189
theorem B1765475 : Blo 1764083 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B6705251 : Blo 1764083 6705251 := bstep (se 1 (by rfl) ⟨5028938, by rfl⟩ : syracuseStep 6705251 = 10057877) B10057877
theorem B8933489 : Blo 1764083 8933489 := bstep (se 2 (by rfl) ⟨3350058, by rfl⟩ : syracuseStep 8933489 = 6700117) B6700117
theorem B1765491 : Blo 1764083 1765491 := bstep (se 1 (by rfl) ⟨1324118, by rfl⟩ : syracuseStep 1765491 = 2648237) B2648237
theorem B1765507 : Blo 1764083 1765507 := bstep (se 1 (by rfl) ⟨1324130, by rfl⟩ : syracuseStep 1765507 = 2648261) B2648261
theorem B1986691 : Blo 1764083 1986691 := bstep (se 1 (by rfl) ⟨1490018, by rfl⟩ : syracuseStep 1986691 = 2980037) B2980037
theorem B1765523 : Blo 1764083 1765523 := bstep (se 1 (by rfl) ⟨1324142, by rfl⟩ : syracuseStep 1765523 = 2648285) B2648285
theorem B11309219 : Blo 1764083 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B1765539 : Blo 1764083 1765539 := bstep (se 1 (by rfl) ⟨1324154, by rfl⟩ : syracuseStep 1765539 = 2648309) B2648309
theorem B7540913 : Blo 1764083 7540913 := bstep (se 2 (by rfl) ⟨2827842, by rfl⟩ : syracuseStep 7540913 = 5655685) B5655685
theorem B1765555 : Blo 1764083 1765555 := bstep (se 1 (by rfl) ⟨1324166, by rfl⟩ : syracuseStep 1765555 = 2648333) B2648333
theorem B2977985 : Blo 1764083 2977985 := bstep (se 2 (by rfl) ⟨1116744, by rfl⟩ : syracuseStep 2977985 = 2233489) B2233489
theorem B1765571 : Blo 1764083 1765571 := bstep (se 1 (by rfl) ⟨1324178, by rfl⟩ : syracuseStep 1765571 = 2648357) B2648357
theorem B3969233 : Blo 1764083 3969233 := bstep (se 2 (by rfl) ⟨1488462, by rfl⟩ : syracuseStep 3969233 = 2976925) B2976925
theorem B1765587 : Blo 1764083 1765587 := bstep (se 1 (by rfl) ⟨1324190, by rfl⟩ : syracuseStep 1765587 = 2648381) B2648381
theorem B3969251 : Blo 1764083 3969251 := bstep (se 1 (by rfl) ⟨2976938, by rfl⟩ : syracuseStep 3969251 = 5953877) B5953877
theorem B1765603 : Blo 1764083 1765603 := bstep (se 1 (by rfl) ⟨1324202, by rfl⟩ : syracuseStep 1765603 = 2648405) B2648405
theorem B1765619 : Blo 1764083 1765619 := bstep (se 1 (by rfl) ⟨1324214, by rfl⟩ : syracuseStep 1765619 = 2648429) B2648429
theorem B1765635 : Blo 1764083 1765635 := bstep (se 1 (by rfl) ⟨1324226, by rfl⟩ : syracuseStep 1765635 = 2648453) B2648453
theorem B1765651 : Blo 1764083 1765651 := bstep (se 1 (by rfl) ⟨1324238, by rfl⟩ : syracuseStep 1765651 = 2648477) B2648477
theorem B1986835 : Blo 1764083 1986835 := bstep (se 1 (by rfl) ⟨1490126, by rfl⟩ : syracuseStep 1986835 = 2980253) B2980253
theorem B1765667 : Blo 1764083 1765667 := bstep (se 1 (by rfl) ⟨1324250, by rfl⟩ : syracuseStep 1765667 = 2648501) B2648501
theorem B1765683 : Blo 1764083 1765683 := bstep (se 1 (by rfl) ⟨1324262, by rfl⟩ : syracuseStep 1765683 = 2648525) B2648525
theorem B2978113 : Blo 1764083 2978113 := bstep (se 2 (by rfl) ⟨1116792, by rfl⟩ : syracuseStep 2978113 = 2233585) B2233585
theorem B1765699 : Blo 1764083 1765699 := bstep (se 1 (by rfl) ⟨1324274, by rfl⟩ : syracuseStep 1765699 = 2648549) B2648549
theorem B1765715 : Blo 1764083 1765715 := bstep (se 1 (by rfl) ⟨1324286, by rfl⟩ : syracuseStep 1765715 = 2648573) B2648573
theorem B2978147 : Blo 1764083 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B1765731 : Blo 1764083 1765731 := bstep (se 1 (by rfl) ⟨1324298, by rfl⟩ : syracuseStep 1765731 = 2648597) B2648597
theorem B12898673 : Blo 1764083 12898673 := bstep (se 2 (by rfl) ⟨4837002, by rfl⟩ : syracuseStep 12898673 = 9674005) B9674005
theorem B1765747 : Blo 1764083 1765747 := bstep (se 1 (by rfl) ⟨1324310, by rfl⟩ : syracuseStep 1765747 = 2648621) B2648621
theorem B1765763 : Blo 1764083 1765763 := bstep (se 1 (by rfl) ⟨1324322, by rfl⟩ : syracuseStep 1765763 = 2648645) B2648645
theorem B1765779 : Blo 1764083 1765779 := bstep (se 1 (by rfl) ⟨1324334, by rfl⟩ : syracuseStep 1765779 = 2648669) B2648669
theorem B5960195 : Blo 1764083 5960195 := bstep (se 1 (by rfl) ⟨4470146, by rfl⟩ : syracuseStep 5960195 = 8940293) B8940293
theorem B1765795 : Blo 1764083 1765795 := bstep (se 1 (by rfl) ⟨1324346, by rfl⟩ : syracuseStep 1765795 = 2648693) B2648693
theorem B1765811 : Blo 1764083 1765811 := bstep (se 1 (by rfl) ⟨1324358, by rfl⟩ : syracuseStep 1765811 = 2648717) B2648717
theorem B1765827 : Blo 1764083 1765827 := bstep (se 1 (by rfl) ⟨1324370, by rfl⟩ : syracuseStep 1765827 = 2648741) B2648741
theorem B5960141 : Blo 1764083 5960141 := bstep (se 3 (by rfl) ⟨1117526, by rfl⟩ : syracuseStep 5960141 = 2235053) B2235053
theorem B1765843 : Blo 1764083 1765843 := bstep (se 1 (by rfl) ⟨1324382, by rfl⟩ : syracuseStep 1765843 = 2648765) B2648765
theorem B2978275 : Blo 1764083 2978275 := bstep (se 1 (by rfl) ⟨2233706, by rfl⟩ : syracuseStep 2978275 = 4467413) B4467413
theorem B1765859 : Blo 1764083 1765859 := bstep (se 1 (by rfl) ⟨1324394, by rfl⟩ : syracuseStep 1765859 = 2648789) B2648789
theorem B3969521 : Blo 1764083 3969521 := bstep (se 2 (by rfl) ⟨1488570, by rfl⟩ : syracuseStep 3969521 = 2977141) B2977141
theorem B1765875 : Blo 1764083 1765875 := bstep (se 1 (by rfl) ⟨1324406, by rfl⟩ : syracuseStep 1765875 = 2648813) B2648813
theorem B3969539 : Blo 1764083 3969539 := bstep (se 1 (by rfl) ⟨2977154, by rfl⟩ : syracuseStep 3969539 = 5954309) B5954309
theorem B1765891 : Blo 1764083 1765891 := bstep (se 1 (by rfl) ⟨1324418, by rfl⟩ : syracuseStep 1765891 = 2648837) B2648837
theorem B1765907 : Blo 1764083 1765907 := bstep (se 1 (by rfl) ⟨1324430, by rfl⟩ : syracuseStep 1765907 = 2648861) B2648861
theorem B1765923 : Blo 1764083 1765923 := bstep (se 1 (by rfl) ⟨1324442, by rfl⟩ : syracuseStep 1765923 = 2648885) B2648885
theorem B1765939 : Blo 1764083 1765939 := bstep (se 1 (by rfl) ⟨1324454, by rfl⟩ : syracuseStep 1765939 = 2648909) B2648909
theorem B1765955 : Blo 1764083 1765955 := bstep (se 1 (by rfl) ⟨1324466, by rfl⟩ : syracuseStep 1765955 = 2648933) B2648933
theorem B1765971 : Blo 1764083 1765971 := bstep (se 1 (by rfl) ⟨1324478, by rfl⟩ : syracuseStep 1765971 = 2648957) B2648957
theorem B1765987 : Blo 1764083 1765987 := bstep (se 1 (by rfl) ⟨1324490, by rfl⟩ : syracuseStep 1765987 = 2648981) B2648981
theorem B2978417 : Blo 1764083 2978417 := bstep (se 2 (by rfl) ⟨1116906, by rfl⟩ : syracuseStep 2978417 = 2233813) B2233813
theorem B2232947 : Blo 1764083 2232947 := bstep (se 1 (by rfl) ⟨1674710, by rfl⟩ : syracuseStep 2232947 = 3349421) B3349421
theorem B1766003 : Blo 1764083 1766003 := bstep (se 1 (by rfl) ⟨1324502, by rfl⟩ : syracuseStep 1766003 = 2649005) B2649005
theorem B1766019 : Blo 1764083 1766019 := bstep (se 1 (by rfl) ⟨1324514, by rfl⟩ : syracuseStep 1766019 = 2649029) B2649029
theorem B5026445 : Blo 1764083 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B1766035 : Blo 1764083 1766035 := bstep (se 1 (by rfl) ⟨1324526, by rfl⟩ : syracuseStep 1766035 = 2649053) B2649053
theorem B1766051 : Blo 1764083 1766051 := bstep (se 1 (by rfl) ⟨1324538, by rfl⟩ : syracuseStep 1766051 = 2649077) B2649077
theorem B1766067 : Blo 1764083 1766067 := bstep (se 1 (by rfl) ⟨1324550, by rfl⟩ : syracuseStep 1766067 = 2649101) B2649101
theorem B1766083 : Blo 1764083 1766083 := bstep (se 1 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 1766083 = 2649125) B2649125
theorem B10056419 : Blo 1764083 10056419 := bstep (se 1 (by rfl) ⟨7542314, by rfl⟩ : syracuseStep 10056419 = 15084629) B15084629
theorem B2978545 : Blo 1764083 2978545 := bstep (se 2 (by rfl) ⟨1116954, by rfl⟩ : syracuseStep 2978545 = 2233909) B2233909
theorem B4469489 : Blo 1764083 4469489 := bstep (se 2 (by rfl) ⟨1676058, by rfl⟩ : syracuseStep 4469489 = 3352117) B3352117
theorem B3969809 : Blo 1764083 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B5960465 : Blo 1764083 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B2978579 : Blo 1764083 2978579 := bstep (se 1 (by rfl) ⟨2233934, by rfl⟩ : syracuseStep 2978579 = 4467869) B4467869
theorem B3969827 : Blo 1764083 3969827 := bstep (se 1 (by rfl) ⟨2977370, by rfl⟩ : syracuseStep 3969827 = 5954741) B5954741
theorem B4469539 : Blo 1764083 4469539 := bstep (se 1 (by rfl) ⟨3352154, by rfl⟩ : syracuseStep 4469539 = 6704309) B6704309
theorem B5026637 : Blo 1764083 5026637 := bstep (se 3 (by rfl) ⟨942494, by rfl⟩ : syracuseStep 5026637 = 1884989) B1884989
theorem B16094065 : Blo 1764083 16094065 := bstep (se 2 (by rfl) ⟨6035274, by rfl⟩ : syracuseStep 16094065 = 12070549) B12070549
theorem B2978707 : Blo 1764083 2978707 := bstep (se 1 (by rfl) ⟨2234030, by rfl⟩ : syracuseStep 2978707 = 4468061) B4468061
theorem B4469681 : Blo 1764083 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B2978849 : Blo 1764083 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B3970097 : Blo 1764083 3970097 := bstep (se 2 (by rfl) ⟨1488786, by rfl⟩ : syracuseStep 3970097 = 2977573) B2977573
theorem B9057329 : Blo 1764083 9057329 := bstep (se 2 (by rfl) ⟨3396498, by rfl⟩ : syracuseStep 9057329 = 6792997) B6792997
theorem B3970115 : Blo 1764083 3970115 := bstep (se 1 (by rfl) ⟨2977586, by rfl⟩ : syracuseStep 3970115 = 5955173) B5955173
theorem B3396689 : Blo 1764083 3396689 := bstep (se 2 (by rfl) ⟨1273758, by rfl⟩ : syracuseStep 3396689 = 2547517) B2547517
theorem B2978977 : Blo 1764083 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B2979011 : Blo 1764083 2979011 := bstep (se 1 (by rfl) ⟨2234258, by rfl⟩ : syracuseStep 2979011 = 4468517) B4468517
theorem B2512129 : Blo 1764083 2512129 := bstep (se 2 (by rfl) ⟨942048, by rfl⟩ : syracuseStep 2512129 = 1884097) B1884097
theorem B10736945 : Blo 1764083 10736945 := bstep (se 2 (by rfl) ⟨4026354, by rfl⟩ : syracuseStep 10736945 = 8052709) B8052709
theorem B2233651 : Blo 1764083 2233651 := bstep (se 1 (by rfl) ⟨1675238, by rfl⟩ : syracuseStep 2233651 = 3350477) B3350477
theorem B2979139 : Blo 1764083 2979139 := bstep (se 1 (by rfl) ⟨2234354, by rfl⟩ : syracuseStep 2979139 = 4468709) B4468709
theorem B4027715 : Blo 1764083 4027715 := bstep (se 1 (by rfl) ⟨3020786, by rfl⟩ : syracuseStep 4027715 = 6041573) B6041573
theorem B17659205 : Blo 1764083 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B3970385 : Blo 1764083 3970385 := bstep (se 2 (by rfl) ⟨1488894, by rfl⟩ : syracuseStep 3970385 = 2977789) B2977789
theorem B2512225 : Blo 1764083 2512225 := bstep (se 2 (by rfl) ⟨942084, by rfl⟩ : syracuseStep 2512225 = 1884169) B1884169
theorem B3970403 : Blo 1764083 3970403 := bstep (se 1 (by rfl) ⟨2977802, by rfl⟩ : syracuseStep 3970403 = 5955605) B5955605
theorem B12719501 : Blo 1764083 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B2233747 : Blo 1764083 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B9541027 : Blo 1764083 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B7542179 : Blo 1764083 7542179 := bstep (se 1 (by rfl) ⟨5656634, by rfl⟩ : syracuseStep 7542179 = 11313269) B11313269
theorem B2979281 : Blo 1764083 2979281 := bstep (se 2 (by rfl) ⟨1117230, by rfl⟩ : syracuseStep 2979281 = 2234461) B2234461
theorem B2684449 : Blo 1764083 2684449 := bstep (se 2 (by rfl) ⟨1006668, by rfl⟩ : syracuseStep 2684449 = 2013337) B2013337
theorem B8934947 : Blo 1764083 8934947 := bstep (se 1 (by rfl) ⟨6701210, by rfl⟩ : syracuseStep 8934947 = 13402421) B13402421
theorem B2979409 : Blo 1764083 2979409 := bstep (se 2 (by rfl) ⟨1117278, by rfl⟩ : syracuseStep 2979409 = 2234557) B2234557
theorem B6035057 : Blo 1764083 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B12719729 : Blo 1764083 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B3970673 : Blo 1764083 3970673 := bstep (se 2 (by rfl) ⟨1489002, by rfl⟩ : syracuseStep 3970673 = 2978005) B2978005
theorem B2979443 : Blo 1764083 2979443 := bstep (se 1 (by rfl) ⟨2234582, by rfl⟩ : syracuseStep 2979443 = 4469165) B4469165
theorem B3970691 : Blo 1764083 3970691 := bstep (se 1 (by rfl) ⟨2978018, by rfl⟩ : syracuseStep 3970691 = 5956037) B5956037
theorem B6698659 : Blo 1764083 6698659 := bstep (se 1 (by rfl) ⟨5023994, by rfl⟩ : syracuseStep 6698659 = 10047989) B10047989
theorem B2684657 : Blo 1764083 2684657 := bstep (se 2 (by rfl) ⟨1006746, by rfl⟩ : syracuseStep 2684657 = 2013493) B2013493
theorem B2979571 : Blo 1764083 2979571 := bstep (se 1 (by rfl) ⟨2234678, by rfl⟩ : syracuseStep 2979571 = 4469357) B4469357
theorem B5027629 : Blo 1764083 5027629 := bstep (se 3 (by rfl) ⟨942680, by rfl⟩ : syracuseStep 5027629 = 1885361) B1885361
theorem B3020593 : Blo 1764083 3020593 := bstep (se 2 (by rfl) ⟨1132722, by rfl⟩ : syracuseStep 3020593 = 2265445) B2265445
theorem B2512721 : Blo 1764083 2512721 := bstep (se 2 (by rfl) ⟨942270, by rfl⟩ : syracuseStep 2512721 = 1884541) B1884541
theorem B2979713 : Blo 1764083 2979713 := bstep (se 2 (by rfl) ⟨1117392, by rfl⟩ : syracuseStep 2979713 = 2234785) B2234785
theorem B2234243 : Blo 1764083 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B3970961 : Blo 1764083 3970961 := bstep (se 2 (by rfl) ⟨1489110, by rfl⟩ : syracuseStep 3970961 = 2978221) B2978221
theorem B3536803 : Blo 1764083 3536803 := bstep (se 1 (by rfl) ⟨2652602, by rfl⟩ : syracuseStep 3536803 = 5305205) B5305205
theorem B3970979 : Blo 1764083 3970979 := bstep (se 1 (by rfl) ⟨2978234, by rfl⟩ : syracuseStep 3970979 = 5956469) B5956469
theorem B2979841 : Blo 1764083 2979841 := bstep (se 2 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 2979841 = 2234881) B2234881
theorem B9541637 : Blo 1764083 9541637 := bstep (se 4 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 9541637 = 1789057) B1789057
theorem B2979875 : Blo 1764083 2979875 := bstep (se 1 (by rfl) ⟨2234906, by rfl⟩ : syracuseStep 2979875 = 4469813) B4469813
theorem B5093489 : Blo 1764083 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B2980003 : Blo 1764083 2980003 := bstep (se 1 (by rfl) ⟨2235002, by rfl⟩ : syracuseStep 2980003 = 4470005) B4470005
theorem B3971249 : Blo 1764083 3971249 := bstep (se 2 (by rfl) ⟨1489218, by rfl⟩ : syracuseStep 3971249 = 2978437) B2978437
theorem B3971267 : Blo 1764083 3971267 := bstep (se 1 (by rfl) ⟨2978450, by rfl⟩ : syracuseStep 3971267 = 5956901) B5956901
theorem B2980145 : Blo 1764083 2980145 := bstep (se 2 (by rfl) ⟨1117554, by rfl⟩ : syracuseStep 2980145 = 2235109) B2235109
theorem B20101445 : Blo 1764083 20101445 := bstep (se 4 (by rfl) ⟨1884510, by rfl⟩ : syracuseStep 20101445 = 3769021) B3769021
theorem B8935757 : Blo 1764083 8935757 := bstep (se 3 (by rfl) ⟨1675454, by rfl⟩ : syracuseStep 8935757 = 3350909) B3350909
theorem B3971537 : Blo 1764083 3971537 := bstep (se 2 (by rfl) ⟨1489326, by rfl⟩ : syracuseStep 3971537 = 2978653) B2978653
theorem B3971555 : Blo 1764083 3971555 := bstep (se 1 (by rfl) ⟨2978666, by rfl⟩ : syracuseStep 3971555 = 5957333) B5957333
theorem B13408739 : Blo 1764083 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B5954093 : Blo 1764083 5954093 := bstep (se 3 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 5954093 = 2232785) B2232785
theorem B2234947 : Blo 1764083 2234947 := bstep (se 1 (by rfl) ⟨1676210, by rfl⟩ : syracuseStep 2234947 = 3352421) B3352421
theorem B5954147 : Blo 1764083 5954147 := bstep (se 1 (by rfl) ⟨4465610, by rfl⟩ : syracuseStep 5954147 = 8931221) B8931221
theorem B19094129 : Blo 1764083 19094129 := bstep (se 2 (by rfl) ⟨7160298, by rfl⟩ : syracuseStep 19094129 = 14320597) B14320597
theorem B9542285 : Blo 1764083 9542285 := bstep (se 3 (by rfl) ⟨1789178, by rfl⟩ : syracuseStep 9542285 = 3578357) B3578357
theorem B11311757 : Blo 1764083 11311757 := bstep (se 3 (by rfl) ⟨2120954, by rfl⟩ : syracuseStep 11311757 = 4241909) B4241909
theorem B2235043 : Blo 1764083 2235043 := bstep (se 1 (by rfl) ⟨1676282, by rfl⟩ : syracuseStep 2235043 = 3352565) B3352565
theorem B2513587 : Blo 1764083 2513587 := bstep (se 1 (by rfl) ⟨1885190, by rfl⟩ : syracuseStep 2513587 = 3770381) B3770381
theorem B3349201 : Blo 1764083 3349201 := bstep (se 2 (by rfl) ⟨1255950, by rfl⟩ : syracuseStep 3349201 = 2511901) B2511901
theorem B2013907 : Blo 1764083 2013907 := bstep (se 1 (by rfl) ⟨1510430, by rfl⟩ : syracuseStep 2013907 = 3020861) B3020861
theorem B3971825 : Blo 1764083 3971825 := bstep (se 2 (by rfl) ⟨1489434, by rfl⟩ : syracuseStep 3971825 = 2978869) B2978869
theorem B3971843 : Blo 1764083 3971843 := bstep (se 1 (by rfl) ⟨2978882, by rfl⟩ : syracuseStep 3971843 = 5957765) B5957765
theorem B5094161 : Blo 1764083 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B2513683 : Blo 1764083 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B8485681 : Blo 1764083 8485681 := bstep (se 2 (by rfl) ⟨3182130, by rfl⟩ : syracuseStep 8485681 = 6364261) B6364261
theorem B5364593 : Blo 1764083 5364593 := bstep (se 2 (by rfl) ⟨2011722, by rfl⟩ : syracuseStep 5364593 = 4023445) B4023445
theorem B5954417 : Blo 1764083 5954417 := bstep (se 2 (by rfl) ⟨2232906, by rfl⟩ : syracuseStep 5954417 = 4465813) B4465813
theorem B20110193 : Blo 1764083 20110193 := bstep (se 2 (by rfl) ⟨7541322, by rfl⟩ : syracuseStep 20110193 = 15082645) B15082645
theorem B21756869 : Blo 1764083 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B6364145 : Blo 1764083 6364145 := bstep (se 2 (by rfl) ⟨2386554, by rfl⟩ : syracuseStep 6364145 = 4773109) B4773109
theorem B3972113 : Blo 1764083 3972113 := bstep (se 2 (by rfl) ⟨1489542, by rfl⟩ : syracuseStep 3972113 = 2979085) B2979085
theorem B3972131 : Blo 1764083 3972131 := bstep (se 1 (by rfl) ⟨2979098, by rfl⟩ : syracuseStep 3972131 = 5958197) B5958197
theorem B3349603 : Blo 1764083 3349603 := bstep (se 1 (by rfl) ⟨2512202, by rfl⟩ : syracuseStep 3349603 = 5024405) B5024405
theorem B15285347 : Blo 1764083 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B17202289 : Blo 1764083 17202289 := bstep (se 2 (by rfl) ⟨6450858, by rfl⟩ : syracuseStep 17202289 = 12901717) B12901717
theorem B3349649 : Blo 1764083 3349649 := bstep (se 2 (by rfl) ⟨1256118, by rfl⟩ : syracuseStep 3349649 = 2512237) B2512237
theorem B2514179 : Blo 1764083 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B3972401 : Blo 1764083 3972401 := bstep (se 2 (by rfl) ⟨1489650, by rfl⟩ : syracuseStep 3972401 = 2979301) B2979301
theorem B3972419 : Blo 1764083 3972419 := bstep (se 1 (by rfl) ⟨2979314, by rfl⟩ : syracuseStep 3972419 = 5958629) B5958629
theorem B6364493 : Blo 1764083 6364493 := bstep (se 3 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 6364493 = 2386685) B2386685
theorem B7077233 : Blo 1764083 7077233 := bstep (se 2 (by rfl) ⟨2653962, by rfl⟩ : syracuseStep 7077233 = 5307925) B5307925
theorem B5954957 : Blo 1764083 5954957 := bstep (se 3 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 5954957 = 2233109) B2233109
theorem B5807537 : Blo 1764083 5807537 := bstep (se 2 (by rfl) ⟨2177826, by rfl⟩ : syracuseStep 5807537 = 4355653) B4355653
theorem B3349937 : Blo 1764083 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B5955011 : Blo 1764083 5955011 := bstep (se 1 (by rfl) ⟨4466258, by rfl⟩ : syracuseStep 5955011 = 8932517) B8932517
theorem B13589957 : Blo 1764083 13589957 := bstep (se 4 (by rfl) ⟨1274058, by rfl⟩ : syracuseStep 13589957 = 2548117) B2548117
theorem B5094989 : Blo 1764083 5094989 := bstep (se 3 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 5094989 = 1910621) B1910621
theorem B3972689 : Blo 1764083 3972689 := bstep (se 2 (by rfl) ⟨1489758, by rfl⟩ : syracuseStep 3972689 = 2979517) B2979517
theorem B3972707 : Blo 1764083 3972707 := bstep (se 1 (by rfl) ⟨2979530, by rfl⟩ : syracuseStep 3972707 = 5959061) B5959061
theorem B21462641 : Blo 1764083 21462641 := bstep (se 2 (by rfl) ⟨8048490, by rfl⟩ : syracuseStep 21462641 = 16096981) B16096981
theorem B2825857 : Blo 1764083 2825857 := bstep (se 2 (by rfl) ⟨1059696, by rfl⟩ : syracuseStep 2825857 = 2119393) B2119393
theorem B2825921 : Blo 1764083 2825921 := bstep (se 2 (by rfl) ⟨1059720, by rfl⟩ : syracuseStep 2825921 = 2119441) B2119441
theorem B5955281 : Blo 1764083 5955281 := bstep (se 2 (by rfl) ⟨2233230, by rfl⟩ : syracuseStep 5955281 = 4466461) B4466461
theorem B6700877 : Blo 1764083 6700877 := bstep (se 3 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 6700877 = 2512829) B2512829
theorem B7642957 : Blo 1764083 7642957 := bstep (se 3 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 7642957 = 2866109) B2866109
theorem B3972977 : Blo 1764083 3972977 := bstep (se 2 (by rfl) ⟨1489866, by rfl⟩ : syracuseStep 3972977 = 2979733) B2979733
theorem B3972995 : Blo 1764083 3972995 := bstep (se 1 (by rfl) ⟨2979746, by rfl⟩ : syracuseStep 3972995 = 5959493) B5959493
theorem B51560333 : Blo 1764083 51560333 := bstep (se 3 (by rfl) ⟨9667562, by rfl⟩ : syracuseStep 51560333 = 19335125) B19335125
theorem B2547667 : Blo 1764083 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B3973121 : Blo 1764083 3973121 := bstep (se 2 (by rfl) ⟨1489920, by rfl⟩ : syracuseStep 3973121 = 2979841) B2979841
theorem B5955659 : Blo 1764083 5955659 := bstep (se 1 (by rfl) ⟨4466744, by rfl⟩ : syracuseStep 5955659 = 8933489) B8933489
theorem B2646155 : Blo 1764083 2646155 := bstep (se 1 (by rfl) ⟨1984616, by rfl⟩ : syracuseStep 2646155 = 3969233) B3969233
theorem B2646167 : Blo 1764083 2646167 := bstep (se 1 (by rfl) ⟨1984625, by rfl⟩ : syracuseStep 2646167 = 3969251) B3969251
theorem B21479575 : Blo 1764083 21479575 := bstep (se 1 (by rfl) ⟨16109681, by rfl⟩ : syracuseStep 21479575 = 32219363) B32219363
theorem B3768535 : Blo 1764083 3768535 := bstep (se 1 (by rfl) ⟨2826401, by rfl⟩ : syracuseStep 3768535 = 5652803) B5652803
theorem B2646233 : Blo 1764083 2646233 := bstep (se 2 (by rfl) ⟨992337, by rfl⟩ : syracuseStep 2646233 = 1984675) B1984675
theorem B3973337 : Blo 1764083 3973337 := bstep (se 2 (by rfl) ⟨1490001, by rfl⟩ : syracuseStep 3973337 = 2980003) B2980003
theorem B13582637 : Blo 1764083 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B6701363 : Blo 1764083 6701363 := bstep (se 1 (by rfl) ⟨5026022, by rfl⟩ : syracuseStep 6701363 = 10052045) B10052045
theorem B3973427 : Blo 1764083 3973427 := bstep (se 1 (by rfl) ⟨2980070, by rfl⟩ : syracuseStep 3973427 = 5960141) B5960141
theorem B2646347 : Blo 1764083 2646347 := bstep (se 1 (by rfl) ⟨1984760, by rfl⟩ : syracuseStep 2646347 = 3969521) B3969521
theorem B2646359 : Blo 1764083 2646359 := bstep (se 1 (by rfl) ⟨1984769, by rfl⟩ : syracuseStep 2646359 = 3969539) B3969539
theorem B3973463 : Blo 1764083 3973463 := bstep (se 1 (by rfl) ⟨2980097, by rfl⟩ : syracuseStep 3973463 = 5960195) B5960195
theorem B5955929 : Blo 1764083 5955929 := bstep (se 2 (by rfl) ⟨2233473, by rfl⟩ : syracuseStep 5955929 = 4466947) B4466947
theorem B2646425 : Blo 1764083 2646425 := bstep (se 2 (by rfl) ⟨992409, by rfl⟩ : syracuseStep 2646425 = 1984819) B1984819
theorem B3350963 : Blo 1764083 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B2646539 : Blo 1764083 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B3973643 : Blo 1764083 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B2646551 : Blo 1764083 2646551 := bstep (se 1 (by rfl) ⟨1984913, by rfl⟩ : syracuseStep 2646551 = 3969827) B3969827
theorem B2646617 : Blo 1764083 2646617 := bstep (se 2 (by rfl) ⟨992481, by rfl⟩ : syracuseStep 2646617 = 1984963) B1984963
theorem B2646731 : Blo 1764083 2646731 := bstep (se 1 (by rfl) ⟨1985048, by rfl⟩ : syracuseStep 2646731 = 3970097) B3970097
theorem B6038219 : Blo 1764083 6038219 := bstep (se 1 (by rfl) ⟨4528664, by rfl⟩ : syracuseStep 6038219 = 9057329) B9057329
theorem B2646743 : Blo 1764083 2646743 := bstep (se 1 (by rfl) ⟨1985057, by rfl⟩ : syracuseStep 2646743 = 3970115) B3970115
theorem B2646809 : Blo 1764083 2646809 := bstep (se 2 (by rfl) ⟨992553, by rfl⟩ : syracuseStep 2646809 = 1985107) B1985107
theorem B19079981 : Blo 1764083 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B122266421 : Blo 1764083 122266421 := bstep (se 5 (by rfl) ⟨5731238, by rfl⟩ : syracuseStep 122266421 = 11462477) B11462477
theorem B11772803 : Blo 1764083 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B2646923 : Blo 1764083 2646923 := bstep (se 1 (by rfl) ⟨1985192, by rfl⟩ : syracuseStep 2646923 = 3970385) B3970385
theorem B2646935 : Blo 1764083 2646935 := bstep (se 1 (by rfl) ⟨1985201, by rfl⟩ : syracuseStep 2646935 = 3970403) B3970403
theorem B3351449 : Blo 1764083 3351449 := bstep (se 2 (by rfl) ⟨1256793, by rfl⟩ : syracuseStep 3351449 = 2513587) B2513587
theorem B8479667 : Blo 1764083 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B4465601 : Blo 1764083 4465601 := bstep (se 2 (by rfl) ⟨1674600, by rfl⟩ : syracuseStep 4465601 = 3349201) B3349201
theorem B2647001 : Blo 1764083 2647001 := bstep (se 2 (by rfl) ⟨992625, by rfl⟩ : syracuseStep 2647001 = 1985251) B1985251
theorem B6358019 : Blo 1764083 6358019 := bstep (se 1 (by rfl) ⟨4768514, by rfl⟩ : syracuseStep 6358019 = 9537029) B9537029
theorem B3769355 : Blo 1764083 3769355 := bstep (se 1 (by rfl) ⟨2827016, by rfl⟩ : syracuseStep 3769355 = 5654033) B5654033
theorem B5956631 : Blo 1764083 5956631 := bstep (se 1 (by rfl) ⟨4467473, by rfl⟩ : syracuseStep 5956631 = 8934947) B8934947
theorem B11314241 : Blo 1764083 11314241 := bstep (se 2 (by rfl) ⟨4242840, by rfl⟩ : syracuseStep 11314241 = 8485681) B8485681
theorem B2647115 : Blo 1764083 2647115 := bstep (se 1 (by rfl) ⟨1985336, by rfl⟩ : syracuseStep 2647115 = 3970673) B3970673
theorem B4023371 : Blo 1764083 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B8479819 : Blo 1764083 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B64406603 : Blo 1764083 64406603 := bstep (se 1 (by rfl) ⟨48304952, by rfl⟩ : syracuseStep 64406603 = 96609905) B96609905
theorem B2647127 : Blo 1764083 2647127 := bstep (se 1 (by rfl) ⟨1985345, by rfl⟩ : syracuseStep 2647127 = 3970691) B3970691
theorem B2647193 : Blo 1764083 2647193 := bstep (se 2 (by rfl) ⟨992697, by rfl⟩ : syracuseStep 2647193 = 1985395) B1985395
theorem B1885399 : Blo 1764083 1885399 := bstep (se 1 (by rfl) ⟨1414049, by rfl⟩ : syracuseStep 1885399 = 2828099) B2828099
theorem B2647307 : Blo 1764083 2647307 := bstep (se 1 (by rfl) ⟨1985480, by rfl⟩ : syracuseStep 2647307 = 3970961) B3970961
theorem B2647319 : Blo 1764083 2647319 := bstep (se 1 (by rfl) ⟨1985489, by rfl⟩ : syracuseStep 2647319 = 3970979) B3970979
theorem B2647385 : Blo 1764083 2647385 := bstep (se 2 (by rfl) ⟨992769, by rfl⟩ : syracuseStep 2647385 = 1985539) B1985539
theorem B3179969 : Blo 1764083 3179969 := bstep (se 2 (by rfl) ⟨1192488, by rfl⟩ : syracuseStep 3179969 = 2384977) B2384977
theorem B2647499 : Blo 1764083 2647499 := bstep (se 1 (by rfl) ⟨1985624, by rfl⟩ : syracuseStep 2647499 = 3971249) B3971249
theorem B2647511 : Blo 1764083 2647511 := bstep (se 1 (by rfl) ⟨1985633, by rfl⟩ : syracuseStep 2647511 = 3971267) B3971267
theorem B4466137 : Blo 1764083 4466137 := bstep (se 2 (by rfl) ⟨1674801, by rfl⟩ : syracuseStep 4466137 = 3349603) B3349603
theorem B4023809 : Blo 1764083 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B7538179 : Blo 1764083 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B2647577 : Blo 1764083 2647577 := bstep (se 2 (by rfl) ⟨992841, by rfl⟩ : syracuseStep 2647577 = 1985683) B1985683
theorem B5957171 : Blo 1764083 5957171 := bstep (se 1 (by rfl) ⟨4467878, by rfl⟩ : syracuseStep 5957171 = 8935757) B8935757
theorem B1885771 : Blo 1764083 1885771 := bstep (se 1 (by rfl) ⟨1414328, by rfl⟩ : syracuseStep 1885771 = 2828657) B2828657
theorem B2647691 : Blo 1764083 2647691 := bstep (se 1 (by rfl) ⟨1985768, by rfl⟩ : syracuseStep 2647691 = 3971537) B3971537
theorem B2647703 : Blo 1764083 2647703 := bstep (se 1 (by rfl) ⟨1985777, by rfl⟩ : syracuseStep 2647703 = 3971555) B3971555
theorem B8939159 : Blo 1764083 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B2647769 : Blo 1764083 2647769 := bstep (se 2 (by rfl) ⟨992913, by rfl⟩ : syracuseStep 2647769 = 1985827) B1985827
theorem B6702851 : Blo 1764083 6702851 := bstep (se 1 (by rfl) ⟨5027138, by rfl⟩ : syracuseStep 6702851 = 10054277) B10054277
theorem B15492881 : Blo 1764083 15492881 := bstep (se 2 (by rfl) ⟨5809830, by rfl⟩ : syracuseStep 15492881 = 11619661) B11619661
theorem B12715811 : Blo 1764083 12715811 := bstep (se 1 (by rfl) ⟨9536858, by rfl⟩ : syracuseStep 12715811 = 19073717) B19073717
theorem B5957441 : Blo 1764083 5957441 := bstep (se 2 (by rfl) ⟨2234040, by rfl⟩ : syracuseStep 5957441 = 4468081) B4468081
theorem B2647883 : Blo 1764083 2647883 := bstep (se 1 (by rfl) ⟨1985912, by rfl⟩ : syracuseStep 2647883 = 3971825) B3971825
theorem B2647895 : Blo 1764083 2647895 := bstep (se 1 (by rfl) ⟨1985921, by rfl⟩ : syracuseStep 2647895 = 3971843) B3971843
theorem B7538521 : Blo 1764083 7538521 := bstep (se 2 (by rfl) ⟨2826945, by rfl⟩ : syracuseStep 7538521 = 5653891) B5653891
theorem B3770201 : Blo 1764083 3770201 := bstep (se 2 (by rfl) ⟨1413825, by rfl⟩ : syracuseStep 3770201 = 2827651) B2827651
theorem B2647961 : Blo 1764083 2647961 := bstep (se 2 (by rfl) ⟨992985, by rfl⟩ : syracuseStep 2647961 = 1985971) B1985971
theorem B2648075 : Blo 1764083 2648075 := bstep (se 1 (by rfl) ⟨1986056, by rfl⟩ : syracuseStep 2648075 = 3972113) B3972113
theorem B2648087 : Blo 1764083 2648087 := bstep (se 1 (by rfl) ⟨1986065, by rfl⟩ : syracuseStep 2648087 = 3972131) B3972131
theorem B3180631 : Blo 1764083 3180631 := bstep (se 1 (by rfl) ⟨2385473, by rfl⟩ : syracuseStep 3180631 = 4770947) B4770947
theorem B2648153 : Blo 1764083 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B6703307 : Blo 1764083 6703307 := bstep (se 1 (by rfl) ⟨5027480, by rfl⟩ : syracuseStep 6703307 = 10054961) B10054961
theorem B2648267 : Blo 1764083 2648267 := bstep (se 1 (by rfl) ⟨1986200, by rfl⟩ : syracuseStep 2648267 = 3972401) B3972401
theorem B13404365 : Blo 1764083 13404365 := bstep (se 3 (by rfl) ⟨2513318, by rfl⟩ : syracuseStep 13404365 = 5026637) B5026637
theorem B2648279 : Blo 1764083 2648279 := bstep (se 1 (by rfl) ⟨1986209, by rfl⟩ : syracuseStep 2648279 = 3972419) B3972419
theorem B8931545 : Blo 1764083 8931545 := bstep (se 2 (by rfl) ⟨3349329, by rfl⟩ : syracuseStep 8931545 = 6698659) B6698659
theorem B1984747 : Blo 1764083 1984747 := bstep (se 1 (by rfl) ⟨1488560, by rfl⟩ : syracuseStep 1984747 = 2977121) B2977121
theorem B2648345 : Blo 1764083 2648345 := bstep (se 2 (by rfl) ⟨993129, by rfl⟩ : syracuseStep 2648345 = 1986259) B1986259
theorem B1984855 : Blo 1764083 1984855 := bstep (se 1 (by rfl) ⟨1488641, by rfl⟩ : syracuseStep 1984855 = 2977283) B2977283
theorem B5957981 : Blo 1764083 5957981 := bstep (se 3 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 5957981 = 2234243) B2234243
theorem B2648459 : Blo 1764083 2648459 := bstep (se 1 (by rfl) ⟨1986344, by rfl⟩ : syracuseStep 2648459 = 3972689) B3972689
theorem B6703505 : Blo 1764083 6703505 := bstep (se 2 (by rfl) ⟨2513814, by rfl⟩ : syracuseStep 6703505 = 5027629) B5027629
theorem B6359447 : Blo 1764083 6359447 := bstep (se 1 (by rfl) ⟨4769585, by rfl⟩ : syracuseStep 6359447 = 9539171) B9539171
theorem B2648471 : Blo 1764083 2648471 := bstep (se 1 (by rfl) ⟨1986353, by rfl⟩ : syracuseStep 2648471 = 3972707) B3972707
theorem B15083981 : Blo 1764083 15083981 := bstep (se 3 (by rfl) ⟨2828246, by rfl⟩ : syracuseStep 15083981 = 5656493) B5656493
theorem B2263511 : Blo 1764083 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B2648537 : Blo 1764083 2648537 := bstep (se 2 (by rfl) ⟨993201, by rfl⟩ : syracuseStep 2648537 = 1986403) B1986403
theorem B3770867 : Blo 1764083 3770867 := bstep (se 1 (by rfl) ⟨2828150, by rfl⟩ : syracuseStep 3770867 = 5656301) B5656301
theorem B1985035 : Blo 1764083 1985035 := bstep (se 1 (by rfl) ⟨1488776, by rfl⟩ : syracuseStep 1985035 = 2977553) B2977553
theorem B4467251 : Blo 1764083 4467251 := bstep (se 1 (by rfl) ⟨3350438, by rfl⟩ : syracuseStep 4467251 = 6700877) B6700877
theorem B2648651 : Blo 1764083 2648651 := bstep (se 1 (by rfl) ⟨1986488, by rfl⟩ : syracuseStep 2648651 = 3972977) B3972977
theorem B2648663 : Blo 1764083 2648663 := bstep (se 1 (by rfl) ⟨1986497, by rfl⟩ : syracuseStep 2648663 = 3972995) B3972995
theorem B38677085 : Blo 1764083 38677085 := bstep (se 3 (by rfl) ⟨7251953, by rfl⟩ : syracuseStep 38677085 = 14503907) B14503907
theorem B1985143 : Blo 1764083 1985143 := bstep (se 1 (by rfl) ⟨1488857, by rfl⟩ : syracuseStep 1985143 = 2977715) B2977715
theorem B2648729 : Blo 1764083 2648729 := bstep (se 2 (by rfl) ⟨993273, by rfl⟩ : syracuseStep 2648729 = 1986547) B1986547
theorem B13404851 : Blo 1764083 13404851 := bstep (se 1 (by rfl) ⟨10053638, by rfl⟩ : syracuseStep 13404851 = 20107277) B20107277
theorem B1764087 : Blo 1764083 1764087 := bstep (se 1 (by rfl) ⟨1323065, by rfl⟩ : syracuseStep 1764087 = 2646131) B2646131
theorem B1764107 : Blo 1764083 1764107 := bstep (se 1 (by rfl) ⟨1323080, by rfl⟩ : syracuseStep 1764107 = 2646161) B2646161
theorem B2648843 : Blo 1764083 2648843 := bstep (se 1 (by rfl) ⟨1986632, by rfl⟩ : syracuseStep 2648843 = 3973265) B3973265
theorem B1764119 : Blo 1764083 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B7539479 : Blo 1764083 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B2648855 : Blo 1764083 2648855 := bstep (se 1 (by rfl) ⟨1986641, by rfl⟩ : syracuseStep 2648855 = 3973283) B3973283
theorem B1764139 : Blo 1764083 1764139 := bstep (se 1 (by rfl) ⟨1323104, by rfl⟩ : syracuseStep 1764139 = 2646209) B2646209
theorem B1985323 : Blo 1764083 1985323 := bstep (se 1 (by rfl) ⟨1488992, by rfl⟩ : syracuseStep 1985323 = 2977985) B2977985
theorem B1764151 : Blo 1764083 1764151 := bstep (se 1 (by rfl) ⟨1323113, by rfl⟩ : syracuseStep 1764151 = 2646227) B2646227
theorem B1764171 : Blo 1764083 1764171 := bstep (se 1 (by rfl) ⟨1323128, by rfl⟩ : syracuseStep 1764171 = 2646257) B2646257
theorem B5024587 : Blo 1764083 5024587 := bstep (se 1 (by rfl) ⟨3768440, by rfl⟩ : syracuseStep 5024587 = 7536881) B7536881
theorem B1764183 : Blo 1764083 1764183 := bstep (se 1 (by rfl) ⟨1323137, by rfl⟩ : syracuseStep 1764183 = 2646275) B2646275
theorem B4467545 : Blo 1764083 4467545 := bstep (se 2 (by rfl) ⟨1675329, by rfl⟩ : syracuseStep 4467545 = 3350659) B3350659
theorem B2648921 : Blo 1764083 2648921 := bstep (se 2 (by rfl) ⟨993345, by rfl⟩ : syracuseStep 2648921 = 1986691) B1986691
theorem B1764203 : Blo 1764083 1764203 := bstep (se 1 (by rfl) ⟨1323152, by rfl⟩ : syracuseStep 1764203 = 2646305) B2646305
theorem B1764215 : Blo 1764083 1764215 := bstep (se 1 (by rfl) ⟨1323161, by rfl⟩ : syracuseStep 1764215 = 2646323) B2646323
theorem B1764235 : Blo 1764083 1764235 := bstep (se 1 (by rfl) ⟨1323176, by rfl⟩ : syracuseStep 1764235 = 2646353) B2646353
theorem B1764247 : Blo 1764083 1764247 := bstep (se 1 (by rfl) ⟨1323185, by rfl⟩ : syracuseStep 1764247 = 2646371) B2646371
theorem B1985431 : Blo 1764083 1985431 := bstep (se 1 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 1985431 = 2978147) B2978147
theorem B5368727 : Blo 1764083 5368727 := bstep (se 1 (by rfl) ⟨4026545, by rfl⟩ : syracuseStep 5368727 = 8053091) B8053091
theorem B1764267 : Blo 1764083 1764267 := bstep (se 1 (by rfl) ⟨1323200, by rfl⟩ : syracuseStep 1764267 = 2646401) B2646401
theorem B1764279 : Blo 1764083 1764279 := bstep (se 1 (by rfl) ⟨1323209, by rfl⟩ : syracuseStep 1764279 = 2646419) B2646419
theorem B1764299 : Blo 1764083 1764299 := bstep (se 1 (by rfl) ⟨1323224, by rfl⟩ : syracuseStep 1764299 = 2646449) B2646449
theorem B2649035 : Blo 1764083 2649035 := bstep (se 1 (by rfl) ⟨1986776, by rfl⟩ : syracuseStep 2649035 = 3973553) B3973553
theorem B1764311 : Blo 1764083 1764311 := bstep (se 1 (by rfl) ⟨1323233, by rfl⟩ : syracuseStep 1764311 = 2646467) B2646467
theorem B2649047 : Blo 1764083 2649047 := bstep (se 1 (by rfl) ⟨1986785, by rfl⟩ : syracuseStep 2649047 = 3973571) B3973571
theorem B1764331 : Blo 1764083 1764331 := bstep (se 1 (by rfl) ⟨1323248, by rfl⟩ : syracuseStep 1764331 = 2646497) B2646497
theorem B1764343 : Blo 1764083 1764343 := bstep (se 1 (by rfl) ⟨1323257, by rfl⟩ : syracuseStep 1764343 = 2646515) B2646515
theorem B1764363 : Blo 1764083 1764363 := bstep (se 1 (by rfl) ⟨1323272, by rfl⟩ : syracuseStep 1764363 = 2646545) B2646545
theorem B1764375 : Blo 1764083 1764375 := bstep (se 1 (by rfl) ⟨1323281, by rfl⟩ : syracuseStep 1764375 = 2646563) B2646563
theorem B2649113 : Blo 1764083 2649113 := bstep (se 2 (by rfl) ⟨993417, by rfl⟩ : syracuseStep 2649113 = 1986835) B1986835
theorem B1764395 : Blo 1764083 1764395 := bstep (se 1 (by rfl) ⟨1323296, by rfl⟩ : syracuseStep 1764395 = 2646593) B2646593
theorem B1764407 : Blo 1764083 1764407 := bstep (se 1 (by rfl) ⟨1323305, by rfl⟩ : syracuseStep 1764407 = 2646611) B2646611
theorem B1764427 : Blo 1764083 1764427 := bstep (se 1 (by rfl) ⟨1323320, by rfl⟩ : syracuseStep 1764427 = 2646641) B2646641
theorem B1985611 : Blo 1764083 1985611 := bstep (se 1 (by rfl) ⟨1489208, by rfl⟩ : syracuseStep 1985611 = 2978417) B2978417
theorem B1764439 : Blo 1764083 1764439 := bstep (se 1 (by rfl) ⟨1323329, by rfl⟩ : syracuseStep 1764439 = 2646659) B2646659
theorem B10185821 : Blo 1764083 10185821 := bstep (se 3 (by rfl) ⟨1909841, by rfl⟩ : syracuseStep 10185821 = 3819683) B3819683
theorem B5024861 : Blo 1764083 5024861 := bstep (se 3 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 5024861 = 1884323) B1884323
theorem B1764459 : Blo 1764083 1764459 := bstep (se 1 (by rfl) ⟨1323344, by rfl⟩ : syracuseStep 1764459 = 2646689) B2646689
theorem B1764471 : Blo 1764083 1764471 := bstep (se 1 (by rfl) ⟨1323353, by rfl⟩ : syracuseStep 1764471 = 2646707) B2646707
theorem B1764491 : Blo 1764083 1764491 := bstep (se 1 (by rfl) ⟨1323368, by rfl⟩ : syracuseStep 1764491 = 2646737) B2646737
theorem B1764503 : Blo 1764083 1764503 := bstep (se 1 (by rfl) ⟨1323377, by rfl⟩ : syracuseStep 1764503 = 2646755) B2646755
theorem B6704279 : Blo 1764083 6704279 := bstep (se 1 (by rfl) ⟨5028209, by rfl⟩ : syracuseStep 6704279 = 10056419) B10056419
theorem B1764523 : Blo 1764083 1764523 := bstep (se 1 (by rfl) ⟨1323392, by rfl⟩ : syracuseStep 1764523 = 2646785) B2646785
theorem B1764535 : Blo 1764083 1764535 := bstep (se 1 (by rfl) ⟨1323401, by rfl⟩ : syracuseStep 1764535 = 2646803) B2646803
theorem B1985719 : Blo 1764083 1985719 := bstep (se 1 (by rfl) ⟨1489289, by rfl⟩ : syracuseStep 1985719 = 2978579) B2978579
theorem B1764555 : Blo 1764083 1764555 := bstep (se 1 (by rfl) ⟨1323416, by rfl⟩ : syracuseStep 1764555 = 2646833) B2646833
theorem B1764567 : Blo 1764083 1764567 := bstep (se 1 (by rfl) ⟨1323425, by rfl⟩ : syracuseStep 1764567 = 2646851) B2646851
theorem B1764587 : Blo 1764083 1764587 := bstep (se 1 (by rfl) ⟨1323440, by rfl⟩ : syracuseStep 1764587 = 2646881) B2646881
theorem B1764599 : Blo 1764083 1764599 := bstep (se 1 (by rfl) ⟨1323449, by rfl⟩ : syracuseStep 1764599 = 2646899) B2646899
theorem B1764619 : Blo 1764083 1764619 := bstep (se 1 (by rfl) ⟨1323464, by rfl⟩ : syracuseStep 1764619 = 2646929) B2646929
theorem B1764631 : Blo 1764083 1764631 := bstep (se 1 (by rfl) ⟨1323473, by rfl⟩ : syracuseStep 1764631 = 2646947) B2646947
theorem B1764651 : Blo 1764083 1764651 := bstep (se 1 (by rfl) ⟨1323488, by rfl⟩ : syracuseStep 1764651 = 2646977) B2646977
theorem B1764663 : Blo 1764083 1764663 := bstep (se 1 (by rfl) ⟨1323497, by rfl⟩ : syracuseStep 1764663 = 2646995) B2646995
theorem B1764683 : Blo 1764083 1764683 := bstep (se 1 (by rfl) ⟨1323512, by rfl⟩ : syracuseStep 1764683 = 2647025) B2647025
theorem B1764695 : Blo 1764083 1764695 := bstep (se 1 (by rfl) ⟨1323521, by rfl⟩ : syracuseStep 1764695 = 2647043) B2647043
theorem B6704477 : Blo 1764083 6704477 := bstep (se 3 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 6704477 = 2514179) B2514179
theorem B1764715 : Blo 1764083 1764715 := bstep (se 1 (by rfl) ⟨1323536, by rfl⟩ : syracuseStep 1764715 = 2647073) B2647073
theorem B1985899 : Blo 1764083 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B1764727 : Blo 1764083 1764727 := bstep (se 1 (by rfl) ⟨1323545, by rfl⟩ : syracuseStep 1764727 = 2647091) B2647091
theorem B1764747 : Blo 1764083 1764747 := bstep (se 1 (by rfl) ⟨1323560, by rfl⟩ : syracuseStep 1764747 = 2647121) B2647121
theorem B2264459 : Blo 1764083 2264459 := bstep (se 1 (by rfl) ⟨1698344, by rfl⟩ : syracuseStep 2264459 = 3396689) B3396689
theorem B2977175 : Blo 1764083 2977175 := bstep (se 1 (by rfl) ⟨2232881, by rfl⟩ : syracuseStep 2977175 = 4465763) B4465763
theorem B1764759 : Blo 1764083 1764759 := bstep (se 1 (by rfl) ⟨1323569, by rfl⟩ : syracuseStep 1764759 = 2647139) B2647139
theorem B1764779 : Blo 1764083 1764779 := bstep (se 1 (by rfl) ⟨1323584, by rfl⟩ : syracuseStep 1764779 = 2647169) B2647169
theorem B5025203 : Blo 1764083 5025203 := bstep (se 1 (by rfl) ⟨3768902, by rfl⟩ : syracuseStep 5025203 = 7537805) B7537805
theorem B1764791 : Blo 1764083 1764791 := bstep (se 1 (by rfl) ⟨1323593, by rfl⟩ : syracuseStep 1764791 = 2647187) B2647187
theorem B3771841 : Blo 1764083 3771841 := bstep (se 2 (by rfl) ⟨1414440, by rfl⟩ : syracuseStep 3771841 = 2828881) B2828881
theorem B1764811 : Blo 1764083 1764811 := bstep (se 1 (by rfl) ⟨1323608, by rfl⟩ : syracuseStep 1764811 = 2647217) B2647217
theorem B5959115 : Blo 1764083 5959115 := bstep (se 1 (by rfl) ⟨4469336, by rfl⟩ : syracuseStep 5959115 = 8938673) B8938673
theorem B1764823 : Blo 1764083 1764823 := bstep (se 1 (by rfl) ⟨1323617, by rfl⟩ : syracuseStep 1764823 = 2647235) B2647235
theorem B1986007 : Blo 1764083 1986007 := bstep (se 1 (by rfl) ⟨1489505, by rfl⟩ : syracuseStep 1986007 = 2979011) B2979011
theorem B1764843 : Blo 1764083 1764843 := bstep (se 1 (by rfl) ⟨1323632, by rfl⟩ : syracuseStep 1764843 = 2647265) B2647265
theorem B1764855 : Blo 1764083 1764855 := bstep (se 1 (by rfl) ⟨1323641, by rfl⟩ : syracuseStep 1764855 = 2647283) B2647283
theorem B1764875 : Blo 1764083 1764875 := bstep (se 1 (by rfl) ⟨1323656, by rfl⟩ : syracuseStep 1764875 = 2647313) B2647313
theorem B2977303 : Blo 1764083 2977303 := bstep (se 1 (by rfl) ⟨2232977, by rfl⟩ : syracuseStep 2977303 = 4465955) B4465955
theorem B1764887 : Blo 1764083 1764887 := bstep (se 1 (by rfl) ⟨1323665, by rfl⟩ : syracuseStep 1764887 = 2647331) B2647331
theorem B1764907 : Blo 1764083 1764907 := bstep (se 1 (by rfl) ⟨1323680, by rfl⟩ : syracuseStep 1764907 = 2647361) B2647361
theorem B1764919 : Blo 1764083 1764919 := bstep (se 1 (by rfl) ⟨1323689, by rfl⟩ : syracuseStep 1764919 = 2647379) B2647379
theorem B1764939 : Blo 1764083 1764939 := bstep (se 1 (by rfl) ⟨1323704, by rfl⟩ : syracuseStep 1764939 = 2647409) B2647409
theorem B1764951 : Blo 1764083 1764951 := bstep (se 1 (by rfl) ⟨1323713, by rfl⟩ : syracuseStep 1764951 = 2647427) B2647427
theorem B1764971 : Blo 1764083 1764971 := bstep (se 1 (by rfl) ⟨1323728, by rfl⟩ : syracuseStep 1764971 = 2647457) B2647457
theorem B1764983 : Blo 1764083 1764983 := bstep (se 1 (by rfl) ⟨1323737, by rfl⟩ : syracuseStep 1764983 = 2647475) B2647475
theorem B1765003 : Blo 1764083 1765003 := bstep (se 1 (by rfl) ⟨1323752, by rfl⟩ : syracuseStep 1765003 = 2647505) B2647505
theorem B1986187 : Blo 1764083 1986187 := bstep (se 1 (by rfl) ⟨1489640, by rfl⟩ : syracuseStep 1986187 = 2979281) B2979281
theorem B1765015 : Blo 1764083 1765015 := bstep (se 1 (by rfl) ⟨1323761, by rfl⟩ : syracuseStep 1765015 = 2647523) B2647523
theorem B1765035 : Blo 1764083 1765035 := bstep (se 1 (by rfl) ⟨1323776, by rfl⟩ : syracuseStep 1765035 = 2647553) B2647553
theorem B1765047 : Blo 1764083 1765047 := bstep (se 1 (by rfl) ⟨1323785, by rfl⟩ : syracuseStep 1765047 = 2647571) B2647571
theorem B1765067 : Blo 1764083 1765067 := bstep (se 1 (by rfl) ⟨1323800, by rfl⟩ : syracuseStep 1765067 = 2647601) B2647601
theorem B1765079 : Blo 1764083 1765079 := bstep (se 1 (by rfl) ⟨1323809, by rfl⟩ : syracuseStep 1765079 = 2647619) B2647619
theorem B4026071 : Blo 1764083 4026071 := bstep (se 1 (by rfl) ⟨3019553, by rfl⟩ : syracuseStep 4026071 = 6039107) B6039107
theorem B5959385 : Blo 1764083 5959385 := bstep (se 2 (by rfl) ⟨2234769, by rfl⟩ : syracuseStep 5959385 = 4469539) B4469539
theorem B1765099 : Blo 1764083 1765099 := bstep (se 1 (by rfl) ⟨1323824, by rfl⟩ : syracuseStep 1765099 = 2647649) B2647649
theorem B1765111 : Blo 1764083 1765111 := bstep (se 1 (by rfl) ⟨1323833, by rfl⟩ : syracuseStep 1765111 = 2647667) B2647667
theorem B1986295 : Blo 1764083 1986295 := bstep (se 1 (by rfl) ⟨1489721, by rfl⟩ : syracuseStep 1986295 = 2979443) B2979443
theorem B1765131 : Blo 1764083 1765131 := bstep (se 1 (by rfl) ⟨1323848, by rfl⟩ : syracuseStep 1765131 = 2647697) B2647697
theorem B1765143 : Blo 1764083 1765143 := bstep (se 1 (by rfl) ⟨1323857, by rfl⟩ : syracuseStep 1765143 = 2647715) B2647715
theorem B1765163 : Blo 1764083 1765163 := bstep (se 1 (by rfl) ⟨1323872, by rfl⟩ : syracuseStep 1765163 = 2647745) B2647745
theorem B8933165 : Blo 1764083 8933165 := bstep (se 3 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 8933165 = 3349937) B3349937
theorem B1765175 : Blo 1764083 1765175 := bstep (se 1 (by rfl) ⟨1323881, by rfl⟩ : syracuseStep 1765175 = 2647763) B2647763
theorem B21458753 : Blo 1764083 21458753 := bstep (se 2 (by rfl) ⟨8047032, by rfl⟩ : syracuseStep 21458753 = 16094065) B16094065
theorem B24162113 : Blo 1764083 24162113 := bstep (se 2 (by rfl) ⟨9060792, by rfl⟩ : syracuseStep 24162113 = 18121585) B18121585
theorem B1765195 : Blo 1764083 1765195 := bstep (se 1 (by rfl) ⟨1323896, by rfl⟩ : syracuseStep 1765195 = 2647793) B2647793
theorem B1789771 : Blo 1764083 1789771 := bstep (se 1 (by rfl) ⟨1342328, by rfl⟩ : syracuseStep 1789771 = 2684657) B2684657
theorem B1765207 : Blo 1764083 1765207 := bstep (se 1 (by rfl) ⟨1323905, by rfl⟩ : syracuseStep 1765207 = 2647811) B2647811
theorem B1765227 : Blo 1764083 1765227 := bstep (se 1 (by rfl) ⟨1323920, by rfl⟩ : syracuseStep 1765227 = 2647841) B2647841
theorem B1765239 : Blo 1764083 1765239 := bstep (se 1 (by rfl) ⟨1323929, by rfl⟩ : syracuseStep 1765239 = 2647859) B2647859
theorem B1765259 : Blo 1764083 1765259 := bstep (se 1 (by rfl) ⟨1323944, by rfl⟩ : syracuseStep 1765259 = 2647889) B2647889
theorem B1765271 : Blo 1764083 1765271 := bstep (se 1 (by rfl) ⟨1323953, by rfl⟩ : syracuseStep 1765271 = 2647907) B2647907
theorem B1765291 : Blo 1764083 1765291 := bstep (se 1 (by rfl) ⟨1323968, by rfl⟩ : syracuseStep 1765291 = 2647937) B2647937
theorem B1986475 : Blo 1764083 1986475 := bstep (se 1 (by rfl) ⟨1489856, by rfl⟩ : syracuseStep 1986475 = 2979713) B2979713
theorem B1765303 : Blo 1764083 1765303 := bstep (se 1 (by rfl) ⟨1323977, by rfl⟩ : syracuseStep 1765303 = 2647955) B2647955
theorem B1765323 : Blo 1764083 1765323 := bstep (se 1 (by rfl) ⟨1323992, by rfl⟩ : syracuseStep 1765323 = 2647985) B2647985
theorem B1765335 : Blo 1764083 1765335 := bstep (se 1 (by rfl) ⟨1324001, by rfl⟩ : syracuseStep 1765335 = 2648003) B2648003
theorem B1765355 : Blo 1764083 1765355 := bstep (se 1 (by rfl) ⟨1324016, by rfl⟩ : syracuseStep 1765355 = 2648033) B2648033
theorem B1765367 : Blo 1764083 1765367 := bstep (se 1 (by rfl) ⟨1324025, by rfl⟩ : syracuseStep 1765367 = 2648051) B2648051
theorem B6361091 : Blo 1764083 6361091 := bstep (se 1 (by rfl) ⟨4770818, by rfl⟩ : syracuseStep 6361091 = 9541637) B9541637
theorem B1765387 : Blo 1764083 1765387 := bstep (se 1 (by rfl) ⟨1324040, by rfl⟩ : syracuseStep 1765387 = 2648081) B2648081
theorem B1765399 : Blo 1764083 1765399 := bstep (se 1 (by rfl) ⟨1324049, by rfl⟩ : syracuseStep 1765399 = 2648099) B2648099
theorem B1986583 : Blo 1764083 1986583 := bstep (se 1 (by rfl) ⟨1489937, by rfl⟩ : syracuseStep 1986583 = 2979875) B2979875
theorem B6041623 : Blo 1764083 6041623 := bstep (se 1 (by rfl) ⟨4531217, by rfl⟩ : syracuseStep 6041623 = 9062435) B9062435
theorem B1765419 : Blo 1764083 1765419 := bstep (se 1 (by rfl) ⟨1324064, by rfl⟩ : syracuseStep 1765419 = 2648129) B2648129
theorem B1765431 : Blo 1764083 1765431 := bstep (se 1 (by rfl) ⟨1324073, by rfl⟩ : syracuseStep 1765431 = 2648147) B2648147
theorem B1765451 : Blo 1764083 1765451 := bstep (se 1 (by rfl) ⟨1324088, by rfl⟩ : syracuseStep 1765451 = 2648177) B2648177
theorem B1765463 : Blo 1764083 1765463 := bstep (se 1 (by rfl) ⟨1324097, by rfl⟩ : syracuseStep 1765463 = 2648195) B2648195
theorem B4239449 : Blo 1764083 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B13406309 : Blo 1764083 13406309 := bstep (se 4 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 13406309 = 2513683) B2513683
theorem B1765483 : Blo 1764083 1765483 := bstep (se 1 (by rfl) ⟨1324112, by rfl⟩ : syracuseStep 1765483 = 2648225) B2648225
theorem B1765495 : Blo 1764083 1765495 := bstep (se 1 (by rfl) ⟨1324121, by rfl⟩ : syracuseStep 1765495 = 2648243) B2648243
theorem B2977931 : Blo 1764083 2977931 := bstep (se 1 (by rfl) ⟨2233448, by rfl⟩ : syracuseStep 2977931 = 4466897) B4466897
theorem B1765515 : Blo 1764083 1765515 := bstep (se 1 (by rfl) ⟨1324136, by rfl⟩ : syracuseStep 1765515 = 2648273) B2648273
theorem B1765527 : Blo 1764083 1765527 := bstep (se 1 (by rfl) ⟨1324145, by rfl⟩ : syracuseStep 1765527 = 2648291) B2648291
theorem B1765547 : Blo 1764083 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B42922165 : Blo 1764083 42922165 := bstep (se 5 (by rfl) ⟨2011976, by rfl⟩ : syracuseStep 42922165 = 4023953) B4023953
theorem B1765559 : Blo 1764083 1765559 := bstep (se 1 (by rfl) ⟨1324169, by rfl⟩ : syracuseStep 1765559 = 2648339) B2648339
theorem B1765579 : Blo 1764083 1765579 := bstep (se 1 (by rfl) ⟨1324184, by rfl⟩ : syracuseStep 1765579 = 2648369) B2648369
theorem B1986763 : Blo 1764083 1986763 := bstep (se 1 (by rfl) ⟨1490072, by rfl⟩ : syracuseStep 1986763 = 2980145) B2980145
theorem B1765591 : Blo 1764083 1765591 := bstep (se 1 (by rfl) ⟨1324193, by rfl⟩ : syracuseStep 1765591 = 2648387) B2648387
theorem B1765611 : Blo 1764083 1765611 := bstep (se 1 (by rfl) ⟨1324208, by rfl⟩ : syracuseStep 1765611 = 2648417) B2648417
theorem B1765623 : Blo 1764083 1765623 := bstep (se 1 (by rfl) ⟨1324217, by rfl⟩ : syracuseStep 1765623 = 2648435) B2648435
theorem B2978059 : Blo 1764083 2978059 := bstep (se 1 (by rfl) ⟨2233544, by rfl⟩ : syracuseStep 2978059 = 4467089) B4467089
theorem B1765643 : Blo 1764083 1765643 := bstep (se 1 (by rfl) ⟨1324232, by rfl⟩ : syracuseStep 1765643 = 2648465) B2648465
theorem B1765655 : Blo 1764083 1765655 := bstep (se 1 (by rfl) ⟨1324241, by rfl⟩ : syracuseStep 1765655 = 2648483) B2648483
theorem B3969305 : Blo 1764083 3969305 := bstep (se 2 (by rfl) ⟨1488489, by rfl⟩ : syracuseStep 3969305 = 2976979) B2976979
theorem B1765675 : Blo 1764083 1765675 := bstep (se 1 (by rfl) ⟨1324256, by rfl⟩ : syracuseStep 1765675 = 2648513) B2648513
theorem B1765687 : Blo 1764083 1765687 := bstep (se 1 (by rfl) ⟨1324265, by rfl⟩ : syracuseStep 1765687 = 2648531) B2648531
theorem B1765707 : Blo 1764083 1765707 := bstep (se 1 (by rfl) ⟨1324280, by rfl⟩ : syracuseStep 1765707 = 2648561) B2648561
theorem B1765719 : Blo 1764083 1765719 := bstep (se 1 (by rfl) ⟨1324289, by rfl⟩ : syracuseStep 1765719 = 2648579) B2648579
theorem B1765739 : Blo 1764083 1765739 := bstep (se 1 (by rfl) ⟨1324304, by rfl⟩ : syracuseStep 1765739 = 2648609) B2648609
theorem B3969395 : Blo 1764083 3969395 := bstep (se 1 (by rfl) ⟨2977046, by rfl⟩ : syracuseStep 3969395 = 5954093) B5954093
theorem B1765751 : Blo 1764083 1765751 := bstep (se 1 (by rfl) ⟨1324313, by rfl⟩ : syracuseStep 1765751 = 2648627) B2648627
theorem B1765771 : Blo 1764083 1765771 := bstep (se 1 (by rfl) ⟨1324328, by rfl⟩ : syracuseStep 1765771 = 2648657) B2648657
theorem B3969431 : Blo 1764083 3969431 := bstep (se 1 (by rfl) ⟨2977073, by rfl⟩ : syracuseStep 3969431 = 5954147) B5954147
theorem B1765783 : Blo 1764083 1765783 := bstep (se 1 (by rfl) ⟨1324337, by rfl⟩ : syracuseStep 1765783 = 2648675) B2648675
theorem B2978201 : Blo 1764083 2978201 := bstep (se 2 (by rfl) ⟨1116825, by rfl⟩ : syracuseStep 2978201 = 2233651) B2233651
theorem B5960087 : Blo 1764083 5960087 := bstep (se 1 (by rfl) ⟨4470065, by rfl⟩ : syracuseStep 5960087 = 8940131) B8940131
theorem B1765803 : Blo 1764083 1765803 := bstep (se 1 (by rfl) ⟨1324352, by rfl⟩ : syracuseStep 1765803 = 2648705) B2648705
theorem B6361523 : Blo 1764083 6361523 := bstep (se 1 (by rfl) ⟨4771142, by rfl⟩ : syracuseStep 6361523 = 9542285) B9542285
theorem B7541171 : Blo 1764083 7541171 := bstep (se 1 (by rfl) ⟨5655878, by rfl⟩ : syracuseStep 7541171 = 11311757) B11311757
theorem B1765815 : Blo 1764083 1765815 := bstep (se 1 (by rfl) ⟨1324361, by rfl⟩ : syracuseStep 1765815 = 2648723) B2648723
theorem B4469195 : Blo 1764083 4469195 := bstep (se 1 (by rfl) ⟨3351896, by rfl⟩ : syracuseStep 4469195 = 6703793) B6703793
theorem B1765835 : Blo 1764083 1765835 := bstep (se 1 (by rfl) ⟨1324376, by rfl⟩ : syracuseStep 1765835 = 2648753) B2648753
theorem B1765847 : Blo 1764083 1765847 := bstep (se 1 (by rfl) ⟨1324385, by rfl⟩ : syracuseStep 1765847 = 2648771) B2648771
theorem B1765867 : Blo 1764083 1765867 := bstep (se 1 (by rfl) ⟨1324400, by rfl⟩ : syracuseStep 1765867 = 2648801) B2648801
theorem B1765879 : Blo 1764083 1765879 := bstep (se 1 (by rfl) ⟨1324409, by rfl⟩ : syracuseStep 1765879 = 2648819) B2648819
theorem B13398533 : Blo 1764083 13398533 := bstep (se 4 (by rfl) ⟨1256112, by rfl⟩ : syracuseStep 13398533 = 2512225) B2512225
theorem B3396107 : Blo 1764083 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B1765899 : Blo 1764083 1765899 := bstep (se 1 (by rfl) ⟨1324424, by rfl⟩ : syracuseStep 1765899 = 2648849) B2648849
theorem B1765911 : Blo 1764083 1765911 := bstep (se 1 (by rfl) ⟨1324433, by rfl⟩ : syracuseStep 1765911 = 2648867) B2648867
theorem B2978329 : Blo 1764083 2978329 := bstep (se 2 (by rfl) ⟨1116873, by rfl⟩ : syracuseStep 2978329 = 2233747) B2233747
theorem B1765931 : Blo 1764083 1765931 := bstep (se 1 (by rfl) ⟨1324448, by rfl⟩ : syracuseStep 1765931 = 2648897) B2648897
theorem B1765943 : Blo 1764083 1765943 := bstep (se 1 (by rfl) ⟨1324457, by rfl⟩ : syracuseStep 1765943 = 2648915) B2648915
theorem B3576395 : Blo 1764083 3576395 := bstep (se 1 (by rfl) ⟨2682296, by rfl⟩ : syracuseStep 3576395 = 5364593) B5364593
theorem B3969611 : Blo 1764083 3969611 := bstep (se 1 (by rfl) ⟨2977208, by rfl⟩ : syracuseStep 3969611 = 5954417) B5954417
theorem B13406795 : Blo 1764083 13406795 := bstep (se 1 (by rfl) ⟨10055096, by rfl⟩ : syracuseStep 13406795 = 20110193) B20110193
theorem B1765963 : Blo 1764083 1765963 := bstep (se 1 (by rfl) ⟨1324472, by rfl⟩ : syracuseStep 1765963 = 2648945) B2648945
theorem B1765975 : Blo 1764083 1765975 := bstep (se 1 (by rfl) ⟨1324481, by rfl⟩ : syracuseStep 1765975 = 2648963) B2648963
theorem B1765995 : Blo 1764083 1765995 := bstep (se 1 (by rfl) ⟨1324496, by rfl⟩ : syracuseStep 1765995 = 2648993) B2648993
theorem B1766007 : Blo 1764083 1766007 := bstep (se 1 (by rfl) ⟨1324505, by rfl⟩ : syracuseStep 1766007 = 2649011) B2649011
theorem B3969665 : Blo 1764083 3969665 := bstep (se 2 (by rfl) ⟨1488624, by rfl⟩ : syracuseStep 3969665 = 2977249) B2977249
theorem B14504579 : Blo 1764083 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B1766027 : Blo 1764083 1766027 := bstep (se 1 (by rfl) ⟨1324520, by rfl⟩ : syracuseStep 1766027 = 2649041) B2649041
theorem B1766039 : Blo 1764083 1766039 := bstep (se 1 (by rfl) ⟨1324529, by rfl⟩ : syracuseStep 1766039 = 2649059) B2649059
theorem B1766059 : Blo 1764083 1766059 := bstep (se 1 (by rfl) ⟨1324544, by rfl⟩ : syracuseStep 1766059 = 2649089) B2649089
theorem B1766071 : Blo 1764083 1766071 := bstep (se 1 (by rfl) ⟨1324553, by rfl⟩ : syracuseStep 1766071 = 2649107) B2649107
theorem B19337933 : Blo 1764083 19337933 := bstep (se 3 (by rfl) ⟨3625862, by rfl⟩ : syracuseStep 19337933 = 7251725) B7251725
theorem B2233099 : Blo 1764083 2233099 := bstep (se 1 (by rfl) ⟨1674824, by rfl⟩ : syracuseStep 2233099 = 3349649) B3349649
theorem B3969881 : Blo 1764083 3969881 := bstep (se 2 (by rfl) ⟨1488705, by rfl⟩ : syracuseStep 3969881 = 2977411) B2977411
theorem B18862949 : Blo 1764083 18862949 := bstep (se 4 (by rfl) ⟨1768401, by rfl⟩ : syracuseStep 18862949 = 3536803) B3536803
theorem B3969971 : Blo 1764083 3969971 := bstep (se 1 (by rfl) ⟨2977478, by rfl⟩ : syracuseStep 3969971 = 5954957) B5954957
theorem B3871691 : Blo 1764083 3871691 := bstep (se 1 (by rfl) ⟨2903768, by rfl⟩ : syracuseStep 3871691 = 5807537) B5807537
theorem B3970007 : Blo 1764083 3970007 := bstep (se 1 (by rfl) ⟨2977505, by rfl⟩ : syracuseStep 3970007 = 5955011) B5955011
theorem B3019801 : Blo 1764083 3019801 := bstep (se 2 (by rfl) ⟨1132425, by rfl⟩ : syracuseStep 3019801 = 2264851) B2264851
theorem B3396659 : Blo 1764083 3396659 := bstep (se 1 (by rfl) ⟨2547494, by rfl⟩ : syracuseStep 3396659 = 5094989) B5094989
theorem B4027457 : Blo 1764083 4027457 := bstep (se 2 (by rfl) ⟨1510296, by rfl⟩ : syracuseStep 4027457 = 3020593) B3020593
theorem B14308427 : Blo 1764083 14308427 := bstep (se 1 (by rfl) ⟨10731320, by rfl⟩ : syracuseStep 14308427 = 21462641) B21462641
theorem B2978903 : Blo 1764083 2978903 := bstep (se 1 (by rfl) ⟨2234177, by rfl⟩ : syracuseStep 2978903 = 4468355) B4468355
theorem B3970187 : Blo 1764083 3970187 := bstep (se 1 (by rfl) ⟨2977640, by rfl⟩ : syracuseStep 3970187 = 5955281) B5955281
theorem B3970241 : Blo 1764083 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B2979031 : Blo 1764083 2979031 := bstep (se 1 (by rfl) ⟨2234273, by rfl⟩ : syracuseStep 2979031 = 4468547) B4468547
theorem B3396889 : Blo 1764083 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B4470167 : Blo 1764083 4470167 := bstep (se 1 (by rfl) ⟨3352625, by rfl⟩ : syracuseStep 4470167 = 6705251) B6705251
theorem B3970457 : Blo 1764083 3970457 := bstep (se 2 (by rfl) ⟨1488921, by rfl⟩ : syracuseStep 3970457 = 2977843) B2977843
theorem B4838849 : Blo 1764083 4838849 := bstep (se 2 (by rfl) ⟨1814568, by rfl⟩ : syracuseStep 4838849 = 3629137) B3629137
theorem B5027275 : Blo 1764083 5027275 := bstep (se 1 (by rfl) ⟨3770456, by rfl⟩ : syracuseStep 5027275 = 7540913) B7540913
theorem B3970547 : Blo 1764083 3970547 := bstep (se 1 (by rfl) ⟨2977910, by rfl⟩ : syracuseStep 3970547 = 5955821) B5955821
theorem B3577367 : Blo 1764083 3577367 := bstep (se 1 (by rfl) ⟨2683025, by rfl⟩ : syracuseStep 3577367 = 5366051) B5366051
theorem B3970583 : Blo 1764083 3970583 := bstep (se 1 (by rfl) ⟨2977937, by rfl⟩ : syracuseStep 3970583 = 5955875) B5955875
theorem B4838935 : Blo 1764083 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B8599115 : Blo 1764083 8599115 := bstep (se 1 (by rfl) ⟨6449336, by rfl⟩ : syracuseStep 8599115 = 12898673) B12898673
theorem B3970763 : Blo 1764083 3970763 := bstep (se 1 (by rfl) ⟨2978072, by rfl⟩ : syracuseStep 3970763 = 5956145) B5956145
theorem B2234071 : Blo 1764083 2234071 := bstep (se 1 (by rfl) ⟨1675553, by rfl⟩ : syracuseStep 2234071 = 3351107) B3351107
theorem B3970817 : Blo 1764083 3970817 := bstep (se 2 (by rfl) ⟨1489056, by rfl⟩ : syracuseStep 3970817 = 2978113) B2978113
theorem B2979659 : Blo 1764083 2979659 := bstep (se 1 (by rfl) ⟨2234744, by rfl⟩ : syracuseStep 2979659 = 4469489) B4469489
theorem B5027777 : Blo 1764083 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B2979787 : Blo 1764083 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B3971033 : Blo 1764083 3971033 := bstep (se 2 (by rfl) ⟨1489137, by rfl⟩ : syracuseStep 3971033 = 2978275) B2978275
theorem B3971123 : Blo 1764083 3971123 := bstep (se 1 (by rfl) ⟨2978342, by rfl⟩ : syracuseStep 3971123 = 5956685) B5956685
theorem B3971159 : Blo 1764083 3971159 := bstep (se 1 (by rfl) ⟨2978369, by rfl⟩ : syracuseStep 3971159 = 5956739) B5956739
theorem B2979929 : Blo 1764083 2979929 := bstep (se 2 (by rfl) ⟨1117473, by rfl⟩ : syracuseStep 2979929 = 2234947) B2234947
theorem B10049629 : Blo 1764083 10049629 := bstep (se 3 (by rfl) ⟨1884305, by rfl⟩ : syracuseStep 10049629 = 3768611) B3768611
theorem B7157963 : Blo 1764083 7157963 := bstep (se 1 (by rfl) ⟨5368472, by rfl⟩ : syracuseStep 7157963 = 10736945) B10736945
theorem B2685143 : Blo 1764083 2685143 := bstep (se 1 (by rfl) ⟨2013857, by rfl⟩ : syracuseStep 2685143 = 4027715) B4027715
theorem B2980057 : Blo 1764083 2980057 := bstep (se 2 (by rfl) ⟨1117521, by rfl⟩ : syracuseStep 2980057 = 2235043) B2235043
theorem B3971339 : Blo 1764083 3971339 := bstep (se 1 (by rfl) ⟨2978504, by rfl⟩ : syracuseStep 3971339 = 5957009) B5957009
theorem B5028119 : Blo 1764083 5028119 := bstep (se 1 (by rfl) ⟨3771089, by rfl⟩ : syracuseStep 5028119 = 7542179) B7542179
theorem B2685209 : Blo 1764083 2685209 := bstep (se 2 (by rfl) ⟨1006953, by rfl⟩ : syracuseStep 2685209 = 2013907) B2013907
theorem B18872621 : Blo 1764083 18872621 := bstep (se 3 (by rfl) ⟨3538616, by rfl⟩ : syracuseStep 18872621 = 7077233) B7077233
theorem B3971393 : Blo 1764083 3971393 := bstep (se 2 (by rfl) ⟨1489272, by rfl⟩ : syracuseStep 3971393 = 2978545) B2978545
theorem B68802929 : Blo 1764083 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B5953985 : Blo 1764083 5953985 := bstep (se 2 (by rfl) ⟨2232744, by rfl⟩ : syracuseStep 5953985 = 4465489) B4465489
theorem B2234891 : Blo 1764083 2234891 := bstep (se 1 (by rfl) ⟨1676168, by rfl⟩ : syracuseStep 2234891 = 3352337) B3352337
theorem B36239885 : Blo 1764083 36239885 := bstep (se 3 (by rfl) ⟨6794978, by rfl⟩ : syracuseStep 36239885 = 13589957) B13589957
theorem B3971609 : Blo 1764083 3971609 := bstep (se 2 (by rfl) ⟨1489353, by rfl⟩ : syracuseStep 3971609 = 2978707) B2978707
theorem B2120267 : Blo 1764083 2120267 := bstep (se 1 (by rfl) ⟨1590200, by rfl⟩ : syracuseStep 2120267 = 3180401) B3180401
theorem B3971699 : Blo 1764083 3971699 := bstep (se 1 (by rfl) ⟨2978774, by rfl⟩ : syracuseStep 3971699 = 5957549) B5957549
theorem B10738307 : Blo 1764083 10738307 := bstep (se 1 (by rfl) ⟨8053730, by rfl⟩ : syracuseStep 10738307 = 16107461) B16107461
theorem B3971735 : Blo 1764083 3971735 := bstep (se 1 (by rfl) ⟨2978801, by rfl⟩ : syracuseStep 3971735 = 5957603) B5957603
theorem B2120459 : Blo 1764083 2120459 := bstep (se 1 (by rfl) ⟨1590344, by rfl⟩ : syracuseStep 2120459 = 3180689) B3180689
theorem B22936385 : Blo 1764083 22936385 := bstep (se 2 (by rfl) ⟨8601144, by rfl⟩ : syracuseStep 22936385 = 17202289) B17202289
theorem B3971915 : Blo 1764083 3971915 := bstep (se 1 (by rfl) ⟨2978936, by rfl⟩ : syracuseStep 3971915 = 5957873) B5957873
theorem B20380517 : Blo 1764083 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B3971969 : Blo 1764083 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B13400963 : Blo 1764083 13400963 := bstep (se 1 (by rfl) ⟨10050722, by rfl⟩ : syracuseStep 13400963 = 20101445) B20101445
theorem B3349451 : Blo 1764083 3349451 := bstep (se 1 (by rfl) ⟨2512088, by rfl⟩ : syracuseStep 3349451 = 5024177) B5024177
theorem B5954525 : Blo 1764083 5954525 := bstep (se 3 (by rfl) ⟨1116473, by rfl⟩ : syracuseStep 5954525 = 2232947) B2232947
theorem B3349505 : Blo 1764083 3349505 := bstep (se 2 (by rfl) ⟨1256064, by rfl⟩ : syracuseStep 3349505 = 2512129) B2512129
theorem B12729419 : Blo 1764083 12729419 := bstep (se 1 (by rfl) ⟨9547064, by rfl⟩ : syracuseStep 12729419 = 19094129) B19094129
theorem B3972185 : Blo 1764083 3972185 := bstep (se 2 (by rfl) ⟨1489569, by rfl⟩ : syracuseStep 3972185 = 2979139) B2979139
theorem B6364291 : Blo 1764083 6364291 := bstep (se 1 (by rfl) ⟨4773218, by rfl⟩ : syracuseStep 6364291 = 9546437) B9546437
theorem B3972275 : Blo 1764083 3972275 := bstep (se 1 (by rfl) ⟨2979206, by rfl⟩ : syracuseStep 3972275 = 5958413) B5958413
theorem B3972311 : Blo 1764083 3972311 := bstep (se 1 (by rfl) ⟨2979233, by rfl⟩ : syracuseStep 3972311 = 5958467) B5958467
theorem B12721369 : Blo 1764083 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B30555397 : Blo 1764083 30555397 := bstep (se 4 (by rfl) ⟨2864568, by rfl⟩ : syracuseStep 30555397 = 5729137) B5729137
theorem B4242763 : Blo 1764083 4242763 := bstep (se 1 (by rfl) ⟨3182072, by rfl⟩ : syracuseStep 4242763 = 6364145) B6364145
theorem B33922421 : Blo 1764083 33922421 := bstep (se 5 (by rfl) ⟨1590113, by rfl⟩ : syracuseStep 33922421 = 3180227) B3180227
theorem B3579265 : Blo 1764083 3579265 := bstep (se 2 (by rfl) ⟨1342224, by rfl⟩ : syracuseStep 3579265 = 2684449) B2684449
theorem B3972491 : Blo 1764083 3972491 := bstep (se 1 (by rfl) ⟨2979368, by rfl⟩ : syracuseStep 3972491 = 5958737) B5958737
theorem B10190231 : Blo 1764083 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B3972545 : Blo 1764083 3972545 := bstep (se 2 (by rfl) ⟨1489704, by rfl⟩ : syracuseStep 3972545 = 2979409) B2979409
theorem B3767809 : Blo 1764083 3767809 := bstep (se 2 (by rfl) ⟨1412928, by rfl⟩ : syracuseStep 3767809 = 2825857) B2825857
theorem B6700589 : Blo 1764083 6700589 := bstep (se 3 (by rfl) ⟨1256360, by rfl⟩ : syracuseStep 6700589 = 2512721) B2512721
theorem B15081005 : Blo 1764083 15081005 := bstep (se 3 (by rfl) ⟨2827688, by rfl⟩ : syracuseStep 15081005 = 5655377) B5655377
theorem B4242995 : Blo 1764083 4242995 := bstep (se 1 (by rfl) ⟨3182246, by rfl⟩ : syracuseStep 4242995 = 6364493) B6364493
theorem B4243033 : Blo 1764083 4243033 := bstep (se 2 (by rfl) ⟨1591137, by rfl⟩ : syracuseStep 4243033 = 3182275) B3182275
theorem B8937053 : Blo 1764083 8937053 := bstep (se 3 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 8937053 = 3351395) B3351395
theorem B3972761 : Blo 1764083 3972761 := bstep (se 2 (by rfl) ⟨1489785, by rfl⟩ : syracuseStep 3972761 = 2979571) B2979571
theorem B27549389 : Blo 1764083 27549389 := bstep (se 3 (by rfl) ⟨5165510, by rfl⟩ : syracuseStep 27549389 = 10331021) B10331021
theorem B3972851 : Blo 1764083 3972851 := bstep (se 1 (by rfl) ⟨2979638, by rfl⟩ : syracuseStep 3972851 = 5959277) B5959277
theorem B10190609 : Blo 1764083 10190609 := bstep (se 2 (by rfl) ⟨3821478, by rfl⟩ : syracuseStep 10190609 = 7642957) B7642957
theorem B3972887 : Blo 1764083 3972887 := bstep (se 1 (by rfl) ⟨2979665, by rfl⟩ : syracuseStep 3972887 = 5959331) B5959331
theorem B1883947 : Blo 1764083 1883947 := bstep (se 1 (by rfl) ⟨1412960, by rfl⟩ : syracuseStep 1883947 = 2825921) B2825921
theorem B3350423 : Blo 1764083 3350423 := bstep (se 1 (by rfl) ⟨2512817, by rfl⟩ : syracuseStep 3350423 = 5025635) B5025635
theorem B34373555 : Blo 1764083 34373555 := bstep (se 1 (by rfl) ⟨25780166, by rfl⟩ : syracuseStep 34373555 = 51560333) B51560333
theorem B5095361 : Blo 1764083 5095361 := bstep (se 2 (by rfl) ⟨1910760, by rfl⟩ : syracuseStep 5095361 = 3821521) B3821521
theorem B3973067 : Blo 1764083 3973067 := bstep (se 1 (by rfl) ⟨2979800, by rfl⟩ : syracuseStep 3973067 = 5959601) B5959601
theorem B10051613 : Blo 1764083 10051613 := bstep (se 3 (by rfl) ⟨1884677, by rfl⟩ : syracuseStep 10051613 = 3769355) B3769355
theorem B2826299 : Blo 1764083 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B8937539 : Blo 1764083 8937539 := bstep (se 1 (by rfl) ⟨6703154, by rfl⟩ : syracuseStep 8937539 = 13406309) B13406309
theorem B2646203 : Blo 1764083 2646203 := bstep (se 1 (by rfl) ⟨1984652, by rfl⟩ : syracuseStep 2646203 = 3969305) B3969305
theorem B28639433 : Blo 1764083 28639433 := bstep (se 2 (by rfl) ⟨10739787, by rfl⟩ : syracuseStep 28639433 = 21479575) B21479575
theorem B57229553 : Blo 1764083 57229553 := bstep (se 2 (by rfl) ⟨21461082, by rfl⟩ : syracuseStep 57229553 = 42922165) B42922165
theorem B2646263 : Blo 1764083 2646263 := bstep (se 1 (by rfl) ⟨1984697, by rfl⟩ : syracuseStep 2646263 = 3969395) B3969395
theorem B2646287 : Blo 1764083 2646287 := bstep (se 1 (by rfl) ⟨1984715, by rfl⟩ : syracuseStep 2646287 = 3969431) B3969431
theorem B3973391 : Blo 1764083 3973391 := bstep (se 1 (by rfl) ⟨2980043, by rfl⟩ : syracuseStep 3973391 = 5960087) B5960087
theorem B3973409 : Blo 1764083 3973409 := bstep (se 2 (by rfl) ⟨1490028, by rfl⟩ : syracuseStep 3973409 = 2980057) B2980057
theorem B2646329 : Blo 1764083 2646329 := bstep (se 2 (by rfl) ⟨992373, by rfl⟩ : syracuseStep 2646329 = 1984747) B1984747
theorem B2384263 : Blo 1764083 2384263 := bstep (se 1 (by rfl) ⟨1788197, by rfl⟩ : syracuseStep 2384263 = 3576395) B3576395
theorem B2646407 : Blo 1764083 2646407 := bstep (se 1 (by rfl) ⟨1984805, by rfl⟩ : syracuseStep 2646407 = 3969611) B3969611
theorem B8937863 : Blo 1764083 8937863 := bstep (se 1 (by rfl) ⟨6703397, by rfl⟩ : syracuseStep 8937863 = 13406795) B13406795
theorem B2646443 : Blo 1764083 2646443 := bstep (se 1 (by rfl) ⟨1984832, by rfl⟩ : syracuseStep 2646443 = 3969665) B3969665
theorem B2646473 : Blo 1764083 2646473 := bstep (se 2 (by rfl) ⟨992427, by rfl⟩ : syracuseStep 2646473 = 1984855) B1984855
theorem B81510947 : Blo 1764083 81510947 := bstep (se 1 (by rfl) ⟨61133210, by rfl⟩ : syracuseStep 81510947 = 122266421) B122266421
theorem B2646587 : Blo 1764083 2646587 := bstep (se 1 (by rfl) ⟨1984940, by rfl⟩ : syracuseStep 2646587 = 3969881) B3969881
theorem B12575299 : Blo 1764083 12575299 := bstep (se 1 (by rfl) ⟨9431474, by rfl⟩ : syracuseStep 12575299 = 18862949) B18862949
theorem B7848535 : Blo 1764083 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B2646647 : Blo 1764083 2646647 := bstep (se 1 (by rfl) ⟨1984985, by rfl⟩ : syracuseStep 2646647 = 3969971) B3969971
theorem B5653111 : Blo 1764083 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B2581127 : Blo 1764083 2581127 := bstep (se 1 (by rfl) ⟨1935845, by rfl⟩ : syracuseStep 2581127 = 3871691) B3871691
theorem B2646671 : Blo 1764083 2646671 := bstep (se 1 (by rfl) ⟨1985003, by rfl⟩ : syracuseStep 2646671 = 3970007) B3970007
theorem B2646713 : Blo 1764083 2646713 := bstep (se 2 (by rfl) ⟨992517, by rfl⟩ : syracuseStep 2646713 = 1985035) B1985035
theorem B7160557 : Blo 1764083 7160557 := bstep (se 3 (by rfl) ⟨1342604, by rfl⟩ : syracuseStep 7160557 = 2685209) B2685209
theorem B2646791 : Blo 1764083 2646791 := bstep (se 1 (by rfl) ⟨1985093, by rfl⟩ : syracuseStep 2646791 = 3970187) B3970187
theorem B2646827 : Blo 1764083 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B2646857 : Blo 1764083 2646857 := bstep (se 2 (by rfl) ⟨992571, by rfl⟩ : syracuseStep 2646857 = 1985143) B1985143
theorem B2646971 : Blo 1764083 2646971 := bstep (se 1 (by rfl) ⟨1985228, by rfl⟩ : syracuseStep 2646971 = 3970457) B3970457
theorem B2647031 : Blo 1764083 2647031 := bstep (se 1 (by rfl) ⟨1985273, by rfl⟩ : syracuseStep 2647031 = 3970547) B3970547
theorem B2384911 : Blo 1764083 2384911 := bstep (se 1 (by rfl) ⟨1788683, by rfl⟩ : syracuseStep 2384911 = 3577367) B3577367
theorem B2647055 : Blo 1764083 2647055 := bstep (se 1 (by rfl) ⟨1985291, by rfl⟩ : syracuseStep 2647055 = 3970583) B3970583
theorem B6038557 : Blo 1764083 6038557 := bstep (se 3 (by rfl) ⟨1132229, by rfl⟩ : syracuseStep 6038557 = 2264459) B2264459
theorem B2647097 : Blo 1764083 2647097 := bstep (se 2 (by rfl) ⟨992661, by rfl⟩ : syracuseStep 2647097 = 1985323) B1985323
theorem B2647175 : Blo 1764083 2647175 := bstep (se 1 (by rfl) ⟨1985381, by rfl⟩ : syracuseStep 2647175 = 3970763) B3970763
theorem B2647211 : Blo 1764083 2647211 := bstep (se 1 (by rfl) ⟨1985408, by rfl⟩ : syracuseStep 2647211 = 3970817) B3970817
theorem B2647241 : Blo 1764083 2647241 := bstep (se 2 (by rfl) ⟨992715, by rfl⟩ : syracuseStep 2647241 = 1985431) B1985431
theorem B3351851 : Blo 1764083 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B2647355 : Blo 1764083 2647355 := bstep (se 1 (by rfl) ⟨1985516, by rfl⟩ : syracuseStep 2647355 = 3971033) B3971033
theorem B2647415 : Blo 1764083 2647415 := bstep (se 1 (by rfl) ⟨1985561, by rfl⟩ : syracuseStep 2647415 = 3971123) B3971123
theorem B2647439 : Blo 1764083 2647439 := bstep (se 1 (by rfl) ⟨1985579, by rfl⟩ : syracuseStep 2647439 = 3971159) B3971159
theorem B11306425 : Blo 1764083 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B2647481 : Blo 1764083 2647481 := bstep (se 2 (by rfl) ⟨992805, by rfl⟩ : syracuseStep 2647481 = 1985611) B1985611
theorem B2647559 : Blo 1764083 2647559 := bstep (se 1 (by rfl) ⟨1985669, by rfl⟩ : syracuseStep 2647559 = 3971339) B3971339
theorem B3352079 : Blo 1764083 3352079 := bstep (se 1 (by rfl) ⟨2514059, by rfl⟩ : syracuseStep 3352079 = 5028119) B5028119
theorem B5654045 : Blo 1764083 5654045 := bstep (se 3 (by rfl) ⟨1060133, by rfl⟩ : syracuseStep 5654045 = 2120267) B2120267
theorem B2647595 : Blo 1764083 2647595 := bstep (se 1 (by rfl) ⟨1985696, by rfl⟩ : syracuseStep 2647595 = 3971393) B3971393
theorem B2647625 : Blo 1764083 2647625 := bstep (se 2 (by rfl) ⟨992859, by rfl⟩ : syracuseStep 2647625 = 1985719) B1985719
theorem B45868619 : Blo 1764083 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B40740529 : Blo 1764083 40740529 := bstep (se 2 (by rfl) ⟨15277698, by rfl⟩ : syracuseStep 40740529 = 30555397) B30555397
theorem B24159923 : Blo 1764083 24159923 := bstep (se 1 (by rfl) ⟨18119942, by rfl⟩ : syracuseStep 24159923 = 36239885) B36239885
theorem B2647739 : Blo 1764083 2647739 := bstep (se 1 (by rfl) ⟨1985804, by rfl⟩ : syracuseStep 2647739 = 3971609) B3971609
theorem B22628069 : Blo 1764083 22628069 := bstep (se 4 (by rfl) ⟨2121381, by rfl⟩ : syracuseStep 22628069 = 4242763) B4242763
theorem B2647799 : Blo 1764083 2647799 := bstep (se 1 (by rfl) ⟨1985849, by rfl⟩ : syracuseStep 2647799 = 3971699) B3971699
theorem B2647823 : Blo 1764083 2647823 := bstep (se 1 (by rfl) ⟨1985867, by rfl⟩ : syracuseStep 2647823 = 3971735) B3971735
theorem B2647865 : Blo 1764083 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B2647943 : Blo 1764083 2647943 := bstep (se 1 (by rfl) ⟨1985957, by rfl⟩ : syracuseStep 2647943 = 3971915) B3971915
theorem B2647979 : Blo 1764083 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B6703033 : Blo 1764083 6703033 := bstep (se 2 (by rfl) ⟨2513637, by rfl⟩ : syracuseStep 6703033 = 5027275) B5027275
theorem B2648009 : Blo 1764083 2648009 := bstep (se 2 (by rfl) ⟨993003, by rfl⟩ : syracuseStep 2648009 = 1986007) B1986007
theorem B5023745 : Blo 1764083 5023745 := bstep (se 2 (by rfl) ⟨1883904, by rfl⟩ : syracuseStep 5023745 = 3767809) B3767809
theorem B5654557 : Blo 1764083 5654557 := bstep (se 3 (by rfl) ⟨1060229, by rfl⟩ : syracuseStep 5654557 = 2120459) B2120459
theorem B41314349 : Blo 1764083 41314349 := bstep (se 3 (by rfl) ⟨7746440, by rfl⟩ : syracuseStep 41314349 = 15492881) B15492881
theorem B2648123 : Blo 1764083 2648123 := bstep (se 1 (by rfl) ⟨1986092, by rfl⟩ : syracuseStep 2648123 = 3972185) B3972185
theorem B2648183 : Blo 1764083 2648183 := bstep (se 1 (by rfl) ⟨1986137, by rfl⟩ : syracuseStep 2648183 = 3972275) B3972275
theorem B2648207 : Blo 1764083 2648207 := bstep (se 1 (by rfl) ⟨1986155, by rfl⟩ : syracuseStep 2648207 = 3972311) B3972311
theorem B61163693 : Blo 1764083 61163693 := bstep (se 3 (by rfl) ⟨11468192, by rfl⟩ : syracuseStep 61163693 = 22936385) B22936385
theorem B2648249 : Blo 1764083 2648249 := bstep (se 2 (by rfl) ⟨993093, by rfl⟩ : syracuseStep 2648249 = 1986187) B1986187
theorem B2648327 : Blo 1764083 2648327 := bstep (se 1 (by rfl) ⟨1986245, by rfl⟩ : syracuseStep 2648327 = 3972491) B3972491
theorem B1984783 : Blo 1764083 1984783 := bstep (se 1 (by rfl) ⟨1488587, by rfl⟩ : syracuseStep 1984783 = 2977175) B2977175
theorem B6793487 : Blo 1764083 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B2648363 : Blo 1764083 2648363 := bstep (se 1 (by rfl) ⟨1986272, by rfl⟩ : syracuseStep 2648363 = 3972545) B3972545
theorem B2648393 : Blo 1764083 2648393 := bstep (se 2 (by rfl) ⟨993147, by rfl⟩ : syracuseStep 2648393 = 1986295) B1986295
theorem B4467059 : Blo 1764083 4467059 := bstep (se 1 (by rfl) ⟨3350294, by rfl⟩ : syracuseStep 4467059 = 6700589) B6700589
theorem B10054003 : Blo 1764083 10054003 := bstep (se 1 (by rfl) ⟨7540502, by rfl⟩ : syracuseStep 10054003 = 15081005) B15081005
theorem B2828663 : Blo 1764083 2828663 := bstep (se 1 (by rfl) ⟨2121497, by rfl⟩ : syracuseStep 2828663 = 4242995) B4242995
theorem B5958035 : Blo 1764083 5958035 := bstep (se 1 (by rfl) ⟨4468526, by rfl⟩ : syracuseStep 5958035 = 8937053) B8937053
theorem B2386361 : Blo 1764083 2386361 := bstep (se 2 (by rfl) ⟨894885, by rfl⟩ : syracuseStep 2386361 = 1789771) B1789771
theorem B2648507 : Blo 1764083 2648507 := bstep (se 1 (by rfl) ⟨1986380, by rfl⟩ : syracuseStep 2648507 = 3972761) B3972761
theorem B2648567 : Blo 1764083 2648567 := bstep (se 1 (by rfl) ⟨1986425, by rfl⟩ : syracuseStep 2648567 = 3972851) B3972851
theorem B6793739 : Blo 1764083 6793739 := bstep (se 1 (by rfl) ⟨5095304, by rfl⟩ : syracuseStep 6793739 = 10190609) B10190609
theorem B2648591 : Blo 1764083 2648591 := bstep (se 1 (by rfl) ⟨1986443, by rfl⟩ : syracuseStep 2648591 = 3972887) B3972887
theorem B8931869 : Blo 1764083 8931869 := bstep (se 3 (by rfl) ⟨1674725, by rfl⟩ : syracuseStep 8931869 = 3349451) B3349451
theorem B14305835 : Blo 1764083 14305835 := bstep (se 1 (by rfl) ⟨10729376, by rfl⟩ : syracuseStep 14305835 = 21458753) B21458753
theorem B16108075 : Blo 1764083 16108075 := bstep (se 1 (by rfl) ⟨12081056, by rfl⟩ : syracuseStep 16108075 = 24162113) B24162113
theorem B2648633 : Blo 1764083 2648633 := bstep (se 2 (by rfl) ⟨993237, by rfl⟩ : syracuseStep 2648633 = 1986475) B1986475
theorem B22915703 : Blo 1764083 22915703 := bstep (se 1 (by rfl) ⟨17186777, by rfl⟩ : syracuseStep 22915703 = 34373555) B34373555
theorem B2648711 : Blo 1764083 2648711 := bstep (se 1 (by rfl) ⟨1986533, by rfl⟩ : syracuseStep 2648711 = 3973067) B3973067
theorem B2648747 : Blo 1764083 2648747 := bstep (se 1 (by rfl) ⟨1986560, by rfl⟩ : syracuseStep 2648747 = 3973121) B3973121
theorem B2648777 : Blo 1764083 2648777 := bstep (se 2 (by rfl) ⟨993291, by rfl⟩ : syracuseStep 2648777 = 1986583) B1986583
theorem B8055497 : Blo 1764083 8055497 := bstep (se 2 (by rfl) ⟨3020811, by rfl⟩ : syracuseStep 8055497 = 6041623) B6041623
theorem B1764103 : Blo 1764083 1764103 := bstep (se 1 (by rfl) ⟨1323077, by rfl⟩ : syracuseStep 1764103 = 2646155) B2646155
theorem B1985287 : Blo 1764083 1985287 := bstep (se 1 (by rfl) ⟨1488965, by rfl⟩ : syracuseStep 1985287 = 2977931) B2977931
theorem B1764111 : Blo 1764083 1764111 := bstep (se 1 (by rfl) ⟨1323083, by rfl⟩ : syracuseStep 1764111 = 2646167) B2646167
theorem B1764155 : Blo 1764083 1764155 := bstep (se 1 (by rfl) ⟨1323116, by rfl⟩ : syracuseStep 1764155 = 2646233) B2646233
theorem B2648891 : Blo 1764083 2648891 := bstep (se 1 (by rfl) ⟨1986668, by rfl⟩ : syracuseStep 2648891 = 3973337) B3973337
theorem B9055091 : Blo 1764083 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B4467575 : Blo 1764083 4467575 := bstep (se 1 (by rfl) ⟨3350681, by rfl⟩ : syracuseStep 4467575 = 6701363) B6701363
theorem B2648951 : Blo 1764083 2648951 := bstep (se 1 (by rfl) ⟨1986713, by rfl⟩ : syracuseStep 2648951 = 3973427) B3973427
theorem B1764231 : Blo 1764083 1764231 := bstep (se 1 (by rfl) ⟨1323173, by rfl⟩ : syracuseStep 1764231 = 2646347) B2646347
theorem B1764239 : Blo 1764083 1764239 := bstep (se 1 (by rfl) ⟨1323179, by rfl⟩ : syracuseStep 1764239 = 2646359) B2646359
theorem B2648975 : Blo 1764083 2648975 := bstep (se 1 (by rfl) ⟨1986731, by rfl⟩ : syracuseStep 2648975 = 3973463) B3973463
theorem B2649017 : Blo 1764083 2649017 := bstep (se 2 (by rfl) ⟨993381, by rfl⟩ : syracuseStep 2649017 = 1986763) B1986763
theorem B1764283 : Blo 1764083 1764283 := bstep (se 1 (by rfl) ⟨1323212, by rfl⟩ : syracuseStep 1764283 = 2646425) B2646425
theorem B1985467 : Blo 1764083 1985467 := bstep (se 1 (by rfl) ⟨1489100, by rfl⟩ : syracuseStep 1985467 = 2978201) B2978201
theorem B5024713 : Blo 1764083 5024713 := bstep (se 2 (by rfl) ⟨1884267, by rfl⟩ : syracuseStep 5024713 = 3768535) B3768535
theorem B8932355 : Blo 1764083 8932355 := bstep (se 1 (by rfl) ⟨6699266, by rfl⟩ : syracuseStep 8932355 = 13398533) B13398533
theorem B1764359 : Blo 1764083 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B2649095 : Blo 1764083 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B1764367 : Blo 1764083 1764367 := bstep (se 1 (by rfl) ⟨1323275, by rfl⟩ : syracuseStep 1764367 = 2646551) B2646551
theorem B1764411 : Blo 1764083 1764411 := bstep (se 1 (by rfl) ⟨1323308, by rfl⟩ : syracuseStep 1764411 = 2646617) B2646617
theorem B9669719 : Blo 1764083 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B1764487 : Blo 1764083 1764487 := bstep (se 1 (by rfl) ⟨1323365, by rfl⟩ : syracuseStep 1764487 = 2646731) B2646731
theorem B4025479 : Blo 1764083 4025479 := bstep (se 1 (by rfl) ⟨3019109, by rfl⟩ : syracuseStep 4025479 = 6038219) B6038219
theorem B1764495 : Blo 1764083 1764495 := bstep (se 1 (by rfl) ⟨1323371, by rfl⟩ : syracuseStep 1764495 = 2646743) B2646743
theorem B1764539 : Blo 1764083 1764539 := bstep (se 1 (by rfl) ⟨1323404, by rfl⟩ : syracuseStep 1764539 = 2646809) B2646809
theorem B1764615 : Blo 1764083 1764615 := bstep (se 1 (by rfl) ⟨1323461, by rfl⟩ : syracuseStep 1764615 = 2646923) B2646923
theorem B1764623 : Blo 1764083 1764623 := bstep (se 1 (by rfl) ⟨1323467, by rfl⟩ : syracuseStep 1764623 = 2646935) B2646935
theorem B2977067 : Blo 1764083 2977067 := bstep (se 1 (by rfl) ⟨2232800, by rfl⟩ : syracuseStep 2977067 = 4465601) B4465601
theorem B1764667 : Blo 1764083 1764667 := bstep (se 1 (by rfl) ⟨1323500, by rfl⟩ : syracuseStep 1764667 = 2647001) B2647001
theorem B2682247 : Blo 1764083 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B1764743 : Blo 1764083 1764743 := bstep (se 1 (by rfl) ⟨1323557, by rfl⟩ : syracuseStep 1764743 = 2647115) B2647115
theorem B1764751 : Blo 1764083 1764751 := bstep (se 1 (by rfl) ⟨1323563, by rfl⟩ : syracuseStep 1764751 = 2647127) B2647127
theorem B1985935 : Blo 1764083 1985935 := bstep (se 1 (by rfl) ⟨1489451, by rfl⟩ : syracuseStep 1985935 = 2978903) B2978903
theorem B1764795 : Blo 1764083 1764795 := bstep (se 1 (by rfl) ⟨1323596, by rfl⟩ : syracuseStep 1764795 = 2647193) B2647193
theorem B1764871 : Blo 1764083 1764871 := bstep (se 1 (by rfl) ⟨1323653, by rfl⟩ : syracuseStep 1764871 = 2647307) B2647307
theorem B1764879 : Blo 1764083 1764879 := bstep (se 1 (by rfl) ⟨1323659, by rfl⟩ : syracuseStep 1764879 = 2647319) B2647319
theorem B1764923 : Blo 1764083 1764923 := bstep (se 1 (by rfl) ⟨1323692, by rfl⟩ : syracuseStep 1764923 = 2647385) B2647385
theorem B1764999 : Blo 1764083 1764999 := bstep (se 1 (by rfl) ⟨1323749, by rfl⟩ : syracuseStep 1764999 = 2647499) B2647499
theorem B1765007 : Blo 1764083 1765007 := bstep (se 1 (by rfl) ⟨1323755, by rfl⟩ : syracuseStep 1765007 = 2647511) B2647511
theorem B2682539 : Blo 1764083 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B2977465 : Blo 1764083 2977465 := bstep (se 2 (by rfl) ⟨1116549, by rfl⟩ : syracuseStep 2977465 = 2233099) B2233099
theorem B1765051 : Blo 1764083 1765051 := bstep (se 1 (by rfl) ⟨1323788, by rfl⟩ : syracuseStep 1765051 = 2647577) B2647577
theorem B1765127 : Blo 1764083 1765127 := bstep (se 1 (by rfl) ⟨1323845, by rfl⟩ : syracuseStep 1765127 = 2647691) B2647691
theorem B1765135 : Blo 1764083 1765135 := bstep (se 1 (by rfl) ⟨1323851, by rfl⟩ : syracuseStep 1765135 = 2647703) B2647703
theorem B5959439 : Blo 1764083 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B10055461 : Blo 1764083 10055461 := bstep (se 4 (by rfl) ⟨942699, by rfl⟩ : syracuseStep 10055461 = 1885399) B1885399
theorem B1765179 : Blo 1764083 1765179 := bstep (se 1 (by rfl) ⟨1323884, by rfl⟩ : syracuseStep 1765179 = 2647769) B2647769
theorem B4468567 : Blo 1764083 4468567 := bstep (se 1 (by rfl) ⟨3351425, by rfl⟩ : syracuseStep 4468567 = 6702851) B6702851
theorem B1765255 : Blo 1764083 1765255 := bstep (se 1 (by rfl) ⟨1323941, by rfl⟩ : syracuseStep 1765255 = 2647883) B2647883
theorem B1986439 : Blo 1764083 1986439 := bstep (se 1 (by rfl) ⟨1489829, by rfl⟩ : syracuseStep 1986439 = 2979659) B2979659
theorem B1765263 : Blo 1764083 1765263 := bstep (se 1 (by rfl) ⟨1323947, by rfl⟩ : syracuseStep 1765263 = 2647895) B2647895
theorem B1765307 : Blo 1764083 1765307 := bstep (se 1 (by rfl) ⟨1323980, by rfl⟩ : syracuseStep 1765307 = 2647961) B2647961
theorem B1765383 : Blo 1764083 1765383 := bstep (se 1 (by rfl) ⟨1324037, by rfl⟩ : syracuseStep 1765383 = 2648075) B2648075
theorem B1765391 : Blo 1764083 1765391 := bstep (se 1 (by rfl) ⟨1324043, by rfl⟩ : syracuseStep 1765391 = 2648087) B2648087
theorem B9056285 : Blo 1764083 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B5959709 : Blo 1764083 5959709 := bstep (se 3 (by rfl) ⟨1117445, by rfl⟩ : syracuseStep 5959709 = 2234891) B2234891
theorem B4026401 : Blo 1764083 4026401 := bstep (se 2 (by rfl) ⟨1509900, by rfl⟩ : syracuseStep 4026401 = 3019801) B3019801
theorem B1765435 : Blo 1764083 1765435 := bstep (se 1 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 1765435 = 2648153) B2648153
theorem B1986619 : Blo 1764083 1986619 := bstep (se 1 (by rfl) ⟨1489964, by rfl⟩ : syracuseStep 1986619 = 2979929) B2979929
theorem B18116741 : Blo 1764083 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B4771975 : Blo 1764083 4771975 := bstep (se 1 (by rfl) ⟨3578981, by rfl⟩ : syracuseStep 4771975 = 7157963) B7157963
theorem B4468871 : Blo 1764083 4468871 := bstep (se 1 (by rfl) ⟨3351653, by rfl⟩ : syracuseStep 4468871 = 6703307) B6703307
theorem B1765511 : Blo 1764083 1765511 := bstep (se 1 (by rfl) ⟨1324133, by rfl⟩ : syracuseStep 1765511 = 2648267) B2648267
theorem B1765519 : Blo 1764083 1765519 := bstep (se 1 (by rfl) ⟨1324139, by rfl⟩ : syracuseStep 1765519 = 2648279) B2648279
theorem B1790095 : Blo 1764083 1790095 := bstep (se 1 (by rfl) ⟨1342571, by rfl⟩ : syracuseStep 1790095 = 2685143) B2685143
theorem B1765563 : Blo 1764083 1765563 := bstep (se 1 (by rfl) ⟨1324172, by rfl⟩ : syracuseStep 1765563 = 2648345) B2648345
theorem B1765639 : Blo 1764083 1765639 := bstep (se 1 (by rfl) ⟨1324229, by rfl⟩ : syracuseStep 1765639 = 2648459) B2648459
theorem B4469003 : Blo 1764083 4469003 := bstep (se 1 (by rfl) ⟨3351752, by rfl⟩ : syracuseStep 4469003 = 6703505) B6703505
theorem B4239631 : Blo 1764083 4239631 := bstep (se 1 (by rfl) ⟨3179723, by rfl⟩ : syracuseStep 4239631 = 6359447) B6359447
theorem B1765647 : Blo 1764083 1765647 := bstep (se 1 (by rfl) ⟨1324235, by rfl⟩ : syracuseStep 1765647 = 2648471) B2648471
theorem B16961825 : Blo 1764083 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B3969323 : Blo 1764083 3969323 := bstep (se 1 (by rfl) ⟨2976992, by rfl⟩ : syracuseStep 3969323 = 5953985) B5953985
theorem B10055987 : Blo 1764083 10055987 := bstep (se 1 (by rfl) ⟨7541990, by rfl⟩ : syracuseStep 10055987 = 15083981) B15083981
theorem B1765691 : Blo 1764083 1765691 := bstep (se 1 (by rfl) ⟨1324268, by rfl⟩ : syracuseStep 1765691 = 2648537) B2648537
theorem B2978167 : Blo 1764083 2978167 := bstep (se 1 (by rfl) ⟨2233625, by rfl⟩ : syracuseStep 2978167 = 4467251) B4467251
theorem B1765767 : Blo 1764083 1765767 := bstep (se 1 (by rfl) ⟨1324325, by rfl⟩ : syracuseStep 1765767 = 2648651) B2648651
theorem B1765775 : Blo 1764083 1765775 := bstep (se 1 (by rfl) ⟨1324331, by rfl⟩ : syracuseStep 1765775 = 2648663) B2648663
theorem B25784723 : Blo 1764083 25784723 := bstep (se 1 (by rfl) ⟨19338542, by rfl⟩ : syracuseStep 25784723 = 38677085) B38677085
theorem B1765819 : Blo 1764083 1765819 := bstep (se 1 (by rfl) ⟨1324364, by rfl⟩ : syracuseStep 1765819 = 2648729) B2648729
theorem B4772353 : Blo 1764083 4772353 := bstep (se 2 (by rfl) ⟨1789632, by rfl⟩ : syracuseStep 4772353 = 3579265) B3579265
theorem B1765895 : Blo 1764083 1765895 := bstep (se 1 (by rfl) ⟨1324421, by rfl⟩ : syracuseStep 1765895 = 2648843) B2648843
theorem B5026319 : Blo 1764083 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1765903 : Blo 1764083 1765903 := bstep (se 1 (by rfl) ⟨1324427, by rfl⟩ : syracuseStep 1765903 = 2648855) B2648855
theorem B2978363 : Blo 1764083 2978363 := bstep (se 1 (by rfl) ⟨2233772, by rfl⟩ : syracuseStep 2978363 = 4467545) B4467545
theorem B10736189 : Blo 1764083 10736189 := bstep (se 3 (by rfl) ⟨2013035, by rfl⟩ : syracuseStep 10736189 = 4026071) B4026071
theorem B1765947 : Blo 1764083 1765947 := bstep (se 1 (by rfl) ⟨1324460, by rfl⟩ : syracuseStep 1765947 = 2648921) B2648921
theorem B13587011 : Blo 1764083 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B8933975 : Blo 1764083 8933975 := bstep (se 1 (by rfl) ⟨6700481, by rfl⟩ : syracuseStep 8933975 = 13400963) B13400963
theorem B1766023 : Blo 1764083 1766023 := bstep (se 1 (by rfl) ⟨1324517, by rfl⟩ : syracuseStep 1766023 = 2649035) B2649035
theorem B1766031 : Blo 1764083 1766031 := bstep (se 1 (by rfl) ⟨1324523, by rfl⟩ : syracuseStep 1766031 = 2649047) B2649047
theorem B3969683 : Blo 1764083 3969683 := bstep (se 1 (by rfl) ⟨2977262, by rfl⟩ : syracuseStep 3969683 = 5954525) B5954525
theorem B2233003 : Blo 1764083 2233003 := bstep (se 1 (by rfl) ⟨1674752, by rfl⟩ : syracuseStep 2233003 = 3349505) B3349505
theorem B1766075 : Blo 1764083 1766075 := bstep (se 1 (by rfl) ⟨1324556, by rfl⟩ : syracuseStep 1766075 = 2649113) B2649113
theorem B3969737 : Blo 1764083 3969737 := bstep (se 2 (by rfl) ⟨1488651, by rfl⟩ : syracuseStep 3969737 = 2977303) B2977303
theorem B6451913 : Blo 1764083 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B4469519 : Blo 1764083 4469519 := bstep (se 1 (by rfl) ⟨3352139, by rfl⟩ : syracuseStep 4469519 = 6704279) B6704279
theorem B5657377 : Blo 1764083 5657377 := bstep (se 2 (by rfl) ⟨2121516, by rfl⟩ : syracuseStep 5657377 = 4243033) B4243033
theorem B4469651 : Blo 1764083 4469651 := bstep (se 1 (by rfl) ⟨3352238, by rfl⟩ : syracuseStep 4469651 = 6704477) B6704477
theorem B22614947 : Blo 1764083 22614947 := bstep (se 1 (by rfl) ⟨16961210, by rfl⟩ : syracuseStep 22614947 = 33922421) B33922421
theorem B2978761 : Blo 1764083 2978761 := bstep (se 2 (by rfl) ⟨1117035, by rfl⟩ : syracuseStep 2978761 = 2234071) B2234071
theorem B2511929 : Blo 1764083 2511929 := bstep (se 2 (by rfl) ⟨941973, by rfl⟩ : syracuseStep 2511929 = 1883947) B1883947
theorem B8934461 : Blo 1764083 8934461 := bstep (se 3 (by rfl) ⟨1675211, by rfl⟩ : syracuseStep 8934461 = 3350423) B3350423
theorem B3396907 : Blo 1764083 3396907 := bstep (se 1 (by rfl) ⟨2547680, by rfl⟩ : syracuseStep 3396907 = 5095361) B5095361
theorem B4240727 : Blo 1764083 4240727 := bstep (se 1 (by rfl) ⟨3180545, by rfl⟩ : syracuseStep 4240727 = 6361091) B6361091
theorem B16954717 : Blo 1764083 16954717 := bstep (se 3 (by rfl) ⟨3179009, by rfl⟩ : syracuseStep 16954717 = 6358019) B6358019
theorem B3970439 : Blo 1764083 3970439 := bstep (se 1 (by rfl) ⟨2977829, by rfl⟩ : syracuseStep 3970439 = 5955659) B5955659
theorem B4240841 : Blo 1764083 4240841 := bstep (se 2 (by rfl) ⟨1590315, by rfl⟩ : syracuseStep 4240841 = 3180631) B3180631
theorem B13399505 : Blo 1764083 13399505 := bstep (se 2 (by rfl) ⟨5024814, by rfl⟩ : syracuseStep 13399505 = 10049629) B10049629
theorem B9057757 : Blo 1764083 9057757 := bstep (se 3 (by rfl) ⟨1698329, by rfl⟩ : syracuseStep 9057757 = 3396659) B3396659
theorem B38155805 : Blo 1764083 38155805 := bstep (se 3 (by rfl) ⟨7154213, by rfl⟩ : syracuseStep 38155805 = 14308427) B14308427
theorem B171750941 : Blo 1764083 171750941 := bstep (se 3 (by rfl) ⟨32203301, by rfl⟩ : syracuseStep 171750941 = 64406603) B64406603
theorem B3970619 : Blo 1764083 3970619 := bstep (se 1 (by rfl) ⟨2977964, by rfl⟩ : syracuseStep 3970619 = 5955929) B5955929
theorem B4241015 : Blo 1764083 4241015 := bstep (se 1 (by rfl) ⟨3180761, by rfl⟩ : syracuseStep 4241015 = 6361523) B6361523
theorem B2233975 : Blo 1764083 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B5027447 : Blo 1764083 5027447 := bstep (se 1 (by rfl) ⟨3770585, by rfl⟩ : syracuseStep 5027447 = 7541171) B7541171
theorem B2979463 : Blo 1764083 2979463 := bstep (se 1 (by rfl) ⟨2234597, by rfl⟩ : syracuseStep 2979463 = 4469195) B4469195
theorem B3970745 : Blo 1764083 3970745 := bstep (se 2 (by rfl) ⟨1489029, by rfl⟩ : syracuseStep 3970745 = 2978059) B2978059
theorem B10057445 : Blo 1764083 10057445 := bstep (se 4 (by rfl) ⟨942885, by rfl⟩ : syracuseStep 10057445 = 1885771) B1885771
theorem B12891955 : Blo 1764083 12891955 := bstep (se 1 (by rfl) ⟨9668966, by rfl⟩ : syracuseStep 12891955 = 19337933) B19337933
theorem B12719987 : Blo 1764083 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B2234299 : Blo 1764083 2234299 := bstep (se 1 (by rfl) ⟨1675724, by rfl⟩ : syracuseStep 2234299 = 3351449) B3351449
theorem B3971087 : Blo 1764083 3971087 := bstep (se 1 (by rfl) ⟨2978315, by rfl⟩ : syracuseStep 3971087 = 5956631) B5956631
theorem B3971105 : Blo 1764083 3971105 := bstep (se 2 (by rfl) ⟨1489164, by rfl⟩ : syracuseStep 3971105 = 2978329) B2978329
theorem B7542827 : Blo 1764083 7542827 := bstep (se 1 (by rfl) ⟨5657120, by rfl⟩ : syracuseStep 7542827 = 11314241) B11314241
theorem B2684971 : Blo 1764083 2684971 := bstep (se 1 (by rfl) ⟨2013728, by rfl⟩ : syracuseStep 2684971 = 4027457) B4027457
theorem B2980111 : Blo 1764083 2980111 := bstep (se 1 (by rfl) ⟨2235083, by rfl⟩ : syracuseStep 2980111 = 4470167) B4470167
theorem B2119979 : Blo 1764083 2119979 := bstep (se 1 (by rfl) ⟨1589984, by rfl⟩ : syracuseStep 2119979 = 3179969) B3179969
theorem B3225899 : Blo 1764083 3225899 := bstep (se 1 (by rfl) ⟨2419424, by rfl⟩ : syracuseStep 3225899 = 4838849) B4838849
theorem B3971447 : Blo 1764083 3971447 := bstep (se 1 (by rfl) ⟨2978585, by rfl⟩ : syracuseStep 3971447 = 5957171) B5957171
theorem B5732743 : Blo 1764083 5732743 := bstep (se 1 (by rfl) ⟨4299557, by rfl⟩ : syracuseStep 5732743 = 8599115) B8599115
theorem B6699449 : Blo 1764083 6699449 := bstep (se 2 (by rfl) ⟨2512293, by rfl⟩ : syracuseStep 6699449 = 5024587) B5024587
theorem B8477207 : Blo 1764083 8477207 := bstep (se 1 (by rfl) ⟨6357905, by rfl⟩ : syracuseStep 8477207 = 12715811) B12715811
theorem B3971627 : Blo 1764083 3971627 := bstep (se 1 (by rfl) ⟨2978720, by rfl⟩ : syracuseStep 3971627 = 5957441) B5957441
theorem B2513467 : Blo 1764083 2513467 := bstep (se 1 (by rfl) ⟨1885100, by rfl⟩ : syracuseStep 2513467 = 3770201) B3770201
theorem B6036029 : Blo 1764083 6036029 := bstep (se 3 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 6036029 = 2263511) B2263511
theorem B8936243 : Blo 1764083 8936243 := bstep (se 1 (by rfl) ⟨6702182, by rfl⟩ : syracuseStep 8936243 = 13404365) B13404365
theorem B5954363 : Blo 1764083 5954363 := bstep (se 1 (by rfl) ⟨4465772, by rfl⟩ : syracuseStep 5954363 = 8931545) B8931545
theorem B8485721 : Blo 1764083 8485721 := bstep (se 2 (by rfl) ⟨3182145, by rfl⟩ : syracuseStep 8485721 = 6364291) B6364291
theorem B12581747 : Blo 1764083 12581747 := bstep (se 1 (by rfl) ⟨9436310, by rfl⟩ : syracuseStep 12581747 = 18872621) B18872621
theorem B3971987 : Blo 1764083 3971987 := bstep (se 1 (by rfl) ⟨2978990, by rfl⟩ : syracuseStep 3971987 = 5957981) B5957981
theorem B3972041 : Blo 1764083 3972041 := bstep (se 2 (by rfl) ⟨1489515, by rfl⟩ : syracuseStep 3972041 = 2979031) B2979031
theorem B2513911 : Blo 1764083 2513911 := bstep (se 1 (by rfl) ⟨1885433, by rfl⟩ : syracuseStep 2513911 = 3770867) B3770867
theorem B7158871 : Blo 1764083 7158871 := bstep (se 1 (by rfl) ⟨5369153, by rfl⟩ : syracuseStep 7158871 = 10738307) B10738307
theorem B8936567 : Blo 1764083 8936567 := bstep (se 1 (by rfl) ⟨6702425, by rfl⟩ : syracuseStep 8936567 = 13404851) B13404851
theorem B5029121 : Blo 1764083 5029121 := bstep (se 2 (by rfl) ⟨1885920, by rfl⟩ : syracuseStep 5029121 = 3771841) B3771841
theorem B3579151 : Blo 1764083 3579151 := bstep (se 1 (by rfl) ⟨2684363, by rfl⟩ : syracuseStep 3579151 = 5368727) B5368727
theorem B5954849 : Blo 1764083 5954849 := bstep (se 2 (by rfl) ⟨2233068, by rfl⟩ : syracuseStep 5954849 = 4466137) B4466137
theorem B10050905 : Blo 1764083 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B8486279 : Blo 1764083 8486279 := bstep (se 1 (by rfl) ⟨6364709, by rfl⟩ : syracuseStep 8486279 = 12729419) B12729419
theorem B6790547 : Blo 1764083 6790547 := bstep (se 1 (by rfl) ⟨5092910, by rfl⟩ : syracuseStep 6790547 = 10185821) B10185821
theorem B3349907 : Blo 1764083 3349907 := bstep (se 1 (by rfl) ⟨2512430, by rfl⟩ : syracuseStep 3349907 = 5024861) B5024861
theorem B3350135 : Blo 1764083 3350135 := bstep (se 1 (by rfl) ⟨2512601, by rfl⟩ : syracuseStep 3350135 = 5025203) B5025203
theorem B3972743 : Blo 1764083 3972743 := bstep (se 1 (by rfl) ⟨2979557, by rfl⟩ : syracuseStep 3972743 = 5959115) B5959115
theorem B10051361 : Blo 1764083 10051361 := bstep (se 2 (by rfl) ⟨3769260, by rfl⟩ : syracuseStep 10051361 = 7538521) B7538521
theorem B18366259 : Blo 1764083 18366259 := bstep (se 1 (by rfl) ⟨13774694, by rfl⟩ : syracuseStep 18366259 = 27549389) B27549389
theorem B3972923 : Blo 1764083 3972923 := bstep (se 1 (by rfl) ⟨2979692, by rfl⟩ : syracuseStep 3972923 = 5959385) B5959385
theorem B5955443 : Blo 1764083 5955443 := bstep (se 1 (by rfl) ⟨4466582, by rfl⟩ : syracuseStep 5955443 = 8933165) B8933165
theorem B3973049 : Blo 1764083 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B6037523 : Blo 1764083 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B6701075 : Blo 1764083 6701075 := bstep (se 1 (by rfl) ⟨5025806, by rfl⟩ : syracuseStep 6701075 = 10051613) B10051613
theorem B3973139 : Blo 1764083 3973139 := bstep (se 1 (by rfl) ⟨2979854, by rfl⟩ : syracuseStep 3973139 = 5959709) B5959709
theorem B7536797 : Blo 1764083 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B2646215 : Blo 1764083 2646215 := bstep (se 1 (by rfl) ⟨1984661, by rfl⟩ : syracuseStep 2646215 = 3969323) B3969323
theorem B85909733 : Blo 1764083 85909733 := bstep (se 4 (by rfl) ⟨8054037, by rfl⟩ : syracuseStep 85909733 = 16108075) B16108075
theorem B14319845 : Blo 1764083 14319845 := bstep (se 4 (by rfl) ⟨1342485, by rfl⟩ : syracuseStep 14319845 = 2684971) B2684971
theorem B3350879 : Blo 1764083 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B2646377 : Blo 1764083 2646377 := bstep (se 2 (by rfl) ⟨992391, by rfl⟩ : syracuseStep 2646377 = 1984783) B1984783
theorem B5652841 : Blo 1764083 5652841 := bstep (se 2 (by rfl) ⟨2119815, by rfl⟩ : syracuseStep 5652841 = 4239631) B4239631
theorem B3973481 : Blo 1764083 3973481 := bstep (se 2 (by rfl) ⟨1490055, by rfl⟩ : syracuseStep 3973481 = 2980111) B2980111
theorem B5955983 : Blo 1764083 5955983 := bstep (se 1 (by rfl) ⟨4466987, by rfl⟩ : syracuseStep 5955983 = 8933975) B8933975
theorem B2646455 : Blo 1764083 2646455 := bstep (se 1 (by rfl) ⟨1984841, by rfl⟩ : syracuseStep 2646455 = 3969683) B3969683
theorem B2646491 : Blo 1764083 2646491 := bstep (se 1 (by rfl) ⟨1984868, by rfl⟩ : syracuseStep 2646491 = 3969737) B3969737
theorem B4301275 : Blo 1764083 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B3179017 : Blo 1764083 3179017 := bstep (se 2 (by rfl) ⟨1192131, by rfl⟩ : syracuseStep 3179017 = 2384263) B2384263
theorem B7643657 : Blo 1764083 7643657 := bstep (se 2 (by rfl) ⟨2866371, by rfl⟩ : syracuseStep 7643657 = 5732743) B5732743
theorem B5956307 : Blo 1764083 5956307 := bstep (se 1 (by rfl) ⟨4467230, by rfl⟩ : syracuseStep 5956307 = 8934461) B8934461
theorem B3351289 : Blo 1764083 3351289 := bstep (se 2 (by rfl) ⟨1256733, by rfl⟩ : syracuseStep 3351289 = 2513467) B2513467
theorem B5653277 : Blo 1764083 5653277 := bstep (se 3 (by rfl) ⟨1059989, by rfl⟩ : syracuseStep 5653277 = 2119979) B2119979
theorem B7537481 : Blo 1764083 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B2827151 : Blo 1764083 2827151 := bstep (se 1 (by rfl) ⟨2120363, by rfl⟩ : syracuseStep 2827151 = 4240727) B4240727
theorem B2646959 : Blo 1764083 2646959 := bstep (se 1 (by rfl) ⟨1985219, by rfl⟩ : syracuseStep 2646959 = 3970439) B3970439
theorem B2647049 : Blo 1764083 2647049 := bstep (se 2 (by rfl) ⟨992643, by rfl⟩ : syracuseStep 2647049 = 1985287) B1985287
theorem B25437203 : Blo 1764083 25437203 := bstep (se 1 (by rfl) ⟨19077902, by rfl⟩ : syracuseStep 25437203 = 38155805) B38155805
theorem B3769363 : Blo 1764083 3769363 := bstep (se 1 (by rfl) ⟨2827022, by rfl⟩ : syracuseStep 3769363 = 5654045) B5654045
theorem B114500627 : Blo 1764083 114500627 := bstep (se 1 (by rfl) ⟨85875470, by rfl⟩ : syracuseStep 114500627 = 171750941) B171750941
theorem B2647079 : Blo 1764083 2647079 := bstep (se 1 (by rfl) ⟨1985309, by rfl⟩ : syracuseStep 2647079 = 3970619) B3970619
theorem B2827343 : Blo 1764083 2827343 := bstep (se 1 (by rfl) ⟨2120507, by rfl⟩ : syracuseStep 2827343 = 4241015) B4241015
theorem B3351631 : Blo 1764083 3351631 := bstep (se 1 (by rfl) ⟨2513723, by rfl⟩ : syracuseStep 3351631 = 5027447) B5027447
theorem B16106615 : Blo 1764083 16106615 := bstep (se 1 (by rfl) ⟨12079961, by rfl⟩ : syracuseStep 16106615 = 24159923) B24159923
theorem B2647163 : Blo 1764083 2647163 := bstep (se 1 (by rfl) ⟨1985372, by rfl⟩ : syracuseStep 2647163 = 3970745) B3970745
theorem B8479991 : Blo 1764083 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B2647289 : Blo 1764083 2647289 := bstep (se 2 (by rfl) ⟨992733, by rfl⟩ : syracuseStep 2647289 = 1985467) B1985467
theorem B3351881 : Blo 1764083 3351881 := bstep (se 2 (by rfl) ⟨1256955, by rfl⟩ : syracuseStep 3351881 = 2513911) B2513911
theorem B2647391 : Blo 1764083 2647391 := bstep (se 1 (by rfl) ⟨1985543, by rfl⟩ : syracuseStep 2647391 = 3971087) B3971087
theorem B3179881 : Blo 1764083 3179881 := bstep (se 2 (by rfl) ⟨1192455, by rfl⟩ : syracuseStep 3179881 = 2384911) B2384911
theorem B2647403 : Blo 1764083 2647403 := bstep (se 1 (by rfl) ⟨1985552, by rfl⟩ : syracuseStep 2647403 = 3971105) B3971105
theorem B27542899 : Blo 1764083 27542899 := bstep (se 1 (by rfl) ⟨20657174, by rfl⟩ : syracuseStep 27542899 = 41314349) B41314349
theorem B5367305 : Blo 1764083 5367305 := bstep (se 2 (by rfl) ⟨2012739, by rfl⟩ : syracuseStep 5367305 = 4025479) B4025479
theorem B2647631 : Blo 1764083 2647631 := bstep (se 1 (by rfl) ⟨1985723, by rfl⟩ : syracuseStep 2647631 = 3971447) B3971447
theorem B1885775 : Blo 1764083 1885775 := bstep (se 1 (by rfl) ⟨1414331, by rfl⟩ : syracuseStep 1885775 = 2828663) B2828663
theorem B4466299 : Blo 1764083 4466299 := bstep (se 1 (by rfl) ⟨3349724, by rfl⟩ : syracuseStep 4466299 = 6699449) B6699449
theorem B9537223 : Blo 1764083 9537223 := bstep (se 1 (by rfl) ⟨7152917, by rfl⟩ : syracuseStep 9537223 = 14305835) B14305835
theorem B2647751 : Blo 1764083 2647751 := bstep (se 1 (by rfl) ⟨1985813, by rfl⟩ : syracuseStep 2647751 = 3971627) B3971627
theorem B4024019 : Blo 1764083 4024019 := bstep (se 1 (by rfl) ⟨3018014, by rfl⟩ : syracuseStep 4024019 = 6036029) B6036029
theorem B2647913 : Blo 1764083 2647913 := bstep (se 2 (by rfl) ⟨992967, by rfl⟩ : syracuseStep 2647913 = 1985935) B1985935
theorem B21481325 : Blo 1764083 21481325 := bstep (se 3 (by rfl) ⟨4027748, by rfl⟩ : syracuseStep 21481325 = 8055497) B8055497
theorem B5957495 : Blo 1764083 5957495 := bstep (se 1 (by rfl) ⟨4468121, by rfl⟩ : syracuseStep 5957495 = 8936243) B8936243
theorem B15075233 : Blo 1764083 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B2647991 : Blo 1764083 2647991 := bstep (se 1 (by rfl) ⟨1985993, by rfl⟩ : syracuseStep 2647991 = 3971987) B3971987
theorem B12077009 : Blo 1764083 12077009 := bstep (se 2 (by rfl) ⟨4528878, by rfl⟩ : syracuseStep 12077009 = 9057757) B9057757
theorem B2648027 : Blo 1764083 2648027 := bstep (se 1 (by rfl) ⟨1986020, by rfl⟩ : syracuseStep 2648027 = 3972041) B3972041
theorem B5957711 : Blo 1764083 5957711 := bstep (se 1 (by rfl) ⟨4468283, by rfl⟩ : syracuseStep 5957711 = 8936567) B8936567
theorem B3352747 : Blo 1764083 3352747 := bstep (se 1 (by rfl) ⟨2514560, by rfl⟩ : syracuseStep 3352747 = 5029121) B5029121
theorem B1984711 : Blo 1764083 1984711 := bstep (se 1 (by rfl) ⟨1488533, by rfl⟩ : syracuseStep 1984711 = 2977067) B2977067
theorem B17189273 : Blo 1764083 17189273 := bstep (se 2 (by rfl) ⟨6445977, by rfl⟩ : syracuseStep 17189273 = 12891955) B12891955
theorem B24488345 : Blo 1764083 24488345 := bstep (se 2 (by rfl) ⟨9183129, by rfl⟩ : syracuseStep 24488345 = 18366259) B18366259
theorem B2648495 : Blo 1764083 2648495 := bstep (se 1 (by rfl) ⟨1986371, by rfl⟩ : syracuseStep 2648495 = 3972743) B3972743
theorem B1788359 : Blo 1764083 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B5958089 : Blo 1764083 5958089 := bstep (se 2 (by rfl) ⟨2234283, by rfl⟩ : syracuseStep 5958089 = 4468567) B4468567
theorem B2648585 : Blo 1764083 2648585 := bstep (se 2 (by rfl) ⟨993219, by rfl⟩ : syracuseStep 2648585 = 1986439) B1986439
theorem B2648615 : Blo 1764083 2648615 := bstep (se 1 (by rfl) ⟨1986461, by rfl⟩ : syracuseStep 2648615 = 3972923) B3972923
theorem B2648699 : Blo 1764083 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B7539409 : Blo 1764083 7539409 := bstep (se 2 (by rfl) ⟨2827278, by rfl⟩ : syracuseStep 7539409 = 5654557) B5654557
theorem B5958359 : Blo 1764083 5958359 := bstep (se 1 (by rfl) ⟨4468769, by rfl⟩ : syracuseStep 5958359 = 8937539) B8937539
theorem B2648825 : Blo 1764083 2648825 := bstep (se 2 (by rfl) ⟨993309, by rfl⟩ : syracuseStep 2648825 = 1986619) B1986619
theorem B1764135 : Blo 1764083 1764135 := bstep (se 1 (by rfl) ⟨1323101, by rfl⟩ : syracuseStep 1764135 = 2646203) B2646203
theorem B32205637 : Blo 1764083 32205637 := bstep (se 4 (by rfl) ⟨3019278, by rfl⟩ : syracuseStep 32205637 = 6038557) B6038557
theorem B38153035 : Blo 1764083 38153035 := bstep (se 1 (by rfl) ⟨28614776, by rfl⟩ : syracuseStep 38153035 = 57229553) B57229553
theorem B1764175 : Blo 1764083 1764175 := bstep (se 1 (by rfl) ⟨1323131, by rfl⟩ : syracuseStep 1764175 = 2646263) B2646263
theorem B1764191 : Blo 1764083 1764191 := bstep (se 1 (by rfl) ⟨1323143, by rfl⟩ : syracuseStep 1764191 = 2646287) B2646287
theorem B2648927 : Blo 1764083 2648927 := bstep (se 1 (by rfl) ⟨1986695, by rfl⟩ : syracuseStep 2648927 = 3973391) B3973391
theorem B2386793 : Blo 1764083 2386793 := bstep (se 2 (by rfl) ⟨895047, by rfl⟩ : syracuseStep 2386793 = 1790095) B1790095
theorem B2648939 : Blo 1764083 2648939 := bstep (se 1 (by rfl) ⟨1986704, by rfl⟩ : syracuseStep 2648939 = 3973409) B3973409
theorem B1764219 : Blo 1764083 1764219 := bstep (se 1 (by rfl) ⟨1323164, by rfl⟩ : syracuseStep 1764219 = 2646329) B2646329
theorem B6703991 : Blo 1764083 6703991 := bstep (se 1 (by rfl) ⟨5027993, by rfl⟩ : syracuseStep 6703991 = 10055987) B10055987
theorem B1764271 : Blo 1764083 1764271 := bstep (se 1 (by rfl) ⟨1323203, by rfl⟩ : syracuseStep 1764271 = 2646407) B2646407
theorem B5958575 : Blo 1764083 5958575 := bstep (se 1 (by rfl) ⟨4468931, by rfl⟩ : syracuseStep 5958575 = 8937863) B8937863
theorem B17189815 : Blo 1764083 17189815 := bstep (se 1 (by rfl) ⟨12892361, by rfl⟩ : syracuseStep 17189815 = 25784723) B25784723
theorem B1764295 : Blo 1764083 1764295 := bstep (se 1 (by rfl) ⟨1323221, by rfl⟩ : syracuseStep 1764295 = 2646443) B2646443
theorem B1764315 : Blo 1764083 1764315 := bstep (se 1 (by rfl) ⟨1323236, by rfl⟩ : syracuseStep 1764315 = 2646473) B2646473
theorem B48311309 : Blo 1764083 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B54340631 : Blo 1764083 54340631 := bstep (se 1 (by rfl) ⟨40755473, by rfl⟩ : syracuseStep 54340631 = 81510947) B81510947
theorem B1764391 : Blo 1764083 1764391 := bstep (se 1 (by rfl) ⟨1323293, by rfl⟩ : syracuseStep 1764391 = 2646587) B2646587
theorem B1985575 : Blo 1764083 1985575 := bstep (se 1 (by rfl) ⟨1489181, by rfl⟩ : syracuseStep 1985575 = 2978363) B2978363
theorem B1764431 : Blo 1764083 1764431 := bstep (se 1 (by rfl) ⟨1323323, by rfl⟩ : syracuseStep 1764431 = 2646647) B2646647
theorem B1764447 : Blo 1764083 1764447 := bstep (se 1 (by rfl) ⟨1323335, by rfl⟩ : syracuseStep 1764447 = 2646671) B2646671
theorem B1764475 : Blo 1764083 1764475 := bstep (se 1 (by rfl) ⟨1323356, by rfl⟩ : syracuseStep 1764475 = 2646713) B2646713
theorem B13405337 : Blo 1764083 13405337 := bstep (se 2 (by rfl) ⟨5027001, by rfl⟩ : syracuseStep 13405337 = 10054003) B10054003
theorem B1764527 : Blo 1764083 1764527 := bstep (se 1 (by rfl) ⟨1323395, by rfl⟩ : syracuseStep 1764527 = 2646791) B2646791
theorem B1764551 : Blo 1764083 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B1764571 : Blo 1764083 1764571 := bstep (se 1 (by rfl) ⟨1323428, by rfl⟩ : syracuseStep 1764571 = 2646857) B2646857
theorem B15076631 : Blo 1764083 15076631 := bstep (se 1 (by rfl) ⟨11307473, by rfl⟩ : syracuseStep 15076631 = 22614947) B22614947
theorem B1764647 : Blo 1764083 1764647 := bstep (se 1 (by rfl) ⟨1323485, by rfl⟩ : syracuseStep 1764647 = 2646971) B2646971
theorem B1764687 : Blo 1764083 1764687 := bstep (se 1 (by rfl) ⟨1323515, by rfl⟩ : syracuseStep 1764687 = 2647031) B2647031
theorem B1764703 : Blo 1764083 1764703 := bstep (se 1 (by rfl) ⟨1323527, by rfl⟩ : syracuseStep 1764703 = 2647055) B2647055
theorem B1764731 : Blo 1764083 1764731 := bstep (se 1 (by rfl) ⟨1323548, by rfl⟩ : syracuseStep 1764731 = 2647097) B2647097
theorem B45231533 : Blo 1764083 45231533 := bstep (se 3 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 45231533 = 16961825) B16961825
theorem B1764783 : Blo 1764083 1764783 := bstep (se 1 (by rfl) ⟨1323587, by rfl⟩ : syracuseStep 1764783 = 2647175) B2647175
theorem B1764807 : Blo 1764083 1764807 := bstep (se 1 (by rfl) ⟨1323605, by rfl⟩ : syracuseStep 1764807 = 2647211) B2647211
theorem B10464713 : Blo 1764083 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B1764827 : Blo 1764083 1764827 := bstep (se 1 (by rfl) ⟨1323620, by rfl⟩ : syracuseStep 1764827 = 2647241) B2647241
theorem B1764903 : Blo 1764083 1764903 := bstep (se 1 (by rfl) ⟨1323677, by rfl⟩ : syracuseStep 1764903 = 2647355) B2647355
theorem B2977337 : Blo 1764083 2977337 := bstep (se 2 (by rfl) ⟨1116501, by rfl⟩ : syracuseStep 2977337 = 2233003) B2233003
theorem B1764943 : Blo 1764083 1764943 := bstep (se 1 (by rfl) ⟨1323707, by rfl⟩ : syracuseStep 1764943 = 2647415) B2647415
theorem B1764959 : Blo 1764083 1764959 := bstep (se 1 (by rfl) ⟨1323719, by rfl⟩ : syracuseStep 1764959 = 2647439) B2647439
theorem B1764987 : Blo 1764083 1764987 := bstep (se 1 (by rfl) ⟨1323740, by rfl⟩ : syracuseStep 1764987 = 2647481) B2647481
theorem B8933003 : Blo 1764083 8933003 := bstep (se 1 (by rfl) ⟨6699752, by rfl⟩ : syracuseStep 8933003 = 13399505) B13399505
theorem B9547409 : Blo 1764083 9547409 := bstep (se 2 (by rfl) ⟨3580278, by rfl⟩ : syracuseStep 9547409 = 7160557) B7160557
theorem B1765039 : Blo 1764083 1765039 := bstep (se 1 (by rfl) ⟨1323779, by rfl⟩ : syracuseStep 1765039 = 2647559) B2647559
theorem B1765063 : Blo 1764083 1765063 := bstep (se 1 (by rfl) ⟨1323797, by rfl⟩ : syracuseStep 1765063 = 2647595) B2647595
theorem B1765083 : Blo 1764083 1765083 := bstep (se 1 (by rfl) ⟨1323812, by rfl⟩ : syracuseStep 1765083 = 2647625) B2647625
theorem B1765159 : Blo 1764083 1765159 := bstep (se 1 (by rfl) ⟨1323869, by rfl⟩ : syracuseStep 1765159 = 2647739) B2647739
theorem B15085379 : Blo 1764083 15085379 := bstep (se 1 (by rfl) ⟨11314034, by rfl⟩ : syracuseStep 15085379 = 22628069) B22628069
theorem B6704963 : Blo 1764083 6704963 := bstep (se 1 (by rfl) ⟨5028722, by rfl⟩ : syracuseStep 6704963 = 10057445) B10057445
theorem B1765199 : Blo 1764083 1765199 := bstep (se 1 (by rfl) ⟨1323899, by rfl⟩ : syracuseStep 1765199 = 2647799) B2647799
theorem B1765215 : Blo 1764083 1765215 := bstep (se 1 (by rfl) ⟨1323911, by rfl⟩ : syracuseStep 1765215 = 2647823) B2647823
theorem B11308909 : Blo 1764083 11308909 := bstep (se 3 (by rfl) ⟨2120420, by rfl⟩ : syracuseStep 11308909 = 4240841) B4240841
theorem B1765243 : Blo 1764083 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B1765295 : Blo 1764083 1765295 := bstep (se 1 (by rfl) ⟨1323971, by rfl⟩ : syracuseStep 1765295 = 2647943) B2647943
theorem B1765319 : Blo 1764083 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B1765339 : Blo 1764083 1765339 := bstep (se 1 (by rfl) ⟨1324004, by rfl⟩ : syracuseStep 1765339 = 2648009) B2648009
theorem B1765415 : Blo 1764083 1765415 := bstep (se 1 (by rfl) ⟨1324061, by rfl⟩ : syracuseStep 1765415 = 2648123) B2648123
theorem B1765455 : Blo 1764083 1765455 := bstep (se 1 (by rfl) ⟨1324091, by rfl⟩ : syracuseStep 1765455 = 2648183) B2648183
theorem B1765471 : Blo 1764083 1765471 := bstep (se 1 (by rfl) ⟨1324103, by rfl⟩ : syracuseStep 1765471 = 2648207) B2648207
theorem B40775795 : Blo 1764083 40775795 := bstep (se 1 (by rfl) ⟨30581846, by rfl⟩ : syracuseStep 40775795 = 61163693) B61163693
theorem B1765499 : Blo 1764083 1765499 := bstep (se 1 (by rfl) ⟨1324124, by rfl⟩ : syracuseStep 1765499 = 2648249) B2648249
theorem B1765551 : Blo 1764083 1765551 := bstep (se 1 (by rfl) ⟨1324163, by rfl⟩ : syracuseStep 1765551 = 2648327) B2648327
theorem B1765575 : Blo 1764083 1765575 := bstep (se 1 (by rfl) ⟨1324181, by rfl⟩ : syracuseStep 1765575 = 2648363) B2648363
theorem B2150599 : Blo 1764083 2150599 := bstep (se 1 (by rfl) ⟨1612949, by rfl⟩ : syracuseStep 2150599 = 3225899) B3225899
theorem B1765595 : Blo 1764083 1765595 := bstep (se 1 (by rfl) ⟨1324196, by rfl⟩ : syracuseStep 1765595 = 2648393) B2648393
theorem B2978039 : Blo 1764083 2978039 := bstep (se 1 (by rfl) ⟨2233529, by rfl⟩ : syracuseStep 2978039 = 4467059) B4467059
theorem B1765671 : Blo 1764083 1765671 := bstep (se 1 (by rfl) ⟨1324253, by rfl⟩ : syracuseStep 1765671 = 2648507) B2648507
theorem B1765711 : Blo 1764083 1765711 := bstep (se 1 (by rfl) ⟨1324283, by rfl⟩ : syracuseStep 1765711 = 2648567) B2648567
theorem B1765727 : Blo 1764083 1765727 := bstep (se 1 (by rfl) ⟨1324295, by rfl⟩ : syracuseStep 1765727 = 2648591) B2648591
theorem B4772201 : Blo 1764083 4772201 := bstep (se 2 (by rfl) ⟨1789575, by rfl⟩ : syracuseStep 4772201 = 3579151) B3579151
theorem B1765755 : Blo 1764083 1765755 := bstep (se 1 (by rfl) ⟨1324316, by rfl⟩ : syracuseStep 1765755 = 2648633) B2648633
theorem B1765807 : Blo 1764083 1765807 := bstep (se 1 (by rfl) ⟨1324355, by rfl⟩ : syracuseStep 1765807 = 2648711) B2648711
theorem B1765831 : Blo 1764083 1765831 := bstep (se 1 (by rfl) ⟨1324373, by rfl⟩ : syracuseStep 1765831 = 2648747) B2648747
theorem B22606289 : Blo 1764083 22606289 := bstep (se 2 (by rfl) ⟨8477358, by rfl⟩ : syracuseStep 22606289 = 16954717) B16954717
theorem B1765851 : Blo 1764083 1765851 := bstep (se 1 (by rfl) ⟨1324388, by rfl⟩ : syracuseStep 1765851 = 2648777) B2648777
theorem B3576329 : Blo 1764083 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B3969575 : Blo 1764083 3969575 := bstep (se 1 (by rfl) ⟨2977181, by rfl⟩ : syracuseStep 3969575 = 5954363) B5954363
theorem B1765927 : Blo 1764083 1765927 := bstep (se 1 (by rfl) ⟨1324445, by rfl⟩ : syracuseStep 1765927 = 2648891) B2648891
theorem B5657147 : Blo 1764083 5657147 := bstep (se 1 (by rfl) ⟨4242860, by rfl⟩ : syracuseStep 5657147 = 8485721) B8485721
theorem B2978383 : Blo 1764083 2978383 := bstep (se 1 (by rfl) ⟨2233787, by rfl⟩ : syracuseStep 2978383 = 4467575) B4467575
theorem B1765967 : Blo 1764083 1765967 := bstep (se 1 (by rfl) ⟨1324475, by rfl⟩ : syracuseStep 1765967 = 2648951) B2648951
theorem B1765983 : Blo 1764083 1765983 := bstep (se 1 (by rfl) ⟨1324487, by rfl⟩ : syracuseStep 1765983 = 2648975) B2648975
theorem B1766011 : Blo 1764083 1766011 := bstep (se 1 (by rfl) ⟨1324508, by rfl⟩ : syracuseStep 1766011 = 2649017) B2649017
theorem B1766063 : Blo 1764083 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B2978633 : Blo 1764083 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B3969899 : Blo 1764083 3969899 := bstep (se 1 (by rfl) ⟨2977424, by rfl⟩ : syracuseStep 3969899 = 5954849) B5954849
theorem B3969953 : Blo 1764083 3969953 := bstep (se 2 (by rfl) ⟨1488732, by rfl⟩ : syracuseStep 3969953 = 2977465) B2977465
theorem B5657519 : Blo 1764083 5657519 := bstep (se 1 (by rfl) ⟨4243139, by rfl⟩ : syracuseStep 5657519 = 8486279) B8486279
theorem B4527031 : Blo 1764083 4527031 := bstep (se 1 (by rfl) ⟨3395273, by rfl⟩ : syracuseStep 4527031 = 6790547) B6790547
theorem B2233271 : Blo 1764083 2233271 := bstep (se 1 (by rfl) ⟨1674953, by rfl⟩ : syracuseStep 2233271 = 3349907) B3349907
theorem B24146909 : Blo 1764083 24146909 := bstep (se 3 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 24146909 = 9055091) B9055091
theorem B13407281 : Blo 1764083 13407281 := bstep (se 2 (by rfl) ⟨5027730, by rfl⟩ : syracuseStep 13407281 = 10055461) B10055461
theorem B2233423 : Blo 1764083 2233423 := bstep (se 1 (by rfl) ⟨1675067, by rfl⟩ : syracuseStep 2233423 = 3350135) B3350135
theorem B3970295 : Blo 1764083 3970295 := bstep (se 1 (by rfl) ⟨2977721, by rfl⟩ : syracuseStep 3970295 = 5955443) B5955443
theorem B2979065 : Blo 1764083 2979065 := bstep (se 2 (by rfl) ⟨1117149, by rfl⟩ : syracuseStep 2979065 = 2234299) B2234299
theorem B2684267 : Blo 1764083 2684267 := bstep (se 1 (by rfl) ⟨2013200, by rfl⟩ : syracuseStep 2684267 = 4026401) B4026401
theorem B2979247 : Blo 1764083 2979247 := bstep (se 1 (by rfl) ⟨2234435, by rfl⟩ : syracuseStep 2979247 = 4468871) B4468871
theorem B19092955 : Blo 1764083 19092955 := bstep (se 1 (by rfl) ⟨14319716, by rfl⟩ : syracuseStep 19092955 = 28639433) B28639433
theorem B6698477 : Blo 1764083 6698477 := bstep (se 3 (by rfl) ⟨1255964, by rfl⟩ : syracuseStep 6698477 = 2511929) B2511929
theorem B2979335 : Blo 1764083 2979335 := bstep (se 1 (by rfl) ⟨2234501, by rfl⟩ : syracuseStep 2979335 = 4469003) B4469003
theorem B6362633 : Blo 1764083 6362633 := bstep (se 2 (by rfl) ⟨2385987, by rfl⟩ : syracuseStep 6362633 = 4771975) B4771975
theorem B7157459 : Blo 1764083 7157459 := bstep (se 1 (by rfl) ⟨5368094, by rfl⟩ : syracuseStep 7157459 = 10736189) B10736189
theorem B9058007 : Blo 1764083 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B38180645 : Blo 1764083 38180645 := bstep (se 4 (by rfl) ⟨3579435, by rfl⟩ : syracuseStep 38180645 = 7158871) B7158871
theorem B3970889 : Blo 1764083 3970889 := bstep (se 2 (by rfl) ⟨1489083, by rfl⟩ : syracuseStep 3970889 = 2978167) B2978167
theorem B2979679 : Blo 1764083 2979679 := bstep (se 1 (by rfl) ⟨2234759, by rfl⟩ : syracuseStep 2979679 = 4469519) B4469519
theorem B2979767 : Blo 1764083 2979767 := bstep (se 1 (by rfl) ⟨2234825, by rfl⟩ : syracuseStep 2979767 = 4469651) B4469651
theorem B6363137 : Blo 1764083 6363137 := bstep (se 2 (by rfl) ⟨2386176, by rfl⟩ : syracuseStep 6363137 = 4772353) B4772353
theorem B16767065 : Blo 1764083 16767065 := bstep (se 2 (by rfl) ⟨6287649, by rfl⟩ : syracuseStep 16767065 = 12575299) B12575299
theorem B2234567 : Blo 1764083 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B2234719 : Blo 1764083 2234719 := bstep (se 1 (by rfl) ⟨1676039, by rfl⟩ : syracuseStep 2234719 = 3352079) B3352079
theorem B7543169 : Blo 1764083 7543169 := bstep (se 2 (by rfl) ⟨2828688, by rfl⟩ : syracuseStep 7543169 = 5657377) B5657377
theorem B30579079 : Blo 1764083 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B6363629 : Blo 1764083 6363629 := bstep (se 3 (by rfl) ⟨1193180, by rfl⟩ : syracuseStep 6363629 = 2386361) B2386361
theorem B6699617 : Blo 1764083 6699617 := bstep (se 2 (by rfl) ⟨2512356, by rfl⟩ : syracuseStep 6699617 = 5024713) B5024713
theorem B3971681 : Blo 1764083 3971681 := bstep (se 2 (by rfl) ⟨1489380, by rfl⟩ : syracuseStep 3971681 = 2978761) B2978761
theorem B3349163 : Blo 1764083 3349163 := bstep (se 1 (by rfl) ⟨2511872, by rfl⟩ : syracuseStep 3349163 = 5023745) B5023745
theorem B5028551 : Blo 1764083 5028551 := bstep (se 1 (by rfl) ⟨3771413, by rfl⟩ : syracuseStep 5028551 = 7542827) B7542827
theorem B27532021 : Blo 1764083 27532021 := bstep (se 5 (by rfl) ⟨1290563, by rfl⟩ : syracuseStep 27532021 = 2581127) B2581127
theorem B4528991 : Blo 1764083 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B3972023 : Blo 1764083 3972023 := bstep (se 1 (by rfl) ⟨2979017, by rfl⟩ : syracuseStep 3972023 = 5958035) B5958035
theorem B4529159 : Blo 1764083 4529159 := bstep (se 1 (by rfl) ⟨3396869, by rfl⟩ : syracuseStep 4529159 = 6793739) B6793739
theorem B5651471 : Blo 1764083 5651471 := bstep (se 1 (by rfl) ⟨4238603, by rfl⟩ : syracuseStep 5651471 = 8477207) B8477207
theorem B5954579 : Blo 1764083 5954579 := bstep (se 1 (by rfl) ⟨4465934, by rfl⟩ : syracuseStep 5954579 = 8931869) B8931869
theorem B4529209 : Blo 1764083 4529209 := bstep (se 2 (by rfl) ⟨1698453, by rfl⟩ : syracuseStep 4529209 = 3396907) B3396907
theorem B15277135 : Blo 1764083 15277135 := bstep (se 1 (by rfl) ⟨11457851, by rfl⟩ : syracuseStep 15277135 = 22915703) B22915703
theorem B8387831 : Blo 1764083 8387831 := bstep (se 1 (by rfl) ⟨6290873, by rfl⟩ : syracuseStep 8387831 = 12581747) B12581747
theorem B5954903 : Blo 1764083 5954903 := bstep (se 1 (by rfl) ⟨4466177, by rfl⟩ : syracuseStep 5954903 = 8932355) B8932355
theorem B6446479 : Blo 1764083 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B3972617 : Blo 1764083 3972617 := bstep (se 2 (by rfl) ⟨1489731, by rfl⟩ : syracuseStep 3972617 = 2979463) B2979463
theorem B6700603 : Blo 1764083 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B54320705 : Blo 1764083 54320705 := bstep (se 2 (by rfl) ⟨20370264, by rfl⟩ : syracuseStep 54320705 = 40740529) B40740529
theorem B3972959 : Blo 1764083 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B6700907 : Blo 1764083 6700907 := bstep (se 1 (by rfl) ⟨5025680, by rfl⟩ : syracuseStep 6700907 = 10051361) B10051361
theorem B8937377 : Blo 1764083 8937377 := bstep (se 2 (by rfl) ⟨3351516, by rfl⟩ : syracuseStep 8937377 = 6703033) B6703033
theorem B44712173 : Blo 1764083 44712173 := bstep (se 3 (by rfl) ⟨8383532, by rfl⟩ : syracuseStep 44712173 = 16767065) B16767065
theorem B2646281 : Blo 1764083 2646281 := bstep (se 2 (by rfl) ⟨992355, by rfl⟩ : syracuseStep 2646281 = 1984711) B1984711
theorem B2867465 : Blo 1764083 2867465 := bstep (se 2 (by rfl) ⟨1075299, by rfl⟩ : syracuseStep 2867465 = 2150599) B2150599
theorem B2384219 : Blo 1764083 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B2646383 : Blo 1764083 2646383 := bstep (se 1 (by rfl) ⟨1984787, by rfl⟩ : syracuseStep 2646383 = 3969575) B3969575
theorem B7537121 : Blo 1764083 7537121 := bstep (se 2 (by rfl) ⟨2826420, by rfl⟩ : syracuseStep 7537121 = 5652841) B5652841
theorem B40772105 : Blo 1764083 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B3768851 : Blo 1764083 3768851 := bstep (se 1 (by rfl) ⟨2826638, by rfl⟩ : syracuseStep 3768851 = 5653277) B5653277
theorem B2646599 : Blo 1764083 2646599 := bstep (se 1 (by rfl) ⟨1984949, by rfl⟩ : syracuseStep 2646599 = 3969899) B3969899
theorem B1884767 : Blo 1764083 1884767 := bstep (se 1 (by rfl) ⟨1413575, by rfl⟩ : syracuseStep 1884767 = 2827151) B2827151
theorem B2646635 : Blo 1764083 2646635 := bstep (se 1 (by rfl) ⟨1984976, by rfl⟩ : syracuseStep 2646635 = 3969953) B3969953
theorem B5735033 : Blo 1764083 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B16097939 : Blo 1764083 16097939 := bstep (se 1 (by rfl) ⟨12073454, by rfl⟩ : syracuseStep 16097939 = 24146909) B24146909
theorem B16958135 : Blo 1764083 16958135 := bstep (se 1 (by rfl) ⟨12718601, by rfl⟩ : syracuseStep 16958135 = 25437203) B25437203
theorem B76333751 : Blo 1764083 76333751 := bstep (se 1 (by rfl) ⟨57250313, by rfl⟩ : syracuseStep 76333751 = 114500627) B114500627
theorem B8938187 : Blo 1764083 8938187 := bstep (se 1 (by rfl) ⟨6703640, by rfl⟩ : syracuseStep 8938187 = 13407281) B13407281
theorem B2646863 : Blo 1764083 2646863 := bstep (se 1 (by rfl) ⟨1985147, by rfl⟩ : syracuseStep 2646863 = 3970295) B3970295
theorem B5653327 : Blo 1764083 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B8938349 : Blo 1764083 8938349 := bstep (se 3 (by rfl) ⟨1675940, by rfl⟩ : syracuseStep 8938349 = 3351881) B3351881
theorem B10052545 : Blo 1764083 10052545 := bstep (se 2 (by rfl) ⟨3769704, by rfl⟩ : syracuseStep 10052545 = 7539409) B7539409
theorem B36709361 : Blo 1764083 36709361 := bstep (se 2 (by rfl) ⟨13766010, by rfl⟩ : syracuseStep 36709361 = 27532021) B27532021
theorem B4465651 : Blo 1764083 4465651 := bstep (se 1 (by rfl) ⟨3349238, by rfl⟩ : syracuseStep 4465651 = 6698477) B6698477
theorem B4768957 : Blo 1764083 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B25453763 : Blo 1764083 25453763 := bstep (se 1 (by rfl) ⟨19090322, by rfl⟩ : syracuseStep 25453763 = 38180645) B38180645
theorem B2647259 : Blo 1764083 2647259 := bstep (se 1 (by rfl) ⟨1985444, by rfl⟩ : syracuseStep 2647259 = 3970889) B3970889
theorem B14320883 : Blo 1764083 14320883 := bstep (se 1 (by rfl) ⟨10740662, by rfl⟩ : syracuseStep 14320883 = 21481325) B21481325
theorem B20383085 : Blo 1764083 20383085 := bstep (se 3 (by rfl) ⟨3821828, by rfl⟩ : syracuseStep 20383085 = 7643657) B7643657
theorem B2647433 : Blo 1764083 2647433 := bstep (se 2 (by rfl) ⟨992787, by rfl⟩ : syracuseStep 2647433 = 1985575) B1985575
theorem B6038945 : Blo 1764083 6038945 := bstep (se 2 (by rfl) ⟨2264604, by rfl⟩ : syracuseStep 6038945 = 4529209) B4529209
theorem B4466411 : Blo 1764083 4466411 := bstep (se 1 (by rfl) ⟨3349808, by rfl⟩ : syracuseStep 4466411 = 6699617) B6699617
theorem B2647787 : Blo 1764083 2647787 := bstep (se 1 (by rfl) ⟨1985840, by rfl⟩ : syracuseStep 2647787 = 3971681) B3971681
theorem B3352367 : Blo 1764083 3352367 := bstep (se 1 (by rfl) ⟨2514275, by rfl⟩ : syracuseStep 3352367 = 5028551) B5028551
theorem B8595305 : Blo 1764083 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B16959365 : Blo 1764083 16959365 := bstep (se 4 (by rfl) ⟨1589940, by rfl⟩ : syracuseStep 16959365 = 3179881) B3179881
theorem B2648015 : Blo 1764083 2648015 := bstep (se 1 (by rfl) ⟨1986011, by rfl⟩ : syracuseStep 2648015 = 3972023) B3972023
theorem B36227087 : Blo 1764083 36227087 := bstep (se 1 (by rfl) ⟨27170315, by rfl⟩ : syracuseStep 36227087 = 54340631) B54340631
theorem B12077309 : Blo 1764083 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B12716297 : Blo 1764083 12716297 := bstep (se 2 (by rfl) ⟨4768611, by rfl⟩ : syracuseStep 12716297 = 9537223) B9537223
theorem B2648411 : Blo 1764083 2648411 := bstep (se 1 (by rfl) ⟨1986308, by rfl⟩ : syracuseStep 2648411 = 3972617) B3972617
theorem B1984891 : Blo 1764083 1984891 := bstep (se 1 (by rfl) ⟨1488668, by rfl⟩ : syracuseStep 1984891 = 2977337) B2977337
theorem B2648639 : Blo 1764083 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B4467271 : Blo 1764083 4467271 := bstep (se 1 (by rfl) ⟨3350453, by rfl⟩ : syracuseStep 4467271 = 6700907) B6700907
theorem B5958251 : Blo 1764083 5958251 := bstep (se 1 (by rfl) ⟨4468688, by rfl⟩ : syracuseStep 5958251 = 8937377) B8937377
theorem B16968365 : Blo 1764083 16968365 := bstep (se 3 (by rfl) ⟨3181568, by rfl⟩ : syracuseStep 16968365 = 6363137) B6363137
theorem B4025015 : Blo 1764083 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B4467383 : Blo 1764083 4467383 := bstep (se 1 (by rfl) ⟨3350537, by rfl⟩ : syracuseStep 4467383 = 6701075) B6701075
theorem B2648759 : Blo 1764083 2648759 := bstep (se 1 (by rfl) ⟨1986569, by rfl⟩ : syracuseStep 2648759 = 3973139) B3973139
theorem B27183863 : Blo 1764083 27183863 := bstep (se 1 (by rfl) ⟨20387897, by rfl⟩ : syracuseStep 27183863 = 40775795) B40775795
theorem B5024531 : Blo 1764083 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B1764143 : Blo 1764083 1764143 := bstep (se 1 (by rfl) ⟨1323107, by rfl⟩ : syracuseStep 1764143 = 2646215) B2646215
theorem B57273155 : Blo 1764083 57273155 := bstep (se 1 (by rfl) ⟨42954866, by rfl⟩ : syracuseStep 57273155 = 85909733) B85909733
theorem B9546563 : Blo 1764083 9546563 := bstep (se 1 (by rfl) ⟨7159922, by rfl⟩ : syracuseStep 9546563 = 14319845) B14319845
theorem B1985359 : Blo 1764083 1985359 := bstep (se 1 (by rfl) ⟨1489019, by rfl⟩ : syracuseStep 1985359 = 2978039) B2978039
theorem B7539581 : Blo 1764083 7539581 := bstep (se 3 (by rfl) ⟨1413671, by rfl⟩ : syracuseStep 7539581 = 2827343) B2827343
theorem B1764251 : Blo 1764083 1764251 := bstep (se 1 (by rfl) ⟨1323188, by rfl⟩ : syracuseStep 1764251 = 2646377) B2646377
theorem B2648987 : Blo 1764083 2648987 := bstep (se 1 (by rfl) ⟨1986740, by rfl⟩ : syracuseStep 2648987 = 3973481) B3973481
theorem B1764303 : Blo 1764083 1764303 := bstep (se 1 (by rfl) ⟨1323227, by rfl⟩ : syracuseStep 1764303 = 2646455) B2646455
theorem B1764327 : Blo 1764083 1764327 := bstep (se 1 (by rfl) ⟨1323245, by rfl⟩ : syracuseStep 1764327 = 2646491) B2646491
theorem B3771431 : Blo 1764083 3771431 := bstep (se 1 (by rfl) ⟨2828573, by rfl⟩ : syracuseStep 3771431 = 5657147) B5657147
theorem B5958845 : Blo 1764083 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B5024987 : Blo 1764083 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B1985755 : Blo 1764083 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B1764639 : Blo 1764083 1764639 := bstep (se 1 (by rfl) ⟨1323479, by rfl⟩ : syracuseStep 1764639 = 2646959) B2646959
theorem B3771679 : Blo 1764083 3771679 := bstep (se 1 (by rfl) ⟨2828759, by rfl⟩ : syracuseStep 3771679 = 5657519) B5657519
theorem B22367549 : Blo 1764083 22367549 := bstep (se 3 (by rfl) ⟨4193915, by rfl⟩ : syracuseStep 22367549 = 8387831) B8387831
theorem B1764699 : Blo 1764083 1764699 := bstep (se 1 (by rfl) ⟨1323524, by rfl⟩ : syracuseStep 1764699 = 2647049) B2647049
theorem B4238689 : Blo 1764083 4238689 := bstep (se 2 (by rfl) ⟨1589508, by rfl⟩ : syracuseStep 4238689 = 3179017) B3179017
theorem B1764719 : Blo 1764083 1764719 := bstep (se 1 (by rfl) ⟨1323539, by rfl⟩ : syracuseStep 1764719 = 2647079) B2647079
theorem B1764775 : Blo 1764083 1764775 := bstep (se 1 (by rfl) ⟨1323581, by rfl⟩ : syracuseStep 1764775 = 2647163) B2647163
theorem B1764859 : Blo 1764083 1764859 := bstep (se 1 (by rfl) ⟨1323644, by rfl⟩ : syracuseStep 1764859 = 2647289) B2647289
theorem B1986043 : Blo 1764083 1986043 := bstep (se 1 (by rfl) ⟨1489532, by rfl⟩ : syracuseStep 1986043 = 2979065) B2979065
theorem B1764927 : Blo 1764083 1764927 := bstep (se 1 (by rfl) ⟨1323695, by rfl⟩ : syracuseStep 1764927 = 2647391) B2647391
theorem B1764935 : Blo 1764083 1764935 := bstep (se 1 (by rfl) ⟨1323701, by rfl⟩ : syracuseStep 1764935 = 2647403) B2647403
theorem B1789511 : Blo 1764083 1789511 := bstep (se 1 (by rfl) ⟨1342133, by rfl⟩ : syracuseStep 1789511 = 2684267) B2684267
theorem B12725869 : Blo 1764083 12725869 := bstep (se 3 (by rfl) ⟨2386100, by rfl⟩ : syracuseStep 12725869 = 4772201) B4772201
theorem B4468385 : Blo 1764083 4468385 := bstep (se 2 (by rfl) ⟨1675644, by rfl⟩ : syracuseStep 4468385 = 3351289) B3351289
theorem B1986223 : Blo 1764083 1986223 := bstep (se 1 (by rfl) ⟨1489667, by rfl⟩ : syracuseStep 1986223 = 2979335) B2979335
theorem B1765087 : Blo 1764083 1765087 := bstep (se 1 (by rfl) ⟨1323815, by rfl⟩ : syracuseStep 1765087 = 2647631) B2647631
theorem B45838061 : Blo 1764083 45838061 := bstep (se 3 (by rfl) ⟨8594636, by rfl⟩ : syracuseStep 45838061 = 17189273) B17189273
theorem B1765167 : Blo 1764083 1765167 := bstep (se 1 (by rfl) ⟨1323875, by rfl⟩ : syracuseStep 1765167 = 2647751) B2647751
theorem B4771639 : Blo 1764083 4771639 := bstep (se 1 (by rfl) ⟨3578729, by rfl⟩ : syracuseStep 4771639 = 7157459) B7157459
theorem B1765275 : Blo 1764083 1765275 := bstep (se 1 (by rfl) ⟨1323956, by rfl⟩ : syracuseStep 1765275 = 2647913) B2647913
theorem B1765327 : Blo 1764083 1765327 := bstep (se 1 (by rfl) ⟨1323995, by rfl⟩ : syracuseStep 1765327 = 2647991) B2647991
theorem B1986511 : Blo 1764083 1986511 := bstep (se 1 (by rfl) ⟨1489883, by rfl⟩ : syracuseStep 1986511 = 2979767) B2979767
theorem B1765351 : Blo 1764083 1765351 := bstep (se 1 (by rfl) ⟨1324013, by rfl⟩ : syracuseStep 1765351 = 2648027) B2648027
theorem B5025817 : Blo 1764083 5025817 := bstep (se 2 (by rfl) ⟨1884681, by rfl⟩ : syracuseStep 5025817 = 3769363) B3769363
theorem B20369513 : Blo 1764083 20369513 := bstep (se 2 (by rfl) ⟨7638567, by rfl⟩ : syracuseStep 20369513 = 15277135) B15277135
theorem B2977897 : Blo 1764083 2977897 := bstep (se 2 (by rfl) ⟨1116711, by rfl⟩ : syracuseStep 2977897 = 2233423) B2233423
theorem B4468841 : Blo 1764083 4468841 := bstep (se 2 (by rfl) ⟨1675815, by rfl⟩ : syracuseStep 4468841 = 3351631) B3351631
theorem B1765663 : Blo 1764083 1765663 := bstep (se 1 (by rfl) ⟨1324247, by rfl⟩ : syracuseStep 1765663 = 2648495) B2648495
theorem B1765723 : Blo 1764083 1765723 := bstep (se 1 (by rfl) ⟨1324292, by rfl⟩ : syracuseStep 1765723 = 2648585) B2648585
theorem B1765743 : Blo 1764083 1765743 := bstep (se 1 (by rfl) ⟨1324307, by rfl⟩ : syracuseStep 1765743 = 2648615) B2648615
theorem B1765799 : Blo 1764083 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B2232775 : Blo 1764083 2232775 := bstep (se 1 (by rfl) ⟨1674581, by rfl⟩ : syracuseStep 2232775 = 3349163) B3349163
theorem B1765883 : Blo 1764083 1765883 := bstep (se 1 (by rfl) ⟨1324412, by rfl⟩ : syracuseStep 1765883 = 2648825) B2648825
theorem B24154685 : Blo 1764083 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1765951 : Blo 1764083 1765951 := bstep (se 1 (by rfl) ⟨1324463, by rfl⟩ : syracuseStep 1765951 = 2648927) B2648927
theorem B1765959 : Blo 1764083 1765959 := bstep (se 1 (by rfl) ⟨1324469, by rfl⟩ : syracuseStep 1765959 = 2648939) B2648939
theorem B4469327 : Blo 1764083 4469327 := bstep (se 1 (by rfl) ⟨3351995, by rfl⟩ : syracuseStep 4469327 = 6703991) B6703991
theorem B25457273 : Blo 1764083 25457273 := bstep (se 2 (by rfl) ⟨9546477, by rfl⟩ : syracuseStep 25457273 = 19092955) B19092955
theorem B3019439 : Blo 1764083 3019439 := bstep (se 1 (by rfl) ⟨2264579, by rfl⟩ : syracuseStep 3019439 = 4529159) B4529159
theorem B32207539 : Blo 1764083 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B3969719 : Blo 1764083 3969719 := bstep (se 1 (by rfl) ⟨2977289, by rfl⟩ : syracuseStep 3969719 = 5954579) B5954579
theorem B8934137 : Blo 1764083 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B3969935 : Blo 1764083 3969935 := bstep (se 1 (by rfl) ⟨2977451, by rfl⟩ : syracuseStep 3969935 = 5954903) B5954903
theorem B6976475 : Blo 1764083 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B36213803 : Blo 1764083 36213803 := bstep (se 1 (by rfl) ⟨27160352, by rfl⟩ : syracuseStep 36213803 = 54320705) B54320705
theorem B15078545 : Blo 1764083 15078545 := bstep (se 2 (by rfl) ⟨5654454, by rfl⟩ : syracuseStep 15078545 = 11308909) B11308909
theorem B10056919 : Blo 1764083 10056919 := bstep (se 1 (by rfl) ⟨7542689, by rfl⟩ : syracuseStep 10056919 = 15085379) B15085379
theorem B4469975 : Blo 1764083 4469975 := bstep (se 1 (by rfl) ⟨3352481, by rfl⟩ : syracuseStep 4469975 = 6704963) B6704963
theorem B4470329 : Blo 1764083 4470329 := bstep (se 2 (by rfl) ⟨1676373, by rfl⟩ : syracuseStep 4470329 = 3352747) B3352747
theorem B2233919 : Blo 1764083 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B3970655 : Blo 1764083 3970655 := bstep (se 1 (by rfl) ⟨2977991, by rfl⟩ : syracuseStep 3970655 = 5955983) B5955983
theorem B15070859 : Blo 1764083 15070859 := bstep (se 1 (by rfl) ⟨11303144, by rfl⟩ : syracuseStep 15070859 = 22606289) B22606289
theorem B2979625 : Blo 1764083 2979625 := bstep (se 2 (by rfl) ⟨1117359, by rfl⟩ : syracuseStep 2979625 = 2234719) B2234719
theorem B3970871 : Blo 1764083 3970871 := bstep (se 1 (by rfl) ⟨2978153, by rfl⟩ : syracuseStep 3970871 = 5956307) B5956307
theorem B10737743 : Blo 1764083 10737743 := bstep (se 1 (by rfl) ⟨8053307, by rfl⟩ : syracuseStep 10737743 = 16106615) B16106615
theorem B3971177 : Blo 1764083 3971177 := bstep (se 2 (by rfl) ⟨1489191, by rfl⟩ : syracuseStep 3971177 = 2978383) B2978383
theorem B3578203 : Blo 1764083 3578203 := bstep (se 1 (by rfl) ⟨2683652, by rfl⟩ : syracuseStep 3578203 = 5367305) B5367305
theorem B4241755 : Blo 1764083 4241755 := bstep (se 1 (by rfl) ⟨3181316, by rfl⟩ : syracuseStep 4241755 = 6362633) B6362633
theorem B42940849 : Blo 1764083 42940849 := bstep (se 2 (by rfl) ⟨16102818, by rfl⟩ : syracuseStep 42940849 = 32205637) B32205637
theorem B50870713 : Blo 1764083 50870713 := bstep (se 2 (by rfl) ⟨19076517, by rfl⟩ : syracuseStep 50870713 = 38153035) B38153035
theorem B6036041 : Blo 1764083 6036041 := bstep (se 2 (by rfl) ⟨2263515, by rfl⟩ : syracuseStep 6036041 = 4527031) B4527031
theorem B22919753 : Blo 1764083 22919753 := bstep (se 2 (by rfl) ⟨8594907, by rfl⟩ : syracuseStep 22919753 = 17189815) B17189815
theorem B3971663 : Blo 1764083 3971663 := bstep (se 1 (by rfl) ⟨2978747, by rfl⟩ : syracuseStep 3971663 = 5957495) B5957495
theorem B10050155 : Blo 1764083 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B8051339 : Blo 1764083 8051339 := bstep (se 1 (by rfl) ⟨6038504, by rfl⟩ : syracuseStep 8051339 = 12077009) B12077009
theorem B3971807 : Blo 1764083 3971807 := bstep (se 1 (by rfl) ⟨2978855, by rfl⟩ : syracuseStep 3971807 = 5957711) B5957711
theorem B5028733 : Blo 1764083 5028733 := bstep (se 3 (by rfl) ⟨942887, by rfl⟩ : syracuseStep 5028733 = 1885775) B1885775
theorem B5028779 : Blo 1764083 5028779 := bstep (se 1 (by rfl) ⟨3771584, by rfl⟩ : syracuseStep 5028779 = 7543169) B7543169
theorem B16325563 : Blo 1764083 16325563 := bstep (se 1 (by rfl) ⟨12244172, by rfl⟩ : syracuseStep 16325563 = 24488345) B24488345
theorem B3972059 : Blo 1764083 3972059 := bstep (se 1 (by rfl) ⟨2979044, by rfl⟩ : syracuseStep 3972059 = 5958089) B5958089
theorem B4242419 : Blo 1764083 4242419 := bstep (se 1 (by rfl) ⟨3181814, by rfl⟩ : syracuseStep 4242419 = 6363629) B6363629
theorem B25459757 : Blo 1764083 25459757 := bstep (se 3 (by rfl) ⟨4773704, by rfl⟩ : syracuseStep 25459757 = 9547409) B9547409
theorem B3972239 : Blo 1764083 3972239 := bstep (se 1 (by rfl) ⟨2979179, by rfl⟩ : syracuseStep 3972239 = 5958359) B5958359
theorem B36723865 : Blo 1764083 36723865 := bstep (se 2 (by rfl) ⟨13771449, by rfl⟩ : syracuseStep 36723865 = 27542899) B27542899
theorem B10730717 : Blo 1764083 10730717 := bstep (se 3 (by rfl) ⟨2012009, by rfl⟩ : syracuseStep 10730717 = 4024019) B4024019
theorem B3972329 : Blo 1764083 3972329 := bstep (se 2 (by rfl) ⟨1489623, by rfl⟩ : syracuseStep 3972329 = 2979247) B2979247
theorem B3972383 : Blo 1764083 3972383 := bstep (se 1 (by rfl) ⟨2979287, by rfl⟩ : syracuseStep 3972383 = 5958575) B5958575
theorem B3767647 : Blo 1764083 3767647 := bstep (se 1 (by rfl) ⟨2825735, by rfl⟩ : syracuseStep 3767647 = 5651471) B5651471
theorem B8936891 : Blo 1764083 8936891 := bstep (se 1 (by rfl) ⟨6702668, by rfl⟩ : syracuseStep 8936891 = 13405337) B13405337
theorem B5955065 : Blo 1764083 5955065 := bstep (se 2 (by rfl) ⟨2233149, by rfl⟩ : syracuseStep 5955065 = 4466299) B4466299
theorem B10051087 : Blo 1764083 10051087 := bstep (se 1 (by rfl) ⟨7538315, by rfl⟩ : syracuseStep 10051087 = 15076631) B15076631
theorem B6364781 : Blo 1764083 6364781 := bstep (se 3 (by rfl) ⟨1193396, by rfl⟩ : syracuseStep 6364781 = 2386793) B2386793
theorem B30154355 : Blo 1764083 30154355 := bstep (se 1 (by rfl) ⟨22615766, by rfl⟩ : syracuseStep 30154355 = 45231533) B45231533
theorem B5955335 : Blo 1764083 5955335 := bstep (se 1 (by rfl) ⟨4466501, by rfl⟩ : syracuseStep 5955335 = 8933003) B8933003
theorem B3972905 : Blo 1764083 3972905 := bstep (se 2 (by rfl) ⟨1489839, by rfl⟩ : syracuseStep 3972905 = 2979679) B2979679
theorem B5955389 : Blo 1764083 5955389 := bstep (se 3 (by rfl) ⟨1116635, by rfl⟩ : syracuseStep 5955389 = 2233271) B2233271
theorem B6701089 : Blo 1764083 6701089 := bstep (se 2 (by rfl) ⟨2512908, by rfl⟩ : syracuseStep 6701089 = 5025817) B5025817
theorem B27181403 : Blo 1764083 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B10731959 : Blo 1764083 10731959 := bstep (se 1 (by rfl) ⟨8048969, by rfl⟩ : syracuseStep 10731959 = 16097939) B16097939
theorem B2646479 : Blo 1764083 2646479 := bstep (se 1 (by rfl) ⟨1984859, by rfl⟩ : syracuseStep 2646479 = 3969719) B3969719
theorem B11305423 : Blo 1764083 11305423 := bstep (se 1 (by rfl) ⟨8479067, by rfl⟩ : syracuseStep 11305423 = 16958135) B16958135
theorem B50889167 : Blo 1764083 50889167 := bstep (se 1 (by rfl) ⟨38166875, by rfl⟩ : syracuseStep 50889167 = 76333751) B76333751
theorem B2646521 : Blo 1764083 2646521 := bstep (se 2 (by rfl) ⟨992445, by rfl⟩ : syracuseStep 2646521 = 1984891) B1984891
theorem B5956091 : Blo 1764083 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B57254465 : Blo 1764083 57254465 := bstep (se 2 (by rfl) ⟨21470424, by rfl⟩ : syracuseStep 57254465 = 42940849) B42940849
theorem B2646623 : Blo 1764083 2646623 := bstep (se 1 (by rfl) ⟨1984967, by rfl⟩ : syracuseStep 2646623 = 3969935) B3969935
theorem B24142535 : Blo 1764083 24142535 := bstep (se 1 (by rfl) ⟨18106901, by rfl⟩ : syracuseStep 24142535 = 36213803) B36213803
theorem B5956361 : Blo 1764083 5956361 := bstep (se 2 (by rfl) ⟨2233635, by rfl⟩ : syracuseStep 5956361 = 4467271) B4467271
theorem B10052363 : Blo 1764083 10052363 := bstep (se 1 (by rfl) ⟨7539272, by rfl⟩ : syracuseStep 10052363 = 15078545) B15078545
theorem B42943385 : Blo 1764083 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B6357917 : Blo 1764083 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B54354893 : Blo 1764083 54354893 := bstep (se 3 (by rfl) ⟨10191542, by rfl⟩ : syracuseStep 54354893 = 20383085) B20383085
theorem B2647103 : Blo 1764083 2647103 := bstep (se 1 (by rfl) ⟨1985327, by rfl⟩ : syracuseStep 2647103 = 3970655) B3970655
theorem B7537769 : Blo 1764083 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B2647145 : Blo 1764083 2647145 := bstep (se 2 (by rfl) ⟨992679, by rfl⟩ : syracuseStep 2647145 = 1985359) B1985359
theorem B2647247 : Blo 1764083 2647247 := bstep (se 1 (by rfl) ⟨1985435, by rfl⟩ : syracuseStep 2647247 = 3970871) B3970871
theorem B21767417 : Blo 1764083 21767417 := bstep (se 2 (by rfl) ⟨8162781, by rfl⟩ : syracuseStep 21767417 = 16325563) B16325563
theorem B13403393 : Blo 1764083 13403393 := bstep (se 2 (by rfl) ⟨5026272, by rfl⟩ : syracuseStep 13403393 = 10052545) B10052545
theorem B11306243 : Blo 1764083 11306243 := bstep (se 1 (by rfl) ⟨8479682, by rfl⟩ : syracuseStep 11306243 = 16959365) B16959365
theorem B24151391 : Blo 1764083 24151391 := bstep (se 1 (by rfl) ⟨18113543, by rfl⟩ : syracuseStep 24151391 = 36227087) B36227087
theorem B2647451 : Blo 1764083 2647451 := bstep (se 1 (by rfl) ⟨1985588, by rfl⟩ : syracuseStep 2647451 = 3971177) B3971177
theorem B5957117 : Blo 1764083 5957117 := bstep (se 3 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 5957117 = 2233919) B2233919
theorem B48965153 : Blo 1764083 48965153 := bstep (se 2 (by rfl) ⟨18361932, by rfl⟩ : syracuseStep 48965153 = 36723865) B36723865
theorem B6358609 : Blo 1764083 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B2647673 : Blo 1764083 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B4024027 : Blo 1764083 4024027 := bstep (se 1 (by rfl) ⟨3018020, by rfl⟩ : syracuseStep 4024027 = 6036041) B6036041
theorem B15279835 : Blo 1764083 15279835 := bstep (se 1 (by rfl) ⟨11459876, by rfl⟩ : syracuseStep 15279835 = 22919753) B22919753
theorem B2647775 : Blo 1764083 2647775 := bstep (se 1 (by rfl) ⟨1985831, by rfl⟩ : syracuseStep 2647775 = 3971663) B3971663
theorem B5367559 : Blo 1764083 5367559 := bstep (se 1 (by rfl) ⟨4025669, by rfl⟩ : syracuseStep 5367559 = 8051339) B8051339
theorem B5023529 : Blo 1764083 5023529 := bstep (se 2 (by rfl) ⟨1883823, by rfl⟩ : syracuseStep 5023529 = 3767647) B3767647
theorem B2647871 : Blo 1764083 2647871 := bstep (se 1 (by rfl) ⟨1985903, by rfl⟩ : syracuseStep 2647871 = 3971807) B3971807
theorem B18122575 : Blo 1764083 18122575 := bstep (se 1 (by rfl) ⟨13591931, by rfl⟩ : syracuseStep 18122575 = 27183863) B27183863
theorem B3352519 : Blo 1764083 3352519 := bstep (se 1 (by rfl) ⟨2514389, by rfl⟩ : syracuseStep 3352519 = 5028779) B5028779
theorem B2648039 : Blo 1764083 2648039 := bstep (se 1 (by rfl) ⟨1986029, by rfl⟩ : syracuseStep 2648039 = 3972059) B3972059
theorem B2828279 : Blo 1764083 2828279 := bstep (se 1 (by rfl) ⟨2121209, by rfl⟩ : syracuseStep 2828279 = 4242419) B4242419
theorem B2648057 : Blo 1764083 2648057 := bstep (se 2 (by rfl) ⟨993021, by rfl⟩ : syracuseStep 2648057 = 1986043) B1986043
theorem B2648159 : Blo 1764083 2648159 := bstep (se 1 (by rfl) ⟨1986119, by rfl⟩ : syracuseStep 2648159 = 3972239) B3972239
theorem B8939645 : Blo 1764083 8939645 := bstep (se 3 (by rfl) ⟨1676183, by rfl⟩ : syracuseStep 8939645 = 3352367) B3352367
theorem B7153811 : Blo 1764083 7153811 := bstep (se 1 (by rfl) ⟨5365358, by rfl⟩ : syracuseStep 7153811 = 10730717) B10730717
theorem B16967825 : Blo 1764083 16967825 := bstep (se 2 (by rfl) ⟨6362934, by rfl⟩ : syracuseStep 16967825 = 12725869) B12725869
theorem B2648219 : Blo 1764083 2648219 := bstep (se 1 (by rfl) ⟨1986164, by rfl⟩ : syracuseStep 2648219 = 3972329) B3972329
theorem B2648255 : Blo 1764083 2648255 := bstep (se 1 (by rfl) ⟨1986191, by rfl⟩ : syracuseStep 2648255 = 3972383) B3972383
theorem B14911699 : Blo 1764083 14911699 := bstep (se 1 (by rfl) ⟨11183774, by rfl⟩ : syracuseStep 14911699 = 22367549) B22367549
theorem B2648297 : Blo 1764083 2648297 := bstep (se 2 (by rfl) ⟨993111, by rfl⟩ : syracuseStep 2648297 = 1986223) B1986223
theorem B5957927 : Blo 1764083 5957927 := bstep (se 1 (by rfl) ⟨4468445, by rfl⟩ : syracuseStep 5957927 = 8936891) B8936891
theorem B30558707 : Blo 1764083 30558707 := bstep (se 1 (by rfl) ⟨22919030, by rfl⟩ : syracuseStep 30558707 = 45838061) B45838061
theorem B2648603 : Blo 1764083 2648603 := bstep (se 1 (by rfl) ⟨1986452, by rfl⟩ : syracuseStep 2648603 = 3972905) B3972905
theorem B2648681 : Blo 1764083 2648681 := bstep (se 2 (by rfl) ⟨993255, by rfl⟩ : syracuseStep 2648681 = 1986511) B1986511
theorem B1764187 : Blo 1764083 1764187 := bstep (se 1 (by rfl) ⟨1323140, by rfl⟩ : syracuseStep 1764187 = 2646281) B2646281
theorem B1911643 : Blo 1764083 1911643 := bstep (se 1 (by rfl) ⟨1433732, by rfl⟩ : syracuseStep 1911643 = 2867465) B2867465
theorem B28633981 : Blo 1764083 28633981 := bstep (se 3 (by rfl) ⟨5368871, by rfl⟩ : syracuseStep 28633981 = 10737743) B10737743
theorem B1764255 : Blo 1764083 1764255 := bstep (se 1 (by rfl) ⟨1323191, by rfl⟩ : syracuseStep 1764255 = 2646383) B2646383
theorem B5024747 : Blo 1764083 5024747 := bstep (se 1 (by rfl) ⟨3768560, by rfl⟩ : syracuseStep 5024747 = 7537121) B7537121
theorem B1764399 : Blo 1764083 1764399 := bstep (se 1 (by rfl) ⟨1323299, by rfl⟩ : syracuseStep 1764399 = 2646599) B2646599
theorem B1764423 : Blo 1764083 1764423 := bstep (se 1 (by rfl) ⟨1323317, by rfl⟩ : syracuseStep 1764423 = 2646635) B2646635
theorem B4770937 : Blo 1764083 4770937 := bstep (se 2 (by rfl) ⟨1789101, by rfl⟩ : syracuseStep 4770937 = 3578203) B3578203
theorem B5655673 : Blo 1764083 5655673 := bstep (se 2 (by rfl) ⟨2120877, by rfl⟩ : syracuseStep 5655673 = 4241755) B4241755
theorem B5958791 : Blo 1764083 5958791 := bstep (se 1 (by rfl) ⟨4469093, by rfl⟩ : syracuseStep 5958791 = 8938187) B8938187
theorem B1764575 : Blo 1764083 1764575 := bstep (se 1 (by rfl) ⟨1323431, by rfl⟩ : syracuseStep 1764575 = 2646863) B2646863
theorem B5958899 : Blo 1764083 5958899 := bstep (se 1 (by rfl) ⟨4469174, by rfl⟩ : syracuseStep 5958899 = 8938349) B8938349
theorem B2977033 : Blo 1764083 2977033 := bstep (se 2 (by rfl) ⟨1116387, by rfl⟩ : syracuseStep 2977033 = 2232775) B2232775
theorem B24472907 : Blo 1764083 24472907 := bstep (se 1 (by rfl) ⟨18354680, by rfl⟩ : syracuseStep 24472907 = 36709361) B36709361
theorem B32206157 : Blo 1764083 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B16969175 : Blo 1764083 16969175 := bstep (se 1 (by rfl) ⟨12726881, by rfl⟩ : syracuseStep 16969175 = 25453763) B25453763
theorem B1764839 : Blo 1764083 1764839 := bstep (se 1 (by rfl) ⟨1323629, by rfl⟩ : syracuseStep 1764839 = 2647259) B2647259
theorem B9547255 : Blo 1764083 9547255 := bstep (se 1 (by rfl) ⟨7160441, by rfl⟩ : syracuseStep 9547255 = 14320883) B14320883
theorem B1764955 : Blo 1764083 1764955 := bstep (se 1 (by rfl) ⟨1323716, by rfl⟩ : syracuseStep 1764955 = 2647433) B2647433
theorem B4025963 : Blo 1764083 4025963 := bstep (se 1 (by rfl) ⟨3019472, by rfl⟩ : syracuseStep 4025963 = 6038945) B6038945
theorem B10047239 : Blo 1764083 10047239 := bstep (se 1 (by rfl) ⟨7535429, by rfl⟩ : syracuseStep 10047239 = 15070859) B15070859
theorem B2977607 : Blo 1764083 2977607 := bstep (se 1 (by rfl) ⟨2233205, by rfl⟩ : syracuseStep 2977607 = 4466411) B4466411
theorem B1765191 : Blo 1764083 1765191 := bstep (se 1 (by rfl) ⟨1323893, by rfl⟩ : syracuseStep 1765191 = 2647787) B2647787
theorem B6704977 : Blo 1764083 6704977 := bstep (se 2 (by rfl) ⟨2514366, by rfl⟩ : syracuseStep 6704977 = 5028733) B5028733
theorem B5730203 : Blo 1764083 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B1765343 : Blo 1764083 1765343 := bstep (se 1 (by rfl) ⟨1324007, by rfl⟩ : syracuseStep 1765343 = 2648015) B2648015
theorem B4772029 : Blo 1764083 4772029 := bstep (se 3 (by rfl) ⟨894755, by rfl⟩ : syracuseStep 4772029 = 1789511) B1789511
theorem B1765607 : Blo 1764083 1765607 := bstep (se 1 (by rfl) ⟨1324205, by rfl⟩ : syracuseStep 1765607 = 2648411) B2648411
theorem B5026045 : Blo 1764083 5026045 := bstep (se 3 (by rfl) ⟨942383, by rfl⟩ : syracuseStep 5026045 = 1884767) B1884767
theorem B1765759 : Blo 1764083 1765759 := bstep (se 1 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 1765759 = 2648639) B2648639
theorem B2683343 : Blo 1764083 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B2978255 : Blo 1764083 2978255 := bstep (se 1 (by rfl) ⟨2233691, by rfl⟩ : syracuseStep 2978255 = 4467383) B4467383
theorem B1765839 : Blo 1764083 1765839 := bstep (se 1 (by rfl) ⟨1324379, by rfl⟩ : syracuseStep 1765839 = 2648759) B2648759
theorem B5026387 : Blo 1764083 5026387 := bstep (se 1 (by rfl) ⟨3769790, by rfl⟩ : syracuseStep 5026387 = 7539581) B7539581
theorem B1765991 : Blo 1764083 1765991 := bstep (se 1 (by rfl) ⟨1324493, by rfl⟩ : syracuseStep 1765991 = 2648987) B2648987
theorem B3970043 : Blo 1764083 3970043 := bstep (se 1 (by rfl) ⟨2977532, by rfl⟩ : syracuseStep 3970043 = 5955065) B5955065
theorem B6362185 : Blo 1764083 6362185 := bstep (se 2 (by rfl) ⟨2385819, by rfl⟩ : syracuseStep 6362185 = 4771639) B4771639
theorem B2978923 : Blo 1764083 2978923 := bstep (se 1 (by rfl) ⟨2234192, by rfl⟩ : syracuseStep 2978923 = 4468385) B4468385
theorem B3970223 : Blo 1764083 3970223 := bstep (se 1 (by rfl) ⟨2977667, by rfl⟩ : syracuseStep 3970223 = 5955335) B5955335
theorem B3970259 : Blo 1764083 3970259 := bstep (se 1 (by rfl) ⟨2977694, by rfl⟩ : syracuseStep 3970259 = 5955389) B5955389
theorem B2979227 : Blo 1764083 2979227 := bstep (se 1 (by rfl) ⟨2234420, by rfl⟩ : syracuseStep 2979227 = 4468841) B4468841
theorem B3970529 : Blo 1764083 3970529 := bstep (se 2 (by rfl) ⟨1488948, by rfl⟩ : syracuseStep 3970529 = 2977897) B2977897
theorem B54318701 : Blo 1764083 54318701 := bstep (se 3 (by rfl) ⟨10184756, by rfl⟩ : syracuseStep 54318701 = 20369513) B20369513
theorem B2512567 : Blo 1764083 2512567 := bstep (se 1 (by rfl) ⟨1884425, by rfl⟩ : syracuseStep 2512567 = 3768851) B3768851
theorem B16103123 : Blo 1764083 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B2979551 : Blo 1764083 2979551 := bstep (se 1 (by rfl) ⟨2234663, by rfl⟩ : syracuseStep 2979551 = 4469327) B4469327
theorem B16971515 : Blo 1764083 16971515 := bstep (se 1 (by rfl) ⟨12728636, by rfl⟩ : syracuseStep 16971515 = 25457273) B25457273
theorem B3823355 : Blo 1764083 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B2012959 : Blo 1764083 2012959 := bstep (se 1 (by rfl) ⟨1509719, by rfl⟩ : syracuseStep 2012959 = 3019439) B3019439
theorem B67827617 : Blo 1764083 67827617 := bstep (se 2 (by rfl) ⟨25435356, by rfl⟩ : syracuseStep 67827617 = 50870713) B50870713
theorem B119232461 : Blo 1764083 119232461 := bstep (se 3 (by rfl) ⟨22356086, by rfl⟩ : syracuseStep 119232461 = 44712173) B44712173
theorem B4650983 : Blo 1764083 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B2979983 : Blo 1764083 2979983 := bstep (se 1 (by rfl) ⟨2234987, by rfl⟩ : syracuseStep 2979983 = 4469975) B4469975
theorem B2980219 : Blo 1764083 2980219 := bstep (se 1 (by rfl) ⟨2235164, by rfl⟩ : syracuseStep 2980219 = 4470329) B4470329
theorem B5954201 : Blo 1764083 5954201 := bstep (se 2 (by rfl) ⟨2232825, by rfl⟩ : syracuseStep 5954201 = 4465651) B4465651
theorem B8477531 : Blo 1764083 8477531 := bstep (se 1 (by rfl) ⟨6358148, by rfl⟩ : syracuseStep 8477531 = 12716297) B12716297
theorem B13409225 : Blo 1764083 13409225 := bstep (se 2 (by rfl) ⟨5028459, by rfl⟩ : syracuseStep 13409225 = 10056919) B10056919
theorem B5028905 : Blo 1764083 5028905 := bstep (se 2 (by rfl) ⟨1885839, by rfl⟩ : syracuseStep 5028905 = 3771679) B3771679
theorem B6700103 : Blo 1764083 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B3972167 : Blo 1764083 3972167 := bstep (se 1 (by rfl) ⟨2979125, by rfl⟩ : syracuseStep 3972167 = 5958251) B5958251
theorem B11312243 : Blo 1764083 11312243 := bstep (se 1 (by rfl) ⟨8484182, by rfl⟩ : syracuseStep 11312243 = 16968365) B16968365
theorem B5651585 : Blo 1764083 5651585 := bstep (se 2 (by rfl) ⟨2119344, by rfl⟩ : syracuseStep 5651585 = 4238689) B4238689
theorem B3349687 : Blo 1764083 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B38182103 : Blo 1764083 38182103 := bstep (se 1 (by rfl) ⟨28636577, by rfl⟩ : syracuseStep 38182103 = 57273155) B57273155
theorem B6364375 : Blo 1764083 6364375 := bstep (se 1 (by rfl) ⟨4773281, by rfl⟩ : syracuseStep 6364375 = 9546563) B9546563
theorem B13401449 : Blo 1764083 13401449 := bstep (se 2 (by rfl) ⟨5025543, by rfl⟩ : syracuseStep 13401449 = 10051087) B10051087
theorem B2514287 : Blo 1764083 2514287 := bstep (se 1 (by rfl) ⟨1885715, by rfl⟩ : syracuseStep 2514287 = 3771431) B3771431
theorem B16973171 : Blo 1764083 16973171 := bstep (se 1 (by rfl) ⟨12729878, by rfl⟩ : syracuseStep 16973171 = 25459757) B25459757
theorem B3972563 : Blo 1764083 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B3349991 : Blo 1764083 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B3972833 : Blo 1764083 3972833 := bstep (se 2 (by rfl) ⟨1489812, by rfl⟩ : syracuseStep 3972833 = 2979625) B2979625
theorem B4243187 : Blo 1764083 4243187 := bstep (se 1 (by rfl) ⟨3182390, by rfl⟩ : syracuseStep 4243187 = 6364781) B6364781
theorem B20102903 : Blo 1764083 20102903 := bstep (se 1 (by rfl) ⟨15077177, by rfl⟩ : syracuseStep 20102903 = 30154355) B30154355
theorem B18120935 : Blo 1764083 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B19882265 : Blo 1764083 19882265 := bstep (se 2 (by rfl) ⟨7455849, by rfl⟩ : syracuseStep 19882265 = 14911699) B14911699
theorem B6701393 : Blo 1764083 6701393 := bstep (se 2 (by rfl) ⟨2513022, by rfl⟩ : syracuseStep 6701393 = 5026045) B5026045
theorem B3973625 : Blo 1764083 3973625 := bstep (se 2 (by rfl) ⟨1490109, by rfl⟩ : syracuseStep 3973625 = 2980219) B2980219
theorem B6701575 : Blo 1764083 6701575 := bstep (se 1 (by rfl) ⟨5026181, by rfl⟩ : syracuseStep 6701575 = 10052363) B10052363
theorem B15073897 : Blo 1764083 15073897 := bstep (se 2 (by rfl) ⟨5652711, by rfl⟩ : syracuseStep 15073897 = 11305423) B11305423
theorem B2646695 : Blo 1764083 2646695 := bstep (se 1 (by rfl) ⟨1985021, by rfl⟩ : syracuseStep 2646695 = 3970043) B3970043
theorem B6701849 : Blo 1764083 6701849 := bstep (se 2 (by rfl) ⟨2513193, by rfl⟩ : syracuseStep 6701849 = 5026387) B5026387
theorem B2646815 : Blo 1764083 2646815 := bstep (se 1 (by rfl) ⟨1985111, by rfl⟩ : syracuseStep 2646815 = 3970223) B3970223
theorem B2646839 : Blo 1764083 2646839 := bstep (se 1 (by rfl) ⟨1985129, by rfl⟩ : syracuseStep 2646839 = 3970259) B3970259
theorem B2647019 : Blo 1764083 2647019 := bstep (se 1 (by rfl) ⟨1985264, by rfl⟩ : syracuseStep 2647019 = 3970529) B3970529
theorem B11314343 : Blo 1764083 11314343 := bstep (se 1 (by rfl) ⟨8485757, by rfl⟩ : syracuseStep 11314343 = 16971515) B16971515
theorem B2548903 : Blo 1764083 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B79488307 : Blo 1764083 79488307 := bstep (se 1 (by rfl) ⟨59616230, by rfl⟩ : syracuseStep 79488307 = 119232461) B119232461
theorem B1885519 : Blo 1764083 1885519 := bstep (se 1 (by rfl) ⟨1414139, by rfl⟩ : syracuseStep 1885519 = 2828279) B2828279
theorem B130573741 : Blo 1764083 130573741 := bstep (se 3 (by rfl) ⟨24482576, by rfl⟩ : syracuseStep 130573741 = 48965153) B48965153
theorem B4769207 : Blo 1764083 4769207 := bstep (se 1 (by rfl) ⟨3576905, by rfl⟩ : syracuseStep 4769207 = 7153811) B7153811
theorem B4466249 : Blo 1764083 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B8939483 : Blo 1764083 8939483 := bstep (se 1 (by rfl) ⟨6704612, by rfl⟩ : syracuseStep 8939483 = 13409225) B13409225
theorem B3352603 : Blo 1764083 3352603 := bstep (se 1 (by rfl) ⟨2514452, by rfl⟩ : syracuseStep 3352603 = 5028905) B5028905
theorem B4466735 : Blo 1764083 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B2648111 : Blo 1764083 2648111 := bstep (se 1 (by rfl) ⟨1986083, by rfl⟩ : syracuseStep 2648111 = 3972167) B3972167
theorem B25454735 : Blo 1764083 25454735 := bstep (se 1 (by rfl) ⟨19091051, by rfl⟩ : syracuseStep 25454735 = 38182103) B38182103
theorem B11315447 : Blo 1764083 11315447 := bstep (se 1 (by rfl) ⟨8486585, by rfl⟩ : syracuseStep 11315447 = 16973171) B16973171
theorem B2648375 : Blo 1764083 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B8939969 : Blo 1764083 8939969 := bstep (se 2 (by rfl) ⟨3352488, by rfl⟩ : syracuseStep 8939969 = 6704977) B6704977
theorem B2648555 : Blo 1764083 2648555 := bstep (se 1 (by rfl) ⟨1986416, by rfl⟩ : syracuseStep 2648555 = 3972833) B3972833
theorem B2828791 : Blo 1764083 2828791 := bstep (se 1 (by rfl) ⟨2121593, by rfl⟩ : syracuseStep 2828791 = 4243187) B4243187
theorem B1985071 : Blo 1764083 1985071 := bstep (se 1 (by rfl) ⟨1488803, by rfl⟩ : syracuseStep 1985071 = 2977607) B2977607
theorem B3820135 : Blo 1764083 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B7154639 : Blo 1764083 7154639 := bstep (se 1 (by rfl) ⟨5365979, by rfl⟩ : syracuseStep 7154639 = 10731959) B10731959
theorem B1764319 : Blo 1764083 1764319 := bstep (se 1 (by rfl) ⟨1323239, by rfl⟩ : syracuseStep 1764319 = 2646479) B2646479
theorem B1788895 : Blo 1764083 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B1985503 : Blo 1764083 1985503 := bstep (se 1 (by rfl) ⟨1489127, by rfl⟩ : syracuseStep 1985503 = 2978255) B2978255
theorem B33926111 : Blo 1764083 33926111 := bstep (se 1 (by rfl) ⟨25444583, by rfl⟩ : syracuseStep 33926111 = 50889167) B50889167
theorem B1764347 : Blo 1764083 1764347 := bstep (se 1 (by rfl) ⟨1323260, by rfl⟩ : syracuseStep 1764347 = 2646521) B2646521
theorem B38169643 : Blo 1764083 38169643 := bstep (se 1 (by rfl) ⟨28627232, by rfl⟩ : syracuseStep 38169643 = 57254465) B57254465
theorem B1764415 : Blo 1764083 1764415 := bstep (se 1 (by rfl) ⟨1323311, by rfl⟩ : syracuseStep 1764415 = 2646623) B2646623
theorem B4238611 : Blo 1764083 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B30149981 : Blo 1764083 30149981 := bstep (se 3 (by rfl) ⟨5653121, by rfl⟩ : syracuseStep 30149981 = 11306243) B11306243
theorem B1764735 : Blo 1764083 1764735 := bstep (se 1 (by rfl) ⟨1323551, by rfl⟩ : syracuseStep 1764735 = 2647103) B2647103
theorem B5025179 : Blo 1764083 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B1764763 : Blo 1764083 1764763 := bstep (se 1 (by rfl) ⟨1323572, by rfl⟩ : syracuseStep 1764763 = 2647145) B2647145
theorem B1764831 : Blo 1764083 1764831 := bstep (se 1 (by rfl) ⟨1323623, by rfl⟩ : syracuseStep 1764831 = 2647247) B2647247
theorem B14511611 : Blo 1764083 14511611 := bstep (se 1 (by rfl) ⟨10883708, by rfl⟩ : syracuseStep 14511611 = 21767417) B21767417
theorem B16100927 : Blo 1764083 16100927 := bstep (se 1 (by rfl) ⟨12075695, by rfl⟩ : syracuseStep 16100927 = 24151391) B24151391
theorem B1764967 : Blo 1764083 1764967 := bstep (se 1 (by rfl) ⟨1323725, by rfl⟩ : syracuseStep 1764967 = 2647451) B2647451
theorem B1986151 : Blo 1764083 1986151 := bstep (se 1 (by rfl) ⟨1489613, by rfl⟩ : syracuseStep 1986151 = 2979227) B2979227
theorem B6704765 : Blo 1764083 6704765 := bstep (se 3 (by rfl) ⟨1257143, by rfl⟩ : syracuseStep 6704765 = 2514287) B2514287
theorem B36212467 : Blo 1764083 36212467 := bstep (se 1 (by rfl) ⟨27159350, by rfl⟩ : syracuseStep 36212467 = 54318701) B54318701
theorem B1765115 : Blo 1764083 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B33943333 : Blo 1764083 33943333 := bstep (se 4 (by rfl) ⟨3182187, by rfl⟩ : syracuseStep 33943333 = 6364375) B6364375
theorem B10735415 : Blo 1764083 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B1765183 : Blo 1764083 1765183 := bstep (se 1 (by rfl) ⟨1323887, by rfl⟩ : syracuseStep 1765183 = 2647775) B2647775
theorem B1986367 : Blo 1764083 1986367 := bstep (se 1 (by rfl) ⟨1489775, by rfl⟩ : syracuseStep 1986367 = 2979551) B2979551
theorem B38178641 : Blo 1764083 38178641 := bstep (se 2 (by rfl) ⟨14316990, by rfl⟩ : syracuseStep 38178641 = 28633981) B28633981
theorem B1765247 : Blo 1764083 1765247 := bstep (se 1 (by rfl) ⟨1323935, by rfl⟩ : syracuseStep 1765247 = 2647871) B2647871
theorem B3100655 : Blo 1764083 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B1765359 : Blo 1764083 1765359 := bstep (se 1 (by rfl) ⟨1324019, by rfl⟩ : syracuseStep 1765359 = 2648039) B2648039
theorem B1765371 : Blo 1764083 1765371 := bstep (se 1 (by rfl) ⟨1324028, by rfl⟩ : syracuseStep 1765371 = 2648057) B2648057
theorem B1765439 : Blo 1764083 1765439 := bstep (se 1 (by rfl) ⟨1324079, by rfl⟩ : syracuseStep 1765439 = 2648159) B2648159
theorem B5959763 : Blo 1764083 5959763 := bstep (se 1 (by rfl) ⟨4469822, by rfl⟩ : syracuseStep 5959763 = 8939645) B8939645
theorem B8482913 : Blo 1764083 8482913 := bstep (se 2 (by rfl) ⟨3181092, by rfl⟩ : syracuseStep 8482913 = 6362185) B6362185
theorem B1986655 : Blo 1764083 1986655 := bstep (se 1 (by rfl) ⟨1489991, by rfl⟩ : syracuseStep 1986655 = 2979983) B2979983
theorem B1765479 : Blo 1764083 1765479 := bstep (se 1 (by rfl) ⟨1324109, by rfl⟩ : syracuseStep 1765479 = 2648219) B2648219
theorem B1765503 : Blo 1764083 1765503 := bstep (se 1 (by rfl) ⟨1324127, by rfl⟩ : syracuseStep 1765503 = 2648255) B2648255
theorem B1765531 : Blo 1764083 1765531 := bstep (se 1 (by rfl) ⟨1324148, by rfl⟩ : syracuseStep 1765531 = 2648297) B2648297
theorem B6361249 : Blo 1764083 6361249 := bstep (se 2 (by rfl) ⟨2385468, by rfl⟩ : syracuseStep 6361249 = 4770937) B4770937
theorem B7540897 : Blo 1764083 7540897 := bstep (se 2 (by rfl) ⟨2827836, by rfl⟩ : syracuseStep 7540897 = 5655673) B5655673
theorem B10735901 : Blo 1764083 10735901 := bstep (se 3 (by rfl) ⟨2012981, by rfl⟩ : syracuseStep 10735901 = 4025963) B4025963
theorem B3969377 : Blo 1764083 3969377 := bstep (se 2 (by rfl) ⟨1488516, by rfl⟩ : syracuseStep 3969377 = 2977033) B2977033
theorem B1765735 : Blo 1764083 1765735 := bstep (se 1 (by rfl) ⟨1324301, by rfl⟩ : syracuseStep 1765735 = 2648603) B2648603
theorem B1765787 : Blo 1764083 1765787 := bstep (se 1 (by rfl) ⟨1324340, by rfl⟩ : syracuseStep 1765787 = 2648681) B2648681
theorem B3969467 : Blo 1764083 3969467 := bstep (se 1 (by rfl) ⟨2977100, by rfl⟩ : syracuseStep 3969467 = 5954201) B5954201
theorem B10195429 : Blo 1764083 10195429 := bstep (se 4 (by rfl) ⟨955821, by rfl⟩ : syracuseStep 10195429 = 1911643) B1911643
theorem B7541495 : Blo 1764083 7541495 := bstep (se 1 (by rfl) ⟨5656121, by rfl⟩ : syracuseStep 7541495 = 11312243) B11312243
theorem B579785525 : Blo 1764083 579785525 := bstep (se 5 (by rfl) ⟨27177446, by rfl⟩ : syracuseStep 579785525 = 54354893) B54354893
theorem B16315271 : Blo 1764083 16315271 := bstep (se 1 (by rfl) ⟨12236453, by rfl⟩ : syracuseStep 16315271 = 24472907) B24472907
theorem B8934299 : Blo 1764083 8934299 := bstep (se 1 (by rfl) ⟨6700724, by rfl⟩ : syracuseStep 8934299 = 13401449) B13401449
theorem B2233327 : Blo 1764083 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B7156745 : Blo 1764083 7156745 := bstep (se 2 (by rfl) ⟨2683779, by rfl⟩ : syracuseStep 7156745 = 5367559) B5367559
theorem B2683945 : Blo 1764083 2683945 := bstep (se 2 (by rfl) ⟨1006479, by rfl⟩ : syracuseStep 2683945 = 2012959) B2012959
theorem B24163433 : Blo 1764083 24163433 := bstep (se 2 (by rfl) ⟨9061287, by rfl⟩ : syracuseStep 24163433 = 18122575) B18122575
theorem B6698159 : Blo 1764083 6698159 := bstep (se 1 (by rfl) ⟨5023619, by rfl⟩ : syracuseStep 6698159 = 10047239) B10047239
theorem B4470025 : Blo 1764083 4470025 := bstep (se 2 (by rfl) ⟨1676259, by rfl⟩ : syracuseStep 4470025 = 3352519) B3352519
theorem B8934785 : Blo 1764083 8934785 := bstep (se 2 (by rfl) ⟨3350544, by rfl⟩ : syracuseStep 8934785 = 6701089) B6701089
theorem B6362705 : Blo 1764083 6362705 := bstep (se 2 (by rfl) ⟨2386014, by rfl⟩ : syracuseStep 6362705 = 4772029) B4772029
theorem B3970727 : Blo 1764083 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B16095023 : Blo 1764083 16095023 := bstep (se 1 (by rfl) ⟨12071267, by rfl⟩ : syracuseStep 16095023 = 24142535) B24142535
theorem B3970907 : Blo 1764083 3970907 := bstep (se 1 (by rfl) ⟨2978180, by rfl⟩ : syracuseStep 3970907 = 5956361) B5956361
theorem B8935595 : Blo 1764083 8935595 := bstep (se 1 (by rfl) ⟨6701696, by rfl⟩ : syracuseStep 8935595 = 13403393) B13403393
theorem B3971411 : Blo 1764083 3971411 := bstep (se 1 (by rfl) ⟨2978558, by rfl⟩ : syracuseStep 3971411 = 5957117) B5957117
theorem B3349019 : Blo 1764083 3349019 := bstep (se 1 (by rfl) ⟨2511764, by rfl⟩ : syracuseStep 3349019 = 5023529) B5023529
theorem B45218411 : Blo 1764083 45218411 := bstep (se 1 (by rfl) ⟨33913808, by rfl⟩ : syracuseStep 45218411 = 67827617) B67827617
theorem B11311883 : Blo 1764083 11311883 := bstep (se 1 (by rfl) ⟨8483912, by rfl⟩ : syracuseStep 11311883 = 16967825) B16967825
theorem B3971897 : Blo 1764083 3971897 := bstep (se 2 (by rfl) ⟨1489461, by rfl⟩ : syracuseStep 3971897 = 2978923) B2978923
theorem B3971951 : Blo 1764083 3971951 := bstep (se 1 (by rfl) ⟨2978963, by rfl⟩ : syracuseStep 3971951 = 5957927) B5957927
theorem B20372471 : Blo 1764083 20372471 := bstep (se 1 (by rfl) ⟨15279353, by rfl⟩ : syracuseStep 20372471 = 30558707) B30558707
theorem B5651687 : Blo 1764083 5651687 := bstep (se 1 (by rfl) ⟨4238765, by rfl⟩ : syracuseStep 5651687 = 8477531) B8477531
theorem B3349831 : Blo 1764083 3349831 := bstep (se 1 (by rfl) ⟨2512373, by rfl⟩ : syracuseStep 3349831 = 5024747) B5024747
theorem B12729673 : Blo 1764083 12729673 := bstep (se 2 (by rfl) ⟨4773627, by rfl⟩ : syracuseStep 12729673 = 9547255) B9547255
theorem B3767723 : Blo 1764083 3767723 := bstep (se 1 (by rfl) ⟨2825792, by rfl⟩ : syracuseStep 3767723 = 5651585) B5651585
theorem B3972527 : Blo 1764083 3972527 := bstep (se 1 (by rfl) ⟨2979395, by rfl⟩ : syracuseStep 3972527 = 5958791) B5958791
theorem B8478145 : Blo 1764083 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B3972599 : Blo 1764083 3972599 := bstep (se 1 (by rfl) ⟨2979449, by rfl⟩ : syracuseStep 3972599 = 5958899) B5958899
theorem B21470771 : Blo 1764083 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B3350089 : Blo 1764083 3350089 := bstep (se 2 (by rfl) ⟨1256283, by rfl⟩ : syracuseStep 3350089 = 2512567) B2512567
theorem B5365369 : Blo 1764083 5365369 := bstep (se 2 (by rfl) ⟨2012013, by rfl⟩ : syracuseStep 5365369 = 4024027) B4024027
theorem B20373113 : Blo 1764083 20373113 := bstep (se 2 (by rfl) ⟨7639917, by rfl⟩ : syracuseStep 20373113 = 15279835) B15279835
theorem B11312783 : Blo 1764083 11312783 := bstep (se 1 (by rfl) ⟨8484587, by rfl⟩ : syracuseStep 11312783 = 16969175) B16969175
theorem B114515693 : Blo 1764083 114515693 := bstep (se 3 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 114515693 = 42943385) B42943385
theorem B13401935 : Blo 1764083 13401935 := bstep (se 1 (by rfl) ⟨10051451, by rfl⟩ : syracuseStep 13401935 = 20102903) B20102903
theorem B3973175 : Blo 1764083 3973175 := bstep (se 1 (by rfl) ⟨2979881, by rfl⟩ : syracuseStep 3973175 = 5959763) B5959763
theorem B2646251 : Blo 1764083 2646251 := bstep (se 1 (by rfl) ⟨1984688, by rfl⟩ : syracuseStep 2646251 = 3969377) B3969377
theorem B2646311 : Blo 1764083 2646311 := bstep (se 1 (by rfl) ⟨1984733, by rfl⟩ : syracuseStep 2646311 = 3969467) B3969467
theorem B386523683 : Blo 1764083 386523683 := bstep (se 1 (by rfl) ⟨289892762, by rfl⟩ : syracuseStep 386523683 = 579785525) B579785525
theorem B5956199 : Blo 1764083 5956199 := bstep (se 1 (by rfl) ⟨4467149, by rfl⟩ : syracuseStep 5956199 = 8934299) B8934299
theorem B28615301 : Blo 1764083 28615301 := bstep (se 4 (by rfl) ⟨2682684, by rfl⟩ : syracuseStep 28615301 = 5365369) B5365369
theorem B2646761 : Blo 1764083 2646761 := bstep (se 2 (by rfl) ⟨992535, by rfl⟩ : syracuseStep 2646761 = 1985071) B1985071
theorem B53019373 : Blo 1764083 53019373 := bstep (se 3 (by rfl) ⟨9941132, by rfl⟩ : syracuseStep 53019373 = 19882265) B19882265
theorem B4465439 : Blo 1764083 4465439 := bstep (se 1 (by rfl) ⟨3349079, by rfl⟩ : syracuseStep 4465439 = 6698159) B6698159
theorem B5956523 : Blo 1764083 5956523 := bstep (se 1 (by rfl) ⟨4467392, by rfl⟩ : syracuseStep 5956523 = 8934785) B8934785
theorem B3179471 : Blo 1764083 3179471 := bstep (se 1 (by rfl) ⟨2384603, by rfl⟩ : syracuseStep 3179471 = 4769207) B4769207
theorem B2647151 : Blo 1764083 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B2647271 : Blo 1764083 2647271 := bstep (se 1 (by rfl) ⟨1985453, by rfl⟩ : syracuseStep 2647271 = 3970907) B3970907
theorem B2647337 : Blo 1764083 2647337 := bstep (se 2 (by rfl) ⟨992751, by rfl⟩ : syracuseStep 2647337 = 1985503) B1985503
theorem B5957063 : Blo 1764083 5957063 := bstep (se 1 (by rfl) ⟨4467797, by rfl⟩ : syracuseStep 5957063 = 8935595) B8935595
theorem B2647607 : Blo 1764083 2647607 := bstep (se 1 (by rfl) ⟨1985705, by rfl⟩ : syracuseStep 2647607 = 3971411) B3971411
theorem B4466441 : Blo 1764083 4466441 := bstep (se 2 (by rfl) ⟨1674915, by rfl⟩ : syracuseStep 4466441 = 3349831) B3349831
theorem B2647931 : Blo 1764083 2647931 := bstep (se 1 (by rfl) ⟨1985948, by rfl⟩ : syracuseStep 2647931 = 3971897) B3971897
theorem B174098321 : Blo 1764083 174098321 := bstep (se 2 (by rfl) ⟨65286870, by rfl⟩ : syracuseStep 174098321 = 130573741) B130573741
theorem B2647967 : Blo 1764083 2647967 := bstep (se 1 (by rfl) ⟨1985975, by rfl⟩ : syracuseStep 2647967 = 3971951) B3971951
theorem B4769759 : Blo 1764083 4769759 := bstep (se 1 (by rfl) ⟨3577319, by rfl⟩ : syracuseStep 4769759 = 7154639) B7154639
theorem B4466785 : Blo 1764083 4466785 := bstep (se 2 (by rfl) ⟨1675044, by rfl⟩ : syracuseStep 4466785 = 3350089) B3350089
theorem B2648201 : Blo 1764083 2648201 := bstep (se 2 (by rfl) ⟨993075, by rfl⟩ : syracuseStep 2648201 = 1986151) B1986151
theorem B2648351 : Blo 1764083 2648351 := bstep (se 1 (by rfl) ⟨1986263, by rfl⟩ : syracuseStep 2648351 = 3972527) B3972527
theorem B2648399 : Blo 1764083 2648399 := bstep (se 1 (by rfl) ⟨1986299, by rfl⟩ : syracuseStep 2648399 = 3972599) B3972599
theorem B14313847 : Blo 1764083 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B10733951 : Blo 1764083 10733951 := bstep (se 1 (by rfl) ⟨8050463, by rfl⟩ : syracuseStep 10733951 = 16100927) B16100927
theorem B2648489 : Blo 1764083 2648489 := bstep (se 2 (by rfl) ⟨993183, by rfl⟩ : syracuseStep 2648489 = 1986367) B1986367
theorem B76343795 : Blo 1764083 76343795 := bstep (se 1 (by rfl) ⟨57257846, by rfl⟩ : syracuseStep 76343795 = 114515693) B114515693
theorem B2067103 : Blo 1764083 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B5655275 : Blo 1764083 5655275 := bstep (se 1 (by rfl) ⟨4241456, by rfl⟩ : syracuseStep 5655275 = 8482913) B8482913
theorem B2648873 : Blo 1764083 2648873 := bstep (se 2 (by rfl) ⟨993327, by rfl⟩ : syracuseStep 2648873 = 1986655) B1986655
theorem B8481665 : Blo 1764083 8481665 := bstep (se 2 (by rfl) ⟨3180624, by rfl⟩ : syracuseStep 8481665 = 6361249) B6361249
theorem B10054529 : Blo 1764083 10054529 := bstep (se 2 (by rfl) ⟨3770448, by rfl⟩ : syracuseStep 10054529 = 7540897) B7540897
theorem B4467595 : Blo 1764083 4467595 := bstep (se 1 (by rfl) ⟨3350696, by rfl⟩ : syracuseStep 4467595 = 6701393) B6701393
theorem B2649083 : Blo 1764083 2649083 := bstep (se 1 (by rfl) ⟨1986812, by rfl⟩ : syracuseStep 2649083 = 3973625) B3973625
theorem B1764463 : Blo 1764083 1764463 := bstep (se 1 (by rfl) ⟨1323347, by rfl⟩ : syracuseStep 1764463 = 2646695) B2646695
theorem B4467899 : Blo 1764083 4467899 := bstep (se 1 (by rfl) ⟨3350924, by rfl⟩ : syracuseStep 4467899 = 6701849) B6701849
theorem B1764543 : Blo 1764083 1764543 := bstep (se 1 (by rfl) ⟨1323407, by rfl⟩ : syracuseStep 1764543 = 2646815) B2646815
theorem B1764559 : Blo 1764083 1764559 := bstep (se 1 (by rfl) ⟨1323419, by rfl⟩ : syracuseStep 1764559 = 2646839) B2646839
theorem B13593905 : Blo 1764083 13593905 := bstep (se 2 (by rfl) ⟨5097714, by rfl⟩ : syracuseStep 13593905 = 10195429) B10195429
theorem B1764679 : Blo 1764083 1764679 := bstep (se 1 (by rfl) ⟨1323509, by rfl⟩ : syracuseStep 1764679 = 2647019) B2647019
theorem B3771721 : Blo 1764083 3771721 := bstep (se 2 (by rfl) ⟨1414395, by rfl⟩ : syracuseStep 3771721 = 2828791) B2828791
theorem B4771163 : Blo 1764083 4771163 := bstep (se 1 (by rfl) ⟨3578372, by rfl⟩ : syracuseStep 4771163 = 7156745) B7156745
theorem B16108955 : Blo 1764083 16108955 := bstep (se 1 (by rfl) ⟨12081716, by rfl⟩ : syracuseStep 16108955 = 24163433) B24163433
theorem B20098529 : Blo 1764083 20098529 := bstep (se 2 (by rfl) ⟨7536948, by rfl⟩ : syracuseStep 20098529 = 15073897) B15073897
theorem B2977499 : Blo 1764083 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B5959655 : Blo 1764083 5959655 := bstep (se 1 (by rfl) ⟨4469741, by rfl⟩ : syracuseStep 5959655 = 8939483) B8939483
theorem B2977769 : Blo 1764083 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B2977823 : Blo 1764083 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B1765407 : Blo 1764083 1765407 := bstep (se 1 (by rfl) ⟨1324055, by rfl⟩ : syracuseStep 1765407 = 2648111) B2648111
theorem B50892857 : Blo 1764083 50892857 := bstep (se 2 (by rfl) ⟨19084821, by rfl⟩ : syracuseStep 50892857 = 38169643) B38169643
theorem B16969823 : Blo 1764083 16969823 := bstep (se 1 (by rfl) ⟨12727367, by rfl⟩ : syracuseStep 16969823 = 25454735) B25454735
theorem B22605925 : Blo 1764083 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B1765583 : Blo 1764083 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B5959979 : Blo 1764083 5959979 := bstep (se 1 (by rfl) ⟨4469984, by rfl⟩ : syracuseStep 5959979 = 8939969) B8939969
theorem B1765703 : Blo 1764083 1765703 := bstep (se 1 (by rfl) ⟨1324277, by rfl⟩ : syracuseStep 1765703 = 2648555) B2648555
theorem B5960033 : Blo 1764083 5960033 := bstep (se 2 (by rfl) ⟨2235012, by rfl⟩ : syracuseStep 5960033 = 4470025) B4470025
theorem B2232679 : Blo 1764083 2232679 := bstep (se 1 (by rfl) ⟨1674509, by rfl⟩ : syracuseStep 2232679 = 3349019) B3349019
theorem B105984409 : Blo 1764083 105984409 := bstep (se 2 (by rfl) ⟨39744153, by rfl⟩ : syracuseStep 105984409 = 79488307) B79488307
theorem B7541255 : Blo 1764083 7541255 := bstep (se 1 (by rfl) ⟨5655941, by rfl⟩ : syracuseStep 7541255 = 11311883) B11311883
theorem B20099987 : Blo 1764083 20099987 := bstep (se 1 (by rfl) ⟨15074990, by rfl⟩ : syracuseStep 20099987 = 30149981) B30149981
theorem B2511815 : Blo 1764083 2511815 := bstep (se 1 (by rfl) ⟨1883861, by rfl⟩ : syracuseStep 2511815 = 3767723) B3767723
theorem B45257777 : Blo 1764083 45257777 := bstep (se 2 (by rfl) ⟨16971666, by rfl⟩ : syracuseStep 45257777 = 33943333) B33943333
theorem B4469843 : Blo 1764083 4469843 := bstep (se 1 (by rfl) ⟨3352382, by rfl⟩ : syracuseStep 4469843 = 6704765) B6704765
theorem B7541855 : Blo 1764083 7541855 := bstep (se 1 (by rfl) ⟨5656391, by rfl⟩ : syracuseStep 7541855 = 11312783) B11312783
theorem B9540773 : Blo 1764083 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B7156943 : Blo 1764083 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B8934623 : Blo 1764083 8934623 := bstep (se 1 (by rfl) ⟨6700967, by rfl⟩ : syracuseStep 8934623 = 13401935) B13401935
theorem B4470137 : Blo 1764083 4470137 := bstep (se 2 (by rfl) ⟨1676301, by rfl⟩ : syracuseStep 4470137 = 3352603) B3352603
theorem B12080623 : Blo 1764083 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B7157267 : Blo 1764083 7157267 := bstep (se 1 (by rfl) ⟨5367950, by rfl⟩ : syracuseStep 7157267 = 10735901) B10735901
theorem B5027663 : Blo 1764083 5027663 := bstep (se 1 (by rfl) ⟨3770747, by rfl⟩ : syracuseStep 5027663 = 7541495) B7541495
theorem B10876847 : Blo 1764083 10876847 := bstep (se 1 (by rfl) ⟨8157635, by rfl⟩ : syracuseStep 10876847 = 16315271) B16315271
theorem B8935433 : Blo 1764083 8935433 := bstep (se 2 (by rfl) ⟨3350787, by rfl⟩ : syracuseStep 8935433 = 6701575) B6701575
theorem B7542895 : Blo 1764083 7542895 := bstep (se 1 (by rfl) ⟨5657171, by rfl⟩ : syracuseStep 7542895 = 11314343) B11314343
theorem B5093513 : Blo 1764083 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B4241803 : Blo 1764083 4241803 := bstep (se 1 (by rfl) ⟨3181352, by rfl⟩ : syracuseStep 4241803 = 6362705) B6362705
theorem B13400477 : Blo 1764083 13400477 := bstep (se 3 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 13400477 = 5025179) B5025179
theorem B10730015 : Blo 1764083 10730015 := bstep (se 1 (by rfl) ⟨8047511, by rfl⟩ : syracuseStep 10730015 = 16095023) B16095023
theorem B3578593 : Blo 1764083 3578593 := bstep (se 2 (by rfl) ⟨1341972, by rfl⟩ : syracuseStep 3578593 = 2683945) B2683945
theorem B7543631 : Blo 1764083 7543631 := bstep (se 1 (by rfl) ⟨5657723, by rfl⟩ : syracuseStep 7543631 = 11315447) B11315447
theorem B3398537 : Blo 1764083 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B30145607 : Blo 1764083 30145607 := bstep (se 1 (by rfl) ⟨22609205, by rfl⟩ : syracuseStep 30145607 = 45218411) B45218411
theorem B16972897 : Blo 1764083 16972897 := bstep (se 2 (by rfl) ⟨6364836, by rfl⟩ : syracuseStep 16972897 = 12729673) B12729673
theorem B2514025 : Blo 1764083 2514025 := bstep (se 2 (by rfl) ⟨942759, by rfl⟩ : syracuseStep 2514025 = 1885519) B1885519
theorem B11304193 : Blo 1764083 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B22617407 : Blo 1764083 22617407 := bstep (se 1 (by rfl) ⟨16963055, by rfl⟩ : syracuseStep 22617407 = 33926111) B33926111
theorem B13581647 : Blo 1764083 13581647 := bstep (se 1 (by rfl) ⟨10186235, by rfl⟩ : syracuseStep 13581647 = 20372471) B20372471
theorem B3767791 : Blo 1764083 3767791 := bstep (se 1 (by rfl) ⟨2825843, by rfl⟩ : syracuseStep 3767791 = 5651687) B5651687
theorem B48283289 : Blo 1764083 48283289 := bstep (se 2 (by rfl) ⟨18106233, by rfl⟩ : syracuseStep 48283289 = 36212467) B36212467
theorem B9674407 : Blo 1764083 9674407 := bstep (se 1 (by rfl) ⟨7255805, by rfl⟩ : syracuseStep 9674407 = 14511611) B14511611
theorem B13582075 : Blo 1764083 13582075 := bstep (se 1 (by rfl) ⟨10186556, by rfl⟩ : syracuseStep 13582075 = 20373113) B20373113
theorem B25452427 : Blo 1764083 25452427 := bstep (se 1 (by rfl) ⟨19089320, by rfl⟩ : syracuseStep 25452427 = 38178641) B38178641
theorem B11313215 : Blo 1764083 11313215 := bstep (se 1 (by rfl) ⟨8484911, by rfl⟩ : syracuseStep 11313215 = 16969823) B16969823
theorem B5955713 : Blo 1764083 5955713 := bstep (se 2 (by rfl) ⟨2233392, by rfl⟩ : syracuseStep 5955713 = 4466785) B4466785
theorem B3973319 : Blo 1764083 3973319 := bstep (se 1 (by rfl) ⟨2979989, by rfl⟩ : syracuseStep 3973319 = 5959979) B5959979
theorem B3973355 : Blo 1764083 3973355 := bstep (se 1 (by rfl) ⟨2980016, by rfl⟩ : syracuseStep 3973355 = 5960033) B5960033
theorem B141312545 : Blo 1764083 141312545 := bstep (se 2 (by rfl) ⟨52992204, by rfl⟩ : syracuseStep 141312545 = 105984409) B105984409
theorem B30171851 : Blo 1764083 30171851 := bstep (se 1 (by rfl) ⟨22628888, by rfl⟩ : syracuseStep 30171851 = 45257777) B45257777
theorem B5956415 : Blo 1764083 5956415 := bstep (se 1 (by rfl) ⟨4467311, by rfl⟩ : syracuseStep 5956415 = 8934623) B8934623
theorem B12723101 : Blo 1764083 12723101 := bstep (se 3 (by rfl) ⟨2385581, by rfl⟩ : syracuseStep 12723101 = 4771163) B4771163
theorem B5956793 : Blo 1764083 5956793 := bstep (se 2 (by rfl) ⟨2233797, by rfl⟩ : syracuseStep 5956793 = 4467595) B4467595
theorem B3351775 : Blo 1764083 3351775 := bstep (se 1 (by rfl) ⟨2513831, by rfl⟩ : syracuseStep 3351775 = 5027663) B5027663
theorem B116065547 : Blo 1764083 116065547 := bstep (se 1 (by rfl) ⟨87049160, by rfl⟩ : syracuseStep 116065547 = 174098321) B174098321
theorem B3179839 : Blo 1764083 3179839 := bstep (se 1 (by rfl) ⟨2384879, by rfl⟩ : syracuseStep 3179839 = 4769759) B4769759
theorem B5956955 : Blo 1764083 5956955 := bstep (se 1 (by rfl) ⟨4467716, by rfl⟩ : syracuseStep 5956955 = 8935433) B8935433
theorem B3352033 : Blo 1764083 3352033 := bstep (se 2 (by rfl) ⟨1257012, by rfl⟩ : syracuseStep 3352033 = 2514025) B2514025
theorem B7153343 : Blo 1764083 7153343 := bstep (se 1 (by rfl) ⟨5365007, by rfl⟩ : syracuseStep 7153343 = 10730015) B10730015
theorem B3770183 : Blo 1764083 3770183 := bstep (se 1 (by rfl) ⟨2827637, by rfl⟩ : syracuseStep 3770183 = 5655275) B5655275
theorem B5654443 : Blo 1764083 5654443 := bstep (se 1 (by rfl) ⟨4240832, by rfl⟩ : syracuseStep 5654443 = 8481665) B8481665
theorem B6703019 : Blo 1764083 6703019 := bstep (se 1 (by rfl) ⟨5027264, by rfl⟩ : syracuseStep 6703019 = 10054529) B10054529
theorem B5023721 : Blo 1764083 5023721 := bstep (se 2 (by rfl) ⟨1883895, by rfl⟩ : syracuseStep 5023721 = 3767791) B3767791
theorem B16107497 : Blo 1764083 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B20097071 : Blo 1764083 20097071 := bstep (se 1 (by rfl) ⟨15072803, by rfl⟩ : syracuseStep 20097071 = 30145607) B30145607
theorem B9062603 : Blo 1764083 9062603 := bstep (se 1 (by rfl) ⟨6796952, by rfl⟩ : syracuseStep 9062603 = 13593905) B13593905
theorem B9054431 : Blo 1764083 9054431 := bstep (se 1 (by rfl) ⟨6790823, by rfl⟩ : syracuseStep 9054431 = 13581647) B13581647
theorem B9062765 : Blo 1764083 9062765 := bstep (se 3 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 9062765 = 3398537) B3398537
theorem B32188859 : Blo 1764083 32188859 := bstep (se 1 (by rfl) ⟨24141644, by rfl⟩ : syracuseStep 32188859 = 48283289) B48283289
theorem B1984999 : Blo 1764083 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B1985179 : Blo 1764083 1985179 := bstep (se 1 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 1985179 = 2977769) B2977769
theorem B1985215 : Blo 1764083 1985215 := bstep (se 1 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 1985215 = 2977823) B2977823
theorem B2648783 : Blo 1764083 2648783 := bstep (se 1 (by rfl) ⟨1986587, by rfl⟩ : syracuseStep 2648783 = 3973175) B3973175
theorem B30141233 : Blo 1764083 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B1764167 : Blo 1764083 1764167 := bstep (se 1 (by rfl) ⟨1323125, by rfl⟩ : syracuseStep 1764167 = 2646251) B2646251
theorem B1764207 : Blo 1764083 1764207 := bstep (se 1 (by rfl) ⟨1323155, by rfl⟩ : syracuseStep 1764207 = 2646311) B2646311
theorem B257682455 : Blo 1764083 257682455 := bstep (se 1 (by rfl) ⟨193261841, by rfl⟩ : syracuseStep 257682455 = 386523683) B386523683
theorem B2976905 : Blo 1764083 2976905 := bstep (se 2 (by rfl) ⟨1116339, by rfl⟩ : syracuseStep 2976905 = 2232679) B2232679
theorem B1764507 : Blo 1764083 1764507 := bstep (se 1 (by rfl) ⟨1323380, by rfl⟩ : syracuseStep 1764507 = 2646761) B2646761
theorem B5655737 : Blo 1764083 5655737 := bstep (se 2 (by rfl) ⟨2120901, by rfl⟩ : syracuseStep 5655737 = 4241803) B4241803
theorem B2976959 : Blo 1764083 2976959 := bstep (se 1 (by rfl) ⟨2232719, by rfl⟩ : syracuseStep 2976959 = 4465439) B4465439
theorem B1764767 : Blo 1764083 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B6360515 : Blo 1764083 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B4771295 : Blo 1764083 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B1764847 : Blo 1764083 1764847 := bstep (se 1 (by rfl) ⟨1323635, by rfl⟩ : syracuseStep 1764847 = 2647271) B2647271
theorem B1764891 : Blo 1764083 1764891 := bstep (se 1 (by rfl) ⟨1323668, by rfl⟩ : syracuseStep 1764891 = 2647337) B2647337
theorem B4771457 : Blo 1764083 4771457 := bstep (se 2 (by rfl) ⟨1789296, by rfl⟩ : syracuseStep 4771457 = 3578593) B3578593
theorem B70692497 : Blo 1764083 70692497 := bstep (se 2 (by rfl) ⟨26509686, by rfl⟩ : syracuseStep 70692497 = 53019373) B53019373
theorem B4771511 : Blo 1764083 4771511 := bstep (se 1 (by rfl) ⟨3578633, by rfl⟩ : syracuseStep 4771511 = 7157267) B7157267
theorem B1765071 : Blo 1764083 1765071 := bstep (se 1 (by rfl) ⟨1323803, by rfl⟩ : syracuseStep 1765071 = 2647607) B2647607
theorem B2977627 : Blo 1764083 2977627 := bstep (se 1 (by rfl) ⟨2233220, by rfl⟩ : syracuseStep 2977627 = 4466441) B4466441
theorem B1765287 : Blo 1764083 1765287 := bstep (se 1 (by rfl) ⟨1323965, by rfl⟩ : syracuseStep 1765287 = 2647931) B2647931
theorem B1765311 : Blo 1764083 1765311 := bstep (se 1 (by rfl) ⟨1323983, by rfl⟩ : syracuseStep 1765311 = 2647967) B2647967
theorem B3395675 : Blo 1764083 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B1765467 : Blo 1764083 1765467 := bstep (se 1 (by rfl) ⟨1324100, by rfl⟩ : syracuseStep 1765467 = 2648201) B2648201
theorem B22630529 : Blo 1764083 22630529 := bstep (se 2 (by rfl) ⟨8486448, by rfl⟩ : syracuseStep 22630529 = 16972897) B16972897
theorem B1765567 : Blo 1764083 1765567 := bstep (se 1 (by rfl) ⟨1324175, by rfl⟩ : syracuseStep 1765567 = 2648351) B2648351
theorem B1765599 : Blo 1764083 1765599 := bstep (se 1 (by rfl) ⟨1324199, by rfl⟩ : syracuseStep 1765599 = 2648399) B2648399
theorem B7155967 : Blo 1764083 7155967 := bstep (se 1 (by rfl) ⟨5366975, by rfl⟩ : syracuseStep 7155967 = 10733951) B10733951
theorem B8933651 : Blo 1764083 8933651 := bstep (se 1 (by rfl) ⟨6700238, by rfl⟩ : syracuseStep 8933651 = 13400477) B13400477
theorem B1765659 : Blo 1764083 1765659 := bstep (se 1 (by rfl) ⟨1324244, by rfl⟩ : syracuseStep 1765659 = 2648489) B2648489
theorem B1765915 : Blo 1764083 1765915 := bstep (se 1 (by rfl) ⟨1324436, by rfl⟩ : syracuseStep 1765915 = 2648873) B2648873
theorem B1766055 : Blo 1764083 1766055 := bstep (se 1 (by rfl) ⟨1324541, by rfl⟩ : syracuseStep 1766055 = 2649083) B2649083
theorem B2978599 : Blo 1764083 2978599 := bstep (se 1 (by rfl) ⟨2233949, by rfl⟩ : syracuseStep 2978599 = 4467899) B4467899
theorem B15078271 : Blo 1764083 15078271 := bstep (se 1 (by rfl) ⟨11308703, by rfl⟩ : syracuseStep 15078271 = 22617407) B22617407
theorem B12899209 : Blo 1764083 12899209 := bstep (se 2 (by rfl) ⟨4837203, by rfl⟩ : syracuseStep 12899209 = 9674407) B9674407
theorem B13399019 : Blo 1764083 13399019 := bstep (se 1 (by rfl) ⟨10049264, by rfl⟩ : syracuseStep 13399019 = 20098529) B20098529
theorem B18109433 : Blo 1764083 18109433 := bstep (se 2 (by rfl) ⟨6791037, by rfl⟩ : syracuseStep 18109433 = 13582075) B13582075
theorem B29004925 : Blo 1764083 29004925 := bstep (se 3 (by rfl) ⟨5438423, by rfl⟩ : syracuseStep 29004925 = 10876847) B10876847
theorem B33936569 : Blo 1764083 33936569 := bstep (se 2 (by rfl) ⟨12726213, by rfl⟩ : syracuseStep 33936569 = 25452427) B25452427
theorem B6698173 : Blo 1764083 6698173 := bstep (se 3 (by rfl) ⟨1255907, by rfl⟩ : syracuseStep 6698173 = 2511815) B2511815
theorem B33928571 : Blo 1764083 33928571 := bstep (se 1 (by rfl) ⟨25446428, by rfl⟩ : syracuseStep 33928571 = 50892857) B50892857
theorem B10057193 : Blo 1764083 10057193 := bstep (se 2 (by rfl) ⟨3771447, by rfl⟩ : syracuseStep 10057193 = 7542895) B7542895
theorem B5027503 : Blo 1764083 5027503 := bstep (se 1 (by rfl) ⟨3770627, by rfl⟩ : syracuseStep 5027503 = 7541255) B7541255
theorem B3970799 : Blo 1764083 3970799 := bstep (se 1 (by rfl) ⟨2978099, by rfl⟩ : syracuseStep 3970799 = 5956199) B5956199
theorem B19076867 : Blo 1764083 19076867 := bstep (se 1 (by rfl) ⟨14307650, by rfl⟩ : syracuseStep 19076867 = 28615301) B28615301
theorem B19085129 : Blo 1764083 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B13399991 : Blo 1764083 13399991 := bstep (se 1 (by rfl) ⟨10049993, by rfl⟩ : syracuseStep 13399991 = 20099987) B20099987
theorem B3971015 : Blo 1764083 3971015 := bstep (se 1 (by rfl) ⟨2978261, by rfl⟩ : syracuseStep 3971015 = 5956523) B5956523
theorem B2979895 : Blo 1764083 2979895 := bstep (se 1 (by rfl) ⟨2234921, by rfl⟩ : syracuseStep 2979895 = 4469843) B4469843
theorem B5027903 : Blo 1764083 5027903 := bstep (se 1 (by rfl) ⟨3770927, by rfl⟩ : syracuseStep 5027903 = 7541855) B7541855
theorem B11024549 : Blo 1764083 11024549 := bstep (se 4 (by rfl) ⟨1033551, by rfl⟩ : syracuseStep 11024549 = 2067103) B2067103
theorem B2980091 : Blo 1764083 2980091 := bstep (se 1 (by rfl) ⟨2235068, by rfl⟩ : syracuseStep 2980091 = 4470137) B4470137
theorem B3971375 : Blo 1764083 3971375 := bstep (se 1 (by rfl) ⟨2978531, by rfl⟩ : syracuseStep 3971375 = 5957063) B5957063
theorem B50895863 : Blo 1764083 50895863 := bstep (se 1 (by rfl) ⟨38171897, by rfl⟩ : syracuseStep 50895863 = 76343795) B76343795
theorem B15072257 : Blo 1764083 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B5028961 : Blo 1764083 5028961 := bstep (se 2 (by rfl) ⟨1885860, by rfl⟩ : syracuseStep 5028961 = 3771721) B3771721
theorem B5029087 : Blo 1764083 5029087 := bstep (se 1 (by rfl) ⟨3771815, by rfl⟩ : syracuseStep 5029087 = 7543631) B7543631
theorem B10739303 : Blo 1764083 10739303 := bstep (se 1 (by rfl) ⟨8054477, by rfl⟩ : syracuseStep 10739303 = 16108955) B16108955
theorem B8478589 : Blo 1764083 8478589 := bstep (se 3 (by rfl) ⟨1589735, by rfl⟩ : syracuseStep 8478589 = 3179471) B3179471
theorem B3973103 : Blo 1764083 3973103 := bstep (se 1 (by rfl) ⟨2979827, by rfl⟩ : syracuseStep 3973103 = 5959655) B5959655
theorem B3973193 : Blo 1764083 3973193 := bstep (se 2 (by rfl) ⟨1489947, by rfl⟩ : syracuseStep 3973193 = 2979895) B2979895
theorem B5955767 : Blo 1764083 5955767 := bstep (se 1 (by rfl) ⟨4466825, by rfl⟩ : syracuseStep 5955767 = 8933651) B8933651
theorem B94208363 : Blo 1764083 94208363 := bstep (se 1 (by rfl) ⟨70656272, by rfl⟩ : syracuseStep 94208363 = 141312545) B141312545
theorem B2646665 : Blo 1764083 2646665 := bstep (se 2 (by rfl) ⟨992499, by rfl⟩ : syracuseStep 2646665 = 1984999) B1984999
theorem B2646905 : Blo 1764083 2646905 := bstep (se 2 (by rfl) ⟨992589, by rfl⟩ : syracuseStep 2646905 = 1985179) B1985179
theorem B22619047 : Blo 1764083 22619047 := bstep (se 1 (by rfl) ⟨16964285, by rfl⟩ : syracuseStep 22619047 = 33928571) B33928571
theorem B2646953 : Blo 1764083 2646953 := bstep (se 2 (by rfl) ⟨992607, by rfl⟩ : syracuseStep 2646953 = 1985215) B1985215
theorem B4768895 : Blo 1764083 4768895 := bstep (se 1 (by rfl) ⟨3576671, by rfl⟩ : syracuseStep 4768895 = 7153343) B7153343
theorem B2647199 : Blo 1764083 2647199 := bstep (se 1 (by rfl) ⟨1985399, by rfl⟩ : syracuseStep 2647199 = 3970799) B3970799
theorem B20104361 : Blo 1764083 20104361 := bstep (se 2 (by rfl) ⟨7539135, by rfl⟩ : syracuseStep 20104361 = 15078271) B15078271
theorem B12723419 : Blo 1764083 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B2647343 : Blo 1764083 2647343 := bstep (se 1 (by rfl) ⟨1985507, by rfl⟩ : syracuseStep 2647343 = 3971015) B3971015
theorem B3351935 : Blo 1764083 3351935 := bstep (se 1 (by rfl) ⟨2513951, by rfl⟩ : syracuseStep 3351935 = 5027903) B5027903
theorem B7349699 : Blo 1764083 7349699 := bstep (se 1 (by rfl) ⟨5512274, by rfl⟩ : syracuseStep 7349699 = 11024549) B11024549
theorem B2647583 : Blo 1764083 2647583 := bstep (se 1 (by rfl) ⟨1985687, by rfl⟩ : syracuseStep 2647583 = 3971375) B3971375
theorem B8930897 : Blo 1764083 8930897 := bstep (se 2 (by rfl) ⟨3349086, by rfl⟩ : syracuseStep 8930897 = 6698173) B6698173
theorem B171788303 : Blo 1764083 171788303 := bstep (se 1 (by rfl) ⟨128841227, by rfl⟩ : syracuseStep 171788303 = 257682455) B257682455
theorem B1984603 : Blo 1764083 1984603 := bstep (se 1 (by rfl) ⟨1488452, by rfl⟩ : syracuseStep 1984603 = 2976905) B2976905
theorem B3770491 : Blo 1764083 3770491 := bstep (se 1 (by rfl) ⟨2827868, by rfl⟩ : syracuseStep 3770491 = 5655737) B5655737
theorem B1984639 : Blo 1764083 1984639 := bstep (se 1 (by rfl) ⟨1488479, by rfl⟩ : syracuseStep 1984639 = 2976959) B2976959
theorem B10053821 : Blo 1764083 10053821 := bstep (se 3 (by rfl) ⟨1885091, by rfl⟩ : syracuseStep 10053821 = 3770183) B3770183
theorem B6703337 : Blo 1764083 6703337 := bstep (se 2 (by rfl) ⟨2513751, by rfl⟩ : syracuseStep 6703337 = 5027503) B5027503
theorem B3180863 : Blo 1764083 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B3180971 : Blo 1764083 3180971 := bstep (se 1 (by rfl) ⟨2385728, by rfl⟩ : syracuseStep 3180971 = 4771457) B4771457
theorem B3181007 : Blo 1764083 3181007 := bstep (se 1 (by rfl) ⟨2385755, by rfl⟩ : syracuseStep 3181007 = 4771511) B4771511
theorem B7539257 : Blo 1764083 7539257 := bstep (se 2 (by rfl) ⟨2827221, by rfl⟩ : syracuseStep 7539257 = 5654443) B5654443
theorem B13396589 : Blo 1764083 13396589 := bstep (se 3 (by rfl) ⟨2511860, by rfl⟩ : syracuseStep 13396589 = 5023721) B5023721
theorem B2648735 : Blo 1764083 2648735 := bstep (se 1 (by rfl) ⟨1986551, by rfl⟩ : syracuseStep 2648735 = 3973103) B3973103
theorem B2263783 : Blo 1764083 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B2648879 : Blo 1764083 2648879 := bstep (se 1 (by rfl) ⟨1986659, by rfl⟩ : syracuseStep 2648879 = 3973319) B3973319
theorem B2648903 : Blo 1764083 2648903 := bstep (se 1 (by rfl) ⟨1986677, by rfl⟩ : syracuseStep 2648903 = 3973355) B3973355
theorem B20114567 : Blo 1764083 20114567 := bstep (se 1 (by rfl) ⟨15085925, by rfl⟩ : syracuseStep 20114567 = 30171851) B30171851
theorem B8482067 : Blo 1764083 8482067 := bstep (se 1 (by rfl) ⟨6361550, by rfl⟩ : syracuseStep 8482067 = 12723101) B12723101
theorem B8932679 : Blo 1764083 8932679 := bstep (se 1 (by rfl) ⟨6699509, by rfl⟩ : syracuseStep 8932679 = 13399019) B13399019
theorem B77377031 : Blo 1764083 77377031 := bstep (se 1 (by rfl) ⟨58032773, by rfl⟩ : syracuseStep 77377031 = 116065547) B116065547
theorem B6704795 : Blo 1764083 6704795 := bstep (se 1 (by rfl) ⟨5028596, by rfl⟩ : syracuseStep 6704795 = 10057193) B10057193
theorem B12717911 : Blo 1764083 12717911 := bstep (se 1 (by rfl) ⟨9538433, by rfl⟩ : syracuseStep 12717911 = 19076867) B19076867
theorem B17198945 : Blo 1764083 17198945 := bstep (se 2 (by rfl) ⟨6449604, by rfl⟩ : syracuseStep 17198945 = 12899209) B12899209
theorem B4468679 : Blo 1764083 4468679 := bstep (se 1 (by rfl) ⟨3351509, by rfl⟩ : syracuseStep 4468679 = 6703019) B6703019
theorem B8933327 : Blo 1764083 8933327 := bstep (se 1 (by rfl) ⟨6699995, by rfl⟩ : syracuseStep 8933327 = 13399991) B13399991
theorem B13398047 : Blo 1764083 13398047 := bstep (se 1 (by rfl) ⟨10048535, by rfl⟩ : syracuseStep 13398047 = 20097071) B20097071
theorem B6705281 : Blo 1764083 6705281 := bstep (se 2 (by rfl) ⟨2514480, by rfl⟩ : syracuseStep 6705281 = 5028961) B5028961
theorem B6041735 : Blo 1764083 6041735 := bstep (se 1 (by rfl) ⟨4531301, by rfl⟩ : syracuseStep 6041735 = 9062603) B9062603
theorem B1986727 : Blo 1764083 1986727 := bstep (se 1 (by rfl) ⟨1490045, by rfl⟩ : syracuseStep 1986727 = 2980091) B2980091
theorem B6041843 : Blo 1764083 6041843 := bstep (se 1 (by rfl) ⟨4531382, by rfl⟩ : syracuseStep 6041843 = 9062765) B9062765
theorem B21459239 : Blo 1764083 21459239 := bstep (se 1 (by rfl) ⟨16094429, by rfl⟩ : syracuseStep 21459239 = 32188859) B32188859
theorem B4469033 : Blo 1764083 4469033 := bstep (se 2 (by rfl) ⟨1675887, by rfl⟩ : syracuseStep 4469033 = 3351775) B3351775
theorem B6705449 : Blo 1764083 6705449 := bstep (se 2 (by rfl) ⟨2514543, by rfl⟩ : syracuseStep 6705449 = 5029087) B5029087
theorem B4239785 : Blo 1764083 4239785 := bstep (se 2 (by rfl) ⟨1589919, by rfl⟩ : syracuseStep 4239785 = 3179839) B3179839
theorem B1765855 : Blo 1764083 1765855 := bstep (se 1 (by rfl) ⟨1324391, by rfl⟩ : syracuseStep 1765855 = 2648783) B2648783
theorem B4469377 : Blo 1764083 4469377 := bstep (se 2 (by rfl) ⟨1676016, by rfl⟩ : syracuseStep 4469377 = 3352033) B3352033
theorem B10048171 : Blo 1764083 10048171 := bstep (se 1 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 10048171 = 15072257) B15072257
theorem B4240343 : Blo 1764083 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B3970169 : Blo 1764083 3970169 := bstep (se 2 (by rfl) ⟨1488813, by rfl⟩ : syracuseStep 3970169 = 2977627) B2977627
theorem B7542143 : Blo 1764083 7542143 := bstep (se 1 (by rfl) ⟨5656607, by rfl⟩ : syracuseStep 7542143 = 11313215) B11313215
theorem B3970475 : Blo 1764083 3970475 := bstep (se 1 (by rfl) ⟨2977856, by rfl⟩ : syracuseStep 3970475 = 5955713) B5955713
theorem B15087019 : Blo 1764083 15087019 := bstep (se 1 (by rfl) ⟨11315264, by rfl⟩ : syracuseStep 15087019 = 22630529) B22630529
theorem B9541289 : Blo 1764083 9541289 := bstep (se 2 (by rfl) ⟨3577983, by rfl⟩ : syracuseStep 9541289 = 7155967) B7155967
theorem B3970943 : Blo 1764083 3970943 := bstep (se 1 (by rfl) ⟨2978207, by rfl⟩ : syracuseStep 3970943 = 5956415) B5956415
theorem B3971195 : Blo 1764083 3971195 := bstep (se 1 (by rfl) ⟨2978396, by rfl⟩ : syracuseStep 3971195 = 5956793) B5956793
theorem B22624379 : Blo 1764083 22624379 := bstep (se 1 (by rfl) ⟨16968284, by rfl⟩ : syracuseStep 22624379 = 33936569) B33936569
theorem B3971303 : Blo 1764083 3971303 := bstep (se 1 (by rfl) ⟨2978477, by rfl⟩ : syracuseStep 3971303 = 5956955) B5956955
theorem B3971465 : Blo 1764083 3971465 := bstep (se 2 (by rfl) ⟨1489299, by rfl⟩ : syracuseStep 3971465 = 2978599) B2978599
theorem B10738331 : Blo 1764083 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B6036287 : Blo 1764083 6036287 := bstep (se 1 (by rfl) ⟨4527215, by rfl⟩ : syracuseStep 6036287 = 9054431) B9054431
theorem B38673233 : Blo 1764083 38673233 := bstep (se 2 (by rfl) ⟨14502462, by rfl⟩ : syracuseStep 38673233 = 29004925) B29004925
theorem B20094155 : Blo 1764083 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B33930575 : Blo 1764083 33930575 := bstep (se 1 (by rfl) ⟨25447931, by rfl⟩ : syracuseStep 33930575 = 50895863) B50895863
theorem B7159535 : Blo 1764083 7159535 := bstep (se 1 (by rfl) ⟨5369651, by rfl⟩ : syracuseStep 7159535 = 10739303) B10739303
theorem B47128331 : Blo 1764083 47128331 := bstep (se 1 (by rfl) ⟨35346248, by rfl⟩ : syracuseStep 47128331 = 70692497) B70692497
theorem B11304785 : Blo 1764083 11304785 := bstep (se 2 (by rfl) ⟨4239294, by rfl⟩ : syracuseStep 11304785 = 8478589) B8478589
theorem B48291821 : Blo 1764083 48291821 := bstep (se 3 (by rfl) ⟨9054716, by rfl⟩ : syracuseStep 48291821 = 18109433) B18109433
theorem B2646137 : Blo 1764083 2646137 := bstep (se 2 (by rfl) ⟨992301, by rfl⟩ : syracuseStep 2646137 = 1984603) B1984603
theorem B2646185 : Blo 1764083 2646185 := bstep (se 2 (by rfl) ⟨992319, by rfl⟩ : syracuseStep 2646185 = 1984639) B1984639
theorem B2826523 : Blo 1764083 2826523 := bstep (se 1 (by rfl) ⟨2119892, by rfl⟩ : syracuseStep 2826523 = 4239785) B4239785
theorem B2826895 : Blo 1764083 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B2646779 : Blo 1764083 2646779 := bstep (se 1 (by rfl) ⟨1985084, by rfl⟩ : syracuseStep 2646779 = 3970169) B3970169
theorem B3179263 : Blo 1764083 3179263 := bstep (se 1 (by rfl) ⟨2384447, by rfl⟩ : syracuseStep 3179263 = 4768895) B4768895
theorem B13402907 : Blo 1764083 13402907 := bstep (se 1 (by rfl) ⟨10052180, by rfl⟩ : syracuseStep 13402907 = 20104361) B20104361
theorem B2646983 : Blo 1764083 2646983 := bstep (se 1 (by rfl) ⟨1985237, by rfl⟩ : syracuseStep 2646983 = 3970475) B3970475
theorem B4899799 : Blo 1764083 4899799 := bstep (se 1 (by rfl) ⟨3674849, by rfl⟩ : syracuseStep 4899799 = 7349699) B7349699
theorem B2647295 : Blo 1764083 2647295 := bstep (se 1 (by rfl) ⟨1985471, by rfl⟩ : syracuseStep 2647295 = 3970943) B3970943
theorem B114525535 : Blo 1764083 114525535 := bstep (se 1 (by rfl) ⟨85894151, by rfl⟩ : syracuseStep 114525535 = 171788303) B171788303
theorem B2647463 : Blo 1764083 2647463 := bstep (se 1 (by rfl) ⟨1985597, by rfl⟩ : syracuseStep 2647463 = 3971195) B3971195
theorem B15082919 : Blo 1764083 15082919 := bstep (se 1 (by rfl) ⟨11312189, by rfl⟩ : syracuseStep 15082919 = 22624379) B22624379
theorem B6702547 : Blo 1764083 6702547 := bstep (se 1 (by rfl) ⟨5026910, by rfl⟩ : syracuseStep 6702547 = 10053821) B10053821
theorem B2647535 : Blo 1764083 2647535 := bstep (se 1 (by rfl) ⟨1985651, by rfl⟩ : syracuseStep 2647535 = 3971303) B3971303
theorem B2647643 : Blo 1764083 2647643 := bstep (se 1 (by rfl) ⟨1985732, by rfl⟩ : syracuseStep 2647643 = 3971465) B3971465
theorem B8931059 : Blo 1764083 8931059 := bstep (se 1 (by rfl) ⟨6698294, by rfl⟩ : syracuseStep 8931059 = 13396589) B13396589
theorem B25782155 : Blo 1764083 25782155 := bstep (se 1 (by rfl) ⟨19336616, by rfl⟩ : syracuseStep 25782155 = 38673233) B38673233
theorem B13396103 : Blo 1764083 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B5654711 : Blo 1764083 5654711 := bstep (se 1 (by rfl) ⟨4241033, by rfl⟩ : syracuseStep 5654711 = 8482067) B8482067
theorem B22620383 : Blo 1764083 22620383 := bstep (se 1 (by rfl) ⟨16965287, by rfl⟩ : syracuseStep 22620383 = 33930575) B33930575
theorem B31418887 : Blo 1764083 31418887 := bstep (se 1 (by rfl) ⟨23564165, by rfl⟩ : syracuseStep 31418887 = 47128331) B47128331
theorem B8932031 : Blo 1764083 8932031 := bstep (se 1 (by rfl) ⟨6699023, by rfl⟩ : syracuseStep 8932031 = 13398047) B13398047
theorem B2648795 : Blo 1764083 2648795 := bstep (se 1 (by rfl) ⟨1986596, by rfl⟩ : syracuseStep 2648795 = 3973193) B3973193
theorem B14306159 : Blo 1764083 14306159 := bstep (se 1 (by rfl) ⟨10729619, by rfl⟩ : syracuseStep 14306159 = 21459239) B21459239
theorem B2648969 : Blo 1764083 2648969 := bstep (se 2 (by rfl) ⟨993363, by rfl⟩ : syracuseStep 2648969 = 1986727) B1986727
theorem B1764443 : Blo 1764083 1764443 := bstep (se 1 (by rfl) ⟨1323332, by rfl⟩ : syracuseStep 1764443 = 2646665) B2646665
theorem B1764603 : Blo 1764083 1764603 := bstep (se 1 (by rfl) ⟨1323452, by rfl⟩ : syracuseStep 1764603 = 2646905) B2646905
theorem B1764635 : Blo 1764083 1764635 := bstep (se 1 (by rfl) ⟨1323476, by rfl⟩ : syracuseStep 1764635 = 2646953) B2646953
theorem B1764799 : Blo 1764083 1764799 := bstep (se 1 (by rfl) ⟨1323599, by rfl⟩ : syracuseStep 1764799 = 2647199) B2647199
theorem B5959169 : Blo 1764083 5959169 := bstep (se 2 (by rfl) ⟨2234688, by rfl⟩ : syracuseStep 5959169 = 4469377) B4469377
theorem B1764895 : Blo 1764083 1764895 := bstep (se 1 (by rfl) ⟨1323671, by rfl⟩ : syracuseStep 1764895 = 2647343) B2647343
theorem B13397561 : Blo 1764083 13397561 := bstep (se 2 (by rfl) ⟨5024085, by rfl⟩ : syracuseStep 13397561 = 10048171) B10048171
theorem B3018377 : Blo 1764083 3018377 := bstep (se 2 (by rfl) ⟨1131891, by rfl⟩ : syracuseStep 3018377 = 2263783) B2263783
theorem B1765055 : Blo 1764083 1765055 := bstep (se 1 (by rfl) ⟨1323791, by rfl⟩ : syracuseStep 1765055 = 2647583) B2647583
theorem B6360859 : Blo 1764083 6360859 := bstep (se 1 (by rfl) ⟨4770644, by rfl⟩ : syracuseStep 6360859 = 9541289) B9541289
theorem B8482589 : Blo 1764083 8482589 := bstep (se 3 (by rfl) ⟨1590485, by rfl⟩ : syracuseStep 8482589 = 3180971) B3180971
theorem B30158729 : Blo 1764083 30158729 := bstep (se 2 (by rfl) ⟨11309523, by rfl⟩ : syracuseStep 30158729 = 22619047) B22619047
theorem B4468891 : Blo 1764083 4468891 := bstep (se 1 (by rfl) ⟨3351668, by rfl⟩ : syracuseStep 4468891 = 6703337) B6703337
theorem B5026171 : Blo 1764083 5026171 := bstep (se 1 (by rfl) ⟨3769628, by rfl⟩ : syracuseStep 5026171 = 7539257) B7539257
theorem B1765823 : Blo 1764083 1765823 := bstep (se 1 (by rfl) ⟨1324367, by rfl⟩ : syracuseStep 1765823 = 2648735) B2648735
theorem B1765919 : Blo 1764083 1765919 := bstep (se 1 (by rfl) ⟨1324439, by rfl⟩ : syracuseStep 1765919 = 2648879) B2648879
theorem B1765935 : Blo 1764083 1765935 := bstep (se 1 (by rfl) ⟨1324451, by rfl⟩ : syracuseStep 1765935 = 2648903) B2648903
theorem B20116025 : Blo 1764083 20116025 := bstep (se 2 (by rfl) ⟨7543509, by rfl⟩ : syracuseStep 20116025 = 15087019) B15087019
theorem B4469863 : Blo 1764083 4469863 := bstep (se 1 (by rfl) ⟨3352397, by rfl⟩ : syracuseStep 4469863 = 6704795) B6704795
theorem B4773023 : Blo 1764083 4773023 := bstep (se 1 (by rfl) ⟨3579767, by rfl⟩ : syracuseStep 4773023 = 7159535) B7159535
theorem B11465963 : Blo 1764083 11465963 := bstep (se 1 (by rfl) ⟨8599472, by rfl⟩ : syracuseStep 11465963 = 17198945) B17198945
theorem B2979119 : Blo 1764083 2979119 := bstep (se 1 (by rfl) ⟨2234339, by rfl⟩ : syracuseStep 2979119 = 4468679) B4468679
theorem B4470187 : Blo 1764083 4470187 := bstep (se 1 (by rfl) ⟨3352640, by rfl⟩ : syracuseStep 4470187 = 6705281) B6705281
theorem B4027823 : Blo 1764083 4027823 := bstep (se 1 (by rfl) ⟨3020867, by rfl⟩ : syracuseStep 4027823 = 6041735) B6041735
theorem B3970511 : Blo 1764083 3970511 := bstep (se 1 (by rfl) ⟨2977883, by rfl⟩ : syracuseStep 3970511 = 5955767) B5955767
theorem B4027895 : Blo 1764083 4027895 := bstep (se 1 (by rfl) ⟨3020921, by rfl⟩ : syracuseStep 4027895 = 6041843) B6041843
theorem B5027321 : Blo 1764083 5027321 := bstep (se 2 (by rfl) ⟨1885245, by rfl⟩ : syracuseStep 5027321 = 3770491) B3770491
theorem B2979355 : Blo 1764083 2979355 := bstep (se 1 (by rfl) ⟨2234516, by rfl⟩ : syracuseStep 2979355 = 4469033) B4469033
theorem B4470299 : Blo 1764083 4470299 := bstep (se 1 (by rfl) ⟨3352724, by rfl⟩ : syracuseStep 4470299 = 6705449) B6705449
theorem B62805575 : Blo 1764083 62805575 := bstep (se 1 (by rfl) ⟨47104181, by rfl⟩ : syracuseStep 62805575 = 94208363) B94208363
theorem B33929117 : Blo 1764083 33929117 := bstep (se 3 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 33929117 = 12723419) B12723419
theorem B2234623 : Blo 1764083 2234623 := bstep (se 1 (by rfl) ⟨1675967, by rfl⟩ : syracuseStep 2234623 = 3351935) B3351935
theorem B5028095 : Blo 1764083 5028095 := bstep (se 1 (by rfl) ⟨3771071, by rfl⟩ : syracuseStep 5028095 = 7542143) B7542143
theorem B5953931 : Blo 1764083 5953931 := bstep (se 1 (by rfl) ⟨4465448, by rfl⟩ : syracuseStep 5953931 = 8930897) B8930897
theorem B2120575 : Blo 1764083 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B2120671 : Blo 1764083 2120671 := bstep (se 1 (by rfl) ⟨1590503, by rfl⟩ : syracuseStep 2120671 = 3181007) B3181007
theorem B7158887 : Blo 1764083 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B13409711 : Blo 1764083 13409711 := bstep (se 1 (by rfl) ⟨10057283, by rfl⟩ : syracuseStep 13409711 = 20114567) B20114567
theorem B16096765 : Blo 1764083 16096765 := bstep (se 3 (by rfl) ⟨3018143, by rfl⟩ : syracuseStep 16096765 = 6036287) B6036287
theorem B5955119 : Blo 1764083 5955119 := bstep (se 1 (by rfl) ⟨4466339, by rfl⟩ : syracuseStep 5955119 = 8932679) B8932679
theorem B51584687 : Blo 1764083 51584687 := bstep (se 1 (by rfl) ⟨38688515, by rfl⟩ : syracuseStep 51584687 = 77377031) B77377031
theorem B7536523 : Blo 1764083 7536523 := bstep (se 1 (by rfl) ⟨5652392, by rfl⟩ : syracuseStep 7536523 = 11304785) B11304785
theorem B8478607 : Blo 1764083 8478607 := bstep (se 1 (by rfl) ⟨6358955, by rfl⟩ : syracuseStep 8478607 = 12717911) B12717911
theorem B5955551 : Blo 1764083 5955551 := bstep (se 1 (by rfl) ⟨4466663, by rfl⟩ : syracuseStep 5955551 = 8933327) B8933327
theorem B32194547 : Blo 1764083 32194547 := bstep (se 1 (by rfl) ⟨24145910, by rfl⟩ : syracuseStep 32194547 = 48291821) B48291821
theorem B3768697 : Blo 1764083 3768697 := bstep (se 2 (by rfl) ⟨1413261, by rfl⟩ : syracuseStep 3768697 = 2826523) B2826523
theorem B13410683 : Blo 1764083 13410683 := bstep (se 1 (by rfl) ⟨10058012, by rfl⟩ : syracuseStep 13410683 = 20116025) B20116025
theorem B6701561 : Blo 1764083 6701561 := bstep (se 2 (by rfl) ⟨2513085, by rfl⟩ : syracuseStep 6701561 = 5026171) B5026171
theorem B7643975 : Blo 1764083 7643975 := bstep (se 1 (by rfl) ⟨5732981, by rfl⟩ : syracuseStep 7643975 = 11465963) B11465963
theorem B3769193 : Blo 1764083 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B2647007 : Blo 1764083 2647007 := bstep (se 1 (by rfl) ⟨1985255, by rfl⟩ : syracuseStep 2647007 = 3970511) B3970511
theorem B3351547 : Blo 1764083 3351547 := bstep (se 1 (by rfl) ⟨2513660, by rfl⟩ : syracuseStep 3351547 = 5027321) B5027321
theorem B2827433 : Blo 1764083 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B17188103 : Blo 1764083 17188103 := bstep (se 1 (by rfl) ⟨12891077, by rfl⟩ : syracuseStep 17188103 = 25782155) B25782155
theorem B22619411 : Blo 1764083 22619411 := bstep (se 1 (by rfl) ⟨16964558, by rfl⟩ : syracuseStep 22619411 = 33929117) B33929117
theorem B2827561 : Blo 1764083 2827561 := bstep (se 2 (by rfl) ⟨1060335, by rfl⟩ : syracuseStep 2827561 = 2120671) B2120671
theorem B8930735 : Blo 1764083 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B152700713 : Blo 1764083 152700713 := bstep (se 2 (by rfl) ⟨57262767, by rfl⟩ : syracuseStep 152700713 = 114525535) B114525535
theorem B9537439 : Blo 1764083 9537439 := bstep (se 1 (by rfl) ⟨7153079, by rfl⟩ : syracuseStep 9537439 = 14306159) B14306159
theorem B8939807 : Blo 1764083 8939807 := bstep (se 1 (by rfl) ⟨6704855, by rfl⟩ : syracuseStep 8939807 = 13409711) B13409711
theorem B8481145 : Blo 1764083 8481145 := bstep (se 2 (by rfl) ⟨3180429, by rfl⟩ : syracuseStep 8481145 = 6360859) B6360859
theorem B8931707 : Blo 1764083 8931707 := bstep (se 1 (by rfl) ⟨6698780, by rfl⟩ : syracuseStep 8931707 = 13397561) B13397561
theorem B5655059 : Blo 1764083 5655059 := bstep (se 1 (by rfl) ⟨4241294, by rfl⟩ : syracuseStep 5655059 = 8482589) B8482589
theorem B20105819 : Blo 1764083 20105819 := bstep (se 1 (by rfl) ⟨15079364, by rfl⟩ : syracuseStep 20105819 = 30158729) B30158729
theorem B1764091 : Blo 1764083 1764091 := bstep (se 1 (by rfl) ⟨1323068, by rfl⟩ : syracuseStep 1764091 = 2646137) B2646137
theorem B1764123 : Blo 1764083 1764123 := bstep (se 1 (by rfl) ⟨1323092, by rfl⟩ : syracuseStep 1764123 = 2646185) B2646185
theorem B5958521 : Blo 1764083 5958521 := bstep (se 2 (by rfl) ⟨2234445, by rfl⟩ : syracuseStep 5958521 = 4468891) B4468891
theorem B1764519 : Blo 1764083 1764519 := bstep (se 1 (by rfl) ⟨1323389, by rfl⟩ : syracuseStep 1764519 = 2646779) B2646779
theorem B1764655 : Blo 1764083 1764655 := bstep (se 1 (by rfl) ⟨1323491, by rfl⟩ : syracuseStep 1764655 = 2646983) B2646983
theorem B3182015 : Blo 1764083 3182015 := bstep (se 1 (by rfl) ⟨2386511, by rfl⟩ : syracuseStep 3182015 = 4773023) B4773023
theorem B1764863 : Blo 1764083 1764863 := bstep (se 1 (by rfl) ⟨1323647, by rfl⟩ : syracuseStep 1764863 = 2647295) B2647295
theorem B1986079 : Blo 1764083 1986079 := bstep (se 1 (by rfl) ⟨1489559, by rfl⟩ : syracuseStep 1986079 = 2979119) B2979119
theorem B1764975 : Blo 1764083 1764975 := bstep (se 1 (by rfl) ⟨1323731, by rfl⟩ : syracuseStep 1764975 = 2647463) B2647463
theorem B10055279 : Blo 1764083 10055279 := bstep (se 1 (by rfl) ⟨7541459, by rfl⟩ : syracuseStep 10055279 = 15082919) B15082919
theorem B1765023 : Blo 1764083 1765023 := bstep (se 1 (by rfl) ⟨1323767, by rfl⟩ : syracuseStep 1765023 = 2647535) B2647535
theorem B4239017 : Blo 1764083 4239017 := bstep (se 2 (by rfl) ⟨1589631, by rfl⟩ : syracuseStep 4239017 = 3179263) B3179263
theorem B1765095 : Blo 1764083 1765095 := bstep (se 1 (by rfl) ⟨1323821, by rfl⟩ : syracuseStep 1765095 = 2647643) B2647643
theorem B6533065 : Blo 1764083 6533065 := bstep (se 2 (by rfl) ⟨2449899, by rfl⟩ : syracuseStep 6533065 = 4899799) B4899799
theorem B5959817 : Blo 1764083 5959817 := bstep (se 2 (by rfl) ⟨2234931, by rfl⟩ : syracuseStep 5959817 = 4469863) B4469863
theorem B167481533 : Blo 1764083 167481533 := bstep (se 3 (by rfl) ⟨31402787, by rfl⟩ : syracuseStep 167481533 = 62805575) B62805575
theorem B3969287 : Blo 1764083 3969287 := bstep (se 1 (by rfl) ⟨2976965, by rfl⟩ : syracuseStep 3969287 = 5953931) B5953931
theorem B1765863 : Blo 1764083 1765863 := bstep (se 1 (by rfl) ⟨1324397, by rfl⟩ : syracuseStep 1765863 = 2648795) B2648795
theorem B5960249 : Blo 1764083 5960249 := bstep (se 2 (by rfl) ⟨2235093, by rfl⟩ : syracuseStep 5960249 = 4470187) B4470187
theorem B1765979 : Blo 1764083 1765979 := bstep (se 1 (by rfl) ⟨1324484, by rfl⟩ : syracuseStep 1765979 = 2648969) B2648969
theorem B4772591 : Blo 1764083 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B3970079 : Blo 1764083 3970079 := bstep (se 1 (by rfl) ⟨2977559, by rfl⟩ : syracuseStep 3970079 = 5955119) B5955119
theorem B2012251 : Blo 1764083 2012251 := bstep (se 1 (by rfl) ⟨1509188, by rfl⟩ : syracuseStep 2012251 = 3018377) B3018377
theorem B10048697 : Blo 1764083 10048697 := bstep (se 2 (by rfl) ⟨3768261, by rfl⟩ : syracuseStep 10048697 = 7536523) B7536523
theorem B3970367 : Blo 1764083 3970367 := bstep (se 1 (by rfl) ⟨2977775, by rfl⟩ : syracuseStep 3970367 = 5955551) B5955551
theorem B2979497 : Blo 1764083 2979497 := bstep (se 2 (by rfl) ⟨1117311, by rfl⟩ : syracuseStep 2979497 = 2234623) B2234623
theorem B15079229 : Blo 1764083 15079229 := bstep (se 3 (by rfl) ⟨2827355, by rfl⟩ : syracuseStep 15079229 = 5654711) B5654711
theorem B8935271 : Blo 1764083 8935271 := bstep (se 1 (by rfl) ⟨6701453, by rfl⟩ : syracuseStep 8935271 = 13402907) B13402907
theorem B13408253 : Blo 1764083 13408253 := bstep (se 3 (by rfl) ⟨2514047, by rfl⟩ : syracuseStep 13408253 = 5028095) B5028095
theorem B41891849 : Blo 1764083 41891849 := bstep (se 2 (by rfl) ⟨15709443, by rfl⟩ : syracuseStep 41891849 = 31418887) B31418887
theorem B2685215 : Blo 1764083 2685215 := bstep (se 1 (by rfl) ⟨2013911, by rfl⟩ : syracuseStep 2685215 = 4027823) B4027823
theorem B2685263 : Blo 1764083 2685263 := bstep (se 1 (by rfl) ⟨2013947, by rfl⟩ : syracuseStep 2685263 = 4027895) B4027895
theorem B2980199 : Blo 1764083 2980199 := bstep (se 1 (by rfl) ⟨2235149, by rfl⟩ : syracuseStep 2980199 = 4470299) B4470299
theorem B5954039 : Blo 1764083 5954039 := bstep (se 1 (by rfl) ⟨4465529, by rfl⟩ : syracuseStep 5954039 = 8931059) B8931059
theorem B15080255 : Blo 1764083 15080255 := bstep (se 1 (by rfl) ⟨11310191, by rfl⟩ : syracuseStep 15080255 = 22620383) B22620383
theorem B5954687 : Blo 1764083 5954687 := bstep (se 1 (by rfl) ⟨4466015, by rfl⟩ : syracuseStep 5954687 = 8932031) B8932031
theorem B8936729 : Blo 1764083 8936729 := bstep (se 2 (by rfl) ⟨3351273, by rfl⟩ : syracuseStep 8936729 = 6702547) B6702547
theorem B21462353 : Blo 1764083 21462353 := bstep (se 2 (by rfl) ⟨8048382, by rfl⟩ : syracuseStep 21462353 = 16096765) B16096765
theorem B3972473 : Blo 1764083 3972473 := bstep (se 2 (by rfl) ⟨1489677, by rfl⟩ : syracuseStep 3972473 = 2979355) B2979355
theorem B3972779 : Blo 1764083 3972779 := bstep (se 1 (by rfl) ⟨2979584, by rfl⟩ : syracuseStep 3972779 = 5959169) B5959169
theorem B34389791 : Blo 1764083 34389791 := bstep (se 1 (by rfl) ⟨25792343, by rfl⟩ : syracuseStep 34389791 = 51584687) B51584687
theorem B11304809 : Blo 1764083 11304809 := bstep (se 2 (by rfl) ⟨4239303, by rfl⟩ : syracuseStep 11304809 = 8478607) B8478607
theorem B21463031 : Blo 1764083 21463031 := bstep (se 1 (by rfl) ⟨16097273, by rfl⟩ : syracuseStep 21463031 = 32194547) B32194547
theorem B3973211 : Blo 1764083 3973211 := bstep (se 1 (by rfl) ⟨2979908, by rfl⟩ : syracuseStep 3973211 = 5959817) B5959817
theorem B2646191 : Blo 1764083 2646191 := bstep (se 1 (by rfl) ⟨1984643, by rfl⟩ : syracuseStep 2646191 = 3969287) B3969287
theorem B3973499 : Blo 1764083 3973499 := bstep (se 1 (by rfl) ⟨2980124, by rfl⟩ : syracuseStep 3973499 = 5960249) B5960249
theorem B45834941 : Blo 1764083 45834941 := bstep (se 3 (by rfl) ⟨8594051, by rfl⟩ : syracuseStep 45834941 = 17188103) B17188103
theorem B2646719 : Blo 1764083 2646719 := bstep (se 1 (by rfl) ⟨1985039, by rfl⟩ : syracuseStep 2646719 = 3970079) B3970079
theorem B1884955 : Blo 1764083 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B2646911 : Blo 1764083 2646911 := bstep (se 1 (by rfl) ⟨1985183, by rfl⟩ : syracuseStep 2646911 = 3970367) B3970367
theorem B10052819 : Blo 1764083 10052819 := bstep (se 1 (by rfl) ⟨7539614, by rfl⟩ : syracuseStep 10052819 = 15079229) B15079229
theorem B5956847 : Blo 1764083 5956847 := bstep (se 1 (by rfl) ⟨4467635, by rfl⟩ : syracuseStep 5956847 = 8935271) B8935271
theorem B8938835 : Blo 1764083 8938835 := bstep (se 1 (by rfl) ⟨6704126, by rfl⟩ : syracuseStep 8938835 = 13408253) B13408253
theorem B27927899 : Blo 1764083 27927899 := bstep (se 1 (by rfl) ⟨20945924, by rfl⟩ : syracuseStep 27927899 = 41891849) B41891849
theorem B3770039 : Blo 1764083 3770039 := bstep (se 1 (by rfl) ⟨2827529, by rfl⟩ : syracuseStep 3770039 = 5655059) B5655059
theorem B3770081 : Blo 1764083 3770081 := bstep (se 2 (by rfl) ⟨1413780, by rfl⟩ : syracuseStep 3770081 = 2827561) B2827561
theorem B13403879 : Blo 1764083 13403879 := bstep (se 1 (by rfl) ⟨10052909, by rfl⟩ : syracuseStep 13403879 = 20105819) B20105819
theorem B10053503 : Blo 1764083 10053503 := bstep (se 1 (by rfl) ⟨7540127, by rfl⟩ : syracuseStep 10053503 = 15080255) B15080255
theorem B2648105 : Blo 1764083 2648105 := bstep (se 2 (by rfl) ⟨993039, by rfl⟩ : syracuseStep 2648105 = 1986079) B1986079
theorem B5957819 : Blo 1764083 5957819 := bstep (se 1 (by rfl) ⟨4468364, by rfl⟩ : syracuseStep 5957819 = 8936729) B8936729
theorem B20383933 : Blo 1764083 20383933 := bstep (se 3 (by rfl) ⟨3821987, by rfl⟩ : syracuseStep 20383933 = 7643975) B7643975
theorem B2648315 : Blo 1764083 2648315 := bstep (se 1 (by rfl) ⟨1986236, by rfl⟩ : syracuseStep 2648315 = 3972473) B3972473
theorem B6703519 : Blo 1764083 6703519 := bstep (se 1 (by rfl) ⟨5027639, by rfl⟩ : syracuseStep 6703519 = 10055279) B10055279
theorem B2648519 : Blo 1764083 2648519 := bstep (se 1 (by rfl) ⟨1986389, by rfl⟩ : syracuseStep 2648519 = 3972779) B3972779
theorem B12716585 : Blo 1764083 12716585 := bstep (se 2 (by rfl) ⟨4768719, by rfl⟩ : syracuseStep 12716585 = 9537439) B9537439
theorem B8710753 : Blo 1764083 8710753 := bstep (se 2 (by rfl) ⟨3266532, by rfl⟩ : syracuseStep 8710753 = 6533065) B6533065
theorem B8940455 : Blo 1764083 8940455 := bstep (se 1 (by rfl) ⟨6705341, by rfl⟩ : syracuseStep 8940455 = 13410683) B13410683
theorem B4467707 : Blo 1764083 4467707 := bstep (se 1 (by rfl) ⟨3350780, by rfl⟩ : syracuseStep 4467707 = 6701561) B6701561
theorem B3181727 : Blo 1764083 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B5024929 : Blo 1764083 5024929 := bstep (se 2 (by rfl) ⟨1884348, by rfl⟩ : syracuseStep 5024929 = 3768697) B3768697
theorem B11308193 : Blo 1764083 11308193 := bstep (se 2 (by rfl) ⟨4240572, by rfl⟩ : syracuseStep 11308193 = 8481145) B8481145
theorem B1764671 : Blo 1764083 1764671 := bstep (se 1 (by rfl) ⟨1323503, by rfl⟩ : syracuseStep 1764671 = 2647007) B2647007
theorem B28642805 : Blo 1764083 28642805 := bstep (se 5 (by rfl) ⟨1342631, by rfl⟩ : syracuseStep 28642805 = 2685263) B2685263
theorem B1986331 : Blo 1764083 1986331 := bstep (se 1 (by rfl) ⟨1489748, by rfl⟩ : syracuseStep 1986331 = 2979497) B2979497
theorem B4468729 : Blo 1764083 4468729 := bstep (se 2 (by rfl) ⟨1675773, by rfl⟩ : syracuseStep 4468729 = 3351547) B3351547
theorem B2683001 : Blo 1764083 2683001 := bstep (se 2 (by rfl) ⟨1006125, by rfl⟩ : syracuseStep 2683001 = 2012251) B2012251
theorem B5959871 : Blo 1764083 5959871 := bstep (se 1 (by rfl) ⟨4469903, by rfl⟩ : syracuseStep 5959871 = 8939807) B8939807
theorem B1790143 : Blo 1764083 1790143 := bstep (se 1 (by rfl) ⟨1342607, by rfl⟩ : syracuseStep 1790143 = 2685215) B2685215
theorem B1986799 : Blo 1764083 1986799 := bstep (se 1 (by rfl) ⟨1490099, by rfl⟩ : syracuseStep 1986799 = 2980199) B2980199
theorem B3969359 : Blo 1764083 3969359 := bstep (se 1 (by rfl) ⟨2977019, by rfl⟩ : syracuseStep 3969359 = 5954039) B5954039
theorem B3969791 : Blo 1764083 3969791 := bstep (se 1 (by rfl) ⟨2977343, by rfl⟩ : syracuseStep 3969791 = 5954687) B5954687
theorem B14308235 : Blo 1764083 14308235 := bstep (se 1 (by rfl) ⟨10731176, by rfl⟩ : syracuseStep 14308235 = 21462353) B21462353
theorem B22926527 : Blo 1764083 22926527 := bstep (se 1 (by rfl) ⟨17194895, by rfl⟩ : syracuseStep 22926527 = 34389791) B34389791
theorem B14308687 : Blo 1764083 14308687 := bstep (se 1 (by rfl) ⟨10731515, by rfl⟩ : syracuseStep 14308687 = 21463031) B21463031
theorem B111654355 : Blo 1764083 111654355 := bstep (se 1 (by rfl) ⟨83740766, by rfl⟩ : syracuseStep 111654355 = 167481533) B167481533
theorem B2512795 : Blo 1764083 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B6699131 : Blo 1764083 6699131 := bstep (se 1 (by rfl) ⟨5024348, by rfl⟩ : syracuseStep 6699131 = 10048697) B10048697
theorem B15079607 : Blo 1764083 15079607 := bstep (se 1 (by rfl) ⟨11309705, by rfl⟩ : syracuseStep 15079607 = 22619411) B22619411
theorem B5953823 : Blo 1764083 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B8485373 : Blo 1764083 8485373 := bstep (se 3 (by rfl) ⟨1591007, by rfl⟩ : syracuseStep 8485373 = 3182015) B3182015
theorem B101800475 : Blo 1764083 101800475 := bstep (se 1 (by rfl) ⟨76350356, by rfl⟩ : syracuseStep 101800475 = 152700713) B152700713
theorem B5954471 : Blo 1764083 5954471 := bstep (se 1 (by rfl) ⟨4465853, by rfl⟩ : syracuseStep 5954471 = 8931707) B8931707
theorem B3972347 : Blo 1764083 3972347 := bstep (se 1 (by rfl) ⟨2979260, by rfl⟩ : syracuseStep 3972347 = 5958521) B5958521
theorem B2826011 : Blo 1764083 2826011 := bstep (se 1 (by rfl) ⟨2119508, by rfl⟩ : syracuseStep 2826011 = 4239017) B4239017
theorem B7536539 : Blo 1764083 7536539 := bstep (se 1 (by rfl) ⟨5652404, by rfl⟩ : syracuseStep 7536539 = 11304809) B11304809
theorem B3973247 : Blo 1764083 3973247 := bstep (se 1 (by rfl) ⟨2979935, by rfl⟩ : syracuseStep 3973247 = 5959871) B5959871
theorem B2646239 : Blo 1764083 2646239 := bstep (se 1 (by rfl) ⟨1984679, by rfl⟩ : syracuseStep 2646239 = 3969359) B3969359
theorem B2646527 : Blo 1764083 2646527 := bstep (se 1 (by rfl) ⟨1984895, by rfl⟩ : syracuseStep 2646527 = 3969791) B3969791
theorem B8938025 : Blo 1764083 8938025 := bstep (se 2 (by rfl) ⟨3351759, by rfl⟩ : syracuseStep 8938025 = 6703519) B6703519
theorem B6701879 : Blo 1764083 6701879 := bstep (se 1 (by rfl) ⟨5026409, by rfl⟩ : syracuseStep 6701879 = 10052819) B10052819
theorem B6702335 : Blo 1764083 6702335 := bstep (se 1 (by rfl) ⟨5026751, by rfl⟩ : syracuseStep 6702335 = 10053503) B10053503
theorem B4466087 : Blo 1764083 4466087 := bstep (se 1 (by rfl) ⟨3349565, by rfl⟩ : syracuseStep 4466087 = 6699131) B6699131
theorem B10053071 : Blo 1764083 10053071 := bstep (se 1 (by rfl) ⟨7539803, by rfl⟩ : syracuseStep 10053071 = 15079607) B15079607
theorem B122226509 : Blo 1764083 122226509 := bstep (se 3 (by rfl) ⟨22917470, by rfl⟩ : syracuseStep 122226509 = 45834941) B45834941
theorem B7538795 : Blo 1764083 7538795 := bstep (se 1 (by rfl) ⟨5654096, by rfl⟩ : syracuseStep 7538795 = 11308193) B11308193
theorem B2648231 : Blo 1764083 2648231 := bstep (se 1 (by rfl) ⟨1986173, by rfl⟩ : syracuseStep 2648231 = 3972347) B3972347
theorem B2648441 : Blo 1764083 2648441 := bstep (se 2 (by rfl) ⟨993165, by rfl⟩ : syracuseStep 2648441 = 1986331) B1986331
theorem B5024359 : Blo 1764083 5024359 := bstep (se 1 (by rfl) ⟨3768269, by rfl⟩ : syracuseStep 5024359 = 7536539) B7536539
theorem B5958305 : Blo 1764083 5958305 := bstep (se 2 (by rfl) ⟨2234364, by rfl⟩ : syracuseStep 5958305 = 4468729) B4468729
theorem B2648807 : Blo 1764083 2648807 := bstep (se 1 (by rfl) ⟨1986605, by rfl⟩ : syracuseStep 2648807 = 3973211) B3973211
theorem B1788667 : Blo 1764083 1788667 := bstep (se 1 (by rfl) ⟨1341500, by rfl⟩ : syracuseStep 1788667 = 2683001) B2683001
theorem B1764127 : Blo 1764083 1764127 := bstep (se 1 (by rfl) ⟨1323095, by rfl⟩ : syracuseStep 1764127 = 2646191) B2646191
theorem B2648999 : Blo 1764083 2648999 := bstep (se 1 (by rfl) ⟨1986749, by rfl⟩ : syracuseStep 2648999 = 3973499) B3973499
theorem B2649065 : Blo 1764083 2649065 := bstep (se 2 (by rfl) ⟨993399, by rfl⟩ : syracuseStep 2649065 = 1986799) B1986799
theorem B1764479 : Blo 1764083 1764479 := bstep (se 1 (by rfl) ⟨1323359, by rfl⟩ : syracuseStep 1764479 = 2646719) B2646719
theorem B1764607 : Blo 1764083 1764607 := bstep (se 1 (by rfl) ⟨1323455, by rfl⟩ : syracuseStep 1764607 = 2646911) B2646911
theorem B9538823 : Blo 1764083 9538823 := bstep (se 1 (by rfl) ⟨7154117, by rfl⟩ : syracuseStep 9538823 = 14308235) B14308235
theorem B5959223 : Blo 1764083 5959223 := bstep (se 1 (by rfl) ⟨4469417, by rfl⟩ : syracuseStep 5959223 = 8938835) B8938835
theorem B9547429 : Blo 1764083 9547429 := bstep (se 4 (by rfl) ⟨895071, by rfl⟩ : syracuseStep 9547429 = 1790143) B1790143
theorem B1765403 : Blo 1764083 1765403 := bstep (se 1 (by rfl) ⟨1324052, by rfl⟩ : syracuseStep 1765403 = 2648105) B2648105
theorem B1765543 : Blo 1764083 1765543 := bstep (se 1 (by rfl) ⟨1324157, by rfl⟩ : syracuseStep 1765543 = 2648315) B2648315
theorem B3969215 : Blo 1764083 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B1765679 : Blo 1764083 1765679 := bstep (se 1 (by rfl) ⟨1324259, by rfl⟩ : syracuseStep 1765679 = 2648519) B2648519
theorem B5656915 : Blo 1764083 5656915 := bstep (se 1 (by rfl) ⟨4242686, by rfl⟩ : syracuseStep 5656915 = 8485373) B8485373
theorem B67866983 : Blo 1764083 67866983 := bstep (se 1 (by rfl) ⟨50900237, by rfl⟩ : syracuseStep 67866983 = 101800475) B101800475
theorem B3969647 : Blo 1764083 3969647 := bstep (se 1 (by rfl) ⟨2977235, by rfl⟩ : syracuseStep 3969647 = 5954471) B5954471
theorem B5960303 : Blo 1764083 5960303 := bstep (se 1 (by rfl) ⟨4470227, by rfl⟩ : syracuseStep 5960303 = 8940455) B8940455
theorem B2978471 : Blo 1764083 2978471 := bstep (se 1 (by rfl) ⟨2233853, by rfl⟩ : syracuseStep 2978471 = 4467707) B4467707
theorem B27178577 : Blo 1764083 27178577 := bstep (se 2 (by rfl) ⟨10191966, by rfl⟩ : syracuseStep 27178577 = 20383933) B20383933
theorem B15284351 : Blo 1764083 15284351 := bstep (se 1 (by rfl) ⟨11463263, by rfl⟩ : syracuseStep 15284351 = 22926527) B22926527
theorem B11614337 : Blo 1764083 11614337 := bstep (se 2 (by rfl) ⟨4355376, by rfl⟩ : syracuseStep 11614337 = 8710753) B8710753
theorem B3971231 : Blo 1764083 3971231 := bstep (se 1 (by rfl) ⟨2978423, by rfl⟩ : syracuseStep 3971231 = 5956847) B5956847
theorem B18618599 : Blo 1764083 18618599 := bstep (se 1 (by rfl) ⟨13963949, by rfl⟩ : syracuseStep 18618599 = 27927899) B27927899
theorem B2513273 : Blo 1764083 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B2513359 : Blo 1764083 2513359 := bstep (se 1 (by rfl) ⟨1885019, by rfl⟩ : syracuseStep 2513359 = 3770039) B3770039
theorem B2513387 : Blo 1764083 2513387 := bstep (se 1 (by rfl) ⟨1885040, by rfl⟩ : syracuseStep 2513387 = 3770081) B3770081
theorem B8935919 : Blo 1764083 8935919 := bstep (se 1 (by rfl) ⟨6701939, by rfl⟩ : syracuseStep 8935919 = 13403879) B13403879
theorem B3971879 : Blo 1764083 3971879 := bstep (se 1 (by rfl) ⟨2978909, by rfl⟩ : syracuseStep 3971879 = 5957819) B5957819
theorem B6699905 : Blo 1764083 6699905 := bstep (se 2 (by rfl) ⟨2512464, by rfl⟩ : syracuseStep 6699905 = 5024929) B5024929
theorem B8477723 : Blo 1764083 8477723 := bstep (se 1 (by rfl) ⟨6358292, by rfl⟩ : syracuseStep 8477723 = 12716585) B12716585
theorem B19078249 : Blo 1764083 19078249 := bstep (se 2 (by rfl) ⟨7154343, by rfl⟩ : syracuseStep 19078249 = 14308687) B14308687
theorem B148872473 : Blo 1764083 148872473 := bstep (se 2 (by rfl) ⟨55827177, by rfl⟩ : syracuseStep 148872473 = 111654355) B111654355
theorem B2121151 : Blo 1764083 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B19095203 : Blo 1764083 19095203 := bstep (se 1 (by rfl) ⟨14321402, by rfl⟩ : syracuseStep 19095203 = 28642805) B28642805
theorem B1884007 : Blo 1764083 1884007 := bstep (se 1 (by rfl) ⟨1413005, by rfl⟩ : syracuseStep 1884007 = 2826011) B2826011
theorem B3350393 : Blo 1764083 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B2646143 : Blo 1764083 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B45244655 : Blo 1764083 45244655 := bstep (se 1 (by rfl) ⟨33933491, by rfl⟩ : syracuseStep 45244655 = 67866983) B67866983
theorem B2646431 : Blo 1764083 2646431 := bstep (se 1 (by rfl) ⟨1984823, by rfl⟩ : syracuseStep 2646431 = 3969647) B3969647
theorem B3973535 : Blo 1764083 3973535 := bstep (se 1 (by rfl) ⟨2980151, by rfl⟩ : syracuseStep 3973535 = 5960303) B5960303
theorem B3351145 : Blo 1764083 3351145 := bstep (se 2 (by rfl) ⟨1256679, by rfl⟩ : syracuseStep 3351145 = 2513359) B2513359
theorem B25436861 : Blo 1764083 25436861 := bstep (se 3 (by rfl) ⟨4769411, by rfl⟩ : syracuseStep 25436861 = 9538823) B9538823
theorem B6702047 : Blo 1764083 6702047 := bstep (se 1 (by rfl) ⟨5026535, by rfl⟩ : syracuseStep 6702047 = 10053071) B10053071
theorem B6702061 : Blo 1764083 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B6702365 : Blo 1764083 6702365 := bstep (se 3 (by rfl) ⟨1256693, by rfl⟩ : syracuseStep 6702365 = 2513387) B2513387
theorem B7742891 : Blo 1764083 7742891 := bstep (se 1 (by rfl) ⟨5807168, by rfl⟩ : syracuseStep 7742891 = 11614337) B11614337
theorem B2647487 : Blo 1764083 2647487 := bstep (se 1 (by rfl) ⟨1985615, by rfl⟩ : syracuseStep 2647487 = 3971231) B3971231
theorem B25437665 : Blo 1764083 25437665 := bstep (se 2 (by rfl) ⟨9539124, by rfl⟩ : syracuseStep 25437665 = 19078249) B19078249
theorem B12412399 : Blo 1764083 12412399 := bstep (se 1 (by rfl) ⟨9309299, by rfl⟩ : syracuseStep 12412399 = 18618599) B18618599
theorem B5957279 : Blo 1764083 5957279 := bstep (se 1 (by rfl) ⟨4467959, by rfl⟩ : syracuseStep 5957279 = 8935919) B8935919
theorem B2647919 : Blo 1764083 2647919 := bstep (se 1 (by rfl) ⟨1985939, by rfl⟩ : syracuseStep 2647919 = 3971879) B3971879
theorem B2828201 : Blo 1764083 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B4466603 : Blo 1764083 4466603 := bstep (se 1 (by rfl) ⟨3349952, by rfl⟩ : syracuseStep 4466603 = 6699905) B6699905
theorem B2648831 : Blo 1764083 2648831 := bstep (se 1 (by rfl) ⟨1986623, by rfl⟩ : syracuseStep 2648831 = 3973247) B3973247
theorem B1764159 : Blo 1764083 1764159 := bstep (se 1 (by rfl) ⟨1323119, by rfl⟩ : syracuseStep 1764159 = 2646239) B2646239
theorem B1587973045 : Blo 1764083 1587973045 := bstep (se 5 (by rfl) ⟨74436236, by rfl⟩ : syracuseStep 1587973045 = 148872473) B148872473
theorem B1764351 : Blo 1764083 1764351 := bstep (se 1 (by rfl) ⟨1323263, by rfl⟩ : syracuseStep 1764351 = 2646527) B2646527
theorem B5958683 : Blo 1764083 5958683 := bstep (se 1 (by rfl) ⟨4469012, by rfl⟩ : syracuseStep 5958683 = 8938025) B8938025
theorem B1985647 : Blo 1764083 1985647 := bstep (se 1 (by rfl) ⟨1489235, by rfl⟩ : syracuseStep 1985647 = 2978471) B2978471
theorem B4467919 : Blo 1764083 4467919 := bstep (se 1 (by rfl) ⟨3350939, by rfl⟩ : syracuseStep 4467919 = 6701879) B6701879
theorem B4468223 : Blo 1764083 4468223 := bstep (se 1 (by rfl) ⟨3351167, by rfl⟩ : syracuseStep 4468223 = 6702335) B6702335
theorem B2977391 : Blo 1764083 2977391 := bstep (se 1 (by rfl) ⟨2233043, by rfl⟩ : syracuseStep 2977391 = 4466087) B4466087
theorem B5025863 : Blo 1764083 5025863 := bstep (se 1 (by rfl) ⟨3769397, by rfl⟩ : syracuseStep 5025863 = 7538795) B7538795
theorem B1765487 : Blo 1764083 1765487 := bstep (se 1 (by rfl) ⟨1324115, by rfl⟩ : syracuseStep 1765487 = 2648231) B2648231
theorem B1765627 : Blo 1764083 1765627 := bstep (se 1 (by rfl) ⟨1324220, by rfl⟩ : syracuseStep 1765627 = 2648441) B2648441
theorem B1765871 : Blo 1764083 1765871 := bstep (se 1 (by rfl) ⟨1324403, by rfl⟩ : syracuseStep 1765871 = 2648807) B2648807
theorem B1765999 : Blo 1764083 1765999 := bstep (se 1 (by rfl) ⟨1324499, by rfl⟩ : syracuseStep 1765999 = 2648999) B2648999
theorem B1766043 : Blo 1764083 1766043 := bstep (se 1 (by rfl) ⟨1324532, by rfl⟩ : syracuseStep 1766043 = 2649065) B2649065
theorem B2512009 : Blo 1764083 2512009 := bstep (se 2 (by rfl) ⟨942003, by rfl⟩ : syracuseStep 2512009 = 1884007) B1884007
theorem B2233595 : Blo 1764083 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B22607261 : Blo 1764083 22607261 := bstep (se 3 (by rfl) ⟨4238861, by rfl⟩ : syracuseStep 22607261 = 8477723) B8477723
theorem B7542553 : Blo 1764083 7542553 := bstep (se 2 (by rfl) ⟨2828457, by rfl⟩ : syracuseStep 7542553 = 5656915) B5656915
theorem B6699145 : Blo 1764083 6699145 := bstep (se 2 (by rfl) ⟨2512179, by rfl⟩ : syracuseStep 6699145 = 5024359) B5024359
theorem B18119051 : Blo 1764083 18119051 := bstep (se 1 (by rfl) ⟨13589288, by rfl⟩ : syracuseStep 18119051 = 27178577) B27178577
theorem B81484339 : Blo 1764083 81484339 := bstep (se 1 (by rfl) ⟨61113254, by rfl⟩ : syracuseStep 81484339 = 122226509) B122226509
theorem B10189567 : Blo 1764083 10189567 := bstep (se 1 (by rfl) ⟨7642175, by rfl⟩ : syracuseStep 10189567 = 15284351) B15284351
theorem B3972203 : Blo 1764083 3972203 := bstep (se 1 (by rfl) ⟨2979152, by rfl⟩ : syracuseStep 3972203 = 5958305) B5958305
theorem B12729905 : Blo 1764083 12729905 := bstep (se 2 (by rfl) ⟨4773714, by rfl⟩ : syracuseStep 12729905 = 9547429) B9547429
theorem B3972815 : Blo 1764083 3972815 := bstep (se 1 (by rfl) ⟨2979611, by rfl⟩ : syracuseStep 3972815 = 5959223) B5959223
theorem B12730135 : Blo 1764083 12730135 := bstep (se 1 (by rfl) ⟨9547601, by rfl⟩ : syracuseStep 12730135 = 19095203) B19095203
theorem B38158229 : Blo 1764083 38158229 := bstep (se 6 (by rfl) ⟨894333, by rfl⟩ : syracuseStep 38158229 = 1788667) B1788667
theorem B3350575 : Blo 1764083 3350575 := bstep (se 1 (by rfl) ⟨2512931, by rfl⟩ : syracuseStep 3350575 = 5025863) B5025863
theorem B30163103 : Blo 1764083 30163103 := bstep (se 1 (by rfl) ⟨22622327, by rfl⟩ : syracuseStep 30163103 = 45244655) B45244655
theorem B16957907 : Blo 1764083 16957907 := bstep (se 1 (by rfl) ⟨12718430, by rfl⟩ : syracuseStep 16957907 = 25436861) B25436861
theorem B5956253 : Blo 1764083 5956253 := bstep (se 3 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 5956253 = 2233595) B2233595
theorem B16958443 : Blo 1764083 16958443 := bstep (se 1 (by rfl) ⟨12718832, by rfl⟩ : syracuseStep 16958443 = 25437665) B25437665
theorem B2117297393 : Blo 1764083 2117297393 := bstep (se 2 (by rfl) ⟨793986522, by rfl⟩ : syracuseStep 2117297393 = 1587973045) B1587973045
theorem B2647529 : Blo 1764083 2647529 := bstep (se 2 (by rfl) ⟨992823, by rfl⟩ : syracuseStep 2647529 = 1985647) B1985647
theorem B5957225 : Blo 1764083 5957225 := bstep (se 2 (by rfl) ⟨2233959, by rfl⟩ : syracuseStep 5957225 = 4467919) B4467919
theorem B16549865 : Blo 1764083 16549865 := bstep (se 2 (by rfl) ⟨6206199, by rfl⟩ : syracuseStep 16549865 = 12412399) B12412399
theorem B2648135 : Blo 1764083 2648135 := bstep (se 1 (by rfl) ⟨1986101, by rfl⟩ : syracuseStep 2648135 = 3972203) B3972203
theorem B1984927 : Blo 1764083 1984927 := bstep (se 1 (by rfl) ⟨1488695, by rfl⟩ : syracuseStep 1984927 = 2977391) B2977391
theorem B2648543 : Blo 1764083 2648543 := bstep (se 1 (by rfl) ⟨1986407, by rfl⟩ : syracuseStep 2648543 = 3972815) B3972815
theorem B25438819 : Blo 1764083 25438819 := bstep (se 1 (by rfl) ⟨19079114, by rfl⟩ : syracuseStep 25438819 = 38158229) B38158229
theorem B1764095 : Blo 1764083 1764095 := bstep (se 1 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 1764095 = 2646143) B2646143
theorem B8932193 : Blo 1764083 8932193 := bstep (se 2 (by rfl) ⟨3349572, by rfl⟩ : syracuseStep 8932193 = 6699145) B6699145
theorem B1764287 : Blo 1764083 1764287 := bstep (se 1 (by rfl) ⟨1323215, by rfl⟩ : syracuseStep 1764287 = 2646431) B2646431
theorem B2649023 : Blo 1764083 2649023 := bstep (se 1 (by rfl) ⟨1986767, by rfl⟩ : syracuseStep 2649023 = 3973535) B3973535
theorem B4468031 : Blo 1764083 4468031 := bstep (se 1 (by rfl) ⟨3351023, by rfl⟩ : syracuseStep 4468031 = 6702047) B6702047
theorem B108645785 : Blo 1764083 108645785 := bstep (se 2 (by rfl) ⟨40742169, by rfl⟩ : syracuseStep 108645785 = 81484339) B81484339
theorem B4468193 : Blo 1764083 4468193 := bstep (se 2 (by rfl) ⟨1675572, by rfl⟩ : syracuseStep 4468193 = 3351145) B3351145
theorem B4468243 : Blo 1764083 4468243 := bstep (se 1 (by rfl) ⟨3351182, by rfl⟩ : syracuseStep 4468243 = 6702365) B6702365
theorem B1764991 : Blo 1764083 1764991 := bstep (se 1 (by rfl) ⟨1323743, by rfl⟩ : syracuseStep 1764991 = 2647487) B2647487
theorem B13586089 : Blo 1764083 13586089 := bstep (se 2 (by rfl) ⟨5094783, by rfl⟩ : syracuseStep 13586089 = 10189567) B10189567
theorem B20647709 : Blo 1764083 20647709 := bstep (se 3 (by rfl) ⟨3871445, by rfl⟩ : syracuseStep 20647709 = 7742891) B7742891
theorem B1765279 : Blo 1764083 1765279 := bstep (se 1 (by rfl) ⟨1323959, by rfl⟩ : syracuseStep 1765279 = 2647919) B2647919
theorem B2977735 : Blo 1764083 2977735 := bstep (se 1 (by rfl) ⟨2233301, by rfl⟩ : syracuseStep 2977735 = 4466603) B4466603
theorem B12079367 : Blo 1764083 12079367 := bstep (se 1 (by rfl) ⟨9059525, by rfl⟩ : syracuseStep 12079367 = 18119051) B18119051
theorem B30167477 : Blo 1764083 30167477 := bstep (se 5 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 30167477 = 2828201) B2828201
theorem B1765887 : Blo 1764083 1765887 := bstep (se 1 (by rfl) ⟨1324415, by rfl⟩ : syracuseStep 1765887 = 2648831) B2648831
theorem B2978815 : Blo 1764083 2978815 := bstep (se 1 (by rfl) ⟨2234111, by rfl⟩ : syracuseStep 2978815 = 4468223) B4468223
theorem B10056737 : Blo 1764083 10056737 := bstep (se 2 (by rfl) ⟨3771276, by rfl⟩ : syracuseStep 10056737 = 7542553) B7542553
theorem B15071507 : Blo 1764083 15071507 := bstep (se 1 (by rfl) ⟨11303630, by rfl⟩ : syracuseStep 15071507 = 22607261) B22607261
theorem B3971519 : Blo 1764083 3971519 := bstep (se 1 (by rfl) ⟨2978639, by rfl⟩ : syracuseStep 3971519 = 5957279) B5957279
theorem B8936081 : Blo 1764083 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B3349345 : Blo 1764083 3349345 := bstep (se 2 (by rfl) ⟨1256004, by rfl⟩ : syracuseStep 3349345 = 2512009) B2512009
theorem B3972455 : Blo 1764083 3972455 := bstep (se 1 (by rfl) ⟨2979341, by rfl⟩ : syracuseStep 3972455 = 5958683) B5958683
theorem B16973513 : Blo 1764083 16973513 := bstep (se 2 (by rfl) ⟨6365067, by rfl⟩ : syracuseStep 16973513 = 12730135) B12730135
theorem B8486603 : Blo 1764083 8486603 := bstep (se 1 (by rfl) ⟨6364952, by rfl⟩ : syracuseStep 8486603 = 12729905) B12729905
theorem B8052911 : Blo 1764083 8052911 := bstep (se 1 (by rfl) ⟨6039683, by rfl⟩ : syracuseStep 8052911 = 12079367) B12079367
theorem B20111651 : Blo 1764083 20111651 := bstep (se 1 (by rfl) ⟨15083738, by rfl⟩ : syracuseStep 20111651 = 30167477) B30167477
theorem B11305271 : Blo 1764083 11305271 := bstep (se 1 (by rfl) ⟨8478953, by rfl⟩ : syracuseStep 11305271 = 16957907) B16957907
theorem B2646569 : Blo 1764083 2646569 := bstep (se 2 (by rfl) ⟨992463, by rfl⟩ : syracuseStep 2646569 = 1984927) B1984927
theorem B1411531595 : Blo 1764083 1411531595 := bstep (se 1 (by rfl) ⟨1058648696, by rfl⟩ : syracuseStep 1411531595 = 2117297393) B2117297393
theorem B4465793 : Blo 1764083 4465793 := bstep (se 2 (by rfl) ⟨1674672, by rfl⟩ : syracuseStep 4465793 = 3349345) B3349345
theorem B22611257 : Blo 1764083 22611257 := bstep (se 2 (by rfl) ⟨8479221, by rfl⟩ : syracuseStep 22611257 = 16958443) B16958443
theorem B2647679 : Blo 1764083 2647679 := bstep (se 1 (by rfl) ⟨1985759, by rfl⟩ : syracuseStep 2647679 = 3971519) B3971519
theorem B5957387 : Blo 1764083 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B5957657 : Blo 1764083 5957657 := bstep (se 2 (by rfl) ⟨2234121, by rfl⟩ : syracuseStep 5957657 = 4468243) B4468243
theorem B18114785 : Blo 1764083 18114785 := bstep (se 2 (by rfl) ⟨6793044, by rfl⟩ : syracuseStep 18114785 = 13586089) B13586089
theorem B2648303 : Blo 1764083 2648303 := bstep (se 1 (by rfl) ⟨1986227, by rfl⟩ : syracuseStep 2648303 = 3972455) B3972455
theorem B11315675 : Blo 1764083 11315675 := bstep (se 1 (by rfl) ⟨8486756, by rfl⟩ : syracuseStep 11315675 = 16973513) B16973513
theorem B13765139 : Blo 1764083 13765139 := bstep (se 1 (by rfl) ⟨10323854, by rfl⟩ : syracuseStep 13765139 = 20647709) B20647709
theorem B4467433 : Blo 1764083 4467433 := bstep (se 2 (by rfl) ⟨1675287, by rfl⟩ : syracuseStep 4467433 = 3350575) B3350575
theorem B6704491 : Blo 1764083 6704491 := bstep (se 1 (by rfl) ⟨5028368, by rfl⟩ : syracuseStep 6704491 = 10056737) B10056737
theorem B33918425 : Blo 1764083 33918425 := bstep (se 2 (by rfl) ⟨12719409, by rfl⟩ : syracuseStep 33918425 = 25438819) B25438819
theorem B1765019 : Blo 1764083 1765019 := bstep (se 1 (by rfl) ⟨1323764, by rfl⟩ : syracuseStep 1765019 = 2647529) B2647529
theorem B1765423 : Blo 1764083 1765423 := bstep (se 1 (by rfl) ⟨1324067, by rfl⟩ : syracuseStep 1765423 = 2648135) B2648135
theorem B10047671 : Blo 1764083 10047671 := bstep (se 1 (by rfl) ⟨7535753, by rfl⟩ : syracuseStep 10047671 = 15071507) B15071507
theorem B1765695 : Blo 1764083 1765695 := bstep (se 1 (by rfl) ⟨1324271, by rfl⟩ : syracuseStep 1765695 = 2648543) B2648543
theorem B1766015 : Blo 1764083 1766015 := bstep (se 1 (by rfl) ⟨1324511, by rfl⟩ : syracuseStep 1766015 = 2649023) B2649023
theorem B2978687 : Blo 1764083 2978687 := bstep (se 1 (by rfl) ⟨2234015, by rfl⟩ : syracuseStep 2978687 = 4468031) B4468031
theorem B72430523 : Blo 1764083 72430523 := bstep (se 1 (by rfl) ⟨54322892, by rfl⟩ : syracuseStep 72430523 = 108645785) B108645785
theorem B2978795 : Blo 1764083 2978795 := bstep (se 1 (by rfl) ⟨2234096, by rfl⟩ : syracuseStep 2978795 = 4468193) B4468193
theorem B5657735 : Blo 1764083 5657735 := bstep (se 1 (by rfl) ⟨4243301, by rfl⟩ : syracuseStep 5657735 = 8486603) B8486603
theorem B3970313 : Blo 1764083 3970313 := bstep (se 2 (by rfl) ⟨1488867, by rfl⟩ : syracuseStep 3970313 = 2977735) B2977735
theorem B20108735 : Blo 1764083 20108735 := bstep (se 1 (by rfl) ⟨15081551, by rfl⟩ : syracuseStep 20108735 = 30163103) B30163103
theorem B3970835 : Blo 1764083 3970835 := bstep (se 1 (by rfl) ⟨2978126, by rfl⟩ : syracuseStep 3970835 = 5956253) B5956253
theorem B3971483 : Blo 1764083 3971483 := bstep (se 1 (by rfl) ⟨2978612, by rfl⟩ : syracuseStep 3971483 = 5957225) B5957225
theorem B11033243 : Blo 1764083 11033243 := bstep (se 1 (by rfl) ⟨8274932, by rfl⟩ : syracuseStep 11033243 = 16549865) B16549865
theorem B3971753 : Blo 1764083 3971753 := bstep (se 2 (by rfl) ⟨1489407, by rfl⟩ : syracuseStep 3971753 = 2978815) B2978815
theorem B5954795 : Blo 1764083 5954795 := bstep (se 1 (by rfl) ⟨4466096, by rfl⟩ : syracuseStep 5954795 = 8932193) B8932193
theorem B7536847 : Blo 1764083 7536847 := bstep (se 1 (by rfl) ⟨5652635, by rfl⟩ : syracuseStep 7536847 = 11305271) B11305271
theorem B2646875 : Blo 1764083 2646875 := bstep (se 1 (by rfl) ⟨1985156, by rfl⟩ : syracuseStep 2646875 = 3970313) B3970313
theorem B15074171 : Blo 1764083 15074171 := bstep (se 1 (by rfl) ⟨11305628, by rfl⟩ : syracuseStep 15074171 = 22611257) B22611257
theorem B5956577 : Blo 1764083 5956577 := bstep (se 2 (by rfl) ⟨2233716, by rfl⟩ : syracuseStep 5956577 = 4467433) B4467433
theorem B2647223 : Blo 1764083 2647223 := bstep (se 1 (by rfl) ⟨1985417, by rfl⟩ : syracuseStep 2647223 = 3970835) B3970835
theorem B12076523 : Blo 1764083 12076523 := bstep (se 1 (by rfl) ⟨9057392, by rfl⟩ : syracuseStep 12076523 = 18114785) B18114785
theorem B2647655 : Blo 1764083 2647655 := bstep (se 1 (by rfl) ⟨1985741, by rfl⟩ : syracuseStep 2647655 = 3971483) B3971483
theorem B9176759 : Blo 1764083 9176759 := bstep (se 1 (by rfl) ⟨6882569, by rfl⟩ : syracuseStep 9176759 = 13765139) B13765139
theorem B2647835 : Blo 1764083 2647835 := bstep (se 1 (by rfl) ⟨1985876, by rfl⟩ : syracuseStep 2647835 = 3971753) B3971753
theorem B8939321 : Blo 1764083 8939321 := bstep (se 2 (by rfl) ⟨3352245, by rfl⟩ : syracuseStep 8939321 = 6704491) B6704491
theorem B22612283 : Blo 1764083 22612283 := bstep (se 1 (by rfl) ⟨16959212, by rfl⟩ : syracuseStep 22612283 = 33918425) B33918425
theorem B5368607 : Blo 1764083 5368607 := bstep (se 1 (by rfl) ⟨4026455, by rfl⟩ : syracuseStep 5368607 = 8052911) B8052911
theorem B1764379 : Blo 1764083 1764379 := bstep (se 1 (by rfl) ⟨1323284, by rfl⟩ : syracuseStep 1764379 = 2646569) B2646569
theorem B1985791 : Blo 1764083 1985791 := bstep (se 1 (by rfl) ⟨1489343, by rfl⟩ : syracuseStep 1985791 = 2978687) B2978687
theorem B48287015 : Blo 1764083 48287015 := bstep (se 1 (by rfl) ⟨36215261, by rfl⟩ : syracuseStep 48287015 = 72430523) B72430523
theorem B1985863 : Blo 1764083 1985863 := bstep (se 1 (by rfl) ⟨1489397, by rfl⟩ : syracuseStep 1985863 = 2978795) B2978795
theorem B2977195 : Blo 1764083 2977195 := bstep (se 1 (by rfl) ⟨2232896, by rfl⟩ : syracuseStep 2977195 = 4465793) B4465793
theorem B13405823 : Blo 1764083 13405823 := bstep (se 1 (by rfl) ⟨10054367, by rfl⟩ : syracuseStep 13405823 = 20108735) B20108735
theorem B1765119 : Blo 1764083 1765119 := bstep (se 1 (by rfl) ⟨1323839, by rfl⟩ : syracuseStep 1765119 = 2647679) B2647679
theorem B1765535 : Blo 1764083 1765535 := bstep (se 1 (by rfl) ⟨1324151, by rfl⟩ : syracuseStep 1765535 = 2648303) B2648303
theorem B3969863 : Blo 1764083 3969863 := bstep (se 1 (by rfl) ⟨2977397, by rfl⟩ : syracuseStep 3969863 = 5954795) B5954795
theorem B6698447 : Blo 1764083 6698447 := bstep (se 1 (by rfl) ⟨5023835, by rfl⟩ : syracuseStep 6698447 = 10047671) B10047671
theorem B13407767 : Blo 1764083 13407767 := bstep (se 1 (by rfl) ⟨10055825, by rfl⟩ : syracuseStep 13407767 = 20111651) B20111651
theorem B15087293 : Blo 1764083 15087293 := bstep (se 3 (by rfl) ⟨2828867, by rfl⟩ : syracuseStep 15087293 = 5657735) B5657735
theorem B941021063 : Blo 1764083 941021063 := bstep (se 1 (by rfl) ⟨705765797, by rfl⟩ : syracuseStep 941021063 = 1411531595) B1411531595
theorem B3971591 : Blo 1764083 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B3971771 : Blo 1764083 3971771 := bstep (se 1 (by rfl) ⟨2978828, by rfl⟩ : syracuseStep 3971771 = 5957657) B5957657
theorem B7543783 : Blo 1764083 7543783 := bstep (se 1 (by rfl) ⟨5657837, by rfl⟩ : syracuseStep 7543783 = 11315675) B11315675
theorem B7355495 : Blo 1764083 7355495 := bstep (se 1 (by rfl) ⟨5516621, by rfl⟩ : syracuseStep 7355495 = 11033243) B11033243
theorem B2646575 : Blo 1764083 2646575 := bstep (se 1 (by rfl) ⟨1984931, by rfl⟩ : syracuseStep 2646575 = 3969863) B3969863
theorem B4465631 : Blo 1764083 4465631 := bstep (se 1 (by rfl) ⟨3349223, by rfl⟩ : syracuseStep 4465631 = 6698447) B6698447
theorem B8938511 : Blo 1764083 8938511 := bstep (se 1 (by rfl) ⟨6703883, by rfl⟩ : syracuseStep 8938511 = 13407767) B13407767
theorem B15074855 : Blo 1764083 15074855 := bstep (se 1 (by rfl) ⟨11306141, by rfl⟩ : syracuseStep 15074855 = 22612283) B22612283
theorem B2647721 : Blo 1764083 2647721 := bstep (se 2 (by rfl) ⟨992895, by rfl⟩ : syracuseStep 2647721 = 1985791) B1985791
theorem B2647727 : Blo 1764083 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B2647817 : Blo 1764083 2647817 := bstep (se 2 (by rfl) ⟨992931, by rfl⟩ : syracuseStep 2647817 = 1985863) B1985863
theorem B2647847 : Blo 1764083 2647847 := bstep (se 1 (by rfl) ⟨1985885, by rfl⟩ : syracuseStep 2647847 = 3971771) B3971771
theorem B19614653 : Blo 1764083 19614653 := bstep (se 3 (by rfl) ⟨3677747, by rfl⟩ : syracuseStep 19614653 = 7355495) B7355495
theorem B1764583 : Blo 1764083 1764583 := bstep (se 1 (by rfl) ⟨1323437, by rfl⟩ : syracuseStep 1764583 = 2646875) B2646875
theorem B1764815 : Blo 1764083 1764815 := bstep (se 1 (by rfl) ⟨1323611, by rfl⟩ : syracuseStep 1764815 = 2647223) B2647223
theorem B1765103 : Blo 1764083 1765103 := bstep (se 1 (by rfl) ⟨1323827, by rfl⟩ : syracuseStep 1765103 = 2647655) B2647655
theorem B1765223 : Blo 1764083 1765223 := bstep (se 1 (by rfl) ⟨1323917, by rfl⟩ : syracuseStep 1765223 = 2647835) B2647835
theorem B5959547 : Blo 1764083 5959547 := bstep (se 1 (by rfl) ⟨4469660, by rfl⟩ : syracuseStep 5959547 = 8939321) B8939321
theorem B627347375 : Blo 1764083 627347375 := bstep (se 1 (by rfl) ⟨470510531, by rfl⟩ : syracuseStep 627347375 = 941021063) B941021063
theorem B3969593 : Blo 1764083 3969593 := bstep (se 2 (by rfl) ⟨1488597, by rfl⟩ : syracuseStep 3969593 = 2977195) B2977195
theorem B32191343 : Blo 1764083 32191343 := bstep (se 1 (by rfl) ⟨24143507, by rfl⟩ : syracuseStep 32191343 = 48287015) B48287015
theorem B10049129 : Blo 1764083 10049129 := bstep (se 2 (by rfl) ⟨3768423, by rfl⟩ : syracuseStep 10049129 = 7536847) B7536847
theorem B10049447 : Blo 1764083 10049447 := bstep (se 1 (by rfl) ⟨7537085, by rfl⟩ : syracuseStep 10049447 = 15074171) B15074171
theorem B3971051 : Blo 1764083 3971051 := bstep (se 1 (by rfl) ⟨2978288, by rfl⟩ : syracuseStep 3971051 = 5956577) B5956577
theorem B8051015 : Blo 1764083 8051015 := bstep (se 1 (by rfl) ⟨6038261, by rfl⟩ : syracuseStep 8051015 = 12076523) B12076523
theorem B6117839 : Blo 1764083 6117839 := bstep (se 1 (by rfl) ⟨4588379, by rfl⟩ : syracuseStep 6117839 = 9176759) B9176759
theorem B10058195 : Blo 1764083 10058195 := bstep (se 1 (by rfl) ⟨7543646, by rfl⟩ : syracuseStep 10058195 = 15087293) B15087293
theorem B10058377 : Blo 1764083 10058377 := bstep (se 2 (by rfl) ⟨3771891, by rfl⟩ : syracuseStep 10058377 = 7543783) B7543783
theorem B3579071 : Blo 1764083 3579071 := bstep (se 1 (by rfl) ⟨2684303, by rfl⟩ : syracuseStep 3579071 = 5368607) B5368607
theorem B8937215 : Blo 1764083 8937215 := bstep (se 1 (by rfl) ⟨6702911, by rfl⟩ : syracuseStep 8937215 = 13405823) B13405823
theorem B2646395 : Blo 1764083 2646395 := bstep (se 1 (by rfl) ⟨1984796, by rfl⟩ : syracuseStep 2646395 = 3969593) B3969593
theorem B9544189 : Blo 1764083 9544189 := bstep (se 3 (by rfl) ⟨1789535, by rfl⟩ : syracuseStep 9544189 = 3579071) B3579071
theorem B13411169 : Blo 1764083 13411169 := bstep (se 2 (by rfl) ⟨5029188, by rfl⟩ : syracuseStep 13411169 = 10058377) B10058377
theorem B2647367 : Blo 1764083 2647367 := bstep (se 1 (by rfl) ⟨1985525, by rfl⟩ : syracuseStep 2647367 = 3971051) B3971051
theorem B5367343 : Blo 1764083 5367343 := bstep (se 1 (by rfl) ⟨4025507, by rfl⟩ : syracuseStep 5367343 = 8051015) B8051015
theorem B13076435 : Blo 1764083 13076435 := bstep (se 1 (by rfl) ⟨9807326, by rfl⟩ : syracuseStep 13076435 = 19614653) B19614653
theorem B5958143 : Blo 1764083 5958143 := bstep (se 1 (by rfl) ⟨4468607, by rfl⟩ : syracuseStep 5958143 = 8937215) B8937215
theorem B1764383 : Blo 1764083 1764383 := bstep (se 1 (by rfl) ⟨1323287, by rfl⟩ : syracuseStep 1764383 = 2646575) B2646575
theorem B2977087 : Blo 1764083 2977087 := bstep (se 1 (by rfl) ⟨2232815, by rfl⟩ : syracuseStep 2977087 = 4465631) B4465631
theorem B5959007 : Blo 1764083 5959007 := bstep (se 1 (by rfl) ⟨4469255, by rfl⟩ : syracuseStep 5959007 = 8938511) B8938511
theorem B1765147 : Blo 1764083 1765147 := bstep (se 1 (by rfl) ⟨1323860, by rfl⟩ : syracuseStep 1765147 = 2647721) B2647721
theorem B1765151 : Blo 1764083 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B1765211 : Blo 1764083 1765211 := bstep (se 1 (by rfl) ⟨1323908, by rfl⟩ : syracuseStep 1765211 = 2647817) B2647817
theorem B1765231 : Blo 1764083 1765231 := bstep (se 1 (by rfl) ⟨1323923, by rfl⟩ : syracuseStep 1765231 = 2647847) B2647847
theorem B6705463 : Blo 1764083 6705463 := bstep (se 1 (by rfl) ⟨5029097, by rfl⟩ : syracuseStep 6705463 = 10058195) B10058195
theorem B418231583 : Blo 1764083 418231583 := bstep (se 1 (by rfl) ⟨313673687, by rfl⟩ : syracuseStep 418231583 = 627347375) B627347375
theorem B21460895 : Blo 1764083 21460895 := bstep (se 1 (by rfl) ⟨16095671, by rfl⟩ : syracuseStep 21460895 = 32191343) B32191343
theorem B10049903 : Blo 1764083 10049903 := bstep (se 1 (by rfl) ⟨7537427, by rfl⟩ : syracuseStep 10049903 = 15074855) B15074855
theorem B6699419 : Blo 1764083 6699419 := bstep (se 1 (by rfl) ⟨5024564, by rfl⟩ : syracuseStep 6699419 = 10049129) B10049129
theorem B6699631 : Blo 1764083 6699631 := bstep (se 1 (by rfl) ⟨5024723, by rfl⟩ : syracuseStep 6699631 = 10049447) B10049447
theorem B4078559 : Blo 1764083 4078559 := bstep (se 1 (by rfl) ⟨3058919, by rfl⟩ : syracuseStep 4078559 = 6117839) B6117839
theorem B3973031 : Blo 1764083 3973031 := bstep (se 1 (by rfl) ⟨2979773, by rfl⟩ : syracuseStep 3973031 = 5959547) B5959547
theorem B4466279 : Blo 1764083 4466279 := bstep (se 1 (by rfl) ⟨3349709, by rfl⟩ : syracuseStep 4466279 = 6699419) B6699419
theorem B2648687 : Blo 1764083 2648687 := bstep (se 1 (by rfl) ⟨1986515, by rfl⟩ : syracuseStep 2648687 = 3973031) B3973031
theorem B1764263 : Blo 1764083 1764263 := bstep (se 1 (by rfl) ⟨1323197, by rfl⟩ : syracuseStep 1764263 = 2646395) B2646395
theorem B8940617 : Blo 1764083 8940617 := bstep (se 2 (by rfl) ⟨3352731, by rfl⟩ : syracuseStep 8940617 = 6705463) B6705463
theorem B8940779 : Blo 1764083 8940779 := bstep (se 1 (by rfl) ⟨6705584, by rfl⟩ : syracuseStep 8940779 = 13411169) B13411169
theorem B12725585 : Blo 1764083 12725585 := bstep (se 2 (by rfl) ⟨4772094, by rfl⟩ : syracuseStep 12725585 = 9544189) B9544189
theorem B8932841 : Blo 1764083 8932841 := bstep (se 2 (by rfl) ⟨3349815, by rfl⟩ : syracuseStep 8932841 = 6699631) B6699631
theorem B1764911 : Blo 1764083 1764911 := bstep (se 1 (by rfl) ⟨1323683, by rfl⟩ : syracuseStep 1764911 = 2647367) B2647367
theorem B14307263 : Blo 1764083 14307263 := bstep (se 1 (by rfl) ⟨10730447, by rfl⟩ : syracuseStep 14307263 = 21460895) B21460895
theorem B3969449 : Blo 1764083 3969449 := bstep (se 2 (by rfl) ⟨1488543, by rfl⟩ : syracuseStep 3969449 = 2977087) B2977087
theorem B7156457 : Blo 1764083 7156457 := bstep (se 2 (by rfl) ⟨2683671, by rfl⟩ : syracuseStep 7156457 = 5367343) B5367343
theorem B34870493 : Blo 1764083 34870493 := bstep (se 3 (by rfl) ⟨6538217, by rfl⟩ : syracuseStep 34870493 = 13076435) B13076435
theorem B10876157 : Blo 1764083 10876157 := bstep (se 3 (by rfl) ⟨2039279, by rfl⟩ : syracuseStep 10876157 = 4078559) B4078559
theorem B278821055 : Blo 1764083 278821055 := bstep (se 1 (by rfl) ⟨209115791, by rfl⟩ : syracuseStep 278821055 = 418231583) B418231583
theorem B6699935 : Blo 1764083 6699935 := bstep (se 1 (by rfl) ⟨5024951, by rfl⟩ : syracuseStep 6699935 = 10049903) B10049903
theorem B3972095 : Blo 1764083 3972095 := bstep (se 1 (by rfl) ⟨2979071, by rfl⟩ : syracuseStep 3972095 = 5958143) B5958143
theorem B3972671 : Blo 1764083 3972671 := bstep (se 1 (by rfl) ⟨2979503, by rfl⟩ : syracuseStep 3972671 = 5959007) B5959007
theorem B2646299 : Blo 1764083 2646299 := bstep (se 1 (by rfl) ⟨1984724, by rfl⟩ : syracuseStep 2646299 = 3969449) B3969449
theorem B7250771 : Blo 1764083 7250771 := bstep (se 1 (by rfl) ⟨5438078, by rfl⟩ : syracuseStep 7250771 = 10876157) B10876157
theorem B4466623 : Blo 1764083 4466623 := bstep (se 1 (by rfl) ⟨3349967, by rfl⟩ : syracuseStep 4466623 = 6699935) B6699935
theorem B2648063 : Blo 1764083 2648063 := bstep (se 1 (by rfl) ⟨1986047, by rfl⟩ : syracuseStep 2648063 = 3972095) B3972095
theorem B2648447 : Blo 1764083 2648447 := bstep (se 1 (by rfl) ⟨1986335, by rfl⟩ : syracuseStep 2648447 = 3972671) B3972671
theorem B9538175 : Blo 1764083 9538175 := bstep (se 1 (by rfl) ⟨7153631, by rfl⟩ : syracuseStep 9538175 = 14307263) B14307263
theorem B4770971 : Blo 1764083 4770971 := bstep (se 1 (by rfl) ⟨3578228, by rfl⟩ : syracuseStep 4770971 = 7156457) B7156457
theorem B2977519 : Blo 1764083 2977519 := bstep (se 1 (by rfl) ⟨2233139, by rfl⟩ : syracuseStep 2977519 = 4466279) B4466279
theorem B185880703 : Blo 1764083 185880703 := bstep (se 1 (by rfl) ⟨139410527, by rfl⟩ : syracuseStep 185880703 = 278821055) B278821055
theorem B1765791 : Blo 1764083 1765791 := bstep (se 1 (by rfl) ⟨1324343, by rfl⟩ : syracuseStep 1765791 = 2648687) B2648687
theorem B5960411 : Blo 1764083 5960411 := bstep (se 1 (by rfl) ⟨4470308, by rfl⟩ : syracuseStep 5960411 = 8940617) B8940617
theorem B5960519 : Blo 1764083 5960519 := bstep (se 1 (by rfl) ⟨4470389, by rfl⟩ : syracuseStep 5960519 = 8940779) B8940779
theorem B8483723 : Blo 1764083 8483723 := bstep (se 1 (by rfl) ⟨6362792, by rfl⟩ : syracuseStep 8483723 = 12725585) B12725585
theorem B23246995 : Blo 1764083 23246995 := bstep (se 1 (by rfl) ⟨17435246, by rfl⟩ : syracuseStep 23246995 = 34870493) B34870493
theorem B5955227 : Blo 1764083 5955227 := bstep (se 1 (by rfl) ⟨4466420, by rfl⟩ : syracuseStep 5955227 = 8932841) B8932841
theorem B247840937 : Blo 1764083 247840937 := bstep (se 2 (by rfl) ⟨92940351, by rfl⟩ : syracuseStep 247840937 = 185880703) B185880703
theorem B3973607 : Blo 1764083 3973607 := bstep (se 1 (by rfl) ⟨2980205, by rfl⟩ : syracuseStep 3973607 = 5960411) B5960411
theorem B3973679 : Blo 1764083 3973679 := bstep (se 1 (by rfl) ⟨2980259, by rfl⟩ : syracuseStep 3973679 = 5960519) B5960519
theorem B4833847 : Blo 1764083 4833847 := bstep (se 1 (by rfl) ⟨3625385, by rfl⟩ : syracuseStep 4833847 = 7250771) B7250771
theorem B6358783 : Blo 1764083 6358783 := bstep (se 1 (by rfl) ⟨4769087, by rfl⟩ : syracuseStep 6358783 = 9538175) B9538175
theorem B3180647 : Blo 1764083 3180647 := bstep (se 1 (by rfl) ⟨2385485, by rfl⟩ : syracuseStep 3180647 = 4770971) B4770971
theorem B1764199 : Blo 1764083 1764199 := bstep (se 1 (by rfl) ⟨1323149, by rfl⟩ : syracuseStep 1764199 = 2646299) B2646299
theorem B5655815 : Blo 1764083 5655815 := bstep (se 1 (by rfl) ⟨4241861, by rfl⟩ : syracuseStep 5655815 = 8483723) B8483723
theorem B1765375 : Blo 1764083 1765375 := bstep (se 1 (by rfl) ⟨1324031, by rfl⟩ : syracuseStep 1765375 = 2648063) B2648063
theorem B1765631 : Blo 1764083 1765631 := bstep (se 1 (by rfl) ⟨1324223, by rfl⟩ : syracuseStep 1765631 = 2648447) B2648447
theorem B3970025 : Blo 1764083 3970025 := bstep (se 2 (by rfl) ⟨1488759, by rfl⟩ : syracuseStep 3970025 = 2977519) B2977519
theorem B3970151 : Blo 1764083 3970151 := bstep (se 1 (by rfl) ⟨2977613, by rfl⟩ : syracuseStep 3970151 = 5955227) B5955227
theorem B30995993 : Blo 1764083 30995993 := bstep (se 2 (by rfl) ⟨11623497, by rfl⟩ : syracuseStep 30995993 = 23246995) B23246995
theorem B5955497 : Blo 1764083 5955497 := bstep (se 2 (by rfl) ⟨2233311, by rfl⟩ : syracuseStep 5955497 = 4466623) B4466623
theorem B2646683 : Blo 1764083 2646683 := bstep (se 1 (by rfl) ⟨1985012, by rfl⟩ : syracuseStep 2646683 = 3970025) B3970025
theorem B2646767 : Blo 1764083 2646767 := bstep (se 1 (by rfl) ⟨1985075, by rfl⟩ : syracuseStep 2646767 = 3970151) B3970151
theorem B3770543 : Blo 1764083 3770543 := bstep (se 1 (by rfl) ⟨2827907, by rfl⟩ : syracuseStep 3770543 = 5655815) B5655815
theorem B165227291 : Blo 1764083 165227291 := bstep (se 1 (by rfl) ⟨123920468, by rfl⟩ : syracuseStep 165227291 = 247840937) B247840937
theorem B2649071 : Blo 1764083 2649071 := bstep (se 1 (by rfl) ⟨1986803, by rfl⟩ : syracuseStep 2649071 = 3973607) B3973607
theorem B2649119 : Blo 1764083 2649119 := bstep (se 1 (by rfl) ⟨1986839, by rfl⟩ : syracuseStep 2649119 = 3973679) B3973679
theorem B20663995 : Blo 1764083 20663995 := bstep (se 1 (by rfl) ⟨15497996, by rfl⟩ : syracuseStep 20663995 = 30995993) B30995993
theorem B3970331 : Blo 1764083 3970331 := bstep (se 1 (by rfl) ⟨2977748, by rfl⟩ : syracuseStep 3970331 = 5955497) B5955497
theorem B6445129 : Blo 1764083 6445129 := bstep (se 2 (by rfl) ⟨2416923, by rfl⟩ : syracuseStep 6445129 = 4833847) B4833847
theorem B2120431 : Blo 1764083 2120431 := bstep (se 1 (by rfl) ⟨1590323, by rfl⟩ : syracuseStep 2120431 = 3180647) B3180647
theorem B8478377 : Blo 1764083 8478377 := bstep (se 2 (by rfl) ⟨3179391, by rfl⟩ : syracuseStep 8478377 = 6358783) B6358783
theorem B8593505 : Blo 1764083 8593505 := bstep (se 2 (by rfl) ⟨3222564, by rfl⟩ : syracuseStep 8593505 = 6445129) B6445129
theorem B2646887 : Blo 1764083 2646887 := bstep (se 1 (by rfl) ⟨1985165, by rfl⟩ : syracuseStep 2646887 = 3970331) B3970331
theorem B2827241 : Blo 1764083 2827241 := bstep (se 2 (by rfl) ⟨1060215, by rfl⟩ : syracuseStep 2827241 = 2120431) B2120431
theorem B110151527 : Blo 1764083 110151527 := bstep (se 1 (by rfl) ⟨82613645, by rfl⟩ : syracuseStep 110151527 = 165227291) B165227291
theorem B27551993 : Blo 1764083 27551993 := bstep (se 2 (by rfl) ⟨10331997, by rfl⟩ : syracuseStep 27551993 = 20663995) B20663995
theorem B1764455 : Blo 1764083 1764455 := bstep (se 1 (by rfl) ⟨1323341, by rfl⟩ : syracuseStep 1764455 = 2646683) B2646683
theorem B1764511 : Blo 1764083 1764511 := bstep (se 1 (by rfl) ⟨1323383, by rfl⟩ : syracuseStep 1764511 = 2646767) B2646767
theorem B1766047 : Blo 1764083 1766047 := bstep (se 1 (by rfl) ⟨1324535, by rfl⟩ : syracuseStep 1766047 = 2649071) B2649071
theorem B1766079 : Blo 1764083 1766079 := bstep (se 1 (by rfl) ⟨1324559, by rfl⟩ : syracuseStep 1766079 = 2649119) B2649119
theorem B2513695 : Blo 1764083 2513695 := bstep (se 1 (by rfl) ⟨1885271, by rfl⟩ : syracuseStep 2513695 = 3770543) B3770543
theorem B5652251 : Blo 1764083 5652251 := bstep (se 1 (by rfl) ⟨4239188, by rfl⟩ : syracuseStep 5652251 = 8478377) B8478377
theorem B1884827 : Blo 1764083 1884827 := bstep (se 1 (by rfl) ⟨1413620, by rfl⟩ : syracuseStep 1884827 = 2827241) B2827241
theorem B3351593 : Blo 1764083 3351593 := bstep (se 2 (by rfl) ⟨1256847, by rfl⟩ : syracuseStep 3351593 = 2513695) B2513695
theorem B5729003 : Blo 1764083 5729003 := bstep (se 1 (by rfl) ⟨4296752, by rfl⟩ : syracuseStep 5729003 = 8593505) B8593505
theorem B1764591 : Blo 1764083 1764591 := bstep (se 1 (by rfl) ⟨1323443, by rfl⟩ : syracuseStep 1764591 = 2646887) B2646887
theorem B1174949621 : Blo 1764083 1174949621 := bstep (se 5 (by rfl) ⟨55075763, by rfl⟩ : syracuseStep 1174949621 = 110151527) B110151527
theorem B73471981 : Blo 1764083 73471981 := bstep (se 3 (by rfl) ⟨13775996, by rfl⟩ : syracuseStep 73471981 = 27551993) B27551993
theorem B3768167 : Blo 1764083 3768167 := bstep (se 1 (by rfl) ⟨2826125, by rfl⟩ : syracuseStep 3768167 = 5652251) B5652251
theorem B3819335 : Blo 1764083 3819335 := bstep (se 1 (by rfl) ⟨2864501, by rfl⟩ : syracuseStep 3819335 = 5729003) B5729003
theorem B97962641 : Blo 1764083 97962641 := bstep (se 2 (by rfl) ⟨36735990, by rfl⟩ : syracuseStep 97962641 = 73471981) B73471981
theorem B5026205 : Blo 1764083 5026205 := bstep (se 3 (by rfl) ⟨942413, by rfl⟩ : syracuseStep 5026205 = 1884827) B1884827
theorem B10048445 : Blo 1764083 10048445 := bstep (se 3 (by rfl) ⟨1884083, by rfl⟩ : syracuseStep 10048445 = 3768167) B3768167
theorem B783299747 : Blo 1764083 783299747 := bstep (se 1 (by rfl) ⟨587474810, by rfl⟩ : syracuseStep 783299747 = 1174949621) B1174949621
theorem B2234395 : Blo 1764083 2234395 := bstep (se 1 (by rfl) ⟨1675796, by rfl⟩ : syracuseStep 2234395 = 3351593) B3351593
theorem B3350803 : Blo 1764083 3350803 := bstep (se 1 (by rfl) ⟨2513102, by rfl⟩ : syracuseStep 3350803 = 5026205) B5026205
theorem B40739573 : Blo 1764083 40739573 := bstep (se 5 (by rfl) ⟨1909667, by rfl⟩ : syracuseStep 40739573 = 3819335) B3819335
theorem B522199831 : Blo 1764083 522199831 := bstep (se 1 (by rfl) ⟨391649873, by rfl⟩ : syracuseStep 522199831 = 783299747) B783299747
theorem B65308427 : Blo 1764083 65308427 := bstep (se 1 (by rfl) ⟨48981320, by rfl⟩ : syracuseStep 65308427 = 97962641) B97962641
theorem B2979193 : Blo 1764083 2979193 := bstep (se 2 (by rfl) ⟨1117197, by rfl⟩ : syracuseStep 2979193 = 2234395) B2234395
theorem B6698963 : Blo 1764083 6698963 := bstep (se 1 (by rfl) ⟨5024222, by rfl⟩ : syracuseStep 6698963 = 10048445) B10048445
theorem B4465975 : Blo 1764083 4465975 := bstep (se 1 (by rfl) ⟨3349481, by rfl⟩ : syracuseStep 4465975 = 6698963) B6698963
theorem B4467737 : Blo 1764083 4467737 := bstep (se 2 (by rfl) ⟨1675401, by rfl⟩ : syracuseStep 4467737 = 3350803) B3350803
theorem B27159715 : Blo 1764083 27159715 := bstep (se 1 (by rfl) ⟨20369786, by rfl⟩ : syracuseStep 27159715 = 40739573) B40739573
theorem B696266441 : Blo 1764083 696266441 := bstep (se 2 (by rfl) ⟨261099915, by rfl⟩ : syracuseStep 696266441 = 522199831) B522199831
theorem B43538951 : Blo 1764083 43538951 := bstep (se 1 (by rfl) ⟨32654213, by rfl⟩ : syracuseStep 43538951 = 65308427) B65308427
theorem B3972257 : Blo 1764083 3972257 := bstep (se 2 (by rfl) ⟨1489596, by rfl⟩ : syracuseStep 3972257 = 2979193) B2979193
theorem B144851813 : Blo 1764083 144851813 := bstep (se 4 (by rfl) ⟨13579857, by rfl⟩ : syracuseStep 144851813 = 27159715) B27159715
theorem B29025967 : Blo 1764083 29025967 := bstep (se 1 (by rfl) ⟨21769475, by rfl⟩ : syracuseStep 29025967 = 43538951) B43538951
theorem B2648171 : Blo 1764083 2648171 := bstep (se 1 (by rfl) ⟨1986128, by rfl⟩ : syracuseStep 2648171 = 3972257) B3972257
theorem B464177627 : Blo 1764083 464177627 := bstep (se 1 (by rfl) ⟨348133220, by rfl⟩ : syracuseStep 464177627 = 696266441) B696266441
theorem B2978491 : Blo 1764083 2978491 := bstep (se 1 (by rfl) ⟨2233868, by rfl⟩ : syracuseStep 2978491 = 4467737) B4467737
theorem B5954633 : Blo 1764083 5954633 := bstep (se 2 (by rfl) ⟨2232987, by rfl⟩ : syracuseStep 5954633 = 4465975) B4465975
theorem B96567875 : Blo 1764083 96567875 := bstep (se 1 (by rfl) ⟨72425906, by rfl⟩ : syracuseStep 96567875 = 144851813) B144851813
theorem B38701289 : Blo 1764083 38701289 := bstep (se 2 (by rfl) ⟨14512983, by rfl⟩ : syracuseStep 38701289 = 29025967) B29025967
theorem B1765447 : Blo 1764083 1765447 := bstep (se 1 (by rfl) ⟨1324085, by rfl⟩ : syracuseStep 1765447 = 2648171) B2648171
theorem B3969755 : Blo 1764083 3969755 := bstep (se 1 (by rfl) ⟨2977316, by rfl⟩ : syracuseStep 3969755 = 5954633) B5954633
theorem B3971321 : Blo 1764083 3971321 := bstep (se 2 (by rfl) ⟨1489245, by rfl⟩ : syracuseStep 3971321 = 2978491) B2978491
theorem B309451751 : Blo 1764083 309451751 := bstep (se 1 (by rfl) ⟨232088813, by rfl⟩ : syracuseStep 309451751 = 464177627) B464177627
theorem B2646503 : Blo 1764083 2646503 := bstep (se 1 (by rfl) ⟨1984877, by rfl⟩ : syracuseStep 2646503 = 3969755) B3969755
theorem B2647547 : Blo 1764083 2647547 := bstep (se 1 (by rfl) ⟨1985660, by rfl⟩ : syracuseStep 2647547 = 3971321) B3971321
theorem B206301167 : Blo 1764083 206301167 := bstep (se 1 (by rfl) ⟨154725875, by rfl⟩ : syracuseStep 206301167 = 309451751) B309451751
theorem B25800859 : Blo 1764083 25800859 := bstep (se 1 (by rfl) ⟨19350644, by rfl⟩ : syracuseStep 25800859 = 38701289) B38701289
theorem B64378583 : Blo 1764083 64378583 := bstep (se 1 (by rfl) ⟨48283937, by rfl⟩ : syracuseStep 64378583 = 96567875) B96567875
theorem B42919055 : Blo 1764083 42919055 := bstep (se 1 (by rfl) ⟨32189291, by rfl⟩ : syracuseStep 42919055 = 64378583) B64378583
theorem B34401145 : Blo 1764083 34401145 := bstep (se 2 (by rfl) ⟨12900429, by rfl⟩ : syracuseStep 34401145 = 25800859) B25800859
theorem B1764335 : Blo 1764083 1764335 := bstep (se 1 (by rfl) ⟨1323251, by rfl⟩ : syracuseStep 1764335 = 2646503) B2646503
theorem B1765031 : Blo 1764083 1765031 := bstep (se 1 (by rfl) ⟨1323773, by rfl⟩ : syracuseStep 1765031 = 2647547) B2647547
theorem B137534111 : Blo 1764083 137534111 := bstep (se 1 (by rfl) ⟨103150583, by rfl⟩ : syracuseStep 137534111 = 206301167) B206301167
theorem B45868193 : Blo 1764083 45868193 := bstep (se 2 (by rfl) ⟨17200572, by rfl⟩ : syracuseStep 45868193 = 34401145) B34401145
theorem B91689407 : Blo 1764083 91689407 := bstep (se 1 (by rfl) ⟨68767055, by rfl⟩ : syracuseStep 91689407 = 137534111) B137534111
theorem B28612703 : Blo 1764083 28612703 := bstep (se 1 (by rfl) ⟨21459527, by rfl⟩ : syracuseStep 28612703 = 42919055) B42919055
theorem B19075135 : Blo 1764083 19075135 := bstep (se 1 (by rfl) ⟨14306351, by rfl⟩ : syracuseStep 19075135 = 28612703) B28612703
theorem B61126271 : Blo 1764083 61126271 := bstep (se 1 (by rfl) ⟨45844703, by rfl⟩ : syracuseStep 61126271 = 91689407) B91689407
theorem B30578795 : Blo 1764083 30578795 := bstep (se 1 (by rfl) ⟨22934096, by rfl⟩ : syracuseStep 30578795 = 45868193) B45868193
theorem B40750847 : Blo 1764083 40750847 := bstep (se 1 (by rfl) ⟨30563135, by rfl⟩ : syracuseStep 40750847 = 61126271) B61126271
theorem B20385863 : Blo 1764083 20385863 := bstep (se 1 (by rfl) ⟨15289397, by rfl⟩ : syracuseStep 20385863 = 30578795) B30578795
theorem B25433513 : Blo 1764083 25433513 := bstep (se 2 (by rfl) ⟨9537567, by rfl⟩ : syracuseStep 25433513 = 19075135) B19075135
theorem B13590575 : Blo 1764083 13590575 := bstep (se 1 (by rfl) ⟨10192931, by rfl⟩ : syracuseStep 13590575 = 20385863) B20385863
theorem B27167231 : Blo 1764083 27167231 := bstep (se 1 (by rfl) ⟨20375423, by rfl⟩ : syracuseStep 27167231 = 40750847) B40750847
theorem B16955675 : Blo 1764083 16955675 := bstep (se 1 (by rfl) ⟨12716756, by rfl⟩ : syracuseStep 16955675 = 25433513) B25433513
theorem B9060383 : Blo 1764083 9060383 := bstep (se 1 (by rfl) ⟨6795287, by rfl⟩ : syracuseStep 9060383 = 13590575) B13590575
theorem B11303783 : Blo 1764083 11303783 := bstep (se 1 (by rfl) ⟨8477837, by rfl⟩ : syracuseStep 11303783 = 16955675) B16955675
theorem B18111487 : Blo 1764083 18111487 := bstep (se 1 (by rfl) ⟨13583615, by rfl⟩ : syracuseStep 18111487 = 27167231) B27167231
theorem B6040255 : Blo 1764083 6040255 := bstep (se 1 (by rfl) ⟨4530191, by rfl⟩ : syracuseStep 6040255 = 9060383) B9060383
theorem B24148649 : Blo 1764083 24148649 := bstep (se 2 (by rfl) ⟨9055743, by rfl⟩ : syracuseStep 24148649 = 18111487) B18111487
theorem B7535855 : Blo 1764083 7535855 := bstep (se 1 (by rfl) ⟨5651891, by rfl⟩ : syracuseStep 7535855 = 11303783) B11303783
theorem B20095613 : Blo 1764083 20095613 := bstep (se 3 (by rfl) ⟨3767927, by rfl⟩ : syracuseStep 20095613 = 7535855) B7535855
theorem B8053673 : Blo 1764083 8053673 := bstep (se 2 (by rfl) ⟨3020127, by rfl⟩ : syracuseStep 8053673 = 6040255) B6040255
theorem B64396397 : Blo 1764083 64396397 := bstep (se 3 (by rfl) ⟨12074324, by rfl⟩ : syracuseStep 64396397 = 24148649) B24148649
theorem B13397075 : Blo 1764083 13397075 := bstep (se 1 (by rfl) ⟨10047806, by rfl⟩ : syracuseStep 13397075 = 20095613) B20095613
theorem B42930931 : Blo 1764083 42930931 := bstep (se 1 (by rfl) ⟨32198198, by rfl⟩ : syracuseStep 42930931 = 64396397) B64396397
theorem B21476461 : Blo 1764083 21476461 := bstep (se 3 (by rfl) ⟨4026836, by rfl⟩ : syracuseStep 21476461 = 8053673) B8053673
theorem B8931383 : Blo 1764083 8931383 := bstep (se 1 (by rfl) ⟨6698537, by rfl⟩ : syracuseStep 8931383 = 13397075) B13397075
theorem B57241241 : Blo 1764083 57241241 := bstep (se 2 (by rfl) ⟨21465465, by rfl⟩ : syracuseStep 57241241 = 42930931) B42930931
theorem B28635281 : Blo 1764083 28635281 := bstep (se 2 (by rfl) ⟨10738230, by rfl⟩ : syracuseStep 28635281 = 21476461) B21476461
theorem B38160827 : Blo 1764083 38160827 := bstep (se 1 (by rfl) ⟨28620620, by rfl⟩ : syracuseStep 38160827 = 57241241) B57241241
theorem B19090187 : Blo 1764083 19090187 := bstep (se 1 (by rfl) ⟨14317640, by rfl⟩ : syracuseStep 19090187 = 28635281) B28635281
theorem B5954255 : Blo 1764083 5954255 := bstep (se 1 (by rfl) ⟨4465691, by rfl⟩ : syracuseStep 5954255 = 8931383) B8931383
theorem B25440551 : Blo 1764083 25440551 := bstep (se 1 (by rfl) ⟨19080413, by rfl⟩ : syracuseStep 25440551 = 38160827) B38160827
theorem B3969503 : Blo 1764083 3969503 := bstep (se 1 (by rfl) ⟨2977127, by rfl⟩ : syracuseStep 3969503 = 5954255) B5954255
theorem B12726791 : Blo 1764083 12726791 := bstep (se 1 (by rfl) ⟨9545093, by rfl⟩ : syracuseStep 12726791 = 19090187) B19090187
theorem B2646335 : Blo 1764083 2646335 := bstep (se 1 (by rfl) ⟨1984751, by rfl⟩ : syracuseStep 2646335 = 3969503) B3969503
theorem B16960367 : Blo 1764083 16960367 := bstep (se 1 (by rfl) ⟨12720275, by rfl⟩ : syracuseStep 16960367 = 25440551) B25440551
theorem B8484527 : Blo 1764083 8484527 := bstep (se 1 (by rfl) ⟨6363395, by rfl⟩ : syracuseStep 8484527 = 12726791) B12726791
theorem B11306911 : Blo 1764083 11306911 := bstep (se 1 (by rfl) ⟨8480183, by rfl⟩ : syracuseStep 11306911 = 16960367) B16960367
theorem B1764223 : Blo 1764083 1764223 := bstep (se 1 (by rfl) ⟨1323167, by rfl⟩ : syracuseStep 1764223 = 2646335) B2646335
theorem B22625405 : Blo 1764083 22625405 := bstep (se 3 (by rfl) ⟨4242263, by rfl⟩ : syracuseStep 22625405 = 8484527) B8484527
theorem B15083603 : Blo 1764083 15083603 := bstep (se 1 (by rfl) ⟨11312702, by rfl⟩ : syracuseStep 15083603 = 22625405) B22625405
theorem B15075881 : Blo 1764083 15075881 := bstep (se 2 (by rfl) ⟨5653455, by rfl⟩ : syracuseStep 15075881 = 11306911) B11306911
theorem B10055735 : Blo 1764083 10055735 := bstep (se 1 (by rfl) ⟨7541801, by rfl⟩ : syracuseStep 10055735 = 15083603) B15083603
theorem B10050587 : Blo 1764083 10050587 := bstep (se 1 (by rfl) ⟨7537940, by rfl⟩ : syracuseStep 10050587 = 15075881) B15075881
theorem B6703823 : Blo 1764083 6703823 := bstep (se 1 (by rfl) ⟨5027867, by rfl⟩ : syracuseStep 6703823 = 10055735) B10055735
theorem B6700391 : Blo 1764083 6700391 := bstep (se 1 (by rfl) ⟨5025293, by rfl⟩ : syracuseStep 6700391 = 10050587) B10050587
theorem B4466927 : Blo 1764083 4466927 := bstep (se 1 (by rfl) ⟨3350195, by rfl⟩ : syracuseStep 4466927 = 6700391) B6700391
theorem B4469215 : Blo 1764083 4469215 := bstep (se 1 (by rfl) ⟨3351911, by rfl⟩ : syracuseStep 4469215 = 6703823) B6703823
theorem B5958953 : Blo 1764083 5958953 := bstep (se 2 (by rfl) ⟨2234607, by rfl⟩ : syracuseStep 5958953 = 4469215) B4469215
theorem B2977951 : Blo 1764083 2977951 := bstep (se 1 (by rfl) ⟨2233463, by rfl⟩ : syracuseStep 2977951 = 4466927) B4466927
theorem B3970601 : Blo 1764083 3970601 := bstep (se 2 (by rfl) ⟨1488975, by rfl⟩ : syracuseStep 3970601 = 2977951) B2977951
theorem B3972635 : Blo 1764083 3972635 := bstep (se 1 (by rfl) ⟨2979476, by rfl⟩ : syracuseStep 3972635 = 5958953) B5958953
theorem B2647067 : Blo 1764083 2647067 := bstep (se 1 (by rfl) ⟨1985300, by rfl⟩ : syracuseStep 2647067 = 3970601) B3970601
theorem B2648423 : Blo 1764083 2648423 := bstep (se 1 (by rfl) ⟨1986317, by rfl⟩ : syracuseStep 2648423 = 3972635) B3972635
theorem B1764711 : Blo 1764083 1764711 := bstep (se 1 (by rfl) ⟨1323533, by rfl⟩ : syracuseStep 1764711 = 2647067) B2647067
theorem B1765615 : Blo 1764083 1765615 := bstep (se 1 (by rfl) ⟨1324211, by rfl⟩ : syracuseStep 1765615 = 2648423) B2648423

theorem C0 (j : ℕ) (h1 : 441020 ≤ j) (h2 : j ≤ 441520) : Blo 1764083 (4 * j + 3) := by
  interval_cases j
  · exact B1764083
  · exact B1764087
  · exact B1764091
  · exact B1764095
  · exact B1764099
  · exact B1764103
  · exact B1764107
  · exact B1764111
  · exact B1764115
  · exact B1764119
  · exact B1764123
  · exact B1764127
  · exact B1764131
  · exact B1764135
  · exact B1764139
  · exact B1764143
  · exact B1764147
  · exact B1764151
  · exact B1764155
  · exact B1764159
  · exact B1764163
  · exact B1764167
  · exact B1764171
  · exact B1764175
  · exact B1764179
  · exact B1764183
  · exact B1764187
  · exact B1764191
  · exact B1764195
  · exact B1764199
  · exact B1764203
  · exact B1764207
  · exact B1764211
  · exact B1764215
  · exact B1764219
  · exact B1764223
  · exact B1764227
  · exact B1764231
  · exact B1764235
  · exact B1764239
  · exact B1764243
  · exact B1764247
  · exact B1764251
  · exact B1764255
  · exact B1764259
  · exact B1764263
  · exact B1764267
  · exact B1764271
  · exact B1764275
  · exact B1764279
  · exact B1764283
  · exact B1764287
  · exact B1764291
  · exact B1764295
  · exact B1764299
  · exact B1764303
  · exact B1764307
  · exact B1764311
  · exact B1764315
  · exact B1764319
  · exact B1764323
  · exact B1764327
  · exact B1764331
  · exact B1764335
  · exact B1764339
  · exact B1764343
  · exact B1764347
  · exact B1764351
  · exact B1764355
  · exact B1764359
  · exact B1764363
  · exact B1764367
  · exact B1764371
  · exact B1764375
  · exact B1764379
  · exact B1764383
  · exact B1764387
  · exact B1764391
  · exact B1764395
  · exact B1764399
  · exact B1764403
  · exact B1764407
  · exact B1764411
  · exact B1764415
  · exact B1764419
  · exact B1764423
  · exact B1764427
  · exact B1764431
  · exact B1764435
  · exact B1764439
  · exact B1764443
  · exact B1764447
  · exact B1764451
  · exact B1764455
  · exact B1764459
  · exact B1764463
  · exact B1764467
  · exact B1764471
  · exact B1764475
  · exact B1764479
  · exact B1764483
  · exact B1764487
  · exact B1764491
  · exact B1764495
  · exact B1764499
  · exact B1764503
  · exact B1764507
  · exact B1764511
  · exact B1764515
  · exact B1764519
  · exact B1764523
  · exact B1764527
  · exact B1764531
  · exact B1764535
  · exact B1764539
  · exact B1764543
  · exact B1764547
  · exact B1764551
  · exact B1764555
  · exact B1764559
  · exact B1764563
  · exact B1764567
  · exact B1764571
  · exact B1764575
  · exact B1764579
  · exact B1764583
  · exact B1764587
  · exact B1764591
  · exact B1764595
  · exact B1764599
  · exact B1764603
  · exact B1764607
  · exact B1764611
  · exact B1764615
  · exact B1764619
  · exact B1764623
  · exact B1764627
  · exact B1764631
  · exact B1764635
  · exact B1764639
  · exact B1764643
  · exact B1764647
  · exact B1764651
  · exact B1764655
  · exact B1764659
  · exact B1764663
  · exact B1764667
  · exact B1764671
  · exact B1764675
  · exact B1764679
  · exact B1764683
  · exact B1764687
  · exact B1764691
  · exact B1764695
  · exact B1764699
  · exact B1764703
  · exact B1764707
  · exact B1764711
  · exact B1764715
  · exact B1764719
  · exact B1764723
  · exact B1764727
  · exact B1764731
  · exact B1764735
  · exact B1764739
  · exact B1764743
  · exact B1764747
  · exact B1764751
  · exact B1764755
  · exact B1764759
  · exact B1764763
  · exact B1764767
  · exact B1764771
  · exact B1764775
  · exact B1764779
  · exact B1764783
  · exact B1764787
  · exact B1764791
  · exact B1764795
  · exact B1764799
  · exact B1764803
  · exact B1764807
  · exact B1764811
  · exact B1764815
  · exact B1764819
  · exact B1764823
  · exact B1764827
  · exact B1764831
  · exact B1764835
  · exact B1764839
  · exact B1764843
  · exact B1764847
  · exact B1764851
  · exact B1764855
  · exact B1764859
  · exact B1764863
  · exact B1764867
  · exact B1764871
  · exact B1764875
  · exact B1764879
  · exact B1764883
  · exact B1764887
  · exact B1764891
  · exact B1764895
  · exact B1764899
  · exact B1764903
  · exact B1764907
  · exact B1764911
  · exact B1764915
  · exact B1764919
  · exact B1764923
  · exact B1764927
  · exact B1764931
  · exact B1764935
  · exact B1764939
  · exact B1764943
  · exact B1764947
  · exact B1764951
  · exact B1764955
  · exact B1764959
  · exact B1764963
  · exact B1764967
  · exact B1764971
  · exact B1764975
  · exact B1764979
  · exact B1764983
  · exact B1764987
  · exact B1764991
  · exact B1764995
  · exact B1764999
  · exact B1765003
  · exact B1765007
  · exact B1765011
  · exact B1765015
  · exact B1765019
  · exact B1765023
  · exact B1765027
  · exact B1765031
  · exact B1765035
  · exact B1765039
  · exact B1765043
  · exact B1765047
  · exact B1765051
  · exact B1765055
  · exact B1765059
  · exact B1765063
  · exact B1765067
  · exact B1765071
  · exact B1765075
  · exact B1765079
  · exact B1765083
  · exact B1765087
  · exact B1765091
  · exact B1765095
  · exact B1765099
  · exact B1765103
  · exact B1765107
  · exact B1765111
  · exact B1765115
  · exact B1765119
  · exact B1765123
  · exact B1765127
  · exact B1765131
  · exact B1765135
  · exact B1765139
  · exact B1765143
  · exact B1765147
  · exact B1765151
  · exact B1765155
  · exact B1765159
  · exact B1765163
  · exact B1765167
  · exact B1765171
  · exact B1765175
  · exact B1765179
  · exact B1765183
  · exact B1765187
  · exact B1765191
  · exact B1765195
  · exact B1765199
  · exact B1765203
  · exact B1765207
  · exact B1765211
  · exact B1765215
  · exact B1765219
  · exact B1765223
  · exact B1765227
  · exact B1765231
  · exact B1765235
  · exact B1765239
  · exact B1765243
  · exact B1765247
  · exact B1765251
  · exact B1765255
  · exact B1765259
  · exact B1765263
  · exact B1765267
  · exact B1765271
  · exact B1765275
  · exact B1765279
  · exact B1765283
  · exact B1765287
  · exact B1765291
  · exact B1765295
  · exact B1765299
  · exact B1765303
  · exact B1765307
  · exact B1765311
  · exact B1765315
  · exact B1765319
  · exact B1765323
  · exact B1765327
  · exact B1765331
  · exact B1765335
  · exact B1765339
  · exact B1765343
  · exact B1765347
  · exact B1765351
  · exact B1765355
  · exact B1765359
  · exact B1765363
  · exact B1765367
  · exact B1765371
  · exact B1765375
  · exact B1765379
  · exact B1765383
  · exact B1765387
  · exact B1765391
  · exact B1765395
  · exact B1765399
  · exact B1765403
  · exact B1765407
  · exact B1765411
  · exact B1765415
  · exact B1765419
  · exact B1765423
  · exact B1765427
  · exact B1765431
  · exact B1765435
  · exact B1765439
  · exact B1765443
  · exact B1765447
  · exact B1765451
  · exact B1765455
  · exact B1765459
  · exact B1765463
  · exact B1765467
  · exact B1765471
  · exact B1765475
  · exact B1765479
  · exact B1765483
  · exact B1765487
  · exact B1765491
  · exact B1765495
  · exact B1765499
  · exact B1765503
  · exact B1765507
  · exact B1765511
  · exact B1765515
  · exact B1765519
  · exact B1765523
  · exact B1765527
  · exact B1765531
  · exact B1765535
  · exact B1765539
  · exact B1765543
  · exact B1765547
  · exact B1765551
  · exact B1765555
  · exact B1765559
  · exact B1765563
  · exact B1765567
  · exact B1765571
  · exact B1765575
  · exact B1765579
  · exact B1765583
  · exact B1765587
  · exact B1765591
  · exact B1765595
  · exact B1765599
  · exact B1765603
  · exact B1765607
  · exact B1765611
  · exact B1765615
  · exact B1765619
  · exact B1765623
  · exact B1765627
  · exact B1765631
  · exact B1765635
  · exact B1765639
  · exact B1765643
  · exact B1765647
  · exact B1765651
  · exact B1765655
  · exact B1765659
  · exact B1765663
  · exact B1765667
  · exact B1765671
  · exact B1765675
  · exact B1765679
  · exact B1765683
  · exact B1765687
  · exact B1765691
  · exact B1765695
  · exact B1765699
  · exact B1765703
  · exact B1765707
  · exact B1765711
  · exact B1765715
  · exact B1765719
  · exact B1765723
  · exact B1765727
  · exact B1765731
  · exact B1765735
  · exact B1765739
  · exact B1765743
  · exact B1765747
  · exact B1765751
  · exact B1765755
  · exact B1765759
  · exact B1765763
  · exact B1765767
  · exact B1765771
  · exact B1765775
  · exact B1765779
  · exact B1765783
  · exact B1765787
  · exact B1765791
  · exact B1765795
  · exact B1765799
  · exact B1765803
  · exact B1765807
  · exact B1765811
  · exact B1765815
  · exact B1765819
  · exact B1765823
  · exact B1765827
  · exact B1765831
  · exact B1765835
  · exact B1765839
  · exact B1765843
  · exact B1765847
  · exact B1765851
  · exact B1765855
  · exact B1765859
  · exact B1765863
  · exact B1765867
  · exact B1765871
  · exact B1765875
  · exact B1765879
  · exact B1765883
  · exact B1765887
  · exact B1765891
  · exact B1765895
  · exact B1765899
  · exact B1765903
  · exact B1765907
  · exact B1765911
  · exact B1765915
  · exact B1765919
  · exact B1765923
  · exact B1765927
  · exact B1765931
  · exact B1765935
  · exact B1765939
  · exact B1765943
  · exact B1765947
  · exact B1765951
  · exact B1765955
  · exact B1765959
  · exact B1765963
  · exact B1765967
  · exact B1765971
  · exact B1765975
  · exact B1765979
  · exact B1765983
  · exact B1765987
  · exact B1765991
  · exact B1765995
  · exact B1765999
  · exact B1766003
  · exact B1766007
  · exact B1766011
  · exact B1766015
  · exact B1766019
  · exact B1766023
  · exact B1766027
  · exact B1766031
  · exact B1766035
  · exact B1766039
  · exact B1766043
  · exact B1766047
  · exact B1766051
  · exact B1766055
  · exact B1766059
  · exact B1766063
  · exact B1766067
  · exact B1766071
  · exact B1766075
  · exact B1766079
  · exact B1766083

theorem solution (m : ℕ) (hlo : 1764083 ≤ m) (hhi : m ≤ 1766083) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 441020 ≤ j := by omega
    have hj2 : j ≤ 441520 := by omega
    have hb : Blo 1764083 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
