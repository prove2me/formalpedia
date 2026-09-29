-- Prove2me | solution 1 for syracuse_descends_range_1782092_1784092
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:44:51.474411+00:00
-- url     : https://prove2.me/submissions/7921e4f9-bb3b-4e3f-9a7f-07fe38da3cab

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


theorem B2007049 : Blo 1782092 2007049 := bbase (se 2 (by rfl) ⟨752643, by rfl⟩ : syracuseStep 2007049 = 1505287) (by norm_num)
theorem B15441941 : Blo 1782092 15441941 := bbase (se 6 (by rfl) ⟨361920, by rfl⟩ : syracuseStep 15441941 = 723841) (by norm_num)
theorem B4014125 : Blo 1782092 4014125 := bbase (se 3 (by rfl) ⟨752648, by rfl⟩ : syracuseStep 4014125 = 1505297) (by norm_num)
theorem B2007085 : Blo 1782092 2007085 := bbase (se 3 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 2007085 = 752657) (by norm_num)
theorem B3383365 : Blo 1782092 3383365 := bbase (se 4 (by rfl) ⟨317190, by rfl⟩ : syracuseStep 3383365 = 634381) (by norm_num)
theorem B4513877 : Blo 1782092 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B5079125 : Blo 1782092 5079125 := bbase (se 8 (by rfl) ⟨29760, by rfl⟩ : syracuseStep 5079125 = 59521) (by norm_num)
theorem B4014197 : Blo 1782092 4014197 := bbase (se 5 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 4014197 = 376331) (by norm_num)
theorem B3809405 : Blo 1782092 3809405 := bbase (se 3 (by rfl) ⟨714263, by rfl⟩ : syracuseStep 3809405 = 1428527) (by norm_num)
theorem B6021269 : Blo 1782092 6021269 := bbase (se 6 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 6021269 = 282247) (by norm_num)
theorem B3383525 : Blo 1782092 3383525 := bbase (se 4 (by rfl) ⟨317205, by rfl⟩ : syracuseStep 3383525 = 634411) (by norm_num)
theorem B3809549 : Blo 1782092 3809549 := bbase (se 3 (by rfl) ⟨714290, by rfl⟩ : syracuseStep 3809549 = 1428581) (by norm_num)
theorem B4514069 : Blo 1782092 4514069 := bbase (se 6 (by rfl) ⟨105798, by rfl⟩ : syracuseStep 4514069 = 211597) (by norm_num)
theorem B3211597 : Blo 1782092 3211597 := bbase (se 3 (by rfl) ⟨602174, by rfl⟩ : syracuseStep 3211597 = 1204349) (by norm_num)
theorem B3383669 : Blo 1782092 3383669 := bbase (se 5 (by rfl) ⟨158609, by rfl⟩ : syracuseStep 3383669 = 317219) (by norm_num)
theorem B3432829 : Blo 1782092 3432829 := bbase (se 3 (by rfl) ⟨643655, by rfl⟩ : syracuseStep 3432829 = 1287311) (by norm_num)
theorem B4284821 : Blo 1782092 4284821 := bbase (se 6 (by rfl) ⟨100425, by rfl⟩ : syracuseStep 4284821 = 200851) (by norm_num)
theorem B2712085 : Blo 1782092 2712085 := bbase (se 6 (by rfl) ⟨63564, by rfl⟩ : syracuseStep 2712085 = 127129) (by norm_num)
theorem B54911573 : Blo 1782092 54911573 := bbase (se 8 (by rfl) ⟨321747, by rfl⟩ : syracuseStep 54911573 = 643495) (by norm_num)
theorem B4514413 : Blo 1782092 4514413 := bbase (se 3 (by rfl) ⟨846452, by rfl⟩ : syracuseStep 4514413 = 1692905) (by norm_num)
theorem B7717493 : Blo 1782092 7717493 := bbase (se 5 (by rfl) ⟨361757, by rfl⟩ : syracuseStep 7717493 = 723515) (by norm_num)
theorem B3809909 : Blo 1782092 3809909 := bbase (se 5 (by rfl) ⟨178589, by rfl⟩ : syracuseStep 3809909 = 357179) (by norm_num)
theorem B3383957 : Blo 1782092 3383957 := bbase (se 6 (by rfl) ⟨79311, by rfl⟩ : syracuseStep 3383957 = 158623) (by norm_num)
theorem B3613405 : Blo 1782092 3613405 := bbase (se 3 (by rfl) ⟨677513, by rfl⟩ : syracuseStep 3613405 = 1355027) (by norm_num)
theorem B4514525 : Blo 1782092 4514525 := bbase (se 3 (by rfl) ⟨846473, by rfl⟩ : syracuseStep 4514525 = 1692947) (by norm_num)
theorem B4285205 : Blo 1782092 4285205 := bbase (se 6 (by rfl) ⟨100434, by rfl⟩ : syracuseStep 4285205 = 200869) (by norm_num)
theorem B3384109 : Blo 1782092 3384109 := bbase (se 3 (by rfl) ⟨634520, by rfl⟩ : syracuseStep 3384109 = 1269041) (by norm_num)
theorem B3613501 : Blo 1782092 3613501 := bbase (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) (by norm_num)
theorem B9028421 : Blo 1782092 9028421 := bbase (se 4 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 9028421 = 1692829) (by norm_num)
theorem B2712413 : Blo 1782092 2712413 := bbase (se 3 (by rfl) ⟨508577, by rfl⟩ : syracuseStep 2712413 = 1017155) (by norm_num)
theorem B3007381 : Blo 1782092 3007381 := bbase (se 6 (by rfl) ⟨70485, by rfl⟩ : syracuseStep 3007381 = 140971) (by norm_num)
theorem B4514717 : Blo 1782092 4514717 := bbase (se 3 (by rfl) ⟨846509, by rfl⟩ : syracuseStep 4514717 = 1693019) (by norm_num)
theorem B3007469 : Blo 1782092 3007469 := bbase (se 3 (by rfl) ⟨563900, by rfl⟩ : syracuseStep 3007469 = 1127801) (by norm_num)
theorem B13542389 : Blo 1782092 13542389 := bbase (se 5 (by rfl) ⟨634799, by rfl⟩ : syracuseStep 13542389 = 1269599) (by norm_num)
theorem B5080117 : Blo 1782092 5080117 := bbase (se 5 (by rfl) ⟨238130, by rfl⟩ : syracuseStep 5080117 = 476261) (by norm_num)
theorem B3384413 : Blo 1782092 3384413 := bbase (se 3 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 3384413 = 1269155) (by norm_num)
theorem B3007597 : Blo 1782092 3007597 := bbase (se 3 (by rfl) ⟨563924, by rfl⟩ : syracuseStep 3007597 = 1127849) (by norm_num)
theorem B10159253 : Blo 1782092 10159253 := bbase (se 6 (by rfl) ⟨238107, by rfl⟩ : syracuseStep 10159253 = 476215) (by norm_num)
theorem B3007685 : Blo 1782092 3007685 := bbase (se 4 (by rfl) ⟨281970, by rfl⟩ : syracuseStep 3007685 = 563941) (by norm_num)
theorem B4515061 : Blo 1782092 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B1983745 : Blo 1782092 1983745 := bbase (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) (by norm_num)
theorem B10151189 : Blo 1782092 10151189 := bbase (se 6 (by rfl) ⟨237918, by rfl⟩ : syracuseStep 10151189 = 475837) (by norm_num)
theorem B4818197 : Blo 1782092 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B2475317 : Blo 1782092 2475317 := bbase (se 5 (by rfl) ⟨116030, by rfl⟩ : syracuseStep 2475317 = 232061) (by norm_num)
theorem B3007813 : Blo 1782092 3007813 := bbase (se 4 (by rfl) ⟨281982, by rfl⟩ : syracuseStep 3007813 = 563965) (by norm_num)
theorem B4515173 : Blo 1782092 4515173 := bbase (se 4 (by rfl) ⟨423297, by rfl⟩ : syracuseStep 4515173 = 846595) (by norm_num)
theorem B13534613 : Blo 1782092 13534613 := bbase (se 6 (by rfl) ⟨317217, by rfl⟩ : syracuseStep 13534613 = 634435) (by norm_num)
theorem B3007901 : Blo 1782092 3007901 := bbase (se 3 (by rfl) ⟨563981, by rfl⟩ : syracuseStep 3007901 = 1127963) (by norm_num)
theorem B3008029 : Blo 1782092 3008029 := bbase (se 3 (by rfl) ⟨564005, by rfl⟩ : syracuseStep 3008029 = 1128011) (by norm_num)
theorem B4515365 : Blo 1782092 4515365 := bbase (se 4 (by rfl) ⟨423315, by rfl⟩ : syracuseStep 4515365 = 846631) (by norm_num)
theorem B3008117 : Blo 1782092 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B3712709 : Blo 1782092 3712709 := bbase (se 4 (by rfl) ⟨348066, by rfl⟩ : syracuseStep 3712709 = 696133) (by norm_num)
theorem B3049181 : Blo 1782092 3049181 := bbase (se 3 (by rfl) ⟨571721, by rfl⟩ : syracuseStep 3049181 = 1143443) (by norm_num)
theorem B3008245 : Blo 1782092 3008245 := bbase (se 5 (by rfl) ⟨141011, by rfl⟩ : syracuseStep 3008245 = 282023) (by norm_num)
theorem B6014789 : Blo 1782092 6014789 := bbase (se 4 (by rfl) ⟨563886, by rfl⟩ : syracuseStep 6014789 = 1127773) (by norm_num)
theorem B3008333 : Blo 1782092 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B3385165 : Blo 1782092 3385165 := bbase (se 3 (by rfl) ⟨634718, by rfl⟩ : syracuseStep 3385165 = 1269437) (by norm_num)
theorem B98928469 : Blo 1782092 98928469 := bbase (se 9 (by rfl) ⟨289829, by rfl⟩ : syracuseStep 98928469 = 579659) (by norm_num)
theorem B3614557 : Blo 1782092 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B4515709 : Blo 1782092 4515709 := bbase (se 3 (by rfl) ⟨846695, by rfl⟩ : syracuseStep 4515709 = 1693391) (by norm_num)
theorem B3008461 : Blo 1782092 3008461 := bbase (se 3 (by rfl) ⟨564086, by rfl⟩ : syracuseStep 3008461 = 1128173) (by norm_num)
theorem B3385309 : Blo 1782092 3385309 := bbase (se 3 (by rfl) ⟨634745, by rfl⟩ : syracuseStep 3385309 = 1269491) (by norm_num)
theorem B4515821 : Blo 1782092 4515821 := bbase (se 3 (by rfl) ⟨846716, by rfl⟩ : syracuseStep 4515821 = 1693433) (by norm_num)
theorem B6768629 : Blo 1782092 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B10299413 : Blo 1782092 10299413 := bbase (se 6 (by rfl) ⟨241392, by rfl⟩ : syracuseStep 10299413 = 482785) (by norm_num)
theorem B3008549 : Blo 1782092 3008549 := bbase (se 4 (by rfl) ⟨282051, by rfl⟩ : syracuseStep 3008549 = 564103) (by norm_num)
theorem B9029717 : Blo 1782092 9029717 := bbase (se 8 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 9029717 = 105817) (by norm_num)
theorem B20088917 : Blo 1782092 20088917 := bbase (se 8 (by rfl) ⟨117708, by rfl⟩ : syracuseStep 20088917 = 235417) (by norm_num)
theorem B6514805 : Blo 1782092 6514805 := bbase (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) (by norm_num)
theorem B3385469 : Blo 1782092 3385469 := bbase (se 3 (by rfl) ⟨634775, by rfl⟩ : syracuseStep 3385469 = 1269551) (by norm_num)
theorem B3008677 : Blo 1782092 3008677 := bbase (se 4 (by rfl) ⟨282063, by rfl⟩ : syracuseStep 3008677 = 564127) (by norm_num)
theorem B6015221 : Blo 1782092 6015221 := bbase (se 5 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 6015221 = 563927) (by norm_num)
theorem B3008765 : Blo 1782092 3008765 := bbase (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) (by norm_num)
theorem B3385613 : Blo 1782092 3385613 := bbase (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) (by norm_num)
theorem B6768917 : Blo 1782092 6768917 := bbase (se 6 (by rfl) ⟨158646, by rfl⟩ : syracuseStep 6768917 = 317293) (by norm_num)
theorem B10160437 : Blo 1782092 10160437 := bbase (se 5 (by rfl) ⟨476270, by rfl⟩ : syracuseStep 10160437 = 952541) (by norm_num)
theorem B3008893 : Blo 1782092 3008893 := bbase (se 3 (by rfl) ⟨564167, by rfl⟩ : syracuseStep 3008893 = 1128335) (by norm_num)
theorem B6097349 : Blo 1782092 6097349 := bbase (se 4 (by rfl) ⟨571626, by rfl⟩ : syracuseStep 6097349 = 1143253) (by norm_num)
theorem B3008981 : Blo 1782092 3008981 := bbase (se 7 (by rfl) ⟨35261, by rfl⟩ : syracuseStep 3008981 = 70523) (by norm_num)
theorem B9021941 : Blo 1782092 9021941 := bbase (se 5 (by rfl) ⟨422903, by rfl⟩ : syracuseStep 9021941 = 845807) (by norm_num)
theorem B2673149 : Blo 1782092 2673149 := bbase (se 3 (by rfl) ⟨501215, by rfl⟩ : syracuseStep 2673149 = 1002431) (by norm_num)
theorem B2673173 : Blo 1782092 2673173 := bbase (se 6 (by rfl) ⟨62652, by rfl⟩ : syracuseStep 2673173 = 125305) (by norm_num)
theorem B2673197 : Blo 1782092 2673197 := bbase (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) (by norm_num)
theorem B3385901 : Blo 1782092 3385901 := bbase (se 3 (by rfl) ⟨634856, by rfl⟩ : syracuseStep 3385901 = 1269713) (by norm_num)
theorem B2673221 : Blo 1782092 2673221 := bbase (se 4 (by rfl) ⟨250614, by rfl⟩ : syracuseStep 2673221 = 501229) (by norm_num)
theorem B3009109 : Blo 1782092 3009109 := bbase (se 8 (by rfl) ⟨17631, by rfl⟩ : syracuseStep 3009109 = 35263) (by norm_num)
theorem B2673245 : Blo 1782092 2673245 := bbase (se 3 (by rfl) ⟨501233, by rfl⟩ : syracuseStep 2673245 = 1002467) (by norm_num)
theorem B2255465 : Blo 1782092 2255465 := bbase (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) (by norm_num)
theorem B2673269 : Blo 1782092 2673269 := bbase (se 5 (by rfl) ⟨125309, by rfl⟩ : syracuseStep 2673269 = 250619) (by norm_num)
theorem B2673293 : Blo 1782092 2673293 := bbase (se 3 (by rfl) ⟨501242, by rfl⟩ : syracuseStep 2673293 = 1002485) (by norm_num)
theorem B4573853 : Blo 1782092 4573853 := bbase (se 3 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 4573853 = 1715195) (by norm_num)
theorem B2255521 : Blo 1782092 2255521 := bbase (se 2 (by rfl) ⟨845820, by rfl⟩ : syracuseStep 2255521 = 1691641) (by norm_num)
theorem B2673317 : Blo 1782092 2673317 := bbase (se 4 (by rfl) ⟨250623, by rfl⟩ : syracuseStep 2673317 = 501247) (by norm_num)
theorem B6015653 : Blo 1782092 6015653 := bbase (se 4 (by rfl) ⟨563967, by rfl⟩ : syracuseStep 6015653 = 1127935) (by norm_num)
theorem B3009197 : Blo 1782092 3009197 := bbase (se 3 (by rfl) ⟨564224, by rfl⟩ : syracuseStep 3009197 = 1128449) (by norm_num)
theorem B2673341 : Blo 1782092 2673341 := bbase (se 3 (by rfl) ⟨501251, by rfl⟩ : syracuseStep 2673341 = 1002503) (by norm_num)
theorem B5712581 : Blo 1782092 5712581 := bbase (se 4 (by rfl) ⟨535554, by rfl⟩ : syracuseStep 5712581 = 1071109) (by norm_num)
theorem B3386053 : Blo 1782092 3386053 := bbase (se 4 (by rfl) ⟨317442, by rfl⟩ : syracuseStep 3386053 = 634885) (by norm_num)
theorem B2673365 : Blo 1782092 2673365 := bbase (se 7 (by rfl) ⟨31328, by rfl⟩ : syracuseStep 2673365 = 62657) (by norm_num)
theorem B25701077 : Blo 1782092 25701077 := bbase (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) (by norm_num)
theorem B2673389 : Blo 1782092 2673389 := bbase (se 3 (by rfl) ⟨501260, by rfl⟩ : syracuseStep 2673389 = 1002521) (by norm_num)
theorem B2411245 : Blo 1782092 2411245 := bbase (se 3 (by rfl) ⟨452108, by rfl⟩ : syracuseStep 2411245 = 904217) (by norm_num)
theorem B2255617 : Blo 1782092 2255617 := bbase (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) (by norm_num)
theorem B2673413 : Blo 1782092 2673413 := bbase (se 4 (by rfl) ⟨250632, by rfl⟩ : syracuseStep 2673413 = 501265) (by norm_num)
theorem B11578133 : Blo 1782092 11578133 := bbase (se 6 (by rfl) ⟨271362, by rfl⟩ : syracuseStep 11578133 = 542725) (by norm_num)
theorem B2673437 : Blo 1782092 2673437 := bbase (se 3 (by rfl) ⟨501269, by rfl⟩ : syracuseStep 2673437 = 1002539) (by norm_num)
theorem B3009325 : Blo 1782092 3009325 := bbase (se 3 (by rfl) ⟨564248, by rfl⟩ : syracuseStep 3009325 = 1128497) (by norm_num)
theorem B2673461 : Blo 1782092 2673461 := bbase (se 5 (by rfl) ⟨125318, by rfl⟩ : syracuseStep 2673461 = 250637) (by norm_num)
theorem B2673485 : Blo 1782092 2673485 := bbase (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) (by norm_num)
theorem B2673509 : Blo 1782092 2673509 := bbase (se 4 (by rfl) ⟨250641, by rfl⟩ : syracuseStep 2673509 = 501283) (by norm_num)
theorem B2673533 : Blo 1782092 2673533 := bbase (se 3 (by rfl) ⟨501287, by rfl⟩ : syracuseStep 2673533 = 1002575) (by norm_num)
theorem B3009413 : Blo 1782092 3009413 := bbase (se 4 (by rfl) ⟨282132, by rfl⟩ : syracuseStep 3009413 = 564265) (by norm_num)
theorem B2673557 : Blo 1782092 2673557 := bbase (se 6 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 2673557 = 125323) (by norm_num)
theorem B2255789 : Blo 1782092 2255789 := bbase (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) (by norm_num)
theorem B2673581 : Blo 1782092 2673581 := bbase (se 3 (by rfl) ⟨501296, by rfl⟩ : syracuseStep 2673581 = 1002593) (by norm_num)
theorem B2673605 : Blo 1782092 2673605 := bbase (se 4 (by rfl) ⟨250650, by rfl⟩ : syracuseStep 2673605 = 501301) (by norm_num)
theorem B3050453 : Blo 1782092 3050453 := bbase (se 7 (by rfl) ⟨35747, by rfl⟩ : syracuseStep 3050453 = 71495) (by norm_num)
theorem B2673629 : Blo 1782092 2673629 := bbase (se 3 (by rfl) ⟨501305, by rfl⟩ : syracuseStep 2673629 = 1002611) (by norm_num)
theorem B2255845 : Blo 1782092 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B2673653 : Blo 1782092 2673653 := bbase (se 5 (by rfl) ⟨125327, by rfl⟩ : syracuseStep 2673653 = 250655) (by norm_num)
theorem B3386357 : Blo 1782092 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B1903609 : Blo 1782092 1903609 := bbase (se 2 (by rfl) ⟨713853, by rfl⟩ : syracuseStep 1903609 = 1427707) (by norm_num)
theorem B3009541 : Blo 1782092 3009541 := bbase (se 4 (by rfl) ⟨282144, by rfl⟩ : syracuseStep 3009541 = 564289) (by norm_num)
theorem B2673677 : Blo 1782092 2673677 := bbase (se 3 (by rfl) ⟨501314, by rfl⟩ : syracuseStep 2673677 = 1002629) (by norm_num)
theorem B2673701 : Blo 1782092 2673701 := bbase (se 4 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 2673701 = 501319) (by norm_num)
theorem B4066357 : Blo 1782092 4066357 := bbase (se 5 (by rfl) ⟨190610, by rfl⟩ : syracuseStep 4066357 = 381221) (by norm_num)
theorem B2673725 : Blo 1782092 2673725 := bbase (se 3 (by rfl) ⟨501323, by rfl⟩ : syracuseStep 2673725 = 1002647) (by norm_num)
theorem B1903681 : Blo 1782092 1903681 := bbase (se 2 (by rfl) ⟨713880, by rfl⟩ : syracuseStep 1903681 = 1427761) (by norm_num)
theorem B2255941 : Blo 1782092 2255941 := bbase (se 4 (by rfl) ⟨211494, by rfl⟩ : syracuseStep 2255941 = 422989) (by norm_num)
theorem B2673749 : Blo 1782092 2673749 := bbase (se 8 (by rfl) ⟨15666, by rfl⟩ : syracuseStep 2673749 = 31333) (by norm_num)
theorem B6016085 : Blo 1782092 6016085 := bbase (se 8 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 6016085 = 70501) (by norm_num)
theorem B3009629 : Blo 1782092 3009629 := bbase (se 3 (by rfl) ⟨564305, by rfl⟩ : syracuseStep 3009629 = 1128611) (by norm_num)
theorem B2673773 : Blo 1782092 2673773 := bbase (se 3 (by rfl) ⟨501332, by rfl⟩ : syracuseStep 2673773 = 1002665) (by norm_num)
theorem B2673797 : Blo 1782092 2673797 := bbase (se 4 (by rfl) ⟨250668, by rfl⟩ : syracuseStep 2673797 = 501337) (by norm_num)
theorem B2673821 : Blo 1782092 2673821 := bbase (se 3 (by rfl) ⟨501341, by rfl⟩ : syracuseStep 2673821 = 1002683) (by norm_num)
theorem B2673845 : Blo 1782092 2673845 := bbase (se 5 (by rfl) ⟨125336, by rfl⟩ : syracuseStep 2673845 = 250673) (by norm_num)
theorem B2673869 : Blo 1782092 2673869 := bbase (se 3 (by rfl) ⟨501350, by rfl⟩ : syracuseStep 2673869 = 1002701) (by norm_num)
theorem B18541781 : Blo 1782092 18541781 := bbase (se 7 (by rfl) ⟨217286, by rfl⟩ : syracuseStep 18541781 = 434573) (by norm_num)
theorem B3009757 : Blo 1782092 3009757 := bbase (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) (by norm_num)
theorem B2673893 : Blo 1782092 2673893 := bbase (se 4 (by rfl) ⟨250677, by rfl⟩ : syracuseStep 2673893 = 501355) (by norm_num)
theorem B2256113 : Blo 1782092 2256113 := bbase (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) (by norm_num)
theorem B1903861 : Blo 1782092 1903861 := bbase (se 5 (by rfl) ⟨89243, by rfl⟩ : syracuseStep 1903861 = 178487) (by norm_num)
theorem B2673917 : Blo 1782092 2673917 := bbase (se 3 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 2673917 = 1002719) (by norm_num)
theorem B2673941 : Blo 1782092 2673941 := bbase (se 6 (by rfl) ⟨62670, by rfl⟩ : syracuseStep 2673941 = 125341) (by norm_num)
theorem B2256169 : Blo 1782092 2256169 := bbase (se 2 (by rfl) ⟨846063, by rfl⟩ : syracuseStep 2256169 = 1692127) (by norm_num)
theorem B2673965 : Blo 1782092 2673965 := bbase (se 3 (by rfl) ⟨501368, by rfl⟩ : syracuseStep 2673965 = 1002737) (by norm_num)
theorem B3009845 : Blo 1782092 3009845 := bbase (se 5 (by rfl) ⟨141086, by rfl⟩ : syracuseStep 3009845 = 282173) (by norm_num)
theorem B2673989 : Blo 1782092 2673989 := bbase (se 4 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 2673989 = 501373) (by norm_num)
theorem B2895173 : Blo 1782092 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B2674013 : Blo 1782092 2674013 := bbase (se 3 (by rfl) ⟨501377, by rfl⟩ : syracuseStep 2674013 = 1002755) (by norm_num)
theorem B9031013 : Blo 1782092 9031013 := bbase (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) (by norm_num)
theorem B2674037 : Blo 1782092 2674037 := bbase (se 5 (by rfl) ⟨125345, by rfl⟩ : syracuseStep 2674037 = 250691) (by norm_num)
theorem B2256265 : Blo 1782092 2256265 := bbase (se 2 (by rfl) ⟨846099, by rfl⟩ : syracuseStep 2256265 = 1692199) (by norm_num)
theorem B2674061 : Blo 1782092 2674061 := bbase (se 3 (by rfl) ⟨501386, by rfl⟩ : syracuseStep 2674061 = 1002773) (by norm_num)
theorem B2674085 : Blo 1782092 2674085 := bbase (se 4 (by rfl) ⟨250695, by rfl⟩ : syracuseStep 2674085 = 501391) (by norm_num)
theorem B2936237 : Blo 1782092 2936237 := bbase (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) (by norm_num)
theorem B6770101 : Blo 1782092 6770101 := bbase (se 5 (by rfl) ⟨317348, by rfl⟩ : syracuseStep 6770101 = 634697) (by norm_num)
theorem B3009973 : Blo 1782092 3009973 := bbase (se 5 (by rfl) ⟨141092, by rfl⟩ : syracuseStep 3009973 = 282185) (by norm_num)
theorem B2674109 : Blo 1782092 2674109 := bbase (se 3 (by rfl) ⟨501395, by rfl⟩ : syracuseStep 2674109 = 1002791) (by norm_num)
theorem B2674133 : Blo 1782092 2674133 := bbase (se 7 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 2674133 = 62675) (by norm_num)
theorem B7228885 : Blo 1782092 7228885 := bbase (se 7 (by rfl) ⟨84713, by rfl⟩ : syracuseStep 7228885 = 169427) (by norm_num)
theorem B3476957 : Blo 1782092 3476957 := bbase (se 3 (by rfl) ⟨651929, by rfl⟩ : syracuseStep 3476957 = 1303859) (by norm_num)
theorem B3091933 : Blo 1782092 3091933 := bbase (se 3 (by rfl) ⟨579737, by rfl⟩ : syracuseStep 3091933 = 1159475) (by norm_num)
theorem B2674157 : Blo 1782092 2674157 := bbase (se 3 (by rfl) ⟨501404, by rfl⟩ : syracuseStep 2674157 = 1002809) (by norm_num)
theorem B6016517 : Blo 1782092 6016517 := bbase (se 4 (by rfl) ⟨564048, by rfl⟩ : syracuseStep 6016517 = 1128097) (by norm_num)
theorem B2674181 : Blo 1782092 2674181 := bbase (se 4 (by rfl) ⟨250704, by rfl⟩ : syracuseStep 2674181 = 501409) (by norm_num)
theorem B3010061 : Blo 1782092 3010061 := bbase (se 3 (by rfl) ⟨564386, by rfl⟩ : syracuseStep 3010061 = 1128773) (by norm_num)
theorem B2674205 : Blo 1782092 2674205 := bbase (se 3 (by rfl) ⟨501413, by rfl⟩ : syracuseStep 2674205 = 1002827) (by norm_num)
theorem B3616285 : Blo 1782092 3616285 := bbase (se 3 (by rfl) ⟨678053, by rfl⟩ : syracuseStep 3616285 = 1356107) (by norm_num)
theorem B3214885 : Blo 1782092 3214885 := bbase (se 4 (by rfl) ⟨301395, by rfl⟩ : syracuseStep 3214885 = 602791) (by norm_num)
theorem B2674229 : Blo 1782092 2674229 := bbase (se 5 (by rfl) ⟨125354, by rfl⟩ : syracuseStep 2674229 = 250709) (by norm_num)
theorem B2256437 : Blo 1782092 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B2674253 : Blo 1782092 2674253 := bbase (se 3 (by rfl) ⟨501422, by rfl⟩ : syracuseStep 2674253 = 1002845) (by norm_num)
theorem B4951637 : Blo 1782092 4951637 := bbase (se 8 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 4951637 = 58027) (by norm_num)
theorem B2674277 : Blo 1782092 2674277 := bbase (se 4 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 2674277 = 501427) (by norm_num)
theorem B2256493 : Blo 1782092 2256493 := bbase (se 3 (by rfl) ⟨423092, by rfl⟩ : syracuseStep 2256493 = 846185) (by norm_num)
theorem B4574837 : Blo 1782092 4574837 := bbase (se 5 (by rfl) ⟨214445, by rfl⟩ : syracuseStep 4574837 = 428891) (by norm_num)
theorem B2674301 : Blo 1782092 2674301 := bbase (se 3 (by rfl) ⟨501431, by rfl⟩ : syracuseStep 2674301 = 1002863) (by norm_num)
theorem B3010189 : Blo 1782092 3010189 := bbase (se 3 (by rfl) ⟨564410, by rfl⟩ : syracuseStep 3010189 = 1128821) (by norm_num)
theorem B2674325 : Blo 1782092 2674325 := bbase (se 6 (by rfl) ⟨62679, by rfl⟩ : syracuseStep 2674325 = 125359) (by norm_num)
theorem B2674349 : Blo 1782092 2674349 := bbase (se 3 (by rfl) ⟨501440, by rfl⟩ : syracuseStep 2674349 = 1002881) (by norm_num)
theorem B1904305 : Blo 1782092 1904305 := bbase (se 2 (by rfl) ⟨714114, by rfl⟩ : syracuseStep 1904305 = 1428229) (by norm_num)
theorem B2674373 : Blo 1782092 2674373 := bbase (se 4 (by rfl) ⟨250722, by rfl⟩ : syracuseStep 2674373 = 501445) (by norm_num)
theorem B2256589 : Blo 1782092 2256589 := bbase (se 3 (by rfl) ⟨423110, by rfl⟩ : syracuseStep 2256589 = 846221) (by norm_num)
theorem B2674397 : Blo 1782092 2674397 := bbase (se 3 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 2674397 = 1002899) (by norm_num)
theorem B8564453 : Blo 1782092 8564453 := bbase (se 4 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 8564453 = 1605835) (by norm_num)
theorem B6770405 : Blo 1782092 6770405 := bbase (se 4 (by rfl) ⟨634725, by rfl⟩ : syracuseStep 6770405 = 1269451) (by norm_num)
theorem B3010277 : Blo 1782092 3010277 := bbase (se 4 (by rfl) ⟨282213, by rfl⟩ : syracuseStep 3010277 = 564427) (by norm_num)
theorem B2674421 : Blo 1782092 2674421 := bbase (se 5 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 2674421 = 250727) (by norm_num)
theorem B4009733 : Blo 1782092 4009733 := bbase (se 4 (by rfl) ⟨375912, by rfl⟩ : syracuseStep 4009733 = 751825) (by norm_num)
theorem B9023237 : Blo 1782092 9023237 := bbase (se 4 (by rfl) ⟨845928, by rfl⟩ : syracuseStep 9023237 = 1691857) (by norm_num)
theorem B2674445 : Blo 1782092 2674445 := bbase (se 3 (by rfl) ⟨501458, by rfl⟩ : syracuseStep 2674445 = 1002917) (by norm_num)
theorem B15224597 : Blo 1782092 15224597 := bbase (se 6 (by rfl) ⟨356826, by rfl⟩ : syracuseStep 15224597 = 713653) (by norm_num)
theorem B2674469 : Blo 1782092 2674469 := bbase (se 4 (by rfl) ⟨250731, by rfl⟩ : syracuseStep 2674469 = 501463) (by norm_num)
theorem B1904429 : Blo 1782092 1904429 := bbase (se 3 (by rfl) ⟨357080, by rfl⟩ : syracuseStep 1904429 = 714161) (by norm_num)
theorem B2674493 : Blo 1782092 2674493 := bbase (se 3 (by rfl) ⟨501467, by rfl⟩ : syracuseStep 2674493 = 1002935) (by norm_num)
theorem B4009805 : Blo 1782092 4009805 := bbase (se 3 (by rfl) ⟨751838, by rfl⟩ : syracuseStep 4009805 = 1503677) (by norm_num)
theorem B2674517 : Blo 1782092 2674517 := bbase (se 9 (by rfl) ⟨7835, by rfl⟩ : syracuseStep 2674517 = 15671) (by norm_num)
theorem B3010405 : Blo 1782092 3010405 := bbase (se 4 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 3010405 = 564451) (by norm_num)
theorem B2674541 : Blo 1782092 2674541 := bbase (se 3 (by rfl) ⟨501476, by rfl⟩ : syracuseStep 2674541 = 1002953) (by norm_num)
theorem B2256761 : Blo 1782092 2256761 := bbase (se 2 (by rfl) ⟨846285, by rfl⟩ : syracuseStep 2256761 = 1692571) (by norm_num)
theorem B2674565 : Blo 1782092 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B4009877 : Blo 1782092 4009877 := bbase (se 6 (by rfl) ⟨93981, by rfl⟩ : syracuseStep 4009877 = 187963) (by norm_num)
theorem B2674589 : Blo 1782092 2674589 := bbase (se 3 (by rfl) ⟨501485, by rfl⟩ : syracuseStep 2674589 = 1002971) (by norm_num)
theorem B2256817 : Blo 1782092 2256817 := bbase (se 2 (by rfl) ⟨846306, by rfl⟩ : syracuseStep 2256817 = 1692613) (by norm_num)
theorem B6016949 : Blo 1782092 6016949 := bbase (se 5 (by rfl) ⟨282044, by rfl⟩ : syracuseStep 6016949 = 564089) (by norm_num)
theorem B2674613 : Blo 1782092 2674613 := bbase (se 5 (by rfl) ⟨125372, by rfl⟩ : syracuseStep 2674613 = 250745) (by norm_num)
theorem B3010493 : Blo 1782092 3010493 := bbase (se 3 (by rfl) ⟨564467, by rfl⟩ : syracuseStep 3010493 = 1128935) (by norm_num)
theorem B2674637 : Blo 1782092 2674637 := bbase (se 3 (by rfl) ⟨501494, by rfl⟩ : syracuseStep 2674637 = 1002989) (by norm_num)
theorem B4009949 : Blo 1782092 4009949 := bbase (se 3 (by rfl) ⟨751865, by rfl⟩ : syracuseStep 4009949 = 1503731) (by norm_num)
theorem B2674661 : Blo 1782092 2674661 := bbase (se 4 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 2674661 = 501499) (by norm_num)
theorem B2854901 : Blo 1782092 2854901 := bbase (se 5 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 2854901 = 267647) (by norm_num)
theorem B2674685 : Blo 1782092 2674685 := bbase (se 3 (by rfl) ⟨501503, by rfl⟩ : syracuseStep 2674685 = 1003007) (by norm_num)
theorem B2256913 : Blo 1782092 2256913 := bbase (se 2 (by rfl) ⟨846342, by rfl⟩ : syracuseStep 2256913 = 1692685) (by norm_num)
theorem B2674709 : Blo 1782092 2674709 := bbase (se 6 (by rfl) ⟨62688, by rfl⟩ : syracuseStep 2674709 = 125377) (by norm_num)
theorem B8572949 : Blo 1782092 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B4010021 : Blo 1782092 4010021 := bbase (se 4 (by rfl) ⟨375939, by rfl⟩ : syracuseStep 4010021 = 751879) (by norm_num)
theorem B1904681 : Blo 1782092 1904681 := bbase (se 2 (by rfl) ⟨714255, by rfl⟩ : syracuseStep 1904681 = 1428511) (by norm_num)
theorem B2674733 : Blo 1782092 2674733 := bbase (se 3 (by rfl) ⟨501512, by rfl⟩ : syracuseStep 2674733 = 1003025) (by norm_num)
theorem B3010621 : Blo 1782092 3010621 := bbase (se 3 (by rfl) ⟨564491, by rfl⟩ : syracuseStep 3010621 = 1128983) (by norm_num)
theorem B2674757 : Blo 1782092 2674757 := bbase (se 4 (by rfl) ⟨250758, by rfl⟩ : syracuseStep 2674757 = 501517) (by norm_num)
theorem B7721045 : Blo 1782092 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B2674781 : Blo 1782092 2674781 := bbase (se 3 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 2674781 = 1003043) (by norm_num)
theorem B4010093 : Blo 1782092 4010093 := bbase (se 3 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 4010093 = 1503785) (by norm_num)
theorem B2674805 : Blo 1782092 2674805 := bbase (se 5 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 2674805 = 250763) (by norm_num)
theorem B2674829 : Blo 1782092 2674829 := bbase (se 3 (by rfl) ⟨501530, by rfl⟩ : syracuseStep 2674829 = 1003061) (by norm_num)
theorem B2674853 : Blo 1782092 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B4010165 : Blo 1782092 4010165 := bbase (se 5 (by rfl) ⟨187976, by rfl⟩ : syracuseStep 4010165 = 375953) (by norm_num)
theorem B2674877 : Blo 1782092 2674877 := bbase (se 3 (by rfl) ⟨501539, by rfl⟩ : syracuseStep 2674877 = 1003079) (by norm_num)
theorem B2257085 : Blo 1782092 2257085 := bbase (se 3 (by rfl) ⟨423203, by rfl⟩ : syracuseStep 2257085 = 846407) (by norm_num)
theorem B2855125 : Blo 1782092 2855125 := bbase (se 7 (by rfl) ⟨33458, by rfl⟩ : syracuseStep 2855125 = 66917) (by norm_num)
theorem B2674901 : Blo 1782092 2674901 := bbase (se 7 (by rfl) ⟨31346, by rfl⟩ : syracuseStep 2674901 = 62693) (by norm_num)
theorem B2674925 : Blo 1782092 2674925 := bbase (se 3 (by rfl) ⟨501548, by rfl⟩ : syracuseStep 2674925 = 1003097) (by norm_num)
theorem B2257141 : Blo 1782092 2257141 := bbase (se 5 (by rfl) ⟨105803, by rfl⟩ : syracuseStep 2257141 = 211607) (by norm_num)
theorem B4010237 : Blo 1782092 4010237 := bbase (se 3 (by rfl) ⟨751919, by rfl⟩ : syracuseStep 4010237 = 1503839) (by norm_num)
theorem B2674949 : Blo 1782092 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B2855189 : Blo 1782092 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B2674973 : Blo 1782092 2674973 := bbase (se 3 (by rfl) ⟨501557, by rfl⟩ : syracuseStep 2674973 = 1003115) (by norm_num)
theorem B2142497 : Blo 1782092 2142497 := bbase (se 2 (by rfl) ⟨803436, by rfl⟩ : syracuseStep 2142497 = 1606873) (by norm_num)
theorem B2674997 : Blo 1782092 2674997 := bbase (se 5 (by rfl) ⟨125390, by rfl⟩ : syracuseStep 2674997 = 250781) (by norm_num)
theorem B4010309 : Blo 1782092 4010309 := bbase (se 4 (by rfl) ⟨375966, by rfl⟩ : syracuseStep 4010309 = 751933) (by norm_num)
theorem B2675021 : Blo 1782092 2675021 := bbase (se 3 (by rfl) ⟨501566, by rfl⟩ : syracuseStep 2675021 = 1003133) (by norm_num)
theorem B2257237 : Blo 1782092 2257237 := bbase (se 10 (by rfl) ⟨3306, by rfl⟩ : syracuseStep 2257237 = 6613) (by norm_num)
theorem B6017381 : Blo 1782092 6017381 := bbase (se 4 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 6017381 = 1128259) (by norm_num)
theorem B2675045 : Blo 1782092 2675045 := bbase (se 4 (by rfl) ⟨250785, by rfl⟩ : syracuseStep 2675045 = 501571) (by norm_num)
theorem B2675069 : Blo 1782092 2675069 := bbase (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) (by norm_num)
theorem B4010381 : Blo 1782092 4010381 := bbase (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) (by norm_num)
theorem B2855317 : Blo 1782092 2855317 := bbase (se 6 (by rfl) ⟨66921, by rfl⟩ : syracuseStep 2855317 = 133843) (by norm_num)
theorem B2675093 : Blo 1782092 2675093 := bbase (se 6 (by rfl) ⟨62697, by rfl⟩ : syracuseStep 2675093 = 125395) (by norm_num)
theorem B2675117 : Blo 1782092 2675117 := bbase (se 3 (by rfl) ⟨501584, by rfl⟩ : syracuseStep 2675117 = 1003169) (by norm_num)
theorem B2675141 : Blo 1782092 2675141 := bbase (se 4 (by rfl) ⟨250794, by rfl⟩ : syracuseStep 2675141 = 501589) (by norm_num)
theorem B4010453 : Blo 1782092 4010453 := bbase (se 7 (by rfl) ⟨46997, by rfl⟩ : syracuseStep 4010453 = 93995) (by norm_num)
theorem B2675165 : Blo 1782092 2675165 := bbase (se 3 (by rfl) ⟨501593, by rfl⟩ : syracuseStep 2675165 = 1003187) (by norm_num)
theorem B1905125 : Blo 1782092 1905125 := bbase (se 4 (by rfl) ⟨178605, by rfl⟩ : syracuseStep 1905125 = 357211) (by norm_num)
theorem B2675189 : Blo 1782092 2675189 := bbase (se 5 (by rfl) ⟨125399, by rfl⟩ : syracuseStep 2675189 = 250799) (by norm_num)
theorem B2257409 : Blo 1782092 2257409 := bbase (se 2 (by rfl) ⟨846528, by rfl⟩ : syracuseStep 2257409 = 1693057) (by norm_num)
theorem B2675213 : Blo 1782092 2675213 := bbase (se 3 (by rfl) ⟨501602, by rfl⟩ : syracuseStep 2675213 = 1003205) (by norm_num)
theorem B4010525 : Blo 1782092 4010525 := bbase (se 3 (by rfl) ⟨751973, by rfl⟩ : syracuseStep 4010525 = 1503947) (by norm_num)
theorem B1806877 : Blo 1782092 1806877 := bbase (se 3 (by rfl) ⟨338789, by rfl⟩ : syracuseStep 1806877 = 677579) (by norm_num)
theorem B2675237 : Blo 1782092 2675237 := bbase (se 4 (by rfl) ⟨250803, by rfl⟩ : syracuseStep 2675237 = 501607) (by norm_num)
theorem B2257465 : Blo 1782092 2257465 := bbase (se 2 (by rfl) ⟨846549, by rfl⟩ : syracuseStep 2257465 = 1693099) (by norm_num)
theorem B2675261 : Blo 1782092 2675261 := bbase (se 3 (by rfl) ⟨501611, by rfl⟩ : syracuseStep 2675261 = 1003223) (by norm_num)
theorem B1929793 : Blo 1782092 1929793 := bbase (se 2 (by rfl) ⟨723672, by rfl⟩ : syracuseStep 1929793 = 1447345) (by norm_num)
theorem B11424341 : Blo 1782092 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B2675285 : Blo 1782092 2675285 := bbase (se 8 (by rfl) ⟨15675, by rfl⟩ : syracuseStep 2675285 = 31351) (by norm_num)
theorem B4010597 : Blo 1782092 4010597 := bbase (se 4 (by rfl) ⟨375993, by rfl⟩ : syracuseStep 4010597 = 751987) (by norm_num)
theorem B2675309 : Blo 1782092 2675309 := bbase (se 3 (by rfl) ⟨501620, by rfl⟩ : syracuseStep 2675309 = 1003241) (by norm_num)
theorem B2142833 : Blo 1782092 2142833 := bbase (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) (by norm_num)
theorem B2675333 : Blo 1782092 2675333 := bbase (se 4 (by rfl) ⟨250812, by rfl⟩ : syracuseStep 2675333 = 501625) (by norm_num)
theorem B5419669 : Blo 1782092 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B2257561 : Blo 1782092 2257561 := bbase (se 2 (by rfl) ⟨846585, by rfl⟩ : syracuseStep 2257561 = 1693171) (by norm_num)
theorem B2675357 : Blo 1782092 2675357 := bbase (se 3 (by rfl) ⟨501629, by rfl⟩ : syracuseStep 2675357 = 1003259) (by norm_num)
theorem B4010669 : Blo 1782092 4010669 := bbase (se 3 (by rfl) ⟨752000, by rfl⟩ : syracuseStep 4010669 = 1504001) (by norm_num)
theorem B2675381 : Blo 1782092 2675381 := bbase (se 5 (by rfl) ⟨125408, by rfl⟩ : syracuseStep 2675381 = 250817) (by norm_num)
theorem B2675405 : Blo 1782092 2675405 := bbase (se 3 (by rfl) ⟨501638, by rfl⟩ : syracuseStep 2675405 = 1003277) (by norm_num)
theorem B2675429 : Blo 1782092 2675429 := bbase (se 4 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 2675429 = 501643) (by norm_num)
theorem B2142949 : Blo 1782092 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B4010741 : Blo 1782092 4010741 := bbase (se 5 (by rfl) ⟨188003, by rfl⟩ : syracuseStep 4010741 = 376007) (by norm_num)
theorem B17134325 : Blo 1782092 17134325 := bbase (se 5 (by rfl) ⟨803171, by rfl⟩ : syracuseStep 17134325 = 1606343) (by norm_num)
theorem B2675453 : Blo 1782092 2675453 := bbase (se 3 (by rfl) ⟨501647, by rfl⟩ : syracuseStep 2675453 = 1003295) (by norm_num)
theorem B6017813 : Blo 1782092 6017813 := bbase (se 6 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 6017813 = 282085) (by norm_num)
theorem B2675477 : Blo 1782092 2675477 := bbase (se 6 (by rfl) ⟨62706, by rfl⟩ : syracuseStep 2675477 = 125413) (by norm_num)
theorem B2675501 : Blo 1782092 2675501 := bbase (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) (by norm_num)
theorem B2143021 : Blo 1782092 2143021 := bbase (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) (by norm_num)
theorem B1807157 : Blo 1782092 1807157 := bbase (se 5 (by rfl) ⟨84710, by rfl⟩ : syracuseStep 1807157 = 169421) (by norm_num)
theorem B4010813 : Blo 1782092 4010813 := bbase (se 3 (by rfl) ⟨752027, by rfl⟩ : syracuseStep 4010813 = 1504055) (by norm_num)
theorem B2675525 : Blo 1782092 2675525 := bbase (se 4 (by rfl) ⟨250830, by rfl⟩ : syracuseStep 2675525 = 501661) (by norm_num)
theorem B2143045 : Blo 1782092 2143045 := bbase (se 4 (by rfl) ⟨200910, by rfl⟩ : syracuseStep 2143045 = 401821) (by norm_num)
theorem B2257733 : Blo 1782092 2257733 := bbase (se 4 (by rfl) ⟨211662, by rfl⟩ : syracuseStep 2257733 = 423325) (by norm_num)
theorem B2675549 : Blo 1782092 2675549 := bbase (se 3 (by rfl) ⟨501665, by rfl⟩ : syracuseStep 2675549 = 1003331) (by norm_num)
theorem B2675573 : Blo 1782092 2675573 := bbase (se 5 (by rfl) ⟨125417, by rfl⟩ : syracuseStep 2675573 = 250835) (by norm_num)
theorem B2257789 : Blo 1782092 2257789 := bbase (se 3 (by rfl) ⟨423335, by rfl⟩ : syracuseStep 2257789 = 846671) (by norm_num)
theorem B4010885 : Blo 1782092 4010885 := bbase (se 4 (by rfl) ⟨376020, by rfl⟩ : syracuseStep 4010885 = 752041) (by norm_num)
theorem B1807237 : Blo 1782092 1807237 := bbase (se 4 (by rfl) ⟨169428, by rfl⟩ : syracuseStep 1807237 = 338857) (by norm_num)
theorem B2675597 : Blo 1782092 2675597 := bbase (se 3 (by rfl) ⟨501674, by rfl⟩ : syracuseStep 2675597 = 1003349) (by norm_num)
theorem B5714837 : Blo 1782092 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B2675621 : Blo 1782092 2675621 := bbase (se 4 (by rfl) ⟨250839, by rfl⟩ : syracuseStep 2675621 = 501679) (by norm_num)
theorem B2675645 : Blo 1782092 2675645 := bbase (se 3 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 2675645 = 1003367) (by norm_num)
theorem B4010957 : Blo 1782092 4010957 := bbase (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) (by norm_num)
theorem B34280405 : Blo 1782092 34280405 := bbase (se 7 (by rfl) ⟨401723, by rfl⟩ : syracuseStep 34280405 = 803447) (by norm_num)
theorem B2675669 : Blo 1782092 2675669 := bbase (se 7 (by rfl) ⟨31355, by rfl⟩ : syracuseStep 2675669 = 62711) (by norm_num)
theorem B2143189 : Blo 1782092 2143189 := bbase (se 7 (by rfl) ⟨25115, by rfl⟩ : syracuseStep 2143189 = 50231) (by norm_num)
theorem B2257885 : Blo 1782092 2257885 := bbase (se 3 (by rfl) ⟨423353, by rfl⟩ : syracuseStep 2257885 = 846707) (by norm_num)
theorem B2675693 : Blo 1782092 2675693 := bbase (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) (by norm_num)
theorem B2675717 : Blo 1782092 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B9024533 : Blo 1782092 9024533 := bbase (se 6 (by rfl) ⟨211512, by rfl⟩ : syracuseStep 9024533 = 423025) (by norm_num)
theorem B4011029 : Blo 1782092 4011029 := bbase (se 6 (by rfl) ⟨94008, by rfl⟩ : syracuseStep 4011029 = 188017) (by norm_num)
theorem B5714965 : Blo 1782092 5714965 := bbase (se 6 (by rfl) ⟨133944, by rfl⟩ : syracuseStep 5714965 = 267889) (by norm_num)
theorem B2675741 : Blo 1782092 2675741 := bbase (se 3 (by rfl) ⟨501701, by rfl⟩ : syracuseStep 2675741 = 1003403) (by norm_num)
theorem B7935013 : Blo 1782092 7935013 := bbase (se 4 (by rfl) ⟨743907, by rfl⟩ : syracuseStep 7935013 = 1487815) (by norm_num)
theorem B3806261 : Blo 1782092 3806261 := bbase (se 5 (by rfl) ⟨178418, by rfl⟩ : syracuseStep 3806261 = 356837) (by norm_num)
theorem B2675765 : Blo 1782092 2675765 := bbase (se 5 (by rfl) ⟨125426, by rfl⟩ : syracuseStep 2675765 = 250853) (by norm_num)
theorem B2675789 : Blo 1782092 2675789 := bbase (se 3 (by rfl) ⟨501710, by rfl⟩ : syracuseStep 2675789 = 1003421) (by norm_num)
theorem B4011101 : Blo 1782092 4011101 := bbase (se 3 (by rfl) ⟨752081, by rfl⟩ : syracuseStep 4011101 = 1504163) (by norm_num)
theorem B2675813 : Blo 1782092 2675813 := bbase (se 4 (by rfl) ⟨250857, by rfl⟩ : syracuseStep 2675813 = 501715) (by norm_num)
theorem B2675837 : Blo 1782092 2675837 := bbase (se 3 (by rfl) ⟨501719, by rfl⟩ : syracuseStep 2675837 = 1003439) (by norm_num)
theorem B2675861 : Blo 1782092 2675861 := bbase (se 6 (by rfl) ⟨62715, by rfl⟩ : syracuseStep 2675861 = 125431) (by norm_num)
theorem B4011173 : Blo 1782092 4011173 := bbase (se 4 (by rfl) ⟨376047, by rfl⟩ : syracuseStep 4011173 = 752095) (by norm_num)
theorem B1807529 : Blo 1782092 1807529 := bbase (se 2 (by rfl) ⟨677823, by rfl⟩ : syracuseStep 1807529 = 1355647) (by norm_num)
theorem B2675885 : Blo 1782092 2675885 := bbase (se 3 (by rfl) ⟨501728, by rfl⟩ : syracuseStep 2675885 = 1003457) (by norm_num)
theorem B6018245 : Blo 1782092 6018245 := bbase (se 4 (by rfl) ⟨564210, by rfl⟩ : syracuseStep 6018245 = 1128421) (by norm_num)
theorem B2675909 : Blo 1782092 2675909 := bbase (se 4 (by rfl) ⟨250866, by rfl⟩ : syracuseStep 2675909 = 501733) (by norm_num)
theorem B2675933 : Blo 1782092 2675933 := bbase (se 3 (by rfl) ⟨501737, by rfl⟩ : syracuseStep 2675933 = 1003475) (by norm_num)
theorem B4011245 : Blo 1782092 4011245 := bbase (se 3 (by rfl) ⟨752108, by rfl⟩ : syracuseStep 4011245 = 1504217) (by norm_num)
theorem B2675957 : Blo 1782092 2675957 := bbase (se 5 (by rfl) ⟨125435, by rfl⟩ : syracuseStep 2675957 = 250871) (by norm_num)
theorem B2675981 : Blo 1782092 2675981 := bbase (se 3 (by rfl) ⟨501746, by rfl⟩ : syracuseStep 2675981 = 1003493) (by norm_num)
theorem B2676005 : Blo 1782092 2676005 := bbase (se 4 (by rfl) ⟨250875, by rfl⟩ : syracuseStep 2676005 = 501751) (by norm_num)
theorem B4011317 : Blo 1782092 4011317 := bbase (se 5 (by rfl) ⟨188030, by rfl⟩ : syracuseStep 4011317 = 376061) (by norm_num)
theorem B2676029 : Blo 1782092 2676029 := bbase (se 3 (by rfl) ⟨501755, by rfl⟩ : syracuseStep 2676029 = 1003511) (by norm_num)
theorem B2676053 : Blo 1782092 2676053 := bbase (se 15 (by rfl) ⟨122, by rfl⟩ : syracuseStep 2676053 = 245) (by norm_num)
theorem B2676077 : Blo 1782092 2676077 := bbase (se 3 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 2676077 = 1003529) (by norm_num)
theorem B16258421 : Blo 1782092 16258421 := bbase (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) (by norm_num)
theorem B4011389 : Blo 1782092 4011389 := bbase (se 3 (by rfl) ⟨752135, by rfl⟩ : syracuseStep 4011389 = 1504271) (by norm_num)
theorem B2676101 : Blo 1782092 2676101 := bbase (se 4 (by rfl) ⟨250884, by rfl⟩ : syracuseStep 2676101 = 501769) (by norm_num)
theorem B31315349 : Blo 1782092 31315349 := bbase (se 6 (by rfl) ⟨733953, by rfl⟩ : syracuseStep 31315349 = 1467907) (by norm_num)
theorem B2676125 : Blo 1782092 2676125 := bbase (se 3 (by rfl) ⟨501773, by rfl⟩ : syracuseStep 2676125 = 1003547) (by norm_num)
theorem B4511173 : Blo 1782092 4511173 := bbase (se 4 (by rfl) ⟨422922, by rfl⟩ : syracuseStep 4511173 = 845845) (by norm_num)
theorem B4011461 : Blo 1782092 4011461 := bbase (se 4 (by rfl) ⟨376074, by rfl⟩ : syracuseStep 4011461 = 752149) (by norm_num)
theorem B4011533 : Blo 1782092 4011533 := bbase (se 3 (by rfl) ⟨752162, by rfl⟩ : syracuseStep 4011533 = 1504325) (by norm_num)
theorem B25712149 : Blo 1782092 25712149 := bbase (se 6 (by rfl) ⟨602628, by rfl⟩ : syracuseStep 25712149 = 1205257) (by norm_num)
theorem B4511285 : Blo 1782092 4511285 := bbase (se 5 (by rfl) ⟨211466, by rfl⟩ : syracuseStep 4511285 = 422933) (by norm_num)
theorem B4011605 : Blo 1782092 4011605 := bbase (se 8 (by rfl) ⟨23505, by rfl⟩ : syracuseStep 4011605 = 47011) (by norm_num)
theorem B2856541 : Blo 1782092 2856541 := bbase (se 3 (by rfl) ⟨535601, by rfl⟩ : syracuseStep 2856541 = 1071203) (by norm_num)
theorem B6018677 : Blo 1782092 6018677 := bbase (se 5 (by rfl) ⟨282125, by rfl⟩ : syracuseStep 6018677 = 564251) (by norm_num)
theorem B4011677 : Blo 1782092 4011677 := bbase (se 3 (by rfl) ⟨752189, by rfl⟩ : syracuseStep 4011677 = 1504379) (by norm_num)
theorem B7616213 : Blo 1782092 7616213 := bbase (se 7 (by rfl) ⟨89252, by rfl⟩ : syracuseStep 7616213 = 178505) (by norm_num)
theorem B4011749 : Blo 1782092 4011749 := bbase (se 4 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 4011749 = 752203) (by norm_num)
theorem B4511477 : Blo 1782092 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B3807013 : Blo 1782092 3807013 := bbase (se 4 (by rfl) ⟨356907, by rfl⟩ : syracuseStep 3807013 = 713815) (by norm_num)
theorem B6772517 : Blo 1782092 6772517 := bbase (se 4 (by rfl) ⟨634923, by rfl⟩ : syracuseStep 6772517 = 1269847) (by norm_num)
theorem B4011821 : Blo 1782092 4011821 := bbase (se 3 (by rfl) ⟨752216, by rfl⟩ : syracuseStep 4011821 = 1504433) (by norm_num)
theorem B8132405 : Blo 1782092 8132405 := bbase (se 5 (by rfl) ⟨381206, by rfl⟩ : syracuseStep 8132405 = 762413) (by norm_num)
theorem B15439733 : Blo 1782092 15439733 := bbase (se 5 (by rfl) ⟨723737, by rfl⟩ : syracuseStep 15439733 = 1447475) (by norm_num)
theorem B4011893 : Blo 1782092 4011893 := bbase (se 5 (by rfl) ⟨188057, by rfl⟩ : syracuseStep 4011893 = 376115) (by norm_num)
theorem B5420933 : Blo 1782092 5420933 := bbase (se 4 (by rfl) ⟨508212, by rfl⟩ : syracuseStep 5420933 = 1016425) (by norm_num)
theorem B2004889 : Blo 1782092 2004889 := bbase (se 2 (by rfl) ⟨751833, by rfl⟩ : syracuseStep 2004889 = 1503667) (by norm_num)
theorem B3807157 : Blo 1782092 3807157 := bbase (se 5 (by rfl) ⟨178460, by rfl⟩ : syracuseStep 3807157 = 356921) (by norm_num)
theorem B2004925 : Blo 1782092 2004925 := bbase (se 3 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 2004925 = 751847) (by norm_num)
theorem B4011965 : Blo 1782092 4011965 := bbase (se 3 (by rfl) ⟨752243, by rfl⟩ : syracuseStep 4011965 = 1504487) (by norm_num)
theorem B2004961 : Blo 1782092 2004961 := bbase (se 2 (by rfl) ⟨751860, by rfl⟩ : syracuseStep 2004961 = 1503721) (by norm_num)
theorem B7616501 : Blo 1782092 7616501 := bbase (se 5 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 7616501 = 714047) (by norm_num)
theorem B2004997 : Blo 1782092 2004997 := bbase (se 4 (by rfl) ⟨187968, by rfl⟩ : syracuseStep 2004997 = 375937) (by norm_num)
theorem B4012037 : Blo 1782092 4012037 := bbase (se 4 (by rfl) ⟨376128, by rfl⟩ : syracuseStep 4012037 = 752257) (by norm_num)
theorem B6019109 : Blo 1782092 6019109 := bbase (se 4 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 6019109 = 1128583) (by norm_num)
theorem B2005033 : Blo 1782092 2005033 := bbase (se 2 (by rfl) ⟨751887, by rfl⟩ : syracuseStep 2005033 = 1503775) (by norm_num)
theorem B6772805 : Blo 1782092 6772805 := bbase (se 4 (by rfl) ⟨634950, by rfl⟩ : syracuseStep 6772805 = 1269901) (by norm_num)
theorem B2005069 : Blo 1782092 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B4511821 : Blo 1782092 4511821 := bbase (se 3 (by rfl) ⟨845966, by rfl⟩ : syracuseStep 4511821 = 1691933) (by norm_num)
theorem B4012109 : Blo 1782092 4012109 := bbase (se 3 (by rfl) ⟨752270, by rfl⟩ : syracuseStep 4012109 = 1504541) (by norm_num)
theorem B2537581 : Blo 1782092 2537581 := bbase (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) (by norm_num)
theorem B2005105 : Blo 1782092 2005105 := bbase (se 2 (by rfl) ⟨751914, by rfl⟩ : syracuseStep 2005105 = 1503829) (by norm_num)
theorem B2005141 : Blo 1782092 2005141 := bbase (se 6 (by rfl) ⟨46995, by rfl⟩ : syracuseStep 2005141 = 93991) (by norm_num)
theorem B4012181 : Blo 1782092 4012181 := bbase (se 6 (by rfl) ⟨94035, by rfl⟩ : syracuseStep 4012181 = 188071) (by norm_num)
theorem B2005177 : Blo 1782092 2005177 := bbase (se 2 (by rfl) ⟨751941, by rfl⟩ : syracuseStep 2005177 = 1503883) (by norm_num)
theorem B4511933 : Blo 1782092 4511933 := bbase (se 3 (by rfl) ⟨845987, by rfl⟩ : syracuseStep 4511933 = 1691975) (by norm_num)
theorem B4577485 : Blo 1782092 4577485 := bbase (se 3 (by rfl) ⟨858278, by rfl⟩ : syracuseStep 4577485 = 1716557) (by norm_num)
theorem B2005213 : Blo 1782092 2005213 := bbase (se 3 (by rfl) ⟨375977, by rfl⟩ : syracuseStep 2005213 = 751955) (by norm_num)
theorem B4012253 : Blo 1782092 4012253 := bbase (se 3 (by rfl) ⟨752297, by rfl⟩ : syracuseStep 4012253 = 1504595) (by norm_num)
theorem B2857213 : Blo 1782092 2857213 := bbase (se 3 (by rfl) ⟨535727, by rfl⟩ : syracuseStep 2857213 = 1071455) (by norm_num)
theorem B2005249 : Blo 1782092 2005249 := bbase (se 2 (by rfl) ⟨751968, by rfl⟩ : syracuseStep 2005249 = 1503937) (by norm_num)
theorem B2005285 : Blo 1782092 2005285 := bbase (se 4 (by rfl) ⟨187995, by rfl⟩ : syracuseStep 2005285 = 375991) (by norm_num)
theorem B9025829 : Blo 1782092 9025829 := bbase (se 4 (by rfl) ⟨846171, by rfl⟩ : syracuseStep 9025829 = 1692343) (by norm_num)
theorem B4012325 : Blo 1782092 4012325 := bbase (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) (by norm_num)
theorem B3807533 : Blo 1782092 3807533 := bbase (se 3 (by rfl) ⟨713912, by rfl⟩ : syracuseStep 3807533 = 1427825) (by norm_num)
theorem B2005321 : Blo 1782092 2005321 := bbase (se 2 (by rfl) ⟨751995, by rfl⟩ : syracuseStep 2005321 = 1503991) (by norm_num)
theorem B5077349 : Blo 1782092 5077349 := bbase (se 4 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 5077349 = 952003) (by norm_num)
theorem B2005357 : Blo 1782092 2005357 := bbase (se 3 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 2005357 = 752009) (by norm_num)
theorem B4012397 : Blo 1782092 4012397 := bbase (se 3 (by rfl) ⟨752324, by rfl⟩ : syracuseStep 4012397 = 1504649) (by norm_num)
theorem B4512125 : Blo 1782092 4512125 := bbase (se 3 (by rfl) ⟨846023, by rfl⟩ : syracuseStep 4512125 = 1692047) (by norm_num)
theorem B2005393 : Blo 1782092 2005393 := bbase (se 2 (by rfl) ⟨752022, by rfl⟩ : syracuseStep 2005393 = 1504045) (by norm_num)
theorem B6429077 : Blo 1782092 6429077 := bbase (se 6 (by rfl) ⟨150681, by rfl⟩ : syracuseStep 6429077 = 301363) (by norm_num)
theorem B2005429 : Blo 1782092 2005429 := bbase (se 5 (by rfl) ⟨94004, by rfl⟩ : syracuseStep 2005429 = 188009) (by norm_num)
theorem B4012469 : Blo 1782092 4012469 := bbase (se 5 (by rfl) ⟨188084, by rfl⟩ : syracuseStep 4012469 = 376169) (by norm_num)
theorem B6019541 : Blo 1782092 6019541 := bbase (se 7 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 6019541 = 141083) (by norm_num)
theorem B2005465 : Blo 1782092 2005465 := bbase (se 2 (by rfl) ⟨752049, by rfl⟩ : syracuseStep 2005465 = 1504099) (by norm_num)
theorem B2005501 : Blo 1782092 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B4012541 : Blo 1782092 4012541 := bbase (se 3 (by rfl) ⟨752351, by rfl⟩ : syracuseStep 4012541 = 1504703) (by norm_num)
theorem B2005537 : Blo 1782092 2005537 := bbase (se 2 (by rfl) ⟨752076, by rfl⟩ : syracuseStep 2005537 = 1504153) (by norm_num)
theorem B2005573 : Blo 1782092 2005573 := bbase (se 4 (by rfl) ⟨188022, by rfl⟩ : syracuseStep 2005573 = 376045) (by norm_num)
theorem B4012613 : Blo 1782092 4012613 := bbase (se 4 (by rfl) ⟨376182, by rfl⟩ : syracuseStep 4012613 = 752365) (by norm_num)
theorem B2005609 : Blo 1782092 2005609 := bbase (se 2 (by rfl) ⟨752103, by rfl⟩ : syracuseStep 2005609 = 1504207) (by norm_num)
theorem B2005645 : Blo 1782092 2005645 := bbase (se 3 (by rfl) ⟨376058, by rfl⟩ : syracuseStep 2005645 = 752117) (by norm_num)
theorem B4012685 : Blo 1782092 4012685 := bbase (se 3 (by rfl) ⟨752378, by rfl⟩ : syracuseStep 4012685 = 1504757) (by norm_num)
theorem B3807901 : Blo 1782092 3807901 := bbase (se 3 (by rfl) ⟨713981, by rfl⟩ : syracuseStep 3807901 = 1427963) (by norm_num)
theorem B2005681 : Blo 1782092 2005681 := bbase (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) (by norm_num)
theorem B6429365 : Blo 1782092 6429365 := bbase (se 5 (by rfl) ⟨301376, by rfl⟩ : syracuseStep 6429365 = 602753) (by norm_num)
theorem B2538173 : Blo 1782092 2538173 := bbase (se 3 (by rfl) ⟨475907, by rfl⟩ : syracuseStep 2538173 = 951815) (by norm_num)
theorem B4512469 : Blo 1782092 4512469 := bbase (se 7 (by rfl) ⟨52880, by rfl⟩ : syracuseStep 4512469 = 105761) (by norm_num)
theorem B2005717 : Blo 1782092 2005717 := bbase (se 7 (by rfl) ⟨23504, by rfl⟩ : syracuseStep 2005717 = 47009) (by norm_num)
theorem B4012757 : Blo 1782092 4012757 := bbase (se 7 (by rfl) ⟨47024, by rfl⟩ : syracuseStep 4012757 = 94049) (by norm_num)
theorem B7617253 : Blo 1782092 7617253 := bbase (se 4 (by rfl) ⟨714117, by rfl⟩ : syracuseStep 7617253 = 1428235) (by norm_num)
theorem B2005753 : Blo 1782092 2005753 := bbase (se 2 (by rfl) ⟨752157, by rfl⟩ : syracuseStep 2005753 = 1504315) (by norm_num)
theorem B2538253 : Blo 1782092 2538253 := bbase (se 3 (by rfl) ⟨475922, by rfl⟩ : syracuseStep 2538253 = 951845) (by norm_num)
theorem B2005789 : Blo 1782092 2005789 := bbase (se 3 (by rfl) ⟨376085, by rfl⟩ : syracuseStep 2005789 = 752171) (by norm_num)
theorem B4012829 : Blo 1782092 4012829 := bbase (se 3 (by rfl) ⟨752405, by rfl⟩ : syracuseStep 4012829 = 1504811) (by norm_num)
theorem B2005825 : Blo 1782092 2005825 := bbase (se 2 (by rfl) ⟨752184, by rfl⟩ : syracuseStep 2005825 = 1504369) (by norm_num)
theorem B4512581 : Blo 1782092 4512581 := bbase (se 4 (by rfl) ⟨423054, by rfl⟩ : syracuseStep 4512581 = 846109) (by norm_num)
theorem B2005861 : Blo 1782092 2005861 := bbase (se 4 (by rfl) ⟨188049, by rfl⟩ : syracuseStep 2005861 = 376099) (by norm_num)
theorem B4012901 : Blo 1782092 4012901 := bbase (se 4 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 4012901 = 752419) (by norm_num)
theorem B2538373 : Blo 1782092 2538373 := bbase (se 4 (by rfl) ⟨237972, by rfl⟩ : syracuseStep 2538373 = 475945) (by norm_num)
theorem B6019973 : Blo 1782092 6019973 := bbase (se 4 (by rfl) ⟨564372, by rfl⟩ : syracuseStep 6019973 = 1128745) (by norm_num)
theorem B2005897 : Blo 1782092 2005897 := bbase (se 2 (by rfl) ⟨752211, by rfl⟩ : syracuseStep 2005897 = 1504423) (by norm_num)
theorem B2005933 : Blo 1782092 2005933 := bbase (se 3 (by rfl) ⟨376112, by rfl⟩ : syracuseStep 2005933 = 752225) (by norm_num)
theorem B4012973 : Blo 1782092 4012973 := bbase (se 3 (by rfl) ⟨752432, by rfl⟩ : syracuseStep 4012973 = 1504865) (by norm_num)
theorem B2005969 : Blo 1782092 2005969 := bbase (se 2 (by rfl) ⟨752238, by rfl⟩ : syracuseStep 2005969 = 1504477) (by norm_num)
theorem B2538469 : Blo 1782092 2538469 := bbase (se 4 (by rfl) ⟨237981, by rfl⟩ : syracuseStep 2538469 = 475963) (by norm_num)
theorem B2006005 : Blo 1782092 2006005 := bbase (se 5 (by rfl) ⟨94031, by rfl⟩ : syracuseStep 2006005 = 188063) (by norm_num)
theorem B4013045 : Blo 1782092 4013045 := bbase (se 5 (by rfl) ⟨188111, by rfl⟩ : syracuseStep 4013045 = 376223) (by norm_num)
theorem B4512773 : Blo 1782092 4512773 := bbase (se 4 (by rfl) ⟨423072, by rfl⟩ : syracuseStep 4512773 = 846145) (by norm_num)
theorem B10296341 : Blo 1782092 10296341 := bbase (se 6 (by rfl) ⟨241320, by rfl⟩ : syracuseStep 10296341 = 482641) (by norm_num)
theorem B2006041 : Blo 1782092 2006041 := bbase (se 2 (by rfl) ⟨752265, by rfl⟩ : syracuseStep 2006041 = 1504531) (by norm_num)
theorem B4283437 : Blo 1782092 4283437 := bbase (se 3 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 4283437 = 1606289) (by norm_num)
theorem B2006077 : Blo 1782092 2006077 := bbase (se 3 (by rfl) ⟨376139, by rfl⟩ : syracuseStep 2006077 = 752279) (by norm_num)
theorem B4013117 : Blo 1782092 4013117 := bbase (se 3 (by rfl) ⟨752459, by rfl⟩ : syracuseStep 4013117 = 1504919) (by norm_num)
theorem B2006113 : Blo 1782092 2006113 := bbase (se 2 (by rfl) ⟨752292, by rfl⟩ : syracuseStep 2006113 = 1504585) (by norm_num)
theorem B2006149 : Blo 1782092 2006149 := bbase (se 4 (by rfl) ⟨188076, by rfl⟩ : syracuseStep 2006149 = 376153) (by norm_num)
theorem B4013189 : Blo 1782092 4013189 := bbase (se 4 (by rfl) ⟨376236, by rfl⟩ : syracuseStep 4013189 = 752473) (by norm_num)
theorem B6511765 : Blo 1782092 6511765 := bbase (se 6 (by rfl) ⟨152619, by rfl⟩ : syracuseStep 6511765 = 305239) (by norm_num)
theorem B2006185 : Blo 1782092 2006185 := bbase (se 2 (by rfl) ⟨752319, by rfl⟩ : syracuseStep 2006185 = 1504639) (by norm_num)
theorem B2006221 : Blo 1782092 2006221 := bbase (se 3 (by rfl) ⟨376166, by rfl⟩ : syracuseStep 2006221 = 752333) (by norm_num)
theorem B4013261 : Blo 1782092 4013261 := bbase (se 3 (by rfl) ⟨752486, by rfl⟩ : syracuseStep 4013261 = 1504973) (by norm_num)
theorem B2006257 : Blo 1782092 2006257 := bbase (se 2 (by rfl) ⟨752346, by rfl⟩ : syracuseStep 2006257 = 1504693) (by norm_num)
theorem B2006293 : Blo 1782092 2006293 := bbase (se 6 (by rfl) ⟨47022, by rfl⟩ : syracuseStep 2006293 = 94045) (by norm_num)
theorem B4013333 : Blo 1782092 4013333 := bbase (se 6 (by rfl) ⟨94062, by rfl⟩ : syracuseStep 4013333 = 188125) (by norm_num)
theorem B6020405 : Blo 1782092 6020405 := bbase (se 5 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 6020405 = 564413) (by norm_num)
theorem B2006329 : Blo 1782092 2006329 := bbase (se 2 (by rfl) ⟨752373, by rfl⟩ : syracuseStep 2006329 = 1504747) (by norm_num)
theorem B34258261 : Blo 1782092 34258261 := bbase (se 11 (by rfl) ⟨25091, by rfl⟩ : syracuseStep 34258261 = 50183) (by norm_num)
theorem B4513117 : Blo 1782092 4513117 := bbase (se 3 (by rfl) ⟨846209, by rfl⟩ : syracuseStep 4513117 = 1692419) (by norm_num)
theorem B2006365 : Blo 1782092 2006365 := bbase (se 3 (by rfl) ⟨376193, by rfl⟩ : syracuseStep 2006365 = 752387) (by norm_num)
theorem B4013405 : Blo 1782092 4013405 := bbase (se 3 (by rfl) ⟨752513, by rfl⟩ : syracuseStep 4013405 = 1505027) (by norm_num)
theorem B2006401 : Blo 1782092 2006401 := bbase (se 2 (by rfl) ⟨752400, by rfl⟩ : syracuseStep 2006401 = 1504801) (by norm_num)
theorem B2006437 : Blo 1782092 2006437 := bbase (se 4 (by rfl) ⟨188103, by rfl⟩ : syracuseStep 2006437 = 376207) (by norm_num)
theorem B4013477 : Blo 1782092 4013477 := bbase (se 4 (by rfl) ⟨376263, by rfl⟩ : syracuseStep 4013477 = 752527) (by norm_num)
theorem B7617989 : Blo 1782092 7617989 := bbase (se 4 (by rfl) ⟨714186, by rfl⟩ : syracuseStep 7617989 = 1428373) (by norm_num)
theorem B2006473 : Blo 1782092 2006473 := bbase (se 2 (by rfl) ⟨752427, by rfl⟩ : syracuseStep 2006473 = 1504855) (by norm_num)
theorem B4513229 : Blo 1782092 4513229 := bbase (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) (by norm_num)
theorem B2538965 : Blo 1782092 2538965 := bbase (se 7 (by rfl) ⟨29753, by rfl⟩ : syracuseStep 2538965 = 59507) (by norm_num)
theorem B2006509 : Blo 1782092 2006509 := bbase (se 3 (by rfl) ⟨376220, by rfl⟩ : syracuseStep 2006509 = 752441) (by norm_num)
theorem B4013549 : Blo 1782092 4013549 := bbase (se 3 (by rfl) ⟨752540, by rfl⟩ : syracuseStep 4013549 = 1505081) (by norm_num)
theorem B11427317 : Blo 1782092 11427317 := bbase (se 5 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 11427317 = 1071311) (by norm_num)
theorem B5078533 : Blo 1782092 5078533 := bbase (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) (by norm_num)
theorem B2006545 : Blo 1782092 2006545 := bbase (se 2 (by rfl) ⟨752454, by rfl⟩ : syracuseStep 2006545 = 1504909) (by norm_num)
theorem B9027125 : Blo 1782092 9027125 := bbase (se 5 (by rfl) ⟨423146, by rfl⟩ : syracuseStep 9027125 = 846293) (by norm_num)
theorem B2006581 : Blo 1782092 2006581 := bbase (se 5 (by rfl) ⟨94058, by rfl⟩ : syracuseStep 2006581 = 188117) (by norm_num)
theorem B4013621 : Blo 1782092 4013621 := bbase (se 5 (by rfl) ⟨188138, by rfl⟩ : syracuseStep 4013621 = 376277) (by norm_num)
theorem B15236693 : Blo 1782092 15236693 := bbase (se 8 (by rfl) ⟨89277, by rfl⟩ : syracuseStep 15236693 = 178555) (by norm_num)
theorem B2006617 : Blo 1782092 2006617 := bbase (se 2 (by rfl) ⟨752481, by rfl⟩ : syracuseStep 2006617 = 1504963) (by norm_num)
theorem B2006653 : Blo 1782092 2006653 := bbase (se 3 (by rfl) ⟨376247, by rfl⟩ : syracuseStep 2006653 = 752495) (by norm_num)
theorem B4013693 : Blo 1782092 4013693 := bbase (se 3 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 4013693 = 1505135) (by norm_num)
theorem B4513421 : Blo 1782092 4513421 := bbase (se 3 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 4513421 = 1692533) (by norm_num)
theorem B4284053 : Blo 1782092 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B2006689 : Blo 1782092 2006689 := bbase (se 2 (by rfl) ⟨752508, by rfl⟩ : syracuseStep 2006689 = 1505017) (by norm_num)
theorem B5078693 : Blo 1782092 5078693 := bbase (se 4 (by rfl) ⟨476127, by rfl⟩ : syracuseStep 5078693 = 952255) (by norm_num)
theorem B2006725 : Blo 1782092 2006725 := bbase (se 4 (by rfl) ⟨188130, by rfl⟩ : syracuseStep 2006725 = 376261) (by norm_num)
theorem B4013765 : Blo 1782092 4013765 := bbase (se 4 (by rfl) ⟨376290, by rfl⟩ : syracuseStep 4013765 = 752581) (by norm_num)
theorem B6020837 : Blo 1782092 6020837 := bbase (se 4 (by rfl) ⟨564453, by rfl⟩ : syracuseStep 6020837 = 1128907) (by norm_num)
theorem B2006761 : Blo 1782092 2006761 := bbase (se 2 (by rfl) ⟨752535, by rfl⟩ : syracuseStep 2006761 = 1505071) (by norm_num)
theorem B2006797 : Blo 1782092 2006797 := bbase (se 3 (by rfl) ⟨376274, by rfl⟩ : syracuseStep 2006797 = 752549) (by norm_num)
theorem B4013837 : Blo 1782092 4013837 := bbase (se 3 (by rfl) ⟨752594, by rfl⟩ : syracuseStep 4013837 = 1505189) (by norm_num)
theorem B2006833 : Blo 1782092 2006833 := bbase (se 2 (by rfl) ⟨752562, by rfl⟩ : syracuseStep 2006833 = 1505125) (by norm_num)
theorem B75210581 : Blo 1782092 75210581 := bbase (se 9 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 75210581 = 440687) (by norm_num)
theorem B4284245 : Blo 1782092 4284245 := bbase (se 9 (by rfl) ⟨12551, by rfl⟩ : syracuseStep 4284245 = 25103) (by norm_num)
theorem B2006869 : Blo 1782092 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B4013909 : Blo 1782092 4013909 := bbase (se 9 (by rfl) ⟨11759, by rfl⟩ : syracuseStep 4013909 = 23519) (by norm_num)
theorem B2006905 : Blo 1782092 2006905 := bbase (se 2 (by rfl) ⟨752589, by rfl⟩ : syracuseStep 2006905 = 1505179) (by norm_num)
theorem B2236285 : Blo 1782092 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B5078933 : Blo 1782092 5078933 := bbase (se 6 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 5078933 = 238075) (by norm_num)
theorem B2006941 : Blo 1782092 2006941 := bbase (se 3 (by rfl) ⟨376301, by rfl⟩ : syracuseStep 2006941 = 752603) (by norm_num)
theorem B4013981 : Blo 1782092 4013981 := bbase (se 3 (by rfl) ⟨752621, by rfl⟩ : syracuseStep 4013981 = 1505243) (by norm_num)
theorem B3383221 : Blo 1782092 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B6766517 : Blo 1782092 6766517 := bbase (se 5 (by rfl) ⟨317180, by rfl⟩ : syracuseStep 6766517 = 634361) (by norm_num)
theorem B18292661 : Blo 1782092 18292661 := bbase (se 5 (by rfl) ⟨857468, by rfl⟩ : syracuseStep 18292661 = 1714937) (by norm_num)
theorem B8568757 : Blo 1782092 8568757 := bbase (se 5 (by rfl) ⟨401660, by rfl⟩ : syracuseStep 8568757 = 803321) (by norm_num)
theorem B2006977 : Blo 1782092 2006977 := bbase (se 2 (by rfl) ⟨752616, by rfl⟩ : syracuseStep 2006977 = 1505233) (by norm_num)
theorem B3858373 : Blo 1782092 3858373 := bbase (se 4 (by rfl) ⟨361722, by rfl⟩ : syracuseStep 3858373 = 723445) (by norm_num)
theorem B20299733 : Blo 1782092 20299733 := bbase (se 7 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 20299733 = 475775) (by norm_num)
theorem B4513765 : Blo 1782092 4513765 := bbase (se 4 (by rfl) ⟨423165, by rfl⟩ : syracuseStep 4513765 = 846331) (by norm_num)
theorem B2007013 : Blo 1782092 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B4014053 : Blo 1782092 4014053 := bbase (se 4 (by rfl) ⟨376317, by rfl⟩ : syracuseStep 4014053 = 752635) (by norm_num)
theorem B2539517 : Blo 1782092 2539517 := bbase (se 3 (by rfl) ⟨476159, by rfl⟩ : syracuseStep 2539517 = 952319) (by norm_num)
theorem B4014161 : Blo 1782092 4014161 := bstep (se 2 (by rfl) ⟨1505310, by rfl⟩ : syracuseStep 4014161 = 3010621) B3010621
theorem B2539603 : Blo 1782092 2539603 := bstep (se 1 (by rfl) ⟨1904702, by rfl⟩ : syracuseStep 2539603 = 3809405) B3809405
theorem B4014179 : Blo 1782092 4014179 := bstep (se 1 (by rfl) ⟨3010634, by rfl⟩ : syracuseStep 4014179 = 6021269) B6021269
theorem B5079149 : Blo 1782092 5079149 := bstep (se 3 (by rfl) ⟨952340, by rfl⟩ : syracuseStep 5079149 = 1904681) B1904681
theorem B3383441 : Blo 1782092 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B42320069 : Blo 1782092 42320069 := bstep (se 4 (by rfl) ⟨3967506, by rfl⟩ : syracuseStep 42320069 = 7935013) B7935013
theorem B6103313 : Blo 1782092 6103313 := bstep (se 2 (by rfl) ⟨2288742, by rfl⟩ : syracuseStep 6103313 = 4577485) B4577485
theorem B5144995 : Blo 1782092 5144995 := bstep (se 1 (by rfl) ⟨3858746, by rfl⟩ : syracuseStep 5144995 = 7717493) B7717493
theorem B2539939 : Blo 1782092 2539939 := bstep (se 1 (by rfl) ⟨1904954, by rfl⟩ : syracuseStep 2539939 = 3809909) B3809909
theorem B3809891 : Blo 1782092 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B9028259 : Blo 1782092 9028259 := bstep (se 1 (by rfl) ⟨6771194, by rfl⟩ : syracuseStep 9028259 = 13542389) B13542389
theorem B10158797 : Blo 1782092 10158797 := bstep (se 3 (by rfl) ⟨1904774, by rfl⟩ : syracuseStep 10158797 = 3809549) B3809549
theorem B2409169 : Blo 1782092 2409169 := bstep (se 2 (by rfl) ⟨903438, by rfl⟩ : syracuseStep 2409169 = 1806877) B1806877
theorem B2573057 : Blo 1782092 2573057 := bstep (se 2 (by rfl) ⟨964896, by rfl⟩ : syracuseStep 2573057 = 1929793) B1929793
theorem B6767459 : Blo 1782092 6767459 := bstep (se 1 (by rfl) ⟨5075594, by rfl⟩ : syracuseStep 6767459 = 10151189) B10151189
theorem B3212131 : Blo 1782092 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B7226225 : Blo 1782092 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B3007361 : Blo 1782092 3007361 := bstep (se 2 (by rfl) ⟨1127760, by rfl⟩ : syracuseStep 3007361 = 2255521) B2255521
theorem B10838947 : Blo 1782092 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B4514737 : Blo 1782092 4514737 := bstep (se 2 (by rfl) ⟨1693026, by rfl⟩ : syracuseStep 4514737 = 3386053) B3386053
theorem B4817873 : Blo 1782092 4817873 := bstep (se 2 (by rfl) ⟨1806702, by rfl⟩ : syracuseStep 4817873 = 3613405) B3613405
theorem B3007489 : Blo 1782092 3007489 := bstep (se 2 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 3007489 = 2255617) B2255617
theorem B3384337 : Blo 1782092 3384337 := bstep (se 2 (by rfl) ⟨1269126, by rfl⟩ : syracuseStep 3384337 = 2538253) B2538253
theorem B3007523 : Blo 1782092 3007523 := bstep (se 1 (by rfl) ⟨2255642, by rfl⟩ : syracuseStep 3007523 = 4511285) B4511285
theorem B2475139 : Blo 1782092 2475139 := bstep (se 1 (by rfl) ⟨1856354, by rfl⟩ : syracuseStep 2475139 = 3712709) B3712709
theorem B2032787 : Blo 1782092 2032787 := bstep (se 1 (by rfl) ⟨1524590, by rfl⟩ : syracuseStep 2032787 = 3049181) B3049181
theorem B3007651 : Blo 1782092 3007651 := bstep (se 1 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 3007651 = 4511477) B4511477
theorem B3384497 : Blo 1782092 3384497 := bstep (se 2 (by rfl) ⟨1269186, by rfl⟩ : syracuseStep 3384497 = 2538373) B2538373
theorem B4515011 : Blo 1782092 4515011 := bstep (se 1 (by rfl) ⟨3386258, by rfl⟩ : syracuseStep 4515011 = 6772517) B6772517
theorem B3613955 : Blo 1782092 3613955 := bstep (se 1 (by rfl) ⟨2710466, by rfl⟩ : syracuseStep 3613955 = 5420933) B5420933
theorem B5080333 : Blo 1782092 5080333 := bstep (se 3 (by rfl) ⟨952562, by rfl⟩ : syracuseStep 5080333 = 1905125) B1905125
theorem B3007793 : Blo 1782092 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B15238469 : Blo 1782092 15238469 := bstep (se 4 (by rfl) ⟨1428606, by rfl⟩ : syracuseStep 15238469 = 2857213) B2857213
theorem B6866275 : Blo 1782092 6866275 := bstep (se 1 (by rfl) ⟨5149706, by rfl⟩ : syracuseStep 6866275 = 10299413) B10299413
theorem B7619953 : Blo 1782092 7619953 := bstep (se 2 (by rfl) ⟨2857482, by rfl⟩ : syracuseStep 7619953 = 5714965) B5714965
theorem B4515203 : Blo 1782092 4515203 := bstep (se 1 (by rfl) ⟨3386402, by rfl⟩ : syracuseStep 4515203 = 6772805) B6772805
theorem B5711249 : Blo 1782092 5711249 := bstep (se 2 (by rfl) ⟨2141718, by rfl⟩ : syracuseStep 5711249 = 4283437) B4283437
theorem B4343203 : Blo 1782092 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B3007921 : Blo 1782092 3007921 := bstep (se 2 (by rfl) ⟨1127970, by rfl⟩ : syracuseStep 3007921 = 2255941) B2255941
theorem B9029069 : Blo 1782092 9029069 := bstep (se 3 (by rfl) ⟨1692950, by rfl⟩ : syracuseStep 9029069 = 3385901) B3385901
theorem B3007955 : Blo 1782092 3007955 := bstep (se 1 (by rfl) ⟨2255966, by rfl⟩ : syracuseStep 3007955 = 4511933) B4511933
theorem B3384899 : Blo 1782092 3384899 := bstep (se 1 (by rfl) ⟨2538674, by rfl⟩ : syracuseStep 3384899 = 5077349) B5077349
theorem B3008083 : Blo 1782092 3008083 := bstep (se 1 (by rfl) ⟨2256062, by rfl⟩ : syracuseStep 3008083 = 4512125) B4512125
theorem B4286051 : Blo 1782092 4286051 := bstep (se 1 (by rfl) ⟨3214538, by rfl⟩ : syracuseStep 4286051 = 6429077) B6429077
theorem B6014573 : Blo 1782092 6014573 := bstep (se 3 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 6014573 = 2255465) B2255465
theorem B4064899 : Blo 1782092 4064899 := bstep (se 1 (by rfl) ⟨3048674, by rfl⟩ : syracuseStep 4064899 = 6097349) B6097349
theorem B12199565 : Blo 1782092 12199565 := bstep (se 3 (by rfl) ⟨2287418, by rfl⟩ : syracuseStep 12199565 = 4574837) B4574837
theorem B6014627 : Blo 1782092 6014627 := bstep (se 1 (by rfl) ⟨4510970, by rfl⟩ : syracuseStep 6014627 = 9021941) B9021941
theorem B3008225 : Blo 1782092 3008225 := bstep (se 2 (by rfl) ⟨1128084, by rfl⟩ : syracuseStep 3008225 = 2256169) B2256169
theorem B3049235 : Blo 1782092 3049235 := bstep (se 1 (by rfl) ⟨2286926, by rfl⟩ : syracuseStep 3049235 = 4573853) B4573853
theorem B4286243 : Blo 1782092 4286243 := bstep (se 1 (by rfl) ⟨3214682, by rfl⟩ : syracuseStep 4286243 = 6429365) B6429365
theorem B6768461 : Blo 1782092 6768461 := bstep (se 3 (by rfl) ⟨1269086, by rfl⟩ : syracuseStep 6768461 = 2538173) B2538173
theorem B3008353 : Blo 1782092 3008353 := bstep (se 2 (by rfl) ⟨1128132, by rfl⟩ : syracuseStep 3008353 = 2256265) B2256265
theorem B7718755 : Blo 1782092 7718755 := bstep (se 1 (by rfl) ⟨5789066, by rfl⟩ : syracuseStep 7718755 = 11578133) B11578133
theorem B3008387 : Blo 1782092 3008387 := bstep (se 1 (by rfl) ⟨2256290, by rfl⟩ : syracuseStep 3008387 = 4512581) B4512581
theorem B68536205 : Blo 1782092 68536205 := bstep (se 3 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 68536205 = 25701077) B25701077
theorem B6014897 : Blo 1782092 6014897 := bstep (se 2 (by rfl) ⟨2255586, by rfl⟩ : syracuseStep 6014897 = 4511173) B4511173
theorem B4122577 : Blo 1782092 4122577 := bstep (se 2 (by rfl) ⟨1545966, by rfl⟩ : syracuseStep 4122577 = 3091933) B3091933
theorem B2033635 : Blo 1782092 2033635 := bstep (se 1 (by rfl) ⟨1525226, by rfl⟩ : syracuseStep 2033635 = 3050453) B3050453
theorem B3008515 : Blo 1782092 3008515 := bstep (se 1 (by rfl) ⟨2256386, by rfl⟩ : syracuseStep 3008515 = 4512773) B4512773
theorem B4286513 : Blo 1782092 4286513 := bstep (se 2 (by rfl) ⟨1607442, by rfl⟩ : syracuseStep 4286513 = 3214885) B3214885
theorem B4819085 : Blo 1782092 4819085 := bstep (se 3 (by rfl) ⟨903578, by rfl⟩ : syracuseStep 4819085 = 1807157) B1807157
theorem B21686413 : Blo 1782092 21686413 := bstep (se 3 (by rfl) ⟨4066202, by rfl⟩ : syracuseStep 21686413 = 8132405) B8132405
theorem B3008657 : Blo 1782092 3008657 := bstep (se 2 (by rfl) ⟨1128246, by rfl⟩ : syracuseStep 3008657 = 2256493) B2256493
theorem B3008785 : Blo 1782092 3008785 := bstep (se 2 (by rfl) ⟨1128294, by rfl⟩ : syracuseStep 3008785 = 2256589) B2256589
theorem B3008819 : Blo 1782092 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B37087541 : Blo 1782092 37087541 := bstep (se 5 (by rfl) ⟨1738478, by rfl⟩ : syracuseStep 37087541 = 3476957) B3476957
theorem B3008947 : Blo 1782092 3008947 := bstep (se 1 (by rfl) ⟨2256710, by rfl⟩ : syracuseStep 3008947 = 4513421) B4513421
theorem B3385795 : Blo 1782092 3385795 := bstep (se 1 (by rfl) ⟨2539346, by rfl⟩ : syracuseStep 3385795 = 5078693) B5078693
theorem B11430341 : Blo 1782092 11430341 := bstep (se 4 (by rfl) ⟨1071594, by rfl⟩ : syracuseStep 11430341 = 2143189) B2143189
theorem B6015437 : Blo 1782092 6015437 := bstep (se 3 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 6015437 = 2255789) B2255789
theorem B4819409 : Blo 1782092 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B2673155 : Blo 1782092 2673155 := bstep (se 1 (by rfl) ⟨2004866, by rfl⟩ : syracuseStep 2673155 = 4009733) B4009733
theorem B6015491 : Blo 1782092 6015491 := bstep (se 1 (by rfl) ⟨4511618, by rfl⟩ : syracuseStep 6015491 = 9023237) B9023237
theorem B2673185 : Blo 1782092 2673185 := bstep (se 2 (by rfl) ⟨1002444, by rfl⟩ : syracuseStep 2673185 = 2004889) B2004889
theorem B2673203 : Blo 1782092 2673203 := bstep (se 1 (by rfl) ⟨2004902, by rfl⟩ : syracuseStep 2673203 = 4009805) B4009805
theorem B3009089 : Blo 1782092 3009089 := bstep (se 2 (by rfl) ⟨1128408, by rfl⟩ : syracuseStep 3009089 = 2256817) B2256817
theorem B2673233 : Blo 1782092 2673233 := bstep (se 2 (by rfl) ⟨1002462, by rfl⟩ : syracuseStep 2673233 = 2004925) B2004925
theorem B2673251 : Blo 1782092 2673251 := bstep (se 1 (by rfl) ⟨2004938, by rfl⟩ : syracuseStep 2673251 = 4009877) B4009877
theorem B3385955 : Blo 1782092 3385955 := bstep (se 1 (by rfl) ⟨2539466, by rfl⟩ : syracuseStep 3385955 = 5078933) B5078933
theorem B2673281 : Blo 1782092 2673281 := bstep (se 2 (by rfl) ⟨1002480, by rfl⟩ : syracuseStep 2673281 = 2004961) B2004961
theorem B2673299 : Blo 1782092 2673299 := bstep (se 1 (by rfl) ⟨2004974, by rfl⟩ : syracuseStep 2673299 = 4009949) B4009949
theorem B1903267 : Blo 1782092 1903267 := bstep (se 1 (by rfl) ⟨1427450, by rfl⟩ : syracuseStep 1903267 = 2854901) B2854901
theorem B2673329 : Blo 1782092 2673329 := bstep (se 2 (by rfl) ⟨1002498, by rfl⟩ : syracuseStep 2673329 = 2004997) B2004997
theorem B3009217 : Blo 1782092 3009217 := bstep (se 2 (by rfl) ⟨1128456, by rfl⟩ : syracuseStep 3009217 = 2256913) B2256913
theorem B2673347 : Blo 1782092 2673347 := bstep (se 1 (by rfl) ⟨2005010, by rfl⟩ : syracuseStep 2673347 = 4010021) B4010021
theorem B2673377 : Blo 1782092 2673377 := bstep (se 2 (by rfl) ⟨1002516, by rfl⟩ : syracuseStep 2673377 = 2005033) B2005033
theorem B5147363 : Blo 1782092 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B3009251 : Blo 1782092 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B2673395 : Blo 1782092 2673395 := bstep (se 1 (by rfl) ⟨2005046, by rfl⟩ : syracuseStep 2673395 = 4010093) B4010093
theorem B2673425 : Blo 1782092 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B6015761 : Blo 1782092 6015761 := bstep (se 2 (by rfl) ⟨2255910, by rfl⟩ : syracuseStep 6015761 = 4511821) B4511821
theorem B2673443 : Blo 1782092 2673443 := bstep (se 1 (by rfl) ⟨2005082, by rfl⟩ : syracuseStep 2673443 = 4010165) B4010165
theorem B2673473 : Blo 1782092 2673473 := bstep (se 2 (by rfl) ⟨1002552, by rfl⟩ : syracuseStep 2673473 = 2005105) B2005105
theorem B2255683 : Blo 1782092 2255683 := bstep (se 1 (by rfl) ⟨1691762, by rfl⟩ : syracuseStep 2255683 = 3383525) B3383525
theorem B2673491 : Blo 1782092 2673491 := bstep (se 1 (by rfl) ⟨2005118, by rfl⟩ : syracuseStep 2673491 = 4010237) B4010237
theorem B3009379 : Blo 1782092 3009379 := bstep (se 1 (by rfl) ⟨2257034, by rfl⟩ : syracuseStep 3009379 = 4514069) B4514069
theorem B2673521 : Blo 1782092 2673521 := bstep (se 2 (by rfl) ⟨1002570, by rfl⟩ : syracuseStep 2673521 = 2005141) B2005141
theorem B2673539 : Blo 1782092 2673539 := bstep (se 1 (by rfl) ⟨2005154, by rfl⟩ : syracuseStep 2673539 = 4010309) B4010309
theorem B13544333 : Blo 1782092 13544333 := bstep (se 3 (by rfl) ⟨2539562, by rfl⟩ : syracuseStep 13544333 = 5079125) B5079125
theorem B2673569 : Blo 1782092 2673569 := bstep (se 2 (by rfl) ⟨1002588, by rfl⟩ : syracuseStep 2673569 = 2005177) B2005177
theorem B2255779 : Blo 1782092 2255779 := bstep (se 1 (by rfl) ⟨1691834, by rfl⟩ : syracuseStep 2255779 = 3383669) B3383669
theorem B2673587 : Blo 1782092 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B2673617 : Blo 1782092 2673617 := bstep (se 2 (by rfl) ⟨1002606, by rfl⟩ : syracuseStep 2673617 = 2005213) B2005213
theorem B2673635 : Blo 1782092 2673635 := bstep (se 1 (by rfl) ⟨2005226, by rfl⟩ : syracuseStep 2673635 = 4010453) B4010453
theorem B3009521 : Blo 1782092 3009521 := bstep (se 2 (by rfl) ⟨1128570, by rfl⟩ : syracuseStep 3009521 = 2257141) B2257141
theorem B2673665 : Blo 1782092 2673665 := bstep (se 2 (by rfl) ⟨1002624, by rfl⟩ : syracuseStep 2673665 = 2005249) B2005249
theorem B10152965 : Blo 1782092 10152965 := bstep (se 4 (by rfl) ⟨951840, by rfl⟩ : syracuseStep 10152965 = 1903681) B1903681
theorem B2673683 : Blo 1782092 2673683 := bstep (se 1 (by rfl) ⟨2005262, by rfl⟩ : syracuseStep 2673683 = 4010525) B4010525
theorem B2673713 : Blo 1782092 2673713 := bstep (se 2 (by rfl) ⟨1002642, by rfl⟩ : syracuseStep 2673713 = 2005285) B2005285
theorem B2673731 : Blo 1782092 2673731 := bstep (se 1 (by rfl) ⟨2005298, by rfl⟩ : syracuseStep 2673731 = 4010597) B4010597
theorem B2673761 : Blo 1782092 2673761 := bstep (se 2 (by rfl) ⟨1002660, by rfl⟩ : syracuseStep 2673761 = 2005321) B2005321
theorem B4820077 : Blo 1782092 4820077 := bstep (se 3 (by rfl) ⟨903764, by rfl⟩ : syracuseStep 4820077 = 1807529) B1807529
theorem B3009649 : Blo 1782092 3009649 := bstep (se 2 (by rfl) ⟨1128618, by rfl⟩ : syracuseStep 3009649 = 2257237) B2257237
theorem B2673779 : Blo 1782092 2673779 := bstep (se 1 (by rfl) ⟨2005334, by rfl⟩ : syracuseStep 2673779 = 4010669) B4010669
theorem B2673809 : Blo 1782092 2673809 := bstep (se 2 (by rfl) ⟨1002678, by rfl⟩ : syracuseStep 2673809 = 2005357) B2005357
theorem B3009683 : Blo 1782092 3009683 := bstep (se 1 (by rfl) ⟨2257262, by rfl⟩ : syracuseStep 3009683 = 4514525) B4514525
theorem B2673827 : Blo 1782092 2673827 := bstep (se 1 (by rfl) ⟨2005370, by rfl⟩ : syracuseStep 2673827 = 4010741) B4010741
theorem B11422883 : Blo 1782092 11422883 := bstep (se 1 (by rfl) ⟨8567162, by rfl⟩ : syracuseStep 11422883 = 17134325) B17134325
theorem B2673857 : Blo 1782092 2673857 := bstep (se 2 (by rfl) ⟨1002696, by rfl⟩ : syracuseStep 2673857 = 2005393) B2005393
theorem B2673875 : Blo 1782092 2673875 := bstep (se 1 (by rfl) ⟨2005406, by rfl⟩ : syracuseStep 2673875 = 4010813) B4010813
theorem B2673905 : Blo 1782092 2673905 := bstep (se 2 (by rfl) ⟨1002714, by rfl⟩ : syracuseStep 2673905 = 2005429) B2005429
theorem B2673923 : Blo 1782092 2673923 := bstep (se 1 (by rfl) ⟨2005442, by rfl⟩ : syracuseStep 2673923 = 4010885) B4010885
theorem B3009811 : Blo 1782092 3009811 := bstep (se 1 (by rfl) ⟨2257358, by rfl⟩ : syracuseStep 3009811 = 4514717) B4514717
theorem B2673953 : Blo 1782092 2673953 := bstep (se 2 (by rfl) ⟨1002732, by rfl⟩ : syracuseStep 2673953 = 2005465) B2005465
theorem B6016301 : Blo 1782092 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B2673971 : Blo 1782092 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B2674001 : Blo 1782092 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B6016355 : Blo 1782092 6016355 := bstep (se 1 (by rfl) ⟨4512266, by rfl⟩ : syracuseStep 6016355 = 9024533) B9024533
theorem B2674019 : Blo 1782092 2674019 := bstep (se 1 (by rfl) ⟨2005514, by rfl⟩ : syracuseStep 2674019 = 4011029) B4011029
theorem B2674049 : Blo 1782092 2674049 := bstep (se 2 (by rfl) ⟨1002768, by rfl⟩ : syracuseStep 2674049 = 2005537) B2005537
theorem B7613837 : Blo 1782092 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B2674067 : Blo 1782092 2674067 := bstep (se 1 (by rfl) ⟨2005550, by rfl⟩ : syracuseStep 2674067 = 4011101) B4011101
theorem B2256275 : Blo 1782092 2256275 := bstep (se 1 (by rfl) ⟨1692206, by rfl⟩ : syracuseStep 2256275 = 3384413) B3384413
theorem B3009953 : Blo 1782092 3009953 := bstep (se 2 (by rfl) ⟨1128732, by rfl⟩ : syracuseStep 3009953 = 2257465) B2257465
theorem B5713325 : Blo 1782092 5713325 := bstep (se 3 (by rfl) ⟨1071248, by rfl⟩ : syracuseStep 5713325 = 2142497) B2142497
theorem B2674097 : Blo 1782092 2674097 := bstep (se 2 (by rfl) ⟨1002786, by rfl⟩ : syracuseStep 2674097 = 2005573) B2005573
theorem B2674115 : Blo 1782092 2674115 := bstep (se 1 (by rfl) ⟨2005586, by rfl⟩ : syracuseStep 2674115 = 4011173) B4011173
theorem B10153421 : Blo 1782092 10153421 := bstep (se 3 (by rfl) ⟨1903766, by rfl⟩ : syracuseStep 10153421 = 3807533) B3807533
theorem B2674145 : Blo 1782092 2674145 := bstep (se 2 (by rfl) ⟨1002804, by rfl⟩ : syracuseStep 2674145 = 2005609) B2005609
theorem B2674163 : Blo 1782092 2674163 := bstep (se 1 (by rfl) ⟨2005622, by rfl⟩ : syracuseStep 2674163 = 4011245) B4011245
theorem B2674193 : Blo 1782092 2674193 := bstep (se 2 (by rfl) ⟨1002822, by rfl⟩ : syracuseStep 2674193 = 2005645) B2005645
theorem B3010081 : Blo 1782092 3010081 := bstep (se 2 (by rfl) ⟨1128780, by rfl⟩ : syracuseStep 3010081 = 2257561) B2257561
theorem B2674211 : Blo 1782092 2674211 := bstep (se 1 (by rfl) ⟨2005658, by rfl⟩ : syracuseStep 2674211 = 4011317) B4011317
theorem B2674241 : Blo 1782092 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B3010115 : Blo 1782092 3010115 := bstep (se 1 (by rfl) ⟨2257586, by rfl⟩ : syracuseStep 3010115 = 4515173) B4515173
theorem B2674259 : Blo 1782092 2674259 := bstep (se 1 (by rfl) ⟨2005694, by rfl⟩ : syracuseStep 2674259 = 4011389) B4011389
theorem B9023075 : Blo 1782092 9023075 := bstep (se 1 (by rfl) ⟨6767306, by rfl⟩ : syracuseStep 9023075 = 13534613) B13534613
theorem B6016625 : Blo 1782092 6016625 := bstep (se 2 (by rfl) ⟨2256234, by rfl⟩ : syracuseStep 6016625 = 4512469) B4512469
theorem B2674289 : Blo 1782092 2674289 := bstep (se 2 (by rfl) ⟨1002858, by rfl⟩ : syracuseStep 2674289 = 2005717) B2005717
theorem B2674307 : Blo 1782092 2674307 := bstep (se 1 (by rfl) ⟨2005730, by rfl⟩ : syracuseStep 2674307 = 4011461) B4011461
theorem B3214993 : Blo 1782092 3214993 := bstep (se 2 (by rfl) ⟨1205622, by rfl⟩ : syracuseStep 3214993 = 2411245) B2411245
theorem B2674337 : Blo 1782092 2674337 := bstep (se 2 (by rfl) ⟨1002876, by rfl⟩ : syracuseStep 2674337 = 2005753) B2005753
theorem B2674355 : Blo 1782092 2674355 := bstep (se 1 (by rfl) ⟨2005766, by rfl⟩ : syracuseStep 2674355 = 4011533) B4011533
theorem B3010243 : Blo 1782092 3010243 := bstep (se 1 (by rfl) ⟨2257682, by rfl⟩ : syracuseStep 3010243 = 4515365) B4515365
theorem B2674385 : Blo 1782092 2674385 := bstep (se 2 (by rfl) ⟨1002894, by rfl⟩ : syracuseStep 2674385 = 2005789) B2005789
theorem B2674403 : Blo 1782092 2674403 := bstep (se 1 (by rfl) ⟨2005802, by rfl⟩ : syracuseStep 2674403 = 4011605) B4011605
theorem B2674433 : Blo 1782092 2674433 := bstep (se 2 (by rfl) ⟨1002912, by rfl⟩ : syracuseStep 2674433 = 2005825) B2005825
theorem B2674451 : Blo 1782092 2674451 := bstep (se 1 (by rfl) ⟨2005838, by rfl⟩ : syracuseStep 2674451 = 4011677) B4011677
theorem B2674481 : Blo 1782092 2674481 := bstep (se 2 (by rfl) ⟨1002930, by rfl⟩ : syracuseStep 2674481 = 2005861) B2005861
theorem B2674499 : Blo 1782092 2674499 := bstep (se 1 (by rfl) ⟨2005874, by rfl⟩ : syracuseStep 2674499 = 4011749) B4011749
theorem B3010385 : Blo 1782092 3010385 := bstep (se 2 (by rfl) ⟨1128894, by rfl⟩ : syracuseStep 3010385 = 2257789) B2257789
theorem B2674529 : Blo 1782092 2674529 := bstep (se 2 (by rfl) ⟨1002948, by rfl⟩ : syracuseStep 2674529 = 2005897) B2005897
theorem B4009841 : Blo 1782092 4009841 := bstep (se 2 (by rfl) ⟨1503690, by rfl⟩ : syracuseStep 4009841 = 3007381) B3007381
theorem B2674547 : Blo 1782092 2674547 := bstep (se 1 (by rfl) ⟨2005910, by rfl⟩ : syracuseStep 2674547 = 4011821) B4011821
theorem B4009859 : Blo 1782092 4009859 := bstep (se 1 (by rfl) ⟨3007394, by rfl⟩ : syracuseStep 4009859 = 6014789) B6014789
theorem B6770573 : Blo 1782092 6770573 := bstep (se 3 (by rfl) ⟨1269482, by rfl⟩ : syracuseStep 6770573 = 2538965) B2538965
theorem B2674577 : Blo 1782092 2674577 := bstep (se 2 (by rfl) ⟨1002966, by rfl⟩ : syracuseStep 2674577 = 2005933) B2005933
theorem B10293155 : Blo 1782092 10293155 := bstep (se 1 (by rfl) ⟨7719866, by rfl⟩ : syracuseStep 10293155 = 15439733) B15439733
theorem B2674595 : Blo 1782092 2674595 := bstep (se 1 (by rfl) ⟨2005946, by rfl⟩ : syracuseStep 2674595 = 4011893) B4011893
theorem B2674625 : Blo 1782092 2674625 := bstep (se 2 (by rfl) ⟨1002984, by rfl⟩ : syracuseStep 2674625 = 2005969) B2005969
theorem B3010513 : Blo 1782092 3010513 := bstep (se 2 (by rfl) ⟨1128942, by rfl⟩ : syracuseStep 3010513 = 2257885) B2257885
theorem B2674643 : Blo 1782092 2674643 := bstep (se 1 (by rfl) ⟨2005982, by rfl⟩ : syracuseStep 2674643 = 4011965) B4011965
theorem B2674673 : Blo 1782092 2674673 := bstep (se 2 (by rfl) ⟨1003002, by rfl⟩ : syracuseStep 2674673 = 2006005) B2006005
theorem B3010547 : Blo 1782092 3010547 := bstep (se 1 (by rfl) ⟨2257910, by rfl⟩ : syracuseStep 3010547 = 4515821) B4515821
theorem B2674691 : Blo 1782092 2674691 := bstep (se 1 (by rfl) ⟨2006018, by rfl⟩ : syracuseStep 2674691 = 4012037) B4012037
theorem B2674721 : Blo 1782092 2674721 := bstep (se 2 (by rfl) ⟨1003020, by rfl⟩ : syracuseStep 2674721 = 2006041) B2006041
theorem B2674739 : Blo 1782092 2674739 := bstep (se 1 (by rfl) ⟨2006054, by rfl⟩ : syracuseStep 2674739 = 4012109) B4012109
theorem B2674769 : Blo 1782092 2674769 := bstep (se 2 (by rfl) ⟨1003038, by rfl⟩ : syracuseStep 2674769 = 2006077) B2006077
theorem B2256979 : Blo 1782092 2256979 := bstep (se 1 (by rfl) ⟨1692734, by rfl⟩ : syracuseStep 2256979 = 3385469) B3385469
theorem B2674787 : Blo 1782092 2674787 := bstep (se 1 (by rfl) ⟨2006090, by rfl⟩ : syracuseStep 2674787 = 4012181) B4012181
theorem B2674817 : Blo 1782092 2674817 := bstep (se 2 (by rfl) ⟨1003056, by rfl⟩ : syracuseStep 2674817 = 2006113) B2006113
theorem B6017165 : Blo 1782092 6017165 := bstep (se 3 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 6017165 = 2256437) B2256437
theorem B4010129 : Blo 1782092 4010129 := bstep (se 2 (by rfl) ⟨1503798, by rfl⟩ : syracuseStep 4010129 = 3007597) B3007597
theorem B2674835 : Blo 1782092 2674835 := bstep (se 1 (by rfl) ⟨2006126, by rfl⟩ : syracuseStep 2674835 = 4012253) B4012253
theorem B4010147 : Blo 1782092 4010147 := bstep (se 1 (by rfl) ⟨3007610, by rfl⟩ : syracuseStep 4010147 = 6015221) B6015221
theorem B2674865 : Blo 1782092 2674865 := bstep (se 2 (by rfl) ⟨1003074, by rfl⟩ : syracuseStep 2674865 = 2006149) B2006149
theorem B2257075 : Blo 1782092 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B6017219 : Blo 1782092 6017219 := bstep (se 1 (by rfl) ⟨4512914, by rfl⟩ : syracuseStep 6017219 = 9025829) B9025829
theorem B2674883 : Blo 1782092 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B2674913 : Blo 1782092 2674913 := bstep (se 2 (by rfl) ⟨1003092, by rfl⟩ : syracuseStep 2674913 = 2006185) B2006185
theorem B2674931 : Blo 1782092 2674931 := bstep (se 1 (by rfl) ⟨2006198, by rfl⟩ : syracuseStep 2674931 = 4012397) B4012397
theorem B2674961 : Blo 1782092 2674961 := bstep (se 2 (by rfl) ⟨1003110, by rfl⟩ : syracuseStep 2674961 = 2006221) B2006221
theorem B2674979 : Blo 1782092 2674979 := bstep (se 1 (by rfl) ⟨2006234, by rfl⟩ : syracuseStep 2674979 = 4012469) B4012469
theorem B5714221 : Blo 1782092 5714221 := bstep (se 3 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 5714221 = 2142833) B2142833
theorem B2675009 : Blo 1782092 2675009 := bstep (se 2 (by rfl) ⟨1003128, by rfl⟩ : syracuseStep 2675009 = 2006257) B2006257
theorem B19272005 : Blo 1782092 19272005 := bstep (se 4 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 19272005 = 3613501) B3613501
theorem B1782099 : Blo 1782092 1782099 := bstep (se 1 (by rfl) ⟨1336574, by rfl⟩ : syracuseStep 1782099 = 2673149) B2673149
theorem B2675027 : Blo 1782092 2675027 := bstep (se 1 (by rfl) ⟨2006270, by rfl⟩ : syracuseStep 2675027 = 4012541) B4012541
theorem B1782115 : Blo 1782092 1782115 := bstep (se 1 (by rfl) ⟨1336586, by rfl⟩ : syracuseStep 1782115 = 2673173) B2673173
theorem B2675057 : Blo 1782092 2675057 := bstep (se 2 (by rfl) ⟨1003146, by rfl⟩ : syracuseStep 2675057 = 2006293) B2006293
theorem B1782131 : Blo 1782092 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1782147 : Blo 1782092 1782147 := bstep (se 1 (by rfl) ⟨1336610, by rfl⟩ : syracuseStep 1782147 = 2673221) B2673221
theorem B2675075 : Blo 1782092 2675075 := bstep (se 1 (by rfl) ⟨2006306, by rfl⟩ : syracuseStep 2675075 = 4012613) B4012613
theorem B9023885 : Blo 1782092 9023885 := bstep (se 3 (by rfl) ⟨1691978, by rfl⟩ : syracuseStep 9023885 = 3383957) B3383957
theorem B1782163 : Blo 1782092 1782163 := bstep (se 1 (by rfl) ⟨1336622, by rfl⟩ : syracuseStep 1782163 = 2673245) B2673245
theorem B2675105 : Blo 1782092 2675105 := bstep (se 2 (by rfl) ⟨1003164, by rfl⟩ : syracuseStep 2675105 = 2006329) B2006329
theorem B1782179 : Blo 1782092 1782179 := bstep (se 1 (by rfl) ⟨1336634, by rfl⟩ : syracuseStep 1782179 = 2673269) B2673269
theorem B4010417 : Blo 1782092 4010417 := bstep (se 2 (by rfl) ⟨1503906, by rfl⟩ : syracuseStep 4010417 = 3007813) B3007813
theorem B1782195 : Blo 1782092 1782195 := bstep (se 1 (by rfl) ⟨1336646, by rfl⟩ : syracuseStep 1782195 = 2673293) B2673293
theorem B2675123 : Blo 1782092 2675123 := bstep (se 1 (by rfl) ⟨2006342, by rfl⟩ : syracuseStep 2675123 = 4012685) B4012685
theorem B1782211 : Blo 1782092 1782211 := bstep (se 1 (by rfl) ⟨1336658, by rfl⟩ : syracuseStep 1782211 = 2673317) B2673317
theorem B4010435 : Blo 1782092 4010435 := bstep (se 1 (by rfl) ⟨3007826, by rfl⟩ : syracuseStep 4010435 = 6015653) B6015653
theorem B527618501 : Blo 1782092 527618501 := bstep (se 4 (by rfl) ⟨49464234, by rfl⟩ : syracuseStep 527618501 = 98928469) B98928469
theorem B6017489 : Blo 1782092 6017489 := bstep (se 2 (by rfl) ⟨2256558, by rfl⟩ : syracuseStep 6017489 = 4513117) B4513117
theorem B1782227 : Blo 1782092 1782227 := bstep (se 1 (by rfl) ⟨1336670, by rfl⟩ : syracuseStep 1782227 = 2673341) B2673341
theorem B2675153 : Blo 1782092 2675153 := bstep (se 2 (by rfl) ⟨1003182, by rfl⟩ : syracuseStep 2675153 = 2006365) B2006365
theorem B1782243 : Blo 1782092 1782243 := bstep (se 1 (by rfl) ⟨1336682, by rfl⟩ : syracuseStep 1782243 = 2673365) B2673365
theorem B2675171 : Blo 1782092 2675171 := bstep (se 1 (by rfl) ⟨2006378, by rfl⟩ : syracuseStep 2675171 = 4012757) B4012757
theorem B1782259 : Blo 1782092 1782259 := bstep (se 1 (by rfl) ⟨1336694, by rfl⟩ : syracuseStep 1782259 = 2673389) B2673389
theorem B2675201 : Blo 1782092 2675201 := bstep (se 2 (by rfl) ⟨1003200, by rfl⟩ : syracuseStep 2675201 = 2006401) B2006401
theorem B1782275 : Blo 1782092 1782275 := bstep (se 1 (by rfl) ⟨1336706, by rfl⟩ : syracuseStep 1782275 = 2673413) B2673413
theorem B1782291 : Blo 1782092 1782291 := bstep (se 1 (by rfl) ⟨1336718, by rfl⟩ : syracuseStep 1782291 = 2673437) B2673437
theorem B2675219 : Blo 1782092 2675219 := bstep (se 1 (by rfl) ⟨2006414, by rfl⟩ : syracuseStep 2675219 = 4012829) B4012829
theorem B1782307 : Blo 1782092 1782307 := bstep (se 1 (by rfl) ⟨1336730, by rfl⟩ : syracuseStep 1782307 = 2673461) B2673461
theorem B2675249 : Blo 1782092 2675249 := bstep (se 2 (by rfl) ⟨1003218, by rfl⟩ : syracuseStep 2675249 = 2006437) B2006437
theorem B1782323 : Blo 1782092 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B1782339 : Blo 1782092 1782339 := bstep (se 1 (by rfl) ⟨1336754, by rfl⟩ : syracuseStep 1782339 = 2673509) B2673509
theorem B2675267 : Blo 1782092 2675267 := bstep (se 1 (by rfl) ⟨2006450, by rfl⟩ : syracuseStep 2675267 = 4012901) B4012901
theorem B1782355 : Blo 1782092 1782355 := bstep (se 1 (by rfl) ⟨1336766, by rfl⟩ : syracuseStep 1782355 = 2673533) B2673533
theorem B2675297 : Blo 1782092 2675297 := bstep (se 2 (by rfl) ⟨1003236, by rfl⟩ : syracuseStep 2675297 = 2006473) B2006473
theorem B1782371 : Blo 1782092 1782371 := bstep (se 1 (by rfl) ⟨1336778, by rfl⟩ : syracuseStep 1782371 = 2673557) B2673557
theorem B9638513 : Blo 1782092 9638513 := bstep (se 2 (by rfl) ⟨3614442, by rfl⟩ : syracuseStep 9638513 = 7228885) B7228885
theorem B1782387 : Blo 1782092 1782387 := bstep (se 1 (by rfl) ⟨1336790, by rfl⟩ : syracuseStep 1782387 = 2673581) B2673581
theorem B2675315 : Blo 1782092 2675315 := bstep (se 1 (by rfl) ⟨2006486, by rfl⟩ : syracuseStep 2675315 = 4012973) B4012973
theorem B1782403 : Blo 1782092 1782403 := bstep (se 1 (by rfl) ⟨1336802, by rfl⟩ : syracuseStep 1782403 = 2673605) B2673605
theorem B2675345 : Blo 1782092 2675345 := bstep (se 2 (by rfl) ⟨1003254, by rfl⟩ : syracuseStep 2675345 = 2006509) B2006509
theorem B1782419 : Blo 1782092 1782419 := bstep (se 1 (by rfl) ⟨1336814, by rfl⟩ : syracuseStep 1782419 = 2673629) B2673629
theorem B1782435 : Blo 1782092 1782435 := bstep (se 1 (by rfl) ⟨1336826, by rfl⟩ : syracuseStep 1782435 = 2673653) B2673653
theorem B2675363 : Blo 1782092 2675363 := bstep (se 1 (by rfl) ⟨2006522, by rfl⟩ : syracuseStep 2675363 = 4013045) B4013045
theorem B2257571 : Blo 1782092 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B6771377 : Blo 1782092 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B1782451 : Blo 1782092 1782451 := bstep (se 1 (by rfl) ⟨1336838, by rfl⟩ : syracuseStep 1782451 = 2673677) B2673677
theorem B2675393 : Blo 1782092 2675393 := bstep (se 2 (by rfl) ⟨1003272, by rfl⟩ : syracuseStep 2675393 = 2006545) B2006545
theorem B1782467 : Blo 1782092 1782467 := bstep (se 1 (by rfl) ⟨1336850, by rfl⟩ : syracuseStep 1782467 = 2673701) B2673701
theorem B9638597 : Blo 1782092 9638597 := bstep (se 4 (by rfl) ⟨903618, by rfl⟩ : syracuseStep 9638597 = 1807237) B1807237
theorem B4010705 : Blo 1782092 4010705 := bstep (se 2 (by rfl) ⟨1504014, by rfl⟩ : syracuseStep 4010705 = 3008029) B3008029
theorem B1782483 : Blo 1782092 1782483 := bstep (se 1 (by rfl) ⟨1336862, by rfl⟩ : syracuseStep 1782483 = 2673725) B2673725
theorem B2675411 : Blo 1782092 2675411 := bstep (se 1 (by rfl) ⟨2006558, by rfl⟩ : syracuseStep 2675411 = 4013117) B4013117
theorem B4821713 : Blo 1782092 4821713 := bstep (se 2 (by rfl) ⟨1808142, by rfl⟩ : syracuseStep 4821713 = 3616285) B3616285
theorem B1782499 : Blo 1782092 1782499 := bstep (se 1 (by rfl) ⟨1336874, by rfl⟩ : syracuseStep 1782499 = 2673749) B2673749
theorem B4010723 : Blo 1782092 4010723 := bstep (se 1 (by rfl) ⟨3008042, by rfl⟩ : syracuseStep 4010723 = 6016085) B6016085
theorem B2675441 : Blo 1782092 2675441 := bstep (se 2 (by rfl) ⟨1003290, by rfl⟩ : syracuseStep 2675441 = 2006581) B2006581
theorem B1782515 : Blo 1782092 1782515 := bstep (se 1 (by rfl) ⟨1336886, by rfl⟩ : syracuseStep 1782515 = 2673773) B2673773
theorem B1782531 : Blo 1782092 1782531 := bstep (se 1 (by rfl) ⟨1336898, by rfl⟩ : syracuseStep 1782531 = 2673797) B2673797
theorem B2675459 : Blo 1782092 2675459 := bstep (se 1 (by rfl) ⟨2006594, by rfl⟩ : syracuseStep 2675459 = 4013189) B4013189
theorem B1782547 : Blo 1782092 1782547 := bstep (se 1 (by rfl) ⟨1336910, by rfl⟩ : syracuseStep 1782547 = 2673821) B2673821
theorem B2675489 : Blo 1782092 2675489 := bstep (se 2 (by rfl) ⟨1003308, by rfl⟩ : syracuseStep 2675489 = 2006617) B2006617
theorem B1782563 : Blo 1782092 1782563 := bstep (se 1 (by rfl) ⟨1336922, by rfl⟩ : syracuseStep 1782563 = 2673845) B2673845
theorem B1782579 : Blo 1782092 1782579 := bstep (se 1 (by rfl) ⟨1336934, by rfl⟩ : syracuseStep 1782579 = 2673869) B2673869
theorem B2675507 : Blo 1782092 2675507 := bstep (se 1 (by rfl) ⟨2006630, by rfl⟩ : syracuseStep 2675507 = 4013261) B4013261
theorem B1782595 : Blo 1782092 1782595 := bstep (se 1 (by rfl) ⟨1336946, by rfl⟩ : syracuseStep 1782595 = 2673893) B2673893
theorem B2675537 : Blo 1782092 2675537 := bstep (se 2 (by rfl) ⟨1003326, by rfl⟩ : syracuseStep 2675537 = 2006653) B2006653
theorem B1782611 : Blo 1782092 1782611 := bstep (se 1 (by rfl) ⟨1336958, by rfl⟩ : syracuseStep 1782611 = 2673917) B2673917
theorem B1782627 : Blo 1782092 1782627 := bstep (se 1 (by rfl) ⟨1336970, by rfl⟩ : syracuseStep 1782627 = 2673941) B2673941
theorem B2675555 : Blo 1782092 2675555 := bstep (se 1 (by rfl) ⟨2006666, by rfl⟩ : syracuseStep 2675555 = 4013333) B4013333
theorem B1782643 : Blo 1782092 1782643 := bstep (se 1 (by rfl) ⟨1336982, by rfl⟩ : syracuseStep 1782643 = 2673965) B2673965
theorem B2675585 : Blo 1782092 2675585 := bstep (se 2 (by rfl) ⟨1003344, by rfl⟩ : syracuseStep 2675585 = 2006689) B2006689
theorem B1782659 : Blo 1782092 1782659 := bstep (se 1 (by rfl) ⟨1336994, by rfl⟩ : syracuseStep 1782659 = 2673989) B2673989
theorem B1930115 : Blo 1782092 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B1782675 : Blo 1782092 1782675 := bstep (se 1 (by rfl) ⟨1337006, by rfl⟩ : syracuseStep 1782675 = 2674013) B2674013
theorem B2675603 : Blo 1782092 2675603 := bstep (se 1 (by rfl) ⟨2006702, by rfl⟩ : syracuseStep 2675603 = 4013405) B4013405
theorem B1782691 : Blo 1782092 1782691 := bstep (se 1 (by rfl) ⟨1337018, by rfl⟩ : syracuseStep 1782691 = 2674037) B2674037
theorem B2675633 : Blo 1782092 2675633 := bstep (se 2 (by rfl) ⟨1003362, by rfl⟩ : syracuseStep 2675633 = 2006725) B2006725
theorem B1782707 : Blo 1782092 1782707 := bstep (se 1 (by rfl) ⟨1337030, by rfl⟩ : syracuseStep 1782707 = 2674061) B2674061
theorem B1782723 : Blo 1782092 1782723 := bstep (se 1 (by rfl) ⟨1337042, by rfl⟩ : syracuseStep 1782723 = 2674085) B2674085
theorem B2675651 : Blo 1782092 2675651 := bstep (se 1 (by rfl) ⟨2006738, by rfl⟩ : syracuseStep 2675651 = 4013477) B4013477
theorem B1782739 : Blo 1782092 1782739 := bstep (se 1 (by rfl) ⟨1337054, by rfl⟩ : syracuseStep 1782739 = 2674109) B2674109
theorem B2675681 : Blo 1782092 2675681 := bstep (se 2 (by rfl) ⟨1003380, by rfl⟩ : syracuseStep 2675681 = 2006761) B2006761
theorem B1782755 : Blo 1782092 1782755 := bstep (se 1 (by rfl) ⟨1337066, by rfl⟩ : syracuseStep 1782755 = 2674133) B2674133
theorem B6018029 : Blo 1782092 6018029 := bstep (se 3 (by rfl) ⟨1128380, by rfl⟩ : syracuseStep 6018029 = 2256761) B2256761
theorem B4010993 : Blo 1782092 4010993 := bstep (se 2 (by rfl) ⟨1504122, by rfl⟩ : syracuseStep 4010993 = 3008245) B3008245
theorem B1782771 : Blo 1782092 1782771 := bstep (se 1 (by rfl) ⟨1337078, by rfl⟩ : syracuseStep 1782771 = 2674157) B2674157
theorem B2675699 : Blo 1782092 2675699 := bstep (se 1 (by rfl) ⟨2006774, by rfl⟩ : syracuseStep 2675699 = 4013549) B4013549
theorem B4011011 : Blo 1782092 4011011 := bstep (se 1 (by rfl) ⟨3008258, by rfl⟩ : syracuseStep 4011011 = 6016517) B6016517
theorem B1782787 : Blo 1782092 1782787 := bstep (se 1 (by rfl) ⟨1337090, by rfl⟩ : syracuseStep 1782787 = 2674181) B2674181
theorem B2675729 : Blo 1782092 2675729 := bstep (se 2 (by rfl) ⟨1003398, by rfl⟩ : syracuseStep 2675729 = 2006797) B2006797
theorem B1782803 : Blo 1782092 1782803 := bstep (se 1 (by rfl) ⟨1337102, by rfl⟩ : syracuseStep 1782803 = 2674205) B2674205
theorem B1782819 : Blo 1782092 1782819 := bstep (se 1 (by rfl) ⟨1337114, by rfl⟩ : syracuseStep 1782819 = 2674229) B2674229
theorem B6018083 : Blo 1782092 6018083 := bstep (se 1 (by rfl) ⟨4513562, by rfl⟩ : syracuseStep 6018083 = 9027125) B9027125
theorem B2675747 : Blo 1782092 2675747 := bstep (se 1 (by rfl) ⟨2006810, by rfl⟩ : syracuseStep 2675747 = 4013621) B4013621
theorem B5076017 : Blo 1782092 5076017 := bstep (se 2 (by rfl) ⟨1903506, by rfl⟩ : syracuseStep 5076017 = 3807013) B3807013
theorem B1782835 : Blo 1782092 1782835 := bstep (se 1 (by rfl) ⟨1337126, by rfl⟩ : syracuseStep 1782835 = 2674253) B2674253
theorem B2675777 : Blo 1782092 2675777 := bstep (se 2 (by rfl) ⟨1003416, by rfl⟩ : syracuseStep 2675777 = 2006833) B2006833
theorem B1782851 : Blo 1782092 1782851 := bstep (se 1 (by rfl) ⟨1337138, by rfl⟩ : syracuseStep 1782851 = 2674277) B2674277
theorem B1782867 : Blo 1782092 1782867 := bstep (se 1 (by rfl) ⟨1337150, by rfl⟩ : syracuseStep 1782867 = 2674301) B2674301
theorem B2675795 : Blo 1782092 2675795 := bstep (se 1 (by rfl) ⟨2006846, by rfl⟩ : syracuseStep 2675795 = 4013693) B4013693
theorem B1782883 : Blo 1782092 1782883 := bstep (se 1 (by rfl) ⟨1337162, by rfl⟩ : syracuseStep 1782883 = 2674325) B2674325
theorem B2856035 : Blo 1782092 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B2675825 : Blo 1782092 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B1782899 : Blo 1782092 1782899 := bstep (se 1 (by rfl) ⟨1337174, by rfl⟩ : syracuseStep 1782899 = 2674349) B2674349
theorem B1782915 : Blo 1782092 1782915 := bstep (se 1 (by rfl) ⟨1337186, by rfl⟩ : syracuseStep 1782915 = 2674373) B2674373
theorem B2675843 : Blo 1782092 2675843 := bstep (se 1 (by rfl) ⟨2006882, by rfl⟩ : syracuseStep 2675843 = 4013765) B4013765
theorem B1782931 : Blo 1782092 1782931 := bstep (se 1 (by rfl) ⟨1337198, by rfl⟩ : syracuseStep 1782931 = 2674397) B2674397
theorem B2675873 : Blo 1782092 2675873 := bstep (se 2 (by rfl) ⟨1003452, by rfl⟩ : syracuseStep 2675873 = 2006905) B2006905
theorem B1782947 : Blo 1782092 1782947 := bstep (se 1 (by rfl) ⟨1337210, by rfl⟩ : syracuseStep 1782947 = 2674421) B2674421
theorem B1782963 : Blo 1782092 1782963 := bstep (se 1 (by rfl) ⟨1337222, by rfl⟩ : syracuseStep 1782963 = 2674445) B2674445
theorem B2675891 : Blo 1782092 2675891 := bstep (se 1 (by rfl) ⟨2006918, by rfl⟩ : syracuseStep 2675891 = 4013837) B4013837
theorem B1782979 : Blo 1782092 1782979 := bstep (se 1 (by rfl) ⟨1337234, by rfl⟩ : syracuseStep 1782979 = 2674469) B2674469
theorem B13538501 : Blo 1782092 13538501 := bstep (se 4 (by rfl) ⟨1269234, by rfl⟩ : syracuseStep 13538501 = 2538469) B2538469
theorem B2675921 : Blo 1782092 2675921 := bstep (se 2 (by rfl) ⟨1003470, by rfl⟩ : syracuseStep 2675921 = 2006941) B2006941
theorem B1782995 : Blo 1782092 1782995 := bstep (se 1 (by rfl) ⟨1337246, by rfl⟩ : syracuseStep 1782995 = 2674493) B2674493
theorem B1783011 : Blo 1782092 1783011 := bstep (se 1 (by rfl) ⟨1337258, by rfl⟩ : syracuseStep 1783011 = 2674517) B2674517
theorem B50140387 : Blo 1782092 50140387 := bstep (se 1 (by rfl) ⟨37605290, by rfl⟩ : syracuseStep 50140387 = 75210581) B75210581
theorem B2856163 : Blo 1782092 2856163 := bstep (se 1 (by rfl) ⟨2142122, by rfl⟩ : syracuseStep 2856163 = 4284245) B4284245
theorem B2675939 : Blo 1782092 2675939 := bstep (se 1 (by rfl) ⟨2006954, by rfl⟩ : syracuseStep 2675939 = 4013909) B4013909
theorem B4510961 : Blo 1782092 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B5076209 : Blo 1782092 5076209 := bstep (se 2 (by rfl) ⟨1903578, by rfl⟩ : syracuseStep 5076209 = 3807157) B3807157
theorem B1783027 : Blo 1782092 1783027 := bstep (se 1 (by rfl) ⟨1337270, by rfl⟩ : syracuseStep 1783027 = 2674541) B2674541
theorem B11425009 : Blo 1782092 11425009 := bstep (se 2 (by rfl) ⟨4284378, by rfl⟩ : syracuseStep 11425009 = 8568757) B8568757
theorem B1783043 : Blo 1782092 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B2675969 : Blo 1782092 2675969 := bstep (se 2 (by rfl) ⟨1003488, by rfl⟩ : syracuseStep 2675969 = 2006977) B2006977
theorem B4011281 : Blo 1782092 4011281 := bstep (se 2 (by rfl) ⟨1504230, by rfl⟩ : syracuseStep 4011281 = 3008461) B3008461
theorem B1783059 : Blo 1782092 1783059 := bstep (se 1 (by rfl) ⟨1337294, by rfl⟩ : syracuseStep 1783059 = 2674589) B2674589
theorem B2675987 : Blo 1782092 2675987 := bstep (se 1 (by rfl) ⟨2006990, by rfl⟩ : syracuseStep 2675987 = 4013981) B4013981
theorem B4511011 : Blo 1782092 4511011 := bstep (se 1 (by rfl) ⟨3383258, by rfl⟩ : syracuseStep 4511011 = 6766517) B6766517
theorem B12195107 : Blo 1782092 12195107 := bstep (se 1 (by rfl) ⟨9146330, by rfl⟩ : syracuseStep 12195107 = 18292661) B18292661
theorem B4011299 : Blo 1782092 4011299 := bstep (se 1 (by rfl) ⟨3008474, by rfl⟩ : syracuseStep 4011299 = 6016949) B6016949
theorem B1783075 : Blo 1782092 1783075 := bstep (se 1 (by rfl) ⟨1337306, by rfl⟩ : syracuseStep 1783075 = 2674613) B2674613
theorem B6018353 : Blo 1782092 6018353 := bstep (se 2 (by rfl) ⟨2256882, by rfl⟩ : syracuseStep 6018353 = 4513765) B4513765
theorem B2676017 : Blo 1782092 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B1783091 : Blo 1782092 1783091 := bstep (se 1 (by rfl) ⟨1337318, by rfl⟩ : syracuseStep 1783091 = 2674637) B2674637
theorem B1783107 : Blo 1782092 1783107 := bstep (se 1 (by rfl) ⟨1337330, by rfl⟩ : syracuseStep 1783107 = 2674661) B2674661
theorem B2676035 : Blo 1782092 2676035 := bstep (se 1 (by rfl) ⟨2007026, by rfl⟩ : syracuseStep 2676035 = 4014053) B4014053
theorem B6772045 : Blo 1782092 6772045 := bstep (se 3 (by rfl) ⟨1269758, by rfl⟩ : syracuseStep 6772045 = 2539517) B2539517
theorem B1783123 : Blo 1782092 1783123 := bstep (se 1 (by rfl) ⟨1337342, by rfl⟩ : syracuseStep 1783123 = 2674685) B2674685
theorem B2676065 : Blo 1782092 2676065 := bstep (se 2 (by rfl) ⟨1003524, by rfl⟩ : syracuseStep 2676065 = 2007049) B2007049
theorem B1783139 : Blo 1782092 1783139 := bstep (se 1 (by rfl) ⟨1337354, by rfl⟩ : syracuseStep 1783139 = 2674709) B2674709
theorem B10294627 : Blo 1782092 10294627 := bstep (se 1 (by rfl) ⟨7720970, by rfl⟩ : syracuseStep 10294627 = 15441941) B15441941
theorem B5715299 : Blo 1782092 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B1783155 : Blo 1782092 1783155 := bstep (se 1 (by rfl) ⟨1337366, by rfl⟩ : syracuseStep 1783155 = 2674733) B2674733
theorem B2676083 : Blo 1782092 2676083 := bstep (se 1 (by rfl) ⟨2007062, by rfl⟩ : syracuseStep 2676083 = 4014125) B4014125
theorem B1783171 : Blo 1782092 1783171 := bstep (se 1 (by rfl) ⟨1337378, by rfl⟩ : syracuseStep 1783171 = 2674757) B2674757
theorem B2676113 : Blo 1782092 2676113 := bstep (se 2 (by rfl) ⟨1003542, by rfl⟩ : syracuseStep 2676113 = 2007085) B2007085
theorem B1783187 : Blo 1782092 1783187 := bstep (se 1 (by rfl) ⟨1337390, by rfl⟩ : syracuseStep 1783187 = 2674781) B2674781
theorem B1783203 : Blo 1782092 1783203 := bstep (se 1 (by rfl) ⟨1337402, by rfl⟩ : syracuseStep 1783203 = 2674805) B2674805
theorem B2676131 : Blo 1782092 2676131 := bstep (se 1 (by rfl) ⟨2007098, by rfl⟩ : syracuseStep 2676131 = 4014197) B4014197
theorem B4511153 : Blo 1782092 4511153 := bstep (se 2 (by rfl) ⟨1691682, by rfl⟩ : syracuseStep 4511153 = 3383365) B3383365
theorem B1783219 : Blo 1782092 1783219 := bstep (se 1 (by rfl) ⟨1337414, by rfl⟩ : syracuseStep 1783219 = 2674829) B2674829
theorem B1783235 : Blo 1782092 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B14464453 : Blo 1782092 14464453 := bstep (se 4 (by rfl) ⟨1356042, by rfl⟩ : syracuseStep 14464453 = 2712085) B2712085
theorem B1783251 : Blo 1782092 1783251 := bstep (se 1 (by rfl) ⟨1337438, by rfl⟩ : syracuseStep 1783251 = 2674877) B2674877
theorem B1783267 : Blo 1782092 1783267 := bstep (se 1 (by rfl) ⟨1337450, by rfl⟩ : syracuseStep 1783267 = 2674901) B2674901
theorem B1783283 : Blo 1782092 1783283 := bstep (se 1 (by rfl) ⟨1337462, by rfl⟩ : syracuseStep 1783283 = 2674925) B2674925
theorem B1783299 : Blo 1782092 1783299 := bstep (se 1 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 1783299 = 2674949) B2674949
theorem B1783315 : Blo 1782092 1783315 := bstep (se 1 (by rfl) ⟨1337486, by rfl⟩ : syracuseStep 1783315 = 2674973) B2674973
theorem B1783331 : Blo 1782092 1783331 := bstep (se 1 (by rfl) ⟨1337498, by rfl⟩ : syracuseStep 1783331 = 2674997) B2674997
theorem B4011569 : Blo 1782092 4011569 := bstep (se 2 (by rfl) ⟨1504338, by rfl⟩ : syracuseStep 4011569 = 3008677) B3008677
theorem B1783347 : Blo 1782092 1783347 := bstep (se 1 (by rfl) ⟨1337510, by rfl⟩ : syracuseStep 1783347 = 2675021) B2675021
theorem B4011587 : Blo 1782092 4011587 := bstep (se 1 (by rfl) ⟨3008690, by rfl⟩ : syracuseStep 4011587 = 6017381) B6017381
theorem B1783363 : Blo 1782092 1783363 := bstep (se 1 (by rfl) ⟨1337522, by rfl⟩ : syracuseStep 1783363 = 2675045) B2675045
theorem B1783379 : Blo 1782092 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B2856547 : Blo 1782092 2856547 := bstep (se 1 (by rfl) ⟨2142410, by rfl⟩ : syracuseStep 2856547 = 4284821) B4284821
theorem B1783395 : Blo 1782092 1783395 := bstep (se 1 (by rfl) ⟨1337546, by rfl⟩ : syracuseStep 1783395 = 2675093) B2675093
theorem B3806833 : Blo 1782092 3806833 := bstep (se 2 (by rfl) ⟨1427562, by rfl⟩ : syracuseStep 3806833 = 2855125) B2855125
theorem B1783411 : Blo 1782092 1783411 := bstep (se 1 (by rfl) ⟨1337558, by rfl⟩ : syracuseStep 1783411 = 2675117) B2675117
theorem B1783427 : Blo 1782092 1783427 := bstep (se 1 (by rfl) ⟨1337570, by rfl⟩ : syracuseStep 1783427 = 2675141) B2675141
theorem B1783443 : Blo 1782092 1783443 := bstep (se 1 (by rfl) ⟨1337582, by rfl⟩ : syracuseStep 1783443 = 2675165) B2675165
theorem B1783459 : Blo 1782092 1783459 := bstep (se 1 (by rfl) ⟨1337594, by rfl⟩ : syracuseStep 1783459 = 2675189) B2675189
theorem B1783475 : Blo 1782092 1783475 := bstep (se 1 (by rfl) ⟨1337606, by rfl⟩ : syracuseStep 1783475 = 2675213) B2675213
theorem B1783491 : Blo 1782092 1783491 := bstep (se 1 (by rfl) ⟨1337618, by rfl⟩ : syracuseStep 1783491 = 2675237) B2675237
theorem B1783507 : Blo 1782092 1783507 := bstep (se 1 (by rfl) ⟨1337630, by rfl⟩ : syracuseStep 1783507 = 2675261) B2675261
theorem B36607715 : Blo 1782092 36607715 := bstep (se 1 (by rfl) ⟨27455786, by rfl⟩ : syracuseStep 36607715 = 54911573) B54911573
theorem B1783523 : Blo 1782092 1783523 := bstep (se 1 (by rfl) ⟨1337642, by rfl⟩ : syracuseStep 1783523 = 2675285) B2675285
theorem B13547249 : Blo 1782092 13547249 := bstep (se 2 (by rfl) ⟨5080218, by rfl⟩ : syracuseStep 13547249 = 10160437) B10160437
theorem B1783539 : Blo 1782092 1783539 := bstep (se 1 (by rfl) ⟨1337654, by rfl⟩ : syracuseStep 1783539 = 2675309) B2675309
theorem B1783555 : Blo 1782092 1783555 := bstep (se 1 (by rfl) ⟨1337666, by rfl⟩ : syracuseStep 1783555 = 2675333) B2675333
theorem B4282129 : Blo 1782092 4282129 := bstep (se 2 (by rfl) ⟨1605798, by rfl⟩ : syracuseStep 4282129 = 3211597) B3211597
theorem B1783571 : Blo 1782092 1783571 := bstep (se 1 (by rfl) ⟨1337678, by rfl⟩ : syracuseStep 1783571 = 2675357) B2675357
theorem B1783587 : Blo 1782092 1783587 := bstep (se 1 (by rfl) ⟨1337690, by rfl⟩ : syracuseStep 1783587 = 2675381) B2675381
theorem B1783603 : Blo 1782092 1783603 := bstep (se 1 (by rfl) ⟨1337702, by rfl⟩ : syracuseStep 1783603 = 2675405) B2675405
theorem B1783619 : Blo 1782092 1783619 := bstep (se 1 (by rfl) ⟨1337714, by rfl⟩ : syracuseStep 1783619 = 2675429) B2675429
theorem B6018893 : Blo 1782092 6018893 := bstep (se 3 (by rfl) ⟨1128542, by rfl⟩ : syracuseStep 6018893 = 2257085) B2257085
theorem B4011857 : Blo 1782092 4011857 := bstep (se 2 (by rfl) ⟨1504446, by rfl⟩ : syracuseStep 4011857 = 3008893) B3008893
theorem B4577105 : Blo 1782092 4577105 := bstep (se 2 (by rfl) ⟨1716414, by rfl⟩ : syracuseStep 4577105 = 3432829) B3432829
theorem B1783635 : Blo 1782092 1783635 := bstep (se 1 (by rfl) ⟨1337726, by rfl⟩ : syracuseStep 1783635 = 2675453) B2675453
theorem B4011875 : Blo 1782092 4011875 := bstep (se 1 (by rfl) ⟨3008906, by rfl⟩ : syracuseStep 4011875 = 6017813) B6017813
theorem B2856803 : Blo 1782092 2856803 := bstep (se 1 (by rfl) ⟨2142602, by rfl⟩ : syracuseStep 2856803 = 4285205) B4285205
theorem B1783651 : Blo 1782092 1783651 := bstep (se 1 (by rfl) ⟨1337738, by rfl⟩ : syracuseStep 1783651 = 2675477) B2675477
theorem B3807089 : Blo 1782092 3807089 := bstep (se 2 (by rfl) ⟨1427658, by rfl⟩ : syracuseStep 3807089 = 2855317) B2855317
theorem B1783667 : Blo 1782092 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B6018947 : Blo 1782092 6018947 := bstep (se 1 (by rfl) ⟨4514210, by rfl⟩ : syracuseStep 6018947 = 9028421) B9028421
theorem B1783683 : Blo 1782092 1783683 := bstep (se 1 (by rfl) ⟨1337762, by rfl⟩ : syracuseStep 1783683 = 2675525) B2675525
theorem B1783699 : Blo 1782092 1783699 := bstep (se 1 (by rfl) ⟨1337774, by rfl⟩ : syracuseStep 1783699 = 2675549) B2675549
theorem B1783715 : Blo 1782092 1783715 := bstep (se 1 (by rfl) ⟨1337786, by rfl⟩ : syracuseStep 1783715 = 2675573) B2675573
theorem B1783731 : Blo 1782092 1783731 := bstep (se 1 (by rfl) ⟨1337798, by rfl⟩ : syracuseStep 1783731 = 2675597) B2675597
theorem B1783747 : Blo 1782092 1783747 := bstep (se 1 (by rfl) ⟨1337810, by rfl⟩ : syracuseStep 1783747 = 2675621) B2675621
theorem B1783763 : Blo 1782092 1783763 := bstep (se 1 (by rfl) ⟨1337822, by rfl⟩ : syracuseStep 1783763 = 2675645) B2675645
theorem B22853603 : Blo 1782092 22853603 := bstep (se 1 (by rfl) ⟨17140202, by rfl⟩ : syracuseStep 22853603 = 34280405) B34280405
theorem B1783779 : Blo 1782092 1783779 := bstep (se 1 (by rfl) ⟨1337834, by rfl⟩ : syracuseStep 1783779 = 2675669) B2675669
theorem B2004979 : Blo 1782092 2004979 := bstep (se 1 (by rfl) ⟨1503734, by rfl⟩ : syracuseStep 2004979 = 3007469) B3007469
theorem B1783795 : Blo 1782092 1783795 := bstep (se 1 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 1783795 = 2675693) B2675693
theorem B1783811 : Blo 1782092 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B1783827 : Blo 1782092 1783827 := bstep (se 1 (by rfl) ⟨1337870, by rfl⟩ : syracuseStep 1783827 = 2675741) B2675741
theorem B2537507 : Blo 1782092 2537507 := bstep (se 1 (by rfl) ⟨1903130, by rfl⟩ : syracuseStep 2537507 = 3806261) B3806261
theorem B1783843 : Blo 1782092 1783843 := bstep (se 1 (by rfl) ⟨1337882, by rfl⟩ : syracuseStep 1783843 = 2675765) B2675765
theorem B1783859 : Blo 1782092 1783859 := bstep (se 1 (by rfl) ⟨1337894, by rfl⟩ : syracuseStep 1783859 = 2675789) B2675789
theorem B1783875 : Blo 1782092 1783875 := bstep (se 1 (by rfl) ⟨1337906, by rfl⟩ : syracuseStep 1783875 = 2675813) B2675813
theorem B1783891 : Blo 1782092 1783891 := bstep (se 1 (by rfl) ⟨1337918, by rfl⟩ : syracuseStep 1783891 = 2675837) B2675837
theorem B6772835 : Blo 1782092 6772835 := bstep (se 1 (by rfl) ⟨5079626, by rfl⟩ : syracuseStep 6772835 = 10159253) B10159253
theorem B1783907 : Blo 1782092 1783907 := bstep (se 1 (by rfl) ⟨1337930, by rfl⟩ : syracuseStep 1783907 = 2675861) B2675861
theorem B4012145 : Blo 1782092 4012145 := bstep (se 2 (by rfl) ⟨1504554, by rfl⟩ : syracuseStep 4012145 = 3009109) B3009109
theorem B1783923 : Blo 1782092 1783923 := bstep (se 1 (by rfl) ⟨1337942, by rfl⟩ : syracuseStep 1783923 = 2675885) B2675885
theorem B2005123 : Blo 1782092 2005123 := bstep (se 1 (by rfl) ⟨1503842, by rfl⟩ : syracuseStep 2005123 = 3007685) B3007685
theorem B4012163 : Blo 1782092 4012163 := bstep (se 1 (by rfl) ⟨3009122, by rfl⟩ : syracuseStep 4012163 = 6018245) B6018245
theorem B1783939 : Blo 1782092 1783939 := bstep (se 1 (by rfl) ⟨1337954, by rfl⟩ : syracuseStep 1783939 = 2675909) B2675909
theorem B6600845 : Blo 1782092 6600845 := bstep (se 3 (by rfl) ⟨1237658, by rfl⟩ : syracuseStep 6600845 = 2475317) B2475317
theorem B6019217 : Blo 1782092 6019217 := bstep (se 2 (by rfl) ⟨2257206, by rfl⟩ : syracuseStep 6019217 = 4514413) B4514413
theorem B1783955 : Blo 1782092 1783955 := bstep (se 1 (by rfl) ⟨1337966, by rfl⟩ : syracuseStep 1783955 = 2675933) B2675933
theorem B1783971 : Blo 1782092 1783971 := bstep (se 1 (by rfl) ⟨1337978, by rfl⟩ : syracuseStep 1783971 = 2675957) B2675957
theorem B1783987 : Blo 1782092 1783987 := bstep (se 1 (by rfl) ⟨1337990, by rfl⟩ : syracuseStep 1783987 = 2675981) B2675981
theorem B1784003 : Blo 1782092 1784003 := bstep (se 1 (by rfl) ⟨1338002, by rfl⟩ : syracuseStep 1784003 = 2676005) B2676005
theorem B5077201 : Blo 1782092 5077201 := bstep (se 2 (by rfl) ⟨1903950, by rfl⟩ : syracuseStep 5077201 = 3807901) B3807901
theorem B1784019 : Blo 1782092 1784019 := bstep (se 1 (by rfl) ⟨1338014, by rfl⟩ : syracuseStep 1784019 = 2676029) B2676029
theorem B1784035 : Blo 1782092 1784035 := bstep (se 1 (by rfl) ⟨1338026, by rfl⟩ : syracuseStep 1784035 = 2676053) B2676053
theorem B1784051 : Blo 1782092 1784051 := bstep (se 1 (by rfl) ⟨1338038, by rfl⟩ : syracuseStep 1784051 = 2676077) B2676077
theorem B1784067 : Blo 1782092 1784067 := bstep (se 1 (by rfl) ⟨1338050, by rfl⟩ : syracuseStep 1784067 = 2676101) B2676101
theorem B2005267 : Blo 1782092 2005267 := bstep (se 1 (by rfl) ⟨1503950, by rfl⟩ : syracuseStep 2005267 = 3007901) B3007901
theorem B1784083 : Blo 1782092 1784083 := bstep (se 1 (by rfl) ⟨1338062, by rfl⟩ : syracuseStep 1784083 = 2676125) B2676125
theorem B10156337 : Blo 1782092 10156337 := bstep (se 2 (by rfl) ⟨3808626, by rfl⟩ : syracuseStep 10156337 = 7617253) B7617253
theorem B2857265 : Blo 1782092 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B83507597 : Blo 1782092 83507597 := bstep (se 3 (by rfl) ⟨15657674, by rfl⟩ : syracuseStep 83507597 = 31315349) B31315349
theorem B4512145 : Blo 1782092 4512145 := bstep (se 2 (by rfl) ⟨1692054, by rfl⟩ : syracuseStep 4512145 = 3384109) B3384109
theorem B4012433 : Blo 1782092 4012433 := bstep (se 2 (by rfl) ⟨1504662, by rfl⟩ : syracuseStep 4012433 = 3009325) B3009325
theorem B2857361 : Blo 1782092 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B2005411 : Blo 1782092 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B4012451 : Blo 1782092 4012451 := bstep (se 1 (by rfl) ⟨3009338, by rfl⟩ : syracuseStep 4012451 = 6018677) B6018677
theorem B2857393 : Blo 1782092 2857393 := bstep (se 2 (by rfl) ⟨1071522, by rfl⟩ : syracuseStep 2857393 = 2143045) B2143045
theorem B7829965 : Blo 1782092 7829965 := bstep (se 3 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 7829965 = 2936237) B2936237
theorem B5077475 : Blo 1782092 5077475 := bstep (se 1 (by rfl) ⟨3808106, by rfl⟩ : syracuseStep 5077475 = 7616213) B7616213
theorem B2005555 : Blo 1782092 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B2538145 : Blo 1782092 2538145 := bstep (se 2 (by rfl) ⟨951804, by rfl⟩ : syracuseStep 2538145 = 1903609) B1903609
theorem B4512419 : Blo 1782092 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B5077667 : Blo 1782092 5077667 := bstep (se 1 (by rfl) ⟨3808250, by rfl⟩ : syracuseStep 5077667 = 7616501) B7616501
theorem B6019757 : Blo 1782092 6019757 := bstep (se 3 (by rfl) ⟨1128704, by rfl⟩ : syracuseStep 6019757 = 2257409) B2257409
theorem B4012721 : Blo 1782092 4012721 := bstep (se 2 (by rfl) ⟨1504770, by rfl⟩ : syracuseStep 4012721 = 3009541) B3009541
theorem B2005699 : Blo 1782092 2005699 := bstep (se 1 (by rfl) ⟨1504274, by rfl⟩ : syracuseStep 2005699 = 3008549) B3008549
theorem B4012739 : Blo 1782092 4012739 := bstep (se 1 (by rfl) ⟨3009554, by rfl⟩ : syracuseStep 4012739 = 6019109) B6019109
theorem B6019811 : Blo 1782092 6019811 := bstep (se 1 (by rfl) ⟨4514858, by rfl⟩ : syracuseStep 6019811 = 9029717) B9029717
theorem B13392611 : Blo 1782092 13392611 := bstep (se 1 (by rfl) ⟨10044458, by rfl⟩ : syracuseStep 13392611 = 20088917) B20088917
theorem B5421809 : Blo 1782092 5421809 := bstep (se 2 (by rfl) ⟨2033178, by rfl⟩ : syracuseStep 5421809 = 4066357) B4066357
theorem B6773489 : Blo 1782092 6773489 := bstep (se 2 (by rfl) ⟨2540058, by rfl⟩ : syracuseStep 6773489 = 5080117) B5080117
theorem B2005843 : Blo 1782092 2005843 := bstep (se 1 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 2005843 = 3008765) B3008765
theorem B4512611 : Blo 1782092 4512611 := bstep (se 1 (by rfl) ⟨3384458, by rfl⟩ : syracuseStep 4512611 = 6768917) B6768917
theorem B8682353 : Blo 1782092 8682353 := bstep (se 2 (by rfl) ⟨3255882, by rfl⟩ : syracuseStep 8682353 = 6511765) B6511765
theorem B30464909 : Blo 1782092 30464909 := bstep (se 3 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 30464909 = 11424341) B11424341
theorem B4013009 : Blo 1782092 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B2005987 : Blo 1782092 2005987 := bstep (se 1 (by rfl) ⟨1504490, by rfl⟩ : syracuseStep 2005987 = 3008981) B3008981
theorem B4013027 : Blo 1782092 4013027 := bstep (se 1 (by rfl) ⟨3009770, by rfl⟩ : syracuseStep 4013027 = 6019541) B6019541
theorem B2538481 : Blo 1782092 2538481 := bstep (se 2 (by rfl) ⟨951930, by rfl⟩ : syracuseStep 2538481 = 1903861) B1903861
theorem B6020081 : Blo 1782092 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B2644993 : Blo 1782092 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B45677681 : Blo 1782092 45677681 := bstep (se 2 (by rfl) ⟨17129130, by rfl⟩ : syracuseStep 45677681 = 34258261) B34258261
theorem B2006131 : Blo 1782092 2006131 := bstep (se 1 (by rfl) ⟨1504598, by rfl⟩ : syracuseStep 2006131 = 3009197) B3009197
theorem B3808387 : Blo 1782092 3808387 := bstep (se 1 (by rfl) ⟨2856290, by rfl⟩ : syracuseStep 3808387 = 5712581) B5712581
theorem B9026801 : Blo 1782092 9026801 := bstep (se 2 (by rfl) ⟨3385050, by rfl⟩ : syracuseStep 9026801 = 6770101) B6770101
theorem B4013297 : Blo 1782092 4013297 := bstep (se 2 (by rfl) ⟨1504986, by rfl⟩ : syracuseStep 4013297 = 3009973) B3009973
theorem B2006275 : Blo 1782092 2006275 := bstep (se 1 (by rfl) ⟨1504706, by rfl⟩ : syracuseStep 2006275 = 3009413) B3009413
theorem B4013315 : Blo 1782092 4013315 := bstep (se 1 (by rfl) ⟨3009986, by rfl⟩ : syracuseStep 4013315 = 6019973) B6019973
theorem B6864227 : Blo 1782092 6864227 := bstep (se 1 (by rfl) ⟨5148170, by rfl⟩ : syracuseStep 6864227 = 10296341) B10296341
theorem B34282865 : Blo 1782092 34282865 := bstep (se 2 (by rfl) ⟨12856074, by rfl⟩ : syracuseStep 34282865 = 25712149) B25712149
theorem B2006419 : Blo 1782092 2006419 := bstep (se 1 (by rfl) ⟨1504814, by rfl⟩ : syracuseStep 2006419 = 3009629) B3009629
theorem B5078477 : Blo 1782092 5078477 := bstep (se 3 (by rfl) ⟨952214, by rfl⟩ : syracuseStep 5078477 = 1904429) B1904429
theorem B3808721 : Blo 1782092 3808721 := bstep (se 2 (by rfl) ⟨1428270, by rfl⟩ : syracuseStep 3808721 = 2856541) B2856541
theorem B12361187 : Blo 1782092 12361187 := bstep (se 1 (by rfl) ⟨9270890, by rfl⟩ : syracuseStep 12361187 = 18541781) B18541781
theorem B6020621 : Blo 1782092 6020621 := bstep (se 3 (by rfl) ⟨1128866, by rfl⟩ : syracuseStep 6020621 = 2257733) B2257733
theorem B4013585 : Blo 1782092 4013585 := bstep (se 2 (by rfl) ⟨1505094, by rfl⟩ : syracuseStep 4013585 = 3010189) B3010189
theorem B2006563 : Blo 1782092 2006563 := bstep (se 1 (by rfl) ⟨1504922, by rfl⟩ : syracuseStep 2006563 = 3009845) B3009845
theorem B4013603 : Blo 1782092 4013603 := bstep (se 1 (by rfl) ⟨3010202, by rfl⟩ : syracuseStep 4013603 = 6020405) B6020405
theorem B2539073 : Blo 1782092 2539073 := bstep (se 2 (by rfl) ⟨952152, by rfl⟩ : syracuseStep 2539073 = 1904305) B1904305
theorem B6020675 : Blo 1782092 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B7233101 : Blo 1782092 7233101 := bstep (se 3 (by rfl) ⟨1356206, by rfl⟩ : syracuseStep 7233101 = 2712413) B2712413
theorem B5078659 : Blo 1782092 5078659 := bstep (se 1 (by rfl) ⟨3808994, by rfl⟩ : syracuseStep 5078659 = 7617989) B7617989
theorem B7618211 : Blo 1782092 7618211 := bstep (se 1 (by rfl) ⟨5713658, by rfl⟩ : syracuseStep 7618211 = 11427317) B11427317
theorem B2006707 : Blo 1782092 2006707 := bstep (se 1 (by rfl) ⟨1505030, by rfl⟩ : syracuseStep 2006707 = 3010061) B3010061
theorem B20577989 : Blo 1782092 20577989 := bstep (se 4 (by rfl) ⟨1929186, by rfl⟩ : syracuseStep 20577989 = 3858373) B3858373
theorem B3301091 : Blo 1782092 3301091 := bstep (se 1 (by rfl) ⟨2475818, by rfl⟩ : syracuseStep 3301091 = 4951637) B4951637
theorem B10157795 : Blo 1782092 10157795 := bstep (se 1 (by rfl) ⟨7618346, by rfl⟩ : syracuseStep 10157795 = 15236693) B15236693
theorem B4513553 : Blo 1782092 4513553 := bstep (se 2 (by rfl) ⟨1692582, by rfl⟩ : syracuseStep 4513553 = 3385165) B3385165
theorem B4013873 : Blo 1782092 4013873 := bstep (se 2 (by rfl) ⟨1505202, by rfl⟩ : syracuseStep 4013873 = 3010405) B3010405
theorem B5709635 : Blo 1782092 5709635 := bstep (se 1 (by rfl) ⟨4282226, by rfl⟩ : syracuseStep 5709635 = 8564453) B8564453
theorem B4513603 : Blo 1782092 4513603 := bstep (se 1 (by rfl) ⟨3385202, by rfl⟩ : syracuseStep 4513603 = 6770405) B6770405
theorem B2006851 : Blo 1782092 2006851 := bstep (se 1 (by rfl) ⟨1505138, by rfl⟩ : syracuseStep 2006851 = 3010277) B3010277
theorem B4013891 : Blo 1782092 4013891 := bstep (se 1 (by rfl) ⟨3010418, by rfl⟩ : syracuseStep 4013891 = 6020837) B6020837
theorem B2981713 : Blo 1782092 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B6020945 : Blo 1782092 6020945 := bstep (se 2 (by rfl) ⟨2257854, by rfl⟩ : syracuseStep 6020945 = 4515709) B4515709
theorem B10149731 : Blo 1782092 10149731 := bstep (se 1 (by rfl) ⟨7612298, by rfl⟩ : syracuseStep 10149731 = 15224597) B15224597
theorem B4513745 : Blo 1782092 4513745 := bstep (se 2 (by rfl) ⟨1692654, by rfl⟩ : syracuseStep 4513745 = 3385309) B3385309
theorem B2006995 : Blo 1782092 2006995 := bstep (se 1 (by rfl) ⟨1505246, by rfl⟩ : syracuseStep 2006995 = 3010493) B3010493
theorem B13533155 : Blo 1782092 13533155 := bstep (se 1 (by rfl) ⟨10149866, by rfl⟩ : syracuseStep 13533155 = 20299733) B20299733
theorem B14106629 : Blo 1782092 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B6766685 : Blo 1782092 6766685 := bstep (se 3 (by rfl) ⟨1268753, by rfl⟩ : syracuseStep 6766685 = 2537507) B2537507
theorem B28213379 : Blo 1782092 28213379 := bstep (se 1 (by rfl) ⟨21160034, by rfl⟩ : syracuseStep 28213379 = 42320069) B42320069
theorem B7618961 : Blo 1782092 7618961 := bstep (se 2 (by rfl) ⟨2857110, by rfl⟩ : syracuseStep 7618961 = 5714221) B5714221
theorem B2539927 : Blo 1782092 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B4514251 : Blo 1782092 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B3809857 : Blo 1782092 3809857 := bstep (se 2 (by rfl) ⟨1428696, by rfl⟩ : syracuseStep 3809857 = 2857393) B2857393
theorem B25707077 : Blo 1782092 25707077 := bstep (se 4 (by rfl) ⟨2410038, by rfl⟩ : syracuseStep 25707077 = 4820077) B4820077
theorem B4817483 : Blo 1782092 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B4514393 : Blo 1782092 4514393 := bstep (se 2 (by rfl) ⟨1692897, by rfl⟩ : syracuseStep 4514393 = 3385795) B3385795
theorem B3211915 : Blo 1782092 3211915 := bstep (se 1 (by rfl) ⟨2408936, by rfl⟩ : syracuseStep 3211915 = 4817873) B4817873
theorem B3384011 : Blo 1782092 3384011 := bstep (se 1 (by rfl) ⟨2538008, by rfl⟩ : syracuseStep 3384011 = 5076017) B5076017
theorem B3007307 : Blo 1782092 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B10150757 : Blo 1782092 10150757 := bstep (se 4 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 10150757 = 1903267) B1903267
theorem B3384193 : Blo 1782092 3384193 := bstep (se 2 (by rfl) ⟨1269072, by rfl⟩ : syracuseStep 3384193 = 2538145) B2538145
theorem B10158979 : Blo 1782092 10158979 := bstep (se 1 (by rfl) ⟨7619234, by rfl⟩ : syracuseStep 10158979 = 15238469) B15238469
theorem B3810199 : Blo 1782092 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B3212225 : Blo 1782092 3212225 := bstep (se 2 (by rfl) ⟨1204584, by rfl⟩ : syracuseStep 3212225 = 2409169) B2409169
theorem B3007435 : Blo 1782092 3007435 := bstep (se 1 (by rfl) ⟨2255576, by rfl⟩ : syracuseStep 3007435 = 4511153) B4511153
theorem B7619629 : Blo 1782092 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B3007577 : Blo 1782092 3007577 := bstep (se 2 (by rfl) ⟨1127841, by rfl⟩ : syracuseStep 3007577 = 2255683) B2255683
theorem B24405143 : Blo 1782092 24405143 := bstep (se 1 (by rfl) ⟨18303857, by rfl⟩ : syracuseStep 24405143 = 36607715) B36607715
theorem B2032823 : Blo 1782092 2032823 := bstep (se 1 (by rfl) ⟨1524617, by rfl⟩ : syracuseStep 2032823 = 3049235) B3049235
theorem B14451929 : Blo 1782092 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B3007705 : Blo 1782092 3007705 := bstep (se 2 (by rfl) ⟨1127889, by rfl⟩ : syracuseStep 3007705 = 2255779) B2255779
theorem B3384641 : Blo 1782092 3384641 := bstep (se 2 (by rfl) ⟨1269240, by rfl⟩ : syracuseStep 3384641 = 2538481) B2538481
theorem B4515223 : Blo 1782092 4515223 := bstep (se 1 (by rfl) ⟨3386417, by rfl⟩ : syracuseStep 4515223 = 6772835) B6772835
theorem B4400563 : Blo 1782092 4400563 := bstep (se 1 (by rfl) ⟨3300422, by rfl⟩ : syracuseStep 4400563 = 6600845) B6600845
theorem B3212723 : Blo 1782092 3212723 := bstep (se 1 (by rfl) ⟨2409542, by rfl⟩ : syracuseStep 3212723 = 4819085) B4819085
theorem B24725027 : Blo 1782092 24725027 := bstep (se 1 (by rfl) ⟨18543770, by rfl⟩ : syracuseStep 24725027 = 37087541) B37087541
theorem B7620227 : Blo 1782092 7620227 := bstep (se 1 (by rfl) ⟨5715170, by rfl⟩ : syracuseStep 7620227 = 11430341) B11430341
theorem B3212939 : Blo 1782092 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B3384983 : Blo 1782092 3384983 := bstep (se 1 (by rfl) ⟨2538737, by rfl⟩ : syracuseStep 3384983 = 5077475) B5077475
theorem B6014681 : Blo 1782092 6014681 := bstep (se 2 (by rfl) ⟨2255505, by rfl⟩ : syracuseStep 6014681 = 4511011) B4511011
theorem B9029393 : Blo 1782092 9029393 := bstep (se 2 (by rfl) ⟨3386022, by rfl⟩ : syracuseStep 9029393 = 6772045) B6772045
theorem B3008279 : Blo 1782092 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B10159937 : Blo 1782092 10159937 := bstep (se 2 (by rfl) ⟨3809976, by rfl⟩ : syracuseStep 10159937 = 7619953) B7619953
theorem B3614539 : Blo 1782092 3614539 := bstep (se 1 (by rfl) ⟨2710904, by rfl⟩ : syracuseStep 3614539 = 5421809) B5421809
theorem B4515659 : Blo 1782092 4515659 := bstep (se 1 (by rfl) ⟨3386744, by rfl⟩ : syracuseStep 4515659 = 6773489) B6773489
theorem B3008407 : Blo 1782092 3008407 := bstep (se 1 (by rfl) ⟨2256305, by rfl⟩ : syracuseStep 3008407 = 4512611) B4512611
theorem B19285937 : Blo 1782092 19285937 := bstep (se 2 (by rfl) ⟨7232226, by rfl⟩ : syracuseStep 19285937 = 14464453) B14464453
theorem B20309939 : Blo 1782092 20309939 := bstep (se 1 (by rfl) ⟨15232454, by rfl⟩ : syracuseStep 20309939 = 30464909) B30464909
theorem B9029555 : Blo 1782092 9029555 := bstep (se 1 (by rfl) ⟨6772166, by rfl⟩ : syracuseStep 9029555 = 13544333) B13544333
theorem B6768643 : Blo 1782092 6768643 := bstep (se 1 (by rfl) ⟨5076482, by rfl⟩ : syracuseStep 6768643 = 10152965) B10152965
theorem B30451787 : Blo 1782092 30451787 := bstep (se 1 (by rfl) ⟨22838840, by rfl⟩ : syracuseStep 30451787 = 45677681) B45677681
theorem B11429981 : Blo 1782092 11429981 := bstep (se 3 (by rfl) ⟨2143121, by rfl⟩ : syracuseStep 11429981 = 4286243) B4286243
theorem B4286657 : Blo 1782092 4286657 := bstep (se 2 (by rfl) ⟨1607496, by rfl⟩ : syracuseStep 4286657 = 3214993) B3214993
theorem B6768947 : Blo 1782092 6768947 := bstep (se 1 (by rfl) ⟨5076710, by rfl⟩ : syracuseStep 6768947 = 10153421) B10153421
theorem B3385651 : Blo 1782092 3385651 := bstep (se 1 (by rfl) ⟨2539238, by rfl⟩ : syracuseStep 3385651 = 5078477) B5078477
theorem B5146973 : Blo 1782092 5146973 := bstep (se 3 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 5146973 = 1930115) B1930115
theorem B6015383 : Blo 1782092 6015383 := bstep (se 1 (by rfl) ⟨4511537, by rfl⟩ : syracuseStep 6015383 = 9023075) B9023075
theorem B3975617 : Blo 1782092 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B10291673 : Blo 1782092 10291673 := bstep (se 2 (by rfl) ⟨3859377, by rfl⟩ : syracuseStep 10291673 = 7718755) B7718755
theorem B3009035 : Blo 1782092 3009035 := bstep (se 1 (by rfl) ⟨2256776, by rfl⟩ : syracuseStep 3009035 = 4513553) B4513553
theorem B2673227 : Blo 1782092 2673227 := bstep (se 1 (by rfl) ⟨2004920, by rfl⟩ : syracuseStep 2673227 = 4009841) B4009841
theorem B2673239 : Blo 1782092 2673239 := bstep (se 1 (by rfl) ⟨2004929, by rfl⟩ : syracuseStep 2673239 = 4009859) B4009859
theorem B3009163 : Blo 1782092 3009163 := bstep (se 1 (by rfl) ⟨2256872, by rfl⟩ : syracuseStep 3009163 = 4513745) B4513745
theorem B9022103 : Blo 1782092 9022103 := bstep (se 1 (by rfl) ⟨6766577, by rfl⟩ : syracuseStep 9022103 = 13533155) B13533155
theorem B2673305 : Blo 1782092 2673305 := bstep (se 2 (by rfl) ⟨1002489, by rfl⟩ : syracuseStep 2673305 = 2004979) B2004979
theorem B3386099 : Blo 1782092 3386099 := bstep (se 1 (by rfl) ⟨2539574, by rfl⟩ : syracuseStep 3386099 = 5079149) B5079149
theorem B2255627 : Blo 1782092 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B2673419 : Blo 1782092 2673419 := bstep (se 1 (by rfl) ⟨2005064, by rfl⟩ : syracuseStep 2673419 = 4010129) B4010129
theorem B2673431 : Blo 1782092 2673431 := bstep (se 1 (by rfl) ⟨2005073, by rfl⟩ : syracuseStep 2673431 = 4010147) B4010147
theorem B3009305 : Blo 1782092 3009305 := bstep (se 2 (by rfl) ⟨1128489, by rfl⟩ : syracuseStep 3009305 = 2256979) B2256979
theorem B3386137 : Blo 1782092 3386137 := bstep (se 2 (by rfl) ⟨1269801, by rfl⟩ : syracuseStep 3386137 = 2539603) B2539603
theorem B2673497 : Blo 1782092 2673497 := bstep (se 2 (by rfl) ⟨1002561, by rfl⟩ : syracuseStep 2673497 = 2005123) B2005123
theorem B12848003 : Blo 1782092 12848003 := bstep (se 1 (by rfl) ⟨9636002, by rfl⟩ : syracuseStep 12848003 = 19272005) B19272005
theorem B3009433 : Blo 1782092 3009433 := bstep (se 2 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 3009433 = 2257075) B2257075
theorem B6015923 : Blo 1782092 6015923 := bstep (se 1 (by rfl) ⟨4511942, by rfl⟩ : syracuseStep 6015923 = 9023885) B9023885
theorem B6769601 : Blo 1782092 6769601 := bstep (se 2 (by rfl) ⟨2538600, by rfl⟩ : syracuseStep 6769601 = 5077201) B5077201
theorem B2673611 : Blo 1782092 2673611 := bstep (se 1 (by rfl) ⟨2005208, by rfl⟩ : syracuseStep 2673611 = 4010417) B4010417
theorem B2673623 : Blo 1782092 2673623 := bstep (se 1 (by rfl) ⟨2005217, by rfl⟩ : syracuseStep 2673623 = 4010435) B4010435
theorem B2673689 : Blo 1782092 2673689 := bstep (se 2 (by rfl) ⟨1002633, by rfl⟩ : syracuseStep 2673689 = 2005267) B2005267
theorem B6425675 : Blo 1782092 6425675 := bstep (se 1 (by rfl) ⟨4819256, by rfl⟩ : syracuseStep 6425675 = 9638513) B9638513
theorem B6425731 : Blo 1782092 6425731 := bstep (se 1 (by rfl) ⟨4819298, by rfl⟩ : syracuseStep 6425731 = 9638597) B9638597
theorem B2673803 : Blo 1782092 2673803 := bstep (se 1 (by rfl) ⟨2005352, by rfl⟩ : syracuseStep 2673803 = 4010705) B4010705
theorem B3214475 : Blo 1782092 3214475 := bstep (se 1 (by rfl) ⟨2410856, by rfl⟩ : syracuseStep 3214475 = 4821713) B4821713
theorem B2673815 : Blo 1782092 2673815 := bstep (se 1 (by rfl) ⟨2005361, by rfl⟩ : syracuseStep 2673815 = 4010723) B4010723
theorem B6016193 : Blo 1782092 6016193 := bstep (se 2 (by rfl) ⟨2256072, by rfl⟩ : syracuseStep 6016193 = 4512145) B4512145
theorem B6859993 : Blo 1782092 6859993 := bstep (se 2 (by rfl) ⟨2572497, by rfl⟩ : syracuseStep 6859993 = 5144995) B5144995
theorem B2673881 : Blo 1782092 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B3386585 : Blo 1782092 3386585 := bstep (se 2 (by rfl) ⟨1269969, by rfl⟩ : syracuseStep 3386585 = 2539939) B2539939
theorem B13536557 : Blo 1782092 13536557 := bstep (se 3 (by rfl) ⟨2538104, by rfl⟩ : syracuseStep 13536557 = 5076209) B5076209
theorem B2673995 : Blo 1782092 2673995 := bstep (se 1 (by rfl) ⟨2005496, by rfl⟩ : syracuseStep 2673995 = 4010993) B4010993
theorem B2674007 : Blo 1782092 2674007 := bstep (se 1 (by rfl) ⟨2005505, by rfl⟩ : syracuseStep 2674007 = 4011011) B4011011
theorem B9637213 : Blo 1782092 9637213 := bstep (se 3 (by rfl) ⟨1806977, by rfl⟩ : syracuseStep 9637213 = 3613955) B3613955
theorem B20311397 : Blo 1782092 20311397 := bstep (se 4 (by rfl) ⟨1904193, by rfl⟩ : syracuseStep 20311397 = 3808387) B3808387
theorem B1904023 : Blo 1782092 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B2674073 : Blo 1782092 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B2256331 : Blo 1782092 2256331 := bstep (se 1 (by rfl) ⟨1692248, by rfl⟩ : syracuseStep 2256331 = 3384497) B3384497
theorem B3010007 : Blo 1782092 3010007 := bstep (se 1 (by rfl) ⟨2257505, by rfl⟩ : syracuseStep 3010007 = 4515011) B4515011
theorem B2674187 : Blo 1782092 2674187 := bstep (se 1 (by rfl) ⟨2005640, by rfl⟩ : syracuseStep 2674187 = 4011281) B4011281
theorem B8130071 : Blo 1782092 8130071 := bstep (se 1 (by rfl) ⟨6097553, by rfl⟩ : syracuseStep 8130071 = 12195107) B12195107
theorem B2674199 : Blo 1782092 2674199 := bstep (se 1 (by rfl) ⟨2005649, by rfl⟩ : syracuseStep 2674199 = 4011299) B4011299
theorem B3010135 : Blo 1782092 3010135 := bstep (se 1 (by rfl) ⟨2257601, by rfl⟩ : syracuseStep 3010135 = 4515203) B4515203
theorem B2674265 : Blo 1782092 2674265 := bstep (se 2 (by rfl) ⟨1002849, by rfl⟩ : syracuseStep 2674265 = 2005699) B2005699
theorem B2674379 : Blo 1782092 2674379 := bstep (se 1 (by rfl) ⟨2005784, by rfl⟩ : syracuseStep 2674379 = 4011569) B4011569
theorem B2674391 : Blo 1782092 2674391 := bstep (se 1 (by rfl) ⟨2005793, by rfl⟩ : syracuseStep 2674391 = 4011587) B4011587
theorem B2256599 : Blo 1782092 2256599 := bstep (se 1 (by rfl) ⟨1692449, by rfl⟩ : syracuseStep 2256599 = 3384899) B3384899
theorem B6016733 : Blo 1782092 6016733 := bstep (se 3 (by rfl) ⟨1128137, by rfl⟩ : syracuseStep 6016733 = 2256275) B2256275
theorem B4009715 : Blo 1782092 4009715 := bstep (se 1 (by rfl) ⟨3007286, by rfl⟩ : syracuseStep 4009715 = 6014573) B6014573
theorem B4009751 : Blo 1782092 4009751 := bstep (se 1 (by rfl) ⟨3007313, by rfl⟩ : syracuseStep 4009751 = 6014627) B6014627
theorem B2674457 : Blo 1782092 2674457 := bstep (se 2 (by rfl) ⟨1002921, by rfl⟩ : syracuseStep 2674457 = 2005843) B2005843
theorem B9031499 : Blo 1782092 9031499 := bstep (se 1 (by rfl) ⟨6773624, by rfl⟩ : syracuseStep 9031499 = 13547249) B13547249
theorem B2674571 : Blo 1782092 2674571 := bstep (se 1 (by rfl) ⟨2005928, by rfl⟩ : syracuseStep 2674571 = 4011857) B4011857
theorem B2674583 : Blo 1782092 2674583 := bstep (se 1 (by rfl) ⟨2005937, by rfl⟩ : syracuseStep 2674583 = 4011875) B4011875
theorem B45690803 : Blo 1782092 45690803 := bstep (se 1 (by rfl) ⟨34268102, by rfl⟩ : syracuseStep 45690803 = 68536205) B68536205
theorem B4009931 : Blo 1782092 4009931 := bstep (se 1 (by rfl) ⟨3007448, by rfl⟩ : syracuseStep 4009931 = 6014897) B6014897
theorem B2674649 : Blo 1782092 2674649 := bstep (se 2 (by rfl) ⟨1002993, by rfl⟩ : syracuseStep 2674649 = 2005987) B2005987
theorem B4009985 : Blo 1782092 4009985 := bstep (se 2 (by rfl) ⟨1503744, by rfl⟩ : syracuseStep 4009985 = 3007489) B3007489
theorem B2674763 : Blo 1782092 2674763 := bstep (se 1 (by rfl) ⟨2006072, by rfl⟩ : syracuseStep 2674763 = 4012145) B4012145
theorem B2674775 : Blo 1782092 2674775 := bstep (se 1 (by rfl) ⟨2006081, by rfl⟩ : syracuseStep 2674775 = 4012163) B4012163
theorem B2674841 : Blo 1782092 2674841 := bstep (se 2 (by rfl) ⟨1003065, by rfl⟩ : syracuseStep 2674841 = 2006131) B2006131
theorem B6770861 : Blo 1782092 6770861 := bstep (se 3 (by rfl) ⟨1269536, by rfl⟩ : syracuseStep 6770861 = 2539073) B2539073
theorem B6770891 : Blo 1782092 6770891 := bstep (se 1 (by rfl) ⟨5078168, by rfl⟩ : syracuseStep 6770891 = 10156337) B10156337
theorem B1904843 : Blo 1782092 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B4010201 : Blo 1782092 4010201 := bstep (se 2 (by rfl) ⟨1503825, by rfl⟩ : syracuseStep 4010201 = 3007651) B3007651
theorem B2674955 : Blo 1782092 2674955 := bstep (se 1 (by rfl) ⟨2006216, by rfl⟩ : syracuseStep 2674955 = 4012433) B4012433
theorem B2674967 : Blo 1782092 2674967 := bstep (se 1 (by rfl) ⟨2006225, by rfl⟩ : syracuseStep 2674967 = 4012451) B4012451
theorem B4010291 : Blo 1782092 4010291 := bstep (se 1 (by rfl) ⟨3007718, by rfl⟩ : syracuseStep 4010291 = 6015437) B6015437
theorem B15233345 : Blo 1782092 15233345 := bstep (se 2 (by rfl) ⟨5712504, by rfl⟩ : syracuseStep 15233345 = 11425009) B11425009
theorem B1782103 : Blo 1782092 1782103 := bstep (se 1 (by rfl) ⟨1336577, by rfl⟩ : syracuseStep 1782103 = 2673155) B2673155
theorem B4010327 : Blo 1782092 4010327 := bstep (se 1 (by rfl) ⟨3007745, by rfl⟩ : syracuseStep 4010327 = 6015491) B6015491
theorem B2675033 : Blo 1782092 2675033 := bstep (se 2 (by rfl) ⟨1003137, by rfl⟩ : syracuseStep 2675033 = 2006275) B2006275
theorem B1782123 : Blo 1782092 1782123 := bstep (se 1 (by rfl) ⟨1336592, by rfl⟩ : syracuseStep 1782123 = 2673185) B2673185
theorem B1782135 : Blo 1782092 1782135 := bstep (se 1 (by rfl) ⟨1336601, by rfl⟩ : syracuseStep 1782135 = 2673203) B2673203
theorem B1782155 : Blo 1782092 1782155 := bstep (se 1 (by rfl) ⟨1336616, by rfl⟩ : syracuseStep 1782155 = 2673233) B2673233
theorem B1782167 : Blo 1782092 1782167 := bstep (se 1 (by rfl) ⟨1336625, by rfl⟩ : syracuseStep 1782167 = 2673251) B2673251
theorem B2257303 : Blo 1782092 2257303 := bstep (se 1 (by rfl) ⟨1692977, by rfl⟩ : syracuseStep 2257303 = 3385955) B3385955
theorem B1782187 : Blo 1782092 1782187 := bstep (se 1 (by rfl) ⟨1336640, by rfl⟩ : syracuseStep 1782187 = 2673281) B2673281
theorem B1782199 : Blo 1782092 1782199 := bstep (se 1 (by rfl) ⟨1336649, by rfl⟩ : syracuseStep 1782199 = 2673299) B2673299
theorem B1782219 : Blo 1782092 1782219 := bstep (se 1 (by rfl) ⟨1336664, by rfl⟩ : syracuseStep 1782219 = 2673329) B2673329
theorem B2675147 : Blo 1782092 2675147 := bstep (se 1 (by rfl) ⟨2006360, by rfl⟩ : syracuseStep 2675147 = 4012721) B4012721
theorem B1782231 : Blo 1782092 1782231 := bstep (se 1 (by rfl) ⟨1336673, by rfl⟩ : syracuseStep 1782231 = 2673347) B2673347
theorem B13726169 : Blo 1782092 13726169 := bstep (se 2 (by rfl) ⟨5147313, by rfl⟩ : syracuseStep 13726169 = 10294627) B10294627
theorem B2675159 : Blo 1782092 2675159 := bstep (se 1 (by rfl) ⟨2006369, by rfl⟩ : syracuseStep 2675159 = 4012739) B4012739
theorem B9155033 : Blo 1782092 9155033 := bstep (se 2 (by rfl) ⟨3433137, by rfl⟩ : syracuseStep 9155033 = 6866275) B6866275
theorem B1782251 : Blo 1782092 1782251 := bstep (se 1 (by rfl) ⟨1336688, by rfl⟩ : syracuseStep 1782251 = 2673377) B2673377
theorem B1782263 : Blo 1782092 1782263 := bstep (se 1 (by rfl) ⟨1336697, by rfl⟩ : syracuseStep 1782263 = 2673395) B2673395
theorem B1782283 : Blo 1782092 1782283 := bstep (se 1 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 1782283 = 2673425) B2673425
theorem B4010507 : Blo 1782092 4010507 := bstep (se 1 (by rfl) ⟨3007880, by rfl⟩ : syracuseStep 4010507 = 6015761) B6015761
theorem B1782295 : Blo 1782092 1782295 := bstep (se 1 (by rfl) ⟨1336721, by rfl⟩ : syracuseStep 1782295 = 2673443) B2673443
theorem B2675225 : Blo 1782092 2675225 := bstep (se 2 (by rfl) ⟨1003209, by rfl⟩ : syracuseStep 2675225 = 2006419) B2006419
theorem B1782315 : Blo 1782092 1782315 := bstep (se 1 (by rfl) ⟨1336736, by rfl⟩ : syracuseStep 1782315 = 2673473) B2673473
theorem B1782327 : Blo 1782092 1782327 := bstep (se 1 (by rfl) ⟨1336745, by rfl⟩ : syracuseStep 1782327 = 2673491) B2673491
theorem B4010561 : Blo 1782092 4010561 := bstep (se 2 (by rfl) ⟨1503960, by rfl⟩ : syracuseStep 4010561 = 3007921) B3007921
theorem B1782347 : Blo 1782092 1782347 := bstep (se 1 (by rfl) ⟨1336760, by rfl⟩ : syracuseStep 1782347 = 2673521) B2673521
theorem B5788235 : Blo 1782092 5788235 := bstep (se 1 (by rfl) ⟨4341176, by rfl⟩ : syracuseStep 5788235 = 8682353) B8682353
theorem B1782359 : Blo 1782092 1782359 := bstep (se 1 (by rfl) ⟨1336769, by rfl⟩ : syracuseStep 1782359 = 2673539) B2673539
theorem B1782379 : Blo 1782092 1782379 := bstep (se 1 (by rfl) ⟨1336784, by rfl⟩ : syracuseStep 1782379 = 2673569) B2673569
theorem B1782391 : Blo 1782092 1782391 := bstep (se 1 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 1782391 = 2673587) B2673587
theorem B1782411 : Blo 1782092 1782411 := bstep (se 1 (by rfl) ⟨1336808, by rfl⟩ : syracuseStep 1782411 = 2673617) B2673617
theorem B2675339 : Blo 1782092 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B1782423 : Blo 1782092 1782423 := bstep (se 1 (by rfl) ⟨1336817, by rfl⟩ : syracuseStep 1782423 = 2673635) B2673635
theorem B2675351 : Blo 1782092 2675351 := bstep (se 1 (by rfl) ⟨2006513, by rfl⟩ : syracuseStep 2675351 = 4013027) B4013027
theorem B1782443 : Blo 1782092 1782443 := bstep (se 1 (by rfl) ⟨1336832, by rfl⟩ : syracuseStep 1782443 = 2673665) B2673665
theorem B6861485 : Blo 1782092 6861485 := bstep (se 3 (by rfl) ⟨1286528, by rfl⟩ : syracuseStep 6861485 = 2573057) B2573057
theorem B1782455 : Blo 1782092 1782455 := bstep (se 1 (by rfl) ⟨1336841, by rfl⟩ : syracuseStep 1782455 = 2673683) B2673683
theorem B1782475 : Blo 1782092 1782475 := bstep (se 1 (by rfl) ⟨1336856, by rfl⟩ : syracuseStep 1782475 = 2673713) B2673713
theorem B1782487 : Blo 1782092 1782487 := bstep (se 1 (by rfl) ⟨1336865, by rfl⟩ : syracuseStep 1782487 = 2673731) B2673731
theorem B2675417 : Blo 1782092 2675417 := bstep (se 2 (by rfl) ⟨1003281, by rfl⟩ : syracuseStep 2675417 = 2006563) B2006563
theorem B1782507 : Blo 1782092 1782507 := bstep (se 1 (by rfl) ⟨1336880, by rfl⟩ : syracuseStep 1782507 = 2673761) B2673761
theorem B1782519 : Blo 1782092 1782519 := bstep (se 1 (by rfl) ⟨1336889, by rfl⟩ : syracuseStep 1782519 = 2673779) B2673779
theorem B1782539 : Blo 1782092 1782539 := bstep (se 1 (by rfl) ⟨1336904, by rfl⟩ : syracuseStep 1782539 = 2673809) B2673809
theorem B1782551 : Blo 1782092 1782551 := bstep (se 1 (by rfl) ⟨1336913, by rfl⟩ : syracuseStep 1782551 = 2673827) B2673827
theorem B7615255 : Blo 1782092 7615255 := bstep (se 1 (by rfl) ⟨5711441, by rfl⟩ : syracuseStep 7615255 = 11422883) B11422883
theorem B4010777 : Blo 1782092 4010777 := bstep (se 2 (by rfl) ⟨1504041, by rfl⟩ : syracuseStep 4010777 = 3008083) B3008083
theorem B1782571 : Blo 1782092 1782571 := bstep (se 1 (by rfl) ⟨1336928, by rfl⟩ : syracuseStep 1782571 = 2673857) B2673857
theorem B1782583 : Blo 1782092 1782583 := bstep (se 1 (by rfl) ⟨1336937, by rfl⟩ : syracuseStep 1782583 = 2673875) B2673875
theorem B5075777 : Blo 1782092 5075777 := bstep (se 2 (by rfl) ⟨1903416, by rfl⟩ : syracuseStep 5075777 = 3806833) B3806833
theorem B1782603 : Blo 1782092 1782603 := bstep (se 1 (by rfl) ⟨1336952, by rfl⟩ : syracuseStep 1782603 = 2673905) B2673905
theorem B6017867 : Blo 1782092 6017867 := bstep (se 1 (by rfl) ⟨4513400, by rfl⟩ : syracuseStep 6017867 = 9026801) B9026801
theorem B2675531 : Blo 1782092 2675531 := bstep (se 1 (by rfl) ⟨2006648, by rfl⟩ : syracuseStep 2675531 = 4013297) B4013297
theorem B1782615 : Blo 1782092 1782615 := bstep (se 1 (by rfl) ⟨1336961, by rfl⟩ : syracuseStep 1782615 = 2673923) B2673923
theorem B2675543 : Blo 1782092 2675543 := bstep (se 1 (by rfl) ⟨2006657, by rfl⟩ : syracuseStep 2675543 = 4013315) B4013315
theorem B5419865 : Blo 1782092 5419865 := bstep (se 2 (by rfl) ⟨2032449, by rfl⟩ : syracuseStep 5419865 = 4064899) B4064899
theorem B6771545 : Blo 1782092 6771545 := bstep (se 2 (by rfl) ⟨2539329, by rfl⟩ : syracuseStep 6771545 = 5078659) B5078659
theorem B1782635 : Blo 1782092 1782635 := bstep (se 1 (by rfl) ⟨1336976, by rfl⟩ : syracuseStep 1782635 = 2673953) B2673953
theorem B4010867 : Blo 1782092 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B1782647 : Blo 1782092 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B1782667 : Blo 1782092 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B4010903 : Blo 1782092 4010903 := bstep (se 1 (by rfl) ⟨3008177, by rfl⟩ : syracuseStep 4010903 = 6016355) B6016355
theorem B1782679 : Blo 1782092 1782679 := bstep (se 1 (by rfl) ⟨1337009, by rfl⟩ : syracuseStep 1782679 = 2674019) B2674019
theorem B4576151 : Blo 1782092 4576151 := bstep (se 1 (by rfl) ⟨3432113, by rfl⟩ : syracuseStep 4576151 = 6864227) B6864227
theorem B2675609 : Blo 1782092 2675609 := bstep (se 2 (by rfl) ⟨1003353, by rfl⟩ : syracuseStep 2675609 = 2006707) B2006707
theorem B1782699 : Blo 1782092 1782699 := bstep (se 1 (by rfl) ⟨1337024, by rfl⟩ : syracuseStep 1782699 = 2674049) B2674049
theorem B5075891 : Blo 1782092 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B1782711 : Blo 1782092 1782711 := bstep (se 1 (by rfl) ⟨1337033, by rfl⟩ : syracuseStep 1782711 = 2674067) B2674067
theorem B1782731 : Blo 1782092 1782731 := bstep (se 1 (by rfl) ⟨1337048, by rfl⟩ : syracuseStep 1782731 = 2674097) B2674097
theorem B1782743 : Blo 1782092 1782743 := bstep (se 1 (by rfl) ⟨1337057, by rfl⟩ : syracuseStep 1782743 = 2674115) B2674115
theorem B1782763 : Blo 1782092 1782763 := bstep (se 1 (by rfl) ⟨1337072, by rfl⟩ : syracuseStep 1782763 = 2674145) B2674145
theorem B1782775 : Blo 1782092 1782775 := bstep (se 1 (by rfl) ⟨1337081, by rfl⟩ : syracuseStep 1782775 = 2674163) B2674163
theorem B1782795 : Blo 1782092 1782795 := bstep (se 1 (by rfl) ⟨1337096, by rfl⟩ : syracuseStep 1782795 = 2674193) B2674193
theorem B2675723 : Blo 1782092 2675723 := bstep (se 1 (by rfl) ⟨2006792, by rfl⟩ : syracuseStep 2675723 = 4013585) B4013585
theorem B1782807 : Blo 1782092 1782807 := bstep (se 1 (by rfl) ⟨1337105, by rfl⟩ : syracuseStep 1782807 = 2674211) B2674211
theorem B2675735 : Blo 1782092 2675735 := bstep (se 1 (by rfl) ⟨2006801, by rfl⟩ : syracuseStep 2675735 = 4013603) B4013603
theorem B1782827 : Blo 1782092 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B1782839 : Blo 1782092 1782839 := bstep (se 1 (by rfl) ⟨1337129, by rfl⟩ : syracuseStep 1782839 = 2674259) B2674259
theorem B4822067 : Blo 1782092 4822067 := bstep (se 1 (by rfl) ⟨3616550, by rfl⟩ : syracuseStep 4822067 = 7233101) B7233101
theorem B41759813 : Blo 1782092 41759813 := bstep (se 4 (by rfl) ⟨3914982, by rfl⟩ : syracuseStep 41759813 = 7829965) B7829965
theorem B4011083 : Blo 1782092 4011083 := bstep (se 1 (by rfl) ⟨3008312, by rfl⟩ : syracuseStep 4011083 = 6016625) B6016625
theorem B1782859 : Blo 1782092 1782859 := bstep (se 1 (by rfl) ⟨1337144, by rfl⟩ : syracuseStep 1782859 = 2674289) B2674289
theorem B1782871 : Blo 1782092 1782871 := bstep (se 1 (by rfl) ⟨1337153, by rfl⟩ : syracuseStep 1782871 = 2674307) B2674307
theorem B6018137 : Blo 1782092 6018137 := bstep (se 2 (by rfl) ⟨2256801, by rfl⟩ : syracuseStep 6018137 = 4513603) B4513603
theorem B2675801 : Blo 1782092 2675801 := bstep (se 2 (by rfl) ⟨1003425, by rfl⟩ : syracuseStep 2675801 = 2006851) B2006851
theorem B1782891 : Blo 1782092 1782891 := bstep (se 1 (by rfl) ⟨1337168, by rfl⟩ : syracuseStep 1782891 = 2674337) B2674337
theorem B1782903 : Blo 1782092 1782903 := bstep (se 1 (by rfl) ⟨1337177, by rfl⟩ : syracuseStep 1782903 = 2674355) B2674355
theorem B4011137 : Blo 1782092 4011137 := bstep (se 2 (by rfl) ⟨1504176, by rfl⟩ : syracuseStep 4011137 = 3008353) B3008353
theorem B13718659 : Blo 1782092 13718659 := bstep (se 1 (by rfl) ⟨10288994, by rfl⟩ : syracuseStep 13718659 = 20577989) B20577989
theorem B1782923 : Blo 1782092 1782923 := bstep (se 1 (by rfl) ⟨1337192, by rfl⟩ : syracuseStep 1782923 = 2674385) B2674385
theorem B2200727 : Blo 1782092 2200727 := bstep (se 1 (by rfl) ⟨1650545, by rfl⟩ : syracuseStep 2200727 = 3301091) B3301091
theorem B1782935 : Blo 1782092 1782935 := bstep (se 1 (by rfl) ⟨1337201, by rfl⟩ : syracuseStep 1782935 = 2674403) B2674403
theorem B6771863 : Blo 1782092 6771863 := bstep (se 1 (by rfl) ⟨5078897, by rfl⟩ : syracuseStep 6771863 = 10157795) B10157795
theorem B1782955 : Blo 1782092 1782955 := bstep (se 1 (by rfl) ⟨1337216, by rfl⟩ : syracuseStep 1782955 = 2674433) B2674433
theorem B1782967 : Blo 1782092 1782967 := bstep (se 1 (by rfl) ⟨1337225, by rfl⟩ : syracuseStep 1782967 = 2674451) B2674451
theorem B1782987 : Blo 1782092 1782987 := bstep (se 1 (by rfl) ⟨1337240, by rfl⟩ : syracuseStep 1782987 = 2674481) B2674481
theorem B2675915 : Blo 1782092 2675915 := bstep (se 1 (by rfl) ⟨2006936, by rfl⟩ : syracuseStep 2675915 = 4013873) B4013873
theorem B3806423 : Blo 1782092 3806423 := bstep (se 1 (by rfl) ⟨2854817, by rfl⟩ : syracuseStep 3806423 = 5709635) B5709635
theorem B1782999 : Blo 1782092 1782999 := bstep (se 1 (by rfl) ⟨1337249, by rfl⟩ : syracuseStep 1782999 = 2674499) B2674499
theorem B2675927 : Blo 1782092 2675927 := bstep (se 1 (by rfl) ⟨2006945, by rfl⟩ : syracuseStep 2675927 = 4013891) B4013891
theorem B1783019 : Blo 1782092 1783019 := bstep (se 1 (by rfl) ⟨1337264, by rfl⟩ : syracuseStep 1783019 = 2674529) B2674529
theorem B1783031 : Blo 1782092 1783031 := bstep (se 1 (by rfl) ⟨1337273, by rfl⟩ : syracuseStep 1783031 = 2674547) B2674547
theorem B1783051 : Blo 1782092 1783051 := bstep (se 1 (by rfl) ⟨1337288, by rfl⟩ : syracuseStep 1783051 = 2674577) B2674577
theorem B6862103 : Blo 1782092 6862103 := bstep (se 1 (by rfl) ⟨5146577, by rfl⟩ : syracuseStep 6862103 = 10293155) B10293155
theorem B1783063 : Blo 1782092 1783063 := bstep (se 1 (by rfl) ⟨1337297, by rfl⟩ : syracuseStep 1783063 = 2674595) B2674595
theorem B2675993 : Blo 1782092 2675993 := bstep (se 2 (by rfl) ⟨1003497, by rfl⟩ : syracuseStep 2675993 = 2006995) B2006995
theorem B1783083 : Blo 1782092 1783083 := bstep (se 1 (by rfl) ⟨1337312, by rfl⟩ : syracuseStep 1783083 = 2674625) B2674625
theorem B1783095 : Blo 1782092 1783095 := bstep (se 1 (by rfl) ⟨1337321, by rfl⟩ : syracuseStep 1783095 = 2674643) B2674643
theorem B1783115 : Blo 1782092 1783115 := bstep (se 1 (by rfl) ⟨1337336, by rfl⟩ : syracuseStep 1783115 = 2674673) B2674673
theorem B1783127 : Blo 1782092 1783127 := bstep (se 1 (by rfl) ⟨1337345, by rfl⟩ : syracuseStep 1783127 = 2674691) B2674691
theorem B4011353 : Blo 1782092 4011353 := bstep (se 2 (by rfl) ⟨1504257, by rfl⟩ : syracuseStep 4011353 = 3008515) B3008515
theorem B1783147 : Blo 1782092 1783147 := bstep (se 1 (by rfl) ⟨1337360, by rfl⟩ : syracuseStep 1783147 = 2674721) B2674721
theorem B1783159 : Blo 1782092 1783159 := bstep (se 1 (by rfl) ⟨1337369, by rfl⟩ : syracuseStep 1783159 = 2674739) B2674739
theorem B1783179 : Blo 1782092 1783179 := bstep (se 1 (by rfl) ⟨1337384, by rfl⟩ : syracuseStep 1783179 = 2674769) B2674769
theorem B2676107 : Blo 1782092 2676107 := bstep (se 1 (by rfl) ⟨2007080, by rfl⟩ : syracuseStep 2676107 = 4014161) B4014161
theorem B1783191 : Blo 1782092 1783191 := bstep (se 1 (by rfl) ⟨1337393, by rfl⟩ : syracuseStep 1783191 = 2674787) B2674787
theorem B2676119 : Blo 1782092 2676119 := bstep (se 1 (by rfl) ⟨2007089, by rfl⟩ : syracuseStep 2676119 = 4014179) B4014179
theorem B1783211 : Blo 1782092 1783211 := bstep (se 1 (by rfl) ⟨1337408, by rfl⟩ : syracuseStep 1783211 = 2674817) B2674817
theorem B4011443 : Blo 1782092 4011443 := bstep (se 1 (by rfl) ⟨3008582, by rfl⟩ : syracuseStep 4011443 = 6017165) B6017165
theorem B1783223 : Blo 1782092 1783223 := bstep (se 1 (by rfl) ⟨1337417, by rfl⟩ : syracuseStep 1783223 = 2674835) B2674835
theorem B1783243 : Blo 1782092 1783243 := bstep (se 1 (by rfl) ⟨1337432, by rfl⟩ : syracuseStep 1783243 = 2674865) B2674865
theorem B4011479 : Blo 1782092 4011479 := bstep (se 1 (by rfl) ⟨3008609, by rfl⟩ : syracuseStep 4011479 = 6017219) B6017219
theorem B1783255 : Blo 1782092 1783255 := bstep (se 1 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 1783255 = 2674883) B2674883
theorem B1783275 : Blo 1782092 1783275 := bstep (se 1 (by rfl) ⟨1337456, by rfl⟩ : syracuseStep 1783275 = 2674913) B2674913
theorem B1783287 : Blo 1782092 1783287 := bstep (se 1 (by rfl) ⟨1337465, by rfl⟩ : syracuseStep 1783287 = 2674931) B2674931
theorem B1783307 : Blo 1782092 1783307 := bstep (se 1 (by rfl) ⟨1337480, by rfl⟩ : syracuseStep 1783307 = 2674961) B2674961
theorem B4068875 : Blo 1782092 4068875 := bstep (se 1 (by rfl) ⟨3051656, by rfl⟩ : syracuseStep 4068875 = 6103313) B6103313
theorem B28915217 : Blo 1782092 28915217 := bstep (se 2 (by rfl) ⟨10843206, by rfl⟩ : syracuseStep 28915217 = 21686413) B21686413
theorem B1783319 : Blo 1782092 1783319 := bstep (se 1 (by rfl) ⟨1337489, by rfl⟩ : syracuseStep 1783319 = 2674979) B2674979
theorem B1783339 : Blo 1782092 1783339 := bstep (se 1 (by rfl) ⟨1337504, by rfl⟩ : syracuseStep 1783339 = 2675009) B2675009
theorem B1783351 : Blo 1782092 1783351 := bstep (se 1 (by rfl) ⟨1337513, by rfl⟩ : syracuseStep 1783351 = 2675027) B2675027
theorem B1783371 : Blo 1782092 1783371 := bstep (se 1 (by rfl) ⟨1337528, by rfl⟩ : syracuseStep 1783371 = 2675057) B2675057
theorem B1783383 : Blo 1782092 1783383 := bstep (se 1 (by rfl) ⟨1337537, by rfl⟩ : syracuseStep 1783383 = 2675075) B2675075
theorem B1783403 : Blo 1782092 1783403 := bstep (se 1 (by rfl) ⟨1337552, by rfl⟩ : syracuseStep 1783403 = 2675105) B2675105
theorem B1783415 : Blo 1782092 1783415 := bstep (se 1 (by rfl) ⟨1337561, by rfl⟩ : syracuseStep 1783415 = 2675123) B2675123
theorem B351745667 : Blo 1782092 351745667 := bstep (se 1 (by rfl) ⟨263809250, by rfl⟩ : syracuseStep 351745667 = 527618501) B527618501
theorem B4011659 : Blo 1782092 4011659 := bstep (se 1 (by rfl) ⟨3008744, by rfl⟩ : syracuseStep 4011659 = 6017489) B6017489
theorem B1783435 : Blo 1782092 1783435 := bstep (se 1 (by rfl) ⟨1337576, by rfl⟩ : syracuseStep 1783435 = 2675153) B2675153
theorem B1783447 : Blo 1782092 1783447 := bstep (se 1 (by rfl) ⟨1337585, by rfl⟩ : syracuseStep 1783447 = 2675171) B2675171
theorem B1783467 : Blo 1782092 1783467 := bstep (se 1 (by rfl) ⟨1337600, by rfl⟩ : syracuseStep 1783467 = 2675201) B2675201
theorem B1783479 : Blo 1782092 1783479 := bstep (se 1 (by rfl) ⟨1337609, by rfl⟩ : syracuseStep 1783479 = 2675219) B2675219
theorem B4011713 : Blo 1782092 4011713 := bstep (se 2 (by rfl) ⟨1504392, by rfl⟩ : syracuseStep 4011713 = 3008785) B3008785
theorem B1783499 : Blo 1782092 1783499 := bstep (se 1 (by rfl) ⟨1337624, by rfl⟩ : syracuseStep 1783499 = 2675249) B2675249
theorem B1783511 : Blo 1782092 1783511 := bstep (se 1 (by rfl) ⟨1337633, by rfl⟩ : syracuseStep 1783511 = 2675267) B2675267
theorem B5420765 : Blo 1782092 5420765 := bstep (se 3 (by rfl) ⟨1016393, by rfl⟩ : syracuseStep 5420765 = 2032787) B2032787
theorem B1783531 : Blo 1782092 1783531 := bstep (se 1 (by rfl) ⟨1337648, by rfl⟩ : syracuseStep 1783531 = 2675297) B2675297
theorem B1783543 : Blo 1782092 1783543 := bstep (se 1 (by rfl) ⟨1337657, by rfl⟩ : syracuseStep 1783543 = 2675315) B2675315
theorem B1783563 : Blo 1782092 1783563 := bstep (se 1 (by rfl) ⟨1337672, by rfl⟩ : syracuseStep 1783563 = 2675345) B2675345
theorem B6018839 : Blo 1782092 6018839 := bstep (se 1 (by rfl) ⟨4514129, by rfl⟩ : syracuseStep 6018839 = 9028259) B9028259
theorem B1783575 : Blo 1782092 1783575 := bstep (se 1 (by rfl) ⟨1337681, by rfl⟩ : syracuseStep 1783575 = 2675363) B2675363
theorem B1783595 : Blo 1782092 1783595 := bstep (se 1 (by rfl) ⟨1337696, by rfl⟩ : syracuseStep 1783595 = 2675393) B2675393
theorem B6772531 : Blo 1782092 6772531 := bstep (se 1 (by rfl) ⟨5079398, by rfl⟩ : syracuseStep 6772531 = 10158797) B10158797
theorem B1783607 : Blo 1782092 1783607 := bstep (se 1 (by rfl) ⟨1337705, by rfl⟩ : syracuseStep 1783607 = 2675411) B2675411
theorem B1783627 : Blo 1782092 1783627 := bstep (se 1 (by rfl) ⟨1337720, by rfl⟩ : syracuseStep 1783627 = 2675441) B2675441
theorem B1783639 : Blo 1782092 1783639 := bstep (se 1 (by rfl) ⟨1337729, by rfl⟩ : syracuseStep 1783639 = 2675459) B2675459
theorem B1783659 : Blo 1782092 1783659 := bstep (se 1 (by rfl) ⟨1337744, by rfl⟩ : syracuseStep 1783659 = 2675489) B2675489
theorem B1783671 : Blo 1782092 1783671 := bstep (se 1 (by rfl) ⟨1337753, by rfl⟩ : syracuseStep 1783671 = 2675507) B2675507
theorem B1783691 : Blo 1782092 1783691 := bstep (se 1 (by rfl) ⟨1337768, by rfl⟩ : syracuseStep 1783691 = 2675537) B2675537
theorem B4511639 : Blo 1782092 4511639 := bstep (se 1 (by rfl) ⟨3383729, by rfl⟩ : syracuseStep 4511639 = 6767459) B6767459
theorem B1783703 : Blo 1782092 1783703 := bstep (se 1 (by rfl) ⟨1337777, by rfl⟩ : syracuseStep 1783703 = 2675555) B2675555
theorem B4011929 : Blo 1782092 4011929 := bstep (se 2 (by rfl) ⟨1504473, by rfl⟩ : syracuseStep 4011929 = 3008947) B3008947
theorem B2004907 : Blo 1782092 2004907 := bstep (se 1 (by rfl) ⟨1503680, by rfl⟩ : syracuseStep 2004907 = 3007361) B3007361
theorem B1783723 : Blo 1782092 1783723 := bstep (se 1 (by rfl) ⟨1337792, by rfl⟩ : syracuseStep 1783723 = 2675585) B2675585
theorem B1783735 : Blo 1782092 1783735 := bstep (se 1 (by rfl) ⟨1337801, by rfl⟩ : syracuseStep 1783735 = 2675603) B2675603
theorem B1783755 : Blo 1782092 1783755 := bstep (se 1 (by rfl) ⟨1337816, by rfl⟩ : syracuseStep 1783755 = 2675633) B2675633
theorem B1783767 : Blo 1782092 1783767 := bstep (se 1 (by rfl) ⟨1337825, by rfl⟩ : syracuseStep 1783767 = 2675651) B2675651
theorem B1783787 : Blo 1782092 1783787 := bstep (se 1 (by rfl) ⟨1337840, by rfl⟩ : syracuseStep 1783787 = 2675681) B2675681
theorem B4012019 : Blo 1782092 4012019 := bstep (se 1 (by rfl) ⟨3009014, by rfl⟩ : syracuseStep 4012019 = 6018029) B6018029
theorem B1783799 : Blo 1782092 1783799 := bstep (se 1 (by rfl) ⟨1337849, by rfl⟩ : syracuseStep 1783799 = 2675699) B2675699
theorem B1783819 : Blo 1782092 1783819 := bstep (se 1 (by rfl) ⟨1337864, by rfl⟩ : syracuseStep 1783819 = 2675729) B2675729
theorem B2005015 : Blo 1782092 2005015 := bstep (se 1 (by rfl) ⟨1503761, by rfl⟩ : syracuseStep 2005015 = 3007523) B3007523
theorem B4012055 : Blo 1782092 4012055 := bstep (se 1 (by rfl) ⟨3009041, by rfl⟩ : syracuseStep 4012055 = 6018083) B6018083
theorem B1783831 : Blo 1782092 1783831 := bstep (se 1 (by rfl) ⟨1337873, by rfl⟩ : syracuseStep 1783831 = 2675747) B2675747
theorem B1783851 : Blo 1782092 1783851 := bstep (se 1 (by rfl) ⟨1337888, by rfl⟩ : syracuseStep 1783851 = 2675777) B2675777
theorem B1783863 : Blo 1782092 1783863 := bstep (se 1 (by rfl) ⟨1337897, by rfl⟩ : syracuseStep 1783863 = 2675795) B2675795
theorem B1783883 : Blo 1782092 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B1783895 : Blo 1782092 1783895 := bstep (se 1 (by rfl) ⟨1337921, by rfl⟩ : syracuseStep 1783895 = 2675843) B2675843
theorem B1783915 : Blo 1782092 1783915 := bstep (se 1 (by rfl) ⟨1337936, by rfl⟩ : syracuseStep 1783915 = 2675873) B2675873
theorem B1783927 : Blo 1782092 1783927 := bstep (se 1 (by rfl) ⟨1337945, by rfl⟩ : syracuseStep 1783927 = 2675891) B2675891
theorem B9025667 : Blo 1782092 9025667 := bstep (se 1 (by rfl) ⟨6769250, by rfl⟩ : syracuseStep 9025667 = 13538501) B13538501
theorem B1783947 : Blo 1782092 1783947 := bstep (se 1 (by rfl) ⟨1337960, by rfl⟩ : syracuseStep 1783947 = 2675921) B2675921
theorem B1783959 : Blo 1782092 1783959 := bstep (se 1 (by rfl) ⟨1337969, by rfl⟩ : syracuseStep 1783959 = 2675939) B2675939
theorem B1783979 : Blo 1782092 1783979 := bstep (se 1 (by rfl) ⟨1337984, by rfl⟩ : syracuseStep 1783979 = 2675969) B2675969
theorem B1783991 : Blo 1782092 1783991 := bstep (se 1 (by rfl) ⟨1337993, by rfl⟩ : syracuseStep 1783991 = 2675987) B2675987
theorem B2005195 : Blo 1782092 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B4012235 : Blo 1782092 4012235 := bstep (se 1 (by rfl) ⟨3009176, by rfl⟩ : syracuseStep 4012235 = 6018353) B6018353
theorem B1784011 : Blo 1782092 1784011 := bstep (se 1 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 1784011 = 2676017) B2676017
theorem B1784023 : Blo 1782092 1784023 := bstep (se 1 (by rfl) ⟨1338017, by rfl⟩ : syracuseStep 1784023 = 2676035) B2676035
theorem B1784043 : Blo 1782092 1784043 := bstep (se 1 (by rfl) ⟨1338032, by rfl⟩ : syracuseStep 1784043 = 2676065) B2676065
theorem B1784055 : Blo 1782092 1784055 := bstep (se 1 (by rfl) ⟨1338041, by rfl⟩ : syracuseStep 1784055 = 2676083) B2676083
theorem B4012289 : Blo 1782092 4012289 := bstep (se 2 (by rfl) ⟨1504608, by rfl⟩ : syracuseStep 4012289 = 3009217) B3009217
theorem B3807499 : Blo 1782092 3807499 := bstep (se 1 (by rfl) ⟨2855624, by rfl⟩ : syracuseStep 3807499 = 5711249) B5711249
theorem B1784075 : Blo 1782092 1784075 := bstep (se 1 (by rfl) ⟨1338056, by rfl⟩ : syracuseStep 1784075 = 2676113) B2676113
theorem B1784087 : Blo 1782092 1784087 := bstep (se 1 (by rfl) ⟨1338065, by rfl⟩ : syracuseStep 1784087 = 2676131) B2676131
theorem B6019379 : Blo 1782092 6019379 := bstep (se 1 (by rfl) ⟨4514534, by rfl⟩ : syracuseStep 6019379 = 9029069) B9029069
theorem B2005303 : Blo 1782092 2005303 := bstep (se 1 (by rfl) ⟨1503977, by rfl⟩ : syracuseStep 2005303 = 3007955) B3007955
theorem B2857367 : Blo 1782092 2857367 := bstep (se 1 (by rfl) ⟨2143025, by rfl⟩ : syracuseStep 2857367 = 4286051) B4286051
theorem B8133043 : Blo 1782092 8133043 := bstep (se 1 (by rfl) ⟨6099782, by rfl⟩ : syracuseStep 8133043 = 12199565) B12199565
theorem B4282841 : Blo 1782092 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B4012505 : Blo 1782092 4012505 := bstep (se 2 (by rfl) ⟨1504689, by rfl⟩ : syracuseStep 4012505 = 3009379) B3009379
theorem B2005483 : Blo 1782092 2005483 := bstep (se 1 (by rfl) ⟨1504112, by rfl⟩ : syracuseStep 2005483 = 3008225) B3008225
theorem B10156589 : Blo 1782092 10156589 := bstep (se 3 (by rfl) ⟨1904360, by rfl⟩ : syracuseStep 10156589 = 3808721) B3808721
theorem B4512307 : Blo 1782092 4512307 := bstep (se 1 (by rfl) ⟨3384230, by rfl⟩ : syracuseStep 4512307 = 6768461) B6768461
theorem B4012595 : Blo 1782092 4012595 := bstep (se 1 (by rfl) ⟨3009446, by rfl⟩ : syracuseStep 4012595 = 6018893) B6018893
theorem B6019649 : Blo 1782092 6019649 := bstep (se 2 (by rfl) ⟨2257368, by rfl⟩ : syracuseStep 6019649 = 4514737) B4514737
theorem B2538059 : Blo 1782092 2538059 := bstep (se 1 (by rfl) ⟨1903544, by rfl⟩ : syracuseStep 2538059 = 3807089) B3807089
theorem B2005591 : Blo 1782092 2005591 := bstep (se 1 (by rfl) ⟨1504193, by rfl⟩ : syracuseStep 2005591 = 3008387) B3008387
theorem B4012631 : Blo 1782092 4012631 := bstep (se 1 (by rfl) ⟨3009473, by rfl⟩ : syracuseStep 4012631 = 6018947) B6018947
theorem B15235735 : Blo 1782092 15235735 := bstep (se 1 (by rfl) ⟨11426801, by rfl⟩ : syracuseStep 15235735 = 22853603) B22853603
theorem B4512449 : Blo 1782092 4512449 := bstep (se 2 (by rfl) ⟨1692168, by rfl⟩ : syracuseStep 4512449 = 3384337) B3384337
theorem B2857675 : Blo 1782092 2857675 := bstep (se 1 (by rfl) ⟨2143256, by rfl⟩ : syracuseStep 2857675 = 4286513) B4286513
theorem B22838021 : Blo 1782092 22838021 := bstep (se 4 (by rfl) ⟨2141064, by rfl⟩ : syracuseStep 22838021 = 4282129) B4282129
theorem B2005771 : Blo 1782092 2005771 := bstep (se 1 (by rfl) ⟨1504328, by rfl⟩ : syracuseStep 2005771 = 3008657) B3008657
theorem B4012811 : Blo 1782092 4012811 := bstep (se 1 (by rfl) ⟨3009608, by rfl⟩ : syracuseStep 4012811 = 6019217) B6019217
theorem B4012865 : Blo 1782092 4012865 := bstep (se 2 (by rfl) ⟨1504824, by rfl⟩ : syracuseStep 4012865 = 3009649) B3009649
theorem B3300185 : Blo 1782092 3300185 := bstep (se 2 (by rfl) ⟨1237569, by rfl⟩ : syracuseStep 3300185 = 2475139) B2475139
theorem B2005879 : Blo 1782092 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B55671731 : Blo 1782092 55671731 := bstep (se 1 (by rfl) ⟨41753798, by rfl⟩ : syracuseStep 55671731 = 83507597) B83507597
theorem B66853849 : Blo 1782092 66853849 := bstep (se 2 (by rfl) ⟨25070193, by rfl⟩ : syracuseStep 66853849 = 50140387) B50140387
theorem B3808217 : Blo 1782092 3808217 := bstep (se 2 (by rfl) ⟨1428081, by rfl⟩ : syracuseStep 3808217 = 2856163) B2856163
theorem B6773777 : Blo 1782092 6773777 := bstep (se 2 (by rfl) ⟨2540166, by rfl⟩ : syracuseStep 6773777 = 5080333) B5080333
theorem B4013081 : Blo 1782092 4013081 := bstep (se 2 (by rfl) ⟨1504905, by rfl⟩ : syracuseStep 4013081 = 3009811) B3009811
theorem B2006059 : Blo 1782092 2006059 := bstep (se 1 (by rfl) ⟨1504544, by rfl⟩ : syracuseStep 2006059 = 3009089) B3009089
theorem B13540445 : Blo 1782092 13540445 := bstep (se 3 (by rfl) ⟨2538833, by rfl⟩ : syracuseStep 13540445 = 5077667) B5077667
theorem B6020189 : Blo 1782092 6020189 := bstep (se 3 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 6020189 = 2257571) B2257571
theorem B4013171 : Blo 1782092 4013171 := bstep (se 1 (by rfl) ⟨3009878, by rfl⟩ : syracuseStep 4013171 = 6019757) B6019757
theorem B3431575 : Blo 1782092 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B2006167 : Blo 1782092 2006167 := bstep (se 1 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 2006167 = 3009251) B3009251
theorem B4013207 : Blo 1782092 4013207 := bstep (se 1 (by rfl) ⟨3009905, by rfl⟩ : syracuseStep 4013207 = 6019811) B6019811
theorem B8928407 : Blo 1782092 8928407 := bstep (se 1 (by rfl) ⟨6696305, by rfl⟩ : syracuseStep 8928407 = 13392611) B13392611
theorem B5790937 : Blo 1782092 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B2006347 : Blo 1782092 2006347 := bstep (se 1 (by rfl) ⟨1504760, by rfl⟩ : syracuseStep 2006347 = 3009521) B3009521
theorem B4013387 : Blo 1782092 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B4013441 : Blo 1782092 4013441 := bstep (se 2 (by rfl) ⟨1505040, by rfl⟩ : syracuseStep 4013441 = 3010081) B3010081
theorem B2006455 : Blo 1782092 2006455 := bstep (se 1 (by rfl) ⟨1504841, by rfl⟩ : syracuseStep 2006455 = 3009683) B3009683
theorem B3808729 : Blo 1782092 3808729 := bstep (se 2 (by rfl) ⟨1428273, by rfl⟩ : syracuseStep 3808729 = 2856547) B2856547
theorem B12205613 : Blo 1782092 12205613 := bstep (se 3 (by rfl) ⟨2288552, by rfl⟩ : syracuseStep 12205613 = 4577105) B4577105
theorem B22855243 : Blo 1782092 22855243 := bstep (se 1 (by rfl) ⟨17141432, by rfl⟩ : syracuseStep 22855243 = 34282865) B34282865
theorem B4013657 : Blo 1782092 4013657 := bstep (se 2 (by rfl) ⟨1505121, by rfl⟩ : syracuseStep 4013657 = 3010243) B3010243
theorem B7618141 : Blo 1782092 7618141 := bstep (se 3 (by rfl) ⟨1428401, by rfl⟩ : syracuseStep 7618141 = 2856803) B2856803
theorem B2006635 : Blo 1782092 2006635 := bstep (se 1 (by rfl) ⟨1504976, by rfl⟩ : syracuseStep 2006635 = 3009953) B3009953
theorem B3808883 : Blo 1782092 3808883 := bstep (se 1 (by rfl) ⟨2856662, by rfl⟩ : syracuseStep 3808883 = 5713325) B5713325
theorem B8240791 : Blo 1782092 8240791 := bstep (se 1 (by rfl) ⟨6180593, by rfl⟩ : syracuseStep 8240791 = 12361187) B12361187
theorem B4013747 : Blo 1782092 4013747 := bstep (se 1 (by rfl) ⟨3010310, by rfl⟩ : syracuseStep 4013747 = 6020621) B6020621
theorem B2006743 : Blo 1782092 2006743 := bstep (se 1 (by rfl) ⟨1505057, by rfl⟩ : syracuseStep 2006743 = 3010115) B3010115
theorem B4013783 : Blo 1782092 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B5078807 : Blo 1782092 5078807 := bstep (se 1 (by rfl) ⟨3809105, by rfl⟩ : syracuseStep 5078807 = 7618211) B7618211
theorem B2006923 : Blo 1782092 2006923 := bstep (se 1 (by rfl) ⟨1505192, by rfl⟩ : syracuseStep 2006923 = 3010385) B3010385
theorem B4013963 : Blo 1782092 4013963 := bstep (se 1 (by rfl) ⟨3010472, by rfl⟩ : syracuseStep 4013963 = 6020945) B6020945
theorem B6766487 : Blo 1782092 6766487 := bstep (se 1 (by rfl) ⟨5074865, by rfl⟩ : syracuseStep 6766487 = 10149731) B10149731
theorem B4513715 : Blo 1782092 4513715 := bstep (se 1 (by rfl) ⟨3385286, by rfl⟩ : syracuseStep 4513715 = 6770573) B6770573
theorem B5496769 : Blo 1782092 5496769 := bstep (se 2 (by rfl) ⟨2061288, by rfl⟩ : syracuseStep 5496769 = 4122577) B4122577
theorem B4014017 : Blo 1782092 4014017 := bstep (se 2 (by rfl) ⟨1505256, by rfl⟩ : syracuseStep 4014017 = 3010513) B3010513
theorem B2711513 : Blo 1782092 2711513 := bstep (se 2 (by rfl) ⟨1016817, by rfl⟩ : syracuseStep 2711513 = 2033635) B2033635
theorem B2007031 : Blo 1782092 2007031 := bstep (se 1 (by rfl) ⟨1505273, by rfl⟩ : syracuseStep 2007031 = 3010547) B3010547
theorem B9404419 : Blo 1782092 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B18808919 : Blo 1782092 18808919 := bstep (se 1 (by rfl) ⟨14106689, by rfl⟩ : syracuseStep 18808919 = 28213379) B28213379
theorem B4513907 : Blo 1782092 4513907 := bstep (se 1 (by rfl) ⟨3385430, by rfl⟩ : syracuseStep 4513907 = 6770861) B6770861
theorem B4513927 : Blo 1782092 4513927 := bstep (se 1 (by rfl) ⟨3385445, by rfl⟩ : syracuseStep 4513927 = 6770891) B6770891
theorem B9150779 : Blo 1782092 9150779 := bstep (se 1 (by rfl) ⟨6863084, by rfl⟩ : syracuseStep 9150779 = 13726169) B13726169
theorem B6103355 : Blo 1782092 6103355 := bstep (se 1 (by rfl) ⟨4577516, by rfl⟩ : syracuseStep 6103355 = 9155033) B9155033
theorem B17138051 : Blo 1782092 17138051 := bstep (se 1 (by rfl) ⟨12853538, by rfl⟩ : syracuseStep 17138051 = 25707077) B25707077
theorem B3211655 : Blo 1782092 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B3858823 : Blo 1782092 3858823 := bstep (se 1 (by rfl) ⟨2894117, by rfl⟩ : syracuseStep 3858823 = 5788235) B5788235
theorem B4514201 : Blo 1782092 4514201 := bstep (se 2 (by rfl) ⟨1692825, by rfl⟩ : syracuseStep 4514201 = 3385651) B3385651
theorem B5079581 : Blo 1782092 5079581 := bstep (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) B1904843
theorem B3383851 : Blo 1782092 3383851 := bstep (se 1 (by rfl) ⟨2537888, by rfl⟩ : syracuseStep 3383851 = 5075777) B5075777
theorem B3613243 : Blo 1782092 3613243 := bstep (se 1 (by rfl) ⟨2709932, by rfl⟩ : syracuseStep 3613243 = 5419865) B5419865
theorem B4514363 : Blo 1782092 4514363 := bstep (se 1 (by rfl) ⟨3385772, by rfl⟩ : syracuseStep 4514363 = 6771545) B6771545
theorem B6767171 : Blo 1782092 6767171 := bstep (se 1 (by rfl) ⟨5075378, by rfl⟩ : syracuseStep 6767171 = 10150757) B10150757
theorem B3383927 : Blo 1782092 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B5079809 : Blo 1782092 5079809 := bstep (se 2 (by rfl) ⟨1904928, by rfl⟩ : syracuseStep 5079809 = 3809857) B3809857
theorem B4514575 : Blo 1782092 4514575 := bstep (se 1 (by rfl) ⟨3385931, by rfl⟩ : syracuseStep 4514575 = 6771863) B6771863
theorem B18301733 : Blo 1782092 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B9634619 : Blo 1782092 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B3810233 : Blo 1782092 3810233 := bstep (se 2 (by rfl) ⟨1428837, by rfl⟩ : syracuseStep 3810233 = 2857675) B2857675
theorem B2712583 : Blo 1782092 2712583 := bstep (se 1 (by rfl) ⟨2034437, by rfl⟩ : syracuseStep 2712583 = 4068875) B4068875
theorem B19276811 : Blo 1782092 19276811 := bstep (se 1 (by rfl) ⟨14457608, by rfl⟩ : syracuseStep 19276811 = 28915217) B28915217
theorem B16483351 : Blo 1782092 16483351 := bstep (se 1 (by rfl) ⟨12362513, by rfl⟩ : syracuseStep 16483351 = 24725027) B24725027
theorem B4514849 : Blo 1782092 4514849 := bstep (se 2 (by rfl) ⟨1693068, by rfl⟩ : syracuseStep 4514849 = 3386137) B3386137
theorem B20317229 : Blo 1782092 20317229 := bstep (se 3 (by rfl) ⟨3809480, by rfl⟩ : syracuseStep 20317229 = 7618961) B7618961
theorem B7619645 : Blo 1782092 7619645 := bstep (se 3 (by rfl) ⟨1428683, by rfl⟩ : syracuseStep 7619645 = 2857367) B2857367
theorem B234497111 : Blo 1782092 234497111 := bstep (se 1 (by rfl) ⟨175872833, by rfl⟩ : syracuseStep 234497111 = 351745667) B351745667
theorem B5080151 : Blo 1782092 5080151 := bstep (se 1 (by rfl) ⟨3810113, by rfl⟩ : syracuseStep 5080151 = 7620227) B7620227
theorem B3613843 : Blo 1782092 3613843 := bstep (se 1 (by rfl) ⟨2710382, by rfl⟩ : syracuseStep 3613843 = 5420765) B5420765
theorem B5080265 : Blo 1782092 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B11420909 : Blo 1782092 11420909 := bstep (se 3 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 11420909 = 4282841) B4282841
theorem B3007759 : Blo 1782092 3007759 := bstep (se 1 (by rfl) ⟨2255819, by rfl⟩ : syracuseStep 3007759 = 4511639) B4511639
theorem B89138465 : Blo 1782092 89138465 := bstep (se 2 (by rfl) ⟨33426924, by rfl⟩ : syracuseStep 89138465 = 66853849) B66853849
theorem B20301191 : Blo 1782092 20301191 := bstep (se 1 (by rfl) ⟨15225893, by rfl⟩ : syracuseStep 20301191 = 30451787) B30451787
theorem B10159505 : Blo 1782092 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B7619987 : Blo 1782092 7619987 := bstep (se 1 (by rfl) ⟨5714990, by rfl⟩ : syracuseStep 7619987 = 11429981) B11429981
theorem B32548301 : Blo 1782092 32548301 := bstep (se 3 (by rfl) ⟨6102806, by rfl⟩ : syracuseStep 32548301 = 12205613) B12205613
theorem B6768157 : Blo 1782092 6768157 := bstep (se 3 (by rfl) ⟨1269029, by rfl⟩ : syracuseStep 6768157 = 2538059) B2538059
theorem B6014735 : Blo 1782092 6014735 := bstep (se 1 (by rfl) ⟨4511051, by rfl⟩ : syracuseStep 6014735 = 9022103) B9022103
theorem B3008299 : Blo 1782092 3008299 := bstep (se 1 (by rfl) ⟨2256224, by rfl⟩ : syracuseStep 3008299 = 4512449) B4512449
theorem B5867417 : Blo 1782092 5867417 := bstep (se 2 (by rfl) ⟨2200281, by rfl⟩ : syracuseStep 5867417 = 4400563) B4400563
theorem B3008441 : Blo 1782092 3008441 := bstep (se 2 (by rfl) ⟨1128165, by rfl⟩ : syracuseStep 3008441 = 2256331) B2256331
theorem B4515851 : Blo 1782092 4515851 := bstep (se 1 (by rfl) ⟨3386888, by rfl⟩ : syracuseStep 4515851 = 6773777) B6773777
theorem B6015005 : Blo 1782092 6015005 := bstep (se 3 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 6015005 = 2255627) B2255627
theorem B10987721 : Blo 1782092 10987721 := bstep (se 2 (by rfl) ⟨4120395, by rfl⟩ : syracuseStep 10987721 = 8240791) B8240791
theorem B9030041 : Blo 1782092 9030041 := bstep (se 2 (by rfl) ⟨3386265, by rfl⟩ : syracuseStep 9030041 = 6772531) B6772531
theorem B4819385 : Blo 1782092 4819385 := bstep (se 2 (by rfl) ⟨1807269, by rfl⟩ : syracuseStep 4819385 = 3614539) B3614539
theorem B2673143 : Blo 1782092 2673143 := bstep (se 1 (by rfl) ⟨2004857, by rfl⟩ : syracuseStep 2673143 = 4009715) B4009715
theorem B2673167 : Blo 1782092 2673167 := bstep (se 1 (by rfl) ⟨2004875, by rfl⟩ : syracuseStep 2673167 = 4009751) B4009751
theorem B3385871 : Blo 1782092 3385871 := bstep (se 1 (by rfl) ⟨2539403, by rfl⟩ : syracuseStep 3385871 = 5078807) B5078807
theorem B2673209 : Blo 1782092 2673209 := bstep (se 2 (by rfl) ⟨1002453, by rfl⟩ : syracuseStep 2673209 = 2004907) B2004907
theorem B30460535 : Blo 1782092 30460535 := bstep (se 1 (by rfl) ⟨22845401, by rfl⟩ : syracuseStep 30460535 = 45690803) B45690803
theorem B3009143 : Blo 1782092 3009143 := bstep (se 1 (by rfl) ⟨2256857, by rfl⟩ : syracuseStep 3009143 = 4513715) B4513715
theorem B2673287 : Blo 1782092 2673287 := bstep (se 1 (by rfl) ⟨2004965, by rfl⟩ : syracuseStep 2673287 = 4009931) B4009931
theorem B2673323 : Blo 1782092 2673323 := bstep (se 1 (by rfl) ⟨2004992, by rfl⟩ : syracuseStep 2673323 = 4009985) B4009985
theorem B2673353 : Blo 1782092 2673353 := bstep (se 2 (by rfl) ⟨1002507, by rfl⟩ : syracuseStep 2673353 = 2005015) B2005015
theorem B2673467 : Blo 1782092 2673467 := bstep (se 1 (by rfl) ⟨2005100, by rfl⟩ : syracuseStep 2673467 = 4010201) B4010201
theorem B2673527 : Blo 1782092 2673527 := bstep (se 1 (by rfl) ⟨2005145, by rfl⟩ : syracuseStep 2673527 = 4010291) B4010291
theorem B2673551 : Blo 1782092 2673551 := bstep (se 1 (by rfl) ⟨2005163, by rfl⟩ : syracuseStep 2673551 = 4010327) B4010327
theorem B2673593 : Blo 1782092 2673593 := bstep (se 2 (by rfl) ⟨1002597, by rfl⟩ : syracuseStep 2673593 = 2005195) B2005195
theorem B2673671 : Blo 1782092 2673671 := bstep (se 1 (by rfl) ⟨2005253, by rfl⟩ : syracuseStep 2673671 = 4010507) B4010507
theorem B2673707 : Blo 1782092 2673707 := bstep (se 1 (by rfl) ⟨2005280, by rfl⟩ : syracuseStep 2673707 = 4010561) B4010561
theorem B3009595 : Blo 1782092 3009595 := bstep (se 1 (by rfl) ⟨2257196, by rfl⟩ : syracuseStep 3009595 = 4514393) B4514393
theorem B5868605 : Blo 1782092 5868605 := bstep (se 3 (by rfl) ⟨1100363, by rfl⟩ : syracuseStep 5868605 = 2200727) B2200727
theorem B65080381 : Blo 1782092 65080381 := bstep (se 3 (by rfl) ⟨12202571, by rfl⟩ : syracuseStep 65080381 = 24405143) B24405143
theorem B2673737 : Blo 1782092 2673737 := bstep (se 2 (by rfl) ⟨1002651, by rfl⟩ : syracuseStep 2673737 = 2005303) B2005303
theorem B4574323 : Blo 1782092 4574323 := bstep (se 1 (by rfl) ⟨3430742, by rfl⟩ : syracuseStep 4574323 = 6861485) B6861485
theorem B2256007 : Blo 1782092 2256007 := bstep (se 1 (by rfl) ⟨1692005, by rfl⟩ : syracuseStep 2256007 = 3384011) B3384011
theorem B2673851 : Blo 1782092 2673851 := bstep (se 1 (by rfl) ⟨2005388, by rfl⟩ : syracuseStep 2673851 = 4010777) B4010777
theorem B3009737 : Blo 1782092 3009737 := bstep (se 2 (by rfl) ⟨1128651, by rfl⟩ : syracuseStep 3009737 = 2257303) B2257303
theorem B2673911 : Blo 1782092 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B2673935 : Blo 1782092 2673935 := bstep (se 1 (by rfl) ⟨2005451, by rfl⟩ : syracuseStep 2673935 = 4010903) B4010903
theorem B3050767 : Blo 1782092 3050767 := bstep (se 1 (by rfl) ⟨2288075, by rfl⟩ : syracuseStep 3050767 = 4576151) B4576151
theorem B2141483 : Blo 1782092 2141483 := bstep (se 1 (by rfl) ⟨1606112, by rfl⟩ : syracuseStep 2141483 = 3212225) B3212225
theorem B2673977 : Blo 1782092 2673977 := bstep (se 2 (by rfl) ⟨1002741, by rfl⟩ : syracuseStep 2673977 = 2005483) B2005483
theorem B3214711 : Blo 1782092 3214711 := bstep (se 1 (by rfl) ⟨2411033, by rfl⟩ : syracuseStep 3214711 = 4822067) B4822067
theorem B27839875 : Blo 1782092 27839875 := bstep (se 1 (by rfl) ⟨20879906, by rfl⟩ : syracuseStep 27839875 = 41759813) B41759813
theorem B2674055 : Blo 1782092 2674055 := bstep (se 1 (by rfl) ⟨2005541, by rfl⟩ : syracuseStep 2674055 = 4011083) B4011083
theorem B6016409 : Blo 1782092 6016409 := bstep (se 2 (by rfl) ⟨2256153, by rfl⟩ : syracuseStep 6016409 = 4512307) B4512307
theorem B2674091 : Blo 1782092 2674091 := bstep (se 1 (by rfl) ⟨2005568, by rfl⟩ : syracuseStep 2674091 = 4011137) B4011137
theorem B2674121 : Blo 1782092 2674121 := bstep (se 2 (by rfl) ⟨1002795, by rfl⟩ : syracuseStep 2674121 = 2005591) B2005591
theorem B4574735 : Blo 1782092 4574735 := bstep (se 1 (by rfl) ⟨3431051, by rfl⟩ : syracuseStep 4574735 = 6862103) B6862103
theorem B2256427 : Blo 1782092 2256427 := bstep (se 1 (by rfl) ⟨1692320, by rfl⟩ : syracuseStep 2256427 = 3384641) B3384641
theorem B2674235 : Blo 1782092 2674235 := bstep (se 1 (by rfl) ⟨2005676, by rfl⟩ : syracuseStep 2674235 = 4011353) B4011353
theorem B2141815 : Blo 1782092 2141815 := bstep (se 1 (by rfl) ⟨1606361, by rfl⟩ : syracuseStep 2141815 = 3212723) B3212723
theorem B2674295 : Blo 1782092 2674295 := bstep (se 1 (by rfl) ⟨2005721, by rfl⟩ : syracuseStep 2674295 = 4011443) B4011443
theorem B2674319 : Blo 1782092 2674319 := bstep (se 1 (by rfl) ⟨2005739, by rfl⟩ : syracuseStep 2674319 = 4011479) B4011479
theorem B2674361 : Blo 1782092 2674361 := bstep (se 2 (by rfl) ⟨1002885, by rfl⟩ : syracuseStep 2674361 = 2005771) B2005771
theorem B10153673 : Blo 1782092 10153673 := bstep (se 2 (by rfl) ⟨3807627, by rfl⟩ : syracuseStep 10153673 = 7615255) B7615255
theorem B2141959 : Blo 1782092 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B2674439 : Blo 1782092 2674439 := bstep (se 1 (by rfl) ⟨2005829, by rfl⟩ : syracuseStep 2674439 = 4011659) B4011659
theorem B2256655 : Blo 1782092 2256655 := bstep (se 1 (by rfl) ⟨1692491, by rfl⟩ : syracuseStep 2256655 = 3384983) B3384983
theorem B2674475 : Blo 1782092 2674475 := bstep (se 1 (by rfl) ⟨2005856, by rfl⟩ : syracuseStep 2674475 = 4011713) B4011713
theorem B4009787 : Blo 1782092 4009787 := bstep (se 1 (by rfl) ⟨3007340, by rfl⟩ : syracuseStep 4009787 = 6014681) B6014681
theorem B2674505 : Blo 1782092 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B13545305 : Blo 1782092 13545305 := bstep (se 2 (by rfl) ⟨5079489, by rfl⟩ : syracuseStep 13545305 = 10158979) B10158979
theorem B3010439 : Blo 1782092 3010439 := bstep (se 1 (by rfl) ⟨2257829, by rfl⟩ : syracuseStep 3010439 = 4515659) B4515659
theorem B4009913 : Blo 1782092 4009913 := bstep (se 2 (by rfl) ⟨1503717, by rfl⟩ : syracuseStep 4009913 = 3007435) B3007435
theorem B2674619 : Blo 1782092 2674619 := bstep (se 1 (by rfl) ⟨2005964, by rfl⟩ : syracuseStep 2674619 = 4011929) B4011929
theorem B12857291 : Blo 1782092 12857291 := bstep (se 1 (by rfl) ⟨9642968, by rfl⟩ : syracuseStep 12857291 = 19285937) B19285937
theorem B2674679 : Blo 1782092 2674679 := bstep (se 1 (by rfl) ⟨2006009, by rfl⟩ : syracuseStep 2674679 = 4012019) B4012019
theorem B2674703 : Blo 1782092 2674703 := bstep (se 1 (by rfl) ⟨2006027, by rfl⟩ : syracuseStep 2674703 = 4012055) B4012055
theorem B2674745 : Blo 1782092 2674745 := bstep (se 2 (by rfl) ⟨1003029, by rfl⟩ : syracuseStep 2674745 = 2006059) B2006059
theorem B6017111 : Blo 1782092 6017111 := bstep (se 1 (by rfl) ⟨4512833, by rfl⟩ : syracuseStep 6017111 = 9025667) B9025667
theorem B2674823 : Blo 1782092 2674823 := bstep (se 1 (by rfl) ⟨2006117, by rfl⟩ : syracuseStep 2674823 = 4012235) B4012235
theorem B2674859 : Blo 1782092 2674859 := bstep (se 1 (by rfl) ⟨2006144, by rfl⟩ : syracuseStep 2674859 = 4012289) B4012289
theorem B2674889 : Blo 1782092 2674889 := bstep (se 2 (by rfl) ⟨1003083, by rfl⟩ : syracuseStep 2674889 = 2006167) B2006167
theorem B4010255 : Blo 1782092 4010255 := bstep (se 1 (by rfl) ⟨3007691, by rfl⟩ : syracuseStep 4010255 = 6015383) B6015383
theorem B4010273 : Blo 1782092 4010273 := bstep (se 2 (by rfl) ⟨1503852, by rfl⟩ : syracuseStep 4010273 = 3007705) B3007705
theorem B9146657 : Blo 1782092 9146657 := bstep (se 2 (by rfl) ⟨3429996, by rfl⟩ : syracuseStep 9146657 = 6859993) B6859993
theorem B7721249 : Blo 1782092 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B2650411 : Blo 1782092 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B6861115 : Blo 1782092 6861115 := bstep (se 1 (by rfl) ⟨5145836, by rfl⟩ : syracuseStep 6861115 = 10291673) B10291673
theorem B2675003 : Blo 1782092 2675003 := bstep (se 1 (by rfl) ⟨2006252, by rfl⟩ : syracuseStep 2675003 = 4012505) B4012505
theorem B6771059 : Blo 1782092 6771059 := bstep (se 1 (by rfl) ⟨5078294, by rfl⟩ : syracuseStep 6771059 = 10156589) B10156589
theorem B2675063 : Blo 1782092 2675063 := bstep (se 1 (by rfl) ⟨2006297, by rfl⟩ : syracuseStep 2675063 = 4012595) B4012595
theorem B1782151 : Blo 1782092 1782151 := bstep (se 1 (by rfl) ⟨1336613, by rfl⟩ : syracuseStep 1782151 = 2673227) B2673227
theorem B1782159 : Blo 1782092 1782159 := bstep (se 1 (by rfl) ⟨1336619, by rfl⟩ : syracuseStep 1782159 = 2673239) B2673239
theorem B2675087 : Blo 1782092 2675087 := bstep (se 1 (by rfl) ⟨2006315, by rfl⟩ : syracuseStep 2675087 = 4012631) B4012631
theorem B2675129 : Blo 1782092 2675129 := bstep (se 2 (by rfl) ⟨1003173, by rfl⟩ : syracuseStep 2675129 = 2006347) B2006347
theorem B1782203 : Blo 1782092 1782203 := bstep (se 1 (by rfl) ⟨1336652, by rfl⟩ : syracuseStep 1782203 = 2673305) B2673305
theorem B12849617 : Blo 1782092 12849617 := bstep (se 2 (by rfl) ⟨4818606, by rfl⟩ : syracuseStep 12849617 = 9637213) B9637213
theorem B2257399 : Blo 1782092 2257399 := bstep (se 1 (by rfl) ⟨1693049, by rfl⟩ : syracuseStep 2257399 = 3386099) B3386099
theorem B15225347 : Blo 1782092 15225347 := bstep (se 1 (by rfl) ⟨11419010, by rfl⟩ : syracuseStep 15225347 = 22838021) B22838021
theorem B1782279 : Blo 1782092 1782279 := bstep (se 1 (by rfl) ⟨1336709, by rfl⟩ : syracuseStep 1782279 = 2673419) B2673419
theorem B2675207 : Blo 1782092 2675207 := bstep (se 1 (by rfl) ⟨2006405, by rfl⟩ : syracuseStep 2675207 = 4012811) B4012811
theorem B1782287 : Blo 1782092 1782287 := bstep (se 1 (by rfl) ⟨1336715, by rfl⟩ : syracuseStep 1782287 = 2673431) B2673431
theorem B2675243 : Blo 1782092 2675243 := bstep (se 1 (by rfl) ⟨2006432, by rfl⟩ : syracuseStep 2675243 = 4012865) B4012865
theorem B1782331 : Blo 1782092 1782331 := bstep (se 1 (by rfl) ⟨1336748, by rfl⟩ : syracuseStep 1782331 = 2673497) B2673497
theorem B2200123 : Blo 1782092 2200123 := bstep (se 1 (by rfl) ⟨1650092, by rfl⟩ : syracuseStep 2200123 = 3300185) B3300185
theorem B6017597 : Blo 1782092 6017597 := bstep (se 3 (by rfl) ⟨1128299, by rfl⟩ : syracuseStep 6017597 = 2256599) B2256599
theorem B2675273 : Blo 1782092 2675273 := bstep (se 2 (by rfl) ⟨1003227, by rfl⟩ : syracuseStep 2675273 = 2006455) B2006455
theorem B8565335 : Blo 1782092 8565335 := bstep (se 1 (by rfl) ⟨6424001, by rfl⟩ : syracuseStep 8565335 = 12848003) B12848003
theorem B4010615 : Blo 1782092 4010615 := bstep (se 1 (by rfl) ⟨3007961, by rfl⟩ : syracuseStep 4010615 = 6015923) B6015923
theorem B37114487 : Blo 1782092 37114487 := bstep (se 1 (by rfl) ⟨27835865, by rfl⟩ : syracuseStep 37114487 = 55671731) B55671731
theorem B1782407 : Blo 1782092 1782407 := bstep (se 1 (by rfl) ⟨1336805, by rfl⟩ : syracuseStep 1782407 = 2673611) B2673611
theorem B1782415 : Blo 1782092 1782415 := bstep (se 1 (by rfl) ⟨1336811, by rfl⟩ : syracuseStep 1782415 = 2673623) B2673623
theorem B1782459 : Blo 1782092 1782459 := bstep (se 1 (by rfl) ⟨1336844, by rfl⟩ : syracuseStep 1782459 = 2673689) B2673689
theorem B2675387 : Blo 1782092 2675387 := bstep (se 1 (by rfl) ⟨2006540, by rfl⟩ : syracuseStep 2675387 = 4013081) B4013081
theorem B2675447 : Blo 1782092 2675447 := bstep (se 1 (by rfl) ⟨2006585, by rfl⟩ : syracuseStep 2675447 = 4013171) B4013171
theorem B1782535 : Blo 1782092 1782535 := bstep (se 1 (by rfl) ⟨1336901, by rfl⟩ : syracuseStep 1782535 = 2673803) B2673803
theorem B2142983 : Blo 1782092 2142983 := bstep (se 1 (by rfl) ⟨1607237, by rfl⟩ : syracuseStep 2142983 = 3214475) B3214475
theorem B1782543 : Blo 1782092 1782543 := bstep (se 1 (by rfl) ⟨1336907, by rfl⟩ : syracuseStep 1782543 = 2673815) B2673815
theorem B2675471 : Blo 1782092 2675471 := bstep (se 1 (by rfl) ⟨2006603, by rfl⟩ : syracuseStep 2675471 = 4013207) B4013207
theorem B5952271 : Blo 1782092 5952271 := bstep (se 1 (by rfl) ⟨4464203, by rfl⟩ : syracuseStep 5952271 = 8928407) B8928407
theorem B13546277 : Blo 1782092 13546277 := bstep (se 4 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 13546277 = 2539927) B2539927
theorem B4010795 : Blo 1782092 4010795 := bstep (se 1 (by rfl) ⟨3008096, by rfl⟩ : syracuseStep 4010795 = 6016193) B6016193
theorem B2675513 : Blo 1782092 2675513 := bstep (se 2 (by rfl) ⟨1003317, by rfl⟩ : syracuseStep 2675513 = 2006635) B2006635
theorem B1782587 : Blo 1782092 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B2257723 : Blo 1782092 2257723 := bstep (se 1 (by rfl) ⟨1693292, by rfl⟩ : syracuseStep 2257723 = 3386585) B3386585
theorem B9024371 : Blo 1782092 9024371 := bstep (se 1 (by rfl) ⟨6768278, by rfl⟩ : syracuseStep 9024371 = 13536557) B13536557
theorem B1782663 : Blo 1782092 1782663 := bstep (se 1 (by rfl) ⟨1336997, by rfl⟩ : syracuseStep 1782663 = 2673995) B2673995
theorem B2675591 : Blo 1782092 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B1782671 : Blo 1782092 1782671 := bstep (se 1 (by rfl) ⟨1337003, by rfl⟩ : syracuseStep 1782671 = 2674007) B2674007
theorem B2675627 : Blo 1782092 2675627 := bstep (se 1 (by rfl) ⟨2006720, by rfl⟩ : syracuseStep 2675627 = 4013441) B4013441
theorem B1782715 : Blo 1782092 1782715 := bstep (se 1 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 1782715 = 2674073) B2674073
theorem B2675657 : Blo 1782092 2675657 := bstep (se 2 (by rfl) ⟨1003371, by rfl⟩ : syracuseStep 2675657 = 2006743) B2006743
theorem B1782791 : Blo 1782092 1782791 := bstep (se 1 (by rfl) ⟨1337093, by rfl⟩ : syracuseStep 1782791 = 2674187) B2674187
theorem B5420047 : Blo 1782092 5420047 := bstep (se 1 (by rfl) ⟨4065035, by rfl⟩ : syracuseStep 5420047 = 8130071) B8130071
theorem B1782799 : Blo 1782092 1782799 := bstep (se 1 (by rfl) ⟨1337099, by rfl⟩ : syracuseStep 1782799 = 2674199) B2674199
theorem B1782843 : Blo 1782092 1782843 := bstep (se 1 (by rfl) ⟨1337132, by rfl⟩ : syracuseStep 1782843 = 2674265) B2674265
theorem B2675771 : Blo 1782092 2675771 := bstep (se 1 (by rfl) ⟨2006828, by rfl⟩ : syracuseStep 2675771 = 4013657) B4013657
theorem B2675831 : Blo 1782092 2675831 := bstep (se 1 (by rfl) ⟨2006873, by rfl⟩ : syracuseStep 2675831 = 4013747) B4013747
theorem B1782919 : Blo 1782092 1782919 := bstep (se 1 (by rfl) ⟨1337189, by rfl⟩ : syracuseStep 1782919 = 2674379) B2674379
theorem B1782927 : Blo 1782092 1782927 := bstep (se 1 (by rfl) ⟨1337195, by rfl⟩ : syracuseStep 1782927 = 2674391) B2674391
theorem B2675855 : Blo 1782092 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B4011155 : Blo 1782092 4011155 := bstep (se 1 (by rfl) ⟨3008366, by rfl⟩ : syracuseStep 4011155 = 6016733) B6016733
theorem B2675897 : Blo 1782092 2675897 := bstep (se 2 (by rfl) ⟨1003461, by rfl⟩ : syracuseStep 2675897 = 2006923) B2006923
theorem B1782971 : Blo 1782092 1782971 := bstep (se 1 (by rfl) ⟨1337228, by rfl⟩ : syracuseStep 1782971 = 2674457) B2674457
theorem B4011209 : Blo 1782092 4011209 := bstep (se 2 (by rfl) ⟨1504203, by rfl⟩ : syracuseStep 4011209 = 3008407) B3008407
theorem B7230701 : Blo 1782092 7230701 := bstep (se 3 (by rfl) ⟨1355756, by rfl⟩ : syracuseStep 7230701 = 2711513) B2711513
theorem B7329025 : Blo 1782092 7329025 := bstep (se 2 (by rfl) ⟨2748384, by rfl⟩ : syracuseStep 7329025 = 5496769) B5496769
theorem B1783047 : Blo 1782092 1783047 := bstep (se 1 (by rfl) ⟨1337285, by rfl⟩ : syracuseStep 1783047 = 2674571) B2674571
theorem B2675975 : Blo 1782092 2675975 := bstep (se 1 (by rfl) ⟨2006981, by rfl⟩ : syracuseStep 2675975 = 4013963) B4013963
theorem B4510991 : Blo 1782092 4510991 := bstep (se 1 (by rfl) ⟨3383243, by rfl⟩ : syracuseStep 4510991 = 6766487) B6766487
theorem B1783055 : Blo 1782092 1783055 := bstep (se 1 (by rfl) ⟨1337291, by rfl⟩ : syracuseStep 1783055 = 2674583) B2674583
theorem B2676011 : Blo 1782092 2676011 := bstep (se 1 (by rfl) ⟨2007008, by rfl⟩ : syracuseStep 2676011 = 4014017) B4014017
theorem B1783099 : Blo 1782092 1783099 := bstep (se 1 (by rfl) ⟨1337324, by rfl⟩ : syracuseStep 1783099 = 2674649) B2674649
theorem B2676041 : Blo 1782092 2676041 := bstep (se 2 (by rfl) ⟨1003515, by rfl⟩ : syracuseStep 2676041 = 2007031) B2007031
theorem B9024857 : Blo 1782092 9024857 := bstep (se 2 (by rfl) ⟨3384321, by rfl⟩ : syracuseStep 9024857 = 6768643) B6768643
theorem B1783175 : Blo 1782092 1783175 := bstep (se 1 (by rfl) ⟨1337381, by rfl⟩ : syracuseStep 1783175 = 2674763) B2674763
theorem B1783183 : Blo 1782092 1783183 := bstep (se 1 (by rfl) ⟨1337387, by rfl⟩ : syracuseStep 1783183 = 2674775) B2674775
theorem B4511123 : Blo 1782092 4511123 := bstep (se 1 (by rfl) ⟨3383342, by rfl⟩ : syracuseStep 4511123 = 6766685) B6766685
theorem B1783227 : Blo 1782092 1783227 := bstep (se 1 (by rfl) ⟨1337420, by rfl⟩ : syracuseStep 1783227 = 2674841) B2674841
theorem B1783303 : Blo 1782092 1783303 := bstep (se 1 (by rfl) ⟨1337477, by rfl⟩ : syracuseStep 1783303 = 2674955) B2674955
theorem B1783311 : Blo 1782092 1783311 := bstep (se 1 (by rfl) ⟨1337483, by rfl⟩ : syracuseStep 1783311 = 2674967) B2674967
theorem B10155563 : Blo 1782092 10155563 := bstep (se 1 (by rfl) ⟨7616672, by rfl⟩ : syracuseStep 10155563 = 15233345) B15233345
theorem B1783355 : Blo 1782092 1783355 := bstep (se 1 (by rfl) ⟨1337516, by rfl⟩ : syracuseStep 1783355 = 2675033) B2675033
theorem B1783431 : Blo 1782092 1783431 := bstep (se 1 (by rfl) ⟨1337573, by rfl⟩ : syracuseStep 1783431 = 2675147) B2675147
theorem B1783439 : Blo 1782092 1783439 := bstep (se 1 (by rfl) ⟨1337579, by rfl⟩ : syracuseStep 1783439 = 2675159) B2675159
theorem B5076665 : Blo 1782092 5076665 := bstep (se 2 (by rfl) ⟨1903749, by rfl⟩ : syracuseStep 5076665 = 3807499) B3807499
theorem B1783483 : Blo 1782092 1783483 := bstep (se 1 (by rfl) ⟨1337612, by rfl⟩ : syracuseStep 1783483 = 2675225) B2675225
theorem B1783559 : Blo 1782092 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B1783567 : Blo 1782092 1783567 := bstep (se 1 (by rfl) ⟨1337675, by rfl⟩ : syracuseStep 1783567 = 2675351) B2675351
theorem B1783611 : Blo 1782092 1783611 := bstep (se 1 (by rfl) ⟨1337708, by rfl⟩ : syracuseStep 1783611 = 2675417) B2675417
theorem B5420861 : Blo 1782092 5420861 := bstep (se 3 (by rfl) ⟨1016411, by rfl⟩ : syracuseStep 5420861 = 2032823) B2032823
theorem B2004871 : Blo 1782092 2004871 := bstep (se 1 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 2004871 = 3007307) B3007307
theorem B4011911 : Blo 1782092 4011911 := bstep (se 1 (by rfl) ⟨3008933, by rfl⟩ : syracuseStep 4011911 = 6017867) B6017867
theorem B1783687 : Blo 1782092 1783687 := bstep (se 1 (by rfl) ⟨1337765, by rfl⟩ : syracuseStep 1783687 = 2675531) B2675531
theorem B1783695 : Blo 1782092 1783695 := bstep (se 1 (by rfl) ⟨1337771, by rfl⟩ : syracuseStep 1783695 = 2675543) B2675543
theorem B10844057 : Blo 1782092 10844057 := bstep (se 2 (by rfl) ⟨4066521, by rfl⟩ : syracuseStep 10844057 = 8133043) B8133043
theorem B6019001 : Blo 1782092 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B1783739 : Blo 1782092 1783739 := bstep (se 1 (by rfl) ⟨1337804, by rfl⟩ : syracuseStep 1783739 = 2675609) B2675609
theorem B1783815 : Blo 1782092 1783815 := bstep (se 1 (by rfl) ⟨1337861, by rfl⟩ : syracuseStep 1783815 = 2675723) B2675723
theorem B1783823 : Blo 1782092 1783823 := bstep (se 1 (by rfl) ⟨1337867, by rfl⟩ : syracuseStep 1783823 = 2675735) B2675735
theorem B2005051 : Blo 1782092 2005051 := bstep (se 1 (by rfl) ⟨1503788, by rfl⟩ : syracuseStep 2005051 = 3007577) B3007577
theorem B4012091 : Blo 1782092 4012091 := bstep (se 1 (by rfl) ⟨3009068, by rfl⟩ : syracuseStep 4012091 = 6018137) B6018137
theorem B1783867 : Blo 1782092 1783867 := bstep (se 1 (by rfl) ⟨1337900, by rfl⟩ : syracuseStep 1783867 = 2675801) B2675801
theorem B1783943 : Blo 1782092 1783943 := bstep (se 1 (by rfl) ⟨1337957, by rfl⟩ : syracuseStep 1783943 = 2675915) B2675915
theorem B2537615 : Blo 1782092 2537615 := bstep (se 1 (by rfl) ⟨1903211, by rfl⟩ : syracuseStep 2537615 = 3806423) B3806423
theorem B1783951 : Blo 1782092 1783951 := bstep (se 1 (by rfl) ⟨1337963, by rfl⟩ : syracuseStep 1783951 = 2675927) B2675927
theorem B4282553 : Blo 1782092 4282553 := bstep (se 2 (by rfl) ⟨1605957, by rfl⟩ : syracuseStep 4282553 = 3211915) B3211915
theorem B4012217 : Blo 1782092 4012217 := bstep (se 2 (by rfl) ⟨1504581, by rfl⟩ : syracuseStep 4012217 = 3009163) B3009163
theorem B1783995 : Blo 1782092 1783995 := bstep (se 1 (by rfl) ⟨1337996, by rfl⟩ : syracuseStep 1783995 = 2675993) B2675993
theorem B20314313 : Blo 1782092 20314313 := bstep (se 2 (by rfl) ⟨7617867, by rfl⟩ : syracuseStep 20314313 = 15235735) B15235735
theorem B1784071 : Blo 1782092 1784071 := bstep (se 1 (by rfl) ⟨1338053, by rfl⟩ : syracuseStep 1784071 = 2676107) B2676107
theorem B1784079 : Blo 1782092 1784079 := bstep (se 1 (by rfl) ⟨1338059, by rfl⟩ : syracuseStep 1784079 = 2676119) B2676119
theorem B4512257 : Blo 1782092 4512257 := bstep (se 2 (by rfl) ⟨1692096, by rfl⟩ : syracuseStep 4512257 = 3384193) B3384193
theorem B6019595 : Blo 1782092 6019595 := bstep (se 1 (by rfl) ⟨4514696, by rfl⟩ : syracuseStep 6019595 = 9029393) B9029393
theorem B2005519 : Blo 1782092 2005519 := bstep (se 1 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 2005519 = 3008279) B3008279
theorem B4012559 : Blo 1782092 4012559 := bstep (se 1 (by rfl) ⟨3009419, by rfl⟩ : syracuseStep 4012559 = 6018839) B6018839
theorem B4012577 : Blo 1782092 4012577 := bstep (se 2 (by rfl) ⟨1504716, by rfl⟩ : syracuseStep 4012577 = 3009433) B3009433
theorem B6773291 : Blo 1782092 6773291 := bstep (se 1 (by rfl) ⟨5079968, by rfl⟩ : syracuseStep 6773291 = 10159937) B10159937
theorem B13539959 : Blo 1782092 13539959 := bstep (se 1 (by rfl) ⟨10154969, by rfl⟩ : syracuseStep 13539959 = 20309939) B20309939
theorem B6019703 : Blo 1782092 6019703 := bstep (se 1 (by rfl) ⟨4514777, by rfl⟩ : syracuseStep 6019703 = 9029555) B9029555
theorem B2857771 : Blo 1782092 2857771 := bstep (se 1 (by rfl) ⟨2143328, by rfl⟩ : syracuseStep 2857771 = 4286657) B4286657
theorem B18291545 : Blo 1782092 18291545 := bstep (se 2 (by rfl) ⟨6859329, by rfl⟩ : syracuseStep 18291545 = 13718659) B13718659
theorem B8567641 : Blo 1782092 8567641 := bstep (se 2 (by rfl) ⟨3212865, by rfl⟩ : syracuseStep 8567641 = 6425731) B6425731
theorem B4512631 : Blo 1782092 4512631 := bstep (se 1 (by rfl) ⟨3384473, by rfl⟩ : syracuseStep 4512631 = 6768947) B6768947
theorem B4012919 : Blo 1782092 4012919 := bstep (se 1 (by rfl) ⟨3009689, by rfl⟩ : syracuseStep 4012919 = 6019379) B6019379
theorem B3431315 : Blo 1782092 3431315 := bstep (se 1 (by rfl) ⟨2573486, by rfl⟩ : syracuseStep 3431315 = 5146973) B5146973
theorem B10157021 : Blo 1782092 10157021 := bstep (se 3 (by rfl) ⟨1904441, by rfl⟩ : syracuseStep 10157021 = 3808883) B3808883
theorem B2006023 : Blo 1782092 2006023 := bstep (se 1 (by rfl) ⟨1504517, by rfl⟩ : syracuseStep 2006023 = 3009035) B3009035
theorem B4013099 : Blo 1782092 4013099 := bstep (se 1 (by rfl) ⟨3009824, by rfl⟩ : syracuseStep 4013099 = 6019649) B6019649
theorem B2006203 : Blo 1782092 2006203 := bstep (se 1 (by rfl) ⟨1504652, by rfl⟩ : syracuseStep 2006203 = 3009305) B3009305
theorem B2538697 : Blo 1782092 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B6020297 : Blo 1782092 6020297 := bstep (se 2 (by rfl) ⟨2257611, by rfl⟩ : syracuseStep 6020297 = 4515223) B4515223
theorem B5078305 : Blo 1782092 5078305 := bstep (se 2 (by rfl) ⟨1904364, by rfl⟩ : syracuseStep 5078305 = 3808729) B3808729
theorem B4513067 : Blo 1782092 4513067 := bstep (se 1 (by rfl) ⟨3384800, by rfl⟩ : syracuseStep 4513067 = 6769601) B6769601
theorem B2538811 : Blo 1782092 2538811 := bstep (se 1 (by rfl) ⟨1904108, by rfl⟩ : syracuseStep 2538811 = 3808217) B3808217
theorem B4283783 : Blo 1782092 4283783 := bstep (se 1 (by rfl) ⟨3212837, by rfl⟩ : syracuseStep 4283783 = 6425675) B6425675
theorem B9026963 : Blo 1782092 9026963 := bstep (se 1 (by rfl) ⟨6770222, by rfl⟩ : syracuseStep 9026963 = 13540445) B13540445
theorem B4013459 : Blo 1782092 4013459 := bstep (se 1 (by rfl) ⟨3010094, by rfl⟩ : syracuseStep 4013459 = 6020189) B6020189
theorem B30473657 : Blo 1782092 30473657 := bstep (se 2 (by rfl) ⟨11427621, by rfl⟩ : syracuseStep 30473657 = 22855243) B22855243
theorem B4013513 : Blo 1782092 4013513 := bstep (se 2 (by rfl) ⟨1505067, by rfl⟩ : syracuseStep 4013513 = 3010135) B3010135
theorem B10157521 : Blo 1782092 10157521 := bstep (se 2 (by rfl) ⟨3809070, by rfl⟩ : syracuseStep 10157521 = 7618141) B7618141
theorem B13540931 : Blo 1782092 13540931 := bstep (se 1 (by rfl) ⟨10155698, by rfl⟩ : syracuseStep 13540931 = 20311397) B20311397
theorem B2006671 : Blo 1782092 2006671 := bstep (se 1 (by rfl) ⟨1505003, by rfl⟩ : syracuseStep 2006671 = 3010007) B3010007
theorem B6020999 : Blo 1782092 6020999 := bstep (se 1 (by rfl) ⟨4515749, by rfl⟩ : syracuseStep 6020999 = 9031499) B9031499
theorem B4514039 : Blo 1782092 4514039 := bstep (se 1 (by rfl) ⟨3385529, by rfl⟩ : syracuseStep 4514039 = 6771059) B6771059
theorem B10150231 : Blo 1782092 10150231 := bstep (se 1 (by rfl) ⟨7612673, by rfl⟩ : syracuseStep 10150231 = 15225347) B15225347
theorem B6766973 : Blo 1782092 6766973 := bstep (se 3 (by rfl) ⟨1268807, by rfl⟩ : syracuseStep 6766973 = 2537615) B2537615
theorem B5710223 : Blo 1782092 5710223 := bstep (se 1 (by rfl) ⟨4282667, by rfl⟩ : syracuseStep 5710223 = 8565335) B8565335
theorem B6423079 : Blo 1782092 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B24396389 : Blo 1782092 24396389 := bstep (se 4 (by rfl) ⟨2287161, by rfl⟩ : syracuseStep 24396389 = 4574323) B4574323
theorem B2540155 : Blo 1782092 2540155 := bstep (se 1 (by rfl) ⟨1905116, by rfl⟩ : syracuseStep 2540155 = 3810233) B3810233
theorem B5079763 : Blo 1782092 5079763 := bstep (se 1 (by rfl) ⟨3809822, by rfl⟩ : syracuseStep 5079763 = 7619645) B7619645
theorem B4817657 : Blo 1782092 4817657 := bstep (se 2 (by rfl) ⟨1806621, by rfl⟩ : syracuseStep 4817657 = 3613243) B3613243
theorem B2933497 : Blo 1782092 2933497 := bstep (se 2 (by rfl) ⟨1100061, by rfl⟩ : syracuseStep 2933497 = 2200123) B2200123
theorem B3007327 : Blo 1782092 3007327 := bstep (se 1 (by rfl) ⟨2255495, by rfl⟩ : syracuseStep 3007327 = 4510991) B4510991
theorem B59425643 : Blo 1782092 59425643 := bstep (se 1 (by rfl) ⟨44569232, by rfl⟩ : syracuseStep 59425643 = 89138465) B89138465
theorem B13534127 : Blo 1782092 13534127 := bstep (se 1 (by rfl) ⟨10150595, by rfl⟩ : syracuseStep 13534127 = 20301191) B20301191
theorem B3007415 : Blo 1782092 3007415 := bstep (se 1 (by rfl) ⟨2255561, by rfl⟩ : syracuseStep 3007415 = 4511123) B4511123
theorem B5079991 : Blo 1782092 5079991 := bstep (se 1 (by rfl) ⟨3809993, by rfl⟩ : syracuseStep 5079991 = 7619987) B7619987
theorem B3384443 : Blo 1782092 3384443 := bstep (se 1 (by rfl) ⟨2538332, by rfl⟩ : syracuseStep 3384443 = 5076665) B5076665
theorem B3613907 : Blo 1782092 3613907 := bstep (se 1 (by rfl) ⟨2710430, by rfl⟩ : syracuseStep 3613907 = 5420861) B5420861
theorem B7226729 : Blo 1782092 7226729 := bstep (se 2 (by rfl) ⟨2710023, by rfl⟩ : syracuseStep 7226729 = 5420047) B5420047
theorem B16270757 : Blo 1782092 16270757 := bstep (se 4 (by rfl) ⟨1525383, by rfl⟩ : syracuseStep 16270757 = 3050767) B3050767
theorem B7325147 : Blo 1782092 7325147 := bstep (se 1 (by rfl) ⟨5493860, by rfl⟩ : syracuseStep 7325147 = 10987721) B10987721
theorem B13542875 : Blo 1782092 13542875 := bstep (se 1 (by rfl) ⟨10157156, by rfl⟩ : syracuseStep 13542875 = 20314313) B20314313
theorem B3008009 : Blo 1782092 3008009 := bstep (se 2 (by rfl) ⟨1128003, by rfl⟩ : syracuseStep 3008009 = 2256007) B2256007
theorem B4818457 : Blo 1782092 4818457 := bstep (se 2 (by rfl) ⟨1806921, by rfl⟩ : syracuseStep 4818457 = 3613843) B3613843
theorem B3384929 : Blo 1782092 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B3008171 : Blo 1782092 3008171 := bstep (se 1 (by rfl) ⟨2256128, by rfl⟩ : syracuseStep 3008171 = 4512257) B4512257
theorem B4515527 : Blo 1782092 4515527 := bstep (se 1 (by rfl) ⟨3386645, by rfl⟩ : syracuseStep 4515527 = 6773291) B6773291
theorem B3385081 : Blo 1782092 3385081 := bstep (se 2 (by rfl) ⟨1269405, by rfl⟩ : syracuseStep 3385081 = 2538811) B2538811
theorem B4286281 : Blo 1782092 4286281 := bstep (se 2 (by rfl) ⟨1607355, by rfl⟩ : syracuseStep 4286281 = 3214711) B3214711
theorem B37119833 : Blo 1782092 37119833 := bstep (se 2 (by rfl) ⟨13919937, by rfl⟩ : syracuseStep 37119833 = 27839875) B27839875
theorem B2287543 : Blo 1782092 2287543 := bstep (se 1 (by rfl) ⟨1715657, by rfl⟩ : syracuseStep 2287543 = 3431315) B3431315
theorem B13543361 : Blo 1782092 13543361 := bstep (se 2 (by rfl) ⟨5078760, by rfl⟩ : syracuseStep 13543361 = 10157521) B10157521
theorem B20580389 : Blo 1782092 20580389 := bstep (se 4 (by rfl) ⟨1929411, by rfl⟩ : syracuseStep 20580389 = 3858823) B3858823
theorem B3008569 : Blo 1782092 3008569 := bstep (se 2 (by rfl) ⟨1128213, by rfl⟩ : syracuseStep 3008569 = 2256427) B2256427
theorem B3008711 : Blo 1782092 3008711 := bstep (se 1 (by rfl) ⟨2256533, by rfl⟩ : syracuseStep 3008711 = 4513067) B4513067
theorem B3049823 : Blo 1782092 3049823 := bstep (se 1 (by rfl) ⟨2287367, by rfl⟩ : syracuseStep 3049823 = 4574735) B4574735
theorem B3008873 : Blo 1782092 3008873 := bstep (se 2 (by rfl) ⟨1128327, by rfl⟩ : syracuseStep 3008873 = 2256655) B2256655
theorem B6769115 : Blo 1782092 6769115 := bstep (se 1 (by rfl) ⟨5076836, by rfl⟩ : syracuseStep 6769115 = 10153673) B10153673
theorem B2673161 : Blo 1782092 2673161 := bstep (se 2 (by rfl) ⟨1002435, by rfl⟩ : syracuseStep 2673161 = 2004871) B2004871
theorem B2673191 : Blo 1782092 2673191 := bstep (se 1 (by rfl) ⟨2004893, by rfl⟩ : syracuseStep 2673191 = 4009787) B4009787
theorem B9030203 : Blo 1782092 9030203 := bstep (se 1 (by rfl) ⟨6772652, by rfl⟩ : syracuseStep 9030203 = 13545305) B13545305
theorem B2673275 : Blo 1782092 2673275 := bstep (se 1 (by rfl) ⟨2004956, by rfl⟩ : syracuseStep 2673275 = 4009913) B4009913
theorem B8571527 : Blo 1782092 8571527 := bstep (se 1 (by rfl) ⟨6428645, by rfl⟩ : syracuseStep 8571527 = 12857291) B12857291
theorem B3009271 : Blo 1782092 3009271 := bstep (se 1 (by rfl) ⟨2256953, by rfl⟩ : syracuseStep 3009271 = 4513907) B4513907
theorem B2673401 : Blo 1782092 2673401 := bstep (se 2 (by rfl) ⟨1002525, by rfl⟩ : syracuseStep 2673401 = 2005051) B2005051
theorem B2673503 : Blo 1782092 2673503 := bstep (se 1 (by rfl) ⟨2005127, by rfl⟩ : syracuseStep 2673503 = 4010255) B4010255
theorem B2673515 : Blo 1782092 2673515 := bstep (se 1 (by rfl) ⟨2005136, by rfl⟩ : syracuseStep 2673515 = 4010273) B4010273
theorem B6097771 : Blo 1782092 6097771 := bstep (se 1 (by rfl) ⟨4573328, by rfl⟩ : syracuseStep 6097771 = 9146657) B9146657
theorem B3009467 : Blo 1782092 3009467 := bstep (se 1 (by rfl) ⟨2257100, by rfl⟩ : syracuseStep 3009467 = 4514201) B4514201
theorem B3386387 : Blo 1782092 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B3009575 : Blo 1782092 3009575 := bstep (se 1 (by rfl) ⟨2257181, by rfl⟩ : syracuseStep 3009575 = 4514363) B4514363
theorem B3533881 : Blo 1782092 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B2255951 : Blo 1782092 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B2673743 : Blo 1782092 2673743 := bstep (se 1 (by rfl) ⟨2005307, by rfl⟩ : syracuseStep 2673743 = 4010615) B4010615
theorem B24742991 : Blo 1782092 24742991 := bstep (se 1 (by rfl) ⟨18557243, by rfl⟩ : syracuseStep 24742991 = 37114487) B37114487
theorem B22842485 : Blo 1782092 22842485 := bstep (se 5 (by rfl) ⟨1070741, by rfl⟩ : syracuseStep 22842485 = 2141483) B2141483
theorem B3386539 : Blo 1782092 3386539 := bstep (se 1 (by rfl) ⟨2539904, by rfl⟩ : syracuseStep 3386539 = 5079809) B5079809
theorem B12201155 : Blo 1782092 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B9030851 : Blo 1782092 9030851 := bstep (se 1 (by rfl) ⟨6773138, by rfl⟩ : syracuseStep 9030851 = 13546277) B13546277
theorem B2673863 : Blo 1782092 2673863 := bstep (se 1 (by rfl) ⟨2005397, by rfl⟩ : syracuseStep 2673863 = 4010795) B4010795
theorem B6016247 : Blo 1782092 6016247 := bstep (se 1 (by rfl) ⟨4512185, by rfl⟩ : syracuseStep 6016247 = 9024371) B9024371
theorem B3009865 : Blo 1782092 3009865 := bstep (se 2 (by rfl) ⟨1128699, by rfl⟩ : syracuseStep 3009865 = 2257399) B2257399
theorem B2674025 : Blo 1782092 2674025 := bstep (se 2 (by rfl) ⟨1002759, by rfl⟩ : syracuseStep 2674025 = 2005519) B2005519
theorem B3009899 : Blo 1782092 3009899 := bstep (se 1 (by rfl) ⟨2257424, by rfl⟩ : syracuseStep 3009899 = 4514849) B4514849
theorem B13544819 : Blo 1782092 13544819 := bstep (se 1 (by rfl) ⟨10158614, by rfl⟩ : syracuseStep 13544819 = 20317229) B20317229
theorem B3386767 : Blo 1782092 3386767 := bstep (se 1 (by rfl) ⟨2540075, by rfl⟩ : syracuseStep 3386767 = 5080151) B5080151
theorem B20589997 : Blo 1782092 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B2674103 : Blo 1782092 2674103 := bstep (se 1 (by rfl) ⟨2005577, by rfl⟩ : syracuseStep 2674103 = 4011155) B4011155
theorem B2674139 : Blo 1782092 2674139 := bstep (se 1 (by rfl) ⟨2005604, by rfl⟩ : syracuseStep 2674139 = 4011209) B4011209
theorem B3386843 : Blo 1782092 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B7613939 : Blo 1782092 7613939 := bstep (se 1 (by rfl) ⟨5710454, by rfl⟩ : syracuseStep 7613939 = 11420909) B11420909
theorem B4820467 : Blo 1782092 4820467 := bstep (se 1 (by rfl) ⟨3615350, by rfl⟩ : syracuseStep 4820467 = 7230701) B7230701
theorem B6016571 : Blo 1782092 6016571 := bstep (se 1 (by rfl) ⟨4512428, by rfl⟩ : syracuseStep 6016571 = 9024857) B9024857
theorem B8564413 : Blo 1782092 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B6770375 : Blo 1782092 6770375 := bstep (se 1 (by rfl) ⟨5077781, by rfl⟩ : syracuseStep 6770375 = 10155563) B10155563
theorem B3010297 : Blo 1782092 3010297 := bstep (se 2 (by rfl) ⟨1128861, by rfl⟩ : syracuseStep 3010297 = 2257723) B2257723
theorem B11423521 : Blo 1782092 11423521 := bstep (se 2 (by rfl) ⟨4283820, by rfl⟩ : syracuseStep 11423521 = 8567641) B8567641
theorem B6016841 : Blo 1782092 6016841 := bstep (se 2 (by rfl) ⟨2256315, by rfl⟩ : syracuseStep 6016841 = 4512631) B4512631
theorem B4009823 : Blo 1782092 4009823 := bstep (se 1 (by rfl) ⟨3007367, by rfl⟩ : syracuseStep 4009823 = 6014735) B6014735
theorem B2674607 : Blo 1782092 2674607 := bstep (se 1 (by rfl) ⟨2005955, by rfl⟩ : syracuseStep 2674607 = 4011911) B4011911
theorem B39088133 : Blo 1782092 39088133 := bstep (se 4 (by rfl) ⟨3664512, by rfl⟩ : syracuseStep 39088133 = 7329025) B7329025
theorem B3010567 : Blo 1782092 3010567 := bstep (se 1 (by rfl) ⟨2257925, by rfl⟩ : syracuseStep 3010567 = 4515851) B4515851
theorem B2674697 : Blo 1782092 2674697 := bstep (se 2 (by rfl) ⟨1003011, by rfl⟩ : syracuseStep 2674697 = 2006023) B2006023
theorem B3616777 : Blo 1782092 3616777 := bstep (se 2 (by rfl) ⟨1356291, by rfl⟩ : syracuseStep 3616777 = 2712583) B2712583
theorem B4010003 : Blo 1782092 4010003 := bstep (se 1 (by rfl) ⟨3007502, by rfl⟩ : syracuseStep 4010003 = 6015005) B6015005
theorem B2674727 : Blo 1782092 2674727 := bstep (se 1 (by rfl) ⟨2006045, by rfl⟩ : syracuseStep 2674727 = 4012091) B4012091
theorem B86773841 : Blo 1782092 86773841 := bstep (se 2 (by rfl) ⟨32540190, by rfl⟩ : syracuseStep 86773841 = 65080381) B65080381
theorem B2855035 : Blo 1782092 2855035 := bstep (se 1 (by rfl) ⟨2141276, by rfl⟩ : syracuseStep 2855035 = 4282553) B4282553
theorem B2674811 : Blo 1782092 2674811 := bstep (se 1 (by rfl) ⟨2006108, by rfl⟩ : syracuseStep 2674811 = 4012217) B4012217
theorem B15241445 : Blo 1782092 15241445 := bstep (se 4 (by rfl) ⟨1428885, by rfl⟩ : syracuseStep 15241445 = 2857771) B2857771
theorem B2674937 : Blo 1782092 2674937 := bstep (se 2 (by rfl) ⟨1003101, by rfl⟩ : syracuseStep 2674937 = 2006203) B2006203
theorem B1782095 : Blo 1782092 1782095 := bstep (se 1 (by rfl) ⟨1336571, by rfl⟩ : syracuseStep 1782095 = 2673143) B2673143
theorem B1782111 : Blo 1782092 1782111 := bstep (se 1 (by rfl) ⟨1336583, by rfl⟩ : syracuseStep 1782111 = 2673167) B2673167
theorem B2675039 : Blo 1782092 2675039 := bstep (se 1 (by rfl) ⟨2006279, by rfl⟩ : syracuseStep 2675039 = 4012559) B4012559
theorem B2257247 : Blo 1782092 2257247 := bstep (se 1 (by rfl) ⟨1692935, by rfl⟩ : syracuseStep 2257247 = 3385871) B3385871
theorem B4010345 : Blo 1782092 4010345 := bstep (se 2 (by rfl) ⟨1503879, by rfl⟩ : syracuseStep 4010345 = 3007759) B3007759
theorem B2675051 : Blo 1782092 2675051 := bstep (se 1 (by rfl) ⟨2006288, by rfl⟩ : syracuseStep 2675051 = 4012577) B4012577
theorem B1782139 : Blo 1782092 1782139 := bstep (se 1 (by rfl) ⟨1336604, by rfl⟩ : syracuseStep 1782139 = 2673209) B2673209
theorem B6771073 : Blo 1782092 6771073 := bstep (se 2 (by rfl) ⟨2539152, by rfl⟩ : syracuseStep 6771073 = 5078305) B5078305
theorem B1782191 : Blo 1782092 1782191 := bstep (se 1 (by rfl) ⟨1336643, by rfl⟩ : syracuseStep 1782191 = 2673287) B2673287
theorem B1782215 : Blo 1782092 1782215 := bstep (se 1 (by rfl) ⟨1336661, by rfl⟩ : syracuseStep 1782215 = 2673323) B2673323
theorem B1782235 : Blo 1782092 1782235 := bstep (se 1 (by rfl) ⟨1336676, by rfl⟩ : syracuseStep 1782235 = 2673353) B2673353
theorem B1782311 : Blo 1782092 1782311 := bstep (se 1 (by rfl) ⟨1336733, by rfl⟩ : syracuseStep 1782311 = 2673467) B2673467
theorem B12194363 : Blo 1782092 12194363 := bstep (se 1 (by rfl) ⟨9145772, by rfl⟩ : syracuseStep 12194363 = 18291545) B18291545
theorem B1782351 : Blo 1782092 1782351 := bstep (se 1 (by rfl) ⟨1336763, by rfl⟩ : syracuseStep 1782351 = 2673527) B2673527
theorem B2675279 : Blo 1782092 2675279 := bstep (se 1 (by rfl) ⟨2006459, by rfl⟩ : syracuseStep 2675279 = 4012919) B4012919
theorem B1782367 : Blo 1782092 1782367 := bstep (se 1 (by rfl) ⟨1336775, by rfl⟩ : syracuseStep 1782367 = 2673551) B2673551
theorem B1782395 : Blo 1782092 1782395 := bstep (se 1 (by rfl) ⟨1336796, by rfl⟩ : syracuseStep 1782395 = 2673593) B2673593
theorem B6771347 : Blo 1782092 6771347 := bstep (se 1 (by rfl) ⟨5078510, by rfl⟩ : syracuseStep 6771347 = 10157021) B10157021
theorem B1782447 : Blo 1782092 1782447 := bstep (se 1 (by rfl) ⟨1336835, by rfl⟩ : syracuseStep 1782447 = 2673671) B2673671
theorem B5714621 : Blo 1782092 5714621 := bstep (se 3 (by rfl) ⟨1071491, by rfl⟩ : syracuseStep 5714621 = 2142983) B2142983
theorem B1782471 : Blo 1782092 1782471 := bstep (se 1 (by rfl) ⟨1336853, by rfl⟩ : syracuseStep 1782471 = 2673707) B2673707
theorem B2675399 : Blo 1782092 2675399 := bstep (se 1 (by rfl) ⟨2006549, by rfl⟩ : syracuseStep 2675399 = 4013099) B4013099
theorem B9024209 : Blo 1782092 9024209 := bstep (se 2 (by rfl) ⟨3384078, by rfl⟩ : syracuseStep 9024209 = 6768157) B6768157
theorem B3912403 : Blo 1782092 3912403 := bstep (se 1 (by rfl) ⟨2934302, by rfl⟩ : syracuseStep 3912403 = 5868605) B5868605
theorem B1782491 : Blo 1782092 1782491 := bstep (se 1 (by rfl) ⟨1336868, by rfl⟩ : syracuseStep 1782491 = 2673737) B2673737
theorem B1782567 : Blo 1782092 1782567 := bstep (se 1 (by rfl) ⟨1336925, by rfl⟩ : syracuseStep 1782567 = 2673851) B2673851
theorem B2855753 : Blo 1782092 2855753 := bstep (se 2 (by rfl) ⟨1070907, by rfl⟩ : syracuseStep 2855753 = 2141815) B2141815
theorem B1782607 : Blo 1782092 1782607 := bstep (se 1 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 1782607 = 2673911) B2673911
theorem B1782623 : Blo 1782092 1782623 := bstep (se 1 (by rfl) ⟨1336967, by rfl⟩ : syracuseStep 1782623 = 2673935) B2673935
theorem B2675561 : Blo 1782092 2675561 := bstep (se 2 (by rfl) ⟨1003335, by rfl⟩ : syracuseStep 2675561 = 2006671) B2006671
theorem B1782651 : Blo 1782092 1782651 := bstep (se 1 (by rfl) ⟨1336988, by rfl⟩ : syracuseStep 1782651 = 2673977) B2673977
theorem B1782703 : Blo 1782092 1782703 := bstep (se 1 (by rfl) ⟨1337027, by rfl⟩ : syracuseStep 1782703 = 2674055) B2674055
theorem B2855855 : Blo 1782092 2855855 := bstep (se 1 (by rfl) ⟨2141891, by rfl⟩ : syracuseStep 2855855 = 4283783) B4283783
theorem B6017975 : Blo 1782092 6017975 := bstep (se 1 (by rfl) ⟨4513481, by rfl⟩ : syracuseStep 6017975 = 9026963) B9026963
theorem B2675639 : Blo 1782092 2675639 := bstep (se 1 (by rfl) ⟨2006729, by rfl⟩ : syracuseStep 2675639 = 4013459) B4013459
theorem B4010939 : Blo 1782092 4010939 := bstep (se 1 (by rfl) ⟨3008204, by rfl⟩ : syracuseStep 4010939 = 6016409) B6016409
theorem B1782727 : Blo 1782092 1782727 := bstep (se 1 (by rfl) ⟨1337045, by rfl⟩ : syracuseStep 1782727 = 2674091) B2674091
theorem B1782747 : Blo 1782092 1782747 := bstep (se 1 (by rfl) ⟨1337060, by rfl⟩ : syracuseStep 1782747 = 2674121) B2674121
theorem B2675675 : Blo 1782092 2675675 := bstep (se 1 (by rfl) ⟨2006756, by rfl⟩ : syracuseStep 2675675 = 4013513) B4013513
theorem B2855945 : Blo 1782092 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B1782823 : Blo 1782092 1782823 := bstep (se 1 (by rfl) ⟨1337117, by rfl⟩ : syracuseStep 1782823 = 2674235) B2674235
theorem B4011065 : Blo 1782092 4011065 := bstep (se 2 (by rfl) ⟨1504149, by rfl⟩ : syracuseStep 4011065 = 3008299) B3008299
theorem B1782863 : Blo 1782092 1782863 := bstep (se 1 (by rfl) ⟨1337147, by rfl⟩ : syracuseStep 1782863 = 2674295) B2674295
theorem B1782879 : Blo 1782092 1782879 := bstep (se 1 (by rfl) ⟨1337159, by rfl⟩ : syracuseStep 1782879 = 2674319) B2674319
theorem B1782907 : Blo 1782092 1782907 := bstep (se 1 (by rfl) ⟨1337180, by rfl⟩ : syracuseStep 1782907 = 2674361) B2674361
theorem B1782959 : Blo 1782092 1782959 := bstep (se 1 (by rfl) ⟨1337219, by rfl⟩ : syracuseStep 1782959 = 2674439) B2674439
theorem B1782983 : Blo 1782092 1782983 := bstep (se 1 (by rfl) ⟨1337237, by rfl⟩ : syracuseStep 1782983 = 2674475) B2674475
theorem B1783003 : Blo 1782092 1783003 := bstep (se 1 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 1783003 = 2674505) B2674505
theorem B1783079 : Blo 1782092 1783079 := bstep (se 1 (by rfl) ⟨1337309, by rfl⟩ : syracuseStep 1783079 = 2674619) B2674619
theorem B1783119 : Blo 1782092 1783119 := bstep (se 1 (by rfl) ⟨1337339, by rfl⟩ : syracuseStep 1783119 = 2674679) B2674679
theorem B12539225 : Blo 1782092 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B1783135 : Blo 1782092 1783135 := bstep (se 1 (by rfl) ⟨1337351, by rfl⟩ : syracuseStep 1783135 = 2674703) B2674703
theorem B1783163 : Blo 1782092 1783163 := bstep (se 1 (by rfl) ⟨1337372, by rfl⟩ : syracuseStep 1783163 = 2674745) B2674745
theorem B4011407 : Blo 1782092 4011407 := bstep (se 1 (by rfl) ⟨3008555, by rfl⟩ : syracuseStep 4011407 = 6017111) B6017111
theorem B12539279 : Blo 1782092 12539279 := bstep (se 1 (by rfl) ⟨9404459, by rfl⟩ : syracuseStep 12539279 = 18808919) B18808919
theorem B1783215 : Blo 1782092 1783215 := bstep (se 1 (by rfl) ⟨1337411, by rfl⟩ : syracuseStep 1783215 = 2674823) B2674823
theorem B1783239 : Blo 1782092 1783239 := bstep (se 1 (by rfl) ⟨1337429, by rfl⟩ : syracuseStep 1783239 = 2674859) B2674859
theorem B1783259 : Blo 1782092 1783259 := bstep (se 1 (by rfl) ⟨1337444, by rfl⟩ : syracuseStep 1783259 = 2674889) B2674889
theorem B6018569 : Blo 1782092 6018569 := bstep (se 2 (by rfl) ⟨2256963, by rfl⟩ : syracuseStep 6018569 = 4513927) B4513927
theorem B1783335 : Blo 1782092 1783335 := bstep (se 1 (by rfl) ⟨1337501, by rfl⟩ : syracuseStep 1783335 = 2675003) B2675003
theorem B625325629 : Blo 1782092 625325629 := bstep (se 3 (by rfl) ⟨117248555, by rfl⟩ : syracuseStep 625325629 = 234497111) B234497111
theorem B1783375 : Blo 1782092 1783375 := bstep (se 1 (by rfl) ⟨1337531, by rfl⟩ : syracuseStep 1783375 = 2675063) B2675063
theorem B11425367 : Blo 1782092 11425367 := bstep (se 1 (by rfl) ⟨8569025, by rfl⟩ : syracuseStep 11425367 = 17138051) B17138051
theorem B1783391 : Blo 1782092 1783391 := bstep (se 1 (by rfl) ⟨1337543, by rfl⟩ : syracuseStep 1783391 = 2675087) B2675087
theorem B1783419 : Blo 1782092 1783419 := bstep (se 1 (by rfl) ⟨1337564, by rfl⟩ : syracuseStep 1783419 = 2675129) B2675129
theorem B8566411 : Blo 1782092 8566411 := bstep (se 1 (by rfl) ⟨6424808, by rfl⟩ : syracuseStep 8566411 = 12849617) B12849617
theorem B1783471 : Blo 1782092 1783471 := bstep (se 1 (by rfl) ⟨1337603, by rfl⟩ : syracuseStep 1783471 = 2675207) B2675207
theorem B1783495 : Blo 1782092 1783495 := bstep (se 1 (by rfl) ⟨1337621, by rfl⟩ : syracuseStep 1783495 = 2675243) B2675243
theorem B4011731 : Blo 1782092 4011731 := bstep (se 1 (by rfl) ⟨3008798, by rfl⟩ : syracuseStep 4011731 = 6017597) B6017597
theorem B4511447 : Blo 1782092 4511447 := bstep (se 1 (by rfl) ⟨3383585, by rfl⟩ : syracuseStep 4511447 = 6767171) B6767171
theorem B1783515 : Blo 1782092 1783515 := bstep (se 1 (by rfl) ⟨1337636, by rfl⟩ : syracuseStep 1783515 = 2675273) B2675273
theorem B9148153 : Blo 1782092 9148153 := bstep (se 2 (by rfl) ⟨3430557, by rfl⟩ : syracuseStep 9148153 = 6861115) B6861115
theorem B1783591 : Blo 1782092 1783591 := bstep (se 1 (by rfl) ⟨1337693, by rfl⟩ : syracuseStep 1783591 = 2675387) B2675387
theorem B1783631 : Blo 1782092 1783631 := bstep (se 1 (by rfl) ⟨1337723, by rfl⟩ : syracuseStep 1783631 = 2675447) B2675447
theorem B1783647 : Blo 1782092 1783647 := bstep (se 1 (by rfl) ⟨1337735, by rfl⟩ : syracuseStep 1783647 = 2675471) B2675471
theorem B1783675 : Blo 1782092 1783675 := bstep (se 1 (by rfl) ⟨1337756, by rfl⟩ : syracuseStep 1783675 = 2675513) B2675513
theorem B1783727 : Blo 1782092 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B1783751 : Blo 1782092 1783751 := bstep (se 1 (by rfl) ⟨1337813, by rfl⟩ : syracuseStep 1783751 = 2675627) B2675627
theorem B1783771 : Blo 1782092 1783771 := bstep (se 1 (by rfl) ⟨1337828, by rfl⟩ : syracuseStep 1783771 = 2675657) B2675657
theorem B12851207 : Blo 1782092 12851207 := bstep (se 1 (by rfl) ⟨9638405, by rfl⟩ : syracuseStep 12851207 = 19276811) B19276811
theorem B1783847 : Blo 1782092 1783847 := bstep (se 1 (by rfl) ⟨1337885, by rfl⟩ : syracuseStep 1783847 = 2675771) B2675771
theorem B4511801 : Blo 1782092 4511801 := bstep (se 2 (by rfl) ⟨1691925, by rfl⟩ : syracuseStep 4511801 = 3383851) B3383851
theorem B1783887 : Blo 1782092 1783887 := bstep (se 1 (by rfl) ⟨1337915, by rfl⟩ : syracuseStep 1783887 = 2675831) B2675831
theorem B1783903 : Blo 1782092 1783903 := bstep (se 1 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 1783903 = 2675855) B2675855
theorem B1783931 : Blo 1782092 1783931 := bstep (se 1 (by rfl) ⟨1337948, by rfl⟩ : syracuseStep 1783931 = 2675897) B2675897
theorem B24402077 : Blo 1782092 24402077 := bstep (se 3 (by rfl) ⟨4575389, by rfl⟩ : syracuseStep 24402077 = 9150779) B9150779
theorem B16275613 : Blo 1782092 16275613 := bstep (se 3 (by rfl) ⟨3051677, by rfl⟩ : syracuseStep 16275613 = 6103355) B6103355
theorem B1783983 : Blo 1782092 1783983 := bstep (se 1 (by rfl) ⟨1337987, by rfl⟩ : syracuseStep 1783983 = 2675975) B2675975
theorem B1784007 : Blo 1782092 1784007 := bstep (se 1 (by rfl) ⟨1338005, by rfl⟩ : syracuseStep 1784007 = 2676011) B2676011
theorem B1784027 : Blo 1782092 1784027 := bstep (se 1 (by rfl) ⟨1338020, by rfl⟩ : syracuseStep 1784027 = 2676041) B2676041
theorem B6773003 : Blo 1782092 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B21698867 : Blo 1782092 21698867 := bstep (se 1 (by rfl) ⟨16274150, by rfl⟩ : syracuseStep 21698867 = 32548301) B32548301
theorem B6019433 : Blo 1782092 6019433 := bstep (se 2 (by rfl) ⟨2257287, by rfl⟩ : syracuseStep 6019433 = 4514575) B4514575
theorem B7936361 : Blo 1782092 7936361 := bstep (se 2 (by rfl) ⟨2976135, by rfl⟩ : syracuseStep 7936361 = 5952271) B5952271
theorem B12851693 : Blo 1782092 12851693 := bstep (se 3 (by rfl) ⟨2409692, by rfl⟩ : syracuseStep 12851693 = 4819385) B4819385
theorem B2005627 : Blo 1782092 2005627 := bstep (se 1 (by rfl) ⟨1504220, by rfl⟩ : syracuseStep 2005627 = 3008441) B3008441
theorem B4012667 : Blo 1782092 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B21977801 : Blo 1782092 21977801 := bstep (se 2 (by rfl) ⟨8241675, by rfl⟩ : syracuseStep 21977801 = 16483351) B16483351
theorem B4012793 : Blo 1782092 4012793 := bstep (se 2 (by rfl) ⟨1504797, by rfl⟩ : syracuseStep 4012793 = 3009595) B3009595
theorem B6020027 : Blo 1782092 6020027 := bstep (se 1 (by rfl) ⟨4515020, by rfl⟩ : syracuseStep 6020027 = 9030041) B9030041
theorem B4013063 : Blo 1782092 4013063 := bstep (se 1 (by rfl) ⟨3009797, by rfl⟩ : syracuseStep 4013063 = 6019595) B6019595
theorem B20307023 : Blo 1782092 20307023 := bstep (se 1 (by rfl) ⟨15230267, by rfl⟩ : syracuseStep 20307023 = 30460535) B30460535
theorem B9026639 : Blo 1782092 9026639 := bstep (se 1 (by rfl) ⟨6769979, by rfl⟩ : syracuseStep 9026639 = 13539959) B13539959
theorem B2006095 : Blo 1782092 2006095 := bstep (se 1 (by rfl) ⟨1504571, by rfl⟩ : syracuseStep 2006095 = 3009143) B3009143
theorem B4013135 : Blo 1782092 4013135 := bstep (se 1 (by rfl) ⟨3009851, by rfl⟩ : syracuseStep 4013135 = 6019703) B6019703
theorem B2006491 : Blo 1782092 2006491 := bstep (se 1 (by rfl) ⟨1504868, by rfl⟩ : syracuseStep 2006491 = 3009737) B3009737
theorem B4013531 : Blo 1782092 4013531 := bstep (se 1 (by rfl) ⟨3010148, by rfl⟩ : syracuseStep 4013531 = 6020297) B6020297
theorem B20315771 : Blo 1782092 20315771 := bstep (se 1 (by rfl) ⟨15236828, by rfl⟩ : syracuseStep 20315771 = 30473657) B30473657
theorem B9027287 : Blo 1782092 9027287 := bstep (se 1 (by rfl) ⟨6770465, by rfl⟩ : syracuseStep 9027287 = 13540931) B13540931
theorem B15646445 : Blo 1782092 15646445 := bstep (se 3 (by rfl) ⟨2933708, by rfl⟩ : syracuseStep 15646445 = 5867417) B5867417
theorem B28917485 : Blo 1782092 28917485 := bstep (se 3 (by rfl) ⟨5422028, by rfl⟩ : syracuseStep 28917485 = 10844057) B10844057
theorem B2006959 : Blo 1782092 2006959 := bstep (se 1 (by rfl) ⟨1505219, by rfl⟩ : syracuseStep 2006959 = 3010439) B3010439
theorem B4013999 : Blo 1782092 4013999 := bstep (se 1 (by rfl) ⟨3010499, by rfl⟩ : syracuseStep 4013999 = 6020999) B6020999
theorem B26058755 : Blo 1782092 26058755 := bstep (se 1 (by rfl) ⟨19544066, by rfl⟩ : syracuseStep 26058755 = 39088133) B39088133
theorem B4014089 : Blo 1782092 4014089 := bstep (se 2 (by rfl) ⟨1505283, by rfl⟩ : syracuseStep 4014089 = 3010567) B3010567
theorem B21700817 : Blo 1782092 21700817 := bstep (se 2 (by rfl) ⟨8137806, by rfl⟩ : syracuseStep 21700817 = 16275613) B16275613
theorem B4514231 : Blo 1782092 4514231 := bstep (se 1 (by rfl) ⟨3385673, by rfl⟩ : syracuseStep 4514231 = 6771347) B6771347
theorem B13533641 : Blo 1782092 13533641 := bstep (se 2 (by rfl) ⟨5075115, by rfl⟩ : syracuseStep 13533641 = 10150231) B10150231
theorem B3809747 : Blo 1782092 3809747 := bstep (se 1 (by rfl) ⟨2857310, by rfl⟩ : syracuseStep 3809747 = 5714621) B5714621
theorem B3211771 : Blo 1782092 3211771 := bstep (se 1 (by rfl) ⟨2408828, by rfl⟩ : syracuseStep 3211771 = 4817657) B4817657
theorem B9028097 : Blo 1782092 9028097 := bstep (se 2 (by rfl) ⟨3385536, by rfl⟩ : syracuseStep 9028097 = 6771073) B6771073
theorem B39617095 : Blo 1782092 39617095 := bstep (se 1 (by rfl) ⟨29712821, by rfl⟩ : syracuseStep 39617095 = 59425643) B59425643
theorem B2409271 : Blo 1782092 2409271 := bstep (se 1 (by rfl) ⟨1806953, by rfl⟩ : syracuseStep 2409271 = 3613907) B3613907
theorem B4817819 : Blo 1782092 4817819 := bstep (se 1 (by rfl) ⟨3613364, by rfl⟩ : syracuseStep 4817819 = 7226729) B7226729
theorem B10847171 : Blo 1782092 10847171 := bstep (se 1 (by rfl) ⟨8135378, by rfl⟩ : syracuseStep 10847171 = 16270757) B16270757
theorem B4883431 : Blo 1782092 4883431 := bstep (se 1 (by rfl) ⟨3662573, by rfl⟩ : syracuseStep 4883431 = 7325147) B7325147
theorem B9028583 : Blo 1782092 9028583 := bstep (se 1 (by rfl) ⟨6771437, by rfl⟩ : syracuseStep 9028583 = 13542875) B13542875
theorem B3007631 : Blo 1782092 3007631 := bstep (se 1 (by rfl) ⟨2255723, by rfl⟩ : syracuseStep 3007631 = 4511447) B4511447
theorem B9028907 : Blo 1782092 9028907 := bstep (se 1 (by rfl) ⟨6771680, by rfl⟩ : syracuseStep 9028907 = 13543361) B13543361
theorem B3007867 : Blo 1782092 3007867 := bstep (se 1 (by rfl) ⟨2255900, by rfl⟩ : syracuseStep 3007867 = 4511801) B4511801
theorem B4711841 : Blo 1782092 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B4515335 : Blo 1782092 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B4515385 : Blo 1782092 4515385 := bstep (se 2 (by rfl) ⟨1693269, by rfl⟩ : syracuseStep 4515385 = 3386539) B3386539
theorem B4515689 : Blo 1782092 4515689 := bstep (se 2 (by rfl) ⟨1693383, by rfl⟩ : syracuseStep 4515689 = 3386767) B3386767
theorem B27453329 : Blo 1782092 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B6424609 : Blo 1782092 6424609 := bstep (se 2 (by rfl) ⟨2409228, by rfl⟩ : syracuseStep 6424609 = 4818457) B4818457
theorem B833767505 : Blo 1782092 833767505 := bstep (se 2 (by rfl) ⟨312662814, by rfl⟩ : syracuseStep 833767505 = 625325629) B625325629
theorem B11421881 : Blo 1782092 11421881 := bstep (se 2 (by rfl) ⟨4283205, by rfl⟩ : syracuseStep 11421881 = 8566411) B8566411
theorem B9029879 : Blo 1782092 9029879 := bstep (se 1 (by rfl) ⟨6772409, by rfl⟩ : syracuseStep 9029879 = 13544819) B13544819
theorem B15231361 : Blo 1782092 15231361 := bstep (se 2 (by rfl) ⟨5711760, by rfl⟩ : syracuseStep 15231361 = 11423521) B11423521
theorem B13543847 : Blo 1782092 13543847 := bstep (se 1 (by rfl) ⟨10157885, by rfl⟩ : syracuseStep 13543847 = 20315771) B20315771
theorem B10430963 : Blo 1782092 10430963 := bstep (se 1 (by rfl) ⟨7823222, by rfl⟩ : syracuseStep 10430963 = 15646445) B15646445
theorem B19278323 : Blo 1782092 19278323 := bstep (se 1 (by rfl) ⟨14458742, by rfl⟩ : syracuseStep 19278323 = 28917485) B28917485
theorem B2673215 : Blo 1782092 2673215 := bstep (se 1 (by rfl) ⟨2004911, by rfl⟩ : syracuseStep 2673215 = 4009823) B4009823
theorem B3050057 : Blo 1782092 3050057 := bstep (se 2 (by rfl) ⟨1143771, by rfl⟩ : syracuseStep 3050057 = 2287543) B2287543
theorem B2673335 : Blo 1782092 2673335 := bstep (se 1 (by rfl) ⟨2005001, by rfl⟩ : syracuseStep 2673335 = 4010003) B4010003
theorem B9030365 : Blo 1782092 9030365 := bstep (se 3 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 9030365 = 3386387) B3386387
theorem B10160963 : Blo 1782092 10160963 := bstep (se 1 (by rfl) ⟨7620722, by rfl⟩ : syracuseStep 10160963 = 15241445) B15241445
theorem B3009359 : Blo 1782092 3009359 := bstep (se 1 (by rfl) ⟨2257019, by rfl⟩ : syracuseStep 3009359 = 4514039) B4514039
theorem B6015869 : Blo 1782092 6015869 := bstep (se 3 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 6015869 = 2255951) B2255951
theorem B2673563 : Blo 1782092 2673563 := bstep (se 1 (by rfl) ⟨2005172, by rfl⟩ : syracuseStep 2673563 = 4010345) B4010345
theorem B8129575 : Blo 1782092 8129575 := bstep (se 1 (by rfl) ⟨6097181, by rfl⟩ : syracuseStep 8129575 = 12194363) B12194363
theorem B16264259 : Blo 1782092 16264259 := bstep (se 1 (by rfl) ⟨12198194, by rfl⟩ : syracuseStep 16264259 = 24396389) B24396389
theorem B6016139 : Blo 1782092 6016139 := bstep (se 1 (by rfl) ⟨4512104, by rfl⟩ : syracuseStep 6016139 = 9024209) B9024209
theorem B1903835 : Blo 1782092 1903835 := bstep (se 1 (by rfl) ⟨1427876, by rfl⟩ : syracuseStep 1903835 = 2855753) B2855753
theorem B9022751 : Blo 1782092 9022751 := bstep (se 1 (by rfl) ⟨6767063, by rfl⟩ : syracuseStep 9022751 = 13534127) B13534127
theorem B2673959 : Blo 1782092 2673959 := bstep (se 1 (by rfl) ⟨2005469, by rfl⟩ : syracuseStep 2673959 = 4010939) B4010939
theorem B2674043 : Blo 1782092 2674043 := bstep (se 1 (by rfl) ⟨2005532, by rfl⟩ : syracuseStep 2674043 = 4011065) B4011065
theorem B8564105 : Blo 1782092 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B57863645 : Blo 1782092 57863645 := bstep (se 3 (by rfl) ⟨10849433, by rfl⟩ : syracuseStep 57863645 = 21698867) B21698867
theorem B2674169 : Blo 1782092 2674169 := bstep (se 2 (by rfl) ⟨1002813, by rfl⟩ : syracuseStep 2674169 = 2005627) B2005627
theorem B3386873 : Blo 1782092 3386873 := bstep (se 2 (by rfl) ⟨1270077, by rfl⟩ : syracuseStep 3386873 = 2540155) B2540155
theorem B2674271 : Blo 1782092 2674271 := bstep (se 1 (by rfl) ⟨2005703, by rfl⟩ : syracuseStep 2674271 = 4011407) B4011407
theorem B8359519 : Blo 1782092 8359519 := bstep (se 1 (by rfl) ⟨6269639, by rfl⟩ : syracuseStep 8359519 = 12539279) B12539279
theorem B4009769 : Blo 1782092 4009769 := bstep (se 2 (by rfl) ⟨1503663, by rfl⟩ : syracuseStep 4009769 = 3007327) B3007327
theorem B3010351 : Blo 1782092 3010351 := bstep (se 1 (by rfl) ⟨2257763, by rfl⟩ : syracuseStep 3010351 = 4515527) B4515527
theorem B2674487 : Blo 1782092 2674487 := bstep (se 1 (by rfl) ⟨2005865, by rfl⟩ : syracuseStep 2674487 = 4011731) B4011731
theorem B8130361 : Blo 1782092 8130361 := bstep (se 2 (by rfl) ⟨3048885, by rfl⟩ : syracuseStep 8130361 = 6097771) B6097771
theorem B2674793 : Blo 1782092 2674793 := bstep (se 2 (by rfl) ⟨1003047, by rfl⟩ : syracuseStep 2674793 = 2006095) B2006095
theorem B1782107 : Blo 1782092 1782107 := bstep (se 1 (by rfl) ⟨1336580, by rfl⟩ : syracuseStep 1782107 = 2673161) B2673161
theorem B1782127 : Blo 1782092 1782127 := bstep (se 1 (by rfl) ⟨1336595, by rfl⟩ : syracuseStep 1782127 = 2673191) B2673191
theorem B1782183 : Blo 1782092 1782183 := bstep (se 1 (by rfl) ⟨1336637, by rfl⟩ : syracuseStep 1782183 = 2673275) B2673275
theorem B2675111 : Blo 1782092 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B5714351 : Blo 1782092 5714351 := bstep (se 1 (by rfl) ⟨4285763, by rfl⟩ : syracuseStep 5714351 = 8571527) B8571527
theorem B14651867 : Blo 1782092 14651867 := bstep (se 1 (by rfl) ⟨10988900, by rfl⟩ : syracuseStep 14651867 = 21977801) B21977801
theorem B1782267 : Blo 1782092 1782267 := bstep (se 1 (by rfl) ⟨1336700, by rfl⟩ : syracuseStep 1782267 = 2673401) B2673401
theorem B2675195 : Blo 1782092 2675195 := bstep (se 1 (by rfl) ⟨2006396, by rfl⟩ : syracuseStep 2675195 = 4012793) B4012793
theorem B1782335 : Blo 1782092 1782335 := bstep (se 1 (by rfl) ⟨1336751, by rfl⟩ : syracuseStep 1782335 = 2673503) B2673503
theorem B1782343 : Blo 1782092 1782343 := bstep (se 1 (by rfl) ⟨1336757, by rfl⟩ : syracuseStep 1782343 = 2673515) B2673515
theorem B2675321 : Blo 1782092 2675321 := bstep (se 2 (by rfl) ⟨1003245, by rfl⟩ : syracuseStep 2675321 = 2006491) B2006491
theorem B6427289 : Blo 1782092 6427289 := bstep (se 2 (by rfl) ⟨2410233, by rfl⟩ : syracuseStep 6427289 = 4820467) B4820467
theorem B2675375 : Blo 1782092 2675375 := bstep (se 1 (by rfl) ⟨2006531, by rfl⟩ : syracuseStep 2675375 = 4013063) B4013063
theorem B1782495 : Blo 1782092 1782495 := bstep (se 1 (by rfl) ⟨1336871, by rfl⟩ : syracuseStep 1782495 = 2673743) B2673743
theorem B13538015 : Blo 1782092 13538015 := bstep (se 1 (by rfl) ⟨10153511, by rfl⟩ : syracuseStep 13538015 = 20307023) B20307023
theorem B6017759 : Blo 1782092 6017759 := bstep (se 1 (by rfl) ⟨4513319, by rfl⟩ : syracuseStep 6017759 = 9026639) B9026639
theorem B2675423 : Blo 1782092 2675423 := bstep (se 1 (by rfl) ⟨2006567, by rfl⟩ : syracuseStep 2675423 = 4013135) B4013135
theorem B16495327 : Blo 1782092 16495327 := bstep (se 1 (by rfl) ⟨12371495, by rfl⟩ : syracuseStep 16495327 = 24742991) B24742991
theorem B1782575 : Blo 1782092 1782575 := bstep (se 1 (by rfl) ⟨1336931, by rfl⟩ : syracuseStep 1782575 = 2673863) B2673863
theorem B4010831 : Blo 1782092 4010831 := bstep (se 1 (by rfl) ⟨3008123, by rfl⟩ : syracuseStep 4010831 = 6016247) B6016247
theorem B1782683 : Blo 1782092 1782683 := bstep (se 1 (by rfl) ⟨1337012, by rfl⟩ : syracuseStep 1782683 = 2674025) B2674025
theorem B1782735 : Blo 1782092 1782735 := bstep (se 1 (by rfl) ⟨1337051, by rfl⟩ : syracuseStep 1782735 = 2674103) B2674103
theorem B1782759 : Blo 1782092 1782759 := bstep (se 1 (by rfl) ⟨1337069, by rfl⟩ : syracuseStep 1782759 = 2674139) B2674139
theorem B2675687 : Blo 1782092 2675687 := bstep (se 1 (by rfl) ⟨2006765, by rfl⟩ : syracuseStep 2675687 = 4013531) B4013531
theorem B2257895 : Blo 1782092 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B5075959 : Blo 1782092 5075959 := bstep (se 1 (by rfl) ⟨3806969, by rfl⟩ : syracuseStep 5075959 = 7613939) B7613939
theorem B4011047 : Blo 1782092 4011047 := bstep (se 1 (by rfl) ⟨3008285, by rfl⟩ : syracuseStep 4011047 = 6016571) B6016571
theorem B5715041 : Blo 1782092 5715041 := bstep (se 2 (by rfl) ⟨2143140, by rfl⟩ : syracuseStep 5715041 = 4286281) B4286281
theorem B7615613 : Blo 1782092 7615613 := bstep (se 3 (by rfl) ⟨1427927, by rfl⟩ : syracuseStep 7615613 = 2855855) B2855855
theorem B6018191 : Blo 1782092 6018191 := bstep (se 1 (by rfl) ⟨4513643, by rfl⟩ : syracuseStep 6018191 = 9027287) B9027287
theorem B4011227 : Blo 1782092 4011227 := bstep (se 1 (by rfl) ⟨3008420, by rfl⟩ : syracuseStep 4011227 = 6016841) B6016841
theorem B2675945 : Blo 1782092 2675945 := bstep (se 2 (by rfl) ⟨1003479, by rfl⟩ : syracuseStep 2675945 = 2006959) B2006959
theorem B1783071 : Blo 1782092 1783071 := bstep (se 1 (by rfl) ⟨1337303, by rfl⟩ : syracuseStep 1783071 = 2674607) B2674607
theorem B2675999 : Blo 1782092 2675999 := bstep (se 1 (by rfl) ⟨2006999, by rfl⟩ : syracuseStep 2675999 = 4013999) B4013999
theorem B1783131 : Blo 1782092 1783131 := bstep (se 1 (by rfl) ⟨1337348, by rfl⟩ : syracuseStep 1783131 = 2674697) B2674697
theorem B7615853 : Blo 1782092 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B1783151 : Blo 1782092 1783151 := bstep (se 1 (by rfl) ⟨1337363, by rfl⟩ : syracuseStep 1783151 = 2674727) B2674727
theorem B19289477 : Blo 1782092 19289477 := bstep (se 4 (by rfl) ⟨1808388, by rfl⟩ : syracuseStep 19289477 = 3616777) B3616777
theorem B57849227 : Blo 1782092 57849227 := bstep (se 1 (by rfl) ⟨43386920, by rfl⟩ : syracuseStep 57849227 = 86773841) B86773841
theorem B4011425 : Blo 1782092 4011425 := bstep (se 2 (by rfl) ⟨1504284, by rfl⟩ : syracuseStep 4011425 = 3008569) B3008569
theorem B1783207 : Blo 1782092 1783207 := bstep (se 1 (by rfl) ⟨1337405, by rfl⟩ : syracuseStep 1783207 = 2674811) B2674811
theorem B3806713 : Blo 1782092 3806713 := bstep (se 2 (by rfl) ⟨1427517, by rfl⟩ : syracuseStep 3806713 = 2855035) B2855035
theorem B1783291 : Blo 1782092 1783291 := bstep (se 1 (by rfl) ⟨1337468, by rfl⟩ : syracuseStep 1783291 = 2674937) B2674937
theorem B1783359 : Blo 1782092 1783359 := bstep (se 1 (by rfl) ⟨1337519, by rfl⟩ : syracuseStep 1783359 = 2675039) B2675039
theorem B1783367 : Blo 1782092 1783367 := bstep (se 1 (by rfl) ⟨1337525, by rfl⟩ : syracuseStep 1783367 = 2675051) B2675051
theorem B4511315 : Blo 1782092 4511315 := bstep (se 1 (by rfl) ⟨3383486, by rfl⟩ : syracuseStep 4511315 = 6766973) B6766973
theorem B9025181 : Blo 1782092 9025181 := bstep (se 3 (by rfl) ⟨1692221, by rfl⟩ : syracuseStep 9025181 = 3384443) B3384443
theorem B1783519 : Blo 1782092 1783519 := bstep (se 1 (by rfl) ⟨1337639, by rfl⟩ : syracuseStep 1783519 = 2675279) B2675279
theorem B1783599 : Blo 1782092 1783599 := bstep (se 1 (by rfl) ⟨1337699, by rfl⟩ : syracuseStep 1783599 = 2675399) B2675399
theorem B1783707 : Blo 1782092 1783707 := bstep (se 1 (by rfl) ⟨1337780, by rfl⟩ : syracuseStep 1783707 = 2675561) B2675561
theorem B2004943 : Blo 1782092 2004943 := bstep (se 1 (by rfl) ⟨1503707, by rfl⟩ : syracuseStep 2004943 = 3007415) B3007415
theorem B4011983 : Blo 1782092 4011983 := bstep (se 1 (by rfl) ⟨3008987, by rfl⟩ : syracuseStep 4011983 = 6017975) B6017975
theorem B1783759 : Blo 1782092 1783759 := bstep (se 1 (by rfl) ⟨1337819, by rfl⟩ : syracuseStep 1783759 = 2675639) B2675639
theorem B1783783 : Blo 1782092 1783783 := bstep (se 1 (by rfl) ⟨1337837, by rfl⟩ : syracuseStep 1783783 = 2675675) B2675675
theorem B33437933 : Blo 1782092 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B8132861 : Blo 1782092 8132861 := bstep (se 3 (by rfl) ⟨1524911, by rfl⟩ : syracuseStep 8132861 = 3049823) B3049823
theorem B6019325 : Blo 1782092 6019325 := bstep (se 3 (by rfl) ⟨1128623, by rfl⟩ : syracuseStep 6019325 = 2257247) B2257247
theorem B5216537 : Blo 1782092 5216537 := bstep (se 2 (by rfl) ⟨1956201, by rfl⟩ : syracuseStep 5216537 = 3912403) B3912403
theorem B6773017 : Blo 1782092 6773017 := bstep (se 2 (by rfl) ⟨2539881, by rfl⟩ : syracuseStep 6773017 = 5079763) B5079763
theorem B4012361 : Blo 1782092 4012361 := bstep (se 2 (by rfl) ⟨1504635, by rfl⟩ : syracuseStep 4012361 = 3009271) B3009271
theorem B2005339 : Blo 1782092 2005339 := bstep (se 1 (by rfl) ⟨1504004, by rfl⟩ : syracuseStep 2005339 = 3008009) B3008009
theorem B4012379 : Blo 1782092 4012379 := bstep (se 1 (by rfl) ⟨3009284, by rfl⟩ : syracuseStep 4012379 = 6018569) B6018569
theorem B15227261 : Blo 1782092 15227261 := bstep (se 3 (by rfl) ⟨2855111, by rfl⟩ : syracuseStep 15227261 = 5710223) B5710223
theorem B7616911 : Blo 1782092 7616911 := bstep (se 1 (by rfl) ⟨5712683, by rfl⟩ : syracuseStep 7616911 = 11425367) B11425367
theorem B84654517 : Blo 1782092 84654517 := bstep (se 5 (by rfl) ⟨3968180, by rfl⟩ : syracuseStep 84654517 = 7936361) B7936361
theorem B2005447 : Blo 1782092 2005447 := bstep (se 1 (by rfl) ⟨1504085, by rfl⟩ : syracuseStep 2005447 = 3008171) B3008171
theorem B24746555 : Blo 1782092 24746555 := bstep (se 1 (by rfl) ⟨18559916, by rfl⟩ : syracuseStep 24746555 = 37119833) B37119833
theorem B6773321 : Blo 1782092 6773321 := bstep (se 2 (by rfl) ⟨2539995, by rfl⟩ : syracuseStep 6773321 = 5079991) B5079991
theorem B15645317 : Blo 1782092 15645317 := bstep (se 4 (by rfl) ⟨1466748, by rfl⟩ : syracuseStep 15645317 = 2933497) B2933497
theorem B8567471 : Blo 1782092 8567471 := bstep (se 1 (by rfl) ⟨6425603, by rfl⟩ : syracuseStep 8567471 = 12851207) B12851207
theorem B13720259 : Blo 1782092 13720259 := bstep (se 1 (by rfl) ⟨10290194, by rfl⟩ : syracuseStep 13720259 = 20580389) B20580389
theorem B16268051 : Blo 1782092 16268051 := bstep (se 1 (by rfl) ⟨12201038, by rfl⟩ : syracuseStep 16268051 = 24402077) B24402077
theorem B2005807 : Blo 1782092 2005807 := bstep (se 1 (by rfl) ⟨1504355, by rfl⟩ : syracuseStep 2005807 = 3008711) B3008711
theorem B2005915 : Blo 1782092 2005915 := bstep (se 1 (by rfl) ⟨1504436, by rfl⟩ : syracuseStep 2005915 = 3008873) B3008873
theorem B4012955 : Blo 1782092 4012955 := bstep (se 1 (by rfl) ⟨3009716, by rfl⟩ : syracuseStep 4012955 = 6019433) B6019433
theorem B9026477 : Blo 1782092 9026477 := bstep (se 3 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 9026477 = 3384929) B3384929
theorem B4512743 : Blo 1782092 4512743 := bstep (se 1 (by rfl) ⟨3384557, by rfl⟩ : syracuseStep 4512743 = 6769115) B6769115
theorem B8567795 : Blo 1782092 8567795 := bstep (se 1 (by rfl) ⟨6425846, by rfl⟩ : syracuseStep 8567795 = 12851693) B12851693
theorem B6020135 : Blo 1782092 6020135 := bstep (se 1 (by rfl) ⟨4515101, by rfl⟩ : syracuseStep 6020135 = 9030203) B9030203
theorem B4013153 : Blo 1782092 4013153 := bstep (se 2 (by rfl) ⟨1504932, by rfl⟩ : syracuseStep 4013153 = 3009865) B3009865
theorem B2006311 : Blo 1782092 2006311 := bstep (se 1 (by rfl) ⟨1504733, by rfl⟩ : syracuseStep 2006311 = 3009467) B3009467
theorem B4013351 : Blo 1782092 4013351 := bstep (se 1 (by rfl) ⟨3010013, by rfl⟩ : syracuseStep 4013351 = 6020027) B6020027
theorem B2006383 : Blo 1782092 2006383 := bstep (se 1 (by rfl) ⟨1504787, by rfl⟩ : syracuseStep 2006383 = 3009575) B3009575
theorem B15228323 : Blo 1782092 15228323 := bstep (se 1 (by rfl) ⟨11421242, by rfl⟩ : syracuseStep 15228323 = 22842485) B22842485
theorem B8134103 : Blo 1782092 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B6020567 : Blo 1782092 6020567 := bstep (se 1 (by rfl) ⟨4515425, by rfl⟩ : syracuseStep 6020567 = 9030851) B9030851
theorem B2006599 : Blo 1782092 2006599 := bstep (se 1 (by rfl) ⟨1504949, by rfl⟩ : syracuseStep 2006599 = 3009899) B3009899
theorem B11419217 : Blo 1782092 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B12197537 : Blo 1782092 12197537 := bstep (se 2 (by rfl) ⟨4574076, by rfl⟩ : syracuseStep 12197537 = 9148153) B9148153
theorem B4513441 : Blo 1782092 4513441 := bstep (se 2 (by rfl) ⟨1692540, by rfl⟩ : syracuseStep 4513441 = 3385081) B3385081
theorem B4013729 : Blo 1782092 4013729 := bstep (se 2 (by rfl) ⟨1505148, by rfl⟩ : syracuseStep 4013729 = 3010297) B3010297
theorem B4513583 : Blo 1782092 4513583 := bstep (se 1 (by rfl) ⟨3385187, by rfl⟩ : syracuseStep 4513583 = 6770375) B6770375
theorem B14467211 : Blo 1782092 14467211 := bstep (se 1 (by rfl) ⟨10850408, by rfl⟩ : syracuseStep 14467211 = 21700817) B21700817
theorem B3809567 : Blo 1782092 3809567 := bstep (se 1 (by rfl) ⟨2857175, by rfl⟩ : syracuseStep 3809567 = 5714351) B5714351
theorem B2539831 : Blo 1782092 2539831 := bstep (se 1 (by rfl) ⟨1904873, by rfl⟩ : syracuseStep 2539831 = 3809747) B3809747
theorem B20308481 : Blo 1782092 20308481 := bstep (se 2 (by rfl) ⟨7615680, by rfl⟩ : syracuseStep 20308481 = 15231361) B15231361
theorem B52822793 : Blo 1782092 52822793 := bstep (se 2 (by rfl) ⟨19808547, by rfl⟩ : syracuseStep 52822793 = 39617095) B39617095
theorem B3007543 : Blo 1782092 3007543 := bstep (se 1 (by rfl) ⟨2255657, by rfl⟩ : syracuseStep 3007543 = 4511315) B4511315
theorem B18302219 : Blo 1782092 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B6767945 : Blo 1782092 6767945 := bstep (se 2 (by rfl) ⟨2537979, by rfl⟩ : syracuseStep 6767945 = 5075959) B5075959
theorem B10839433 : Blo 1782092 10839433 := bstep (se 2 (by rfl) ⟨4064787, by rfl⟩ : syracuseStep 10839433 = 8129575) B8129575
theorem B555845003 : Blo 1782092 555845003 := bstep (se 1 (by rfl) ⟨416883752, by rfl⟩ : syracuseStep 555845003 = 833767505) B833767505
theorem B22291955 : Blo 1782092 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B10151507 : Blo 1782092 10151507 := bstep (se 1 (by rfl) ⟨7613630, by rfl⟩ : syracuseStep 10151507 = 15227261) B15227261
theorem B9029231 : Blo 1782092 9029231 := bstep (se 1 (by rfl) ⟨6771923, by rfl⟩ : syracuseStep 9029231 = 13543847) B13543847
theorem B2033371 : Blo 1782092 2033371 := bstep (se 1 (by rfl) ⟨1525028, by rfl⟩ : syracuseStep 2033371 = 3050057) B3050057
theorem B4515547 : Blo 1782092 4515547 := bstep (se 1 (by rfl) ⟨3386660, by rfl⟩ : syracuseStep 4515547 = 6773321) B6773321
theorem B17139437 : Blo 1782092 17139437 := bstep (se 3 (by rfl) ⟨3213644, by rfl⟩ : syracuseStep 17139437 = 6427289) B6427289
theorem B5711647 : Blo 1782092 5711647 := bstep (se 1 (by rfl) ⟨4283735, by rfl⟩ : syracuseStep 5711647 = 8567471) B8567471
theorem B3008495 : Blo 1782092 3008495 := bstep (se 1 (by rfl) ⟨2256371, by rfl⟩ : syracuseStep 3008495 = 4512743) B4512743
theorem B6015167 : Blo 1782092 6015167 := bstep (se 1 (by rfl) ⟨4511375, by rfl⟩ : syracuseStep 6015167 = 9022751) B9022751
theorem B10152215 : Blo 1782092 10152215 := bstep (se 1 (by rfl) ⟨7614161, by rfl⟩ : syracuseStep 10152215 = 15228323) B15228323
theorem B7612811 : Blo 1782092 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B12847517 : Blo 1782092 12847517 := bstep (se 3 (by rfl) ⟨2408909, by rfl⟩ : syracuseStep 12847517 = 4817819) B4817819
theorem B10840481 : Blo 1782092 10840481 := bstep (se 2 (by rfl) ⟨4065180, by rfl⟩ : syracuseStep 10840481 = 8130361) B8130361
theorem B2673179 : Blo 1782092 2673179 := bstep (se 1 (by rfl) ⟨2004884, by rfl⟩ : syracuseStep 2673179 = 4009769) B4009769
theorem B3009055 : Blo 1782092 3009055 := bstep (se 1 (by rfl) ⟨2256791, by rfl⟩ : syracuseStep 3009055 = 4513583) B4513583
theorem B2673257 : Blo 1782092 2673257 := bstep (se 2 (by rfl) ⟨1002471, by rfl⟩ : syracuseStep 2673257 = 2004943) B2004943
theorem B15240109 : Blo 1782092 15240109 := bstep (se 3 (by rfl) ⟨2857520, by rfl⟩ : syracuseStep 15240109 = 5715041) B5715041
theorem B3009487 : Blo 1782092 3009487 := bstep (se 1 (by rfl) ⟨2257115, by rfl⟩ : syracuseStep 3009487 = 4514231) B4514231
theorem B9022427 : Blo 1782092 9022427 := bstep (se 1 (by rfl) ⟨6766820, by rfl⟩ : syracuseStep 9022427 = 13533641) B13533641
theorem B9030689 : Blo 1782092 9030689 := bstep (se 2 (by rfl) ⟨3386508, by rfl⟩ : syracuseStep 9030689 = 6773017) B6773017
theorem B2673785 : Blo 1782092 2673785 := bstep (se 2 (by rfl) ⟨1002669, by rfl⟩ : syracuseStep 2673785 = 2005339) B2005339
theorem B2673887 : Blo 1782092 2673887 := bstep (se 1 (by rfl) ⟨2005415, by rfl⟩ : syracuseStep 2673887 = 4010831) B4010831
theorem B112872689 : Blo 1782092 112872689 := bstep (se 2 (by rfl) ⟨42327258, by rfl⟩ : syracuseStep 112872689 = 84654517) B84654517
theorem B2673929 : Blo 1782092 2673929 := bstep (se 2 (by rfl) ⟨1002723, by rfl⟩ : syracuseStep 2673929 = 2005447) B2005447
theorem B2674031 : Blo 1782092 2674031 := bstep (se 1 (by rfl) ⟨2005523, by rfl⟩ : syracuseStep 2674031 = 4011047) B4011047
theorem B2674151 : Blo 1782092 2674151 := bstep (se 1 (by rfl) ⟨2005613, by rfl⟩ : syracuseStep 2674151 = 4011227) B4011227
theorem B2674283 : Blo 1782092 2674283 := bstep (se 1 (by rfl) ⟨2005712, by rfl⟩ : syracuseStep 2674283 = 4011425) B4011425
theorem B3141227 : Blo 1782092 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B3010223 : Blo 1782092 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B2674409 : Blo 1782092 2674409 := bstep (se 2 (by rfl) ⟨1002903, by rfl⟩ : syracuseStep 2674409 = 2005807) B2005807
theorem B6016787 : Blo 1782092 6016787 := bstep (se 1 (by rfl) ⟨4512590, by rfl⟩ : syracuseStep 6016787 = 9025181) B9025181
theorem B2674553 : Blo 1782092 2674553 := bstep (se 2 (by rfl) ⟨1002957, by rfl⟩ : syracuseStep 2674553 = 2005915) B2005915
theorem B3010459 : Blo 1782092 3010459 := bstep (se 1 (by rfl) ⟨2257844, by rfl⟩ : syracuseStep 3010459 = 4515689) B4515689
theorem B39071645 : Blo 1782092 39071645 := bstep (se 3 (by rfl) ⟨7325933, by rfl⟩ : syracuseStep 39071645 = 14651867) B14651867
theorem B2674655 : Blo 1782092 2674655 := bstep (se 1 (by rfl) ⟨2005991, by rfl⟩ : syracuseStep 2674655 = 4011983) B4011983
theorem B9031661 : Blo 1782092 9031661 := bstep (se 3 (by rfl) ⟨1693436, by rfl⟩ : syracuseStep 9031661 = 3386873) B3386873
theorem B7614587 : Blo 1782092 7614587 := bstep (se 1 (by rfl) ⟨5710940, by rfl⟩ : syracuseStep 7614587 = 11421881) B11421881
theorem B3477691 : Blo 1782092 3477691 := bstep (se 1 (by rfl) ⟨2608268, by rfl⟩ : syracuseStep 3477691 = 5216537) B5216537
theorem B2674907 : Blo 1782092 2674907 := bstep (se 1 (by rfl) ⟨2006180, by rfl⟩ : syracuseStep 2674907 = 4012361) B4012361
theorem B2674919 : Blo 1782092 2674919 := bstep (se 1 (by rfl) ⟨2006189, by rfl⟩ : syracuseStep 2674919 = 4012379) B4012379
theorem B12849445 : Blo 1782092 12849445 := bstep (se 4 (by rfl) ⟨1204635, by rfl⟩ : syracuseStep 12849445 = 2409271) B2409271
theorem B1782143 : Blo 1782092 1782143 := bstep (se 1 (by rfl) ⟨1336607, by rfl⟩ : syracuseStep 1782143 = 2673215) B2673215
theorem B2675081 : Blo 1782092 2675081 := bstep (se 2 (by rfl) ⟨1003155, by rfl⟩ : syracuseStep 2675081 = 2006311) B2006311
theorem B1782223 : Blo 1782092 1782223 := bstep (se 1 (by rfl) ⟨1336667, by rfl⟩ : syracuseStep 1782223 = 2673335) B2673335
theorem B9146839 : Blo 1782092 9146839 := bstep (se 1 (by rfl) ⟨6860129, by rfl⟩ : syracuseStep 9146839 = 13720259) B13720259
theorem B2675177 : Blo 1782092 2675177 := bstep (se 2 (by rfl) ⟨1003191, by rfl⟩ : syracuseStep 2675177 = 2006383) B2006383
theorem B4010489 : Blo 1782092 4010489 := bstep (se 2 (by rfl) ⟨1503933, by rfl⟩ : syracuseStep 4010489 = 3007867) B3007867
theorem B4010579 : Blo 1782092 4010579 := bstep (se 1 (by rfl) ⟨3007934, by rfl⟩ : syracuseStep 4010579 = 6015869) B6015869
theorem B1782375 : Blo 1782092 1782375 := bstep (se 1 (by rfl) ⟨1336781, by rfl⟩ : syracuseStep 1782375 = 2673563) B2673563
theorem B2675303 : Blo 1782092 2675303 := bstep (se 1 (by rfl) ⟨2006477, by rfl⟩ : syracuseStep 2675303 = 4012955) B4012955
theorem B6017651 : Blo 1782092 6017651 := bstep (se 1 (by rfl) ⟨4513238, by rfl⟩ : syracuseStep 6017651 = 9026477) B9026477
theorem B5075617 : Blo 1782092 5075617 := bstep (se 2 (by rfl) ⟨1903356, by rfl⟩ : syracuseStep 5075617 = 3806713) B3806713
theorem B10842839 : Blo 1782092 10842839 := bstep (se 1 (by rfl) ⟨8132129, by rfl⟩ : syracuseStep 10842839 = 16264259) B16264259
theorem B43381469 : Blo 1782092 43381469 := bstep (se 3 (by rfl) ⟨8134025, by rfl⟩ : syracuseStep 43381469 = 16268051) B16268051
theorem B2675435 : Blo 1782092 2675435 := bstep (se 1 (by rfl) ⟨2006576, by rfl⟩ : syracuseStep 2675435 = 4013153) B4013153
theorem B4010759 : Blo 1782092 4010759 := bstep (se 1 (by rfl) ⟨3008069, by rfl⟩ : syracuseStep 4010759 = 6016139) B6016139
theorem B2675465 : Blo 1782092 2675465 := bstep (se 2 (by rfl) ⟨1003299, by rfl⟩ : syracuseStep 2675465 = 2006599) B2006599
theorem B11146025 : Blo 1782092 11146025 := bstep (se 2 (by rfl) ⟨4179759, by rfl⟩ : syracuseStep 11146025 = 8359519) B8359519
theorem B1782639 : Blo 1782092 1782639 := bstep (se 1 (by rfl) ⟨1336979, by rfl⟩ : syracuseStep 1782639 = 2673959) B2673959
theorem B2675567 : Blo 1782092 2675567 := bstep (se 1 (by rfl) ⟨2006675, by rfl⟩ : syracuseStep 2675567 = 4013351) B4013351
theorem B6017921 : Blo 1782092 6017921 := bstep (se 2 (by rfl) ⟨2256720, by rfl⟩ : syracuseStep 6017921 = 4513441) B4513441
theorem B1782695 : Blo 1782092 1782695 := bstep (se 1 (by rfl) ⟨1337021, by rfl⟩ : syracuseStep 1782695 = 2674043) B2674043
theorem B1782779 : Blo 1782092 1782779 := bstep (se 1 (by rfl) ⟨1337084, by rfl⟩ : syracuseStep 1782779 = 2674169) B2674169
theorem B1782847 : Blo 1782092 1782847 := bstep (se 1 (by rfl) ⟨1337135, by rfl⟩ : syracuseStep 1782847 = 2674271) B2674271
theorem B8131691 : Blo 1782092 8131691 := bstep (se 1 (by rfl) ⟨6098768, by rfl⟩ : syracuseStep 8131691 = 12197537) B12197537
theorem B2675819 : Blo 1782092 2675819 := bstep (se 1 (by rfl) ⟨2006864, by rfl⟩ : syracuseStep 2675819 = 4013729) B4013729
theorem B1782991 : Blo 1782092 1782991 := bstep (se 1 (by rfl) ⟨1337243, by rfl⟩ : syracuseStep 1782991 = 2674487) B2674487
theorem B17372503 : Blo 1782092 17372503 := bstep (se 1 (by rfl) ⟨13029377, by rfl⟩ : syracuseStep 17372503 = 26058755) B26058755
theorem B2676059 : Blo 1782092 2676059 := bstep (se 1 (by rfl) ⟨2007044, by rfl⟩ : syracuseStep 2676059 = 4014089) B4014089
theorem B8566145 : Blo 1782092 8566145 := bstep (se 2 (by rfl) ⟨3212304, by rfl⟩ : syracuseStep 8566145 = 6424609) B6424609
theorem B1783195 : Blo 1782092 1783195 := bstep (se 1 (by rfl) ⟨1337396, by rfl⟩ : syracuseStep 1783195 = 2674793) B2674793
theorem B1783407 : Blo 1782092 1783407 := bstep (se 1 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 1783407 = 2675111) B2675111
theorem B1783463 : Blo 1782092 1783463 := bstep (se 1 (by rfl) ⟨1337597, by rfl⟩ : syracuseStep 1783463 = 2675195) B2675195
theorem B6018731 : Blo 1782092 6018731 := bstep (se 1 (by rfl) ⟨4514048, by rfl⟩ : syracuseStep 6018731 = 9028097) B9028097
theorem B1783547 : Blo 1782092 1783547 := bstep (se 1 (by rfl) ⟨1337660, by rfl⟩ : syracuseStep 1783547 = 2675321) B2675321
theorem B1783583 : Blo 1782092 1783583 := bstep (se 1 (by rfl) ⟨1337687, by rfl⟩ : syracuseStep 1783583 = 2675375) B2675375
theorem B9025343 : Blo 1782092 9025343 := bstep (se 1 (by rfl) ⟨6769007, by rfl⟩ : syracuseStep 9025343 = 13538015) B13538015
theorem B4011839 : Blo 1782092 4011839 := bstep (se 1 (by rfl) ⟨3008879, by rfl⟩ : syracuseStep 4011839 = 6017759) B6017759
theorem B1783615 : Blo 1782092 1783615 := bstep (se 1 (by rfl) ⟨1337711, by rfl⟩ : syracuseStep 1783615 = 2675423) B2675423
theorem B10155881 : Blo 1782092 10155881 := bstep (se 2 (by rfl) ⟨3808455, by rfl⟩ : syracuseStep 10155881 = 7616911) B7616911
theorem B5076893 : Blo 1782092 5076893 := bstep (se 3 (by rfl) ⟨951917, by rfl⟩ : syracuseStep 5076893 = 1903835) B1903835
theorem B7231447 : Blo 1782092 7231447 := bstep (se 1 (by rfl) ⟨5423585, by rfl⟩ : syracuseStep 7231447 = 10847171) B10847171
theorem B6019055 : Blo 1782092 6019055 := bstep (se 1 (by rfl) ⟨4514291, by rfl⟩ : syracuseStep 6019055 = 9028583) B9028583
theorem B1783791 : Blo 1782092 1783791 := bstep (se 1 (by rfl) ⟨1337843, by rfl⟩ : syracuseStep 1783791 = 2675687) B2675687
theorem B4282361 : Blo 1782092 4282361 := bstep (se 2 (by rfl) ⟨1605885, by rfl⟩ : syracuseStep 4282361 = 3211771) B3211771
theorem B5077075 : Blo 1782092 5077075 := bstep (se 1 (by rfl) ⟨3807806, by rfl⟩ : syracuseStep 5077075 = 7615613) B7615613
theorem B2005087 : Blo 1782092 2005087 := bstep (se 1 (by rfl) ⟨1503815, by rfl⟩ : syracuseStep 2005087 = 3007631) B3007631
theorem B4012127 : Blo 1782092 4012127 := bstep (se 1 (by rfl) ⟨3009095, by rfl⟩ : syracuseStep 4012127 = 6018191) B6018191
theorem B1783963 : Blo 1782092 1783963 := bstep (se 1 (by rfl) ⟨1337972, by rfl⟩ : syracuseStep 1783963 = 2675945) B2675945
theorem B1783999 : Blo 1782092 1783999 := bstep (se 1 (by rfl) ⟨1337999, by rfl⟩ : syracuseStep 1783999 = 2675999) B2675999
theorem B6019271 : Blo 1782092 6019271 := bstep (se 1 (by rfl) ⟨4514453, by rfl⟩ : syracuseStep 6019271 = 9028907) B9028907
theorem B5077235 : Blo 1782092 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B12859651 : Blo 1782092 12859651 := bstep (se 1 (by rfl) ⟨9644738, by rfl⟩ : syracuseStep 12859651 = 19289477) B19289477
theorem B38566151 : Blo 1782092 38566151 := bstep (se 1 (by rfl) ⟨28924613, by rfl⟩ : syracuseStep 38566151 = 57849227) B57849227
theorem B21993769 : Blo 1782092 21993769 := bstep (se 2 (by rfl) ⟨8247663, by rfl⟩ : syracuseStep 21993769 = 16495327) B16495327
theorem B6511241 : Blo 1782092 6511241 := bstep (se 2 (by rfl) ⟨2441715, by rfl⟩ : syracuseStep 6511241 = 4883431) B4883431
theorem B6019919 : Blo 1782092 6019919 := bstep (se 1 (by rfl) ⟨4514939, by rfl⟩ : syracuseStep 6019919 = 9029879) B9029879
theorem B5421907 : Blo 1782092 5421907 := bstep (se 1 (by rfl) ⟨4066430, by rfl⟩ : syracuseStep 5421907 = 8132861) B8132861
theorem B4012883 : Blo 1782092 4012883 := bstep (se 1 (by rfl) ⟨3009662, by rfl⟩ : syracuseStep 4012883 = 6019325) B6019325
theorem B6953975 : Blo 1782092 6953975 := bstep (se 1 (by rfl) ⟨5215481, by rfl⟩ : syracuseStep 6953975 = 10430963) B10430963
theorem B12852215 : Blo 1782092 12852215 := bstep (se 1 (by rfl) ⟨9639161, by rfl⟩ : syracuseStep 12852215 = 19278323) B19278323
theorem B41720845 : Blo 1782092 41720845 := bstep (se 3 (by rfl) ⟨7822658, by rfl⟩ : syracuseStep 41720845 = 15645317) B15645317
theorem B16497703 : Blo 1782092 16497703 := bstep (se 1 (by rfl) ⟨12373277, by rfl⟩ : syracuseStep 16497703 = 24746555) B24746555
theorem B6020243 : Blo 1782092 6020243 := bstep (se 1 (by rfl) ⟨4515182, by rfl⟩ : syracuseStep 6020243 = 9030365) B9030365
theorem B6773975 : Blo 1782092 6773975 := bstep (se 1 (by rfl) ⟨5080481, by rfl⟩ : syracuseStep 6773975 = 10160963) B10160963
theorem B2006239 : Blo 1782092 2006239 := bstep (se 1 (by rfl) ⟨1504679, by rfl⟩ : syracuseStep 2006239 = 3009359) B3009359
theorem B4013423 : Blo 1782092 4013423 := bstep (se 1 (by rfl) ⟨3010067, by rfl⟩ : syracuseStep 4013423 = 6020135) B6020135
theorem B6020513 : Blo 1782092 6020513 := bstep (se 2 (by rfl) ⟨2257692, by rfl⟩ : syracuseStep 6020513 = 4515385) B4515385
theorem B5709403 : Blo 1782092 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B5422735 : Blo 1782092 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B4013711 : Blo 1782092 4013711 := bstep (se 1 (by rfl) ⟨3010283, by rfl⟩ : syracuseStep 4013711 = 6020567) B6020567
theorem B38575763 : Blo 1782092 38575763 := bstep (se 1 (by rfl) ⟨28931822, by rfl⟩ : syracuseStep 38575763 = 57863645) B57863645
theorem B4013801 : Blo 1782092 4013801 := bstep (se 2 (by rfl) ⟨1505175, by rfl⟩ : syracuseStep 4013801 = 3010351) B3010351
theorem B6021053 : Blo 1782092 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B22847453 : Blo 1782092 22847453 := bstep (se 3 (by rfl) ⟨4283897, by rfl⟩ : syracuseStep 22847453 = 8567795) B8567795
theorem B2539711 : Blo 1782092 2539711 := bstep (se 1 (by rfl) ⟨1904783, by rfl⟩ : syracuseStep 2539711 = 3809567) B3809567
theorem B4636921 : Blo 1782092 4636921 := bstep (se 2 (by rfl) ⟨1738845, by rfl⟩ : syracuseStep 4636921 = 3477691) B3477691
theorem B21684509 : Blo 1782092 21684509 := bstep (se 3 (by rfl) ⟨4065845, by rfl⟩ : syracuseStep 21684509 = 8131691) B8131691
theorem B17146201 : Blo 1782092 17146201 := bstep (se 2 (by rfl) ⟨6429825, by rfl⟩ : syracuseStep 17146201 = 12859651) B12859651
theorem B7430683 : Blo 1782092 7430683 := bstep (se 1 (by rfl) ⟨5573012, by rfl⟩ : syracuseStep 7430683 = 11146025) B11146025
theorem B6767489 : Blo 1782092 6767489 := bstep (se 2 (by rfl) ⟨2537808, by rfl⟩ : syracuseStep 6767489 = 5075617) B5075617
theorem B5710763 : Blo 1782092 5710763 := bstep (se 1 (by rfl) ⟨4283072, by rfl⟩ : syracuseStep 5710763 = 8566145) B8566145
theorem B14861303 : Blo 1782092 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B6767671 : Blo 1782092 6767671 := bstep (se 1 (by rfl) ⟨5075753, by rfl⟩ : syracuseStep 6767671 = 10151507) B10151507
theorem B3384595 : Blo 1782092 3384595 := bstep (se 1 (by rfl) ⟨2538446, by rfl⟩ : syracuseStep 3384595 = 5076893) B5076893
theorem B21996937 : Blo 1782092 21996937 := bstep (se 2 (by rfl) ⟨8248851, by rfl⟩ : syracuseStep 21996937 = 16497703) B16497703
theorem B3384823 : Blo 1782092 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B6768143 : Blo 1782092 6768143 := bstep (se 1 (by rfl) ⟨5076107, by rfl⟩ : syracuseStep 6768143 = 10152215) B10152215
theorem B7226987 : Blo 1782092 7226987 := bstep (se 1 (by rfl) ⟨5420240, by rfl⟩ : syracuseStep 7226987 = 10840481) B10840481
theorem B14452577 : Blo 1782092 14452577 := bstep (se 2 (by rfl) ⟨5419716, by rfl⟩ : syracuseStep 14452577 = 10839433) B10839433
theorem B6014951 : Blo 1782092 6014951 := bstep (se 1 (by rfl) ⟨4511213, by rfl⟩ : syracuseStep 6014951 = 9022427) B9022427
theorem B7612537 : Blo 1782092 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B4515983 : Blo 1782092 4515983 := bstep (se 1 (by rfl) ⟨3386987, by rfl⟩ : syracuseStep 4515983 = 6773975) B6773975
theorem B25717175 : Blo 1782092 25717175 := bstep (se 1 (by rfl) ⟨19287881, by rfl⟩ : syracuseStep 25717175 = 38575763) B38575763
theorem B15231635 : Blo 1782092 15231635 := bstep (se 1 (by rfl) ⟨11423726, by rfl⟩ : syracuseStep 15231635 = 22847453) B22847453
theorem B9644807 : Blo 1782092 9644807 := bstep (se 1 (by rfl) ⟨7233605, by rfl⟩ : syracuseStep 9644807 = 14467211) B14467211
theorem B6769433 : Blo 1782092 6769433 := bstep (se 2 (by rfl) ⟨2538537, by rfl⟩ : syracuseStep 6769433 = 5077075) B5077075
theorem B2673449 : Blo 1782092 2673449 := bstep (se 2 (by rfl) ⟨1002543, by rfl⟩ : syracuseStep 2673449 = 2005087) B2005087
theorem B2673659 : Blo 1782092 2673659 := bstep (se 1 (by rfl) ⟨2005244, by rfl⟩ : syracuseStep 2673659 = 4010489) B4010489
theorem B17132593 : Blo 1782092 17132593 := bstep (se 2 (by rfl) ⟨6424722, by rfl⟩ : syracuseStep 17132593 = 12849445) B12849445
theorem B2673719 : Blo 1782092 2673719 := bstep (se 1 (by rfl) ⟨2005289, by rfl⟩ : syracuseStep 2673719 = 4010579) B4010579
theorem B3386441 : Blo 1782092 3386441 := bstep (se 2 (by rfl) ⟨1269915, by rfl⟩ : syracuseStep 3386441 = 2539831) B2539831
theorem B7228559 : Blo 1782092 7228559 := bstep (se 1 (by rfl) ⟨5421419, by rfl⟩ : syracuseStep 7228559 = 10842839) B10842839
theorem B28920979 : Blo 1782092 28920979 := bstep (se 1 (by rfl) ⟨21690734, by rfl⟩ : syracuseStep 28920979 = 43381469) B43381469
theorem B2673839 : Blo 1782092 2673839 := bstep (se 1 (by rfl) ⟨2005379, by rfl⟩ : syracuseStep 2673839 = 4010759) B4010759
theorem B12201479 : Blo 1782092 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B7229209 : Blo 1782092 7229209 := bstep (se 2 (by rfl) ⟨2710953, by rfl⟩ : syracuseStep 7229209 = 5421907) B5421907
theorem B6016895 : Blo 1782092 6016895 := bstep (se 1 (by rfl) ⟨4512671, by rfl⟩ : syracuseStep 6016895 = 9025343) B9025343
theorem B2674559 : Blo 1782092 2674559 := bstep (se 1 (by rfl) ⟨2005919, by rfl⟩ : syracuseStep 2674559 = 4011839) B4011839
theorem B20320145 : Blo 1782092 20320145 := bstep (se 2 (by rfl) ⟨7620054, by rfl⟩ : syracuseStep 20320145 = 15240109) B15240109
theorem B6770587 : Blo 1782092 6770587 := bstep (se 1 (by rfl) ⟨5077940, by rfl⟩ : syracuseStep 6770587 = 10155881) B10155881
theorem B2854907 : Blo 1782092 2854907 := bstep (se 1 (by rfl) ⟨2141180, by rfl⟩ : syracuseStep 2854907 = 4282361) B4282361
theorem B55627793 : Blo 1782092 55627793 := bstep (se 2 (by rfl) ⟨20860422, by rfl⟩ : syracuseStep 55627793 = 41720845) B41720845
theorem B2674751 : Blo 1782092 2674751 := bstep (se 1 (by rfl) ⟨2006063, by rfl⟩ : syracuseStep 2674751 = 4012127) B4012127
theorem B4010057 : Blo 1782092 4010057 := bstep (se 2 (by rfl) ⟨1503771, by rfl⟩ : syracuseStep 4010057 = 3007543) B3007543
theorem B4010111 : Blo 1782092 4010111 := bstep (se 1 (by rfl) ⟨3007583, by rfl⟩ : syracuseStep 4010111 = 6015167) B6015167
theorem B25710767 : Blo 1782092 25710767 := bstep (se 1 (by rfl) ⟨19283075, by rfl⟩ : syracuseStep 25710767 = 38566151) B38566151
theorem B5075207 : Blo 1782092 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B8565011 : Blo 1782092 8565011 := bstep (se 1 (by rfl) ⟨6423758, by rfl⟩ : syracuseStep 8565011 = 12847517) B12847517
theorem B8376605 : Blo 1782092 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B2674985 : Blo 1782092 2674985 := bstep (se 2 (by rfl) ⟨1003119, by rfl⟩ : syracuseStep 2674985 = 2006239) B2006239
theorem B1782119 : Blo 1782092 1782119 := bstep (se 1 (by rfl) ⟨1336589, by rfl⟩ : syracuseStep 1782119 = 2673179) B2673179
theorem B1782171 : Blo 1782092 1782171 := bstep (se 1 (by rfl) ⟨1336628, by rfl⟩ : syracuseStep 1782171 = 2673257) B2673257
theorem B23163337 : Blo 1782092 23163337 := bstep (se 2 (by rfl) ⟨8686251, by rfl⟩ : syracuseStep 23163337 = 17372503) B17372503
theorem B2675255 : Blo 1782092 2675255 := bstep (se 1 (by rfl) ⟨2006441, by rfl⟩ : syracuseStep 2675255 = 4012883) B4012883
theorem B1782523 : Blo 1782092 1782523 := bstep (se 1 (by rfl) ⟨1336892, by rfl⟩ : syracuseStep 1782523 = 2673785) B2673785
theorem B1782591 : Blo 1782092 1782591 := bstep (se 1 (by rfl) ⟨1336943, by rfl⟩ : syracuseStep 1782591 = 2673887) B2673887
theorem B75248459 : Blo 1782092 75248459 := bstep (se 1 (by rfl) ⟨56436344, by rfl⟩ : syracuseStep 75248459 = 112872689) B112872689
theorem B1782619 : Blo 1782092 1782619 := bstep (se 1 (by rfl) ⟨1336964, by rfl⟩ : syracuseStep 1782619 = 2673929) B2673929
theorem B7230313 : Blo 1782092 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B1782687 : Blo 1782092 1782687 := bstep (se 1 (by rfl) ⟨1337015, by rfl⟩ : syracuseStep 1782687 = 2674031) B2674031
theorem B2675615 : Blo 1782092 2675615 := bstep (se 1 (by rfl) ⟨2006711, by rfl⟩ : syracuseStep 2675615 = 4013423) B4013423
theorem B1782767 : Blo 1782092 1782767 := bstep (se 1 (by rfl) ⟨1337075, by rfl⟩ : syracuseStep 1782767 = 2674151) B2674151
theorem B7615529 : Blo 1782092 7615529 := bstep (se 2 (by rfl) ⟨2855823, by rfl⟩ : syracuseStep 7615529 = 5711647) B5711647
theorem B1782855 : Blo 1782092 1782855 := bstep (se 1 (by rfl) ⟨1337141, by rfl⟩ : syracuseStep 1782855 = 2674283) B2674283
theorem B2675807 : Blo 1782092 2675807 := bstep (se 1 (by rfl) ⟨2006855, by rfl⟩ : syracuseStep 2675807 = 4013711) B4013711
theorem B1782939 : Blo 1782092 1782939 := bstep (se 1 (by rfl) ⟨1337204, by rfl⟩ : syracuseStep 1782939 = 2674409) B2674409
theorem B2675867 : Blo 1782092 2675867 := bstep (se 1 (by rfl) ⟨2006900, by rfl⟩ : syracuseStep 2675867 = 4013801) B4013801
theorem B4011191 : Blo 1782092 4011191 := bstep (se 1 (by rfl) ⟨3008393, by rfl⟩ : syracuseStep 4011191 = 6016787) B6016787
theorem B1783035 : Blo 1782092 1783035 := bstep (se 1 (by rfl) ⟨1337276, by rfl⟩ : syracuseStep 1783035 = 2674553) B2674553
theorem B26047763 : Blo 1782092 26047763 := bstep (se 1 (by rfl) ⟨19535822, by rfl⟩ : syracuseStep 26047763 = 39071645) B39071645
theorem B1783103 : Blo 1782092 1783103 := bstep (se 1 (by rfl) ⟨1337327, by rfl⟩ : syracuseStep 1783103 = 2674655) B2674655
theorem B1783271 : Blo 1782092 1783271 := bstep (se 1 (by rfl) ⟨1337453, by rfl⟩ : syracuseStep 1783271 = 2674907) B2674907
theorem B1783279 : Blo 1782092 1783279 := bstep (se 1 (by rfl) ⟨1337459, by rfl⟩ : syracuseStep 1783279 = 2674919) B2674919
theorem B1783387 : Blo 1782092 1783387 := bstep (se 1 (by rfl) ⟨1337540, by rfl⟩ : syracuseStep 1783387 = 2675081) B2675081
theorem B1783451 : Blo 1782092 1783451 := bstep (se 1 (by rfl) ⟨1337588, by rfl⟩ : syracuseStep 1783451 = 2675177) B2675177
theorem B20305565 : Blo 1782092 20305565 := bstep (se 3 (by rfl) ⟨3807293, by rfl⟩ : syracuseStep 20305565 = 7614587) B7614587
theorem B13538987 : Blo 1782092 13538987 := bstep (se 1 (by rfl) ⟨10154240, by rfl⟩ : syracuseStep 13538987 = 20308481) B20308481
theorem B29325025 : Blo 1782092 29325025 := bstep (se 2 (by rfl) ⟨10996884, by rfl⟩ : syracuseStep 29325025 = 21993769) B21993769
theorem B1783535 : Blo 1782092 1783535 := bstep (se 1 (by rfl) ⟨1337651, by rfl⟩ : syracuseStep 1783535 = 2675303) B2675303
theorem B4011767 : Blo 1782092 4011767 := bstep (se 1 (by rfl) ⟨3008825, by rfl⟩ : syracuseStep 4011767 = 6017651) B6017651
theorem B1783623 : Blo 1782092 1783623 := bstep (se 1 (by rfl) ⟨1337717, by rfl⟩ : syracuseStep 1783623 = 2675435) B2675435
theorem B35215195 : Blo 1782092 35215195 := bstep (se 1 (by rfl) ⟨26411396, by rfl⟩ : syracuseStep 35215195 = 52822793) B52822793
theorem B1783643 : Blo 1782092 1783643 := bstep (se 1 (by rfl) ⟨1337732, by rfl⟩ : syracuseStep 1783643 = 2675465) B2675465
theorem B1783711 : Blo 1782092 1783711 := bstep (se 1 (by rfl) ⟨1337783, by rfl⟩ : syracuseStep 1783711 = 2675567) B2675567
theorem B4011947 : Blo 1782092 4011947 := bstep (se 1 (by rfl) ⟨3008960, by rfl⟩ : syracuseStep 4011947 = 6017921) B6017921
theorem B12195785 : Blo 1782092 12195785 := bstep (se 2 (by rfl) ⟨4573419, by rfl⟩ : syracuseStep 12195785 = 9146839) B9146839
theorem B4012073 : Blo 1782092 4012073 := bstep (se 2 (by rfl) ⟨1504527, by rfl⟩ : syracuseStep 4012073 = 3009055) B3009055
theorem B1783879 : Blo 1782092 1783879 := bstep (se 1 (by rfl) ⟨1337909, by rfl⟩ : syracuseStep 1783879 = 2675819) B2675819
theorem B4511963 : Blo 1782092 4511963 := bstep (se 1 (by rfl) ⟨3383972, by rfl⟩ : syracuseStep 4511963 = 6767945) B6767945
theorem B1784039 : Blo 1782092 1784039 := bstep (se 1 (by rfl) ⟨1338029, by rfl⟩ : syracuseStep 1784039 = 2676059) B2676059
theorem B370563335 : Blo 1782092 370563335 := bstep (se 1 (by rfl) ⟨277922501, by rfl⟩ : syracuseStep 370563335 = 555845003) B555845003
theorem B6019487 : Blo 1782092 6019487 := bstep (se 1 (by rfl) ⟨4514615, by rfl⟩ : syracuseStep 6019487 = 9029231) B9029231
theorem B4012487 : Blo 1782092 4012487 := bstep (se 1 (by rfl) ⟨3009365, by rfl⟩ : syracuseStep 4012487 = 6018731) B6018731
theorem B11426291 : Blo 1782092 11426291 := bstep (se 1 (by rfl) ⟨8569718, by rfl⟩ : syracuseStep 11426291 = 17139437) B17139437
theorem B4012649 : Blo 1782092 4012649 := bstep (se 2 (by rfl) ⟨1504743, by rfl⟩ : syracuseStep 4012649 = 3009487) B3009487
theorem B2005663 : Blo 1782092 2005663 := bstep (se 1 (by rfl) ⟨1504247, by rfl⟩ : syracuseStep 2005663 = 3008495) B3008495
theorem B4012703 : Blo 1782092 4012703 := bstep (se 1 (by rfl) ⟨3009527, by rfl⟩ : syracuseStep 4012703 = 6019055) B6019055
theorem B4012847 : Blo 1782092 4012847 := bstep (se 1 (by rfl) ⟨3009635, by rfl⟩ : syracuseStep 4012847 = 6019271) B6019271
theorem B4340827 : Blo 1782092 4340827 := bstep (se 1 (by rfl) ⟨3255620, by rfl⟩ : syracuseStep 4340827 = 6511241) B6511241
theorem B4013279 : Blo 1782092 4013279 := bstep (se 1 (by rfl) ⟨3009959, by rfl⟩ : syracuseStep 4013279 = 6019919) B6019919
theorem B4635983 : Blo 1782092 4635983 := bstep (se 1 (by rfl) ⟨3476987, by rfl⟩ : syracuseStep 4635983 = 6953975) B6953975
theorem B8568143 : Blo 1782092 8568143 := bstep (se 1 (by rfl) ⟨6426107, by rfl⟩ : syracuseStep 8568143 = 12852215) B12852215
theorem B6020459 : Blo 1782092 6020459 := bstep (se 1 (by rfl) ⟨4515344, by rfl⟩ : syracuseStep 6020459 = 9030689) B9030689
theorem B4013495 : Blo 1782092 4013495 := bstep (se 1 (by rfl) ⟨3010121, by rfl⟩ : syracuseStep 4013495 = 6020243) B6020243
theorem B4013675 : Blo 1782092 4013675 := bstep (se 1 (by rfl) ⟨3010256, by rfl⟩ : syracuseStep 4013675 = 6020513) B6020513
theorem B2711161 : Blo 1782092 2711161 := bstep (se 2 (by rfl) ⟨1016685, by rfl⟩ : syracuseStep 2711161 = 2033371) B2033371
theorem B6020729 : Blo 1782092 6020729 := bstep (se 2 (by rfl) ⟨2257773, by rfl⟩ : syracuseStep 6020729 = 4515547) B4515547
theorem B2006815 : Blo 1782092 2006815 := bstep (se 1 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 2006815 = 3010223) B3010223
theorem B4013945 : Blo 1782092 4013945 := bstep (se 2 (by rfl) ⟨1505229, by rfl⟩ : syracuseStep 4013945 = 3010459) B3010459
theorem B9641929 : Blo 1782092 9641929 := bstep (se 2 (by rfl) ⟨3615723, by rfl⟩ : syracuseStep 9641929 = 7231447) B7231447
theorem B4014035 : Blo 1782092 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B6021107 : Blo 1782092 6021107 := bstep (se 1 (by rfl) ⟨4515830, by rfl⟩ : syracuseStep 6021107 = 9031661) B9031661
theorem B37085195 : Blo 1782092 37085195 := bstep (se 1 (by rfl) ⟨27813896, by rfl⟩ : syracuseStep 37085195 = 55627793) B55627793
theorem B10150049 : Blo 1782092 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B3383471 : Blo 1782092 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B5710007 : Blo 1782092 5710007 := bstep (se 1 (by rfl) ⟨4282505, by rfl⟩ : syracuseStep 5710007 = 8565011) B8565011
theorem B19276157 : Blo 1782092 19276157 := bstep (se 3 (by rfl) ⟨3614279, by rfl⟩ : syracuseStep 19276157 = 7228559) B7228559
theorem B30884449 : Blo 1782092 30884449 := bstep (se 2 (by rfl) ⟨11581668, by rfl⟩ : syracuseStep 30884449 = 23163337) B23163337
theorem B9635051 : Blo 1782092 9635051 := bstep (se 1 (by rfl) ⟨7226288, by rfl⟩ : syracuseStep 9635051 = 14452577) B14452577
theorem B3007975 : Blo 1782092 3007975 := bstep (se 1 (by rfl) ⟨2255981, by rfl⟩ : syracuseStep 3007975 = 4511963) B4511963
theorem B38561305 : Blo 1782092 38561305 := bstep (se 2 (by rfl) ⟨14460489, by rfl⟩ : syracuseStep 38561305 = 28920979) B28920979
theorem B29329249 : Blo 1782092 29329249 := bstep (se 2 (by rfl) ⟨10998468, by rfl⟩ : syracuseStep 29329249 = 21996937) B21996937
theorem B3614881 : Blo 1782092 3614881 := bstep (se 2 (by rfl) ⟨1355580, by rfl⟩ : syracuseStep 3614881 = 2711161) B2711161
theorem B3090655 : Blo 1782092 3090655 := bstep (se 1 (by rfl) ⟨2317991, by rfl⟩ : syracuseStep 3090655 = 4635983) B4635983
theorem B5712095 : Blo 1782092 5712095 := bstep (se 1 (by rfl) ⟨4284071, by rfl⟩ : syracuseStep 5712095 = 8568143) B8568143
theorem B4014071 : Blo 1782092 4014071 := bstep (se 1 (by rfl) ⟨3010553, by rfl⟩ : syracuseStep 4014071 = 6021107) B6021107
theorem B12855905 : Blo 1782092 12855905 := bstep (se 2 (by rfl) ⟨4820964, by rfl⟩ : syracuseStep 12855905 = 9641929) B9641929
theorem B1903271 : Blo 1782092 1903271 := bstep (se 1 (by rfl) ⟨1427453, by rfl⟩ : syracuseStep 1903271 = 2854907) B2854907
theorem B2673371 : Blo 1782092 2673371 := bstep (se 1 (by rfl) ⟨2005028, by rfl⟩ : syracuseStep 2673371 = 4010057) B4010057
theorem B2673407 : Blo 1782092 2673407 := bstep (se 1 (by rfl) ⟨2005055, by rfl⟩ : syracuseStep 2673407 = 4010111) B4010111
theorem B17140511 : Blo 1782092 17140511 := bstep (se 1 (by rfl) ⟨12855383, by rfl⟩ : syracuseStep 17140511 = 25710767) B25710767
theorem B3386281 : Blo 1782092 3386281 := bstep (se 2 (by rfl) ⟨1269855, by rfl⟩ : syracuseStep 3386281 = 2539711) B2539711
theorem B9907535 : Blo 1782092 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B9907577 : Blo 1782092 9907577 := bstep (se 2 (by rfl) ⟨3715341, by rfl⟩ : syracuseStep 9907577 = 7430683) B7430683
theorem B2674127 : Blo 1782092 2674127 := bstep (se 1 (by rfl) ⟨2005595, by rfl⟩ : syracuseStep 2674127 = 4011191) B4011191
theorem B2674217 : Blo 1782092 2674217 := bstep (se 2 (by rfl) ⟨1002831, by rfl⟩ : syracuseStep 2674217 = 2005663) B2005663
theorem B13537043 : Blo 1782092 13537043 := bstep (se 1 (by rfl) ⟨10152782, by rfl⟩ : syracuseStep 13537043 = 20305565) B20305565
theorem B2674511 : Blo 1782092 2674511 := bstep (se 1 (by rfl) ⟨2005883, by rfl⟩ : syracuseStep 2674511 = 4011767) B4011767
theorem B2674631 : Blo 1782092 2674631 := bstep (se 1 (by rfl) ⟨2005973, by rfl⟩ : syracuseStep 2674631 = 4011947) B4011947
theorem B4009967 : Blo 1782092 4009967 := bstep (se 1 (by rfl) ⟨3007475, by rfl⟩ : syracuseStep 4009967 = 6014951) B6014951
theorem B2674715 : Blo 1782092 2674715 := bstep (se 1 (by rfl) ⟨2006036, by rfl⟩ : syracuseStep 2674715 = 4012073) B4012073
theorem B22843457 : Blo 1782092 22843457 := bstep (se 2 (by rfl) ⟨8566296, by rfl⟩ : syracuseStep 22843457 = 17132593) B17132593
theorem B9023561 : Blo 1782092 9023561 := bstep (se 2 (by rfl) ⟨3383835, by rfl⟩ : syracuseStep 9023561 = 6767671) B6767671
theorem B3010655 : Blo 1782092 3010655 := bstep (se 1 (by rfl) ⟨2257991, by rfl⟩ : syracuseStep 3010655 = 4515983) B4515983
theorem B5787769 : Blo 1782092 5787769 := bstep (se 2 (by rfl) ⟨2170413, by rfl⟩ : syracuseStep 5787769 = 4340827) B4340827
theorem B247042223 : Blo 1782092 247042223 := bstep (se 1 (by rfl) ⟨185281667, by rfl⟩ : syracuseStep 247042223 = 370563335) B370563335
theorem B19271965 : Blo 1782092 19271965 := bstep (se 3 (by rfl) ⟨3613493, by rfl⟩ : syracuseStep 19271965 = 7226987) B7226987
theorem B2674991 : Blo 1782092 2674991 := bstep (se 1 (by rfl) ⟨2006243, by rfl⟩ : syracuseStep 2674991 = 4012487) B4012487
theorem B2675099 : Blo 1782092 2675099 := bstep (se 1 (by rfl) ⟨2006324, by rfl⟩ : syracuseStep 2675099 = 4012649) B4012649
theorem B10154423 : Blo 1782092 10154423 := bstep (se 1 (by rfl) ⟨7615817, by rfl⟩ : syracuseStep 10154423 = 15231635) B15231635
theorem B2675135 : Blo 1782092 2675135 := bstep (se 1 (by rfl) ⟨2006351, by rfl⟩ : syracuseStep 2675135 = 4012703) B4012703
theorem B1782299 : Blo 1782092 1782299 := bstep (se 1 (by rfl) ⟨1336724, by rfl⟩ : syracuseStep 1782299 = 2673449) B2673449
theorem B2675231 : Blo 1782092 2675231 := bstep (se 1 (by rfl) ⟨2006423, by rfl⟩ : syracuseStep 2675231 = 4012847) B4012847
theorem B1782439 : Blo 1782092 1782439 := bstep (se 1 (by rfl) ⟨1336829, by rfl⟩ : syracuseStep 1782439 = 2673659) B2673659
theorem B1782479 : Blo 1782092 1782479 := bstep (se 1 (by rfl) ⟨1336859, by rfl⟩ : syracuseStep 1782479 = 2673719) B2673719
theorem B2257627 : Blo 1782092 2257627 := bstep (se 1 (by rfl) ⟨1693220, by rfl⟩ : syracuseStep 2257627 = 3386441) B3386441
theorem B1782559 : Blo 1782092 1782559 := bstep (se 1 (by rfl) ⟨1336919, by rfl⟩ : syracuseStep 1782559 = 2673839) B2673839
theorem B2675519 : Blo 1782092 2675519 := bstep (se 1 (by rfl) ⟨2006639, by rfl⟩ : syracuseStep 2675519 = 4013279) B4013279
theorem B2675663 : Blo 1782092 2675663 := bstep (se 1 (by rfl) ⟨2006747, by rfl⟩ : syracuseStep 2675663 = 4013495) B4013495
theorem B9638945 : Blo 1782092 9638945 := bstep (se 2 (by rfl) ⟨3614604, by rfl⟩ : syracuseStep 9638945 = 7229209) B7229209
theorem B2675753 : Blo 1782092 2675753 := bstep (se 2 (by rfl) ⟨1003407, by rfl⟩ : syracuseStep 2675753 = 2006815) B2006815
theorem B2675783 : Blo 1782092 2675783 := bstep (se 1 (by rfl) ⟨2006837, by rfl⟩ : syracuseStep 2675783 = 4013675) B4013675
theorem B46953593 : Blo 1782092 46953593 := bstep (se 2 (by rfl) ⟨17607597, by rfl⟩ : syracuseStep 46953593 = 35215195) B35215195
theorem B4011263 : Blo 1782092 4011263 := bstep (se 1 (by rfl) ⟨3008447, by rfl⟩ : syracuseStep 4011263 = 6016895) B6016895
theorem B1783039 : Blo 1782092 1783039 := bstep (se 1 (by rfl) ⟨1337279, by rfl⟩ : syracuseStep 1783039 = 2674559) B2674559
theorem B2675963 : Blo 1782092 2675963 := bstep (se 1 (by rfl) ⟨2006972, by rfl⟩ : syracuseStep 2675963 = 4013945) B4013945
theorem B13546763 : Blo 1782092 13546763 := bstep (se 1 (by rfl) ⟨10160072, by rfl⟩ : syracuseStep 13546763 = 20320145) B20320145
theorem B2676023 : Blo 1782092 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B1783167 : Blo 1782092 1783167 := bstep (se 1 (by rfl) ⟨1337375, by rfl⟩ : syracuseStep 1783167 = 2674751) B2674751
theorem B14456339 : Blo 1782092 14456339 := bstep (se 1 (by rfl) ⟨10842254, by rfl⟩ : syracuseStep 14456339 = 21684509) B21684509
theorem B5584403 : Blo 1782092 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B1783323 : Blo 1782092 1783323 := bstep (se 1 (by rfl) ⟨1337492, by rfl⟩ : syracuseStep 1783323 = 2674985) B2674985
theorem B6182561 : Blo 1782092 6182561 := bstep (se 2 (by rfl) ⟨2318460, by rfl⟩ : syracuseStep 6182561 = 4636921) B4636921
theorem B1783503 : Blo 1782092 1783503 := bstep (se 1 (by rfl) ⟨1337627, by rfl⟩ : syracuseStep 1783503 = 2675255) B2675255
theorem B22861601 : Blo 1782092 22861601 := bstep (se 2 (by rfl) ⟨8573100, by rfl⟩ : syracuseStep 22861601 = 17146201) B17146201
theorem B50165639 : Blo 1782092 50165639 := bstep (se 1 (by rfl) ⟨37624229, by rfl⟩ : syracuseStep 50165639 = 75248459) B75248459
theorem B4511659 : Blo 1782092 4511659 := bstep (se 1 (by rfl) ⟨3383744, by rfl⟩ : syracuseStep 4511659 = 6767489) B6767489
theorem B1783743 : Blo 1782092 1783743 := bstep (se 1 (by rfl) ⟨1337807, by rfl⟩ : syracuseStep 1783743 = 2675615) B2675615
theorem B3807175 : Blo 1782092 3807175 := bstep (se 1 (by rfl) ⟨2855381, by rfl⟩ : syracuseStep 3807175 = 5710763) B5710763
theorem B5077019 : Blo 1782092 5077019 := bstep (se 1 (by rfl) ⟨3807764, by rfl⟩ : syracuseStep 5077019 = 7615529) B7615529
theorem B1783871 : Blo 1782092 1783871 := bstep (se 1 (by rfl) ⟨1337903, by rfl⟩ : syracuseStep 1783871 = 2675807) B2675807
theorem B1783911 : Blo 1782092 1783911 := bstep (se 1 (by rfl) ⟨1337933, by rfl⟩ : syracuseStep 1783911 = 2675867) B2675867
theorem B17365175 : Blo 1782092 17365175 := bstep (se 1 (by rfl) ⟨13023881, by rfl⟩ : syracuseStep 17365175 = 26047763) B26047763
theorem B4512095 : Blo 1782092 4512095 := bstep (se 1 (by rfl) ⟨3384071, by rfl⟩ : syracuseStep 4512095 = 6768143) B6768143
theorem B9025991 : Blo 1782092 9025991 := bstep (se 1 (by rfl) ⟨6769493, by rfl⟩ : syracuseStep 9025991 = 13538987) B13538987
theorem B9640417 : Blo 1782092 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B4012991 : Blo 1782092 4012991 := bstep (se 1 (by rfl) ⟨3009743, by rfl⟩ : syracuseStep 4012991 = 6019487) B6019487
theorem B17144783 : Blo 1782092 17144783 := bstep (se 1 (by rfl) ⟨12858587, by rfl⟩ : syracuseStep 17144783 = 25717175) B25717175
theorem B7617527 : Blo 1782092 7617527 := bstep (se 1 (by rfl) ⟨5713145, by rfl⟩ : syracuseStep 7617527 = 11426291) B11426291
theorem B4512793 : Blo 1782092 4512793 := bstep (se 2 (by rfl) ⟨1692297, by rfl⟩ : syracuseStep 4512793 = 3384595) B3384595
theorem B6429871 : Blo 1782092 6429871 := bstep (se 1 (by rfl) ⟨4822403, by rfl⟩ : syracuseStep 6429871 = 9644807) B9644807
theorem B4512955 : Blo 1782092 4512955 := bstep (se 1 (by rfl) ⟨3384716, by rfl⟩ : syracuseStep 4512955 = 6769433) B6769433
theorem B4513097 : Blo 1782092 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B4013639 : Blo 1782092 4013639 := bstep (se 1 (by rfl) ⟨3010229, by rfl⟩ : syracuseStep 4013639 = 6020459) B6020459
theorem B39100033 : Blo 1782092 39100033 := bstep (se 2 (by rfl) ⟨14662512, by rfl⟩ : syracuseStep 39100033 = 29325025) B29325025
theorem B8134319 : Blo 1782092 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B4013819 : Blo 1782092 4013819 := bstep (se 1 (by rfl) ⟨3010364, by rfl⟩ : syracuseStep 4013819 = 6020729) B6020729
theorem B32522093 : Blo 1782092 32522093 := bstep (se 3 (by rfl) ⟨6097892, by rfl⟩ : syracuseStep 32522093 = 12195785) B12195785
theorem B9027449 : Blo 1782092 9027449 := bstep (se 2 (by rfl) ⟨3385293, by rfl⟩ : syracuseStep 9027449 = 6770587) B6770587
theorem B24723463 : Blo 1782092 24723463 := bstep (se 1 (by rfl) ⟨18542597, by rfl⟩ : syracuseStep 24723463 = 37085195) B37085195
theorem B15228971 : Blo 1782092 15228971 := bstep (se 1 (by rfl) ⟨11421728, by rfl⟩ : syracuseStep 15228971 = 22843457) B22843457
theorem B2007103 : Blo 1782092 2007103 := bstep (se 1 (by rfl) ⟨1505327, by rfl⟩ : syracuseStep 2007103 = 3010655) B3010655
theorem B6766699 : Blo 1782092 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B7717025 : Blo 1782092 7717025 := bstep (se 2 (by rfl) ⟨2893884, by rfl⟩ : syracuseStep 7717025 = 5787769) B5787769
theorem B12853889 : Blo 1782092 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B31302395 : Blo 1782092 31302395 := bstep (se 1 (by rfl) ⟨23476796, by rfl⟩ : syracuseStep 31302395 = 46953593) B46953593
theorem B26420093 : Blo 1782092 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B4121707 : Blo 1782092 4121707 := bstep (se 1 (by rfl) ⟨3091280, by rfl⟩ : syracuseStep 4121707 = 6182561) B6182561
theorem B16483493 : Blo 1782092 16483493 := bstep (se 4 (by rfl) ⟨1545327, by rfl⟩ : syracuseStep 16483493 = 3090655) B3090655
theorem B4515041 : Blo 1782092 4515041 := bstep (se 2 (by rfl) ⟨1693140, by rfl⟩ : syracuseStep 4515041 = 3386281) B3386281
theorem B3384679 : Blo 1782092 3384679 := bstep (se 1 (by rfl) ⟨2538509, by rfl⟩ : syracuseStep 3384679 = 5077019) B5077019
theorem B11576783 : Blo 1782092 11576783 := bstep (se 1 (by rfl) ⟨8682587, by rfl⟩ : syracuseStep 11576783 = 17365175) B17365175
theorem B3008063 : Blo 1782092 3008063 := bstep (se 1 (by rfl) ⟨2256047, by rfl⟩ : syracuseStep 3008063 = 4512095) B4512095
theorem B8570603 : Blo 1782092 8570603 := bstep (se 1 (by rfl) ⟨6427952, by rfl⟩ : syracuseStep 8570603 = 12855905) B12855905
theorem B11429855 : Blo 1782092 11429855 := bstep (se 1 (by rfl) ⟨8572391, by rfl⟩ : syracuseStep 11429855 = 17144783) B17144783
theorem B51415073 : Blo 1782092 51415073 := bstep (se 2 (by rfl) ⟨19280652, by rfl⟩ : syracuseStep 51415073 = 38561305) B38561305
theorem B3008731 : Blo 1782092 3008731 := bstep (se 1 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 3008731 = 4513097) B4513097
theorem B6015545 : Blo 1782092 6015545 := bstep (se 2 (by rfl) ⟨2255829, by rfl⟩ : syracuseStep 6015545 = 4511659) B4511659
theorem B2673311 : Blo 1782092 2673311 := bstep (se 1 (by rfl) ⟨2004983, by rfl⟩ : syracuseStep 2673311 = 4009967) B4009967
theorem B6015707 : Blo 1782092 6015707 := bstep (se 1 (by rfl) ⟨4511780, by rfl⟩ : syracuseStep 6015707 = 9023561) B9023561
theorem B164694815 : Blo 1782092 164694815 := bstep (se 1 (by rfl) ⟨123521111, by rfl⟩ : syracuseStep 164694815 = 247042223) B247042223
theorem B4819841 : Blo 1782092 4819841 := bstep (se 2 (by rfl) ⟨1807440, by rfl⟩ : syracuseStep 4819841 = 3614881) B3614881
theorem B6769615 : Blo 1782092 6769615 := bstep (se 1 (by rfl) ⟨5077211, by rfl⟩ : syracuseStep 6769615 = 10154423) B10154423
theorem B9022589 : Blo 1782092 9022589 := bstep (se 3 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 9022589 = 3383471) B3383471
theorem B25693469 : Blo 1782092 25693469 := bstep (se 3 (by rfl) ⟨4817525, by rfl⟩ : syracuseStep 25693469 = 9635051) B9635051
theorem B6425963 : Blo 1782092 6425963 := bstep (se 1 (by rfl) ⟨4819472, by rfl⟩ : syracuseStep 6425963 = 9638945) B9638945
theorem B2674175 : Blo 1782092 2674175 := bstep (se 1 (by rfl) ⟨2005631, by rfl⟩ : syracuseStep 2674175 = 4011263) B4011263
theorem B9031175 : Blo 1782092 9031175 := bstep (se 1 (by rfl) ⟨6773381, by rfl⟩ : syracuseStep 9031175 = 13546763) B13546763
theorem B3010169 : Blo 1782092 3010169 := bstep (se 2 (by rfl) ⟨1128813, by rfl⟩ : syracuseStep 3010169 = 2257627) B2257627
theorem B9637559 : Blo 1782092 9637559 := bstep (se 1 (by rfl) ⟨7228169, by rfl⟩ : syracuseStep 9637559 = 14456339) B14456339
theorem B3722935 : Blo 1782092 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B15241067 : Blo 1782092 15241067 := bstep (se 1 (by rfl) ⟨11430800, by rfl⟩ : syracuseStep 15241067 = 22861601) B22861601
theorem B33443759 : Blo 1782092 33443759 := bstep (se 1 (by rfl) ⟨25082819, by rfl⟩ : syracuseStep 33443759 = 50165639) B50165639
theorem B6017057 : Blo 1782092 6017057 := bstep (se 2 (by rfl) ⟨2256396, by rfl⟩ : syracuseStep 6017057 = 4512793) B4512793
theorem B8573161 : Blo 1782092 8573161 := bstep (se 2 (by rfl) ⟨3214935, by rfl⟩ : syracuseStep 8573161 = 6429871) B6429871
theorem B6017273 : Blo 1782092 6017273 := bstep (se 2 (by rfl) ⟨2256477, by rfl⟩ : syracuseStep 6017273 = 4512955) B4512955
theorem B6017327 : Blo 1782092 6017327 := bstep (se 1 (by rfl) ⟨4512995, by rfl⟩ : syracuseStep 6017327 = 9025991) B9025991
theorem B5075389 : Blo 1782092 5075389 := bstep (se 3 (by rfl) ⟨951635, by rfl⟩ : syracuseStep 5075389 = 1903271) B1903271
theorem B1782247 : Blo 1782092 1782247 := bstep (se 1 (by rfl) ⟨1336685, by rfl⟩ : syracuseStep 1782247 = 2673371) B2673371
theorem B1782271 : Blo 1782092 1782271 := bstep (se 1 (by rfl) ⟨1336703, by rfl⟩ : syracuseStep 1782271 = 2673407) B2673407
theorem B2675327 : Blo 1782092 2675327 := bstep (se 1 (by rfl) ⟨2006495, by rfl⟩ : syracuseStep 2675327 = 4012991) B4012991
theorem B4010633 : Blo 1782092 4010633 := bstep (se 2 (by rfl) ⟨1503987, by rfl⟩ : syracuseStep 4010633 = 3007975) B3007975
theorem B1782751 : Blo 1782092 1782751 := bstep (se 1 (by rfl) ⟨1337063, by rfl⟩ : syracuseStep 1782751 = 2674127) B2674127
theorem B1782811 : Blo 1782092 1782811 := bstep (se 1 (by rfl) ⟨1337108, by rfl⟩ : syracuseStep 1782811 = 2674217) B2674217
theorem B2675759 : Blo 1782092 2675759 := bstep (se 1 (by rfl) ⟨2006819, by rfl⟩ : syracuseStep 2675759 = 4013639) B4013639
theorem B39105665 : Blo 1782092 39105665 := bstep (se 2 (by rfl) ⟨14664624, by rfl⟩ : syracuseStep 39105665 = 29329249) B29329249
theorem B2675879 : Blo 1782092 2675879 := bstep (se 1 (by rfl) ⟨2006909, by rfl⟩ : syracuseStep 2675879 = 4013819) B4013819
theorem B9024695 : Blo 1782092 9024695 := bstep (se 1 (by rfl) ⟨6768521, by rfl⟩ : syracuseStep 9024695 = 13537043) B13537043
theorem B1783007 : Blo 1782092 1783007 := bstep (se 1 (by rfl) ⟨1337255, by rfl⟩ : syracuseStep 1783007 = 2674511) B2674511
theorem B21681395 : Blo 1782092 21681395 := bstep (se 1 (by rfl) ⟨16261046, by rfl⟩ : syracuseStep 21681395 = 32522093) B32522093
theorem B6018299 : Blo 1782092 6018299 := bstep (se 1 (by rfl) ⟨4513724, by rfl⟩ : syracuseStep 6018299 = 9027449) B9027449
theorem B5076233 : Blo 1782092 5076233 := bstep (se 2 (by rfl) ⟨1903587, by rfl⟩ : syracuseStep 5076233 = 3807175) B3807175
theorem B1783087 : Blo 1782092 1783087 := bstep (se 1 (by rfl) ⟨1337315, by rfl⟩ : syracuseStep 1783087 = 2674631) B2674631
theorem B2676047 : Blo 1782092 2676047 := bstep (se 1 (by rfl) ⟨2007035, by rfl⟩ : syracuseStep 2676047 = 4014071) B4014071
theorem B1783143 : Blo 1782092 1783143 := bstep (se 1 (by rfl) ⟨1337357, by rfl⟩ : syracuseStep 1783143 = 2674715) B2674715
theorem B3806671 : Blo 1782092 3806671 := bstep (se 1 (by rfl) ⟨2855003, by rfl⟩ : syracuseStep 3806671 = 5710007) B5710007
theorem B1783327 : Blo 1782092 1783327 := bstep (se 1 (by rfl) ⟨1337495, by rfl⟩ : syracuseStep 1783327 = 2674991) B2674991
theorem B12850771 : Blo 1782092 12850771 := bstep (se 1 (by rfl) ⟨9638078, by rfl⟩ : syracuseStep 12850771 = 19276157) B19276157
theorem B1783399 : Blo 1782092 1783399 := bstep (se 1 (by rfl) ⟨1337549, by rfl⟩ : syracuseStep 1783399 = 2675099) B2675099
theorem B1783423 : Blo 1782092 1783423 := bstep (se 1 (by rfl) ⟨1337567, by rfl⟩ : syracuseStep 1783423 = 2675135) B2675135
theorem B1783487 : Blo 1782092 1783487 := bstep (se 1 (by rfl) ⟨1337615, by rfl⟩ : syracuseStep 1783487 = 2675231) B2675231
theorem B25695953 : Blo 1782092 25695953 := bstep (se 2 (by rfl) ⟨9635982, by rfl⟩ : syracuseStep 25695953 = 19271965) B19271965
theorem B1783679 : Blo 1782092 1783679 := bstep (se 1 (by rfl) ⟨1337759, by rfl⟩ : syracuseStep 1783679 = 2675519) B2675519
theorem B1783775 : Blo 1782092 1783775 := bstep (se 1 (by rfl) ⟨1337831, by rfl⟩ : syracuseStep 1783775 = 2675663) B2675663
theorem B1783835 : Blo 1782092 1783835 := bstep (se 1 (by rfl) ⟨1337876, by rfl⟩ : syracuseStep 1783835 = 2675753) B2675753
theorem B1783855 : Blo 1782092 1783855 := bstep (se 1 (by rfl) ⟨1337891, by rfl⟩ : syracuseStep 1783855 = 2675783) B2675783
theorem B41179265 : Blo 1782092 41179265 := bstep (se 2 (by rfl) ⟨15442224, by rfl⟩ : syracuseStep 41179265 = 30884449) B30884449
theorem B1783975 : Blo 1782092 1783975 := bstep (se 1 (by rfl) ⟨1337981, by rfl⟩ : syracuseStep 1783975 = 2675963) B2675963
theorem B1784015 : Blo 1782092 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B3808063 : Blo 1782092 3808063 := bstep (se 1 (by rfl) ⟨2856047, by rfl⟩ : syracuseStep 3808063 = 5712095) B5712095
theorem B11427007 : Blo 1782092 11427007 := bstep (se 1 (by rfl) ⟨8570255, by rfl⟩ : syracuseStep 11427007 = 17140511) B17140511
theorem B5078351 : Blo 1782092 5078351 := bstep (se 1 (by rfl) ⟨3808763, by rfl⟩ : syracuseStep 5078351 = 7617527) B7617527
theorem B52133377 : Blo 1782092 52133377 := bstep (se 2 (by rfl) ⟨19550016, by rfl⟩ : syracuseStep 52133377 = 39100033) B39100033
theorem B422723285 : Blo 1782092 422723285 := bstep (se 7 (by rfl) ⟨4953788, by rfl⟩ : syracuseStep 422723285 = 9907577) B9907577
theorem B5422879 : Blo 1782092 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B32964617 : Blo 1782092 32964617 := bstep (se 2 (by rfl) ⟨12361731, by rfl⟩ : syracuseStep 32964617 = 24723463) B24723463
theorem B5144683 : Blo 1782092 5144683 := bstep (se 1 (by rfl) ⟨3858512, by rfl⟩ : syracuseStep 5144683 = 7717025) B7717025
theorem B8569259 : Blo 1782092 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B6767185 : Blo 1782092 6767185 := bstep (se 2 (by rfl) ⟨2537694, by rfl⟩ : syracuseStep 6767185 = 5075389) B5075389
theorem B17613395 : Blo 1782092 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B3384155 : Blo 1782092 3384155 := bstep (se 1 (by rfl) ⟨2538116, by rfl⟩ : syracuseStep 3384155 = 5076233) B5076233
theorem B7717855 : Blo 1782092 7717855 := bstep (se 1 (by rfl) ⟨5788391, by rfl⟩ : syracuseStep 7717855 = 11576783) B11576783
theorem B17130635 : Blo 1782092 17130635 := bstep (se 1 (by rfl) ⟨12847976, by rfl⟩ : syracuseStep 17130635 = 25695953) B25695953
theorem B7619903 : Blo 1782092 7619903 := bstep (se 1 (by rfl) ⟨5714927, by rfl⟩ : syracuseStep 7619903 = 11429855) B11429855
theorem B34276715 : Blo 1782092 34276715 := bstep (se 1 (by rfl) ⟨25707536, by rfl⟩ : syracuseStep 34276715 = 51415073) B51415073
theorem B27452843 : Blo 1782092 27452843 := bstep (se 1 (by rfl) ⟨20589632, by rfl⟩ : syracuseStep 27452843 = 41179265) B41179265
theorem B3213227 : Blo 1782092 3213227 := bstep (se 1 (by rfl) ⟨2409920, by rfl⟩ : syracuseStep 3213227 = 4819841) B4819841
theorem B69511169 : Blo 1782092 69511169 := bstep (se 2 (by rfl) ⟨26066688, by rfl⟩ : syracuseStep 69511169 = 52133377) B52133377
theorem B6015059 : Blo 1782092 6015059 := bstep (se 1 (by rfl) ⟨4511294, by rfl⟩ : syracuseStep 6015059 = 9022589) B9022589
theorem B3385567 : Blo 1782092 3385567 := bstep (se 1 (by rfl) ⟨2539175, by rfl⟩ : syracuseStep 3385567 = 5078351) B5078351
theorem B6425039 : Blo 1782092 6425039 := bstep (se 1 (by rfl) ⟨4818779, by rfl⟩ : syracuseStep 6425039 = 9637559) B9637559
theorem B281815523 : Blo 1782092 281815523 := bstep (se 1 (by rfl) ⟨211361642, by rfl⟩ : syracuseStep 281815523 = 422723285) B422723285
theorem B10160711 : Blo 1782092 10160711 := bstep (se 1 (by rfl) ⟨7620533, by rfl⟩ : syracuseStep 10160711 = 15241067) B15241067
theorem B10152647 : Blo 1782092 10152647 := bstep (se 1 (by rfl) ⟨7614485, by rfl⟩ : syracuseStep 10152647 = 15228971) B15228971
theorem B9022265 : Blo 1782092 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B11430881 : Blo 1782092 11430881 := bstep (se 2 (by rfl) ⟨4286580, by rfl⟩ : syracuseStep 11430881 = 8573161) B8573161
theorem B2673755 : Blo 1782092 2673755 := bstep (se 1 (by rfl) ⟨2005316, by rfl⟩ : syracuseStep 2673755 = 4010633) B4010633
theorem B20868263 : Blo 1782092 20868263 := bstep (se 1 (by rfl) ⟨15651197, by rfl⟩ : syracuseStep 20868263 = 31302395) B31302395
theorem B26070443 : Blo 1782092 26070443 := bstep (se 1 (by rfl) ⟨19552832, by rfl⟩ : syracuseStep 26070443 = 39105665) B39105665
theorem B10988995 : Blo 1782092 10988995 := bstep (se 1 (by rfl) ⟨8241746, by rfl⟩ : syracuseStep 10988995 = 16483493) B16483493
theorem B6016463 : Blo 1782092 6016463 := bstep (se 1 (by rfl) ⟨4512347, by rfl⟩ : syracuseStep 6016463 = 9024695) B9024695
theorem B3010027 : Blo 1782092 3010027 := bstep (se 1 (by rfl) ⟨2257520, by rfl⟩ : syracuseStep 3010027 = 4515041) B4515041
theorem B14454263 : Blo 1782092 14454263 := bstep (se 1 (by rfl) ⟨10840697, by rfl⟩ : syracuseStep 14454263 = 21681395) B21681395
theorem B5713735 : Blo 1782092 5713735 := bstep (se 1 (by rfl) ⟨4285301, by rfl⟩ : syracuseStep 5713735 = 8570603) B8570603
theorem B4010363 : Blo 1782092 4010363 := bstep (se 1 (by rfl) ⟨3007772, by rfl⟩ : syracuseStep 4010363 = 6015545) B6015545
theorem B1782207 : Blo 1782092 1782207 := bstep (se 1 (by rfl) ⟨1336655, by rfl⟩ : syracuseStep 1782207 = 2673311) B2673311
theorem B4010471 : Blo 1782092 4010471 := bstep (se 1 (by rfl) ⟨3007853, by rfl⟩ : syracuseStep 4010471 = 6015707) B6015707
theorem B5075561 : Blo 1782092 5075561 := bstep (se 2 (by rfl) ⟨1903335, by rfl⟩ : syracuseStep 5075561 = 3806671) B3806671
theorem B17134361 : Blo 1782092 17134361 := bstep (se 2 (by rfl) ⟨6425385, by rfl⟩ : syracuseStep 17134361 = 12850771) B12850771
theorem B1782783 : Blo 1782092 1782783 := bstep (se 1 (by rfl) ⟨1337087, by rfl⟩ : syracuseStep 1782783 = 2674175) B2674175
theorem B7230505 : Blo 1782092 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B22295839 : Blo 1782092 22295839 := bstep (se 1 (by rfl) ⟨16721879, by rfl⟩ : syracuseStep 22295839 = 33443759) B33443759
theorem B4011371 : Blo 1782092 4011371 := bstep (se 1 (by rfl) ⟨3008528, by rfl⟩ : syracuseStep 4011371 = 6017057) B6017057
theorem B2676137 : Blo 1782092 2676137 := bstep (se 2 (by rfl) ⟨1003551, by rfl⟩ : syracuseStep 2676137 = 2007103) B2007103
theorem B4011515 : Blo 1782092 4011515 := bstep (se 1 (by rfl) ⟨3008636, by rfl⟩ : syracuseStep 4011515 = 6017273) B6017273
theorem B4011551 : Blo 1782092 4011551 := bstep (se 1 (by rfl) ⟨3008663, by rfl⟩ : syracuseStep 4011551 = 6017327) B6017327
theorem B4011641 : Blo 1782092 4011641 := bstep (se 2 (by rfl) ⟨1504365, by rfl⟩ : syracuseStep 4011641 = 3008731) B3008731
theorem B1783551 : Blo 1782092 1783551 := bstep (se 1 (by rfl) ⟨1337663, by rfl⟩ : syracuseStep 1783551 = 2675327) B2675327
theorem B1783839 : Blo 1782092 1783839 := bstep (se 1 (by rfl) ⟨1337879, by rfl⟩ : syracuseStep 1783839 = 2675759) B2675759
theorem B1783919 : Blo 1782092 1783919 := bstep (se 1 (by rfl) ⟨1337939, by rfl⟩ : syracuseStep 1783919 = 2675879) B2675879
theorem B4012199 : Blo 1782092 4012199 := bstep (se 1 (by rfl) ⟨3009149, by rfl⟩ : syracuseStep 4012199 = 6018299) B6018299
theorem B1784031 : Blo 1782092 1784031 := bstep (se 1 (by rfl) ⟨1338023, by rfl⟩ : syracuseStep 1784031 = 2676047) B2676047
theorem B2005375 : Blo 1782092 2005375 := bstep (se 1 (by rfl) ⟨1504031, by rfl⟩ : syracuseStep 2005375 = 3008063) B3008063
theorem B5077417 : Blo 1782092 5077417 := bstep (se 2 (by rfl) ⟨1904031, by rfl⟩ : syracuseStep 5077417 = 3808063) B3808063
theorem B9026153 : Blo 1782092 9026153 := bstep (se 2 (by rfl) ⟨3384807, by rfl⟩ : syracuseStep 9026153 = 6769615) B6769615
theorem B5495609 : Blo 1782092 5495609 := bstep (se 2 (by rfl) ⟨2060853, by rfl⟩ : syracuseStep 5495609 = 4121707) B4121707
theorem B15236009 : Blo 1782092 15236009 := bstep (se 2 (by rfl) ⟨5713503, by rfl⟩ : syracuseStep 15236009 = 11427007) B11427007
theorem B4512905 : Blo 1782092 4512905 := bstep (se 2 (by rfl) ⟨1692339, by rfl⟩ : syracuseStep 4512905 = 3384679) B3384679
theorem B109796543 : Blo 1782092 109796543 := bstep (se 1 (by rfl) ⟨82347407, by rfl⟩ : syracuseStep 109796543 = 164694815) B164694815
theorem B17128979 : Blo 1782092 17128979 := bstep (se 1 (by rfl) ⟨12846734, by rfl⟩ : syracuseStep 17128979 = 25693469) B25693469
theorem B4283975 : Blo 1782092 4283975 := bstep (se 1 (by rfl) ⟨3212981, by rfl⟩ : syracuseStep 4283975 = 6425963) B6425963
theorem B4963913 : Blo 1782092 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B6020783 : Blo 1782092 6020783 := bstep (se 1 (by rfl) ⟨4515587, by rfl⟩ : syracuseStep 6020783 = 9031175) B9031175
theorem B2006779 : Blo 1782092 2006779 := bstep (se 1 (by rfl) ⟨1505084, by rfl⟩ : syracuseStep 2006779 = 3010169) B3010169
theorem B4514089 : Blo 1782092 4514089 := bstep (se 2 (by rfl) ⟨1692783, by rfl⟩ : syracuseStep 4514089 = 3385567) B3385567
theorem B3383707 : Blo 1782092 3383707 := bstep (se 1 (by rfl) ⟨2537780, by rfl⟩ : syracuseStep 3383707 = 5075561) B5075561
theorem B11420423 : Blo 1782092 11420423 := bstep (se 1 (by rfl) ⟨8565317, by rfl⟩ : syracuseStep 11420423 = 17130635) B17130635
theorem B5079935 : Blo 1782092 5079935 := bstep (se 1 (by rfl) ⟨3809951, by rfl⟩ : syracuseStep 5079935 = 7619903) B7619903
theorem B18301895 : Blo 1782092 18301895 := bstep (se 1 (by rfl) ⟨13726421, by rfl⟩ : syracuseStep 18301895 = 27452843) B27452843
theorem B10290473 : Blo 1782092 10290473 := bstep (se 2 (by rfl) ⟨3858927, by rfl⟩ : syracuseStep 10290473 = 7717855) B7717855
theorem B187877015 : Blo 1782092 187877015 := bstep (se 1 (by rfl) ⟨140907761, by rfl⟩ : syracuseStep 187877015 = 281815523) B281815523
theorem B6768431 : Blo 1782092 6768431 := bstep (se 1 (by rfl) ⟨5076323, by rfl⟩ : syracuseStep 6768431 = 10152647) B10152647
theorem B6014843 : Blo 1782092 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B3663739 : Blo 1782092 3663739 := bstep (se 1 (by rfl) ⟨2747804, by rfl⟩ : syracuseStep 3663739 = 5495609) B5495609
theorem B7620587 : Blo 1782092 7620587 := bstep (se 1 (by rfl) ⟨5715440, by rfl⟩ : syracuseStep 7620587 = 11430881) B11430881
theorem B3008603 : Blo 1782092 3008603 := bstep (se 1 (by rfl) ⟨2256452, by rfl⟩ : syracuseStep 3008603 = 4512905) B4512905
theorem B13912175 : Blo 1782092 13912175 := bstep (se 1 (by rfl) ⟨10434131, by rfl⟩ : syracuseStep 13912175 = 20868263) B20868263
theorem B73197695 : Blo 1782092 73197695 := bstep (se 1 (by rfl) ⟨54898271, by rfl⟩ : syracuseStep 73197695 = 109796543) B109796543
theorem B9636175 : Blo 1782092 9636175 := bstep (se 1 (by rfl) ⟨7227131, by rfl⟩ : syracuseStep 9636175 = 14454263) B14454263
theorem B6859577 : Blo 1782092 6859577 := bstep (se 2 (by rfl) ⟨2572341, by rfl⟩ : syracuseStep 6859577 = 5144683) B5144683
theorem B2673575 : Blo 1782092 2673575 := bstep (se 1 (by rfl) ⟨2005181, by rfl⟩ : syracuseStep 2673575 = 4010363) B4010363
theorem B5712839 : Blo 1782092 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B2673647 : Blo 1782092 2673647 := bstep (se 1 (by rfl) ⟨2005235, by rfl⟩ : syracuseStep 2673647 = 4010471) B4010471
theorem B11742263 : Blo 1782092 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B2673833 : Blo 1782092 2673833 := bstep (se 2 (by rfl) ⟨1002687, by rfl⟩ : syracuseStep 2673833 = 2005375) B2005375
theorem B11422907 : Blo 1782092 11422907 := bstep (se 1 (by rfl) ⟨8567180, by rfl⟩ : syracuseStep 11422907 = 17134361) B17134361
theorem B6769889 : Blo 1782092 6769889 := bstep (se 2 (by rfl) ⟨2538708, by rfl⟩ : syracuseStep 6769889 = 5077417) B5077417
theorem B2256103 : Blo 1782092 2256103 := bstep (se 1 (by rfl) ⟨1692077, by rfl⟩ : syracuseStep 2256103 = 3384155) B3384155
theorem B9022913 : Blo 1782092 9022913 := bstep (se 2 (by rfl) ⟨3383592, by rfl⟩ : syracuseStep 9022913 = 6767185) B6767185
theorem B2674247 : Blo 1782092 2674247 := bstep (se 1 (by rfl) ⟨2005685, by rfl⟩ : syracuseStep 2674247 = 4011371) B4011371
theorem B22851143 : Blo 1782092 22851143 := bstep (se 1 (by rfl) ⟨17138357, by rfl⟩ : syracuseStep 22851143 = 34276715) B34276715
theorem B2674343 : Blo 1782092 2674343 := bstep (se 1 (by rfl) ⟨2005757, by rfl⟩ : syracuseStep 2674343 = 4011515) B4011515
theorem B2674367 : Blo 1782092 2674367 := bstep (se 1 (by rfl) ⟨2005775, by rfl⟩ : syracuseStep 2674367 = 4011551) B4011551
theorem B2674427 : Blo 1782092 2674427 := bstep (se 1 (by rfl) ⟨2005820, by rfl⟩ : syracuseStep 2674427 = 4011641) B4011641
theorem B17133437 : Blo 1782092 17133437 := bstep (se 3 (by rfl) ⟨3212519, by rfl⟩ : syracuseStep 17133437 = 6425039) B6425039
theorem B4010039 : Blo 1782092 4010039 := bstep (se 1 (by rfl) ⟨3007529, by rfl⟩ : syracuseStep 4010039 = 6015059) B6015059
theorem B2674799 : Blo 1782092 2674799 := bstep (se 1 (by rfl) ⟨2006099, by rfl⟩ : syracuseStep 2674799 = 4012199) B4012199
theorem B6017435 : Blo 1782092 6017435 := bstep (se 1 (by rfl) ⟨4513076, by rfl⟩ : syracuseStep 6017435 = 9026153) B9026153
theorem B14651993 : Blo 1782092 14651993 := bstep (se 2 (by rfl) ⟨5494497, by rfl⟩ : syracuseStep 14651993 = 10988995) B10988995
theorem B1782503 : Blo 1782092 1782503 := bstep (se 1 (by rfl) ⟨1336877, by rfl⟩ : syracuseStep 1782503 = 2673755) B2673755
theorem B17380295 : Blo 1782092 17380295 := bstep (se 1 (by rfl) ⟨13035221, by rfl⟩ : syracuseStep 17380295 = 26070443) B26070443
theorem B4010975 : Blo 1782092 4010975 := bstep (se 1 (by rfl) ⟨3008231, by rfl⟩ : syracuseStep 4010975 = 6016463) B6016463
theorem B2675705 : Blo 1782092 2675705 := bstep (se 2 (by rfl) ⟨1003389, by rfl⟩ : syracuseStep 2675705 = 2006779) B2006779
theorem B2855983 : Blo 1782092 2855983 := bstep (se 1 (by rfl) ⟨2141987, by rfl⟩ : syracuseStep 2855983 = 4283975) B4283975
theorem B87905645 : Blo 1782092 87905645 := bstep (se 3 (by rfl) ⟨16482308, by rfl⟩ : syracuseStep 87905645 = 32964617) B32964617
theorem B1784091 : Blo 1782092 1784091 := bstep (se 1 (by rfl) ⟨1338068, by rfl⟩ : syracuseStep 1784091 = 2676137) B2676137
theorem B46340779 : Blo 1782092 46340779 := bstep (se 1 (by rfl) ⟨34755584, by rfl⟩ : syracuseStep 46340779 = 69511169) B69511169
theorem B9640673 : Blo 1782092 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B29727785 : Blo 1782092 29727785 := bstep (se 2 (by rfl) ⟨11147919, by rfl⟩ : syracuseStep 29727785 = 22295839) B22295839
theorem B6773807 : Blo 1782092 6773807 := bstep (se 1 (by rfl) ⟨5080355, by rfl⟩ : syracuseStep 6773807 = 10160711) B10160711
theorem B10157339 : Blo 1782092 10157339 := bstep (se 1 (by rfl) ⟨7618004, by rfl⟩ : syracuseStep 10157339 = 15236009) B15236009
theorem B4013369 : Blo 1782092 4013369 := bstep (se 2 (by rfl) ⟨1505013, by rfl⟩ : syracuseStep 4013369 = 3010027) B3010027
theorem B11419319 : Blo 1782092 11419319 := bstep (se 1 (by rfl) ⟨8564489, by rfl⟩ : syracuseStep 11419319 = 17128979) B17128979
theorem B3309275 : Blo 1782092 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B7618313 : Blo 1782092 7618313 := bstep (se 2 (by rfl) ⟨2856867, by rfl⟩ : syracuseStep 7618313 = 5713735) B5713735
theorem B8568605 : Blo 1782092 8568605 := bstep (se 3 (by rfl) ⟨1606613, by rfl⟩ : syracuseStep 8568605 = 3213227) B3213227
theorem B4013855 : Blo 1782092 4013855 := bstep (se 1 (by rfl) ⟨3010391, by rfl⟩ : syracuseStep 4013855 = 6020783) B6020783
theorem B5080391 : Blo 1782092 5080391 := bstep (se 1 (by rfl) ⟨3810293, by rfl⟩ : syracuseStep 5080391 = 7620587) B7620587
theorem B9274783 : Blo 1782092 9274783 := bstep (se 1 (by rfl) ⟨6956087, by rfl⟩ : syracuseStep 9274783 = 13912175) B13912175
theorem B3008137 : Blo 1782092 3008137 := bstep (se 2 (by rfl) ⟨1128051, by rfl⟩ : syracuseStep 3008137 = 2256103) B2256103
theorem B8824733 : Blo 1782092 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B19818523 : Blo 1782092 19818523 := bstep (se 1 (by rfl) ⟨14863892, by rfl⟩ : syracuseStep 19818523 = 29727785) B29727785
theorem B4515871 : Blo 1782092 4515871 := bstep (se 1 (by rfl) ⟨3386903, by rfl⟩ : syracuseStep 4515871 = 6773807) B6773807
theorem B6015275 : Blo 1782092 6015275 := bstep (se 1 (by rfl) ⟨4511456, by rfl⟩ : syracuseStep 6015275 = 9022913) B9022913
theorem B7612879 : Blo 1782092 7612879 := bstep (se 1 (by rfl) ⟨5709659, by rfl⟩ : syracuseStep 7612879 = 11419319) B11419319
theorem B4884985 : Blo 1782092 4884985 := bstep (se 2 (by rfl) ⟨1831869, by rfl⟩ : syracuseStep 4884985 = 3663739) B3663739
theorem B5712403 : Blo 1782092 5712403 := bstep (se 1 (by rfl) ⟨4284302, by rfl⟩ : syracuseStep 5712403 = 8568605) B8568605
theorem B11422291 : Blo 1782092 11422291 := bstep (se 1 (by rfl) ⟨8566718, by rfl⟩ : syracuseStep 11422291 = 17133437) B17133437
theorem B2673359 : Blo 1782092 2673359 := bstep (se 1 (by rfl) ⟨2005019, by rfl⟩ : syracuseStep 2673359 = 4010039) B4010039
theorem B9767995 : Blo 1782092 9767995 := bstep (se 1 (by rfl) ⟨7325996, by rfl⟩ : syracuseStep 9767995 = 14651993) B14651993
theorem B12848233 : Blo 1782092 12848233 := bstep (se 2 (by rfl) ⟨4818087, by rfl⟩ : syracuseStep 12848233 = 9636175) B9636175
theorem B7613615 : Blo 1782092 7613615 := bstep (se 1 (by rfl) ⟨5710211, by rfl⟩ : syracuseStep 7613615 = 11420423) B11420423
theorem B3386623 : Blo 1782092 3386623 := bstep (se 1 (by rfl) ⟨2539967, by rfl⟩ : syracuseStep 3386623 = 5079935) B5079935
theorem B12201263 : Blo 1782092 12201263 := bstep (se 1 (by rfl) ⟨9150947, by rfl⟩ : syracuseStep 12201263 = 18301895) B18301895
theorem B11586863 : Blo 1782092 11586863 := bstep (se 1 (by rfl) ⟨8690147, by rfl⟩ : syracuseStep 11586863 = 17380295) B17380295
theorem B2673983 : Blo 1782092 2673983 := bstep (se 1 (by rfl) ⟨2005487, by rfl⟩ : syracuseStep 2673983 = 4010975) B4010975
theorem B6860315 : Blo 1782092 6860315 := bstep (se 1 (by rfl) ⟨5145236, by rfl⟩ : syracuseStep 6860315 = 10290473) B10290473
theorem B61787705 : Blo 1782092 61787705 := bstep (se 2 (by rfl) ⟨23170389, by rfl⟩ : syracuseStep 61787705 = 46340779) B46340779
theorem B125251343 : Blo 1782092 125251343 := bstep (se 1 (by rfl) ⟨93938507, by rfl⟩ : syracuseStep 125251343 = 187877015) B187877015
theorem B4009895 : Blo 1782092 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B6427115 : Blo 1782092 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B1782383 : Blo 1782092 1782383 := bstep (se 1 (by rfl) ⟨1336787, by rfl⟩ : syracuseStep 1782383 = 2673575) B2673575
theorem B1782431 : Blo 1782092 1782431 := bstep (se 1 (by rfl) ⟨1336823, by rfl⟩ : syracuseStep 1782431 = 2673647) B2673647
theorem B7828175 : Blo 1782092 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B1782555 : Blo 1782092 1782555 := bstep (se 1 (by rfl) ⟨1336916, by rfl⟩ : syracuseStep 1782555 = 2673833) B2673833
theorem B7615271 : Blo 1782092 7615271 := bstep (se 1 (by rfl) ⟨5711453, by rfl⟩ : syracuseStep 7615271 = 11422907) B11422907
theorem B6771559 : Blo 1782092 6771559 := bstep (se 1 (by rfl) ⟨5078669, by rfl⟩ : syracuseStep 6771559 = 10157339) B10157339
theorem B2675579 : Blo 1782092 2675579 := bstep (se 1 (by rfl) ⟨2006684, by rfl⟩ : syracuseStep 2675579 = 4013369) B4013369
theorem B1782831 : Blo 1782092 1782831 := bstep (se 1 (by rfl) ⟨1337123, by rfl⟩ : syracuseStep 1782831 = 2674247) B2674247
theorem B15234095 : Blo 1782092 15234095 := bstep (se 1 (by rfl) ⟨11425571, by rfl⟩ : syracuseStep 15234095 = 22851143) B22851143
theorem B1782895 : Blo 1782092 1782895 := bstep (se 1 (by rfl) ⟨1337171, by rfl⟩ : syracuseStep 1782895 = 2674343) B2674343
theorem B1782911 : Blo 1782092 1782911 := bstep (se 1 (by rfl) ⟨1337183, by rfl⟩ : syracuseStep 1782911 = 2674367) B2674367
theorem B1782951 : Blo 1782092 1782951 := bstep (se 1 (by rfl) ⟨1337213, by rfl⟩ : syracuseStep 1782951 = 2674427) B2674427
theorem B2675903 : Blo 1782092 2675903 := bstep (se 1 (by rfl) ⟨2006927, by rfl⟩ : syracuseStep 2675903 = 4013855) B4013855
theorem B1783199 : Blo 1782092 1783199 := bstep (se 1 (by rfl) ⟨1337399, by rfl⟩ : syracuseStep 1783199 = 2674799) B2674799
theorem B4011623 : Blo 1782092 4011623 := bstep (se 1 (by rfl) ⟨3008717, by rfl⟩ : syracuseStep 4011623 = 6017435) B6017435
theorem B6018785 : Blo 1782092 6018785 := bstep (se 2 (by rfl) ⟨2257044, by rfl⟩ : syracuseStep 6018785 = 4514089) B4514089
theorem B4511609 : Blo 1782092 4511609 := bstep (se 2 (by rfl) ⟨1691853, by rfl⟩ : syracuseStep 4511609 = 3383707) B3383707
theorem B1783803 : Blo 1782092 1783803 := bstep (se 1 (by rfl) ⟨1337852, by rfl⟩ : syracuseStep 1783803 = 2675705) B2675705
theorem B58603763 : Blo 1782092 58603763 := bstep (se 1 (by rfl) ⟨43952822, by rfl⟩ : syracuseStep 58603763 = 87905645) B87905645
theorem B4512287 : Blo 1782092 4512287 := bstep (se 1 (by rfl) ⟨3384215, by rfl⟩ : syracuseStep 4512287 = 6768431) B6768431
theorem B2005735 : Blo 1782092 2005735 := bstep (se 1 (by rfl) ⟨1504301, by rfl⟩ : syracuseStep 2005735 = 3008603) B3008603
theorem B3807977 : Blo 1782092 3807977 := bstep (se 2 (by rfl) ⟨1427991, by rfl⟩ : syracuseStep 3807977 = 2855983) B2855983
theorem B48798463 : Blo 1782092 48798463 := bstep (se 1 (by rfl) ⟨36598847, by rfl⟩ : syracuseStep 48798463 = 73197695) B73197695
theorem B3808559 : Blo 1782092 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B4513259 : Blo 1782092 4513259 := bstep (se 1 (by rfl) ⟨3384944, by rfl⟩ : syracuseStep 4513259 = 6769889) B6769889
theorem B18292205 : Blo 1782092 18292205 := bstep (se 3 (by rfl) ⟨3429788, by rfl⟩ : syracuseStep 18292205 = 6859577) B6859577
theorem B5078875 : Blo 1782092 5078875 := bstep (se 1 (by rfl) ⟨3809156, by rfl⟩ : syracuseStep 5078875 = 7618313) B7618313
theorem B6021161 : Blo 1782092 6021161 := bstep (se 2 (by rfl) ⟨2257935, by rfl⟩ : syracuseStep 6021161 = 4515871) B4515871
theorem B4284743 : Blo 1782092 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B10150505 : Blo 1782092 10150505 := bstep (se 2 (by rfl) ⟨3806439, by rfl⟩ : syracuseStep 10150505 = 7612879) B7612879
theorem B15229721 : Blo 1782092 15229721 := bstep (se 2 (by rfl) ⟨5711145, by rfl⟩ : syracuseStep 15229721 = 11422291) B11422291
theorem B9028745 : Blo 1782092 9028745 := bstep (se 2 (by rfl) ⟨3385779, by rfl⟩ : syracuseStep 9028745 = 6771559) B6771559
theorem B3007739 : Blo 1782092 3007739 := bstep (se 1 (by rfl) ⟨2255804, by rfl⟩ : syracuseStep 3007739 = 4511609) B4511609
theorem B5883155 : Blo 1782092 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B17130977 : Blo 1782092 17130977 := bstep (se 2 (by rfl) ⟨6424116, by rfl⟩ : syracuseStep 17130977 = 12848233) B12848233
theorem B164767213 : Blo 1782092 164767213 := bstep (se 3 (by rfl) ⟨30893852, by rfl⟩ : syracuseStep 164767213 = 61787705) B61787705
theorem B4515497 : Blo 1782092 4515497 := bstep (se 2 (by rfl) ⟨1693311, by rfl⟩ : syracuseStep 4515497 = 3386623) B3386623
theorem B3008191 : Blo 1782092 3008191 := bstep (se 1 (by rfl) ⟨2256143, by rfl⟩ : syracuseStep 3008191 = 4512287) B4512287
theorem B20875133 : Blo 1782092 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B3008839 : Blo 1782092 3008839 := bstep (se 1 (by rfl) ⟨2256629, by rfl⟩ : syracuseStep 3008839 = 4513259) B4513259
theorem B4573543 : Blo 1782092 4573543 := bstep (se 1 (by rfl) ⟨3430157, by rfl⟩ : syracuseStep 4573543 = 6860315) B6860315
theorem B2673263 : Blo 1782092 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B26053253 : Blo 1782092 26053253 := bstep (se 4 (by rfl) ⟨2442492, by rfl⟩ : syracuseStep 26053253 = 4884985) B4884985
theorem B52095973 : Blo 1782092 52095973 := bstep (se 4 (by rfl) ⟨4883997, by rfl⟩ : syracuseStep 52095973 = 9767995) B9767995
theorem B3386927 : Blo 1782092 3386927 := bstep (se 1 (by rfl) ⟨2540195, by rfl⟩ : syracuseStep 3386927 = 5080391) B5080391
theorem B2674313 : Blo 1782092 2674313 := bstep (se 2 (by rfl) ⟨1002867, by rfl⟩ : syracuseStep 2674313 = 2005735) B2005735
theorem B65064617 : Blo 1782092 65064617 := bstep (se 2 (by rfl) ⟨24399231, by rfl⟩ : syracuseStep 65064617 = 48798463) B48798463
theorem B2674415 : Blo 1782092 2674415 := bstep (se 1 (by rfl) ⟨2005811, by rfl⟩ : syracuseStep 2674415 = 4011623) B4011623
theorem B4010183 : Blo 1782092 4010183 := bstep (se 1 (by rfl) ⟨3007637, by rfl⟩ : syracuseStep 4010183 = 6015275) B6015275
theorem B1782239 : Blo 1782092 1782239 := bstep (se 1 (by rfl) ⟨1336679, by rfl⟩ : syracuseStep 1782239 = 2673359) B2673359
theorem B12366377 : Blo 1782092 12366377 := bstep (se 2 (by rfl) ⟨4637391, by rfl⟩ : syracuseStep 12366377 = 9274783) B9274783
theorem B10154605 : Blo 1782092 10154605 := bstep (se 3 (by rfl) ⟨1903988, by rfl⟩ : syracuseStep 10154605 = 3807977) B3807977
theorem B5075743 : Blo 1782092 5075743 := bstep (se 1 (by rfl) ⟨3806807, by rfl⟩ : syracuseStep 5075743 = 7613615) B7613615
theorem B4010849 : Blo 1782092 4010849 := bstep (se 2 (by rfl) ⟨1504068, by rfl⟩ : syracuseStep 4010849 = 3008137) B3008137
theorem B1782655 : Blo 1782092 1782655 := bstep (se 1 (by rfl) ⟨1336991, by rfl⟩ : syracuseStep 1782655 = 2673983) B2673983
theorem B12194803 : Blo 1782092 12194803 := bstep (se 1 (by rfl) ⟨9146102, by rfl⟩ : syracuseStep 12194803 = 18292205) B18292205
theorem B6771833 : Blo 1782092 6771833 := bstep (se 2 (by rfl) ⟨2539437, by rfl⟩ : syracuseStep 6771833 = 5078875) B5078875
theorem B105698789 : Blo 1782092 105698789 := bstep (se 4 (by rfl) ⟨9909261, by rfl⟩ : syracuseStep 105698789 = 19818523) B19818523
theorem B5076847 : Blo 1782092 5076847 := bstep (se 1 (by rfl) ⟨3807635, by rfl⟩ : syracuseStep 5076847 = 7615271) B7615271
theorem B1783719 : Blo 1782092 1783719 := bstep (se 1 (by rfl) ⟨1337789, by rfl⟩ : syracuseStep 1783719 = 2675579) B2675579
theorem B156276701 : Blo 1782092 156276701 := bstep (se 3 (by rfl) ⟨29301881, by rfl⟩ : syracuseStep 156276701 = 58603763) B58603763
theorem B7616537 : Blo 1782092 7616537 := bstep (se 2 (by rfl) ⟨2856201, by rfl⟩ : syracuseStep 7616537 = 5712403) B5712403
theorem B10156063 : Blo 1782092 10156063 := bstep (se 1 (by rfl) ⟨7617047, by rfl⟩ : syracuseStep 10156063 = 15234095) B15234095
theorem B1783935 : Blo 1782092 1783935 := bstep (se 1 (by rfl) ⟨1337951, by rfl⟩ : syracuseStep 1783935 = 2675903) B2675903
theorem B4012523 : Blo 1782092 4012523 := bstep (se 1 (by rfl) ⟨3009392, by rfl⟩ : syracuseStep 4012523 = 6018785) B6018785
theorem B2539039 : Blo 1782092 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B8134175 : Blo 1782092 8134175 := bstep (se 1 (by rfl) ⟨6100631, by rfl⟩ : syracuseStep 8134175 = 12201263) B12201263
theorem B7724575 : Blo 1782092 7724575 := bstep (se 1 (by rfl) ⟨5793431, by rfl⟩ : syracuseStep 7724575 = 11586863) B11586863
theorem B83500895 : Blo 1782092 83500895 := bstep (se 1 (by rfl) ⟨62625671, by rfl⟩ : syracuseStep 83500895 = 125251343) B125251343
theorem B4014107 : Blo 1782092 4014107 := bstep (se 1 (by rfl) ⟨3010580, by rfl⟩ : syracuseStep 4014107 = 6021161) B6021161
theorem B13541417 : Blo 1782092 13541417 := bstep (se 2 (by rfl) ⟨5078031, by rfl⟩ : syracuseStep 13541417 = 10156063) B10156063
theorem B6767003 : Blo 1782092 6767003 := bstep (se 1 (by rfl) ⟨5075252, by rfl⟩ : syracuseStep 6767003 = 10150505) B10150505
theorem B45703925 : Blo 1782092 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B4514555 : Blo 1782092 4514555 := bstep (se 1 (by rfl) ⟨3385916, by rfl⟩ : syracuseStep 4514555 = 6771833) B6771833
theorem B11420651 : Blo 1782092 11420651 := bstep (se 1 (by rfl) ⟨8565488, by rfl⟩ : syracuseStep 11420651 = 17130977) B17130977
theorem B6767657 : Blo 1782092 6767657 := bstep (se 2 (by rfl) ⟨2537871, by rfl⟩ : syracuseStep 6767657 = 5075743) B5075743
theorem B69461297 : Blo 1782092 69461297 := bstep (se 2 (by rfl) ⟨26047986, by rfl⟩ : syracuseStep 69461297 = 52095973) B52095973
theorem B17368835 : Blo 1782092 17368835 := bstep (se 1 (by rfl) ⟨13026626, by rfl⟩ : syracuseStep 17368835 = 26053253) B26053253
theorem B3385385 : Blo 1782092 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B10299433 : Blo 1782092 10299433 := bstep (se 2 (by rfl) ⟨3862287, by rfl⟩ : syracuseStep 10299433 = 7724575) B7724575
theorem B6769129 : Blo 1782092 6769129 := bstep (se 2 (by rfl) ⟨2538423, by rfl⟩ : syracuseStep 6769129 = 5076847) B5076847
theorem B55667263 : Blo 1782092 55667263 := bstep (se 1 (by rfl) ⟨41750447, by rfl⟩ : syracuseStep 55667263 = 83500895) B83500895
theorem B2673455 : Blo 1782092 2673455 := bstep (se 1 (by rfl) ⟨2005091, by rfl⟩ : syracuseStep 2673455 = 4010183) B4010183
theorem B8244251 : Blo 1782092 8244251 := bstep (se 1 (by rfl) ⟨6183188, by rfl⟩ : syracuseStep 8244251 = 12366377) B12366377
theorem B6098057 : Blo 1782092 6098057 := bstep (se 2 (by rfl) ⟨2286771, by rfl⟩ : syracuseStep 6098057 = 4573543) B4573543
theorem B10153147 : Blo 1782092 10153147 := bstep (se 1 (by rfl) ⟨7614860, by rfl⟩ : syracuseStep 10153147 = 15229721) B15229721
theorem B2673899 : Blo 1782092 2673899 := bstep (se 1 (by rfl) ⟨2005424, by rfl⟩ : syracuseStep 2673899 = 4010849) B4010849
theorem B3010331 : Blo 1782092 3010331 := bstep (se 1 (by rfl) ⟨2257748, by rfl⟩ : syracuseStep 3010331 = 4515497) B4515497
theorem B2675015 : Blo 1782092 2675015 := bstep (se 1 (by rfl) ⟨2006261, by rfl⟩ : syracuseStep 2675015 = 4012523) B4012523
theorem B1782175 : Blo 1782092 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B219689617 : Blo 1782092 219689617 := bstep (se 2 (by rfl) ⟨82383606, by rfl⟩ : syracuseStep 219689617 = 164767213) B164767213
theorem B4010921 : Blo 1782092 4010921 := bstep (se 2 (by rfl) ⟨1504095, by rfl⟩ : syracuseStep 4010921 = 3008191) B3008191
theorem B2257951 : Blo 1782092 2257951 := bstep (se 1 (by rfl) ⟨1693463, by rfl⟩ : syracuseStep 2257951 = 3386927) B3386927
theorem B1782875 : Blo 1782092 1782875 := bstep (se 1 (by rfl) ⟨1337156, by rfl⟩ : syracuseStep 1782875 = 2674313) B2674313
theorem B1782943 : Blo 1782092 1782943 := bstep (se 1 (by rfl) ⟨1337207, by rfl⟩ : syracuseStep 1782943 = 2674415) B2674415
theorem B4011785 : Blo 1782092 4011785 := bstep (se 2 (by rfl) ⟨1504419, by rfl⟩ : syracuseStep 4011785 = 3008839) B3008839
theorem B6019163 : Blo 1782092 6019163 := bstep (se 1 (by rfl) ⟨4514372, by rfl⟩ : syracuseStep 6019163 = 9028745) B9028745
theorem B13539473 : Blo 1782092 13539473 := bstep (se 2 (by rfl) ⟨5077302, by rfl⟩ : syracuseStep 13539473 = 10154605) B10154605
theorem B2005159 : Blo 1782092 2005159 := bstep (se 1 (by rfl) ⟨1503869, by rfl⟩ : syracuseStep 2005159 = 3007739) B3007739
theorem B3922103 : Blo 1782092 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B70465859 : Blo 1782092 70465859 := bstep (se 1 (by rfl) ⟨52849394, by rfl⟩ : syracuseStep 70465859 = 105698789) B105698789
theorem B13916755 : Blo 1782092 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B104184467 : Blo 1782092 104184467 := bstep (se 1 (by rfl) ⟨78138350, by rfl⟩ : syracuseStep 104184467 = 156276701) B156276701
theorem B16259737 : Blo 1782092 16259737 := bstep (se 2 (by rfl) ⟨6097401, by rfl⟩ : syracuseStep 16259737 = 12194803) B12194803
theorem B5077691 : Blo 1782092 5077691 := bstep (se 1 (by rfl) ⟨3808268, by rfl⟩ : syracuseStep 5077691 = 7616537) B7616537
theorem B5422783 : Blo 1782092 5422783 := bstep (se 1 (by rfl) ⟨4067087, by rfl⟩ : syracuseStep 5422783 = 8134175) B8134175
theorem B43376411 : Blo 1782092 43376411 := bstep (se 1 (by rfl) ⟨32532308, by rfl⟩ : syracuseStep 43376411 = 65064617) B65064617
theorem B9027611 : Blo 1782092 9027611 := bstep (se 1 (by rfl) ⟨6770708, by rfl⟩ : syracuseStep 9027611 = 13541417) B13541417
theorem B18555673 : Blo 1782092 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B2614735 : Blo 1782092 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B3385127 : Blo 1782092 3385127 := bstep (se 1 (by rfl) ⟨2538845, by rfl⟩ : syracuseStep 3385127 = 5077691) B5077691
theorem B4065371 : Blo 1782092 4065371 := bstep (se 1 (by rfl) ⟨3049028, by rfl⟩ : syracuseStep 4065371 = 6098057) B6098057
theorem B13732577 : Blo 1782092 13732577 := bstep (se 2 (by rfl) ⟨5149716, by rfl⟩ : syracuseStep 13732577 = 10299433) B10299433
theorem B2673545 : Blo 1782092 2673545 := bstep (se 2 (by rfl) ⟨1002579, by rfl⟩ : syracuseStep 2673545 = 2005159) B2005159
theorem B30469283 : Blo 1782092 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B3009703 : Blo 1782092 3009703 := bstep (se 1 (by rfl) ⟨2257277, by rfl⟩ : syracuseStep 3009703 = 4514555) B4514555
theorem B2673947 : Blo 1782092 2673947 := bstep (se 1 (by rfl) ⟨2005460, by rfl⟩ : syracuseStep 2673947 = 4010921) B4010921
theorem B7613767 : Blo 1782092 7613767 := bstep (se 1 (by rfl) ⟨5710325, by rfl⟩ : syracuseStep 7613767 = 11420651) B11420651
theorem B74223017 : Blo 1782092 74223017 := bstep (se 2 (by rfl) ⟨27833631, by rfl⟩ : syracuseStep 74223017 = 55667263) B55667263
theorem B21679649 : Blo 1782092 21679649 := bstep (se 2 (by rfl) ⟨8129868, by rfl⟩ : syracuseStep 21679649 = 16259737) B16259737
theorem B2674523 : Blo 1782092 2674523 := bstep (se 1 (by rfl) ⟨2005892, by rfl⟩ : syracuseStep 2674523 = 4011785) B4011785
theorem B2256923 : Blo 1782092 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B3010601 : Blo 1782092 3010601 := bstep (se 2 (by rfl) ⟨1128975, by rfl⟩ : syracuseStep 3010601 = 2257951) B2257951
theorem B46977239 : Blo 1782092 46977239 := bstep (se 1 (by rfl) ⟨35232929, by rfl⟩ : syracuseStep 46977239 = 70465859) B70465859
theorem B13537529 : Blo 1782092 13537529 := bstep (se 2 (by rfl) ⟨5076573, by rfl⟩ : syracuseStep 13537529 = 10153147) B10153147
theorem B69456311 : Blo 1782092 69456311 := bstep (se 1 (by rfl) ⟨52092233, by rfl⟩ : syracuseStep 69456311 = 104184467) B104184467
theorem B1782303 : Blo 1782092 1782303 := bstep (se 1 (by rfl) ⟨1336727, by rfl⟩ : syracuseStep 1782303 = 2673455) B2673455
theorem B1782599 : Blo 1782092 1782599 := bstep (se 1 (by rfl) ⟨1336949, by rfl⟩ : syracuseStep 1782599 = 2673899) B2673899
theorem B7230377 : Blo 1782092 7230377 := bstep (se 2 (by rfl) ⟨2711391, by rfl⟩ : syracuseStep 7230377 = 5422783) B5422783
theorem B2676071 : Blo 1782092 2676071 := bstep (se 1 (by rfl) ⟨2007053, by rfl⟩ : syracuseStep 2676071 = 4014107) B4014107
theorem B185267573 : Blo 1782092 185267573 := bstep (se 5 (by rfl) ⟨8684417, by rfl⟩ : syracuseStep 185267573 = 17368835) B17368835
theorem B1783343 : Blo 1782092 1783343 := bstep (se 1 (by rfl) ⟨1337507, by rfl⟩ : syracuseStep 1783343 = 2675015) B2675015
theorem B4511335 : Blo 1782092 4511335 := bstep (se 1 (by rfl) ⟨3383501, by rfl⟩ : syracuseStep 4511335 = 6767003) B6767003
theorem B9025505 : Blo 1782092 9025505 := bstep (se 2 (by rfl) ⟨3384564, by rfl⟩ : syracuseStep 9025505 = 6769129) B6769129
theorem B4511771 : Blo 1782092 4511771 := bstep (se 1 (by rfl) ⟨3383828, by rfl⟩ : syracuseStep 4511771 = 6767657) B6767657
theorem B292919489 : Blo 1782092 292919489 := bstep (se 2 (by rfl) ⟨109844808, by rfl⟩ : syracuseStep 292919489 = 219689617) B219689617
theorem B46307531 : Blo 1782092 46307531 := bstep (se 1 (by rfl) ⟨34730648, by rfl⟩ : syracuseStep 46307531 = 69461297) B69461297
theorem B4012775 : Blo 1782092 4012775 := bstep (se 1 (by rfl) ⟨3009581, by rfl⟩ : syracuseStep 4012775 = 6019163) B6019163
theorem B9026315 : Blo 1782092 9026315 := bstep (se 1 (by rfl) ⟨6769736, by rfl⟩ : syracuseStep 9026315 = 13539473) B13539473
theorem B5496167 : Blo 1782092 5496167 := bstep (se 1 (by rfl) ⟨4122125, by rfl⟩ : syracuseStep 5496167 = 8244251) B8244251
theorem B115670429 : Blo 1782092 115670429 := bstep (se 3 (by rfl) ⟨21688205, by rfl⟩ : syracuseStep 115670429 = 43376411) B43376411
theorem B2006887 : Blo 1782092 2006887 := bstep (se 1 (by rfl) ⟨1505165, by rfl⟩ : syracuseStep 2006887 = 3010331) B3010331
theorem B2007067 : Blo 1782092 2007067 := bstep (se 1 (by rfl) ⟨1505300, by rfl⟩ : syracuseStep 2007067 = 3010601) B3010601
theorem B31318159 : Blo 1782092 31318159 := bstep (se 1 (by rfl) ⟨23488619, by rfl⟩ : syracuseStep 31318159 = 46977239) B46977239
theorem B123511715 : Blo 1782092 123511715 := bstep (se 1 (by rfl) ⟨92633786, by rfl⟩ : syracuseStep 123511715 = 185267573) B185267573
theorem B24740897 : Blo 1782092 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B3007847 : Blo 1782092 3007847 := bstep (se 1 (by rfl) ⟨2255885, by rfl⟩ : syracuseStep 3007847 = 4511771) B4511771
theorem B10151689 : Blo 1782092 10151689 := bstep (se 2 (by rfl) ⟨3806883, by rfl⟩ : syracuseStep 10151689 = 7613767) B7613767
theorem B6015113 : Blo 1782092 6015113 := bstep (se 2 (by rfl) ⟨2255667, by rfl⟩ : syracuseStep 6015113 = 4511335) B4511335
theorem B3664111 : Blo 1782092 3664111 := bstep (se 1 (by rfl) ⟨2748083, by rfl⟩ : syracuseStep 3664111 = 5496167) B5496167
theorem B77113619 : Blo 1782092 77113619 := bstep (se 1 (by rfl) ⟨57835214, by rfl⟩ : syracuseStep 77113619 = 115670429) B115670429
theorem B49482011 : Blo 1782092 49482011 := bstep (se 1 (by rfl) ⟨37111508, by rfl⟩ : syracuseStep 49482011 = 74223017) B74223017
theorem B14453099 : Blo 1782092 14453099 := bstep (se 1 (by rfl) ⟨10839824, by rfl⟩ : syracuseStep 14453099 = 21679649) B21679649
theorem B46304207 : Blo 1782092 46304207 := bstep (se 1 (by rfl) ⟨34728155, by rfl⟩ : syracuseStep 46304207 = 69456311) B69456311
theorem B4820251 : Blo 1782092 4820251 := bstep (se 1 (by rfl) ⟨3615188, by rfl⟩ : syracuseStep 4820251 = 7230377) B7230377
theorem B43363957 : Blo 1782092 43363957 := bstep (se 5 (by rfl) ⟨2032685, by rfl⟩ : syracuseStep 43363957 = 4065371) B4065371
theorem B2256751 : Blo 1782092 2256751 := bstep (se 1 (by rfl) ⟨1692563, by rfl⟩ : syracuseStep 2256751 = 3385127) B3385127
theorem B6017003 : Blo 1782092 6017003 := bstep (se 1 (by rfl) ⟨4512752, by rfl⟩ : syracuseStep 6017003 = 9025505) B9025505
theorem B30871687 : Blo 1782092 30871687 := bstep (se 1 (by rfl) ⟨23153765, by rfl⟩ : syracuseStep 30871687 = 46307531) B46307531
theorem B9155051 : Blo 1782092 9155051 := bstep (se 1 (by rfl) ⟨6866288, by rfl⟩ : syracuseStep 9155051 = 13732577) B13732577
theorem B2675183 : Blo 1782092 2675183 := bstep (se 1 (by rfl) ⟨2006387, by rfl⟩ : syracuseStep 2675183 = 4012775) B4012775
theorem B6017543 : Blo 1782092 6017543 := bstep (se 1 (by rfl) ⟨4513157, by rfl⟩ : syracuseStep 6017543 = 9026315) B9026315
theorem B1782363 : Blo 1782092 1782363 := bstep (se 1 (by rfl) ⟨1336772, by rfl⟩ : syracuseStep 1782363 = 2673545) B2673545
theorem B3486313 : Blo 1782092 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B20312855 : Blo 1782092 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B1782631 : Blo 1782092 1782631 := bstep (se 1 (by rfl) ⟨1336973, by rfl⟩ : syracuseStep 1782631 = 2673947) B2673947
theorem B2675849 : Blo 1782092 2675849 := bstep (se 2 (by rfl) ⟨1003443, by rfl⟩ : syracuseStep 2675849 = 2006887) B2006887
theorem B1783015 : Blo 1782092 1783015 := bstep (se 1 (by rfl) ⟨1337261, by rfl⟩ : syracuseStep 1783015 = 2674523) B2674523
theorem B6018407 : Blo 1782092 6018407 := bstep (se 1 (by rfl) ⟨4513805, by rfl⟩ : syracuseStep 6018407 = 9027611) B9027611
theorem B6018461 : Blo 1782092 6018461 := bstep (se 3 (by rfl) ⟨1128461, by rfl⟩ : syracuseStep 6018461 = 2256923) B2256923
theorem B9025019 : Blo 1782092 9025019 := bstep (se 1 (by rfl) ⟨6768764, by rfl⟩ : syracuseStep 9025019 = 13537529) B13537529
theorem B1784047 : Blo 1782092 1784047 := bstep (se 1 (by rfl) ⟨1338035, by rfl⟩ : syracuseStep 1784047 = 2676071) B2676071
theorem B195279659 : Blo 1782092 195279659 := bstep (se 1 (by rfl) ⟨146459744, by rfl⟩ : syracuseStep 195279659 = 292919489) B292919489
theorem B4012937 : Blo 1782092 4012937 := bstep (se 2 (by rfl) ⟨1504851, by rfl⟩ : syracuseStep 4012937 = 3009703) B3009703
theorem B6103367 : Blo 1782092 6103367 := bstep (se 1 (by rfl) ⟨4577525, by rfl⟩ : syracuseStep 6103367 = 9155051) B9155051
theorem B13541903 : Blo 1782092 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B9635399 : Blo 1782092 9635399 := bstep (se 1 (by rfl) ⟨7226549, by rfl⟩ : syracuseStep 9635399 = 14453099) B14453099
theorem B30869471 : Blo 1782092 30869471 := bstep (se 1 (by rfl) ⟨23152103, by rfl⟩ : syracuseStep 30869471 = 46304207) B46304207
theorem B13535585 : Blo 1782092 13535585 := bstep (se 2 (by rfl) ⟨5075844, by rfl⟩ : syracuseStep 13535585 = 10151689) B10151689
theorem B3009001 : Blo 1782092 3009001 := bstep (se 2 (by rfl) ⟨1128375, by rfl⟩ : syracuseStep 3009001 = 2256751) B2256751
theorem B41757545 : Blo 1782092 41757545 := bstep (se 2 (by rfl) ⟨15659079, by rfl⟩ : syracuseStep 41757545 = 31318159) B31318159
theorem B4885481 : Blo 1782092 4885481 := bstep (se 2 (by rfl) ⟨1832055, by rfl⟩ : syracuseStep 4885481 = 3664111) B3664111
theorem B82341143 : Blo 1782092 82341143 := bstep (se 1 (by rfl) ⟨61755857, by rfl⟩ : syracuseStep 82341143 = 123511715) B123511715
theorem B4648417 : Blo 1782092 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B6016679 : Blo 1782092 6016679 := bstep (se 1 (by rfl) ⟨4512509, by rfl⟩ : syracuseStep 6016679 = 9025019) B9025019
theorem B4010075 : Blo 1782092 4010075 := bstep (se 1 (by rfl) ⟨3007556, by rfl⟩ : syracuseStep 4010075 = 6015113) B6015113
theorem B51409079 : Blo 1782092 51409079 := bstep (se 1 (by rfl) ⟨38556809, by rfl⟩ : syracuseStep 51409079 = 77113619) B77113619
theorem B6427001 : Blo 1782092 6427001 := bstep (se 2 (by rfl) ⟨2410125, by rfl⟩ : syracuseStep 6427001 = 4820251) B4820251
theorem B2675291 : Blo 1782092 2675291 := bstep (se 1 (by rfl) ⟨2006468, by rfl⟩ : syracuseStep 2675291 = 4012937) B4012937
theorem B4011335 : Blo 1782092 4011335 := bstep (se 1 (by rfl) ⟨3008501, by rfl⟩ : syracuseStep 4011335 = 6017003) B6017003
theorem B2676089 : Blo 1782092 2676089 := bstep (se 2 (by rfl) ⟨1003533, by rfl⟩ : syracuseStep 2676089 = 2007067) B2007067
theorem B65975725 : Blo 1782092 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B41162249 : Blo 1782092 41162249 := bstep (se 2 (by rfl) ⟨15435843, by rfl⟩ : syracuseStep 41162249 = 30871687) B30871687
theorem B1783455 : Blo 1782092 1783455 := bstep (se 1 (by rfl) ⟨1337591, by rfl⟩ : syracuseStep 1783455 = 2675183) B2675183
theorem B4011695 : Blo 1782092 4011695 := bstep (se 1 (by rfl) ⟨3008771, by rfl⟩ : syracuseStep 4011695 = 6017543) B6017543
theorem B1783899 : Blo 1782092 1783899 := bstep (se 1 (by rfl) ⟨1337924, by rfl⟩ : syracuseStep 1783899 = 2675849) B2675849
theorem B2005231 : Blo 1782092 2005231 := bstep (se 1 (by rfl) ⟨1503923, by rfl⟩ : syracuseStep 2005231 = 3007847) B3007847
theorem B4012271 : Blo 1782092 4012271 := bstep (se 1 (by rfl) ⟨3009203, by rfl⟩ : syracuseStep 4012271 = 6018407) B6018407
theorem B4012307 : Blo 1782092 4012307 := bstep (se 1 (by rfl) ⟨3009230, by rfl⟩ : syracuseStep 4012307 = 6018461) B6018461
theorem B32988007 : Blo 1782092 32988007 := bstep (se 1 (by rfl) ⟨24741005, by rfl⟩ : syracuseStep 32988007 = 49482011) B49482011
theorem B130186439 : Blo 1782092 130186439 := bstep (se 1 (by rfl) ⟨97639829, by rfl⟩ : syracuseStep 130186439 = 195279659) B195279659
theorem B57818609 : Blo 1782092 57818609 := bstep (se 2 (by rfl) ⟨21681978, by rfl⟩ : syracuseStep 57818609 = 43363957) B43363957
theorem B4284667 : Blo 1782092 4284667 := bstep (se 1 (by rfl) ⟨3213500, by rfl⟩ : syracuseStep 4284667 = 6427001) B6427001
theorem B9027935 : Blo 1782092 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B6423599 : Blo 1782092 6423599 := bstep (se 1 (by rfl) ⟨4817699, by rfl⟩ : syracuseStep 6423599 = 9635399) B9635399
theorem B43984009 : Blo 1782092 43984009 := bstep (se 2 (by rfl) ⟨16494003, by rfl⟩ : syracuseStep 43984009 = 32988007) B32988007
theorem B87967633 : Blo 1782092 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B38545739 : Blo 1782092 38545739 := bstep (se 1 (by rfl) ⟨28909304, by rfl⟩ : syracuseStep 38545739 = 57818609) B57818609
theorem B24791557 : Blo 1782092 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B13027949 : Blo 1782092 13027949 := bstep (se 3 (by rfl) ⟨2442740, by rfl⟩ : syracuseStep 13027949 = 4885481) B4885481
theorem B2673383 : Blo 1782092 2673383 := bstep (se 1 (by rfl) ⟨2005037, by rfl⟩ : syracuseStep 2673383 = 4010075) B4010075
theorem B2673641 : Blo 1782092 2673641 := bstep (se 2 (by rfl) ⟨1002615, by rfl⟩ : syracuseStep 2673641 = 2005231) B2005231
theorem B2674223 : Blo 1782092 2674223 := bstep (se 1 (by rfl) ⟨2005667, by rfl⟩ : syracuseStep 2674223 = 4011335) B4011335
theorem B2674463 : Blo 1782092 2674463 := bstep (se 1 (by rfl) ⟨2005847, by rfl⟩ : syracuseStep 2674463 = 4011695) B4011695
theorem B2674847 : Blo 1782092 2674847 := bstep (se 1 (by rfl) ⟨2006135, by rfl⟩ : syracuseStep 2674847 = 4012271) B4012271
theorem B2674871 : Blo 1782092 2674871 := bstep (se 1 (by rfl) ⟨2006153, by rfl⟩ : syracuseStep 2674871 = 4012307) B4012307
theorem B9023723 : Blo 1782092 9023723 := bstep (se 1 (by rfl) ⟨6767792, by rfl⟩ : syracuseStep 9023723 = 13535585) B13535585
theorem B86790959 : Blo 1782092 86790959 := bstep (se 1 (by rfl) ⟨65093219, by rfl⟩ : syracuseStep 86790959 = 130186439) B130186439
theorem B4011119 : Blo 1782092 4011119 := bstep (se 1 (by rfl) ⟨3008339, by rfl⟩ : syracuseStep 4011119 = 6016679) B6016679
theorem B82318589 : Blo 1782092 82318589 := bstep (se 3 (by rfl) ⟨15434735, by rfl⟩ : syracuseStep 82318589 = 30869471) B30869471
theorem B34272719 : Blo 1782092 34272719 := bstep (se 1 (by rfl) ⟨25704539, by rfl⟩ : syracuseStep 34272719 = 51409079) B51409079
theorem B4068911 : Blo 1782092 4068911 := bstep (se 1 (by rfl) ⟨3051683, by rfl⟩ : syracuseStep 4068911 = 6103367) B6103367
theorem B1783527 : Blo 1782092 1783527 := bstep (se 1 (by rfl) ⟨1337645, by rfl⟩ : syracuseStep 1783527 = 2675291) B2675291
theorem B4012001 : Blo 1782092 4012001 := bstep (se 2 (by rfl) ⟨1504500, by rfl⟩ : syracuseStep 4012001 = 3009001) B3009001
theorem B1784059 : Blo 1782092 1784059 := bstep (se 1 (by rfl) ⟨1338044, by rfl⟩ : syracuseStep 1784059 = 2676089) B2676089
theorem B27441499 : Blo 1782092 27441499 := bstep (se 1 (by rfl) ⟨20581124, by rfl⟩ : syracuseStep 27441499 = 41162249) B41162249
theorem B54894095 : Blo 1782092 54894095 := bstep (se 1 (by rfl) ⟨41170571, by rfl⟩ : syracuseStep 54894095 = 82341143) B82341143
theorem B111353453 : Blo 1782092 111353453 := bstep (se 3 (by rfl) ⟨20878772, by rfl⟩ : syracuseStep 111353453 = 41757545) B41757545
theorem B57860639 : Blo 1782092 57860639 := bstep (se 1 (by rfl) ⟨43395479, by rfl⟩ : syracuseStep 57860639 = 86790959) B86790959
theorem B33055409 : Blo 1782092 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B54879059 : Blo 1782092 54879059 := bstep (se 1 (by rfl) ⟨41159294, by rfl⟩ : syracuseStep 54879059 = 82318589) B82318589
theorem B22848479 : Blo 1782092 22848479 := bstep (se 1 (by rfl) ⟨17136359, by rfl⟩ : syracuseStep 22848479 = 34272719) B34272719
theorem B8685299 : Blo 1782092 8685299 := bstep (se 1 (by rfl) ⟨6513974, by rfl⟩ : syracuseStep 8685299 = 13027949) B13027949
theorem B36596063 : Blo 1782092 36596063 := bstep (se 1 (by rfl) ⟨27447047, by rfl⟩ : syracuseStep 36596063 = 54894095) B54894095
theorem B6015815 : Blo 1782092 6015815 := bstep (se 1 (by rfl) ⟨4511861, by rfl⟩ : syracuseStep 6015815 = 9023723) B9023723
theorem B5712889 : Blo 1782092 5712889 := bstep (se 2 (by rfl) ⟨2142333, by rfl⟩ : syracuseStep 5712889 = 4284667) B4284667
theorem B36588665 : Blo 1782092 36588665 := bstep (se 2 (by rfl) ⟨13720749, by rfl⟩ : syracuseStep 36588665 = 27441499) B27441499
theorem B2674079 : Blo 1782092 2674079 := bstep (se 1 (by rfl) ⟨2005559, by rfl⟩ : syracuseStep 2674079 = 4011119) B4011119
theorem B2674667 : Blo 1782092 2674667 := bstep (se 1 (by rfl) ⟨2006000, by rfl⟩ : syracuseStep 2674667 = 4012001) B4012001
theorem B10850429 : Blo 1782092 10850429 := bstep (se 3 (by rfl) ⟨2034455, by rfl⟩ : syracuseStep 10850429 = 4068911) B4068911
theorem B1782255 : Blo 1782092 1782255 := bstep (se 1 (by rfl) ⟨1336691, by rfl⟩ : syracuseStep 1782255 = 2673383) B2673383
theorem B1782427 : Blo 1782092 1782427 := bstep (se 1 (by rfl) ⟨1336820, by rfl⟩ : syracuseStep 1782427 = 2673641) B2673641
theorem B1782815 : Blo 1782092 1782815 := bstep (se 1 (by rfl) ⟨1337111, by rfl⟩ : syracuseStep 1782815 = 2674223) B2674223
theorem B1782975 : Blo 1782092 1782975 := bstep (se 1 (by rfl) ⟨1337231, by rfl⟩ : syracuseStep 1782975 = 2674463) B2674463
theorem B117290177 : Blo 1782092 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B1783231 : Blo 1782092 1783231 := bstep (se 1 (by rfl) ⟨1337423, by rfl⟩ : syracuseStep 1783231 = 2674847) B2674847
theorem B1783247 : Blo 1782092 1783247 := bstep (se 1 (by rfl) ⟨1337435, by rfl⟩ : syracuseStep 1783247 = 2674871) B2674871
theorem B6018623 : Blo 1782092 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B4282399 : Blo 1782092 4282399 := bstep (se 1 (by rfl) ⟨3211799, by rfl⟩ : syracuseStep 4282399 = 6423599) B6423599
theorem B58645345 : Blo 1782092 58645345 := bstep (se 2 (by rfl) ⟨21992004, by rfl⟩ : syracuseStep 58645345 = 43984009) B43984009
theorem B25697159 : Blo 1782092 25697159 := bstep (se 1 (by rfl) ⟨19272869, by rfl⟩ : syracuseStep 25697159 = 38545739) B38545739
theorem B74235635 : Blo 1782092 74235635 := bstep (se 1 (by rfl) ⟨55676726, by rfl⟩ : syracuseStep 74235635 = 111353453) B111353453
theorem B5709865 : Blo 1782092 5709865 := bstep (se 2 (by rfl) ⟨2141199, by rfl⟩ : syracuseStep 5709865 = 4282399) B4282399
theorem B7233619 : Blo 1782092 7233619 := bstep (se 1 (by rfl) ⟨5425214, by rfl⟩ : syracuseStep 7233619 = 10850429) B10850429
theorem B36586039 : Blo 1782092 36586039 := bstep (se 1 (by rfl) ⟨27439529, by rfl⟩ : syracuseStep 36586039 = 54879059) B54879059
theorem B78193451 : Blo 1782092 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B78193793 : Blo 1782092 78193793 := bstep (se 2 (by rfl) ⟨29322672, by rfl⟩ : syracuseStep 78193793 = 58645345) B58645345
theorem B24397375 : Blo 1782092 24397375 := bstep (se 1 (by rfl) ⟨18298031, by rfl⟩ : syracuseStep 24397375 = 36596063) B36596063
theorem B88147757 : Blo 1782092 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B17131439 : Blo 1782092 17131439 := bstep (se 1 (by rfl) ⟨12848579, by rfl⟩ : syracuseStep 17131439 = 25697159) B25697159
theorem B49490423 : Blo 1782092 49490423 := bstep (se 1 (by rfl) ⟨37117817, by rfl⟩ : syracuseStep 49490423 = 74235635) B74235635
theorem B15232319 : Blo 1782092 15232319 := bstep (se 1 (by rfl) ⟨11424239, by rfl⟩ : syracuseStep 15232319 = 22848479) B22848479
theorem B4010543 : Blo 1782092 4010543 := bstep (se 1 (by rfl) ⟨3007907, by rfl⟩ : syracuseStep 4010543 = 6015815) B6015815
theorem B24392443 : Blo 1782092 24392443 := bstep (se 1 (by rfl) ⟨18294332, by rfl⟩ : syracuseStep 24392443 = 36588665) B36588665
theorem B1782719 : Blo 1782092 1782719 := bstep (se 1 (by rfl) ⟨1337039, by rfl⟩ : syracuseStep 1782719 = 2674079) B2674079
theorem B1783111 : Blo 1782092 1783111 := bstep (se 1 (by rfl) ⟨1337333, by rfl⟩ : syracuseStep 1783111 = 2674667) B2674667
theorem B38573759 : Blo 1782092 38573759 := bstep (se 1 (by rfl) ⟨28930319, by rfl⟩ : syracuseStep 38573759 = 57860639) B57860639
theorem B4012415 : Blo 1782092 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B5790199 : Blo 1782092 5790199 := bstep (se 1 (by rfl) ⟨4342649, by rfl⟩ : syracuseStep 5790199 = 8685299) B8685299
theorem B7617185 : Blo 1782092 7617185 := bstep (se 2 (by rfl) ⟨2856444, by rfl⟩ : syracuseStep 7617185 = 5712889) B5712889
theorem B32523257 : Blo 1782092 32523257 := bstep (se 2 (by rfl) ⟨12196221, by rfl⟩ : syracuseStep 32523257 = 24392443) B24392443
theorem B11420959 : Blo 1782092 11420959 := bstep (se 1 (by rfl) ⟨8565719, by rfl⟩ : syracuseStep 11420959 = 17131439) B17131439
theorem B7613153 : Blo 1782092 7613153 := bstep (se 2 (by rfl) ⟨2854932, by rfl⟩ : syracuseStep 7613153 = 5709865) B5709865
theorem B9644825 : Blo 1782092 9644825 := bstep (se 2 (by rfl) ⟨3616809, by rfl⟩ : syracuseStep 9644825 = 7233619) B7233619
theorem B2673695 : Blo 1782092 2673695 := bstep (se 1 (by rfl) ⟨2005271, by rfl⟩ : syracuseStep 2673695 = 4010543) B4010543
theorem B52128967 : Blo 1782092 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B7720265 : Blo 1782092 7720265 := bstep (se 2 (by rfl) ⟨2895099, by rfl⟩ : syracuseStep 7720265 = 5790199) B5790199
theorem B58765171 : Blo 1782092 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B2674943 : Blo 1782092 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B32993615 : Blo 1782092 32993615 := bstep (se 1 (by rfl) ⟨24745211, by rfl⟩ : syracuseStep 32993615 = 49490423) B49490423
theorem B102863357 : Blo 1782092 102863357 := bstep (se 3 (by rfl) ⟨19286879, by rfl⟩ : syracuseStep 102863357 = 38573759) B38573759
theorem B10154879 : Blo 1782092 10154879 := bstep (se 1 (by rfl) ⟨7616159, by rfl⟩ : syracuseStep 10154879 = 15232319) B15232319
theorem B208516781 : Blo 1782092 208516781 := bstep (se 3 (by rfl) ⟨39096896, by rfl⟩ : syracuseStep 208516781 = 78193793) B78193793
theorem B48781385 : Blo 1782092 48781385 := bstep (se 2 (by rfl) ⟨18293019, by rfl⟩ : syracuseStep 48781385 = 36586039) B36586039
theorem B5078123 : Blo 1782092 5078123 := bstep (se 1 (by rfl) ⟨3808592, by rfl⟩ : syracuseStep 5078123 = 7617185) B7617185
theorem B32529833 : Blo 1782092 32529833 := bstep (se 2 (by rfl) ⟨12198687, by rfl⟩ : syracuseStep 32529833 = 24397375) B24397375
theorem B68575571 : Blo 1782092 68575571 := bstep (se 1 (by rfl) ⟨51431678, by rfl⟩ : syracuseStep 68575571 = 102863357) B102863357
theorem B87982973 : Blo 1782092 87982973 := bstep (se 3 (by rfl) ⟨16496807, by rfl⟩ : syracuseStep 87982973 = 32993615) B32993615
theorem B139011187 : Blo 1782092 139011187 := bstep (se 1 (by rfl) ⟨104258390, by rfl⟩ : syracuseStep 139011187 = 208516781) B208516781
theorem B3385415 : Blo 1782092 3385415 := bstep (se 1 (by rfl) ⟨2539061, by rfl⟩ : syracuseStep 3385415 = 5078123) B5078123
theorem B5146843 : Blo 1782092 5146843 := bstep (se 1 (by rfl) ⟨3860132, by rfl⟩ : syracuseStep 5146843 = 7720265) B7720265
theorem B21686555 : Blo 1782092 21686555 := bstep (se 1 (by rfl) ⟨16264916, by rfl⟩ : syracuseStep 21686555 = 32529833) B32529833
theorem B6769919 : Blo 1782092 6769919 := bstep (se 1 (by rfl) ⟨5077439, by rfl⟩ : syracuseStep 6769919 = 10154879) B10154879
theorem B69505289 : Blo 1782092 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B5075435 : Blo 1782092 5075435 := bstep (se 1 (by rfl) ⟨3806576, by rfl⟩ : syracuseStep 5075435 = 7613153) B7613153
theorem B1782463 : Blo 1782092 1782463 := bstep (se 1 (by rfl) ⟨1336847, by rfl⟩ : syracuseStep 1782463 = 2673695) B2673695
theorem B78353561 : Blo 1782092 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B1783295 : Blo 1782092 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B21682171 : Blo 1782092 21682171 := bstep (se 1 (by rfl) ⟨16261628, by rfl⟩ : syracuseStep 21682171 = 32523257) B32523257
theorem B32520923 : Blo 1782092 32520923 := bstep (se 1 (by rfl) ⟨24390692, by rfl⟩ : syracuseStep 32520923 = 48781385) B48781385
theorem B15227945 : Blo 1782092 15227945 := bstep (se 2 (by rfl) ⟨5710479, by rfl⟩ : syracuseStep 15227945 = 11420959) B11420959
theorem B6429883 : Blo 1782092 6429883 := bstep (se 1 (by rfl) ⟨4822412, by rfl⟩ : syracuseStep 6429883 = 9644825) B9644825
theorem B9027773 : Blo 1782092 9027773 := bstep (se 3 (by rfl) ⟨1692707, by rfl⟩ : syracuseStep 9027773 = 3385415) B3385415
theorem B3383623 : Blo 1782092 3383623 := bstep (se 1 (by rfl) ⟨2537717, by rfl⟩ : syracuseStep 3383623 = 5075435) B5075435
theorem B58655315 : Blo 1782092 58655315 := bstep (se 1 (by rfl) ⟨43991486, by rfl⟩ : syracuseStep 58655315 = 87982973) B87982973
theorem B10151963 : Blo 1782092 10151963 := bstep (se 1 (by rfl) ⟨7613972, by rfl⟩ : syracuseStep 10151963 = 15227945) B15227945
theorem B46336859 : Blo 1782092 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B52235707 : Blo 1782092 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B185348249 : Blo 1782092 185348249 := bstep (se 2 (by rfl) ⟨69505593, by rfl⟩ : syracuseStep 185348249 = 139011187) B139011187
theorem B8573177 : Blo 1782092 8573177 := bstep (se 2 (by rfl) ⟨3214941, by rfl⟩ : syracuseStep 8573177 = 6429883) B6429883
theorem B21680615 : Blo 1782092 21680615 := bstep (se 1 (by rfl) ⟨16260461, by rfl⟩ : syracuseStep 21680615 = 32520923) B32520923
theorem B45717047 : Blo 1782092 45717047 := bstep (se 1 (by rfl) ⟨34287785, by rfl⟩ : syracuseStep 45717047 = 68575571) B68575571
theorem B6862457 : Blo 1782092 6862457 := bstep (se 2 (by rfl) ⟨2573421, by rfl⟩ : syracuseStep 6862457 = 5146843) B5146843
theorem B14457703 : Blo 1782092 14457703 := bstep (se 1 (by rfl) ⟨10843277, by rfl⟩ : syracuseStep 14457703 = 21686555) B21686555
theorem B4513279 : Blo 1782092 4513279 := bstep (se 1 (by rfl) ⟨3384959, by rfl⟩ : syracuseStep 4513279 = 6769919) B6769919
theorem B28909561 : Blo 1782092 28909561 := bstep (se 2 (by rfl) ⟨10841085, by rfl⟩ : syracuseStep 28909561 = 21682171) B21682171
theorem B19276937 : Blo 1782092 19276937 := bstep (se 2 (by rfl) ⟨7228851, by rfl⟩ : syracuseStep 19276937 = 14457703) B14457703
theorem B6767975 : Blo 1782092 6767975 := bstep (se 1 (by rfl) ⟨5075981, by rfl⟩ : syracuseStep 6767975 = 10151963) B10151963
theorem B38546081 : Blo 1782092 38546081 := bstep (se 2 (by rfl) ⟨14454780, by rfl⟩ : syracuseStep 38546081 = 28909561) B28909561
theorem B14453743 : Blo 1782092 14453743 := bstep (se 1 (by rfl) ⟨10840307, by rfl⟩ : syracuseStep 14453743 = 21680615) B21680615
theorem B39103543 : Blo 1782092 39103543 := bstep (se 1 (by rfl) ⟨29327657, by rfl⟩ : syracuseStep 39103543 = 58655315) B58655315
theorem B30478031 : Blo 1782092 30478031 := bstep (se 1 (by rfl) ⟨22858523, by rfl⟩ : syracuseStep 30478031 = 45717047) B45717047
theorem B4574971 : Blo 1782092 4574971 := bstep (se 1 (by rfl) ⟨3431228, by rfl⟩ : syracuseStep 4574971 = 6862457) B6862457
theorem B6017705 : Blo 1782092 6017705 := bstep (se 2 (by rfl) ⟨2256639, by rfl⟩ : syracuseStep 6017705 = 4513279) B4513279
theorem B123565499 : Blo 1782092 123565499 := bstep (se 1 (by rfl) ⟨92674124, by rfl⟩ : syracuseStep 123565499 = 185348249) B185348249
theorem B6018515 : Blo 1782092 6018515 := bstep (se 1 (by rfl) ⟨4513886, by rfl⟩ : syracuseStep 6018515 = 9027773) B9027773
theorem B5715451 : Blo 1782092 5715451 := bstep (se 1 (by rfl) ⟨4286588, by rfl⟩ : syracuseStep 5715451 = 8573177) B8573177
theorem B4511497 : Blo 1782092 4511497 := bstep (se 2 (by rfl) ⟨1691811, by rfl⟩ : syracuseStep 4511497 = 3383623) B3383623
theorem B30891239 : Blo 1782092 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B69647609 : Blo 1782092 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B208552229 : Blo 1782092 208552229 := bstep (se 4 (by rfl) ⟨19551771, by rfl⟩ : syracuseStep 208552229 = 39103543) B39103543
theorem B6015329 : Blo 1782092 6015329 := bstep (se 2 (by rfl) ⟨2255748, by rfl⟩ : syracuseStep 6015329 = 4511497) B4511497
theorem B20318687 : Blo 1782092 20318687 := bstep (se 1 (by rfl) ⟨15239015, by rfl⟩ : syracuseStep 20318687 = 30478031) B30478031
theorem B19271657 : Blo 1782092 19271657 := bstep (se 2 (by rfl) ⟨7226871, by rfl⟩ : syracuseStep 19271657 = 14453743) B14453743
theorem B6099961 : Blo 1782092 6099961 := bstep (se 2 (by rfl) ⟨2287485, by rfl⟩ : syracuseStep 6099961 = 4574971) B4574971
theorem B4011803 : Blo 1782092 4011803 := bstep (se 1 (by rfl) ⟨3008852, by rfl⟩ : syracuseStep 4011803 = 6017705) B6017705
theorem B12851291 : Blo 1782092 12851291 := bstep (se 1 (by rfl) ⟨9638468, by rfl⟩ : syracuseStep 12851291 = 19276937) B19276937
theorem B4511983 : Blo 1782092 4511983 := bstep (se 1 (by rfl) ⟨3383987, by rfl⟩ : syracuseStep 4511983 = 6767975) B6767975
theorem B82376999 : Blo 1782092 82376999 := bstep (se 1 (by rfl) ⟨61782749, by rfl⟩ : syracuseStep 82376999 = 123565499) B123565499
theorem B4012343 : Blo 1782092 4012343 := bstep (se 1 (by rfl) ⟨3009257, by rfl⟩ : syracuseStep 4012343 = 6018515) B6018515
theorem B25697387 : Blo 1782092 25697387 := bstep (se 1 (by rfl) ⟨19273040, by rfl⟩ : syracuseStep 25697387 = 38546081) B38546081
theorem B20594159 : Blo 1782092 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B46431739 : Blo 1782092 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B30482405 : Blo 1782092 30482405 := bstep (se 4 (by rfl) ⟨2857725, by rfl⟩ : syracuseStep 30482405 = 5715451) B5715451
theorem B139034819 : Blo 1782092 139034819 := bstep (se 1 (by rfl) ⟨104276114, by rfl⟩ : syracuseStep 139034819 = 208552229) B208552229
theorem B61908985 : Blo 1782092 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B17131591 : Blo 1782092 17131591 := bstep (se 1 (by rfl) ⟨12848693, by rfl⟩ : syracuseStep 17131591 = 25697387) B25697387
theorem B12847771 : Blo 1782092 12847771 := bstep (se 1 (by rfl) ⟨9635828, by rfl⟩ : syracuseStep 12847771 = 19271657) B19271657
theorem B6015977 : Blo 1782092 6015977 := bstep (se 2 (by rfl) ⟨2255991, by rfl⟩ : syracuseStep 6015977 = 4511983) B4511983
theorem B2674535 : Blo 1782092 2674535 := bstep (se 1 (by rfl) ⟨2005901, by rfl⟩ : syracuseStep 2674535 = 4011803) B4011803
theorem B2674895 : Blo 1782092 2674895 := bstep (se 1 (by rfl) ⟨2006171, by rfl⟩ : syracuseStep 2674895 = 4012343) B4012343
theorem B4010219 : Blo 1782092 4010219 := bstep (se 1 (by rfl) ⟨3007664, by rfl⟩ : syracuseStep 4010219 = 6015329) B6015329
theorem B13545791 : Blo 1782092 13545791 := bstep (se 1 (by rfl) ⟨10159343, by rfl⟩ : syracuseStep 13545791 = 20318687) B20318687
theorem B20321603 : Blo 1782092 20321603 := bstep (se 1 (by rfl) ⟨15241202, by rfl⟩ : syracuseStep 20321603 = 30482405) B30482405
theorem B8133281 : Blo 1782092 8133281 := bstep (se 2 (by rfl) ⟨3049980, by rfl⟩ : syracuseStep 8133281 = 6099961) B6099961
theorem B8567527 : Blo 1782092 8567527 := bstep (se 1 (by rfl) ⟨6425645, by rfl⟩ : syracuseStep 8567527 = 12851291) B12851291
theorem B54917999 : Blo 1782092 54917999 := bstep (se 1 (by rfl) ⟨41188499, by rfl⟩ : syracuseStep 54917999 = 82376999) B82376999
theorem B13729439 : Blo 1782092 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B17130361 : Blo 1782092 17130361 := bstep (se 2 (by rfl) ⟨6423885, by rfl⟩ : syracuseStep 17130361 = 12847771) B12847771
theorem B36611999 : Blo 1782092 36611999 := bstep (se 1 (by rfl) ⟨27458999, by rfl⟩ : syracuseStep 36611999 = 54917999) B54917999
theorem B9152959 : Blo 1782092 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B82545313 : Blo 1782092 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B22842121 : Blo 1782092 22842121 := bstep (se 2 (by rfl) ⟨8565795, by rfl⟩ : syracuseStep 22842121 = 17131591) B17131591
theorem B2673479 : Blo 1782092 2673479 := bstep (se 1 (by rfl) ⟨2005109, by rfl⟩ : syracuseStep 2673479 = 4010219) B4010219
theorem B9030527 : Blo 1782092 9030527 := bstep (se 1 (by rfl) ⟨6772895, by rfl⟩ : syracuseStep 9030527 = 13545791) B13545791
theorem B11423369 : Blo 1782092 11423369 := bstep (se 2 (by rfl) ⟨4283763, by rfl⟩ : syracuseStep 11423369 = 8567527) B8567527
theorem B4010651 : Blo 1782092 4010651 := bstep (se 1 (by rfl) ⟨3007988, by rfl⟩ : syracuseStep 4010651 = 6015977) B6015977
theorem B1783023 : Blo 1782092 1783023 := bstep (se 1 (by rfl) ⟨1337267, by rfl⟩ : syracuseStep 1783023 = 2674535) B2674535
theorem B92689879 : Blo 1782092 92689879 := bstep (se 1 (by rfl) ⟨69517409, by rfl⟩ : syracuseStep 92689879 = 139034819) B139034819
theorem B1783263 : Blo 1782092 1783263 := bstep (se 1 (by rfl) ⟨1337447, by rfl⟩ : syracuseStep 1783263 = 2674895) B2674895
theorem B13547735 : Blo 1782092 13547735 := bstep (se 1 (by rfl) ⟨10160801, by rfl⟩ : syracuseStep 13547735 = 20321603) B20321603
theorem B5422187 : Blo 1782092 5422187 := bstep (se 1 (by rfl) ⟨4066640, by rfl⟩ : syracuseStep 5422187 = 8133281) B8133281
theorem B110060417 : Blo 1782092 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B22840481 : Blo 1782092 22840481 := bstep (se 2 (by rfl) ⟨8565180, by rfl⟩ : syracuseStep 22840481 = 17130361) B17130361
theorem B123586505 : Blo 1782092 123586505 := bstep (se 2 (by rfl) ⟨46344939, by rfl⟩ : syracuseStep 123586505 = 92689879) B92689879
theorem B3614791 : Blo 1782092 3614791 := bstep (se 1 (by rfl) ⟨2711093, by rfl⟩ : syracuseStep 3614791 = 5422187) B5422187
theorem B2673767 : Blo 1782092 2673767 := bstep (se 1 (by rfl) ⟨2005325, by rfl⟩ : syracuseStep 2673767 = 4010651) B4010651
theorem B24407999 : Blo 1782092 24407999 := bstep (se 1 (by rfl) ⟨18305999, by rfl⟩ : syracuseStep 24407999 = 36611999) B36611999
theorem B9031823 : Blo 1782092 9031823 := bstep (se 1 (by rfl) ⟨6773867, by rfl⟩ : syracuseStep 9031823 = 13547735) B13547735
theorem B1782319 : Blo 1782092 1782319 := bstep (se 1 (by rfl) ⟨1336739, by rfl⟩ : syracuseStep 1782319 = 2673479) B2673479
theorem B7615579 : Blo 1782092 7615579 := bstep (se 1 (by rfl) ⟨5711684, by rfl⟩ : syracuseStep 7615579 = 11423369) B11423369
theorem B12203945 : Blo 1782092 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B30456161 : Blo 1782092 30456161 := bstep (se 2 (by rfl) ⟨11421060, by rfl⟩ : syracuseStep 30456161 = 22842121) B22842121
theorem B6020351 : Blo 1782092 6020351 := bstep (se 1 (by rfl) ⟨4515263, by rfl⟩ : syracuseStep 6020351 = 9030527) B9030527
theorem B6021215 : Blo 1782092 6021215 := bstep (se 1 (by rfl) ⟨4515911, by rfl⟩ : syracuseStep 6021215 = 9031823) B9031823
theorem B8135963 : Blo 1782092 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B16271999 : Blo 1782092 16271999 := bstep (se 1 (by rfl) ⟨12203999, by rfl⟩ : syracuseStep 16271999 = 24407999) B24407999
theorem B4819721 : Blo 1782092 4819721 := bstep (se 2 (by rfl) ⟨1807395, by rfl⟩ : syracuseStep 4819721 = 3614791) B3614791
theorem B82391003 : Blo 1782092 82391003 := bstep (se 1 (by rfl) ⟨61793252, by rfl⟩ : syracuseStep 82391003 = 123586505) B123586505
theorem B10154105 : Blo 1782092 10154105 := bstep (se 2 (by rfl) ⟨3807789, by rfl⟩ : syracuseStep 10154105 = 7615579) B7615579
theorem B20304107 : Blo 1782092 20304107 := bstep (se 1 (by rfl) ⟨15228080, by rfl⟩ : syracuseStep 20304107 = 30456161) B30456161
theorem B1782511 : Blo 1782092 1782511 := bstep (se 1 (by rfl) ⟨1336883, by rfl⟩ : syracuseStep 1782511 = 2673767) B2673767
theorem B73373611 : Blo 1782092 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B15226987 : Blo 1782092 15226987 := bstep (se 1 (by rfl) ⟨11420240, by rfl⟩ : syracuseStep 15226987 = 22840481) B22840481
theorem B4013567 : Blo 1782092 4013567 := bstep (se 1 (by rfl) ⟨3010175, by rfl⟩ : syracuseStep 4013567 = 6020351) B6020351
theorem B4014143 : Blo 1782092 4014143 := bstep (se 1 (by rfl) ⟨3010607, by rfl⟩ : syracuseStep 4014143 = 6021215) B6021215
theorem B5423975 : Blo 1782092 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B10847999 : Blo 1782092 10847999 := bstep (se 1 (by rfl) ⟨8135999, by rfl⟩ : syracuseStep 10847999 = 16271999) B16271999
theorem B97831481 : Blo 1782092 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B6769403 : Blo 1782092 6769403 := bstep (se 1 (by rfl) ⟨5077052, by rfl⟩ : syracuseStep 6769403 = 10154105) B10154105
theorem B20302649 : Blo 1782092 20302649 := bstep (se 2 (by rfl) ⟨7613493, by rfl⟩ : syracuseStep 20302649 = 15226987) B15226987
theorem B13536071 : Blo 1782092 13536071 := bstep (se 1 (by rfl) ⟨10152053, by rfl⟩ : syracuseStep 13536071 = 20304107) B20304107
theorem B2675711 : Blo 1782092 2675711 := bstep (se 1 (by rfl) ⟨2006783, by rfl⟩ : syracuseStep 2675711 = 4013567) B4013567
theorem B12852589 : Blo 1782092 12852589 := bstep (se 3 (by rfl) ⟨2409860, by rfl⟩ : syracuseStep 12852589 = 4819721) B4819721
theorem B54927335 : Blo 1782092 54927335 := bstep (se 1 (by rfl) ⟨41195501, by rfl⟩ : syracuseStep 54927335 = 82391003) B82391003
theorem B13535099 : Blo 1782092 13535099 := bstep (se 1 (by rfl) ⟨10151324, by rfl⟩ : syracuseStep 13535099 = 20302649) B20302649
theorem B3615983 : Blo 1782092 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B9024047 : Blo 1782092 9024047 := bstep (se 1 (by rfl) ⟨6768035, by rfl⟩ : syracuseStep 9024047 = 13536071) B13536071
theorem B2676095 : Blo 1782092 2676095 := bstep (se 1 (by rfl) ⟨2007071, by rfl⟩ : syracuseStep 2676095 = 4014143) B4014143
theorem B1043535797 : Blo 1782092 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B1783807 : Blo 1782092 1783807 := bstep (se 1 (by rfl) ⟨1337855, by rfl⟩ : syracuseStep 1783807 = 2675711) B2675711
theorem B7231999 : Blo 1782092 7231999 := bstep (se 1 (by rfl) ⟨5423999, by rfl⟩ : syracuseStep 7231999 = 10847999) B10847999
theorem B17136785 : Blo 1782092 17136785 := bstep (se 2 (by rfl) ⟨6426294, by rfl⟩ : syracuseStep 17136785 = 12852589) B12852589
theorem B4512935 : Blo 1782092 4512935 := bstep (se 1 (by rfl) ⟨3384701, by rfl⟩ : syracuseStep 4512935 = 6769403) B6769403
theorem B36618223 : Blo 1782092 36618223 := bstep (se 1 (by rfl) ⟨27463667, by rfl⟩ : syracuseStep 36618223 = 54927335) B54927335
theorem B9642665 : Blo 1782092 9642665 := bstep (se 2 (by rfl) ⟨3615999, by rfl⟩ : syracuseStep 9642665 = 7231999) B7231999
theorem B695690531 : Blo 1782092 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B3008623 : Blo 1782092 3008623 := bstep (se 1 (by rfl) ⟨2256467, by rfl⟩ : syracuseStep 3008623 = 4512935) B4512935
theorem B2410655 : Blo 1782092 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B6016031 : Blo 1782092 6016031 := bstep (se 1 (by rfl) ⟨4512023, by rfl⟩ : syracuseStep 6016031 = 9024047) B9024047
theorem B9023399 : Blo 1782092 9023399 := bstep (se 1 (by rfl) ⟨6767549, by rfl⟩ : syracuseStep 9023399 = 13535099) B13535099
theorem B11424523 : Blo 1782092 11424523 := bstep (se 1 (by rfl) ⟨8568392, by rfl⟩ : syracuseStep 11424523 = 17136785) B17136785
theorem B1784063 : Blo 1782092 1784063 := bstep (se 1 (by rfl) ⟨1338047, by rfl⟩ : syracuseStep 1784063 = 2676095) B2676095
theorem B48824297 : Blo 1782092 48824297 := bstep (se 2 (by rfl) ⟨18309111, by rfl⟩ : syracuseStep 48824297 = 36618223) B36618223
theorem B6015599 : Blo 1782092 6015599 := bstep (se 1 (by rfl) ⟨4511699, by rfl⟩ : syracuseStep 6015599 = 9023399) B9023399
theorem B32549531 : Blo 1782092 32549531 := bstep (se 1 (by rfl) ⟨24412148, by rfl⟩ : syracuseStep 32549531 = 48824297) B48824297
theorem B463793687 : Blo 1782092 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B15232697 : Blo 1782092 15232697 := bstep (se 2 (by rfl) ⟨5712261, by rfl⟩ : syracuseStep 15232697 = 11424523) B11424523
theorem B4010687 : Blo 1782092 4010687 := bstep (se 1 (by rfl) ⟨3008015, by rfl⟩ : syracuseStep 4010687 = 6016031) B6016031
theorem B4011497 : Blo 1782092 4011497 := bstep (se 2 (by rfl) ⟨1504311, by rfl⟩ : syracuseStep 4011497 = 3008623) B3008623
theorem B6428413 : Blo 1782092 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B6428443 : Blo 1782092 6428443 := bstep (se 1 (by rfl) ⟨4821332, by rfl⟩ : syracuseStep 6428443 = 9642665) B9642665
theorem B34284869 : Blo 1782092 34284869 := bstep (se 4 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 34284869 = 6428413) B6428413
theorem B8571257 : Blo 1782092 8571257 := bstep (se 2 (by rfl) ⟨3214221, by rfl⟩ : syracuseStep 8571257 = 6428443) B6428443
theorem B2673791 : Blo 1782092 2673791 := bstep (se 1 (by rfl) ⟨2005343, by rfl⟩ : syracuseStep 2673791 = 4010687) B4010687
theorem B2674331 : Blo 1782092 2674331 := bstep (se 1 (by rfl) ⟨2005748, by rfl⟩ : syracuseStep 2674331 = 4011497) B4011497
theorem B86798749 : Blo 1782092 86798749 := bstep (se 3 (by rfl) ⟨16274765, by rfl⟩ : syracuseStep 86798749 = 32549531) B32549531
theorem B4010399 : Blo 1782092 4010399 := bstep (se 1 (by rfl) ⟨3007799, by rfl⟩ : syracuseStep 4010399 = 6015599) B6015599
theorem B309195791 : Blo 1782092 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B10155131 : Blo 1782092 10155131 := bstep (se 1 (by rfl) ⟨7616348, by rfl⟩ : syracuseStep 10155131 = 15232697) B15232697
theorem B22856579 : Blo 1782092 22856579 := bstep (se 1 (by rfl) ⟨17142434, by rfl⟩ : syracuseStep 22856579 = 34284869) B34284869
theorem B2673599 : Blo 1782092 2673599 := bstep (se 1 (by rfl) ⟨2005199, by rfl⟩ : syracuseStep 2673599 = 4010399) B4010399
theorem B115731665 : Blo 1782092 115731665 := bstep (se 2 (by rfl) ⟨43399374, by rfl⟩ : syracuseStep 115731665 = 86798749) B86798749
theorem B206130527 : Blo 1782092 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B6770087 : Blo 1782092 6770087 := bstep (se 1 (by rfl) ⟨5077565, by rfl⟩ : syracuseStep 6770087 = 10155131) B10155131
theorem B5714171 : Blo 1782092 5714171 := bstep (se 1 (by rfl) ⟨4285628, by rfl⟩ : syracuseStep 5714171 = 8571257) B8571257
theorem B1782527 : Blo 1782092 1782527 := bstep (se 1 (by rfl) ⟨1336895, by rfl⟩ : syracuseStep 1782527 = 2673791) B2673791
theorem B1782887 : Blo 1782092 1782887 := bstep (se 1 (by rfl) ⟨1337165, by rfl⟩ : syracuseStep 1782887 = 2674331) B2674331
theorem B3809447 : Blo 1782092 3809447 := bstep (se 1 (by rfl) ⟨2857085, by rfl⟩ : syracuseStep 3809447 = 5714171) B5714171
theorem B15237719 : Blo 1782092 15237719 := bstep (se 1 (by rfl) ⟨11428289, by rfl⟩ : syracuseStep 15237719 = 22856579) B22856579
theorem B77154443 : Blo 1782092 77154443 := bstep (se 1 (by rfl) ⟨57865832, by rfl⟩ : syracuseStep 77154443 = 115731665) B115731665
theorem B1782399 : Blo 1782092 1782399 := bstep (se 1 (by rfl) ⟨1336799, by rfl⟩ : syracuseStep 1782399 = 2673599) B2673599
theorem B137420351 : Blo 1782092 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B4513391 : Blo 1782092 4513391 := bstep (se 1 (by rfl) ⟨3385043, by rfl⟩ : syracuseStep 4513391 = 6770087) B6770087
theorem B2539631 : Blo 1782092 2539631 := bstep (se 1 (by rfl) ⟨1904723, by rfl⟩ : syracuseStep 2539631 = 3809447) B3809447
theorem B10158479 : Blo 1782092 10158479 := bstep (se 1 (by rfl) ⟨7618859, by rfl⟩ : syracuseStep 10158479 = 15237719) B15237719
theorem B91613567 : Blo 1782092 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B3008927 : Blo 1782092 3008927 := bstep (se 1 (by rfl) ⟨2256695, by rfl⟩ : syracuseStep 3008927 = 4513391) B4513391
theorem B51436295 : Blo 1782092 51436295 := bstep (se 1 (by rfl) ⟨38577221, by rfl⟩ : syracuseStep 51436295 = 77154443) B77154443
theorem B61075711 : Blo 1782092 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B6772319 : Blo 1782092 6772319 := bstep (se 1 (by rfl) ⟨5079239, by rfl⟩ : syracuseStep 6772319 = 10158479) B10158479
theorem B6772349 : Blo 1782092 6772349 := bstep (se 3 (by rfl) ⟨1269815, by rfl⟩ : syracuseStep 6772349 = 2539631) B2539631
theorem B2005951 : Blo 1782092 2005951 := bstep (se 1 (by rfl) ⟨1504463, by rfl⟩ : syracuseStep 2005951 = 3008927) B3008927
theorem B34290863 : Blo 1782092 34290863 := bstep (se 1 (by rfl) ⟨25718147, by rfl⟩ : syracuseStep 34290863 = 51436295) B51436295
theorem B4514879 : Blo 1782092 4514879 := bstep (se 1 (by rfl) ⟨3386159, by rfl⟩ : syracuseStep 4514879 = 6772319) B6772319
theorem B4514899 : Blo 1782092 4514899 := bstep (se 1 (by rfl) ⟨3386174, by rfl⟩ : syracuseStep 4514899 = 6772349) B6772349
theorem B2674601 : Blo 1782092 2674601 := bstep (se 2 (by rfl) ⟨1002975, by rfl⟩ : syracuseStep 2674601 = 2005951) B2005951
theorem B22860575 : Blo 1782092 22860575 := bstep (se 1 (by rfl) ⟨17145431, by rfl⟩ : syracuseStep 22860575 = 34290863) B34290863
theorem B81434281 : Blo 1782092 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B108579041 : Blo 1782092 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B15240383 : Blo 1782092 15240383 := bstep (se 1 (by rfl) ⟨11430287, by rfl⟩ : syracuseStep 15240383 = 22860575) B22860575
theorem B3009919 : Blo 1782092 3009919 := bstep (se 1 (by rfl) ⟨2257439, by rfl⟩ : syracuseStep 3009919 = 4514879) B4514879
theorem B1783067 : Blo 1782092 1783067 := bstep (se 1 (by rfl) ⟨1337300, by rfl⟩ : syracuseStep 1783067 = 2674601) B2674601
theorem B6019865 : Blo 1782092 6019865 := bstep (se 2 (by rfl) ⟨2257449, by rfl⟩ : syracuseStep 6019865 = 4514899) B4514899
theorem B72386027 : Blo 1782092 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B10160255 : Blo 1782092 10160255 := bstep (se 1 (by rfl) ⟨7620191, by rfl⟩ : syracuseStep 10160255 = 15240383) B15240383
theorem B4013225 : Blo 1782092 4013225 := bstep (se 2 (by rfl) ⟨1504959, by rfl⟩ : syracuseStep 4013225 = 3009919) B3009919
theorem B4013243 : Blo 1782092 4013243 := bstep (se 1 (by rfl) ⟨3009932, by rfl⟩ : syracuseStep 4013243 = 6019865) B6019865
theorem B2675483 : Blo 1782092 2675483 := bstep (se 1 (by rfl) ⟨2006612, by rfl⟩ : syracuseStep 2675483 = 4013225) B4013225
theorem B2675495 : Blo 1782092 2675495 := bstep (se 1 (by rfl) ⟨2006621, by rfl⟩ : syracuseStep 2675495 = 4013243) B4013243
theorem B48257351 : Blo 1782092 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B6773503 : Blo 1782092 6773503 := bstep (se 1 (by rfl) ⟨5080127, by rfl⟩ : syracuseStep 6773503 = 10160255) B10160255
theorem B32171567 : Blo 1782092 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B9031337 : Blo 1782092 9031337 := bstep (se 2 (by rfl) ⟨3386751, by rfl⟩ : syracuseStep 9031337 = 6773503) B6773503
theorem B1783655 : Blo 1782092 1783655 := bstep (se 1 (by rfl) ⟨1337741, by rfl⟩ : syracuseStep 1783655 = 2675483) B2675483
theorem B1783663 : Blo 1782092 1783663 := bstep (se 1 (by rfl) ⟨1337747, by rfl⟩ : syracuseStep 1783663 = 2675495) B2675495
theorem B85790845 : Blo 1782092 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B6020891 : Blo 1782092 6020891 := bstep (se 1 (by rfl) ⟨4515668, by rfl⟩ : syracuseStep 6020891 = 9031337) B9031337
theorem B457551173 : Blo 1782092 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B4013927 : Blo 1782092 4013927 := bstep (se 1 (by rfl) ⟨3010445, by rfl⟩ : syracuseStep 4013927 = 6020891) B6020891
theorem B305034115 : Blo 1782092 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B2675951 : Blo 1782092 2675951 := bstep (se 1 (by rfl) ⟨2006963, by rfl⟩ : syracuseStep 2675951 = 4013927) B4013927
theorem B406712153 : Blo 1782092 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B1783967 : Blo 1782092 1783967 := bstep (se 1 (by rfl) ⟨1337975, by rfl⟩ : syracuseStep 1783967 = 2675951) B2675951
theorem B271141435 : Blo 1782092 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 1782092 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B964058435 : Blo 1782092 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B642705623 : Blo 1782092 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B428470415 : Blo 1782092 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 1782092 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B761725181 : Blo 1782092 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B507816787 : Blo 1782092 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 1782092 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 1782092 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 1782092 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 1782092 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 1782092 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 1782092 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 1782092 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 1782092 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 1782092 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 1782092 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 1782092 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 1782092 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 1782092 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 1782092 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 1782092 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 1782092 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 1782092 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 1782092 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 1782092 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 1782092 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 1782092 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 1782092 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 1782092 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 1782092 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 1782092 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 1782092 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 1782092 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 1782092 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 1782092 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 1782092 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 1782092 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 1782092 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 1782092 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 1782092 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 1782092 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 1782092 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 1782092 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 1782092 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 1782092 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 1782092 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 1782092 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 1782092 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B1783579 : Blo 1782092 1783579 := bstep (se 1 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 1783579 = 2675369) B2675369

theorem C0 (j : ℕ) (h1 : 445523 ≤ j) (h2 : j ≤ 446022) : Blo 1782092 (4 * j + 3) := by
  interval_cases j
  · exact B1782095
  · exact B1782099
  · exact B1782103
  · exact B1782107
  · exact B1782111
  · exact B1782115
  · exact B1782119
  · exact B1782123
  · exact B1782127
  · exact B1782131
  · exact B1782135
  · exact B1782139
  · exact B1782143
  · exact B1782147
  · exact B1782151
  · exact B1782155
  · exact B1782159
  · exact B1782163
  · exact B1782167
  · exact B1782171
  · exact B1782175
  · exact B1782179
  · exact B1782183
  · exact B1782187
  · exact B1782191
  · exact B1782195
  · exact B1782199
  · exact B1782203
  · exact B1782207
  · exact B1782211
  · exact B1782215
  · exact B1782219
  · exact B1782223
  · exact B1782227
  · exact B1782231
  · exact B1782235
  · exact B1782239
  · exact B1782243
  · exact B1782247
  · exact B1782251
  · exact B1782255
  · exact B1782259
  · exact B1782263
  · exact B1782267
  · exact B1782271
  · exact B1782275
  · exact B1782279
  · exact B1782283
  · exact B1782287
  · exact B1782291
  · exact B1782295
  · exact B1782299
  · exact B1782303
  · exact B1782307
  · exact B1782311
  · exact B1782315
  · exact B1782319
  · exact B1782323
  · exact B1782327
  · exact B1782331
  · exact B1782335
  · exact B1782339
  · exact B1782343
  · exact B1782347
  · exact B1782351
  · exact B1782355
  · exact B1782359
  · exact B1782363
  · exact B1782367
  · exact B1782371
  · exact B1782375
  · exact B1782379
  · exact B1782383
  · exact B1782387
  · exact B1782391
  · exact B1782395
  · exact B1782399
  · exact B1782403
  · exact B1782407
  · exact B1782411
  · exact B1782415
  · exact B1782419
  · exact B1782423
  · exact B1782427
  · exact B1782431
  · exact B1782435
  · exact B1782439
  · exact B1782443
  · exact B1782447
  · exact B1782451
  · exact B1782455
  · exact B1782459
  · exact B1782463
  · exact B1782467
  · exact B1782471
  · exact B1782475
  · exact B1782479
  · exact B1782483
  · exact B1782487
  · exact B1782491
  · exact B1782495
  · exact B1782499
  · exact B1782503
  · exact B1782507
  · exact B1782511
  · exact B1782515
  · exact B1782519
  · exact B1782523
  · exact B1782527
  · exact B1782531
  · exact B1782535
  · exact B1782539
  · exact B1782543
  · exact B1782547
  · exact B1782551
  · exact B1782555
  · exact B1782559
  · exact B1782563
  · exact B1782567
  · exact B1782571
  · exact B1782575
  · exact B1782579
  · exact B1782583
  · exact B1782587
  · exact B1782591
  · exact B1782595
  · exact B1782599
  · exact B1782603
  · exact B1782607
  · exact B1782611
  · exact B1782615
  · exact B1782619
  · exact B1782623
  · exact B1782627
  · exact B1782631
  · exact B1782635
  · exact B1782639
  · exact B1782643
  · exact B1782647
  · exact B1782651
  · exact B1782655
  · exact B1782659
  · exact B1782663
  · exact B1782667
  · exact B1782671
  · exact B1782675
  · exact B1782679
  · exact B1782683
  · exact B1782687
  · exact B1782691
  · exact B1782695
  · exact B1782699
  · exact B1782703
  · exact B1782707
  · exact B1782711
  · exact B1782715
  · exact B1782719
  · exact B1782723
  · exact B1782727
  · exact B1782731
  · exact B1782735
  · exact B1782739
  · exact B1782743
  · exact B1782747
  · exact B1782751
  · exact B1782755
  · exact B1782759
  · exact B1782763
  · exact B1782767
  · exact B1782771
  · exact B1782775
  · exact B1782779
  · exact B1782783
  · exact B1782787
  · exact B1782791
  · exact B1782795
  · exact B1782799
  · exact B1782803
  · exact B1782807
  · exact B1782811
  · exact B1782815
  · exact B1782819
  · exact B1782823
  · exact B1782827
  · exact B1782831
  · exact B1782835
  · exact B1782839
  · exact B1782843
  · exact B1782847
  · exact B1782851
  · exact B1782855
  · exact B1782859
  · exact B1782863
  · exact B1782867
  · exact B1782871
  · exact B1782875
  · exact B1782879
  · exact B1782883
  · exact B1782887
  · exact B1782891
  · exact B1782895
  · exact B1782899
  · exact B1782903
  · exact B1782907
  · exact B1782911
  · exact B1782915
  · exact B1782919
  · exact B1782923
  · exact B1782927
  · exact B1782931
  · exact B1782935
  · exact B1782939
  · exact B1782943
  · exact B1782947
  · exact B1782951
  · exact B1782955
  · exact B1782959
  · exact B1782963
  · exact B1782967
  · exact B1782971
  · exact B1782975
  · exact B1782979
  · exact B1782983
  · exact B1782987
  · exact B1782991
  · exact B1782995
  · exact B1782999
  · exact B1783003
  · exact B1783007
  · exact B1783011
  · exact B1783015
  · exact B1783019
  · exact B1783023
  · exact B1783027
  · exact B1783031
  · exact B1783035
  · exact B1783039
  · exact B1783043
  · exact B1783047
  · exact B1783051
  · exact B1783055
  · exact B1783059
  · exact B1783063
  · exact B1783067
  · exact B1783071
  · exact B1783075
  · exact B1783079
  · exact B1783083
  · exact B1783087
  · exact B1783091
  · exact B1783095
  · exact B1783099
  · exact B1783103
  · exact B1783107
  · exact B1783111
  · exact B1783115
  · exact B1783119
  · exact B1783123
  · exact B1783127
  · exact B1783131
  · exact B1783135
  · exact B1783139
  · exact B1783143
  · exact B1783147
  · exact B1783151
  · exact B1783155
  · exact B1783159
  · exact B1783163
  · exact B1783167
  · exact B1783171
  · exact B1783175
  · exact B1783179
  · exact B1783183
  · exact B1783187
  · exact B1783191
  · exact B1783195
  · exact B1783199
  · exact B1783203
  · exact B1783207
  · exact B1783211
  · exact B1783215
  · exact B1783219
  · exact B1783223
  · exact B1783227
  · exact B1783231
  · exact B1783235
  · exact B1783239
  · exact B1783243
  · exact B1783247
  · exact B1783251
  · exact B1783255
  · exact B1783259
  · exact B1783263
  · exact B1783267
  · exact B1783271
  · exact B1783275
  · exact B1783279
  · exact B1783283
  · exact B1783287
  · exact B1783291
  · exact B1783295
  · exact B1783299
  · exact B1783303
  · exact B1783307
  · exact B1783311
  · exact B1783315
  · exact B1783319
  · exact B1783323
  · exact B1783327
  · exact B1783331
  · exact B1783335
  · exact B1783339
  · exact B1783343
  · exact B1783347
  · exact B1783351
  · exact B1783355
  · exact B1783359
  · exact B1783363
  · exact B1783367
  · exact B1783371
  · exact B1783375
  · exact B1783379
  · exact B1783383
  · exact B1783387
  · exact B1783391
  · exact B1783395
  · exact B1783399
  · exact B1783403
  · exact B1783407
  · exact B1783411
  · exact B1783415
  · exact B1783419
  · exact B1783423
  · exact B1783427
  · exact B1783431
  · exact B1783435
  · exact B1783439
  · exact B1783443
  · exact B1783447
  · exact B1783451
  · exact B1783455
  · exact B1783459
  · exact B1783463
  · exact B1783467
  · exact B1783471
  · exact B1783475
  · exact B1783479
  · exact B1783483
  · exact B1783487
  · exact B1783491
  · exact B1783495
  · exact B1783499
  · exact B1783503
  · exact B1783507
  · exact B1783511
  · exact B1783515
  · exact B1783519
  · exact B1783523
  · exact B1783527
  · exact B1783531
  · exact B1783535
  · exact B1783539
  · exact B1783543
  · exact B1783547
  · exact B1783551
  · exact B1783555
  · exact B1783559
  · exact B1783563
  · exact B1783567
  · exact B1783571
  · exact B1783575
  · exact B1783579
  · exact B1783583
  · exact B1783587
  · exact B1783591
  · exact B1783595
  · exact B1783599
  · exact B1783603
  · exact B1783607
  · exact B1783611
  · exact B1783615
  · exact B1783619
  · exact B1783623
  · exact B1783627
  · exact B1783631
  · exact B1783635
  · exact B1783639
  · exact B1783643
  · exact B1783647
  · exact B1783651
  · exact B1783655
  · exact B1783659
  · exact B1783663
  · exact B1783667
  · exact B1783671
  · exact B1783675
  · exact B1783679
  · exact B1783683
  · exact B1783687
  · exact B1783691
  · exact B1783695
  · exact B1783699
  · exact B1783703
  · exact B1783707
  · exact B1783711
  · exact B1783715
  · exact B1783719
  · exact B1783723
  · exact B1783727
  · exact B1783731
  · exact B1783735
  · exact B1783739
  · exact B1783743
  · exact B1783747
  · exact B1783751
  · exact B1783755
  · exact B1783759
  · exact B1783763
  · exact B1783767
  · exact B1783771
  · exact B1783775
  · exact B1783779
  · exact B1783783
  · exact B1783787
  · exact B1783791
  · exact B1783795
  · exact B1783799
  · exact B1783803
  · exact B1783807
  · exact B1783811
  · exact B1783815
  · exact B1783819
  · exact B1783823
  · exact B1783827
  · exact B1783831
  · exact B1783835
  · exact B1783839
  · exact B1783843
  · exact B1783847
  · exact B1783851
  · exact B1783855
  · exact B1783859
  · exact B1783863
  · exact B1783867
  · exact B1783871
  · exact B1783875
  · exact B1783879
  · exact B1783883
  · exact B1783887
  · exact B1783891
  · exact B1783895
  · exact B1783899
  · exact B1783903
  · exact B1783907
  · exact B1783911
  · exact B1783915
  · exact B1783919
  · exact B1783923
  · exact B1783927
  · exact B1783931
  · exact B1783935
  · exact B1783939
  · exact B1783943
  · exact B1783947
  · exact B1783951
  · exact B1783955
  · exact B1783959
  · exact B1783963
  · exact B1783967
  · exact B1783971
  · exact B1783975
  · exact B1783979
  · exact B1783983
  · exact B1783987
  · exact B1783991
  · exact B1783995
  · exact B1783999
  · exact B1784003
  · exact B1784007
  · exact B1784011
  · exact B1784015
  · exact B1784019
  · exact B1784023
  · exact B1784027
  · exact B1784031
  · exact B1784035
  · exact B1784039
  · exact B1784043
  · exact B1784047
  · exact B1784051
  · exact B1784055
  · exact B1784059
  · exact B1784063
  · exact B1784067
  · exact B1784071
  · exact B1784075
  · exact B1784079
  · exact B1784083
  · exact B1784087
  · exact B1784091

theorem solution (m : ℕ) (hlo : 1782092 ≤ m) (hhi : m ≤ 1784092) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 445523 ≤ j := by omega
    have hj2 : j ≤ 446022 := by omega
    have hb : Blo 1782092 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
