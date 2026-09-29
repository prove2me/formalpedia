-- Prove2me | solution 1 for syracuse_descends_range_1845624_1847624
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:05:19.002943+00:00
-- url     : https://prove2.me/submissions/4e78d9ac-1664-470a-896d-daa65257b7c4

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


theorem B5259269 : Blo 1845624 5259269 := bbase (se 4 (by rfl) ⟨493056, by rfl⟩ : syracuseStep 5259269 = 986113) (by norm_num)
theorem B2768909 : Blo 1845624 2768909 := bbase (se 3 (by rfl) ⟨519170, by rfl⟩ : syracuseStep 2768909 = 1038341) (by norm_num)
theorem B4153373 : Blo 1845624 4153373 := bbase (se 3 (by rfl) ⟨778757, by rfl⟩ : syracuseStep 4153373 = 1557515) (by norm_num)
theorem B2768933 : Blo 1845624 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B2768957 : Blo 1845624 2768957 := bbase (se 3 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 2768957 = 1038359) (by norm_num)
theorem B2768981 : Blo 1845624 2768981 := bbase (se 8 (by rfl) ⟨16224, by rfl⟩ : syracuseStep 2768981 = 32449) (by norm_num)
theorem B4153445 : Blo 1845624 4153445 := bbase (se 4 (by rfl) ⟨389385, by rfl⟩ : syracuseStep 4153445 = 778771) (by norm_num)
theorem B8872037 : Blo 1845624 8872037 := bbase (se 4 (by rfl) ⟨831753, by rfl⟩ : syracuseStep 8872037 = 1663507) (by norm_num)
theorem B2769005 : Blo 1845624 2769005 := bbase (se 3 (by rfl) ⟨519188, by rfl⟩ : syracuseStep 2769005 = 1038377) (by norm_num)
theorem B2769029 : Blo 1845624 2769029 := bbase (se 4 (by rfl) ⟨259596, by rfl⟩ : syracuseStep 2769029 = 519193) (by norm_num)
theorem B6234245 : Blo 1845624 6234245 := bbase (se 4 (by rfl) ⟨584460, by rfl⟩ : syracuseStep 6234245 = 1168921) (by norm_num)
theorem B2769053 : Blo 1845624 2769053 := bbase (se 3 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 2769053 = 1038395) (by norm_num)
theorem B9347237 : Blo 1845624 9347237 := bbase (se 4 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 9347237 = 1752607) (by norm_num)
theorem B4153517 : Blo 1845624 4153517 := bbase (se 3 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 4153517 = 1557569) (by norm_num)
theorem B2769077 : Blo 1845624 2769077 := bbase (se 5 (by rfl) ⟨129800, by rfl⟩ : syracuseStep 2769077 = 259601) (by norm_num)
theorem B2769101 : Blo 1845624 2769101 := bbase (se 3 (by rfl) ⟨519206, by rfl⟩ : syracuseStep 2769101 = 1038413) (by norm_num)
theorem B14016725 : Blo 1845624 14016725 := bbase (se 7 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 14016725 = 328517) (by norm_num)
theorem B2769125 : Blo 1845624 2769125 := bbase (se 4 (by rfl) ⟨259605, by rfl⟩ : syracuseStep 2769125 = 519211) (by norm_num)
theorem B2105573 : Blo 1845624 2105573 := bbase (se 4 (by rfl) ⟨197397, by rfl⟩ : syracuseStep 2105573 = 394795) (by norm_num)
theorem B4153589 : Blo 1845624 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B2769149 : Blo 1845624 2769149 := bbase (se 3 (by rfl) ⟨519215, by rfl⟩ : syracuseStep 2769149 = 1038431) (by norm_num)
theorem B3506429 : Blo 1845624 3506429 := bbase (se 3 (by rfl) ⟨657455, by rfl⟩ : syracuseStep 3506429 = 1314911) (by norm_num)
theorem B2769173 : Blo 1845624 2769173 := bbase (se 6 (by rfl) ⟨64902, by rfl⟩ : syracuseStep 2769173 = 129805) (by norm_num)
theorem B2105633 : Blo 1845624 2105633 := bbase (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) (by norm_num)
theorem B2769197 : Blo 1845624 2769197 := bbase (se 3 (by rfl) ⟨519224, by rfl⟩ : syracuseStep 2769197 = 1038449) (by norm_num)
theorem B4153661 : Blo 1845624 4153661 := bbase (se 3 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 4153661 = 1557623) (by norm_num)
theorem B2769221 : Blo 1845624 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B2769245 : Blo 1845624 2769245 := bbase (se 3 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 2769245 = 1038467) (by norm_num)
theorem B2769269 : Blo 1845624 2769269 := bbase (se 5 (by rfl) ⟨129809, by rfl⟩ : syracuseStep 2769269 = 259619) (by norm_num)
theorem B4153733 : Blo 1845624 4153733 := bbase (se 4 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 4153733 = 778825) (by norm_num)
theorem B2769293 : Blo 1845624 2769293 := bbase (se 3 (by rfl) ⟨519242, by rfl⟩ : syracuseStep 2769293 = 1038485) (by norm_num)
theorem B3506581 : Blo 1845624 3506581 := bbase (se 6 (by rfl) ⟨82185, by rfl⟩ : syracuseStep 3506581 = 164371) (by norm_num)
theorem B2769317 : Blo 1845624 2769317 := bbase (se 4 (by rfl) ⟨259623, by rfl⟩ : syracuseStep 2769317 = 519247) (by norm_num)
theorem B2769341 : Blo 1845624 2769341 := bbase (se 3 (by rfl) ⟨519251, by rfl⟩ : syracuseStep 2769341 = 1038503) (by norm_num)
theorem B4153805 : Blo 1845624 4153805 := bbase (se 3 (by rfl) ⟨778838, by rfl⟩ : syracuseStep 4153805 = 1557677) (by norm_num)
theorem B2769365 : Blo 1845624 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B6316501 : Blo 1845624 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B2769389 : Blo 1845624 2769389 := bbase (se 3 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 2769389 = 1038521) (by norm_num)
theorem B2769413 : Blo 1845624 2769413 := bbase (se 4 (by rfl) ⟨259632, by rfl⟩ : syracuseStep 2769413 = 519265) (by norm_num)
theorem B4153877 : Blo 1845624 4153877 := bbase (se 6 (by rfl) ⟨97356, by rfl⟩ : syracuseStep 4153877 = 194713) (by norm_num)
theorem B2769437 : Blo 1845624 2769437 := bbase (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) (by norm_num)
theorem B2769461 : Blo 1845624 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B6234677 : Blo 1845624 6234677 := bbase (se 5 (by rfl) ⟨292250, by rfl⟩ : syracuseStep 6234677 = 584501) (by norm_num)
theorem B2769485 : Blo 1845624 2769485 := bbase (se 3 (by rfl) ⟨519278, by rfl⟩ : syracuseStep 2769485 = 1038557) (by norm_num)
theorem B4153949 : Blo 1845624 4153949 := bbase (se 3 (by rfl) ⟨778865, by rfl⟩ : syracuseStep 4153949 = 1557731) (by norm_num)
theorem B2769509 : Blo 1845624 2769509 := bbase (se 4 (by rfl) ⟨259641, by rfl⟩ : syracuseStep 2769509 = 519283) (by norm_num)
theorem B3326581 : Blo 1845624 3326581 := bbase (se 5 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 3326581 = 311867) (by norm_num)
theorem B2769533 : Blo 1845624 2769533 := bbase (se 3 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 2769533 = 1038575) (by norm_num)
theorem B2769557 : Blo 1845624 2769557 := bbase (se 6 (by rfl) ⟨64911, by rfl⟩ : syracuseStep 2769557 = 129823) (by norm_num)
theorem B4154021 : Blo 1845624 4154021 := bbase (se 4 (by rfl) ⟨389439, by rfl⟩ : syracuseStep 4154021 = 778879) (by norm_num)
theorem B5259941 : Blo 1845624 5259941 := bbase (se 4 (by rfl) ⟨493119, by rfl⟩ : syracuseStep 5259941 = 986239) (by norm_num)
theorem B2769581 : Blo 1845624 2769581 := bbase (se 3 (by rfl) ⟨519296, by rfl⟩ : syracuseStep 2769581 = 1038593) (by norm_num)
theorem B2769605 : Blo 1845624 2769605 := bbase (se 4 (by rfl) ⟨259650, by rfl⟩ : syracuseStep 2769605 = 519301) (by norm_num)
theorem B3506885 : Blo 1845624 3506885 := bbase (se 4 (by rfl) ⟨328770, by rfl⟩ : syracuseStep 3506885 = 657541) (by norm_num)
theorem B2769629 : Blo 1845624 2769629 := bbase (se 3 (by rfl) ⟨519305, by rfl⟩ : syracuseStep 2769629 = 1038611) (by norm_num)
theorem B4154093 : Blo 1845624 4154093 := bbase (se 3 (by rfl) ⟨778892, by rfl⟩ : syracuseStep 4154093 = 1557785) (by norm_num)
theorem B4211437 : Blo 1845624 4211437 := bbase (se 3 (by rfl) ⟨789644, by rfl⟩ : syracuseStep 4211437 = 1579289) (by norm_num)
theorem B2769653 : Blo 1845624 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B2769677 : Blo 1845624 2769677 := bbase (se 3 (by rfl) ⟨519314, by rfl⟩ : syracuseStep 2769677 = 1038629) (by norm_num)
theorem B2769701 : Blo 1845624 2769701 := bbase (se 4 (by rfl) ⟨259659, by rfl⟩ : syracuseStep 2769701 = 519319) (by norm_num)
theorem B2106157 : Blo 1845624 2106157 := bbase (se 3 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 2106157 = 789809) (by norm_num)
theorem B4154165 : Blo 1845624 4154165 := bbase (se 5 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 4154165 = 389453) (by norm_num)
theorem B2769725 : Blo 1845624 2769725 := bbase (se 3 (by rfl) ⟨519323, by rfl⟩ : syracuseStep 2769725 = 1038647) (by norm_num)
theorem B2769749 : Blo 1845624 2769749 := bbase (se 9 (by rfl) ⟨8114, by rfl⟩ : syracuseStep 2769749 = 16229) (by norm_num)
theorem B2769773 : Blo 1845624 2769773 := bbase (se 3 (by rfl) ⟨519332, by rfl⟩ : syracuseStep 2769773 = 1038665) (by norm_num)
theorem B4154237 : Blo 1845624 4154237 := bbase (se 3 (by rfl) ⟨778919, by rfl⟩ : syracuseStep 4154237 = 1557839) (by norm_num)
theorem B4989829 : Blo 1845624 4989829 := bbase (se 4 (by rfl) ⟨467796, by rfl⟩ : syracuseStep 4989829 = 935593) (by norm_num)
theorem B2769797 : Blo 1845624 2769797 := bbase (se 4 (by rfl) ⟨259668, by rfl⟩ : syracuseStep 2769797 = 519337) (by norm_num)
theorem B2769821 : Blo 1845624 2769821 := bbase (se 3 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 2769821 = 1038683) (by norm_num)
theorem B2769845 : Blo 1845624 2769845 := bbase (se 5 (by rfl) ⟨129836, by rfl⟩ : syracuseStep 2769845 = 259673) (by norm_num)
theorem B4154309 : Blo 1845624 4154309 := bbase (se 4 (by rfl) ⟨389466, by rfl⟩ : syracuseStep 4154309 = 778933) (by norm_num)
theorem B2769869 : Blo 1845624 2769869 := bbase (se 3 (by rfl) ⟨519350, by rfl⟩ : syracuseStep 2769869 = 1038701) (by norm_num)
theorem B2769893 : Blo 1845624 2769893 := bbase (se 4 (by rfl) ⟨259677, by rfl⟩ : syracuseStep 2769893 = 519355) (by norm_num)
theorem B6235109 : Blo 1845624 6235109 := bbase (se 4 (by rfl) ⟨584541, by rfl⟩ : syracuseStep 6235109 = 1169083) (by norm_num)
theorem B2769917 : Blo 1845624 2769917 := bbase (se 3 (by rfl) ⟨519359, by rfl⟩ : syracuseStep 2769917 = 1038719) (by norm_num)
theorem B4154381 : Blo 1845624 4154381 := bbase (se 3 (by rfl) ⟨778946, by rfl⟩ : syracuseStep 4154381 = 1557893) (by norm_num)
theorem B2769941 : Blo 1845624 2769941 := bbase (se 6 (by rfl) ⟨64920, by rfl⟩ : syracuseStep 2769941 = 129841) (by norm_num)
theorem B3744805 : Blo 1845624 3744805 := bbase (se 4 (by rfl) ⟨351075, by rfl⟩ : syracuseStep 3744805 = 702151) (by norm_num)
theorem B2769965 : Blo 1845624 2769965 := bbase (se 3 (by rfl) ⟨519368, by rfl⟩ : syracuseStep 2769965 = 1038737) (by norm_num)
theorem B5915717 : Blo 1845624 5915717 := bbase (se 4 (by rfl) ⟨554598, by rfl⟩ : syracuseStep 5915717 = 1109197) (by norm_num)
theorem B2769989 : Blo 1845624 2769989 := bbase (se 4 (by rfl) ⟨259686, by rfl⟩ : syracuseStep 2769989 = 519373) (by norm_num)
theorem B4154453 : Blo 1845624 4154453 := bbase (se 8 (by rfl) ⟨24342, by rfl⟩ : syracuseStep 4154453 = 48685) (by norm_num)
theorem B5260373 : Blo 1845624 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B2770013 : Blo 1845624 2770013 := bbase (se 3 (by rfl) ⟨519377, by rfl⟩ : syracuseStep 2770013 = 1038755) (by norm_num)
theorem B2770037 : Blo 1845624 2770037 := bbase (se 5 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 2770037 = 259691) (by norm_num)
theorem B2958461 : Blo 1845624 2958461 := bbase (se 3 (by rfl) ⟨554711, by rfl⟩ : syracuseStep 2958461 = 1109423) (by norm_num)
theorem B2335873 : Blo 1845624 2335873 := bbase (se 2 (by rfl) ⟨875952, by rfl⟩ : syracuseStep 2335873 = 1751905) (by norm_num)
theorem B2770061 : Blo 1845624 2770061 := bbase (se 3 (by rfl) ⟨519386, by rfl⟩ : syracuseStep 2770061 = 1038773) (by norm_num)
theorem B4154525 : Blo 1845624 4154525 := bbase (se 3 (by rfl) ⟨778973, by rfl⟩ : syracuseStep 4154525 = 1557947) (by norm_num)
theorem B2770085 : Blo 1845624 2770085 := bbase (se 4 (by rfl) ⟨259695, by rfl⟩ : syracuseStep 2770085 = 519391) (by norm_num)
theorem B2770109 : Blo 1845624 2770109 := bbase (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) (by norm_num)
theorem B7013573 : Blo 1845624 7013573 := bbase (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) (by norm_num)
theorem B2770133 : Blo 1845624 2770133 := bbase (se 7 (by rfl) ⟨32462, by rfl⟩ : syracuseStep 2770133 = 64925) (by norm_num)
theorem B2335969 : Blo 1845624 2335969 := bbase (se 2 (by rfl) ⟨875988, by rfl⟩ : syracuseStep 2335969 = 1751977) (by norm_num)
theorem B4154597 : Blo 1845624 4154597 := bbase (se 4 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 4154597 = 778987) (by norm_num)
theorem B7890149 : Blo 1845624 7890149 := bbase (se 4 (by rfl) ⟨739701, by rfl⟩ : syracuseStep 7890149 = 1479403) (by norm_num)
theorem B2770157 : Blo 1845624 2770157 := bbase (se 3 (by rfl) ⟨519404, by rfl⟩ : syracuseStep 2770157 = 1038809) (by norm_num)
theorem B2770181 : Blo 1845624 2770181 := bbase (se 4 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 2770181 = 519409) (by norm_num)
theorem B3327245 : Blo 1845624 3327245 := bbase (se 3 (by rfl) ⟨623858, by rfl⟩ : syracuseStep 3327245 = 1247717) (by norm_num)
theorem B2770205 : Blo 1845624 2770205 := bbase (se 3 (by rfl) ⟨519413, by rfl⟩ : syracuseStep 2770205 = 1038827) (by norm_num)
theorem B4154669 : Blo 1845624 4154669 := bbase (se 3 (by rfl) ⟨779000, by rfl⟩ : syracuseStep 4154669 = 1558001) (by norm_num)
theorem B2770229 : Blo 1845624 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B2958653 : Blo 1845624 2958653 := bbase (se 3 (by rfl) ⟨554747, by rfl⟩ : syracuseStep 2958653 = 1109495) (by norm_num)
theorem B2770253 : Blo 1845624 2770253 := bbase (se 3 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 2770253 = 1038845) (by norm_num)
theorem B2770277 : Blo 1845624 2770277 := bbase (se 4 (by rfl) ⟨259713, by rfl⟩ : syracuseStep 2770277 = 519427) (by norm_num)
theorem B4154741 : Blo 1845624 4154741 := bbase (se 5 (by rfl) ⟨194753, by rfl⟩ : syracuseStep 4154741 = 389507) (by norm_num)
theorem B2770301 : Blo 1845624 2770301 := bbase (se 3 (by rfl) ⟨519431, by rfl⟩ : syracuseStep 2770301 = 1038863) (by norm_num)
theorem B2336141 : Blo 1845624 2336141 := bbase (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) (by norm_num)
theorem B2770325 : Blo 1845624 2770325 := bbase (se 6 (by rfl) ⟨64929, by rfl⟩ : syracuseStep 2770325 = 129859) (by norm_num)
theorem B6235541 : Blo 1845624 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B3327389 : Blo 1845624 3327389 := bbase (se 3 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 3327389 = 1247771) (by norm_num)
theorem B2770349 : Blo 1845624 2770349 := bbase (se 3 (by rfl) ⟨519440, by rfl⟩ : syracuseStep 2770349 = 1038881) (by norm_num)
theorem B9348533 : Blo 1845624 9348533 := bbase (se 5 (by rfl) ⟨438212, by rfl⟩ : syracuseStep 9348533 = 876425) (by norm_num)
theorem B4154813 : Blo 1845624 4154813 := bbase (se 3 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 4154813 = 1558055) (by norm_num)
theorem B2958781 : Blo 1845624 2958781 := bbase (se 3 (by rfl) ⟨554771, by rfl⟩ : syracuseStep 2958781 = 1109543) (by norm_num)
theorem B2336197 : Blo 1845624 2336197 := bbase (se 4 (by rfl) ⟨219018, by rfl⟩ : syracuseStep 2336197 = 438037) (by norm_num)
theorem B2770373 : Blo 1845624 2770373 := bbase (se 4 (by rfl) ⟨259722, by rfl⟩ : syracuseStep 2770373 = 519445) (by norm_num)
theorem B2770397 : Blo 1845624 2770397 := bbase (se 3 (by rfl) ⟨519449, by rfl⟩ : syracuseStep 2770397 = 1038899) (by norm_num)
theorem B7013861 : Blo 1845624 7013861 := bbase (se 4 (by rfl) ⟨657549, by rfl⟩ : syracuseStep 7013861 = 1315099) (by norm_num)
theorem B2770421 : Blo 1845624 2770421 := bbase (se 5 (by rfl) ⟨129863, by rfl⟩ : syracuseStep 2770421 = 259727) (by norm_num)
theorem B4154885 : Blo 1845624 4154885 := bbase (se 4 (by rfl) ⟨389520, by rfl⟩ : syracuseStep 4154885 = 779041) (by norm_num)
theorem B2770445 : Blo 1845624 2770445 := bbase (se 3 (by rfl) ⟨519458, by rfl⟩ : syracuseStep 2770445 = 1038917) (by norm_num)
theorem B3114517 : Blo 1845624 3114517 := bbase (se 6 (by rfl) ⟨72996, by rfl⟩ : syracuseStep 3114517 = 145993) (by norm_num)
theorem B2336293 : Blo 1845624 2336293 := bbase (se 4 (by rfl) ⟨219027, by rfl⟩ : syracuseStep 2336293 = 438055) (by norm_num)
theorem B2770469 : Blo 1845624 2770469 := bbase (se 4 (by rfl) ⟨259731, by rfl⟩ : syracuseStep 2770469 = 519463) (by norm_num)
theorem B2770493 : Blo 1845624 2770493 := bbase (se 3 (by rfl) ⟨519467, by rfl⟩ : syracuseStep 2770493 = 1038935) (by norm_num)
theorem B4154957 : Blo 1845624 4154957 := bbase (se 3 (by rfl) ⟨779054, by rfl⟩ : syracuseStep 4154957 = 1558109) (by norm_num)
theorem B2770517 : Blo 1845624 2770517 := bbase (se 8 (by rfl) ⟨16233, by rfl⟩ : syracuseStep 2770517 = 32467) (by norm_num)
theorem B3114605 : Blo 1845624 3114605 := bbase (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) (by norm_num)
theorem B2770541 : Blo 1845624 2770541 := bbase (se 3 (by rfl) ⟨519476, by rfl⟩ : syracuseStep 2770541 = 1038953) (by norm_num)
theorem B2770565 : Blo 1845624 2770565 := bbase (se 4 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 2770565 = 519481) (by norm_num)
theorem B4155029 : Blo 1845624 4155029 := bbase (se 6 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 4155029 = 194767) (by norm_num)
theorem B2770589 : Blo 1845624 2770589 := bbase (se 3 (by rfl) ⟨519485, by rfl⟩ : syracuseStep 2770589 = 1038971) (by norm_num)
theorem B4621997 : Blo 1845624 4621997 := bbase (se 3 (by rfl) ⟨866624, by rfl⟩ : syracuseStep 4621997 = 1733249) (by norm_num)
theorem B2770613 : Blo 1845624 2770613 := bbase (se 5 (by rfl) ⟨129872, by rfl⟩ : syracuseStep 2770613 = 259745) (by norm_num)
theorem B2770637 : Blo 1845624 2770637 := bbase (se 3 (by rfl) ⟨519494, by rfl⟩ : syracuseStep 2770637 = 1038989) (by norm_num)
theorem B2336465 : Blo 1845624 2336465 := bbase (se 2 (by rfl) ⟨876174, by rfl⟩ : syracuseStep 2336465 = 1752349) (by norm_num)
theorem B4155101 : Blo 1845624 4155101 := bbase (se 3 (by rfl) ⟨779081, by rfl⟩ : syracuseStep 4155101 = 1558163) (by norm_num)
theorem B2770661 : Blo 1845624 2770661 := bbase (se 4 (by rfl) ⟨259749, by rfl⟩ : syracuseStep 2770661 = 519499) (by norm_num)
theorem B3114733 : Blo 1845624 3114733 := bbase (se 3 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 3114733 = 1168025) (by norm_num)
theorem B2770685 : Blo 1845624 2770685 := bbase (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) (by norm_num)
theorem B2336521 : Blo 1845624 2336521 := bbase (se 2 (by rfl) ⟨876195, by rfl⟩ : syracuseStep 2336521 = 1752391) (by norm_num)
theorem B2770709 : Blo 1845624 2770709 := bbase (se 6 (by rfl) ⟨64938, by rfl⟩ : syracuseStep 2770709 = 129877) (by norm_num)
theorem B4155173 : Blo 1845624 4155173 := bbase (se 4 (by rfl) ⟨389547, by rfl⟩ : syracuseStep 4155173 = 779095) (by norm_num)
theorem B2770733 : Blo 1845624 2770733 := bbase (se 3 (by rfl) ⟨519512, by rfl⟩ : syracuseStep 2770733 = 1039025) (by norm_num)
theorem B3114821 : Blo 1845624 3114821 := bbase (se 4 (by rfl) ⟨292014, by rfl⟩ : syracuseStep 3114821 = 584029) (by norm_num)
theorem B5916485 : Blo 1845624 5916485 := bbase (se 4 (by rfl) ⟨554670, by rfl⟩ : syracuseStep 5916485 = 1109341) (by norm_num)
theorem B2770757 : Blo 1845624 2770757 := bbase (se 4 (by rfl) ⟨259758, by rfl⟩ : syracuseStep 2770757 = 519517) (by norm_num)
theorem B5261125 : Blo 1845624 5261125 := bbase (se 4 (by rfl) ⟨493230, by rfl⟩ : syracuseStep 5261125 = 986461) (by norm_num)
theorem B2770781 : Blo 1845624 2770781 := bbase (se 3 (by rfl) ⟨519521, by rfl⟩ : syracuseStep 2770781 = 1039043) (by norm_num)
theorem B2336617 : Blo 1845624 2336617 := bbase (se 2 (by rfl) ⟨876231, by rfl⟩ : syracuseStep 2336617 = 1752463) (by norm_num)
theorem B4155245 : Blo 1845624 4155245 := bbase (se 3 (by rfl) ⟨779108, by rfl⟩ : syracuseStep 4155245 = 1558217) (by norm_num)
theorem B13313909 : Blo 1845624 13313909 := bbase (se 5 (by rfl) ⟨624089, by rfl⟩ : syracuseStep 13313909 = 1248179) (by norm_num)
theorem B2770805 : Blo 1845624 2770805 := bbase (se 5 (by rfl) ⟨129881, by rfl⟩ : syracuseStep 2770805 = 259763) (by norm_num)
theorem B2770829 : Blo 1845624 2770829 := bbase (se 3 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 2770829 = 1039061) (by norm_num)
theorem B2770853 : Blo 1845624 2770853 := bbase (se 4 (by rfl) ⟨259767, by rfl⟩ : syracuseStep 2770853 = 519535) (by norm_num)
theorem B4155317 : Blo 1845624 4155317 := bbase (se 5 (by rfl) ⟨194780, by rfl⟩ : syracuseStep 4155317 = 389561) (by norm_num)
theorem B2770877 : Blo 1845624 2770877 := bbase (se 3 (by rfl) ⟨519539, by rfl⟩ : syracuseStep 2770877 = 1039079) (by norm_num)
theorem B3114949 : Blo 1845624 3114949 := bbase (se 4 (by rfl) ⟨292026, by rfl⟩ : syracuseStep 3114949 = 584053) (by norm_num)
theorem B10512341 : Blo 1845624 10512341 := bbase (se 7 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 10512341 = 246383) (by norm_num)
theorem B2770901 : Blo 1845624 2770901 := bbase (se 7 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 2770901 = 64943) (by norm_num)
theorem B2770925 : Blo 1845624 2770925 := bbase (se 3 (by rfl) ⟨519548, by rfl⟩ : syracuseStep 2770925 = 1039097) (by norm_num)
theorem B4155389 : Blo 1845624 4155389 := bbase (se 3 (by rfl) ⟨779135, by rfl⟩ : syracuseStep 4155389 = 1558271) (by norm_num)
theorem B2770949 : Blo 1845624 2770949 := bbase (se 4 (by rfl) ⟨259776, by rfl⟩ : syracuseStep 2770949 = 519553) (by norm_num)
theorem B2336789 : Blo 1845624 2336789 := bbase (se 6 (by rfl) ⟨54768, by rfl⟩ : syracuseStep 2336789 = 109537) (by norm_num)
theorem B3115037 : Blo 1845624 3115037 := bbase (se 3 (by rfl) ⟨584069, by rfl⟩ : syracuseStep 3115037 = 1168139) (by norm_num)
theorem B2770973 : Blo 1845624 2770973 := bbase (se 3 (by rfl) ⟨519557, by rfl⟩ : syracuseStep 2770973 = 1039115) (by norm_num)
theorem B2770997 : Blo 1845624 2770997 := bbase (se 5 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 2770997 = 259781) (by norm_num)
theorem B2959421 : Blo 1845624 2959421 := bbase (se 3 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 2959421 = 1109783) (by norm_num)
theorem B4155461 : Blo 1845624 4155461 := bbase (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) (by norm_num)
theorem B2336845 : Blo 1845624 2336845 := bbase (se 3 (by rfl) ⟨438158, by rfl⟩ : syracuseStep 2336845 = 876317) (by norm_num)
theorem B2771021 : Blo 1845624 2771021 := bbase (se 3 (by rfl) ⟨519566, by rfl⟩ : syracuseStep 2771021 = 1039133) (by norm_num)
theorem B2771045 : Blo 1845624 2771045 := bbase (se 4 (by rfl) ⟨259785, by rfl⟩ : syracuseStep 2771045 = 519571) (by norm_num)
theorem B7104629 : Blo 1845624 7104629 := bbase (se 5 (by rfl) ⟨333029, by rfl⟩ : syracuseStep 7104629 = 666059) (by norm_num)
theorem B2771069 : Blo 1845624 2771069 := bbase (se 3 (by rfl) ⟨519575, by rfl⟩ : syracuseStep 2771069 = 1039151) (by norm_num)
theorem B4155533 : Blo 1845624 4155533 := bbase (se 3 (by rfl) ⟨779162, by rfl⟩ : syracuseStep 4155533 = 1558325) (by norm_num)
theorem B2771093 : Blo 1845624 2771093 := bbase (se 6 (by rfl) ⟨64947, by rfl⟩ : syracuseStep 2771093 = 129895) (by norm_num)
theorem B3115165 : Blo 1845624 3115165 := bbase (se 3 (by rfl) ⟨584093, by rfl⟩ : syracuseStep 3115165 = 1168187) (by norm_num)
theorem B2336941 : Blo 1845624 2336941 := bbase (se 3 (by rfl) ⟨438176, by rfl⟩ : syracuseStep 2336941 = 876353) (by norm_num)
theorem B2771117 : Blo 1845624 2771117 := bbase (se 3 (by rfl) ⟨519584, by rfl⟩ : syracuseStep 2771117 = 1039169) (by norm_num)
theorem B7104709 : Blo 1845624 7104709 := bbase (se 4 (by rfl) ⟨666066, by rfl⟩ : syracuseStep 7104709 = 1332133) (by norm_num)
theorem B8423621 : Blo 1845624 8423621 := bbase (se 4 (by rfl) ⟨789714, by rfl⟩ : syracuseStep 8423621 = 1579429) (by norm_num)
theorem B7891141 : Blo 1845624 7891141 := bbase (se 4 (by rfl) ⟨739794, by rfl⟩ : syracuseStep 7891141 = 1479589) (by norm_num)
theorem B2771141 : Blo 1845624 2771141 := bbase (se 4 (by rfl) ⟨259794, by rfl⟩ : syracuseStep 2771141 = 519589) (by norm_num)
theorem B44902613 : Blo 1845624 44902613 := bbase (se 7 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 44902613 = 1052405) (by norm_num)
theorem B4155605 : Blo 1845624 4155605 := bbase (se 7 (by rfl) ⟨48698, by rfl⟩ : syracuseStep 4155605 = 97397) (by norm_num)
theorem B2771165 : Blo 1845624 2771165 := bbase (se 3 (by rfl) ⟨519593, by rfl⟩ : syracuseStep 2771165 = 1039187) (by norm_num)
theorem B3115253 : Blo 1845624 3115253 := bbase (se 5 (by rfl) ⟨146027, by rfl⟩ : syracuseStep 3115253 = 292055) (by norm_num)
theorem B2771189 : Blo 1845624 2771189 := bbase (se 5 (by rfl) ⟨129899, by rfl⟩ : syracuseStep 2771189 = 259799) (by norm_num)
theorem B2771213 : Blo 1845624 2771213 := bbase (se 3 (by rfl) ⟨519602, by rfl⟩ : syracuseStep 2771213 = 1039205) (by norm_num)
theorem B4155677 : Blo 1845624 4155677 := bbase (se 3 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 4155677 = 1558379) (by norm_num)
theorem B2771237 : Blo 1845624 2771237 := bbase (se 4 (by rfl) ⟨259803, by rfl⟩ : syracuseStep 2771237 = 519607) (by norm_num)
theorem B2771261 : Blo 1845624 2771261 := bbase (se 3 (by rfl) ⟨519611, by rfl⟩ : syracuseStep 2771261 = 1039223) (by norm_num)
theorem B5916997 : Blo 1845624 5916997 := bbase (se 4 (by rfl) ⟨554718, by rfl⟩ : syracuseStep 5916997 = 1109437) (by norm_num)
theorem B2771285 : Blo 1845624 2771285 := bbase (se 10 (by rfl) ⟨4059, by rfl⟩ : syracuseStep 2771285 = 8119) (by norm_num)
theorem B2337113 : Blo 1845624 2337113 := bbase (se 2 (by rfl) ⟨876417, by rfl⟩ : syracuseStep 2337113 = 1752835) (by norm_num)
theorem B4155749 : Blo 1845624 4155749 := bbase (se 4 (by rfl) ⟨389601, by rfl⟩ : syracuseStep 4155749 = 779203) (by norm_num)
theorem B2771309 : Blo 1845624 2771309 := bbase (se 3 (by rfl) ⟨519620, by rfl⟩ : syracuseStep 2771309 = 1039241) (by norm_num)
theorem B11225461 : Blo 1845624 11225461 := bbase (se 5 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 11225461 = 1052387) (by norm_num)
theorem B3115381 : Blo 1845624 3115381 := bbase (se 5 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 3115381 = 292067) (by norm_num)
theorem B4671877 : Blo 1845624 4671877 := bbase (se 4 (by rfl) ⟨437988, by rfl⟩ : syracuseStep 4671877 = 875977) (by norm_num)
theorem B2771333 : Blo 1845624 2771333 := bbase (se 4 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 2771333 = 519625) (by norm_num)
theorem B2337169 : Blo 1845624 2337169 := bbase (se 2 (by rfl) ⟨876438, by rfl⟩ : syracuseStep 2337169 = 1752877) (by norm_num)
theorem B2369945 : Blo 1845624 2369945 := bbase (se 2 (by rfl) ⟨888729, by rfl⟩ : syracuseStep 2369945 = 1777459) (by norm_num)
theorem B2771357 : Blo 1845624 2771357 := bbase (se 3 (by rfl) ⟨519629, by rfl⟩ : syracuseStep 2771357 = 1039259) (by norm_num)
theorem B4155821 : Blo 1845624 4155821 := bbase (se 3 (by rfl) ⟨779216, by rfl⟩ : syracuseStep 4155821 = 1558433) (by norm_num)
theorem B2771381 : Blo 1845624 2771381 := bbase (se 5 (by rfl) ⟨129908, by rfl⟩ : syracuseStep 2771381 = 259817) (by norm_num)
theorem B4991429 : Blo 1845624 4991429 := bbase (se 4 (by rfl) ⟨467946, by rfl⟩ : syracuseStep 4991429 = 935893) (by norm_num)
theorem B3115469 : Blo 1845624 3115469 := bbase (se 3 (by rfl) ⟨584150, by rfl⟩ : syracuseStep 3115469 = 1168301) (by norm_num)
theorem B2771405 : Blo 1845624 2771405 := bbase (se 3 (by rfl) ⟨519638, by rfl⟩ : syracuseStep 2771405 = 1039277) (by norm_num)
theorem B2771429 : Blo 1845624 2771429 := bbase (se 4 (by rfl) ⟨259821, by rfl⟩ : syracuseStep 2771429 = 519643) (by norm_num)
theorem B2337265 : Blo 1845624 2337265 := bbase (se 2 (by rfl) ⟨876474, by rfl⟩ : syracuseStep 2337265 = 1752949) (by norm_num)
theorem B4671989 : Blo 1845624 4671989 := bbase (se 5 (by rfl) ⟨218999, by rfl⟩ : syracuseStep 4671989 = 437999) (by norm_num)
theorem B4155893 : Blo 1845624 4155893 := bbase (se 5 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 4155893 = 389615) (by norm_num)
theorem B4155965 : Blo 1845624 4155965 := bbase (se 3 (by rfl) ⟨779243, by rfl⟩ : syracuseStep 4155965 = 1558487) (by norm_num)
theorem B3115597 : Blo 1845624 3115597 := bbase (se 3 (by rfl) ⟨584174, by rfl⟩ : syracuseStep 3115597 = 1168349) (by norm_num)
theorem B4156037 : Blo 1845624 4156037 := bbase (se 4 (by rfl) ⟨389628, by rfl⟩ : syracuseStep 4156037 = 779257) (by norm_num)
theorem B7015045 : Blo 1845624 7015045 := bbase (se 4 (by rfl) ⟨657660, by rfl⟩ : syracuseStep 7015045 = 1315321) (by norm_num)
theorem B2337437 : Blo 1845624 2337437 := bbase (se 3 (by rfl) ⟨438269, by rfl⟩ : syracuseStep 2337437 = 876539) (by norm_num)
theorem B3115685 : Blo 1845624 3115685 := bbase (se 4 (by rfl) ⟨292095, by rfl⟩ : syracuseStep 3115685 = 584191) (by norm_num)
theorem B4672181 : Blo 1845624 4672181 := bbase (se 5 (by rfl) ⟨219008, by rfl⟩ : syracuseStep 4672181 = 438017) (by norm_num)
theorem B3943093 : Blo 1845624 3943093 := bbase (se 5 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 3943093 = 369665) (by norm_num)
theorem B9349829 : Blo 1845624 9349829 := bbase (se 4 (by rfl) ⟨876546, by rfl⟩ : syracuseStep 9349829 = 1753093) (by norm_num)
theorem B4156109 : Blo 1845624 4156109 := bbase (se 3 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 4156109 = 1558541) (by norm_num)
theorem B2337493 : Blo 1845624 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B17083093 : Blo 1845624 17083093 := bbase (se 7 (by rfl) ⟨200192, by rfl⟩ : syracuseStep 17083093 = 400385) (by norm_num)
theorem B26618645 : Blo 1845624 26618645 := bbase (se 6 (by rfl) ⟨623874, by rfl⟩ : syracuseStep 26618645 = 1247749) (by norm_num)
theorem B4156181 : Blo 1845624 4156181 := bbase (se 6 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 4156181 = 194821) (by norm_num)
theorem B3115813 : Blo 1845624 3115813 := bbase (se 4 (by rfl) ⟨292107, by rfl⟩ : syracuseStep 3115813 = 584215) (by norm_num)
theorem B5327669 : Blo 1845624 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B8874805 : Blo 1845624 8874805 := bbase (se 5 (by rfl) ⟨416006, by rfl⟩ : syracuseStep 8874805 = 832013) (by norm_num)
theorem B2337589 : Blo 1845624 2337589 := bbase (se 5 (by rfl) ⟨109574, by rfl⟩ : syracuseStep 2337589 = 219149) (by norm_num)
theorem B11832149 : Blo 1845624 11832149 := bbase (se 9 (by rfl) ⟨34664, by rfl⟩ : syracuseStep 11832149 = 69329) (by norm_num)
theorem B4156253 : Blo 1845624 4156253 := bbase (se 3 (by rfl) ⟨779297, by rfl⟩ : syracuseStep 4156253 = 1558595) (by norm_num)
theorem B3115901 : Blo 1845624 3115901 := bbase (se 3 (by rfl) ⟨584231, by rfl⟩ : syracuseStep 3115901 = 1168463) (by norm_num)
theorem B4156325 : Blo 1845624 4156325 := bbase (se 4 (by rfl) ⟨389655, by rfl⟩ : syracuseStep 4156325 = 779311) (by norm_num)
theorem B2337761 : Blo 1845624 2337761 := bbase (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) (by norm_num)
theorem B4156397 : Blo 1845624 4156397 := bbase (se 3 (by rfl) ⟨779324, by rfl⟩ : syracuseStep 4156397 = 1558649) (by norm_num)
theorem B3116029 : Blo 1845624 3116029 := bbase (se 3 (by rfl) ⟨584255, by rfl⟩ : syracuseStep 3116029 = 1168511) (by norm_num)
theorem B4672525 : Blo 1845624 4672525 := bbase (se 3 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 4672525 = 1752197) (by norm_num)
theorem B2337817 : Blo 1845624 2337817 := bbase (se 2 (by rfl) ⟨876681, by rfl⟩ : syracuseStep 2337817 = 1753363) (by norm_num)
theorem B13495349 : Blo 1845624 13495349 := bbase (se 5 (by rfl) ⟨632594, by rfl⟩ : syracuseStep 13495349 = 1265189) (by norm_num)
theorem B4156469 : Blo 1845624 4156469 := bbase (se 5 (by rfl) ⟨194834, by rfl⟩ : syracuseStep 4156469 = 389669) (by norm_num)
theorem B6229061 : Blo 1845624 6229061 := bbase (se 4 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 6229061 = 1167949) (by norm_num)
theorem B3116117 : Blo 1845624 3116117 := bbase (se 8 (by rfl) ⟨18258, by rfl⟩ : syracuseStep 3116117 = 36517) (by norm_num)
theorem B2337913 : Blo 1845624 2337913 := bbase (se 2 (by rfl) ⟨876717, by rfl⟩ : syracuseStep 2337913 = 1753435) (by norm_num)
theorem B4672637 : Blo 1845624 4672637 := bbase (se 3 (by rfl) ⟨876119, by rfl⟩ : syracuseStep 4672637 = 1752239) (by norm_num)
theorem B4156541 : Blo 1845624 4156541 := bbase (se 3 (by rfl) ⟨779351, by rfl⟩ : syracuseStep 4156541 = 1558703) (by norm_num)
theorem B3124373 : Blo 1845624 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B4156613 : Blo 1845624 4156613 := bbase (se 4 (by rfl) ⟨389682, by rfl⟩ : syracuseStep 4156613 = 779365) (by norm_num)
theorem B3116245 : Blo 1845624 3116245 := bbase (se 7 (by rfl) ⟨36518, by rfl⟩ : syracuseStep 3116245 = 73037) (by norm_num)
theorem B1871105 : Blo 1845624 1871105 := bbase (se 2 (by rfl) ⟨701664, by rfl⟩ : syracuseStep 1871105 = 1403329) (by norm_num)
theorem B4156685 : Blo 1845624 4156685 := bbase (se 3 (by rfl) ⟨779378, by rfl⟩ : syracuseStep 4156685 = 1558757) (by norm_num)
theorem B2338085 : Blo 1845624 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B3116333 : Blo 1845624 3116333 := bbase (se 3 (by rfl) ⟨584312, by rfl⟩ : syracuseStep 3116333 = 1168625) (by norm_num)
theorem B4672829 : Blo 1845624 4672829 := bbase (se 3 (by rfl) ⟨876155, by rfl⟩ : syracuseStep 4672829 = 1752311) (by norm_num)
theorem B4156757 : Blo 1845624 4156757 := bbase (se 11 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4156757 = 6089) (by norm_num)
theorem B2338141 : Blo 1845624 2338141 := bbase (se 3 (by rfl) ⟨438401, by rfl⟩ : syracuseStep 2338141 = 876803) (by norm_num)
theorem B3796325 : Blo 1845624 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B9981301 : Blo 1845624 9981301 := bbase (se 5 (by rfl) ⟨467873, by rfl⟩ : syracuseStep 9981301 = 935747) (by norm_num)
theorem B4156829 : Blo 1845624 4156829 := bbase (se 3 (by rfl) ⟨779405, by rfl⟩ : syracuseStep 4156829 = 1558811) (by norm_num)
theorem B3329437 : Blo 1845624 3329437 := bbase (se 3 (by rfl) ⟨624269, by rfl⟩ : syracuseStep 3329437 = 1248539) (by norm_num)
theorem B3116461 : Blo 1845624 3116461 := bbase (se 3 (by rfl) ⟨584336, by rfl⟩ : syracuseStep 3116461 = 1168673) (by norm_num)
theorem B2338237 : Blo 1845624 2338237 := bbase (se 3 (by rfl) ⟨438419, by rfl⟩ : syracuseStep 2338237 = 876839) (by norm_num)
theorem B4156901 : Blo 1845624 4156901 := bbase (se 4 (by rfl) ⟨389709, by rfl⟩ : syracuseStep 4156901 = 779419) (by norm_num)
theorem B6229493 : Blo 1845624 6229493 := bbase (se 5 (by rfl) ⟨292007, by rfl⟩ : syracuseStep 6229493 = 584015) (by norm_num)
theorem B3116549 : Blo 1845624 3116549 := bbase (se 4 (by rfl) ⟨292176, by rfl⟩ : syracuseStep 3116549 = 584353) (by norm_num)
theorem B3943981 : Blo 1845624 3943981 := bbase (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) (by norm_num)
theorem B4156973 : Blo 1845624 4156973 := bbase (se 3 (by rfl) ⟨779432, by rfl⟩ : syracuseStep 4156973 = 1558865) (by norm_num)
theorem B7884341 : Blo 1845624 7884341 := bbase (se 5 (by rfl) ⟨369578, by rfl⟩ : syracuseStep 7884341 = 739157) (by norm_num)
theorem B17985077 : Blo 1845624 17985077 := bbase (se 5 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 17985077 = 1686101) (by norm_num)
theorem B4157045 : Blo 1845624 4157045 := bbase (se 5 (by rfl) ⟨194861, by rfl⟩ : syracuseStep 4157045 = 389723) (by norm_num)
theorem B3116677 : Blo 1845624 3116677 := bbase (se 4 (by rfl) ⟨292188, by rfl⟩ : syracuseStep 3116677 = 584377) (by norm_num)
theorem B4673173 : Blo 1845624 4673173 := bbase (se 6 (by rfl) ⟨109527, by rfl⟩ : syracuseStep 4673173 = 219055) (by norm_num)
theorem B2076349 : Blo 1845624 2076349 := bbase (se 3 (by rfl) ⟨389315, by rfl⟩ : syracuseStep 2076349 = 778631) (by norm_num)
theorem B4157117 : Blo 1845624 4157117 := bbase (se 3 (by rfl) ⟨779459, by rfl⟩ : syracuseStep 4157117 = 1558919) (by norm_num)
theorem B3157709 : Blo 1845624 3157709 := bbase (se 3 (by rfl) ⟨592070, by rfl⟩ : syracuseStep 3157709 = 1184141) (by norm_num)
theorem B3116765 : Blo 1845624 3116765 := bbase (se 3 (by rfl) ⟨584393, by rfl⟩ : syracuseStep 3116765 = 1168787) (by norm_num)
theorem B2076385 : Blo 1845624 2076385 := bbase (se 2 (by rfl) ⟨778644, by rfl⟩ : syracuseStep 2076385 = 1557289) (by norm_num)
theorem B2076421 : Blo 1845624 2076421 := bbase (se 4 (by rfl) ⟨194664, by rfl⟩ : syracuseStep 2076421 = 389329) (by norm_num)
theorem B4673285 : Blo 1845624 4673285 := bbase (se 4 (by rfl) ⟨438120, by rfl⟩ : syracuseStep 4673285 = 876241) (by norm_num)
theorem B2076457 : Blo 1845624 2076457 := bbase (se 2 (by rfl) ⟨778671, by rfl⟩ : syracuseStep 2076457 = 1557343) (by norm_num)
theorem B2076493 : Blo 1845624 2076493 := bbase (se 3 (by rfl) ⟨389342, by rfl⟩ : syracuseStep 2076493 = 778685) (by norm_num)
theorem B3116893 : Blo 1845624 3116893 := bbase (se 3 (by rfl) ⟨584417, by rfl⟩ : syracuseStep 3116893 = 1168835) (by norm_num)
theorem B4165469 : Blo 1845624 4165469 := bbase (se 3 (by rfl) ⟨781025, by rfl⟩ : syracuseStep 4165469 = 1562051) (by norm_num)
theorem B2076529 : Blo 1845624 2076529 := bbase (se 2 (by rfl) ⟨778698, by rfl⟩ : syracuseStep 2076529 = 1557397) (by norm_num)
theorem B2076565 : Blo 1845624 2076565 := bbase (se 6 (by rfl) ⟨48669, by rfl⟩ : syracuseStep 2076565 = 97339) (by norm_num)
theorem B6229925 : Blo 1845624 6229925 := bbase (se 4 (by rfl) ⟨584055, by rfl⟩ : syracuseStep 6229925 = 1168111) (by norm_num)
theorem B3116981 : Blo 1845624 3116981 := bbase (se 5 (by rfl) ⟨146108, by rfl⟩ : syracuseStep 3116981 = 292217) (by norm_num)
theorem B2076601 : Blo 1845624 2076601 := bbase (se 2 (by rfl) ⟨778725, by rfl⟩ : syracuseStep 2076601 = 1557451) (by norm_num)
theorem B4673477 : Blo 1845624 4673477 := bbase (se 4 (by rfl) ⟨438138, by rfl⟩ : syracuseStep 4673477 = 876277) (by norm_num)
theorem B35975125 : Blo 1845624 35975125 := bbase (se 7 (by rfl) ⟨421583, by rfl⟩ : syracuseStep 35975125 = 843167) (by norm_num)
theorem B9351125 : Blo 1845624 9351125 := bbase (se 7 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 9351125 = 219167) (by norm_num)
theorem B2076637 : Blo 1845624 2076637 := bbase (se 3 (by rfl) ⟨389369, by rfl⟩ : syracuseStep 2076637 = 778739) (by norm_num)
theorem B2076673 : Blo 1845624 2076673 := bbase (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) (by norm_num)
theorem B5918741 : Blo 1845624 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B3944477 : Blo 1845624 3944477 := bbase (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) (by norm_num)
theorem B2076709 : Blo 1845624 2076709 := bbase (se 4 (by rfl) ⟨194691, by rfl⟩ : syracuseStep 2076709 = 389383) (by norm_num)
theorem B3117109 : Blo 1845624 3117109 := bbase (se 5 (by rfl) ⟨146114, by rfl⟩ : syracuseStep 3117109 = 292229) (by norm_num)
theorem B2076745 : Blo 1845624 2076745 := bbase (se 2 (by rfl) ⟨778779, by rfl⟩ : syracuseStep 2076745 = 1557559) (by norm_num)
theorem B2076781 : Blo 1845624 2076781 := bbase (se 3 (by rfl) ⟨389396, by rfl⟩ : syracuseStep 2076781 = 778793) (by norm_num)
theorem B1896565 : Blo 1845624 1896565 := bbase (se 5 (by rfl) ⟨88901, by rfl⟩ : syracuseStep 1896565 = 177803) (by norm_num)
theorem B10514549 : Blo 1845624 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B3117197 : Blo 1845624 3117197 := bbase (se 3 (by rfl) ⟨584474, by rfl⟩ : syracuseStep 3117197 = 1168949) (by norm_num)
theorem B2076817 : Blo 1845624 2076817 := bbase (se 2 (by rfl) ⟨778806, by rfl⟩ : syracuseStep 2076817 = 1557613) (by norm_num)
theorem B2076853 : Blo 1845624 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B5918933 : Blo 1845624 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B2076889 : Blo 1845624 2076889 := bbase (se 2 (by rfl) ⟨778833, by rfl⟩ : syracuseStep 2076889 = 1557667) (by norm_num)
theorem B2076925 : Blo 1845624 2076925 := bbase (se 3 (by rfl) ⟨389423, by rfl⟩ : syracuseStep 2076925 = 778847) (by norm_num)
theorem B3117325 : Blo 1845624 3117325 := bbase (se 3 (by rfl) ⟨584498, by rfl⟩ : syracuseStep 3117325 = 1168997) (by norm_num)
theorem B15175957 : Blo 1845624 15175957 := bbase (se 6 (by rfl) ⟨355686, by rfl⟩ : syracuseStep 15175957 = 711373) (by norm_num)
theorem B4673821 : Blo 1845624 4673821 := bbase (se 3 (by rfl) ⟨876341, by rfl⟩ : syracuseStep 4673821 = 1752683) (by norm_num)
theorem B2076961 : Blo 1845624 2076961 := bbase (se 2 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 2076961 = 1557721) (by norm_num)
theorem B2076997 : Blo 1845624 2076997 := bbase (se 4 (by rfl) ⟨194718, by rfl⟩ : syracuseStep 2076997 = 389437) (by norm_num)
theorem B5615941 : Blo 1845624 5615941 := bbase (se 4 (by rfl) ⟨526494, by rfl⟩ : syracuseStep 5615941 = 1052989) (by norm_num)
theorem B6230357 : Blo 1845624 6230357 := bbase (se 10 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 6230357 = 18253) (by norm_num)
theorem B3117413 : Blo 1845624 3117413 := bbase (se 4 (by rfl) ⟨292257, by rfl⟩ : syracuseStep 3117413 = 584515) (by norm_num)
theorem B2077033 : Blo 1845624 2077033 := bbase (se 2 (by rfl) ⟨778887, by rfl⟩ : syracuseStep 2077033 = 1557775) (by norm_num)
theorem B9474421 : Blo 1845624 9474421 := bbase (se 5 (by rfl) ⟨444113, by rfl⟩ : syracuseStep 9474421 = 888227) (by norm_num)
theorem B2077069 : Blo 1845624 2077069 := bbase (se 3 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 2077069 = 778901) (by norm_num)
theorem B4673933 : Blo 1845624 4673933 := bbase (se 3 (by rfl) ⟨876362, by rfl⟩ : syracuseStep 4673933 = 1752725) (by norm_num)
theorem B2077105 : Blo 1845624 2077105 := bbase (se 2 (by rfl) ⟨778914, by rfl⟩ : syracuseStep 2077105 = 1557829) (by norm_num)
theorem B2077141 : Blo 1845624 2077141 := bbase (se 7 (by rfl) ⟨24341, by rfl⟩ : syracuseStep 2077141 = 48683) (by norm_num)
theorem B24654293 : Blo 1845624 24654293 := bbase (se 7 (by rfl) ⟨288917, by rfl⟩ : syracuseStep 24654293 = 577835) (by norm_num)
theorem B8425957 : Blo 1845624 8425957 := bbase (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) (by norm_num)
theorem B3117541 : Blo 1845624 3117541 := bbase (se 4 (by rfl) ⟨292269, by rfl⟩ : syracuseStep 3117541 = 584539) (by norm_num)
theorem B4436461 : Blo 1845624 4436461 := bbase (se 3 (by rfl) ⟨831836, by rfl⟩ : syracuseStep 4436461 = 1663673) (by norm_num)
theorem B2077177 : Blo 1845624 2077177 := bbase (se 2 (by rfl) ⟨778941, by rfl⟩ : syracuseStep 2077177 = 1557883) (by norm_num)
theorem B2077213 : Blo 1845624 2077213 := bbase (se 3 (by rfl) ⟨389477, by rfl⟩ : syracuseStep 2077213 = 778955) (by norm_num)
theorem B3117629 : Blo 1845624 3117629 := bbase (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) (by norm_num)
theorem B2077249 : Blo 1845624 2077249 := bbase (se 2 (by rfl) ⟨778968, by rfl⟩ : syracuseStep 2077249 = 1557937) (by norm_num)
theorem B4674125 : Blo 1845624 4674125 := bbase (se 3 (by rfl) ⟨876398, by rfl⟩ : syracuseStep 4674125 = 1752797) (by norm_num)
theorem B15782485 : Blo 1845624 15782485 := bbase (se 8 (by rfl) ⟨92475, by rfl⟩ : syracuseStep 15782485 = 184951) (by norm_num)
theorem B2077285 : Blo 1845624 2077285 := bbase (se 4 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 2077285 = 389491) (by norm_num)
theorem B2077321 : Blo 1845624 2077321 := bbase (se 2 (by rfl) ⟨778995, by rfl⟩ : syracuseStep 2077321 = 1557991) (by norm_num)
theorem B6402725 : Blo 1845624 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B2077357 : Blo 1845624 2077357 := bbase (se 3 (by rfl) ⟨389504, by rfl⟩ : syracuseStep 2077357 = 779009) (by norm_num)
theorem B3117757 : Blo 1845624 3117757 := bbase (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) (by norm_num)
theorem B1970897 : Blo 1845624 1970897 := bbase (se 2 (by rfl) ⟨739086, by rfl⟩ : syracuseStep 1970897 = 1478173) (by norm_num)
theorem B2077393 : Blo 1845624 2077393 := bbase (se 2 (by rfl) ⟨779022, by rfl⟩ : syracuseStep 2077393 = 1558045) (by norm_num)
theorem B2077429 : Blo 1845624 2077429 := bbase (se 5 (by rfl) ⟨97379, by rfl⟩ : syracuseStep 2077429 = 194759) (by norm_num)
theorem B6230789 : Blo 1845624 6230789 := bbase (se 4 (by rfl) ⟨584136, by rfl⟩ : syracuseStep 6230789 = 1168273) (by norm_num)
theorem B3117845 : Blo 1845624 3117845 := bbase (se 6 (by rfl) ⟨73074, by rfl⟩ : syracuseStep 3117845 = 146149) (by norm_num)
theorem B2077465 : Blo 1845624 2077465 := bbase (se 2 (by rfl) ⟨779049, by rfl⟩ : syracuseStep 2077465 = 1558099) (by norm_num)
theorem B2077501 : Blo 1845624 2077501 := bbase (se 3 (by rfl) ⟨389531, by rfl⟩ : syracuseStep 2077501 = 779063) (by norm_num)
theorem B2700101 : Blo 1845624 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B2077537 : Blo 1845624 2077537 := bbase (se 2 (by rfl) ⟨779076, by rfl⟩ : syracuseStep 2077537 = 1558153) (by norm_num)
theorem B3945341 : Blo 1845624 3945341 := bbase (se 3 (by rfl) ⟨739751, by rfl⟩ : syracuseStep 3945341 = 1479503) (by norm_num)
theorem B2077573 : Blo 1845624 2077573 := bbase (se 4 (by rfl) ⟨194772, by rfl⟩ : syracuseStep 2077573 = 389545) (by norm_num)
theorem B3158941 : Blo 1845624 3158941 := bbase (se 3 (by rfl) ⟨592301, by rfl⟩ : syracuseStep 3158941 = 1184603) (by norm_num)
theorem B4674469 : Blo 1845624 4674469 := bbase (se 4 (by rfl) ⟨438231, by rfl⟩ : syracuseStep 4674469 = 876463) (by norm_num)
theorem B2077609 : Blo 1845624 2077609 := bbase (se 2 (by rfl) ⟨779103, by rfl⟩ : syracuseStep 2077609 = 1558207) (by norm_num)
theorem B11826101 : Blo 1845624 11826101 := bbase (se 5 (by rfl) ⟨554348, by rfl⟩ : syracuseStep 11826101 = 1108697) (by norm_num)
theorem B1971145 : Blo 1845624 1971145 := bbase (se 2 (by rfl) ⟨739179, by rfl⟩ : syracuseStep 1971145 = 1478359) (by norm_num)
theorem B2077645 : Blo 1845624 2077645 := bbase (se 3 (by rfl) ⟨389558, by rfl⟩ : syracuseStep 2077645 = 779117) (by norm_num)
theorem B2077681 : Blo 1845624 2077681 := bbase (se 2 (by rfl) ⟨779130, by rfl⟩ : syracuseStep 2077681 = 1558261) (by norm_num)
theorem B5256181 : Blo 1845624 5256181 := bbase (se 5 (by rfl) ⟨246383, by rfl⟩ : syracuseStep 5256181 = 492767) (by norm_num)
theorem B3552269 : Blo 1845624 3552269 := bbase (se 3 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 3552269 = 1332101) (by norm_num)
theorem B3945485 : Blo 1845624 3945485 := bbase (se 3 (by rfl) ⟨739778, by rfl⟩ : syracuseStep 3945485 = 1479557) (by norm_num)
theorem B4674581 : Blo 1845624 4674581 := bbase (se 6 (by rfl) ⟨109560, by rfl⟩ : syracuseStep 4674581 = 219121) (by norm_num)
theorem B2077717 : Blo 1845624 2077717 := bbase (se 6 (by rfl) ⟨48696, by rfl⟩ : syracuseStep 2077717 = 97393) (by norm_num)
theorem B25621525 : Blo 1845624 25621525 := bbase (se 6 (by rfl) ⟨600504, by rfl⟩ : syracuseStep 25621525 = 1201009) (by norm_num)
theorem B2077753 : Blo 1845624 2077753 := bbase (se 2 (by rfl) ⟨779157, by rfl⟩ : syracuseStep 2077753 = 1558315) (by norm_num)
theorem B3847253 : Blo 1845624 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B2077789 : Blo 1845624 2077789 := bbase (se 3 (by rfl) ⟨389585, by rfl⟩ : syracuseStep 2077789 = 779171) (by norm_num)
theorem B2806901 : Blo 1845624 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B2077825 : Blo 1845624 2077825 := bbase (se 2 (by rfl) ⟨779184, by rfl⟩ : syracuseStep 2077825 = 1558369) (by norm_num)
theorem B2077861 : Blo 1845624 2077861 := bbase (se 4 (by rfl) ⟨194799, by rfl⟩ : syracuseStep 2077861 = 389599) (by norm_num)
theorem B6231221 : Blo 1845624 6231221 := bbase (se 5 (by rfl) ⟨292088, by rfl⟩ : syracuseStep 6231221 = 584177) (by norm_num)
theorem B4437173 : Blo 1845624 4437173 := bbase (se 5 (by rfl) ⟨207992, by rfl⟩ : syracuseStep 4437173 = 415985) (by norm_num)
theorem B2077897 : Blo 1845624 2077897 := bbase (se 2 (by rfl) ⟨779211, by rfl⟩ : syracuseStep 2077897 = 1558423) (by norm_num)
theorem B4674773 : Blo 1845624 4674773 := bbase (se 7 (by rfl) ⟨54782, by rfl⟩ : syracuseStep 4674773 = 109565) (by norm_num)
theorem B9352421 : Blo 1845624 9352421 := bbase (se 4 (by rfl) ⟨876789, by rfl⟩ : syracuseStep 9352421 = 1753579) (by norm_num)
theorem B2077933 : Blo 1845624 2077933 := bbase (se 3 (by rfl) ⟨389612, by rfl⟩ : syracuseStep 2077933 = 779225) (by norm_num)
theorem B2077969 : Blo 1845624 2077969 := bbase (se 2 (by rfl) ⟨779238, by rfl⟩ : syracuseStep 2077969 = 1558477) (by norm_num)
theorem B2078005 : Blo 1845624 2078005 := bbase (se 5 (by rfl) ⟨97406, by rfl⟩ : syracuseStep 2078005 = 194813) (by norm_num)
theorem B16840021 : Blo 1845624 16840021 := bbase (se 13 (by rfl) ⟨3083, by rfl⟩ : syracuseStep 16840021 = 6167) (by norm_num)
theorem B2078041 : Blo 1845624 2078041 := bbase (se 2 (by rfl) ⟨779265, by rfl⟩ : syracuseStep 2078041 = 1558531) (by norm_num)
theorem B1971577 : Blo 1845624 1971577 := bbase (se 2 (by rfl) ⟨739341, by rfl⟩ : syracuseStep 1971577 = 1478683) (by norm_num)
theorem B2078077 : Blo 1845624 2078077 := bbase (se 3 (by rfl) ⟨389639, by rfl⟩ : syracuseStep 2078077 = 779279) (by norm_num)
theorem B7009685 : Blo 1845624 7009685 := bbase (se 6 (by rfl) ⟨164289, by rfl⟩ : syracuseStep 7009685 = 328579) (by norm_num)
theorem B2078113 : Blo 1845624 2078113 := bbase (se 2 (by rfl) ⟨779292, by rfl⟩ : syracuseStep 2078113 = 1558585) (by norm_num)
theorem B2217385 : Blo 1845624 2217385 := bbase (se 2 (by rfl) ⟨831519, by rfl⟩ : syracuseStep 2217385 = 1663039) (by norm_num)
theorem B6657461 : Blo 1845624 6657461 := bbase (se 5 (by rfl) ⟨312068, by rfl⟩ : syracuseStep 6657461 = 624137) (by norm_num)
theorem B1971649 : Blo 1845624 1971649 := bbase (se 2 (by rfl) ⟨739368, by rfl⟩ : syracuseStep 1971649 = 1478737) (by norm_num)
theorem B2078149 : Blo 1845624 2078149 := bbase (se 4 (by rfl) ⟨194826, by rfl⟩ : syracuseStep 2078149 = 389653) (by norm_num)
theorem B2078185 : Blo 1845624 2078185 := bbase (se 2 (by rfl) ⟨779319, by rfl⟩ : syracuseStep 2078185 = 1558639) (by norm_num)
theorem B2078221 : Blo 1845624 2078221 := bbase (se 3 (by rfl) ⟨389666, by rfl⟩ : syracuseStep 2078221 = 779333) (by norm_num)
theorem B4675117 : Blo 1845624 4675117 := bbase (se 3 (by rfl) ⟨876584, by rfl⟩ : syracuseStep 4675117 = 1753169) (by norm_num)
theorem B2078257 : Blo 1845624 2078257 := bbase (se 2 (by rfl) ⟨779346, by rfl⟩ : syracuseStep 2078257 = 1558693) (by norm_num)
theorem B4437557 : Blo 1845624 4437557 := bbase (se 5 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 4437557 = 416021) (by norm_num)
theorem B2078293 : Blo 1845624 2078293 := bbase (se 8 (by rfl) ⟨12177, by rfl⟩ : syracuseStep 2078293 = 24355) (by norm_num)
theorem B6231653 : Blo 1845624 6231653 := bbase (se 4 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 6231653 = 1168435) (by norm_num)
theorem B2078329 : Blo 1845624 2078329 := bbase (se 2 (by rfl) ⟨779373, by rfl⟩ : syracuseStep 2078329 = 1558747) (by norm_num)
theorem B2217601 : Blo 1845624 2217601 := bbase (se 2 (by rfl) ⟨831600, by rfl⟩ : syracuseStep 2217601 = 1663201) (by norm_num)
theorem B9344645 : Blo 1845624 9344645 := bbase (se 4 (by rfl) ⟨876060, by rfl⟩ : syracuseStep 9344645 = 1752121) (by norm_num)
theorem B4675229 : Blo 1845624 4675229 := bbase (se 3 (by rfl) ⟨876605, by rfl⟩ : syracuseStep 4675229 = 1753211) (by norm_num)
theorem B2078365 : Blo 1845624 2078365 := bbase (se 3 (by rfl) ⟨389693, by rfl⟩ : syracuseStep 2078365 = 779387) (by norm_num)
theorem B7009973 : Blo 1845624 7009973 := bbase (se 5 (by rfl) ⟨328592, by rfl⟩ : syracuseStep 7009973 = 657185) (by norm_num)
theorem B2078401 : Blo 1845624 2078401 := bbase (se 2 (by rfl) ⟨779400, by rfl⟩ : syracuseStep 2078401 = 1558801) (by norm_num)
theorem B2078437 : Blo 1845624 2078437 := bbase (se 4 (by rfl) ⟨194853, by rfl⟩ : syracuseStep 2078437 = 389707) (by norm_num)
theorem B2807557 : Blo 1845624 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B2078473 : Blo 1845624 2078473 := bbase (se 2 (by rfl) ⟨779427, by rfl⟩ : syracuseStep 2078473 = 1558855) (by norm_num)
theorem B3503893 : Blo 1845624 3503893 := bbase (se 6 (by rfl) ⟨82122, by rfl⟩ : syracuseStep 3503893 = 164245) (by norm_num)
theorem B2078509 : Blo 1845624 2078509 := bbase (se 3 (by rfl) ⟨389720, by rfl⟩ : syracuseStep 2078509 = 779441) (by norm_num)
theorem B1972021 : Blo 1845624 1972021 := bbase (se 5 (by rfl) ⟨92438, by rfl⟩ : syracuseStep 1972021 = 184877) (by norm_num)
theorem B5060405 : Blo 1845624 5060405 := bbase (se 5 (by rfl) ⟨237206, by rfl⟩ : syracuseStep 5060405 = 474413) (by norm_num)
theorem B2078545 : Blo 1845624 2078545 := bbase (se 2 (by rfl) ⟨779454, by rfl⟩ : syracuseStep 2078545 = 1558909) (by norm_num)
theorem B4437845 : Blo 1845624 4437845 := bbase (se 9 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 4437845 = 26003) (by norm_num)
theorem B3159893 : Blo 1845624 3159893 := bbase (se 9 (by rfl) ⟨9257, by rfl⟩ : syracuseStep 3159893 = 18515) (by norm_num)
theorem B4675421 : Blo 1845624 4675421 := bbase (se 3 (by rfl) ⟨876641, by rfl⟩ : syracuseStep 4675421 = 1753283) (by norm_num)
theorem B2807693 : Blo 1845624 2807693 := bbase (se 3 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 2807693 = 1052885) (by norm_num)
theorem B3504053 : Blo 1845624 3504053 := bbase (se 5 (by rfl) ⟨164252, by rfl⟩ : syracuseStep 3504053 = 328505) (by norm_num)
theorem B3651533 : Blo 1845624 3651533 := bbase (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) (by norm_num)
theorem B6232085 : Blo 1845624 6232085 := bbase (se 6 (by rfl) ⟨146064, by rfl⟩ : syracuseStep 6232085 = 292129) (by norm_num)
theorem B3373093 : Blo 1845624 3373093 := bbase (se 4 (by rfl) ⟨316227, by rfl⟩ : syracuseStep 3373093 = 632455) (by norm_num)
theorem B7485493 : Blo 1845624 7485493 := bbase (se 5 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 7485493 = 701765) (by norm_num)
theorem B3504197 : Blo 1845624 3504197 := bbase (se 4 (by rfl) ⟨328518, by rfl⟩ : syracuseStep 3504197 = 657037) (by norm_num)
theorem B8992853 : Blo 1845624 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B5617781 : Blo 1845624 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B1972397 : Blo 1845624 1972397 := bbase (se 3 (by rfl) ⟨369824, by rfl⟩ : syracuseStep 1972397 = 739649) (by norm_num)
theorem B4675765 : Blo 1845624 4675765 := bbase (se 5 (by rfl) ⟨219176, by rfl⟩ : syracuseStep 4675765 = 438353) (by norm_num)
theorem B17742037 : Blo 1845624 17742037 := bbase (se 7 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 17742037 = 415829) (by norm_num)
theorem B6314213 : Blo 1845624 6314213 := bbase (se 4 (by rfl) ⟨591957, by rfl⟩ : syracuseStep 6314213 = 1183915) (by norm_num)
theorem B1972469 : Blo 1845624 1972469 := bbase (se 5 (by rfl) ⟨92459, by rfl⟩ : syracuseStep 1972469 = 184919) (by norm_num)
theorem B5331221 : Blo 1845624 5331221 := bbase (se 6 (by rfl) ⟨124950, by rfl⟩ : syracuseStep 5331221 = 249901) (by norm_num)
theorem B4675877 : Blo 1845624 4675877 := bbase (se 4 (by rfl) ⟨438363, by rfl⟩ : syracuseStep 4675877 = 876727) (by norm_num)
theorem B3504485 : Blo 1845624 3504485 := bbase (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) (by norm_num)
theorem B2529677 : Blo 1845624 2529677 := bbase (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) (by norm_num)
theorem B6658469 : Blo 1845624 6658469 := bbase (se 4 (by rfl) ⟨624231, by rfl⟩ : syracuseStep 6658469 = 1248463) (by norm_num)
theorem B1972657 : Blo 1845624 1972657 := bbase (se 2 (by rfl) ⟨739746, by rfl⟩ : syracuseStep 1972657 = 1479493) (by norm_num)
theorem B6232517 : Blo 1845624 6232517 := bbase (se 4 (by rfl) ⟨584298, by rfl⟩ : syracuseStep 6232517 = 1168597) (by norm_num)
theorem B5257685 : Blo 1845624 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B4676069 : Blo 1845624 4676069 := bbase (se 4 (by rfl) ⟨438381, by rfl⟩ : syracuseStep 4676069 = 876763) (by norm_num)
theorem B3504637 : Blo 1845624 3504637 := bbase (se 3 (by rfl) ⟨657119, by rfl⟩ : syracuseStep 3504637 = 1314239) (by norm_num)
theorem B1972841 : Blo 1845624 1972841 := bbase (se 2 (by rfl) ⟨739815, by rfl⟩ : syracuseStep 1972841 = 1479631) (by norm_num)
theorem B8420117 : Blo 1845624 8420117 := bbase (se 6 (by rfl) ⟨197346, by rfl⟩ : syracuseStep 8420117 = 394693) (by norm_num)
theorem B3504941 : Blo 1845624 3504941 := bbase (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) (by norm_num)
theorem B4676413 : Blo 1845624 4676413 := bbase (se 3 (by rfl) ⟨876827, by rfl⟩ : syracuseStep 4676413 = 1753655) (by norm_num)
theorem B7011157 : Blo 1845624 7011157 := bbase (se 9 (by rfl) ⟨20540, by rfl⟩ : syracuseStep 7011157 = 41081) (by norm_num)
theorem B5913461 : Blo 1845624 5913461 := bbase (se 5 (by rfl) ⟨277193, by rfl⟩ : syracuseStep 5913461 = 554387) (by norm_num)
theorem B6314869 : Blo 1845624 6314869 := bbase (se 5 (by rfl) ⟨296009, by rfl⟩ : syracuseStep 6314869 = 592019) (by norm_num)
theorem B6232949 : Blo 1845624 6232949 := bbase (se 5 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 6232949 = 584339) (by norm_num)
theorem B9345941 : Blo 1845624 9345941 := bbase (se 6 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 9345941 = 438091) (by norm_num)
theorem B4676525 : Blo 1845624 4676525 := bbase (se 3 (by rfl) ⟨876848, by rfl⟩ : syracuseStep 4676525 = 1753697) (by norm_num)
theorem B7592885 : Blo 1845624 7592885 := bbase (se 5 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 7592885 = 711833) (by norm_num)
theorem B2628541 : Blo 1845624 2628541 := bbase (se 3 (by rfl) ⟨492851, by rfl⟩ : syracuseStep 2628541 = 985703) (by norm_num)
theorem B2956397 : Blo 1845624 2956397 := bbase (se 3 (by rfl) ⟨554324, by rfl⟩ : syracuseStep 2956397 = 1108649) (by norm_num)
theorem B4676717 : Blo 1845624 4676717 := bbase (se 3 (by rfl) ⟨876884, by rfl⟩ : syracuseStep 4676717 = 1753769) (by norm_num)
theorem B7011461 : Blo 1845624 7011461 := bbase (se 4 (by rfl) ⟨657324, by rfl⟩ : syracuseStep 7011461 = 1314649) (by norm_num)
theorem B2628877 : Blo 1845624 2628877 := bbase (se 3 (by rfl) ⟨492914, by rfl⟩ : syracuseStep 2628877 = 985829) (by norm_num)
theorem B2219297 : Blo 1845624 2219297 := bbase (se 2 (by rfl) ⟨832236, by rfl⟩ : syracuseStep 2219297 = 1664473) (by norm_num)
theorem B6233381 : Blo 1845624 6233381 := bbase (se 4 (by rfl) ⟨584379, by rfl⟩ : syracuseStep 6233381 = 1168759) (by norm_num)
theorem B7486789 : Blo 1845624 7486789 := bbase (se 4 (by rfl) ⟨701886, by rfl⟩ : syracuseStep 7486789 = 1403773) (by norm_num)
theorem B4152725 : Blo 1845624 4152725 := bbase (se 6 (by rfl) ⟨97329, by rfl⟩ : syracuseStep 4152725 = 194659) (by norm_num)
theorem B4152797 : Blo 1845624 4152797 := bbase (se 3 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 4152797 = 1557299) (by norm_num)
theorem B2629093 : Blo 1845624 2629093 := bbase (se 4 (by rfl) ⟨246477, by rfl⟩ : syracuseStep 2629093 = 492955) (by norm_num)
theorem B5062117 : Blo 1845624 5062117 := bbase (se 4 (by rfl) ⟨474573, by rfl⟩ : syracuseStep 5062117 = 949147) (by norm_num)
theorem B7888373 : Blo 1845624 7888373 := bbase (se 5 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 7888373 = 739535) (by norm_num)
theorem B2219509 : Blo 1845624 2219509 := bbase (se 5 (by rfl) ⟨104039, by rfl⟩ : syracuseStep 2219509 = 208079) (by norm_num)
theorem B8420885 : Blo 1845624 8420885 := bbase (se 6 (by rfl) ⟨197364, by rfl⟩ : syracuseStep 8420885 = 394729) (by norm_num)
theorem B3505693 : Blo 1845624 3505693 := bbase (se 3 (by rfl) ⟨657317, by rfl⟩ : syracuseStep 3505693 = 1314635) (by norm_num)
theorem B4152869 : Blo 1845624 4152869 := bbase (se 4 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 4152869 = 778663) (by norm_num)
theorem B2768453 : Blo 1845624 2768453 := bbase (se 4 (by rfl) ⟨259542, by rfl⟩ : syracuseStep 2768453 = 519085) (by norm_num)
theorem B2768477 : Blo 1845624 2768477 := bbase (se 3 (by rfl) ⟨519089, by rfl⟩ : syracuseStep 2768477 = 1038179) (by norm_num)
theorem B4152941 : Blo 1845624 4152941 := bbase (se 3 (by rfl) ⟨778676, by rfl⟩ : syracuseStep 4152941 = 1557353) (by norm_num)
theorem B2768501 : Blo 1845624 2768501 := bbase (se 5 (by rfl) ⟨129773, by rfl⟩ : syracuseStep 2768501 = 259547) (by norm_num)
theorem B2219653 : Blo 1845624 2219653 := bbase (se 4 (by rfl) ⟨208092, by rfl⟩ : syracuseStep 2219653 = 416185) (by norm_num)
theorem B2768525 : Blo 1845624 2768525 := bbase (se 3 (by rfl) ⟨519098, by rfl⟩ : syracuseStep 2768525 = 1038197) (by norm_num)
theorem B2768549 : Blo 1845624 2768549 := bbase (se 4 (by rfl) ⟨259551, by rfl⟩ : syracuseStep 2768549 = 519103) (by norm_num)
theorem B3505837 : Blo 1845624 3505837 := bbase (se 3 (by rfl) ⟨657344, by rfl⟩ : syracuseStep 3505837 = 1314689) (by norm_num)
theorem B4153013 : Blo 1845624 4153013 := bbase (se 5 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 4153013 = 389345) (by norm_num)
theorem B2768573 : Blo 1845624 2768573 := bbase (se 3 (by rfl) ⟨519107, by rfl⟩ : syracuseStep 2768573 = 1038215) (by norm_num)
theorem B2768597 : Blo 1845624 2768597 := bbase (se 7 (by rfl) ⟨32444, by rfl⟩ : syracuseStep 2768597 = 64889) (by norm_num)
theorem B6233813 : Blo 1845624 6233813 := bbase (se 7 (by rfl) ⟨73052, by rfl⟩ : syracuseStep 6233813 = 146105) (by norm_num)
theorem B56884949 : Blo 1845624 56884949 := bbase (se 7 (by rfl) ⟨666620, by rfl⟩ : syracuseStep 56884949 = 1333241) (by norm_num)
theorem B5996261 : Blo 1845624 5996261 := bbase (se 4 (by rfl) ⟨562149, by rfl⟩ : syracuseStep 5996261 = 1124299) (by norm_num)
theorem B2768621 : Blo 1845624 2768621 := bbase (se 3 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 2768621 = 1038233) (by norm_num)
theorem B9985781 : Blo 1845624 9985781 := bbase (se 5 (by rfl) ⟨468083, by rfl⟩ : syracuseStep 9985781 = 936167) (by norm_num)
theorem B4153085 : Blo 1845624 4153085 := bbase (se 3 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 4153085 = 1557407) (by norm_num)
theorem B2768645 : Blo 1845624 2768645 := bbase (se 4 (by rfl) ⟨259560, by rfl⟩ : syracuseStep 2768645 = 519121) (by norm_num)
theorem B2957077 : Blo 1845624 2957077 := bbase (se 6 (by rfl) ⟨69306, by rfl⟩ : syracuseStep 2957077 = 138613) (by norm_num)
theorem B2768669 : Blo 1845624 2768669 := bbase (se 3 (by rfl) ⟨519125, by rfl⟩ : syracuseStep 2768669 = 1038251) (by norm_num)
theorem B2768693 : Blo 1845624 2768693 := bbase (se 5 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 2768693 = 259565) (by norm_num)
theorem B14024501 : Blo 1845624 14024501 := bbase (se 5 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 14024501 = 1314797) (by norm_num)
theorem B4153157 : Blo 1845624 4153157 := bbase (se 4 (by rfl) ⟨389358, by rfl⟩ : syracuseStep 4153157 = 778717) (by norm_num)
theorem B2768717 : Blo 1845624 2768717 := bbase (se 3 (by rfl) ⟨519134, by rfl⟩ : syracuseStep 2768717 = 1038269) (by norm_num)
theorem B3505997 : Blo 1845624 3505997 := bbase (se 3 (by rfl) ⟨657374, by rfl⟩ : syracuseStep 3505997 = 1314749) (by norm_num)
theorem B2957141 : Blo 1845624 2957141 := bbase (se 9 (by rfl) ⟨8663, by rfl⟩ : syracuseStep 2957141 = 17327) (by norm_num)
theorem B2629469 : Blo 1845624 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B2768741 : Blo 1845624 2768741 := bbase (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) (by norm_num)
theorem B2768765 : Blo 1845624 2768765 := bbase (se 3 (by rfl) ⟨519143, by rfl⟩ : syracuseStep 2768765 = 1038287) (by norm_num)
theorem B4153229 : Blo 1845624 4153229 := bbase (se 3 (by rfl) ⟨778730, by rfl⟩ : syracuseStep 4153229 = 1557461) (by norm_num)
theorem B2768789 : Blo 1845624 2768789 := bbase (se 6 (by rfl) ⟨64893, by rfl⟩ : syracuseStep 2768789 = 129787) (by norm_num)
theorem B2768813 : Blo 1845624 2768813 := bbase (se 3 (by rfl) ⟨519152, by rfl⟩ : syracuseStep 2768813 = 1038305) (by norm_num)
theorem B2768837 : Blo 1845624 2768837 := bbase (se 4 (by rfl) ⟨259578, by rfl⟩ : syracuseStep 2768837 = 519157) (by norm_num)
theorem B4153301 : Blo 1845624 4153301 := bbase (se 7 (by rfl) ⟨48671, by rfl⟩ : syracuseStep 4153301 = 97343) (by norm_num)
theorem B2768861 : Blo 1845624 2768861 := bbase (se 3 (by rfl) ⟨519161, by rfl⟩ : syracuseStep 2768861 = 1038323) (by norm_num)
theorem B3506141 : Blo 1845624 3506141 := bbase (se 3 (by rfl) ⟨657401, by rfl⟩ : syracuseStep 3506141 = 1314803) (by norm_num)
theorem B2768885 : Blo 1845624 2768885 := bbase (se 5 (by rfl) ⟨129791, by rfl⟩ : syracuseStep 2768885 = 259583) (by norm_num)
theorem B2768897 : Blo 1845624 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B3506179 : Blo 1845624 3506179 := bstep (se 1 (by rfl) ⟨2629634, by rfl⟩ : syracuseStep 3506179 = 5259269) B5259269
theorem B2768915 : Blo 1845624 2768915 := bstep (se 1 (by rfl) ⟨2076686, by rfl⟩ : syracuseStep 2768915 = 4153373) B4153373
theorem B2768945 : Blo 1845624 2768945 := bstep (se 2 (by rfl) ⟨1038354, by rfl⟩ : syracuseStep 2768945 = 2076709) B2076709
theorem B4497457 : Blo 1845624 4497457 := bstep (se 2 (by rfl) ⟨1686546, by rfl⟩ : syracuseStep 4497457 = 3373093) B3373093
theorem B2768963 : Blo 1845624 2768963 := bstep (se 1 (by rfl) ⟨2076722, by rfl⟩ : syracuseStep 2768963 = 4153445) B4153445
theorem B5914691 : Blo 1845624 5914691 := bstep (se 1 (by rfl) ⟨4436018, by rfl⟩ : syracuseStep 5914691 = 8872037) B8872037
theorem B10518605 : Blo 1845624 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B2768993 : Blo 1845624 2768993 := bstep (se 2 (by rfl) ⟨1038372, by rfl⟩ : syracuseStep 2768993 = 2076745) B2076745
theorem B2769011 : Blo 1845624 2769011 := bstep (se 1 (by rfl) ⟨2076758, by rfl⟩ : syracuseStep 2769011 = 4153517) B4153517
theorem B2769041 : Blo 1845624 2769041 := bstep (se 2 (by rfl) ⟨1038390, by rfl⟩ : syracuseStep 2769041 = 2076781) B2076781
theorem B2769059 : Blo 1845624 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B2769089 : Blo 1845624 2769089 := bstep (se 2 (by rfl) ⟨1038408, by rfl⟩ : syracuseStep 2769089 = 2076817) B2076817
theorem B4153553 : Blo 1845624 4153553 := bstep (se 2 (by rfl) ⟨1557582, by rfl⟩ : syracuseStep 4153553 = 3115165) B3115165
theorem B2769107 : Blo 1845624 2769107 := bstep (se 1 (by rfl) ⟨2076830, by rfl⟩ : syracuseStep 2769107 = 4153661) B4153661
theorem B4153571 : Blo 1845624 4153571 := bstep (se 1 (by rfl) ⟨3115178, by rfl⟩ : syracuseStep 4153571 = 6230357) B6230357
theorem B2769137 : Blo 1845624 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B6234353 : Blo 1845624 6234353 := bstep (se 2 (by rfl) ⟨2337882, by rfl⟩ : syracuseStep 6234353 = 4675765) B4675765
theorem B2769155 : Blo 1845624 2769155 := bstep (se 1 (by rfl) ⟨2076866, by rfl⟩ : syracuseStep 2769155 = 4153733) B4153733
theorem B2769185 : Blo 1845624 2769185 := bstep (se 2 (by rfl) ⟨1038444, by rfl⟩ : syracuseStep 2769185 = 2076889) B2076889
theorem B2769203 : Blo 1845624 2769203 := bstep (se 1 (by rfl) ⟨2076902, by rfl⟩ : syracuseStep 2769203 = 4153805) B4153805
theorem B2769233 : Blo 1845624 2769233 := bstep (se 2 (by rfl) ⟨1038462, by rfl⟩ : syracuseStep 2769233 = 2076925) B2076925
theorem B2769251 : Blo 1845624 2769251 := bstep (se 1 (by rfl) ⟨2076938, by rfl⟩ : syracuseStep 2769251 = 4153877) B4153877
theorem B20234609 : Blo 1845624 20234609 := bstep (se 2 (by rfl) ⟨7587978, by rfl⟩ : syracuseStep 20234609 = 15175957) B15175957
theorem B2769281 : Blo 1845624 2769281 := bstep (se 2 (by rfl) ⟨1038480, by rfl⟩ : syracuseStep 2769281 = 2076961) B2076961
theorem B2769299 : Blo 1845624 2769299 := bstep (se 1 (by rfl) ⟨2076974, by rfl⟩ : syracuseStep 2769299 = 4153949) B4153949
theorem B2769329 : Blo 1845624 2769329 := bstep (se 2 (by rfl) ⟨1038498, by rfl⟩ : syracuseStep 2769329 = 2076997) B2076997
theorem B7487921 : Blo 1845624 7487921 := bstep (se 2 (by rfl) ⟨2807970, by rfl⟩ : syracuseStep 7487921 = 5615941) B5615941
theorem B7889329 : Blo 1845624 7889329 := bstep (se 2 (by rfl) ⟨2958498, by rfl⟩ : syracuseStep 7889329 = 5916997) B5916997
theorem B2769347 : Blo 1845624 2769347 := bstep (se 1 (by rfl) ⟨2077010, by rfl⟩ : syracuseStep 2769347 = 4154021) B4154021
theorem B4268483 : Blo 1845624 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B3506627 : Blo 1845624 3506627 := bstep (se 1 (by rfl) ⟨2629970, by rfl⟩ : syracuseStep 3506627 = 5259941) B5259941
theorem B5259725 : Blo 1845624 5259725 := bstep (se 3 (by rfl) ⟨986198, by rfl⟩ : syracuseStep 5259725 = 1972397) B1972397
theorem B2769377 : Blo 1845624 2769377 := bstep (se 2 (by rfl) ⟨1038516, by rfl⟩ : syracuseStep 2769377 = 2077033) B2077033
theorem B14967281 : Blo 1845624 14967281 := bstep (se 2 (by rfl) ⟨5612730, by rfl⟩ : syracuseStep 14967281 = 11225461) B11225461
theorem B4153841 : Blo 1845624 4153841 := bstep (se 2 (by rfl) ⟨1557690, by rfl⟩ : syracuseStep 4153841 = 3115381) B3115381
theorem B2769395 : Blo 1845624 2769395 := bstep (se 1 (by rfl) ⟨2077046, by rfl⟩ : syracuseStep 2769395 = 4154093) B4154093
theorem B12632561 : Blo 1845624 12632561 := bstep (se 2 (by rfl) ⟨4737210, by rfl⟩ : syracuseStep 12632561 = 9474421) B9474421
theorem B4153859 : Blo 1845624 4153859 := bstep (se 1 (by rfl) ⟨3115394, by rfl⟩ : syracuseStep 4153859 = 6230789) B6230789
theorem B2769425 : Blo 1845624 2769425 := bstep (se 2 (by rfl) ⟨1038534, by rfl⟩ : syracuseStep 2769425 = 2077069) B2077069
theorem B2769443 : Blo 1845624 2769443 := bstep (se 1 (by rfl) ⟨2077082, by rfl⟩ : syracuseStep 2769443 = 4154165) B4154165
theorem B2769473 : Blo 1845624 2769473 := bstep (se 2 (by rfl) ⟨1038552, by rfl⟩ : syracuseStep 2769473 = 2077105) B2077105
theorem B2769491 : Blo 1845624 2769491 := bstep (se 1 (by rfl) ⟨2077118, by rfl⟩ : syracuseStep 2769491 = 4154237) B4154237
theorem B2630227 : Blo 1845624 2630227 := bstep (se 1 (by rfl) ⟨1972670, by rfl⟩ : syracuseStep 2630227 = 3945341) B3945341
theorem B2769521 : Blo 1845624 2769521 := bstep (se 2 (by rfl) ⟨1038570, by rfl⟩ : syracuseStep 2769521 = 2077141) B2077141
theorem B8422001 : Blo 1845624 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B2769539 : Blo 1845624 2769539 := bstep (se 1 (by rfl) ⟨2077154, by rfl⟩ : syracuseStep 2769539 = 4154309) B4154309
theorem B5259917 : Blo 1845624 5259917 := bstep (se 3 (by rfl) ⟨986234, by rfl⟩ : syracuseStep 5259917 = 1972469) B1972469
theorem B5915281 : Blo 1845624 5915281 := bstep (se 2 (by rfl) ⟨2218230, by rfl⟩ : syracuseStep 5915281 = 4436461) B4436461
theorem B2769569 : Blo 1845624 2769569 := bstep (se 2 (by rfl) ⟨1038588, by rfl⟩ : syracuseStep 2769569 = 2077177) B2077177
theorem B4989613 : Blo 1845624 4989613 := bstep (se 3 (by rfl) ⟨935552, by rfl⟩ : syracuseStep 4989613 = 1871105) B1871105
theorem B2769587 : Blo 1845624 2769587 := bstep (se 1 (by rfl) ⟨2077190, by rfl⟩ : syracuseStep 2769587 = 4154381) B4154381
theorem B2630323 : Blo 1845624 2630323 := bstep (se 1 (by rfl) ⟨1972742, by rfl⟩ : syracuseStep 2630323 = 3945485) B3945485
theorem B11838149 : Blo 1845624 11838149 := bstep (se 4 (by rfl) ⟨1109826, by rfl⟩ : syracuseStep 11838149 = 2219653) B2219653
theorem B2769617 : Blo 1845624 2769617 := bstep (se 2 (by rfl) ⟨1038606, by rfl⟩ : syracuseStep 2769617 = 2077213) B2077213
theorem B2769635 : Blo 1845624 2769635 := bstep (se 1 (by rfl) ⟨2077226, by rfl⟩ : syracuseStep 2769635 = 4154453) B4154453
theorem B3506915 : Blo 1845624 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B2769665 : Blo 1845624 2769665 := bstep (se 2 (by rfl) ⟨1038624, by rfl⟩ : syracuseStep 2769665 = 2077249) B2077249
theorem B6234893 : Blo 1845624 6234893 := bstep (se 3 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 6234893 = 2338085) B2338085
theorem B4154129 : Blo 1845624 4154129 := bstep (se 2 (by rfl) ⟨1557798, by rfl⟩ : syracuseStep 4154129 = 3115597) B3115597
theorem B2769683 : Blo 1845624 2769683 := bstep (se 1 (by rfl) ⟨2077262, by rfl⟩ : syracuseStep 2769683 = 4154525) B4154525
theorem B4154147 : Blo 1845624 4154147 := bstep (se 1 (by rfl) ⟨3115610, by rfl⟩ : syracuseStep 4154147 = 6231221) B6231221
theorem B2958115 : Blo 1845624 2958115 := bstep (se 1 (by rfl) ⟨2218586, by rfl⟩ : syracuseStep 2958115 = 4437173) B4437173
theorem B2769713 : Blo 1845624 2769713 := bstep (se 2 (by rfl) ⟨1038642, by rfl⟩ : syracuseStep 2769713 = 2077285) B2077285
theorem B2769731 : Blo 1845624 2769731 := bstep (se 1 (by rfl) ⟨2077298, by rfl⟩ : syracuseStep 2769731 = 4154597) B4154597
theorem B6234947 : Blo 1845624 6234947 := bstep (se 1 (by rfl) ⟨4676210, by rfl⟩ : syracuseStep 6234947 = 9352421) B9352421
theorem B2769761 : Blo 1845624 2769761 := bstep (se 2 (by rfl) ⟨1038660, by rfl⟩ : syracuseStep 2769761 = 2077321) B2077321
theorem B2769779 : Blo 1845624 2769779 := bstep (se 1 (by rfl) ⟨2077334, by rfl⟩ : syracuseStep 2769779 = 4154669) B4154669
theorem B2769809 : Blo 1845624 2769809 := bstep (se 2 (by rfl) ⟨1038678, by rfl⟩ : syracuseStep 2769809 = 2077357) B2077357
theorem B2769827 : Blo 1845624 2769827 := bstep (se 1 (by rfl) ⟨2077370, by rfl⟩ : syracuseStep 2769827 = 4154741) B4154741
theorem B2769857 : Blo 1845624 2769857 := bstep (se 2 (by rfl) ⟨1038696, by rfl⟩ : syracuseStep 2769857 = 2077393) B2077393
theorem B2769875 : Blo 1845624 2769875 := bstep (se 1 (by rfl) ⟨2077406, by rfl⟩ : syracuseStep 2769875 = 4154813) B4154813
theorem B2769905 : Blo 1845624 2769905 := bstep (se 2 (by rfl) ⟨1038714, by rfl⟩ : syracuseStep 2769905 = 2077429) B2077429
theorem B2769923 : Blo 1845624 2769923 := bstep (se 1 (by rfl) ⟨2077442, by rfl⟩ : syracuseStep 2769923 = 4154885) B4154885
theorem B2769953 : Blo 1845624 2769953 := bstep (se 2 (by rfl) ⟨1038732, by rfl⟩ : syracuseStep 2769953 = 2077465) B2077465
theorem B2958371 : Blo 1845624 2958371 := bstep (se 1 (by rfl) ⟨2218778, by rfl⟩ : syracuseStep 2958371 = 4437557) B4437557
theorem B4154417 : Blo 1845624 4154417 := bstep (se 2 (by rfl) ⟨1557906, by rfl⟩ : syracuseStep 4154417 = 3115813) B3115813
theorem B2769971 : Blo 1845624 2769971 := bstep (se 1 (by rfl) ⟨2077478, by rfl⟩ : syracuseStep 2769971 = 4154957) B4154957
theorem B4154435 : Blo 1845624 4154435 := bstep (se 1 (by rfl) ⟨3115826, by rfl⟩ : syracuseStep 4154435 = 6231653) B6231653
theorem B2770001 : Blo 1845624 2770001 := bstep (se 2 (by rfl) ⟨1038750, by rfl⟩ : syracuseStep 2770001 = 2077501) B2077501
theorem B6235217 : Blo 1845624 6235217 := bstep (se 2 (by rfl) ⟨2338206, by rfl⟩ : syracuseStep 6235217 = 4676413) B4676413
theorem B2770019 : Blo 1845624 2770019 := bstep (se 1 (by rfl) ⟨2077514, by rfl⟩ : syracuseStep 2770019 = 4155029) B4155029
theorem B9348209 : Blo 1845624 9348209 := bstep (se 2 (by rfl) ⟨3505578, by rfl⟩ : syracuseStep 9348209 = 7011157) B7011157
theorem B3081331 : Blo 1845624 3081331 := bstep (se 1 (by rfl) ⟨2310998, by rfl⟩ : syracuseStep 3081331 = 4621997) B4621997
theorem B2770049 : Blo 1845624 2770049 := bstep (se 2 (by rfl) ⟨1038768, by rfl⟩ : syracuseStep 2770049 = 2077537) B2077537
theorem B2770067 : Blo 1845624 2770067 := bstep (se 1 (by rfl) ⟨2077550, by rfl⟩ : syracuseStep 2770067 = 4155101) B4155101
theorem B6653105 : Blo 1845624 6653105 := bstep (se 2 (by rfl) ⟨2494914, by rfl⟩ : syracuseStep 6653105 = 4989829) B4989829
theorem B2770097 : Blo 1845624 2770097 := bstep (se 2 (by rfl) ⟨1038786, by rfl⟩ : syracuseStep 2770097 = 2077573) B2077573
theorem B2770115 : Blo 1845624 2770115 := bstep (se 1 (by rfl) ⟨2077586, by rfl⟩ : syracuseStep 2770115 = 4155173) B4155173
theorem B4211921 : Blo 1845624 4211921 := bstep (se 2 (by rfl) ⟨1579470, by rfl⟩ : syracuseStep 4211921 = 3158941) B3158941
theorem B2770145 : Blo 1845624 2770145 := bstep (se 2 (by rfl) ⟨1038804, by rfl⟩ : syracuseStep 2770145 = 2077609) B2077609
theorem B2958563 : Blo 1845624 2958563 := bstep (se 1 (by rfl) ⟨2218922, by rfl⟩ : syracuseStep 2958563 = 4437845) B4437845
theorem B2106595 : Blo 1845624 2106595 := bstep (se 1 (by rfl) ⟨1579946, by rfl⟩ : syracuseStep 2106595 = 3159893) B3159893
theorem B2770163 : Blo 1845624 2770163 := bstep (se 1 (by rfl) ⟨2077622, by rfl⟩ : syracuseStep 2770163 = 4155245) B4155245
theorem B2770193 : Blo 1845624 2770193 := bstep (se 2 (by rfl) ⟨1038822, by rfl⟩ : syracuseStep 2770193 = 2077645) B2077645
theorem B2336035 : Blo 1845624 2336035 := bstep (se 1 (by rfl) ⟨1752026, by rfl⟩ : syracuseStep 2336035 = 3504053) B3504053
theorem B2770211 : Blo 1845624 2770211 := bstep (se 1 (by rfl) ⟨2077658, by rfl⟩ : syracuseStep 2770211 = 4155317) B4155317
theorem B2434355 : Blo 1845624 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B2770241 : Blo 1845624 2770241 := bstep (se 2 (by rfl) ⟨1038840, by rfl⟩ : syracuseStep 2770241 = 2077681) B2077681
theorem B4154705 : Blo 1845624 4154705 := bstep (se 2 (by rfl) ⟨1558014, by rfl⟩ : syracuseStep 4154705 = 3116029) B3116029
theorem B2770259 : Blo 1845624 2770259 := bstep (se 1 (by rfl) ⟨2077694, by rfl⟩ : syracuseStep 2770259 = 4155389) B4155389
theorem B4154723 : Blo 1845624 4154723 := bstep (se 1 (by rfl) ⟨3116042, by rfl⟩ : syracuseStep 4154723 = 6232085) B6232085
theorem B2770289 : Blo 1845624 2770289 := bstep (se 2 (by rfl) ⟨1038858, by rfl⟩ : syracuseStep 2770289 = 2077717) B2077717
theorem B34162033 : Blo 1845624 34162033 := bstep (se 2 (by rfl) ⟨12810762, by rfl⟩ : syracuseStep 34162033 = 25621525) B25621525
theorem B2336131 : Blo 1845624 2336131 := bstep (se 1 (by rfl) ⟨1752098, by rfl⟩ : syracuseStep 2336131 = 3504197) B3504197
theorem B2770307 : Blo 1845624 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B2770337 : Blo 1845624 2770337 := bstep (se 2 (by rfl) ⟨1038876, by rfl⟩ : syracuseStep 2770337 = 2077753) B2077753
theorem B3745187 : Blo 1845624 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B2770355 : Blo 1845624 2770355 := bstep (se 1 (by rfl) ⟨2077766, by rfl⟩ : syracuseStep 2770355 = 4155533) B4155533
theorem B2770385 : Blo 1845624 2770385 := bstep (se 2 (by rfl) ⟨1038894, by rfl⟩ : syracuseStep 2770385 = 2077789) B2077789
theorem B2770403 : Blo 1845624 2770403 := bstep (se 1 (by rfl) ⟨2077802, by rfl⟩ : syracuseStep 2770403 = 4155605) B4155605
theorem B3114497 : Blo 1845624 3114497 := bstep (se 2 (by rfl) ⟨1167936, by rfl⟩ : syracuseStep 3114497 = 2335873) B2335873
theorem B2770433 : Blo 1845624 2770433 := bstep (se 2 (by rfl) ⟨1038912, by rfl⟩ : syracuseStep 2770433 = 2077825) B2077825
theorem B2770451 : Blo 1845624 2770451 := bstep (se 1 (by rfl) ⟨2077838, by rfl⟩ : syracuseStep 2770451 = 4155677) B4155677
theorem B2770481 : Blo 1845624 2770481 := bstep (se 2 (by rfl) ⟨1038930, by rfl⟩ : syracuseStep 2770481 = 2077861) B2077861
theorem B33326645 : Blo 1845624 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B2770499 : Blo 1845624 2770499 := bstep (se 1 (by rfl) ⟨2077874, by rfl⟩ : syracuseStep 2770499 = 4155749) B4155749
theorem B2770529 : Blo 1845624 2770529 := bstep (se 2 (by rfl) ⟨1038948, by rfl⟩ : syracuseStep 2770529 = 2077897) B2077897
theorem B5260909 : Blo 1845624 5260909 := bstep (se 3 (by rfl) ⟨986420, by rfl⟩ : syracuseStep 5260909 = 1972841) B1972841
theorem B4154993 : Blo 1845624 4154993 := bstep (se 2 (by rfl) ⟨1558122, by rfl⟩ : syracuseStep 4154993 = 3116245) B3116245
theorem B2770547 : Blo 1845624 2770547 := bstep (se 1 (by rfl) ⟨2077910, by rfl⟩ : syracuseStep 2770547 = 4155821) B4155821
theorem B3114625 : Blo 1845624 3114625 := bstep (se 2 (by rfl) ⟨1167984, by rfl⟩ : syracuseStep 3114625 = 2335969) B2335969
theorem B4155011 : Blo 1845624 4155011 := bstep (se 1 (by rfl) ⟨3116258, by rfl⟩ : syracuseStep 4155011 = 6232517) B6232517
theorem B2770577 : Blo 1845624 2770577 := bstep (se 2 (by rfl) ⟨1038966, by rfl⟩ : syracuseStep 2770577 = 2077933) B2077933
theorem B3114659 : Blo 1845624 3114659 := bstep (se 1 (by rfl) ⟨2335994, by rfl⟩ : syracuseStep 3114659 = 4671989) B4671989
theorem B2770595 : Blo 1845624 2770595 := bstep (se 1 (by rfl) ⟨2077946, by rfl⟩ : syracuseStep 2770595 = 4155893) B4155893
theorem B2770625 : Blo 1845624 2770625 := bstep (se 2 (by rfl) ⟨1038984, by rfl⟩ : syracuseStep 2770625 = 2077969) B2077969
theorem B2770643 : Blo 1845624 2770643 := bstep (se 1 (by rfl) ⟨2077982, by rfl⟩ : syracuseStep 2770643 = 4155965) B4155965
theorem B2770673 : Blo 1845624 2770673 := bstep (se 2 (by rfl) ⟨1039002, by rfl⟩ : syracuseStep 2770673 = 2078005) B2078005
theorem B2770691 : Blo 1845624 2770691 := bstep (se 1 (by rfl) ⟨2078018, by rfl⟩ : syracuseStep 2770691 = 4156037) B4156037
theorem B2770721 : Blo 1845624 2770721 := bstep (se 2 (by rfl) ⟨1039020, by rfl⟩ : syracuseStep 2770721 = 2078041) B2078041
theorem B3114787 : Blo 1845624 3114787 := bstep (se 1 (by rfl) ⟨2336090, by rfl⟩ : syracuseStep 3114787 = 4672181) B4672181
theorem B2770739 : Blo 1845624 2770739 := bstep (se 1 (by rfl) ⟨2078054, by rfl⟩ : syracuseStep 2770739 = 4156109) B4156109
theorem B2770769 : Blo 1845624 2770769 := bstep (se 2 (by rfl) ⟨1039038, by rfl⟩ : syracuseStep 2770769 = 2078077) B2078077
theorem B17745763 : Blo 1845624 17745763 := bstep (se 1 (by rfl) ⟨13309322, by rfl⟩ : syracuseStep 17745763 = 26618645) B26618645
theorem B2770787 : Blo 1845624 2770787 := bstep (se 1 (by rfl) ⟨2078090, by rfl⟩ : syracuseStep 2770787 = 4156181) B4156181
theorem B2336627 : Blo 1845624 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B2770817 : Blo 1845624 2770817 := bstep (se 2 (by rfl) ⟨1039056, by rfl⟩ : syracuseStep 2770817 = 2078113) B2078113
theorem B4155281 : Blo 1845624 4155281 := bstep (se 2 (by rfl) ⟨1558230, by rfl⟩ : syracuseStep 4155281 = 3116461) B3116461
theorem B2770835 : Blo 1845624 2770835 := bstep (se 1 (by rfl) ⟨2078126, by rfl⟩ : syracuseStep 2770835 = 4156253) B4156253
theorem B3942307 : Blo 1845624 3942307 := bstep (se 1 (by rfl) ⟨2956730, by rfl⟩ : syracuseStep 3942307 = 5913461) B5913461
theorem B4155299 : Blo 1845624 4155299 := bstep (se 1 (by rfl) ⟨3116474, by rfl⟩ : syracuseStep 4155299 = 6232949) B6232949
theorem B3114929 : Blo 1845624 3114929 := bstep (se 2 (by rfl) ⟨1168098, by rfl⟩ : syracuseStep 3114929 = 2336197) B2336197
theorem B2770865 : Blo 1845624 2770865 := bstep (se 2 (by rfl) ⟨1039074, by rfl⟩ : syracuseStep 2770865 = 2078149) B2078149
theorem B2770883 : Blo 1845624 2770883 := bstep (se 1 (by rfl) ⟨2078162, by rfl⟩ : syracuseStep 2770883 = 4156325) B4156325
theorem B2770913 : Blo 1845624 2770913 := bstep (se 2 (by rfl) ⟨1039092, by rfl⟩ : syracuseStep 2770913 = 2078185) B2078185
theorem B2959345 : Blo 1845624 2959345 := bstep (se 2 (by rfl) ⟨1109754, by rfl⟩ : syracuseStep 2959345 = 2219509) B2219509
theorem B2770931 : Blo 1845624 2770931 := bstep (se 1 (by rfl) ⟨2078198, by rfl⟩ : syracuseStep 2770931 = 4156397) B4156397
theorem B2770961 : Blo 1845624 2770961 := bstep (se 2 (by rfl) ⟨1039110, by rfl⟩ : syracuseStep 2770961 = 2078221) B2078221
theorem B8996899 : Blo 1845624 8996899 := bstep (se 1 (by rfl) ⟨6747674, by rfl⟩ : syracuseStep 8996899 = 13495349) B13495349
theorem B2770979 : Blo 1845624 2770979 := bstep (se 1 (by rfl) ⟨2078234, by rfl⟩ : syracuseStep 2770979 = 4156469) B4156469
theorem B3115057 : Blo 1845624 3115057 := bstep (se 2 (by rfl) ⟨1168146, by rfl⟩ : syracuseStep 3115057 = 2336293) B2336293
theorem B2771009 : Blo 1845624 2771009 := bstep (se 2 (by rfl) ⟨1039128, by rfl⟩ : syracuseStep 2771009 = 2078257) B2078257
theorem B3115091 : Blo 1845624 3115091 := bstep (se 1 (by rfl) ⟨2336318, by rfl⟩ : syracuseStep 3115091 = 4672637) B4672637
theorem B2771027 : Blo 1845624 2771027 := bstep (se 1 (by rfl) ⟨2078270, by rfl⟩ : syracuseStep 2771027 = 4156541) B4156541
theorem B2771057 : Blo 1845624 2771057 := bstep (se 2 (by rfl) ⟨1039146, by rfl⟩ : syracuseStep 2771057 = 2078293) B2078293
theorem B2771075 : Blo 1845624 2771075 := bstep (se 1 (by rfl) ⟨2078306, by rfl⟩ : syracuseStep 2771075 = 4156613) B4156613
theorem B13494413 : Blo 1845624 13494413 := bstep (se 3 (by rfl) ⟨2530202, by rfl⟩ : syracuseStep 13494413 = 5060405) B5060405
theorem B2771105 : Blo 1845624 2771105 := bstep (se 2 (by rfl) ⟨1039164, by rfl⟩ : syracuseStep 2771105 = 2078329) B2078329
theorem B4155569 : Blo 1845624 4155569 := bstep (se 2 (by rfl) ⟨1558338, by rfl⟩ : syracuseStep 4155569 = 3116677) B3116677
theorem B2771123 : Blo 1845624 2771123 := bstep (se 1 (by rfl) ⟨2078342, by rfl⟩ : syracuseStep 2771123 = 4156685) B4156685
theorem B21022901 : Blo 1845624 21022901 := bstep (se 5 (by rfl) ⟨985448, by rfl⟩ : syracuseStep 21022901 = 1970897) B1970897
theorem B4155587 : Blo 1845624 4155587 := bstep (se 1 (by rfl) ⟨3116690, by rfl⟩ : syracuseStep 4155587 = 6233381) B6233381
theorem B2771153 : Blo 1845624 2771153 := bstep (se 2 (by rfl) ⟨1039182, by rfl⟩ : syracuseStep 2771153 = 2078365) B2078365
theorem B3115219 : Blo 1845624 3115219 := bstep (se 1 (by rfl) ⟨2336414, by rfl⟩ : syracuseStep 3115219 = 4672829) B4672829
theorem B2771171 : Blo 1845624 2771171 := bstep (se 1 (by rfl) ⟨2078378, by rfl⟩ : syracuseStep 2771171 = 4156757) B4156757
theorem B2771201 : Blo 1845624 2771201 := bstep (se 2 (by rfl) ⟨1039200, by rfl⟩ : syracuseStep 2771201 = 2078401) B2078401
theorem B10520837 : Blo 1845624 10520837 := bstep (se 4 (by rfl) ⟨986328, by rfl⟩ : syracuseStep 10520837 = 1972657) B1972657
theorem B2771219 : Blo 1845624 2771219 := bstep (se 1 (by rfl) ⟨2078414, by rfl⟩ : syracuseStep 2771219 = 4156829) B4156829
theorem B2771249 : Blo 1845624 2771249 := bstep (se 2 (by rfl) ⟨1039218, by rfl⟩ : syracuseStep 2771249 = 2078437) B2078437
theorem B2771267 : Blo 1845624 2771267 := bstep (se 1 (by rfl) ⟨2078450, by rfl⟩ : syracuseStep 2771267 = 4156901) B4156901
theorem B3115361 : Blo 1845624 3115361 := bstep (se 2 (by rfl) ⟨1168260, by rfl⟩ : syracuseStep 3115361 = 2336521) B2336521
theorem B2771297 : Blo 1845624 2771297 := bstep (se 2 (by rfl) ⟨1039236, by rfl⟩ : syracuseStep 2771297 = 2078473) B2078473
theorem B5613923 : Blo 1845624 5613923 := bstep (se 1 (by rfl) ⟨4210442, by rfl⟩ : syracuseStep 5613923 = 8420885) B8420885
theorem B4671857 : Blo 1845624 4671857 := bstep (se 2 (by rfl) ⟨1751946, by rfl⟩ : syracuseStep 4671857 = 3503893) B3503893
theorem B3942769 : Blo 1845624 3942769 := bstep (se 2 (by rfl) ⟨1478538, by rfl⟩ : syracuseStep 3942769 = 2957077) B2957077
theorem B2771315 : Blo 1845624 2771315 := bstep (se 1 (by rfl) ⟨2078486, by rfl⟩ : syracuseStep 2771315 = 4156973) B4156973
theorem B1845635 : Blo 1845624 1845635 := bstep (se 1 (by rfl) ⟨1384226, by rfl⟩ : syracuseStep 1845635 = 2768453) B2768453
theorem B10512773 : Blo 1845624 10512773 := bstep (se 4 (by rfl) ⟨985572, by rfl⟩ : syracuseStep 10512773 = 1971145) B1971145
theorem B2771345 : Blo 1845624 2771345 := bstep (se 2 (by rfl) ⟨1039254, by rfl⟩ : syracuseStep 2771345 = 2078509) B2078509
theorem B1845651 : Blo 1845624 1845651 := bstep (se 1 (by rfl) ⟨1384238, by rfl⟩ : syracuseStep 1845651 = 2768477) B2768477
theorem B1845667 : Blo 1845624 1845667 := bstep (se 1 (by rfl) ⟨1384250, by rfl⟩ : syracuseStep 1845667 = 2768501) B2768501
theorem B2771363 : Blo 1845624 2771363 := bstep (se 1 (by rfl) ⟨2078522, by rfl⟩ : syracuseStep 2771363 = 4157045) B4157045
theorem B7014833 : Blo 1845624 7014833 := bstep (se 2 (by rfl) ⟨2630562, by rfl⟩ : syracuseStep 7014833 = 5261125) B5261125
theorem B1845683 : Blo 1845624 1845683 := bstep (se 1 (by rfl) ⟨1384262, by rfl⟩ : syracuseStep 1845683 = 2768525) B2768525
theorem B2771393 : Blo 1845624 2771393 := bstep (se 2 (by rfl) ⟨1039272, by rfl⟩ : syracuseStep 2771393 = 2078545) B2078545
theorem B1845699 : Blo 1845624 1845699 := bstep (se 1 (by rfl) ⟨1384274, by rfl⟩ : syracuseStep 1845699 = 2768549) B2768549
theorem B4155857 : Blo 1845624 4155857 := bstep (se 2 (by rfl) ⟨1558446, by rfl⟩ : syracuseStep 4155857 = 3116893) B3116893
theorem B1845715 : Blo 1845624 1845715 := bstep (se 1 (by rfl) ⟨1384286, by rfl⟩ : syracuseStep 1845715 = 2768573) B2768573
theorem B2771411 : Blo 1845624 2771411 := bstep (se 1 (by rfl) ⟨2078558, by rfl⟩ : syracuseStep 2771411 = 4157117) B4157117
theorem B3115489 : Blo 1845624 3115489 := bstep (se 2 (by rfl) ⟨1168308, by rfl⟩ : syracuseStep 3115489 = 2336617) B2336617
theorem B1845731 : Blo 1845624 1845731 := bstep (se 1 (by rfl) ⟨1384298, by rfl⟩ : syracuseStep 1845731 = 2768597) B2768597
theorem B4155875 : Blo 1845624 4155875 := bstep (se 1 (by rfl) ⟨3116906, by rfl⟩ : syracuseStep 4155875 = 6233813) B6233813
theorem B37923299 : Blo 1845624 37923299 := bstep (se 1 (by rfl) ⟨28442474, by rfl⟩ : syracuseStep 37923299 = 56884949) B56884949
theorem B1845747 : Blo 1845624 1845747 := bstep (se 1 (by rfl) ⟨1384310, by rfl⟩ : syracuseStep 1845747 = 2768621) B2768621
theorem B1845763 : Blo 1845624 1845763 := bstep (se 1 (by rfl) ⟨1384322, by rfl⟩ : syracuseStep 1845763 = 2768645) B2768645
theorem B3115523 : Blo 1845624 3115523 := bstep (se 1 (by rfl) ⟨2336642, by rfl⟩ : syracuseStep 3115523 = 4673285) B4673285
theorem B1845779 : Blo 1845624 1845779 := bstep (se 1 (by rfl) ⟨1384334, by rfl⟩ : syracuseStep 1845779 = 2768669) B2768669
theorem B1845795 : Blo 1845624 1845795 := bstep (se 1 (by rfl) ⟨1384346, by rfl⟩ : syracuseStep 1845795 = 2768693) B2768693
theorem B9349667 : Blo 1845624 9349667 := bstep (se 1 (by rfl) ⟨7012250, by rfl⟩ : syracuseStep 9349667 = 14024501) B14024501
theorem B1845811 : Blo 1845624 1845811 := bstep (se 1 (by rfl) ⟨1384358, by rfl⟩ : syracuseStep 1845811 = 2768717) B2768717
theorem B2337331 : Blo 1845624 2337331 := bstep (se 1 (by rfl) ⟨1752998, by rfl⟩ : syracuseStep 2337331 = 3505997) B3505997
theorem B1845827 : Blo 1845624 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B1845843 : Blo 1845624 1845843 := bstep (se 1 (by rfl) ⟨1384382, by rfl⟩ : syracuseStep 1845843 = 2768765) B2768765
theorem B1845859 : Blo 1845624 1845859 := bstep (se 1 (by rfl) ⟨1384394, by rfl⟩ : syracuseStep 1845859 = 2768789) B2768789
theorem B47966833 : Blo 1845624 47966833 := bstep (se 2 (by rfl) ⟨17987562, by rfl⟩ : syracuseStep 47966833 = 35975125) B35975125
theorem B1845875 : Blo 1845624 1845875 := bstep (se 1 (by rfl) ⟨1384406, by rfl⟩ : syracuseStep 1845875 = 2768813) B2768813
theorem B1845891 : Blo 1845624 1845891 := bstep (se 1 (by rfl) ⟨1384418, by rfl⟩ : syracuseStep 1845891 = 2768837) B2768837
theorem B3115651 : Blo 1845624 3115651 := bstep (se 1 (by rfl) ⟨2336738, by rfl⟩ : syracuseStep 3115651 = 4673477) B4673477
theorem B1845907 : Blo 1845624 1845907 := bstep (se 1 (by rfl) ⟨1384430, by rfl⟩ : syracuseStep 1845907 = 2768861) B2768861
theorem B2337427 : Blo 1845624 2337427 := bstep (se 1 (by rfl) ⟨1753070, by rfl⟩ : syracuseStep 2337427 = 3506141) B3506141
theorem B1845923 : Blo 1845624 1845923 := bstep (se 1 (by rfl) ⟨1384442, by rfl⟩ : syracuseStep 1845923 = 2768885) B2768885
theorem B1845939 : Blo 1845624 1845939 := bstep (se 1 (by rfl) ⟨1384454, by rfl⟩ : syracuseStep 1845939 = 2768909) B2768909
theorem B1845955 : Blo 1845624 1845955 := bstep (se 1 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 1845955 = 2768933) B2768933
theorem B9472717 : Blo 1845624 9472717 := bstep (se 3 (by rfl) ⟨1776134, by rfl⟩ : syracuseStep 9472717 = 3552269) B3552269
theorem B1845971 : Blo 1845624 1845971 := bstep (se 1 (by rfl) ⟨1384478, by rfl⟩ : syracuseStep 1845971 = 2768957) B2768957
theorem B1845987 : Blo 1845624 1845987 := bstep (se 1 (by rfl) ⟨1384490, by rfl⟩ : syracuseStep 1845987 = 2768981) B2768981
theorem B9980657 : Blo 1845624 9980657 := bstep (se 2 (by rfl) ⟨3742746, by rfl⟩ : syracuseStep 9980657 = 7485493) B7485493
theorem B4156145 : Blo 1845624 4156145 := bstep (se 2 (by rfl) ⟨1558554, by rfl⟩ : syracuseStep 4156145 = 3117109) B3117109
theorem B1846003 : Blo 1845624 1846003 := bstep (se 1 (by rfl) ⟨1384502, by rfl⟩ : syracuseStep 1846003 = 2769005) B2769005
theorem B1846019 : Blo 1845624 1846019 := bstep (se 1 (by rfl) ⟨1384514, by rfl⟩ : syracuseStep 1846019 = 2769029) B2769029
theorem B4156163 : Blo 1845624 4156163 := bstep (se 1 (by rfl) ⟨3117122, by rfl⟩ : syracuseStep 4156163 = 6234245) B6234245
theorem B3115793 : Blo 1845624 3115793 := bstep (se 2 (by rfl) ⟨1168422, by rfl⟩ : syracuseStep 3115793 = 2336845) B2336845
theorem B1846035 : Blo 1845624 1846035 := bstep (se 1 (by rfl) ⟨1384526, by rfl⟩ : syracuseStep 1846035 = 2769053) B2769053
theorem B59894549 : Blo 1845624 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B1846051 : Blo 1845624 1846051 := bstep (se 1 (by rfl) ⟨1384538, by rfl⟩ : syracuseStep 1846051 = 2769077) B2769077
theorem B1846067 : Blo 1845624 1846067 := bstep (se 1 (by rfl) ⟨1384550, by rfl⟩ : syracuseStep 1846067 = 2769101) B2769101
theorem B1846083 : Blo 1845624 1846083 := bstep (se 1 (by rfl) ⟨1384562, by rfl⟩ : syracuseStep 1846083 = 2769125) B2769125
theorem B1846099 : Blo 1845624 1846099 := bstep (se 1 (by rfl) ⟨1384574, by rfl⟩ : syracuseStep 1846099 = 2769149) B2769149
theorem B1846115 : Blo 1845624 1846115 := bstep (se 1 (by rfl) ⟨1384586, by rfl⟩ : syracuseStep 1846115 = 2769173) B2769173
theorem B1846131 : Blo 1845624 1846131 := bstep (se 1 (by rfl) ⟨1384598, by rfl⟩ : syracuseStep 1846131 = 2769197) B2769197
theorem B1846147 : Blo 1845624 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B10259341 : Blo 1845624 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B3115921 : Blo 1845624 3115921 := bstep (se 2 (by rfl) ⟨1168470, by rfl⟩ : syracuseStep 3115921 = 2336941) B2336941
theorem B1846163 : Blo 1845624 1846163 := bstep (se 1 (by rfl) ⟨1384622, by rfl⟩ : syracuseStep 1846163 = 2769245) B2769245
theorem B1846179 : Blo 1845624 1846179 := bstep (se 1 (by rfl) ⟨1384634, by rfl⟩ : syracuseStep 1846179 = 2769269) B2769269
theorem B9472945 : Blo 1845624 9472945 := bstep (se 2 (by rfl) ⟨3552354, by rfl⟩ : syracuseStep 9472945 = 7104709) B7104709
theorem B10521521 : Blo 1845624 10521521 := bstep (se 2 (by rfl) ⟨3945570, by rfl⟩ : syracuseStep 10521521 = 7891141) B7891141
theorem B1846195 : Blo 1845624 1846195 := bstep (se 1 (by rfl) ⟨1384646, by rfl⟩ : syracuseStep 1846195 = 2769293) B2769293
theorem B3115955 : Blo 1845624 3115955 := bstep (se 1 (by rfl) ⟨2336966, by rfl⟩ : syracuseStep 3115955 = 4673933) B4673933
theorem B1846211 : Blo 1845624 1846211 := bstep (se 1 (by rfl) ⟨1384658, by rfl⟩ : syracuseStep 1846211 = 2769317) B2769317
theorem B7883725 : Blo 1845624 7883725 := bstep (se 3 (by rfl) ⟨1478198, by rfl⟩ : syracuseStep 7883725 = 2956397) B2956397
theorem B1846227 : Blo 1845624 1846227 := bstep (se 1 (by rfl) ⟨1384670, by rfl⟩ : syracuseStep 1846227 = 2769341) B2769341
theorem B1846243 : Blo 1845624 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B16436195 : Blo 1845624 16436195 := bstep (se 1 (by rfl) ⟨12327146, by rfl⟩ : syracuseStep 16436195 = 24654293) B24654293
theorem B1846259 : Blo 1845624 1846259 := bstep (se 1 (by rfl) ⟨1384694, by rfl⟩ : syracuseStep 1846259 = 2769389) B2769389
theorem B1846275 : Blo 1845624 1846275 := bstep (se 1 (by rfl) ⟨1384706, by rfl⟩ : syracuseStep 1846275 = 2769413) B2769413
theorem B4156433 : Blo 1845624 4156433 := bstep (se 2 (by rfl) ⟨1558662, by rfl⟩ : syracuseStep 4156433 = 3117325) B3117325
theorem B1846291 : Blo 1845624 1846291 := bstep (se 1 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 1846291 = 2769437) B2769437
theorem B1846307 : Blo 1845624 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B4156451 : Blo 1845624 4156451 := bstep (se 1 (by rfl) ⟨3117338, by rfl⟩ : syracuseStep 4156451 = 6234677) B6234677
theorem B1846323 : Blo 1845624 1846323 := bstep (se 1 (by rfl) ⟨1384742, by rfl⟩ : syracuseStep 1846323 = 2769485) B2769485
theorem B3116083 : Blo 1845624 3116083 := bstep (se 1 (by rfl) ⟨2337062, by rfl⟩ : syracuseStep 3116083 = 4674125) B4674125
theorem B1846339 : Blo 1845624 1846339 := bstep (se 1 (by rfl) ⟨1384754, by rfl⟩ : syracuseStep 1846339 = 2769509) B2769509
theorem B1846355 : Blo 1845624 1846355 := bstep (se 1 (by rfl) ⟨1384766, by rfl⟩ : syracuseStep 1846355 = 2769533) B2769533
theorem B1846371 : Blo 1845624 1846371 := bstep (se 1 (by rfl) ⟨1384778, by rfl⟩ : syracuseStep 1846371 = 2769557) B2769557
theorem B1846387 : Blo 1845624 1846387 := bstep (se 1 (by rfl) ⟨1384790, by rfl⟩ : syracuseStep 1846387 = 2769581) B2769581
theorem B1846403 : Blo 1845624 1846403 := bstep (se 1 (by rfl) ⟨1384802, by rfl⟩ : syracuseStep 1846403 = 2769605) B2769605
theorem B2337923 : Blo 1845624 2337923 := bstep (se 1 (by rfl) ⟨1753442, by rfl⟩ : syracuseStep 2337923 = 3506885) B3506885
theorem B1846419 : Blo 1845624 1846419 := bstep (se 1 (by rfl) ⟨1384814, by rfl⟩ : syracuseStep 1846419 = 2769629) B2769629
theorem B1846435 : Blo 1845624 1846435 := bstep (se 1 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 1846435 = 2769653) B2769653
theorem B6229169 : Blo 1845624 6229169 := bstep (se 2 (by rfl) ⟨2335938, by rfl⟩ : syracuseStep 6229169 = 4671877) B4671877
theorem B1846451 : Blo 1845624 1846451 := bstep (se 1 (by rfl) ⟨1384838, by rfl⟩ : syracuseStep 1846451 = 2769677) B2769677
theorem B3116225 : Blo 1845624 3116225 := bstep (se 2 (by rfl) ⟨1168584, by rfl⟩ : syracuseStep 3116225 = 2337169) B2337169
theorem B1846467 : Blo 1845624 1846467 := bstep (se 1 (by rfl) ⟨1384850, by rfl⟩ : syracuseStep 1846467 = 2769701) B2769701
theorem B1846483 : Blo 1845624 1846483 := bstep (se 1 (by rfl) ⟨1384862, by rfl⟩ : syracuseStep 1846483 = 2769725) B2769725
theorem B1846499 : Blo 1845624 1846499 := bstep (se 1 (by rfl) ⟨1384874, by rfl⟩ : syracuseStep 1846499 = 2769749) B2769749
theorem B1846515 : Blo 1845624 1846515 := bstep (se 1 (by rfl) ⟨1384886, by rfl⟩ : syracuseStep 1846515 = 2769773) B2769773
theorem B1846531 : Blo 1845624 1846531 := bstep (se 1 (by rfl) ⟨1384898, by rfl⟩ : syracuseStep 1846531 = 2769797) B2769797
theorem B5614861 : Blo 1845624 5614861 := bstep (se 3 (by rfl) ⟨1052786, by rfl⟩ : syracuseStep 5614861 = 2105573) B2105573
theorem B21040397 : Blo 1845624 21040397 := bstep (se 3 (by rfl) ⟨3945074, by rfl⟩ : syracuseStep 21040397 = 7890149) B7890149
theorem B1846547 : Blo 1845624 1846547 := bstep (se 1 (by rfl) ⟨1384910, by rfl⟩ : syracuseStep 1846547 = 2769821) B2769821
theorem B7884067 : Blo 1845624 7884067 := bstep (se 1 (by rfl) ⟨5913050, by rfl⟩ : syracuseStep 7884067 = 11826101) B11826101
theorem B1846563 : Blo 1845624 1846563 := bstep (se 1 (by rfl) ⟨1384922, by rfl⟩ : syracuseStep 1846563 = 2769845) B2769845
theorem B11234609 : Blo 1845624 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B4156721 : Blo 1845624 4156721 := bstep (se 2 (by rfl) ⟨1558770, by rfl⟩ : syracuseStep 4156721 = 3117541) B3117541
theorem B1846579 : Blo 1845624 1846579 := bstep (se 1 (by rfl) ⟨1384934, by rfl⟩ : syracuseStep 1846579 = 2769869) B2769869
theorem B31567157 : Blo 1845624 31567157 := bstep (se 5 (by rfl) ⟨1479710, by rfl⟩ : syracuseStep 31567157 = 2959421) B2959421
theorem B3116353 : Blo 1845624 3116353 := bstep (se 2 (by rfl) ⟨1168632, by rfl⟩ : syracuseStep 3116353 = 2337265) B2337265
theorem B1846595 : Blo 1845624 1846595 := bstep (se 1 (by rfl) ⟨1384946, by rfl⟩ : syracuseStep 1846595 = 2769893) B2769893
theorem B4156739 : Blo 1845624 4156739 := bstep (se 1 (by rfl) ⟨3117554, by rfl⟩ : syracuseStep 4156739 = 6235109) B6235109
theorem B9350477 : Blo 1845624 9350477 := bstep (se 3 (by rfl) ⟨1753214, by rfl⟩ : syracuseStep 9350477 = 3506429) B3506429
theorem B4672849 : Blo 1845624 4672849 := bstep (se 2 (by rfl) ⟨1752318, by rfl⟩ : syracuseStep 4672849 = 3504637) B3504637
theorem B1846611 : Blo 1845624 1846611 := bstep (se 1 (by rfl) ⟨1384958, by rfl⟩ : syracuseStep 1846611 = 2769917) B2769917
theorem B1846627 : Blo 1845624 1846627 := bstep (se 1 (by rfl) ⟨1384970, by rfl⟩ : syracuseStep 1846627 = 2769941) B2769941
theorem B3116387 : Blo 1845624 3116387 := bstep (se 1 (by rfl) ⟨2337290, by rfl⟩ : syracuseStep 3116387 = 4674581) B4674581
theorem B1846643 : Blo 1845624 1846643 := bstep (se 1 (by rfl) ⟨1384982, by rfl⟩ : syracuseStep 1846643 = 2769965) B2769965
theorem B3943811 : Blo 1845624 3943811 := bstep (se 1 (by rfl) ⟨2957858, by rfl⟩ : syracuseStep 3943811 = 5915717) B5915717
theorem B1846659 : Blo 1845624 1846659 := bstep (se 1 (by rfl) ⟨1384994, by rfl⟩ : syracuseStep 1846659 = 2769989) B2769989
theorem B1846675 : Blo 1845624 1846675 := bstep (se 1 (by rfl) ⟨1385006, by rfl⟩ : syracuseStep 1846675 = 2770013) B2770013
theorem B1871267 : Blo 1845624 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B1846691 : Blo 1845624 1846691 := bstep (se 1 (by rfl) ⟨1385018, by rfl⟩ : syracuseStep 1846691 = 2770037) B2770037
theorem B5615021 : Blo 1845624 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B5918125 : Blo 1845624 5918125 := bstep (se 3 (by rfl) ⟨1109648, by rfl⟩ : syracuseStep 5918125 = 2219297) B2219297
theorem B1846707 : Blo 1845624 1846707 := bstep (se 1 (by rfl) ⟨1385030, by rfl⟩ : syracuseStep 1846707 = 2770061) B2770061
theorem B1846723 : Blo 1845624 1846723 := bstep (se 1 (by rfl) ⟨1385042, by rfl⟩ : syracuseStep 1846723 = 2770085) B2770085
theorem B1846739 : Blo 1845624 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B1846755 : Blo 1845624 1846755 := bstep (se 1 (by rfl) ⟨1385066, by rfl⟩ : syracuseStep 1846755 = 2770133) B2770133
theorem B3116515 : Blo 1845624 3116515 := bstep (se 1 (by rfl) ⟨2337386, by rfl⟩ : syracuseStep 3116515 = 4674773) B4674773
theorem B4435441 : Blo 1845624 4435441 := bstep (se 2 (by rfl) ⟨1663290, by rfl⟩ : syracuseStep 4435441 = 3326581) B3326581
theorem B1846771 : Blo 1845624 1846771 := bstep (se 1 (by rfl) ⟨1385078, by rfl⟩ : syracuseStep 1846771 = 2770157) B2770157
theorem B1846787 : Blo 1845624 1846787 := bstep (se 1 (by rfl) ⟨1385090, by rfl⟩ : syracuseStep 1846787 = 2770181) B2770181
theorem B1846803 : Blo 1845624 1846803 := bstep (se 1 (by rfl) ⟨1385102, by rfl⟩ : syracuseStep 1846803 = 2770205) B2770205
theorem B1846819 : Blo 1845624 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B1846835 : Blo 1845624 1846835 := bstep (se 1 (by rfl) ⟨1385126, by rfl⟩ : syracuseStep 1846835 = 2770253) B2770253
theorem B1846851 : Blo 1845624 1846851 := bstep (se 1 (by rfl) ⟨1385138, by rfl⟩ : syracuseStep 1846851 = 2770277) B2770277
theorem B4157009 : Blo 1845624 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B1846867 : Blo 1845624 1846867 := bstep (se 1 (by rfl) ⟨1385150, by rfl⟩ : syracuseStep 1846867 = 2770301) B2770301
theorem B4673123 : Blo 1845624 4673123 := bstep (se 1 (by rfl) ⟨3504842, by rfl⟩ : syracuseStep 4673123 = 7009685) B7009685
theorem B1846883 : Blo 1845624 1846883 := bstep (se 1 (by rfl) ⟨1385162, by rfl⟩ : syracuseStep 1846883 = 2770325) B2770325
theorem B4157027 : Blo 1845624 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B3116657 : Blo 1845624 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B22777457 : Blo 1845624 22777457 := bstep (se 2 (by rfl) ⟨8541546, by rfl⟩ : syracuseStep 22777457 = 17083093) B17083093
theorem B1846899 : Blo 1845624 1846899 := bstep (se 1 (by rfl) ⟨1385174, by rfl⟩ : syracuseStep 1846899 = 2770349) B2770349
theorem B1846915 : Blo 1845624 1846915 := bstep (se 1 (by rfl) ⟨1385186, by rfl⟩ : syracuseStep 1846915 = 2770373) B2770373
theorem B5615249 : Blo 1845624 5615249 := bstep (se 2 (by rfl) ⟨2105718, by rfl⟩ : syracuseStep 5615249 = 4211437) B4211437
theorem B1846931 : Blo 1845624 1846931 := bstep (se 1 (by rfl) ⟨1385198, by rfl⟩ : syracuseStep 1846931 = 2770397) B2770397
theorem B1846947 : Blo 1845624 1846947 := bstep (se 1 (by rfl) ⟨1385210, by rfl⟩ : syracuseStep 1846947 = 2770421) B2770421
theorem B1846963 : Blo 1845624 1846963 := bstep (se 1 (by rfl) ⟨1385222, by rfl⟩ : syracuseStep 1846963 = 2770445) B2770445
theorem B1846979 : Blo 1845624 1846979 := bstep (se 1 (by rfl) ⟨1385234, by rfl⟩ : syracuseStep 1846979 = 2770469) B2770469
theorem B6229709 : Blo 1845624 6229709 := bstep (se 3 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 6229709 = 2336141) B2336141
theorem B6745805 : Blo 1845624 6745805 := bstep (se 3 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 6745805 = 2529677) B2529677
theorem B1846995 : Blo 1845624 1846995 := bstep (se 1 (by rfl) ⟨1385246, by rfl⟩ : syracuseStep 1846995 = 2770493) B2770493
theorem B1847011 : Blo 1845624 1847011 := bstep (se 1 (by rfl) ⟨1385258, by rfl⟩ : syracuseStep 1847011 = 2770517) B2770517
theorem B6319853 : Blo 1845624 6319853 := bstep (se 3 (by rfl) ⟨1184972, by rfl⟩ : syracuseStep 6319853 = 2369945) B2369945
theorem B11833073 : Blo 1845624 11833073 := bstep (se 2 (by rfl) ⟨4437402, by rfl⟩ : syracuseStep 11833073 = 8874805) B8874805
theorem B3116785 : Blo 1845624 3116785 := bstep (se 2 (by rfl) ⟨1168794, by rfl⟩ : syracuseStep 3116785 = 2337589) B2337589
theorem B2076403 : Blo 1845624 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B1847027 : Blo 1845624 1847027 := bstep (se 1 (by rfl) ⟨1385270, by rfl⟩ : syracuseStep 1847027 = 2770541) B2770541
theorem B6229763 : Blo 1845624 6229763 := bstep (se 1 (by rfl) ⟨4672322, by rfl⟩ : syracuseStep 6229763 = 9344645) B9344645
theorem B1847043 : Blo 1845624 1847043 := bstep (se 1 (by rfl) ⟨1385282, by rfl⟩ : syracuseStep 1847043 = 2770565) B2770565
theorem B3116819 : Blo 1845624 3116819 := bstep (se 1 (by rfl) ⟨2337614, by rfl⟩ : syracuseStep 3116819 = 4675229) B4675229
theorem B1847059 : Blo 1845624 1847059 := bstep (se 1 (by rfl) ⟨1385294, by rfl⟩ : syracuseStep 1847059 = 2770589) B2770589
theorem B4673315 : Blo 1845624 4673315 := bstep (se 1 (by rfl) ⟨3504986, by rfl⟩ : syracuseStep 4673315 = 7009973) B7009973
theorem B1847075 : Blo 1845624 1847075 := bstep (se 1 (by rfl) ⟨1385306, by rfl⟩ : syracuseStep 1847075 = 2770613) B2770613
theorem B1847091 : Blo 1845624 1847091 := bstep (se 1 (by rfl) ⟨1385318, by rfl⟩ : syracuseStep 1847091 = 2770637) B2770637
theorem B1847107 : Blo 1845624 1847107 := bstep (se 1 (by rfl) ⟨1385330, by rfl⟩ : syracuseStep 1847107 = 2770661) B2770661
theorem B1847123 : Blo 1845624 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B1847139 : Blo 1845624 1847139 := bstep (se 1 (by rfl) ⟨1385354, by rfl⟩ : syracuseStep 1847139 = 2770709) B2770709
theorem B1847155 : Blo 1845624 1847155 := bstep (se 1 (by rfl) ⟨1385366, by rfl⟩ : syracuseStep 1847155 = 2770733) B2770733
theorem B2076547 : Blo 1845624 2076547 := bstep (se 1 (by rfl) ⟨1557410, by rfl⟩ : syracuseStep 2076547 = 3114821) B3114821
theorem B3944323 : Blo 1845624 3944323 := bstep (se 1 (by rfl) ⟨2958242, by rfl⟩ : syracuseStep 3944323 = 5916485) B5916485
theorem B1847171 : Blo 1845624 1847171 := bstep (se 1 (by rfl) ⟨1385378, by rfl⟩ : syracuseStep 1847171 = 2770757) B2770757
theorem B3116947 : Blo 1845624 3116947 := bstep (se 1 (by rfl) ⟨2337710, by rfl⟩ : syracuseStep 3116947 = 4675421) B4675421
theorem B1847187 : Blo 1845624 1847187 := bstep (se 1 (by rfl) ⟨1385390, by rfl⟩ : syracuseStep 1847187 = 2770781) B2770781
theorem B1847203 : Blo 1845624 1847203 := bstep (se 1 (by rfl) ⟨1385402, by rfl⟩ : syracuseStep 1847203 = 2770805) B2770805
theorem B1871795 : Blo 1845624 1871795 := bstep (se 1 (by rfl) ⟨1403846, by rfl⟩ : syracuseStep 1871795 = 2807693) B2807693
theorem B1847219 : Blo 1845624 1847219 := bstep (se 1 (by rfl) ⟨1385414, by rfl⟩ : syracuseStep 1847219 = 2770829) B2770829
theorem B1847235 : Blo 1845624 1847235 := bstep (se 1 (by rfl) ⟨1385426, by rfl⟩ : syracuseStep 1847235 = 2770853) B2770853
theorem B1847251 : Blo 1845624 1847251 := bstep (se 1 (by rfl) ⟨1385438, by rfl⟩ : syracuseStep 1847251 = 2770877) B2770877
theorem B7008227 : Blo 1845624 7008227 := bstep (se 1 (by rfl) ⟨5256170, by rfl⟩ : syracuseStep 7008227 = 10512341) B10512341
theorem B1847267 : Blo 1845624 1847267 := bstep (se 1 (by rfl) ⟨1385450, by rfl⟩ : syracuseStep 1847267 = 2770901) B2770901
theorem B7008241 : Blo 1845624 7008241 := bstep (se 2 (by rfl) ⟨2628090, by rfl⟩ : syracuseStep 7008241 = 5256181) B5256181
theorem B1847283 : Blo 1845624 1847283 := bstep (se 1 (by rfl) ⟨1385462, by rfl⟩ : syracuseStep 1847283 = 2770925) B2770925
theorem B1847299 : Blo 1845624 1847299 := bstep (se 1 (by rfl) ⟨1385474, by rfl⟩ : syracuseStep 1847299 = 2770949) B2770949
theorem B6230033 : Blo 1845624 6230033 := bstep (se 2 (by rfl) ⟨2336262, by rfl⟩ : syracuseStep 6230033 = 4672525) B4672525
theorem B2076691 : Blo 1845624 2076691 := bstep (se 1 (by rfl) ⟨1557518, by rfl⟩ : syracuseStep 2076691 = 3115037) B3115037
theorem B1847315 : Blo 1845624 1847315 := bstep (se 1 (by rfl) ⟨1385486, by rfl⟩ : syracuseStep 1847315 = 2770973) B2770973
theorem B3117089 : Blo 1845624 3117089 := bstep (se 2 (by rfl) ⟨1168908, by rfl⟩ : syracuseStep 3117089 = 2337817) B2337817
theorem B1847331 : Blo 1845624 1847331 := bstep (se 1 (by rfl) ⟨1385498, by rfl⟩ : syracuseStep 1847331 = 2770997) B2770997
theorem B4993073 : Blo 1845624 4993073 := bstep (se 2 (by rfl) ⟨1872402, by rfl⟩ : syracuseStep 4993073 = 3744805) B3744805
theorem B1847347 : Blo 1845624 1847347 := bstep (se 1 (by rfl) ⟨1385510, by rfl⟩ : syracuseStep 1847347 = 2771021) B2771021
theorem B1847363 : Blo 1845624 1847363 := bstep (se 1 (by rfl) ⟨1385522, by rfl⟩ : syracuseStep 1847363 = 2771045) B2771045
theorem B1847379 : Blo 1845624 1847379 := bstep (se 1 (by rfl) ⟨1385534, by rfl⟩ : syracuseStep 1847379 = 2771069) B2771069
theorem B1847395 : Blo 1845624 1847395 := bstep (se 1 (by rfl) ⟨1385546, by rfl⟩ : syracuseStep 1847395 = 2771093) B2771093
theorem B1847411 : Blo 1845624 1847411 := bstep (se 1 (by rfl) ⟨1385558, by rfl⟩ : syracuseStep 1847411 = 2771117) B2771117
theorem B5615747 : Blo 1845624 5615747 := bstep (se 1 (by rfl) ⟨4211810, by rfl⟩ : syracuseStep 5615747 = 8423621) B8423621
theorem B1847427 : Blo 1845624 1847427 := bstep (se 1 (by rfl) ⟨1385570, by rfl⟩ : syracuseStep 1847427 = 2771141) B2771141
theorem B1847443 : Blo 1845624 1847443 := bstep (se 1 (by rfl) ⟨1385582, by rfl⟩ : syracuseStep 1847443 = 2771165) B2771165
theorem B3117217 : Blo 1845624 3117217 := bstep (se 2 (by rfl) ⟨1168956, by rfl⟩ : syracuseStep 3117217 = 2337913) B2337913
theorem B2076835 : Blo 1845624 2076835 := bstep (se 1 (by rfl) ⟨1557626, by rfl⟩ : syracuseStep 2076835 = 3115253) B3115253
theorem B1847459 : Blo 1845624 1847459 := bstep (se 1 (by rfl) ⟨1385594, by rfl⟩ : syracuseStep 1847459 = 2771189) B2771189
theorem B1847475 : Blo 1845624 1847475 := bstep (se 1 (by rfl) ⟨1385606, by rfl⟩ : syracuseStep 1847475 = 2771213) B2771213
theorem B3117251 : Blo 1845624 3117251 := bstep (se 1 (by rfl) ⟨2337938, by rfl⟩ : syracuseStep 3117251 = 4675877) B4675877
theorem B1847491 : Blo 1845624 1847491 := bstep (se 1 (by rfl) ⟨1385618, by rfl⟩ : syracuseStep 1847491 = 2771237) B2771237
theorem B1847507 : Blo 1845624 1847507 := bstep (se 1 (by rfl) ⟨1385630, by rfl⟩ : syracuseStep 1847507 = 2771261) B2771261
theorem B1847523 : Blo 1845624 1847523 := bstep (se 1 (by rfl) ⟨1385642, by rfl⟩ : syracuseStep 1847523 = 2771285) B2771285
theorem B1847539 : Blo 1845624 1847539 := bstep (se 1 (by rfl) ⟨1385654, by rfl⟩ : syracuseStep 1847539 = 2771309) B2771309
theorem B1847555 : Blo 1845624 1847555 := bstep (se 1 (by rfl) ⟨1385666, by rfl⟩ : syracuseStep 1847555 = 2771333) B2771333
theorem B1847571 : Blo 1845624 1847571 := bstep (se 1 (by rfl) ⟨1385678, by rfl⟩ : syracuseStep 1847571 = 2771357) B2771357
theorem B1847587 : Blo 1845624 1847587 := bstep (se 1 (by rfl) ⟨1385690, by rfl⟩ : syracuseStep 1847587 = 2771381) B2771381
theorem B2076979 : Blo 1845624 2076979 := bstep (se 1 (by rfl) ⟨1557734, by rfl⟩ : syracuseStep 2076979 = 3115469) B3115469
theorem B1847603 : Blo 1845624 1847603 := bstep (se 1 (by rfl) ⟨1385702, by rfl⟩ : syracuseStep 1847603 = 2771405) B2771405
theorem B3117379 : Blo 1845624 3117379 := bstep (se 1 (by rfl) ⟨2338034, by rfl⟩ : syracuseStep 3117379 = 4676069) B4676069
theorem B1847619 : Blo 1845624 1847619 := bstep (se 1 (by rfl) ⟨1385714, by rfl⟩ : syracuseStep 1847619 = 2771429) B2771429
theorem B9982385 : Blo 1845624 9982385 := bstep (se 2 (by rfl) ⟨3743394, by rfl⟩ : syracuseStep 9982385 = 7486789) B7486789
theorem B2077123 : Blo 1845624 2077123 := bstep (se 1 (by rfl) ⟨1557842, by rfl⟩ : syracuseStep 2077123 = 3115685) B3115685
theorem B3117521 : Blo 1845624 3117521 := bstep (se 2 (by rfl) ⟨1169070, by rfl⟩ : syracuseStep 3117521 = 2338141) B2338141
theorem B13308401 : Blo 1845624 13308401 := bstep (se 2 (by rfl) ⟨4990650, by rfl⟩ : syracuseStep 13308401 = 9981301) B9981301
theorem B3551779 : Blo 1845624 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B6230573 : Blo 1845624 6230573 := bstep (se 3 (by rfl) ⟨1168232, by rfl⟩ : syracuseStep 6230573 = 2336465) B2336465
theorem B3945041 : Blo 1845624 3945041 := bstep (se 2 (by rfl) ⟨1479390, by rfl⟩ : syracuseStep 3945041 = 2958781) B2958781
theorem B3117649 : Blo 1845624 3117649 := bstep (se 2 (by rfl) ⟨1169118, by rfl⟩ : syracuseStep 3117649 = 2338237) B2338237
theorem B2077267 : Blo 1845624 2077267 := bstep (se 1 (by rfl) ⟨1557950, by rfl⟩ : syracuseStep 2077267 = 3115901) B3115901
theorem B6230627 : Blo 1845624 6230627 := bstep (se 1 (by rfl) ⟨4672970, by rfl⟩ : syracuseStep 6230627 = 9345941) B9345941
theorem B3117683 : Blo 1845624 3117683 := bstep (se 1 (by rfl) ⟨2338262, by rfl⟩ : syracuseStep 3117683 = 4676525) B4676525
theorem B4674257 : Blo 1845624 4674257 := bstep (se 2 (by rfl) ⟨1752846, by rfl⟩ : syracuseStep 4674257 = 3505693) B3505693
theorem B2077411 : Blo 1845624 2077411 := bstep (se 1 (by rfl) ⟨1558058, by rfl⟩ : syracuseStep 2077411 = 3116117) B3116117
theorem B3117811 : Blo 1845624 3117811 := bstep (se 1 (by rfl) ⟨2338358, by rfl⟩ : syracuseStep 3117811 = 4676717) B4676717
theorem B4674307 : Blo 1845624 4674307 := bstep (se 1 (by rfl) ⟨3505730, by rfl⟩ : syracuseStep 4674307 = 7011461) B7011461
theorem B33682229 : Blo 1845624 33682229 := bstep (se 5 (by rfl) ⟨1578854, by rfl⟩ : syracuseStep 33682229 = 3157709) B3157709
theorem B6230897 : Blo 1845624 6230897 := bstep (se 2 (by rfl) ⟨2336586, by rfl⟩ : syracuseStep 6230897 = 4673173) B4673173
theorem B2077555 : Blo 1845624 2077555 := bstep (se 1 (by rfl) ⟨1558166, by rfl⟩ : syracuseStep 2077555 = 3116333) B3116333
theorem B4674449 : Blo 1845624 4674449 := bstep (se 2 (by rfl) ⟨1752918, by rfl⟩ : syracuseStep 4674449 = 3505837) B3505837
theorem B2077699 : Blo 1845624 2077699 := bstep (se 1 (by rfl) ⟨1558274, by rfl⟩ : syracuseStep 2077699 = 3116549) B3116549
theorem B5256227 : Blo 1845624 5256227 := bstep (se 1 (by rfl) ⟨3942170, by rfl⟩ : syracuseStep 5256227 = 7884341) B7884341
theorem B11990051 : Blo 1845624 11990051 := bstep (se 1 (by rfl) ⟨8992538, by rfl⟩ : syracuseStep 11990051 = 17985077) B17985077
theorem B2077843 : Blo 1845624 2077843 := bstep (se 1 (by rfl) ⟨1558382, by rfl⟩ : syracuseStep 2077843 = 3116765) B3116765
theorem B6657187 : Blo 1845624 6657187 := bstep (se 1 (by rfl) ⟨4992890, by rfl⟩ : syracuseStep 6657187 = 9985781) B9985781
theorem B1971427 : Blo 1845624 1971427 := bstep (se 1 (by rfl) ⟨1478570, by rfl⟩ : syracuseStep 1971427 = 2957141) B2957141
theorem B2077987 : Blo 1845624 2077987 := bstep (se 1 (by rfl) ⟨1558490, by rfl⟩ : syracuseStep 2077987 = 3116981) B3116981
theorem B3945827 : Blo 1845624 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B6231437 : Blo 1845624 6231437 := bstep (se 3 (by rfl) ⟨1168394, by rfl⟩ : syracuseStep 6231437 = 2336789) B2336789
theorem B7009699 : Blo 1845624 7009699 := bstep (se 1 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 7009699 = 10514549) B10514549
theorem B2078131 : Blo 1845624 2078131 := bstep (se 1 (by rfl) ⟨1558598, by rfl⟩ : syracuseStep 2078131 = 3117197) B3117197
theorem B6231491 : Blo 1845624 6231491 := bstep (se 1 (by rfl) ⟨4673618, by rfl⟩ : syracuseStep 6231491 = 9347237) B9347237
theorem B9344483 : Blo 1845624 9344483 := bstep (se 1 (by rfl) ⟨7008362, by rfl⟩ : syracuseStep 9344483 = 14016725) B14016725
theorem B2528753 : Blo 1845624 2528753 := bstep (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) B1896565
theorem B2078275 : Blo 1845624 2078275 := bstep (se 1 (by rfl) ⟨1558706, by rfl⟩ : syracuseStep 2078275 = 3117413) B3117413
theorem B21034565 : Blo 1845624 21034565 := bstep (se 4 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 21034565 = 3943981) B3943981
theorem B23656049 : Blo 1845624 23656049 := bstep (se 2 (by rfl) ⟨8871018, by rfl⟩ : syracuseStep 23656049 = 17742037) B17742037
theorem B18945677 : Blo 1845624 18945677 := bstep (se 3 (by rfl) ⟨3552314, by rfl⟩ : syracuseStep 18945677 = 7104629) B7104629
theorem B6231761 : Blo 1845624 6231761 := bstep (se 2 (by rfl) ⟨2336910, by rfl⟩ : syracuseStep 6231761 = 4673821) B4673821
theorem B2078419 : Blo 1845624 2078419 := bstep (se 1 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 2078419 = 3117629) B3117629
theorem B2078563 : Blo 1845624 2078563 := bstep (se 1 (by rfl) ⟨1558922, by rfl⟩ : syracuseStep 2078563 = 3117845) B3117845
theorem B4675441 : Blo 1845624 4675441 := bstep (se 2 (by rfl) ⟨1753290, by rfl⟩ : syracuseStep 4675441 = 3506581) B3506581
theorem B119740301 : Blo 1845624 119740301 := bstep (se 3 (by rfl) ⟨22451306, by rfl⟩ : syracuseStep 119740301 = 44902613) B44902613
theorem B15783821 : Blo 1845624 15783821 := bstep (se 3 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 15783821 = 5918933) B5918933
theorem B11827205 : Blo 1845624 11827205 := bstep (se 4 (by rfl) ⟨1108800, by rfl⟩ : syracuseStep 11827205 = 2217601) B2217601
theorem B1972307 : Blo 1845624 1972307 := bstep (se 1 (by rfl) ⟨1479230, by rfl⟩ : syracuseStep 1972307 = 2958461) B2958461
theorem B21043313 : Blo 1845624 21043313 := bstep (se 2 (by rfl) ⟨7891242, by rfl⟩ : syracuseStep 21043313 = 15782485) B15782485
theorem B4675715 : Blo 1845624 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B9353393 : Blo 1845624 9353393 := bstep (se 2 (by rfl) ⟨3507522, by rfl⟩ : syracuseStep 9353393 = 7015045) B7015045
theorem B2218163 : Blo 1845624 2218163 := bstep (se 1 (by rfl) ⟨1663622, by rfl⟩ : syracuseStep 2218163 = 3327245) B3327245
theorem B1972435 : Blo 1845624 1972435 := bstep (se 1 (by rfl) ⟨1479326, by rfl⟩ : syracuseStep 1972435 = 2958653) B2958653
theorem B6232301 : Blo 1845624 6232301 := bstep (se 3 (by rfl) ⟨1168556, by rfl⟩ : syracuseStep 6232301 = 2337113) B2337113
theorem B5257457 : Blo 1845624 5257457 := bstep (se 2 (by rfl) ⟨1971546, by rfl⟩ : syracuseStep 5257457 = 3943093) B3943093
theorem B9345293 : Blo 1845624 9345293 := bstep (se 3 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 9345293 = 3504485) B3504485
theorem B2218259 : Blo 1845624 2218259 := bstep (se 1 (by rfl) ⟨1663694, by rfl⟩ : syracuseStep 2218259 = 3327389) B3327389
theorem B6232355 : Blo 1845624 6232355 := bstep (se 1 (by rfl) ⟨4674266, by rfl⟩ : syracuseStep 6232355 = 9348533) B9348533
theorem B4438307 : Blo 1845624 4438307 := bstep (se 1 (by rfl) ⟨3328730, by rfl⟩ : syracuseStep 4438307 = 6657461) B6657461
theorem B4675907 : Blo 1845624 4675907 := bstep (se 1 (by rfl) ⟨3506930, by rfl⟩ : syracuseStep 4675907 = 7013861) B7013861
theorem B2808209 : Blo 1845624 2808209 := bstep (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) B2106157
theorem B8419825 : Blo 1845624 8419825 := bstep (se 2 (by rfl) ⟨3157434, by rfl⟩ : syracuseStep 8419825 = 6314869) B6314869
theorem B13310477 : Blo 1845624 13310477 := bstep (se 3 (by rfl) ⟨2495714, by rfl⟩ : syracuseStep 13310477 = 4991429) B4991429
theorem B6232625 : Blo 1845624 6232625 := bstep (se 2 (by rfl) ⟨2337234, by rfl⟩ : syracuseStep 6232625 = 4674469) B4674469
theorem B3504721 : Blo 1845624 3504721 := bstep (se 2 (by rfl) ⟨1314270, by rfl⟩ : syracuseStep 3504721 = 2628541) B2628541
theorem B5995235 : Blo 1845624 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B4209475 : Blo 1845624 4209475 := bstep (se 1 (by rfl) ⟨3157106, by rfl⟩ : syracuseStep 4209475 = 6314213) B6314213
theorem B3554147 : Blo 1845624 3554147 := bstep (se 1 (by rfl) ⟨2665610, by rfl⟩ : syracuseStep 3554147 = 5331221) B5331221
theorem B4438979 : Blo 1845624 4438979 := bstep (se 1 (by rfl) ⟨3329234, by rfl⟩ : syracuseStep 4438979 = 6658469) B6658469
theorem B3505123 : Blo 1845624 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B3505169 : Blo 1845624 3505169 := bstep (se 2 (by rfl) ⟨1314438, by rfl⟩ : syracuseStep 3505169 = 2628877) B2628877
theorem B6233165 : Blo 1845624 6233165 := bstep (se 3 (by rfl) ⟨1168718, by rfl⟩ : syracuseStep 6233165 = 2337437) B2337437
theorem B22453361 : Blo 1845624 22453361 := bstep (se 2 (by rfl) ⟨8420010, by rfl⟩ : syracuseStep 22453361 = 16840021) B16840021
theorem B6233219 : Blo 1845624 6233219 := bstep (se 1 (by rfl) ⟨4674914, by rfl⟩ : syracuseStep 6233219 = 9349829) B9349829
theorem B2628769 : Blo 1845624 2628769 := bstep (se 2 (by rfl) ⟨985788, by rfl⟩ : syracuseStep 2628769 = 1971577) B1971577
theorem B4439249 : Blo 1845624 4439249 := bstep (se 2 (by rfl) ⟨1664718, by rfl⟩ : syracuseStep 4439249 = 3329437) B3329437
theorem B2956513 : Blo 1845624 2956513 := bstep (se 2 (by rfl) ⟨1108692, by rfl⟩ : syracuseStep 2956513 = 2217385) B2217385
theorem B7888099 : Blo 1845624 7888099 := bstep (se 1 (by rfl) ⟨5916074, by rfl⟩ : syracuseStep 7888099 = 11832149) B11832149
theorem B2628865 : Blo 1845624 2628865 := bstep (se 2 (by rfl) ⟨985824, by rfl⟩ : syracuseStep 2628865 = 1971649) B1971649
theorem B5061923 : Blo 1845624 5061923 := bstep (se 1 (by rfl) ⟨3796442, by rfl⟩ : syracuseStep 5061923 = 7592885) B7592885
theorem B3505457 : Blo 1845624 3505457 := bstep (se 2 (by rfl) ⟨1314546, by rfl⟩ : syracuseStep 3505457 = 2629093) B2629093
theorem B6749489 : Blo 1845624 6749489 := bstep (se 2 (by rfl) ⟨2531058, by rfl⟩ : syracuseStep 6749489 = 5062117) B5062117
theorem B4152689 : Blo 1845624 4152689 := bstep (se 2 (by rfl) ⟨1557258, by rfl⟩ : syracuseStep 4152689 = 3114517) B3114517
theorem B4152707 : Blo 1845624 4152707 := bstep (se 1 (by rfl) ⟨3114530, by rfl⟩ : syracuseStep 4152707 = 6229061) B6229061
theorem B22453645 : Blo 1845624 22453645 := bstep (se 3 (by rfl) ⟨4210058, by rfl⟩ : syracuseStep 22453645 = 8420117) B8420117
theorem B6233489 : Blo 1845624 6233489 := bstep (se 2 (by rfl) ⟨2337558, by rfl⟩ : syracuseStep 6233489 = 4675117) B4675117
theorem B7200269 : Blo 1845624 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B2530883 : Blo 1845624 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B7011917 : Blo 1845624 7011917 := bstep (se 3 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 7011917 = 2629469) B2629469
theorem B2768465 : Blo 1845624 2768465 := bstep (se 2 (by rfl) ⟨1038174, by rfl⟩ : syracuseStep 2768465 = 2076349) B2076349
theorem B2768483 : Blo 1845624 2768483 := bstep (se 1 (by rfl) ⟨2076362, by rfl⟩ : syracuseStep 2768483 = 4152725) B4152725
theorem B2768513 : Blo 1845624 2768513 := bstep (se 2 (by rfl) ⟨1038192, by rfl⟩ : syracuseStep 2768513 = 2076385) B2076385
theorem B35503757 : Blo 1845624 35503757 := bstep (se 3 (by rfl) ⟨6656954, by rfl⟩ : syracuseStep 35503757 = 13313909) B13313909
theorem B4152977 : Blo 1845624 4152977 := bstep (se 2 (by rfl) ⟨1557366, by rfl⟩ : syracuseStep 4152977 = 3114733) B3114733
theorem B2768531 : Blo 1845624 2768531 := bstep (se 1 (by rfl) ⟨2076398, by rfl⟩ : syracuseStep 2768531 = 4152797) B4152797
theorem B4152995 : Blo 1845624 4152995 := bstep (se 1 (by rfl) ⟨3114746, by rfl⟩ : syracuseStep 4152995 = 6229493) B6229493
theorem B5258915 : Blo 1845624 5258915 := bstep (se 1 (by rfl) ⟨3944186, by rfl⟩ : syracuseStep 5258915 = 7888373) B7888373
theorem B2768561 : Blo 1845624 2768561 := bstep (se 2 (by rfl) ⟨1038210, by rfl⟩ : syracuseStep 2768561 = 2076421) B2076421
theorem B2768579 : Blo 1845624 2768579 := bstep (se 1 (by rfl) ⟨2076434, by rfl⟩ : syracuseStep 2768579 = 4152869) B4152869
theorem B2768609 : Blo 1845624 2768609 := bstep (se 2 (by rfl) ⟨1038228, by rfl⟩ : syracuseStep 2768609 = 2076457) B2076457
theorem B2629361 : Blo 1845624 2629361 := bstep (se 2 (by rfl) ⟨986010, by rfl⟩ : syracuseStep 2629361 = 1972021) B1972021
theorem B2768627 : Blo 1845624 2768627 := bstep (se 1 (by rfl) ⟨2076470, by rfl⟩ : syracuseStep 2768627 = 4152941) B4152941
theorem B2768657 : Blo 1845624 2768657 := bstep (se 2 (by rfl) ⟨1038246, by rfl⟩ : syracuseStep 2768657 = 2076493) B2076493
theorem B2768675 : Blo 1845624 2768675 := bstep (se 1 (by rfl) ⟨2076506, by rfl⟩ : syracuseStep 2768675 = 4153013) B4153013
theorem B2768705 : Blo 1845624 2768705 := bstep (se 2 (by rfl) ⟨1038264, by rfl⟩ : syracuseStep 2768705 = 2076529) B2076529
theorem B3997507 : Blo 1845624 3997507 := bstep (se 1 (by rfl) ⟨2998130, by rfl⟩ : syracuseStep 3997507 = 5996261) B5996261
theorem B2768723 : Blo 1845624 2768723 := bstep (se 1 (by rfl) ⟨2076542, by rfl⟩ : syracuseStep 2768723 = 4153085) B4153085
theorem B2768753 : Blo 1845624 2768753 := bstep (se 2 (by rfl) ⟨1038282, by rfl⟩ : syracuseStep 2768753 = 2076565) B2076565
theorem B2768771 : Blo 1845624 2768771 := bstep (se 1 (by rfl) ⟨2076578, by rfl⟩ : syracuseStep 2768771 = 4153157) B4153157
theorem B2776979 : Blo 1845624 2776979 := bstep (se 1 (by rfl) ⟨2082734, by rfl⟩ : syracuseStep 2776979 = 4165469) B4165469
theorem B2768801 : Blo 1845624 2768801 := bstep (se 2 (by rfl) ⟨1038300, by rfl⟩ : syracuseStep 2768801 = 2076601) B2076601
theorem B6234029 : Blo 1845624 6234029 := bstep (se 3 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 6234029 = 2337761) B2337761
theorem B4153265 : Blo 1845624 4153265 := bstep (se 2 (by rfl) ⟨1557474, by rfl⟩ : syracuseStep 4153265 = 3114949) B3114949
theorem B2768819 : Blo 1845624 2768819 := bstep (se 1 (by rfl) ⟨2076614, by rfl⟩ : syracuseStep 2768819 = 4153229) B4153229
theorem B4153283 : Blo 1845624 4153283 := bstep (se 1 (by rfl) ⟨3114962, by rfl⟩ : syracuseStep 4153283 = 6229925) B6229925
theorem B2768849 : Blo 1845624 2768849 := bstep (se 2 (by rfl) ⟨1038318, by rfl⟩ : syracuseStep 2768849 = 2076637) B2076637
theorem B2768867 : Blo 1845624 2768867 := bstep (se 1 (by rfl) ⟨2076650, by rfl⟩ : syracuseStep 2768867 = 4153301) B4153301
theorem B6234083 : Blo 1845624 6234083 := bstep (se 1 (by rfl) ⟨4675562, by rfl⟩ : syracuseStep 6234083 = 9351125) B9351125
theorem B4153355 : Blo 1845624 4153355 := bstep (se 1 (by rfl) ⟨3115016, by rfl⟩ : syracuseStep 4153355 = 6230033) B6230033
theorem B2768921 : Blo 1845624 2768921 := bstep (se 2 (by rfl) ⟨1038345, by rfl⟩ : syracuseStep 2768921 = 2076691) B2076691
theorem B7012403 : Blo 1845624 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B4153409 : Blo 1845624 4153409 := bstep (se 2 (by rfl) ⟨1557528, by rfl⟩ : syracuseStep 4153409 = 3115057) B3115057
theorem B5996609 : Blo 1845624 5996609 := bstep (se 2 (by rfl) ⟨2248728, by rfl⟩ : syracuseStep 5996609 = 4497457) B4497457
theorem B3743831 : Blo 1845624 3743831 := bstep (se 1 (by rfl) ⟨2807873, by rfl⟩ : syracuseStep 3743831 = 5615747) B5615747
theorem B2769035 : Blo 1845624 2769035 := bstep (se 1 (by rfl) ⟨2076776, by rfl⟩ : syracuseStep 2769035 = 4153553) B4153553
theorem B2769047 : Blo 1845624 2769047 := bstep (se 1 (by rfl) ⟨2076785, by rfl⟩ : syracuseStep 2769047 = 4153571) B4153571
theorem B2769113 : Blo 1845624 2769113 := bstep (se 2 (by rfl) ⟨1038417, by rfl⟩ : syracuseStep 2769113 = 2076835) B2076835
theorem B5259485 : Blo 1845624 5259485 := bstep (se 3 (by rfl) ⟨986153, by rfl⟩ : syracuseStep 5259485 = 1972307) B1972307
theorem B4153625 : Blo 1845624 4153625 := bstep (se 2 (by rfl) ⟨1557609, by rfl⟩ : syracuseStep 4153625 = 3115219) B3115219
theorem B2629913 : Blo 1845624 2629913 := bstep (se 2 (by rfl) ⟨986217, by rfl⟩ : syracuseStep 2629913 = 1972435) B1972435
theorem B3506483 : Blo 1845624 3506483 := bstep (se 1 (by rfl) ⟨2629862, by rfl⟩ : syracuseStep 3506483 = 5259725) B5259725
theorem B2769227 : Blo 1845624 2769227 := bstep (se 1 (by rfl) ⟨2076920, by rfl⟩ : syracuseStep 2769227 = 4153841) B4153841
theorem B8421707 : Blo 1845624 8421707 := bstep (se 1 (by rfl) ⟨6316280, by rfl⟩ : syracuseStep 8421707 = 12632561) B12632561
theorem B8872267 : Blo 1845624 8872267 := bstep (se 1 (by rfl) ⟨6654200, by rfl⟩ : syracuseStep 8872267 = 13308401) B13308401
theorem B2769239 : Blo 1845624 2769239 := bstep (se 1 (by rfl) ⟨2076929, by rfl⟩ : syracuseStep 2769239 = 4153859) B4153859
theorem B6234461 : Blo 1845624 6234461 := bstep (se 3 (by rfl) ⟨1168961, by rfl⟩ : syracuseStep 6234461 = 2337923) B2337923
theorem B4153715 : Blo 1845624 4153715 := bstep (se 1 (by rfl) ⟨3115286, by rfl⟩ : syracuseStep 4153715 = 6230573) B6230573
theorem B2630027 : Blo 1845624 2630027 := bstep (se 1 (by rfl) ⟨1972520, by rfl⟩ : syracuseStep 2630027 = 3945041) B3945041
theorem B4153751 : Blo 1845624 4153751 := bstep (se 1 (by rfl) ⟨3115313, by rfl⟩ : syracuseStep 4153751 = 6230627) B6230627
theorem B2769305 : Blo 1845624 2769305 := bstep (se 2 (by rfl) ⟨1038489, by rfl⟩ : syracuseStep 2769305 = 2076979) B2076979
theorem B5915101 : Blo 1845624 5915101 := bstep (se 3 (by rfl) ⟨1109081, by rfl⟩ : syracuseStep 5915101 = 2218163) B2218163
theorem B2769419 : Blo 1845624 2769419 := bstep (se 1 (by rfl) ⟨2077064, by rfl⟩ : syracuseStep 2769419 = 4154129) B4154129
theorem B2769431 : Blo 1845624 2769431 := bstep (se 1 (by rfl) ⟨2077073, by rfl⟩ : syracuseStep 2769431 = 4154147) B4154147
theorem B22454819 : Blo 1845624 22454819 := bstep (se 1 (by rfl) ⟨16841114, by rfl⟩ : syracuseStep 22454819 = 33682229) B33682229
theorem B10519105 : Blo 1845624 10519105 := bstep (se 2 (by rfl) ⟨3944664, by rfl⟩ : syracuseStep 10519105 = 7889329) B7889329
theorem B4153931 : Blo 1845624 4153931 := bstep (se 1 (by rfl) ⟨3115448, by rfl⟩ : syracuseStep 4153931 = 6230897) B6230897
theorem B2769497 : Blo 1845624 2769497 := bstep (se 2 (by rfl) ⟨1038561, by rfl⟩ : syracuseStep 2769497 = 2077123) B2077123
theorem B7889501 : Blo 1845624 7889501 := bstep (se 3 (by rfl) ⟨1479281, by rfl⟩ : syracuseStep 7889501 = 2958563) B2958563
theorem B16433765 : Blo 1845624 16433765 := bstep (se 4 (by rfl) ⟨1540665, by rfl⟩ : syracuseStep 16433765 = 3081331) B3081331
theorem B4153985 : Blo 1845624 4153985 := bstep (se 2 (by rfl) ⟨1557744, by rfl⟩ : syracuseStep 4153985 = 3115489) B3115489
theorem B2769611 : Blo 1845624 2769611 := bstep (se 1 (by rfl) ⟨2077208, by rfl⟩ : syracuseStep 2769611 = 4154417) B4154417
theorem B2769623 : Blo 1845624 2769623 := bstep (se 1 (by rfl) ⟨2077217, by rfl⟩ : syracuseStep 2769623 = 4154435) B4154435
theorem B4735705 : Blo 1845624 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B5915357 : Blo 1845624 5915357 := bstep (se 3 (by rfl) ⟨1109129, by rfl⟩ : syracuseStep 5915357 = 2218259) B2218259
theorem B2769689 : Blo 1845624 2769689 := bstep (se 2 (by rfl) ⟨1038633, by rfl⟩ : syracuseStep 2769689 = 2077267) B2077267
theorem B3506969 : Blo 1845624 3506969 := bstep (se 2 (by rfl) ⟨1315113, by rfl⟩ : syracuseStep 3506969 = 2630227) B2630227
theorem B9347885 : Blo 1845624 9347885 := bstep (se 3 (by rfl) ⟨1752728, by rfl⟩ : syracuseStep 9347885 = 3505457) B3505457
theorem B4154201 : Blo 1845624 4154201 := bstep (se 2 (by rfl) ⟨1557825, by rfl⟩ : syracuseStep 4154201 = 3115651) B3115651
theorem B2769803 : Blo 1845624 2769803 := bstep (se 1 (by rfl) ⟨2077352, by rfl⟩ : syracuseStep 2769803 = 4154705) B4154705
theorem B6652817 : Blo 1845624 6652817 := bstep (se 2 (by rfl) ⟨2494806, by rfl⟩ : syracuseStep 6652817 = 4989613) B4989613
theorem B2769815 : Blo 1845624 2769815 := bstep (se 1 (by rfl) ⟨2077361, by rfl⟩ : syracuseStep 2769815 = 4154723) B4154723
theorem B2630551 : Blo 1845624 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B4154291 : Blo 1845624 4154291 := bstep (se 1 (by rfl) ⟨3115718, by rfl⟩ : syracuseStep 4154291 = 6231437) B6231437
theorem B4154327 : Blo 1845624 4154327 := bstep (se 1 (by rfl) ⟨3115745, by rfl⟩ : syracuseStep 4154327 = 6231491) B6231491
theorem B2769881 : Blo 1845624 2769881 := bstep (se 2 (by rfl) ⟨1038705, by rfl⟩ : syracuseStep 2769881 = 2077411) B2077411
theorem B7488557 : Blo 1845624 7488557 := bstep (se 3 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 7488557 = 2808209) B2808209
theorem B50521157 : Blo 1845624 50521157 := bstep (se 4 (by rfl) ⟨4736358, by rfl⟩ : syracuseStep 50521157 = 9472717) B9472717
theorem B15770699 : Blo 1845624 15770699 := bstep (se 1 (by rfl) ⟨11828024, by rfl⟩ : syracuseStep 15770699 = 23656049) B23656049
theorem B2769995 : Blo 1845624 2769995 := bstep (se 1 (by rfl) ⟨2077496, by rfl⟩ : syracuseStep 2769995 = 4154993) B4154993
theorem B2770007 : Blo 1845624 2770007 := bstep (se 1 (by rfl) ⟨2077505, by rfl⟩ : syracuseStep 2770007 = 4155011) B4155011
theorem B5612633 : Blo 1845624 5612633 := bstep (se 2 (by rfl) ⟨2104737, by rfl⟩ : syracuseStep 5612633 = 4209475) B4209475
theorem B4154507 : Blo 1845624 4154507 := bstep (se 1 (by rfl) ⟨3115880, by rfl⟩ : syracuseStep 4154507 = 6231761) B6231761
theorem B2770073 : Blo 1845624 2770073 := bstep (se 2 (by rfl) ⟨1038777, by rfl⟩ : syracuseStep 2770073 = 2077555) B2077555
theorem B4154561 : Blo 1845624 4154561 := bstep (se 2 (by rfl) ⟨1557960, by rfl⟩ : syracuseStep 4154561 = 3115921) B3115921
theorem B2770187 : Blo 1845624 2770187 := bstep (se 1 (by rfl) ⟨2077640, by rfl⟩ : syracuseStep 2770187 = 4155281) B4155281
theorem B10511633 : Blo 1845624 10511633 := bstep (se 2 (by rfl) ⟨3941862, by rfl⟩ : syracuseStep 10511633 = 7883725) B7883725
theorem B2770199 : Blo 1845624 2770199 := bstep (se 1 (by rfl) ⟨2077649, by rfl⟩ : syracuseStep 2770199 = 4155299) B4155299
theorem B39912749 : Blo 1845624 39912749 := bstep (se 3 (by rfl) ⟨7483640, by rfl⟩ : syracuseStep 39912749 = 14967281) B14967281
theorem B6743341 : Blo 1845624 6743341 := bstep (se 3 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 6743341 = 2528753) B2528753
theorem B2770265 : Blo 1845624 2770265 := bstep (se 2 (by rfl) ⟨1038849, by rfl⟩ : syracuseStep 2770265 = 2077699) B2077699
theorem B4154777 : Blo 1845624 4154777 := bstep (se 2 (by rfl) ⟨1558041, by rfl⟩ : syracuseStep 4154777 = 3116083) B3116083
theorem B8996275 : Blo 1845624 8996275 := bstep (se 1 (by rfl) ⟨6747206, by rfl⟩ : syracuseStep 8996275 = 13494413) B13494413
theorem B2770379 : Blo 1845624 2770379 := bstep (se 1 (by rfl) ⟨2077784, by rfl⟩ : syracuseStep 2770379 = 4155569) B4155569
theorem B6235595 : Blo 1845624 6235595 := bstep (se 1 (by rfl) ⟨4676696, by rfl⟩ : syracuseStep 6235595 = 9353393) B9353393
theorem B2770391 : Blo 1845624 2770391 := bstep (se 1 (by rfl) ⟨2077793, by rfl⟩ : syracuseStep 2770391 = 4155587) B4155587
theorem B4154867 : Blo 1845624 4154867 := bstep (se 1 (by rfl) ⟨3116150, by rfl⟩ : syracuseStep 4154867 = 6232301) B6232301
theorem B7013891 : Blo 1845624 7013891 := bstep (se 1 (by rfl) ⟨5260418, by rfl⟩ : syracuseStep 7013891 = 10520837) B10520837
theorem B4154903 : Blo 1845624 4154903 := bstep (se 1 (by rfl) ⟨3116177, by rfl⟩ : syracuseStep 4154903 = 6232355) B6232355
theorem B2958871 : Blo 1845624 2958871 := bstep (se 1 (by rfl) ⟨2219153, by rfl⟩ : syracuseStep 2958871 = 4438307) B4438307
theorem B2770457 : Blo 1845624 2770457 := bstep (se 2 (by rfl) ⟨1038921, by rfl⟩ : syracuseStep 2770457 = 2077843) B2077843
theorem B3114571 : Blo 1845624 3114571 := bstep (se 1 (by rfl) ⟨2335928, by rfl⟩ : syracuseStep 3114571 = 4671857) B4671857
theorem B3942017 : Blo 1845624 3942017 := bstep (se 2 (by rfl) ⟨1478256, by rfl⟩ : syracuseStep 3942017 = 2956513) B2956513
theorem B2770571 : Blo 1845624 2770571 := bstep (se 1 (by rfl) ⟨2077928, by rfl⟩ : syracuseStep 2770571 = 4155857) B4155857
theorem B2770583 : Blo 1845624 2770583 := bstep (se 1 (by rfl) ⟨2077937, by rfl⟩ : syracuseStep 2770583 = 4155875) B4155875
theorem B25282199 : Blo 1845624 25282199 := bstep (se 1 (by rfl) ⟨18961649, by rfl⟩ : syracuseStep 25282199 = 37923299) B37923299
theorem B8873651 : Blo 1845624 8873651 := bstep (se 1 (by rfl) ⟨6655238, by rfl⟩ : syracuseStep 8873651 = 13310477) B13310477
theorem B4155083 : Blo 1845624 4155083 := bstep (se 1 (by rfl) ⟨3116312, by rfl⟩ : syracuseStep 4155083 = 6232625) B6232625
theorem B50521805 : Blo 1845624 50521805 := bstep (se 3 (by rfl) ⟨9472838, by rfl⟩ : syracuseStep 50521805 = 18945677) B18945677
theorem B14026445 : Blo 1845624 14026445 := bstep (se 3 (by rfl) ⟨2629958, by rfl⟩ : syracuseStep 14026445 = 5259917) B5259917
theorem B10512089 : Blo 1845624 10512089 := bstep (se 2 (by rfl) ⟨3942033, by rfl⟩ : syracuseStep 10512089 = 7884067) B7884067
theorem B3114713 : Blo 1845624 3114713 := bstep (se 2 (by rfl) ⟨1168017, by rfl⟩ : syracuseStep 3114713 = 2336035) B2336035
theorem B2770649 : Blo 1845624 2770649 := bstep (se 2 (by rfl) ⟨1038993, by rfl⟩ : syracuseStep 2770649 = 2077987) B2077987
theorem B4155137 : Blo 1845624 4155137 := bstep (se 2 (by rfl) ⟨1558176, by rfl⟩ : syracuseStep 4155137 = 3116353) B3116353
theorem B45549377 : Blo 1845624 45549377 := bstep (se 2 (by rfl) ⟨17081016, by rfl⟩ : syracuseStep 45549377 = 34162033) B34162033
theorem B6653771 : Blo 1845624 6653771 := bstep (se 1 (by rfl) ⟨4990328, by rfl⟩ : syracuseStep 6653771 = 9980657) B9980657
theorem B2770763 : Blo 1845624 2770763 := bstep (se 1 (by rfl) ⟨2078072, by rfl⟩ : syracuseStep 2770763 = 4156145) B4156145
theorem B2770775 : Blo 1845624 2770775 := bstep (se 1 (by rfl) ⟨2078081, by rfl⟩ : syracuseStep 2770775 = 4156163) B4156163
theorem B3114841 : Blo 1845624 3114841 := bstep (se 2 (by rfl) ⟨1168065, by rfl⟩ : syracuseStep 3114841 = 2336131) B2336131
theorem B39929699 : Blo 1845624 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B7890833 : Blo 1845624 7890833 := bstep (se 2 (by rfl) ⟨2959062, by rfl⟩ : syracuseStep 7890833 = 5918125) B5918125
theorem B2369431 : Blo 1845624 2369431 := bstep (se 1 (by rfl) ⟨1777073, by rfl⟩ : syracuseStep 2369431 = 3554147) B3554147
theorem B2770841 : Blo 1845624 2770841 := bstep (se 2 (by rfl) ⟨1039065, by rfl⟩ : syracuseStep 2770841 = 2078131) B2078131
theorem B7014347 : Blo 1845624 7014347 := bstep (se 1 (by rfl) ⟨5260760, by rfl⟩ : syracuseStep 7014347 = 10521521) B10521521
theorem B2959319 : Blo 1845624 2959319 := bstep (se 1 (by rfl) ⟨2219489, by rfl⟩ : syracuseStep 2959319 = 4438979) B4438979
theorem B4155353 : Blo 1845624 4155353 := bstep (se 2 (by rfl) ⟨1558257, by rfl⟩ : syracuseStep 4155353 = 3116515) B3116515
theorem B2336779 : Blo 1845624 2336779 := bstep (se 1 (by rfl) ⟨1752584, by rfl⟩ : syracuseStep 2336779 = 3505169) B3505169
theorem B2770955 : Blo 1845624 2770955 := bstep (se 1 (by rfl) ⟨2078216, by rfl⟩ : syracuseStep 2770955 = 4156433) B4156433
theorem B2770967 : Blo 1845624 2770967 := bstep (se 1 (by rfl) ⟨2078225, by rfl⟩ : syracuseStep 2770967 = 4156451) B4156451
theorem B4155443 : Blo 1845624 4155443 := bstep (se 1 (by rfl) ⟨3116582, by rfl⟩ : syracuseStep 4155443 = 6233165) B6233165
theorem B54716485 : Blo 1845624 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B14968907 : Blo 1845624 14968907 := bstep (se 1 (by rfl) ⟨11226680, by rfl⟩ : syracuseStep 14968907 = 22453361) B22453361
theorem B4155479 : Blo 1845624 4155479 := bstep (se 1 (by rfl) ⟨3116609, by rfl⟩ : syracuseStep 4155479 = 6233219) B6233219
theorem B2771033 : Blo 1845624 2771033 := bstep (se 2 (by rfl) ⟨1039137, by rfl⟩ : syracuseStep 2771033 = 2078275) B2078275
theorem B2959499 : Blo 1845624 2959499 := bstep (se 1 (by rfl) ⟨2219624, by rfl⟩ : syracuseStep 2959499 = 4439249) B4439249
theorem B7014545 : Blo 1845624 7014545 := bstep (se 2 (by rfl) ⟨2630454, by rfl⟩ : syracuseStep 7014545 = 5260909) B5260909
theorem B14026931 : Blo 1845624 14026931 := bstep (se 1 (by rfl) ⟨10520198, by rfl⟩ : syracuseStep 14026931 = 21040397) B21040397
theorem B7489739 : Blo 1845624 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B2771147 : Blo 1845624 2771147 := bstep (se 1 (by rfl) ⟨2078360, by rfl⟩ : syracuseStep 2771147 = 4156721) B4156721
theorem B4499659 : Blo 1845624 4499659 := bstep (se 1 (by rfl) ⟨3374744, by rfl⟩ : syracuseStep 4499659 = 6749489) B6749489
theorem B2771159 : Blo 1845624 2771159 := bstep (se 1 (by rfl) ⟨2078369, by rfl⟩ : syracuseStep 2771159 = 4156739) B4156739
theorem B4155659 : Blo 1845624 4155659 := bstep (se 1 (by rfl) ⟨3116744, by rfl⟩ : syracuseStep 4155659 = 6233489) B6233489
theorem B2771225 : Blo 1845624 2771225 := bstep (se 2 (by rfl) ⟨1039209, by rfl⟩ : syracuseStep 2771225 = 2078419) B2078419
theorem B4155713 : Blo 1845624 4155713 := bstep (se 2 (by rfl) ⟨1558392, by rfl⟩ : syracuseStep 4155713 = 3116785) B3116785
theorem B1845643 : Blo 1845624 1845643 := bstep (se 1 (by rfl) ⟨1384232, by rfl⟩ : syracuseStep 1845643 = 2768465) B2768465
theorem B2771339 : Blo 1845624 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B1845655 : Blo 1845624 1845655 := bstep (se 1 (by rfl) ⟨1384241, by rfl⟩ : syracuseStep 1845655 = 2768483) B2768483
theorem B3115415 : Blo 1845624 3115415 := bstep (se 1 (by rfl) ⟨2336561, by rfl⟩ : syracuseStep 3115415 = 4673123) B4673123
theorem B2771351 : Blo 1845624 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B1845675 : Blo 1845624 1845675 := bstep (se 1 (by rfl) ⟨1384256, by rfl⟩ : syracuseStep 1845675 = 2768513) B2768513
theorem B23669171 : Blo 1845624 23669171 := bstep (se 1 (by rfl) ⟨17751878, by rfl⟩ : syracuseStep 23669171 = 35503757) B35503757
theorem B1845687 : Blo 1845624 1845687 := bstep (se 1 (by rfl) ⟨1384265, by rfl⟩ : syracuseStep 1845687 = 2768531) B2768531
theorem B1845707 : Blo 1845624 1845707 := bstep (se 1 (by rfl) ⟨1384280, by rfl⟩ : syracuseStep 1845707 = 2768561) B2768561
theorem B1845719 : Blo 1845624 1845719 := bstep (se 1 (by rfl) ⟨1384289, by rfl⟩ : syracuseStep 1845719 = 2768579) B2768579
theorem B23661017 : Blo 1845624 23661017 := bstep (se 2 (by rfl) ⟨8872881, by rfl⟩ : syracuseStep 23661017 = 17745763) B17745763
theorem B2771417 : Blo 1845624 2771417 := bstep (se 2 (by rfl) ⟨1039281, by rfl⟩ : syracuseStep 2771417 = 2078563) B2078563
theorem B4991453 : Blo 1845624 4991453 := bstep (se 3 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 4991453 = 1871795) B1871795
theorem B1845739 : Blo 1845624 1845739 := bstep (se 1 (by rfl) ⟨1384304, by rfl⟩ : syracuseStep 1845739 = 2768609) B2768609
theorem B4213235 : Blo 1845624 4213235 := bstep (se 1 (by rfl) ⟨3159926, by rfl⟩ : syracuseStep 4213235 = 6319853) B6319853
theorem B1845751 : Blo 1845624 1845751 := bstep (se 1 (by rfl) ⟨1384313, by rfl⟩ : syracuseStep 1845751 = 2768627) B2768627
theorem B1845771 : Blo 1845624 1845771 := bstep (se 1 (by rfl) ⟨1384328, by rfl⟩ : syracuseStep 1845771 = 2768657) B2768657
theorem B1845783 : Blo 1845624 1845783 := bstep (se 1 (by rfl) ⟨1384337, by rfl⟩ : syracuseStep 1845783 = 2768675) B2768675
theorem B3115543 : Blo 1845624 3115543 := bstep (se 1 (by rfl) ⟨2336657, by rfl⟩ : syracuseStep 3115543 = 4673315) B4673315
theorem B4155929 : Blo 1845624 4155929 := bstep (se 2 (by rfl) ⟨1558473, by rfl⟩ : syracuseStep 4155929 = 3116947) B3116947
theorem B1845803 : Blo 1845624 1845803 := bstep (se 1 (by rfl) ⟨1384352, by rfl⟩ : syracuseStep 1845803 = 2768705) B2768705
theorem B1845815 : Blo 1845624 1845815 := bstep (se 1 (by rfl) ⟨1384361, by rfl⟩ : syracuseStep 1845815 = 2768723) B2768723
theorem B1845835 : Blo 1845624 1845835 := bstep (se 1 (by rfl) ⟨1384376, by rfl⟩ : syracuseStep 1845835 = 2768753) B2768753
theorem B1845847 : Blo 1845624 1845847 := bstep (se 1 (by rfl) ⟨1384385, by rfl⟩ : syracuseStep 1845847 = 2768771) B2768771
theorem B1845867 : Blo 1845624 1845867 := bstep (se 1 (by rfl) ⟨1384400, by rfl⟩ : syracuseStep 1845867 = 2768801) B2768801
theorem B4156019 : Blo 1845624 4156019 := bstep (se 1 (by rfl) ⟨3117014, by rfl⟩ : syracuseStep 4156019 = 6234029) B6234029
theorem B1845879 : Blo 1845624 1845879 := bstep (se 1 (by rfl) ⟨1384409, by rfl⟩ : syracuseStep 1845879 = 2768819) B2768819
theorem B1845899 : Blo 1845624 1845899 := bstep (se 1 (by rfl) ⟨1384424, by rfl⟩ : syracuseStep 1845899 = 2768849) B2768849
theorem B4672151 : Blo 1845624 4672151 := bstep (se 1 (by rfl) ⟨3504113, by rfl⟩ : syracuseStep 4672151 = 7008227) B7008227
theorem B1845911 : Blo 1845624 1845911 := bstep (se 1 (by rfl) ⟨1384433, by rfl⟩ : syracuseStep 1845911 = 2768867) B2768867
theorem B4156055 : Blo 1845624 4156055 := bstep (se 1 (by rfl) ⟨3117041, by rfl⟩ : syracuseStep 4156055 = 6234083) B6234083
theorem B1845931 : Blo 1845624 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B1845943 : Blo 1845624 1845943 := bstep (se 1 (by rfl) ⟨1384457, by rfl⟩ : syracuseStep 1845943 = 2768915) B2768915
theorem B1845963 : Blo 1845624 1845963 := bstep (se 1 (by rfl) ⟨1384472, by rfl⟩ : syracuseStep 1845963 = 2768945) B2768945
theorem B3328715 : Blo 1845624 3328715 := bstep (se 1 (by rfl) ⟨2496536, by rfl⟩ : syracuseStep 3328715 = 4993073) B4993073
theorem B1845975 : Blo 1845624 1845975 := bstep (se 1 (by rfl) ⟨1384481, by rfl⟩ : syracuseStep 1845975 = 2768963) B2768963
theorem B3943127 : Blo 1845624 3943127 := bstep (se 1 (by rfl) ⟨2957345, by rfl⟩ : syracuseStep 3943127 = 5914691) B5914691
theorem B11995865 : Blo 1845624 11995865 := bstep (se 2 (by rfl) ⟨4498449, by rfl⟩ : syracuseStep 11995865 = 8996899) B8996899
theorem B1845995 : Blo 1845624 1845995 := bstep (se 1 (by rfl) ⟨1384496, by rfl⟩ : syracuseStep 1845995 = 2768993) B2768993
theorem B1846007 : Blo 1845624 1846007 := bstep (se 1 (by rfl) ⟨1384505, by rfl⟩ : syracuseStep 1846007 = 2769011) B2769011
theorem B1846027 : Blo 1845624 1846027 := bstep (se 1 (by rfl) ⟨1384520, by rfl⟩ : syracuseStep 1846027 = 2769041) B2769041
theorem B1846039 : Blo 1845624 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B1846059 : Blo 1845624 1846059 := bstep (se 1 (by rfl) ⟨1384544, by rfl⟩ : syracuseStep 1846059 = 2769089) B2769089
theorem B1846071 : Blo 1845624 1846071 := bstep (se 1 (by rfl) ⟨1384553, by rfl⟩ : syracuseStep 1846071 = 2769107) B2769107
theorem B1846091 : Blo 1845624 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B4156235 : Blo 1845624 4156235 := bstep (se 1 (by rfl) ⟨3117176, by rfl⟩ : syracuseStep 4156235 = 6234353) B6234353
theorem B1846103 : Blo 1845624 1846103 := bstep (se 1 (by rfl) ⟨1384577, by rfl⟩ : syracuseStep 1846103 = 2769155) B2769155
theorem B1846123 : Blo 1845624 1846123 := bstep (se 1 (by rfl) ⟨1384592, by rfl⟩ : syracuseStep 1846123 = 2769185) B2769185
theorem B1846135 : Blo 1845624 1846135 := bstep (se 1 (by rfl) ⟨1384601, by rfl⟩ : syracuseStep 1846135 = 2769203) B2769203
theorem B4156289 : Blo 1845624 4156289 := bstep (se 2 (by rfl) ⟨1558608, by rfl⟩ : syracuseStep 4156289 = 3117217) B3117217
theorem B1846155 : Blo 1845624 1846155 := bstep (se 1 (by rfl) ⟨1384616, by rfl⟩ : syracuseStep 1846155 = 2769233) B2769233
theorem B1846167 : Blo 1845624 1846167 := bstep (se 1 (by rfl) ⟨1384625, by rfl⟩ : syracuseStep 1846167 = 2769251) B2769251
theorem B1846187 : Blo 1845624 1846187 := bstep (se 1 (by rfl) ⟨1384640, by rfl⟩ : syracuseStep 1846187 = 2769281) B2769281
theorem B1846199 : Blo 1845624 1846199 := bstep (se 1 (by rfl) ⟨1384649, by rfl⟩ : syracuseStep 1846199 = 2769299) B2769299
theorem B1846219 : Blo 1845624 1846219 := bstep (se 1 (by rfl) ⟨1384664, by rfl⟩ : syracuseStep 1846219 = 2769329) B2769329
theorem B6654923 : Blo 1845624 6654923 := bstep (se 1 (by rfl) ⟨4991192, by rfl⟩ : syracuseStep 6654923 = 9982385) B9982385
theorem B1846231 : Blo 1845624 1846231 := bstep (se 1 (by rfl) ⟨1384673, by rfl⟩ : syracuseStep 1846231 = 2769347) B2769347
theorem B2845655 : Blo 1845624 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B2337751 : Blo 1845624 2337751 := bstep (se 1 (by rfl) ⟨1753313, by rfl⟩ : syracuseStep 2337751 = 3506627) B3506627
theorem B1846251 : Blo 1845624 1846251 := bstep (se 1 (by rfl) ⟨1384688, by rfl⟩ : syracuseStep 1846251 = 2769377) B2769377
theorem B1846263 : Blo 1845624 1846263 := bstep (se 1 (by rfl) ⟨1384697, by rfl⟩ : syracuseStep 1846263 = 2769395) B2769395
theorem B1846283 : Blo 1845624 1846283 := bstep (se 1 (by rfl) ⟨1384712, by rfl⟩ : syracuseStep 1846283 = 2769425) B2769425
theorem B1846295 : Blo 1845624 1846295 := bstep (se 1 (by rfl) ⟨1384721, by rfl⟩ : syracuseStep 1846295 = 2769443) B2769443
theorem B1846315 : Blo 1845624 1846315 := bstep (se 1 (by rfl) ⟨1384736, by rfl⟩ : syracuseStep 1846315 = 2769473) B2769473
theorem B1846327 : Blo 1845624 1846327 := bstep (se 1 (by rfl) ⟨1384745, by rfl⟩ : syracuseStep 1846327 = 2769491) B2769491
theorem B1846347 : Blo 1845624 1846347 := bstep (se 1 (by rfl) ⟨1384760, by rfl⟩ : syracuseStep 1846347 = 2769521) B2769521
theorem B5614667 : Blo 1845624 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B1846359 : Blo 1845624 1846359 := bstep (se 1 (by rfl) ⟨1384769, by rfl⟩ : syracuseStep 1846359 = 2769539) B2769539
theorem B4156505 : Blo 1845624 4156505 := bstep (se 2 (by rfl) ⟨1558689, by rfl⟩ : syracuseStep 4156505 = 3117379) B3117379
theorem B1846379 : Blo 1845624 1846379 := bstep (se 1 (by rfl) ⟨1384784, by rfl⟩ : syracuseStep 1846379 = 2769569) B2769569
theorem B1846391 : Blo 1845624 1846391 := bstep (se 1 (by rfl) ⟨1384793, by rfl⟩ : syracuseStep 1846391 = 2769587) B2769587
theorem B7892099 : Blo 1845624 7892099 := bstep (se 1 (by rfl) ⟨5919074, by rfl⟩ : syracuseStep 7892099 = 11838149) B11838149
theorem B1846411 : Blo 1845624 1846411 := bstep (se 1 (by rfl) ⟨1384808, by rfl⟩ : syracuseStep 1846411 = 2769617) B2769617
theorem B3116171 : Blo 1845624 3116171 := bstep (se 1 (by rfl) ⟨2337128, by rfl⟩ : syracuseStep 3116171 = 4674257) B4674257
theorem B1846423 : Blo 1845624 1846423 := bstep (se 1 (by rfl) ⟨1384817, by rfl⟩ : syracuseStep 1846423 = 2769635) B2769635
theorem B1846443 : Blo 1845624 1846443 := bstep (se 1 (by rfl) ⟨1384832, by rfl⟩ : syracuseStep 1846443 = 2769665) B2769665
theorem B4156595 : Blo 1845624 4156595 := bstep (se 1 (by rfl) ⟨3117446, by rfl⟩ : syracuseStep 4156595 = 6234893) B6234893
theorem B1846455 : Blo 1845624 1846455 := bstep (se 1 (by rfl) ⟨1384841, by rfl⟩ : syracuseStep 1846455 = 2769683) B2769683
theorem B1846475 : Blo 1845624 1846475 := bstep (se 1 (by rfl) ⟨1384856, by rfl⟩ : syracuseStep 1846475 = 2769713) B2769713
theorem B1846487 : Blo 1845624 1846487 := bstep (se 1 (by rfl) ⟨1384865, by rfl⟩ : syracuseStep 1846487 = 2769731) B2769731
theorem B4156631 : Blo 1845624 4156631 := bstep (se 1 (by rfl) ⟨3117473, by rfl⟩ : syracuseStep 4156631 = 6234947) B6234947
theorem B1846507 : Blo 1845624 1846507 := bstep (se 1 (by rfl) ⟨1384880, by rfl⟩ : syracuseStep 1846507 = 2769761) B2769761
theorem B1846519 : Blo 1845624 1846519 := bstep (se 1 (by rfl) ⟨1384889, by rfl⟩ : syracuseStep 1846519 = 2769779) B2769779
theorem B255823109 : Blo 1845624 255823109 := bstep (se 4 (by rfl) ⟨23983416, by rfl⟩ : syracuseStep 255823109 = 47966833) B47966833
theorem B1846539 : Blo 1845624 1846539 := bstep (se 1 (by rfl) ⟨1384904, by rfl⟩ : syracuseStep 1846539 = 2769809) B2769809
theorem B3116299 : Blo 1845624 3116299 := bstep (se 1 (by rfl) ⟨2337224, by rfl⟩ : syracuseStep 3116299 = 4674449) B4674449
theorem B1846551 : Blo 1845624 1846551 := bstep (se 1 (by rfl) ⟨1384913, by rfl⟩ : syracuseStep 1846551 = 2769827) B2769827
theorem B1846571 : Blo 1845624 1846571 := bstep (se 1 (by rfl) ⟨1384928, by rfl⟩ : syracuseStep 1846571 = 2769857) B2769857
theorem B1846583 : Blo 1845624 1846583 := bstep (se 1 (by rfl) ⟨1384937, by rfl⟩ : syracuseStep 1846583 = 2769875) B2769875
theorem B11226433 : Blo 1845624 11226433 := bstep (se 2 (by rfl) ⟨4209912, by rfl⟩ : syracuseStep 11226433 = 8419825) B8419825
theorem B1846603 : Blo 1845624 1846603 := bstep (se 1 (by rfl) ⟨1384952, by rfl⟩ : syracuseStep 1846603 = 2769905) B2769905
theorem B1846615 : Blo 1845624 1846615 := bstep (se 1 (by rfl) ⟨1384961, by rfl⟩ : syracuseStep 1846615 = 2769923) B2769923
theorem B1846635 : Blo 1845624 1846635 := bstep (se 1 (by rfl) ⟨1384976, by rfl⟩ : syracuseStep 1846635 = 2769953) B2769953
theorem B1846647 : Blo 1845624 1846647 := bstep (se 1 (by rfl) ⟨1384985, by rfl⟩ : syracuseStep 1846647 = 2769971) B2769971
theorem B1846667 : Blo 1845624 1846667 := bstep (se 1 (by rfl) ⟨1385000, by rfl⟩ : syracuseStep 1846667 = 2770001) B2770001
theorem B4156811 : Blo 1845624 4156811 := bstep (se 1 (by rfl) ⟨3117608, by rfl⟩ : syracuseStep 4156811 = 6235217) B6235217
theorem B1846679 : Blo 1845624 1846679 := bstep (se 1 (by rfl) ⟨1385009, by rfl⟩ : syracuseStep 1846679 = 2770019) B2770019
theorem B3116441 : Blo 1845624 3116441 := bstep (se 2 (by rfl) ⟨1168665, by rfl⟩ : syracuseStep 3116441 = 2337331) B2337331
theorem B1846699 : Blo 1845624 1846699 := bstep (se 1 (by rfl) ⟨1385024, by rfl⟩ : syracuseStep 1846699 = 2770049) B2770049
theorem B1846711 : Blo 1845624 1846711 := bstep (se 1 (by rfl) ⟨1385033, by rfl⟩ : syracuseStep 1846711 = 2770067) B2770067
theorem B4672961 : Blo 1845624 4672961 := bstep (se 2 (by rfl) ⟨1752360, by rfl⟩ : syracuseStep 4672961 = 3504721) B3504721
theorem B4156865 : Blo 1845624 4156865 := bstep (se 2 (by rfl) ⟨1558824, by rfl⟩ : syracuseStep 4156865 = 3117649) B3117649
theorem B4435403 : Blo 1845624 4435403 := bstep (se 1 (by rfl) ⟨3326552, by rfl⟩ : syracuseStep 4435403 = 6653105) B6653105
theorem B1846731 : Blo 1845624 1846731 := bstep (se 1 (by rfl) ⟨1385048, by rfl⟩ : syracuseStep 1846731 = 2770097) B2770097
theorem B1846743 : Blo 1845624 1846743 := bstep (se 1 (by rfl) ⟨1385057, by rfl⟩ : syracuseStep 1846743 = 2770115) B2770115
theorem B1846763 : Blo 1845624 1846763 := bstep (se 1 (by rfl) ⟨1385072, by rfl⟩ : syracuseStep 1846763 = 2770145) B2770145
theorem B1846775 : Blo 1845624 1846775 := bstep (se 1 (by rfl) ⟨1385081, by rfl⟩ : syracuseStep 1846775 = 2770163) B2770163
theorem B1846795 : Blo 1845624 1846795 := bstep (se 1 (by rfl) ⟨1385096, by rfl⟩ : syracuseStep 1846795 = 2770193) B2770193
theorem B1846807 : Blo 1845624 1846807 := bstep (se 1 (by rfl) ⟨1385105, by rfl⟩ : syracuseStep 1846807 = 2770211) B2770211
theorem B3116569 : Blo 1845624 3116569 := bstep (se 2 (by rfl) ⟨1168713, by rfl⟩ : syracuseStep 3116569 = 2337427) B2337427
theorem B1846827 : Blo 1845624 1846827 := bstep (se 1 (by rfl) ⟨1385120, by rfl⟩ : syracuseStep 1846827 = 2770241) B2770241
theorem B1846839 : Blo 1845624 1846839 := bstep (se 1 (by rfl) ⟨1385129, by rfl⟩ : syracuseStep 1846839 = 2770259) B2770259
theorem B1846859 : Blo 1845624 1846859 := bstep (se 1 (by rfl) ⟨1385144, by rfl⟩ : syracuseStep 1846859 = 2770289) B2770289
theorem B1846871 : Blo 1845624 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B14028389 : Blo 1845624 14028389 := bstep (se 4 (by rfl) ⟨1315161, by rfl⟩ : syracuseStep 14028389 = 2630323) B2630323
theorem B1846891 : Blo 1845624 1846891 := bstep (se 1 (by rfl) ⟨1385168, by rfl⟩ : syracuseStep 1846891 = 2770337) B2770337
theorem B1846903 : Blo 1845624 1846903 := bstep (se 1 (by rfl) ⟨1385177, by rfl⟩ : syracuseStep 1846903 = 2770355) B2770355
theorem B1846923 : Blo 1845624 1846923 := bstep (se 1 (by rfl) ⟨1385192, by rfl⟩ : syracuseStep 1846923 = 2770385) B2770385
theorem B6229655 : Blo 1845624 6229655 := bstep (se 1 (by rfl) ⟨4672241, by rfl⟩ : syracuseStep 6229655 = 9344483) B9344483
theorem B1846935 : Blo 1845624 1846935 := bstep (se 1 (by rfl) ⟨1385201, by rfl⟩ : syracuseStep 1846935 = 2770403) B2770403
theorem B4157081 : Blo 1845624 4157081 := bstep (se 2 (by rfl) ⟨1558905, by rfl⟩ : syracuseStep 4157081 = 3117811) B3117811
theorem B2076331 : Blo 1845624 2076331 := bstep (se 1 (by rfl) ⟨1557248, by rfl⟩ : syracuseStep 2076331 = 3114497) B3114497
theorem B1846955 : Blo 1845624 1846955 := bstep (se 1 (by rfl) ⟨1385216, by rfl⟩ : syracuseStep 1846955 = 2770433) B2770433
theorem B1846967 : Blo 1845624 1846967 := bstep (se 1 (by rfl) ⟨1385225, by rfl⟩ : syracuseStep 1846967 = 2770451) B2770451
theorem B1846987 : Blo 1845624 1846987 := bstep (se 1 (by rfl) ⟨1385240, by rfl⟩ : syracuseStep 1846987 = 2770481) B2770481
theorem B1846999 : Blo 1845624 1846999 := bstep (se 1 (by rfl) ⟨1385249, by rfl⟩ : syracuseStep 1846999 = 2770499) B2770499
theorem B3944153 : Blo 1845624 3944153 := bstep (se 2 (by rfl) ⟨1479057, by rfl⟩ : syracuseStep 3944153 = 2958115) B2958115
theorem B1847019 : Blo 1845624 1847019 := bstep (se 1 (by rfl) ⟨1385264, by rfl⟩ : syracuseStep 1847019 = 2770529) B2770529
theorem B1847031 : Blo 1845624 1847031 := bstep (se 1 (by rfl) ⟨1385273, by rfl⟩ : syracuseStep 1847031 = 2770547) B2770547
theorem B1847051 : Blo 1845624 1847051 := bstep (se 1 (by rfl) ⟨1385288, by rfl⟩ : syracuseStep 1847051 = 2770577) B2770577
theorem B2076439 : Blo 1845624 2076439 := bstep (se 1 (by rfl) ⟨1557329, by rfl⟩ : syracuseStep 2076439 = 3114659) B3114659
theorem B1847063 : Blo 1845624 1847063 := bstep (se 1 (by rfl) ⟨1385297, by rfl⟩ : syracuseStep 1847063 = 2770595) B2770595
theorem B1847083 : Blo 1845624 1847083 := bstep (se 1 (by rfl) ⟨1385312, by rfl⟩ : syracuseStep 1847083 = 2770625) B2770625
theorem B19967789 : Blo 1845624 19967789 := bstep (se 3 (by rfl) ⟨3743960, by rfl⟩ : syracuseStep 19967789 = 7487921) B7487921
theorem B1847095 : Blo 1845624 1847095 := bstep (se 1 (by rfl) ⟨1385321, by rfl⟩ : syracuseStep 1847095 = 2770643) B2770643
theorem B1847115 : Blo 1845624 1847115 := bstep (se 1 (by rfl) ⟨1385336, by rfl⟩ : syracuseStep 1847115 = 2770673) B2770673
theorem B1847127 : Blo 1845624 1847127 := bstep (se 1 (by rfl) ⟨1385345, by rfl⟩ : syracuseStep 1847127 = 2770691) B2770691
theorem B1847147 : Blo 1845624 1847147 := bstep (se 1 (by rfl) ⟨1385360, by rfl⟩ : syracuseStep 1847147 = 2770721) B2770721
theorem B1847159 : Blo 1845624 1847159 := bstep (se 1 (by rfl) ⟨1385369, by rfl⟩ : syracuseStep 1847159 = 2770739) B2770739
theorem B1847179 : Blo 1845624 1847179 := bstep (se 1 (by rfl) ⟨1385384, by rfl⟩ : syracuseStep 1847179 = 2770769) B2770769
theorem B1847191 : Blo 1845624 1847191 := bstep (se 1 (by rfl) ⟨1385393, by rfl⟩ : syracuseStep 1847191 = 2770787) B2770787
theorem B1847211 : Blo 1845624 1847211 := bstep (se 1 (by rfl) ⟨1385408, by rfl⟩ : syracuseStep 1847211 = 2770817) B2770817
theorem B79826867 : Blo 1845624 79826867 := bstep (se 1 (by rfl) ⟨59870150, by rfl⟩ : syracuseStep 79826867 = 119740301) B119740301
theorem B1847223 : Blo 1845624 1847223 := bstep (se 1 (by rfl) ⟨1385417, by rfl⟩ : syracuseStep 1847223 = 2770835) B2770835
theorem B10522547 : Blo 1845624 10522547 := bstep (se 1 (by rfl) ⟨7891910, by rfl⟩ : syracuseStep 10522547 = 15783821) B15783821
theorem B2076619 : Blo 1845624 2076619 := bstep (se 1 (by rfl) ⟨1557464, by rfl⟩ : syracuseStep 2076619 = 3114929) B3114929
theorem B1847243 : Blo 1845624 1847243 := bstep (se 1 (by rfl) ⟨1385432, by rfl⟩ : syracuseStep 1847243 = 2770865) B2770865
theorem B1847255 : Blo 1845624 1847255 := bstep (se 1 (by rfl) ⟨1385441, by rfl⟩ : syracuseStep 1847255 = 2770883) B2770883
theorem B4673497 : Blo 1845624 4673497 := bstep (se 2 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 4673497 = 3505123) B3505123
theorem B1847275 : Blo 1845624 1847275 := bstep (se 1 (by rfl) ⟨1385456, by rfl⟩ : syracuseStep 1847275 = 2770913) B2770913
theorem B1847287 : Blo 1845624 1847287 := bstep (se 1 (by rfl) ⟨1385465, by rfl⟩ : syracuseStep 1847287 = 2770931) B2770931
theorem B7884803 : Blo 1845624 7884803 := bstep (se 1 (by rfl) ⟨5913602, by rfl⟩ : syracuseStep 7884803 = 11827205) B11827205
theorem B14020613 : Blo 1845624 14020613 := bstep (se 4 (by rfl) ⟨1314432, by rfl⟩ : syracuseStep 14020613 = 2628865) B2628865
theorem B1847307 : Blo 1845624 1847307 := bstep (se 1 (by rfl) ⟨1385480, by rfl⟩ : syracuseStep 1847307 = 2770961) B2770961
theorem B1847319 : Blo 1845624 1847319 := bstep (se 1 (by rfl) ⟨1385489, by rfl⟩ : syracuseStep 1847319 = 2770979) B2770979
theorem B1847339 : Blo 1845624 1847339 := bstep (se 1 (by rfl) ⟨1385504, by rfl⟩ : syracuseStep 1847339 = 2771009) B2771009
theorem B2076727 : Blo 1845624 2076727 := bstep (se 1 (by rfl) ⟨1557545, by rfl⟩ : syracuseStep 2076727 = 3115091) B3115091
theorem B1847351 : Blo 1845624 1847351 := bstep (se 1 (by rfl) ⟨1385513, by rfl⟩ : syracuseStep 1847351 = 2771027) B2771027
theorem B1847371 : Blo 1845624 1847371 := bstep (se 1 (by rfl) ⟨1385528, by rfl⟩ : syracuseStep 1847371 = 2771057) B2771057
theorem B14028875 : Blo 1845624 14028875 := bstep (se 1 (by rfl) ⟨10521656, by rfl⟩ : syracuseStep 14028875 = 21043313) B21043313
theorem B3117143 : Blo 1845624 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B1847383 : Blo 1845624 1847383 := bstep (se 1 (by rfl) ⟨1385537, by rfl⟩ : syracuseStep 1847383 = 2771075) B2771075
theorem B1847403 : Blo 1845624 1847403 := bstep (se 1 (by rfl) ⟨1385552, by rfl⟩ : syracuseStep 1847403 = 2771105) B2771105
theorem B1847415 : Blo 1845624 1847415 := bstep (se 1 (by rfl) ⟨1385561, by rfl⟩ : syracuseStep 1847415 = 2771123) B2771123
theorem B1847435 : Blo 1845624 1847435 := bstep (se 1 (by rfl) ⟨1385576, by rfl⟩ : syracuseStep 1847435 = 2771153) B2771153
theorem B88871053 : Blo 1845624 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B1847447 : Blo 1845624 1847447 := bstep (se 1 (by rfl) ⟨1385585, by rfl⟩ : syracuseStep 1847447 = 2771171) B2771171
theorem B1847467 : Blo 1845624 1847467 := bstep (se 1 (by rfl) ⟨1385600, by rfl⟩ : syracuseStep 1847467 = 2771201) B2771201
theorem B6230195 : Blo 1845624 6230195 := bstep (se 1 (by rfl) ⟨4672646, by rfl⟩ : syracuseStep 6230195 = 9345293) B9345293
theorem B1847479 : Blo 1845624 1847479 := bstep (se 1 (by rfl) ⟨1385609, by rfl⟩ : syracuseStep 1847479 = 2771219) B2771219
theorem B1847499 : Blo 1845624 1847499 := bstep (se 1 (by rfl) ⟨1385624, by rfl⟩ : syracuseStep 1847499 = 2771249) B2771249
theorem B3117271 : Blo 1845624 3117271 := bstep (se 1 (by rfl) ⟨2337953, by rfl⟩ : syracuseStep 3117271 = 4675907) B4675907
theorem B8876249 : Blo 1845624 8876249 := bstep (se 2 (by rfl) ⟨3328593, by rfl⟩ : syracuseStep 8876249 = 6657187) B6657187
theorem B1847511 : Blo 1845624 1847511 := bstep (se 1 (by rfl) ⟨1385633, by rfl⟩ : syracuseStep 1847511 = 2771267) B2771267
theorem B2076907 : Blo 1845624 2076907 := bstep (se 1 (by rfl) ⟨1557680, by rfl⟩ : syracuseStep 2076907 = 3115361) B3115361
theorem B1847531 : Blo 1845624 1847531 := bstep (se 1 (by rfl) ⟨1385648, by rfl⟩ : syracuseStep 1847531 = 2771297) B2771297
theorem B1847543 : Blo 1845624 1847543 := bstep (se 1 (by rfl) ⟨1385657, by rfl⟩ : syracuseStep 1847543 = 2771315) B2771315
theorem B7008515 : Blo 1845624 7008515 := bstep (se 1 (by rfl) ⟨5256386, by rfl⟩ : syracuseStep 7008515 = 10512773) B10512773
theorem B1847563 : Blo 1845624 1847563 := bstep (se 1 (by rfl) ⟨1385672, by rfl⟩ : syracuseStep 1847563 = 2771345) B2771345
theorem B1847575 : Blo 1845624 1847575 := bstep (se 1 (by rfl) ⟨1385681, by rfl⟩ : syracuseStep 1847575 = 2771363) B2771363
theorem B1847595 : Blo 1845624 1847595 := bstep (se 1 (by rfl) ⟨1385696, by rfl⟩ : syracuseStep 1847595 = 2771393) B2771393
theorem B60739885 : Blo 1845624 60739885 := bstep (se 3 (by rfl) ⟨11388728, by rfl⟩ : syracuseStep 60739885 = 22777457) B22777457
theorem B1847607 : Blo 1845624 1847607 := bstep (se 1 (by rfl) ⟨1385705, by rfl⟩ : syracuseStep 1847607 = 2771411) B2771411
theorem B2077015 : Blo 1845624 2077015 := bstep (se 1 (by rfl) ⟨1557761, by rfl⟩ : syracuseStep 2077015 = 3115523) B3115523
theorem B19960181 : Blo 1845624 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B6230465 : Blo 1845624 6230465 := bstep (se 2 (by rfl) ⟨2336424, by rfl⟩ : syracuseStep 6230465 = 4672849) B4672849
theorem B2077195 : Blo 1845624 2077195 := bstep (se 1 (by rfl) ⟨1557896, by rfl⟩ : syracuseStep 2077195 = 3115793) B3115793
theorem B29938193 : Blo 1845624 29938193 := bstep (se 2 (by rfl) ⟨11226822, by rfl⟩ : syracuseStep 29938193 = 22453645) B22453645
theorem B9351773 : Blo 1845624 9351773 := bstep (se 3 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 9351773 = 3506915) B3506915
theorem B2077303 : Blo 1845624 2077303 := bstep (se 1 (by rfl) ⟨1557977, by rfl⟩ : syracuseStep 2077303 = 3115955) B3115955
theorem B10957463 : Blo 1845624 10957463 := bstep (se 1 (by rfl) ⟨8218097, by rfl⟩ : syracuseStep 10957463 = 16436195) B16436195
theorem B2077483 : Blo 1845624 2077483 := bstep (se 1 (by rfl) ⟨1558112, by rfl⟩ : syracuseStep 2077483 = 3116225) B3116225
theorem B2077591 : Blo 1845624 2077591 := bstep (se 1 (by rfl) ⟨1558193, by rfl⟩ : syracuseStep 2077591 = 3116387) B3116387
theorem B6231005 : Blo 1845624 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B4674611 : Blo 1845624 4674611 := bstep (se 1 (by rfl) ⟨3505958, by rfl⟩ : syracuseStep 4674611 = 7011917) B7011917
theorem B2077771 : Blo 1845624 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B5330009 : Blo 1845624 5330009 := bstep (se 2 (by rfl) ⟨1998753, by rfl⟩ : syracuseStep 5330009 = 3997507) B3997507
theorem B2077879 : Blo 1845624 2077879 := bstep (se 1 (by rfl) ⟨1558409, by rfl⟩ : syracuseStep 2077879 = 3116819) B3116819
theorem B5256409 : Blo 1845624 5256409 := bstep (se 2 (by rfl) ⟨1971153, by rfl⟩ : syracuseStep 5256409 = 3942307) B3942307
theorem B23655685 : Blo 1845624 23655685 := bstep (se 4 (by rfl) ⟨2217720, by rfl⟩ : syracuseStep 23655685 = 4435441) B4435441
theorem B9344321 : Blo 1845624 9344321 := bstep (se 2 (by rfl) ⟨3504120, by rfl⟩ : syracuseStep 9344321 = 7008241) B7008241
theorem B3945793 : Blo 1845624 3945793 := bstep (se 2 (by rfl) ⟨1479672, by rfl⟩ : syracuseStep 3945793 = 2959345) B2959345
theorem B4674905 : Blo 1845624 4674905 := bstep (se 2 (by rfl) ⟨1753089, by rfl⟩ : syracuseStep 4674905 = 3506179) B3506179
theorem B2078059 : Blo 1845624 2078059 := bstep (se 1 (by rfl) ⟨1558544, by rfl⟩ : syracuseStep 2078059 = 3117089) B3117089
theorem B2078167 : Blo 1845624 2078167 := bstep (se 1 (by rfl) ⟨1558625, by rfl⟩ : syracuseStep 2078167 = 3117251) B3117251
theorem B13489739 : Blo 1845624 13489739 := bstep (se 1 (by rfl) ⟨10117304, by rfl⟩ : syracuseStep 13489739 = 20234609) B20234609
theorem B2078347 : Blo 1845624 2078347 := bstep (se 1 (by rfl) ⟨1558760, by rfl⟩ : syracuseStep 2078347 = 3117521) B3117521
theorem B2078455 : Blo 1845624 2078455 := bstep (se 1 (by rfl) ⟨1558841, by rfl⟩ : syracuseStep 2078455 = 3117683) B3117683
theorem B5257025 : Blo 1845624 5257025 := bstep (se 2 (by rfl) ⟨1971384, by rfl⟩ : syracuseStep 5257025 = 3942769) B3942769
theorem B25966453 : Blo 1845624 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B3504151 : Blo 1845624 3504151 := bstep (se 1 (by rfl) ⟨2628113, by rfl⟩ : syracuseStep 3504151 = 5256227) B5256227
theorem B7993367 : Blo 1845624 7993367 := bstep (se 1 (by rfl) ⟨5995025, by rfl⟩ : syracuseStep 7993367 = 11990051) B11990051
theorem B1972247 : Blo 1845624 1972247 := bstep (se 1 (by rfl) ⟨1479185, by rfl⟩ : syracuseStep 1972247 = 2958371) B2958371
theorem B6232139 : Blo 1845624 6232139 := bstep (se 1 (by rfl) ⟨4674104, by rfl⟩ : syracuseStep 6232139 = 9348209) B9348209
theorem B2807947 : Blo 1845624 2807947 := bstep (se 1 (by rfl) ⟨2105960, by rfl⟩ : syracuseStep 2807947 = 4211921) B4211921
theorem B7887041 : Blo 1845624 7887041 := bstep (se 2 (by rfl) ⟨2957640, by rfl⟩ : syracuseStep 7887041 = 5915281) B5915281
theorem B2496791 : Blo 1845624 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B6232409 : Blo 1845624 6232409 := bstep (se 2 (by rfl) ⟨2337153, by rfl⟩ : syracuseStep 6232409 = 4674307) B4674307
theorem B14023043 : Blo 1845624 14023043 := bstep (se 1 (by rfl) ⟨10517282, by rfl⟩ : syracuseStep 14023043 = 21034565) B21034565
theorem B12630593 : Blo 1845624 12630593 := bstep (se 2 (by rfl) ⟨4736472, by rfl⟩ : syracuseStep 12630593 = 9472945) B9472945
theorem B14015267 : Blo 1845624 14015267 := bstep (se 1 (by rfl) ⟨10511450, by rfl⟩ : syracuseStep 14015267 = 21022901) B21022901
theorem B3504971 : Blo 1845624 3504971 := bstep (se 1 (by rfl) ⟨2628728, by rfl⟩ : syracuseStep 3504971 = 5257457) B5257457
theorem B6749021 : Blo 1845624 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B3505025 : Blo 1845624 3505025 := bstep (se 2 (by rfl) ⟨1314384, by rfl⟩ : syracuseStep 3505025 = 2628769) B2628769
theorem B3742615 : Blo 1845624 3742615 := bstep (se 1 (by rfl) ⟨2806961, by rfl⟩ : syracuseStep 3742615 = 5613923) B5613923
theorem B4676555 : Blo 1845624 4676555 := bstep (se 1 (by rfl) ⟨3507416, by rfl⟩ : syracuseStep 4676555 = 7014833) B7014833
theorem B2628569 : Blo 1845624 2628569 := bstep (se 2 (by rfl) ⟨985713, by rfl⟩ : syracuseStep 2628569 = 1971427) B1971427
theorem B10517465 : Blo 1845624 10517465 := bstep (se 2 (by rfl) ⟨3944049, by rfl⟩ : syracuseStep 10517465 = 7888099) B7888099
theorem B2808793 : Blo 1845624 2808793 := bstep (se 2 (by rfl) ⟨1053297, by rfl⟩ : syracuseStep 2808793 = 2106595) B2106595
theorem B7486481 : Blo 1845624 7486481 := bstep (se 2 (by rfl) ⟨2807430, by rfl⟩ : syracuseStep 7486481 = 5614861) B5614861
theorem B6233111 : Blo 1845624 6233111 := bstep (se 1 (by rfl) ⟨4674833, by rfl⟩ : syracuseStep 6233111 = 9349667) B9349667
theorem B14973997 : Blo 1845624 14973997 := bstep (se 3 (by rfl) ⟨2807624, by rfl⟩ : syracuseStep 14973997 = 5615249) B5615249
theorem B3996823 : Blo 1845624 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B9346265 : Blo 1845624 9346265 := bstep (se 2 (by rfl) ⟨3504849, by rfl⟩ : syracuseStep 9346265 = 7009699) B7009699
theorem B7011629 : Blo 1845624 7011629 := bstep (se 3 (by rfl) ⟨1314680, by rfl⟩ : syracuseStep 7011629 = 2629361) B2629361
theorem B4152779 : Blo 1845624 4152779 := bstep (se 1 (by rfl) ⟨3114584, by rfl⟩ : syracuseStep 4152779 = 6229169) B6229169
theorem B4152833 : Blo 1845624 4152833 := bstep (se 2 (by rfl) ⟨1557312, by rfl⟩ : syracuseStep 4152833 = 3114625) B3114625
theorem B3374615 : Blo 1845624 3374615 := bstep (se 1 (by rfl) ⟨2530961, by rfl⟩ : syracuseStep 3374615 = 5061923) B5061923
theorem B21044771 : Blo 1845624 21044771 := bstep (se 1 (by rfl) ⟨15783578, by rfl⟩ : syracuseStep 21044771 = 31567157) B31567157
theorem B6233651 : Blo 1845624 6233651 := bstep (se 1 (by rfl) ⟨4675238, by rfl⟩ : syracuseStep 6233651 = 9350477) B9350477
theorem B2768459 : Blo 1845624 2768459 := bstep (se 1 (by rfl) ⟨2076344, by rfl⟩ : syracuseStep 2768459 = 4152689) B4152689
theorem B2768471 : Blo 1845624 2768471 := bstep (se 1 (by rfl) ⟨2076353, by rfl⟩ : syracuseStep 2768471 = 4152707) B4152707
theorem B2629207 : Blo 1845624 2629207 := bstep (se 1 (by rfl) ⟨1971905, by rfl⟩ : syracuseStep 2629207 = 3943811) B3943811
theorem B3743347 : Blo 1845624 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B2768537 : Blo 1845624 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B4800179 : Blo 1845624 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B4153049 : Blo 1845624 4153049 := bstep (se 2 (by rfl) ⟨1557393, by rfl⟩ : syracuseStep 4153049 = 3114787) B3114787
theorem B2768651 : Blo 1845624 2768651 := bstep (se 1 (by rfl) ⟨2076488, by rfl⟩ : syracuseStep 2768651 = 4152977) B4152977
theorem B2768663 : Blo 1845624 2768663 := bstep (se 1 (by rfl) ⟨2076497, by rfl⟩ : syracuseStep 2768663 = 4152995) B4152995
theorem B3505943 : Blo 1845624 3505943 := bstep (se 1 (by rfl) ⟨2629457, by rfl⟩ : syracuseStep 3505943 = 5258915) B5258915
theorem B4153139 : Blo 1845624 4153139 := bstep (se 1 (by rfl) ⟨3114854, by rfl⟩ : syracuseStep 4153139 = 6229709) B6229709
theorem B4497203 : Blo 1845624 4497203 := bstep (se 1 (by rfl) ⟨3372902, by rfl⟩ : syracuseStep 4497203 = 6745805) B6745805
theorem B6233921 : Blo 1845624 6233921 := bstep (se 2 (by rfl) ⟨2337720, by rfl⟩ : syracuseStep 6233921 = 4675441) B4675441
theorem B7888715 : Blo 1845624 7888715 := bstep (se 1 (by rfl) ⟨5916536, by rfl⟩ : syracuseStep 7888715 = 11833073) B11833073
theorem B4153175 : Blo 1845624 4153175 := bstep (se 1 (by rfl) ⟨3114881, by rfl⟩ : syracuseStep 4153175 = 6229763) B6229763
theorem B2768729 : Blo 1845624 2768729 := bstep (se 2 (by rfl) ⟨1038273, by rfl⟩ : syracuseStep 2768729 = 2076547) B2076547
theorem B5259097 : Blo 1845624 5259097 := bstep (se 2 (by rfl) ⟨1972161, by rfl⟩ : syracuseStep 5259097 = 3944323) B3944323
theorem B1851319 : Blo 1845624 1851319 := bstep (se 1 (by rfl) ⟨1388489, by rfl⟩ : syracuseStep 1851319 = 2776979) B2776979
theorem B2768843 : Blo 1845624 2768843 := bstep (se 1 (by rfl) ⟨2076632, by rfl⟩ : syracuseStep 2768843 = 4153265) B4153265
theorem B2768855 : Blo 1845624 2768855 := bstep (se 1 (by rfl) ⟨2076641, by rfl⟩ : syracuseStep 2768855 = 4153283) B4153283
theorem B9347075 : Blo 1845624 9347075 := bstep (se 1 (by rfl) ⟨7010306, by rfl⟩ : syracuseStep 9347075 = 14020613) B14020613
theorem B2768903 : Blo 1845624 2768903 := bstep (se 1 (by rfl) ⟨2076677, by rfl⟩ : syracuseStep 2768903 = 4153355) B4153355
theorem B2768939 : Blo 1845624 2768939 := bstep (se 1 (by rfl) ⟨2076704, by rfl⟩ : syracuseStep 2768939 = 4153409) B4153409
theorem B3997739 : Blo 1845624 3997739 := bstep (se 1 (by rfl) ⟨2998304, by rfl⟩ : syracuseStep 3997739 = 5996609) B5996609
theorem B5259325 : Blo 1845624 5259325 := bstep (se 3 (by rfl) ⟨986123, by rfl⟩ : syracuseStep 5259325 = 1972247) B1972247
theorem B2768969 : Blo 1845624 2768969 := bstep (se 2 (by rfl) ⟨1038363, by rfl⟩ : syracuseStep 2768969 = 2076727) B2076727
theorem B4153463 : Blo 1845624 4153463 := bstep (se 1 (by rfl) ⟨3115097, by rfl⟩ : syracuseStep 4153463 = 6230195) B6230195
theorem B3506323 : Blo 1845624 3506323 := bstep (se 1 (by rfl) ⟨2629742, by rfl⟩ : syracuseStep 3506323 = 5259485) B5259485
theorem B3743929 : Blo 1845624 3743929 := bstep (se 2 (by rfl) ⟨1403973, by rfl⟩ : syracuseStep 3743929 = 2807947) B2807947
theorem B2769083 : Blo 1845624 2769083 := bstep (se 1 (by rfl) ⟨2076812, by rfl⟩ : syracuseStep 2769083 = 4153625) B4153625
theorem B14213357 : Blo 1845624 14213357 := bstep (se 3 (by rfl) ⟨2665004, by rfl⟩ : syracuseStep 14213357 = 5330009) B5330009
theorem B2769143 : Blo 1845624 2769143 := bstep (se 1 (by rfl) ⟨2076857, by rfl⟩ : syracuseStep 2769143 = 4153715) B4153715
theorem B2769167 : Blo 1845624 2769167 := bstep (se 1 (by rfl) ⟨2076875, by rfl⟩ : syracuseStep 2769167 = 4153751) B4153751
theorem B4153643 : Blo 1845624 4153643 := bstep (se 1 (by rfl) ⟨3115232, by rfl⟩ : syracuseStep 4153643 = 6230465) B6230465
theorem B2769209 : Blo 1845624 2769209 := bstep (se 2 (by rfl) ⟨1038453, by rfl⟩ : syracuseStep 2769209 = 2076907) B2076907
theorem B2769287 : Blo 1845624 2769287 := bstep (se 1 (by rfl) ⟨2076965, by rfl⟩ : syracuseStep 2769287 = 4153931) B4153931
theorem B80986513 : Blo 1845624 80986513 := bstep (se 2 (by rfl) ⟨30369942, by rfl⟩ : syracuseStep 80986513 = 60739885) B60739885
theorem B5259667 : Blo 1845624 5259667 := bstep (se 1 (by rfl) ⟨3944750, by rfl⟩ : syracuseStep 5259667 = 7889501) B7889501
theorem B6234515 : Blo 1845624 6234515 := bstep (se 1 (by rfl) ⟨4675886, by rfl⟩ : syracuseStep 6234515 = 9351773) B9351773
theorem B2769323 : Blo 1845624 2769323 := bstep (se 1 (by rfl) ⟨2076992, by rfl⟩ : syracuseStep 2769323 = 4153985) B4153985
theorem B11829689 : Blo 1845624 11829689 := bstep (se 2 (by rfl) ⟨4436133, by rfl⟩ : syracuseStep 11829689 = 8872267) B8872267
theorem B2769353 : Blo 1845624 2769353 := bstep (se 2 (by rfl) ⟨1038507, by rfl⟩ : syracuseStep 2769353 = 2077015) B2077015
theorem B2769467 : Blo 1845624 2769467 := bstep (se 1 (by rfl) ⟨2077100, by rfl⟩ : syracuseStep 2769467 = 4154201) B4154201
theorem B2769527 : Blo 1845624 2769527 := bstep (se 1 (by rfl) ⟨2077145, by rfl⟩ : syracuseStep 2769527 = 4154291) B4154291
theorem B2769551 : Blo 1845624 2769551 := bstep (se 1 (by rfl) ⟨2077163, by rfl⟩ : syracuseStep 2769551 = 4154327) B4154327
theorem B4154003 : Blo 1845624 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B2769593 : Blo 1845624 2769593 := bstep (se 2 (by rfl) ⟨1038597, by rfl⟩ : syracuseStep 2769593 = 2077195) B2077195
theorem B4154057 : Blo 1845624 4154057 := bstep (se 2 (by rfl) ⟨1557771, by rfl⟩ : syracuseStep 4154057 = 3115543) B3115543
theorem B7013101 : Blo 1845624 7013101 := bstep (se 3 (by rfl) ⟨1314956, by rfl⟩ : syracuseStep 7013101 = 2629913) B2629913
theorem B14025473 : Blo 1845624 14025473 := bstep (se 2 (by rfl) ⟨5259552, by rfl⟩ : syracuseStep 14025473 = 10519105) B10519105
theorem B2769671 : Blo 1845624 2769671 := bstep (se 1 (by rfl) ⟨2077253, by rfl⟩ : syracuseStep 2769671 = 4154507) B4154507
theorem B2769707 : Blo 1845624 2769707 := bstep (se 1 (by rfl) ⟨2077280, by rfl⟩ : syracuseStep 2769707 = 4154561) B4154561
theorem B2769737 : Blo 1845624 2769737 := bstep (se 2 (by rfl) ⟨1038651, by rfl⟩ : syracuseStep 2769737 = 2077303) B2077303
theorem B26608499 : Blo 1845624 26608499 := bstep (se 1 (by rfl) ⟨19956374, by rfl⟩ : syracuseStep 26608499 = 39912749) B39912749
theorem B2769851 : Blo 1845624 2769851 := bstep (se 1 (by rfl) ⟨2077388, by rfl⟩ : syracuseStep 2769851 = 4154777) B4154777
theorem B2769911 : Blo 1845624 2769911 := bstep (se 1 (by rfl) ⟨2077433, by rfl⟩ : syracuseStep 2769911 = 4154867) B4154867
theorem B2769935 : Blo 1845624 2769935 := bstep (se 1 (by rfl) ⟨2077451, by rfl⟩ : syracuseStep 2769935 = 4154903) B4154903
theorem B7013405 : Blo 1845624 7013405 := bstep (se 3 (by rfl) ⟨1315013, by rfl⟩ : syracuseStep 7013405 = 2630027) B2630027
theorem B2769977 : Blo 1845624 2769977 := bstep (se 2 (by rfl) ⟨1038741, by rfl⟩ : syracuseStep 2769977 = 2077483) B2077483
theorem B5915767 : Blo 1845624 5915767 := bstep (se 1 (by rfl) ⟨4436825, by rfl⟩ : syracuseStep 5915767 = 8873651) B8873651
theorem B2770055 : Blo 1845624 2770055 := bstep (se 1 (by rfl) ⟨2077541, by rfl⟩ : syracuseStep 2770055 = 4155083) B4155083
theorem B2770091 : Blo 1845624 2770091 := bstep (se 1 (by rfl) ⟨2077568, by rfl⟩ : syracuseStep 2770091 = 4155137) B4155137
theorem B2770121 : Blo 1845624 2770121 := bstep (se 2 (by rfl) ⟨1038795, by rfl⟩ : syracuseStep 2770121 = 2077591) B2077591
theorem B3507401 : Blo 1845624 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B5260555 : Blo 1845624 5260555 := bstep (se 1 (by rfl) ⟨3945416, by rfl⟩ : syracuseStep 5260555 = 7890833) B7890833
theorem B3745057 : Blo 1845624 3745057 := bstep (se 2 (by rfl) ⟨1404396, by rfl⟩ : syracuseStep 3745057 = 2808793) B2808793
theorem B2770235 : Blo 1845624 2770235 := bstep (se 1 (by rfl) ⟨2077676, by rfl⟩ : syracuseStep 2770235 = 4155353) B4155353
theorem B2770295 : Blo 1845624 2770295 := bstep (se 1 (by rfl) ⟨2077721, by rfl⟩ : syracuseStep 2770295 = 4155443) B4155443
theorem B9979271 : Blo 1845624 9979271 := bstep (se 1 (by rfl) ⟨7484453, by rfl⟩ : syracuseStep 9979271 = 14968907) B14968907
theorem B4154759 : Blo 1845624 4154759 := bstep (se 1 (by rfl) ⟨3116069, by rfl⟩ : syracuseStep 4154759 = 6232139) B6232139
theorem B2770319 : Blo 1845624 2770319 := bstep (se 1 (by rfl) ⟨2077739, by rfl⟩ : syracuseStep 2770319 = 4155479) B4155479
theorem B19965329 : Blo 1845624 19965329 := bstep (se 2 (by rfl) ⟨7486998, by rfl⟩ : syracuseStep 19965329 = 14973997) B14973997
theorem B2770361 : Blo 1845624 2770361 := bstep (se 2 (by rfl) ⟨1038885, by rfl⟩ : syracuseStep 2770361 = 2077771) B2077771
theorem B2770439 : Blo 1845624 2770439 := bstep (se 1 (by rfl) ⟨2077829, by rfl⟩ : syracuseStep 2770439 = 4155659) B4155659
theorem B2770475 : Blo 1845624 2770475 := bstep (se 1 (by rfl) ⟨2077856, by rfl⟩ : syracuseStep 2770475 = 4155713) B4155713
theorem B4154939 : Blo 1845624 4154939 := bstep (se 1 (by rfl) ⟨3116204, by rfl⟩ : syracuseStep 4154939 = 6232409) B6232409
theorem B35964485 : Blo 1845624 35964485 := bstep (se 4 (by rfl) ⟨3371670, by rfl⟩ : syracuseStep 35964485 = 6743341) B6743341
theorem B2770505 : Blo 1845624 2770505 := bstep (se 2 (by rfl) ⟨1038939, by rfl⟩ : syracuseStep 2770505 = 2077879) B2077879
theorem B9348695 : Blo 1845624 9348695 := bstep (se 1 (by rfl) ⟨7011521, by rfl⟩ : syracuseStep 9348695 = 14023043) B14023043
theorem B15779447 : Blo 1845624 15779447 := bstep (se 1 (by rfl) ⟨11834585, by rfl⟩ : syracuseStep 15779447 = 23669171) B23669171
theorem B3327635 : Blo 1845624 3327635 := bstep (se 1 (by rfl) ⟨2495726, by rfl⟩ : syracuseStep 3327635 = 4991453) B4991453
theorem B31540913 : Blo 1845624 31540913 := bstep (se 2 (by rfl) ⟨11827842, by rfl⟩ : syracuseStep 31540913 = 23655685) B23655685
theorem B4155065 : Blo 1845624 4155065 := bstep (se 2 (by rfl) ⟨1558149, by rfl⟩ : syracuseStep 4155065 = 3116299) B3116299
theorem B2770619 : Blo 1845624 2770619 := bstep (se 1 (by rfl) ⟨2077964, by rfl⟩ : syracuseStep 2770619 = 4155929) B4155929
theorem B2770679 : Blo 1845624 2770679 := bstep (se 1 (by rfl) ⟨2078009, by rfl⟩ : syracuseStep 2770679 = 4156019) B4156019
theorem B14968577 : Blo 1845624 14968577 := bstep (se 2 (by rfl) ⟨5613216, by rfl⟩ : syracuseStep 14968577 = 11226433) B11226433
theorem B5261057 : Blo 1845624 5261057 := bstep (se 2 (by rfl) ⟨1972896, by rfl⟩ : syracuseStep 5261057 = 3945793) B3945793
theorem B3114767 : Blo 1845624 3114767 := bstep (se 1 (by rfl) ⟨2336075, by rfl⟩ : syracuseStep 3114767 = 4672151) B4672151
theorem B2770703 : Blo 1845624 2770703 := bstep (se 1 (by rfl) ⟨2078027, by rfl⟩ : syracuseStep 2770703 = 4156055) B4156055
theorem B2770745 : Blo 1845624 2770745 := bstep (se 2 (by rfl) ⟨1039029, by rfl⟩ : syracuseStep 2770745 = 2078059) B2078059
theorem B7997243 : Blo 1845624 7997243 := bstep (se 1 (by rfl) ⟨5997932, by rfl⟩ : syracuseStep 7997243 = 11995865) B11995865
theorem B2770823 : Blo 1845624 2770823 := bstep (se 1 (by rfl) ⟨2078117, by rfl⟩ : syracuseStep 2770823 = 4156235) B4156235
theorem B2336683 : Blo 1845624 2336683 := bstep (se 1 (by rfl) ⟨1752512, by rfl⟩ : syracuseStep 2336683 = 3505025) B3505025
theorem B2770859 : Blo 1845624 2770859 := bstep (se 1 (by rfl) ⟨2078144, by rfl⟩ : syracuseStep 2770859 = 4156289) B4156289
theorem B2770889 : Blo 1845624 2770889 := bstep (se 2 (by rfl) ⟨1039083, by rfl⟩ : syracuseStep 2770889 = 2078167) B2078167
theorem B4990987 : Blo 1845624 4990987 := bstep (se 1 (by rfl) ⟨3743240, by rfl⟩ : syracuseStep 4990987 = 7486481) B7486481
theorem B4155407 : Blo 1845624 4155407 := bstep (se 1 (by rfl) ⟨3116555, by rfl⟩ : syracuseStep 4155407 = 6233111) B6233111
theorem B4155425 : Blo 1845624 4155425 := bstep (se 2 (by rfl) ⟨1558284, by rfl⟩ : syracuseStep 4155425 = 3116569) B3116569
theorem B2771003 : Blo 1845624 2771003 := bstep (se 1 (by rfl) ⟨2078252, by rfl⟩ : syracuseStep 2771003 = 4156505) B4156505
theorem B9349181 : Blo 1845624 9349181 := bstep (se 3 (by rfl) ⟨1752971, by rfl⟩ : syracuseStep 9349181 = 3505943) B3505943
theorem B5261399 : Blo 1845624 5261399 := bstep (se 1 (by rfl) ⟨3946049, by rfl⟩ : syracuseStep 5261399 = 7892099) B7892099
theorem B2771063 : Blo 1845624 2771063 := bstep (se 1 (by rfl) ⟨2078297, by rfl⟩ : syracuseStep 2771063 = 4156595) B4156595
theorem B2771087 : Blo 1845624 2771087 := bstep (se 1 (by rfl) ⟨2078315, by rfl⟩ : syracuseStep 2771087 = 4156631) B4156631
theorem B4991129 : Blo 1845624 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B2771129 : Blo 1845624 2771129 := bstep (se 2 (by rfl) ⟨1039173, by rfl⟩ : syracuseStep 2771129 = 2078347) B2078347
theorem B2771207 : Blo 1845624 2771207 := bstep (se 1 (by rfl) ⟨2078405, by rfl⟩ : syracuseStep 2771207 = 4156811) B4156811
theorem B3115307 : Blo 1845624 3115307 := bstep (se 1 (by rfl) ⟨2336480, by rfl⟩ : syracuseStep 3115307 = 4672961) B4672961
theorem B2771243 : Blo 1845624 2771243 := bstep (se 1 (by rfl) ⟨2078432, by rfl⟩ : syracuseStep 2771243 = 4156865) B4156865
theorem B2771273 : Blo 1845624 2771273 := bstep (se 2 (by rfl) ⟨1039227, by rfl⟩ : syracuseStep 2771273 = 2078455) B2078455
theorem B4155767 : Blo 1845624 4155767 := bstep (se 1 (by rfl) ⟨3116825, by rfl⟩ : syracuseStep 4155767 = 6233651) B6233651
theorem B1845639 : Blo 1845624 1845639 := bstep (se 1 (by rfl) ⟨1384229, by rfl⟩ : syracuseStep 1845639 = 2768459) B2768459
theorem B1845647 : Blo 1845624 1845647 := bstep (se 1 (by rfl) ⟨1384235, by rfl⟩ : syracuseStep 1845647 = 2768471) B2768471
theorem B1845691 : Blo 1845624 1845691 := bstep (se 1 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 1845691 = 2768537) B2768537
theorem B2771387 : Blo 1845624 2771387 := bstep (se 1 (by rfl) ⟨2078540, by rfl⟩ : syracuseStep 2771387 = 4157081) B4157081
theorem B34621937 : Blo 1845624 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B1845767 : Blo 1845624 1845767 := bstep (se 1 (by rfl) ⟨1384325, by rfl⟩ : syracuseStep 1845767 = 2768651) B2768651
theorem B1845775 : Blo 1845624 1845775 := bstep (se 1 (by rfl) ⟨1384331, by rfl⟩ : syracuseStep 1845775 = 2768663) B2768663
theorem B4155947 : Blo 1845624 4155947 := bstep (se 1 (by rfl) ⟨3116960, by rfl⟩ : syracuseStep 4155947 = 6233921) B6233921
theorem B1845819 : Blo 1845624 1845819 := bstep (se 1 (by rfl) ⟨1384364, by rfl⟩ : syracuseStep 1845819 = 2768729) B2768729
theorem B2468425 : Blo 1845624 2468425 := bstep (se 2 (by rfl) ⟨925659, by rfl⟩ : syracuseStep 2468425 = 1851319) B1851319
theorem B53217911 : Blo 1845624 53217911 := bstep (se 1 (by rfl) ⟨39913433, by rfl⟩ : syracuseStep 53217911 = 79826867) B79826867
theorem B7015031 : Blo 1845624 7015031 := bstep (se 1 (by rfl) ⟨5261273, by rfl⟩ : syracuseStep 7015031 = 10522547) B10522547
theorem B1845895 : Blo 1845624 1845895 := bstep (se 1 (by rfl) ⟨1384421, by rfl⟩ : syracuseStep 1845895 = 2768843) B2768843
theorem B1845903 : Blo 1845624 1845903 := bstep (se 1 (by rfl) ⟨1384427, by rfl⟩ : syracuseStep 1845903 = 2768855) B2768855
theorem B3115705 : Blo 1845624 3115705 := bstep (se 2 (by rfl) ⟨1168389, by rfl⟩ : syracuseStep 3115705 = 2336779) B2336779
theorem B1845947 : Blo 1845624 1845947 := bstep (se 1 (by rfl) ⟨1384460, by rfl⟩ : syracuseStep 1845947 = 2768921) B2768921
theorem B4672201 : Blo 1845624 4672201 := bstep (se 2 (by rfl) ⟨1752075, by rfl⟩ : syracuseStep 4672201 = 3504151) B3504151
theorem B1846023 : Blo 1845624 1846023 := bstep (se 1 (by rfl) ⟨1384517, by rfl⟩ : syracuseStep 1846023 = 2769035) B2769035
theorem B1846031 : Blo 1845624 1846031 := bstep (se 1 (by rfl) ⟨1384523, by rfl⟩ : syracuseStep 1846031 = 2769047) B2769047
theorem B1846075 : Blo 1845624 1846075 := bstep (se 1 (by rfl) ⟨1384556, by rfl⟩ : syracuseStep 1846075 = 2769113) B2769113
theorem B5917499 : Blo 1845624 5917499 := bstep (se 1 (by rfl) ⟨4438124, by rfl⟩ : syracuseStep 5917499 = 8876249) B8876249
theorem B4672343 : Blo 1845624 4672343 := bstep (se 1 (by rfl) ⟨3504257, by rfl⟩ : syracuseStep 4672343 = 7008515) B7008515
theorem B2337655 : Blo 1845624 2337655 := bstep (se 1 (by rfl) ⟨1753241, by rfl⟩ : syracuseStep 2337655 = 3506483) B3506483
theorem B1846151 : Blo 1845624 1846151 := bstep (se 1 (by rfl) ⟨1384613, by rfl⟩ : syracuseStep 1846151 = 2769227) B2769227
theorem B5614471 : Blo 1845624 5614471 := bstep (se 1 (by rfl) ⟨4210853, by rfl⟩ : syracuseStep 5614471 = 8421707) B8421707
theorem B1846159 : Blo 1845624 1846159 := bstep (se 1 (by rfl) ⟨1384619, by rfl⟩ : syracuseStep 1846159 = 2769239) B2769239
theorem B4156307 : Blo 1845624 4156307 := bstep (se 1 (by rfl) ⟨3117230, by rfl⟩ : syracuseStep 4156307 = 6234461) B6234461
theorem B13306787 : Blo 1845624 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B5999545 : Blo 1845624 5999545 := bstep (se 2 (by rfl) ⟨2249829, by rfl⟩ : syracuseStep 5999545 = 4499659) B4499659
theorem B1846203 : Blo 1845624 1846203 := bstep (se 1 (by rfl) ⟨1384652, by rfl⟩ : syracuseStep 1846203 = 2769305) B2769305
theorem B4156361 : Blo 1845624 4156361 := bstep (se 2 (by rfl) ⟨1558635, by rfl⟩ : syracuseStep 4156361 = 3117271) B3117271
theorem B1846279 : Blo 1845624 1846279 := bstep (se 1 (by rfl) ⟨1384709, by rfl⟩ : syracuseStep 1846279 = 2769419) B2769419
theorem B19958795 : Blo 1845624 19958795 := bstep (se 1 (by rfl) ⟨14969096, by rfl⟩ : syracuseStep 19958795 = 29938193) B29938193
theorem B1846287 : Blo 1845624 1846287 := bstep (se 1 (by rfl) ⟨1384715, by rfl⟩ : syracuseStep 1846287 = 2769431) B2769431
theorem B14969879 : Blo 1845624 14969879 := bstep (se 1 (by rfl) ⟨11227409, by rfl⟩ : syracuseStep 14969879 = 22454819) B22454819
theorem B1846331 : Blo 1845624 1846331 := bstep (se 1 (by rfl) ⟨1384748, by rfl⟩ : syracuseStep 1846331 = 2769497) B2769497
theorem B10955843 : Blo 1845624 10955843 := bstep (se 1 (by rfl) ⟨8216882, by rfl⟩ : syracuseStep 10955843 = 16433765) B16433765
theorem B1846407 : Blo 1845624 1846407 := bstep (se 1 (by rfl) ⟨1384805, by rfl⟩ : syracuseStep 1846407 = 2769611) B2769611
theorem B1846415 : Blo 1845624 1846415 := bstep (se 1 (by rfl) ⟨1384811, by rfl⟩ : syracuseStep 1846415 = 2769623) B2769623
theorem B3943571 : Blo 1845624 3943571 := bstep (se 1 (by rfl) ⟨2957678, by rfl⟩ : syracuseStep 3943571 = 5915357) B5915357
theorem B1846459 : Blo 1845624 1846459 := bstep (se 1 (by rfl) ⟨1384844, by rfl⟩ : syracuseStep 1846459 = 2769689) B2769689
theorem B2337979 : Blo 1845624 2337979 := bstep (se 1 (by rfl) ⟨1753484, by rfl⟩ : syracuseStep 2337979 = 3506969) B3506969
theorem B1846535 : Blo 1845624 1846535 := bstep (se 1 (by rfl) ⟨1384901, by rfl⟩ : syracuseStep 1846535 = 2769803) B2769803
theorem B4435211 : Blo 1845624 4435211 := bstep (se 1 (by rfl) ⟨3326408, by rfl⟩ : syracuseStep 4435211 = 6652817) B6652817
theorem B1846543 : Blo 1845624 1846543 := bstep (se 1 (by rfl) ⟨1384907, by rfl⟩ : syracuseStep 1846543 = 2769815) B2769815
theorem B1846587 : Blo 1845624 1846587 := bstep (se 1 (by rfl) ⟨1384940, by rfl⟩ : syracuseStep 1846587 = 2769881) B2769881
theorem B4992371 : Blo 1845624 4992371 := bstep (se 1 (by rfl) ⟨3744278, by rfl⟩ : syracuseStep 4992371 = 7488557) B7488557
theorem B3116407 : Blo 1845624 3116407 := bstep (se 1 (by rfl) ⟨2337305, by rfl⟩ : syracuseStep 3116407 = 4674611) B4674611
theorem B33680771 : Blo 1845624 33680771 := bstep (se 1 (by rfl) ⟨25260578, by rfl⟩ : syracuseStep 33680771 = 50521157) B50521157
theorem B10513799 : Blo 1845624 10513799 := bstep (se 1 (by rfl) ⟨7885349, by rfl⟩ : syracuseStep 10513799 = 15770699) B15770699
theorem B1846663 : Blo 1845624 1846663 := bstep (se 1 (by rfl) ⟨1384997, by rfl⟩ : syracuseStep 1846663 = 2769995) B2769995
theorem B1846671 : Blo 1845624 1846671 := bstep (se 1 (by rfl) ⟨1385003, by rfl⟩ : syracuseStep 1846671 = 2770007) B2770007
theorem B1846715 : Blo 1845624 1846715 := bstep (se 1 (by rfl) ⟨1385036, by rfl⟩ : syracuseStep 1846715 = 2770073) B2770073
theorem B1846791 : Blo 1845624 1846791 := bstep (se 1 (by rfl) ⟨1385093, by rfl⟩ : syracuseStep 1846791 = 2770187) B2770187
theorem B7007755 : Blo 1845624 7007755 := bstep (se 1 (by rfl) ⟨5255816, by rfl⟩ : syracuseStep 7007755 = 10511633) B10511633
theorem B1846799 : Blo 1845624 1846799 := bstep (se 1 (by rfl) ⟨1385099, by rfl⟩ : syracuseStep 1846799 = 2770199) B2770199
theorem B6229547 : Blo 1845624 6229547 := bstep (se 1 (by rfl) ⟨4672160, by rfl⟩ : syracuseStep 6229547 = 9344321) B9344321
theorem B1846843 : Blo 1845624 1846843 := bstep (se 1 (by rfl) ⟨1385132, by rfl⟩ : syracuseStep 1846843 = 2770265) B2770265
theorem B3116603 : Blo 1845624 3116603 := bstep (se 1 (by rfl) ⟨2337452, by rfl⟩ : syracuseStep 3116603 = 4674905) B4674905
theorem B1846919 : Blo 1845624 1846919 := bstep (se 1 (by rfl) ⟨1385189, by rfl⟩ : syracuseStep 1846919 = 2770379) B2770379
theorem B4157063 : Blo 1845624 4157063 := bstep (se 1 (by rfl) ⟨3117797, by rfl⟩ : syracuseStep 4157063 = 6235595) B6235595
theorem B1846927 : Blo 1845624 1846927 := bstep (se 1 (by rfl) ⟨1385195, by rfl⟩ : syracuseStep 1846927 = 2770391) B2770391
theorem B1846971 : Blo 1845624 1846971 := bstep (se 1 (by rfl) ⟨1385228, by rfl⟩ : syracuseStep 1846971 = 2770457) B2770457
theorem B1847047 : Blo 1845624 1847047 := bstep (se 1 (by rfl) ⟨1385285, by rfl⟩ : syracuseStep 1847047 = 2770571) B2770571
theorem B1847055 : Blo 1845624 1847055 := bstep (se 1 (by rfl) ⟨1385291, by rfl⟩ : syracuseStep 1847055 = 2770583) B2770583
theorem B16854799 : Blo 1845624 16854799 := bstep (se 1 (by rfl) ⟨12641099, by rfl⟩ : syracuseStep 16854799 = 25282199) B25282199
theorem B33681203 : Blo 1845624 33681203 := bstep (se 1 (by rfl) ⟨25260902, by rfl⟩ : syracuseStep 33681203 = 50521805) B50521805
theorem B9350963 : Blo 1845624 9350963 := bstep (se 1 (by rfl) ⟨7013222, by rfl⟩ : syracuseStep 9350963 = 14026445) B14026445
theorem B7008059 : Blo 1845624 7008059 := bstep (se 1 (by rfl) ⟨5256044, by rfl⟩ : syracuseStep 7008059 = 10512089) B10512089
theorem B2076475 : Blo 1845624 2076475 := bstep (se 1 (by rfl) ⟨1557356, by rfl⟩ : syracuseStep 2076475 = 3114713) B3114713
theorem B1847099 : Blo 1845624 1847099 := bstep (se 1 (by rfl) ⟨1385324, by rfl⟩ : syracuseStep 1847099 = 2770649) B2770649
theorem B4435847 : Blo 1845624 4435847 := bstep (se 1 (by rfl) ⟨3326885, by rfl⟩ : syracuseStep 4435847 = 6653771) B6653771
theorem B1847175 : Blo 1845624 1847175 := bstep (se 1 (by rfl) ⟨1385381, by rfl⟩ : syracuseStep 1847175 = 2770763) B2770763
theorem B1847183 : Blo 1845624 1847183 := bstep (se 1 (by rfl) ⟨1385387, by rfl⟩ : syracuseStep 1847183 = 2770775) B2770775
theorem B26619799 : Blo 1845624 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1847227 : Blo 1845624 1847227 := bstep (se 1 (by rfl) ⟨1385420, by rfl⟩ : syracuseStep 1847227 = 2770841) B2770841
theorem B3117001 : Blo 1845624 3117001 := bstep (se 2 (by rfl) ⟨1168875, by rfl⟩ : syracuseStep 3117001 = 2337751) B2337751
theorem B11235293 : Blo 1845624 11235293 := bstep (se 3 (by rfl) ⟨2106617, by rfl⟩ : syracuseStep 11235293 = 4213235) B4213235
theorem B1847303 : Blo 1845624 1847303 := bstep (se 1 (by rfl) ⟨1385477, by rfl⟩ : syracuseStep 1847303 = 2770955) B2770955
theorem B5328911 : Blo 1845624 5328911 := bstep (se 1 (by rfl) ⟨3996683, by rfl⟩ : syracuseStep 5328911 = 7993367) B7993367
theorem B1847311 : Blo 1845624 1847311 := bstep (se 1 (by rfl) ⟨1385483, by rfl⟩ : syracuseStep 1847311 = 2770967) B2770967
theorem B1847355 : Blo 1845624 1847355 := bstep (se 1 (by rfl) ⟨1385516, by rfl⟩ : syracuseStep 1847355 = 2771033) B2771033
theorem B9351287 : Blo 1845624 9351287 := bstep (se 1 (by rfl) ⟨7013465, by rfl⟩ : syracuseStep 9351287 = 14026931) B14026931
theorem B4993159 : Blo 1845624 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B1847431 : Blo 1845624 1847431 := bstep (se 1 (by rfl) ⟨1385573, by rfl⟩ : syracuseStep 1847431 = 2771147) B2771147
theorem B1847439 : Blo 1845624 1847439 := bstep (se 1 (by rfl) ⟨1385579, by rfl⟩ : syracuseStep 1847439 = 2771159) B2771159
theorem B1847483 : Blo 1845624 1847483 := bstep (se 1 (by rfl) ⟨1385612, by rfl⟩ : syracuseStep 1847483 = 2771225) B2771225
theorem B5329097 : Blo 1845624 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B1847559 : Blo 1845624 1847559 := bstep (se 1 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 1847559 = 2771339) B2771339
theorem B2076943 : Blo 1845624 2076943 := bstep (se 1 (by rfl) ⟨1557707, by rfl⟩ : syracuseStep 2076943 = 3115415) B3115415
theorem B1847567 : Blo 1845624 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B7008545 : Blo 1845624 7008545 := bstep (se 2 (by rfl) ⟨2628204, by rfl⟩ : syracuseStep 7008545 = 5256409) B5256409
theorem B15774011 : Blo 1845624 15774011 := bstep (se 1 (by rfl) ⟨11830508, by rfl⟩ : syracuseStep 15774011 = 23661017) B23661017
theorem B1847611 : Blo 1845624 1847611 := bstep (se 1 (by rfl) ⟨1385708, by rfl⟩ : syracuseStep 1847611 = 2771417) B2771417
theorem B12800477 : Blo 1845624 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B9343511 : Blo 1845624 9343511 := bstep (se 1 (by rfl) ⟨7007633, by rfl⟩ : syracuseStep 9343511 = 14015267) B14015267
theorem B8876573 : Blo 1845624 8876573 := bstep (se 3 (by rfl) ⟨1664357, by rfl⟩ : syracuseStep 8876573 = 3328715) B3328715
theorem B10515005 : Blo 1845624 10515005 := bstep (se 3 (by rfl) ⟨1971563, by rfl⟩ : syracuseStep 10515005 = 3943127) B3943127
theorem B4436615 : Blo 1845624 4436615 := bstep (se 1 (by rfl) ⟨3327461, by rfl⟩ : syracuseStep 4436615 = 6654923) B6654923
theorem B3117703 : Blo 1845624 3117703 := bstep (se 1 (by rfl) ⟨2338277, by rfl⟩ : syracuseStep 3117703 = 4676555) B4676555
theorem B1897103 : Blo 1845624 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B3945161 : Blo 1845624 3945161 := bstep (se 2 (by rfl) ⟨1479435, by rfl⟩ : syracuseStep 3945161 = 2958871) B2958871
theorem B2077447 : Blo 1845624 2077447 := bstep (se 1 (by rfl) ⟨1558085, by rfl⟩ : syracuseStep 2077447 = 3116171) B3116171
theorem B19960613 : Blo 1845624 19960613 := bstep (se 4 (by rfl) ⟨1871307, by rfl⟩ : syracuseStep 19960613 = 3742615) B3742615
theorem B12636965 : Blo 1845624 12636965 := bstep (se 4 (by rfl) ⟨1184715, by rfl⟩ : syracuseStep 12636965 = 2369431) B2369431
theorem B6230843 : Blo 1845624 6230843 := bstep (se 1 (by rfl) ⟨4673132, by rfl⟩ : syracuseStep 6230843 = 9346265) B9346265
theorem B4674419 : Blo 1845624 4674419 := bstep (se 1 (by rfl) ⟨3505814, by rfl⟩ : syracuseStep 4674419 = 7011629) B7011629
theorem B2077627 : Blo 1845624 2077627 := bstep (se 1 (by rfl) ⟨1558220, by rfl⟩ : syracuseStep 2077627 = 3116441) B3116441
theorem B2249743 : Blo 1845624 2249743 := bstep (se 1 (by rfl) ⟨1687307, by rfl⟩ : syracuseStep 2249743 = 3374615) B3374615
theorem B14029847 : Blo 1845624 14029847 := bstep (se 1 (by rfl) ⟨10522385, by rfl⟩ : syracuseStep 14029847 = 21044771) B21044771
theorem B9352259 : Blo 1845624 9352259 := bstep (se 1 (by rfl) ⟨7014194, by rfl⟩ : syracuseStep 9352259 = 14028389) B14028389
theorem B7009517 : Blo 1845624 7009517 := bstep (se 3 (by rfl) ⟨1314284, by rfl⟩ : syracuseStep 7009517 = 2628569) B2628569
theorem B6231329 : Blo 1845624 6231329 := bstep (se 2 (by rfl) ⟨2336748, by rfl⟩ : syracuseStep 6231329 = 4673497) B4673497
theorem B5256535 : Blo 1845624 5256535 := bstep (se 1 (by rfl) ⟨3942401, by rfl⟩ : syracuseStep 5256535 = 7884803) B7884803
theorem B4674935 : Blo 1845624 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B9352583 : Blo 1845624 9352583 := bstep (se 1 (by rfl) ⟨7014437, by rfl⟩ : syracuseStep 9352583 = 14028875) B14028875
theorem B2078095 : Blo 1845624 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B72955313 : Blo 1845624 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B118494737 : Blo 1845624 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B9983549 : Blo 1845624 9983549 := bstep (se 3 (by rfl) ⟨1871915, by rfl⟩ : syracuseStep 9983549 = 3743831) B3743831
theorem B7304975 : Blo 1845624 7304975 := bstep (se 1 (by rfl) ⟨5478731, by rfl⟩ : syracuseStep 7304975 = 10957463) B10957463
theorem B6231923 : Blo 1845624 6231923 := bstep (se 1 (by rfl) ⟨4673942, by rfl⟩ : syracuseStep 6231923 = 9347885) B9347885
theorem B7886801 : Blo 1845624 7886801 := bstep (se 2 (by rfl) ⟨2957550, by rfl⟩ : syracuseStep 7886801 = 5915101) B5915101
theorem B3741755 : Blo 1845624 3741755 := bstep (se 1 (by rfl) ⟨2806316, by rfl⟩ : syracuseStep 3741755 = 5612633) B5612633
theorem B6658109 : Blo 1845624 6658109 := bstep (se 3 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 6658109 = 2496791) B2496791
theorem B6314273 : Blo 1845624 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B4675927 : Blo 1845624 4675927 := bstep (se 1 (by rfl) ⟨3506945, by rfl⟩ : syracuseStep 4675927 = 7013891) B7013891
theorem B8993159 : Blo 1845624 8993159 := bstep (se 1 (by rfl) ⟨6744869, by rfl⟩ : syracuseStep 8993159 = 13489739) B13489739
theorem B2628011 : Blo 1845624 2628011 := bstep (se 1 (by rfl) ⟨1971008, by rfl⟩ : syracuseStep 2628011 = 3942017) B3942017
theorem B11827741 : Blo 1845624 11827741 := bstep (se 3 (by rfl) ⟨2217701, by rfl⟩ : syracuseStep 11827741 = 4435403) B4435403
theorem B3504683 : Blo 1845624 3504683 := bstep (se 1 (by rfl) ⟨2628512, by rfl⟩ : syracuseStep 3504683 = 5257025) B5257025
theorem B30366251 : Blo 1845624 30366251 := bstep (se 1 (by rfl) ⟨22774688, by rfl⟩ : syracuseStep 30366251 = 45549377) B45549377
theorem B4676231 : Blo 1845624 4676231 := bstep (se 1 (by rfl) ⟨3507173, by rfl⟩ : syracuseStep 4676231 = 7014347) B7014347
theorem B1972879 : Blo 1845624 1972879 := bstep (se 1 (by rfl) ⟨1479659, by rfl⟩ : syracuseStep 1972879 = 2959319) B2959319
theorem B1972999 : Blo 1845624 1972999 := bstep (se 1 (by rfl) ⟨1479749, by rfl⟩ : syracuseStep 1972999 = 2959499) B2959499
theorem B4676363 : Blo 1845624 4676363 := bstep (se 1 (by rfl) ⟨3507272, by rfl⟩ : syracuseStep 4676363 = 7014545) B7014545
theorem B5258027 : Blo 1845624 5258027 := bstep (se 1 (by rfl) ⟨3943520, by rfl⟩ : syracuseStep 5258027 = 7887041) B7887041
theorem B8420395 : Blo 1845624 8420395 := bstep (se 1 (by rfl) ⟨6315296, by rfl⟩ : syracuseStep 8420395 = 12630593) B12630593
theorem B7011643 : Blo 1845624 7011643 := bstep (se 1 (by rfl) ⟨5258732, by rfl⟩ : syracuseStep 7011643 = 10517465) B10517465
theorem B3743111 : Blo 1845624 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B4152761 : Blo 1845624 4152761 := bstep (se 2 (by rfl) ⟨1557285, by rfl⟩ : syracuseStep 4152761 = 3114571) B3114571
theorem B3505609 : Blo 1845624 3505609 := bstep (se 2 (by rfl) ⟨1314603, by rfl⟩ : syracuseStep 3505609 = 2629207) B2629207
theorem B11992541 : Blo 1845624 11992541 := bstep (se 3 (by rfl) ⟨2248601, by rfl⟩ : syracuseStep 11992541 = 4497203) B4497203
theorem B170548739 : Blo 1845624 170548739 := bstep (se 1 (by rfl) ⟨127911554, by rfl⟩ : syracuseStep 170548739 = 255823109) B255823109
theorem B9346589 : Blo 1845624 9346589 := bstep (se 3 (by rfl) ⟨1752485, by rfl⟩ : syracuseStep 9346589 = 3504971) B3504971
theorem B2768441 : Blo 1845624 2768441 := bstep (se 2 (by rfl) ⟨1038165, by rfl⟩ : syracuseStep 2768441 = 2076331) B2076331
theorem B17997389 : Blo 1845624 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B47980133 : Blo 1845624 47980133 := bstep (se 4 (by rfl) ⟨4498137, by rfl⟩ : syracuseStep 47980133 = 8996275) B8996275
theorem B2768519 : Blo 1845624 2768519 := bstep (se 1 (by rfl) ⟨2076389, by rfl⟩ : syracuseStep 2768519 = 4152779) B4152779
theorem B2768555 : Blo 1845624 2768555 := bstep (se 1 (by rfl) ⟨2076416, by rfl⟩ : syracuseStep 2768555 = 4152833) B4152833
theorem B2768585 : Blo 1845624 2768585 := bstep (se 2 (by rfl) ⟨1038219, by rfl⟩ : syracuseStep 2768585 = 2076439) B2076439
theorem B4153103 : Blo 1845624 4153103 := bstep (se 1 (by rfl) ⟨3114827, by rfl⟩ : syracuseStep 4153103 = 6229655) B6229655
theorem B4153121 : Blo 1845624 4153121 := bstep (se 2 (by rfl) ⟨1557420, by rfl⟩ : syracuseStep 4153121 = 3114841) B3114841
theorem B7012129 : Blo 1845624 7012129 := bstep (se 2 (by rfl) ⟨2629548, by rfl⟩ : syracuseStep 7012129 = 5259097) B5259097
theorem B2768699 : Blo 1845624 2768699 := bstep (se 1 (by rfl) ⟨2076524, by rfl⟩ : syracuseStep 2768699 = 4153049) B4153049
theorem B2629435 : Blo 1845624 2629435 := bstep (se 1 (by rfl) ⟨1972076, by rfl⟩ : syracuseStep 2629435 = 3944153) B3944153
theorem B13311859 : Blo 1845624 13311859 := bstep (se 1 (by rfl) ⟨9983894, by rfl⟩ : syracuseStep 13311859 = 19967789) B19967789
theorem B2768759 : Blo 1845624 2768759 := bstep (se 1 (by rfl) ⟨2076569, by rfl⟩ : syracuseStep 2768759 = 4153139) B4153139
theorem B5259143 : Blo 1845624 5259143 := bstep (se 1 (by rfl) ⟨3944357, by rfl⟩ : syracuseStep 5259143 = 7888715) B7888715
theorem B2768783 : Blo 1845624 2768783 := bstep (se 1 (by rfl) ⟨2076587, by rfl⟩ : syracuseStep 2768783 = 4153175) B4153175
theorem B2768825 : Blo 1845624 2768825 := bstep (se 2 (by rfl) ⟨1038309, by rfl⟩ : syracuseStep 2768825 = 2076619) B2076619
theorem B2768975 : Blo 1845624 2768975 := bstep (se 1 (by rfl) ⟨2076731, by rfl⟩ : syracuseStep 2768975 = 4153463) B4153463
theorem B6234191 : Blo 1845624 6234191 := bstep (se 1 (by rfl) ⟨4675643, by rfl⟩ : syracuseStep 6234191 = 9351287) B9351287
theorem B7012433 : Blo 1845624 7012433 := bstep (se 2 (by rfl) ⟨2629662, by rfl⟩ : syracuseStep 7012433 = 5259325) B5259325
theorem B9978013 : Blo 1845624 9978013 := bstep (se 3 (by rfl) ⟨1870877, by rfl⟩ : syracuseStep 9978013 = 3741755) B3741755
theorem B2769095 : Blo 1845624 2769095 := bstep (se 1 (by rfl) ⟨2076821, by rfl⟩ : syracuseStep 2769095 = 4153643) B4153643
theorem B2769257 : Blo 1845624 2769257 := bstep (se 2 (by rfl) ⟨1038471, by rfl⟩ : syracuseStep 2769257 = 2076943) B2076943
theorem B2957743 : Blo 1845624 2957743 := bstep (se 1 (by rfl) ⟨2218307, by rfl⟩ : syracuseStep 2957743 = 4436615) B4436615
theorem B2769335 : Blo 1845624 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B6234569 : Blo 1845624 6234569 := bstep (se 2 (by rfl) ⟨2337963, by rfl⟩ : syracuseStep 6234569 = 4675927) B4675927
theorem B2769371 : Blo 1845624 2769371 := bstep (se 1 (by rfl) ⟨2077028, by rfl⟩ : syracuseStep 2769371 = 4154057) B4154057
theorem B2630107 : Blo 1845624 2630107 := bstep (se 1 (by rfl) ⟨1972580, by rfl⟩ : syracuseStep 2630107 = 3945161) B3945161
theorem B7012889 : Blo 1845624 7012889 := bstep (se 2 (by rfl) ⟨2629833, by rfl⟩ : syracuseStep 7012889 = 5259667) B5259667
theorem B4153895 : Blo 1845624 4153895 := bstep (se 1 (by rfl) ⟨3115421, by rfl⟩ : syracuseStep 4153895 = 6230843) B6230843
theorem B85303925 : Blo 1845624 85303925 := bstep (se 5 (by rfl) ⟨3998621, by rfl⟩ : syracuseStep 85303925 = 7997243) B7997243
theorem B15770321 : Blo 1845624 15770321 := bstep (se 2 (by rfl) ⟨5913870, by rfl⟩ : syracuseStep 15770321 = 11827741) B11827741
theorem B6234839 : Blo 1845624 6234839 := bstep (se 1 (by rfl) ⟨4676129, by rfl⟩ : syracuseStep 6234839 = 9352259) B9352259
theorem B4154219 : Blo 1845624 4154219 := bstep (se 1 (by rfl) ⟨3115664, by rfl⟩ : syracuseStep 4154219 = 6231329) B6231329
theorem B4154273 : Blo 1845624 4154273 := bstep (se 2 (by rfl) ⟨1557852, by rfl⟩ : syracuseStep 4154273 = 3115705) B3115705
theorem B6652847 : Blo 1845624 6652847 := bstep (se 1 (by rfl) ⟨4989635, by rfl⟩ : syracuseStep 6652847 = 9979271) B9979271
theorem B2769839 : Blo 1845624 2769839 := bstep (se 1 (by rfl) ⟨2077379, by rfl⟩ : syracuseStep 2769839 = 4154759) B4154759
theorem B6235055 : Blo 1845624 6235055 := bstep (se 1 (by rfl) ⟨4676291, by rfl⟩ : syracuseStep 6235055 = 9352583) B9352583
theorem B48636875 : Blo 1845624 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B2769929 : Blo 1845624 2769929 := bstep (se 2 (by rfl) ⟨1038723, by rfl⟩ : syracuseStep 2769929 = 2077447) B2077447
theorem B2630665 : Blo 1845624 2630665 := bstep (se 2 (by rfl) ⟨986499, by rfl⟩ : syracuseStep 2630665 = 1972999) B1972999
theorem B78996491 : Blo 1845624 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B2769959 : Blo 1845624 2769959 := bstep (se 1 (by rfl) ⟨2077469, by rfl⟩ : syracuseStep 2769959 = 4154939) B4154939
theorem B10519631 : Blo 1845624 10519631 := bstep (se 1 (by rfl) ⟨7889723, by rfl⟩ : syracuseStep 10519631 = 15779447) B15779447
theorem B2770043 : Blo 1845624 2770043 := bstep (se 1 (by rfl) ⟨2077532, by rfl⟩ : syracuseStep 2770043 = 4155065) B4155065
theorem B9979051 : Blo 1845624 9979051 := bstep (se 1 (by rfl) ⟨7484288, by rfl⟩ : syracuseStep 9979051 = 14968577) B14968577
theorem B3507371 : Blo 1845624 3507371 := bstep (se 1 (by rfl) ⟨2630528, by rfl⟩ : syracuseStep 3507371 = 5261057) B5261057
theorem B4154615 : Blo 1845624 4154615 := bstep (se 1 (by rfl) ⟨3115961, by rfl⟩ : syracuseStep 4154615 = 6231923) B6231923
theorem B2770169 : Blo 1845624 2770169 := bstep (se 2 (by rfl) ⟨1038813, by rfl⟩ : syracuseStep 2770169 = 2077627) B2077627
theorem B2770271 : Blo 1845624 2770271 := bstep (se 1 (by rfl) ⟨2077703, by rfl⟩ : syracuseStep 2770271 = 4155407) B4155407
theorem B2999657 : Blo 1845624 2999657 := bstep (se 2 (by rfl) ⟨1124871, by rfl⟩ : syracuseStep 2999657 = 2249743) B2249743
theorem B2770283 : Blo 1845624 2770283 := bstep (se 1 (by rfl) ⟨2077712, by rfl⟩ : syracuseStep 2770283 = 4155425) B4155425
theorem B3507599 : Blo 1845624 3507599 := bstep (se 1 (by rfl) ⟨2630699, by rfl⟩ : syracuseStep 3507599 = 5261399) B5261399
theorem B3327419 : Blo 1845624 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B2770511 : Blo 1845624 2770511 := bstep (se 1 (by rfl) ⟨2077883, by rfl⟩ : syracuseStep 2770511 = 4155767) B4155767
theorem B7014073 : Blo 1845624 7014073 := bstep (se 2 (by rfl) ⟨2630277, by rfl⟩ : syracuseStep 7014073 = 5260555) B5260555
theorem B2336455 : Blo 1845624 2336455 := bstep (se 1 (by rfl) ⟨1752341, by rfl⟩ : syracuseStep 2336455 = 3504683) B3504683
theorem B2770631 : Blo 1845624 2770631 := bstep (se 1 (by rfl) ⟨2077973, by rfl⟩ : syracuseStep 2770631 = 4155947) B4155947
theorem B20244167 : Blo 1845624 20244167 := bstep (se 1 (by rfl) ⟨15183125, by rfl⟩ : syracuseStep 20244167 = 30366251) B30366251
theorem B9348857 : Blo 1845624 9348857 := bstep (se 2 (by rfl) ⟨3505821, by rfl⟩ : syracuseStep 9348857 = 7011643) B7011643
theorem B4155209 : Blo 1845624 4155209 := bstep (se 2 (by rfl) ⟨1558203, by rfl⟩ : syracuseStep 4155209 = 3116407) B3116407
theorem B2770793 : Blo 1845624 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B3114895 : Blo 1845624 3114895 := bstep (se 1 (by rfl) ⟨2336171, by rfl⟩ : syracuseStep 3114895 = 4672343) B4672343
theorem B2770871 : Blo 1845624 2770871 := bstep (se 1 (by rfl) ⟨2078153, by rfl⟩ : syracuseStep 2770871 = 4156307) B4156307
theorem B2770907 : Blo 1845624 2770907 := bstep (se 1 (by rfl) ⟨2078180, by rfl⟩ : syracuseStep 2770907 = 4156361) B4156361
theorem B13305863 : Blo 1845624 13305863 := bstep (se 1 (by rfl) ⟨9979397, by rfl⟩ : syracuseStep 13305863 = 19958795) B19958795
theorem B9979919 : Blo 1845624 9979919 := bstep (se 1 (by rfl) ⟨7484939, by rfl⟩ : syracuseStep 9979919 = 14969879) B14969879
theorem B3328247 : Blo 1845624 3328247 := bstep (se 1 (by rfl) ⟨2496185, by rfl⟩ : syracuseStep 3328247 = 4992371) B4992371
theorem B113699159 : Blo 1845624 113699159 := bstep (se 1 (by rfl) ⟨85274369, by rfl⟩ : syracuseStep 113699159 = 170548739) B170548739
theorem B22473065 : Blo 1845624 22473065 := bstep (se 2 (by rfl) ⟨8427399, by rfl⟩ : syracuseStep 22473065 = 16854799) B16854799
theorem B1845627 : Blo 1845624 1845627 := bstep (se 1 (by rfl) ⟨1384220, by rfl⟩ : syracuseStep 1845627 = 2768441) B2768441
theorem B9349505 : Blo 1845624 9349505 := bstep (se 2 (by rfl) ⟨3506064, by rfl⟩ : syracuseStep 9349505 = 7012129) B7012129
theorem B1845679 : Blo 1845624 1845679 := bstep (se 1 (by rfl) ⟨1384259, by rfl⟩ : syracuseStep 1845679 = 2768519) B2768519
theorem B2771375 : Blo 1845624 2771375 := bstep (se 1 (by rfl) ⟨2078531, by rfl⟩ : syracuseStep 2771375 = 4157063) B4157063
theorem B1845703 : Blo 1845624 1845703 := bstep (se 1 (by rfl) ⟨1384277, by rfl⟩ : syracuseStep 1845703 = 2768555) B2768555
theorem B1845723 : Blo 1845624 1845723 := bstep (se 1 (by rfl) ⟨1384292, by rfl⟩ : syracuseStep 1845723 = 2768585) B2768585
theorem B4672039 : Blo 1845624 4672039 := bstep (se 1 (by rfl) ⟨3504029, by rfl⟩ : syracuseStep 4672039 = 7008059) B7008059
theorem B1845799 : Blo 1845624 1845799 := bstep (se 1 (by rfl) ⟨1384349, by rfl⟩ : syracuseStep 1845799 = 2768699) B2768699
theorem B3115577 : Blo 1845624 3115577 := bstep (se 2 (by rfl) ⟨1168341, by rfl⟩ : syracuseStep 3115577 = 2336683) B2336683
theorem B1845839 : Blo 1845624 1845839 := bstep (se 1 (by rfl) ⟨1384379, by rfl⟩ : syracuseStep 1845839 = 2768759) B2768759
theorem B1845855 : Blo 1845624 1845855 := bstep (se 1 (by rfl) ⟨1384391, by rfl⟩ : syracuseStep 1845855 = 2768783) B2768783
theorem B4156001 : Blo 1845624 4156001 := bstep (se 2 (by rfl) ⟨1558500, by rfl⟩ : syracuseStep 4156001 = 3117001) B3117001
theorem B1845883 : Blo 1845624 1845883 := bstep (se 1 (by rfl) ⟨1384412, by rfl⟩ : syracuseStep 1845883 = 2768825) B2768825
theorem B7490195 : Blo 1845624 7490195 := bstep (se 1 (by rfl) ⟨5617646, by rfl⟩ : syracuseStep 7490195 = 11235293) B11235293
theorem B1845935 : Blo 1845624 1845935 := bstep (se 1 (by rfl) ⟨1384451, by rfl⟩ : syracuseStep 1845935 = 2768903) B2768903
theorem B6654649 : Blo 1845624 6654649 := bstep (se 2 (by rfl) ⟨2495493, by rfl⟩ : syracuseStep 6654649 = 4990987) B4990987
theorem B1845959 : Blo 1845624 1845959 := bstep (se 1 (by rfl) ⟨1384469, by rfl⟩ : syracuseStep 1845959 = 2768939) B2768939
theorem B1845979 : Blo 1845624 1845979 := bstep (se 1 (by rfl) ⟨1384484, by rfl⟩ : syracuseStep 1845979 = 2768969) B2768969
theorem B10660637 : Blo 1845624 10660637 := bstep (se 3 (by rfl) ⟨1998869, by rfl⟩ : syracuseStep 10660637 = 3997739) B3997739
theorem B1846055 : Blo 1845624 1846055 := bstep (se 1 (by rfl) ⟨1384541, by rfl⟩ : syracuseStep 1846055 = 2769083) B2769083
theorem B1846095 : Blo 1845624 1846095 := bstep (se 1 (by rfl) ⟨1384571, by rfl⟩ : syracuseStep 1846095 = 2769143) B2769143
theorem B1846111 : Blo 1845624 1846111 := bstep (se 1 (by rfl) ⟨1384583, by rfl⟩ : syracuseStep 1846111 = 2769167) B2769167
theorem B4672363 : Blo 1845624 4672363 := bstep (se 1 (by rfl) ⟨3504272, by rfl⟩ : syracuseStep 4672363 = 7008545) B7008545
theorem B1846139 : Blo 1845624 1846139 := bstep (se 1 (by rfl) ⟨1384604, by rfl⟩ : syracuseStep 1846139 = 2769209) B2769209
theorem B4991905 : Blo 1845624 4991905 := bstep (se 2 (by rfl) ⟨1871964, by rfl⟩ : syracuseStep 4991905 = 3743929) B3743929
theorem B1846191 : Blo 1845624 1846191 := bstep (se 1 (by rfl) ⟨1384643, by rfl⟩ : syracuseStep 1846191 = 2769287) B2769287
theorem B4156343 : Blo 1845624 4156343 := bstep (se 1 (by rfl) ⟨3117257, by rfl⟩ : syracuseStep 4156343 = 6234515) B6234515
theorem B1846215 : Blo 1845624 1846215 := bstep (se 1 (by rfl) ⟨1384661, by rfl⟩ : syracuseStep 1846215 = 2769323) B2769323
theorem B1846235 : Blo 1845624 1846235 := bstep (se 1 (by rfl) ⟨1384676, by rfl⟩ : syracuseStep 1846235 = 2769353) B2769353
theorem B6229007 : Blo 1845624 6229007 := bstep (se 1 (by rfl) ⟨4671755, by rfl⟩ : syracuseStep 6229007 = 9343511) B9343511
theorem B5917715 : Blo 1845624 5917715 := bstep (se 1 (by rfl) ⟨4438286, by rfl⟩ : syracuseStep 5917715 = 8876573) B8876573
theorem B1846311 : Blo 1845624 1846311 := bstep (se 1 (by rfl) ⟨1384733, by rfl⟩ : syracuseStep 1846311 = 2769467) B2769467
theorem B1846351 : Blo 1845624 1846351 := bstep (se 1 (by rfl) ⟨1384763, by rfl⟩ : syracuseStep 1846351 = 2769527) B2769527
theorem B1846367 : Blo 1845624 1846367 := bstep (se 1 (by rfl) ⟨1384775, by rfl⟩ : syracuseStep 1846367 = 2769551) B2769551
theorem B1846395 : Blo 1845624 1846395 := bstep (se 1 (by rfl) ⟨1384796, by rfl⟩ : syracuseStep 1846395 = 2769593) B2769593
theorem B9350315 : Blo 1845624 9350315 := bstep (se 1 (by rfl) ⟨7012736, by rfl⟩ : syracuseStep 9350315 = 14025473) B14025473
theorem B1846447 : Blo 1845624 1846447 := bstep (se 1 (by rfl) ⟨1384835, by rfl⟩ : syracuseStep 1846447 = 2769671) B2769671
theorem B107982017 : Blo 1845624 107982017 := bstep (se 2 (by rfl) ⟨40493256, by rfl⟩ : syracuseStep 107982017 = 80986513) B80986513
theorem B13307075 : Blo 1845624 13307075 := bstep (se 1 (by rfl) ⟨9980306, by rfl⟩ : syracuseStep 13307075 = 19960613) B19960613
theorem B8424643 : Blo 1845624 8424643 := bstep (se 1 (by rfl) ⟨6318482, by rfl⟩ : syracuseStep 8424643 = 12636965) B12636965
theorem B1846471 : Blo 1845624 1846471 := bstep (se 1 (by rfl) ⟨1384853, by rfl⟩ : syracuseStep 1846471 = 2769707) B2769707
theorem B1846491 : Blo 1845624 1846491 := bstep (se 1 (by rfl) ⟨1384868, by rfl⟩ : syracuseStep 1846491 = 2769737) B2769737
theorem B17738999 : Blo 1845624 17738999 := bstep (se 1 (by rfl) ⟨13304249, by rfl⟩ : syracuseStep 17738999 = 26608499) B26608499
theorem B3116279 : Blo 1845624 3116279 := bstep (se 1 (by rfl) ⟨2337209, by rfl⟩ : syracuseStep 3116279 = 4674419) B4674419
theorem B1846567 : Blo 1845624 1846567 := bstep (se 1 (by rfl) ⟨1384925, by rfl⟩ : syracuseStep 1846567 = 2769851) B2769851
theorem B1846607 : Blo 1845624 1846607 := bstep (se 1 (by rfl) ⟨1384955, by rfl⟩ : syracuseStep 1846607 = 2769911) B2769911
theorem B1846623 : Blo 1845624 1846623 := bstep (se 1 (by rfl) ⟨1384967, by rfl⟩ : syracuseStep 1846623 = 2769935) B2769935
theorem B1846651 : Blo 1845624 1846651 := bstep (se 1 (by rfl) ⟨1384988, by rfl⟩ : syracuseStep 1846651 = 2769977) B2769977
theorem B10522021 : Blo 1845624 10522021 := bstep (se 4 (by rfl) ⟨986439, by rfl⟩ : syracuseStep 10522021 = 1972879) B1972879
theorem B1846703 : Blo 1845624 1846703 := bstep (se 1 (by rfl) ⟨1385027, by rfl⟩ : syracuseStep 1846703 = 2770055) B2770055
theorem B1846727 : Blo 1845624 1846727 := bstep (se 1 (by rfl) ⟨1385045, by rfl⟩ : syracuseStep 1846727 = 2770091) B2770091
theorem B1846747 : Blo 1845624 1846747 := bstep (se 1 (by rfl) ⟨1385060, by rfl⟩ : syracuseStep 1846747 = 2770121) B2770121
theorem B4673011 : Blo 1845624 4673011 := bstep (se 1 (by rfl) ⟨3504758, by rfl⟩ : syracuseStep 4673011 = 7009517) B7009517
theorem B4156937 : Blo 1845624 4156937 := bstep (se 2 (by rfl) ⟨1558851, by rfl⟩ : syracuseStep 4156937 = 3117703) B3117703
theorem B1846823 : Blo 1845624 1846823 := bstep (se 1 (by rfl) ⟨1385117, by rfl⟩ : syracuseStep 1846823 = 2770235) B2770235
theorem B1846863 : Blo 1845624 1846863 := bstep (se 1 (by rfl) ⟨1385147, by rfl⟩ : syracuseStep 1846863 = 2770295) B2770295
theorem B3116623 : Blo 1845624 3116623 := bstep (se 1 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 3116623 = 4674935) B4674935
theorem B1846879 : Blo 1845624 1846879 := bstep (se 1 (by rfl) ⟨1385159, by rfl⟩ : syracuseStep 1846879 = 2770319) B2770319
theorem B6229601 : Blo 1845624 6229601 := bstep (se 2 (by rfl) ⟨2336100, by rfl⟩ : syracuseStep 6229601 = 4672201) B4672201
theorem B1846907 : Blo 1845624 1846907 := bstep (se 1 (by rfl) ⟨1385180, by rfl⟩ : syracuseStep 1846907 = 2770361) B2770361
theorem B9350801 : Blo 1845624 9350801 := bstep (se 2 (by rfl) ⟨3506550, by rfl⟩ : syracuseStep 9350801 = 7013101) B7013101
theorem B1846959 : Blo 1845624 1846959 := bstep (se 1 (by rfl) ⟨1385219, by rfl⟩ : syracuseStep 1846959 = 2770439) B2770439
theorem B9981629 : Blo 1845624 9981629 := bstep (se 3 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 9981629 = 3743111) B3743111
theorem B1846983 : Blo 1845624 1846983 := bstep (se 1 (by rfl) ⟨1385237, by rfl⟩ : syracuseStep 1846983 = 2770475) B2770475
theorem B6655699 : Blo 1845624 6655699 := bstep (se 1 (by rfl) ⟨4991774, by rfl⟩ : syracuseStep 6655699 = 9983549) B9983549
theorem B1847003 : Blo 1845624 1847003 := bstep (se 1 (by rfl) ⟨1385252, by rfl⟩ : syracuseStep 1847003 = 2770505) B2770505
theorem B7008029 : Blo 1845624 7008029 := bstep (se 3 (by rfl) ⟨1314005, by rfl⟩ : syracuseStep 7008029 = 2628011) B2628011
theorem B1847079 : Blo 1845624 1847079 := bstep (se 1 (by rfl) ⟨1385309, by rfl⟩ : syracuseStep 1847079 = 2770619) B2770619
theorem B3116873 : Blo 1845624 3116873 := bstep (se 2 (by rfl) ⟨1168827, by rfl⟩ : syracuseStep 3116873 = 2337655) B2337655
theorem B1847119 : Blo 1845624 1847119 := bstep (se 1 (by rfl) ⟨1385339, by rfl⟩ : syracuseStep 1847119 = 2770679) B2770679
theorem B2076511 : Blo 1845624 2076511 := bstep (se 1 (by rfl) ⟨1557383, by rfl⟩ : syracuseStep 2076511 = 3114767) B3114767
theorem B1847135 : Blo 1845624 1847135 := bstep (se 1 (by rfl) ⟨1385351, by rfl⟩ : syracuseStep 1847135 = 2770703) B2770703
theorem B4869983 : Blo 1845624 4869983 := bstep (se 1 (by rfl) ⟨3652487, by rfl⟩ : syracuseStep 4869983 = 7304975) B7304975
theorem B1847163 : Blo 1845624 1847163 := bstep (se 1 (by rfl) ⟨1385372, by rfl⟩ : syracuseStep 1847163 = 2770745) B2770745
theorem B7999393 : Blo 1845624 7999393 := bstep (se 2 (by rfl) ⟨2999772, by rfl⟩ : syracuseStep 7999393 = 5999545) B5999545
theorem B1847215 : Blo 1845624 1847215 := bstep (se 1 (by rfl) ⟨1385411, by rfl⟩ : syracuseStep 1847215 = 2770823) B2770823
theorem B1847239 : Blo 1845624 1847239 := bstep (se 1 (by rfl) ⟨1385429, by rfl⟩ : syracuseStep 1847239 = 2770859) B2770859
theorem B1847259 : Blo 1845624 1847259 := bstep (se 1 (by rfl) ⟨1385444, by rfl⟩ : syracuseStep 1847259 = 2770889) B2770889
theorem B1847335 : Blo 1845624 1847335 := bstep (se 1 (by rfl) ⟨1385501, by rfl⟩ : syracuseStep 1847335 = 2771003) B2771003
theorem B11227193 : Blo 1845624 11227193 := bstep (se 2 (by rfl) ⟨4210197, by rfl⟩ : syracuseStep 11227193 = 8420395) B8420395
theorem B1847375 : Blo 1845624 1847375 := bstep (se 1 (by rfl) ⟨1385531, by rfl⟩ : syracuseStep 1847375 = 2771063) B2771063
theorem B1847391 : Blo 1845624 1847391 := bstep (se 1 (by rfl) ⟨1385543, by rfl⟩ : syracuseStep 1847391 = 2771087) B2771087
theorem B1847419 : Blo 1845624 1847419 := bstep (se 1 (by rfl) ⟨1385564, by rfl⟩ : syracuseStep 1847419 = 2771129) B2771129
theorem B1847471 : Blo 1845624 1847471 := bstep (se 1 (by rfl) ⟨1385603, by rfl⟩ : syracuseStep 1847471 = 2771207) B2771207
theorem B2076871 : Blo 1845624 2076871 := bstep (se 1 (by rfl) ⟨1557653, by rfl⟩ : syracuseStep 2076871 = 3115307) B3115307
theorem B1847495 : Blo 1845624 1847495 := bstep (se 1 (by rfl) ⟨1385621, by rfl⟩ : syracuseStep 1847495 = 2771243) B2771243
theorem B1847515 : Blo 1845624 1847515 := bstep (se 1 (by rfl) ⟨1385636, by rfl⟩ : syracuseStep 1847515 = 2771273) B2771273
theorem B3117305 : Blo 1845624 3117305 := bstep (se 2 (by rfl) ⟨1168989, by rfl⟩ : syracuseStep 3117305 = 2337979) B2337979
theorem B1847591 : Blo 1845624 1847591 := bstep (se 1 (by rfl) ⟨1385693, by rfl⟩ : syracuseStep 1847591 = 2771387) B2771387
theorem B23081291 : Blo 1845624 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B5058941 : Blo 1845624 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B4993409 : Blo 1845624 4993409 := bstep (se 2 (by rfl) ⟨1872528, by rfl⟩ : syracuseStep 4993409 = 3745057) B3745057
theorem B3117487 : Blo 1845624 3117487 := bstep (se 1 (by rfl) ⟨2338115, by rfl⟩ : syracuseStep 3117487 = 4676231) B4676231
theorem B7008713 : Blo 1845624 7008713 := bstep (se 2 (by rfl) ⟨2628267, by rfl⟩ : syracuseStep 7008713 = 5256535) B5256535
theorem B3117575 : Blo 1845624 3117575 := bstep (se 1 (by rfl) ⟨2338181, by rfl⟩ : syracuseStep 3117575 = 4676363) B4676363
theorem B3944999 : Blo 1845624 3944999 := bstep (se 1 (by rfl) ⟨2958749, by rfl⟩ : syracuseStep 3944999 = 5917499) B5917499
theorem B4674145 : Blo 1845624 4674145 := bstep (se 2 (by rfl) ⟨1752804, by rfl⟩ : syracuseStep 4674145 = 3505609) B3505609
theorem B9343673 : Blo 1845624 9343673 := bstep (se 2 (by rfl) ⟨3503877, by rfl⟩ : syracuseStep 9343673 = 7007755) B7007755
theorem B7303895 : Blo 1845624 7303895 := bstep (se 1 (by rfl) ⟨5477921, by rfl⟩ : syracuseStep 7303895 = 10955843) B10955843
theorem B7009199 : Blo 1845624 7009199 := bstep (se 1 (by rfl) ⟨5256899, by rfl⟩ : syracuseStep 7009199 = 10513799) B10513799
theorem B6231059 : Blo 1845624 6231059 := bstep (se 1 (by rfl) ⟨4673294, by rfl⟩ : syracuseStep 6231059 = 9346589) B9346589
theorem B2077735 : Blo 1845624 2077735 := bstep (se 1 (by rfl) ⟨1558301, by rfl⟩ : syracuseStep 2077735 = 3116603) B3116603
theorem B11998259 : Blo 1845624 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B31986755 : Blo 1845624 31986755 := bstep (se 1 (by rfl) ⟨23990066, by rfl⟩ : syracuseStep 31986755 = 47980133) B47980133
theorem B17749145 : Blo 1845624 17749145 := bstep (se 2 (by rfl) ⟨6655929, by rfl⟩ : syracuseStep 17749145 = 13311859) B13311859
theorem B35493065 : Blo 1845624 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B6231383 : Blo 1845624 6231383 := bstep (se 1 (by rfl) ⟨4673537, by rfl⟩ : syracuseStep 6231383 = 9347075) B9347075
theorem B3552607 : Blo 1845624 3552607 := bstep (se 1 (by rfl) ⟨2664455, by rfl⟩ : syracuseStep 3552607 = 5328911) B5328911
theorem B3552731 : Blo 1845624 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B9475571 : Blo 1845624 9475571 := bstep (se 1 (by rfl) ⟨7106678, by rfl⟩ : syracuseStep 9475571 = 14213357) B14213357
theorem B6657545 : Blo 1845624 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B4675097 : Blo 1845624 4675097 := bstep (se 2 (by rfl) ⟨1753161, by rfl⟩ : syracuseStep 4675097 = 3506323) B3506323
theorem B10516007 : Blo 1845624 10516007 := bstep (se 1 (by rfl) ⟨7887005, by rfl⟩ : syracuseStep 10516007 = 15774011) B15774011
theorem B7886459 : Blo 1845624 7886459 := bstep (se 1 (by rfl) ⟨5914844, by rfl⟩ : syracuseStep 7886459 = 11829689) B11829689
theorem B7010003 : Blo 1845624 7010003 := bstep (se 1 (by rfl) ⟨5257502, by rfl⟩ : syracuseStep 7010003 = 10515005) B10515005
theorem B10516189 : Blo 1845624 10516189 := bstep (se 3 (by rfl) ⟨1971785, by rfl⟩ : syracuseStep 10516189 = 3943571) B3943571
theorem B9353069 : Blo 1845624 9353069 := bstep (se 3 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 9353069 = 3507401) B3507401
theorem B9353231 : Blo 1845624 9353231 := bstep (se 1 (by rfl) ⟨7014923, by rfl⟩ : syracuseStep 9353231 = 14029847) B14029847
theorem B4675603 : Blo 1845624 4675603 := bstep (se 1 (by rfl) ⟨3506702, by rfl⟩ : syracuseStep 4675603 = 7013405) B7013405
theorem B3291233 : Blo 1845624 3291233 := bstep (se 2 (by rfl) ⟨1234212, by rfl⟩ : syracuseStep 3291233 = 2468425) B2468425
theorem B13310219 : Blo 1845624 13310219 := bstep (se 1 (by rfl) ⟨9982664, by rfl⟩ : syracuseStep 13310219 = 19965329) B19965329
theorem B23976323 : Blo 1845624 23976323 := bstep (se 1 (by rfl) ⟨17982242, by rfl⟩ : syracuseStep 23976323 = 35964485) B35964485
theorem B6232463 : Blo 1845624 6232463 := bstep (se 1 (by rfl) ⟨4674347, by rfl⟩ : syracuseStep 6232463 = 9348695) B9348695
theorem B2218423 : Blo 1845624 2218423 := bstep (se 1 (by rfl) ⟨1663817, by rfl⟩ : syracuseStep 2218423 = 3327635) B3327635
theorem B21027275 : Blo 1845624 21027275 := bstep (se 1 (by rfl) ⟨15770456, by rfl⟩ : syracuseStep 21027275 = 31540913) B31540913
theorem B7485961 : Blo 1845624 7485961 := bstep (se 2 (by rfl) ⟨2807235, by rfl⟩ : syracuseStep 7485961 = 5614471) B5614471
theorem B34134605 : Blo 1845624 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B31980109 : Blo 1845624 31980109 := bstep (se 3 (by rfl) ⟨5996270, by rfl⟩ : syracuseStep 31980109 = 11992541) B11992541
theorem B5257867 : Blo 1845624 5257867 := bstep (se 1 (by rfl) ⟨3943400, by rfl⟩ : syracuseStep 5257867 = 7886801) B7886801
theorem B6232787 : Blo 1845624 6232787 := bstep (se 1 (by rfl) ⟨4674590, by rfl⟩ : syracuseStep 6232787 = 9349181) B9349181
theorem B4438739 : Blo 1845624 4438739 := bstep (se 1 (by rfl) ⟨3329054, by rfl⟩ : syracuseStep 4438739 = 6658109) B6658109
theorem B7887689 : Blo 1845624 7887689 := bstep (se 2 (by rfl) ⟨2957883, by rfl⟩ : syracuseStep 7887689 = 5915767) B5915767
theorem B4209515 : Blo 1845624 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B5995439 : Blo 1845624 5995439 := bstep (se 1 (by rfl) ⟨4496579, by rfl⟩ : syracuseStep 5995439 = 8993159) B8993159
theorem B35478607 : Blo 1845624 35478607 := bstep (se 1 (by rfl) ⟨26608955, by rfl⟩ : syracuseStep 35478607 = 53217911) B53217911
theorem B4676687 : Blo 1845624 4676687 := bstep (se 1 (by rfl) ⟨3507515, by rfl⟩ : syracuseStep 4676687 = 7015031) B7015031
theorem B3505351 : Blo 1845624 3505351 := bstep (se 1 (by rfl) ⟨2629013, by rfl⟩ : syracuseStep 3505351 = 5258027) B5258027
theorem B8871191 : Blo 1845624 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B2956807 : Blo 1845624 2956807 := bstep (se 1 (by rfl) ⟨2217605, by rfl⟩ : syracuseStep 2956807 = 4435211) B4435211
theorem B22453847 : Blo 1845624 22453847 := bstep (se 1 (by rfl) ⟨16840385, by rfl⟩ : syracuseStep 22453847 = 33680771) B33680771
theorem B2768507 : Blo 1845624 2768507 := bstep (se 1 (by rfl) ⟨2076380, by rfl⟩ : syracuseStep 2768507 = 4152761) B4152761
theorem B4153031 : Blo 1845624 4153031 := bstep (se 1 (by rfl) ⟨3114773, by rfl⟩ : syracuseStep 4153031 = 6229547) B6229547
theorem B2768633 : Blo 1845624 2768633 := bstep (se 2 (by rfl) ⟨1038237, by rfl⟩ : syracuseStep 2768633 = 2076475) B2076475
theorem B3505913 : Blo 1845624 3505913 := bstep (se 2 (by rfl) ⟨1314717, by rfl⟩ : syracuseStep 3505913 = 2629435) B2629435
theorem B2768735 : Blo 1845624 2768735 := bstep (se 1 (by rfl) ⟨2076551, by rfl⟩ : syracuseStep 2768735 = 4153103) B4153103
theorem B2768747 : Blo 1845624 2768747 := bstep (se 1 (by rfl) ⟨2076560, by rfl⟩ : syracuseStep 2768747 = 4153121) B4153121
theorem B22454135 : Blo 1845624 22454135 := bstep (se 1 (by rfl) ⟨16840601, by rfl⟩ : syracuseStep 22454135 = 33681203) B33681203
theorem B6233975 : Blo 1845624 6233975 := bstep (se 1 (by rfl) ⟨4675481, by rfl⟩ : syracuseStep 6233975 = 9350963) B9350963
theorem B2957231 : Blo 1845624 2957231 := bstep (se 1 (by rfl) ⟨2217923, by rfl⟩ : syracuseStep 2957231 = 4435847) B4435847
theorem B3506095 : Blo 1845624 3506095 := bstep (se 1 (by rfl) ⟨2629571, by rfl⟩ : syracuseStep 3506095 = 5259143) B5259143
theorem B6234137 : Blo 1845624 6234137 := bstep (se 2 (by rfl) ⟨2337801, by rfl⟩ : syracuseStep 6234137 = 4675603) B4675603
theorem B15769637 : Blo 1845624 15769637 := bstep (se 4 (by rfl) ⟨1478403, by rfl⟩ : syracuseStep 15769637 = 2956807) B2956807
theorem B13304017 : Blo 1845624 13304017 := bstep (se 2 (by rfl) ⟨4989006, by rfl⟩ : syracuseStep 13304017 = 9978013) B9978013
theorem B2769161 : Blo 1845624 2769161 := bstep (se 2 (by rfl) ⟨1038435, by rfl⟩ : syracuseStep 2769161 = 2076871) B2076871
theorem B2769263 : Blo 1845624 2769263 := bstep (se 1 (by rfl) ⟨2076947, by rfl⟩ : syracuseStep 2769263 = 4153895) B4153895
theorem B2629999 : Blo 1845624 2629999 := bstep (se 1 (by rfl) ⟨1972499, by rfl⟩ : syracuseStep 2629999 = 3944999) B3944999
theorem B56869283 : Blo 1845624 56869283 := bstep (se 1 (by rfl) ⟨42651962, by rfl⟩ : syracuseStep 56869283 = 85303925) B85303925
theorem B2769479 : Blo 1845624 2769479 := bstep (se 1 (by rfl) ⟨2077109, by rfl⟩ : syracuseStep 2769479 = 4154219) B4154219
theorem B2957897 : Blo 1845624 2957897 := bstep (se 2 (by rfl) ⟨1109211, by rfl⟩ : syracuseStep 2957897 = 2218423) B2218423
theorem B2769515 : Blo 1845624 2769515 := bstep (se 1 (by rfl) ⟨2077136, by rfl⟩ : syracuseStep 2769515 = 4154273) B4154273
theorem B3506809 : Blo 1845624 3506809 := bstep (se 2 (by rfl) ⟨1315053, by rfl⟩ : syracuseStep 3506809 = 2630107) B2630107
theorem B32424583 : Blo 1845624 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B4154039 : Blo 1845624 4154039 := bstep (se 1 (by rfl) ⟨3115529, by rfl⟩ : syracuseStep 4154039 = 6231059) B6231059
theorem B21324503 : Blo 1845624 21324503 := bstep (se 1 (by rfl) ⟨15993377, by rfl⟩ : syracuseStep 21324503 = 31986755) B31986755
theorem B7013087 : Blo 1845624 7013087 := bstep (se 1 (by rfl) ⟨5259815, by rfl⟩ : syracuseStep 7013087 = 10519631) B10519631
theorem B42640145 : Blo 1845624 42640145 := bstep (se 2 (by rfl) ⟨15990054, by rfl⟩ : syracuseStep 42640145 = 31980109) B31980109
theorem B2769743 : Blo 1845624 2769743 := bstep (se 1 (by rfl) ⟨2077307, by rfl⟩ : syracuseStep 2769743 = 4154615) B4154615
theorem B4154255 : Blo 1845624 4154255 := bstep (se 1 (by rfl) ⟨3115691, by rfl⟩ : syracuseStep 4154255 = 6231383) B6231383
theorem B1999771 : Blo 1845624 1999771 := bstep (se 1 (by rfl) ⟨1499828, by rfl⟩ : syracuseStep 1999771 = 2999657) B2999657
theorem B8872865 : Blo 1845624 8872865 := bstep (se 2 (by rfl) ⟨3327324, by rfl⟩ : syracuseStep 8872865 = 6654649) B6654649
theorem B2368487 : Blo 1845624 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B6317047 : Blo 1845624 6317047 := bstep (se 1 (by rfl) ⟨4737785, by rfl⟩ : syracuseStep 6317047 = 9475571) B9475571
theorem B35497061 : Blo 1845624 35497061 := bstep (se 4 (by rfl) ⟨3327849, by rfl⟩ : syracuseStep 35497061 = 6655699) B6655699
theorem B2770139 : Blo 1845624 2770139 := bstep (se 1 (by rfl) ⟨2077604, by rfl⟩ : syracuseStep 2770139 = 4155209) B4155209
theorem B6235379 : Blo 1845624 6235379 := bstep (se 1 (by rfl) ⟨4676534, by rfl⟩ : syracuseStep 6235379 = 9353069) B9353069
theorem B6653279 : Blo 1845624 6653279 := bstep (se 1 (by rfl) ⟨4989959, by rfl⟩ : syracuseStep 6653279 = 9979919) B9979919
theorem B6235487 : Blo 1845624 6235487 := bstep (se 1 (by rfl) ⟨4676615, by rfl⟩ : syracuseStep 6235487 = 9353231) B9353231
theorem B3507553 : Blo 1845624 3507553 := bstep (se 2 (by rfl) ⟨1315332, by rfl⟩ : syracuseStep 3507553 = 2630665) B2630665
theorem B2770313 : Blo 1845624 2770313 := bstep (se 2 (by rfl) ⟨1038867, by rfl⟩ : syracuseStep 2770313 = 2077735) B2077735
theorem B8873479 : Blo 1845624 8873479 := bstep (se 1 (by rfl) ⟨6655109, by rfl⟩ : syracuseStep 8873479 = 13310219) B13310219
theorem B13305401 : Blo 1845624 13305401 := bstep (se 2 (by rfl) ⟨4989525, by rfl⟩ : syracuseStep 13305401 = 9979051) B9979051
theorem B15984215 : Blo 1845624 15984215 := bstep (se 1 (by rfl) ⟨11988161, by rfl⟩ : syracuseStep 15984215 = 23976323) B23976323
theorem B11232857 : Blo 1845624 11232857 := bstep (se 2 (by rfl) ⟨4212321, by rfl⟩ : syracuseStep 11232857 = 8424643) B8424643
theorem B4154975 : Blo 1845624 4154975 := bstep (se 1 (by rfl) ⟨3116231, by rfl⟩ : syracuseStep 4154975 = 6232463) B6232463
theorem B14018183 : Blo 1845624 14018183 := bstep (se 1 (by rfl) ⟨10513637, by rfl⟩ : syracuseStep 14018183 = 21027275) B21027275
theorem B2770667 : Blo 1845624 2770667 := bstep (se 1 (by rfl) ⟨2078000, by rfl⟩ : syracuseStep 2770667 = 4156001) B4156001
theorem B4736809 : Blo 1845624 4736809 := bstep (se 2 (by rfl) ⟨1776303, by rfl⟩ : syracuseStep 4736809 = 3552607) B3552607
theorem B4155191 : Blo 1845624 4155191 := bstep (se 1 (by rfl) ⟨3116393, by rfl⟩ : syracuseStep 4155191 = 6232787) B6232787
theorem B2770895 : Blo 1845624 2770895 := bstep (se 1 (by rfl) ⟨2078171, by rfl⟩ : syracuseStep 2770895 = 4156343) B4156343
theorem B28428365 : Blo 1845624 28428365 := bstep (se 3 (by rfl) ⟨5330318, by rfl⟩ : syracuseStep 28428365 = 10660637) B10660637
theorem B4155497 : Blo 1845624 4155497 := bstep (se 2 (by rfl) ⟨1558311, by rfl⟩ : syracuseStep 4155497 = 3116623) B3116623
theorem B3115273 : Blo 1845624 3115273 := bstep (se 2 (by rfl) ⟨1168227, by rfl⟩ : syracuseStep 3115273 = 2336455) B2336455
theorem B2771291 : Blo 1845624 2771291 := bstep (se 1 (by rfl) ⟨2078468, by rfl⟩ : syracuseStep 2771291 = 4156937) B4156937
theorem B14969231 : Blo 1845624 14969231 := bstep (se 1 (by rfl) ⟨11226923, by rfl⟩ : syracuseStep 14969231 = 22453847) B22453847
theorem B1845671 : Blo 1845624 1845671 := bstep (se 1 (by rfl) ⟨1384253, by rfl⟩ : syracuseStep 1845671 = 2768507) B2768507
theorem B6654419 : Blo 1845624 6654419 := bstep (se 1 (by rfl) ⟨4990814, by rfl⟩ : syracuseStep 6654419 = 9981629) B9981629
theorem B1845755 : Blo 1845624 1845755 := bstep (se 1 (by rfl) ⟨1384316, by rfl⟩ : syracuseStep 1845755 = 2768633) B2768633
theorem B2337275 : Blo 1845624 2337275 := bstep (se 1 (by rfl) ⟨1752956, by rfl⟩ : syracuseStep 2337275 = 3505913) B3505913
theorem B4672019 : Blo 1845624 4672019 := bstep (se 1 (by rfl) ⟨3504014, by rfl⟩ : syracuseStep 4672019 = 7008029) B7008029
theorem B1845823 : Blo 1845624 1845823 := bstep (se 1 (by rfl) ⟨1384367, by rfl⟩ : syracuseStep 1845823 = 2768735) B2768735
theorem B3246655 : Blo 1845624 3246655 := bstep (se 1 (by rfl) ⟨2434991, by rfl⟩ : syracuseStep 3246655 = 4869983) B4869983
theorem B1845831 : Blo 1845624 1845831 := bstep (se 1 (by rfl) ⟨1384373, by rfl⟩ : syracuseStep 1845831 = 2768747) B2768747
theorem B14969423 : Blo 1845624 14969423 := bstep (se 1 (by rfl) ⟨11227067, by rfl⟩ : syracuseStep 14969423 = 22454135) B22454135
theorem B4155983 : Blo 1845624 4155983 := bstep (se 1 (by rfl) ⟨3116987, by rfl⟩ : syracuseStep 4155983 = 6233975) B6233975
theorem B1845983 : Blo 1845624 1845983 := bstep (se 1 (by rfl) ⟨1384487, by rfl⟩ : syracuseStep 1845983 = 2768975) B2768975
theorem B4156127 : Blo 1845624 4156127 := bstep (se 1 (by rfl) ⟨3117095, by rfl⟩ : syracuseStep 4156127 = 6234191) B6234191
theorem B1846063 : Blo 1845624 1846063 := bstep (se 1 (by rfl) ⟨1384547, by rfl⟩ : syracuseStep 1846063 = 2769095) B2769095
theorem B15387527 : Blo 1845624 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B1846171 : Blo 1845624 1846171 := bstep (se 1 (by rfl) ⟨1384628, by rfl⟩ : syracuseStep 1846171 = 2769257) B2769257
theorem B3328939 : Blo 1845624 3328939 := bstep (se 1 (by rfl) ⟨2496704, by rfl⟩ : syracuseStep 3328939 = 4993409) B4993409
theorem B8776621 : Blo 1845624 8776621 := bstep (se 3 (by rfl) ⟨1645616, by rfl⟩ : syracuseStep 8776621 = 3291233) B3291233
theorem B1846223 : Blo 1845624 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B4672475 : Blo 1845624 4672475 := bstep (se 1 (by rfl) ⟨3504356, by rfl⟩ : syracuseStep 4672475 = 7008713) B7008713
theorem B4156379 : Blo 1845624 4156379 := bstep (se 1 (by rfl) ⟨3117284, by rfl⟩ : syracuseStep 4156379 = 6234569) B6234569
theorem B1846247 : Blo 1845624 1846247 := bstep (se 1 (by rfl) ⟨1384685, by rfl⟩ : syracuseStep 1846247 = 2769371) B2769371
theorem B6229115 : Blo 1845624 6229115 := bstep (se 1 (by rfl) ⟨4671836, by rfl⟩ : syracuseStep 6229115 = 9343673) B9343673
theorem B10513547 : Blo 1845624 10513547 := bstep (se 1 (by rfl) ⟨7885160, by rfl⟩ : syracuseStep 10513547 = 15770321) B15770321
theorem B4869263 : Blo 1845624 4869263 := bstep (se 1 (by rfl) ⟨3651947, by rfl⟩ : syracuseStep 4869263 = 7303895) B7303895
theorem B4156559 : Blo 1845624 4156559 := bstep (se 1 (by rfl) ⟨3117419, by rfl⟩ : syracuseStep 4156559 = 6234839) B6234839
theorem B3943657 : Blo 1845624 3943657 := bstep (se 2 (by rfl) ⟨1478871, by rfl⟩ : syracuseStep 3943657 = 2957743) B2957743
theorem B4156649 : Blo 1845624 4156649 := bstep (se 2 (by rfl) ⟨1558743, by rfl⟩ : syracuseStep 4156649 = 3117487) B3117487
theorem B4435231 : Blo 1845624 4435231 := bstep (se 1 (by rfl) ⟨3326423, by rfl⟩ : syracuseStep 4435231 = 6652847) B6652847
theorem B4672799 : Blo 1845624 4672799 := bstep (se 1 (by rfl) ⟨3504599, by rfl⟩ : syracuseStep 4672799 = 7009199) B7009199
theorem B1846559 : Blo 1845624 1846559 := bstep (se 1 (by rfl) ⟨1384919, by rfl⟩ : syracuseStep 1846559 = 2769839) B2769839
theorem B4156703 : Blo 1845624 4156703 := bstep (se 1 (by rfl) ⟨3117527, by rfl⟩ : syracuseStep 4156703 = 6235055) B6235055
theorem B8875325 : Blo 1845624 8875325 := bstep (se 3 (by rfl) ⟨1664123, by rfl⟩ : syracuseStep 8875325 = 3328247) B3328247
theorem B1846619 : Blo 1845624 1846619 := bstep (se 1 (by rfl) ⟨1384964, by rfl⟩ : syracuseStep 1846619 = 2769929) B2769929
theorem B9981281 : Blo 1845624 9981281 := bstep (se 2 (by rfl) ⟨3742980, by rfl⟩ : syracuseStep 9981281 = 7485961) B7485961
theorem B1846639 : Blo 1845624 1846639 := bstep (se 1 (by rfl) ⟨1384979, by rfl⟩ : syracuseStep 1846639 = 2769959) B2769959
theorem B7998839 : Blo 1845624 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B6229385 : Blo 1845624 6229385 := bstep (se 2 (by rfl) ⟨2336019, by rfl⟩ : syracuseStep 6229385 = 4672039) B4672039
theorem B1846695 : Blo 1845624 1846695 := bstep (se 1 (by rfl) ⟨1385021, by rfl⟩ : syracuseStep 1846695 = 2770043) B2770043
theorem B2338247 : Blo 1845624 2338247 := bstep (se 1 (by rfl) ⟨1753685, by rfl⟩ : syracuseStep 2338247 = 3507371) B3507371
theorem B23662043 : Blo 1845624 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1846779 : Blo 1845624 1846779 := bstep (se 1 (by rfl) ⟨1385084, by rfl⟩ : syracuseStep 1846779 = 2770169) B2770169
theorem B1846847 : Blo 1845624 1846847 := bstep (se 1 (by rfl) ⟨1385135, by rfl⟩ : syracuseStep 1846847 = 2770271) B2770271
theorem B1846855 : Blo 1845624 1846855 := bstep (se 1 (by rfl) ⟨1385141, by rfl⟩ : syracuseStep 1846855 = 2770283) B2770283
theorem B2338399 : Blo 1845624 2338399 := bstep (se 1 (by rfl) ⟨1753799, by rfl⟩ : syracuseStep 2338399 = 3507599) B3507599
theorem B59928173 : Blo 1845624 59928173 := bstep (se 3 (by rfl) ⟨11236532, by rfl⟩ : syracuseStep 59928173 = 22473065) B22473065
theorem B3116731 : Blo 1845624 3116731 := bstep (se 1 (by rfl) ⟨2337548, by rfl⟩ : syracuseStep 3116731 = 4675097) B4675097
theorem B1847007 : Blo 1845624 1847007 := bstep (se 1 (by rfl) ⟨1385255, by rfl⟩ : syracuseStep 1847007 = 2770511) B2770511
theorem B1847087 : Blo 1845624 1847087 := bstep (se 1 (by rfl) ⟨1385315, by rfl⟩ : syracuseStep 1847087 = 2770631) B2770631
theorem B13496111 : Blo 1845624 13496111 := bstep (se 1 (by rfl) ⟨10122083, by rfl⟩ : syracuseStep 13496111 = 20244167) B20244167
theorem B4673335 : Blo 1845624 4673335 := bstep (se 1 (by rfl) ⟨3505001, by rfl⟩ : syracuseStep 4673335 = 7010003) B7010003
theorem B6229817 : Blo 1845624 6229817 := bstep (se 2 (by rfl) ⟨2336181, by rfl⟩ : syracuseStep 6229817 = 4672363) B4672363
theorem B6655873 : Blo 1845624 6655873 := bstep (se 2 (by rfl) ⟨2495952, by rfl⟩ : syracuseStep 6655873 = 4991905) B4991905
theorem B1847195 : Blo 1845624 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B1847247 : Blo 1845624 1847247 := bstep (se 1 (by rfl) ⟨1385435, by rfl⟩ : syracuseStep 1847247 = 2770871) B2770871
theorem B1847271 : Blo 1845624 1847271 := bstep (se 1 (by rfl) ⟨1385453, by rfl⟩ : syracuseStep 1847271 = 2770907) B2770907
theorem B47304809 : Blo 1845624 47304809 := bstep (se 2 (by rfl) ⟨17739303, by rfl⟩ : syracuseStep 47304809 = 35478607) B35478607
theorem B4673801 : Blo 1845624 4673801 := bstep (se 2 (by rfl) ⟨1752675, by rfl⟩ : syracuseStep 4673801 = 3505351) B3505351
theorem B1847583 : Blo 1845624 1847583 := bstep (se 1 (by rfl) ⟨1385687, by rfl⟩ : syracuseStep 1847583 = 2771375) B2771375
theorem B2077051 : Blo 1845624 2077051 := bstep (se 1 (by rfl) ⟨1557788, by rfl⟩ : syracuseStep 2077051 = 3115577) B3115577
theorem B4993463 : Blo 1845624 4993463 := bstep (se 1 (by rfl) ⟨3745097, by rfl⟩ : syracuseStep 4993463 = 7490195) B7490195
theorem B14029361 : Blo 1845624 14029361 := bstep (se 2 (by rfl) ⟨5261010, by rfl⟩ : syracuseStep 14029361 = 10522021) B10522021
theorem B2806343 : Blo 1845624 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B6230681 : Blo 1845624 6230681 := bstep (se 2 (by rfl) ⟨2336505, by rfl⟩ : syracuseStep 6230681 = 4673011) B4673011
theorem B3945143 : Blo 1845624 3945143 := bstep (se 1 (by rfl) ⟨2958857, by rfl⟩ : syracuseStep 3945143 = 5917715) B5917715
theorem B3117791 : Blo 1845624 3117791 := bstep (se 1 (by rfl) ⟨2338343, by rfl⟩ : syracuseStep 3117791 = 4676687) B4676687
theorem B71988011 : Blo 1845624 71988011 := bstep (se 1 (by rfl) ⟨53991008, by rfl⟩ : syracuseStep 71988011 = 107982017) B107982017
theorem B11825999 : Blo 1845624 11825999 := bstep (se 1 (by rfl) ⟨8869499, by rfl⟩ : syracuseStep 11825999 = 17738999) B17738999
theorem B2077519 : Blo 1845624 2077519 := bstep (se 1 (by rfl) ⟨1558139, by rfl⟩ : syracuseStep 2077519 = 3116279) B3116279
theorem B9352097 : Blo 1845624 9352097 := bstep (se 2 (by rfl) ⟨3507036, by rfl⟩ : syracuseStep 9352097 = 7014073) B7014073
theorem B14021585 : Blo 1845624 14021585 := bstep (se 2 (by rfl) ⟨5258094, by rfl⟩ : syracuseStep 14021585 = 10516189) B10516189
theorem B2077915 : Blo 1845624 2077915 := bstep (se 1 (by rfl) ⟨1558436, by rfl⟩ : syracuseStep 2077915 = 3116873) B3116873
theorem B4674793 : Blo 1845624 4674793 := bstep (se 2 (by rfl) ⟨1753047, by rfl⟩ : syracuseStep 4674793 = 3506095) B3506095
theorem B1971487 : Blo 1845624 1971487 := bstep (se 1 (by rfl) ⟨1478615, by rfl⟩ : syracuseStep 1971487 = 2957231) B2957231
theorem B7484795 : Blo 1845624 7484795 := bstep (se 1 (by rfl) ⟨5613596, by rfl⟩ : syracuseStep 7484795 = 11227193) B11227193
theorem B4674955 : Blo 1845624 4674955 := bstep (se 1 (by rfl) ⟨3506216, by rfl⟩ : syracuseStep 4674955 = 7012433) B7012433
theorem B2078203 : Blo 1845624 2078203 := bstep (se 1 (by rfl) ⟨1558652, by rfl⟩ : syracuseStep 2078203 = 3117305) B3117305
theorem B2078383 : Blo 1845624 2078383 := bstep (se 1 (by rfl) ⟨1558787, by rfl⟩ : syracuseStep 2078383 = 3117575) B3117575
theorem B4675259 : Blo 1845624 4675259 := bstep (se 1 (by rfl) ⟨3506444, by rfl⟩ : syracuseStep 4675259 = 7012889) B7012889
theorem B47331053 : Blo 1845624 47331053 := bstep (se 3 (by rfl) ⟨8874572, by rfl⟩ : syracuseStep 47331053 = 17749145) B17749145
theorem B52664327 : Blo 1845624 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B6232193 : Blo 1845624 6232193 := bstep (se 2 (by rfl) ⟨2337072, by rfl⟩ : syracuseStep 6232193 = 4674145) B4674145
theorem B7010489 : Blo 1845624 7010489 := bstep (se 2 (by rfl) ⟨2628933, by rfl⟩ : syracuseStep 7010489 = 5257867) B5257867
theorem B2218279 : Blo 1845624 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B13490509 : Blo 1845624 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B4438363 : Blo 1845624 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B7010671 : Blo 1845624 7010671 := bstep (se 1 (by rfl) ⟨5258003, by rfl⟩ : syracuseStep 7010671 = 10516007) B10516007
theorem B5257639 : Blo 1845624 5257639 := bstep (se 1 (by rfl) ⟨3943229, by rfl⟩ : syracuseStep 5257639 = 7886459) B7886459
theorem B6232571 : Blo 1845624 6232571 := bstep (se 1 (by rfl) ⟨4674428, by rfl⟩ : syracuseStep 6232571 = 9348857) B9348857
theorem B8870575 : Blo 1845624 8870575 := bstep (se 1 (by rfl) ⟨6652931, by rfl⟩ : syracuseStep 8870575 = 13305863) B13305863
theorem B75799439 : Blo 1845624 75799439 := bstep (se 1 (by rfl) ⟨56849579, by rfl⟩ : syracuseStep 75799439 = 113699159) B113699159
theorem B6233003 : Blo 1845624 6233003 := bstep (se 1 (by rfl) ⟨4674752, by rfl⟩ : syracuseStep 6233003 = 9349505) B9349505
theorem B22756403 : Blo 1845624 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B5258459 : Blo 1845624 5258459 := bstep (se 1 (by rfl) ⟨3943844, by rfl⟩ : syracuseStep 5258459 = 7887689) B7887689
theorem B11836637 : Blo 1845624 11836637 := bstep (se 3 (by rfl) ⟨2219369, by rfl⟩ : syracuseStep 11836637 = 4438739) B4438739
theorem B3996959 : Blo 1845624 3996959 := bstep (se 1 (by rfl) ⟨2997719, by rfl⟩ : syracuseStep 3996959 = 5995439) B5995439
theorem B4152671 : Blo 1845624 4152671 := bstep (se 1 (by rfl) ⟨3114503, by rfl⟩ : syracuseStep 4152671 = 6229007) B6229007
theorem B6233543 : Blo 1845624 6233543 := bstep (se 1 (by rfl) ⟨4675157, by rfl⟩ : syracuseStep 6233543 = 9350315) B9350315
theorem B8871383 : Blo 1845624 8871383 := bstep (se 1 (by rfl) ⟨6653537, by rfl⟩ : syracuseStep 8871383 = 13307075) B13307075
theorem B5914127 : Blo 1845624 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B4153067 : Blo 1845624 4153067 := bstep (se 1 (by rfl) ⟨3114800, by rfl⟩ : syracuseStep 4153067 = 6229601) B6229601
theorem B6233867 : Blo 1845624 6233867 := bstep (se 1 (by rfl) ⟨4675400, by rfl⟩ : syracuseStep 6233867 = 9350801) B9350801
theorem B2768681 : Blo 1845624 2768681 := bstep (se 2 (by rfl) ⟨1038255, by rfl⟩ : syracuseStep 2768681 = 2076511) B2076511
theorem B2768687 : Blo 1845624 2768687 := bstep (se 1 (by rfl) ⟨2076515, by rfl⟩ : syracuseStep 2768687 = 4153031) B4153031
theorem B4153193 : Blo 1845624 4153193 := bstep (se 2 (by rfl) ⟨1557447, by rfl⟩ : syracuseStep 4153193 = 3114895) B3114895
theorem B10665857 : Blo 1845624 10665857 := bstep (se 2 (by rfl) ⟨3999696, by rfl⟩ : syracuseStep 10665857 = 7999393) B7999393
theorem B75808973 : Blo 1845624 75808973 := bstep (se 3 (by rfl) ⟨14214182, by rfl⟩ : syracuseStep 75808973 = 28428365) B28428365
theorem B37912855 : Blo 1845624 37912855 := bstep (se 1 (by rfl) ⟨28434641, by rfl⟩ : syracuseStep 37912855 = 56869283) B56869283
theorem B4153697 : Blo 1845624 4153697 := bstep (se 2 (by rfl) ⟨1557636, by rfl⟩ : syracuseStep 4153697 = 3115273) B3115273
theorem B2957705 : Blo 1845624 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B4153787 : Blo 1845624 4153787 := bstep (se 1 (by rfl) ⟨3115340, by rfl⟩ : syracuseStep 4153787 = 6230681) B6230681
theorem B2769359 : Blo 1845624 2769359 := bstep (se 1 (by rfl) ⟨2077019, by rfl⟩ : syracuseStep 2769359 = 4154039) B4154039
theorem B9347561 : Blo 1845624 9347561 := bstep (se 2 (by rfl) ⟨3505335, by rfl⟩ : syracuseStep 9347561 = 7010671) B7010671
theorem B3506665 : Blo 1845624 3506665 := bstep (se 2 (by rfl) ⟨1314999, by rfl⟩ : syracuseStep 3506665 = 2629999) B2629999
theorem B2769401 : Blo 1845624 2769401 := bstep (se 2 (by rfl) ⟨1038525, by rfl⟩ : syracuseStep 2769401 = 2077051) B2077051
theorem B28426763 : Blo 1845624 28426763 := bstep (se 1 (by rfl) ⟨21320072, by rfl⟩ : syracuseStep 28426763 = 42640145) B42640145
theorem B2769503 : Blo 1845624 2769503 := bstep (se 1 (by rfl) ⟨2077127, by rfl⟩ : syracuseStep 2769503 = 4154255) B4154255
theorem B5915243 : Blo 1845624 5915243 := bstep (se 1 (by rfl) ⟨4436432, by rfl⟩ : syracuseStep 5915243 = 8872865) B8872865
theorem B6234731 : Blo 1845624 6234731 := bstep (se 1 (by rfl) ⟨4676048, by rfl⟩ : syracuseStep 6234731 = 9352097) B9352097
theorem B9347723 : Blo 1845624 9347723 := bstep (se 1 (by rfl) ⟨7010792, by rfl⟩ : syracuseStep 9347723 = 14021585) B14021585
theorem B10658557 : Blo 1845624 10658557 := bstep (se 3 (by rfl) ⟨1998479, by rfl⟩ : syracuseStep 10658557 = 3996959) B3996959
theorem B4989863 : Blo 1845624 4989863 := bstep (se 1 (by rfl) ⟨3742397, by rfl⟩ : syracuseStep 4989863 = 7484795) B7484795
theorem B7488571 : Blo 1845624 7488571 := bstep (se 1 (by rfl) ⟨5616428, by rfl⟩ : syracuseStep 7488571 = 11232857) B11232857
theorem B2769983 : Blo 1845624 2769983 := bstep (se 1 (by rfl) ⟨2077487, by rfl⟩ : syracuseStep 2769983 = 4154975) B4154975
theorem B2770025 : Blo 1845624 2770025 := bstep (se 2 (by rfl) ⟨1038759, by rfl⟩ : syracuseStep 2770025 = 2077519) B2077519
theorem B6235325 : Blo 1845624 6235325 := bstep (se 3 (by rfl) ⟨1169123, by rfl⟩ : syracuseStep 6235325 = 2338247) B2338247
theorem B2770127 : Blo 1845624 2770127 := bstep (se 1 (by rfl) ⟨2077595, by rfl⟩ : syracuseStep 2770127 = 4155191) B4155191
theorem B2770331 : Blo 1845624 2770331 := bstep (se 1 (by rfl) ⟨2077748, by rfl⟩ : syracuseStep 2770331 = 4155497) B4155497
theorem B4154795 : Blo 1845624 4154795 := bstep (se 1 (by rfl) ⟨3116096, by rfl⟩ : syracuseStep 4154795 = 6232193) B6232193
theorem B9979487 : Blo 1845624 9979487 := bstep (se 1 (by rfl) ⟨7484615, by rfl⟩ : syracuseStep 9979487 = 14969231) B14969231
theorem B2770553 : Blo 1845624 2770553 := bstep (se 2 (by rfl) ⟨1038957, by rfl⟩ : syracuseStep 2770553 = 2077915) B2077915
theorem B4155047 : Blo 1845624 4155047 := bstep (se 1 (by rfl) ⟨3116285, by rfl⟩ : syracuseStep 4155047 = 6232571) B6232571
theorem B3114679 : Blo 1845624 3114679 := bstep (se 1 (by rfl) ⟨2336009, by rfl⟩ : syracuseStep 3114679 = 4672019) B4672019
theorem B9979615 : Blo 1845624 9979615 := bstep (se 1 (by rfl) ⟨7484711, by rfl⟩ : syracuseStep 9979615 = 14969423) B14969423
theorem B2770655 : Blo 1845624 2770655 := bstep (se 1 (by rfl) ⟨2077991, by rfl⟩ : syracuseStep 2770655 = 4155983) B4155983
theorem B10520381 : Blo 1845624 10520381 := bstep (se 3 (by rfl) ⟨1972571, by rfl⟩ : syracuseStep 10520381 = 3945143) B3945143
theorem B2770751 : Blo 1845624 2770751 := bstep (se 1 (by rfl) ⟨2078063, by rfl⟩ : syracuseStep 2770751 = 4156127) B4156127
theorem B4155335 : Blo 1845624 4155335 := bstep (se 1 (by rfl) ⟨3116501, by rfl⟩ : syracuseStep 4155335 = 6233003) B6233003
theorem B3114983 : Blo 1845624 3114983 := bstep (se 1 (by rfl) ⟨2336237, by rfl⟩ : syracuseStep 3114983 = 4672475) B4672475
theorem B2770919 : Blo 1845624 2770919 := bstep (se 1 (by rfl) ⟨2078189, by rfl⟩ : syracuseStep 2770919 = 4156379) B4156379
theorem B2770937 : Blo 1845624 2770937 := bstep (se 2 (by rfl) ⟨1039101, by rfl⟩ : syracuseStep 2770937 = 2078203) B2078203
theorem B11831305 : Blo 1845624 11831305 := bstep (se 2 (by rfl) ⟨4436739, by rfl⟩ : syracuseStep 11831305 = 8873479) B8873479
theorem B3246175 : Blo 1845624 3246175 := bstep (se 1 (by rfl) ⟨2434631, by rfl⟩ : syracuseStep 3246175 = 4869263) B4869263
theorem B2771039 : Blo 1845624 2771039 := bstep (se 1 (by rfl) ⟨2078279, by rfl⟩ : syracuseStep 2771039 = 4156559) B4156559
theorem B7891091 : Blo 1845624 7891091 := bstep (se 1 (by rfl) ⟨5918318, by rfl⟩ : syracuseStep 7891091 = 11836637) B11836637
theorem B2771099 : Blo 1845624 2771099 := bstep (se 1 (by rfl) ⟨2078324, by rfl⟩ : syracuseStep 2771099 = 4156649) B4156649
theorem B3115199 : Blo 1845624 3115199 := bstep (se 1 (by rfl) ⟨2336399, by rfl⟩ : syracuseStep 3115199 = 4672799) B4672799
theorem B2771135 : Blo 1845624 2771135 := bstep (se 1 (by rfl) ⟨2078351, by rfl⟩ : syracuseStep 2771135 = 4156703) B4156703
theorem B5916883 : Blo 1845624 5916883 := bstep (se 1 (by rfl) ⟨4437662, by rfl⟩ : syracuseStep 5916883 = 8875325) B8875325
theorem B2771177 : Blo 1845624 2771177 := bstep (se 2 (by rfl) ⟨1039191, by rfl⟩ : syracuseStep 2771177 = 2078383) B2078383
theorem B6654187 : Blo 1845624 6654187 := bstep (se 1 (by rfl) ⟨4990640, by rfl⟩ : syracuseStep 6654187 = 9981281) B9981281
theorem B4155641 : Blo 1845624 4155641 := bstep (se 2 (by rfl) ⟨1558365, by rfl⟩ : syracuseStep 4155641 = 3116731) B3116731
theorem B4155695 : Blo 1845624 4155695 := bstep (se 1 (by rfl) ⟨3116771, by rfl⟩ : syracuseStep 4155695 = 6233543) B6233543
theorem B3942751 : Blo 1845624 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B8874497 : Blo 1845624 8874497 := bstep (se 2 (by rfl) ⟨3327936, by rfl⟩ : syracuseStep 8874497 = 6655873) B6655873
theorem B4155911 : Blo 1845624 4155911 := bstep (se 1 (by rfl) ⟨3116933, by rfl⟩ : syracuseStep 4155911 = 6233867) B6233867
theorem B1845787 : Blo 1845624 1845787 := bstep (se 1 (by rfl) ⟨1384340, by rfl⟩ : syracuseStep 1845787 = 2768681) B2768681
theorem B1845791 : Blo 1845624 1845791 := bstep (se 1 (by rfl) ⟨1384343, by rfl⟩ : syracuseStep 1845791 = 2768687) B2768687
theorem B8997407 : Blo 1845624 8997407 := bstep (se 1 (by rfl) ⟨6748055, by rfl⟩ : syracuseStep 8997407 = 13496111) B13496111
theorem B4156091 : Blo 1845624 4156091 := bstep (se 1 (by rfl) ⟨3117068, by rfl⟩ : syracuseStep 4156091 = 6234137) B6234137
theorem B10513091 : Blo 1845624 10513091 := bstep (se 1 (by rfl) ⟨7884818, by rfl⟩ : syracuseStep 10513091 = 15769637) B15769637
theorem B1846107 : Blo 1845624 1846107 := bstep (se 1 (by rfl) ⟨1384580, by rfl⟩ : syracuseStep 1846107 = 2769161) B2769161
theorem B3115867 : Blo 1845624 3115867 := bstep (se 1 (by rfl) ⟨2336900, by rfl⟩ : syracuseStep 3115867 = 4673801) B4673801
theorem B1846175 : Blo 1845624 1846175 := bstep (se 1 (by rfl) ⟨1384631, by rfl⟩ : syracuseStep 1846175 = 2769263) B2769263
theorem B17738689 : Blo 1845624 17738689 := bstep (se 2 (by rfl) ⟨6652008, by rfl⟩ : syracuseStep 17738689 = 13304017) B13304017
theorem B3328975 : Blo 1845624 3328975 := bstep (se 1 (by rfl) ⟨2496731, by rfl⟩ : syracuseStep 3328975 = 4993463) B4993463
theorem B1870895 : Blo 1845624 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B1846319 : Blo 1845624 1846319 := bstep (se 1 (by rfl) ⟨1384739, by rfl⟩ : syracuseStep 1846319 = 2769479) B2769479
theorem B1846343 : Blo 1845624 1846343 := bstep (se 1 (by rfl) ⟨1384757, by rfl⟩ : syracuseStep 1846343 = 2769515) B2769515
theorem B5917817 : Blo 1845624 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B47992007 : Blo 1845624 47992007 := bstep (se 1 (by rfl) ⟨35994005, by rfl⟩ : syracuseStep 47992007 = 71988011) B71988011
theorem B7883999 : Blo 1845624 7883999 := bstep (se 1 (by rfl) ⟨5912999, by rfl⟩ : syracuseStep 7883999 = 11825999) B11825999
theorem B1846495 : Blo 1845624 1846495 := bstep (se 1 (by rfl) ⟨1384871, by rfl⟩ : syracuseStep 1846495 = 2769743) B2769743
theorem B4328873 : Blo 1845624 4328873 := bstep (se 2 (by rfl) ⟨1623327, by rfl⟩ : syracuseStep 4328873 = 3246655) B3246655
theorem B1846759 : Blo 1845624 1846759 := bstep (se 1 (by rfl) ⟨1385069, by rfl⟩ : syracuseStep 1846759 = 2770139) B2770139
theorem B4156919 : Blo 1845624 4156919 := bstep (se 1 (by rfl) ⟨3117689, by rfl⟩ : syracuseStep 4156919 = 6235379) B6235379
theorem B43232777 : Blo 1845624 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B4435519 : Blo 1845624 4435519 := bstep (se 1 (by rfl) ⟨3326639, by rfl⟩ : syracuseStep 4435519 = 6653279) B6653279
theorem B4156991 : Blo 1845624 4156991 := bstep (se 1 (by rfl) ⟨3117743, by rfl⟩ : syracuseStep 4156991 = 6235487) B6235487
theorem B1846875 : Blo 1845624 1846875 := bstep (se 1 (by rfl) ⟨1385156, by rfl⟩ : syracuseStep 1846875 = 2770313) B2770313
theorem B3116839 : Blo 1845624 3116839 := bstep (se 1 (by rfl) ⟨2337629, by rfl⟩ : syracuseStep 3116839 = 4675259) B4675259
theorem B1847111 : Blo 1845624 1847111 := bstep (se 1 (by rfl) ⟨1385333, by rfl⟩ : syracuseStep 1847111 = 2770667) B2770667
theorem B11702161 : Blo 1845624 11702161 := bstep (se 2 (by rfl) ⟨4388310, by rfl⟩ : syracuseStep 11702161 = 8776621) B8776621
theorem B1847263 : Blo 1845624 1847263 := bstep (se 1 (by rfl) ⟨1385447, by rfl⟩ : syracuseStep 1847263 = 2770895) B2770895
theorem B4673659 : Blo 1845624 4673659 := bstep (se 1 (by rfl) ⟨3505244, by rfl⟩ : syracuseStep 4673659 = 7010489) B7010489
theorem B1847527 : Blo 1845624 1847527 := bstep (se 1 (by rfl) ⟨1385645, by rfl⟩ : syracuseStep 1847527 = 2771291) B2771291
theorem B4436279 : Blo 1845624 4436279 := bstep (se 1 (by rfl) ⟨3327209, by rfl⟩ : syracuseStep 4436279 = 6654419) B6654419
theorem B56865341 : Blo 1845624 56865341 := bstep (se 3 (by rfl) ⟨10662251, by rfl⟩ : syracuseStep 56865341 = 21324503) B21324503
theorem B50532959 : Blo 1845624 50532959 := bstep (se 1 (by rfl) ⟨37899719, by rfl⟩ : syracuseStep 50532959 = 75799439) B75799439
theorem B7009031 : Blo 1845624 7009031 := bstep (se 1 (by rfl) ⟨5256773, by rfl⟩ : syracuseStep 7009031 = 10513547) B10513547
theorem B3117865 : Blo 1845624 3117865 := bstep (se 2 (by rfl) ⟨1169199, by rfl⟩ : syracuseStep 3117865 = 2338399) B2338399
theorem B15774695 : Blo 1845624 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B6231113 : Blo 1845624 6231113 := bstep (se 2 (by rfl) ⟨2336667, by rfl⟩ : syracuseStep 6231113 = 4673335) B4673335
theorem B33690917 : Blo 1845624 33690917 := bstep (se 4 (by rfl) ⟨3158523, by rfl⟩ : syracuseStep 33690917 = 6317047) B6317047
theorem B31536539 : Blo 1845624 31536539 := bstep (se 1 (by rfl) ⟨23652404, by rfl⟩ : syracuseStep 31536539 = 47304809) B47304809
theorem B9352907 : Blo 1845624 9352907 := bstep (se 1 (by rfl) ⟨7014680, by rfl⟩ : syracuseStep 9352907 = 14029361) B14029361
theorem B17987345 : Blo 1845624 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B4675391 : Blo 1845624 4675391 := bstep (se 1 (by rfl) ⟨3506543, by rfl⟩ : syracuseStep 4675391 = 7013087) B7013087
theorem B2078527 : Blo 1845624 2078527 := bstep (se 1 (by rfl) ⟨1558895, by rfl⟩ : syracuseStep 2078527 = 3117791) B3117791
theorem B7010185 : Blo 1845624 7010185 := bstep (se 2 (by rfl) ⟨2628819, by rfl⟩ : syracuseStep 7010185 = 5257639) B5257639
theorem B14022557 : Blo 1845624 14022557 := bstep (se 3 (by rfl) ⟨2629229, by rfl⟩ : syracuseStep 14022557 = 5258459) B5258459
theorem B23664707 : Blo 1845624 23664707 := bstep (se 1 (by rfl) ⟨17748530, by rfl⟩ : syracuseStep 23664707 = 35497061) B35497061
theorem B4675745 : Blo 1845624 4675745 := bstep (se 2 (by rfl) ⟨1753404, by rfl⟩ : syracuseStep 4675745 = 3506809) B3506809
theorem B11827433 : Blo 1845624 11827433 := bstep (se 2 (by rfl) ⟨4435287, by rfl⟩ : syracuseStep 11827433 = 8870575) B8870575
theorem B8870267 : Blo 1845624 8870267 := bstep (se 1 (by rfl) ⟨6652700, by rfl⟩ : syracuseStep 8870267 = 13305401) B13305401
theorem B10656143 : Blo 1845624 10656143 := bstep (se 1 (by rfl) ⟨7992107, by rfl⟩ : syracuseStep 10656143 = 15984215) B15984215
theorem B9345455 : Blo 1845624 9345455 := bstep (se 1 (by rfl) ⟨7009091, by rfl⟩ : syracuseStep 9345455 = 14018183) B14018183
theorem B31554035 : Blo 1845624 31554035 := bstep (se 1 (by rfl) ⟨23665526, by rfl⟩ : syracuseStep 31554035 = 47331053) B47331053
theorem B4438585 : Blo 1845624 4438585 := bstep (se 2 (by rfl) ⟨1664469, by rfl⟩ : syracuseStep 4438585 = 3328939) B3328939
theorem B23657021 : Blo 1845624 23657021 := bstep (se 3 (by rfl) ⟨4435691, by rfl⟩ : syracuseStep 23657021 = 8871383) B8871383
theorem B6232733 : Blo 1845624 6232733 := bstep (se 3 (by rfl) ⟨1168637, by rfl⟩ : syracuseStep 6232733 = 2337275) B2337275
theorem B35109551 : Blo 1845624 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B7887725 : Blo 1845624 7887725 := bstep (se 3 (by rfl) ⟨1478948, by rfl⟩ : syracuseStep 7887725 = 2957897) B2957897
theorem B5258209 : Blo 1845624 5258209 := bstep (se 2 (by rfl) ⟨1971828, by rfl⟩ : syracuseStep 5258209 = 3943657) B3943657
theorem B6233057 : Blo 1845624 6233057 := bstep (se 2 (by rfl) ⟨2337396, by rfl⟩ : syracuseStep 6233057 = 4674793) B4674793
theorem B5913641 : Blo 1845624 5913641 := bstep (se 2 (by rfl) ⟨2217615, by rfl⟩ : syracuseStep 5913641 = 4435231) B4435231
theorem B2628649 : Blo 1845624 2628649 := bstep (se 2 (by rfl) ⟨985743, by rfl⟩ : syracuseStep 2628649 = 1971487) B1971487
theorem B4676737 : Blo 1845624 4676737 := bstep (se 2 (by rfl) ⟨1753776, by rfl⟩ : syracuseStep 4676737 = 3507553) B3507553
theorem B6233273 : Blo 1845624 6233273 := bstep (se 2 (by rfl) ⟨2337477, by rfl⟩ : syracuseStep 6233273 = 4674955) B4674955
theorem B15170935 : Blo 1845624 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B4152743 : Blo 1845624 4152743 := bstep (se 1 (by rfl) ⟨3114557, by rfl⟩ : syracuseStep 4152743 = 6229115) B6229115
theorem B10665445 : Blo 1845624 10665445 := bstep (se 4 (by rfl) ⟨999885, by rfl⟩ : syracuseStep 10665445 = 1999771) B1999771
theorem B2768447 : Blo 1845624 2768447 := bstep (se 1 (by rfl) ⟨2076335, by rfl⟩ : syracuseStep 2768447 = 4152671) B4152671
theorem B5332559 : Blo 1845624 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B4152923 : Blo 1845624 4152923 := bstep (se 1 (by rfl) ⟨3114692, by rfl⟩ : syracuseStep 4152923 = 6229385) B6229385
theorem B28442285 : Blo 1845624 28442285 := bstep (se 3 (by rfl) ⟨5332928, by rfl⟩ : syracuseStep 28442285 = 10665857) B10665857
theorem B41033405 : Blo 1845624 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B6315745 : Blo 1845624 6315745 := bstep (se 2 (by rfl) ⟨2368404, by rfl⟩ : syracuseStep 6315745 = 4736809) B4736809
theorem B39952115 : Blo 1845624 39952115 := bstep (se 1 (by rfl) ⟨29964086, by rfl⟩ : syracuseStep 39952115 = 59928173) B59928173
theorem B2768711 : Blo 1845624 2768711 := bstep (se 1 (by rfl) ⟨2076533, by rfl⟩ : syracuseStep 2768711 = 4153067) B4153067
theorem B4153211 : Blo 1845624 4153211 := bstep (se 1 (by rfl) ⟨3114908, by rfl⟩ : syracuseStep 4153211 = 6229817) B6229817
theorem B2768795 : Blo 1845624 2768795 := bstep (se 1 (by rfl) ⟨2076596, by rfl⟩ : syracuseStep 2768795 = 4153193) B4153193
theorem B6315965 : Blo 1845624 6315965 := bstep (se 3 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 6315965 = 2368487) B2368487
theorem B4989053 : Blo 1845624 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B2957519 : Blo 1845624 2957519 := bstep (se 1 (by rfl) ⟨2218139, by rfl⟩ : syracuseStep 2957519 = 4436279) B4436279
theorem B2769131 : Blo 1845624 2769131 := bstep (se 1 (by rfl) ⟨2076848, by rfl⟩ : syracuseStep 2769131 = 4153697) B4153697
theorem B7889177 : Blo 1845624 7889177 := bstep (se 2 (by rfl) ⟨2958441, by rfl⟩ : syracuseStep 7889177 = 5916883) B5916883
theorem B2769191 : Blo 1845624 2769191 := bstep (se 1 (by rfl) ⟨2076893, by rfl⟩ : syracuseStep 2769191 = 4153787) B4153787
theorem B8872249 : Blo 1845624 8872249 := bstep (se 2 (by rfl) ⟨3327093, by rfl⟩ : syracuseStep 8872249 = 6654187) B6654187
theorem B4154075 : Blo 1845624 4154075 := bstep (se 1 (by rfl) ⟨3115556, by rfl⟩ : syracuseStep 4154075 = 6231113) B6231113
theorem B2769863 : Blo 1845624 2769863 := bstep (se 1 (by rfl) ⟨2077397, by rfl⟩ : syracuseStep 2769863 = 4154795) B4154795
theorem B6652991 : Blo 1845624 6652991 := bstep (se 1 (by rfl) ⟨4989743, by rfl⟩ : syracuseStep 6652991 = 9979487) B9979487
theorem B2770031 : Blo 1845624 2770031 := bstep (se 1 (by rfl) ⟨2077523, by rfl⟩ : syracuseStep 2770031 = 4155047) B4155047
theorem B4154489 : Blo 1845624 4154489 := bstep (se 2 (by rfl) ⟨1557933, by rfl⟩ : syracuseStep 4154489 = 3115867) B3115867
theorem B6235271 : Blo 1845624 6235271 := bstep (se 1 (by rfl) ⟨4676453, by rfl⟩ : syracuseStep 6235271 = 9352907) B9352907
theorem B7013587 : Blo 1845624 7013587 := bstep (se 1 (by rfl) ⟨5260190, by rfl⟩ : syracuseStep 7013587 = 10520381) B10520381
theorem B23651585 : Blo 1845624 23651585 := bstep (se 2 (by rfl) ⟨8869344, by rfl⟩ : syracuseStep 23651585 = 17738689) B17738689
theorem B9348371 : Blo 1845624 9348371 := bstep (se 1 (by rfl) ⟨7011278, by rfl⟩ : syracuseStep 9348371 = 14022557) B14022557
theorem B2770223 : Blo 1845624 2770223 := bstep (se 1 (by rfl) ⟨2077667, by rfl⟩ : syracuseStep 2770223 = 4155335) B4155335
theorem B56845637 : Blo 1845624 56845637 := bstep (se 4 (by rfl) ⟨5329278, by rfl⟩ : syracuseStep 56845637 = 10658557) B10658557
theorem B5260727 : Blo 1845624 5260727 := bstep (se 1 (by rfl) ⟨3945545, by rfl⟩ : syracuseStep 5260727 = 7891091) B7891091
theorem B2770427 : Blo 1845624 2770427 := bstep (se 1 (by rfl) ⟨2077820, by rfl⟩ : syracuseStep 2770427 = 4155641) B4155641
theorem B6235649 : Blo 1845624 6235649 := bstep (se 2 (by rfl) ⟨2338368, by rfl⟩ : syracuseStep 6235649 = 4676737) B4676737
theorem B2770463 : Blo 1845624 2770463 := bstep (se 1 (by rfl) ⟨2077847, by rfl⟩ : syracuseStep 2770463 = 4155695) B4155695
theorem B7104095 : Blo 1845624 7104095 := bstep (se 1 (by rfl) ⟨5328071, by rfl⟩ : syracuseStep 7104095 = 10656143) B10656143
theorem B5916331 : Blo 1845624 5916331 := bstep (se 1 (by rfl) ⟨4437248, by rfl⟩ : syracuseStep 5916331 = 8874497) B8874497
theorem B2770607 : Blo 1845624 2770607 := bstep (se 1 (by rfl) ⟨2077955, by rfl⟩ : syracuseStep 2770607 = 4155911) B4155911
theorem B5998271 : Blo 1845624 5998271 := bstep (se 1 (by rfl) ⟨4498703, by rfl⟩ : syracuseStep 5998271 = 8997407) B8997407
theorem B15771347 : Blo 1845624 15771347 := bstep (se 1 (by rfl) ⟨11828510, by rfl⟩ : syracuseStep 15771347 = 23657021) B23657021
theorem B4155155 : Blo 1845624 4155155 := bstep (se 1 (by rfl) ⟨3116366, by rfl⟩ : syracuseStep 4155155 = 6232733) B6232733
theorem B23406367 : Blo 1845624 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B2770727 : Blo 1845624 2770727 := bstep (se 1 (by rfl) ⟨2078045, by rfl⟩ : syracuseStep 2770727 = 4156091) B4156091
theorem B20227913 : Blo 1845624 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B109422413 : Blo 1845624 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B4155371 : Blo 1845624 4155371 := bstep (se 1 (by rfl) ⟨3116528, by rfl⟩ : syracuseStep 4155371 = 6233057) B6233057
theorem B3942427 : Blo 1845624 3942427 := bstep (se 1 (by rfl) ⟨2956820, by rfl⟩ : syracuseStep 3942427 = 5913641) B5913641
theorem B4155515 : Blo 1845624 4155515 := bstep (se 1 (by rfl) ⟨3116636, by rfl⟩ : syracuseStep 4155515 = 6233273) B6233273
theorem B2885915 : Blo 1845624 2885915 := bstep (se 1 (by rfl) ⟨2164436, by rfl⟩ : syracuseStep 2885915 = 4328873) B4328873
theorem B13306153 : Blo 1845624 13306153 := bstep (se 2 (by rfl) ⟨4989807, by rfl⟩ : syracuseStep 13306153 = 9979615) B9979615
theorem B2771279 : Blo 1845624 2771279 := bstep (se 1 (by rfl) ⟨2078459, by rfl⟩ : syracuseStep 2771279 = 4156919) B4156919
theorem B28821851 : Blo 1845624 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B1845631 : Blo 1845624 1845631 := bstep (se 1 (by rfl) ⟨1384223, by rfl⟩ : syracuseStep 1845631 = 2768447) B2768447
theorem B2771327 : Blo 1845624 2771327 := bstep (se 1 (by rfl) ⟨2078495, by rfl⟩ : syracuseStep 2771327 = 4156991) B4156991
theorem B4155785 : Blo 1845624 4155785 := bstep (se 2 (by rfl) ⟨1558419, by rfl⟩ : syracuseStep 4155785 = 3116839) B3116839
theorem B2771369 : Blo 1845624 2771369 := bstep (se 2 (by rfl) ⟨1039263, by rfl⟩ : syracuseStep 2771369 = 2078527) B2078527
theorem B13306301 : Blo 1845624 13306301 := bstep (se 3 (by rfl) ⟨2494931, by rfl⟩ : syracuseStep 13306301 = 4989863) B4989863
theorem B26634743 : Blo 1845624 26634743 := bstep (se 1 (by rfl) ⟨19976057, by rfl⟩ : syracuseStep 26634743 = 39952115) B39952115
theorem B1845807 : Blo 1845624 1845807 := bstep (se 1 (by rfl) ⟨1384355, by rfl⟩ : syracuseStep 1845807 = 2768711) B2768711
theorem B1845863 : Blo 1845624 1845863 := bstep (se 1 (by rfl) ⟨1384397, by rfl⟩ : syracuseStep 1845863 = 2768795) B2768795
theorem B50539315 : Blo 1845624 50539315 := bstep (se 1 (by rfl) ⟨37904486, by rfl⟩ : syracuseStep 50539315 = 75808973) B75808973
theorem B1846239 : Blo 1845624 1846239 := bstep (se 1 (by rfl) ⟨1384679, by rfl⟩ : syracuseStep 1846239 = 2769359) B2769359
theorem B15780845 : Blo 1845624 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B1846267 : Blo 1845624 1846267 := bstep (se 1 (by rfl) ⟨1384700, by rfl⟩ : syracuseStep 1846267 = 2769401) B2769401
theorem B18951175 : Blo 1845624 18951175 := bstep (se 1 (by rfl) ⟨14213381, by rfl⟩ : syracuseStep 18951175 = 28426763) B28426763
theorem B1846335 : Blo 1845624 1846335 := bstep (se 1 (by rfl) ⟨1384751, by rfl⟩ : syracuseStep 1846335 = 2769503) B2769503
theorem B33688639 : Blo 1845624 33688639 := bstep (se 1 (by rfl) ⟨25266479, by rfl⟩ : syracuseStep 33688639 = 50532959) B50532959
theorem B3943495 : Blo 1845624 3943495 := bstep (se 1 (by rfl) ⟨2957621, by rfl⟩ : syracuseStep 3943495 = 5915243) B5915243
theorem B4156487 : Blo 1845624 4156487 := bstep (se 1 (by rfl) ⟨3117365, by rfl⟩ : syracuseStep 4156487 = 6234731) B6234731
theorem B17312933 : Blo 1845624 17312933 := bstep (se 4 (by rfl) ⟨1623087, by rfl⟩ : syracuseStep 17312933 = 3246175) B3246175
theorem B4672687 : Blo 1845624 4672687 := bstep (se 1 (by rfl) ⟨3504515, by rfl⟩ : syracuseStep 4672687 = 7009031) B7009031
theorem B1846655 : Blo 1845624 1846655 := bstep (se 1 (by rfl) ⟨1384991, by rfl⟩ : syracuseStep 1846655 = 2769983) B2769983
theorem B1846683 : Blo 1845624 1846683 := bstep (se 1 (by rfl) ⟨1385012, by rfl⟩ : syracuseStep 1846683 = 2770025) B2770025
theorem B5918113 : Blo 1845624 5918113 := bstep (se 2 (by rfl) ⟨2219292, by rfl⟩ : syracuseStep 5918113 = 4438585) B4438585
theorem B4156883 : Blo 1845624 4156883 := bstep (se 1 (by rfl) ⟨3117662, by rfl⟩ : syracuseStep 4156883 = 6235325) B6235325
theorem B1846751 : Blo 1845624 1846751 := bstep (se 1 (by rfl) ⟨1385063, by rfl⟩ : syracuseStep 1846751 = 2770127) B2770127
theorem B21024359 : Blo 1845624 21024359 := bstep (se 1 (by rfl) ⟨15768269, by rfl⟩ : syracuseStep 21024359 = 31536539) B31536539
theorem B1846887 : Blo 1845624 1846887 := bstep (se 1 (by rfl) ⟨1385165, by rfl⟩ : syracuseStep 1846887 = 2770331) B2770331
theorem B23654045 : Blo 1845624 23654045 := bstep (se 3 (by rfl) ⟨4435133, by rfl⟩ : syracuseStep 23654045 = 8870267) B8870267
theorem B4157153 : Blo 1845624 4157153 := bstep (se 2 (by rfl) ⟨1558932, by rfl⟩ : syracuseStep 4157153 = 3117865) B3117865
theorem B1847035 : Blo 1845624 1847035 := bstep (se 1 (by rfl) ⟨1385276, by rfl⟩ : syracuseStep 1847035 = 2770553) B2770553
theorem B1847103 : Blo 1845624 1847103 := bstep (se 1 (by rfl) ⟨1385327, by rfl⟩ : syracuseStep 1847103 = 2770655) B2770655
theorem B3116927 : Blo 1845624 3116927 := bstep (se 1 (by rfl) ⟨2337695, by rfl⟩ : syracuseStep 3116927 = 4675391) B4675391
theorem B1847167 : Blo 1845624 1847167 := bstep (se 1 (by rfl) ⟨1385375, by rfl⟩ : syracuseStep 1847167 = 2770751) B2770751
theorem B2076655 : Blo 1845624 2076655 := bstep (se 1 (by rfl) ⟨1557491, by rfl⟩ : syracuseStep 2076655 = 3114983) B3114983
theorem B1847279 : Blo 1845624 1847279 := bstep (se 1 (by rfl) ⟨1385459, by rfl⟩ : syracuseStep 1847279 = 2770919) B2770919
theorem B1847291 : Blo 1845624 1847291 := bstep (se 1 (by rfl) ⟨1385468, by rfl⟩ : syracuseStep 1847291 = 2770937) B2770937
theorem B1847359 : Blo 1845624 1847359 := bstep (se 1 (by rfl) ⟨1385519, by rfl⟩ : syracuseStep 1847359 = 2771039) B2771039
theorem B1847399 : Blo 1845624 1847399 := bstep (se 1 (by rfl) ⟨1385549, by rfl⟩ : syracuseStep 1847399 = 2771099) B2771099
theorem B3117163 : Blo 1845624 3117163 := bstep (se 1 (by rfl) ⟨2337872, by rfl⟩ : syracuseStep 3117163 = 4675745) B4675745
theorem B2076799 : Blo 1845624 2076799 := bstep (se 1 (by rfl) ⟨1557599, by rfl⟩ : syracuseStep 2076799 = 3115199) B3115199
theorem B1847423 : Blo 1845624 1847423 := bstep (se 1 (by rfl) ⟨1385567, by rfl⟩ : syracuseStep 1847423 = 2771135) B2771135
theorem B7884955 : Blo 1845624 7884955 := bstep (se 1 (by rfl) ⟨5913716, by rfl⟩ : syracuseStep 7884955 = 11827433) B11827433
theorem B1847451 : Blo 1845624 1847451 := bstep (se 1 (by rfl) ⟨1385588, by rfl⟩ : syracuseStep 1847451 = 2771177) B2771177
theorem B6230303 : Blo 1845624 6230303 := bstep (se 1 (by rfl) ⟨4672727, by rfl⟩ : syracuseStep 6230303 = 9345455) B9345455
theorem B7008727 : Blo 1845624 7008727 := bstep (se 1 (by rfl) ⟨5256545, by rfl⟩ : syracuseStep 7008727 = 10513091) B10513091
theorem B31994671 : Blo 1845624 31994671 := bstep (se 1 (by rfl) ⟨23996003, by rfl⟩ : syracuseStep 31994671 = 47992007) B47992007
theorem B5255999 : Blo 1845624 5255999 := bstep (se 1 (by rfl) ⟨3941999, by rfl⟩ : syracuseStep 5255999 = 7883999) B7883999
theorem B18961523 : Blo 1845624 18961523 := bstep (se 1 (by rfl) ⟨14221142, by rfl⟩ : syracuseStep 18961523 = 28442285) B28442285
theorem B15602881 : Blo 1845624 15602881 := bstep (se 2 (by rfl) ⟨5851080, by rfl⟩ : syracuseStep 15602881 = 11702161) B11702161
theorem B15775073 : Blo 1845624 15775073 := bstep (se 2 (by rfl) ⟨5915652, by rfl⟩ : syracuseStep 15775073 = 11831305) B11831305
theorem B6231545 : Blo 1845624 6231545 := bstep (se 2 (by rfl) ⟨2336829, by rfl⟩ : syracuseStep 6231545 = 4673659) B4673659
theorem B1971803 : Blo 1845624 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B6231707 : Blo 1845624 6231707 := bstep (se 1 (by rfl) ⟨4673780, by rfl⟩ : syracuseStep 6231707 = 9347561) B9347561
theorem B50550473 : Blo 1845624 50550473 := bstep (se 2 (by rfl) ⟨18956427, by rfl⟩ : syracuseStep 50550473 = 37912855) B37912855
theorem B6231815 : Blo 1845624 6231815 := bstep (se 1 (by rfl) ⟨4673861, by rfl⟩ : syracuseStep 6231815 = 9347723) B9347723
theorem B5257001 : Blo 1845624 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B4675553 : Blo 1845624 4675553 := bstep (se 2 (by rfl) ⟨1753332, by rfl⟩ : syracuseStep 4675553 = 3506665) B3506665
theorem B10516463 : Blo 1845624 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B22460611 : Blo 1845624 22460611 := bstep (se 1 (by rfl) ⟨16845458, by rfl⟩ : syracuseStep 22460611 = 33690917) B33690917
theorem B11991563 : Blo 1845624 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B4438633 : Blo 1845624 4438633 := bstep (se 2 (by rfl) ⟨1664487, by rfl⟩ : syracuseStep 4438633 = 3328975) B3328975
theorem B7010945 : Blo 1845624 7010945 := bstep (se 2 (by rfl) ⟨2629104, by rfl⟩ : syracuseStep 7010945 = 5258209) B5258209
theorem B15776471 : Blo 1845624 15776471 := bstep (se 1 (by rfl) ⟨11832353, by rfl⟩ : syracuseStep 15776471 = 23664707) B23664707
theorem B3504865 : Blo 1845624 3504865 := bstep (se 2 (by rfl) ⟨1314324, by rfl⟩ : syracuseStep 3504865 = 2628649) B2628649
theorem B9984761 : Blo 1845624 9984761 := bstep (se 2 (by rfl) ⟨3744285, by rfl⟩ : syracuseStep 9984761 = 7488571) B7488571
theorem B151640909 : Blo 1845624 151640909 := bstep (se 3 (by rfl) ⟨28432670, by rfl⟩ : syracuseStep 151640909 = 56865341) B56865341
theorem B14220157 : Blo 1845624 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B21036023 : Blo 1845624 21036023 := bstep (se 1 (by rfl) ⟨15777017, by rfl⟩ : syracuseStep 21036023 = 31554035) B31554035
theorem B5258483 : Blo 1845624 5258483 := bstep (se 1 (by rfl) ⟨3943862, by rfl⟩ : syracuseStep 5258483 = 7887725) B7887725
theorem B14220593 : Blo 1845624 14220593 := bstep (se 2 (by rfl) ⟨5332722, by rfl⟩ : syracuseStep 14220593 = 10665445) B10665445
theorem B5914025 : Blo 1845624 5914025 := bstep (se 2 (by rfl) ⟨2217759, by rfl⟩ : syracuseStep 5914025 = 4435519) B4435519
theorem B4152905 : Blo 1845624 4152905 := bstep (se 2 (by rfl) ⟨1557339, by rfl⟩ : syracuseStep 4152905 = 3114679) B3114679
theorem B2768495 : Blo 1845624 2768495 := bstep (se 1 (by rfl) ⟨2076371, by rfl⟩ : syracuseStep 2768495 = 4152743) B4152743
theorem B8420993 : Blo 1845624 8420993 := bstep (se 2 (by rfl) ⟨3157872, by rfl⟩ : syracuseStep 8420993 = 6315745) B6315745
theorem B2768615 : Blo 1845624 2768615 := bstep (se 1 (by rfl) ⟨2076461, by rfl⟩ : syracuseStep 2768615 = 4152923) B4152923
theorem B9346913 : Blo 1845624 9346913 := bstep (se 2 (by rfl) ⟨3505092, by rfl⟩ : syracuseStep 9346913 = 7010185) B7010185
theorem B2768807 : Blo 1845624 2768807 := bstep (se 1 (by rfl) ⟨2076605, by rfl⟩ : syracuseStep 2768807 = 4153211) B4153211
theorem B4210643 : Blo 1845624 4210643 := bstep (se 1 (by rfl) ⟨3157982, by rfl⟩ : syracuseStep 4210643 = 6315965) B6315965
theorem B3326035 : Blo 1845624 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B2769065 : Blo 1845624 2769065 := bstep (se 2 (by rfl) ⟨1038399, by rfl⟩ : syracuseStep 2769065 = 2076799) B2076799
theorem B5259451 : Blo 1845624 5259451 := bstep (se 1 (by rfl) ⟨3944588, by rfl⟩ : syracuseStep 5259451 = 7889177) B7889177
theorem B4153535 : Blo 1845624 4153535 := bstep (se 1 (by rfl) ⟨3115151, by rfl⟩ : syracuseStep 4153535 = 6230303) B6230303
theorem B11829665 : Blo 1845624 11829665 := bstep (se 2 (by rfl) ⟨4436124, by rfl⟩ : syracuseStep 11829665 = 8872249) B8872249
theorem B2769383 : Blo 1845624 2769383 := bstep (se 1 (by rfl) ⟨2077037, by rfl⟩ : syracuseStep 2769383 = 4154075) B4154075
theorem B12641015 : Blo 1845624 12641015 := bstep (se 1 (by rfl) ⟨9480761, by rfl⟩ : syracuseStep 12641015 = 18961523) B18961523
theorem B2769659 : Blo 1845624 2769659 := bstep (se 1 (by rfl) ⟨2077244, by rfl⟩ : syracuseStep 2769659 = 4154489) B4154489
theorem B37897091 : Blo 1845624 37897091 := bstep (se 1 (by rfl) ⟨28422818, by rfl⟩ : syracuseStep 37897091 = 56845637) B56845637
theorem B3507151 : Blo 1845624 3507151 := bstep (se 1 (by rfl) ⟨2630363, by rfl⟩ : syracuseStep 3507151 = 5260727) B5260727
theorem B4154363 : Blo 1845624 4154363 := bstep (se 1 (by rfl) ⟨3115772, by rfl⟩ : syracuseStep 4154363 = 6231545) B6231545
theorem B4736063 : Blo 1845624 4736063 := bstep (se 1 (by rfl) ⟨3552047, by rfl⟩ : syracuseStep 4736063 = 7104095) B7104095
theorem B4154471 : Blo 1845624 4154471 := bstep (se 1 (by rfl) ⟨3115853, by rfl⟩ : syracuseStep 4154471 = 6231707) B6231707
theorem B4154543 : Blo 1845624 4154543 := bstep (se 1 (by rfl) ⟨3115907, by rfl⟩ : syracuseStep 4154543 = 6231815) B6231815
theorem B2770103 : Blo 1845624 2770103 := bstep (se 1 (by rfl) ⟨2077577, by rfl⟩ : syracuseStep 2770103 = 4155155) B4155155
theorem B13485275 : Blo 1845624 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B2770247 : Blo 1845624 2770247 := bstep (se 1 (by rfl) ⟨2077685, by rfl⟩ : syracuseStep 2770247 = 4155371) B4155371
theorem B2770343 : Blo 1845624 2770343 := bstep (se 1 (by rfl) ⟨2077757, by rfl⟩ : syracuseStep 2770343 = 4155515) B4155515
theorem B44918185 : Blo 1845624 44918185 := bstep (se 2 (by rfl) ⟨16844319, by rfl⟩ : syracuseStep 44918185 = 33688639) B33688639
theorem B2770523 : Blo 1845624 2770523 := bstep (se 1 (by rfl) ⟨2077892, by rfl⟩ : syracuseStep 2770523 = 4155785) B4155785
theorem B7890817 : Blo 1845624 7890817 := bstep (se 2 (by rfl) ⟨2959056, by rfl⟩ : syracuseStep 7890817 = 5918113) B5918113
theorem B10520563 : Blo 1845624 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B2770991 : Blo 1845624 2770991 := bstep (se 1 (by rfl) ⟨2078243, by rfl⟩ : syracuseStep 2770991 = 4156487) B4156487
theorem B14018669 : Blo 1845624 14018669 := bstep (se 3 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 14018669 = 5257001) B5257001
theorem B9480395 : Blo 1845624 9480395 := bstep (se 1 (by rfl) ⟨7110296, by rfl⟩ : syracuseStep 9480395 = 14220593) B14220593
theorem B3942683 : Blo 1845624 3942683 := bstep (se 1 (by rfl) ⟨2957012, by rfl⟩ : syracuseStep 3942683 = 5914025) B5914025
theorem B2771255 : Blo 1845624 2771255 := bstep (se 1 (by rfl) ⟨2078441, by rfl⟩ : syracuseStep 2771255 = 4156883) B4156883
theorem B1845663 : Blo 1845624 1845663 := bstep (se 1 (by rfl) ⟨1384247, by rfl⟩ : syracuseStep 1845663 = 2768495) B2768495
theorem B5613995 : Blo 1845624 5613995 := bstep (se 1 (by rfl) ⟨4210496, by rfl⟩ : syracuseStep 5613995 = 8420993) B8420993
theorem B2771435 : Blo 1845624 2771435 := bstep (se 1 (by rfl) ⟨2078576, by rfl⟩ : syracuseStep 2771435 = 4157153) B4157153
theorem B1845743 : Blo 1845624 1845743 := bstep (se 1 (by rfl) ⟨1384307, by rfl⟩ : syracuseStep 1845743 = 2768615) B2768615
theorem B1845871 : Blo 1845624 1845871 := bstep (se 1 (by rfl) ⟨1384403, by rfl⟩ : syracuseStep 1845871 = 2768807) B2768807
theorem B4156217 : Blo 1845624 4156217 := bstep (se 2 (by rfl) ⟨1558581, by rfl⟩ : syracuseStep 4156217 = 3117163) B3117163
theorem B1846087 : Blo 1845624 1846087 := bstep (se 1 (by rfl) ⟨1384565, by rfl⟩ : syracuseStep 1846087 = 2769131) B2769131
theorem B1846127 : Blo 1845624 1846127 := bstep (se 1 (by rfl) ⟨1384595, by rfl⟩ : syracuseStep 1846127 = 2769191) B2769191
theorem B10513273 : Blo 1845624 10513273 := bstep (se 2 (by rfl) ⟨3942477, by rfl⟩ : syracuseStep 10513273 = 7884955) B7884955
theorem B1846575 : Blo 1845624 1846575 := bstep (se 1 (by rfl) ⟨1384931, by rfl⟩ : syracuseStep 1846575 = 2769863) B2769863
theorem B4435327 : Blo 1845624 4435327 := bstep (se 1 (by rfl) ⟨3326495, by rfl⟩ : syracuseStep 4435327 = 6652991) B6652991
theorem B7695773 : Blo 1845624 7695773 := bstep (se 3 (by rfl) ⟨1442957, by rfl⟩ : syracuseStep 7695773 = 2885915) B2885915
theorem B1846687 : Blo 1845624 1846687 := bstep (se 1 (by rfl) ⟨1385015, by rfl⟩ : syracuseStep 1846687 = 2770031) B2770031
theorem B4156847 : Blo 1845624 4156847 := bstep (se 1 (by rfl) ⟨3117635, by rfl⟩ : syracuseStep 4156847 = 6235271) B6235271
theorem B5918177 : Blo 1845624 5918177 := bstep (se 2 (by rfl) ⟨2219316, by rfl⟩ : syracuseStep 5918177 = 4438633) B4438633
theorem B1846815 : Blo 1845624 1846815 := bstep (se 1 (by rfl) ⟨1385111, by rfl⟩ : syracuseStep 1846815 = 2770223) B2770223
theorem B4673153 : Blo 1845624 4673153 := bstep (se 2 (by rfl) ⟨1752432, by rfl⟩ : syracuseStep 4673153 = 3504865) B3504865
theorem B1846951 : Blo 1845624 1846951 := bstep (se 1 (by rfl) ⟨1385213, by rfl⟩ : syracuseStep 1846951 = 2770427) B2770427
theorem B4157099 : Blo 1845624 4157099 := bstep (se 1 (by rfl) ⟨3117824, by rfl⟩ : syracuseStep 4157099 = 6235649) B6235649
theorem B1846975 : Blo 1845624 1846975 := bstep (se 1 (by rfl) ⟨1385231, by rfl⟩ : syracuseStep 1846975 = 2770463) B2770463
theorem B42659561 : Blo 1845624 42659561 := bstep (se 2 (by rfl) ⟨15997335, by rfl⟩ : syracuseStep 42659561 = 31994671) B31994671
theorem B1847071 : Blo 1845624 1847071 := bstep (se 1 (by rfl) ⟨1385303, by rfl⟩ : syracuseStep 1847071 = 2770607) B2770607
theorem B10514231 : Blo 1845624 10514231 := bstep (se 1 (by rfl) ⟨7885673, by rfl⟩ : syracuseStep 10514231 = 15771347) B15771347
theorem B18960209 : Blo 1845624 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B1847151 : Blo 1845624 1847151 := bstep (se 1 (by rfl) ⟨1385363, by rfl⟩ : syracuseStep 1847151 = 2770727) B2770727
theorem B3117035 : Blo 1845624 3117035 := bstep (se 1 (by rfl) ⟨2337776, by rfl⟩ : syracuseStep 3117035 = 4675553) B4675553
theorem B25268233 : Blo 1845624 25268233 := bstep (se 2 (by rfl) ⟨9475587, by rfl⟩ : syracuseStep 25268233 = 18951175) B18951175
theorem B1847519 : Blo 1845624 1847519 := bstep (se 1 (by rfl) ⟨1385639, by rfl⟩ : syracuseStep 1847519 = 2771279) B2771279
theorem B19214567 : Blo 1845624 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B6230249 : Blo 1845624 6230249 := bstep (se 2 (by rfl) ⟨2336343, by rfl⟩ : syracuseStep 6230249 = 4672687) B4672687
theorem B1847551 : Blo 1845624 1847551 := bstep (se 1 (by rfl) ⟨1385663, by rfl⟩ : syracuseStep 1847551 = 2771327) B2771327
theorem B20803841 : Blo 1845624 20803841 := bstep (se 2 (by rfl) ⟨7801440, by rfl⟩ : syracuseStep 20803841 = 15602881) B15602881
theorem B9351449 : Blo 1845624 9351449 := bstep (se 2 (by rfl) ⟨3506793, by rfl⟩ : syracuseStep 9351449 = 7013587) B7013587
theorem B1847579 : Blo 1845624 1847579 := bstep (se 1 (by rfl) ⟨1385684, by rfl⟩ : syracuseStep 1847579 = 2771369) B2771369
theorem B17756495 : Blo 1845624 17756495 := bstep (se 1 (by rfl) ⟨13317371, by rfl⟩ : syracuseStep 17756495 = 26634743) B26634743
theorem B4673963 : Blo 1845624 4673963 := bstep (se 1 (by rfl) ⟨3505472, by rfl⟩ : syracuseStep 4673963 = 7010945) B7010945
theorem B6656507 : Blo 1845624 6656507 := bstep (se 1 (by rfl) ⟨4992380, by rfl⟩ : syracuseStep 6656507 = 9984761) B9984761
theorem B15995389 : Blo 1845624 15995389 := bstep (se 3 (by rfl) ⟨2999135, by rfl⟩ : syracuseStep 15995389 = 5998271) B5998271
theorem B101093939 : Blo 1845624 101093939 := bstep (se 1 (by rfl) ⟨75820454, by rfl⟩ : syracuseStep 101093939 = 151640909) B151640909
theorem B31208489 : Blo 1845624 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B11228381 : Blo 1845624 11228381 := bstep (se 3 (by rfl) ⟨2105321, by rfl⟩ : syracuseStep 11228381 = 4210643) B4210643
theorem B6231275 : Blo 1845624 6231275 := bstep (se 1 (by rfl) ⟨4673456, by rfl⟩ : syracuseStep 6231275 = 9346913) B9346913
theorem B2077951 : Blo 1845624 2077951 := bstep (se 1 (by rfl) ⟨1558463, by rfl⟩ : syracuseStep 2077951 = 3116927) B3116927
theorem B5256569 : Blo 1845624 5256569 := bstep (se 2 (by rfl) ⟨1971213, by rfl⟩ : syracuseStep 5256569 = 3942427) B3942427
theorem B29947481 : Blo 1845624 29947481 := bstep (se 2 (by rfl) ⟨11230305, by rfl⟩ : syracuseStep 29947481 = 22460611) B22460611
theorem B17741537 : Blo 1845624 17741537 := bstep (se 2 (by rfl) ⟨6653076, by rfl⟩ : syracuseStep 17741537 = 13306153) B13306153
theorem B46167821 : Blo 1845624 46167821 := bstep (se 3 (by rfl) ⟨8656466, by rfl⟩ : syracuseStep 46167821 = 17312933) B17312933
theorem B7886717 : Blo 1845624 7886717 := bstep (se 3 (by rfl) ⟨1478759, by rfl⟩ : syracuseStep 7886717 = 2957519) B2957519
theorem B3503999 : Blo 1845624 3503999 := bstep (se 1 (by rfl) ⟨2627999, by rfl⟩ : syracuseStep 3503999 = 5255999) B5255999
theorem B9344969 : Blo 1845624 9344969 := bstep (se 2 (by rfl) ⟨3504363, by rfl⟩ : syracuseStep 9344969 = 7008727) B7008727
theorem B15767723 : Blo 1845624 15767723 := bstep (se 1 (by rfl) ⟨11825792, by rfl⟩ : syracuseStep 15767723 = 23651585) B23651585
theorem B6232247 : Blo 1845624 6232247 := bstep (se 1 (by rfl) ⟨4674185, by rfl⟩ : syracuseStep 6232247 = 9348371) B9348371
theorem B10516715 : Blo 1845624 10516715 := bstep (se 1 (by rfl) ⟨7887536, by rfl⟩ : syracuseStep 10516715 = 15775073) B15775073
theorem B67385753 : Blo 1845624 67385753 := bstep (se 2 (by rfl) ⟨25269657, by rfl⟩ : syracuseStep 67385753 = 50539315) B50539315
theorem B33700315 : Blo 1845624 33700315 := bstep (se 1 (by rfl) ⟨25275236, by rfl⟩ : syracuseStep 33700315 = 50550473) B50550473
theorem B72948275 : Blo 1845624 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B7010975 : Blo 1845624 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B5257993 : Blo 1845624 5257993 := bstep (se 2 (by rfl) ⟨1971747, by rfl⟩ : syracuseStep 5257993 = 3943495) B3943495
theorem B5258141 : Blo 1845624 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B8870867 : Blo 1845624 8870867 := bstep (se 1 (by rfl) ⟨6653150, by rfl⟩ : syracuseStep 8870867 = 13306301) B13306301
theorem B7994375 : Blo 1845624 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B10517647 : Blo 1845624 10517647 := bstep (se 1 (by rfl) ⟨7888235, by rfl⟩ : syracuseStep 10517647 = 15776471) B15776471
theorem B14024015 : Blo 1845624 14024015 := bstep (se 1 (by rfl) ⟨10518011, by rfl⟩ : syracuseStep 14024015 = 21036023) B21036023
theorem B3505655 : Blo 1845624 3505655 := bstep (se 1 (by rfl) ⟨2629241, by rfl⟩ : syracuseStep 3505655 = 5258483) B5258483
theorem B7888441 : Blo 1845624 7888441 := bstep (se 2 (by rfl) ⟨2958165, by rfl⟩ : syracuseStep 7888441 = 5916331) B5916331
theorem B2768603 : Blo 1845624 2768603 := bstep (se 1 (by rfl) ⟨2076452, by rfl⟩ : syracuseStep 2768603 = 4152905) B4152905
theorem B14016239 : Blo 1845624 14016239 := bstep (se 1 (by rfl) ⟨10512179, by rfl⟩ : syracuseStep 14016239 = 21024359) B21024359
theorem B15769363 : Blo 1845624 15769363 := bstep (se 1 (by rfl) ⟨11827022, by rfl⟩ : syracuseStep 15769363 = 23654045) B23654045
theorem B2768873 : Blo 1845624 2768873 := bstep (se 2 (by rfl) ⟨1038327, by rfl⟩ : syracuseStep 2768873 = 2076655) B2076655
theorem B2769023 : Blo 1845624 2769023 := bstep (se 1 (by rfl) ⟨2076767, by rfl⟩ : syracuseStep 2769023 = 4153535) B4153535
theorem B4153499 : Blo 1845624 4153499 := bstep (se 1 (by rfl) ⟨3115124, by rfl⟩ : syracuseStep 4153499 = 6230249) B6230249
theorem B13869227 : Blo 1845624 13869227 := bstep (se 1 (by rfl) ⟨10401920, by rfl⟩ : syracuseStep 13869227 = 20803841) B20803841
theorem B6234299 : Blo 1845624 6234299 := bstep (se 1 (by rfl) ⟨4675724, by rfl⟩ : syracuseStep 6234299 = 9351449) B9351449
theorem B11837663 : Blo 1845624 11837663 := bstep (se 1 (by rfl) ⟨8878247, by rfl⟩ : syracuseStep 11837663 = 17756495) B17756495
theorem B7012601 : Blo 1845624 7012601 := bstep (se 2 (by rfl) ⟨2629725, by rfl⟩ : syracuseStep 7012601 = 5259451) B5259451
theorem B67395959 : Blo 1845624 67395959 := bstep (se 1 (by rfl) ⟨50546969, by rfl⟩ : syracuseStep 67395959 = 101093939) B101093939
theorem B25264727 : Blo 1845624 25264727 := bstep (se 1 (by rfl) ⟨18948545, by rfl⟩ : syracuseStep 25264727 = 37897091) B37897091
theorem B44933753 : Blo 1845624 44933753 := bstep (se 2 (by rfl) ⟨16850157, by rfl⟩ : syracuseStep 44933753 = 33700315) B33700315
theorem B2769575 : Blo 1845624 2769575 := bstep (se 1 (by rfl) ⟨2077181, by rfl⟩ : syracuseStep 2769575 = 4154363) B4154363
theorem B2769647 : Blo 1845624 2769647 := bstep (se 1 (by rfl) ⟨2077235, by rfl⟩ : syracuseStep 2769647 = 4154471) B4154471
theorem B2769695 : Blo 1845624 2769695 := bstep (se 1 (by rfl) ⟨2077271, by rfl⟩ : syracuseStep 2769695 = 4154543) B4154543
theorem B4154183 : Blo 1845624 4154183 := bstep (se 1 (by rfl) ⟨3115637, by rfl⟩ : syracuseStep 4154183 = 6231275) B6231275
theorem B19964987 : Blo 1845624 19964987 := bstep (se 1 (by rfl) ⟨14973740, by rfl⟩ : syracuseStep 19964987 = 29947481) B29947481
theorem B14017697 : Blo 1845624 14017697 := bstep (se 2 (by rfl) ⟨5256636, by rfl⟩ : syracuseStep 14017697 = 10513273) B10513273
theorem B30778547 : Blo 1845624 30778547 := bstep (se 1 (by rfl) ⟨23083910, by rfl⟩ : syracuseStep 30778547 = 46167821) B46167821
theorem B10511815 : Blo 1845624 10511815 := bstep (se 1 (by rfl) ⟨7883861, by rfl⟩ : syracuseStep 10511815 = 15767723) B15767723
theorem B4154831 : Blo 1845624 4154831 := bstep (se 1 (by rfl) ⟨3116123, by rfl⟩ : syracuseStep 4154831 = 6232247) B6232247
theorem B2770601 : Blo 1845624 2770601 := bstep (se 2 (by rfl) ⟨1038975, by rfl⟩ : syracuseStep 2770601 = 2077951) B2077951
theorem B2770811 : Blo 1845624 2770811 := bstep (se 1 (by rfl) ⟨2078108, by rfl⟩ : syracuseStep 2770811 = 4156217) B4156217
theorem B9349343 : Blo 1845624 9349343 := bstep (se 1 (by rfl) ⟨7012007, by rfl⟩ : syracuseStep 9349343 = 14024015) B14024015
theorem B5130515 : Blo 1845624 5130515 := bstep (se 1 (by rfl) ⟨3847886, by rfl⟩ : syracuseStep 5130515 = 7695773) B7695773
theorem B2771231 : Blo 1845624 2771231 := bstep (se 1 (by rfl) ⟨2078423, by rfl⟩ : syracuseStep 2771231 = 4156847) B4156847
theorem B2337103 : Blo 1845624 2337103 := bstep (se 1 (by rfl) ⟨1752827, by rfl⟩ : syracuseStep 2337103 = 3505655) B3505655
theorem B3115435 : Blo 1845624 3115435 := bstep (se 1 (by rfl) ⟨2336576, by rfl⟩ : syracuseStep 3115435 = 4673153) B4673153
theorem B2771399 : Blo 1845624 2771399 := bstep (se 1 (by rfl) ⟨2078549, by rfl⟩ : syracuseStep 2771399 = 4157099) B4157099
theorem B1845735 : Blo 1845624 1845735 := bstep (se 1 (by rfl) ⟨1384301, by rfl⟩ : syracuseStep 1845735 = 2768603) B2768603
theorem B10521089 : Blo 1845624 10521089 := bstep (se 2 (by rfl) ⟨3945408, by rfl⟩ : syracuseStep 10521089 = 7890817) B7890817
theorem B14027417 : Blo 1845624 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B1845915 : Blo 1845624 1845915 := bstep (se 1 (by rfl) ⟨1384436, by rfl⟩ : syracuseStep 1845915 = 2768873) B2768873
theorem B4434713 : Blo 1845624 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B1846043 : Blo 1845624 1846043 := bstep (se 1 (by rfl) ⟨1384532, by rfl⟩ : syracuseStep 1846043 = 2769065) B2769065
theorem B3115975 : Blo 1845624 3115975 := bstep (se 1 (by rfl) ⟨2336981, by rfl⟩ : syracuseStep 3115975 = 4673963) B4673963
theorem B1846255 : Blo 1845624 1846255 := bstep (se 1 (by rfl) ⟨1384691, by rfl⟩ : syracuseStep 1846255 = 2769383) B2769383
theorem B1846439 : Blo 1845624 1846439 := bstep (se 1 (by rfl) ⟨1384829, by rfl⟩ : syracuseStep 1846439 = 2769659) B2769659
theorem B21327185 : Blo 1845624 21327185 := bstep (se 2 (by rfl) ⟨7997694, by rfl⟩ : syracuseStep 21327185 = 15995389) B15995389
theorem B3157375 : Blo 1845624 3157375 := bstep (se 1 (by rfl) ⟨2368031, by rfl⟩ : syracuseStep 3157375 = 4736063) B4736063
theorem B1846735 : Blo 1845624 1846735 := bstep (se 1 (by rfl) ⟨1385051, by rfl⟩ : syracuseStep 1846735 = 2770103) B2770103
theorem B8990183 : Blo 1845624 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B1846831 : Blo 1845624 1846831 := bstep (se 1 (by rfl) ⟨1385123, by rfl⟩ : syracuseStep 1846831 = 2770247) B2770247
theorem B1846895 : Blo 1845624 1846895 := bstep (se 1 (by rfl) ⟨1385171, by rfl⟩ : syracuseStep 1846895 = 2770343) B2770343
theorem B1847015 : Blo 1845624 1847015 := bstep (se 1 (by rfl) ⟨1385261, by rfl⟩ : syracuseStep 1847015 = 2770523) B2770523
theorem B14970653 : Blo 1845624 14970653 := bstep (se 3 (by rfl) ⟨2806997, by rfl⟩ : syracuseStep 14970653 = 5613995) B5613995
theorem B6229979 : Blo 1845624 6229979 := bstep (se 1 (by rfl) ⟨4672484, by rfl⟩ : syracuseStep 6229979 = 9344969) B9344969
theorem B1847327 : Blo 1845624 1847327 := bstep (se 1 (by rfl) ⟨1385495, by rfl⟩ : syracuseStep 1847327 = 2770991) B2770991
theorem B6320263 : Blo 1845624 6320263 := bstep (se 1 (by rfl) ⟨4740197, by rfl⟩ : syracuseStep 6320263 = 9480395) B9480395
theorem B1847503 : Blo 1845624 1847503 := bstep (se 1 (by rfl) ⟨1385627, by rfl⟩ : syracuseStep 1847503 = 2771255) B2771255
theorem B1847623 : Blo 1845624 1847623 := bstep (se 1 (by rfl) ⟨1385717, by rfl⟩ : syracuseStep 1847623 = 2771435) B2771435
theorem B48632183 : Blo 1845624 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B4673983 : Blo 1845624 4673983 := bstep (se 1 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 4673983 = 7010975) B7010975
theorem B5329583 : Blo 1845624 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B3945451 : Blo 1845624 3945451 := bstep (se 1 (by rfl) ⟨2959088, by rfl⟩ : syracuseStep 3945451 = 5918177) B5918177
theorem B9343997 : Blo 1845624 9343997 := bstep (se 3 (by rfl) ⟨1751999, by rfl⟩ : syracuseStep 9343997 = 3503999) B3503999
theorem B21025817 : Blo 1845624 21025817 := bstep (se 2 (by rfl) ⟨7884681, by rfl⟩ : syracuseStep 21025817 = 15769363) B15769363
theorem B28439707 : Blo 1845624 28439707 := bstep (se 1 (by rfl) ⟨21329780, by rfl⟩ : syracuseStep 28439707 = 42659561) B42659561
theorem B9344159 : Blo 1845624 9344159 := bstep (se 1 (by rfl) ⟨7008119, by rfl⟩ : syracuseStep 9344159 = 14016239) B14016239
theorem B7009487 : Blo 1845624 7009487 := bstep (se 1 (by rfl) ⟨5257115, by rfl⟩ : syracuseStep 7009487 = 10514231) B10514231
theorem B2078023 : Blo 1845624 2078023 := bstep (se 1 (by rfl) ⟨1558517, by rfl⟩ : syracuseStep 2078023 = 3117035) B3117035
theorem B33690977 : Blo 1845624 33690977 := bstep (se 2 (by rfl) ⟨12634116, by rfl⟩ : syracuseStep 33690977 = 25268233) B25268233
theorem B12809711 : Blo 1845624 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B7886443 : Blo 1845624 7886443 := bstep (se 1 (by rfl) ⟨5914832, by rfl⟩ : syracuseStep 7886443 = 11829665) B11829665
theorem B4437671 : Blo 1845624 4437671 := bstep (se 1 (by rfl) ⟨3328253, by rfl⟩ : syracuseStep 4437671 = 6656507) B6656507
theorem B8427343 : Blo 1845624 8427343 := bstep (se 1 (by rfl) ⟨6320507, by rfl⟩ : syracuseStep 8427343 = 12641015) B12641015
theorem B20805659 : Blo 1845624 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B7485587 : Blo 1845624 7485587 := bstep (se 1 (by rfl) ⟨5614190, by rfl⟩ : syracuseStep 7485587 = 11228381) B11228381
theorem B3504379 : Blo 1845624 3504379 := bstep (se 1 (by rfl) ⟨2628284, by rfl⟩ : syracuseStep 3504379 = 5256569) B5256569
theorem B7010657 : Blo 1845624 7010657 := bstep (se 2 (by rfl) ⟨2628996, by rfl⟩ : syracuseStep 7010657 = 5257993) B5257993
theorem B11827691 : Blo 1845624 11827691 := bstep (se 1 (by rfl) ⟨8870768, by rfl⟩ : syracuseStep 11827691 = 17741537) B17741537
theorem B5257811 : Blo 1845624 5257811 := bstep (se 1 (by rfl) ⟨3943358, by rfl⟩ : syracuseStep 5257811 = 7886717) B7886717
theorem B4676201 : Blo 1845624 4676201 := bstep (se 2 (by rfl) ⟨1753575, by rfl⟩ : syracuseStep 4676201 = 3507151) B3507151
theorem B9345779 : Blo 1845624 9345779 := bstep (se 1 (by rfl) ⟨7009334, by rfl⟩ : syracuseStep 9345779 = 14018669) B14018669
theorem B7011143 : Blo 1845624 7011143 := bstep (se 1 (by rfl) ⟨5258357, by rfl⟩ : syracuseStep 7011143 = 10516715) B10516715
theorem B2628455 : Blo 1845624 2628455 := bstep (se 1 (by rfl) ⟨1971341, by rfl⟩ : syracuseStep 2628455 = 3942683) B3942683
theorem B14023529 : Blo 1845624 14023529 := bstep (se 2 (by rfl) ⟨5258823, by rfl⟩ : syracuseStep 14023529 = 10517647) B10517647
theorem B44923835 : Blo 1845624 44923835 := bstep (se 1 (by rfl) ⟨33692876, by rfl⟩ : syracuseStep 44923835 = 67385753) B67385753
theorem B5913769 : Blo 1845624 5913769 := bstep (se 2 (by rfl) ⟨2217663, by rfl⟩ : syracuseStep 5913769 = 4435327) B4435327
theorem B59890913 : Blo 1845624 59890913 := bstep (se 2 (by rfl) ⟨22459092, by rfl⟩ : syracuseStep 59890913 = 44918185) B44918185
theorem B3505427 : Blo 1845624 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B5913911 : Blo 1845624 5913911 := bstep (se 1 (by rfl) ⟨4435433, by rfl⟩ : syracuseStep 5913911 = 8870867) B8870867
theorem B10517921 : Blo 1845624 10517921 := bstep (se 2 (by rfl) ⟨3944220, by rfl⟩ : syracuseStep 10517921 = 7888441) B7888441
theorem B12640139 : Blo 1845624 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B2768999 : Blo 1845624 2768999 := bstep (se 1 (by rfl) ⟨2076749, by rfl⟩ : syracuseStep 2768999 = 4153499) B4153499
theorem B16843151 : Blo 1845624 16843151 := bstep (se 1 (by rfl) ⟨12632363, by rfl⟩ : syracuseStep 16843151 = 25264727) B25264727
theorem B82076125 : Blo 1845624 82076125 := bstep (se 3 (by rfl) ⟨15389273, by rfl⟩ : syracuseStep 82076125 = 30778547) B30778547
theorem B2769455 : Blo 1845624 2769455 := bstep (se 1 (by rfl) ⟨2077091, by rfl⟩ : syracuseStep 2769455 = 4154183) B4154183
theorem B4153913 : Blo 1845624 4153913 := bstep (se 2 (by rfl) ⟨1557717, by rfl⟩ : syracuseStep 4153913 = 3115435) B3115435
theorem B14017211 : Blo 1845624 14017211 := bstep (se 1 (by rfl) ⟨10512908, by rfl⟩ : syracuseStep 14017211 = 21025817) B21025817
theorem B2769887 : Blo 1845624 2769887 := bstep (se 1 (by rfl) ⟨2077415, by rfl⟩ : syracuseStep 2769887 = 4154831) B4154831
theorem B4154633 : Blo 1845624 4154633 := bstep (se 2 (by rfl) ⟨1557987, by rfl⟩ : syracuseStep 4154633 = 3115975) B3115975
theorem B5260601 : Blo 1845624 5260601 := bstep (se 2 (by rfl) ⟨1972725, by rfl⟩ : syracuseStep 5260601 = 3945451) B3945451
theorem B13870439 : Blo 1845624 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B4990391 : Blo 1845624 4990391 := bstep (se 1 (by rfl) ⟨3742793, by rfl⟩ : syracuseStep 4990391 = 7485587) B7485587
theorem B7014059 : Blo 1845624 7014059 := bstep (se 1 (by rfl) ⟨5260544, by rfl⟩ : syracuseStep 7014059 = 10521089) B10521089
theorem B2770697 : Blo 1845624 2770697 := bstep (se 2 (by rfl) ⟨1039011, by rfl⟩ : syracuseStep 2770697 = 2078023) B2078023
theorem B9349019 : Blo 1845624 9349019 := bstep (se 1 (by rfl) ⟨7011764, by rfl⟩ : syracuseStep 9349019 = 14023529) B14023529
theorem B2336951 : Blo 1845624 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B3942607 : Blo 1845624 3942607 := bstep (se 1 (by rfl) ⟨2956955, by rfl⟩ : syracuseStep 3942607 = 5913911) B5913911
theorem B9980435 : Blo 1845624 9980435 := bstep (se 1 (by rfl) ⟨7485326, by rfl⟩ : syracuseStep 9980435 = 14970653) B14970653
theorem B1846015 : Blo 1845624 1846015 := bstep (se 1 (by rfl) ⟨1384511, by rfl⟩ : syracuseStep 1846015 = 2769023) B2769023
theorem B4156199 : Blo 1845624 4156199 := bstep (se 1 (by rfl) ⟨3117149, by rfl⟩ : syracuseStep 4156199 = 6234299) B6234299
theorem B7891775 : Blo 1845624 7891775 := bstep (se 1 (by rfl) ⟨5918831, by rfl⟩ : syracuseStep 7891775 = 11837663) B11837663
theorem B4672505 : Blo 1845624 4672505 := bstep (se 2 (by rfl) ⟨1752189, by rfl⟩ : syracuseStep 4672505 = 3504379) B3504379
theorem B3116137 : Blo 1845624 3116137 := bstep (se 2 (by rfl) ⟨1168551, by rfl⟩ : syracuseStep 3116137 = 2337103) B2337103
theorem B1846383 : Blo 1845624 1846383 := bstep (se 1 (by rfl) ⟨1384787, by rfl⟩ : syracuseStep 1846383 = 2769575) B2769575
theorem B1846431 : Blo 1845624 1846431 := bstep (se 1 (by rfl) ⟨1384823, by rfl⟩ : syracuseStep 1846431 = 2769647) B2769647
theorem B1846463 : Blo 1845624 1846463 := bstep (se 1 (by rfl) ⟨1384847, by rfl⟩ : syracuseStep 1846463 = 2769695) B2769695
theorem B6229331 : Blo 1845624 6229331 := bstep (se 1 (by rfl) ⟨4671998, by rfl⟩ : syracuseStep 6229331 = 9343997) B9343997
theorem B6229439 : Blo 1845624 6229439 := bstep (se 1 (by rfl) ⟨4672079, by rfl⟩ : syracuseStep 6229439 = 9344159) B9344159
theorem B4672991 : Blo 1845624 4672991 := bstep (se 1 (by rfl) ⟨3504743, by rfl⟩ : syracuseStep 4672991 = 7009487) B7009487
theorem B1847067 : Blo 1845624 1847067 := bstep (se 1 (by rfl) ⟨1385300, by rfl⟩ : syracuseStep 1847067 = 2770601) B2770601
theorem B1847207 : Blo 1845624 1847207 := bstep (se 1 (by rfl) ⟨1385405, by rfl⟩ : syracuseStep 1847207 = 2770811) B2770811
theorem B3420343 : Blo 1845624 3420343 := bstep (se 1 (by rfl) ⟨2565257, by rfl⟩ : syracuseStep 3420343 = 5130515) B5130515
theorem B1847487 : Blo 1845624 1847487 := bstep (se 1 (by rfl) ⟨1385615, by rfl⟩ : syracuseStep 1847487 = 2771231) B2771231
theorem B7885025 : Blo 1845624 7885025 := bstep (se 2 (by rfl) ⟨2956884, by rfl⟩ : syracuseStep 7885025 = 5913769) B5913769
theorem B4673771 : Blo 1845624 4673771 := bstep (se 1 (by rfl) ⟨3505328, by rfl⟩ : syracuseStep 4673771 = 7010657) B7010657
theorem B1847599 : Blo 1845624 1847599 := bstep (se 1 (by rfl) ⟨1385699, by rfl⟩ : syracuseStep 1847599 = 2771399) B2771399
theorem B7885127 : Blo 1845624 7885127 := bstep (se 1 (by rfl) ⟨5913845, by rfl⟩ : syracuseStep 7885127 = 11827691) B11827691
theorem B3117467 : Blo 1845624 3117467 := bstep (se 1 (by rfl) ⟨2338100, by rfl⟩ : syracuseStep 3117467 = 4676201) B4676201
theorem B9351611 : Blo 1845624 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B11833789 : Blo 1845624 11833789 := bstep (se 3 (by rfl) ⟨2218835, by rfl⟩ : syracuseStep 11833789 = 4437671) B4437671
theorem B6230519 : Blo 1845624 6230519 := bstep (se 1 (by rfl) ⟨4672889, by rfl⟩ : syracuseStep 6230519 = 9345779) B9345779
theorem B4674095 : Blo 1845624 4674095 := bstep (se 1 (by rfl) ⟨3505571, by rfl⟩ : syracuseStep 4674095 = 7011143) B7011143
theorem B10515257 : Blo 1845624 10515257 := bstep (se 2 (by rfl) ⟨3943221, by rfl⟩ : syracuseStep 10515257 = 7886443) B7886443
theorem B14218123 : Blo 1845624 14218123 := bstep (se 1 (by rfl) ⟨10663592, by rfl⟩ : syracuseStep 14218123 = 21327185) B21327185
theorem B7009213 : Blo 1845624 7009213 := bstep (se 3 (by rfl) ⟨1314227, by rfl⟩ : syracuseStep 7009213 = 2628455) B2628455
theorem B5993455 : Blo 1845624 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B11236457 : Blo 1845624 11236457 := bstep (se 2 (by rfl) ⟨4213671, by rfl⟩ : syracuseStep 11236457 = 8427343) B8427343
theorem B8426759 : Blo 1845624 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B4675067 : Blo 1845624 4675067 := bstep (se 1 (by rfl) ⟨3506300, by rfl⟩ : syracuseStep 4675067 = 7012601) B7012601
theorem B8427017 : Blo 1845624 8427017 := bstep (se 2 (by rfl) ⟨3160131, by rfl⟩ : syracuseStep 8427017 = 6320263) B6320263
theorem B32421455 : Blo 1845624 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B44930639 : Blo 1845624 44930639 := bstep (se 1 (by rfl) ⟨33697979, by rfl⟩ : syracuseStep 44930639 = 67395959) B67395959
theorem B29955835 : Blo 1845624 29955835 := bstep (se 1 (by rfl) ⟨22466876, by rfl⟩ : syracuseStep 29955835 = 44933753) B44933753
theorem B36984605 : Blo 1845624 36984605 := bstep (se 3 (by rfl) ⟨6934613, by rfl⟩ : syracuseStep 36984605 = 13869227) B13869227
theorem B3553055 : Blo 1845624 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B6231977 : Blo 1845624 6231977 := bstep (se 2 (by rfl) ⟨2336991, by rfl⟩ : syracuseStep 6231977 = 4673983) B4673983
theorem B13309991 : Blo 1845624 13309991 := bstep (se 1 (by rfl) ⟨9982493, by rfl⟩ : syracuseStep 13309991 = 19964987) B19964987
theorem B9345131 : Blo 1845624 9345131 := bstep (se 1 (by rfl) ⟨7008848, by rfl⟩ : syracuseStep 9345131 = 14017697) B14017697
theorem B22460651 : Blo 1845624 22460651 := bstep (se 1 (by rfl) ⟨16845488, by rfl⟩ : syracuseStep 22460651 = 33690977) B33690977
theorem B34159229 : Blo 1845624 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B6232895 : Blo 1845624 6232895 := bstep (se 1 (by rfl) ⟨4674671, by rfl⟩ : syracuseStep 6232895 = 9349343) B9349343
theorem B37919609 : Blo 1845624 37919609 := bstep (se 2 (by rfl) ⟨14219853, by rfl⟩ : syracuseStep 37919609 = 28439707) B28439707
theorem B3505207 : Blo 1845624 3505207 := bstep (se 1 (by rfl) ⟨2628905, by rfl⟩ : syracuseStep 3505207 = 5257811) B5257811
theorem B4209833 : Blo 1845624 4209833 := bstep (se 2 (by rfl) ⟨1578687, by rfl⟩ : syracuseStep 4209833 = 3157375) B3157375
theorem B2956475 : Blo 1845624 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B14015753 : Blo 1845624 14015753 := bstep (se 2 (by rfl) ⟨5255907, by rfl⟩ : syracuseStep 14015753 = 10511815) B10511815
theorem B29949223 : Blo 1845624 29949223 := bstep (se 1 (by rfl) ⟨22461917, by rfl⟩ : syracuseStep 29949223 = 44923835) B44923835
theorem B39927275 : Blo 1845624 39927275 := bstep (se 1 (by rfl) ⟨29945456, by rfl⟩ : syracuseStep 39927275 = 59890913) B59890913
theorem B7011947 : Blo 1845624 7011947 := bstep (se 1 (by rfl) ⟨5258960, by rfl⟩ : syracuseStep 7011947 = 10517921) B10517921
theorem B4153319 : Blo 1845624 4153319 := bstep (se 1 (by rfl) ⟨3114989, by rfl⟩ : syracuseStep 4153319 = 6229979) B6229979
theorem B6234407 : Blo 1845624 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B4153679 : Blo 1845624 4153679 := bstep (se 1 (by rfl) ⟨3115259, by rfl⟩ : syracuseStep 4153679 = 6230519) B6230519
theorem B2769275 : Blo 1845624 2769275 := bstep (se 1 (by rfl) ⟨2076956, by rfl⟩ : syracuseStep 2769275 = 4153913) B4153913
theorem B15778385 : Blo 1845624 15778385 := bstep (se 2 (by rfl) ⟨5916894, by rfl⟩ : syracuseStep 15778385 = 11833789) B11833789
theorem B22471357 : Blo 1845624 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B2769755 : Blo 1845624 2769755 := bstep (se 1 (by rfl) ⟨2077316, by rfl⟩ : syracuseStep 2769755 = 4154633) B4154633
theorem B3507067 : Blo 1845624 3507067 := bstep (se 1 (by rfl) ⟨2630300, by rfl⟩ : syracuseStep 3507067 = 5260601) B5260601
theorem B3326927 : Blo 1845624 3326927 := bstep (se 1 (by rfl) ⟨2495195, by rfl⟩ : syracuseStep 3326927 = 4990391) B4990391
theorem B18957497 : Blo 1845624 18957497 := bstep (se 2 (by rfl) ⟨7109061, by rfl⟩ : syracuseStep 18957497 = 14218123) B14218123
theorem B2368703 : Blo 1845624 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B4154651 : Blo 1845624 4154651 := bstep (se 1 (by rfl) ⟨3115988, by rfl⟩ : syracuseStep 4154651 = 6231977) B6231977
theorem B8873327 : Blo 1845624 8873327 := bstep (se 1 (by rfl) ⟨6654995, by rfl⟩ : syracuseStep 8873327 = 13309991) B13309991
theorem B4154849 : Blo 1845624 4154849 := bstep (se 2 (by rfl) ⟨1558068, by rfl⟩ : syracuseStep 4154849 = 3116137) B3116137
theorem B2770799 : Blo 1845624 2770799 := bstep (se 1 (by rfl) ⟨2078099, by rfl⟩ : syracuseStep 2770799 = 4156199) B4156199
theorem B4155263 : Blo 1845624 4155263 := bstep (se 1 (by rfl) ⟨3116447, by rfl⟩ : syracuseStep 4155263 = 6232895) B6232895
theorem B5261183 : Blo 1845624 5261183 := bstep (se 1 (by rfl) ⟨3945887, by rfl⟩ : syracuseStep 5261183 = 7891775) B7891775
theorem B3115003 : Blo 1845624 3115003 := bstep (se 1 (by rfl) ⟨2336252, by rfl⟩ : syracuseStep 3115003 = 4672505) B4672505
theorem B98625613 : Blo 1845624 98625613 := bstep (se 3 (by rfl) ⟨18492302, by rfl⟩ : syracuseStep 98625613 = 36984605) B36984605
theorem B3115327 : Blo 1845624 3115327 := bstep (se 1 (by rfl) ⟨2336495, by rfl⟩ : syracuseStep 3115327 = 4672991) B4672991
theorem B26618183 : Blo 1845624 26618183 := bstep (se 1 (by rfl) ⟨19963637, by rfl⟩ : syracuseStep 26618183 = 39927275) B39927275
theorem B1845999 : Blo 1845624 1845999 := bstep (se 1 (by rfl) ⟨1384499, by rfl⟩ : syracuseStep 1845999 = 2768999) B2768999
theorem B3115847 : Blo 1845624 3115847 := bstep (se 1 (by rfl) ⟨2336885, by rfl⟩ : syracuseStep 3115847 = 4673771) B4673771
theorem B1846303 : Blo 1845624 1846303 := bstep (se 1 (by rfl) ⟨1384727, by rfl⟩ : syracuseStep 1846303 = 2769455) B2769455
theorem B3116063 : Blo 1845624 3116063 := bstep (se 1 (by rfl) ⟨2337047, by rfl⟩ : syracuseStep 3116063 = 4674095) B4674095
theorem B11226221 : Blo 1845624 11226221 := bstep (se 3 (by rfl) ⟨2104916, by rfl⟩ : syracuseStep 11226221 = 4209833) B4209833
theorem B1846591 : Blo 1845624 1846591 := bstep (se 1 (by rfl) ⟨1384943, by rfl⟩ : syracuseStep 1846591 = 2769887) B2769887
theorem B7490971 : Blo 1845624 7490971 := bstep (se 1 (by rfl) ⟨5618228, by rfl⟩ : syracuseStep 7490971 = 11236457) B11236457
theorem B3116711 : Blo 1845624 3116711 := bstep (se 1 (by rfl) ⟨2337533, by rfl⟩ : syracuseStep 3116711 = 4675067) B4675067
theorem B21614303 : Blo 1845624 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B1847131 : Blo 1845624 1847131 := bstep (se 1 (by rfl) ⟨1385348, by rfl⟩ : syracuseStep 1847131 = 2770697) B2770697
theorem B7991273 : Blo 1845624 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B6230087 : Blo 1845624 6230087 := bstep (se 1 (by rfl) ⟨4672565, by rfl⟩ : syracuseStep 6230087 = 9345131) B9345131
theorem B4673609 : Blo 1845624 4673609 := bstep (se 2 (by rfl) ⟨1752603, by rfl⟩ : syracuseStep 4673609 = 3505207) B3505207
theorem B39932297 : Blo 1845624 39932297 := bstep (se 2 (by rfl) ⟨14974611, by rfl⟩ : syracuseStep 39932297 = 29949223) B29949223
theorem B1970983 : Blo 1845624 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B9343835 : Blo 1845624 9343835 := bstep (se 1 (by rfl) ⟨7007876, by rfl⟩ : syracuseStep 9343835 = 14015753) B14015753
theorem B39941113 : Blo 1845624 39941113 := bstep (se 2 (by rfl) ⟨14977917, by rfl⟩ : syracuseStep 39941113 = 29955835) B29955835
theorem B4674631 : Blo 1845624 4674631 := bstep (se 1 (by rfl) ⟨3505973, by rfl⟩ : syracuseStep 4674631 = 7011947) B7011947
theorem B5256683 : Blo 1845624 5256683 := bstep (se 1 (by rfl) ⟨3942512, by rfl⟩ : syracuseStep 5256683 = 7885025) B7885025
theorem B5256751 : Blo 1845624 5256751 := bstep (se 1 (by rfl) ⟨3942563, by rfl⟩ : syracuseStep 5256751 = 7885127) B7885127
theorem B4560457 : Blo 1845624 4560457 := bstep (se 2 (by rfl) ⟨1710171, by rfl⟩ : syracuseStep 4560457 = 3420343) B3420343
theorem B2078311 : Blo 1845624 2078311 := bstep (se 1 (by rfl) ⟨1558733, by rfl⟩ : syracuseStep 2078311 = 3117467) B3117467
theorem B5256809 : Blo 1845624 5256809 := bstep (se 2 (by rfl) ⟨1971303, by rfl⟩ : syracuseStep 5256809 = 3942607) B3942607
theorem B9344807 : Blo 1845624 9344807 := bstep (se 1 (by rfl) ⟨7008605, by rfl⟩ : syracuseStep 9344807 = 14017211) B14017211
theorem B6231869 : Blo 1845624 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B7010171 : Blo 1845624 7010171 := bstep (se 1 (by rfl) ⟨5257628, by rfl⟩ : syracuseStep 7010171 = 10515257) B10515257
theorem B109434833 : Blo 1845624 109434833 := bstep (se 2 (by rfl) ⟨41038062, by rfl⟩ : syracuseStep 109434833 = 82076125) B82076125
theorem B9246959 : Blo 1845624 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B5618011 : Blo 1845624 5618011 := bstep (se 1 (by rfl) ⟨4213508, by rfl⟩ : syracuseStep 5618011 = 8427017) B8427017
theorem B44915069 : Blo 1845624 44915069 := bstep (se 3 (by rfl) ⟨8421575, by rfl⟩ : syracuseStep 44915069 = 16843151) B16843151
theorem B4676039 : Blo 1845624 4676039 := bstep (se 1 (by rfl) ⟨3507029, by rfl⟩ : syracuseStep 4676039 = 7014059) B7014059
theorem B9345617 : Blo 1845624 9345617 := bstep (se 2 (by rfl) ⟨3504606, by rfl⟩ : syracuseStep 9345617 = 7009213) B7009213
theorem B6232679 : Blo 1845624 6232679 := bstep (se 1 (by rfl) ⟨4674509, by rfl⟩ : syracuseStep 6232679 = 9349019) B9349019
theorem B26614493 : Blo 1845624 26614493 := bstep (se 3 (by rfl) ⟨4990217, by rfl⟩ : syracuseStep 26614493 = 9980435) B9980435
theorem B14973767 : Blo 1845624 14973767 := bstep (se 1 (by rfl) ⟨11230325, by rfl⟩ : syracuseStep 14973767 = 22460651) B22460651
theorem B119815037 : Blo 1845624 119815037 := bstep (se 3 (by rfl) ⟨22465319, by rfl⟩ : syracuseStep 119815037 = 44930639) B44930639
theorem B22772819 : Blo 1845624 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B25279739 : Blo 1845624 25279739 := bstep (se 1 (by rfl) ⟨18959804, by rfl⟩ : syracuseStep 25279739 = 37919609) B37919609
theorem B4152887 : Blo 1845624 4152887 := bstep (se 1 (by rfl) ⟨3114665, by rfl⟩ : syracuseStep 4152887 = 6229331) B6229331
theorem B4152959 : Blo 1845624 4152959 := bstep (se 1 (by rfl) ⟨3114719, by rfl⟩ : syracuseStep 4152959 = 6229439) B6229439
theorem B2768879 : Blo 1845624 2768879 := bstep (se 1 (by rfl) ⟨2076659, by rfl⟩ : syracuseStep 2768879 = 4153319) B4153319
theorem B4153391 : Blo 1845624 4153391 := bstep (se 1 (by rfl) ⟨3115043, by rfl⟩ : syracuseStep 4153391 = 6230087) B6230087
theorem B2769119 : Blo 1845624 2769119 := bstep (se 1 (by rfl) ⟨2076839, by rfl⟩ : syracuseStep 2769119 = 4153679) B4153679
theorem B10518923 : Blo 1845624 10518923 := bstep (se 1 (by rfl) ⟨7889192, by rfl⟩ : syracuseStep 10518923 = 15778385) B15778385
theorem B4153769 : Blo 1845624 4153769 := bstep (se 2 (by rfl) ⟨1557663, by rfl⟩ : syracuseStep 4153769 = 3115327) B3115327
theorem B50553325 : Blo 1845624 50553325 := bstep (se 3 (by rfl) ⟨9478748, by rfl⟩ : syracuseStep 50553325 = 18957497) B18957497
theorem B6316541 : Blo 1845624 6316541 := bstep (se 3 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 6316541 = 2368703) B2368703
theorem B2769767 : Blo 1845624 2769767 := bstep (se 1 (by rfl) ⟨2077325, by rfl⟩ : syracuseStep 2769767 = 4154651) B4154651
theorem B5915551 : Blo 1845624 5915551 := bstep (se 1 (by rfl) ⟨4436663, by rfl⟩ : syracuseStep 5915551 = 8873327) B8873327
theorem B2769899 : Blo 1845624 2769899 := bstep (se 1 (by rfl) ⟨2077424, by rfl⟩ : syracuseStep 2769899 = 4154849) B4154849
theorem B4154579 : Blo 1845624 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B2770175 : Blo 1845624 2770175 := bstep (se 1 (by rfl) ⟨2077631, by rfl⟩ : syracuseStep 2770175 = 4155263) B4155263
theorem B3507455 : Blo 1845624 3507455 := bstep (se 1 (by rfl) ⟨2630591, by rfl⟩ : syracuseStep 3507455 = 5261183) B5261183
theorem B17745455 : Blo 1845624 17745455 := bstep (se 1 (by rfl) ⟨13309091, by rfl⟩ : syracuseStep 17745455 = 26618183) B26618183
theorem B29943379 : Blo 1845624 29943379 := bstep (se 1 (by rfl) ⟨22457534, by rfl⟩ : syracuseStep 29943379 = 44915069) B44915069
theorem B4155119 : Blo 1845624 4155119 := bstep (se 1 (by rfl) ⟨3116339, by rfl⟩ : syracuseStep 4155119 = 6232679) B6232679
theorem B9987961 : Blo 1845624 9987961 := bstep (se 2 (by rfl) ⟨3745485, by rfl⟩ : syracuseStep 9987961 = 7490971) B7490971
theorem B15181879 : Blo 1845624 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B6080609 : Blo 1845624 6080609 := bstep (se 2 (by rfl) ⟨2280228, by rfl⟩ : syracuseStep 6080609 = 4560457) B4560457
theorem B2771081 : Blo 1845624 2771081 := bstep (se 2 (by rfl) ⟨1039155, by rfl⟩ : syracuseStep 2771081 = 2078311) B2078311
theorem B16853159 : Blo 1845624 16853159 := bstep (se 1 (by rfl) ⟨12639869, by rfl⟩ : syracuseStep 16853159 = 25279739) B25279739
theorem B5327515 : Blo 1845624 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B1845919 : Blo 1845624 1845919 := bstep (se 1 (by rfl) ⟨1384439, by rfl⟩ : syracuseStep 1845919 = 2768879) B2768879
theorem B3115739 : Blo 1845624 3115739 := bstep (se 1 (by rfl) ⟨2336804, by rfl⟩ : syracuseStep 3115739 = 4673609) B4673609
theorem B131500817 : Blo 1845624 131500817 := bstep (se 2 (by rfl) ⟨49312806, by rfl⟩ : syracuseStep 131500817 = 98625613) B98625613
theorem B4156271 : Blo 1845624 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B1846183 : Blo 1845624 1846183 := bstep (se 1 (by rfl) ⟨1384637, by rfl⟩ : syracuseStep 1846183 = 2769275) B2769275
theorem B7490681 : Blo 1845624 7490681 := bstep (se 2 (by rfl) ⟨2809005, by rfl⟩ : syracuseStep 7490681 = 5618011) B5618011
theorem B6229223 : Blo 1845624 6229223 := bstep (se 1 (by rfl) ⟨4671917, by rfl⟩ : syracuseStep 6229223 = 9343835) B9343835
theorem B1846503 : Blo 1845624 1846503 := bstep (se 1 (by rfl) ⟨1384877, by rfl⟩ : syracuseStep 1846503 = 2769755) B2769755
theorem B29961809 : Blo 1845624 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B6229871 : Blo 1845624 6229871 := bstep (se 1 (by rfl) ⟨4672403, by rfl⟩ : syracuseStep 6229871 = 9344807) B9344807
theorem B1847199 : Blo 1845624 1847199 := bstep (se 1 (by rfl) ⟨1385399, by rfl⟩ : syracuseStep 1847199 = 2770799) B2770799
theorem B4673447 : Blo 1845624 4673447 := bstep (se 1 (by rfl) ⟨3505085, by rfl⟩ : syracuseStep 4673447 = 7010171) B7010171
theorem B6164639 : Blo 1845624 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B3117359 : Blo 1845624 3117359 := bstep (se 1 (by rfl) ⟨2338019, by rfl⟩ : syracuseStep 3117359 = 4676039) B4676039
theorem B6230411 : Blo 1845624 6230411 := bstep (se 1 (by rfl) ⟨4672808, by rfl⟩ : syracuseStep 6230411 = 9345617) B9345617
theorem B2077231 : Blo 1845624 2077231 := bstep (se 1 (by rfl) ⟨1557923, by rfl⟩ : syracuseStep 2077231 = 3115847) B3115847
theorem B9982511 : Blo 1845624 9982511 := bstep (se 1 (by rfl) ⟨7486883, by rfl⟩ : syracuseStep 9982511 = 14973767) B14973767
theorem B79876691 : Blo 1845624 79876691 := bstep (se 1 (by rfl) ⟨59907518, by rfl⟩ : syracuseStep 79876691 = 119815037) B119815037
theorem B2077375 : Blo 1845624 2077375 := bstep (se 1 (by rfl) ⟨1558031, by rfl⟩ : syracuseStep 2077375 = 3116063) B3116063
theorem B7009001 : Blo 1845624 7009001 := bstep (se 2 (by rfl) ⟨2628375, by rfl⟩ : syracuseStep 7009001 = 5256751) B5256751
theorem B7484147 : Blo 1845624 7484147 := bstep (se 1 (by rfl) ⟨5613110, by rfl⟩ : syracuseStep 7484147 = 11226221) B11226221
theorem B2077807 : Blo 1845624 2077807 := bstep (se 1 (by rfl) ⟨1558355, by rfl⟩ : syracuseStep 2077807 = 3116711) B3116711
theorem B26621531 : Blo 1845624 26621531 := bstep (se 1 (by rfl) ⟨19966148, by rfl⟩ : syracuseStep 26621531 = 39932297) B39932297
theorem B3504455 : Blo 1845624 3504455 := bstep (se 1 (by rfl) ⟨2628341, by rfl⟩ : syracuseStep 3504455 = 5256683) B5256683
theorem B2627977 : Blo 1845624 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B3504539 : Blo 1845624 3504539 := bstep (se 1 (by rfl) ⟨2628404, by rfl⟩ : syracuseStep 3504539 = 5256809) B5256809
theorem B4676089 : Blo 1845624 4676089 := bstep (se 2 (by rfl) ⟨1753533, by rfl⟩ : syracuseStep 4676089 = 3507067) B3507067
theorem B72956555 : Blo 1845624 72956555 := bstep (se 1 (by rfl) ⟨54717416, by rfl⟩ : syracuseStep 72956555 = 109434833) B109434833
theorem B53254817 : Blo 1845624 53254817 := bstep (se 2 (by rfl) ⟨19970556, by rfl⟩ : syracuseStep 53254817 = 39941113) B39941113
theorem B6232841 : Blo 1845624 6232841 := bstep (se 2 (by rfl) ⟨2337315, by rfl⟩ : syracuseStep 6232841 = 4674631) B4674631
theorem B17742995 : Blo 1845624 17742995 := bstep (se 1 (by rfl) ⟨13307246, by rfl⟩ : syracuseStep 17742995 = 26614493) B26614493
theorem B2768591 : Blo 1845624 2768591 := bstep (se 1 (by rfl) ⟨2076443, by rfl⟩ : syracuseStep 2768591 = 4152887) B4152887
theorem B2768639 : Blo 1845624 2768639 := bstep (se 1 (by rfl) ⟨2076479, by rfl⟩ : syracuseStep 2768639 = 4152959) B4152959
theorem B14409535 : Blo 1845624 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B8871805 : Blo 1845624 8871805 := bstep (se 3 (by rfl) ⟨1663463, by rfl⟩ : syracuseStep 8871805 = 3326927) B3326927
theorem B4153337 : Blo 1845624 4153337 := bstep (se 2 (by rfl) ⟨1557501, by rfl⟩ : syracuseStep 4153337 = 3115003) B3115003
theorem B2768927 : Blo 1845624 2768927 := bstep (se 1 (by rfl) ⟨2076695, by rfl⟩ : syracuseStep 2768927 = 4153391) B4153391
theorem B20242505 : Blo 1845624 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B4153607 : Blo 1845624 4153607 := bstep (se 1 (by rfl) ⟨3115205, by rfl⟩ : syracuseStep 4153607 = 6230411) B6230411
theorem B7012615 : Blo 1845624 7012615 := bstep (se 1 (by rfl) ⟨5259461, by rfl⟩ : syracuseStep 7012615 = 10518923) B10518923
theorem B2769179 : Blo 1845624 2769179 := bstep (se 1 (by rfl) ⟨2076884, by rfl⟩ : syracuseStep 2769179 = 4153769) B4153769
theorem B4211027 : Blo 1845624 4211027 := bstep (se 1 (by rfl) ⟨3158270, by rfl⟩ : syracuseStep 4211027 = 6316541) B6316541
theorem B4989431 : Blo 1845624 4989431 := bstep (se 1 (by rfl) ⟨3742073, by rfl⟩ : syracuseStep 4989431 = 7484147) B7484147
theorem B6234785 : Blo 1845624 6234785 := bstep (se 2 (by rfl) ⟨2338044, by rfl⟩ : syracuseStep 6234785 = 4676089) B4676089
theorem B2769641 : Blo 1845624 2769641 := bstep (se 2 (by rfl) ⟨1038615, by rfl⟩ : syracuseStep 2769641 = 2077231) B2077231
theorem B2769719 : Blo 1845624 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B2769833 : Blo 1845624 2769833 := bstep (se 2 (by rfl) ⟨1038687, by rfl⟩ : syracuseStep 2769833 = 2077375) B2077375
theorem B11830303 : Blo 1845624 11830303 := bstep (se 1 (by rfl) ⟨8872727, by rfl⟩ : syracuseStep 11830303 = 17745455) B17745455
theorem B2770079 : Blo 1845624 2770079 := bstep (se 1 (by rfl) ⟨2077559, by rfl⟩ : syracuseStep 2770079 = 4155119) B4155119
theorem B2770409 : Blo 1845624 2770409 := bstep (se 2 (by rfl) ⟨1038903, by rfl⟩ : syracuseStep 2770409 = 2077807) B2077807
theorem B2336303 : Blo 1845624 2336303 := bstep (se 1 (by rfl) ⟨1752227, by rfl⟩ : syracuseStep 2336303 = 3504455) B3504455
theorem B2336359 : Blo 1845624 2336359 := bstep (se 1 (by rfl) ⟨1752269, by rfl⟩ : syracuseStep 2336359 = 3504539) B3504539
theorem B48637703 : Blo 1845624 48637703 := bstep (se 1 (by rfl) ⟨36478277, by rfl⟩ : syracuseStep 48637703 = 72956555) B72956555
theorem B4155227 : Blo 1845624 4155227 := bstep (se 1 (by rfl) ⟨3116420, by rfl⟩ : syracuseStep 4155227 = 6232841) B6232841
theorem B2770847 : Blo 1845624 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B19974539 : Blo 1845624 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B19212713 : Blo 1845624 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B1845727 : Blo 1845624 1845727 := bstep (se 1 (by rfl) ⟨1384295, by rfl⟩ : syracuseStep 1845727 = 2768591) B2768591
theorem B1845759 : Blo 1845624 1845759 := bstep (se 1 (by rfl) ⟨1384319, by rfl⟩ : syracuseStep 1845759 = 2768639) B2768639
theorem B269617733 : Blo 1845624 269617733 := bstep (se 4 (by rfl) ⟨25276662, by rfl⟩ : syracuseStep 269617733 = 50553325) B50553325
theorem B3115631 : Blo 1845624 3115631 := bstep (se 1 (by rfl) ⟨2336723, by rfl⟩ : syracuseStep 3115631 = 4673447) B4673447
theorem B1846079 : Blo 1845624 1846079 := bstep (se 1 (by rfl) ⟨1384559, by rfl⟩ : syracuseStep 1846079 = 2769119) B2769119
theorem B6655007 : Blo 1845624 6655007 := bstep (se 1 (by rfl) ⟨4991255, by rfl⟩ : syracuseStep 6655007 = 9982511) B9982511
theorem B53251127 : Blo 1845624 53251127 := bstep (se 1 (by rfl) ⟨39938345, by rfl⟩ : syracuseStep 53251127 = 79876691) B79876691
theorem B4672667 : Blo 1845624 4672667 := bstep (se 1 (by rfl) ⟨3504500, by rfl⟩ : syracuseStep 4672667 = 7009001) B7009001
theorem B1846511 : Blo 1845624 1846511 := bstep (se 1 (by rfl) ⟨1384883, by rfl⟩ : syracuseStep 1846511 = 2769767) B2769767
theorem B1846599 : Blo 1845624 1846599 := bstep (se 1 (by rfl) ⟨1384949, by rfl⟩ : syracuseStep 1846599 = 2769899) B2769899
theorem B28413413 : Blo 1845624 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B1846783 : Blo 1845624 1846783 := bstep (se 1 (by rfl) ⟨1385087, by rfl⟩ : syracuseStep 1846783 = 2770175) B2770175
theorem B2338303 : Blo 1845624 2338303 := bstep (se 1 (by rfl) ⟨1753727, by rfl⟩ : syracuseStep 2338303 = 3507455) B3507455
theorem B17747687 : Blo 1845624 17747687 := bstep (se 1 (by rfl) ⟨13310765, by rfl⟩ : syracuseStep 17747687 = 26621531) B26621531
theorem B1847387 : Blo 1845624 1847387 := bstep (se 1 (by rfl) ⟨1385540, by rfl⟩ : syracuseStep 1847387 = 2771081) B2771081
theorem B11235439 : Blo 1845624 11235439 := bstep (se 1 (by rfl) ⟨8426579, by rfl⟩ : syracuseStep 11235439 = 16853159) B16853159
theorem B2077159 : Blo 1845624 2077159 := bstep (se 1 (by rfl) ⟨1557869, by rfl⟩ : syracuseStep 2077159 = 3115739) B3115739
theorem B87667211 : Blo 1845624 87667211 := bstep (se 1 (by rfl) ⟨65750408, by rfl⟩ : syracuseStep 87667211 = 131500817) B131500817
theorem B4993787 : Blo 1845624 4993787 := bstep (se 1 (by rfl) ⟨3745340, by rfl⟩ : syracuseStep 4993787 = 7490681) B7490681
theorem B39924505 : Blo 1845624 39924505 := bstep (se 2 (by rfl) ⟨14971689, by rfl⟩ : syracuseStep 39924505 = 29943379) B29943379
theorem B13317281 : Blo 1845624 13317281 := bstep (se 2 (by rfl) ⟨4993980, by rfl⟩ : syracuseStep 13317281 = 9987961) B9987961
theorem B4109759 : Blo 1845624 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B2078239 : Blo 1845624 2078239 := bstep (se 1 (by rfl) ⟨1558679, by rfl⟩ : syracuseStep 2078239 = 3117359) B3117359
theorem B3503969 : Blo 1845624 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B7887401 : Blo 1845624 7887401 := bstep (se 2 (by rfl) ⟨2957775, by rfl⟩ : syracuseStep 7887401 = 5915551) B5915551
theorem B4053739 : Blo 1845624 4053739 := bstep (se 1 (by rfl) ⟨3040304, by rfl⟩ : syracuseStep 4053739 = 6080609) B6080609
theorem B35503211 : Blo 1845624 35503211 := bstep (se 1 (by rfl) ⟨26627408, by rfl⟩ : syracuseStep 35503211 = 53254817) B53254817
theorem B11828663 : Blo 1845624 11828663 := bstep (se 1 (by rfl) ⟨8871497, by rfl⟩ : syracuseStep 11828663 = 17742995) B17742995
theorem B4152815 : Blo 1845624 4152815 := bstep (se 1 (by rfl) ⟨3114611, by rfl⟩ : syracuseStep 4152815 = 6229223) B6229223
theorem B11829073 : Blo 1845624 11829073 := bstep (se 2 (by rfl) ⟨4435902, by rfl⟩ : syracuseStep 11829073 = 8871805) B8871805
theorem B4153247 : Blo 1845624 4153247 := bstep (se 1 (by rfl) ⟨3114935, by rfl⟩ : syracuseStep 4153247 = 6229871) B6229871
theorem B2768891 : Blo 1845624 2768891 := bstep (se 1 (by rfl) ⟨2076668, by rfl⟩ : syracuseStep 2768891 = 4153337) B4153337
theorem B2769071 : Blo 1845624 2769071 := bstep (se 1 (by rfl) ⟨2076803, by rfl⟩ : syracuseStep 2769071 = 4153607) B4153607
theorem B3326287 : Blo 1845624 3326287 := bstep (se 1 (by rfl) ⟨2494715, by rfl⟩ : syracuseStep 3326287 = 4989431) B4989431
theorem B2769545 : Blo 1845624 2769545 := bstep (se 2 (by rfl) ⟨1038579, by rfl⟩ : syracuseStep 2769545 = 2077159) B2077159
theorem B53232673 : Blo 1845624 53232673 := bstep (se 2 (by rfl) ⟨19962252, by rfl⟩ : syracuseStep 53232673 = 39924505) B39924505
theorem B2770151 : Blo 1845624 2770151 := bstep (se 1 (by rfl) ⟨2077613, by rfl⟩ : syracuseStep 2770151 = 4155227) B4155227
theorem B2335979 : Blo 1845624 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B2770985 : Blo 1845624 2770985 := bstep (se 2 (by rfl) ⟨1039119, by rfl⟩ : syracuseStep 2770985 = 2078239) B2078239
theorem B23668807 : Blo 1845624 23668807 := bstep (se 1 (by rfl) ⟨17751605, by rfl⟩ : syracuseStep 23668807 = 35503211) B35503211
theorem B3115111 : Blo 1845624 3115111 := bstep (se 1 (by rfl) ⟨2336333, by rfl⟩ : syracuseStep 3115111 = 4672667) B4672667
theorem B3115145 : Blo 1845624 3115145 := bstep (se 2 (by rfl) ⟨1168179, by rfl⟩ : syracuseStep 3115145 = 2336359) B2336359
theorem B18942275 : Blo 1845624 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B15772097 : Blo 1845624 15772097 := bstep (se 2 (by rfl) ⟨5914536, by rfl⟩ : syracuseStep 15772097 = 11829073) B11829073
theorem B11831791 : Blo 1845624 11831791 := bstep (se 1 (by rfl) ⟨8873843, by rfl⟩ : syracuseStep 11831791 = 17747687) B17747687
theorem B1845927 : Blo 1845624 1845927 := bstep (se 1 (by rfl) ⟨1384445, by rfl⟩ : syracuseStep 1845927 = 2768891) B2768891
theorem B1845951 : Blo 1845624 1845951 := bstep (se 1 (by rfl) ⟨1384463, by rfl⟩ : syracuseStep 1845951 = 2768927) B2768927
theorem B17746685 : Blo 1845624 17746685 := bstep (se 3 (by rfl) ⟨3327503, by rfl⟩ : syracuseStep 17746685 = 6655007) B6655007
theorem B1846119 : Blo 1845624 1846119 := bstep (se 1 (by rfl) ⟨1384589, by rfl⟩ : syracuseStep 1846119 = 2769179) B2769179
theorem B53980013 : Blo 1845624 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B9350153 : Blo 1845624 9350153 := bstep (se 2 (by rfl) ⟨3506307, by rfl⟩ : syracuseStep 9350153 = 7012615) B7012615
theorem B4156523 : Blo 1845624 4156523 := bstep (se 1 (by rfl) ⟨3117392, by rfl⟩ : syracuseStep 4156523 = 6234785) B6234785
theorem B1846427 : Blo 1845624 1846427 := bstep (se 1 (by rfl) ⟨1384820, by rfl⟩ : syracuseStep 1846427 = 2769641) B2769641
theorem B3329191 : Blo 1845624 3329191 := bstep (se 1 (by rfl) ⟨2496893, by rfl⟩ : syracuseStep 3329191 = 4993787) B4993787
theorem B1846479 : Blo 1845624 1846479 := bstep (se 1 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 1846479 = 2769719) B2769719
theorem B1846555 : Blo 1845624 1846555 := bstep (se 1 (by rfl) ⟨1384916, by rfl⟩ : syracuseStep 1846555 = 2769833) B2769833
theorem B1846719 : Blo 1845624 1846719 := bstep (se 1 (by rfl) ⟨1385039, by rfl⟩ : syracuseStep 1846719 = 2770079) B2770079
theorem B2739839 : Blo 1845624 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B1846939 : Blo 1845624 1846939 := bstep (se 1 (by rfl) ⟨1385204, by rfl⟩ : syracuseStep 1846939 = 2770409) B2770409
theorem B1847231 : Blo 1845624 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B233779229 : Blo 1845624 233779229 := bstep (se 3 (by rfl) ⟨43833605, by rfl⟩ : syracuseStep 233779229 = 87667211) B87667211
theorem B15773737 : Blo 1845624 15773737 := bstep (se 2 (by rfl) ⟨5915151, by rfl⟩ : syracuseStep 15773737 = 11830303) B11830303
theorem B6230141 : Blo 1845624 6230141 := bstep (se 3 (by rfl) ⟨1168151, by rfl⟩ : syracuseStep 6230141 = 2336303) B2336303
theorem B13316359 : Blo 1845624 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B12808475 : Blo 1845624 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B179745155 : Blo 1845624 179745155 := bstep (se 1 (by rfl) ⟨134808866, by rfl⟩ : syracuseStep 179745155 = 269617733) B269617733
theorem B2077087 : Blo 1845624 2077087 := bstep (se 1 (by rfl) ⟨1557815, by rfl⟩ : syracuseStep 2077087 = 3115631) B3115631
theorem B3117737 : Blo 1845624 3117737 := bstep (se 2 (by rfl) ⟨1169151, by rfl⟩ : syracuseStep 3117737 = 2338303) B2338303
theorem B129700541 : Blo 1845624 129700541 := bstep (se 3 (by rfl) ⟨24318851, by rfl⟩ : syracuseStep 129700541 = 48637703) B48637703
theorem B35500751 : Blo 1845624 35500751 := bstep (se 1 (by rfl) ⟨26625563, by rfl⟩ : syracuseStep 35500751 = 53251127) B53251127
theorem B7885775 : Blo 1845624 7885775 := bstep (se 1 (by rfl) ⟨5914331, by rfl⟩ : syracuseStep 7885775 = 11828663) B11828663
theorem B14980585 : Blo 1845624 14980585 := bstep (se 2 (by rfl) ⟨5617719, by rfl⟩ : syracuseStep 14980585 = 11235439) B11235439
theorem B2807351 : Blo 1845624 2807351 := bstep (se 1 (by rfl) ⟨2105513, by rfl⟩ : syracuseStep 2807351 = 4211027) B4211027
theorem B8878187 : Blo 1845624 8878187 := bstep (se 1 (by rfl) ⟨6658640, by rfl⟩ : syracuseStep 8878187 = 13317281) B13317281
theorem B5404985 : Blo 1845624 5404985 := bstep (se 2 (by rfl) ⟨2026869, by rfl⟩ : syracuseStep 5404985 = 4053739) B4053739
theorem B5258267 : Blo 1845624 5258267 := bstep (se 1 (by rfl) ⟨3943700, by rfl⟩ : syracuseStep 5258267 = 7887401) B7887401
theorem B2768543 : Blo 1845624 2768543 := bstep (se 1 (by rfl) ⟨2076407, by rfl⟩ : syracuseStep 2768543 = 4152815) B4152815
theorem B2768831 : Blo 1845624 2768831 := bstep (se 1 (by rfl) ⟨2076623, by rfl⟩ : syracuseStep 2768831 = 4153247) B4153247
theorem B155852819 : Blo 1845624 155852819 := bstep (se 1 (by rfl) ⟨116889614, by rfl⟩ : syracuseStep 155852819 = 233779229) B233779229
theorem B4153427 : Blo 1845624 4153427 := bstep (se 1 (by rfl) ⟨3115070, by rfl⟩ : syracuseStep 4153427 = 6230141) B6230141
theorem B4153481 : Blo 1845624 4153481 := bstep (se 2 (by rfl) ⟨1557555, by rfl⟩ : syracuseStep 4153481 = 3115111) B3115111
theorem B23675165 : Blo 1845624 23675165 := bstep (se 3 (by rfl) ⟨4439093, by rfl⟩ : syracuseStep 23675165 = 8878187) B8878187
theorem B86467027 : Blo 1845624 86467027 := bstep (se 1 (by rfl) ⟨64850270, by rfl⟩ : syracuseStep 86467027 = 129700541) B129700541
theorem B23667167 : Blo 1845624 23667167 := bstep (se 1 (by rfl) ⟨17750375, by rfl⟩ : syracuseStep 23667167 = 35500751) B35500751
theorem B2769449 : Blo 1845624 2769449 := bstep (se 2 (by rfl) ⟨1038543, by rfl⟩ : syracuseStep 2769449 = 2077087) B2077087
theorem B70976897 : Blo 1845624 70976897 := bstep (se 2 (by rfl) ⟨26616336, by rfl⟩ : syracuseStep 70976897 = 53232673) B53232673
theorem B11831123 : Blo 1845624 11831123 := bstep (se 1 (by rfl) ⟨8873342, by rfl⟩ : syracuseStep 11831123 = 17746685) B17746685
theorem B19974113 : Blo 1845624 19974113 := bstep (se 2 (by rfl) ⟨7490292, by rfl⟩ : syracuseStep 19974113 = 14980585) B14980585
theorem B2771015 : Blo 1845624 2771015 := bstep (se 1 (by rfl) ⟨2078261, by rfl⟩ : syracuseStep 2771015 = 4156523) B4156523
theorem B1845695 : Blo 1845624 1845695 := bstep (se 1 (by rfl) ⟨1384271, by rfl⟩ : syracuseStep 1845695 = 2768543) B2768543
theorem B1845887 : Blo 1845624 1845887 := bstep (se 1 (by rfl) ⟨1384415, by rfl⟩ : syracuseStep 1845887 = 2768831) B2768831
theorem B21031649 : Blo 1845624 21031649 := bstep (se 2 (by rfl) ⟨7886868, by rfl⟩ : syracuseStep 21031649 = 15773737) B15773737
theorem B31558409 : Blo 1845624 31558409 := bstep (se 2 (by rfl) ⟨11834403, by rfl⟩ : syracuseStep 31558409 = 23668807) B23668807
theorem B1846047 : Blo 1845624 1846047 := bstep (se 1 (by rfl) ⟨1384535, by rfl⟩ : syracuseStep 1846047 = 2769071) B2769071
theorem B8538983 : Blo 1845624 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B17755145 : Blo 1845624 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B1846363 : Blo 1845624 1846363 := bstep (se 1 (by rfl) ⟨1384772, by rfl⟩ : syracuseStep 1846363 = 2769545) B2769545
theorem B4435049 : Blo 1845624 4435049 := bstep (se 2 (by rfl) ⟨1663143, by rfl⟩ : syracuseStep 4435049 = 3326287) B3326287
theorem B6229277 : Blo 1845624 6229277 := bstep (se 3 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 6229277 = 2335979) B2335979
theorem B1846767 : Blo 1845624 1846767 := bstep (se 1 (by rfl) ⟨1385075, by rfl⟩ : syracuseStep 1846767 = 2770151) B2770151
theorem B17755685 : Blo 1845624 17755685 := bstep (se 4 (by rfl) ⟨1664595, by rfl⟩ : syracuseStep 17755685 = 3329191) B3329191
theorem B1871567 : Blo 1845624 1871567 := bstep (se 1 (by rfl) ⟨1403675, by rfl⟩ : syracuseStep 1871567 = 2807351) B2807351
theorem B1847323 : Blo 1845624 1847323 := bstep (se 1 (by rfl) ⟨1385492, by rfl⟩ : syracuseStep 1847323 = 2770985) B2770985
theorem B2076763 : Blo 1845624 2076763 := bstep (se 1 (by rfl) ⟨1557572, by rfl⟩ : syracuseStep 2076763 = 3115145) B3115145
theorem B12628183 : Blo 1845624 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B10514731 : Blo 1845624 10514731 := bstep (se 1 (by rfl) ⟨7886048, by rfl⟩ : syracuseStep 10514731 = 15772097) B15772097
theorem B119830103 : Blo 1845624 119830103 := bstep (se 1 (by rfl) ⟨89872577, by rfl⟩ : syracuseStep 119830103 = 179745155) B179745155
theorem B2078491 : Blo 1845624 2078491 := bstep (se 1 (by rfl) ⟨1558868, by rfl⟩ : syracuseStep 2078491 = 3117737) B3117737
theorem B15775721 : Blo 1845624 15775721 := bstep (se 2 (by rfl) ⟨5915895, by rfl⟩ : syracuseStep 15775721 = 11831791) B11831791
theorem B3603323 : Blo 1845624 3603323 := bstep (se 1 (by rfl) ⟨2702492, by rfl⟩ : syracuseStep 3603323 = 5404985) B5404985
theorem B7306237 : Blo 1845624 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B35986675 : Blo 1845624 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B6233435 : Blo 1845624 6233435 := bstep (se 1 (by rfl) ⟨4675076, by rfl⟩ : syracuseStep 6233435 = 9350153) B9350153
theorem B3505511 : Blo 1845624 3505511 := bstep (se 1 (by rfl) ⟨2629133, by rfl⟩ : syracuseStep 3505511 = 5258267) B5258267
theorem B21028733 : Blo 1845624 21028733 := bstep (se 3 (by rfl) ⟨3942887, by rfl⟩ : syracuseStep 21028733 = 7885775) B7885775
theorem B2768951 : Blo 1845624 2768951 := bstep (se 1 (by rfl) ⟨2076713, by rfl⟩ : syracuseStep 2768951 = 4153427) B4153427
theorem B2768987 : Blo 1845624 2768987 := bstep (se 1 (by rfl) ⟨2076740, by rfl⟩ : syracuseStep 2768987 = 4153481) B4153481
theorem B2769017 : Blo 1845624 2769017 := bstep (se 2 (by rfl) ⟨1038381, by rfl⟩ : syracuseStep 2769017 = 2076763) B2076763
theorem B15778111 : Blo 1845624 15778111 := bstep (se 1 (by rfl) ⟨11833583, by rfl⟩ : syracuseStep 15778111 = 23667167) B23667167
theorem B47317931 : Blo 1845624 47317931 := bstep (se 1 (by rfl) ⟨35488448, by rfl⟩ : syracuseStep 47317931 = 70976897) B70976897
theorem B9741649 : Blo 1845624 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B47982233 : Blo 1845624 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B21038939 : Blo 1845624 21038939 := bstep (se 1 (by rfl) ⟨15779204, by rfl⟩ : syracuseStep 21038939 = 31558409) B31558409
theorem B31549661 : Blo 1845624 31549661 := bstep (se 3 (by rfl) ⟨5915561, by rfl⟩ : syracuseStep 31549661 = 11831123) B11831123
theorem B4155623 : Blo 1845624 4155623 := bstep (se 1 (by rfl) ⟨3116717, by rfl⟩ : syracuseStep 4155623 = 6233435) B6233435
theorem B2337007 : Blo 1845624 2337007 := bstep (se 1 (by rfl) ⟨1752755, by rfl⟩ : syracuseStep 2337007 = 3505511) B3505511
theorem B2771321 : Blo 1845624 2771321 := bstep (se 2 (by rfl) ⟨1039245, by rfl⟩ : syracuseStep 2771321 = 2078491) B2078491
theorem B14019155 : Blo 1845624 14019155 := bstep (se 1 (by rfl) ⟨10514366, by rfl⟩ : syracuseStep 14019155 = 21028733) B21028733
theorem B103901879 : Blo 1845624 103901879 := bstep (se 1 (by rfl) ⟨77926409, by rfl⟩ : syracuseStep 103901879 = 155852819) B155852819
theorem B16837577 : Blo 1845624 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B1846299 : Blo 1845624 1846299 := bstep (se 1 (by rfl) ⟨1384724, by rfl⟩ : syracuseStep 1846299 = 2769449) B2769449
theorem B14019641 : Blo 1845624 14019641 := bstep (se 2 (by rfl) ⟨5257365, by rfl⟩ : syracuseStep 14019641 = 10514731) B10514731
theorem B115289369 : Blo 1845624 115289369 := bstep (se 2 (by rfl) ⟨43233513, by rfl⟩ : syracuseStep 115289369 = 86467027) B86467027
theorem B13316075 : Blo 1845624 13316075 := bstep (se 1 (by rfl) ⟨9987056, by rfl⟩ : syracuseStep 13316075 = 19974113) B19974113
theorem B1847343 : Blo 1845624 1847343 := bstep (se 1 (by rfl) ⟨1385507, by rfl⟩ : syracuseStep 1847343 = 2771015) B2771015
theorem B14021099 : Blo 1845624 14021099 := bstep (se 1 (by rfl) ⟨10515824, by rfl⟩ : syracuseStep 14021099 = 21031649) B21031649
theorem B15783443 : Blo 1845624 15783443 := bstep (se 1 (by rfl) ⟨11837582, by rfl⟩ : syracuseStep 15783443 = 23675165) B23675165
theorem B79886735 : Blo 1845624 79886735 := bstep (se 1 (by rfl) ⟨59915051, by rfl⟩ : syracuseStep 79886735 = 119830103) B119830103
theorem B10517147 : Blo 1845624 10517147 := bstep (se 1 (by rfl) ⟨7887860, by rfl⟩ : syracuseStep 10517147 = 15775721) B15775721
theorem B5692655 : Blo 1845624 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B11836763 : Blo 1845624 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B2956699 : Blo 1845624 2956699 := bstep (se 1 (by rfl) ⟨2217524, by rfl⟩ : syracuseStep 2956699 = 4435049) B4435049
theorem B19963381 : Blo 1845624 19963381 := bstep (se 5 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 19963381 = 1871567) B1871567
theorem B4152851 : Blo 1845624 4152851 := bstep (se 1 (by rfl) ⟨3114638, by rfl⟩ : syracuseStep 4152851 = 6229277) B6229277
theorem B9608861 : Blo 1845624 9608861 := bstep (se 3 (by rfl) ⟨1801661, by rfl⟩ : syracuseStep 9608861 = 3603323) B3603323
theorem B11837123 : Blo 1845624 11837123 := bstep (se 1 (by rfl) ⟨8877842, by rfl⟩ : syracuseStep 11837123 = 17755685) B17755685
theorem B9347399 : Blo 1845624 9347399 := bstep (se 1 (by rfl) ⟨7010549, by rfl⟩ : syracuseStep 9347399 = 14021099) B14021099
theorem B21037481 : Blo 1845624 21037481 := bstep (se 2 (by rfl) ⟨7889055, by rfl⟩ : syracuseStep 21037481 = 15778111) B15778111
theorem B14025959 : Blo 1845624 14025959 := bstep (se 1 (by rfl) ⟨10519469, by rfl⟩ : syracuseStep 14025959 = 21038939) B21038939
theorem B2770415 : Blo 1845624 2770415 := bstep (se 1 (by rfl) ⟨2077811, by rfl⟩ : syracuseStep 2770415 = 4155623) B4155623
theorem B53257823 : Blo 1845624 53257823 := bstep (se 1 (by rfl) ⟨39943367, by rfl⟩ : syracuseStep 53257823 = 79886735) B79886735
theorem B127952621 : Blo 1845624 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B3942265 : Blo 1845624 3942265 := bstep (se 2 (by rfl) ⟨1478349, by rfl⟩ : syracuseStep 3942265 = 2956699) B2956699
theorem B11225051 : Blo 1845624 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B26617841 : Blo 1845624 26617841 := bstep (se 2 (by rfl) ⟨9981690, by rfl⟩ : syracuseStep 26617841 = 19963381) B19963381
theorem B3795103 : Blo 1845624 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B76859579 : Blo 1845624 76859579 := bstep (se 1 (by rfl) ⟨57644684, by rfl⟩ : syracuseStep 76859579 = 115289369) B115289369
theorem B7891175 : Blo 1845624 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B7891415 : Blo 1845624 7891415 := bstep (se 1 (by rfl) ⟨5918561, by rfl⟩ : syracuseStep 7891415 = 11837123) B11837123
theorem B1845967 : Blo 1845624 1845967 := bstep (se 1 (by rfl) ⟨1384475, by rfl⟩ : syracuseStep 1845967 = 2768951) B2768951
theorem B1845991 : Blo 1845624 1845991 := bstep (se 1 (by rfl) ⟨1384493, by rfl⟩ : syracuseStep 1845991 = 2768987) B2768987
theorem B1846011 : Blo 1845624 1846011 := bstep (se 1 (by rfl) ⟨1384508, by rfl⟩ : syracuseStep 1846011 = 2769017) B2769017
theorem B3116009 : Blo 1845624 3116009 := bstep (se 2 (by rfl) ⟨1168503, by rfl⟩ : syracuseStep 3116009 = 2337007) B2337007
theorem B10522295 : Blo 1845624 10522295 := bstep (se 1 (by rfl) ⟨7891721, by rfl⟩ : syracuseStep 10522295 = 15783443) B15783443
theorem B21033107 : Blo 1845624 21033107 := bstep (se 1 (by rfl) ⟨15774830, by rfl⟩ : syracuseStep 21033107 = 31549661) B31549661
theorem B1847547 : Blo 1845624 1847547 := bstep (se 1 (by rfl) ⟨1385660, by rfl⟩ : syracuseStep 1847547 = 2771321) B2771321
theorem B12988865 : Blo 1845624 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B69267919 : Blo 1845624 69267919 := bstep (se 1 (by rfl) ⟨51950939, by rfl⟩ : syracuseStep 69267919 = 103901879) B103901879
theorem B8877383 : Blo 1845624 8877383 := bstep (se 1 (by rfl) ⟨6658037, by rfl⟩ : syracuseStep 8877383 = 13316075) B13316075
theorem B31545287 : Blo 1845624 31545287 := bstep (se 1 (by rfl) ⟨23658965, by rfl⟩ : syracuseStep 31545287 = 47317931) B47317931
theorem B9346103 : Blo 1845624 9346103 := bstep (se 1 (by rfl) ⟨7009577, by rfl⟩ : syracuseStep 9346103 = 14019155) B14019155
theorem B7011431 : Blo 1845624 7011431 := bstep (se 1 (by rfl) ⟨5258573, by rfl⟩ : syracuseStep 7011431 = 10517147) B10517147
theorem B9346427 : Blo 1845624 9346427 := bstep (se 1 (by rfl) ⟨7009820, by rfl⟩ : syracuseStep 9346427 = 14019641) B14019641
theorem B2768567 : Blo 1845624 2768567 := bstep (se 1 (by rfl) ⟨2076425, by rfl⟩ : syracuseStep 2768567 = 4152851) B4152851
theorem B6405907 : Blo 1845624 6405907 := bstep (se 1 (by rfl) ⟨4804430, by rfl⟩ : syracuseStep 6405907 = 9608861) B9608861
theorem B14024987 : Blo 1845624 14024987 := bstep (se 1 (by rfl) ⟨10518740, by rfl⟩ : syracuseStep 14024987 = 21037481) B21037481
theorem B8659243 : Blo 1845624 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B92357225 : Blo 1845624 92357225 := bstep (se 2 (by rfl) ⟨34633959, by rfl⟩ : syracuseStep 92357225 = 69267919) B69267919
theorem B35505215 : Blo 1845624 35505215 := bstep (se 1 (by rfl) ⟨26628911, by rfl⟩ : syracuseStep 35505215 = 53257823) B53257823
theorem B21030191 : Blo 1845624 21030191 := bstep (se 1 (by rfl) ⟨15772643, by rfl⟩ : syracuseStep 21030191 = 31545287) B31545287
theorem B17745227 : Blo 1845624 17745227 := bstep (se 1 (by rfl) ⟨13308920, by rfl⟩ : syracuseStep 17745227 = 26617841) B26617841
theorem B5260783 : Blo 1845624 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B5260943 : Blo 1845624 5260943 := bstep (se 1 (by rfl) ⟨3945707, by rfl⟩ : syracuseStep 5260943 = 7891415) B7891415
theorem B1845711 : Blo 1845624 1845711 := bstep (se 1 (by rfl) ⟨1384283, by rfl⟩ : syracuseStep 1845711 = 2768567) B2768567
theorem B7014863 : Blo 1845624 7014863 := bstep (se 1 (by rfl) ⟨5261147, by rfl⟩ : syracuseStep 7014863 = 10522295) B10522295
theorem B9350639 : Blo 1845624 9350639 := bstep (se 1 (by rfl) ⟨7012979, by rfl⟩ : syracuseStep 9350639 = 14025959) B14025959
theorem B5918255 : Blo 1845624 5918255 := bstep (se 1 (by rfl) ⟨4438691, by rfl⟩ : syracuseStep 5918255 = 8877383) B8877383
theorem B1846943 : Blo 1845624 1846943 := bstep (se 1 (by rfl) ⟨1385207, by rfl⟩ : syracuseStep 1846943 = 2770415) B2770415
theorem B7483367 : Blo 1845624 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B2077339 : Blo 1845624 2077339 := bstep (se 1 (by rfl) ⟨1558004, by rfl⟩ : syracuseStep 2077339 = 3116009) B3116009
theorem B6230735 : Blo 1845624 6230735 := bstep (se 1 (by rfl) ⟨4673051, by rfl⟩ : syracuseStep 6230735 = 9346103) B9346103
theorem B4674287 : Blo 1845624 4674287 := bstep (se 1 (by rfl) ⟨3505715, by rfl⟩ : syracuseStep 4674287 = 7011431) B7011431
theorem B6230951 : Blo 1845624 6230951 := bstep (se 1 (by rfl) ⟨4673213, by rfl⟩ : syracuseStep 6230951 = 9346427) B9346427
theorem B8541209 : Blo 1845624 8541209 := bstep (se 2 (by rfl) ⟨3202953, by rfl⟩ : syracuseStep 8541209 = 6405907) B6405907
theorem B5256353 : Blo 1845624 5256353 := bstep (se 2 (by rfl) ⟨1971132, by rfl⟩ : syracuseStep 5256353 = 3942265) B3942265
theorem B14022071 : Blo 1845624 14022071 := bstep (se 1 (by rfl) ⟨10516553, by rfl⟩ : syracuseStep 14022071 = 21033107) B21033107
theorem B6231599 : Blo 1845624 6231599 := bstep (se 1 (by rfl) ⟨4673699, by rfl⟩ : syracuseStep 6231599 = 9347399) B9347399
theorem B20240549 : Blo 1845624 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B85301747 : Blo 1845624 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B51239719 : Blo 1845624 51239719 := bstep (se 1 (by rfl) ⟨38429789, by rfl⟩ : syracuseStep 51239719 = 76859579) B76859579
theorem B61571483 : Blo 1845624 61571483 := bstep (se 1 (by rfl) ⟨46178612, by rfl⟩ : syracuseStep 61571483 = 92357225) B92357225
theorem B4153823 : Blo 1845624 4153823 := bstep (se 1 (by rfl) ⟨3115367, by rfl⟩ : syracuseStep 4153823 = 6230735) B6230735
theorem B4153967 : Blo 1845624 4153967 := bstep (se 1 (by rfl) ⟨3115475, by rfl⟩ : syracuseStep 4153967 = 6230951) B6230951
theorem B2769785 : Blo 1845624 2769785 := bstep (se 2 (by rfl) ⟨1038669, by rfl⟩ : syracuseStep 2769785 = 2077339) B2077339
theorem B11830151 : Blo 1845624 11830151 := bstep (se 1 (by rfl) ⟨8872613, by rfl⟩ : syracuseStep 11830151 = 17745227) B17745227
theorem B9348047 : Blo 1845624 9348047 := bstep (se 1 (by rfl) ⟨7011035, by rfl⟩ : syracuseStep 9348047 = 14022071) B14022071
theorem B4154399 : Blo 1845624 4154399 := bstep (se 1 (by rfl) ⟨3115799, by rfl⟩ : syracuseStep 4154399 = 6231599) B6231599
theorem B3507295 : Blo 1845624 3507295 := bstep (se 1 (by rfl) ⟨2630471, by rfl⟩ : syracuseStep 3507295 = 5260943) B5260943
theorem B13493699 : Blo 1845624 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B7014377 : Blo 1845624 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B22776557 : Blo 1845624 22776557 := bstep (se 3 (by rfl) ⟨4270604, by rfl⟩ : syracuseStep 22776557 = 8541209) B8541209
theorem B9349991 : Blo 1845624 9349991 := bstep (se 1 (by rfl) ⟨7012493, by rfl⟩ : syracuseStep 9349991 = 14024987) B14024987
theorem B3116191 : Blo 1845624 3116191 := bstep (se 1 (by rfl) ⟨2337143, by rfl⟩ : syracuseStep 3116191 = 4674287) B4674287
theorem B23670143 : Blo 1845624 23670143 := bstep (se 1 (by rfl) ⟨17752607, by rfl⟩ : syracuseStep 23670143 = 35505215) B35505215
theorem B14020127 : Blo 1845624 14020127 := bstep (se 1 (by rfl) ⟨10515095, by rfl⟩ : syracuseStep 14020127 = 21030191) B21030191
theorem B46182629 : Blo 1845624 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B3945503 : Blo 1845624 3945503 := bstep (se 1 (by rfl) ⟨2959127, by rfl⟩ : syracuseStep 3945503 = 5918255) B5918255
theorem B3504235 : Blo 1845624 3504235 := bstep (se 1 (by rfl) ⟨2628176, by rfl⟩ : syracuseStep 3504235 = 5256353) B5256353
theorem B68319625 : Blo 1845624 68319625 := bstep (se 2 (by rfl) ⟨25619859, by rfl⟩ : syracuseStep 68319625 = 51239719) B51239719
theorem B4676575 : Blo 1845624 4676575 := bstep (se 1 (by rfl) ⟨3507431, by rfl⟩ : syracuseStep 4676575 = 7014863) B7014863
theorem B56867831 : Blo 1845624 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B6233759 : Blo 1845624 6233759 := bstep (se 1 (by rfl) ⟨4675319, by rfl⟩ : syracuseStep 6233759 = 9350639) B9350639
theorem B19955645 : Blo 1845624 19955645 := bstep (se 3 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 19955645 = 7483367) B7483367
theorem B2769215 : Blo 1845624 2769215 := bstep (se 1 (by rfl) ⟨2076911, by rfl⟩ : syracuseStep 2769215 = 4153823) B4153823
theorem B2769311 : Blo 1845624 2769311 := bstep (se 1 (by rfl) ⟨2076983, by rfl⟩ : syracuseStep 2769311 = 4153967) B4153967
theorem B2769599 : Blo 1845624 2769599 := bstep (se 1 (by rfl) ⟨2077199, by rfl⟩ : syracuseStep 2769599 = 4154399) B4154399
theorem B2630335 : Blo 1845624 2630335 := bstep (se 1 (by rfl) ⟨1972751, by rfl⟩ : syracuseStep 2630335 = 3945503) B3945503
theorem B8995799 : Blo 1845624 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B6235433 : Blo 1845624 6235433 := bstep (se 2 (by rfl) ⟨2338287, by rfl⟩ : syracuseStep 6235433 = 4676575) B4676575
theorem B4154921 : Blo 1845624 4154921 := bstep (se 2 (by rfl) ⟨1558095, by rfl⟩ : syracuseStep 4154921 = 3116191) B3116191
theorem B60737485 : Blo 1845624 60737485 := bstep (se 3 (by rfl) ⟨11388278, by rfl⟩ : syracuseStep 60737485 = 22776557) B22776557
theorem B15780095 : Blo 1845624 15780095 := bstep (se 1 (by rfl) ⟨11835071, by rfl⟩ : syracuseStep 15780095 = 23670143) B23670143
theorem B4155839 : Blo 1845624 4155839 := bstep (se 1 (by rfl) ⟨3116879, by rfl⟩ : syracuseStep 4155839 = 6233759) B6233759
theorem B4672313 : Blo 1845624 4672313 := bstep (se 2 (by rfl) ⟨1752117, by rfl⟩ : syracuseStep 4672313 = 3504235) B3504235
theorem B30788419 : Blo 1845624 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B1846523 : Blo 1845624 1846523 := bstep (se 1 (by rfl) ⟨1384892, by rfl⟩ : syracuseStep 1846523 = 2769785) B2769785
theorem B41047655 : Blo 1845624 41047655 := bstep (se 1 (by rfl) ⟨30785741, by rfl⟩ : syracuseStep 41047655 = 61571483) B61571483
theorem B91092833 : Blo 1845624 91092833 := bstep (se 2 (by rfl) ⟨34159812, by rfl⟩ : syracuseStep 91092833 = 68319625) B68319625
theorem B7886767 : Blo 1845624 7886767 := bstep (se 1 (by rfl) ⟨5915075, by rfl⟩ : syracuseStep 7886767 = 11830151) B11830151
theorem B6232031 : Blo 1845624 6232031 := bstep (se 1 (by rfl) ⟨4674023, by rfl⟩ : syracuseStep 6232031 = 9348047) B9348047
theorem B4676251 : Blo 1845624 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B4676393 : Blo 1845624 4676393 := bstep (se 2 (by rfl) ⟨1753647, by rfl⟩ : syracuseStep 4676393 = 3507295) B3507295
theorem B6233327 : Blo 1845624 6233327 := bstep (se 1 (by rfl) ⟨4674995, by rfl⟩ : syracuseStep 6233327 = 9349991) B9349991
theorem B37911887 : Blo 1845624 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B9346751 : Blo 1845624 9346751 := bstep (se 1 (by rfl) ⟨7010063, by rfl⟩ : syracuseStep 9346751 = 14020127) B14020127
theorem B13303763 : Blo 1845624 13303763 := bstep (se 1 (by rfl) ⟨9977822, by rfl⟩ : syracuseStep 13303763 = 19955645) B19955645
theorem B5997199 : Blo 1845624 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B6235001 : Blo 1845624 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B3507113 : Blo 1845624 3507113 := bstep (se 2 (by rfl) ⟨1315167, by rfl⟩ : syracuseStep 3507113 = 2630335) B2630335
theorem B2769947 : Blo 1845624 2769947 := bstep (se 1 (by rfl) ⟨2077460, by rfl⟩ : syracuseStep 2769947 = 4154921) B4154921
theorem B41051225 : Blo 1845624 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B60728555 : Blo 1845624 60728555 := bstep (se 1 (by rfl) ⟨45546416, by rfl⟩ : syracuseStep 60728555 = 91092833) B91092833
theorem B4154687 : Blo 1845624 4154687 := bstep (se 1 (by rfl) ⟨3116015, by rfl⟩ : syracuseStep 4154687 = 6232031) B6232031
theorem B10520063 : Blo 1845624 10520063 := bstep (se 1 (by rfl) ⟨7890047, by rfl⟩ : syracuseStep 10520063 = 15780095) B15780095
theorem B2770559 : Blo 1845624 2770559 := bstep (se 1 (by rfl) ⟨2077919, by rfl⟩ : syracuseStep 2770559 = 4155839) B4155839
theorem B3114875 : Blo 1845624 3114875 := bstep (se 1 (by rfl) ⟨2336156, by rfl⟩ : syracuseStep 3114875 = 4672313) B4672313
theorem B4155551 : Blo 1845624 4155551 := bstep (se 1 (by rfl) ⟨3116663, by rfl⟩ : syracuseStep 4155551 = 6233327) B6233327
theorem B25274591 : Blo 1845624 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B1846143 : Blo 1845624 1846143 := bstep (se 1 (by rfl) ⟨1384607, by rfl⟩ : syracuseStep 1846143 = 2769215) B2769215
theorem B1846207 : Blo 1845624 1846207 := bstep (se 1 (by rfl) ⟨1384655, by rfl⟩ : syracuseStep 1846207 = 2769311) B2769311
theorem B1846399 : Blo 1845624 1846399 := bstep (se 1 (by rfl) ⟨1384799, by rfl⟩ : syracuseStep 1846399 = 2769599) B2769599
theorem B4156955 : Blo 1845624 4156955 := bstep (se 1 (by rfl) ⟨3117716, by rfl⟩ : syracuseStep 4156955 = 6235433) B6235433
theorem B3117595 : Blo 1845624 3117595 := bstep (se 1 (by rfl) ⟨2338196, by rfl⟩ : syracuseStep 3117595 = 4676393) B4676393
theorem B6231167 : Blo 1845624 6231167 := bstep (se 1 (by rfl) ⟨4673375, by rfl⟩ : syracuseStep 6231167 = 9346751) B9346751
theorem B10515689 : Blo 1845624 10515689 := bstep (se 2 (by rfl) ⟨3943383, by rfl⟩ : syracuseStep 10515689 = 7886767) B7886767
theorem B80983313 : Blo 1845624 80983313 := bstep (se 2 (by rfl) ⟨30368742, by rfl⟩ : syracuseStep 80983313 = 60737485) B60737485
theorem B8869175 : Blo 1845624 8869175 := bstep (se 1 (by rfl) ⟨6651881, by rfl⟩ : syracuseStep 8869175 = 13303763) B13303763
theorem B109460413 : Blo 1845624 109460413 := bstep (se 3 (by rfl) ⟨20523827, by rfl⟩ : syracuseStep 109460413 = 41047655) B41047655
theorem B4154111 : Blo 1845624 4154111 := bstep (se 1 (by rfl) ⟨3115583, by rfl⟩ : syracuseStep 4154111 = 6231167) B6231167
theorem B40485703 : Blo 1845624 40485703 := bstep (se 1 (by rfl) ⟨30364277, by rfl⟩ : syracuseStep 40485703 = 60728555) B60728555
theorem B7996265 : Blo 1845624 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B2769791 : Blo 1845624 2769791 := bstep (se 1 (by rfl) ⟨2077343, by rfl⟩ : syracuseStep 2769791 = 4154687) B4154687
theorem B7013375 : Blo 1845624 7013375 := bstep (se 1 (by rfl) ⟨5260031, by rfl⟩ : syracuseStep 7013375 = 10520063) B10520063
theorem B2770367 : Blo 1845624 2770367 := bstep (se 1 (by rfl) ⟨2077775, by rfl⟩ : syracuseStep 2770367 = 4155551) B4155551
theorem B2771303 : Blo 1845624 2771303 := bstep (se 1 (by rfl) ⟨2078477, by rfl⟩ : syracuseStep 2771303 = 4156955) B4156955
theorem B4156667 : Blo 1845624 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B2338075 : Blo 1845624 2338075 := bstep (se 1 (by rfl) ⟨1753556, by rfl⟩ : syracuseStep 2338075 = 3507113) B3507113
theorem B1846631 : Blo 1845624 1846631 := bstep (se 1 (by rfl) ⟨1384973, by rfl⟩ : syracuseStep 1846631 = 2769947) B2769947
theorem B4156793 : Blo 1845624 4156793 := bstep (se 2 (by rfl) ⟨1558797, by rfl⟩ : syracuseStep 4156793 = 3117595) B3117595
theorem B53988875 : Blo 1845624 53988875 := bstep (se 1 (by rfl) ⟨40491656, by rfl⟩ : syracuseStep 53988875 = 80983313) B80983313
theorem B1847039 : Blo 1845624 1847039 := bstep (se 1 (by rfl) ⟨1385279, by rfl⟩ : syracuseStep 1847039 = 2770559) B2770559
theorem B2076583 : Blo 1845624 2076583 := bstep (se 1 (by rfl) ⟨1557437, by rfl⟩ : syracuseStep 2076583 = 3114875) B3114875
theorem B27367483 : Blo 1845624 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B7010459 : Blo 1845624 7010459 := bstep (se 1 (by rfl) ⟨5257844, by rfl⟩ : syracuseStep 7010459 = 10515689) B10515689
theorem B5912783 : Blo 1845624 5912783 := bstep (se 1 (by rfl) ⟨4434587, by rfl⟩ : syracuseStep 5912783 = 8869175) B8869175
theorem B145947217 : Blo 1845624 145947217 := bstep (se 2 (by rfl) ⟨54730206, by rfl⟩ : syracuseStep 145947217 = 109460413) B109460413
theorem B16849727 : Blo 1845624 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B2769407 : Blo 1845624 2769407 := bstep (se 1 (by rfl) ⟨2077055, by rfl⟩ : syracuseStep 2769407 = 4154111) B4154111
theorem B3941855 : Blo 1845624 3941855 := bstep (se 1 (by rfl) ⟨2956391, by rfl⟩ : syracuseStep 3941855 = 5912783) B5912783
theorem B11233151 : Blo 1845624 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B2771111 : Blo 1845624 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B2771195 : Blo 1845624 2771195 := bstep (se 1 (by rfl) ⟨2078396, by rfl⟩ : syracuseStep 2771195 = 4156793) B4156793
theorem B36489977 : Blo 1845624 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B1846527 : Blo 1845624 1846527 := bstep (se 1 (by rfl) ⟨1384895, by rfl⟩ : syracuseStep 1846527 = 2769791) B2769791
theorem B194596289 : Blo 1845624 194596289 := bstep (se 2 (by rfl) ⟨72973608, by rfl⟩ : syracuseStep 194596289 = 145947217) B145947217
theorem B1846911 : Blo 1845624 1846911 := bstep (se 1 (by rfl) ⟨1385183, by rfl⟩ : syracuseStep 1846911 = 2770367) B2770367
theorem B53980937 : Blo 1845624 53980937 := bstep (se 2 (by rfl) ⟨20242851, by rfl⟩ : syracuseStep 53980937 = 40485703) B40485703
theorem B4673639 : Blo 1845624 4673639 := bstep (se 1 (by rfl) ⟨3505229, by rfl⟩ : syracuseStep 4673639 = 7010459) B7010459
theorem B1847535 : Blo 1845624 1847535 := bstep (se 1 (by rfl) ⟨1385651, by rfl⟩ : syracuseStep 1847535 = 2771303) B2771303
theorem B3117433 : Blo 1845624 3117433 := bstep (se 2 (by rfl) ⟨1169037, by rfl⟩ : syracuseStep 3117433 = 2338075) B2338075
theorem B35992583 : Blo 1845624 35992583 := bstep (se 1 (by rfl) ⟨26994437, by rfl⟩ : syracuseStep 35992583 = 53988875) B53988875
theorem B5330843 : Blo 1845624 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B4675583 : Blo 1845624 4675583 := bstep (se 1 (by rfl) ⟨3506687, by rfl⟩ : syracuseStep 4675583 = 7013375) B7013375
theorem B2768777 : Blo 1845624 2768777 := bstep (se 2 (by rfl) ⟨1038291, by rfl⟩ : syracuseStep 2768777 = 2076583) B2076583
theorem B23995055 : Blo 1845624 23995055 := bstep (se 1 (by rfl) ⟨17996291, by rfl⟩ : syracuseStep 23995055 = 35992583) B35992583
theorem B7488767 : Blo 1845624 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B129730859 : Blo 1845624 129730859 := bstep (se 1 (by rfl) ⟨97298144, by rfl⟩ : syracuseStep 129730859 = 194596289) B194596289
theorem B1845851 : Blo 1845624 1845851 := bstep (se 1 (by rfl) ⟨1384388, by rfl⟩ : syracuseStep 1845851 = 2768777) B2768777
theorem B3115759 : Blo 1845624 3115759 := bstep (se 1 (by rfl) ⟨2336819, by rfl⟩ : syracuseStep 3115759 = 4673639) B4673639
theorem B1846271 : Blo 1845624 1846271 := bstep (se 1 (by rfl) ⟨1384703, by rfl⟩ : syracuseStep 1846271 = 2769407) B2769407
theorem B4156577 : Blo 1845624 4156577 := bstep (se 2 (by rfl) ⟨1558716, by rfl⟩ : syracuseStep 4156577 = 3117433) B3117433
theorem B3117055 : Blo 1845624 3117055 := bstep (se 1 (by rfl) ⟨2337791, by rfl⟩ : syracuseStep 3117055 = 4675583) B4675583
theorem B1847407 : Blo 1845624 1847407 := bstep (se 1 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 1847407 = 2771111) B2771111
theorem B1847463 : Blo 1845624 1847463 := bstep (se 1 (by rfl) ⟨1385597, by rfl⟩ : syracuseStep 1847463 = 2771195) B2771195
theorem B24326651 : Blo 1845624 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B2627903 : Blo 1845624 2627903 := bstep (se 1 (by rfl) ⟨1970927, by rfl⟩ : syracuseStep 2627903 = 3941855) B3941855
theorem B3553895 : Blo 1845624 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B35987291 : Blo 1845624 35987291 := bstep (se 1 (by rfl) ⟨26990468, by rfl⟩ : syracuseStep 35987291 = 53980937) B53980937
theorem B4154345 : Blo 1845624 4154345 := bstep (se 2 (by rfl) ⟨1557879, by rfl⟩ : syracuseStep 4154345 = 3115759) B3115759
theorem B2369263 : Blo 1845624 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B2771051 : Blo 1845624 2771051 := bstep (se 1 (by rfl) ⟨2078288, by rfl⟩ : syracuseStep 2771051 = 4156577) B4156577
theorem B4156073 : Blo 1845624 4156073 := bstep (se 2 (by rfl) ⟨1558527, by rfl⟩ : syracuseStep 4156073 = 3117055) B3117055
theorem B7007741 : Blo 1845624 7007741 := bstep (se 3 (by rfl) ⟨1313951, by rfl⟩ : syracuseStep 7007741 = 2627903) B2627903
theorem B4992511 : Blo 1845624 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B86487239 : Blo 1845624 86487239 := bstep (se 1 (by rfl) ⟨64865429, by rfl⟩ : syracuseStep 86487239 = 129730859) B129730859
theorem B23991527 : Blo 1845624 23991527 := bstep (se 1 (by rfl) ⟨17993645, by rfl⟩ : syracuseStep 23991527 = 35987291) B35987291
theorem B16217767 : Blo 1845624 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B15996703 : Blo 1845624 15996703 := bstep (se 1 (by rfl) ⟨11997527, by rfl⟩ : syracuseStep 15996703 = 23995055) B23995055
theorem B2769563 : Blo 1845624 2769563 := bstep (se 1 (by rfl) ⟨2077172, by rfl⟩ : syracuseStep 2769563 = 4154345) B4154345
theorem B2770715 : Blo 1845624 2770715 := bstep (se 1 (by rfl) ⟨2078036, by rfl⟩ : syracuseStep 2770715 = 4156073) B4156073
theorem B4671827 : Blo 1845624 4671827 := bstep (se 1 (by rfl) ⟨3503870, by rfl⟩ : syracuseStep 4671827 = 7007741) B7007741
theorem B57658159 : Blo 1845624 57658159 := bstep (se 1 (by rfl) ⟨43243619, by rfl⟩ : syracuseStep 57658159 = 86487239) B86487239
theorem B15994351 : Blo 1845624 15994351 := bstep (se 1 (by rfl) ⟨11995763, by rfl⟩ : syracuseStep 15994351 = 23991527) B23991527
theorem B1847367 : Blo 1845624 1847367 := bstep (se 1 (by rfl) ⟨1385525, by rfl⟩ : syracuseStep 1847367 = 2771051) B2771051
theorem B6656681 : Blo 1845624 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B21623689 : Blo 1845624 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B3159017 : Blo 1845624 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B21328937 : Blo 1845624 21328937 := bstep (se 2 (by rfl) ⟨7998351, by rfl⟩ : syracuseStep 21328937 = 15996703) B15996703
theorem B2106011 : Blo 1845624 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B3114551 : Blo 1845624 3114551 := bstep (se 1 (by rfl) ⟨2335913, by rfl⟩ : syracuseStep 3114551 = 4671827) B4671827
theorem B1846375 : Blo 1845624 1846375 := bstep (se 1 (by rfl) ⟨1384781, by rfl⟩ : syracuseStep 1846375 = 2769563) B2769563
theorem B76877545 : Blo 1845624 76877545 := bstep (se 2 (by rfl) ⟨28829079, by rfl⟩ : syracuseStep 76877545 = 57658159) B57658159
theorem B1847143 : Blo 1845624 1847143 := bstep (se 1 (by rfl) ⟨1385357, by rfl⟩ : syracuseStep 1847143 = 2770715) B2770715
theorem B14219291 : Blo 1845624 14219291 := bstep (se 1 (by rfl) ⟨10664468, by rfl⟩ : syracuseStep 14219291 = 21328937) B21328937
theorem B17751149 : Blo 1845624 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B115326341 : Blo 1845624 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B85303205 : Blo 1845624 85303205 := bstep (se 4 (by rfl) ⟨7997175, by rfl⟩ : syracuseStep 85303205 = 15994351) B15994351
theorem B9479527 : Blo 1845624 9479527 := bstep (se 1 (by rfl) ⟨7109645, by rfl⟩ : syracuseStep 9479527 = 14219291) B14219291
theorem B76884227 : Blo 1845624 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B2076367 : Blo 1845624 2076367 := bstep (se 1 (by rfl) ⟨1557275, by rfl⟩ : syracuseStep 2076367 = 3114551) B3114551
theorem B5616029 : Blo 1845624 5616029 := bstep (se 3 (by rfl) ⟨1053005, by rfl⟩ : syracuseStep 5616029 = 2106011) B2106011
theorem B11834099 : Blo 1845624 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B102503393 : Blo 1845624 102503393 := bstep (se 2 (by rfl) ⟨38438772, by rfl⟩ : syracuseStep 102503393 = 76877545) B76877545
theorem B56868803 : Blo 1845624 56868803 := bstep (se 1 (by rfl) ⟨42651602, by rfl⟩ : syracuseStep 56868803 = 85303205) B85303205
theorem B3744019 : Blo 1845624 3744019 := bstep (se 1 (by rfl) ⟨2808014, by rfl⟩ : syracuseStep 3744019 = 5616029) B5616029
theorem B7889399 : Blo 1845624 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B202229909 : Blo 1845624 202229909 := bstep (se 6 (by rfl) ⟨4739763, by rfl⟩ : syracuseStep 202229909 = 9479527) B9479527
theorem B68335595 : Blo 1845624 68335595 := bstep (se 1 (by rfl) ⟨51251696, by rfl⟩ : syracuseStep 68335595 = 102503393) B102503393
theorem B51256151 : Blo 1845624 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B2768489 : Blo 1845624 2768489 := bstep (se 2 (by rfl) ⟨1038183, by rfl⟩ : syracuseStep 2768489 = 2076367) B2076367
theorem B37912535 : Blo 1845624 37912535 := bstep (se 1 (by rfl) ⟨28434401, by rfl⟩ : syracuseStep 37912535 = 56868803) B56868803
theorem B5259599 : Blo 1845624 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B45557063 : Blo 1845624 45557063 := bstep (se 1 (by rfl) ⟨34167797, by rfl⟩ : syracuseStep 45557063 = 68335595) B68335595
theorem B34170767 : Blo 1845624 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B1845659 : Blo 1845624 1845659 := bstep (se 1 (by rfl) ⟨1384244, by rfl⟩ : syracuseStep 1845659 = 2768489) B2768489
theorem B25275023 : Blo 1845624 25275023 := bstep (se 1 (by rfl) ⟨18956267, by rfl⟩ : syracuseStep 25275023 = 37912535) B37912535
theorem B4992025 : Blo 1845624 4992025 := bstep (se 2 (by rfl) ⟨1872009, by rfl⟩ : syracuseStep 4992025 = 3744019) B3744019
theorem B134819939 : Blo 1845624 134819939 := bstep (se 1 (by rfl) ⟨101114954, by rfl⟩ : syracuseStep 134819939 = 202229909) B202229909
theorem B3506399 : Blo 1845624 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B30371375 : Blo 1845624 30371375 := bstep (se 1 (by rfl) ⟨22778531, by rfl⟩ : syracuseStep 30371375 = 45557063) B45557063
theorem B6656033 : Blo 1845624 6656033 := bstep (se 2 (by rfl) ⟨2496012, by rfl⟩ : syracuseStep 6656033 = 4992025) B4992025
theorem B89879959 : Blo 1845624 89879959 := bstep (se 1 (by rfl) ⟨67409969, by rfl⟩ : syracuseStep 89879959 = 134819939) B134819939
theorem B22780511 : Blo 1845624 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B16850015 : Blo 1845624 16850015 := bstep (se 1 (by rfl) ⟨12637511, by rfl⟩ : syracuseStep 16850015 = 25275023) B25275023
theorem B11233343 : Blo 1845624 11233343 := bstep (se 1 (by rfl) ⟨8425007, by rfl⟩ : syracuseStep 11233343 = 16850015) B16850015
theorem B2337599 : Blo 1845624 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B20247583 : Blo 1845624 20247583 := bstep (se 1 (by rfl) ⟨15185687, by rfl⟩ : syracuseStep 20247583 = 30371375) B30371375
theorem B4437355 : Blo 1845624 4437355 := bstep (se 1 (by rfl) ⟨3328016, by rfl⟩ : syracuseStep 4437355 = 6656033) B6656033
theorem B15187007 : Blo 1845624 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B119839945 : Blo 1845624 119839945 := bstep (se 2 (by rfl) ⟨44939979, by rfl⟩ : syracuseStep 119839945 = 89879959) B89879959
theorem B159786593 : Blo 1845624 159786593 := bstep (se 2 (by rfl) ⟨59919972, by rfl⟩ : syracuseStep 159786593 = 119839945) B119839945
theorem B5916473 : Blo 1845624 5916473 := bstep (se 2 (by rfl) ⟨2218677, by rfl⟩ : syracuseStep 5916473 = 4437355) B4437355
theorem B26996777 : Blo 1845624 26996777 := bstep (se 2 (by rfl) ⟨10123791, by rfl⟩ : syracuseStep 26996777 = 20247583) B20247583
theorem B29955581 : Blo 1845624 29955581 := bstep (se 3 (by rfl) ⟨5616671, by rfl⟩ : syracuseStep 29955581 = 11233343) B11233343
theorem B10124671 : Blo 1845624 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B6233597 : Blo 1845624 6233597 := bstep (se 3 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 6233597 = 2337599) B2337599
theorem B17997851 : Blo 1845624 17997851 := bstep (se 1 (by rfl) ⟨13498388, by rfl⟩ : syracuseStep 17997851 = 26996777) B26996777
theorem B4155731 : Blo 1845624 4155731 := bstep (se 1 (by rfl) ⟨3116798, by rfl⟩ : syracuseStep 4155731 = 6233597) B6233597
theorem B106524395 : Blo 1845624 106524395 := bstep (se 1 (by rfl) ⟨79893296, by rfl⟩ : syracuseStep 106524395 = 159786593) B159786593
theorem B3944315 : Blo 1845624 3944315 := bstep (se 1 (by rfl) ⟨2958236, by rfl⟩ : syracuseStep 3944315 = 5916473) B5916473
theorem B19970387 : Blo 1845624 19970387 := bstep (se 1 (by rfl) ⟨14977790, by rfl⟩ : syracuseStep 19970387 = 29955581) B29955581
theorem B13499561 : Blo 1845624 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B2770487 : Blo 1845624 2770487 := bstep (se 1 (by rfl) ⟨2077865, by rfl⟩ : syracuseStep 2770487 = 4155731) B4155731
theorem B13313591 : Blo 1845624 13313591 := bstep (se 1 (by rfl) ⟨9985193, by rfl⟩ : syracuseStep 13313591 = 19970387) B19970387
theorem B8999707 : Blo 1845624 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B11998567 : Blo 1845624 11998567 := bstep (se 1 (by rfl) ⟨8998925, by rfl⟩ : syracuseStep 11998567 = 17997851) B17997851
theorem B10518173 : Blo 1845624 10518173 := bstep (se 3 (by rfl) ⟨1972157, by rfl⟩ : syracuseStep 10518173 = 3944315) B3944315
theorem B71016263 : Blo 1845624 71016263 := bstep (se 1 (by rfl) ⟨53262197, by rfl⟩ : syracuseStep 71016263 = 106524395) B106524395
theorem B47344175 : Blo 1845624 47344175 := bstep (se 1 (by rfl) ⟨35508131, by rfl⟩ : syracuseStep 47344175 = 71016263) B71016263
theorem B1846991 : Blo 1845624 1846991 := bstep (se 1 (by rfl) ⟨1385243, by rfl⟩ : syracuseStep 1846991 = 2770487) B2770487
theorem B8875727 : Blo 1845624 8875727 := bstep (se 1 (by rfl) ⟨6656795, by rfl⟩ : syracuseStep 8875727 = 13313591) B13313591
theorem B11999609 : Blo 1845624 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B15998089 : Blo 1845624 15998089 := bstep (se 2 (by rfl) ⟨5999283, by rfl⟩ : syracuseStep 15998089 = 11998567) B11998567
theorem B7012115 : Blo 1845624 7012115 := bstep (se 1 (by rfl) ⟨5259086, by rfl⟩ : syracuseStep 7012115 = 10518173) B10518173
theorem B5917151 : Blo 1845624 5917151 := bstep (se 1 (by rfl) ⟨4437863, by rfl⟩ : syracuseStep 5917151 = 8875727) B8875727
theorem B7999739 : Blo 1845624 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B4674743 : Blo 1845624 4674743 := bstep (se 1 (by rfl) ⟨3506057, by rfl⟩ : syracuseStep 4674743 = 7012115) B7012115
theorem B21330785 : Blo 1845624 21330785 := bstep (se 2 (by rfl) ⟨7999044, by rfl⟩ : syracuseStep 21330785 = 15998089) B15998089
theorem B31562783 : Blo 1845624 31562783 := bstep (se 1 (by rfl) ⟨23672087, by rfl⟩ : syracuseStep 31562783 = 47344175) B47344175
theorem B5333159 : Blo 1845624 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B15779069 : Blo 1845624 15779069 := bstep (se 3 (by rfl) ⟨2958575, by rfl⟩ : syracuseStep 15779069 = 5917151) B5917151
theorem B3116495 : Blo 1845624 3116495 := bstep (se 1 (by rfl) ⟨2337371, by rfl⟩ : syracuseStep 3116495 = 4674743) B4674743
theorem B21041855 : Blo 1845624 21041855 := bstep (se 1 (by rfl) ⟨15781391, by rfl⟩ : syracuseStep 21041855 = 31562783) B31562783
theorem B56882093 : Blo 1845624 56882093 := bstep (se 3 (by rfl) ⟨10665392, by rfl⟩ : syracuseStep 56882093 = 21330785) B21330785
theorem B14221757 : Blo 1845624 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B10519379 : Blo 1845624 10519379 := bstep (se 1 (by rfl) ⟨7889534, by rfl⟩ : syracuseStep 10519379 = 15779069) B15779069
theorem B151685581 : Blo 1845624 151685581 := bstep (se 3 (by rfl) ⟨28441046, by rfl⟩ : syracuseStep 151685581 = 56882093) B56882093
theorem B14027903 : Blo 1845624 14027903 := bstep (se 1 (by rfl) ⟨10520927, by rfl⟩ : syracuseStep 14027903 = 21041855) B21041855
theorem B2077663 : Blo 1845624 2077663 := bstep (se 1 (by rfl) ⟨1558247, by rfl⟩ : syracuseStep 2077663 = 3116495) B3116495
theorem B7012919 : Blo 1845624 7012919 := bstep (se 1 (by rfl) ⟨5259689, by rfl⟩ : syracuseStep 7012919 = 10519379) B10519379
theorem B2770217 : Blo 1845624 2770217 := bstep (se 2 (by rfl) ⟨1038831, by rfl⟩ : syracuseStep 2770217 = 2077663) B2077663
theorem B202247441 : Blo 1845624 202247441 := bstep (se 2 (by rfl) ⟨75842790, by rfl⟩ : syracuseStep 202247441 = 151685581) B151685581
theorem B37924685 : Blo 1845624 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B9351935 : Blo 1845624 9351935 := bstep (se 1 (by rfl) ⟨7013951, by rfl⟩ : syracuseStep 9351935 = 14027903) B14027903
theorem B6234623 : Blo 1845624 6234623 := bstep (se 1 (by rfl) ⟨4675967, by rfl⟩ : syracuseStep 6234623 = 9351935) B9351935
theorem B25283123 : Blo 1845624 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B1846811 : Blo 1845624 1846811 := bstep (se 1 (by rfl) ⟨1385108, by rfl⟩ : syracuseStep 1846811 = 2770217) B2770217
theorem B4675279 : Blo 1845624 4675279 := bstep (se 1 (by rfl) ⟨3506459, by rfl⟩ : syracuseStep 4675279 = 7012919) B7012919
theorem B134831627 : Blo 1845624 134831627 := bstep (se 1 (by rfl) ⟨101123720, by rfl⟩ : syracuseStep 134831627 = 202247441) B202247441
theorem B4156415 : Blo 1845624 4156415 := bstep (se 1 (by rfl) ⟨3117311, by rfl⟩ : syracuseStep 4156415 = 6234623) B6234623
theorem B16855415 : Blo 1845624 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B89887751 : Blo 1845624 89887751 := bstep (se 1 (by rfl) ⟨67415813, by rfl⟩ : syracuseStep 89887751 = 134831627) B134831627
theorem B6233705 : Blo 1845624 6233705 := bstep (se 2 (by rfl) ⟨2337639, by rfl⟩ : syracuseStep 6233705 = 4675279) B4675279
theorem B59925167 : Blo 1845624 59925167 := bstep (se 1 (by rfl) ⟨44943875, by rfl⟩ : syracuseStep 59925167 = 89887751) B89887751
theorem B2770943 : Blo 1845624 2770943 := bstep (se 1 (by rfl) ⟨2078207, by rfl⟩ : syracuseStep 2770943 = 4156415) B4156415
theorem B4155803 : Blo 1845624 4155803 := bstep (se 1 (by rfl) ⟨3116852, by rfl⟩ : syracuseStep 4155803 = 6233705) B6233705
theorem B11236943 : Blo 1845624 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B2770535 : Blo 1845624 2770535 := bstep (se 1 (by rfl) ⟨2077901, by rfl⟩ : syracuseStep 2770535 = 4155803) B4155803
theorem B7491295 : Blo 1845624 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B1847295 : Blo 1845624 1847295 := bstep (se 1 (by rfl) ⟨1385471, by rfl⟩ : syracuseStep 1847295 = 2770943) B2770943
theorem B39950111 : Blo 1845624 39950111 := bstep (se 1 (by rfl) ⟨29962583, by rfl⟩ : syracuseStep 39950111 = 59925167) B59925167
theorem B39953573 : Blo 1845624 39953573 := bstep (se 4 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 39953573 = 7491295) B7491295
theorem B26633407 : Blo 1845624 26633407 := bstep (se 1 (by rfl) ⟨19975055, by rfl⟩ : syracuseStep 26633407 = 39950111) B39950111
theorem B1847023 : Blo 1845624 1847023 := bstep (se 1 (by rfl) ⟨1385267, by rfl⟩ : syracuseStep 1847023 = 2770535) B2770535
theorem B26635715 : Blo 1845624 26635715 := bstep (se 1 (by rfl) ⟨19976786, by rfl⟩ : syracuseStep 26635715 = 39953573) B39953573
theorem B35511209 : Blo 1845624 35511209 := bstep (se 2 (by rfl) ⟨13316703, by rfl⟩ : syracuseStep 35511209 = 26633407) B26633407
theorem B17757143 : Blo 1845624 17757143 := bstep (se 1 (by rfl) ⟨13317857, by rfl⟩ : syracuseStep 17757143 = 26635715) B26635715
theorem B23674139 : Blo 1845624 23674139 := bstep (se 1 (by rfl) ⟨17755604, by rfl⟩ : syracuseStep 23674139 = 35511209) B35511209
theorem B11838095 : Blo 1845624 11838095 := bstep (se 1 (by rfl) ⟨8878571, by rfl⟩ : syracuseStep 11838095 = 17757143) B17757143
theorem B15782759 : Blo 1845624 15782759 := bstep (se 1 (by rfl) ⟨11837069, by rfl⟩ : syracuseStep 15782759 = 23674139) B23674139
theorem B7892063 : Blo 1845624 7892063 := bstep (se 1 (by rfl) ⟨5919047, by rfl⟩ : syracuseStep 7892063 = 11838095) B11838095
theorem B10521839 : Blo 1845624 10521839 := bstep (se 1 (by rfl) ⟨7891379, by rfl⟩ : syracuseStep 10521839 = 15782759) B15782759
theorem B5261375 : Blo 1845624 5261375 := bstep (se 1 (by rfl) ⟨3946031, by rfl⟩ : syracuseStep 5261375 = 7892063) B7892063
theorem B7014559 : Blo 1845624 7014559 := bstep (se 1 (by rfl) ⟨5260919, by rfl⟩ : syracuseStep 7014559 = 10521839) B10521839
theorem B14030333 : Blo 1845624 14030333 := bstep (se 3 (by rfl) ⟨2630687, by rfl⟩ : syracuseStep 14030333 = 5261375) B5261375
theorem B9352745 : Blo 1845624 9352745 := bstep (se 2 (by rfl) ⟨3507279, by rfl⟩ : syracuseStep 9352745 = 7014559) B7014559
theorem B6235163 : Blo 1845624 6235163 := bstep (se 1 (by rfl) ⟨4676372, by rfl⟩ : syracuseStep 6235163 = 9352745) B9352745
theorem B9353555 : Blo 1845624 9353555 := bstep (se 1 (by rfl) ⟨7015166, by rfl⟩ : syracuseStep 9353555 = 14030333) B14030333
theorem B6235703 : Blo 1845624 6235703 := bstep (se 1 (by rfl) ⟨4676777, by rfl⟩ : syracuseStep 6235703 = 9353555) B9353555
theorem B4156775 : Blo 1845624 4156775 := bstep (se 1 (by rfl) ⟨3117581, by rfl⟩ : syracuseStep 4156775 = 6235163) B6235163
theorem B2771183 : Blo 1845624 2771183 := bstep (se 1 (by rfl) ⟨2078387, by rfl⟩ : syracuseStep 2771183 = 4156775) B4156775
theorem B4157135 : Blo 1845624 4157135 := bstep (se 1 (by rfl) ⟨3117851, by rfl⟩ : syracuseStep 4157135 = 6235703) B6235703
theorem B2771423 : Blo 1845624 2771423 := bstep (se 1 (by rfl) ⟨2078567, by rfl⟩ : syracuseStep 2771423 = 4157135) B4157135
theorem B1847455 : Blo 1845624 1847455 := bstep (se 1 (by rfl) ⟨1385591, by rfl⟩ : syracuseStep 1847455 = 2771183) B2771183
theorem B1847615 : Blo 1845624 1847615 := bstep (se 1 (by rfl) ⟨1385711, by rfl⟩ : syracuseStep 1847615 = 2771423) B2771423

theorem C0 (j : ℕ) (h1 : 461406 ≤ j) (h2 : j ≤ 461905) : Blo 1845624 (4 * j + 3) := by
  interval_cases j
  · exact B1845627
  · exact B1845631
  · exact B1845635
  · exact B1845639
  · exact B1845643
  · exact B1845647
  · exact B1845651
  · exact B1845655
  · exact B1845659
  · exact B1845663
  · exact B1845667
  · exact B1845671
  · exact B1845675
  · exact B1845679
  · exact B1845683
  · exact B1845687
  · exact B1845691
  · exact B1845695
  · exact B1845699
  · exact B1845703
  · exact B1845707
  · exact B1845711
  · exact B1845715
  · exact B1845719
  · exact B1845723
  · exact B1845727
  · exact B1845731
  · exact B1845735
  · exact B1845739
  · exact B1845743
  · exact B1845747
  · exact B1845751
  · exact B1845755
  · exact B1845759
  · exact B1845763
  · exact B1845767
  · exact B1845771
  · exact B1845775
  · exact B1845779
  · exact B1845783
  · exact B1845787
  · exact B1845791
  · exact B1845795
  · exact B1845799
  · exact B1845803
  · exact B1845807
  · exact B1845811
  · exact B1845815
  · exact B1845819
  · exact B1845823
  · exact B1845827
  · exact B1845831
  · exact B1845835
  · exact B1845839
  · exact B1845843
  · exact B1845847
  · exact B1845851
  · exact B1845855
  · exact B1845859
  · exact B1845863
  · exact B1845867
  · exact B1845871
  · exact B1845875
  · exact B1845879
  · exact B1845883
  · exact B1845887
  · exact B1845891
  · exact B1845895
  · exact B1845899
  · exact B1845903
  · exact B1845907
  · exact B1845911
  · exact B1845915
  · exact B1845919
  · exact B1845923
  · exact B1845927
  · exact B1845931
  · exact B1845935
  · exact B1845939
  · exact B1845943
  · exact B1845947
  · exact B1845951
  · exact B1845955
  · exact B1845959
  · exact B1845963
  · exact B1845967
  · exact B1845971
  · exact B1845975
  · exact B1845979
  · exact B1845983
  · exact B1845987
  · exact B1845991
  · exact B1845995
  · exact B1845999
  · exact B1846003
  · exact B1846007
  · exact B1846011
  · exact B1846015
  · exact B1846019
  · exact B1846023
  · exact B1846027
  · exact B1846031
  · exact B1846035
  · exact B1846039
  · exact B1846043
  · exact B1846047
  · exact B1846051
  · exact B1846055
  · exact B1846059
  · exact B1846063
  · exact B1846067
  · exact B1846071
  · exact B1846075
  · exact B1846079
  · exact B1846083
  · exact B1846087
  · exact B1846091
  · exact B1846095
  · exact B1846099
  · exact B1846103
  · exact B1846107
  · exact B1846111
  · exact B1846115
  · exact B1846119
  · exact B1846123
  · exact B1846127
  · exact B1846131
  · exact B1846135
  · exact B1846139
  · exact B1846143
  · exact B1846147
  · exact B1846151
  · exact B1846155
  · exact B1846159
  · exact B1846163
  · exact B1846167
  · exact B1846171
  · exact B1846175
  · exact B1846179
  · exact B1846183
  · exact B1846187
  · exact B1846191
  · exact B1846195
  · exact B1846199
  · exact B1846203
  · exact B1846207
  · exact B1846211
  · exact B1846215
  · exact B1846219
  · exact B1846223
  · exact B1846227
  · exact B1846231
  · exact B1846235
  · exact B1846239
  · exact B1846243
  · exact B1846247
  · exact B1846251
  · exact B1846255
  · exact B1846259
  · exact B1846263
  · exact B1846267
  · exact B1846271
  · exact B1846275
  · exact B1846279
  · exact B1846283
  · exact B1846287
  · exact B1846291
  · exact B1846295
  · exact B1846299
  · exact B1846303
  · exact B1846307
  · exact B1846311
  · exact B1846315
  · exact B1846319
  · exact B1846323
  · exact B1846327
  · exact B1846331
  · exact B1846335
  · exact B1846339
  · exact B1846343
  · exact B1846347
  · exact B1846351
  · exact B1846355
  · exact B1846359
  · exact B1846363
  · exact B1846367
  · exact B1846371
  · exact B1846375
  · exact B1846379
  · exact B1846383
  · exact B1846387
  · exact B1846391
  · exact B1846395
  · exact B1846399
  · exact B1846403
  · exact B1846407
  · exact B1846411
  · exact B1846415
  · exact B1846419
  · exact B1846423
  · exact B1846427
  · exact B1846431
  · exact B1846435
  · exact B1846439
  · exact B1846443
  · exact B1846447
  · exact B1846451
  · exact B1846455
  · exact B1846459
  · exact B1846463
  · exact B1846467
  · exact B1846471
  · exact B1846475
  · exact B1846479
  · exact B1846483
  · exact B1846487
  · exact B1846491
  · exact B1846495
  · exact B1846499
  · exact B1846503
  · exact B1846507
  · exact B1846511
  · exact B1846515
  · exact B1846519
  · exact B1846523
  · exact B1846527
  · exact B1846531
  · exact B1846535
  · exact B1846539
  · exact B1846543
  · exact B1846547
  · exact B1846551
  · exact B1846555
  · exact B1846559
  · exact B1846563
  · exact B1846567
  · exact B1846571
  · exact B1846575
  · exact B1846579
  · exact B1846583
  · exact B1846587
  · exact B1846591
  · exact B1846595
  · exact B1846599
  · exact B1846603
  · exact B1846607
  · exact B1846611
  · exact B1846615
  · exact B1846619
  · exact B1846623
  · exact B1846627
  · exact B1846631
  · exact B1846635
  · exact B1846639
  · exact B1846643
  · exact B1846647
  · exact B1846651
  · exact B1846655
  · exact B1846659
  · exact B1846663
  · exact B1846667
  · exact B1846671
  · exact B1846675
  · exact B1846679
  · exact B1846683
  · exact B1846687
  · exact B1846691
  · exact B1846695
  · exact B1846699
  · exact B1846703
  · exact B1846707
  · exact B1846711
  · exact B1846715
  · exact B1846719
  · exact B1846723
  · exact B1846727
  · exact B1846731
  · exact B1846735
  · exact B1846739
  · exact B1846743
  · exact B1846747
  · exact B1846751
  · exact B1846755
  · exact B1846759
  · exact B1846763
  · exact B1846767
  · exact B1846771
  · exact B1846775
  · exact B1846779
  · exact B1846783
  · exact B1846787
  · exact B1846791
  · exact B1846795
  · exact B1846799
  · exact B1846803
  · exact B1846807
  · exact B1846811
  · exact B1846815
  · exact B1846819
  · exact B1846823
  · exact B1846827
  · exact B1846831
  · exact B1846835
  · exact B1846839
  · exact B1846843
  · exact B1846847
  · exact B1846851
  · exact B1846855
  · exact B1846859
  · exact B1846863
  · exact B1846867
  · exact B1846871
  · exact B1846875
  · exact B1846879
  · exact B1846883
  · exact B1846887
  · exact B1846891
  · exact B1846895
  · exact B1846899
  · exact B1846903
  · exact B1846907
  · exact B1846911
  · exact B1846915
  · exact B1846919
  · exact B1846923
  · exact B1846927
  · exact B1846931
  · exact B1846935
  · exact B1846939
  · exact B1846943
  · exact B1846947
  · exact B1846951
  · exact B1846955
  · exact B1846959
  · exact B1846963
  · exact B1846967
  · exact B1846971
  · exact B1846975
  · exact B1846979
  · exact B1846983
  · exact B1846987
  · exact B1846991
  · exact B1846995
  · exact B1846999
  · exact B1847003
  · exact B1847007
  · exact B1847011
  · exact B1847015
  · exact B1847019
  · exact B1847023
  · exact B1847027
  · exact B1847031
  · exact B1847035
  · exact B1847039
  · exact B1847043
  · exact B1847047
  · exact B1847051
  · exact B1847055
  · exact B1847059
  · exact B1847063
  · exact B1847067
  · exact B1847071
  · exact B1847075
  · exact B1847079
  · exact B1847083
  · exact B1847087
  · exact B1847091
  · exact B1847095
  · exact B1847099
  · exact B1847103
  · exact B1847107
  · exact B1847111
  · exact B1847115
  · exact B1847119
  · exact B1847123
  · exact B1847127
  · exact B1847131
  · exact B1847135
  · exact B1847139
  · exact B1847143
  · exact B1847147
  · exact B1847151
  · exact B1847155
  · exact B1847159
  · exact B1847163
  · exact B1847167
  · exact B1847171
  · exact B1847175
  · exact B1847179
  · exact B1847183
  · exact B1847187
  · exact B1847191
  · exact B1847195
  · exact B1847199
  · exact B1847203
  · exact B1847207
  · exact B1847211
  · exact B1847215
  · exact B1847219
  · exact B1847223
  · exact B1847227
  · exact B1847231
  · exact B1847235
  · exact B1847239
  · exact B1847243
  · exact B1847247
  · exact B1847251
  · exact B1847255
  · exact B1847259
  · exact B1847263
  · exact B1847267
  · exact B1847271
  · exact B1847275
  · exact B1847279
  · exact B1847283
  · exact B1847287
  · exact B1847291
  · exact B1847295
  · exact B1847299
  · exact B1847303
  · exact B1847307
  · exact B1847311
  · exact B1847315
  · exact B1847319
  · exact B1847323
  · exact B1847327
  · exact B1847331
  · exact B1847335
  · exact B1847339
  · exact B1847343
  · exact B1847347
  · exact B1847351
  · exact B1847355
  · exact B1847359
  · exact B1847363
  · exact B1847367
  · exact B1847371
  · exact B1847375
  · exact B1847379
  · exact B1847383
  · exact B1847387
  · exact B1847391
  · exact B1847395
  · exact B1847399
  · exact B1847403
  · exact B1847407
  · exact B1847411
  · exact B1847415
  · exact B1847419
  · exact B1847423
  · exact B1847427
  · exact B1847431
  · exact B1847435
  · exact B1847439
  · exact B1847443
  · exact B1847447
  · exact B1847451
  · exact B1847455
  · exact B1847459
  · exact B1847463
  · exact B1847467
  · exact B1847471
  · exact B1847475
  · exact B1847479
  · exact B1847483
  · exact B1847487
  · exact B1847491
  · exact B1847495
  · exact B1847499
  · exact B1847503
  · exact B1847507
  · exact B1847511
  · exact B1847515
  · exact B1847519
  · exact B1847523
  · exact B1847527
  · exact B1847531
  · exact B1847535
  · exact B1847539
  · exact B1847543
  · exact B1847547
  · exact B1847551
  · exact B1847555
  · exact B1847559
  · exact B1847563
  · exact B1847567
  · exact B1847571
  · exact B1847575
  · exact B1847579
  · exact B1847583
  · exact B1847587
  · exact B1847591
  · exact B1847595
  · exact B1847599
  · exact B1847603
  · exact B1847607
  · exact B1847611
  · exact B1847615
  · exact B1847619
  · exact B1847623

theorem solution (m : ℕ) (hlo : 1845624 ≤ m) (hhi : m ≤ 1847624) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 461406 ≤ j := by omega
    have hj2 : j ≤ 461905 := by omega
    have hb : Blo 1845624 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
