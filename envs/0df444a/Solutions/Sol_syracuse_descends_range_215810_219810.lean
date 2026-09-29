-- Prove2me | solution 1 for syracuse_descends_range_215810_219810
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:55.983219+00:00
-- url     : https://prove2.me/submissions/f07ecf3f-e951-424d-8ee7-b1da66bf6ae7

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


theorem B491525 : Blo 215810 491525 := bbase (se 4 (by rfl) ⟨46080, by rfl⟩ : syracuseStep 491525 = 92161) (by norm_num)
theorem B294925 : Blo 215810 294925 := bbase (se 3 (by rfl) ⟨55298, by rfl⟩ : syracuseStep 294925 = 110597) (by norm_num)
theorem B262165 : Blo 215810 262165 := bbase (se 6 (by rfl) ⟨6144, by rfl⟩ : syracuseStep 262165 = 12289) (by norm_num)
theorem B327701 : Blo 215810 327701 := bbase (se 6 (by rfl) ⟨7680, by rfl⟩ : syracuseStep 327701 = 15361) (by norm_num)
theorem B327725 : Blo 215810 327725 := bbase (se 3 (by rfl) ⟨61448, by rfl⟩ : syracuseStep 327725 = 122897) (by norm_num)
theorem B327749 : Blo 215810 327749 := bbase (se 4 (by rfl) ⟨30726, by rfl⟩ : syracuseStep 327749 = 61453) (by norm_num)
theorem B491597 : Blo 215810 491597 := bbase (se 3 (by rfl) ⟨92174, by rfl⟩ : syracuseStep 491597 = 184349) (by norm_num)
theorem B327773 : Blo 215810 327773 := bbase (se 3 (by rfl) ⟨61457, by rfl⟩ : syracuseStep 327773 = 122915) (by norm_num)
theorem B262261 : Blo 215810 262261 := bbase (se 5 (by rfl) ⟨12293, by rfl⟩ : syracuseStep 262261 = 24587) (by norm_num)
theorem B327797 : Blo 215810 327797 := bbase (se 5 (by rfl) ⟨15365, by rfl⟩ : syracuseStep 327797 = 30731) (by norm_num)
theorem B393349 : Blo 215810 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B327821 : Blo 215810 327821 := bbase (se 3 (by rfl) ⟨61466, by rfl⟩ : syracuseStep 327821 = 122933) (by norm_num)
theorem B491669 : Blo 215810 491669 := bbase (se 6 (by rfl) ⟨11523, by rfl⟩ : syracuseStep 491669 = 23047) (by norm_num)
theorem B327845 : Blo 215810 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B327869 : Blo 215810 327869 := bbase (se 3 (by rfl) ⟨61475, by rfl⟩ : syracuseStep 327869 = 122951) (by norm_num)
theorem B327893 : Blo 215810 327893 := bbase (se 7 (by rfl) ⟨3842, by rfl⟩ : syracuseStep 327893 = 7685) (by norm_num)
theorem B491741 : Blo 215810 491741 := bbase (se 3 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 491741 = 184403) (by norm_num)
theorem B327917 : Blo 215810 327917 := bbase (se 3 (by rfl) ⟨61484, by rfl⟩ : syracuseStep 327917 = 122969) (by norm_num)
theorem B327941 : Blo 215810 327941 := bbase (se 4 (by rfl) ⟨30744, by rfl⟩ : syracuseStep 327941 = 61489) (by norm_num)
theorem B327965 : Blo 215810 327965 := bbase (se 3 (by rfl) ⟨61493, by rfl⟩ : syracuseStep 327965 = 122987) (by norm_num)
theorem B491813 : Blo 215810 491813 := bbase (se 4 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 491813 = 92215) (by norm_num)
theorem B622885 : Blo 215810 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B327989 : Blo 215810 327989 := bbase (se 5 (by rfl) ⟨15374, by rfl⟩ : syracuseStep 327989 = 30749) (by norm_num)
theorem B328013 : Blo 215810 328013 := bbase (se 3 (by rfl) ⟨61502, by rfl⟩ : syracuseStep 328013 = 123005) (by norm_num)
theorem B328037 : Blo 215810 328037 := bbase (se 4 (by rfl) ⟨30753, by rfl⟩ : syracuseStep 328037 = 61507) (by norm_num)
theorem B491885 : Blo 215810 491885 := bbase (se 3 (by rfl) ⟨92228, by rfl⟩ : syracuseStep 491885 = 184457) (by norm_num)
theorem B328061 : Blo 215810 328061 := bbase (se 3 (by rfl) ⟨61511, by rfl⟩ : syracuseStep 328061 = 123023) (by norm_num)
theorem B328085 : Blo 215810 328085 := bbase (se 6 (by rfl) ⟨7689, by rfl⟩ : syracuseStep 328085 = 15379) (by norm_num)
theorem B328109 : Blo 215810 328109 := bbase (se 3 (by rfl) ⟨61520, by rfl⟩ : syracuseStep 328109 = 123041) (by norm_num)
theorem B491957 : Blo 215810 491957 := bbase (se 5 (by rfl) ⟨23060, by rfl⟩ : syracuseStep 491957 = 46121) (by norm_num)
theorem B328133 : Blo 215810 328133 := bbase (se 4 (by rfl) ⟨30762, by rfl⟩ : syracuseStep 328133 = 61525) (by norm_num)
theorem B623045 : Blo 215810 623045 := bbase (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) (by norm_num)
theorem B328157 : Blo 215810 328157 := bbase (se 3 (by rfl) ⟨61529, by rfl⟩ : syracuseStep 328157 = 123059) (by norm_num)
theorem B262645 : Blo 215810 262645 := bbase (se 5 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 262645 = 24623) (by norm_num)
theorem B328181 : Blo 215810 328181 := bbase (se 5 (by rfl) ⟨15383, by rfl⟩ : syracuseStep 328181 = 30767) (by norm_num)
theorem B492029 : Blo 215810 492029 := bbase (se 3 (by rfl) ⟨92255, by rfl⟩ : syracuseStep 492029 = 184511) (by norm_num)
theorem B328205 : Blo 215810 328205 := bbase (se 3 (by rfl) ⟨61538, by rfl⟩ : syracuseStep 328205 = 123077) (by norm_num)
theorem B328229 : Blo 215810 328229 := bbase (se 4 (by rfl) ⟨30771, by rfl⟩ : syracuseStep 328229 = 61543) (by norm_num)
theorem B328253 : Blo 215810 328253 := bbase (se 3 (by rfl) ⟨61547, by rfl⟩ : syracuseStep 328253 = 123095) (by norm_num)
theorem B787013 : Blo 215810 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B492101 : Blo 215810 492101 := bbase (se 4 (by rfl) ⟨46134, by rfl⟩ : syracuseStep 492101 = 92269) (by norm_num)
theorem B328277 : Blo 215810 328277 := bbase (se 8 (by rfl) ⟨1923, by rfl⟩ : syracuseStep 328277 = 3847) (by norm_num)
theorem B328301 : Blo 215810 328301 := bbase (se 3 (by rfl) ⟨61556, by rfl⟩ : syracuseStep 328301 = 123113) (by norm_num)
theorem B328325 : Blo 215810 328325 := bbase (se 4 (by rfl) ⟨30780, by rfl⟩ : syracuseStep 328325 = 61561) (by norm_num)
theorem B492173 : Blo 215810 492173 := bbase (se 3 (by rfl) ⟨92282, by rfl⟩ : syracuseStep 492173 = 184565) (by norm_num)
theorem B1049237 : Blo 215810 1049237 := bbase (se 6 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 1049237 = 49183) (by norm_num)
theorem B328349 : Blo 215810 328349 := bbase (se 3 (by rfl) ⟨61565, by rfl⟩ : syracuseStep 328349 = 123131) (by norm_num)
theorem B623285 : Blo 215810 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B328373 : Blo 215810 328373 := bbase (se 5 (by rfl) ⟨15392, by rfl⟩ : syracuseStep 328373 = 30785) (by norm_num)
theorem B328397 : Blo 215810 328397 := bbase (se 3 (by rfl) ⟨61574, by rfl⟩ : syracuseStep 328397 = 123149) (by norm_num)
theorem B492245 : Blo 215810 492245 := bbase (se 7 (by rfl) ⟨5768, by rfl⟩ : syracuseStep 492245 = 11537) (by norm_num)
theorem B328421 : Blo 215810 328421 := bbase (se 4 (by rfl) ⟨30789, by rfl⟩ : syracuseStep 328421 = 61579) (by norm_num)
theorem B328445 : Blo 215810 328445 := bbase (se 3 (by rfl) ⟨61583, by rfl⟩ : syracuseStep 328445 = 123167) (by norm_num)
theorem B819989 : Blo 215810 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B328469 : Blo 215810 328469 := bbase (se 6 (by rfl) ⟨7698, by rfl⟩ : syracuseStep 328469 = 15397) (by norm_num)
theorem B492317 : Blo 215810 492317 := bbase (se 3 (by rfl) ⟨92309, by rfl⟩ : syracuseStep 492317 = 184619) (by norm_num)
theorem B328493 : Blo 215810 328493 := bbase (se 3 (by rfl) ⟨61592, by rfl⟩ : syracuseStep 328493 = 123185) (by norm_num)
theorem B328517 : Blo 215810 328517 := bbase (se 4 (by rfl) ⟨30798, by rfl⟩ : syracuseStep 328517 = 61597) (by norm_num)
theorem B328541 : Blo 215810 328541 := bbase (se 3 (by rfl) ⟨61601, by rfl⟩ : syracuseStep 328541 = 123203) (by norm_num)
theorem B492389 : Blo 215810 492389 := bbase (se 4 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 492389 = 92323) (by norm_num)
theorem B623477 : Blo 215810 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B328565 : Blo 215810 328565 := bbase (se 5 (by rfl) ⟨15401, by rfl⟩ : syracuseStep 328565 = 30803) (by norm_num)
theorem B328589 : Blo 215810 328589 := bbase (se 3 (by rfl) ⟨61610, by rfl⟩ : syracuseStep 328589 = 123221) (by norm_num)
theorem B328613 : Blo 215810 328613 := bbase (se 4 (by rfl) ⟨30807, by rfl⟩ : syracuseStep 328613 = 61615) (by norm_num)
theorem B492461 : Blo 215810 492461 := bbase (se 3 (by rfl) ⟨92336, by rfl⟩ : syracuseStep 492461 = 184673) (by norm_num)
theorem B263093 : Blo 215810 263093 := bbase (se 5 (by rfl) ⟨12332, by rfl⟩ : syracuseStep 263093 = 24665) (by norm_num)
theorem B328637 : Blo 215810 328637 := bbase (se 3 (by rfl) ⟨61619, by rfl⟩ : syracuseStep 328637 = 123239) (by norm_num)
theorem B328661 : Blo 215810 328661 := bbase (se 7 (by rfl) ⟨3851, by rfl⟩ : syracuseStep 328661 = 7703) (by norm_num)
theorem B328685 : Blo 215810 328685 := bbase (se 3 (by rfl) ⟨61628, by rfl⟩ : syracuseStep 328685 = 123257) (by norm_num)
theorem B492533 : Blo 215810 492533 := bbase (se 5 (by rfl) ⟨23087, by rfl⟩ : syracuseStep 492533 = 46175) (by norm_num)
theorem B328709 : Blo 215810 328709 := bbase (se 4 (by rfl) ⟨30816, by rfl⟩ : syracuseStep 328709 = 61633) (by norm_num)
theorem B328733 : Blo 215810 328733 := bbase (se 3 (by rfl) ⟨61637, by rfl⟩ : syracuseStep 328733 = 123275) (by norm_num)
theorem B820277 : Blo 215810 820277 := bbase (se 5 (by rfl) ⟨38450, by rfl⟩ : syracuseStep 820277 = 76901) (by norm_num)
theorem B328757 : Blo 215810 328757 := bbase (se 5 (by rfl) ⟨15410, by rfl⟩ : syracuseStep 328757 = 30821) (by norm_num)
theorem B492605 : Blo 215810 492605 := bbase (se 3 (by rfl) ⟨92363, by rfl⟩ : syracuseStep 492605 = 184727) (by norm_num)
theorem B328781 : Blo 215810 328781 := bbase (se 3 (by rfl) ⟨61646, by rfl⟩ : syracuseStep 328781 = 123293) (by norm_num)
theorem B328805 : Blo 215810 328805 := bbase (se 4 (by rfl) ⟨30825, by rfl⟩ : syracuseStep 328805 = 61651) (by norm_num)
theorem B328829 : Blo 215810 328829 := bbase (se 3 (by rfl) ⟨61655, by rfl⟩ : syracuseStep 328829 = 123311) (by norm_num)
theorem B492677 : Blo 215810 492677 := bbase (se 4 (by rfl) ⟨46188, by rfl⟩ : syracuseStep 492677 = 92377) (by norm_num)
theorem B328853 : Blo 215810 328853 := bbase (se 6 (by rfl) ⟨7707, by rfl⟩ : syracuseStep 328853 = 15415) (by norm_num)
theorem B328877 : Blo 215810 328877 := bbase (se 3 (by rfl) ⟨61664, by rfl⟩ : syracuseStep 328877 = 123329) (by norm_num)
theorem B328901 : Blo 215810 328901 := bbase (se 4 (by rfl) ⟨30834, by rfl⟩ : syracuseStep 328901 = 61669) (by norm_num)
theorem B492749 : Blo 215810 492749 := bbase (se 3 (by rfl) ⟨92390, by rfl⟩ : syracuseStep 492749 = 184781) (by norm_num)
theorem B328925 : Blo 215810 328925 := bbase (se 3 (by rfl) ⟨61673, by rfl⟩ : syracuseStep 328925 = 123347) (by norm_num)
theorem B525541 : Blo 215810 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B328949 : Blo 215810 328949 := bbase (se 5 (by rfl) ⟨15419, by rfl⟩ : syracuseStep 328949 = 30839) (by norm_num)
theorem B328973 : Blo 215810 328973 := bbase (se 3 (by rfl) ⟨61682, by rfl⟩ : syracuseStep 328973 = 123365) (by norm_num)
theorem B492821 : Blo 215810 492821 := bbase (se 6 (by rfl) ⟨11550, by rfl⟩ : syracuseStep 492821 = 23101) (by norm_num)
theorem B918821 : Blo 215810 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B328997 : Blo 215810 328997 := bbase (se 4 (by rfl) ⟨30843, by rfl⟩ : syracuseStep 328997 = 61687) (by norm_num)
theorem B329005 : Blo 215810 329005 := bbase (se 3 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 329005 = 123377) (by norm_num)
theorem B787765 : Blo 215810 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B329021 : Blo 215810 329021 := bbase (se 3 (by rfl) ⟨61691, by rfl⟩ : syracuseStep 329021 = 123383) (by norm_num)
theorem B230725 : Blo 215810 230725 := bbase (se 4 (by rfl) ⟨21630, by rfl⟩ : syracuseStep 230725 = 43261) (by norm_num)
theorem B329045 : Blo 215810 329045 := bbase (se 12 (by rfl) ⟨120, by rfl⟩ : syracuseStep 329045 = 241) (by norm_num)
theorem B492893 : Blo 215810 492893 := bbase (se 3 (by rfl) ⟨92417, by rfl⟩ : syracuseStep 492893 = 184835) (by norm_num)
theorem B329069 : Blo 215810 329069 := bbase (se 3 (by rfl) ⟨61700, by rfl⟩ : syracuseStep 329069 = 123401) (by norm_num)
theorem B296309 : Blo 215810 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B329093 : Blo 215810 329093 := bbase (se 4 (by rfl) ⟨30852, by rfl⟩ : syracuseStep 329093 = 61705) (by norm_num)
theorem B230797 : Blo 215810 230797 := bbase (se 3 (by rfl) ⟨43274, by rfl⟩ : syracuseStep 230797 = 86549) (by norm_num)
theorem B329117 : Blo 215810 329117 := bbase (se 3 (by rfl) ⟨61709, by rfl⟩ : syracuseStep 329117 = 123419) (by norm_num)
theorem B492965 : Blo 215810 492965 := bbase (se 4 (by rfl) ⟨46215, by rfl⟩ : syracuseStep 492965 = 92431) (by norm_num)
theorem B329141 : Blo 215810 329141 := bbase (se 5 (by rfl) ⟨15428, by rfl⟩ : syracuseStep 329141 = 30857) (by norm_num)
theorem B329165 : Blo 215810 329165 := bbase (se 3 (by rfl) ⟨61718, by rfl⟩ : syracuseStep 329165 = 123437) (by norm_num)
theorem B329189 : Blo 215810 329189 := bbase (se 4 (by rfl) ⟨30861, by rfl⟩ : syracuseStep 329189 = 61723) (by norm_num)
theorem B263657 : Blo 215810 263657 := bbase (se 2 (by rfl) ⟨98871, by rfl⟩ : syracuseStep 263657 = 197743) (by norm_num)
theorem B394733 : Blo 215810 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B493037 : Blo 215810 493037 := bbase (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) (by norm_num)
theorem B329213 : Blo 215810 329213 := bbase (se 3 (by rfl) ⟨61727, by rfl⟩ : syracuseStep 329213 = 123455) (by norm_num)
theorem B263693 : Blo 215810 263693 := bbase (se 3 (by rfl) ⟨49442, by rfl⟩ : syracuseStep 263693 = 98885) (by norm_num)
theorem B329237 : Blo 215810 329237 := bbase (se 6 (by rfl) ⟨7716, by rfl⟩ : syracuseStep 329237 = 15433) (by norm_num)
theorem B329261 : Blo 215810 329261 := bbase (se 3 (by rfl) ⟨61736, by rfl⟩ : syracuseStep 329261 = 123473) (by norm_num)
theorem B493109 : Blo 215810 493109 := bbase (se 5 (by rfl) ⟨23114, by rfl⟩ : syracuseStep 493109 = 46229) (by norm_num)
theorem B329285 : Blo 215810 329285 := bbase (se 4 (by rfl) ⟨30870, by rfl⟩ : syracuseStep 329285 = 61741) (by norm_num)
theorem B329309 : Blo 215810 329309 := bbase (se 3 (by rfl) ⟨61745, by rfl⟩ : syracuseStep 329309 = 123491) (by norm_num)
theorem B329333 : Blo 215810 329333 := bbase (se 5 (by rfl) ⟨15437, by rfl⟩ : syracuseStep 329333 = 30875) (by norm_num)
theorem B329341 : Blo 215810 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B493181 : Blo 215810 493181 := bbase (se 3 (by rfl) ⟨92471, by rfl⟩ : syracuseStep 493181 = 184943) (by norm_num)
theorem B394885 : Blo 215810 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B329357 : Blo 215810 329357 := bbase (se 3 (by rfl) ⟨61754, by rfl⟩ : syracuseStep 329357 = 123509) (by norm_num)
theorem B1574549 : Blo 215810 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B329381 : Blo 215810 329381 := bbase (se 4 (by rfl) ⟨30879, by rfl⟩ : syracuseStep 329381 = 61759) (by norm_num)
theorem B329405 : Blo 215810 329405 := bbase (se 3 (by rfl) ⟨61763, by rfl⟩ : syracuseStep 329405 = 123527) (by norm_num)
theorem B394949 : Blo 215810 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B493253 : Blo 215810 493253 := bbase (se 4 (by rfl) ⟨46242, by rfl⟩ : syracuseStep 493253 = 92485) (by norm_num)
theorem B329429 : Blo 215810 329429 := bbase (se 7 (by rfl) ⟨3860, by rfl⟩ : syracuseStep 329429 = 7721) (by norm_num)
theorem B329453 : Blo 215810 329453 := bbase (se 3 (by rfl) ⟨61772, by rfl⟩ : syracuseStep 329453 = 123545) (by norm_num)
theorem B231169 : Blo 215810 231169 := bbase (se 2 (by rfl) ⟨86688, by rfl⟩ : syracuseStep 231169 = 173377) (by norm_num)
theorem B329477 : Blo 215810 329477 := bbase (se 4 (by rfl) ⟨30888, by rfl⟩ : syracuseStep 329477 = 61777) (by norm_num)
theorem B493325 : Blo 215810 493325 := bbase (se 3 (by rfl) ⟨92498, by rfl⟩ : syracuseStep 493325 = 184997) (by norm_num)
theorem B329501 : Blo 215810 329501 := bbase (se 3 (by rfl) ⟨61781, by rfl⟩ : syracuseStep 329501 = 123563) (by norm_num)
theorem B263969 : Blo 215810 263969 := bbase (se 2 (by rfl) ⟨98988, by rfl⟩ : syracuseStep 263969 = 197977) (by norm_num)
theorem B329525 : Blo 215810 329525 := bbase (se 5 (by rfl) ⟨15446, by rfl⟩ : syracuseStep 329525 = 30893) (by norm_num)
theorem B264001 : Blo 215810 264001 := bbase (se 2 (by rfl) ⟨99000, by rfl⟩ : syracuseStep 264001 = 198001) (by norm_num)
theorem B329549 : Blo 215810 329549 := bbase (se 3 (by rfl) ⟨61790, by rfl⟩ : syracuseStep 329549 = 123581) (by norm_num)
theorem B395093 : Blo 215810 395093 := bbase (se 9 (by rfl) ⟨1157, by rfl⟩ : syracuseStep 395093 = 2315) (by norm_num)
theorem B493397 : Blo 215810 493397 := bbase (se 9 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 493397 = 2891) (by norm_num)
theorem B624469 : Blo 215810 624469 := bbase (se 9 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 624469 = 3659) (by norm_num)
theorem B264029 : Blo 215810 264029 := bbase (se 3 (by rfl) ⟨49505, by rfl⟩ : syracuseStep 264029 = 99011) (by norm_num)
theorem B329573 : Blo 215810 329573 := bbase (se 4 (by rfl) ⟨30897, by rfl⟩ : syracuseStep 329573 = 61795) (by norm_num)
theorem B1181557 : Blo 215810 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B329597 : Blo 215810 329597 := bbase (se 3 (by rfl) ⟨61799, by rfl⟩ : syracuseStep 329597 = 123599) (by norm_num)
theorem B526213 : Blo 215810 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B329621 : Blo 215810 329621 := bbase (se 6 (by rfl) ⟨7725, by rfl⟩ : syracuseStep 329621 = 15451) (by norm_num)
theorem B493469 : Blo 215810 493469 := bbase (se 3 (by rfl) ⟨92525, by rfl⟩ : syracuseStep 493469 = 185051) (by norm_num)
theorem B329645 : Blo 215810 329645 := bbase (se 3 (by rfl) ⟨61808, by rfl⟩ : syracuseStep 329645 = 123617) (by norm_num)
theorem B1869749 : Blo 215810 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B329669 : Blo 215810 329669 := bbase (se 4 (by rfl) ⟨30906, by rfl⟩ : syracuseStep 329669 = 61813) (by norm_num)
theorem B329693 : Blo 215810 329693 := bbase (se 3 (by rfl) ⟨61817, by rfl⟩ : syracuseStep 329693 = 123635) (by norm_num)
theorem B493541 : Blo 215810 493541 := bbase (se 4 (by rfl) ⟨46269, by rfl⟩ : syracuseStep 493541 = 92539) (by norm_num)
theorem B493613 : Blo 215810 493613 := bbase (se 3 (by rfl) ⟨92552, by rfl⟩ : syracuseStep 493613 = 185105) (by norm_num)
theorem B526445 : Blo 215810 526445 := bbase (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) (by norm_num)
theorem B493685 : Blo 215810 493685 := bbase (se 5 (by rfl) ⟨23141, by rfl⟩ : syracuseStep 493685 = 46283) (by norm_num)
theorem B231545 : Blo 215810 231545 := bbase (se 2 (by rfl) ⟨86829, by rfl⟩ : syracuseStep 231545 = 173659) (by norm_num)
theorem B493757 : Blo 215810 493757 := bbase (se 3 (by rfl) ⟨92579, by rfl⟩ : syracuseStep 493757 = 185159) (by norm_num)
theorem B231617 : Blo 215810 231617 := bbase (se 2 (by rfl) ⟨86856, by rfl⟩ : syracuseStep 231617 = 173713) (by norm_num)
theorem B821461 : Blo 215810 821461 := bbase (se 7 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 821461 = 19253) (by norm_num)
theorem B526589 : Blo 215810 526589 := bbase (se 3 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 526589 = 197471) (by norm_num)
theorem B493829 : Blo 215810 493829 := bbase (se 4 (by rfl) ⟨46296, by rfl⟩ : syracuseStep 493829 = 92593) (by norm_num)
theorem B2787605 : Blo 215810 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B788773 : Blo 215810 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B526637 : Blo 215810 526637 := bbase (se 3 (by rfl) ⟨98744, by rfl⟩ : syracuseStep 526637 = 197489) (by norm_num)
theorem B493901 : Blo 215810 493901 := bbase (se 3 (by rfl) ⟨92606, by rfl⟩ : syracuseStep 493901 = 185213) (by norm_num)
theorem B231805 : Blo 215810 231805 := bbase (se 3 (by rfl) ⟨43463, by rfl⟩ : syracuseStep 231805 = 86927) (by norm_num)
theorem B493973 : Blo 215810 493973 := bbase (se 6 (by rfl) ⟨11577, by rfl⟩ : syracuseStep 493973 = 23155) (by norm_num)
theorem B494045 : Blo 215810 494045 := bbase (se 3 (by rfl) ⟨92633, by rfl⟩ : syracuseStep 494045 = 185267) (by norm_num)
theorem B821765 : Blo 215810 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B494117 : Blo 215810 494117 := bbase (se 4 (by rfl) ⟨46323, by rfl⟩ : syracuseStep 494117 = 92647) (by norm_num)
theorem B231989 : Blo 215810 231989 := bbase (se 5 (by rfl) ⟨10874, by rfl⟩ : syracuseStep 231989 = 21749) (by norm_num)
theorem B461389 : Blo 215810 461389 := bbase (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) (by norm_num)
theorem B526925 : Blo 215810 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B494189 : Blo 215810 494189 := bbase (se 3 (by rfl) ⟨92660, by rfl⟩ : syracuseStep 494189 = 185321) (by norm_num)
theorem B658037 : Blo 215810 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B494261 : Blo 215810 494261 := bbase (se 5 (by rfl) ⟨23168, by rfl⟩ : syracuseStep 494261 = 46337) (by norm_num)
theorem B1247957 : Blo 215810 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B494333 : Blo 215810 494333 := bbase (se 3 (by rfl) ⟨92687, by rfl⟩ : syracuseStep 494333 = 185375) (by norm_num)
theorem B494405 : Blo 215810 494405 := bbase (se 4 (by rfl) ⟨46350, by rfl⟩ : syracuseStep 494405 = 92701) (by norm_num)
theorem B494477 : Blo 215810 494477 := bbase (se 3 (by rfl) ⟨92714, by rfl⟩ : syracuseStep 494477 = 185429) (by norm_num)
theorem B625573 : Blo 215810 625573 := bbase (se 4 (by rfl) ⟨58647, by rfl⟩ : syracuseStep 625573 = 117295) (by norm_num)
theorem B494549 : Blo 215810 494549 := bbase (se 7 (by rfl) ⟨5795, by rfl⟩ : syracuseStep 494549 = 11591) (by norm_num)
theorem B232741 : Blo 215810 232741 := bbase (se 4 (by rfl) ⟨21819, by rfl⟩ : syracuseStep 232741 = 43639) (by norm_num)
theorem B232813 : Blo 215810 232813 := bbase (se 3 (by rfl) ⟨43652, by rfl⟩ : syracuseStep 232813 = 87305) (by norm_num)
theorem B462277 : Blo 215810 462277 := bbase (se 4 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 462277 = 86677) (by norm_num)
theorem B232993 : Blo 215810 232993 := bbase (se 2 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 232993 = 174745) (by norm_num)
theorem B1248821 : Blo 215810 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B364189 : Blo 215810 364189 := bbase (se 3 (by rfl) ⟨68285, by rfl⟩ : syracuseStep 364189 = 136571) (by norm_num)
theorem B495325 : Blo 215810 495325 := bbase (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) (by norm_num)
theorem B364277 : Blo 215810 364277 := bbase (se 5 (by rfl) ⟨17075, by rfl⟩ : syracuseStep 364277 = 34151) (by norm_num)
theorem B15109973 : Blo 215810 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B364405 : Blo 215810 364405 := bbase (se 5 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 364405 = 34163) (by norm_num)
theorem B1249141 : Blo 215810 1249141 := bbase (se 5 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 1249141 = 117107) (by norm_num)
theorem B462773 : Blo 215810 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B364493 : Blo 215810 364493 := bbase (se 3 (by rfl) ⟨68342, by rfl⟩ : syracuseStep 364493 = 136685) (by norm_num)
theorem B233437 : Blo 215810 233437 := bbase (se 3 (by rfl) ⟨43769, by rfl⟩ : syracuseStep 233437 = 87539) (by norm_num)
theorem B495661 : Blo 215810 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B364621 : Blo 215810 364621 := bbase (se 3 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 364621 = 136733) (by norm_num)
theorem B233561 : Blo 215810 233561 := bbase (se 2 (by rfl) ⟨87585, by rfl⟩ : syracuseStep 233561 = 175171) (by norm_num)
theorem B364709 : Blo 215810 364709 := bbase (se 4 (by rfl) ⟨34191, by rfl⟩ : syracuseStep 364709 = 68383) (by norm_num)
theorem B2265365 : Blo 215810 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B364837 : Blo 215810 364837 := bbase (se 4 (by rfl) ⟨34203, by rfl⟩ : syracuseStep 364837 = 68407) (by norm_num)
theorem B233813 : Blo 215810 233813 := bbase (se 10 (by rfl) ⟨342, by rfl⟩ : syracuseStep 233813 = 685) (by norm_num)
theorem B364925 : Blo 215810 364925 := bbase (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) (by norm_num)
theorem B692725 : Blo 215810 692725 := bbase (se 5 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 692725 = 64943) (by norm_num)
theorem B365053 : Blo 215810 365053 := bbase (se 3 (by rfl) ⟨68447, by rfl⟩ : syracuseStep 365053 = 136895) (by norm_num)
theorem B823877 : Blo 215810 823877 := bbase (se 4 (by rfl) ⟨77238, by rfl⟩ : syracuseStep 823877 = 154477) (by norm_num)
theorem B365141 : Blo 215810 365141 := bbase (se 8 (by rfl) ⟨2139, by rfl⟩ : syracuseStep 365141 = 4279) (by norm_num)
theorem B365269 : Blo 215810 365269 := bbase (se 7 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 365269 = 8561) (by norm_num)
theorem B266965 : Blo 215810 266965 := bbase (se 7 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 266965 = 6257) (by norm_num)
theorem B234257 : Blo 215810 234257 := bbase (se 2 (by rfl) ⟨87846, by rfl⟩ : syracuseStep 234257 = 175693) (by norm_num)
theorem B463637 : Blo 215810 463637 := bbase (se 6 (by rfl) ⟨10866, by rfl⟩ : syracuseStep 463637 = 21733) (by norm_num)
theorem B365357 : Blo 215810 365357 := bbase (se 3 (by rfl) ⟨68504, by rfl⟩ : syracuseStep 365357 = 137009) (by norm_num)
theorem B332605 : Blo 215810 332605 := bbase (se 3 (by rfl) ⟨62363, by rfl⟩ : syracuseStep 332605 = 124727) (by norm_num)
theorem B824165 : Blo 215810 824165 := bbase (se 4 (by rfl) ⟨77265, by rfl⟩ : syracuseStep 824165 = 154531) (by norm_num)
theorem B496493 : Blo 215810 496493 := bbase (se 3 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 496493 = 186185) (by norm_num)
theorem B463781 : Blo 215810 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B365485 : Blo 215810 365485 := bbase (se 3 (by rfl) ⟨68528, by rfl⟩ : syracuseStep 365485 = 137057) (by norm_num)
theorem B365573 : Blo 215810 365573 := bbase (se 4 (by rfl) ⟨34272, by rfl⟩ : syracuseStep 365573 = 68545) (by norm_num)
theorem B234505 : Blo 215810 234505 := bbase (se 2 (by rfl) ⟨87939, by rfl⟩ : syracuseStep 234505 = 175879) (by norm_num)
theorem B365701 : Blo 215810 365701 := bbase (se 4 (by rfl) ⟨34284, by rfl⟩ : syracuseStep 365701 = 68569) (by norm_num)
theorem B365789 : Blo 215810 365789 := bbase (se 3 (by rfl) ⟨68585, by rfl⟩ : syracuseStep 365789 = 137171) (by norm_num)
theorem B365917 : Blo 215810 365917 := bbase (se 3 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 365917 = 137219) (by norm_num)
theorem B366005 : Blo 215810 366005 := bbase (se 5 (by rfl) ⟨17156, by rfl⟩ : syracuseStep 366005 = 34313) (by norm_num)
theorem B988661 : Blo 215810 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B366133 : Blo 215810 366133 := bbase (se 5 (by rfl) ⟨17162, by rfl⟩ : syracuseStep 366133 = 34325) (by norm_num)
theorem B366221 : Blo 215810 366221 := bbase (se 3 (by rfl) ⟨68666, by rfl⟩ : syracuseStep 366221 = 137333) (by norm_num)
theorem B464525 : Blo 215810 464525 := bbase (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) (by norm_num)
theorem B562877 : Blo 215810 562877 := bbase (se 3 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 562877 = 211079) (by norm_num)
theorem B235229 : Blo 215810 235229 := bbase (se 3 (by rfl) ⟨44105, by rfl⟩ : syracuseStep 235229 = 88211) (by norm_num)
theorem B366349 : Blo 215810 366349 := bbase (se 3 (by rfl) ⟨68690, by rfl⟩ : syracuseStep 366349 = 137381) (by norm_num)
theorem B1251125 : Blo 215810 1251125 := bbase (se 5 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 1251125 = 117293) (by norm_num)
theorem B366437 : Blo 215810 366437 := bbase (se 4 (by rfl) ⟨34353, by rfl⟩ : syracuseStep 366437 = 68707) (by norm_num)
theorem B366565 : Blo 215810 366565 := bbase (se 4 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 366565 = 68731) (by norm_num)
theorem B825349 : Blo 215810 825349 := bbase (se 4 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 825349 = 154753) (by norm_num)
theorem B366653 : Blo 215810 366653 := bbase (se 3 (by rfl) ⟨68747, by rfl⟩ : syracuseStep 366653 = 137495) (by norm_num)
theorem B366781 : Blo 215810 366781 := bbase (se 3 (by rfl) ⟨68771, by rfl⟩ : syracuseStep 366781 = 137543) (by norm_num)
theorem B366869 : Blo 215810 366869 := bbase (se 6 (by rfl) ⟨8598, by rfl⟩ : syracuseStep 366869 = 17197) (by norm_num)
theorem B825653 : Blo 215810 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B465277 : Blo 215810 465277 := bbase (se 3 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 465277 = 174479) (by norm_num)
theorem B366997 : Blo 215810 366997 := bbase (se 6 (by rfl) ⟨8601, by rfl⟩ : syracuseStep 366997 = 17203) (by norm_num)
theorem B367085 : Blo 215810 367085 := bbase (se 3 (by rfl) ⟨68828, by rfl⟩ : syracuseStep 367085 = 137657) (by norm_num)
theorem B465421 : Blo 215810 465421 := bbase (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) (by norm_num)
theorem B1645109 : Blo 215810 1645109 := bbase (se 5 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 1645109 = 154229) (by norm_num)
theorem B236125 : Blo 215810 236125 := bbase (se 3 (by rfl) ⟨44273, by rfl⟩ : syracuseStep 236125 = 88547) (by norm_num)
theorem B367213 : Blo 215810 367213 := bbase (se 3 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 367213 = 137705) (by norm_num)
theorem B498325 : Blo 215810 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B367301 : Blo 215810 367301 := bbase (se 4 (by rfl) ⟨34434, by rfl⟩ : syracuseStep 367301 = 68869) (by norm_num)
theorem B498397 : Blo 215810 498397 := bbase (se 3 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 498397 = 186899) (by norm_num)
theorem B367429 : Blo 215810 367429 := bbase (se 4 (by rfl) ⟨34446, by rfl⟩ : syracuseStep 367429 = 68893) (by norm_num)
theorem B465797 : Blo 215810 465797 := bbase (se 4 (by rfl) ⟨43668, by rfl⟩ : syracuseStep 465797 = 87337) (by norm_num)
theorem B367517 : Blo 215810 367517 := bbase (se 3 (by rfl) ⟨68909, by rfl⟩ : syracuseStep 367517 = 137819) (by norm_num)
theorem B662437 : Blo 215810 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B367645 : Blo 215810 367645 := bbase (se 3 (by rfl) ⟨68933, by rfl⟩ : syracuseStep 367645 = 137867) (by norm_num)
theorem B367733 : Blo 215810 367733 := bbase (se 5 (by rfl) ⟨17237, by rfl⟩ : syracuseStep 367733 = 34475) (by norm_num)
theorem B367861 : Blo 215810 367861 := bbase (se 5 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 367861 = 34487) (by norm_num)
theorem B466165 : Blo 215810 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B695557 : Blo 215810 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B1187093 : Blo 215810 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B924965 : Blo 215810 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B695621 : Blo 215810 695621 := bbase (se 4 (by rfl) ⟨65214, by rfl⟩ : syracuseStep 695621 = 130429) (by norm_num)
theorem B367949 : Blo 215810 367949 := bbase (se 3 (by rfl) ⟨68990, by rfl⟩ : syracuseStep 367949 = 137981) (by norm_num)
theorem B728405 : Blo 215810 728405 := bbase (se 11 (by rfl) ⟨533, by rfl⟩ : syracuseStep 728405 = 1067) (by norm_num)
theorem B368077 : Blo 215810 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B368165 : Blo 215810 368165 := bbase (se 4 (by rfl) ⟨34515, by rfl⟩ : syracuseStep 368165 = 69031) (by norm_num)
theorem B1777301 : Blo 215810 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B368293 : Blo 215810 368293 := bbase (se 4 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 368293 = 69055) (by norm_num)
theorem B368381 : Blo 215810 368381 := bbase (se 3 (by rfl) ⟨69071, by rfl⟩ : syracuseStep 368381 = 138143) (by norm_num)
theorem B728837 : Blo 215810 728837 := bbase (se 4 (by rfl) ⟨68328, by rfl⟩ : syracuseStep 728837 = 136657) (by norm_num)
theorem B368509 : Blo 215810 368509 := bbase (se 3 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 368509 = 138191) (by norm_num)
theorem B368597 : Blo 215810 368597 := bbase (se 7 (by rfl) ⟨4319, by rfl⟩ : syracuseStep 368597 = 8639) (by norm_num)
theorem B368725 : Blo 215810 368725 := bbase (se 8 (by rfl) ⟨2160, by rfl⟩ : syracuseStep 368725 = 4321) (by norm_num)
theorem B401501 : Blo 215810 401501 := bbase (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) (by norm_num)
theorem B368813 : Blo 215810 368813 := bbase (se 3 (by rfl) ⟨69152, by rfl⟩ : syracuseStep 368813 = 138305) (by norm_num)
theorem B729269 : Blo 215810 729269 := bbase (se 5 (by rfl) ⟨34184, by rfl⟩ : syracuseStep 729269 = 68369) (by norm_num)
theorem B2367701 : Blo 215810 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B368941 : Blo 215810 368941 := bbase (se 3 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 368941 = 138353) (by norm_num)
theorem B2662741 : Blo 215810 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B827765 : Blo 215810 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B369029 : Blo 215810 369029 := bbase (se 4 (by rfl) ⟨34596, by rfl⟩ : syracuseStep 369029 = 69193) (by norm_num)
theorem B369157 : Blo 215810 369157 := bbase (se 4 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 369157 = 69217) (by norm_num)
theorem B369245 : Blo 215810 369245 := bbase (se 3 (by rfl) ⟨69233, by rfl⟩ : syracuseStep 369245 = 138467) (by norm_num)
theorem B729701 : Blo 215810 729701 := bbase (se 4 (by rfl) ⟨68409, by rfl⟩ : syracuseStep 729701 = 136819) (by norm_num)
theorem B828053 : Blo 215810 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B467669 : Blo 215810 467669 := bbase (se 7 (by rfl) ⟨5480, by rfl⟩ : syracuseStep 467669 = 10961) (by norm_num)
theorem B369373 : Blo 215810 369373 := bbase (se 3 (by rfl) ⟨69257, by rfl⟩ : syracuseStep 369373 = 138515) (by norm_num)
theorem B369461 : Blo 215810 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B467813 : Blo 215810 467813 := bbase (se 4 (by rfl) ⟨43857, by rfl⟩ : syracuseStep 467813 = 87715) (by norm_num)
theorem B369589 : Blo 215810 369589 := bbase (se 5 (by rfl) ⟨17324, by rfl⟩ : syracuseStep 369589 = 34649) (by norm_num)
theorem B369677 : Blo 215810 369677 := bbase (se 3 (by rfl) ⟨69314, by rfl⟩ : syracuseStep 369677 = 138629) (by norm_num)
theorem B730133 : Blo 215810 730133 := bbase (se 6 (by rfl) ⟨17112, by rfl⟩ : syracuseStep 730133 = 34225) (by norm_num)
theorem B926741 : Blo 215810 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B369805 : Blo 215810 369805 := bbase (se 3 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 369805 = 138677) (by norm_num)
theorem B468173 : Blo 215810 468173 := bbase (se 3 (by rfl) ⟨87782, by rfl⟩ : syracuseStep 468173 = 175565) (by norm_num)
theorem B369893 : Blo 215810 369893 := bbase (se 4 (by rfl) ⟨34677, by rfl⟩ : syracuseStep 369893 = 69355) (by norm_num)
theorem B370021 : Blo 215810 370021 := bbase (se 4 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 370021 = 69379) (by norm_num)
theorem B370109 : Blo 215810 370109 := bbase (se 3 (by rfl) ⟨69395, by rfl⟩ : syracuseStep 370109 = 138791) (by norm_num)
theorem B730565 : Blo 215810 730565 := bbase (se 4 (by rfl) ⟨68490, by rfl⟩ : syracuseStep 730565 = 136981) (by norm_num)
theorem B1123877 : Blo 215810 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B370237 : Blo 215810 370237 := bbase (se 3 (by rfl) ⟨69419, by rfl⟩ : syracuseStep 370237 = 138839) (by norm_num)
theorem B370325 : Blo 215810 370325 := bbase (se 6 (by rfl) ⟨8679, by rfl⟩ : syracuseStep 370325 = 17359) (by norm_num)
theorem B370453 : Blo 215810 370453 := bbase (se 6 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 370453 = 17365) (by norm_num)
theorem B829237 : Blo 215810 829237 := bbase (se 5 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 829237 = 77741) (by norm_num)
theorem B1877813 : Blo 215810 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B370541 : Blo 215810 370541 := bbase (se 3 (by rfl) ⟨69476, by rfl⟩ : syracuseStep 370541 = 138953) (by norm_num)
theorem B730997 : Blo 215810 730997 := bbase (se 5 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 730997 = 68531) (by norm_num)
theorem B370669 : Blo 215810 370669 := bbase (se 3 (by rfl) ⟨69500, by rfl⟩ : syracuseStep 370669 = 139001) (by norm_num)
theorem B927733 : Blo 215810 927733 := bbase (se 5 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 927733 = 86975) (by norm_num)
theorem B469061 : Blo 215810 469061 := bbase (se 4 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 469061 = 87949) (by norm_num)
theorem B370757 : Blo 215810 370757 := bbase (se 4 (by rfl) ⟨34758, by rfl⟩ : syracuseStep 370757 = 69517) (by norm_num)
theorem B829541 : Blo 215810 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B370885 : Blo 215810 370885 := bbase (se 4 (by rfl) ⟨34770, by rfl⟩ : syracuseStep 370885 = 69541) (by norm_num)
theorem B3352853 : Blo 215810 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B698645 : Blo 215810 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B731429 : Blo 215810 731429 := bbase (se 4 (by rfl) ⟨68571, by rfl⟩ : syracuseStep 731429 = 137143) (by norm_num)
theorem B469309 : Blo 215810 469309 := bbase (se 3 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 469309 = 175991) (by norm_num)
theorem B9382229 : Blo 215810 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B731861 : Blo 215810 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B273233 : Blo 215810 273233 := bbase (se 2 (by rfl) ⟨102462, by rfl⟩ : syracuseStep 273233 = 204925) (by norm_num)
theorem B273289 : Blo 215810 273289 := bbase (se 2 (by rfl) ⟨102483, by rfl⟩ : syracuseStep 273289 = 204967) (by norm_num)
theorem B273385 : Blo 215810 273385 := bbase (se 2 (by rfl) ⟨102519, by rfl⟩ : syracuseStep 273385 = 205039) (by norm_num)
theorem B371773 : Blo 215810 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B732293 : Blo 215810 732293 := bbase (se 4 (by rfl) ⟨68652, by rfl⟩ : syracuseStep 732293 = 137305) (by norm_num)
theorem B273557 : Blo 215810 273557 := bbase (se 6 (by rfl) ⟨6411, by rfl⟩ : syracuseStep 273557 = 12823) (by norm_num)
theorem B273613 : Blo 215810 273613 := bbase (se 3 (by rfl) ⟨51302, by rfl⟩ : syracuseStep 273613 = 102605) (by norm_num)
theorem B273709 : Blo 215810 273709 := bbase (se 3 (by rfl) ⟨51320, by rfl⟩ : syracuseStep 273709 = 102641) (by norm_num)
theorem B437653 : Blo 215810 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B1093013 : Blo 215810 1093013 := bbase (se 6 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 1093013 = 51235) (by norm_num)
theorem B437717 : Blo 215810 437717 := bbase (se 7 (by rfl) ⟨5129, by rfl⟩ : syracuseStep 437717 = 10259) (by norm_num)
theorem B273881 : Blo 215810 273881 := bbase (se 2 (by rfl) ⟨102705, by rfl⟩ : syracuseStep 273881 = 205411) (by norm_num)
theorem B667109 : Blo 215810 667109 := bbase (se 4 (by rfl) ⟨62541, by rfl⟩ : syracuseStep 667109 = 125083) (by norm_num)
theorem B273937 : Blo 215810 273937 := bbase (se 2 (by rfl) ⟨102726, by rfl⟩ : syracuseStep 273937 = 205453) (by norm_num)
theorem B732725 : Blo 215810 732725 := bbase (se 5 (by rfl) ⟨34346, by rfl⟩ : syracuseStep 732725 = 68693) (by norm_num)
theorem B274033 : Blo 215810 274033 := bbase (se 2 (by rfl) ⟨102762, by rfl⟩ : syracuseStep 274033 = 205525) (by norm_num)
theorem B372485 : Blo 215810 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B274205 : Blo 215810 274205 := bbase (se 3 (by rfl) ⟨51413, by rfl⟩ : syracuseStep 274205 = 102827) (by norm_num)
theorem B274261 : Blo 215810 274261 := bbase (se 9 (by rfl) ⟨803, by rfl⟩ : syracuseStep 274261 = 1607) (by norm_num)
theorem B274357 : Blo 215810 274357 := bbase (se 5 (by rfl) ⟨12860, by rfl⟩ : syracuseStep 274357 = 25721) (by norm_num)
theorem B733157 : Blo 215810 733157 := bbase (se 4 (by rfl) ⟨68733, by rfl⟩ : syracuseStep 733157 = 137467) (by norm_num)
theorem B372773 : Blo 215810 372773 := bbase (se 4 (by rfl) ⟨34947, by rfl⟩ : syracuseStep 372773 = 69895) (by norm_num)
theorem B274529 : Blo 215810 274529 := bbase (se 2 (by rfl) ⟨102948, by rfl⟩ : syracuseStep 274529 = 205897) (by norm_num)
theorem B274585 : Blo 215810 274585 := bbase (se 2 (by rfl) ⟨102969, by rfl⟩ : syracuseStep 274585 = 205939) (by norm_num)
theorem B831653 : Blo 215810 831653 := bbase (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) (by norm_num)
theorem B307405 : Blo 215810 307405 := bbase (se 3 (by rfl) ⟨57638, by rfl⟩ : syracuseStep 307405 = 115277) (by norm_num)
theorem B274681 : Blo 215810 274681 := bbase (se 2 (by rfl) ⟨103005, by rfl⟩ : syracuseStep 274681 = 206011) (by norm_num)
theorem B733589 : Blo 215810 733589 := bbase (se 6 (by rfl) ⟨17193, by rfl⟩ : syracuseStep 733589 = 34387) (by norm_num)
theorem B274853 : Blo 215810 274853 := bbase (se 4 (by rfl) ⟨25767, by rfl⟩ : syracuseStep 274853 = 51535) (by norm_num)
theorem B831941 : Blo 215810 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B274909 : Blo 215810 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B307741 : Blo 215810 307741 := bbase (se 3 (by rfl) ⟨57701, by rfl⟩ : syracuseStep 307741 = 115403) (by norm_num)
theorem B275005 : Blo 215810 275005 := bbase (se 3 (by rfl) ⟨51563, by rfl⟩ : syracuseStep 275005 = 103127) (by norm_num)
theorem B1094309 : Blo 215810 1094309 := bbase (se 4 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 1094309 = 205183) (by norm_num)
theorem B1127141 : Blo 215810 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B275177 : Blo 215810 275177 := bbase (se 2 (by rfl) ⟨103191, by rfl⟩ : syracuseStep 275177 = 206383) (by norm_num)
theorem B307957 : Blo 215810 307957 := bbase (se 5 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 307957 = 28871) (by norm_num)
theorem B275233 : Blo 215810 275233 := bbase (se 2 (by rfl) ⟨103212, by rfl⟩ : syracuseStep 275233 = 206425) (by norm_num)
theorem B734021 : Blo 215810 734021 := bbase (se 4 (by rfl) ⟨68814, by rfl⟩ : syracuseStep 734021 = 137629) (by norm_num)
theorem B373573 : Blo 215810 373573 := bbase (se 4 (by rfl) ⟨35022, by rfl⟩ : syracuseStep 373573 = 70045) (by norm_num)
theorem B275329 : Blo 215810 275329 := bbase (se 2 (by rfl) ⟨103248, by rfl⟩ : syracuseStep 275329 = 206497) (by norm_num)
theorem B799621 : Blo 215810 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B275501 : Blo 215810 275501 := bbase (se 3 (by rfl) ⟨51656, by rfl⟩ : syracuseStep 275501 = 103313) (by norm_num)
theorem B275557 : Blo 215810 275557 := bbase (se 4 (by rfl) ⟨25833, by rfl⟩ : syracuseStep 275557 = 51667) (by norm_num)
theorem B242797 : Blo 215810 242797 := bbase (se 3 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 242797 = 91049) (by norm_num)
theorem B308333 : Blo 215810 308333 := bbase (se 3 (by rfl) ⟨57812, by rfl⟩ : syracuseStep 308333 = 115625) (by norm_num)
theorem B242833 : Blo 215810 242833 := bbase (se 2 (by rfl) ⟨91062, by rfl⟩ : syracuseStep 242833 = 182125) (by norm_num)
theorem B373909 : Blo 215810 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B242869 : Blo 215810 242869 := bbase (se 5 (by rfl) ⟨11384, by rfl⟩ : syracuseStep 242869 = 22769) (by norm_num)
theorem B1881269 : Blo 215810 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B275653 : Blo 215810 275653 := bbase (se 4 (by rfl) ⟨25842, by rfl⟩ : syracuseStep 275653 = 51685) (by norm_num)
theorem B242905 : Blo 215810 242905 := bbase (se 2 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 242905 = 182179) (by norm_num)
theorem B734453 : Blo 215810 734453 := bbase (se 5 (by rfl) ⟨34427, by rfl⟩ : syracuseStep 734453 = 68855) (by norm_num)
theorem B242941 : Blo 215810 242941 := bbase (se 3 (by rfl) ⟨45551, by rfl⟩ : syracuseStep 242941 = 91103) (by norm_num)
theorem B242977 : Blo 215810 242977 := bbase (se 2 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 242977 = 182233) (by norm_num)
theorem B243013 : Blo 215810 243013 := bbase (se 4 (by rfl) ⟨22782, by rfl⟩ : syracuseStep 243013 = 45565) (by norm_num)
theorem B243049 : Blo 215810 243049 := bbase (se 2 (by rfl) ⟨91143, by rfl⟩ : syracuseStep 243049 = 182287) (by norm_num)
theorem B275825 : Blo 215810 275825 := bbase (se 2 (by rfl) ⟨103434, by rfl⟩ : syracuseStep 275825 = 206869) (by norm_num)
theorem B243085 : Blo 215810 243085 := bbase (se 3 (by rfl) ⟨45578, by rfl⟩ : syracuseStep 243085 = 91157) (by norm_num)
theorem B275881 : Blo 215810 275881 := bbase (se 2 (by rfl) ⟨103455, by rfl⟩ : syracuseStep 275881 = 206911) (by norm_num)
theorem B243121 : Blo 215810 243121 := bbase (se 2 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 243121 = 182341) (by norm_num)
theorem B243157 : Blo 215810 243157 := bbase (se 7 (by rfl) ⟨2849, by rfl⟩ : syracuseStep 243157 = 5699) (by norm_num)
theorem B243193 : Blo 215810 243193 := bbase (se 2 (by rfl) ⟨91197, by rfl⟩ : syracuseStep 243193 = 182395) (by norm_num)
theorem B275977 : Blo 215810 275977 := bbase (se 2 (by rfl) ⟨103491, by rfl⟩ : syracuseStep 275977 = 206983) (by norm_num)
theorem B243229 : Blo 215810 243229 := bbase (se 3 (by rfl) ⟨45605, by rfl⟩ : syracuseStep 243229 = 91211) (by norm_num)
theorem B243265 : Blo 215810 243265 := bbase (se 2 (by rfl) ⟨91224, by rfl⟩ : syracuseStep 243265 = 182449) (by norm_num)
theorem B243301 : Blo 215810 243301 := bbase (se 4 (by rfl) ⟨22809, by rfl⟩ : syracuseStep 243301 = 45619) (by norm_num)
theorem B833125 : Blo 215810 833125 := bbase (se 4 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 833125 = 156211) (by norm_num)
theorem B243337 : Blo 215810 243337 := bbase (se 2 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 243337 = 182503) (by norm_num)
theorem B734885 : Blo 215810 734885 := bbase (se 4 (by rfl) ⟨68895, by rfl⟩ : syracuseStep 734885 = 137791) (by norm_num)
theorem B243373 : Blo 215810 243373 := bbase (se 3 (by rfl) ⟨45632, by rfl⟩ : syracuseStep 243373 = 91265) (by norm_num)
theorem B276149 : Blo 215810 276149 := bbase (se 5 (by rfl) ⟨12944, by rfl⟩ : syracuseStep 276149 = 25889) (by norm_num)
theorem B243409 : Blo 215810 243409 := bbase (se 2 (by rfl) ⟨91278, by rfl⟩ : syracuseStep 243409 = 182557) (by norm_num)
theorem B3192533 : Blo 215810 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B276205 : Blo 215810 276205 := bbase (se 3 (by rfl) ⟨51788, by rfl⟩ : syracuseStep 276205 = 103577) (by norm_num)
theorem B243445 : Blo 215810 243445 := bbase (se 5 (by rfl) ⟨11411, by rfl⟩ : syracuseStep 243445 = 22823) (by norm_num)
theorem B243481 : Blo 215810 243481 := bbase (se 2 (by rfl) ⟨91305, by rfl⟩ : syracuseStep 243481 = 182611) (by norm_num)
theorem B243517 : Blo 215810 243517 := bbase (se 3 (by rfl) ⟨45659, by rfl⟩ : syracuseStep 243517 = 91319) (by norm_num)
theorem B276301 : Blo 215810 276301 := bbase (se 3 (by rfl) ⟨51806, by rfl⟩ : syracuseStep 276301 = 103613) (by norm_num)
theorem B243553 : Blo 215810 243553 := bbase (se 2 (by rfl) ⟨91332, by rfl⟩ : syracuseStep 243553 = 182665) (by norm_num)
theorem B243589 : Blo 215810 243589 := bbase (se 4 (by rfl) ⟨22836, by rfl⟩ : syracuseStep 243589 = 45673) (by norm_num)
theorem B833429 : Blo 215810 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B2537365 : Blo 215810 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B243625 : Blo 215810 243625 := bbase (se 2 (by rfl) ⟨91359, by rfl⟩ : syracuseStep 243625 = 182719) (by norm_num)
theorem B1095605 : Blo 215810 1095605 := bbase (se 5 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 1095605 = 102713) (by norm_num)
theorem B243661 : Blo 215810 243661 := bbase (se 3 (by rfl) ⟨45686, by rfl⟩ : syracuseStep 243661 = 91373) (by norm_num)
theorem B702437 : Blo 215810 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B243697 : Blo 215810 243697 := bbase (se 2 (by rfl) ⟨91386, by rfl⟩ : syracuseStep 243697 = 182773) (by norm_num)
theorem B1718261 : Blo 215810 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B276473 : Blo 215810 276473 := bbase (se 2 (by rfl) ⟨103677, by rfl⟩ : syracuseStep 276473 = 207355) (by norm_num)
theorem B243733 : Blo 215810 243733 := bbase (se 6 (by rfl) ⟨5712, by rfl⟩ : syracuseStep 243733 = 11425) (by norm_num)
theorem B276529 : Blo 215810 276529 := bbase (se 2 (by rfl) ⟨103698, by rfl⟩ : syracuseStep 276529 = 207397) (by norm_num)
theorem B243769 : Blo 215810 243769 := bbase (se 2 (by rfl) ⟨91413, by rfl⟩ : syracuseStep 243769 = 182827) (by norm_num)
theorem B735317 : Blo 215810 735317 := bbase (se 8 (by rfl) ⟨4308, by rfl⟩ : syracuseStep 735317 = 8617) (by norm_num)
theorem B243805 : Blo 215810 243805 := bbase (se 3 (by rfl) ⟨45713, by rfl⟩ : syracuseStep 243805 = 91427) (by norm_num)
theorem B243841 : Blo 215810 243841 := bbase (se 2 (by rfl) ⟨91440, by rfl⟩ : syracuseStep 243841 = 182881) (by norm_num)
theorem B276625 : Blo 215810 276625 := bbase (se 2 (by rfl) ⟨103734, by rfl⟩ : syracuseStep 276625 = 207469) (by norm_num)
theorem B1652885 : Blo 215810 1652885 := bbase (se 6 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 1652885 = 77479) (by norm_num)
theorem B243877 : Blo 215810 243877 := bbase (se 4 (by rfl) ⟨22863, by rfl⟩ : syracuseStep 243877 = 45727) (by norm_num)
theorem B243913 : Blo 215810 243913 := bbase (se 2 (by rfl) ⟨91467, by rfl⟩ : syracuseStep 243913 = 182935) (by norm_num)
theorem B243949 : Blo 215810 243949 := bbase (se 3 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 243949 = 91481) (by norm_num)
theorem B243985 : Blo 215810 243985 := bbase (se 2 (by rfl) ⟨91494, by rfl⟩ : syracuseStep 243985 = 182989) (by norm_num)
theorem B1063205 : Blo 215810 1063205 := bbase (se 4 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 1063205 = 199351) (by norm_num)
theorem B244021 : Blo 215810 244021 := bbase (se 5 (by rfl) ⟨11438, by rfl⟩ : syracuseStep 244021 = 22877) (by norm_num)
theorem B899381 : Blo 215810 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B276797 : Blo 215810 276797 := bbase (se 3 (by rfl) ⟨51899, by rfl⟩ : syracuseStep 276797 = 103799) (by norm_num)
theorem B244057 : Blo 215810 244057 := bbase (se 2 (by rfl) ⟨91521, by rfl⟩ : syracuseStep 244057 = 183043) (by norm_num)
theorem B440677 : Blo 215810 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B276853 : Blo 215810 276853 := bbase (se 5 (by rfl) ⟨12977, by rfl⟩ : syracuseStep 276853 = 25955) (by norm_num)
theorem B244093 : Blo 215810 244093 := bbase (se 3 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 244093 = 91535) (by norm_num)
theorem B244129 : Blo 215810 244129 := bbase (se 2 (by rfl) ⟨91548, by rfl⟩ : syracuseStep 244129 = 183097) (by norm_num)
theorem B440749 : Blo 215810 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B244165 : Blo 215810 244165 := bbase (se 4 (by rfl) ⟨22890, by rfl⟩ : syracuseStep 244165 = 45781) (by norm_num)
theorem B276949 : Blo 215810 276949 := bbase (se 7 (by rfl) ⟨3245, by rfl⟩ : syracuseStep 276949 = 6491) (by norm_num)
theorem B244201 : Blo 215810 244201 := bbase (se 2 (by rfl) ⟨91575, by rfl⟩ : syracuseStep 244201 = 183151) (by norm_num)
theorem B309757 : Blo 215810 309757 := bbase (se 3 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 309757 = 116159) (by norm_num)
theorem B735749 : Blo 215810 735749 := bbase (se 4 (by rfl) ⟨68976, by rfl⟩ : syracuseStep 735749 = 137953) (by norm_num)
theorem B244237 : Blo 215810 244237 := bbase (se 3 (by rfl) ⟨45794, by rfl⟩ : syracuseStep 244237 = 91589) (by norm_num)
theorem B244273 : Blo 215810 244273 := bbase (se 2 (by rfl) ⟨91602, by rfl⟩ : syracuseStep 244273 = 183205) (by norm_num)
theorem B244309 : Blo 215810 244309 := bbase (se 8 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 244309 = 2863) (by norm_num)
theorem B244345 : Blo 215810 244345 := bbase (se 2 (by rfl) ⟨91629, by rfl⟩ : syracuseStep 244345 = 183259) (by norm_num)
theorem B277121 : Blo 215810 277121 := bbase (se 2 (by rfl) ⟨103920, by rfl⟩ : syracuseStep 277121 = 207841) (by norm_num)
theorem B244381 : Blo 215810 244381 := bbase (se 3 (by rfl) ⟨45821, by rfl⟩ : syracuseStep 244381 = 91643) (by norm_num)
theorem B277177 : Blo 215810 277177 := bbase (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) (by norm_num)
theorem B244417 : Blo 215810 244417 := bbase (se 2 (by rfl) ⟨91656, by rfl⟩ : syracuseStep 244417 = 183313) (by norm_num)
theorem B244453 : Blo 215810 244453 := bbase (se 4 (by rfl) ⟨22917, by rfl⟩ : syracuseStep 244453 = 45835) (by norm_num)
theorem B277229 : Blo 215810 277229 := bbase (se 3 (by rfl) ⟨51980, by rfl⟩ : syracuseStep 277229 = 103961) (by norm_num)
theorem B244489 : Blo 215810 244489 := bbase (se 2 (by rfl) ⟨91683, by rfl⟩ : syracuseStep 244489 = 183367) (by norm_num)
theorem B277273 : Blo 215810 277273 := bbase (se 2 (by rfl) ⟨103977, by rfl⟩ : syracuseStep 277273 = 207955) (by norm_num)
theorem B637733 : Blo 215810 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B244525 : Blo 215810 244525 := bbase (se 3 (by rfl) ⟨45848, by rfl⟩ : syracuseStep 244525 = 91697) (by norm_num)
theorem B244561 : Blo 215810 244561 := bbase (se 2 (by rfl) ⟨91710, by rfl⟩ : syracuseStep 244561 = 183421) (by norm_num)
theorem B441197 : Blo 215810 441197 := bbase (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) (by norm_num)
theorem B244597 : Blo 215810 244597 := bbase (se 5 (by rfl) ⟨11465, by rfl⟩ : syracuseStep 244597 = 22931) (by norm_num)
theorem B703349 : Blo 215810 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B932741 : Blo 215810 932741 := bbase (se 4 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 932741 = 174889) (by norm_num)
theorem B277393 : Blo 215810 277393 := bbase (se 2 (by rfl) ⟨104022, by rfl⟩ : syracuseStep 277393 = 208045) (by norm_num)
theorem B244633 : Blo 215810 244633 := bbase (se 2 (by rfl) ⟨91737, by rfl⟩ : syracuseStep 244633 = 183475) (by norm_num)
theorem B736181 : Blo 215810 736181 := bbase (se 5 (by rfl) ⟨34508, by rfl⟩ : syracuseStep 736181 = 69017) (by norm_num)
theorem B244669 : Blo 215810 244669 := bbase (se 3 (by rfl) ⟨45875, by rfl⟩ : syracuseStep 244669 = 91751) (by norm_num)
theorem B277445 : Blo 215810 277445 := bbase (se 4 (by rfl) ⟨26010, by rfl⟩ : syracuseStep 277445 = 52021) (by norm_num)
theorem B244705 : Blo 215810 244705 := bbase (se 2 (by rfl) ⟨91764, by rfl⟩ : syracuseStep 244705 = 183529) (by norm_num)
theorem B375797 : Blo 215810 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B277501 : Blo 215810 277501 := bbase (se 3 (by rfl) ⟨52031, by rfl⟩ : syracuseStep 277501 = 104063) (by norm_num)
theorem B244741 : Blo 215810 244741 := bbase (se 4 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 244741 = 45889) (by norm_num)
theorem B244777 : Blo 215810 244777 := bbase (se 2 (by rfl) ⟨91791, by rfl⟩ : syracuseStep 244777 = 183583) (by norm_num)
theorem B277553 : Blo 215810 277553 := bbase (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) (by norm_num)
theorem B244813 : Blo 215810 244813 := bbase (se 3 (by rfl) ⟨45902, by rfl⟩ : syracuseStep 244813 = 91805) (by norm_num)
theorem B310349 : Blo 215810 310349 := bbase (se 3 (by rfl) ⟨58190, by rfl⟩ : syracuseStep 310349 = 116381) (by norm_num)
theorem B277597 : Blo 215810 277597 := bbase (se 3 (by rfl) ⟨52049, by rfl⟩ : syracuseStep 277597 = 104099) (by norm_num)
theorem B244849 : Blo 215810 244849 := bbase (se 2 (by rfl) ⟨91818, by rfl⟩ : syracuseStep 244849 = 183637) (by norm_num)
theorem B244885 : Blo 215810 244885 := bbase (se 6 (by rfl) ⟨5739, by rfl⟩ : syracuseStep 244885 = 11479) (by norm_num)
theorem B310429 : Blo 215810 310429 := bbase (se 3 (by rfl) ⟨58205, by rfl⟩ : syracuseStep 310429 = 116411) (by norm_num)
theorem B933029 : Blo 215810 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B244921 : Blo 215810 244921 := bbase (se 2 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 244921 = 183691) (by norm_num)
theorem B1096901 : Blo 215810 1096901 := bbase (se 4 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 1096901 = 205669) (by norm_num)
theorem B244957 : Blo 215810 244957 := bbase (se 3 (by rfl) ⟨45929, by rfl⟩ : syracuseStep 244957 = 91859) (by norm_num)
theorem B244993 : Blo 215810 244993 := bbase (se 2 (by rfl) ⟨91872, by rfl⟩ : syracuseStep 244993 = 183745) (by norm_num)
theorem B277769 : Blo 215810 277769 := bbase (se 2 (by rfl) ⟨104163, by rfl⟩ : syracuseStep 277769 = 208327) (by norm_num)
theorem B310549 : Blo 215810 310549 := bbase (se 6 (by rfl) ⟨7278, by rfl⟩ : syracuseStep 310549 = 14557) (by norm_num)
theorem B245029 : Blo 215810 245029 := bbase (se 4 (by rfl) ⟨22971, by rfl⟩ : syracuseStep 245029 = 45943) (by norm_num)
theorem B507197 : Blo 215810 507197 := bbase (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) (by norm_num)
theorem B277825 : Blo 215810 277825 := bbase (se 2 (by rfl) ⟨104184, by rfl⟩ : syracuseStep 277825 = 208369) (by norm_num)
theorem B245065 : Blo 215810 245065 := bbase (se 2 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 245065 = 183799) (by norm_num)
theorem B736613 : Blo 215810 736613 := bbase (se 4 (by rfl) ⟨69057, by rfl⟩ : syracuseStep 736613 = 138115) (by norm_num)
theorem B245101 : Blo 215810 245101 := bbase (se 3 (by rfl) ⟨45956, by rfl⟩ : syracuseStep 245101 = 91913) (by norm_num)
theorem B310645 : Blo 215810 310645 := bbase (se 5 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 310645 = 29123) (by norm_num)
theorem B245137 : Blo 215810 245137 := bbase (se 2 (by rfl) ⟨91926, by rfl⟩ : syracuseStep 245137 = 183853) (by norm_num)
theorem B277921 : Blo 215810 277921 := bbase (se 2 (by rfl) ⟨104220, by rfl⟩ : syracuseStep 277921 = 208441) (by norm_num)
theorem B245173 : Blo 215810 245173 := bbase (se 5 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 245173 = 22985) (by norm_num)
theorem B245209 : Blo 215810 245209 := bbase (se 2 (by rfl) ⟨91953, by rfl⟩ : syracuseStep 245209 = 183907) (by norm_num)
theorem B245245 : Blo 215810 245245 := bbase (se 3 (by rfl) ⟨45983, by rfl⟩ : syracuseStep 245245 = 91967) (by norm_num)
theorem B900629 : Blo 215810 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B245281 : Blo 215810 245281 := bbase (se 2 (by rfl) ⟨91980, by rfl⟩ : syracuseStep 245281 = 183961) (by norm_num)
theorem B441917 : Blo 215810 441917 := bbase (se 3 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 441917 = 165719) (by norm_num)
theorem B245317 : Blo 215810 245317 := bbase (se 4 (by rfl) ⟨22998, by rfl⟩ : syracuseStep 245317 = 45997) (by norm_num)
theorem B278093 : Blo 215810 278093 := bbase (se 3 (by rfl) ⟨52142, by rfl⟩ : syracuseStep 278093 = 104285) (by norm_num)
theorem B638549 : Blo 215810 638549 := bbase (se 8 (by rfl) ⟨3741, by rfl⟩ : syracuseStep 638549 = 7483) (by norm_num)
theorem B245353 : Blo 215810 245353 := bbase (se 2 (by rfl) ⟨92007, by rfl⟩ : syracuseStep 245353 = 184015) (by norm_num)
theorem B278149 : Blo 215810 278149 := bbase (se 4 (by rfl) ⟨26076, by rfl⟩ : syracuseStep 278149 = 52153) (by norm_num)
theorem B245389 : Blo 215810 245389 := bbase (se 3 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 245389 = 92021) (by norm_num)
theorem B245425 : Blo 215810 245425 := bbase (se 2 (by rfl) ⟨92034, by rfl⟩ : syracuseStep 245425 = 184069) (by norm_num)
theorem B245461 : Blo 215810 245461 := bbase (se 7 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 245461 = 5753) (by norm_num)
theorem B245497 : Blo 215810 245497 := bbase (se 2 (by rfl) ⟨92061, by rfl⟩ : syracuseStep 245497 = 184123) (by norm_num)
theorem B737045 : Blo 215810 737045 := bbase (se 6 (by rfl) ⟨17274, by rfl⟩ : syracuseStep 737045 = 34549) (by norm_num)
theorem B245533 : Blo 215810 245533 := bbase (se 3 (by rfl) ⟨46037, by rfl⟩ : syracuseStep 245533 = 92075) (by norm_num)
theorem B245569 : Blo 215810 245569 := bbase (se 2 (by rfl) ⟨92088, by rfl⟩ : syracuseStep 245569 = 184177) (by norm_num)
theorem B245605 : Blo 215810 245605 := bbase (se 4 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 245605 = 46051) (by norm_num)
theorem B311141 : Blo 215810 311141 := bbase (se 4 (by rfl) ⟨29169, by rfl⟩ : syracuseStep 311141 = 58339) (by norm_num)
theorem B245641 : Blo 215810 245641 := bbase (se 2 (by rfl) ⟨92115, by rfl⟩ : syracuseStep 245641 = 184231) (by norm_num)
theorem B933781 : Blo 215810 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B245677 : Blo 215810 245677 := bbase (se 3 (by rfl) ⟨46064, by rfl⟩ : syracuseStep 245677 = 92129) (by norm_num)
theorem B245713 : Blo 215810 245713 := bbase (se 2 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 245713 = 184285) (by norm_num)
theorem B245749 : Blo 215810 245749 := bbase (se 5 (by rfl) ⟨11519, by rfl⟩ : syracuseStep 245749 = 23039) (by norm_num)
theorem B245785 : Blo 215810 245785 := bbase (se 2 (by rfl) ⟨92169, by rfl⟩ : syracuseStep 245785 = 184339) (by norm_num)
theorem B245821 : Blo 215810 245821 := bbase (se 3 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 245821 = 92183) (by norm_num)
theorem B245857 : Blo 215810 245857 := bbase (se 2 (by rfl) ⟨92196, by rfl⟩ : syracuseStep 245857 = 184393) (by norm_num)
theorem B245893 : Blo 215810 245893 := bbase (se 4 (by rfl) ⟨23052, by rfl⟩ : syracuseStep 245893 = 46105) (by norm_num)
theorem B245929 : Blo 215810 245929 := bbase (se 2 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 245929 = 184447) (by norm_num)
theorem B409789 : Blo 215810 409789 := bbase (se 3 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 409789 = 153671) (by norm_num)
theorem B737477 : Blo 215810 737477 := bbase (se 4 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 737477 = 138277) (by norm_num)
theorem B245965 : Blo 215810 245965 := bbase (se 3 (by rfl) ⟨46118, by rfl⟩ : syracuseStep 245965 = 92237) (by norm_num)
theorem B278749 : Blo 215810 278749 := bbase (se 3 (by rfl) ⟨52265, by rfl⟩ : syracuseStep 278749 = 104531) (by norm_num)
theorem B246001 : Blo 215810 246001 := bbase (se 2 (by rfl) ⟨92250, by rfl⟩ : syracuseStep 246001 = 184501) (by norm_num)
theorem B246037 : Blo 215810 246037 := bbase (se 6 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 246037 = 11533) (by norm_num)
theorem B278825 : Blo 215810 278825 := bbase (se 2 (by rfl) ⟨104559, by rfl⟩ : syracuseStep 278825 = 209119) (by norm_num)
theorem B475445 : Blo 215810 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B246073 : Blo 215810 246073 := bbase (se 2 (by rfl) ⟨92277, by rfl⟩ : syracuseStep 246073 = 184555) (by norm_num)
theorem B246109 : Blo 215810 246109 := bbase (se 3 (by rfl) ⟨46145, by rfl⟩ : syracuseStep 246109 = 92291) (by norm_num)
theorem B246145 : Blo 215810 246145 := bbase (se 2 (by rfl) ⟨92304, by rfl⟩ : syracuseStep 246145 = 184609) (by norm_num)
theorem B311693 : Blo 215810 311693 := bbase (se 3 (by rfl) ⟨58442, by rfl⟩ : syracuseStep 311693 = 116885) (by norm_num)
theorem B246181 : Blo 215810 246181 := bbase (se 4 (by rfl) ⟨23079, by rfl⟩ : syracuseStep 246181 = 46159) (by norm_num)
theorem B246217 : Blo 215810 246217 := bbase (se 2 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 246217 = 184663) (by norm_num)
theorem B1098197 : Blo 215810 1098197 := bbase (se 7 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 1098197 = 25739) (by norm_num)
theorem B410093 : Blo 215810 410093 := bbase (se 3 (by rfl) ⟨76892, by rfl⟩ : syracuseStep 410093 = 153785) (by norm_num)
theorem B246253 : Blo 215810 246253 := bbase (se 3 (by rfl) ⟨46172, by rfl⟩ : syracuseStep 246253 = 92345) (by norm_num)
theorem B246289 : Blo 215810 246289 := bbase (se 2 (by rfl) ⟨92358, by rfl⟩ : syracuseStep 246289 = 184717) (by norm_num)
theorem B246325 : Blo 215810 246325 := bbase (se 5 (by rfl) ⟨11546, by rfl⟩ : syracuseStep 246325 = 23093) (by norm_num)
theorem B246361 : Blo 215810 246361 := bbase (se 2 (by rfl) ⟨92385, by rfl⟩ : syracuseStep 246361 = 184771) (by norm_num)
theorem B737909 : Blo 215810 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B934517 : Blo 215810 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B246397 : Blo 215810 246397 := bbase (se 3 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 246397 = 92399) (by norm_num)
theorem B246421 : Blo 215810 246421 := bbase (se 6 (by rfl) ⟨5775, by rfl⟩ : syracuseStep 246421 = 11551) (by norm_num)
theorem B246433 : Blo 215810 246433 := bbase (se 2 (by rfl) ⟨92412, by rfl⟩ : syracuseStep 246433 = 184825) (by norm_num)
theorem B246469 : Blo 215810 246469 := bbase (se 4 (by rfl) ⟨23106, by rfl⟩ : syracuseStep 246469 = 46213) (by norm_num)
theorem B246505 : Blo 215810 246505 := bbase (se 2 (by rfl) ⟨92439, by rfl⟩ : syracuseStep 246505 = 184879) (by norm_num)
theorem B246541 : Blo 215810 246541 := bbase (se 3 (by rfl) ⟨46226, by rfl⟩ : syracuseStep 246541 = 92453) (by norm_num)
theorem B508717 : Blo 215810 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B246577 : Blo 215810 246577 := bbase (se 2 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 246577 = 184933) (by norm_num)
theorem B246613 : Blo 215810 246613 := bbase (se 9 (by rfl) ⟨722, by rfl⟩ : syracuseStep 246613 = 1445) (by norm_num)
theorem B770933 : Blo 215810 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B246649 : Blo 215810 246649 := bbase (se 2 (by rfl) ⟨92493, by rfl⟩ : syracuseStep 246649 = 184987) (by norm_num)
theorem B246685 : Blo 215810 246685 := bbase (se 3 (by rfl) ⟨46253, by rfl⟩ : syracuseStep 246685 = 92507) (by norm_num)
theorem B246721 : Blo 215810 246721 := bbase (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) (by norm_num)
theorem B246757 : Blo 215810 246757 := bbase (se 4 (by rfl) ⟨23133, by rfl⟩ : syracuseStep 246757 = 46267) (by norm_num)
theorem B246793 : Blo 215810 246793 := bbase (se 2 (by rfl) ⟨92547, by rfl⟩ : syracuseStep 246793 = 185095) (by norm_num)
theorem B738341 : Blo 215810 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B246829 : Blo 215810 246829 := bbase (se 3 (by rfl) ⟨46280, by rfl⟩ : syracuseStep 246829 = 92561) (by norm_num)
theorem B246865 : Blo 215810 246865 := bbase (se 2 (by rfl) ⟨92574, by rfl⟩ : syracuseStep 246865 = 185149) (by norm_num)
theorem B246901 : Blo 215810 246901 := bbase (se 5 (by rfl) ⟨11573, by rfl⟩ : syracuseStep 246901 = 23147) (by norm_num)
theorem B312445 : Blo 215810 312445 := bbase (se 3 (by rfl) ⟨58583, by rfl⟩ : syracuseStep 312445 = 117167) (by norm_num)
theorem B246937 : Blo 215810 246937 := bbase (se 2 (by rfl) ⟨92601, by rfl⟩ : syracuseStep 246937 = 185203) (by norm_num)
theorem B1230005 : Blo 215810 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B279733 : Blo 215810 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B246973 : Blo 215810 246973 := bbase (se 3 (by rfl) ⟨46307, by rfl⟩ : syracuseStep 246973 = 92615) (by norm_num)
theorem B410845 : Blo 215810 410845 := bbase (se 3 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 410845 = 154067) (by norm_num)
theorem B247009 : Blo 215810 247009 := bbase (se 2 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 247009 = 185257) (by norm_num)
theorem B247045 : Blo 215810 247045 := bbase (se 4 (by rfl) ⟨23160, by rfl⟩ : syracuseStep 247045 = 46321) (by norm_num)
theorem B247081 : Blo 215810 247081 := bbase (se 2 (by rfl) ⟨92655, by rfl⟩ : syracuseStep 247081 = 185311) (by norm_num)
theorem B247117 : Blo 215810 247117 := bbase (se 3 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 247117 = 92669) (by norm_num)
theorem B410989 : Blo 215810 410989 := bbase (se 3 (by rfl) ⟨77060, by rfl⟩ : syracuseStep 410989 = 154121) (by norm_num)
theorem B247153 : Blo 215810 247153 := bbase (se 2 (by rfl) ⟨92682, by rfl⟩ : syracuseStep 247153 = 185365) (by norm_num)
theorem B247189 : Blo 215810 247189 := bbase (se 6 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 247189 = 11587) (by norm_num)
theorem B247225 : Blo 215810 247225 := bbase (se 2 (by rfl) ⟨92709, by rfl⟩ : syracuseStep 247225 = 185419) (by norm_num)
theorem B738773 : Blo 215810 738773 := bbase (se 7 (by rfl) ⟨8657, by rfl⟩ : syracuseStep 738773 = 17315) (by norm_num)
theorem B247261 : Blo 215810 247261 := bbase (se 3 (by rfl) ⟨46361, by rfl⟩ : syracuseStep 247261 = 92723) (by norm_num)
theorem B247297 : Blo 215810 247297 := bbase (se 2 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 247297 = 185473) (by norm_num)
theorem B411149 : Blo 215810 411149 := bbase (se 3 (by rfl) ⟨77090, by rfl⟩ : syracuseStep 411149 = 154181) (by norm_num)
theorem B247393 : Blo 215810 247393 := bbase (se 2 (by rfl) ⟨92772, by rfl⟩ : syracuseStep 247393 = 185545) (by norm_num)
theorem B411293 : Blo 215810 411293 := bbase (se 3 (by rfl) ⟨77117, by rfl⟩ : syracuseStep 411293 = 154235) (by norm_num)
theorem B1099493 : Blo 215810 1099493 := bbase (se 4 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 1099493 = 206155) (by norm_num)
theorem B739205 : Blo 215810 739205 := bbase (se 4 (by rfl) ⟨69300, by rfl⟩ : syracuseStep 739205 = 138601) (by norm_num)
theorem B411581 : Blo 215810 411581 := bbase (se 3 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 411581 = 154343) (by norm_num)
theorem B411733 : Blo 215810 411733 := bbase (se 8 (by rfl) ⟨2412, by rfl⟩ : syracuseStep 411733 = 4825) (by norm_num)
theorem B739637 : Blo 215810 739637 := bbase (se 5 (by rfl) ⟨34670, by rfl⟩ : syracuseStep 739637 = 69341) (by norm_num)
theorem B412037 : Blo 215810 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B444901 : Blo 215810 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B248465 : Blo 215810 248465 := bbase (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) (by norm_num)
theorem B346837 : Blo 215810 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B740069 : Blo 215810 740069 := bbase (se 4 (by rfl) ⟨69381, by rfl⟩ : syracuseStep 740069 = 138763) (by norm_num)
theorem B248761 : Blo 215810 248761 := bbase (se 2 (by rfl) ⟨93285, by rfl⟩ : syracuseStep 248761 = 186571) (by norm_num)
theorem B347093 : Blo 215810 347093 := bbase (se 7 (by rfl) ⟨4067, by rfl⟩ : syracuseStep 347093 = 8135) (by norm_num)
theorem B1100789 : Blo 215810 1100789 := bbase (se 5 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 1100789 = 103199) (by norm_num)
theorem B1395701 : Blo 215810 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B2477141 : Blo 215810 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B412789 : Blo 215810 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B347285 : Blo 215810 347285 := bbase (se 6 (by rfl) ⟨8139, by rfl⟩ : syracuseStep 347285 = 16279) (by norm_num)
theorem B740501 : Blo 215810 740501 := bbase (se 6 (by rfl) ⟨17355, by rfl⟩ : syracuseStep 740501 = 34711) (by norm_num)
theorem B412933 : Blo 215810 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B413093 : Blo 215810 413093 := bbase (se 4 (by rfl) ⟨38727, by rfl⟩ : syracuseStep 413093 = 77455) (by norm_num)
theorem B413237 : Blo 215810 413237 := bbase (se 5 (by rfl) ⟨19370, by rfl⟩ : syracuseStep 413237 = 38741) (by norm_num)
theorem B740933 : Blo 215810 740933 := bbase (se 4 (by rfl) ⟨69462, by rfl⟩ : syracuseStep 740933 = 138925) (by norm_num)
theorem B2248373 : Blo 215810 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B413525 : Blo 215810 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B937813 : Blo 215810 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B413677 : Blo 215810 413677 := bbase (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) (by norm_num)
theorem B741365 : Blo 215810 741365 := bbase (se 5 (by rfl) ⟨34751, by rfl⟩ : syracuseStep 741365 = 69503) (by norm_num)
theorem B348221 : Blo 215810 348221 := bbase (se 3 (by rfl) ⟨65291, by rfl⟩ : syracuseStep 348221 = 130583) (by norm_num)
theorem B1855669 : Blo 215810 1855669 := bbase (se 5 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 1855669 = 173969) (by norm_num)
theorem B1102085 : Blo 215810 1102085 := bbase (se 4 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 1102085 = 206641) (by norm_num)
theorem B413981 : Blo 215810 413981 := bbase (se 3 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 413981 = 155243) (by norm_num)
theorem B741797 : Blo 215810 741797 := bbase (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) (by norm_num)
theorem B348605 : Blo 215810 348605 := bbase (se 3 (by rfl) ⟨65363, by rfl⟩ : syracuseStep 348605 = 130727) (by norm_num)
theorem B348733 : Blo 215810 348733 := bbase (se 3 (by rfl) ⟨65387, by rfl⟩ : syracuseStep 348733 = 130775) (by norm_num)
theorem B414733 : Blo 215810 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B414877 : Blo 215810 414877 := bbase (se 3 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 414877 = 155579) (by norm_num)
theorem B415037 : Blo 215810 415037 := bbase (se 3 (by rfl) ⟨77819, by rfl⟩ : syracuseStep 415037 = 155639) (by norm_num)
theorem B415181 : Blo 215810 415181 := bbase (se 3 (by rfl) ⟨77846, by rfl⟩ : syracuseStep 415181 = 155693) (by norm_num)
theorem B1103381 : Blo 215810 1103381 := bbase (se 6 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 1103381 = 51721) (by norm_num)
theorem B349733 : Blo 215810 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B546365 : Blo 215810 546365 := bbase (se 3 (by rfl) ⟨102443, by rfl⟩ : syracuseStep 546365 = 204887) (by norm_num)
theorem B349861 : Blo 215810 349861 := bbase (se 4 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 349861 = 65599) (by norm_num)
theorem B415469 : Blo 215810 415469 := bbase (se 3 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 415469 = 155801) (by norm_num)
theorem B1660661 : Blo 215810 1660661 := bbase (se 5 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 1660661 = 155687) (by norm_num)
theorem B415621 : Blo 215810 415621 := bbase (se 4 (by rfl) ⟨38964, by rfl⟩ : syracuseStep 415621 = 77929) (by norm_num)
theorem B546709 : Blo 215810 546709 := bbase (se 6 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 546709 = 25627) (by norm_num)
theorem B481229 : Blo 215810 481229 := bbase (se 3 (by rfl) ⟨90230, by rfl⟩ : syracuseStep 481229 = 180461) (by norm_num)
theorem B546821 : Blo 215810 546821 := bbase (se 4 (by rfl) ⟨51264, by rfl⟩ : syracuseStep 546821 = 102529) (by norm_num)
theorem B350245 : Blo 215810 350245 := bbase (se 4 (by rfl) ⟨32835, by rfl⟩ : syracuseStep 350245 = 65671) (by norm_num)
theorem B1857653 : Blo 215810 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B415925 : Blo 215810 415925 := bbase (se 5 (by rfl) ⟨19496, by rfl⟩ : syracuseStep 415925 = 38993) (by norm_num)
theorem B547013 : Blo 215810 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B350501 : Blo 215810 350501 := bbase (se 4 (by rfl) ⟨32859, by rfl⟩ : syracuseStep 350501 = 65719) (by norm_num)
theorem B1431893 : Blo 215810 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B547357 : Blo 215810 547357 := bbase (se 3 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 547357 = 205259) (by norm_num)
theorem B2087477 : Blo 215810 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B875125 : Blo 215810 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B547469 : Blo 215810 547469 := bbase (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) (by norm_num)
theorem B1104677 : Blo 215810 1104677 := bbase (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) (by norm_num)
theorem B219953 : Blo 215810 219953 := bbase (se 2 (by rfl) ⟨82482, by rfl⟩ : syracuseStep 219953 = 164965) (by norm_num)
theorem B547661 : Blo 215810 547661 := bbase (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) (by norm_num)
theorem B416677 : Blo 215810 416677 := bbase (se 4 (by rfl) ⟨39063, by rfl⟩ : syracuseStep 416677 = 78127) (by norm_num)
theorem B416821 : Blo 215810 416821 := bbase (se 5 (by rfl) ⟨19538, by rfl⟩ : syracuseStep 416821 = 39077) (by norm_num)
theorem B1039493 : Blo 215810 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B351373 : Blo 215810 351373 := bbase (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) (by norm_num)
theorem B548005 : Blo 215810 548005 := bbase (se 4 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 548005 = 102751) (by norm_num)
theorem B416981 : Blo 215810 416981 := bbase (se 7 (by rfl) ⟨4886, by rfl⟩ : syracuseStep 416981 = 9773) (by norm_num)
theorem B351469 : Blo 215810 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B548117 : Blo 215810 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B15621461 : Blo 215810 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B417125 : Blo 215810 417125 := bbase (se 4 (by rfl) ⟨39105, by rfl⟩ : syracuseStep 417125 = 78211) (by norm_num)
theorem B220537 : Blo 215810 220537 := bbase (se 2 (by rfl) ⟨82701, by rfl⟩ : syracuseStep 220537 = 165403) (by norm_num)
theorem B253309 : Blo 215810 253309 := bbase (se 3 (by rfl) ⟨47495, by rfl⟩ : syracuseStep 253309 = 94991) (by norm_num)
theorem B351629 : Blo 215810 351629 := bbase (se 3 (by rfl) ⟨65930, by rfl⟩ : syracuseStep 351629 = 131861) (by norm_num)
theorem B548309 : Blo 215810 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B1171093 : Blo 215810 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B2088629 : Blo 215810 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B548653 : Blo 215810 548653 := bbase (se 3 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 548653 = 205745) (by norm_num)
theorem B548765 : Blo 215810 548765 := bbase (se 3 (by rfl) ⟨102893, by rfl⟩ : syracuseStep 548765 = 205787) (by norm_num)
theorem B1105973 : Blo 215810 1105973 := bbase (se 5 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 1105973 = 103685) (by norm_num)
theorem B548957 : Blo 215810 548957 := bbase (se 3 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 548957 = 205859) (by norm_num)
theorem B1597589 : Blo 215810 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B680293 : Blo 215810 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B549301 : Blo 215810 549301 := bbase (se 5 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 549301 = 51497) (by norm_num)
theorem B549413 : Blo 215810 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B221869 : Blo 215810 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B549605 : Blo 215810 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B615413 : Blo 215810 615413 := bbase (se 5 (by rfl) ⟨28847, by rfl⟩ : syracuseStep 615413 = 57695) (by norm_num)
theorem B549949 : Blo 215810 549949 := bbase (se 3 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 549949 = 206231) (by norm_num)
theorem B550061 : Blo 215810 550061 := bbase (se 3 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 550061 = 206273) (by norm_num)
theorem B1107269 : Blo 215810 1107269 := bbase (se 4 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 1107269 = 207613) (by norm_num)
theorem B550253 : Blo 215810 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B222629 : Blo 215810 222629 := bbase (se 4 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 222629 = 41743) (by norm_num)
theorem B1041893 : Blo 215810 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B550597 : Blo 215810 550597 := bbase (se 4 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 550597 = 103237) (by norm_num)
theorem B550709 : Blo 215810 550709 := bbase (se 5 (by rfl) ⟨25814, by rfl⟩ : syracuseStep 550709 = 51629) (by norm_num)
theorem B550901 : Blo 215810 550901 := bbase (se 5 (by rfl) ⟨25823, by rfl⟩ : syracuseStep 550901 = 51647) (by norm_num)
theorem B845909 : Blo 215810 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B485621 : Blo 215810 485621 := bbase (se 5 (by rfl) ⟨22763, by rfl⟩ : syracuseStep 485621 = 45527) (by norm_num)
theorem B485693 : Blo 215810 485693 := bbase (se 3 (by rfl) ⟨91067, by rfl⟩ : syracuseStep 485693 = 182135) (by norm_num)
theorem B551245 : Blo 215810 551245 := bbase (se 3 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 551245 = 206717) (by norm_num)
theorem B485765 : Blo 215810 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B551357 : Blo 215810 551357 := bbase (se 3 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 551357 = 206759) (by norm_num)
theorem B485837 : Blo 215810 485837 := bbase (se 3 (by rfl) ⟨91094, by rfl⟩ : syracuseStep 485837 = 182189) (by norm_num)
theorem B485909 : Blo 215810 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B616997 : Blo 215810 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B1108565 : Blo 215810 1108565 := bbase (se 8 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 1108565 = 12991) (by norm_num)
theorem B485981 : Blo 215810 485981 := bbase (se 3 (by rfl) ⟨91121, by rfl⟩ : syracuseStep 485981 = 182243) (by norm_num)
theorem B551549 : Blo 215810 551549 := bbase (se 3 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 551549 = 206831) (by norm_num)
theorem B486053 : Blo 215810 486053 := bbase (se 4 (by rfl) ⟨45567, by rfl⟩ : syracuseStep 486053 = 91135) (by norm_num)
theorem B486125 : Blo 215810 486125 := bbase (se 3 (by rfl) ⟨91148, by rfl⟩ : syracuseStep 486125 = 182297) (by norm_num)
theorem B486197 : Blo 215810 486197 := bbase (se 5 (by rfl) ⟨22790, by rfl⟩ : syracuseStep 486197 = 45581) (by norm_num)
theorem B1239893 : Blo 215810 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B486269 : Blo 215810 486269 := bbase (se 3 (by rfl) ⟨91175, by rfl⟩ : syracuseStep 486269 = 182351) (by norm_num)
theorem B584597 : Blo 215810 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B486341 : Blo 215810 486341 := bbase (se 4 (by rfl) ⟨45594, by rfl⟩ : syracuseStep 486341 = 91189) (by norm_num)
theorem B551893 : Blo 215810 551893 := bbase (se 7 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 551893 = 12935) (by norm_num)
theorem B486413 : Blo 215810 486413 := bbase (se 3 (by rfl) ⟨91202, by rfl⟩ : syracuseStep 486413 = 182405) (by norm_num)
theorem B552005 : Blo 215810 552005 := bbase (se 4 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 552005 = 103501) (by norm_num)
theorem B486485 : Blo 215810 486485 := bbase (se 8 (by rfl) ⟨2850, by rfl⟩ : syracuseStep 486485 = 5701) (by norm_num)
theorem B486557 : Blo 215810 486557 := bbase (se 3 (by rfl) ⟨91229, by rfl⟩ : syracuseStep 486557 = 182459) (by norm_num)
theorem B617669 : Blo 215810 617669 := bbase (se 4 (by rfl) ⟨57906, by rfl⟩ : syracuseStep 617669 = 115813) (by norm_num)
theorem B486629 : Blo 215810 486629 := bbase (se 4 (by rfl) ⟨45621, by rfl⟩ : syracuseStep 486629 = 91243) (by norm_num)
theorem B552197 : Blo 215810 552197 := bbase (se 4 (by rfl) ⟨51768, by rfl⟩ : syracuseStep 552197 = 103537) (by norm_num)
theorem B945413 : Blo 215810 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B1109285 : Blo 215810 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B486701 : Blo 215810 486701 := bbase (se 3 (by rfl) ⟨91256, by rfl⟩ : syracuseStep 486701 = 182513) (by norm_num)
theorem B486773 : Blo 215810 486773 := bbase (se 5 (by rfl) ⟨22817, by rfl⟩ : syracuseStep 486773 = 45635) (by norm_num)
theorem B1011061 : Blo 215810 1011061 := bbase (se 5 (by rfl) ⟨47393, by rfl⟩ : syracuseStep 1011061 = 94787) (by norm_num)
theorem B486845 : Blo 215810 486845 := bbase (se 3 (by rfl) ⟨91283, by rfl⟩ : syracuseStep 486845 = 182567) (by norm_num)
theorem B585157 : Blo 215810 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B486917 : Blo 215810 486917 := bbase (se 4 (by rfl) ⟨45648, by rfl⟩ : syracuseStep 486917 = 91297) (by norm_num)
theorem B355909 : Blo 215810 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B486989 : Blo 215810 486989 := bbase (se 3 (by rfl) ⟨91310, by rfl⟩ : syracuseStep 486989 = 182621) (by norm_num)
theorem B552541 : Blo 215810 552541 := bbase (se 3 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 552541 = 207203) (by norm_num)
theorem B618101 : Blo 215810 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B487061 : Blo 215810 487061 := bbase (se 6 (by rfl) ⟨11415, by rfl⟩ : syracuseStep 487061 = 22831) (by norm_num)
theorem B552653 : Blo 215810 552653 := bbase (se 3 (by rfl) ⟨103622, by rfl⟩ : syracuseStep 552653 = 207245) (by norm_num)
theorem B487133 : Blo 215810 487133 := bbase (se 3 (by rfl) ⟨91337, by rfl⟩ : syracuseStep 487133 = 182675) (by norm_num)
theorem B487205 : Blo 215810 487205 := bbase (se 4 (by rfl) ⟨45675, by rfl⟩ : syracuseStep 487205 = 91351) (by norm_num)
theorem B2649941 : Blo 215810 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B1109861 : Blo 215810 1109861 := bbase (se 4 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 1109861 = 208099) (by norm_num)
theorem B487277 : Blo 215810 487277 := bbase (se 3 (by rfl) ⟨91364, by rfl⟩ : syracuseStep 487277 = 182729) (by norm_num)
theorem B552845 : Blo 215810 552845 := bbase (se 3 (by rfl) ⟨103658, by rfl⟩ : syracuseStep 552845 = 207317) (by norm_num)
theorem B487349 : Blo 215810 487349 := bbase (se 5 (by rfl) ⟨22844, by rfl⟩ : syracuseStep 487349 = 45689) (by norm_num)
theorem B1896373 : Blo 215810 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1142741 : Blo 215810 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B487421 : Blo 215810 487421 := bbase (se 3 (by rfl) ⟨91391, by rfl⟩ : syracuseStep 487421 = 182783) (by norm_num)
theorem B487493 : Blo 215810 487493 := bbase (se 4 (by rfl) ⟨45702, by rfl⟩ : syracuseStep 487493 = 91405) (by norm_num)
theorem B323717 : Blo 215810 323717 := bbase (se 4 (by rfl) ⟨30348, by rfl⟩ : syracuseStep 323717 = 60697) (by norm_num)
theorem B487565 : Blo 215810 487565 := bbase (se 3 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 487565 = 182837) (by norm_num)
theorem B323741 : Blo 215810 323741 := bbase (se 3 (by rfl) ⟨60701, by rfl⟩ : syracuseStep 323741 = 121403) (by norm_num)
theorem B323765 : Blo 215810 323765 := bbase (se 5 (by rfl) ⟨15176, by rfl⟩ : syracuseStep 323765 = 30353) (by norm_num)
theorem B323789 : Blo 215810 323789 := bbase (se 3 (by rfl) ⟨60710, by rfl⟩ : syracuseStep 323789 = 121421) (by norm_num)
theorem B487637 : Blo 215810 487637 := bbase (se 7 (by rfl) ⟨5714, by rfl⟩ : syracuseStep 487637 = 11429) (by norm_num)
theorem B323813 : Blo 215810 323813 := bbase (se 4 (by rfl) ⟨30357, by rfl⟩ : syracuseStep 323813 = 60715) (by norm_num)
theorem B553189 : Blo 215810 553189 := bbase (se 4 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 553189 = 103723) (by norm_num)
theorem B323837 : Blo 215810 323837 := bbase (se 3 (by rfl) ⟨60719, by rfl⟩ : syracuseStep 323837 = 121439) (by norm_num)
theorem B323861 : Blo 215810 323861 := bbase (se 6 (by rfl) ⟨7590, by rfl⟩ : syracuseStep 323861 = 15181) (by norm_num)
theorem B487709 : Blo 215810 487709 := bbase (se 3 (by rfl) ⟨91445, by rfl⟩ : syracuseStep 487709 = 182891) (by norm_num)
theorem B323885 : Blo 215810 323885 := bbase (se 3 (by rfl) ⟨60728, by rfl⟩ : syracuseStep 323885 = 121457) (by norm_num)
theorem B323909 : Blo 215810 323909 := bbase (se 4 (by rfl) ⟨30366, by rfl⟩ : syracuseStep 323909 = 60733) (by norm_num)
theorem B553301 : Blo 215810 553301 := bbase (se 10 (by rfl) ⟨810, by rfl⟩ : syracuseStep 553301 = 1621) (by norm_num)
theorem B323933 : Blo 215810 323933 := bbase (se 3 (by rfl) ⟨60737, by rfl⟩ : syracuseStep 323933 = 121475) (by norm_num)
theorem B487781 : Blo 215810 487781 := bbase (se 4 (by rfl) ⟨45729, by rfl⟩ : syracuseStep 487781 = 91459) (by norm_num)
theorem B618853 : Blo 215810 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B323957 : Blo 215810 323957 := bbase (se 5 (by rfl) ⟨15185, by rfl⟩ : syracuseStep 323957 = 30371) (by norm_num)
theorem B323981 : Blo 215810 323981 := bbase (se 3 (by rfl) ⟨60746, by rfl⟩ : syracuseStep 323981 = 121493) (by norm_num)
theorem B324005 : Blo 215810 324005 := bbase (se 4 (by rfl) ⟨30375, by rfl⟩ : syracuseStep 324005 = 60751) (by norm_num)
theorem B487853 : Blo 215810 487853 := bbase (se 3 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 487853 = 182945) (by norm_num)
theorem B389557 : Blo 215810 389557 := bbase (se 5 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 389557 = 36521) (by norm_num)
theorem B324029 : Blo 215810 324029 := bbase (se 3 (by rfl) ⟨60755, by rfl⟩ : syracuseStep 324029 = 121511) (by norm_num)
theorem B324053 : Blo 215810 324053 := bbase (se 7 (by rfl) ⟨3797, by rfl⟩ : syracuseStep 324053 = 7595) (by norm_num)
theorem B324077 : Blo 215810 324077 := bbase (se 3 (by rfl) ⟨60764, by rfl⟩ : syracuseStep 324077 = 121529) (by norm_num)
theorem B487925 : Blo 215810 487925 := bbase (se 5 (by rfl) ⟨22871, by rfl⟩ : syracuseStep 487925 = 45743) (by norm_num)
theorem B324101 : Blo 215810 324101 := bbase (se 4 (by rfl) ⟨30384, by rfl⟩ : syracuseStep 324101 = 60769) (by norm_num)
theorem B553493 : Blo 215810 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B324125 : Blo 215810 324125 := bbase (se 3 (by rfl) ⟨60773, by rfl⟩ : syracuseStep 324125 = 121547) (by norm_num)
theorem B324149 : Blo 215810 324149 := bbase (se 5 (by rfl) ⟨15194, by rfl⟩ : syracuseStep 324149 = 30389) (by norm_num)
theorem B487997 : Blo 215810 487997 := bbase (se 3 (by rfl) ⟨91499, by rfl⟩ : syracuseStep 487997 = 182999) (by norm_num)
theorem B389701 : Blo 215810 389701 := bbase (se 4 (by rfl) ⟨36534, by rfl⟩ : syracuseStep 389701 = 73069) (by norm_num)
theorem B324173 : Blo 215810 324173 := bbase (se 3 (by rfl) ⟨60782, by rfl⟩ : syracuseStep 324173 = 121565) (by norm_num)
theorem B324197 : Blo 215810 324197 := bbase (se 4 (by rfl) ⟨30393, by rfl⟩ : syracuseStep 324197 = 60787) (by norm_num)
theorem B324221 : Blo 215810 324221 := bbase (se 3 (by rfl) ⟨60791, by rfl⟩ : syracuseStep 324221 = 121583) (by norm_num)
theorem B488069 : Blo 215810 488069 := bbase (se 4 (by rfl) ⟨45756, by rfl⟩ : syracuseStep 488069 = 91513) (by norm_num)
theorem B324245 : Blo 215810 324245 := bbase (se 6 (by rfl) ⟨7599, by rfl⟩ : syracuseStep 324245 = 15199) (by norm_num)
theorem B324269 : Blo 215810 324269 := bbase (se 3 (by rfl) ⟨60800, by rfl⟩ : syracuseStep 324269 = 121601) (by norm_num)
theorem B324293 : Blo 215810 324293 := bbase (se 4 (by rfl) ⟨30402, by rfl⟩ : syracuseStep 324293 = 60805) (by norm_num)
theorem B488141 : Blo 215810 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B324317 : Blo 215810 324317 := bbase (se 3 (by rfl) ⟨60809, by rfl⟩ : syracuseStep 324317 = 121619) (by norm_num)
theorem B324341 : Blo 215810 324341 := bbase (se 5 (by rfl) ⟨15203, by rfl⟩ : syracuseStep 324341 = 30407) (by norm_num)
theorem B324365 : Blo 215810 324365 := bbase (se 3 (by rfl) ⟨60818, by rfl⟩ : syracuseStep 324365 = 121637) (by norm_num)
theorem B488213 : Blo 215810 488213 := bbase (se 6 (by rfl) ⟨11442, by rfl⟩ : syracuseStep 488213 = 22885) (by norm_num)
theorem B324389 : Blo 215810 324389 := bbase (se 4 (by rfl) ⟨30411, by rfl⟩ : syracuseStep 324389 = 60823) (by norm_num)
theorem B750389 : Blo 215810 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B324413 : Blo 215810 324413 := bbase (se 3 (by rfl) ⟨60827, by rfl⟩ : syracuseStep 324413 = 121655) (by norm_num)
theorem B586565 : Blo 215810 586565 := bbase (se 4 (by rfl) ⟨54990, by rfl⟩ : syracuseStep 586565 = 109981) (by norm_num)
theorem B324437 : Blo 215810 324437 := bbase (se 9 (by rfl) ⟨950, by rfl⟩ : syracuseStep 324437 = 1901) (by norm_num)
theorem B488285 : Blo 215810 488285 := bbase (se 3 (by rfl) ⟨91553, by rfl⟩ : syracuseStep 488285 = 183107) (by norm_num)
theorem B324461 : Blo 215810 324461 := bbase (se 3 (by rfl) ⟨60836, by rfl⟩ : syracuseStep 324461 = 121673) (by norm_num)
theorem B553837 : Blo 215810 553837 := bbase (se 3 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 553837 = 207689) (by norm_num)
theorem B324485 : Blo 215810 324485 := bbase (se 4 (by rfl) ⟨30420, by rfl⟩ : syracuseStep 324485 = 60841) (by norm_num)
theorem B324509 : Blo 215810 324509 := bbase (se 3 (by rfl) ⟨60845, by rfl⟩ : syracuseStep 324509 = 121691) (by norm_num)
theorem B488357 : Blo 215810 488357 := bbase (se 4 (by rfl) ⟨45783, by rfl⟩ : syracuseStep 488357 = 91567) (by norm_num)
theorem B291757 : Blo 215810 291757 := bbase (se 3 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 291757 = 109409) (by norm_num)
theorem B324533 : Blo 215810 324533 := bbase (se 5 (by rfl) ⟨15212, by rfl⟩ : syracuseStep 324533 = 30425) (by norm_num)
theorem B324557 : Blo 215810 324557 := bbase (se 3 (by rfl) ⟨60854, by rfl⟩ : syracuseStep 324557 = 121709) (by norm_num)
theorem B553949 : Blo 215810 553949 := bbase (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) (by norm_num)
theorem B324581 : Blo 215810 324581 := bbase (se 4 (by rfl) ⟨30429, by rfl⟩ : syracuseStep 324581 = 60859) (by norm_num)
theorem B488429 : Blo 215810 488429 := bbase (se 3 (by rfl) ⟨91580, by rfl⟩ : syracuseStep 488429 = 183161) (by norm_num)
theorem B324605 : Blo 215810 324605 := bbase (se 3 (by rfl) ⟨60863, by rfl⟩ : syracuseStep 324605 = 121727) (by norm_num)
theorem B324629 : Blo 215810 324629 := bbase (se 6 (by rfl) ⟨7608, by rfl⟩ : syracuseStep 324629 = 15217) (by norm_num)
theorem B324653 : Blo 215810 324653 := bbase (se 3 (by rfl) ⟨60872, by rfl⟩ : syracuseStep 324653 = 121745) (by norm_num)
theorem B488501 : Blo 215810 488501 := bbase (se 5 (by rfl) ⟨22898, by rfl⟩ : syracuseStep 488501 = 45797) (by norm_num)
theorem B324677 : Blo 215810 324677 := bbase (se 4 (by rfl) ⟨30438, by rfl⟩ : syracuseStep 324677 = 60877) (by norm_num)
theorem B947285 : Blo 215810 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B324701 : Blo 215810 324701 := bbase (se 3 (by rfl) ⟨60881, by rfl⟩ : syracuseStep 324701 = 121763) (by norm_num)
theorem B324725 : Blo 215810 324725 := bbase (se 5 (by rfl) ⟨15221, by rfl⟩ : syracuseStep 324725 = 30443) (by norm_num)
theorem B1111157 : Blo 215810 1111157 := bbase (se 5 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 1111157 = 104171) (by norm_num)
theorem B488573 : Blo 215810 488573 := bbase (se 3 (by rfl) ⟨91607, by rfl⟩ : syracuseStep 488573 = 183215) (by norm_num)
theorem B390277 : Blo 215810 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B324749 : Blo 215810 324749 := bbase (se 3 (by rfl) ⟨60890, by rfl⟩ : syracuseStep 324749 = 121781) (by norm_num)
theorem B554141 : Blo 215810 554141 := bbase (se 3 (by rfl) ⟨103901, by rfl⟩ : syracuseStep 554141 = 207803) (by norm_num)
theorem B324773 : Blo 215810 324773 := bbase (se 4 (by rfl) ⟨30447, by rfl⟩ : syracuseStep 324773 = 60895) (by norm_num)
theorem B324797 : Blo 215810 324797 := bbase (se 3 (by rfl) ⟨60899, by rfl⟩ : syracuseStep 324797 = 121799) (by norm_num)
theorem B488645 : Blo 215810 488645 := bbase (se 4 (by rfl) ⟨45810, by rfl⟩ : syracuseStep 488645 = 91621) (by norm_num)
theorem B324821 : Blo 215810 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B259301 : Blo 215810 259301 := bbase (se 4 (by rfl) ⟨24309, by rfl⟩ : syracuseStep 259301 = 48619) (by norm_num)
theorem B324845 : Blo 215810 324845 := bbase (se 3 (by rfl) ⟨60908, by rfl⟩ : syracuseStep 324845 = 121817) (by norm_num)
theorem B586997 : Blo 215810 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B324869 : Blo 215810 324869 := bbase (se 4 (by rfl) ⟨30456, by rfl⟩ : syracuseStep 324869 = 60913) (by norm_num)
theorem B488717 : Blo 215810 488717 := bbase (se 3 (by rfl) ⟨91634, by rfl⟩ : syracuseStep 488717 = 183269) (by norm_num)
theorem B324893 : Blo 215810 324893 := bbase (se 3 (by rfl) ⟨60917, by rfl⟩ : syracuseStep 324893 = 121835) (by norm_num)
theorem B324917 : Blo 215810 324917 := bbase (se 5 (by rfl) ⟨15230, by rfl⟩ : syracuseStep 324917 = 30461) (by norm_num)
theorem B324941 : Blo 215810 324941 := bbase (se 3 (by rfl) ⟨60926, by rfl⟩ : syracuseStep 324941 = 121853) (by norm_num)
theorem B488789 : Blo 215810 488789 := bbase (se 13 (by rfl) ⟨89, by rfl⟩ : syracuseStep 488789 = 179) (by norm_num)
theorem B1668437 : Blo 215810 1668437 := bbase (se 13 (by rfl) ⟨305, by rfl⟩ : syracuseStep 1668437 = 611) (by norm_num)
theorem B324965 : Blo 215810 324965 := bbase (se 4 (by rfl) ⟨30465, by rfl⟩ : syracuseStep 324965 = 60931) (by norm_num)
theorem B324989 : Blo 215810 324989 := bbase (se 3 (by rfl) ⟨60935, by rfl⟩ : syracuseStep 324989 = 121871) (by norm_num)
theorem B259465 : Blo 215810 259465 := bbase (se 2 (by rfl) ⟨97299, by rfl⟩ : syracuseStep 259465 = 194599) (by norm_num)
theorem B325013 : Blo 215810 325013 := bbase (se 6 (by rfl) ⟨7617, by rfl⟩ : syracuseStep 325013 = 15235) (by norm_num)
theorem B488861 : Blo 215810 488861 := bbase (se 3 (by rfl) ⟨91661, by rfl⟩ : syracuseStep 488861 = 183323) (by norm_num)
theorem B325037 : Blo 215810 325037 := bbase (se 3 (by rfl) ⟨60944, by rfl⟩ : syracuseStep 325037 = 121889) (by norm_num)
theorem B325061 : Blo 215810 325061 := bbase (se 4 (by rfl) ⟨30474, by rfl⟩ : syracuseStep 325061 = 60949) (by norm_num)
theorem B521677 : Blo 215810 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B325085 : Blo 215810 325085 := bbase (se 3 (by rfl) ⟨60953, by rfl⟩ : syracuseStep 325085 = 121907) (by norm_num)
theorem B488933 : Blo 215810 488933 := bbase (se 4 (by rfl) ⟨45837, by rfl⟩ : syracuseStep 488933 = 91675) (by norm_num)
theorem B325109 : Blo 215810 325109 := bbase (se 5 (by rfl) ⟨15239, by rfl⟩ : syracuseStep 325109 = 30479) (by norm_num)
theorem B554485 : Blo 215810 554485 := bbase (se 5 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 554485 = 51983) (by norm_num)
theorem B882181 : Blo 215810 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B325133 : Blo 215810 325133 := bbase (se 3 (by rfl) ⟨60962, by rfl⟩ : syracuseStep 325133 = 121925) (by norm_num)
theorem B751141 : Blo 215810 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B325157 : Blo 215810 325157 := bbase (se 4 (by rfl) ⟨30483, by rfl⟩ : syracuseStep 325157 = 60967) (by norm_num)
theorem B489005 : Blo 215810 489005 := bbase (se 3 (by rfl) ⟨91688, by rfl⟩ : syracuseStep 489005 = 183377) (by norm_num)
theorem B325181 : Blo 215810 325181 := bbase (se 3 (by rfl) ⟨60971, by rfl⟩ : syracuseStep 325181 = 121943) (by norm_num)
theorem B325205 : Blo 215810 325205 := bbase (se 8 (by rfl) ⟨1905, by rfl⟩ : syracuseStep 325205 = 3811) (by norm_num)
theorem B259681 : Blo 215810 259681 := bbase (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) (by norm_num)
theorem B554597 : Blo 215810 554597 := bbase (se 4 (by rfl) ⟨51993, by rfl⟩ : syracuseStep 554597 = 103987) (by norm_num)
theorem B325229 : Blo 215810 325229 := bbase (se 3 (by rfl) ⟨60980, by rfl⟩ : syracuseStep 325229 = 121961) (by norm_num)
theorem B489077 : Blo 215810 489077 := bbase (se 5 (by rfl) ⟨22925, by rfl⟩ : syracuseStep 489077 = 45851) (by norm_num)
theorem B325253 : Blo 215810 325253 := bbase (se 4 (by rfl) ⟨30492, by rfl⟩ : syracuseStep 325253 = 60985) (by norm_num)
theorem B325277 : Blo 215810 325277 := bbase (se 3 (by rfl) ⟨60989, by rfl⟩ : syracuseStep 325277 = 121979) (by norm_num)
theorem B325301 : Blo 215810 325301 := bbase (se 5 (by rfl) ⟨15248, by rfl⟩ : syracuseStep 325301 = 30497) (by norm_num)
theorem B489149 : Blo 215810 489149 := bbase (se 3 (by rfl) ⟨91715, by rfl⟩ : syracuseStep 489149 = 183431) (by norm_num)
theorem B325325 : Blo 215810 325325 := bbase (se 3 (by rfl) ⟨60998, by rfl⟩ : syracuseStep 325325 = 121997) (by norm_num)
theorem B325349 : Blo 215810 325349 := bbase (se 4 (by rfl) ⟨30501, by rfl⟩ : syracuseStep 325349 = 61003) (by norm_num)
theorem B325373 : Blo 215810 325373 := bbase (se 3 (by rfl) ⟨61007, by rfl⟩ : syracuseStep 325373 = 122015) (by norm_num)
theorem B489221 : Blo 215810 489221 := bbase (se 4 (by rfl) ⟨45864, by rfl⟩ : syracuseStep 489221 = 91729) (by norm_num)
theorem B259849 : Blo 215810 259849 := bbase (se 2 (by rfl) ⟨97443, by rfl⟩ : syracuseStep 259849 = 194887) (by norm_num)
theorem B325397 : Blo 215810 325397 := bbase (se 6 (by rfl) ⟨7626, by rfl⟩ : syracuseStep 325397 = 15253) (by norm_num)
theorem B554789 : Blo 215810 554789 := bbase (se 4 (by rfl) ⟨52011, by rfl⟩ : syracuseStep 554789 = 104023) (by norm_num)
theorem B325421 : Blo 215810 325421 := bbase (se 3 (by rfl) ⟨61016, by rfl⟩ : syracuseStep 325421 = 122033) (by norm_num)
theorem B325445 : Blo 215810 325445 := bbase (se 4 (by rfl) ⟨30510, by rfl⟩ : syracuseStep 325445 = 61021) (by norm_num)
theorem B489293 : Blo 215810 489293 := bbase (se 3 (by rfl) ⟨91742, by rfl⟩ : syracuseStep 489293 = 183485) (by norm_num)
theorem B5699413 : Blo 215810 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B325469 : Blo 215810 325469 := bbase (se 3 (by rfl) ⟨61025, by rfl⟩ : syracuseStep 325469 = 122051) (by norm_num)
theorem B325493 : Blo 215810 325493 := bbase (se 5 (by rfl) ⟨15257, by rfl⟩ : syracuseStep 325493 = 30515) (by norm_num)
theorem B522101 : Blo 215810 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B325517 : Blo 215810 325517 := bbase (se 3 (by rfl) ⟨61034, by rfl⟩ : syracuseStep 325517 = 122069) (by norm_num)
theorem B489365 : Blo 215810 489365 := bbase (se 6 (by rfl) ⟨11469, by rfl⟩ : syracuseStep 489365 = 22939) (by norm_num)
theorem B325541 : Blo 215810 325541 := bbase (se 4 (by rfl) ⟨30519, by rfl⟩ : syracuseStep 325541 = 61039) (by norm_num)
theorem B391085 : Blo 215810 391085 := bbase (se 3 (by rfl) ⟨73328, by rfl⟩ : syracuseStep 391085 = 146657) (by norm_num)
theorem B325565 : Blo 215810 325565 := bbase (se 3 (by rfl) ⟨61043, by rfl⟩ : syracuseStep 325565 = 122087) (by norm_num)
theorem B325589 : Blo 215810 325589 := bbase (se 7 (by rfl) ⟨3815, by rfl⟩ : syracuseStep 325589 = 7631) (by norm_num)
theorem B489437 : Blo 215810 489437 := bbase (se 3 (by rfl) ⟨91769, by rfl⟩ : syracuseStep 489437 = 183539) (by norm_num)
theorem B325613 : Blo 215810 325613 := bbase (se 3 (by rfl) ⟨61052, by rfl⟩ : syracuseStep 325613 = 122105) (by norm_num)
theorem B325637 : Blo 215810 325637 := bbase (se 4 (by rfl) ⟨30528, by rfl⟩ : syracuseStep 325637 = 61057) (by norm_num)
theorem B325661 : Blo 215810 325661 := bbase (se 3 (by rfl) ⟨61061, by rfl⟩ : syracuseStep 325661 = 122123) (by norm_num)
theorem B489509 : Blo 215810 489509 := bbase (se 4 (by rfl) ⟨45891, by rfl⟩ : syracuseStep 489509 = 91783) (by norm_num)
theorem B325685 : Blo 215810 325685 := bbase (se 5 (by rfl) ⟨15266, by rfl⟩ : syracuseStep 325685 = 30533) (by norm_num)
theorem B325709 : Blo 215810 325709 := bbase (se 3 (by rfl) ⟨61070, by rfl⟩ : syracuseStep 325709 = 122141) (by norm_num)
theorem B325733 : Blo 215810 325733 := bbase (se 4 (by rfl) ⟨30537, by rfl⟩ : syracuseStep 325733 = 61075) (by norm_num)
theorem B489581 : Blo 215810 489581 := bbase (se 3 (by rfl) ⟨91796, by rfl⟩ : syracuseStep 489581 = 183593) (by norm_num)
theorem B325757 : Blo 215810 325757 := bbase (se 3 (by rfl) ⟨61079, by rfl⟩ : syracuseStep 325757 = 122159) (by norm_num)
theorem B555133 : Blo 215810 555133 := bbase (se 3 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 555133 = 208175) (by norm_num)
theorem B325781 : Blo 215810 325781 := bbase (se 6 (by rfl) ⟨7635, by rfl⟩ : syracuseStep 325781 = 15271) (by norm_num)
theorem B522389 : Blo 215810 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B325805 : Blo 215810 325805 := bbase (se 3 (by rfl) ⟨61088, by rfl⟩ : syracuseStep 325805 = 122177) (by norm_num)
theorem B489653 : Blo 215810 489653 := bbase (se 5 (by rfl) ⟨22952, by rfl⟩ : syracuseStep 489653 = 45905) (by norm_num)
theorem B325829 : Blo 215810 325829 := bbase (se 4 (by rfl) ⟨30546, by rfl⟩ : syracuseStep 325829 = 61093) (by norm_num)
theorem B325853 : Blo 215810 325853 := bbase (se 3 (by rfl) ⟨61097, by rfl⟩ : syracuseStep 325853 = 122195) (by norm_num)
theorem B555245 : Blo 215810 555245 := bbase (se 3 (by rfl) ⟨104108, by rfl⟩ : syracuseStep 555245 = 208217) (by norm_num)
theorem B325877 : Blo 215810 325877 := bbase (se 5 (by rfl) ⟨15275, by rfl⟩ : syracuseStep 325877 = 30551) (by norm_num)
theorem B489725 : Blo 215810 489725 := bbase (se 3 (by rfl) ⟨91823, by rfl⟩ : syracuseStep 489725 = 183647) (by norm_num)
theorem B325901 : Blo 215810 325901 := bbase (se 3 (by rfl) ⟨61106, by rfl⟩ : syracuseStep 325901 = 122213) (by norm_num)
theorem B260377 : Blo 215810 260377 := bbase (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) (by norm_num)
theorem B325925 : Blo 215810 325925 := bbase (se 4 (by rfl) ⟨30555, by rfl⟩ : syracuseStep 325925 = 61111) (by norm_num)
theorem B325949 : Blo 215810 325949 := bbase (se 3 (by rfl) ⟨61115, by rfl⟩ : syracuseStep 325949 = 122231) (by norm_num)
theorem B489797 : Blo 215810 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B325973 : Blo 215810 325973 := bbase (se 10 (by rfl) ⟨477, by rfl⟩ : syracuseStep 325973 = 955) (by norm_num)
theorem B325997 : Blo 215810 325997 := bbase (se 3 (by rfl) ⟨61124, by rfl⟩ : syracuseStep 325997 = 122249) (by norm_num)
theorem B326021 : Blo 215810 326021 := bbase (se 4 (by rfl) ⟨30564, by rfl⟩ : syracuseStep 326021 = 61129) (by norm_num)
theorem B1112453 : Blo 215810 1112453 := bbase (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) (by norm_num)
theorem B489869 : Blo 215810 489869 := bbase (se 3 (by rfl) ⟨91850, by rfl⟩ : syracuseStep 489869 = 183701) (by norm_num)
theorem B326045 : Blo 215810 326045 := bbase (se 3 (by rfl) ⟨61133, by rfl⟩ : syracuseStep 326045 = 122267) (by norm_num)
theorem B555437 : Blo 215810 555437 := bbase (se 3 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 555437 = 208289) (by norm_num)
theorem B326069 : Blo 215810 326069 := bbase (se 5 (by rfl) ⟨15284, by rfl⟩ : syracuseStep 326069 = 30569) (by norm_num)
theorem B326093 : Blo 215810 326093 := bbase (se 3 (by rfl) ⟨61142, by rfl⟩ : syracuseStep 326093 = 122285) (by norm_num)
theorem B489941 : Blo 215810 489941 := bbase (se 7 (by rfl) ⟨5741, by rfl⟩ : syracuseStep 489941 = 11483) (by norm_num)
theorem B784853 : Blo 215810 784853 := bbase (se 7 (by rfl) ⟨9197, by rfl⟩ : syracuseStep 784853 = 18395) (by norm_num)
theorem B326117 : Blo 215810 326117 := bbase (se 4 (by rfl) ⟨30573, by rfl⟩ : syracuseStep 326117 = 61147) (by norm_num)
theorem B326141 : Blo 215810 326141 := bbase (se 3 (by rfl) ⟨61151, by rfl⟩ : syracuseStep 326141 = 122303) (by norm_num)
theorem B424453 : Blo 215810 424453 := bbase (se 4 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 424453 = 79585) (by norm_num)
theorem B326165 : Blo 215810 326165 := bbase (se 6 (by rfl) ⟨7644, by rfl⟩ : syracuseStep 326165 = 15289) (by norm_num)
theorem B490013 : Blo 215810 490013 := bbase (se 3 (by rfl) ⟨91877, by rfl⟩ : syracuseStep 490013 = 183755) (by norm_num)
theorem B326189 : Blo 215810 326189 := bbase (se 3 (by rfl) ⟨61160, by rfl⟩ : syracuseStep 326189 = 122321) (by norm_num)
theorem B326213 : Blo 215810 326213 := bbase (se 4 (by rfl) ⟨30582, by rfl⟩ : syracuseStep 326213 = 61165) (by norm_num)
theorem B326237 : Blo 215810 326237 := bbase (se 3 (by rfl) ⟨61169, by rfl⟩ : syracuseStep 326237 = 122339) (by norm_num)
theorem B784997 : Blo 215810 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B490085 : Blo 215810 490085 := bbase (se 4 (by rfl) ⟨45945, by rfl⟩ : syracuseStep 490085 = 91891) (by norm_num)
theorem B326261 : Blo 215810 326261 := bbase (se 5 (by rfl) ⟨15293, by rfl⟩ : syracuseStep 326261 = 30587) (by norm_num)
theorem B326285 : Blo 215810 326285 := bbase (se 3 (by rfl) ⟨61178, by rfl⟩ : syracuseStep 326285 = 122357) (by norm_num)
theorem B326309 : Blo 215810 326309 := bbase (se 4 (by rfl) ⟨30591, by rfl⟩ : syracuseStep 326309 = 61183) (by norm_num)
theorem B490157 : Blo 215810 490157 := bbase (se 3 (by rfl) ⟨91904, by rfl⟩ : syracuseStep 490157 = 183809) (by norm_num)
theorem B326333 : Blo 215810 326333 := bbase (se 3 (by rfl) ⟨61187, by rfl⟩ : syracuseStep 326333 = 122375) (by norm_num)
theorem B326357 : Blo 215810 326357 := bbase (se 7 (by rfl) ⟨3824, by rfl⟩ : syracuseStep 326357 = 7649) (by norm_num)
theorem B326381 : Blo 215810 326381 := bbase (se 3 (by rfl) ⟨61196, by rfl⟩ : syracuseStep 326381 = 122393) (by norm_num)
theorem B490229 : Blo 215810 490229 := bbase (se 5 (by rfl) ⟨22979, by rfl⟩ : syracuseStep 490229 = 45959) (by norm_num)
theorem B326405 : Blo 215810 326405 := bbase (se 4 (by rfl) ⟨30600, by rfl⟩ : syracuseStep 326405 = 61201) (by norm_num)
theorem B555781 : Blo 215810 555781 := bbase (se 4 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 555781 = 104209) (by norm_num)
theorem B326429 : Blo 215810 326429 := bbase (se 3 (by rfl) ⟨61205, by rfl⟩ : syracuseStep 326429 = 122411) (by norm_num)
theorem B326453 : Blo 215810 326453 := bbase (se 5 (by rfl) ⟨15302, by rfl⟩ : syracuseStep 326453 = 30605) (by norm_num)
theorem B490301 : Blo 215810 490301 := bbase (se 3 (by rfl) ⟨91931, by rfl⟩ : syracuseStep 490301 = 183863) (by norm_num)
theorem B326477 : Blo 215810 326477 := bbase (se 3 (by rfl) ⟨61214, by rfl⟩ : syracuseStep 326477 = 122429) (by norm_num)
theorem B326501 : Blo 215810 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B555893 : Blo 215810 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B326525 : Blo 215810 326525 := bbase (se 3 (by rfl) ⟨61223, by rfl⟩ : syracuseStep 326525 = 122447) (by norm_num)
theorem B785285 : Blo 215810 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B490373 : Blo 215810 490373 := bbase (se 4 (by rfl) ⟨45972, by rfl⟩ : syracuseStep 490373 = 91945) (by norm_num)
theorem B326549 : Blo 215810 326549 := bbase (se 6 (by rfl) ⟨7653, by rfl⟩ : syracuseStep 326549 = 15307) (by norm_num)
theorem B326573 : Blo 215810 326573 := bbase (se 3 (by rfl) ⟨61232, by rfl⟩ : syracuseStep 326573 = 122465) (by norm_num)
theorem B326597 : Blo 215810 326597 := bbase (se 4 (by rfl) ⟨30618, by rfl⟩ : syracuseStep 326597 = 61237) (by norm_num)
theorem B490445 : Blo 215810 490445 := bbase (se 3 (by rfl) ⟨91958, by rfl⟩ : syracuseStep 490445 = 183917) (by norm_num)
theorem B326621 : Blo 215810 326621 := bbase (se 3 (by rfl) ⟨61241, by rfl⟩ : syracuseStep 326621 = 122483) (by norm_num)
theorem B326645 : Blo 215810 326645 := bbase (se 5 (by rfl) ⟨15311, by rfl⟩ : syracuseStep 326645 = 30623) (by norm_num)
theorem B326669 : Blo 215810 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B490517 : Blo 215810 490517 := bbase (se 6 (by rfl) ⟨11496, by rfl⟩ : syracuseStep 490517 = 22993) (by norm_num)
theorem B326693 : Blo 215810 326693 := bbase (se 4 (by rfl) ⟨30627, by rfl⟩ : syracuseStep 326693 = 61255) (by norm_num)
theorem B556085 : Blo 215810 556085 := bbase (se 5 (by rfl) ⟨26066, by rfl⟩ : syracuseStep 556085 = 52133) (by norm_num)
theorem B326717 : Blo 215810 326717 := bbase (se 3 (by rfl) ⟨61259, by rfl⟩ : syracuseStep 326717 = 122519) (by norm_num)
theorem B326741 : Blo 215810 326741 := bbase (se 8 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 326741 = 3829) (by norm_num)
theorem B490589 : Blo 215810 490589 := bbase (se 3 (by rfl) ⟨91985, by rfl⟩ : syracuseStep 490589 = 183971) (by norm_num)
theorem B326765 : Blo 215810 326765 := bbase (se 3 (by rfl) ⟨61268, by rfl⟩ : syracuseStep 326765 = 122537) (by norm_num)
theorem B326789 : Blo 215810 326789 := bbase (se 4 (by rfl) ⟨30636, by rfl⟩ : syracuseStep 326789 = 61273) (by norm_num)
theorem B621701 : Blo 215810 621701 := bbase (se 4 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 621701 = 116569) (by norm_num)
theorem B326813 : Blo 215810 326813 := bbase (se 3 (by rfl) ⟨61277, by rfl⟩ : syracuseStep 326813 = 122555) (by norm_num)
theorem B490661 : Blo 215810 490661 := bbase (se 4 (by rfl) ⟨45999, by rfl⟩ : syracuseStep 490661 = 91999) (by norm_num)
theorem B326837 : Blo 215810 326837 := bbase (se 5 (by rfl) ⟨15320, by rfl⟩ : syracuseStep 326837 = 30641) (by norm_num)
theorem B326861 : Blo 215810 326861 := bbase (se 3 (by rfl) ⟨61286, by rfl⟩ : syracuseStep 326861 = 122573) (by norm_num)
theorem B326885 : Blo 215810 326885 := bbase (se 4 (by rfl) ⟨30645, by rfl⟩ : syracuseStep 326885 = 61291) (by norm_num)
theorem B490733 : Blo 215810 490733 := bbase (se 3 (by rfl) ⟨92012, by rfl⟩ : syracuseStep 490733 = 184025) (by norm_num)
theorem B326909 : Blo 215810 326909 := bbase (se 3 (by rfl) ⟨61295, by rfl⟩ : syracuseStep 326909 = 122591) (by norm_num)
theorem B326933 : Blo 215810 326933 := bbase (se 6 (by rfl) ⟨7662, by rfl⟩ : syracuseStep 326933 = 15325) (by norm_num)
theorem B326957 : Blo 215810 326957 := bbase (se 3 (by rfl) ⟨61304, by rfl⟩ : syracuseStep 326957 = 122609) (by norm_num)
theorem B490805 : Blo 215810 490805 := bbase (se 5 (by rfl) ⟨23006, by rfl⟩ : syracuseStep 490805 = 46013) (by norm_num)
theorem B326981 : Blo 215810 326981 := bbase (se 4 (by rfl) ⟨30654, by rfl⟩ : syracuseStep 326981 = 61309) (by norm_num)
theorem B327005 : Blo 215810 327005 := bbase (se 3 (by rfl) ⟨61313, by rfl⟩ : syracuseStep 327005 = 122627) (by norm_num)
theorem B261473 : Blo 215810 261473 := bbase (se 2 (by rfl) ⟨98052, by rfl⟩ : syracuseStep 261473 = 196105) (by norm_num)
theorem B327029 : Blo 215810 327029 := bbase (se 5 (by rfl) ⟨15329, by rfl⟩ : syracuseStep 327029 = 30659) (by norm_num)
theorem B490877 : Blo 215810 490877 := bbase (se 3 (by rfl) ⟨92039, by rfl⟩ : syracuseStep 490877 = 184079) (by norm_num)
theorem B327053 : Blo 215810 327053 := bbase (se 3 (by rfl) ⟨61322, by rfl⟩ : syracuseStep 327053 = 122645) (by norm_num)
theorem B327077 : Blo 215810 327077 := bbase (se 4 (by rfl) ⟨30663, by rfl⟩ : syracuseStep 327077 = 61327) (by norm_num)
theorem B327101 : Blo 215810 327101 := bbase (se 3 (by rfl) ⟨61331, by rfl⟩ : syracuseStep 327101 = 122663) (by norm_num)
theorem B490949 : Blo 215810 490949 := bbase (se 4 (by rfl) ⟨46026, by rfl⟩ : syracuseStep 490949 = 92053) (by norm_num)
theorem B327125 : Blo 215810 327125 := bbase (se 7 (by rfl) ⟨3833, by rfl⟩ : syracuseStep 327125 = 7667) (by norm_num)
theorem B327149 : Blo 215810 327149 := bbase (se 3 (by rfl) ⟨61340, by rfl⟩ : syracuseStep 327149 = 122681) (by norm_num)
theorem B327173 : Blo 215810 327173 := bbase (se 4 (by rfl) ⟨30672, by rfl⟩ : syracuseStep 327173 = 61345) (by norm_num)
theorem B491021 : Blo 215810 491021 := bbase (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) (by norm_num)
theorem B327197 : Blo 215810 327197 := bbase (se 3 (by rfl) ⟨61349, by rfl⟩ : syracuseStep 327197 = 122699) (by norm_num)
theorem B327221 : Blo 215810 327221 := bbase (se 5 (by rfl) ⟨15338, by rfl⟩ : syracuseStep 327221 = 30677) (by norm_num)
theorem B327245 : Blo 215810 327245 := bbase (se 3 (by rfl) ⟨61358, by rfl⟩ : syracuseStep 327245 = 122717) (by norm_num)
theorem B491093 : Blo 215810 491093 := bbase (se 8 (by rfl) ⟨2877, by rfl⟩ : syracuseStep 491093 = 5755) (by norm_num)
theorem B327269 : Blo 215810 327269 := bbase (se 4 (by rfl) ⟨30681, by rfl⟩ : syracuseStep 327269 = 61363) (by norm_num)
theorem B327293 : Blo 215810 327293 := bbase (se 3 (by rfl) ⟨61367, by rfl⟩ : syracuseStep 327293 = 122735) (by norm_num)
theorem B327317 : Blo 215810 327317 := bbase (se 6 (by rfl) ⟨7671, by rfl⟩ : syracuseStep 327317 = 15343) (by norm_num)
theorem B491165 : Blo 215810 491165 := bbase (se 3 (by rfl) ⟨92093, by rfl⟩ : syracuseStep 491165 = 184187) (by norm_num)
theorem B327341 : Blo 215810 327341 := bbase (se 3 (by rfl) ⟨61376, by rfl⟩ : syracuseStep 327341 = 122753) (by norm_num)
theorem B327365 : Blo 215810 327365 := bbase (se 4 (by rfl) ⟨30690, by rfl⟩ : syracuseStep 327365 = 61381) (by norm_num)
theorem B327389 : Blo 215810 327389 := bbase (se 3 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 327389 = 122771) (by norm_num)
theorem B491237 : Blo 215810 491237 := bbase (se 4 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 491237 = 92107) (by norm_num)
theorem B327413 : Blo 215810 327413 := bbase (se 5 (by rfl) ⟨15347, by rfl⟩ : syracuseStep 327413 = 30695) (by norm_num)
theorem B327437 : Blo 215810 327437 := bbase (se 3 (by rfl) ⟨61394, by rfl⟩ : syracuseStep 327437 = 122789) (by norm_num)
theorem B327461 : Blo 215810 327461 := bbase (se 4 (by rfl) ⟨30699, by rfl⟩ : syracuseStep 327461 = 61399) (by norm_num)
theorem B491309 : Blo 215810 491309 := bbase (se 3 (by rfl) ⟨92120, by rfl⟩ : syracuseStep 491309 = 184241) (by norm_num)
theorem B327485 : Blo 215810 327485 := bbase (se 3 (by rfl) ⟨61403, by rfl⟩ : syracuseStep 327485 = 122807) (by norm_num)
theorem B5930837 : Blo 215810 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B3211093 : Blo 215810 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1408853 : Blo 215810 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B327509 : Blo 215810 327509 := bbase (se 9 (by rfl) ⟨959, by rfl⟩ : syracuseStep 327509 = 1919) (by norm_num)
theorem B327533 : Blo 215810 327533 := bbase (se 3 (by rfl) ⟨61412, by rfl⟩ : syracuseStep 327533 = 122825) (by norm_num)
theorem B491381 : Blo 215810 491381 := bbase (se 5 (by rfl) ⟨23033, by rfl⟩ : syracuseStep 491381 = 46067) (by norm_num)
theorem B327557 : Blo 215810 327557 := bbase (se 4 (by rfl) ⟨30708, by rfl⟩ : syracuseStep 327557 = 61417) (by norm_num)
theorem B327581 : Blo 215810 327581 := bbase (se 3 (by rfl) ⟨61421, by rfl⟩ : syracuseStep 327581 = 122843) (by norm_num)
theorem B393133 : Blo 215810 393133 := bbase (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) (by norm_num)
theorem B327605 : Blo 215810 327605 := bbase (se 5 (by rfl) ⟨15356, by rfl⟩ : syracuseStep 327605 = 30713) (by norm_num)
theorem B491453 : Blo 215810 491453 := bbase (se 3 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 491453 = 184295) (by norm_num)
theorem B327629 : Blo 215810 327629 := bbase (se 3 (by rfl) ⟨61430, by rfl⟩ : syracuseStep 327629 = 122861) (by norm_num)
theorem B327653 : Blo 215810 327653 := bbase (se 4 (by rfl) ⟨30717, by rfl⟩ : syracuseStep 327653 = 61435) (by norm_num)
theorem B1048565 : Blo 215810 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B327677 : Blo 215810 327677 := bbase (se 3 (by rfl) ⟨61439, by rfl⟩ : syracuseStep 327677 = 122879) (by norm_num)
theorem B327683 : Blo 215810 327683 := bstep (se 1 (by rfl) ⟨245762, by rfl⟩ : syracuseStep 327683 = 491525) B491525
theorem B393233 : Blo 215810 393233 := bstep (se 2 (by rfl) ⟨147462, by rfl⟩ : syracuseStep 393233 = 294925) B294925
theorem B327713 : Blo 215810 327713 := bstep (se 2 (by rfl) ⟨122892, by rfl⟩ : syracuseStep 327713 = 245785) B245785
theorem B327731 : Blo 215810 327731 := bstep (se 1 (by rfl) ⟨245798, by rfl⟩ : syracuseStep 327731 = 491597) B491597
theorem B327761 : Blo 215810 327761 := bstep (se 2 (by rfl) ⟨122910, by rfl⟩ : syracuseStep 327761 = 245821) B245821
theorem B327779 : Blo 215810 327779 := bstep (se 1 (by rfl) ⟨245834, by rfl⟩ : syracuseStep 327779 = 491669) B491669
theorem B491633 : Blo 215810 491633 := bstep (se 2 (by rfl) ⟨184362, by rfl⟩ : syracuseStep 491633 = 368725) B368725
theorem B327809 : Blo 215810 327809 := bstep (se 2 (by rfl) ⟨122928, by rfl⟩ : syracuseStep 327809 = 245857) B245857
theorem B491651 : Blo 215810 491651 := bstep (se 1 (by rfl) ⟨368738, by rfl⟩ : syracuseStep 491651 = 737477) B737477
theorem B327827 : Blo 215810 327827 := bstep (se 1 (by rfl) ⟨245870, by rfl⟩ : syracuseStep 327827 = 491741) B491741
theorem B524465 : Blo 215810 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B327857 : Blo 215810 327857 := bstep (se 2 (by rfl) ⟨122946, by rfl⟩ : syracuseStep 327857 = 245893) B245893
theorem B327875 : Blo 215810 327875 := bstep (se 1 (by rfl) ⟨245906, by rfl⟩ : syracuseStep 327875 = 491813) B491813
theorem B40337621 : Blo 215810 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B327905 : Blo 215810 327905 := bstep (se 2 (by rfl) ⟨122964, by rfl⟩ : syracuseStep 327905 = 245929) B245929
theorem B622829 : Blo 215810 622829 := bstep (se 3 (by rfl) ⟨116780, by rfl⟩ : syracuseStep 622829 = 233561) B233561
theorem B327923 : Blo 215810 327923 := bstep (se 1 (by rfl) ⟨245942, by rfl⟩ : syracuseStep 327923 = 491885) B491885
theorem B327953 : Blo 215810 327953 := bstep (se 2 (by rfl) ⟨122982, by rfl⟩ : syracuseStep 327953 = 245965) B245965
theorem B327971 : Blo 215810 327971 := bstep (se 1 (by rfl) ⟨245978, by rfl⟩ : syracuseStep 327971 = 491957) B491957
theorem B328001 : Blo 215810 328001 := bstep (se 2 (by rfl) ⟨123000, by rfl⟩ : syracuseStep 328001 = 246001) B246001
theorem B328019 : Blo 215810 328019 := bstep (se 1 (by rfl) ⟨246014, by rfl⟩ : syracuseStep 328019 = 492029) B492029
theorem B328049 : Blo 215810 328049 := bstep (se 2 (by rfl) ⟨123018, by rfl⟩ : syracuseStep 328049 = 246037) B246037
theorem B524675 : Blo 215810 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B328067 : Blo 215810 328067 := bstep (se 1 (by rfl) ⟨246050, by rfl⟩ : syracuseStep 328067 = 492101) B492101
theorem B491921 : Blo 215810 491921 := bstep (se 2 (by rfl) ⟨184470, by rfl⟩ : syracuseStep 491921 = 368941) B368941
theorem B328097 : Blo 215810 328097 := bstep (se 2 (by rfl) ⟨123036, by rfl⟩ : syracuseStep 328097 = 246073) B246073
theorem B491939 : Blo 215810 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B623011 : Blo 215810 623011 := bstep (se 1 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 623011 = 934517) B934517
theorem B328115 : Blo 215810 328115 := bstep (se 1 (by rfl) ⟨246086, by rfl⟩ : syracuseStep 328115 = 492173) B492173
theorem B328145 : Blo 215810 328145 := bstep (se 2 (by rfl) ⟨123054, by rfl⟩ : syracuseStep 328145 = 246109) B246109
theorem B328163 : Blo 215810 328163 := bstep (se 1 (by rfl) ⟨246122, by rfl⟩ : syracuseStep 328163 = 492245) B492245
theorem B328193 : Blo 215810 328193 := bstep (se 2 (by rfl) ⟨123072, by rfl⟩ : syracuseStep 328193 = 246145) B246145
theorem B328211 : Blo 215810 328211 := bstep (se 1 (by rfl) ⟨246158, by rfl⟩ : syracuseStep 328211 = 492317) B492317
theorem B328241 : Blo 215810 328241 := bstep (se 2 (by rfl) ⟨123090, by rfl⟩ : syracuseStep 328241 = 246181) B246181
theorem B328259 : Blo 215810 328259 := bstep (se 1 (by rfl) ⟨246194, by rfl⟩ : syracuseStep 328259 = 492389) B492389
theorem B328289 : Blo 215810 328289 := bstep (se 2 (by rfl) ⟨123108, by rfl⟩ : syracuseStep 328289 = 246217) B246217
theorem B328307 : Blo 215810 328307 := bstep (se 1 (by rfl) ⟨246230, by rfl⟩ : syracuseStep 328307 = 492461) B492461
theorem B328337 : Blo 215810 328337 := bstep (se 2 (by rfl) ⟨123126, by rfl⟩ : syracuseStep 328337 = 246253) B246253
theorem B328355 : Blo 215810 328355 := bstep (se 1 (by rfl) ⟨246266, by rfl⟩ : syracuseStep 328355 = 492533) B492533
theorem B492209 : Blo 215810 492209 := bstep (se 2 (by rfl) ⟨184578, by rfl⟩ : syracuseStep 492209 = 369157) B369157
theorem B328385 : Blo 215810 328385 := bstep (se 2 (by rfl) ⟨123144, by rfl⟩ : syracuseStep 328385 = 246289) B246289
theorem B492227 : Blo 215810 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B328403 : Blo 215810 328403 := bstep (se 1 (by rfl) ⟨246302, by rfl⟩ : syracuseStep 328403 = 492605) B492605
theorem B328433 : Blo 215810 328433 := bstep (se 2 (by rfl) ⟨123162, by rfl⟩ : syracuseStep 328433 = 246325) B246325
theorem B328451 : Blo 215810 328451 := bstep (se 1 (by rfl) ⟨246338, by rfl⟩ : syracuseStep 328451 = 492677) B492677
theorem B328481 : Blo 215810 328481 := bstep (se 2 (by rfl) ⟨123180, by rfl⟩ : syracuseStep 328481 = 246361) B246361
theorem B820003 : Blo 215810 820003 := bstep (se 1 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 820003 = 1230005) B1230005
theorem B328499 : Blo 215810 328499 := bstep (se 1 (by rfl) ⟨246374, by rfl⟩ : syracuseStep 328499 = 492749) B492749
theorem B328529 : Blo 215810 328529 := bstep (se 2 (by rfl) ⟨123198, by rfl⟩ : syracuseStep 328529 = 246397) B246397
theorem B328547 : Blo 215810 328547 := bstep (se 1 (by rfl) ⟨246410, by rfl⟩ : syracuseStep 328547 = 492821) B492821
theorem B328577 : Blo 215810 328577 := bstep (se 2 (by rfl) ⟨123216, by rfl⟩ : syracuseStep 328577 = 246433) B246433
theorem B623501 : Blo 215810 623501 := bstep (se 3 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 623501 = 233813) B233813
theorem B295825 : Blo 215810 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B328595 : Blo 215810 328595 := bstep (se 1 (by rfl) ⟨246446, by rfl⟩ : syracuseStep 328595 = 492893) B492893
theorem B328625 : Blo 215810 328625 := bstep (se 2 (by rfl) ⟨123234, by rfl⟩ : syracuseStep 328625 = 246469) B246469
theorem B328643 : Blo 215810 328643 := bstep (se 1 (by rfl) ⟨246482, by rfl⟩ : syracuseStep 328643 = 492965) B492965
theorem B492497 : Blo 215810 492497 := bstep (se 2 (by rfl) ⟨184686, by rfl⟩ : syracuseStep 492497 = 369373) B369373
theorem B328673 : Blo 215810 328673 := bstep (se 2 (by rfl) ⟨123252, by rfl⟩ : syracuseStep 328673 = 246505) B246505
theorem B492515 : Blo 215810 492515 := bstep (se 1 (by rfl) ⟨369386, by rfl⟩ : syracuseStep 492515 = 738773) B738773
theorem B328691 : Blo 215810 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B328721 : Blo 215810 328721 := bstep (se 2 (by rfl) ⟨123270, by rfl⟩ : syracuseStep 328721 = 246541) B246541
theorem B328739 : Blo 215810 328739 := bstep (se 1 (by rfl) ⟨246554, by rfl⟩ : syracuseStep 328739 = 493109) B493109
theorem B328769 : Blo 215810 328769 := bstep (se 2 (by rfl) ⟨123288, by rfl⟩ : syracuseStep 328769 = 246577) B246577
theorem B328787 : Blo 215810 328787 := bstep (se 1 (by rfl) ⟨246590, by rfl⟩ : syracuseStep 328787 = 493181) B493181
theorem B1049699 : Blo 215810 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B328817 : Blo 215810 328817 := bstep (se 2 (by rfl) ⟨123306, by rfl⟩ : syracuseStep 328817 = 246613) B246613
theorem B263299 : Blo 215810 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B328835 : Blo 215810 328835 := bstep (se 1 (by rfl) ⟨246626, by rfl⟩ : syracuseStep 328835 = 493253) B493253
theorem B328865 : Blo 215810 328865 := bstep (se 2 (by rfl) ⟨123324, by rfl⟩ : syracuseStep 328865 = 246649) B246649
theorem B328883 : Blo 215810 328883 := bstep (se 1 (by rfl) ⟨246662, by rfl⟩ : syracuseStep 328883 = 493325) B493325
theorem B328913 : Blo 215810 328913 := bstep (se 2 (by rfl) ⟨123342, by rfl⟩ : syracuseStep 328913 = 246685) B246685
theorem B263395 : Blo 215810 263395 := bstep (se 1 (by rfl) ⟨197546, by rfl⟩ : syracuseStep 263395 = 395093) B395093
theorem B328931 : Blo 215810 328931 := bstep (se 1 (by rfl) ⟨246698, by rfl⟩ : syracuseStep 328931 = 493397) B493397
theorem B492785 : Blo 215810 492785 := bstep (se 2 (by rfl) ⟨184794, by rfl⟩ : syracuseStep 492785 = 369589) B369589
theorem B328961 : Blo 215810 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B492803 : Blo 215810 492803 := bstep (se 1 (by rfl) ⟨369602, by rfl⟩ : syracuseStep 492803 = 739205) B739205
theorem B328979 : Blo 215810 328979 := bstep (se 1 (by rfl) ⟨246734, by rfl⟩ : syracuseStep 328979 = 493469) B493469
theorem B1246499 : Blo 215810 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B329009 : Blo 215810 329009 := bstep (se 2 (by rfl) ⟨123378, by rfl⟩ : syracuseStep 329009 = 246757) B246757
theorem B329027 : Blo 215810 329027 := bstep (se 1 (by rfl) ⟨246770, by rfl⟩ : syracuseStep 329027 = 493541) B493541
theorem B329057 : Blo 215810 329057 := bstep (se 2 (by rfl) ⟨123396, by rfl⟩ : syracuseStep 329057 = 246793) B246793
theorem B329075 : Blo 215810 329075 := bstep (se 1 (by rfl) ⟨246806, by rfl⟩ : syracuseStep 329075 = 493613) B493613
theorem B329105 : Blo 215810 329105 := bstep (se 2 (by rfl) ⟨123414, by rfl⟩ : syracuseStep 329105 = 246829) B246829
theorem B329123 : Blo 215810 329123 := bstep (se 1 (by rfl) ⟨246842, by rfl⟩ : syracuseStep 329123 = 493685) B493685
theorem B329153 : Blo 215810 329153 := bstep (se 2 (by rfl) ⟨123432, by rfl⟩ : syracuseStep 329153 = 246865) B246865
theorem B329171 : Blo 215810 329171 := bstep (se 1 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 329171 = 493757) B493757
theorem B329201 : Blo 215810 329201 := bstep (se 2 (by rfl) ⟨123450, by rfl⟩ : syracuseStep 329201 = 246901) B246901
theorem B329219 : Blo 215810 329219 := bstep (se 1 (by rfl) ⟨246914, by rfl⟩ : syracuseStep 329219 = 493829) B493829
theorem B493073 : Blo 215810 493073 := bstep (se 2 (by rfl) ⟨184902, by rfl⟩ : syracuseStep 493073 = 369805) B369805
theorem B329249 : Blo 215810 329249 := bstep (se 2 (by rfl) ⟨123468, by rfl⟩ : syracuseStep 329249 = 246937) B246937
theorem B493091 : Blo 215810 493091 := bstep (se 1 (by rfl) ⟨369818, by rfl⟩ : syracuseStep 493091 = 739637) B739637
theorem B329267 : Blo 215810 329267 := bstep (se 1 (by rfl) ⟨246950, by rfl⟩ : syracuseStep 329267 = 493901) B493901
theorem B329297 : Blo 215810 329297 := bstep (se 2 (by rfl) ⟨123486, by rfl⟩ : syracuseStep 329297 = 246973) B246973
theorem B329315 : Blo 215810 329315 := bstep (se 1 (by rfl) ⟨246986, by rfl⟩ : syracuseStep 329315 = 493973) B493973
theorem B329345 : Blo 215810 329345 := bstep (se 2 (by rfl) ⟨123504, by rfl⟩ : syracuseStep 329345 = 247009) B247009
theorem B329363 : Blo 215810 329363 := bstep (se 1 (by rfl) ⟨247022, by rfl⟩ : syracuseStep 329363 = 494045) B494045
theorem B329393 : Blo 215810 329393 := bstep (se 2 (by rfl) ⟨123522, by rfl⟩ : syracuseStep 329393 = 247045) B247045
theorem B329411 : Blo 215810 329411 := bstep (se 1 (by rfl) ⟨247058, by rfl⟩ : syracuseStep 329411 = 494117) B494117
theorem B329441 : Blo 215810 329441 := bstep (se 2 (by rfl) ⟨123540, by rfl⟩ : syracuseStep 329441 = 247081) B247081
theorem B1050353 : Blo 215810 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B329459 : Blo 215810 329459 := bstep (se 1 (by rfl) ⟨247094, by rfl⟩ : syracuseStep 329459 = 494189) B494189
theorem B329489 : Blo 215810 329489 := bstep (se 2 (by rfl) ⟨123558, by rfl⟩ : syracuseStep 329489 = 247117) B247117
theorem B329507 : Blo 215810 329507 := bstep (se 1 (by rfl) ⟨247130, by rfl⟩ : syracuseStep 329507 = 494261) B494261
theorem B493361 : Blo 215810 493361 := bstep (se 2 (by rfl) ⟨185010, by rfl⟩ : syracuseStep 493361 = 370021) B370021
theorem B329537 : Blo 215810 329537 := bstep (se 2 (by rfl) ⟨123576, by rfl⟩ : syracuseStep 329537 = 247153) B247153
theorem B493379 : Blo 215810 493379 := bstep (se 1 (by rfl) ⟨370034, by rfl⟩ : syracuseStep 493379 = 740069) B740069
theorem B329555 : Blo 215810 329555 := bstep (se 1 (by rfl) ⟨247166, by rfl⟩ : syracuseStep 329555 = 494333) B494333
theorem B329585 : Blo 215810 329585 := bstep (se 2 (by rfl) ⟨123594, by rfl⟩ : syracuseStep 329585 = 247189) B247189
theorem B329603 : Blo 215810 329603 := bstep (se 1 (by rfl) ⟨247202, by rfl⟩ : syracuseStep 329603 = 494405) B494405
theorem B329633 : Blo 215810 329633 := bstep (se 2 (by rfl) ⟨123612, by rfl⟩ : syracuseStep 329633 = 247225) B247225
theorem B329651 : Blo 215810 329651 := bstep (se 1 (by rfl) ⟨247238, by rfl⟩ : syracuseStep 329651 = 494477) B494477
theorem B329681 : Blo 215810 329681 := bstep (se 2 (by rfl) ⟨123630, by rfl⟩ : syracuseStep 329681 = 247261) B247261
theorem B231395 : Blo 215810 231395 := bstep (se 1 (by rfl) ⟨173546, by rfl⟩ : syracuseStep 231395 = 347093) B347093
theorem B329699 : Blo 215810 329699 := bstep (se 1 (by rfl) ⟨247274, by rfl⟩ : syracuseStep 329699 = 494549) B494549
theorem B329729 : Blo 215810 329729 := bstep (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) B247297
theorem B624685 : Blo 215810 624685 := bstep (se 3 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 624685 = 234257) B234257
theorem B493649 : Blo 215810 493649 := bstep (se 2 (by rfl) ⟨185118, by rfl⟩ : syracuseStep 493649 = 370237) B370237
theorem B493667 : Blo 215810 493667 := bstep (se 1 (by rfl) ⟨370250, by rfl⟩ : syracuseStep 493667 = 740501) B740501
theorem B2001037 : Blo 215810 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B526513 : Blo 215810 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B1247501 : Blo 215810 1247501 := bstep (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) B467813
theorem B493937 : Blo 215810 493937 := bstep (se 2 (by rfl) ⟨185226, by rfl⟩ : syracuseStep 493937 = 370453) B370453
theorem B493955 : Blo 215810 493955 := bstep (se 1 (by rfl) ⟨370466, by rfl⟩ : syracuseStep 493955 = 740933) B740933
theorem B494225 : Blo 215810 494225 := bstep (se 2 (by rfl) ⟨185334, by rfl⟩ : syracuseStep 494225 = 370669) B370669
theorem B494243 : Blo 215810 494243 := bstep (se 1 (by rfl) ⟨370682, by rfl⟩ : syracuseStep 494243 = 741365) B741365
theorem B232147 : Blo 215810 232147 := bstep (se 1 (by rfl) ⟨174110, by rfl⟩ : syracuseStep 232147 = 348221) B348221
theorem B494513 : Blo 215810 494513 := bstep (se 2 (by rfl) ⟨185442, by rfl⟩ : syracuseStep 494513 = 370885) B370885
theorem B494531 : Blo 215810 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B822221 : Blo 215810 822221 := bstep (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) B308333
theorem B232403 : Blo 215810 232403 := bstep (se 1 (by rfl) ⟨174302, by rfl⟩ : syracuseStep 232403 = 348605) B348605
theorem B1051697 : Blo 215810 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B625745 : Blo 215810 625745 := bstep (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) B469309
theorem B330995 : Blo 215810 330995 := bstep (se 1 (by rfl) ⟨248246, by rfl⟩ : syracuseStep 330995 = 496493) B496493
theorem B691469 : Blo 215810 691469 := bstep (se 3 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 691469 = 259301) B259301
theorem B593201 : Blo 215810 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B1314245 : Blo 215810 1314245 := bstep (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) B246421
theorem B462449 : Blo 215810 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B790157 : Blo 215810 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B659107 : Blo 215810 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B233155 : Blo 215810 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B364243 : Blo 215810 364243 := bstep (se 1 (by rfl) ⟨273182, by rfl⟩ : syracuseStep 364243 = 546365) B546365
theorem B593677 : Blo 215810 593677 := bstep (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) B222629
theorem B364385 : Blo 215810 364385 := bstep (se 2 (by rfl) ⟨136644, by rfl⟩ : syracuseStep 364385 = 273289) B273289
theorem B1052621 : Blo 215810 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B364513 : Blo 215810 364513 := bstep (se 2 (by rfl) ⟨136692, by rfl⟩ : syracuseStep 364513 = 273385) B273385
theorem B364547 : Blo 215810 364547 := bstep (se 1 (by rfl) ⟨273410, by rfl⟩ : syracuseStep 364547 = 546821) B546821
theorem B364675 : Blo 215810 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B954595 : Blo 215810 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B364817 : Blo 215810 364817 := bstep (se 2 (by rfl) ⟨136806, by rfl⟩ : syracuseStep 364817 = 273613) B273613
theorem B1773893 : Blo 215810 1773893 := bstep (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) B332605
theorem B364945 : Blo 215810 364945 := bstep (se 2 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 364945 = 273709) B273709
theorem B364979 : Blo 215810 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B365107 : Blo 215810 365107 := bstep (se 1 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 365107 = 547661) B547661
theorem B627277 : Blo 215810 627277 := bstep (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) B235229
theorem B365249 : Blo 215810 365249 := bstep (se 2 (by rfl) ⟨136968, by rfl⟩ : syracuseStep 365249 = 273937) B273937
theorem B4264645 : Blo 215810 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B692995 : Blo 215810 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B365377 : Blo 215810 365377 := bstep (se 2 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 365377 = 274033) B274033
theorem B365411 : Blo 215810 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B463747 : Blo 215810 463747 := bstep (se 1 (by rfl) ⟨347810, by rfl⟩ : syracuseStep 463747 = 695621) B695621
theorem B234419 : Blo 215810 234419 := bstep (se 1 (by rfl) ⟨175814, by rfl⟩ : syracuseStep 234419 = 351629) B351629
theorem B660433 : Blo 215810 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B365539 : Blo 215810 365539 := bstep (se 1 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 365539 = 548309) B548309
theorem B1184867 : Blo 215810 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B365681 : Blo 215810 365681 := bstep (se 2 (by rfl) ⟨137130, by rfl⟩ : syracuseStep 365681 = 274261) B274261
theorem B1250417 : Blo 215810 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B365809 : Blo 215810 365809 := bstep (se 2 (by rfl) ⟨137178, by rfl⟩ : syracuseStep 365809 = 274357) B274357
theorem B2528497 : Blo 215810 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B1873165 : Blo 215810 1873165 := bstep (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) B702437
theorem B365843 : Blo 215810 365843 := bstep (se 1 (by rfl) ⟨274382, by rfl⟩ : syracuseStep 365843 = 548765) B548765
theorem B660881 : Blo 215810 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B365971 : Blo 215810 365971 := bstep (se 1 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 365971 = 548957) B548957
theorem B267667 : Blo 215810 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B1578467 : Blo 215810 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B366113 : Blo 215810 366113 := bstep (se 2 (by rfl) ⟨137292, by rfl⟩ : syracuseStep 366113 = 274585) B274585
theorem B366241 : Blo 215810 366241 := bstep (se 2 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 366241 = 274681) B274681
theorem B366275 : Blo 215810 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B825137 : Blo 215810 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B366403 : Blo 215810 366403 := bstep (se 1 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 366403 = 549605) B549605
theorem B366545 : Blo 215810 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B923633 : Blo 215810 923633 := bstep (se 2 (by rfl) ⟨346362, by rfl⟩ : syracuseStep 923633 = 692725) B692725
theorem B366673 : Blo 215810 366673 := bstep (se 2 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 366673 = 275005) B275005
theorem B464977 : Blo 215810 464977 := bstep (se 2 (by rfl) ⟨174366, by rfl⟩ : syracuseStep 464977 = 348733) B348733
theorem B366707 : Blo 215810 366707 := bstep (se 1 (by rfl) ⟨275030, by rfl⟩ : syracuseStep 366707 = 550061) B550061
theorem B2398349 : Blo 215810 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B366835 : Blo 215810 366835 := bstep (se 1 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 366835 = 550253) B550253
theorem B694595 : Blo 215810 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B366977 : Blo 215810 366977 := bstep (se 2 (by rfl) ⟨137616, by rfl⟩ : syracuseStep 366977 = 275233) B275233
theorem B498097 : Blo 215810 498097 := bstep (se 2 (by rfl) ⟨186786, by rfl⟩ : syracuseStep 498097 = 373573) B373573
theorem B367105 : Blo 215810 367105 := bstep (se 2 (by rfl) ⟨137664, by rfl⟩ : syracuseStep 367105 = 275329) B275329
theorem B367139 : Blo 215810 367139 := bstep (se 1 (by rfl) ⟨275354, by rfl⟩ : syracuseStep 367139 = 550709) B550709
theorem B1251875 : Blo 215810 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B1874501 : Blo 215810 1874501 := bstep (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) B351469
theorem B367267 : Blo 215810 367267 := bstep (se 1 (by rfl) ⟨275450, by rfl⟩ : syracuseStep 367267 = 550901) B550901
theorem B563939 : Blo 215810 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B367409 : Blo 215810 367409 := bstep (se 2 (by rfl) ⟨137778, by rfl⟩ : syracuseStep 367409 = 275557) B275557
theorem B2235235 : Blo 215810 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B465763 : Blo 215810 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B498545 : Blo 215810 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B367537 : Blo 215810 367537 := bstep (se 2 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 367537 = 275653) B275653
theorem B367571 : Blo 215810 367571 := bstep (se 1 (by rfl) ⟨275678, by rfl⟩ : syracuseStep 367571 = 551357) B551357
theorem B662573 : Blo 215810 662573 := bstep (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) B248465
theorem B367699 : Blo 215810 367699 := bstep (se 1 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 367699 = 551549) B551549
theorem B367841 : Blo 215810 367841 := bstep (se 2 (by rfl) ⟨137940, by rfl⟩ : syracuseStep 367841 = 275881) B275881
theorem B826595 : Blo 215810 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B695569 : Blo 215810 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B367969 : Blo 215810 367969 := bstep (se 2 (by rfl) ⟨137988, by rfl⟩ : syracuseStep 367969 = 275977) B275977
theorem B368003 : Blo 215810 368003 := bstep (se 1 (by rfl) ⟨276002, by rfl⟩ : syracuseStep 368003 = 552005) B552005
theorem B368131 : Blo 215810 368131 := bstep (se 1 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 368131 = 552197) B552197
theorem B728621 : Blo 215810 728621 := bstep (se 3 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 728621 = 273233) B273233
theorem B466481 : Blo 215810 466481 := bstep (se 2 (by rfl) ⟨174930, by rfl⟩ : syracuseStep 466481 = 349861) B349861
theorem B728675 : Blo 215810 728675 := bstep (se 1 (by rfl) ⟨546506, by rfl⟩ : syracuseStep 728675 = 1093013) B1093013
theorem B368273 : Blo 215810 368273 := bstep (se 2 (by rfl) ⟨138102, by rfl⟩ : syracuseStep 368273 = 276205) B276205
theorem B2465477 : Blo 215810 2465477 := bstep (se 4 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 2465477 = 462277) B462277
theorem B368401 : Blo 215810 368401 := bstep (se 2 (by rfl) ⟨138150, by rfl⟩ : syracuseStep 368401 = 276301) B276301
theorem B368435 : Blo 215810 368435 := bstep (se 1 (by rfl) ⟨276326, by rfl⟩ : syracuseStep 368435 = 552653) B552653
theorem B728945 : Blo 215810 728945 := bstep (se 2 (by rfl) ⟨273354, by rfl⟩ : syracuseStep 728945 = 546709) B546709
theorem B3383153 : Blo 215810 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B368563 : Blo 215810 368563 := bstep (se 1 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 368563 = 552845) B552845
theorem B761827 : Blo 215810 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B466993 : Blo 215810 466993 := bstep (se 2 (by rfl) ⟨175122, by rfl⟩ : syracuseStep 466993 = 350245) B350245
theorem B368705 : Blo 215810 368705 := bstep (se 2 (by rfl) ⟨138264, by rfl⟩ : syracuseStep 368705 = 276529) B276529
theorem B368833 : Blo 215810 368833 := bstep (se 2 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 368833 = 276625) B276625
theorem B827597 : Blo 215810 827597 := bstep (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) B310349
theorem B368867 : Blo 215810 368867 := bstep (se 1 (by rfl) ⟨276650, by rfl⟩ : syracuseStep 368867 = 553301) B553301
theorem B368995 : Blo 215810 368995 := bstep (se 1 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 368995 = 553493) B553493
theorem B729485 : Blo 215810 729485 := bstep (se 3 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 729485 = 273557) B273557
theorem B926093 : Blo 215810 926093 := bstep (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) B347285
theorem B729539 : Blo 215810 729539 := bstep (se 1 (by rfl) ⟨547154, by rfl⟩ : syracuseStep 729539 = 1094309) B1094309
theorem B369137 : Blo 215810 369137 := bstep (se 2 (by rfl) ⟨138426, by rfl⟩ : syracuseStep 369137 = 276853) B276853
theorem B1319429 : Blo 215810 1319429 := bstep (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) B247393
theorem B369265 : Blo 215810 369265 := bstep (se 2 (by rfl) ⟨138474, by rfl⟩ : syracuseStep 369265 = 276949) B276949
theorem B369299 : Blo 215810 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B565937 : Blo 215810 565937 := bstep (se 2 (by rfl) ⟨212226, by rfl⟩ : syracuseStep 565937 = 424453) B424453
theorem B729809 : Blo 215810 729809 := bstep (se 2 (by rfl) ⟨273678, by rfl⟩ : syracuseStep 729809 = 547357) B547357
theorem B631523 : Blo 215810 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B369427 : Blo 215810 369427 := bstep (se 1 (by rfl) ⟨277070, by rfl⟩ : syracuseStep 369427 = 554141) B554141
theorem B1254179 : Blo 215810 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B664433 : Blo 215810 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B369569 : Blo 215810 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B697261 : Blo 215810 697261 := bstep (se 3 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 697261 = 261473) B261473
theorem B664529 : Blo 215810 664529 := bstep (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) B498397
theorem B369697 : Blo 215810 369697 := bstep (se 2 (by rfl) ⟨138636, by rfl⟩ : syracuseStep 369697 = 277273) B277273
theorem B369731 : Blo 215810 369731 := bstep (se 1 (by rfl) ⟨277298, by rfl⟩ : syracuseStep 369731 = 554597) B554597
theorem B369857 : Blo 215810 369857 := bstep (se 2 (by rfl) ⟨138696, by rfl⟩ : syracuseStep 369857 = 277393) B277393
theorem B369859 : Blo 215810 369859 := bstep (se 1 (by rfl) ⟨277394, by rfl⟩ : syracuseStep 369859 = 554789) B554789
theorem B730349 : Blo 215810 730349 := bstep (se 3 (by rfl) ⟨136940, by rfl⟩ : syracuseStep 730349 = 273881) B273881
theorem B730403 : Blo 215810 730403 := bstep (se 1 (by rfl) ⟨547802, by rfl⟩ : syracuseStep 730403 = 1095605) B1095605
theorem B370001 : Blo 215810 370001 := bstep (se 2 (by rfl) ⟨138750, by rfl⟩ : syracuseStep 370001 = 277501) B277501
theorem B370129 : Blo 215810 370129 := bstep (se 2 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 370129 = 277597) B277597
theorem B370163 : Blo 215810 370163 := bstep (se 1 (by rfl) ⟨277622, by rfl⟩ : syracuseStep 370163 = 555245) B555245
theorem B468497 : Blo 215810 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B730673 : Blo 215810 730673 := bstep (se 2 (by rfl) ⟨274002, by rfl⟩ : syracuseStep 730673 = 548005) B548005
theorem B370291 : Blo 215810 370291 := bstep (se 1 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 370291 = 555437) B555437
theorem B927409 : Blo 215810 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B370433 : Blo 215810 370433 := bstep (se 2 (by rfl) ⟨138912, by rfl⟩ : syracuseStep 370433 = 277825) B277825
theorem B337745 : Blo 215810 337745 := bstep (se 2 (by rfl) ⟨126654, by rfl⟩ : syracuseStep 337745 = 253309) B253309
theorem B370561 : Blo 215810 370561 := bstep (se 2 (by rfl) ⟨138960, by rfl⟩ : syracuseStep 370561 = 277921) B277921
theorem B468899 : Blo 215810 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B370595 : Blo 215810 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B6301637 : Blo 215810 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B993293 : Blo 215810 993293 := bstep (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) B372485
theorem B370723 : Blo 215810 370723 := bstep (se 1 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 370723 = 556085) B556085
theorem B731213 : Blo 215810 731213 := bstep (se 3 (by rfl) ⟨137102, by rfl⟩ : syracuseStep 731213 = 274205) B274205
theorem B731267 : Blo 215810 731267 := bstep (se 1 (by rfl) ⟨548450, by rfl⟩ : syracuseStep 731267 = 1096901) B1096901
theorem B370865 : Blo 215810 370865 := bstep (se 2 (by rfl) ⟨139074, by rfl⟩ : syracuseStep 370865 = 278149) B278149
theorem B338131 : Blo 215810 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B829709 : Blo 215810 829709 := bstep (se 3 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 829709 = 311141) B311141
theorem B600419 : Blo 215810 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B731537 : Blo 215810 731537 := bstep (se 2 (by rfl) ⟨274326, by rfl⟩ : syracuseStep 731537 = 548653) B548653
theorem B699043 : Blo 215810 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B732077 : Blo 215810 732077 := bstep (se 3 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 732077 = 274529) B274529
theorem B371665 : Blo 215810 371665 := bstep (se 2 (by rfl) ⟨139374, by rfl⟩ : syracuseStep 371665 = 278749) B278749
theorem B732131 : Blo 215810 732131 := bstep (se 1 (by rfl) ⟨549098, by rfl⟩ : syracuseStep 732131 = 1098197) B1098197
theorem B273395 : Blo 215810 273395 := bstep (se 1 (by rfl) ⟨205046, by rfl⟩ : syracuseStep 273395 = 410093) B410093
theorem B830513 : Blo 215810 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B699491 : Blo 215810 699491 := bstep (se 1 (by rfl) ⟨524618, by rfl⟩ : syracuseStep 699491 = 1049237) B1049237
theorem B3550321 : Blo 215810 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B732401 : Blo 215810 732401 := bstep (se 2 (by rfl) ⟨274650, by rfl⟩ : syracuseStep 732401 = 549301) B549301
theorem B6040973 : Blo 215810 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B274099 : Blo 215810 274099 := bstep (se 1 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 274099 = 411149) B411149
theorem B831181 : Blo 215810 831181 := bstep (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) B311693
theorem B732941 : Blo 215810 732941 := bstep (se 3 (by rfl) ⟨137426, by rfl⟩ : syracuseStep 732941 = 274853) B274853
theorem B274195 : Blo 215810 274195 := bstep (se 1 (by rfl) ⟨205646, by rfl⟩ : syracuseStep 274195 = 411293) B411293
theorem B732995 : Blo 215810 732995 := bstep (se 1 (by rfl) ⟨549746, by rfl⟩ : syracuseStep 732995 = 1099493) B1099493
theorem B733265 : Blo 215810 733265 := bstep (se 2 (by rfl) ⟨274974, by rfl⟩ : syracuseStep 733265 = 549949) B549949
theorem B1388677 : Blo 215810 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B372977 : Blo 215810 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B274691 : Blo 215810 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B700721 : Blo 215810 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B438691 : Blo 215810 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B307633 : Blo 215810 307633 := bstep (se 2 (by rfl) ⟨115362, by rfl⟩ : syracuseStep 307633 = 230725) B230725
theorem B831971 : Blo 215810 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B307729 : Blo 215810 307729 := bstep (se 2 (by rfl) ⟨115398, by rfl⟩ : syracuseStep 307729 = 230797) B230797
theorem B733805 : Blo 215810 733805 := bstep (se 3 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 733805 = 275177) B275177
theorem B733859 : Blo 215810 733859 := bstep (se 1 (by rfl) ⟨550394, by rfl⟩ : syracuseStep 733859 = 1100789) B1100789
theorem B930467 : Blo 215810 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B1651427 : Blo 215810 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B439121 : Blo 215810 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B734129 : Blo 215810 734129 := bstep (se 2 (by rfl) ⟨275298, by rfl⟩ : syracuseStep 734129 = 550597) B550597
theorem B275395 : Blo 215810 275395 := bstep (se 1 (by rfl) ⟨206546, by rfl⟩ : syracuseStep 275395 = 413093) B413093
theorem B308225 : Blo 215810 308225 := bstep (se 2 (by rfl) ⟨115584, by rfl⟩ : syracuseStep 308225 = 231169) B231169
theorem B832547 : Blo 215810 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B275491 : Blo 215810 275491 := bstep (se 1 (by rfl) ⟨206618, by rfl⟩ : syracuseStep 275491 = 413237) B413237
theorem B832625 : Blo 215810 832625 := bstep (se 2 (by rfl) ⟨312234, by rfl⟩ : syracuseStep 832625 = 624469) B624469
theorem B701581 : Blo 215810 701581 := bstep (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) B263093
theorem B242851 : Blo 215810 242851 := bstep (se 1 (by rfl) ⟨182138, by rfl⟩ : syracuseStep 242851 = 364277) B364277
theorem B701617 : Blo 215810 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B10073315 : Blo 215810 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B242995 : Blo 215810 242995 := bstep (se 1 (by rfl) ⟨182246, by rfl⟩ : syracuseStep 242995 = 364493) B364493
theorem B2471309 : Blo 215810 2471309 := bstep (se 3 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 2471309 = 926741) B926741
theorem B243139 : Blo 215810 243139 := bstep (se 1 (by rfl) ⟨182354, by rfl⟩ : syracuseStep 243139 = 364709) B364709
theorem B734669 : Blo 215810 734669 := bstep (se 3 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 734669 = 275501) B275501
theorem B734723 : Blo 215810 734723 := bstep (se 1 (by rfl) ⟨551042, by rfl⟩ : syracuseStep 734723 = 1102085) B1102085
theorem B275987 : Blo 215810 275987 := bstep (se 1 (by rfl) ⟨206990, by rfl⟩ : syracuseStep 275987 = 413981) B413981
theorem B243283 : Blo 215810 243283 := bstep (se 1 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 243283 = 364925) B364925
theorem B1095281 : Blo 215810 1095281 := bstep (se 2 (by rfl) ⟨410730, by rfl⟩ : syracuseStep 1095281 = 821461) B821461
theorem B243427 : Blo 215810 243427 := bstep (se 1 (by rfl) ⟨182570, by rfl⟩ : syracuseStep 243427 = 365141) B365141
theorem B734993 : Blo 215810 734993 := bstep (se 2 (by rfl) ⟨275622, by rfl⟩ : syracuseStep 734993 = 551245) B551245
theorem B1259333 : Blo 215810 1259333 := bstep (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) B236125
theorem B309091 : Blo 215810 309091 := bstep (se 1 (by rfl) ⟨231818, by rfl⟩ : syracuseStep 309091 = 463637) B463637
theorem B243571 : Blo 215810 243571 := bstep (se 1 (by rfl) ⟨182678, by rfl⟩ : syracuseStep 243571 = 365357) B365357
theorem B309187 : Blo 215810 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B243715 : Blo 215810 243715 := bstep (se 1 (by rfl) ⟨182786, by rfl⟩ : syracuseStep 243715 = 365573) B365573
theorem B243859 : Blo 215810 243859 := bstep (se 1 (by rfl) ⟨182894, by rfl⟩ : syracuseStep 243859 = 365789) B365789
theorem B276691 : Blo 215810 276691 := bstep (se 1 (by rfl) ⟨207518, by rfl⟩ : syracuseStep 276691 = 415037) B415037
theorem B244003 : Blo 215810 244003 := bstep (se 1 (by rfl) ⟨183002, by rfl⟩ : syracuseStep 244003 = 366005) B366005
theorem B735533 : Blo 215810 735533 := bstep (se 3 (by rfl) ⟨137912, by rfl⟩ : syracuseStep 735533 = 275825) B275825
theorem B276787 : Blo 215810 276787 := bstep (se 1 (by rfl) ⟨207590, by rfl⟩ : syracuseStep 276787 = 415181) B415181
theorem B735587 : Blo 215810 735587 := bstep (se 1 (by rfl) ⟨551690, by rfl⟩ : syracuseStep 735587 = 1103381) B1103381
theorem B244147 : Blo 215810 244147 := bstep (se 1 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 244147 = 366221) B366221
theorem B309683 : Blo 215810 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B1423813 : Blo 215810 1423813 := bstep (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) B266965
theorem B375251 : Blo 215810 375251 := bstep (se 1 (by rfl) ⟨281438, by rfl⟩ : syracuseStep 375251 = 562877) B562877
theorem B834083 : Blo 215810 834083 := bstep (se 1 (by rfl) ⟨625562, by rfl⟩ : syracuseStep 834083 = 1251125) B1251125
theorem B834097 : Blo 215810 834097 := bstep (se 2 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 834097 = 625573) B625573
theorem B244291 : Blo 215810 244291 := bstep (se 1 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 244291 = 366437) B366437
theorem B703085 : Blo 215810 703085 := bstep (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) B263657
theorem B735857 : Blo 215810 735857 := bstep (se 2 (by rfl) ⟨275946, by rfl⟩ : syracuseStep 735857 = 551893) B551893
theorem B703181 : Blo 215810 703181 := bstep (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) B263693
theorem B244435 : Blo 215810 244435 := bstep (se 1 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 244435 = 366653) B366653
theorem B277283 : Blo 215810 277283 := bstep (se 1 (by rfl) ⟨207962, by rfl⟩ : syracuseStep 277283 = 415925) B415925
theorem B244579 : Blo 215810 244579 := bstep (se 1 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 244579 = 366869) B366869
theorem B244723 : Blo 215810 244723 := bstep (se 1 (by rfl) ⟨183542, by rfl⟩ : syracuseStep 244723 = 367085) B367085
theorem B1096739 : Blo 215810 1096739 := bstep (se 1 (by rfl) ⟨822554, by rfl⟩ : syracuseStep 1096739 = 1645109) B1645109
theorem B1391651 : Blo 215810 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B310321 : Blo 215810 310321 := bstep (se 2 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 310321 = 232741) B232741
theorem B244867 : Blo 215810 244867 := bstep (se 1 (by rfl) ⟨183650, by rfl⟩ : syracuseStep 244867 = 367301) B367301
theorem B736397 : Blo 215810 736397 := bstep (se 3 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 736397 = 276149) B276149
theorem B736451 : Blo 215810 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B245011 : Blo 215810 245011 := bstep (se 1 (by rfl) ⟨183758, by rfl⟩ : syracuseStep 245011 = 367517) B367517
theorem B310657 : Blo 215810 310657 := bstep (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) B232993
theorem B245155 : Blo 215810 245155 := bstep (se 1 (by rfl) ⟨183866, by rfl⟩ : syracuseStep 245155 = 367733) B367733
theorem B474545 : Blo 215810 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B736721 : Blo 215810 736721 := bstep (se 2 (by rfl) ⟨276270, by rfl⟩ : syracuseStep 736721 = 552541) B552541
theorem B277987 : Blo 215810 277987 := bstep (se 1 (by rfl) ⟨208490, by rfl⟩ : syracuseStep 277987 = 416981) B416981
theorem B245299 : Blo 215810 245299 := bstep (se 1 (by rfl) ⟨183974, by rfl⟩ : syracuseStep 245299 = 367949) B367949
theorem B278083 : Blo 215810 278083 := bstep (se 1 (by rfl) ⟨208562, by rfl⟩ : syracuseStep 278083 = 417125) B417125
theorem B1326725 : Blo 215810 1326725 := bstep (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) B248761
theorem B245443 : Blo 215810 245443 := bstep (se 1 (by rfl) ⟨184082, by rfl⟩ : syracuseStep 245443 = 368165) B368165
theorem B1392419 : Blo 215810 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B1097549 : Blo 215810 1097549 := bstep (se 3 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 1097549 = 411581) B411581
theorem B245587 : Blo 215810 245587 := bstep (se 1 (by rfl) ⟨184190, by rfl⟩ : syracuseStep 245587 = 368381) B368381
theorem B311249 : Blo 215810 311249 := bstep (se 2 (by rfl) ⟨116718, by rfl⟩ : syracuseStep 311249 = 233437) B233437
theorem B245731 : Blo 215810 245731 := bstep (se 1 (by rfl) ⟨184298, by rfl⟩ : syracuseStep 245731 = 368597) B368597
theorem B737261 : Blo 215810 737261 := bstep (se 3 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 737261 = 276473) B276473
theorem B737315 : Blo 215810 737315 := bstep (se 1 (by rfl) ⟨552986, by rfl⟩ : syracuseStep 737315 = 1105973) B1105973
theorem B1065059 : Blo 215810 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B245875 : Blo 215810 245875 := bstep (se 1 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 245875 = 368813) B368813
theorem B2474225 : Blo 215810 2474225 := bstep (se 2 (by rfl) ⟨927834, by rfl⟩ : syracuseStep 2474225 = 1855669) B1855669
theorem B246019 : Blo 215810 246019 := bstep (se 1 (by rfl) ⟨184514, by rfl⟩ : syracuseStep 246019 = 369029) B369029
theorem B409873 : Blo 215810 409873 := bstep (se 2 (by rfl) ⟨153702, by rfl⟩ : syracuseStep 409873 = 307405) B307405
theorem B737585 : Blo 215810 737585 := bstep (se 2 (by rfl) ⟨276594, by rfl⟩ : syracuseStep 737585 = 553189) B553189
theorem B1982789 : Blo 215810 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B1393037 : Blo 215810 1393037 := bstep (se 3 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 1393037 = 522389) B522389
theorem B246163 : Blo 215810 246163 := bstep (se 1 (by rfl) ⟨184622, by rfl⟩ : syracuseStep 246163 = 369245) B369245
theorem B311779 : Blo 215810 311779 := bstep (se 1 (by rfl) ⟨233834, by rfl⟩ : syracuseStep 311779 = 467669) B467669
theorem B246307 : Blo 215810 246307 := bstep (se 1 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 246307 = 369461) B369461
theorem B410275 : Blo 215810 410275 := bstep (se 1 (by rfl) ⟨307706, by rfl⟩ : syracuseStep 410275 = 615413) B615413
theorem B246451 : Blo 215810 246451 := bstep (se 1 (by rfl) ⟨184838, by rfl⟩ : syracuseStep 246451 = 369677) B369677
theorem B2081477 : Blo 215810 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B410321 : Blo 215810 410321 := bstep (se 2 (by rfl) ⟨153870, by rfl⟩ : syracuseStep 410321 = 307741) B307741
theorem B934669 : Blo 215810 934669 := bstep (se 3 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 934669 = 350501) B350501
theorem B312115 : Blo 215810 312115 := bstep (se 1 (by rfl) ⟨234086, by rfl⟩ : syracuseStep 312115 = 468173) B468173
theorem B246595 : Blo 215810 246595 := bstep (se 1 (by rfl) ⟨184946, by rfl⟩ : syracuseStep 246595 = 369893) B369893
theorem B738125 : Blo 215810 738125 := bstep (se 3 (by rfl) ⟨138398, by rfl⟩ : syracuseStep 738125 = 276797) B276797
theorem B738179 : Blo 215810 738179 := bstep (se 1 (by rfl) ⟨553634, by rfl⟩ : syracuseStep 738179 = 1107269) B1107269
theorem B246739 : Blo 215810 246739 := bstep (se 1 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 246739 = 370109) B370109
theorem B410609 : Blo 215810 410609 := bstep (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) B307957
theorem B246883 : Blo 215810 246883 := bstep (se 1 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 246883 = 370325) B370325
theorem B738449 : Blo 215810 738449 := bstep (se 2 (by rfl) ⟨276918, by rfl⟩ : syracuseStep 738449 = 553837) B553837
theorem B247027 : Blo 215810 247027 := bstep (se 1 (by rfl) ⟨185270, by rfl⟩ : syracuseStep 247027 = 370541) B370541
theorem B312673 : Blo 215810 312673 := bstep (se 2 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 312673 = 234505) B234505
theorem B312707 : Blo 215810 312707 := bstep (se 1 (by rfl) ⟨234530, by rfl⟩ : syracuseStep 312707 = 469061) B469061
theorem B247171 : Blo 215810 247171 := bstep (se 1 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 247171 = 370757) B370757
theorem B1754693 : Blo 215810 1754693 := bstep (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) B329005
theorem B738989 : Blo 215810 738989 := bstep (se 3 (by rfl) ⟨138560, by rfl⟩ : syracuseStep 738989 = 277121) B277121
theorem B411331 : Blo 215810 411331 := bstep (se 1 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 411331 = 616997) B616997
theorem B739043 : Blo 215810 739043 := bstep (se 1 (by rfl) ⟨554282, by rfl⟩ : syracuseStep 739043 = 1108565) B1108565
theorem B345953 : Blo 215810 345953 := bstep (se 2 (by rfl) ⟨129732, by rfl⟩ : syracuseStep 345953 = 259465) B259465
theorem B1656773 : Blo 215810 1656773 := bstep (se 4 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 1656773 = 310645) B310645
theorem B5392325 : Blo 215810 5392325 := bstep (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) B1011061
theorem B739277 : Blo 215810 739277 := bstep (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) B277229
theorem B739313 : Blo 215810 739313 := bstep (se 2 (by rfl) ⟨277242, by rfl⟩ : syracuseStep 739313 = 554485) B554485
theorem B1001521 : Blo 215810 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B346241 : Blo 215810 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B411779 : Blo 215810 411779 := bstep (se 1 (by rfl) ⟨308834, by rfl⟩ : syracuseStep 411779 = 617669) B617669
theorem B739523 : Blo 215810 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B444739 : Blo 215810 444739 := bstep (se 1 (by rfl) ⟨333554, by rfl⟩ : syracuseStep 444739 = 667109) B667109
theorem B346465 : Blo 215810 346465 := bstep (se 2 (by rfl) ⟨129924, by rfl⟩ : syracuseStep 346465 = 259849) B259849
theorem B412067 : Blo 215810 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B739853 : Blo 215810 739853 := bstep (se 3 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 739853 = 277445) B277445
theorem B739907 : Blo 215810 739907 := bstep (se 1 (by rfl) ⟨554930, by rfl⟩ : syracuseStep 739907 = 1109861) B1109861
theorem B1002125 : Blo 215810 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B1100465 : Blo 215810 1100465 := bstep (se 2 (by rfl) ⟨412674, by rfl⟩ : syracuseStep 1100465 = 825349) B825349
theorem B248515 : Blo 215810 248515 := bstep (se 1 (by rfl) ⟨186386, by rfl⟩ : syracuseStep 248515 = 372773) B372773
theorem B215811 : Blo 215810 215811 := bstep (se 1 (by rfl) ⟨161858, by rfl⟩ : syracuseStep 215811 = 323717) B323717
theorem B215827 : Blo 215810 215827 := bstep (se 1 (by rfl) ⟨161870, by rfl⟩ : syracuseStep 215827 = 323741) B323741
theorem B215843 : Blo 215810 215843 := bstep (se 1 (by rfl) ⟨161882, by rfl⟩ : syracuseStep 215843 = 323765) B323765
theorem B740141 : Blo 215810 740141 := bstep (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) B277553
theorem B215859 : Blo 215810 215859 := bstep (se 1 (by rfl) ⟨161894, by rfl⟩ : syracuseStep 215859 = 323789) B323789
theorem B215875 : Blo 215810 215875 := bstep (se 1 (by rfl) ⟨161906, by rfl⟩ : syracuseStep 215875 = 323813) B323813
theorem B740177 : Blo 215810 740177 := bstep (se 2 (by rfl) ⟨277566, by rfl⟩ : syracuseStep 740177 = 555133) B555133
theorem B215891 : Blo 215810 215891 := bstep (se 1 (by rfl) ⟨161918, by rfl⟩ : syracuseStep 215891 = 323837) B323837
theorem B215907 : Blo 215810 215907 := bstep (se 1 (by rfl) ⟨161930, by rfl⟩ : syracuseStep 215907 = 323861) B323861
theorem B215923 : Blo 215810 215923 := bstep (se 1 (by rfl) ⟨161942, by rfl⟩ : syracuseStep 215923 = 323885) B323885
theorem B215939 : Blo 215810 215939 := bstep (se 1 (by rfl) ⟨161954, by rfl⟩ : syracuseStep 215939 = 323909) B323909
theorem B215955 : Blo 215810 215955 := bstep (se 1 (by rfl) ⟨161966, by rfl⟩ : syracuseStep 215955 = 323933) B323933
theorem B215971 : Blo 215810 215971 := bstep (se 1 (by rfl) ⟨161978, by rfl⟩ : syracuseStep 215971 = 323957) B323957
theorem B215987 : Blo 215810 215987 := bstep (se 1 (by rfl) ⟨161990, by rfl⟩ : syracuseStep 215987 = 323981) B323981
theorem B216003 : Blo 215810 216003 := bstep (se 1 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 216003 = 324005) B324005
theorem B216019 : Blo 215810 216019 := bstep (se 1 (by rfl) ⟨162014, by rfl⟩ : syracuseStep 216019 = 324029) B324029
theorem B216035 : Blo 215810 216035 := bstep (se 1 (by rfl) ⟨162026, by rfl⟩ : syracuseStep 216035 = 324053) B324053
theorem B216051 : Blo 215810 216051 := bstep (se 1 (by rfl) ⟨162038, by rfl⟩ : syracuseStep 216051 = 324077) B324077
theorem B216067 : Blo 215810 216067 := bstep (se 1 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 216067 = 324101) B324101
theorem B216083 : Blo 215810 216083 := bstep (se 1 (by rfl) ⟨162062, by rfl⟩ : syracuseStep 216083 = 324125) B324125
theorem B216099 : Blo 215810 216099 := bstep (se 1 (by rfl) ⟨162074, by rfl⟩ : syracuseStep 216099 = 324149) B324149
theorem B216115 : Blo 215810 216115 := bstep (se 1 (by rfl) ⟨162086, by rfl⟩ : syracuseStep 216115 = 324173) B324173
theorem B216131 : Blo 215810 216131 := bstep (se 1 (by rfl) ⟨162098, by rfl⟩ : syracuseStep 216131 = 324197) B324197
theorem B216147 : Blo 215810 216147 := bstep (se 1 (by rfl) ⟨162110, by rfl⟩ : syracuseStep 216147 = 324221) B324221
theorem B216163 : Blo 215810 216163 := bstep (se 1 (by rfl) ⟨162122, by rfl⟩ : syracuseStep 216163 = 324245) B324245
theorem B216179 : Blo 215810 216179 := bstep (se 1 (by rfl) ⟨162134, by rfl⟩ : syracuseStep 216179 = 324269) B324269
theorem B216195 : Blo 215810 216195 := bstep (se 1 (by rfl) ⟨162146, by rfl⟩ : syracuseStep 216195 = 324293) B324293
theorem B216211 : Blo 215810 216211 := bstep (se 1 (by rfl) ⟨162158, by rfl⟩ : syracuseStep 216211 = 324317) B324317
theorem B216227 : Blo 215810 216227 := bstep (se 1 (by rfl) ⟨162170, by rfl⟩ : syracuseStep 216227 = 324341) B324341
theorem B216243 : Blo 215810 216243 := bstep (se 1 (by rfl) ⟨162182, by rfl⟩ : syracuseStep 216243 = 324365) B324365
theorem B216259 : Blo 215810 216259 := bstep (se 1 (by rfl) ⟨162194, by rfl⟩ : syracuseStep 216259 = 324389) B324389
theorem B216275 : Blo 215810 216275 := bstep (se 1 (by rfl) ⟨162206, by rfl⟩ : syracuseStep 216275 = 324413) B324413
theorem B216291 : Blo 215810 216291 := bstep (se 1 (by rfl) ⟨162218, by rfl⟩ : syracuseStep 216291 = 324437) B324437
theorem B216307 : Blo 215810 216307 := bstep (se 1 (by rfl) ⟨162230, by rfl⟩ : syracuseStep 216307 = 324461) B324461
theorem B216323 : Blo 215810 216323 := bstep (se 1 (by rfl) ⟨162242, by rfl⟩ : syracuseStep 216323 = 324485) B324485
theorem B216339 : Blo 215810 216339 := bstep (se 1 (by rfl) ⟨162254, by rfl⟩ : syracuseStep 216339 = 324509) B324509
theorem B216355 : Blo 215810 216355 := bstep (se 1 (by rfl) ⟨162266, by rfl⟩ : syracuseStep 216355 = 324533) B324533
theorem B216371 : Blo 215810 216371 := bstep (se 1 (by rfl) ⟨162278, by rfl⟩ : syracuseStep 216371 = 324557) B324557
theorem B216387 : Blo 215810 216387 := bstep (se 1 (by rfl) ⟨162290, by rfl⟩ : syracuseStep 216387 = 324581) B324581
theorem B413009 : Blo 215810 413009 := bstep (se 2 (by rfl) ⟨154878, by rfl⟩ : syracuseStep 413009 = 309757) B309757
theorem B216403 : Blo 215810 216403 := bstep (se 1 (by rfl) ⟨162302, by rfl⟩ : syracuseStep 216403 = 324605) B324605
theorem B216419 : Blo 215810 216419 := bstep (se 1 (by rfl) ⟨162314, by rfl⟩ : syracuseStep 216419 = 324629) B324629
theorem B740717 : Blo 215810 740717 := bstep (se 3 (by rfl) ⟨138884, by rfl⟩ : syracuseStep 740717 = 277769) B277769
theorem B216435 : Blo 215810 216435 := bstep (se 1 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 216435 = 324653) B324653
theorem B216451 : Blo 215810 216451 := bstep (se 1 (by rfl) ⟨162338, by rfl⟩ : syracuseStep 216451 = 324677) B324677
theorem B3165581 : Blo 215810 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B216467 : Blo 215810 216467 := bstep (se 1 (by rfl) ⟨162350, by rfl⟩ : syracuseStep 216467 = 324701) B324701
theorem B216483 : Blo 215810 216483 := bstep (se 1 (by rfl) ⟨162362, by rfl⟩ : syracuseStep 216483 = 324725) B324725
theorem B740771 : Blo 215810 740771 := bstep (se 1 (by rfl) ⟨555578, by rfl⟩ : syracuseStep 740771 = 1111157) B1111157
theorem B216499 : Blo 215810 216499 := bstep (se 1 (by rfl) ⟨162374, by rfl⟩ : syracuseStep 216499 = 324749) B324749
theorem B216515 : Blo 215810 216515 := bstep (se 1 (by rfl) ⟨162386, by rfl⟩ : syracuseStep 216515 = 324773) B324773
theorem B216531 : Blo 215810 216531 := bstep (se 1 (by rfl) ⟨162398, by rfl⟩ : syracuseStep 216531 = 324797) B324797
theorem B216547 : Blo 215810 216547 := bstep (se 1 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 216547 = 324821) B324821
theorem B1166833 : Blo 215810 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B216563 : Blo 215810 216563 := bstep (se 1 (by rfl) ⟨162422, by rfl⟩ : syracuseStep 216563 = 324845) B324845
theorem B216579 : Blo 215810 216579 := bstep (se 1 (by rfl) ⟨162434, by rfl⟩ : syracuseStep 216579 = 324869) B324869
theorem B216595 : Blo 215810 216595 := bstep (se 1 (by rfl) ⟨162446, by rfl⟩ : syracuseStep 216595 = 324893) B324893
theorem B216611 : Blo 215810 216611 := bstep (se 1 (by rfl) ⟨162458, by rfl⟩ : syracuseStep 216611 = 324917) B324917
theorem B216627 : Blo 215810 216627 := bstep (se 1 (by rfl) ⟨162470, by rfl⟩ : syracuseStep 216627 = 324941) B324941
theorem B216643 : Blo 215810 216643 := bstep (se 1 (by rfl) ⟨162482, by rfl⟩ : syracuseStep 216643 = 324965) B324965
theorem B216659 : Blo 215810 216659 := bstep (se 1 (by rfl) ⟨162494, by rfl⟩ : syracuseStep 216659 = 324989) B324989
theorem B216675 : Blo 215810 216675 := bstep (se 1 (by rfl) ⟨162506, by rfl⟩ : syracuseStep 216675 = 325013) B325013
theorem B216691 : Blo 215810 216691 := bstep (se 1 (by rfl) ⟨162518, by rfl⟩ : syracuseStep 216691 = 325037) B325037
theorem B216707 : Blo 215810 216707 := bstep (se 1 (by rfl) ⟨162530, by rfl⟩ : syracuseStep 216707 = 325061) B325061
theorem B216723 : Blo 215810 216723 := bstep (se 1 (by rfl) ⟨162542, by rfl⟩ : syracuseStep 216723 = 325085) B325085
theorem B216739 : Blo 215810 216739 := bstep (se 1 (by rfl) ⟨162554, by rfl⟩ : syracuseStep 216739 = 325109) B325109
theorem B741041 : Blo 215810 741041 := bstep (se 2 (by rfl) ⟨277890, by rfl⟩ : syracuseStep 741041 = 555781) B555781
theorem B216755 : Blo 215810 216755 := bstep (se 1 (by rfl) ⟨162566, by rfl⟩ : syracuseStep 216755 = 325133) B325133
theorem B216771 : Blo 215810 216771 := bstep (se 1 (by rfl) ⟨162578, by rfl⟩ : syracuseStep 216771 = 325157) B325157
theorem B216787 : Blo 215810 216787 := bstep (se 1 (by rfl) ⟨162590, by rfl⟩ : syracuseStep 216787 = 325181) B325181
theorem B216803 : Blo 215810 216803 := bstep (se 1 (by rfl) ⟨162602, by rfl⟩ : syracuseStep 216803 = 325205) B325205
theorem B216819 : Blo 215810 216819 := bstep (se 1 (by rfl) ⟨162614, by rfl⟩ : syracuseStep 216819 = 325229) B325229
theorem B216835 : Blo 215810 216835 := bstep (se 1 (by rfl) ⟨162626, by rfl⟩ : syracuseStep 216835 = 325253) B325253
theorem B216851 : Blo 215810 216851 := bstep (se 1 (by rfl) ⟨162638, by rfl⟩ : syracuseStep 216851 = 325277) B325277
theorem B216867 : Blo 215810 216867 := bstep (se 1 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 216867 = 325301) B325301
theorem B216883 : Blo 215810 216883 := bstep (se 1 (by rfl) ⟨162662, by rfl⟩ : syracuseStep 216883 = 325325) B325325
theorem B216899 : Blo 215810 216899 := bstep (se 1 (by rfl) ⟨162674, by rfl⟩ : syracuseStep 216899 = 325349) B325349
theorem B216915 : Blo 215810 216915 := bstep (se 1 (by rfl) ⟨162686, by rfl⟩ : syracuseStep 216915 = 325373) B325373
theorem B216931 : Blo 215810 216931 := bstep (se 1 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 216931 = 325397) B325397
theorem B216947 : Blo 215810 216947 := bstep (se 1 (by rfl) ⟨162710, by rfl⟩ : syracuseStep 216947 = 325421) B325421
theorem B216963 : Blo 215810 216963 := bstep (se 1 (by rfl) ⟨162722, by rfl⟩ : syracuseStep 216963 = 325445) B325445
theorem B216979 : Blo 215810 216979 := bstep (se 1 (by rfl) ⟨162734, by rfl⟩ : syracuseStep 216979 = 325469) B325469
theorem B216995 : Blo 215810 216995 := bstep (se 1 (by rfl) ⟨162746, by rfl⟩ : syracuseStep 216995 = 325493) B325493
theorem B348067 : Blo 215810 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B217011 : Blo 215810 217011 := bstep (se 1 (by rfl) ⟨162758, by rfl⟩ : syracuseStep 217011 = 325517) B325517
theorem B217027 : Blo 215810 217027 := bstep (se 1 (by rfl) ⟨162770, by rfl⟩ : syracuseStep 217027 = 325541) B325541
theorem B217043 : Blo 215810 217043 := bstep (se 1 (by rfl) ⟨162782, by rfl⟩ : syracuseStep 217043 = 325565) B325565
theorem B217059 : Blo 215810 217059 := bstep (se 1 (by rfl) ⟨162794, by rfl⟩ : syracuseStep 217059 = 325589) B325589
theorem B217075 : Blo 215810 217075 := bstep (se 1 (by rfl) ⟨162806, by rfl⟩ : syracuseStep 217075 = 325613) B325613
theorem B217091 : Blo 215810 217091 := bstep (se 1 (by rfl) ⟨162818, by rfl⟩ : syracuseStep 217091 = 325637) B325637
theorem B217107 : Blo 215810 217107 := bstep (se 1 (by rfl) ⟨162830, by rfl⟩ : syracuseStep 217107 = 325661) B325661
theorem B217123 : Blo 215810 217123 := bstep (se 1 (by rfl) ⟨162842, by rfl⟩ : syracuseStep 217123 = 325685) B325685
theorem B217139 : Blo 215810 217139 := bstep (se 1 (by rfl) ⟨162854, by rfl⟩ : syracuseStep 217139 = 325709) B325709
theorem B217155 : Blo 215810 217155 := bstep (se 1 (by rfl) ⟨162866, by rfl⟩ : syracuseStep 217155 = 325733) B325733
theorem B217171 : Blo 215810 217171 := bstep (se 1 (by rfl) ⟨162878, by rfl⟩ : syracuseStep 217171 = 325757) B325757
theorem B217187 : Blo 215810 217187 := bstep (se 1 (by rfl) ⟨162890, by rfl⟩ : syracuseStep 217187 = 325781) B325781
theorem B1101923 : Blo 215810 1101923 := bstep (se 1 (by rfl) ⟨826442, by rfl⟩ : syracuseStep 1101923 = 1652885) B1652885
theorem B217203 : Blo 215810 217203 := bstep (se 1 (by rfl) ⟨162902, by rfl⟩ : syracuseStep 217203 = 325805) B325805
theorem B217219 : Blo 215810 217219 := bstep (se 1 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 217219 = 325829) B325829
theorem B217235 : Blo 215810 217235 := bstep (se 1 (by rfl) ⟨162926, by rfl⟩ : syracuseStep 217235 = 325853) B325853
theorem B217251 : Blo 215810 217251 := bstep (se 1 (by rfl) ⟨162938, by rfl⟩ : syracuseStep 217251 = 325877) B325877
theorem B217267 : Blo 215810 217267 := bstep (se 1 (by rfl) ⟨162950, by rfl⟩ : syracuseStep 217267 = 325901) B325901
theorem B217283 : Blo 215810 217283 := bstep (se 1 (by rfl) ⟨162962, by rfl⟩ : syracuseStep 217283 = 325925) B325925
theorem B708803 : Blo 215810 708803 := bstep (se 1 (by rfl) ⟨531602, by rfl⟩ : syracuseStep 708803 = 1063205) B1063205
theorem B741581 : Blo 215810 741581 := bstep (se 3 (by rfl) ⟨139046, by rfl⟩ : syracuseStep 741581 = 278093) B278093
theorem B413905 : Blo 215810 413905 := bstep (se 2 (by rfl) ⟨155214, by rfl⟩ : syracuseStep 413905 = 310429) B310429
theorem B217299 : Blo 215810 217299 := bstep (se 1 (by rfl) ⟨162974, by rfl⟩ : syracuseStep 217299 = 325949) B325949
theorem B217315 : Blo 215810 217315 := bstep (se 1 (by rfl) ⟨162986, by rfl⟩ : syracuseStep 217315 = 325973) B325973
theorem B217331 : Blo 215810 217331 := bstep (se 1 (by rfl) ⟨162998, by rfl⟩ : syracuseStep 217331 = 325997) B325997
theorem B217347 : Blo 215810 217347 := bstep (se 1 (by rfl) ⟨163010, by rfl⟩ : syracuseStep 217347 = 326021) B326021
theorem B741635 : Blo 215810 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B217363 : Blo 215810 217363 := bstep (se 1 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 217363 = 326045) B326045
theorem B217379 : Blo 215810 217379 := bstep (se 1 (by rfl) ⟨163034, by rfl⟩ : syracuseStep 217379 = 326069) B326069
theorem B217395 : Blo 215810 217395 := bstep (se 1 (by rfl) ⟨163046, by rfl⟩ : syracuseStep 217395 = 326093) B326093
theorem B217411 : Blo 215810 217411 := bstep (se 1 (by rfl) ⟨163058, by rfl⟩ : syracuseStep 217411 = 326117) B326117
theorem B217427 : Blo 215810 217427 := bstep (se 1 (by rfl) ⟨163070, by rfl⟩ : syracuseStep 217427 = 326141) B326141
theorem B217443 : Blo 215810 217443 := bstep (se 1 (by rfl) ⟨163082, by rfl⟩ : syracuseStep 217443 = 326165) B326165
theorem B414065 : Blo 215810 414065 := bstep (se 2 (by rfl) ⟨155274, by rfl⟩ : syracuseStep 414065 = 310549) B310549
theorem B217459 : Blo 215810 217459 := bstep (se 1 (by rfl) ⟨163094, by rfl⟩ : syracuseStep 217459 = 326189) B326189
theorem B217475 : Blo 215810 217475 := bstep (se 1 (by rfl) ⟨163106, by rfl⟩ : syracuseStep 217475 = 326213) B326213
theorem B217491 : Blo 215810 217491 := bstep (se 1 (by rfl) ⟨163118, by rfl⟩ : syracuseStep 217491 = 326237) B326237
theorem B217507 : Blo 215810 217507 := bstep (se 1 (by rfl) ⟨163130, by rfl⟩ : syracuseStep 217507 = 326261) B326261
theorem B217523 : Blo 215810 217523 := bstep (se 1 (by rfl) ⟨163142, by rfl⟩ : syracuseStep 217523 = 326285) B326285
theorem B217539 : Blo 215810 217539 := bstep (se 1 (by rfl) ⟨163154, by rfl⟩ : syracuseStep 217539 = 326309) B326309
theorem B17125829 : Blo 215810 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B217555 : Blo 215810 217555 := bstep (se 1 (by rfl) ⟨163166, by rfl⟩ : syracuseStep 217555 = 326333) B326333
theorem B217571 : Blo 215810 217571 := bstep (se 1 (by rfl) ⟨163178, by rfl⟩ : syracuseStep 217571 = 326357) B326357
theorem B217587 : Blo 215810 217587 := bstep (se 1 (by rfl) ⟨163190, by rfl⟩ : syracuseStep 217587 = 326381) B326381
theorem B217603 : Blo 215810 217603 := bstep (se 1 (by rfl) ⟨163202, by rfl⟩ : syracuseStep 217603 = 326405) B326405
theorem B217619 : Blo 215810 217619 := bstep (se 1 (by rfl) ⟨163214, by rfl⟩ : syracuseStep 217619 = 326429) B326429
theorem B217635 : Blo 215810 217635 := bstep (se 1 (by rfl) ⟨163226, by rfl⟩ : syracuseStep 217635 = 326453) B326453
theorem B217651 : Blo 215810 217651 := bstep (se 1 (by rfl) ⟨163238, by rfl⟩ : syracuseStep 217651 = 326477) B326477
theorem B217667 : Blo 215810 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B217683 : Blo 215810 217683 := bstep (se 1 (by rfl) ⟨163262, by rfl⟩ : syracuseStep 217683 = 326525) B326525
theorem B217699 : Blo 215810 217699 := bstep (se 1 (by rfl) ⟨163274, by rfl⟩ : syracuseStep 217699 = 326549) B326549
theorem B217715 : Blo 215810 217715 := bstep (se 1 (by rfl) ⟨163286, by rfl⟩ : syracuseStep 217715 = 326573) B326573
theorem B217731 : Blo 215810 217731 := bstep (se 1 (by rfl) ⟨163298, by rfl⟩ : syracuseStep 217731 = 326597) B326597
theorem B217747 : Blo 215810 217747 := bstep (se 1 (by rfl) ⟨163310, by rfl⟩ : syracuseStep 217747 = 326621) B326621
theorem B217763 : Blo 215810 217763 := bstep (se 1 (by rfl) ⟨163322, by rfl⟩ : syracuseStep 217763 = 326645) B326645
theorem B217779 : Blo 215810 217779 := bstep (se 1 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 217779 = 326669) B326669
theorem B217795 : Blo 215810 217795 := bstep (se 1 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 217795 = 326693) B326693
theorem B217811 : Blo 215810 217811 := bstep (se 1 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 217811 = 326717) B326717
theorem B217827 : Blo 215810 217827 := bstep (se 1 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 217827 = 326741) B326741
theorem B217843 : Blo 215810 217843 := bstep (se 1 (by rfl) ⟨163382, by rfl⟩ : syracuseStep 217843 = 326765) B326765
theorem B217859 : Blo 215810 217859 := bstep (se 1 (by rfl) ⟨163394, by rfl⟩ : syracuseStep 217859 = 326789) B326789
theorem B414467 : Blo 215810 414467 := bstep (se 1 (by rfl) ⟨310850, by rfl⟩ : syracuseStep 414467 = 621701) B621701
theorem B217875 : Blo 215810 217875 := bstep (se 1 (by rfl) ⟨163406, by rfl⟩ : syracuseStep 217875 = 326813) B326813
theorem B217891 : Blo 215810 217891 := bstep (se 1 (by rfl) ⟨163418, by rfl⟩ : syracuseStep 217891 = 326837) B326837
theorem B217907 : Blo 215810 217907 := bstep (se 1 (by rfl) ⟨163430, by rfl⟩ : syracuseStep 217907 = 326861) B326861
theorem B217923 : Blo 215810 217923 := bstep (se 1 (by rfl) ⟨163442, by rfl⟩ : syracuseStep 217923 = 326885) B326885
theorem B217939 : Blo 215810 217939 := bstep (se 1 (by rfl) ⟨163454, by rfl⟩ : syracuseStep 217939 = 326909) B326909
theorem B217955 : Blo 215810 217955 := bstep (se 1 (by rfl) ⟨163466, by rfl⟩ : syracuseStep 217955 = 326933) B326933
theorem B1561457 : Blo 215810 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B217971 : Blo 215810 217971 := bstep (se 1 (by rfl) ⟨163478, by rfl⟩ : syracuseStep 217971 = 326957) B326957
theorem B217987 : Blo 215810 217987 := bstep (se 1 (by rfl) ⟨163490, by rfl⟩ : syracuseStep 217987 = 326981) B326981
theorem B1102733 : Blo 215810 1102733 := bstep (se 3 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 1102733 = 413525) B413525
theorem B218003 : Blo 215810 218003 := bstep (se 1 (by rfl) ⟨163502, by rfl⟩ : syracuseStep 218003 = 327005) B327005
theorem B218019 : Blo 215810 218019 := bstep (se 1 (by rfl) ⟨163514, by rfl⟩ : syracuseStep 218019 = 327029) B327029
theorem B218035 : Blo 215810 218035 := bstep (se 1 (by rfl) ⟨163526, by rfl⟩ : syracuseStep 218035 = 327053) B327053
theorem B218051 : Blo 215810 218051 := bstep (se 1 (by rfl) ⟨163538, by rfl⟩ : syracuseStep 218051 = 327077) B327077
theorem B218067 : Blo 215810 218067 := bstep (se 1 (by rfl) ⟨163550, by rfl⟩ : syracuseStep 218067 = 327101) B327101
theorem B218083 : Blo 215810 218083 := bstep (se 1 (by rfl) ⟨163562, by rfl⟩ : syracuseStep 218083 = 327125) B327125
theorem B218099 : Blo 215810 218099 := bstep (se 1 (by rfl) ⟨163574, by rfl⟩ : syracuseStep 218099 = 327149) B327149
theorem B218115 : Blo 215810 218115 := bstep (se 1 (by rfl) ⟨163586, by rfl⟩ : syracuseStep 218115 = 327173) B327173
theorem B218131 : Blo 215810 218131 := bstep (se 1 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 218131 = 327197) B327197
theorem B218147 : Blo 215810 218147 := bstep (se 1 (by rfl) ⟨163610, by rfl⟩ : syracuseStep 218147 = 327221) B327221
theorem B218163 : Blo 215810 218163 := bstep (se 1 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 218163 = 327245) B327245
theorem B218179 : Blo 215810 218179 := bstep (se 1 (by rfl) ⟨163634, by rfl⟩ : syracuseStep 218179 = 327269) B327269
theorem B218195 : Blo 215810 218195 := bstep (se 1 (by rfl) ⟨163646, by rfl⟩ : syracuseStep 218195 = 327293) B327293
theorem B218211 : Blo 215810 218211 := bstep (se 1 (by rfl) ⟨163658, by rfl⟩ : syracuseStep 218211 = 327317) B327317
theorem B218227 : Blo 215810 218227 := bstep (se 1 (by rfl) ⟨163670, by rfl⟩ : syracuseStep 218227 = 327341) B327341
theorem B218243 : Blo 215810 218243 := bstep (se 1 (by rfl) ⟨163682, by rfl⟩ : syracuseStep 218243 = 327365) B327365
theorem B1234061 : Blo 215810 1234061 := bstep (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) B462773
theorem B218259 : Blo 215810 218259 := bstep (se 1 (by rfl) ⟨163694, by rfl⟩ : syracuseStep 218259 = 327389) B327389
theorem B218275 : Blo 215810 218275 := bstep (se 1 (by rfl) ⟨163706, by rfl⟩ : syracuseStep 218275 = 327413) B327413
theorem B218291 : Blo 215810 218291 := bstep (se 1 (by rfl) ⟨163718, by rfl⟩ : syracuseStep 218291 = 327437) B327437
theorem B218307 : Blo 215810 218307 := bstep (se 1 (by rfl) ⟨163730, by rfl⟩ : syracuseStep 218307 = 327461) B327461
theorem B218323 : Blo 215810 218323 := bstep (se 1 (by rfl) ⟨163742, by rfl⟩ : syracuseStep 218323 = 327485) B327485
theorem B3953891 : Blo 215810 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B939235 : Blo 215810 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B218339 : Blo 215810 218339 := bstep (se 1 (by rfl) ⟨163754, by rfl⟩ : syracuseStep 218339 = 327509) B327509
theorem B218355 : Blo 215810 218355 := bstep (se 1 (by rfl) ⟨163766, by rfl⟩ : syracuseStep 218355 = 327533) B327533
theorem B218371 : Blo 215810 218371 := bstep (se 1 (by rfl) ⟨163778, by rfl⟩ : syracuseStep 218371 = 327557) B327557
theorem B218387 : Blo 215810 218387 := bstep (se 1 (by rfl) ⟨163790, by rfl⟩ : syracuseStep 218387 = 327581) B327581
theorem B218403 : Blo 215810 218403 := bstep (se 1 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 218403 = 327605) B327605
theorem B218419 : Blo 215810 218419 := bstep (se 1 (by rfl) ⟨163814, by rfl⟩ : syracuseStep 218419 = 327629) B327629
theorem B218435 : Blo 215810 218435 := bstep (se 1 (by rfl) ⟨163826, by rfl⟩ : syracuseStep 218435 = 327653) B327653
theorem B218451 : Blo 215810 218451 := bstep (se 1 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 218451 = 327677) B327677
theorem B218467 : Blo 215810 218467 := bstep (se 1 (by rfl) ⟨163850, by rfl⟩ : syracuseStep 218467 = 327701) B327701
theorem B349553 : Blo 215810 349553 := bstep (se 2 (by rfl) ⟨131082, by rfl⟩ : syracuseStep 349553 = 262165) B262165
theorem B218483 : Blo 215810 218483 := bstep (se 1 (by rfl) ⟨163862, by rfl⟩ : syracuseStep 218483 = 327725) B327725
theorem B218499 : Blo 215810 218499 := bstep (se 1 (by rfl) ⟨163874, by rfl⟩ : syracuseStep 218499 = 327749) B327749
theorem B218515 : Blo 215810 218515 := bstep (se 1 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 218515 = 327773) B327773
theorem B218531 : Blo 215810 218531 := bstep (se 1 (by rfl) ⟨163898, by rfl⟩ : syracuseStep 218531 = 327797) B327797
theorem B218547 : Blo 215810 218547 := bstep (se 1 (by rfl) ⟨163910, by rfl⟩ : syracuseStep 218547 = 327821) B327821
theorem B218563 : Blo 215810 218563 := bstep (se 1 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 218563 = 327845) B327845
theorem B218579 : Blo 215810 218579 := bstep (se 1 (by rfl) ⟨163934, by rfl⟩ : syracuseStep 218579 = 327869) B327869
theorem B218595 : Blo 215810 218595 := bstep (se 1 (by rfl) ⟨163946, by rfl⟩ : syracuseStep 218595 = 327893) B327893
theorem B349681 : Blo 215810 349681 := bstep (se 2 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 349681 = 262261) B262261
theorem B218611 : Blo 215810 218611 := bstep (se 1 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 218611 = 327917) B327917
theorem B218627 : Blo 215810 218627 := bstep (se 1 (by rfl) ⟨163970, by rfl⟩ : syracuseStep 218627 = 327941) B327941
theorem B218643 : Blo 215810 218643 := bstep (se 1 (by rfl) ⟨163982, by rfl⟩ : syracuseStep 218643 = 327965) B327965
theorem B218659 : Blo 215810 218659 := bstep (se 1 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 218659 = 327989) B327989
theorem B316963 : Blo 215810 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B218675 : Blo 215810 218675 := bstep (se 1 (by rfl) ⟨164006, by rfl⟩ : syracuseStep 218675 = 328013) B328013
theorem B218691 : Blo 215810 218691 := bstep (se 1 (by rfl) ⟨164018, by rfl⟩ : syracuseStep 218691 = 328037) B328037
theorem B546385 : Blo 215810 546385 := bstep (se 2 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 546385 = 409789) B409789
theorem B218707 : Blo 215810 218707 := bstep (se 1 (by rfl) ⟨164030, by rfl⟩ : syracuseStep 218707 = 328061) B328061
theorem B218723 : Blo 215810 218723 := bstep (se 1 (by rfl) ⟨164042, by rfl⟩ : syracuseStep 218723 = 328085) B328085
theorem B218739 : Blo 215810 218739 := bstep (se 1 (by rfl) ⟨164054, by rfl⟩ : syracuseStep 218739 = 328109) B328109
theorem B218755 : Blo 215810 218755 := bstep (se 1 (by rfl) ⟨164066, by rfl⟩ : syracuseStep 218755 = 328133) B328133
theorem B415363 : Blo 215810 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B218771 : Blo 215810 218771 := bstep (se 1 (by rfl) ⟨164078, by rfl⟩ : syracuseStep 218771 = 328157) B328157
theorem B218787 : Blo 215810 218787 := bstep (se 1 (by rfl) ⟨164090, by rfl⟩ : syracuseStep 218787 = 328181) B328181
theorem B218803 : Blo 215810 218803 := bstep (se 1 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 218803 = 328205) B328205
theorem B218819 : Blo 215810 218819 := bstep (se 1 (by rfl) ⟨164114, by rfl⟩ : syracuseStep 218819 = 328229) B328229
theorem B218835 : Blo 215810 218835 := bstep (se 1 (by rfl) ⟨164126, by rfl⟩ : syracuseStep 218835 = 328253) B328253
theorem B218851 : Blo 215810 218851 := bstep (se 1 (by rfl) ⟨164138, by rfl⟩ : syracuseStep 218851 = 328277) B328277
theorem B218867 : Blo 215810 218867 := bstep (se 1 (by rfl) ⟨164150, by rfl⟩ : syracuseStep 218867 = 328301) B328301
theorem B218883 : Blo 215810 218883 := bstep (se 1 (by rfl) ⟨164162, by rfl⟩ : syracuseStep 218883 = 328325) B328325
theorem B218899 : Blo 215810 218899 := bstep (se 1 (by rfl) ⟨164174, by rfl⟩ : syracuseStep 218899 = 328349) B328349
theorem B415523 : Blo 215810 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B218915 : Blo 215810 218915 := bstep (se 1 (by rfl) ⟨164186, by rfl⟩ : syracuseStep 218915 = 328373) B328373
theorem B907057 : Blo 215810 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B218931 : Blo 215810 218931 := bstep (se 1 (by rfl) ⟨164198, by rfl⟩ : syracuseStep 218931 = 328397) B328397
theorem B218947 : Blo 215810 218947 := bstep (se 1 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 218947 = 328421) B328421
theorem B218963 : Blo 215810 218963 := bstep (se 1 (by rfl) ⟨164222, by rfl⟩ : syracuseStep 218963 = 328445) B328445
theorem B546659 : Blo 215810 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B218979 : Blo 215810 218979 := bstep (se 1 (by rfl) ⟨164234, by rfl⟩ : syracuseStep 218979 = 328469) B328469
theorem B218995 : Blo 215810 218995 := bstep (se 1 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 218995 = 328493) B328493
theorem B219011 : Blo 215810 219011 := bstep (se 1 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 219011 = 328517) B328517
theorem B219027 : Blo 215810 219027 := bstep (se 1 (by rfl) ⟨164270, by rfl⟩ : syracuseStep 219027 = 328541) B328541
theorem B513955 : Blo 215810 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B219043 : Blo 215810 219043 := bstep (se 1 (by rfl) ⟨164282, by rfl⟩ : syracuseStep 219043 = 328565) B328565
theorem B219059 : Blo 215810 219059 := bstep (se 1 (by rfl) ⟨164294, by rfl⟩ : syracuseStep 219059 = 328589) B328589
theorem B219075 : Blo 215810 219075 := bstep (se 1 (by rfl) ⟨164306, by rfl⟩ : syracuseStep 219075 = 328613) B328613
theorem B219091 : Blo 215810 219091 := bstep (se 1 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 219091 = 328637) B328637
theorem B219107 : Blo 215810 219107 := bstep (se 1 (by rfl) ⟨164330, by rfl⟩ : syracuseStep 219107 = 328661) B328661
theorem B219123 : Blo 215810 219123 := bstep (se 1 (by rfl) ⟨164342, by rfl⟩ : syracuseStep 219123 = 328685) B328685
theorem B219139 : Blo 215810 219139 := bstep (se 1 (by rfl) ⟨164354, by rfl⟩ : syracuseStep 219139 = 328709) B328709
theorem B219155 : Blo 215810 219155 := bstep (se 1 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 219155 = 328733) B328733
theorem B546851 : Blo 215810 546851 := bstep (se 1 (by rfl) ⟨410138, by rfl⟩ : syracuseStep 546851 = 820277) B820277
theorem B219171 : Blo 215810 219171 := bstep (se 1 (by rfl) ⟨164378, by rfl⟩ : syracuseStep 219171 = 328757) B328757
theorem B219187 : Blo 215810 219187 := bstep (se 1 (by rfl) ⟨164390, by rfl⟩ : syracuseStep 219187 = 328781) B328781
theorem B219203 : Blo 215810 219203 := bstep (se 1 (by rfl) ⟨164402, by rfl⟩ : syracuseStep 219203 = 328805) B328805
theorem B219219 : Blo 215810 219219 := bstep (se 1 (by rfl) ⟨164414, by rfl⟩ : syracuseStep 219219 = 328829) B328829
theorem B219235 : Blo 215810 219235 := bstep (se 1 (by rfl) ⟨164426, by rfl⟩ : syracuseStep 219235 = 328853) B328853
theorem B219251 : Blo 215810 219251 := bstep (se 1 (by rfl) ⟨164438, by rfl⟩ : syracuseStep 219251 = 328877) B328877
theorem B219267 : Blo 215810 219267 := bstep (se 1 (by rfl) ⟨164450, by rfl⟩ : syracuseStep 219267 = 328901) B328901
theorem B219283 : Blo 215810 219283 := bstep (se 1 (by rfl) ⟨164462, by rfl⟩ : syracuseStep 219283 = 328925) B328925
theorem B219299 : Blo 215810 219299 := bstep (se 1 (by rfl) ⟨164474, by rfl⟩ : syracuseStep 219299 = 328949) B328949
theorem B219315 : Blo 215810 219315 := bstep (se 1 (by rfl) ⟨164486, by rfl⟩ : syracuseStep 219315 = 328973) B328973
theorem B219331 : Blo 215810 219331 := bstep (se 1 (by rfl) ⟨164498, by rfl⟩ : syracuseStep 219331 = 328997) B328997
theorem B219347 : Blo 215810 219347 := bstep (se 1 (by rfl) ⟨164510, by rfl⟩ : syracuseStep 219347 = 329021) B329021
theorem B219363 : Blo 215810 219363 := bstep (se 1 (by rfl) ⟨164522, by rfl⟩ : syracuseStep 219363 = 329045) B329045
theorem B219379 : Blo 215810 219379 := bstep (se 1 (by rfl) ⟨164534, by rfl⟩ : syracuseStep 219379 = 329069) B329069
theorem B219395 : Blo 215810 219395 := bstep (se 1 (by rfl) ⟨164546, by rfl⟩ : syracuseStep 219395 = 329093) B329093
theorem B219411 : Blo 215810 219411 := bstep (se 1 (by rfl) ⟨164558, by rfl⟩ : syracuseStep 219411 = 329117) B329117
theorem B219427 : Blo 215810 219427 := bstep (se 1 (by rfl) ⟨164570, by rfl⟩ : syracuseStep 219427 = 329141) B329141
theorem B219443 : Blo 215810 219443 := bstep (se 1 (by rfl) ⟨164582, by rfl⟩ : syracuseStep 219443 = 329165) B329165
theorem B219459 : Blo 215810 219459 := bstep (se 1 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 219459 = 329189) B329189
theorem B219475 : Blo 215810 219475 := bstep (se 1 (by rfl) ⟨164606, by rfl⟩ : syracuseStep 219475 = 329213) B329213
theorem B219491 : Blo 215810 219491 := bstep (se 1 (by rfl) ⟨164618, by rfl⟩ : syracuseStep 219491 = 329237) B329237
theorem B219507 : Blo 215810 219507 := bstep (se 1 (by rfl) ⟨164630, by rfl⟩ : syracuseStep 219507 = 329261) B329261
theorem B219523 : Blo 215810 219523 := bstep (se 1 (by rfl) ⟨164642, by rfl⟩ : syracuseStep 219523 = 329285) B329285
theorem B678289 : Blo 215810 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B219539 : Blo 215810 219539 := bstep (se 1 (by rfl) ⟨164654, by rfl⟩ : syracuseStep 219539 = 329309) B329309
theorem B219555 : Blo 215810 219555 := bstep (se 1 (by rfl) ⟨164666, by rfl⟩ : syracuseStep 219555 = 329333) B329333
theorem B219571 : Blo 215810 219571 := bstep (se 1 (by rfl) ⟨164678, by rfl⟩ : syracuseStep 219571 = 329357) B329357
theorem B219587 : Blo 215810 219587 := bstep (se 1 (by rfl) ⟨164690, by rfl⟩ : syracuseStep 219587 = 329381) B329381
theorem B219603 : Blo 215810 219603 := bstep (se 1 (by rfl) ⟨164702, by rfl⟩ : syracuseStep 219603 = 329405) B329405
theorem B219619 : Blo 215810 219619 := bstep (se 1 (by rfl) ⟨164714, by rfl⟩ : syracuseStep 219619 = 329429) B329429
theorem B219635 : Blo 215810 219635 := bstep (se 1 (by rfl) ⟨164726, by rfl⟩ : syracuseStep 219635 = 329453) B329453
theorem B219651 : Blo 215810 219651 := bstep (se 1 (by rfl) ⟨164738, by rfl⟩ : syracuseStep 219651 = 329477) B329477
theorem B219667 : Blo 215810 219667 := bstep (se 1 (by rfl) ⟨164750, by rfl⟩ : syracuseStep 219667 = 329501) B329501
theorem B219683 : Blo 215810 219683 := bstep (se 1 (by rfl) ⟨164762, by rfl⟩ : syracuseStep 219683 = 329525) B329525
theorem B219699 : Blo 215810 219699 := bstep (se 1 (by rfl) ⟨164774, by rfl⟩ : syracuseStep 219699 = 329549) B329549
theorem B219715 : Blo 215810 219715 := bstep (se 1 (by rfl) ⟨164786, by rfl⟩ : syracuseStep 219715 = 329573) B329573
theorem B219731 : Blo 215810 219731 := bstep (se 1 (by rfl) ⟨164798, by rfl⟩ : syracuseStep 219731 = 329597) B329597
theorem B219747 : Blo 215810 219747 := bstep (se 1 (by rfl) ⟨164810, by rfl⟩ : syracuseStep 219747 = 329621) B329621
theorem B219763 : Blo 215810 219763 := bstep (se 1 (by rfl) ⟨164822, by rfl⟩ : syracuseStep 219763 = 329645) B329645
theorem B219779 : Blo 215810 219779 := bstep (se 1 (by rfl) ⟨164834, by rfl⟩ : syracuseStep 219779 = 329669) B329669
theorem B219795 : Blo 215810 219795 := bstep (se 1 (by rfl) ⟨164846, by rfl⟩ : syracuseStep 219795 = 329693) B329693
theorem B350963 : Blo 215810 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B416593 : Blo 215810 416593 := bstep (se 2 (by rfl) ⟨156222, by rfl⟩ : syracuseStep 416593 = 312445) B312445
theorem B351059 : Blo 215810 351059 := bstep (se 1 (by rfl) ⟨263294, by rfl⟩ : syracuseStep 351059 = 526589) B526589
theorem B1858403 : Blo 215810 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B351091 : Blo 215810 351091 := bstep (se 1 (by rfl) ⟨263318, by rfl⟩ : syracuseStep 351091 = 526637) B526637
theorem B547793 : Blo 215810 547793 := bstep (se 2 (by rfl) ⟨205422, by rfl⟩ : syracuseStep 547793 = 410845) B410845
theorem B547843 : Blo 215810 547843 := bstep (se 1 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 547843 = 821765) B821765
theorem B547985 : Blo 215810 547985 := bstep (se 2 (by rfl) ⟨205494, by rfl⟩ : syracuseStep 547985 = 410989) B410989
theorem B875789 : Blo 215810 875789 := bstep (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) B328421
theorem B1236293 : Blo 215810 1236293 := bstep (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) B231805
theorem B1662605 : Blo 215810 1662605 := bstep (se 3 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 1662605 = 623477) B623477
theorem B1105649 : Blo 215810 1105649 := bstep (se 2 (by rfl) ⟨414618, by rfl⟩ : syracuseStep 1105649 = 829237) B829237
theorem B352001 : Blo 215810 352001 := bstep (se 2 (by rfl) ⟨132000, by rfl⟩ : syracuseStep 352001 = 264001) B264001
theorem B1498915 : Blo 215810 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B1236977 : Blo 215810 1236977 := bstep (se 2 (by rfl) ⟨463866, by rfl⟩ : syracuseStep 1236977 = 927733) B927733
theorem B548977 : Blo 215810 548977 := bstep (se 2 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 548977 = 411733) B411733
theorem B549251 : Blo 215810 549251 := bstep (se 1 (by rfl) ⟨411938, by rfl⟩ : syracuseStep 549251 = 823877) B823877
theorem B2974133 : Blo 215810 2974133 := bstep (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) B278825
theorem B549443 : Blo 215810 549443 := bstep (se 1 (by rfl) ⟨412082, by rfl⟩ : syracuseStep 549443 = 824165) B824165
theorem B2450189 : Blo 215810 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B615185 : Blo 215810 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B1107107 : Blo 215810 1107107 := bstep (se 1 (by rfl) ⟨830330, by rfl⟩ : syracuseStep 1107107 = 1660661) B1660661
theorem B320819 : Blo 215810 320819 := bstep (se 1 (by rfl) ⟨240614, by rfl⟩ : syracuseStep 320819 = 481229) B481229
theorem B1238435 : Blo 215810 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B550385 : Blo 215810 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B550435 : Blo 215810 550435 := bstep (se 1 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 550435 = 825653) B825653
theorem B550577 : Blo 215810 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B583537 : Blo 215810 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B780209 : Blo 215810 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B1107917 : Blo 215810 1107917 := bstep (se 3 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 1107917 = 415469) B415469
theorem B616643 : Blo 215810 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B3532997 : Blo 215810 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B485585 : Blo 215810 485585 := bstep (se 2 (by rfl) ⟨182094, by rfl⟩ : syracuseStep 485585 = 364189) B364189
theorem B485603 : Blo 215810 485603 := bstep (se 1 (by rfl) ⟨364202, by rfl⟩ : syracuseStep 485603 = 728405) B728405
theorem B10414307 : Blo 215810 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B485873 : Blo 215810 485873 := bstep (se 2 (by rfl) ⟨182202, by rfl⟩ : syracuseStep 485873 = 364405) B364405
theorem B1665521 : Blo 215810 1665521 := bstep (se 2 (by rfl) ⟨624570, by rfl⟩ : syracuseStep 1665521 = 1249141) B1249141
theorem B485891 : Blo 215810 485891 := bstep (se 1 (by rfl) ⟨364418, by rfl⟩ : syracuseStep 485891 = 728837) B728837
theorem B551569 : Blo 215810 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B486161 : Blo 215810 486161 := bstep (se 2 (by rfl) ⟨182310, by rfl⟩ : syracuseStep 486161 = 364621) B364621
theorem B486179 : Blo 215810 486179 := bstep (se 1 (by rfl) ⟨364634, by rfl⟩ : syracuseStep 486179 = 729269) B729269
theorem B551843 : Blo 215810 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B617453 : Blo 215810 617453 := bstep (se 3 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 617453 = 231545) B231545
theorem B486449 : Blo 215810 486449 := bstep (se 2 (by rfl) ⟨182418, by rfl⟩ : syracuseStep 486449 = 364837) B364837
theorem B486467 : Blo 215810 486467 := bstep (se 1 (by rfl) ⟨364850, by rfl⟩ : syracuseStep 486467 = 729701) B729701
theorem B552035 : Blo 215810 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B617645 : Blo 215810 617645 := bstep (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) B231617
theorem B519409 : Blo 215810 519409 := bstep (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) B389557
theorem B486737 : Blo 215810 486737 := bstep (se 2 (by rfl) ⟨182526, by rfl⟩ : syracuseStep 486737 = 365053) B365053
theorem B486755 : Blo 215810 486755 := bstep (se 1 (by rfl) ⟨365066, by rfl⟩ : syracuseStep 486755 = 730133) B730133
theorem B519601 : Blo 215810 519601 := bstep (se 2 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 519601 = 389701) B389701
theorem B487025 : Blo 215810 487025 := bstep (se 2 (by rfl) ⟨182634, by rfl⟩ : syracuseStep 487025 = 365269) B365269
theorem B487043 : Blo 215810 487043 := bstep (se 1 (by rfl) ⟨365282, by rfl⟩ : syracuseStep 487043 = 730565) B730565
theorem B749251 : Blo 215810 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B389009 : Blo 215810 389009 := bstep (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) B291757
theorem B487313 : Blo 215810 487313 := bstep (se 2 (by rfl) ⟨182742, by rfl⟩ : syracuseStep 487313 = 365485) B365485
theorem B487331 : Blo 215810 487331 := bstep (se 1 (by rfl) ⟨365498, by rfl⟩ : syracuseStep 487331 = 730997) B730997
theorem B552977 : Blo 215810 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B553027 : Blo 215810 553027 := bstep (se 1 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 553027 = 829541) B829541
theorem B618637 : Blo 215810 618637 := bstep (se 3 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 618637 = 231989) B231989
theorem B323729 : Blo 215810 323729 := bstep (se 2 (by rfl) ⟨121398, by rfl⟩ : syracuseStep 323729 = 242797) B242797
theorem B323747 : Blo 215810 323747 := bstep (se 1 (by rfl) ⟨242810, by rfl⟩ : syracuseStep 323747 = 485621) B485621
theorem B487601 : Blo 215810 487601 := bstep (se 2 (by rfl) ⟨182850, by rfl⟩ : syracuseStep 487601 = 365701) B365701
theorem B323777 : Blo 215810 323777 := bstep (se 2 (by rfl) ⟨121416, by rfl⟩ : syracuseStep 323777 = 242833) B242833
theorem B487619 : Blo 215810 487619 := bstep (se 1 (by rfl) ⟨365714, by rfl⟩ : syracuseStep 487619 = 731429) B731429
theorem B1405133 : Blo 215810 1405133 := bstep (se 3 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 1405133 = 526925) B526925
theorem B553169 : Blo 215810 553169 := bstep (se 2 (by rfl) ⟨207438, by rfl⟩ : syracuseStep 553169 = 414877) B414877
theorem B323795 : Blo 215810 323795 := bstep (se 1 (by rfl) ⟨242846, by rfl⟩ : syracuseStep 323795 = 485693) B485693
theorem B6254819 : Blo 215810 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B323825 : Blo 215810 323825 := bstep (se 2 (by rfl) ⟨121434, by rfl⟩ : syracuseStep 323825 = 242869) B242869
theorem B323843 : Blo 215810 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B323873 : Blo 215810 323873 := bstep (se 2 (by rfl) ⟨121452, by rfl⟩ : syracuseStep 323873 = 242905) B242905
theorem B323891 : Blo 215810 323891 := bstep (se 1 (by rfl) ⟨242918, by rfl⟩ : syracuseStep 323891 = 485837) B485837
theorem B323921 : Blo 215810 323921 := bstep (se 2 (by rfl) ⟨121470, by rfl⟩ : syracuseStep 323921 = 242941) B242941
theorem B323939 : Blo 215810 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B323969 : Blo 215810 323969 := bstep (se 2 (by rfl) ⟨121488, by rfl⟩ : syracuseStep 323969 = 242977) B242977
theorem B323987 : Blo 215810 323987 := bstep (se 1 (by rfl) ⟨242990, by rfl⟩ : syracuseStep 323987 = 485981) B485981
theorem B324017 : Blo 215810 324017 := bstep (se 2 (by rfl) ⟨121506, by rfl⟩ : syracuseStep 324017 = 243013) B243013
theorem B324035 : Blo 215810 324035 := bstep (se 1 (by rfl) ⟨243026, by rfl⟩ : syracuseStep 324035 = 486053) B486053
theorem B487889 : Blo 215810 487889 := bstep (se 2 (by rfl) ⟨182958, by rfl⟩ : syracuseStep 487889 = 365917) B365917
theorem B324065 : Blo 215810 324065 := bstep (se 2 (by rfl) ⟨121524, by rfl⟩ : syracuseStep 324065 = 243049) B243049
theorem B487907 : Blo 215810 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B324083 : Blo 215810 324083 := bstep (se 1 (by rfl) ⟨243062, by rfl⟩ : syracuseStep 324083 = 486125) B486125
theorem B324113 : Blo 215810 324113 := bstep (se 2 (by rfl) ⟨121542, by rfl⟩ : syracuseStep 324113 = 243085) B243085
theorem B324131 : Blo 215810 324131 := bstep (se 1 (by rfl) ⟨243098, by rfl⟩ : syracuseStep 324131 = 486197) B486197
theorem B324161 : Blo 215810 324161 := bstep (se 2 (by rfl) ⟨121560, by rfl⟩ : syracuseStep 324161 = 243121) B243121
theorem B1241669 : Blo 215810 1241669 := bstep (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) B232813
theorem B324179 : Blo 215810 324179 := bstep (se 1 (by rfl) ⟨243134, by rfl⟩ : syracuseStep 324179 = 486269) B486269
theorem B389731 : Blo 215810 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B324209 : Blo 215810 324209 := bstep (se 2 (by rfl) ⟨121578, by rfl⟩ : syracuseStep 324209 = 243157) B243157
theorem B324227 : Blo 215810 324227 := bstep (se 1 (by rfl) ⟨243170, by rfl⟩ : syracuseStep 324227 = 486341) B486341
theorem B324257 : Blo 215810 324257 := bstep (se 2 (by rfl) ⟨121596, by rfl⟩ : syracuseStep 324257 = 243193) B243193
theorem B1176241 : Blo 215810 1176241 := bstep (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) B882181
theorem B324275 : Blo 215810 324275 := bstep (se 1 (by rfl) ⟨243206, by rfl⟩ : syracuseStep 324275 = 486413) B486413
theorem B324305 : Blo 215810 324305 := bstep (se 2 (by rfl) ⟨121614, by rfl⟩ : syracuseStep 324305 = 243229) B243229
theorem B324323 : Blo 215810 324323 := bstep (se 1 (by rfl) ⟨243242, by rfl⟩ : syracuseStep 324323 = 486485) B486485
theorem B488177 : Blo 215810 488177 := bstep (se 2 (by rfl) ⟨183066, by rfl⟩ : syracuseStep 488177 = 366133) B366133
theorem B324353 : Blo 215810 324353 := bstep (se 2 (by rfl) ⟨121632, by rfl⟩ : syracuseStep 324353 = 243265) B243265
theorem B488195 : Blo 215810 488195 := bstep (se 1 (by rfl) ⟨366146, by rfl⟩ : syracuseStep 488195 = 732293) B732293
theorem B1700621 : Blo 215810 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B324371 : Blo 215810 324371 := bstep (se 1 (by rfl) ⟨243278, by rfl⟩ : syracuseStep 324371 = 486557) B486557
theorem B586541 : Blo 215810 586541 := bstep (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) B219953
theorem B324401 : Blo 215810 324401 := bstep (se 2 (by rfl) ⟨121650, by rfl⟩ : syracuseStep 324401 = 243301) B243301
theorem B1110833 : Blo 215810 1110833 := bstep (se 2 (by rfl) ⟨416562, by rfl⟩ : syracuseStep 1110833 = 833125) B833125
theorem B324419 : Blo 215810 324419 := bstep (se 1 (by rfl) ⟨243314, by rfl⟩ : syracuseStep 324419 = 486629) B486629
theorem B324449 : Blo 215810 324449 := bstep (se 2 (by rfl) ⟨121668, by rfl⟩ : syracuseStep 324449 = 243337) B243337
theorem B324467 : Blo 215810 324467 := bstep (se 1 (by rfl) ⟨243350, by rfl⟩ : syracuseStep 324467 = 486701) B486701
theorem B324497 : Blo 215810 324497 := bstep (se 2 (by rfl) ⟨121686, by rfl⟩ : syracuseStep 324497 = 243373) B243373
theorem B324515 : Blo 215810 324515 := bstep (se 1 (by rfl) ⟨243386, by rfl⟩ : syracuseStep 324515 = 486773) B486773
theorem B324545 : Blo 215810 324545 := bstep (se 2 (by rfl) ⟨121704, by rfl⟩ : syracuseStep 324545 = 243409) B243409
theorem B324563 : Blo 215810 324563 := bstep (se 1 (by rfl) ⟨243422, by rfl⟩ : syracuseStep 324563 = 486845) B486845
theorem B291811 : Blo 215810 291811 := bstep (se 1 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 291811 = 437717) B437717
theorem B324593 : Blo 215810 324593 := bstep (se 2 (by rfl) ⟨121722, by rfl⟩ : syracuseStep 324593 = 243445) B243445
theorem B324611 : Blo 215810 324611 := bstep (se 1 (by rfl) ⟨243458, by rfl⟩ : syracuseStep 324611 = 486917) B486917
theorem B1242125 : Blo 215810 1242125 := bstep (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) B465797
theorem B488465 : Blo 215810 488465 := bstep (se 2 (by rfl) ⟨183174, by rfl⟩ : syracuseStep 488465 = 366349) B366349
theorem B324641 : Blo 215810 324641 := bstep (se 2 (by rfl) ⟨121740, by rfl⟩ : syracuseStep 324641 = 243481) B243481
theorem B488483 : Blo 215810 488483 := bstep (se 1 (by rfl) ⟨366362, by rfl⟩ : syracuseStep 488483 = 732725) B732725
theorem B324659 : Blo 215810 324659 := bstep (se 1 (by rfl) ⟨243494, by rfl⟩ : syracuseStep 324659 = 486989) B486989
theorem B324689 : Blo 215810 324689 := bstep (se 2 (by rfl) ⟨121758, by rfl⟩ : syracuseStep 324689 = 243517) B243517
theorem B324707 : Blo 215810 324707 := bstep (se 1 (by rfl) ⟨243530, by rfl⟩ : syracuseStep 324707 = 487061) B487061
theorem B7599217 : Blo 215810 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B324737 : Blo 215810 324737 := bstep (se 2 (by rfl) ⟨121776, by rfl⟩ : syracuseStep 324737 = 243553) B243553
theorem B324755 : Blo 215810 324755 := bstep (se 1 (by rfl) ⟨243566, by rfl⟩ : syracuseStep 324755 = 487133) B487133
theorem B324785 : Blo 215810 324785 := bstep (se 2 (by rfl) ⟨121794, by rfl⟩ : syracuseStep 324785 = 243589) B243589
theorem B554161 : Blo 215810 554161 := bstep (se 2 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 554161 = 415621) B415621
theorem B324803 : Blo 215810 324803 := bstep (se 1 (by rfl) ⟨243602, by rfl⟩ : syracuseStep 324803 = 487205) B487205
theorem B324833 : Blo 215810 324833 := bstep (se 2 (by rfl) ⟨121812, by rfl⟩ : syracuseStep 324833 = 243625) B243625
theorem B1766627 : Blo 215810 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B324851 : Blo 215810 324851 := bstep (se 1 (by rfl) ⟨243638, by rfl⟩ : syracuseStep 324851 = 487277) B487277
theorem B324881 : Blo 215810 324881 := bstep (se 2 (by rfl) ⟨121830, by rfl⟩ : syracuseStep 324881 = 243661) B243661
theorem B324899 : Blo 215810 324899 := bstep (se 1 (by rfl) ⟨243674, by rfl⟩ : syracuseStep 324899 = 487349) B487349
theorem B488753 : Blo 215810 488753 := bstep (se 2 (by rfl) ⟨183282, by rfl⟩ : syracuseStep 488753 = 366565) B366565
theorem B324929 : Blo 215810 324929 := bstep (se 2 (by rfl) ⟨121848, by rfl⟩ : syracuseStep 324929 = 243697) B243697
theorem B488771 : Blo 215810 488771 := bstep (se 1 (by rfl) ⟨366578, by rfl⟩ : syracuseStep 488771 = 733157) B733157
theorem B324947 : Blo 215810 324947 := bstep (se 1 (by rfl) ⟨243710, by rfl⟩ : syracuseStep 324947 = 487421) B487421
theorem B324977 : Blo 215810 324977 := bstep (se 2 (by rfl) ⟨121866, by rfl⟩ : syracuseStep 324977 = 243733) B243733
theorem B324995 : Blo 215810 324995 := bstep (se 1 (by rfl) ⟨243746, by rfl⟩ : syracuseStep 324995 = 487493) B487493
theorem B325025 : Blo 215810 325025 := bstep (se 2 (by rfl) ⟨121884, by rfl⟩ : syracuseStep 325025 = 243769) B243769
theorem B325043 : Blo 215810 325043 := bstep (se 1 (by rfl) ⟨243782, by rfl⟩ : syracuseStep 325043 = 487565) B487565
theorem B554435 : Blo 215810 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B325073 : Blo 215810 325073 := bstep (se 2 (by rfl) ⟨121902, by rfl⟩ : syracuseStep 325073 = 243805) B243805
theorem B325091 : Blo 215810 325091 := bstep (se 1 (by rfl) ⟨243818, by rfl⟩ : syracuseStep 325091 = 487637) B487637
theorem B325121 : Blo 215810 325121 := bstep (se 2 (by rfl) ⟨121920, by rfl⟩ : syracuseStep 325121 = 243841) B243841
theorem B325139 : Blo 215810 325139 := bstep (se 1 (by rfl) ⟨243854, by rfl⟩ : syracuseStep 325139 = 487709) B487709
theorem B325169 : Blo 215810 325169 := bstep (se 2 (by rfl) ⟨121938, by rfl⟩ : syracuseStep 325169 = 243877) B243877
theorem B325187 : Blo 215810 325187 := bstep (se 1 (by rfl) ⟨243890, by rfl⟩ : syracuseStep 325187 = 487781) B487781
theorem B489041 : Blo 215810 489041 := bstep (se 2 (by rfl) ⟨183390, by rfl⟩ : syracuseStep 489041 = 366781) B366781
theorem B325217 : Blo 215810 325217 := bstep (se 2 (by rfl) ⟨121956, by rfl⟩ : syracuseStep 325217 = 243913) B243913
theorem B489059 : Blo 215810 489059 := bstep (se 1 (by rfl) ⟨366794, by rfl⟩ : syracuseStep 489059 = 733589) B733589
theorem B325235 : Blo 215810 325235 := bstep (se 1 (by rfl) ⟨243926, by rfl⟩ : syracuseStep 325235 = 487853) B487853
theorem B554627 : Blo 215810 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B325265 : Blo 215810 325265 := bstep (se 2 (by rfl) ⟨121974, by rfl⟩ : syracuseStep 325265 = 243949) B243949
theorem B325283 : Blo 215810 325283 := bstep (se 1 (by rfl) ⟨243962, by rfl⟩ : syracuseStep 325283 = 487925) B487925
theorem B2815669 : Blo 215810 2815669 := bstep (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) B263969
theorem B325313 : Blo 215810 325313 := bstep (se 2 (by rfl) ⟨121992, by rfl⟩ : syracuseStep 325313 = 243985) B243985
theorem B325331 : Blo 215810 325331 := bstep (se 1 (by rfl) ⟨243998, by rfl⟩ : syracuseStep 325331 = 487997) B487997
theorem B325361 : Blo 215810 325361 := bstep (se 2 (by rfl) ⟨122010, by rfl⟩ : syracuseStep 325361 = 244021) B244021
theorem B325379 : Blo 215810 325379 := bstep (se 1 (by rfl) ⟨244034, by rfl⟩ : syracuseStep 325379 = 488069) B488069
theorem B325409 : Blo 215810 325409 := bstep (se 2 (by rfl) ⟨122028, by rfl⟩ : syracuseStep 325409 = 244057) B244057
theorem B587569 : Blo 215810 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B325427 : Blo 215810 325427 := bstep (se 1 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 325427 = 488141) B488141
theorem B751427 : Blo 215810 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B325457 : Blo 215810 325457 := bstep (se 2 (by rfl) ⟨122046, by rfl⟩ : syracuseStep 325457 = 244093) B244093
theorem B620369 : Blo 215810 620369 := bstep (se 2 (by rfl) ⟨232638, by rfl⟩ : syracuseStep 620369 = 465277) B465277
theorem B325475 : Blo 215810 325475 := bstep (se 1 (by rfl) ⟨244106, by rfl⟩ : syracuseStep 325475 = 488213) B488213
theorem B489329 : Blo 215810 489329 := bstep (se 2 (by rfl) ⟨183498, by rfl⟩ : syracuseStep 489329 = 366997) B366997
theorem B325505 : Blo 215810 325505 := bstep (se 2 (by rfl) ⟨122064, by rfl⟩ : syracuseStep 325505 = 244129) B244129
theorem B391043 : Blo 215810 391043 := bstep (se 1 (by rfl) ⟨293282, by rfl⟩ : syracuseStep 391043 = 586565) B586565
theorem B489347 : Blo 215810 489347 := bstep (se 1 (by rfl) ⟨367010, by rfl⟩ : syracuseStep 489347 = 734021) B734021
theorem B587665 : Blo 215810 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B325523 : Blo 215810 325523 := bstep (se 1 (by rfl) ⟨244142, by rfl⟩ : syracuseStep 325523 = 488285) B488285
theorem B325553 : Blo 215810 325553 := bstep (se 2 (by rfl) ⟨122082, by rfl⟩ : syracuseStep 325553 = 244165) B244165
theorem B325571 : Blo 215810 325571 := bstep (se 1 (by rfl) ⟨244178, by rfl⟩ : syracuseStep 325571 = 488357) B488357
theorem B325601 : Blo 215810 325601 := bstep (se 2 (by rfl) ⟨122100, by rfl⟩ : syracuseStep 325601 = 244201) B244201
theorem B325619 : Blo 215810 325619 := bstep (se 1 (by rfl) ⟨244214, by rfl⟩ : syracuseStep 325619 = 488429) B488429
theorem B325649 : Blo 215810 325649 := bstep (se 2 (by rfl) ⟨122118, by rfl⟩ : syracuseStep 325649 = 244237) B244237
theorem B620561 : Blo 215810 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B325667 : Blo 215810 325667 := bstep (se 1 (by rfl) ⟨244250, by rfl⟩ : syracuseStep 325667 = 488501) B488501
theorem B325697 : Blo 215810 325697 := bstep (se 2 (by rfl) ⟨122136, by rfl⟩ : syracuseStep 325697 = 244273) B244273
theorem B325715 : Blo 215810 325715 := bstep (se 1 (by rfl) ⟨244286, by rfl⟩ : syracuseStep 325715 = 488573) B488573
theorem B325745 : Blo 215810 325745 := bstep (se 2 (by rfl) ⟨122154, by rfl⟩ : syracuseStep 325745 = 244309) B244309
theorem B325763 : Blo 215810 325763 := bstep (se 1 (by rfl) ⟨244322, by rfl⟩ : syracuseStep 325763 = 488645) B488645
theorem B489617 : Blo 215810 489617 := bstep (se 2 (by rfl) ⟨183606, by rfl⟩ : syracuseStep 489617 = 367213) B367213
theorem B325793 : Blo 215810 325793 := bstep (se 2 (by rfl) ⟨122172, by rfl⟩ : syracuseStep 325793 = 244345) B244345
theorem B391331 : Blo 215810 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B489635 : Blo 215810 489635 := bstep (se 1 (by rfl) ⟨367226, by rfl⟩ : syracuseStep 489635 = 734453) B734453
theorem B325811 : Blo 215810 325811 := bstep (se 1 (by rfl) ⟨244358, by rfl⟩ : syracuseStep 325811 = 488717) B488717
theorem B325841 : Blo 215810 325841 := bstep (se 2 (by rfl) ⟨122190, by rfl⟩ : syracuseStep 325841 = 244381) B244381
theorem B325859 : Blo 215810 325859 := bstep (se 1 (by rfl) ⟨244394, by rfl⟩ : syracuseStep 325859 = 488789) B488789
theorem B1112291 : Blo 215810 1112291 := bstep (se 1 (by rfl) ⟨834218, by rfl⟩ : syracuseStep 1112291 = 1668437) B1668437
theorem B325889 : Blo 215810 325889 := bstep (se 2 (by rfl) ⟨122208, by rfl⟩ : syracuseStep 325889 = 244417) B244417
theorem B325907 : Blo 215810 325907 := bstep (se 1 (by rfl) ⟨244430, by rfl⟩ : syracuseStep 325907 = 488861) B488861
theorem B325937 : Blo 215810 325937 := bstep (se 2 (by rfl) ⟨122226, by rfl⟩ : syracuseStep 325937 = 244453) B244453
theorem B2816309 : Blo 215810 2816309 := bstep (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) B264029
theorem B325955 : Blo 215810 325955 := bstep (se 1 (by rfl) ⟨244466, by rfl⟩ : syracuseStep 325955 = 488933) B488933
theorem B325985 : Blo 215810 325985 := bstep (se 2 (by rfl) ⟨122244, by rfl⟩ : syracuseStep 325985 = 244489) B244489
theorem B326003 : Blo 215810 326003 := bstep (se 1 (by rfl) ⟨244502, by rfl⟩ : syracuseStep 326003 = 489005) B489005
theorem B326033 : Blo 215810 326033 := bstep (se 2 (by rfl) ⟨122262, by rfl⟩ : syracuseStep 326033 = 244525) B244525
theorem B326051 : Blo 215810 326051 := bstep (se 1 (by rfl) ⟨244538, by rfl⟩ : syracuseStep 326051 = 489077) B489077
theorem B489905 : Blo 215810 489905 := bstep (se 2 (by rfl) ⟨183714, by rfl⟩ : syracuseStep 489905 = 367429) B367429
theorem B326081 : Blo 215810 326081 := bstep (se 2 (by rfl) ⟨122280, by rfl⟩ : syracuseStep 326081 = 244561) B244561
theorem B489923 : Blo 215810 489923 := bstep (se 1 (by rfl) ⟨367442, by rfl⟩ : syracuseStep 489923 = 734885) B734885
theorem B326099 : Blo 215810 326099 := bstep (se 1 (by rfl) ⟨244574, by rfl⟩ : syracuseStep 326099 = 489149) B489149
theorem B2128355 : Blo 215810 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B326129 : Blo 215810 326129 := bstep (se 2 (by rfl) ⟨122298, by rfl⟩ : syracuseStep 326129 = 244597) B244597
theorem B326147 : Blo 215810 326147 := bstep (se 1 (by rfl) ⟨244610, by rfl⟩ : syracuseStep 326147 = 489221) B489221
theorem B326177 : Blo 215810 326177 := bstep (se 2 (by rfl) ⟨122316, by rfl⟩ : syracuseStep 326177 = 244633) B244633
theorem B555569 : Blo 215810 555569 := bstep (se 2 (by rfl) ⟨208338, by rfl⟩ : syracuseStep 555569 = 416677) B416677
theorem B326195 : Blo 215810 326195 := bstep (se 1 (by rfl) ⟨244646, by rfl⟩ : syracuseStep 326195 = 489293) B489293
theorem B326225 : Blo 215810 326225 := bstep (se 2 (by rfl) ⟨122334, by rfl⟩ : syracuseStep 326225 = 244669) B244669
theorem B326243 : Blo 215810 326243 := bstep (se 1 (by rfl) ⟨244682, by rfl⟩ : syracuseStep 326243 = 489365) B489365
theorem B555619 : Blo 215810 555619 := bstep (se 1 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 555619 = 833429) B833429
theorem B260723 : Blo 215810 260723 := bstep (se 1 (by rfl) ⟨195542, by rfl⟩ : syracuseStep 260723 = 391085) B391085
theorem B326273 : Blo 215810 326273 := bstep (se 2 (by rfl) ⟨122352, by rfl⟩ : syracuseStep 326273 = 244705) B244705
theorem B326291 : Blo 215810 326291 := bstep (se 1 (by rfl) ⟨244718, by rfl⟩ : syracuseStep 326291 = 489437) B489437
theorem B1145507 : Blo 215810 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B326321 : Blo 215810 326321 := bstep (se 2 (by rfl) ⟨122370, by rfl⟩ : syracuseStep 326321 = 244741) B244741
theorem B326339 : Blo 215810 326339 := bstep (se 1 (by rfl) ⟨244754, by rfl⟩ : syracuseStep 326339 = 489509) B489509
theorem B490193 : Blo 215810 490193 := bstep (se 2 (by rfl) ⟨183822, by rfl⟩ : syracuseStep 490193 = 367645) B367645
theorem B326369 : Blo 215810 326369 := bstep (se 2 (by rfl) ⟨122388, by rfl⟩ : syracuseStep 326369 = 244777) B244777
theorem B490211 : Blo 215810 490211 := bstep (se 1 (by rfl) ⟨367658, by rfl⟩ : syracuseStep 490211 = 735317) B735317
theorem B555761 : Blo 215810 555761 := bstep (se 2 (by rfl) ⟨208410, by rfl⟩ : syracuseStep 555761 = 416821) B416821
theorem B326387 : Blo 215810 326387 := bstep (se 1 (by rfl) ⟨244790, by rfl⟩ : syracuseStep 326387 = 489581) B489581
theorem B326417 : Blo 215810 326417 := bstep (se 2 (by rfl) ⟨122406, by rfl⟩ : syracuseStep 326417 = 244813) B244813
theorem B326435 : Blo 215810 326435 := bstep (se 1 (by rfl) ⟨244826, by rfl⟩ : syracuseStep 326435 = 489653) B489653
theorem B326465 : Blo 215810 326465 := bstep (se 2 (by rfl) ⟨122424, by rfl⟩ : syracuseStep 326465 = 244849) B244849
theorem B326483 : Blo 215810 326483 := bstep (se 1 (by rfl) ⟨244862, by rfl⟩ : syracuseStep 326483 = 489725) B489725
theorem B326513 : Blo 215810 326513 := bstep (se 2 (by rfl) ⟨122442, by rfl⟩ : syracuseStep 326513 = 244885) B244885
theorem B326531 : Blo 215810 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B326561 : Blo 215810 326561 := bstep (se 2 (by rfl) ⟨122460, by rfl⟩ : syracuseStep 326561 = 244921) B244921
theorem B326579 : Blo 215810 326579 := bstep (se 1 (by rfl) ⟨244934, by rfl⟩ : syracuseStep 326579 = 489869) B489869
theorem B326609 : Blo 215810 326609 := bstep (se 2 (by rfl) ⟨122478, by rfl⟩ : syracuseStep 326609 = 244957) B244957
theorem B326627 : Blo 215810 326627 := bstep (se 1 (by rfl) ⟨244970, by rfl⟩ : syracuseStep 326627 = 489941) B489941
theorem B523235 : Blo 215810 523235 := bstep (se 1 (by rfl) ⟨392426, by rfl⟩ : syracuseStep 523235 = 784853) B784853
theorem B490481 : Blo 215810 490481 := bstep (se 2 (by rfl) ⟨183930, by rfl⟩ : syracuseStep 490481 = 367861) B367861
theorem B621553 : Blo 215810 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B326657 : Blo 215810 326657 := bstep (se 2 (by rfl) ⟨122496, by rfl⟩ : syracuseStep 326657 = 244993) B244993
theorem B490499 : Blo 215810 490499 := bstep (se 1 (by rfl) ⟨367874, by rfl⟩ : syracuseStep 490499 = 735749) B735749
theorem B326675 : Blo 215810 326675 := bstep (se 1 (by rfl) ⟨245006, by rfl⟩ : syracuseStep 326675 = 490013) B490013
theorem B326705 : Blo 215810 326705 := bstep (se 2 (by rfl) ⟨122514, by rfl⟩ : syracuseStep 326705 = 245029) B245029
theorem B523331 : Blo 215810 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B326723 : Blo 215810 326723 := bstep (se 1 (by rfl) ⟨245042, by rfl⟩ : syracuseStep 326723 = 490085) B490085
theorem B326753 : Blo 215810 326753 := bstep (se 2 (by rfl) ⟨122532, by rfl⟩ : syracuseStep 326753 = 245065) B245065
theorem B326771 : Blo 215810 326771 := bstep (se 1 (by rfl) ⟨245078, by rfl⟩ : syracuseStep 326771 = 490157) B490157
theorem B326801 : Blo 215810 326801 := bstep (se 2 (by rfl) ⟨122550, by rfl⟩ : syracuseStep 326801 = 245101) B245101
theorem B294049 : Blo 215810 294049 := bstep (se 2 (by rfl) ⟨110268, by rfl⟩ : syracuseStep 294049 = 220537) B220537
theorem B326819 : Blo 215810 326819 := bstep (se 1 (by rfl) ⟨245114, by rfl⟩ : syracuseStep 326819 = 490229) B490229
theorem B326849 : Blo 215810 326849 := bstep (se 2 (by rfl) ⟨122568, by rfl⟩ : syracuseStep 326849 = 245137) B245137
theorem B326867 : Blo 215810 326867 := bstep (se 1 (by rfl) ⟨245150, by rfl⟩ : syracuseStep 326867 = 490301) B490301
theorem B326897 : Blo 215810 326897 := bstep (se 2 (by rfl) ⟨122586, by rfl⟩ : syracuseStep 326897 = 245173) B245173
theorem B294131 : Blo 215810 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B523523 : Blo 215810 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B326915 : Blo 215810 326915 := bstep (se 1 (by rfl) ⟨245186, by rfl⟩ : syracuseStep 326915 = 490373) B490373
theorem B621827 : Blo 215810 621827 := bstep (se 1 (by rfl) ⟨466370, by rfl⟩ : syracuseStep 621827 = 932741) B932741
theorem B490769 : Blo 215810 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B326945 : Blo 215810 326945 := bstep (se 2 (by rfl) ⟨122604, by rfl⟩ : syracuseStep 326945 = 245209) B245209
theorem B490787 : Blo 215810 490787 := bstep (se 1 (by rfl) ⟨368090, by rfl⟩ : syracuseStep 490787 = 736181) B736181
theorem B326963 : Blo 215810 326963 := bstep (se 1 (by rfl) ⟨245222, by rfl⟩ : syracuseStep 326963 = 490445) B490445
theorem B326993 : Blo 215810 326993 := bstep (se 2 (by rfl) ⟨122622, by rfl⟩ : syracuseStep 326993 = 245245) B245245
theorem B327011 : Blo 215810 327011 := bstep (se 1 (by rfl) ⟨245258, by rfl⟩ : syracuseStep 327011 = 490517) B490517
theorem B327041 : Blo 215810 327041 := bstep (se 2 (by rfl) ⟨122640, by rfl⟩ : syracuseStep 327041 = 245281) B245281
theorem B327059 : Blo 215810 327059 := bstep (se 1 (by rfl) ⟨245294, by rfl⟩ : syracuseStep 327059 = 490589) B490589
theorem B327089 : Blo 215810 327089 := bstep (se 2 (by rfl) ⟨122658, by rfl⟩ : syracuseStep 327089 = 245317) B245317
theorem B327107 : Blo 215810 327107 := bstep (se 1 (by rfl) ⟨245330, by rfl⟩ : syracuseStep 327107 = 490661) B490661
theorem B622019 : Blo 215810 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B327137 : Blo 215810 327137 := bstep (se 2 (by rfl) ⟨122676, by rfl⟩ : syracuseStep 327137 = 245353) B245353
theorem B327155 : Blo 215810 327155 := bstep (se 1 (by rfl) ⟨245366, by rfl⟩ : syracuseStep 327155 = 490733) B490733
theorem B327185 : Blo 215810 327185 := bstep (se 2 (by rfl) ⟨122694, by rfl⟩ : syracuseStep 327185 = 245389) B245389
theorem B327203 : Blo 215810 327203 := bstep (se 1 (by rfl) ⟨245402, by rfl⟩ : syracuseStep 327203 = 490805) B490805
theorem B491057 : Blo 215810 491057 := bstep (se 2 (by rfl) ⟨184146, by rfl⟩ : syracuseStep 491057 = 368293) B368293
theorem B327233 : Blo 215810 327233 := bstep (se 2 (by rfl) ⟨122712, by rfl⟩ : syracuseStep 327233 = 245425) B245425
theorem B491075 : Blo 215810 491075 := bstep (se 1 (by rfl) ⟨368306, by rfl⟩ : syracuseStep 491075 = 736613) B736613
theorem B327251 : Blo 215810 327251 := bstep (se 1 (by rfl) ⟨245438, by rfl⟩ : syracuseStep 327251 = 490877) B490877
theorem B327281 : Blo 215810 327281 := bstep (se 2 (by rfl) ⟨122730, by rfl⟩ : syracuseStep 327281 = 245461) B245461
theorem B327299 : Blo 215810 327299 := bstep (se 1 (by rfl) ⟨245474, by rfl⟩ : syracuseStep 327299 = 490949) B490949
theorem B327329 : Blo 215810 327329 := bstep (se 2 (by rfl) ⟨122748, by rfl⟩ : syracuseStep 327329 = 245497) B245497
theorem B327347 : Blo 215810 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B327377 : Blo 215810 327377 := bstep (se 2 (by rfl) ⟨122766, by rfl⟩ : syracuseStep 327377 = 245533) B245533
theorem B294611 : Blo 215810 294611 := bstep (se 1 (by rfl) ⟨220958, by rfl⟩ : syracuseStep 294611 = 441917) B441917
theorem B425699 : Blo 215810 425699 := bstep (se 1 (by rfl) ⟨319274, by rfl⟩ : syracuseStep 425699 = 638549) B638549
theorem B327395 : Blo 215810 327395 := bstep (se 1 (by rfl) ⟨245546, by rfl⟩ : syracuseStep 327395 = 491093) B491093
theorem B327425 : Blo 215810 327425 := bstep (se 2 (by rfl) ⟨122784, by rfl⟩ : syracuseStep 327425 = 245569) B245569
theorem B327443 : Blo 215810 327443 := bstep (se 1 (by rfl) ⟨245582, by rfl⟩ : syracuseStep 327443 = 491165) B491165
theorem B5603093 : Blo 215810 5603093 := bstep (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) B262645
theorem B327473 : Blo 215810 327473 := bstep (se 2 (by rfl) ⟨122802, by rfl⟩ : syracuseStep 327473 = 245605) B245605
theorem B327491 : Blo 215810 327491 := bstep (se 1 (by rfl) ⟨245618, by rfl⟩ : syracuseStep 327491 = 491237) B491237
theorem B491345 : Blo 215810 491345 := bstep (se 2 (by rfl) ⟨184254, by rfl⟩ : syracuseStep 491345 = 368509) B368509
theorem B327521 : Blo 215810 327521 := bstep (se 2 (by rfl) ⟨122820, by rfl⟩ : syracuseStep 327521 = 245641) B245641
theorem B491363 : Blo 215810 491363 := bstep (se 1 (by rfl) ⟨368522, by rfl⟩ : syracuseStep 491363 = 737045) B737045
theorem B1245041 : Blo 215810 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B327539 : Blo 215810 327539 := bstep (se 1 (by rfl) ⟨245654, by rfl⟩ : syracuseStep 327539 = 491309) B491309
theorem B524177 : Blo 215810 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B327569 : Blo 215810 327569 := bstep (se 2 (by rfl) ⟨122838, by rfl⟩ : syracuseStep 327569 = 245677) B245677
theorem B327587 : Blo 215810 327587 := bstep (se 1 (by rfl) ⟨245690, by rfl⟩ : syracuseStep 327587 = 491381) B491381
theorem B327617 : Blo 215810 327617 := bstep (se 2 (by rfl) ⟨122856, by rfl⟩ : syracuseStep 327617 = 245713) B245713
theorem B327635 : Blo 215810 327635 := bstep (se 1 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 327635 = 491453) B491453
theorem B327665 : Blo 215810 327665 := bstep (se 2 (by rfl) ⟨122874, by rfl⟩ : syracuseStep 327665 = 245749) B245749
theorem B491543 : Blo 215810 491543 := bstep (se 1 (by rfl) ⟨368657, by rfl⟩ : syracuseStep 491543 = 737315) B737315
theorem B1048621 : Blo 215810 1048621 := bstep (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) B393233
theorem B622657 : Blo 215810 622657 := bstep (se 2 (by rfl) ⟨233496, by rfl⟩ : syracuseStep 622657 = 466993) B466993
theorem B327755 : Blo 215810 327755 := bstep (se 1 (by rfl) ⟨245816, by rfl⟩ : syracuseStep 327755 = 491633) B491633
theorem B327767 : Blo 215810 327767 := bstep (se 1 (by rfl) ⟨245825, by rfl⟩ : syracuseStep 327767 = 491651) B491651
theorem B327833 : Blo 215810 327833 := bstep (se 2 (by rfl) ⟨122937, by rfl⟩ : syracuseStep 327833 = 245875) B245875
theorem B491723 : Blo 215810 491723 := bstep (se 1 (by rfl) ⟨368792, by rfl⟩ : syracuseStep 491723 = 737585) B737585
theorem B491777 : Blo 215810 491777 := bstep (se 2 (by rfl) ⟨184416, by rfl⟩ : syracuseStep 491777 = 368833) B368833
theorem B327947 : Blo 215810 327947 := bstep (se 1 (by rfl) ⟨245960, by rfl⟩ : syracuseStep 327947 = 491921) B491921
theorem B327959 : Blo 215810 327959 := bstep (se 1 (by rfl) ⟨245969, by rfl⟩ : syracuseStep 327959 = 491939) B491939
theorem B328025 : Blo 215810 328025 := bstep (se 2 (by rfl) ⟨123009, by rfl⟩ : syracuseStep 328025 = 246019) B246019
theorem B328139 : Blo 215810 328139 := bstep (se 1 (by rfl) ⟨246104, by rfl⟩ : syracuseStep 328139 = 492209) B492209
theorem B328151 : Blo 215810 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B491993 : Blo 215810 491993 := bstep (se 2 (by rfl) ⟨184497, by rfl⟩ : syracuseStep 491993 = 368995) B368995
theorem B328217 : Blo 215810 328217 := bstep (se 2 (by rfl) ⟨123081, by rfl⟩ : syracuseStep 328217 = 246163) B246163
theorem B492083 : Blo 215810 492083 := bstep (se 1 (by rfl) ⟨369062, by rfl⟩ : syracuseStep 492083 = 738125) B738125
theorem B492119 : Blo 215810 492119 := bstep (se 1 (by rfl) ⟨369089, by rfl⟩ : syracuseStep 492119 = 738179) B738179
theorem B328331 : Blo 215810 328331 := bstep (se 1 (by rfl) ⟨246248, by rfl⟩ : syracuseStep 328331 = 492497) B492497
theorem B328343 : Blo 215810 328343 := bstep (se 1 (by rfl) ⟨246257, by rfl⟩ : syracuseStep 328343 = 492515) B492515
theorem B328409 : Blo 215810 328409 := bstep (se 2 (by rfl) ⟨123153, by rfl⟩ : syracuseStep 328409 = 246307) B246307
theorem B492299 : Blo 215810 492299 := bstep (se 1 (by rfl) ⟨369224, by rfl⟩ : syracuseStep 492299 = 738449) B738449
theorem B492353 : Blo 215810 492353 := bstep (se 2 (by rfl) ⟨184632, by rfl⟩ : syracuseStep 492353 = 369265) B369265
theorem B328523 : Blo 215810 328523 := bstep (se 1 (by rfl) ⟨246392, by rfl⟩ : syracuseStep 328523 = 492785) B492785
theorem B328535 : Blo 215810 328535 := bstep (se 1 (by rfl) ⟨246401, by rfl⟩ : syracuseStep 328535 = 492803) B492803
theorem B328601 : Blo 215810 328601 := bstep (se 2 (by rfl) ⟨123225, by rfl⟩ : syracuseStep 328601 = 246451) B246451
theorem B328715 : Blo 215810 328715 := bstep (se 1 (by rfl) ⟨246536, by rfl⟩ : syracuseStep 328715 = 493073) B493073
theorem B1246225 : Blo 215810 1246225 := bstep (se 2 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 1246225 = 934669) B934669
theorem B328727 : Blo 215810 328727 := bstep (se 1 (by rfl) ⟨246545, by rfl⟩ : syracuseStep 328727 = 493091) B493091
theorem B492569 : Blo 215810 492569 := bstep (se 2 (by rfl) ⟨184713, by rfl⟩ : syracuseStep 492569 = 369427) B369427
theorem B328793 : Blo 215810 328793 := bstep (se 2 (by rfl) ⟨123297, by rfl⟩ : syracuseStep 328793 = 246595) B246595
theorem B492659 : Blo 215810 492659 := bstep (se 1 (by rfl) ⟨369494, by rfl⟩ : syracuseStep 492659 = 738989) B738989
theorem B492695 : Blo 215810 492695 := bstep (se 1 (by rfl) ⟨369521, by rfl⟩ : syracuseStep 492695 = 739043) B739043
theorem B394433 : Blo 215810 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B328907 : Blo 215810 328907 := bstep (se 1 (by rfl) ⟨246680, by rfl⟩ : syracuseStep 328907 = 493361) B493361
theorem B328919 : Blo 215810 328919 := bstep (se 1 (by rfl) ⟨246689, by rfl⟩ : syracuseStep 328919 = 493379) B493379
theorem B230635 : Blo 215810 230635 := bstep (se 1 (by rfl) ⟨172976, by rfl⟩ : syracuseStep 230635 = 345953) B345953
theorem B328985 : Blo 215810 328985 := bstep (se 2 (by rfl) ⟨123369, by rfl⟩ : syracuseStep 328985 = 246739) B246739
theorem B492851 : Blo 215810 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B492875 : Blo 215810 492875 := bstep (se 1 (by rfl) ⟨369656, by rfl⟩ : syracuseStep 492875 = 739313) B739313
theorem B492929 : Blo 215810 492929 := bstep (se 2 (by rfl) ⟨184848, by rfl⟩ : syracuseStep 492929 = 369697) B369697
theorem B329099 : Blo 215810 329099 := bstep (se 1 (by rfl) ⟨246824, by rfl⟩ : syracuseStep 329099 = 493649) B493649
theorem B329111 : Blo 215810 329111 := bstep (se 1 (by rfl) ⟨246833, by rfl⟩ : syracuseStep 329111 = 493667) B493667
theorem B493015 : Blo 215810 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B329177 : Blo 215810 329177 := bstep (se 2 (by rfl) ⟨123441, by rfl⟩ : syracuseStep 329177 = 246883) B246883
theorem B329291 : Blo 215810 329291 := bstep (se 1 (by rfl) ⟨246968, by rfl⟩ : syracuseStep 329291 = 493937) B493937
theorem B329303 : Blo 215810 329303 := bstep (se 1 (by rfl) ⟨246977, by rfl⟩ : syracuseStep 329303 = 493955) B493955
theorem B493145 : Blo 215810 493145 := bstep (se 2 (by rfl) ⟨184929, by rfl⟩ : syracuseStep 493145 = 369859) B369859
theorem B329369 : Blo 215810 329369 := bstep (se 2 (by rfl) ⟨123513, by rfl⟩ : syracuseStep 329369 = 247027) B247027
theorem B493235 : Blo 215810 493235 := bstep (se 1 (by rfl) ⟨369926, by rfl⟩ : syracuseStep 493235 = 739853) B739853
theorem B493271 : Blo 215810 493271 := bstep (se 1 (by rfl) ⟨369953, by rfl⟩ : syracuseStep 493271 = 739907) B739907
theorem B329483 : Blo 215810 329483 := bstep (se 1 (by rfl) ⟨247112, by rfl⟩ : syracuseStep 329483 = 494225) B494225
theorem B329495 : Blo 215810 329495 := bstep (se 1 (by rfl) ⟨247121, by rfl⟩ : syracuseStep 329495 = 494243) B494243
theorem B329561 : Blo 215810 329561 := bstep (se 2 (by rfl) ⟨123585, by rfl⟩ : syracuseStep 329561 = 247171) B247171
theorem B493427 : Blo 215810 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B3508085 : Blo 215810 3508085 := bstep (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) B328883
theorem B493451 : Blo 215810 493451 := bstep (se 1 (by rfl) ⟨370088, by rfl⟩ : syracuseStep 493451 = 740177) B740177
theorem B493505 : Blo 215810 493505 := bstep (se 2 (by rfl) ⟨185064, by rfl⟩ : syracuseStep 493505 = 370129) B370129
theorem B329675 : Blo 215810 329675 := bstep (se 1 (by rfl) ⟨247256, by rfl⟩ : syracuseStep 329675 = 494513) B494513
theorem B329687 : Blo 215810 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B493721 : Blo 215810 493721 := bstep (se 2 (by rfl) ⟨185145, by rfl⟩ : syracuseStep 493721 = 370291) B370291
theorem B460979 : Blo 215810 460979 := bstep (se 1 (by rfl) ⟨345734, by rfl⟩ : syracuseStep 460979 = 691469) B691469
theorem B493811 : Blo 215810 493811 := bstep (se 1 (by rfl) ⟨370358, by rfl⟩ : syracuseStep 493811 = 740717) B740717
theorem B493847 : Blo 215810 493847 := bstep (se 1 (by rfl) ⟨370385, by rfl⟩ : syracuseStep 493847 = 740771) B740771
theorem B526771 : Blo 215810 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B494027 : Blo 215810 494027 := bstep (se 1 (by rfl) ⟨370520, by rfl⟩ : syracuseStep 494027 = 741041) B741041
theorem B494081 : Blo 215810 494081 := bstep (se 2 (by rfl) ⟨185280, by rfl⟩ : syracuseStep 494081 = 370561) B370561
theorem B821933 : Blo 215810 821933 := bstep (se 3 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 821933 = 308225) B308225
theorem B494297 : Blo 215810 494297 := bstep (se 2 (by rfl) ⟨185361, by rfl⟩ : syracuseStep 494297 = 370723) B370723
theorem B1641221 : Blo 215810 1641221 := bstep (se 4 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 1641221 = 307729) B307729
theorem B494387 : Blo 215810 494387 := bstep (se 1 (by rfl) ⟨370790, by rfl⟩ : syracuseStep 494387 = 741581) B741581
theorem B494423 : Blo 215810 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B1182595 : Blo 215810 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B592985 : Blo 215810 592985 := bstep (se 2 (by rfl) ⟨222369, by rfl⟩ : syracuseStep 592985 = 444739) B444739
theorem B461953 : Blo 215810 461953 := bstep (se 2 (by rfl) ⟨173232, by rfl⟩ : syracuseStep 461953 = 346465) B346465
theorem B789911 : Blo 215810 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B822707 : Blo 215810 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B855517 : Blo 215810 855517 := bstep (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) B320819
theorem B364439 : Blo 215810 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B495553 : Blo 215810 495553 := bstep (se 2 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 495553 = 371665) B371665
theorem B364567 : Blo 215810 364567 := bstep (se 1 (by rfl) ⟨273425, by rfl⟩ : syracuseStep 364567 = 546851) B546851
theorem B692545 : Blo 215810 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B1249667 : Blo 215810 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B233975 : Blo 215810 233975 := bstep (se 1 (by rfl) ⟨175481, by rfl⟩ : syracuseStep 233975 = 350963) B350963
theorem B692801 : Blo 215810 692801 := bstep (se 2 (by rfl) ⟨259800, by rfl⟩ : syracuseStep 692801 = 519601) B519601
theorem B332363 : Blo 215810 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B365195 : Blo 215810 365195 := bstep (se 1 (by rfl) ⟨273896, by rfl⟩ : syracuseStep 365195 = 547793) B547793
theorem B365323 : Blo 215810 365323 := bstep (se 1 (by rfl) ⟨273992, by rfl⟩ : syracuseStep 365323 = 547985) B547985
theorem B824195 : Blo 215810 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B365465 : Blo 215810 365465 := bstep (se 2 (by rfl) ⟨137049, by rfl⟩ : syracuseStep 365465 = 274099) B274099
theorem B791569 : Blo 215810 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B365593 : Blo 215810 365593 := bstep (se 2 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 365593 = 274195) B274195
theorem B1643651 : Blo 215810 1643651 := bstep (se 1 (by rfl) ⟨1232738, by rfl⟩ : syracuseStep 1643651 = 2465477) B2465477
theorem B234667 : Blo 215810 234667 := bstep (se 1 (by rfl) ⟨176000, by rfl⟩ : syracuseStep 234667 = 352001) B352001
theorem B464089 : Blo 215810 464089 := bstep (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) B348067
theorem B824651 : Blo 215810 824651 := bstep (se 1 (by rfl) ⟨618488, by rfl⟩ : syracuseStep 824651 = 1236977) B1236977
theorem B824849 : Blo 215810 824849 := bstep (se 2 (by rfl) ⟨309318, by rfl⟩ : syracuseStep 824849 = 618637) B618637
theorem B366167 : Blo 215810 366167 := bstep (se 1 (by rfl) ⟨274625, by rfl⟩ : syracuseStep 366167 = 549251) B549251
theorem B923309 : Blo 215810 923309 := bstep (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) B346241
theorem B366295 : Blo 215810 366295 := bstep (se 1 (by rfl) ⟨274721, by rfl⟩ : syracuseStep 366295 = 549443) B549443
theorem B825623 : Blo 215810 825623 := bstep (se 1 (by rfl) ⟨619217, by rfl⟩ : syracuseStep 825623 = 1238435) B1238435
theorem B366923 : Blo 215810 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B923993 : Blo 215810 923993 := bstep (se 2 (by rfl) ⟨346497, by rfl⟩ : syracuseStep 923993 = 692995) B692995
theorem B367051 : Blo 215810 367051 := bstep (se 1 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 367051 = 550577) B550577
theorem B825821 : Blo 215810 825821 := bstep (se 3 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 825821 = 309683) B309683
theorem B367193 : Blo 215810 367193 := bstep (se 2 (by rfl) ⟨137697, by rfl⟩ : syracuseStep 367193 = 275395) B275395
theorem B4201091 : Blo 215810 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B662195 : Blo 215810 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B367321 : Blo 215810 367321 := bstep (se 2 (by rfl) ⟨137745, by rfl⟩ : syracuseStep 367321 = 275491) B275491
theorem B10132289 : Blo 215810 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B1252313 : Blo 215810 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B695261 : Blo 215810 695261 := bstep (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) B260723
theorem B2497553 : Blo 215810 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B3054685 : Blo 215810 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B1875149 : Blo 215810 1875149 := bstep (se 3 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 1875149 = 703181) B703181
theorem B367895 : Blo 215810 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B466241 : Blo 215810 466241 := bstep (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) B349681
theorem B368023 : Blo 215810 368023 := bstep (se 1 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 368023 = 552035) B552035
theorem B466327 : Blo 215810 466327 := bstep (se 1 (by rfl) ⟨349745, by rfl⟩ : syracuseStep 466327 = 699491) B699491
theorem B728513 : Blo 215810 728513 := bstep (se 2 (by rfl) ⟨273192, by rfl⟩ : syracuseStep 728513 = 546385) B546385
theorem B729053 : Blo 215810 729053 := bstep (se 3 (by rfl) ⟨136697, by rfl⟩ : syracuseStep 729053 = 273395) B273395
theorem B368651 : Blo 215810 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B368779 : Blo 215810 368779 := bstep (se 1 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 368779 = 553169) B553169
theorem B4169879 : Blo 215810 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B467147 : Blo 215810 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B368921 : Blo 215810 368921 := bstep (se 2 (by rfl) ⟨138345, by rfl⟩ : syracuseStep 368921 = 276691) B276691
theorem B827779 : Blo 215810 827779 := bstep (se 1 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 827779 = 1241669) B1241669
theorem B369049 : Blo 215810 369049 := bstep (se 2 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 369049 = 276787) B276787
theorem B1647053 : Blo 215810 1647053 := bstep (se 3 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 1647053 = 617645) B617645
theorem B664129 : Blo 215810 664129 := bstep (se 2 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 664129 = 498097) B498097
theorem B828083 : Blo 215810 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B1581869 : Blo 215810 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B1647539 : Blo 215810 1647539 := bstep (se 1 (by rfl) ⟨1235654, by rfl⟩ : syracuseStep 1647539 = 2471309) B2471309
theorem B369623 : Blo 215810 369623 := bstep (se 1 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 369623 = 554435) B554435
theorem B730187 : Blo 215810 730187 := bstep (se 1 (by rfl) ⟨547640, by rfl⟩ : syracuseStep 730187 = 1095281) B1095281
theorem B369751 : Blo 215810 369751 := bstep (se 1 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 369751 = 554627) B554627
theorem B468121 : Blo 215810 468121 := bstep (se 2 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 468121 = 351091) B351091
theorem B500951 : Blo 215810 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B828737 : Blo 215810 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B730457 : Blo 215810 730457 := bstep (se 2 (by rfl) ⟨273921, by rfl⟩ : syracuseStep 730457 = 547843) B547843
theorem B1877539 : Blo 215810 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B1418903 : Blo 215810 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B927425 : Blo 215810 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B370379 : Blo 215810 370379 := bstep (se 1 (by rfl) ⟨277784, by rfl⟩ : syracuseStep 370379 = 555569) B555569
theorem B370507 : Blo 215810 370507 := bstep (se 1 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 370507 = 555761) B555761
theorem B2500469 : Blo 215810 2500469 := bstep (se 5 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 2500469 = 234419) B234419
theorem B370649 : Blo 215810 370649 := bstep (se 2 (by rfl) ⟨138993, by rfl⟩ : syracuseStep 370649 = 277987) B277987
theorem B731159 : Blo 215810 731159 := bstep (se 1 (by rfl) ⟨548369, by rfl⟩ : syracuseStep 731159 = 1096739) B1096739
theorem B927767 : Blo 215810 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B370777 : Blo 215810 370777 := bstep (se 2 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 370777 = 278083) B278083
theorem B7088309 : Blo 215810 7088309 := bstep (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) B664529
theorem B1648997 : Blo 215810 1648997 := bstep (se 4 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 1648997 = 309187) B309187
theorem B928279 : Blo 215810 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B829997 : Blo 215810 829997 := bstep (se 3 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 829997 = 311249) B311249
theorem B731699 : Blo 215810 731699 := bstep (se 1 (by rfl) ⟨548774, by rfl⟩ : syracuseStep 731699 = 1097549) B1097549
theorem B830027 : Blo 215810 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B731969 : Blo 215810 731969 := bstep (se 2 (by rfl) ⟨274488, by rfl⟩ : syracuseStep 731969 = 548977) B548977
theorem B1649483 : Blo 215810 1649483 := bstep (se 1 (by rfl) ⟨1237112, by rfl⟩ : syracuseStep 1649483 = 2474225) B2474225
theorem B1321859 : Blo 215810 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B928691 : Blo 215810 928691 := bstep (se 1 (by rfl) ⟨696518, by rfl⟩ : syracuseStep 928691 = 1393037) B1393037
theorem B273547 : Blo 215810 273547 := bstep (se 1 (by rfl) ⟨205160, by rfl⟩ : syracuseStep 273547 = 410321) B410321
theorem B830681 : Blo 215810 830681 := bstep (se 2 (by rfl) ⟨311505, by rfl⟩ : syracuseStep 830681 = 623011) B623011
theorem B732509 : Blo 215810 732509 := bstep (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) B274691
theorem B699799 : Blo 215810 699799 := bstep (se 1 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 699799 = 1049699) B1049699
theorem B830999 : Blo 215810 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B1093337 : Blo 215810 1093337 := bstep (se 2 (by rfl) ⟨410001, by rfl⟩ : syracuseStep 1093337 = 820003) B820003
theorem B700235 : Blo 215810 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B929681 : Blo 215810 929681 := bstep (se 2 (by rfl) ⟨348630, by rfl⟩ : syracuseStep 929681 = 697261) B697261
theorem B274519 : Blo 215810 274519 := bstep (se 1 (by rfl) ⟨205889, by rfl⟩ : syracuseStep 274519 = 411779) B411779
theorem B831667 : Blo 215810 831667 := bstep (se 1 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 831667 = 1247501) B1247501
theorem B668083 : Blo 215810 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B733643 : Blo 215810 733643 := bstep (se 1 (by rfl) ⟨550232, by rfl⟩ : syracuseStep 733643 = 1100465) B1100465
theorem B5550605 : Blo 215810 5550605 := bstep (se 3 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 5550605 = 2081477) B2081477
theorem B1684061 : Blo 215810 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B701131 : Blo 215810 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B733913 : Blo 215810 733913 := bstep (se 2 (by rfl) ⟨275217, by rfl⟩ : syracuseStep 733913 = 550435) B550435
theorem B275339 : Blo 215810 275339 := bstep (se 1 (by rfl) ⟨206504, by rfl⟩ : syracuseStep 275339 = 413009) B413009
theorem B2110387 : Blo 215810 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B308299 : Blo 215810 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B242923 : Blo 215810 242923 := bstep (se 1 (by rfl) ⟨182192, by rfl⟩ : syracuseStep 242923 = 364385) B364385
theorem B1094957 : Blo 215810 1094957 := bstep (se 3 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 1094957 = 410609) B410609
theorem B701747 : Blo 215810 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B243031 : Blo 215810 243031 := bstep (se 1 (by rfl) ⟨182273, by rfl⟩ : syracuseStep 243031 = 364547) B364547
theorem B832913 : Blo 215810 832913 := bstep (se 2 (by rfl) ⟨312342, by rfl⟩ : syracuseStep 832913 = 624685) B624685
theorem B734615 : Blo 215810 734615 := bstep (se 1 (by rfl) ⟨550961, by rfl⟩ : syracuseStep 734615 = 1101923) B1101923
theorem B472535 : Blo 215810 472535 := bstep (se 1 (by rfl) ⟨354401, by rfl⟩ : syracuseStep 472535 = 708803) B708803
theorem B243211 : Blo 215810 243211 := bstep (se 1 (by rfl) ⟨182408, by rfl⟩ : syracuseStep 243211 = 364817) B364817
theorem B2668049 : Blo 215810 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B702017 : Blo 215810 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B276043 : Blo 215810 276043 := bstep (se 1 (by rfl) ⟨207032, by rfl⟩ : syracuseStep 276043 = 414065) B414065
theorem B243319 : Blo 215810 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B11417219 : Blo 215810 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B243499 : Blo 215810 243499 := bstep (se 1 (by rfl) ⟨182624, by rfl⟩ : syracuseStep 243499 = 365249) B365249
theorem B276311 : Blo 215810 276311 := bstep (se 1 (by rfl) ⟨207233, by rfl⟩ : syracuseStep 276311 = 414467) B414467
theorem B243607 : Blo 215810 243607 := bstep (se 1 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 243607 = 365411) B365411
theorem B735155 : Blo 215810 735155 := bstep (se 1 (by rfl) ⟨551366, by rfl⟩ : syracuseStep 735155 = 1102733) B1102733
theorem B243787 : Blo 215810 243787 := bstep (se 1 (by rfl) ⟨182840, by rfl⟩ : syracuseStep 243787 = 365681) B365681
theorem B833611 : Blo 215810 833611 := bstep (se 1 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 833611 = 1250417) B1250417
theorem B243895 : Blo 215810 243895 := bstep (se 1 (by rfl) ⟨182921, by rfl⟩ : syracuseStep 243895 = 365843) B365843
theorem B735425 : Blo 215810 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B932057 : Blo 215810 932057 := bstep (se 2 (by rfl) ⟨349521, by rfl⟩ : syracuseStep 932057 = 699043) B699043
theorem B440587 : Blo 215810 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B309529 : Blo 215810 309529 := bstep (se 2 (by rfl) ⟨116073, by rfl⟩ : syracuseStep 309529 = 232147) B232147
theorem B932141 : Blo 215810 932141 := bstep (se 3 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 932141 = 349553) B349553
theorem B833885 : Blo 215810 833885 := bstep (se 3 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 833885 = 312707) B312707
theorem B1325413 : Blo 215810 1325413 := bstep (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) B248515
theorem B244075 : Blo 215810 244075 := bstep (se 1 (by rfl) ⟨183056, by rfl⟩ : syracuseStep 244075 = 366113) B366113
theorem B244183 : Blo 215810 244183 := bstep (se 1 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 244183 = 366275) B366275
theorem B277015 : Blo 215810 277015 := bstep (se 1 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 277015 = 415523) B415523
theorem B4209245 : Blo 215810 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B244363 : Blo 215810 244363 := bstep (se 1 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 244363 = 366545) B366545
theorem B735965 : Blo 215810 735965 := bstep (se 3 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 735965 = 275987) B275987
theorem B244471 : Blo 215810 244471 := bstep (se 1 (by rfl) ⟨183353, by rfl⟩ : syracuseStep 244471 = 366707) B366707
theorem B4733761 : Blo 215810 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B244651 : Blo 215810 244651 := bstep (se 1 (by rfl) ⟨183488, by rfl⟩ : syracuseStep 244651 = 366977) B366977
theorem B244759 : Blo 215810 244759 := bstep (se 1 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 244759 = 367139) B367139
theorem B834583 : Blo 215810 834583 := bstep (se 1 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 834583 = 1251875) B1251875
theorem B375959 : Blo 215810 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B244939 : Blo 215810 244939 := bstep (se 1 (by rfl) ⟨183704, by rfl⟩ : syracuseStep 244939 = 367409) B367409
theorem B245047 : Blo 215810 245047 := bstep (se 1 (by rfl) ⟨183785, by rfl⟩ : syracuseStep 245047 = 367571) B367571
theorem B1555777 : Blo 215810 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B441715 : Blo 215810 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B245227 : Blo 215810 245227 := bstep (se 1 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 245227 = 367841) B367841
theorem B245335 : Blo 215810 245335 := bstep (se 1 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 245335 = 368003) B368003
theorem B999001 : Blo 215810 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B310873 : Blo 215810 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B310987 : Blo 215810 310987 := bstep (se 1 (by rfl) ⟨233240, by rfl⟩ : syracuseStep 310987 = 466481) B466481
theorem B245515 : Blo 215810 245515 := bstep (se 1 (by rfl) ⟨184136, by rfl⟩ : syracuseStep 245515 = 368273) B368273
theorem B737099 : Blo 215810 737099 := bstep (se 1 (by rfl) ⟨552824, by rfl⟩ : syracuseStep 737099 = 1105649) B1105649
theorem B245623 : Blo 215810 245623 := bstep (se 1 (by rfl) ⟨184217, by rfl⟩ : syracuseStep 245623 = 368435) B368435
theorem B245803 : Blo 215810 245803 := bstep (se 1 (by rfl) ⟨184352, by rfl⟩ : syracuseStep 245803 = 368705) B368705
theorem B1654829 : Blo 215810 1654829 := bstep (se 3 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 1654829 = 620561) B620561
theorem B737369 : Blo 215810 737369 := bstep (se 2 (by rfl) ⟨276513, by rfl⟩ : syracuseStep 737369 = 553027) B553027
theorem B245911 : Blo 215810 245911 := bstep (se 1 (by rfl) ⟨184433, by rfl⟩ : syracuseStep 245911 = 368867) B368867
theorem B1851569 : Blo 215810 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1982755 : Blo 215810 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B246091 : Blo 215810 246091 := bstep (se 1 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 246091 = 369137) B369137
theorem B246199 : Blo 215810 246199 := bstep (se 1 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 246199 = 369299) B369299
theorem B377291 : Blo 215810 377291 := bstep (se 1 (by rfl) ⟨282968, by rfl⟩ : syracuseStep 377291 = 565937) B565937
theorem B410123 : Blo 215810 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B836119 : Blo 215810 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B410177 : Blo 215810 410177 := bstep (se 2 (by rfl) ⟨153816, by rfl⟩ : syracuseStep 410177 = 307633) B307633
theorem B442955 : Blo 215810 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B246379 : Blo 215810 246379 := bstep (se 1 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 246379 = 369569) B369569
theorem B246487 : Blo 215810 246487 := bstep (se 1 (by rfl) ⟨184865, by rfl⟩ : syracuseStep 246487 = 369731) B369731
theorem B836369 : Blo 215810 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B738071 : Blo 215810 738071 := bstep (se 1 (by rfl) ⟨553553, by rfl⟩ : syracuseStep 738071 = 1107107) B1107107
theorem B246571 : Blo 215810 246571 := bstep (se 1 (by rfl) ⟨184928, by rfl⟩ : syracuseStep 246571 = 369857) B369857
theorem B1852253 : Blo 215810 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B246667 : Blo 215810 246667 := bstep (se 1 (by rfl) ⟨185000, by rfl⟩ : syracuseStep 246667 = 370001) B370001
theorem B5686193 : Blo 215810 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B246775 : Blo 215810 246775 := bstep (se 1 (by rfl) ⟨185081, by rfl⟩ : syracuseStep 246775 = 370163) B370163
theorem B312331 : Blo 215810 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B1098845 : Blo 215810 1098845 := bstep (se 3 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 1098845 = 412067) B412067
theorem B246955 : Blo 215810 246955 := bstep (se 1 (by rfl) ⟨185216, by rfl⟩ : syracuseStep 246955 = 370433) B370433
theorem B1000669 : Blo 215810 1000669 := bstep (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) B375251
theorem B312599 : Blo 215810 312599 := bstep (se 1 (by rfl) ⟨234449, by rfl⟩ : syracuseStep 312599 = 468899) B468899
theorem B247063 : Blo 215810 247063 := bstep (se 1 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 247063 = 370595) B370595
theorem B738611 : Blo 215810 738611 := bstep (se 1 (by rfl) ⟨553958, by rfl⟩ : syracuseStep 738611 = 1107917) B1107917
theorem B247243 : Blo 215810 247243 := bstep (se 1 (by rfl) ⟨185432, by rfl⟩ : syracuseStep 247243 = 370865) B370865
theorem B411095 : Blo 215810 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B935441 : Blo 215810 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B738881 : Blo 215810 738881 := bstep (se 2 (by rfl) ⟨277080, by rfl⟩ : syracuseStep 738881 = 554161) B554161
theorem B935489 : Blo 215810 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B411635 : Blo 215810 411635 := bstep (se 1 (by rfl) ⟨308726, by rfl⟩ : syracuseStep 411635 = 617453) B617453
theorem B739421 : Blo 215810 739421 := bstep (se 3 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 739421 = 277283) B277283
theorem B1427557 : Blo 215810 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B936157 : Blo 215810 936157 := bstep (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) B351059
theorem B3754225 : Blo 215810 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B412121 : Blo 215810 412121 := bstep (se 2 (by rfl) ⟨154545, by rfl⟩ : syracuseStep 412121 = 309091) B309091
theorem B215819 : Blo 215810 215819 := bstep (se 1 (by rfl) ⟨161864, by rfl⟩ : syracuseStep 215819 = 323729) B323729
theorem B215831 : Blo 215810 215831 := bstep (se 1 (by rfl) ⟨161873, by rfl⟩ : syracuseStep 215831 = 323747) B323747
theorem B215851 : Blo 215810 215851 := bstep (se 1 (by rfl) ⟨161888, by rfl⟩ : syracuseStep 215851 = 323777) B323777
theorem B936755 : Blo 215810 936755 := bstep (se 1 (by rfl) ⟨702566, by rfl⟩ : syracuseStep 936755 = 1405133) B1405133
theorem B215863 : Blo 215810 215863 := bstep (se 1 (by rfl) ⟨161897, by rfl⟩ : syracuseStep 215863 = 323795) B323795
theorem B215883 : Blo 215810 215883 := bstep (se 1 (by rfl) ⟨161912, by rfl⟩ : syracuseStep 215883 = 323825) B323825
theorem B248651 : Blo 215810 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B215895 : Blo 215810 215895 := bstep (se 1 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 215895 = 323843) B323843
theorem B215915 : Blo 215810 215915 := bstep (se 1 (by rfl) ⟨161936, by rfl⟩ : syracuseStep 215915 = 323873) B323873
theorem B215927 : Blo 215810 215927 := bstep (se 1 (by rfl) ⟨161945, by rfl⟩ : syracuseStep 215927 = 323891) B323891
theorem B215947 : Blo 215810 215947 := bstep (se 1 (by rfl) ⟨161960, by rfl⟩ : syracuseStep 215947 = 323921) B323921
theorem B215959 : Blo 215810 215959 := bstep (se 1 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 215959 = 323939) B323939
theorem B215979 : Blo 215810 215979 := bstep (se 1 (by rfl) ⟨161984, by rfl⟩ : syracuseStep 215979 = 323969) B323969
theorem B215991 : Blo 215810 215991 := bstep (se 1 (by rfl) ⟨161993, by rfl⟩ : syracuseStep 215991 = 323987) B323987
theorem B216011 : Blo 215810 216011 := bstep (se 1 (by rfl) ⟨162008, by rfl⟩ : syracuseStep 216011 = 324017) B324017
theorem B216023 : Blo 215810 216023 := bstep (se 1 (by rfl) ⟨162017, by rfl⟩ : syracuseStep 216023 = 324035) B324035
theorem B216043 : Blo 215810 216043 := bstep (se 1 (by rfl) ⟨162032, by rfl⟩ : syracuseStep 216043 = 324065) B324065
theorem B216055 : Blo 215810 216055 := bstep (se 1 (by rfl) ⟨162041, by rfl⟩ : syracuseStep 216055 = 324083) B324083
theorem B216075 : Blo 215810 216075 := bstep (se 1 (by rfl) ⟨162056, by rfl⟩ : syracuseStep 216075 = 324113) B324113
theorem B216087 : Blo 215810 216087 := bstep (se 1 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 216087 = 324131) B324131
theorem B216107 : Blo 215810 216107 := bstep (se 1 (by rfl) ⟨162080, by rfl⟩ : syracuseStep 216107 = 324161) B324161
theorem B216119 : Blo 215810 216119 := bstep (se 1 (by rfl) ⟨162089, by rfl⟩ : syracuseStep 216119 = 324179) B324179
theorem B216139 : Blo 215810 216139 := bstep (se 1 (by rfl) ⟨162104, by rfl⟩ : syracuseStep 216139 = 324209) B324209
theorem B216151 : Blo 215810 216151 := bstep (se 1 (by rfl) ⟨162113, by rfl⟩ : syracuseStep 216151 = 324227) B324227
theorem B216171 : Blo 215810 216171 := bstep (se 1 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 216171 = 324257) B324257
theorem B216183 : Blo 215810 216183 := bstep (se 1 (by rfl) ⟨162137, by rfl⟩ : syracuseStep 216183 = 324275) B324275
theorem B216203 : Blo 215810 216203 := bstep (se 1 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 216203 = 324305) B324305
theorem B216215 : Blo 215810 216215 := bstep (se 1 (by rfl) ⟨162161, by rfl⟩ : syracuseStep 216215 = 324323) B324323
theorem B1100951 : Blo 215810 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B216235 : Blo 215810 216235 := bstep (se 1 (by rfl) ⟨162176, by rfl⟩ : syracuseStep 216235 = 324353) B324353
theorem B1133747 : Blo 215810 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B216247 : Blo 215810 216247 := bstep (se 1 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 216247 = 324371) B324371
theorem B904385 : Blo 215810 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B216267 : Blo 215810 216267 := bstep (se 1 (by rfl) ⟨162200, by rfl⟩ : syracuseStep 216267 = 324401) B324401
theorem B740555 : Blo 215810 740555 := bstep (se 1 (by rfl) ⟨555416, by rfl⟩ : syracuseStep 740555 = 1110833) B1110833
theorem B216279 : Blo 215810 216279 := bstep (se 1 (by rfl) ⟨162209, by rfl⟩ : syracuseStep 216279 = 324419) B324419
theorem B216299 : Blo 215810 216299 := bstep (se 1 (by rfl) ⟨162224, by rfl⟩ : syracuseStep 216299 = 324449) B324449
theorem B216311 : Blo 215810 216311 := bstep (se 1 (by rfl) ⟨162233, by rfl⟩ : syracuseStep 216311 = 324467) B324467
theorem B216331 : Blo 215810 216331 := bstep (se 1 (by rfl) ⟨162248, by rfl⟩ : syracuseStep 216331 = 324497) B324497
theorem B216343 : Blo 215810 216343 := bstep (se 1 (by rfl) ⟨162257, by rfl⟩ : syracuseStep 216343 = 324515) B324515
theorem B216363 : Blo 215810 216363 := bstep (se 1 (by rfl) ⟨162272, by rfl⟩ : syracuseStep 216363 = 324545) B324545
theorem B216375 : Blo 215810 216375 := bstep (se 1 (by rfl) ⟨162281, by rfl⟩ : syracuseStep 216375 = 324563) B324563
theorem B216395 : Blo 215810 216395 := bstep (se 1 (by rfl) ⟨162296, by rfl⟩ : syracuseStep 216395 = 324593) B324593
theorem B216407 : Blo 215810 216407 := bstep (se 1 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 216407 = 324611) B324611
theorem B216427 : Blo 215810 216427 := bstep (se 1 (by rfl) ⟨162320, by rfl⟩ : syracuseStep 216427 = 324641) B324641
theorem B216439 : Blo 215810 216439 := bstep (se 1 (by rfl) ⟨162329, by rfl⟩ : syracuseStep 216439 = 324659) B324659
theorem B216459 : Blo 215810 216459 := bstep (se 1 (by rfl) ⟨162344, by rfl⟩ : syracuseStep 216459 = 324689) B324689
theorem B216471 : Blo 215810 216471 := bstep (se 1 (by rfl) ⟨162353, by rfl⟩ : syracuseStep 216471 = 324707) B324707
theorem B216491 : Blo 215810 216491 := bstep (se 1 (by rfl) ⟨162368, by rfl⟩ : syracuseStep 216491 = 324737) B324737
theorem B216503 : Blo 215810 216503 := bstep (se 1 (by rfl) ⟨162377, by rfl⟩ : syracuseStep 216503 = 324755) B324755
theorem B216523 : Blo 215810 216523 := bstep (se 1 (by rfl) ⟨162392, by rfl⟩ : syracuseStep 216523 = 324785) B324785
theorem B216535 : Blo 215810 216535 := bstep (se 1 (by rfl) ⟨162401, by rfl⟩ : syracuseStep 216535 = 324803) B324803
theorem B740825 : Blo 215810 740825 := bstep (se 2 (by rfl) ⟨277809, by rfl⟩ : syracuseStep 740825 = 555619) B555619
theorem B216555 : Blo 215810 216555 := bstep (se 1 (by rfl) ⟨162416, by rfl⟩ : syracuseStep 216555 = 324833) B324833
theorem B216567 : Blo 215810 216567 := bstep (se 1 (by rfl) ⟨162425, by rfl⟩ : syracuseStep 216567 = 324851) B324851
theorem B216587 : Blo 215810 216587 := bstep (se 1 (by rfl) ⟨162440, by rfl⟩ : syracuseStep 216587 = 324881) B324881
theorem B216599 : Blo 215810 216599 := bstep (se 1 (by rfl) ⟨162449, by rfl⟩ : syracuseStep 216599 = 324899) B324899
theorem B216619 : Blo 215810 216619 := bstep (se 1 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 216619 = 324929) B324929
theorem B216631 : Blo 215810 216631 := bstep (se 1 (by rfl) ⟨162473, by rfl⟩ : syracuseStep 216631 = 324947) B324947
theorem B216651 : Blo 215810 216651 := bstep (se 1 (by rfl) ⟨162488, by rfl⟩ : syracuseStep 216651 = 324977) B324977
theorem B216663 : Blo 215810 216663 := bstep (se 1 (by rfl) ⟨162497, by rfl⟩ : syracuseStep 216663 = 324995) B324995
theorem B216683 : Blo 215810 216683 := bstep (se 1 (by rfl) ⟨162512, by rfl⟩ : syracuseStep 216683 = 325025) B325025
theorem B216695 : Blo 215810 216695 := bstep (se 1 (by rfl) ⟨162521, by rfl⟩ : syracuseStep 216695 = 325043) B325043
theorem B216715 : Blo 215810 216715 := bstep (se 1 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 216715 = 325073) B325073
theorem B216727 : Blo 215810 216727 := bstep (se 1 (by rfl) ⟨162545, by rfl⟩ : syracuseStep 216727 = 325091) B325091
theorem B216747 : Blo 215810 216747 := bstep (se 1 (by rfl) ⟨162560, by rfl⟩ : syracuseStep 216747 = 325121) B325121
theorem B216759 : Blo 215810 216759 := bstep (se 1 (by rfl) ⟨162569, by rfl⟩ : syracuseStep 216759 = 325139) B325139
theorem B216779 : Blo 215810 216779 := bstep (se 1 (by rfl) ⟨162584, by rfl⟩ : syracuseStep 216779 = 325169) B325169
theorem B216791 : Blo 215810 216791 := bstep (se 1 (by rfl) ⟨162593, by rfl⟩ : syracuseStep 216791 = 325187) B325187
theorem B216811 : Blo 215810 216811 := bstep (se 1 (by rfl) ⟨162608, by rfl⟩ : syracuseStep 216811 = 325217) B325217
theorem B216823 : Blo 215810 216823 := bstep (se 1 (by rfl) ⟨162617, by rfl⟩ : syracuseStep 216823 = 325235) B325235
theorem B216843 : Blo 215810 216843 := bstep (se 1 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 216843 = 325265) B325265
theorem B216855 : Blo 215810 216855 := bstep (se 1 (by rfl) ⟨162641, by rfl⟩ : syracuseStep 216855 = 325283) B325283
theorem B216875 : Blo 215810 216875 := bstep (se 1 (by rfl) ⟨162656, by rfl⟩ : syracuseStep 216875 = 325313) B325313
theorem B1265453 : Blo 215810 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B216887 : Blo 215810 216887 := bstep (se 1 (by rfl) ⟨162665, by rfl⟩ : syracuseStep 216887 = 325331) B325331
theorem B216907 : Blo 215810 216907 := bstep (se 1 (by rfl) ⟨162680, by rfl⟩ : syracuseStep 216907 = 325361) B325361
theorem B216919 : Blo 215810 216919 := bstep (se 1 (by rfl) ⟨162689, by rfl⟩ : syracuseStep 216919 = 325379) B325379
theorem B1658717 : Blo 215810 1658717 := bstep (se 3 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 1658717 = 622019) B622019
theorem B216939 : Blo 215810 216939 := bstep (se 1 (by rfl) ⟨162704, by rfl⟩ : syracuseStep 216939 = 325409) B325409
theorem B216951 : Blo 215810 216951 := bstep (se 1 (by rfl) ⟨162713, by rfl⟩ : syracuseStep 216951 = 325427) B325427
theorem B839555 : Blo 215810 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B216971 : Blo 215810 216971 := bstep (se 1 (by rfl) ⟨162728, by rfl⟩ : syracuseStep 216971 = 325457) B325457
theorem B413579 : Blo 215810 413579 := bstep (se 1 (by rfl) ⟨310184, by rfl⟩ : syracuseStep 413579 = 620369) B620369
theorem B216983 : Blo 215810 216983 := bstep (se 1 (by rfl) ⟨162737, by rfl⟩ : syracuseStep 216983 = 325475) B325475
theorem B217003 : Blo 215810 217003 := bstep (se 1 (by rfl) ⟨162752, by rfl⟩ : syracuseStep 217003 = 325505) B325505
theorem B217015 : Blo 215810 217015 := bstep (se 1 (by rfl) ⟨162761, by rfl⟩ : syracuseStep 217015 = 325523) B325523
theorem B217035 : Blo 215810 217035 := bstep (se 1 (by rfl) ⟨162776, by rfl⟩ : syracuseStep 217035 = 325553) B325553
theorem B217047 : Blo 215810 217047 := bstep (se 1 (by rfl) ⟨162785, by rfl⟩ : syracuseStep 217047 = 325571) B325571
theorem B217067 : Blo 215810 217067 := bstep (se 1 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 217067 = 325601) B325601
theorem B217079 : Blo 215810 217079 := bstep (se 1 (by rfl) ⟨162809, by rfl⟩ : syracuseStep 217079 = 325619) B325619
theorem B217099 : Blo 215810 217099 := bstep (se 1 (by rfl) ⟨162824, by rfl⟩ : syracuseStep 217099 = 325649) B325649
theorem B217111 : Blo 215810 217111 := bstep (se 1 (by rfl) ⟨162833, by rfl⟩ : syracuseStep 217111 = 325667) B325667
theorem B217131 : Blo 215810 217131 := bstep (se 1 (by rfl) ⟨162848, by rfl⟩ : syracuseStep 217131 = 325697) B325697
theorem B217143 : Blo 215810 217143 := bstep (se 1 (by rfl) ⟨162857, by rfl⟩ : syracuseStep 217143 = 325715) B325715
theorem B413761 : Blo 215810 413761 := bstep (se 2 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 413761 = 310321) B310321
theorem B217163 : Blo 215810 217163 := bstep (se 1 (by rfl) ⟨162872, by rfl⟩ : syracuseStep 217163 = 325745) B325745
theorem B217175 : Blo 215810 217175 := bstep (se 1 (by rfl) ⟨162881, by rfl⟩ : syracuseStep 217175 = 325763) B325763
theorem B217195 : Blo 215810 217195 := bstep (se 1 (by rfl) ⟨162896, by rfl⟩ : syracuseStep 217195 = 325793) B325793
theorem B217207 : Blo 215810 217207 := bstep (se 1 (by rfl) ⟨162905, by rfl⟩ : syracuseStep 217207 = 325811) B325811
theorem B217227 : Blo 215810 217227 := bstep (se 1 (by rfl) ⟨162920, by rfl⟩ : syracuseStep 217227 = 325841) B325841
theorem B217239 : Blo 215810 217239 := bstep (se 1 (by rfl) ⟨162929, by rfl⟩ : syracuseStep 217239 = 325859) B325859
theorem B741527 : Blo 215810 741527 := bstep (se 1 (by rfl) ⟨556145, by rfl⟩ : syracuseStep 741527 = 1112291) B1112291
theorem B217259 : Blo 215810 217259 := bstep (se 1 (by rfl) ⟨162944, by rfl⟩ : syracuseStep 217259 = 325889) B325889
theorem B217271 : Blo 215810 217271 := bstep (se 1 (by rfl) ⟨162953, by rfl⟩ : syracuseStep 217271 = 325907) B325907
theorem B217291 : Blo 215810 217291 := bstep (se 1 (by rfl) ⟨162968, by rfl⟩ : syracuseStep 217291 = 325937) B325937
theorem B217303 : Blo 215810 217303 := bstep (se 1 (by rfl) ⟨162977, by rfl⟩ : syracuseStep 217303 = 325955) B325955
theorem B217323 : Blo 215810 217323 := bstep (se 1 (by rfl) ⟨162992, by rfl⟩ : syracuseStep 217323 = 325985) B325985
theorem B217335 : Blo 215810 217335 := bstep (se 1 (by rfl) ⟨163001, by rfl⟩ : syracuseStep 217335 = 326003) B326003
theorem B4837637 : Blo 215810 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B217355 : Blo 215810 217355 := bstep (se 1 (by rfl) ⟨163016, by rfl⟩ : syracuseStep 217355 = 326033) B326033
theorem B217367 : Blo 215810 217367 := bstep (se 1 (by rfl) ⟨163025, by rfl⟩ : syracuseStep 217367 = 326051) B326051
theorem B217387 : Blo 215810 217387 := bstep (se 1 (by rfl) ⟨163040, by rfl⟩ : syracuseStep 217387 = 326081) B326081
theorem B217399 : Blo 215810 217399 := bstep (se 1 (by rfl) ⟨163049, by rfl⟩ : syracuseStep 217399 = 326099) B326099
theorem B217419 : Blo 215810 217419 := bstep (se 1 (by rfl) ⟨163064, by rfl⟩ : syracuseStep 217419 = 326129) B326129
theorem B217431 : Blo 215810 217431 := bstep (se 1 (by rfl) ⟨163073, by rfl⟩ : syracuseStep 217431 = 326147) B326147
theorem B217451 : Blo 215810 217451 := bstep (se 1 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 217451 = 326177) B326177
theorem B217463 : Blo 215810 217463 := bstep (se 1 (by rfl) ⟨163097, by rfl⟩ : syracuseStep 217463 = 326195) B326195
theorem B217483 : Blo 215810 217483 := bstep (se 1 (by rfl) ⟨163112, by rfl⟩ : syracuseStep 217483 = 326225) B326225
theorem B217495 : Blo 215810 217495 := bstep (se 1 (by rfl) ⟨163121, by rfl⟩ : syracuseStep 217495 = 326243) B326243
theorem B217515 : Blo 215810 217515 := bstep (se 1 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 217515 = 326273) B326273
theorem B217527 : Blo 215810 217527 := bstep (se 1 (by rfl) ⟨163145, by rfl⟩ : syracuseStep 217527 = 326291) B326291
theorem B217547 : Blo 215810 217547 := bstep (se 1 (by rfl) ⟨163160, by rfl⟩ : syracuseStep 217547 = 326321) B326321
theorem B217559 : Blo 215810 217559 := bstep (se 1 (by rfl) ⟨163169, by rfl⟩ : syracuseStep 217559 = 326339) B326339
theorem B217579 : Blo 215810 217579 := bstep (se 1 (by rfl) ⟨163184, by rfl⟩ : syracuseStep 217579 = 326369) B326369
theorem B217591 : Blo 215810 217591 := bstep (se 1 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 217591 = 326387) B326387
theorem B414209 : Blo 215810 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B217611 : Blo 215810 217611 := bstep (se 1 (by rfl) ⟨163208, by rfl⟩ : syracuseStep 217611 = 326417) B326417
theorem B217623 : Blo 215810 217623 := bstep (se 1 (by rfl) ⟨163217, by rfl⟩ : syracuseStep 217623 = 326435) B326435
theorem B217643 : Blo 215810 217643 := bstep (se 1 (by rfl) ⟨163232, by rfl⟩ : syracuseStep 217643 = 326465) B326465
theorem B217655 : Blo 215810 217655 := bstep (se 1 (by rfl) ⟨163241, by rfl⟩ : syracuseStep 217655 = 326483) B326483
theorem B217675 : Blo 215810 217675 := bstep (se 1 (by rfl) ⟨163256, by rfl⟩ : syracuseStep 217675 = 326513) B326513
theorem B217687 : Blo 215810 217687 := bstep (se 1 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 217687 = 326531) B326531
theorem B217707 : Blo 215810 217707 := bstep (se 1 (by rfl) ⟨163280, by rfl⟩ : syracuseStep 217707 = 326561) B326561
theorem B217719 : Blo 215810 217719 := bstep (se 1 (by rfl) ⟨163289, by rfl⟩ : syracuseStep 217719 = 326579) B326579
theorem B217739 : Blo 215810 217739 := bstep (se 1 (by rfl) ⟨163304, by rfl⟩ : syracuseStep 217739 = 326609) B326609
theorem B217751 : Blo 215810 217751 := bstep (se 1 (by rfl) ⟨163313, by rfl⟩ : syracuseStep 217751 = 326627) B326627
theorem B348823 : Blo 215810 348823 := bstep (se 1 (by rfl) ⟨261617, by rfl⟩ : syracuseStep 348823 = 523235) B523235
theorem B217771 : Blo 215810 217771 := bstep (se 1 (by rfl) ⟨163328, by rfl⟩ : syracuseStep 217771 = 326657) B326657
theorem B217783 : Blo 215810 217783 := bstep (se 1 (by rfl) ⟨163337, by rfl⟩ : syracuseStep 217783 = 326675) B326675
theorem B217803 : Blo 215810 217803 := bstep (se 1 (by rfl) ⟨163352, by rfl⟩ : syracuseStep 217803 = 326705) B326705
theorem B348887 : Blo 215810 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B217815 : Blo 215810 217815 := bstep (se 1 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 217815 = 326723) B326723
theorem B217835 : Blo 215810 217835 := bstep (se 1 (by rfl) ⟨163376, by rfl⟩ : syracuseStep 217835 = 326753) B326753
theorem B217847 : Blo 215810 217847 := bstep (se 1 (by rfl) ⟨163385, by rfl⟩ : syracuseStep 217847 = 326771) B326771
theorem B3134213 : Blo 215810 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B217867 : Blo 215810 217867 := bstep (se 1 (by rfl) ⟨163400, by rfl⟩ : syracuseStep 217867 = 326801) B326801
theorem B217879 : Blo 215810 217879 := bstep (se 1 (by rfl) ⟨163409, by rfl⟩ : syracuseStep 217879 = 326819) B326819
theorem B217899 : Blo 215810 217899 := bstep (se 1 (by rfl) ⟨163424, by rfl⟩ : syracuseStep 217899 = 326849) B326849
theorem B217911 : Blo 215810 217911 := bstep (se 1 (by rfl) ⟨163433, by rfl⟩ : syracuseStep 217911 = 326867) B326867
theorem B217931 : Blo 215810 217931 := bstep (se 1 (by rfl) ⟨163448, by rfl⟩ : syracuseStep 217931 = 326897) B326897
theorem B349015 : Blo 215810 349015 := bstep (se 1 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 349015 = 523523) B523523
theorem B217943 : Blo 215810 217943 := bstep (se 1 (by rfl) ⟨163457, by rfl⟩ : syracuseStep 217943 = 326915) B326915
theorem B414551 : Blo 215810 414551 := bstep (se 1 (by rfl) ⟨310913, by rfl⟩ : syracuseStep 414551 = 621827) B621827
theorem B217963 : Blo 215810 217963 := bstep (se 1 (by rfl) ⟨163472, by rfl⟩ : syracuseStep 217963 = 326945) B326945
theorem B217975 : Blo 215810 217975 := bstep (se 1 (by rfl) ⟨163481, by rfl⟩ : syracuseStep 217975 = 326963) B326963
theorem B217995 : Blo 215810 217995 := bstep (se 1 (by rfl) ⟨163496, by rfl⟩ : syracuseStep 217995 = 326993) B326993
theorem B218007 : Blo 215810 218007 := bstep (se 1 (by rfl) ⟨163505, by rfl⟩ : syracuseStep 218007 = 327011) B327011
theorem B218027 : Blo 215810 218027 := bstep (se 1 (by rfl) ⟨163520, by rfl⟩ : syracuseStep 218027 = 327041) B327041
theorem B218039 : Blo 215810 218039 := bstep (se 1 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 218039 = 327059) B327059
theorem B218059 : Blo 215810 218059 := bstep (se 1 (by rfl) ⟨163544, by rfl⟩ : syracuseStep 218059 = 327089) B327089
theorem B218071 : Blo 215810 218071 := bstep (se 1 (by rfl) ⟨163553, by rfl⟩ : syracuseStep 218071 = 327107) B327107
theorem B218091 : Blo 215810 218091 := bstep (se 1 (by rfl) ⟨163568, by rfl⟩ : syracuseStep 218091 = 327137) B327137
theorem B218103 : Blo 215810 218103 := bstep (se 1 (by rfl) ⟨163577, by rfl⟩ : syracuseStep 218103 = 327155) B327155
theorem B218123 : Blo 215810 218123 := bstep (se 1 (by rfl) ⟨163592, by rfl⟩ : syracuseStep 218123 = 327185) B327185
theorem B218135 : Blo 215810 218135 := bstep (se 1 (by rfl) ⟨163601, by rfl⟩ : syracuseStep 218135 = 327203) B327203
theorem B218155 : Blo 215810 218155 := bstep (se 1 (by rfl) ⟨163616, by rfl⟩ : syracuseStep 218155 = 327233) B327233
theorem B1037357 : Blo 215810 1037357 := bstep (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) B389009
theorem B218167 : Blo 215810 218167 := bstep (se 1 (by rfl) ⟨163625, by rfl⟩ : syracuseStep 218167 = 327251) B327251
theorem B218187 : Blo 215810 218187 := bstep (se 1 (by rfl) ⟨163640, by rfl⟩ : syracuseStep 218187 = 327281) B327281
theorem B218199 : Blo 215810 218199 := bstep (se 1 (by rfl) ⟨163649, by rfl⟩ : syracuseStep 218199 = 327299) B327299
theorem B218219 : Blo 215810 218219 := bstep (se 1 (by rfl) ⟨163664, by rfl⟩ : syracuseStep 218219 = 327329) B327329
theorem B218231 : Blo 215810 218231 := bstep (se 1 (by rfl) ⟨163673, by rfl⟩ : syracuseStep 218231 = 327347) B327347
theorem B218251 : Blo 215810 218251 := bstep (se 1 (by rfl) ⟨163688, by rfl⟩ : syracuseStep 218251 = 327377) B327377
theorem B283799 : Blo 215810 283799 := bstep (se 1 (by rfl) ⟨212849, by rfl⟩ : syracuseStep 283799 = 425699) B425699
theorem B218263 : Blo 215810 218263 := bstep (se 1 (by rfl) ⟨163697, by rfl⟩ : syracuseStep 218263 = 327395) B327395
theorem B218283 : Blo 215810 218283 := bstep (se 1 (by rfl) ⟨163712, by rfl⟩ : syracuseStep 218283 = 327425) B327425
theorem B218295 : Blo 215810 218295 := bstep (se 1 (by rfl) ⟨163721, by rfl⟩ : syracuseStep 218295 = 327443) B327443
theorem B218315 : Blo 215810 218315 := bstep (se 1 (by rfl) ⟨163736, by rfl⟩ : syracuseStep 218315 = 327473) B327473
theorem B218327 : Blo 215810 218327 := bstep (se 1 (by rfl) ⟨163745, by rfl⟩ : syracuseStep 218327 = 327491) B327491
theorem B218347 : Blo 215810 218347 := bstep (se 1 (by rfl) ⟨163760, by rfl⟩ : syracuseStep 218347 = 327521) B327521
theorem B218359 : Blo 215810 218359 := bstep (se 1 (by rfl) ⟨163769, by rfl⟩ : syracuseStep 218359 = 327539) B327539
theorem B349451 : Blo 215810 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B218379 : Blo 215810 218379 := bstep (se 1 (by rfl) ⟨163784, by rfl⟩ : syracuseStep 218379 = 327569) B327569
theorem B218391 : Blo 215810 218391 := bstep (se 1 (by rfl) ⟨163793, by rfl⟩ : syracuseStep 218391 = 327587) B327587
theorem B218411 : Blo 215810 218411 := bstep (se 1 (by rfl) ⟨163808, by rfl⟩ : syracuseStep 218411 = 327617) B327617
theorem B218423 : Blo 215810 218423 := bstep (se 1 (by rfl) ⟨163817, by rfl⟩ : syracuseStep 218423 = 327635) B327635
theorem B218443 : Blo 215810 218443 := bstep (se 1 (by rfl) ⟨163832, by rfl⟩ : syracuseStep 218443 = 327665) B327665
theorem B218455 : Blo 215810 218455 := bstep (se 1 (by rfl) ⟨163841, by rfl⟩ : syracuseStep 218455 = 327683) B327683
theorem B218475 : Blo 215810 218475 := bstep (se 1 (by rfl) ⟨163856, by rfl⟩ : syracuseStep 218475 = 327713) B327713
theorem B218487 : Blo 215810 218487 := bstep (se 1 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 218487 = 327731) B327731
theorem B218507 : Blo 215810 218507 := bstep (se 1 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 218507 = 327761) B327761
theorem B218519 : Blo 215810 218519 := bstep (se 1 (by rfl) ⟨163889, by rfl⟩ : syracuseStep 218519 = 327779) B327779
theorem B710039 : Blo 215810 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B218539 : Blo 215810 218539 := bstep (se 1 (by rfl) ⟨163904, by rfl⟩ : syracuseStep 218539 = 327809) B327809
theorem B218551 : Blo 215810 218551 := bstep (se 1 (by rfl) ⟨163913, by rfl⟩ : syracuseStep 218551 = 327827) B327827
theorem B349643 : Blo 215810 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B218571 : Blo 215810 218571 := bstep (se 1 (by rfl) ⟨163928, by rfl⟩ : syracuseStep 218571 = 327857) B327857
theorem B218583 : Blo 215810 218583 := bstep (se 1 (by rfl) ⟨163937, by rfl⟩ : syracuseStep 218583 = 327875) B327875
theorem B26891747 : Blo 215810 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B218603 : Blo 215810 218603 := bstep (se 1 (by rfl) ⟨163952, by rfl⟩ : syracuseStep 218603 = 327905) B327905
theorem B415219 : Blo 215810 415219 := bstep (se 1 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 415219 = 622829) B622829
theorem B218615 : Blo 215810 218615 := bstep (se 1 (by rfl) ⟨163961, by rfl⟩ : syracuseStep 218615 = 327923) B327923
theorem B218635 : Blo 215810 218635 := bstep (se 1 (by rfl) ⟨163976, by rfl⟩ : syracuseStep 218635 = 327953) B327953
theorem B218647 : Blo 215810 218647 := bstep (se 1 (by rfl) ⟨163985, by rfl⟩ : syracuseStep 218647 = 327971) B327971
theorem B218667 : Blo 215810 218667 := bstep (se 1 (by rfl) ⟨164000, by rfl⟩ : syracuseStep 218667 = 328001) B328001
theorem B218679 : Blo 215810 218679 := bstep (se 1 (by rfl) ⟨164009, by rfl⟩ : syracuseStep 218679 = 328019) B328019
theorem B218699 : Blo 215810 218699 := bstep (se 1 (by rfl) ⟨164024, by rfl⟩ : syracuseStep 218699 = 328049) B328049
theorem B218711 : Blo 215810 218711 := bstep (se 1 (by rfl) ⟨164033, by rfl⟩ : syracuseStep 218711 = 328067) B328067
theorem B218731 : Blo 215810 218731 := bstep (se 1 (by rfl) ⟨164048, by rfl⟩ : syracuseStep 218731 = 328097) B328097
theorem B218743 : Blo 215810 218743 := bstep (se 1 (by rfl) ⟨164057, by rfl⟩ : syracuseStep 218743 = 328115) B328115
theorem B218763 : Blo 215810 218763 := bstep (se 1 (by rfl) ⟨164072, by rfl⟩ : syracuseStep 218763 = 328145) B328145
theorem B218775 : Blo 215810 218775 := bstep (se 1 (by rfl) ⟨164081, by rfl⟩ : syracuseStep 218775 = 328163) B328163
theorem B218795 : Blo 215810 218795 := bstep (se 1 (by rfl) ⟨164096, by rfl⟩ : syracuseStep 218795 = 328193) B328193
theorem B218807 : Blo 215810 218807 := bstep (se 1 (by rfl) ⟨164105, by rfl⟩ : syracuseStep 218807 = 328211) B328211
theorem B546497 : Blo 215810 546497 := bstep (se 2 (by rfl) ⟨204936, by rfl⟩ : syracuseStep 546497 = 409873) B409873
theorem B218827 : Blo 215810 218827 := bstep (se 1 (by rfl) ⟨164120, by rfl⟩ : syracuseStep 218827 = 328241) B328241
theorem B218839 : Blo 215810 218839 := bstep (se 1 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 218839 = 328259) B328259
theorem B218859 : Blo 215810 218859 := bstep (se 1 (by rfl) ⟨164144, by rfl⟩ : syracuseStep 218859 = 328289) B328289
theorem B218871 : Blo 215810 218871 := bstep (se 1 (by rfl) ⟨164153, by rfl⟩ : syracuseStep 218871 = 328307) B328307
theorem B218891 : Blo 215810 218891 := bstep (se 1 (by rfl) ⟨164168, by rfl⟩ : syracuseStep 218891 = 328337) B328337
theorem B218903 : Blo 215810 218903 := bstep (se 1 (by rfl) ⟨164177, by rfl⟩ : syracuseStep 218903 = 328355) B328355
theorem B218923 : Blo 215810 218923 := bstep (se 1 (by rfl) ⟨164192, by rfl⟩ : syracuseStep 218923 = 328385) B328385
theorem B218935 : Blo 215810 218935 := bstep (se 1 (by rfl) ⟨164201, by rfl⟩ : syracuseStep 218935 = 328403) B328403
theorem B218955 : Blo 215810 218955 := bstep (se 1 (by rfl) ⟨164216, by rfl⟩ : syracuseStep 218955 = 328433) B328433
theorem B218967 : Blo 215810 218967 := bstep (se 1 (by rfl) ⟨164225, by rfl⟩ : syracuseStep 218967 = 328451) B328451
theorem B218987 : Blo 215810 218987 := bstep (se 1 (by rfl) ⟨164240, by rfl⟩ : syracuseStep 218987 = 328481) B328481
theorem B218999 : Blo 215810 218999 := bstep (se 1 (by rfl) ⟨164249, by rfl⟩ : syracuseStep 218999 = 328499) B328499
theorem B219019 : Blo 215810 219019 := bstep (se 1 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 219019 = 328529) B328529
theorem B219031 : Blo 215810 219031 := bstep (se 1 (by rfl) ⟨164273, by rfl⟩ : syracuseStep 219031 = 328547) B328547
theorem B219051 : Blo 215810 219051 := bstep (se 1 (by rfl) ⟨164288, by rfl⟩ : syracuseStep 219051 = 328577) B328577
theorem B415667 : Blo 215810 415667 := bstep (se 1 (by rfl) ⟨311750, by rfl⟩ : syracuseStep 415667 = 623501) B623501
theorem B219063 : Blo 215810 219063 := bstep (se 1 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 219063 = 328595) B328595
theorem B219083 : Blo 215810 219083 := bstep (se 1 (by rfl) ⟨164312, by rfl⟩ : syracuseStep 219083 = 328625) B328625
theorem B219095 : Blo 215810 219095 := bstep (se 1 (by rfl) ⟨164321, by rfl⟩ : syracuseStep 219095 = 328643) B328643
theorem B415705 : Blo 215810 415705 := bstep (se 2 (by rfl) ⟨155889, by rfl⟩ : syracuseStep 415705 = 311779) B311779
theorem B219115 : Blo 215810 219115 := bstep (se 1 (by rfl) ⟨164336, by rfl⟩ : syracuseStep 219115 = 328673) B328673
theorem B219127 : Blo 215810 219127 := bstep (se 1 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 219127 = 328691) B328691
theorem B219147 : Blo 215810 219147 := bstep (se 1 (by rfl) ⟨164360, by rfl⟩ : syracuseStep 219147 = 328721) B328721
theorem B219159 : Blo 215810 219159 := bstep (se 1 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 219159 = 328739) B328739
theorem B219179 : Blo 215810 219179 := bstep (se 1 (by rfl) ⟨164384, by rfl⟩ : syracuseStep 219179 = 328769) B328769
theorem B219191 : Blo 215810 219191 := bstep (se 1 (by rfl) ⟨164393, by rfl⟩ : syracuseStep 219191 = 328787) B328787
theorem B219211 : Blo 215810 219211 := bstep (se 1 (by rfl) ⟨164408, by rfl⟩ : syracuseStep 219211 = 328817) B328817
theorem B219223 : Blo 215810 219223 := bstep (se 1 (by rfl) ⟨164417, by rfl⟩ : syracuseStep 219223 = 328835) B328835
theorem B219243 : Blo 215810 219243 := bstep (se 1 (by rfl) ⟨164432, by rfl⟩ : syracuseStep 219243 = 328865) B328865
theorem B219255 : Blo 215810 219255 := bstep (se 1 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 219255 = 328883) B328883
theorem B219275 : Blo 215810 219275 := bstep (se 1 (by rfl) ⟨164456, by rfl⟩ : syracuseStep 219275 = 328913) B328913
theorem B219287 : Blo 215810 219287 := bstep (se 1 (by rfl) ⟨164465, by rfl⟩ : syracuseStep 219287 = 328931) B328931
theorem B219307 : Blo 215810 219307 := bstep (se 1 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 219307 = 328961) B328961
theorem B219319 : Blo 215810 219319 := bstep (se 1 (by rfl) ⟨164489, by rfl⟩ : syracuseStep 219319 = 328979) B328979
theorem B219339 : Blo 215810 219339 := bstep (se 1 (by rfl) ⟨164504, by rfl⟩ : syracuseStep 219339 = 329009) B329009
theorem B219351 : Blo 215810 219351 := bstep (se 1 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 219351 = 329027) B329027
theorem B547033 : Blo 215810 547033 := bstep (se 2 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 547033 = 410275) B410275
theorem B219371 : Blo 215810 219371 := bstep (se 1 (by rfl) ⟨164528, by rfl⟩ : syracuseStep 219371 = 329057) B329057
theorem B219383 : Blo 215810 219383 := bstep (se 1 (by rfl) ⟨164537, by rfl⟩ : syracuseStep 219383 = 329075) B329075
theorem B219403 : Blo 215810 219403 := bstep (se 1 (by rfl) ⟨164552, by rfl⟩ : syracuseStep 219403 = 329105) B329105
theorem B219415 : Blo 215810 219415 := bstep (se 1 (by rfl) ⟨164561, by rfl⟩ : syracuseStep 219415 = 329123) B329123
theorem B219435 : Blo 215810 219435 := bstep (se 1 (by rfl) ⟨164576, by rfl⟩ : syracuseStep 219435 = 329153) B329153
theorem B219447 : Blo 215810 219447 := bstep (se 1 (by rfl) ⟨164585, by rfl⟩ : syracuseStep 219447 = 329171) B329171
theorem B219467 : Blo 215810 219467 := bstep (se 1 (by rfl) ⟨164600, by rfl⟩ : syracuseStep 219467 = 329201) B329201
theorem B219479 : Blo 215810 219479 := bstep (se 1 (by rfl) ⟨164609, by rfl⟩ : syracuseStep 219479 = 329219) B329219
theorem B1399133 : Blo 215810 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B219499 : Blo 215810 219499 := bstep (se 1 (by rfl) ⟨164624, by rfl⟩ : syracuseStep 219499 = 329249) B329249
theorem B219511 : Blo 215810 219511 := bstep (se 1 (by rfl) ⟨164633, by rfl⟩ : syracuseStep 219511 = 329267) B329267
theorem B1169795 : Blo 215810 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B219531 : Blo 215810 219531 := bstep (se 1 (by rfl) ⟨164648, by rfl⟩ : syracuseStep 219531 = 329297) B329297
theorem B219543 : Blo 215810 219543 := bstep (se 1 (by rfl) ⟨164657, by rfl⟩ : syracuseStep 219543 = 329315) B329315
theorem B416153 : Blo 215810 416153 := bstep (se 2 (by rfl) ⟨156057, by rfl⟩ : syracuseStep 416153 = 312115) B312115
theorem B219563 : Blo 215810 219563 := bstep (se 1 (by rfl) ⟨164672, by rfl⟩ : syracuseStep 219563 = 329345) B329345
theorem B219575 : Blo 215810 219575 := bstep (se 1 (by rfl) ⟨164681, by rfl⟩ : syracuseStep 219575 = 329363) B329363
theorem B219595 : Blo 215810 219595 := bstep (se 1 (by rfl) ⟨164696, by rfl⟩ : syracuseStep 219595 = 329393) B329393
theorem B219607 : Blo 215810 219607 := bstep (se 1 (by rfl) ⟨164705, by rfl⟩ : syracuseStep 219607 = 329411) B329411
theorem B219627 : Blo 215810 219627 := bstep (se 1 (by rfl) ⟨164720, by rfl⟩ : syracuseStep 219627 = 329441) B329441
theorem B219639 : Blo 215810 219639 := bstep (se 1 (by rfl) ⟨164729, by rfl⟩ : syracuseStep 219639 = 329459) B329459
theorem B219659 : Blo 215810 219659 := bstep (se 1 (by rfl) ⟨164744, by rfl⟩ : syracuseStep 219659 = 329489) B329489
theorem B219671 : Blo 215810 219671 := bstep (se 1 (by rfl) ⟨164753, by rfl⟩ : syracuseStep 219671 = 329507) B329507
theorem B219691 : Blo 215810 219691 := bstep (se 1 (by rfl) ⟨164768, by rfl⟩ : syracuseStep 219691 = 329537) B329537
theorem B219703 : Blo 215810 219703 := bstep (se 1 (by rfl) ⟨164777, by rfl⟩ : syracuseStep 219703 = 329555) B329555
theorem B219723 : Blo 215810 219723 := bstep (se 1 (by rfl) ⟨164792, by rfl⟩ : syracuseStep 219723 = 329585) B329585
theorem B219735 : Blo 215810 219735 := bstep (se 1 (by rfl) ⟨164801, by rfl⟩ : syracuseStep 219735 = 329603) B329603
theorem B219755 : Blo 215810 219755 := bstep (se 1 (by rfl) ⟨164816, by rfl⟩ : syracuseStep 219755 = 329633) B329633
theorem B219767 : Blo 215810 219767 := bstep (se 1 (by rfl) ⟨164825, by rfl⟩ : syracuseStep 219767 = 329651) B329651
theorem B1104515 : Blo 215810 1104515 := bstep (se 1 (by rfl) ⟨828386, by rfl⟩ : syracuseStep 1104515 = 1656773) B1656773
theorem B3594883 : Blo 215810 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B219787 : Blo 215810 219787 := bstep (se 1 (by rfl) ⟨164840, by rfl⟩ : syracuseStep 219787 = 329681) B329681
theorem B219799 : Blo 215810 219799 := bstep (se 1 (by rfl) ⟨164849, by rfl⟩ : syracuseStep 219799 = 329699) B329699
theorem B351065 : Blo 215810 351065 := bstep (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) B263299
theorem B416897 : Blo 215810 416897 := bstep (se 2 (by rfl) ⟨156336, by rfl⟩ : syracuseStep 416897 = 312673) B312673
theorem B548147 : Blo 215810 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B417163 : Blo 215810 417163 := bstep (se 1 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 417163 = 625745) B625745
theorem B1564109 : Blo 215810 1564109 := bstep (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) B586541
theorem B220663 : Blo 215810 220663 := bstep (se 1 (by rfl) ⟨165497, by rfl⟩ : syracuseStep 220663 = 330995) B330995
theorem B1236545 : Blo 215810 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B548441 : Blo 215810 548441 := bstep (se 2 (by rfl) ⟨205665, by rfl⟩ : syracuseStep 548441 = 411331) B411331
theorem B778049 : Blo 215810 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B1335361 : Blo 215810 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B450841 : Blo 215810 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B1040971 : Blo 215810 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B10543709 : Blo 215810 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B550091 : Blo 215810 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B615755 : Blo 215810 615755 := bstep (se 1 (by rfl) ⟨461816, by rfl⟩ : syracuseStep 615755 = 923633) B923633
theorem B1598899 : Blo 215810 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1238935 : Blo 215810 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B583645 : Blo 215810 583645 := bstep (se 3 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 583645 = 218867) B218867
theorem B551063 : Blo 215810 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B583859 : Blo 215810 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B878809 : Blo 215810 878809 := bstep (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) B659107
theorem B1108241 : Blo 215810 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B485657 : Blo 215810 485657 := bstep (se 2 (by rfl) ⟨182121, by rfl⟩ : syracuseStep 485657 = 364243) B364243
theorem B485747 : Blo 215810 485747 := bstep (se 1 (by rfl) ⟨364310, by rfl⟩ : syracuseStep 485747 = 728621) B728621
theorem B485783 : Blo 215810 485783 := bstep (se 1 (by rfl) ⟨364337, by rfl⟩ : syracuseStep 485783 = 728675) B728675
theorem B1108403 : Blo 215810 1108403 := bstep (se 1 (by rfl) ⟨831302, by rfl⟩ : syracuseStep 1108403 = 1662605) B1662605
theorem B485963 : Blo 215810 485963 := bstep (se 1 (by rfl) ⟨364472, by rfl⟩ : syracuseStep 485963 = 728945) B728945
theorem B2255435 : Blo 215810 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B617053 : Blo 215810 617053 := bstep (se 3 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 617053 = 231395) B231395
theorem B486017 : Blo 215810 486017 := bstep (se 2 (by rfl) ⟨182256, by rfl⟩ : syracuseStep 486017 = 364513) B364513
theorem B879277 : Blo 215810 879277 := bstep (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) B329729
theorem B551731 : Blo 215810 551731 := bstep (se 1 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 551731 = 827597) B827597
theorem B486233 : Blo 215810 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B486323 : Blo 215810 486323 := bstep (se 1 (by rfl) ⟨364742, by rfl⟩ : syracuseStep 486323 = 729485) B729485
theorem B617395 : Blo 215810 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B551873 : Blo 215810 551873 := bstep (se 2 (by rfl) ⟨206952, by rfl⟩ : syracuseStep 551873 = 413905) B413905
theorem B486359 : Blo 215810 486359 := bstep (se 1 (by rfl) ⟨364769, by rfl⟩ : syracuseStep 486359 = 729539) B729539
theorem B1272793 : Blo 215810 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B879619 : Blo 215810 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B1043549 : Blo 215810 1043549 := bstep (se 3 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 1043549 = 391331) B391331
theorem B486539 : Blo 215810 486539 := bstep (se 1 (by rfl) ⟨364904, by rfl⟩ : syracuseStep 486539 = 729809) B729809
theorem B1633459 : Blo 215810 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B486593 : Blo 215810 486593 := bstep (se 2 (by rfl) ⟨182472, by rfl⟩ : syracuseStep 486593 = 364945) B364945
theorem B584921 : Blo 215810 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B486809 : Blo 215810 486809 := bstep (se 2 (by rfl) ⟨182553, by rfl⟩ : syracuseStep 486809 = 365107) B365107
theorem B519641 : Blo 215810 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B486899 : Blo 215810 486899 := bstep (se 1 (by rfl) ⟨365174, by rfl⟩ : syracuseStep 486899 = 730349) B730349
theorem B1568261 : Blo 215810 1568261 := bstep (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) B294049
theorem B486935 : Blo 215810 486935 := bstep (se 1 (by rfl) ⟨365201, by rfl⟩ : syracuseStep 486935 = 730403) B730403
theorem B1568321 : Blo 215810 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B1601117 : Blo 215810 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B487115 : Blo 215810 487115 := bstep (se 1 (by rfl) ⟨365336, by rfl⟩ : syracuseStep 487115 = 730673) B730673
theorem B487169 : Blo 215810 487169 := bstep (se 2 (by rfl) ⟨182688, by rfl⟩ : syracuseStep 487169 = 365377) B365377
theorem B7499573 : Blo 215810 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B618329 : Blo 215810 618329 := bstep (se 2 (by rfl) ⟨231873, by rfl⟩ : syracuseStep 618329 = 463747) B463747
theorem B1404773 : Blo 215810 1404773 := bstep (se 4 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 1404773 = 263395) B263395
theorem B225163 : Blo 215810 225163 := bstep (se 1 (by rfl) ⟨168872, by rfl⟩ : syracuseStep 225163 = 337745) B337745
theorem B880577 : Blo 215810 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B520139 : Blo 215810 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B389081 : Blo 215810 389081 := bstep (se 2 (by rfl) ⟨145905, by rfl⟩ : syracuseStep 389081 = 291811) B291811
theorem B487385 : Blo 215810 487385 := bstep (se 2 (by rfl) ⟨182769, by rfl⟩ : syracuseStep 487385 = 365539) B365539
theorem B487475 : Blo 215810 487475 := bstep (se 1 (by rfl) ⟨365606, by rfl⟩ : syracuseStep 487475 = 731213) B731213
theorem B487511 : Blo 215810 487511 := bstep (se 1 (by rfl) ⟨365633, by rfl⟩ : syracuseStep 487511 = 731267) B731267
theorem B2355331 : Blo 215810 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B323723 : Blo 215810 323723 := bstep (se 1 (by rfl) ⟨242792, by rfl⟩ : syracuseStep 323723 = 485585) B485585
theorem B323735 : Blo 215810 323735 := bstep (se 1 (by rfl) ⟨242801, by rfl⟩ : syracuseStep 323735 = 485603) B485603
theorem B6942871 : Blo 215810 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B553139 : Blo 215810 553139 := bstep (se 1 (by rfl) ⟨414854, by rfl⟩ : syracuseStep 553139 = 829709) B829709
theorem B323801 : Blo 215810 323801 := bstep (se 2 (by rfl) ⟨121425, by rfl⟩ : syracuseStep 323801 = 242851) B242851
theorem B487691 : Blo 215810 487691 := bstep (se 1 (by rfl) ⟨365768, by rfl⟩ : syracuseStep 487691 = 731537) B731537
theorem B487745 : Blo 215810 487745 := bstep (se 2 (by rfl) ⟨182904, by rfl⟩ : syracuseStep 487745 = 365809) B365809
theorem B3371329 : Blo 215810 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B323915 : Blo 215810 323915 := bstep (se 1 (by rfl) ⟨242936, by rfl⟩ : syracuseStep 323915 = 485873) B485873
theorem B1110347 : Blo 215810 1110347 := bstep (se 1 (by rfl) ⟨832760, by rfl⟩ : syracuseStep 1110347 = 1665521) B1665521
theorem B323927 : Blo 215810 323927 := bstep (se 1 (by rfl) ⟨242945, by rfl⟩ : syracuseStep 323927 = 485891) B485891
theorem B323993 : Blo 215810 323993 := bstep (se 2 (by rfl) ⟨121497, by rfl⟩ : syracuseStep 323993 = 242995) B242995
theorem B324107 : Blo 215810 324107 := bstep (se 1 (by rfl) ⟨243080, by rfl⟩ : syracuseStep 324107 = 486161) B486161
theorem B324119 : Blo 215810 324119 := bstep (se 1 (by rfl) ⟨243089, by rfl⟩ : syracuseStep 324119 = 486179) B486179
theorem B487961 : Blo 215810 487961 := bstep (se 2 (by rfl) ⟨182985, by rfl⟩ : syracuseStep 487961 = 365971) B365971
theorem B324185 : Blo 215810 324185 := bstep (se 2 (by rfl) ⟨121569, by rfl⟩ : syracuseStep 324185 = 243139) B243139
theorem B488051 : Blo 215810 488051 := bstep (se 1 (by rfl) ⟨366038, by rfl⟩ : syracuseStep 488051 = 732077) B732077
theorem B488087 : Blo 215810 488087 := bstep (se 1 (by rfl) ⟨366065, by rfl⟩ : syracuseStep 488087 = 732131) B732131
theorem B324299 : Blo 215810 324299 := bstep (se 1 (by rfl) ⟨243224, by rfl⟩ : syracuseStep 324299 = 486449) B486449
theorem B553675 : Blo 215810 553675 := bstep (se 1 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 553675 = 830513) B830513
theorem B324311 : Blo 215810 324311 := bstep (se 1 (by rfl) ⟨243233, by rfl⟩ : syracuseStep 324311 = 486467) B486467
theorem B422617 : Blo 215810 422617 := bstep (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) B316963
theorem B324377 : Blo 215810 324377 := bstep (se 2 (by rfl) ⟨121641, by rfl⟩ : syracuseStep 324377 = 243283) B243283
theorem B488267 : Blo 215810 488267 := bstep (se 1 (by rfl) ⟨366200, by rfl⟩ : syracuseStep 488267 = 732401) B732401
theorem B553817 : Blo 215810 553817 := bstep (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) B415363
theorem B488321 : Blo 215810 488321 := bstep (se 2 (by rfl) ⟨183120, by rfl⟩ : syracuseStep 488321 = 366241) B366241
theorem B324491 : Blo 215810 324491 := bstep (se 1 (by rfl) ⟨243368, by rfl⟩ : syracuseStep 324491 = 486737) B486737
theorem B324503 : Blo 215810 324503 := bstep (se 1 (by rfl) ⟨243377, by rfl⟩ : syracuseStep 324503 = 486755) B486755
theorem B4027315 : Blo 215810 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B324569 : Blo 215810 324569 := bstep (se 2 (by rfl) ⟨121713, by rfl⟩ : syracuseStep 324569 = 243427) B243427
theorem B783425 : Blo 215810 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B324683 : Blo 215810 324683 := bstep (se 1 (by rfl) ⟨243512, by rfl⟩ : syracuseStep 324683 = 487025) B487025
theorem B324695 : Blo 215810 324695 := bstep (se 1 (by rfl) ⟨243521, by rfl⟩ : syracuseStep 324695 = 487043) B487043
theorem B488537 : Blo 215810 488537 := bstep (se 2 (by rfl) ⟨183201, by rfl⟩ : syracuseStep 488537 = 366403) B366403
theorem B324761 : Blo 215810 324761 := bstep (se 2 (by rfl) ⟨121785, by rfl⟩ : syracuseStep 324761 = 243571) B243571
theorem B488627 : Blo 215810 488627 := bstep (se 1 (by rfl) ⟨366470, by rfl⟩ : syracuseStep 488627 = 732941) B732941
theorem B488663 : Blo 215810 488663 := bstep (se 1 (by rfl) ⟨366497, by rfl⟩ : syracuseStep 488663 = 732995) B732995
theorem B685273 : Blo 215810 685273 := bstep (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) B513955
theorem B619741 : Blo 215810 619741 := bstep (se 3 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 619741 = 232403) B232403
theorem B324875 : Blo 215810 324875 := bstep (se 1 (by rfl) ⟨243656, by rfl⟩ : syracuseStep 324875 = 487313) B487313
theorem B324887 : Blo 215810 324887 := bstep (se 1 (by rfl) ⟨243665, by rfl⟩ : syracuseStep 324887 = 487331) B487331
theorem B324953 : Blo 215810 324953 := bstep (se 2 (by rfl) ⟨121857, by rfl⟩ : syracuseStep 324953 = 243715) B243715
theorem B488843 : Blo 215810 488843 := bstep (se 1 (by rfl) ⟨366632, by rfl⟩ : syracuseStep 488843 = 733265) B733265
theorem B488897 : Blo 215810 488897 := bstep (se 2 (by rfl) ⟨183336, by rfl⟩ : syracuseStep 488897 = 366673) B366673
theorem B619969 : Blo 215810 619969 := bstep (se 2 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 619969 = 464977) B464977
theorem B325067 : Blo 215810 325067 := bstep (se 1 (by rfl) ⟨243800, by rfl⟩ : syracuseStep 325067 = 487601) B487601
theorem B325079 : Blo 215810 325079 := bstep (se 1 (by rfl) ⟨243809, by rfl⟩ : syracuseStep 325079 = 487619) B487619
theorem B325145 : Blo 215810 325145 := bstep (se 2 (by rfl) ⟨121929, by rfl⟩ : syracuseStep 325145 = 243859) B243859
theorem B325259 : Blo 215810 325259 := bstep (se 1 (by rfl) ⟨243944, by rfl⟩ : syracuseStep 325259 = 487889) B487889
theorem B325271 : Blo 215810 325271 := bstep (se 1 (by rfl) ⟨243953, by rfl⟩ : syracuseStep 325271 = 487907) B487907
theorem B554647 : Blo 215810 554647 := bstep (se 1 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 554647 = 831971) B831971
theorem B489113 : Blo 215810 489113 := bstep (se 2 (by rfl) ⟨183417, by rfl⟩ : syracuseStep 489113 = 366835) B366835
theorem B325337 : Blo 215810 325337 := bstep (se 2 (by rfl) ⟨122001, by rfl⟩ : syracuseStep 325337 = 244003) B244003
theorem B489203 : Blo 215810 489203 := bstep (se 1 (by rfl) ⟨366902, by rfl⟩ : syracuseStep 489203 = 733805) B733805
theorem B489239 : Blo 215810 489239 := bstep (se 1 (by rfl) ⟨366929, by rfl⟩ : syracuseStep 489239 = 733859) B733859
theorem B620311 : Blo 215810 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B325451 : Blo 215810 325451 := bstep (se 1 (by rfl) ⟨244088, by rfl⟩ : syracuseStep 325451 = 488177) B488177
theorem B325463 : Blo 215810 325463 := bstep (se 1 (by rfl) ⟨244097, by rfl⟩ : syracuseStep 325463 = 488195) B488195
theorem B292747 : Blo 215810 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B325529 : Blo 215810 325529 := bstep (se 2 (by rfl) ⟨122073, by rfl⟩ : syracuseStep 325529 = 244147) B244147
theorem B1898417 : Blo 215810 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B489419 : Blo 215810 489419 := bstep (se 1 (by rfl) ⟨367064, by rfl⟩ : syracuseStep 489419 = 734129) B734129
theorem B784349 : Blo 215810 784349 := bstep (se 3 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 784349 = 294131) B294131
theorem B489473 : Blo 215810 489473 := bstep (se 2 (by rfl) ⟨183552, by rfl⟩ : syracuseStep 489473 = 367105) B367105
theorem B325643 : Blo 215810 325643 := bstep (se 1 (by rfl) ⟨244232, by rfl⟩ : syracuseStep 325643 = 488465) B488465
theorem B555031 : Blo 215810 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B325655 : Blo 215810 325655 := bstep (se 1 (by rfl) ⟨244241, by rfl⟩ : syracuseStep 325655 = 488483) B488483
theorem B1112129 : Blo 215810 1112129 := bstep (se 2 (by rfl) ⟨417048, by rfl⟩ : syracuseStep 1112129 = 834097) B834097
theorem B555083 : Blo 215810 555083 := bstep (se 1 (by rfl) ⟨416312, by rfl⟩ : syracuseStep 555083 = 832625) B832625
theorem B325721 : Blo 215810 325721 := bstep (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) B244291
theorem B1177751 : Blo 215810 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B6715543 : Blo 215810 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B325835 : Blo 215810 325835 := bstep (se 1 (by rfl) ⟨244376, by rfl⟩ : syracuseStep 325835 = 488753) B488753
theorem B325847 : Blo 215810 325847 := bstep (se 1 (by rfl) ⟨244385, by rfl⟩ : syracuseStep 325847 = 488771) B488771
theorem B489689 : Blo 215810 489689 := bstep (se 2 (by rfl) ⟨183633, by rfl⟩ : syracuseStep 489689 = 367267) B367267
theorem B325913 : Blo 215810 325913 := bstep (se 2 (by rfl) ⟨122217, by rfl⟩ : syracuseStep 325913 = 244435) B244435
theorem B489779 : Blo 215810 489779 := bstep (se 1 (by rfl) ⟨367334, by rfl⟩ : syracuseStep 489779 = 734669) B734669
theorem B489815 : Blo 215810 489815 := bstep (se 1 (by rfl) ⟨367361, by rfl⟩ : syracuseStep 489815 = 734723) B734723
theorem B326027 : Blo 215810 326027 := bstep (se 1 (by rfl) ⟨244520, by rfl⟩ : syracuseStep 326027 = 489041) B489041
theorem B326039 : Blo 215810 326039 := bstep (se 1 (by rfl) ⟨244529, by rfl⟩ : syracuseStep 326039 = 489059) B489059
theorem B555457 : Blo 215810 555457 := bstep (se 2 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 555457 = 416593) B416593
theorem B326105 : Blo 215810 326105 := bstep (se 2 (by rfl) ⟨122289, by rfl⟩ : syracuseStep 326105 = 244579) B244579
theorem B2980313 : Blo 215810 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B621017 : Blo 215810 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B489995 : Blo 215810 489995 := bstep (se 1 (by rfl) ⟨367496, by rfl⟩ : syracuseStep 489995 = 734993) B734993
theorem B3504653 : Blo 215810 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B490049 : Blo 215810 490049 := bstep (se 2 (by rfl) ⟨183768, by rfl⟩ : syracuseStep 490049 = 367537) B367537
theorem B326219 : Blo 215810 326219 := bstep (se 1 (by rfl) ⟨244664, by rfl⟩ : syracuseStep 326219 = 489329) B489329
theorem B260695 : Blo 215810 260695 := bstep (se 1 (by rfl) ⟨195521, by rfl⟩ : syracuseStep 260695 = 391043) B391043
theorem B326231 : Blo 215810 326231 := bstep (se 1 (by rfl) ⟨244673, by rfl⟩ : syracuseStep 326231 = 489347) B489347
theorem B326297 : Blo 215810 326297 := bstep (se 2 (by rfl) ⟨122361, by rfl⟩ : syracuseStep 326297 = 244723) B244723
theorem B326411 : Blo 215810 326411 := bstep (se 1 (by rfl) ⟨244808, by rfl⟩ : syracuseStep 326411 = 489617) B489617
theorem B326423 : Blo 215810 326423 := bstep (se 1 (by rfl) ⟨244817, by rfl⟩ : syracuseStep 326423 = 489635) B489635
theorem B490265 : Blo 215810 490265 := bstep (se 2 (by rfl) ⟨183849, by rfl⟩ : syracuseStep 490265 = 367699) B367699
theorem B326489 : Blo 215810 326489 := bstep (se 2 (by rfl) ⟨122433, by rfl⟩ : syracuseStep 326489 = 244867) B244867
theorem B490355 : Blo 215810 490355 := bstep (se 1 (by rfl) ⟨367766, by rfl⟩ : syracuseStep 490355 = 735533) B735533
theorem B490391 : Blo 215810 490391 := bstep (se 1 (by rfl) ⟨367793, by rfl⟩ : syracuseStep 490391 = 735587) B735587
theorem B326603 : Blo 215810 326603 := bstep (se 1 (by rfl) ⟨244952, by rfl⟩ : syracuseStep 326603 = 489905) B489905
theorem B326615 : Blo 215810 326615 := bstep (se 1 (by rfl) ⟨244961, by rfl⟩ : syracuseStep 326615 = 489923) B489923
theorem B556055 : Blo 215810 556055 := bstep (se 1 (by rfl) ⟨417041, by rfl⟩ : syracuseStep 556055 = 834083) B834083
theorem B326681 : Blo 215810 326681 := bstep (se 2 (by rfl) ⟨122505, by rfl⟩ : syracuseStep 326681 = 245011) B245011
theorem B490571 : Blo 215810 490571 := bstep (se 1 (by rfl) ⟨367928, by rfl⟩ : syracuseStep 490571 = 735857) B735857
theorem B490625 : Blo 215810 490625 := bstep (se 2 (by rfl) ⟨183984, by rfl⟩ : syracuseStep 490625 = 367969) B367969
theorem B326795 : Blo 215810 326795 := bstep (se 1 (by rfl) ⟨245096, by rfl⟩ : syracuseStep 326795 = 490193) B490193
theorem B326807 : Blo 215810 326807 := bstep (se 1 (by rfl) ⟨245105, by rfl⟩ : syracuseStep 326807 = 490211) B490211
theorem B326873 : Blo 215810 326873 := bstep (se 2 (by rfl) ⟨122577, by rfl⟩ : syracuseStep 326873 = 245155) B245155
theorem B785629 : Blo 215810 785629 := bstep (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) B294611
theorem B326987 : Blo 215810 326987 := bstep (se 1 (by rfl) ⟨245240, by rfl⟩ : syracuseStep 326987 = 490481) B490481
theorem B326999 : Blo 215810 326999 := bstep (se 1 (by rfl) ⟨245249, by rfl⟩ : syracuseStep 326999 = 490499) B490499
theorem B490841 : Blo 215810 490841 := bstep (se 2 (by rfl) ⟨184065, by rfl⟩ : syracuseStep 490841 = 368131) B368131
theorem B327065 : Blo 215810 327065 := bstep (se 2 (by rfl) ⟨122649, by rfl⟩ : syracuseStep 327065 = 245299) B245299
theorem B490931 : Blo 215810 490931 := bstep (se 1 (by rfl) ⟨368198, by rfl⟩ : syracuseStep 490931 = 736397) B736397
theorem B490967 : Blo 215810 490967 := bstep (se 1 (by rfl) ⟨368225, by rfl⟩ : syracuseStep 490967 = 736451) B736451
theorem B327179 : Blo 215810 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B327191 : Blo 215810 327191 := bstep (se 1 (by rfl) ⟨245393, by rfl⟩ : syracuseStep 327191 = 490787) B490787
theorem B327257 : Blo 215810 327257 := bstep (se 2 (by rfl) ⟨122721, by rfl⟩ : syracuseStep 327257 = 245443) B245443
theorem B491147 : Blo 215810 491147 := bstep (se 1 (by rfl) ⟨368360, by rfl⟩ : syracuseStep 491147 = 736721) B736721
theorem B491201 : Blo 215810 491201 := bstep (se 2 (by rfl) ⟨184200, by rfl⟩ : syracuseStep 491201 = 368401) B368401
theorem B327371 : Blo 215810 327371 := bstep (se 1 (by rfl) ⟨245528, by rfl⟩ : syracuseStep 327371 = 491057) B491057
theorem B327383 : Blo 215810 327383 := bstep (se 1 (by rfl) ⟨245537, by rfl⟩ : syracuseStep 327383 = 491075) B491075
theorem B1998553 : Blo 215810 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B884483 : Blo 215810 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B327449 : Blo 215810 327449 := bstep (se 2 (by rfl) ⟨122793, by rfl⟩ : syracuseStep 327449 = 245587) B245587
theorem B3735395 : Blo 215810 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B327563 : Blo 215810 327563 := bstep (se 1 (by rfl) ⟨245672, by rfl⟩ : syracuseStep 327563 = 491345) B491345
theorem B327575 : Blo 215810 327575 := bstep (se 1 (by rfl) ⟨245681, by rfl⟩ : syracuseStep 327575 = 491363) B491363
theorem B491417 : Blo 215810 491417 := bstep (se 2 (by rfl) ⟨184281, by rfl⟩ : syracuseStep 491417 = 368563) B368563
theorem B1015769 : Blo 215810 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B327641 : Blo 215810 327641 := bstep (se 2 (by rfl) ⟨122865, by rfl⟩ : syracuseStep 327641 = 245731) B245731
theorem B491507 : Blo 215810 491507 := bstep (se 1 (by rfl) ⟨368630, by rfl⟩ : syracuseStep 491507 = 737261) B737261
theorem B327695 : Blo 215810 327695 := bstep (se 1 (by rfl) ⟨245771, by rfl⟩ : syracuseStep 327695 = 491543) B491543
theorem B327737 : Blo 215810 327737 := bstep (se 2 (by rfl) ⟨122901, by rfl⟩ : syracuseStep 327737 = 245803) B245803
theorem B491579 : Blo 215810 491579 := bstep (se 1 (by rfl) ⟨368684, by rfl⟩ : syracuseStep 491579 = 737369) B737369
theorem B327815 : Blo 215810 327815 := bstep (se 1 (by rfl) ⟨245861, by rfl⟩ : syracuseStep 327815 = 491723) B491723
theorem B327851 : Blo 215810 327851 := bstep (se 1 (by rfl) ⟨245888, by rfl⟩ : syracuseStep 327851 = 491777) B491777
theorem B491705 : Blo 215810 491705 := bstep (se 2 (by rfl) ⟨184389, by rfl⟩ : syracuseStep 491705 = 368779) B368779
theorem B327881 : Blo 215810 327881 := bstep (se 2 (by rfl) ⟨122955, by rfl⟩ : syracuseStep 327881 = 245911) B245911
theorem B327995 : Blo 215810 327995 := bstep (se 1 (by rfl) ⟨245996, by rfl⟩ : syracuseStep 327995 = 491993) B491993
theorem B328055 : Blo 215810 328055 := bstep (se 1 (by rfl) ⟨246041, by rfl⟩ : syracuseStep 328055 = 492083) B492083
theorem B328079 : Blo 215810 328079 := bstep (se 1 (by rfl) ⟨246059, by rfl⟩ : syracuseStep 328079 = 492119) B492119
theorem B328121 : Blo 215810 328121 := bstep (se 2 (by rfl) ⟨123045, by rfl⟩ : syracuseStep 328121 = 246091) B246091
theorem B328199 : Blo 215810 328199 := bstep (se 1 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 328199 = 492299) B492299
theorem B557579 : Blo 215810 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B492047 : Blo 215810 492047 := bstep (se 1 (by rfl) ⟨369035, by rfl⟩ : syracuseStep 492047 = 738071) B738071
theorem B1245725 : Blo 215810 1245725 := bstep (se 3 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 1245725 = 467147) B467147
theorem B492065 : Blo 215810 492065 := bstep (se 2 (by rfl) ⟨184524, by rfl⟩ : syracuseStep 492065 = 369049) B369049
theorem B328235 : Blo 215810 328235 := bstep (se 1 (by rfl) ⟨246176, by rfl⟩ : syracuseStep 328235 = 492353) B492353
theorem B328265 : Blo 215810 328265 := bstep (se 2 (by rfl) ⟨123099, by rfl⟩ : syracuseStep 328265 = 246199) B246199
theorem B328379 : Blo 215810 328379 := bstep (se 1 (by rfl) ⟨246284, by rfl⟩ : syracuseStep 328379 = 492569) B492569
theorem B1114825 : Blo 215810 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B328439 : Blo 215810 328439 := bstep (se 1 (by rfl) ⟨246329, by rfl⟩ : syracuseStep 328439 = 492659) B492659
theorem B885505 : Blo 215810 885505 := bstep (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) B664129
theorem B328463 : Blo 215810 328463 := bstep (se 1 (by rfl) ⟨246347, by rfl⟩ : syracuseStep 328463 = 492695) B492695
theorem B328505 : Blo 215810 328505 := bstep (se 2 (by rfl) ⟨123189, by rfl⟩ : syracuseStep 328505 = 246379) B246379
theorem B492407 : Blo 215810 492407 := bstep (se 1 (by rfl) ⟨369305, by rfl⟩ : syracuseStep 492407 = 738611) B738611
theorem B328583 : Blo 215810 328583 := bstep (se 1 (by rfl) ⟨246437, by rfl⟩ : syracuseStep 328583 = 492875) B492875
theorem B328619 : Blo 215810 328619 := bstep (se 1 (by rfl) ⟨246464, by rfl⟩ : syracuseStep 328619 = 492929) B492929
theorem B328649 : Blo 215810 328649 := bstep (se 2 (by rfl) ⟨123243, by rfl⟩ : syracuseStep 328649 = 246487) B246487
theorem B623627 : Blo 215810 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B492587 : Blo 215810 492587 := bstep (se 1 (by rfl) ⟨369440, by rfl⟩ : syracuseStep 492587 = 738881) B738881
theorem B328763 : Blo 215810 328763 := bstep (se 1 (by rfl) ⟨246572, by rfl⟩ : syracuseStep 328763 = 493145) B493145
theorem B328823 : Blo 215810 328823 := bstep (se 1 (by rfl) ⟨246617, by rfl⟩ : syracuseStep 328823 = 493235) B493235
theorem B328847 : Blo 215810 328847 := bstep (se 1 (by rfl) ⟨246635, by rfl⟩ : syracuseStep 328847 = 493271) B493271
theorem B328889 : Blo 215810 328889 := bstep (se 2 (by rfl) ⟨123333, by rfl⟩ : syracuseStep 328889 = 246667) B246667
theorem B328951 : Blo 215810 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B328967 : Blo 215810 328967 := bstep (se 1 (by rfl) ⟨246725, by rfl⟩ : syracuseStep 328967 = 493451) B493451
theorem B329003 : Blo 215810 329003 := bstep (se 1 (by rfl) ⟨246752, by rfl⟩ : syracuseStep 329003 = 493505) B493505
theorem B623933 : Blo 215810 623933 := bstep (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) B233975
theorem B329033 : Blo 215810 329033 := bstep (se 2 (by rfl) ⟨123387, by rfl⟩ : syracuseStep 329033 = 246775) B246775
theorem B492947 : Blo 215810 492947 := bstep (se 1 (by rfl) ⟨369710, by rfl⟩ : syracuseStep 492947 = 739421) B739421
theorem B329147 : Blo 215810 329147 := bstep (se 1 (by rfl) ⟨246860, by rfl⟩ : syracuseStep 329147 = 493721) B493721
theorem B493001 : Blo 215810 493001 := bstep (se 2 (by rfl) ⟨184875, by rfl⟩ : syracuseStep 493001 = 369751) B369751
theorem B329207 : Blo 215810 329207 := bstep (se 1 (by rfl) ⟨246905, by rfl⟩ : syracuseStep 329207 = 493811) B493811
theorem B329231 : Blo 215810 329231 := bstep (se 1 (by rfl) ⟨246923, by rfl⟩ : syracuseStep 329231 = 493847) B493847
theorem B1181213 : Blo 215810 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B886301 : Blo 215810 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B624161 : Blo 215810 624161 := bstep (se 2 (by rfl) ⟨234060, by rfl⟩ : syracuseStep 624161 = 468121) B468121
theorem B329273 : Blo 215810 329273 := bstep (se 2 (by rfl) ⟨123477, by rfl⟩ : syracuseStep 329273 = 246955) B246955
theorem B329351 : Blo 215810 329351 := bstep (se 1 (by rfl) ⟨247013, by rfl⟩ : syracuseStep 329351 = 494027) B494027
theorem B329387 : Blo 215810 329387 := bstep (se 1 (by rfl) ⟨247040, by rfl⟩ : syracuseStep 329387 = 494081) B494081
theorem B329417 : Blo 215810 329417 := bstep (se 2 (by rfl) ⟨123531, by rfl⟩ : syracuseStep 329417 = 247063) B247063
theorem B329531 : Blo 215810 329531 := bstep (se 1 (by rfl) ⟨247148, by rfl⟩ : syracuseStep 329531 = 494297) B494297
theorem B624503 : Blo 215810 624503 := bstep (se 1 (by rfl) ⟨468377, by rfl⟩ : syracuseStep 624503 = 936755) B936755
theorem B329591 : Blo 215810 329591 := bstep (se 1 (by rfl) ⟨247193, by rfl⟩ : syracuseStep 329591 = 494387) B494387
theorem B329615 : Blo 215810 329615 := bstep (se 1 (by rfl) ⟨247211, by rfl⟩ : syracuseStep 329615 = 494423) B494423
theorem B2131865 : Blo 215810 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B329657 : Blo 215810 329657 := bstep (se 2 (by rfl) ⟨123621, by rfl⟩ : syracuseStep 329657 = 247243) B247243
theorem B657353 : Blo 215810 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B395323 : Blo 215810 395323 := bstep (se 1 (by rfl) ⟨296492, by rfl⟩ : syracuseStep 395323 = 592985) B592985
theorem B755831 : Blo 215810 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B493703 : Blo 215810 493703 := bstep (se 1 (by rfl) ⟨370277, by rfl⟩ : syracuseStep 493703 = 740555) B740555
theorem B526607 : Blo 215810 526607 := bstep (se 1 (by rfl) ⟨394955, by rfl⟩ : syracuseStep 526607 = 789911) B789911
theorem B493883 : Blo 215810 493883 := bstep (se 1 (by rfl) ⟨370412, by rfl⟩ : syracuseStep 493883 = 740825) B740825
theorem B494009 : Blo 215810 494009 := bstep (se 2 (by rfl) ⟨185253, by rfl⟩ : syracuseStep 494009 = 370507) B370507
theorem B559703 : Blo 215810 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B494351 : Blo 215810 494351 := bstep (se 1 (by rfl) ⟨370763, by rfl⟩ : syracuseStep 494351 = 741527) B741527
theorem B494369 : Blo 215810 494369 := bstep (se 2 (by rfl) ⟨185388, by rfl⟩ : syracuseStep 494369 = 370777) B370777
theorem B4950821 : Blo 215810 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B1903409 : Blo 215810 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B1248209 : Blo 215810 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B461867 : Blo 215810 461867 := bstep (se 1 (by rfl) ⟨346400, by rfl⟩ : syracuseStep 461867 = 692801) B692801
theorem B756797 : Blo 215810 756797 := bstep (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) B283799
theorem B691571 : Blo 215810 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B822737 : Blo 215810 822737 := bstep (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) B617053
theorem B1314269 : Blo 215810 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B232967 : Blo 215810 232967 := bstep (se 1 (by rfl) ⟨174725, by rfl⟩ : syracuseStep 232967 = 349451) B349451
theorem B17927831 : Blo 215810 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B364331 : Blo 215810 364331 := bstep (se 1 (by rfl) ⟨273248, by rfl⟩ : syracuseStep 364331 = 546497) B546497
theorem B1576793 : Blo 215810 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B823193 : Blo 215810 823193 := bstep (se 2 (by rfl) ⟨308697, by rfl⟩ : syracuseStep 823193 = 617395) B617395
theorem B2494637 : Blo 215810 2494637 := bstep (se 3 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 2494637 = 935489) B935489
theorem B364729 : Blo 215810 364729 := bstep (se 2 (by rfl) ⟨136773, by rfl⟩ : syracuseStep 364729 = 273547) B273547
theorem B1315045 : Blo 215810 1315045 := bstep (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) B246571
theorem B6754859 : Blo 215810 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B1250099 : Blo 215810 1250099 := bstep (se 1 (by rfl) ⟨937574, by rfl⟩ : syracuseStep 1250099 = 1875149) B1875149
theorem B365431 : Blo 215810 365431 := bstep (se 1 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 365431 = 548147) B548147
theorem B824363 : Blo 215810 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B365627 : Blo 215810 365627 := bstep (se 1 (by rfl) ⟨274220, by rfl⟩ : syracuseStep 365627 = 548441) B548441
theorem B300217 : Blo 215810 300217 := bstep (se 2 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 300217 = 225163) B225163
theorem B660737 : Blo 215810 660737 := bstep (se 2 (by rfl) ⟨247776, by rfl⟩ : syracuseStep 660737 = 495553) B495553
theorem B366025 : Blo 215810 366025 := bstep (se 2 (by rfl) ⟨137259, by rfl⟩ : syracuseStep 366025 = 274519) B274519
theorem B923393 : Blo 215810 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B4495105 : Blo 215810 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B1054579 : Blo 215810 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B890777 : Blo 215810 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B366727 : Blo 215810 366727 := bstep (se 1 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 366727 = 550091) B550091
theorem B465097 : Blo 215810 465097 := bstep (se 2 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 465097 = 348823) B348823
theorem B1251557 : Blo 215810 1251557 := bstep (se 4 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 1251557 = 234667) B234667
theorem B563489 : Blo 215810 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B465353 : Blo 215810 465353 := bstep (se 2 (by rfl) ⟨174507, by rfl⟩ : syracuseStep 465353 = 349015) B349015
theorem B1055425 : Blo 215810 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B367375 : Blo 215810 367375 := bstep (se 1 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 367375 = 551063) B551063
theorem B4725539 : Blo 215810 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B826321 : Blo 215810 826321 := bstep (se 2 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 826321 = 619741) B619741
theorem B826625 : Blo 215810 826625 := bstep (se 2 (by rfl) ⟨309984, by rfl⟩ : syracuseStep 826625 = 619969) B619969
theorem B367915 : Blo 215810 367915 := bstep (se 1 (by rfl) ⟨275936, by rfl⟩ : syracuseStep 367915 = 551873) B551873
theorem B695699 : Blo 215810 695699 := bstep (se 1 (by rfl) ⟨521774, by rfl⟩ : syracuseStep 695699 = 1043549) B1043549
theorem B368057 : Blo 215810 368057 := bstep (se 2 (by rfl) ⟨138021, by rfl⟩ : syracuseStep 368057 = 276043) B276043
theorem B827081 : Blo 215810 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B728891 : Blo 215810 728891 := bstep (se 1 (by rfl) ⟨546668, by rfl⟩ : syracuseStep 728891 = 1093337) B1093337
theorem B466823 : Blo 215810 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B368759 : Blo 215810 368759 := bstep (se 1 (by rfl) ⟨276569, by rfl⟩ : syracuseStep 368759 = 553139) B553139
theorem B8954057 : Blo 215810 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B729377 : Blo 215810 729377 := bstep (se 2 (by rfl) ⟨273516, by rfl⟩ : syracuseStep 729377 = 547033) B547033
theorem B1122707 : Blo 215810 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B369211 : Blo 215810 369211 := bstep (se 1 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 369211 = 553817) B553817
theorem B369353 : Blo 215810 369353 := bstep (se 2 (by rfl) ⟨138507, by rfl⟩ : syracuseStep 369353 = 277015) B277015
theorem B4793177 : Blo 215810 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B729971 : Blo 215810 729971 := bstep (se 1 (by rfl) ⟨547478, by rfl⟩ : syracuseStep 729971 = 1094957) B1094957
theorem B467831 : Blo 215810 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B1778699 : Blo 215810 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B468011 : Blo 215810 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B7611479 : Blo 215810 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B370055 : Blo 215810 370055 := bstep (se 1 (by rfl) ⟨277541, by rfl⟩ : syracuseStep 370055 = 555083) B555083
theorem B4072913 : Blo 215810 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B2336435 : Blo 215810 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B2074369 : Blo 215810 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B370703 : Blo 215810 370703 := bstep (se 1 (by rfl) ⟨278027, by rfl⟩ : syracuseStep 370703 = 556055) B556055
theorem B2664737 : Blo 215810 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B1387037 : Blo 215810 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B1780481 : Blo 215810 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B830209 : Blo 215810 830209 := bstep (se 2 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 830209 = 622657) B622657
theorem B2960165 : Blo 215810 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B601121 : Blo 215810 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B273451 : Blo 215810 273451 := bstep (se 1 (by rfl) ⟨205088, by rfl⟩ : syracuseStep 273451 = 410177) B410177
theorem B732563 : Blo 215810 732563 := bstep (se 1 (by rfl) ⟨549422, by rfl⟩ : syracuseStep 732563 = 1098845) B1098845
theorem B1387961 : Blo 215810 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B2338723 : Blo 215810 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B274423 : Blo 215810 274423 := bstep (se 1 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 274423 = 411635) B411635
theorem B1093661 : Blo 215810 1093661 := bstep (se 3 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 1093661 = 410123) B410123
theorem B307319 : Blo 215810 307319 := bstep (se 1 (by rfl) ⟨230489, by rfl⟩ : syracuseStep 307319 = 460979) B460979
theorem B307513 : Blo 215810 307513 := bstep (se 2 (by rfl) ⟨115317, by rfl⟩ : syracuseStep 307513 = 230635) B230635
theorem B274747 : Blo 215810 274747 := bstep (se 1 (by rfl) ⟨206060, by rfl⟩ : syracuseStep 274747 = 412121) B412121
theorem B1094147 : Blo 215810 1094147 := bstep (se 1 (by rfl) ⟨820610, by rfl⟩ : syracuseStep 1094147 = 1641221) B1641221
theorem B930365 : Blo 215810 930365 := bstep (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) B348887
theorem B4207285 : Blo 215810 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B2503385 : Blo 215810 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B733967 : Blo 215810 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B734237 : Blo 215810 734237 := bstep (se 3 (by rfl) ⟨137669, by rfl⟩ : syracuseStep 734237 = 275339) B275339
theorem B1651913 : Blo 215810 1651913 := bstep (se 2 (by rfl) ⟨619467, by rfl⟩ : syracuseStep 1651913 = 1238935) B1238935
theorem B275719 : Blo 215810 275719 := bstep (se 1 (by rfl) ⟨206789, by rfl⟩ : syracuseStep 275719 = 413579) B413579
theorem B242959 : Blo 215810 242959 := bstep (se 1 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 242959 = 364439) B364439
theorem B3225091 : Blo 215810 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B833111 : Blo 215810 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B276139 : Blo 215810 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B243463 : Blo 215810 243463 := bstep (se 1 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 243463 = 365195) B365195
theorem B276367 : Blo 215810 276367 := bstep (se 1 (by rfl) ⟨207275, by rfl⟩ : syracuseStep 276367 = 414551) B414551
theorem B702361 : Blo 215810 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B243643 : Blo 215810 243643 := bstep (se 1 (by rfl) ⟨182732, by rfl⟩ : syracuseStep 243643 = 365465) B365465
theorem B833597 : Blo 215810 833597 := bstep (se 3 (by rfl) ⟨156299, by rfl⟩ : syracuseStep 833597 = 312599) B312599
theorem B1095767 : Blo 215810 1095767 := bstep (se 1 (by rfl) ⟨821825, by rfl⟩ : syracuseStep 1095767 = 1643651) B1643651
theorem B473359 : Blo 215810 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B244111 : Blo 215810 244111 := bstep (se 1 (by rfl) ⟨183083, by rfl⟩ : syracuseStep 244111 = 366167) B366167
theorem B735641 : Blo 215810 735641 := bstep (se 2 (by rfl) ⟨275865, by rfl⟩ : syracuseStep 735641 = 551731) B551731
theorem B932381 : Blo 215810 932381 := bstep (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) B349643
theorem B1096253 : Blo 215810 1096253 := bstep (se 3 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 1096253 = 411095) B411095
theorem B277111 : Blo 215810 277111 := bstep (se 1 (by rfl) ⟨207833, by rfl⟩ : syracuseStep 277111 = 415667) B415667
theorem B244615 : Blo 215810 244615 := bstep (se 1 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 244615 = 366923) B366923
theorem B2177945 : Blo 215810 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B277435 : Blo 215810 277435 := bstep (se 1 (by rfl) ⟨208076, by rfl⟩ : syracuseStep 277435 = 416153) B416153
theorem B244795 : Blo 215810 244795 := bstep (se 1 (by rfl) ⟨183596, by rfl⟩ : syracuseStep 244795 = 367193) B367193
theorem B736343 : Blo 215810 736343 := bstep (se 1 (by rfl) ⟨552257, by rfl⟩ : syracuseStep 736343 = 1104515) B1104515
theorem B2800727 : Blo 215810 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B441463 : Blo 215810 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B933065 : Blo 215810 933065 := bstep (se 2 (by rfl) ⟨349899, by rfl⟩ : syracuseStep 933065 = 699799) B699799
theorem B834875 : Blo 215810 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B277931 : Blo 215810 277931 := bstep (se 1 (by rfl) ⟨208448, by rfl⟩ : syracuseStep 277931 = 416897) B416897
theorem B245263 : Blo 215810 245263 := bstep (se 1 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 245263 = 367895) B367895
theorem B736829 : Blo 215810 736829 := bstep (se 3 (by rfl) ⟨138155, by rfl⟩ : syracuseStep 736829 = 276311) B276311
theorem B5062445 : Blo 215810 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B245767 : Blo 215810 245767 := bstep (se 1 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 245767 = 368651) B368651
theorem B245947 : Blo 215810 245947 := bstep (se 1 (by rfl) ⟨184460, by rfl⟩ : syracuseStep 245947 = 368921) B368921
theorem B9257161 : Blo 215810 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B1098035 : Blo 215810 1098035 := bstep (se 1 (by rfl) ⟨823526, by rfl⟩ : syracuseStep 1098035 = 1647053) B1647053
theorem B7029139 : Blo 215810 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B1556957 : Blo 215810 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B1098359 : Blo 215810 1098359 := bstep (se 1 (by rfl) ⟨823769, by rfl⟩ : syracuseStep 1098359 = 1647539) B1647539
theorem B246415 : Blo 215810 246415 := bstep (se 1 (by rfl) ⟨184811, by rfl⟩ : syracuseStep 246415 = 369623) B369623
theorem B410503 : Blo 215810 410503 := bstep (se 1 (by rfl) ⟨307877, by rfl⟩ : syracuseStep 410503 = 615755) B615755
theorem B738233 : Blo 215810 738233 := bstep (se 2 (by rfl) ⟨276837, by rfl⟩ : syracuseStep 738233 = 553675) B553675
theorem B934841 : Blo 215810 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B246919 : Blo 215810 246919 := bstep (se 1 (by rfl) ⟨185189, by rfl⟩ : syracuseStep 246919 = 370379) B370379
theorem B247099 : Blo 215810 247099 := bstep (se 1 (by rfl) ⟨185324, by rfl⟩ : syracuseStep 247099 = 370649) B370649
theorem B411065 : Blo 215810 411065 := bstep (se 2 (by rfl) ⟨154149, by rfl⟩ : syracuseStep 411065 = 308299) B308299
theorem B738827 : Blo 215810 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B1099331 : Blo 215810 1099331 := bstep (se 1 (by rfl) ⟨824498, by rfl⟩ : syracuseStep 1099331 = 1648997) B1648997
theorem B738935 : Blo 215810 738935 := bstep (se 1 (by rfl) ⟨554201, by rfl⟩ : syracuseStep 738935 = 1108403) B1108403
theorem B1099655 : Blo 215810 1099655 := bstep (se 1 (by rfl) ⟨824741, by rfl⟩ : syracuseStep 1099655 = 1649483) B1649483
theorem B739529 : Blo 215810 739529 := bstep (se 2 (by rfl) ⟨277323, by rfl⟩ : syracuseStep 739529 = 554647) B554647
theorem B936173 : Blo 215810 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B346427 : Blo 215810 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B1067411 : Blo 215810 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B4999715 : Blo 215810 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B412219 : Blo 215810 412219 := bstep (se 1 (by rfl) ⟨309164, by rfl⟩ : syracuseStep 412219 = 618329) B618329
theorem B936515 : Blo 215810 936515 := bstep (se 1 (by rfl) ⟨702386, by rfl⟩ : syracuseStep 936515 = 1404773) B1404773
theorem B1854029 : Blo 215810 1854029 := bstep (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) B695261
theorem B215815 : Blo 215810 215815 := bstep (se 1 (by rfl) ⟨161861, by rfl⟩ : syracuseStep 215815 = 323723) B323723
theorem B215823 : Blo 215810 215823 := bstep (se 1 (by rfl) ⟨161867, by rfl⟩ : syracuseStep 215823 = 323735) B323735
theorem B215867 : Blo 215810 215867 := bstep (se 1 (by rfl) ⟨161900, by rfl⟩ : syracuseStep 215867 = 323801) B323801
theorem B215943 : Blo 215810 215943 := bstep (se 1 (by rfl) ⟨161957, by rfl⟩ : syracuseStep 215943 = 323915) B323915
theorem B740231 : Blo 215810 740231 := bstep (se 1 (by rfl) ⟨555173, by rfl⟩ : syracuseStep 740231 = 1110347) B1110347
theorem B215951 : Blo 215810 215951 := bstep (se 1 (by rfl) ⟨161963, by rfl⟩ : syracuseStep 215951 = 323927) B323927
theorem B215995 : Blo 215810 215995 := bstep (se 1 (by rfl) ⟨161996, by rfl⟩ : syracuseStep 215995 = 323993) B323993
theorem B216071 : Blo 215810 216071 := bstep (se 1 (by rfl) ⟨162053, by rfl⟩ : syracuseStep 216071 = 324107) B324107
theorem B216079 : Blo 215810 216079 := bstep (se 1 (by rfl) ⟨162059, by rfl⟩ : syracuseStep 216079 = 324119) B324119
theorem B412705 : Blo 215810 412705 := bstep (se 2 (by rfl) ⟨154764, by rfl⟩ : syracuseStep 412705 = 309529) B309529
theorem B216123 : Blo 215810 216123 := bstep (se 1 (by rfl) ⟨162092, by rfl⟩ : syracuseStep 216123 = 324185) B324185
theorem B1002557 : Blo 215810 1002557 := bstep (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) B375959
theorem B216199 : Blo 215810 216199 := bstep (se 1 (by rfl) ⟨162149, by rfl⟩ : syracuseStep 216199 = 324299) B324299
theorem B216207 : Blo 215810 216207 := bstep (se 1 (by rfl) ⟨162155, by rfl⟩ : syracuseStep 216207 = 324311) B324311
theorem B2411693 : Blo 215810 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B216251 : Blo 215810 216251 := bstep (se 1 (by rfl) ⟨162188, by rfl⟩ : syracuseStep 216251 = 324377) B324377
theorem B740609 : Blo 215810 740609 := bstep (se 2 (by rfl) ⟨277728, by rfl⟩ : syracuseStep 740609 = 555457) B555457
theorem B216327 : Blo 215810 216327 := bstep (se 1 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 216327 = 324491) B324491
theorem B216335 : Blo 215810 216335 := bstep (se 1 (by rfl) ⟨162251, by rfl⟩ : syracuseStep 216335 = 324503) B324503
theorem B216379 : Blo 215810 216379 := bstep (se 1 (by rfl) ⟨162284, by rfl⟩ : syracuseStep 216379 = 324569) B324569
theorem B216455 : Blo 215810 216455 := bstep (se 1 (by rfl) ⟨162341, by rfl⟩ : syracuseStep 216455 = 324683) B324683
theorem B216463 : Blo 215810 216463 := bstep (se 1 (by rfl) ⟨162347, by rfl⟩ : syracuseStep 216463 = 324695) B324695
theorem B216507 : Blo 215810 216507 := bstep (se 1 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 216507 = 324761) B324761
theorem B347593 : Blo 215810 347593 := bstep (se 2 (by rfl) ⟨130347, by rfl⟩ : syracuseStep 347593 = 260695) B260695
theorem B216583 : Blo 215810 216583 := bstep (se 1 (by rfl) ⟨162437, by rfl⟩ : syracuseStep 216583 = 324875) B324875
theorem B216591 : Blo 215810 216591 := bstep (se 1 (by rfl) ⟨162443, by rfl⟩ : syracuseStep 216591 = 324887) B324887
theorem B216635 : Blo 215810 216635 := bstep (se 1 (by rfl) ⟨162476, by rfl⟩ : syracuseStep 216635 = 324953) B324953
theorem B216711 : Blo 215810 216711 := bstep (se 1 (by rfl) ⟨162533, by rfl⟩ : syracuseStep 216711 = 325067) B325067
theorem B216719 : Blo 215810 216719 := bstep (se 1 (by rfl) ⟨162539, by rfl⟩ : syracuseStep 216719 = 325079) B325079
theorem B315023 : Blo 215810 315023 := bstep (se 1 (by rfl) ⟨236267, by rfl⟩ : syracuseStep 315023 = 472535) B472535
theorem B216763 : Blo 215810 216763 := bstep (se 1 (by rfl) ⟨162572, by rfl⟩ : syracuseStep 216763 = 325145) B325145
theorem B6311681 : Blo 215810 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B216839 : Blo 215810 216839 := bstep (se 1 (by rfl) ⟨162629, by rfl⟩ : syracuseStep 216839 = 325259) B325259
theorem B216847 : Blo 215810 216847 := bstep (se 1 (by rfl) ⟨162635, by rfl⟩ : syracuseStep 216847 = 325271) B325271
theorem B216891 : Blo 215810 216891 := bstep (se 1 (by rfl) ⟨162668, by rfl⟩ : syracuseStep 216891 = 325337) B325337
theorem B216967 : Blo 215810 216967 := bstep (se 1 (by rfl) ⟨162725, by rfl⟩ : syracuseStep 216967 = 325451) B325451
theorem B216975 : Blo 215810 216975 := bstep (se 1 (by rfl) ⟨162731, by rfl⟩ : syracuseStep 216975 = 325463) B325463
theorem B217019 : Blo 215810 217019 := bstep (se 1 (by rfl) ⟨162764, by rfl⟩ : syracuseStep 217019 = 325529) B325529
theorem B217095 : Blo 215810 217095 := bstep (se 1 (by rfl) ⟨162821, by rfl⟩ : syracuseStep 217095 = 325643) B325643
theorem B217103 : Blo 215810 217103 := bstep (se 1 (by rfl) ⟨162827, by rfl⟩ : syracuseStep 217103 = 325655) B325655
theorem B741419 : Blo 215810 741419 := bstep (se 1 (by rfl) ⟨556064, by rfl⟩ : syracuseStep 741419 = 1112129) B1112129
theorem B217147 : Blo 215810 217147 := bstep (se 1 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 217147 = 325721) B325721
theorem B217223 : Blo 215810 217223 := bstep (se 1 (by rfl) ⟨162917, by rfl⟩ : syracuseStep 217223 = 325835) B325835
theorem B217231 : Blo 215810 217231 := bstep (se 1 (by rfl) ⟨162923, by rfl⟩ : syracuseStep 217231 = 325847) B325847
theorem B217275 : Blo 215810 217275 := bstep (se 1 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 217275 = 325913) B325913
theorem B217351 : Blo 215810 217351 := bstep (se 1 (by rfl) ⟨163013, by rfl⟩ : syracuseStep 217351 = 326027) B326027
theorem B217359 : Blo 215810 217359 := bstep (se 1 (by rfl) ⟨163019, by rfl⟩ : syracuseStep 217359 = 326039) B326039
theorem B414011 : Blo 215810 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B217403 : Blo 215810 217403 := bstep (se 1 (by rfl) ⟨163052, by rfl⟩ : syracuseStep 217403 = 326105) B326105
theorem B1986875 : Blo 215810 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B217479 : Blo 215810 217479 := bstep (se 1 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 217479 = 326219) B326219
theorem B217487 : Blo 215810 217487 := bstep (se 1 (by rfl) ⟨163115, by rfl⟩ : syracuseStep 217487 = 326231) B326231
theorem B2806163 : Blo 215810 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B217531 : Blo 215810 217531 := bstep (se 1 (by rfl) ⟨163148, by rfl⟩ : syracuseStep 217531 = 326297) B326297
theorem B217607 : Blo 215810 217607 := bstep (se 1 (by rfl) ⟨163205, by rfl⟩ : syracuseStep 217607 = 326411) B326411
theorem B217615 : Blo 215810 217615 := bstep (se 1 (by rfl) ⟨163211, by rfl⟩ : syracuseStep 217615 = 326423) B326423
theorem B217659 : Blo 215810 217659 := bstep (se 1 (by rfl) ⟨163244, by rfl⟩ : syracuseStep 217659 = 326489) B326489
theorem B217735 : Blo 215810 217735 := bstep (se 1 (by rfl) ⟨163301, by rfl⟩ : syracuseStep 217735 = 326603) B326603
theorem B217743 : Blo 215810 217743 := bstep (se 1 (by rfl) ⟨163307, by rfl⟩ : syracuseStep 217743 = 326615) B326615
theorem B217787 : Blo 215810 217787 := bstep (se 1 (by rfl) ⟨163340, by rfl⟩ : syracuseStep 217787 = 326681) B326681
theorem B217863 : Blo 215810 217863 := bstep (se 1 (by rfl) ⟨163397, by rfl⟩ : syracuseStep 217863 = 326795) B326795
theorem B217871 : Blo 215810 217871 := bstep (se 1 (by rfl) ⟨163403, by rfl⟩ : syracuseStep 217871 = 326807) B326807
theorem B1332001 : Blo 215810 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B414497 : Blo 215810 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B217915 : Blo 215810 217915 := bstep (se 1 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 217915 = 326873) B326873
theorem B217991 : Blo 215810 217991 := bstep (se 1 (by rfl) ⟨163493, by rfl⟩ : syracuseStep 217991 = 326987) B326987
theorem B217999 : Blo 215810 217999 := bstep (se 1 (by rfl) ⟨163499, by rfl⟩ : syracuseStep 217999 = 326999) B326999
theorem B414649 : Blo 215810 414649 := bstep (se 2 (by rfl) ⟨155493, by rfl⟩ : syracuseStep 414649 = 310987) B310987
theorem B218043 : Blo 215810 218043 := bstep (se 1 (by rfl) ⟨163532, by rfl⟩ : syracuseStep 218043 = 327065) B327065
theorem B218119 : Blo 215810 218119 := bstep (se 1 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 218119 = 327179) B327179
theorem B218127 : Blo 215810 218127 := bstep (se 1 (by rfl) ⟨163595, by rfl⟩ : syracuseStep 218127 = 327191) B327191
theorem B218171 : Blo 215810 218171 := bstep (se 1 (by rfl) ⟨163628, by rfl⟩ : syracuseStep 218171 = 327257) B327257
theorem B218247 : Blo 215810 218247 := bstep (se 1 (by rfl) ⟨163685, by rfl⟩ : syracuseStep 218247 = 327371) B327371
theorem B218255 : Blo 215810 218255 := bstep (se 1 (by rfl) ⟨163691, by rfl⟩ : syracuseStep 218255 = 327383) B327383
theorem B218299 : Blo 215810 218299 := bstep (se 1 (by rfl) ⟨163724, by rfl⟩ : syracuseStep 218299 = 327449) B327449
theorem B1037549 : Blo 215810 1037549 := bstep (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) B389081
theorem B218375 : Blo 215810 218375 := bstep (se 1 (by rfl) ⟨163781, by rfl⟩ : syracuseStep 218375 = 327563) B327563
theorem B218383 : Blo 215810 218383 := bstep (se 1 (by rfl) ⟨163787, by rfl⟩ : syracuseStep 218383 = 327575) B327575
theorem B677179 : Blo 215810 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B218427 : Blo 215810 218427 := bstep (se 1 (by rfl) ⟨163820, by rfl⟩ : syracuseStep 218427 = 327641) B327641
theorem B1103219 : Blo 215810 1103219 := bstep (se 1 (by rfl) ⟨827414, by rfl⟩ : syracuseStep 1103219 = 1654829) B1654829
theorem B218503 : Blo 215810 218503 := bstep (se 1 (by rfl) ⟨163877, by rfl⟩ : syracuseStep 218503 = 327755) B327755
theorem B218511 : Blo 215810 218511 := bstep (se 1 (by rfl) ⟨163883, by rfl⟩ : syracuseStep 218511 = 327767) B327767
theorem B1398161 : Blo 215810 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B218555 : Blo 215810 218555 := bstep (se 1 (by rfl) ⟨163916, by rfl⟩ : syracuseStep 218555 = 327833) B327833
theorem B1234379 : Blo 215810 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B218631 : Blo 215810 218631 := bstep (se 1 (by rfl) ⟨163973, by rfl⟩ : syracuseStep 218631 = 327947) B327947
theorem B218639 : Blo 215810 218639 := bstep (se 1 (by rfl) ⟨163979, by rfl⟩ : syracuseStep 218639 = 327959) B327959
theorem B218683 : Blo 215810 218683 := bstep (se 1 (by rfl) ⟨164012, by rfl⟩ : syracuseStep 218683 = 328025) B328025
theorem B251527 : Blo 215810 251527 := bstep (se 1 (by rfl) ⟨188645, by rfl⟩ : syracuseStep 251527 = 377291) B377291
theorem B218759 : Blo 215810 218759 := bstep (se 1 (by rfl) ⟨164069, by rfl⟩ : syracuseStep 218759 = 328139) B328139
theorem B218767 : Blo 215810 218767 := bstep (se 1 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 218767 = 328151) B328151
theorem B218811 : Blo 215810 218811 := bstep (se 1 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 218811 = 328217) B328217
theorem B2643673 : Blo 215810 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B218887 : Blo 215810 218887 := bstep (se 1 (by rfl) ⟨164165, by rfl⟩ : syracuseStep 218887 = 328331) B328331
theorem B218895 : Blo 215810 218895 := bstep (se 1 (by rfl) ⟨164171, by rfl⟩ : syracuseStep 218895 = 328343) B328343
theorem B218939 : Blo 215810 218939 := bstep (se 1 (by rfl) ⟨164204, by rfl⟩ : syracuseStep 218939 = 328409) B328409
theorem B1103705 : Blo 215810 1103705 := bstep (se 2 (by rfl) ⟨413889, by rfl⟩ : syracuseStep 1103705 = 827779) B827779
theorem B219015 : Blo 215810 219015 := bstep (se 1 (by rfl) ⟨164261, by rfl⟩ : syracuseStep 219015 = 328523) B328523
theorem B219023 : Blo 215810 219023 := bstep (se 1 (by rfl) ⟨164267, by rfl⟩ : syracuseStep 219023 = 328535) B328535
theorem B1234835 : Blo 215810 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B219067 : Blo 215810 219067 := bstep (se 1 (by rfl) ⟨164300, by rfl⟩ : syracuseStep 219067 = 328601) B328601
theorem B3790795 : Blo 215810 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B219143 : Blo 215810 219143 := bstep (se 1 (by rfl) ⟨164357, by rfl⟩ : syracuseStep 219143 = 328715) B328715
theorem B219151 : Blo 215810 219151 := bstep (se 1 (by rfl) ⟨164363, by rfl⟩ : syracuseStep 219151 = 328727) B328727
theorem B219195 : Blo 215810 219195 := bstep (se 1 (by rfl) ⟨164396, by rfl⟩ : syracuseStep 219195 = 328793) B328793
theorem B219271 : Blo 215810 219271 := bstep (se 1 (by rfl) ⟨164453, by rfl⟩ : syracuseStep 219271 = 328907) B328907
theorem B219279 : Blo 215810 219279 := bstep (se 1 (by rfl) ⟨164459, by rfl⟩ : syracuseStep 219279 = 328919) B328919
theorem B219323 : Blo 215810 219323 := bstep (se 1 (by rfl) ⟨164492, by rfl⟩ : syracuseStep 219323 = 328985) B328985
theorem B219399 : Blo 215810 219399 := bstep (se 1 (by rfl) ⟨164549, by rfl⟩ : syracuseStep 219399 = 329099) B329099
theorem B219407 : Blo 215810 219407 := bstep (se 1 (by rfl) ⟨164555, by rfl⟩ : syracuseStep 219407 = 329111) B329111
theorem B219451 : Blo 215810 219451 := bstep (se 1 (by rfl) ⟨164588, by rfl⟩ : syracuseStep 219451 = 329177) B329177
theorem B219527 : Blo 215810 219527 := bstep (se 1 (by rfl) ⟨164645, by rfl⟩ : syracuseStep 219527 = 329291) B329291
theorem B219535 : Blo 215810 219535 := bstep (se 1 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 219535 = 329303) B329303
theorem B219579 : Blo 215810 219579 := bstep (se 1 (by rfl) ⟨164684, by rfl⟩ : syracuseStep 219579 = 329369) B329369
theorem B219655 : Blo 215810 219655 := bstep (se 1 (by rfl) ⟨164741, by rfl⟩ : syracuseStep 219655 = 329483) B329483
theorem B219663 : Blo 215810 219663 := bstep (se 1 (by rfl) ⟨164747, by rfl⟩ : syracuseStep 219663 = 329495) B329495
theorem B219707 : Blo 215810 219707 := bstep (se 1 (by rfl) ⟨164780, by rfl⟩ : syracuseStep 219707 = 329561) B329561
theorem B219783 : Blo 215810 219783 := bstep (se 1 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 219783 = 329675) B329675
theorem B219791 : Blo 215810 219791 := bstep (se 1 (by rfl) ⟨164843, by rfl⟩ : syracuseStep 219791 = 329687) B329687
theorem B416441 : Blo 215810 416441 := bstep (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) B312331
theorem B1661633 : Blo 215810 1661633 := bstep (se 2 (by rfl) ⟨623112, by rfl⟩ : syracuseStep 1661633 = 1246225) B1246225
theorem B1334225 : Blo 215810 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B547955 : Blo 215810 547955 := bstep (se 1 (by rfl) ⟨410966, by rfl⟩ : syracuseStep 547955 = 821933) B821933
theorem B548471 : Blo 215810 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B843635 : Blo 215810 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B1105811 : Blo 215810 1105811 := bstep (se 1 (by rfl) ⟨829358, by rfl⟩ : syracuseStep 1105811 = 1658717) B1658717
theorem B778193 : Blo 215810 778193 := bstep (se 2 (by rfl) ⟨291822, by rfl⟩ : syracuseStep 778193 = 583645) B583645
theorem B1171745 : Blo 215810 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B5005633 : Blo 215810 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B2089475 : Blo 215810 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1335869 : Blo 215810 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B549463 : Blo 215810 549463 := bstep (se 1 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 549463 = 824195) B824195
theorem B549767 : Blo 215810 549767 := bstep (se 1 (by rfl) ⟨412325, by rfl⟩ : syracuseStep 549767 = 824651) B824651
theorem B1172369 : Blo 215810 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B549899 : Blo 215810 549899 := bstep (se 1 (by rfl) ⟨412424, by rfl⟩ : syracuseStep 549899 = 824849) B824849
theorem B615539 : Blo 215810 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B1697057 : Blo 215810 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B1172825 : Blo 215810 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B615937 : Blo 215810 615937 := bstep (se 2 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 615937 = 461953) B461953
theorem B550415 : Blo 215810 550415 := bstep (se 1 (by rfl) ⟨412811, by rfl⟩ : syracuseStep 550415 = 825623) B825623
theorem B615995 : Blo 215810 615995 := bstep (se 1 (by rfl) ⟨461996, by rfl⟩ : syracuseStep 615995 = 923993) B923993
theorem B779863 : Blo 215810 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B550547 : Blo 215810 550547 := bstep (se 1 (by rfl) ⟨412910, by rfl⟩ : syracuseStep 550547 = 825821) B825821
theorem B1140689 : Blo 215810 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B1665035 : Blo 215810 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B485675 : Blo 215810 485675 := bstep (se 1 (by rfl) ⟨364256, by rfl⟩ : syracuseStep 485675 = 728513) B728513
theorem B1042739 : Blo 215810 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B518699 : Blo 215810 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B486035 : Blo 215810 486035 := bstep (se 1 (by rfl) ⟨364526, by rfl⟩ : syracuseStep 486035 = 729053) B729053
theorem B486089 : Blo 215810 486089 := bstep (se 2 (by rfl) ⟨182283, by rfl⟩ : syracuseStep 486089 = 364567) B364567
theorem B551681 : Blo 215810 551681 := bstep (se 2 (by rfl) ⟨206880, by rfl⟩ : syracuseStep 551681 = 413761) B413761
theorem B2779919 : Blo 215810 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B3140441 : Blo 215810 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B1108889 : Blo 215810 1108889 := bstep (se 2 (by rfl) ⟨415833, by rfl⟩ : syracuseStep 1108889 = 831667) B831667
theorem B3140669 : Blo 215810 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B552055 : Blo 215810 552055 := bstep (se 1 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 552055 = 828083) B828083
theorem B486791 : Blo 215810 486791 := bstep (se 1 (by rfl) ⟨365093, by rfl⟩ : syracuseStep 486791 = 730187) B730187
theorem B552491 : Blo 215810 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B486971 : Blo 215810 486971 := bstep (se 1 (by rfl) ⟨365228, by rfl⟩ : syracuseStep 486971 = 730457) B730457
theorem B3731021 : Blo 215810 3731021 := bstep (se 3 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 3731021 = 1399133) B1399133
theorem B487097 : Blo 215810 487097 := bstep (se 2 (by rfl) ⟨182661, by rfl⟩ : syracuseStep 487097 = 365323) B365323
theorem B945935 : Blo 215810 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B618283 : Blo 215810 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B5369753 : Blo 215810 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B2813849 : Blo 215810 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1666979 : Blo 215810 1666979 := bstep (se 1 (by rfl) ⟨1250234, by rfl⟩ : syracuseStep 1666979 = 2500469) B2500469
theorem B487439 : Blo 215810 487439 := bstep (se 1 (by rfl) ⟨365579, by rfl⟩ : syracuseStep 487439 = 731159) B731159
theorem B618511 : Blo 215810 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B487457 : Blo 215810 487457 := bstep (se 2 (by rfl) ⟨182796, by rfl⟩ : syracuseStep 487457 = 365593) B365593
theorem B323771 : Blo 215810 323771 := bstep (se 1 (by rfl) ⟨242828, by rfl⟩ : syracuseStep 323771 = 485657) B485657
theorem B323831 : Blo 215810 323831 := bstep (se 1 (by rfl) ⟨242873, by rfl⟩ : syracuseStep 323831 = 485747) B485747
theorem B323855 : Blo 215810 323855 := bstep (se 1 (by rfl) ⟨242891, by rfl⟩ : syracuseStep 323855 = 485783) B485783
theorem B913697 : Blo 215810 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B618785 : Blo 215810 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B323897 : Blo 215810 323897 := bstep (se 2 (by rfl) ⟨121461, by rfl⟩ : syracuseStep 323897 = 242923) B242923
theorem B553331 : Blo 215810 553331 := bstep (se 1 (by rfl) ⟨414998, by rfl⟩ : syracuseStep 553331 = 829997) B829997
theorem B487799 : Blo 215810 487799 := bstep (se 1 (by rfl) ⟨365849, by rfl⟩ : syracuseStep 487799 = 731699) B731699
theorem B323975 : Blo 215810 323975 := bstep (se 1 (by rfl) ⟨242981, by rfl⟩ : syracuseStep 323975 = 485963) B485963
theorem B553351 : Blo 215810 553351 := bstep (se 1 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 553351 = 830027) B830027
theorem B1503623 : Blo 215810 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B324011 : Blo 215810 324011 := bstep (se 1 (by rfl) ⟨243008, by rfl⟩ : syracuseStep 324011 = 486017) B486017
theorem B324041 : Blo 215810 324041 := bstep (se 2 (by rfl) ⟨121515, by rfl⟩ : syracuseStep 324041 = 243031) B243031
theorem B487979 : Blo 215810 487979 := bstep (se 1 (by rfl) ⟨365984, by rfl⟩ : syracuseStep 487979 = 731969) B731969
theorem B324155 : Blo 215810 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B881239 : Blo 215810 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B324215 : Blo 215810 324215 := bstep (se 1 (by rfl) ⟨243161, by rfl⟩ : syracuseStep 324215 = 486323) B486323
theorem B619127 : Blo 215810 619127 := bstep (se 1 (by rfl) ⟨464345, by rfl⟩ : syracuseStep 619127 = 928691) B928691
theorem B324239 : Blo 215810 324239 := bstep (se 1 (by rfl) ⟨243179, by rfl⟩ : syracuseStep 324239 = 486359) B486359
theorem B553625 : Blo 215810 553625 := bstep (se 2 (by rfl) ⟨207609, by rfl⟩ : syracuseStep 553625 = 415219) B415219
theorem B324281 : Blo 215810 324281 := bstep (se 2 (by rfl) ⟨121605, by rfl⟩ : syracuseStep 324281 = 243211) B243211
theorem B324359 : Blo 215810 324359 := bstep (se 1 (by rfl) ⟨243269, by rfl⟩ : syracuseStep 324359 = 486539) B486539
theorem B324395 : Blo 215810 324395 := bstep (se 1 (by rfl) ⟨243296, by rfl⟩ : syracuseStep 324395 = 486593) B486593
theorem B553787 : Blo 215810 553787 := bstep (se 1 (by rfl) ⟨415340, by rfl⟩ : syracuseStep 553787 = 830681) B830681
theorem B389947 : Blo 215810 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B324425 : Blo 215810 324425 := bstep (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) B243319
theorem B488339 : Blo 215810 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B324539 : Blo 215810 324539 := bstep (se 1 (by rfl) ⟨243404, by rfl⟩ : syracuseStep 324539 = 486809) B486809
theorem B488393 : Blo 215810 488393 := bstep (se 2 (by rfl) ⟨183147, by rfl⟩ : syracuseStep 488393 = 366295) B366295
theorem B324599 : Blo 215810 324599 := bstep (se 1 (by rfl) ⟨243449, by rfl⟩ : syracuseStep 324599 = 486899) B486899
theorem B1045507 : Blo 215810 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B324623 : Blo 215810 324623 := bstep (se 1 (by rfl) ⟨243467, by rfl⟩ : syracuseStep 324623 = 486935) B486935
theorem B553999 : Blo 215810 553999 := bstep (se 1 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 553999 = 830999) B830999
theorem B1045547 : Blo 215810 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B324665 : Blo 215810 324665 := bstep (se 2 (by rfl) ⟨121749, by rfl⟩ : syracuseStep 324665 = 243499) B243499
theorem B324743 : Blo 215810 324743 := bstep (se 1 (by rfl) ⟨243557, by rfl⟩ : syracuseStep 324743 = 487115) B487115
theorem B324779 : Blo 215810 324779 := bstep (se 1 (by rfl) ⟨243584, by rfl⟩ : syracuseStep 324779 = 487169) B487169
theorem B390329 : Blo 215810 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B324809 : Blo 215810 324809 := bstep (se 2 (by rfl) ⟨121803, by rfl⟩ : syracuseStep 324809 = 243607) B243607
theorem B619787 : Blo 215810 619787 := bstep (se 1 (by rfl) ⟨464840, by rfl⟩ : syracuseStep 619787 = 929681) B929681
theorem B554273 : Blo 215810 554273 := bstep (se 2 (by rfl) ⟨207852, by rfl⟩ : syracuseStep 554273 = 415705) B415705
theorem B1176869 : Blo 215810 1176869 := bstep (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) B220663
theorem B587051 : Blo 215810 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B324923 : Blo 215810 324923 := bstep (se 1 (by rfl) ⟨243692, by rfl⟩ : syracuseStep 324923 = 487385) B487385
theorem B324983 : Blo 215810 324983 := bstep (se 1 (by rfl) ⟨243737, by rfl⟩ : syracuseStep 324983 = 487475) B487475
theorem B325007 : Blo 215810 325007 := bstep (se 1 (by rfl) ⟨243755, by rfl⟩ : syracuseStep 325007 = 487511) B487511
theorem B325049 : Blo 215810 325049 := bstep (se 2 (by rfl) ⟨121893, by rfl⟩ : syracuseStep 325049 = 243787) B243787
theorem B1111481 : Blo 215810 1111481 := bstep (se 2 (by rfl) ⟨416805, by rfl⟩ : syracuseStep 1111481 = 833611) B833611
theorem B325127 : Blo 215810 325127 := bstep (se 1 (by rfl) ⟨243845, by rfl⟩ : syracuseStep 325127 = 487691) B487691
theorem B325163 : Blo 215810 325163 := bstep (se 1 (by rfl) ⟨243872, by rfl⟩ : syracuseStep 325163 = 487745) B487745
theorem B325193 : Blo 215810 325193 := bstep (se 2 (by rfl) ⟨121947, by rfl⟩ : syracuseStep 325193 = 243895) B243895
theorem B489095 : Blo 215810 489095 := bstep (se 1 (by rfl) ⟨366821, by rfl⟩ : syracuseStep 489095 = 733643) B733643
theorem B3700403 : Blo 215810 3700403 := bstep (se 1 (by rfl) ⟨2775302, by rfl⟩ : syracuseStep 3700403 = 5550605) B5550605
theorem B587449 : Blo 215810 587449 := bstep (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) B440587
theorem B325307 : Blo 215810 325307 := bstep (se 1 (by rfl) ⟨243980, by rfl⟩ : syracuseStep 325307 = 487961) B487961
theorem B325367 : Blo 215810 325367 := bstep (se 1 (by rfl) ⟨244025, by rfl⟩ : syracuseStep 325367 = 488051) B488051
theorem B325391 : Blo 215810 325391 := bstep (se 1 (by rfl) ⟨244043, by rfl⟩ : syracuseStep 325391 = 488087) B488087
theorem B1767217 : Blo 215810 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B325433 : Blo 215810 325433 := bstep (se 2 (by rfl) ⟨122037, by rfl⟩ : syracuseStep 325433 = 244075) B244075
theorem B489275 : Blo 215810 489275 := bstep (se 1 (by rfl) ⟨366956, by rfl⟩ : syracuseStep 489275 = 733913) B733913
theorem B325511 : Blo 215810 325511 := bstep (se 1 (by rfl) ⟨244133, by rfl⟩ : syracuseStep 325511 = 488267) B488267
theorem B325547 : Blo 215810 325547 := bstep (se 1 (by rfl) ⟨244160, by rfl⟩ : syracuseStep 325547 = 488321) B488321
theorem B489401 : Blo 215810 489401 := bstep (se 2 (by rfl) ⟨183525, by rfl⟩ : syracuseStep 489401 = 367051) B367051
theorem B325577 : Blo 215810 325577 := bstep (se 2 (by rfl) ⟨122091, by rfl⟩ : syracuseStep 325577 = 244183) B244183
theorem B522283 : Blo 215810 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B325691 : Blo 215810 325691 := bstep (se 1 (by rfl) ⟨244268, by rfl⟩ : syracuseStep 325691 = 488537) B488537
theorem B2652277 : Blo 215810 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B325751 : Blo 215810 325751 := bstep (se 1 (by rfl) ⟨244313, by rfl⟩ : syracuseStep 325751 = 488627) B488627
theorem B325775 : Blo 215810 325775 := bstep (se 1 (by rfl) ⟨244331, by rfl⟩ : syracuseStep 325775 = 488663) B488663
theorem B1243309 : Blo 215810 1243309 := bstep (se 3 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 1243309 = 466241) B466241
theorem B325817 : Blo 215810 325817 := bstep (se 2 (by rfl) ⟨122181, by rfl⟩ : syracuseStep 325817 = 244363) B244363
theorem B325895 : Blo 215810 325895 := bstep (se 1 (by rfl) ⟨244421, by rfl⟩ : syracuseStep 325895 = 488843) B488843
theorem B555275 : Blo 215810 555275 := bstep (se 1 (by rfl) ⟨416456, by rfl⟩ : syracuseStep 555275 = 832913) B832913
theorem B489743 : Blo 215810 489743 := bstep (se 1 (by rfl) ⟨367307, by rfl⟩ : syracuseStep 489743 = 734615) B734615
theorem B489761 : Blo 215810 489761 := bstep (se 2 (by rfl) ⟨183660, by rfl⟩ : syracuseStep 489761 = 367321) B367321
theorem B325931 : Blo 215810 325931 := bstep (se 1 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 325931 = 488897) B488897
theorem B325961 : Blo 215810 325961 := bstep (se 2 (by rfl) ⟨122235, by rfl⟩ : syracuseStep 325961 = 244471) B244471
theorem B326075 : Blo 215810 326075 := bstep (se 1 (by rfl) ⟨244556, by rfl⟩ : syracuseStep 326075 = 489113) B489113
theorem B326135 : Blo 215810 326135 := bstep (se 1 (by rfl) ⟨244601, by rfl⟩ : syracuseStep 326135 = 489203) B489203
theorem B326159 : Blo 215810 326159 := bstep (se 1 (by rfl) ⟨244619, by rfl⟩ : syracuseStep 326159 = 489239) B489239
theorem B326201 : Blo 215810 326201 := bstep (se 2 (by rfl) ⟨122325, by rfl⟩ : syracuseStep 326201 = 244651) B244651
theorem B490103 : Blo 215810 490103 := bstep (se 1 (by rfl) ⟨367577, by rfl⟩ : syracuseStep 490103 = 735155) B735155
theorem B326279 : Blo 215810 326279 := bstep (se 1 (by rfl) ⟨244709, by rfl⟩ : syracuseStep 326279 = 489419) B489419
theorem B522899 : Blo 215810 522899 := bstep (se 1 (by rfl) ⟨392174, by rfl⟩ : syracuseStep 522899 = 784349) B784349
theorem B326315 : Blo 215810 326315 := bstep (se 1 (by rfl) ⟨244736, by rfl⟩ : syracuseStep 326315 = 489473) B489473
theorem B326345 : Blo 215810 326345 := bstep (se 2 (by rfl) ⟨122379, by rfl⟩ : syracuseStep 326345 = 244759) B244759
theorem B1112777 : Blo 215810 1112777 := bstep (se 2 (by rfl) ⟨417291, by rfl⟩ : syracuseStep 1112777 = 834583) B834583
theorem B490283 : Blo 215810 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B326459 : Blo 215810 326459 := bstep (se 1 (by rfl) ⟨244844, by rfl⟩ : syracuseStep 326459 = 489689) B489689
theorem B621371 : Blo 215810 621371 := bstep (se 1 (by rfl) ⟨466028, by rfl⟩ : syracuseStep 621371 = 932057) B932057
theorem B621427 : Blo 215810 621427 := bstep (se 1 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 621427 = 932141) B932141
theorem B326519 : Blo 215810 326519 := bstep (se 1 (by rfl) ⟨244889, by rfl⟩ : syracuseStep 326519 = 489779) B489779
theorem B326543 : Blo 215810 326543 := bstep (se 1 (by rfl) ⟨244907, by rfl⟩ : syracuseStep 326543 = 489815) B489815
theorem B555923 : Blo 215810 555923 := bstep (se 1 (by rfl) ⟨416942, by rfl⟩ : syracuseStep 555923 = 833885) B833885
theorem B326585 : Blo 215810 326585 := bstep (se 2 (by rfl) ⟨122469, by rfl⟩ : syracuseStep 326585 = 244939) B244939
theorem B1047505 : Blo 215810 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B326663 : Blo 215810 326663 := bstep (se 1 (by rfl) ⟨244997, by rfl⟩ : syracuseStep 326663 = 489995) B489995
theorem B326699 : Blo 215810 326699 := bstep (se 1 (by rfl) ⟨245024, by rfl⟩ : syracuseStep 326699 = 490049) B490049
theorem B326729 : Blo 215810 326729 := bstep (se 2 (by rfl) ⟨122523, by rfl⟩ : syracuseStep 326729 = 245047) B245047
theorem B490643 : Blo 215810 490643 := bstep (se 1 (by rfl) ⟨367982, by rfl⟩ : syracuseStep 490643 = 735965) B735965
theorem B588953 : Blo 215810 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B556217 : Blo 215810 556217 := bstep (se 2 (by rfl) ⟨208581, by rfl⟩ : syracuseStep 556217 = 417163) B417163
theorem B326843 : Blo 215810 326843 := bstep (se 1 (by rfl) ⟨245132, by rfl⟩ : syracuseStep 326843 = 490265) B490265
theorem B490697 : Blo 215810 490697 := bstep (se 2 (by rfl) ⟨184011, by rfl⟩ : syracuseStep 490697 = 368023) B368023
theorem B621769 : Blo 215810 621769 := bstep (se 2 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 621769 = 466327) B466327
theorem B326903 : Blo 215810 326903 := bstep (se 1 (by rfl) ⟨245177, by rfl⟩ : syracuseStep 326903 = 490355) B490355
theorem B326927 : Blo 215810 326927 := bstep (se 1 (by rfl) ⟨245195, by rfl⟩ : syracuseStep 326927 = 490391) B490391
theorem B326969 : Blo 215810 326969 := bstep (se 2 (by rfl) ⟨122613, by rfl⟩ : syracuseStep 326969 = 245227) B245227
theorem B327047 : Blo 215810 327047 := bstep (se 1 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 327047 = 490571) B490571
theorem B327083 : Blo 215810 327083 := bstep (se 1 (by rfl) ⟨245312, by rfl⟩ : syracuseStep 327083 = 490625) B490625
theorem B327113 : Blo 215810 327113 := bstep (se 2 (by rfl) ⟨122667, by rfl⟩ : syracuseStep 327113 = 245335) B245335
theorem B327227 : Blo 215810 327227 := bstep (se 1 (by rfl) ⟨245420, by rfl⟩ : syracuseStep 327227 = 490841) B490841
theorem B327287 : Blo 215810 327287 := bstep (se 1 (by rfl) ⟨245465, by rfl⟩ : syracuseStep 327287 = 490931) B490931
theorem B327311 : Blo 215810 327311 := bstep (se 1 (by rfl) ⟨245483, by rfl⟩ : syracuseStep 327311 = 490967) B490967
theorem B327353 : Blo 215810 327353 := bstep (se 2 (by rfl) ⟨122757, by rfl⟩ : syracuseStep 327353 = 245515) B245515
theorem B327431 : Blo 215810 327431 := bstep (se 1 (by rfl) ⟨245573, by rfl⟩ : syracuseStep 327431 = 491147) B491147
theorem B327467 : Blo 215810 327467 := bstep (se 1 (by rfl) ⟨245600, by rfl⟩ : syracuseStep 327467 = 491201) B491201
theorem B327497 : Blo 215810 327497 := bstep (se 2 (by rfl) ⟨122811, by rfl⟩ : syracuseStep 327497 = 245623) B245623
theorem B589655 : Blo 215810 589655 := bstep (se 1 (by rfl) ⟨442241, by rfl⟩ : syracuseStep 589655 = 884483) B884483
theorem B491399 : Blo 215810 491399 := bstep (se 1 (by rfl) ⟨368549, by rfl⟩ : syracuseStep 491399 = 737099) B737099
theorem B2490263 : Blo 215810 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B327611 : Blo 215810 327611 := bstep (se 1 (by rfl) ⟨245708, by rfl⟩ : syracuseStep 327611 = 491417) B491417
theorem B327671 : Blo 215810 327671 := bstep (se 1 (by rfl) ⟨245753, by rfl⟩ : syracuseStep 327671 = 491507) B491507
theorem B327689 : Blo 215810 327689 := bstep (se 2 (by rfl) ⟨122883, by rfl⟩ : syracuseStep 327689 = 245767) B245767
theorem B327719 : Blo 215810 327719 := bstep (se 1 (by rfl) ⟨245789, by rfl⟩ : syracuseStep 327719 = 491579) B491579
theorem B327803 : Blo 215810 327803 := bstep (se 1 (by rfl) ⟨245852, by rfl⟩ : syracuseStep 327803 = 491705) B491705
theorem B327929 : Blo 215810 327929 := bstep (se 2 (by rfl) ⟨122973, by rfl⟩ : syracuseStep 327929 = 245947) B245947
theorem B819517 : Blo 215810 819517 := bstep (se 3 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 819517 = 307319) B307319
theorem B328031 : Blo 215810 328031 := bstep (se 1 (by rfl) ⟨246023, by rfl⟩ : syracuseStep 328031 = 492047) B492047
theorem B328043 : Blo 215810 328043 := bstep (se 1 (by rfl) ⟨246032, by rfl⟩ : syracuseStep 328043 = 492065) B492065
theorem B9372185 : Blo 215810 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B328271 : Blo 215810 328271 := bstep (se 1 (by rfl) ⟨246203, by rfl⟩ : syracuseStep 328271 = 492407) B492407
theorem B492155 : Blo 215810 492155 := bstep (se 1 (by rfl) ⟨369116, by rfl⟩ : syracuseStep 492155 = 738233) B738233
theorem B623227 : Blo 215810 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B328391 : Blo 215810 328391 := bstep (se 1 (by rfl) ⟨246293, by rfl⟩ : syracuseStep 328391 = 492587) B492587
theorem B492281 : Blo 215810 492281 := bstep (se 2 (by rfl) ⟨184605, by rfl⟩ : syracuseStep 492281 = 369211) B369211
theorem B328553 : Blo 215810 328553 := bstep (se 2 (by rfl) ⟨123207, by rfl⟩ : syracuseStep 328553 = 246415) B246415
theorem B328631 : Blo 215810 328631 := bstep (se 1 (by rfl) ⟨246473, by rfl⟩ : syracuseStep 328631 = 492947) B492947
theorem B328667 : Blo 215810 328667 := bstep (se 1 (by rfl) ⟨246500, by rfl⟩ : syracuseStep 328667 = 493001) B493001
theorem B1180673 : Blo 215810 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B492551 : Blo 215810 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B787475 : Blo 215810 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B590867 : Blo 215810 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B492623 : Blo 215810 492623 := bstep (se 1 (by rfl) ⟨369467, by rfl⟩ : syracuseStep 492623 = 738935) B738935
theorem B7013573 : Blo 215810 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B329135 : Blo 215810 329135 := bstep (se 1 (by rfl) ⟨246851, by rfl⟩ : syracuseStep 329135 = 493703) B493703
theorem B493019 : Blo 215810 493019 := bstep (se 1 (by rfl) ⟨369764, by rfl⟩ : syracuseStep 493019 = 739529) B739529
theorem B624115 : Blo 215810 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B329225 : Blo 215810 329225 := bstep (se 2 (by rfl) ⟨123459, by rfl⟩ : syracuseStep 329225 = 246919) B246919
theorem B230951 : Blo 215810 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B329255 : Blo 215810 329255 := bstep (se 1 (by rfl) ⟨246941, by rfl⟩ : syracuseStep 329255 = 493883) B493883
theorem B329339 : Blo 215810 329339 := bstep (se 1 (by rfl) ⟨247004, by rfl⟩ : syracuseStep 329339 = 494009) B494009
theorem B624343 : Blo 215810 624343 := bstep (se 1 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 624343 = 936515) B936515
theorem B329465 : Blo 215810 329465 := bstep (se 2 (by rfl) ⟨123549, by rfl⟩ : syracuseStep 329465 = 247099) B247099
theorem B329567 : Blo 215810 329567 := bstep (se 1 (by rfl) ⟨247175, by rfl⟩ : syracuseStep 329567 = 494351) B494351
theorem B329579 : Blo 215810 329579 := bstep (se 1 (by rfl) ⟨247184, by rfl⟩ : syracuseStep 329579 = 494369) B494369
theorem B493487 : Blo 215810 493487 := bstep (se 1 (by rfl) ⟨370115, by rfl⟩ : syracuseStep 493487 = 740231) B740231
theorem B821249 : Blo 215810 821249 := bstep (se 2 (by rfl) ⟨307968, by rfl⟩ : syracuseStep 821249 = 615937) B615937
theorem B1607795 : Blo 215810 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B493739 : Blo 215810 493739 := bstep (se 1 (by rfl) ⟨370304, by rfl⟩ : syracuseStep 493739 = 740609) B740609
theorem B461047 : Blo 215810 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B494279 : Blo 215810 494279 := bstep (se 1 (by rfl) ⟨370709, by rfl⟩ : syracuseStep 494279 = 741419) B741419
theorem B1870775 : Blo 215810 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B822919 : Blo 215810 822919 := bstep (se 1 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 822919 = 1234379) B1234379
theorem B823223 : Blo 215810 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B593851 : Blo 215810 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B364601 : Blo 215810 364601 := bstep (se 2 (by rfl) ⟨136725, by rfl⟩ : syracuseStep 364601 = 273451) B273451
theorem B3150359 : Blo 215810 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B463457 : Blo 215810 463457 := bstep (se 2 (by rfl) ⟨173796, by rfl⟩ : syracuseStep 463457 = 347593) B347593
theorem B889483 : Blo 215810 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B365303 : Blo 215810 365303 := bstep (se 1 (by rfl) ⟨273977, by rfl⟩ : syracuseStep 365303 = 547955) B547955
theorem B463799 : Blo 215810 463799 := bstep (se 1 (by rfl) ⟨347849, by rfl⟩ : syracuseStep 463799 = 695699) B695699
theorem B824377 : Blo 215810 824377 := bstep (se 2 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 824377 = 618283) B618283
theorem B365647 : Blo 215810 365647 := bstep (se 1 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 365647 = 548471) B548471
theorem B3118297 : Blo 215810 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B365897 : Blo 215810 365897 := bstep (se 2 (by rfl) ⟨137211, by rfl⟩ : syracuseStep 365897 = 274423) B274423
theorem B824681 : Blo 215810 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B5969371 : Blo 215810 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B890579 : Blo 215810 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B366329 : Blo 215810 366329 := bstep (se 2 (by rfl) ⟨137373, by rfl⟩ : syracuseStep 366329 = 274747) B274747
theorem B366511 : Blo 215810 366511 := bstep (se 1 (by rfl) ⟨274883, by rfl⟩ : syracuseStep 366511 = 549767) B549767
theorem B366599 : Blo 215810 366599 := bstep (se 1 (by rfl) ⟨274949, by rfl⟩ : syracuseStep 366599 = 549899) B549899
theorem B1185799 : Blo 215810 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B366943 : Blo 215810 366943 := bstep (se 1 (by rfl) ⟨275207, by rfl⟩ : syracuseStep 366943 = 550415) B550415
theorem B1776001 : Blo 215810 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B367031 : Blo 215810 367031 := bstep (se 1 (by rfl) ⟨275273, by rfl⟩ : syracuseStep 367031 = 550547) B550547
theorem B1776491 : Blo 215810 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B695159 : Blo 215810 695159 := bstep (se 1 (by rfl) ⟨521369, by rfl⟩ : syracuseStep 695159 = 1042739) B1042739
theorem B3611621 : Blo 215810 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B367625 : Blo 215810 367625 := bstep (se 2 (by rfl) ⟨137859, by rfl⟩ : syracuseStep 367625 = 275719) B275719
theorem B924691 : Blo 215810 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B1186987 : Blo 215810 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B367787 : Blo 215810 367787 := bstep (se 1 (by rfl) ⟨275840, by rfl⟩ : syracuseStep 367787 = 551681) B551681
theorem B4300121 : Blo 215810 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B335369 : Blo 215810 335369 := bstep (se 2 (by rfl) ⟨125763, by rfl⟩ : syracuseStep 335369 = 251527) B251527
theorem B368185 : Blo 215810 368185 := bstep (se 2 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 368185 = 276139) B276139
theorem B925307 : Blo 215810 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B368327 : Blo 215810 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B630623 : Blo 215810 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B368489 : Blo 215810 368489 := bstep (se 2 (by rfl) ⟨138183, by rfl⟩ : syracuseStep 368489 = 276367) B276367
theorem B5054393 : Blo 215810 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B3579835 : Blo 215810 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B1875899 : Blo 215810 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B729107 : Blo 215810 729107 := bstep (se 1 (by rfl) ⟨546830, by rfl⟩ : syracuseStep 729107 = 1093661) B1093661
theorem B696377 : Blo 215810 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B368887 : Blo 215810 368887 := bstep (se 1 (by rfl) ⟨276665, by rfl⟩ : syracuseStep 368887 = 553331) B553331
theorem B729431 : Blo 215810 729431 := bstep (se 1 (by rfl) ⟨547073, by rfl⟩ : syracuseStep 729431 = 1094147) B1094147
theorem B631145 : Blo 215810 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B369083 : Blo 215810 369083 := bstep (se 1 (by rfl) ⟨276812, by rfl⟩ : syracuseStep 369083 = 553625) B553625
theorem B369191 : Blo 215810 369191 := bstep (se 1 (by rfl) ⟨276893, by rfl⟩ : syracuseStep 369191 = 553787) B553787
theorem B697031 : Blo 215810 697031 := bstep (se 1 (by rfl) ⟨522773, by rfl⟩ : syracuseStep 697031 = 1045547) B1045547
theorem B369481 : Blo 215810 369481 := bstep (se 2 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 369481 = 277111) B277111
theorem B369515 : Blo 215810 369515 := bstep (se 1 (by rfl) ⟨277136, by rfl⟩ : syracuseStep 369515 = 554273) B554273
theorem B2466935 : Blo 215810 2466935 := bstep (se 1 (by rfl) ⟨1850201, by rfl⟩ : syracuseStep 2466935 = 3700403) B3700403
theorem B828569 : Blo 215810 828569 := bstep (se 2 (by rfl) ⟨310713, by rfl⟩ : syracuseStep 828569 = 621427) B621427
theorem B369913 : Blo 215810 369913 := bstep (se 2 (by rfl) ⟨138717, by rfl⟩ : syracuseStep 369913 = 277435) B277435
theorem B730511 : Blo 215810 730511 := bstep (se 1 (by rfl) ⟨547883, by rfl⟩ : syracuseStep 730511 = 1095767) B1095767
theorem B370183 : Blo 215810 370183 := bstep (se 1 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 370183 = 555275) B555275
theorem B829025 : Blo 215810 829025 := bstep (se 2 (by rfl) ⟨310884, by rfl⟩ : syracuseStep 829025 = 621769) B621769
theorem B730835 : Blo 215810 730835 := bstep (se 1 (by rfl) ⟨548126, by rfl⟩ : syracuseStep 730835 = 1096253) B1096253
theorem B370615 : Blo 215810 370615 := bstep (se 1 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 370615 = 555923) B555923
theorem B1451963 : Blo 215810 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B370811 : Blo 215810 370811 := bstep (se 1 (by rfl) ⟨278108, by rfl⟩ : syracuseStep 370811 = 556217) B556217
theorem B4204781 : Blo 215810 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B732023 : Blo 215810 732023 := bstep (se 1 (by rfl) ⟨549017, by rfl⟩ : syracuseStep 732023 = 1098035) B1098035
theorem B2108389 : Blo 215810 2108389 := bstep (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) B395323
theorem B371719 : Blo 215810 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B830483 : Blo 215810 830483 := bstep (se 1 (by rfl) ⟨622862, by rfl⟩ : syracuseStep 830483 = 1245725) B1245725
theorem B732239 : Blo 215810 732239 := bstep (se 1 (by rfl) ⟨549179, by rfl⟩ : syracuseStep 732239 = 1098359) B1098359
theorem B732617 : Blo 215810 732617 := bstep (se 2 (by rfl) ⟨274731, by rfl⟩ : syracuseStep 732617 = 549463) B549463
theorem B1486433 : Blo 215810 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B274043 : Blo 215810 274043 := bstep (se 1 (by rfl) ⟨205532, by rfl⟩ : syracuseStep 274043 = 411065) B411065
theorem B4009661 : Blo 215810 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B732887 : Blo 215810 732887 := bstep (se 1 (by rfl) ⟨549665, by rfl⟩ : syracuseStep 732887 = 1099331) B1099331
theorem B2993885 : Blo 215810 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B733103 : Blo 215810 733103 := bstep (se 1 (by rfl) ⟨549827, by rfl⟩ : syracuseStep 733103 = 1099655) B1099655
theorem B1421243 : Blo 215810 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B438601 : Blo 215810 438601 := bstep (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) B328951
theorem B373135 : Blo 215810 373135 := bstep (se 1 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 373135 = 559703) B559703
theorem B832139 : Blo 215810 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B2765825 : Blo 215810 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B4207787 : Blo 215810 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B242887 : Blo 215810 242887 := bstep (se 1 (by rfl) ⟨182165, by rfl⟩ : syracuseStep 242887 = 364331) B364331
theorem B1324583 : Blo 215810 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B4503239 : Blo 215810 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B833399 : Blo 215810 833399 := bstep (se 1 (by rfl) ⟨625049, by rfl⟩ : syracuseStep 833399 = 1250099) B1250099
theorem B2766797 : Blo 215810 2766797 := bstep (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) B1037549
theorem B243751 : Blo 215810 243751 := bstep (se 1 (by rfl) ⟨182813, by rfl⟩ : syracuseStep 243751 = 365627) B365627
theorem B440491 : Blo 215810 440491 := bstep (se 1 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 440491 = 660737) B660737
theorem B735479 : Blo 215810 735479 := bstep (se 1 (by rfl) ⟨551609, by rfl⟩ : syracuseStep 735479 = 1103219) B1103219
theorem B932107 : Blo 215810 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B6404629 : Blo 215810 6404629 := bstep (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) B300217
theorem B735803 : Blo 215810 735803 := bstep (se 1 (by rfl) ⟨551852, by rfl⟩ : syracuseStep 735803 = 1103705) B1103705
theorem B834371 : Blo 215810 834371 := bstep (se 1 (by rfl) ⟨625778, by rfl⟩ : syracuseStep 834371 = 1251557) B1251557
theorem B736073 : Blo 215810 736073 := bstep (se 2 (by rfl) ⟨276027, by rfl⟩ : syracuseStep 736073 = 552055) B552055
theorem B375659 : Blo 215810 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B310235 : Blo 215810 310235 := bstep (se 1 (by rfl) ⟨232676, by rfl⟩ : syracuseStep 310235 = 465353) B465353
theorem B245371 : Blo 215810 245371 := bstep (se 1 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 245371 = 368057) B368057
theorem B1752941 : Blo 215810 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B311215 : Blo 215810 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B737207 : Blo 215810 737207 := bstep (se 1 (by rfl) ⟨552905, by rfl⟩ : syracuseStep 737207 = 1105811) B1105811
theorem B245839 : Blo 215810 245839 := bstep (se 1 (by rfl) ⟨184379, by rfl⟩ : syracuseStep 245839 = 368759) B368759
theorem B2015549 : Blo 215810 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B1392983 : Blo 215810 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B410017 : Blo 215810 410017 := bstep (se 2 (by rfl) ⟨153756, by rfl⟩ : syracuseStep 410017 = 307513) B307513
theorem B246235 : Blo 215810 246235 := bstep (se 1 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 246235 = 369353) B369353
theorem B737801 : Blo 215810 737801 := bstep (se 2 (by rfl) ⟨276675, by rfl⟩ : syracuseStep 737801 = 553351) B553351
theorem B3195451 : Blo 215810 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B311887 : Blo 215810 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B312007 : Blo 215810 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B410359 : Blo 215810 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B1131371 : Blo 215810 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B246703 : Blo 215810 246703 := bstep (se 1 (by rfl) ⟨185027, by rfl⟩ : syracuseStep 246703 = 370055) B370055
theorem B410663 : Blo 215810 410663 := bstep (se 1 (by rfl) ⟨307997, by rfl⟩ : syracuseStep 410663 = 615995) B615995
theorem B1557623 : Blo 215810 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B1394009 : Blo 215810 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B247135 : Blo 215810 247135 := bstep (se 1 (by rfl) ⟨185351, by rfl⟩ : syracuseStep 247135 = 370703) B370703
theorem B738665 : Blo 215810 738665 := bstep (se 2 (by rfl) ⟨276999, by rfl⟩ : syracuseStep 738665 = 553999) B553999
theorem B345799 : Blo 215810 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B1853279 : Blo 215810 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B739259 : Blo 215810 739259 := bstep (se 1 (by rfl) ⟨554444, by rfl⟩ : syracuseStep 739259 = 1108889) B1108889
theorem B3524897 : Blo 215810 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B936481 : Blo 215810 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B1231645 : Blo 215810 1231645 := bstep (se 3 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 1231645 = 461867) B461867
theorem B215847 : Blo 215810 215847 := bstep (se 1 (by rfl) ⟨161885, by rfl⟩ : syracuseStep 215847 = 323771) B323771
theorem B2673485 : Blo 215810 2673485 := bstep (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) B1002557
theorem B2018125 : Blo 215810 2018125 := bstep (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) B756797
theorem B215887 : Blo 215810 215887 := bstep (se 1 (by rfl) ⟨161915, by rfl⟩ : syracuseStep 215887 = 323831) B323831
theorem B215903 : Blo 215810 215903 := bstep (se 1 (by rfl) ⟨161927, by rfl⟩ : syracuseStep 215903 = 323855) B323855
theorem B609131 : Blo 215810 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B412523 : Blo 215810 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B215931 : Blo 215810 215931 := bstep (se 1 (by rfl) ⟨161948, by rfl⟩ : syracuseStep 215931 = 323897) B323897
theorem B1657745 : Blo 215810 1657745 := bstep (se 2 (by rfl) ⟨621654, by rfl⟩ : syracuseStep 1657745 = 1243309) B1243309
theorem B215983 : Blo 215810 215983 := bstep (se 1 (by rfl) ⟨161987, by rfl⟩ : syracuseStep 215983 = 323975) B323975
theorem B216007 : Blo 215810 216007 := bstep (se 1 (by rfl) ⟨162005, by rfl⟩ : syracuseStep 216007 = 324011) B324011
theorem B216027 : Blo 215810 216027 := bstep (se 1 (by rfl) ⟨162020, by rfl⟩ : syracuseStep 216027 = 324041) B324041
theorem B216103 : Blo 215810 216103 := bstep (se 1 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 216103 = 324155) B324155
theorem B216143 : Blo 215810 216143 := bstep (se 1 (by rfl) ⟨162107, by rfl⟩ : syracuseStep 216143 = 324215) B324215
theorem B412751 : Blo 215810 412751 := bstep (se 1 (by rfl) ⟨309563, by rfl⟩ : syracuseStep 412751 = 619127) B619127
theorem B216159 : Blo 215810 216159 := bstep (se 1 (by rfl) ⟨162119, by rfl⟩ : syracuseStep 216159 = 324239) B324239
theorem B216187 : Blo 215810 216187 := bstep (se 1 (by rfl) ⟨162140, by rfl⟩ : syracuseStep 216187 = 324281) B324281
theorem B216239 : Blo 215810 216239 := bstep (se 1 (by rfl) ⟨162179, by rfl⟩ : syracuseStep 216239 = 324359) B324359
theorem B216263 : Blo 215810 216263 := bstep (se 1 (by rfl) ⟨162197, by rfl⟩ : syracuseStep 216263 = 324395) B324395
theorem B216283 : Blo 215810 216283 := bstep (se 1 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 216283 = 324425) B324425
theorem B216359 : Blo 215810 216359 := bstep (se 1 (by rfl) ⟨162269, by rfl⟩ : syracuseStep 216359 = 324539) B324539
theorem B216399 : Blo 215810 216399 := bstep (se 1 (by rfl) ⟨162299, by rfl⟩ : syracuseStep 216399 = 324599) B324599
theorem B216415 : Blo 215810 216415 := bstep (se 1 (by rfl) ⟨162311, by rfl⟩ : syracuseStep 216415 = 324623) B324623
theorem B216443 : Blo 215810 216443 := bstep (se 1 (by rfl) ⟨162332, by rfl⟩ : syracuseStep 216443 = 324665) B324665
theorem B216495 : Blo 215810 216495 := bstep (se 1 (by rfl) ⟨162371, by rfl⟩ : syracuseStep 216495 = 324743) B324743
theorem B216519 : Blo 215810 216519 := bstep (se 1 (by rfl) ⟨162389, by rfl⟩ : syracuseStep 216519 = 324779) B324779
theorem B216539 : Blo 215810 216539 := bstep (se 1 (by rfl) ⟨162404, by rfl⟩ : syracuseStep 216539 = 324809) B324809
theorem B1101275 : Blo 215810 1101275 := bstep (se 1 (by rfl) ⟨825956, by rfl⟩ : syracuseStep 1101275 = 1651913) B1651913
theorem B413191 : Blo 215810 413191 := bstep (se 1 (by rfl) ⟨309893, by rfl⟩ : syracuseStep 413191 = 619787) B619787
theorem B216615 : Blo 215810 216615 := bstep (se 1 (by rfl) ⟨162461, by rfl⟩ : syracuseStep 216615 = 324923) B324923
theorem B216655 : Blo 215810 216655 := bstep (se 1 (by rfl) ⟨162491, by rfl⟩ : syracuseStep 216655 = 324983) B324983
theorem B216671 : Blo 215810 216671 := bstep (se 1 (by rfl) ⟨162503, by rfl⟩ : syracuseStep 216671 = 325007) B325007
theorem B216699 : Blo 215810 216699 := bstep (se 1 (by rfl) ⟨162524, by rfl⟩ : syracuseStep 216699 = 325049) B325049
theorem B740987 : Blo 215810 740987 := bstep (se 1 (by rfl) ⟨555740, by rfl⟩ : syracuseStep 740987 = 1111481) B1111481
theorem B216751 : Blo 215810 216751 := bstep (se 1 (by rfl) ⟨162563, by rfl⟩ : syracuseStep 216751 = 325127) B325127
theorem B216775 : Blo 215810 216775 := bstep (se 1 (by rfl) ⟨162581, by rfl⟩ : syracuseStep 216775 = 325163) B325163
theorem B216795 : Blo 215810 216795 := bstep (se 1 (by rfl) ⟨162596, by rfl⟩ : syracuseStep 216795 = 325193) B325193
theorem B741149 : Blo 215810 741149 := bstep (se 3 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 741149 = 277931) B277931
theorem B216871 : Blo 215810 216871 := bstep (se 1 (by rfl) ⟨162653, by rfl⟩ : syracuseStep 216871 = 325307) B325307
theorem B216911 : Blo 215810 216911 := bstep (se 1 (by rfl) ⟨162683, by rfl⟩ : syracuseStep 216911 = 325367) B325367
theorem B216927 : Blo 215810 216927 := bstep (se 1 (by rfl) ⟨162695, by rfl⟩ : syracuseStep 216927 = 325391) B325391
theorem B216955 : Blo 215810 216955 := bstep (se 1 (by rfl) ⟨162716, by rfl⟩ : syracuseStep 216955 = 325433) B325433
theorem B217007 : Blo 215810 217007 := bstep (se 1 (by rfl) ⟨162755, by rfl⟩ : syracuseStep 217007 = 325511) B325511
theorem B1101761 : Blo 215810 1101761 := bstep (se 2 (by rfl) ⟨413160, by rfl⟩ : syracuseStep 1101761 = 826321) B826321
theorem B1396673 : Blo 215810 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B217031 : Blo 215810 217031 := bstep (se 1 (by rfl) ⟨162773, by rfl⟩ : syracuseStep 217031 = 325547) B325547
theorem B217051 : Blo 215810 217051 := bstep (se 1 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 217051 = 325577) B325577
theorem B217127 : Blo 215810 217127 := bstep (se 1 (by rfl) ⟨162845, by rfl⟩ : syracuseStep 217127 = 325691) B325691
theorem B217167 : Blo 215810 217167 := bstep (se 1 (by rfl) ⟨162875, by rfl⟩ : syracuseStep 217167 = 325751) B325751
theorem B217183 : Blo 215810 217183 := bstep (se 1 (by rfl) ⟨162887, by rfl⟩ : syracuseStep 217183 = 325775) B325775
theorem B217211 : Blo 215810 217211 := bstep (se 1 (by rfl) ⟨162908, by rfl⟩ : syracuseStep 217211 = 325817) B325817
theorem B217263 : Blo 215810 217263 := bstep (se 1 (by rfl) ⟨162947, by rfl⟩ : syracuseStep 217263 = 325895) B325895
theorem B217287 : Blo 215810 217287 := bstep (se 1 (by rfl) ⟨162965, by rfl⟩ : syracuseStep 217287 = 325931) B325931
theorem B217307 : Blo 215810 217307 := bstep (se 1 (by rfl) ⟨162980, by rfl⟩ : syracuseStep 217307 = 325961) B325961
theorem B217383 : Blo 215810 217383 := bstep (se 1 (by rfl) ⟨163037, by rfl⟩ : syracuseStep 217383 = 326075) B326075
theorem B217423 : Blo 215810 217423 := bstep (se 1 (by rfl) ⟨163067, by rfl⟩ : syracuseStep 217423 = 326135) B326135
theorem B217439 : Blo 215810 217439 := bstep (se 1 (by rfl) ⟨163079, by rfl⟩ : syracuseStep 217439 = 326159) B326159
theorem B217467 : Blo 215810 217467 := bstep (se 1 (by rfl) ⟨163100, by rfl⟩ : syracuseStep 217467 = 326201) B326201
theorem B840061 : Blo 215810 840061 := bstep (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) B315023
theorem B217519 : Blo 215810 217519 := bstep (se 1 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 217519 = 326279) B326279
theorem B348599 : Blo 215810 348599 := bstep (se 1 (by rfl) ⟨261449, by rfl⟩ : syracuseStep 348599 = 522899) B522899
theorem B217543 : Blo 215810 217543 := bstep (se 1 (by rfl) ⟨163157, by rfl⟩ : syracuseStep 217543 = 326315) B326315
theorem B217563 : Blo 215810 217563 := bstep (se 1 (by rfl) ⟨163172, by rfl⟩ : syracuseStep 217563 = 326345) B326345
theorem B741851 : Blo 215810 741851 := bstep (se 1 (by rfl) ⟨556388, by rfl⟩ : syracuseStep 741851 = 1112777) B1112777
theorem B217639 : Blo 215810 217639 := bstep (se 1 (by rfl) ⟨163229, by rfl⟩ : syracuseStep 217639 = 326459) B326459
theorem B414247 : Blo 215810 414247 := bstep (se 1 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 414247 = 621371) B621371
theorem B217679 : Blo 215810 217679 := bstep (se 1 (by rfl) ⟨163259, by rfl⟩ : syracuseStep 217679 = 326519) B326519
theorem B217695 : Blo 215810 217695 := bstep (se 1 (by rfl) ⟨163271, by rfl⟩ : syracuseStep 217695 = 326543) B326543
theorem B217723 : Blo 215810 217723 := bstep (se 1 (by rfl) ⟨163292, by rfl⟩ : syracuseStep 217723 = 326585) B326585
theorem B217775 : Blo 215810 217775 := bstep (se 1 (by rfl) ⟨163331, by rfl⟩ : syracuseStep 217775 = 326663) B326663
theorem B217799 : Blo 215810 217799 := bstep (se 1 (by rfl) ⟨163349, by rfl⟩ : syracuseStep 217799 = 326699) B326699
theorem B217819 : Blo 215810 217819 := bstep (se 1 (by rfl) ⟨163364, by rfl⟩ : syracuseStep 217819 = 326729) B326729
theorem B217895 : Blo 215810 217895 := bstep (se 1 (by rfl) ⟨163421, by rfl⟩ : syracuseStep 217895 = 326843) B326843
theorem B217935 : Blo 215810 217935 := bstep (se 1 (by rfl) ⟨163451, by rfl⟩ : syracuseStep 217935 = 326903) B326903
theorem B217951 : Blo 215810 217951 := bstep (se 1 (by rfl) ⟨163463, by rfl⟩ : syracuseStep 217951 = 326927) B326927
theorem B217979 : Blo 215810 217979 := bstep (se 1 (by rfl) ⟨163484, by rfl⟩ : syracuseStep 217979 = 326969) B326969
theorem B218031 : Blo 215810 218031 := bstep (se 1 (by rfl) ⟨163523, by rfl⟩ : syracuseStep 218031 = 327047) B327047
theorem B218055 : Blo 215810 218055 := bstep (se 1 (by rfl) ⟨163541, by rfl⟩ : syracuseStep 218055 = 327083) B327083
theorem B218075 : Blo 215810 218075 := bstep (se 1 (by rfl) ⟨163556, by rfl⟩ : syracuseStep 218075 = 327113) B327113
theorem B2249693 : Blo 215810 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B218151 : Blo 215810 218151 := bstep (se 1 (by rfl) ⟨163613, by rfl⟩ : syracuseStep 218151 = 327227) B327227
theorem B218191 : Blo 215810 218191 := bstep (se 1 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 218191 = 327287) B327287
theorem B218207 : Blo 215810 218207 := bstep (se 1 (by rfl) ⟨163655, by rfl⟩ : syracuseStep 218207 = 327311) B327311
theorem B218235 : Blo 215810 218235 := bstep (se 1 (by rfl) ⟨163676, by rfl⟩ : syracuseStep 218235 = 327353) B327353
theorem B218287 : Blo 215810 218287 := bstep (se 1 (by rfl) ⟨163715, by rfl⟩ : syracuseStep 218287 = 327431) B327431
theorem B218311 : Blo 215810 218311 := bstep (se 1 (by rfl) ⟨163733, by rfl⟩ : syracuseStep 218311 = 327467) B327467
theorem B218331 : Blo 215810 218331 := bstep (se 1 (by rfl) ⟨163748, by rfl⟩ : syracuseStep 218331 = 327497) B327497
theorem B1660175 : Blo 215810 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B218407 : Blo 215810 218407 := bstep (se 1 (by rfl) ⟨163805, by rfl⟩ : syracuseStep 218407 = 327611) B327611
theorem B218447 : Blo 215810 218447 := bstep (se 1 (by rfl) ⟨163835, by rfl⟩ : syracuseStep 218447 = 327671) B327671
theorem B218463 : Blo 215810 218463 := bstep (se 1 (by rfl) ⟨163847, by rfl⟩ : syracuseStep 218463 = 327695) B327695
theorem B218491 : Blo 215810 218491 := bstep (se 1 (by rfl) ⟨163868, by rfl⟩ : syracuseStep 218491 = 327737) B327737
theorem B218543 : Blo 215810 218543 := bstep (se 1 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 218543 = 327815) B327815
theorem B218567 : Blo 215810 218567 := bstep (se 1 (by rfl) ⟨163925, by rfl⟩ : syracuseStep 218567 = 327851) B327851
theorem B218587 : Blo 215810 218587 := bstep (se 1 (by rfl) ⟨163940, by rfl⟩ : syracuseStep 218587 = 327881) B327881
theorem B218663 : Blo 215810 218663 := bstep (se 1 (by rfl) ⟨163997, by rfl⟩ : syracuseStep 218663 = 327995) B327995
theorem B218703 : Blo 215810 218703 := bstep (se 1 (by rfl) ⟨164027, by rfl⟩ : syracuseStep 218703 = 328055) B328055
theorem B218719 : Blo 215810 218719 := bstep (se 1 (by rfl) ⟨164039, by rfl⟩ : syracuseStep 218719 = 328079) B328079
theorem B12342881 : Blo 215810 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B218747 : Blo 215810 218747 := bstep (se 1 (by rfl) ⟨164060, by rfl⟩ : syracuseStep 218747 = 328121) B328121
theorem B1037971 : Blo 215810 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B218799 : Blo 215810 218799 := bstep (se 1 (by rfl) ⟨164099, by rfl⟩ : syracuseStep 218799 = 328199) B328199
theorem B218823 : Blo 215810 218823 := bstep (se 1 (by rfl) ⟨164117, by rfl⟩ : syracuseStep 218823 = 328235) B328235
theorem B218843 : Blo 215810 218843 := bstep (se 1 (by rfl) ⟨164132, by rfl⟩ : syracuseStep 218843 = 328265) B328265
theorem B6674177 : Blo 215810 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B218919 : Blo 215810 218919 := bstep (se 1 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 218919 = 328379) B328379
theorem B218959 : Blo 215810 218959 := bstep (se 1 (by rfl) ⟨164219, by rfl⟩ : syracuseStep 218959 = 328439) B328439
theorem B218975 : Blo 215810 218975 := bstep (se 1 (by rfl) ⟨164231, by rfl⟩ : syracuseStep 218975 = 328463) B328463
theorem B219003 : Blo 215810 219003 := bstep (se 1 (by rfl) ⟨164252, by rfl⟩ : syracuseStep 219003 = 328505) B328505
theorem B219055 : Blo 215810 219055 := bstep (se 1 (by rfl) ⟨164291, by rfl⟩ : syracuseStep 219055 = 328583) B328583
theorem B219079 : Blo 215810 219079 := bstep (se 1 (by rfl) ⟨164309, by rfl⟩ : syracuseStep 219079 = 328619) B328619
theorem B219099 : Blo 215810 219099 := bstep (se 1 (by rfl) ⟨164324, by rfl⟩ : syracuseStep 219099 = 328649) B328649
theorem B415751 : Blo 215810 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B219175 : Blo 215810 219175 := bstep (se 1 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 219175 = 328763) B328763
theorem B219215 : Blo 215810 219215 := bstep (se 1 (by rfl) ⟨164411, by rfl⟩ : syracuseStep 219215 = 328823) B328823
theorem B219231 : Blo 215810 219231 := bstep (se 1 (by rfl) ⟨164423, by rfl⟩ : syracuseStep 219231 = 328847) B328847
theorem B219259 : Blo 215810 219259 := bstep (se 1 (by rfl) ⟨164444, by rfl⟩ : syracuseStep 219259 = 328889) B328889
theorem B1104029 : Blo 215810 1104029 := bstep (se 3 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 1104029 = 414011) B414011
theorem B219311 : Blo 215810 219311 := bstep (se 1 (by rfl) ⟨164483, by rfl⟩ : syracuseStep 219311 = 328967) B328967
theorem B219335 : Blo 215810 219335 := bstep (se 1 (by rfl) ⟨164501, by rfl⟩ : syracuseStep 219335 = 329003) B329003
theorem B415955 : Blo 215810 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B219355 : Blo 215810 219355 := bstep (se 1 (by rfl) ⟨164516, by rfl⟩ : syracuseStep 219355 = 329033) B329033
theorem B219431 : Blo 215810 219431 := bstep (se 1 (by rfl) ⟨164573, by rfl⟩ : syracuseStep 219431 = 329147) B329147
theorem B219471 : Blo 215810 219471 := bstep (se 1 (by rfl) ⟨164603, by rfl⟩ : syracuseStep 219471 = 329207) B329207
theorem B219487 : Blo 215810 219487 := bstep (se 1 (by rfl) ⟨164615, by rfl⟩ : syracuseStep 219487 = 329231) B329231
theorem B416107 : Blo 215810 416107 := bstep (se 1 (by rfl) ⟨312080, by rfl⟩ : syracuseStep 416107 = 624161) B624161
theorem B219515 : Blo 215810 219515 := bstep (se 1 (by rfl) ⟨164636, by rfl⟩ : syracuseStep 219515 = 329273) B329273
theorem B219567 : Blo 215810 219567 := bstep (se 1 (by rfl) ⟨164675, by rfl⟩ : syracuseStep 219567 = 329351) B329351
theorem B219591 : Blo 215810 219591 := bstep (se 1 (by rfl) ⟨164693, by rfl⟩ : syracuseStep 219591 = 329387) B329387
theorem B219611 : Blo 215810 219611 := bstep (se 1 (by rfl) ⟨164708, by rfl⟩ : syracuseStep 219611 = 329417) B329417
theorem B547337 : Blo 215810 547337 := bstep (se 2 (by rfl) ⟨205251, by rfl⟩ : syracuseStep 547337 = 410503) B410503
theorem B219687 : Blo 215810 219687 := bstep (se 1 (by rfl) ⟨164765, by rfl⟩ : syracuseStep 219687 = 329531) B329531
theorem B416335 : Blo 215810 416335 := bstep (se 1 (by rfl) ⟨312251, by rfl⟩ : syracuseStep 416335 = 624503) B624503
theorem B219727 : Blo 215810 219727 := bstep (se 1 (by rfl) ⟨164795, by rfl⟩ : syracuseStep 219727 = 329591) B329591
theorem B219743 : Blo 215810 219743 := bstep (se 1 (by rfl) ⟨164807, by rfl⟩ : syracuseStep 219743 = 329615) B329615
theorem B219771 : Blo 215810 219771 := bstep (se 1 (by rfl) ⟨164828, by rfl⟩ : syracuseStep 219771 = 329657) B329657
theorem B351071 : Blo 215810 351071 := bstep (se 1 (by rfl) ⟨263303, by rfl⟩ : syracuseStep 351071 = 526607) B526607
theorem B711607 : Blo 215810 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B3333143 : Blo 215810 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1236019 : Blo 215810 1236019 := bstep (se 1 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 1236019 = 1854029) B1854029
theorem B1268939 : Blo 215810 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1105325 : Blo 215810 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B1039817 : Blo 215810 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B548491 : Blo 215810 548491 := bstep (se 1 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 548491 = 822737) B822737
theorem B876179 : Blo 215810 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B11951887 : Blo 215810 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B548795 : Blo 215810 548795 := bstep (se 1 (by rfl) ⟨411596, by rfl⟩ : syracuseStep 548795 = 823193) B823193
theorem B1663091 : Blo 215810 1663091 := bstep (se 1 (by rfl) ⟨1247318, by rfl⟩ : syracuseStep 1663091 = 2494637) B2494637
theorem B549575 : Blo 215810 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B549625 : Blo 215810 549625 := bstep (se 2 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 549625 = 412219) B412219
theorem B22438853 : Blo 215810 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B1106945 : Blo 215810 1106945 := bstep (se 2 (by rfl) ⟨415104, by rfl⟩ : syracuseStep 1106945 = 830209) B830209
theorem B615595 : Blo 215810 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B550273 : Blo 215810 550273 := bstep (se 2 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 550273 = 412705) B412705
theorem B1107755 : Blo 215810 1107755 := bstep (se 1 (by rfl) ⟨830816, by rfl⟩ : syracuseStep 1107755 = 1661633) B1661633
theorem B551083 : Blo 215810 551083 := bstep (se 1 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 551083 = 826625) B826625
theorem B551387 : Blo 215810 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B485927 : Blo 215810 485927 := bstep (se 1 (by rfl) ⟨364445, by rfl⟩ : syracuseStep 485927 = 728891) B728891
theorem B3041837 : Blo 215810 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B518795 : Blo 215810 518795 := bstep (se 1 (by rfl) ⟨389096, by rfl⟩ : syracuseStep 518795 = 778193) B778193
theorem B486251 : Blo 215810 486251 := bstep (se 1 (by rfl) ⟨364688, by rfl⟩ : syracuseStep 486251 = 729377) B729377
theorem B781163 : Blo 215810 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B486305 : Blo 215810 486305 := bstep (se 2 (by rfl) ⟨182364, by rfl⟩ : syracuseStep 486305 = 364729) B364729
theorem B486647 : Blo 215810 486647 := bstep (se 1 (by rfl) ⟨364985, by rfl⟩ : syracuseStep 486647 = 729971) B729971
theorem B781579 : Blo 215810 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B5074319 : Blo 215810 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1174985 : Blo 215810 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B781883 : Blo 215810 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B2715275 : Blo 215810 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B519929 : Blo 215810 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B487241 : Blo 215810 487241 := bstep (se 2 (by rfl) ⟨182715, by rfl⟩ : syracuseStep 487241 = 365431) B365431
theorem B552865 : Blo 215810 552865 := bstep (se 2 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 552865 = 414649) B414649
theorem B1110023 : Blo 215810 1110023 := bstep (se 1 (by rfl) ⟨832517, by rfl⟩ : syracuseStep 1110023 = 1665035) B1665035
theorem B323783 : Blo 215810 323783 := bstep (se 1 (by rfl) ⟨242837, by rfl⟩ : syracuseStep 323783 = 485675) B485675
theorem B323945 : Blo 215810 323945 := bstep (se 2 (by rfl) ⟨121479, by rfl⟩ : syracuseStep 323945 = 242959) B242959
theorem B324023 : Blo 215810 324023 := bstep (se 1 (by rfl) ⟨243017, by rfl⟩ : syracuseStep 324023 = 486035) B486035
theorem B324059 : Blo 215810 324059 := bstep (se 1 (by rfl) ⟨243044, by rfl⟩ : syracuseStep 324059 = 486089) B486089
theorem B1110509 : Blo 215810 1110509 := bstep (se 3 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 1110509 = 416441) B416441
theorem B2093627 : Blo 215810 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B488033 : Blo 215810 488033 := bstep (se 2 (by rfl) ⟨183012, by rfl⟩ : syracuseStep 488033 = 366025) B366025
theorem B2093779 : Blo 215810 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B7893773 : Blo 215810 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B13202189 : Blo 215810 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B783265 : Blo 215810 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B324527 : Blo 215810 324527 := bstep (se 1 (by rfl) ⟨243395, by rfl⟩ : syracuseStep 324527 = 486791) B486791
theorem B488375 : Blo 215810 488375 := bstep (se 1 (by rfl) ⟨366281, by rfl⟩ : syracuseStep 488375 = 732563) B732563
theorem B5993473 : Blo 215810 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B324617 : Blo 215810 324617 := bstep (se 2 (by rfl) ⟨121731, by rfl⟩ : syracuseStep 324617 = 243463) B243463
theorem B324647 : Blo 215810 324647 := bstep (se 1 (by rfl) ⟨243485, by rfl⟩ : syracuseStep 324647 = 486971) B486971
theorem B2487347 : Blo 215810 2487347 := bstep (se 1 (by rfl) ⟨1865510, by rfl⟩ : syracuseStep 2487347 = 3731021) B3731021
theorem B2356289 : Blo 215810 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B324731 : Blo 215810 324731 := bstep (se 1 (by rfl) ⟨243548, by rfl⟩ : syracuseStep 324731 = 487097) B487097
theorem B1406105 : Blo 215810 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B324857 : Blo 215810 324857 := bstep (se 2 (by rfl) ⟨121821, by rfl⟩ : syracuseStep 324857 = 243643) B243643
theorem B1111319 : Blo 215810 1111319 := bstep (se 1 (by rfl) ⟨833489, by rfl⟩ : syracuseStep 1111319 = 1666979) B1666979
theorem B324959 : Blo 215810 324959 := bstep (se 1 (by rfl) ⟨243719, by rfl⟩ : syracuseStep 324959 = 487439) B487439
theorem B324971 : Blo 215810 324971 := bstep (se 1 (by rfl) ⟨243728, by rfl⟩ : syracuseStep 324971 = 487457) B487457
theorem B1602989 : Blo 215810 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B3536369 : Blo 215810 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B488969 : Blo 215810 488969 := bstep (se 2 (by rfl) ⟨183363, by rfl⟩ : syracuseStep 488969 = 366727) B366727
theorem B325199 : Blo 215810 325199 := bstep (se 1 (by rfl) ⟨243899, by rfl⟩ : syracuseStep 325199 = 487799) B487799
theorem B620129 : Blo 215810 620129 := bstep (se 2 (by rfl) ⟨232548, by rfl⟩ : syracuseStep 620129 = 465097) B465097
theorem B325319 : Blo 215810 325319 := bstep (se 1 (by rfl) ⟨243989, by rfl⟩ : syracuseStep 325319 = 487979) B487979
theorem B620243 : Blo 215810 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B1668923 : Blo 215810 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B489311 : Blo 215810 489311 := bstep (se 1 (by rfl) ⟨366983, by rfl⟩ : syracuseStep 489311 = 733967) B733967
theorem B325481 : Blo 215810 325481 := bstep (se 2 (by rfl) ⟨122055, by rfl⟩ : syracuseStep 325481 = 244111) B244111
theorem B325559 : Blo 215810 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B325595 : Blo 215810 325595 := bstep (se 1 (by rfl) ⟨244196, by rfl⟩ : syracuseStep 325595 = 488393) B488393
theorem B489491 : Blo 215810 489491 := bstep (se 1 (by rfl) ⟨367118, by rfl⟩ : syracuseStep 489491 = 734237) B734237
theorem B260219 : Blo 215810 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B784579 : Blo 215810 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B391367 : Blo 215810 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B1407233 : Blo 215810 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B489833 : Blo 215810 489833 := bstep (se 2 (by rfl) ⟨183687, by rfl⟩ : syracuseStep 489833 = 367375) B367375
theorem B555407 : Blo 215810 555407 := bstep (se 1 (by rfl) ⟨416555, by rfl⟩ : syracuseStep 555407 = 833111) B833111
theorem B326063 : Blo 215810 326063 := bstep (se 1 (by rfl) ⟨244547, by rfl⟩ : syracuseStep 326063 = 489095) B489095
theorem B326153 : Blo 215810 326153 := bstep (se 2 (by rfl) ⟨122307, by rfl⟩ : syracuseStep 326153 = 244615) B244615
theorem B326183 : Blo 215810 326183 := bstep (se 1 (by rfl) ⟨244637, by rfl⟩ : syracuseStep 326183 = 489275) B489275
theorem B326267 : Blo 215810 326267 := bstep (se 1 (by rfl) ⟨244700, by rfl⟩ : syracuseStep 326267 = 489401) B489401
theorem B621245 : Blo 215810 621245 := bstep (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) B232967
theorem B555731 : Blo 215810 555731 := bstep (se 1 (by rfl) ⟨416798, by rfl⟩ : syracuseStep 555731 = 833597) B833597
theorem B326393 : Blo 215810 326393 := bstep (se 2 (by rfl) ⟨122397, by rfl⟩ : syracuseStep 326393 = 244795) B244795
theorem B588617 : Blo 215810 588617 := bstep (se 2 (by rfl) ⟨220731, by rfl⟩ : syracuseStep 588617 = 441463) B441463
theorem B326495 : Blo 215810 326495 := bstep (se 1 (by rfl) ⟨244871, by rfl⟩ : syracuseStep 326495 = 489743) B489743
theorem B326507 : Blo 215810 326507 := bstep (se 1 (by rfl) ⟨244880, by rfl⟩ : syracuseStep 326507 = 489761) B489761
theorem B490427 : Blo 215810 490427 := bstep (se 1 (by rfl) ⟨367820, by rfl⟩ : syracuseStep 490427 = 735641) B735641
theorem B621587 : Blo 215810 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B490553 : Blo 215810 490553 := bstep (se 2 (by rfl) ⟨183957, by rfl⟩ : syracuseStep 490553 = 367915) B367915
theorem B326735 : Blo 215810 326735 := bstep (se 1 (by rfl) ⟨245051, by rfl⟩ : syracuseStep 326735 = 490103) B490103
theorem B326855 : Blo 215810 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B327017 : Blo 215810 327017 := bstep (se 2 (by rfl) ⟨122631, by rfl⟩ : syracuseStep 327017 = 245263) B245263
theorem B490895 : Blo 215810 490895 := bstep (se 1 (by rfl) ⟨368171, by rfl⟩ : syracuseStep 490895 = 736343) B736343
theorem B1867151 : Blo 215810 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B327095 : Blo 215810 327095 := bstep (se 1 (by rfl) ⟨245321, by rfl⟩ : syracuseStep 327095 = 490643) B490643
theorem B392635 : Blo 215810 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B327131 : Blo 215810 327131 := bstep (se 1 (by rfl) ⟨245348, by rfl⟩ : syracuseStep 327131 = 490697) B490697
theorem B622043 : Blo 215810 622043 := bstep (se 1 (by rfl) ⟨466532, by rfl⟩ : syracuseStep 622043 = 933065) B933065
theorem B556583 : Blo 215810 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B491219 : Blo 215810 491219 := bstep (se 1 (by rfl) ⟨368414, by rfl⟩ : syracuseStep 491219 = 736829) B736829
theorem B3374963 : Blo 215810 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B393103 : Blo 215810 393103 := bstep (se 1 (by rfl) ⟨294827, by rfl⟩ : syracuseStep 393103 = 589655) B589655
theorem B327599 : Blo 215810 327599 := bstep (se 1 (by rfl) ⟨245699, by rfl⟩ : syracuseStep 327599 = 491399) B491399
theorem B327785 : Blo 215810 327785 := bstep (se 2 (by rfl) ⟨122919, by rfl⟩ : syracuseStep 327785 = 245839) B245839
theorem B1343699 : Blo 215810 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B491849 : Blo 215810 491849 := bstep (se 2 (by rfl) ⟨184443, by rfl⟩ : syracuseStep 491849 = 368887) B368887
theorem B491867 : Blo 215810 491867 := bstep (se 1 (by rfl) ⟨368900, by rfl⟩ : syracuseStep 491867 = 737801) B737801
theorem B328103 : Blo 215810 328103 := bstep (se 1 (by rfl) ⟨246077, by rfl⟩ : syracuseStep 328103 = 492155) B492155
theorem B328187 : Blo 215810 328187 := bstep (se 1 (by rfl) ⟨246140, by rfl⟩ : syracuseStep 328187 = 492281) B492281
theorem B754247 : Blo 215810 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B328313 : Blo 215810 328313 := bstep (se 2 (by rfl) ⟨123117, by rfl⟩ : syracuseStep 328313 = 246235) B246235
theorem B787115 : Blo 215810 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B328367 : Blo 215810 328367 := bstep (se 1 (by rfl) ⟨246275, by rfl⟩ : syracuseStep 328367 = 492551) B492551
theorem B524983 : Blo 215810 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B393911 : Blo 215810 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B328415 : Blo 215810 328415 := bstep (se 1 (by rfl) ⟨246311, by rfl⟩ : syracuseStep 328415 = 492623) B492623
theorem B4260601 : Blo 215810 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B492443 : Blo 215810 492443 := bstep (se 1 (by rfl) ⟨369332, by rfl⟩ : syracuseStep 492443 = 738665) B738665
theorem B328679 : Blo 215810 328679 := bstep (se 1 (by rfl) ⟨246509, by rfl⟩ : syracuseStep 328679 = 493019) B493019
theorem B492641 : Blo 215810 492641 := bstep (se 2 (by rfl) ⟨184740, by rfl⟩ : syracuseStep 492641 = 369481) B369481
theorem B328937 : Blo 215810 328937 := bstep (se 2 (by rfl) ⟨123351, by rfl⟩ : syracuseStep 328937 = 246703) B246703
theorem B328991 : Blo 215810 328991 := bstep (se 1 (by rfl) ⟨246743, by rfl⟩ : syracuseStep 328991 = 493487) B493487
theorem B492839 : Blo 215810 492839 := bstep (se 1 (by rfl) ⟨369629, by rfl⟩ : syracuseStep 492839 = 739259) B739259
theorem B329159 : Blo 215810 329159 := bstep (se 1 (by rfl) ⟨246869, by rfl⟩ : syracuseStep 329159 = 493739) B493739
theorem B820793 : Blo 215810 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B493217 : Blo 215810 493217 := bstep (se 2 (by rfl) ⟨184956, by rfl⟩ : syracuseStep 493217 = 369913) B369913
theorem B329513 : Blo 215810 329513 := bstep (se 2 (by rfl) ⟨123567, by rfl⟩ : syracuseStep 329513 = 247135) B247135
theorem B329519 : Blo 215810 329519 := bstep (se 1 (by rfl) ⟨247139, by rfl⟩ : syracuseStep 329519 = 494279) B494279
theorem B1247183 : Blo 215810 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B493577 : Blo 215810 493577 := bstep (se 2 (by rfl) ⟨185091, by rfl⟩ : syracuseStep 493577 = 370183) B370183
theorem B461065 : Blo 215810 461065 := bstep (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) B345799
theorem B493991 : Blo 215810 493991 := bstep (se 1 (by rfl) ⟨370493, by rfl⟩ : syracuseStep 493991 = 740987) B740987
theorem B494099 : Blo 215810 494099 := bstep (se 1 (by rfl) ⟨370574, by rfl⟩ : syracuseStep 494099 = 741149) B741149
theorem B494153 : Blo 215810 494153 := bstep (se 2 (by rfl) ⟨185307, by rfl⟩ : syracuseStep 494153 = 370615) B370615
theorem B232399 : Blo 215810 232399 := bstep (se 1 (by rfl) ⟨174299, by rfl⟩ : syracuseStep 232399 = 348599) B348599
theorem B494567 : Blo 215810 494567 := bstep (se 1 (by rfl) ⟨370925, by rfl⟩ : syracuseStep 494567 = 741851) B741851
theorem B2100239 : Blo 215810 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B1248641 : Blo 215810 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B1642193 : Blo 215810 1642193 := bstep (se 2 (by rfl) ⟨615822, by rfl⟩ : syracuseStep 1642193 = 1231645) B1231645
theorem B8228587 : Blo 215810 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B2690833 : Blo 215810 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B364891 : Blo 215810 364891 := bstep (se 1 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 364891 = 547337) B547337
theorem B234047 : Blo 215810 234047 := bstep (se 1 (by rfl) ⟨175535, by rfl⟩ : syracuseStep 234047 = 351071) B351071
theorem B1184327 : Blo 215810 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B463439 : Blo 215810 463439 := bstep (se 1 (by rfl) ⟨347579, by rfl⟩ : syracuseStep 463439 = 695159) B695159
theorem B693211 : Blo 215810 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B3871901 : Blo 215810 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B791801 : Blo 215810 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B365863 : Blo 215810 365863 := bstep (se 1 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 365863 = 548795) B548795
theorem B1250599 : Blo 215810 1250599 := bstep (se 1 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 1250599 = 1875899) B1875899
theorem B693917 : Blo 215810 693917 := bstep (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) B260219
theorem B5936885 : Blo 215810 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B366383 : Blo 215810 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B464687 : Blo 215810 464687 := bstep (se 1 (by rfl) ⟨348515, by rfl⟩ : syracuseStep 464687 = 697031) B697031
theorem B1120081 : Blo 215810 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B497513 : Blo 215810 497513 := bstep (se 2 (by rfl) ⟨186567, by rfl⟩ : syracuseStep 497513 = 373135) B373135
theorem B1644623 : Blo 215810 1644623 := bstep (se 1 (by rfl) ⟨1233467, by rfl⟩ : syracuseStep 1644623 = 2466935) B2466935
theorem B1185977 : Blo 215810 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B2791705 : Blo 215810 2791705 := bstep (se 2 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 2791705 = 2093779) B2093779
theorem B4168421 : Blo 215810 4168421 := bstep (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) B781579
theorem B367591 : Blo 215810 367591 := bstep (se 1 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 367591 = 551387) B551387
theorem B1383961 : Blo 215810 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B3382879 : Blo 215810 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B990955 : Blo 215810 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B1810183 : Blo 215810 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B827293 : Blo 215810 827293 := bstep (se 3 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 827293 = 310235) B310235
theorem B1581065 : Blo 215810 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B2368001 : Blo 215810 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B1843883 : Blo 215810 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B4007029 : Blo 215810 4007029 := bstep (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) B375659
theorem B1844531 : Blo 215810 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B1648025 : Blo 215810 1648025 := bstep (se 2 (by rfl) ⟨618009, by rfl⟩ : syracuseStep 1648025 = 1236019) B1236019
theorem B1582649 : Blo 215810 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B370271 : Blo 215810 370271 := bstep (se 1 (by rfl) ⟨277703, by rfl⟩ : syracuseStep 370271 = 555407) B555407
theorem B730781 : Blo 215810 730781 := bstep (se 3 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 730781 = 274043) B274043
theorem B370487 : Blo 215810 370487 := bstep (se 1 (by rfl) ⟨277865, by rfl⟩ : syracuseStep 370487 = 555731) B555731
theorem B731321 : Blo 215810 731321 := bstep (se 2 (by rfl) ⟨274245, by rfl⟩ : syracuseStep 731321 = 548491) B548491
theorem B1681661 : Blo 215810 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B15935849 : Blo 215810 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B928655 : Blo 215810 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B1092689 : Blo 215810 1092689 := bstep (se 2 (by rfl) ⟨409758, by rfl⟩ : syracuseStep 1092689 = 819517) B819517
theorem B273775 : Blo 215810 273775 := bstep (se 1 (by rfl) ⟨205331, by rfl⟩ : syracuseStep 273775 = 410663) B410663
theorem B830969 : Blo 215810 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B929339 : Blo 215810 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B732833 : Blo 215810 732833 := bstep (se 2 (by rfl) ⟨274812, by rfl⟩ : syracuseStep 732833 = 549625) B549625
theorem B733697 : Blo 215810 733697 := bstep (se 2 (by rfl) ⟨275136, by rfl⟩ : syracuseStep 733697 = 550273) B550273
theorem B1782323 : Blo 215810 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B275015 : Blo 215810 275015 := bstep (se 1 (by rfl) ⟨206261, by rfl⟩ : syracuseStep 275015 = 412523) B412523
theorem B832153 : Blo 215810 832153 := bstep (se 2 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 832153 = 624115) B624115
theorem B275167 : Blo 215810 275167 := bstep (se 1 (by rfl) ⟨206375, by rfl⟩ : syracuseStep 275167 = 412751) B412751
theorem B832457 : Blo 215810 832457 := bstep (se 2 (by rfl) ⟨312171, by rfl⟩ : syracuseStep 832457 = 624343) B624343
theorem B734183 : Blo 215810 734183 := bstep (se 1 (by rfl) ⟨550637, by rfl⟩ : syracuseStep 734183 = 1101275) B1101275
theorem B734507 : Blo 215810 734507 := bstep (se 1 (by rfl) ⟨550880, by rfl⟩ : syracuseStep 734507 = 1101761) B1101761
theorem B931115 : Blo 215810 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B243067 : Blo 215810 243067 := bstep (se 1 (by rfl) ⟨182300, by rfl⟩ : syracuseStep 243067 = 364601) B364601
theorem B734777 : Blo 215810 734777 := bstep (se 2 (by rfl) ⟨275541, by rfl⟩ : syracuseStep 734777 = 551083) B551083
theorem B308971 : Blo 215810 308971 := bstep (se 1 (by rfl) ⟨231728, by rfl⟩ : syracuseStep 308971 = 463457) B463457
theorem B243535 : Blo 215810 243535 := bstep (se 1 (by rfl) ⟨182651, by rfl⟩ : syracuseStep 243535 = 365303) B365303
theorem B309199 : Blo 215810 309199 := bstep (se 1 (by rfl) ⟨231899, by rfl⟩ : syracuseStep 309199 = 463799) B463799
theorem B243931 : Blo 215810 243931 := bstep (se 1 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 243931 = 365897) B365897
theorem B244219 : Blo 215810 244219 := bstep (se 1 (by rfl) ⟨183164, by rfl⟩ : syracuseStep 244219 = 366329) B366329
theorem B2341493 : Blo 215810 2341493 := bstep (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) B219515
theorem B244399 : Blo 215810 244399 := bstep (se 1 (by rfl) ⟨183299, by rfl⟩ : syracuseStep 244399 = 366599) B366599
theorem B736019 : Blo 215810 736019 := bstep (se 1 (by rfl) ⟨552014, by rfl⟩ : syracuseStep 736019 = 1104029) B1104029
theorem B244687 : Blo 215810 244687 := bstep (se 1 (by rfl) ⟨183515, by rfl⟩ : syracuseStep 244687 = 367031) B367031
theorem B2374877 : Blo 215810 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B2407747 : Blo 215810 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B245083 : Blo 215810 245083 := bstep (se 1 (by rfl) ⟨183812, by rfl⟩ : syracuseStep 245083 = 367625) B367625
theorem B245191 : Blo 215810 245191 := bstep (se 1 (by rfl) ⟨183893, by rfl⟩ : syracuseStep 245191 = 367787) B367787
theorem B1097225 : Blo 215810 1097225 := bstep (se 2 (by rfl) ⟨411459, by rfl⟩ : syracuseStep 1097225 = 822919) B822919
theorem B2866747 : Blo 215810 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B736883 : Blo 215810 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B245551 : Blo 215810 245551 := bstep (se 1 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 245551 = 368327) B368327
theorem B737153 : Blo 215810 737153 := bstep (se 2 (by rfl) ⟨276432, by rfl⟩ : syracuseStep 737153 = 552865) B552865
theorem B245659 : Blo 215810 245659 := bstep (se 1 (by rfl) ⟨184244, by rfl⟩ : syracuseStep 245659 = 368489) B368489
theorem B1982501 : Blo 215810 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B246055 : Blo 215810 246055 := bstep (se 1 (by rfl) ⟨184541, by rfl⟩ : syracuseStep 246055 = 369083) B369083
theorem B246127 : Blo 215810 246127 := bstep (se 1 (by rfl) ⟨184595, by rfl⟩ : syracuseStep 246127 = 369191) B369191
theorem B246343 : Blo 215810 246343 := bstep (se 1 (by rfl) ⟨184757, by rfl⟩ : syracuseStep 246343 = 369515) B369515
theorem B14959235 : Blo 215810 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B737963 : Blo 215810 737963 := bstep (se 1 (by rfl) ⟨553472, by rfl⟩ : syracuseStep 737963 = 1106945) B1106945
theorem B738503 : Blo 215810 738503 := bstep (se 1 (by rfl) ⟨553877, by rfl⟩ : syracuseStep 738503 = 1107755) B1107755
theorem B1099169 : Blo 215810 1099169 := bstep (se 2 (by rfl) ⟨412188, by rfl⟩ : syracuseStep 1099169 = 824377) B824377
theorem B247207 : Blo 215810 247207 := bstep (se 1 (by rfl) ⟨185405, by rfl⟩ : syracuseStep 247207 = 370811) B370811
theorem B2803187 : Blo 215810 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B345863 : Blo 215810 345863 := bstep (se 1 (by rfl) ⟨259397, by rfl⟩ : syracuseStep 345863 = 518795) B518795
theorem B1624349 : Blo 215810 1624349 := bstep (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) B609131
theorem B2673107 : Blo 215810 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B346619 : Blo 215810 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B740015 : Blo 215810 740015 := bstep (se 1 (by rfl) ⟨555011, by rfl⟩ : syracuseStep 740015 = 1110023) B1110023
theorem B215855 : Blo 215810 215855 := bstep (se 1 (by rfl) ⟨161891, by rfl⟩ : syracuseStep 215855 = 323783) B323783
theorem B215963 : Blo 215810 215963 := bstep (se 1 (by rfl) ⟨161972, by rfl⟩ : syracuseStep 215963 = 323945) B323945
theorem B216015 : Blo 215810 216015 := bstep (se 1 (by rfl) ⟨162011, by rfl⟩ : syracuseStep 216015 = 324023) B324023
theorem B216039 : Blo 215810 216039 := bstep (se 1 (by rfl) ⟨162029, by rfl⟩ : syracuseStep 216039 = 324059) B324059
theorem B740339 : Blo 215810 740339 := bstep (se 1 (by rfl) ⟨555254, by rfl⟩ : syracuseStep 740339 = 1110509) B1110509
theorem B1395751 : Blo 215810 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B5262515 : Blo 215810 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B8801459 : Blo 215810 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B216351 : Blo 215810 216351 := bstep (se 1 (by rfl) ⟨162263, by rfl⟩ : syracuseStep 216351 = 324527) B324527
theorem B216411 : Blo 215810 216411 := bstep (se 1 (by rfl) ⟨162308, by rfl⟩ : syracuseStep 216411 = 324617) B324617
theorem B216431 : Blo 215810 216431 := bstep (se 1 (by rfl) ⟨162323, by rfl⟩ : syracuseStep 216431 = 324647) B324647
theorem B8539505 : Blo 215810 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1658231 : Blo 215810 1658231 := bstep (se 1 (by rfl) ⟨1243673, by rfl⟩ : syracuseStep 1658231 = 2487347) B2487347
theorem B216487 : Blo 215810 216487 := bstep (se 1 (by rfl) ⟨162365, by rfl⟩ : syracuseStep 216487 = 324731) B324731
theorem B937403 : Blo 215810 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B2805191 : Blo 215810 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B216571 : Blo 215810 216571 := bstep (se 1 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 216571 = 324857) B324857
theorem B740879 : Blo 215810 740879 := bstep (se 1 (by rfl) ⟨555659, by rfl⟩ : syracuseStep 740879 = 1111319) B1111319
theorem B216639 : Blo 215810 216639 := bstep (se 1 (by rfl) ⟨162479, by rfl⟩ : syracuseStep 216639 = 324959) B324959
theorem B216647 : Blo 215810 216647 := bstep (se 1 (by rfl) ⟨162485, by rfl⟩ : syracuseStep 216647 = 324971) B324971
theorem B1068659 : Blo 215810 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B216799 : Blo 215810 216799 := bstep (se 1 (by rfl) ⟨162599, by rfl⟩ : syracuseStep 216799 = 325199) B325199
theorem B413419 : Blo 215810 413419 := bstep (se 1 (by rfl) ⟨310064, by rfl⟩ : syracuseStep 413419 = 620129) B620129
theorem B216879 : Blo 215810 216879 := bstep (se 1 (by rfl) ⟨162659, by rfl⟩ : syracuseStep 216879 = 325319) B325319
theorem B3002159 : Blo 215810 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B413495 : Blo 215810 413495 := bstep (se 1 (by rfl) ⟨310121, by rfl⟩ : syracuseStep 413495 = 620243) B620243
theorem B216987 : Blo 215810 216987 := bstep (se 1 (by rfl) ⟨162740, by rfl⟩ : syracuseStep 216987 = 325481) B325481
theorem B217039 : Blo 215810 217039 := bstep (se 1 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 217039 = 325559) B325559
theorem B217063 : Blo 215810 217063 := bstep (se 1 (by rfl) ⟨162797, by rfl⟩ : syracuseStep 217063 = 325595) B325595
theorem B1232921 : Blo 215810 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B938155 : Blo 215810 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B217375 : Blo 215810 217375 := bstep (se 1 (by rfl) ⟨163031, by rfl⟩ : syracuseStep 217375 = 326063) B326063
theorem B217435 : Blo 215810 217435 := bstep (se 1 (by rfl) ⟨163076, by rfl⟩ : syracuseStep 217435 = 326153) B326153
theorem B217455 : Blo 215810 217455 := bstep (se 1 (by rfl) ⟨163091, by rfl⟩ : syracuseStep 217455 = 326183) B326183
theorem B217511 : Blo 215810 217511 := bstep (se 1 (by rfl) ⟨163133, by rfl⟩ : syracuseStep 217511 = 326267) B326267
theorem B414163 : Blo 215810 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B217595 : Blo 215810 217595 := bstep (se 1 (by rfl) ⟨163196, by rfl⟩ : syracuseStep 217595 = 326393) B326393
theorem B217663 : Blo 215810 217663 := bstep (se 1 (by rfl) ⟨163247, by rfl⟩ : syracuseStep 217663 = 326495) B326495
theorem B217671 : Blo 215810 217671 := bstep (se 1 (by rfl) ⟨163253, by rfl⟩ : syracuseStep 217671 = 326507) B326507
theorem B414391 : Blo 215810 414391 := bstep (se 1 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 414391 = 621587) B621587
theorem B217823 : Blo 215810 217823 := bstep (se 1 (by rfl) ⟨163367, by rfl⟩ : syracuseStep 217823 = 326735) B326735
theorem B217903 : Blo 215810 217903 := bstep (se 1 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 217903 = 326855) B326855
theorem B218011 : Blo 215810 218011 := bstep (se 1 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 218011 = 327017) B327017
theorem B4674509 : Blo 215810 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B218063 : Blo 215810 218063 := bstep (se 1 (by rfl) ⟨163547, by rfl⟩ : syracuseStep 218063 = 327095) B327095
theorem B218087 : Blo 215810 218087 := bstep (se 1 (by rfl) ⟨163565, by rfl⟩ : syracuseStep 218087 = 327131) B327131
theorem B414695 : Blo 215810 414695 := bstep (se 1 (by rfl) ⟨311021, by rfl⟩ : syracuseStep 414695 = 622043) B622043
theorem B414953 : Blo 215810 414953 := bstep (se 2 (by rfl) ⟨155607, by rfl⟩ : syracuseStep 414953 = 311215) B311215
theorem B2249975 : Blo 215810 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B4773113 : Blo 215810 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B218399 : Blo 215810 218399 := bstep (se 1 (by rfl) ⟨163799, by rfl⟩ : syracuseStep 218399 = 327599) B327599
theorem B218459 : Blo 215810 218459 := bstep (se 1 (by rfl) ⟨163844, by rfl⟩ : syracuseStep 218459 = 327689) B327689
theorem B218479 : Blo 215810 218479 := bstep (se 1 (by rfl) ⟨163859, by rfl⟩ : syracuseStep 218479 = 327719) B327719
theorem B218535 : Blo 215810 218535 := bstep (se 1 (by rfl) ⟨163901, by rfl⟩ : syracuseStep 218535 = 327803) B327803
theorem B1857005 : Blo 215810 1857005 := bstep (se 3 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 1857005 = 696377) B696377
theorem B218619 : Blo 215810 218619 := bstep (se 1 (by rfl) ⟨163964, by rfl⟩ : syracuseStep 218619 = 327929) B327929
theorem B218687 : Blo 215810 218687 := bstep (se 1 (by rfl) ⟨164015, by rfl⟩ : syracuseStep 218687 = 328031) B328031
theorem B218695 : Blo 215810 218695 := bstep (se 1 (by rfl) ⟨164021, by rfl⟩ : syracuseStep 218695 = 328043) B328043
theorem B6248123 : Blo 215810 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B218847 : Blo 215810 218847 := bstep (se 1 (by rfl) ⟨164135, by rfl⟩ : syracuseStep 218847 = 328271) B328271
theorem B218927 : Blo 215810 218927 := bstep (se 1 (by rfl) ⟨164195, by rfl⟩ : syracuseStep 218927 = 328391) B328391
theorem B546689 : Blo 215810 546689 := bstep (se 2 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 546689 = 410017) B410017
theorem B219035 : Blo 215810 219035 := bstep (se 1 (by rfl) ⟨164276, by rfl⟩ : syracuseStep 219035 = 328553) B328553
theorem B219087 : Blo 215810 219087 := bstep (se 1 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 219087 = 328631) B328631
theorem B219111 : Blo 215810 219111 := bstep (se 1 (by rfl) ⟨164333, by rfl⟩ : syracuseStep 219111 = 328667) B328667
theorem B1038415 : Blo 215810 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B415849 : Blo 215810 415849 := bstep (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) B311887
theorem B4675715 : Blo 215810 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B416009 : Blo 215810 416009 := bstep (se 2 (by rfl) ⟨156003, by rfl⟩ : syracuseStep 416009 = 312007) B312007
theorem B219423 : Blo 215810 219423 := bstep (se 1 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 219423 = 329135) B329135
theorem B547145 : Blo 215810 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B219483 : Blo 215810 219483 := bstep (se 1 (by rfl) ⟨164612, by rfl⟩ : syracuseStep 219483 = 329225) B329225
theorem B219503 : Blo 215810 219503 := bstep (se 1 (by rfl) ⟨164627, by rfl⟩ : syracuseStep 219503 = 329255) B329255
theorem B219559 : Blo 215810 219559 := bstep (se 1 (by rfl) ⟨164669, by rfl⟩ : syracuseStep 219559 = 329339) B329339
theorem B219643 : Blo 215810 219643 := bstep (se 1 (by rfl) ⟨164732, by rfl⟩ : syracuseStep 219643 = 329465) B329465
theorem B1235519 : Blo 215810 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B219711 : Blo 215810 219711 := bstep (se 1 (by rfl) ⟨164783, by rfl⟩ : syracuseStep 219711 = 329567) B329567
theorem B219719 : Blo 215810 219719 := bstep (se 1 (by rfl) ⟨164789, by rfl⟩ : syracuseStep 219719 = 329579) B329579
theorem B547499 : Blo 215810 547499 := bstep (se 1 (by rfl) ⟨410624, by rfl⟩ : syracuseStep 547499 = 821249) B821249
theorem B1071863 : Blo 215810 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B2349931 : Blo 215810 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B1105163 : Blo 215810 1105163 := bstep (se 1 (by rfl) ⟨828872, by rfl⟩ : syracuseStep 1105163 = 1657745) B1657745
theorem B548815 : Blo 215810 548815 := bstep (se 1 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 548815 = 823223) B823223
theorem B614729 : Blo 215810 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B1499795 : Blo 215810 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B1106783 : Blo 215810 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B549787 : Blo 215810 549787 := bstep (se 1 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 549787 = 824681) B824681
theorem B4449451 : Blo 215810 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B2811185 : Blo 215810 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B615869 : Blo 215810 615869 := bstep (se 3 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 615869 = 230951) B230951
theorem B550921 : Blo 215810 550921 := bstep (se 2 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 550921 = 413191) B413191
theorem B2222095 : Blo 215810 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B845959 : Blo 215810 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B223579 : Blo 215810 223579 := bstep (se 1 (by rfl) ⟨167684, by rfl⟩ : syracuseStep 223579 = 335369) B335369
theorem B616871 : Blo 215810 616871 := bstep (se 1 (by rfl) ⟨462653, by rfl⟩ : syracuseStep 616871 = 925307) B925307
theorem B584119 : Blo 215810 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B3369595 : Blo 215810 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B486071 : Blo 215810 486071 := bstep (se 1 (by rfl) ⟨364553, by rfl⟩ : syracuseStep 486071 = 729107) B729107
theorem B1108669 : Blo 215810 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B1108727 : Blo 215810 1108727 := bstep (se 1 (by rfl) ⟨831545, by rfl⟩ : syracuseStep 1108727 = 1663091) B1663091
theorem B486287 : Blo 215810 486287 := bstep (se 1 (by rfl) ⟨364715, by rfl⟩ : syracuseStep 486287 = 729431) B729431
theorem B420763 : Blo 215810 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B584801 : Blo 215810 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B1109213 : Blo 215810 1109213 := bstep (se 3 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 1109213 = 415955) B415955
theorem B552329 : Blo 215810 552329 := bstep (se 2 (by rfl) ⟨207123, by rfl⟩ : syracuseStep 552329 = 414247) B414247
theorem B552379 : Blo 215810 552379 := bstep (se 1 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 552379 = 828569) B828569
theorem B487007 : Blo 215810 487007 := bstep (se 1 (by rfl) ⟨365255, by rfl⟩ : syracuseStep 487007 = 730511) B730511
theorem B552683 : Blo 215810 552683 := bstep (se 1 (by rfl) ⟨414512, by rfl⟩ : syracuseStep 552683 = 829025) B829025
theorem B487223 : Blo 215810 487223 := bstep (se 1 (by rfl) ⟨365417, by rfl⟩ : syracuseStep 487223 = 730835) B730835
theorem B1044353 : Blo 215810 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B7991297 : Blo 215810 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B487529 : Blo 215810 487529 := bstep (se 2 (by rfl) ⟨182823, by rfl⟩ : syracuseStep 487529 = 365647) B365647
theorem B323849 : Blo 215810 323849 := bstep (se 2 (by rfl) ⟨121443, by rfl⟩ : syracuseStep 323849 = 242887) B242887
theorem B4157729 : Blo 215810 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B323951 : Blo 215810 323951 := bstep (se 1 (by rfl) ⟨242963, by rfl⟩ : syracuseStep 323951 = 485927) B485927
theorem B2027891 : Blo 215810 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B324167 : Blo 215810 324167 := bstep (se 1 (by rfl) ⟨243125, by rfl⟩ : syracuseStep 324167 = 486251) B486251
theorem B520775 : Blo 215810 520775 := bstep (se 1 (by rfl) ⟨390581, by rfl⟩ : syracuseStep 520775 = 781163) B781163
theorem B488015 : Blo 215810 488015 := bstep (se 1 (by rfl) ⟨366011, by rfl⟩ : syracuseStep 488015 = 732023) B732023
theorem B324203 : Blo 215810 324203 := bstep (se 1 (by rfl) ⟨243152, by rfl⟩ : syracuseStep 324203 = 486305) B486305
theorem B7959161 : Blo 215810 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B553655 : Blo 215810 553655 := bstep (se 1 (by rfl) ⟨415241, by rfl⟩ : syracuseStep 553655 = 830483) B830483
theorem B488159 : Blo 215810 488159 := bstep (se 1 (by rfl) ⟨366119, by rfl⟩ : syracuseStep 488159 = 732239) B732239
theorem B324431 : Blo 215810 324431 := bstep (se 1 (by rfl) ⟨243323, by rfl⟩ : syracuseStep 324431 = 486647) B486647
theorem B488411 : Blo 215810 488411 := bstep (se 1 (by rfl) ⟨366308, by rfl⟩ : syracuseStep 488411 = 732617) B732617
theorem B783323 : Blo 215810 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B521255 : Blo 215810 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B488591 : Blo 215810 488591 := bstep (se 1 (by rfl) ⟨366443, by rfl⟩ : syracuseStep 488591 = 732887) B732887
theorem B1995923 : Blo 215810 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B324827 : Blo 215810 324827 := bstep (se 1 (by rfl) ⟨243620, by rfl⟩ : syracuseStep 324827 = 487241) B487241
theorem B488681 : Blo 215810 488681 := bstep (se 2 (by rfl) ⟨183255, by rfl⟩ : syracuseStep 488681 = 366511) B366511
theorem B488735 : Blo 215810 488735 := bstep (se 1 (by rfl) ⟨366551, by rfl⟩ : syracuseStep 488735 = 733103) B733103
theorem B947495 : Blo 215810 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B325001 : Blo 215810 325001 := bstep (se 2 (by rfl) ⟨121875, by rfl⟩ : syracuseStep 325001 = 243751) B243751
theorem B587321 : Blo 215810 587321 := bstep (se 2 (by rfl) ⟨220245, by rfl⟩ : syracuseStep 587321 = 440491) B440491
theorem B1046105 : Blo 215810 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B1242809 : Blo 215810 1242809 := bstep (se 2 (by rfl) ⟨466053, by rfl⟩ : syracuseStep 1242809 = 932107) B932107
theorem B325355 : Blo 215810 325355 := bstep (se 1 (by rfl) ⟨244016, by rfl⟩ : syracuseStep 325355 = 488033) B488033
theorem B554759 : Blo 215810 554759 := bstep (se 1 (by rfl) ⟨416069, by rfl⟩ : syracuseStep 554759 = 832139) B832139
theorem B489257 : Blo 215810 489257 := bstep (se 2 (by rfl) ⟨183471, by rfl⟩ : syracuseStep 489257 = 366943) B366943
theorem B554809 : Blo 215810 554809 := bstep (se 2 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 554809 = 416107) B416107
theorem B325583 : Blo 215810 325583 := bstep (se 1 (by rfl) ⟨244187, by rfl⟩ : syracuseStep 325583 = 488375) B488375
theorem B1570859 : Blo 215810 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B555113 : Blo 215810 555113 := bstep (se 2 (by rfl) ⟨208167, by rfl⟩ : syracuseStep 555113 = 416335) B416335
theorem B2357579 : Blo 215810 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B325979 : Blo 215810 325979 := bstep (se 1 (by rfl) ⟨244484, by rfl⟩ : syracuseStep 325979 = 488969) B488969
theorem B883055 : Blo 215810 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B1112615 : Blo 215810 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B326207 : Blo 215810 326207 := bstep (se 1 (by rfl) ⟨244655, by rfl⟩ : syracuseStep 326207 = 489311) B489311
theorem B948809 : Blo 215810 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B555599 : Blo 215810 555599 := bstep (se 1 (by rfl) ⟨416699, by rfl⟩ : syracuseStep 555599 = 833399) B833399
theorem B326327 : Blo 215810 326327 := bstep (se 1 (by rfl) ⟨244745, by rfl⟩ : syracuseStep 326327 = 489491) B489491
theorem B260911 : Blo 215810 260911 := bstep (se 1 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 260911 = 391367) B391367
theorem B490319 : Blo 215810 490319 := bstep (se 1 (by rfl) ⟨367739, by rfl⟩ : syracuseStep 490319 = 735479) B735479
theorem B326555 : Blo 215810 326555 := bstep (se 1 (by rfl) ⟨244916, by rfl⟩ : syracuseStep 326555 = 489833) B489833
theorem B490535 : Blo 215810 490535 := bstep (se 1 (by rfl) ⟨367901, by rfl⟩ : syracuseStep 490535 = 735803) B735803
theorem B556247 : Blo 215810 556247 := bstep (se 1 (by rfl) ⟨417185, by rfl⟩ : syracuseStep 556247 = 834371) B834371
theorem B392411 : Blo 215810 392411 := bstep (se 1 (by rfl) ⟨294308, by rfl⟩ : syracuseStep 392411 = 588617) B588617
theorem B490715 : Blo 215810 490715 := bstep (se 1 (by rfl) ⟨368036, by rfl⟩ : syracuseStep 490715 = 736073) B736073
theorem B523513 : Blo 215810 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B326951 : Blo 215810 326951 := bstep (se 1 (by rfl) ⟨245213, by rfl⟩ : syracuseStep 326951 = 490427) B490427
theorem B327035 : Blo 215810 327035 := bstep (se 1 (by rfl) ⟨245276, by rfl⟩ : syracuseStep 327035 = 490553) B490553
theorem B490913 : Blo 215810 490913 := bstep (se 2 (by rfl) ⟨184092, by rfl⟩ : syracuseStep 490913 = 368185) B368185
theorem B2096549 : Blo 215810 2096549 := bstep (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) B393103
theorem B327161 : Blo 215810 327161 := bstep (se 2 (by rfl) ⟨122685, by rfl⟩ : syracuseStep 327161 = 245371) B245371
theorem B327263 : Blo 215810 327263 := bstep (se 1 (by rfl) ⟨245447, by rfl⟩ : syracuseStep 327263 = 490895) B490895
theorem B1244767 : Blo 215810 1244767 := bstep (se 1 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 1244767 = 1867151) B1867151
theorem B327479 : Blo 215810 327479 := bstep (se 1 (by rfl) ⟨245609, by rfl⟩ : syracuseStep 327479 = 491219) B491219
theorem B491471 : Blo 215810 491471 := bstep (se 1 (by rfl) ⟨368603, by rfl⟩ : syracuseStep 491471 = 737207) B737207
theorem B327899 : Blo 215810 327899 := bstep (se 1 (by rfl) ⟨245924, by rfl⟩ : syracuseStep 327899 = 491849) B491849
theorem B327911 : Blo 215810 327911 := bstep (se 1 (by rfl) ⟨245933, by rfl⟩ : syracuseStep 327911 = 491867) B491867
theorem B328073 : Blo 215810 328073 := bstep (se 2 (by rfl) ⟨123027, by rfl⟩ : syracuseStep 328073 = 246055) B246055
theorem B491975 : Blo 215810 491975 := bstep (se 1 (by rfl) ⟨368981, by rfl⟩ : syracuseStep 491975 = 737963) B737963
theorem B262607 : Blo 215810 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B328169 : Blo 215810 328169 := bstep (se 2 (by rfl) ⟨123063, by rfl⟩ : syracuseStep 328169 = 246127) B246127
theorem B328295 : Blo 215810 328295 := bstep (se 1 (by rfl) ⟨246221, by rfl⟩ : syracuseStep 328295 = 492443) B492443
theorem B328427 : Blo 215810 328427 := bstep (se 1 (by rfl) ⟨246320, by rfl⟩ : syracuseStep 328427 = 492641) B492641
theorem B328457 : Blo 215810 328457 := bstep (se 2 (by rfl) ⟨123171, by rfl⟩ : syracuseStep 328457 = 246343) B246343
theorem B492335 : Blo 215810 492335 := bstep (se 1 (by rfl) ⟨369251, by rfl⟩ : syracuseStep 492335 = 738503) B738503
theorem B1639277 : Blo 215810 1639277 := bstep (se 3 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 1639277 = 614729) B614729
theorem B328559 : Blo 215810 328559 := bstep (se 1 (by rfl) ⟨246419, by rfl⟩ : syracuseStep 328559 = 492839) B492839
theorem B1868791 : Blo 215810 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B328811 : Blo 215810 328811 := bstep (se 1 (by rfl) ⟨246608, by rfl⟩ : syracuseStep 328811 = 493217) B493217
theorem B230575 : Blo 215810 230575 := bstep (se 1 (by rfl) ⟨172931, by rfl⟩ : syracuseStep 230575 = 345863) B345863
theorem B329051 : Blo 215810 329051 := bstep (se 1 (by rfl) ⟨246788, by rfl⟩ : syracuseStep 329051 = 493577) B493577
theorem B5342705 : Blo 215810 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B624125 : Blo 215810 624125 := bstep (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) B234047
theorem B1082899 : Blo 215810 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B5932601 : Blo 215810 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B329327 : Blo 215810 329327 := bstep (se 1 (by rfl) ⟨246995, by rfl⟩ : syracuseStep 329327 = 493991) B493991
theorem B329399 : Blo 215810 329399 := bstep (se 1 (by rfl) ⟨247049, by rfl⟩ : syracuseStep 329399 = 494099) B494099
theorem B329435 : Blo 215810 329435 := bstep (se 1 (by rfl) ⟨247076, by rfl⟩ : syracuseStep 329435 = 494153) B494153
theorem B2098973 : Blo 215810 2098973 := bstep (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) B787115
theorem B493343 : Blo 215810 493343 := bstep (se 1 (by rfl) ⟨370007, by rfl⟩ : syracuseStep 493343 = 740015) B740015
theorem B329609 : Blo 215810 329609 := bstep (se 2 (by rfl) ⟨123603, by rfl⟩ : syracuseStep 329609 = 247207) B247207
theorem B329711 : Blo 215810 329711 := bstep (se 1 (by rfl) ⟨247283, by rfl⟩ : syracuseStep 329711 = 494567) B494567
theorem B493559 : Blo 215810 493559 := bstep (se 1 (by rfl) ⟨370169, by rfl⟩ : syracuseStep 493559 = 740339) B740339
theorem B3508343 : Blo 215810 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B5867639 : Blo 215810 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B624935 : Blo 215810 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B1870127 : Blo 215810 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B493919 : Blo 215810 493919 := bstep (se 1 (by rfl) ⟨370439, by rfl⟩ : syracuseStep 493919 = 740879) B740879
theorem B2001439 : Blo 215810 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B821947 : Blo 215810 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B789551 : Blo 215810 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B10325069 : Blo 215810 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B3116339 : Blo 215810 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B5999933 : Blo 215810 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B2526653 : Blo 215810 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B4492793 : Blo 215810 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B3182075 : Blo 215810 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B527867 : Blo 215810 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B1478225 : Blo 215810 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B462611 : Blo 215810 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B4165415 : Blo 215810 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B561017 : Blo 215810 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B364459 : Blo 215810 364459 := bstep (se 1 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 364459 = 546689) B546689
theorem B3117143 : Blo 215810 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B790651 : Blo 215810 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B364763 : Blo 215810 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B823679 : Blo 215810 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B364999 : Blo 215810 364999 := bstep (se 1 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 364999 = 547499) B547499
theorem B365033 : Blo 215810 365033 := bstep (se 2 (by rfl) ⟨136887, by rfl⟩ : syracuseStep 365033 = 273775) B273775
theorem B1054043 : Blo 215810 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B1250873 : Blo 215810 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B1874123 : Blo 215810 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B366889 : Blo 215810 366889 := bstep (se 2 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 366889 = 275167) B275167
theorem B1055099 : Blo 215810 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B924281 : Blo 215810 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B2792069 : Blo 215810 2792069 := bstep (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) B523513
theorem B924317 : Blo 215810 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B10623899 : Blo 215810 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B728459 : Blo 215810 728459 := bstep (se 1 (by rfl) ⟨546344, by rfl⟩ : syracuseStep 728459 = 1092689) B1092689
theorem B368219 : Blo 215810 368219 := bstep (se 1 (by rfl) ⟨276164, by rfl⟩ : syracuseStep 368219 = 552329) B552329
theorem B368455 : Blo 215810 368455 := bstep (se 1 (by rfl) ⟨276341, by rfl⟩ : syracuseStep 368455 = 552683) B552683
theorem B1384553 : Blo 215810 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B1351927 : Blo 215810 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B1188215 : Blo 215810 1188215 := bstep (se 1 (by rfl) ⟨891161, by rfl⟩ : syracuseStep 1188215 = 1782323) B1782323
theorem B369103 : Blo 215810 369103 := bstep (se 1 (by rfl) ⟨276827, by rfl⟩ : syracuseStep 369103 = 553655) B553655
theorem B6333005 : Blo 215810 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B697403 : Blo 215810 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B828539 : Blo 215810 828539 := bstep (se 1 (by rfl) ⟨621404, by rfl⟩ : syracuseStep 828539 = 1242809) B1242809
theorem B369839 : Blo 215810 369839 := bstep (se 1 (by rfl) ⟨277379, by rfl⟩ : syracuseStep 369839 = 554759) B554759
theorem B370075 : Blo 215810 370075 := bstep (se 1 (by rfl) ⟨277556, by rfl⟩ : syracuseStep 370075 = 555113) B555113
theorem B632539 : Blo 215810 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B370399 : Blo 215810 370399 := bstep (se 1 (by rfl) ⟨277799, by rfl⟩ : syracuseStep 370399 = 555599) B555599
theorem B1845281 : Blo 215810 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B370831 : Blo 215810 370831 := bstep (se 1 (by rfl) ⟨278123, by rfl⟩ : syracuseStep 370831 = 556247) B556247
theorem B1321273 : Blo 215810 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B731483 : Blo 215810 731483 := bstep (se 1 (by rfl) ⟨548612, by rfl⟩ : syracuseStep 731483 = 1097225) B1097225
theorem B731753 : Blo 215810 731753 := bstep (se 2 (by rfl) ⟨274407, by rfl⟩ : syracuseStep 731753 = 548815) B548815
theorem B1321667 : Blo 215810 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B895799 : Blo 215810 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B502831 : Blo 215810 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B9972823 : Blo 215810 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B699977 : Blo 215810 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B732779 : Blo 215810 732779 := bstep (se 1 (by rfl) ⟨549584, by rfl⟩ : syracuseStep 732779 = 1099169) B1099169
theorem B5680801 : Blo 215810 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B733049 : Blo 215810 733049 := bstep (se 2 (by rfl) ⟨274893, by rfl⟩ : syracuseStep 733049 = 549787) B549787
theorem B831455 : Blo 215810 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B733373 : Blo 215810 733373 := bstep (se 3 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 733373 = 275015) B275015
theorem B1782071 : Blo 215810 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B1192421 : Blo 215810 1192421 := bstep (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) B223579
theorem B832427 : Blo 215810 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B1094795 : Blo 215810 1094795 := bstep (se 1 (by rfl) ⟨821096, by rfl⟩ : syracuseStep 1094795 = 1642193) B1642193
theorem B275663 : Blo 215810 275663 := bstep (se 1 (by rfl) ⟨206747, by rfl⟩ : syracuseStep 275663 = 413495) B413495
theorem B734561 : Blo 215810 734561 := bstep (se 2 (by rfl) ⟨275460, by rfl⟩ : syracuseStep 734561 = 550921) B550921
theorem B2962793 : Blo 215810 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1127945 : Blo 215810 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B276463 : Blo 215810 276463 := bstep (se 1 (by rfl) ⟨207347, by rfl⟩ : syracuseStep 276463 = 414695) B414695
theorem B276635 : Blo 215810 276635 := bstep (se 1 (by rfl) ⟨207476, by rfl⟩ : syracuseStep 276635 = 414953) B414953
theorem B244255 : Blo 215810 244255 := bstep (se 1 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 244255 = 366383) B366383
theorem B309791 : Blo 215810 309791 := bstep (se 1 (by rfl) ⟨232343, by rfl⟩ : syracuseStep 309791 = 464687) B464687
theorem B1096415 : Blo 215810 1096415 := bstep (se 1 (by rfl) ⟨822311, by rfl⟩ : syracuseStep 1096415 = 1644623) B1644623
theorem B277339 : Blo 215810 277339 := bstep (se 1 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 277339 = 416009) B416009
theorem B1391525 : Blo 215810 1391525 := bstep (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) B260911
theorem B736505 : Blo 215810 736505 := bstep (se 2 (by rfl) ⟨276189, by rfl⟩ : syracuseStep 736505 = 552379) B552379
theorem B736775 : Blo 215810 736775 := bstep (se 1 (by rfl) ⟨552581, by rfl⟩ : syracuseStep 736775 = 1105163) B1105163
theorem B1326701 : Blo 215810 1326701 := bstep (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) B497513
theorem B3587777 : Blo 215810 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B999863 : Blo 215810 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B1229255 : Blo 215810 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B737855 : Blo 215810 737855 := bstep (se 1 (by rfl) ⟨553391, by rfl⟩ : syracuseStep 737855 = 1106783) B1106783
theorem B1229687 : Blo 215810 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1098683 : Blo 215810 1098683 := bstep (se 1 (by rfl) ⟨824012, by rfl⟩ : syracuseStep 1098683 = 1648025) B1648025
theorem B410579 : Blo 215810 410579 := bstep (se 1 (by rfl) ⟨307934, by rfl⟩ : syracuseStep 410579 = 615869) B615869
theorem B246847 : Blo 215810 246847 := bstep (se 1 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 246847 = 370271) B370271
theorem B246991 : Blo 215810 246991 := bstep (se 1 (by rfl) ⟨185243, by rfl⟩ : syracuseStep 246991 = 370487) B370487
theorem B411247 : Blo 215810 411247 := bstep (se 1 (by rfl) ⟨308435, by rfl⟩ : syracuseStep 411247 = 616871) B616871
theorem B739151 : Blo 215810 739151 := bstep (se 1 (by rfl) ⟨554363, by rfl⟩ : syracuseStep 739151 = 1108727) B1108727
theorem B739475 : Blo 215810 739475 := bstep (se 1 (by rfl) ⟨554606, by rfl⟩ : syracuseStep 739475 = 1109213) B1109213
theorem B411961 : Blo 215810 411961 := bstep (se 2 (by rfl) ⟨154485, by rfl⟩ : syracuseStep 411961 = 308971) B308971
theorem B739745 : Blo 215810 739745 := bstep (se 2 (by rfl) ⟨277404, by rfl⟩ : syracuseStep 739745 = 554809) B554809
theorem B1493441 : Blo 215810 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B412265 : Blo 215810 412265 := bstep (se 2 (by rfl) ⟨154599, by rfl⟩ : syracuseStep 412265 = 309199) B309199
theorem B5327531 : Blo 215810 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B215899 : Blo 215810 215899 := bstep (se 1 (by rfl) ⟨161924, by rfl⟩ : syracuseStep 215899 = 323849) B323849
theorem B2771819 : Blo 215810 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B215967 : Blo 215810 215967 := bstep (se 1 (by rfl) ⟨161975, by rfl⟩ : syracuseStep 215967 = 323951) B323951
theorem B3722273 : Blo 215810 3722273 := bstep (se 2 (by rfl) ⟨1395852, by rfl⟩ : syracuseStep 3722273 = 2791705) B2791705
theorem B216111 : Blo 215810 216111 := bstep (se 1 (by rfl) ⟨162083, by rfl⟩ : syracuseStep 216111 = 324167) B324167
theorem B347183 : Blo 215810 347183 := bstep (se 1 (by rfl) ⟨260387, by rfl⟩ : syracuseStep 347183 = 520775) B520775
theorem B216135 : Blo 215810 216135 := bstep (se 1 (by rfl) ⟨162101, by rfl⟩ : syracuseStep 216135 = 324203) B324203
theorem B216287 : Blo 215810 216287 := bstep (se 1 (by rfl) ⟨162215, by rfl⟩ : syracuseStep 216287 = 324431) B324431
theorem B347503 : Blo 215810 347503 := bstep (se 1 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 347503 = 521255) B521255
theorem B1330615 : Blo 215810 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B216551 : Blo 215810 216551 := bstep (se 1 (by rfl) ⟨162413, by rfl⟩ : syracuseStep 216551 = 324827) B324827
theorem B216667 : Blo 215810 216667 := bstep (se 1 (by rfl) ⟨162500, by rfl⟩ : syracuseStep 216667 = 325001) B325001
theorem B3133241 : Blo 215810 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B216903 : Blo 215810 216903 := bstep (se 1 (by rfl) ⟨162677, by rfl⟩ : syracuseStep 216903 = 325355) B325355
theorem B217055 : Blo 215810 217055 := bstep (se 1 (by rfl) ⟨162791, by rfl⟩ : syracuseStep 217055 = 325583) B325583
theorem B217319 : Blo 215810 217319 := bstep (se 1 (by rfl) ⟨162989, by rfl⟩ : syracuseStep 217319 = 325979) B325979
theorem B741743 : Blo 215810 741743 := bstep (se 1 (by rfl) ⟨556307, by rfl⟩ : syracuseStep 741743 = 1112615) B1112615
theorem B217471 : Blo 215810 217471 := bstep (se 1 (by rfl) ⟨163103, by rfl⟩ : syracuseStep 217471 = 326207) B326207
theorem B1560995 : Blo 215810 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B217551 : Blo 215810 217551 := bstep (se 1 (by rfl) ⟨163163, by rfl⟩ : syracuseStep 217551 = 326327) B326327
theorem B217703 : Blo 215810 217703 := bstep (se 1 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 217703 = 326555) B326555
theorem B3822329 : Blo 215810 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B4510505 : Blo 215810 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B1659689 : Blo 215810 1659689 := bstep (se 2 (by rfl) ⟨622383, by rfl⟩ : syracuseStep 1659689 = 1244767) B1244767
theorem B217967 : Blo 215810 217967 := bstep (se 1 (by rfl) ⟨163475, by rfl⟩ : syracuseStep 217967 = 326951) B326951
theorem B218023 : Blo 215810 218023 := bstep (se 1 (by rfl) ⟨163517, by rfl⟩ : syracuseStep 218023 = 327035) B327035
theorem B1397699 : Blo 215810 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B218107 : Blo 215810 218107 := bstep (se 1 (by rfl) ⟨163580, by rfl⟩ : syracuseStep 218107 = 327161) B327161
theorem B2413577 : Blo 215810 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B218175 : Blo 215810 218175 := bstep (se 1 (by rfl) ⟨163631, by rfl⟩ : syracuseStep 218175 = 327263) B327263
theorem B218319 : Blo 215810 218319 := bstep (se 1 (by rfl) ⟨163739, by rfl⟩ : syracuseStep 218319 = 327479) B327479
theorem B1103057 : Blo 215810 1103057 := bstep (se 2 (by rfl) ⟨413646, by rfl⟩ : syracuseStep 1103057 = 827293) B827293
theorem B218523 : Blo 215810 218523 := bstep (se 1 (by rfl) ⟨163892, by rfl⟩ : syracuseStep 218523 = 327785) B327785
theorem B218735 : Blo 215810 218735 := bstep (se 1 (by rfl) ⟨164051, by rfl⟩ : syracuseStep 218735 = 328103) B328103
theorem B218791 : Blo 215810 218791 := bstep (se 1 (by rfl) ⟨164093, by rfl⟩ : syracuseStep 218791 = 328187) B328187
theorem B218875 : Blo 215810 218875 := bstep (se 1 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 218875 = 328313) B328313
theorem B218911 : Blo 215810 218911 := bstep (se 1 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 218911 = 328367) B328367
theorem B218943 : Blo 215810 218943 := bstep (se 1 (by rfl) ⟨164207, by rfl⟩ : syracuseStep 218943 = 328415) B328415
theorem B219119 : Blo 215810 219119 := bstep (se 1 (by rfl) ⟨164339, by rfl⟩ : syracuseStep 219119 = 328679) B328679
theorem B219291 : Blo 215810 219291 := bstep (se 1 (by rfl) ⟨164468, by rfl⟩ : syracuseStep 219291 = 328937) B328937
theorem B219327 : Blo 215810 219327 := bstep (se 1 (by rfl) ⟨164495, by rfl⟩ : syracuseStep 219327 = 328991) B328991
theorem B219439 : Blo 215810 219439 := bstep (se 1 (by rfl) ⟨164579, by rfl⟩ : syracuseStep 219439 = 329159) B329159
theorem B547195 : Blo 215810 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B219675 : Blo 215810 219675 := bstep (se 1 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 219675 = 329513) B329513
theorem B219679 : Blo 215810 219679 := bstep (se 1 (by rfl) ⟨164759, by rfl⟩ : syracuseStep 219679 = 329519) B329519
theorem B6314669 : Blo 215810 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B1235837 : Blo 215810 1235837 := bstep (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) B463439
theorem B1400159 : Blo 215810 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B5693003 : Blo 215810 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B1105487 : Blo 215810 1105487 := bstep (se 1 (by rfl) ⟨829115, by rfl⟩ : syracuseStep 1105487 = 1658231) B1658231
theorem B712439 : Blo 215810 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B614753 : Blo 215810 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B778825 : Blo 215810 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B2482973 : Blo 215810 2482973 := bstep (se 3 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 2482973 = 931115) B931115
theorem B1238003 : Blo 215810 1238003 := bstep (se 1 (by rfl) ⟨928502, by rfl⟩ : syracuseStep 1238003 = 1857005) B1857005
theorem B3957923 : Blo 215810 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1861001 : Blo 215810 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B2778947 : Blo 215810 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B714575 : Blo 215810 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B551225 : Blo 215810 551225 := bstep (se 2 (by rfl) ⟨206709, by rfl⟩ : syracuseStep 551225 = 413419) B413419
theorem B10971449 : Blo 215810 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B1239461 : Blo 215810 1239461 := bstep (se 4 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 1239461 = 232399) B232399
theorem B486521 : Blo 215810 486521 := bstep (se 2 (by rfl) ⟨182445, by rfl⟩ : syracuseStep 486521 = 364891) B364891
theorem B552217 : Blo 215810 552217 := bstep (se 2 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 552217 = 414163) B414163
theorem B4484429 : Blo 215810 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1109537 : Blo 215810 1109537 := bstep (se 2 (by rfl) ⟨416076, by rfl⟩ : syracuseStep 1109537 = 832153) B832153
theorem B552521 : Blo 215810 552521 := bstep (se 2 (by rfl) ⟨207195, by rfl⟩ : syracuseStep 552521 = 414391) B414391
theorem B487187 : Blo 215810 487187 := bstep (se 1 (by rfl) ⟨365390, by rfl⟩ : syracuseStep 487187 = 730781) B730781
theorem B487547 : Blo 215810 487547 := bstep (se 1 (by rfl) ⟨365660, by rfl⟩ : syracuseStep 487547 = 731321) B731321
theorem B487817 : Blo 215810 487817 := bstep (se 2 (by rfl) ⟨182931, by rfl⟩ : syracuseStep 487817 = 365863) B365863
theorem B1667465 : Blo 215810 1667465 := bstep (se 2 (by rfl) ⟨625299, by rfl⟩ : syracuseStep 1667465 = 1250599) B1250599
theorem B324047 : Blo 215810 324047 := bstep (se 1 (by rfl) ⟨243035, by rfl⟩ : syracuseStep 324047 = 486071) B486071
theorem B324089 : Blo 215810 324089 := bstep (se 2 (by rfl) ⟨121533, by rfl⟩ : syracuseStep 324089 = 243067) B243067
theorem B324191 : Blo 215810 324191 := bstep (se 1 (by rfl) ⟨243143, by rfl⟩ : syracuseStep 324191 = 486287) B486287
theorem B619103 : Blo 215810 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B389867 : Blo 215810 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B553979 : Blo 215810 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B619559 : Blo 215810 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B324671 : Blo 215810 324671 := bstep (se 1 (by rfl) ⟨243503, by rfl⟩ : syracuseStep 324671 = 487007) B487007
theorem B324713 : Blo 215810 324713 := bstep (se 2 (by rfl) ⟨121767, by rfl⟩ : syracuseStep 324713 = 243535) B243535
theorem B488555 : Blo 215810 488555 := bstep (se 1 (by rfl) ⟨366416, by rfl⟩ : syracuseStep 488555 = 732833) B732833
theorem B324815 : Blo 215810 324815 := bstep (se 1 (by rfl) ⟨243611, by rfl⟩ : syracuseStep 324815 = 487223) B487223
theorem B325019 : Blo 215810 325019 := bstep (se 1 (by rfl) ⟨243764, by rfl⟩ : syracuseStep 325019 = 487529) B487529
theorem B554465 : Blo 215810 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B325241 : Blo 215810 325241 := bstep (se 2 (by rfl) ⟨121965, by rfl⟩ : syracuseStep 325241 = 243931) B243931
theorem B489131 : Blo 215810 489131 := bstep (se 1 (by rfl) ⟨366848, by rfl⟩ : syracuseStep 489131 = 733697) B733697
theorem B325343 : Blo 215810 325343 := bstep (se 1 (by rfl) ⟨244007, by rfl⟩ : syracuseStep 325343 = 488015) B488015
theorem B5306107 : Blo 215810 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B325439 : Blo 215810 325439 := bstep (se 1 (by rfl) ⟨244079, by rfl⟩ : syracuseStep 325439 = 488159) B488159
theorem B1046429 : Blo 215810 1046429 := bstep (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) B392411
theorem B554971 : Blo 215810 554971 := bstep (se 1 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 554971 = 832457) B832457
theorem B325607 : Blo 215810 325607 := bstep (se 1 (by rfl) ⟨244205, by rfl⟩ : syracuseStep 325607 = 488411) B488411
theorem B522215 : Blo 215810 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B489455 : Blo 215810 489455 := bstep (se 1 (by rfl) ⟨367091, by rfl⟩ : syracuseStep 489455 = 734183) B734183
theorem B325625 : Blo 215810 325625 := bstep (se 2 (by rfl) ⟨122109, by rfl⟩ : syracuseStep 325625 = 244219) B244219
theorem B325727 : Blo 215810 325727 := bstep (se 1 (by rfl) ⟨244295, by rfl⟩ : syracuseStep 325727 = 488591) B488591
theorem B325787 : Blo 215810 325787 := bstep (se 1 (by rfl) ⟨244340, by rfl⟩ : syracuseStep 325787 = 488681) B488681
theorem B325823 : Blo 215810 325823 := bstep (se 1 (by rfl) ⟨244367, by rfl⟩ : syracuseStep 325823 = 488735) B488735
theorem B489671 : Blo 215810 489671 := bstep (se 1 (by rfl) ⟨367253, by rfl⟩ : syracuseStep 489671 = 734507) B734507
theorem B325865 : Blo 215810 325865 := bstep (se 2 (by rfl) ⟨122199, by rfl⟩ : syracuseStep 325865 = 244399) B244399
theorem B391547 : Blo 215810 391547 := bstep (se 1 (by rfl) ⟨293660, by rfl⟩ : syracuseStep 391547 = 587321) B587321
theorem B489851 : Blo 215810 489851 := bstep (se 1 (by rfl) ⟨367388, by rfl⟩ : syracuseStep 489851 = 734777) B734777
theorem B326171 : Blo 215810 326171 := bstep (se 1 (by rfl) ⟨244628, by rfl⟩ : syracuseStep 326171 = 489257) B489257
theorem B326249 : Blo 215810 326249 := bstep (se 2 (by rfl) ⟨122343, by rfl⟩ : syracuseStep 326249 = 244687) B244687
theorem B490121 : Blo 215810 490121 := bstep (se 2 (by rfl) ⟨183795, by rfl⟩ : syracuseStep 490121 = 367591) B367591
theorem B1047239 : Blo 215810 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B1571719 : Blo 215810 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B588703 : Blo 215810 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B3210329 : Blo 215810 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B326777 : Blo 215810 326777 := bstep (se 2 (by rfl) ⟨122541, by rfl⟩ : syracuseStep 326777 = 245083) B245083
theorem B490679 : Blo 215810 490679 := bstep (se 1 (by rfl) ⟨368009, by rfl⟩ : syracuseStep 490679 = 736019) B736019
theorem B326879 : Blo 215810 326879 := bstep (se 1 (by rfl) ⟨245159, by rfl⟩ : syracuseStep 326879 = 490319) B490319
theorem B326921 : Blo 215810 326921 := bstep (se 2 (by rfl) ⟨122595, by rfl⟩ : syracuseStep 326921 = 245191) B245191
theorem B327023 : Blo 215810 327023 := bstep (se 1 (by rfl) ⟨245267, by rfl⟩ : syracuseStep 327023 = 490535) B490535
theorem B327143 : Blo 215810 327143 := bstep (se 1 (by rfl) ⟨245357, by rfl⟩ : syracuseStep 327143 = 490715) B490715
theorem B327275 : Blo 215810 327275 := bstep (se 1 (by rfl) ⟨245456, by rfl⟩ : syracuseStep 327275 = 490913) B490913
theorem B2784941 : Blo 215810 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B327401 : Blo 215810 327401 := bstep (se 2 (by rfl) ⟨122775, by rfl⟩ : syracuseStep 327401 = 245551) B245551
theorem B491255 : Blo 215810 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B327545 : Blo 215810 327545 := bstep (se 2 (by rfl) ⟨122829, by rfl⟩ : syracuseStep 327545 = 245659) B245659
theorem B491435 : Blo 215810 491435 := bstep (se 1 (by rfl) ⟨368576, by rfl⟩ : syracuseStep 491435 = 737153) B737153
theorem B327647 : Blo 215810 327647 := bstep (se 1 (by rfl) ⟨245735, by rfl⟩ : syracuseStep 327647 = 491471) B491471
theorem B819503 : Blo 215810 819503 := bstep (se 1 (by rfl) ⟨614627, by rfl⟩ : syracuseStep 819503 = 1229255) B1229255
theorem B327983 : Blo 215810 327983 := bstep (se 1 (by rfl) ⟨245987, by rfl⟩ : syracuseStep 327983 = 491975) B491975
theorem B1802569 : Blo 215810 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B491903 : Blo 215810 491903 := bstep (se 1 (by rfl) ⟨368927, by rfl⟩ : syracuseStep 491903 = 737855) B737855
theorem B328223 : Blo 215810 328223 := bstep (se 1 (by rfl) ⟨246167, by rfl⟩ : syracuseStep 328223 = 492335) B492335
theorem B819791 : Blo 215810 819791 := bstep (se 1 (by rfl) ⟨614843, by rfl⟩ : syracuseStep 819791 = 1229687) B1229687
theorem B492137 : Blo 215810 492137 := bstep (se 2 (by rfl) ⟨184551, by rfl⟩ : syracuseStep 492137 = 369103) B369103
theorem B328895 : Blo 215810 328895 := bstep (se 1 (by rfl) ⟨246671, by rfl⟩ : syracuseStep 328895 = 493343) B493343
theorem B492767 : Blo 215810 492767 := bstep (se 1 (by rfl) ⟨369575, by rfl⟩ : syracuseStep 492767 = 739151) B739151
theorem B2491721 : Blo 215810 2491721 := bstep (se 2 (by rfl) ⟨934395, by rfl⟩ : syracuseStep 2491721 = 1868791) B1868791
theorem B329039 : Blo 215810 329039 := bstep (se 1 (by rfl) ⟨246779, by rfl⟩ : syracuseStep 329039 = 493559) B493559
theorem B329129 : Blo 215810 329129 := bstep (se 2 (by rfl) ⟨123423, by rfl⟩ : syracuseStep 329129 = 246847) B246847
theorem B492983 : Blo 215810 492983 := bstep (se 1 (by rfl) ⟨369737, by rfl⟩ : syracuseStep 492983 = 739475) B739475
theorem B1246751 : Blo 215810 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B329279 : Blo 215810 329279 := bstep (se 1 (by rfl) ⟨246959, by rfl⟩ : syracuseStep 329279 = 493919) B493919
theorem B329321 : Blo 215810 329321 := bstep (se 2 (by rfl) ⟨123495, by rfl⟩ : syracuseStep 329321 = 246991) B246991
theorem B493163 : Blo 215810 493163 := bstep (se 1 (by rfl) ⟨369872, by rfl⟩ : syracuseStep 493163 = 739745) B739745
theorem B493433 : Blo 215810 493433 := bstep (se 2 (by rfl) ⟨185037, by rfl⟩ : syracuseStep 493433 = 370075) B370075
theorem B10192877 : Blo 215810 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B1443865 : Blo 215810 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B231455 : Blo 215810 231455 := bstep (se 1 (by rfl) ⟨173591, by rfl⟩ : syracuseStep 231455 = 347183) B347183
theorem B526367 : Blo 215810 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B6883379 : Blo 215810 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B3999955 : Blo 215810 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B493865 : Blo 215810 493865 := bstep (se 2 (by rfl) ⟨185199, by rfl⟩ : syracuseStep 493865 = 370399) B370399
theorem B985483 : Blo 215810 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B494441 : Blo 215810 494441 := bstep (se 2 (by rfl) ⟨185415, by rfl⟩ : syracuseStep 494441 = 370831) B370831
theorem B494495 : Blo 215810 494495 := bstep (se 1 (by rfl) ⟨370871, by rfl⟩ : syracuseStep 494495 = 741743) B741743
theorem B1249415 : Blo 215810 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B463337 : Blo 215810 463337 := bstep (se 2 (by rfl) ⟨173751, by rfl⟩ : syracuseStep 463337 = 347503) B347503
theorem B1774153 : Blo 215810 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B823891 : Blo 215810 823891 := bstep (se 1 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 823891 = 1235837) B1235837
theorem B7082599 : Blo 215810 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B7574401 : Blo 215810 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B923035 : Blo 215810 923035 := bstep (se 1 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 923035 = 1384553) B1384553
theorem B1054201 : Blo 215810 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B792143 : Blo 215810 792143 := bstep (se 1 (by rfl) ⟨594107, by rfl⟩ : syracuseStep 792143 = 1188215) B1188215
theorem B825335 : Blo 215810 825335 := bstep (se 1 (by rfl) ⟨619001, by rfl⟩ : syracuseStep 825335 = 1238003) B1238003
theorem B464935 : Blo 215810 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B826109 : Blo 215810 826109 := bstep (se 3 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 826109 = 309791) B309791
theorem B367483 : Blo 215810 367483 := bstep (se 1 (by rfl) ⟨275612, by rfl⟩ : syracuseStep 367483 = 551225) B551225
theorem B7314299 : Blo 215810 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B826307 : Blo 215810 826307 := bstep (se 1 (by rfl) ⟨619730, by rfl⟩ : syracuseStep 826307 = 1239461) B1239461
theorem B2989619 : Blo 215810 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B368347 : Blo 215810 368347 := bstep (se 1 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 368347 = 552521) B552521
theorem B466651 : Blo 215810 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B368617 : Blo 215810 368617 := bstep (se 2 (by rfl) ⟨138231, by rfl⟩ : syracuseStep 368617 = 276463) B276463
theorem B1188047 : Blo 215810 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B794947 : Blo 215810 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B729593 : Blo 215810 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B369319 : Blo 215810 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B729863 : Blo 215810 729863 := bstep (se 1 (by rfl) ⟨547397, by rfl⟩ : syracuseStep 729863 = 1094795) B1094795
theorem B1975195 : Blo 215810 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B369643 : Blo 215810 369643 := bstep (se 1 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 369643 = 554465) B554465
theorem B369785 : Blo 215810 369785 := bstep (se 2 (by rfl) ⟨138669, by rfl⟩ : syracuseStep 369785 = 277339) B277339
theorem B697619 : Blo 215810 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B698159 : Blo 215810 698159 := bstep (se 1 (by rfl) ⟨523619, by rfl⟩ : syracuseStep 698159 = 1047239) B1047239
theorem B730943 : Blo 215810 730943 := bstep (se 1 (by rfl) ⟨548207, by rfl⟩ : syracuseStep 730943 = 1096415) B1096415
theorem B927683 : Blo 215810 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B2140219 : Blo 215810 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B666575 : Blo 215810 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B1092851 : Blo 215810 1092851 := bstep (se 1 (by rfl) ⟨819638, by rfl⟩ : syracuseStep 1092851 = 1639277) B1639277
theorem B732455 : Blo 215810 732455 := bstep (se 1 (by rfl) ⟨549341, by rfl⟩ : syracuseStep 732455 = 1098683) B1098683
theorem B273719 : Blo 215810 273719 := bstep (se 1 (by rfl) ⟨205289, by rfl⟩ : syracuseStep 273719 = 410579) B410579
theorem B700285 : Blo 215810 700285 := bstep (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) B262607
theorem B2338895 : Blo 215810 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B3911759 : Blo 215810 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B307433 : Blo 215810 307433 := bstep (se 2 (by rfl) ⟨115287, by rfl⟩ : syracuseStep 307433 = 230575) B230575
theorem B1650941 : Blo 215810 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B995627 : Blo 215810 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B274843 : Blo 215810 274843 := bstep (se 1 (by rfl) ⟨206132, by rfl⟩ : syracuseStep 274843 = 412265) B412265
theorem B3551687 : Blo 215810 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B1847879 : Blo 215810 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B2077559 : Blo 215810 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B1684435 : Blo 215810 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B6436205 : Blo 215810 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B2078095 : Blo 215810 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B243175 : Blo 215810 243175 := bstep (se 1 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 243175 = 364763) B364763
theorem B243355 : Blo 215810 243355 := bstep (se 1 (by rfl) ⟨182516, by rfl⟩ : syracuseStep 243355 = 365033) B365033
theorem B735101 : Blo 215810 735101 := bstep (se 3 (by rfl) ⟨137831, by rfl⟩ : syracuseStep 735101 = 275663) B275663
theorem B931799 : Blo 215810 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B2668585 : Blo 215810 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B735371 : Blo 215810 735371 := bstep (se 1 (by rfl) ⟨551528, by rfl⟩ : syracuseStep 735371 = 1103057) B1103057
theorem B702695 : Blo 215810 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B1095929 : Blo 215810 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B833915 : Blo 215810 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B670441 : Blo 215810 670441 := bstep (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) B502831
theorem B703399 : Blo 215810 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B736289 : Blo 215810 736289 := bstep (se 2 (by rfl) ⟨276108, by rfl⟩ : syracuseStep 736289 = 552217) B552217
theorem B4209779 : Blo 215810 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B933439 : Blo 215810 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B736991 : Blo 215810 736991 := bstep (se 1 (by rfl) ⟨552743, by rfl⟩ : syracuseStep 736991 = 1105487) B1105487
theorem B245479 : Blo 215810 245479 := bstep (se 1 (by rfl) ⟨184109, by rfl⟩ : syracuseStep 245479 = 368219) B368219
theorem B474959 : Blo 215810 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B409835 : Blo 215810 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B737693 : Blo 215810 737693 := bstep (se 3 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 737693 = 276635) B276635
theorem B1655315 : Blo 215810 1655315 := bstep (se 1 (by rfl) ⟨1241486, by rfl⟩ : syracuseStep 1655315 = 2482973) B2482973
theorem B2638615 : Blo 215810 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B246559 : Blo 215810 246559 := bstep (se 1 (by rfl) ⟨184919, by rfl⟩ : syracuseStep 246559 = 369839) B369839
theorem B1852631 : Blo 215810 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B476383 : Blo 215810 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B1230187 : Blo 215810 1230187 := bstep (se 1 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 1230187 = 1845281) B1845281
theorem B739691 : Blo 215810 739691 := bstep (se 1 (by rfl) ⟨554768, by rfl⟩ : syracuseStep 739691 = 1109537) B1109537
theorem B739961 : Blo 215810 739961 := bstep (se 2 (by rfl) ⟨277485, by rfl⟩ : syracuseStep 739961 = 554971) B554971
theorem B216031 : Blo 215810 216031 := bstep (se 1 (by rfl) ⟨162023, by rfl⟩ : syracuseStep 216031 = 324047) B324047
theorem B216059 : Blo 215810 216059 := bstep (se 1 (by rfl) ⟨162044, by rfl⟩ : syracuseStep 216059 = 324089) B324089
theorem B216127 : Blo 215810 216127 := bstep (se 1 (by rfl) ⟨162095, by rfl⟩ : syracuseStep 216127 = 324191) B324191
theorem B413039 : Blo 215810 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B216447 : Blo 215810 216447 := bstep (se 1 (by rfl) ⟨162335, by rfl⟩ : syracuseStep 216447 = 324671) B324671
theorem B216475 : Blo 215810 216475 := bstep (se 1 (by rfl) ⟨162356, by rfl⟩ : syracuseStep 216475 = 324713) B324713
theorem B216543 : Blo 215810 216543 := bstep (se 1 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 216543 = 324815) B324815
theorem B216679 : Blo 215810 216679 := bstep (se 1 (by rfl) ⟨162509, by rfl⟩ : syracuseStep 216679 = 325019) B325019
theorem B216827 : Blo 215810 216827 := bstep (se 1 (by rfl) ⟨162620, by rfl⟩ : syracuseStep 216827 = 325241) B325241
theorem B216895 : Blo 215810 216895 := bstep (se 1 (by rfl) ⟨162671, by rfl⟩ : syracuseStep 216895 = 325343) B325343
theorem B216959 : Blo 215810 216959 := bstep (se 1 (by rfl) ⟨162719, by rfl⟩ : syracuseStep 216959 = 325439) B325439
theorem B11980781 : Blo 215810 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B217071 : Blo 215810 217071 := bstep (se 1 (by rfl) ⟨162803, by rfl⟩ : syracuseStep 217071 = 325607) B325607
theorem B348143 : Blo 215810 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B217083 : Blo 215810 217083 := bstep (se 1 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 217083 = 325625) B325625
theorem B217151 : Blo 215810 217151 := bstep (se 1 (by rfl) ⟨162863, by rfl⟩ : syracuseStep 217151 = 325727) B325727
theorem B217191 : Blo 215810 217191 := bstep (se 1 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 217191 = 325787) B325787
theorem B217215 : Blo 215810 217215 := bstep (se 1 (by rfl) ⟨162911, by rfl⟩ : syracuseStep 217215 = 325823) B325823
theorem B217243 : Blo 215810 217243 := bstep (se 1 (by rfl) ⟨162932, by rfl⟩ : syracuseStep 217243 = 325865) B325865
theorem B217447 : Blo 215810 217447 := bstep (se 1 (by rfl) ⟨163085, by rfl⟩ : syracuseStep 217447 = 326171) B326171
theorem B217499 : Blo 215810 217499 := bstep (se 1 (by rfl) ⟨163124, by rfl⟩ : syracuseStep 217499 = 326249) B326249
theorem B1233629 : Blo 215810 1233629 := bstep (se 3 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 1233629 = 462611) B462611
theorem B217851 : Blo 215810 217851 := bstep (se 1 (by rfl) ⟨163388, by rfl⟩ : syracuseStep 217851 = 326777) B326777
theorem B217919 : Blo 215810 217919 := bstep (se 1 (by rfl) ⟨163439, by rfl⟩ : syracuseStep 217919 = 326879) B326879
theorem B217947 : Blo 215810 217947 := bstep (se 1 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 217947 = 326921) B326921
theorem B218015 : Blo 215810 218015 := bstep (se 1 (by rfl) ⟨163511, by rfl⟩ : syracuseStep 218015 = 327023) B327023
theorem B1496045 : Blo 215810 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B218095 : Blo 215810 218095 := bstep (se 1 (by rfl) ⟨163571, by rfl⟩ : syracuseStep 218095 = 327143) B327143
theorem B218183 : Blo 215810 218183 := bstep (se 1 (by rfl) ⟨163637, by rfl⟩ : syracuseStep 218183 = 327275) B327275
theorem B1856627 : Blo 215810 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B218267 : Blo 215810 218267 := bstep (se 1 (by rfl) ⟨163700, by rfl⟩ : syracuseStep 218267 = 327401) B327401
theorem B218363 : Blo 215810 218363 := bstep (se 1 (by rfl) ⟨163772, by rfl⟩ : syracuseStep 218363 = 327545) B327545
theorem B218431 : Blo 215810 218431 := bstep (se 1 (by rfl) ⟨163823, by rfl⟩ : syracuseStep 218431 = 327647) B327647
theorem B218599 : Blo 215810 218599 := bstep (se 1 (by rfl) ⟨163949, by rfl⟩ : syracuseStep 218599 = 327899) B327899
theorem B218607 : Blo 215810 218607 := bstep (se 1 (by rfl) ⟨163955, by rfl⟩ : syracuseStep 218607 = 327911) B327911
theorem B218715 : Blo 215810 218715 := bstep (se 1 (by rfl) ⟨164036, by rfl⟩ : syracuseStep 218715 = 328073) B328073
theorem B218779 : Blo 215810 218779 := bstep (se 1 (by rfl) ⟨164084, by rfl⟩ : syracuseStep 218779 = 328169) B328169
theorem B218863 : Blo 215810 218863 := bstep (se 1 (by rfl) ⟨164147, by rfl⟩ : syracuseStep 218863 = 328295) B328295
theorem B218951 : Blo 215810 218951 := bstep (se 1 (by rfl) ⟨164213, by rfl⟩ : syracuseStep 218951 = 328427) B328427
theorem B218971 : Blo 215810 218971 := bstep (se 1 (by rfl) ⟨164228, by rfl⟩ : syracuseStep 218971 = 328457) B328457
theorem B219039 : Blo 215810 219039 := bstep (se 1 (by rfl) ⟨164279, by rfl⟩ : syracuseStep 219039 = 328559) B328559
theorem B219207 : Blo 215810 219207 := bstep (se 1 (by rfl) ⟨164405, by rfl⟩ : syracuseStep 219207 = 328811) B328811
theorem B1038433 : Blo 215810 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B219367 : Blo 215810 219367 := bstep (se 1 (by rfl) ⟨164525, by rfl⟩ : syracuseStep 219367 = 329051) B329051
theorem B3561803 : Blo 215810 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B416083 : Blo 215810 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B3955067 : Blo 215810 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B219551 : Blo 215810 219551 := bstep (se 1 (by rfl) ⟨164663, by rfl⟩ : syracuseStep 219551 = 329327) B329327
theorem B219599 : Blo 215810 219599 := bstep (se 1 (by rfl) ⟨164699, by rfl⟩ : syracuseStep 219599 = 329399) B329399
theorem B219623 : Blo 215810 219623 := bstep (se 1 (by rfl) ⟨164717, by rfl⟩ : syracuseStep 219623 = 329435) B329435
theorem B1399315 : Blo 215810 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B219739 : Blo 215810 219739 := bstep (se 1 (by rfl) ⟨164804, by rfl⟩ : syracuseStep 219739 = 329609) B329609
theorem B219807 : Blo 215810 219807 := bstep (se 1 (by rfl) ⟨164855, by rfl⟩ : syracuseStep 219807 = 329711) B329711
theorem B1039645 : Blo 215810 1039645 := bstep (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) B389867
theorem B2481515 : Blo 215810 2481515 := bstep (se 1 (by rfl) ⟨1861136, by rfl⟩ : syracuseStep 2481515 = 3722273) B3722273
theorem B548329 : Blo 215810 548329 := bstep (se 2 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 548329 = 411247) B411247
theorem B843385 : Blo 215810 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B2121383 : Blo 215810 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B351911 : Blo 215810 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B2776943 : Blo 215810 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B2088827 : Blo 215810 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B549119 : Blo 215810 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B1040663 : Blo 215810 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B549281 : Blo 215810 549281 := bstep (se 2 (by rfl) ⟨205980, by rfl⟩ : syracuseStep 549281 = 411961) B411961
theorem B1761697 : Blo 215810 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B3007003 : Blo 215810 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B1106459 : Blo 215810 1106459 := bstep (se 1 (by rfl) ⟨829844, by rfl⟩ : syracuseStep 1106459 = 1659689) B1659689
theorem B3007853 : Blo 215810 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B13297097 : Blo 215810 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B616187 : Blo 215810 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B1861379 : Blo 215810 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B616211 : Blo 215810 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B485639 : Blo 215810 485639 := bstep (se 1 (by rfl) ⟨364229, by rfl⟩ : syracuseStep 485639 = 728459) B728459
theorem B3795335 : Blo 215810 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B485945 : Blo 215810 485945 := bstep (se 2 (by rfl) ⟨182229, by rfl⟩ : syracuseStep 485945 = 364459) B364459
theorem B4222003 : Blo 215810 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B486665 : Blo 215810 486665 := bstep (se 2 (by rfl) ⟨182499, by rfl⟩ : syracuseStep 486665 = 364999) B364999
theorem B552359 : Blo 215810 552359 := bstep (se 1 (by rfl) ⟨414269, by rfl⟩ : syracuseStep 552359 = 828539) B828539
theorem B1666493 : Blo 215810 1666493 := bstep (se 3 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 1666493 = 624935) B624935
theorem B1240667 : Blo 215810 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B487655 : Blo 215810 487655 := bstep (se 1 (by rfl) ⟨365741, by rfl⟩ : syracuseStep 487655 = 731483) B731483
theorem B487835 : Blo 215810 487835 := bstep (se 1 (by rfl) ⟨365876, by rfl⟩ : syracuseStep 487835 = 731753) B731753
theorem B881111 : Blo 215810 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B324347 : Blo 215810 324347 := bstep (se 1 (by rfl) ⟨243260, by rfl⟩ : syracuseStep 324347 = 486521) B486521
theorem B2388797 : Blo 215810 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B7074809 : Blo 215810 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B488519 : Blo 215810 488519 := bstep (se 1 (by rfl) ⟨366389, by rfl⟩ : syracuseStep 488519 = 732779) B732779
theorem B324791 : Blo 215810 324791 := bstep (se 1 (by rfl) ⟨243593, by rfl⟩ : syracuseStep 324791 = 487187) B487187
theorem B488699 : Blo 215810 488699 := bstep (se 1 (by rfl) ⟨366524, by rfl⟩ : syracuseStep 488699 = 733049) B733049
theorem B554303 : Blo 215810 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B325031 : Blo 215810 325031 := bstep (se 1 (by rfl) ⟨243773, by rfl⟩ : syracuseStep 325031 = 487547) B487547
theorem B488915 : Blo 215810 488915 := bstep (se 1 (by rfl) ⟨366686, by rfl⟩ : syracuseStep 488915 = 733373) B733373
theorem B325211 : Blo 215810 325211 := bstep (se 1 (by rfl) ⟨243908, by rfl⟩ : syracuseStep 325211 = 487817) B487817
theorem B1111643 : Blo 215810 1111643 := bstep (se 1 (by rfl) ⟨833732, by rfl⟩ : syracuseStep 1111643 = 1667465) B1667465
theorem B489185 : Blo 215810 489185 := bstep (se 2 (by rfl) ⟨183444, by rfl⟩ : syracuseStep 489185 = 366889) B366889
theorem B554951 : Blo 215810 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B325673 : Blo 215810 325673 := bstep (se 2 (by rfl) ⟨122127, by rfl⟩ : syracuseStep 325673 = 244255) B244255
theorem B325703 : Blo 215810 325703 := bstep (se 1 (by rfl) ⟨244277, by rfl⟩ : syracuseStep 325703 = 488555) B488555
theorem B489707 : Blo 215810 489707 := bstep (se 1 (by rfl) ⟨367280, by rfl⟩ : syracuseStep 489707 = 734561) B734561
theorem B326087 : Blo 215810 326087 := bstep (se 1 (by rfl) ⟨244565, by rfl⟩ : syracuseStep 326087 = 489131) B489131
theorem B2095625 : Blo 215810 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B784937 : Blo 215810 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B326303 : Blo 215810 326303 := bstep (se 1 (by rfl) ⟨244727, by rfl⟩ : syracuseStep 326303 = 489455) B489455
theorem B326447 : Blo 215810 326447 := bstep (se 1 (by rfl) ⟨244835, by rfl⟩ : syracuseStep 326447 = 489671) B489671
theorem B261031 : Blo 215810 261031 := bstep (se 1 (by rfl) ⟨195773, by rfl⟩ : syracuseStep 261031 = 391547) B391547
theorem B326567 : Blo 215810 326567 := bstep (se 1 (by rfl) ⟨244925, by rfl⟩ : syracuseStep 326567 = 489851) B489851
theorem B326747 : Blo 215810 326747 := bstep (se 1 (by rfl) ⟨245060, by rfl⟩ : syracuseStep 326747 = 490121) B490121
theorem B327119 : Blo 215810 327119 := bstep (se 1 (by rfl) ⟨245339, by rfl⟩ : syracuseStep 327119 = 490679) B490679
theorem B491003 : Blo 215810 491003 := bstep (se 1 (by rfl) ⟨368252, by rfl⟩ : syracuseStep 491003 = 736505) B736505
theorem B491183 : Blo 215810 491183 := bstep (se 1 (by rfl) ⟨368387, by rfl⟩ : syracuseStep 491183 = 736775) B736775
theorem B884467 : Blo 215810 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B491273 : Blo 215810 491273 := bstep (se 2 (by rfl) ⟨184227, by rfl⟩ : syracuseStep 491273 = 368455) B368455
theorem B2391851 : Blo 215810 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B327503 : Blo 215810 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B327623 : Blo 215810 327623 := bstep (se 1 (by rfl) ⟨245717, by rfl⟩ : syracuseStep 327623 = 491435) B491435
theorem B327935 : Blo 215810 327935 := bstep (se 1 (by rfl) ⟨245951, by rfl⟩ : syracuseStep 327935 = 491903) B491903
theorem B491795 : Blo 215810 491795 := bstep (se 1 (by rfl) ⟨368846, by rfl⟩ : syracuseStep 491795 = 737693) B737693
theorem B328091 : Blo 215810 328091 := bstep (se 1 (by rfl) ⟨246068, by rfl⟩ : syracuseStep 328091 = 492137) B492137
theorem B819821 : Blo 215810 819821 := bstep (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) B307433
theorem B328511 : Blo 215810 328511 := bstep (se 1 (by rfl) ⟨246383, by rfl⟩ : syracuseStep 328511 = 492767) B492767
theorem B492425 : Blo 215810 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B328655 : Blo 215810 328655 := bstep (se 1 (by rfl) ⟨246491, by rfl⟩ : syracuseStep 328655 = 492983) B492983
theorem B328745 : Blo 215810 328745 := bstep (se 2 (by rfl) ⟨123279, by rfl⟩ : syracuseStep 328745 = 246559) B246559
theorem B328775 : Blo 215810 328775 := bstep (se 1 (by rfl) ⟨246581, by rfl⟩ : syracuseStep 328775 = 493163) B493163
theorem B328955 : Blo 215810 328955 := bstep (se 1 (by rfl) ⟨246716, by rfl⟩ : syracuseStep 328955 = 493433) B493433
theorem B492857 : Blo 215810 492857 := bstep (se 2 (by rfl) ⟨184821, by rfl⟩ : syracuseStep 492857 = 369643) B369643
theorem B4588919 : Blo 215810 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B329243 : Blo 215810 329243 := bstep (se 1 (by rfl) ⟨246932, by rfl⟩ : syracuseStep 329243 = 493865) B493865
theorem B493127 : Blo 215810 493127 := bstep (se 1 (by rfl) ⟨369845, by rfl⟩ : syracuseStep 493127 = 739691) B739691
theorem B493307 : Blo 215810 493307 := bstep (se 1 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 493307 = 739961) B739961
theorem B1640249 : Blo 215810 1640249 := bstep (se 2 (by rfl) ⟨615093, by rfl⟩ : syracuseStep 1640249 = 1230187) B1230187
theorem B329627 : Blo 215810 329627 := bstep (se 1 (by rfl) ⟨247220, by rfl⟩ : syracuseStep 329627 = 494441) B494441
theorem B329663 : Blo 215810 329663 := bstep (se 1 (by rfl) ⟨247247, by rfl⟩ : syracuseStep 329663 = 494495) B494495
theorem B2853625 : Blo 215810 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B822419 : Blo 215810 822419 := bstep (se 1 (by rfl) ⟨616814, by rfl⟩ : syracuseStep 822419 = 1233629) B1233629
theorem B1313977 : Blo 215810 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B528095 : Blo 215810 528095 := bstep (se 1 (by rfl) ⟨396071, by rfl⟩ : syracuseStep 528095 = 792143) B792143
theorem B1643165 : Blo 215810 1643165 := bstep (se 3 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 1643165 = 616187) B616187
theorem B1414255 : Blo 215810 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B792031 : Blo 215810 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B366079 : Blo 215810 366079 := bstep (se 1 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 366079 = 549119) B549119
theorem B693775 : Blo 215810 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B366187 : Blo 215810 366187 := bstep (se 1 (by rfl) ⟨274640, by rfl⟩ : syracuseStep 366187 = 549281) B549281
theorem B366457 : Blo 215810 366457 := bstep (se 2 (by rfl) ⟨137421, by rfl⟩ : syracuseStep 366457 = 274843) B274843
theorem B2365537 : Blo 215810 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B9443465 : Blo 215810 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B2005235 : Blo 215810 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B10099201 : Blo 215810 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B465439 : Blo 215810 465439 := bstep (se 1 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 465439 = 698159) B698159
theorem B2530223 : Blo 215810 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B728567 : Blo 215810 728567 := bstep (se 1 (by rfl) ⟨546425, by rfl⟩ : syracuseStep 728567 = 1092851) B1092851
theorem B368239 : Blo 215810 368239 := bstep (se 1 (by rfl) ⟨276179, by rfl⟩ : syracuseStep 368239 = 552359) B552359
theorem B827111 : Blo 215810 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B1384577 : Blo 215810 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B663751 : Blo 215810 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B2367791 : Blo 215810 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B1385039 : Blo 215810 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B729917 : Blo 215810 729917 := bstep (se 3 (by rfl) ⟨136859, by rfl⟩ : syracuseStep 729917 = 273719) B273719
theorem B369535 : Blo 215810 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B893921 : Blo 215810 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B369967 : Blo 215810 369967 := bstep (se 1 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 369967 = 554951) B554951
theorem B468463 : Blo 215810 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B730619 : Blo 215810 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B1386193 : Blo 215810 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B731105 : Blo 215810 731105 := bstep (se 2 (by rfl) ⟨274164, by rfl⟩ : syracuseStep 731105 = 548329) B548329
theorem B1124513 : Blo 215810 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B3713525 : Blo 215810 3713525 := bstep (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) B348143
theorem B273223 : Blo 215810 273223 := bstep (se 1 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 273223 = 409835) B409835
theorem B1059929 : Blo 215810 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B2403425 : Blo 215810 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B4009337 : Blo 215810 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B831167 : Blo 215810 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B3518153 : Blo 215810 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B2633593 : Blo 215810 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B6795251 : Blo 215810 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B635177 : Blo 215810 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B832943 : Blo 215810 832943 := bstep (se 1 (by rfl) ⟨624707, by rfl⟩ : syracuseStep 832943 = 1249415) B1249415
theorem B308891 : Blo 215810 308891 := bstep (se 1 (by rfl) ⟨231668, by rfl⟩ : syracuseStep 308891 = 463337) B463337
theorem B997363 : Blo 215810 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B2374535 : Blo 215810 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B2636711 : Blo 215810 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B1654343 : Blo 215810 1654343 := bstep (se 1 (by rfl) ⟨1240757, by rfl⟩ : syracuseStep 1654343 = 2481515) B2481515
theorem B933713 : Blo 215810 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B1851295 : Blo 215810 1851295 := bstep (se 1 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 1851295 = 2776943) B2776943
theorem B1392551 : Blo 215810 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B737639 : Blo 215810 737639 := bstep (se 1 (by rfl) ⟨553229, by rfl⟩ : syracuseStep 737639 = 1106459) B1106459
theorem B246523 : Blo 215810 246523 := bstep (se 1 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 246523 = 369785) B369785
theorem B1098521 : Blo 215810 1098521 := bstep (se 2 (by rfl) ⟨411945, by rfl⟩ : syracuseStep 1098521 = 823891) B823891
theorem B8864731 : Blo 215810 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B410807 : Blo 215810 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B2245913 : Blo 215810 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B2770793 : Blo 215810 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B1230713 : Blo 215810 1230713 := bstep (se 2 (by rfl) ⟨461517, by rfl⟩ : syracuseStep 1230713 = 923035) B923035
theorem B444383 : Blo 215810 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B1559263 : Blo 215810 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B2607839 : Blo 215810 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B3558113 : Blo 215810 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B1100627 : Blo 215810 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B11226077 : Blo 215810 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B1231919 : Blo 215810 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B216231 : Blo 215810 216231 := bstep (se 1 (by rfl) ⟨162173, by rfl⟩ : syracuseStep 216231 = 324347) B324347
theorem B1592531 : Blo 215810 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B216527 : Blo 215810 216527 := bstep (se 1 (by rfl) ⟨162395, by rfl⟩ : syracuseStep 216527 = 324791) B324791
theorem B216687 : Blo 215810 216687 := bstep (se 1 (by rfl) ⟨162515, by rfl⟩ : syracuseStep 216687 = 325031) B325031
theorem B1101437 : Blo 215810 1101437 := bstep (se 3 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 1101437 = 413039) B413039
theorem B216807 : Blo 215810 216807 := bstep (se 1 (by rfl) ⟨162605, by rfl⟩ : syracuseStep 216807 = 325211) B325211
theorem B741095 : Blo 215810 741095 := bstep (se 1 (by rfl) ⟨555821, by rfl⟩ : syracuseStep 741095 = 1111643) B1111643
theorem B937865 : Blo 215810 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B348041 : Blo 215810 348041 := bstep (se 2 (by rfl) ⟨130515, by rfl⟩ : syracuseStep 348041 = 261031) B261031
theorem B217115 : Blo 215810 217115 := bstep (se 1 (by rfl) ⟨162836, by rfl⟩ : syracuseStep 217115 = 325673) B325673
theorem B217135 : Blo 215810 217135 := bstep (se 1 (by rfl) ⟨162851, by rfl⟩ : syracuseStep 217135 = 325703) B325703
theorem B217391 : Blo 215810 217391 := bstep (se 1 (by rfl) ⟨163043, by rfl⟩ : syracuseStep 217391 = 326087) B326087
theorem B1397083 : Blo 215810 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B938429 : Blo 215810 938429 := bstep (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) B351911
theorem B217535 : Blo 215810 217535 := bstep (se 1 (by rfl) ⟨163151, by rfl⟩ : syracuseStep 217535 = 326303) B326303
theorem B217631 : Blo 215810 217631 := bstep (se 1 (by rfl) ⟨163223, by rfl⟩ : syracuseStep 217631 = 326447) B326447
theorem B217711 : Blo 215810 217711 := bstep (se 1 (by rfl) ⟨163283, by rfl⟩ : syracuseStep 217711 = 326567) B326567
theorem B217831 : Blo 215810 217831 := bstep (se 1 (by rfl) ⟨163373, by rfl⟩ : syracuseStep 217831 = 326747) B326747
theorem B218079 : Blo 215810 218079 := bstep (se 1 (by rfl) ⟨163559, by rfl⟩ : syracuseStep 218079 = 327119) B327119
theorem B1594567 : Blo 215810 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B218335 : Blo 215810 218335 := bstep (se 1 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 218335 = 327503) B327503
theorem B316639 : Blo 215810 316639 := bstep (se 1 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 316639 = 474959) B474959
theorem B218415 : Blo 215810 218415 := bstep (se 1 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 218415 = 327623) B327623
theorem B546335 : Blo 215810 546335 := bstep (se 1 (by rfl) ⟨409751, by rfl⟩ : syracuseStep 546335 = 819503) B819503
theorem B218655 : Blo 215810 218655 := bstep (se 1 (by rfl) ⟨163991, by rfl⟩ : syracuseStep 218655 = 327983) B327983
theorem B1103543 : Blo 215810 1103543 := bstep (se 1 (by rfl) ⟨827657, by rfl⟩ : syracuseStep 1103543 = 1655315) B1655315
theorem B218815 : Blo 215810 218815 := bstep (se 1 (by rfl) ⟨164111, by rfl⟩ : syracuseStep 218815 = 328223) B328223
theorem B546527 : Blo 215810 546527 := bstep (se 1 (by rfl) ⟨409895, by rfl⟩ : syracuseStep 546527 = 819791) B819791
theorem B2348929 : Blo 215810 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B219263 : Blo 215810 219263 := bstep (se 1 (by rfl) ⟨164447, by rfl⟩ : syracuseStep 219263 = 328895) B328895
theorem B1235087 : Blo 215810 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B1661147 : Blo 215810 1661147 := bstep (se 1 (by rfl) ⟨1245860, by rfl⟩ : syracuseStep 1661147 = 2491721) B2491721
theorem B219359 : Blo 215810 219359 := bstep (se 1 (by rfl) ⟨164519, by rfl⟩ : syracuseStep 219359 = 329039) B329039
theorem B219419 : Blo 215810 219419 := bstep (se 1 (by rfl) ⟨164564, by rfl⟩ : syracuseStep 219419 = 329129) B329129
theorem B219519 : Blo 215810 219519 := bstep (se 1 (by rfl) ⟨164639, by rfl⟩ : syracuseStep 219519 = 329279) B329279
theorem B219547 : Blo 215810 219547 := bstep (se 1 (by rfl) ⟨164660, by rfl⟩ : syracuseStep 219547 = 329321) B329321
theorem B350911 : Blo 215810 350911 := bstep (se 1 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 350911 = 526367) B526367
theorem B7987187 : Blo 215810 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B1925153 : Blo 215810 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B5333273 : Blo 215810 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B1860317 : Blo 215810 1860317 := bstep (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) B697619
theorem B1237751 : Blo 215810 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B550223 : Blo 215810 550223 := bstep (se 1 (by rfl) ⟨412667, by rfl⟩ : syracuseStep 550223 = 825335) B825335
theorem B5629337 : Blo 215810 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B550739 : Blo 215810 550739 := bstep (se 1 (by rfl) ⟨413054, by rfl⟩ : syracuseStep 550739 = 826109) B826109
theorem B4876199 : Blo 215810 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B550871 : Blo 215810 550871 := bstep (se 1 (by rfl) ⟨413153, by rfl⟩ : syracuseStep 550871 = 826307) B826307
theorem B1993079 : Blo 215810 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B617213 : Blo 215810 617213 := bstep (se 3 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 617213 = 231455) B231455
theorem B486395 : Blo 215810 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B486575 : Blo 215810 486575 := bstep (se 1 (by rfl) ⟨364931, by rfl⟩ : syracuseStep 486575 = 729863) B729863
theorem B1240919 : Blo 215810 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B487295 : Blo 215810 487295 := bstep (se 1 (by rfl) ⟨365471, by rfl⟩ : syracuseStep 487295 = 730943) B730943
theorem B618455 : Blo 215810 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B2093165 : Blo 215810 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B323759 : Blo 215810 323759 := bstep (se 1 (by rfl) ⟨242819, by rfl⟩ : syracuseStep 323759 = 485639) B485639
theorem B323963 : Blo 215810 323963 := bstep (se 1 (by rfl) ⟨242972, by rfl⟩ : syracuseStep 323963 = 485945) B485945
theorem B324233 : Blo 215810 324233 := bstep (se 2 (by rfl) ⟨121587, by rfl⟩ : syracuseStep 324233 = 243175) B243175
theorem B1405601 : Blo 215810 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B324443 : Blo 215810 324443 := bstep (se 1 (by rfl) ⟨243332, by rfl⟩ : syracuseStep 324443 = 486665) B486665
theorem B488303 : Blo 215810 488303 := bstep (se 1 (by rfl) ⟨366227, by rfl⟩ : syracuseStep 488303 = 732455) B732455
theorem B324473 : Blo 215810 324473 := bstep (se 2 (by rfl) ⟨121677, by rfl⟩ : syracuseStep 324473 = 243355) B243355
theorem B1110995 : Blo 215810 1110995 := bstep (se 1 (by rfl) ⟨833246, by rfl⟩ : syracuseStep 1110995 = 1666493) B1666493
theorem B619913 : Blo 215810 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B325103 : Blo 215810 325103 := bstep (se 1 (by rfl) ⟨243827, by rfl⟩ : syracuseStep 325103 = 487655) B487655
theorem B325223 : Blo 215810 325223 := bstep (se 1 (by rfl) ⟨243917, by rfl⟩ : syracuseStep 325223 = 487835) B487835
theorem B587407 : Blo 215810 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B554777 : Blo 215810 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B4716539 : Blo 215810 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B1865753 : Blo 215810 1865753 := bstep (se 2 (by rfl) ⟨699657, by rfl⟩ : syracuseStep 1865753 = 1399315) B1399315
theorem B325679 : Blo 215810 325679 := bstep (se 1 (by rfl) ⟨244259, by rfl⟩ : syracuseStep 325679 = 488519) B488519
theorem B325799 : Blo 215810 325799 := bstep (se 1 (by rfl) ⟨244349, by rfl⟩ : syracuseStep 325799 = 488699) B488699
theorem B4290803 : Blo 215810 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B325943 : Blo 215810 325943 := bstep (se 1 (by rfl) ⟨244457, by rfl⟩ : syracuseStep 325943 = 488915) B488915
theorem B2488805 : Blo 215810 2488805 := bstep (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) B466651
theorem B326123 : Blo 215810 326123 := bstep (se 1 (by rfl) ⟨244592, by rfl⟩ : syracuseStep 326123 = 489185) B489185
theorem B489977 : Blo 215810 489977 := bstep (se 2 (by rfl) ⟨183741, by rfl⟩ : syracuseStep 489977 = 367483) B367483
theorem B490067 : Blo 215810 490067 := bstep (se 1 (by rfl) ⟨367550, by rfl⟩ : syracuseStep 490067 = 735101) B735101
theorem B621199 : Blo 215810 621199 := bstep (se 1 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 621199 = 931799) B931799
theorem B490247 : Blo 215810 490247 := bstep (se 1 (by rfl) ⟨367685, by rfl⟩ : syracuseStep 490247 = 735371) B735371
theorem B326471 : Blo 215810 326471 := bstep (se 1 (by rfl) ⟨244853, by rfl⟩ : syracuseStep 326471 = 489707) B489707
theorem B555943 : Blo 215810 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B490859 : Blo 215810 490859 := bstep (se 1 (by rfl) ⟨368144, by rfl⟩ : syracuseStep 490859 = 736289) B736289
theorem B1244585 : Blo 215810 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B491129 : Blo 215810 491129 := bstep (se 2 (by rfl) ⟨184173, by rfl⟩ : syracuseStep 491129 = 368347) B368347
theorem B327305 : Blo 215810 327305 := bstep (se 2 (by rfl) ⟨122739, by rfl⟩ : syracuseStep 327305 = 245479) B245479
theorem B1179289 : Blo 215810 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B327335 : Blo 215810 327335 := bstep (se 1 (by rfl) ⟨245501, by rfl⟩ : syracuseStep 327335 = 491003) B491003
theorem B327455 : Blo 215810 327455 := bstep (se 1 (by rfl) ⟨245591, by rfl⟩ : syracuseStep 327455 = 491183) B491183
theorem B491327 : Blo 215810 491327 := bstep (se 1 (by rfl) ⟨368495, by rfl⟩ : syracuseStep 491327 = 736991) B736991
theorem B327515 : Blo 215810 327515 := bstep (se 1 (by rfl) ⟨245636, by rfl⟩ : syracuseStep 327515 = 491273) B491273
theorem B491489 : Blo 215810 491489 := bstep (se 2 (by rfl) ⟨184308, by rfl⟩ : syracuseStep 491489 = 368617) B368617
theorem B327863 : Blo 215810 327863 := bstep (se 1 (by rfl) ⟨245897, by rfl⟩ : syracuseStep 327863 = 491795) B491795
theorem B491759 : Blo 215810 491759 := bstep (se 1 (by rfl) ⟨368819, by rfl⟩ : syracuseStep 491759 = 737639) B737639
theorem B885001 : Blo 215810 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B328283 : Blo 215810 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B328571 : Blo 215810 328571 := bstep (se 1 (by rfl) ⟨246428, by rfl⟩ : syracuseStep 328571 = 492857) B492857
theorem B328697 : Blo 215810 328697 := bstep (se 2 (by rfl) ⟨123261, by rfl⟩ : syracuseStep 328697 = 246523) B246523
theorem B328751 : Blo 215810 328751 := bstep (se 1 (by rfl) ⟨246563, by rfl⟩ : syracuseStep 328751 = 493127) B493127
theorem B328871 : Blo 215810 328871 := bstep (se 1 (by rfl) ⟨246653, by rfl⟩ : syracuseStep 328871 = 493307) B493307
theorem B492713 : Blo 215810 492713 := bstep (se 2 (by rfl) ⟨184767, by rfl⟩ : syracuseStep 492713 = 369535) B369535
theorem B820475 : Blo 215810 820475 := bstep (se 1 (by rfl) ⟨615356, by rfl⟩ : syracuseStep 820475 = 1230713) B1230713
theorem B296255 : Blo 215810 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B493289 : Blo 215810 493289 := bstep (se 2 (by rfl) ⟨184983, by rfl⟩ : syracuseStep 493289 = 369967) B369967
theorem B1738559 : Blo 215810 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B624617 : Blo 215810 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B821279 : Blo 215810 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B494063 : Blo 215810 494063 := bstep (se 1 (by rfl) ⟨370547, by rfl⟩ : syracuseStep 494063 = 741095) B741095
theorem B625243 : Blo 215810 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B232027 : Blo 215810 232027 := bstep (se 1 (by rfl) ⟨174020, by rfl⟩ : syracuseStep 232027 = 348041) B348041
theorem B625619 : Blo 215810 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B3804833 : Blo 215810 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B1871525 : Blo 215810 1871525 := bstep (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) B350911
theorem B364223 : Blo 215810 364223 := bstep (se 1 (by rfl) ⟨273167, by rfl⟩ : syracuseStep 364223 = 546335) B546335
theorem B364297 : Blo 215810 364297 := bstep (se 2 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 364297 = 273223) B273223
theorem B364351 : Blo 215810 364351 := bstep (se 1 (by rfl) ⟨273263, by rfl⟩ : syracuseStep 364351 = 546527) B546527
theorem B6295643 : Blo 215810 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B823391 : Blo 215810 823391 := bstep (se 1 (by rfl) ⟨617543, by rfl⟩ : syracuseStep 823391 = 1235087) B1235087
theorem B823709 : Blo 215810 823709 := bstep (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) B308891
theorem B3511457 : Blo 215810 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B1283435 : Blo 215810 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B923051 : Blo 215810 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B1578527 : Blo 215810 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B923359 : Blo 215810 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B825167 : Blo 215810 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B366815 : Blo 215810 366815 := bstep (se 1 (by rfl) ⟨275111, by rfl⟩ : syracuseStep 366815 = 550223) B550223
theorem B367159 : Blo 215810 367159 := bstep (se 1 (by rfl) ⟨275369, by rfl⟩ : syracuseStep 367159 = 550739) B550739
theorem B3250799 : Blo 215810 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B367247 : Blo 215810 367247 := bstep (se 1 (by rfl) ⟨275435, by rfl⟩ : syracuseStep 367247 = 550871) B550871
theorem B1056041 : Blo 215810 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B925033 : Blo 215810 925033 := bstep (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) B693775
theorem B827279 : Blo 215810 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B4530167 : Blo 215810 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B3154049 : Blo 215810 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B828265 : Blo 215810 828265 := bstep (se 2 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 828265 = 621199) B621199
theorem B369851 : Blo 215810 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B2860535 : Blo 215810 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B1583023 : Blo 215810 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B829723 : Blo 215810 829723 := bstep (se 1 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 829723 = 1244585) B1244585
theorem B2468393 : Blo 215810 2468393 := bstep (se 2 (by rfl) ⟨925647, by rfl⟩ : syracuseStep 2468393 = 1851295) B1851295
theorem B928367 : Blo 215810 928367 := bstep (se 1 (by rfl) ⟨696275, by rfl⟩ : syracuseStep 928367 = 1392551) B1392551
theorem B732347 : Blo 215810 732347 := bstep (se 1 (by rfl) ⟨549260, by rfl⟩ : syracuseStep 732347 = 1098521) B1098521
theorem B273871 : Blo 215810 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B3059279 : Blo 215810 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B1093499 : Blo 215810 1093499 := bstep (se 1 (by rfl) ⟨820124, by rfl⟩ : syracuseStep 1093499 = 1640249) B1640249
theorem B1847195 : Blo 215810 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B2372075 : Blo 215810 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B733751 : Blo 215810 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B7484051 : Blo 215810 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B1061687 : Blo 215810 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B1848257 : Blo 215810 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B734291 : Blo 215810 734291 := bstep (se 1 (by rfl) ⟨550718, by rfl⟩ : syracuseStep 734291 = 1101437) B1101437
theorem B1095443 : Blo 215810 1095443 := bstep (se 1 (by rfl) ⟨821582, by rfl⟩ : syracuseStep 1095443 = 1643165) B1643165
theorem B2079017 : Blo 215810 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B735695 : Blo 215810 735695 := bstep (se 1 (by rfl) ⟨551771, by rfl⟩ : syracuseStep 735695 = 1103543) B1103543
theorem B1751969 : Blo 215810 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1686815 : Blo 215810 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B5324791 : Blo 215810 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B3555515 : Blo 215810 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B3752891 : Blo 215810 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B1688741 : Blo 215810 1688741 := bstep (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) B316639
theorem B1885673 : Blo 215810 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B1328719 : Blo 215810 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B2475683 : Blo 215810 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B411475 : Blo 215810 411475 := bstep (se 1 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 411475 = 617213) B617213
theorem B706619 : Blo 215810 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B2672891 : Blo 215810 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B2345435 : Blo 215810 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B3131905 : Blo 215810 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B412303 : Blo 215810 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B1329817 : Blo 215810 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B1395443 : Blo 215810 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B215839 : Blo 215810 215839 := bstep (se 1 (by rfl) ⟨161879, by rfl⟩ : syracuseStep 215839 = 323759) B323759
theorem B215975 : Blo 215810 215975 := bstep (se 1 (by rfl) ⟨161981, by rfl⟩ : syracuseStep 215975 = 323963) B323963
theorem B216155 : Blo 215810 216155 := bstep (se 1 (by rfl) ⟨162116, by rfl⟩ : syracuseStep 216155 = 324233) B324233
theorem B937067 : Blo 215810 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B216295 : Blo 215810 216295 := bstep (se 1 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 216295 = 324443) B324443
theorem B216315 : Blo 215810 216315 := bstep (se 1 (by rfl) ⟨162236, by rfl⟩ : syracuseStep 216315 = 324473) B324473
theorem B740663 : Blo 215810 740663 := bstep (se 1 (by rfl) ⟨555497, by rfl⟩ : syracuseStep 740663 = 1110995) B1110995
theorem B413275 : Blo 215810 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B216735 : Blo 215810 216735 := bstep (se 1 (by rfl) ⟨162551, by rfl⟩ : syracuseStep 216735 = 325103) B325103
theorem B216815 : Blo 215810 216815 := bstep (se 1 (by rfl) ⟨162611, by rfl⟩ : syracuseStep 216815 = 325223) B325223
theorem B741257 : Blo 215810 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B217119 : Blo 215810 217119 := bstep (se 1 (by rfl) ⟨162839, by rfl⟩ : syracuseStep 217119 = 325679) B325679
theorem B217199 : Blo 215810 217199 := bstep (se 1 (by rfl) ⟨162899, by rfl⟩ : syracuseStep 217199 = 325799) B325799
theorem B217295 : Blo 215810 217295 := bstep (se 1 (by rfl) ⟨162971, by rfl⟩ : syracuseStep 217295 = 325943) B325943
theorem B1659203 : Blo 215810 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B217415 : Blo 215810 217415 := bstep (se 1 (by rfl) ⟨163061, by rfl⟩ : syracuseStep 217415 = 326123) B326123
theorem B217647 : Blo 215810 217647 := bstep (se 1 (by rfl) ⟨163235, by rfl⟩ : syracuseStep 217647 = 326471) B326471
theorem B1757807 : Blo 215810 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B1102895 : Blo 215810 1102895 := bstep (se 1 (by rfl) ⟨827171, by rfl⟩ : syracuseStep 1102895 = 1654343) B1654343
theorem B218203 : Blo 215810 218203 := bstep (se 1 (by rfl) ⟨163652, by rfl⟩ : syracuseStep 218203 = 327305) B327305
theorem B218223 : Blo 215810 218223 := bstep (se 1 (by rfl) ⟨163667, by rfl⟩ : syracuseStep 218223 = 327335) B327335
theorem B218303 : Blo 215810 218303 := bstep (se 1 (by rfl) ⟨163727, by rfl⟩ : syracuseStep 218303 = 327455) B327455
theorem B218343 : Blo 215810 218343 := bstep (se 1 (by rfl) ⟨163757, by rfl⟩ : syracuseStep 218343 = 327515) B327515
theorem B218623 : Blo 215810 218623 := bstep (se 1 (by rfl) ⟨163967, by rfl⟩ : syracuseStep 218623 = 327935) B327935
theorem B218727 : Blo 215810 218727 := bstep (se 1 (by rfl) ⟨164045, by rfl⟩ : syracuseStep 218727 = 328091) B328091
theorem B546547 : Blo 215810 546547 := bstep (se 1 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 546547 = 819821) B819821
theorem B219007 : Blo 215810 219007 := bstep (se 1 (by rfl) ⟨164255, by rfl⟩ : syracuseStep 219007 = 328511) B328511
theorem B219103 : Blo 215810 219103 := bstep (se 1 (by rfl) ⟨164327, by rfl⟩ : syracuseStep 219103 = 328655) B328655
theorem B219163 : Blo 215810 219163 := bstep (se 1 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 219163 = 328745) B328745
theorem B219183 : Blo 215810 219183 := bstep (se 1 (by rfl) ⟨164387, by rfl⟩ : syracuseStep 219183 = 328775) B328775
theorem B219303 : Blo 215810 219303 := bstep (se 1 (by rfl) ⟨164477, by rfl⟩ : syracuseStep 219303 = 328955) B328955
theorem B1497275 : Blo 215810 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B219495 : Blo 215810 219495 := bstep (se 1 (by rfl) ⟨164621, by rfl⟩ : syracuseStep 219495 = 329243) B329243
theorem B219751 : Blo 215810 219751 := bstep (se 1 (by rfl) ⟨164813, by rfl⟩ : syracuseStep 219751 = 329627) B329627
theorem B11819641 : Blo 215810 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B219775 : Blo 215810 219775 := bstep (se 1 (by rfl) ⟨164831, by rfl⟩ : syracuseStep 219775 = 329663) B329663
theorem B548279 : Blo 215810 548279 := bstep (se 1 (by rfl) ⟨411209, by rfl⟩ : syracuseStep 548279 = 822419) B822419
theorem B352063 : Blo 215810 352063 := bstep (se 1 (by rfl) ⟨264047, by rfl⟩ : syracuseStep 352063 = 528095) B528095
theorem B2383789 : Blo 215810 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B1107431 : Blo 215810 1107431 := bstep (se 1 (by rfl) ⟨830573, by rfl⟩ : syracuseStep 1107431 = 1661147) B1661147
theorem B1336823 : Blo 215810 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B485711 : Blo 215810 485711 := bstep (se 1 (by rfl) ⟨364283, by rfl⟩ : syracuseStep 485711 = 728567) B728567
theorem B551407 : Blo 215810 551407 := bstep (se 1 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 551407 = 827111) B827111
theorem B1862777 : Blo 215810 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B1240211 : Blo 215810 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B486611 : Blo 215810 486611 := bstep (se 1 (by rfl) ⟨364958, by rfl⟩ : syracuseStep 486611 = 729917) B729917
theorem B487079 : Blo 215810 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B487403 : Blo 215810 487403 := bstep (se 1 (by rfl) ⟨365552, by rfl⟩ : syracuseStep 487403 = 731105) B731105
theorem B749675 : Blo 215810 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B2126089 : Blo 215810 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B324263 : Blo 215810 324263 := bstep (se 1 (by rfl) ⟨243197, by rfl⟩ : syracuseStep 324263 = 486395) B486395
theorem B488105 : Blo 215810 488105 := bstep (se 2 (by rfl) ⟨183039, by rfl⟩ : syracuseStep 488105 = 366079) B366079
theorem B1602283 : Blo 215810 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B324383 : Blo 215810 324383 := bstep (se 1 (by rfl) ⟨243287, by rfl⟩ : syracuseStep 324383 = 486575) B486575
theorem B488249 : Blo 215810 488249 := bstep (se 2 (by rfl) ⟨183093, by rfl⟩ : syracuseStep 488249 = 366187) B366187
theorem B783209 : Blo 215810 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B554111 : Blo 215810 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B488609 : Blo 215810 488609 := bstep (se 2 (by rfl) ⟨183228, by rfl⟩ : syracuseStep 488609 = 366457) B366457
theorem B324863 : Blo 215810 324863 := bstep (se 1 (by rfl) ⟨243647, by rfl⟩ : syracuseStep 324863 = 487295) B487295
theorem B423451 : Blo 215810 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B325535 : Blo 215810 325535 := bstep (se 1 (by rfl) ⟨244151, by rfl⟩ : syracuseStep 325535 = 488303) B488303
theorem B13465601 : Blo 215810 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B620585 : Blo 215810 620585 := bstep (se 2 (by rfl) ⟨232719, by rfl⟩ : syracuseStep 620585 = 465439) B465439
theorem B555295 : Blo 215810 555295 := bstep (se 1 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 555295 = 832943) B832943
theorem B3144359 : Blo 215810 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B1243835 : Blo 215810 1243835 := bstep (se 1 (by rfl) ⟨932876, by rfl⟩ : syracuseStep 1243835 = 1865753) B1865753
theorem B326651 : Blo 215810 326651 := bstep (se 1 (by rfl) ⟨244988, by rfl⟩ : syracuseStep 326651 = 489977) B489977
theorem B326711 : Blo 215810 326711 := bstep (se 1 (by rfl) ⟨245033, by rfl⟩ : syracuseStep 326711 = 490067) B490067
theorem B326831 : Blo 215810 326831 := bstep (se 1 (by rfl) ⟨245123, by rfl⟩ : syracuseStep 326831 = 490247) B490247
theorem B490985 : Blo 215810 490985 := bstep (se 2 (by rfl) ⟨184119, by rfl⟩ : syracuseStep 490985 = 368239) B368239
theorem B1572385 : Blo 215810 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B327239 : Blo 215810 327239 := bstep (se 1 (by rfl) ⟨245429, by rfl⟩ : syracuseStep 327239 = 490859) B490859
theorem B327419 : Blo 215810 327419 := bstep (se 1 (by rfl) ⟨245564, by rfl⟩ : syracuseStep 327419 = 491129) B491129
theorem B327551 : Blo 215810 327551 := bstep (se 1 (by rfl) ⟨245663, by rfl⟩ : syracuseStep 327551 = 491327) B491327
theorem B622475 : Blo 215810 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B327659 : Blo 215810 327659 := bstep (se 1 (by rfl) ⟨245744, by rfl⟩ : syracuseStep 327659 = 491489) B491489
theorem B327839 : Blo 215810 327839 := bstep (se 1 (by rfl) ⟨245879, by rfl⟩ : syracuseStep 327839 = 491759) B491759
theorem B1999133 : Blo 215810 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B1180001 : Blo 215810 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B328475 : Blo 215810 328475 := bstep (se 1 (by rfl) ⟨246356, by rfl⟩ : syracuseStep 328475 = 492713) B492713
theorem B328859 : Blo 215810 328859 := bstep (se 1 (by rfl) ⟨246644, by rfl⟩ : syracuseStep 328859 = 493289) B493289
theorem B329375 : Blo 215810 329375 := bstep (se 1 (by rfl) ⟨247031, by rfl⟩ : syracuseStep 329375 = 494063) B494063
theorem B1771625 : Blo 215810 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B493775 : Blo 215810 493775 := bstep (se 1 (by rfl) ⟨370331, by rfl⟩ : syracuseStep 493775 = 740663) B740663
theorem B1247683 : Blo 215810 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B494171 : Blo 215810 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B4197095 : Blo 215810 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B986269 : Blo 215810 986269 := bstep (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) B369851
theorem B790013 : Blo 215810 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B1773089 : Blo 215810 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B855623 : Blo 215810 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B1052351 : Blo 215810 1052351 := bstep (se 1 (by rfl) ⟨789263, by rfl⟩ : syracuseStep 1052351 = 1578527) B1578527
theorem B2167199 : Blo 215810 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B365161 : Blo 215810 365161 := bstep (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) B273871
theorem B365519 : Blo 215810 365519 := bstep (se 1 (by rfl) ⟨274139, by rfl⟩ : syracuseStep 365519 = 548279) B548279
theorem B3020111 : Blo 215810 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B2102699 : Blo 215810 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B2136377 : Blo 215810 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B1907023 : Blo 215810 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B891215 : Blo 215810 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B1645595 : Blo 215810 1645595 := bstep (se 1 (by rfl) ⟨1234196, by rfl⟩ : syracuseStep 1645595 = 2468393) B2468393
theorem B826807 : Blo 215810 826807 := bstep (se 1 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 826807 = 1240211) B1240211
theorem B728729 : Blo 215810 728729 := bstep (se 2 (by rfl) ⟨273273, by rfl⟩ : syracuseStep 728729 = 546547) B546547
theorem B2039519 : Blo 215810 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B728999 : Blo 215810 728999 := bstep (se 1 (by rfl) ⟨546749, by rfl⟩ : syracuseStep 728999 = 1093499) B1093499
theorem B2498845 : Blo 215810 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B1581383 : Blo 215810 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B4989367 : Blo 215810 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B369407 : Blo 215810 369407 := bstep (se 1 (by rfl) ⟨277055, by rfl⟩ : syracuseStep 369407 = 554111) B554111
theorem B730295 : Blo 215810 730295 := bstep (se 1 (by rfl) ⟨547721, by rfl⟩ : syracuseStep 730295 = 1095443) B1095443
theorem B1386011 : Blo 215810 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B829223 : Blo 215810 829223 := bstep (se 1 (by rfl) ⟨621917, by rfl⟩ : syracuseStep 829223 = 1243835) B1243835
theorem B1124543 : Blo 215810 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B469417 : Blo 215810 469417 := bstep (se 2 (by rfl) ⟨176031, by rfl⟩ : syracuseStep 469417 = 352063) B352063
theorem B2370343 : Blo 215810 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B2501927 : Blo 215810 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B1125827 : Blo 215810 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B1257115 : Blo 215810 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B1650455 : Blo 215810 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B1159039 : Blo 215810 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B471079 : Blo 215810 471079 := bstep (se 1 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 471079 = 706619) B706619
theorem B1781927 : Blo 215810 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B930295 : Blo 215810 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B2536555 : Blo 215810 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B242815 : Blo 215810 242815 := bstep (se 1 (by rfl) ⟨182111, by rfl⟩ : syracuseStep 242815 = 364223) B364223
theorem B2110697 : Blo 215810 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B735209 : Blo 215810 735209 := bstep (se 2 (by rfl) ⟨275703, by rfl⟩ : syracuseStep 735209 = 551407) B551407
theorem B4175873 : Blo 215810 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B735263 : Blo 215810 735263 := bstep (se 1 (by rfl) ⟨551447, by rfl⟩ : syracuseStep 735263 = 1102895) B1102895
theorem B2340971 : Blo 215810 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B833657 : Blo 215810 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B998183 : Blo 215810 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B244543 : Blo 215810 244543 := bstep (se 1 (by rfl) ⟨183407, by rfl⟩ : syracuseStep 244543 = 366815) B366815
theorem B244831 : Blo 215810 244831 := bstep (se 1 (by rfl) ⟨183623, by rfl⟩ : syracuseStep 244831 = 367247) B367247
theorem B704027 : Blo 215810 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B2834785 : Blo 215810 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B738287 : Blo 215810 738287 := bstep (se 1 (by rfl) ⟨553715, by rfl⟩ : syracuseStep 738287 = 1107431) B1107431
theorem B1231145 : Blo 215810 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B1231463 : Blo 215810 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B740393 : Blo 215810 740393 := bstep (se 2 (by rfl) ⟨277647, by rfl⟩ : syracuseStep 740393 = 555295) B555295
theorem B216175 : Blo 215810 216175 := bstep (se 1 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 216175 = 324263) B324263
theorem B216255 : Blo 215810 216255 := bstep (se 1 (by rfl) ⟨162191, by rfl⟩ : syracuseStep 216255 = 324383) B324383
theorem B707791 : Blo 215810 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B1232171 : Blo 215810 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B216575 : Blo 215810 216575 := bstep (se 1 (by rfl) ⟨162431, by rfl⟩ : syracuseStep 216575 = 324863) B324863
theorem B217023 : Blo 215810 217023 := bstep (se 1 (by rfl) ⟨162767, by rfl⟩ : syracuseStep 217023 = 325535) B325535
theorem B413723 : Blo 215810 413723 := bstep (se 1 (by rfl) ⟨310292, by rfl⟩ : syracuseStep 413723 = 620585) B620585
theorem B1233377 : Blo 215810 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B1167979 : Blo 215810 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B217767 : Blo 215810 217767 := bstep (se 1 (by rfl) ⟨163325, by rfl⟩ : syracuseStep 217767 = 326651) B326651
theorem B217807 : Blo 215810 217807 := bstep (se 1 (by rfl) ⟨163355, by rfl⟩ : syracuseStep 217807 = 326711) B326711
theorem B217887 : Blo 215810 217887 := bstep (se 1 (by rfl) ⟨163415, by rfl⟩ : syracuseStep 217887 = 326831) B326831
theorem B218159 : Blo 215810 218159 := bstep (se 1 (by rfl) ⟨163619, by rfl⟩ : syracuseStep 218159 = 327239) B327239
theorem B218279 : Blo 215810 218279 := bstep (se 1 (by rfl) ⟨163709, by rfl⟩ : syracuseStep 218279 = 327419) B327419
theorem B218367 : Blo 215810 218367 := bstep (se 1 (by rfl) ⟨163775, by rfl⟩ : syracuseStep 218367 = 327551) B327551
theorem B414983 : Blo 215810 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B218439 : Blo 215810 218439 := bstep (se 1 (by rfl) ⟨163829, by rfl⟩ : syracuseStep 218439 = 327659) B327659
theorem B7099721 : Blo 215810 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B218575 : Blo 215810 218575 := bstep (se 1 (by rfl) ⟨163931, by rfl⟩ : syracuseStep 218575 = 327863) B327863
theorem B218855 : Blo 215810 218855 := bstep (se 1 (by rfl) ⟨164141, by rfl⟩ : syracuseStep 218855 = 328283) B328283
theorem B219047 : Blo 215810 219047 := bstep (se 1 (by rfl) ⟨164285, by rfl⟩ : syracuseStep 219047 = 328571) B328571
theorem B219131 : Blo 215810 219131 := bstep (se 1 (by rfl) ⟨164348, by rfl⟩ : syracuseStep 219131 = 328697) B328697
theorem B219167 : Blo 215810 219167 := bstep (se 1 (by rfl) ⟨164375, by rfl⟩ : syracuseStep 219167 = 328751) B328751
theorem B219247 : Blo 215810 219247 := bstep (se 1 (by rfl) ⟨164435, by rfl⟩ : syracuseStep 219247 = 328871) B328871
theorem B546983 : Blo 215810 546983 := bstep (se 1 (by rfl) ⟨410237, by rfl⟩ : syracuseStep 546983 = 820475) B820475
theorem B1104353 : Blo 215810 1104353 := bstep (se 2 (by rfl) ⟨414132, by rfl⟩ : syracuseStep 1104353 = 828265) B828265
theorem B416411 : Blo 215810 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B547519 : Blo 215810 547519 := bstep (se 1 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 547519 = 821279) B821279
theorem B1563623 : Blo 215810 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B417079 : Blo 215810 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B548633 : Blo 215810 548633 := bstep (se 2 (by rfl) ⟨205737, by rfl⟩ : syracuseStep 548633 = 411475) B411475
theorem B548927 : Blo 215810 548927 := bstep (se 1 (by rfl) ⟨411695, by rfl⟩ : syracuseStep 548927 = 823391) B823391
theorem B1106135 : Blo 215810 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B549139 : Blo 215810 549139 := bstep (se 1 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 549139 = 823709) B823709
theorem B1106297 : Blo 215810 1106297 := bstep (se 2 (by rfl) ⟨414861, by rfl⟩ : syracuseStep 1106297 = 829723) B829723
theorem B1171871 : Blo 215810 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B1237477 : Blo 215810 1237477 := bstep (se 4 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 1237477 = 232027) B232027
theorem B549737 : Blo 215810 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B615367 : Blo 215810 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B550111 : Blo 215810 550111 := bstep (se 1 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 550111 = 825167) B825167
theorem B551033 : Blo 215810 551033 := bstep (se 2 (by rfl) ⟨206637, by rfl⟩ : syracuseStep 551033 = 413275) B413275
theorem B485729 : Blo 215810 485729 := bstep (se 2 (by rfl) ⟨182148, by rfl⟩ : syracuseStep 485729 = 364297) B364297
theorem B485801 : Blo 215810 485801 := bstep (se 2 (by rfl) ⟨182175, by rfl⟩ : syracuseStep 485801 = 364351) B364351
theorem B551519 : Blo 215810 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B323807 : Blo 215810 323807 := bstep (se 1 (by rfl) ⟨242855, by rfl⟩ : syracuseStep 323807 = 485711) B485711
theorem B618911 : Blo 215810 618911 := bstep (se 1 (by rfl) ⟨464183, by rfl⟩ : syracuseStep 618911 = 928367) B928367
theorem B8384957 : Blo 215810 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B1241851 : Blo 215810 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B488231 : Blo 215810 488231 := bstep (se 1 (by rfl) ⟨366173, by rfl⟩ : syracuseStep 488231 = 732347) B732347
theorem B324407 : Blo 215810 324407 := bstep (se 1 (by rfl) ⟨243305, by rfl⟩ : syracuseStep 324407 = 486611) B486611
theorem B324719 : Blo 215810 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B324935 : Blo 215810 324935 := bstep (se 1 (by rfl) ⟨243701, by rfl⟩ : syracuseStep 324935 = 487403) B487403
theorem B2258405 : Blo 215810 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B489167 : Blo 215810 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B325403 : Blo 215810 325403 := bstep (se 1 (by rfl) ⟨244052, by rfl⟩ : syracuseStep 325403 = 488105) B488105
theorem B325499 : Blo 215810 325499 := bstep (se 1 (by rfl) ⟨244124, by rfl⟩ : syracuseStep 325499 = 488249) B488249
theorem B522139 : Blo 215810 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B489527 : Blo 215810 489527 := bstep (se 1 (by rfl) ⟨367145, by rfl⟩ : syracuseStep 489527 = 734291) B734291
theorem B489545 : Blo 215810 489545 := bstep (se 2 (by rfl) ⟨183579, by rfl⟩ : syracuseStep 489545 = 367159) B367159
theorem B325739 : Blo 215810 325739 := bstep (se 1 (by rfl) ⟨244304, by rfl⟩ : syracuseStep 325739 = 488609) B488609
theorem B15759521 : Blo 215810 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B8977067 : Blo 215810 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B490463 : Blo 215810 490463 := bstep (se 1 (by rfl) ⟨367847, by rfl⟩ : syracuseStep 490463 = 735695) B735695
theorem B2096513 : Blo 215810 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B327323 : Blo 215810 327323 := bstep (se 1 (by rfl) ⟨245492, by rfl⟩ : syracuseStep 327323 = 490985) B490985
theorem B3178385 : Blo 215810 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B786667 : Blo 215810 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B6652489 : Blo 215810 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B492191 : Blo 215810 492191 := bstep (se 1 (by rfl) ⟨369143, by rfl⟩ : syracuseStep 492191 = 738287) B738287
theorem B820489 : Blo 215810 820489 := bstep (se 2 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 820489 = 615367) B615367
theorem B1181083 : Blo 215810 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B329183 : Blo 215810 329183 := bstep (se 1 (by rfl) ⟨246887, by rfl⟩ : syracuseStep 329183 = 493775) B493775
theorem B820763 : Blo 215810 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B329447 : Blo 215810 329447 := bstep (se 1 (by rfl) ⟨247085, by rfl⟩ : syracuseStep 329447 = 494171) B494171
theorem B820975 : Blo 215810 820975 := bstep (se 1 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 820975 = 1231463) B1231463
theorem B493595 : Blo 215810 493595 := bstep (se 1 (by rfl) ⟨370196, by rfl⟩ : syracuseStep 493595 = 740393) B740393
theorem B821447 : Blo 215810 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B526675 : Blo 215810 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B1182059 : Blo 215810 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B1444799 : Blo 215810 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B822251 : Blo 215810 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B625889 : Blo 215810 625889 := bstep (se 2 (by rfl) ⟨234708, by rfl⟩ : syracuseStep 625889 = 469417) B469417
theorem B364655 : Blo 215810 364655 := bstep (se 1 (by rfl) ⟨273491, by rfl⟩ : syracuseStep 364655 = 546983) B546983
theorem B1315025 : Blo 215810 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B594143 : Blo 215810 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B1676153 : Blo 215810 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B365755 : Blo 215810 365755 := bstep (se 1 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 365755 = 548633) B548633
theorem B365951 : Blo 215810 365951 := bstep (se 1 (by rfl) ⟨274463, by rfl⟩ : syracuseStep 365951 = 548927) B548927
theorem B628105 : Blo 215810 628105 := bstep (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) B471079
theorem B1054255 : Blo 215810 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B366491 : Blo 215810 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B367355 : Blo 215810 367355 := bstep (se 1 (by rfl) ⟨275516, by rfl⟩ : syracuseStep 367355 = 551033) B551033
theorem B3382073 : Blo 215810 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B367679 : Blo 215810 367679 := bstep (se 1 (by rfl) ⟨275759, by rfl⟩ : syracuseStep 367679 = 551519) B551519
theorem B2661821 : Blo 215810 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B696185 : Blo 215810 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B1187951 : Blo 215810 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B730025 : Blo 215810 730025 := bstep (se 2 (by rfl) ⟨273759, by rfl⟩ : syracuseStep 730025 = 547519) B547519
theorem B469351 : Blo 215810 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B732185 : Blo 215810 732185 := bstep (se 2 (by rfl) ⟨274569, by rfl⟩ : syracuseStep 732185 = 549139) B549139
theorem B3779713 : Blo 215810 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B1649969 : Blo 215810 1649969 := bstep (se 2 (by rfl) ⟨618738, by rfl⟩ : syracuseStep 1649969 = 1237477) B1237477
theorem B8892341 : Blo 215810 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B733481 : Blo 215810 733481 := bstep (se 2 (by rfl) ⟨275055, by rfl⟩ : syracuseStep 733481 = 550111) B550111
theorem B2798063 : Blo 215810 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B570415 : Blo 215810 570415 := bstep (se 1 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 570415 = 855623) B855623
theorem B701567 : Blo 215810 701567 := bstep (se 1 (by rfl) ⟨526175, by rfl⟩ : syracuseStep 701567 = 1052351) B1052351
theorem B275815 : Blo 215810 275815 := bstep (se 1 (by rfl) ⟨206861, by rfl⟩ : syracuseStep 275815 = 413723) B413723
theorem B243679 : Blo 215810 243679 := bstep (se 1 (by rfl) ⟨182759, by rfl⟩ : syracuseStep 243679 = 365519) B365519
theorem B4733147 : Blo 215810 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B2013407 : Blo 215810 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B3160457 : Blo 215810 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B1424251 : Blo 215810 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B736235 : Blo 215810 736235 := bstep (se 1 (by rfl) ⟨552176, by rfl⟩ : syracuseStep 736235 = 1104353) B1104353
theorem B277607 : Blo 215810 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B1097063 : Blo 215810 1097063 := bstep (se 1 (by rfl) ⟨822797, by rfl⟩ : syracuseStep 1097063 = 1645595) B1645595
theorem B1359679 : Blo 215810 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B737423 : Blo 215810 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B737531 : Blo 215810 737531 := bstep (se 1 (by rfl) ⟨553148, by rfl⟩ : syracuseStep 737531 = 1106297) B1106297
theorem B2998781 : Blo 215810 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B246271 : Blo 215810 246271 := bstep (se 1 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 246271 = 369407) B369407
theorem B1557305 : Blo 215810 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1655801 : Blo 215810 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B1100303 : Blo 215810 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B215871 : Blo 215810 215871 := bstep (se 1 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 215871 = 323807) B323807
theorem B412607 : Blo 215810 412607 := bstep (se 1 (by rfl) ⟨309455, by rfl⟩ : syracuseStep 412607 = 618911) B618911
theorem B5589971 : Blo 215810 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B2542697 : Blo 215810 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B216271 : Blo 215810 216271 := bstep (se 1 (by rfl) ⟨162203, by rfl⟩ : syracuseStep 216271 = 324407) B324407
theorem B216479 : Blo 215810 216479 := bstep (se 1 (by rfl) ⟨162359, by rfl⟩ : syracuseStep 216479 = 324719) B324719
theorem B216623 : Blo 215810 216623 := bstep (se 1 (by rfl) ⟨162467, by rfl⟩ : syracuseStep 216623 = 324935) B324935
theorem B216935 : Blo 215810 216935 := bstep (se 1 (by rfl) ⟨162701, by rfl⟩ : syracuseStep 216935 = 325403) B325403
theorem B216999 : Blo 215810 216999 := bstep (se 1 (by rfl) ⟨162749, by rfl⟩ : syracuseStep 216999 = 325499) B325499
theorem B1560647 : Blo 215810 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B217159 : Blo 215810 217159 := bstep (se 1 (by rfl) ⟨162869, by rfl⟩ : syracuseStep 217159 = 325739) B325739
theorem B10506347 : Blo 215810 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B5984711 : Blo 215810 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B1102409 : Blo 215810 1102409 := bstep (se 2 (by rfl) ⟨413403, by rfl⟩ : syracuseStep 1102409 = 826807) B826807
theorem B6181541 : Blo 215810 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B1397675 : Blo 215810 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B218215 : Blo 215810 218215 := bstep (se 1 (by rfl) ⟨163661, by rfl⟩ : syracuseStep 218215 = 327323) B327323
theorem B2118923 : Blo 215810 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B218559 : Blo 215810 218559 := bstep (se 1 (by rfl) ⟨163919, by rfl⟩ : syracuseStep 218559 = 327839) B327839
theorem B1332755 : Blo 215810 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B3331793 : Blo 215810 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B218983 : Blo 215810 218983 := bstep (se 1 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 218983 = 328475) B328475
theorem B219239 : Blo 215810 219239 := bstep (se 1 (by rfl) ⟨164429, by rfl⟩ : syracuseStep 219239 = 328859) B328859
theorem B219583 : Blo 215810 219583 := bstep (se 1 (by rfl) ⟨164687, by rfl⟩ : syracuseStep 219583 = 329375) B329375
theorem B1663577 : Blo 215810 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B1106621 : Blo 215810 1106621 := bstep (se 3 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 1106621 = 414983) B414983
theorem B1401799 : Blo 215810 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B3696029 : Blo 215810 3696029 := bstep (se 3 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 3696029 = 1386011) B1386011
theorem B943721 : Blo 215810 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B1042415 : Blo 215810 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B485819 : Blo 215810 485819 := bstep (se 1 (by rfl) ⟨364364, by rfl⟩ : syracuseStep 485819 = 728729) B728729
theorem B485999 : Blo 215810 485999 := bstep (se 1 (by rfl) ⟨364499, by rfl⟩ : syracuseStep 485999 = 728999) B728999
theorem B781247 : Blo 215810 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B1240393 : Blo 215810 1240393 := bstep (se 2 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 1240393 = 930295) B930295
theorem B486863 : Blo 215810 486863 := bstep (se 1 (by rfl) ⟨365147, by rfl⟩ : syracuseStep 486863 = 730295) B730295
theorem B486881 : Blo 215810 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B552815 : Blo 215810 552815 := bstep (se 1 (by rfl) ⟨414611, by rfl⟩ : syracuseStep 552815 = 829223) B829223
theorem B323753 : Blo 215810 323753 := bstep (se 2 (by rfl) ⟨121407, by rfl⟩ : syracuseStep 323753 = 242815) B242815
theorem B323819 : Blo 215810 323819 := bstep (se 1 (by rfl) ⟨242864, by rfl⟩ : syracuseStep 323819 = 485729) B485729
theorem B323867 : Blo 215810 323867 := bstep (se 1 (by rfl) ⟨242900, by rfl⟩ : syracuseStep 323867 = 485801) B485801
theorem B1667951 : Blo 215810 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B750551 : Blo 215810 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B325487 : Blo 215810 325487 := bstep (se 1 (by rfl) ⟨244115, by rfl⟩ : syracuseStep 325487 = 488231) B488231
theorem B1407131 : Blo 215810 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B1505603 : Blo 215810 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B326057 : Blo 215810 326057 := bstep (se 2 (by rfl) ⟨122271, by rfl⟩ : syracuseStep 326057 = 244543) B244543
theorem B326111 : Blo 215810 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B490139 : Blo 215810 490139 := bstep (se 1 (by rfl) ⟨367604, by rfl⟩ : syracuseStep 490139 = 735209) B735209
theorem B2783915 : Blo 215810 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B490175 : Blo 215810 490175 := bstep (se 1 (by rfl) ⟨367631, by rfl⟩ : syracuseStep 490175 = 735263) B735263
theorem B326351 : Blo 215810 326351 := bstep (se 1 (by rfl) ⟨244763, by rfl⟩ : syracuseStep 326351 = 489527) B489527
theorem B326363 : Blo 215810 326363 := bstep (se 1 (by rfl) ⟨244772, by rfl⟩ : syracuseStep 326363 = 489545) B489545
theorem B326441 : Blo 215810 326441 := bstep (se 2 (by rfl) ⟨122415, by rfl⟩ : syracuseStep 326441 = 244831) B244831
theorem B556105 : Blo 215810 556105 := bstep (se 2 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 556105 = 417079) B417079
theorem B326975 : Blo 215810 326975 := bstep (se 1 (by rfl) ⟨245231, by rfl⟩ : syracuseStep 326975 = 490463) B490463
theorem B491615 : Blo 215810 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B491687 : Blo 215810 491687 := bstep (se 1 (by rfl) ⟨368765, by rfl⟩ : syracuseStep 491687 = 737531) B737531
theorem B4161725 : Blo 215810 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B1048889 : Blo 215810 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B1999187 : Blo 215810 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B328127 : Blo 215810 328127 := bstep (se 1 (by rfl) ⟨246095, by rfl⟩ : syracuseStep 328127 = 492191) B492191
theorem B328361 : Blo 215810 328361 := bstep (se 2 (by rfl) ⟨123135, by rfl⟩ : syracuseStep 328361 = 246271) B246271
theorem B1869065 : Blo 215810 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B329063 : Blo 215810 329063 := bstep (se 1 (by rfl) ⟨246797, by rfl⟩ : syracuseStep 329063 = 493595) B493595
theorem B788039 : Blo 215810 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B1574777 : Blo 215810 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B396095 : Blo 215810 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B625801 : Blo 215810 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B1117435 : Blo 215810 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B1412615 : Blo 215810 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B888503 : Blo 215810 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B1774547 : Blo 215810 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B464123 : Blo 215810 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B20158469 : Blo 215810 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B2464019 : Blo 215810 2464019 := bstep (se 1 (by rfl) ⟨1848014, by rfl⟩ : syracuseStep 2464019 = 3696029) B3696029
theorem B629147 : Blo 215810 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B694943 : Blo 215810 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B760553 : Blo 215810 760553 := bstep (se 2 (by rfl) ⟨285207, by rfl⟩ : syracuseStep 760553 = 570415) B570415
theorem B367753 : Blo 215810 367753 := bstep (se 2 (by rfl) ⟨137907, by rfl⟩ : syracuseStep 367753 = 275815) B275815
theorem B368543 : Blo 215810 368543 := bstep (se 1 (by rfl) ⟨276407, by rfl⟩ : syracuseStep 368543 = 552815) B552815
theorem B467711 : Blo 215810 467711 := bstep (se 1 (by rfl) ⟨350783, by rfl⟩ : syracuseStep 467711 = 701567) B701567
theorem B3155431 : Blo 215810 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B2106971 : Blo 215810 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B731375 : Blo 215810 731375 := bstep (se 1 (by rfl) ⟨548531, by rfl⟩ : syracuseStep 731375 = 1097063) B1097063
theorem B8005877 : Blo 215810 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B1812905 : Blo 215810 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B733535 : Blo 215810 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B1093985 : Blo 215810 1093985 := bstep (se 2 (by rfl) ⟨410244, by rfl⟩ : syracuseStep 1093985 = 820489) B820489
theorem B275071 : Blo 215810 275071 := bstep (se 1 (by rfl) ⟨206303, by rfl⟩ : syracuseStep 275071 = 412607) B412607
theorem B963199 : Blo 215810 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B1094633 : Blo 215810 1094633 := bstep (se 2 (by rfl) ⟨410487, by rfl⟩ : syracuseStep 1094633 = 820975) B820975
theorem B243103 : Blo 215810 243103 := bstep (se 1 (by rfl) ⟨182327, by rfl⟩ : syracuseStep 243103 = 364655) B364655
theorem B734939 : Blo 215810 734939 := bstep (se 1 (by rfl) ⟨551204, by rfl⟩ : syracuseStep 734939 = 1102409) B1102409
theorem B702233 : Blo 215810 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B931783 : Blo 215810 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B243967 : Blo 215810 243967 := bstep (se 1 (by rfl) ⟨182975, by rfl⟩ : syracuseStep 243967 = 365951) B365951
theorem B244327 : Blo 215810 244327 := bstep (se 1 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 244327 = 366491) B366491
theorem B1653857 : Blo 215810 1653857 := bstep (se 2 (by rfl) ⟨620196, by rfl⟩ : syracuseStep 1653857 = 1240393) B1240393
theorem B244903 : Blo 215810 244903 := bstep (se 1 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 244903 = 367355) B367355
theorem B245119 : Blo 215810 245119 := bstep (se 1 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 245119 = 367679) B367679
theorem B737747 : Blo 215810 737747 := bstep (se 1 (by rfl) ⟨553310, by rfl⟩ : syracuseStep 737747 = 1106621) B1106621
theorem B837473 : Blo 215810 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B1099979 : Blo 215810 1099979 := bstep (se 1 (by rfl) ⟨824984, by rfl⟩ : syracuseStep 1099979 = 1649969) B1649969
theorem B215835 : Blo 215810 215835 := bstep (se 1 (by rfl) ⟨161876, by rfl⟩ : syracuseStep 215835 = 323753) B323753
theorem B215879 : Blo 215810 215879 := bstep (se 1 (by rfl) ⟨161909, by rfl⟩ : syracuseStep 215879 = 323819) B323819
theorem B215911 : Blo 215810 215911 := bstep (se 1 (by rfl) ⟨161933, by rfl⟩ : syracuseStep 215911 = 323867) B323867
theorem B740285 : Blo 215810 740285 := bstep (se 3 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 740285 = 277607) B277607
theorem B216991 : Blo 215810 216991 := bstep (se 1 (by rfl) ⟨162743, by rfl⟩ : syracuseStep 216991 = 325487) B325487
theorem B741473 : Blo 215810 741473 := bstep (se 2 (by rfl) ⟨278052, by rfl⟩ : syracuseStep 741473 = 556105) B556105
theorem B938087 : Blo 215810 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B1003735 : Blo 215810 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B217371 : Blo 215810 217371 := bstep (se 1 (by rfl) ⟨163028, by rfl⟩ : syracuseStep 217371 = 326057) B326057
theorem B217407 : Blo 215810 217407 := bstep (se 1 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 217407 = 326111) B326111
theorem B1855943 : Blo 215810 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B217567 : Blo 215810 217567 := bstep (se 1 (by rfl) ⟨163175, by rfl⟩ : syracuseStep 217567 = 326351) B326351
theorem B217575 : Blo 215810 217575 := bstep (se 1 (by rfl) ⟨163181, by rfl⟩ : syracuseStep 217575 = 326363) B326363
theorem B217627 : Blo 215810 217627 := bstep (se 1 (by rfl) ⟨163220, by rfl⟩ : syracuseStep 217627 = 326441) B326441
theorem B217983 : Blo 215810 217983 := bstep (se 1 (by rfl) ⟨163487, by rfl⟩ : syracuseStep 217983 = 326975) B326975
theorem B1038203 : Blo 215810 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1103867 : Blo 215810 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B8869985 : Blo 215810 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B219455 : Blo 215810 219455 := bstep (se 1 (by rfl) ⟨164591, by rfl⟩ : syracuseStep 219455 = 329183) B329183
theorem B547175 : Blo 215810 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B219631 : Blo 215810 219631 := bstep (se 1 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 219631 = 329447) B329447
theorem B12671477 : Blo 215810 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B547631 : Blo 215810 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B3726647 : Blo 215810 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B548167 : Blo 215810 548167 := bstep (se 1 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 548167 = 822251) B822251
theorem B1695131 : Blo 215810 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B417259 : Blo 215810 417259 := bstep (se 1 (by rfl) ⟨312944, by rfl⟩ : syracuseStep 417259 = 625889) B625889
theorem B7004231 : Blo 215810 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B876683 : Blo 215810 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B3989807 : Blo 215810 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B4121027 : Blo 215810 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B2221195 : Blo 215810 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B2254715 : Blo 215810 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B1109051 : Blo 215810 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B486683 : Blo 215810 486683 := bstep (se 1 (by rfl) ⟨365012, by rfl⟩ : syracuseStep 486683 = 730025) B730025
theorem B487673 : Blo 215810 487673 := bstep (se 2 (by rfl) ⟨182877, by rfl⟩ : syracuseStep 487673 = 365755) B365755
theorem B323879 : Blo 215810 323879 := bstep (se 1 (by rfl) ⟨242909, by rfl⟩ : syracuseStep 323879 = 485819) B485819
theorem B323999 : Blo 215810 323999 := bstep (se 1 (by rfl) ⟨242999, by rfl⟩ : syracuseStep 323999 = 485999) B485999
theorem B520831 : Blo 215810 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B488123 : Blo 215810 488123 := bstep (se 1 (by rfl) ⟨366092, by rfl⟩ : syracuseStep 488123 = 732185) B732185
theorem B1405673 : Blo 215810 1405673 := bstep (se 2 (by rfl) ⟨527127, by rfl⟩ : syracuseStep 1405673 = 1054255) B1054255
theorem B324575 : Blo 215810 324575 := bstep (se 1 (by rfl) ⟨243431, by rfl⟩ : syracuseStep 324575 = 486863) B486863
theorem B324587 : Blo 215810 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B5928227 : Blo 215810 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B324905 : Blo 215810 324905 := bstep (se 2 (by rfl) ⟨121839, by rfl⟩ : syracuseStep 324905 = 243679) B243679
theorem B488987 : Blo 215810 488987 := bstep (se 1 (by rfl) ⟨366740, by rfl⟩ : syracuseStep 488987 = 733481) B733481
theorem B1865375 : Blo 215810 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B1111967 : Blo 215810 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B1899001 : Blo 215810 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B1342271 : Blo 215810 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B326759 : Blo 215810 326759 := bstep (se 1 (by rfl) ⟨245069, by rfl⟩ : syracuseStep 326759 = 490139) B490139
theorem B326783 : Blo 215810 326783 := bstep (se 1 (by rfl) ⟨245087, by rfl⟩ : syracuseStep 326783 = 490175) B490175
theorem B490823 : Blo 215810 490823 := bstep (se 1 (by rfl) ⟨368117, by rfl⟩ : syracuseStep 490823 = 736235) B736235
theorem B327743 : Blo 215810 327743 := bstep (se 1 (by rfl) ⟨245807, by rfl⟩ : syracuseStep 327743 = 491615) B491615
theorem B327791 : Blo 215810 327791 := bstep (se 1 (by rfl) ⟨245843, by rfl⟩ : syracuseStep 327791 = 491687) B491687
theorem B491831 : Blo 215810 491831 := bstep (se 1 (by rfl) ⟨368873, by rfl⟩ : syracuseStep 491831 = 737747) B737747
theorem B1246043 : Blo 215810 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B525359 : Blo 215810 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B1049851 : Blo 215810 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B493523 : Blo 215810 493523 := bstep (se 1 (by rfl) ⟨370142, by rfl⟩ : syracuseStep 493523 = 740285) B740285
theorem B494315 : Blo 215810 494315 := bstep (se 1 (by rfl) ⟨370736, by rfl⟩ : syracuseStep 494315 = 741473) B741473
theorem B625391 : Blo 215810 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B1183031 : Blo 215810 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B692135 : Blo 215810 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B13438979 : Blo 215810 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B1642679 : Blo 215810 1642679 := bstep (se 1 (by rfl) ⟨1232009, by rfl⟩ : syracuseStep 1642679 = 2464019) B2464019
theorem B364783 : Blo 215810 364783 := bstep (se 1 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 364783 = 547175) B547175
theorem B463295 : Blo 215810 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B365087 : Blo 215810 365087 := bstep (se 1 (by rfl) ⟨273815, by rfl⟩ : syracuseStep 365087 = 547631) B547631
theorem B2233261 : Blo 215810 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B2659871 : Blo 215810 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B694441 : Blo 215810 694441 := bstep (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) B520831
theorem B366761 : Blo 215810 366761 := bstep (se 2 (by rfl) ⟨137535, by rfl⟩ : syracuseStep 366761 = 275071) B275071
theorem B1284265 : Blo 215810 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B3579389 : Blo 215810 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1056253 : Blo 215810 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B729323 : Blo 215810 729323 := bstep (se 1 (by rfl) ⟨546992, by rfl⟩ : syracuseStep 729323 = 1093985) B1093985
theorem B729755 : Blo 215810 729755 := bstep (se 1 (by rfl) ⟨547316, by rfl⟩ : syracuseStep 729755 = 1094633) B1094633
theorem B2532001 : Blo 215810 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B468155 : Blo 215810 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B730889 : Blo 215810 730889 := bstep (se 2 (by rfl) ⟨274083, by rfl⟩ : syracuseStep 730889 = 548167) B548167
theorem B2369341 : Blo 215810 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B2337821 : Blo 215810 2337821 := bstep (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) B876683
theorem B2797037 : Blo 215810 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B5353253 : Blo 215810 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B733319 : Blo 215810 733319 := bstep (se 1 (by rfl) ⟨549989, by rfl⟩ : syracuseStep 733319 = 1099979) B1099979
theorem B2961593 : Blo 215810 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B4207241 : Blo 215810 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B309415 : Blo 215810 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B735911 : Blo 215810 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B5913323 : Blo 215810 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B834401 : Blo 215810 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B1489913 : Blo 215810 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B507035 : Blo 215810 507035 := bstep (se 1 (by rfl) ⟨380276, by rfl⟩ : syracuseStep 507035 = 760553) B760553
theorem B1130087 : Blo 215810 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B245695 : Blo 215810 245695 := bstep (se 1 (by rfl) ⟨184271, by rfl⟩ : syracuseStep 245695 = 368543) B368543
theorem B4669487 : Blo 215810 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B311807 : Blo 215810 311807 := bstep (se 1 (by rfl) ⟨233855, by rfl⟩ : syracuseStep 311807 = 467711) B467711
theorem B739367 : Blo 215810 739367 := bstep (se 1 (by rfl) ⟨554525, by rfl⟩ : syracuseStep 739367 = 1109051) B1109051
theorem B215919 : Blo 215810 215919 := bstep (se 1 (by rfl) ⟨161939, by rfl⟩ : syracuseStep 215919 = 323879) B323879
theorem B215999 : Blo 215810 215999 := bstep (se 1 (by rfl) ⟨161999, by rfl⟩ : syracuseStep 215999 = 323999) B323999
theorem B937115 : Blo 215810 937115 := bstep (se 1 (by rfl) ⟨702836, by rfl⟩ : syracuseStep 937115 = 1405673) B1405673
theorem B216383 : Blo 215810 216383 := bstep (se 1 (by rfl) ⟨162287, by rfl⟩ : syracuseStep 216383 = 324575) B324575
theorem B216391 : Blo 215810 216391 := bstep (se 1 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 216391 = 324587) B324587
theorem B3952151 : Blo 215810 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B216603 : Blo 215810 216603 := bstep (se 1 (by rfl) ⟨162452, by rfl⟩ : syracuseStep 216603 = 324905) B324905
theorem B741311 : Blo 215810 741311 := bstep (se 1 (by rfl) ⟨555983, by rfl⟩ : syracuseStep 741311 = 1111967) B1111967
theorem B1102571 : Blo 215810 1102571 := bstep (se 1 (by rfl) ⟨826928, by rfl⟩ : syracuseStep 1102571 = 1653857) B1653857
theorem B217839 : Blo 215810 217839 := bstep (se 1 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 217839 = 326759) B326759
theorem B217855 : Blo 215810 217855 := bstep (se 1 (by rfl) ⟨163391, by rfl⟩ : syracuseStep 217855 = 326783) B326783
theorem B2774483 : Blo 215810 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B1332791 : Blo 215810 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B218751 : Blo 215810 218751 := bstep (se 1 (by rfl) ⟨164063, by rfl⟩ : syracuseStep 218751 = 328127) B328127
theorem B218907 : Blo 215810 218907 := bstep (se 1 (by rfl) ⟨164180, by rfl⟩ : syracuseStep 218907 = 328361) B328361
theorem B219375 : Blo 215810 219375 := bstep (se 1 (by rfl) ⟨164531, by rfl⟩ : syracuseStep 219375 = 329063) B329063
theorem B941743 : Blo 215810 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1237295 : Blo 215810 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B419431 : Blo 215810 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B8447651 : Blo 215810 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B2484431 : Blo 215810 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B2747351 : Blo 215810 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B1404647 : Blo 215810 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B1503143 : Blo 215810 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B487583 : Blo 215810 487583 := bstep (se 1 (by rfl) ⟨365687, by rfl⟩ : syracuseStep 487583 = 731375) B731375
theorem B5337251 : Blo 215810 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B1208603 : Blo 215810 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B324137 : Blo 215810 324137 := bstep (se 2 (by rfl) ⟨121551, by rfl⟩ : syracuseStep 324137 = 243103) B243103
theorem B324455 : Blo 215810 324455 := bstep (se 1 (by rfl) ⟨243341, by rfl⟩ : syracuseStep 324455 = 486683) B486683
theorem B1242377 : Blo 215810 1242377 := bstep (se 2 (by rfl) ⟨465891, by rfl⟩ : syracuseStep 1242377 = 931783) B931783
theorem B325115 : Blo 215810 325115 := bstep (se 1 (by rfl) ⟨243836, by rfl⟩ : syracuseStep 325115 = 487673) B487673
theorem B489023 : Blo 215810 489023 := bstep (se 1 (by rfl) ⟨366767, by rfl⟩ : syracuseStep 489023 = 733535) B733535
theorem B325289 : Blo 215810 325289 := bstep (se 2 (by rfl) ⟨121983, by rfl⟩ : syracuseStep 325289 = 243967) B243967
theorem B325415 : Blo 215810 325415 := bstep (se 1 (by rfl) ⟨244061, by rfl⟩ : syracuseStep 325415 = 488123) B488123
theorem B325769 : Blo 215810 325769 := bstep (se 2 (by rfl) ⟨122163, by rfl⟩ : syracuseStep 325769 = 244327) B244327
theorem B325991 : Blo 215810 325991 := bstep (se 1 (by rfl) ⟨244493, by rfl⟩ : syracuseStep 325991 = 488987) B488987
theorem B1243583 : Blo 215810 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B489959 : Blo 215810 489959 := bstep (se 1 (by rfl) ⟨367469, by rfl⟩ : syracuseStep 489959 = 734939) B734939
theorem B490337 : Blo 215810 490337 := bstep (se 2 (by rfl) ⟨183876, by rfl⟩ : syracuseStep 490337 = 367753) B367753
theorem B326537 : Blo 215810 326537 := bstep (se 2 (by rfl) ⟨122451, by rfl⟩ : syracuseStep 326537 = 244903) B244903
theorem B326825 : Blo 215810 326825 := bstep (se 2 (by rfl) ⟨122559, by rfl⟩ : syracuseStep 326825 = 245119) B245119
theorem B556345 : Blo 215810 556345 := bstep (se 2 (by rfl) ⟨208629, by rfl⟩ : syracuseStep 556345 = 417259) B417259
theorem B327215 : Blo 215810 327215 := bstep (se 1 (by rfl) ⟨245411, by rfl⟩ : syracuseStep 327215 = 490823) B490823
theorem B3112991 : Blo 215810 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B327887 : Blo 215810 327887 := bstep (se 1 (by rfl) ⟨245915, by rfl⟩ : syracuseStep 327887 = 491831) B491831
theorem B3376001 : Blo 215810 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B329015 : Blo 215810 329015 := bstep (se 1 (by rfl) ⟨246761, by rfl⟩ : syracuseStep 329015 = 493523) B493523
theorem B492911 : Blo 215810 492911 := bstep (se 1 (by rfl) ⟨369683, by rfl⟩ : syracuseStep 492911 = 739367) B739367
theorem B329543 : Blo 215810 329543 := bstep (se 1 (by rfl) ⟨247157, by rfl⟩ : syracuseStep 329543 = 494315) B494315
theorem B624743 : Blo 215810 624743 := bstep (se 1 (by rfl) ⟨468557, by rfl⟩ : syracuseStep 624743 = 937115) B937115
theorem B559241 : Blo 215810 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B788687 : Blo 215810 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B461423 : Blo 215810 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B494207 : Blo 215810 494207 := bstep (se 1 (by rfl) ⟨370655, by rfl⟩ : syracuseStep 494207 = 741311) B741311
theorem B1773247 : Blo 215810 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B888527 : Blo 215810 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B824863 : Blo 215810 824863 := bstep (se 1 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 824863 = 1237295) B1237295
theorem B1974395 : Blo 215810 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B925921 : Blo 215810 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B1712353 : Blo 215810 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B828251 : Blo 215810 828251 := bstep (se 1 (by rfl) ⟨621188, by rfl⟩ : syracuseStep 828251 = 1242377) B1242377
theorem B829055 : Blo 215810 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B3942215 : Blo 215810 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B993275 : Blo 215810 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B338023 : Blo 215810 338023 := bstep (se 1 (by rfl) ⟨253517, by rfl⟩ : syracuseStep 338023 = 507035) B507035
theorem B1255657 : Blo 215810 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B830695 : Blo 215810 830695 := bstep (se 1 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 830695 = 1246043) B1246043
theorem B831485 : Blo 215810 831485 := bstep (se 3 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 831485 = 311807) B311807
theorem B2634767 : Blo 215810 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B8959319 : Blo 215810 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B1095119 : Blo 215810 1095119 := bstep (se 1 (by rfl) ⟨821339, by rfl⟩ : syracuseStep 1095119 = 1642679) B1642679
theorem B308863 : Blo 215810 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B243391 : Blo 215810 243391 := bstep (se 1 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 243391 = 365087) B365087
theorem B735047 : Blo 215810 735047 := bstep (se 1 (by rfl) ⟨551285, by rfl⟩ : syracuseStep 735047 = 1102571) B1102571
theorem B1849655 : Blo 215810 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B244507 : Blo 215810 244507 := bstep (se 1 (by rfl) ⟨183380, by rfl⟩ : syracuseStep 244507 = 366761) B366761
theorem B312103 : Blo 215810 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B1656287 : Blo 215810 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B1558547 : Blo 215810 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B936431 : Blo 215810 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B1002095 : Blo 215810 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B3558167 : Blo 215810 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B805735 : Blo 215810 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B412553 : Blo 215810 412553 := bstep (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) B309415
theorem B216091 : Blo 215810 216091 := bstep (se 1 (by rfl) ⟨162068, by rfl⟩ : syracuseStep 216091 = 324137) B324137
theorem B2804827 : Blo 215810 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B216303 : Blo 215810 216303 := bstep (se 1 (by rfl) ⟨162227, by rfl⟩ : syracuseStep 216303 = 324455) B324455
theorem B216743 : Blo 215810 216743 := bstep (se 1 (by rfl) ⟨162557, by rfl⟩ : syracuseStep 216743 = 325115) B325115
theorem B216859 : Blo 215810 216859 := bstep (se 1 (by rfl) ⟨162644, by rfl⟩ : syracuseStep 216859 = 325289) B325289
theorem B216943 : Blo 215810 216943 := bstep (se 1 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 216943 = 325415) B325415
theorem B217179 : Blo 215810 217179 := bstep (se 1 (by rfl) ⟨162884, by rfl⟩ : syracuseStep 217179 = 325769) B325769
theorem B217327 : Blo 215810 217327 := bstep (se 1 (by rfl) ⟨162995, by rfl⟩ : syracuseStep 217327 = 325991) B325991
theorem B12636485 : Blo 215810 12636485 := bstep (se 4 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 12636485 = 2369341) B2369341
theorem B741793 : Blo 215810 741793 := bstep (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) B556345
theorem B217691 : Blo 215810 217691 := bstep (se 1 (by rfl) ⟨163268, by rfl⟩ : syracuseStep 217691 = 326537) B326537
theorem B217883 : Blo 215810 217883 := bstep (se 1 (by rfl) ⟨163412, by rfl⟩ : syracuseStep 217883 = 326825) B326825
theorem B218143 : Blo 215810 218143 := bstep (se 1 (by rfl) ⟨163607, by rfl⟩ : syracuseStep 218143 = 327215) B327215
theorem B218495 : Blo 215810 218495 := bstep (se 1 (by rfl) ⟨163871, by rfl⟩ : syracuseStep 218495 = 327743) B327743
theorem B218527 : Blo 215810 218527 := bstep (se 1 (by rfl) ⟨163895, by rfl⟩ : syracuseStep 218527 = 327791) B327791
theorem B350239 : Blo 215810 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B1399801 : Blo 215810 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B416927 : Blo 215810 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B2386259 : Blo 215810 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B486215 : Blo 215810 486215 := bstep (se 1 (by rfl) ⟨364661, by rfl⟩ : syracuseStep 486215 = 729323) B729323
theorem B486377 : Blo 215810 486377 := bstep (se 2 (by rfl) ⟨182391, by rfl⟩ : syracuseStep 486377 = 364783) B364783
theorem B486503 : Blo 215810 486503 := bstep (se 1 (by rfl) ⟨364877, by rfl⟩ : syracuseStep 486503 = 729755) B729755
theorem B5631767 : Blo 215810 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B487259 : Blo 215810 487259 := bstep (se 1 (by rfl) ⟨365444, by rfl⟩ : syracuseStep 487259 = 730889) B730889
theorem B2977681 : Blo 215810 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1831567 : Blo 215810 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B1864691 : Blo 215810 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B3568835 : Blo 215810 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B488879 : Blo 215810 488879 := bstep (se 1 (by rfl) ⟨366659, by rfl⟩ : syracuseStep 488879 = 733319) B733319
theorem B325055 : Blo 215810 325055 := bstep (se 1 (by rfl) ⟨243791, by rfl⟩ : syracuseStep 325055 = 487583) B487583
theorem B326015 : Blo 215810 326015 := bstep (se 1 (by rfl) ⟨244511, by rfl⟩ : syracuseStep 326015 = 489023) B489023
theorem B326639 : Blo 215810 326639 := bstep (se 1 (by rfl) ⟨244979, by rfl⟩ : syracuseStep 326639 = 489959) B489959
theorem B490607 : Blo 215810 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B326891 : Blo 215810 326891 := bstep (se 1 (by rfl) ⟨245168, by rfl⟩ : syracuseStep 326891 = 490337) B490337
theorem B556267 : Blo 215810 556267 := bstep (se 1 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 556267 = 834401) B834401
theorem B1408337 : Blo 215810 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B753391 : Blo 215810 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B327593 : Blo 215810 327593 := bstep (se 2 (by rfl) ⟨122847, by rfl⟩ : syracuseStep 327593 = 245695) B245695
theorem B328607 : Blo 215810 328607 := bstep (se 1 (by rfl) ⟨246455, by rfl⟩ : syracuseStep 328607 = 492911) B492911
theorem B525791 : Blo 215810 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B624287 : Blo 215810 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B329471 : Blo 215810 329471 := bstep (se 1 (by rfl) ⟨247103, by rfl⟩ : syracuseStep 329471 = 494207) B494207
theorem B592351 : Blo 215810 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B8424323 : Blo 215810 8424323 := bstep (se 1 (by rfl) ⟨6318242, by rfl⟩ : syracuseStep 8424323 = 12636485) B12636485
theorem B1674209 : Blo 215810 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B3739769 : Blo 215810 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B2364329 : Blo 215810 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B3970241 : Blo 215810 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B1316263 : Blo 215810 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B989057 : Blo 215810 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B2628143 : Blo 215810 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B662183 : Blo 215810 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B466985 : Blo 215810 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B5972879 : Blo 215810 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B730079 : Blo 215810 730079 := bstep (se 1 (by rfl) ⟨547559, by rfl⟩ : syracuseStep 730079 = 1095119) B1095119
theorem B2075327 : Blo 215810 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B372827 : Blo 215810 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B668063 : Blo 215810 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B2372111 : Blo 215810 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B2442089 : Blo 215810 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B1590839 : Blo 215810 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1230461 : Blo 215810 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B1099817 : Blo 215810 1099817 := bstep (se 2 (by rfl) ⟨412431, by rfl⟩ : syracuseStep 1099817 = 824863) B824863
theorem B411817 : Blo 215810 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B1100141 : Blo 215810 1100141 := bstep (se 3 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 1100141 = 412553) B412553
theorem B3754511 : Blo 215810 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B1756511 : Blo 215810 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B2379223 : Blo 215810 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B216703 : Blo 215810 216703 := bstep (se 1 (by rfl) ⟨162527, by rfl⟩ : syracuseStep 216703 = 325055) B325055
theorem B1233103 : Blo 215810 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B217343 : Blo 215810 217343 := bstep (se 1 (by rfl) ⟨163007, by rfl⟩ : syracuseStep 217343 = 326015) B326015
theorem B741689 : Blo 215810 741689 := bstep (se 2 (by rfl) ⟨278133, by rfl⟩ : syracuseStep 741689 = 556267) B556267
theorem B217759 : Blo 215810 217759 := bstep (se 1 (by rfl) ⟨163319, by rfl⟩ : syracuseStep 217759 = 326639) B326639
theorem B217927 : Blo 215810 217927 := bstep (se 1 (by rfl) ⟨163445, by rfl⟩ : syracuseStep 217927 = 326891) B326891
theorem B938891 : Blo 215810 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B1004521 : Blo 215810 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B218395 : Blo 215810 218395 := bstep (se 1 (by rfl) ⟨163796, by rfl⟩ : syracuseStep 218395 = 327593) B327593
theorem B218591 : Blo 215810 218591 := bstep (se 1 (by rfl) ⟨163943, by rfl⟩ : syracuseStep 218591 = 327887) B327887
theorem B1234561 : Blo 215810 1234561 := bstep (se 2 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 1234561 = 925921) B925921
theorem B2283137 : Blo 215810 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B2250667 : Blo 215810 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B219343 : Blo 215810 219343 := bstep (se 1 (by rfl) ⟨164507, by rfl⟩ : syracuseStep 219343 = 329015) B329015
theorem B1104191 : Blo 215810 1104191 := bstep (se 1 (by rfl) ⟨828143, by rfl⟩ : syracuseStep 1104191 = 1656287) B1656287
theorem B219695 : Blo 215810 219695 := bstep (se 1 (by rfl) ⟨164771, by rfl⟩ : syracuseStep 219695 = 329543) B329543
theorem B1039031 : Blo 215810 1039031 := bstep (se 1 (by rfl) ⟨779273, by rfl⟩ : syracuseStep 1039031 = 1558547) B1558547
theorem B416495 : Blo 215810 416495 := bstep (se 1 (by rfl) ⟨312371, by rfl⟩ : syracuseStep 416495 = 624743) B624743
theorem B450697 : Blo 215810 450697 := bstep (se 2 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 450697 = 338023) B338023
theorem B1074313 : Blo 215810 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B1664549 : Blo 215810 1664549 := bstep (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) B312103
theorem B1107593 : Blo 215810 1107593 := bstep (se 2 (by rfl) ⟨415347, by rfl⟩ : syracuseStep 1107593 = 830695) B830695
theorem B552167 : Blo 215810 552167 := bstep (se 1 (by rfl) ⟨414125, by rfl⟩ : syracuseStep 552167 = 828251) B828251
theorem B552703 : Blo 215810 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B324143 : Blo 215810 324143 := bstep (se 1 (by rfl) ⟨243107, by rfl⟩ : syracuseStep 324143 = 486215) B486215
theorem B324251 : Blo 215810 324251 := bstep (se 1 (by rfl) ⟨243188, by rfl⟩ : syracuseStep 324251 = 486377) B486377
theorem B324335 : Blo 215810 324335 := bstep (se 1 (by rfl) ⟨243251, by rfl⟩ : syracuseStep 324335 = 486503) B486503
theorem B324521 : Blo 215810 324521 := bstep (se 2 (by rfl) ⟨121695, by rfl⟩ : syracuseStep 324521 = 243391) B243391
theorem B324839 : Blo 215810 324839 := bstep (se 1 (by rfl) ⟨243629, by rfl⟩ : syracuseStep 324839 = 487259) B487259
theorem B554323 : Blo 215810 554323 := bstep (se 1 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 554323 = 831485) B831485
theorem B1111805 : Blo 215810 1111805 := bstep (se 3 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 1111805 = 416927) B416927
theorem B1243127 : Blo 215810 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B325919 : Blo 215810 325919 := bstep (se 1 (by rfl) ⟨244439, by rfl⟩ : syracuseStep 325919 = 488879) B488879
theorem B326009 : Blo 215810 326009 := bstep (se 2 (by rfl) ⟨122253, by rfl⟩ : syracuseStep 326009 = 244507) B244507
theorem B490031 : Blo 215810 490031 := bstep (se 1 (by rfl) ⟨367523, by rfl⟩ : syracuseStep 490031 = 735047) B735047
theorem B1866401 : Blo 215810 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B327071 : Blo 215810 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B1245293 : Blo 215810 1245293 := bstep (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) B466985
theorem B820307 : Blo 215810 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B2493179 : Blo 215810 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B494459 : Blo 215810 494459 := bstep (se 1 (by rfl) ⟨370844, by rfl⟩ : syracuseStep 494459 = 741689) B741689
theorem B625927 : Blo 215810 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B1576219 : Blo 215810 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B692687 : Blo 215810 692687 := bstep (se 1 (by rfl) ⟨519515, by rfl⟩ : syracuseStep 692687 = 1039031) B1039031
theorem B1644137 : Blo 215810 1644137 := bstep (se 2 (by rfl) ⟨616551, by rfl⟩ : syracuseStep 1644137 = 1233103) B1233103
theorem B1383551 : Blo 215810 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B368111 : Blo 215810 368111 := bstep (se 1 (by rfl) ⟨276083, by rfl⟩ : syracuseStep 368111 = 552167) B552167
theorem B1646081 : Blo 215810 1646081 := bstep (se 2 (by rfl) ⟨617280, by rfl⟩ : syracuseStep 1646081 = 1234561) B1234561
theorem B4464557 : Blo 215810 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B1581407 : Blo 215810 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B828751 : Blo 215810 828751 := bstep (se 1 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 828751 = 1243127) B1243127
theorem B600929 : Blo 215810 600929 := bstep (se 2 (by rfl) ⟨225348, by rfl⟩ : syracuseStep 600929 = 450697) B450697
theorem B1060559 : Blo 215810 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B733211 : Blo 215810 733211 := bstep (se 1 (by rfl) ⟨549908, by rfl⟩ : syracuseStep 733211 = 1099817) B1099817
theorem B733427 : Blo 215810 733427 := bstep (se 1 (by rfl) ⟨550070, by rfl⟩ : syracuseStep 733427 = 1100141) B1100141
theorem B2503007 : Blo 215810 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B5616215 : Blo 215810 5616215 := bstep (se 1 (by rfl) ⟨4212161, by rfl⟩ : syracuseStep 5616215 = 8424323) B8424323
theorem B3159205 : Blo 215810 3159205 := bstep (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) B592351
theorem B1522091 : Blo 215810 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B736127 : Blo 215810 736127 := bstep (se 1 (by rfl) ⟨552095, by rfl⟩ : syracuseStep 736127 = 1104191) B1104191
theorem B1752095 : Blo 215810 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B441455 : Blo 215810 441455 := bstep (se 1 (by rfl) ⟨331091, by rfl⟩ : syracuseStep 441455 = 662183) B662183
theorem B277663 : Blo 215810 277663 := bstep (se 1 (by rfl) ⟨208247, by rfl⟩ : syracuseStep 277663 = 416495) B416495
theorem B736937 : Blo 215810 736937 := bstep (se 2 (by rfl) ⟨276351, by rfl⟩ : syracuseStep 736937 = 552703) B552703
theorem B2637485 : Blo 215810 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B3981919 : Blo 215810 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B738395 : Blo 215810 738395 := bstep (se 1 (by rfl) ⟨553796, by rfl⟩ : syracuseStep 738395 = 1107593) B1107593
theorem B739097 : Blo 215810 739097 := bstep (se 2 (by rfl) ⟨277161, by rfl⟩ : syracuseStep 739097 = 554323) B554323
theorem B1755017 : Blo 215810 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B3000889 : Blo 215810 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B248551 : Blo 215810 248551 := bstep (se 1 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 248551 = 372827) B372827
theorem B445375 : Blo 215810 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B216095 : Blo 215810 216095 := bstep (se 1 (by rfl) ⟨162071, by rfl⟩ : syracuseStep 216095 = 324143) B324143
theorem B216167 : Blo 215810 216167 := bstep (se 1 (by rfl) ⟨162125, by rfl⟩ : syracuseStep 216167 = 324251) B324251
theorem B216223 : Blo 215810 216223 := bstep (se 1 (by rfl) ⟨162167, by rfl⟩ : syracuseStep 216223 = 324335) B324335
theorem B216347 : Blo 215810 216347 := bstep (se 1 (by rfl) ⟨162260, by rfl⟩ : syracuseStep 216347 = 324521) B324521
theorem B216559 : Blo 215810 216559 := bstep (se 1 (by rfl) ⟨162419, by rfl⟩ : syracuseStep 216559 = 324839) B324839
theorem B741203 : Blo 215810 741203 := bstep (se 1 (by rfl) ⟨555902, by rfl⟩ : syracuseStep 741203 = 1111805) B1111805
theorem B217279 : Blo 215810 217279 := bstep (se 1 (by rfl) ⟨162959, by rfl⟩ : syracuseStep 217279 = 325919) B325919
theorem B217339 : Blo 215810 217339 := bstep (se 1 (by rfl) ⟨163004, by rfl⟩ : syracuseStep 217339 = 326009) B326009
theorem B218047 : Blo 215810 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B1628059 : Blo 215810 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B219071 : Blo 215810 219071 := bstep (se 1 (by rfl) ⟨164303, by rfl⟩ : syracuseStep 219071 = 328607) B328607
theorem B416191 : Blo 215810 416191 := bstep (se 1 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 416191 = 624287) B624287
theorem B219647 : Blo 215810 219647 := bstep (se 1 (by rfl) ⟨164735, by rfl⟩ : syracuseStep 219647 = 329471) B329471
theorem B1432417 : Blo 215810 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1171007 : Blo 215810 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B549089 : Blo 215810 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B2646827 : Blo 215810 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B1402109 : Blo 215810 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B3172297 : Blo 215810 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B486719 : Blo 215810 486719 := bstep (se 1 (by rfl) ⟨365039, by rfl⟩ : syracuseStep 486719 = 730079) B730079
theorem B1109699 : Blo 215810 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B1339361 : Blo 215810 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B326687 : Blo 215810 326687 := bstep (se 1 (by rfl) ⟨245015, by rfl⟩ : syracuseStep 326687 = 490031) B490031
theorem B1244267 : Blo 215810 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B492263 : Blo 215810 492263 := bstep (se 1 (by rfl) ⟨369197, by rfl⟩ : syracuseStep 492263 = 738395) B738395
theorem B5309225 : Blo 215810 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B492731 : Blo 215810 492731 := bstep (se 1 (by rfl) ⟨369548, by rfl⟩ : syracuseStep 492731 = 739097) B739097
theorem B329639 : Blo 215810 329639 := bstep (se 1 (by rfl) ⟨247229, by rfl⟩ : syracuseStep 329639 = 494459) B494459
theorem B494135 : Blo 215810 494135 := bstep (se 1 (by rfl) ⟨370601, by rfl⟩ : syracuseStep 494135 = 741203) B741203
theorem B4229729 : Blo 215810 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B461791 : Blo 215810 461791 := bstep (se 1 (by rfl) ⟨346343, by rfl⟩ : syracuseStep 461791 = 692687) B692687
theorem B4001185 : Blo 215810 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B2101625 : Blo 215810 2101625 := bstep (se 2 (by rfl) ⟨788109, by rfl⟩ : syracuseStep 2101625 = 1576219) B1576219
theorem B922367 : Blo 215810 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B366059 : Blo 215810 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B1054271 : Blo 215810 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B16849093 : Blo 215810 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B400619 : Blo 215810 400619 := bstep (se 1 (by rfl) ⟨300464, by rfl⟩ : syracuseStep 400619 = 600929) B600929
theorem B2170745 : Blo 215810 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B892907 : Blo 215810 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B3744143 : Blo 215810 3744143 := bstep (se 1 (by rfl) ⟨2808107, by rfl⟩ : syracuseStep 3744143 = 5616215) B5616215
theorem B1909889 : Blo 215810 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B370217 : Blo 215810 370217 := bstep (se 2 (by rfl) ⟨138831, by rfl⟩ : syracuseStep 370217 = 277663) B277663
theorem B829511 : Blo 215810 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B830195 : Blo 215810 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B1096091 : Blo 215810 1096091 := bstep (se 1 (by rfl) ⟨822068, by rfl⟩ : syracuseStep 1096091 = 1644137) B1644137
theorem B1325605 : Blo 215810 1325605 := bstep (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) B248551
theorem B834569 : Blo 215810 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B245407 : Blo 215810 245407 := bstep (se 1 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 245407 = 368111) B368111
theorem B2375333 : Blo 215810 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B1097387 : Blo 215810 1097387 := bstep (se 1 (by rfl) ⟨823040, by rfl⟩ : syracuseStep 1097387 = 1646081) B1646081
theorem B934739 : Blo 215810 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B739799 : Blo 215810 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B707039 : Blo 215810 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B1168063 : Blo 215810 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B217791 : Blo 215810 217791 := bstep (se 1 (by rfl) ⟨163343, by rfl⟩ : syracuseStep 217791 = 326687) B326687
theorem B1758323 : Blo 215810 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B546871 : Blo 215810 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B4708853 : Blo 215810 4708853 := bstep (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) B441455
theorem B1170011 : Blo 215810 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B1105001 : Blo 215810 1105001 := bstep (se 2 (by rfl) ⟨414375, by rfl⟩ : syracuseStep 1105001 = 828751) B828751
theorem B1662119 : Blo 215810 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B780671 : Blo 215810 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B2976371 : Blo 215810 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1764551 : Blo 215810 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B324479 : Blo 215810 324479 := bstep (se 1 (by rfl) ⟨243359, by rfl⟩ : syracuseStep 324479 = 486719) B486719
theorem B488807 : Blo 215810 488807 := bstep (se 1 (by rfl) ⟨366605, by rfl⟩ : syracuseStep 488807 = 733211) B733211
theorem B488951 : Blo 215810 488951 := bstep (se 1 (by rfl) ⟨366713, by rfl⟩ : syracuseStep 488951 = 733427) B733427
theorem B1668671 : Blo 215810 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B554921 : Blo 215810 554921 := bstep (se 2 (by rfl) ⟨208095, by rfl⟩ : syracuseStep 554921 = 416191) B416191
theorem B1014727 : Blo 215810 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B490751 : Blo 215810 490751 := bstep (se 1 (by rfl) ⟨368063, by rfl⟩ : syracuseStep 490751 = 736127) B736127
theorem B491291 : Blo 215810 491291 := bstep (se 1 (by rfl) ⟨368468, by rfl⟩ : syracuseStep 491291 = 736937) B736937
theorem B328175 : Blo 215810 328175 := bstep (se 1 (by rfl) ⟨246131, by rfl⟩ : syracuseStep 328175 = 492263) B492263
theorem B3539483 : Blo 215810 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B623159 : Blo 215810 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B328487 : Blo 215810 328487 := bstep (se 1 (by rfl) ⟨246365, by rfl⟩ : syracuseStep 328487 = 492731) B492731
theorem B493199 : Blo 215810 493199 := bstep (se 1 (by rfl) ⟨369899, by rfl⟩ : syracuseStep 493199 = 739799) B739799
theorem B329423 : Blo 215810 329423 := bstep (se 1 (by rfl) ⟨247067, by rfl⟩ : syracuseStep 329423 = 494135) B494135
theorem B2819819 : Blo 215810 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B2459645 : Blo 215810 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B6229669 : Blo 215810 6229669 := bstep (se 4 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 6229669 = 1168063) B1168063
theorem B267079 : Blo 215810 267079 := bstep (se 1 (by rfl) ⟨200309, by rfl⟩ : syracuseStep 267079 = 400619) B400619
theorem B1447163 : Blo 215810 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B595271 : Blo 215810 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B2496095 : Blo 215810 2496095 := bstep (se 1 (by rfl) ⟨1872071, by rfl⟩ : syracuseStep 2496095 = 3744143) B3744143
theorem B3120029 : Blo 215810 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B729161 : Blo 215810 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B1352969 : Blo 215810 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B369947 : Blo 215810 369947 := bstep (se 1 (by rfl) ⟨277460, by rfl⟩ : syracuseStep 369947 = 554921) B554921
theorem B730727 : Blo 215810 730727 := bstep (se 1 (by rfl) ⟨548045, by rfl⟩ : syracuseStep 730727 = 1096091) B1096091
theorem B1583555 : Blo 215810 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B731591 : Blo 215810 731591 := bstep (se 1 (by rfl) ⟨548693, by rfl⟩ : syracuseStep 731591 = 1097387) B1097387
theorem B471359 : Blo 215810 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B244039 : Blo 215810 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B702847 : Blo 215810 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B736667 : Blo 215810 736667 := bstep (se 1 (by rfl) ⟨552500, by rfl⟩ : syracuseStep 736667 = 1105001) B1105001
theorem B246811 : Blo 215810 246811 := bstep (se 1 (by rfl) ⟨185108, by rfl⟩ : syracuseStep 246811 = 370217) B370217
theorem B1984247 : Blo 215810 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B22465457 : Blo 215810 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B216319 : Blo 215810 216319 := bstep (se 1 (by rfl) ⟨162239, by rfl⟩ : syracuseStep 216319 = 324479) B324479
theorem B219759 : Blo 215810 219759 := bstep (se 1 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 219759 = 329639) B329639
theorem B1401083 : Blo 215810 1401083 := bstep (se 1 (by rfl) ⟨1050812, by rfl⟩ : syracuseStep 1401083 = 2101625) B2101625
theorem B1172215 : Blo 215810 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B615721 : Blo 215810 615721 := bstep (se 2 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 615721 = 461791) B461791
theorem B3139235 : Blo 215810 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B5334913 : Blo 215810 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B1108079 : Blo 215810 1108079 := bstep (se 1 (by rfl) ⟨831059, by rfl⟩ : syracuseStep 1108079 = 1662119) B1662119
theorem B1273259 : Blo 215810 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B553007 : Blo 215810 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B520447 : Blo 215810 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B553463 : Blo 215810 553463 := bstep (se 1 (by rfl) ⟨415097, by rfl⟩ : syracuseStep 553463 = 830195) B830195
theorem B1176367 : Blo 215810 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B1767473 : Blo 215810 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B325871 : Blo 215810 325871 := bstep (se 1 (by rfl) ⟨244403, by rfl⟩ : syracuseStep 325871 = 488807) B488807
theorem B325967 : Blo 215810 325967 := bstep (se 1 (by rfl) ⟨244475, by rfl⟩ : syracuseStep 325967 = 488951) B488951
theorem B1112447 : Blo 215810 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B556379 : Blo 215810 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B327167 : Blo 215810 327167 := bstep (se 1 (by rfl) ⟨245375, by rfl⟩ : syracuseStep 327167 = 490751) B490751
theorem B327209 : Blo 215810 327209 := bstep (se 2 (by rfl) ⟨122703, by rfl⟩ : syracuseStep 327209 = 245407) B245407
theorem B327527 : Blo 215810 327527 := bstep (se 1 (by rfl) ⟨245645, by rfl⟩ : syracuseStep 327527 = 491291) B491291
theorem B2359655 : Blo 215810 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B328799 : Blo 215810 328799 := bstep (se 1 (by rfl) ⟨246599, by rfl⟩ : syracuseStep 328799 = 493199) B493199
theorem B1639763 : Blo 215810 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B329081 : Blo 215810 329081 := bstep (se 2 (by rfl) ⟨123405, by rfl⟩ : syracuseStep 329081 = 246811) B246811
theorem B820961 : Blo 215810 820961 := bstep (se 2 (by rfl) ⟨307860, by rfl⟩ : syracuseStep 820961 = 615721) B615721
theorem B14976971 : Blo 215810 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B7113217 : Blo 215810 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B396847 : Blo 215810 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B693929 : Blo 215810 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B368671 : Blo 215810 368671 := bstep (se 1 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 368671 = 553007) B553007
theorem B368975 : Blo 215810 368975 := bstep (se 1 (by rfl) ⟨276731, by rfl⟩ : syracuseStep 368975 = 553463) B553463
theorem B370919 : Blo 215810 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B1256957 : Blo 215810 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B1322831 : Blo 215810 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B3748517 : Blo 215810 3748517 := bstep (se 4 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 3748517 = 702847) B702847
theorem B964775 : Blo 215810 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B2080019 : Blo 215810 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B7519517 : Blo 215810 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B8306225 : Blo 215810 8306225 := bstep (se 2 (by rfl) ⟨3114834, by rfl⟩ : syracuseStep 8306225 = 6229669) B6229669
theorem B934055 : Blo 215810 934055 := bstep (se 1 (by rfl) ⟨700541, by rfl⟩ : syracuseStep 934055 = 1401083) B1401083
theorem B901979 : Blo 215810 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B246631 : Blo 215810 246631 := bstep (se 1 (by rfl) ⟨184973, by rfl⟩ : syracuseStep 246631 = 369947) B369947
theorem B738719 : Blo 215810 738719 := bstep (se 1 (by rfl) ⟨554039, by rfl⟩ : syracuseStep 738719 = 1108079) B1108079
theorem B217247 : Blo 215810 217247 := bstep (se 1 (by rfl) ⟨162935, by rfl⟩ : syracuseStep 217247 = 325871) B325871
theorem B217311 : Blo 215810 217311 := bstep (se 1 (by rfl) ⟨162983, by rfl⟩ : syracuseStep 217311 = 325967) B325967
theorem B741631 : Blo 215810 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B218111 : Blo 215810 218111 := bstep (se 1 (by rfl) ⟨163583, by rfl⟩ : syracuseStep 218111 = 327167) B327167
theorem B218139 : Blo 215810 218139 := bstep (se 1 (by rfl) ⟨163604, by rfl⟩ : syracuseStep 218139 = 327209) B327209
theorem B218351 : Blo 215810 218351 := bstep (se 1 (by rfl) ⟨163763, by rfl⟩ : syracuseStep 218351 = 327527) B327527
theorem B218783 : Blo 215810 218783 := bstep (se 1 (by rfl) ⟨164087, by rfl⟩ : syracuseStep 218783 = 328175) B328175
theorem B415439 : Blo 215810 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B218991 : Blo 215810 218991 := bstep (se 1 (by rfl) ⟨164243, by rfl⟩ : syracuseStep 218991 = 328487) B328487
theorem B219615 : Blo 215810 219615 := bstep (se 1 (by rfl) ⟨164711, by rfl⟩ : syracuseStep 219615 = 329423) B329423
theorem B1664063 : Blo 215810 1664063 := bstep (se 1 (by rfl) ⟨1248047, by rfl⟩ : syracuseStep 1664063 = 2496095) B2496095
theorem B6251813 : Blo 215810 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B486107 : Blo 215810 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B1568489 : Blo 215810 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B487151 : Blo 215810 487151 := bstep (se 1 (by rfl) ⟨365363, by rfl⟩ : syracuseStep 487151 = 730727) B730727
theorem B356105 : Blo 215810 356105 := bstep (se 2 (by rfl) ⟨133539, by rfl⟩ : syracuseStep 356105 = 267079) B267079
theorem B2092823 : Blo 215810 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B4222813 : Blo 215810 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B487727 : Blo 215810 487727 := bstep (se 1 (by rfl) ⟨365795, by rfl⟩ : syracuseStep 487727 = 731591) B731591
theorem B848839 : Blo 215810 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B325385 : Blo 215810 325385 := bstep (se 2 (by rfl) ⟨122019, by rfl⟩ : syracuseStep 325385 = 244039) B244039
theorem B1178315 : Blo 215810 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B491111 : Blo 215810 491111 := bstep (se 1 (by rfl) ⟨368333, by rfl⟩ : syracuseStep 491111 = 736667) B736667
theorem B491561 : Blo 215810 491561 := bstep (se 2 (by rfl) ⟨184335, by rfl⟩ : syracuseStep 491561 = 368671) B368671
theorem B622703 : Blo 215810 622703 := bstep (se 1 (by rfl) ⟨467027, by rfl⟩ : syracuseStep 622703 = 934055) B934055
theorem B1573103 : Blo 215810 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B492479 : Blo 215810 492479 := bstep (se 1 (by rfl) ⟨369359, by rfl⟩ : syracuseStep 492479 = 738719) B738719
theorem B328841 : Blo 215810 328841 := bstep (se 2 (by rfl) ⟨123315, by rfl⟩ : syracuseStep 328841 = 246631) B246631
theorem B462619 : Blo 215810 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B529129 : Blo 215810 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B988841 : Blo 215810 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B4167875 : Blo 215810 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B237403 : Blo 215810 237403 := bstep (se 1 (by rfl) ⟨178052, by rfl⟩ : syracuseStep 237403 = 356105) B356105
theorem B2499011 : Blo 215810 2499011 := bstep (se 1 (by rfl) ⟨1874258, by rfl⟩ : syracuseStep 2499011 = 3748517) B3748517
theorem B1386679 : Blo 215810 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B601319 : Blo 215810 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B1093175 : Blo 215810 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B9484289 : Blo 215810 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B276959 : Blo 215810 276959 := bstep (se 1 (by rfl) ⟨207719, by rfl⟩ : syracuseStep 276959 = 415439) B415439
theorem B245983 : Blo 215810 245983 := bstep (se 1 (by rfl) ⟨184487, by rfl⟩ : syracuseStep 245983 = 368975) B368975
theorem B1131785 : Blo 215810 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B247279 : Blo 215810 247279 := bstep (se 1 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 247279 = 370919) B370919
theorem B837971 : Blo 215810 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B1395215 : Blo 215810 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B216923 : Blo 215810 216923 := bstep (se 1 (by rfl) ⟨162692, by rfl⟩ : syracuseStep 216923 = 325385) B325385
theorem B643183 : Blo 215810 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B4182637 : Blo 215810 4182637 := bstep (se 3 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 4182637 = 1568489) B1568489
theorem B3527549 : Blo 215810 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B219199 : Blo 215810 219199 := bstep (se 1 (by rfl) ⟨164399, by rfl⟩ : syracuseStep 219199 = 328799) B328799
theorem B219387 : Blo 215810 219387 := bstep (se 1 (by rfl) ⟨164540, by rfl⟩ : syracuseStep 219387 = 329081) B329081
theorem B547307 : Blo 215810 547307 := bstep (se 1 (by rfl) ⟨410480, by rfl⟩ : syracuseStep 547307 = 820961) B820961
theorem B9984647 : Blo 215810 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B5630417 : Blo 215810 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B1109375 : Blo 215810 1109375 := bstep (se 1 (by rfl) ⟨832031, by rfl⟩ : syracuseStep 1109375 = 1664063) B1664063
theorem B324071 : Blo 215810 324071 := bstep (se 1 (by rfl) ⟨243053, by rfl⟩ : syracuseStep 324071 = 486107) B486107
theorem B324767 : Blo 215810 324767 := bstep (se 1 (by rfl) ⟨243575, by rfl⟩ : syracuseStep 324767 = 487151) B487151
theorem B325151 : Blo 215810 325151 := bstep (se 1 (by rfl) ⟨243863, by rfl⟩ : syracuseStep 325151 = 487727) B487727
theorem B785543 : Blo 215810 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B5013011 : Blo 215810 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B5537483 : Blo 215810 5537483 := bstep (se 1 (by rfl) ⟨4153112, by rfl⟩ : syracuseStep 5537483 = 8306225) B8306225
theorem B327407 : Blo 215810 327407 := bstep (se 1 (by rfl) ⟨245555, by rfl⟩ : syracuseStep 327407 = 491111) B491111
theorem B327707 : Blo 215810 327707 := bstep (se 1 (by rfl) ⟨245780, by rfl⟩ : syracuseStep 327707 = 491561) B491561
theorem B1048735 : Blo 215810 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B327977 : Blo 215810 327977 := bstep (se 2 (by rfl) ⟨122991, by rfl⟩ : syracuseStep 327977 = 245983) B245983
theorem B328319 : Blo 215810 328319 := bstep (se 1 (by rfl) ⟨246239, by rfl⟩ : syracuseStep 328319 = 492479) B492479
theorem B754523 : Blo 215810 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B558647 : Blo 215810 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B329705 : Blo 215810 329705 := bstep (se 2 (by rfl) ⟨123639, by rfl⟩ : syracuseStep 329705 = 247279) B247279
theorem B659227 : Blo 215810 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B364871 : Blo 215810 364871 := bstep (se 1 (by rfl) ⟨273653, by rfl⟩ : syracuseStep 364871 = 547307) B547307
theorem B6656431 : Blo 215810 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B5576849 : Blo 215810 5576849 := bstep (se 2 (by rfl) ⟨2091318, by rfl⟩ : syracuseStep 5576849 = 4182637) B4182637
theorem B400879 : Blo 215810 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B728783 : Blo 215810 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B930143 : Blo 215810 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B1848905 : Blo 215810 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B705505 : Blo 215810 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B738557 : Blo 215810 738557 := bstep (se 3 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 738557 = 276959) B276959
theorem B3753611 : Blo 215810 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B739583 : Blo 215810 739583 := bstep (se 1 (by rfl) ⟨554687, by rfl⟩ : syracuseStep 739583 = 1109375) B1109375
theorem B216047 : Blo 215810 216047 := bstep (se 1 (by rfl) ⟨162035, by rfl⟩ : syracuseStep 216047 = 324071) B324071
theorem B216511 : Blo 215810 216511 := bstep (se 1 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 216511 = 324767) B324767
theorem B216767 : Blo 215810 216767 := bstep (se 1 (by rfl) ⟨162575, by rfl⟩ : syracuseStep 216767 = 325151) B325151
theorem B316537 : Blo 215810 316537 := bstep (se 2 (by rfl) ⟨118701, by rfl⟩ : syracuseStep 316537 = 237403) B237403
theorem B3691655 : Blo 215810 3691655 := bstep (se 1 (by rfl) ⟨2768741, by rfl⟩ : syracuseStep 3691655 = 5537483) B5537483
theorem B218271 : Blo 215810 218271 := bstep (se 1 (by rfl) ⟨163703, by rfl⟩ : syracuseStep 218271 = 327407) B327407
theorem B415135 : Blo 215810 415135 := bstep (se 1 (by rfl) ⟨311351, by rfl⟩ : syracuseStep 415135 = 622703) B622703
theorem B219227 : Blo 215810 219227 := bstep (se 1 (by rfl) ⟨164420, by rfl⟩ : syracuseStep 219227 = 328841) B328841
theorem B13721237 : Blo 215810 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B2351699 : Blo 215810 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B2778583 : Blo 215810 2778583 := bstep (se 1 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 2778583 = 4167875) B4167875
theorem B616825 : Blo 215810 616825 := bstep (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) B462619
theorem B1666007 : Blo 215810 1666007 := bstep (se 1 (by rfl) ⟨1249505, by rfl⟩ : syracuseStep 1666007 = 2499011) B2499011
theorem B2094781 : Blo 215810 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B6322859 : Blo 215810 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B3342007 : Blo 215810 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B492371 : Blo 215810 492371 := bstep (se 1 (by rfl) ⟨369278, by rfl⟩ : syracuseStep 492371 = 738557) B738557
theorem B493055 : Blo 215810 493055 := bstep (se 1 (by rfl) ⟨369791, by rfl⟩ : syracuseStep 493055 = 739583) B739583
theorem B3704777 : Blo 215810 3704777 := bstep (se 2 (by rfl) ⟨1389291, by rfl⟩ : syracuseStep 3704777 = 2778583) B2778583
theorem B822433 : Blo 215810 822433 := bstep (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) B616825
theorem B2461103 : Blo 215810 2461103 := bstep (se 1 (by rfl) ⟨1845827, by rfl⟩ : syracuseStep 2461103 = 3691655) B3691655
theorem B9147491 : Blo 215810 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B2793041 : Blo 215810 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B2138021 : Blo 215810 2138021 := bstep (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) B400879
theorem B503015 : Blo 215810 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B372431 : Blo 215810 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B2502407 : Blo 215810 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B243247 : Blo 215810 243247 := bstep (se 1 (by rfl) ⟨182435, by rfl⟩ : syracuseStep 243247 = 364871) B364871
theorem B3717899 : Blo 215810 3717899 := bstep (se 1 (by rfl) ⟨2788424, by rfl⟩ : syracuseStep 3717899 = 5576849) B5576849
theorem B1688197 : Blo 215810 1688197 := bstep (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) B316537
theorem B1232603 : Blo 215810 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B4215239 : Blo 215810 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B218471 : Blo 215810 218471 := bstep (se 1 (by rfl) ⟨163853, by rfl⟩ : syracuseStep 218471 = 327707) B327707
theorem B218651 : Blo 215810 218651 := bstep (se 1 (by rfl) ⟨163988, by rfl⟩ : syracuseStep 218651 = 327977) B327977
theorem B1398313 : Blo 215810 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B218879 : Blo 215810 218879 := bstep (se 1 (by rfl) ⟨164159, by rfl⟩ : syracuseStep 218879 = 328319) B328319
theorem B940673 : Blo 215810 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B219803 : Blo 215810 219803 := bstep (se 1 (by rfl) ⟨164852, by rfl⟩ : syracuseStep 219803 = 329705) B329705
theorem B878969 : Blo 215810 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B485855 : Blo 215810 485855 := bstep (se 1 (by rfl) ⟨364391, by rfl⟩ : syracuseStep 485855 = 728783) B728783
theorem B1567799 : Blo 215810 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B8875241 : Blo 215810 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B553513 : Blo 215810 553513 := bstep (se 2 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 553513 = 415135) B415135
theorem B1110671 : Blo 215810 1110671 := bstep (se 1 (by rfl) ⟨833003, by rfl⟩ : syracuseStep 1110671 = 1666007) B1666007
theorem B620095 : Blo 215810 620095 := bstep (se 1 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 620095 = 930143) B930143
theorem B4456009 : Blo 215810 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B328247 : Blo 215810 328247 := bstep (se 1 (by rfl) ⟨246185, by rfl⟩ : syracuseStep 328247 = 492371) B492371
theorem B328703 : Blo 215810 328703 := bstep (se 1 (by rfl) ⟨246527, by rfl⟩ : syracuseStep 328703 = 493055) B493055
theorem B1640735 : Blo 215810 1640735 := bstep (se 1 (by rfl) ⟨1230551, by rfl⟩ : syracuseStep 1640735 = 2461103) B2461103
theorem B821735 : Blo 215810 821735 := bstep (se 1 (by rfl) ⟨616301, by rfl⟩ : syracuseStep 821735 = 1232603) B1232603
theorem B6098327 : Blo 215810 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B627115 : Blo 215810 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B826793 : Blo 215810 826793 := bstep (se 2 (by rfl) ⟨310047, by rfl⟩ : syracuseStep 826793 = 620095) B620095
theorem B5941345 : Blo 215810 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B2469851 : Blo 215810 2469851 := bstep (se 1 (by rfl) ⟨1852388, by rfl⟩ : syracuseStep 2469851 = 3704777) B3704777
theorem B1096577 : Blo 215810 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B1425347 : Blo 215810 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B738017 : Blo 215810 738017 := bstep (se 2 (by rfl) ⟨276756, by rfl⟩ : syracuseStep 738017 = 553513) B553513
theorem B2343917 : Blo 215810 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B5916827 : Blo 215810 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B248287 : Blo 215810 248287 := bstep (se 1 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 248287 = 372431) B372431
theorem B740447 : Blo 215810 740447 := bstep (se 1 (by rfl) ⟨555335, by rfl⟩ : syracuseStep 740447 = 1110671) B1110671
theorem B2478599 : Blo 215810 2478599 := bstep (se 1 (by rfl) ⟨1858949, by rfl⟩ : syracuseStep 2478599 = 3717899) B3717899
theorem B2250929 : Blo 215810 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B2810159 : Blo 215810 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B1862027 : Blo 215810 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B323903 : Blo 215810 323903 := bstep (se 1 (by rfl) ⟨242927, by rfl⟩ : syracuseStep 323903 = 485855) B485855
theorem B1045199 : Blo 215810 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B1864417 : Blo 215810 1864417 := bstep (se 2 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 1864417 = 1398313) B1398313
theorem B324329 : Blo 215810 324329 := bstep (se 2 (by rfl) ⟨121623, by rfl⟩ : syracuseStep 324329 = 243247) B243247
theorem B1668271 : Blo 215810 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B1341373 : Blo 215810 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B492011 : Blo 215810 492011 := bstep (se 1 (by rfl) ⟨369008, by rfl⟩ : syracuseStep 492011 = 738017) B738017
theorem B493631 : Blo 215810 493631 := bstep (se 1 (by rfl) ⟨370223, by rfl⟩ : syracuseStep 493631 = 740447) B740447
theorem B4065551 : Blo 215810 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B331049 : Blo 215810 331049 := bstep (se 2 (by rfl) ⟨124143, by rfl⟩ : syracuseStep 331049 = 248287) B248287
theorem B1873439 : Blo 215810 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B1646567 : Blo 215810 1646567 := bstep (se 1 (by rfl) ⟨1234925, by rfl⟩ : syracuseStep 1646567 = 2469851) B2469851
theorem B696799 : Blo 215810 696799 := bstep (se 1 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 696799 = 1045199) B1045199
theorem B731051 : Blo 215810 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B3944551 : Blo 215810 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B1093823 : Blo 215810 1093823 := bstep (se 1 (by rfl) ⟨820367, by rfl⟩ : syracuseStep 1093823 = 1640735) B1640735
theorem B1652399 : Blo 215810 1652399 := bstep (se 1 (by rfl) ⟨1239299, by rfl⟩ : syracuseStep 1652399 = 2478599) B2478599
theorem B836153 : Blo 215810 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B1788497 : Blo 215810 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B215935 : Blo 215810 215935 := bstep (se 1 (by rfl) ⟨161951, by rfl⟩ : syracuseStep 215935 = 323903) B323903
theorem B216219 : Blo 215810 216219 := bstep (se 1 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 216219 = 324329) B324329
theorem B218831 : Blo 215810 218831 := bstep (se 1 (by rfl) ⟨164123, by rfl⟩ : syracuseStep 218831 = 328247) B328247
theorem B1562611 : Blo 215810 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B219135 : Blo 215810 219135 := bstep (se 1 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 219135 = 328703) B328703
theorem B547823 : Blo 215810 547823 := bstep (se 1 (by rfl) ⟨410867, by rfl⟩ : syracuseStep 547823 = 821735) B821735
theorem B7921793 : Blo 215810 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B1500619 : Blo 215810 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B551195 : Blo 215810 551195 := bstep (se 1 (by rfl) ⟨413396, by rfl⟩ : syracuseStep 551195 = 826793) B826793
theorem B2485889 : Blo 215810 2485889 := bstep (se 2 (by rfl) ⟨932208, by rfl⟩ : syracuseStep 2485889 = 1864417) B1864417
theorem B2224361 : Blo 215810 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B1241351 : Blo 215810 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B950231 : Blo 215810 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B328007 : Blo 215810 328007 := bstep (se 1 (by rfl) ⟨246005, by rfl⟩ : syracuseStep 328007 = 492011) B492011
theorem B557435 : Blo 215810 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B329087 : Blo 215810 329087 := bstep (se 1 (by rfl) ⟨246815, by rfl⟩ : syracuseStep 329087 = 493631) B493631
theorem B2000825 : Blo 215810 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B1248959 : Blo 215810 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B365215 : Blo 215810 365215 := bstep (se 1 (by rfl) ⟨273911, by rfl⟩ : syracuseStep 365215 = 547823) B547823
theorem B5281195 : Blo 215810 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B367463 : Blo 215810 367463 := bstep (se 1 (by rfl) ⟨275597, by rfl⟩ : syracuseStep 367463 = 551195) B551195
theorem B729215 : Blo 215810 729215 := bstep (se 1 (by rfl) ⟨546911, by rfl⟩ : syracuseStep 729215 = 1093823) B1093823
theorem B1482907 : Blo 215810 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B827567 : Blo 215810 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B2533949 : Blo 215810 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B929065 : Blo 215810 929065 := bstep (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) B696799
theorem B1192331 : Blo 215810 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B1097711 : Blo 215810 1097711 := bstep (se 1 (by rfl) ⟨823283, by rfl⟩ : syracuseStep 1097711 = 1646567) B1646567
theorem B5259401 : Blo 215810 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B1657259 : Blo 215810 1657259 := bstep (se 1 (by rfl) ⟨1242944, by rfl⟩ : syracuseStep 1657259 = 2485889) B2485889
theorem B2083481 : Blo 215810 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B1101599 : Blo 215810 1101599 := bstep (se 1 (by rfl) ⟨826199, by rfl⟩ : syracuseStep 1101599 = 1652399) B1652399
theorem B2710367 : Blo 215810 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B220699 : Blo 215810 220699 := bstep (se 1 (by rfl) ⟨165524, by rfl⟩ : syracuseStep 220699 = 331049) B331049
theorem B487367 : Blo 215810 487367 := bstep (se 1 (by rfl) ⟨365525, by rfl⟩ : syracuseStep 487367 = 731051) B731051
theorem B3506267 : Blo 215810 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B1806911 : Blo 215810 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B794887 : Blo 215810 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B731807 : Blo 215810 731807 := bstep (se 1 (by rfl) ⟨548855, by rfl⟩ : syracuseStep 731807 = 1097711) B1097711
theorem B1977209 : Blo 215810 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B371623 : Blo 215810 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B1388987 : Blo 215810 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B832639 : Blo 215810 832639 := bstep (se 1 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 832639 = 1248959) B1248959
theorem B734399 : Blo 215810 734399 := bstep (se 1 (by rfl) ⟨550799, by rfl⟩ : syracuseStep 734399 = 1101599) B1101599
theorem B244975 : Blo 215810 244975 := bstep (se 1 (by rfl) ⟨183731, by rfl⟩ : syracuseStep 244975 = 367463) B367463
theorem B1689299 : Blo 215810 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B218671 : Blo 215810 218671 := bstep (se 1 (by rfl) ⟨164003, by rfl⟩ : syracuseStep 218671 = 328007) B328007
theorem B219391 : Blo 215810 219391 := bstep (se 1 (by rfl) ⟨164543, by rfl⟩ : syracuseStep 219391 = 329087) B329087
theorem B1333883 : Blo 215810 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B1104839 : Blo 215810 1104839 := bstep (se 1 (by rfl) ⟨828629, by rfl⟩ : syracuseStep 1104839 = 1657259) B1657259
theorem B1238753 : Blo 215810 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B486143 : Blo 215810 486143 := bstep (se 1 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 486143 = 729215) B729215
theorem B551711 : Blo 215810 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B486953 : Blo 215810 486953 := bstep (se 2 (by rfl) ⟨182607, by rfl⟩ : syracuseStep 486953 = 365215) B365215
theorem B7041593 : Blo 215810 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B324911 : Blo 215810 324911 := bstep (se 1 (by rfl) ⟨243683, by rfl⟩ : syracuseStep 324911 = 487367) B487367
theorem B294265 : Blo 215810 294265 := bstep (se 2 (by rfl) ⟨110349, by rfl⟩ : syracuseStep 294265 = 220699) B220699
theorem B18777581 : Blo 215810 18777581 := bstep (se 3 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 18777581 = 7041593) B7041593
theorem B495497 : Blo 215810 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B889255 : Blo 215810 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B825835 : Blo 215810 825835 := bstep (se 1 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 825835 = 1238753) B1238753
theorem B367807 : Blo 215810 367807 := bstep (se 1 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 367807 = 551711) B551711
theorem B1318139 : Blo 215810 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B925991 : Blo 215810 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B2337511 : Blo 215810 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B1126199 : Blo 215810 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B4239397 : Blo 215810 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B736559 : Blo 215810 736559 := bstep (se 1 (by rfl) ⟨552419, by rfl⟩ : syracuseStep 736559 = 1104839) B1104839
theorem B216607 : Blo 215810 216607 := bstep (se 1 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 216607 = 324911) B324911
theorem B1204607 : Blo 215810 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B1110185 : Blo 215810 1110185 := bstep (se 2 (by rfl) ⟨416319, by rfl⟩ : syracuseStep 1110185 = 832639) B832639
theorem B487871 : Blo 215810 487871 := bstep (se 1 (by rfl) ⟨365903, by rfl⟩ : syracuseStep 487871 = 731807) B731807
theorem B324095 : Blo 215810 324095 := bstep (se 1 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 324095 = 486143) B486143
theorem B324635 : Blo 215810 324635 := bstep (se 1 (by rfl) ⟨243476, by rfl⟩ : syracuseStep 324635 = 486953) B486953
theorem B489599 : Blo 215810 489599 := bstep (se 1 (by rfl) ⟨367199, by rfl⟩ : syracuseStep 489599 = 734399) B734399
theorem B326633 : Blo 215810 326633 := bstep (se 2 (by rfl) ⟨122487, by rfl⟩ : syracuseStep 326633 = 244975) B244975
theorem B392353 : Blo 215810 392353 := bstep (se 2 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 392353 = 294265) B294265
theorem B22610117 : Blo 215810 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B12518387 : Blo 215810 12518387 := bstep (se 1 (by rfl) ⟨9388790, by rfl⟩ : syracuseStep 12518387 = 18777581) B18777581
theorem B3116681 : Blo 215810 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B1185673 : Blo 215810 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B1321325 : Blo 215810 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B803071 : Blo 215810 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B740123 : Blo 215810 740123 := bstep (se 1 (by rfl) ⟨555092, by rfl⟩ : syracuseStep 740123 = 1110185) B1110185
theorem B216063 : Blo 215810 216063 := bstep (se 1 (by rfl) ⟨162047, by rfl⟩ : syracuseStep 216063 = 324095) B324095
theorem B1101113 : Blo 215810 1101113 := bstep (se 2 (by rfl) ⟨412917, by rfl⟩ : syracuseStep 1101113 = 825835) B825835
theorem B216423 : Blo 215810 216423 := bstep (se 1 (by rfl) ⟨162317, by rfl⟩ : syracuseStep 216423 = 324635) B324635
theorem B217755 : Blo 215810 217755 := bstep (se 1 (by rfl) ⟨163316, by rfl⟩ : syracuseStep 217755 = 326633) B326633
theorem B878759 : Blo 215810 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B617327 : Blo 215810 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B2092549 : Blo 215810 2092549 := bstep (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) B392353
theorem B750799 : Blo 215810 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B325247 : Blo 215810 325247 := bstep (se 1 (by rfl) ⟨243935, by rfl⟩ : syracuseStep 325247 = 487871) B487871
theorem B326399 : Blo 215810 326399 := bstep (se 1 (by rfl) ⟨244799, by rfl⟩ : syracuseStep 326399 = 489599) B489599
theorem B490409 : Blo 215810 490409 := bstep (se 2 (by rfl) ⟨183903, by rfl⟩ : syracuseStep 490409 = 367807) B367807
theorem B491039 : Blo 215810 491039 := bstep (se 1 (by rfl) ⟨368279, by rfl⟩ : syracuseStep 491039 = 736559) B736559
theorem B60293645 : Blo 215810 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B493415 : Blo 215810 493415 := bstep (se 1 (by rfl) ⟨370061, by rfl⟩ : syracuseStep 493415 = 740123) B740123
theorem B2790065 : Blo 215810 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B4004261 : Blo 215810 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B1580897 : Blo 215810 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B734075 : Blo 215810 734075 := bstep (se 1 (by rfl) ⟨550556, by rfl⟩ : syracuseStep 734075 = 1101113) B1101113
theorem B2077787 : Blo 215810 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B411551 : Blo 215810 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B216831 : Blo 215810 216831 := bstep (se 1 (by rfl) ⟨162623, by rfl⟩ : syracuseStep 216831 = 325247) B325247
theorem B217599 : Blo 215810 217599 := bstep (se 1 (by rfl) ⟨163199, by rfl⟩ : syracuseStep 217599 = 326399) B326399
theorem B1070761 : Blo 215810 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B8345591 : Blo 215810 8345591 := bstep (se 1 (by rfl) ⟨6259193, by rfl⟩ : syracuseStep 8345591 = 12518387) B12518387
theorem B585839 : Blo 215810 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B880883 : Blo 215810 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B326939 : Blo 215810 326939 := bstep (se 1 (by rfl) ⟨245204, by rfl⟩ : syracuseStep 326939 = 490409) B490409
theorem B327359 : Blo 215810 327359 := bstep (se 1 (by rfl) ⟨245519, by rfl⟩ : syracuseStep 327359 = 491039) B491039
theorem B328943 : Blo 215810 328943 := bstep (se 1 (by rfl) ⟨246707, by rfl⟩ : syracuseStep 328943 = 493415) B493415
theorem B1053931 : Blo 215810 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B1385191 : Blo 215810 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B274367 : Blo 215810 274367 := bstep (se 1 (by rfl) ⟨205775, by rfl⟩ : syracuseStep 274367 = 411551) B411551
theorem B2669507 : Blo 215810 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B1427681 : Blo 215810 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B217959 : Blo 215810 217959 := bstep (se 1 (by rfl) ⟨163469, by rfl⟩ : syracuseStep 217959 = 326939) B326939
theorem B218239 : Blo 215810 218239 := bstep (se 1 (by rfl) ⟨163679, by rfl⟩ : syracuseStep 218239 = 327359) B327359
theorem B1562237 : Blo 215810 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B40195763 : Blo 215810 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1860043 : Blo 215810 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B5563727 : Blo 215810 5563727 := bstep (se 1 (by rfl) ⟨4172795, by rfl⟩ : syracuseStep 5563727 = 8345591) B8345591
theorem B587255 : Blo 215810 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B489383 : Blo 215810 489383 := bstep (se 1 (by rfl) ⟨367037, by rfl⟩ : syracuseStep 489383 = 734075) B734075
theorem B951787 : Blo 215810 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B3709151 : Blo 215810 3709151 := bstep (se 1 (by rfl) ⟨2781863, by rfl⟩ : syracuseStep 3709151 = 5563727) B5563727
theorem B1779671 : Blo 215810 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B731645 : Blo 215810 731645 := bstep (se 3 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 731645 = 274367) B274367
theorem B1846921 : Blo 215810 1846921 := bstep (se 2 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 1846921 = 1385191) B1385191
theorem B2480057 : Blo 215810 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B219295 : Blo 215810 219295 := bstep (se 1 (by rfl) ⟨164471, by rfl⟩ : syracuseStep 219295 = 328943) B328943
theorem B1041491 : Blo 215810 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B26797175 : Blo 215810 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1566013 : Blo 215810 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B1405241 : Blo 215810 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B326255 : Blo 215810 326255 := bstep (se 1 (by rfl) ⟨244691, by rfl⟩ : syracuseStep 326255 = 489383) B489383
theorem B2462561 : Blo 215810 2462561 := bstep (se 2 (by rfl) ⟨923460, by rfl⟩ : syracuseStep 2462561 = 1846921) B1846921
theorem B694327 : Blo 215810 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B17864783 : Blo 215810 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B1653371 : Blo 215810 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B2472767 : Blo 215810 2472767 := bstep (se 1 (by rfl) ⟨1854575, by rfl⟩ : syracuseStep 2472767 = 3709151) B3709151
theorem B936827 : Blo 215810 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B217503 : Blo 215810 217503 := bstep (se 1 (by rfl) ⟨163127, by rfl⟩ : syracuseStep 217503 = 326255) B326255
theorem B2088017 : Blo 215810 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B1269049 : Blo 215810 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B4745789 : Blo 215810 4745789 := bstep (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) B1779671
theorem B487763 : Blo 215810 487763 := bstep (se 1 (by rfl) ⟨365822, by rfl⟩ : syracuseStep 487763 = 731645) B731645
theorem B624551 : Blo 215810 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B1641707 : Blo 215810 1641707 := bstep (se 1 (by rfl) ⟨1231280, by rfl⟩ : syracuseStep 1641707 = 2462561) B2462561
theorem B925769 : Blo 215810 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B1648511 : Blo 215810 1648511 := bstep (se 1 (by rfl) ⟨1236383, by rfl⟩ : syracuseStep 1648511 = 2472767) B2472767
theorem B11909855 : Blo 215810 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B1392011 : Blo 215810 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B3163859 : Blo 215810 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B1692065 : Blo 215810 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1102247 : Blo 215810 1102247 := bstep (se 1 (by rfl) ⟨826685, by rfl⟩ : syracuseStep 1102247 = 1653371) B1653371
theorem B325175 : Blo 215810 325175 := bstep (se 1 (by rfl) ⟨243881, by rfl⟩ : syracuseStep 325175 = 487763) B487763
theorem B7939903 : Blo 215810 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B928007 : Blo 215810 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B2109239 : Blo 215810 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B1094471 : Blo 215810 1094471 := bstep (se 1 (by rfl) ⟨820853, by rfl⟩ : syracuseStep 1094471 = 1641707) B1641707
theorem B1128043 : Blo 215810 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B734831 : Blo 215810 734831 := bstep (se 1 (by rfl) ⟨551123, by rfl⟩ : syracuseStep 734831 = 1102247) B1102247
theorem B1099007 : Blo 215810 1099007 := bstep (se 1 (by rfl) ⟨824255, by rfl⟩ : syracuseStep 1099007 = 1648511) B1648511
theorem B216783 : Blo 215810 216783 := bstep (se 1 (by rfl) ⟨162587, by rfl⟩ : syracuseStep 216783 = 325175) B325175
theorem B1665469 : Blo 215810 1665469 := bstep (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) B624551
theorem B617179 : Blo 215810 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B10586537 : Blo 215810 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B822905 : Blo 215810 822905 := bstep (se 2 (by rfl) ⟨308589, by rfl⟩ : syracuseStep 822905 = 617179) B617179
theorem B729647 : Blo 215810 729647 := bstep (se 1 (by rfl) ⟨547235, by rfl⟩ : syracuseStep 729647 = 1094471) B1094471
theorem B732671 : Blo 215810 732671 := bstep (se 1 (by rfl) ⟨549503, by rfl⟩ : syracuseStep 732671 = 1099007) B1099007
theorem B2220625 : Blo 215810 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B618671 : Blo 215810 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B1504057 : Blo 215810 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B1406159 : Blo 215810 1406159 := bstep (se 1 (by rfl) ⟨1054619, by rfl⟩ : syracuseStep 1406159 = 2109239) B2109239
theorem B489887 : Blo 215810 489887 := bstep (se 1 (by rfl) ⟨367415, by rfl⟩ : syracuseStep 489887 = 734831) B734831
theorem B2005409 : Blo 215810 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B2960833 : Blo 215810 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B7057691 : Blo 215810 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B412447 : Blo 215810 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B937439 : Blo 215810 937439 := bstep (se 1 (by rfl) ⟨703079, by rfl⟩ : syracuseStep 937439 = 1406159) B1406159
theorem B548603 : Blo 215810 548603 := bstep (se 1 (by rfl) ⟨411452, by rfl⟩ : syracuseStep 548603 = 822905) B822905
theorem B486431 : Blo 215810 486431 := bstep (se 1 (by rfl) ⟨364823, by rfl⟩ : syracuseStep 486431 = 729647) B729647
theorem B488447 : Blo 215810 488447 := bstep (se 1 (by rfl) ⟨366335, by rfl⟩ : syracuseStep 488447 = 732671) B732671
theorem B326591 : Blo 215810 326591 := bstep (se 1 (by rfl) ⟨244943, by rfl⟩ : syracuseStep 326591 = 489887) B489887
theorem B624959 : Blo 215810 624959 := bstep (se 1 (by rfl) ⟨468719, by rfl⟩ : syracuseStep 624959 = 937439) B937439
theorem B365735 : Blo 215810 365735 := bstep (se 1 (by rfl) ⟨274301, by rfl⟩ : syracuseStep 365735 = 548603) B548603
theorem B5347757 : Blo 215810 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B3947777 : Blo 215810 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B4705127 : Blo 215810 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B217727 : Blo 215810 217727 := bstep (se 1 (by rfl) ⟨163295, by rfl⟩ : syracuseStep 217727 = 326591) B326591
theorem B549929 : Blo 215810 549929 := bstep (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) B412447
theorem B324287 : Blo 215810 324287 := bstep (se 1 (by rfl) ⟨243215, by rfl⟩ : syracuseStep 324287 = 486431) B486431
theorem B325631 : Blo 215810 325631 := bstep (se 1 (by rfl) ⟨244223, by rfl⟩ : syracuseStep 325631 = 488447) B488447
theorem B366619 : Blo 215810 366619 := bstep (se 1 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 366619 = 549929) B549929
theorem B2631851 : Blo 215810 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B243823 : Blo 215810 243823 := bstep (se 1 (by rfl) ⟨182867, by rfl⟩ : syracuseStep 243823 = 365735) B365735
theorem B216191 : Blo 215810 216191 := bstep (se 1 (by rfl) ⟨162143, by rfl⟩ : syracuseStep 216191 = 324287) B324287
theorem B217087 : Blo 215810 217087 := bstep (se 1 (by rfl) ⟨162815, by rfl⟩ : syracuseStep 217087 = 325631) B325631
theorem B416639 : Blo 215810 416639 := bstep (se 1 (by rfl) ⟨312479, by rfl⟩ : syracuseStep 416639 = 624959) B624959
theorem B3136751 : Blo 215810 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B3565171 : Blo 215810 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B4753561 : Blo 215810 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B277759 : Blo 215810 277759 := bstep (se 1 (by rfl) ⟨208319, by rfl⟩ : syracuseStep 277759 = 416639) B416639
theorem B1754567 : Blo 215810 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B2091167 : Blo 215810 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B488825 : Blo 215810 488825 := bstep (se 2 (by rfl) ⟨183309, by rfl⟩ : syracuseStep 488825 = 366619) B366619
theorem B325097 : Blo 215810 325097 := bstep (se 2 (by rfl) ⟨121911, by rfl⟩ : syracuseStep 325097 = 243823) B243823
theorem B370345 : Blo 215810 370345 := bstep (se 2 (by rfl) ⟨138879, by rfl⟩ : syracuseStep 370345 = 277759) B277759
theorem B6338081 : Blo 215810 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B1394111 : Blo 215810 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B216731 : Blo 215810 216731 := bstep (se 1 (by rfl) ⟨162548, by rfl⟩ : syracuseStep 216731 = 325097) B325097
theorem B1169711 : Blo 215810 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B325883 : Blo 215810 325883 := bstep (se 1 (by rfl) ⟨244412, by rfl⟩ : syracuseStep 325883 = 488825) B488825
theorem B493793 : Blo 215810 493793 := bstep (se 2 (by rfl) ⟨185172, by rfl⟩ : syracuseStep 493793 = 370345) B370345
theorem B929407 : Blo 215810 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B217255 : Blo 215810 217255 := bstep (se 1 (by rfl) ⟨162941, by rfl⟩ : syracuseStep 217255 = 325883) B325883
theorem B779807 : Blo 215810 779807 := bstep (se 1 (by rfl) ⟨584855, by rfl⟩ : syracuseStep 779807 = 1169711) B1169711
theorem B4225387 : Blo 215810 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B329195 : Blo 215810 329195 := bstep (se 1 (by rfl) ⟨246896, by rfl⟩ : syracuseStep 329195 = 493793) B493793
theorem B1239209 : Blo 215810 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B519871 : Blo 215810 519871 := bstep (se 1 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 519871 = 779807) B779807
theorem B5633849 : Blo 215810 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B693161 : Blo 215810 693161 := bstep (se 2 (by rfl) ⟨259935, by rfl⟩ : syracuseStep 693161 = 519871) B519871
theorem B826139 : Blo 215810 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B3755899 : Blo 215810 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B219463 : Blo 215810 219463 := bstep (se 1 (by rfl) ⟨164597, by rfl⟩ : syracuseStep 219463 = 329195) B329195
theorem B462107 : Blo 215810 462107 := bstep (se 1 (by rfl) ⟨346580, by rfl⟩ : syracuseStep 462107 = 693161) B693161
theorem B550759 : Blo 215810 550759 := bstep (se 1 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 550759 = 826139) B826139
theorem B5007865 : Blo 215810 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B308071 : Blo 215810 308071 := bstep (se 1 (by rfl) ⟨231053, by rfl⟩ : syracuseStep 308071 = 462107) B462107
theorem B734345 : Blo 215810 734345 := bstep (se 2 (by rfl) ⟨275379, by rfl⟩ : syracuseStep 734345 = 550759) B550759
theorem B6677153 : Blo 215810 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B410761 : Blo 215810 410761 := bstep (se 2 (by rfl) ⟨154035, by rfl⟩ : syracuseStep 410761 = 308071) B308071
theorem B4451435 : Blo 215810 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B489563 : Blo 215810 489563 := bstep (se 1 (by rfl) ⟨367172, by rfl⟩ : syracuseStep 489563 = 734345) B734345
theorem B2967623 : Blo 215810 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B547681 : Blo 215810 547681 := bstep (se 2 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 547681 = 410761) B410761
theorem B326375 : Blo 215810 326375 := bstep (se 1 (by rfl) ⟨244781, by rfl⟩ : syracuseStep 326375 = 489563) B489563
theorem B730241 : Blo 215810 730241 := bstep (se 2 (by rfl) ⟨273840, by rfl⟩ : syracuseStep 730241 = 547681) B547681
theorem B1978415 : Blo 215810 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B217583 : Blo 215810 217583 := bstep (se 1 (by rfl) ⟨163187, by rfl⟩ : syracuseStep 217583 = 326375) B326375
theorem B1318943 : Blo 215810 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B486827 : Blo 215810 486827 := bstep (se 1 (by rfl) ⟨365120, by rfl⟩ : syracuseStep 486827 = 730241) B730241
theorem B879295 : Blo 215810 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B324551 : Blo 215810 324551 := bstep (se 1 (by rfl) ⟨243413, by rfl⟩ : syracuseStep 324551 = 486827) B486827
theorem B216367 : Blo 215810 216367 := bstep (se 1 (by rfl) ⟨162275, by rfl⟩ : syracuseStep 216367 = 324551) B324551
theorem B1172393 : Blo 215810 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B781595 : Blo 215810 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B521063 : Blo 215810 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B347375 : Blo 215810 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B231583 : Blo 215810 231583 := bstep (se 1 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 231583 = 347375) B347375
theorem B308777 : Blo 215810 308777 := bstep (se 2 (by rfl) ⟨115791, by rfl⟩ : syracuseStep 308777 = 231583) B231583
theorem B823405 : Blo 215810 823405 := bstep (se 3 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 823405 = 308777) B308777
theorem B1097873 : Blo 215810 1097873 := bstep (se 2 (by rfl) ⟨411702, by rfl⟩ : syracuseStep 1097873 = 823405) B823405
theorem B731915 : Blo 215810 731915 := bstep (se 1 (by rfl) ⟨548936, by rfl⟩ : syracuseStep 731915 = 1097873) B1097873
theorem B487943 : Blo 215810 487943 := bstep (se 1 (by rfl) ⟨365957, by rfl⟩ : syracuseStep 487943 = 731915) B731915
theorem B325295 : Blo 215810 325295 := bstep (se 1 (by rfl) ⟨243971, by rfl⟩ : syracuseStep 325295 = 487943) B487943
theorem B216863 : Blo 215810 216863 := bstep (se 1 (by rfl) ⟨162647, by rfl⟩ : syracuseStep 216863 = 325295) B325295

theorem C0 (j : ℕ) (h1 : 53952 ≤ j) (h2 : j ≤ 54651) : Blo 215810 (4 * j + 3) := by
  interval_cases j
  · exact B215811
  · exact B215815
  · exact B215819
  · exact B215823
  · exact B215827
  · exact B215831
  · exact B215835
  · exact B215839
  · exact B215843
  · exact B215847
  · exact B215851
  · exact B215855
  · exact B215859
  · exact B215863
  · exact B215867
  · exact B215871
  · exact B215875
  · exact B215879
  · exact B215883
  · exact B215887
  · exact B215891
  · exact B215895
  · exact B215899
  · exact B215903
  · exact B215907
  · exact B215911
  · exact B215915
  · exact B215919
  · exact B215923
  · exact B215927
  · exact B215931
  · exact B215935
  · exact B215939
  · exact B215943
  · exact B215947
  · exact B215951
  · exact B215955
  · exact B215959
  · exact B215963
  · exact B215967
  · exact B215971
  · exact B215975
  · exact B215979
  · exact B215983
  · exact B215987
  · exact B215991
  · exact B215995
  · exact B215999
  · exact B216003
  · exact B216007
  · exact B216011
  · exact B216015
  · exact B216019
  · exact B216023
  · exact B216027
  · exact B216031
  · exact B216035
  · exact B216039
  · exact B216043
  · exact B216047
  · exact B216051
  · exact B216055
  · exact B216059
  · exact B216063
  · exact B216067
  · exact B216071
  · exact B216075
  · exact B216079
  · exact B216083
  · exact B216087
  · exact B216091
  · exact B216095
  · exact B216099
  · exact B216103
  · exact B216107
  · exact B216111
  · exact B216115
  · exact B216119
  · exact B216123
  · exact B216127
  · exact B216131
  · exact B216135
  · exact B216139
  · exact B216143
  · exact B216147
  · exact B216151
  · exact B216155
  · exact B216159
  · exact B216163
  · exact B216167
  · exact B216171
  · exact B216175
  · exact B216179
  · exact B216183
  · exact B216187
  · exact B216191
  · exact B216195
  · exact B216199
  · exact B216203
  · exact B216207
  · exact B216211
  · exact B216215
  · exact B216219
  · exact B216223
  · exact B216227
  · exact B216231
  · exact B216235
  · exact B216239
  · exact B216243
  · exact B216247
  · exact B216251
  · exact B216255
  · exact B216259
  · exact B216263
  · exact B216267
  · exact B216271
  · exact B216275
  · exact B216279
  · exact B216283
  · exact B216287
  · exact B216291
  · exact B216295
  · exact B216299
  · exact B216303
  · exact B216307
  · exact B216311
  · exact B216315
  · exact B216319
  · exact B216323
  · exact B216327
  · exact B216331
  · exact B216335
  · exact B216339
  · exact B216343
  · exact B216347
  · exact B216351
  · exact B216355
  · exact B216359
  · exact B216363
  · exact B216367
  · exact B216371
  · exact B216375
  · exact B216379
  · exact B216383
  · exact B216387
  · exact B216391
  · exact B216395
  · exact B216399
  · exact B216403
  · exact B216407
  · exact B216411
  · exact B216415
  · exact B216419
  · exact B216423
  · exact B216427
  · exact B216431
  · exact B216435
  · exact B216439
  · exact B216443
  · exact B216447
  · exact B216451
  · exact B216455
  · exact B216459
  · exact B216463
  · exact B216467
  · exact B216471
  · exact B216475
  · exact B216479
  · exact B216483
  · exact B216487
  · exact B216491
  · exact B216495
  · exact B216499
  · exact B216503
  · exact B216507
  · exact B216511
  · exact B216515
  · exact B216519
  · exact B216523
  · exact B216527
  · exact B216531
  · exact B216535
  · exact B216539
  · exact B216543
  · exact B216547
  · exact B216551
  · exact B216555
  · exact B216559
  · exact B216563
  · exact B216567
  · exact B216571
  · exact B216575
  · exact B216579
  · exact B216583
  · exact B216587
  · exact B216591
  · exact B216595
  · exact B216599
  · exact B216603
  · exact B216607
  · exact B216611
  · exact B216615
  · exact B216619
  · exact B216623
  · exact B216627
  · exact B216631
  · exact B216635
  · exact B216639
  · exact B216643
  · exact B216647
  · exact B216651
  · exact B216655
  · exact B216659
  · exact B216663
  · exact B216667
  · exact B216671
  · exact B216675
  · exact B216679
  · exact B216683
  · exact B216687
  · exact B216691
  · exact B216695
  · exact B216699
  · exact B216703
  · exact B216707
  · exact B216711
  · exact B216715
  · exact B216719
  · exact B216723
  · exact B216727
  · exact B216731
  · exact B216735
  · exact B216739
  · exact B216743
  · exact B216747
  · exact B216751
  · exact B216755
  · exact B216759
  · exact B216763
  · exact B216767
  · exact B216771
  · exact B216775
  · exact B216779
  · exact B216783
  · exact B216787
  · exact B216791
  · exact B216795
  · exact B216799
  · exact B216803
  · exact B216807
  · exact B216811
  · exact B216815
  · exact B216819
  · exact B216823
  · exact B216827
  · exact B216831
  · exact B216835
  · exact B216839
  · exact B216843
  · exact B216847
  · exact B216851
  · exact B216855
  · exact B216859
  · exact B216863
  · exact B216867
  · exact B216871
  · exact B216875
  · exact B216879
  · exact B216883
  · exact B216887
  · exact B216891
  · exact B216895
  · exact B216899
  · exact B216903
  · exact B216907
  · exact B216911
  · exact B216915
  · exact B216919
  · exact B216923
  · exact B216927
  · exact B216931
  · exact B216935
  · exact B216939
  · exact B216943
  · exact B216947
  · exact B216951
  · exact B216955
  · exact B216959
  · exact B216963
  · exact B216967
  · exact B216971
  · exact B216975
  · exact B216979
  · exact B216983
  · exact B216987
  · exact B216991
  · exact B216995
  · exact B216999
  · exact B217003
  · exact B217007
  · exact B217011
  · exact B217015
  · exact B217019
  · exact B217023
  · exact B217027
  · exact B217031
  · exact B217035
  · exact B217039
  · exact B217043
  · exact B217047
  · exact B217051
  · exact B217055
  · exact B217059
  · exact B217063
  · exact B217067
  · exact B217071
  · exact B217075
  · exact B217079
  · exact B217083
  · exact B217087
  · exact B217091
  · exact B217095
  · exact B217099
  · exact B217103
  · exact B217107
  · exact B217111
  · exact B217115
  · exact B217119
  · exact B217123
  · exact B217127
  · exact B217131
  · exact B217135
  · exact B217139
  · exact B217143
  · exact B217147
  · exact B217151
  · exact B217155
  · exact B217159
  · exact B217163
  · exact B217167
  · exact B217171
  · exact B217175
  · exact B217179
  · exact B217183
  · exact B217187
  · exact B217191
  · exact B217195
  · exact B217199
  · exact B217203
  · exact B217207
  · exact B217211
  · exact B217215
  · exact B217219
  · exact B217223
  · exact B217227
  · exact B217231
  · exact B217235
  · exact B217239
  · exact B217243
  · exact B217247
  · exact B217251
  · exact B217255
  · exact B217259
  · exact B217263
  · exact B217267
  · exact B217271
  · exact B217275
  · exact B217279
  · exact B217283
  · exact B217287
  · exact B217291
  · exact B217295
  · exact B217299
  · exact B217303
  · exact B217307
  · exact B217311
  · exact B217315
  · exact B217319
  · exact B217323
  · exact B217327
  · exact B217331
  · exact B217335
  · exact B217339
  · exact B217343
  · exact B217347
  · exact B217351
  · exact B217355
  · exact B217359
  · exact B217363
  · exact B217367
  · exact B217371
  · exact B217375
  · exact B217379
  · exact B217383
  · exact B217387
  · exact B217391
  · exact B217395
  · exact B217399
  · exact B217403
  · exact B217407
  · exact B217411
  · exact B217415
  · exact B217419
  · exact B217423
  · exact B217427
  · exact B217431
  · exact B217435
  · exact B217439
  · exact B217443
  · exact B217447
  · exact B217451
  · exact B217455
  · exact B217459
  · exact B217463
  · exact B217467
  · exact B217471
  · exact B217475
  · exact B217479
  · exact B217483
  · exact B217487
  · exact B217491
  · exact B217495
  · exact B217499
  · exact B217503
  · exact B217507
  · exact B217511
  · exact B217515
  · exact B217519
  · exact B217523
  · exact B217527
  · exact B217531
  · exact B217535
  · exact B217539
  · exact B217543
  · exact B217547
  · exact B217551
  · exact B217555
  · exact B217559
  · exact B217563
  · exact B217567
  · exact B217571
  · exact B217575
  · exact B217579
  · exact B217583
  · exact B217587
  · exact B217591
  · exact B217595
  · exact B217599
  · exact B217603
  · exact B217607
  · exact B217611
  · exact B217615
  · exact B217619
  · exact B217623
  · exact B217627
  · exact B217631
  · exact B217635
  · exact B217639
  · exact B217643
  · exact B217647
  · exact B217651
  · exact B217655
  · exact B217659
  · exact B217663
  · exact B217667
  · exact B217671
  · exact B217675
  · exact B217679
  · exact B217683
  · exact B217687
  · exact B217691
  · exact B217695
  · exact B217699
  · exact B217703
  · exact B217707
  · exact B217711
  · exact B217715
  · exact B217719
  · exact B217723
  · exact B217727
  · exact B217731
  · exact B217735
  · exact B217739
  · exact B217743
  · exact B217747
  · exact B217751
  · exact B217755
  · exact B217759
  · exact B217763
  · exact B217767
  · exact B217771
  · exact B217775
  · exact B217779
  · exact B217783
  · exact B217787
  · exact B217791
  · exact B217795
  · exact B217799
  · exact B217803
  · exact B217807
  · exact B217811
  · exact B217815
  · exact B217819
  · exact B217823
  · exact B217827
  · exact B217831
  · exact B217835
  · exact B217839
  · exact B217843
  · exact B217847
  · exact B217851
  · exact B217855
  · exact B217859
  · exact B217863
  · exact B217867
  · exact B217871
  · exact B217875
  · exact B217879
  · exact B217883
  · exact B217887
  · exact B217891
  · exact B217895
  · exact B217899
  · exact B217903
  · exact B217907
  · exact B217911
  · exact B217915
  · exact B217919
  · exact B217923
  · exact B217927
  · exact B217931
  · exact B217935
  · exact B217939
  · exact B217943
  · exact B217947
  · exact B217951
  · exact B217955
  · exact B217959
  · exact B217963
  · exact B217967
  · exact B217971
  · exact B217975
  · exact B217979
  · exact B217983
  · exact B217987
  · exact B217991
  · exact B217995
  · exact B217999
  · exact B218003
  · exact B218007
  · exact B218011
  · exact B218015
  · exact B218019
  · exact B218023
  · exact B218027
  · exact B218031
  · exact B218035
  · exact B218039
  · exact B218043
  · exact B218047
  · exact B218051
  · exact B218055
  · exact B218059
  · exact B218063
  · exact B218067
  · exact B218071
  · exact B218075
  · exact B218079
  · exact B218083
  · exact B218087
  · exact B218091
  · exact B218095
  · exact B218099
  · exact B218103
  · exact B218107
  · exact B218111
  · exact B218115
  · exact B218119
  · exact B218123
  · exact B218127
  · exact B218131
  · exact B218135
  · exact B218139
  · exact B218143
  · exact B218147
  · exact B218151
  · exact B218155
  · exact B218159
  · exact B218163
  · exact B218167
  · exact B218171
  · exact B218175
  · exact B218179
  · exact B218183
  · exact B218187
  · exact B218191
  · exact B218195
  · exact B218199
  · exact B218203
  · exact B218207
  · exact B218211
  · exact B218215
  · exact B218219
  · exact B218223
  · exact B218227
  · exact B218231
  · exact B218235
  · exact B218239
  · exact B218243
  · exact B218247
  · exact B218251
  · exact B218255
  · exact B218259
  · exact B218263
  · exact B218267
  · exact B218271
  · exact B218275
  · exact B218279
  · exact B218283
  · exact B218287
  · exact B218291
  · exact B218295
  · exact B218299
  · exact B218303
  · exact B218307
  · exact B218311
  · exact B218315
  · exact B218319
  · exact B218323
  · exact B218327
  · exact B218331
  · exact B218335
  · exact B218339
  · exact B218343
  · exact B218347
  · exact B218351
  · exact B218355
  · exact B218359
  · exact B218363
  · exact B218367
  · exact B218371
  · exact B218375
  · exact B218379
  · exact B218383
  · exact B218387
  · exact B218391
  · exact B218395
  · exact B218399
  · exact B218403
  · exact B218407
  · exact B218411
  · exact B218415
  · exact B218419
  · exact B218423
  · exact B218427
  · exact B218431
  · exact B218435
  · exact B218439
  · exact B218443
  · exact B218447
  · exact B218451
  · exact B218455
  · exact B218459
  · exact B218463
  · exact B218467
  · exact B218471
  · exact B218475
  · exact B218479
  · exact B218483
  · exact B218487
  · exact B218491
  · exact B218495
  · exact B218499
  · exact B218503
  · exact B218507
  · exact B218511
  · exact B218515
  · exact B218519
  · exact B218523
  · exact B218527
  · exact B218531
  · exact B218535
  · exact B218539
  · exact B218543
  · exact B218547
  · exact B218551
  · exact B218555
  · exact B218559
  · exact B218563
  · exact B218567
  · exact B218571
  · exact B218575
  · exact B218579
  · exact B218583
  · exact B218587
  · exact B218591
  · exact B218595
  · exact B218599
  · exact B218603
  · exact B218607

theorem C1 (j : ℕ) (h1 : 54652 ≤ j) (h2 : j ≤ 54951) : Blo 215810 (4 * j + 3) := by
  interval_cases j
  · exact B218611
  · exact B218615
  · exact B218619
  · exact B218623
  · exact B218627
  · exact B218631
  · exact B218635
  · exact B218639
  · exact B218643
  · exact B218647
  · exact B218651
  · exact B218655
  · exact B218659
  · exact B218663
  · exact B218667
  · exact B218671
  · exact B218675
  · exact B218679
  · exact B218683
  · exact B218687
  · exact B218691
  · exact B218695
  · exact B218699
  · exact B218703
  · exact B218707
  · exact B218711
  · exact B218715
  · exact B218719
  · exact B218723
  · exact B218727
  · exact B218731
  · exact B218735
  · exact B218739
  · exact B218743
  · exact B218747
  · exact B218751
  · exact B218755
  · exact B218759
  · exact B218763
  · exact B218767
  · exact B218771
  · exact B218775
  · exact B218779
  · exact B218783
  · exact B218787
  · exact B218791
  · exact B218795
  · exact B218799
  · exact B218803
  · exact B218807
  · exact B218811
  · exact B218815
  · exact B218819
  · exact B218823
  · exact B218827
  · exact B218831
  · exact B218835
  · exact B218839
  · exact B218843
  · exact B218847
  · exact B218851
  · exact B218855
  · exact B218859
  · exact B218863
  · exact B218867
  · exact B218871
  · exact B218875
  · exact B218879
  · exact B218883
  · exact B218887
  · exact B218891
  · exact B218895
  · exact B218899
  · exact B218903
  · exact B218907
  · exact B218911
  · exact B218915
  · exact B218919
  · exact B218923
  · exact B218927
  · exact B218931
  · exact B218935
  · exact B218939
  · exact B218943
  · exact B218947
  · exact B218951
  · exact B218955
  · exact B218959
  · exact B218963
  · exact B218967
  · exact B218971
  · exact B218975
  · exact B218979
  · exact B218983
  · exact B218987
  · exact B218991
  · exact B218995
  · exact B218999
  · exact B219003
  · exact B219007
  · exact B219011
  · exact B219015
  · exact B219019
  · exact B219023
  · exact B219027
  · exact B219031
  · exact B219035
  · exact B219039
  · exact B219043
  · exact B219047
  · exact B219051
  · exact B219055
  · exact B219059
  · exact B219063
  · exact B219067
  · exact B219071
  · exact B219075
  · exact B219079
  · exact B219083
  · exact B219087
  · exact B219091
  · exact B219095
  · exact B219099
  · exact B219103
  · exact B219107
  · exact B219111
  · exact B219115
  · exact B219119
  · exact B219123
  · exact B219127
  · exact B219131
  · exact B219135
  · exact B219139
  · exact B219143
  · exact B219147
  · exact B219151
  · exact B219155
  · exact B219159
  · exact B219163
  · exact B219167
  · exact B219171
  · exact B219175
  · exact B219179
  · exact B219183
  · exact B219187
  · exact B219191
  · exact B219195
  · exact B219199
  · exact B219203
  · exact B219207
  · exact B219211
  · exact B219215
  · exact B219219
  · exact B219223
  · exact B219227
  · exact B219231
  · exact B219235
  · exact B219239
  · exact B219243
  · exact B219247
  · exact B219251
  · exact B219255
  · exact B219259
  · exact B219263
  · exact B219267
  · exact B219271
  · exact B219275
  · exact B219279
  · exact B219283
  · exact B219287
  · exact B219291
  · exact B219295
  · exact B219299
  · exact B219303
  · exact B219307
  · exact B219311
  · exact B219315
  · exact B219319
  · exact B219323
  · exact B219327
  · exact B219331
  · exact B219335
  · exact B219339
  · exact B219343
  · exact B219347
  · exact B219351
  · exact B219355
  · exact B219359
  · exact B219363
  · exact B219367
  · exact B219371
  · exact B219375
  · exact B219379
  · exact B219383
  · exact B219387
  · exact B219391
  · exact B219395
  · exact B219399
  · exact B219403
  · exact B219407
  · exact B219411
  · exact B219415
  · exact B219419
  · exact B219423
  · exact B219427
  · exact B219431
  · exact B219435
  · exact B219439
  · exact B219443
  · exact B219447
  · exact B219451
  · exact B219455
  · exact B219459
  · exact B219463
  · exact B219467
  · exact B219471
  · exact B219475
  · exact B219479
  · exact B219483
  · exact B219487
  · exact B219491
  · exact B219495
  · exact B219499
  · exact B219503
  · exact B219507
  · exact B219511
  · exact B219515
  · exact B219519
  · exact B219523
  · exact B219527
  · exact B219531
  · exact B219535
  · exact B219539
  · exact B219543
  · exact B219547
  · exact B219551
  · exact B219555
  · exact B219559
  · exact B219563
  · exact B219567
  · exact B219571
  · exact B219575
  · exact B219579
  · exact B219583
  · exact B219587
  · exact B219591
  · exact B219595
  · exact B219599
  · exact B219603
  · exact B219607
  · exact B219611
  · exact B219615
  · exact B219619
  · exact B219623
  · exact B219627
  · exact B219631
  · exact B219635
  · exact B219639
  · exact B219643
  · exact B219647
  · exact B219651
  · exact B219655
  · exact B219659
  · exact B219663
  · exact B219667
  · exact B219671
  · exact B219675
  · exact B219679
  · exact B219683
  · exact B219687
  · exact B219691
  · exact B219695
  · exact B219699
  · exact B219703
  · exact B219707
  · exact B219711
  · exact B219715
  · exact B219719
  · exact B219723
  · exact B219727
  · exact B219731
  · exact B219735
  · exact B219739
  · exact B219743
  · exact B219747
  · exact B219751
  · exact B219755
  · exact B219759
  · exact B219763
  · exact B219767
  · exact B219771
  · exact B219775
  · exact B219779
  · exact B219783
  · exact B219787
  · exact B219791
  · exact B219795
  · exact B219799
  · exact B219803
  · exact B219807

theorem solution (m : ℕ) (hlo : 215810 ≤ m) (hhi : m ≤ 219810) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 53952 ≤ j := by omega
    have hj2 : j ≤ 54951 := by omega
    have hb : Blo 215810 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 54652 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
