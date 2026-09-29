-- Prove2me | solution 1 for syracuse_descends_range_1792097_1794097
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:47:51.487235+00:00
-- url     : https://prove2.me/submissions/ab0a844c-992a-4132-bb9c-80a819c97e44

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


theorem B1843205 : Blo 1792097 1843205 := bbase (se 4 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 1843205 = 345601) (by norm_num)
theorem B4538389 : Blo 1792097 4538389 := bbase (se 6 (by rfl) ⟨106368, by rfl⟩ : syracuseStep 4538389 = 212737) (by norm_num)
theorem B2269225 : Blo 1792097 2269225 := bbase (se 2 (by rfl) ⟨850959, by rfl⟩ : syracuseStep 2269225 = 1701919) (by norm_num)
theorem B4309109 : Blo 1792097 4309109 := bbase (se 5 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 4309109 = 403979) (by norm_num)
theorem B3883133 : Blo 1792097 3883133 := bbase (se 3 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 3883133 = 1456175) (by norm_num)
theorem B4538501 : Blo 1792097 4538501 := bbase (se 4 (by rfl) ⟨425484, by rfl⟩ : syracuseStep 4538501 = 850969) (by norm_num)
theorem B2269397 : Blo 1792097 2269397 := bbase (se 7 (by rfl) ⟨26594, by rfl⟩ : syracuseStep 2269397 = 53189) (by norm_num)
theorem B6054101 : Blo 1792097 6054101 := bbase (se 7 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 6054101 = 141893) (by norm_num)
theorem B6807797 : Blo 1792097 6807797 := bbase (se 5 (by rfl) ⟨319115, by rfl⟩ : syracuseStep 6807797 = 638231) (by norm_num)
theorem B2269453 : Blo 1792097 2269453 := bbase (se 3 (by rfl) ⟨425522, by rfl⟩ : syracuseStep 2269453 = 851045) (by norm_num)
theorem B4309309 : Blo 1792097 4309309 := bbase (se 3 (by rfl) ⟨807995, by rfl⟩ : syracuseStep 4309309 = 1615991) (by norm_num)
theorem B4538693 : Blo 1792097 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B2269549 : Blo 1792097 2269549 := bbase (se 3 (by rfl) ⟨425540, by rfl⟩ : syracuseStep 2269549 = 851081) (by norm_num)
theorem B2269721 : Blo 1792097 2269721 := bbase (se 2 (by rfl) ⟨851145, by rfl⟩ : syracuseStep 2269721 = 1702291) (by norm_num)
theorem B2269777 : Blo 1792097 2269777 := bbase (se 2 (by rfl) ⟨851166, by rfl⟩ : syracuseStep 2269777 = 1702333) (by norm_num)
theorem B6054533 : Blo 1792097 6054533 := bbase (se 4 (by rfl) ⟨567612, by rfl⟩ : syracuseStep 6054533 = 1135225) (by norm_num)
theorem B4539037 : Blo 1792097 4539037 := bbase (se 3 (by rfl) ⟨851069, by rfl⟩ : syracuseStep 4539037 = 1702139) (by norm_num)
theorem B2269873 : Blo 1792097 2269873 := bbase (se 2 (by rfl) ⟨851202, by rfl⟩ : syracuseStep 2269873 = 1702405) (by norm_num)
theorem B4203197 : Blo 1792097 4203197 := bbase (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) (by norm_num)
theorem B7660277 : Blo 1792097 7660277 := bbase (se 5 (by rfl) ⟨359075, by rfl⟩ : syracuseStep 7660277 = 718151) (by norm_num)
theorem B4539149 : Blo 1792097 4539149 := bbase (se 3 (by rfl) ⟨851090, by rfl⟩ : syracuseStep 4539149 = 1702181) (by norm_num)
theorem B3498773 : Blo 1792097 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B2155285 : Blo 1792097 2155285 := bbase (se 6 (by rfl) ⟨50514, by rfl⟩ : syracuseStep 2155285 = 101029) (by norm_num)
theorem B2270045 : Blo 1792097 2270045 := bbase (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) (by norm_num)
theorem B2016121 : Blo 1792097 2016121 := bbase (se 2 (by rfl) ⟨756045, by rfl⟩ : syracuseStep 2016121 = 1512091) (by norm_num)
theorem B2270101 : Blo 1792097 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B2016157 : Blo 1792097 2016157 := bbase (se 3 (by rfl) ⟨378029, by rfl⟩ : syracuseStep 2016157 = 756059) (by norm_num)
theorem B5104549 : Blo 1792097 5104549 := bbase (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) (by norm_num)
theorem B9077669 : Blo 1792097 9077669 := bbase (se 4 (by rfl) ⟨851031, by rfl⟩ : syracuseStep 9077669 = 1702063) (by norm_num)
theorem B5743541 : Blo 1792097 5743541 := bbase (se 5 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 5743541 = 538457) (by norm_num)
theorem B2016193 : Blo 1792097 2016193 := bbase (se 2 (by rfl) ⟨756072, by rfl⟩ : syracuseStep 2016193 = 1512145) (by norm_num)
theorem B4539341 : Blo 1792097 4539341 := bbase (se 3 (by rfl) ⟨851126, by rfl⟩ : syracuseStep 4539341 = 1702253) (by norm_num)
theorem B2016229 : Blo 1792097 2016229 := bbase (se 4 (by rfl) ⟨189021, by rfl⟩ : syracuseStep 2016229 = 378043) (by norm_num)
theorem B2270197 : Blo 1792097 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B2016265 : Blo 1792097 2016265 := bbase (se 2 (by rfl) ⟨756099, by rfl⟩ : syracuseStep 2016265 = 1512199) (by norm_num)
theorem B2016301 : Blo 1792097 2016301 := bbase (se 3 (by rfl) ⟨378056, by rfl⟩ : syracuseStep 2016301 = 756113) (by norm_num)
theorem B11486261 : Blo 1792097 11486261 := bbase (se 5 (by rfl) ⟨538418, by rfl⟩ : syracuseStep 11486261 = 1076837) (by norm_num)
theorem B6054965 : Blo 1792097 6054965 := bbase (se 5 (by rfl) ⟨283826, by rfl⟩ : syracuseStep 6054965 = 567653) (by norm_num)
theorem B2016337 : Blo 1792097 2016337 := bbase (se 2 (by rfl) ⟨756126, by rfl⟩ : syracuseStep 2016337 = 1512253) (by norm_num)
theorem B4310117 : Blo 1792097 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B2016373 : Blo 1792097 2016373 := bbase (se 5 (by rfl) ⟨94517, by rfl⟩ : syracuseStep 2016373 = 189035) (by norm_num)
theorem B2688149 : Blo 1792097 2688149 := bbase (se 6 (by rfl) ⟨63003, by rfl⟩ : syracuseStep 2688149 = 126007) (by norm_num)
theorem B2016409 : Blo 1792097 2016409 := bbase (se 2 (by rfl) ⟨756153, by rfl⟩ : syracuseStep 2016409 = 1512307) (by norm_num)
theorem B2270369 : Blo 1792097 2270369 := bbase (se 2 (by rfl) ⟨851388, by rfl⟩ : syracuseStep 2270369 = 1702777) (by norm_num)
theorem B2688173 : Blo 1792097 2688173 := bbase (se 3 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 2688173 = 1008065) (by norm_num)
theorem B2016445 : Blo 1792097 2016445 := bbase (se 3 (by rfl) ⟨378083, by rfl⟩ : syracuseStep 2016445 = 756167) (by norm_num)
theorem B2688197 : Blo 1792097 2688197 := bbase (se 4 (by rfl) ⟨252018, by rfl⟩ : syracuseStep 2688197 = 504037) (by norm_num)
theorem B2270425 : Blo 1792097 2270425 := bbase (se 2 (by rfl) ⟨851409, by rfl⟩ : syracuseStep 2270425 = 1702819) (by norm_num)
theorem B2688221 : Blo 1792097 2688221 := bbase (se 3 (by rfl) ⟨504041, by rfl⟩ : syracuseStep 2688221 = 1008083) (by norm_num)
theorem B2016481 : Blo 1792097 2016481 := bbase (se 2 (by rfl) ⟨756180, by rfl⟩ : syracuseStep 2016481 = 1512361) (by norm_num)
theorem B2688245 : Blo 1792097 2688245 := bbase (se 5 (by rfl) ⟨126011, by rfl⟩ : syracuseStep 2688245 = 252023) (by norm_num)
theorem B2016517 : Blo 1792097 2016517 := bbase (se 4 (by rfl) ⟨189048, by rfl⟩ : syracuseStep 2016517 = 378097) (by norm_num)
theorem B5178629 : Blo 1792097 5178629 := bbase (se 4 (by rfl) ⟨485496, by rfl⟩ : syracuseStep 5178629 = 970993) (by norm_num)
theorem B2688269 : Blo 1792097 2688269 := bbase (se 3 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 2688269 = 1008101) (by norm_num)
theorem B2688293 : Blo 1792097 2688293 := bbase (se 4 (by rfl) ⟨252027, by rfl⟩ : syracuseStep 2688293 = 504055) (by norm_num)
theorem B4539685 : Blo 1792097 4539685 := bbase (se 4 (by rfl) ⟨425595, by rfl⟩ : syracuseStep 4539685 = 851191) (by norm_num)
theorem B2016553 : Blo 1792097 2016553 := bbase (se 2 (by rfl) ⟨756207, by rfl⟩ : syracuseStep 2016553 = 1512415) (by norm_num)
theorem B2270521 : Blo 1792097 2270521 := bbase (se 2 (by rfl) ⟨851445, by rfl⟩ : syracuseStep 2270521 = 1702891) (by norm_num)
theorem B2688317 : Blo 1792097 2688317 := bbase (se 3 (by rfl) ⟨504059, by rfl⟩ : syracuseStep 2688317 = 1008119) (by norm_num)
theorem B2016589 : Blo 1792097 2016589 := bbase (se 3 (by rfl) ⟨378110, by rfl⟩ : syracuseStep 2016589 = 756221) (by norm_num)
theorem B2688341 : Blo 1792097 2688341 := bbase (se 12 (by rfl) ⟨984, by rfl⟩ : syracuseStep 2688341 = 1969) (by norm_num)
theorem B3024229 : Blo 1792097 3024229 := bbase (se 4 (by rfl) ⟨283521, by rfl⟩ : syracuseStep 3024229 = 567043) (by norm_num)
theorem B2688365 : Blo 1792097 2688365 := bbase (se 3 (by rfl) ⟨504068, by rfl⟩ : syracuseStep 2688365 = 1008137) (by norm_num)
theorem B2016625 : Blo 1792097 2016625 := bbase (se 2 (by rfl) ⟨756234, by rfl⟩ : syracuseStep 2016625 = 1512469) (by norm_num)
theorem B2688389 : Blo 1792097 2688389 := bbase (se 4 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 2688389 = 504073) (by norm_num)
theorem B2016661 : Blo 1792097 2016661 := bbase (se 6 (by rfl) ⟨47265, by rfl⟩ : syracuseStep 2016661 = 94531) (by norm_num)
theorem B6808981 : Blo 1792097 6808981 := bbase (se 6 (by rfl) ⟨159585, by rfl⟩ : syracuseStep 6808981 = 319171) (by norm_num)
theorem B4539797 : Blo 1792097 4539797 := bbase (se 6 (by rfl) ⟨106401, by rfl⟩ : syracuseStep 4539797 = 212803) (by norm_num)
theorem B2688413 : Blo 1792097 2688413 := bbase (se 3 (by rfl) ⟨504077, by rfl⟩ : syracuseStep 2688413 = 1008155) (by norm_num)
theorem B6464933 : Blo 1792097 6464933 := bbase (se 4 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 6464933 = 1212175) (by norm_num)
theorem B2688437 : Blo 1792097 2688437 := bbase (se 5 (by rfl) ⟨126020, by rfl⟩ : syracuseStep 2688437 = 252041) (by norm_num)
theorem B2016697 : Blo 1792097 2016697 := bbase (se 2 (by rfl) ⟨756261, by rfl⟩ : syracuseStep 2016697 = 1512523) (by norm_num)
theorem B3024317 : Blo 1792097 3024317 := bbase (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) (by norm_num)
theorem B2688461 : Blo 1792097 2688461 := bbase (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) (by norm_num)
theorem B2016733 : Blo 1792097 2016733 := bbase (se 3 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 2016733 = 756275) (by norm_num)
theorem B2688485 : Blo 1792097 2688485 := bbase (se 4 (by rfl) ⟨252045, by rfl⟩ : syracuseStep 2688485 = 504091) (by norm_num)
theorem B8177125 : Blo 1792097 8177125 := bbase (se 4 (by rfl) ⟨766605, by rfl⟩ : syracuseStep 8177125 = 1533211) (by norm_num)
theorem B2688509 : Blo 1792097 2688509 := bbase (se 3 (by rfl) ⟨504095, by rfl⟩ : syracuseStep 2688509 = 1008191) (by norm_num)
theorem B4089341 : Blo 1792097 4089341 := bbase (se 3 (by rfl) ⟨766751, by rfl⟩ : syracuseStep 4089341 = 1533503) (by norm_num)
theorem B2016769 : Blo 1792097 2016769 := bbase (se 2 (by rfl) ⟨756288, by rfl⟩ : syracuseStep 2016769 = 1512577) (by norm_num)
theorem B2688533 : Blo 1792097 2688533 := bbase (se 6 (by rfl) ⟨63012, by rfl⟩ : syracuseStep 2688533 = 126025) (by norm_num)
theorem B2016805 : Blo 1792097 2016805 := bbase (se 4 (by rfl) ⟨189075, by rfl⟩ : syracuseStep 2016805 = 378151) (by norm_num)
theorem B2688557 : Blo 1792097 2688557 := bbase (se 3 (by rfl) ⟨504104, by rfl⟩ : syracuseStep 2688557 = 1008209) (by norm_num)
theorem B3024445 : Blo 1792097 3024445 := bbase (se 3 (by rfl) ⟨567083, by rfl⟩ : syracuseStep 3024445 = 1134167) (by norm_num)
theorem B2688581 : Blo 1792097 2688581 := bbase (se 4 (by rfl) ⟨252054, by rfl⟩ : syracuseStep 2688581 = 504109) (by norm_num)
theorem B2016841 : Blo 1792097 2016841 := bbase (se 2 (by rfl) ⟨756315, by rfl⟩ : syracuseStep 2016841 = 1512631) (by norm_num)
theorem B4539989 : Blo 1792097 4539989 := bbase (se 8 (by rfl) ⟨26601, by rfl⟩ : syracuseStep 4539989 = 53203) (by norm_num)
theorem B11650645 : Blo 1792097 11650645 := bbase (se 8 (by rfl) ⟨68265, by rfl⟩ : syracuseStep 11650645 = 136531) (by norm_num)
theorem B2688605 : Blo 1792097 2688605 := bbase (se 3 (by rfl) ⟨504113, by rfl⟩ : syracuseStep 2688605 = 1008227) (by norm_num)
theorem B2016877 : Blo 1792097 2016877 := bbase (se 3 (by rfl) ⟨378164, by rfl⟩ : syracuseStep 2016877 = 756329) (by norm_num)
theorem B2688629 : Blo 1792097 2688629 := bbase (se 5 (by rfl) ⟨126029, by rfl⟩ : syracuseStep 2688629 = 252059) (by norm_num)
theorem B2688653 : Blo 1792097 2688653 := bbase (se 3 (by rfl) ⟨504122, by rfl⟩ : syracuseStep 2688653 = 1008245) (by norm_num)
theorem B2016913 : Blo 1792097 2016913 := bbase (se 2 (by rfl) ⟨756342, by rfl⟩ : syracuseStep 2016913 = 1512685) (by norm_num)
theorem B3024533 : Blo 1792097 3024533 := bbase (se 6 (by rfl) ⟨70887, by rfl⟩ : syracuseStep 3024533 = 141775) (by norm_num)
theorem B2688677 : Blo 1792097 2688677 := bbase (se 4 (by rfl) ⟨252063, by rfl⟩ : syracuseStep 2688677 = 504127) (by norm_num)
theorem B2016949 : Blo 1792097 2016949 := bbase (se 5 (by rfl) ⟨94544, by rfl⟩ : syracuseStep 2016949 = 189089) (by norm_num)
theorem B2688701 : Blo 1792097 2688701 := bbase (se 3 (by rfl) ⟨504131, by rfl⟩ : syracuseStep 2688701 = 1008263) (by norm_num)
theorem B6809285 : Blo 1792097 6809285 := bbase (se 4 (by rfl) ⟨638370, by rfl⟩ : syracuseStep 6809285 = 1276741) (by norm_num)
theorem B2688725 : Blo 1792097 2688725 := bbase (se 7 (by rfl) ⟨31508, by rfl⟩ : syracuseStep 2688725 = 63017) (by norm_num)
theorem B2016985 : Blo 1792097 2016985 := bbase (se 2 (by rfl) ⟨756369, by rfl⟩ : syracuseStep 2016985 = 1512739) (by norm_num)
theorem B7268069 : Blo 1792097 7268069 := bbase (se 4 (by rfl) ⟨681381, by rfl⟩ : syracuseStep 7268069 = 1362763) (by norm_num)
theorem B2688749 : Blo 1792097 2688749 := bbase (se 3 (by rfl) ⟨504140, by rfl⟩ : syracuseStep 2688749 = 1008281) (by norm_num)
theorem B2017021 : Blo 1792097 2017021 := bbase (se 3 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 2017021 = 756383) (by norm_num)
theorem B3229445 : Blo 1792097 3229445 := bbase (se 4 (by rfl) ⟨302760, by rfl⟩ : syracuseStep 3229445 = 605521) (by norm_num)
theorem B2688773 : Blo 1792097 2688773 := bbase (se 4 (by rfl) ⟨252072, by rfl⟩ : syracuseStep 2688773 = 504145) (by norm_num)
theorem B4032269 : Blo 1792097 4032269 := bbase (se 3 (by rfl) ⟨756050, by rfl⟩ : syracuseStep 4032269 = 1512101) (by norm_num)
theorem B3024661 : Blo 1792097 3024661 := bbase (se 6 (by rfl) ⟨70890, by rfl⟩ : syracuseStep 3024661 = 141781) (by norm_num)
theorem B2688797 : Blo 1792097 2688797 := bbase (se 3 (by rfl) ⟨504149, by rfl⟩ : syracuseStep 2688797 = 1008299) (by norm_num)
theorem B2017057 : Blo 1792097 2017057 := bbase (se 2 (by rfl) ⟨756396, by rfl⟩ : syracuseStep 2017057 = 1512793) (by norm_num)
theorem B10209077 : Blo 1792097 10209077 := bbase (se 5 (by rfl) ⟨478550, by rfl⟩ : syracuseStep 10209077 = 957101) (by norm_num)
theorem B2688821 : Blo 1792097 2688821 := bbase (se 5 (by rfl) ⟨126038, by rfl⟩ : syracuseStep 2688821 = 252077) (by norm_num)
theorem B2017093 : Blo 1792097 2017093 := bbase (se 4 (by rfl) ⟨189102, by rfl⟩ : syracuseStep 2017093 = 378205) (by norm_num)
theorem B2688845 : Blo 1792097 2688845 := bbase (se 3 (by rfl) ⟨504158, by rfl⟩ : syracuseStep 2688845 = 1008317) (by norm_num)
theorem B4663117 : Blo 1792097 4663117 := bbase (se 3 (by rfl) ⟨874334, by rfl⟩ : syracuseStep 4663117 = 1748669) (by norm_num)
theorem B4032341 : Blo 1792097 4032341 := bbase (se 9 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 4032341 = 23627) (by norm_num)
theorem B2688869 : Blo 1792097 2688869 := bbase (se 4 (by rfl) ⟨252081, by rfl⟩ : syracuseStep 2688869 = 504163) (by norm_num)
theorem B2017129 : Blo 1792097 2017129 := bbase (se 2 (by rfl) ⟨756423, by rfl⟩ : syracuseStep 2017129 = 1512847) (by norm_num)
theorem B3024749 : Blo 1792097 3024749 := bbase (se 3 (by rfl) ⟨567140, by rfl⟩ : syracuseStep 3024749 = 1134281) (by norm_num)
theorem B2688893 : Blo 1792097 2688893 := bbase (se 3 (by rfl) ⟨504167, by rfl⟩ : syracuseStep 2688893 = 1008335) (by norm_num)
theorem B2017165 : Blo 1792097 2017165 := bbase (se 3 (by rfl) ⟨378218, by rfl⟩ : syracuseStep 2017165 = 756437) (by norm_num)
theorem B2688917 : Blo 1792097 2688917 := bbase (se 6 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 2688917 = 126043) (by norm_num)
theorem B4032413 : Blo 1792097 4032413 := bbase (se 3 (by rfl) ⟨756077, by rfl⟩ : syracuseStep 4032413 = 1512155) (by norm_num)
theorem B2688941 : Blo 1792097 2688941 := bbase (se 3 (by rfl) ⟨504176, by rfl⟩ : syracuseStep 2688941 = 1008353) (by norm_num)
theorem B4540333 : Blo 1792097 4540333 := bbase (se 3 (by rfl) ⟨851312, by rfl⟩ : syracuseStep 4540333 = 1702625) (by norm_num)
theorem B2017201 : Blo 1792097 2017201 := bbase (se 2 (by rfl) ⟨756450, by rfl⟩ : syracuseStep 2017201 = 1512901) (by norm_num)
theorem B2688965 : Blo 1792097 2688965 := bbase (se 4 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 2688965 = 504181) (by norm_num)
theorem B2017237 : Blo 1792097 2017237 := bbase (se 7 (by rfl) ⟨23639, by rfl⟩ : syracuseStep 2017237 = 47279) (by norm_num)
theorem B74631125 : Blo 1792097 74631125 := bbase (se 7 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 74631125 = 1749167) (by norm_num)
theorem B2688989 : Blo 1792097 2688989 := bbase (se 3 (by rfl) ⟨504185, by rfl⟩ : syracuseStep 2688989 = 1008371) (by norm_num)
theorem B4032485 : Blo 1792097 4032485 := bbase (se 4 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 4032485 = 756091) (by norm_num)
theorem B3024877 : Blo 1792097 3024877 := bbase (se 3 (by rfl) ⟨567164, by rfl⟩ : syracuseStep 3024877 = 1134329) (by norm_num)
theorem B2689013 : Blo 1792097 2689013 := bbase (se 5 (by rfl) ⟨126047, by rfl⟩ : syracuseStep 2689013 = 252095) (by norm_num)
theorem B2017273 : Blo 1792097 2017273 := bbase (se 2 (by rfl) ⟨756477, by rfl⟩ : syracuseStep 2017273 = 1512955) (by norm_num)
theorem B2689037 : Blo 1792097 2689037 := bbase (se 3 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 2689037 = 1008389) (by norm_num)
theorem B2017309 : Blo 1792097 2017309 := bbase (se 3 (by rfl) ⟨378245, by rfl⟩ : syracuseStep 2017309 = 756491) (by norm_num)
theorem B4540445 : Blo 1792097 4540445 := bbase (se 3 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 4540445 = 1702667) (by norm_num)
theorem B2689061 : Blo 1792097 2689061 := bbase (se 4 (by rfl) ⟨252099, by rfl⟩ : syracuseStep 2689061 = 504199) (by norm_num)
theorem B4032557 : Blo 1792097 4032557 := bbase (se 3 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 4032557 = 1512209) (by norm_num)
theorem B2689085 : Blo 1792097 2689085 := bbase (se 3 (by rfl) ⟨504203, by rfl⟩ : syracuseStep 2689085 = 1008407) (by norm_num)
theorem B2017345 : Blo 1792097 2017345 := bbase (se 2 (by rfl) ⟨756504, by rfl⟩ : syracuseStep 2017345 = 1513009) (by norm_num)
theorem B3024965 : Blo 1792097 3024965 := bbase (se 4 (by rfl) ⟨283590, by rfl⟩ : syracuseStep 3024965 = 567181) (by norm_num)
theorem B2689109 : Blo 1792097 2689109 := bbase (se 8 (by rfl) ⟨15756, by rfl⟩ : syracuseStep 2689109 = 31513) (by norm_num)
theorem B2017381 : Blo 1792097 2017381 := bbase (se 4 (by rfl) ⟨189129, by rfl⟩ : syracuseStep 2017381 = 378259) (by norm_num)
theorem B2689133 : Blo 1792097 2689133 := bbase (se 3 (by rfl) ⟨504212, by rfl⟩ : syracuseStep 2689133 = 1008425) (by norm_num)
theorem B4032629 : Blo 1792097 4032629 := bbase (se 5 (by rfl) ⟨189029, by rfl⟩ : syracuseStep 4032629 = 378059) (by norm_num)
theorem B2689157 : Blo 1792097 2689157 := bbase (se 4 (by rfl) ⟨252108, by rfl⟩ : syracuseStep 2689157 = 504217) (by norm_num)
theorem B2017417 : Blo 1792097 2017417 := bbase (se 2 (by rfl) ⟨756531, by rfl⟩ : syracuseStep 2017417 = 1513063) (by norm_num)
theorem B2689181 : Blo 1792097 2689181 := bbase (se 3 (by rfl) ⟨504221, by rfl⟩ : syracuseStep 2689181 = 1008443) (by norm_num)
theorem B2017453 : Blo 1792097 2017453 := bbase (se 3 (by rfl) ⟨378272, by rfl⟩ : syracuseStep 2017453 = 756545) (by norm_num)
theorem B2689205 : Blo 1792097 2689205 := bbase (se 5 (by rfl) ⟨126056, by rfl⟩ : syracuseStep 2689205 = 252113) (by norm_num)
theorem B9078965 : Blo 1792097 9078965 := bbase (se 5 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 9078965 = 851153) (by norm_num)
theorem B4032701 : Blo 1792097 4032701 := bbase (se 3 (by rfl) ⟨756131, by rfl⟩ : syracuseStep 4032701 = 1512263) (by norm_num)
theorem B3025093 : Blo 1792097 3025093 := bbase (se 4 (by rfl) ⟨283602, by rfl⟩ : syracuseStep 3025093 = 567205) (by norm_num)
theorem B2689229 : Blo 1792097 2689229 := bbase (se 3 (by rfl) ⟨504230, by rfl⟩ : syracuseStep 2689229 = 1008461) (by norm_num)
theorem B2017489 : Blo 1792097 2017489 := bbase (se 2 (by rfl) ⟨756558, by rfl⟩ : syracuseStep 2017489 = 1513117) (by norm_num)
theorem B4540637 : Blo 1792097 4540637 := bbase (se 3 (by rfl) ⟨851369, by rfl⟩ : syracuseStep 4540637 = 1702739) (by norm_num)
theorem B2689253 : Blo 1792097 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B2017525 : Blo 1792097 2017525 := bbase (se 5 (by rfl) ⟨94571, by rfl⟩ : syracuseStep 2017525 = 189143) (by norm_num)
theorem B2689277 : Blo 1792097 2689277 := bbase (se 3 (by rfl) ⟨504239, by rfl⟩ : syracuseStep 2689277 = 1008479) (by norm_num)
theorem B4032773 : Blo 1792097 4032773 := bbase (se 4 (by rfl) ⟨378072, by rfl⟩ : syracuseStep 4032773 = 756145) (by norm_num)
theorem B2689301 : Blo 1792097 2689301 := bbase (se 6 (by rfl) ⟨63030, by rfl⟩ : syracuseStep 2689301 = 126061) (by norm_num)
theorem B2017561 : Blo 1792097 2017561 := bbase (se 2 (by rfl) ⟨756585, by rfl⟩ : syracuseStep 2017561 = 1513171) (by norm_num)
theorem B3025181 : Blo 1792097 3025181 := bbase (se 3 (by rfl) ⟨567221, by rfl⟩ : syracuseStep 3025181 = 1134443) (by norm_num)
theorem B2689325 : Blo 1792097 2689325 := bbase (se 3 (by rfl) ⟨504248, by rfl⟩ : syracuseStep 2689325 = 1008497) (by norm_num)
theorem B2017597 : Blo 1792097 2017597 := bbase (se 3 (by rfl) ⟨378299, by rfl⟩ : syracuseStep 2017597 = 756599) (by norm_num)
theorem B2689349 : Blo 1792097 2689349 := bbase (se 4 (by rfl) ⟨252126, by rfl⟩ : syracuseStep 2689349 = 504253) (by norm_num)
theorem B5744965 : Blo 1792097 5744965 := bbase (se 4 (by rfl) ⟨538590, by rfl⟩ : syracuseStep 5744965 = 1077181) (by norm_num)
theorem B4032845 : Blo 1792097 4032845 := bbase (se 3 (by rfl) ⟨756158, by rfl⟩ : syracuseStep 4032845 = 1512317) (by norm_num)
theorem B2689373 : Blo 1792097 2689373 := bbase (se 3 (by rfl) ⟨504257, by rfl⟩ : syracuseStep 2689373 = 1008515) (by norm_num)
theorem B2017633 : Blo 1792097 2017633 := bbase (se 2 (by rfl) ⟨756612, by rfl⟩ : syracuseStep 2017633 = 1513225) (by norm_num)
theorem B2689397 : Blo 1792097 2689397 := bbase (se 5 (by rfl) ⟨126065, by rfl⟩ : syracuseStep 2689397 = 252131) (by norm_num)
theorem B5106053 : Blo 1792097 5106053 := bbase (se 4 (by rfl) ⟨478692, by rfl⟩ : syracuseStep 5106053 = 957385) (by norm_num)
theorem B2017669 : Blo 1792097 2017669 := bbase (se 4 (by rfl) ⟨189156, by rfl⟩ : syracuseStep 2017669 = 378313) (by norm_num)
theorem B2689421 : Blo 1792097 2689421 := bbase (se 3 (by rfl) ⟨504266, by rfl⟩ : syracuseStep 2689421 = 1008533) (by norm_num)
theorem B4032917 : Blo 1792097 4032917 := bbase (se 6 (by rfl) ⟨94521, by rfl⟩ : syracuseStep 4032917 = 189043) (by norm_num)
theorem B3025309 : Blo 1792097 3025309 := bbase (se 3 (by rfl) ⟨567245, by rfl⟩ : syracuseStep 3025309 = 1134491) (by norm_num)
theorem B2689445 : Blo 1792097 2689445 := bbase (se 4 (by rfl) ⟨252135, by rfl⟩ : syracuseStep 2689445 = 504271) (by norm_num)
theorem B2017705 : Blo 1792097 2017705 := bbase (se 2 (by rfl) ⟨756639, by rfl⟩ : syracuseStep 2017705 = 1513279) (by norm_num)
theorem B2689469 : Blo 1792097 2689469 := bbase (se 3 (by rfl) ⟨504275, by rfl⟩ : syracuseStep 2689469 = 1008551) (by norm_num)
theorem B2017741 : Blo 1792097 2017741 := bbase (se 3 (by rfl) ⟨378326, by rfl⟩ : syracuseStep 2017741 = 756653) (by norm_num)
theorem B2689493 : Blo 1792097 2689493 := bbase (se 7 (by rfl) ⟨31517, by rfl⟩ : syracuseStep 2689493 = 63035) (by norm_num)
theorem B4032989 : Blo 1792097 4032989 := bbase (se 3 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 4032989 = 1512371) (by norm_num)
theorem B7662053 : Blo 1792097 7662053 := bbase (se 4 (by rfl) ⟨718317, by rfl⟩ : syracuseStep 7662053 = 1436635) (by norm_num)
theorem B2689517 : Blo 1792097 2689517 := bbase (se 3 (by rfl) ⟨504284, by rfl⟩ : syracuseStep 2689517 = 1008569) (by norm_num)
theorem B2017777 : Blo 1792097 2017777 := bbase (se 2 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 2017777 = 1513333) (by norm_num)
theorem B3025397 : Blo 1792097 3025397 := bbase (se 5 (by rfl) ⟨141815, by rfl⟩ : syracuseStep 3025397 = 283631) (by norm_num)
theorem B2689541 : Blo 1792097 2689541 := bbase (se 4 (by rfl) ⟨252144, by rfl⟩ : syracuseStep 2689541 = 504289) (by norm_num)
theorem B2017813 : Blo 1792097 2017813 := bbase (se 6 (by rfl) ⟨47292, by rfl⟩ : syracuseStep 2017813 = 94585) (by norm_num)
theorem B2689565 : Blo 1792097 2689565 := bbase (se 3 (by rfl) ⟨504293, by rfl⟩ : syracuseStep 2689565 = 1008587) (by norm_num)
theorem B4033061 : Blo 1792097 4033061 := bbase (se 4 (by rfl) ⟨378099, by rfl⟩ : syracuseStep 4033061 = 756199) (by norm_num)
theorem B2689589 : Blo 1792097 2689589 := bbase (se 5 (by rfl) ⟨126074, by rfl⟩ : syracuseStep 2689589 = 252149) (by norm_num)
theorem B4540981 : Blo 1792097 4540981 := bbase (se 5 (by rfl) ⟨212858, by rfl⟩ : syracuseStep 4540981 = 425717) (by norm_num)
theorem B2017849 : Blo 1792097 2017849 := bbase (se 2 (by rfl) ⟨756693, by rfl⟩ : syracuseStep 2017849 = 1513387) (by norm_num)
theorem B3828293 : Blo 1792097 3828293 := bbase (se 4 (by rfl) ⟨358902, by rfl⟩ : syracuseStep 3828293 = 717805) (by norm_num)
theorem B2689613 : Blo 1792097 2689613 := bbase (se 3 (by rfl) ⟨504302, by rfl⟩ : syracuseStep 2689613 = 1008605) (by norm_num)
theorem B9202261 : Blo 1792097 9202261 := bbase (se 8 (by rfl) ⟨53919, by rfl⟩ : syracuseStep 9202261 = 107839) (by norm_num)
theorem B2017885 : Blo 1792097 2017885 := bbase (se 3 (by rfl) ⟨378353, by rfl⟩ : syracuseStep 2017885 = 756707) (by norm_num)
theorem B2689637 : Blo 1792097 2689637 := bbase (se 4 (by rfl) ⟨252153, by rfl⟩ : syracuseStep 2689637 = 504307) (by norm_num)
theorem B4033133 : Blo 1792097 4033133 := bbase (se 3 (by rfl) ⟨756212, by rfl⟩ : syracuseStep 4033133 = 1512425) (by norm_num)
theorem B3025525 : Blo 1792097 3025525 := bbase (se 5 (by rfl) ⟨141821, by rfl⟩ : syracuseStep 3025525 = 283643) (by norm_num)
theorem B2689661 : Blo 1792097 2689661 := bbase (se 3 (by rfl) ⟨504311, by rfl⟩ : syracuseStep 2689661 = 1008623) (by norm_num)
theorem B2017921 : Blo 1792097 2017921 := bbase (se 2 (by rfl) ⟨756720, by rfl⟩ : syracuseStep 2017921 = 1513441) (by norm_num)
theorem B2689685 : Blo 1792097 2689685 := bbase (se 6 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 2689685 = 126079) (by norm_num)
theorem B2017957 : Blo 1792097 2017957 := bbase (se 4 (by rfl) ⟨189183, by rfl⟩ : syracuseStep 2017957 = 378367) (by norm_num)
theorem B4541093 : Blo 1792097 4541093 := bbase (se 4 (by rfl) ⟨425727, by rfl⟩ : syracuseStep 4541093 = 851455) (by norm_num)
theorem B2689709 : Blo 1792097 2689709 := bbase (se 3 (by rfl) ⟨504320, by rfl⟩ : syracuseStep 2689709 = 1008641) (by norm_num)
theorem B4033205 : Blo 1792097 4033205 := bbase (se 5 (by rfl) ⟨189056, by rfl⟩ : syracuseStep 4033205 = 378113) (by norm_num)
theorem B2689733 : Blo 1792097 2689733 := bbase (se 4 (by rfl) ⟨252162, by rfl⟩ : syracuseStep 2689733 = 504325) (by norm_num)
theorem B2017993 : Blo 1792097 2017993 := bbase (se 2 (by rfl) ⟨756747, by rfl⟩ : syracuseStep 2017993 = 1513495) (by norm_num)
theorem B3025613 : Blo 1792097 3025613 := bbase (se 3 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 3025613 = 1134605) (by norm_num)
theorem B2689757 : Blo 1792097 2689757 := bbase (se 3 (by rfl) ⟨504329, by rfl⟩ : syracuseStep 2689757 = 1008659) (by norm_num)
theorem B6048485 : Blo 1792097 6048485 := bbase (se 4 (by rfl) ⟨567045, by rfl⟩ : syracuseStep 6048485 = 1134091) (by norm_num)
theorem B2018029 : Blo 1792097 2018029 := bbase (se 3 (by rfl) ⟨378380, by rfl⟩ : syracuseStep 2018029 = 756761) (by norm_num)
theorem B2689781 : Blo 1792097 2689781 := bbase (se 5 (by rfl) ⟨126083, by rfl⟩ : syracuseStep 2689781 = 252167) (by norm_num)
theorem B4033277 : Blo 1792097 4033277 := bbase (se 3 (by rfl) ⟨756239, by rfl⟩ : syracuseStep 4033277 = 1512479) (by norm_num)
theorem B2689805 : Blo 1792097 2689805 := bbase (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) (by norm_num)
theorem B2018065 : Blo 1792097 2018065 := bbase (se 2 (by rfl) ⟨756774, by rfl⟩ : syracuseStep 2018065 = 1513549) (by norm_num)
theorem B2689829 : Blo 1792097 2689829 := bbase (se 4 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 2689829 = 504343) (by norm_num)
theorem B2018101 : Blo 1792097 2018101 := bbase (se 5 (by rfl) ⟨94598, by rfl⟩ : syracuseStep 2018101 = 189197) (by norm_num)
theorem B3828541 : Blo 1792097 3828541 := bbase (se 3 (by rfl) ⟨717851, by rfl⟩ : syracuseStep 3828541 = 1435703) (by norm_num)
theorem B2689853 : Blo 1792097 2689853 := bbase (se 3 (by rfl) ⟨504347, by rfl⟩ : syracuseStep 2689853 = 1008695) (by norm_num)
theorem B4033349 : Blo 1792097 4033349 := bbase (se 4 (by rfl) ⟨378126, by rfl⟩ : syracuseStep 4033349 = 756253) (by norm_num)
theorem B3025741 : Blo 1792097 3025741 := bbase (se 3 (by rfl) ⟨567326, by rfl⟩ : syracuseStep 3025741 = 1134653) (by norm_num)
theorem B2689877 : Blo 1792097 2689877 := bbase (se 9 (by rfl) ⟨7880, by rfl⟩ : syracuseStep 2689877 = 15761) (by norm_num)
theorem B2018137 : Blo 1792097 2018137 := bbase (se 2 (by rfl) ⟨756801, by rfl⟩ : syracuseStep 2018137 = 1513603) (by norm_num)
theorem B4541285 : Blo 1792097 4541285 := bbase (se 4 (by rfl) ⟨425745, by rfl⟩ : syracuseStep 4541285 = 851491) (by norm_num)
theorem B2689901 : Blo 1792097 2689901 := bbase (se 3 (by rfl) ⟨504356, by rfl⟩ : syracuseStep 2689901 = 1008713) (by norm_num)
theorem B2018173 : Blo 1792097 2018173 := bbase (se 3 (by rfl) ⟨378407, by rfl⟩ : syracuseStep 2018173 = 756815) (by norm_num)
theorem B6548357 : Blo 1792097 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B2689925 : Blo 1792097 2689925 := bbase (se 4 (by rfl) ⟨252180, by rfl⟩ : syracuseStep 2689925 = 504361) (by norm_num)
theorem B4033421 : Blo 1792097 4033421 := bbase (se 3 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 4033421 = 1512533) (by norm_num)
theorem B14740373 : Blo 1792097 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B3230621 : Blo 1792097 3230621 := bbase (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) (by norm_num)
theorem B2689949 : Blo 1792097 2689949 := bbase (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) (by norm_num)
theorem B2018209 : Blo 1792097 2018209 := bbase (se 2 (by rfl) ⟨756828, by rfl⟩ : syracuseStep 2018209 = 1513657) (by norm_num)
theorem B3402661 : Blo 1792097 3402661 := bbase (se 4 (by rfl) ⟨318999, by rfl⟩ : syracuseStep 3402661 = 637999) (by norm_num)
theorem B3025829 : Blo 1792097 3025829 := bbase (se 4 (by rfl) ⟨283671, by rfl⟩ : syracuseStep 3025829 = 567343) (by norm_num)
theorem B2689973 : Blo 1792097 2689973 := bbase (se 5 (by rfl) ⟨126092, by rfl⟩ : syracuseStep 2689973 = 252185) (by norm_num)
theorem B2018245 : Blo 1792097 2018245 := bbase (se 4 (by rfl) ⟨189210, by rfl⟩ : syracuseStep 2018245 = 378421) (by norm_num)
theorem B2100173 : Blo 1792097 2100173 := bbase (se 3 (by rfl) ⟨393782, by rfl⟩ : syracuseStep 2100173 = 787565) (by norm_num)
theorem B2689997 : Blo 1792097 2689997 := bbase (se 3 (by rfl) ⟨504374, by rfl⟩ : syracuseStep 2689997 = 1008749) (by norm_num)
theorem B74591189 : Blo 1792097 74591189 := bbase (se 7 (by rfl) ⟨874115, by rfl⟩ : syracuseStep 74591189 = 1748231) (by norm_num)
theorem B4033493 : Blo 1792097 4033493 := bbase (se 7 (by rfl) ⟨47267, by rfl⟩ : syracuseStep 4033493 = 94535) (by norm_num)
theorem B2690021 : Blo 1792097 2690021 := bbase (se 4 (by rfl) ⟨252189, by rfl⟩ : syracuseStep 2690021 = 504379) (by norm_num)
theorem B2018281 : Blo 1792097 2018281 := bbase (se 2 (by rfl) ⟨756855, by rfl⟩ : syracuseStep 2018281 = 1513711) (by norm_num)
theorem B2690045 : Blo 1792097 2690045 := bbase (se 3 (by rfl) ⟨504383, by rfl⟩ : syracuseStep 2690045 = 1008767) (by norm_num)
theorem B2018317 : Blo 1792097 2018317 := bbase (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) (by norm_num)
theorem B2690069 : Blo 1792097 2690069 := bbase (se 6 (by rfl) ⟨63048, by rfl⟩ : syracuseStep 2690069 = 126097) (by norm_num)
theorem B4033565 : Blo 1792097 4033565 := bbase (se 3 (by rfl) ⟨756293, by rfl⟩ : syracuseStep 4033565 = 1512587) (by norm_num)
theorem B3025957 : Blo 1792097 3025957 := bbase (se 4 (by rfl) ⟨283683, by rfl⟩ : syracuseStep 3025957 = 567367) (by norm_num)
theorem B2690093 : Blo 1792097 2690093 := bbase (se 3 (by rfl) ⟨504392, by rfl⟩ : syracuseStep 2690093 = 1008785) (by norm_num)
theorem B2018353 : Blo 1792097 2018353 := bbase (se 2 (by rfl) ⟨756882, by rfl⟩ : syracuseStep 2018353 = 1513765) (by norm_num)
theorem B3402805 : Blo 1792097 3402805 := bbase (se 5 (by rfl) ⟨159506, by rfl⟩ : syracuseStep 3402805 = 319013) (by norm_num)
theorem B2690117 : Blo 1792097 2690117 := bbase (se 4 (by rfl) ⟨252198, by rfl⟩ : syracuseStep 2690117 = 504397) (by norm_num)
theorem B2690141 : Blo 1792097 2690141 := bbase (se 3 (by rfl) ⟨504401, by rfl⟩ : syracuseStep 2690141 = 1008803) (by norm_num)
theorem B4033637 : Blo 1792097 4033637 := bbase (se 4 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 4033637 = 756307) (by norm_num)
theorem B2690165 : Blo 1792097 2690165 := bbase (se 5 (by rfl) ⟨126101, by rfl⟩ : syracuseStep 2690165 = 252203) (by norm_num)
theorem B3026045 : Blo 1792097 3026045 := bbase (se 3 (by rfl) ⟨567383, by rfl⟩ : syracuseStep 3026045 = 1134767) (by norm_num)
theorem B2690189 : Blo 1792097 2690189 := bbase (se 3 (by rfl) ⟨504410, by rfl⟩ : syracuseStep 2690189 = 1008821) (by norm_num)
theorem B6048917 : Blo 1792097 6048917 := bbase (se 6 (by rfl) ⟨141771, by rfl⟩ : syracuseStep 6048917 = 283543) (by norm_num)
theorem B2690213 : Blo 1792097 2690213 := bbase (se 4 (by rfl) ⟨252207, by rfl⟩ : syracuseStep 2690213 = 504415) (by norm_num)
theorem B4033709 : Blo 1792097 4033709 := bbase (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) (by norm_num)
theorem B2690237 : Blo 1792097 2690237 := bbase (se 3 (by rfl) ⟨504419, by rfl⟩ : syracuseStep 2690237 = 1008839) (by norm_num)
theorem B3402965 : Blo 1792097 3402965 := bbase (se 7 (by rfl) ⟨39878, by rfl⟩ : syracuseStep 3402965 = 79757) (by norm_num)
theorem B2690261 : Blo 1792097 2690261 := bbase (se 7 (by rfl) ⟨31526, by rfl⟩ : syracuseStep 2690261 = 63053) (by norm_num)
theorem B2690285 : Blo 1792097 2690285 := bbase (se 3 (by rfl) ⟨504428, by rfl⟩ : syracuseStep 2690285 = 1008857) (by norm_num)
theorem B4033781 : Blo 1792097 4033781 := bbase (se 5 (by rfl) ⟨189083, by rfl⟩ : syracuseStep 4033781 = 378167) (by norm_num)
theorem B3026173 : Blo 1792097 3026173 := bbase (se 3 (by rfl) ⟨567407, by rfl⟩ : syracuseStep 3026173 = 1134815) (by norm_num)
theorem B2690309 : Blo 1792097 2690309 := bbase (se 4 (by rfl) ⟨252216, by rfl⟩ : syracuseStep 2690309 = 504433) (by norm_num)
theorem B24546581 : Blo 1792097 24546581 := bbase (se 6 (by rfl) ⟨575310, by rfl⟩ : syracuseStep 24546581 = 1150621) (by norm_num)
theorem B2690333 : Blo 1792097 2690333 := bbase (se 3 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 2690333 = 1008875) (by norm_num)
theorem B3829045 : Blo 1792097 3829045 := bbase (se 5 (by rfl) ⟨179486, by rfl⟩ : syracuseStep 3829045 = 358973) (by norm_num)
theorem B2690357 : Blo 1792097 2690357 := bbase (se 5 (by rfl) ⟨126110, by rfl⟩ : syracuseStep 2690357 = 252221) (by norm_num)
theorem B4033853 : Blo 1792097 4033853 := bbase (se 3 (by rfl) ⟨756347, by rfl⟩ : syracuseStep 4033853 = 1512695) (by norm_num)
theorem B2690381 : Blo 1792097 2690381 := bbase (se 3 (by rfl) ⟨504446, by rfl⟩ : syracuseStep 2690381 = 1008893) (by norm_num)
theorem B113397077 : Blo 1792097 113397077 := bbase (se 11 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 113397077 = 166109) (by norm_num)
theorem B3026261 : Blo 1792097 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B3067229 : Blo 1792097 3067229 := bbase (se 3 (by rfl) ⟨575105, by rfl⟩ : syracuseStep 3067229 = 1150211) (by norm_num)
theorem B3403109 : Blo 1792097 3403109 := bbase (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) (by norm_num)
theorem B2690405 : Blo 1792097 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B2690429 : Blo 1792097 2690429 := bbase (se 3 (by rfl) ⟨504455, by rfl⟩ : syracuseStep 2690429 = 1008911) (by norm_num)
theorem B4033925 : Blo 1792097 4033925 := bbase (se 4 (by rfl) ⟨378180, by rfl⟩ : syracuseStep 4033925 = 756361) (by norm_num)
theorem B2690453 : Blo 1792097 2690453 := bbase (se 6 (by rfl) ⟨63057, by rfl⟩ : syracuseStep 2690453 = 126115) (by norm_num)
theorem B2690477 : Blo 1792097 2690477 := bbase (se 3 (by rfl) ⟨504464, by rfl⟩ : syracuseStep 2690477 = 1008929) (by norm_num)
theorem B9080261 : Blo 1792097 9080261 := bbase (se 4 (by rfl) ⟨851274, by rfl⟩ : syracuseStep 9080261 = 1702549) (by norm_num)
theorem B2690501 : Blo 1792097 2690501 := bbase (se 4 (by rfl) ⟨252234, by rfl⟩ : syracuseStep 2690501 = 504469) (by norm_num)
theorem B3452357 : Blo 1792097 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B4033997 : Blo 1792097 4033997 := bbase (se 3 (by rfl) ⟨756374, by rfl⟩ : syracuseStep 4033997 = 1512749) (by norm_num)
theorem B3026389 : Blo 1792097 3026389 := bbase (se 7 (by rfl) ⟨35465, by rfl⟩ : syracuseStep 3026389 = 70931) (by norm_num)
theorem B2690525 : Blo 1792097 2690525 := bbase (se 3 (by rfl) ⟨504473, by rfl⟩ : syracuseStep 2690525 = 1008947) (by norm_num)
theorem B2690549 : Blo 1792097 2690549 := bbase (se 5 (by rfl) ⟨126119, by rfl⟩ : syracuseStep 2690549 = 252239) (by norm_num)
theorem B2870797 : Blo 1792097 2870797 := bbase (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) (by norm_num)
theorem B2690573 : Blo 1792097 2690573 := bbase (se 3 (by rfl) ⟨504482, by rfl⟩ : syracuseStep 2690573 = 1008965) (by norm_num)
theorem B4034069 : Blo 1792097 4034069 := bbase (se 6 (by rfl) ⟨94548, by rfl⟩ : syracuseStep 4034069 = 189097) (by norm_num)
theorem B2690597 : Blo 1792097 2690597 := bbase (se 4 (by rfl) ⟨252243, by rfl⟩ : syracuseStep 2690597 = 504487) (by norm_num)
theorem B3026477 : Blo 1792097 3026477 := bbase (se 3 (by rfl) ⟨567464, by rfl⟩ : syracuseStep 3026477 = 1134929) (by norm_num)
theorem B2690621 : Blo 1792097 2690621 := bbase (se 3 (by rfl) ⟨504491, by rfl⟩ : syracuseStep 2690621 = 1008983) (by norm_num)
theorem B6049349 : Blo 1792097 6049349 := bbase (se 4 (by rfl) ⟨567126, by rfl⟩ : syracuseStep 6049349 = 1134253) (by norm_num)
theorem B2690645 : Blo 1792097 2690645 := bbase (se 8 (by rfl) ⟨15765, by rfl⟩ : syracuseStep 2690645 = 31531) (by norm_num)
theorem B4034141 : Blo 1792097 4034141 := bbase (se 3 (by rfl) ⟨756401, by rfl⟩ : syracuseStep 4034141 = 1512803) (by norm_num)
theorem B2870893 : Blo 1792097 2870893 := bbase (se 3 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 2870893 = 1076585) (by norm_num)
theorem B2690669 : Blo 1792097 2690669 := bbase (se 3 (by rfl) ⟨504500, by rfl⟩ : syracuseStep 2690669 = 1009001) (by norm_num)
theorem B3403397 : Blo 1792097 3403397 := bbase (se 4 (by rfl) ⟨319068, by rfl⟩ : syracuseStep 3403397 = 638137) (by norm_num)
theorem B2690693 : Blo 1792097 2690693 := bbase (se 4 (by rfl) ⟨252252, by rfl⟩ : syracuseStep 2690693 = 504505) (by norm_num)
theorem B4845205 : Blo 1792097 4845205 := bbase (se 6 (by rfl) ⟨113559, by rfl⟩ : syracuseStep 4845205 = 227119) (by norm_num)
theorem B2690717 : Blo 1792097 2690717 := bbase (se 3 (by rfl) ⟨504509, by rfl⟩ : syracuseStep 2690717 = 1009019) (by norm_num)
theorem B4034213 : Blo 1792097 4034213 := bbase (se 4 (by rfl) ⟨378207, by rfl⟩ : syracuseStep 4034213 = 756415) (by norm_num)
theorem B3026605 : Blo 1792097 3026605 := bbase (se 3 (by rfl) ⟨567488, by rfl⟩ : syracuseStep 3026605 = 1134977) (by norm_num)
theorem B2690741 : Blo 1792097 2690741 := bbase (se 5 (by rfl) ⟨126128, by rfl⟩ : syracuseStep 2690741 = 252257) (by norm_num)
theorem B2690765 : Blo 1792097 2690765 := bbase (se 3 (by rfl) ⟨504518, by rfl⟩ : syracuseStep 2690765 = 1009037) (by norm_num)
theorem B2690789 : Blo 1792097 2690789 := bbase (se 4 (by rfl) ⟨252261, by rfl⟩ : syracuseStep 2690789 = 504523) (by norm_num)
theorem B2043625 : Blo 1792097 2043625 := bbase (se 2 (by rfl) ⟨766359, by rfl⟩ : syracuseStep 2043625 = 1532719) (by norm_num)
theorem B4034285 : Blo 1792097 4034285 := bbase (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) (by norm_num)
theorem B2690813 : Blo 1792097 2690813 := bbase (se 3 (by rfl) ⟨504527, by rfl⟩ : syracuseStep 2690813 = 1009055) (by norm_num)
theorem B3026693 : Blo 1792097 3026693 := bbase (se 4 (by rfl) ⟨283752, by rfl⟩ : syracuseStep 3026693 = 567505) (by norm_num)
theorem B6811397 : Blo 1792097 6811397 := bbase (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) (by norm_num)
theorem B2871053 : Blo 1792097 2871053 := bbase (se 3 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 2871053 = 1076645) (by norm_num)
theorem B2690837 : Blo 1792097 2690837 := bbase (se 6 (by rfl) ⟨63066, by rfl⟩ : syracuseStep 2690837 = 126133) (by norm_num)
theorem B3403549 : Blo 1792097 3403549 := bbase (se 3 (by rfl) ⟨638165, by rfl⟩ : syracuseStep 3403549 = 1276331) (by norm_num)
theorem B2690861 : Blo 1792097 2690861 := bbase (se 3 (by rfl) ⟨504536, by rfl⟩ : syracuseStep 2690861 = 1009073) (by norm_num)
theorem B2182961 : Blo 1792097 2182961 := bbase (se 2 (by rfl) ⟨818610, by rfl⟩ : syracuseStep 2182961 = 1637221) (by norm_num)
theorem B15314741 : Blo 1792097 15314741 := bbase (se 5 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 15314741 = 1435757) (by norm_num)
theorem B4034357 : Blo 1792097 4034357 := bbase (se 5 (by rfl) ⟨189110, by rfl⟩ : syracuseStep 4034357 = 378221) (by norm_num)
theorem B2690885 : Blo 1792097 2690885 := bbase (se 4 (by rfl) ⟨252270, by rfl⟩ : syracuseStep 2690885 = 504541) (by norm_num)
theorem B2690909 : Blo 1792097 2690909 := bbase (se 3 (by rfl) ⟨504545, by rfl⟩ : syracuseStep 2690909 = 1009091) (by norm_num)
theorem B2690933 : Blo 1792097 2690933 := bbase (se 5 (by rfl) ⟨126137, by rfl⟩ : syracuseStep 2690933 = 252275) (by norm_num)
theorem B4034429 : Blo 1792097 4034429 := bbase (se 3 (by rfl) ⟨756455, by rfl⟩ : syracuseStep 4034429 = 1512911) (by norm_num)
theorem B3026821 : Blo 1792097 3026821 := bbase (se 4 (by rfl) ⟨283764, by rfl⟩ : syracuseStep 3026821 = 567529) (by norm_num)
theorem B5746565 : Blo 1792097 5746565 := bbase (se 4 (by rfl) ⟨538740, by rfl⟩ : syracuseStep 5746565 = 1077481) (by norm_num)
theorem B2690957 : Blo 1792097 2690957 := bbase (se 3 (by rfl) ⟨504554, by rfl⟩ : syracuseStep 2690957 = 1009109) (by norm_num)
theorem B2690981 : Blo 1792097 2690981 := bbase (se 4 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 2690981 = 504559) (by norm_num)
theorem B5107637 : Blo 1792097 5107637 := bbase (se 5 (by rfl) ⟨239420, by rfl⟩ : syracuseStep 5107637 = 478841) (by norm_num)
theorem B2691005 : Blo 1792097 2691005 := bbase (se 3 (by rfl) ⟨504563, by rfl⟩ : syracuseStep 2691005 = 1009127) (by norm_num)
theorem B4034501 : Blo 1792097 4034501 := bbase (se 4 (by rfl) ⟨378234, by rfl⟩ : syracuseStep 4034501 = 756469) (by norm_num)
theorem B10211285 : Blo 1792097 10211285 := bbase (se 7 (by rfl) ⟨119663, by rfl⟩ : syracuseStep 10211285 = 239327) (by norm_num)
theorem B2691029 : Blo 1792097 2691029 := bbase (se 7 (by rfl) ⟨31535, by rfl⟩ : syracuseStep 2691029 = 63071) (by norm_num)
theorem B3026909 : Blo 1792097 3026909 := bbase (se 3 (by rfl) ⟨567545, by rfl⟩ : syracuseStep 3026909 = 1135091) (by norm_num)
theorem B3067885 : Blo 1792097 3067885 := bbase (se 3 (by rfl) ⟨575228, by rfl⟩ : syracuseStep 3067885 = 1150457) (by norm_num)
theorem B2691053 : Blo 1792097 2691053 := bbase (se 3 (by rfl) ⟨504572, by rfl⟩ : syracuseStep 2691053 = 1009145) (by norm_num)
theorem B6049781 : Blo 1792097 6049781 := bbase (se 5 (by rfl) ⟨283583, by rfl⟩ : syracuseStep 6049781 = 567167) (by norm_num)
theorem B5451781 : Blo 1792097 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B2691077 : Blo 1792097 2691077 := bbase (se 4 (by rfl) ⟨252288, by rfl⟩ : syracuseStep 2691077 = 504577) (by norm_num)
theorem B4034573 : Blo 1792097 4034573 := bbase (se 3 (by rfl) ⟨756482, by rfl⟩ : syracuseStep 4034573 = 1512965) (by norm_num)
theorem B2691101 : Blo 1792097 2691101 := bbase (se 3 (by rfl) ⟨504581, by rfl⟩ : syracuseStep 2691101 = 1009163) (by norm_num)
theorem B6811685 : Blo 1792097 6811685 := bbase (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) (by norm_num)
theorem B4427821 : Blo 1792097 4427821 := bbase (se 3 (by rfl) ⟨830216, by rfl⟩ : syracuseStep 4427821 = 1660433) (by norm_num)
theorem B2691125 : Blo 1792097 2691125 := bbase (se 5 (by rfl) ⟨126146, by rfl⟩ : syracuseStep 2691125 = 252293) (by norm_num)
theorem B3403853 : Blo 1792097 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B4034645 : Blo 1792097 4034645 := bbase (se 8 (by rfl) ⟨23640, by rfl⟩ : syracuseStep 4034645 = 47281) (by norm_num)
theorem B3027037 : Blo 1792097 3027037 := bbase (se 3 (by rfl) ⟨567569, by rfl⟩ : syracuseStep 3027037 = 1135139) (by norm_num)
theorem B2551933 : Blo 1792097 2551933 := bbase (se 3 (by rfl) ⟨478487, by rfl⟩ : syracuseStep 2551933 = 956975) (by norm_num)
theorem B4034717 : Blo 1792097 4034717 := bbase (se 3 (by rfl) ⟨756509, by rfl⟩ : syracuseStep 4034717 = 1513019) (by norm_num)
theorem B3829933 : Blo 1792097 3829933 := bbase (se 3 (by rfl) ⟨718112, by rfl⟩ : syracuseStep 3829933 = 1436225) (by norm_num)
theorem B3027125 : Blo 1792097 3027125 := bbase (se 5 (by rfl) ⟨141896, by rfl⟩ : syracuseStep 3027125 = 283793) (by norm_num)
theorem B22974677 : Blo 1792097 22974677 := bbase (se 7 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 22974677 = 538469) (by norm_num)
theorem B4034789 : Blo 1792097 4034789 := bbase (se 4 (by rfl) ⟨378261, by rfl⟩ : syracuseStep 4034789 = 756523) (by norm_num)
theorem B4034861 : Blo 1792097 4034861 := bbase (se 3 (by rfl) ⟨756536, by rfl⟩ : syracuseStep 4034861 = 1513073) (by norm_num)
theorem B3027253 : Blo 1792097 3027253 := bbase (se 5 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 3027253 = 283805) (by norm_num)
theorem B4034933 : Blo 1792097 4034933 := bbase (se 5 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 4034933 = 378275) (by norm_num)
theorem B3027341 : Blo 1792097 3027341 := bbase (se 3 (by rfl) ⟨567626, by rfl⟩ : syracuseStep 3027341 = 1135253) (by norm_num)
theorem B6050213 : Blo 1792097 6050213 := bbase (se 4 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 6050213 = 1134415) (by norm_num)
theorem B4035005 : Blo 1792097 4035005 := bbase (se 3 (by rfl) ⟨756563, by rfl⟩ : syracuseStep 4035005 = 1513127) (by norm_num)
theorem B2183653 : Blo 1792097 2183653 := bbase (se 4 (by rfl) ⟨204717, by rfl⟩ : syracuseStep 2183653 = 409435) (by norm_num)
theorem B4035077 : Blo 1792097 4035077 := bbase (se 4 (by rfl) ⟨378288, by rfl⟩ : syracuseStep 4035077 = 756577) (by norm_num)
theorem B3027469 : Blo 1792097 3027469 := bbase (se 3 (by rfl) ⟨567650, by rfl⟩ : syracuseStep 3027469 = 1135301) (by norm_num)
theorem B4035149 : Blo 1792097 4035149 := bbase (se 3 (by rfl) ⟨756590, by rfl⟩ : syracuseStep 4035149 = 1513181) (by norm_num)
theorem B5108309 : Blo 1792097 5108309 := bbase (se 8 (by rfl) ⟨29931, by rfl⟩ : syracuseStep 5108309 = 59863) (by norm_num)
theorem B9695861 : Blo 1792097 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B3592837 : Blo 1792097 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B5526149 : Blo 1792097 5526149 := bbase (se 4 (by rfl) ⟨518076, by rfl⟩ : syracuseStep 5526149 = 1036153) (by norm_num)
theorem B4035221 : Blo 1792097 4035221 := bbase (se 6 (by rfl) ⟨94575, by rfl⟩ : syracuseStep 4035221 = 189151) (by norm_num)
theorem B3830429 : Blo 1792097 3830429 := bbase (se 3 (by rfl) ⟨718205, by rfl⟩ : syracuseStep 3830429 = 1436411) (by norm_num)
theorem B9081557 : Blo 1792097 9081557 := bbase (se 7 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 9081557 = 212849) (by norm_num)
theorem B4035293 : Blo 1792097 4035293 := bbase (se 3 (by rfl) ⟨756617, by rfl⟩ : syracuseStep 4035293 = 1513235) (by norm_num)
theorem B4035365 : Blo 1792097 4035365 := bbase (se 4 (by rfl) ⟨378315, by rfl⟩ : syracuseStep 4035365 = 756631) (by norm_num)
theorem B3404605 : Blo 1792097 3404605 := bbase (se 3 (by rfl) ⟨638363, by rfl⟩ : syracuseStep 3404605 = 1276727) (by norm_num)
theorem B7656277 : Blo 1792097 7656277 := bbase (se 9 (by rfl) ⟨22430, by rfl⟩ : syracuseStep 7656277 = 44861) (by norm_num)
theorem B6050645 : Blo 1792097 6050645 := bbase (se 9 (by rfl) ⟨17726, by rfl⟩ : syracuseStep 6050645 = 35453) (by norm_num)
theorem B11490133 : Blo 1792097 11490133 := bbase (se 9 (by rfl) ⟨33662, by rfl⟩ : syracuseStep 11490133 = 67325) (by norm_num)
theorem B4035437 : Blo 1792097 4035437 := bbase (se 3 (by rfl) ⟨756644, by rfl⟩ : syracuseStep 4035437 = 1513289) (by norm_num)
theorem B2872181 : Blo 1792097 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B2552725 : Blo 1792097 2552725 := bbase (se 6 (by rfl) ⟨59829, by rfl⟩ : syracuseStep 2552725 = 119659) (by norm_num)
theorem B4035509 : Blo 1792097 4035509 := bbase (se 5 (by rfl) ⟨189164, by rfl⟩ : syracuseStep 4035509 = 378329) (by norm_num)
theorem B13620149 : Blo 1792097 13620149 := bbase (se 5 (by rfl) ⟨638444, by rfl⟩ : syracuseStep 13620149 = 1276889) (by norm_num)
theorem B3404749 : Blo 1792097 3404749 := bbase (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) (by norm_num)
theorem B9204725 : Blo 1792097 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B4035581 : Blo 1792097 4035581 := bbase (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) (by norm_num)
theorem B5108741 : Blo 1792097 5108741 := bbase (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) (by norm_num)
theorem B1913873 : Blo 1792097 1913873 := bbase (se 2 (by rfl) ⟨717702, by rfl⟩ : syracuseStep 1913873 = 1435405) (by norm_num)
theorem B3879989 : Blo 1792097 3879989 := bbase (se 5 (by rfl) ⟨181874, by rfl⟩ : syracuseStep 3879989 = 363749) (by norm_num)
theorem B4035653 : Blo 1792097 4035653 := bbase (se 4 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 4035653 = 756685) (by norm_num)
theorem B24540245 : Blo 1792097 24540245 := bbase (se 8 (by rfl) ⟨143790, by rfl⟩ : syracuseStep 24540245 = 287581) (by norm_num)
theorem B3404909 : Blo 1792097 3404909 := bbase (se 3 (by rfl) ⟨638420, by rfl⟩ : syracuseStep 3404909 = 1276841) (by norm_num)
theorem B9073781 : Blo 1792097 9073781 := bbase (se 5 (by rfl) ⟨425333, by rfl⟩ : syracuseStep 9073781 = 850667) (by norm_num)
theorem B4846709 : Blo 1792097 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B4306061 : Blo 1792097 4306061 := bbase (se 3 (by rfl) ⟨807386, by rfl⟩ : syracuseStep 4306061 = 1614773) (by norm_num)
theorem B4035725 : Blo 1792097 4035725 := bbase (se 3 (by rfl) ⟨756698, by rfl⟩ : syracuseStep 4035725 = 1513397) (by norm_num)
theorem B4035797 : Blo 1792097 4035797 := bbase (se 7 (by rfl) ⟨47294, by rfl⟩ : syracuseStep 4035797 = 94589) (by norm_num)
theorem B2553061 : Blo 1792097 2553061 := bbase (se 4 (by rfl) ⟨239349, by rfl⟩ : syracuseStep 2553061 = 478699) (by norm_num)
theorem B3405053 : Blo 1792097 3405053 := bbase (se 3 (by rfl) ⟨638447, by rfl⟩ : syracuseStep 3405053 = 1276895) (by norm_num)
theorem B6051077 : Blo 1792097 6051077 := bbase (se 4 (by rfl) ⟨567288, by rfl⟩ : syracuseStep 6051077 = 1134577) (by norm_num)
theorem B1914121 : Blo 1792097 1914121 := bbase (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) (by norm_num)
theorem B4035869 : Blo 1792097 4035869 := bbase (se 3 (by rfl) ⟨756725, by rfl⟩ : syracuseStep 4035869 = 1513451) (by norm_num)
theorem B13612373 : Blo 1792097 13612373 := bbase (se 13 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 13612373 = 4985) (by norm_num)
theorem B4035941 : Blo 1792097 4035941 := bbase (se 4 (by rfl) ⟨378369, by rfl⟩ : syracuseStep 4035941 = 756739) (by norm_num)
theorem B2872693 : Blo 1792097 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B8181157 : Blo 1792097 8181157 := bbase (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) (by norm_num)
theorem B2184617 : Blo 1792097 2184617 := bbase (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) (by norm_num)
theorem B4036013 : Blo 1792097 4036013 := bbase (se 3 (by rfl) ⟨756752, by rfl⟩ : syracuseStep 4036013 = 1513505) (by norm_num)
theorem B2553277 : Blo 1792097 2553277 := bbase (se 3 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 2553277 = 957479) (by norm_num)
theorem B4036085 : Blo 1792097 4036085 := bbase (se 5 (by rfl) ⟨189191, by rfl⟩ : syracuseStep 4036085 = 378383) (by norm_num)
theorem B10909205 : Blo 1792097 10909205 := bbase (se 6 (by rfl) ⟨255684, by rfl⟩ : syracuseStep 10909205 = 511369) (by norm_num)
theorem B3831317 : Blo 1792097 3831317 := bbase (se 6 (by rfl) ⟨89796, by rfl⟩ : syracuseStep 3831317 = 179593) (by norm_num)
theorem B3405341 : Blo 1792097 3405341 := bbase (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) (by norm_num)
theorem B4036157 : Blo 1792097 4036157 := bbase (se 3 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 4036157 = 1513559) (by norm_num)
theorem B6805093 : Blo 1792097 6805093 := bbase (se 4 (by rfl) ⟨637977, by rfl⟩ : syracuseStep 6805093 = 1275955) (by norm_num)
theorem B4912757 : Blo 1792097 4912757 := bbase (se 5 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 4912757 = 460571) (by norm_num)
theorem B4036229 : Blo 1792097 4036229 := bbase (se 4 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 4036229 = 756793) (by norm_num)
theorem B3831437 : Blo 1792097 3831437 := bbase (se 3 (by rfl) ⟨718394, by rfl⟩ : syracuseStep 3831437 = 1436789) (by norm_num)
theorem B6051509 : Blo 1792097 6051509 := bbase (se 5 (by rfl) ⟨283664, by rfl⟩ : syracuseStep 6051509 = 567329) (by norm_num)
theorem B3405493 : Blo 1792097 3405493 := bbase (se 5 (by rfl) ⟨159632, by rfl⟩ : syracuseStep 3405493 = 319265) (by norm_num)
theorem B1914565 : Blo 1792097 1914565 := bbase (se 4 (by rfl) ⟨179490, by rfl⟩ : syracuseStep 1914565 = 358981) (by norm_num)
theorem B4036301 : Blo 1792097 4036301 := bbase (se 3 (by rfl) ⟨756806, by rfl⟩ : syracuseStep 4036301 = 1513613) (by norm_num)
theorem B1914625 : Blo 1792097 1914625 := bbase (se 2 (by rfl) ⟨717984, by rfl⟩ : syracuseStep 1914625 = 1435969) (by norm_num)
theorem B4036373 : Blo 1792097 4036373 := bbase (se 6 (by rfl) ⟨94602, by rfl⟩ : syracuseStep 4036373 = 189205) (by norm_num)
theorem B2553653 : Blo 1792097 2553653 := bbase (se 5 (by rfl) ⟨119702, by rfl⟩ : syracuseStep 2553653 = 239405) (by norm_num)
theorem B4036445 : Blo 1792097 4036445 := bbase (se 3 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 4036445 = 1513667) (by norm_num)
theorem B6805397 : Blo 1792097 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B3274661 : Blo 1792097 3274661 := bbase (se 4 (by rfl) ⟨306999, by rfl⟩ : syracuseStep 3274661 = 613999) (by norm_num)
theorem B4036517 : Blo 1792097 4036517 := bbase (se 4 (by rfl) ⟨378423, by rfl⟩ : syracuseStep 4036517 = 756847) (by norm_num)
theorem B3405797 : Blo 1792097 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B4036589 : Blo 1792097 4036589 := bbase (se 3 (by rfl) ⟨756860, by rfl⟩ : syracuseStep 4036589 = 1513721) (by norm_num)
theorem B2299909 : Blo 1792097 2299909 := bbase (se 4 (by rfl) ⟨215616, by rfl⟩ : syracuseStep 2299909 = 431233) (by norm_num)
theorem B4036661 : Blo 1792097 4036661 := bbase (se 5 (by rfl) ⟨189218, by rfl⟩ : syracuseStep 4036661 = 378437) (by norm_num)
theorem B1914941 : Blo 1792097 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B3881029 : Blo 1792097 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B17234005 : Blo 1792097 17234005 := bbase (se 8 (by rfl) ⟨100980, by rfl⟩ : syracuseStep 17234005 = 201961) (by norm_num)
theorem B25860181 : Blo 1792097 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B6051941 : Blo 1792097 6051941 := bbase (se 4 (by rfl) ⟨567369, by rfl⟩ : syracuseStep 6051941 = 1134739) (by norm_num)
theorem B4536445 : Blo 1792097 4536445 := bbase (se 3 (by rfl) ⟨850583, by rfl⟩ : syracuseStep 4536445 = 1701167) (by norm_num)
theorem B4536557 : Blo 1792097 4536557 := bbase (se 3 (by rfl) ⟨850604, by rfl⟩ : syracuseStep 4536557 = 1701209) (by norm_num)
theorem B24254741 : Blo 1792097 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B13277525 : Blo 1792097 13277525 := bbase (se 10 (by rfl) ⟨19449, by rfl⟩ : syracuseStep 13277525 = 38899) (by norm_num)
theorem B2873693 : Blo 1792097 2873693 := bbase (se 3 (by rfl) ⟨538817, by rfl⟩ : syracuseStep 2873693 = 1077635) (by norm_num)
theorem B9075077 : Blo 1792097 9075077 := bbase (se 4 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 9075077 = 1701577) (by norm_num)
theorem B4536749 : Blo 1792097 4536749 := bbase (se 3 (by rfl) ⟨850640, by rfl⟩ : syracuseStep 4536749 = 1701281) (by norm_num)
theorem B2726389 : Blo 1792097 2726389 := bbase (se 5 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 2726389 = 255599) (by norm_num)
theorem B1915385 : Blo 1792097 1915385 := bbase (se 2 (by rfl) ⟨718269, by rfl⟩ : syracuseStep 1915385 = 1436539) (by norm_num)
theorem B6052373 : Blo 1792097 6052373 := bbase (se 6 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 6052373 = 283705) (by norm_num)
theorem B1915445 : Blo 1792097 1915445 := bbase (se 5 (by rfl) ⟨89786, by rfl⟩ : syracuseStep 1915445 = 179573) (by norm_num)
theorem B1940089 : Blo 1792097 1940089 := bbase (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) (by norm_num)
theorem B1915573 : Blo 1792097 1915573 := bbase (se 5 (by rfl) ⟨89792, by rfl⟩ : syracuseStep 1915573 = 179585) (by norm_num)
theorem B5741285 : Blo 1792097 5741285 := bbase (se 4 (by rfl) ⟨538245, by rfl⟩ : syracuseStep 5741285 = 1076491) (by norm_num)
theorem B4537093 : Blo 1792097 4537093 := bbase (se 4 (by rfl) ⟨425352, by rfl⟩ : syracuseStep 4537093 = 850705) (by norm_num)
theorem B2456357 : Blo 1792097 2456357 := bbase (se 4 (by rfl) ⟨230283, by rfl⟩ : syracuseStep 2456357 = 460567) (by norm_num)
theorem B2153261 : Blo 1792097 2153261 := bbase (se 3 (by rfl) ⟨403736, by rfl⟩ : syracuseStep 2153261 = 807473) (by norm_num)
theorem B8616773 : Blo 1792097 8616773 := bbase (se 4 (by rfl) ⟨807822, by rfl⟩ : syracuseStep 8616773 = 1615645) (by norm_num)
theorem B4537205 : Blo 1792097 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B2423749 : Blo 1792097 2423749 := bbase (se 4 (by rfl) ⟨227226, by rfl⟩ : syracuseStep 2423749 = 454453) (by norm_num)
theorem B6052805 : Blo 1792097 6052805 := bbase (se 4 (by rfl) ⟨567450, by rfl⟩ : syracuseStep 6052805 = 1134901) (by norm_num)
theorem B2268157 : Blo 1792097 2268157 := bbase (se 3 (by rfl) ⟨425279, by rfl⟩ : syracuseStep 2268157 = 850559) (by norm_num)
theorem B2300977 : Blo 1792097 2300977 := bbase (se 2 (by rfl) ⟨862866, by rfl⟩ : syracuseStep 2300977 = 1725733) (by norm_num)
theorem B4537397 : Blo 1792097 4537397 := bbase (se 5 (by rfl) ⟨212690, by rfl⟩ : syracuseStep 4537397 = 425381) (by norm_num)
theorem B2268253 : Blo 1792097 2268253 := bbase (se 3 (by rfl) ⟨425297, by rfl⟩ : syracuseStep 2268253 = 850595) (by norm_num)
theorem B2153569 : Blo 1792097 2153569 := bbase (se 2 (by rfl) ⟨807588, by rfl⟩ : syracuseStep 2153569 = 1615177) (by norm_num)
theorem B2301049 : Blo 1792097 2301049 := bbase (se 2 (by rfl) ⟨862893, by rfl⟩ : syracuseStep 2301049 = 1725787) (by norm_num)
theorem B2153597 : Blo 1792097 2153597 := bbase (se 3 (by rfl) ⟨403799, by rfl⟩ : syracuseStep 2153597 = 807599) (by norm_num)
theorem B27589781 : Blo 1792097 27589781 := bbase (se 6 (by rfl) ⟨646635, by rfl⟩ : syracuseStep 27589781 = 1293271) (by norm_num)
theorem B8617157 : Blo 1792097 8617157 := bbase (se 4 (by rfl) ⟨807858, by rfl⟩ : syracuseStep 8617157 = 1615717) (by norm_num)
theorem B2268425 : Blo 1792097 2268425 := bbase (se 2 (by rfl) ⟨850659, by rfl⟩ : syracuseStep 2268425 = 1701319) (by norm_num)
theorem B2268481 : Blo 1792097 2268481 := bbase (se 2 (by rfl) ⟨850680, by rfl⟩ : syracuseStep 2268481 = 1701361) (by norm_num)
theorem B1940809 : Blo 1792097 1940809 := bbase (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) (by norm_num)
theorem B6053237 : Blo 1792097 6053237 := bbase (se 5 (by rfl) ⟨283745, by rfl⟩ : syracuseStep 6053237 = 567491) (by norm_num)
theorem B4537741 : Blo 1792097 4537741 := bbase (se 3 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 4537741 = 1701653) (by norm_num)
theorem B2268577 : Blo 1792097 2268577 := bbase (se 2 (by rfl) ⟨850716, by rfl⟩ : syracuseStep 2268577 = 1701433) (by norm_num)
theorem B31071701 : Blo 1792097 31071701 := bbase (se 7 (by rfl) ⟨364121, by rfl⟩ : syracuseStep 31071701 = 728243) (by norm_num)
theorem B4849141 : Blo 1792097 4849141 := bbase (se 5 (by rfl) ⟨227303, by rfl⟩ : syracuseStep 4849141 = 454607) (by norm_num)
theorem B4537853 : Blo 1792097 4537853 := bbase (se 3 (by rfl) ⟨850847, by rfl⟩ : syracuseStep 4537853 = 1701695) (by norm_num)
theorem B4308493 : Blo 1792097 4308493 := bbase (se 3 (by rfl) ⟨807842, by rfl⟩ : syracuseStep 4308493 = 1615685) (by norm_num)
theorem B8175173 : Blo 1792097 8175173 := bbase (se 4 (by rfl) ⟨766422, by rfl⟩ : syracuseStep 8175173 = 1532845) (by norm_num)
theorem B2268749 : Blo 1792097 2268749 := bbase (se 3 (by rfl) ⟨425390, by rfl⟩ : syracuseStep 2268749 = 850781) (by norm_num)
theorem B2154097 : Blo 1792097 2154097 := bbase (se 2 (by rfl) ⟨807786, by rfl⟩ : syracuseStep 2154097 = 1615573) (by norm_num)
theorem B5742197 : Blo 1792097 5742197 := bbase (se 5 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 5742197 = 538331) (by norm_num)
theorem B2268805 : Blo 1792097 2268805 := bbase (se 4 (by rfl) ⟨212700, by rfl⟩ : syracuseStep 2268805 = 425401) (by norm_num)
theorem B2727557 : Blo 1792097 2727557 := bbase (se 4 (by rfl) ⟨255708, by rfl⟩ : syracuseStep 2727557 = 511417) (by norm_num)
theorem B9076373 : Blo 1792097 9076373 := bbase (se 6 (by rfl) ⟨212727, by rfl⟩ : syracuseStep 9076373 = 425455) (by norm_num)
theorem B4538045 : Blo 1792097 4538045 := bbase (se 3 (by rfl) ⟨850883, by rfl⟩ : syracuseStep 4538045 = 1701767) (by norm_num)
theorem B2268901 : Blo 1792097 2268901 := bbase (se 4 (by rfl) ⟨212709, by rfl⟩ : syracuseStep 2268901 = 425419) (by norm_num)
theorem B9699061 : Blo 1792097 9699061 := bbase (se 5 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 9699061 = 909287) (by norm_num)
theorem B7659269 : Blo 1792097 7659269 := bbase (se 4 (by rfl) ⟨718056, by rfl⟩ : syracuseStep 7659269 = 1436113) (by norm_num)
theorem B6053669 : Blo 1792097 6053669 := bbase (se 4 (by rfl) ⟨567531, by rfl⟩ : syracuseStep 6053669 = 1135063) (by norm_num)
theorem B1941293 : Blo 1792097 1941293 := bbase (se 3 (by rfl) ⟨363992, by rfl⟩ : syracuseStep 1941293 = 727985) (by norm_num)
theorem B5103445 : Blo 1792097 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B10207093 : Blo 1792097 10207093 := bbase (se 5 (by rfl) ⟨478457, by rfl⟩ : syracuseStep 10207093 = 956915) (by norm_num)
theorem B2269073 : Blo 1792097 2269073 := bbase (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) (by norm_num)
theorem B4087741 : Blo 1792097 4087741 := bbase (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) (by norm_num)
theorem B2269129 : Blo 1792097 2269129 := bbase (se 2 (by rfl) ⟨850923, by rfl⟩ : syracuseStep 2269129 = 1701847) (by norm_num)
theorem B10346453 : Blo 1792097 10346453 := bbase (se 7 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 10346453 = 242495) (by norm_num)
theorem B6807509 : Blo 1792097 6807509 := bbase (se 7 (by rfl) ⟨79775, by rfl⟩ : syracuseStep 6807509 = 159551) (by norm_num)
theorem B19390421 : Blo 1792097 19390421 := bbase (se 7 (by rfl) ⟨227231, by rfl⟩ : syracuseStep 19390421 = 454463) (by norm_num)
theorem B1794051 : Blo 1792097 1794051 := bstep (se 1 (by rfl) ⟨1345538, by rfl⟩ : syracuseStep 1794051 = 2691077) B2691077
theorem B1794067 : Blo 1792097 1794067 := bstep (se 1 (by rfl) ⟨1345550, by rfl⟩ : syracuseStep 1794067 = 2691101) B2691101
theorem B1794083 : Blo 1792097 1794083 := bstep (se 1 (by rfl) ⟨1345562, by rfl⟩ : syracuseStep 1794083 = 2691125) B2691125
theorem B5103661 : Blo 1792097 5103661 := bstep (se 3 (by rfl) ⟨956936, by rfl⟩ : syracuseStep 5103661 = 1913873) B1913873
theorem B2269235 : Blo 1792097 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B19660853 : Blo 1792097 19660853 := bstep (se 5 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 19660853 = 1843205) B1843205
theorem B2588755 : Blo 1792097 2588755 := bstep (se 1 (by rfl) ⟨1941566, by rfl⟩ : syracuseStep 2588755 = 3883133) B3883133
theorem B22978673 : Blo 1792097 22978673 := bstep (se 2 (by rfl) ⟨8617002, by rfl⟩ : syracuseStep 22978673 = 17234005) B17234005
theorem B34480241 : Blo 1792097 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B4538531 : Blo 1792097 4538531 := bstep (se 1 (by rfl) ⟨3403898, by rfl⟩ : syracuseStep 4538531 = 6807797) B6807797
theorem B73572749 : Blo 1792097 73572749 := bstep (se 3 (by rfl) ⟨13794890, by rfl⟩ : syracuseStep 73572749 = 27589781) B27589781
theorem B6463907 : Blo 1792097 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B6054317 : Blo 1792097 6054317 := bstep (se 3 (by rfl) ⟨1135184, by rfl⟩ : syracuseStep 6054317 = 2270369) B2270369
theorem B7659953 : Blo 1792097 7659953 := bstep (se 2 (by rfl) ⟨2872482, by rfl⟩ : syracuseStep 7659953 = 5744965) B5744965
theorem B2802131 : Blo 1792097 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B6054371 : Blo 1792097 6054371 := bstep (se 1 (by rfl) ⟨4540778, by rfl⟩ : syracuseStep 6054371 = 9081557) B9081557
theorem B15311429 : Blo 1792097 15311429 := bstep (se 4 (by rfl) ⟨1435446, by rfl⟩ : syracuseStep 15311429 = 2870893) B2870893
theorem B6136483 : Blo 1792097 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B16360163 : Blo 1792097 16360163 := bstep (se 1 (by rfl) ⟨12270122, by rfl⟩ : syracuseStep 16360163 = 24540245) B24540245
theorem B6054641 : Blo 1792097 6054641 := bstep (se 2 (by rfl) ⟨2270490, by rfl⟩ : syracuseStep 6054641 = 4540981) B4540981
theorem B2269939 : Blo 1792097 2269939 := bstep (se 1 (by rfl) ⟨1702454, by rfl⟩ : syracuseStep 2269939 = 3404909) B3404909
theorem B2270035 : Blo 1792097 2270035 := bstep (se 1 (by rfl) ⟨1702526, by rfl⟩ : syracuseStep 2270035 = 3405053) B3405053
theorem B35406733 : Blo 1792097 35406733 := bstep (se 3 (by rfl) ⟨6638762, by rfl⟩ : syracuseStep 35406733 = 13277525) B13277525
theorem B4309955 : Blo 1792097 4309955 := bstep (se 1 (by rfl) ⟨3232466, by rfl⟩ : syracuseStep 4309955 = 6464933) B6464933
theorem B2016211 : Blo 1792097 2016211 := bstep (se 1 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 2016211 = 3024317) B3024317
theorem B5104721 : Blo 1792097 5104721 := bstep (se 2 (by rfl) ⟨1914270, by rfl⟩ : syracuseStep 5104721 = 3828541) B3828541
theorem B4539473 : Blo 1792097 4539473 := bstep (se 2 (by rfl) ⟨1702302, by rfl⟩ : syracuseStep 4539473 = 3404605) B3404605
theorem B2016355 : Blo 1792097 2016355 := bstep (se 1 (by rfl) ⟨1512266, by rfl⟩ : syracuseStep 2016355 = 3024533) B3024533
theorem B5825645 : Blo 1792097 5825645 := bstep (se 3 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 5825645 = 2184617) B2184617
theorem B10208369 : Blo 1792097 10208369 := bstep (se 2 (by rfl) ⟨3828138, by rfl⟩ : syracuseStep 10208369 = 7656277) B7656277
theorem B15320177 : Blo 1792097 15320177 := bstep (se 2 (by rfl) ⟨5745066, by rfl⟩ : syracuseStep 15320177 = 11490133) B11490133
theorem B4539523 : Blo 1792097 4539523 := bstep (se 1 (by rfl) ⟨3404642, by rfl⟩ : syracuseStep 4539523 = 6809285) B6809285
theorem B2688161 : Blo 1792097 2688161 := bstep (se 2 (by rfl) ⟨1008060, by rfl⟩ : syracuseStep 2688161 = 2016121) B2016121
theorem B2688179 : Blo 1792097 2688179 := bstep (se 1 (by rfl) ⟨2016134, by rfl⟩ : syracuseStep 2688179 = 4032269) B4032269
theorem B2688209 : Blo 1792097 2688209 := bstep (se 2 (by rfl) ⟨1008078, by rfl⟩ : syracuseStep 2688209 = 2016157) B2016157
theorem B2688227 : Blo 1792097 2688227 := bstep (se 1 (by rfl) ⟨2016170, by rfl⟩ : syracuseStep 2688227 = 4032341) B4032341
theorem B2016499 : Blo 1792097 2016499 := bstep (se 1 (by rfl) ⟨1512374, by rfl⟩ : syracuseStep 2016499 = 3024749) B3024749
theorem B2688257 : Blo 1792097 2688257 := bstep (se 2 (by rfl) ⟨1008096, by rfl⟩ : syracuseStep 2688257 = 2016193) B2016193
theorem B4539665 : Blo 1792097 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B2688275 : Blo 1792097 2688275 := bstep (se 1 (by rfl) ⟨2016206, by rfl⟩ : syracuseStep 2688275 = 4032413) B4032413
theorem B2688305 : Blo 1792097 2688305 := bstep (se 2 (by rfl) ⟨1008114, by rfl⟩ : syracuseStep 2688305 = 2016229) B2016229
theorem B22971701 : Blo 1792097 22971701 := bstep (se 5 (by rfl) ⟨1076798, by rfl⟩ : syracuseStep 22971701 = 2153597) B2153597
theorem B2688323 : Blo 1792097 2688323 := bstep (se 1 (by rfl) ⟨2016242, by rfl⟩ : syracuseStep 2688323 = 4032485) B4032485
theorem B2270531 : Blo 1792097 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B3024209 : Blo 1792097 3024209 := bstep (se 2 (by rfl) ⟨1134078, by rfl⟩ : syracuseStep 3024209 = 2268157) B2268157
theorem B2688353 : Blo 1792097 2688353 := bstep (se 2 (by rfl) ⟨1008132, by rfl⟩ : syracuseStep 2688353 = 2016265) B2016265
theorem B2688371 : Blo 1792097 2688371 := bstep (se 1 (by rfl) ⟨2016278, by rfl⟩ : syracuseStep 2688371 = 4032557) B4032557
theorem B2016643 : Blo 1792097 2016643 := bstep (se 1 (by rfl) ⟨1512482, by rfl⟩ : syracuseStep 2016643 = 3024965) B3024965
theorem B2688401 : Blo 1792097 2688401 := bstep (se 2 (by rfl) ⟨1008150, by rfl⟩ : syracuseStep 2688401 = 2016301) B2016301
theorem B2688419 : Blo 1792097 2688419 := bstep (se 1 (by rfl) ⟨2016314, by rfl⟩ : syracuseStep 2688419 = 4032629) B4032629
theorem B2688449 : Blo 1792097 2688449 := bstep (se 2 (by rfl) ⟨1008168, by rfl⟩ : syracuseStep 2688449 = 2016337) B2016337
theorem B3024337 : Blo 1792097 3024337 := bstep (se 2 (by rfl) ⟨1134126, by rfl⟩ : syracuseStep 3024337 = 2268253) B2268253
theorem B2688467 : Blo 1792097 2688467 := bstep (se 1 (by rfl) ⟨2016350, by rfl⟩ : syracuseStep 2688467 = 4032701) B4032701
theorem B2688497 : Blo 1792097 2688497 := bstep (se 2 (by rfl) ⟨1008186, by rfl⟩ : syracuseStep 2688497 = 2016373) B2016373
theorem B3024371 : Blo 1792097 3024371 := bstep (se 1 (by rfl) ⟨2268278, by rfl⟩ : syracuseStep 3024371 = 4536557) B4536557
theorem B2688515 : Blo 1792097 2688515 := bstep (se 1 (by rfl) ⟨2016386, by rfl⟩ : syracuseStep 2688515 = 4032773) B4032773
theorem B21800461 : Blo 1792097 21800461 := bstep (se 3 (by rfl) ⟨4087586, by rfl⟩ : syracuseStep 21800461 = 8175173) B8175173
theorem B2016787 : Blo 1792097 2016787 := bstep (se 1 (by rfl) ⟨1512590, by rfl⟩ : syracuseStep 2016787 = 3025181) B3025181
theorem B2688545 : Blo 1792097 2688545 := bstep (se 2 (by rfl) ⟨1008204, by rfl⟩ : syracuseStep 2688545 = 2016409) B2016409
theorem B2688563 : Blo 1792097 2688563 := bstep (se 1 (by rfl) ⟨2016422, by rfl⟩ : syracuseStep 2688563 = 4032845) B4032845
theorem B2688593 : Blo 1792097 2688593 := bstep (se 2 (by rfl) ⟨1008222, by rfl⟩ : syracuseStep 2688593 = 2016445) B2016445
theorem B2688611 : Blo 1792097 2688611 := bstep (se 1 (by rfl) ⟨2016458, by rfl⟩ : syracuseStep 2688611 = 4032917) B4032917
theorem B3024499 : Blo 1792097 3024499 := bstep (se 1 (by rfl) ⟨2268374, by rfl⟩ : syracuseStep 3024499 = 4536749) B4536749
theorem B2688641 : Blo 1792097 2688641 := bstep (se 2 (by rfl) ⟨1008240, by rfl⟩ : syracuseStep 2688641 = 2016481) B2016481
theorem B2688659 : Blo 1792097 2688659 := bstep (se 1 (by rfl) ⟨2016494, by rfl⟩ : syracuseStep 2688659 = 4032989) B4032989
theorem B2016931 : Blo 1792097 2016931 := bstep (se 1 (by rfl) ⟨1512698, by rfl⟩ : syracuseStep 2016931 = 3025397) B3025397
theorem B2688689 : Blo 1792097 2688689 := bstep (se 2 (by rfl) ⟨1008258, by rfl⟩ : syracuseStep 2688689 = 2016517) B2016517
theorem B2688707 : Blo 1792097 2688707 := bstep (se 1 (by rfl) ⟨2016530, by rfl⟩ : syracuseStep 2688707 = 4033061) B4033061
theorem B2688737 : Blo 1792097 2688737 := bstep (se 2 (by rfl) ⟨1008276, by rfl⟩ : syracuseStep 2688737 = 2016553) B2016553
theorem B5105393 : Blo 1792097 5105393 := bstep (se 2 (by rfl) ⟨1914522, by rfl⟩ : syracuseStep 5105393 = 3829045) B3829045
theorem B2688755 : Blo 1792097 2688755 := bstep (se 1 (by rfl) ⟨2016566, by rfl⟩ : syracuseStep 2688755 = 4033133) B4033133
theorem B3024641 : Blo 1792097 3024641 := bstep (se 2 (by rfl) ⟨1134240, by rfl⟩ : syracuseStep 3024641 = 2268481) B2268481
theorem B2688785 : Blo 1792097 2688785 := bstep (se 2 (by rfl) ⟨1008294, by rfl⟩ : syracuseStep 2688785 = 2016589) B2016589
theorem B2688803 : Blo 1792097 2688803 := bstep (se 1 (by rfl) ⟨2016602, by rfl⟩ : syracuseStep 2688803 = 4033205) B4033205
theorem B4032305 : Blo 1792097 4032305 := bstep (se 2 (by rfl) ⟨1512114, by rfl⟩ : syracuseStep 4032305 = 3024229) B3024229
theorem B2017075 : Blo 1792097 2017075 := bstep (se 1 (by rfl) ⟨1512806, by rfl⟩ : syracuseStep 2017075 = 3025613) B3025613
theorem B2688833 : Blo 1792097 2688833 := bstep (se 2 (by rfl) ⟨1008312, by rfl⟩ : syracuseStep 2688833 = 2016625) B2016625
theorem B4032323 : Blo 1792097 4032323 := bstep (se 1 (by rfl) ⟨3024242, by rfl⟩ : syracuseStep 4032323 = 6048485) B6048485
theorem B2688851 : Blo 1792097 2688851 := bstep (se 1 (by rfl) ⟨2016638, by rfl⟩ : syracuseStep 2688851 = 4033277) B4033277
theorem B2688881 : Blo 1792097 2688881 := bstep (se 2 (by rfl) ⟨1008330, by rfl⟩ : syracuseStep 2688881 = 2016661) B2016661
theorem B9078641 : Blo 1792097 9078641 := bstep (se 2 (by rfl) ⟨3404490, by rfl⟩ : syracuseStep 9078641 = 6808981) B6808981
theorem B3024769 : Blo 1792097 3024769 := bstep (se 2 (by rfl) ⟨1134288, by rfl⟩ : syracuseStep 3024769 = 2268577) B2268577
theorem B2688899 : Blo 1792097 2688899 := bstep (se 1 (by rfl) ⟨2016674, by rfl⟩ : syracuseStep 2688899 = 4033349) B4033349
theorem B5744515 : Blo 1792097 5744515 := bstep (se 1 (by rfl) ⟨4308386, by rfl⟩ : syracuseStep 5744515 = 8616773) B8616773
theorem B2688929 : Blo 1792097 2688929 := bstep (se 2 (by rfl) ⟨1008348, by rfl⟩ : syracuseStep 2688929 = 2016697) B2016697
theorem B3024803 : Blo 1792097 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B2688947 : Blo 1792097 2688947 := bstep (se 1 (by rfl) ⟨2016710, by rfl⟩ : syracuseStep 2688947 = 4033421) B4033421
theorem B2017219 : Blo 1792097 2017219 := bstep (se 1 (by rfl) ⟨1512914, by rfl⟩ : syracuseStep 2017219 = 3025829) B3025829
theorem B2688977 : Blo 1792097 2688977 := bstep (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) B2016733
theorem B49727459 : Blo 1792097 49727459 := bstep (se 1 (by rfl) ⟨37295594, by rfl⟩ : syracuseStep 49727459 = 74591189) B74591189
theorem B2688995 : Blo 1792097 2688995 := bstep (se 1 (by rfl) ⟨2016746, by rfl⟩ : syracuseStep 2688995 = 4033493) B4033493
theorem B6465521 : Blo 1792097 6465521 := bstep (se 2 (by rfl) ⟨2424570, by rfl⟩ : syracuseStep 6465521 = 4849141) B4849141
theorem B2689025 : Blo 1792097 2689025 := bstep (se 2 (by rfl) ⟨1008384, by rfl⟩ : syracuseStep 2689025 = 2016769) B2016769
theorem B3827729 : Blo 1792097 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B2689043 : Blo 1792097 2689043 := bstep (se 1 (by rfl) ⟨2016782, by rfl⟩ : syracuseStep 2689043 = 4033565) B4033565
theorem B5744657 : Blo 1792097 5744657 := bstep (se 2 (by rfl) ⟨2154246, by rfl⟩ : syracuseStep 5744657 = 4308493) B4308493
theorem B3024931 : Blo 1792097 3024931 := bstep (se 1 (by rfl) ⟨2268698, by rfl⟩ : syracuseStep 3024931 = 4537397) B4537397
theorem B2689073 : Blo 1792097 2689073 := bstep (se 2 (by rfl) ⟨1008402, by rfl⟩ : syracuseStep 2689073 = 2016805) B2016805
theorem B2689091 : Blo 1792097 2689091 := bstep (se 1 (by rfl) ⟨2016818, by rfl⟩ : syracuseStep 2689091 = 4033637) B4033637
theorem B4032593 : Blo 1792097 4032593 := bstep (se 2 (by rfl) ⟨1512222, by rfl⟩ : syracuseStep 4032593 = 3024445) B3024445
theorem B2017363 : Blo 1792097 2017363 := bstep (se 1 (by rfl) ⟨1513022, by rfl⟩ : syracuseStep 2017363 = 3026045) B3026045
theorem B2689121 : Blo 1792097 2689121 := bstep (se 2 (by rfl) ⟨1008420, by rfl⟩ : syracuseStep 2689121 = 2016841) B2016841
theorem B4032611 : Blo 1792097 4032611 := bstep (se 1 (by rfl) ⟨3024458, by rfl⟩ : syracuseStep 4032611 = 6048917) B6048917
theorem B15534193 : Blo 1792097 15534193 := bstep (se 2 (by rfl) ⟨5825322, by rfl⟩ : syracuseStep 15534193 = 11650645) B11650645
theorem B2689139 : Blo 1792097 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B5744771 : Blo 1792097 5744771 := bstep (se 1 (by rfl) ⟨4308578, by rfl⟩ : syracuseStep 5744771 = 8617157) B8617157
theorem B6809741 : Blo 1792097 6809741 := bstep (se 3 (by rfl) ⟨1276826, by rfl⟩ : syracuseStep 6809741 = 2553653) B2553653
theorem B2689169 : Blo 1792097 2689169 := bstep (se 2 (by rfl) ⟨1008438, by rfl⟩ : syracuseStep 2689169 = 2016877) B2016877
theorem B2689187 : Blo 1792097 2689187 := bstep (se 1 (by rfl) ⟨2016890, by rfl⟩ : syracuseStep 2689187 = 4033781) B4033781
theorem B3025073 : Blo 1792097 3025073 := bstep (se 2 (by rfl) ⟨1134402, by rfl⟩ : syracuseStep 3025073 = 2268805) B2268805
theorem B2689217 : Blo 1792097 2689217 := bstep (se 2 (by rfl) ⟨1008456, by rfl⟩ : syracuseStep 2689217 = 2016913) B2016913
theorem B2689235 : Blo 1792097 2689235 := bstep (se 1 (by rfl) ⟨2016926, by rfl⟩ : syracuseStep 2689235 = 4033853) B4033853
theorem B75598051 : Blo 1792097 75598051 := bstep (se 1 (by rfl) ⟨56698538, by rfl⟩ : syracuseStep 75598051 = 113397077) B113397077
theorem B2017507 : Blo 1792097 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B2689265 : Blo 1792097 2689265 := bstep (se 2 (by rfl) ⟨1008474, by rfl⟩ : syracuseStep 2689265 = 2016949) B2016949
theorem B4540657 : Blo 1792097 4540657 := bstep (se 2 (by rfl) ⟨1702746, by rfl⟩ : syracuseStep 4540657 = 3405493) B3405493
theorem B2689283 : Blo 1792097 2689283 := bstep (se 1 (by rfl) ⟨2016962, by rfl⟩ : syracuseStep 2689283 = 4033925) B4033925
theorem B2689313 : Blo 1792097 2689313 := bstep (se 2 (by rfl) ⟨1008492, by rfl⟩ : syracuseStep 2689313 = 2016985) B2016985
theorem B3025201 : Blo 1792097 3025201 := bstep (se 2 (by rfl) ⟨1134450, by rfl⟩ : syracuseStep 3025201 = 2268901) B2268901
theorem B2689331 : Blo 1792097 2689331 := bstep (se 1 (by rfl) ⟨2016998, by rfl⟩ : syracuseStep 2689331 = 4033997) B4033997
theorem B2689361 : Blo 1792097 2689361 := bstep (se 2 (by rfl) ⟨1008510, by rfl⟩ : syracuseStep 2689361 = 2017021) B2017021
theorem B3025235 : Blo 1792097 3025235 := bstep (se 1 (by rfl) ⟨2268926, by rfl⟩ : syracuseStep 3025235 = 4537853) B4537853
theorem B2689379 : Blo 1792097 2689379 := bstep (se 1 (by rfl) ⟨2017034, by rfl⟩ : syracuseStep 2689379 = 4034069) B4034069
theorem B4032881 : Blo 1792097 4032881 := bstep (se 2 (by rfl) ⟨1512330, by rfl⟩ : syracuseStep 4032881 = 3024661) B3024661
theorem B2017651 : Blo 1792097 2017651 := bstep (se 1 (by rfl) ⟨1513238, by rfl⟩ : syracuseStep 2017651 = 3026477) B3026477
theorem B2689409 : Blo 1792097 2689409 := bstep (se 2 (by rfl) ⟨1008528, by rfl⟩ : syracuseStep 2689409 = 2017057) B2017057
theorem B4032899 : Blo 1792097 4032899 := bstep (se 1 (by rfl) ⟨3024674, by rfl⟩ : syracuseStep 4032899 = 6049349) B6049349
theorem B2689427 : Blo 1792097 2689427 := bstep (se 1 (by rfl) ⟨2017070, by rfl⟩ : syracuseStep 2689427 = 4034141) B4034141
theorem B3828131 : Blo 1792097 3828131 := bstep (se 1 (by rfl) ⟨2871098, by rfl⟩ : syracuseStep 3828131 = 5742197) B5742197
theorem B2689457 : Blo 1792097 2689457 := bstep (se 2 (by rfl) ⟨1008546, by rfl⟩ : syracuseStep 2689457 = 2017093) B2017093
theorem B2689475 : Blo 1792097 2689475 := bstep (se 1 (by rfl) ⟨2017106, by rfl⟩ : syracuseStep 2689475 = 4034213) B4034213
theorem B3025363 : Blo 1792097 3025363 := bstep (se 1 (by rfl) ⟨2269022, by rfl⟩ : syracuseStep 3025363 = 4538045) B4538045
theorem B2689505 : Blo 1792097 2689505 := bstep (se 2 (by rfl) ⟨1008564, by rfl⟩ : syracuseStep 2689505 = 2017129) B2017129
theorem B13609457 : Blo 1792097 13609457 := bstep (se 2 (by rfl) ⟨5103546, by rfl⟩ : syracuseStep 13609457 = 10207093) B10207093
theorem B2689523 : Blo 1792097 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B5106179 : Blo 1792097 5106179 := bstep (se 1 (by rfl) ⟨3829634, by rfl⟩ : syracuseStep 5106179 = 7659269) B7659269
theorem B2017795 : Blo 1792097 2017795 := bstep (se 1 (by rfl) ⟨1513346, by rfl⟩ : syracuseStep 2017795 = 3026693) B3026693
theorem B4540931 : Blo 1792097 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B2689553 : Blo 1792097 2689553 := bstep (se 2 (by rfl) ⟨1008582, by rfl⟩ : syracuseStep 2689553 = 2017165) B2017165
theorem B41388565 : Blo 1792097 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B10209827 : Blo 1792097 10209827 := bstep (se 1 (by rfl) ⟨7657370, by rfl⟩ : syracuseStep 10209827 = 15314741) B15314741
theorem B2689571 : Blo 1792097 2689571 := bstep (se 1 (by rfl) ⟨2017178, by rfl⟩ : syracuseStep 2689571 = 4034357) B4034357
theorem B2689601 : Blo 1792097 2689601 := bstep (se 2 (by rfl) ⟨1008600, by rfl⟩ : syracuseStep 2689601 = 2017201) B2017201
theorem B16362053 : Blo 1792097 16362053 := bstep (se 4 (by rfl) ⟨1533942, by rfl⟩ : syracuseStep 16362053 = 3067885) B3067885
theorem B5450321 : Blo 1792097 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B2689619 : Blo 1792097 2689619 := bstep (se 1 (by rfl) ⟨2017214, by rfl⟩ : syracuseStep 2689619 = 4034429) B4034429
theorem B3025505 : Blo 1792097 3025505 := bstep (se 2 (by rfl) ⟨1134564, by rfl⟩ : syracuseStep 3025505 = 2269129) B2269129
theorem B2689649 : Blo 1792097 2689649 := bstep (se 2 (by rfl) ⟨1008618, by rfl⟩ : syracuseStep 2689649 = 2017237) B2017237
theorem B2689667 : Blo 1792097 2689667 := bstep (se 1 (by rfl) ⟨2017250, by rfl⟩ : syracuseStep 2689667 = 4034501) B4034501
theorem B4033169 : Blo 1792097 4033169 := bstep (se 2 (by rfl) ⟨1512438, by rfl⟩ : syracuseStep 4033169 = 3024877) B3024877
theorem B2017939 : Blo 1792097 2017939 := bstep (se 1 (by rfl) ⟨1513454, by rfl⟩ : syracuseStep 2017939 = 3026909) B3026909
theorem B2689697 : Blo 1792097 2689697 := bstep (se 2 (by rfl) ⟨1008636, by rfl⟩ : syracuseStep 2689697 = 2017273) B2017273
theorem B4033187 : Blo 1792097 4033187 := bstep (se 1 (by rfl) ⟨3024890, by rfl⟩ : syracuseStep 4033187 = 6049781) B6049781
theorem B3066545 : Blo 1792097 3066545 := bstep (se 2 (by rfl) ⟨1149954, by rfl⟩ : syracuseStep 3066545 = 2299909) B2299909
theorem B7269041 : Blo 1792097 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B2689715 : Blo 1792097 2689715 := bstep (se 1 (by rfl) ⟨2017286, by rfl⟩ : syracuseStep 2689715 = 4034573) B4034573
theorem B4541123 : Blo 1792097 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B2689745 : Blo 1792097 2689745 := bstep (se 2 (by rfl) ⟨1008654, by rfl⟩ : syracuseStep 2689745 = 2017309) B2017309
theorem B3025633 : Blo 1792097 3025633 := bstep (se 2 (by rfl) ⟨1134612, by rfl⟩ : syracuseStep 3025633 = 2269225) B2269225
theorem B2689763 : Blo 1792097 2689763 := bstep (se 1 (by rfl) ⟨2017322, by rfl⟩ : syracuseStep 2689763 = 4034645) B4034645
theorem B2689793 : Blo 1792097 2689793 := bstep (se 2 (by rfl) ⟨1008672, by rfl⟩ : syracuseStep 2689793 = 2017345) B2017345
theorem B3025667 : Blo 1792097 3025667 := bstep (se 1 (by rfl) ⟨2269250, by rfl⟩ : syracuseStep 3025667 = 4538501) B4538501
theorem B2689811 : Blo 1792097 2689811 := bstep (se 1 (by rfl) ⟨2017358, by rfl⟩ : syracuseStep 2689811 = 4034717) B4034717
theorem B2018083 : Blo 1792097 2018083 := bstep (se 1 (by rfl) ⟨1513562, by rfl⟩ : syracuseStep 2018083 = 3027125) B3027125
theorem B2689841 : Blo 1792097 2689841 := bstep (se 2 (by rfl) ⟨1008690, by rfl⟩ : syracuseStep 2689841 = 2017381) B2017381
theorem B2689859 : Blo 1792097 2689859 := bstep (se 1 (by rfl) ⟨2017394, by rfl⟩ : syracuseStep 2689859 = 4034789) B4034789
theorem B5106509 : Blo 1792097 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B6048593 : Blo 1792097 6048593 := bstep (se 2 (by rfl) ⟨2268222, by rfl⟩ : syracuseStep 6048593 = 4536445) B4536445
theorem B3402577 : Blo 1792097 3402577 := bstep (se 2 (by rfl) ⟨1275966, by rfl⟩ : syracuseStep 3402577 = 2551933) B2551933
theorem B2689889 : Blo 1792097 2689889 := bstep (se 2 (by rfl) ⟨1008708, by rfl⟩ : syracuseStep 2689889 = 2017417) B2017417
theorem B2689907 : Blo 1792097 2689907 := bstep (se 1 (by rfl) ⟨2017430, by rfl⟩ : syracuseStep 2689907 = 4034861) B4034861
theorem B3025795 : Blo 1792097 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B5106577 : Blo 1792097 5106577 := bstep (se 2 (by rfl) ⟨1914966, by rfl⟩ : syracuseStep 5106577 = 3829933) B3829933
theorem B2689937 : Blo 1792097 2689937 := bstep (se 2 (by rfl) ⟨1008726, by rfl⟩ : syracuseStep 2689937 = 2017453) B2017453
theorem B2689955 : Blo 1792097 2689955 := bstep (se 1 (by rfl) ⟨2017466, by rfl⟩ : syracuseStep 2689955 = 4034933) B4034933
theorem B4033457 : Blo 1792097 4033457 := bstep (se 2 (by rfl) ⟨1512546, by rfl⟩ : syracuseStep 4033457 = 3025093) B3025093
theorem B2018227 : Blo 1792097 2018227 := bstep (se 1 (by rfl) ⟨1513670, by rfl⟩ : syracuseStep 2018227 = 3027341) B3027341
theorem B2689985 : Blo 1792097 2689985 := bstep (se 2 (by rfl) ⟨1008744, by rfl⟩ : syracuseStep 2689985 = 2017489) B2017489
theorem B4033475 : Blo 1792097 4033475 := bstep (se 1 (by rfl) ⟨3025106, by rfl⟩ : syracuseStep 4033475 = 6050213) B6050213
theorem B2690003 : Blo 1792097 2690003 := bstep (se 1 (by rfl) ⟨2017502, by rfl⟩ : syracuseStep 2690003 = 4035005) B4035005
theorem B2690033 : Blo 1792097 2690033 := bstep (se 2 (by rfl) ⟨1008762, by rfl⟩ : syracuseStep 2690033 = 2017525) B2017525
theorem B2690051 : Blo 1792097 2690051 := bstep (se 1 (by rfl) ⟨2017538, by rfl⟩ : syracuseStep 2690051 = 4035077) B4035077
theorem B3025937 : Blo 1792097 3025937 := bstep (se 2 (by rfl) ⟨1134726, by rfl⟩ : syracuseStep 3025937 = 2269453) B2269453
theorem B2690081 : Blo 1792097 2690081 := bstep (se 2 (by rfl) ⟨1008780, by rfl⟩ : syracuseStep 2690081 = 2017561) B2017561
theorem B2690099 : Blo 1792097 2690099 := bstep (se 1 (by rfl) ⟨2017574, by rfl⟩ : syracuseStep 2690099 = 4035149) B4035149
theorem B26201141 : Blo 1792097 26201141 := bstep (se 5 (by rfl) ⟨1228178, by rfl⟩ : syracuseStep 26201141 = 2456357) B2456357
theorem B2690129 : Blo 1792097 2690129 := bstep (se 2 (by rfl) ⟨1008798, by rfl⟩ : syracuseStep 2690129 = 2017597) B2017597
theorem B5745745 : Blo 1792097 5745745 := bstep (se 2 (by rfl) ⟨2154654, by rfl⟩ : syracuseStep 5745745 = 4309309) B4309309
theorem B2690147 : Blo 1792097 2690147 := bstep (se 1 (by rfl) ⟨2017610, by rfl⟩ : syracuseStep 2690147 = 4035221) B4035221
theorem B2690177 : Blo 1792097 2690177 := bstep (se 2 (by rfl) ⟨1008816, by rfl⟩ : syracuseStep 2690177 = 2017633) B2017633
theorem B3026065 : Blo 1792097 3026065 := bstep (se 2 (by rfl) ⟨1134774, by rfl⟩ : syracuseStep 3026065 = 2269549) B2269549
theorem B2690195 : Blo 1792097 2690195 := bstep (se 1 (by rfl) ⟨2017646, by rfl⟩ : syracuseStep 2690195 = 4035293) B4035293
theorem B5106851 : Blo 1792097 5106851 := bstep (se 1 (by rfl) ⟨3830138, by rfl⟩ : syracuseStep 5106851 = 7660277) B7660277
theorem B2690225 : Blo 1792097 2690225 := bstep (se 2 (by rfl) ⟨1008834, by rfl⟩ : syracuseStep 2690225 = 2017669) B2017669
theorem B3026099 : Blo 1792097 3026099 := bstep (se 1 (by rfl) ⟨2269574, by rfl⟩ : syracuseStep 3026099 = 4539149) B4539149
theorem B2690243 : Blo 1792097 2690243 := bstep (se 1 (by rfl) ⟨2017682, by rfl⟩ : syracuseStep 2690243 = 4035365) B4035365
theorem B4033745 : Blo 1792097 4033745 := bstep (se 2 (by rfl) ⟨1512654, by rfl⟩ : syracuseStep 4033745 = 3025309) B3025309
theorem B2690273 : Blo 1792097 2690273 := bstep (se 2 (by rfl) ⟨1008852, by rfl⟩ : syracuseStep 2690273 = 2017705) B2017705
theorem B4033763 : Blo 1792097 4033763 := bstep (se 1 (by rfl) ⟨3025322, by rfl⟩ : syracuseStep 4033763 = 6050645) B6050645
theorem B2690291 : Blo 1792097 2690291 := bstep (se 1 (by rfl) ⟨2017718, by rfl⟩ : syracuseStep 2690291 = 4035437) B4035437
theorem B11488517 : Blo 1792097 11488517 := bstep (se 4 (by rfl) ⟨1077048, by rfl⟩ : syracuseStep 11488517 = 2154097) B2154097
theorem B2690321 : Blo 1792097 2690321 := bstep (se 2 (by rfl) ⟨1008870, by rfl⟩ : syracuseStep 2690321 = 2017741) B2017741
theorem B3829027 : Blo 1792097 3829027 := bstep (se 1 (by rfl) ⟨2871770, by rfl⟩ : syracuseStep 3829027 = 5743541) B5743541
theorem B2690339 : Blo 1792097 2690339 := bstep (se 1 (by rfl) ⟨2017754, by rfl⟩ : syracuseStep 2690339 = 4035509) B4035509
theorem B9080099 : Blo 1792097 9080099 := bstep (se 1 (by rfl) ⟨6810074, by rfl⟩ : syracuseStep 9080099 = 13620149) B13620149
theorem B2911537 : Blo 1792097 2911537 := bstep (se 2 (by rfl) ⟨1091826, by rfl⟩ : syracuseStep 2911537 = 2183653) B2183653
theorem B3026227 : Blo 1792097 3026227 := bstep (se 1 (by rfl) ⟨2269670, by rfl⟩ : syracuseStep 3026227 = 4539341) B4539341
theorem B2690369 : Blo 1792097 2690369 := bstep (se 2 (by rfl) ⟨1008888, by rfl⟩ : syracuseStep 2690369 = 2017777) B2017777
theorem B2690387 : Blo 1792097 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B6049133 : Blo 1792097 6049133 := bstep (se 3 (by rfl) ⟨1134212, by rfl⟩ : syracuseStep 6049133 = 2268425) B2268425
theorem B2690417 : Blo 1792097 2690417 := bstep (se 2 (by rfl) ⟨1008906, by rfl⟩ : syracuseStep 2690417 = 2017813) B2017813
theorem B2690435 : Blo 1792097 2690435 := bstep (se 1 (by rfl) ⟨2017826, by rfl⟩ : syracuseStep 2690435 = 4035653) B4035653
theorem B2690465 : Blo 1792097 2690465 := bstep (se 2 (by rfl) ⟨1008924, by rfl⟩ : syracuseStep 2690465 = 2017849) B2017849
theorem B6049187 : Blo 1792097 6049187 := bstep (se 1 (by rfl) ⟨4536890, by rfl⟩ : syracuseStep 6049187 = 9073781) B9073781
theorem B3231139 : Blo 1792097 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B2690483 : Blo 1792097 2690483 := bstep (se 1 (by rfl) ⟨2017862, by rfl⟩ : syracuseStep 2690483 = 4035725) B4035725
theorem B3026369 : Blo 1792097 3026369 := bstep (se 2 (by rfl) ⟨1134888, by rfl⟩ : syracuseStep 3026369 = 2269777) B2269777
theorem B2690513 : Blo 1792097 2690513 := bstep (se 2 (by rfl) ⟨1008942, by rfl⟩ : syracuseStep 2690513 = 2017885) B2017885
theorem B2690531 : Blo 1792097 2690531 := bstep (se 1 (by rfl) ⟨2017898, by rfl⟩ : syracuseStep 2690531 = 4035797) B4035797
theorem B4034033 : Blo 1792097 4034033 := bstep (se 2 (by rfl) ⟨1512762, by rfl⟩ : syracuseStep 4034033 = 3025525) B3025525
theorem B2690561 : Blo 1792097 2690561 := bstep (se 2 (by rfl) ⟨1008960, by rfl⟩ : syracuseStep 2690561 = 2017921) B2017921
theorem B4034051 : Blo 1792097 4034051 := bstep (se 1 (by rfl) ⟨3025538, by rfl⟩ : syracuseStep 4034051 = 6051077) B6051077
theorem B3452419 : Blo 1792097 3452419 := bstep (se 1 (by rfl) ⟨2589314, by rfl⟩ : syracuseStep 3452419 = 5178629) B5178629
theorem B2690579 : Blo 1792097 2690579 := bstep (se 1 (by rfl) ⟨2017934, by rfl⟩ : syracuseStep 2690579 = 4035869) B4035869
theorem B2690609 : Blo 1792097 2690609 := bstep (se 2 (by rfl) ⟨1008978, by rfl⟩ : syracuseStep 2690609 = 2017957) B2017957
theorem B3026497 : Blo 1792097 3026497 := bstep (se 2 (by rfl) ⟨1134936, by rfl⟩ : syracuseStep 3026497 = 2269873) B2269873
theorem B2690627 : Blo 1792097 2690627 := bstep (se 1 (by rfl) ⟨2017970, by rfl⟩ : syracuseStep 2690627 = 4035941) B4035941
theorem B2690657 : Blo 1792097 2690657 := bstep (se 2 (by rfl) ⟨1008996, by rfl⟩ : syracuseStep 2690657 = 2017993) B2017993
theorem B3026531 : Blo 1792097 3026531 := bstep (se 1 (by rfl) ⟨2269898, by rfl⟩ : syracuseStep 3026531 = 4539797) B4539797
theorem B2690675 : Blo 1792097 2690675 := bstep (se 1 (by rfl) ⟨2018006, by rfl⟩ : syracuseStep 2690675 = 4036013) B4036013
theorem B2690705 : Blo 1792097 2690705 := bstep (se 2 (by rfl) ⟨1009014, by rfl⟩ : syracuseStep 2690705 = 2018029) B2018029
theorem B2690723 : Blo 1792097 2690723 := bstep (se 1 (by rfl) ⟨2018042, by rfl⟩ : syracuseStep 2690723 = 4036085) B4036085
theorem B6049457 : Blo 1792097 6049457 := bstep (se 2 (by rfl) ⟨2268546, by rfl⟩ : syracuseStep 6049457 = 4537093) B4537093
theorem B2690753 : Blo 1792097 2690753 := bstep (se 2 (by rfl) ⟨1009032, by rfl⟩ : syracuseStep 2690753 = 2018065) B2018065
theorem B2690771 : Blo 1792097 2690771 := bstep (se 1 (by rfl) ⟨2018078, by rfl⟩ : syracuseStep 2690771 = 4036157) B4036157
theorem B3026659 : Blo 1792097 3026659 := bstep (se 1 (by rfl) ⟨2269994, by rfl⟩ : syracuseStep 3026659 = 4539989) B4539989
theorem B2690801 : Blo 1792097 2690801 := bstep (se 2 (by rfl) ⟨1009050, by rfl⟩ : syracuseStep 2690801 = 2018101) B2018101
theorem B2690819 : Blo 1792097 2690819 := bstep (se 1 (by rfl) ⟨2018114, by rfl⟩ : syracuseStep 2690819 = 4036229) B4036229
theorem B4034321 : Blo 1792097 4034321 := bstep (se 2 (by rfl) ⟨1512870, by rfl⟩ : syracuseStep 4034321 = 3025741) B3025741
theorem B2690849 : Blo 1792097 2690849 := bstep (se 2 (by rfl) ⟨1009068, by rfl⟩ : syracuseStep 2690849 = 2018137) B2018137
theorem B4034339 : Blo 1792097 4034339 := bstep (se 1 (by rfl) ⟨3025754, by rfl⟩ : syracuseStep 4034339 = 6051509) B6051509
theorem B2690867 : Blo 1792097 2690867 := bstep (se 1 (by rfl) ⟨2018150, by rfl⟩ : syracuseStep 2690867 = 4036301) B4036301
theorem B4845379 : Blo 1792097 4845379 := bstep (se 1 (by rfl) ⟨3634034, by rfl⟩ : syracuseStep 4845379 = 7268069) B7268069
theorem B2690897 : Blo 1792097 2690897 := bstep (se 2 (by rfl) ⟨1009086, by rfl⟩ : syracuseStep 2690897 = 2018173) B2018173
theorem B2690915 : Blo 1792097 2690915 := bstep (se 1 (by rfl) ⟨2018186, by rfl⟩ : syracuseStep 2690915 = 4036373) B4036373
theorem B3403633 : Blo 1792097 3403633 := bstep (se 2 (by rfl) ⟨1276362, by rfl⟩ : syracuseStep 3403633 = 2552725) B2552725
theorem B3026801 : Blo 1792097 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B2690945 : Blo 1792097 2690945 := bstep (se 2 (by rfl) ⟨1009104, by rfl⟩ : syracuseStep 2690945 = 2018209) B2018209
theorem B2690963 : Blo 1792097 2690963 := bstep (se 1 (by rfl) ⟨2018222, by rfl⟩ : syracuseStep 2690963 = 4036445) B4036445
theorem B3231665 : Blo 1792097 3231665 := bstep (se 2 (by rfl) ⟨1211874, by rfl⟩ : syracuseStep 3231665 = 2423749) B2423749
theorem B2690993 : Blo 1792097 2690993 := bstep (se 2 (by rfl) ⟨1009122, by rfl⟩ : syracuseStep 2690993 = 2018245) B2018245
theorem B2183107 : Blo 1792097 2183107 := bstep (se 1 (by rfl) ⟨1637330, by rfl⟩ : syracuseStep 2183107 = 3274661) B3274661
theorem B2691011 : Blo 1792097 2691011 := bstep (se 1 (by rfl) ⟨2018258, by rfl⟩ : syracuseStep 2691011 = 4036517) B4036517
theorem B2691041 : Blo 1792097 2691041 := bstep (se 2 (by rfl) ⟨1009140, by rfl⟩ : syracuseStep 2691041 = 2018281) B2018281
theorem B49754083 : Blo 1792097 49754083 := bstep (se 1 (by rfl) ⟨37315562, by rfl⟩ : syracuseStep 49754083 = 74631125) B74631125
theorem B5107693 : Blo 1792097 5107693 := bstep (se 3 (by rfl) ⟨957692, by rfl⟩ : syracuseStep 5107693 = 1915385) B1915385
theorem B3026929 : Blo 1792097 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B2691059 : Blo 1792097 2691059 := bstep (se 1 (by rfl) ⟨2018294, by rfl⟩ : syracuseStep 2691059 = 4036589) B4036589
theorem B2691089 : Blo 1792097 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B3026963 : Blo 1792097 3026963 := bstep (se 1 (by rfl) ⟨2270222, by rfl⟩ : syracuseStep 3026963 = 4540445) B4540445
theorem B2691107 : Blo 1792097 2691107 := bstep (se 1 (by rfl) ⟨2018330, by rfl⟩ : syracuseStep 2691107 = 4036661) B4036661
theorem B4034609 : Blo 1792097 4034609 := bstep (se 2 (by rfl) ⟨1512978, by rfl⟩ : syracuseStep 4034609 = 3025957) B3025957
theorem B58945589 : Blo 1792097 58945589 := bstep (se 5 (by rfl) ⟨2763074, by rfl⟩ : syracuseStep 58945589 = 5526149) B5526149
theorem B3067969 : Blo 1792097 3067969 := bstep (se 2 (by rfl) ⟨1150488, by rfl⟩ : syracuseStep 3067969 = 2300977) B2300977
theorem B2691137 : Blo 1792097 2691137 := bstep (se 2 (by rfl) ⟨1009176, by rfl⟩ : syracuseStep 2691137 = 2018353) B2018353
theorem B4034627 : Blo 1792097 4034627 := bstep (se 1 (by rfl) ⟨3025970, by rfl⟩ : syracuseStep 4034627 = 6051941) B6051941
theorem B9080909 : Blo 1792097 9080909 := bstep (se 3 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 9080909 = 3405341) B3405341
theorem B2871425 : Blo 1792097 2871425 := bstep (se 2 (by rfl) ⟨1076784, by rfl⟩ : syracuseStep 2871425 = 2153569) B2153569
theorem B5107853 : Blo 1792097 5107853 := bstep (se 3 (by rfl) ⟨957722, by rfl⟩ : syracuseStep 5107853 = 1915445) B1915445
theorem B3027091 : Blo 1792097 3027091 := bstep (se 1 (by rfl) ⟨2270318, by rfl⟩ : syracuseStep 3027091 = 4540637) B4540637
theorem B3068065 : Blo 1792097 3068065 := bstep (se 2 (by rfl) ⟨1150524, by rfl⟩ : syracuseStep 3068065 = 2301049) B2301049
theorem B6049997 : Blo 1792097 6049997 := bstep (se 3 (by rfl) ⟨1134374, by rfl⟩ : syracuseStep 6049997 = 2268749) B2268749
theorem B6050051 : Blo 1792097 6050051 := bstep (se 1 (by rfl) ⟨4537538, by rfl⟩ : syracuseStep 6050051 = 9075077) B9075077
theorem B3404035 : Blo 1792097 3404035 := bstep (se 1 (by rfl) ⟨2553026, by rfl⟩ : syracuseStep 3404035 = 5106053) B5106053
theorem B3027233 : Blo 1792097 3027233 := bstep (se 2 (by rfl) ⟨1135212, by rfl⟩ : syracuseStep 3027233 = 2270425) B2270425
theorem B3404081 : Blo 1792097 3404081 := bstep (se 2 (by rfl) ⟨1276530, by rfl⟩ : syracuseStep 3404081 = 2553061) B2553061
theorem B5108035 : Blo 1792097 5108035 := bstep (se 1 (by rfl) ⟨3831026, by rfl⟩ : syracuseStep 5108035 = 7662053) B7662053
theorem B4034897 : Blo 1792097 4034897 := bstep (se 2 (by rfl) ⟨1513086, by rfl⟩ : syracuseStep 4034897 = 3026173) B3026173
theorem B2552161 : Blo 1792097 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B4034915 : Blo 1792097 4034915 := bstep (se 1 (by rfl) ⟨3026186, by rfl⟩ : syracuseStep 4034915 = 6052373) B6052373
theorem B2552195 : Blo 1792097 2552195 := bstep (se 1 (by rfl) ⟨1914146, by rfl⟩ : syracuseStep 2552195 = 3828293) B3828293
theorem B3027361 : Blo 1792097 3027361 := bstep (se 2 (by rfl) ⟨1135260, by rfl⟩ : syracuseStep 3027361 = 2270521) B2270521
theorem B3027395 : Blo 1792097 3027395 := bstep (se 1 (by rfl) ⟨2270546, by rfl⟩ : syracuseStep 3027395 = 4541093) B4541093
theorem B3830257 : Blo 1792097 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B6050321 : Blo 1792097 6050321 := bstep (se 2 (by rfl) ⟨2268870, by rfl⟩ : syracuseStep 6050321 = 4537741) B4537741
theorem B10908209 : Blo 1792097 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B3027523 : Blo 1792097 3027523 := bstep (se 1 (by rfl) ⟨2270642, by rfl⟩ : syracuseStep 3027523 = 4541285) B4541285
theorem B3404369 : Blo 1792097 3404369 := bstep (se 2 (by rfl) ⟨1276638, by rfl⟩ : syracuseStep 3404369 = 2553277) B2553277
theorem B9826915 : Blo 1792097 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B4035185 : Blo 1792097 4035185 := bstep (se 2 (by rfl) ⟨1513194, by rfl⟩ : syracuseStep 4035185 = 3026389) B3026389
theorem B4035203 : Blo 1792097 4035203 := bstep (se 1 (by rfl) ⟨3026402, by rfl⟩ : syracuseStep 4035203 = 6052805) B6052805
theorem B5821229 : Blo 1792097 5821229 := bstep (se 3 (by rfl) ⟨1091480, by rfl⟩ : syracuseStep 5821229 = 2182961) B2182961
theorem B9073457 : Blo 1792097 9073457 := bstep (se 2 (by rfl) ⟨3402546, by rfl⟩ : syracuseStep 9073457 = 6805093) B6805093
theorem B22401845 : Blo 1792097 22401845 := bstep (se 5 (by rfl) ⟨1050086, by rfl⟩ : syracuseStep 22401845 = 2100173) B2100173
theorem B16364387 : Blo 1792097 16364387 := bstep (se 1 (by rfl) ⟨12273290, by rfl⟩ : syracuseStep 16364387 = 24546581) B24546581
theorem B6460273 : Blo 1792097 6460273 := bstep (se 2 (by rfl) ⟨2422602, by rfl⟩ : syracuseStep 6460273 = 4845205) B4845205
theorem B4035473 : Blo 1792097 4035473 := bstep (se 2 (by rfl) ⟨1513302, by rfl⟩ : syracuseStep 4035473 = 3026605) B3026605
theorem B2044819 : Blo 1792097 2044819 := bstep (se 1 (by rfl) ⟨1533614, by rfl⟩ : syracuseStep 2044819 = 3067229) B3067229
theorem B4035491 : Blo 1792097 4035491 := bstep (se 1 (by rfl) ⟨3026618, by rfl⟩ : syracuseStep 4035491 = 6053237) B6053237
theorem B2552753 : Blo 1792097 2552753 := bstep (se 2 (by rfl) ⟨957282, by rfl⟩ : syracuseStep 2552753 = 1914565) B1914565
theorem B2724833 : Blo 1792097 2724833 := bstep (se 2 (by rfl) ⟨1021812, by rfl⟩ : syracuseStep 2724833 = 2043625) B2043625
theorem B20714467 : Blo 1792097 20714467 := bstep (se 1 (by rfl) ⟨15535850, by rfl⟩ : syracuseStep 20714467 = 31071701) B31071701
theorem B12932081 : Blo 1792097 12932081 := bstep (se 2 (by rfl) ⟨4849530, by rfl⟩ : syracuseStep 12932081 = 9699061) B9699061
theorem B2552833 : Blo 1792097 2552833 := bstep (se 2 (by rfl) ⟨957312, by rfl⟩ : syracuseStep 2552833 = 1914625) B1914625
theorem B15324173 : Blo 1792097 15324173 := bstep (se 3 (by rfl) ⟨2873282, by rfl⟩ : syracuseStep 15324173 = 5746565) B5746565
theorem B6050861 : Blo 1792097 6050861 := bstep (se 3 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 6050861 = 2269073) B2269073
theorem B6050915 : Blo 1792097 6050915 := bstep (se 1 (by rfl) ⟨4538186, by rfl⟩ : syracuseStep 6050915 = 9076373) B9076373
theorem B6804593 : Blo 1792097 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B4035761 : Blo 1792097 4035761 := bstep (se 2 (by rfl) ⟨1513410, by rfl⟩ : syracuseStep 4035761 = 3026821) B3026821
theorem B1914035 : Blo 1792097 1914035 := bstep (se 1 (by rfl) ⟨1435526, by rfl⟩ : syracuseStep 1914035 = 2871053) B2871053
theorem B4035779 : Blo 1792097 4035779 := bstep (se 1 (by rfl) ⟨3026834, by rfl⟩ : syracuseStep 4035779 = 6053669) B6053669
theorem B3405091 : Blo 1792097 3405091 := bstep (se 1 (by rfl) ⟨2553818, by rfl⟩ : syracuseStep 3405091 = 5107637) B5107637
theorem B6051185 : Blo 1792097 6051185 := bstep (se 2 (by rfl) ⟨2269194, by rfl⟩ : syracuseStep 6051185 = 4538389) B4538389
theorem B5903761 : Blo 1792097 5903761 := bstep (se 2 (by rfl) ⟨2213910, by rfl⟩ : syracuseStep 5903761 = 4427821) B4427821
theorem B2872739 : Blo 1792097 2872739 := bstep (se 1 (by rfl) ⟨2154554, by rfl⟩ : syracuseStep 2872739 = 4309109) B4309109
theorem B5174705 : Blo 1792097 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B4036049 : Blo 1792097 4036049 := bstep (se 2 (by rfl) ⟨1513518, by rfl⟩ : syracuseStep 4036049 = 3027037) B3027037
theorem B15316451 : Blo 1792097 15316451 := bstep (se 1 (by rfl) ⟨11487338, by rfl⟩ : syracuseStep 15316451 = 22974677) B22974677
theorem B4036067 : Blo 1792097 4036067 := bstep (se 1 (by rfl) ⟨3027050, by rfl⟩ : syracuseStep 4036067 = 6054101) B6054101
theorem B11482829 : Blo 1792097 11482829 := bstep (se 3 (by rfl) ⟨2153030, by rfl⟩ : syracuseStep 11482829 = 4306061) B4306061
theorem B3405539 : Blo 1792097 3405539 := bstep (se 1 (by rfl) ⟨2554154, by rfl⟩ : syracuseStep 3405539 = 5108309) B5108309
theorem B4036337 : Blo 1792097 4036337 := bstep (se 2 (by rfl) ⟨1513626, by rfl⟩ : syracuseStep 4036337 = 3027253) B3027253
theorem B4036355 : Blo 1792097 4036355 := bstep (se 1 (by rfl) ⟨3027266, by rfl⟩ : syracuseStep 4036355 = 6054533) B6054533
theorem B2553619 : Blo 1792097 2553619 := bstep (se 1 (by rfl) ⟨1915214, by rfl⟩ : syracuseStep 2553619 = 3830429) B3830429
theorem B6051725 : Blo 1792097 6051725 := bstep (se 3 (by rfl) ⟨1134698, by rfl⟩ : syracuseStep 6051725 = 2269397) B2269397
theorem B1914787 : Blo 1792097 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B6051779 : Blo 1792097 6051779 := bstep (se 1 (by rfl) ⟨4538834, by rfl⟩ : syracuseStep 6051779 = 9077669) B9077669
theorem B3405827 : Blo 1792097 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B4036625 : Blo 1792097 4036625 := bstep (se 2 (by rfl) ⟨1513734, by rfl⟩ : syracuseStep 4036625 = 3027469) B3027469
theorem B2586659 : Blo 1792097 2586659 := bstep (se 1 (by rfl) ⟨1939994, by rfl⟩ : syracuseStep 2586659 = 3879989) B3879989
theorem B7657507 : Blo 1792097 7657507 := bstep (se 1 (by rfl) ⟨5743130, by rfl⟩ : syracuseStep 7657507 = 11486261) B11486261
theorem B4036643 : Blo 1792097 4036643 := bstep (se 1 (by rfl) ⟨3027482, by rfl⟩ : syracuseStep 4036643 = 6054965) B6054965
theorem B2873411 : Blo 1792097 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B1792099 : Blo 1792097 1792099 := bstep (se 1 (by rfl) ⟨1344074, by rfl⟩ : syracuseStep 1792099 = 2688149) B2688149
theorem B12269681 : Blo 1792097 12269681 := bstep (se 2 (by rfl) ⟨4601130, by rfl⟩ : syracuseStep 12269681 = 9202261) B9202261
theorem B1792115 : Blo 1792097 1792115 := bstep (se 1 (by rfl) ⟨1344086, by rfl⟩ : syracuseStep 1792115 = 2688173) B2688173
theorem B1792131 : Blo 1792097 1792131 := bstep (se 1 (by rfl) ⟨1344098, by rfl⟩ : syracuseStep 1792131 = 2688197) B2688197
theorem B1792147 : Blo 1792097 1792147 := bstep (se 1 (by rfl) ⟨1344110, by rfl⟩ : syracuseStep 1792147 = 2688221) B2688221
theorem B1792163 : Blo 1792097 1792163 := bstep (se 1 (by rfl) ⟨1344122, by rfl⟩ : syracuseStep 1792163 = 2688245) B2688245
theorem B4790449 : Blo 1792097 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B1792179 : Blo 1792097 1792179 := bstep (se 1 (by rfl) ⟨1344134, by rfl⟩ : syracuseStep 1792179 = 2688269) B2688269
theorem B1792195 : Blo 1792097 1792195 := bstep (se 1 (by rfl) ⟨1344146, by rfl⟩ : syracuseStep 1792195 = 2688293) B2688293
theorem B6052049 : Blo 1792097 6052049 := bstep (se 2 (by rfl) ⟨2269518, by rfl⟩ : syracuseStep 6052049 = 4539037) B4539037
theorem B1792211 : Blo 1792097 1792211 := bstep (se 1 (by rfl) ⟨1344158, by rfl⟩ : syracuseStep 1792211 = 2688317) B2688317
theorem B1792227 : Blo 1792097 1792227 := bstep (se 1 (by rfl) ⟨1344170, by rfl⟩ : syracuseStep 1792227 = 2688341) B2688341
theorem B9074915 : Blo 1792097 9074915 := bstep (se 1 (by rfl) ⟨6806186, by rfl⟩ : syracuseStep 9074915 = 13612373) B13612373
theorem B2554097 : Blo 1792097 2554097 := bstep (se 2 (by rfl) ⟨957786, by rfl⟩ : syracuseStep 2554097 = 1915573) B1915573
theorem B1792243 : Blo 1792097 1792243 := bstep (se 1 (by rfl) ⟨1344182, by rfl⟩ : syracuseStep 1792243 = 2688365) B2688365
theorem B1792259 : Blo 1792097 1792259 := bstep (se 1 (by rfl) ⟨1344194, by rfl⟩ : syracuseStep 1792259 = 2688389) B2688389
theorem B1792275 : Blo 1792097 1792275 := bstep (se 1 (by rfl) ⟨1344206, by rfl⟩ : syracuseStep 1792275 = 2688413) B2688413
theorem B1792291 : Blo 1792097 1792291 := bstep (se 1 (by rfl) ⟨1344218, by rfl⟩ : syracuseStep 1792291 = 2688437) B2688437
theorem B1792307 : Blo 1792097 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1792323 : Blo 1792097 1792323 := bstep (se 1 (by rfl) ⟨1344242, by rfl⟩ : syracuseStep 1792323 = 2688485) B2688485
theorem B1792339 : Blo 1792097 1792339 := bstep (se 1 (by rfl) ⟨1344254, by rfl⟩ : syracuseStep 1792339 = 2688509) B2688509
theorem B2726227 : Blo 1792097 2726227 := bstep (se 1 (by rfl) ⟨2044670, by rfl⟩ : syracuseStep 2726227 = 4089341) B4089341
theorem B1792355 : Blo 1792097 1792355 := bstep (se 1 (by rfl) ⟨1344266, by rfl⟩ : syracuseStep 1792355 = 2688533) B2688533
theorem B7272803 : Blo 1792097 7272803 := bstep (se 1 (by rfl) ⟨5454602, by rfl⟩ : syracuseStep 7272803 = 10909205) B10909205
theorem B2554211 : Blo 1792097 2554211 := bstep (se 1 (by rfl) ⟨1915658, by rfl⟩ : syracuseStep 2554211 = 3831317) B3831317
theorem B2873713 : Blo 1792097 2873713 := bstep (se 2 (by rfl) ⟨1077642, by rfl⟩ : syracuseStep 2873713 = 2155285) B2155285
theorem B1792371 : Blo 1792097 1792371 := bstep (se 1 (by rfl) ⟨1344278, by rfl⟩ : syracuseStep 1792371 = 2688557) B2688557
theorem B1792387 : Blo 1792097 1792387 := bstep (se 1 (by rfl) ⟨1344290, by rfl⟩ : syracuseStep 1792387 = 2688581) B2688581
theorem B1792403 : Blo 1792097 1792403 := bstep (se 1 (by rfl) ⟨1344302, by rfl⟩ : syracuseStep 1792403 = 2688605) B2688605
theorem B1792419 : Blo 1792097 1792419 := bstep (se 1 (by rfl) ⟨1344314, by rfl⟩ : syracuseStep 1792419 = 2688629) B2688629
theorem B3275171 : Blo 1792097 3275171 := bstep (se 1 (by rfl) ⟨2456378, by rfl⟩ : syracuseStep 3275171 = 4912757) B4912757
theorem B1792435 : Blo 1792097 1792435 := bstep (se 1 (by rfl) ⟨1344326, by rfl⟩ : syracuseStep 1792435 = 2688653) B2688653
theorem B2554291 : Blo 1792097 2554291 := bstep (se 1 (by rfl) ⟨1915718, by rfl⟩ : syracuseStep 2554291 = 3831437) B3831437
theorem B1792451 : Blo 1792097 1792451 := bstep (se 1 (by rfl) ⟨1344338, by rfl⟩ : syracuseStep 1792451 = 2688677) B2688677
theorem B1792467 : Blo 1792097 1792467 := bstep (se 1 (by rfl) ⟨1344350, by rfl⟩ : syracuseStep 1792467 = 2688701) B2688701
theorem B1792483 : Blo 1792097 1792483 := bstep (se 1 (by rfl) ⟨1344362, by rfl⟩ : syracuseStep 1792483 = 2688725) B2688725
theorem B1792499 : Blo 1792097 1792499 := bstep (se 1 (by rfl) ⟨1344374, by rfl⟩ : syracuseStep 1792499 = 2688749) B2688749
theorem B2152963 : Blo 1792097 2152963 := bstep (se 1 (by rfl) ⟨1614722, by rfl⟩ : syracuseStep 2152963 = 3229445) B3229445
theorem B1792515 : Blo 1792097 1792515 := bstep (se 1 (by rfl) ⟨1344386, by rfl⟩ : syracuseStep 1792515 = 2688773) B2688773
theorem B1792531 : Blo 1792097 1792531 := bstep (se 1 (by rfl) ⟨1344398, by rfl⟩ : syracuseStep 1792531 = 2688797) B2688797
theorem B6806051 : Blo 1792097 6806051 := bstep (se 1 (by rfl) ⟨5104538, by rfl⟩ : syracuseStep 6806051 = 10209077) B10209077
theorem B1792547 : Blo 1792097 1792547 := bstep (se 1 (by rfl) ⟨1344410, by rfl⟩ : syracuseStep 1792547 = 2688821) B2688821
theorem B4536881 : Blo 1792097 4536881 := bstep (se 2 (by rfl) ⟨1701330, by rfl⟩ : syracuseStep 4536881 = 3402661) B3402661
theorem B6806065 : Blo 1792097 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B1792563 : Blo 1792097 1792563 := bstep (se 1 (by rfl) ⟨1344422, by rfl⟩ : syracuseStep 1792563 = 2688845) B2688845
theorem B1792579 : Blo 1792097 1792579 := bstep (se 1 (by rfl) ⟨1344434, by rfl⟩ : syracuseStep 1792579 = 2688869) B2688869
theorem B1792595 : Blo 1792097 1792595 := bstep (se 1 (by rfl) ⟨1344446, by rfl⟩ : syracuseStep 1792595 = 2688893) B2688893
theorem B4536931 : Blo 1792097 4536931 := bstep (se 1 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 4536931 = 6805397) B6805397
theorem B1792611 : Blo 1792097 1792611 := bstep (se 1 (by rfl) ⟨1344458, by rfl⟩ : syracuseStep 1792611 = 2688917) B2688917
theorem B1792627 : Blo 1792097 1792627 := bstep (se 1 (by rfl) ⟨1344470, by rfl⟩ : syracuseStep 1792627 = 2688941) B2688941
theorem B1792643 : Blo 1792097 1792643 := bstep (se 1 (by rfl) ⟨1344482, by rfl⟩ : syracuseStep 1792643 = 2688965) B2688965
theorem B1792659 : Blo 1792097 1792659 := bstep (se 1 (by rfl) ⟨1344494, by rfl⟩ : syracuseStep 1792659 = 2688989) B2688989
theorem B1792675 : Blo 1792097 1792675 := bstep (se 1 (by rfl) ⟨1344506, by rfl⟩ : syracuseStep 1792675 = 2689013) B2689013
theorem B1792691 : Blo 1792097 1792691 := bstep (se 1 (by rfl) ⟨1344518, by rfl⟩ : syracuseStep 1792691 = 2689037) B2689037
theorem B1792707 : Blo 1792097 1792707 := bstep (se 1 (by rfl) ⟨1344530, by rfl⟩ : syracuseStep 1792707 = 2689061) B2689061
theorem B1792723 : Blo 1792097 1792723 := bstep (se 1 (by rfl) ⟨1344542, by rfl⟩ : syracuseStep 1792723 = 2689085) B2689085
theorem B1792739 : Blo 1792097 1792739 := bstep (se 1 (by rfl) ⟨1344554, by rfl⟩ : syracuseStep 1792739 = 2689109) B2689109
theorem B6052589 : Blo 1792097 6052589 := bstep (se 3 (by rfl) ⟨1134860, by rfl⟩ : syracuseStep 6052589 = 2269721) B2269721
theorem B4537073 : Blo 1792097 4537073 := bstep (se 2 (by rfl) ⟨1701402, by rfl⟩ : syracuseStep 4537073 = 3402805) B3402805
theorem B1792755 : Blo 1792097 1792755 := bstep (se 1 (by rfl) ⟨1344566, by rfl⟩ : syracuseStep 1792755 = 2689133) B2689133
theorem B1792771 : Blo 1792097 1792771 := bstep (se 1 (by rfl) ⟨1344578, by rfl⟩ : syracuseStep 1792771 = 2689157) B2689157
theorem B1792787 : Blo 1792097 1792787 := bstep (se 1 (by rfl) ⟨1344590, by rfl⟩ : syracuseStep 1792787 = 2689181) B2689181
theorem B1792803 : Blo 1792097 1792803 := bstep (se 1 (by rfl) ⟨1344602, by rfl⟩ : syracuseStep 1792803 = 2689205) B2689205
theorem B6052643 : Blo 1792097 6052643 := bstep (se 1 (by rfl) ⟨4539482, by rfl⟩ : syracuseStep 6052643 = 9078965) B9078965
theorem B1792819 : Blo 1792097 1792819 := bstep (se 1 (by rfl) ⟨1344614, by rfl⟩ : syracuseStep 1792819 = 2689229) B2689229
theorem B1792835 : Blo 1792097 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B1792851 : Blo 1792097 1792851 := bstep (se 1 (by rfl) ⟨1344638, by rfl⟩ : syracuseStep 1792851 = 2689277) B2689277
theorem B1792867 : Blo 1792097 1792867 := bstep (se 1 (by rfl) ⟨1344650, by rfl⟩ : syracuseStep 1792867 = 2689301) B2689301
theorem B16169827 : Blo 1792097 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B1792883 : Blo 1792097 1792883 := bstep (se 1 (by rfl) ⟨1344662, by rfl⟩ : syracuseStep 1792883 = 2689325) B2689325
theorem B1792899 : Blo 1792097 1792899 := bstep (se 1 (by rfl) ⟨1344674, by rfl⟩ : syracuseStep 1792899 = 2689349) B2689349
theorem B1792915 : Blo 1792097 1792915 := bstep (se 1 (by rfl) ⟨1344686, by rfl⟩ : syracuseStep 1792915 = 2689373) B2689373
theorem B1915795 : Blo 1792097 1915795 := bstep (se 1 (by rfl) ⟨1436846, by rfl⟩ : syracuseStep 1915795 = 2873693) B2873693
theorem B1792931 : Blo 1792097 1792931 := bstep (se 1 (by rfl) ⟨1344698, by rfl⟩ : syracuseStep 1792931 = 2689397) B2689397
theorem B1792947 : Blo 1792097 1792947 := bstep (se 1 (by rfl) ⟨1344710, by rfl⟩ : syracuseStep 1792947 = 2689421) B2689421
theorem B1792963 : Blo 1792097 1792963 := bstep (se 1 (by rfl) ⟨1344722, by rfl⟩ : syracuseStep 1792963 = 2689445) B2689445
theorem B1792979 : Blo 1792097 1792979 := bstep (se 1 (by rfl) ⟨1344734, by rfl⟩ : syracuseStep 1792979 = 2689469) B2689469
theorem B1792995 : Blo 1792097 1792995 := bstep (se 1 (by rfl) ⟨1344746, by rfl⟩ : syracuseStep 1792995 = 2689493) B2689493
theorem B1793011 : Blo 1792097 1793011 := bstep (se 1 (by rfl) ⟨1344758, by rfl⟩ : syracuseStep 1793011 = 2689517) B2689517
theorem B1793027 : Blo 1792097 1793027 := bstep (se 1 (by rfl) ⟨1344770, by rfl⟩ : syracuseStep 1793027 = 2689541) B2689541
theorem B9075725 : Blo 1792097 9075725 := bstep (se 3 (by rfl) ⟨1701698, by rfl⟩ : syracuseStep 9075725 = 3403397) B3403397
theorem B1793043 : Blo 1792097 1793043 := bstep (se 1 (by rfl) ⟨1344782, by rfl⟩ : syracuseStep 1793043 = 2689565) B2689565
theorem B1793059 : Blo 1792097 1793059 := bstep (se 1 (by rfl) ⟨1344794, by rfl⟩ : syracuseStep 1793059 = 2689589) B2689589
theorem B6052913 : Blo 1792097 6052913 := bstep (se 2 (by rfl) ⟨2269842, by rfl⟩ : syracuseStep 6052913 = 4539685) B4539685
theorem B1793075 : Blo 1792097 1793075 := bstep (se 1 (by rfl) ⟨1344806, by rfl⟩ : syracuseStep 1793075 = 2689613) B2689613
theorem B1793091 : Blo 1792097 1793091 := bstep (se 1 (by rfl) ⟨1344818, by rfl⟩ : syracuseStep 1793091 = 2689637) B2689637
theorem B1793107 : Blo 1792097 1793107 := bstep (se 1 (by rfl) ⟨1344830, by rfl⟩ : syracuseStep 1793107 = 2689661) B2689661
theorem B2587745 : Blo 1792097 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B1793123 : Blo 1792097 1793123 := bstep (se 1 (by rfl) ⟨1344842, by rfl⟩ : syracuseStep 1793123 = 2689685) B2689685
theorem B1793139 : Blo 1792097 1793139 := bstep (se 1 (by rfl) ⟨1344854, by rfl⟩ : syracuseStep 1793139 = 2689709) B2689709
theorem B1793155 : Blo 1792097 1793155 := bstep (se 1 (by rfl) ⟨1344866, by rfl⟩ : syracuseStep 1793155 = 2689733) B2689733
theorem B1793171 : Blo 1792097 1793171 := bstep (se 1 (by rfl) ⟨1344878, by rfl⟩ : syracuseStep 1793171 = 2689757) B2689757
theorem B1793187 : Blo 1792097 1793187 := bstep (se 1 (by rfl) ⟨1344890, by rfl⟩ : syracuseStep 1793187 = 2689781) B2689781
theorem B1793203 : Blo 1792097 1793203 := bstep (se 1 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 1793203 = 2689805) B2689805
theorem B1793219 : Blo 1792097 1793219 := bstep (se 1 (by rfl) ⟨1344914, by rfl⟩ : syracuseStep 1793219 = 2689829) B2689829
theorem B1793235 : Blo 1792097 1793235 := bstep (se 1 (by rfl) ⟨1344926, by rfl⟩ : syracuseStep 1793235 = 2689853) B2689853
theorem B1793251 : Blo 1792097 1793251 := bstep (se 1 (by rfl) ⟨1344938, by rfl⟩ : syracuseStep 1793251 = 2689877) B2689877
theorem B1793267 : Blo 1792097 1793267 := bstep (se 1 (by rfl) ⟨1344950, by rfl⟩ : syracuseStep 1793267 = 2689901) B2689901
theorem B4365571 : Blo 1792097 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B1793283 : Blo 1792097 1793283 := bstep (se 1 (by rfl) ⟨1344962, by rfl⟩ : syracuseStep 1793283 = 2689925) B2689925
theorem B15310093 : Blo 1792097 15310093 := bstep (se 3 (by rfl) ⟨2870642, by rfl⟩ : syracuseStep 15310093 = 5741285) B5741285
theorem B2153747 : Blo 1792097 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B1793299 : Blo 1792097 1793299 := bstep (se 1 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 1793299 = 2689949) B2689949
theorem B1793315 : Blo 1792097 1793315 := bstep (se 1 (by rfl) ⟨1344986, by rfl⟩ : syracuseStep 1793315 = 2689973) B2689973
theorem B10902833 : Blo 1792097 10902833 := bstep (se 2 (by rfl) ⟨4088562, by rfl⟩ : syracuseStep 10902833 = 8177125) B8177125
theorem B1793331 : Blo 1792097 1793331 := bstep (se 1 (by rfl) ⟨1344998, by rfl⟩ : syracuseStep 1793331 = 2689997) B2689997
theorem B1793347 : Blo 1792097 1793347 := bstep (se 1 (by rfl) ⟨1345010, by rfl⟩ : syracuseStep 1793347 = 2690021) B2690021
theorem B1793363 : Blo 1792097 1793363 := bstep (se 1 (by rfl) ⟨1345022, by rfl⟩ : syracuseStep 1793363 = 2690045) B2690045
theorem B1793379 : Blo 1792097 1793379 := bstep (se 1 (by rfl) ⟨1345034, by rfl⟩ : syracuseStep 1793379 = 2690069) B2690069
theorem B1793395 : Blo 1792097 1793395 := bstep (se 1 (by rfl) ⟨1345046, by rfl⟩ : syracuseStep 1793395 = 2690093) B2690093
theorem B1793411 : Blo 1792097 1793411 := bstep (se 1 (by rfl) ⟨1345058, by rfl⟩ : syracuseStep 1793411 = 2690117) B2690117
theorem B9330061 : Blo 1792097 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B1793427 : Blo 1792097 1793427 := bstep (se 1 (by rfl) ⟨1345070, by rfl⟩ : syracuseStep 1793427 = 2690141) B2690141
theorem B1793443 : Blo 1792097 1793443 := bstep (se 1 (by rfl) ⟨1345082, by rfl⟩ : syracuseStep 1793443 = 2690165) B2690165
theorem B1793459 : Blo 1792097 1793459 := bstep (se 1 (by rfl) ⟨1345094, by rfl⟩ : syracuseStep 1793459 = 2690189) B2690189
theorem B1793475 : Blo 1792097 1793475 := bstep (se 1 (by rfl) ⟨1345106, by rfl⟩ : syracuseStep 1793475 = 2690213) B2690213
theorem B5742029 : Blo 1792097 5742029 := bstep (se 3 (by rfl) ⟨1076630, by rfl⟩ : syracuseStep 5742029 = 2153261) B2153261
theorem B5176781 : Blo 1792097 5176781 := bstep (se 3 (by rfl) ⟨970646, by rfl⟩ : syracuseStep 5176781 = 1941293) B1941293
theorem B1793491 : Blo 1792097 1793491 := bstep (se 1 (by rfl) ⟨1345118, by rfl⟩ : syracuseStep 1793491 = 2690237) B2690237
theorem B2268643 : Blo 1792097 2268643 := bstep (se 1 (by rfl) ⟨1701482, by rfl⟩ : syracuseStep 2268643 = 3402965) B3402965
theorem B1793507 : Blo 1792097 1793507 := bstep (se 1 (by rfl) ⟨1345130, by rfl⟩ : syracuseStep 1793507 = 2690261) B2690261
theorem B1793523 : Blo 1792097 1793523 := bstep (se 1 (by rfl) ⟨1345142, by rfl⟩ : syracuseStep 1793523 = 2690285) B2690285
theorem B1793539 : Blo 1792097 1793539 := bstep (se 1 (by rfl) ⟨1345154, by rfl⟩ : syracuseStep 1793539 = 2690309) B2690309
theorem B1793555 : Blo 1792097 1793555 := bstep (se 1 (by rfl) ⟨1345166, by rfl⟩ : syracuseStep 1793555 = 2690333) B2690333
theorem B1793571 : Blo 1792097 1793571 := bstep (se 1 (by rfl) ⟨1345178, by rfl⟩ : syracuseStep 1793571 = 2690357) B2690357
theorem B1793587 : Blo 1792097 1793587 := bstep (se 1 (by rfl) ⟨1345190, by rfl⟩ : syracuseStep 1793587 = 2690381) B2690381
theorem B2268739 : Blo 1792097 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B1793603 : Blo 1792097 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B6053453 : Blo 1792097 6053453 := bstep (se 3 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 6053453 = 2270045) B2270045
theorem B1793619 : Blo 1792097 1793619 := bstep (se 1 (by rfl) ⟨1345214, by rfl⟩ : syracuseStep 1793619 = 2690429) B2690429
theorem B1793635 : Blo 1792097 1793635 := bstep (se 1 (by rfl) ⟨1345226, by rfl⟩ : syracuseStep 1793635 = 2690453) B2690453
theorem B1793651 : Blo 1792097 1793651 := bstep (se 1 (by rfl) ⟨1345238, by rfl⟩ : syracuseStep 1793651 = 2690477) B2690477
theorem B6053507 : Blo 1792097 6053507 := bstep (se 1 (by rfl) ⟨4540130, by rfl⟩ : syracuseStep 6053507 = 9080261) B9080261
theorem B1793667 : Blo 1792097 1793667 := bstep (se 1 (by rfl) ⟨1345250, by rfl⟩ : syracuseStep 1793667 = 2690501) B2690501
theorem B2301571 : Blo 1792097 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B1793683 : Blo 1792097 1793683 := bstep (se 1 (by rfl) ⟨1345262, by rfl⟩ : syracuseStep 1793683 = 2690525) B2690525
theorem B1793699 : Blo 1792097 1793699 := bstep (se 1 (by rfl) ⟨1345274, by rfl⟩ : syracuseStep 1793699 = 2690549) B2690549
theorem B1793715 : Blo 1792097 1793715 := bstep (se 1 (by rfl) ⟨1345286, by rfl⟩ : syracuseStep 1793715 = 2690573) B2690573
theorem B1793731 : Blo 1792097 1793731 := bstep (se 1 (by rfl) ⟨1345298, by rfl⟩ : syracuseStep 1793731 = 2690597) B2690597
theorem B4538065 : Blo 1792097 4538065 := bstep (se 2 (by rfl) ⟨1701774, by rfl⟩ : syracuseStep 4538065 = 3403549) B3403549
theorem B1793747 : Blo 1792097 1793747 := bstep (se 1 (by rfl) ⟨1345310, by rfl⟩ : syracuseStep 1793747 = 2690621) B2690621
theorem B1793763 : Blo 1792097 1793763 := bstep (se 1 (by rfl) ⟨1345322, by rfl⟩ : syracuseStep 1793763 = 2690645) B2690645
theorem B1793779 : Blo 1792097 1793779 := bstep (se 1 (by rfl) ⟨1345334, by rfl⟩ : syracuseStep 1793779 = 2690669) B2690669
theorem B1793795 : Blo 1792097 1793795 := bstep (se 1 (by rfl) ⟨1345346, by rfl⟩ : syracuseStep 1793795 = 2690693) B2690693
theorem B1818371 : Blo 1792097 1818371 := bstep (se 1 (by rfl) ⟨1363778, by rfl⟩ : syracuseStep 1818371 = 2727557) B2727557
theorem B6217489 : Blo 1792097 6217489 := bstep (se 2 (by rfl) ⟨2331558, by rfl⟩ : syracuseStep 6217489 = 4663117) B4663117
theorem B1793811 : Blo 1792097 1793811 := bstep (se 1 (by rfl) ⟨1345358, by rfl⟩ : syracuseStep 1793811 = 2690717) B2690717
theorem B1793827 : Blo 1792097 1793827 := bstep (se 1 (by rfl) ⟨1345370, by rfl⟩ : syracuseStep 1793827 = 2690741) B2690741
theorem B1793843 : Blo 1792097 1793843 := bstep (se 1 (by rfl) ⟨1345382, by rfl⟩ : syracuseStep 1793843 = 2690765) B2690765
theorem B1793859 : Blo 1792097 1793859 := bstep (se 1 (by rfl) ⟨1345394, by rfl⟩ : syracuseStep 1793859 = 2690789) B2690789
theorem B1793875 : Blo 1792097 1793875 := bstep (se 1 (by rfl) ⟨1345406, by rfl⟩ : syracuseStep 1793875 = 2690813) B2690813
theorem B1793891 : Blo 1792097 1793891 := bstep (se 1 (by rfl) ⟨1345418, by rfl⟩ : syracuseStep 1793891 = 2690837) B2690837
theorem B1793907 : Blo 1792097 1793907 := bstep (se 1 (by rfl) ⟨1345430, by rfl⟩ : syracuseStep 1793907 = 2690861) B2690861
theorem B1793923 : Blo 1792097 1793923 := bstep (se 1 (by rfl) ⟨1345442, by rfl⟩ : syracuseStep 1793923 = 2690885) B2690885
theorem B6053777 : Blo 1792097 6053777 := bstep (se 2 (by rfl) ⟨2270166, by rfl⟩ : syracuseStep 6053777 = 4540333) B4540333
theorem B1793939 : Blo 1792097 1793939 := bstep (se 1 (by rfl) ⟨1345454, by rfl⟩ : syracuseStep 1793939 = 2690909) B2690909
theorem B1793955 : Blo 1792097 1793955 := bstep (se 1 (by rfl) ⟨1345466, by rfl⟩ : syracuseStep 1793955 = 2690933) B2690933
theorem B1793971 : Blo 1792097 1793971 := bstep (se 1 (by rfl) ⟨1345478, by rfl⟩ : syracuseStep 1793971 = 2690957) B2690957
theorem B1793987 : Blo 1792097 1793987 := bstep (se 1 (by rfl) ⟨1345490, by rfl⟩ : syracuseStep 1793987 = 2690981) B2690981
theorem B14540741 : Blo 1792097 14540741 := bstep (se 4 (by rfl) ⟨1363194, by rfl⟩ : syracuseStep 14540741 = 2726389) B2726389
theorem B1794003 : Blo 1792097 1794003 := bstep (se 1 (by rfl) ⟨1345502, by rfl⟩ : syracuseStep 1794003 = 2691005) B2691005
theorem B6897635 : Blo 1792097 6897635 := bstep (se 1 (by rfl) ⟨5173226, by rfl⟩ : syracuseStep 6897635 = 10346453) B10346453
theorem B4538339 : Blo 1792097 4538339 := bstep (se 1 (by rfl) ⟨3403754, by rfl⟩ : syracuseStep 4538339 = 6807509) B6807509
theorem B6807523 : Blo 1792097 6807523 := bstep (se 1 (by rfl) ⟨5105642, by rfl⟩ : syracuseStep 6807523 = 10211285) B10211285
theorem B12926947 : Blo 1792097 12926947 := bstep (se 1 (by rfl) ⟨9695210, by rfl⟩ : syracuseStep 12926947 = 19390421) B19390421
theorem B1794019 : Blo 1792097 1794019 := bstep (se 1 (by rfl) ⟨1345514, by rfl⟩ : syracuseStep 1794019 = 2691029) B2691029
theorem B1794035 : Blo 1792097 1794035 := bstep (se 1 (by rfl) ⟨1345526, by rfl⟩ : syracuseStep 1794035 = 2691053) B2691053
theorem B1794059 : Blo 1792097 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B1794071 : Blo 1792097 1794071 := bstep (se 1 (by rfl) ⟨1345553, by rfl⟩ : syracuseStep 1794071 = 2691107) B2691107
theorem B39297059 : Blo 1792097 39297059 := bstep (se 1 (by rfl) ⟨29472794, by rfl⟩ : syracuseStep 39297059 = 58945589) B58945589
theorem B1794091 : Blo 1792097 1794091 := bstep (se 1 (by rfl) ⟨1345568, by rfl⟩ : syracuseStep 1794091 = 2691137) B2691137
theorem B6053939 : Blo 1792097 6053939 := bstep (se 1 (by rfl) ⟨4540454, by rfl⟩ : syracuseStep 6053939 = 9080909) B9080909
theorem B15319115 : Blo 1792097 15319115 := bstep (se 1 (by rfl) ⟨11489336, by rfl⟩ : syracuseStep 15319115 = 22978673) B22978673
theorem B22986827 : Blo 1792097 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B6897757 : Blo 1792097 6897757 := bstep (se 3 (by rfl) ⟨1293329, by rfl⟩ : syracuseStep 6897757 = 2586659) B2586659
theorem B52428941 : Blo 1792097 52428941 := bstep (se 3 (by rfl) ⟨9830426, by rfl⟩ : syracuseStep 52428941 = 19660853) B19660853
theorem B2269387 : Blo 1792097 2269387 := bstep (se 1 (by rfl) ⟨1702040, by rfl⟩ : syracuseStep 2269387 = 3404081) B3404081
theorem B4309271 : Blo 1792097 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B1868087 : Blo 1792097 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B6054209 : Blo 1792097 6054209 := bstep (se 2 (by rfl) ⟨2270328, by rfl⟩ : syracuseStep 6054209 = 4540657) B4540657
theorem B4538713 : Blo 1792097 4538713 := bstep (se 2 (by rfl) ⟨1702017, by rfl⟩ : syracuseStep 4538713 = 3404035) B3404035
theorem B10207619 : Blo 1792097 10207619 := bstep (se 1 (by rfl) ⟨7655714, by rfl⟩ : syracuseStep 10207619 = 15311429) B15311429
theorem B14934563 : Blo 1792097 14934563 := bstep (se 1 (by rfl) ⟨11200922, by rfl⟩ : syracuseStep 14934563 = 22401845) B22401845
theorem B10216115 : Blo 1792097 10216115 := bstep (se 1 (by rfl) ⟨7662086, by rfl⟩ : syracuseStep 10216115 = 15324173) B15324173
theorem B5743325 : Blo 1792097 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B3883763 : Blo 1792097 3883763 := bstep (se 1 (by rfl) ⟨2912822, by rfl⟩ : syracuseStep 3883763 = 5825645) B5825645
theorem B6054749 : Blo 1792097 6054749 := bstep (se 3 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 6054749 = 2270531) B2270531
theorem B2016139 : Blo 1792097 2016139 := bstep (se 1 (by rfl) ⟨1512104, by rfl⟩ : syracuseStep 2016139 = 3024209) B3024209
theorem B3449803 : Blo 1792097 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B2016247 : Blo 1792097 2016247 := bstep (se 1 (by rfl) ⟨1512185, by rfl⟩ : syracuseStep 2016247 = 3024371) B3024371
theorem B2270359 : Blo 1792097 2270359 := bstep (se 1 (by rfl) ⟨1702769, by rfl⟩ : syracuseStep 2270359 = 3405539) B3405539
theorem B2016427 : Blo 1792097 2016427 := bstep (se 1 (by rfl) ⟨1512320, by rfl⟩ : syracuseStep 2016427 = 3024641) B3024641
theorem B6808769 : Blo 1792097 6808769 := bstep (se 2 (by rfl) ⟨2553288, by rfl⟩ : syracuseStep 6808769 = 5106577) B5106577
theorem B2688203 : Blo 1792097 2688203 := bstep (se 1 (by rfl) ⟨2016152, by rfl⟩ : syracuseStep 2688203 = 4032305) B4032305
theorem B15312077 : Blo 1792097 15312077 := bstep (se 3 (by rfl) ⟨2871014, by rfl⟩ : syracuseStep 15312077 = 5742029) B5742029
theorem B2688215 : Blo 1792097 2688215 := bstep (se 1 (by rfl) ⟨2016161, by rfl⟩ : syracuseStep 2688215 = 4032323) B4032323
theorem B2016535 : Blo 1792097 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B2688281 : Blo 1792097 2688281 := bstep (se 2 (by rfl) ⟨1008105, by rfl⟩ : syracuseStep 2688281 = 2016211) B2016211
theorem B4310347 : Blo 1792097 4310347 := bstep (se 1 (by rfl) ⟨3232760, by rfl⟩ : syracuseStep 4310347 = 6465521) B6465521
theorem B2688395 : Blo 1792097 2688395 := bstep (se 1 (by rfl) ⟨2016296, by rfl⟩ : syracuseStep 2688395 = 4032593) B4032593
theorem B2688407 : Blo 1792097 2688407 := bstep (se 1 (by rfl) ⟨2016305, by rfl⟩ : syracuseStep 2688407 = 4032611) B4032611
theorem B4539827 : Blo 1792097 4539827 := bstep (se 1 (by rfl) ⟨3404870, by rfl⟩ : syracuseStep 4539827 = 6809741) B6809741
theorem B7660993 : Blo 1792097 7660993 := bstep (se 2 (by rfl) ⟨2872872, by rfl⟩ : syracuseStep 7660993 = 5745745) B5745745
theorem B2016715 : Blo 1792097 2016715 := bstep (se 1 (by rfl) ⟨1512536, by rfl⟩ : syracuseStep 2016715 = 3025073) B3025073
theorem B2688473 : Blo 1792097 2688473 := bstep (se 2 (by rfl) ⟨1008177, by rfl⟩ : syracuseStep 2688473 = 2016355) B2016355
theorem B9078317 : Blo 1792097 9078317 := bstep (se 3 (by rfl) ⟨1702184, by rfl⟩ : syracuseStep 9078317 = 3404369) B3404369
theorem B2016823 : Blo 1792097 2016823 := bstep (se 1 (by rfl) ⟨1512617, by rfl⟩ : syracuseStep 2016823 = 3025235) B3025235
theorem B2688587 : Blo 1792097 2688587 := bstep (se 1 (by rfl) ⟨2016440, by rfl⟩ : syracuseStep 2688587 = 4032881) B4032881
theorem B2688599 : Blo 1792097 2688599 := bstep (se 1 (by rfl) ⟨2016449, by rfl⟩ : syracuseStep 2688599 = 4032899) B4032899
theorem B2688665 : Blo 1792097 2688665 := bstep (se 2 (by rfl) ⟨1008249, by rfl⟩ : syracuseStep 2688665 = 2016499) B2016499
theorem B3024587 : Blo 1792097 3024587 := bstep (se 1 (by rfl) ⟨2268440, by rfl⟩ : syracuseStep 3024587 = 4536881) B4536881
theorem B5105369 : Blo 1792097 5105369 := bstep (se 2 (by rfl) ⟨1914513, by rfl⟩ : syracuseStep 5105369 = 3829027) B3829027
theorem B4540121 : Blo 1792097 4540121 := bstep (se 2 (by rfl) ⟨1702545, by rfl⟩ : syracuseStep 4540121 = 3405091) B3405091
theorem B2017003 : Blo 1792097 2017003 := bstep (se 1 (by rfl) ⟨1512752, by rfl⟩ : syracuseStep 2017003 = 3025505) B3025505
theorem B2688779 : Blo 1792097 2688779 := bstep (se 1 (by rfl) ⟨2016584, by rfl⟩ : syracuseStep 2688779 = 4033169) B4033169
theorem B2688791 : Blo 1792097 2688791 := bstep (se 1 (by rfl) ⟨2016593, by rfl⟩ : syracuseStep 2688791 = 4033187) B4033187
theorem B19384109 : Blo 1792097 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B3024715 : Blo 1792097 3024715 := bstep (se 1 (by rfl) ⟨2268536, by rfl⟩ : syracuseStep 3024715 = 4537073) B4537073
theorem B2017111 : Blo 1792097 2017111 := bstep (se 1 (by rfl) ⟨1512833, by rfl⟩ : syracuseStep 2017111 = 3025667) B3025667
theorem B2688857 : Blo 1792097 2688857 := bstep (se 2 (by rfl) ⟨1008321, by rfl⟩ : syracuseStep 2688857 = 2016643) B2016643
theorem B20416373 : Blo 1792097 20416373 := bstep (se 5 (by rfl) ⟨957017, by rfl⟩ : syracuseStep 20416373 = 1914035) B1914035
theorem B4032395 : Blo 1792097 4032395 := bstep (se 1 (by rfl) ⟨3024296, by rfl⟩ : syracuseStep 4032395 = 6048593) B6048593
theorem B4032449 : Blo 1792097 4032449 := bstep (se 2 (by rfl) ⟨1512168, by rfl⟩ : syracuseStep 4032449 = 3024337) B3024337
theorem B2688971 : Blo 1792097 2688971 := bstep (se 1 (by rfl) ⟨2016728, by rfl⟩ : syracuseStep 2688971 = 4033457) B4033457
theorem B2688983 : Blo 1792097 2688983 := bstep (se 1 (by rfl) ⟨2016737, by rfl⟩ : syracuseStep 2688983 = 4033475) B4033475
theorem B3024857 : Blo 1792097 3024857 := bstep (se 2 (by rfl) ⟨1134321, by rfl⟩ : syracuseStep 3024857 = 2268643) B2268643
theorem B2017291 : Blo 1792097 2017291 := bstep (se 1 (by rfl) ⟨1512968, by rfl⟩ : syracuseStep 2017291 = 3025937) B3025937
theorem B29067281 : Blo 1792097 29067281 := bstep (se 2 (by rfl) ⟨10900230, by rfl⟩ : syracuseStep 29067281 = 21800461) B21800461
theorem B2689049 : Blo 1792097 2689049 := bstep (se 2 (by rfl) ⟨1008393, by rfl⟩ : syracuseStep 2689049 = 2016787) B2016787
theorem B17467427 : Blo 1792097 17467427 := bstep (se 1 (by rfl) ⟨13100570, by rfl⟩ : syracuseStep 17467427 = 26201141) B26201141
theorem B3024985 : Blo 1792097 3024985 := bstep (se 2 (by rfl) ⟨1134369, by rfl⟩ : syracuseStep 3024985 = 2268739) B2268739
theorem B10217573 : Blo 1792097 10217573 := bstep (se 4 (by rfl) ⟨957897, by rfl⟩ : syracuseStep 10217573 = 1915795) B1915795
theorem B2017399 : Blo 1792097 2017399 := bstep (se 1 (by rfl) ⟨1513049, by rfl⟩ : syracuseStep 2017399 = 3026099) B3026099
theorem B2689163 : Blo 1792097 2689163 := bstep (se 1 (by rfl) ⟨2016872, by rfl⟩ : syracuseStep 2689163 = 4033745) B4033745
theorem B2689175 : Blo 1792097 2689175 := bstep (se 1 (by rfl) ⟨2016881, by rfl⟩ : syracuseStep 2689175 = 4033763) B4033763
theorem B4032665 : Blo 1792097 4032665 := bstep (se 2 (by rfl) ⟨1512249, by rfl⟩ : syracuseStep 4032665 = 3024499) B3024499
theorem B7268555 : Blo 1792097 7268555 := bstep (se 1 (by rfl) ⟨5451416, by rfl⟩ : syracuseStep 7268555 = 10902833) B10902833
theorem B2689241 : Blo 1792097 2689241 := bstep (se 2 (by rfl) ⟨1008465, by rfl⟩ : syracuseStep 2689241 = 2016931) B2016931
theorem B4032755 : Blo 1792097 4032755 := bstep (se 1 (by rfl) ⟨3024566, by rfl⟩ : syracuseStep 4032755 = 6049133) B6049133
theorem B4032791 : Blo 1792097 4032791 := bstep (se 1 (by rfl) ⟨3024593, by rfl⟩ : syracuseStep 4032791 = 6049187) B6049187
theorem B2017579 : Blo 1792097 2017579 := bstep (se 1 (by rfl) ⟨1513184, by rfl⟩ : syracuseStep 2017579 = 3026369) B3026369
theorem B3451187 : Blo 1792097 3451187 := bstep (se 1 (by rfl) ⟨2588390, by rfl⟩ : syracuseStep 3451187 = 5176781) B5176781
theorem B2689355 : Blo 1792097 2689355 := bstep (se 1 (by rfl) ⟨2017016, by rfl⟩ : syracuseStep 2689355 = 4034033) B4034033
theorem B2689367 : Blo 1792097 2689367 := bstep (se 1 (by rfl) ⟨2017025, by rfl⟩ : syracuseStep 2689367 = 4034051) B4034051
theorem B2017687 : Blo 1792097 2017687 := bstep (se 1 (by rfl) ⟨1513265, by rfl⟩ : syracuseStep 2017687 = 3026531) B3026531
theorem B2689433 : Blo 1792097 2689433 := bstep (se 2 (by rfl) ⟨1008537, by rfl⟩ : syracuseStep 2689433 = 2017075) B2017075
theorem B4032971 : Blo 1792097 4032971 := bstep (se 1 (by rfl) ⟨3024728, by rfl⟩ : syracuseStep 4032971 = 6049457) B6049457
theorem B4033025 : Blo 1792097 4033025 := bstep (se 2 (by rfl) ⟨1512384, by rfl⟩ : syracuseStep 4033025 = 3024769) B3024769
theorem B2689547 : Blo 1792097 2689547 := bstep (se 1 (by rfl) ⟨2017160, by rfl⟩ : syracuseStep 2689547 = 4034321) B4034321
theorem B2689559 : Blo 1792097 2689559 := bstep (se 1 (by rfl) ⟨2017169, by rfl⟩ : syracuseStep 2689559 = 4034339) B4034339
theorem B2017867 : Blo 1792097 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B2910809 : Blo 1792097 2910809 := bstep (se 2 (by rfl) ⟨1091553, by rfl⟩ : syracuseStep 2910809 = 2183107) B2183107
theorem B2689625 : Blo 1792097 2689625 := bstep (se 2 (by rfl) ⟨1008609, by rfl⟩ : syracuseStep 2689625 = 2017219) B2017219
theorem B9693827 : Blo 1792097 9693827 := bstep (se 1 (by rfl) ⟨7270370, by rfl⟩ : syracuseStep 9693827 = 14540741) B14540741
theorem B6810257 : Blo 1792097 6810257 := bstep (se 2 (by rfl) ⟨2553846, by rfl⟩ : syracuseStep 6810257 = 5107693) B5107693
theorem B4598423 : Blo 1792097 4598423 := bstep (se 1 (by rfl) ⟨3448817, by rfl⟩ : syracuseStep 4598423 = 6897635) B6897635
theorem B3025559 : Blo 1792097 3025559 := bstep (se 1 (by rfl) ⟨2269169, by rfl⟩ : syracuseStep 3025559 = 4538339) B4538339
theorem B2017975 : Blo 1792097 2017975 := bstep (se 1 (by rfl) ⟨1513481, by rfl⟩ : syracuseStep 2017975 = 3026963) B3026963
theorem B2689739 : Blo 1792097 2689739 := bstep (se 1 (by rfl) ⟨2017304, by rfl⟩ : syracuseStep 2689739 = 4034609) B4034609
theorem B2689751 : Blo 1792097 2689751 := bstep (se 1 (by rfl) ⟨2017313, by rfl⟩ : syracuseStep 2689751 = 4034627) B4034627
theorem B4033241 : Blo 1792097 4033241 := bstep (se 2 (by rfl) ⟨1512465, by rfl⟩ : syracuseStep 4033241 = 3024931) B3024931
theorem B10210009 : Blo 1792097 10210009 := bstep (se 2 (by rfl) ⟨3828753, by rfl⟩ : syracuseStep 10210009 = 7657507) B7657507
theorem B4090625 : Blo 1792097 4090625 := bstep (se 2 (by rfl) ⟨1533984, by rfl⟩ : syracuseStep 4090625 = 3067969) B3067969
theorem B3025687 : Blo 1792097 3025687 := bstep (se 1 (by rfl) ⟨2269265, by rfl⟩ : syracuseStep 3025687 = 4538531) B4538531
theorem B2689817 : Blo 1792097 2689817 := bstep (se 2 (by rfl) ⟨1008681, by rfl⟩ : syracuseStep 2689817 = 2017363) B2017363
theorem B3451673 : Blo 1792097 3451673 := bstep (se 2 (by rfl) ⟨1294377, by rfl⟩ : syracuseStep 3451673 = 2588755) B2588755
theorem B4033331 : Blo 1792097 4033331 := bstep (se 1 (by rfl) ⟨3024998, by rfl⟩ : syracuseStep 4033331 = 6049997) B6049997
theorem B20712257 : Blo 1792097 20712257 := bstep (se 2 (by rfl) ⟨7767096, by rfl⟩ : syracuseStep 20712257 = 15534193) B15534193
theorem B4033367 : Blo 1792097 4033367 := bstep (se 1 (by rfl) ⟨3025025, by rfl⟩ : syracuseStep 4033367 = 6050051) B6050051
theorem B2018155 : Blo 1792097 2018155 := bstep (se 1 (by rfl) ⟨1513616, by rfl⟩ : syracuseStep 2018155 = 3027233) B3027233
theorem B4090753 : Blo 1792097 4090753 := bstep (se 2 (by rfl) ⟨1534032, by rfl⟩ : syracuseStep 4090753 = 3068065) B3068065
theorem B2689931 : Blo 1792097 2689931 := bstep (se 1 (by rfl) ⟨2017448, by rfl⟩ : syracuseStep 2689931 = 4034897) B4034897
theorem B2689943 : Blo 1792097 2689943 := bstep (se 1 (by rfl) ⟨2017457, by rfl⟩ : syracuseStep 2689943 = 4034915) B4034915
theorem B6900653 : Blo 1792097 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B49048499 : Blo 1792097 49048499 := bstep (se 1 (by rfl) ⟨36786374, by rfl⟩ : syracuseStep 49048499 = 73572749) B73572749
theorem B5106635 : Blo 1792097 5106635 := bstep (se 1 (by rfl) ⟨3829976, by rfl⟩ : syracuseStep 5106635 = 7659953) B7659953
theorem B2018263 : Blo 1792097 2018263 := bstep (se 1 (by rfl) ⟨1513697, by rfl⟩ : syracuseStep 2018263 = 3027395) B3027395
theorem B100797401 : Blo 1792097 100797401 := bstep (se 2 (by rfl) ⟨37799025, by rfl⟩ : syracuseStep 100797401 = 75598051) B75598051
theorem B2690009 : Blo 1792097 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B4033547 : Blo 1792097 4033547 := bstep (se 1 (by rfl) ⟨3025160, by rfl⟩ : syracuseStep 4033547 = 6050321) B6050321
theorem B4033601 : Blo 1792097 4033601 := bstep (se 2 (by rfl) ⟨1512600, by rfl⟩ : syracuseStep 4033601 = 3025201) B3025201
theorem B2690123 : Blo 1792097 2690123 := bstep (se 1 (by rfl) ⟨2017592, by rfl⟩ : syracuseStep 2690123 = 4035185) B4035185
theorem B2690135 : Blo 1792097 2690135 := bstep (se 1 (by rfl) ⟨2017601, by rfl⟩ : syracuseStep 2690135 = 4035203) B4035203
theorem B6810713 : Blo 1792097 6810713 := bstep (se 2 (by rfl) ⟨2554017, by rfl⟩ : syracuseStep 6810713 = 5108035) B5108035
theorem B3402881 : Blo 1792097 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B10906775 : Blo 1792097 10906775 := bstep (se 1 (by rfl) ⟨8180081, by rfl⟩ : syracuseStep 10906775 = 16360163) B16360163
theorem B2690201 : Blo 1792097 2690201 := bstep (se 2 (by rfl) ⟨1008825, by rfl⟩ : syracuseStep 2690201 = 2017651) B2017651
theorem B6048971 : Blo 1792097 6048971 := bstep (se 1 (by rfl) ⟨4536728, by rfl⟩ : syracuseStep 6048971 = 9073457) B9073457
theorem B2690315 : Blo 1792097 2690315 := bstep (se 1 (by rfl) ⟨2017736, by rfl⟩ : syracuseStep 2690315 = 4035473) B4035473
theorem B2690327 : Blo 1792097 2690327 := bstep (se 1 (by rfl) ⟨2017745, by rfl⟩ : syracuseStep 2690327 = 4035491) B4035491
theorem B4033817 : Blo 1792097 4033817 := bstep (se 2 (by rfl) ⟨1512681, by rfl⟩ : syracuseStep 4033817 = 3025363) B3025363
theorem B6810925 : Blo 1792097 6810925 := bstep (se 3 (by rfl) ⟨1277048, by rfl⟩ : syracuseStep 6810925 = 2554097) B2554097
theorem B8621387 : Blo 1792097 8621387 := bstep (se 1 (by rfl) ⟨6466040, by rfl⟩ : syracuseStep 8621387 = 12932081) B12932081
theorem B2690393 : Blo 1792097 2690393 := bstep (se 2 (by rfl) ⟨1008897, by rfl⟩ : syracuseStep 2690393 = 2017795) B2017795
theorem B55184753 : Blo 1792097 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B4033907 : Blo 1792097 4033907 := bstep (se 1 (by rfl) ⟨3025430, by rfl⟩ : syracuseStep 4033907 = 6050861) B6050861
theorem B3403147 : Blo 1792097 3403147 := bstep (se 1 (by rfl) ⟨2552360, by rfl⟩ : syracuseStep 3403147 = 5104721) B5104721
theorem B3026315 : Blo 1792097 3026315 := bstep (se 1 (by rfl) ⟨2269736, by rfl⟩ : syracuseStep 3026315 = 4539473) B4539473
theorem B4033943 : Blo 1792097 4033943 := bstep (se 1 (by rfl) ⟨3025457, by rfl⟩ : syracuseStep 4033943 = 6050915) B6050915
theorem B2690507 : Blo 1792097 2690507 := bstep (se 1 (by rfl) ⟨2017880, by rfl⟩ : syracuseStep 2690507 = 4035761) B4035761
theorem B2690519 : Blo 1792097 2690519 := bstep (se 1 (by rfl) ⟨2017889, by rfl⟩ : syracuseStep 2690519 = 4035779) B4035779
theorem B6049241 : Blo 1792097 6049241 := bstep (se 2 (by rfl) ⟨2268465, by rfl⟩ : syracuseStep 6049241 = 4536931) B4536931
theorem B13102553 : Blo 1792097 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B3026443 : Blo 1792097 3026443 := bstep (se 1 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 3026443 = 4539665) B4539665
theorem B2690585 : Blo 1792097 2690585 := bstep (se 2 (by rfl) ⟨1008969, by rfl⟩ : syracuseStep 2690585 = 2017939) B2017939
theorem B15314467 : Blo 1792097 15314467 := bstep (se 1 (by rfl) ⟨11485850, by rfl⟩ : syracuseStep 15314467 = 22971701) B22971701
theorem B4034123 : Blo 1792097 4034123 := bstep (se 1 (by rfl) ⟨3025592, by rfl⟩ : syracuseStep 4034123 = 6051185) B6051185
theorem B6811229 : Blo 1792097 6811229 := bstep (se 3 (by rfl) ⟨1277105, by rfl⟩ : syracuseStep 6811229 = 2554211) B2554211
theorem B4034177 : Blo 1792097 4034177 := bstep (se 2 (by rfl) ⟨1512816, by rfl⟩ : syracuseStep 4034177 = 3025633) B3025633
theorem B2690699 : Blo 1792097 2690699 := bstep (se 1 (by rfl) ⟨2018024, by rfl⟩ : syracuseStep 2690699 = 4036049) B4036049
theorem B10210967 : Blo 1792097 10210967 := bstep (se 1 (by rfl) ⟨7658225, by rfl⟩ : syracuseStep 10210967 = 15316451) B15316451
theorem B2690711 : Blo 1792097 2690711 := bstep (se 1 (by rfl) ⟨2018033, by rfl⟩ : syracuseStep 2690711 = 4036067) B4036067
theorem B3026585 : Blo 1792097 3026585 := bstep (se 2 (by rfl) ⟨1134969, by rfl⟩ : syracuseStep 3026585 = 2269939) B2269939
theorem B2690777 : Blo 1792097 2690777 := bstep (se 2 (by rfl) ⟨1009041, by rfl⟩ : syracuseStep 2690777 = 2018083) B2018083
theorem B3026713 : Blo 1792097 3026713 := bstep (se 2 (by rfl) ⟨1135017, by rfl⟩ : syracuseStep 3026713 = 2270035) B2270035
theorem B7655219 : Blo 1792097 7655219 := bstep (se 1 (by rfl) ⟨5741414, by rfl⟩ : syracuseStep 7655219 = 11482829) B11482829
theorem B8613697 : Blo 1792097 8613697 := bstep (se 2 (by rfl) ⟨3230136, by rfl⟩ : syracuseStep 8613697 = 6460273) B6460273
theorem B3403595 : Blo 1792097 3403595 := bstep (se 1 (by rfl) ⟨2552696, by rfl⟩ : syracuseStep 3403595 = 5105393) B5105393
theorem B2690891 : Blo 1792097 2690891 := bstep (se 1 (by rfl) ⟨2018168, by rfl⟩ : syracuseStep 2690891 = 4036337) B4036337
theorem B2690903 : Blo 1792097 2690903 := bstep (se 1 (by rfl) ⟨2018177, by rfl⟩ : syracuseStep 2690903 = 4036355) B4036355
theorem B4034393 : Blo 1792097 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B2690969 : Blo 1792097 2690969 := bstep (se 2 (by rfl) ⟨1009113, by rfl⟩ : syracuseStep 2690969 = 2018227) B2018227
theorem B4034483 : Blo 1792097 4034483 := bstep (se 1 (by rfl) ⟨3025862, by rfl⟩ : syracuseStep 4034483 = 6051725) B6051725
theorem B4034519 : Blo 1792097 4034519 := bstep (se 1 (by rfl) ⟨3025889, by rfl⟩ : syracuseStep 4034519 = 6051779) B6051779
theorem B27619289 : Blo 1792097 27619289 := bstep (se 2 (by rfl) ⟨10357233, by rfl⟩ : syracuseStep 27619289 = 20714467) B20714467
theorem B3403777 : Blo 1792097 3403777 := bstep (se 2 (by rfl) ⟨1276416, by rfl⟩ : syracuseStep 3403777 = 2552833) B2552833
theorem B2551819 : Blo 1792097 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B3829771 : Blo 1792097 3829771 := bstep (se 1 (by rfl) ⟨2872328, by rfl⟩ : syracuseStep 3829771 = 5744657) B5744657
theorem B2691083 : Blo 1792097 2691083 := bstep (se 1 (by rfl) ⟨2018312, by rfl⟩ : syracuseStep 2691083 = 4036625) B4036625
theorem B2691095 : Blo 1792097 2691095 := bstep (se 1 (by rfl) ⟨2018321, by rfl⟩ : syracuseStep 2691095 = 4036643) B4036643
theorem B8179787 : Blo 1792097 8179787 := bstep (se 1 (by rfl) ⟨6134840, by rfl⟩ : syracuseStep 8179787 = 12269681) B12269681
theorem B3829847 : Blo 1792097 3829847 := bstep (se 1 (by rfl) ⟨2872385, by rfl⟩ : syracuseStep 3829847 = 5744771) B5744771
theorem B4034699 : Blo 1792097 4034699 := bstep (se 1 (by rfl) ⟨3026024, by rfl⟩ : syracuseStep 4034699 = 6052049) B6052049
theorem B6049943 : Blo 1792097 6049943 := bstep (se 1 (by rfl) ⟨4537457, by rfl⟩ : syracuseStep 6049943 = 9074915) B9074915
theorem B4034753 : Blo 1792097 4034753 := bstep (se 2 (by rfl) ⟨1513032, by rfl⟩ : syracuseStep 4034753 = 3026065) B3026065
theorem B2552087 : Blo 1792097 2552087 := bstep (se 1 (by rfl) ⟨1914065, by rfl⟩ : syracuseStep 2552087 = 3828131) B3828131
theorem B2183447 : Blo 1792097 2183447 := bstep (se 1 (by rfl) ⟨1637585, by rfl⟩ : syracuseStep 2183447 = 3275171) B3275171
theorem B9072971 : Blo 1792097 9072971 := bstep (se 1 (by rfl) ⟨6804728, by rfl⟩ : syracuseStep 9072971 = 13609457) B13609457
theorem B3404119 : Blo 1792097 3404119 := bstep (se 1 (by rfl) ⟨2553089, by rfl⟩ : syracuseStep 3404119 = 5106179) B5106179
theorem B3027287 : Blo 1792097 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B5820761 : Blo 1792097 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B10908035 : Blo 1792097 10908035 := bstep (se 1 (by rfl) ⟨8181026, by rfl⟩ : syracuseStep 10908035 = 16362053) B16362053
theorem B3633547 : Blo 1792097 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B4034969 : Blo 1792097 4034969 := bstep (se 2 (by rfl) ⟨1513113, by rfl⟩ : syracuseStep 4034969 = 3026227) B3026227
theorem B2044363 : Blo 1792097 2044363 := bstep (se 1 (by rfl) ⟨1533272, by rfl⟩ : syracuseStep 2044363 = 3066545) B3066545
theorem B3027415 : Blo 1792097 3027415 := bstep (se 1 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 3027415 = 4541123) B4541123
theorem B4035059 : Blo 1792097 4035059 := bstep (se 1 (by rfl) ⟨3026294, by rfl⟩ : syracuseStep 4035059 = 6052589) B6052589
theorem B12440081 : Blo 1792097 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B4035095 : Blo 1792097 4035095 := bstep (se 1 (by rfl) ⟨3026321, by rfl⟩ : syracuseStep 4035095 = 6052643) B6052643
theorem B3404339 : Blo 1792097 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B6050483 : Blo 1792097 6050483 := bstep (se 1 (by rfl) ⟨4537862, by rfl⟩ : syracuseStep 6050483 = 9075725) B9075725
theorem B4035275 : Blo 1792097 4035275 := bstep (se 1 (by rfl) ⟨3026456, by rfl⟩ : syracuseStep 4035275 = 6052913) B6052913
theorem B4035329 : Blo 1792097 4035329 := bstep (se 2 (by rfl) ⟨1513248, by rfl⟩ : syracuseStep 4035329 = 3026497) B3026497
theorem B3404567 : Blo 1792097 3404567 := bstep (se 1 (by rfl) ⟨2553425, by rfl⟩ : syracuseStep 3404567 = 5106851) B5106851
theorem B3068761 : Blo 1792097 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B6050753 : Blo 1792097 6050753 := bstep (se 2 (by rfl) ⟨2269032, by rfl⟩ : syracuseStep 6050753 = 4538065) B4538065
theorem B4035545 : Blo 1792097 4035545 := bstep (se 2 (by rfl) ⟨1513329, by rfl⟩ : syracuseStep 4035545 = 3026659) B3026659
theorem B3404825 : Blo 1792097 3404825 := bstep (se 2 (by rfl) ⟨1276809, by rfl⟩ : syracuseStep 3404825 = 2553619) B2553619
theorem B4035635 : Blo 1792097 4035635 := bstep (se 1 (by rfl) ⟨3026726, by rfl⟩ : syracuseStep 4035635 = 6053453) B6053453
theorem B4035671 : Blo 1792097 4035671 := bstep (se 1 (by rfl) ⟨3026753, by rfl⟩ : syracuseStep 4035671 = 6053507) B6053507
theorem B6460505 : Blo 1792097 6460505 := bstep (se 2 (by rfl) ⟨2422689, by rfl⟩ : syracuseStep 6460505 = 4845379) B4845379
theorem B2553049 : Blo 1792097 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B20428037 : Blo 1792097 20428037 := bstep (se 4 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 20428037 = 3830257) B3830257
theorem B4035851 : Blo 1792097 4035851 := bstep (se 1 (by rfl) ⟨3026888, by rfl⟩ : syracuseStep 4035851 = 6053777) B6053777
theorem B4035905 : Blo 1792097 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B9082205 : Blo 1792097 9082205 := bstep (se 3 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 9082205 = 3405827) B3405827
theorem B11482469 : Blo 1792097 11482469 := bstep (se 4 (by rfl) ⟨1076481, by rfl⟩ : syracuseStep 11482469 = 2152963) B2152963
theorem B6804881 : Blo 1792097 6804881 := bstep (se 2 (by rfl) ⟨2551830, by rfl⟩ : syracuseStep 6804881 = 5103661) B5103661
theorem B1914283 : Blo 1792097 1914283 := bstep (se 1 (by rfl) ⟨1435712, by rfl⟩ : syracuseStep 1914283 = 2871425) B2871425
theorem B3405235 : Blo 1792097 3405235 := bstep (se 1 (by rfl) ⟨2553926, by rfl⟩ : syracuseStep 3405235 = 5107853) B5107853
theorem B6051293 : Blo 1792097 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B4036121 : Blo 1792097 4036121 := bstep (se 2 (by rfl) ⟨1513545, by rfl⟩ : syracuseStep 4036121 = 3027091) B3027091
theorem B6387265 : Blo 1792097 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B4036211 : Blo 1792097 4036211 := bstep (se 1 (by rfl) ⟨3027158, by rfl⟩ : syracuseStep 4036211 = 6054317) B6054317
theorem B4036247 : Blo 1792097 4036247 := bstep (se 1 (by rfl) ⟨3027185, by rfl⟩ : syracuseStep 4036247 = 6054371) B6054371
theorem B3634969 : Blo 1792097 3634969 := bstep (se 2 (by rfl) ⟨1363113, by rfl⟩ : syracuseStep 3634969 = 2726227) B2726227
theorem B3831617 : Blo 1792097 3831617 := bstep (se 2 (by rfl) ⟨1436856, by rfl⟩ : syracuseStep 3831617 = 2873713) B2873713
theorem B4036427 : Blo 1792097 4036427 := bstep (se 1 (by rfl) ⟨3027320, by rfl⟩ : syracuseStep 4036427 = 6054641) B6054641
theorem B3880819 : Blo 1792097 3880819 := bstep (se 1 (by rfl) ⟨2910614, by rfl⟩ : syracuseStep 3880819 = 5821229) B5821229
theorem B4036481 : Blo 1792097 4036481 := bstep (se 2 (by rfl) ⟨1513680, by rfl⟩ : syracuseStep 4036481 = 3027361) B3027361
theorem B3405721 : Blo 1792097 3405721 := bstep (se 2 (by rfl) ⟨1277145, by rfl⟩ : syracuseStep 3405721 = 2554291) B2554291
theorem B2873303 : Blo 1792097 2873303 := bstep (se 1 (by rfl) ⟨2154977, by rfl⟩ : syracuseStep 2873303 = 4309955) B4309955
theorem B1816555 : Blo 1792097 1816555 := bstep (se 1 (by rfl) ⟨1362416, by rfl⟩ : syracuseStep 1816555 = 2724833) B2724833
theorem B9074753 : Blo 1792097 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B4536395 : Blo 1792097 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B6805579 : Blo 1792097 6805579 := bstep (se 1 (by rfl) ⟨5104184, by rfl⟩ : syracuseStep 6805579 = 10208369) B10208369
theorem B10213451 : Blo 1792097 10213451 := bstep (se 1 (by rfl) ⟨7660088, by rfl⟩ : syracuseStep 10213451 = 15320177) B15320177
theorem B4036697 : Blo 1792097 4036697 := bstep (se 2 (by rfl) ⟨1513761, by rfl⟩ : syracuseStep 4036697 = 3027523) B3027523
theorem B1792107 : Blo 1792097 1792107 := bstep (se 1 (by rfl) ⟨1344080, by rfl⟩ : syracuseStep 1792107 = 2688161) B2688161
theorem B1792119 : Blo 1792097 1792119 := bstep (se 1 (by rfl) ⟨1344089, by rfl⟩ : syracuseStep 1792119 = 2688179) B2688179
theorem B1792139 : Blo 1792097 1792139 := bstep (se 1 (by rfl) ⟨1344104, by rfl⟩ : syracuseStep 1792139 = 2688209) B2688209
theorem B1792151 : Blo 1792097 1792151 := bstep (se 1 (by rfl) ⟨1344113, by rfl⟩ : syracuseStep 1792151 = 2688227) B2688227
theorem B1792171 : Blo 1792097 1792171 := bstep (se 1 (by rfl) ⟨1344128, by rfl⟩ : syracuseStep 1792171 = 2688257) B2688257
theorem B1792183 : Blo 1792097 1792183 := bstep (se 1 (by rfl) ⟨1344137, by rfl⟩ : syracuseStep 1792183 = 2688275) B2688275
theorem B1792203 : Blo 1792097 1792203 := bstep (se 1 (by rfl) ⟨1344152, by rfl⟩ : syracuseStep 1792203 = 2688305) B2688305
theorem B1792215 : Blo 1792097 1792215 := bstep (se 1 (by rfl) ⟨1344161, by rfl⟩ : syracuseStep 1792215 = 2688323) B2688323
theorem B8181977 : Blo 1792097 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B1792235 : Blo 1792097 1792235 := bstep (se 1 (by rfl) ⟨1344176, by rfl⟩ : syracuseStep 1792235 = 2688353) B2688353
theorem B1792247 : Blo 1792097 1792247 := bstep (se 1 (by rfl) ⟨1344185, by rfl⟩ : syracuseStep 1792247 = 2688371) B2688371
theorem B1792267 : Blo 1792097 1792267 := bstep (se 1 (by rfl) ⟨1344200, by rfl⟩ : syracuseStep 1792267 = 2688401) B2688401
theorem B1792279 : Blo 1792097 1792279 := bstep (se 1 (by rfl) ⟨1344209, by rfl⟩ : syracuseStep 1792279 = 2688419) B2688419
theorem B1915159 : Blo 1792097 1915159 := bstep (se 1 (by rfl) ⟨1436369, by rfl⟩ : syracuseStep 1915159 = 2872739) B2872739
theorem B1792299 : Blo 1792097 1792299 := bstep (se 1 (by rfl) ⟨1344224, by rfl⟩ : syracuseStep 1792299 = 2688449) B2688449
theorem B1792311 : Blo 1792097 1792311 := bstep (se 1 (by rfl) ⟨1344233, by rfl⟩ : syracuseStep 1792311 = 2688467) B2688467
theorem B1792331 : Blo 1792097 1792331 := bstep (se 1 (by rfl) ⟨1344248, by rfl⟩ : syracuseStep 1792331 = 2688497) B2688497
theorem B1792343 : Blo 1792097 1792343 := bstep (se 1 (by rfl) ⟨1344257, by rfl⟩ : syracuseStep 1792343 = 2688515) B2688515
theorem B6805853 : Blo 1792097 6805853 := bstep (se 3 (by rfl) ⟨1276097, by rfl⟩ : syracuseStep 6805853 = 2552195) B2552195
theorem B1792363 : Blo 1792097 1792363 := bstep (se 1 (by rfl) ⟨1344272, by rfl⟩ : syracuseStep 1792363 = 2688545) B2688545
theorem B1792375 : Blo 1792097 1792375 := bstep (se 1 (by rfl) ⟨1344281, by rfl⟩ : syracuseStep 1792375 = 2688563) B2688563
theorem B1792395 : Blo 1792097 1792395 := bstep (se 1 (by rfl) ⟨1344296, by rfl⟩ : syracuseStep 1792395 = 2688593) B2688593
theorem B1792407 : Blo 1792097 1792407 := bstep (se 1 (by rfl) ⟨1344305, by rfl⟩ : syracuseStep 1792407 = 2688611) B2688611
theorem B1792427 : Blo 1792097 1792427 := bstep (se 1 (by rfl) ⟨1344320, by rfl⟩ : syracuseStep 1792427 = 2688641) B2688641
theorem B1792439 : Blo 1792097 1792439 := bstep (se 1 (by rfl) ⟨1344329, by rfl⟩ : syracuseStep 1792439 = 2688659) B2688659
theorem B4536769 : Blo 1792097 4536769 := bstep (se 2 (by rfl) ⟨1701288, by rfl⟩ : syracuseStep 4536769 = 3402577) B3402577
theorem B1792459 : Blo 1792097 1792459 := bstep (se 1 (by rfl) ⟨1344344, by rfl⟩ : syracuseStep 1792459 = 2688689) B2688689
theorem B1792471 : Blo 1792097 1792471 := bstep (se 1 (by rfl) ⟨1344353, by rfl⟩ : syracuseStep 1792471 = 2688707) B2688707
theorem B21559769 : Blo 1792097 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B1792491 : Blo 1792097 1792491 := bstep (se 1 (by rfl) ⟨1344368, by rfl⟩ : syracuseStep 1792491 = 2688737) B2688737
theorem B1792503 : Blo 1792097 1792503 := bstep (se 1 (by rfl) ⟨1344377, by rfl⟩ : syracuseStep 1792503 = 2688755) B2688755
theorem B1792523 : Blo 1792097 1792523 := bstep (se 1 (by rfl) ⟨1344392, by rfl⟩ : syracuseStep 1792523 = 2688785) B2688785
theorem B47208977 : Blo 1792097 47208977 := bstep (se 2 (by rfl) ⟨17703366, by rfl⟩ : syracuseStep 47208977 = 35406733) B35406733
theorem B1792535 : Blo 1792097 1792535 := bstep (se 1 (by rfl) ⟨1344401, by rfl⟩ : syracuseStep 1792535 = 2688803) B2688803
theorem B2726425 : Blo 1792097 2726425 := bstep (se 2 (by rfl) ⟨1022409, by rfl⟩ : syracuseStep 2726425 = 2044819) B2044819
theorem B1792555 : Blo 1792097 1792555 := bstep (se 1 (by rfl) ⟨1344416, by rfl⟩ : syracuseStep 1792555 = 2688833) B2688833
theorem B1792567 : Blo 1792097 1792567 := bstep (se 1 (by rfl) ⟨1344425, by rfl⟩ : syracuseStep 1792567 = 2688851) B2688851
theorem B1792587 : Blo 1792097 1792587 := bstep (se 1 (by rfl) ⟨1344440, by rfl⟩ : syracuseStep 1792587 = 2688881) B2688881
theorem B6052427 : Blo 1792097 6052427 := bstep (se 1 (by rfl) ⟨4539320, by rfl⟩ : syracuseStep 6052427 = 9078641) B9078641
theorem B1792599 : Blo 1792097 1792599 := bstep (se 1 (by rfl) ⟨1344449, by rfl⟩ : syracuseStep 1792599 = 2688899) B2688899
theorem B1792619 : Blo 1792097 1792619 := bstep (se 1 (by rfl) ⟨1344464, by rfl⟩ : syracuseStep 1792619 = 2688929) B2688929
theorem B1792631 : Blo 1792097 1792631 := bstep (se 1 (by rfl) ⟨1344473, by rfl⟩ : syracuseStep 1792631 = 2688947) B2688947
theorem B1792651 : Blo 1792097 1792651 := bstep (se 1 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 1792651 = 2688977) B2688977
theorem B33151639 : Blo 1792097 33151639 := bstep (se 1 (by rfl) ⟨24863729, by rfl⟩ : syracuseStep 33151639 = 49727459) B49727459
theorem B1792663 : Blo 1792097 1792663 := bstep (se 1 (by rfl) ⟨1344497, by rfl⟩ : syracuseStep 1792663 = 2688995) B2688995
theorem B1792683 : Blo 1792097 1792683 := bstep (se 1 (by rfl) ⟨1344512, by rfl⟩ : syracuseStep 1792683 = 2689025) B2689025
theorem B1792695 : Blo 1792097 1792695 := bstep (se 1 (by rfl) ⟨1344521, by rfl⟩ : syracuseStep 1792695 = 2689043) B2689043
theorem B1792715 : Blo 1792097 1792715 := bstep (se 1 (by rfl) ⟨1344536, by rfl⟩ : syracuseStep 1792715 = 2689073) B2689073
theorem B1792727 : Blo 1792097 1792727 := bstep (se 1 (by rfl) ⟨1344545, by rfl⟩ : syracuseStep 1792727 = 2689091) B2689091
theorem B1915607 : Blo 1792097 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B1792747 : Blo 1792097 1792747 := bstep (se 1 (by rfl) ⟨1344560, by rfl⟩ : syracuseStep 1792747 = 2689121) B2689121
theorem B1792759 : Blo 1792097 1792759 := bstep (se 1 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 1792759 = 2689139) B2689139
theorem B1792779 : Blo 1792097 1792779 := bstep (se 1 (by rfl) ⟨1344584, by rfl⟩ : syracuseStep 1792779 = 2689169) B2689169
theorem B1792791 : Blo 1792097 1792791 := bstep (se 1 (by rfl) ⟨1344593, by rfl⟩ : syracuseStep 1792791 = 2689187) B2689187
theorem B1792811 : Blo 1792097 1792811 := bstep (se 1 (by rfl) ⟨1344608, by rfl⟩ : syracuseStep 1792811 = 2689217) B2689217
theorem B29088557 : Blo 1792097 29088557 := bstep (se 3 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 29088557 = 10908209) B10908209
theorem B1792823 : Blo 1792097 1792823 := bstep (se 1 (by rfl) ⟨1344617, by rfl⟩ : syracuseStep 1792823 = 2689235) B2689235
theorem B1792843 : Blo 1792097 1792843 := bstep (se 1 (by rfl) ⟨1344632, by rfl⟩ : syracuseStep 1792843 = 2689265) B2689265
theorem B1792855 : Blo 1792097 1792855 := bstep (se 1 (by rfl) ⟨1344641, by rfl⟩ : syracuseStep 1792855 = 2689283) B2689283
theorem B6052697 : Blo 1792097 6052697 := bstep (se 2 (by rfl) ⟨2269761, by rfl⟩ : syracuseStep 6052697 = 4539523) B4539523
theorem B1792875 : Blo 1792097 1792875 := bstep (se 1 (by rfl) ⟨1344656, by rfl⟩ : syracuseStep 1792875 = 2689313) B2689313
theorem B1792887 : Blo 1792097 1792887 := bstep (se 1 (by rfl) ⟨1344665, by rfl⟩ : syracuseStep 1792887 = 2689331) B2689331
theorem B1792907 : Blo 1792097 1792907 := bstep (se 1 (by rfl) ⟨1344680, by rfl⟩ : syracuseStep 1792907 = 2689361) B2689361
theorem B1792919 : Blo 1792097 1792919 := bstep (se 1 (by rfl) ⟨1344689, by rfl⟩ : syracuseStep 1792919 = 2689379) B2689379
theorem B4848535 : Blo 1792097 4848535 := bstep (se 1 (by rfl) ⟨3636401, by rfl⟩ : syracuseStep 4848535 = 7272803) B7272803
theorem B1792939 : Blo 1792097 1792939 := bstep (se 1 (by rfl) ⟨1344704, by rfl⟩ : syracuseStep 1792939 = 2689409) B2689409
theorem B1792951 : Blo 1792097 1792951 := bstep (se 1 (by rfl) ⟨1344713, by rfl⟩ : syracuseStep 1792951 = 2689427) B2689427
theorem B1792971 : Blo 1792097 1792971 := bstep (se 1 (by rfl) ⟨1344728, by rfl⟩ : syracuseStep 1792971 = 2689457) B2689457
theorem B1792983 : Blo 1792097 1792983 := bstep (se 1 (by rfl) ⟨1344737, by rfl⟩ : syracuseStep 1792983 = 2689475) B2689475
theorem B1793003 : Blo 1792097 1793003 := bstep (se 1 (by rfl) ⟨1344752, by rfl⟩ : syracuseStep 1793003 = 2689505) B2689505
theorem B1793015 : Blo 1792097 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1793035 : Blo 1792097 1793035 := bstep (se 1 (by rfl) ⟨1344776, by rfl⟩ : syracuseStep 1793035 = 2689553) B2689553
theorem B20413457 : Blo 1792097 20413457 := bstep (se 2 (by rfl) ⟨7655046, by rfl⟩ : syracuseStep 20413457 = 15310093) B15310093
theorem B4537367 : Blo 1792097 4537367 := bstep (se 1 (by rfl) ⟨3403025, by rfl⟩ : syracuseStep 4537367 = 6806051) B6806051
theorem B6806551 : Blo 1792097 6806551 := bstep (se 1 (by rfl) ⟨5104913, by rfl⟩ : syracuseStep 6806551 = 10209827) B10209827
theorem B1793047 : Blo 1792097 1793047 := bstep (se 1 (by rfl) ⟨1344785, by rfl⟩ : syracuseStep 1793047 = 2689571) B2689571
theorem B1793067 : Blo 1792097 1793067 := bstep (se 1 (by rfl) ⟨1344800, by rfl⟩ : syracuseStep 1793067 = 2689601) B2689601
theorem B1793079 : Blo 1792097 1793079 := bstep (se 1 (by rfl) ⟨1344809, by rfl⟩ : syracuseStep 1793079 = 2689619) B2689619
theorem B3882049 : Blo 1792097 3882049 := bstep (se 2 (by rfl) ⟨1455768, by rfl⟩ : syracuseStep 3882049 = 2911537) B2911537
theorem B1793099 : Blo 1792097 1793099 := bstep (se 1 (by rfl) ⟨1344824, by rfl⟩ : syracuseStep 1793099 = 2689649) B2689649
theorem B1793111 : Blo 1792097 1793111 := bstep (se 1 (by rfl) ⟨1344833, by rfl⟩ : syracuseStep 1793111 = 2689667) B2689667
theorem B1793131 : Blo 1792097 1793131 := bstep (se 1 (by rfl) ⟨1344848, by rfl⟩ : syracuseStep 1793131 = 2689697) B2689697
theorem B1793143 : Blo 1792097 1793143 := bstep (se 1 (by rfl) ⟨1344857, by rfl⟩ : syracuseStep 1793143 = 2689715) B2689715
theorem B1793163 : Blo 1792097 1793163 := bstep (se 1 (by rfl) ⟨1344872, by rfl⟩ : syracuseStep 1793163 = 2689745) B2689745
theorem B1793175 : Blo 1792097 1793175 := bstep (se 1 (by rfl) ⟨1344881, by rfl⟩ : syracuseStep 1793175 = 2689763) B2689763
theorem B1793195 : Blo 1792097 1793195 := bstep (se 1 (by rfl) ⟨1344896, by rfl⟩ : syracuseStep 1793195 = 2689793) B2689793
theorem B1793207 : Blo 1792097 1793207 := bstep (se 1 (by rfl) ⟨1344905, by rfl⟩ : syracuseStep 1793207 = 2689811) B2689811
theorem B7871681 : Blo 1792097 7871681 := bstep (se 2 (by rfl) ⟨2951880, by rfl⟩ : syracuseStep 7871681 = 5903761) B5903761
theorem B1793227 : Blo 1792097 1793227 := bstep (se 1 (by rfl) ⟨1344920, by rfl⟩ : syracuseStep 1793227 = 2689841) B2689841
theorem B1793239 : Blo 1792097 1793239 := bstep (se 1 (by rfl) ⟨1344929, by rfl⟩ : syracuseStep 1793239 = 2689859) B2689859
theorem B4308185 : Blo 1792097 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B1793259 : Blo 1792097 1793259 := bstep (se 1 (by rfl) ⟨1344944, by rfl⟩ : syracuseStep 1793259 = 2689889) B2689889
theorem B1793271 : Blo 1792097 1793271 := bstep (se 1 (by rfl) ⟨1344953, by rfl⟩ : syracuseStep 1793271 = 2689907) B2689907
theorem B1793291 : Blo 1792097 1793291 := bstep (se 1 (by rfl) ⟨1344968, by rfl⟩ : syracuseStep 1793291 = 2689937) B2689937
theorem B1793303 : Blo 1792097 1793303 := bstep (se 1 (by rfl) ⟨1344977, by rfl⟩ : syracuseStep 1793303 = 2689955) B2689955
theorem B1793323 : Blo 1792097 1793323 := bstep (se 1 (by rfl) ⟨1344992, by rfl⟩ : syracuseStep 1793323 = 2689985) B2689985
theorem B1793335 : Blo 1792097 1793335 := bstep (se 1 (by rfl) ⟨1345001, by rfl⟩ : syracuseStep 1793335 = 2690003) B2690003
theorem B1793355 : Blo 1792097 1793355 := bstep (se 1 (by rfl) ⟨1345016, by rfl⟩ : syracuseStep 1793355 = 2690033) B2690033
theorem B1793367 : Blo 1792097 1793367 := bstep (se 1 (by rfl) ⟨1345025, by rfl⟩ : syracuseStep 1793367 = 2690051) B2690051
theorem B4603225 : Blo 1792097 4603225 := bstep (se 2 (by rfl) ⟨1726209, by rfl⟩ : syracuseStep 4603225 = 3452419) B3452419
theorem B4848989 : Blo 1792097 4848989 := bstep (se 3 (by rfl) ⟨909185, by rfl⟩ : syracuseStep 4848989 = 1818371) B1818371
theorem B1793387 : Blo 1792097 1793387 := bstep (se 1 (by rfl) ⟨1345040, by rfl⟩ : syracuseStep 1793387 = 2690081) B2690081
theorem B1793399 : Blo 1792097 1793399 := bstep (se 1 (by rfl) ⟨1345049, by rfl⟩ : syracuseStep 1793399 = 2690099) B2690099
theorem B1793419 : Blo 1792097 1793419 := bstep (se 1 (by rfl) ⟨1345064, by rfl⟩ : syracuseStep 1793419 = 2690129) B2690129
theorem B1793431 : Blo 1792097 1793431 := bstep (se 1 (by rfl) ⟨1345073, by rfl⟩ : syracuseStep 1793431 = 2690147) B2690147
theorem B1793451 : Blo 1792097 1793451 := bstep (se 1 (by rfl) ⟨1345088, by rfl⟩ : syracuseStep 1793451 = 2690177) B2690177
theorem B1793463 : Blo 1792097 1793463 := bstep (se 1 (by rfl) ⟨1345097, by rfl⟩ : syracuseStep 1793463 = 2690195) B2690195
theorem B1793483 : Blo 1792097 1793483 := bstep (se 1 (by rfl) ⟨1345112, by rfl⟩ : syracuseStep 1793483 = 2690225) B2690225
theorem B1793495 : Blo 1792097 1793495 := bstep (se 1 (by rfl) ⟨1345121, by rfl⟩ : syracuseStep 1793495 = 2690243) B2690243
theorem B1793515 : Blo 1792097 1793515 := bstep (se 1 (by rfl) ⟨1345136, by rfl⟩ : syracuseStep 1793515 = 2690273) B2690273
theorem B1793527 : Blo 1792097 1793527 := bstep (se 1 (by rfl) ⟨1345145, by rfl⟩ : syracuseStep 1793527 = 2690291) B2690291
theorem B7659011 : Blo 1792097 7659011 := bstep (se 1 (by rfl) ⟨5744258, by rfl⟩ : syracuseStep 7659011 = 11488517) B11488517
theorem B1793547 : Blo 1792097 1793547 := bstep (se 1 (by rfl) ⟨1345160, by rfl⟩ : syracuseStep 1793547 = 2690321) B2690321
theorem B1793559 : Blo 1792097 1793559 := bstep (se 1 (by rfl) ⟨1345169, by rfl⟩ : syracuseStep 1793559 = 2690339) B2690339
theorem B6053399 : Blo 1792097 6053399 := bstep (se 1 (by rfl) ⟨4540049, by rfl⟩ : syracuseStep 6053399 = 9080099) B9080099
theorem B1793579 : Blo 1792097 1793579 := bstep (se 1 (by rfl) ⟨1345184, by rfl⟩ : syracuseStep 1793579 = 2690369) B2690369
theorem B1793591 : Blo 1792097 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B1793611 : Blo 1792097 1793611 := bstep (se 1 (by rfl) ⟨1345208, by rfl⟩ : syracuseStep 1793611 = 2690417) B2690417
theorem B1793623 : Blo 1792097 1793623 := bstep (se 1 (by rfl) ⟨1345217, by rfl⟩ : syracuseStep 1793623 = 2690435) B2690435
theorem B43638365 : Blo 1792097 43638365 := bstep (se 3 (by rfl) ⟨8182193, by rfl⟩ : syracuseStep 43638365 = 16364387) B16364387
theorem B1793643 : Blo 1792097 1793643 := bstep (se 1 (by rfl) ⟨1345232, by rfl⟩ : syracuseStep 1793643 = 2690465) B2690465
theorem B1793655 : Blo 1792097 1793655 := bstep (se 1 (by rfl) ⟨1345241, by rfl⟩ : syracuseStep 1793655 = 2690483) B2690483
theorem B1793675 : Blo 1792097 1793675 := bstep (se 1 (by rfl) ⟨1345256, by rfl⟩ : syracuseStep 1793675 = 2690513) B2690513
theorem B1793687 : Blo 1792097 1793687 := bstep (se 1 (by rfl) ⟨1345265, by rfl⟩ : syracuseStep 1793687 = 2690531) B2690531
theorem B1793707 : Blo 1792097 1793707 := bstep (se 1 (by rfl) ⟨1345280, by rfl⟩ : syracuseStep 1793707 = 2690561) B2690561
theorem B1793719 : Blo 1792097 1793719 := bstep (se 1 (by rfl) ⟨1345289, by rfl⟩ : syracuseStep 1793719 = 2690579) B2690579
theorem B8289985 : Blo 1792097 8289985 := bstep (se 2 (by rfl) ⟨3108744, by rfl⟩ : syracuseStep 8289985 = 6217489) B6217489
theorem B1793739 : Blo 1792097 1793739 := bstep (se 1 (by rfl) ⟨1345304, by rfl⟩ : syracuseStep 1793739 = 2690609) B2690609
theorem B1793751 : Blo 1792097 1793751 := bstep (se 1 (by rfl) ⟨1345313, by rfl⟩ : syracuseStep 1793751 = 2690627) B2690627
theorem B1793771 : Blo 1792097 1793771 := bstep (se 1 (by rfl) ⟨1345328, by rfl⟩ : syracuseStep 1793771 = 2690657) B2690657
theorem B1793783 : Blo 1792097 1793783 := bstep (se 1 (by rfl) ⟨1345337, by rfl⟩ : syracuseStep 1793783 = 2690675) B2690675
theorem B1793803 : Blo 1792097 1793803 := bstep (se 1 (by rfl) ⟨1345352, by rfl⟩ : syracuseStep 1793803 = 2690705) B2690705
theorem B1793815 : Blo 1792097 1793815 := bstep (se 1 (by rfl) ⟨1345361, by rfl⟩ : syracuseStep 1793815 = 2690723) B2690723
theorem B1793835 : Blo 1792097 1793835 := bstep (se 1 (by rfl) ⟨1345376, by rfl⟩ : syracuseStep 1793835 = 2690753) B2690753
theorem B6807341 : Blo 1792097 6807341 := bstep (se 3 (by rfl) ⟨1276376, by rfl⟩ : syracuseStep 6807341 = 2552753) B2552753
theorem B1793847 : Blo 1792097 1793847 := bstep (se 1 (by rfl) ⟨1345385, by rfl⟩ : syracuseStep 1793847 = 2690771) B2690771
theorem B4538177 : Blo 1792097 4538177 := bstep (se 2 (by rfl) ⟨1701816, by rfl⟩ : syracuseStep 4538177 = 3403633) B3403633
theorem B1793867 : Blo 1792097 1793867 := bstep (se 1 (by rfl) ⟨1345400, by rfl⟩ : syracuseStep 1793867 = 2690801) B2690801
theorem B1793879 : Blo 1792097 1793879 := bstep (se 1 (by rfl) ⟨1345409, by rfl⟩ : syracuseStep 1793879 = 2690819) B2690819
theorem B7659353 : Blo 1792097 7659353 := bstep (se 2 (by rfl) ⟨2872257, by rfl⟩ : syracuseStep 7659353 = 5744515) B5744515
theorem B1793899 : Blo 1792097 1793899 := bstep (se 1 (by rfl) ⟨1345424, by rfl⟩ : syracuseStep 1793899 = 2690849) B2690849
theorem B1793911 : Blo 1792097 1793911 := bstep (se 1 (by rfl) ⟨1345433, by rfl⟩ : syracuseStep 1793911 = 2690867) B2690867
theorem B1793931 : Blo 1792097 1793931 := bstep (se 1 (by rfl) ⟨1345448, by rfl⟩ : syracuseStep 1793931 = 2690897) B2690897
theorem B1793943 : Blo 1792097 1793943 := bstep (se 1 (by rfl) ⟨1345457, by rfl⟩ : syracuseStep 1793943 = 2690915) B2690915
theorem B1793963 : Blo 1792097 1793963 := bstep (se 1 (by rfl) ⟨1345472, by rfl⟩ : syracuseStep 1793963 = 2690945) B2690945
theorem B1793975 : Blo 1792097 1793975 := bstep (se 1 (by rfl) ⟨1345481, by rfl⟩ : syracuseStep 1793975 = 2690963) B2690963
theorem B2154443 : Blo 1792097 2154443 := bstep (se 1 (by rfl) ⟨1615832, by rfl⟩ : syracuseStep 2154443 = 3231665) B3231665
theorem B1793995 : Blo 1792097 1793995 := bstep (se 1 (by rfl) ⟨1345496, by rfl⟩ : syracuseStep 1793995 = 2690993) B2690993
theorem B1794007 : Blo 1792097 1794007 := bstep (se 1 (by rfl) ⟨1345505, by rfl⟩ : syracuseStep 1794007 = 2691011) B2691011
theorem B9076697 : Blo 1792097 9076697 := bstep (se 2 (by rfl) ⟨3403761, by rfl⟩ : syracuseStep 9076697 = 6807523) B6807523
theorem B17235929 : Blo 1792097 17235929 := bstep (se 2 (by rfl) ⟨6463473, by rfl⟩ : syracuseStep 17235929 = 12926947) B12926947
theorem B66338777 : Blo 1792097 66338777 := bstep (se 2 (by rfl) ⟨24877041, by rfl⟩ : syracuseStep 66338777 = 49754083) B49754083
theorem B1794027 : Blo 1792097 1794027 := bstep (se 1 (by rfl) ⟨1345520, by rfl⟩ : syracuseStep 1794027 = 2691041) B2691041
theorem B1794039 : Blo 1792097 1794039 := bstep (se 1 (by rfl) ⟨1345529, by rfl⟩ : syracuseStep 1794039 = 2691059) B2691059
theorem B4538369 : Blo 1792097 4538369 := bstep (se 2 (by rfl) ⟨1701888, by rfl⟩ : syracuseStep 4538369 = 3403777) B3403777
theorem B1794055 : Blo 1792097 1794055 := bstep (se 1 (by rfl) ⟨1345541, by rfl⟩ : syracuseStep 1794055 = 2691083) B2691083
theorem B1794063 : Blo 1792097 1794063 := bstep (se 1 (by rfl) ⟨1345547, by rfl⟩ : syracuseStep 1794063 = 2691095) B2691095
theorem B26198039 : Blo 1792097 26198039 := bstep (se 1 (by rfl) ⟨19648529, by rfl⟩ : syracuseStep 26198039 = 39297059) B39297059
theorem B46579805 : Blo 1792097 46579805 := bstep (se 3 (by rfl) ⟨8733713, by rfl⟩ : syracuseStep 46579805 = 17467427) B17467427
theorem B14540933 : Blo 1792097 14540933 := bstep (se 4 (by rfl) ⟨1363212, by rfl⟩ : syracuseStep 14540933 = 2726425) B2726425
theorem B2269559 : Blo 1792097 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B4538825 : Blo 1792097 4538825 := bstep (se 2 (by rfl) ⟨1702059, by rfl⟩ : syracuseStep 4538825 = 3404119) B3404119
theorem B2589175 : Blo 1792097 2589175 := bstep (se 1 (by rfl) ⟨1941881, by rfl⟩ : syracuseStep 2589175 = 3883763) B3883763
theorem B2269711 : Blo 1792097 2269711 := bstep (se 1 (by rfl) ⟨1702283, by rfl⟩ : syracuseStep 2269711 = 3404567) B3404567
theorem B19382813 : Blo 1792097 19382813 := bstep (se 3 (by rfl) ⟨3634277, by rfl⟩ : syracuseStep 19382813 = 7268555) B7268555
theorem B2269883 : Blo 1792097 2269883 := bstep (se 1 (by rfl) ⟨1702412, by rfl⟩ : syracuseStep 2269883 = 3404825) B3404825
theorem B4539179 : Blo 1792097 4539179 := bstep (se 1 (by rfl) ⟨3404384, by rfl⟩ : syracuseStep 4539179 = 6808769) B6808769
theorem B10208051 : Blo 1792097 10208051 := bstep (se 1 (by rfl) ⟨7656038, by rfl⟩ : syracuseStep 10208051 = 15312077) B15312077
theorem B4981565 : Blo 1792097 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B6054803 : Blo 1792097 6054803 := bstep (se 1 (by rfl) ⟨4541102, by rfl⟩ : syracuseStep 6054803 = 9082205) B9082205
theorem B13616261 : Blo 1792097 13616261 := bstep (se 4 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 13616261 = 2553049) B2553049
theorem B2016391 : Blo 1792097 2016391 := bstep (se 1 (by rfl) ⟨1512293, by rfl⟩ : syracuseStep 2016391 = 3024587) B3024587
theorem B2688185 : Blo 1792097 2688185 := bstep (se 2 (by rfl) ⟨1008069, by rfl⟩ : syracuseStep 2688185 = 2016139) B2016139
theorem B6464713 : Blo 1792097 6464713 := bstep (se 2 (by rfl) ⟨2424267, by rfl⟩ : syracuseStep 6464713 = 4848535) B4848535
theorem B2688263 : Blo 1792097 2688263 := bstep (se 1 (by rfl) ⟨2016197, by rfl⟩ : syracuseStep 2688263 = 4032395) B4032395
theorem B2688299 : Blo 1792097 2688299 := bstep (se 1 (by rfl) ⟨2016224, by rfl⟩ : syracuseStep 2688299 = 4032449) B4032449
theorem B2016571 : Blo 1792097 2016571 := bstep (se 1 (by rfl) ⟨1512428, by rfl⟩ : syracuseStep 2016571 = 3024857) B3024857
theorem B2688329 : Blo 1792097 2688329 := bstep (se 2 (by rfl) ⟨1008123, by rfl⟩ : syracuseStep 2688329 = 2016247) B2016247
theorem B3024263 : Blo 1792097 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B6808967 : Blo 1792097 6808967 := bstep (se 1 (by rfl) ⟨5106725, by rfl⟩ : syracuseStep 6808967 = 10213451) B10213451
theorem B2688443 : Blo 1792097 2688443 := bstep (se 1 (by rfl) ⟨2016332, by rfl⟩ : syracuseStep 2688443 = 4032665) B4032665
theorem B2688503 : Blo 1792097 2688503 := bstep (se 1 (by rfl) ⟨2016377, by rfl⟩ : syracuseStep 2688503 = 4032755) B4032755
theorem B2688527 : Blo 1792097 2688527 := bstep (se 1 (by rfl) ⟨2016395, by rfl⟩ : syracuseStep 2688527 = 4032791) B4032791
theorem B2688569 : Blo 1792097 2688569 := bstep (se 2 (by rfl) ⟨1008213, by rfl⟩ : syracuseStep 2688569 = 2016427) B2016427
theorem B116368973 : Blo 1792097 116368973 := bstep (se 3 (by rfl) ⟨21819182, by rfl⟩ : syracuseStep 116368973 = 43638365) B43638365
theorem B2688647 : Blo 1792097 2688647 := bstep (se 1 (by rfl) ⟨2016485, by rfl⟩ : syracuseStep 2688647 = 4032971) B4032971
theorem B2688683 : Blo 1792097 2688683 := bstep (se 1 (by rfl) ⟨2016512, by rfl⟩ : syracuseStep 2688683 = 4033025) B4033025
theorem B2688713 : Blo 1792097 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B4540171 : Blo 1792097 4540171 := bstep (se 1 (by rfl) ⟨3405128, by rfl⟩ : syracuseStep 4540171 = 6810257) B6810257
theorem B3065615 : Blo 1792097 3065615 := bstep (se 1 (by rfl) ⟨2299211, by rfl⟩ : syracuseStep 3065615 = 4598423) B4598423
theorem B2017039 : Blo 1792097 2017039 := bstep (se 1 (by rfl) ⟨1512779, by rfl⟩ : syracuseStep 2017039 = 3025559) B3025559
theorem B6137633 : Blo 1792097 6137633 := bstep (se 2 (by rfl) ⟨2301612, by rfl⟩ : syracuseStep 6137633 = 4603225) B4603225
theorem B2688827 : Blo 1792097 2688827 := bstep (se 1 (by rfl) ⟨2016620, by rfl⟩ : syracuseStep 2688827 = 4033241) B4033241
theorem B19392371 : Blo 1792097 19392371 := bstep (se 1 (by rfl) ⟨14544278, by rfl⟩ : syracuseStep 19392371 = 29088557) B29088557
theorem B2688887 : Blo 1792097 2688887 := bstep (se 1 (by rfl) ⟨2016665, by rfl⟩ : syracuseStep 2688887 = 4033331) B4033331
theorem B2688911 : Blo 1792097 2688911 := bstep (se 1 (by rfl) ⟨2016683, by rfl⟩ : syracuseStep 2688911 = 4033367) B4033367
theorem B4540313 : Blo 1792097 4540313 := bstep (se 2 (by rfl) ⟨1702617, by rfl⟩ : syracuseStep 4540313 = 3405235) B3405235
theorem B2688953 : Blo 1792097 2688953 := bstep (se 2 (by rfl) ⟨1008357, by rfl⟩ : syracuseStep 2688953 = 2016715) B2016715
theorem B2689031 : Blo 1792097 2689031 := bstep (se 1 (by rfl) ⟨2016773, by rfl⟩ : syracuseStep 2689031 = 4033547) B4033547
theorem B13608971 : Blo 1792097 13608971 := bstep (se 1 (by rfl) ⟨10206728, by rfl⟩ : syracuseStep 13608971 = 20413457) B20413457
theorem B3024911 : Blo 1792097 3024911 := bstep (se 1 (by rfl) ⟨2268683, by rfl⟩ : syracuseStep 3024911 = 4537367) B4537367
theorem B2689067 : Blo 1792097 2689067 := bstep (se 1 (by rfl) ⟨2016800, by rfl⟩ : syracuseStep 2689067 = 4033601) B4033601
theorem B4540475 : Blo 1792097 4540475 := bstep (se 1 (by rfl) ⟨3405356, by rfl⟩ : syracuseStep 4540475 = 6810713) B6810713
theorem B2689097 : Blo 1792097 2689097 := bstep (se 2 (by rfl) ⟨1008411, by rfl⟩ : syracuseStep 2689097 = 2016823) B2016823
theorem B4032647 : Blo 1792097 4032647 := bstep (se 1 (by rfl) ⟨3024485, by rfl⟩ : syracuseStep 4032647 = 6048971) B6048971
theorem B2689211 : Blo 1792097 2689211 := bstep (se 1 (by rfl) ⟨2016908, by rfl⟩ : syracuseStep 2689211 = 4033817) B4033817
theorem B10209509 : Blo 1792097 10209509 := bstep (se 4 (by rfl) ⟨957141, by rfl⟩ : syracuseStep 10209509 = 1914283) B1914283
theorem B2689271 : Blo 1792097 2689271 := bstep (se 1 (by rfl) ⟨2016953, by rfl⟩ : syracuseStep 2689271 = 4033907) B4033907
theorem B11053313 : Blo 1792097 11053313 := bstep (se 2 (by rfl) ⟨4144992, by rfl⟩ : syracuseStep 11053313 = 8289985) B8289985
theorem B2017543 : Blo 1792097 2017543 := bstep (se 1 (by rfl) ⟨1513157, by rfl⟩ : syracuseStep 2017543 = 3026315) B3026315
theorem B2689295 : Blo 1792097 2689295 := bstep (se 1 (by rfl) ⟨2016971, by rfl⟩ : syracuseStep 2689295 = 4033943) B4033943
theorem B2689337 : Blo 1792097 2689337 := bstep (se 2 (by rfl) ⟨1008501, by rfl⟩ : syracuseStep 2689337 = 2017003) B2017003
theorem B4032827 : Blo 1792097 4032827 := bstep (se 1 (by rfl) ⟨3024620, by rfl⟩ : syracuseStep 4032827 = 6049241) B6049241
theorem B8735035 : Blo 1792097 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B5106007 : Blo 1792097 5106007 := bstep (se 1 (by rfl) ⟨3829505, by rfl⟩ : syracuseStep 5106007 = 7659011) B7659011
theorem B2689415 : Blo 1792097 2689415 := bstep (se 1 (by rfl) ⟨2017061, by rfl⟩ : syracuseStep 2689415 = 4034123) B4034123
theorem B4540819 : Blo 1792097 4540819 := bstep (se 1 (by rfl) ⟨3405614, by rfl⟩ : syracuseStep 4540819 = 6811229) B6811229
theorem B2689451 : Blo 1792097 2689451 := bstep (se 1 (by rfl) ⟨2017088, by rfl⟩ : syracuseStep 2689451 = 4034177) B4034177
theorem B4032953 : Blo 1792097 4032953 := bstep (se 2 (by rfl) ⟨1512357, by rfl⟩ : syracuseStep 4032953 = 3024715) B3024715
theorem B2017723 : Blo 1792097 2017723 := bstep (se 1 (by rfl) ⟨1513292, by rfl⟩ : syracuseStep 2017723 = 3026585) B3026585
theorem B2689481 : Blo 1792097 2689481 := bstep (se 2 (by rfl) ⟨1008555, by rfl⟩ : syracuseStep 2689481 = 2017111) B2017111
theorem B5745181 : Blo 1792097 5745181 := bstep (se 3 (by rfl) ⟨1077221, by rfl⟩ : syracuseStep 5745181 = 2154443) B2154443
theorem B4540961 : Blo 1792097 4540961 := bstep (se 2 (by rfl) ⟨1702860, by rfl⟩ : syracuseStep 4540961 = 3405721) B3405721
theorem B3025451 : Blo 1792097 3025451 := bstep (se 1 (by rfl) ⟨2269088, by rfl⟩ : syracuseStep 3025451 = 4538177) B4538177
theorem B2689595 : Blo 1792097 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B5106235 : Blo 1792097 5106235 := bstep (se 1 (by rfl) ⟨3829676, by rfl⟩ : syracuseStep 5106235 = 7659353) B7659353
theorem B2689655 : Blo 1792097 2689655 := bstep (se 1 (by rfl) ⟨2017241, by rfl⟩ : syracuseStep 2689655 = 4034483) B4034483
theorem B2689679 : Blo 1792097 2689679 := bstep (se 1 (by rfl) ⟨2017259, by rfl⟩ : syracuseStep 2689679 = 4034519) B4034519
theorem B3402425 : Blo 1792097 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B2689721 : Blo 1792097 2689721 := bstep (se 2 (by rfl) ⟨1008645, by rfl⟩ : syracuseStep 2689721 = 2017291) B2017291
theorem B5106361 : Blo 1792097 5106361 := bstep (se 2 (by rfl) ⟨1914885, by rfl⟩ : syracuseStep 5106361 = 3829771) B3829771
theorem B2689799 : Blo 1792097 2689799 := bstep (se 1 (by rfl) ⟨2017349, by rfl⟩ : syracuseStep 2689799 = 4034699) B4034699
theorem B4033295 : Blo 1792097 4033295 := bstep (se 1 (by rfl) ⟨3024971, by rfl⟩ : syracuseStep 4033295 = 6049943) B6049943
theorem B4033313 : Blo 1792097 4033313 := bstep (se 2 (by rfl) ⟨1512492, by rfl⟩ : syracuseStep 4033313 = 3024985) B3024985
theorem B2689835 : Blo 1792097 2689835 := bstep (se 1 (by rfl) ⟨2017376, by rfl⟩ : syracuseStep 2689835 = 4034753) B4034753
theorem B2689865 : Blo 1792097 2689865 := bstep (se 2 (by rfl) ⟨1008699, by rfl⟩ : syracuseStep 2689865 = 2017399) B2017399
theorem B6048647 : Blo 1792097 6048647 := bstep (se 1 (by rfl) ⟨4536485, by rfl⟩ : syracuseStep 6048647 = 9072971) B9072971
theorem B2018191 : Blo 1792097 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B3025849 : Blo 1792097 3025849 := bstep (se 2 (by rfl) ⟨1134693, by rfl⟩ : syracuseStep 3025849 = 2269387) B2269387
theorem B2689979 : Blo 1792097 2689979 := bstep (se 1 (by rfl) ⟨2017484, by rfl⟩ : syracuseStep 2689979 = 4034969) B4034969
theorem B2690039 : Blo 1792097 2690039 := bstep (se 1 (by rfl) ⟨2017529, by rfl⟩ : syracuseStep 2690039 = 4035059) B4035059
theorem B20704261 : Blo 1792097 20704261 := bstep (se 4 (by rfl) ⟨1941024, by rfl⟩ : syracuseStep 20704261 = 3882049) B3882049
theorem B8293387 : Blo 1792097 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B2690063 : Blo 1792097 2690063 := bstep (se 1 (by rfl) ⟨2017547, by rfl⟩ : syracuseStep 2690063 = 4035095) B4035095
theorem B9956375 : Blo 1792097 9956375 := bstep (se 1 (by rfl) ⟨7467281, by rfl⟩ : syracuseStep 9956375 = 14934563) B14934563
theorem B2690105 : Blo 1792097 2690105 := bstep (se 2 (by rfl) ⟨1008789, by rfl⟩ : syracuseStep 2690105 = 2017579) B2017579
theorem B4033655 : Blo 1792097 4033655 := bstep (se 1 (by rfl) ⟨3025241, by rfl⟩ : syracuseStep 4033655 = 6050483) B6050483
theorem B6810743 : Blo 1792097 6810743 := bstep (se 1 (by rfl) ⟨5108057, by rfl⟩ : syracuseStep 6810743 = 10216115) B10216115
theorem B2690183 : Blo 1792097 2690183 := bstep (se 1 (by rfl) ⟨2017637, by rfl⟩ : syracuseStep 2690183 = 4035275) B4035275
theorem B3828883 : Blo 1792097 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B2690219 : Blo 1792097 2690219 := bstep (se 1 (by rfl) ⟨2017664, by rfl⟩ : syracuseStep 2690219 = 4035329) B4035329
theorem B4844729 : Blo 1792097 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B2690249 : Blo 1792097 2690249 := bstep (se 2 (by rfl) ⟨1008843, by rfl⟩ : syracuseStep 2690249 = 2017687) B2017687
theorem B11488493 : Blo 1792097 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B6049025 : Blo 1792097 6049025 := bstep (se 2 (by rfl) ⟨2268384, by rfl⟩ : syracuseStep 6049025 = 4536769) B4536769
theorem B4033835 : Blo 1792097 4033835 := bstep (se 1 (by rfl) ⟨3025376, by rfl⟩ : syracuseStep 4033835 = 6050753) B6050753
theorem B2690363 : Blo 1792097 2690363 := bstep (se 1 (by rfl) ⟨2017772, by rfl⟩ : syracuseStep 2690363 = 4035545) B4035545
theorem B2690423 : Blo 1792097 2690423 := bstep (se 1 (by rfl) ⟨2017817, by rfl⟩ : syracuseStep 2690423 = 4035635) B4035635
theorem B2690447 : Blo 1792097 2690447 := bstep (se 1 (by rfl) ⟨2017835, by rfl⟩ : syracuseStep 2690447 = 4035671) B4035671
theorem B2690489 : Blo 1792097 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B9203165 : Blo 1792097 9203165 := bstep (se 3 (by rfl) ⟨1725593, by rfl⟩ : syracuseStep 9203165 = 3451187) B3451187
theorem B13618691 : Blo 1792097 13618691 := bstep (se 1 (by rfl) ⟨10214018, by rfl⟩ : syracuseStep 13618691 = 20428037) B20428037
theorem B2690567 : Blo 1792097 2690567 := bstep (se 1 (by rfl) ⟨2017925, by rfl⟩ : syracuseStep 2690567 = 4035851) B4035851
theorem B2690603 : Blo 1792097 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B7654979 : Blo 1792097 7654979 := bstep (se 1 (by rfl) ⟨5741234, by rfl⟩ : syracuseStep 7654979 = 11482469) B11482469
theorem B2690633 : Blo 1792097 2690633 := bstep (se 2 (by rfl) ⟨1008987, by rfl⟩ : syracuseStep 2690633 = 2017975) B2017975
theorem B3026551 : Blo 1792097 3026551 := bstep (se 1 (by rfl) ⟨2269913, by rfl⟩ : syracuseStep 3026551 = 4539827) B4539827
theorem B4034195 : Blo 1792097 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B2690747 : Blo 1792097 2690747 := bstep (se 1 (by rfl) ⟨2018060, by rfl⟩ : syracuseStep 2690747 = 4036121) B4036121
theorem B4034249 : Blo 1792097 4034249 := bstep (se 2 (by rfl) ⟨1512843, by rfl⟩ : syracuseStep 4034249 = 3025687) B3025687
theorem B2690807 : Blo 1792097 2690807 := bstep (se 1 (by rfl) ⟨2018105, by rfl⟩ : syracuseStep 2690807 = 4036211) B4036211
theorem B2690831 : Blo 1792097 2690831 := bstep (se 1 (by rfl) ⟨2018123, by rfl⟩ : syracuseStep 2690831 = 4036247) B4036247
theorem B4091681 : Blo 1792097 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B2690873 : Blo 1792097 2690873 := bstep (se 2 (by rfl) ⟨1009077, by rfl⟩ : syracuseStep 2690873 = 2018155) B2018155
theorem B3026747 : Blo 1792097 3026747 := bstep (se 1 (by rfl) ⟨2270060, by rfl⟩ : syracuseStep 3026747 = 4540121) B4540121
theorem B12922739 : Blo 1792097 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B2690951 : Blo 1792097 2690951 := bstep (se 1 (by rfl) ⟨2018213, by rfl⟩ : syracuseStep 2690951 = 4036427) B4036427
theorem B13610915 : Blo 1792097 13610915 := bstep (se 1 (by rfl) ⟨10208186, by rfl⟩ : syracuseStep 13610915 = 20416373) B20416373
theorem B2690987 : Blo 1792097 2690987 := bstep (se 1 (by rfl) ⟨2018240, by rfl⟩ : syracuseStep 2690987 = 4036481) B4036481
theorem B4599737 : Blo 1792097 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B2691017 : Blo 1792097 2691017 := bstep (se 2 (by rfl) ⟨1009131, by rfl⟩ : syracuseStep 2691017 = 2018263) B2018263
theorem B19378187 : Blo 1792097 19378187 := bstep (se 1 (by rfl) ⟨14533640, by rfl⟩ : syracuseStep 19378187 = 29067281) B29067281
theorem B6049835 : Blo 1792097 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B2691131 : Blo 1792097 2691131 := bstep (se 1 (by rfl) ⟨2018348, by rfl⟩ : syracuseStep 2691131 = 4036697) B4036697
theorem B6811715 : Blo 1792097 6811715 := bstep (se 1 (by rfl) ⟨5108786, by rfl⟩ : syracuseStep 6811715 = 10217573) B10217573
theorem B3027145 : Blo 1792097 3027145 := bstep (se 2 (by rfl) ⟨1135179, by rfl⟩ : syracuseStep 3027145 = 2270359) B2270359
theorem B7762157 : Blo 1792097 7762157 := bstep (se 3 (by rfl) ⟨1455404, by rfl⟩ : syracuseStep 7762157 = 2910809) B2910809
theorem B14373179 : Blo 1792097 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B4034951 : Blo 1792097 4034951 := bstep (se 1 (by rfl) ⟨3026213, by rfl⟩ : syracuseStep 4034951 = 6052427) B6052427
theorem B9081233 : Blo 1792097 9081233 := bstep (se 2 (by rfl) ⟨3405462, by rfl⟩ : syracuseStep 9081233 = 6810925) B6810925
theorem B5747129 : Blo 1792097 5747129 := bstep (se 2 (by rfl) ⟨2155173, by rfl⟩ : syracuseStep 5747129 = 4310347) B4310347
theorem B13808171 : Blo 1792097 13808171 := bstep (se 1 (by rfl) ⟨10356128, by rfl⟩ : syracuseStep 13808171 = 20712257) B20712257
theorem B4035131 : Blo 1792097 4035131 := bstep (se 1 (by rfl) ⟨3026348, by rfl⟩ : syracuseStep 4035131 = 6052697) B6052697
theorem B5108285 : Blo 1792097 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B4600435 : Blo 1792097 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B32698999 : Blo 1792097 32698999 := bstep (se 1 (by rfl) ⟨24524249, by rfl⟩ : syracuseStep 32698999 = 49048499) B49048499
theorem B3404423 : Blo 1792097 3404423 := bstep (se 1 (by rfl) ⟨2553317, by rfl⟩ : syracuseStep 3404423 = 5106635) B5106635
theorem B4035257 : Blo 1792097 4035257 := bstep (se 2 (by rfl) ⟨1513221, by rfl⟩ : syracuseStep 4035257 = 3026443) B3026443
theorem B20419289 : Blo 1792097 20419289 := bstep (se 2 (by rfl) ⟨7657233, by rfl⟩ : syracuseStep 20419289 = 15314467) B15314467
theorem B9204461 : Blo 1792097 9204461 := bstep (se 3 (by rfl) ⟨1725836, by rfl⟩ : syracuseStep 9204461 = 3451673) B3451673
theorem B8516353 : Blo 1792097 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B7271183 : Blo 1792097 7271183 := bstep (se 1 (by rfl) ⟨5453387, by rfl⟩ : syracuseStep 7271183 = 10906775) B10906775
theorem B5247787 : Blo 1792097 5247787 := bstep (se 1 (by rfl) ⟨3935840, by rfl⟩ : syracuseStep 5247787 = 7871681) B7871681
theorem B5747591 : Blo 1792097 5747591 := bstep (se 1 (by rfl) ⟨4310693, by rfl⟩ : syracuseStep 5747591 = 8621387) B8621387
theorem B87274421 : Blo 1792097 87274421 := bstep (se 5 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 87274421 = 8181977) B8181977
theorem B4035599 : Blo 1792097 4035599 := bstep (se 1 (by rfl) ⟨3026699, by rfl⟩ : syracuseStep 4035599 = 6053399) B6053399
theorem B4846625 : Blo 1792097 4846625 := bstep (se 2 (by rfl) ⟨1817484, by rfl⟩ : syracuseStep 4846625 = 3634969) B3634969
theorem B4035617 : Blo 1792097 4035617 := bstep (se 2 (by rfl) ⟨1513356, by rfl⟩ : syracuseStep 4035617 = 3026713) B3026713
theorem B5174425 : Blo 1792097 5174425 := bstep (se 2 (by rfl) ⟨1940409, by rfl⟩ : syracuseStep 5174425 = 3880819) B3880819
theorem B2422073 : Blo 1792097 2422073 := bstep (se 2 (by rfl) ⟨908277, by rfl⟩ : syracuseStep 2422073 = 1816555) B1816555
theorem B6051131 : Blo 1792097 6051131 := bstep (se 1 (by rfl) ⟨4538348, by rfl⟩ : syracuseStep 6051131 = 9076697) B9076697
theorem B11490619 : Blo 1792097 11490619 := bstep (se 1 (by rfl) ⟨8617964, by rfl⟩ : syracuseStep 11490619 = 17235929) B17235929
theorem B44225851 : Blo 1792097 44225851 := bstep (se 1 (by rfl) ⟨33169388, by rfl⟩ : syracuseStep 44225851 = 66338777) B66338777
theorem B18412859 : Blo 1792097 18412859 := bstep (se 1 (by rfl) ⟨13809644, by rfl⟩ : syracuseStep 18412859 = 27619289) B27619289
theorem B4035959 : Blo 1792097 4035959 := bstep (se 1 (by rfl) ⟨3026969, by rfl⟩ : syracuseStep 4035959 = 6053939) B6053939
theorem B10212743 : Blo 1792097 10212743 := bstep (se 1 (by rfl) ⟨7659557, by rfl⟩ : syracuseStep 10212743 = 15319115) B15319115
theorem B5453191 : Blo 1792097 5453191 := bstep (se 1 (by rfl) ⟨4089893, by rfl⟩ : syracuseStep 5453191 = 8179787) B8179787
theorem B15324551 : Blo 1792097 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B34952627 : Blo 1792097 34952627 := bstep (se 1 (by rfl) ⟨26214470, by rfl⟩ : syracuseStep 34952627 = 52428941) B52428941
theorem B9074105 : Blo 1792097 9074105 := bstep (se 2 (by rfl) ⟨3402789, by rfl⟩ : syracuseStep 9074105 = 6805579) B6805579
theorem B9197009 : Blo 1792097 9197009 := bstep (se 2 (by rfl) ⟨3448878, by rfl⟩ : syracuseStep 9197009 = 6897757) B6897757
theorem B2872847 : Blo 1792097 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B4036139 : Blo 1792097 4036139 := bstep (se 1 (by rfl) ⟨3027104, by rfl⟩ : syracuseStep 4036139 = 6054209) B6054209
theorem B3880507 : Blo 1792097 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B10212925 : Blo 1792097 10212925 := bstep (se 3 (by rfl) ⟨1914923, by rfl⟩ : syracuseStep 10212925 = 3829847) B3829847
theorem B6805079 : Blo 1792097 6805079 := bstep (se 1 (by rfl) ⟨5103809, by rfl⟩ : syracuseStep 6805079 = 10207619) B10207619
theorem B7272023 : Blo 1792097 7272023 := bstep (se 1 (by rfl) ⟨5454017, by rfl⟩ : syracuseStep 7272023 = 10908035) B10908035
theorem B2553545 : Blo 1792097 2553545 := bstep (se 2 (by rfl) ⟨957579, by rfl⟩ : syracuseStep 2553545 = 1915159) B1915159
theorem B6051617 : Blo 1792097 6051617 := bstep (se 2 (by rfl) ⟨2269356, by rfl⟩ : syracuseStep 6051617 = 4538713) B4538713
theorem B4036499 : Blo 1792097 4036499 := bstep (se 1 (by rfl) ⟨3027374, by rfl⟩ : syracuseStep 4036499 = 6054749) B6054749
theorem B2725817 : Blo 1792097 2725817 := bstep (se 2 (by rfl) ⟨1022181, by rfl⟩ : syracuseStep 2725817 = 2044363) B2044363
theorem B4036553 : Blo 1792097 4036553 := bstep (se 2 (by rfl) ⟨1513707, by rfl⟩ : syracuseStep 4036553 = 3027415) B3027415
theorem B4307003 : Blo 1792097 4307003 := bstep (se 1 (by rfl) ⟨3230252, by rfl⟩ : syracuseStep 4307003 = 6460505) B6460505
theorem B6805565 : Blo 1792097 6805565 := bstep (se 3 (by rfl) ⟨1276043, by rfl⟩ : syracuseStep 6805565 = 2552087) B2552087
theorem B5822525 : Blo 1792097 5822525 := bstep (se 3 (by rfl) ⟨1091723, by rfl⟩ : syracuseStep 5822525 = 2183447) B2183447
theorem B1792135 : Blo 1792097 1792135 := bstep (se 1 (by rfl) ⟨1344101, by rfl⟩ : syracuseStep 1792135 = 2688203) B2688203
theorem B1792143 : Blo 1792097 1792143 := bstep (se 1 (by rfl) ⟨1344107, by rfl⟩ : syracuseStep 1792143 = 2688215) B2688215
theorem B1792187 : Blo 1792097 1792187 := bstep (se 1 (by rfl) ⟨1344140, by rfl⟩ : syracuseStep 1792187 = 2688281) B2688281
theorem B44202185 : Blo 1792097 44202185 := bstep (se 2 (by rfl) ⟨16575819, by rfl⟩ : syracuseStep 44202185 = 33151639) B33151639
theorem B1792263 : Blo 1792097 1792263 := bstep (se 1 (by rfl) ⟨1344197, by rfl⟩ : syracuseStep 1792263 = 2688395) B2688395
theorem B4536587 : Blo 1792097 4536587 := bstep (se 1 (by rfl) ⟨3402440, by rfl⟩ : syracuseStep 4536587 = 6804881) B6804881
theorem B1792271 : Blo 1792097 1792271 := bstep (se 1 (by rfl) ⟨1344203, by rfl⟩ : syracuseStep 1792271 = 2688407) B2688407
theorem B13613345 : Blo 1792097 13613345 := bstep (se 2 (by rfl) ⟨5105004, by rfl⟩ : syracuseStep 13613345 = 10210009) B10210009
theorem B51722549 : Blo 1792097 51722549 := bstep (se 5 (by rfl) ⟨2424494, by rfl⟩ : syracuseStep 51722549 = 4848989) B4848989
theorem B1792315 : Blo 1792097 1792315 := bstep (se 1 (by rfl) ⟨1344236, by rfl⟩ : syracuseStep 1792315 = 2688473) B2688473
theorem B6052211 : Blo 1792097 6052211 := bstep (se 1 (by rfl) ⟨4539158, by rfl⟩ : syracuseStep 6052211 = 9078317) B9078317
theorem B1792391 : Blo 1792097 1792391 := bstep (se 1 (by rfl) ⟨1344293, by rfl⟩ : syracuseStep 1792391 = 2688587) B2688587
theorem B1792399 : Blo 1792097 1792399 := bstep (se 1 (by rfl) ⟨1344299, by rfl⟩ : syracuseStep 1792399 = 2688599) B2688599
theorem B1792443 : Blo 1792097 1792443 := bstep (se 1 (by rfl) ⟨1344332, by rfl⟩ : syracuseStep 1792443 = 2688665) B2688665
theorem B5454337 : Blo 1792097 5454337 := bstep (se 2 (by rfl) ⟨2045376, by rfl⟩ : syracuseStep 5454337 = 4090753) B4090753
theorem B1792519 : Blo 1792097 1792519 := bstep (se 1 (by rfl) ⟨1344389, by rfl⟩ : syracuseStep 1792519 = 2688779) B2688779
theorem B1792527 : Blo 1792097 1792527 := bstep (se 1 (by rfl) ⟨1344395, by rfl⟩ : syracuseStep 1792527 = 2688791) B2688791
theorem B2554411 : Blo 1792097 2554411 := bstep (se 1 (by rfl) ⟨1915808, by rfl⟩ : syracuseStep 2554411 = 3831617) B3831617
theorem B1792571 : Blo 1792097 1792571 := bstep (se 1 (by rfl) ⟨1344428, by rfl⟩ : syracuseStep 1792571 = 2688857) B2688857
theorem B1792647 : Blo 1792097 1792647 := bstep (se 1 (by rfl) ⟨1344485, by rfl⟩ : syracuseStep 1792647 = 2688971) B2688971
theorem B1792655 : Blo 1792097 1792655 := bstep (se 1 (by rfl) ⟨1344491, by rfl⟩ : syracuseStep 1792655 = 2688983) B2688983
theorem B1915535 : Blo 1792097 1915535 := bstep (se 1 (by rfl) ⟨1436651, by rfl⟩ : syracuseStep 1915535 = 2873303) B2873303
theorem B1792699 : Blo 1792097 1792699 := bstep (se 1 (by rfl) ⟨1344524, by rfl⟩ : syracuseStep 1792699 = 2689049) B2689049
theorem B9075401 : Blo 1792097 9075401 := bstep (se 2 (by rfl) ⟨3403275, by rfl⟩ : syracuseStep 9075401 = 6806551) B6806551
theorem B1792775 : Blo 1792097 1792775 := bstep (se 1 (by rfl) ⟨1344581, by rfl⟩ : syracuseStep 1792775 = 2689163) B2689163
theorem B1792783 : Blo 1792097 1792783 := bstep (se 1 (by rfl) ⟨1344587, by rfl⟩ : syracuseStep 1792783 = 2689175) B2689175
theorem B1792827 : Blo 1792097 1792827 := bstep (se 1 (by rfl) ⟨1344620, by rfl⟩ : syracuseStep 1792827 = 2689241) B2689241
theorem B1792903 : Blo 1792097 1792903 := bstep (se 1 (by rfl) ⟨1344677, by rfl⟩ : syracuseStep 1792903 = 2689355) B2689355
theorem B1792911 : Blo 1792097 1792911 := bstep (se 1 (by rfl) ⟨1344683, by rfl⟩ : syracuseStep 1792911 = 2689367) B2689367
theorem B4537235 : Blo 1792097 4537235 := bstep (se 1 (by rfl) ⟨3402926, by rfl⟩ : syracuseStep 4537235 = 6805853) B6805853
theorem B1792955 : Blo 1792097 1792955 := bstep (se 1 (by rfl) ⟨1344716, by rfl⟩ : syracuseStep 1792955 = 2689433) B2689433
theorem B1793031 : Blo 1792097 1793031 := bstep (se 1 (by rfl) ⟨1344773, by rfl⟩ : syracuseStep 1793031 = 2689547) B2689547
theorem B31472651 : Blo 1792097 31472651 := bstep (se 1 (by rfl) ⟨23604488, by rfl⟩ : syracuseStep 31472651 = 47208977) B47208977
theorem B1793039 : Blo 1792097 1793039 := bstep (se 1 (by rfl) ⟨1344779, by rfl⟩ : syracuseStep 1793039 = 2689559) B2689559
theorem B1793083 : Blo 1792097 1793083 := bstep (se 1 (by rfl) ⟨1344812, by rfl⟩ : syracuseStep 1793083 = 2689625) B2689625
theorem B6462551 : Blo 1792097 6462551 := bstep (se 1 (by rfl) ⟨4846913, by rfl⟩ : syracuseStep 6462551 = 9693827) B9693827
theorem B1793159 : Blo 1792097 1793159 := bstep (se 1 (by rfl) ⟨1344869, by rfl⟩ : syracuseStep 1793159 = 2689739) B2689739
theorem B1793167 : Blo 1792097 1793167 := bstep (se 1 (by rfl) ⟨1344875, by rfl⟩ : syracuseStep 1793167 = 2689751) B2689751
theorem B2727083 : Blo 1792097 2727083 := bstep (se 1 (by rfl) ⟨2045312, by rfl⟩ : syracuseStep 2727083 = 4090625) B4090625
theorem B4537529 : Blo 1792097 4537529 := bstep (se 2 (by rfl) ⟨1701573, by rfl⟩ : syracuseStep 4537529 = 3403147) B3403147
theorem B1793211 : Blo 1792097 1793211 := bstep (se 1 (by rfl) ⟨1344908, by rfl⟩ : syracuseStep 1793211 = 2689817) B2689817
theorem B13614317 : Blo 1792097 13614317 := bstep (se 3 (by rfl) ⟨2552684, by rfl⟩ : syracuseStep 13614317 = 5105369) B5105369
theorem B10214657 : Blo 1792097 10214657 := bstep (se 2 (by rfl) ⟨3830496, by rfl⟩ : syracuseStep 10214657 = 7660993) B7660993
theorem B1793287 : Blo 1792097 1793287 := bstep (se 1 (by rfl) ⟨1344965, by rfl⟩ : syracuseStep 1793287 = 2689931) B2689931
theorem B1793295 : Blo 1792097 1793295 := bstep (se 1 (by rfl) ⟨1344971, by rfl⟩ : syracuseStep 1793295 = 2689943) B2689943
theorem B67198267 : Blo 1792097 67198267 := bstep (se 1 (by rfl) ⟨50398700, by rfl⟩ : syracuseStep 67198267 = 100797401) B100797401
theorem B1793339 : Blo 1792097 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B1793415 : Blo 1792097 1793415 := bstep (se 1 (by rfl) ⟨1345061, by rfl⟩ : syracuseStep 1793415 = 2690123) B2690123
theorem B1793423 : Blo 1792097 1793423 := bstep (se 1 (by rfl) ⟨1345067, by rfl⟩ : syracuseStep 1793423 = 2690135) B2690135
theorem B2268587 : Blo 1792097 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B1793467 : Blo 1792097 1793467 := bstep (se 1 (by rfl) ⟨1345100, by rfl⟩ : syracuseStep 1793467 = 2690201) B2690201
theorem B1793543 : Blo 1792097 1793543 := bstep (se 1 (by rfl) ⟨1345157, by rfl⟩ : syracuseStep 1793543 = 2690315) B2690315
theorem B1793551 : Blo 1792097 1793551 := bstep (se 1 (by rfl) ⟨1345163, by rfl⟩ : syracuseStep 1793551 = 2690327) B2690327
theorem B1793595 : Blo 1792097 1793595 := bstep (se 1 (by rfl) ⟨1345196, by rfl⟩ : syracuseStep 1793595 = 2690393) B2690393
theorem B36789835 : Blo 1792097 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B1793671 : Blo 1792097 1793671 := bstep (se 1 (by rfl) ⟨1345253, by rfl⟩ : syracuseStep 1793671 = 2690507) B2690507
theorem B1793679 : Blo 1792097 1793679 := bstep (se 1 (by rfl) ⟨1345259, by rfl⟩ : syracuseStep 1793679 = 2690519) B2690519
theorem B1793723 : Blo 1792097 1793723 := bstep (se 1 (by rfl) ⟨1345292, by rfl⟩ : syracuseStep 1793723 = 2690585) B2690585
theorem B11484929 : Blo 1792097 11484929 := bstep (se 2 (by rfl) ⟨4306848, by rfl⟩ : syracuseStep 11484929 = 8613697) B8613697
theorem B1793799 : Blo 1792097 1793799 := bstep (se 1 (by rfl) ⟨1345349, by rfl⟩ : syracuseStep 1793799 = 2690699) B2690699
theorem B6807311 : Blo 1792097 6807311 := bstep (se 1 (by rfl) ⟨5105483, by rfl⟩ : syracuseStep 6807311 = 10210967) B10210967
theorem B1793807 : Blo 1792097 1793807 := bstep (se 1 (by rfl) ⟨1345355, by rfl⟩ : syracuseStep 1793807 = 2690711) B2690711
theorem B1793851 : Blo 1792097 1793851 := bstep (se 1 (by rfl) ⟨1345388, by rfl⟩ : syracuseStep 1793851 = 2690777) B2690777
theorem B4538227 : Blo 1792097 4538227 := bstep (se 1 (by rfl) ⟨3403670, by rfl⟩ : syracuseStep 4538227 = 6807341) B6807341
theorem B5103479 : Blo 1792097 5103479 := bstep (se 1 (by rfl) ⟨3827609, by rfl⟩ : syracuseStep 5103479 = 7655219) B7655219
theorem B2269063 : Blo 1792097 2269063 := bstep (se 1 (by rfl) ⟨1701797, by rfl⟩ : syracuseStep 2269063 = 3403595) B3403595
theorem B1793927 : Blo 1792097 1793927 := bstep (se 1 (by rfl) ⟨1345445, by rfl⟩ : syracuseStep 1793927 = 2690891) B2690891
theorem B1793935 : Blo 1792097 1793935 := bstep (se 1 (by rfl) ⟨1345451, by rfl⟩ : syracuseStep 1793935 = 2690903) B2690903
theorem B1793979 : Blo 1792097 1793979 := bstep (se 1 (by rfl) ⟨1345484, by rfl⟩ : syracuseStep 1793979 = 2690969) B2690969
theorem B12918791 : Blo 1792097 12918791 := bstep (se 1 (by rfl) ⟨9689093, by rfl⟩ : syracuseStep 12918791 = 19378187) B19378187
theorem B1794087 : Blo 1792097 1794087 := bstep (se 1 (by rfl) ⟨1345565, by rfl⟩ : syracuseStep 1794087 = 2691131) B2691131
theorem B69861437 : Blo 1792097 69861437 := bstep (se 3 (by rfl) ⟨13099019, by rfl⟩ : syracuseStep 69861437 = 26198039) B26198039
theorem B6054155 : Blo 1792097 6054155 := bstep (se 1 (by rfl) ⟨4540616, by rfl⟩ : syracuseStep 6054155 = 9081233) B9081233
theorem B2269615 : Blo 1792097 2269615 := bstep (se 1 (by rfl) ⟨1702211, by rfl⟩ : syracuseStep 2269615 = 3404423) B3404423
theorem B6808009 : Blo 1792097 6808009 := bstep (se 2 (by rfl) ⟨2553003, by rfl⟩ : syracuseStep 6808009 = 5106007) B5106007
theorem B12919277 : Blo 1792097 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B6136307 : Blo 1792097 6136307 := bstep (se 1 (by rfl) ⟨4602230, by rfl⟩ : syracuseStep 6136307 = 9204461) B9204461
theorem B6054425 : Blo 1792097 6054425 := bstep (se 2 (by rfl) ⟨2270409, by rfl⟩ : syracuseStep 6054425 = 4540819) B4540819
theorem B7660241 : Blo 1792097 7660241 := bstep (se 2 (by rfl) ⟨2872590, by rfl⟩ : syracuseStep 7660241 = 5745181) B5745181
theorem B6808313 : Blo 1792097 6808313 := bstep (se 2 (by rfl) ⟨2553117, by rfl⟩ : syracuseStep 6808313 = 5106235) B5106235
theorem B9077507 : Blo 1792097 9077507 := bstep (se 1 (by rfl) ⟨6808130, by rfl⟩ : syracuseStep 9077507 = 13616261) B13616261
theorem B43598665 : Blo 1792097 43598665 := bstep (se 2 (by rfl) ⟨16349499, by rfl⟩ : syracuseStep 43598665 = 32698999) B32698999
theorem B6808481 : Blo 1792097 6808481 := bstep (se 2 (by rfl) ⟨2553180, by rfl⟩ : syracuseStep 6808481 = 5106361) B5106361
theorem B2016175 : Blo 1792097 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B6808495 : Blo 1792097 6808495 := bstep (se 1 (by rfl) ⟨5106371, by rfl⟩ : syracuseStep 6808495 = 10212743) B10212743
theorem B4539311 : Blo 1792097 4539311 := bstep (se 1 (by rfl) ⟨3404483, by rfl⟩ : syracuseStep 4539311 = 6808967) B6808967
theorem B10216367 : Blo 1792097 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B11355137 : Blo 1792097 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B77579315 : Blo 1792097 77579315 := bstep (se 1 (by rfl) ⟨58184486, by rfl⟩ : syracuseStep 77579315 = 116368973) B116368973
theorem B6997049 : Blo 1792097 6997049 := bstep (se 2 (by rfl) ⟨2623893, by rfl⟩ : syracuseStep 6997049 = 5247787) B5247787
theorem B12928247 : Blo 1792097 12928247 := bstep (se 1 (by rfl) ⟨9696185, by rfl⟩ : syracuseStep 12928247 = 19392371) B19392371
theorem B2016607 : Blo 1792097 2016607 := bstep (se 1 (by rfl) ⟨1512455, by rfl⟩ : syracuseStep 2016607 = 3024911) B3024911
theorem B7660925 : Blo 1792097 7660925 := bstep (se 3 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 7660925 = 2872847) B2872847
theorem B2688431 : Blo 1792097 2688431 := bstep (se 1 (by rfl) ⟨2016323, by rfl⟩ : syracuseStep 2688431 = 4032647) B4032647
theorem B29468123 : Blo 1792097 29468123 := bstep (se 1 (by rfl) ⟨22101092, by rfl⟩ : syracuseStep 29468123 = 44202185) B44202185
theorem B3024391 : Blo 1792097 3024391 := bstep (se 1 (by rfl) ⟨2268293, by rfl⟩ : syracuseStep 3024391 = 4536587) B4536587
theorem B2688521 : Blo 1792097 2688521 := bstep (se 2 (by rfl) ⟨1008195, by rfl⟩ : syracuseStep 2688521 = 2016391) B2016391
theorem B5105177 : Blo 1792097 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B34481699 : Blo 1792097 34481699 := bstep (se 1 (by rfl) ⟨25861274, by rfl⟩ : syracuseStep 34481699 = 51722549) B51722549
theorem B2688551 : Blo 1792097 2688551 := bstep (se 1 (by rfl) ⟨2016413, by rfl⟩ : syracuseStep 2688551 = 4032827) B4032827
theorem B19392061 : Blo 1792097 19392061 := bstep (se 3 (by rfl) ⟨3636011, by rfl⟩ : syracuseStep 19392061 = 7272023) B7272023
theorem B8619617 : Blo 1792097 8619617 := bstep (se 2 (by rfl) ⟨3232356, by rfl⟩ : syracuseStep 8619617 = 6464713) B6464713
theorem B2688635 : Blo 1792097 2688635 := bstep (se 1 (by rfl) ⟨2016476, by rfl⟩ : syracuseStep 2688635 = 4032953) B4032953
theorem B2016967 : Blo 1792097 2016967 := bstep (se 1 (by rfl) ⟨1512725, by rfl⟩ : syracuseStep 2016967 = 3025451) B3025451
theorem B2688761 : Blo 1792097 2688761 := bstep (se 2 (by rfl) ⟨1008285, by rfl⟩ : syracuseStep 2688761 = 2016571) B2016571
theorem B15320825 : Blo 1792097 15320825 := bstep (se 2 (by rfl) ⟨5745309, by rfl⟩ : syracuseStep 15320825 = 11490619) B11490619
theorem B58967801 : Blo 1792097 58967801 := bstep (se 2 (by rfl) ⟨22112925, by rfl⟩ : syracuseStep 58967801 = 44225851) B44225851
theorem B2688863 : Blo 1792097 2688863 := bstep (se 1 (by rfl) ⟨2016647, by rfl⟩ : syracuseStep 2688863 = 4033295) B4033295
theorem B2688875 : Blo 1792097 2688875 := bstep (se 1 (by rfl) ⟨2016656, by rfl⟩ : syracuseStep 2688875 = 4033313) B4033313
theorem B6809453 : Blo 1792097 6809453 := bstep (se 3 (by rfl) ⟨1276772, by rfl⟩ : syracuseStep 6809453 = 2553545) B2553545
theorem B4032431 : Blo 1792097 4032431 := bstep (se 1 (by rfl) ⟨3024323, by rfl⟩ : syracuseStep 4032431 = 6048647) B6048647
theorem B29075381 : Blo 1792097 29075381 := bstep (se 5 (by rfl) ⟨1362908, by rfl⟩ : syracuseStep 29075381 = 2725817) B2725817
theorem B3024823 : Blo 1792097 3024823 := bstep (se 1 (by rfl) ⟨2268617, by rfl⟩ : syracuseStep 3024823 = 4537235) B4537235
theorem B20981767 : Blo 1792097 20981767 := bstep (se 1 (by rfl) ⟨15736325, by rfl⟩ : syracuseStep 20981767 = 31472651) B31472651
theorem B6637583 : Blo 1792097 6637583 := bstep (se 1 (by rfl) ⟨4978187, by rfl⟩ : syracuseStep 6637583 = 9956375) B9956375
theorem B2689103 : Blo 1792097 2689103 := bstep (se 1 (by rfl) ⟨2016827, by rfl⟩ : syracuseStep 2689103 = 4033655) B4033655
theorem B4540495 : Blo 1792097 4540495 := bstep (se 1 (by rfl) ⟨3405371, by rfl⟩ : syracuseStep 4540495 = 6810743) B6810743
theorem B13617233 : Blo 1792097 13617233 := bstep (se 2 (by rfl) ⟨5106462, by rfl⟩ : syracuseStep 13617233 = 10212925) B10212925
theorem B3025019 : Blo 1792097 3025019 := bstep (se 1 (by rfl) ⟨2268764, by rfl⟩ : syracuseStep 3025019 = 4537529) B4537529
theorem B4032683 : Blo 1792097 4032683 := bstep (se 1 (by rfl) ⟨3024512, by rfl⟩ : syracuseStep 4032683 = 6049025) B6049025
theorem B6809771 : Blo 1792097 6809771 := bstep (se 1 (by rfl) ⟨5107328, by rfl⟩ : syracuseStep 6809771 = 10214657) B10214657
theorem B2689223 : Blo 1792097 2689223 := bstep (se 1 (by rfl) ⟨2016917, by rfl⟩ : syracuseStep 2689223 = 4033835) B4033835
theorem B9079127 : Blo 1792097 9079127 := bstep (se 1 (by rfl) ⟨6809345, by rfl⟩ : syracuseStep 9079127 = 13618691) B13618691
theorem B2689385 : Blo 1792097 2689385 := bstep (se 2 (by rfl) ⟨1008519, by rfl⟩ : syracuseStep 2689385 = 2017039) B2017039
theorem B2689463 : Blo 1792097 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B2689499 : Blo 1792097 2689499 := bstep (se 1 (by rfl) ⟨2017124, by rfl⟩ : syracuseStep 2689499 = 4034249) B4034249
theorem B3025417 : Blo 1792097 3025417 := bstep (se 2 (by rfl) ⟨1134531, by rfl⟩ : syracuseStep 3025417 = 2269063) B2269063
theorem B2017831 : Blo 1792097 2017831 := bstep (se 1 (by rfl) ⟨1513373, by rfl⟩ : syracuseStep 2017831 = 3026747) B3026747
theorem B3402319 : Blo 1792097 3402319 := bstep (se 1 (by rfl) ⟨2551739, by rfl⟩ : syracuseStep 3402319 = 5103479) B5103479
theorem B3066491 : Blo 1792097 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B3025579 : Blo 1792097 3025579 := bstep (se 1 (by rfl) ⟨2269184, by rfl⟩ : syracuseStep 3025579 = 4538369) B4538369
theorem B4033223 : Blo 1792097 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B4541143 : Blo 1792097 4541143 := bstep (se 1 (by rfl) ⟨3405857, by rfl⟩ : syracuseStep 4541143 = 6811715) B6811715
theorem B9693955 : Blo 1792097 9693955 := bstep (se 1 (by rfl) ⟨7270466, by rfl⟩ : syracuseStep 9693955 = 14540933) B14540933
theorem B15526733 : Blo 1792097 15526733 := bstep (se 3 (by rfl) ⟨2911262, by rfl⟩ : syracuseStep 15526733 = 5822525) B5822525
theorem B2689967 : Blo 1792097 2689967 := bstep (se 1 (by rfl) ⟨2017475, by rfl⟩ : syracuseStep 2689967 = 4034951) B4034951
theorem B3025883 : Blo 1792097 3025883 := bstep (se 1 (by rfl) ⟨2269412, by rfl⟩ : syracuseStep 3025883 = 4538825) B4538825
theorem B2690057 : Blo 1792097 2690057 := bstep (se 2 (by rfl) ⟨1008771, by rfl⟩ : syracuseStep 2690057 = 2017543) B2017543
theorem B12921875 : Blo 1792097 12921875 := bstep (se 1 (by rfl) ⟨9691406, by rfl⟩ : syracuseStep 12921875 = 19382813) B19382813
theorem B2690087 : Blo 1792097 2690087 := bstep (se 1 (by rfl) ⟨2017565, by rfl⟩ : syracuseStep 2690087 = 4035131) B4035131
theorem B2690171 : Blo 1792097 2690171 := bstep (se 1 (by rfl) ⟨2017628, by rfl⟩ : syracuseStep 2690171 = 4035257) B4035257
theorem B3026119 : Blo 1792097 3026119 := bstep (se 1 (by rfl) ⟨2269589, by rfl⟩ : syracuseStep 3026119 = 4539179) B4539179
theorem B3321043 : Blo 1792097 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B2690297 : Blo 1792097 2690297 := bstep (se 2 (by rfl) ⟨1008861, by rfl⟩ : syracuseStep 2690297 = 2017723) B2017723
theorem B58182947 : Blo 1792097 58182947 := bstep (se 1 (by rfl) ⟨43637210, by rfl⟩ : syracuseStep 58182947 = 87274421) B87274421
theorem B2690399 : Blo 1792097 2690399 := bstep (se 1 (by rfl) ⟨2017799, by rfl⟩ : syracuseStep 2690399 = 4035599) B4035599
theorem B3026281 : Blo 1792097 3026281 := bstep (se 2 (by rfl) ⟨1134855, by rfl⟩ : syracuseStep 3026281 = 2269711) B2269711
theorem B3231083 : Blo 1792097 3231083 := bstep (se 1 (by rfl) ⟨2423312, by rfl⟩ : syracuseStep 3231083 = 4846625) B4846625
theorem B2690411 : Blo 1792097 2690411 := bstep (se 1 (by rfl) ⟨2017808, by rfl⟩ : syracuseStep 2690411 = 4035617) B4035617
theorem B6458861 : Blo 1792097 6458861 := bstep (se 3 (by rfl) ⟨1211036, by rfl⟩ : syracuseStep 6458861 = 2422073) B2422073
theorem B4034087 : Blo 1792097 4034087 := bstep (se 1 (by rfl) ⟨3025565, by rfl⟩ : syracuseStep 4034087 = 6051131) B6051131
theorem B12275239 : Blo 1792097 12275239 := bstep (se 1 (by rfl) ⟨9206429, by rfl⟩ : syracuseStep 12275239 = 18412859) B18412859
theorem B2690639 : Blo 1792097 2690639 := bstep (se 1 (by rfl) ⟨2017979, by rfl⟩ : syracuseStep 2690639 = 4035959) B4035959
theorem B23301751 : Blo 1792097 23301751 := bstep (se 1 (by rfl) ⟨17476313, by rfl⟩ : syracuseStep 23301751 = 34952627) B34952627
theorem B6049403 : Blo 1792097 6049403 := bstep (se 1 (by rfl) ⟨4537052, by rfl⟩ : syracuseStep 6049403 = 9074105) B9074105
theorem B6131339 : Blo 1792097 6131339 := bstep (se 1 (by rfl) ⟨4598504, by rfl⟩ : syracuseStep 6131339 = 9197009) B9197009
theorem B2690759 : Blo 1792097 2690759 := bstep (se 1 (by rfl) ⟨2018069, by rfl⟩ : syracuseStep 2690759 = 4036139) B4036139
theorem B6049565 : Blo 1792097 6049565 := bstep (se 3 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 6049565 = 2268587) B2268587
theorem B2043743 : Blo 1792097 2043743 := bstep (se 1 (by rfl) ⟨1532807, by rfl⟩ : syracuseStep 2043743 = 3065615) B3065615
theorem B2690921 : Blo 1792097 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B4034411 : Blo 1792097 4034411 := bstep (se 1 (by rfl) ⟨3025808, by rfl⟩ : syracuseStep 4034411 = 6051617) B6051617
theorem B4034465 : Blo 1792097 4034465 := bstep (se 2 (by rfl) ⟨1512924, by rfl⟩ : syracuseStep 4034465 = 3025849) B3025849
theorem B2690999 : Blo 1792097 2690999 := bstep (se 1 (by rfl) ⟨2018249, by rfl⟩ : syracuseStep 2690999 = 4036499) B4036499
theorem B3026875 : Blo 1792097 3026875 := bstep (se 1 (by rfl) ⟨2270156, by rfl⟩ : syracuseStep 3026875 = 4540313) B4540313
theorem B2691035 : Blo 1792097 2691035 := bstep (se 1 (by rfl) ⟨2018276, by rfl⟩ : syracuseStep 2691035 = 4036553) B4036553
theorem B9072647 : Blo 1792097 9072647 := bstep (se 1 (by rfl) ⟨6804485, by rfl⟩ : syracuseStep 9072647 = 13608971) B13608971
theorem B2871335 : Blo 1792097 2871335 := bstep (se 1 (by rfl) ⟨2153501, by rfl⟩ : syracuseStep 2871335 = 4307003) B4307003
theorem B3026983 : Blo 1792097 3026983 := bstep (se 1 (by rfl) ⟨2270237, by rfl⟩ : syracuseStep 3026983 = 4540475) B4540475
theorem B7368875 : Blo 1792097 7368875 := bstep (se 1 (by rfl) ⟨5526656, by rfl⟩ : syracuseStep 7368875 = 11053313) B11053313
theorem B4034807 : Blo 1792097 4034807 := bstep (se 1 (by rfl) ⟨3026105, by rfl⟩ : syracuseStep 4034807 = 6052211) B6052211
theorem B3027307 : Blo 1792097 3027307 := bstep (se 1 (by rfl) ⟨2270480, by rfl⟩ : syracuseStep 3027307 = 4540961) B4540961
theorem B5108093 : Blo 1792097 5108093 := bstep (se 3 (by rfl) ⟨957767, by rfl⟩ : syracuseStep 5108093 = 1915535) B1915535
theorem B6050267 : Blo 1792097 6050267 := bstep (se 1 (by rfl) ⟨4537700, by rfl⟩ : syracuseStep 6050267 = 9075401) B9075401
theorem B9073133 : Blo 1792097 9073133 := bstep (se 3 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 9073133 = 3402425) B3402425
theorem B7270921 : Blo 1792097 7270921 := bstep (se 2 (by rfl) ⟨2726595, by rfl⟩ : syracuseStep 7270921 = 5453191) B5453191
theorem B5174009 : Blo 1792097 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B4035401 : Blo 1792097 4035401 := bstep (se 2 (by rfl) ⟨1513275, by rfl⟩ : syracuseStep 4035401 = 3026551) B3026551
theorem B6050969 : Blo 1792097 6050969 := bstep (se 2 (by rfl) ⟨2269113, by rfl⟩ : syracuseStep 6050969 = 4538227) B4538227
theorem B7656619 : Blo 1792097 7656619 := bstep (se 1 (by rfl) ⟨5742464, by rfl⟩ : syracuseStep 7656619 = 11484929) B11484929
theorem B8615159 : Blo 1792097 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B9073943 : Blo 1792097 9073943 := bstep (se 1 (by rfl) ⟨6805457, by rfl⟩ : syracuseStep 9073943 = 13610915) B13610915
theorem B13808933 : Blo 1792097 13808933 := bstep (se 4 (by rfl) ⟨1294587, by rfl⟩ : syracuseStep 13808933 = 2589175) B2589175
theorem B31053203 : Blo 1792097 31053203 := bstep (se 1 (by rfl) ⟨23289902, by rfl⟩ : syracuseStep 31053203 = 46579805) B46579805
theorem B5174771 : Blo 1792097 5174771 := bstep (se 1 (by rfl) ⟨3881078, by rfl⟩ : syracuseStep 5174771 = 7762157) B7762157
theorem B9582119 : Blo 1792097 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B17233469 : Blo 1792097 17233469 := bstep (se 3 (by rfl) ⟨3231275, by rfl⟩ : syracuseStep 17233469 = 6462551) B6462551
theorem B4036193 : Blo 1792097 4036193 := bstep (se 2 (by rfl) ⟨1513572, by rfl⟩ : syracuseStep 4036193 = 3027145) B3027145
theorem B3831419 : Blo 1792097 3831419 := bstep (se 1 (by rfl) ⟨2873564, by rfl⟩ : syracuseStep 3831419 = 5747129) B5747129
theorem B11646713 : Blo 1792097 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B13612859 : Blo 1792097 13612859 := bstep (se 1 (by rfl) ⟨10209644, by rfl⟩ : syracuseStep 13612859 = 20419289) B20419289
theorem B4847455 : Blo 1792097 4847455 := bstep (se 1 (by rfl) ⟨3635591, by rfl⟩ : syracuseStep 4847455 = 7271183) B7271183
theorem B6805367 : Blo 1792097 6805367 := bstep (se 1 (by rfl) ⟨5104025, by rfl⟩ : syracuseStep 6805367 = 10208051) B10208051
theorem B3831727 : Blo 1792097 3831727 := bstep (se 1 (by rfl) ⟨2873795, by rfl⟩ : syracuseStep 3831727 = 5747591) B5747591
theorem B4036535 : Blo 1792097 4036535 := bstep (se 1 (by rfl) ⟨3027401, by rfl⟩ : syracuseStep 4036535 = 6054803) B6054803
theorem B7272449 : Blo 1792097 7272449 := bstep (se 2 (by rfl) ⟨2727168, by rfl⟩ : syracuseStep 7272449 = 5454337) B5454337
theorem B3405881 : Blo 1792097 3405881 := bstep (se 2 (by rfl) ⟨1277205, by rfl⟩ : syracuseStep 3405881 = 2554411) B2554411
theorem B1792123 : Blo 1792097 1792123 := bstep (se 1 (by rfl) ⟨1344092, by rfl⟩ : syracuseStep 1792123 = 2688185) B2688185
theorem B27596933 : Blo 1792097 27596933 := bstep (se 4 (by rfl) ⟨2587212, by rfl⟩ : syracuseStep 27596933 = 5174425) B5174425
theorem B6133913 : Blo 1792097 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B1792175 : Blo 1792097 1792175 := bstep (se 1 (by rfl) ⟨1344131, by rfl⟩ : syracuseStep 1792175 = 2688263) B2688263
theorem B1792199 : Blo 1792097 1792199 := bstep (se 1 (by rfl) ⟨1344149, by rfl⟩ : syracuseStep 1792199 = 2688299) B2688299
theorem B1792219 : Blo 1792097 1792219 := bstep (se 1 (by rfl) ⟨1344164, by rfl⟩ : syracuseStep 1792219 = 2688329) B2688329
theorem B1792295 : Blo 1792097 1792295 := bstep (se 1 (by rfl) ⟨1344221, by rfl⟩ : syracuseStep 1792295 = 2688443) B2688443
theorem B6052157 : Blo 1792097 6052157 := bstep (se 3 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 6052157 = 2269559) B2269559
theorem B1792335 : Blo 1792097 1792335 := bstep (se 1 (by rfl) ⟨1344251, by rfl⟩ : syracuseStep 1792335 = 2688503) B2688503
theorem B1792351 : Blo 1792097 1792351 := bstep (se 1 (by rfl) ⟨1344263, by rfl⟩ : syracuseStep 1792351 = 2688527) B2688527
theorem B1792379 : Blo 1792097 1792379 := bstep (se 1 (by rfl) ⟨1344284, by rfl⟩ : syracuseStep 1792379 = 2688569) B2688569
theorem B4536719 : Blo 1792097 4536719 := bstep (se 1 (by rfl) ⟨3402539, by rfl⟩ : syracuseStep 4536719 = 6805079) B6805079
theorem B1792431 : Blo 1792097 1792431 := bstep (se 1 (by rfl) ⟨1344323, by rfl⟩ : syracuseStep 1792431 = 2688647) B2688647
theorem B1792455 : Blo 1792097 1792455 := bstep (se 1 (by rfl) ⟨1344341, by rfl⟩ : syracuseStep 1792455 = 2688683) B2688683
theorem B1792475 : Blo 1792097 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B1792551 : Blo 1792097 1792551 := bstep (se 1 (by rfl) ⟨1344413, by rfl⟩ : syracuseStep 1792551 = 2688827) B2688827
theorem B1792591 : Blo 1792097 1792591 := bstep (se 1 (by rfl) ⟨1344443, by rfl⟩ : syracuseStep 1792591 = 2688887) B2688887
theorem B1792607 : Blo 1792097 1792607 := bstep (se 1 (by rfl) ⟨1344455, by rfl⟩ : syracuseStep 1792607 = 2688911) B2688911
theorem B1792635 : Blo 1792097 1792635 := bstep (se 1 (by rfl) ⟨1344476, by rfl⟩ : syracuseStep 1792635 = 2688953) B2688953
theorem B1792687 : Blo 1792097 1792687 := bstep (se 1 (by rfl) ⟨1344515, by rfl⟩ : syracuseStep 1792687 = 2689031) B2689031
theorem B27605681 : Blo 1792097 27605681 := bstep (se 2 (by rfl) ⟨10352130, by rfl⟩ : syracuseStep 27605681 = 20704261) B20704261
theorem B11057849 : Blo 1792097 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B1792711 : Blo 1792097 1792711 := bstep (se 1 (by rfl) ⟨1344533, by rfl⟩ : syracuseStep 1792711 = 2689067) B2689067
theorem B4537043 : Blo 1792097 4537043 := bstep (se 1 (by rfl) ⟨3402782, by rfl⟩ : syracuseStep 4537043 = 6805565) B6805565
theorem B1792731 : Blo 1792097 1792731 := bstep (se 1 (by rfl) ⟨1344548, by rfl⟩ : syracuseStep 1792731 = 2689097) B2689097
theorem B36821789 : Blo 1792097 36821789 := bstep (se 3 (by rfl) ⟨6904085, by rfl⟩ : syracuseStep 36821789 = 13808171) B13808171
theorem B1792807 : Blo 1792097 1792807 := bstep (se 1 (by rfl) ⟨1344605, by rfl⟩ : syracuseStep 1792807 = 2689211) B2689211
theorem B6806339 : Blo 1792097 6806339 := bstep (se 1 (by rfl) ⟨5104754, by rfl⟩ : syracuseStep 6806339 = 10209509) B10209509
theorem B13622093 : Blo 1792097 13622093 := bstep (se 3 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 13622093 = 5108285) B5108285
theorem B1792847 : Blo 1792097 1792847 := bstep (se 1 (by rfl) ⟨1344635, by rfl⟩ : syracuseStep 1792847 = 2689271) B2689271
theorem B1792863 : Blo 1792097 1792863 := bstep (se 1 (by rfl) ⟨1344647, by rfl⟩ : syracuseStep 1792863 = 2689295) B2689295
theorem B9075563 : Blo 1792097 9075563 := bstep (se 1 (by rfl) ⟨6806672, by rfl⟩ : syracuseStep 9075563 = 13613345) B13613345
theorem B1792891 : Blo 1792097 1792891 := bstep (se 1 (by rfl) ⟨1344668, by rfl⟩ : syracuseStep 1792891 = 2689337) B2689337
theorem B1792943 : Blo 1792097 1792943 := bstep (se 1 (by rfl) ⟨1344707, by rfl⟩ : syracuseStep 1792943 = 2689415) B2689415
theorem B1792967 : Blo 1792097 1792967 := bstep (se 1 (by rfl) ⟨1344725, by rfl⟩ : syracuseStep 1792967 = 2689451) B2689451
theorem B1792987 : Blo 1792097 1792987 := bstep (se 1 (by rfl) ⟨1344740, by rfl⟩ : syracuseStep 1792987 = 2689481) B2689481
theorem B358390757 : Blo 1792097 358390757 := bstep (se 4 (by rfl) ⟨33599133, by rfl⟩ : syracuseStep 358390757 = 67198267) B67198267
theorem B1793063 : Blo 1792097 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1793103 : Blo 1792097 1793103 := bstep (se 1 (by rfl) ⟨1344827, by rfl⟩ : syracuseStep 1793103 = 2689655) B2689655
theorem B1793119 : Blo 1792097 1793119 := bstep (se 1 (by rfl) ⟨1344839, by rfl⟩ : syracuseStep 1793119 = 2689679) B2689679
theorem B1793147 : Blo 1792097 1793147 := bstep (se 1 (by rfl) ⟨1344860, by rfl⟩ : syracuseStep 1793147 = 2689721) B2689721
theorem B6053021 : Blo 1792097 6053021 := bstep (se 3 (by rfl) ⟨1134941, by rfl⟩ : syracuseStep 6053021 = 2269883) B2269883
theorem B1793199 : Blo 1792097 1793199 := bstep (se 1 (by rfl) ⟨1344899, by rfl⟩ : syracuseStep 1793199 = 2689799) B2689799
theorem B1793223 : Blo 1792097 1793223 := bstep (se 1 (by rfl) ⟨1344917, by rfl⟩ : syracuseStep 1793223 = 2689835) B2689835
theorem B1793243 : Blo 1792097 1793243 := bstep (se 1 (by rfl) ⟨1344932, by rfl⟩ : syracuseStep 1793243 = 2689865) B2689865
theorem B1793319 : Blo 1792097 1793319 := bstep (se 1 (by rfl) ⟨1344989, by rfl⟩ : syracuseStep 1793319 = 2689979) B2689979
theorem B1793359 : Blo 1792097 1793359 := bstep (se 1 (by rfl) ⟨1345019, by rfl⟩ : syracuseStep 1793359 = 2690039) B2690039
theorem B1793375 : Blo 1792097 1793375 := bstep (se 1 (by rfl) ⟨1345031, by rfl⟩ : syracuseStep 1793375 = 2690063) B2690063
theorem B1793403 : Blo 1792097 1793403 := bstep (se 1 (by rfl) ⟨1345052, by rfl⟩ : syracuseStep 1793403 = 2690105) B2690105
theorem B16367021 : Blo 1792097 16367021 := bstep (se 3 (by rfl) ⟨3068816, by rfl⟩ : syracuseStep 16367021 = 6137633) B6137633
theorem B1793455 : Blo 1792097 1793455 := bstep (se 1 (by rfl) ⟨1345091, by rfl⟩ : syracuseStep 1793455 = 2690183) B2690183
theorem B49053113 : Blo 1792097 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B1793479 : Blo 1792097 1793479 := bstep (se 1 (by rfl) ⟨1345109, by rfl⟩ : syracuseStep 1793479 = 2690219) B2690219
theorem B1818055 : Blo 1792097 1818055 := bstep (se 1 (by rfl) ⟨1363541, by rfl⟩ : syracuseStep 1818055 = 2727083) B2727083
theorem B1793499 : Blo 1792097 1793499 := bstep (se 1 (by rfl) ⟨1345124, by rfl⟩ : syracuseStep 1793499 = 2690249) B2690249
theorem B9076211 : Blo 1792097 9076211 := bstep (se 1 (by rfl) ⟨6807158, by rfl⟩ : syracuseStep 9076211 = 13614317) B13614317
theorem B7658995 : Blo 1792097 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B1793575 : Blo 1792097 1793575 := bstep (se 1 (by rfl) ⟨1345181, by rfl⟩ : syracuseStep 1793575 = 2690363) B2690363
theorem B1793615 : Blo 1792097 1793615 := bstep (se 1 (by rfl) ⟨1345211, by rfl⟩ : syracuseStep 1793615 = 2690423) B2690423
theorem B1793631 : Blo 1792097 1793631 := bstep (se 1 (by rfl) ⟨1345223, by rfl⟩ : syracuseStep 1793631 = 2690447) B2690447
theorem B1793659 : Blo 1792097 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B6135443 : Blo 1792097 6135443 := bstep (se 1 (by rfl) ⟨4601582, by rfl⟩ : syracuseStep 6135443 = 9203165) B9203165
theorem B1793711 : Blo 1792097 1793711 := bstep (se 1 (by rfl) ⟨1345283, by rfl⟩ : syracuseStep 1793711 = 2690567) B2690567
theorem B6053561 : Blo 1792097 6053561 := bstep (se 2 (by rfl) ⟨2270085, by rfl⟩ : syracuseStep 6053561 = 4540171) B4540171
theorem B1793735 : Blo 1792097 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B5103319 : Blo 1792097 5103319 := bstep (se 1 (by rfl) ⟨3827489, by rfl⟩ : syracuseStep 5103319 = 7654979) B7654979
theorem B1793755 : Blo 1792097 1793755 := bstep (se 1 (by rfl) ⟨1345316, by rfl⟩ : syracuseStep 1793755 = 2690633) B2690633
theorem B1793831 : Blo 1792097 1793831 := bstep (se 1 (by rfl) ⟨1345373, by rfl⟩ : syracuseStep 1793831 = 2690747) B2690747
theorem B1793871 : Blo 1792097 1793871 := bstep (se 1 (by rfl) ⟨1345403, by rfl⟩ : syracuseStep 1793871 = 2690807) B2690807
theorem B4538207 : Blo 1792097 4538207 := bstep (se 1 (by rfl) ⟨3403655, by rfl⟩ : syracuseStep 4538207 = 6807311) B6807311
theorem B1793887 : Blo 1792097 1793887 := bstep (se 1 (by rfl) ⟨1345415, by rfl⟩ : syracuseStep 1793887 = 2690831) B2690831
theorem B2727787 : Blo 1792097 2727787 := bstep (se 1 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 2727787 = 4091681) B4091681
theorem B1793915 : Blo 1792097 1793915 := bstep (se 1 (by rfl) ⟨1345436, by rfl⟩ : syracuseStep 1793915 = 2690873) B2690873
theorem B1793967 : Blo 1792097 1793967 := bstep (se 1 (by rfl) ⟨1345475, by rfl⟩ : syracuseStep 1793967 = 2690951) B2690951
theorem B1793991 : Blo 1792097 1793991 := bstep (se 1 (by rfl) ⟨1345493, by rfl⟩ : syracuseStep 1793991 = 2690987) B2690987
theorem B1794011 : Blo 1792097 1794011 := bstep (se 1 (by rfl) ⟨1345508, by rfl⟩ : syracuseStep 1794011 = 2691017) B2691017
theorem B27975689 : Blo 1792097 27975689 := bstep (se 2 (by rfl) ⟨10490883, by rfl⟩ : syracuseStep 27975689 = 20981767) B20981767
theorem B6053993 : Blo 1792097 6053993 := bstep (se 2 (by rfl) ⟨2270247, by rfl⟩ : syracuseStep 6053993 = 4540495) B4540495
theorem B3449339 : Blo 1792097 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B4538875 : Blo 1792097 4538875 := bstep (se 1 (by rfl) ⟨3404156, by rfl⟩ : syracuseStep 4538875 = 6808313) B6808313
theorem B9077345 : Blo 1792097 9077345 := bstep (se 2 (by rfl) ⟨3404004, by rfl⟩ : syracuseStep 9077345 = 6808009) B6808009
theorem B4538987 : Blo 1792097 4538987 := bstep (se 1 (by rfl) ⟨3404240, by rfl⟩ : syracuseStep 4538987 = 6808481) B6808481
theorem B7570091 : Blo 1792097 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B5743439 : Blo 1792097 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B8618831 : Blo 1792097 8618831 := bstep (se 1 (by rfl) ⟨6464123, by rfl⟩ : syracuseStep 8618831 = 12928247) B12928247
theorem B20702135 : Blo 1792097 20702135 := bstep (se 1 (by rfl) ⟨15526601, by rfl⟩ : syracuseStep 20702135 = 31053203) B31053203
theorem B6054857 : Blo 1792097 6054857 := bstep (se 2 (by rfl) ⟨2270571, by rfl⟩ : syracuseStep 6054857 = 4541143) B4541143
theorem B19645415 : Blo 1792097 19645415 := bstep (se 1 (by rfl) ⟨14734061, by rfl⟩ : syracuseStep 19645415 = 29468123) B29468123
theorem B21799925 : Blo 1792097 21799925 := bstep (se 5 (by rfl) ⟨1021871, by rfl⟩ : syracuseStep 21799925 = 2043743) B2043743
theorem B22987799 : Blo 1792097 22987799 := bstep (se 1 (by rfl) ⟨17240849, by rfl⟩ : syracuseStep 22987799 = 34481699) B34481699
theorem B58131553 : Blo 1792097 58131553 := bstep (se 2 (by rfl) ⟨21799332, by rfl⟩ : syracuseStep 58131553 = 43598665) B43598665
theorem B17712229 : Blo 1792097 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B2688233 : Blo 1792097 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B9077993 : Blo 1792097 9077993 := bstep (se 2 (by rfl) ⟨3404247, by rfl⟩ : syracuseStep 9077993 = 6808495) B6808495
theorem B4539635 : Blo 1792097 4539635 := bstep (se 1 (by rfl) ⟨3404726, by rfl⟩ : syracuseStep 4539635 = 6809453) B6809453
theorem B2688287 : Blo 1792097 2688287 := bstep (se 1 (by rfl) ⟨2016215, by rfl⟩ : syracuseStep 2688287 = 4032431) B4032431
theorem B19383587 : Blo 1792097 19383587 := bstep (se 1 (by rfl) ⟨14537690, by rfl⟩ : syracuseStep 19383587 = 29075381) B29075381
theorem B2270587 : Blo 1792097 2270587 := bstep (se 1 (by rfl) ⟨1702940, by rfl⟩ : syracuseStep 2270587 = 3405881) B3405881
theorem B9078155 : Blo 1792097 9078155 := bstep (se 1 (by rfl) ⟨6808616, by rfl⟩ : syracuseStep 9078155 = 13617233) B13617233
theorem B2016679 : Blo 1792097 2016679 := bstep (se 1 (by rfl) ⟨1512509, by rfl⟩ : syracuseStep 2016679 = 3025019) B3025019
theorem B4089275 : Blo 1792097 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B2688455 : Blo 1792097 2688455 := bstep (se 1 (by rfl) ⟨2016341, by rfl⟩ : syracuseStep 2688455 = 4032683) B4032683
theorem B4539847 : Blo 1792097 4539847 := bstep (se 1 (by rfl) ⟨3404885, by rfl⟩ : syracuseStep 4539847 = 6809771) B6809771
theorem B10208825 : Blo 1792097 10208825 := bstep (se 2 (by rfl) ⟨3828309, by rfl⟩ : syracuseStep 10208825 = 7656619) B7656619
theorem B3024479 : Blo 1792097 3024479 := bstep (se 1 (by rfl) ⟨2268359, by rfl⟩ : syracuseStep 3024479 = 4536719) B4536719
theorem B10217117 : Blo 1792097 10217117 := bstep (se 3 (by rfl) ⟨1915709, by rfl⟩ : syracuseStep 10217117 = 3831419) B3831419
theorem B2688809 : Blo 1792097 2688809 := bstep (se 2 (by rfl) ⟨1008303, by rfl⟩ : syracuseStep 2688809 = 2016607) B2016607
theorem B2688815 : Blo 1792097 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B3024695 : Blo 1792097 3024695 := bstep (se 1 (by rfl) ⟨2268521, by rfl⟩ : syracuseStep 3024695 = 4537043) B4537043
theorem B2017255 : Blo 1792097 2017255 := bstep (se 1 (by rfl) ⟨1512941, by rfl⟩ : syracuseStep 2017255 = 3025883) B3025883
theorem B31057901 : Blo 1792097 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B4032521 : Blo 1792097 4032521 := bstep (se 2 (by rfl) ⟨1512195, by rfl⟩ : syracuseStep 4032521 = 3024391) B3024391
theorem B25856081 : Blo 1792097 25856081 := bstep (se 2 (by rfl) ⟨9696030, by rfl⟩ : syracuseStep 25856081 = 19392061) B19392061
theorem B41404621 : Blo 1792097 41404621 := bstep (se 3 (by rfl) ⟨7763366, by rfl⟩ : syracuseStep 41404621 = 15526733) B15526733
theorem B2689289 : Blo 1792097 2689289 := bstep (se 2 (by rfl) ⟨1008483, by rfl⟩ : syracuseStep 2689289 = 2016967) B2016967
theorem B2689391 : Blo 1792097 2689391 := bstep (se 1 (by rfl) ⟨2017043, by rfl⟩ : syracuseStep 2689391 = 4034087) B4034087
theorem B4032935 : Blo 1792097 4032935 := bstep (se 1 (by rfl) ⟨3024701, by rfl⟩ : syracuseStep 4032935 = 6049403) B6049403
theorem B4090295 : Blo 1792097 4090295 := bstep (se 1 (by rfl) ⟨3067721, by rfl⟩ : syracuseStep 4090295 = 6135443) B6135443
theorem B4033043 : Blo 1792097 4033043 := bstep (se 1 (by rfl) ⟨3024782, by rfl⟩ : syracuseStep 4033043 = 6049565) B6049565
theorem B3025471 : Blo 1792097 3025471 := bstep (se 1 (by rfl) ⟨2269103, by rfl⟩ : syracuseStep 3025471 = 4538207) B4538207
theorem B2689607 : Blo 1792097 2689607 := bstep (se 1 (by rfl) ⟨2017205, by rfl⟩ : syracuseStep 2689607 = 4034411) B4034411
theorem B4033097 : Blo 1792097 4033097 := bstep (se 2 (by rfl) ⟨1512411, by rfl⟩ : syracuseStep 4033097 = 3024823) B3024823
theorem B2689643 : Blo 1792097 2689643 := bstep (se 1 (by rfl) ⟨2017232, by rfl⟩ : syracuseStep 2689643 = 4034465) B4034465
theorem B6048431 : Blo 1792097 6048431 := bstep (se 1 (by rfl) ⟨4536323, by rfl⟩ : syracuseStep 6048431 = 9072647) B9072647
theorem B8612527 : Blo 1792097 8612527 := bstep (se 1 (by rfl) ⟨6459395, by rfl⟩ : syracuseStep 8612527 = 12918791) B12918791
theorem B46574291 : Blo 1792097 46574291 := bstep (se 1 (by rfl) ⟨34930718, by rfl⟩ : syracuseStep 46574291 = 69861437) B69861437
theorem B2689871 : Blo 1792097 2689871 := bstep (se 1 (by rfl) ⟨2017403, by rfl⟩ : syracuseStep 2689871 = 4034807) B4034807
theorem B4033511 : Blo 1792097 4033511 := bstep (se 1 (by rfl) ⟨3025133, by rfl⟩ : syracuseStep 4033511 = 6050267) B6050267
theorem B6048755 : Blo 1792097 6048755 := bstep (se 1 (by rfl) ⟨4536566, by rfl⟩ : syracuseStep 6048755 = 9073133) B9073133
theorem B8612851 : Blo 1792097 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B4090871 : Blo 1792097 4090871 := bstep (se 1 (by rfl) ⟨3068153, by rfl⟩ : syracuseStep 4090871 = 6136307) B6136307
theorem B5106827 : Blo 1792097 5106827 := bstep (se 1 (by rfl) ⟨3830120, by rfl⟩ : syracuseStep 5106827 = 7660241) B7660241
theorem B2690267 : Blo 1792097 2690267 := bstep (se 1 (by rfl) ⟨2017700, by rfl⟩ : syracuseStep 2690267 = 4035401) B4035401
theorem B3026153 : Blo 1792097 3026153 := bstep (se 2 (by rfl) ⟨1134807, by rfl⟩ : syracuseStep 3026153 = 2269615) B2269615
theorem B3026207 : Blo 1792097 3026207 := bstep (se 1 (by rfl) ⟨2269655, by rfl⟩ : syracuseStep 3026207 = 4539311) B4539311
theorem B6810911 : Blo 1792097 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B4033889 : Blo 1792097 4033889 := bstep (se 2 (by rfl) ⟨1512708, by rfl⟩ : syracuseStep 4033889 = 3025417) B3025417
theorem B9694561 : Blo 1792097 9694561 := bstep (se 2 (by rfl) ⟨3635460, by rfl⟩ : syracuseStep 9694561 = 7270921) B7270921
theorem B51719543 : Blo 1792097 51719543 := bstep (se 1 (by rfl) ⟨38789657, by rfl⟩ : syracuseStep 51719543 = 77579315) B77579315
theorem B4664699 : Blo 1792097 4664699 := bstep (se 1 (by rfl) ⟨3498524, by rfl⟩ : syracuseStep 4664699 = 6997049) B6997049
theorem B2690441 : Blo 1792097 2690441 := bstep (se 2 (by rfl) ⟨1008915, by rfl⟩ : syracuseStep 2690441 = 2017831) B2017831
theorem B4033979 : Blo 1792097 4033979 := bstep (se 1 (by rfl) ⟨3025484, by rfl⟩ : syracuseStep 4033979 = 6050969) B6050969
theorem B6049295 : Blo 1792097 6049295 := bstep (se 1 (by rfl) ⟨4536971, by rfl⟩ : syracuseStep 6049295 = 9073943) B9073943
theorem B4034105 : Blo 1792097 4034105 := bstep (se 2 (by rfl) ⟨1512789, by rfl⟩ : syracuseStep 4034105 = 3025579) B3025579
theorem B5107283 : Blo 1792097 5107283 := bstep (se 1 (by rfl) ⟨3830462, by rfl⟩ : syracuseStep 5107283 = 7660925) B7660925
theorem B232771157 : Blo 1792097 232771157 := bstep (se 8 (by rfl) ⟨1363893, by rfl⟩ : syracuseStep 232771157 = 2727787) B2727787
theorem B3403451 : Blo 1792097 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B11488979 : Blo 1792097 11488979 := bstep (se 1 (by rfl) ⟨8616734, by rfl⟩ : syracuseStep 11488979 = 17233469) B17233469
theorem B5746411 : Blo 1792097 5746411 := bstep (se 1 (by rfl) ⟨4309808, by rfl⟩ : syracuseStep 5746411 = 8619617) B8619617
theorem B2690795 : Blo 1792097 2690795 := bstep (se 1 (by rfl) ⟨2018096, by rfl⟩ : syracuseStep 2690795 = 4036193) B4036193
theorem B2691023 : Blo 1792097 2691023 := bstep (se 1 (by rfl) ⟨2018267, by rfl⟩ : syracuseStep 2691023 = 4036535) B4036535
theorem B4034771 : Blo 1792097 4034771 := bstep (se 1 (by rfl) ⟨3026078, by rfl⟩ : syracuseStep 4034771 = 6052157) B6052157
theorem B4034825 : Blo 1792097 4034825 := bstep (se 2 (by rfl) ⟨1513059, by rfl⟩ : syracuseStep 4034825 = 3026119) B3026119
theorem B2044327 : Blo 1792097 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B18403787 : Blo 1792097 18403787 := bstep (se 1 (by rfl) ⟨13802840, by rfl⟩ : syracuseStep 18403787 = 27605681) B27605681
theorem B4035041 : Blo 1792097 4035041 := bstep (se 2 (by rfl) ⟨1513140, by rfl⟩ : syracuseStep 4035041 = 3026281) B3026281
theorem B24547859 : Blo 1792097 24547859 := bstep (se 1 (by rfl) ⟨18410894, by rfl⟩ : syracuseStep 24547859 = 36821789) B36821789
theorem B9081395 : Blo 1792097 9081395 := bstep (se 1 (by rfl) ⟨6811046, by rfl⟩ : syracuseStep 9081395 = 13622093) B13622093
theorem B6050375 : Blo 1792097 6050375 := bstep (se 1 (by rfl) ⟨4537781, by rfl⟩ : syracuseStep 6050375 = 9075563) B9075563
theorem B10211993 : Blo 1792097 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B8614583 : Blo 1792097 8614583 := bstep (se 1 (by rfl) ⟨6460937, by rfl⟩ : syracuseStep 8614583 = 12921875) B12921875
theorem B4035347 : Blo 1792097 4035347 := bstep (se 1 (by rfl) ⟨3026510, by rfl⟩ : syracuseStep 4035347 = 6053021) B6053021
theorem B31069001 : Blo 1792097 31069001 := bstep (se 2 (by rfl) ⟨11650875, by rfl⟩ : syracuseStep 31069001 = 23301751) B23301751
theorem B6804425 : Blo 1792097 6804425 := bstep (se 2 (by rfl) ⟨2551659, by rfl⟩ : syracuseStep 6804425 = 5103319) B5103319
theorem B4305907 : Blo 1792097 4305907 := bstep (se 1 (by rfl) ⟨3229430, by rfl⟩ : syracuseStep 4305907 = 6458861) B6458861
theorem B6050807 : Blo 1792097 6050807 := bstep (se 1 (by rfl) ⟨4538105, by rfl⟩ : syracuseStep 6050807 = 9076211) B9076211
theorem B9696293 : Blo 1792097 9696293 := bstep (se 4 (by rfl) ⟨909027, by rfl⟩ : syracuseStep 9696293 = 1818055) B1818055
theorem B4035707 : Blo 1792097 4035707 := bstep (se 1 (by rfl) ⟨3026780, by rfl⟩ : syracuseStep 4035707 = 6053561) B6053561
theorem B5108969 : Blo 1792097 5108969 := bstep (se 2 (by rfl) ⟨1915863, by rfl⟩ : syracuseStep 5108969 = 3831727) B3831727
theorem B4035833 : Blo 1792097 4035833 := bstep (se 2 (by rfl) ⟨1513437, by rfl⟩ : syracuseStep 4035833 = 3026875) B3026875
theorem B17700221 : Blo 1792097 17700221 := bstep (se 3 (by rfl) ⟨3318791, by rfl⟩ : syracuseStep 17700221 = 6637583) B6637583
theorem B4035977 : Blo 1792097 4035977 := bstep (se 2 (by rfl) ⟨1513491, by rfl⟩ : syracuseStep 4035977 = 3026983) B3026983
theorem B7656893 : Blo 1792097 7656893 := bstep (se 3 (by rfl) ⟨1435667, by rfl⟩ : syracuseStep 7656893 = 2871335) B2871335
theorem B4912583 : Blo 1792097 4912583 := bstep (se 1 (by rfl) ⟨3684437, by rfl⟩ : syracuseStep 4912583 = 7368875) B7368875
theorem B4036103 : Blo 1792097 4036103 := bstep (se 1 (by rfl) ⟨3027077, by rfl⟩ : syracuseStep 4036103 = 6054155) B6054155
theorem B3405395 : Blo 1792097 3405395 := bstep (se 1 (by rfl) ⟨2554046, by rfl⟩ : syracuseStep 3405395 = 5108093) B5108093
theorem B4036283 : Blo 1792097 4036283 := bstep (se 1 (by rfl) ⟨3027212, by rfl⟩ : syracuseStep 4036283 = 6054425) B6054425
theorem B4036409 : Blo 1792097 4036409 := bstep (se 2 (by rfl) ⟨1513653, by rfl⟩ : syracuseStep 4036409 = 3027307) B3027307
theorem B6051671 : Blo 1792097 6051671 := bstep (se 1 (by rfl) ⟨4538753, by rfl⟩ : syracuseStep 6051671 = 9077507) B9077507
theorem B4536425 : Blo 1792097 4536425 := bstep (se 2 (by rfl) ⟨1701159, by rfl⟩ : syracuseStep 4536425 = 3402319) B3402319
theorem B9205955 : Blo 1792097 9205955 := bstep (se 1 (by rfl) ⟨6904466, by rfl⟩ : syracuseStep 9205955 = 13808933) B13808933
theorem B1792287 : Blo 1792097 1792287 := bstep (se 1 (by rfl) ⟨1344215, by rfl⟩ : syracuseStep 1792287 = 2688431) B2688431
theorem B12925273 : Blo 1792097 12925273 := bstep (se 2 (by rfl) ⟨4846977, by rfl⟩ : syracuseStep 12925273 = 9693955) B9693955
theorem B1792347 : Blo 1792097 1792347 := bstep (se 1 (by rfl) ⟨1344260, by rfl⟩ : syracuseStep 1792347 = 2688521) B2688521
theorem B1792367 : Blo 1792097 1792367 := bstep (se 1 (by rfl) ⟨1344275, by rfl⟩ : syracuseStep 1792367 = 2688551) B2688551
theorem B6388079 : Blo 1792097 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B1792423 : Blo 1792097 1792423 := bstep (se 1 (by rfl) ⟨1344317, by rfl⟩ : syracuseStep 1792423 = 2688635) B2688635
theorem B1792507 : Blo 1792097 1792507 := bstep (se 1 (by rfl) ⟨1344380, by rfl⟩ : syracuseStep 1792507 = 2688761) B2688761
theorem B10213883 : Blo 1792097 10213883 := bstep (se 1 (by rfl) ⟨7660412, by rfl⟩ : syracuseStep 10213883 = 15320825) B15320825
theorem B39311867 : Blo 1792097 39311867 := bstep (se 1 (by rfl) ⟨29483900, by rfl⟩ : syracuseStep 39311867 = 58967801) B58967801
theorem B9075239 : Blo 1792097 9075239 := bstep (se 1 (by rfl) ⟨6806429, by rfl⟩ : syracuseStep 9075239 = 13612859) B13612859
theorem B1792575 : Blo 1792097 1792575 := bstep (se 1 (by rfl) ⟨1344431, by rfl⟩ : syracuseStep 1792575 = 2688863) B2688863
theorem B1792583 : Blo 1792097 1792583 := bstep (se 1 (by rfl) ⟨1344437, by rfl⟩ : syracuseStep 1792583 = 2688875) B2688875
theorem B4536911 : Blo 1792097 4536911 := bstep (se 1 (by rfl) ⟨3402683, by rfl⟩ : syracuseStep 4536911 = 6805367) B6805367
theorem B4848299 : Blo 1792097 4848299 := bstep (se 1 (by rfl) ⟨3636224, by rfl⟩ : syracuseStep 4848299 = 7272449) B7272449
theorem B1792735 : Blo 1792097 1792735 := bstep (se 1 (by rfl) ⟨1344551, by rfl⟩ : syracuseStep 1792735 = 2689103) B2689103
theorem B18397955 : Blo 1792097 18397955 := bstep (se 1 (by rfl) ⟨13798466, by rfl⟩ : syracuseStep 18397955 = 27596933) B27596933
theorem B1792815 : Blo 1792097 1792815 := bstep (se 1 (by rfl) ⟨1344611, by rfl⟩ : syracuseStep 1792815 = 2689223) B2689223
theorem B6052751 : Blo 1792097 6052751 := bstep (se 1 (by rfl) ⟨4539563, by rfl⟩ : syracuseStep 6052751 = 9079127) B9079127
theorem B1792923 : Blo 1792097 1792923 := bstep (se 1 (by rfl) ⟨1344692, by rfl⟩ : syracuseStep 1792923 = 2689385) B2689385
theorem B1792975 : Blo 1792097 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B1792999 : Blo 1792097 1792999 := bstep (se 1 (by rfl) ⟨1344749, by rfl⟩ : syracuseStep 1792999 = 2689499) B2689499
theorem B7371899 : Blo 1792097 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B4537559 : Blo 1792097 4537559 := bstep (se 1 (by rfl) ⟨3403169, by rfl⟩ : syracuseStep 4537559 = 6806339) B6806339
theorem B1793311 : Blo 1792097 1793311 := bstep (se 1 (by rfl) ⟨1344983, by rfl⟩ : syracuseStep 1793311 = 2689967) B2689967
theorem B238927171 : Blo 1792097 238927171 := bstep (se 1 (by rfl) ⟨179195378, by rfl⟩ : syracuseStep 238927171 = 358390757) B358390757
theorem B1793371 : Blo 1792097 1793371 := bstep (se 1 (by rfl) ⟨1345028, by rfl⟩ : syracuseStep 1793371 = 2690057) B2690057
theorem B1793391 : Blo 1792097 1793391 := bstep (se 1 (by rfl) ⟨1345043, by rfl⟩ : syracuseStep 1793391 = 2690087) B2690087
theorem B16366985 : Blo 1792097 16366985 := bstep (se 2 (by rfl) ⟨6137619, by rfl⟩ : syracuseStep 16366985 = 12275239) B12275239
theorem B1793447 : Blo 1792097 1793447 := bstep (se 1 (by rfl) ⟨1345085, by rfl⟩ : syracuseStep 1793447 = 2690171) B2690171
theorem B1793531 : Blo 1792097 1793531 := bstep (se 1 (by rfl) ⟨1345148, by rfl⟩ : syracuseStep 1793531 = 2690297) B2690297
theorem B38788631 : Blo 1792097 38788631 := bstep (se 1 (by rfl) ⟨29091473, by rfl⟩ : syracuseStep 38788631 = 58182947) B58182947
theorem B1793599 : Blo 1792097 1793599 := bstep (se 1 (by rfl) ⟨1345199, by rfl⟩ : syracuseStep 1793599 = 2690399) B2690399
theorem B2154055 : Blo 1792097 2154055 := bstep (se 1 (by rfl) ⟨1615541, by rfl⟩ : syracuseStep 2154055 = 3231083) B3231083
theorem B1793607 : Blo 1792097 1793607 := bstep (se 1 (by rfl) ⟨1345205, by rfl⟩ : syracuseStep 1793607 = 2690411) B2690411
theorem B10911347 : Blo 1792097 10911347 := bstep (se 1 (by rfl) ⟨8183510, by rfl⟩ : syracuseStep 10911347 = 16367021) B16367021
theorem B32702075 : Blo 1792097 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B1793759 : Blo 1792097 1793759 := bstep (se 1 (by rfl) ⟨1345319, by rfl⟩ : syracuseStep 1793759 = 2690639) B2690639
theorem B4087559 : Blo 1792097 4087559 := bstep (se 1 (by rfl) ⟨3065669, by rfl⟩ : syracuseStep 4087559 = 6131339) B6131339
theorem B6463273 : Blo 1792097 6463273 := bstep (se 2 (by rfl) ⟨2423727, by rfl⟩ : syracuseStep 6463273 = 4847455) B4847455
theorem B1793839 : Blo 1792097 1793839 := bstep (se 1 (by rfl) ⟨1345379, by rfl⟩ : syracuseStep 1793839 = 2690759) B2690759
theorem B55197557 : Blo 1792097 55197557 := bstep (se 5 (by rfl) ⟨2587385, by rfl⟩ : syracuseStep 55197557 = 5174771) B5174771
theorem B1793947 : Blo 1792097 1793947 := bstep (se 1 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 1793947 = 2690921) B2690921
theorem B1793999 : Blo 1792097 1793999 := bstep (se 1 (by rfl) ⟨1345499, by rfl⟩ : syracuseStep 1793999 = 2690999) B2690999
theorem B1794023 : Blo 1792097 1794023 := bstep (se 1 (by rfl) ⟨1345517, by rfl⟩ : syracuseStep 1794023 = 2691035) B2691035
theorem B55206161 : Blo 1792097 55206161 := bstep (se 2 (by rfl) ⟨20702310, by rfl⟩ : syracuseStep 55206161 = 41404621) B41404621
theorem B6054263 : Blo 1792097 6054263 := bstep (se 1 (by rfl) ⟨4540697, by rfl⟩ : syracuseStep 6054263 = 9081395) B9081395
theorem B6807995 : Blo 1792097 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B5743055 : Blo 1792097 5743055 := bstep (se 1 (by rfl) ⟨4307291, by rfl⟩ : syracuseStep 5743055 = 8614583) B8614583
theorem B14533283 : Blo 1792097 14533283 := bstep (se 1 (by rfl) ⟨10899962, by rfl⟩ : syracuseStep 14533283 = 21799925) B21799925
theorem B6464195 : Blo 1792097 6464195 := bstep (se 1 (by rfl) ⟨4848146, by rfl⟩ : syracuseStep 6464195 = 9696293) B9696293
theorem B5104595 : Blo 1792097 5104595 := bstep (se 1 (by rfl) ⟨3828446, by rfl⟩ : syracuseStep 5104595 = 7656893) B7656893
theorem B2270263 : Blo 1792097 2270263 := bstep (se 1 (by rfl) ⟨1702697, by rfl⟩ : syracuseStep 2270263 = 3405395) B3405395
theorem B2016319 : Blo 1792097 2016319 := bstep (se 1 (by rfl) ⟨1512239, by rfl⟩ : syracuseStep 2016319 = 3024479) B3024479
theorem B13100221 : Blo 1792097 13100221 := bstep (se 3 (by rfl) ⟨2456291, by rfl⟩ : syracuseStep 13100221 = 4912583) B4912583
theorem B2016463 : Blo 1792097 2016463 := bstep (se 1 (by rfl) ⟨1512347, by rfl⟩ : syracuseStep 2016463 = 3024695) B3024695
theorem B2688347 : Blo 1792097 2688347 := bstep (se 1 (by rfl) ⟨2016260, by rfl⟩ : syracuseStep 2688347 = 4032521) B4032521
theorem B17237387 : Blo 1792097 17237387 := bstep (se 1 (by rfl) ⟨12928040, by rfl⟩ : syracuseStep 17237387 = 25856081) B25856081
theorem B3024283 : Blo 1792097 3024283 := bstep (se 1 (by rfl) ⟨2268212, by rfl⟩ : syracuseStep 3024283 = 4536425) B4536425
theorem B6137303 : Blo 1792097 6137303 := bstep (se 1 (by rfl) ⟨4602977, by rfl⟩ : syracuseStep 6137303 = 9205955) B9205955
theorem B2688623 : Blo 1792097 2688623 := bstep (se 1 (by rfl) ⟨2016467, by rfl⟩ : syracuseStep 2688623 = 4032935) B4032935
theorem B6809255 : Blo 1792097 6809255 := bstep (se 1 (by rfl) ⟨5106941, by rfl⟩ : syracuseStep 6809255 = 10213883) B10213883
theorem B26207911 : Blo 1792097 26207911 := bstep (se 1 (by rfl) ⟨19655933, by rfl⟩ : syracuseStep 26207911 = 39311867) B39311867
theorem B2688695 : Blo 1792097 2688695 := bstep (se 1 (by rfl) ⟨2016521, by rfl⟩ : syracuseStep 2688695 = 4033043) B4033043
theorem B2688731 : Blo 1792097 2688731 := bstep (se 1 (by rfl) ⟨2016548, by rfl⟩ : syracuseStep 2688731 = 4033097) B4033097
theorem B3024607 : Blo 1792097 3024607 := bstep (se 1 (by rfl) ⟨2268455, by rfl⟩ : syracuseStep 3024607 = 4536911) B4536911
theorem B20186909 : Blo 1792097 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B4032287 : Blo 1792097 4032287 := bstep (se 1 (by rfl) ⟨3024215, by rfl⟩ : syracuseStep 4032287 = 6048431) B6048431
theorem B31049527 : Blo 1792097 31049527 := bstep (se 1 (by rfl) ⟨23287145, by rfl⟩ : syracuseStep 31049527 = 46574291) B46574291
theorem B2688905 : Blo 1792097 2688905 := bstep (se 2 (by rfl) ⟨1008339, by rfl⟩ : syracuseStep 2688905 = 2016679) B2016679
theorem B2689007 : Blo 1792097 2689007 := bstep (se 1 (by rfl) ⟨2016755, by rfl⟩ : syracuseStep 2689007 = 4033511) B4033511
theorem B4032503 : Blo 1792097 4032503 := bstep (se 1 (by rfl) ⟨3024377, by rfl⟩ : syracuseStep 4032503 = 6048755) B6048755
theorem B3025039 : Blo 1792097 3025039 := bstep (se 1 (by rfl) ⟨2268779, by rfl⟩ : syracuseStep 3025039 = 4537559) B4537559
theorem B2017435 : Blo 1792097 2017435 := bstep (se 1 (by rfl) ⟨1513076, by rfl⟩ : syracuseStep 2017435 = 3026153) B3026153
theorem B2017471 : Blo 1792097 2017471 := bstep (se 1 (by rfl) ⟨1513103, by rfl⟩ : syracuseStep 2017471 = 3026207) B3026207
theorem B4540607 : Blo 1792097 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B2689259 : Blo 1792097 2689259 := bstep (se 1 (by rfl) ⟨2016944, by rfl⟩ : syracuseStep 2689259 = 4033889) B4033889
theorem B2689319 : Blo 1792097 2689319 := bstep (se 1 (by rfl) ⟨2016989, by rfl⟩ : syracuseStep 2689319 = 4033979) B4033979
theorem B7661881 : Blo 1792097 7661881 := bstep (se 2 (by rfl) ⟨2873205, by rfl⟩ : syracuseStep 7661881 = 5746411) B5746411
theorem B4032863 : Blo 1792097 4032863 := bstep (se 1 (by rfl) ⟨3024647, by rfl⟩ : syracuseStep 4032863 = 6049295) B6049295
theorem B2689403 : Blo 1792097 2689403 := bstep (se 1 (by rfl) ⟨2017052, by rfl⟩ : syracuseStep 2689403 = 4034105) B4034105
theorem B21801383 : Blo 1792097 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B36792949 : Blo 1792097 36792949 := bstep (se 5 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 36792949 = 3449339) B3449339
theorem B2689673 : Blo 1792097 2689673 := bstep (se 2 (by rfl) ⟨1008627, by rfl⟩ : syracuseStep 2689673 = 2017255) B2017255
theorem B2689847 : Blo 1792097 2689847 := bstep (se 1 (by rfl) ⟨2017385, by rfl⟩ : syracuseStep 2689847 = 4034771) B4034771
theorem B2689883 : Blo 1792097 2689883 := bstep (se 1 (by rfl) ⟨2017412, by rfl⟩ : syracuseStep 2689883 = 4034825) B4034825
theorem B2690027 : Blo 1792097 2690027 := bstep (se 1 (by rfl) ⟨2017520, by rfl⟩ : syracuseStep 2690027 = 4035041) B4035041
theorem B13618205 : Blo 1792097 13618205 := bstep (se 3 (by rfl) ⟨2553413, by rfl⟩ : syracuseStep 13618205 = 5106827) B5106827
theorem B4033583 : Blo 1792097 4033583 := bstep (se 1 (by rfl) ⟨3025187, by rfl⟩ : syracuseStep 4033583 = 6050375) B6050375
theorem B3025991 : Blo 1792097 3025991 := bstep (se 1 (by rfl) ⟨2269493, by rfl⟩ : syracuseStep 3025991 = 4538987) B4538987
theorem B2690231 : Blo 1792097 2690231 := bstep (se 1 (by rfl) ⟨2017673, by rfl⟩ : syracuseStep 2690231 = 4035347) B4035347
theorem B20712667 : Blo 1792097 20712667 := bstep (se 1 (by rfl) ⟨15534500, by rfl⟩ : syracuseStep 20712667 = 31069001) B31069001
theorem B3828959 : Blo 1792097 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B5745887 : Blo 1792097 5745887 := bstep (se 1 (by rfl) ⟨4309415, by rfl⟩ : syracuseStep 5745887 = 8618831) B8618831
theorem B4033871 : Blo 1792097 4033871 := bstep (se 1 (by rfl) ⟨3025403, by rfl⟩ : syracuseStep 4033871 = 6050807) B6050807
theorem B2690471 : Blo 1792097 2690471 := bstep (se 1 (by rfl) ⟨2017853, by rfl⟩ : syracuseStep 2690471 = 4035707) B4035707
theorem B4033961 : Blo 1792097 4033961 := bstep (se 2 (by rfl) ⟨1512735, by rfl⟩ : syracuseStep 4033961 = 3025471) B3025471
theorem B3026423 : Blo 1792097 3026423 := bstep (se 1 (by rfl) ⟨2269817, by rfl⟩ : syracuseStep 3026423 = 4539635) B4539635
theorem B2690555 : Blo 1792097 2690555 := bstep (se 1 (by rfl) ⟨2017916, by rfl⟩ : syracuseStep 2690555 = 4035833) B4035833
theorem B12922391 : Blo 1792097 12922391 := bstep (se 1 (by rfl) ⟨9691793, by rfl⟩ : syracuseStep 12922391 = 19383587) B19383587
theorem B11800147 : Blo 1792097 11800147 := bstep (se 1 (by rfl) ⟨8850110, by rfl⟩ : syracuseStep 11800147 = 17700221) B17700221
theorem B2690651 : Blo 1792097 2690651 := bstep (se 1 (by rfl) ⟨2017988, by rfl⟩ : syracuseStep 2690651 = 4035977) B4035977
theorem B17034877 : Blo 1792097 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B2690735 : Blo 1792097 2690735 := bstep (se 1 (by rfl) ⟨2018051, by rfl⟩ : syracuseStep 2690735 = 4036103) B4036103
theorem B6811411 : Blo 1792097 6811411 := bstep (se 1 (by rfl) ⟨5108558, by rfl⟩ : syracuseStep 6811411 = 10217117) B10217117
theorem B2690855 : Blo 1792097 2690855 := bstep (se 1 (by rfl) ⟨2018141, by rfl⟩ : syracuseStep 2690855 = 4036283) B4036283
theorem B10907453 : Blo 1792097 10907453 := bstep (se 3 (by rfl) ⟨2045147, by rfl⟩ : syracuseStep 10907453 = 4090295) B4090295
theorem B2690939 : Blo 1792097 2690939 := bstep (se 1 (by rfl) ⟨2018204, by rfl⟩ : syracuseStep 2690939 = 4036409) B4036409
theorem B4034447 : Blo 1792097 4034447 := bstep (se 1 (by rfl) ⟨3025835, by rfl⟩ : syracuseStep 4034447 = 6051671) B6051671
theorem B20705267 : Blo 1792097 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B77508737 : Blo 1792097 77508737 := bstep (se 2 (by rfl) ⟨29065776, by rfl⟩ : syracuseStep 77508737 = 58131553) B58131553
theorem B6050159 : Blo 1792097 6050159 := bstep (se 1 (by rfl) ⟨4537619, by rfl⟩ : syracuseStep 6050159 = 9075239) B9075239
theorem B3232199 : Blo 1792097 3232199 := bstep (se 1 (by rfl) ⟨2424149, by rfl⟩ : syracuseStep 3232199 = 4848299) B4848299
theorem B3027449 : Blo 1792097 3027449 := bstep (se 2 (by rfl) ⟨1135293, by rfl⟩ : syracuseStep 3027449 = 2270587) B2270587
theorem B4035167 : Blo 1792097 4035167 := bstep (se 1 (by rfl) ⟨3026375, by rfl⟩ : syracuseStep 4035167 = 6052751) B6052751
theorem B2872073 : Blo 1792097 2872073 := bstep (se 2 (by rfl) ⟨1077027, by rfl⟩ : syracuseStep 2872073 = 2154055) B2154055
theorem B3109799 : Blo 1792097 3109799 := bstep (se 1 (by rfl) ⟨2332349, by rfl⟩ : syracuseStep 3109799 = 4664699) B4664699
theorem B25859087 : Blo 1792097 25859087 := bstep (se 1 (by rfl) ⟨19394315, by rfl⟩ : syracuseStep 25859087 = 38788631) B38788631
theorem B3404855 : Blo 1792097 3404855 := bstep (se 1 (by rfl) ⟨2553641, by rfl⟩ : syracuseStep 3404855 = 5107283) B5107283
theorem B2725039 : Blo 1792097 2725039 := bstep (se 1 (by rfl) ⟨2043779, by rfl⟩ : syracuseStep 2725039 = 4087559) B4087559
theorem B10908989 : Blo 1792097 10908989 := bstep (se 3 (by rfl) ⟨2045435, by rfl⟩ : syracuseStep 10908989 = 4090871) B4090871
theorem B18650459 : Blo 1792097 18650459 := bstep (se 1 (by rfl) ⟨13987844, by rfl⟩ : syracuseStep 18650459 = 27975689) B27975689
theorem B4035995 : Blo 1792097 4035995 := bstep (se 1 (by rfl) ⟨3026996, by rfl⟩ : syracuseStep 4035995 = 6053993) B6053993
theorem B12269191 : Blo 1792097 12269191 := bstep (se 1 (by rfl) ⟨9201893, by rfl⟩ : syracuseStep 12269191 = 18403787) B18403787
theorem B16365239 : Blo 1792097 16365239 := bstep (se 1 (by rfl) ⟨12273929, by rfl⟩ : syracuseStep 16365239 = 24547859) B24547859
theorem B6051563 : Blo 1792097 6051563 := bstep (se 1 (by rfl) ⟨4538672, by rfl⟩ : syracuseStep 6051563 = 9077345) B9077345
theorem B17233697 : Blo 1792097 17233697 := bstep (se 2 (by rfl) ⟨6462636, by rfl⟩ : syracuseStep 17233697 = 12925273) B12925273
theorem B2725769 : Blo 1792097 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B13801423 : Blo 1792097 13801423 := bstep (se 1 (by rfl) ⟨10351067, by rfl⟩ : syracuseStep 13801423 = 20702135) B20702135
theorem B4536283 : Blo 1792097 4536283 := bstep (se 1 (by rfl) ⟨3402212, by rfl⟩ : syracuseStep 4536283 = 6804425) B6804425
theorem B4036571 : Blo 1792097 4036571 := bstep (se 1 (by rfl) ⟨3027428, by rfl⟩ : syracuseStep 4036571 = 6054857) B6054857
theorem B13096943 : Blo 1792097 13096943 := bstep (se 1 (by rfl) ⟨9822707, by rfl⟩ : syracuseStep 13096943 = 19645415) B19645415
theorem B6051833 : Blo 1792097 6051833 := bstep (se 2 (by rfl) ⟨2269437, by rfl⟩ : syracuseStep 6051833 = 4538875) B4538875
theorem B15325199 : Blo 1792097 15325199 := bstep (se 1 (by rfl) ⟨11493899, by rfl⟩ : syracuseStep 15325199 = 22987799) B22987799
theorem B1792155 : Blo 1792097 1792155 := bstep (se 1 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 1792155 = 2688233) B2688233
theorem B6051995 : Blo 1792097 6051995 := bstep (se 1 (by rfl) ⟨4538996, by rfl⟩ : syracuseStep 6051995 = 9077993) B9077993
theorem B3405979 : Blo 1792097 3405979 := bstep (se 1 (by rfl) ⟨2554484, by rfl⟩ : syracuseStep 3405979 = 5108969) B5108969
theorem B1792191 : Blo 1792097 1792191 := bstep (se 1 (by rfl) ⟨1344143, by rfl⟩ : syracuseStep 1792191 = 2688287) B2688287
theorem B11483369 : Blo 1792097 11483369 := bstep (se 2 (by rfl) ⟨4306263, by rfl⟩ : syracuseStep 11483369 = 8612527) B8612527
theorem B6052103 : Blo 1792097 6052103 := bstep (se 1 (by rfl) ⟨4539077, by rfl⟩ : syracuseStep 6052103 = 9078155) B9078155
theorem B2726183 : Blo 1792097 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B1792303 : Blo 1792097 1792303 := bstep (se 1 (by rfl) ⟨1344227, by rfl⟩ : syracuseStep 1792303 = 2688455) B2688455
theorem B6805883 : Blo 1792097 6805883 := bstep (se 1 (by rfl) ⟨5104412, by rfl⟩ : syracuseStep 6805883 = 10208825) B10208825
theorem B1792539 : Blo 1792097 1792539 := bstep (se 1 (by rfl) ⟨1344404, by rfl⟩ : syracuseStep 1792539 = 2688809) B2688809
theorem B1792543 : Blo 1792097 1792543 := bstep (se 1 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 1792543 = 2688815) B2688815
theorem B5741209 : Blo 1792097 5741209 := bstep (se 2 (by rfl) ⟨2152953, by rfl⟩ : syracuseStep 5741209 = 4305907) B4305907
theorem B11483801 : Blo 1792097 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B23616305 : Blo 1792097 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B1792859 : Blo 1792097 1792859 := bstep (se 1 (by rfl) ⟨1344644, by rfl⟩ : syracuseStep 1792859 = 2689289) B2689289
theorem B1792927 : Blo 1792097 1792927 := bstep (se 1 (by rfl) ⟨1344695, by rfl⟩ : syracuseStep 1792927 = 2689391) B2689391
theorem B1793071 : Blo 1792097 1793071 := bstep (se 1 (by rfl) ⟨1344803, by rfl⟩ : syracuseStep 1793071 = 2689607) B2689607
theorem B1793095 : Blo 1792097 1793095 := bstep (se 1 (by rfl) ⟨1344821, by rfl⟩ : syracuseStep 1793095 = 2689643) B2689643
theorem B318569561 : Blo 1792097 318569561 := bstep (se 2 (by rfl) ⟨119463585, by rfl⟩ : syracuseStep 318569561 = 238927171) B238927171
theorem B12926081 : Blo 1792097 12926081 := bstep (se 2 (by rfl) ⟨4847280, by rfl⟩ : syracuseStep 12926081 = 9694561) B9694561
theorem B1793247 : Blo 1792097 1793247 := bstep (se 1 (by rfl) ⟨1344935, by rfl⟩ : syracuseStep 1793247 = 2689871) B2689871
theorem B6053129 : Blo 1792097 6053129 := bstep (se 2 (by rfl) ⟨2269923, by rfl⟩ : syracuseStep 6053129 = 4539847) B4539847
theorem B49061213 : Blo 1792097 49061213 := bstep (se 3 (by rfl) ⟨9198977, by rfl⟩ : syracuseStep 49061213 = 18397955) B18397955
theorem B4914599 : Blo 1792097 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B1793511 : Blo 1792097 1793511 := bstep (se 1 (by rfl) ⟨1345133, by rfl⟩ : syracuseStep 1793511 = 2690267) B2690267
theorem B34479695 : Blo 1792097 34479695 := bstep (se 1 (by rfl) ⟨25859771, by rfl⟩ : syracuseStep 34479695 = 51719543) B51719543
theorem B1793627 : Blo 1792097 1793627 := bstep (se 1 (by rfl) ⟨1345220, by rfl⟩ : syracuseStep 1793627 = 2690441) B2690441
theorem B10911323 : Blo 1792097 10911323 := bstep (se 1 (by rfl) ⟨8183492, by rfl⟩ : syracuseStep 10911323 = 16366985) B16366985
theorem B8617697 : Blo 1792097 8617697 := bstep (se 2 (by rfl) ⟨3231636, by rfl⟩ : syracuseStep 8617697 = 6463273) B6463273
theorem B155180771 : Blo 1792097 155180771 := bstep (se 1 (by rfl) ⟨116385578, by rfl⟩ : syracuseStep 155180771 = 232771157) B232771157
theorem B7274231 : Blo 1792097 7274231 := bstep (se 1 (by rfl) ⟨5455673, by rfl⟩ : syracuseStep 7274231 = 10911347) B10911347
theorem B2268967 : Blo 1792097 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B7659319 : Blo 1792097 7659319 := bstep (se 1 (by rfl) ⟨5744489, by rfl⟩ : syracuseStep 7659319 = 11488979) B11488979
theorem B1793863 : Blo 1792097 1793863 := bstep (se 1 (by rfl) ⟨1345397, by rfl⟩ : syracuseStep 1793863 = 2690795) B2690795
theorem B36798371 : Blo 1792097 36798371 := bstep (se 1 (by rfl) ⟨27598778, by rfl⟩ : syracuseStep 36798371 = 55197557) B55197557
theorem B1794015 : Blo 1792097 1794015 := bstep (se 1 (by rfl) ⟨1345511, by rfl⟩ : syracuseStep 1794015 = 2691023) B2691023
theorem B4538663 : Blo 1792097 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B2154799 : Blo 1792097 2154799 := bstep (se 1 (by rfl) ⟨1616099, by rfl⟩ : syracuseStep 2154799 = 3232199) B3232199
theorem B10215841 : Blo 1792097 10215841 := bstep (se 2 (by rfl) ⟨3830940, by rfl⟩ : syracuseStep 10215841 = 7661881) B7661881
theorem B4309463 : Blo 1792097 4309463 := bstep (se 1 (by rfl) ⟨3232097, by rfl⟩ : syracuseStep 4309463 = 6464195) B6464195
theorem B49734557 : Blo 1792097 49734557 := bstep (se 3 (by rfl) ⟨9325229, by rfl⟩ : syracuseStep 49734557 = 18650459) B18650459
theorem B45966365 : Blo 1792097 45966365 := bstep (se 3 (by rfl) ⟨8618693, by rfl⟩ : syracuseStep 45966365 = 17237387) B17237387
theorem B4539503 : Blo 1792097 4539503 := bstep (se 1 (by rfl) ⟨3404627, by rfl⟩ : syracuseStep 4539503 = 6809255) B6809255
theorem B2688191 : Blo 1792097 2688191 := bstep (se 1 (by rfl) ⟨2016143, by rfl⟩ : syracuseStep 2688191 = 4032287) B4032287
theorem B2688335 : Blo 1792097 2688335 := bstep (se 1 (by rfl) ⟨2016251, by rfl⟩ : syracuseStep 2688335 = 4032503) B4032503
theorem B10216799 : Blo 1792097 10216799 := bstep (se 1 (by rfl) ⟨7662599, by rfl⟩ : syracuseStep 10216799 = 15325199) B15325199
theorem B2688425 : Blo 1792097 2688425 := bstep (se 2 (by rfl) ⟨1008159, by rfl⟩ : syracuseStep 2688425 = 2016319) B2016319
theorem B2688575 : Blo 1792097 2688575 := bstep (se 1 (by rfl) ⟨2016431, by rfl⟩ : syracuseStep 2688575 = 4032863) B4032863
theorem B17466961 : Blo 1792097 17466961 := bstep (se 2 (by rfl) ⟨6550110, by rfl⟩ : syracuseStep 17466961 = 13100221) B13100221
theorem B2688617 : Blo 1792097 2688617 := bstep (se 2 (by rfl) ⟨1008231, by rfl⟩ : syracuseStep 2688617 = 2016463) B2016463
theorem B14534255 : Blo 1792097 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B27616889 : Blo 1792097 27616889 := bstep (se 2 (by rfl) ⟨10356333, by rfl⟩ : syracuseStep 27616889 = 20712667) B20712667
theorem B52422389 : Blo 1792097 52422389 := bstep (se 5 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 52422389 = 4914599) B4914599
theorem B4032377 : Blo 1792097 4032377 := bstep (se 2 (by rfl) ⟨1512141, by rfl⟩ : syracuseStep 4032377 = 3024283) B3024283
theorem B9078803 : Blo 1792097 9078803 := bstep (se 1 (by rfl) ⟨6809102, by rfl⟩ : syracuseStep 9078803 = 13618205) B13618205
theorem B2689055 : Blo 1792097 2689055 := bstep (se 1 (by rfl) ⟨2016791, by rfl⟩ : syracuseStep 2689055 = 4033583) B4033583
theorem B2017327 : Blo 1792097 2017327 := bstep (se 1 (by rfl) ⟨1512995, by rfl⟩ : syracuseStep 2017327 = 3025991) B3025991
theorem B212379707 : Blo 1792097 212379707 := bstep (se 1 (by rfl) ⟨159284780, by rfl⟩ : syracuseStep 212379707 = 318569561) B318569561
theorem B2689247 : Blo 1792097 2689247 := bstep (se 1 (by rfl) ⟨2016935, by rfl⟩ : syracuseStep 2689247 = 4033871) B4033871
theorem B2689307 : Blo 1792097 2689307 := bstep (se 1 (by rfl) ⟨2016980, by rfl⟩ : syracuseStep 2689307 = 4033961) B4033961
theorem B4032809 : Blo 1792097 4032809 := bstep (se 2 (by rfl) ⟨1512303, by rfl⟩ : syracuseStep 4032809 = 3024607) B3024607
theorem B2017615 : Blo 1792097 2017615 := bstep (se 1 (by rfl) ⟨1513211, by rfl⟩ : syracuseStep 2017615 = 3026423) B3026423
theorem B7268717 : Blo 1792097 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B3025289 : Blo 1792097 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B8292797 : Blo 1792097 8292797 := bstep (se 3 (by rfl) ⟨1554899, by rfl⟩ : syracuseStep 8292797 = 3109799) B3109799
theorem B5745131 : Blo 1792097 5745131 := bstep (se 1 (by rfl) ⟨4308848, by rfl⟩ : syracuseStep 5745131 = 8617697) B8617697
theorem B2689631 : Blo 1792097 2689631 := bstep (se 1 (by rfl) ⟨2017223, by rfl⟩ : syracuseStep 2689631 = 4034447) B4034447
theorem B18401897 : Blo 1792097 18401897 := bstep (se 2 (by rfl) ⟨6900711, by rfl⟩ : syracuseStep 18401897 = 13801423) B13801423
theorem B6048377 : Blo 1792097 6048377 := bstep (se 2 (by rfl) ⟨2268141, by rfl⟩ : syracuseStep 6048377 = 4536283) B4536283
theorem B9079613 : Blo 1792097 9079613 := bstep (se 3 (by rfl) ⟨1702427, by rfl⟩ : syracuseStep 9079613 = 3404855) B3404855
theorem B4033385 : Blo 1792097 4033385 := bstep (se 2 (by rfl) ⟨1512519, by rfl⟩ : syracuseStep 4033385 = 3025039) B3025039
theorem B2689913 : Blo 1792097 2689913 := bstep (se 2 (by rfl) ⟨1008717, by rfl⟩ : syracuseStep 2689913 = 2017435) B2017435
theorem B4541305 : Blo 1792097 4541305 := bstep (se 2 (by rfl) ⟨1702989, by rfl⟩ : syracuseStep 4541305 = 3405979) B3405979
theorem B4033439 : Blo 1792097 4033439 := bstep (se 1 (by rfl) ⟨3025079, by rfl⟩ : syracuseStep 4033439 = 6050159) B6050159
theorem B2689961 : Blo 1792097 2689961 := bstep (se 2 (by rfl) ⟨1008735, by rfl⟩ : syracuseStep 2689961 = 2017471) B2017471
theorem B3828703 : Blo 1792097 3828703 := bstep (se 1 (by rfl) ⟨2871527, by rfl⟩ : syracuseStep 3828703 = 5743055) B5743055
theorem B2018299 : Blo 1792097 2018299 := bstep (se 1 (by rfl) ⟨1513724, by rfl⟩ : syracuseStep 2018299 = 3027449) B3027449
theorem B2690111 : Blo 1792097 2690111 := bstep (se 1 (by rfl) ⟨2017583, by rfl⟩ : syracuseStep 2690111 = 4035167) B4035167
theorem B3403063 : Blo 1792097 3403063 := bstep (se 1 (by rfl) ⟨2552297, by rfl⟩ : syracuseStep 3403063 = 5104595) B5104595
theorem B17239391 : Blo 1792097 17239391 := bstep (se 1 (by rfl) ⟨12929543, by rfl⟩ : syracuseStep 17239391 = 25859087) B25859087
theorem B7269821 : Blo 1792097 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B49057265 : Blo 1792097 49057265 := bstep (se 2 (by rfl) ⟨18396474, by rfl⟩ : syracuseStep 49057265 = 36792949) B36792949
theorem B7654945 : Blo 1792097 7654945 := bstep (se 2 (by rfl) ⟨2870604, by rfl⟩ : syracuseStep 7654945 = 5741209) B5741209
theorem B2690663 : Blo 1792097 2690663 := bstep (se 1 (by rfl) ⟨2017997, by rfl⟩ : syracuseStep 2690663 = 4035995) B4035995
theorem B4034375 : Blo 1792097 4034375 := bstep (se 1 (by rfl) ⟨3025781, by rfl⟩ : syracuseStep 4034375 = 6051563) B6051563
theorem B11489131 : Blo 1792097 11489131 := bstep (se 1 (by rfl) ⟨8616848, by rfl⟩ : syracuseStep 11489131 = 17233697) B17233697
theorem B2691047 : Blo 1792097 2691047 := bstep (se 1 (by rfl) ⟨2018285, by rfl⟩ : syracuseStep 2691047 = 4036571) B4036571
theorem B4034555 : Blo 1792097 4034555 := bstep (se 1 (by rfl) ⟨3025916, by rfl⟩ : syracuseStep 4034555 = 6051833) B6051833
theorem B3027017 : Blo 1792097 3027017 := bstep (se 2 (by rfl) ⟨1135131, by rfl⟩ : syracuseStep 3027017 = 2270263) B2270263
theorem B4034663 : Blo 1792097 4034663 := bstep (se 1 (by rfl) ⟨3025997, by rfl⟩ : syracuseStep 4034663 = 6051995) B6051995
theorem B3027071 : Blo 1792097 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B7655579 : Blo 1792097 7655579 := bstep (se 1 (by rfl) ⟨5741684, by rfl⟩ : syracuseStep 7655579 = 11483369) B11483369
theorem B4034735 : Blo 1792097 4034735 := bstep (se 1 (by rfl) ⟨3026051, by rfl⟩ : syracuseStep 4034735 = 6052103) B6052103
theorem B3633385 : Blo 1792097 3633385 := bstep (se 2 (by rfl) ⟨1362519, by rfl⟩ : syracuseStep 3633385 = 2725039) B2725039
theorem B7655867 : Blo 1792097 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B15733529 : Blo 1792097 15733529 := bstep (se 2 (by rfl) ⟨5900073, by rfl⟩ : syracuseStep 15733529 = 11800147) B11800147
theorem B2552639 : Blo 1792097 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B3830591 : Blo 1792097 3830591 := bstep (se 1 (by rfl) ⟨2872943, by rfl⟩ : syracuseStep 3830591 = 5745887) B5745887
theorem B22713169 : Blo 1792097 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B4035419 : Blo 1792097 4035419 := bstep (se 1 (by rfl) ⟨3026564, by rfl⟩ : syracuseStep 4035419 = 6053129) B6053129
theorem B34943881 : Blo 1792097 34943881 := bstep (se 2 (by rfl) ⟨13103955, by rfl⟩ : syracuseStep 34943881 = 26207911) B26207911
theorem B32707475 : Blo 1792097 32707475 := bstep (se 1 (by rfl) ⟨24530606, by rfl⟩ : syracuseStep 32707475 = 49061213) B49061213
theorem B8614927 : Blo 1792097 8614927 := bstep (se 1 (by rfl) ⟨6461195, by rfl⟩ : syracuseStep 8614927 = 12922391) B12922391
theorem B9081881 : Blo 1792097 9081881 := bstep (se 2 (by rfl) ⟨3405705, by rfl⟩ : syracuseStep 9081881 = 6811411) B6811411
theorem B41399369 : Blo 1792097 41399369 := bstep (se 2 (by rfl) ⟨15524763, by rfl⟩ : syracuseStep 41399369 = 31049527) B31049527
theorem B10212425 : Blo 1792097 10212425 := bstep (se 2 (by rfl) ⟨3829659, by rfl⟩ : syracuseStep 10212425 = 7659319) B7659319
theorem B103453847 : Blo 1792097 103453847 := bstep (se 1 (by rfl) ⟨77590385, by rfl⟩ : syracuseStep 103453847 = 155180771) B155180771
theorem B7271635 : Blo 1792097 7271635 := bstep (se 1 (by rfl) ⟨5453726, by rfl⟩ : syracuseStep 7271635 = 10907453) B10907453
theorem B24532247 : Blo 1792097 24532247 := bstep (se 1 (by rfl) ⟨18399185, by rfl⟩ : syracuseStep 24532247 = 36798371) B36798371
theorem B51672491 : Blo 1792097 51672491 := bstep (se 1 (by rfl) ⟨38754368, by rfl⟩ : syracuseStep 51672491 = 77508737) B77508737
theorem B36804107 : Blo 1792097 36804107 := bstep (se 1 (by rfl) ⟨27603080, by rfl⟩ : syracuseStep 36804107 = 55206161) B55206161
theorem B4036175 : Blo 1792097 4036175 := bstep (se 1 (by rfl) ⟨3027131, by rfl⟩ : syracuseStep 4036175 = 6054263) B6054263
theorem B34469549 : Blo 1792097 34469549 := bstep (se 3 (by rfl) ⟨6463040, by rfl⟩ : syracuseStep 34469549 = 12926081) B12926081
theorem B9688855 : Blo 1792097 9688855 := bstep (se 1 (by rfl) ⟨7266641, by rfl⟩ : syracuseStep 9688855 = 14533283) B14533283
theorem B1914715 : Blo 1792097 1914715 := bstep (se 1 (by rfl) ⟨1436036, by rfl⟩ : syracuseStep 1914715 = 2872073) B2872073
theorem B7272659 : Blo 1792097 7272659 := bstep (se 1 (by rfl) ⟨5454494, by rfl⟩ : syracuseStep 7272659 = 10908989) B10908989
theorem B1792231 : Blo 1792097 1792231 := bstep (se 1 (by rfl) ⟨1344173, by rfl⟩ : syracuseStep 1792231 = 2688347) B2688347
theorem B1792415 : Blo 1792097 1792415 := bstep (se 1 (by rfl) ⟨1344311, by rfl⟩ : syracuseStep 1792415 = 2688623) B2688623
theorem B1792463 : Blo 1792097 1792463 := bstep (se 1 (by rfl) ⟨1344347, by rfl⟩ : syracuseStep 1792463 = 2688695) B2688695
theorem B10910159 : Blo 1792097 10910159 := bstep (se 1 (by rfl) ⟨8182619, by rfl⟩ : syracuseStep 10910159 = 16365239) B16365239
theorem B1792487 : Blo 1792097 1792487 := bstep (se 1 (by rfl) ⟨1344365, by rfl⟩ : syracuseStep 1792487 = 2688731) B2688731
theorem B13457939 : Blo 1792097 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B16366141 : Blo 1792097 16366141 := bstep (se 3 (by rfl) ⟨3068651, by rfl⟩ : syracuseStep 16366141 = 6137303) B6137303
theorem B1792603 : Blo 1792097 1792603 := bstep (se 1 (by rfl) ⟨1344452, by rfl⟩ : syracuseStep 1792603 = 2688905) B2688905
theorem B8731295 : Blo 1792097 8731295 := bstep (se 1 (by rfl) ⟨6548471, by rfl⟩ : syracuseStep 8731295 = 13096943) B13096943
theorem B1792671 : Blo 1792097 1792671 := bstep (se 1 (by rfl) ⟨1344503, by rfl⟩ : syracuseStep 1792671 = 2689007) B2689007
theorem B1792839 : Blo 1792097 1792839 := bstep (se 1 (by rfl) ⟨1344629, by rfl⟩ : syracuseStep 1792839 = 2689259) B2689259
theorem B1792879 : Blo 1792097 1792879 := bstep (se 1 (by rfl) ⟨1344659, by rfl⟩ : syracuseStep 1792879 = 2689319) B2689319
theorem B4537255 : Blo 1792097 4537255 := bstep (se 1 (by rfl) ⟨3402941, by rfl⟩ : syracuseStep 4537255 = 6805883) B6805883
theorem B1792935 : Blo 1792097 1792935 := bstep (se 1 (by rfl) ⟨1344701, by rfl⟩ : syracuseStep 1792935 = 2689403) B2689403
theorem B1793115 : Blo 1792097 1793115 := bstep (se 1 (by rfl) ⟨1344836, by rfl⟩ : syracuseStep 1793115 = 2689673) B2689673
theorem B15744203 : Blo 1792097 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B1793231 : Blo 1792097 1793231 := bstep (se 1 (by rfl) ⟨1344923, by rfl⟩ : syracuseStep 1793231 = 2689847) B2689847
theorem B1793255 : Blo 1792097 1793255 := bstep (se 1 (by rfl) ⟨1344941, by rfl⟩ : syracuseStep 1793255 = 2689883) B2689883
theorem B1793351 : Blo 1792097 1793351 := bstep (se 1 (by rfl) ⟨1345013, by rfl⟩ : syracuseStep 1793351 = 2690027) B2690027
theorem B1793487 : Blo 1792097 1793487 := bstep (se 1 (by rfl) ⟨1345115, by rfl⟩ : syracuseStep 1793487 = 2690231) B2690231
theorem B16358921 : Blo 1792097 16358921 := bstep (se 2 (by rfl) ⟨6134595, by rfl⟩ : syracuseStep 16358921 = 12269191) B12269191
theorem B1793647 : Blo 1792097 1793647 := bstep (se 1 (by rfl) ⟨1345235, by rfl⟩ : syracuseStep 1793647 = 2690471) B2690471
theorem B1793703 : Blo 1792097 1793703 := bstep (se 1 (by rfl) ⟨1345277, by rfl⟩ : syracuseStep 1793703 = 2690555) B2690555
theorem B22986463 : Blo 1792097 22986463 := bstep (se 1 (by rfl) ⟨17239847, by rfl⟩ : syracuseStep 22986463 = 34479695) B34479695
theorem B1793767 : Blo 1792097 1793767 := bstep (se 1 (by rfl) ⟨1345325, by rfl⟩ : syracuseStep 1793767 = 2690651) B2690651
theorem B7274215 : Blo 1792097 7274215 := bstep (se 1 (by rfl) ⟨5455661, by rfl⟩ : syracuseStep 7274215 = 10911323) B10911323
theorem B1793823 : Blo 1792097 1793823 := bstep (se 1 (by rfl) ⟨1345367, by rfl⟩ : syracuseStep 1793823 = 2690735) B2690735
theorem B4849487 : Blo 1792097 4849487 := bstep (se 1 (by rfl) ⟨3637115, by rfl⟩ : syracuseStep 4849487 = 7274231) B7274231
theorem B1793903 : Blo 1792097 1793903 := bstep (se 1 (by rfl) ⟨1345427, by rfl⟩ : syracuseStep 1793903 = 2690855) B2690855
theorem B1793959 : Blo 1792097 1793959 := bstep (se 1 (by rfl) ⟨1345469, by rfl⟩ : syracuseStep 1793959 = 2690939) B2690939
theorem B55214045 : Blo 1792097 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B5103719 : Blo 1792097 5103719 := bstep (se 1 (by rfl) ⟨3827789, by rfl⟩ : syracuseStep 5103719 = 7655579) B7655579
theorem B5103911 : Blo 1792097 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B6054587 : Blo 1792097 6054587 := bstep (se 1 (by rfl) ⟨4540940, by rfl⟩ : syracuseStep 6054587 = 9081881) B9081881
theorem B27599579 : Blo 1792097 27599579 := bstep (se 1 (by rfl) ⟨20699684, by rfl⟩ : syracuseStep 27599579 = 41399369) B41399369
theorem B6808283 : Blo 1792097 6808283 := bstep (se 1 (by rfl) ⟨5106212, by rfl⟩ : syracuseStep 6808283 = 10212425) B10212425
theorem B68969231 : Blo 1792097 68969231 := bstep (se 1 (by rfl) ⟨51726923, by rfl⟩ : syracuseStep 68969231 = 103453847) B103453847
theorem B34448327 : Blo 1792097 34448327 := bstep (se 1 (by rfl) ⟨25836245, by rfl⟩ : syracuseStep 34448327 = 51672491) B51672491
theorem B19383245 : Blo 1792097 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B24536071 : Blo 1792097 24536071 := bstep (se 1 (by rfl) ⟨18402053, by rfl⟩ : syracuseStep 24536071 = 36804107) B36804107
theorem B22979699 : Blo 1792097 22979699 := bstep (se 1 (by rfl) ⟨17234774, by rfl⟩ : syracuseStep 22979699 = 34469549) B34469549
theorem B34948259 : Blo 1792097 34948259 := bstep (se 1 (by rfl) ⟨26211194, by rfl⟩ : syracuseStep 34948259 = 52422389) B52422389
theorem B6055073 : Blo 1792097 6055073 := bstep (se 2 (by rfl) ⟨2270652, by rfl⟩ : syracuseStep 6055073 = 4541305) B4541305
theorem B2688251 : Blo 1792097 2688251 := bstep (se 1 (by rfl) ⟨2016188, by rfl⟩ : syracuseStep 2688251 = 4032377) B4032377
theorem B5104937 : Blo 1792097 5104937 := bstep (se 2 (by rfl) ⟨1914351, by rfl⟩ : syracuseStep 5104937 = 3828703) B3828703
theorem B11486569 : Blo 1792097 11486569 := bstep (se 2 (by rfl) ⟨4307463, by rfl⟩ : syracuseStep 11486569 = 8614927) B8614927
theorem B2688539 : Blo 1792097 2688539 := bstep (se 1 (by rfl) ⟨2016404, by rfl⟩ : syracuseStep 2688539 = 4032809) B4032809
theorem B2016859 : Blo 1792097 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B38758013 : Blo 1792097 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B4032251 : Blo 1792097 4032251 := bstep (se 1 (by rfl) ⟨3024188, by rfl⟩ : syracuseStep 4032251 = 6048377) B6048377
theorem B2688923 : Blo 1792097 2688923 := bstep (se 1 (by rfl) ⟨2016692, by rfl⟩ : syracuseStep 2688923 = 4033385) B4033385
theorem B2688959 : Blo 1792097 2688959 := bstep (se 1 (by rfl) ⟨2016719, by rfl⟩ : syracuseStep 2688959 = 4033439) B4033439
theorem B10496135 : Blo 1792097 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B30648617 : Blo 1792097 30648617 := bstep (se 2 (by rfl) ⟨11493231, by rfl⟩ : syracuseStep 30648617 = 22986463) B22986463
theorem B32704843 : Blo 1792097 32704843 := bstep (se 1 (by rfl) ⟨24528632, by rfl⟩ : syracuseStep 32704843 = 49057265) B49057265
theorem B10905947 : Blo 1792097 10905947 := bstep (se 1 (by rfl) ⟨8179460, by rfl⟩ : syracuseStep 10905947 = 16358921) B16358921
theorem B2689583 : Blo 1792097 2689583 := bstep (se 1 (by rfl) ⟨2017187, by rfl⟩ : syracuseStep 2689583 = 4034375) B4034375
theorem B36809363 : Blo 1792097 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B2689703 : Blo 1792097 2689703 := bstep (se 1 (by rfl) ⟨2017277, by rfl⟩ : syracuseStep 2689703 = 4034555) B4034555
theorem B2018011 : Blo 1792097 2018011 := bstep (se 1 (by rfl) ⟨1513508, by rfl⟩ : syracuseStep 2018011 = 3027017) B3027017
theorem B2689769 : Blo 1792097 2689769 := bstep (se 2 (by rfl) ⟨1008663, by rfl⟩ : syracuseStep 2689769 = 2017327) B2017327
theorem B2689775 : Blo 1792097 2689775 := bstep (se 1 (by rfl) ⟨2017331, by rfl⟩ : syracuseStep 2689775 = 4034663) B4034663
theorem B2018047 : Blo 1792097 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B2689823 : Blo 1792097 2689823 := bstep (se 1 (by rfl) ⟨2017367, by rfl⟩ : syracuseStep 2689823 = 4034735) B4034735
theorem B3025775 : Blo 1792097 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B143551349 : Blo 1792097 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B4844513 : Blo 1792097 4844513 := bstep (se 2 (by rfl) ⟨1816692, by rfl⟩ : syracuseStep 4844513 = 3633385) B3633385
theorem B2690153 : Blo 1792097 2690153 := bstep (se 2 (by rfl) ⟨1008807, by rfl⟩ : syracuseStep 2690153 = 2017615) B2017615
theorem B10489019 : Blo 1792097 10489019 := bstep (se 1 (by rfl) ⟨7866764, by rfl⟩ : syracuseStep 10489019 = 15733529) B15733529
theorem B2690279 : Blo 1792097 2690279 := bstep (se 1 (by rfl) ⟨2017709, by rfl⟩ : syracuseStep 2690279 = 4035419) B4035419
theorem B33156371 : Blo 1792097 33156371 := bstep (se 1 (by rfl) ⟨24867278, by rfl⟩ : syracuseStep 33156371 = 49734557) B49734557
theorem B3026335 : Blo 1792097 3026335 := bstep (se 1 (by rfl) ⟨2269751, by rfl⟩ : syracuseStep 3026335 = 4539503) B4539503
theorem B16354831 : Blo 1792097 16354831 := bstep (se 1 (by rfl) ⟨12266123, by rfl⟩ : syracuseStep 16354831 = 24532247) B24532247
theorem B6811199 : Blo 1792097 6811199 := bstep (se 1 (by rfl) ⟨5108399, by rfl⟩ : syracuseStep 6811199 = 10216799) B10216799
theorem B2690783 : Blo 1792097 2690783 := bstep (se 1 (by rfl) ⟨2018087, by rfl⟩ : syracuseStep 2690783 = 4036175) B4036175
theorem B18411259 : Blo 1792097 18411259 := bstep (se 1 (by rfl) ⟨13808444, by rfl⟩ : syracuseStep 18411259 = 27616889) B27616889
theorem B46591841 : Blo 1792097 46591841 := bstep (se 2 (by rfl) ⟨17471940, by rfl⟩ : syracuseStep 46591841 = 34943881) B34943881
theorem B6049673 : Blo 1792097 6049673 := bstep (se 2 (by rfl) ⟨2268627, by rfl⟩ : syracuseStep 6049673 = 4537255) B4537255
theorem B2691065 : Blo 1792097 2691065 := bstep (se 2 (by rfl) ⟨1009149, by rfl⟩ : syracuseStep 2691065 = 2018299) B2018299
theorem B141586471 : Blo 1792097 141586471 := bstep (se 1 (by rfl) ⟨106189853, by rfl⟩ : syracuseStep 141586471 = 212379707) B212379707
theorem B9695513 : Blo 1792097 9695513 := bstep (se 2 (by rfl) ⟨3635817, by rfl⟩ : syracuseStep 9695513 = 7271635) B7271635
theorem B3830087 : Blo 1792097 3830087 := bstep (se 1 (by rfl) ⟨2872565, by rfl⟩ : syracuseStep 3830087 = 5745131) B5745131
theorem B12267931 : Blo 1792097 12267931 := bstep (se 1 (by rfl) ⟨9200948, by rfl⟩ : syracuseStep 12267931 = 18401897) B18401897
theorem B5820863 : Blo 1792097 5820863 := bstep (se 1 (by rfl) ⟨4365647, by rfl⟩ : syracuseStep 5820863 = 8731295) B8731295
theorem B4846547 : Blo 1792097 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B2552953 : Blo 1792097 2552953 := bstep (se 2 (by rfl) ⟨957357, by rfl⟩ : syracuseStep 2552953 = 1914715) B1914715
theorem B3232991 : Blo 1792097 3232991 := bstep (se 1 (by rfl) ⟨2424743, by rfl⟩ : syracuseStep 3232991 = 4849487) B4849487
theorem B2873065 : Blo 1792097 2873065 := bstep (se 2 (by rfl) ⟨1077399, by rfl⟩ : syracuseStep 2873065 = 2154799) B2154799
theorem B13621121 : Blo 1792097 13621121 := bstep (se 2 (by rfl) ⟨5107920, by rfl⟩ : syracuseStep 13621121 = 10215841) B10215841
theorem B21804983 : Blo 1792097 21804983 := bstep (se 1 (by rfl) ⟨16353737, by rfl⟩ : syracuseStep 21804983 = 32707475) B32707475
theorem B30644243 : Blo 1792097 30644243 := bstep (se 1 (by rfl) ⟨22983182, by rfl⟩ : syracuseStep 30644243 = 45966365) B45966365
theorem B21821521 : Blo 1792097 21821521 := bstep (se 2 (by rfl) ⟨8183070, by rfl⟩ : syracuseStep 21821521 = 16366141) B16366141
theorem B1792127 : Blo 1792097 1792127 := bstep (se 1 (by rfl) ⟨1344095, by rfl⟩ : syracuseStep 1792127 = 2688191) B2688191
theorem B1792223 : Blo 1792097 1792223 := bstep (se 1 (by rfl) ⟨1344167, by rfl⟩ : syracuseStep 1792223 = 2688335) B2688335
theorem B1792283 : Blo 1792097 1792283 := bstep (se 1 (by rfl) ⟨1344212, by rfl⟩ : syracuseStep 1792283 = 2688425) B2688425
theorem B1792383 : Blo 1792097 1792383 := bstep (se 1 (by rfl) ⟨1344287, by rfl⟩ : syracuseStep 1792383 = 2688575) B2688575
theorem B1792411 : Blo 1792097 1792411 := bstep (se 1 (by rfl) ⟨1344308, by rfl⟩ : syracuseStep 1792411 = 2688617) B2688617
theorem B30284225 : Blo 1792097 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B11491901 : Blo 1792097 11491901 := bstep (se 3 (by rfl) ⟨2154731, by rfl⟩ : syracuseStep 11491901 = 4309463) B4309463
theorem B6052535 : Blo 1792097 6052535 := bstep (se 1 (by rfl) ⟨4539401, by rfl⟩ : syracuseStep 6052535 = 9078803) B9078803
theorem B1792703 : Blo 1792097 1792703 := bstep (se 1 (by rfl) ⟨1344527, by rfl⟩ : syracuseStep 1792703 = 2689055) B2689055
theorem B4848439 : Blo 1792097 4848439 := bstep (se 1 (by rfl) ⟨3636329, by rfl⟩ : syracuseStep 4848439 = 7272659) B7272659
theorem B1792831 : Blo 1792097 1792831 := bstep (se 1 (by rfl) ⟨1344623, by rfl⟩ : syracuseStep 1792831 = 2689247) B2689247
theorem B1792871 : Blo 1792097 1792871 := bstep (se 1 (by rfl) ⟨1344653, by rfl⟩ : syracuseStep 1792871 = 2689307) B2689307
theorem B5528531 : Blo 1792097 5528531 := bstep (se 1 (by rfl) ⟨4146398, by rfl⟩ : syracuseStep 5528531 = 8292797) B8292797
theorem B7273439 : Blo 1792097 7273439 := bstep (se 1 (by rfl) ⟨5455079, by rfl⟩ : syracuseStep 7273439 = 10910159) B10910159
theorem B1793087 : Blo 1792097 1793087 := bstep (se 1 (by rfl) ⟨1344815, by rfl⟩ : syracuseStep 1793087 = 2689631) B2689631
theorem B4537417 : Blo 1792097 4537417 := bstep (se 2 (by rfl) ⟨1701531, by rfl⟩ : syracuseStep 4537417 = 3403063) B3403063
theorem B6053075 : Blo 1792097 6053075 := bstep (se 1 (by rfl) ⟨4539806, by rfl⟩ : syracuseStep 6053075 = 9079613) B9079613
theorem B1793275 : Blo 1792097 1793275 := bstep (se 1 (by rfl) ⟨1344956, by rfl⟩ : syracuseStep 1793275 = 2689913) B2689913
theorem B1793307 : Blo 1792097 1793307 := bstep (se 1 (by rfl) ⟨1344980, by rfl⟩ : syracuseStep 1793307 = 2689961) B2689961
theorem B1793407 : Blo 1792097 1793407 := bstep (se 1 (by rfl) ⟨1345055, by rfl⟩ : syracuseStep 1793407 = 2690111) B2690111
theorem B10206593 : Blo 1792097 10206593 := bstep (se 2 (by rfl) ⟨3827472, by rfl⟩ : syracuseStep 10206593 = 7654945) B7654945
theorem B23289281 : Blo 1792097 23289281 := bstep (se 2 (by rfl) ⟨8733480, by rfl⟩ : syracuseStep 23289281 = 17466961) B17466961
theorem B6807037 : Blo 1792097 6807037 := bstep (se 3 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 6807037 = 2552639) B2552639
theorem B10214909 : Blo 1792097 10214909 := bstep (se 3 (by rfl) ⟨1915295, by rfl⟩ : syracuseStep 10214909 = 3830591) B3830591
theorem B11492927 : Blo 1792097 11492927 := bstep (se 1 (by rfl) ⟨8619695, by rfl⟩ : syracuseStep 11492927 = 17239391) B17239391
theorem B9698953 : Blo 1792097 9698953 := bstep (se 2 (by rfl) ⟨3637107, by rfl⟩ : syracuseStep 9698953 = 7274215) B7274215
theorem B12918473 : Blo 1792097 12918473 := bstep (se 2 (by rfl) ⟨4844427, by rfl⟩ : syracuseStep 12918473 = 9688855) B9688855
theorem B1793775 : Blo 1792097 1793775 := bstep (se 1 (by rfl) ⟨1345331, by rfl⟩ : syracuseStep 1793775 = 2690663) B2690663
theorem B15318841 : Blo 1792097 15318841 := bstep (se 2 (by rfl) ⟨5744565, by rfl⟩ : syracuseStep 15318841 = 11489131) B11489131
theorem B1794031 : Blo 1792097 1794031 := bstep (se 1 (by rfl) ⟨1345523, by rfl⟩ : syracuseStep 1794031 = 2691047) B2691047
theorem B6463675 : Blo 1792097 6463675 := bstep (se 1 (by rfl) ⟨4847756, by rfl⟩ : syracuseStep 6463675 = 9695513) B9695513
theorem B43606457 : Blo 1792097 43606457 := bstep (se 2 (by rfl) ⟨16352421, by rfl⟩ : syracuseStep 43606457 = 32704843) B32704843
theorem B18399719 : Blo 1792097 18399719 := bstep (se 1 (by rfl) ⟨13799789, by rfl⟩ : syracuseStep 18399719 = 27599579) B27599579
theorem B4538855 : Blo 1792097 4538855 := bstep (se 1 (by rfl) ⟨3404141, by rfl⟩ : syracuseStep 4538855 = 6808283) B6808283
theorem B15319799 : Blo 1792097 15319799 := bstep (se 1 (by rfl) ⟨11489849, by rfl⟩ : syracuseStep 15319799 = 22979699) B22979699
theorem B23298839 : Blo 1792097 23298839 := bstep (se 1 (by rfl) ⟨17474129, by rfl⟩ : syracuseStep 23298839 = 34948259) B34948259
theorem B6464585 : Blo 1792097 6464585 := bstep (se 2 (by rfl) ⟨2424219, by rfl⟩ : syracuseStep 6464585 = 4848439) B4848439
theorem B25838675 : Blo 1792097 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B2688167 : Blo 1792097 2688167 := bstep (se 1 (by rfl) ⟨2016125, by rfl⟩ : syracuseStep 2688167 = 4032251) B4032251
theorem B6997423 : Blo 1792097 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B20432411 : Blo 1792097 20432411 := bstep (se 1 (by rfl) ⟨15324308, by rfl⟩ : syracuseStep 20432411 = 30648617) B30648617
theorem B7661267 : Blo 1792097 7661267 := bstep (se 1 (by rfl) ⟨5745950, by rfl⟩ : syracuseStep 7661267 = 11491901) B11491901
theorem B98158301 : Blo 1792097 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B2017183 : Blo 1792097 2017183 := bstep (se 1 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 2017183 = 3025775) B3025775
theorem B95700899 : Blo 1792097 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B3229675 : Blo 1792097 3229675 := bstep (se 1 (by rfl) ⟨2422256, by rfl⟩ : syracuseStep 3229675 = 4844513) B4844513
theorem B2689145 : Blo 1792097 2689145 := bstep (se 2 (by rfl) ⟨1008429, by rfl⟩ : syracuseStep 2689145 = 2016859) B2016859
theorem B22104247 : Blo 1792097 22104247 := bstep (se 1 (by rfl) ⟨16578185, by rfl⟩ : syracuseStep 22104247 = 33156371) B33156371
theorem B15526187 : Blo 1792097 15526187 := bstep (se 1 (by rfl) ⟨11644640, by rfl⟩ : syracuseStep 15526187 = 23289281) B23289281
theorem B6809939 : Blo 1792097 6809939 := bstep (se 1 (by rfl) ⟨5107454, by rfl⟩ : syracuseStep 6809939 = 10214909) B10214909
theorem B7661951 : Blo 1792097 7661951 := bstep (se 1 (by rfl) ⟨5746463, by rfl⟩ : syracuseStep 7661951 = 11492927) B11492927
theorem B4540799 : Blo 1792097 4540799 := bstep (se 1 (by rfl) ⟨3405599, by rfl⟩ : syracuseStep 4540799 = 6811199) B6811199
theorem B20425121 : Blo 1792097 20425121 := bstep (se 2 (by rfl) ⟨7659420, by rfl⟩ : syracuseStep 20425121 = 15318841) B15318841
theorem B8612315 : Blo 1792097 8612315 := bstep (se 1 (by rfl) ⟨6459236, by rfl⟩ : syracuseStep 8612315 = 12918473) B12918473
theorem B4033115 : Blo 1792097 4033115 := bstep (se 1 (by rfl) ⟨3024836, by rfl⟩ : syracuseStep 4033115 = 6049673) B6049673
theorem B3402479 : Blo 1792097 3402479 := bstep (se 1 (by rfl) ⟨2551859, by rfl⟩ : syracuseStep 3402479 = 5103719) B5103719
theorem B27970717 : Blo 1792097 27970717 := bstep (se 3 (by rfl) ⟨5244509, by rfl⟩ : syracuseStep 27970717 = 10489019) B10489019
theorem B8621309 : Blo 1792097 8621309 := bstep (se 3 (by rfl) ⟨1616495, by rfl⟩ : syracuseStep 8621309 = 3232991) B3232991
theorem B22965551 : Blo 1792097 22965551 := bstep (se 1 (by rfl) ⟨17224163, by rfl⟩ : syracuseStep 22965551 = 34448327) B34448327
theorem B12922163 : Blo 1792097 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B3231031 : Blo 1792097 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B13610429 : Blo 1792097 13610429 := bstep (se 3 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 13610429 = 5103911) B5103911
theorem B3403291 : Blo 1792097 3403291 := bstep (se 1 (by rfl) ⟨2552468, by rfl⟩ : syracuseStep 3403291 = 5104937) B5104937
theorem B2690681 : Blo 1792097 2690681 := bstep (se 2 (by rfl) ⟨1009005, by rfl⟩ : syracuseStep 2690681 = 2018011) B2018011
theorem B2690729 : Blo 1792097 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B9080747 : Blo 1792097 9080747 := bstep (se 1 (by rfl) ⟨6810560, by rfl⟩ : syracuseStep 9080747 = 13621121) B13621121
theorem B14536655 : Blo 1792097 14536655 := bstep (se 1 (by rfl) ⟨10902491, by rfl⟩ : syracuseStep 14536655 = 21804983) B21804983
theorem B32714761 : Blo 1792097 32714761 := bstep (se 2 (by rfl) ⟨12268035, by rfl⟩ : syracuseStep 32714761 = 24536071) B24536071
theorem B6049889 : Blo 1792097 6049889 := bstep (se 2 (by rfl) ⟨2268708, by rfl⟩ : syracuseStep 6049889 = 4537417) B4537417
theorem B3403937 : Blo 1792097 3403937 := bstep (se 2 (by rfl) ⟨1276476, by rfl⟩ : syracuseStep 3403937 = 2552953) B2552953
theorem B7270631 : Blo 1792097 7270631 := bstep (se 1 (by rfl) ⟨5452973, by rfl⟩ : syracuseStep 7270631 = 10905947) B10905947
theorem B20189483 : Blo 1792097 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B4035023 : Blo 1792097 4035023 := bstep (se 1 (by rfl) ⟨3026267, by rfl⟩ : syracuseStep 4035023 = 6052535) B6052535
theorem B15315425 : Blo 1792097 15315425 := bstep (se 2 (by rfl) ⟨5743284, by rfl⟩ : syracuseStep 15315425 = 11486569) B11486569
theorem B4035113 : Blo 1792097 4035113 := bstep (se 2 (by rfl) ⟨1513167, by rfl⟩ : syracuseStep 4035113 = 3026335) B3026335
theorem B4035383 : Blo 1792097 4035383 := bstep (se 1 (by rfl) ⟨3026537, by rfl⟩ : syracuseStep 4035383 = 6053075) B6053075
theorem B12931937 : Blo 1792097 12931937 := bstep (se 2 (by rfl) ⟨4849476, by rfl⟩ : syracuseStep 12931937 = 9698953) B9698953
theorem B6804395 : Blo 1792097 6804395 := bstep (se 1 (by rfl) ⟨5103296, by rfl⟩ : syracuseStep 6804395 = 10206593) B10206593
theorem B3830753 : Blo 1792097 3830753 := bstep (se 2 (by rfl) ⟨1436532, by rfl⟩ : syracuseStep 3830753 = 2873065) B2873065
theorem B24548345 : Blo 1792097 24548345 := bstep (se 2 (by rfl) ⟨9205629, by rfl⟩ : syracuseStep 24548345 = 18411259) B18411259
theorem B14742749 : Blo 1792097 14742749 := bstep (se 3 (by rfl) ⟨2764265, by rfl⟩ : syracuseStep 14742749 = 5528531) B5528531
theorem B31061227 : Blo 1792097 31061227 := bstep (se 1 (by rfl) ⟨23295920, by rfl⟩ : syracuseStep 31061227 = 46591841) B46591841
theorem B188781961 : Blo 1792097 188781961 := bstep (se 2 (by rfl) ⟨70793235, by rfl⟩ : syracuseStep 188781961 = 141586471) B141586471
theorem B29095361 : Blo 1792097 29095361 := bstep (se 2 (by rfl) ⟨10910760, by rfl⟩ : syracuseStep 29095361 = 21821521) B21821521
theorem B2553391 : Blo 1792097 2553391 := bstep (se 1 (by rfl) ⟨1915043, by rfl⟩ : syracuseStep 2553391 = 3830087) B3830087
theorem B4036391 : Blo 1792097 4036391 := bstep (se 1 (by rfl) ⟨3027293, by rfl⟩ : syracuseStep 4036391 = 6054587) B6054587
theorem B45979487 : Blo 1792097 45979487 := bstep (se 1 (by rfl) ⟨34484615, by rfl⟩ : syracuseStep 45979487 = 68969231) B68969231
theorem B16357241 : Blo 1792097 16357241 := bstep (se 2 (by rfl) ⟨6133965, by rfl⟩ : syracuseStep 16357241 = 12267931) B12267931
theorem B4036715 : Blo 1792097 4036715 := bstep (se 1 (by rfl) ⟨3027536, by rfl⟩ : syracuseStep 4036715 = 6055073) B6055073
theorem B1792167 : Blo 1792097 1792167 := bstep (se 1 (by rfl) ⟨1344125, by rfl⟩ : syracuseStep 1792167 = 2688251) B2688251
theorem B1792359 : Blo 1792097 1792359 := bstep (se 1 (by rfl) ⟨1344269, by rfl⟩ : syracuseStep 1792359 = 2688539) B2688539
theorem B15522301 : Blo 1792097 15522301 := bstep (se 3 (by rfl) ⟨2910431, by rfl⟩ : syracuseStep 15522301 = 5820863) B5820863
theorem B1792615 : Blo 1792097 1792615 := bstep (se 1 (by rfl) ⟨1344461, by rfl⟩ : syracuseStep 1792615 = 2688923) B2688923
theorem B1792639 : Blo 1792097 1792639 := bstep (se 1 (by rfl) ⟨1344479, by rfl⟩ : syracuseStep 1792639 = 2688959) B2688959
theorem B20429495 : Blo 1792097 20429495 := bstep (se 1 (by rfl) ⟨15322121, by rfl⟩ : syracuseStep 20429495 = 30644243) B30644243
theorem B1794043 : Blo 1792097 1794043 := bstep (se 1 (by rfl) ⟨1345532, by rfl⟩ : syracuseStep 1794043 = 2691065) B2691065
theorem B1793055 : Blo 1792097 1793055 := bstep (se 1 (by rfl) ⟨1344791, by rfl⟩ : syracuseStep 1793055 = 2689583) B2689583
theorem B1793135 : Blo 1792097 1793135 := bstep (se 1 (by rfl) ⟨1344851, by rfl⟩ : syracuseStep 1793135 = 2689703) B2689703
theorem B1793179 : Blo 1792097 1793179 := bstep (se 1 (by rfl) ⟨1344884, by rfl⟩ : syracuseStep 1793179 = 2689769) B2689769
theorem B1793183 : Blo 1792097 1793183 := bstep (se 1 (by rfl) ⟨1344887, by rfl⟩ : syracuseStep 1793183 = 2689775) B2689775
theorem B1793215 : Blo 1792097 1793215 := bstep (se 1 (by rfl) ⟨1344911, by rfl⟩ : syracuseStep 1793215 = 2689823) B2689823
theorem B4848959 : Blo 1792097 4848959 := bstep (se 1 (by rfl) ⟨3636719, by rfl⟩ : syracuseStep 4848959 = 7273439) B7273439
theorem B9076049 : Blo 1792097 9076049 := bstep (se 2 (by rfl) ⟨3403518, by rfl⟩ : syracuseStep 9076049 = 6807037) B6807037
theorem B21806441 : Blo 1792097 21806441 := bstep (se 2 (by rfl) ⟨8177415, by rfl⟩ : syracuseStep 21806441 = 16354831) B16354831
theorem B1793435 : Blo 1792097 1793435 := bstep (se 1 (by rfl) ⟨1345076, by rfl⟩ : syracuseStep 1793435 = 2690153) B2690153
theorem B1793519 : Blo 1792097 1793519 := bstep (se 1 (by rfl) ⟨1345139, by rfl⟩ : syracuseStep 1793519 = 2690279) B2690279
theorem B1793855 : Blo 1792097 1793855 := bstep (se 1 (by rfl) ⟨1345391, by rfl⟩ : syracuseStep 1793855 = 2690783) B2690783
theorem B2269291 : Blo 1792097 2269291 := bstep (se 1 (by rfl) ⟨1701968, by rfl⟩ : syracuseStep 2269291 = 3403937) B3403937
theorem B13459655 : Blo 1792097 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B8618233 : Blo 1792097 8618233 := bstep (se 2 (by rfl) ⟨3231837, by rfl⟩ : syracuseStep 8618233 = 6463675) B6463675
theorem B15532559 : Blo 1792097 15532559 := bstep (se 1 (by rfl) ⟨11649419, by rfl⟩ : syracuseStep 15532559 = 23298839) B23298839
theorem B4309723 : Blo 1792097 4309723 := bstep (se 1 (by rfl) ⟨3232292, by rfl⟩ : syracuseStep 4309723 = 6464585) B6464585
theorem B65438867 : Blo 1792097 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B10904827 : Blo 1792097 10904827 := bstep (se 1 (by rfl) ⟨8178620, by rfl⟩ : syracuseStep 10904827 = 16357241) B16357241
theorem B4539959 : Blo 1792097 4539959 := bstep (se 1 (by rfl) ⟨3404969, by rfl⟩ : syracuseStep 4539959 = 6809939) B6809939
theorem B13616747 : Blo 1792097 13616747 := bstep (se 1 (by rfl) ⟨10212560, by rfl⟩ : syracuseStep 13616747 = 20425121) B20425121
theorem B2688743 : Blo 1792097 2688743 := bstep (se 1 (by rfl) ⟨2016557, by rfl⟩ : syracuseStep 2688743 = 4033115) B4033115
theorem B251709281 : Blo 1792097 251709281 := bstep (se 2 (by rfl) ⟨94390980, by rfl⟩ : syracuseStep 251709281 = 188781961) B188781961
theorem B2689577 : Blo 1792097 2689577 := bstep (se 2 (by rfl) ⟨1008591, by rfl⟩ : syracuseStep 2689577 = 2017183) B2017183
theorem B4033259 : Blo 1792097 4033259 := bstep (se 1 (by rfl) ⟨3024944, by rfl⟩ : syracuseStep 4033259 = 6049889) B6049889
theorem B2690015 : Blo 1792097 2690015 := bstep (se 1 (by rfl) ⟨2017511, by rfl⟩ : syracuseStep 2690015 = 4035023) B4035023
theorem B10210283 : Blo 1792097 10210283 := bstep (se 1 (by rfl) ⟨7657712, by rfl⟩ : syracuseStep 10210283 = 15315425) B15315425
theorem B12266479 : Blo 1792097 12266479 := bstep (se 1 (by rfl) ⟨9199859, by rfl⟩ : syracuseStep 12266479 = 18399719) B18399719
theorem B3025903 : Blo 1792097 3025903 := bstep (se 1 (by rfl) ⟨2269427, by rfl⟩ : syracuseStep 3025903 = 4538855) B4538855
theorem B2690075 : Blo 1792097 2690075 := bstep (se 1 (by rfl) ⟨2017556, by rfl⟩ : syracuseStep 2690075 = 4035113) B4035113
theorem B2690255 : Blo 1792097 2690255 := bstep (se 1 (by rfl) ⟨2017691, by rfl⟩ : syracuseStep 2690255 = 4035383) B4035383
theorem B8621291 : Blo 1792097 8621291 := bstep (se 1 (by rfl) ⟨6465968, by rfl⟩ : syracuseStep 8621291 = 12931937) B12931937
theorem B20696401 : Blo 1792097 20696401 := bstep (se 2 (by rfl) ⟨7761150, by rfl⟩ : syracuseStep 20696401 = 15522301) B15522301
theorem B5107511 : Blo 1792097 5107511 := bstep (se 1 (by rfl) ⟨3830633, by rfl⟩ : syracuseStep 5107511 = 7661267) B7661267
theorem B2690927 : Blo 1792097 2690927 := bstep (se 1 (by rfl) ⟨2018195, by rfl⟩ : syracuseStep 2690927 = 4036391) B4036391
theorem B2691143 : Blo 1792097 2691143 := bstep (se 1 (by rfl) ⟨2018357, by rfl⟩ : syracuseStep 2691143 = 4036715) B4036715
theorem B10350791 : Blo 1792097 10350791 := bstep (se 1 (by rfl) ⟨7763093, by rfl⟩ : syracuseStep 10350791 = 15526187) B15526187
theorem B37294289 : Blo 1792097 37294289 := bstep (se 2 (by rfl) ⟨13985358, by rfl⟩ : syracuseStep 37294289 = 27970717) B27970717
theorem B5107967 : Blo 1792097 5107967 := bstep (se 1 (by rfl) ⟨3830975, by rfl⟩ : syracuseStep 5107967 = 7661951) B7661951
theorem B3027199 : Blo 1792097 3027199 := bstep (se 1 (by rfl) ⟨2270399, by rfl⟩ : syracuseStep 3027199 = 4540799) B4540799
theorem B41414969 : Blo 1792097 41414969 := bstep (se 2 (by rfl) ⟨15530613, by rfl⟩ : syracuseStep 41414969 = 31061227) B31061227
theorem B13619663 : Blo 1792097 13619663 := bstep (se 1 (by rfl) ⟨10214747, by rfl⟩ : syracuseStep 13619663 = 20429495) B20429495
theorem B3404521 : Blo 1792097 3404521 := bstep (se 2 (by rfl) ⟨1276695, by rfl⟩ : syracuseStep 3404521 = 2553391) B2553391
theorem B5747539 : Blo 1792097 5747539 := bstep (se 1 (by rfl) ⟨4310654, by rfl⟩ : syracuseStep 5747539 = 8621309) B8621309
theorem B8614775 : Blo 1792097 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B3232639 : Blo 1792097 3232639 := bstep (se 1 (by rfl) ⟨2424479, by rfl⟩ : syracuseStep 3232639 = 4848959) B4848959
theorem B6050699 : Blo 1792097 6050699 := bstep (se 1 (by rfl) ⟨4538024, by rfl⟩ : syracuseStep 6050699 = 9076049) B9076049
theorem B14537627 : Blo 1792097 14537627 := bstep (se 1 (by rfl) ⟨10903220, by rfl⟩ : syracuseStep 14537627 = 21806441) B21806441
theorem B9073619 : Blo 1792097 9073619 := bstep (se 1 (by rfl) ⟨6805214, by rfl⟩ : syracuseStep 9073619 = 13610429) B13610429
theorem B255202397 : Blo 1792097 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B17224933 : Blo 1792097 17224933 := bstep (se 4 (by rfl) ⟨1614837, by rfl⟩ : syracuseStep 17224933 = 3229675) B3229675
theorem B43619681 : Blo 1792097 43619681 := bstep (se 2 (by rfl) ⟨16357380, by rfl⟩ : syracuseStep 43619681 = 32714761) B32714761
theorem B4847087 : Blo 1792097 4847087 := bstep (se 1 (by rfl) ⟨3635315, by rfl⟩ : syracuseStep 4847087 = 7270631) B7270631
theorem B29472329 : Blo 1792097 29472329 := bstep (se 2 (by rfl) ⟨11052123, by rfl⟩ : syracuseStep 29472329 = 22104247) B22104247
theorem B29070971 : Blo 1792097 29070971 := bstep (se 1 (by rfl) ⟨21803228, by rfl⟩ : syracuseStep 29070971 = 43606457) B43606457
theorem B10213199 : Blo 1792097 10213199 := bstep (se 1 (by rfl) ⟨7659899, by rfl⟩ : syracuseStep 10213199 = 15319799) B15319799
theorem B4536263 : Blo 1792097 4536263 := bstep (se 1 (by rfl) ⟨3402197, by rfl⟩ : syracuseStep 4536263 = 6804395) B6804395
theorem B16365563 : Blo 1792097 16365563 := bstep (se 1 (by rfl) ⟨12274172, by rfl⟩ : syracuseStep 16365563 = 24548345) B24548345
theorem B17225783 : Blo 1792097 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B1792111 : Blo 1792097 1792111 := bstep (se 1 (by rfl) ⟨1344083, by rfl⟩ : syracuseStep 1792111 = 2688167) B2688167
theorem B9828499 : Blo 1792097 9828499 := bstep (se 1 (by rfl) ⟨7371374, by rfl⟩ : syracuseStep 9828499 = 14742749) B14742749
theorem B19396907 : Blo 1792097 19396907 := bstep (se 1 (by rfl) ⟨14547680, by rfl⟩ : syracuseStep 19396907 = 29095361) B29095361
theorem B13621607 : Blo 1792097 13621607 := bstep (se 1 (by rfl) ⟨10216205, by rfl⟩ : syracuseStep 13621607 = 20432411) B20432411
theorem B30652991 : Blo 1792097 30652991 := bstep (se 1 (by rfl) ⟨22989743, by rfl⟩ : syracuseStep 30652991 = 45979487) B45979487
theorem B1792763 : Blo 1792097 1792763 := bstep (se 1 (by rfl) ⟨1344572, by rfl⟩ : syracuseStep 1792763 = 2689145) B2689145
theorem B5741543 : Blo 1792097 5741543 := bstep (se 1 (by rfl) ⟨4306157, by rfl⟩ : syracuseStep 5741543 = 8612315) B8612315
theorem B4308041 : Blo 1792097 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B2268319 : Blo 1792097 2268319 := bstep (se 1 (by rfl) ⟨1701239, by rfl⟩ : syracuseStep 2268319 = 3402479) B3402479
theorem B9329897 : Blo 1792097 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B4537721 : Blo 1792097 4537721 := bstep (se 2 (by rfl) ⟨1701645, by rfl⟩ : syracuseStep 4537721 = 3403291) B3403291
theorem B15310367 : Blo 1792097 15310367 := bstep (se 1 (by rfl) ⟨11482775, by rfl⟩ : syracuseStep 15310367 = 22965551) B22965551
theorem B1793787 : Blo 1792097 1793787 := bstep (se 1 (by rfl) ⟨1345340, by rfl⟩ : syracuseStep 1793787 = 2690681) B2690681
theorem B1793819 : Blo 1792097 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B10215341 : Blo 1792097 10215341 := bstep (se 3 (by rfl) ⟨1915376, by rfl⟩ : syracuseStep 10215341 = 3830753) B3830753
theorem B6053831 : Blo 1792097 6053831 := bstep (se 1 (by rfl) ⟨4540373, by rfl⟩ : syracuseStep 6053831 = 9080747) B9080747
theorem B9691103 : Blo 1792097 9691103 := bstep (se 1 (by rfl) ⟨7268327, by rfl⟩ : syracuseStep 9691103 = 14536655) B14536655
theorem B1794095 : Blo 1792097 1794095 := bstep (se 1 (by rfl) ⟨1345571, by rfl⟩ : syracuseStep 1794095 = 2691143) B2691143
theorem B24862859 : Blo 1792097 24862859 := bstep (se 1 (by rfl) ⟨18647144, by rfl⟩ : syracuseStep 24862859 = 37294289) B37294289
theorem B10355039 : Blo 1792097 10355039 := bstep (se 1 (by rfl) ⟨7766279, by rfl⟩ : syracuseStep 10355039 = 15532559) B15532559
theorem B5743183 : Blo 1792097 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B9691751 : Blo 1792097 9691751 := bstep (se 1 (by rfl) ⟨7268813, by rfl⟩ : syracuseStep 9691751 = 14537627) B14537627
theorem B116319149 : Blo 1792097 116319149 := bstep (se 3 (by rfl) ⟨21809840, by rfl⟩ : syracuseStep 116319149 = 43619681) B43619681
theorem B4539361 : Blo 1792097 4539361 := bstep (se 2 (by rfl) ⟨1702260, by rfl⟩ : syracuseStep 4539361 = 3404521) B3404521
theorem B9077831 : Blo 1792097 9077831 := bstep (se 1 (by rfl) ⟨6808373, by rfl⟩ : syracuseStep 9077831 = 13616747) B13616747
theorem B4310185 : Blo 1792097 4310185 := bstep (se 2 (by rfl) ⟨1616319, by rfl⟩ : syracuseStep 4310185 = 3232639) B3232639
theorem B6808799 : Blo 1792097 6808799 := bstep (se 1 (by rfl) ⟨5106599, by rfl⟩ : syracuseStep 6808799 = 10213199) B10213199
theorem B167806187 : Blo 1792097 167806187 := bstep (se 1 (by rfl) ⟨125854640, by rfl⟩ : syracuseStep 167806187 = 251709281) B251709281
theorem B3024175 : Blo 1792097 3024175 := bstep (se 1 (by rfl) ⟨2268131, by rfl⟩ : syracuseStep 3024175 = 4536263) B4536263
theorem B3024425 : Blo 1792097 3024425 := bstep (se 2 (by rfl) ⟨1134159, by rfl⟩ : syracuseStep 3024425 = 2268319) B2268319
theorem B2688839 : Blo 1792097 2688839 := bstep (se 1 (by rfl) ⟨2016629, by rfl⟩ : syracuseStep 2688839 = 4033259) B4033259
theorem B3827695 : Blo 1792097 3827695 := bstep (se 1 (by rfl) ⟨2870771, by rfl⟩ : syracuseStep 3827695 = 5741543) B5741543
theorem B6219931 : Blo 1792097 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B3025147 : Blo 1792097 3025147 := bstep (se 1 (by rfl) ⟨2268860, by rfl⟩ : syracuseStep 3025147 = 4537721) B4537721
theorem B6810227 : Blo 1792097 6810227 := bstep (se 1 (by rfl) ⟨5107670, by rfl⟩ : syracuseStep 6810227 = 10215341) B10215341
theorem B6900527 : Blo 1792097 6900527 := bstep (se 1 (by rfl) ⟨5175395, by rfl⟩ : syracuseStep 6900527 = 10350791) B10350791
theorem B3025721 : Blo 1792097 3025721 := bstep (se 2 (by rfl) ⟨1134645, by rfl⟩ : syracuseStep 3025721 = 2269291) B2269291
theorem B27609979 : Blo 1792097 27609979 := bstep (se 1 (by rfl) ⟨20707484, by rfl⟩ : syracuseStep 27609979 = 41414969) B41414969
theorem B9079775 : Blo 1792097 9079775 := bstep (se 1 (by rfl) ⟨6809831, by rfl⟩ : syracuseStep 9079775 = 13619663) B13619663
theorem B35892413 : Blo 1792097 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B4033799 : Blo 1792097 4033799 := bstep (se 1 (by rfl) ⟨3025349, by rfl⟩ : syracuseStep 4033799 = 6050699) B6050699
theorem B6049079 : Blo 1792097 6049079 := bstep (se 1 (by rfl) ⟨4536809, by rfl⟩ : syracuseStep 6049079 = 9073619) B9073619
theorem B170134931 : Blo 1792097 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B43625911 : Blo 1792097 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B5746297 : Blo 1792097 5746297 := bstep (se 2 (by rfl) ⟨2154861, by rfl⟩ : syracuseStep 5746297 = 4309723) B4309723
theorem B3026639 : Blo 1792097 3026639 := bstep (se 1 (by rfl) ⟨2269979, by rfl⟩ : syracuseStep 3026639 = 4539959) B4539959
theorem B19648219 : Blo 1792097 19648219 := bstep (se 1 (by rfl) ⟨14736164, by rfl⟩ : syracuseStep 19648219 = 29472329) B29472329
theorem B7663385 : Blo 1792097 7663385 := bstep (se 2 (by rfl) ⟨2873769, by rfl⟩ : syracuseStep 7663385 = 5747539) B5747539
theorem B16355305 : Blo 1792097 16355305 := bstep (se 2 (by rfl) ⟨6133239, by rfl⟩ : syracuseStep 16355305 = 12266479) B12266479
theorem B4034537 : Blo 1792097 4034537 := bstep (se 2 (by rfl) ⟨1512951, by rfl⟩ : syracuseStep 4034537 = 3025903) B3025903
theorem B12931271 : Blo 1792097 12931271 := bstep (se 1 (by rfl) ⟨9698453, by rfl⟩ : syracuseStep 12931271 = 19396907) B19396907
theorem B9081071 : Blo 1792097 9081071 := bstep (se 1 (by rfl) ⟨6810803, by rfl⟩ : syracuseStep 9081071 = 13621607) B13621607
theorem B22966577 : Blo 1792097 22966577 := bstep (se 2 (by rfl) ⟨8612466, by rfl⟩ : syracuseStep 22966577 = 17224933) B17224933
theorem B20435327 : Blo 1792097 20435327 := bstep (se 1 (by rfl) ⟨15326495, by rfl⟩ : syracuseStep 20435327 = 30652991) B30652991
theorem B27595201 : Blo 1792097 27595201 := bstep (se 2 (by rfl) ⟨10348200, by rfl⟩ : syracuseStep 27595201 = 20696401) B20696401
theorem B2872027 : Blo 1792097 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B5747527 : Blo 1792097 5747527 := bstep (se 1 (by rfl) ⟨4310645, by rfl⟩ : syracuseStep 5747527 = 8621291) B8621291
theorem B3405007 : Blo 1792097 3405007 := bstep (se 1 (by rfl) ⟨2553755, by rfl⟩ : syracuseStep 3405007 = 5107511) B5107511
theorem B4035887 : Blo 1792097 4035887 := bstep (se 1 (by rfl) ⟨3026915, by rfl⟩ : syracuseStep 4035887 = 6053831) B6053831
theorem B6460735 : Blo 1792097 6460735 := bstep (se 1 (by rfl) ⟨4845551, by rfl⟩ : syracuseStep 6460735 = 9691103) B9691103
theorem B3405311 : Blo 1792097 3405311 := bstep (se 1 (by rfl) ⟨2553983, by rfl⟩ : syracuseStep 3405311 = 5107967) B5107967
theorem B13104665 : Blo 1792097 13104665 := bstep (se 2 (by rfl) ⟨4914249, by rfl⟩ : syracuseStep 13104665 = 9828499) B9828499
theorem B11490977 : Blo 1792097 11490977 := bstep (se 2 (by rfl) ⟨4309116, by rfl⟩ : syracuseStep 11490977 = 8618233) B8618233
theorem B4036265 : Blo 1792097 4036265 := bstep (se 2 (by rfl) ⟨1513599, by rfl⟩ : syracuseStep 4036265 = 3027199) B3027199
theorem B19380647 : Blo 1792097 19380647 := bstep (se 1 (by rfl) ⟨14535485, by rfl⟩ : syracuseStep 19380647 = 29070971) B29070971
theorem B1792495 : Blo 1792097 1792495 := bstep (se 1 (by rfl) ⟨1344371, by rfl⟩ : syracuseStep 1792495 = 2688743) B2688743
theorem B12925565 : Blo 1792097 12925565 := bstep (se 3 (by rfl) ⟨2423543, by rfl⟩ : syracuseStep 12925565 = 4847087) B4847087
theorem B10910375 : Blo 1792097 10910375 := bstep (se 1 (by rfl) ⟨8182781, by rfl⟩ : syracuseStep 10910375 = 16365563) B16365563
theorem B11483855 : Blo 1792097 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B14539769 : Blo 1792097 14539769 := bstep (se 2 (by rfl) ⟨5452413, by rfl⟩ : syracuseStep 14539769 = 10904827) B10904827
theorem B1793051 : Blo 1792097 1793051 := bstep (se 1 (by rfl) ⟨1344788, by rfl⟩ : syracuseStep 1793051 = 2689577) B2689577
theorem B1793343 : Blo 1792097 1793343 := bstep (se 1 (by rfl) ⟨1345007, by rfl⟩ : syracuseStep 1793343 = 2690015) B2690015
theorem B6806855 : Blo 1792097 6806855 := bstep (se 1 (by rfl) ⟨5105141, by rfl⟩ : syracuseStep 6806855 = 10210283) B10210283
theorem B1793383 : Blo 1792097 1793383 := bstep (se 1 (by rfl) ⟨1345037, by rfl⟩ : syracuseStep 1793383 = 2690075) B2690075
theorem B1793503 : Blo 1792097 1793503 := bstep (se 1 (by rfl) ⟨1345127, by rfl⟩ : syracuseStep 1793503 = 2690255) B2690255
theorem B10206911 : Blo 1792097 10206911 := bstep (se 1 (by rfl) ⟨7655183, by rfl⟩ : syracuseStep 10206911 = 15310367) B15310367
theorem B1793951 : Blo 1792097 1793951 := bstep (se 1 (by rfl) ⟨1345463, by rfl⟩ : syracuseStep 1793951 = 2690927) B2690927
theorem B6054047 : Blo 1792097 6054047 := bstep (se 1 (by rfl) ⟨4540535, by rfl⟩ : syracuseStep 6054047 = 9081071) B9081071
theorem B15311051 : Blo 1792097 15311051 := bstep (se 1 (by rfl) ⟨11483288, by rfl⟩ : syracuseStep 15311051 = 22966577) B22966577
theorem B13623551 : Blo 1792097 13623551 := bstep (se 1 (by rfl) ⟨10217663, by rfl⟩ : syracuseStep 13623551 = 20435327) B20435327
theorem B77546099 : Blo 1792097 77546099 := bstep (se 1 (by rfl) ⟨58159574, by rfl⟩ : syracuseStep 77546099 = 116319149) B116319149
theorem B4539199 : Blo 1792097 4539199 := bstep (se 1 (by rfl) ⟨3404399, by rfl⟩ : syracuseStep 4539199 = 6808799) B6808799
theorem B111870791 : Blo 1792097 111870791 := bstep (se 1 (by rfl) ⟨83903093, by rfl⟩ : syracuseStep 111870791 = 167806187) B167806187
theorem B2270207 : Blo 1792097 2270207 := bstep (se 1 (by rfl) ⟨1702655, by rfl⟩ : syracuseStep 2270207 = 3405311) B3405311
theorem B2016283 : Blo 1792097 2016283 := bstep (se 1 (by rfl) ⟨1512212, by rfl⟩ : syracuseStep 2016283 = 3024425) B3024425
theorem B7660651 : Blo 1792097 7660651 := bstep (se 1 (by rfl) ⟨5745488, by rfl⟩ : syracuseStep 7660651 = 11490977) B11490977
theorem B4540009 : Blo 1792097 4540009 := bstep (se 2 (by rfl) ⟨1702503, by rfl⟩ : syracuseStep 4540009 = 3405007) B3405007
theorem B12920431 : Blo 1792097 12920431 := bstep (se 1 (by rfl) ⟨9690323, by rfl⟩ : syracuseStep 12920431 = 19380647) B19380647
theorem B4032233 : Blo 1792097 4032233 := bstep (se 2 (by rfl) ⟨1512087, by rfl⟩ : syracuseStep 4032233 = 3024175) B3024175
theorem B4540151 : Blo 1792097 4540151 := bstep (se 1 (by rfl) ⟨3405113, by rfl⟩ : syracuseStep 4540151 = 6810227) B6810227
theorem B2017147 : Blo 1792097 2017147 := bstep (se 1 (by rfl) ⟨1512860, by rfl⟩ : syracuseStep 2017147 = 3025721) B3025721
theorem B9693179 : Blo 1792097 9693179 := bstep (se 1 (by rfl) ⟨7269884, by rfl⟩ : syracuseStep 9693179 = 14539769) B14539769
theorem B7661729 : Blo 1792097 7661729 := bstep (se 2 (by rfl) ⟨2873148, by rfl⟩ : syracuseStep 7661729 = 5746297) B5746297
theorem B2689199 : Blo 1792097 2689199 := bstep (se 1 (by rfl) ⟨2016899, by rfl⟩ : syracuseStep 2689199 = 4033799) B4033799
theorem B4032719 : Blo 1792097 4032719 := bstep (se 1 (by rfl) ⟨3024539, by rfl⟩ : syracuseStep 4032719 = 6049079) B6049079
theorem B2017759 : Blo 1792097 2017759 := bstep (se 1 (by rfl) ⟨1513319, by rfl⟩ : syracuseStep 2017759 = 3026639) B3026639
theorem B2689691 : Blo 1792097 2689691 := bstep (se 1 (by rfl) ⟨2017268, by rfl⟩ : syracuseStep 2689691 = 4034537) B4034537
theorem B16575239 : Blo 1792097 16575239 := bstep (se 1 (by rfl) ⟨12431429, by rfl⟩ : syracuseStep 16575239 = 24862859) B24862859
theorem B8620847 : Blo 1792097 8620847 := bstep (se 1 (by rfl) ⟨6465635, by rfl⟩ : syracuseStep 8620847 = 12931271) B12931271
theorem B8293241 : Blo 1792097 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B4033529 : Blo 1792097 4033529 := bstep (se 2 (by rfl) ⟨1512573, by rfl⟩ : syracuseStep 4033529 = 3025147) B3025147
theorem B36793601 : Blo 1792097 36793601 := bstep (se 2 (by rfl) ⟨13797600, by rfl⟩ : syracuseStep 36793601 = 27595201) B27595201
theorem B2690591 : Blo 1792097 2690591 := bstep (se 1 (by rfl) ⟨2017943, by rfl⟩ : syracuseStep 2690591 = 4035887) B4035887
theorem B3829369 : Blo 1792097 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B8736443 : Blo 1792097 8736443 := bstep (se 1 (by rfl) ⟨6552332, by rfl⟩ : syracuseStep 8736443 = 13104665) B13104665
theorem B7663369 : Blo 1792097 7663369 := bstep (se 2 (by rfl) ⟨2873763, by rfl⟩ : syracuseStep 7663369 = 5747527) B5747527
theorem B2690843 : Blo 1792097 2690843 := bstep (se 1 (by rfl) ⟨2018132, by rfl⟩ : syracuseStep 2690843 = 4036265) B4036265
theorem B5746913 : Blo 1792097 5746913 := bstep (se 2 (by rfl) ⟨2155092, by rfl⟩ : syracuseStep 5746913 = 4310185) B4310185
theorem B8614313 : Blo 1792097 8614313 := bstep (se 2 (by rfl) ⟨3230367, by rfl⟩ : syracuseStep 8614313 = 6460735) B6460735
theorem B7655903 : Blo 1792097 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B4600351 : Blo 1792097 4600351 := bstep (se 1 (by rfl) ⟨3450263, by rfl⟩ : syracuseStep 4600351 = 6900527) B6900527
theorem B58167881 : Blo 1792097 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B113423287 : Blo 1792097 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B6804607 : Blo 1792097 6804607 := bstep (se 1 (by rfl) ⟨5103455, by rfl⟩ : syracuseStep 6804607 = 10206911) B10206911
theorem B5108923 : Blo 1792097 5108923 := bstep (se 1 (by rfl) ⟨3831692, by rfl⟩ : syracuseStep 5108923 = 7663385) B7663385
theorem B6903359 : Blo 1792097 6903359 := bstep (se 1 (by rfl) ⟨5177519, by rfl⟩ : syracuseStep 6903359 = 10355039) B10355039
theorem B6051887 : Blo 1792097 6051887 := bstep (se 1 (by rfl) ⟨4538915, by rfl⟩ : syracuseStep 6051887 = 9077831) B9077831
theorem B7657577 : Blo 1792097 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B36813305 : Blo 1792097 36813305 := bstep (se 2 (by rfl) ⟨13804989, by rfl⟩ : syracuseStep 36813305 = 27609979) B27609979
theorem B1792559 : Blo 1792097 1792559 := bstep (se 1 (by rfl) ⟨1344419, by rfl⟩ : syracuseStep 1792559 = 2688839) B2688839
theorem B6052481 : Blo 1792097 6052481 := bstep (se 2 (by rfl) ⟨2269680, by rfl⟩ : syracuseStep 6052481 = 4539361) B4539361
theorem B25844669 : Blo 1792097 25844669 := bstep (se 3 (by rfl) ⟨4845875, by rfl⟩ : syracuseStep 25844669 = 9691751) B9691751
theorem B8617043 : Blo 1792097 8617043 := bstep (se 1 (by rfl) ⟨6462782, by rfl⟩ : syracuseStep 8617043 = 12925565) B12925565
theorem B7273583 : Blo 1792097 7273583 := bstep (se 1 (by rfl) ⟨5455187, by rfl⟩ : syracuseStep 7273583 = 10910375) B10910375
theorem B6053183 : Blo 1792097 6053183 := bstep (se 1 (by rfl) ⟨4539887, by rfl⟩ : syracuseStep 6053183 = 9079775) B9079775
theorem B23928275 : Blo 1792097 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B4537903 : Blo 1792097 4537903 := bstep (se 1 (by rfl) ⟨3403427, by rfl⟩ : syracuseStep 4537903 = 6806855) B6806855
theorem B26197625 : Blo 1792097 26197625 := bstep (se 2 (by rfl) ⟨9824109, by rfl⟩ : syracuseStep 26197625 = 19648219) B19648219
theorem B21807073 : Blo 1792097 21807073 := bstep (se 2 (by rfl) ⟨8177652, by rfl⟩ : syracuseStep 21807073 = 16355305) B16355305
theorem B5103593 : Blo 1792097 5103593 := bstep (se 2 (by rfl) ⟨1913847, by rfl⟩ : syracuseStep 5103593 = 3827695) B3827695
theorem B10207367 : Blo 1792097 10207367 := bstep (se 1 (by rfl) ⟨7655525, by rfl⟩ : syracuseStep 10207367 = 15311051) B15311051
theorem B5742875 : Blo 1792097 5742875 := bstep (se 1 (by rfl) ⟨4307156, by rfl⟩ : syracuseStep 5742875 = 8614313) B8614313
theorem B5103935 : Blo 1792097 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B74580527 : Blo 1792097 74580527 := bstep (se 1 (by rfl) ⟨55935395, by rfl⟩ : syracuseStep 74580527 = 111870791) B111870791
theorem B2688155 : Blo 1792097 2688155 := bstep (se 1 (by rfl) ⟨2016116, by rfl⟩ : syracuseStep 2688155 = 4032233) B4032233
theorem B2688377 : Blo 1792097 2688377 := bstep (se 2 (by rfl) ⟨1008141, by rfl⟩ : syracuseStep 2688377 = 2016283) B2016283
theorem B5105051 : Blo 1792097 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B2688479 : Blo 1792097 2688479 := bstep (se 1 (by rfl) ⟨2016359, by rfl⟩ : syracuseStep 2688479 = 4032719) B4032719
theorem B17229779 : Blo 1792097 17229779 := bstep (se 1 (by rfl) ⟨12922334, by rfl⟩ : syracuseStep 17229779 = 25844669) B25844669
theorem B2689019 : Blo 1792097 2689019 := bstep (se 1 (by rfl) ⟨2016764, by rfl⟩ : syracuseStep 2689019 = 4033529) B4033529
theorem B5744695 : Blo 1792097 5744695 := bstep (se 1 (by rfl) ⟨4308521, by rfl⟩ : syracuseStep 5744695 = 8617043) B8617043
theorem B5105825 : Blo 1792097 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B24529067 : Blo 1792097 24529067 := bstep (se 1 (by rfl) ⟨18396800, by rfl⟩ : syracuseStep 24529067 = 36793601) B36793601
theorem B15952183 : Blo 1792097 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B10217825 : Blo 1792097 10217825 := bstep (se 2 (by rfl) ⟨3831684, by rfl⟩ : syracuseStep 10217825 = 7663369) B7663369
theorem B2689529 : Blo 1792097 2689529 := bstep (se 2 (by rfl) ⟨1008573, by rfl⟩ : syracuseStep 2689529 = 2017147) B2017147
theorem B29076097 : Blo 1792097 29076097 := bstep (se 2 (by rfl) ⟨10903536, by rfl⟩ : syracuseStep 29076097 = 21807073) B21807073
theorem B3402395 : Blo 1792097 3402395 := bstep (se 1 (by rfl) ⟨2551796, by rfl⟩ : syracuseStep 3402395 = 5103593) B5103593
theorem B2690345 : Blo 1792097 2690345 := bstep (se 2 (by rfl) ⟨1008879, by rfl⟩ : syracuseStep 2690345 = 2017759) B2017759
theorem B3026767 : Blo 1792097 3026767 := bstep (se 1 (by rfl) ⟨2270075, by rfl⟩ : syracuseStep 3026767 = 4540151) B4540151
theorem B4034591 : Blo 1792097 4034591 := bstep (se 1 (by rfl) ⟨3025943, by rfl⟩ : syracuseStep 4034591 = 6051887) B6051887
theorem B5107819 : Blo 1792097 5107819 := bstep (se 1 (by rfl) ⟨3830864, by rfl⟩ : syracuseStep 5107819 = 7661729) B7661729
theorem B9072809 : Blo 1792097 9072809 := bstep (se 2 (by rfl) ⟨3402303, by rfl⟩ : syracuseStep 9072809 = 6804607) B6804607
theorem B6811897 : Blo 1792097 6811897 := bstep (se 2 (by rfl) ⟨2554461, by rfl⟩ : syracuseStep 6811897 = 5108923) B5108923
theorem B4034987 : Blo 1792097 4034987 := bstep (se 1 (by rfl) ⟨3026240, by rfl⟩ : syracuseStep 4034987 = 6052481) B6052481
theorem B5747231 : Blo 1792097 5747231 := bstep (se 1 (by rfl) ⟨4310423, by rfl⟩ : syracuseStep 5747231 = 8620847) B8620847
theorem B44200637 : Blo 1792097 44200637 := bstep (se 3 (by rfl) ⟨8287619, by rfl⟩ : syracuseStep 44200637 = 16575239) B16575239
theorem B6050537 : Blo 1792097 6050537 := bstep (se 2 (by rfl) ⟨2268951, by rfl⟩ : syracuseStep 6050537 = 4537903) B4537903
theorem B4035455 : Blo 1792097 4035455 := bstep (se 1 (by rfl) ⟨3026591, by rfl⟩ : syracuseStep 4035455 = 6053183) B6053183
theorem B4036031 : Blo 1792097 4036031 := bstep (se 1 (by rfl) ⟨3027023, by rfl⟩ : syracuseStep 4036031 = 6054047) B6054047
theorem B3831275 : Blo 1792097 3831275 := bstep (se 1 (by rfl) ⟨2873456, by rfl⟩ : syracuseStep 3831275 = 5746913) B5746913
theorem B9082367 : Blo 1792097 9082367 := bstep (se 1 (by rfl) ⟨6811775, by rfl⟩ : syracuseStep 9082367 = 13623551) B13623551
theorem B38778587 : Blo 1792097 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B51697399 : Blo 1792097 51697399 := bstep (se 1 (by rfl) ⟨38773049, by rfl⟩ : syracuseStep 51697399 = 77546099) B77546099
theorem B6133801 : Blo 1792097 6133801 := bstep (se 2 (by rfl) ⟨2300175, by rfl⟩ : syracuseStep 6133801 = 4600351) B4600351
theorem B4602239 : Blo 1792097 4602239 := bstep (se 1 (by rfl) ⟨3451679, by rfl⟩ : syracuseStep 4602239 = 6903359) B6903359
theorem B6052265 : Blo 1792097 6052265 := bstep (se 2 (by rfl) ⟨2269599, by rfl⟩ : syracuseStep 6052265 = 4539199) B4539199
theorem B151231049 : Blo 1792097 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B6462119 : Blo 1792097 6462119 := bstep (se 1 (by rfl) ⟨4846589, by rfl⟩ : syracuseStep 6462119 = 9693179) B9693179
theorem B1792799 : Blo 1792097 1792799 := bstep (se 1 (by rfl) ⟨1344599, by rfl⟩ : syracuseStep 1792799 = 2689199) B2689199
theorem B10214201 : Blo 1792097 10214201 := bstep (se 2 (by rfl) ⟨3830325, by rfl⟩ : syracuseStep 10214201 = 7660651) B7660651
theorem B69860333 : Blo 1792097 69860333 := bstep (se 3 (by rfl) ⟨13098812, by rfl⟩ : syracuseStep 69860333 = 26197625) B26197625
theorem B24542203 : Blo 1792097 24542203 := bstep (se 1 (by rfl) ⟨18406652, by rfl⟩ : syracuseStep 24542203 = 36813305) B36813305
theorem B1793127 : Blo 1792097 1793127 := bstep (se 1 (by rfl) ⟨1344845, by rfl⟩ : syracuseStep 1793127 = 2689691) B2689691
theorem B5528827 : Blo 1792097 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B4849055 : Blo 1792097 4849055 := bstep (se 1 (by rfl) ⟨3636791, by rfl⟩ : syracuseStep 4849055 = 7273583) B7273583
theorem B6053345 : Blo 1792097 6053345 := bstep (se 2 (by rfl) ⟨2270004, by rfl⟩ : syracuseStep 6053345 = 4540009) B4540009
theorem B17227241 : Blo 1792097 17227241 := bstep (se 2 (by rfl) ⟨6460215, by rfl⟩ : syracuseStep 17227241 = 12920431) B12920431
theorem B1793727 : Blo 1792097 1793727 := bstep (se 1 (by rfl) ⟨1345295, by rfl⟩ : syracuseStep 1793727 = 2690591) B2690591
theorem B5824295 : Blo 1792097 5824295 := bstep (se 1 (by rfl) ⟨4368221, by rfl⟩ : syracuseStep 5824295 = 8736443) B8736443
theorem B1793895 : Blo 1792097 1793895 := bstep (se 1 (by rfl) ⟨1345421, by rfl⟩ : syracuseStep 1793895 = 2690843) B2690843
theorem B6053885 : Blo 1792097 6053885 := bstep (se 3 (by rfl) ⟨1135103, by rfl⟩ : syracuseStep 6053885 = 2270207) B2270207
theorem B7659593 : Blo 1792097 7659593 := bstep (se 2 (by rfl) ⟨2872347, by rfl⟩ : syracuseStep 7659593 = 5744695) B5744695
theorem B29467091 : Blo 1792097 29467091 := bstep (se 1 (by rfl) ⟨22100318, by rfl⟩ : syracuseStep 29467091 = 44200637) B44200637
theorem B6054911 : Blo 1792097 6054911 := bstep (se 1 (by rfl) ⟨4541183, by rfl⟩ : syracuseStep 6054911 = 9082367) B9082367
theorem B11486519 : Blo 1792097 11486519 := bstep (se 1 (by rfl) ⟨8614889, by rfl⟩ : syracuseStep 11486519 = 17229779) B17229779
theorem B16352711 : Blo 1792097 16352711 := bstep (se 1 (by rfl) ⟨12264533, by rfl⟩ : syracuseStep 16352711 = 24529067) B24529067
theorem B100820699 : Blo 1792097 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B6809467 : Blo 1792097 6809467 := bstep (se 1 (by rfl) ⟨5107100, by rfl⟩ : syracuseStep 6809467 = 10214201) B10214201
theorem B46573555 : Blo 1792097 46573555 := bstep (se 1 (by rfl) ⟨34930166, by rfl⟩ : syracuseStep 46573555 = 69860333) B69860333
theorem B68929865 : Blo 1792097 68929865 := bstep (se 2 (by rfl) ⟨25848699, by rfl⟩ : syracuseStep 68929865 = 51697399) B51697399
theorem B2689727 : Blo 1792097 2689727 := bstep (se 1 (by rfl) ⟨2017295, by rfl⟩ : syracuseStep 2689727 = 4034591) B4034591
theorem B8178401 : Blo 1792097 8178401 := bstep (se 2 (by rfl) ⟨3066900, by rfl⟩ : syracuseStep 8178401 = 6133801) B6133801
theorem B6048539 : Blo 1792097 6048539 := bstep (se 1 (by rfl) ⟨4536404, by rfl⟩ : syracuseStep 6048539 = 9072809) B9072809
theorem B6810425 : Blo 1792097 6810425 := bstep (se 2 (by rfl) ⟨2553909, by rfl⟩ : syracuseStep 6810425 = 5107819) B5107819
theorem B3828583 : Blo 1792097 3828583 := bstep (se 1 (by rfl) ⟨2871437, by rfl⟩ : syracuseStep 3828583 = 5742875) B5742875
theorem B3402623 : Blo 1792097 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B2689991 : Blo 1792097 2689991 := bstep (se 1 (by rfl) ⟨2017493, by rfl⟩ : syracuseStep 2689991 = 4034987) B4034987
theorem B4033691 : Blo 1792097 4033691 := bstep (se 1 (by rfl) ⟨3025268, by rfl⟩ : syracuseStep 4033691 = 6050537) B6050537
theorem B2690303 : Blo 1792097 2690303 := bstep (se 1 (by rfl) ⟨2017727, by rfl⟩ : syracuseStep 2690303 = 4035455) B4035455
theorem B38768129 : Blo 1792097 38768129 := bstep (se 2 (by rfl) ⟨14538048, by rfl⟩ : syracuseStep 38768129 = 29076097) B29076097
theorem B3403367 : Blo 1792097 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B2690687 : Blo 1792097 2690687 := bstep (se 1 (by rfl) ⟨2018015, by rfl⟩ : syracuseStep 2690687 = 4036031) B4036031
theorem B32722937 : Blo 1792097 32722937 := bstep (se 2 (by rfl) ⟨12271101, by rfl⟩ : syracuseStep 32722937 = 24542203) B24542203
theorem B3403883 : Blo 1792097 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B198881405 : Blo 1792097 198881405 := bstep (se 3 (by rfl) ⟨37290263, by rfl⟩ : syracuseStep 198881405 = 74580527) B74580527
theorem B6811883 : Blo 1792097 6811883 := bstep (se 1 (by rfl) ⟨5108912, by rfl⟩ : syracuseStep 6811883 = 10217825) B10217825
theorem B3068159 : Blo 1792097 3068159 := bstep (se 1 (by rfl) ⟨2301119, by rfl⟩ : syracuseStep 3068159 = 4602239) B4602239
theorem B4034843 : Blo 1792097 4034843 := bstep (se 1 (by rfl) ⟨3026132, by rfl⟩ : syracuseStep 4034843 = 6052265) B6052265
theorem B85078309 : Blo 1792097 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B3232703 : Blo 1792097 3232703 := bstep (se 1 (by rfl) ⟨2424527, by rfl⟩ : syracuseStep 3232703 = 4849055) B4849055
theorem B4035563 : Blo 1792097 4035563 := bstep (se 1 (by rfl) ⟨3026672, by rfl⟩ : syracuseStep 4035563 = 6053345) B6053345
theorem B4035689 : Blo 1792097 4035689 := bstep (se 2 (by rfl) ⟨1513383, by rfl⟩ : syracuseStep 4035689 = 3026767) B3026767
theorem B4035923 : Blo 1792097 4035923 := bstep (se 1 (by rfl) ⟨3026942, by rfl⟩ : syracuseStep 4035923 = 6053885) B6053885
theorem B6804911 : Blo 1792097 6804911 := bstep (se 1 (by rfl) ⟨5103683, by rfl⟩ : syracuseStep 6804911 = 10207367) B10207367
theorem B9082529 : Blo 1792097 9082529 := bstep (se 2 (by rfl) ⟨3405948, by rfl⟩ : syracuseStep 9082529 = 6811897) B6811897
theorem B1792103 : Blo 1792097 1792103 := bstep (se 1 (by rfl) ⟨1344077, by rfl⟩ : syracuseStep 1792103 = 2688155) B2688155
theorem B1792251 : Blo 1792097 1792251 := bstep (se 1 (by rfl) ⟨1344188, by rfl⟩ : syracuseStep 1792251 = 2688377) B2688377
theorem B1792319 : Blo 1792097 1792319 := bstep (se 1 (by rfl) ⟨1344239, by rfl⟩ : syracuseStep 1792319 = 2688479) B2688479
theorem B2554183 : Blo 1792097 2554183 := bstep (se 1 (by rfl) ⟨1915637, by rfl⟩ : syracuseStep 2554183 = 3831275) B3831275
theorem B25852391 : Blo 1792097 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B1792679 : Blo 1792097 1792679 := bstep (se 1 (by rfl) ⟨1344509, by rfl⟩ : syracuseStep 1792679 = 2689019) B2689019
theorem B15325949 : Blo 1792097 15325949 := bstep (se 3 (by rfl) ⟨2873615, by rfl⟩ : syracuseStep 15325949 = 5747231) B5747231
theorem B7371769 : Blo 1792097 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B1793019 : Blo 1792097 1793019 := bstep (se 1 (by rfl) ⟨1344764, by rfl⟩ : syracuseStep 1793019 = 2689529) B2689529
theorem B2268263 : Blo 1792097 2268263 := bstep (se 1 (by rfl) ⟨1701197, by rfl⟩ : syracuseStep 2268263 = 3402395) B3402395
theorem B4308079 : Blo 1792097 4308079 := bstep (se 1 (by rfl) ⟨3231059, by rfl⟩ : syracuseStep 4308079 = 6462119) B6462119
theorem B1793563 : Blo 1792097 1793563 := bstep (se 1 (by rfl) ⟨1345172, by rfl⟩ : syracuseStep 1793563 = 2690345) B2690345
theorem B11484827 : Blo 1792097 11484827 := bstep (se 1 (by rfl) ⟨8613620, by rfl⟩ : syracuseStep 11484827 = 17227241) B17227241
theorem B3882863 : Blo 1792097 3882863 := bstep (se 1 (by rfl) ⟨2912147, by rfl⟩ : syracuseStep 3882863 = 5824295) B5824295
theorem B132587603 : Blo 1792097 132587603 := bstep (se 1 (by rfl) ⟨99440702, by rfl⟩ : syracuseStep 132587603 = 198881405) B198881405
theorem B9077021 : Blo 1792097 9077021 := bstep (se 3 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 9077021 = 3403883) B3403883
theorem B19644727 : Blo 1792097 19644727 := bstep (se 1 (by rfl) ⟨14733545, by rfl⟩ : syracuseStep 19644727 = 29467091) B29467091
theorem B2155135 : Blo 1792097 2155135 := bstep (se 1 (by rfl) ⟨1616351, by rfl⟩ : syracuseStep 2155135 = 3232703) B3232703
theorem B6055019 : Blo 1792097 6055019 := bstep (se 1 (by rfl) ⟨4541264, by rfl⟩ : syracuseStep 6055019 = 9082529) B9082529
theorem B5104777 : Blo 1792097 5104777 := bstep (se 2 (by rfl) ⟨1914291, by rfl⟩ : syracuseStep 5104777 = 3828583) B3828583
theorem B5744105 : Blo 1792097 5744105 := bstep (se 2 (by rfl) ⟨2154039, by rfl⟩ : syracuseStep 5744105 = 4308079) B4308079
theorem B10217299 : Blo 1792097 10217299 := bstep (se 1 (by rfl) ⟨7662974, by rfl⟩ : syracuseStep 10217299 = 15325949) B15325949
theorem B4032359 : Blo 1792097 4032359 := bstep (se 1 (by rfl) ⟨3024269, by rfl⟩ : syracuseStep 4032359 = 6048539) B6048539
theorem B4540283 : Blo 1792097 4540283 := bstep (se 1 (by rfl) ⟨3405212, by rfl⟩ : syracuseStep 4540283 = 6810425) B6810425
theorem B2689127 : Blo 1792097 2689127 := bstep (se 1 (by rfl) ⟨2016845, by rfl⟩ : syracuseStep 2689127 = 4033691) B4033691
theorem B9079289 : Blo 1792097 9079289 := bstep (se 2 (by rfl) ⟨3404733, by rfl⟩ : syracuseStep 9079289 = 6809467) B6809467
theorem B62098073 : Blo 1792097 62098073 := bstep (se 2 (by rfl) ⟨23286777, by rfl⟩ : syracuseStep 62098073 = 46573555) B46573555
theorem B5106395 : Blo 1792097 5106395 := bstep (se 1 (by rfl) ⟨3829796, by rfl⟩ : syracuseStep 5106395 = 7659593) B7659593
theorem B4541255 : Blo 1792097 4541255 := bstep (se 1 (by rfl) ⟨3405941, by rfl⟩ : syracuseStep 4541255 = 6811883) B6811883
theorem B2689895 : Blo 1792097 2689895 := bstep (se 1 (by rfl) ⟨2017421, by rfl⟩ : syracuseStep 2689895 = 4034843) B4034843
theorem B6048701 : Blo 1792097 6048701 := bstep (se 3 (by rfl) ⟨1134131, by rfl⟩ : syracuseStep 6048701 = 2268263) B2268263
theorem B113437745 : Blo 1792097 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B2690375 : Blo 1792097 2690375 := bstep (se 1 (by rfl) ⟨2017781, by rfl⟩ : syracuseStep 2690375 = 4035563) B4035563
theorem B2690459 : Blo 1792097 2690459 := bstep (se 1 (by rfl) ⟨2017844, by rfl⟩ : syracuseStep 2690459 = 4035689) B4035689
theorem B2690615 : Blo 1792097 2690615 := bstep (se 1 (by rfl) ⟨2017961, by rfl⟩ : syracuseStep 2690615 = 4035923) B4035923
theorem B45953243 : Blo 1792097 45953243 := bstep (se 1 (by rfl) ⟨34464932, by rfl⟩ : syracuseStep 45953243 = 68929865) B68929865
theorem B5452267 : Blo 1792097 5452267 := bstep (se 1 (by rfl) ⟨4089200, by rfl⟩ : syracuseStep 5452267 = 8178401) B8178401
theorem B7656551 : Blo 1792097 7656551 := bstep (se 1 (by rfl) ⟨5742413, by rfl⟩ : syracuseStep 7656551 = 11484827) B11484827
theorem B3405577 : Blo 1792097 3405577 := bstep (se 2 (by rfl) ⟨1277091, by rfl⟩ : syracuseStep 3405577 = 2554183) B2554183
theorem B8181757 : Blo 1792097 8181757 := bstep (se 3 (by rfl) ⟨1534079, by rfl⟩ : syracuseStep 8181757 = 3068159) B3068159
theorem B4036607 : Blo 1792097 4036607 := bstep (se 1 (by rfl) ⟨3027455, by rfl⟩ : syracuseStep 4036607 = 6054911) B6054911
theorem B7657679 : Blo 1792097 7657679 := bstep (se 1 (by rfl) ⟨5743259, by rfl⟩ : syracuseStep 7657679 = 11486519) B11486519
theorem B4536607 : Blo 1792097 4536607 := bstep (se 1 (by rfl) ⟨3402455, by rfl⟩ : syracuseStep 4536607 = 6804911) B6804911
theorem B10901807 : Blo 1792097 10901807 := bstep (se 1 (by rfl) ⟨8176355, by rfl⟩ : syracuseStep 10901807 = 16352711) B16352711
theorem B67213799 : Blo 1792097 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B9829025 : Blo 1792097 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B17234927 : Blo 1792097 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B1793151 : Blo 1792097 1793151 := bstep (se 1 (by rfl) ⟨1344863, by rfl⟩ : syracuseStep 1793151 = 2689727) B2689727
theorem B2268415 : Blo 1792097 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B1793327 : Blo 1792097 1793327 := bstep (se 1 (by rfl) ⟨1344995, by rfl⟩ : syracuseStep 1793327 = 2689991) B2689991
theorem B1793535 : Blo 1792097 1793535 := bstep (se 1 (by rfl) ⟨1345151, by rfl⟩ : syracuseStep 1793535 = 2690303) B2690303
theorem B10354301 : Blo 1792097 10354301 := bstep (se 3 (by rfl) ⟨1941431, by rfl⟩ : syracuseStep 10354301 = 3882863) B3882863
theorem B25845419 : Blo 1792097 25845419 := bstep (se 1 (by rfl) ⟨19384064, by rfl⟩ : syracuseStep 25845419 = 38768129) B38768129
theorem B2268911 : Blo 1792097 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B1793791 : Blo 1792097 1793791 := bstep (se 1 (by rfl) ⟨1345343, by rfl⟩ : syracuseStep 1793791 = 2690687) B2690687
theorem B21815291 : Blo 1792097 21815291 := bstep (se 1 (by rfl) ⟨16361468, by rfl⟩ : syracuseStep 21815291 = 32722937) B32722937
theorem B88391735 : Blo 1792097 88391735 := bstep (se 1 (by rfl) ⟨66293801, by rfl⟩ : syracuseStep 88391735 = 132587603) B132587603
theorem B5104367 : Blo 1792097 5104367 := bstep (se 1 (by rfl) ⟨3828275, by rfl⟩ : syracuseStep 5104367 = 7656551) B7656551
theorem B2688239 : Blo 1792097 2688239 := bstep (se 1 (by rfl) ⟨2016179, by rfl⟩ : syracuseStep 2688239 = 4032359) B4032359
theorem B5105119 : Blo 1792097 5105119 := bstep (se 1 (by rfl) ⟨3828839, by rfl⟩ : syracuseStep 5105119 = 7657679) B7657679
theorem B7267871 : Blo 1792097 7267871 := bstep (se 1 (by rfl) ⟨5450903, by rfl⟩ : syracuseStep 7267871 = 10901807) B10901807
theorem B3024553 : Blo 1792097 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B4032467 : Blo 1792097 4032467 := bstep (se 1 (by rfl) ⟨3024350, by rfl⟩ : syracuseStep 4032467 = 6048701) B6048701
theorem B4540769 : Blo 1792097 4540769 := bstep (se 2 (by rfl) ⟨1702788, by rfl⟩ : syracuseStep 4540769 = 3405577) B3405577
theorem B17230279 : Blo 1792097 17230279 := bstep (se 1 (by rfl) ⟨12922709, by rfl⟩ : syracuseStep 17230279 = 25845419) B25845419
theorem B58174109 : Blo 1792097 58174109 := bstep (se 3 (by rfl) ⟨10907645, by rfl⟩ : syracuseStep 58174109 = 21815291) B21815291
theorem B6048809 : Blo 1792097 6048809 := bstep (se 2 (by rfl) ⟨2268303, by rfl⟩ : syracuseStep 6048809 = 4536607) B4536607
theorem B26192969 : Blo 1792097 26192969 := bstep (se 2 (by rfl) ⟨9822363, by rfl⟩ : syracuseStep 26192969 = 19644727) B19644727
theorem B7269689 : Blo 1792097 7269689 := bstep (se 2 (by rfl) ⟨2726133, by rfl⟩ : syracuseStep 7269689 = 5452267) B5452267
theorem B3829403 : Blo 1792097 3829403 := bstep (se 1 (by rfl) ⟨2872052, by rfl⟩ : syracuseStep 3829403 = 5744105) B5744105
theorem B3026855 : Blo 1792097 3026855 := bstep (se 1 (by rfl) ⟨2270141, by rfl⟩ : syracuseStep 3026855 = 4540283) B4540283
theorem B2691071 : Blo 1792097 2691071 := bstep (se 1 (by rfl) ⟨2018303, by rfl⟩ : syracuseStep 2691071 = 4036607) B4036607
theorem B41398715 : Blo 1792097 41398715 := bstep (se 1 (by rfl) ⟨31049036, by rfl⟩ : syracuseStep 41398715 = 62098073) B62098073
theorem B3404263 : Blo 1792097 3404263 := bstep (se 1 (by rfl) ⟨2553197, by rfl⟩ : syracuseStep 3404263 = 5106395) B5106395
theorem B3027503 : Blo 1792097 3027503 := bstep (se 1 (by rfl) ⟨2270627, by rfl⟩ : syracuseStep 3027503 = 4541255) B4541255
theorem B6050429 : Blo 1792097 6050429 := bstep (se 3 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 6050429 = 2268911) B2268911
theorem B11489951 : Blo 1792097 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B75625163 : Blo 1792097 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B6902867 : Blo 1792097 6902867 := bstep (se 1 (by rfl) ⟨5177150, by rfl⟩ : syracuseStep 6902867 = 10354301) B10354301
theorem B10909009 : Blo 1792097 10909009 := bstep (se 2 (by rfl) ⟨4090878, by rfl⟩ : syracuseStep 10909009 = 8181757) B8181757
theorem B30635495 : Blo 1792097 30635495 := bstep (se 1 (by rfl) ⟨22976621, by rfl⟩ : syracuseStep 30635495 = 45953243) B45953243
theorem B6051347 : Blo 1792097 6051347 := bstep (se 1 (by rfl) ⟨4538510, by rfl⟩ : syracuseStep 6051347 = 9077021) B9077021
theorem B4036679 : Blo 1792097 4036679 := bstep (se 1 (by rfl) ⟨3027509, by rfl⟩ : syracuseStep 4036679 = 6055019) B6055019
theorem B2873513 : Blo 1792097 2873513 := bstep (se 2 (by rfl) ⟨1077567, by rfl⟩ : syracuseStep 2873513 = 2155135) B2155135
theorem B1792751 : Blo 1792097 1792751 := bstep (se 1 (by rfl) ⟨1344563, by rfl⟩ : syracuseStep 1792751 = 2689127) B2689127
theorem B6806369 : Blo 1792097 6806369 := bstep (se 2 (by rfl) ⟨2552388, by rfl⟩ : syracuseStep 6806369 = 5104777) B5104777
theorem B44809199 : Blo 1792097 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B6052859 : Blo 1792097 6052859 := bstep (se 1 (by rfl) ⟨4539644, by rfl⟩ : syracuseStep 6052859 = 9079289) B9079289
theorem B6552683 : Blo 1792097 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B1793263 : Blo 1792097 1793263 := bstep (se 1 (by rfl) ⟨1344947, by rfl⟩ : syracuseStep 1793263 = 2689895) B2689895
theorem B1793583 : Blo 1792097 1793583 := bstep (se 1 (by rfl) ⟨1345187, by rfl⟩ : syracuseStep 1793583 = 2690375) B2690375
theorem B1793639 : Blo 1792097 1793639 := bstep (se 1 (by rfl) ⟨1345229, by rfl⟩ : syracuseStep 1793639 = 2690459) B2690459
theorem B1793743 : Blo 1792097 1793743 := bstep (se 1 (by rfl) ⟨1345307, by rfl⟩ : syracuseStep 1793743 = 2690615) B2690615
theorem B13623065 : Blo 1792097 13623065 := bstep (se 2 (by rfl) ⟨5108649, by rfl⟩ : syracuseStep 13623065 = 10217299) B10217299
theorem B18407645 : Blo 1792097 18407645 := bstep (se 3 (by rfl) ⟨3451433, by rfl⟩ : syracuseStep 18407645 = 6902867) B6902867
theorem B27599143 : Blo 1792097 27599143 := bstep (se 1 (by rfl) ⟨20699357, by rfl⟩ : syracuseStep 27599143 = 41398715) B41398715
theorem B4539017 : Blo 1792097 4539017 := bstep (se 2 (by rfl) ⟨1702131, by rfl⟩ : syracuseStep 4539017 = 3404263) B3404263
theorem B20423663 : Blo 1792097 20423663 := bstep (se 1 (by rfl) ⟨15317747, by rfl⟩ : syracuseStep 20423663 = 30635495) B30635495
theorem B2688311 : Blo 1792097 2688311 := bstep (se 1 (by rfl) ⟨2016233, by rfl⟩ : syracuseStep 2688311 = 4032467) B4032467
theorem B30639869 : Blo 1792097 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B38782739 : Blo 1792097 38782739 := bstep (se 1 (by rfl) ⟨29087054, by rfl⟩ : syracuseStep 38782739 = 58174109) B58174109
theorem B4032539 : Blo 1792097 4032539 := bstep (se 1 (by rfl) ⟨3024404, by rfl⟩ : syracuseStep 4032539 = 6048809) B6048809
theorem B4368455 : Blo 1792097 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B4032737 : Blo 1792097 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B2017903 : Blo 1792097 2017903 := bstep (se 1 (by rfl) ⟨1513427, by rfl⟩ : syracuseStep 2017903 = 3026855) B3026855
theorem B58927823 : Blo 1792097 58927823 := bstep (se 1 (by rfl) ⟨44195867, by rfl⟩ : syracuseStep 58927823 = 88391735) B88391735
theorem B2018335 : Blo 1792097 2018335 := bstep (se 1 (by rfl) ⟨1513751, by rfl⟩ : syracuseStep 2018335 = 3027503) B3027503
theorem B4033619 : Blo 1792097 4033619 := bstep (se 1 (by rfl) ⟨3025214, by rfl⟩ : syracuseStep 4033619 = 6050429) B6050429
theorem B7662701 : Blo 1792097 7662701 := bstep (se 3 (by rfl) ⟨1436756, by rfl⟩ : syracuseStep 7662701 = 2873513) B2873513
theorem B50416775 : Blo 1792097 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B3402911 : Blo 1792097 3402911 := bstep (se 1 (by rfl) ⟨2552183, by rfl⟩ : syracuseStep 3402911 = 5104367) B5104367
theorem B22973705 : Blo 1792097 22973705 := bstep (se 2 (by rfl) ⟨8615139, by rfl⟩ : syracuseStep 22973705 = 17230279) B17230279
theorem B4034231 : Blo 1792097 4034231 := bstep (se 1 (by rfl) ⟨3025673, by rfl⟩ : syracuseStep 4034231 = 6051347) B6051347
theorem B2691119 : Blo 1792097 2691119 := bstep (se 1 (by rfl) ⟨2018339, by rfl⟩ : syracuseStep 2691119 = 4036679) B4036679
theorem B3027179 : Blo 1792097 3027179 := bstep (se 1 (by rfl) ⟨2270384, by rfl⟩ : syracuseStep 3027179 = 4540769) B4540769
theorem B10211741 : Blo 1792097 10211741 := bstep (se 3 (by rfl) ⟨1914701, by rfl⟩ : syracuseStep 10211741 = 3829403) B3829403
theorem B14545345 : Blo 1792097 14545345 := bstep (se 2 (by rfl) ⟨5454504, by rfl⟩ : syracuseStep 14545345 = 10909009) B10909009
theorem B29872799 : Blo 1792097 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B4035239 : Blo 1792097 4035239 := bstep (se 1 (by rfl) ⟨3026429, by rfl⟩ : syracuseStep 4035239 = 6052859) B6052859
theorem B17461979 : Blo 1792097 17461979 := bstep (se 1 (by rfl) ⟨13096484, by rfl⟩ : syracuseStep 17461979 = 26192969) B26192969
theorem B4846459 : Blo 1792097 4846459 := bstep (se 1 (by rfl) ⟨3634844, by rfl⟩ : syracuseStep 4846459 = 7269689) B7269689
theorem B9082043 : Blo 1792097 9082043 := bstep (se 1 (by rfl) ⟨6811532, by rfl⟩ : syracuseStep 9082043 = 13623065) B13623065
theorem B1792159 : Blo 1792097 1792159 := bstep (se 1 (by rfl) ⟨1344119, by rfl⟩ : syracuseStep 1792159 = 2688239) B2688239
theorem B19380989 : Blo 1792097 19380989 := bstep (se 3 (by rfl) ⟨3633935, by rfl⟩ : syracuseStep 19380989 = 7267871) B7267871
theorem B4537579 : Blo 1792097 4537579 := bstep (se 1 (by rfl) ⟨3403184, by rfl⟩ : syracuseStep 4537579 = 6806369) B6806369
theorem B6806825 : Blo 1792097 6806825 := bstep (se 2 (by rfl) ⟨2552559, by rfl⟩ : syracuseStep 6806825 = 5105119) B5105119
theorem B1794047 : Blo 1792097 1794047 := bstep (se 1 (by rfl) ⟨1345535, by rfl⟩ : syracuseStep 1794047 = 2691071) B2691071
theorem B1794079 : Blo 1792097 1794079 := bstep (se 1 (by rfl) ⟨1345559, by rfl⟩ : syracuseStep 1794079 = 2691119) B2691119
theorem B12271763 : Blo 1792097 12271763 := bstep (se 1 (by rfl) ⟨9203822, by rfl⟩ : syracuseStep 12271763 = 18407645) B18407645
theorem B6807827 : Blo 1792097 6807827 := bstep (se 1 (by rfl) ⟨5105870, by rfl⟩ : syracuseStep 6807827 = 10211741) B10211741
theorem B36798857 : Blo 1792097 36798857 := bstep (se 2 (by rfl) ⟨13799571, by rfl⟩ : syracuseStep 36798857 = 27599143) B27599143
theorem B19915199 : Blo 1792097 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B11641319 : Blo 1792097 11641319 := bstep (se 1 (by rfl) ⟨8730989, by rfl⟩ : syracuseStep 11641319 = 17461979) B17461979
theorem B13615775 : Blo 1792097 13615775 := bstep (se 1 (by rfl) ⟨10211831, by rfl⟩ : syracuseStep 13615775 = 20423663) B20423663
theorem B6054695 : Blo 1792097 6054695 := bstep (se 1 (by rfl) ⟨4541021, by rfl⟩ : syracuseStep 6054695 = 9082043) B9082043
theorem B25855159 : Blo 1792097 25855159 := bstep (se 1 (by rfl) ⟨19391369, by rfl⟩ : syracuseStep 25855159 = 38782739) B38782739
theorem B2688359 : Blo 1792097 2688359 := bstep (se 1 (by rfl) ⟨2016269, by rfl⟩ : syracuseStep 2688359 = 4032539) B4032539
theorem B2688491 : Blo 1792097 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B2689079 : Blo 1792097 2689079 := bstep (se 1 (by rfl) ⟨2016809, by rfl⟩ : syracuseStep 2689079 = 4033619) B4033619
theorem B2689487 : Blo 1792097 2689487 := bstep (se 1 (by rfl) ⟨2017115, by rfl⟩ : syracuseStep 2689487 = 4034231) B4034231
theorem B2018119 : Blo 1792097 2018119 := bstep (se 1 (by rfl) ⟨1513589, by rfl⟩ : syracuseStep 2018119 = 3027179) B3027179
theorem B20433869 : Blo 1792097 20433869 := bstep (se 3 (by rfl) ⟨3831350, by rfl⟩ : syracuseStep 20433869 = 7662701) B7662701
theorem B3026011 : Blo 1792097 3026011 := bstep (se 1 (by rfl) ⟨2269508, by rfl⟩ : syracuseStep 3026011 = 4539017) B4539017
theorem B2690159 : Blo 1792097 2690159 := bstep (se 1 (by rfl) ⟨2017619, by rfl⟩ : syracuseStep 2690159 = 4035239) B4035239
theorem B19393793 : Blo 1792097 19393793 := bstep (se 2 (by rfl) ⟨7272672, by rfl⟩ : syracuseStep 19393793 = 14545345) B14545345
theorem B2690537 : Blo 1792097 2690537 := bstep (se 2 (by rfl) ⟨1008951, by rfl⟩ : syracuseStep 2690537 = 2017903) B2017903
theorem B20426579 : Blo 1792097 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B2691113 : Blo 1792097 2691113 := bstep (se 2 (by rfl) ⟨1009167, by rfl⟩ : syracuseStep 2691113 = 2018335) B2018335
theorem B2912303 : Blo 1792097 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B6050105 : Blo 1792097 6050105 := bstep (se 2 (by rfl) ⟨2268789, by rfl⟩ : syracuseStep 6050105 = 4537579) B4537579
theorem B39285215 : Blo 1792097 39285215 := bstep (se 1 (by rfl) ⟨29463911, by rfl⟩ : syracuseStep 39285215 = 58927823) B58927823
theorem B15315803 : Blo 1792097 15315803 := bstep (se 1 (by rfl) ⟨11486852, by rfl⟩ : syracuseStep 15315803 = 22973705) B22973705
theorem B9074429 : Blo 1792097 9074429 := bstep (se 3 (by rfl) ⟨1701455, by rfl⟩ : syracuseStep 9074429 = 3402911) B3402911
theorem B1792207 : Blo 1792097 1792207 := bstep (se 1 (by rfl) ⟨1344155, by rfl⟩ : syracuseStep 1792207 = 2688311) B2688311
theorem B6461945 : Blo 1792097 6461945 := bstep (se 2 (by rfl) ⟨2423229, by rfl⟩ : syracuseStep 6461945 = 4846459) B4846459
theorem B51682637 : Blo 1792097 51682637 := bstep (se 3 (by rfl) ⟨9690494, by rfl⟩ : syracuseStep 51682637 = 19380989) B19380989
theorem B33611183 : Blo 1792097 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B4537883 : Blo 1792097 4537883 := bstep (se 1 (by rfl) ⟨3403412, by rfl⟩ : syracuseStep 4537883 = 6806825) B6806825
theorem B1794075 : Blo 1792097 1794075 := bstep (se 1 (by rfl) ⟨1345556, by rfl⟩ : syracuseStep 1794075 = 2691113) B2691113
theorem B1941535 : Blo 1792097 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B4538551 : Blo 1792097 4538551 := bstep (se 1 (by rfl) ⟨3403913, by rfl⟩ : syracuseStep 4538551 = 6807827) B6807827
theorem B26190143 : Blo 1792097 26190143 := bstep (se 1 (by rfl) ⟨19642607, by rfl⟩ : syracuseStep 26190143 = 39285215) B39285215
theorem B9077183 : Blo 1792097 9077183 := bstep (se 1 (by rfl) ⟨6807887, by rfl⟩ : syracuseStep 9077183 = 13615775) B13615775
theorem B34473545 : Blo 1792097 34473545 := bstep (se 2 (by rfl) ⟨12927579, by rfl⟩ : syracuseStep 34473545 = 25855159) B25855159
theorem B12929195 : Blo 1792097 12929195 := bstep (se 1 (by rfl) ⟨9696896, by rfl⟩ : syracuseStep 12929195 = 19393793) B19393793
theorem B22407455 : Blo 1792097 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B3025255 : Blo 1792097 3025255 := bstep (se 1 (by rfl) ⟨2268941, by rfl⟩ : syracuseStep 3025255 = 4537883) B4537883
theorem B13617719 : Blo 1792097 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B4033403 : Blo 1792097 4033403 := bstep (se 1 (by rfl) ⟨3025052, by rfl⟩ : syracuseStep 4033403 = 6050105) B6050105
theorem B7760879 : Blo 1792097 7760879 := bstep (se 1 (by rfl) ⟨5820659, by rfl⟩ : syracuseStep 7760879 = 11641319) B11641319
theorem B10210535 : Blo 1792097 10210535 := bstep (se 1 (by rfl) ⟨7657901, by rfl⟩ : syracuseStep 10210535 = 15315803) B15315803
theorem B2690825 : Blo 1792097 2690825 := bstep (se 2 (by rfl) ⟨1009059, by rfl⟩ : syracuseStep 2690825 = 2018119) B2018119
theorem B6049619 : Blo 1792097 6049619 := bstep (se 1 (by rfl) ⟨4537214, by rfl⟩ : syracuseStep 6049619 = 9074429) B9074429
theorem B4034681 : Blo 1792097 4034681 := bstep (se 2 (by rfl) ⟨1513005, by rfl⟩ : syracuseStep 4034681 = 3026011) B3026011
theorem B8181175 : Blo 1792097 8181175 := bstep (se 1 (by rfl) ⟨6135881, by rfl⟩ : syracuseStep 8181175 = 12271763) B12271763
theorem B24532571 : Blo 1792097 24532571 := bstep (se 1 (by rfl) ⟨18399428, by rfl⟩ : syracuseStep 24532571 = 36798857) B36798857
theorem B13276799 : Blo 1792097 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B4036463 : Blo 1792097 4036463 := bstep (se 1 (by rfl) ⟨3027347, by rfl⟩ : syracuseStep 4036463 = 6054695) B6054695
theorem B1792239 : Blo 1792097 1792239 := bstep (se 1 (by rfl) ⟨1344179, by rfl⟩ : syracuseStep 1792239 = 2688359) B2688359
theorem B1792327 : Blo 1792097 1792327 := bstep (se 1 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 1792327 = 2688491) B2688491
theorem B1792719 : Blo 1792097 1792719 := bstep (se 1 (by rfl) ⟨1344539, by rfl⟩ : syracuseStep 1792719 = 2689079) B2689079
theorem B1792991 : Blo 1792097 1792991 := bstep (se 1 (by rfl) ⟨1344743, by rfl⟩ : syracuseStep 1792991 = 2689487) B2689487
theorem B4307963 : Blo 1792097 4307963 := bstep (se 1 (by rfl) ⟨3230972, by rfl⟩ : syracuseStep 4307963 = 6461945) B6461945
theorem B13622579 : Blo 1792097 13622579 := bstep (se 1 (by rfl) ⟨10216934, by rfl⟩ : syracuseStep 13622579 = 20433869) B20433869
theorem B1793439 : Blo 1792097 1793439 := bstep (se 1 (by rfl) ⟨1345079, by rfl⟩ : syracuseStep 1793439 = 2690159) B2690159
theorem B34455091 : Blo 1792097 34455091 := bstep (se 1 (by rfl) ⟨25841318, by rfl⟩ : syracuseStep 34455091 = 51682637) B51682637
theorem B1793691 : Blo 1792097 1793691 := bstep (se 1 (by rfl) ⟨1345268, by rfl⟩ : syracuseStep 1793691 = 2690537) B2690537
theorem B10354853 : Blo 1792097 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B59753213 : Blo 1792097 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B8619463 : Blo 1792097 8619463 := bstep (se 1 (by rfl) ⟨6464597, by rfl⟩ : syracuseStep 8619463 = 12929195) B12929195
theorem B9078479 : Blo 1792097 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B2688935 : Blo 1792097 2688935 := bstep (se 1 (by rfl) ⟨2016701, by rfl⟩ : syracuseStep 2688935 = 4033403) B4033403
theorem B4033079 : Blo 1792097 4033079 := bstep (se 1 (by rfl) ⟨3024809, by rfl⟩ : syracuseStep 4033079 = 6049619) B6049619
theorem B11487901 : Blo 1792097 11487901 := bstep (se 3 (by rfl) ⟨2153981, by rfl⟩ : syracuseStep 11487901 = 4307963) B4307963
theorem B2689787 : Blo 1792097 2689787 := bstep (se 1 (by rfl) ⟨2017340, by rfl⟩ : syracuseStep 2689787 = 4034681) B4034681
theorem B17460095 : Blo 1792097 17460095 := bstep (se 1 (by rfl) ⟨13095071, by rfl⟩ : syracuseStep 17460095 = 26190143) B26190143
theorem B4033673 : Blo 1792097 4033673 := bstep (se 2 (by rfl) ⟨1512627, by rfl⟩ : syracuseStep 4033673 = 3025255) B3025255
theorem B22982363 : Blo 1792097 22982363 := bstep (se 1 (by rfl) ⟨17236772, by rfl⟩ : syracuseStep 22982363 = 34473545) B34473545
theorem B16355047 : Blo 1792097 16355047 := bstep (se 1 (by rfl) ⟨12266285, by rfl⟩ : syracuseStep 16355047 = 24532571) B24532571
theorem B8851199 : Blo 1792097 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B2690975 : Blo 1792097 2690975 := bstep (se 1 (by rfl) ⟨2018231, by rfl⟩ : syracuseStep 2690975 = 4036463) B4036463
theorem B10908233 : Blo 1792097 10908233 := bstep (se 2 (by rfl) ⟨4090587, by rfl⟩ : syracuseStep 10908233 = 8181175) B8181175
theorem B5173919 : Blo 1792097 5173919 := bstep (se 1 (by rfl) ⟨3880439, by rfl⟩ : syracuseStep 5173919 = 7760879) B7760879
theorem B9081719 : Blo 1792097 9081719 := bstep (se 1 (by rfl) ⟨6811289, by rfl⟩ : syracuseStep 9081719 = 13622579) B13622579
theorem B6051401 : Blo 1792097 6051401 := bstep (se 2 (by rfl) ⟨2269275, by rfl⟩ : syracuseStep 6051401 = 4538551) B4538551
theorem B6051455 : Blo 1792097 6051455 := bstep (se 1 (by rfl) ⟨4538591, by rfl⟩ : syracuseStep 6051455 = 9077183) B9077183
theorem B45940121 : Blo 1792097 45940121 := bstep (se 2 (by rfl) ⟨17227545, by rfl⟩ : syracuseStep 45940121 = 34455091) B34455091
theorem B6807023 : Blo 1792097 6807023 := bstep (se 1 (by rfl) ⟨5105267, by rfl⟩ : syracuseStep 6807023 = 10210535) B10210535
theorem B1793883 : Blo 1792097 1793883 := bstep (se 1 (by rfl) ⟨1345412, by rfl⟩ : syracuseStep 1793883 = 2690825) B2690825
theorem B3449279 : Blo 1792097 3449279 := bstep (se 1 (by rfl) ⟨2586959, by rfl⟩ : syracuseStep 3449279 = 5173919) B5173919
theorem B6054479 : Blo 1792097 6054479 := bstep (se 1 (by rfl) ⟨4540859, by rfl⟩ : syracuseStep 6054479 = 9081719) B9081719
theorem B2688719 : Blo 1792097 2688719 := bstep (se 1 (by rfl) ⟨2016539, by rfl⟩ : syracuseStep 2688719 = 4033079) B4033079
theorem B2689115 : Blo 1792097 2689115 := bstep (se 1 (by rfl) ⟨2016836, by rfl⟩ : syracuseStep 2689115 = 4033673) B4033673
theorem B15321575 : Blo 1792097 15321575 := bstep (se 1 (by rfl) ⟨11491181, by rfl⟩ : syracuseStep 15321575 = 22982363) B22982363
theorem B4034267 : Blo 1792097 4034267 := bstep (se 1 (by rfl) ⟨3025700, by rfl⟩ : syracuseStep 4034267 = 6051401) B6051401
theorem B4034303 : Blo 1792097 4034303 := bstep (se 1 (by rfl) ⟨3025727, by rfl⟩ : syracuseStep 4034303 = 6051455) B6051455
theorem B30626747 : Blo 1792097 30626747 := bstep (se 1 (by rfl) ⟨22970060, by rfl⟩ : syracuseStep 30626747 = 45940121) B45940121
theorem B46560253 : Blo 1792097 46560253 := bstep (se 3 (by rfl) ⟨8730047, by rfl⟩ : syracuseStep 46560253 = 17460095) B17460095
theorem B6903235 : Blo 1792097 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B7272155 : Blo 1792097 7272155 := bstep (se 1 (by rfl) ⟨5454116, by rfl⟩ : syracuseStep 7272155 = 10908233) B10908233
theorem B39835475 : Blo 1792097 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B15317201 : Blo 1792097 15317201 := bstep (se 2 (by rfl) ⟨5743950, by rfl⟩ : syracuseStep 15317201 = 11487901) B11487901
theorem B6052319 : Blo 1792097 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B1792623 : Blo 1792097 1792623 := bstep (se 1 (by rfl) ⟨1344467, by rfl⟩ : syracuseStep 1792623 = 2688935) B2688935
theorem B1793191 : Blo 1792097 1793191 := bstep (se 1 (by rfl) ⟨1344893, by rfl⟩ : syracuseStep 1793191 = 2689787) B2689787
theorem B11492617 : Blo 1792097 11492617 := bstep (se 2 (by rfl) ⟨4309731, by rfl⟩ : syracuseStep 11492617 = 8619463) B8619463
theorem B21806729 : Blo 1792097 21806729 := bstep (se 2 (by rfl) ⟨8177523, by rfl⟩ : syracuseStep 21806729 = 16355047) B16355047
theorem B4538015 : Blo 1792097 4538015 := bstep (se 1 (by rfl) ⟨3403511, by rfl⟩ : syracuseStep 4538015 = 6807023) B6807023
theorem B1793983 : Blo 1792097 1793983 := bstep (se 1 (by rfl) ⟨1345487, by rfl⟩ : syracuseStep 1793983 = 2690975) B2690975
theorem B94412789 : Blo 1792097 94412789 := bstep (se 5 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 94412789 = 8851199) B8851199
theorem B62080337 : Blo 1792097 62080337 := bstep (se 2 (by rfl) ⟨23280126, by rfl⟩ : syracuseStep 62080337 = 46560253) B46560253
theorem B3025343 : Blo 1792097 3025343 := bstep (se 1 (by rfl) ⟨2269007, by rfl⟩ : syracuseStep 3025343 = 4538015) B4538015
theorem B2689511 : Blo 1792097 2689511 := bstep (se 1 (by rfl) ⟨2017133, by rfl⟩ : syracuseStep 2689511 = 4034267) B4034267
theorem B2689535 : Blo 1792097 2689535 := bstep (se 1 (by rfl) ⟨2017151, by rfl⟩ : syracuseStep 2689535 = 4034303) B4034303
theorem B62941859 : Blo 1792097 62941859 := bstep (se 1 (by rfl) ⟨47206394, by rfl⟩ : syracuseStep 62941859 = 94412789) B94412789
theorem B20417831 : Blo 1792097 20417831 := bstep (se 1 (by rfl) ⟨15313373, by rfl⟩ : syracuseStep 20417831 = 30626747) B30626747
theorem B10211467 : Blo 1792097 10211467 := bstep (se 1 (by rfl) ⟨7658600, by rfl⟩ : syracuseStep 10211467 = 15317201) B15317201
theorem B4034879 : Blo 1792097 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B15323489 : Blo 1792097 15323489 := bstep (se 2 (by rfl) ⟨5746308, by rfl⟩ : syracuseStep 15323489 = 11492617) B11492617
theorem B9204313 : Blo 1792097 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B14537819 : Blo 1792097 14537819 := bstep (se 1 (by rfl) ⟨10903364, by rfl⟩ : syracuseStep 14537819 = 21806729) B21806729
theorem B2299519 : Blo 1792097 2299519 := bstep (se 1 (by rfl) ⟨1724639, by rfl⟩ : syracuseStep 2299519 = 3449279) B3449279
theorem B4036319 : Blo 1792097 4036319 := bstep (se 1 (by rfl) ⟨3027239, by rfl⟩ : syracuseStep 4036319 = 6054479) B6054479
theorem B1792479 : Blo 1792097 1792479 := bstep (se 1 (by rfl) ⟨1344359, by rfl⟩ : syracuseStep 1792479 = 2688719) B2688719
theorem B4848103 : Blo 1792097 4848103 := bstep (se 1 (by rfl) ⟨3636077, by rfl⟩ : syracuseStep 4848103 = 7272155) B7272155
theorem B26556983 : Blo 1792097 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B1792743 : Blo 1792097 1792743 := bstep (se 1 (by rfl) ⟨1344557, by rfl⟩ : syracuseStep 1792743 = 2689115) B2689115
theorem B10214383 : Blo 1792097 10214383 := bstep (se 1 (by rfl) ⟨7660787, by rfl⟩ : syracuseStep 10214383 = 15321575) B15321575
theorem B13615289 : Blo 1792097 13615289 := bstep (se 2 (by rfl) ⟨5105733, by rfl⟩ : syracuseStep 13615289 = 10211467) B10211467
theorem B10215659 : Blo 1792097 10215659 := bstep (se 1 (by rfl) ⟨7661744, by rfl⟩ : syracuseStep 10215659 = 15323489) B15323489
theorem B6464137 : Blo 1792097 6464137 := bstep (se 2 (by rfl) ⟨2424051, by rfl⟩ : syracuseStep 6464137 = 4848103) B4848103
theorem B9691879 : Blo 1792097 9691879 := bstep (se 1 (by rfl) ⟨7268909, by rfl⟩ : syracuseStep 9691879 = 14537819) B14537819
theorem B12272417 : Blo 1792097 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B41386891 : Blo 1792097 41386891 := bstep (se 1 (by rfl) ⟨31040168, by rfl⟩ : syracuseStep 41386891 = 62080337) B62080337
theorem B2016895 : Blo 1792097 2016895 := bstep (se 1 (by rfl) ⟨1512671, by rfl⟩ : syracuseStep 2016895 = 3025343) B3025343
theorem B17704655 : Blo 1792097 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B41961239 : Blo 1792097 41961239 := bstep (se 1 (by rfl) ⟨31470929, by rfl⟩ : syracuseStep 41961239 = 62941859) B62941859
theorem B3066025 : Blo 1792097 3066025 := bstep (se 2 (by rfl) ⟨1149759, by rfl⟩ : syracuseStep 3066025 = 2299519) B2299519
theorem B2689919 : Blo 1792097 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B2690879 : Blo 1792097 2690879 := bstep (se 1 (by rfl) ⟨2018159, by rfl⟩ : syracuseStep 2690879 = 4036319) B4036319
theorem B13619177 : Blo 1792097 13619177 := bstep (se 2 (by rfl) ⟨5107191, by rfl⟩ : syracuseStep 13619177 = 10214383) B10214383
theorem B13611887 : Blo 1792097 13611887 := bstep (se 1 (by rfl) ⟨10208915, by rfl⟩ : syracuseStep 13611887 = 20417831) B20417831
theorem B1793007 : Blo 1792097 1793007 := bstep (se 1 (by rfl) ⟨1344755, by rfl⟩ : syracuseStep 1793007 = 2689511) B2689511
theorem B1793023 : Blo 1792097 1793023 := bstep (se 1 (by rfl) ⟨1344767, by rfl⟩ : syracuseStep 1793023 = 2689535) B2689535
theorem B9076859 : Blo 1792097 9076859 := bstep (se 1 (by rfl) ⟨6807644, by rfl⟩ : syracuseStep 9076859 = 13615289) B13615289
theorem B4088033 : Blo 1792097 4088033 := bstep (se 2 (by rfl) ⟨1533012, by rfl⟩ : syracuseStep 4088033 = 3066025) B3066025
theorem B8618849 : Blo 1792097 8618849 := bstep (se 2 (by rfl) ⟨3232068, by rfl⟩ : syracuseStep 8618849 = 6464137) B6464137
theorem B55182521 : Blo 1792097 55182521 := bstep (se 2 (by rfl) ⟨20693445, by rfl⟩ : syracuseStep 55182521 = 41386891) B41386891
theorem B2689193 : Blo 1792097 2689193 := bstep (se 2 (by rfl) ⟨1008447, by rfl⟩ : syracuseStep 2689193 = 2016895) B2016895
theorem B9079451 : Blo 1792097 9079451 := bstep (se 1 (by rfl) ⟨6809588, by rfl⟩ : syracuseStep 9079451 = 13619177) B13619177
theorem B6810439 : Blo 1792097 6810439 := bstep (se 1 (by rfl) ⟨5107829, by rfl⟩ : syracuseStep 6810439 = 10215659) B10215659
theorem B12922505 : Blo 1792097 12922505 := bstep (se 2 (by rfl) ⟨4845939, by rfl⟩ : syracuseStep 12922505 = 9691879) B9691879
theorem B8181611 : Blo 1792097 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B9074591 : Blo 1792097 9074591 := bstep (se 1 (by rfl) ⟨6805943, by rfl⟩ : syracuseStep 9074591 = 13611887) B13611887
theorem B11803103 : Blo 1792097 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B27974159 : Blo 1792097 27974159 := bstep (se 1 (by rfl) ⟨20980619, by rfl⟩ : syracuseStep 27974159 = 41961239) B41961239
theorem B1793279 : Blo 1792097 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B1793919 : Blo 1792097 1793919 := bstep (se 1 (by rfl) ⟨1345439, by rfl⟩ : syracuseStep 1793919 = 2690879) B2690879
theorem B5745899 : Blo 1792097 5745899 := bstep (se 1 (by rfl) ⟨4309424, by rfl⟩ : syracuseStep 5745899 = 8618849) B8618849
theorem B9080585 : Blo 1792097 9080585 := bstep (se 2 (by rfl) ⟨3405219, by rfl⟩ : syracuseStep 9080585 = 6810439) B6810439
theorem B6049727 : Blo 1792097 6049727 := bstep (se 1 (by rfl) ⟨4537295, by rfl⟩ : syracuseStep 6049727 = 9074591) B9074591
theorem B7868735 : Blo 1792097 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B18649439 : Blo 1792097 18649439 := bstep (se 1 (by rfl) ⟨13987079, by rfl⟩ : syracuseStep 18649439 = 27974159) B27974159
theorem B8615003 : Blo 1792097 8615003 := bstep (se 1 (by rfl) ⟨6461252, by rfl⟩ : syracuseStep 8615003 = 12922505) B12922505
theorem B6051239 : Blo 1792097 6051239 := bstep (se 1 (by rfl) ⟨4538429, by rfl⟩ : syracuseStep 6051239 = 9076859) B9076859
theorem B2725355 : Blo 1792097 2725355 := bstep (se 1 (by rfl) ⟨2044016, by rfl⟩ : syracuseStep 2725355 = 4088033) B4088033
theorem B36788347 : Blo 1792097 36788347 := bstep (se 1 (by rfl) ⟨27591260, by rfl⟩ : syracuseStep 36788347 = 55182521) B55182521
theorem B5454407 : Blo 1792097 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B1792795 : Blo 1792097 1792795 := bstep (se 1 (by rfl) ⟨1344596, by rfl⟩ : syracuseStep 1792795 = 2689193) B2689193
theorem B6052967 : Blo 1792097 6052967 := bstep (se 1 (by rfl) ⟨4539725, by rfl⟩ : syracuseStep 6052967 = 9079451) B9079451
theorem B4033151 : Blo 1792097 4033151 := bstep (se 1 (by rfl) ⟨3024863, by rfl⟩ : syracuseStep 4033151 = 6049727) B6049727
theorem B5245823 : Blo 1792097 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B22973341 : Blo 1792097 22973341 := bstep (se 3 (by rfl) ⟨4307501, by rfl⟩ : syracuseStep 22973341 = 8615003) B8615003
theorem B4034159 : Blo 1792097 4034159 := bstep (se 1 (by rfl) ⟨3025619, by rfl⟩ : syracuseStep 4034159 = 6051239) B6051239
theorem B4035311 : Blo 1792097 4035311 := bstep (se 1 (by rfl) ⟨3026483, by rfl⟩ : syracuseStep 4035311 = 6052967) B6052967
theorem B3830599 : Blo 1792097 3830599 := bstep (se 1 (by rfl) ⟨2872949, by rfl⟩ : syracuseStep 3830599 = 5745899) B5745899
theorem B49051129 : Blo 1792097 49051129 := bstep (se 2 (by rfl) ⟨18394173, by rfl⟩ : syracuseStep 49051129 = 36788347) B36788347
theorem B12432959 : Blo 1792097 12432959 := bstep (se 1 (by rfl) ⟨9324719, by rfl⟩ : syracuseStep 12432959 = 18649439) B18649439
theorem B1816903 : Blo 1792097 1816903 := bstep (se 1 (by rfl) ⟨1362677, by rfl⟩ : syracuseStep 1816903 = 2725355) B2725355
theorem B3636271 : Blo 1792097 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B6053723 : Blo 1792097 6053723 := bstep (se 1 (by rfl) ⟨4540292, by rfl⟩ : syracuseStep 6053723 = 9080585) B9080585
theorem B30631121 : Blo 1792097 30631121 := bstep (se 2 (by rfl) ⟨11486670, by rfl⟩ : syracuseStep 30631121 = 22973341) B22973341
theorem B2688767 : Blo 1792097 2688767 := bstep (se 1 (by rfl) ⟨2016575, by rfl⟩ : syracuseStep 2688767 = 4033151) B4033151
theorem B2689439 : Blo 1792097 2689439 := bstep (se 1 (by rfl) ⟨2017079, by rfl⟩ : syracuseStep 2689439 = 4034159) B4034159
theorem B19393445 : Blo 1792097 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B2690207 : Blo 1792097 2690207 := bstep (se 1 (by rfl) ⟨2017655, by rfl⟩ : syracuseStep 2690207 = 4035311) B4035311
theorem B5107465 : Blo 1792097 5107465 := bstep (se 2 (by rfl) ⟨1915299, by rfl⟩ : syracuseStep 5107465 = 3830599) B3830599
theorem B65401505 : Blo 1792097 65401505 := bstep (se 2 (by rfl) ⟨24525564, by rfl⟩ : syracuseStep 65401505 = 49051129) B49051129
theorem B4035815 : Blo 1792097 4035815 := bstep (se 1 (by rfl) ⟨3026861, by rfl⟩ : syracuseStep 4035815 = 6053723) B6053723
theorem B8288639 : Blo 1792097 8288639 := bstep (se 1 (by rfl) ⟨6216479, by rfl⟩ : syracuseStep 8288639 = 12432959) B12432959
theorem B9690149 : Blo 1792097 9690149 := bstep (se 4 (by rfl) ⟨908451, by rfl⟩ : syracuseStep 9690149 = 1816903) B1816903
theorem B3497215 : Blo 1792097 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B4662953 : Blo 1792097 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B6809953 : Blo 1792097 6809953 := bstep (se 2 (by rfl) ⟨2553732, by rfl⟩ : syracuseStep 6809953 = 5107465) B5107465
theorem B25840397 : Blo 1792097 25840397 := bstep (se 3 (by rfl) ⟨4845074, by rfl⟩ : syracuseStep 25840397 = 9690149) B9690149
theorem B43601003 : Blo 1792097 43601003 := bstep (se 1 (by rfl) ⟨32700752, by rfl⟩ : syracuseStep 43601003 = 65401505) B65401505
theorem B2690543 : Blo 1792097 2690543 := bstep (se 1 (by rfl) ⟨2017907, by rfl⟩ : syracuseStep 2690543 = 4035815) B4035815
theorem B5525759 : Blo 1792097 5525759 := bstep (se 1 (by rfl) ⟨4144319, by rfl⟩ : syracuseStep 5525759 = 8288639) B8288639
theorem B20420747 : Blo 1792097 20420747 := bstep (se 1 (by rfl) ⟨15315560, by rfl⟩ : syracuseStep 20420747 = 30631121) B30631121
theorem B1792511 : Blo 1792097 1792511 := bstep (se 1 (by rfl) ⟨1344383, by rfl⟩ : syracuseStep 1792511 = 2688767) B2688767
theorem B1792959 : Blo 1792097 1792959 := bstep (se 1 (by rfl) ⟨1344719, by rfl⟩ : syracuseStep 1792959 = 2689439) B2689439
theorem B1793471 : Blo 1792097 1793471 := bstep (se 1 (by rfl) ⟨1345103, by rfl⟩ : syracuseStep 1793471 = 2690207) B2690207
theorem B51715853 : Blo 1792097 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B29067335 : Blo 1792097 29067335 := bstep (se 1 (by rfl) ⟨21800501, by rfl⟩ : syracuseStep 29067335 = 43601003) B43601003
theorem B9079937 : Blo 1792097 9079937 := bstep (se 2 (by rfl) ⟨3404976, by rfl⟩ : syracuseStep 9079937 = 6809953) B6809953
theorem B3108635 : Blo 1792097 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B34477235 : Blo 1792097 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B3683839 : Blo 1792097 3683839 := bstep (se 1 (by rfl) ⟨2762879, by rfl⟩ : syracuseStep 3683839 = 5525759) B5525759
theorem B13613831 : Blo 1792097 13613831 := bstep (se 1 (by rfl) ⟨10210373, by rfl⟩ : syracuseStep 13613831 = 20420747) B20420747
theorem B17226931 : Blo 1792097 17226931 := bstep (se 1 (by rfl) ⟨12920198, by rfl⟩ : syracuseStep 17226931 = 25840397) B25840397
theorem B1793695 : Blo 1792097 1793695 := bstep (se 1 (by rfl) ⟨1345271, by rfl⟩ : syracuseStep 1793695 = 2690543) B2690543
theorem B19378223 : Blo 1792097 19378223 := bstep (se 1 (by rfl) ⟨14533667, by rfl⟩ : syracuseStep 19378223 = 29067335) B29067335
theorem B4911785 : Blo 1792097 4911785 := bstep (se 2 (by rfl) ⟨1841919, by rfl⟩ : syracuseStep 4911785 = 3683839) B3683839
theorem B22984823 : Blo 1792097 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B22969241 : Blo 1792097 22969241 := bstep (se 2 (by rfl) ⟨8613465, by rfl⟩ : syracuseStep 22969241 = 17226931) B17226931
theorem B9075887 : Blo 1792097 9075887 := bstep (se 1 (by rfl) ⟨6806915, by rfl⟩ : syracuseStep 9075887 = 13613831) B13613831
theorem B6053291 : Blo 1792097 6053291 := bstep (se 1 (by rfl) ⟨4539968, by rfl⟩ : syracuseStep 6053291 = 9079937) B9079937
theorem B2072423 : Blo 1792097 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B12918815 : Blo 1792097 12918815 := bstep (se 1 (by rfl) ⟨9689111, by rfl⟩ : syracuseStep 12918815 = 19378223) B19378223
theorem B15312827 : Blo 1792097 15312827 := bstep (se 1 (by rfl) ⟨11484620, by rfl⟩ : syracuseStep 15312827 = 22969241) B22969241
theorem B15323215 : Blo 1792097 15323215 := bstep (se 1 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 15323215 = 22984823) B22984823
theorem B6050591 : Blo 1792097 6050591 := bstep (se 1 (by rfl) ⟨4537943, by rfl⟩ : syracuseStep 6050591 = 9075887) B9075887
theorem B5526461 : Blo 1792097 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B4035527 : Blo 1792097 4035527 := bstep (se 1 (by rfl) ⟨3026645, by rfl⟩ : syracuseStep 4035527 = 6053291) B6053291
theorem B3274523 : Blo 1792097 3274523 := bstep (se 1 (by rfl) ⟨2455892, by rfl⟩ : syracuseStep 3274523 = 4911785) B4911785
theorem B20430953 : Blo 1792097 20430953 := bstep (se 2 (by rfl) ⟨7661607, by rfl⟩ : syracuseStep 20430953 = 15323215) B15323215
theorem B10208551 : Blo 1792097 10208551 := bstep (se 1 (by rfl) ⟨7656413, by rfl⟩ : syracuseStep 10208551 = 15312827) B15312827
theorem B8612543 : Blo 1792097 8612543 := bstep (se 1 (by rfl) ⟨6459407, by rfl⟩ : syracuseStep 8612543 = 12918815) B12918815
theorem B4033727 : Blo 1792097 4033727 := bstep (se 1 (by rfl) ⟨3025295, by rfl⟩ : syracuseStep 4033727 = 6050591) B6050591
theorem B2690351 : Blo 1792097 2690351 := bstep (se 1 (by rfl) ⟨2017763, by rfl⟩ : syracuseStep 2690351 = 4035527) B4035527
theorem B2183015 : Blo 1792097 2183015 := bstep (se 1 (by rfl) ⟨1637261, by rfl⟩ : syracuseStep 2183015 = 3274523) B3274523
theorem B3684307 : Blo 1792097 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B2689151 : Blo 1792097 2689151 := bstep (se 1 (by rfl) ⟨2016863, by rfl⟩ : syracuseStep 2689151 = 4033727) B4033727
theorem B13611401 : Blo 1792097 13611401 := bstep (se 2 (by rfl) ⟨5104275, by rfl⟩ : syracuseStep 13611401 = 10208551) B10208551
theorem B5821373 : Blo 1792097 5821373 := bstep (se 3 (by rfl) ⟨1091507, by rfl⟩ : syracuseStep 5821373 = 2183015) B2183015
theorem B4912409 : Blo 1792097 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B13620635 : Blo 1792097 13620635 := bstep (se 1 (by rfl) ⟨10215476, by rfl⟩ : syracuseStep 13620635 = 20430953) B20430953
theorem B5741695 : Blo 1792097 5741695 := bstep (se 1 (by rfl) ⟨4306271, by rfl⟩ : syracuseStep 5741695 = 8612543) B8612543
theorem B1793567 : Blo 1792097 1793567 := bstep (se 1 (by rfl) ⟨1345175, by rfl⟩ : syracuseStep 1793567 = 2690351) B2690351
theorem B30622373 : Blo 1792097 30622373 := bstep (se 4 (by rfl) ⟨2870847, by rfl⟩ : syracuseStep 30622373 = 5741695) B5741695
theorem B9080423 : Blo 1792097 9080423 := bstep (se 1 (by rfl) ⟨6810317, by rfl⟩ : syracuseStep 9080423 = 13620635) B13620635
theorem B9074267 : Blo 1792097 9074267 := bstep (se 1 (by rfl) ⟨6805700, by rfl⟩ : syracuseStep 9074267 = 13611401) B13611401
theorem B3880915 : Blo 1792097 3880915 := bstep (se 1 (by rfl) ⟨2910686, by rfl⟩ : syracuseStep 3880915 = 5821373) B5821373
theorem B3274939 : Blo 1792097 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B1792767 : Blo 1792097 1792767 := bstep (se 1 (by rfl) ⟨1344575, by rfl⟩ : syracuseStep 1792767 = 2689151) B2689151
theorem B4366585 : Blo 1792097 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B20414915 : Blo 1792097 20414915 := bstep (se 1 (by rfl) ⟨15311186, by rfl⟩ : syracuseStep 20414915 = 30622373) B30622373
theorem B6049511 : Blo 1792097 6049511 := bstep (se 1 (by rfl) ⟨4537133, by rfl⟩ : syracuseStep 6049511 = 9074267) B9074267
theorem B20698213 : Blo 1792097 20698213 := bstep (se 4 (by rfl) ⟨1940457, by rfl⟩ : syracuseStep 20698213 = 3880915) B3880915
theorem B6053615 : Blo 1792097 6053615 := bstep (se 1 (by rfl) ⟨4540211, by rfl⟩ : syracuseStep 6053615 = 9080423) B9080423
theorem B4033007 : Blo 1792097 4033007 := bstep (se 1 (by rfl) ⟨3024755, by rfl⟩ : syracuseStep 4033007 = 6049511) B6049511
theorem B13609943 : Blo 1792097 13609943 := bstep (se 1 (by rfl) ⟨10207457, by rfl⟩ : syracuseStep 13609943 = 20414915) B20414915
theorem B4035743 : Blo 1792097 4035743 := bstep (se 1 (by rfl) ⟨3026807, by rfl⟩ : syracuseStep 4035743 = 6053615) B6053615
theorem B5822113 : Blo 1792097 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B27597617 : Blo 1792097 27597617 := bstep (se 2 (by rfl) ⟨10349106, by rfl⟩ : syracuseStep 27597617 = 20698213) B20698213
theorem B2688671 : Blo 1792097 2688671 := bstep (se 1 (by rfl) ⟨2016503, by rfl⟩ : syracuseStep 2688671 = 4033007) B4033007
theorem B2690495 : Blo 1792097 2690495 := bstep (se 1 (by rfl) ⟨2017871, by rfl⟩ : syracuseStep 2690495 = 4035743) B4035743
theorem B9073295 : Blo 1792097 9073295 := bstep (se 1 (by rfl) ⟨6804971, by rfl⟩ : syracuseStep 9073295 = 13609943) B13609943
theorem B7762817 : Blo 1792097 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B18398411 : Blo 1792097 18398411 := bstep (se 1 (by rfl) ⟨13798808, by rfl⟩ : syracuseStep 18398411 = 27597617) B27597617
theorem B12265607 : Blo 1792097 12265607 := bstep (se 1 (by rfl) ⟨9199205, by rfl⟩ : syracuseStep 12265607 = 18398411) B18398411
theorem B6048863 : Blo 1792097 6048863 := bstep (se 1 (by rfl) ⟨4536647, by rfl⟩ : syracuseStep 6048863 = 9073295) B9073295
theorem B1792447 : Blo 1792097 1792447 := bstep (se 1 (by rfl) ⟨1344335, by rfl⟩ : syracuseStep 1792447 = 2688671) B2688671
theorem B1793663 : Blo 1792097 1793663 := bstep (se 1 (by rfl) ⟨1345247, by rfl⟩ : syracuseStep 1793663 = 2690495) B2690495
theorem B20700845 : Blo 1792097 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B8177071 : Blo 1792097 8177071 := bstep (se 1 (by rfl) ⟨6132803, by rfl⟩ : syracuseStep 8177071 = 12265607) B12265607
theorem B4032575 : Blo 1792097 4032575 := bstep (se 1 (by rfl) ⟨3024431, by rfl⟩ : syracuseStep 4032575 = 6048863) B6048863
theorem B13800563 : Blo 1792097 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B9200375 : Blo 1792097 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B2688383 : Blo 1792097 2688383 := bstep (se 1 (by rfl) ⟨2016287, by rfl⟩ : syracuseStep 2688383 = 4032575) B4032575
theorem B10902761 : Blo 1792097 10902761 := bstep (se 2 (by rfl) ⟨4088535, by rfl⟩ : syracuseStep 10902761 = 8177071) B8177071
theorem B7268507 : Blo 1792097 7268507 := bstep (se 1 (by rfl) ⟨5451380, by rfl⟩ : syracuseStep 7268507 = 10902761) B10902761
theorem B6133583 : Blo 1792097 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B1792255 : Blo 1792097 1792255 := bstep (se 1 (by rfl) ⟨1344191, by rfl⟩ : syracuseStep 1792255 = 2688383) B2688383
theorem B4089055 : Blo 1792097 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B4845671 : Blo 1792097 4845671 := bstep (se 1 (by rfl) ⟨3634253, by rfl⟩ : syracuseStep 4845671 = 7268507) B7268507
theorem B3230447 : Blo 1792097 3230447 := bstep (se 1 (by rfl) ⟨2422835, by rfl⟩ : syracuseStep 3230447 = 4845671) B4845671
theorem B5452073 : Blo 1792097 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B8614525 : Blo 1792097 8614525 := bstep (se 3 (by rfl) ⟨1615223, by rfl⟩ : syracuseStep 8614525 = 3230447) B3230447
theorem B3634715 : Blo 1792097 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B11486033 : Blo 1792097 11486033 := bstep (se 2 (by rfl) ⟨4307262, by rfl⟩ : syracuseStep 11486033 = 8614525) B8614525
theorem B2423143 : Blo 1792097 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B3230857 : Blo 1792097 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B7657355 : Blo 1792097 7657355 := bstep (se 1 (by rfl) ⟨5743016, by rfl⟩ : syracuseStep 7657355 = 11486033) B11486033
theorem B5104903 : Blo 1792097 5104903 := bstep (se 1 (by rfl) ⟨3828677, by rfl⟩ : syracuseStep 5104903 = 7657355) B7657355
theorem B17231237 : Blo 1792097 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B11487491 : Blo 1792097 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B6806537 : Blo 1792097 6806537 := bstep (se 2 (by rfl) ⟨2552451, by rfl⟩ : syracuseStep 6806537 = 5104903) B5104903
theorem B7658327 : Blo 1792097 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B4537691 : Blo 1792097 4537691 := bstep (se 1 (by rfl) ⟨3403268, by rfl⟩ : syracuseStep 4537691 = 6806537) B6806537
theorem B3025127 : Blo 1792097 3025127 := bstep (se 1 (by rfl) ⟨2268845, by rfl⟩ : syracuseStep 3025127 = 4537691) B4537691
theorem B20422205 : Blo 1792097 20422205 := bstep (se 3 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 20422205 = 7658327) B7658327
theorem B2016751 : Blo 1792097 2016751 := bstep (se 1 (by rfl) ⟨1512563, by rfl⟩ : syracuseStep 2016751 = 3025127) B3025127
theorem B13614803 : Blo 1792097 13614803 := bstep (se 1 (by rfl) ⟨10211102, by rfl⟩ : syracuseStep 13614803 = 20422205) B20422205
theorem B2689001 : Blo 1792097 2689001 := bstep (se 2 (by rfl) ⟨1008375, by rfl⟩ : syracuseStep 2689001 = 2016751) B2016751
theorem B9076535 : Blo 1792097 9076535 := bstep (se 1 (by rfl) ⟨6807401, by rfl⟩ : syracuseStep 9076535 = 13614803) B13614803
theorem B6051023 : Blo 1792097 6051023 := bstep (se 1 (by rfl) ⟨4538267, by rfl⟩ : syracuseStep 6051023 = 9076535) B9076535
theorem B1792667 : Blo 1792097 1792667 := bstep (se 1 (by rfl) ⟨1344500, by rfl⟩ : syracuseStep 1792667 = 2689001) B2689001
theorem B4034015 : Blo 1792097 4034015 := bstep (se 1 (by rfl) ⟨3025511, by rfl⟩ : syracuseStep 4034015 = 6051023) B6051023
theorem B2689343 : Blo 1792097 2689343 := bstep (se 1 (by rfl) ⟨2017007, by rfl⟩ : syracuseStep 2689343 = 4034015) B4034015
theorem B1792895 : Blo 1792097 1792895 := bstep (se 1 (by rfl) ⟨1344671, by rfl⟩ : syracuseStep 1792895 = 2689343) B2689343

theorem C0 (j : ℕ) (h1 : 448024 ≤ j) (h2 : j ≤ 448523) : Blo 1792097 (4 * j + 3) := by
  interval_cases j
  · exact B1792099
  · exact B1792103
  · exact B1792107
  · exact B1792111
  · exact B1792115
  · exact B1792119
  · exact B1792123
  · exact B1792127
  · exact B1792131
  · exact B1792135
  · exact B1792139
  · exact B1792143
  · exact B1792147
  · exact B1792151
  · exact B1792155
  · exact B1792159
  · exact B1792163
  · exact B1792167
  · exact B1792171
  · exact B1792175
  · exact B1792179
  · exact B1792183
  · exact B1792187
  · exact B1792191
  · exact B1792195
  · exact B1792199
  · exact B1792203
  · exact B1792207
  · exact B1792211
  · exact B1792215
  · exact B1792219
  · exact B1792223
  · exact B1792227
  · exact B1792231
  · exact B1792235
  · exact B1792239
  · exact B1792243
  · exact B1792247
  · exact B1792251
  · exact B1792255
  · exact B1792259
  · exact B1792263
  · exact B1792267
  · exact B1792271
  · exact B1792275
  · exact B1792279
  · exact B1792283
  · exact B1792287
  · exact B1792291
  · exact B1792295
  · exact B1792299
  · exact B1792303
  · exact B1792307
  · exact B1792311
  · exact B1792315
  · exact B1792319
  · exact B1792323
  · exact B1792327
  · exact B1792331
  · exact B1792335
  · exact B1792339
  · exact B1792343
  · exact B1792347
  · exact B1792351
  · exact B1792355
  · exact B1792359
  · exact B1792363
  · exact B1792367
  · exact B1792371
  · exact B1792375
  · exact B1792379
  · exact B1792383
  · exact B1792387
  · exact B1792391
  · exact B1792395
  · exact B1792399
  · exact B1792403
  · exact B1792407
  · exact B1792411
  · exact B1792415
  · exact B1792419
  · exact B1792423
  · exact B1792427
  · exact B1792431
  · exact B1792435
  · exact B1792439
  · exact B1792443
  · exact B1792447
  · exact B1792451
  · exact B1792455
  · exact B1792459
  · exact B1792463
  · exact B1792467
  · exact B1792471
  · exact B1792475
  · exact B1792479
  · exact B1792483
  · exact B1792487
  · exact B1792491
  · exact B1792495
  · exact B1792499
  · exact B1792503
  · exact B1792507
  · exact B1792511
  · exact B1792515
  · exact B1792519
  · exact B1792523
  · exact B1792527
  · exact B1792531
  · exact B1792535
  · exact B1792539
  · exact B1792543
  · exact B1792547
  · exact B1792551
  · exact B1792555
  · exact B1792559
  · exact B1792563
  · exact B1792567
  · exact B1792571
  · exact B1792575
  · exact B1792579
  · exact B1792583
  · exact B1792587
  · exact B1792591
  · exact B1792595
  · exact B1792599
  · exact B1792603
  · exact B1792607
  · exact B1792611
  · exact B1792615
  · exact B1792619
  · exact B1792623
  · exact B1792627
  · exact B1792631
  · exact B1792635
  · exact B1792639
  · exact B1792643
  · exact B1792647
  · exact B1792651
  · exact B1792655
  · exact B1792659
  · exact B1792663
  · exact B1792667
  · exact B1792671
  · exact B1792675
  · exact B1792679
  · exact B1792683
  · exact B1792687
  · exact B1792691
  · exact B1792695
  · exact B1792699
  · exact B1792703
  · exact B1792707
  · exact B1792711
  · exact B1792715
  · exact B1792719
  · exact B1792723
  · exact B1792727
  · exact B1792731
  · exact B1792735
  · exact B1792739
  · exact B1792743
  · exact B1792747
  · exact B1792751
  · exact B1792755
  · exact B1792759
  · exact B1792763
  · exact B1792767
  · exact B1792771
  · exact B1792775
  · exact B1792779
  · exact B1792783
  · exact B1792787
  · exact B1792791
  · exact B1792795
  · exact B1792799
  · exact B1792803
  · exact B1792807
  · exact B1792811
  · exact B1792815
  · exact B1792819
  · exact B1792823
  · exact B1792827
  · exact B1792831
  · exact B1792835
  · exact B1792839
  · exact B1792843
  · exact B1792847
  · exact B1792851
  · exact B1792855
  · exact B1792859
  · exact B1792863
  · exact B1792867
  · exact B1792871
  · exact B1792875
  · exact B1792879
  · exact B1792883
  · exact B1792887
  · exact B1792891
  · exact B1792895
  · exact B1792899
  · exact B1792903
  · exact B1792907
  · exact B1792911
  · exact B1792915
  · exact B1792919
  · exact B1792923
  · exact B1792927
  · exact B1792931
  · exact B1792935
  · exact B1792939
  · exact B1792943
  · exact B1792947
  · exact B1792951
  · exact B1792955
  · exact B1792959
  · exact B1792963
  · exact B1792967
  · exact B1792971
  · exact B1792975
  · exact B1792979
  · exact B1792983
  · exact B1792987
  · exact B1792991
  · exact B1792995
  · exact B1792999
  · exact B1793003
  · exact B1793007
  · exact B1793011
  · exact B1793015
  · exact B1793019
  · exact B1793023
  · exact B1793027
  · exact B1793031
  · exact B1793035
  · exact B1793039
  · exact B1793043
  · exact B1793047
  · exact B1793051
  · exact B1793055
  · exact B1793059
  · exact B1793063
  · exact B1793067
  · exact B1793071
  · exact B1793075
  · exact B1793079
  · exact B1793083
  · exact B1793087
  · exact B1793091
  · exact B1793095
  · exact B1793099
  · exact B1793103
  · exact B1793107
  · exact B1793111
  · exact B1793115
  · exact B1793119
  · exact B1793123
  · exact B1793127
  · exact B1793131
  · exact B1793135
  · exact B1793139
  · exact B1793143
  · exact B1793147
  · exact B1793151
  · exact B1793155
  · exact B1793159
  · exact B1793163
  · exact B1793167
  · exact B1793171
  · exact B1793175
  · exact B1793179
  · exact B1793183
  · exact B1793187
  · exact B1793191
  · exact B1793195
  · exact B1793199
  · exact B1793203
  · exact B1793207
  · exact B1793211
  · exact B1793215
  · exact B1793219
  · exact B1793223
  · exact B1793227
  · exact B1793231
  · exact B1793235
  · exact B1793239
  · exact B1793243
  · exact B1793247
  · exact B1793251
  · exact B1793255
  · exact B1793259
  · exact B1793263
  · exact B1793267
  · exact B1793271
  · exact B1793275
  · exact B1793279
  · exact B1793283
  · exact B1793287
  · exact B1793291
  · exact B1793295
  · exact B1793299
  · exact B1793303
  · exact B1793307
  · exact B1793311
  · exact B1793315
  · exact B1793319
  · exact B1793323
  · exact B1793327
  · exact B1793331
  · exact B1793335
  · exact B1793339
  · exact B1793343
  · exact B1793347
  · exact B1793351
  · exact B1793355
  · exact B1793359
  · exact B1793363
  · exact B1793367
  · exact B1793371
  · exact B1793375
  · exact B1793379
  · exact B1793383
  · exact B1793387
  · exact B1793391
  · exact B1793395
  · exact B1793399
  · exact B1793403
  · exact B1793407
  · exact B1793411
  · exact B1793415
  · exact B1793419
  · exact B1793423
  · exact B1793427
  · exact B1793431
  · exact B1793435
  · exact B1793439
  · exact B1793443
  · exact B1793447
  · exact B1793451
  · exact B1793455
  · exact B1793459
  · exact B1793463
  · exact B1793467
  · exact B1793471
  · exact B1793475
  · exact B1793479
  · exact B1793483
  · exact B1793487
  · exact B1793491
  · exact B1793495
  · exact B1793499
  · exact B1793503
  · exact B1793507
  · exact B1793511
  · exact B1793515
  · exact B1793519
  · exact B1793523
  · exact B1793527
  · exact B1793531
  · exact B1793535
  · exact B1793539
  · exact B1793543
  · exact B1793547
  · exact B1793551
  · exact B1793555
  · exact B1793559
  · exact B1793563
  · exact B1793567
  · exact B1793571
  · exact B1793575
  · exact B1793579
  · exact B1793583
  · exact B1793587
  · exact B1793591
  · exact B1793595
  · exact B1793599
  · exact B1793603
  · exact B1793607
  · exact B1793611
  · exact B1793615
  · exact B1793619
  · exact B1793623
  · exact B1793627
  · exact B1793631
  · exact B1793635
  · exact B1793639
  · exact B1793643
  · exact B1793647
  · exact B1793651
  · exact B1793655
  · exact B1793659
  · exact B1793663
  · exact B1793667
  · exact B1793671
  · exact B1793675
  · exact B1793679
  · exact B1793683
  · exact B1793687
  · exact B1793691
  · exact B1793695
  · exact B1793699
  · exact B1793703
  · exact B1793707
  · exact B1793711
  · exact B1793715
  · exact B1793719
  · exact B1793723
  · exact B1793727
  · exact B1793731
  · exact B1793735
  · exact B1793739
  · exact B1793743
  · exact B1793747
  · exact B1793751
  · exact B1793755
  · exact B1793759
  · exact B1793763
  · exact B1793767
  · exact B1793771
  · exact B1793775
  · exact B1793779
  · exact B1793783
  · exact B1793787
  · exact B1793791
  · exact B1793795
  · exact B1793799
  · exact B1793803
  · exact B1793807
  · exact B1793811
  · exact B1793815
  · exact B1793819
  · exact B1793823
  · exact B1793827
  · exact B1793831
  · exact B1793835
  · exact B1793839
  · exact B1793843
  · exact B1793847
  · exact B1793851
  · exact B1793855
  · exact B1793859
  · exact B1793863
  · exact B1793867
  · exact B1793871
  · exact B1793875
  · exact B1793879
  · exact B1793883
  · exact B1793887
  · exact B1793891
  · exact B1793895
  · exact B1793899
  · exact B1793903
  · exact B1793907
  · exact B1793911
  · exact B1793915
  · exact B1793919
  · exact B1793923
  · exact B1793927
  · exact B1793931
  · exact B1793935
  · exact B1793939
  · exact B1793943
  · exact B1793947
  · exact B1793951
  · exact B1793955
  · exact B1793959
  · exact B1793963
  · exact B1793967
  · exact B1793971
  · exact B1793975
  · exact B1793979
  · exact B1793983
  · exact B1793987
  · exact B1793991
  · exact B1793995
  · exact B1793999
  · exact B1794003
  · exact B1794007
  · exact B1794011
  · exact B1794015
  · exact B1794019
  · exact B1794023
  · exact B1794027
  · exact B1794031
  · exact B1794035
  · exact B1794039
  · exact B1794043
  · exact B1794047
  · exact B1794051
  · exact B1794055
  · exact B1794059
  · exact B1794063
  · exact B1794067
  · exact B1794071
  · exact B1794075
  · exact B1794079
  · exact B1794083
  · exact B1794087
  · exact B1794091
  · exact B1794095

theorem solution (m : ℕ) (hlo : 1792097 ≤ m) (hhi : m ≤ 1794097) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 448024 ≤ j := by omega
    have hj2 : j ≤ 448523 := by omega
    have hb : Blo 1792097 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
