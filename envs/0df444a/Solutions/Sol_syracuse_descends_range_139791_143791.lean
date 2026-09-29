-- Prove2me | solution 1 for syracuse_descends_range_139791_143791
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:36.584771+00:00
-- url     : https://prove2.me/submissions/d1cb217e-a7be-4303-9967-f39152bed561

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


theorem B229405 : Blo 139791 229405 := bbase (se 3 (by rfl) ⟨43013, by rfl⟩ : syracuseStep 229405 = 86027) (by norm_num)
theorem B721061 : Blo 139791 721061 := bbase (se 4 (by rfl) ⟨67599, by rfl⟩ : syracuseStep 721061 = 135199) (by norm_num)
theorem B295093 : Blo 139791 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B360733 : Blo 139791 360733 := bbase (se 3 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 360733 = 135275) (by norm_num)
theorem B164197 : Blo 139791 164197 := bbase (se 4 (by rfl) ⟨15393, by rfl⟩ : syracuseStep 164197 = 30787) (by norm_num)
theorem B360845 : Blo 139791 360845 := bbase (se 3 (by rfl) ⟨67658, by rfl⟩ : syracuseStep 360845 = 135317) (by norm_num)
theorem B197077 : Blo 139791 197077 := bbase (se 7 (by rfl) ⟨2309, by rfl⟩ : syracuseStep 197077 = 4619) (by norm_num)
theorem B361037 : Blo 139791 361037 := bbase (se 3 (by rfl) ⟨67694, by rfl⟩ : syracuseStep 361037 = 135389) (by norm_num)
theorem B230045 : Blo 139791 230045 := bbase (se 3 (by rfl) ⟨43133, by rfl⟩ : syracuseStep 230045 = 86267) (by norm_num)
theorem B361381 : Blo 139791 361381 := bbase (se 4 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 361381 = 67759) (by norm_num)
theorem B361493 : Blo 139791 361493 := bbase (se 6 (by rfl) ⟨8472, by rfl⟩ : syracuseStep 361493 = 16945) (by norm_num)
theorem B361685 : Blo 139791 361685 := bbase (se 7 (by rfl) ⟨4238, by rfl⟩ : syracuseStep 361685 = 8477) (by norm_num)
theorem B459989 : Blo 139791 459989 := bbase (se 7 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 459989 = 10781) (by norm_num)
theorem B722197 : Blo 139791 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B460181 : Blo 139791 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B722357 : Blo 139791 722357 := bbase (se 5 (by rfl) ⟨33860, by rfl⟩ : syracuseStep 722357 = 67721) (by norm_num)
theorem B362029 : Blo 139791 362029 := bbase (se 3 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 362029 = 135761) (by norm_num)
theorem B362141 : Blo 139791 362141 := bbase (se 3 (by rfl) ⟨67901, by rfl⟩ : syracuseStep 362141 = 135803) (by norm_num)
theorem B362333 : Blo 139791 362333 := bbase (se 3 (by rfl) ⟨67937, by rfl⟩ : syracuseStep 362333 = 135875) (by norm_num)
theorem B362677 : Blo 139791 362677 := bbase (se 5 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 362677 = 34001) (by norm_num)
theorem B362765 : Blo 139791 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B362789 : Blo 139791 362789 := bbase (se 4 (by rfl) ⟨34011, by rfl⟩ : syracuseStep 362789 = 68023) (by norm_num)
theorem B362981 : Blo 139791 362981 := bbase (se 4 (by rfl) ⟨34029, by rfl⟩ : syracuseStep 362981 = 68059) (by norm_num)
theorem B723653 : Blo 139791 723653 := bbase (se 4 (by rfl) ⟨67842, by rfl⟩ : syracuseStep 723653 = 135685) (by norm_num)
theorem B363325 : Blo 139791 363325 := bbase (se 3 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 363325 = 136247) (by norm_num)
theorem B199541 : Blo 139791 199541 := bbase (se 5 (by rfl) ⟨9353, by rfl⟩ : syracuseStep 199541 = 18707) (by norm_num)
theorem B363437 : Blo 139791 363437 := bbase (se 3 (by rfl) ⟨68144, by rfl⟩ : syracuseStep 363437 = 136289) (by norm_num)
theorem B199621 : Blo 139791 199621 := bbase (se 4 (by rfl) ⟨18714, by rfl⟩ : syracuseStep 199621 = 37429) (by norm_num)
theorem B330725 : Blo 139791 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B199741 : Blo 139791 199741 := bbase (se 3 (by rfl) ⟨37451, by rfl⟩ : syracuseStep 199741 = 74903) (by norm_num)
theorem B363629 : Blo 139791 363629 := bbase (se 3 (by rfl) ⟨68180, by rfl⟩ : syracuseStep 363629 = 136361) (by norm_num)
theorem B199837 : Blo 139791 199837 := bbase (se 3 (by rfl) ⟨37469, by rfl⟩ : syracuseStep 199837 = 74939) (by norm_num)
theorem B265493 : Blo 139791 265493 := bbase (se 6 (by rfl) ⟨6222, by rfl⟩ : syracuseStep 265493 = 12445) (by norm_num)
theorem B363973 : Blo 139791 363973 := bbase (se 4 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 363973 = 68245) (by norm_num)
theorem B265781 : Blo 139791 265781 := bbase (se 5 (by rfl) ⟨12458, by rfl⟩ : syracuseStep 265781 = 24917) (by norm_num)
theorem B200333 : Blo 139791 200333 := bbase (se 3 (by rfl) ⟨37562, by rfl⟩ : syracuseStep 200333 = 75125) (by norm_num)
theorem B265933 : Blo 139791 265933 := bbase (se 3 (by rfl) ⟨49862, by rfl⟩ : syracuseStep 265933 = 99725) (by norm_num)
theorem B298765 : Blo 139791 298765 := bbase (se 3 (by rfl) ⟨56018, by rfl⟩ : syracuseStep 298765 = 112037) (by norm_num)
theorem B1085237 : Blo 139791 1085237 := bbase (se 5 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 1085237 = 101741) (by norm_num)
theorem B298885 : Blo 139791 298885 := bbase (se 4 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 298885 = 56041) (by norm_num)
theorem B724949 : Blo 139791 724949 := bbase (se 7 (by rfl) ⟨8495, by rfl⟩ : syracuseStep 724949 = 16991) (by norm_num)
theorem B266237 : Blo 139791 266237 := bbase (se 3 (by rfl) ⟨49919, by rfl⟩ : syracuseStep 266237 = 99839) (by norm_num)
theorem B299141 : Blo 139791 299141 := bbase (se 4 (by rfl) ⟨28044, by rfl⟩ : syracuseStep 299141 = 56089) (by norm_num)
theorem B168113 : Blo 139791 168113 := bbase (se 2 (by rfl) ⟨63042, by rfl⟩ : syracuseStep 168113 = 126085) (by norm_num)
theorem B200885 : Blo 139791 200885 := bbase (se 5 (by rfl) ⟨9416, by rfl⟩ : syracuseStep 200885 = 18833) (by norm_num)
theorem B364877 : Blo 139791 364877 := bbase (se 3 (by rfl) ⟨68414, by rfl⟩ : syracuseStep 364877 = 136829) (by norm_num)
theorem B168421 : Blo 139791 168421 := bbase (se 4 (by rfl) ⟨15789, by rfl⟩ : syracuseStep 168421 = 31579) (by norm_num)
theorem B168517 : Blo 139791 168517 := bbase (se 4 (by rfl) ⟨15798, by rfl⟩ : syracuseStep 168517 = 31597) (by norm_num)
theorem B168661 : Blo 139791 168661 := bbase (se 7 (by rfl) ⟨1976, by rfl⟩ : syracuseStep 168661 = 3953) (by norm_num)
theorem B266989 : Blo 139791 266989 := bbase (se 3 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 266989 = 100121) (by norm_num)
theorem B1151765 : Blo 139791 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B267133 : Blo 139791 267133 := bbase (se 3 (by rfl) ⟨50087, by rfl⟩ : syracuseStep 267133 = 100175) (by norm_num)
theorem B201637 : Blo 139791 201637 := bbase (se 4 (by rfl) ⟨18903, by rfl⟩ : syracuseStep 201637 = 37807) (by norm_num)
theorem B1151957 : Blo 139791 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B300029 : Blo 139791 300029 := bbase (se 3 (by rfl) ⟨56255, by rfl⟩ : syracuseStep 300029 = 112511) (by norm_num)
theorem B267293 : Blo 139791 267293 := bbase (se 3 (by rfl) ⟨50117, by rfl⟩ : syracuseStep 267293 = 100235) (by norm_num)
theorem B693317 : Blo 139791 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B267437 : Blo 139791 267437 := bbase (se 3 (by rfl) ⟨50144, by rfl⟩ : syracuseStep 267437 = 100289) (by norm_num)
theorem B726245 : Blo 139791 726245 := bbase (se 4 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 726245 = 136171) (by norm_num)
theorem B300269 : Blo 139791 300269 := bbase (se 3 (by rfl) ⟨56300, by rfl⟩ : syracuseStep 300269 = 112601) (by norm_num)
theorem B267725 : Blo 139791 267725 := bbase (se 3 (by rfl) ⟨50198, by rfl⟩ : syracuseStep 267725 = 100397) (by norm_num)
theorem B267877 : Blo 139791 267877 := bbase (se 4 (by rfl) ⟨25113, by rfl⟩ : syracuseStep 267877 = 50227) (by norm_num)
theorem B169661 : Blo 139791 169661 := bbase (se 3 (by rfl) ⟨31811, by rfl⟩ : syracuseStep 169661 = 63623) (by norm_num)
theorem B202429 : Blo 139791 202429 := bbase (se 3 (by rfl) ⟨37955, by rfl⟩ : syracuseStep 202429 = 75911) (by norm_num)
theorem B300773 : Blo 139791 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B300781 : Blo 139791 300781 := bbase (se 3 (by rfl) ⟨56396, by rfl⟩ : syracuseStep 300781 = 112793) (by norm_num)
theorem B268181 : Blo 139791 268181 := bbase (se 6 (by rfl) ⟨6285, by rfl⟩ : syracuseStep 268181 = 12571) (by norm_num)
theorem B202765 : Blo 139791 202765 := bbase (se 3 (by rfl) ⟨38018, by rfl⟩ : syracuseStep 202765 = 76037) (by norm_num)
theorem B202981 : Blo 139791 202981 := bbase (se 4 (by rfl) ⟨19029, by rfl⟩ : syracuseStep 202981 = 38059) (by norm_num)
theorem B432373 : Blo 139791 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B170353 : Blo 139791 170353 := bbase (se 2 (by rfl) ⟨63882, by rfl⟩ : syracuseStep 170353 = 127765) (by norm_num)
theorem B235973 : Blo 139791 235973 := bbase (se 4 (by rfl) ⟨22122, by rfl⟩ : syracuseStep 235973 = 44245) (by norm_num)
theorem B727541 : Blo 139791 727541 := bbase (se 5 (by rfl) ⟨34103, by rfl⟩ : syracuseStep 727541 = 68207) (by norm_num)
theorem B236101 : Blo 139791 236101 := bbase (se 4 (by rfl) ⟨22134, by rfl⟩ : syracuseStep 236101 = 44269) (by norm_num)
theorem B170569 : Blo 139791 170569 := bbase (se 2 (by rfl) ⟨63963, by rfl⟩ : syracuseStep 170569 = 127927) (by norm_num)
theorem B203357 : Blo 139791 203357 := bbase (se 3 (by rfl) ⟨38129, by rfl⟩ : syracuseStep 203357 = 76259) (by norm_num)
theorem B268933 : Blo 139791 268933 := bbase (se 4 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 268933 = 50425) (by norm_num)
theorem B236189 : Blo 139791 236189 := bbase (se 3 (by rfl) ⟨44285, by rfl⟩ : syracuseStep 236189 = 88571) (by norm_num)
theorem B400085 : Blo 139791 400085 := bbase (se 7 (by rfl) ⟨4688, by rfl⟩ : syracuseStep 400085 = 9377) (by norm_num)
theorem B269077 : Blo 139791 269077 := bbase (se 6 (by rfl) ⟨6306, by rfl⟩ : syracuseStep 269077 = 12613) (by norm_num)
theorem B236317 : Blo 139791 236317 := bbase (se 3 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 236317 = 88619) (by norm_num)
theorem B203581 : Blo 139791 203581 := bbase (se 3 (by rfl) ⟨38171, by rfl⟩ : syracuseStep 203581 = 76343) (by norm_num)
theorem B760661 : Blo 139791 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B301909 : Blo 139791 301909 := bbase (se 9 (by rfl) ⟨884, by rfl⟩ : syracuseStep 301909 = 1769) (by norm_num)
theorem B236405 : Blo 139791 236405 := bbase (se 5 (by rfl) ⟨11081, by rfl⟩ : syracuseStep 236405 = 22163) (by norm_num)
theorem B269237 : Blo 139791 269237 := bbase (se 5 (by rfl) ⟨12620, by rfl⟩ : syracuseStep 269237 = 25241) (by norm_num)
theorem B236533 : Blo 139791 236533 := bbase (se 5 (by rfl) ⟨11087, by rfl⟩ : syracuseStep 236533 = 22175) (by norm_num)
theorem B367669 : Blo 139791 367669 := bbase (se 5 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 367669 = 34469) (by norm_num)
theorem B269381 : Blo 139791 269381 := bbase (se 4 (by rfl) ⟨25254, by rfl⟩ : syracuseStep 269381 = 50509) (by norm_num)
theorem B236621 : Blo 139791 236621 := bbase (se 3 (by rfl) ⟨44366, by rfl⟩ : syracuseStep 236621 = 88733) (by norm_num)
theorem B728261 : Blo 139791 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B236749 : Blo 139791 236749 := bbase (se 3 (by rfl) ⟨44390, by rfl⟩ : syracuseStep 236749 = 88781) (by norm_num)
theorem B302285 : Blo 139791 302285 := bbase (se 3 (by rfl) ⟨56678, by rfl⟩ : syracuseStep 302285 = 113357) (by norm_num)
theorem B269525 : Blo 139791 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B466165 : Blo 139791 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B236837 : Blo 139791 236837 := bbase (se 4 (by rfl) ⟨22203, by rfl⟩ : syracuseStep 236837 = 44407) (by norm_num)
theorem B269669 : Blo 139791 269669 := bbase (se 4 (by rfl) ⟨25281, by rfl⟩ : syracuseStep 269669 = 50563) (by norm_num)
theorem B236965 : Blo 139791 236965 := bbase (se 4 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 236965 = 44431) (by norm_num)
theorem B237053 : Blo 139791 237053 := bbase (se 3 (by rfl) ⟨44447, by rfl⟩ : syracuseStep 237053 = 88895) (by norm_num)
theorem B269821 : Blo 139791 269821 := bbase (se 3 (by rfl) ⟨50591, by rfl⟩ : syracuseStep 269821 = 101183) (by norm_num)
theorem B237181 : Blo 139791 237181 := bbase (se 3 (by rfl) ⟨44471, by rfl⟩ : syracuseStep 237181 = 88943) (by norm_num)
theorem B237269 : Blo 139791 237269 := bbase (se 7 (by rfl) ⟨2780, by rfl⟩ : syracuseStep 237269 = 5561) (by norm_num)
theorem B2989781 : Blo 139791 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B171805 : Blo 139791 171805 := bbase (se 3 (by rfl) ⟨32213, by rfl⟩ : syracuseStep 171805 = 64427) (by norm_num)
theorem B270125 : Blo 139791 270125 := bbase (se 3 (by rfl) ⟨50648, by rfl⟩ : syracuseStep 270125 = 101297) (by norm_num)
theorem B532277 : Blo 139791 532277 := bbase (se 5 (by rfl) ⟨24950, by rfl⟩ : syracuseStep 532277 = 49901) (by norm_num)
theorem B237397 : Blo 139791 237397 := bbase (se 9 (by rfl) ⟨695, by rfl⟩ : syracuseStep 237397 = 1391) (by norm_num)
theorem B401269 : Blo 139791 401269 := bbase (se 5 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 401269 = 37619) (by norm_num)
theorem B237485 : Blo 139791 237485 := bbase (se 3 (by rfl) ⟨44528, by rfl⟩ : syracuseStep 237485 = 89057) (by norm_num)
theorem B597941 : Blo 139791 597941 := bbase (se 5 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 597941 = 56057) (by norm_num)
theorem B401429 : Blo 139791 401429 := bbase (se 6 (by rfl) ⟨9408, by rfl⟩ : syracuseStep 401429 = 18817) (by norm_num)
theorem B434197 : Blo 139791 434197 := bbase (se 6 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 434197 = 20353) (by norm_num)
theorem B237613 : Blo 139791 237613 := bbase (se 3 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 237613 = 89105) (by norm_num)
theorem B532565 : Blo 139791 532565 := bbase (se 8 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 532565 = 6241) (by norm_num)
theorem B237701 : Blo 139791 237701 := bbase (se 4 (by rfl) ⟨22284, by rfl⟩ : syracuseStep 237701 = 44569) (by norm_num)
theorem B172265 : Blo 139791 172265 := bbase (se 2 (by rfl) ⟨64599, by rfl⟩ : syracuseStep 172265 = 129199) (by norm_num)
theorem B237829 : Blo 139791 237829 := bbase (se 4 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 237829 = 44593) (by norm_num)
theorem B401669 : Blo 139791 401669 := bbase (se 4 (by rfl) ⟨37656, by rfl⟩ : syracuseStep 401669 = 75313) (by norm_num)
theorem B237917 : Blo 139791 237917 := bbase (se 3 (by rfl) ⟨44609, by rfl⟩ : syracuseStep 237917 = 89219) (by norm_num)
theorem B172477 : Blo 139791 172477 := bbase (se 3 (by rfl) ⟨32339, by rfl⟩ : syracuseStep 172477 = 64679) (by norm_num)
theorem B401861 : Blo 139791 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B238045 : Blo 139791 238045 := bbase (se 3 (by rfl) ⟨44633, by rfl⟩ : syracuseStep 238045 = 89267) (by norm_num)
theorem B270877 : Blo 139791 270877 := bbase (se 3 (by rfl) ⟨50789, by rfl⟩ : syracuseStep 270877 = 101579) (by norm_num)
theorem B238133 : Blo 139791 238133 := bbase (se 5 (by rfl) ⟨11162, by rfl⟩ : syracuseStep 238133 = 22325) (by norm_num)
theorem B172621 : Blo 139791 172621 := bbase (se 3 (by rfl) ⟨32366, by rfl⟩ : syracuseStep 172621 = 64733) (by norm_num)
theorem B303709 : Blo 139791 303709 := bbase (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) (by norm_num)
theorem B271021 : Blo 139791 271021 := bbase (se 3 (by rfl) ⟨50816, by rfl⟩ : syracuseStep 271021 = 101633) (by norm_num)
theorem B238261 : Blo 139791 238261 := bbase (se 5 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 238261 = 22337) (by norm_num)
theorem B238349 : Blo 139791 238349 := bbase (se 3 (by rfl) ⟨44690, by rfl⟩ : syracuseStep 238349 = 89381) (by norm_num)
theorem B303925 : Blo 139791 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B271181 : Blo 139791 271181 := bbase (se 3 (by rfl) ⟨50846, by rfl⟩ : syracuseStep 271181 = 101693) (by norm_num)
theorem B238477 : Blo 139791 238477 := bbase (se 3 (by rfl) ⟨44714, by rfl⟩ : syracuseStep 238477 = 89429) (by norm_num)
theorem B271325 : Blo 139791 271325 := bbase (se 3 (by rfl) ⟨50873, by rfl⟩ : syracuseStep 271325 = 101747) (by norm_num)
theorem B238565 : Blo 139791 238565 := bbase (se 4 (by rfl) ⟨22365, by rfl⟩ : syracuseStep 238565 = 44731) (by norm_num)
theorem B304229 : Blo 139791 304229 := bbase (se 4 (by rfl) ⟨28521, by rfl⟩ : syracuseStep 304229 = 57043) (by norm_num)
theorem B238693 : Blo 139791 238693 := bbase (se 4 (by rfl) ⟨22377, by rfl⟩ : syracuseStep 238693 = 44755) (by norm_num)
theorem B238781 : Blo 139791 238781 := bbase (se 3 (by rfl) ⟨44771, by rfl⟩ : syracuseStep 238781 = 89543) (by norm_num)
theorem B533749 : Blo 139791 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B271613 : Blo 139791 271613 := bbase (se 3 (by rfl) ⟨50927, by rfl⟩ : syracuseStep 271613 = 101855) (by norm_num)
theorem B238909 : Blo 139791 238909 := bbase (se 3 (by rfl) ⟨44795, by rfl⟩ : syracuseStep 238909 = 89591) (by norm_num)
theorem B238997 : Blo 139791 238997 := bbase (se 6 (by rfl) ⟨5601, by rfl⟩ : syracuseStep 238997 = 11203) (by norm_num)
theorem B271765 : Blo 139791 271765 := bbase (se 6 (by rfl) ⟨6369, by rfl⟩ : syracuseStep 271765 = 12739) (by norm_num)
theorem B402853 : Blo 139791 402853 := bbase (se 4 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 402853 = 75535) (by norm_num)
theorem B239125 : Blo 139791 239125 := bbase (se 6 (by rfl) ⟨5604, by rfl⟩ : syracuseStep 239125 = 11209) (by norm_num)
theorem B534053 : Blo 139791 534053 := bbase (se 4 (by rfl) ⟨50067, by rfl⟩ : syracuseStep 534053 = 100135) (by norm_num)
theorem B239213 : Blo 139791 239213 := bbase (se 3 (by rfl) ⟨44852, by rfl⟩ : syracuseStep 239213 = 89705) (by norm_num)
theorem B468629 : Blo 139791 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B599717 : Blo 139791 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B304813 : Blo 139791 304813 := bbase (se 3 (by rfl) ⟨57152, by rfl⟩ : syracuseStep 304813 = 114305) (by norm_num)
theorem B272069 : Blo 139791 272069 := bbase (se 4 (by rfl) ⟨25506, by rfl⟩ : syracuseStep 272069 = 51013) (by norm_num)
theorem B239341 : Blo 139791 239341 := bbase (se 3 (by rfl) ⟨44876, by rfl⟩ : syracuseStep 239341 = 89753) (by norm_num)
theorem B239429 : Blo 139791 239429 := bbase (se 4 (by rfl) ⟨22446, by rfl⟩ : syracuseStep 239429 = 44893) (by norm_num)
theorem B599957 : Blo 139791 599957 := bbase (se 6 (by rfl) ⟨14061, by rfl⟩ : syracuseStep 599957 = 28123) (by norm_num)
theorem B337861 : Blo 139791 337861 := bbase (se 4 (by rfl) ⟨31674, by rfl⟩ : syracuseStep 337861 = 63349) (by norm_num)
theorem B305093 : Blo 139791 305093 := bbase (se 4 (by rfl) ⟨28602, by rfl⟩ : syracuseStep 305093 = 57205) (by norm_num)
theorem B239557 : Blo 139791 239557 := bbase (se 4 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 239557 = 44917) (by norm_num)
theorem B796661 : Blo 139791 796661 := bbase (se 5 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 796661 = 74687) (by norm_num)
theorem B239645 : Blo 139791 239645 := bbase (se 3 (by rfl) ⟨44933, by rfl⟩ : syracuseStep 239645 = 89867) (by norm_num)
theorem B239773 : Blo 139791 239773 := bbase (se 3 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 239773 = 89915) (by norm_num)
theorem B305309 : Blo 139791 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B239861 : Blo 139791 239861 := bbase (se 5 (by rfl) ⟨11243, by rfl⟩ : syracuseStep 239861 = 22487) (by norm_num)
theorem B239989 : Blo 139791 239989 := bbase (se 5 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 239989 = 22499) (by norm_num)
theorem B272821 : Blo 139791 272821 := bbase (se 5 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 272821 = 25577) (by norm_num)
theorem B240077 : Blo 139791 240077 := bbase (se 3 (by rfl) ⟨45014, by rfl⟩ : syracuseStep 240077 = 90029) (by norm_num)
theorem B403957 : Blo 139791 403957 := bbase (se 5 (by rfl) ⟨18935, by rfl⟩ : syracuseStep 403957 = 37871) (by norm_num)
theorem B404021 : Blo 139791 404021 := bbase (se 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) (by norm_num)
theorem B272965 : Blo 139791 272965 := bbase (se 4 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 272965 = 51181) (by norm_num)
theorem B240205 : Blo 139791 240205 := bbase (se 3 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 240205 = 90077) (by norm_num)
theorem B338525 : Blo 139791 338525 := bbase (se 3 (by rfl) ⟨63473, by rfl⟩ : syracuseStep 338525 = 126947) (by norm_num)
theorem B240293 : Blo 139791 240293 := bbase (se 4 (by rfl) ⟨22527, by rfl⟩ : syracuseStep 240293 = 45055) (by norm_num)
theorem B240365 : Blo 139791 240365 := bbase (se 3 (by rfl) ⟨45068, by rfl⟩ : syracuseStep 240365 = 90137) (by norm_num)
theorem B240421 : Blo 139791 240421 := bbase (se 4 (by rfl) ⟨22539, by rfl⟩ : syracuseStep 240421 = 45079) (by norm_num)
theorem B240509 : Blo 139791 240509 := bbase (se 3 (by rfl) ⟨45095, by rfl⟩ : syracuseStep 240509 = 90191) (by norm_num)
theorem B732053 : Blo 139791 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B306125 : Blo 139791 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B240637 : Blo 139791 240637 := bbase (se 3 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 240637 = 90239) (by norm_num)
theorem B306173 : Blo 139791 306173 := bbase (se 3 (by rfl) ⟨57407, by rfl⟩ : syracuseStep 306173 = 114815) (by norm_num)
theorem B1027093 : Blo 139791 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B240725 : Blo 139791 240725 := bbase (se 8 (by rfl) ⟨1410, by rfl⟩ : syracuseStep 240725 = 2821) (by norm_num)
theorem B306317 : Blo 139791 306317 := bbase (se 3 (by rfl) ⟨57434, by rfl⟩ : syracuseStep 306317 = 114869) (by norm_num)
theorem B240853 : Blo 139791 240853 := bbase (se 7 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 240853 = 5645) (by norm_num)
theorem B568549 : Blo 139791 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B240941 : Blo 139791 240941 := bbase (se 3 (by rfl) ⟨45176, by rfl⟩ : syracuseStep 240941 = 90353) (by norm_num)
theorem B241069 : Blo 139791 241069 := bbase (se 3 (by rfl) ⟨45200, by rfl⟩ : syracuseStep 241069 = 90401) (by norm_num)
theorem B241157 : Blo 139791 241157 := bbase (se 4 (by rfl) ⟨22608, by rfl⟩ : syracuseStep 241157 = 45217) (by norm_num)
theorem B536165 : Blo 139791 536165 := bbase (se 4 (by rfl) ⟨50265, by rfl⟩ : syracuseStep 536165 = 100531) (by norm_num)
theorem B241285 : Blo 139791 241285 := bbase (se 4 (by rfl) ⟨22620, by rfl⟩ : syracuseStep 241285 = 45241) (by norm_num)
theorem B241373 : Blo 139791 241373 := bbase (se 3 (by rfl) ⟨45257, by rfl⟩ : syracuseStep 241373 = 90515) (by norm_num)
theorem B306965 : Blo 139791 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B438053 : Blo 139791 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B241501 : Blo 139791 241501 := bbase (se 3 (by rfl) ⟨45281, by rfl⟩ : syracuseStep 241501 = 90563) (by norm_num)
theorem B307061 : Blo 139791 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B536453 : Blo 139791 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B241589 : Blo 139791 241589 := bbase (se 5 (by rfl) ⟨11324, by rfl⟩ : syracuseStep 241589 = 22649) (by norm_num)
theorem B405461 : Blo 139791 405461 := bbase (se 7 (by rfl) ⟨4751, by rfl⟩ : syracuseStep 405461 = 9503) (by norm_num)
theorem B1093621 : Blo 139791 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B241717 : Blo 139791 241717 := bbase (se 5 (by rfl) ⟨11330, by rfl⟩ : syracuseStep 241717 = 22661) (by norm_num)
theorem B602245 : Blo 139791 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B241805 : Blo 139791 241805 := bbase (se 3 (by rfl) ⟨45338, by rfl⟩ : syracuseStep 241805 = 90677) (by norm_num)
theorem B307381 : Blo 139791 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B241933 : Blo 139791 241933 := bbase (se 3 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 241933 = 90725) (by norm_num)
theorem B340301 : Blo 139791 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B242021 : Blo 139791 242021 := bbase (se 4 (by rfl) ⟨22689, by rfl⟩ : syracuseStep 242021 = 45379) (by norm_num)
theorem B242117 : Blo 139791 242117 := bbase (se 4 (by rfl) ⟨22698, by rfl⟩ : syracuseStep 242117 = 45397) (by norm_num)
theorem B242149 : Blo 139791 242149 := bbase (se 4 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 242149 = 45403) (by norm_num)
theorem B242237 : Blo 139791 242237 := bbase (se 3 (by rfl) ⟨45419, by rfl⟩ : syracuseStep 242237 = 90839) (by norm_num)
theorem B242365 : Blo 139791 242365 := bbase (se 3 (by rfl) ⟨45443, by rfl⟩ : syracuseStep 242365 = 90887) (by norm_num)
theorem B471797 : Blo 139791 471797 := bbase (se 5 (by rfl) ⟨22115, by rfl⟩ : syracuseStep 471797 = 44231) (by norm_num)
theorem B242453 : Blo 139791 242453 := bbase (se 6 (by rfl) ⟨5682, by rfl⟩ : syracuseStep 242453 = 11365) (by norm_num)
theorem B209693 : Blo 139791 209693 := bbase (se 3 (by rfl) ⟨39317, by rfl⟩ : syracuseStep 209693 = 78635) (by norm_num)
theorem B209717 : Blo 139791 209717 := bbase (se 5 (by rfl) ⟨9830, by rfl⟩ : syracuseStep 209717 = 19661) (by norm_num)
theorem B209741 : Blo 139791 209741 := bbase (se 3 (by rfl) ⟨39326, by rfl⟩ : syracuseStep 209741 = 78653) (by norm_num)
theorem B209765 : Blo 139791 209765 := bbase (se 4 (by rfl) ⟨19665, by rfl⟩ : syracuseStep 209765 = 39331) (by norm_num)
theorem B177005 : Blo 139791 177005 := bbase (se 3 (by rfl) ⟨33188, by rfl⟩ : syracuseStep 177005 = 66377) (by norm_num)
theorem B209789 : Blo 139791 209789 := bbase (se 3 (by rfl) ⟨39335, by rfl⟩ : syracuseStep 209789 = 78671) (by norm_num)
theorem B209813 : Blo 139791 209813 := bbase (se 6 (by rfl) ⟨4917, by rfl⟩ : syracuseStep 209813 = 9835) (by norm_num)
theorem B242581 : Blo 139791 242581 := bbase (se 6 (by rfl) ⟨5685, by rfl⟩ : syracuseStep 242581 = 11371) (by norm_num)
theorem B177049 : Blo 139791 177049 := bbase (se 2 (by rfl) ⟨66393, by rfl⟩ : syracuseStep 177049 = 132787) (by norm_num)
theorem B177061 : Blo 139791 177061 := bbase (se 4 (by rfl) ⟨16599, by rfl⟩ : syracuseStep 177061 = 33199) (by norm_num)
theorem B209837 : Blo 139791 209837 := bbase (se 3 (by rfl) ⟨39344, by rfl⟩ : syracuseStep 209837 = 78689) (by norm_num)
theorem B209861 : Blo 139791 209861 := bbase (se 4 (by rfl) ⟨19674, by rfl⟩ : syracuseStep 209861 = 39349) (by norm_num)
theorem B209885 : Blo 139791 209885 := bbase (se 3 (by rfl) ⟨39353, by rfl⟩ : syracuseStep 209885 = 78707) (by norm_num)
theorem B275437 : Blo 139791 275437 := bbase (se 3 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 275437 = 103289) (by norm_num)
theorem B209909 : Blo 139791 209909 := bbase (se 5 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 209909 = 19679) (by norm_num)
theorem B898037 : Blo 139791 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B177157 : Blo 139791 177157 := bbase (se 4 (by rfl) ⟨16608, by rfl⟩ : syracuseStep 177157 = 33217) (by norm_num)
theorem B209933 : Blo 139791 209933 := bbase (se 3 (by rfl) ⟨39362, by rfl⟩ : syracuseStep 209933 = 78725) (by norm_num)
theorem B1061909 : Blo 139791 1061909 := bbase (se 6 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 1061909 = 49777) (by norm_num)
theorem B209957 : Blo 139791 209957 := bbase (se 4 (by rfl) ⟨19683, by rfl⟩ : syracuseStep 209957 = 39367) (by norm_num)
theorem B537637 : Blo 139791 537637 := bbase (se 4 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 537637 = 100807) (by norm_num)
theorem B144437 : Blo 139791 144437 := bbase (se 5 (by rfl) ⟨6770, by rfl⟩ : syracuseStep 144437 = 13541) (by norm_num)
theorem B209981 : Blo 139791 209981 := bbase (se 3 (by rfl) ⟨39371, by rfl⟩ : syracuseStep 209981 = 78743) (by norm_num)
theorem B210005 : Blo 139791 210005 := bbase (se 8 (by rfl) ⟨1230, by rfl⟩ : syracuseStep 210005 = 2461) (by norm_num)
theorem B504917 : Blo 139791 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B1225813 : Blo 139791 1225813 := bbase (se 8 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 1225813 = 14365) (by norm_num)
theorem B210029 : Blo 139791 210029 := bbase (se 3 (by rfl) ⟨39380, by rfl⟩ : syracuseStep 210029 = 78761) (by norm_num)
theorem B210053 : Blo 139791 210053 := bbase (se 4 (by rfl) ⟨19692, by rfl⟩ : syracuseStep 210053 = 39385) (by norm_num)
theorem B210077 : Blo 139791 210077 := bbase (se 3 (by rfl) ⟨39389, by rfl⟩ : syracuseStep 210077 = 78779) (by norm_num)
theorem B472229 : Blo 139791 472229 := bbase (se 4 (by rfl) ⟨44271, by rfl⟩ : syracuseStep 472229 = 88543) (by norm_num)
theorem B177329 : Blo 139791 177329 := bbase (se 2 (by rfl) ⟨66498, by rfl⟩ : syracuseStep 177329 = 132997) (by norm_num)
theorem B210101 : Blo 139791 210101 := bbase (se 5 (by rfl) ⟨9848, by rfl⟩ : syracuseStep 210101 = 19697) (by norm_num)
theorem B210125 : Blo 139791 210125 := bbase (se 3 (by rfl) ⟨39398, by rfl⟩ : syracuseStep 210125 = 78797) (by norm_num)
theorem B210149 : Blo 139791 210149 := bbase (se 4 (by rfl) ⟨19701, by rfl⟩ : syracuseStep 210149 = 39403) (by norm_num)
theorem B177385 : Blo 139791 177385 := bbase (se 2 (by rfl) ⟨66519, by rfl⟩ : syracuseStep 177385 = 133039) (by norm_num)
theorem B210173 : Blo 139791 210173 := bbase (se 3 (by rfl) ⟨39407, by rfl⟩ : syracuseStep 210173 = 78815) (by norm_num)
theorem B210197 : Blo 139791 210197 := bbase (se 6 (by rfl) ⟨4926, by rfl⟩ : syracuseStep 210197 = 9853) (by norm_num)
theorem B210221 : Blo 139791 210221 := bbase (se 3 (by rfl) ⟨39416, by rfl⟩ : syracuseStep 210221 = 78833) (by norm_num)
theorem B243005 : Blo 139791 243005 := bbase (se 3 (by rfl) ⟨45563, by rfl⟩ : syracuseStep 243005 = 91127) (by norm_num)
theorem B210245 : Blo 139791 210245 := bbase (se 4 (by rfl) ⟨19710, by rfl⟩ : syracuseStep 210245 = 39421) (by norm_num)
theorem B177481 : Blo 139791 177481 := bbase (se 2 (by rfl) ⟨66555, by rfl⟩ : syracuseStep 177481 = 133111) (by norm_num)
theorem B537941 : Blo 139791 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B210269 : Blo 139791 210269 := bbase (se 3 (by rfl) ⟨39425, by rfl⟩ : syracuseStep 210269 = 78851) (by norm_num)
theorem B210293 : Blo 139791 210293 := bbase (se 5 (by rfl) ⟨9857, by rfl⟩ : syracuseStep 210293 = 19715) (by norm_num)
theorem B210317 : Blo 139791 210317 := bbase (se 3 (by rfl) ⟨39434, by rfl⟩ : syracuseStep 210317 = 78869) (by norm_num)
theorem B144797 : Blo 139791 144797 := bbase (se 3 (by rfl) ⟨27149, by rfl⟩ : syracuseStep 144797 = 54299) (by norm_num)
theorem B210341 : Blo 139791 210341 := bbase (se 4 (by rfl) ⟨19719, by rfl⟩ : syracuseStep 210341 = 39439) (by norm_num)
theorem B210365 : Blo 139791 210365 := bbase (se 3 (by rfl) ⟨39443, by rfl⟩ : syracuseStep 210365 = 78887) (by norm_num)
theorem B210389 : Blo 139791 210389 := bbase (se 7 (by rfl) ⟨2465, by rfl⟩ : syracuseStep 210389 = 4931) (by norm_num)
theorem B210413 : Blo 139791 210413 := bbase (se 3 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 210413 = 78905) (by norm_num)
theorem B177653 : Blo 139791 177653 := bbase (se 5 (by rfl) ⟨8327, by rfl⟩ : syracuseStep 177653 = 16655) (by norm_num)
theorem B210437 : Blo 139791 210437 := bbase (se 4 (by rfl) ⟨19728, by rfl⟩ : syracuseStep 210437 = 39457) (by norm_num)
theorem B407045 : Blo 139791 407045 := bbase (se 4 (by rfl) ⟨38160, by rfl⟩ : syracuseStep 407045 = 76321) (by norm_num)
theorem B210461 : Blo 139791 210461 := bbase (se 3 (by rfl) ⟨39461, by rfl⟩ : syracuseStep 210461 = 78923) (by norm_num)
theorem B177709 : Blo 139791 177709 := bbase (se 3 (by rfl) ⟨33320, by rfl⟩ : syracuseStep 177709 = 66641) (by norm_num)
theorem B210485 : Blo 139791 210485 := bbase (se 5 (by rfl) ⟨9866, by rfl⟩ : syracuseStep 210485 = 19733) (by norm_num)
theorem B210509 : Blo 139791 210509 := bbase (se 3 (by rfl) ⟨39470, by rfl⟩ : syracuseStep 210509 = 78941) (by norm_num)
theorem B472661 : Blo 139791 472661 := bbase (se 8 (by rfl) ⟨2769, by rfl⟩ : syracuseStep 472661 = 5539) (by norm_num)
theorem B603733 : Blo 139791 603733 := bbase (se 8 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 603733 = 7075) (by norm_num)
theorem B210533 : Blo 139791 210533 := bbase (se 4 (by rfl) ⟨19737, by rfl⟩ : syracuseStep 210533 = 39475) (by norm_num)
theorem B603749 : Blo 139791 603749 := bbase (se 4 (by rfl) ⟨56601, by rfl⟩ : syracuseStep 603749 = 113203) (by norm_num)
theorem B210557 : Blo 139791 210557 := bbase (se 3 (by rfl) ⟨39479, by rfl⟩ : syracuseStep 210557 = 78959) (by norm_num)
theorem B177805 : Blo 139791 177805 := bbase (se 3 (by rfl) ⟨33338, by rfl⟩ : syracuseStep 177805 = 66677) (by norm_num)
theorem B210581 : Blo 139791 210581 := bbase (se 6 (by rfl) ⟨4935, by rfl⟩ : syracuseStep 210581 = 9871) (by norm_num)
theorem B210605 : Blo 139791 210605 := bbase (se 3 (by rfl) ⟨39488, by rfl⟩ : syracuseStep 210605 = 78977) (by norm_num)
theorem B210629 : Blo 139791 210629 := bbase (se 4 (by rfl) ⟨19746, by rfl⟩ : syracuseStep 210629 = 39493) (by norm_num)
theorem B210653 : Blo 139791 210653 := bbase (se 3 (by rfl) ⟨39497, by rfl⟩ : syracuseStep 210653 = 78995) (by norm_num)
theorem B341741 : Blo 139791 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B210677 : Blo 139791 210677 := bbase (se 5 (by rfl) ⟨9875, by rfl⟩ : syracuseStep 210677 = 19751) (by norm_num)
theorem B210701 : Blo 139791 210701 := bbase (se 3 (by rfl) ⟨39506, by rfl⟩ : syracuseStep 210701 = 79013) (by norm_num)
theorem B210725 : Blo 139791 210725 := bbase (se 4 (by rfl) ⟨19755, by rfl⟩ : syracuseStep 210725 = 39511) (by norm_num)
theorem B177977 : Blo 139791 177977 := bbase (se 2 (by rfl) ⟨66741, by rfl⟩ : syracuseStep 177977 = 133483) (by norm_num)
theorem B210749 : Blo 139791 210749 := bbase (se 3 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 210749 = 79031) (by norm_num)
theorem B210773 : Blo 139791 210773 := bbase (se 9 (by rfl) ⟨617, by rfl⟩ : syracuseStep 210773 = 1235) (by norm_num)
theorem B210797 : Blo 139791 210797 := bbase (se 3 (by rfl) ⟨39524, by rfl⟩ : syracuseStep 210797 = 79049) (by norm_num)
theorem B178033 : Blo 139791 178033 := bbase (se 2 (by rfl) ⟨66762, by rfl⟩ : syracuseStep 178033 = 133525) (by norm_num)
theorem B210821 : Blo 139791 210821 := bbase (se 4 (by rfl) ⟨19764, by rfl⟩ : syracuseStep 210821 = 39529) (by norm_num)
theorem B210845 : Blo 139791 210845 := bbase (se 3 (by rfl) ⟨39533, by rfl⟩ : syracuseStep 210845 = 79067) (by norm_num)
theorem B243629 : Blo 139791 243629 := bbase (se 3 (by rfl) ⟨45680, by rfl⟩ : syracuseStep 243629 = 91361) (by norm_num)
theorem B210869 : Blo 139791 210869 := bbase (se 5 (by rfl) ⟨9884, by rfl⟩ : syracuseStep 210869 = 19769) (by norm_num)
theorem B210893 : Blo 139791 210893 := bbase (se 3 (by rfl) ⟨39542, by rfl⟩ : syracuseStep 210893 = 79085) (by norm_num)
theorem B178129 : Blo 139791 178129 := bbase (se 2 (by rfl) ⟨66798, by rfl⟩ : syracuseStep 178129 = 133597) (by norm_num)
theorem B210917 : Blo 139791 210917 := bbase (se 4 (by rfl) ⟨19773, by rfl⟩ : syracuseStep 210917 = 39547) (by norm_num)
theorem B210941 : Blo 139791 210941 := bbase (se 3 (by rfl) ⟨39551, by rfl⟩ : syracuseStep 210941 = 79103) (by norm_num)
theorem B473093 : Blo 139791 473093 := bbase (se 4 (by rfl) ⟨44352, by rfl⟩ : syracuseStep 473093 = 88705) (by norm_num)
theorem B210965 : Blo 139791 210965 := bbase (se 6 (by rfl) ⟨4944, by rfl⟩ : syracuseStep 210965 = 9889) (by norm_num)
theorem B210989 : Blo 139791 210989 := bbase (se 3 (by rfl) ⟨39560, by rfl⟩ : syracuseStep 210989 = 79121) (by norm_num)
theorem B211013 : Blo 139791 211013 := bbase (se 4 (by rfl) ⟨19782, by rfl⟩ : syracuseStep 211013 = 39565) (by norm_num)
theorem B211037 : Blo 139791 211037 := bbase (se 3 (by rfl) ⟨39569, by rfl⟩ : syracuseStep 211037 = 79139) (by norm_num)
theorem B211061 : Blo 139791 211061 := bbase (se 5 (by rfl) ⟨9893, by rfl⟩ : syracuseStep 211061 = 19787) (by norm_num)
theorem B178301 : Blo 139791 178301 := bbase (se 3 (by rfl) ⟨33431, by rfl⟩ : syracuseStep 178301 = 66863) (by norm_num)
theorem B211085 : Blo 139791 211085 := bbase (se 3 (by rfl) ⟨39578, by rfl⟩ : syracuseStep 211085 = 79157) (by norm_num)
theorem B211109 : Blo 139791 211109 := bbase (se 4 (by rfl) ⟨19791, by rfl⟩ : syracuseStep 211109 = 39583) (by norm_num)
theorem B407717 : Blo 139791 407717 := bbase (se 4 (by rfl) ⟨38223, by rfl⟩ : syracuseStep 407717 = 76447) (by norm_num)
theorem B178357 : Blo 139791 178357 := bbase (se 5 (by rfl) ⟨8360, by rfl⟩ : syracuseStep 178357 = 16721) (by norm_num)
theorem B211133 : Blo 139791 211133 := bbase (se 3 (by rfl) ⟨39587, by rfl⟩ : syracuseStep 211133 = 79175) (by norm_num)
theorem B506069 : Blo 139791 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B211157 : Blo 139791 211157 := bbase (se 7 (by rfl) ⟨2474, by rfl⟩ : syracuseStep 211157 = 4949) (by norm_num)
theorem B211181 : Blo 139791 211181 := bbase (se 3 (by rfl) ⟨39596, by rfl⟩ : syracuseStep 211181 = 79193) (by norm_num)
theorem B211205 : Blo 139791 211205 := bbase (se 4 (by rfl) ⟨19800, by rfl⟩ : syracuseStep 211205 = 39601) (by norm_num)
theorem B178453 : Blo 139791 178453 := bbase (se 6 (by rfl) ⟨4182, by rfl⟩ : syracuseStep 178453 = 8365) (by norm_num)
theorem B211229 : Blo 139791 211229 := bbase (se 3 (by rfl) ⟨39605, by rfl⟩ : syracuseStep 211229 = 79211) (by norm_num)
theorem B211253 : Blo 139791 211253 := bbase (se 5 (by rfl) ⟨9902, by rfl⟩ : syracuseStep 211253 = 19805) (by norm_num)
theorem B211277 : Blo 139791 211277 := bbase (se 3 (by rfl) ⟨39614, by rfl⟩ : syracuseStep 211277 = 79229) (by norm_num)
theorem B211301 : Blo 139791 211301 := bbase (se 4 (by rfl) ⟨19809, by rfl⟩ : syracuseStep 211301 = 39619) (by norm_num)
theorem B211325 : Blo 139791 211325 := bbase (se 3 (by rfl) ⟨39623, by rfl⟩ : syracuseStep 211325 = 79247) (by norm_num)
theorem B342397 : Blo 139791 342397 := bbase (se 3 (by rfl) ⟨64199, by rfl⟩ : syracuseStep 342397 = 128399) (by norm_num)
theorem B211349 : Blo 139791 211349 := bbase (se 6 (by rfl) ⟨4953, by rfl⟩ : syracuseStep 211349 = 9907) (by norm_num)
theorem B211373 : Blo 139791 211373 := bbase (se 3 (by rfl) ⟨39632, by rfl⟩ : syracuseStep 211373 = 79265) (by norm_num)
theorem B473525 : Blo 139791 473525 := bbase (se 5 (by rfl) ⟨22196, by rfl⟩ : syracuseStep 473525 = 44393) (by norm_num)
theorem B178625 : Blo 139791 178625 := bbase (se 2 (by rfl) ⟨66984, by rfl⟩ : syracuseStep 178625 = 133969) (by norm_num)
theorem B211397 : Blo 139791 211397 := bbase (se 4 (by rfl) ⟨19818, by rfl⟩ : syracuseStep 211397 = 39637) (by norm_num)
theorem B211421 : Blo 139791 211421 := bbase (se 3 (by rfl) ⟨39641, by rfl⟩ : syracuseStep 211421 = 79283) (by norm_num)
theorem B211445 : Blo 139791 211445 := bbase (se 5 (by rfl) ⟨9911, by rfl⟩ : syracuseStep 211445 = 19823) (by norm_num)
theorem B178681 : Blo 139791 178681 := bbase (se 2 (by rfl) ⟨67005, by rfl⟩ : syracuseStep 178681 = 134011) (by norm_num)
theorem B211469 : Blo 139791 211469 := bbase (se 3 (by rfl) ⟨39650, by rfl⟩ : syracuseStep 211469 = 79301) (by norm_num)
theorem B211493 : Blo 139791 211493 := bbase (se 4 (by rfl) ⟨19827, by rfl⟩ : syracuseStep 211493 = 39655) (by norm_num)
theorem B211517 : Blo 139791 211517 := bbase (se 3 (by rfl) ⟨39659, by rfl⟩ : syracuseStep 211517 = 79319) (by norm_num)
theorem B211541 : Blo 139791 211541 := bbase (se 8 (by rfl) ⟨1239, by rfl⟩ : syracuseStep 211541 = 2479) (by norm_num)
theorem B408149 : Blo 139791 408149 := bbase (se 8 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 408149 = 4783) (by norm_num)
theorem B178777 : Blo 139791 178777 := bbase (se 2 (by rfl) ⟨67041, by rfl⟩ : syracuseStep 178777 = 134083) (by norm_num)
theorem B211565 : Blo 139791 211565 := bbase (se 3 (by rfl) ⟨39668, by rfl⟩ : syracuseStep 211565 = 79337) (by norm_num)
theorem B211589 : Blo 139791 211589 := bbase (se 4 (by rfl) ⟨19836, by rfl⟩ : syracuseStep 211589 = 39673) (by norm_num)
theorem B211613 : Blo 139791 211613 := bbase (se 3 (by rfl) ⟨39677, by rfl⟩ : syracuseStep 211613 = 79355) (by norm_num)
theorem B211637 : Blo 139791 211637 := bbase (se 5 (by rfl) ⟨9920, by rfl⟩ : syracuseStep 211637 = 19841) (by norm_num)
theorem B211661 : Blo 139791 211661 := bbase (se 3 (by rfl) ⟨39686, by rfl⟩ : syracuseStep 211661 = 79373) (by norm_num)
theorem B211685 : Blo 139791 211685 := bbase (se 4 (by rfl) ⟨19845, by rfl⟩ : syracuseStep 211685 = 39691) (by norm_num)
theorem B211709 : Blo 139791 211709 := bbase (se 3 (by rfl) ⟨39695, by rfl⟩ : syracuseStep 211709 = 79391) (by norm_num)
theorem B178949 : Blo 139791 178949 := bbase (se 4 (by rfl) ⟨16776, by rfl⟩ : syracuseStep 178949 = 33553) (by norm_num)
theorem B211733 : Blo 139791 211733 := bbase (se 6 (by rfl) ⟨4962, by rfl⟩ : syracuseStep 211733 = 9925) (by norm_num)
theorem B211757 : Blo 139791 211757 := bbase (se 3 (by rfl) ⟨39704, by rfl⟩ : syracuseStep 211757 = 79409) (by norm_num)
theorem B179005 : Blo 139791 179005 := bbase (se 3 (by rfl) ⟨33563, by rfl⟩ : syracuseStep 179005 = 67127) (by norm_num)
theorem B211781 : Blo 139791 211781 := bbase (se 4 (by rfl) ⟨19854, by rfl⟩ : syracuseStep 211781 = 39709) (by norm_num)
theorem B211805 : Blo 139791 211805 := bbase (se 3 (by rfl) ⟨39713, by rfl⟩ : syracuseStep 211805 = 79427) (by norm_num)
theorem B473957 : Blo 139791 473957 := bbase (se 4 (by rfl) ⟨44433, by rfl⟩ : syracuseStep 473957 = 88867) (by norm_num)
theorem B211829 : Blo 139791 211829 := bbase (se 5 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 211829 = 19859) (by norm_num)
theorem B211853 : Blo 139791 211853 := bbase (se 3 (by rfl) ⟨39722, by rfl⟩ : syracuseStep 211853 = 79445) (by norm_num)
theorem B1096597 : Blo 139791 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B179101 : Blo 139791 179101 := bbase (se 3 (by rfl) ⟨33581, by rfl⟩ : syracuseStep 179101 = 67163) (by norm_num)
theorem B211877 : Blo 139791 211877 := bbase (se 4 (by rfl) ⟨19863, by rfl⟩ : syracuseStep 211877 = 39727) (by norm_num)
theorem B211901 : Blo 139791 211901 := bbase (se 3 (by rfl) ⟨39731, by rfl⟩ : syracuseStep 211901 = 79463) (by norm_num)
theorem B211925 : Blo 139791 211925 := bbase (se 7 (by rfl) ⟨2483, by rfl⟩ : syracuseStep 211925 = 4967) (by norm_num)
theorem B211949 : Blo 139791 211949 := bbase (se 3 (by rfl) ⟨39740, by rfl⟩ : syracuseStep 211949 = 79481) (by norm_num)
theorem B769013 : Blo 139791 769013 := bbase (se 5 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 769013 = 72095) (by norm_num)
theorem B343037 : Blo 139791 343037 := bbase (se 3 (by rfl) ⟨64319, by rfl⟩ : syracuseStep 343037 = 128639) (by norm_num)
theorem B211973 : Blo 139791 211973 := bbase (se 4 (by rfl) ⟨19872, by rfl⟩ : syracuseStep 211973 = 39745) (by norm_num)
theorem B1227797 : Blo 139791 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B211997 : Blo 139791 211997 := bbase (se 3 (by rfl) ⟨39749, by rfl⟩ : syracuseStep 211997 = 79499) (by norm_num)
theorem B212021 : Blo 139791 212021 := bbase (se 5 (by rfl) ⟨9938, by rfl⟩ : syracuseStep 212021 = 19877) (by norm_num)
theorem B343109 : Blo 139791 343109 := bbase (se 4 (by rfl) ⟨32166, by rfl⟩ : syracuseStep 343109 = 64333) (by norm_num)
theorem B179273 : Blo 139791 179273 := bbase (se 2 (by rfl) ⟨67227, by rfl⟩ : syracuseStep 179273 = 134455) (by norm_num)
theorem B212045 : Blo 139791 212045 := bbase (se 3 (by rfl) ⟨39758, by rfl⟩ : syracuseStep 212045 = 79517) (by norm_num)
theorem B212069 : Blo 139791 212069 := bbase (se 4 (by rfl) ⟨19881, by rfl⟩ : syracuseStep 212069 = 39763) (by norm_num)
theorem B212093 : Blo 139791 212093 := bbase (se 3 (by rfl) ⟨39767, by rfl⟩ : syracuseStep 212093 = 79535) (by norm_num)
theorem B179329 : Blo 139791 179329 := bbase (se 2 (by rfl) ⟨67248, by rfl⟩ : syracuseStep 179329 = 134497) (by norm_num)
theorem B212117 : Blo 139791 212117 := bbase (se 6 (by rfl) ⟨4971, by rfl⟩ : syracuseStep 212117 = 9943) (by norm_num)
theorem B212141 : Blo 139791 212141 := bbase (se 3 (by rfl) ⟨39776, by rfl⟩ : syracuseStep 212141 = 79553) (by norm_num)
theorem B212165 : Blo 139791 212165 := bbase (se 4 (by rfl) ⟨19890, by rfl⟩ : syracuseStep 212165 = 39781) (by norm_num)
theorem B212189 : Blo 139791 212189 := bbase (se 3 (by rfl) ⟨39785, by rfl⟩ : syracuseStep 212189 = 79571) (by norm_num)
theorem B179425 : Blo 139791 179425 := bbase (se 2 (by rfl) ⟨67284, by rfl⟩ : syracuseStep 179425 = 134569) (by norm_num)
theorem B212213 : Blo 139791 212213 := bbase (se 5 (by rfl) ⟨9947, by rfl⟩ : syracuseStep 212213 = 19895) (by norm_num)
theorem B212237 : Blo 139791 212237 := bbase (se 3 (by rfl) ⟨39794, by rfl⟩ : syracuseStep 212237 = 79589) (by norm_num)
theorem B474389 : Blo 139791 474389 := bbase (se 6 (by rfl) ⟨11118, by rfl⟩ : syracuseStep 474389 = 22237) (by norm_num)
theorem B212261 : Blo 139791 212261 := bbase (se 4 (by rfl) ⟨19899, by rfl⟩ : syracuseStep 212261 = 39799) (by norm_num)
theorem B212285 : Blo 139791 212285 := bbase (se 3 (by rfl) ⟨39803, by rfl⟩ : syracuseStep 212285 = 79607) (by norm_num)
theorem B408901 : Blo 139791 408901 := bbase (se 4 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 408901 = 76669) (by norm_num)
theorem B212309 : Blo 139791 212309 := bbase (se 11 (by rfl) ⟨155, by rfl⟩ : syracuseStep 212309 = 311) (by norm_num)
theorem B212333 : Blo 139791 212333 := bbase (se 3 (by rfl) ⟨39812, by rfl⟩ : syracuseStep 212333 = 79625) (by norm_num)
theorem B212357 : Blo 139791 212357 := bbase (se 4 (by rfl) ⟨19908, by rfl⟩ : syracuseStep 212357 = 39817) (by norm_num)
theorem B179597 : Blo 139791 179597 := bbase (se 3 (by rfl) ⟨33674, by rfl⟩ : syracuseStep 179597 = 67349) (by norm_num)
theorem B540053 : Blo 139791 540053 := bbase (se 6 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 540053 = 25315) (by norm_num)
theorem B212381 : Blo 139791 212381 := bbase (se 3 (by rfl) ⟨39821, by rfl⟩ : syracuseStep 212381 = 79643) (by norm_num)
theorem B212405 : Blo 139791 212405 := bbase (se 5 (by rfl) ⟨9956, by rfl⟩ : syracuseStep 212405 = 19913) (by norm_num)
theorem B179653 : Blo 139791 179653 := bbase (se 4 (by rfl) ⟨16842, by rfl⟩ : syracuseStep 179653 = 33685) (by norm_num)
theorem B343493 : Blo 139791 343493 := bbase (se 4 (by rfl) ⟨32202, by rfl⟩ : syracuseStep 343493 = 64405) (by norm_num)
theorem B212429 : Blo 139791 212429 := bbase (se 3 (by rfl) ⟨39830, by rfl⟩ : syracuseStep 212429 = 79661) (by norm_num)
theorem B212453 : Blo 139791 212453 := bbase (se 4 (by rfl) ⟨19917, by rfl⟩ : syracuseStep 212453 = 39835) (by norm_num)
theorem B212477 : Blo 139791 212477 := bbase (se 3 (by rfl) ⟨39839, by rfl⟩ : syracuseStep 212477 = 79679) (by norm_num)
theorem B212501 : Blo 139791 212501 := bbase (se 6 (by rfl) ⟨4980, by rfl⟩ : syracuseStep 212501 = 9961) (by norm_num)
theorem B179749 : Blo 139791 179749 := bbase (se 4 (by rfl) ⟨16851, by rfl⟩ : syracuseStep 179749 = 33703) (by norm_num)
theorem B212525 : Blo 139791 212525 := bbase (se 3 (by rfl) ⟨39848, by rfl⟩ : syracuseStep 212525 = 79697) (by norm_num)
theorem B212549 : Blo 139791 212549 := bbase (se 4 (by rfl) ⟨19926, by rfl⟩ : syracuseStep 212549 = 39853) (by norm_num)
theorem B212573 : Blo 139791 212573 := bbase (se 3 (by rfl) ⟨39857, by rfl⟩ : syracuseStep 212573 = 79715) (by norm_num)
theorem B212597 : Blo 139791 212597 := bbase (se 5 (by rfl) ⟨9965, by rfl⟩ : syracuseStep 212597 = 19931) (by norm_num)
theorem B212621 : Blo 139791 212621 := bbase (se 3 (by rfl) ⟨39866, by rfl⟩ : syracuseStep 212621 = 79733) (by norm_num)
theorem B212645 : Blo 139791 212645 := bbase (se 4 (by rfl) ⟨19935, by rfl⟩ : syracuseStep 212645 = 39871) (by norm_num)
theorem B245413 : Blo 139791 245413 := bbase (se 4 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 245413 = 46015) (by norm_num)
theorem B540341 : Blo 139791 540341 := bbase (se 5 (by rfl) ⟨25328, by rfl⟩ : syracuseStep 540341 = 50657) (by norm_num)
theorem B212669 : Blo 139791 212669 := bbase (se 3 (by rfl) ⟨39875, by rfl⟩ : syracuseStep 212669 = 79751) (by norm_num)
theorem B474821 : Blo 139791 474821 := bbase (se 4 (by rfl) ⟨44514, by rfl⟩ : syracuseStep 474821 = 89029) (by norm_num)
theorem B179921 : Blo 139791 179921 := bbase (se 2 (by rfl) ⟨67470, by rfl⟩ : syracuseStep 179921 = 134941) (by norm_num)
theorem B212693 : Blo 139791 212693 := bbase (se 7 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 212693 = 4985) (by norm_num)
theorem B343781 : Blo 139791 343781 := bbase (se 4 (by rfl) ⟨32229, by rfl⟩ : syracuseStep 343781 = 64459) (by norm_num)
theorem B212717 : Blo 139791 212717 := bbase (se 3 (by rfl) ⟨39884, by rfl⟩ : syracuseStep 212717 = 79769) (by norm_num)
theorem B212741 : Blo 139791 212741 := bbase (se 4 (by rfl) ⟨19944, by rfl⟩ : syracuseStep 212741 = 39889) (by norm_num)
theorem B179977 : Blo 139791 179977 := bbase (se 2 (by rfl) ⟨67491, by rfl⟩ : syracuseStep 179977 = 134983) (by norm_num)
theorem B212765 : Blo 139791 212765 := bbase (se 3 (by rfl) ⟨39893, by rfl⟩ : syracuseStep 212765 = 79787) (by norm_num)
theorem B212789 : Blo 139791 212789 := bbase (se 5 (by rfl) ⟨9974, by rfl⟩ : syracuseStep 212789 = 19949) (by norm_num)
theorem B606005 : Blo 139791 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B212813 : Blo 139791 212813 := bbase (se 3 (by rfl) ⟨39902, by rfl⟩ : syracuseStep 212813 = 79805) (by norm_num)
theorem B212837 : Blo 139791 212837 := bbase (se 4 (by rfl) ⟨19953, by rfl⟩ : syracuseStep 212837 = 39907) (by norm_num)
theorem B180073 : Blo 139791 180073 := bbase (se 2 (by rfl) ⟨67527, by rfl⟩ : syracuseStep 180073 = 135055) (by norm_num)
theorem B212861 : Blo 139791 212861 := bbase (se 3 (by rfl) ⟨39911, by rfl⟩ : syracuseStep 212861 = 79823) (by norm_num)
theorem B212885 : Blo 139791 212885 := bbase (se 6 (by rfl) ⟨4989, by rfl⟩ : syracuseStep 212885 = 9979) (by norm_num)
theorem B212909 : Blo 139791 212909 := bbase (se 3 (by rfl) ⟨39920, by rfl⟩ : syracuseStep 212909 = 79841) (by norm_num)
theorem B507829 : Blo 139791 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B212933 : Blo 139791 212933 := bbase (se 4 (by rfl) ⟨19962, by rfl⟩ : syracuseStep 212933 = 39925) (by norm_num)
theorem B212957 : Blo 139791 212957 := bbase (se 3 (by rfl) ⟨39929, by rfl⟩ : syracuseStep 212957 = 79859) (by norm_num)
theorem B212981 : Blo 139791 212981 := bbase (se 5 (by rfl) ⟨9983, by rfl⟩ : syracuseStep 212981 = 19967) (by norm_num)
theorem B213005 : Blo 139791 213005 := bbase (se 3 (by rfl) ⟨39938, by rfl⟩ : syracuseStep 213005 = 79877) (by norm_num)
theorem B180245 : Blo 139791 180245 := bbase (se 6 (by rfl) ⟨4224, by rfl⟩ : syracuseStep 180245 = 8449) (by norm_num)
theorem B213029 : Blo 139791 213029 := bbase (se 4 (by rfl) ⟨19971, by rfl⟩ : syracuseStep 213029 = 39943) (by norm_num)
theorem B213053 : Blo 139791 213053 := bbase (se 3 (by rfl) ⟨39947, by rfl⟩ : syracuseStep 213053 = 79895) (by norm_num)
theorem B180301 : Blo 139791 180301 := bbase (se 3 (by rfl) ⟨33806, by rfl⟩ : syracuseStep 180301 = 67613) (by norm_num)
theorem B213077 : Blo 139791 213077 := bbase (se 8 (by rfl) ⟨1248, by rfl⟩ : syracuseStep 213077 = 2497) (by norm_num)
theorem B213101 : Blo 139791 213101 := bbase (se 3 (by rfl) ⟨39956, by rfl⟩ : syracuseStep 213101 = 79913) (by norm_num)
theorem B475253 : Blo 139791 475253 := bbase (se 5 (by rfl) ⟨22277, by rfl⟩ : syracuseStep 475253 = 44555) (by norm_num)
theorem B213125 : Blo 139791 213125 := bbase (se 4 (by rfl) ⟨19980, by rfl⟩ : syracuseStep 213125 = 39961) (by norm_num)
theorem B213149 : Blo 139791 213149 := bbase (se 3 (by rfl) ⟨39965, by rfl⟩ : syracuseStep 213149 = 79931) (by norm_num)
theorem B180397 : Blo 139791 180397 := bbase (se 3 (by rfl) ⟨33824, by rfl⟩ : syracuseStep 180397 = 67649) (by norm_num)
theorem B213173 : Blo 139791 213173 := bbase (se 5 (by rfl) ⟨9992, by rfl⟩ : syracuseStep 213173 = 19985) (by norm_num)
theorem B213197 : Blo 139791 213197 := bbase (se 3 (by rfl) ⟨39974, by rfl⟩ : syracuseStep 213197 = 79949) (by norm_num)
theorem B213221 : Blo 139791 213221 := bbase (se 4 (by rfl) ⟨19989, by rfl⟩ : syracuseStep 213221 = 39979) (by norm_num)
theorem B213245 : Blo 139791 213245 := bbase (se 3 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 213245 = 79967) (by norm_num)
theorem B213269 : Blo 139791 213269 := bbase (se 6 (by rfl) ⟨4998, by rfl⟩ : syracuseStep 213269 = 9997) (by norm_num)
theorem B213293 : Blo 139791 213293 := bbase (se 3 (by rfl) ⟨39992, by rfl⟩ : syracuseStep 213293 = 79985) (by norm_num)
theorem B213317 : Blo 139791 213317 := bbase (se 4 (by rfl) ⟨19998, by rfl⟩ : syracuseStep 213317 = 39997) (by norm_num)
theorem B180569 : Blo 139791 180569 := bbase (se 2 (by rfl) ⟨67713, by rfl⟩ : syracuseStep 180569 = 135427) (by norm_num)
theorem B213341 : Blo 139791 213341 := bbase (se 3 (by rfl) ⟨40001, by rfl⟩ : syracuseStep 213341 = 80003) (by norm_num)
theorem B213365 : Blo 139791 213365 := bbase (se 5 (by rfl) ⟨10001, by rfl⟩ : syracuseStep 213365 = 20003) (by norm_num)
theorem B213389 : Blo 139791 213389 := bbase (se 3 (by rfl) ⟨40010, by rfl⟩ : syracuseStep 213389 = 80021) (by norm_num)
theorem B180625 : Blo 139791 180625 := bbase (se 2 (by rfl) ⟨67734, by rfl⟩ : syracuseStep 180625 = 135469) (by norm_num)
theorem B213413 : Blo 139791 213413 := bbase (se 4 (by rfl) ⟨20007, by rfl⟩ : syracuseStep 213413 = 40015) (by norm_num)
theorem B213437 : Blo 139791 213437 := bbase (se 3 (by rfl) ⟨40019, by rfl⟩ : syracuseStep 213437 = 80039) (by norm_num)
theorem B213445 : Blo 139791 213445 := bbase (se 4 (by rfl) ⟨20010, by rfl⟩ : syracuseStep 213445 = 40021) (by norm_num)
theorem B213461 : Blo 139791 213461 := bbase (se 7 (by rfl) ⟨2501, by rfl⟩ : syracuseStep 213461 = 5003) (by norm_num)
theorem B213485 : Blo 139791 213485 := bbase (se 3 (by rfl) ⟨40028, by rfl⟩ : syracuseStep 213485 = 80057) (by norm_num)
theorem B180721 : Blo 139791 180721 := bbase (se 2 (by rfl) ⟨67770, by rfl⟩ : syracuseStep 180721 = 135541) (by norm_num)
theorem B213509 : Blo 139791 213509 := bbase (se 4 (by rfl) ⟨20016, by rfl⟩ : syracuseStep 213509 = 40033) (by norm_num)
theorem B213533 : Blo 139791 213533 := bbase (se 3 (by rfl) ⟨40037, by rfl⟩ : syracuseStep 213533 = 80075) (by norm_num)
theorem B475685 : Blo 139791 475685 := bbase (se 4 (by rfl) ⟨44595, by rfl⟩ : syracuseStep 475685 = 89191) (by norm_num)
theorem B213557 : Blo 139791 213557 := bbase (se 5 (by rfl) ⟨10010, by rfl⟩ : syracuseStep 213557 = 20021) (by norm_num)
theorem B213581 : Blo 139791 213581 := bbase (se 3 (by rfl) ⟨40046, by rfl⟩ : syracuseStep 213581 = 80093) (by norm_num)
theorem B213605 : Blo 139791 213605 := bbase (se 4 (by rfl) ⟨20025, by rfl⟩ : syracuseStep 213605 = 40051) (by norm_num)
theorem B213629 : Blo 139791 213629 := bbase (se 3 (by rfl) ⟨40055, by rfl⟩ : syracuseStep 213629 = 80111) (by norm_num)
theorem B213653 : Blo 139791 213653 := bbase (se 6 (by rfl) ⟨5007, by rfl⟩ : syracuseStep 213653 = 10015) (by norm_num)
theorem B180893 : Blo 139791 180893 := bbase (se 3 (by rfl) ⟨33917, by rfl⟩ : syracuseStep 180893 = 67835) (by norm_num)
theorem B213677 : Blo 139791 213677 := bbase (se 3 (by rfl) ⟨40064, by rfl⟩ : syracuseStep 213677 = 80129) (by norm_num)
theorem B770741 : Blo 139791 770741 := bbase (se 5 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 770741 = 72257) (by norm_num)
theorem B213701 : Blo 139791 213701 := bbase (se 4 (by rfl) ⟨20034, by rfl⟩ : syracuseStep 213701 = 40069) (by norm_num)
theorem B180949 : Blo 139791 180949 := bbase (se 7 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 180949 = 4241) (by norm_num)
theorem B213725 : Blo 139791 213725 := bbase (se 3 (by rfl) ⟨40073, by rfl⟩ : syracuseStep 213725 = 80147) (by norm_num)
theorem B213749 : Blo 139791 213749 := bbase (se 5 (by rfl) ⟨10019, by rfl⟩ : syracuseStep 213749 = 20039) (by norm_num)
theorem B213773 : Blo 139791 213773 := bbase (se 3 (by rfl) ⟨40082, by rfl⟩ : syracuseStep 213773 = 80165) (by norm_num)
theorem B213797 : Blo 139791 213797 := bbase (se 4 (by rfl) ⟨20043, by rfl⟩ : syracuseStep 213797 = 40087) (by norm_num)
theorem B181045 : Blo 139791 181045 := bbase (se 5 (by rfl) ⟨8486, by rfl⟩ : syracuseStep 181045 = 16973) (by norm_num)
theorem B213821 : Blo 139791 213821 := bbase (se 3 (by rfl) ⟨40091, by rfl⟩ : syracuseStep 213821 = 80183) (by norm_num)
theorem B213845 : Blo 139791 213845 := bbase (se 9 (by rfl) ⟨626, by rfl⟩ : syracuseStep 213845 = 1253) (by norm_num)
theorem B541525 : Blo 139791 541525 := bbase (se 9 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 541525 = 3173) (by norm_num)
theorem B213869 : Blo 139791 213869 := bbase (se 3 (by rfl) ⟨40100, by rfl⟩ : syracuseStep 213869 = 80201) (by norm_num)
theorem B213893 : Blo 139791 213893 := bbase (se 4 (by rfl) ⟨20052, by rfl⟩ : syracuseStep 213893 = 40105) (by norm_num)
theorem B213917 : Blo 139791 213917 := bbase (se 3 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 213917 = 80219) (by norm_num)
theorem B508837 : Blo 139791 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B213941 : Blo 139791 213941 := bbase (se 5 (by rfl) ⟨10028, by rfl⟩ : syracuseStep 213941 = 20057) (by norm_num)
theorem B213965 : Blo 139791 213965 := bbase (se 3 (by rfl) ⟨40118, by rfl⟩ : syracuseStep 213965 = 80237) (by norm_num)
theorem B476117 : Blo 139791 476117 := bbase (se 7 (by rfl) ⟨5579, by rfl⟩ : syracuseStep 476117 = 11159) (by norm_num)
theorem B181217 : Blo 139791 181217 := bbase (se 2 (by rfl) ⟨67956, by rfl⟩ : syracuseStep 181217 = 135913) (by norm_num)
theorem B213989 : Blo 139791 213989 := bbase (se 4 (by rfl) ⟨20061, by rfl⟩ : syracuseStep 213989 = 40123) (by norm_num)
theorem B214013 : Blo 139791 214013 := bbase (se 3 (by rfl) ⟨40127, by rfl⟩ : syracuseStep 214013 = 80255) (by norm_num)
theorem B214037 : Blo 139791 214037 := bbase (se 6 (by rfl) ⟨5016, by rfl⟩ : syracuseStep 214037 = 10033) (by norm_num)
theorem B181273 : Blo 139791 181273 := bbase (se 2 (by rfl) ⟨67977, by rfl⟩ : syracuseStep 181273 = 135955) (by norm_num)
theorem B214061 : Blo 139791 214061 := bbase (se 3 (by rfl) ⟨40136, by rfl⟩ : syracuseStep 214061 = 80273) (by norm_num)
theorem B214085 : Blo 139791 214085 := bbase (se 4 (by rfl) ⟨20070, by rfl⟩ : syracuseStep 214085 = 40141) (by norm_num)
theorem B214109 : Blo 139791 214109 := bbase (se 3 (by rfl) ⟨40145, by rfl⟩ : syracuseStep 214109 = 80291) (by norm_num)
theorem B214133 : Blo 139791 214133 := bbase (se 5 (by rfl) ⟨10037, by rfl⟩ : syracuseStep 214133 = 20075) (by norm_num)
theorem B181369 : Blo 139791 181369 := bbase (se 2 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 181369 = 136027) (by norm_num)
theorem B541829 : Blo 139791 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B214157 : Blo 139791 214157 := bbase (se 3 (by rfl) ⟨40154, by rfl⟩ : syracuseStep 214157 = 80309) (by norm_num)
theorem B214181 : Blo 139791 214181 := bbase (se 4 (by rfl) ⟨20079, by rfl⟩ : syracuseStep 214181 = 40159) (by norm_num)
theorem B214205 : Blo 139791 214205 := bbase (se 3 (by rfl) ⟨40163, by rfl⟩ : syracuseStep 214205 = 80327) (by norm_num)
theorem B214229 : Blo 139791 214229 := bbase (se 7 (by rfl) ⟨2510, by rfl⟩ : syracuseStep 214229 = 5021) (by norm_num)
theorem B214253 : Blo 139791 214253 := bbase (se 3 (by rfl) ⟨40172, by rfl⟩ : syracuseStep 214253 = 80345) (by norm_num)
theorem B214277 : Blo 139791 214277 := bbase (se 4 (by rfl) ⟨20088, by rfl⟩ : syracuseStep 214277 = 40177) (by norm_num)
theorem B214301 : Blo 139791 214301 := bbase (se 3 (by rfl) ⟨40181, by rfl⟩ : syracuseStep 214301 = 80363) (by norm_num)
theorem B181541 : Blo 139791 181541 := bbase (se 4 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 181541 = 34039) (by norm_num)
theorem B214325 : Blo 139791 214325 := bbase (se 5 (by rfl) ⟨10046, by rfl⟩ : syracuseStep 214325 = 20093) (by norm_num)
theorem B214349 : Blo 139791 214349 := bbase (se 3 (by rfl) ⟨40190, by rfl⟩ : syracuseStep 214349 = 80381) (by norm_num)
theorem B181597 : Blo 139791 181597 := bbase (se 3 (by rfl) ⟨34049, by rfl⟩ : syracuseStep 181597 = 68099) (by norm_num)
theorem B214373 : Blo 139791 214373 := bbase (se 4 (by rfl) ⟨20097, by rfl⟩ : syracuseStep 214373 = 40195) (by norm_num)
theorem B214397 : Blo 139791 214397 := bbase (se 3 (by rfl) ⟨40199, by rfl⟩ : syracuseStep 214397 = 80399) (by norm_num)
theorem B378245 : Blo 139791 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B476549 : Blo 139791 476549 := bbase (se 4 (by rfl) ⟨44676, by rfl⟩ : syracuseStep 476549 = 89353) (by norm_num)
theorem B214421 : Blo 139791 214421 := bbase (se 6 (by rfl) ⟨5025, by rfl⟩ : syracuseStep 214421 = 10051) (by norm_num)
theorem B214445 : Blo 139791 214445 := bbase (se 3 (by rfl) ⟨40208, by rfl⟩ : syracuseStep 214445 = 80417) (by norm_num)
theorem B181693 : Blo 139791 181693 := bbase (se 3 (by rfl) ⟨34067, by rfl⟩ : syracuseStep 181693 = 68135) (by norm_num)
theorem B214469 : Blo 139791 214469 := bbase (se 4 (by rfl) ⟨20106, by rfl⟩ : syracuseStep 214469 = 40213) (by norm_num)
theorem B214493 : Blo 139791 214493 := bbase (se 3 (by rfl) ⟨40217, by rfl⟩ : syracuseStep 214493 = 80435) (by norm_num)
theorem B214517 : Blo 139791 214517 := bbase (se 5 (by rfl) ⟨10055, by rfl⟩ : syracuseStep 214517 = 20111) (by norm_num)
theorem B214541 : Blo 139791 214541 := bbase (se 3 (by rfl) ⟨40226, by rfl⟩ : syracuseStep 214541 = 80453) (by norm_num)
theorem B214565 : Blo 139791 214565 := bbase (se 4 (by rfl) ⟨20115, by rfl⟩ : syracuseStep 214565 = 40231) (by norm_num)
theorem B214589 : Blo 139791 214589 := bbase (se 3 (by rfl) ⟨40235, by rfl⟩ : syracuseStep 214589 = 80471) (by norm_num)
theorem B214613 : Blo 139791 214613 := bbase (se 8 (by rfl) ⟨1257, by rfl⟩ : syracuseStep 214613 = 2515) (by norm_num)
theorem B181865 : Blo 139791 181865 := bbase (se 2 (by rfl) ⟨68199, by rfl⟩ : syracuseStep 181865 = 136399) (by norm_num)
theorem B214637 : Blo 139791 214637 := bbase (se 3 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 214637 = 80489) (by norm_num)
theorem B345725 : Blo 139791 345725 := bbase (se 3 (by rfl) ⟨64823, by rfl⟩ : syracuseStep 345725 = 129647) (by norm_num)
theorem B214661 : Blo 139791 214661 := bbase (se 4 (by rfl) ⟨20124, by rfl⟩ : syracuseStep 214661 = 40249) (by norm_num)
theorem B214685 : Blo 139791 214685 := bbase (se 3 (by rfl) ⟨40253, by rfl⟩ : syracuseStep 214685 = 80507) (by norm_num)
theorem B181921 : Blo 139791 181921 := bbase (se 2 (by rfl) ⟨68220, by rfl⟩ : syracuseStep 181921 = 136441) (by norm_num)
theorem B214709 : Blo 139791 214709 := bbase (se 5 (by rfl) ⟨10064, by rfl⟩ : syracuseStep 214709 = 20129) (by norm_num)
theorem B214733 : Blo 139791 214733 := bbase (se 3 (by rfl) ⟨40262, by rfl⟩ : syracuseStep 214733 = 80525) (by norm_num)
theorem B214757 : Blo 139791 214757 := bbase (se 4 (by rfl) ⟨20133, by rfl⟩ : syracuseStep 214757 = 40267) (by norm_num)
theorem B214781 : Blo 139791 214781 := bbase (se 3 (by rfl) ⟨40271, by rfl⟩ : syracuseStep 214781 = 80543) (by norm_num)
theorem B214805 : Blo 139791 214805 := bbase (se 6 (by rfl) ⟨5034, by rfl⟩ : syracuseStep 214805 = 10069) (by norm_num)
theorem B149293 : Blo 139791 149293 := bbase (se 3 (by rfl) ⟨27992, by rfl⟩ : syracuseStep 149293 = 55985) (by norm_num)
theorem B214829 : Blo 139791 214829 := bbase (se 3 (by rfl) ⟨40280, by rfl⟩ : syracuseStep 214829 = 80561) (by norm_num)
theorem B149297 : Blo 139791 149297 := bbase (se 2 (by rfl) ⟨55986, by rfl⟩ : syracuseStep 149297 = 111973) (by norm_num)
theorem B476981 : Blo 139791 476981 := bbase (se 5 (by rfl) ⟨22358, by rfl⟩ : syracuseStep 476981 = 44717) (by norm_num)
theorem B214853 : Blo 139791 214853 := bbase (se 4 (by rfl) ⟨20142, by rfl⟩ : syracuseStep 214853 = 40285) (by norm_num)
theorem B149321 : Blo 139791 149321 := bbase (se 2 (by rfl) ⟨55995, by rfl⟩ : syracuseStep 149321 = 111991) (by norm_num)
theorem B280397 : Blo 139791 280397 := bbase (se 3 (by rfl) ⟨52574, by rfl⟩ : syracuseStep 280397 = 105149) (by norm_num)
theorem B214877 : Blo 139791 214877 := bbase (se 3 (by rfl) ⟨40289, by rfl⟩ : syracuseStep 214877 = 80579) (by norm_num)
theorem B804725 : Blo 139791 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B214901 : Blo 139791 214901 := bbase (se 5 (by rfl) ⟨10073, by rfl⟩ : syracuseStep 214901 = 20147) (by norm_num)
theorem B214925 : Blo 139791 214925 := bbase (se 3 (by rfl) ⟨40298, by rfl⟩ : syracuseStep 214925 = 80597) (by norm_num)
theorem B214949 : Blo 139791 214949 := bbase (se 4 (by rfl) ⟨20151, by rfl⟩ : syracuseStep 214949 = 40303) (by norm_num)
theorem B214973 : Blo 139791 214973 := bbase (se 3 (by rfl) ⟨40307, by rfl⟩ : syracuseStep 214973 = 80615) (by norm_num)
theorem B214997 : Blo 139791 214997 := bbase (se 7 (by rfl) ⟨2519, by rfl⟩ : syracuseStep 214997 = 5039) (by norm_num)
theorem B215021 : Blo 139791 215021 := bbase (se 3 (by rfl) ⟨40316, by rfl⟩ : syracuseStep 215021 = 80633) (by norm_num)
theorem B215045 : Blo 139791 215045 := bbase (se 4 (by rfl) ⟨20160, by rfl⟩ : syracuseStep 215045 = 40321) (by norm_num)
theorem B215069 : Blo 139791 215069 := bbase (se 3 (by rfl) ⟨40325, by rfl⟩ : syracuseStep 215069 = 80651) (by norm_num)
theorem B215093 : Blo 139791 215093 := bbase (se 5 (by rfl) ⟨10082, by rfl⟩ : syracuseStep 215093 = 20165) (by norm_num)
theorem B215117 : Blo 139791 215117 := bbase (se 3 (by rfl) ⟨40334, by rfl⟩ : syracuseStep 215117 = 80669) (by norm_num)
theorem B247901 : Blo 139791 247901 := bbase (se 3 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 247901 = 92963) (by norm_num)
theorem B215141 : Blo 139791 215141 := bbase (se 4 (by rfl) ⟨20169, by rfl⟩ : syracuseStep 215141 = 40339) (by norm_num)
theorem B215165 : Blo 139791 215165 := bbase (se 3 (by rfl) ⟨40343, by rfl⟩ : syracuseStep 215165 = 80687) (by norm_num)
theorem B215189 : Blo 139791 215189 := bbase (se 6 (by rfl) ⟨5043, by rfl⟩ : syracuseStep 215189 = 10087) (by norm_num)
theorem B215213 : Blo 139791 215213 := bbase (se 3 (by rfl) ⟨40352, by rfl⟩ : syracuseStep 215213 = 80705) (by norm_num)
theorem B215237 : Blo 139791 215237 := bbase (se 4 (by rfl) ⟨20178, by rfl⟩ : syracuseStep 215237 = 40357) (by norm_num)
theorem B215245 : Blo 139791 215245 := bbase (se 3 (by rfl) ⟨40358, by rfl⟩ : syracuseStep 215245 = 80717) (by norm_num)
theorem B215261 : Blo 139791 215261 := bbase (se 3 (by rfl) ⟨40361, by rfl⟩ : syracuseStep 215261 = 80723) (by norm_num)
theorem B477413 : Blo 139791 477413 := bbase (se 4 (by rfl) ⟨44757, by rfl⟩ : syracuseStep 477413 = 89515) (by norm_num)
theorem B215285 : Blo 139791 215285 := bbase (se 5 (by rfl) ⟨10091, by rfl⟩ : syracuseStep 215285 = 20183) (by norm_num)
theorem B182521 : Blo 139791 182521 := bbase (se 2 (by rfl) ⟨68445, by rfl⟩ : syracuseStep 182521 = 136891) (by norm_num)
theorem B215309 : Blo 139791 215309 := bbase (se 3 (by rfl) ⟨40370, by rfl⟩ : syracuseStep 215309 = 80741) (by norm_num)
theorem B215333 : Blo 139791 215333 := bbase (se 4 (by rfl) ⟨20187, by rfl⟩ : syracuseStep 215333 = 40375) (by norm_num)
theorem B215357 : Blo 139791 215357 := bbase (se 3 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 215357 = 80759) (by norm_num)
theorem B215381 : Blo 139791 215381 := bbase (se 10 (by rfl) ⟨315, by rfl⟩ : syracuseStep 215381 = 631) (by norm_num)
theorem B149861 : Blo 139791 149861 := bbase (se 4 (by rfl) ⟨14049, by rfl⟩ : syracuseStep 149861 = 28099) (by norm_num)
theorem B215405 : Blo 139791 215405 := bbase (se 3 (by rfl) ⟨40388, by rfl⟩ : syracuseStep 215405 = 80777) (by norm_num)
theorem B215429 : Blo 139791 215429 := bbase (se 4 (by rfl) ⟨20196, by rfl⟩ : syracuseStep 215429 = 40393) (by norm_num)
theorem B215453 : Blo 139791 215453 := bbase (se 3 (by rfl) ⟨40397, by rfl⟩ : syracuseStep 215453 = 80795) (by norm_num)
theorem B215477 : Blo 139791 215477 := bbase (se 5 (by rfl) ⟨10100, by rfl⟩ : syracuseStep 215477 = 20201) (by norm_num)
theorem B215501 : Blo 139791 215501 := bbase (se 3 (by rfl) ⟨40406, by rfl⟩ : syracuseStep 215501 = 80813) (by norm_num)
theorem B215525 : Blo 139791 215525 := bbase (se 4 (by rfl) ⟨20205, by rfl⟩ : syracuseStep 215525 = 40411) (by norm_num)
theorem B215549 : Blo 139791 215549 := bbase (se 3 (by rfl) ⟨40415, by rfl⟩ : syracuseStep 215549 = 80831) (by norm_num)
theorem B215573 : Blo 139791 215573 := bbase (se 6 (by rfl) ⟨5052, by rfl⟩ : syracuseStep 215573 = 10105) (by norm_num)
theorem B150049 : Blo 139791 150049 := bbase (se 2 (by rfl) ⟨56268, by rfl⟩ : syracuseStep 150049 = 112537) (by norm_num)
theorem B215597 : Blo 139791 215597 := bbase (se 3 (by rfl) ⟨40424, by rfl⟩ : syracuseStep 215597 = 80849) (by norm_num)
theorem B215621 : Blo 139791 215621 := bbase (se 4 (by rfl) ⟨20214, by rfl⟩ : syracuseStep 215621 = 40429) (by norm_num)
theorem B215645 : Blo 139791 215645 := bbase (se 3 (by rfl) ⟨40433, by rfl⟩ : syracuseStep 215645 = 80867) (by norm_num)
theorem B215669 : Blo 139791 215669 := bbase (se 5 (by rfl) ⟨10109, by rfl⟩ : syracuseStep 215669 = 20219) (by norm_num)
theorem B477845 : Blo 139791 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B1493653 : Blo 139791 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B216029 : Blo 139791 216029 := bbase (se 3 (by rfl) ⟨40505, by rfl⟩ : syracuseStep 216029 = 81011) (by norm_num)
theorem B248845 : Blo 139791 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B805909 : Blo 139791 805909 := bbase (se 6 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 805909 = 37777) (by norm_num)
theorem B478277 : Blo 139791 478277 := bbase (se 4 (by rfl) ⟨44838, by rfl⟩ : syracuseStep 478277 = 89677) (by norm_num)
theorem B314549 : Blo 139791 314549 := bbase (se 5 (by rfl) ⟨14744, by rfl⟩ : syracuseStep 314549 = 29489) (by norm_num)
theorem B543941 : Blo 139791 543941 := bbase (se 4 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 543941 = 101989) (by norm_num)
theorem B314621 : Blo 139791 314621 := bbase (se 3 (by rfl) ⟨58991, by rfl⟩ : syracuseStep 314621 = 117983) (by norm_num)
theorem B642325 : Blo 139791 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B314693 : Blo 139791 314693 := bbase (se 4 (by rfl) ⟨29502, by rfl⟩ : syracuseStep 314693 = 59005) (by norm_num)
theorem B150869 : Blo 139791 150869 := bbase (se 11 (by rfl) ⟨110, by rfl⟩ : syracuseStep 150869 = 221) (by norm_num)
theorem B314765 : Blo 139791 314765 := bbase (se 3 (by rfl) ⟨59018, by rfl⟩ : syracuseStep 314765 = 118037) (by norm_num)
theorem B216461 : Blo 139791 216461 := bbase (se 3 (by rfl) ⟨40586, by rfl⟩ : syracuseStep 216461 = 81173) (by norm_num)
theorem B314837 : Blo 139791 314837 := bbase (se 7 (by rfl) ⟨3689, by rfl⟩ : syracuseStep 314837 = 7379) (by norm_num)
theorem B544229 : Blo 139791 544229 := bbase (se 4 (by rfl) ⟨51021, by rfl⟩ : syracuseStep 544229 = 102043) (by norm_num)
theorem B478709 : Blo 139791 478709 := bbase (se 5 (by rfl) ⟨22439, by rfl⟩ : syracuseStep 478709 = 44879) (by norm_num)
theorem B708101 : Blo 139791 708101 := bbase (se 4 (by rfl) ⟨66384, by rfl⟩ : syracuseStep 708101 = 132769) (by norm_num)
theorem B216589 : Blo 139791 216589 := bbase (se 3 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 216589 = 81221) (by norm_num)
theorem B314909 : Blo 139791 314909 := bbase (se 3 (by rfl) ⟨59045, by rfl⟩ : syracuseStep 314909 = 118091) (by norm_num)
theorem B216661 : Blo 139791 216661 := bbase (se 8 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 216661 = 2539) (by norm_num)
theorem B314981 : Blo 139791 314981 := bbase (se 4 (by rfl) ⟨29529, by rfl⟩ : syracuseStep 314981 = 59059) (by norm_num)
theorem B315053 : Blo 139791 315053 := bbase (se 3 (by rfl) ⟨59072, by rfl⟩ : syracuseStep 315053 = 118145) (by norm_num)
theorem B315125 : Blo 139791 315125 := bbase (se 5 (by rfl) ⟨14771, by rfl⟩ : syracuseStep 315125 = 29543) (by norm_num)
theorem B610037 : Blo 139791 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B151313 : Blo 139791 151313 := bbase (se 2 (by rfl) ⟨56742, by rfl⟩ : syracuseStep 151313 = 113485) (by norm_num)
theorem B315197 : Blo 139791 315197 := bbase (se 3 (by rfl) ⟨59099, by rfl⟩ : syracuseStep 315197 = 118199) (by norm_num)
theorem B184133 : Blo 139791 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B315269 : Blo 139791 315269 := bbase (se 4 (by rfl) ⟨29556, by rfl⟩ : syracuseStep 315269 = 59113) (by norm_num)
theorem B479141 : Blo 139791 479141 := bbase (se 4 (by rfl) ⟨44919, by rfl⟩ : syracuseStep 479141 = 89839) (by norm_num)
theorem B315341 : Blo 139791 315341 := bbase (se 3 (by rfl) ⟨59126, by rfl⟩ : syracuseStep 315341 = 118253) (by norm_num)
theorem B151561 : Blo 139791 151561 := bbase (se 2 (by rfl) ⟨56835, by rfl⟩ : syracuseStep 151561 = 113671) (by norm_num)
theorem B315413 : Blo 139791 315413 := bbase (se 6 (by rfl) ⟨7392, by rfl⟩ : syracuseStep 315413 = 14785) (by norm_num)
theorem B315485 : Blo 139791 315485 := bbase (se 3 (by rfl) ⟨59153, by rfl⟩ : syracuseStep 315485 = 118307) (by norm_num)
theorem B675989 : Blo 139791 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B315557 : Blo 139791 315557 := bbase (se 4 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 315557 = 59167) (by norm_num)
theorem B315629 : Blo 139791 315629 := bbase (se 3 (by rfl) ⟨59180, by rfl⟩ : syracuseStep 315629 = 118361) (by norm_num)
theorem B315701 : Blo 139791 315701 := bbase (se 5 (by rfl) ⟨14798, by rfl⟩ : syracuseStep 315701 = 29597) (by norm_num)
theorem B151889 : Blo 139791 151889 := bbase (se 2 (by rfl) ⟨56958, by rfl⟩ : syracuseStep 151889 = 113917) (by norm_num)
theorem B479573 : Blo 139791 479573 := bbase (se 10 (by rfl) ⟨702, by rfl⟩ : syracuseStep 479573 = 1405) (by norm_num)
theorem B315773 : Blo 139791 315773 := bbase (se 3 (by rfl) ⟨59207, by rfl⟩ : syracuseStep 315773 = 118415) (by norm_num)
theorem B151993 : Blo 139791 151993 := bbase (se 2 (by rfl) ⟨56997, by rfl⟩ : syracuseStep 151993 = 113995) (by norm_num)
theorem B315845 : Blo 139791 315845 := bbase (se 4 (by rfl) ⟨29610, by rfl⟩ : syracuseStep 315845 = 59221) (by norm_num)
theorem B1102325 : Blo 139791 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B283133 : Blo 139791 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B152065 : Blo 139791 152065 := bbase (se 2 (by rfl) ⟨57024, by rfl⟩ : syracuseStep 152065 = 114049) (by norm_num)
theorem B315917 : Blo 139791 315917 := bbase (se 3 (by rfl) ⟨59234, by rfl⟩ : syracuseStep 315917 = 118469) (by norm_num)
theorem B315989 : Blo 139791 315989 := bbase (se 8 (by rfl) ⟨1851, by rfl⟩ : syracuseStep 315989 = 3703) (by norm_num)
theorem B1069685 : Blo 139791 1069685 := bbase (se 5 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 1069685 = 100283) (by norm_num)
theorem B545413 : Blo 139791 545413 := bbase (se 4 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 545413 = 102265) (by norm_num)
theorem B316061 : Blo 139791 316061 := bbase (se 3 (by rfl) ⟨59261, by rfl⟩ : syracuseStep 316061 = 118523) (by norm_num)
theorem B316133 : Blo 139791 316133 := bbase (se 4 (by rfl) ⟨29637, by rfl⟩ : syracuseStep 316133 = 59275) (by norm_num)
theorem B217829 : Blo 139791 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B480005 : Blo 139791 480005 := bbase (se 4 (by rfl) ⟨45000, by rfl⟩ : syracuseStep 480005 = 90001) (by norm_num)
theorem B709397 : Blo 139791 709397 := bbase (se 6 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 709397 = 33253) (by norm_num)
theorem B316205 : Blo 139791 316205 := bbase (se 3 (by rfl) ⟨59288, by rfl⟩ : syracuseStep 316205 = 118577) (by norm_num)
theorem B316277 : Blo 139791 316277 := bbase (se 5 (by rfl) ⟨14825, by rfl⟩ : syracuseStep 316277 = 29651) (by norm_num)
theorem B152437 : Blo 139791 152437 := bbase (se 5 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 152437 = 14291) (by norm_num)
theorem B1135541 : Blo 139791 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B545717 : Blo 139791 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B316349 : Blo 139791 316349 := bbase (se 3 (by rfl) ⟨59315, by rfl⟩ : syracuseStep 316349 = 118631) (by norm_num)
theorem B807893 : Blo 139791 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B316421 : Blo 139791 316421 := bbase (se 4 (by rfl) ⟨29664, by rfl⟩ : syracuseStep 316421 = 59329) (by norm_num)
theorem B316493 : Blo 139791 316493 := bbase (se 3 (by rfl) ⟨59342, by rfl⟩ : syracuseStep 316493 = 118685) (by norm_num)
theorem B316565 : Blo 139791 316565 := bbase (se 6 (by rfl) ⟨7419, by rfl⟩ : syracuseStep 316565 = 14839) (by norm_num)
theorem B480437 : Blo 139791 480437 := bbase (se 5 (by rfl) ⟨22520, by rfl⟩ : syracuseStep 480437 = 45041) (by norm_num)
theorem B316637 : Blo 139791 316637 := bbase (se 3 (by rfl) ⟨59369, by rfl⟩ : syracuseStep 316637 = 118739) (by norm_num)
theorem B152813 : Blo 139791 152813 := bbase (se 3 (by rfl) ⟨28652, by rfl⟩ : syracuseStep 152813 = 57305) (by norm_num)
theorem B316709 : Blo 139791 316709 := bbase (se 4 (by rfl) ⟨29691, by rfl⟩ : syracuseStep 316709 = 59383) (by norm_num)
theorem B152885 : Blo 139791 152885 := bbase (se 5 (by rfl) ⟨7166, by rfl⟩ : syracuseStep 152885 = 14333) (by norm_num)
theorem B382277 : Blo 139791 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B218461 : Blo 139791 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B316781 : Blo 139791 316781 := bbase (se 3 (by rfl) ⟨59396, by rfl⟩ : syracuseStep 316781 = 118793) (by norm_num)
theorem B316853 : Blo 139791 316853 := bbase (se 5 (by rfl) ⟨14852, by rfl⟩ : syracuseStep 316853 = 29705) (by norm_num)
theorem B611813 : Blo 139791 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B153073 : Blo 139791 153073 := bbase (se 2 (by rfl) ⟨57402, by rfl⟩ : syracuseStep 153073 = 114805) (by norm_num)
theorem B316925 : Blo 139791 316925 := bbase (se 3 (by rfl) ⟨59423, by rfl⟩ : syracuseStep 316925 = 118847) (by norm_num)
theorem B874037 : Blo 139791 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B579125 : Blo 139791 579125 := bbase (se 5 (by rfl) ⟨27146, by rfl⟩ : syracuseStep 579125 = 54293) (by norm_num)
theorem B316997 : Blo 139791 316997 := bbase (se 4 (by rfl) ⟨29718, by rfl⟩ : syracuseStep 316997 = 59437) (by norm_num)
theorem B448085 : Blo 139791 448085 := bbase (se 8 (by rfl) ⟨2625, by rfl⟩ : syracuseStep 448085 = 5251) (by norm_num)
theorem B480869 : Blo 139791 480869 := bbase (se 4 (by rfl) ⟨45081, by rfl⟩ : syracuseStep 480869 = 90163) (by norm_num)
theorem B317069 : Blo 139791 317069 := bbase (se 3 (by rfl) ⟨59450, by rfl⟩ : syracuseStep 317069 = 118901) (by norm_num)
theorem B153257 : Blo 139791 153257 := bbase (se 2 (by rfl) ⟨57471, by rfl⟩ : syracuseStep 153257 = 114943) (by norm_num)
theorem B317141 : Blo 139791 317141 := bbase (se 7 (by rfl) ⟨3716, by rfl⟩ : syracuseStep 317141 = 7433) (by norm_num)
theorem B677605 : Blo 139791 677605 := bbase (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) (by norm_num)
theorem B1365781 : Blo 139791 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B317213 : Blo 139791 317213 := bbase (se 3 (by rfl) ⟨59477, by rfl⟩ : syracuseStep 317213 = 118955) (by norm_num)
theorem B317285 : Blo 139791 317285 := bbase (se 4 (by rfl) ⟨29745, by rfl⟩ : syracuseStep 317285 = 59491) (by norm_num)
theorem B317357 : Blo 139791 317357 := bbase (se 3 (by rfl) ⟨59504, by rfl⟩ : syracuseStep 317357 = 119009) (by norm_num)
theorem B350125 : Blo 139791 350125 := bbase (se 3 (by rfl) ⟨65648, by rfl⟩ : syracuseStep 350125 = 131297) (by norm_num)
theorem B317429 : Blo 139791 317429 := bbase (se 5 (by rfl) ⟨14879, by rfl⟩ : syracuseStep 317429 = 29759) (by norm_num)
theorem B481301 : Blo 139791 481301 := bbase (se 6 (by rfl) ⟨11280, by rfl⟩ : syracuseStep 481301 = 22561) (by norm_num)
theorem B710693 : Blo 139791 710693 := bbase (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) (by norm_num)
theorem B317501 : Blo 139791 317501 := bbase (se 3 (by rfl) ⟨59531, by rfl⟩ : syracuseStep 317501 = 119063) (by norm_num)
theorem B317573 : Blo 139791 317573 := bbase (se 4 (by rfl) ⟨29772, by rfl⟩ : syracuseStep 317573 = 59545) (by norm_num)
theorem B317645 : Blo 139791 317645 := bbase (se 3 (by rfl) ⟨59558, by rfl⟩ : syracuseStep 317645 = 119117) (by norm_num)
theorem B1300693 : Blo 139791 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B1038581 : Blo 139791 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B317717 : Blo 139791 317717 := bbase (se 6 (by rfl) ⟨7446, by rfl⟩ : syracuseStep 317717 = 14893) (by norm_num)
theorem B317789 : Blo 139791 317789 := bbase (se 3 (by rfl) ⟨59585, by rfl⟩ : syracuseStep 317789 = 119171) (by norm_num)
theorem B317861 : Blo 139791 317861 := bbase (se 4 (by rfl) ⟨29799, by rfl⟩ : syracuseStep 317861 = 59599) (by norm_num)
theorem B481733 : Blo 139791 481733 := bbase (se 4 (by rfl) ⟨45162, by rfl⟩ : syracuseStep 481733 = 90325) (by norm_num)
theorem B612805 : Blo 139791 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B317933 : Blo 139791 317933 := bbase (se 3 (by rfl) ⟨59612, by rfl⟩ : syracuseStep 317933 = 119225) (by norm_num)
theorem B318005 : Blo 139791 318005 := bbase (se 5 (by rfl) ⟨14906, by rfl⟩ : syracuseStep 318005 = 29813) (by norm_num)
theorem B318077 : Blo 139791 318077 := bbase (se 3 (by rfl) ⟨59639, by rfl⟩ : syracuseStep 318077 = 119279) (by norm_num)
theorem B318149 : Blo 139791 318149 := bbase (se 4 (by rfl) ⟨29826, by rfl⟩ : syracuseStep 318149 = 59653) (by norm_num)
theorem B318221 : Blo 139791 318221 := bbase (se 3 (by rfl) ⟨59666, by rfl⟩ : syracuseStep 318221 = 119333) (by norm_num)
theorem B318293 : Blo 139791 318293 := bbase (se 9 (by rfl) ⟨932, by rfl⟩ : syracuseStep 318293 = 1865) (by norm_num)
theorem B482165 : Blo 139791 482165 := bbase (se 5 (by rfl) ⟨22601, by rfl⟩ : syracuseStep 482165 = 45203) (by norm_num)
theorem B318365 : Blo 139791 318365 := bbase (se 3 (by rfl) ⟨59693, by rfl⟩ : syracuseStep 318365 = 119387) (by norm_num)
theorem B318437 : Blo 139791 318437 := bbase (se 4 (by rfl) ⟨29853, by rfl⟩ : syracuseStep 318437 = 59707) (by norm_num)
theorem B318509 : Blo 139791 318509 := bbase (se 3 (by rfl) ⟨59720, by rfl⟩ : syracuseStep 318509 = 119441) (by norm_num)
theorem B220205 : Blo 139791 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B777269 : Blo 139791 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B318581 : Blo 139791 318581 := bbase (se 5 (by rfl) ⟨14933, by rfl⟩ : syracuseStep 318581 = 29867) (by norm_num)
theorem B810101 : Blo 139791 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B318653 : Blo 139791 318653 := bbase (se 3 (by rfl) ⟨59747, by rfl⟩ : syracuseStep 318653 = 119495) (by norm_num)
theorem B318725 : Blo 139791 318725 := bbase (se 4 (by rfl) ⟨29880, by rfl⟩ : syracuseStep 318725 = 59761) (by norm_num)
theorem B154885 : Blo 139791 154885 := bbase (se 4 (by rfl) ⟨14520, by rfl⟩ : syracuseStep 154885 = 29041) (by norm_num)
theorem B482597 : Blo 139791 482597 := bbase (se 4 (by rfl) ⟨45243, by rfl⟩ : syracuseStep 482597 = 90487) (by norm_num)
theorem B711989 : Blo 139791 711989 := bbase (se 5 (by rfl) ⟨33374, by rfl⟩ : syracuseStep 711989 = 66749) (by norm_num)
theorem B908597 : Blo 139791 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B318797 : Blo 139791 318797 := bbase (se 3 (by rfl) ⟨59774, by rfl⟩ : syracuseStep 318797 = 119549) (by norm_num)
theorem B318869 : Blo 139791 318869 := bbase (se 6 (by rfl) ⟨7473, by rfl⟩ : syracuseStep 318869 = 14947) (by norm_num)
theorem B253381 : Blo 139791 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B318941 : Blo 139791 318941 := bbase (se 3 (by rfl) ⟨59801, by rfl⟩ : syracuseStep 318941 = 119603) (by norm_num)
theorem B253453 : Blo 139791 253453 := bbase (se 3 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 253453 = 95045) (by norm_num)
theorem B319013 : Blo 139791 319013 := bbase (se 4 (by rfl) ⟨29907, by rfl⟩ : syracuseStep 319013 = 59815) (by norm_num)
theorem B155233 : Blo 139791 155233 := bbase (se 2 (by rfl) ⟨58212, by rfl⟩ : syracuseStep 155233 = 116425) (by norm_num)
theorem B319085 : Blo 139791 319085 := bbase (se 3 (by rfl) ⟨59828, by rfl⟩ : syracuseStep 319085 = 119657) (by norm_num)
theorem B319157 : Blo 139791 319157 := bbase (se 5 (by rfl) ⟨14960, by rfl⟩ : syracuseStep 319157 = 29921) (by norm_num)
theorem B483029 : Blo 139791 483029 := bbase (se 7 (by rfl) ⟨5660, by rfl⟩ : syracuseStep 483029 = 11321) (by norm_num)
theorem B253685 : Blo 139791 253685 := bbase (se 5 (by rfl) ⟨11891, by rfl⟩ : syracuseStep 253685 = 23783) (by norm_num)
theorem B319229 : Blo 139791 319229 := bbase (se 3 (by rfl) ⟨59855, by rfl⟩ : syracuseStep 319229 = 119711) (by norm_num)
theorem B581381 : Blo 139791 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B319301 : Blo 139791 319301 := bbase (se 4 (by rfl) ⟨29934, by rfl⟩ : syracuseStep 319301 = 59869) (by norm_num)
theorem B319373 : Blo 139791 319373 := bbase (se 3 (by rfl) ⟨59882, by rfl⟩ : syracuseStep 319373 = 119765) (by norm_num)
theorem B286621 : Blo 139791 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B319445 : Blo 139791 319445 := bbase (se 7 (by rfl) ⟨3743, by rfl⟩ : syracuseStep 319445 = 7487) (by norm_num)
theorem B319517 : Blo 139791 319517 := bbase (se 3 (by rfl) ⟨59909, by rfl⟩ : syracuseStep 319517 = 119819) (by norm_num)
theorem B286805 : Blo 139791 286805 := bbase (se 8 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 286805 = 3361) (by norm_num)
theorem B319589 : Blo 139791 319589 := bbase (se 4 (by rfl) ⟨29961, by rfl⟩ : syracuseStep 319589 = 59923) (by norm_num)
theorem B483461 : Blo 139791 483461 := bbase (se 4 (by rfl) ⟨45324, by rfl⟩ : syracuseStep 483461 = 90649) (by norm_num)
theorem B319661 : Blo 139791 319661 := bbase (se 3 (by rfl) ⟨59936, by rfl⟩ : syracuseStep 319661 = 119873) (by norm_num)
theorem B319733 : Blo 139791 319733 := bbase (se 5 (by rfl) ⟨14987, by rfl⟩ : syracuseStep 319733 = 29975) (by norm_num)
theorem B319805 : Blo 139791 319805 := bbase (se 3 (by rfl) ⟨59963, by rfl⟩ : syracuseStep 319805 = 119927) (by norm_num)
theorem B450917 : Blo 139791 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B319877 : Blo 139791 319877 := bbase (se 4 (by rfl) ⟨29988, by rfl⟩ : syracuseStep 319877 = 59977) (by norm_num)
theorem B319949 : Blo 139791 319949 := bbase (se 3 (by rfl) ⟨59990, by rfl⟩ : syracuseStep 319949 = 119981) (by norm_num)
theorem B254477 : Blo 139791 254477 := bbase (se 3 (by rfl) ⟨47714, by rfl⟩ : syracuseStep 254477 = 95429) (by norm_num)
theorem B320021 : Blo 139791 320021 := bbase (se 6 (by rfl) ⟨7500, by rfl⟩ : syracuseStep 320021 = 15001) (by norm_num)
theorem B483893 : Blo 139791 483893 := bbase (se 5 (by rfl) ⟨22682, by rfl⟩ : syracuseStep 483893 = 45365) (by norm_num)
theorem B713285 : Blo 139791 713285 := bbase (se 4 (by rfl) ⟨66870, by rfl⟩ : syracuseStep 713285 = 133741) (by norm_num)
theorem B287317 : Blo 139791 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B320093 : Blo 139791 320093 := bbase (se 3 (by rfl) ⟨60017, by rfl⟩ : syracuseStep 320093 = 120035) (by norm_num)
theorem B320165 : Blo 139791 320165 := bbase (se 4 (by rfl) ⟨30015, by rfl⟩ : syracuseStep 320165 = 60031) (by norm_num)
theorem B320237 : Blo 139791 320237 := bbase (se 3 (by rfl) ⟨60044, by rfl⟩ : syracuseStep 320237 = 120089) (by norm_num)
theorem B254765 : Blo 139791 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B320309 : Blo 139791 320309 := bbase (se 5 (by rfl) ⟨15014, by rfl⟩ : syracuseStep 320309 = 30029) (by norm_num)
theorem B189253 : Blo 139791 189253 := bbase (se 4 (by rfl) ⟨17742, by rfl⟩ : syracuseStep 189253 = 35485) (by norm_num)
theorem B254837 : Blo 139791 254837 := bbase (se 5 (by rfl) ⟨11945, by rfl⟩ : syracuseStep 254837 = 23891) (by norm_num)
theorem B320381 : Blo 139791 320381 := bbase (se 3 (by rfl) ⟨60071, by rfl⟩ : syracuseStep 320381 = 120143) (by norm_num)
theorem B517013 : Blo 139791 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B320453 : Blo 139791 320453 := bbase (se 4 (by rfl) ⟨30042, by rfl⟩ : syracuseStep 320453 = 60085) (by norm_num)
theorem B1139669 : Blo 139791 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B484325 : Blo 139791 484325 := bbase (se 4 (by rfl) ⟨45405, by rfl⟩ : syracuseStep 484325 = 90811) (by norm_num)
theorem B320525 : Blo 139791 320525 := bbase (se 3 (by rfl) ⟨60098, by rfl⟩ : syracuseStep 320525 = 120197) (by norm_num)
theorem B320597 : Blo 139791 320597 := bbase (se 8 (by rfl) ⟨1878, by rfl⟩ : syracuseStep 320597 = 3757) (by norm_num)
theorem B320669 : Blo 139791 320669 := bbase (se 3 (by rfl) ⟨60125, by rfl⟩ : syracuseStep 320669 = 120251) (by norm_num)
theorem B451813 : Blo 139791 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B320741 : Blo 139791 320741 := bbase (se 4 (by rfl) ⟨30069, by rfl⟩ : syracuseStep 320741 = 60139) (by norm_num)
theorem B320813 : Blo 139791 320813 := bbase (se 3 (by rfl) ⟨60152, by rfl⟩ : syracuseStep 320813 = 120305) (by norm_num)
theorem B320885 : Blo 139791 320885 := bbase (se 5 (by rfl) ⟨15041, by rfl⟩ : syracuseStep 320885 = 30083) (by norm_num)
theorem B484757 : Blo 139791 484757 := bbase (se 6 (by rfl) ⟨11361, by rfl⟩ : syracuseStep 484757 = 22723) (by norm_num)
theorem B320957 : Blo 139791 320957 := bbase (se 3 (by rfl) ⟨60179, by rfl⟩ : syracuseStep 320957 = 120359) (by norm_num)
theorem B157165 : Blo 139791 157165 := bbase (se 3 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 157165 = 58937) (by norm_num)
theorem B386549 : Blo 139791 386549 := bbase (se 5 (by rfl) ⟨18119, by rfl⟩ : syracuseStep 386549 = 36239) (by norm_num)
theorem B189949 : Blo 139791 189949 := bbase (se 3 (by rfl) ⟨35615, by rfl⟩ : syracuseStep 189949 = 71231) (by norm_num)
theorem B321029 : Blo 139791 321029 := bbase (se 4 (by rfl) ⟨30096, by rfl⟩ : syracuseStep 321029 = 60193) (by norm_num)
theorem B321101 : Blo 139791 321101 := bbase (se 3 (by rfl) ⟨60206, by rfl⟩ : syracuseStep 321101 = 120413) (by norm_num)
theorem B3434069 : Blo 139791 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B157297 : Blo 139791 157297 := bbase (se 2 (by rfl) ⟨58986, by rfl⟩ : syracuseStep 157297 = 117973) (by norm_num)
theorem B353909 : Blo 139791 353909 := bbase (se 5 (by rfl) ⟨16589, by rfl⟩ : syracuseStep 353909 = 33179) (by norm_num)
theorem B157333 : Blo 139791 157333 := bbase (se 6 (by rfl) ⟨3687, by rfl⟩ : syracuseStep 157333 = 7375) (by norm_num)
theorem B321173 : Blo 139791 321173 := bbase (se 6 (by rfl) ⟨7527, by rfl⟩ : syracuseStep 321173 = 15055) (by norm_num)
theorem B157369 : Blo 139791 157369 := bbase (se 2 (by rfl) ⟨59013, by rfl⟩ : syracuseStep 157369 = 118027) (by norm_num)
theorem B157405 : Blo 139791 157405 := bbase (se 3 (by rfl) ⟨29513, by rfl⟩ : syracuseStep 157405 = 59027) (by norm_num)
theorem B321245 : Blo 139791 321245 := bbase (se 3 (by rfl) ⟨60233, by rfl⟩ : syracuseStep 321245 = 120467) (by norm_num)
theorem B157441 : Blo 139791 157441 := bbase (se 2 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 157441 = 118081) (by norm_num)
theorem B157477 : Blo 139791 157477 := bbase (se 4 (by rfl) ⟨14763, by rfl⟩ : syracuseStep 157477 = 29527) (by norm_num)
theorem B321317 : Blo 139791 321317 := bbase (se 4 (by rfl) ⟨30123, by rfl⟩ : syracuseStep 321317 = 60247) (by norm_num)
theorem B485189 : Blo 139791 485189 := bbase (se 4 (by rfl) ⟨45486, by rfl⟩ : syracuseStep 485189 = 90973) (by norm_num)
theorem B157513 : Blo 139791 157513 := bbase (se 2 (by rfl) ⟨59067, by rfl⟩ : syracuseStep 157513 = 118135) (by norm_num)
theorem B714581 : Blo 139791 714581 := bbase (se 9 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 714581 = 4187) (by norm_num)
theorem B157549 : Blo 139791 157549 := bbase (se 3 (by rfl) ⟨29540, by rfl⟩ : syracuseStep 157549 = 59081) (by norm_num)
theorem B321389 : Blo 139791 321389 := bbase (se 3 (by rfl) ⟨60260, by rfl⟩ : syracuseStep 321389 = 120521) (by norm_num)
theorem B157585 : Blo 139791 157585 := bbase (se 2 (by rfl) ⟨59094, by rfl⟩ : syracuseStep 157585 = 118189) (by norm_num)
theorem B157621 : Blo 139791 157621 := bbase (se 5 (by rfl) ⟨7388, by rfl⟩ : syracuseStep 157621 = 14777) (by norm_num)
theorem B321461 : Blo 139791 321461 := bbase (se 5 (by rfl) ⟨15068, by rfl⟩ : syracuseStep 321461 = 30137) (by norm_num)
theorem B354253 : Blo 139791 354253 := bbase (se 3 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 354253 = 132845) (by norm_num)
theorem B157657 : Blo 139791 157657 := bbase (se 2 (by rfl) ⟨59121, by rfl⟩ : syracuseStep 157657 = 118243) (by norm_num)
theorem B157693 : Blo 139791 157693 := bbase (se 3 (by rfl) ⟨29567, by rfl⟩ : syracuseStep 157693 = 59135) (by norm_num)
theorem B321533 : Blo 139791 321533 := bbase (se 3 (by rfl) ⟨60287, by rfl⟩ : syracuseStep 321533 = 120575) (by norm_num)
theorem B157729 : Blo 139791 157729 := bbase (se 2 (by rfl) ⟨59148, by rfl⟩ : syracuseStep 157729 = 118297) (by norm_num)
theorem B354365 : Blo 139791 354365 := bbase (se 3 (by rfl) ⟨66443, by rfl⟩ : syracuseStep 354365 = 132887) (by norm_num)
theorem B157765 : Blo 139791 157765 := bbase (se 4 (by rfl) ⟨14790, by rfl⟩ : syracuseStep 157765 = 29581) (by norm_num)
theorem B321605 : Blo 139791 321605 := bbase (se 4 (by rfl) ⟨30150, by rfl⟩ : syracuseStep 321605 = 60301) (by norm_num)
theorem B157801 : Blo 139791 157801 := bbase (se 2 (by rfl) ⟨59175, by rfl⟩ : syracuseStep 157801 = 118351) (by norm_num)
theorem B157837 : Blo 139791 157837 := bbase (se 3 (by rfl) ⟨29594, by rfl⟩ : syracuseStep 157837 = 59189) (by norm_num)
theorem B321677 : Blo 139791 321677 := bbase (se 3 (by rfl) ⟨60314, by rfl⟩ : syracuseStep 321677 = 120629) (by norm_num)
theorem B157873 : Blo 139791 157873 := bbase (se 2 (by rfl) ⟨59202, by rfl⟩ : syracuseStep 157873 = 118405) (by norm_num)
theorem B157909 : Blo 139791 157909 := bbase (se 7 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 157909 = 3701) (by norm_num)
theorem B321749 : Blo 139791 321749 := bbase (se 7 (by rfl) ⟨3770, by rfl⟩ : syracuseStep 321749 = 7541) (by norm_num)
theorem B157945 : Blo 139791 157945 := bbase (se 2 (by rfl) ⟨59229, by rfl⟩ : syracuseStep 157945 = 118459) (by norm_num)
theorem B354557 : Blo 139791 354557 := bbase (se 3 (by rfl) ⟨66479, by rfl⟩ : syracuseStep 354557 = 132959) (by norm_num)
theorem B157981 : Blo 139791 157981 := bbase (se 3 (by rfl) ⟨29621, by rfl⟩ : syracuseStep 157981 = 59243) (by norm_num)
theorem B321821 : Blo 139791 321821 := bbase (se 3 (by rfl) ⟨60341, by rfl⟩ : syracuseStep 321821 = 120683) (by norm_num)
theorem B158017 : Blo 139791 158017 := bbase (se 2 (by rfl) ⟨59256, by rfl⟩ : syracuseStep 158017 = 118513) (by norm_num)
theorem B158053 : Blo 139791 158053 := bbase (se 4 (by rfl) ⟨14817, by rfl⟩ : syracuseStep 158053 = 29635) (by norm_num)
theorem B321893 : Blo 139791 321893 := bbase (se 4 (by rfl) ⟨30177, by rfl⟩ : syracuseStep 321893 = 60355) (by norm_num)
theorem B485765 : Blo 139791 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B158089 : Blo 139791 158089 := bbase (se 2 (by rfl) ⟨59283, by rfl⟩ : syracuseStep 158089 = 118567) (by norm_num)
theorem B1206677 : Blo 139791 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B158125 : Blo 139791 158125 := bbase (se 3 (by rfl) ⟨29648, by rfl⟩ : syracuseStep 158125 = 59297) (by norm_num)
theorem B321965 : Blo 139791 321965 := bbase (se 3 (by rfl) ⟨60368, by rfl⟩ : syracuseStep 321965 = 120737) (by norm_num)
theorem B158161 : Blo 139791 158161 := bbase (se 2 (by rfl) ⟨59310, by rfl⟩ : syracuseStep 158161 = 118621) (by norm_num)
theorem B158197 : Blo 139791 158197 := bbase (se 5 (by rfl) ⟨7415, by rfl⟩ : syracuseStep 158197 = 14831) (by norm_num)
theorem B322037 : Blo 139791 322037 := bbase (se 5 (by rfl) ⟨15095, by rfl⟩ : syracuseStep 322037 = 30191) (by norm_num)
theorem B158233 : Blo 139791 158233 := bbase (se 2 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 158233 = 118675) (by norm_num)
theorem B158269 : Blo 139791 158269 := bbase (se 3 (by rfl) ⟨29675, by rfl⟩ : syracuseStep 158269 = 59351) (by norm_num)
theorem B322109 : Blo 139791 322109 := bbase (se 3 (by rfl) ⟨60395, by rfl⟩ : syracuseStep 322109 = 120791) (by norm_num)
theorem B354901 : Blo 139791 354901 := bbase (se 8 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 354901 = 4159) (by norm_num)
theorem B158305 : Blo 139791 158305 := bbase (se 2 (by rfl) ⟨59364, by rfl⟩ : syracuseStep 158305 = 118729) (by norm_num)
theorem B158341 : Blo 139791 158341 := bbase (se 4 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 158341 = 29689) (by norm_num)
theorem B322181 : Blo 139791 322181 := bbase (se 4 (by rfl) ⟨30204, by rfl⟩ : syracuseStep 322181 = 60409) (by norm_num)
theorem B158377 : Blo 139791 158377 := bbase (se 2 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 158377 = 118783) (by norm_num)
theorem B355013 : Blo 139791 355013 := bbase (se 4 (by rfl) ⟨33282, by rfl⟩ : syracuseStep 355013 = 66565) (by norm_num)
theorem B158413 : Blo 139791 158413 := bbase (se 3 (by rfl) ⟨29702, by rfl⟩ : syracuseStep 158413 = 59405) (by norm_num)
theorem B322253 : Blo 139791 322253 := bbase (se 3 (by rfl) ⟨60422, by rfl⟩ : syracuseStep 322253 = 120845) (by norm_num)
theorem B158449 : Blo 139791 158449 := bbase (se 2 (by rfl) ⟨59418, by rfl⟩ : syracuseStep 158449 = 118837) (by norm_num)
theorem B158485 : Blo 139791 158485 := bbase (se 6 (by rfl) ⟨3714, by rfl⟩ : syracuseStep 158485 = 7429) (by norm_num)
theorem B322325 : Blo 139791 322325 := bbase (se 6 (by rfl) ⟨7554, by rfl⟩ : syracuseStep 322325 = 15109) (by norm_num)
theorem B191269 : Blo 139791 191269 := bbase (se 4 (by rfl) ⟨17931, by rfl⟩ : syracuseStep 191269 = 35863) (by norm_num)
theorem B158521 : Blo 139791 158521 := bbase (se 2 (by rfl) ⟨59445, by rfl⟩ : syracuseStep 158521 = 118891) (by norm_num)
theorem B158557 : Blo 139791 158557 := bbase (se 3 (by rfl) ⟨29729, by rfl⟩ : syracuseStep 158557 = 59459) (by norm_num)
theorem B322397 : Blo 139791 322397 := bbase (se 3 (by rfl) ⟨60449, by rfl⟩ : syracuseStep 322397 = 120899) (by norm_num)
theorem B191333 : Blo 139791 191333 := bbase (se 4 (by rfl) ⟨17937, by rfl⟩ : syracuseStep 191333 = 35875) (by norm_num)
theorem B158593 : Blo 139791 158593 := bbase (se 2 (by rfl) ⟨59472, by rfl⟩ : syracuseStep 158593 = 118945) (by norm_num)
theorem B355205 : Blo 139791 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B158629 : Blo 139791 158629 := bbase (se 4 (by rfl) ⟨14871, by rfl⟩ : syracuseStep 158629 = 29743) (by norm_num)
theorem B322469 : Blo 139791 322469 := bbase (se 4 (by rfl) ⟨30231, by rfl⟩ : syracuseStep 322469 = 60463) (by norm_num)
theorem B158665 : Blo 139791 158665 := bbase (se 2 (by rfl) ⟨59499, by rfl⟩ : syracuseStep 158665 = 118999) (by norm_num)
theorem B158701 : Blo 139791 158701 := bbase (se 3 (by rfl) ⟨29756, by rfl⟩ : syracuseStep 158701 = 59513) (by norm_num)
theorem B322541 : Blo 139791 322541 := bbase (se 3 (by rfl) ⟨60476, by rfl⟩ : syracuseStep 322541 = 120953) (by norm_num)
theorem B158737 : Blo 139791 158737 := bbase (se 2 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 158737 = 119053) (by norm_num)
theorem B158773 : Blo 139791 158773 := bbase (se 5 (by rfl) ⟨7442, by rfl⟩ : syracuseStep 158773 = 14885) (by norm_num)
theorem B322613 : Blo 139791 322613 := bbase (se 5 (by rfl) ⟨15122, by rfl⟩ : syracuseStep 322613 = 30245) (by norm_num)
theorem B158809 : Blo 139791 158809 := bbase (se 2 (by rfl) ⟨59553, by rfl⟩ : syracuseStep 158809 = 119107) (by norm_num)
theorem B715877 : Blo 139791 715877 := bbase (se 4 (by rfl) ⟨67113, by rfl⟩ : syracuseStep 715877 = 134227) (by norm_num)
theorem B158845 : Blo 139791 158845 := bbase (se 3 (by rfl) ⟨29783, by rfl⟩ : syracuseStep 158845 = 59567) (by norm_num)
theorem B322685 : Blo 139791 322685 := bbase (se 3 (by rfl) ⟨60503, by rfl⟩ : syracuseStep 322685 = 121007) (by norm_num)
theorem B158881 : Blo 139791 158881 := bbase (se 2 (by rfl) ⟨59580, by rfl⟩ : syracuseStep 158881 = 119161) (by norm_num)
theorem B257189 : Blo 139791 257189 := bbase (se 4 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 257189 = 48223) (by norm_num)
theorem B650405 : Blo 139791 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B224453 : Blo 139791 224453 := bbase (se 4 (by rfl) ⟨21042, by rfl⟩ : syracuseStep 224453 = 42085) (by norm_num)
theorem B158917 : Blo 139791 158917 := bbase (se 4 (by rfl) ⟨14898, by rfl⟩ : syracuseStep 158917 = 29797) (by norm_num)
theorem B322757 : Blo 139791 322757 := bbase (se 4 (by rfl) ⟨30258, by rfl⟩ : syracuseStep 322757 = 60517) (by norm_num)
theorem B355549 : Blo 139791 355549 := bbase (se 3 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 355549 = 133331) (by norm_num)
theorem B158953 : Blo 139791 158953 := bbase (se 2 (by rfl) ⟨59607, by rfl⟩ : syracuseStep 158953 = 119215) (by norm_num)
theorem B158989 : Blo 139791 158989 := bbase (se 3 (by rfl) ⟨29810, by rfl⟩ : syracuseStep 158989 = 59621) (by norm_num)
theorem B322829 : Blo 139791 322829 := bbase (se 3 (by rfl) ⟨60530, by rfl⟩ : syracuseStep 322829 = 121061) (by norm_num)
theorem B159025 : Blo 139791 159025 := bbase (se 2 (by rfl) ⟨59634, by rfl⟩ : syracuseStep 159025 = 119269) (by norm_num)
theorem B650549 : Blo 139791 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B355661 : Blo 139791 355661 := bbase (se 3 (by rfl) ⟨66686, by rfl⟩ : syracuseStep 355661 = 133373) (by norm_num)
theorem B159061 : Blo 139791 159061 := bbase (se 11 (by rfl) ⟨116, by rfl⟩ : syracuseStep 159061 = 233) (by norm_num)
theorem B322901 : Blo 139791 322901 := bbase (se 11 (by rfl) ⟨236, by rfl⟩ : syracuseStep 322901 = 473) (by norm_num)
theorem B159097 : Blo 139791 159097 := bbase (se 2 (by rfl) ⟨59661, by rfl⟩ : syracuseStep 159097 = 119323) (by norm_num)
theorem B159133 : Blo 139791 159133 := bbase (se 3 (by rfl) ⟨29837, by rfl⟩ : syracuseStep 159133 = 59675) (by norm_num)
theorem B322973 : Blo 139791 322973 := bbase (se 3 (by rfl) ⟨60557, by rfl⟩ : syracuseStep 322973 = 121115) (by norm_num)
theorem B159169 : Blo 139791 159169 := bbase (se 2 (by rfl) ⟨59688, by rfl⟩ : syracuseStep 159169 = 119377) (by norm_num)
theorem B159205 : Blo 139791 159205 := bbase (se 4 (by rfl) ⟨14925, by rfl⟩ : syracuseStep 159205 = 29851) (by norm_num)
theorem B323045 : Blo 139791 323045 := bbase (se 4 (by rfl) ⟨30285, by rfl⟩ : syracuseStep 323045 = 60571) (by norm_num)
theorem B159241 : Blo 139791 159241 := bbase (se 2 (by rfl) ⟨59715, by rfl⟩ : syracuseStep 159241 = 119431) (by norm_num)
theorem B355853 : Blo 139791 355853 := bbase (se 3 (by rfl) ⟨66722, by rfl⟩ : syracuseStep 355853 = 133445) (by norm_num)
theorem B159277 : Blo 139791 159277 := bbase (se 3 (by rfl) ⟨29864, by rfl⟩ : syracuseStep 159277 = 59729) (by norm_num)
theorem B323117 : Blo 139791 323117 := bbase (se 3 (by rfl) ⟨60584, by rfl⟩ : syracuseStep 323117 = 121169) (by norm_num)
theorem B159313 : Blo 139791 159313 := bbase (se 2 (by rfl) ⟨59742, by rfl⟩ : syracuseStep 159313 = 119485) (by norm_num)
theorem B159349 : Blo 139791 159349 := bbase (se 5 (by rfl) ⟨7469, by rfl⟩ : syracuseStep 159349 = 14939) (by norm_num)
theorem B323189 : Blo 139791 323189 := bbase (se 5 (by rfl) ⟨15149, by rfl⟩ : syracuseStep 323189 = 30299) (by norm_num)
theorem B159385 : Blo 139791 159385 := bbase (se 2 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 159385 = 119539) (by norm_num)
theorem B159421 : Blo 139791 159421 := bbase (se 3 (by rfl) ⟨29891, by rfl⟩ : syracuseStep 159421 = 59783) (by norm_num)
theorem B323261 : Blo 139791 323261 := bbase (se 3 (by rfl) ⟨60611, by rfl⟩ : syracuseStep 323261 = 121223) (by norm_num)
theorem B224965 : Blo 139791 224965 := bbase (se 4 (by rfl) ⟨21090, by rfl⟩ : syracuseStep 224965 = 42181) (by norm_num)
theorem B159449 : Blo 139791 159449 := bbase (se 2 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 159449 = 119587) (by norm_num)
theorem B159457 : Blo 139791 159457 := bbase (se 2 (by rfl) ⟨59796, by rfl⟩ : syracuseStep 159457 = 119593) (by norm_num)
theorem B159493 : Blo 139791 159493 := bbase (se 4 (by rfl) ⟨14952, by rfl⟩ : syracuseStep 159493 = 29905) (by norm_num)
theorem B323333 : Blo 139791 323333 := bbase (se 4 (by rfl) ⟨30312, by rfl⟩ : syracuseStep 323333 = 60625) (by norm_num)
theorem B159529 : Blo 139791 159529 := bbase (se 2 (by rfl) ⟨59823, by rfl⟩ : syracuseStep 159529 = 119647) (by norm_num)
theorem B159565 : Blo 139791 159565 := bbase (se 3 (by rfl) ⟨29918, by rfl⟩ : syracuseStep 159565 = 59837) (by norm_num)
theorem B323405 : Blo 139791 323405 := bbase (se 3 (by rfl) ⟨60638, by rfl⟩ : syracuseStep 323405 = 121277) (by norm_num)
theorem B356197 : Blo 139791 356197 := bbase (se 4 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 356197 = 66787) (by norm_num)
theorem B159601 : Blo 139791 159601 := bbase (se 2 (by rfl) ⟨59850, by rfl⟩ : syracuseStep 159601 = 119701) (by norm_num)
theorem B683909 : Blo 139791 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B159637 : Blo 139791 159637 := bbase (se 6 (by rfl) ⟨3741, by rfl⟩ : syracuseStep 159637 = 7483) (by norm_num)
theorem B323477 : Blo 139791 323477 := bbase (se 6 (by rfl) ⟨7581, by rfl⟩ : syracuseStep 323477 = 15163) (by norm_num)
theorem B159673 : Blo 139791 159673 := bbase (se 2 (by rfl) ⟨59877, by rfl⟩ : syracuseStep 159673 = 119755) (by norm_num)
theorem B356309 : Blo 139791 356309 := bbase (se 7 (by rfl) ⟨4175, by rfl⟩ : syracuseStep 356309 = 8351) (by norm_num)
theorem B3502037 : Blo 139791 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B159709 : Blo 139791 159709 := bbase (se 3 (by rfl) ⟨29945, by rfl⟩ : syracuseStep 159709 = 59891) (by norm_num)
theorem B159745 : Blo 139791 159745 := bbase (se 2 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 159745 = 119809) (by norm_num)
theorem B159769 : Blo 139791 159769 := bbase (se 2 (by rfl) ⟨59913, by rfl⟩ : syracuseStep 159769 = 119827) (by norm_num)
theorem B159781 : Blo 139791 159781 := bbase (se 4 (by rfl) ⟨14979, by rfl⟩ : syracuseStep 159781 = 29959) (by norm_num)
theorem B454709 : Blo 139791 454709 := bbase (se 5 (by rfl) ⟨21314, by rfl⟩ : syracuseStep 454709 = 42629) (by norm_num)
theorem B159817 : Blo 139791 159817 := bbase (se 2 (by rfl) ⟨59931, by rfl⟩ : syracuseStep 159817 = 119863) (by norm_num)
theorem B2093141 : Blo 139791 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B323693 : Blo 139791 323693 := bbase (se 3 (by rfl) ⟨60692, by rfl⟩ : syracuseStep 323693 = 121385) (by norm_num)
theorem B159853 : Blo 139791 159853 := bbase (se 3 (by rfl) ⟨29972, by rfl⟩ : syracuseStep 159853 = 59945) (by norm_num)
theorem B159889 : Blo 139791 159889 := bbase (se 2 (by rfl) ⟨59958, by rfl⟩ : syracuseStep 159889 = 119917) (by norm_num)
theorem B356501 : Blo 139791 356501 := bbase (se 6 (by rfl) ⟨8355, by rfl⟩ : syracuseStep 356501 = 16711) (by norm_num)
theorem B159925 : Blo 139791 159925 := bbase (se 5 (by rfl) ⟨7496, by rfl⟩ : syracuseStep 159925 = 14993) (by norm_num)
theorem B1077461 : Blo 139791 1077461 := bbase (se 7 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 1077461 = 25253) (by norm_num)
theorem B159961 : Blo 139791 159961 := bbase (se 2 (by rfl) ⟨59985, by rfl⟩ : syracuseStep 159961 = 119971) (by norm_num)
theorem B225509 : Blo 139791 225509 := bbase (se 4 (by rfl) ⟨21141, by rfl⟩ : syracuseStep 225509 = 42283) (by norm_num)
theorem B159997 : Blo 139791 159997 := bbase (se 3 (by rfl) ⟨29999, by rfl⟩ : syracuseStep 159997 = 59999) (by norm_num)
theorem B160033 : Blo 139791 160033 := bbase (se 2 (by rfl) ⟨60012, by rfl⟩ : syracuseStep 160033 = 120025) (by norm_num)
theorem B160061 : Blo 139791 160061 := bbase (se 3 (by rfl) ⟨30011, by rfl⟩ : syracuseStep 160061 = 60023) (by norm_num)
theorem B160069 : Blo 139791 160069 := bbase (se 4 (by rfl) ⟨15006, by rfl⟩ : syracuseStep 160069 = 30013) (by norm_num)
theorem B160105 : Blo 139791 160105 := bbase (se 2 (by rfl) ⟨60039, by rfl⟩ : syracuseStep 160105 = 120079) (by norm_num)
theorem B717173 : Blo 139791 717173 := bbase (se 5 (by rfl) ⟨33617, by rfl⟩ : syracuseStep 717173 = 67235) (by norm_num)
theorem B160141 : Blo 139791 160141 := bbase (se 3 (by rfl) ⟨30026, by rfl⟩ : syracuseStep 160141 = 60053) (by norm_num)
theorem B160177 : Blo 139791 160177 := bbase (se 2 (by rfl) ⟨60066, by rfl⟩ : syracuseStep 160177 = 120133) (by norm_num)
theorem B160213 : Blo 139791 160213 := bbase (se 7 (by rfl) ⟨1877, by rfl⟩ : syracuseStep 160213 = 3755) (by norm_num)
theorem B356845 : Blo 139791 356845 := bbase (se 3 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 356845 = 133817) (by norm_num)
theorem B160249 : Blo 139791 160249 := bbase (se 2 (by rfl) ⟨60093, by rfl⟩ : syracuseStep 160249 = 120187) (by norm_num)
theorem B160285 : Blo 139791 160285 := bbase (se 3 (by rfl) ⟨30053, by rfl⟩ : syracuseStep 160285 = 60107) (by norm_num)
theorem B160321 : Blo 139791 160321 := bbase (se 2 (by rfl) ⟨60120, by rfl⟩ : syracuseStep 160321 = 120241) (by norm_num)
theorem B356957 : Blo 139791 356957 := bbase (se 3 (by rfl) ⟨66929, by rfl⟩ : syracuseStep 356957 = 133859) (by norm_num)
theorem B160357 : Blo 139791 160357 := bbase (se 4 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 160357 = 30067) (by norm_num)
theorem B160393 : Blo 139791 160393 := bbase (se 2 (by rfl) ⟨60147, by rfl⟩ : syracuseStep 160393 = 120295) (by norm_num)
theorem B160429 : Blo 139791 160429 := bbase (se 3 (by rfl) ⟨30080, by rfl⟩ : syracuseStep 160429 = 60161) (by norm_num)
theorem B160465 : Blo 139791 160465 := bbase (se 2 (by rfl) ⟨60174, by rfl⟩ : syracuseStep 160465 = 120349) (by norm_num)
theorem B160501 : Blo 139791 160501 := bbase (se 5 (by rfl) ⟨7523, by rfl⟩ : syracuseStep 160501 = 15047) (by norm_num)
theorem B226061 : Blo 139791 226061 := bbase (se 3 (by rfl) ⟨42386, by rfl⟩ : syracuseStep 226061 = 84773) (by norm_num)
theorem B160537 : Blo 139791 160537 := bbase (se 2 (by rfl) ⟨60201, by rfl⟩ : syracuseStep 160537 = 120403) (by norm_num)
theorem B357149 : Blo 139791 357149 := bbase (se 3 (by rfl) ⟨66965, by rfl⟩ : syracuseStep 357149 = 133931) (by norm_num)
theorem B226093 : Blo 139791 226093 := bbase (se 3 (by rfl) ⟨42392, by rfl⟩ : syracuseStep 226093 = 84785) (by norm_num)
theorem B160573 : Blo 139791 160573 := bbase (se 3 (by rfl) ⟨30107, by rfl⟩ : syracuseStep 160573 = 60215) (by norm_num)
theorem B160609 : Blo 139791 160609 := bbase (se 2 (by rfl) ⟨60228, by rfl⟩ : syracuseStep 160609 = 120457) (by norm_num)
theorem B160645 : Blo 139791 160645 := bbase (se 4 (by rfl) ⟨15060, by rfl⟩ : syracuseStep 160645 = 30121) (by norm_num)
theorem B160681 : Blo 139791 160681 := bbase (se 2 (by rfl) ⟨60255, by rfl⟩ : syracuseStep 160681 = 120511) (by norm_num)
theorem B160717 : Blo 139791 160717 := bbase (se 3 (by rfl) ⟨30134, by rfl⟩ : syracuseStep 160717 = 60269) (by norm_num)
theorem B160741 : Blo 139791 160741 := bbase (se 4 (by rfl) ⟨15069, by rfl⟩ : syracuseStep 160741 = 30139) (by norm_num)
theorem B160753 : Blo 139791 160753 := bbase (se 2 (by rfl) ⟨60282, by rfl⟩ : syracuseStep 160753 = 120565) (by norm_num)
theorem B160789 : Blo 139791 160789 := bbase (se 6 (by rfl) ⟨3768, by rfl⟩ : syracuseStep 160789 = 7537) (by norm_num)
theorem B160825 : Blo 139791 160825 := bbase (se 2 (by rfl) ⟨60309, by rfl⟩ : syracuseStep 160825 = 120619) (by norm_num)
theorem B160861 : Blo 139791 160861 := bbase (se 3 (by rfl) ⟨30161, by rfl⟩ : syracuseStep 160861 = 60323) (by norm_num)
theorem B193637 : Blo 139791 193637 := bbase (se 4 (by rfl) ⟨18153, by rfl⟩ : syracuseStep 193637 = 36307) (by norm_num)
theorem B357493 : Blo 139791 357493 := bbase (se 5 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 357493 = 33515) (by norm_num)
theorem B160897 : Blo 139791 160897 := bbase (se 2 (by rfl) ⟨60336, by rfl⟩ : syracuseStep 160897 = 120673) (by norm_num)
theorem B160933 : Blo 139791 160933 := bbase (se 4 (by rfl) ⟨15087, by rfl⟩ : syracuseStep 160933 = 30175) (by norm_num)
theorem B160969 : Blo 139791 160969 := bbase (se 2 (by rfl) ⟨60363, by rfl⟩ : syracuseStep 160969 = 120727) (by norm_num)
theorem B914645 : Blo 139791 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B357605 : Blo 139791 357605 := bbase (se 4 (by rfl) ⟨33525, by rfl⟩ : syracuseStep 357605 = 67051) (by norm_num)
theorem B161005 : Blo 139791 161005 := bbase (se 3 (by rfl) ⟨30188, by rfl⟩ : syracuseStep 161005 = 60377) (by norm_num)
theorem B161041 : Blo 139791 161041 := bbase (se 2 (by rfl) ⟨60390, by rfl⟩ : syracuseStep 161041 = 120781) (by norm_num)
theorem B1209653 : Blo 139791 1209653 := bbase (se 5 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 1209653 = 113405) (by norm_num)
theorem B161077 : Blo 139791 161077 := bbase (se 5 (by rfl) ⟨7550, by rfl⟩ : syracuseStep 161077 = 15101) (by norm_num)
theorem B161113 : Blo 139791 161113 := bbase (se 2 (by rfl) ⟨60417, by rfl⟩ : syracuseStep 161113 = 120835) (by norm_num)
theorem B161149 : Blo 139791 161149 := bbase (se 3 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 161149 = 60431) (by norm_num)
theorem B161185 : Blo 139791 161185 := bbase (se 2 (by rfl) ⟨60444, by rfl⟩ : syracuseStep 161185 = 120889) (by norm_num)
theorem B357797 : Blo 139791 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B161221 : Blo 139791 161221 := bbase (se 4 (by rfl) ⟨15114, by rfl⟩ : syracuseStep 161221 = 30229) (by norm_num)
theorem B161257 : Blo 139791 161257 := bbase (se 2 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 161257 = 120943) (by norm_num)
theorem B161293 : Blo 139791 161293 := bbase (se 3 (by rfl) ⟨30242, by rfl⟩ : syracuseStep 161293 = 60485) (by norm_num)
theorem B161329 : Blo 139791 161329 := bbase (se 2 (by rfl) ⟨60498, by rfl⟩ : syracuseStep 161329 = 120997) (by norm_num)
theorem B1799765 : Blo 139791 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B161365 : Blo 139791 161365 := bbase (se 8 (by rfl) ⟨945, by rfl⟩ : syracuseStep 161365 = 1891) (by norm_num)
theorem B161401 : Blo 139791 161401 := bbase (se 2 (by rfl) ⟨60525, by rfl⟩ : syracuseStep 161401 = 121051) (by norm_num)
theorem B718469 : Blo 139791 718469 := bbase (se 4 (by rfl) ⟨67356, by rfl⟩ : syracuseStep 718469 = 134713) (by norm_num)
theorem B161437 : Blo 139791 161437 := bbase (se 3 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 161437 = 60539) (by norm_num)
theorem B161473 : Blo 139791 161473 := bbase (se 2 (by rfl) ⟨60552, by rfl⟩ : syracuseStep 161473 = 121105) (by norm_num)
theorem B227021 : Blo 139791 227021 := bbase (se 3 (by rfl) ⟨42566, by rfl⟩ : syracuseStep 227021 = 85133) (by norm_num)
theorem B161509 : Blo 139791 161509 := bbase (se 4 (by rfl) ⟨15141, by rfl⟩ : syracuseStep 161509 = 30283) (by norm_num)
theorem B358141 : Blo 139791 358141 := bbase (se 3 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 358141 = 134303) (by norm_num)
theorem B161545 : Blo 139791 161545 := bbase (se 2 (by rfl) ⟨60579, by rfl⟩ : syracuseStep 161545 = 121159) (by norm_num)
theorem B161581 : Blo 139791 161581 := bbase (se 3 (by rfl) ⟨30296, by rfl⟩ : syracuseStep 161581 = 60593) (by norm_num)
theorem B161617 : Blo 139791 161617 := bbase (se 2 (by rfl) ⟨60606, by rfl⟩ : syracuseStep 161617 = 121213) (by norm_num)
theorem B358253 : Blo 139791 358253 := bbase (se 3 (by rfl) ⟨67172, by rfl⟩ : syracuseStep 358253 = 134345) (by norm_num)
theorem B161653 : Blo 139791 161653 := bbase (se 5 (by rfl) ⟨7577, by rfl⟩ : syracuseStep 161653 = 15155) (by norm_num)
theorem B161689 : Blo 139791 161689 := bbase (se 2 (by rfl) ⟨60633, by rfl⟩ : syracuseStep 161689 = 121267) (by norm_num)
theorem B161725 : Blo 139791 161725 := bbase (se 3 (by rfl) ⟨30323, by rfl⟩ : syracuseStep 161725 = 60647) (by norm_num)
theorem B161761 : Blo 139791 161761 := bbase (se 2 (by rfl) ⟨60660, by rfl⟩ : syracuseStep 161761 = 121321) (by norm_num)
theorem B358445 : Blo 139791 358445 := bbase (se 3 (by rfl) ⟨67208, by rfl⟩ : syracuseStep 358445 = 134417) (by norm_num)
theorem B292925 : Blo 139791 292925 := bbase (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) (by norm_num)
theorem B456965 : Blo 139791 456965 := bbase (se 4 (by rfl) ⟨42840, by rfl⟩ : syracuseStep 456965 = 85681) (by norm_num)
theorem B391493 : Blo 139791 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B227701 : Blo 139791 227701 := bbase (se 5 (by rfl) ⟨10673, by rfl⟩ : syracuseStep 227701 = 21347) (by norm_num)
theorem B358789 : Blo 139791 358789 := bbase (se 4 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 358789 = 67273) (by norm_num)
theorem B227765 : Blo 139791 227765 := bbase (se 5 (by rfl) ⟨10676, by rfl⟩ : syracuseStep 227765 = 21353) (by norm_num)
theorem B358901 : Blo 139791 358901 := bbase (se 5 (by rfl) ⟨16823, by rfl⟩ : syracuseStep 358901 = 33647) (by norm_num)
theorem B260597 : Blo 139791 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B260653 : Blo 139791 260653 := bbase (se 3 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 260653 = 97745) (by norm_num)
theorem B686677 : Blo 139791 686677 := bbase (se 8 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 686677 = 8047) (by norm_num)
theorem B359093 : Blo 139791 359093 := bbase (se 5 (by rfl) ⟨16832, by rfl⟩ : syracuseStep 359093 = 33665) (by norm_num)
theorem B162533 : Blo 139791 162533 := bbase (se 4 (by rfl) ⟨15237, by rfl⟩ : syracuseStep 162533 = 30475) (by norm_num)
theorem B1178389 : Blo 139791 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B162605 : Blo 139791 162605 := bbase (se 3 (by rfl) ⟨30488, by rfl⟩ : syracuseStep 162605 = 60977) (by norm_num)
theorem B1014677 : Blo 139791 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B719765 : Blo 139791 719765 := bbase (se 6 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 719765 = 33739) (by norm_num)
theorem B1637333 : Blo 139791 1637333 := bbase (se 7 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 1637333 = 38375) (by norm_num)
theorem B457733 : Blo 139791 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B359437 : Blo 139791 359437 := bbase (se 3 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 359437 = 134789) (by norm_num)
theorem B359549 : Blo 139791 359549 := bbase (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) (by norm_num)
theorem B458005 : Blo 139791 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B261397 : Blo 139791 261397 := bbase (se 6 (by rfl) ⟨6126, by rfl⟩ : syracuseStep 261397 = 12253) (by norm_num)
theorem B359741 : Blo 139791 359741 := bbase (se 3 (by rfl) ⟨67451, by rfl⟩ : syracuseStep 359741 = 134903) (by norm_num)
theorem B359869 : Blo 139791 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B458245 : Blo 139791 458245 := bbase (se 4 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 458245 = 85921) (by norm_num)
theorem B982613 : Blo 139791 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B360085 : Blo 139791 360085 := bbase (se 6 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 360085 = 16879) (by norm_num)
theorem B229085 : Blo 139791 229085 := bbase (se 3 (by rfl) ⟨42953, by rfl⟩ : syracuseStep 229085 = 85907) (by norm_num)
theorem B360197 : Blo 139791 360197 := bbase (se 4 (by rfl) ⟨33768, by rfl⟩ : syracuseStep 360197 = 67537) (by norm_num)
theorem B491285 : Blo 139791 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B229277 : Blo 139791 229277 := bbase (se 3 (by rfl) ⟨42989, by rfl⟩ : syracuseStep 229277 = 85979) (by norm_num)
theorem B360389 : Blo 139791 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B163829 : Blo 139791 163829 := bbase (se 5 (by rfl) ⟨7679, by rfl⟩ : syracuseStep 163829 = 15359) (by norm_num)
theorem B229969 : Blo 139791 229969 := bstep (se 2 (by rfl) ⟨86238, by rfl⟩ : syracuseStep 229969 = 172477) B172477
theorem B459373 : Blo 139791 459373 := bstep (se 3 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 459373 = 172265) B172265
theorem B262769 : Blo 139791 262769 := bstep (se 2 (by rfl) ⟨98538, by rfl⟩ : syracuseStep 262769 = 197077) B197077
theorem B361169 : Blo 139791 361169 := bstep (se 2 (by rfl) ⟨135438, by rfl⟩ : syracuseStep 361169 = 270877) B270877
theorem B361219 : Blo 139791 361219 := bstep (se 1 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 361219 = 541829) B541829
theorem B361361 : Blo 139791 361361 := bstep (se 2 (by rfl) ⟨135510, by rfl⟩ : syracuseStep 361361 = 271021) B271021
theorem B1573829 : Blo 139791 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B230483 : Blo 139791 230483 := bstep (se 1 (by rfl) ⟨172862, by rfl⟩ : syracuseStep 230483 = 345725) B345725
theorem B722033 : Blo 139791 722033 := bstep (se 2 (by rfl) ⟨270762, by rfl⟩ : syracuseStep 722033 = 541525) B541525
theorem B755021 : Blo 139791 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B362353 : Blo 139791 362353 := bstep (se 2 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 362353 = 271765) B271765
theorem B362627 : Blo 139791 362627 := bstep (se 1 (by rfl) ⟨271970, by rfl⟩ : syracuseStep 362627 = 543941) B543941
theorem B362819 : Blo 139791 362819 := bstep (se 1 (by rfl) ⟨272114, by rfl⟩ : syracuseStep 362819 = 544229) B544229
theorem B723491 : Blo 139791 723491 := bstep (se 1 (by rfl) ⟨542618, by rfl⟩ : syracuseStep 723491 = 1085237) B1085237
theorem B199427 : Blo 139791 199427 := bstep (se 1 (by rfl) ⟨149570, by rfl⟩ : syracuseStep 199427 = 299141) B299141
theorem B920645 : Blo 139791 920645 := bstep (se 4 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 920645 = 172621) B172621
theorem B363761 : Blo 139791 363761 := bstep (se 2 (by rfl) ⟨136410, by rfl⟩ : syracuseStep 363761 = 272821) B272821
theorem B757027 : Blo 139791 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B363811 : Blo 139791 363811 := bstep (se 1 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 363811 = 545717) B545717
theorem B1707317 : Blo 139791 1707317 := bstep (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) B160061
theorem B724301 : Blo 139791 724301 := bstep (se 3 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 724301 = 271613) B271613
theorem B200065 : Blo 139791 200065 := bstep (se 2 (by rfl) ⟨75024, by rfl⟩ : syracuseStep 200065 = 150049) B150049
theorem B363953 : Blo 139791 363953 := bstep (se 2 (by rfl) ⟨136482, by rfl⟩ : syracuseStep 363953 = 272965) B272965
theorem B200179 : Blo 139791 200179 := bstep (se 1 (by rfl) ⟨150134, by rfl⟩ : syracuseStep 200179 = 300269) B300269
theorem B1019405 : Blo 139791 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B298723 : Blo 139791 298723 := bstep (se 1 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 298723 = 448085) B448085
theorem B266161 : Blo 139791 266161 := bstep (se 2 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 266161 = 199621) B199621
theorem B331793 : Blo 139791 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B266321 : Blo 139791 266321 := bstep (se 2 (by rfl) ⟨99870, by rfl⟩ : syracuseStep 266321 = 199741) B199741
theorem B2330765 : Blo 139791 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B692387 : Blo 139791 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B1544501 : Blo 139791 1544501 := bstep (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) B144797
theorem B856433 : Blo 139791 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B266723 : Blo 139791 266723 := bstep (se 1 (by rfl) ⟨200042, by rfl⟩ : syracuseStep 266723 = 400085) B400085
theorem B398125 : Blo 139791 398125 := bstep (se 3 (by rfl) ⟨74648, by rfl⟩ : syracuseStep 398125 = 149297) B149297
theorem B201523 : Blo 139791 201523 := bstep (se 1 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 201523 = 302285) B302285
theorem B398189 : Blo 139791 398189 := bstep (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) B149321
theorem B299953 : Blo 139791 299953 := bstep (se 2 (by rfl) ⟨112482, by rfl⟩ : syracuseStep 299953 = 224965) B224965
theorem B398353 : Blo 139791 398353 := bstep (se 2 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 398353 = 298765) B298765
theorem B169123 : Blo 139791 169123 := bstep (se 1 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 169123 = 253685) B253685
theorem B398513 : Blo 139791 398513 := bstep (se 2 (by rfl) ⟨149442, by rfl⟩ : syracuseStep 398513 = 298885) B298885
theorem B398627 : Blo 139791 398627 := bstep (se 1 (by rfl) ⟨298970, by rfl⟩ : syracuseStep 398627 = 597941) B597941
theorem B267619 : Blo 139791 267619 := bstep (se 1 (by rfl) ⟨200714, by rfl⟩ : syracuseStep 267619 = 401429) B401429
theorem B267779 : Blo 139791 267779 := bstep (se 1 (by rfl) ⟨200834, by rfl⟩ : syracuseStep 267779 = 401669) B401669
theorem B300611 : Blo 139791 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B661069 : Blo 139791 661069 := bstep (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) B247901
theorem B169651 : Blo 139791 169651 := bstep (se 1 (by rfl) ⟨127238, by rfl⟩ : syracuseStep 169651 = 254477) B254477
theorem B202657 : Blo 139791 202657 := bstep (se 2 (by rfl) ⟨75996, by rfl⟩ : syracuseStep 202657 = 151993) B151993
theorem B759779 : Blo 139791 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B202753 : Blo 139791 202753 := bstep (se 2 (by rfl) ⟨76032, by rfl⟩ : syracuseStep 202753 = 152065) B152065
theorem B202819 : Blo 139791 202819 := bstep (se 1 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 202819 = 304229) B304229
theorem B727217 : Blo 139791 727217 := bstep (se 2 (by rfl) ⟨272706, by rfl⟩ : syracuseStep 727217 = 545413) B545413
theorem B399629 : Blo 139791 399629 := bstep (se 3 (by rfl) ⟨74930, by rfl⟩ : syracuseStep 399629 = 149861) B149861
theorem B301457 : Blo 139791 301457 := bstep (se 2 (by rfl) ⟨113046, by rfl⟩ : syracuseStep 301457 = 226093) B226093
theorem B235939 : Blo 139791 235939 := bstep (se 1 (by rfl) ⟨176954, by rfl⟩ : syracuseStep 235939 = 353909) B353909
theorem B399811 : Blo 139791 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B203249 : Blo 139791 203249 := bstep (se 2 (by rfl) ⟨76218, by rfl⟩ : syracuseStep 203249 = 152437) B152437
theorem B236081 : Blo 139791 236081 := bstep (se 2 (by rfl) ⟨88530, by rfl⟩ : syracuseStep 236081 = 177061) B177061
theorem B268849 : Blo 139791 268849 := bstep (se 2 (by rfl) ⟨100818, by rfl⟩ : syracuseStep 268849 = 201637) B201637
theorem B399971 : Blo 139791 399971 := bstep (se 1 (by rfl) ⟨299978, by rfl⟩ : syracuseStep 399971 = 599957) B599957
theorem B694925 : Blo 139791 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B367249 : Blo 139791 367249 := bstep (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) B275437
theorem B531107 : Blo 139791 531107 := bstep (se 1 (by rfl) ⟨398330, by rfl⟩ : syracuseStep 531107 = 796661) B796661
theorem B236209 : Blo 139791 236209 := bstep (se 2 (by rfl) ⟨88578, by rfl⟩ : syracuseStep 236209 = 177157) B177157
theorem B236243 : Blo 139791 236243 := bstep (se 1 (by rfl) ⟨177182, by rfl⟩ : syracuseStep 236243 = 354365) B354365
theorem B236371 : Blo 139791 236371 := bstep (se 1 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 236371 = 354557) B354557
theorem B236513 : Blo 139791 236513 := bstep (se 2 (by rfl) ⟨88692, by rfl⟩ : syracuseStep 236513 = 177385) B177385
theorem B269347 : Blo 139791 269347 := bstep (se 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) B404021
theorem B236641 : Blo 139791 236641 := bstep (se 2 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 236641 = 177481) B177481
theorem B236675 : Blo 139791 236675 := bstep (se 1 (by rfl) ⟨177506, by rfl⟩ : syracuseStep 236675 = 355013) B355013
theorem B236803 : Blo 139791 236803 := bstep (se 1 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 236803 = 355205) B355205
theorem B433421 : Blo 139791 433421 := bstep (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) B162533
theorem B204083 : Blo 139791 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B204115 : Blo 139791 204115 := bstep (se 1 (by rfl) ⟨153086, by rfl⟩ : syracuseStep 204115 = 306173) B306173
theorem B236945 : Blo 139791 236945 := bstep (se 2 (by rfl) ⟨88854, by rfl⟩ : syracuseStep 236945 = 177709) B177709
theorem B204211 : Blo 139791 204211 := bstep (se 1 (by rfl) ⟨153158, by rfl⟩ : syracuseStep 204211 = 306317) B306317
theorem B433603 : Blo 139791 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B433613 : Blo 139791 433613 := bstep (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) B162605
theorem B237073 : Blo 139791 237073 := bstep (se 2 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 237073 = 177805) B177805
theorem B237107 : Blo 139791 237107 := bstep (se 1 (by rfl) ⟨177830, by rfl⟩ : syracuseStep 237107 = 355661) B355661
theorem B269905 : Blo 139791 269905 := bstep (se 2 (by rfl) ⟨101214, by rfl⟩ : syracuseStep 269905 = 202429) B202429
theorem B532109 : Blo 139791 532109 := bstep (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) B199541
theorem B401041 : Blo 139791 401041 := bstep (se 2 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 401041 = 300781) B300781
theorem B237235 : Blo 139791 237235 := bstep (se 1 (by rfl) ⟨177926, by rfl⟩ : syracuseStep 237235 = 355853) B355853
theorem B237377 : Blo 139791 237377 := bstep (se 2 (by rfl) ⟨89016, by rfl⟩ : syracuseStep 237377 = 178033) B178033
theorem B204643 : Blo 139791 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B204707 : Blo 139791 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B237505 : Blo 139791 237505 := bstep (se 2 (by rfl) ⟨89064, by rfl⟩ : syracuseStep 237505 = 178129) B178129
theorem B237539 : Blo 139791 237539 := bstep (se 1 (by rfl) ⟨178154, by rfl⟩ : syracuseStep 237539 = 356309) B356309
theorem B2334691 : Blo 139791 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B270307 : Blo 139791 270307 := bstep (se 1 (by rfl) ⟨202730, by rfl⟩ : syracuseStep 270307 = 405461) B405461
theorem B270353 : Blo 139791 270353 := bstep (se 2 (by rfl) ⟨101382, by rfl⟩ : syracuseStep 270353 = 202765) B202765
theorem B303139 : Blo 139791 303139 := bstep (se 1 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 303139 = 454709) B454709
theorem B237667 : Blo 139791 237667 := bstep (se 1 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 237667 = 356501) B356501
theorem B1614005 : Blo 139791 1614005 := bstep (se 5 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 1614005 = 151313) B151313
theorem B237809 : Blo 139791 237809 := bstep (se 2 (by rfl) ⟨89178, by rfl⟩ : syracuseStep 237809 = 178357) B178357
theorem B270641 : Blo 139791 270641 := bstep (se 2 (by rfl) ⟨101490, by rfl⟩ : syracuseStep 270641 = 202981) B202981
theorem B237937 : Blo 139791 237937 := bstep (se 2 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 237937 = 178453) B178453
theorem B237971 : Blo 139791 237971 := bstep (se 1 (by rfl) ⟨178478, by rfl⟩ : syracuseStep 237971 = 356957) B356957
theorem B303601 : Blo 139791 303601 := bstep (se 2 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 303601 = 227701) B227701
theorem B139795 : Blo 139791 139795 := bstep (se 1 (by rfl) ⟨104846, by rfl⟩ : syracuseStep 139795 = 209693) B209693
theorem B238099 : Blo 139791 238099 := bstep (se 1 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 238099 = 357149) B357149
theorem B139811 : Blo 139791 139811 := bstep (se 1 (by rfl) ⟨104858, by rfl⟩ : syracuseStep 139811 = 209717) B209717
theorem B139827 : Blo 139791 139827 := bstep (se 1 (by rfl) ⟨104870, by rfl⟩ : syracuseStep 139827 = 209741) B209741
theorem B139843 : Blo 139791 139843 := bstep (se 1 (by rfl) ⟨104882, by rfl⟩ : syracuseStep 139843 = 209765) B209765
theorem B139859 : Blo 139791 139859 := bstep (se 1 (by rfl) ⟨104894, by rfl⟩ : syracuseStep 139859 = 209789) B209789
theorem B139875 : Blo 139791 139875 := bstep (se 1 (by rfl) ⟨104906, by rfl⟩ : syracuseStep 139875 = 209813) B209813
theorem B139891 : Blo 139791 139891 := bstep (se 1 (by rfl) ⟨104918, by rfl⟩ : syracuseStep 139891 = 209837) B209837
theorem B139907 : Blo 139791 139907 := bstep (se 1 (by rfl) ⟨104930, by rfl⟩ : syracuseStep 139907 = 209861) B209861
theorem B139923 : Blo 139791 139923 := bstep (se 1 (by rfl) ⟨104942, by rfl⟩ : syracuseStep 139923 = 209885) B209885
theorem B238241 : Blo 139791 238241 := bstep (se 2 (by rfl) ⟨89340, by rfl⟩ : syracuseStep 238241 = 178681) B178681
theorem B139939 : Blo 139791 139939 := bstep (se 1 (by rfl) ⟨104954, by rfl⟩ : syracuseStep 139939 = 209909) B209909
theorem B598691 : Blo 139791 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B139955 : Blo 139791 139955 := bstep (se 1 (by rfl) ⟨104966, by rfl⟩ : syracuseStep 139955 = 209933) B209933
theorem B139971 : Blo 139791 139971 := bstep (se 1 (by rfl) ⟨104978, by rfl⟩ : syracuseStep 139971 = 209957) B209957
theorem B139987 : Blo 139791 139987 := bstep (se 1 (by rfl) ⟨104990, by rfl⟩ : syracuseStep 139987 = 209981) B209981
theorem B140003 : Blo 139791 140003 := bstep (se 1 (by rfl) ⟨105002, by rfl⟩ : syracuseStep 140003 = 210005) B210005
theorem B336611 : Blo 139791 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B140019 : Blo 139791 140019 := bstep (se 1 (by rfl) ⟨105014, by rfl⟩ : syracuseStep 140019 = 210029) B210029
theorem B140035 : Blo 139791 140035 := bstep (se 1 (by rfl) ⟨105026, by rfl⟩ : syracuseStep 140035 = 210053) B210053
theorem B140051 : Blo 139791 140051 := bstep (se 1 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 140051 = 210077) B210077
theorem B238369 : Blo 139791 238369 := bstep (se 2 (by rfl) ⟨89388, by rfl⟩ : syracuseStep 238369 = 178777) B178777
theorem B140067 : Blo 139791 140067 := bstep (se 1 (by rfl) ⟨105050, by rfl⟩ : syracuseStep 140067 = 210101) B210101
theorem B140083 : Blo 139791 140083 := bstep (se 1 (by rfl) ⟨105062, by rfl⟩ : syracuseStep 140083 = 210125) B210125
theorem B140099 : Blo 139791 140099 := bstep (se 1 (by rfl) ⟨105074, by rfl⟩ : syracuseStep 140099 = 210149) B210149
theorem B238403 : Blo 139791 238403 := bstep (se 1 (by rfl) ⟨178802, by rfl⟩ : syracuseStep 238403 = 357605) B357605
theorem B140115 : Blo 139791 140115 := bstep (se 1 (by rfl) ⟨105086, by rfl⟩ : syracuseStep 140115 = 210173) B210173
theorem B140131 : Blo 139791 140131 := bstep (se 1 (by rfl) ⟨105098, by rfl⟩ : syracuseStep 140131 = 210197) B210197
theorem B140147 : Blo 139791 140147 := bstep (se 1 (by rfl) ⟨105110, by rfl⟩ : syracuseStep 140147 = 210221) B210221
theorem B140163 : Blo 139791 140163 := bstep (se 1 (by rfl) ⟨105122, by rfl⟩ : syracuseStep 140163 = 210245) B210245
theorem B402317 : Blo 139791 402317 := bstep (se 3 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 402317 = 150869) B150869
theorem B140179 : Blo 139791 140179 := bstep (se 1 (by rfl) ⟨105134, by rfl⟩ : syracuseStep 140179 = 210269) B210269
theorem B140195 : Blo 139791 140195 := bstep (se 1 (by rfl) ⟨105146, by rfl⟩ : syracuseStep 140195 = 210293) B210293
theorem B140211 : Blo 139791 140211 := bstep (se 1 (by rfl) ⟨105158, by rfl⟩ : syracuseStep 140211 = 210317) B210317
theorem B140227 : Blo 139791 140227 := bstep (se 1 (by rfl) ⟨105170, by rfl⟩ : syracuseStep 140227 = 210341) B210341
theorem B238531 : Blo 139791 238531 := bstep (se 1 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 238531 = 357797) B357797
theorem B140243 : Blo 139791 140243 := bstep (se 1 (by rfl) ⟨105182, by rfl⟩ : syracuseStep 140243 = 210365) B210365
theorem B140259 : Blo 139791 140259 := bstep (se 1 (by rfl) ⟨105194, by rfl⟩ : syracuseStep 140259 = 210389) B210389
theorem B140275 : Blo 139791 140275 := bstep (se 1 (by rfl) ⟨105206, by rfl⟩ : syracuseStep 140275 = 210413) B210413
theorem B140291 : Blo 139791 140291 := bstep (se 1 (by rfl) ⟨105218, by rfl⟩ : syracuseStep 140291 = 210437) B210437
theorem B271363 : Blo 139791 271363 := bstep (se 1 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 271363 = 407045) B407045
theorem B140307 : Blo 139791 140307 := bstep (se 1 (by rfl) ⟨105230, by rfl⟩ : syracuseStep 140307 = 210461) B210461
theorem B140323 : Blo 139791 140323 := bstep (se 1 (by rfl) ⟨105242, by rfl⟩ : syracuseStep 140323 = 210485) B210485
theorem B140339 : Blo 139791 140339 := bstep (se 1 (by rfl) ⟨105254, by rfl⟩ : syracuseStep 140339 = 210509) B210509
theorem B140355 : Blo 139791 140355 := bstep (se 1 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 140355 = 210533) B210533
theorem B402499 : Blo 139791 402499 := bstep (se 1 (by rfl) ⟨301874, by rfl⟩ : syracuseStep 402499 = 603749) B603749
theorem B271441 : Blo 139791 271441 := bstep (se 2 (by rfl) ⟨101790, by rfl⟩ : syracuseStep 271441 = 203581) B203581
theorem B238673 : Blo 139791 238673 := bstep (se 2 (by rfl) ⟨89502, by rfl⟩ : syracuseStep 238673 = 179005) B179005
theorem B140371 : Blo 139791 140371 := bstep (se 1 (by rfl) ⟨105278, by rfl⟩ : syracuseStep 140371 = 210557) B210557
theorem B140387 : Blo 139791 140387 := bstep (se 1 (by rfl) ⟨105290, by rfl⟩ : syracuseStep 140387 = 210581) B210581
theorem B402545 : Blo 139791 402545 := bstep (se 2 (by rfl) ⟨150954, by rfl⟩ : syracuseStep 402545 = 301909) B301909
theorem B140403 : Blo 139791 140403 := bstep (se 1 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 140403 = 210605) B210605
theorem B140419 : Blo 139791 140419 := bstep (se 1 (by rfl) ⟨105314, by rfl⟩ : syracuseStep 140419 = 210629) B210629
theorem B140435 : Blo 139791 140435 := bstep (se 1 (by rfl) ⟨105326, by rfl⟩ : syracuseStep 140435 = 210653) B210653
theorem B140451 : Blo 139791 140451 := bstep (se 1 (by rfl) ⟨105338, by rfl⟩ : syracuseStep 140451 = 210677) B210677
theorem B140467 : Blo 139791 140467 := bstep (se 1 (by rfl) ⟨105350, by rfl⟩ : syracuseStep 140467 = 210701) B210701
theorem B140483 : Blo 139791 140483 := bstep (se 1 (by rfl) ⟨105362, by rfl⟩ : syracuseStep 140483 = 210725) B210725
theorem B238801 : Blo 139791 238801 := bstep (se 2 (by rfl) ⟨89550, by rfl⟩ : syracuseStep 238801 = 179101) B179101
theorem B140499 : Blo 139791 140499 := bstep (se 1 (by rfl) ⟨105374, by rfl⟩ : syracuseStep 140499 = 210749) B210749
theorem B140515 : Blo 139791 140515 := bstep (se 1 (by rfl) ⟨105386, by rfl⟩ : syracuseStep 140515 = 210773) B210773
theorem B140531 : Blo 139791 140531 := bstep (se 1 (by rfl) ⟨105398, by rfl⟩ : syracuseStep 140531 = 210797) B210797
theorem B238835 : Blo 139791 238835 := bstep (se 1 (by rfl) ⟨179126, by rfl⟩ : syracuseStep 238835 = 358253) B358253
theorem B140547 : Blo 139791 140547 := bstep (se 1 (by rfl) ⟨105410, by rfl⟩ : syracuseStep 140547 = 210821) B210821
theorem B140563 : Blo 139791 140563 := bstep (se 1 (by rfl) ⟨105422, by rfl⟩ : syracuseStep 140563 = 210845) B210845
theorem B140579 : Blo 139791 140579 := bstep (se 1 (by rfl) ⟨105434, by rfl⟩ : syracuseStep 140579 = 210869) B210869
theorem B140595 : Blo 139791 140595 := bstep (se 1 (by rfl) ⟨105446, by rfl⟩ : syracuseStep 140595 = 210893) B210893
theorem B140611 : Blo 139791 140611 := bstep (se 1 (by rfl) ⟨105458, by rfl⟩ : syracuseStep 140611 = 210917) B210917
theorem B140627 : Blo 139791 140627 := bstep (se 1 (by rfl) ⟨105470, by rfl⟩ : syracuseStep 140627 = 210941) B210941
theorem B140643 : Blo 139791 140643 := bstep (se 1 (by rfl) ⟨105482, by rfl⟩ : syracuseStep 140643 = 210965) B210965
theorem B140659 : Blo 139791 140659 := bstep (se 1 (by rfl) ⟨105494, by rfl⟩ : syracuseStep 140659 = 210989) B210989
theorem B238963 : Blo 139791 238963 := bstep (se 1 (by rfl) ⟨179222, by rfl⟩ : syracuseStep 238963 = 358445) B358445
theorem B140675 : Blo 139791 140675 := bstep (se 1 (by rfl) ⟨105506, by rfl⟩ : syracuseStep 140675 = 211013) B211013
theorem B140691 : Blo 139791 140691 := bstep (se 1 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 140691 = 211037) B211037
theorem B140707 : Blo 139791 140707 := bstep (se 1 (by rfl) ⟨105530, by rfl⟩ : syracuseStep 140707 = 211061) B211061
theorem B140723 : Blo 139791 140723 := bstep (se 1 (by rfl) ⟨105542, by rfl⟩ : syracuseStep 140723 = 211085) B211085
theorem B140739 : Blo 139791 140739 := bstep (se 1 (by rfl) ⟨105554, by rfl⟩ : syracuseStep 140739 = 211109) B211109
theorem B271811 : Blo 139791 271811 := bstep (se 1 (by rfl) ⟨203858, by rfl⟩ : syracuseStep 271811 = 407717) B407717
theorem B140755 : Blo 139791 140755 := bstep (se 1 (by rfl) ⟨105566, by rfl⟩ : syracuseStep 140755 = 211133) B211133
theorem B337379 : Blo 139791 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B140771 : Blo 139791 140771 := bstep (se 1 (by rfl) ⟨105578, by rfl⟩ : syracuseStep 140771 = 211157) B211157
theorem B140787 : Blo 139791 140787 := bstep (se 1 (by rfl) ⟨105590, by rfl⟩ : syracuseStep 140787 = 211181) B211181
theorem B239105 : Blo 139791 239105 := bstep (se 2 (by rfl) ⟨89664, by rfl⟩ : syracuseStep 239105 = 179329) B179329
theorem B140803 : Blo 139791 140803 := bstep (se 1 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 140803 = 211205) B211205
theorem B304643 : Blo 139791 304643 := bstep (se 1 (by rfl) ⟨228482, by rfl⟩ : syracuseStep 304643 = 456965) B456965
theorem B140819 : Blo 139791 140819 := bstep (se 1 (by rfl) ⟨105614, by rfl⟩ : syracuseStep 140819 = 211229) B211229
theorem B140835 : Blo 139791 140835 := bstep (se 1 (by rfl) ⟨105626, by rfl⟩ : syracuseStep 140835 = 211253) B211253
theorem B140851 : Blo 139791 140851 := bstep (se 1 (by rfl) ⟨105638, by rfl⟩ : syracuseStep 140851 = 211277) B211277
theorem B140867 : Blo 139791 140867 := bstep (se 1 (by rfl) ⟨105650, by rfl⟩ : syracuseStep 140867 = 211301) B211301
theorem B796229 : Blo 139791 796229 := bstep (se 4 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 796229 = 149293) B149293
theorem B140883 : Blo 139791 140883 := bstep (se 1 (by rfl) ⟨105662, by rfl⟩ : syracuseStep 140883 = 211325) B211325
theorem B140899 : Blo 139791 140899 := bstep (se 1 (by rfl) ⟨105674, by rfl⟩ : syracuseStep 140899 = 211349) B211349
theorem B140915 : Blo 139791 140915 := bstep (se 1 (by rfl) ⟨105686, by rfl⟩ : syracuseStep 140915 = 211373) B211373
theorem B239233 : Blo 139791 239233 := bstep (se 2 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 239233 = 179425) B179425
theorem B140931 : Blo 139791 140931 := bstep (se 1 (by rfl) ⟨105698, by rfl⟩ : syracuseStep 140931 = 211397) B211397
theorem B140947 : Blo 139791 140947 := bstep (se 1 (by rfl) ⟨105710, by rfl⟩ : syracuseStep 140947 = 211421) B211421
theorem B140963 : Blo 139791 140963 := bstep (se 1 (by rfl) ⟨105722, by rfl⟩ : syracuseStep 140963 = 211445) B211445
theorem B239267 : Blo 139791 239267 := bstep (se 1 (by rfl) ⟨179450, by rfl⟩ : syracuseStep 239267 = 358901) B358901
theorem B206513 : Blo 139791 206513 := bstep (se 2 (by rfl) ⟨77442, by rfl⟩ : syracuseStep 206513 = 154885) B154885
theorem B140979 : Blo 139791 140979 := bstep (se 1 (by rfl) ⟨105734, by rfl⟩ : syracuseStep 140979 = 211469) B211469
theorem B140995 : Blo 139791 140995 := bstep (se 1 (by rfl) ⟨105746, by rfl⟩ : syracuseStep 140995 = 211493) B211493
theorem B534221 : Blo 139791 534221 := bstep (se 3 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 534221 = 200333) B200333
theorem B141011 : Blo 139791 141011 := bstep (se 1 (by rfl) ⟨105758, by rfl⟩ : syracuseStep 141011 = 211517) B211517
theorem B141027 : Blo 139791 141027 := bstep (se 1 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 141027 = 211541) B211541
theorem B272099 : Blo 139791 272099 := bstep (se 1 (by rfl) ⟨204074, by rfl⟩ : syracuseStep 272099 = 408149) B408149
theorem B141043 : Blo 139791 141043 := bstep (se 1 (by rfl) ⟨105782, by rfl⟩ : syracuseStep 141043 = 211565) B211565
theorem B141059 : Blo 139791 141059 := bstep (se 1 (by rfl) ⟨105794, by rfl⟩ : syracuseStep 141059 = 211589) B211589
theorem B141075 : Blo 139791 141075 := bstep (se 1 (by rfl) ⟨105806, by rfl⟩ : syracuseStep 141075 = 211613) B211613
theorem B141091 : Blo 139791 141091 := bstep (se 1 (by rfl) ⟨105818, by rfl⟩ : syracuseStep 141091 = 211637) B211637
theorem B239395 : Blo 139791 239395 := bstep (se 1 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 239395 = 359093) B359093
theorem B141107 : Blo 139791 141107 := bstep (se 1 (by rfl) ⟨105830, by rfl⟩ : syracuseStep 141107 = 211661) B211661
theorem B141123 : Blo 139791 141123 := bstep (se 1 (by rfl) ⟨105842, by rfl⟩ : syracuseStep 141123 = 211685) B211685
theorem B141139 : Blo 139791 141139 := bstep (se 1 (by rfl) ⟨105854, by rfl⟩ : syracuseStep 141139 = 211709) B211709
theorem B141155 : Blo 139791 141155 := bstep (se 1 (by rfl) ⟨105866, by rfl⟩ : syracuseStep 141155 = 211733) B211733
theorem B141171 : Blo 139791 141171 := bstep (se 1 (by rfl) ⟨105878, by rfl⟩ : syracuseStep 141171 = 211757) B211757
theorem B141187 : Blo 139791 141187 := bstep (se 1 (by rfl) ⟨105890, by rfl⟩ : syracuseStep 141187 = 211781) B211781
theorem B141203 : Blo 139791 141203 := bstep (se 1 (by rfl) ⟨105902, by rfl⟩ : syracuseStep 141203 = 211805) B211805
theorem B141219 : Blo 139791 141219 := bstep (se 1 (by rfl) ⟨105914, by rfl⟩ : syracuseStep 141219 = 211829) B211829
theorem B337841 : Blo 139791 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B239537 : Blo 139791 239537 := bstep (se 2 (by rfl) ⟨89826, by rfl⟩ : syracuseStep 239537 = 179653) B179653
theorem B141235 : Blo 139791 141235 := bstep (se 1 (by rfl) ⟨105926, by rfl⟩ : syracuseStep 141235 = 211853) B211853
theorem B141251 : Blo 139791 141251 := bstep (se 1 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 141251 = 211877) B211877
theorem B141267 : Blo 139791 141267 := bstep (se 1 (by rfl) ⟨105950, by rfl⟩ : syracuseStep 141267 = 211901) B211901
theorem B141283 : Blo 139791 141283 := bstep (se 1 (by rfl) ⟨105962, by rfl⟩ : syracuseStep 141283 = 211925) B211925
theorem B1091555 : Blo 139791 1091555 := bstep (se 1 (by rfl) ⟨818666, by rfl⟩ : syracuseStep 1091555 = 1637333) B1637333
theorem B141299 : Blo 139791 141299 := bstep (se 1 (by rfl) ⟨105974, by rfl⟩ : syracuseStep 141299 = 211949) B211949
theorem B141315 : Blo 139791 141315 := bstep (se 1 (by rfl) ⟨105986, by rfl⟩ : syracuseStep 141315 = 211973) B211973
theorem B305155 : Blo 139791 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B337937 : Blo 139791 337937 := bstep (se 2 (by rfl) ⟨126726, by rfl⟩ : syracuseStep 337937 = 253453) B253453
theorem B141331 : Blo 139791 141331 := bstep (se 1 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 141331 = 211997) B211997
theorem B141347 : Blo 139791 141347 := bstep (se 1 (by rfl) ⟨106010, by rfl⟩ : syracuseStep 141347 = 212021) B212021
theorem B239665 : Blo 139791 239665 := bstep (se 2 (by rfl) ⟨89874, by rfl⟩ : syracuseStep 239665 = 179749) B179749
theorem B141363 : Blo 139791 141363 := bstep (se 1 (by rfl) ⟨106022, by rfl⟩ : syracuseStep 141363 = 212045) B212045
theorem B141379 : Blo 139791 141379 := bstep (se 1 (by rfl) ⟨106034, by rfl⟩ : syracuseStep 141379 = 212069) B212069
theorem B141395 : Blo 139791 141395 := bstep (se 1 (by rfl) ⟨106046, by rfl⟩ : syracuseStep 141395 = 212093) B212093
theorem B239699 : Blo 139791 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B141411 : Blo 139791 141411 := bstep (se 1 (by rfl) ⟨106058, by rfl⟩ : syracuseStep 141411 = 212117) B212117
theorem B141427 : Blo 139791 141427 := bstep (se 1 (by rfl) ⟨106070, by rfl⟩ : syracuseStep 141427 = 212141) B212141
theorem B206977 : Blo 139791 206977 := bstep (se 2 (by rfl) ⟨77616, by rfl⟩ : syracuseStep 206977 = 155233) B155233
theorem B141443 : Blo 139791 141443 := bstep (se 1 (by rfl) ⟨106082, by rfl⟩ : syracuseStep 141443 = 212165) B212165
theorem B141459 : Blo 139791 141459 := bstep (se 1 (by rfl) ⟨106094, by rfl⟩ : syracuseStep 141459 = 212189) B212189
theorem B141475 : Blo 139791 141475 := bstep (se 1 (by rfl) ⟨106106, by rfl⟩ : syracuseStep 141475 = 212213) B212213
theorem B141491 : Blo 139791 141491 := bstep (se 1 (by rfl) ⟨106118, by rfl⟩ : syracuseStep 141491 = 212237) B212237
theorem B141507 : Blo 139791 141507 := bstep (se 1 (by rfl) ⟨106130, by rfl⟩ : syracuseStep 141507 = 212261) B212261
theorem B141523 : Blo 139791 141523 := bstep (se 1 (by rfl) ⟨106142, by rfl⟩ : syracuseStep 141523 = 212285) B212285
theorem B239827 : Blo 139791 239827 := bstep (se 1 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 239827 = 359741) B359741
theorem B141539 : Blo 139791 141539 := bstep (se 1 (by rfl) ⟨106154, by rfl⟩ : syracuseStep 141539 = 212309) B212309
theorem B141555 : Blo 139791 141555 := bstep (se 1 (by rfl) ⟨106166, by rfl⟩ : syracuseStep 141555 = 212333) B212333
theorem B141571 : Blo 139791 141571 := bstep (se 1 (by rfl) ⟨106178, by rfl⟩ : syracuseStep 141571 = 212357) B212357
theorem B141587 : Blo 139791 141587 := bstep (se 1 (by rfl) ⟨106190, by rfl⟩ : syracuseStep 141587 = 212381) B212381
theorem B3352853 : Blo 139791 3352853 := bstep (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) B157165
theorem B141603 : Blo 139791 141603 := bstep (se 1 (by rfl) ⟨106202, by rfl⟩ : syracuseStep 141603 = 212405) B212405
theorem B141619 : Blo 139791 141619 := bstep (se 1 (by rfl) ⟨106214, by rfl⟩ : syracuseStep 141619 = 212429) B212429
theorem B141635 : Blo 139791 141635 := bstep (se 1 (by rfl) ⟨106226, by rfl⟩ : syracuseStep 141635 = 212453) B212453
theorem B141651 : Blo 139791 141651 := bstep (se 1 (by rfl) ⟨106238, by rfl⟩ : syracuseStep 141651 = 212477) B212477
theorem B239969 : Blo 139791 239969 := bstep (se 2 (by rfl) ⟨89988, by rfl⟩ : syracuseStep 239969 = 179977) B179977
theorem B141667 : Blo 139791 141667 := bstep (se 1 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 141667 = 212501) B212501
theorem B141683 : Blo 139791 141683 := bstep (se 1 (by rfl) ⟨106262, by rfl⟩ : syracuseStep 141683 = 212525) B212525
theorem B141699 : Blo 139791 141699 := bstep (se 1 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 141699 = 212549) B212549
theorem B141715 : Blo 139791 141715 := bstep (se 1 (by rfl) ⟨106286, by rfl⟩ : syracuseStep 141715 = 212573) B212573
theorem B141731 : Blo 139791 141731 := bstep (se 1 (by rfl) ⟨106298, by rfl⟩ : syracuseStep 141731 = 212597) B212597
theorem B141747 : Blo 139791 141747 := bstep (se 1 (by rfl) ⟨106310, by rfl⟩ : syracuseStep 141747 = 212621) B212621
theorem B141763 : Blo 139791 141763 := bstep (se 1 (by rfl) ⟨106322, by rfl⟩ : syracuseStep 141763 = 212645) B212645
theorem B141779 : Blo 139791 141779 := bstep (se 1 (by rfl) ⟨106334, by rfl⟩ : syracuseStep 141779 = 212669) B212669
theorem B240097 : Blo 139791 240097 := bstep (se 2 (by rfl) ⟨90036, by rfl⟩ : syracuseStep 240097 = 180073) B180073
theorem B141795 : Blo 139791 141795 := bstep (se 1 (by rfl) ⟨106346, by rfl⟩ : syracuseStep 141795 = 212693) B212693
theorem B535025 : Blo 139791 535025 := bstep (se 2 (by rfl) ⟨200634, by rfl⟩ : syracuseStep 535025 = 401269) B401269
theorem B141811 : Blo 139791 141811 := bstep (se 1 (by rfl) ⟨106358, by rfl⟩ : syracuseStep 141811 = 212717) B212717
theorem B141827 : Blo 139791 141827 := bstep (se 1 (by rfl) ⟨106370, by rfl⟩ : syracuseStep 141827 = 212741) B212741
theorem B240131 : Blo 139791 240131 := bstep (se 1 (by rfl) ⟨180098, by rfl⟩ : syracuseStep 240131 = 360197) B360197
theorem B141843 : Blo 139791 141843 := bstep (se 1 (by rfl) ⟨106382, by rfl⟩ : syracuseStep 141843 = 212765) B212765
theorem B141859 : Blo 139791 141859 := bstep (se 1 (by rfl) ⟨106394, by rfl⟩ : syracuseStep 141859 = 212789) B212789
theorem B404003 : Blo 139791 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B141875 : Blo 139791 141875 := bstep (se 1 (by rfl) ⟨106406, by rfl⟩ : syracuseStep 141875 = 212813) B212813
theorem B141891 : Blo 139791 141891 := bstep (se 1 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 141891 = 212837) B212837
theorem B141907 : Blo 139791 141907 := bstep (se 1 (by rfl) ⟨106430, by rfl⟩ : syracuseStep 141907 = 212861) B212861
theorem B141923 : Blo 139791 141923 := bstep (se 1 (by rfl) ⟨106442, by rfl⟩ : syracuseStep 141923 = 212885) B212885
theorem B141939 : Blo 139791 141939 := bstep (se 1 (by rfl) ⟨106454, by rfl⟩ : syracuseStep 141939 = 212909) B212909
theorem B141955 : Blo 139791 141955 := bstep (se 1 (by rfl) ⟨106466, by rfl⟩ : syracuseStep 141955 = 212933) B212933
theorem B240259 : Blo 139791 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B436877 : Blo 139791 436877 := bstep (se 3 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 436877 = 163829) B163829
theorem B141971 : Blo 139791 141971 := bstep (se 1 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 141971 = 212957) B212957
theorem B141987 : Blo 139791 141987 := bstep (se 1 (by rfl) ⟨106490, by rfl⟩ : syracuseStep 141987 = 212981) B212981
theorem B142003 : Blo 139791 142003 := bstep (se 1 (by rfl) ⟨106502, by rfl⟩ : syracuseStep 142003 = 213005) B213005
theorem B142019 : Blo 139791 142019 := bstep (se 1 (by rfl) ⟨106514, by rfl⟩ : syracuseStep 142019 = 213029) B213029
theorem B305873 : Blo 139791 305873 := bstep (se 2 (by rfl) ⟨114702, by rfl⟩ : syracuseStep 305873 = 229405) B229405
theorem B142035 : Blo 139791 142035 := bstep (se 1 (by rfl) ⟨106526, by rfl⟩ : syracuseStep 142035 = 213053) B213053
theorem B142051 : Blo 139791 142051 := bstep (se 1 (by rfl) ⟨106538, by rfl⟩ : syracuseStep 142051 = 213077) B213077
theorem B142067 : Blo 139791 142067 := bstep (se 1 (by rfl) ⟨106550, by rfl⟩ : syracuseStep 142067 = 213101) B213101
theorem B142083 : Blo 139791 142083 := bstep (se 1 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 142083 = 213125) B213125
theorem B240401 : Blo 139791 240401 := bstep (se 2 (by rfl) ⟨90150, by rfl⟩ : syracuseStep 240401 = 180301) B180301
theorem B142099 : Blo 139791 142099 := bstep (se 1 (by rfl) ⟨106574, by rfl⟩ : syracuseStep 142099 = 213149) B213149
theorem B142115 : Blo 139791 142115 := bstep (se 1 (by rfl) ⟨106586, by rfl⟩ : syracuseStep 142115 = 213173) B213173
theorem B142131 : Blo 139791 142131 := bstep (se 1 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 142131 = 213197) B213197
theorem B142147 : Blo 139791 142147 := bstep (se 1 (by rfl) ⟨106610, by rfl⟩ : syracuseStep 142147 = 213221) B213221
theorem B142163 : Blo 139791 142163 := bstep (se 1 (by rfl) ⟨106622, by rfl⟩ : syracuseStep 142163 = 213245) B213245
theorem B142179 : Blo 139791 142179 := bstep (se 1 (by rfl) ⟨106634, by rfl⟩ : syracuseStep 142179 = 213269) B213269
theorem B142195 : Blo 139791 142195 := bstep (se 1 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 142195 = 213293) B213293
theorem B142211 : Blo 139791 142211 := bstep (se 1 (by rfl) ⟨106658, by rfl⟩ : syracuseStep 142211 = 213317) B213317
theorem B240529 : Blo 139791 240529 := bstep (se 2 (by rfl) ⟨90198, by rfl⟩ : syracuseStep 240529 = 180397) B180397
theorem B142227 : Blo 139791 142227 := bstep (se 1 (by rfl) ⟨106670, by rfl⟩ : syracuseStep 142227 = 213341) B213341
theorem B142243 : Blo 139791 142243 := bstep (se 1 (by rfl) ⟨106682, by rfl⟩ : syracuseStep 142243 = 213365) B213365
theorem B142259 : Blo 139791 142259 := bstep (se 1 (by rfl) ⟨106694, by rfl⟩ : syracuseStep 142259 = 213389) B213389
theorem B240563 : Blo 139791 240563 := bstep (se 1 (by rfl) ⟨180422, by rfl⟩ : syracuseStep 240563 = 360845) B360845
theorem B142275 : Blo 139791 142275 := bstep (se 1 (by rfl) ⟨106706, by rfl⟩ : syracuseStep 142275 = 213413) B213413
theorem B142291 : Blo 139791 142291 := bstep (se 1 (by rfl) ⟨106718, by rfl⟩ : syracuseStep 142291 = 213437) B213437
theorem B142307 : Blo 139791 142307 := bstep (se 1 (by rfl) ⟨106730, by rfl⟩ : syracuseStep 142307 = 213461) B213461
theorem B142323 : Blo 139791 142323 := bstep (se 1 (by rfl) ⟨106742, by rfl⟩ : syracuseStep 142323 = 213485) B213485
theorem B142339 : Blo 139791 142339 := bstep (se 1 (by rfl) ⟨106754, by rfl⟩ : syracuseStep 142339 = 213509) B213509
theorem B142355 : Blo 139791 142355 := bstep (se 1 (by rfl) ⟨106766, by rfl⟩ : syracuseStep 142355 = 213533) B213533
theorem B142371 : Blo 139791 142371 := bstep (se 1 (by rfl) ⟨106778, by rfl⟩ : syracuseStep 142371 = 213557) B213557
theorem B142387 : Blo 139791 142387 := bstep (se 1 (by rfl) ⟨106790, by rfl⟩ : syracuseStep 142387 = 213581) B213581
theorem B240691 : Blo 139791 240691 := bstep (se 1 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 240691 = 361037) B361037
theorem B142403 : Blo 139791 142403 := bstep (se 1 (by rfl) ⟨106802, by rfl⟩ : syracuseStep 142403 = 213605) B213605
theorem B142419 : Blo 139791 142419 := bstep (se 1 (by rfl) ⟨106814, by rfl⟩ : syracuseStep 142419 = 213629) B213629
theorem B142435 : Blo 139791 142435 := bstep (se 1 (by rfl) ⟨106826, by rfl⟩ : syracuseStep 142435 = 213653) B213653
theorem B142451 : Blo 139791 142451 := bstep (se 1 (by rfl) ⟨106838, by rfl⟩ : syracuseStep 142451 = 213677) B213677
theorem B142467 : Blo 139791 142467 := bstep (se 1 (by rfl) ⟨106850, by rfl⟩ : syracuseStep 142467 = 213701) B213701
theorem B535693 : Blo 139791 535693 := bstep (se 3 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 535693 = 200885) B200885
theorem B142483 : Blo 139791 142483 := bstep (se 1 (by rfl) ⟨106862, by rfl⟩ : syracuseStep 142483 = 213725) B213725
theorem B142499 : Blo 139791 142499 := bstep (se 1 (by rfl) ⟨106874, by rfl⟩ : syracuseStep 142499 = 213749) B213749
theorem B142515 : Blo 139791 142515 := bstep (se 1 (by rfl) ⟨106886, by rfl⟩ : syracuseStep 142515 = 213773) B213773
theorem B240833 : Blo 139791 240833 := bstep (se 2 (by rfl) ⟨90312, by rfl⟩ : syracuseStep 240833 = 180625) B180625
theorem B142531 : Blo 139791 142531 := bstep (se 1 (by rfl) ⟨106898, by rfl⟩ : syracuseStep 142531 = 213797) B213797
theorem B142547 : Blo 139791 142547 := bstep (se 1 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 142547 = 213821) B213821
theorem B142563 : Blo 139791 142563 := bstep (se 1 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 142563 = 213845) B213845
theorem B142579 : Blo 139791 142579 := bstep (se 1 (by rfl) ⟨106934, by rfl⟩ : syracuseStep 142579 = 213869) B213869
theorem B142595 : Blo 139791 142595 := bstep (se 1 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 142595 = 213893) B213893
theorem B601357 : Blo 139791 601357 := bstep (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) B225509
theorem B142611 : Blo 139791 142611 := bstep (se 1 (by rfl) ⟨106958, by rfl⟩ : syracuseStep 142611 = 213917) B213917
theorem B142627 : Blo 139791 142627 := bstep (se 1 (by rfl) ⟨106970, by rfl⟩ : syracuseStep 142627 = 213941) B213941
theorem B142643 : Blo 139791 142643 := bstep (se 1 (by rfl) ⟨106982, by rfl⟩ : syracuseStep 142643 = 213965) B213965
theorem B240961 : Blo 139791 240961 := bstep (se 2 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 240961 = 180721) B180721
theorem B142659 : Blo 139791 142659 := bstep (se 1 (by rfl) ⟨106994, by rfl⟩ : syracuseStep 142659 = 213989) B213989
theorem B142675 : Blo 139791 142675 := bstep (se 1 (by rfl) ⟨107006, by rfl⟩ : syracuseStep 142675 = 214013) B214013
theorem B142691 : Blo 139791 142691 := bstep (se 1 (by rfl) ⟨107018, by rfl⟩ : syracuseStep 142691 = 214037) B214037
theorem B240995 : Blo 139791 240995 := bstep (se 1 (by rfl) ⟨180746, by rfl⟩ : syracuseStep 240995 = 361493) B361493
theorem B142707 : Blo 139791 142707 := bstep (se 1 (by rfl) ⟨107030, by rfl⟩ : syracuseStep 142707 = 214061) B214061
theorem B142723 : Blo 139791 142723 := bstep (se 1 (by rfl) ⟨107042, by rfl⟩ : syracuseStep 142723 = 214085) B214085
theorem B142739 : Blo 139791 142739 := bstep (se 1 (by rfl) ⟨107054, by rfl⟩ : syracuseStep 142739 = 214109) B214109
theorem B142755 : Blo 139791 142755 := bstep (se 1 (by rfl) ⟨107066, by rfl⟩ : syracuseStep 142755 = 214133) B214133
theorem B142771 : Blo 139791 142771 := bstep (se 1 (by rfl) ⟨107078, by rfl⟩ : syracuseStep 142771 = 214157) B214157
theorem B142787 : Blo 139791 142787 := bstep (se 1 (by rfl) ⟨107090, by rfl⟩ : syracuseStep 142787 = 214181) B214181
theorem B404945 : Blo 139791 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B142803 : Blo 139791 142803 := bstep (se 1 (by rfl) ⟨107102, by rfl⟩ : syracuseStep 142803 = 214205) B214205
theorem B142819 : Blo 139791 142819 := bstep (se 1 (by rfl) ⟨107114, by rfl⟩ : syracuseStep 142819 = 214229) B214229
theorem B241123 : Blo 139791 241123 := bstep (se 1 (by rfl) ⟨180842, by rfl⟩ : syracuseStep 241123 = 361685) B361685
theorem B306659 : Blo 139791 306659 := bstep (se 1 (by rfl) ⟨229994, by rfl⟩ : syracuseStep 306659 = 459989) B459989
theorem B142835 : Blo 139791 142835 := bstep (se 1 (by rfl) ⟨107126, by rfl⟩ : syracuseStep 142835 = 214253) B214253
theorem B142851 : Blo 139791 142851 := bstep (se 1 (by rfl) ⟨107138, by rfl⟩ : syracuseStep 142851 = 214277) B214277
theorem B142867 : Blo 139791 142867 := bstep (se 1 (by rfl) ⟨107150, by rfl⟩ : syracuseStep 142867 = 214301) B214301
theorem B142883 : Blo 139791 142883 := bstep (se 1 (by rfl) ⟨107162, by rfl⟩ : syracuseStep 142883 = 214325) B214325
theorem B405037 : Blo 139791 405037 := bstep (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) B151889
theorem B142899 : Blo 139791 142899 := bstep (se 1 (by rfl) ⟨107174, by rfl⟩ : syracuseStep 142899 = 214349) B214349
theorem B142915 : Blo 139791 142915 := bstep (se 1 (by rfl) ⟨107186, by rfl⟩ : syracuseStep 142915 = 214373) B214373
theorem B142931 : Blo 139791 142931 := bstep (se 1 (by rfl) ⟨107198, by rfl⟩ : syracuseStep 142931 = 214397) B214397
theorem B142947 : Blo 139791 142947 := bstep (se 1 (by rfl) ⟨107210, by rfl⟩ : syracuseStep 142947 = 214421) B214421
theorem B241265 : Blo 139791 241265 := bstep (se 2 (by rfl) ⟨90474, by rfl⟩ : syracuseStep 241265 = 180949) B180949
theorem B142963 : Blo 139791 142963 := bstep (se 1 (by rfl) ⟨107222, by rfl⟩ : syracuseStep 142963 = 214445) B214445
theorem B142979 : Blo 139791 142979 := bstep (se 1 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 142979 = 214469) B214469
theorem B142995 : Blo 139791 142995 := bstep (se 1 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 142995 = 214493) B214493
theorem B143011 : Blo 139791 143011 := bstep (se 1 (by rfl) ⟨107258, by rfl⟩ : syracuseStep 143011 = 214517) B214517
theorem B143027 : Blo 139791 143027 := bstep (se 1 (by rfl) ⟨107270, by rfl⟩ : syracuseStep 143027 = 214541) B214541
theorem B143043 : Blo 139791 143043 := bstep (se 1 (by rfl) ⟨107282, by rfl⟩ : syracuseStep 143043 = 214565) B214565
theorem B143059 : Blo 139791 143059 := bstep (se 1 (by rfl) ⟨107294, by rfl⟩ : syracuseStep 143059 = 214589) B214589
theorem B143075 : Blo 139791 143075 := bstep (se 1 (by rfl) ⟨107306, by rfl⟩ : syracuseStep 143075 = 214613) B214613
theorem B405233 : Blo 139791 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B241393 : Blo 139791 241393 := bstep (se 2 (by rfl) ⟨90522, by rfl⟩ : syracuseStep 241393 = 181045) B181045
theorem B143091 : Blo 139791 143091 := bstep (se 1 (by rfl) ⟨107318, by rfl⟩ : syracuseStep 143091 = 214637) B214637
theorem B143107 : Blo 139791 143107 := bstep (se 1 (by rfl) ⟨107330, by rfl⟩ : syracuseStep 143107 = 214661) B214661
theorem B241427 : Blo 139791 241427 := bstep (se 1 (by rfl) ⟨181070, by rfl⟩ : syracuseStep 241427 = 362141) B362141
theorem B143123 : Blo 139791 143123 := bstep (se 1 (by rfl) ⟨107342, by rfl⟩ : syracuseStep 143123 = 214685) B214685
theorem B143139 : Blo 139791 143139 := bstep (se 1 (by rfl) ⟨107354, by rfl⟩ : syracuseStep 143139 = 214709) B214709
theorem B143155 : Blo 139791 143155 := bstep (se 1 (by rfl) ⟨107366, by rfl⟩ : syracuseStep 143155 = 214733) B214733
theorem B143171 : Blo 139791 143171 := bstep (se 1 (by rfl) ⟨107378, by rfl⟩ : syracuseStep 143171 = 214757) B214757
theorem B143187 : Blo 139791 143187 := bstep (se 1 (by rfl) ⟨107390, by rfl⟩ : syracuseStep 143187 = 214781) B214781
theorem B143203 : Blo 139791 143203 := bstep (se 1 (by rfl) ⟨107402, by rfl⟩ : syracuseStep 143203 = 214805) B214805
theorem B143219 : Blo 139791 143219 := bstep (se 1 (by rfl) ⟨107414, by rfl⟩ : syracuseStep 143219 = 214829) B214829
theorem B143235 : Blo 139791 143235 := bstep (se 1 (by rfl) ⟨107426, by rfl⟩ : syracuseStep 143235 = 214853) B214853
theorem B241555 : Blo 139791 241555 := bstep (se 1 (by rfl) ⟨181166, by rfl⟩ : syracuseStep 241555 = 362333) B362333
theorem B143251 : Blo 139791 143251 := bstep (se 1 (by rfl) ⟨107438, by rfl⟩ : syracuseStep 143251 = 214877) B214877
theorem B536483 : Blo 139791 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B143267 : Blo 139791 143267 := bstep (se 1 (by rfl) ⟨107450, by rfl⟩ : syracuseStep 143267 = 214901) B214901
theorem B143283 : Blo 139791 143283 := bstep (se 1 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 143283 = 214925) B214925
theorem B143299 : Blo 139791 143299 := bstep (se 1 (by rfl) ⟨107474, by rfl⟩ : syracuseStep 143299 = 214949) B214949
theorem B143315 : Blo 139791 143315 := bstep (se 1 (by rfl) ⟨107486, by rfl⟩ : syracuseStep 143315 = 214973) B214973
theorem B143331 : Blo 139791 143331 := bstep (se 1 (by rfl) ⟨107498, by rfl⟩ : syracuseStep 143331 = 214997) B214997
theorem B143347 : Blo 139791 143347 := bstep (se 1 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 143347 = 215021) B215021
theorem B143363 : Blo 139791 143363 := bstep (se 1 (by rfl) ⟨107522, by rfl⟩ : syracuseStep 143363 = 215045) B215045
theorem B143379 : Blo 139791 143379 := bstep (se 1 (by rfl) ⟨107534, by rfl⟩ : syracuseStep 143379 = 215069) B215069
theorem B241697 : Blo 139791 241697 := bstep (se 2 (by rfl) ⟨90636, by rfl⟩ : syracuseStep 241697 = 181273) B181273
theorem B143395 : Blo 139791 143395 := bstep (se 1 (by rfl) ⟨107546, by rfl⟩ : syracuseStep 143395 = 215093) B215093
theorem B143411 : Blo 139791 143411 := bstep (se 1 (by rfl) ⟨107558, by rfl⟩ : syracuseStep 143411 = 215117) B215117
theorem B143427 : Blo 139791 143427 := bstep (se 1 (by rfl) ⟨107570, by rfl⟩ : syracuseStep 143427 = 215141) B215141
theorem B143443 : Blo 139791 143443 := bstep (se 1 (by rfl) ⟨107582, by rfl⟩ : syracuseStep 143443 = 215165) B215165
theorem B143459 : Blo 139791 143459 := bstep (se 1 (by rfl) ⟨107594, by rfl⟩ : syracuseStep 143459 = 215189) B215189
theorem B143475 : Blo 139791 143475 := bstep (se 1 (by rfl) ⟨107606, by rfl⟩ : syracuseStep 143475 = 215213) B215213
theorem B143491 : Blo 139791 143491 := bstep (se 1 (by rfl) ⟨107618, by rfl⟩ : syracuseStep 143491 = 215237) B215237
theorem B143507 : Blo 139791 143507 := bstep (se 1 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 143507 = 215261) B215261
theorem B241825 : Blo 139791 241825 := bstep (se 2 (by rfl) ⟨90684, by rfl⟩ : syracuseStep 241825 = 181369) B181369
theorem B143523 : Blo 139791 143523 := bstep (se 1 (by rfl) ⟨107642, by rfl⟩ : syracuseStep 143523 = 215285) B215285
theorem B143539 : Blo 139791 143539 := bstep (se 1 (by rfl) ⟨107654, by rfl⟩ : syracuseStep 143539 = 215309) B215309
theorem B241859 : Blo 139791 241859 := bstep (se 1 (by rfl) ⟨181394, by rfl⟩ : syracuseStep 241859 = 362789) B362789
theorem B143555 : Blo 139791 143555 := bstep (se 1 (by rfl) ⟨107666, by rfl⟩ : syracuseStep 143555 = 215333) B215333
theorem B143571 : Blo 139791 143571 := bstep (se 1 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 143571 = 215357) B215357
theorem B143587 : Blo 139791 143587 := bstep (se 1 (by rfl) ⟨107690, by rfl⟩ : syracuseStep 143587 = 215381) B215381
theorem B143603 : Blo 139791 143603 := bstep (se 1 (by rfl) ⟨107702, by rfl⟩ : syracuseStep 143603 = 215405) B215405
theorem B143619 : Blo 139791 143619 := bstep (se 1 (by rfl) ⟨107714, by rfl⟩ : syracuseStep 143619 = 215429) B215429
theorem B143635 : Blo 139791 143635 := bstep (se 1 (by rfl) ⟨107726, by rfl⟩ : syracuseStep 143635 = 215453) B215453
theorem B143651 : Blo 139791 143651 := bstep (se 1 (by rfl) ⟨107738, by rfl⟩ : syracuseStep 143651 = 215477) B215477
theorem B602417 : Blo 139791 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B143667 : Blo 139791 143667 := bstep (se 1 (by rfl) ⟨107750, by rfl⟩ : syracuseStep 143667 = 215501) B215501
theorem B241987 : Blo 139791 241987 := bstep (se 1 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 241987 = 362981) B362981
theorem B143683 : Blo 139791 143683 := bstep (se 1 (by rfl) ⟨107762, by rfl⟩ : syracuseStep 143683 = 215525) B215525
theorem B143699 : Blo 139791 143699 := bstep (se 1 (by rfl) ⟨107774, by rfl⟩ : syracuseStep 143699 = 215549) B215549
theorem B143715 : Blo 139791 143715 := bstep (se 1 (by rfl) ⟨107786, by rfl⟩ : syracuseStep 143715 = 215573) B215573
theorem B143731 : Blo 139791 143731 := bstep (se 1 (by rfl) ⟨107798, by rfl⟩ : syracuseStep 143731 = 215597) B215597
theorem B143747 : Blo 139791 143747 := bstep (se 1 (by rfl) ⟨107810, by rfl⟩ : syracuseStep 143747 = 215621) B215621
theorem B143763 : Blo 139791 143763 := bstep (se 1 (by rfl) ⟨107822, by rfl⟩ : syracuseStep 143763 = 215645) B215645
theorem B143779 : Blo 139791 143779 := bstep (se 1 (by rfl) ⟨107834, by rfl⟩ : syracuseStep 143779 = 215669) B215669
theorem B242129 : Blo 139791 242129 := bstep (se 2 (by rfl) ⟨90798, by rfl⟩ : syracuseStep 242129 = 181597) B181597
theorem B537137 : Blo 139791 537137 := bstep (se 2 (by rfl) ⟨201426, by rfl⟩ : syracuseStep 537137 = 402853) B402853
theorem B242257 : Blo 139791 242257 := bstep (se 2 (by rfl) ⟨90846, by rfl⟩ : syracuseStep 242257 = 181693) B181693
theorem B242291 : Blo 139791 242291 := bstep (se 1 (by rfl) ⟨181718, by rfl⟩ : syracuseStep 242291 = 363437) B363437
theorem B144019 : Blo 139791 144019 := bstep (se 1 (by rfl) ⟨108014, by rfl⟩ : syracuseStep 144019 = 216029) B216029
theorem B242419 : Blo 139791 242419 := bstep (se 1 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 242419 = 363629) B363629
theorem B209699 : Blo 139791 209699 := bstep (se 1 (by rfl) ⟨157274, by rfl⟩ : syracuseStep 209699 = 314549) B314549
theorem B209729 : Blo 139791 209729 := bstep (se 2 (by rfl) ⟨78648, by rfl⟩ : syracuseStep 209729 = 157297) B157297
theorem B209747 : Blo 139791 209747 := bstep (se 1 (by rfl) ⟨157310, by rfl⟩ : syracuseStep 209747 = 314621) B314621
theorem B176995 : Blo 139791 176995 := bstep (se 1 (by rfl) ⟨132746, by rfl⟩ : syracuseStep 176995 = 265493) B265493
theorem B209777 : Blo 139791 209777 := bstep (se 2 (by rfl) ⟨78666, by rfl⟩ : syracuseStep 209777 = 157333) B157333
theorem B242561 : Blo 139791 242561 := bstep (se 2 (by rfl) ⟨90960, by rfl⟩ : syracuseStep 242561 = 181921) B181921
theorem B209795 : Blo 139791 209795 := bstep (se 1 (by rfl) ⟨157346, by rfl⟩ : syracuseStep 209795 = 314693) B314693
theorem B209825 : Blo 139791 209825 := bstep (se 2 (by rfl) ⟨78684, by rfl⟩ : syracuseStep 209825 = 157369) B157369
theorem B209843 : Blo 139791 209843 := bstep (se 1 (by rfl) ⟨157382, by rfl⟩ : syracuseStep 209843 = 314765) B314765
theorem B144307 : Blo 139791 144307 := bstep (se 1 (by rfl) ⟨108230, by rfl⟩ : syracuseStep 144307 = 216461) B216461
theorem B472013 : Blo 139791 472013 := bstep (se 3 (by rfl) ⟨88502, by rfl⟩ : syracuseStep 472013 = 177005) B177005
theorem B209873 : Blo 139791 209873 := bstep (se 2 (by rfl) ⟨78702, by rfl⟩ : syracuseStep 209873 = 157405) B157405
theorem B209891 : Blo 139791 209891 := bstep (se 1 (by rfl) ⟨157418, by rfl⟩ : syracuseStep 209891 = 314837) B314837
theorem B209921 : Blo 139791 209921 := bstep (se 2 (by rfl) ⟨78720, by rfl⟩ : syracuseStep 209921 = 157441) B157441
theorem B472067 : Blo 139791 472067 := bstep (se 1 (by rfl) ⟨354050, by rfl⟩ : syracuseStep 472067 = 708101) B708101
theorem B209939 : Blo 139791 209939 := bstep (se 1 (by rfl) ⟨157454, by rfl⟩ : syracuseStep 209939 = 314909) B314909
theorem B209969 : Blo 139791 209969 := bstep (se 2 (by rfl) ⟨78738, by rfl⟩ : syracuseStep 209969 = 157477) B157477
theorem B209987 : Blo 139791 209987 := bstep (se 1 (by rfl) ⟨157490, by rfl⟩ : syracuseStep 209987 = 314981) B314981
theorem B210017 : Blo 139791 210017 := bstep (se 2 (by rfl) ⟨78756, by rfl⟩ : syracuseStep 210017 = 157513) B157513
theorem B210035 : Blo 139791 210035 := bstep (se 1 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 210035 = 315053) B315053
theorem B210065 : Blo 139791 210065 := bstep (se 2 (by rfl) ⟨78774, by rfl⟩ : syracuseStep 210065 = 157549) B157549
theorem B210083 : Blo 139791 210083 := bstep (se 1 (by rfl) ⟨157562, by rfl⟩ : syracuseStep 210083 = 315125) B315125
theorem B406691 : Blo 139791 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B210113 : Blo 139791 210113 := bstep (se 2 (by rfl) ⟨78792, by rfl⟩ : syracuseStep 210113 = 157585) B157585
theorem B210131 : Blo 139791 210131 := bstep (se 1 (by rfl) ⟨157598, by rfl⟩ : syracuseStep 210131 = 315197) B315197
theorem B210161 : Blo 139791 210161 := bstep (se 2 (by rfl) ⟨78810, by rfl⟩ : syracuseStep 210161 = 157621) B157621
theorem B210179 : Blo 139791 210179 := bstep (se 1 (by rfl) ⟨157634, by rfl⟩ : syracuseStep 210179 = 315269) B315269
theorem B472337 : Blo 139791 472337 := bstep (se 2 (by rfl) ⟨177126, by rfl⟩ : syracuseStep 472337 = 354253) B354253
theorem B210209 : Blo 139791 210209 := bstep (se 2 (by rfl) ⟨78828, by rfl⟩ : syracuseStep 210209 = 157657) B157657
theorem B210227 : Blo 139791 210227 := bstep (se 1 (by rfl) ⟨157670, by rfl⟩ : syracuseStep 210227 = 315341) B315341
theorem B800077 : Blo 139791 800077 := bstep (se 3 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 800077 = 300029) B300029
theorem B210257 : Blo 139791 210257 := bstep (se 2 (by rfl) ⟨78846, by rfl⟩ : syracuseStep 210257 = 157693) B157693
theorem B177491 : Blo 139791 177491 := bstep (se 1 (by rfl) ⟨133118, by rfl⟩ : syracuseStep 177491 = 266237) B266237
theorem B210275 : Blo 139791 210275 := bstep (se 1 (by rfl) ⟨157706, by rfl⟩ : syracuseStep 210275 = 315413) B315413
theorem B210305 : Blo 139791 210305 := bstep (se 2 (by rfl) ⟨78864, by rfl⟩ : syracuseStep 210305 = 157729) B157729
theorem B210323 : Blo 139791 210323 := bstep (se 1 (by rfl) ⟨157742, by rfl⟩ : syracuseStep 210323 = 315485) B315485
theorem B210353 : Blo 139791 210353 := bstep (se 2 (by rfl) ⟨78882, by rfl⟩ : syracuseStep 210353 = 157765) B157765
theorem B210371 : Blo 139791 210371 := bstep (se 1 (by rfl) ⟨157778, by rfl⟩ : syracuseStep 210371 = 315557) B315557
theorem B210401 : Blo 139791 210401 := bstep (se 2 (by rfl) ⟨78900, by rfl⟩ : syracuseStep 210401 = 157801) B157801
theorem B210419 : Blo 139791 210419 := bstep (se 1 (by rfl) ⟨157814, by rfl⟩ : syracuseStep 210419 = 315629) B315629
theorem B1848845 : Blo 139791 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B210449 : Blo 139791 210449 := bstep (se 2 (by rfl) ⟨78918, by rfl⟩ : syracuseStep 210449 = 157837) B157837
theorem B210467 : Blo 139791 210467 := bstep (se 1 (by rfl) ⟨157850, by rfl⟩ : syracuseStep 210467 = 315701) B315701
theorem B243251 : Blo 139791 243251 := bstep (se 1 (by rfl) ⟨182438, by rfl⟩ : syracuseStep 243251 = 364877) B364877
theorem B210497 : Blo 139791 210497 := bstep (se 2 (by rfl) ⟨78936, by rfl⟩ : syracuseStep 210497 = 157873) B157873
theorem B210515 : Blo 139791 210515 := bstep (se 1 (by rfl) ⟨157886, by rfl⟩ : syracuseStep 210515 = 315773) B315773
theorem B210545 : Blo 139791 210545 := bstep (se 2 (by rfl) ⟨78954, by rfl⟩ : syracuseStep 210545 = 157909) B157909
theorem B210563 : Blo 139791 210563 := bstep (se 1 (by rfl) ⟨157922, by rfl⟩ : syracuseStep 210563 = 315845) B315845
theorem B210593 : Blo 139791 210593 := bstep (se 2 (by rfl) ⟨78972, by rfl⟩ : syracuseStep 210593 = 157945) B157945
theorem B243361 : Blo 139791 243361 := bstep (se 2 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 243361 = 182521) B182521
theorem B210611 : Blo 139791 210611 := bstep (se 1 (by rfl) ⟨157958, by rfl⟩ : syracuseStep 210611 = 315917) B315917
theorem B210641 : Blo 139791 210641 := bstep (se 2 (by rfl) ⟨78990, by rfl⟩ : syracuseStep 210641 = 157981) B157981
theorem B210659 : Blo 139791 210659 := bstep (se 1 (by rfl) ⟨157994, by rfl⟩ : syracuseStep 210659 = 315989) B315989
theorem B210689 : Blo 139791 210689 := bstep (se 2 (by rfl) ⟨79008, by rfl⟩ : syracuseStep 210689 = 158017) B158017
theorem B210707 : Blo 139791 210707 := bstep (se 1 (by rfl) ⟨158030, by rfl⟩ : syracuseStep 210707 = 316061) B316061
theorem B472877 : Blo 139791 472877 := bstep (se 3 (by rfl) ⟨88664, by rfl⟩ : syracuseStep 472877 = 177329) B177329
theorem B210737 : Blo 139791 210737 := bstep (se 2 (by rfl) ⟨79026, by rfl⟩ : syracuseStep 210737 = 158053) B158053
theorem B210755 : Blo 139791 210755 := bstep (se 1 (by rfl) ⟨158066, by rfl⟩ : syracuseStep 210755 = 316133) B316133
theorem B210785 : Blo 139791 210785 := bstep (se 2 (by rfl) ⟨79044, by rfl⟩ : syracuseStep 210785 = 158089) B158089
theorem B472931 : Blo 139791 472931 := bstep (se 1 (by rfl) ⟨354698, by rfl⟩ : syracuseStep 472931 = 709397) B709397
theorem B767843 : Blo 139791 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B210803 : Blo 139791 210803 := bstep (se 1 (by rfl) ⟨158102, by rfl⟩ : syracuseStep 210803 = 316205) B316205
theorem B210833 : Blo 139791 210833 := bstep (se 2 (by rfl) ⟨79062, by rfl⟩ : syracuseStep 210833 = 158125) B158125
theorem B210851 : Blo 139791 210851 := bstep (se 1 (by rfl) ⟨158138, by rfl⟩ : syracuseStep 210851 = 316277) B316277
theorem B210881 : Blo 139791 210881 := bstep (se 2 (by rfl) ⟨79080, by rfl⟩ : syracuseStep 210881 = 158161) B158161
theorem B407501 : Blo 139791 407501 := bstep (se 3 (by rfl) ⟨76406, by rfl⟩ : syracuseStep 407501 = 152813) B152813
theorem B210899 : Blo 139791 210899 := bstep (se 1 (by rfl) ⟨158174, by rfl⟩ : syracuseStep 210899 = 316349) B316349
theorem B538595 : Blo 139791 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B767971 : Blo 139791 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B210929 : Blo 139791 210929 := bstep (se 2 (by rfl) ⟨79098, by rfl⟩ : syracuseStep 210929 = 158197) B158197
theorem B538609 : Blo 139791 538609 := bstep (se 2 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 538609 = 403957) B403957
theorem B210947 : Blo 139791 210947 := bstep (se 1 (by rfl) ⟨158210, by rfl⟩ : syracuseStep 210947 = 316421) B316421
theorem B178195 : Blo 139791 178195 := bstep (se 1 (by rfl) ⟨133646, by rfl⟩ : syracuseStep 178195 = 267293) B267293
theorem B210977 : Blo 139791 210977 := bstep (se 2 (by rfl) ⟨79116, by rfl⟩ : syracuseStep 210977 = 158233) B158233
theorem B210995 : Blo 139791 210995 := bstep (se 1 (by rfl) ⟨158246, by rfl⟩ : syracuseStep 210995 = 316493) B316493
theorem B211025 : Blo 139791 211025 := bstep (se 2 (by rfl) ⟨79134, by rfl⟩ : syracuseStep 211025 = 158269) B158269
theorem B211043 : Blo 139791 211043 := bstep (se 1 (by rfl) ⟨158282, by rfl⟩ : syracuseStep 211043 = 316565) B316565
theorem B473201 : Blo 139791 473201 := bstep (se 2 (by rfl) ⟨177450, by rfl⟩ : syracuseStep 473201 = 354901) B354901
theorem B178291 : Blo 139791 178291 := bstep (se 1 (by rfl) ⟨133718, by rfl⟩ : syracuseStep 178291 = 267437) B267437
theorem B211073 : Blo 139791 211073 := bstep (se 2 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 211073 = 158305) B158305
theorem B407693 : Blo 139791 407693 := bstep (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) B152885
theorem B211091 : Blo 139791 211091 := bstep (se 1 (by rfl) ⟨158318, by rfl⟩ : syracuseStep 211091 = 316637) B316637
theorem B211121 : Blo 139791 211121 := bstep (se 2 (by rfl) ⟨79170, by rfl⟩ : syracuseStep 211121 = 158341) B158341
theorem B211139 : Blo 139791 211139 := bstep (se 1 (by rfl) ⟨158354, by rfl⟩ : syracuseStep 211139 = 316709) B316709
theorem B211169 : Blo 139791 211169 := bstep (se 2 (by rfl) ⟨79188, by rfl⟩ : syracuseStep 211169 = 158377) B158377
theorem B211187 : Blo 139791 211187 := bstep (se 1 (by rfl) ⟨158390, by rfl⟩ : syracuseStep 211187 = 316781) B316781
theorem B211217 : Blo 139791 211217 := bstep (se 2 (by rfl) ⟨79206, by rfl⟩ : syracuseStep 211217 = 158413) B158413
theorem B211235 : Blo 139791 211235 := bstep (se 1 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 211235 = 316853) B316853
theorem B211265 : Blo 139791 211265 := bstep (se 2 (by rfl) ⟨79224, by rfl⟩ : syracuseStep 211265 = 158449) B158449
theorem B211283 : Blo 139791 211283 := bstep (se 1 (by rfl) ⟨158462, by rfl⟩ : syracuseStep 211283 = 316925) B316925
theorem B211313 : Blo 139791 211313 := bstep (se 2 (by rfl) ⟨79242, by rfl⟩ : syracuseStep 211313 = 158485) B158485
theorem B211331 : Blo 139791 211331 := bstep (se 1 (by rfl) ⟨158498, by rfl⟩ : syracuseStep 211331 = 316997) B316997
theorem B1227149 : Blo 139791 1227149 := bstep (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) B460181
theorem B211361 : Blo 139791 211361 := bstep (se 2 (by rfl) ⟨79260, by rfl⟩ : syracuseStep 211361 = 158521) B158521
theorem B211379 : Blo 139791 211379 := bstep (se 1 (by rfl) ⟨158534, by rfl⟩ : syracuseStep 211379 = 317069) B317069
theorem B899525 : Blo 139791 899525 := bstep (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) B168661
theorem B211409 : Blo 139791 211409 := bstep (se 2 (by rfl) ⟨79278, by rfl⟩ : syracuseStep 211409 = 158557) B158557
theorem B211427 : Blo 139791 211427 := bstep (se 1 (by rfl) ⟨158570, by rfl⟩ : syracuseStep 211427 = 317141) B317141
theorem B211457 : Blo 139791 211457 := bstep (se 2 (by rfl) ⟨79296, by rfl⟩ : syracuseStep 211457 = 158593) B158593
theorem B211475 : Blo 139791 211475 := bstep (se 1 (by rfl) ⟨158606, by rfl⟩ : syracuseStep 211475 = 317213) B317213
theorem B211505 : Blo 139791 211505 := bstep (se 2 (by rfl) ⟨79314, by rfl⟩ : syracuseStep 211505 = 158629) B158629
theorem B211523 : Blo 139791 211523 := bstep (se 1 (by rfl) ⟨158642, by rfl⟩ : syracuseStep 211523 = 317285) B317285
theorem B211553 : Blo 139791 211553 := bstep (se 2 (by rfl) ⟨79332, by rfl⟩ : syracuseStep 211553 = 158665) B158665
theorem B178787 : Blo 139791 178787 := bstep (se 1 (by rfl) ⟨134090, by rfl⟩ : syracuseStep 178787 = 268181) B268181
theorem B211571 : Blo 139791 211571 := bstep (se 1 (by rfl) ⟨158678, by rfl⟩ : syracuseStep 211571 = 317357) B317357
theorem B473741 : Blo 139791 473741 := bstep (se 3 (by rfl) ⟨88826, by rfl⟩ : syracuseStep 473741 = 177653) B177653
theorem B211601 : Blo 139791 211601 := bstep (se 2 (by rfl) ⟨79350, by rfl⟩ : syracuseStep 211601 = 158701) B158701
theorem B211619 : Blo 139791 211619 := bstep (se 1 (by rfl) ⟨158714, by rfl⟩ : syracuseStep 211619 = 317429) B317429
theorem B211649 : Blo 139791 211649 := bstep (se 2 (by rfl) ⟨79368, by rfl⟩ : syracuseStep 211649 = 158737) B158737
theorem B473795 : Blo 139791 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B211667 : Blo 139791 211667 := bstep (se 1 (by rfl) ⟨158750, by rfl⟩ : syracuseStep 211667 = 317501) B317501
theorem B211697 : Blo 139791 211697 := bstep (se 2 (by rfl) ⟨79386, by rfl⟩ : syracuseStep 211697 = 158773) B158773
theorem B211715 : Blo 139791 211715 := bstep (se 1 (by rfl) ⟨158786, by rfl⟩ : syracuseStep 211715 = 317573) B317573
theorem B211745 : Blo 139791 211745 := bstep (se 2 (by rfl) ⟨79404, by rfl⟩ : syracuseStep 211745 = 158809) B158809
theorem B211763 : Blo 139791 211763 := bstep (se 1 (by rfl) ⟨158822, by rfl⟩ : syracuseStep 211763 = 317645) B317645
theorem B211793 : Blo 139791 211793 := bstep (se 2 (by rfl) ⟨79422, by rfl⟩ : syracuseStep 211793 = 158845) B158845
theorem B211811 : Blo 139791 211811 := bstep (se 1 (by rfl) ⟨158858, by rfl⟩ : syracuseStep 211811 = 317717) B317717
theorem B211841 : Blo 139791 211841 := bstep (se 2 (by rfl) ⟨79440, by rfl⟩ : syracuseStep 211841 = 158881) B158881
theorem B211859 : Blo 139791 211859 := bstep (se 1 (by rfl) ⟨158894, by rfl⟩ : syracuseStep 211859 = 317789) B317789
theorem B211889 : Blo 139791 211889 := bstep (se 2 (by rfl) ⟨79458, by rfl⟩ : syracuseStep 211889 = 158917) B158917
theorem B211907 : Blo 139791 211907 := bstep (se 1 (by rfl) ⟨158930, by rfl⟩ : syracuseStep 211907 = 317861) B317861
theorem B474065 : Blo 139791 474065 := bstep (se 2 (by rfl) ⟨177774, by rfl⟩ : syracuseStep 474065 = 355549) B355549
theorem B211937 : Blo 139791 211937 := bstep (se 2 (by rfl) ⟨79476, by rfl⟩ : syracuseStep 211937 = 158953) B158953
theorem B211955 : Blo 139791 211955 := bstep (se 1 (by rfl) ⟨158966, by rfl⟩ : syracuseStep 211955 = 317933) B317933
theorem B211985 : Blo 139791 211985 := bstep (se 2 (by rfl) ⟨79494, by rfl⟩ : syracuseStep 211985 = 158989) B158989
theorem B212003 : Blo 139791 212003 := bstep (se 1 (by rfl) ⟨159002, by rfl⟩ : syracuseStep 212003 = 318005) B318005
theorem B212033 : Blo 139791 212033 := bstep (se 2 (by rfl) ⟨79512, by rfl⟩ : syracuseStep 212033 = 159025) B159025
theorem B212051 : Blo 139791 212051 := bstep (se 1 (by rfl) ⟨159038, by rfl⟩ : syracuseStep 212051 = 318077) B318077
theorem B408685 : Blo 139791 408685 := bstep (se 3 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 408685 = 153257) B153257
theorem B212081 : Blo 139791 212081 := bstep (se 2 (by rfl) ⟨79530, by rfl⟩ : syracuseStep 212081 = 159061) B159061
theorem B212099 : Blo 139791 212099 := bstep (se 1 (by rfl) ⟨159074, by rfl⟩ : syracuseStep 212099 = 318149) B318149
theorem B212129 : Blo 139791 212129 := bstep (se 2 (by rfl) ⟨79548, by rfl⟩ : syracuseStep 212129 = 159097) B159097
theorem B212147 : Blo 139791 212147 := bstep (se 1 (by rfl) ⟨159110, by rfl⟩ : syracuseStep 212147 = 318221) B318221
theorem B605389 : Blo 139791 605389 := bstep (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) B227021
theorem B212177 : Blo 139791 212177 := bstep (se 2 (by rfl) ⟨79566, by rfl⟩ : syracuseStep 212177 = 159133) B159133
theorem B507107 : Blo 139791 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B212195 : Blo 139791 212195 := bstep (se 1 (by rfl) ⟨159146, by rfl⟩ : syracuseStep 212195 = 318293) B318293
theorem B212225 : Blo 139791 212225 := bstep (se 2 (by rfl) ⟨79584, by rfl⟩ : syracuseStep 212225 = 159169) B159169
theorem B802061 : Blo 139791 802061 := bstep (se 3 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 802061 = 300773) B300773
theorem B212243 : Blo 139791 212243 := bstep (se 1 (by rfl) ⟨159182, by rfl⟩ : syracuseStep 212243 = 318365) B318365
theorem B179491 : Blo 139791 179491 := bstep (se 1 (by rfl) ⟨134618, by rfl⟩ : syracuseStep 179491 = 269237) B269237
theorem B212273 : Blo 139791 212273 := bstep (se 2 (by rfl) ⟨79602, by rfl⟩ : syracuseStep 212273 = 159205) B159205
theorem B212291 : Blo 139791 212291 := bstep (se 1 (by rfl) ⟨159218, by rfl⟩ : syracuseStep 212291 = 318437) B318437
theorem B212321 : Blo 139791 212321 := bstep (se 2 (by rfl) ⟨79620, by rfl⟩ : syracuseStep 212321 = 159241) B159241
theorem B212339 : Blo 139791 212339 := bstep (se 1 (by rfl) ⟨159254, by rfl⟩ : syracuseStep 212339 = 318509) B318509
theorem B179587 : Blo 139791 179587 := bstep (se 1 (by rfl) ⟨134690, by rfl⟩ : syracuseStep 179587 = 269381) B269381
theorem B212369 : Blo 139791 212369 := bstep (se 2 (by rfl) ⟨79638, by rfl⟩ : syracuseStep 212369 = 159277) B159277
theorem B212387 : Blo 139791 212387 := bstep (se 1 (by rfl) ⟨159290, by rfl⟩ : syracuseStep 212387 = 318581) B318581
theorem B540067 : Blo 139791 540067 := bstep (se 1 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 540067 = 810101) B810101
theorem B212417 : Blo 139791 212417 := bstep (se 2 (by rfl) ⟨79656, by rfl⟩ : syracuseStep 212417 = 159313) B159313
theorem B5848517 : Blo 139791 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B212435 : Blo 139791 212435 := bstep (se 1 (by rfl) ⟨159326, by rfl⟩ : syracuseStep 212435 = 318653) B318653
theorem B474605 : Blo 139791 474605 := bstep (se 3 (by rfl) ⟨88988, by rfl⟩ : syracuseStep 474605 = 177977) B177977
theorem B212465 : Blo 139791 212465 := bstep (se 2 (by rfl) ⟨79674, by rfl⟩ : syracuseStep 212465 = 159349) B159349
theorem B212483 : Blo 139791 212483 := bstep (se 1 (by rfl) ⟨159362, by rfl⟩ : syracuseStep 212483 = 318725) B318725
theorem B212513 : Blo 139791 212513 := bstep (se 2 (by rfl) ⟨79692, by rfl⟩ : syracuseStep 212513 = 159385) B159385
theorem B474659 : Blo 139791 474659 := bstep (se 1 (by rfl) ⟨355994, by rfl⟩ : syracuseStep 474659 = 711989) B711989
theorem B605731 : Blo 139791 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B212531 : Blo 139791 212531 := bstep (se 1 (by rfl) ⟨159398, by rfl⟩ : syracuseStep 212531 = 318797) B318797
theorem B212561 : Blo 139791 212561 := bstep (se 2 (by rfl) ⟨79710, by rfl⟩ : syracuseStep 212561 = 159421) B159421
theorem B212579 : Blo 139791 212579 := bstep (se 1 (by rfl) ⟨159434, by rfl⟩ : syracuseStep 212579 = 318869) B318869
theorem B212609 : Blo 139791 212609 := bstep (se 2 (by rfl) ⟨79728, by rfl⟩ : syracuseStep 212609 = 159457) B159457
theorem B212627 : Blo 139791 212627 := bstep (se 1 (by rfl) ⟨159470, by rfl⟩ : syracuseStep 212627 = 318941) B318941
theorem B212657 : Blo 139791 212657 := bstep (se 2 (by rfl) ⟨79746, by rfl⟩ : syracuseStep 212657 = 159493) B159493
theorem B212675 : Blo 139791 212675 := bstep (se 1 (by rfl) ⟨159506, by rfl⟩ : syracuseStep 212675 = 319013) B319013
theorem B212705 : Blo 139791 212705 := bstep (se 2 (by rfl) ⟨79764, by rfl⟩ : syracuseStep 212705 = 159529) B159529
theorem B212723 : Blo 139791 212723 := bstep (se 1 (by rfl) ⟨159542, by rfl⟩ : syracuseStep 212723 = 319085) B319085
theorem B212753 : Blo 139791 212753 := bstep (se 2 (by rfl) ⟨79782, by rfl⟩ : syracuseStep 212753 = 159565) B159565
theorem B212771 : Blo 139791 212771 := bstep (se 1 (by rfl) ⟨159578, by rfl⟩ : syracuseStep 212771 = 319157) B319157
theorem B474929 : Blo 139791 474929 := bstep (se 2 (by rfl) ⟨178098, by rfl⟩ : syracuseStep 474929 = 356197) B356197
theorem B212801 : Blo 139791 212801 := bstep (se 2 (by rfl) ⟨79800, by rfl⟩ : syracuseStep 212801 = 159601) B159601
theorem B212819 : Blo 139791 212819 := bstep (se 1 (by rfl) ⟨159614, by rfl⟩ : syracuseStep 212819 = 319229) B319229
theorem B212849 : Blo 139791 212849 := bstep (se 2 (by rfl) ⟨79818, by rfl⟩ : syracuseStep 212849 = 159637) B159637
theorem B180083 : Blo 139791 180083 := bstep (se 1 (by rfl) ⟨135062, by rfl⟩ : syracuseStep 180083 = 270125) B270125
theorem B212867 : Blo 139791 212867 := bstep (se 1 (by rfl) ⟨159650, by rfl⟩ : syracuseStep 212867 = 319301) B319301
theorem B212897 : Blo 139791 212897 := bstep (se 2 (by rfl) ⟨79836, by rfl⟩ : syracuseStep 212897 = 159673) B159673
theorem B212915 : Blo 139791 212915 := bstep (se 1 (by rfl) ⟨159686, by rfl⟩ : syracuseStep 212915 = 319373) B319373
theorem B212945 : Blo 139791 212945 := bstep (se 2 (by rfl) ⟨79854, by rfl⟩ : syracuseStep 212945 = 159709) B159709
theorem B212963 : Blo 139791 212963 := bstep (se 1 (by rfl) ⟨159722, by rfl⟩ : syracuseStep 212963 = 319445) B319445
theorem B1458161 : Blo 139791 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B212993 : Blo 139791 212993 := bstep (se 2 (by rfl) ⟨79872, by rfl⟩ : syracuseStep 212993 = 159745) B159745
theorem B213011 : Blo 139791 213011 := bstep (se 1 (by rfl) ⟨159758, by rfl⟩ : syracuseStep 213011 = 319517) B319517
theorem B213025 : Blo 139791 213025 := bstep (se 2 (by rfl) ⟨79884, by rfl⟩ : syracuseStep 213025 = 159769) B159769
theorem B213041 : Blo 139791 213041 := bstep (se 2 (by rfl) ⟨79890, by rfl⟩ : syracuseStep 213041 = 159781) B159781
theorem B213059 : Blo 139791 213059 := bstep (se 1 (by rfl) ⟨159794, by rfl⟩ : syracuseStep 213059 = 319589) B319589
theorem B213089 : Blo 139791 213089 := bstep (se 2 (by rfl) ⟨79908, by rfl⟩ : syracuseStep 213089 = 159817) B159817
theorem B213107 : Blo 139791 213107 := bstep (se 1 (by rfl) ⟨159830, by rfl⟩ : syracuseStep 213107 = 319661) B319661
theorem B213137 : Blo 139791 213137 := bstep (se 2 (by rfl) ⟨79926, by rfl⟩ : syracuseStep 213137 = 159853) B159853
theorem B213155 : Blo 139791 213155 := bstep (se 1 (by rfl) ⟨159866, by rfl⟩ : syracuseStep 213155 = 319733) B319733
theorem B802993 : Blo 139791 802993 := bstep (se 2 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 802993 = 602245) B602245
theorem B213185 : Blo 139791 213185 := bstep (se 2 (by rfl) ⟨79944, by rfl⟩ : syracuseStep 213185 = 159889) B159889
theorem B213203 : Blo 139791 213203 := bstep (se 1 (by rfl) ⟨159902, by rfl⟩ : syracuseStep 213203 = 319805) B319805
theorem B409841 : Blo 139791 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B213233 : Blo 139791 213233 := bstep (se 2 (by rfl) ⟨79962, by rfl⟩ : syracuseStep 213233 = 159925) B159925
theorem B213251 : Blo 139791 213251 := bstep (se 1 (by rfl) ⟨159938, by rfl⟩ : syracuseStep 213251 = 319877) B319877
theorem B213281 : Blo 139791 213281 := bstep (se 2 (by rfl) ⟨79980, by rfl⟩ : syracuseStep 213281 = 159961) B159961
theorem B213299 : Blo 139791 213299 := bstep (se 1 (by rfl) ⟨159974, by rfl⟩ : syracuseStep 213299 = 319949) B319949
theorem B475469 : Blo 139791 475469 := bstep (se 3 (by rfl) ⟨89150, by rfl⟩ : syracuseStep 475469 = 178301) B178301
theorem B213329 : Blo 139791 213329 := bstep (se 2 (by rfl) ⟨79998, by rfl⟩ : syracuseStep 213329 = 159997) B159997
theorem B213347 : Blo 139791 213347 := bstep (se 1 (by rfl) ⟨160010, by rfl⟩ : syracuseStep 213347 = 320021) B320021
theorem B213377 : Blo 139791 213377 := bstep (se 2 (by rfl) ⟨80016, by rfl⟩ : syracuseStep 213377 = 160033) B160033
theorem B475523 : Blo 139791 475523 := bstep (se 1 (by rfl) ⟨356642, by rfl⟩ : syracuseStep 475523 = 713285) B713285
theorem B213395 : Blo 139791 213395 := bstep (se 1 (by rfl) ⟨160046, by rfl⟩ : syracuseStep 213395 = 320093) B320093
theorem B213425 : Blo 139791 213425 := bstep (se 2 (by rfl) ⟨80034, by rfl⟩ : syracuseStep 213425 = 160069) B160069
theorem B213443 : Blo 139791 213443 := bstep (se 1 (by rfl) ⟨160082, by rfl⟩ : syracuseStep 213443 = 320165) B320165
theorem B213473 : Blo 139791 213473 := bstep (se 2 (by rfl) ⟨80052, by rfl⟩ : syracuseStep 213473 = 160105) B160105
theorem B213491 : Blo 139791 213491 := bstep (se 1 (by rfl) ⟨160118, by rfl⟩ : syracuseStep 213491 = 320237) B320237
theorem B213521 : Blo 139791 213521 := bstep (se 2 (by rfl) ⟨80070, by rfl⟩ : syracuseStep 213521 = 160141) B160141
theorem B213539 : Blo 139791 213539 := bstep (se 1 (by rfl) ⟨160154, by rfl⟩ : syracuseStep 213539 = 320309) B320309
theorem B180787 : Blo 139791 180787 := bstep (se 1 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 180787 = 271181) B271181
theorem B213569 : Blo 139791 213569 := bstep (se 2 (by rfl) ⟨80088, by rfl⟩ : syracuseStep 213569 = 160177) B160177
theorem B213587 : Blo 139791 213587 := bstep (se 1 (by rfl) ⟨160190, by rfl⟩ : syracuseStep 213587 = 320381) B320381
theorem B344675 : Blo 139791 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B213617 : Blo 139791 213617 := bstep (se 2 (by rfl) ⟨80106, by rfl⟩ : syracuseStep 213617 = 160213) B160213
theorem B213635 : Blo 139791 213635 := bstep (se 1 (by rfl) ⟨160226, by rfl⟩ : syracuseStep 213635 = 320453) B320453
theorem B475793 : Blo 139791 475793 := bstep (se 2 (by rfl) ⟨178422, by rfl⟩ : syracuseStep 475793 = 356845) B356845
theorem B180883 : Blo 139791 180883 := bstep (se 1 (by rfl) ⟨135662, by rfl⟩ : syracuseStep 180883 = 271325) B271325
theorem B213665 : Blo 139791 213665 := bstep (se 2 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 213665 = 160249) B160249
theorem B213683 : Blo 139791 213683 := bstep (se 1 (by rfl) ⟨160262, by rfl⟩ : syracuseStep 213683 = 320525) B320525
theorem B967373 : Blo 139791 967373 := bstep (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) B362765
theorem B213713 : Blo 139791 213713 := bstep (se 2 (by rfl) ⟨80142, by rfl⟩ : syracuseStep 213713 = 160285) B160285
theorem B213731 : Blo 139791 213731 := bstep (se 1 (by rfl) ⟨160298, by rfl⟩ : syracuseStep 213731 = 320597) B320597
theorem B213761 : Blo 139791 213761 := bstep (se 2 (by rfl) ⟨80160, by rfl⟩ : syracuseStep 213761 = 160321) B160321
theorem B213779 : Blo 139791 213779 := bstep (se 1 (by rfl) ⟨160334, by rfl⟩ : syracuseStep 213779 = 320669) B320669
theorem B213809 : Blo 139791 213809 := bstep (se 2 (by rfl) ⟨80178, by rfl⟩ : syracuseStep 213809 = 160357) B160357
theorem B213827 : Blo 139791 213827 := bstep (se 1 (by rfl) ⟨160370, by rfl⟩ : syracuseStep 213827 = 320741) B320741
theorem B1065797 : Blo 139791 1065797 := bstep (se 4 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 1065797 = 199837) B199837
theorem B213857 : Blo 139791 213857 := bstep (se 2 (by rfl) ⟨80196, by rfl⟩ : syracuseStep 213857 = 160393) B160393
theorem B213875 : Blo 139791 213875 := bstep (se 1 (by rfl) ⟨160406, by rfl⟩ : syracuseStep 213875 = 320813) B320813
theorem B213905 : Blo 139791 213905 := bstep (se 2 (by rfl) ⟨80214, by rfl⟩ : syracuseStep 213905 = 160429) B160429
theorem B213923 : Blo 139791 213923 := bstep (se 1 (by rfl) ⟨160442, by rfl⟩ : syracuseStep 213923 = 320885) B320885
theorem B213953 : Blo 139791 213953 := bstep (se 2 (by rfl) ⟨80232, by rfl⟩ : syracuseStep 213953 = 160465) B160465
theorem B213971 : Blo 139791 213971 := bstep (se 1 (by rfl) ⟨160478, by rfl⟩ : syracuseStep 213971 = 320957) B320957
theorem B214001 : Blo 139791 214001 := bstep (se 2 (by rfl) ⟨80250, by rfl⟩ : syracuseStep 214001 = 160501) B160501
theorem B214019 : Blo 139791 214019 := bstep (se 1 (by rfl) ⟨160514, by rfl⟩ : syracuseStep 214019 = 321029) B321029
theorem B214049 : Blo 139791 214049 := bstep (se 2 (by rfl) ⟨80268, by rfl⟩ : syracuseStep 214049 = 160537) B160537
theorem B214067 : Blo 139791 214067 := bstep (se 1 (by rfl) ⟨160550, by rfl⟩ : syracuseStep 214067 = 321101) B321101
theorem B214097 : Blo 139791 214097 := bstep (se 2 (by rfl) ⟨80286, by rfl⟩ : syracuseStep 214097 = 160573) B160573
theorem B312419 : Blo 139791 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B214115 : Blo 139791 214115 := bstep (se 1 (by rfl) ⟨160586, by rfl⟩ : syracuseStep 214115 = 321173) B321173
theorem B214145 : Blo 139791 214145 := bstep (se 2 (by rfl) ⟨80304, by rfl⟩ : syracuseStep 214145 = 160609) B160609
theorem B181379 : Blo 139791 181379 := bstep (se 1 (by rfl) ⟨136034, by rfl⟩ : syracuseStep 181379 = 272069) B272069
theorem B214163 : Blo 139791 214163 := bstep (se 1 (by rfl) ⟨160622, by rfl⟩ : syracuseStep 214163 = 321245) B321245
theorem B476333 : Blo 139791 476333 := bstep (se 3 (by rfl) ⟨89312, by rfl⟩ : syracuseStep 476333 = 178625) B178625
theorem B214193 : Blo 139791 214193 := bstep (se 2 (by rfl) ⟨80322, by rfl⟩ : syracuseStep 214193 = 160645) B160645
theorem B214211 : Blo 139791 214211 := bstep (se 1 (by rfl) ⟨160658, by rfl⟩ : syracuseStep 214211 = 321317) B321317
theorem B3032261 : Blo 139791 3032261 := bstep (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) B568549
theorem B214241 : Blo 139791 214241 := bstep (se 2 (by rfl) ⟨80340, by rfl⟩ : syracuseStep 214241 = 160681) B160681
theorem B476387 : Blo 139791 476387 := bstep (se 1 (by rfl) ⟨357290, by rfl⟩ : syracuseStep 476387 = 714581) B714581
theorem B214259 : Blo 139791 214259 := bstep (se 1 (by rfl) ⟨160694, by rfl⟩ : syracuseStep 214259 = 321389) B321389
theorem B214289 : Blo 139791 214289 := bstep (se 2 (by rfl) ⟨80358, by rfl⟩ : syracuseStep 214289 = 160717) B160717
theorem B214307 : Blo 139791 214307 := bstep (se 1 (by rfl) ⟨160730, by rfl⟩ : syracuseStep 214307 = 321461) B321461
theorem B214321 : Blo 139791 214321 := bstep (se 2 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 214321 = 160741) B160741
theorem B214337 : Blo 139791 214337 := bstep (se 2 (by rfl) ⟨80376, by rfl⟩ : syracuseStep 214337 = 160753) B160753
theorem B214355 : Blo 139791 214355 := bstep (se 1 (by rfl) ⟨160766, by rfl⟩ : syracuseStep 214355 = 321533) B321533
theorem B214385 : Blo 139791 214385 := bstep (se 2 (by rfl) ⟨80394, by rfl⟩ : syracuseStep 214385 = 160789) B160789
theorem B214403 : Blo 139791 214403 := bstep (se 1 (by rfl) ⟨160802, by rfl⟩ : syracuseStep 214403 = 321605) B321605
theorem B214433 : Blo 139791 214433 := bstep (se 2 (by rfl) ⟨80412, by rfl⟩ : syracuseStep 214433 = 160825) B160825
theorem B214451 : Blo 139791 214451 := bstep (se 1 (by rfl) ⟨160838, by rfl⟩ : syracuseStep 214451 = 321677) B321677
theorem B3851717 : Blo 139791 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B1394117 : Blo 139791 1394117 := bstep (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) B261397
theorem B214481 : Blo 139791 214481 := bstep (se 2 (by rfl) ⟨80430, by rfl⟩ : syracuseStep 214481 = 160861) B160861
theorem B214499 : Blo 139791 214499 := bstep (se 1 (by rfl) ⟨160874, by rfl⟩ : syracuseStep 214499 = 321749) B321749
theorem B476657 : Blo 139791 476657 := bstep (se 2 (by rfl) ⟨178746, by rfl⟩ : syracuseStep 476657 = 357493) B357493
theorem B214529 : Blo 139791 214529 := bstep (se 2 (by rfl) ⟨80448, by rfl⟩ : syracuseStep 214529 = 160897) B160897
theorem B214547 : Blo 139791 214547 := bstep (se 1 (by rfl) ⟨160910, by rfl⟩ : syracuseStep 214547 = 321821) B321821
theorem B214577 : Blo 139791 214577 := bstep (se 2 (by rfl) ⟨80466, by rfl⟩ : syracuseStep 214577 = 160933) B160933
theorem B214595 : Blo 139791 214595 := bstep (se 1 (by rfl) ⟨160946, by rfl⟩ : syracuseStep 214595 = 321893) B321893
theorem B542285 : Blo 139791 542285 := bstep (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) B203357
theorem B214625 : Blo 139791 214625 := bstep (se 2 (by rfl) ⟨80484, by rfl⟩ : syracuseStep 214625 = 160969) B160969
theorem B804451 : Blo 139791 804451 := bstep (se 1 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 804451 = 1206677) B1206677
theorem B214643 : Blo 139791 214643 := bstep (se 1 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 214643 = 321965) B321965
theorem B214673 : Blo 139791 214673 := bstep (se 2 (by rfl) ⟨80502, by rfl⟩ : syracuseStep 214673 = 161005) B161005
theorem B214691 : Blo 139791 214691 := bstep (se 1 (by rfl) ⟨161018, by rfl⟩ : syracuseStep 214691 = 322037) B322037
theorem B214721 : Blo 139791 214721 := bstep (se 2 (by rfl) ⟨80520, by rfl⟩ : syracuseStep 214721 = 161041) B161041
theorem B214739 : Blo 139791 214739 := bstep (se 1 (by rfl) ⟨161054, by rfl⟩ : syracuseStep 214739 = 322109) B322109
theorem B214769 : Blo 139791 214769 := bstep (se 2 (by rfl) ⟨80538, by rfl⟩ : syracuseStep 214769 = 161077) B161077
theorem B214787 : Blo 139791 214787 := bstep (se 1 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 214787 = 322181) B322181
theorem B214817 : Blo 139791 214817 := bstep (se 2 (by rfl) ⟨80556, by rfl⟩ : syracuseStep 214817 = 161113) B161113
theorem B214835 : Blo 139791 214835 := bstep (se 1 (by rfl) ⟨161126, by rfl⟩ : syracuseStep 214835 = 322253) B322253
theorem B214865 : Blo 139791 214865 := bstep (se 2 (by rfl) ⟨80574, by rfl⟩ : syracuseStep 214865 = 161149) B161149
theorem B214883 : Blo 139791 214883 := bstep (se 1 (by rfl) ⟨161162, by rfl⟩ : syracuseStep 214883 = 322325) B322325
theorem B214913 : Blo 139791 214913 := bstep (se 2 (by rfl) ⟨80592, by rfl⟩ : syracuseStep 214913 = 161185) B161185
theorem B214931 : Blo 139791 214931 := bstep (se 1 (by rfl) ⟨161198, by rfl⟩ : syracuseStep 214931 = 322397) B322397
theorem B214961 : Blo 139791 214961 := bstep (se 2 (by rfl) ⟨80610, by rfl⟩ : syracuseStep 214961 = 161221) B161221
theorem B214979 : Blo 139791 214979 := bstep (se 1 (by rfl) ⟨161234, by rfl⟩ : syracuseStep 214979 = 322469) B322469
theorem B640973 : Blo 139791 640973 := bstep (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) B240365
theorem B215009 : Blo 139791 215009 := bstep (se 2 (by rfl) ⟨80628, by rfl⟩ : syracuseStep 215009 = 161257) B161257
theorem B215027 : Blo 139791 215027 := bstep (se 1 (by rfl) ⟨161270, by rfl⟩ : syracuseStep 215027 = 322541) B322541
theorem B477197 : Blo 139791 477197 := bstep (se 3 (by rfl) ⟨89474, by rfl⟩ : syracuseStep 477197 = 178949) B178949
theorem B215057 : Blo 139791 215057 := bstep (se 2 (by rfl) ⟨80646, by rfl⟩ : syracuseStep 215057 = 161293) B161293
theorem B215075 : Blo 139791 215075 := bstep (se 1 (by rfl) ⟨161306, by rfl⟩ : syracuseStep 215075 = 322613) B322613
theorem B215105 : Blo 139791 215105 := bstep (se 2 (by rfl) ⟨80664, by rfl⟩ : syracuseStep 215105 = 161329) B161329
theorem B477251 : Blo 139791 477251 := bstep (se 1 (by rfl) ⟨357938, by rfl⟩ : syracuseStep 477251 = 715877) B715877
theorem B215123 : Blo 139791 215123 := bstep (se 1 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 215123 = 322685) B322685
theorem B804977 : Blo 139791 804977 := bstep (se 2 (by rfl) ⟨301866, by rfl⟩ : syracuseStep 804977 = 603733) B603733
theorem B215153 : Blo 139791 215153 := bstep (se 2 (by rfl) ⟨80682, by rfl⟩ : syracuseStep 215153 = 161365) B161365
theorem B149635 : Blo 139791 149635 := bstep (se 1 (by rfl) ⟨112226, by rfl⟩ : syracuseStep 149635 = 224453) B224453
theorem B215171 : Blo 139791 215171 := bstep (se 1 (by rfl) ⟨161378, by rfl⟩ : syracuseStep 215171 = 322757) B322757
theorem B215201 : Blo 139791 215201 := bstep (se 2 (by rfl) ⟨80700, by rfl⟩ : syracuseStep 215201 = 161401) B161401
theorem B215219 : Blo 139791 215219 := bstep (se 1 (by rfl) ⟨161414, by rfl⟩ : syracuseStep 215219 = 322829) B322829
theorem B215249 : Blo 139791 215249 := bstep (se 2 (by rfl) ⟨80718, by rfl⟩ : syracuseStep 215249 = 161437) B161437
theorem B215267 : Blo 139791 215267 := bstep (se 1 (by rfl) ⟨161450, by rfl⟩ : syracuseStep 215267 = 322901) B322901
theorem B215297 : Blo 139791 215297 := bstep (se 2 (by rfl) ⟨80736, by rfl⟩ : syracuseStep 215297 = 161473) B161473
theorem B510221 : Blo 139791 510221 := bstep (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) B191333
theorem B215315 : Blo 139791 215315 := bstep (se 1 (by rfl) ⟨161486, by rfl⟩ : syracuseStep 215315 = 322973) B322973
theorem B903473 : Blo 139791 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B215345 : Blo 139791 215345 := bstep (se 2 (by rfl) ⟨80754, by rfl⟩ : syracuseStep 215345 = 161509) B161509
theorem B215363 : Blo 139791 215363 := bstep (se 1 (by rfl) ⟨161522, by rfl⟩ : syracuseStep 215363 = 323045) B323045
theorem B477521 : Blo 139791 477521 := bstep (se 2 (by rfl) ⟨179070, by rfl⟩ : syracuseStep 477521 = 358141) B358141
theorem B215393 : Blo 139791 215393 := bstep (se 2 (by rfl) ⟨80772, by rfl⟩ : syracuseStep 215393 = 161545) B161545
theorem B1821041 : Blo 139791 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B215411 : Blo 139791 215411 := bstep (se 1 (by rfl) ⟨161558, by rfl⟩ : syracuseStep 215411 = 323117) B323117
theorem B215441 : Blo 139791 215441 := bstep (se 2 (by rfl) ⟨80790, by rfl⟩ : syracuseStep 215441 = 161581) B161581
theorem B215459 : Blo 139791 215459 := bstep (se 1 (by rfl) ⟨161594, by rfl⟩ : syracuseStep 215459 = 323189) B323189
theorem B215489 : Blo 139791 215489 := bstep (se 2 (by rfl) ⟨80808, by rfl⟩ : syracuseStep 215489 = 161617) B161617
theorem B215507 : Blo 139791 215507 := bstep (se 1 (by rfl) ⟨161630, by rfl⟩ : syracuseStep 215507 = 323261) B323261
theorem B215537 : Blo 139791 215537 := bstep (se 2 (by rfl) ⟨80826, by rfl⟩ : syracuseStep 215537 = 161653) B161653
theorem B215555 : Blo 139791 215555 := bstep (se 1 (by rfl) ⟨161666, by rfl⟩ : syracuseStep 215555 = 323333) B323333
theorem B215585 : Blo 139791 215585 := bstep (se 2 (by rfl) ⟨80844, by rfl⟩ : syracuseStep 215585 = 161689) B161689
theorem B215603 : Blo 139791 215603 := bstep (se 1 (by rfl) ⟨161702, by rfl⟩ : syracuseStep 215603 = 323405) B323405
theorem B215633 : Blo 139791 215633 := bstep (se 2 (by rfl) ⟨80862, by rfl⟩ : syracuseStep 215633 = 161725) B161725
theorem B215651 : Blo 139791 215651 := bstep (se 1 (by rfl) ⟨161738, by rfl⟩ : syracuseStep 215651 = 323477) B323477
theorem B215681 : Blo 139791 215681 := bstep (se 2 (by rfl) ⟨80880, by rfl⟩ : syracuseStep 215681 = 161761) B161761
theorem B1395427 : Blo 139791 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B215795 : Blo 139791 215795 := bstep (se 1 (by rfl) ⟨161846, by rfl⟩ : syracuseStep 215795 = 323693) B323693
theorem B478061 : Blo 139791 478061 := bstep (se 3 (by rfl) ⟨89636, by rfl⟩ : syracuseStep 478061 = 179273) B179273
theorem B478115 : Blo 139791 478115 := bstep (se 1 (by rfl) ⟨358586, by rfl⟩ : syracuseStep 478115 = 717173) B717173
theorem B576497 : Blo 139791 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B314531 : Blo 139791 314531 := bstep (se 1 (by rfl) ⟨235898, by rfl⟩ : syracuseStep 314531 = 471797) B471797
theorem B478385 : Blo 139791 478385 := bstep (se 2 (by rfl) ⟨179394, by rfl⟩ : syracuseStep 478385 = 358789) B358789
theorem B150707 : Blo 139791 150707 := bstep (se 1 (by rfl) ⟨113030, by rfl⟩ : syracuseStep 150707 = 226061) B226061
theorem B707939 : Blo 139791 707939 := bstep (se 1 (by rfl) ⟨530954, by rfl⟩ : syracuseStep 707939 = 1061909) B1061909
theorem B347537 : Blo 139791 347537 := bstep (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) B260653
theorem B314801 : Blo 139791 314801 := bstep (se 2 (by rfl) ⟨118050, by rfl⟩ : syracuseStep 314801 = 236101) B236101
theorem B314819 : Blo 139791 314819 := bstep (se 1 (by rfl) ⟨236114, by rfl⟩ : syracuseStep 314819 = 472229) B472229
theorem B609763 : Blo 139791 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B806435 : Blo 139791 806435 := bstep (se 1 (by rfl) ⟨604826, by rfl⟩ : syracuseStep 806435 = 1209653) B1209653
theorem B1625669 : Blo 139791 1625669 := bstep (se 4 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 1625669 = 304813) B304813
theorem B478925 : Blo 139791 478925 := bstep (se 3 (by rfl) ⟨89798, by rfl⟩ : syracuseStep 478925 = 179597) B179597
theorem B315089 : Blo 139791 315089 := bstep (se 2 (by rfl) ⟨118158, by rfl⟩ : syracuseStep 315089 = 236317) B236317
theorem B315107 : Blo 139791 315107 := bstep (se 1 (by rfl) ⟨236330, by rfl⟩ : syracuseStep 315107 = 472661) B472661
theorem B1199843 : Blo 139791 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B478979 : Blo 139791 478979 := bstep (se 1 (by rfl) ⟨359234, by rfl⟩ : syracuseStep 478979 = 718469) B718469
theorem B315377 : Blo 139791 315377 := bstep (se 2 (by rfl) ⟨118266, by rfl⟩ : syracuseStep 315377 = 236533) B236533
theorem B315395 : Blo 139791 315395 := bstep (se 1 (by rfl) ⟨236546, by rfl⟩ : syracuseStep 315395 = 473093) B473093
theorem B479249 : Blo 139791 479249 := bstep (se 2 (by rfl) ⟨179718, by rfl⟩ : syracuseStep 479249 = 359437) B359437
theorem B708749 : Blo 139791 708749 := bstep (se 3 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 708749 = 265781) B265781
theorem B315665 : Blo 139791 315665 := bstep (se 2 (by rfl) ⟨118374, by rfl⟩ : syracuseStep 315665 = 236749) B236749
theorem B315683 : Blo 139791 315683 := bstep (se 1 (by rfl) ⟨236762, by rfl⟩ : syracuseStep 315683 = 473525) B473525
theorem B151843 : Blo 139791 151843 := bstep (se 1 (by rfl) ⟨113882, by rfl⟩ : syracuseStep 151843 = 227765) B227765
theorem B610673 : Blo 139791 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B545201 : Blo 139791 545201 := bstep (se 2 (by rfl) ⟨204450, by rfl⟩ : syracuseStep 545201 = 408901) B408901
theorem B479789 : Blo 139791 479789 := bstep (se 3 (by rfl) ⟨89960, by rfl⟩ : syracuseStep 479789 = 179921) B179921
theorem B315953 : Blo 139791 315953 := bstep (se 2 (by rfl) ⟨118482, by rfl⟩ : syracuseStep 315953 = 236965) B236965
theorem B315971 : Blo 139791 315971 := bstep (se 1 (by rfl) ⟨236978, by rfl⟩ : syracuseStep 315971 = 473957) B473957
theorem B479825 : Blo 139791 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B676451 : Blo 139791 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B479843 : Blo 139791 479843 := bstep (se 1 (by rfl) ⟨359882, by rfl⟩ : syracuseStep 479843 = 719765) B719765
theorem B512675 : Blo 139791 512675 := bstep (se 1 (by rfl) ⟨384506, by rfl⟩ : syracuseStep 512675 = 769013) B769013
theorem B610993 : Blo 139791 610993 := bstep (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) B458245
theorem B1168141 : Blo 139791 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B1528645 : Blo 139791 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B316241 : Blo 139791 316241 := bstep (se 2 (by rfl) ⟨118590, by rfl⟩ : syracuseStep 316241 = 237181) B237181
theorem B316259 : Blo 139791 316259 := bstep (se 1 (by rfl) ⟨237194, by rfl⟩ : syracuseStep 316259 = 474389) B474389
theorem B480113 : Blo 139791 480113 := bstep (se 2 (by rfl) ⟨180042, by rfl⟩ : syracuseStep 480113 = 360085) B360085
theorem B316529 : Blo 139791 316529 := bstep (se 2 (by rfl) ⟨118698, by rfl⟩ : syracuseStep 316529 = 237397) B237397
theorem B316547 : Blo 139791 316547 := bstep (se 1 (by rfl) ⟨237410, by rfl⟩ : syracuseStep 316547 = 474821) B474821
theorem B152723 : Blo 139791 152723 := bstep (se 1 (by rfl) ⟨114542, by rfl⟩ : syracuseStep 152723 = 229085) B229085
theorem B677105 : Blo 139791 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B152851 : Blo 139791 152851 := bstep (se 1 (by rfl) ⟨114638, by rfl⟩ : syracuseStep 152851 = 229277) B229277
theorem B578929 : Blo 139791 578929 := bstep (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) B434197
theorem B808325 : Blo 139791 808325 := bstep (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) B151561
theorem B480653 : Blo 139791 480653 := bstep (se 3 (by rfl) ⟨90122, by rfl⟩ : syracuseStep 480653 = 180245) B180245
theorem B316817 : Blo 139791 316817 := bstep (se 2 (by rfl) ⟨118806, by rfl⟩ : syracuseStep 316817 = 237613) B237613
theorem B316835 : Blo 139791 316835 := bstep (se 1 (by rfl) ⟨237626, by rfl⟩ : syracuseStep 316835 = 475253) B475253
theorem B480707 : Blo 139791 480707 := bstep (se 1 (by rfl) ⟨360530, by rfl⟩ : syracuseStep 480707 = 721061) B721061
theorem B317105 : Blo 139791 317105 := bstep (se 2 (by rfl) ⟨118914, by rfl⟩ : syracuseStep 317105 = 237829) B237829
theorem B317123 : Blo 139791 317123 := bstep (se 1 (by rfl) ⟨237842, by rfl⟩ : syracuseStep 317123 = 475685) B475685
theorem B480977 : Blo 139791 480977 := bstep (se 2 (by rfl) ⟨180366, by rfl⟩ : syracuseStep 480977 = 360733) B360733
theorem B513827 : Blo 139791 513827 := bstep (se 1 (by rfl) ⟨385370, by rfl⟩ : syracuseStep 513827 = 770741) B770741
theorem B448301 : Blo 139791 448301 := bstep (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) B168113
theorem B284593 : Blo 139791 284593 := bstep (se 2 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 284593 = 213445) B213445
theorem B317393 : Blo 139791 317393 := bstep (se 2 (by rfl) ⟨119022, by rfl⟩ : syracuseStep 317393 = 238045) B238045
theorem B317411 : Blo 139791 317411 := bstep (se 1 (by rfl) ⟨238058, by rfl⟩ : syracuseStep 317411 = 476117) B476117
theorem B907469 : Blo 139791 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B481517 : Blo 139791 481517 := bstep (se 3 (by rfl) ⟨90284, by rfl⟩ : syracuseStep 481517 = 180569) B180569
theorem B317681 : Blo 139791 317681 := bstep (se 2 (by rfl) ⟨119130, by rfl⟩ : syracuseStep 317681 = 238261) B238261
theorem B252163 : Blo 139791 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B317699 : Blo 139791 317699 := bstep (se 1 (by rfl) ⟨238274, by rfl⟩ : syracuseStep 317699 = 476549) B476549
theorem B481571 : Blo 139791 481571 := bstep (se 1 (by rfl) ⟨361178, by rfl⟩ : syracuseStep 481571 = 722357) B722357
theorem B252337 : Blo 139791 252337 := bstep (se 2 (by rfl) ⟨94626, by rfl⟩ : syracuseStep 252337 = 189253) B189253
theorem B1071629 : Blo 139791 1071629 := bstep (se 3 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 1071629 = 401861) B401861
theorem B317969 : Blo 139791 317969 := bstep (se 2 (by rfl) ⟨119238, by rfl⟩ : syracuseStep 317969 = 238477) B238477
theorem B317987 : Blo 139791 317987 := bstep (se 1 (by rfl) ⟨238490, by rfl⟩ : syracuseStep 317987 = 476981) B476981
theorem B678449 : Blo 139791 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B481841 : Blo 139791 481841 := bstep (se 2 (by rfl) ⟨180690, by rfl⟩ : syracuseStep 481841 = 361381) B361381
theorem B186931 : Blo 139791 186931 := bstep (se 1 (by rfl) ⟨140198, by rfl⟩ : syracuseStep 186931 = 280397) B280397
theorem B2939533 : Blo 139791 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B318257 : Blo 139791 318257 := bstep (se 2 (by rfl) ⟨119346, by rfl⟩ : syracuseStep 318257 = 238693) B238693
theorem B318275 : Blo 139791 318275 := bstep (se 1 (by rfl) ⟨238706, by rfl⟩ : syracuseStep 318275 = 477413) B477413
theorem B711665 : Blo 139791 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B482381 : Blo 139791 482381 := bstep (se 3 (by rfl) ⟨90446, by rfl⟩ : syracuseStep 482381 = 180893) B180893
theorem B318545 : Blo 139791 318545 := bstep (se 2 (by rfl) ⟨119454, by rfl⟩ : syracuseStep 318545 = 238909) B238909
theorem B318563 : Blo 139791 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B482435 : Blo 139791 482435 := bstep (se 1 (by rfl) ⟨361826, by rfl⟩ : syracuseStep 482435 = 723653) B723653
theorem B875717 : Blo 139791 875717 := bstep (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) B164197
theorem B580877 : Blo 139791 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B220483 : Blo 139791 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B253265 : Blo 139791 253265 := bstep (se 2 (by rfl) ⟨94974, by rfl⟩ : syracuseStep 253265 = 189949) B189949
theorem B318833 : Blo 139791 318833 := bstep (se 2 (by rfl) ⟨119562, by rfl⟩ : syracuseStep 318833 = 239125) B239125
theorem B318851 : Blo 139791 318851 := bstep (se 1 (by rfl) ⟨239138, by rfl⟩ : syracuseStep 318851 = 478277) B478277
theorem B482705 : Blo 139791 482705 := bstep (se 2 (by rfl) ⟨181014, by rfl⟩ : syracuseStep 482705 = 362029) B362029
theorem B679373 : Blo 139791 679373 := bstep (se 3 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 679373 = 254765) B254765
theorem B679565 : Blo 139791 679565 := bstep (se 3 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 679565 = 254837) B254837
theorem B319121 : Blo 139791 319121 := bstep (se 2 (by rfl) ⟨119670, by rfl⟩ : syracuseStep 319121 = 239341) B239341
theorem B319139 : Blo 139791 319139 := bstep (se 1 (by rfl) ⟨239354, by rfl⟩ : syracuseStep 319139 = 478709) B478709
theorem B483245 : Blo 139791 483245 := bstep (se 3 (by rfl) ⟨90608, by rfl⟩ : syracuseStep 483245 = 181217) B181217
theorem B450481 : Blo 139791 450481 := bstep (se 2 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 450481 = 337861) B337861
theorem B319409 : Blo 139791 319409 := bstep (se 2 (by rfl) ⟨119778, by rfl⟩ : syracuseStep 319409 = 239557) B239557
theorem B319427 : Blo 139791 319427 := bstep (se 1 (by rfl) ⟨239570, by rfl⟩ : syracuseStep 319427 = 479141) B479141
theorem B483299 : Blo 139791 483299 := bstep (se 1 (by rfl) ⟨362474, by rfl⟩ : syracuseStep 483299 = 724949) B724949
theorem B450659 : Blo 139791 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B385165 : Blo 139791 385165 := bstep (se 3 (by rfl) ⟨72218, by rfl⟩ : syracuseStep 385165 = 144437) B144437
theorem B319697 : Blo 139791 319697 := bstep (se 2 (by rfl) ⟨119886, by rfl⟩ : syracuseStep 319697 = 239773) B239773
theorem B319715 : Blo 139791 319715 := bstep (se 1 (by rfl) ⟨239786, by rfl⟩ : syracuseStep 319715 = 479573) B479573
theorem B483569 : Blo 139791 483569 := bstep (se 2 (by rfl) ⟨181338, by rfl⟩ : syracuseStep 483569 = 362677) B362677
theorem B516365 : Blo 139791 516365 := bstep (se 3 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 516365 = 193637) B193637
theorem B286993 : Blo 139791 286993 := bstep (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) B215245
theorem B909701 : Blo 139791 909701 := bstep (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) B170569
theorem B713123 : Blo 139791 713123 := bstep (se 1 (by rfl) ⟨534842, by rfl⟩ : syracuseStep 713123 = 1069685) B1069685
theorem B1532357 : Blo 139791 1532357 := bstep (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) B287317
theorem B319985 : Blo 139791 319985 := bstep (se 2 (by rfl) ⟨119994, by rfl⟩ : syracuseStep 319985 = 239989) B239989
theorem B320003 : Blo 139791 320003 := bstep (se 1 (by rfl) ⟨240002, by rfl⟩ : syracuseStep 320003 = 480005) B480005
theorem B484109 : Blo 139791 484109 := bstep (se 3 (by rfl) ⟨90770, by rfl⟩ : syracuseStep 484109 = 181541) B181541
theorem B320273 : Blo 139791 320273 := bstep (se 2 (by rfl) ⟨120102, by rfl⟩ : syracuseStep 320273 = 240205) B240205
theorem B320291 : Blo 139791 320291 := bstep (se 1 (by rfl) ⟨240218, by rfl⟩ : syracuseStep 320291 = 480437) B480437
theorem B484163 : Blo 139791 484163 := bstep (se 1 (by rfl) ⟨363122, by rfl⟩ : syracuseStep 484163 = 726245) B726245
theorem B648013 : Blo 139791 648013 := bstep (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) B243005
theorem B1991537 : Blo 139791 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B386083 : Blo 139791 386083 := bstep (se 1 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 386083 = 579125) B579125
theorem B255025 : Blo 139791 255025 := bstep (se 2 (by rfl) ⟨95634, by rfl⟩ : syracuseStep 255025 = 191269) B191269
theorem B320561 : Blo 139791 320561 := bstep (se 2 (by rfl) ⟨120210, by rfl⟩ : syracuseStep 320561 = 240421) B240421
theorem B320579 : Blo 139791 320579 := bstep (se 1 (by rfl) ⟨240434, by rfl⟩ : syracuseStep 320579 = 480869) B480869
theorem B484433 : Blo 139791 484433 := bstep (se 2 (by rfl) ⟨181662, by rfl⟩ : syracuseStep 484433 = 363325) B363325
theorem B713933 : Blo 139791 713933 := bstep (se 3 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 713933 = 267725) B267725
theorem B1631501 : Blo 139791 1631501 := bstep (se 3 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 1631501 = 611813) B611813
theorem B320849 : Blo 139791 320849 := bstep (se 2 (by rfl) ⟨120318, by rfl⟩ : syracuseStep 320849 = 240637) B240637
theorem B320867 : Blo 139791 320867 := bstep (se 1 (by rfl) ⟨240650, by rfl⟩ : syracuseStep 320867 = 481301) B481301
theorem B1369457 : Blo 139791 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1074545 : Blo 139791 1074545 := bstep (se 2 (by rfl) ⟨402954, by rfl⟩ : syracuseStep 1074545 = 805909) B805909
theorem B484973 : Blo 139791 484973 := bstep (se 3 (by rfl) ⟨90932, by rfl⟩ : syracuseStep 484973 = 181865) B181865
theorem B321137 : Blo 139791 321137 := bstep (se 2 (by rfl) ⟨120426, by rfl⟩ : syracuseStep 321137 = 240853) B240853
theorem B157315 : Blo 139791 157315 := bstep (se 1 (by rfl) ⟨117986, by rfl⟩ : syracuseStep 157315 = 235973) B235973
theorem B321155 : Blo 139791 321155 := bstep (se 1 (by rfl) ⟨240866, by rfl⟩ : syracuseStep 321155 = 481733) B481733
theorem B485027 : Blo 139791 485027 := bstep (se 1 (by rfl) ⟨363770, by rfl⟩ : syracuseStep 485027 = 727541) B727541
theorem B157459 : Blo 139791 157459 := bstep (se 1 (by rfl) ⟨118094, by rfl⟩ : syracuseStep 157459 = 236189) B236189
theorem B452429 : Blo 139791 452429 := bstep (se 3 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 452429 = 169661) B169661
theorem B321425 : Blo 139791 321425 := bstep (se 2 (by rfl) ⟨120534, by rfl⟩ : syracuseStep 321425 = 241069) B241069
theorem B157603 : Blo 139791 157603 := bstep (se 1 (by rfl) ⟨118202, by rfl⟩ : syracuseStep 157603 = 236405) B236405
theorem B321443 : Blo 139791 321443 := bstep (se 1 (by rfl) ⟨241082, by rfl⟩ : syracuseStep 321443 = 482165) B482165
theorem B485297 : Blo 139791 485297 := bstep (se 2 (by rfl) ⟨181986, by rfl⟩ : syracuseStep 485297 = 363973) B363973
theorem B288785 : Blo 139791 288785 := bstep (se 2 (by rfl) ⟨108294, by rfl⟩ : syracuseStep 288785 = 216589) B216589
theorem B518179 : Blo 139791 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B157747 : Blo 139791 157747 := bstep (se 1 (by rfl) ⟨118310, by rfl⟩ : syracuseStep 157747 = 236621) B236621
theorem B288881 : Blo 139791 288881 := bstep (se 2 (by rfl) ⟨108330, by rfl⟩ : syracuseStep 288881 = 216661) B216661
theorem B485507 : Blo 139791 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B944261 : Blo 139791 944261 := bstep (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) B177049
theorem B321713 : Blo 139791 321713 := bstep (se 2 (by rfl) ⟨120642, by rfl⟩ : syracuseStep 321713 = 241285) B241285
theorem B157891 : Blo 139791 157891 := bstep (se 1 (by rfl) ⟨118418, by rfl⟩ : syracuseStep 157891 = 236837) B236837
theorem B321731 : Blo 139791 321731 := bstep (se 1 (by rfl) ⟨241298, by rfl⟩ : syracuseStep 321731 = 482597) B482597
theorem B354577 : Blo 139791 354577 := bstep (se 2 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 354577 = 265933) B265933
theorem B158035 : Blo 139791 158035 := bstep (se 1 (by rfl) ⟨118526, by rfl⟩ : syracuseStep 158035 = 237053) B237053
theorem B322001 : Blo 139791 322001 := bstep (se 2 (by rfl) ⟨120750, by rfl⟩ : syracuseStep 322001 = 241501) B241501
theorem B158179 : Blo 139791 158179 := bstep (se 1 (by rfl) ⟨118634, by rfl⟩ : syracuseStep 158179 = 237269) B237269
theorem B1993187 : Blo 139791 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B322019 : Blo 139791 322019 := bstep (se 1 (by rfl) ⟨241514, by rfl⟩ : syracuseStep 322019 = 483029) B483029
theorem B387587 : Blo 139791 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B813581 : Blo 139791 813581 := bstep (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) B305093
theorem B354851 : Blo 139791 354851 := bstep (se 1 (by rfl) ⟨266138, by rfl⟩ : syracuseStep 354851 = 532277) B532277
theorem B158323 : Blo 139791 158323 := bstep (se 1 (by rfl) ⟨118742, by rfl⟩ : syracuseStep 158323 = 237485) B237485
theorem B355043 : Blo 139791 355043 := bstep (se 1 (by rfl) ⟨266282, by rfl⟩ : syracuseStep 355043 = 532565) B532565
theorem B191203 : Blo 139791 191203 := bstep (se 1 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 191203 = 286805) B286805
theorem B322289 : Blo 139791 322289 := bstep (se 2 (by rfl) ⟨120858, by rfl⟩ : syracuseStep 322289 = 241717) B241717
theorem B158467 : Blo 139791 158467 := bstep (se 1 (by rfl) ⟨118850, by rfl⟩ : syracuseStep 158467 = 237701) B237701
theorem B322307 : Blo 139791 322307 := bstep (se 1 (by rfl) ⟨241730, by rfl⟩ : syracuseStep 322307 = 483461) B483461
theorem B158611 : Blo 139791 158611 := bstep (se 1 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 158611 = 237917) B237917
theorem B322577 : Blo 139791 322577 := bstep (se 2 (by rfl) ⟨120966, by rfl⟩ : syracuseStep 322577 = 241933) B241933
theorem B158755 : Blo 139791 158755 := bstep (se 1 (by rfl) ⟨119066, by rfl⟩ : syracuseStep 158755 = 238133) B238133
theorem B322595 : Blo 139791 322595 := bstep (se 1 (by rfl) ⟨241946, by rfl⟩ : syracuseStep 322595 = 483893) B483893
theorem B814157 : Blo 139791 814157 := bstep (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) B305309
theorem B158899 : Blo 139791 158899 := bstep (se 1 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 158899 = 238349) B238349
theorem B3665173 : Blo 139791 3665173 := bstep (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) B171805
theorem B224561 : Blo 139791 224561 := bstep (se 2 (by rfl) ⟨84210, by rfl⟩ : syracuseStep 224561 = 168421) B168421
theorem B322865 : Blo 139791 322865 := bstep (se 2 (by rfl) ⟨121074, by rfl⟩ : syracuseStep 322865 = 242149) B242149
theorem B159043 : Blo 139791 159043 := bstep (se 1 (by rfl) ⟨119282, by rfl⟩ : syracuseStep 159043 = 238565) B238565
theorem B322883 : Blo 139791 322883 := bstep (se 1 (by rfl) ⟨242162, by rfl⟩ : syracuseStep 322883 = 484325) B484325
theorem B224689 : Blo 139791 224689 := bstep (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) B168517
theorem B159187 : Blo 139791 159187 := bstep (se 1 (by rfl) ⟨119390, by rfl⟩ : syracuseStep 159187 = 238781) B238781
theorem B323153 : Blo 139791 323153 := bstep (se 2 (by rfl) ⟨121182, by rfl⟩ : syracuseStep 323153 = 242365) B242365
theorem B159331 : Blo 139791 159331 := bstep (se 1 (by rfl) ⟨119498, by rfl⟩ : syracuseStep 159331 = 238997) B238997
theorem B323171 : Blo 139791 323171 := bstep (se 1 (by rfl) ⟨242378, by rfl⟩ : syracuseStep 323171 = 484757) B484757
theorem B355985 : Blo 139791 355985 := bstep (se 2 (by rfl) ⟨133494, by rfl⟩ : syracuseStep 355985 = 266989) B266989
theorem B257699 : Blo 139791 257699 := bstep (se 1 (by rfl) ⟨193274, by rfl⟩ : syracuseStep 257699 = 386549) B386549
theorem B356035 : Blo 139791 356035 := bstep (se 1 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 356035 = 534053) B534053
theorem B2289379 : Blo 139791 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B159475 : Blo 139791 159475 := bstep (se 1 (by rfl) ⟨119606, by rfl⟩ : syracuseStep 159475 = 239213) B239213
theorem B356177 : Blo 139791 356177 := bstep (se 2 (by rfl) ⟨133566, by rfl⟩ : syracuseStep 356177 = 267133) B267133
theorem B323441 : Blo 139791 323441 := bstep (se 2 (by rfl) ⟨121290, by rfl⟩ : syracuseStep 323441 = 242581) B242581
theorem B159619 : Blo 139791 159619 := bstep (se 1 (by rfl) ⟨119714, by rfl⟩ : syracuseStep 159619 = 239429) B239429
theorem B323459 : Blo 139791 323459 := bstep (se 1 (by rfl) ⟨242594, by rfl⟩ : syracuseStep 323459 = 485189) B485189
theorem B159763 : Blo 139791 159763 := bstep (se 1 (by rfl) ⟨119822, by rfl⟩ : syracuseStep 159763 = 239645) B239645
theorem B716849 : Blo 139791 716849 := bstep (se 2 (by rfl) ⟨268818, by rfl⟩ : syracuseStep 716849 = 537637) B537637
theorem B1634417 : Blo 139791 1634417 := bstep (se 2 (by rfl) ⟨612906, by rfl⟩ : syracuseStep 1634417 = 1225813) B1225813
theorem B159907 : Blo 139791 159907 := bstep (se 1 (by rfl) ⟨119930, by rfl⟩ : syracuseStep 159907 = 239861) B239861
theorem B323843 : Blo 139791 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B160051 : Blo 139791 160051 := bstep (se 1 (by rfl) ⟨120038, by rfl⟩ : syracuseStep 160051 = 240077) B240077
theorem B2453813 : Blo 139791 2453813 := bstep (se 5 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 2453813 = 230045) B230045
theorem B225683 : Blo 139791 225683 := bstep (se 1 (by rfl) ⟨169262, by rfl⟩ : syracuseStep 225683 = 338525) B338525
theorem B160195 : Blo 139791 160195 := bstep (se 1 (by rfl) ⟨120146, by rfl⟩ : syracuseStep 160195 = 240293) B240293
theorem B291281 : Blo 139791 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B160339 : Blo 139791 160339 := bstep (se 1 (by rfl) ⟨120254, by rfl⟩ : syracuseStep 160339 = 240509) B240509
theorem B488035 : Blo 139791 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B160483 : Blo 139791 160483 := bstep (se 1 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 160483 = 240725) B240725
theorem B357169 : Blo 139791 357169 := bstep (se 2 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 357169 = 267877) B267877
theorem B160627 : Blo 139791 160627 := bstep (se 1 (by rfl) ⟨120470, by rfl⟩ : syracuseStep 160627 = 240941) B240941
theorem B160771 : Blo 139791 160771 := bstep (se 1 (by rfl) ⟨120578, by rfl⟩ : syracuseStep 160771 = 241157) B241157
theorem B357443 : Blo 139791 357443 := bstep (se 1 (by rfl) ⟨268082, by rfl⟩ : syracuseStep 357443 = 536165) B536165
theorem B160915 : Blo 139791 160915 := bstep (se 1 (by rfl) ⟨120686, by rfl⟩ : syracuseStep 160915 = 241373) B241373
theorem B357635 : Blo 139791 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B455939 : Blo 139791 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B816389 : Blo 139791 816389 := bstep (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) B153073
theorem B161059 : Blo 139791 161059 := bstep (se 1 (by rfl) ⟨120794, by rfl⟩ : syracuseStep 161059 = 241589) B241589
theorem B161203 : Blo 139791 161203 := bstep (se 1 (by rfl) ⟨120902, by rfl⟩ : syracuseStep 161203 = 241805) B241805
theorem B587213 : Blo 139791 587213 := bstep (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) B220205
theorem B718307 : Blo 139791 718307 := bstep (se 1 (by rfl) ⟨538730, by rfl⟩ : syracuseStep 718307 = 1077461) B1077461
theorem B161347 : Blo 139791 161347 := bstep (se 1 (by rfl) ⟨121010, by rfl⟩ : syracuseStep 161347 = 242021) B242021
theorem B1734257 : Blo 139791 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B161411 : Blo 139791 161411 := bstep (se 1 (by rfl) ⟨121058, by rfl⟩ : syracuseStep 161411 = 242117) B242117
theorem B161491 : Blo 139791 161491 := bstep (se 1 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 161491 = 242237) B242237
theorem B685837 : Blo 139791 685837 := bstep (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) B257189
theorem B227137 : Blo 139791 227137 := bstep (se 2 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 227137 = 170353) B170353
theorem B456529 : Blo 139791 456529 := bstep (se 2 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 456529 = 342397) B342397
theorem B161635 : Blo 139791 161635 := bstep (se 1 (by rfl) ⟨121226, by rfl⟩ : syracuseStep 161635 = 242453) B242453
theorem B718733 : Blo 139791 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B817073 : Blo 139791 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B915569 : Blo 139791 915569 := bstep (se 2 (by rfl) ⟨343338, by rfl⟩ : syracuseStep 915569 = 686677) B686677
theorem B1734797 : Blo 139791 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B358577 : Blo 139791 358577 := bstep (se 2 (by rfl) ⟨134466, by rfl⟩ : syracuseStep 358577 = 268933) B268933
theorem B1308869 : Blo 139791 1308869 := bstep (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) B245413
theorem B358627 : Blo 139791 358627 := bstep (se 1 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 358627 = 537941) B537941
theorem B719117 : Blo 139791 719117 := bstep (se 3 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 719117 = 269669) B269669
theorem B358769 : Blo 139791 358769 := bstep (se 2 (by rfl) ⟨134538, by rfl⟩ : syracuseStep 358769 = 269077) B269077
theorem B1571185 : Blo 139791 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B227827 : Blo 139791 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B162419 : Blo 139791 162419 := bstep (se 1 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 162419 = 243629) B243629
theorem B195283 : Blo 139791 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B490225 : Blo 139791 490225 := bstep (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) B367669
theorem B260995 : Blo 139791 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B621553 : Blo 139791 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B425197 : Blo 139791 425197 := bstep (se 3 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 425197 = 159449) B159449
theorem B359761 : Blo 139791 359761 := bstep (se 2 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 359761 = 269821) B269821
theorem B228691 : Blo 139791 228691 := bstep (se 1 (by rfl) ⟨171518, by rfl⟩ : syracuseStep 228691 = 343037) B343037
theorem B818531 : Blo 139791 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B228739 : Blo 139791 228739 := bstep (se 1 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 228739 = 343109) B343109
theorem B491021 : Blo 139791 491021 := bstep (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) B184133
theorem B1867333 : Blo 139791 1867333 := bstep (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) B350125
theorem B360035 : Blo 139791 360035 := bstep (se 1 (by rfl) ⟨270026, by rfl⟩ : syracuseStep 360035 = 540053) B540053
theorem B228995 : Blo 139791 228995 := bstep (se 1 (by rfl) ⟨171746, by rfl⟩ : syracuseStep 228995 = 343493) B343493
theorem B655075 : Blo 139791 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B360227 : Blo 139791 360227 := bstep (se 1 (by rfl) ⟨270170, by rfl⟩ : syracuseStep 360227 = 540341) B540341
theorem B229187 : Blo 139791 229187 := bstep (se 1 (by rfl) ⟨171890, by rfl⟩ : syracuseStep 229187 = 343781) B343781
theorem B327523 : Blo 139791 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B1081349 : Blo 139791 1081349 := bstep (se 4 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 1081349 = 202753) B202753
theorem B1049219 : Blo 139791 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B721709 : Blo 139791 721709 := bstep (se 3 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 721709 = 270641) B270641
theorem B361523 : Blo 139791 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B427315 : Blo 139791 427315 := bstep (se 1 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 427315 = 640973) B640973
theorem B361817 : Blo 139791 361817 := bstep (se 2 (by rfl) ⟨135681, by rfl⟩ : syracuseStep 361817 = 271363) B271363
theorem B1344869 : Blo 139791 1344869 := bstep (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) B252163
theorem B361921 : Blo 139791 361921 := bstep (se 2 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 361921 = 271441) B271441
theorem B1214027 : Blo 139791 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B919133 : Blo 139791 919133 := bstep (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) B344675
theorem B1083779 : Blo 139791 1083779 := bstep (se 1 (by rfl) ⟨812834, by rfl⟩ : syracuseStep 1083779 = 1625669) B1625669
theorem B690905 : Blo 139791 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B461591 : Blo 139791 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B199513 : Blo 139791 199513 := bstep (se 2 (by rfl) ⟨74817, by rfl⟩ : syracuseStep 199513 = 149635) B149635
theorem B363467 : Blo 139791 363467 := bstep (se 1 (by rfl) ⟨272600, by rfl⟩ : syracuseStep 363467 = 545201) B545201
theorem B265459 : Blo 139791 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B265675 : Blo 139791 265675 := bstep (se 1 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 265675 = 398513) B398513
theorem B265751 : Blo 139791 265751 := bstep (se 1 (by rfl) ⟨199313, by rfl⟩ : syracuseStep 265751 = 398627) B398627
theorem B200407 : Blo 139791 200407 := bstep (se 1 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 200407 = 300611) B300611
theorem B266419 : Blo 139791 266419 := bstep (se 1 (by rfl) ⟨199814, by rfl⟩ : syracuseStep 266419 = 399629) B399629
theorem B200971 : Blo 139791 200971 := bstep (se 1 (by rfl) ⟨150728, by rfl⟩ : syracuseStep 200971 = 301457) B301457
theorem B4624685 : Blo 139791 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B430429 : Blo 139791 430429 := bstep (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) B161411
theorem B4886897 : Blo 139791 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B266647 : Blo 139791 266647 := bstep (se 1 (by rfl) ⟨199985, by rfl⟩ : syracuseStep 266647 = 399971) B399971
theorem B463283 : Blo 139791 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B266753 : Blo 139791 266753 := bstep (se 2 (by rfl) ⟨100032, by rfl⟩ : syracuseStep 266753 = 200065) B200065
theorem B299585 : Blo 139791 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B725597 : Blo 139791 725597 := bstep (se 3 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 725597 = 272099) B272099
theorem B266905 : Blo 139791 266905 := bstep (se 2 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 266905 = 200179) B200179
theorem B398297 : Blo 139791 398297 := bstep (se 2 (by rfl) ⟨149361, by rfl⟩ : syracuseStep 398297 = 298723) B298723
theorem B3052505 : Blo 139791 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B300439 : Blo 139791 300439 := bstep (se 1 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 300439 = 450659) B450659
theorem B1021571 : Blo 139791 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B1087181 : Blo 139791 1087181 := bstep (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) B407693
theorem B202457 : Blo 139791 202457 := bstep (se 2 (by rfl) ⟨75921, by rfl⟩ : syracuseStep 202457 = 151843) B151843
theorem B268211 : Blo 139791 268211 := bstep (se 1 (by rfl) ⟨201158, by rfl⟩ : syracuseStep 268211 = 402317) B402317
theorem B268363 : Blo 139791 268363 := bstep (se 1 (by rfl) ⟨201272, by rfl⟩ : syracuseStep 268363 = 402545) B402545
theorem B1087667 : Blo 139791 1087667 := bstep (se 1 (by rfl) ⟨815750, by rfl⟩ : syracuseStep 1087667 = 1631501) B1631501
theorem B203095 : Blo 139791 203095 := bstep (se 1 (by rfl) ⟨152321, by rfl⟩ : syracuseStep 203095 = 304643) B304643
theorem B530819 : Blo 139791 530819 := bstep (se 1 (by rfl) ⟨398114, by rfl⟩ : syracuseStep 530819 = 796229) B796229
theorem B530833 : Blo 139791 530833 := bstep (se 2 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 530833 = 398125) B398125
theorem B268697 : Blo 139791 268697 := bstep (se 2 (by rfl) ⟨100761, by rfl⟩ : syracuseStep 268697 = 201523) B201523
theorem B2038193 : Blo 139791 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B235993 : Blo 139791 235993 := bstep (se 2 (by rfl) ⟨88497, by rfl⟩ : syracuseStep 235993 = 176995) B176995
theorem B301619 : Blo 139791 301619 := bstep (se 1 (by rfl) ⟨226214, by rfl⟩ : syracuseStep 301619 = 452429) B452429
theorem B399937 : Blo 139791 399937 := bstep (se 2 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 399937 = 299953) B299953
theorem B727703 : Blo 139791 727703 := bstep (se 1 (by rfl) ⟨545777, by rfl⟩ : syracuseStep 727703 = 1091555) B1091555
theorem B531137 : Blo 139791 531137 := bstep (se 2 (by rfl) ⟨199176, by rfl⟩ : syracuseStep 531137 = 398353) B398353
theorem B629507 : Blo 139791 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B2235235 : Blo 139791 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B433117 : Blo 139791 433117 := bstep (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) B162419
theorem B236567 : Blo 139791 236567 := bstep (se 1 (by rfl) ⟨177425, by rfl⟩ : syracuseStep 236567 = 354851) B354851
theorem B269335 : Blo 139791 269335 := bstep (se 1 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 269335 = 404003) B404003
theorem B203801 : Blo 139791 203801 := bstep (se 2 (by rfl) ⟨76425, by rfl⟩ : syracuseStep 203801 = 152851) B152851
theorem B203915 : Blo 139791 203915 := bstep (se 1 (by rfl) ⟨152936, by rfl⟩ : syracuseStep 203915 = 305873) B305873
theorem B236695 : Blo 139791 236695 := bstep (se 1 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 236695 = 355043) B355043
theorem B2202805 : Blo 139791 2202805 := bstep (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) B206513
theorem B531805 : Blo 139791 531805 := bstep (se 3 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 531805 = 199427) B199427
theorem B1089125 : Blo 139791 1089125 := bstep (se 4 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 1089125 = 204211) B204211
theorem B269963 : Blo 139791 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B204439 : Blo 139791 204439 := bstep (se 1 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 204439 = 306659) B306659
theorem B302849 : Blo 139791 302849 := bstep (se 2 (by rfl) ⟨113568, by rfl⟩ : syracuseStep 302849 = 227137) B227137
theorem B237323 : Blo 139791 237323 := bstep (se 1 (by rfl) ⟨177992, by rfl⟩ : syracuseStep 237323 = 355985) B355985
theorem B270155 : Blo 139791 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B270209 : Blo 139791 270209 := bstep (se 2 (by rfl) ⟨101328, by rfl⟩ : syracuseStep 270209 = 202657) B202657
theorem B237451 : Blo 139791 237451 := bstep (se 1 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 237451 = 356177) B356177
theorem B1023961 : Blo 139791 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B237593 : Blo 139791 237593 := bstep (se 2 (by rfl) ⟨89097, by rfl⟩ : syracuseStep 237593 = 178195) B178195
theorem B1089611 : Blo 139791 1089611 := bstep (se 1 (by rfl) ⟨817208, by rfl⟩ : syracuseStep 1089611 = 1634417) B1634417
theorem B270425 : Blo 139791 270425 := bstep (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) B202819
theorem B237721 : Blo 139791 237721 := bstep (se 2 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 237721 = 178291) B178291
theorem B401611 : Blo 139791 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B401885 : Blo 139791 401885 := bstep (se 3 (by rfl) ⟨75353, by rfl⟩ : syracuseStep 401885 = 150707) B150707
theorem B139799 : Blo 139791 139799 := bstep (se 1 (by rfl) ⟨104849, by rfl⟩ : syracuseStep 139799 = 209699) B209699
theorem B139819 : Blo 139791 139819 := bstep (se 1 (by rfl) ⟨104864, by rfl⟩ : syracuseStep 139819 = 209729) B209729
theorem B139831 : Blo 139791 139831 := bstep (se 1 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 139831 = 209747) B209747
theorem B336449 : Blo 139791 336449 := bstep (se 2 (by rfl) ⟨126168, by rfl⟩ : syracuseStep 336449 = 252337) B252337
theorem B139851 : Blo 139791 139851 := bstep (se 1 (by rfl) ⟨104888, by rfl⟩ : syracuseStep 139851 = 209777) B209777
theorem B139863 : Blo 139791 139863 := bstep (se 1 (by rfl) ⟨104897, by rfl⟩ : syracuseStep 139863 = 209795) B209795
theorem B533081 : Blo 139791 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B1352285 : Blo 139791 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B139883 : Blo 139791 139883 := bstep (se 1 (by rfl) ⟨104912, by rfl⟩ : syracuseStep 139883 = 209825) B209825
theorem B139895 : Blo 139791 139895 := bstep (se 1 (by rfl) ⟨104921, by rfl⟩ : syracuseStep 139895 = 209843) B209843
theorem B139915 : Blo 139791 139915 := bstep (se 1 (by rfl) ⟨104936, by rfl⟩ : syracuseStep 139915 = 209873) B209873
theorem B139927 : Blo 139791 139927 := bstep (se 1 (by rfl) ⟨104945, by rfl⟩ : syracuseStep 139927 = 209891) B209891
theorem B303769 : Blo 139791 303769 := bstep (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) B227827
theorem B139947 : Blo 139791 139947 := bstep (se 1 (by rfl) ⟨104960, by rfl⟩ : syracuseStep 139947 = 209921) B209921
theorem B139959 : Blo 139791 139959 := bstep (se 1 (by rfl) ⟨104969, by rfl⟩ : syracuseStep 139959 = 209939) B209939
theorem B139979 : Blo 139791 139979 := bstep (se 1 (by rfl) ⟨104984, by rfl⟩ : syracuseStep 139979 = 209969) B209969
theorem B139991 : Blo 139791 139991 := bstep (se 1 (by rfl) ⟨104993, by rfl⟩ : syracuseStep 139991 = 209987) B209987
theorem B238295 : Blo 139791 238295 := bstep (se 1 (by rfl) ⟨178721, by rfl⟩ : syracuseStep 238295 = 357443) B357443
theorem B140011 : Blo 139791 140011 := bstep (se 1 (by rfl) ⟨105008, by rfl⟩ : syracuseStep 140011 = 210017) B210017
theorem B140023 : Blo 139791 140023 := bstep (se 1 (by rfl) ⟨105017, by rfl⟩ : syracuseStep 140023 = 210035) B210035
theorem B140043 : Blo 139791 140043 := bstep (se 1 (by rfl) ⟨105032, by rfl⟩ : syracuseStep 140043 = 210065) B210065
theorem B140055 : Blo 139791 140055 := bstep (se 1 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 140055 = 210083) B210083
theorem B271127 : Blo 139791 271127 := bstep (se 1 (by rfl) ⟨203345, by rfl⟩ : syracuseStep 271127 = 406691) B406691
theorem B140075 : Blo 139791 140075 := bstep (se 1 (by rfl) ⟨105056, by rfl⟩ : syracuseStep 140075 = 210113) B210113
theorem B140087 : Blo 139791 140087 := bstep (se 1 (by rfl) ⟨105065, by rfl⟩ : syracuseStep 140087 = 210131) B210131
theorem B140107 : Blo 139791 140107 := bstep (se 1 (by rfl) ⟨105080, by rfl⟩ : syracuseStep 140107 = 210161) B210161
theorem B140119 : Blo 139791 140119 := bstep (se 1 (by rfl) ⟨105089, by rfl⟩ : syracuseStep 140119 = 210179) B210179
theorem B238423 : Blo 139791 238423 := bstep (se 1 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 238423 = 357635) B357635
theorem B303959 : Blo 139791 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B140139 : Blo 139791 140139 := bstep (se 1 (by rfl) ⟨105104, by rfl⟩ : syracuseStep 140139 = 210209) B210209
theorem B140151 : Blo 139791 140151 := bstep (se 1 (by rfl) ⟨105113, by rfl⟩ : syracuseStep 140151 = 210227) B210227
theorem B140171 : Blo 139791 140171 := bstep (se 1 (by rfl) ⟨105128, by rfl⟩ : syracuseStep 140171 = 210257) B210257
theorem B140183 : Blo 139791 140183 := bstep (se 1 (by rfl) ⟨105137, by rfl⟩ : syracuseStep 140183 = 210275) B210275
theorem B140203 : Blo 139791 140203 := bstep (se 1 (by rfl) ⟨105152, by rfl⟩ : syracuseStep 140203 = 210305) B210305
theorem B140215 : Blo 139791 140215 := bstep (se 1 (by rfl) ⟨105161, by rfl⟩ : syracuseStep 140215 = 210323) B210323
theorem B140235 : Blo 139791 140235 := bstep (se 1 (by rfl) ⟨105176, by rfl⟩ : syracuseStep 140235 = 210353) B210353
theorem B140247 : Blo 139791 140247 := bstep (se 1 (by rfl) ⟨105185, by rfl⟩ : syracuseStep 140247 = 210371) B210371
theorem B140267 : Blo 139791 140267 := bstep (se 1 (by rfl) ⟨105200, by rfl⟩ : syracuseStep 140267 = 210401) B210401
theorem B140279 : Blo 139791 140279 := bstep (se 1 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 140279 = 210419) B210419
theorem B140299 : Blo 139791 140299 := bstep (se 1 (by rfl) ⟨105224, by rfl⟩ : syracuseStep 140299 = 210449) B210449
theorem B140311 : Blo 139791 140311 := bstep (se 1 (by rfl) ⟨105233, by rfl⟩ : syracuseStep 140311 = 210467) B210467
theorem B140331 : Blo 139791 140331 := bstep (se 1 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 140331 = 210497) B210497
theorem B926765 : Blo 139791 926765 := bstep (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) B347537
theorem B140343 : Blo 139791 140343 := bstep (se 1 (by rfl) ⟨105257, by rfl⟩ : syracuseStep 140343 = 210515) B210515
theorem B140363 : Blo 139791 140363 := bstep (se 1 (by rfl) ⟨105272, by rfl⟩ : syracuseStep 140363 = 210545) B210545
theorem B140375 : Blo 139791 140375 := bstep (se 1 (by rfl) ⟨105281, by rfl⟩ : syracuseStep 140375 = 210563) B210563
theorem B140395 : Blo 139791 140395 := bstep (se 1 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 140395 = 210593) B210593
theorem B140407 : Blo 139791 140407 := bstep (se 1 (by rfl) ⟨105305, by rfl⟩ : syracuseStep 140407 = 210611) B210611
theorem B140427 : Blo 139791 140427 := bstep (se 1 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 140427 = 210641) B210641
theorem B140439 : Blo 139791 140439 := bstep (se 1 (by rfl) ⟨105329, by rfl⟩ : syracuseStep 140439 = 210659) B210659
theorem B140459 : Blo 139791 140459 := bstep (se 1 (by rfl) ⟨105344, by rfl⟩ : syracuseStep 140459 = 210689) B210689
theorem B140471 : Blo 139791 140471 := bstep (se 1 (by rfl) ⟨105353, by rfl⟩ : syracuseStep 140471 = 210707) B210707
theorem B140491 : Blo 139791 140491 := bstep (se 1 (by rfl) ⟨105368, by rfl⟩ : syracuseStep 140491 = 210737) B210737
theorem B1156301 : Blo 139791 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B140503 : Blo 139791 140503 := bstep (se 1 (by rfl) ⟨105377, by rfl⟩ : syracuseStep 140503 = 210755) B210755
theorem B140523 : Blo 139791 140523 := bstep (se 1 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 140523 = 210785) B210785
theorem B140535 : Blo 139791 140535 := bstep (se 1 (by rfl) ⟨105401, by rfl⟩ : syracuseStep 140535 = 210803) B210803
theorem B140555 : Blo 139791 140555 := bstep (se 1 (by rfl) ⟨105416, by rfl⟩ : syracuseStep 140555 = 210833) B210833
theorem B140567 : Blo 139791 140567 := bstep (se 1 (by rfl) ⟨105425, by rfl⟩ : syracuseStep 140567 = 210851) B210851
theorem B140587 : Blo 139791 140587 := bstep (se 1 (by rfl) ⟨105440, by rfl⟩ : syracuseStep 140587 = 210881) B210881
theorem B271667 : Blo 139791 271667 := bstep (se 1 (by rfl) ⟨203750, by rfl⟩ : syracuseStep 271667 = 407501) B407501
theorem B140599 : Blo 139791 140599 := bstep (se 1 (by rfl) ⟨105449, by rfl⟩ : syracuseStep 140599 = 210899) B210899
theorem B828737 : Blo 139791 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B140619 : Blo 139791 140619 := bstep (se 1 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 140619 = 210929) B210929
theorem B140631 : Blo 139791 140631 := bstep (se 1 (by rfl) ⟨105473, by rfl⟩ : syracuseStep 140631 = 210947) B210947
theorem B140651 : Blo 139791 140651 := bstep (se 1 (by rfl) ⟨105488, by rfl⟩ : syracuseStep 140651 = 210977) B210977
theorem B140663 : Blo 139791 140663 := bstep (se 1 (by rfl) ⟨105497, by rfl⟩ : syracuseStep 140663 = 210995) B210995
theorem B140683 : Blo 139791 140683 := bstep (se 1 (by rfl) ⟨105512, by rfl⟩ : syracuseStep 140683 = 211025) B211025
theorem B140695 : Blo 139791 140695 := bstep (se 1 (by rfl) ⟨105521, by rfl⟩ : syracuseStep 140695 = 211043) B211043
theorem B140715 : Blo 139791 140715 := bstep (se 1 (by rfl) ⟨105536, by rfl⟩ : syracuseStep 140715 = 211073) B211073
theorem B1156531 : Blo 139791 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B140727 : Blo 139791 140727 := bstep (se 1 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 140727 = 211091) B211091
theorem B140747 : Blo 139791 140747 := bstep (se 1 (by rfl) ⟨105560, by rfl⟩ : syracuseStep 140747 = 211121) B211121
theorem B239051 : Blo 139791 239051 := bstep (se 1 (by rfl) ⟨179288, by rfl⟩ : syracuseStep 239051 = 358577) B358577
theorem B140759 : Blo 139791 140759 := bstep (se 1 (by rfl) ⟨105569, by rfl⟩ : syracuseStep 140759 = 211139) B211139
theorem B140779 : Blo 139791 140779 := bstep (se 1 (by rfl) ⟨105584, by rfl⟩ : syracuseStep 140779 = 211169) B211169
theorem B140791 : Blo 139791 140791 := bstep (se 1 (by rfl) ⟨105593, by rfl⟩ : syracuseStep 140791 = 211187) B211187
theorem B140811 : Blo 139791 140811 := bstep (se 1 (by rfl) ⟨105608, by rfl⟩ : syracuseStep 140811 = 211217) B211217
theorem B140823 : Blo 139791 140823 := bstep (se 1 (by rfl) ⟨105617, by rfl⟩ : syracuseStep 140823 = 211235) B211235
theorem B140843 : Blo 139791 140843 := bstep (se 1 (by rfl) ⟨105632, by rfl⟩ : syracuseStep 140843 = 211265) B211265
theorem B140855 : Blo 139791 140855 := bstep (se 1 (by rfl) ⟨105641, by rfl⟩ : syracuseStep 140855 = 211283) B211283
theorem B140875 : Blo 139791 140875 := bstep (se 1 (by rfl) ⟨105656, by rfl⟩ : syracuseStep 140875 = 211313) B211313
theorem B239179 : Blo 139791 239179 := bstep (se 1 (by rfl) ⟨179384, by rfl⟩ : syracuseStep 239179 = 358769) B358769
theorem B140887 : Blo 139791 140887 := bstep (se 1 (by rfl) ⟨105665, by rfl⟩ : syracuseStep 140887 = 211331) B211331
theorem B140907 : Blo 139791 140907 := bstep (se 1 (by rfl) ⟨105680, by rfl⟩ : syracuseStep 140907 = 211361) B211361
theorem B140919 : Blo 139791 140919 := bstep (se 1 (by rfl) ⟨105689, by rfl⟩ : syracuseStep 140919 = 211379) B211379
theorem B599683 : Blo 139791 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B140939 : Blo 139791 140939 := bstep (se 1 (by rfl) ⟨105704, by rfl⟩ : syracuseStep 140939 = 211409) B211409
theorem B566929 : Blo 139791 566929 := bstep (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) B425197
theorem B140951 : Blo 139791 140951 := bstep (se 1 (by rfl) ⟨105713, by rfl⟩ : syracuseStep 140951 = 211427) B211427
theorem B140971 : Blo 139791 140971 := bstep (se 1 (by rfl) ⟨105728, by rfl⟩ : syracuseStep 140971 = 211457) B211457
theorem B140983 : Blo 139791 140983 := bstep (se 1 (by rfl) ⟨105737, by rfl⟩ : syracuseStep 140983 = 211475) B211475
theorem B141003 : Blo 139791 141003 := bstep (se 1 (by rfl) ⟨105752, by rfl⟩ : syracuseStep 141003 = 211505) B211505
theorem B141015 : Blo 139791 141015 := bstep (se 1 (by rfl) ⟨105761, by rfl⟩ : syracuseStep 141015 = 211523) B211523
theorem B239321 : Blo 139791 239321 := bstep (se 2 (by rfl) ⟨89745, by rfl⟩ : syracuseStep 239321 = 179491) B179491
theorem B141035 : Blo 139791 141035 := bstep (se 1 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 141035 = 211553) B211553
theorem B141047 : Blo 139791 141047 := bstep (se 1 (by rfl) ⟨105785, by rfl⟩ : syracuseStep 141047 = 211571) B211571
theorem B141067 : Blo 139791 141067 := bstep (se 1 (by rfl) ⟨105800, by rfl⟩ : syracuseStep 141067 = 211601) B211601
theorem B141079 : Blo 139791 141079 := bstep (se 1 (by rfl) ⟨105809, by rfl⟩ : syracuseStep 141079 = 211619) B211619
theorem B304921 : Blo 139791 304921 := bstep (se 2 (by rfl) ⟨114345, by rfl⟩ : syracuseStep 304921 = 228691) B228691
theorem B272153 : Blo 139791 272153 := bstep (se 2 (by rfl) ⟨102057, by rfl⟩ : syracuseStep 272153 = 204115) B204115
theorem B141099 : Blo 139791 141099 := bstep (se 1 (by rfl) ⟨105824, by rfl⟩ : syracuseStep 141099 = 211649) B211649
theorem B141111 : Blo 139791 141111 := bstep (se 1 (by rfl) ⟨105833, by rfl⟩ : syracuseStep 141111 = 211667) B211667
theorem B141131 : Blo 139791 141131 := bstep (se 1 (by rfl) ⟨105848, by rfl⟩ : syracuseStep 141131 = 211697) B211697
theorem B141143 : Blo 139791 141143 := bstep (se 1 (by rfl) ⟨105857, by rfl⟩ : syracuseStep 141143 = 211715) B211715
theorem B239449 : Blo 139791 239449 := bstep (se 2 (by rfl) ⟨89793, by rfl⟩ : syracuseStep 239449 = 179587) B179587
theorem B304985 : Blo 139791 304985 := bstep (se 2 (by rfl) ⟨114369, by rfl⟩ : syracuseStep 304985 = 228739) B228739
theorem B141163 : Blo 139791 141163 := bstep (se 1 (by rfl) ⟨105872, by rfl⟩ : syracuseStep 141163 = 211745) B211745
theorem B141175 : Blo 139791 141175 := bstep (se 1 (by rfl) ⟨105881, by rfl⟩ : syracuseStep 141175 = 211763) B211763
theorem B141195 : Blo 139791 141195 := bstep (se 1 (by rfl) ⟨105896, by rfl⟩ : syracuseStep 141195 = 211793) B211793
theorem B141207 : Blo 139791 141207 := bstep (se 1 (by rfl) ⟨105905, by rfl⟩ : syracuseStep 141207 = 211811) B211811
theorem B141227 : Blo 139791 141227 := bstep (se 1 (by rfl) ⟨105920, by rfl⟩ : syracuseStep 141227 = 211841) B211841
theorem B141239 : Blo 139791 141239 := bstep (se 1 (by rfl) ⟨105929, by rfl⟩ : syracuseStep 141239 = 211859) B211859
theorem B141259 : Blo 139791 141259 := bstep (se 1 (by rfl) ⟨105944, by rfl⟩ : syracuseStep 141259 = 211889) B211889
theorem B141271 : Blo 139791 141271 := bstep (se 1 (by rfl) ⟨105953, by rfl⟩ : syracuseStep 141271 = 211907) B211907
theorem B141291 : Blo 139791 141291 := bstep (se 1 (by rfl) ⟨105968, by rfl⟩ : syracuseStep 141291 = 211937) B211937
theorem B141303 : Blo 139791 141303 := bstep (se 1 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 141303 = 211955) B211955
theorem B141323 : Blo 139791 141323 := bstep (se 1 (by rfl) ⟨105992, by rfl⟩ : syracuseStep 141323 = 211985) B211985
theorem B141335 : Blo 139791 141335 := bstep (se 1 (by rfl) ⟨106001, by rfl⟩ : syracuseStep 141335 = 212003) B212003
theorem B141355 : Blo 139791 141355 := bstep (se 1 (by rfl) ⟨106016, by rfl⟩ : syracuseStep 141355 = 212033) B212033
theorem B141367 : Blo 139791 141367 := bstep (se 1 (by rfl) ⟨106025, by rfl⟩ : syracuseStep 141367 = 212051) B212051
theorem B141387 : Blo 139791 141387 := bstep (se 1 (by rfl) ⟨106040, by rfl⟩ : syracuseStep 141387 = 212081) B212081
theorem B141399 : Blo 139791 141399 := bstep (se 1 (by rfl) ⟨106049, by rfl⟩ : syracuseStep 141399 = 212099) B212099
theorem B141419 : Blo 139791 141419 := bstep (se 1 (by rfl) ⟨106064, by rfl⟩ : syracuseStep 141419 = 212129) B212129
theorem B141431 : Blo 139791 141431 := bstep (se 1 (by rfl) ⟨106073, by rfl⟩ : syracuseStep 141431 = 212147) B212147
theorem B141451 : Blo 139791 141451 := bstep (se 1 (by rfl) ⟨106088, by rfl⟩ : syracuseStep 141451 = 212177) B212177
theorem B141463 : Blo 139791 141463 := bstep (se 1 (by rfl) ⟨106097, by rfl⟩ : syracuseStep 141463 = 212195) B212195
theorem B141483 : Blo 139791 141483 := bstep (se 1 (by rfl) ⟨106112, by rfl⟩ : syracuseStep 141483 = 212225) B212225
theorem B534707 : Blo 139791 534707 := bstep (se 1 (by rfl) ⟨401030, by rfl⟩ : syracuseStep 534707 = 802061) B802061
theorem B141495 : Blo 139791 141495 := bstep (se 1 (by rfl) ⟨106121, by rfl⟩ : syracuseStep 141495 = 212243) B212243
theorem B534721 : Blo 139791 534721 := bstep (se 2 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 534721 = 401041) B401041
theorem B141515 : Blo 139791 141515 := bstep (se 1 (by rfl) ⟨106136, by rfl⟩ : syracuseStep 141515 = 212273) B212273
theorem B141527 : Blo 139791 141527 := bstep (se 1 (by rfl) ⟨106145, by rfl⟩ : syracuseStep 141527 = 212291) B212291
theorem B141547 : Blo 139791 141547 := bstep (se 1 (by rfl) ⟨106160, by rfl⟩ : syracuseStep 141547 = 212321) B212321
theorem B141559 : Blo 139791 141559 := bstep (se 1 (by rfl) ⟨106169, by rfl⟩ : syracuseStep 141559 = 212339) B212339
theorem B141579 : Blo 139791 141579 := bstep (se 1 (by rfl) ⟨106184, by rfl⟩ : syracuseStep 141579 = 212369) B212369
theorem B141591 : Blo 139791 141591 := bstep (se 1 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 141591 = 212387) B212387
theorem B141611 : Blo 139791 141611 := bstep (se 1 (by rfl) ⟨106208, by rfl⟩ : syracuseStep 141611 = 212417) B212417
theorem B141623 : Blo 139791 141623 := bstep (se 1 (by rfl) ⟨106217, by rfl⟩ : syracuseStep 141623 = 212435) B212435
theorem B141643 : Blo 139791 141643 := bstep (se 1 (by rfl) ⟨106232, by rfl⟩ : syracuseStep 141643 = 212465) B212465
theorem B141655 : Blo 139791 141655 := bstep (se 1 (by rfl) ⟨106241, by rfl⟩ : syracuseStep 141655 = 212483) B212483
theorem B141675 : Blo 139791 141675 := bstep (se 1 (by rfl) ⟨106256, by rfl⟩ : syracuseStep 141675 = 212513) B212513
theorem B141687 : Blo 139791 141687 := bstep (se 1 (by rfl) ⟨106265, by rfl⟩ : syracuseStep 141687 = 212531) B212531
theorem B141707 : Blo 139791 141707 := bstep (se 1 (by rfl) ⟨106280, by rfl⟩ : syracuseStep 141707 = 212561) B212561
theorem B141719 : Blo 139791 141719 := bstep (se 1 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 141719 = 212579) B212579
theorem B240023 : Blo 139791 240023 := bstep (se 1 (by rfl) ⟨180017, by rfl⟩ : syracuseStep 240023 = 360035) B360035
theorem B141739 : Blo 139791 141739 := bstep (se 1 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 141739 = 212609) B212609
theorem B141751 : Blo 139791 141751 := bstep (se 1 (by rfl) ⟨106313, by rfl⟩ : syracuseStep 141751 = 212627) B212627
theorem B141771 : Blo 139791 141771 := bstep (se 1 (by rfl) ⟨106328, by rfl⟩ : syracuseStep 141771 = 212657) B212657
theorem B141783 : Blo 139791 141783 := bstep (se 1 (by rfl) ⟨106337, by rfl⟩ : syracuseStep 141783 = 212675) B212675
theorem B436697 : Blo 139791 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B272857 : Blo 139791 272857 := bstep (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) B204643
theorem B141803 : Blo 139791 141803 := bstep (se 1 (by rfl) ⟨106352, by rfl⟩ : syracuseStep 141803 = 212705) B212705
theorem B141815 : Blo 139791 141815 := bstep (se 1 (by rfl) ⟨106361, by rfl⟩ : syracuseStep 141815 = 212723) B212723
theorem B141835 : Blo 139791 141835 := bstep (se 1 (by rfl) ⟨106376, by rfl⟩ : syracuseStep 141835 = 212753) B212753
theorem B141847 : Blo 139791 141847 := bstep (se 1 (by rfl) ⟨106385, by rfl⟩ : syracuseStep 141847 = 212771) B212771
theorem B240151 : Blo 139791 240151 := bstep (se 1 (by rfl) ⟨180113, by rfl⟩ : syracuseStep 240151 = 360227) B360227
theorem B141867 : Blo 139791 141867 := bstep (se 1 (by rfl) ⟨106400, by rfl⟩ : syracuseStep 141867 = 212801) B212801
theorem B141879 : Blo 139791 141879 := bstep (se 1 (by rfl) ⟨106409, by rfl⟩ : syracuseStep 141879 = 212819) B212819
theorem B600641 : Blo 139791 600641 := bstep (se 2 (by rfl) ⟨225240, by rfl⟩ : syracuseStep 600641 = 450481) B450481
theorem B141899 : Blo 139791 141899 := bstep (se 1 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 141899 = 212849) B212849
theorem B141911 : Blo 139791 141911 := bstep (se 1 (by rfl) ⟨106433, by rfl⟩ : syracuseStep 141911 = 212867) B212867
theorem B141931 : Blo 139791 141931 := bstep (se 1 (by rfl) ⟨106448, by rfl⟩ : syracuseStep 141931 = 212897) B212897
theorem B141943 : Blo 139791 141943 := bstep (se 1 (by rfl) ⟨106457, by rfl⟩ : syracuseStep 141943 = 212915) B212915
theorem B141963 : Blo 139791 141963 := bstep (se 1 (by rfl) ⟨106472, by rfl⟩ : syracuseStep 141963 = 212945) B212945
theorem B141975 : Blo 139791 141975 := bstep (se 1 (by rfl) ⟨106481, by rfl⟩ : syracuseStep 141975 = 212963) B212963
theorem B141995 : Blo 139791 141995 := bstep (se 1 (by rfl) ⟨106496, by rfl⟩ : syracuseStep 141995 = 212993) B212993
theorem B142007 : Blo 139791 142007 := bstep (se 1 (by rfl) ⟨106505, by rfl⟩ : syracuseStep 142007 = 213011) B213011
theorem B142027 : Blo 139791 142027 := bstep (se 1 (by rfl) ⟨106520, by rfl⟩ : syracuseStep 142027 = 213041) B213041
theorem B142039 : Blo 139791 142039 := bstep (se 1 (by rfl) ⟨106529, by rfl⟩ : syracuseStep 142039 = 213059) B213059
theorem B404185 : Blo 139791 404185 := bstep (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) B303139
theorem B142059 : Blo 139791 142059 := bstep (se 1 (by rfl) ⟨106544, by rfl⟩ : syracuseStep 142059 = 213089) B213089
theorem B142071 : Blo 139791 142071 := bstep (se 1 (by rfl) ⟨106553, by rfl⟩ : syracuseStep 142071 = 213107) B213107
theorem B142091 : Blo 139791 142091 := bstep (se 1 (by rfl) ⟨106568, by rfl⟩ : syracuseStep 142091 = 213137) B213137
theorem B142103 : Blo 139791 142103 := bstep (se 1 (by rfl) ⟨106577, by rfl⟩ : syracuseStep 142103 = 213155) B213155
theorem B142123 : Blo 139791 142123 := bstep (se 1 (by rfl) ⟨106592, by rfl⟩ : syracuseStep 142123 = 213185) B213185
theorem B142135 : Blo 139791 142135 := bstep (se 1 (by rfl) ⟨106601, by rfl⟩ : syracuseStep 142135 = 213203) B213203
theorem B273227 : Blo 139791 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B142155 : Blo 139791 142155 := bstep (se 1 (by rfl) ⟨106616, by rfl⟩ : syracuseStep 142155 = 213233) B213233
theorem B142167 : Blo 139791 142167 := bstep (se 1 (by rfl) ⟨106625, by rfl⟩ : syracuseStep 142167 = 213251) B213251
theorem B142187 : Blo 139791 142187 := bstep (se 1 (by rfl) ⟨106640, by rfl⟩ : syracuseStep 142187 = 213281) B213281
theorem B142199 : Blo 139791 142199 := bstep (se 1 (by rfl) ⟨106649, by rfl⟩ : syracuseStep 142199 = 213299) B213299
theorem B142219 : Blo 139791 142219 := bstep (se 1 (by rfl) ⟨106664, by rfl⟩ : syracuseStep 142219 = 213329) B213329
theorem B142231 : Blo 139791 142231 := bstep (se 1 (by rfl) ⟨106673, by rfl⟩ : syracuseStep 142231 = 213347) B213347
theorem B142251 : Blo 139791 142251 := bstep (se 1 (by rfl) ⟨106688, by rfl⟩ : syracuseStep 142251 = 213377) B213377
theorem B142263 : Blo 139791 142263 := bstep (se 1 (by rfl) ⟨106697, by rfl⟩ : syracuseStep 142263 = 213395) B213395
theorem B142283 : Blo 139791 142283 := bstep (se 1 (by rfl) ⟨106712, by rfl⟩ : syracuseStep 142283 = 213425) B213425
theorem B142295 : Blo 139791 142295 := bstep (se 1 (by rfl) ⟨106721, by rfl⟩ : syracuseStep 142295 = 213443) B213443
theorem B142315 : Blo 139791 142315 := bstep (se 1 (by rfl) ⟨106736, by rfl⟩ : syracuseStep 142315 = 213473) B213473
theorem B142327 : Blo 139791 142327 := bstep (se 1 (by rfl) ⟨106745, by rfl⟩ : syracuseStep 142327 = 213491) B213491
theorem B142347 : Blo 139791 142347 := bstep (se 1 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 142347 = 213521) B213521
theorem B142359 : Blo 139791 142359 := bstep (se 1 (by rfl) ⟨106769, by rfl⟩ : syracuseStep 142359 = 213539) B213539
theorem B142379 : Blo 139791 142379 := bstep (se 1 (by rfl) ⟨106784, by rfl⟩ : syracuseStep 142379 = 213569) B213569
theorem B142391 : Blo 139791 142391 := bstep (se 1 (by rfl) ⟨106793, by rfl⟩ : syracuseStep 142391 = 213587) B213587
theorem B142411 : Blo 139791 142411 := bstep (se 1 (by rfl) ⟨106808, by rfl⟩ : syracuseStep 142411 = 213617) B213617
theorem B142423 : Blo 139791 142423 := bstep (se 1 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 142423 = 213635) B213635
theorem B142443 : Blo 139791 142443 := bstep (se 1 (by rfl) ⟨106832, by rfl⟩ : syracuseStep 142443 = 213665) B213665
theorem B142455 : Blo 139791 142455 := bstep (se 1 (by rfl) ⟨106841, by rfl⟩ : syracuseStep 142455 = 213683) B213683
theorem B142475 : Blo 139791 142475 := bstep (se 1 (by rfl) ⟨106856, by rfl⟩ : syracuseStep 142475 = 213713) B213713
theorem B240779 : Blo 139791 240779 := bstep (se 1 (by rfl) ⟨180584, by rfl⟩ : syracuseStep 240779 = 361169) B361169
theorem B142487 : Blo 139791 142487 := bstep (se 1 (by rfl) ⟨106865, by rfl⟩ : syracuseStep 142487 = 213731) B213731
theorem B142507 : Blo 139791 142507 := bstep (se 1 (by rfl) ⟨106880, by rfl⟩ : syracuseStep 142507 = 213761) B213761
theorem B142519 : Blo 139791 142519 := bstep (se 1 (by rfl) ⟨106889, by rfl⟩ : syracuseStep 142519 = 213779) B213779
theorem B142539 : Blo 139791 142539 := bstep (se 1 (by rfl) ⟨106904, by rfl⟩ : syracuseStep 142539 = 213809) B213809
theorem B142551 : Blo 139791 142551 := bstep (se 1 (by rfl) ⟨106913, by rfl⟩ : syracuseStep 142551 = 213827) B213827
theorem B142571 : Blo 139791 142571 := bstep (se 1 (by rfl) ⟨106928, by rfl⟩ : syracuseStep 142571 = 213857) B213857
theorem B142583 : Blo 139791 142583 := bstep (se 1 (by rfl) ⟨106937, by rfl⟩ : syracuseStep 142583 = 213875) B213875
theorem B142603 : Blo 139791 142603 := bstep (se 1 (by rfl) ⟨106952, by rfl⟩ : syracuseStep 142603 = 213905) B213905
theorem B240907 : Blo 139791 240907 := bstep (se 1 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 240907 = 361361) B361361
theorem B142615 : Blo 139791 142615 := bstep (se 1 (by rfl) ⟨106961, by rfl⟩ : syracuseStep 142615 = 213923) B213923
theorem B142635 : Blo 139791 142635 := bstep (se 1 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 142635 = 213953) B213953
theorem B142647 : Blo 139791 142647 := bstep (se 1 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 142647 = 213971) B213971
theorem B404801 : Blo 139791 404801 := bstep (se 2 (by rfl) ⟨151800, by rfl⟩ : syracuseStep 404801 = 303601) B303601
theorem B142667 : Blo 139791 142667 := bstep (se 1 (by rfl) ⟨107000, by rfl⟩ : syracuseStep 142667 = 214001) B214001
theorem B142679 : Blo 139791 142679 := bstep (se 1 (by rfl) ⟨107009, by rfl⟩ : syracuseStep 142679 = 214019) B214019
theorem B863581 : Blo 139791 863581 := bstep (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) B323843
theorem B142699 : Blo 139791 142699 := bstep (se 1 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 142699 = 214049) B214049
theorem B142711 : Blo 139791 142711 := bstep (se 1 (by rfl) ⟨107033, by rfl⟩ : syracuseStep 142711 = 214067) B214067
theorem B142731 : Blo 139791 142731 := bstep (se 1 (by rfl) ⟨107048, by rfl⟩ : syracuseStep 142731 = 214097) B214097
theorem B208279 : Blo 139791 208279 := bstep (se 1 (by rfl) ⟨156209, by rfl⟩ : syracuseStep 208279 = 312419) B312419
theorem B142743 : Blo 139791 142743 := bstep (se 1 (by rfl) ⟨107057, by rfl⟩ : syracuseStep 142743 = 214115) B214115
theorem B241049 : Blo 139791 241049 := bstep (se 2 (by rfl) ⟨90393, by rfl⟩ : syracuseStep 241049 = 180787) B180787
theorem B142763 : Blo 139791 142763 := bstep (se 1 (by rfl) ⟨107072, by rfl⟩ : syracuseStep 142763 = 214145) B214145
theorem B142775 : Blo 139791 142775 := bstep (se 1 (by rfl) ⟨107081, by rfl⟩ : syracuseStep 142775 = 214163) B214163
theorem B306625 : Blo 139791 306625 := bstep (se 2 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 306625 = 229969) B229969
theorem B142795 : Blo 139791 142795 := bstep (se 1 (by rfl) ⟨107096, by rfl⟩ : syracuseStep 142795 = 214193) B214193
theorem B142807 : Blo 139791 142807 := bstep (se 1 (by rfl) ⟨107105, by rfl⟩ : syracuseStep 142807 = 214211) B214211
theorem B142827 : Blo 139791 142827 := bstep (se 1 (by rfl) ⟨107120, by rfl⟩ : syracuseStep 142827 = 214241) B214241
theorem B142839 : Blo 139791 142839 := bstep (se 1 (by rfl) ⟨107129, by rfl⟩ : syracuseStep 142839 = 214259) B214259
theorem B142859 : Blo 139791 142859 := bstep (se 1 (by rfl) ⟨107144, by rfl⟩ : syracuseStep 142859 = 214289) B214289
theorem B142871 : Blo 139791 142871 := bstep (se 1 (by rfl) ⟨107153, by rfl⟩ : syracuseStep 142871 = 214307) B214307
theorem B241177 : Blo 139791 241177 := bstep (se 2 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 241177 = 180883) B180883
theorem B142891 : Blo 139791 142891 := bstep (se 1 (by rfl) ⟨107168, by rfl⟩ : syracuseStep 142891 = 214337) B214337
theorem B503347 : Blo 139791 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B142903 : Blo 139791 142903 := bstep (se 1 (by rfl) ⟨107177, by rfl⟩ : syracuseStep 142903 = 214355) B214355
theorem B142923 : Blo 139791 142923 := bstep (se 1 (by rfl) ⟨107192, by rfl⟩ : syracuseStep 142923 = 214385) B214385
theorem B142935 : Blo 139791 142935 := bstep (se 1 (by rfl) ⟨107201, by rfl⟩ : syracuseStep 142935 = 214403) B214403
theorem B142955 : Blo 139791 142955 := bstep (se 1 (by rfl) ⟨107216, by rfl⟩ : syracuseStep 142955 = 214433) B214433
theorem B142967 : Blo 139791 142967 := bstep (se 1 (by rfl) ⟨107225, by rfl⟩ : syracuseStep 142967 = 214451) B214451
theorem B929411 : Blo 139791 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B142987 : Blo 139791 142987 := bstep (se 1 (by rfl) ⟨107240, by rfl⟩ : syracuseStep 142987 = 214481) B214481
theorem B142999 : Blo 139791 142999 := bstep (se 1 (by rfl) ⟨107249, by rfl⟩ : syracuseStep 142999 = 214499) B214499
theorem B143019 : Blo 139791 143019 := bstep (se 1 (by rfl) ⟨107264, by rfl⟩ : syracuseStep 143019 = 214529) B214529
theorem B143031 : Blo 139791 143031 := bstep (se 1 (by rfl) ⟨107273, by rfl⟩ : syracuseStep 143031 = 214547) B214547
theorem B143051 : Blo 139791 143051 := bstep (se 1 (by rfl) ⟨107288, by rfl⟩ : syracuseStep 143051 = 214577) B214577
theorem B143063 : Blo 139791 143063 := bstep (se 1 (by rfl) ⟨107297, by rfl⟩ : syracuseStep 143063 = 214595) B214595
theorem B143083 : Blo 139791 143083 := bstep (se 1 (by rfl) ⟨107312, by rfl⟩ : syracuseStep 143083 = 214625) B214625
theorem B143095 : Blo 139791 143095 := bstep (se 1 (by rfl) ⟨107321, by rfl⟩ : syracuseStep 143095 = 214643) B214643
theorem B143115 : Blo 139791 143115 := bstep (se 1 (by rfl) ⟨107336, by rfl⟩ : syracuseStep 143115 = 214673) B214673
theorem B864017 : Blo 139791 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B143127 : Blo 139791 143127 := bstep (se 1 (by rfl) ⟨107345, by rfl⟩ : syracuseStep 143127 = 214691) B214691
theorem B143147 : Blo 139791 143147 := bstep (se 1 (by rfl) ⟨107360, by rfl⟩ : syracuseStep 143147 = 214721) B214721
theorem B143159 : Blo 139791 143159 := bstep (se 1 (by rfl) ⟨107369, by rfl⟩ : syracuseStep 143159 = 214739) B214739
theorem B143179 : Blo 139791 143179 := bstep (se 1 (by rfl) ⟨107384, by rfl⟩ : syracuseStep 143179 = 214769) B214769
theorem B143191 : Blo 139791 143191 := bstep (se 1 (by rfl) ⟨107393, by rfl⟩ : syracuseStep 143191 = 214787) B214787
theorem B143211 : Blo 139791 143211 := bstep (se 1 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 143211 = 214817) B214817
theorem B143223 : Blo 139791 143223 := bstep (se 1 (by rfl) ⟨107417, by rfl⟩ : syracuseStep 143223 = 214835) B214835
theorem B143243 : Blo 139791 143243 := bstep (se 1 (by rfl) ⟨107432, by rfl⟩ : syracuseStep 143243 = 214865) B214865
theorem B143255 : Blo 139791 143255 := bstep (se 1 (by rfl) ⟨107441, by rfl⟩ : syracuseStep 143255 = 214883) B214883
theorem B143275 : Blo 139791 143275 := bstep (se 1 (by rfl) ⟨107456, by rfl⟩ : syracuseStep 143275 = 214913) B214913
theorem B143287 : Blo 139791 143287 := bstep (se 1 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 143287 = 214931) B214931
theorem B143307 : Blo 139791 143307 := bstep (se 1 (by rfl) ⟨107480, by rfl⟩ : syracuseStep 143307 = 214961) B214961
theorem B143319 : Blo 139791 143319 := bstep (se 1 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 143319 = 214979) B214979
theorem B143339 : Blo 139791 143339 := bstep (se 1 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 143339 = 215009) B215009
theorem B143351 : Blo 139791 143351 := bstep (se 1 (by rfl) ⟨107513, by rfl⟩ : syracuseStep 143351 = 215027) B215027
theorem B143371 : Blo 139791 143371 := bstep (se 1 (by rfl) ⟨107528, by rfl⟩ : syracuseStep 143371 = 215057) B215057
theorem B143383 : Blo 139791 143383 := bstep (se 1 (by rfl) ⟨107537, by rfl⟩ : syracuseStep 143383 = 215075) B215075
theorem B143403 : Blo 139791 143403 := bstep (se 1 (by rfl) ⟨107552, by rfl⟩ : syracuseStep 143403 = 215105) B215105
theorem B143415 : Blo 139791 143415 := bstep (se 1 (by rfl) ⟨107561, by rfl⟩ : syracuseStep 143415 = 215123) B215123
theorem B340033 : Blo 139791 340033 := bstep (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) B255025
theorem B536651 : Blo 139791 536651 := bstep (se 1 (by rfl) ⟨402488, by rfl⟩ : syracuseStep 536651 = 804977) B804977
theorem B143435 : Blo 139791 143435 := bstep (se 1 (by rfl) ⟨107576, by rfl⟩ : syracuseStep 143435 = 215153) B215153
theorem B241751 : Blo 139791 241751 := bstep (se 1 (by rfl) ⟨181313, by rfl⟩ : syracuseStep 241751 = 362627) B362627
theorem B143447 : Blo 139791 143447 := bstep (se 1 (by rfl) ⟨107585, by rfl⟩ : syracuseStep 143447 = 215171) B215171
theorem B536665 : Blo 139791 536665 := bstep (se 2 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 536665 = 402499) B402499
theorem B143467 : Blo 139791 143467 := bstep (se 1 (by rfl) ⟨107600, by rfl⟩ : syracuseStep 143467 = 215201) B215201
theorem B143479 : Blo 139791 143479 := bstep (se 1 (by rfl) ⟨107609, by rfl⟩ : syracuseStep 143479 = 215219) B215219
theorem B143499 : Blo 139791 143499 := bstep (se 1 (by rfl) ⟨107624, by rfl⟩ : syracuseStep 143499 = 215249) B215249
theorem B143511 : Blo 139791 143511 := bstep (se 1 (by rfl) ⟨107633, by rfl⟩ : syracuseStep 143511 = 215267) B215267
theorem B143531 : Blo 139791 143531 := bstep (se 1 (by rfl) ⟨107648, by rfl⟩ : syracuseStep 143531 = 215297) B215297
theorem B340147 : Blo 139791 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B143543 : Blo 139791 143543 := bstep (se 1 (by rfl) ⟨107657, by rfl⟩ : syracuseStep 143543 = 215315) B215315
theorem B602315 : Blo 139791 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B143563 : Blo 139791 143563 := bstep (se 1 (by rfl) ⟨107672, by rfl⟩ : syracuseStep 143563 = 215345) B215345
theorem B241879 : Blo 139791 241879 := bstep (se 1 (by rfl) ⟨181409, by rfl⟩ : syracuseStep 241879 = 362819) B362819
theorem B143575 : Blo 139791 143575 := bstep (se 1 (by rfl) ⟨107681, by rfl⟩ : syracuseStep 143575 = 215363) B215363
theorem B143595 : Blo 139791 143595 := bstep (se 1 (by rfl) ⟨107696, by rfl⟩ : syracuseStep 143595 = 215393) B215393
theorem B143607 : Blo 139791 143607 := bstep (se 1 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 143607 = 215411) B215411
theorem B143627 : Blo 139791 143627 := bstep (se 1 (by rfl) ⟨107720, by rfl⟩ : syracuseStep 143627 = 215441) B215441
theorem B143639 : Blo 139791 143639 := bstep (se 1 (by rfl) ⟨107729, by rfl⟩ : syracuseStep 143639 = 215459) B215459
theorem B143659 : Blo 139791 143659 := bstep (se 1 (by rfl) ⟨107744, by rfl⟩ : syracuseStep 143659 = 215489) B215489
theorem B143671 : Blo 139791 143671 := bstep (se 1 (by rfl) ⟨107753, by rfl⟩ : syracuseStep 143671 = 215507) B215507
theorem B143691 : Blo 139791 143691 := bstep (se 1 (by rfl) ⟨107768, by rfl⟩ : syracuseStep 143691 = 215537) B215537
theorem B143703 : Blo 139791 143703 := bstep (se 1 (by rfl) ⟨107777, by rfl⟩ : syracuseStep 143703 = 215555) B215555
theorem B143723 : Blo 139791 143723 := bstep (se 1 (by rfl) ⟨107792, by rfl⟩ : syracuseStep 143723 = 215585) B215585
theorem B143735 : Blo 139791 143735 := bstep (se 1 (by rfl) ⟨107801, by rfl⟩ : syracuseStep 143735 = 215603) B215603
theorem B143755 : Blo 139791 143755 := bstep (se 1 (by rfl) ⟨107816, by rfl⟩ : syracuseStep 143755 = 215633) B215633
theorem B143767 : Blo 139791 143767 := bstep (se 1 (by rfl) ⟨107825, by rfl⟩ : syracuseStep 143767 = 215651) B215651
theorem B143787 : Blo 139791 143787 := bstep (se 1 (by rfl) ⟨107840, by rfl⟩ : syracuseStep 143787 = 215681) B215681
theorem B209687 : Blo 139791 209687 := bstep (se 1 (by rfl) ⟨157265, by rfl⟩ : syracuseStep 209687 = 314531) B314531
theorem B242507 : Blo 139791 242507 := bstep (se 1 (by rfl) ⟨181880, by rfl⟩ : syracuseStep 242507 = 363761) B363761
theorem B209753 : Blo 139791 209753 := bstep (se 2 (by rfl) ⟨78657, by rfl⟩ : syracuseStep 209753 = 157315) B157315
theorem B471959 : Blo 139791 471959 := bstep (se 1 (by rfl) ⟨353969, by rfl⟩ : syracuseStep 471959 = 707939) B707939
theorem B209867 : Blo 139791 209867 := bstep (se 1 (by rfl) ⟨157400, by rfl⟩ : syracuseStep 209867 = 314801) B314801
theorem B242635 : Blo 139791 242635 := bstep (se 1 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 242635 = 363953) B363953
theorem B209879 : Blo 139791 209879 := bstep (se 1 (by rfl) ⟨157409, by rfl⟩ : syracuseStep 209879 = 314819) B314819
theorem B537623 : Blo 139791 537623 := bstep (se 1 (by rfl) ⟨403217, by rfl⟩ : syracuseStep 537623 = 806435) B806435
theorem B209945 : Blo 139791 209945 := bstep (se 2 (by rfl) ⟨78729, by rfl⟩ : syracuseStep 209945 = 157459) B157459
theorem B210059 : Blo 139791 210059 := bstep (se 1 (by rfl) ⟨157544, by rfl⟩ : syracuseStep 210059 = 315089) B315089
theorem B210071 : Blo 139791 210071 := bstep (se 1 (by rfl) ⟨157553, by rfl⟩ : syracuseStep 210071 = 315107) B315107
theorem B799895 : Blo 139791 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B210137 : Blo 139791 210137 := bstep (se 2 (by rfl) ⟨78801, by rfl⟩ : syracuseStep 210137 = 157603) B157603
theorem B210251 : Blo 139791 210251 := bstep (se 1 (by rfl) ⟨157688, by rfl⟩ : syracuseStep 210251 = 315377) B315377
theorem B210263 : Blo 139791 210263 := bstep (se 1 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 210263 = 315395) B315395
theorem B406873 : Blo 139791 406873 := bstep (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) B305155
theorem B177547 : Blo 139791 177547 := bstep (se 1 (by rfl) ⟨133160, by rfl⟩ : syracuseStep 177547 = 266321) B266321
theorem B210329 : Blo 139791 210329 := bstep (se 2 (by rfl) ⟨78873, by rfl⟩ : syracuseStep 210329 = 157747) B157747
theorem B472499 : Blo 139791 472499 := bstep (se 1 (by rfl) ⟨354374, by rfl⟩ : syracuseStep 472499 = 708749) B708749
theorem B1553843 : Blo 139791 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B275969 : Blo 139791 275969 := bstep (se 2 (by rfl) ⟨103488, by rfl⟩ : syracuseStep 275969 = 206977) B206977
theorem B210443 : Blo 139791 210443 := bstep (se 1 (by rfl) ⟨157832, by rfl⟩ : syracuseStep 210443 = 315665) B315665
theorem B210455 : Blo 139791 210455 := bstep (se 1 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 210455 = 315683) B315683
theorem B1029667 : Blo 139791 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B210521 : Blo 139791 210521 := bstep (se 2 (by rfl) ⟨78945, by rfl⟩ : syracuseStep 210521 = 157891) B157891
theorem B996965 : Blo 139791 996965 := bstep (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) B186931
theorem B177815 : Blo 139791 177815 := bstep (se 1 (by rfl) ⟨133361, by rfl⟩ : syracuseStep 177815 = 266723) B266723
theorem B472769 : Blo 139791 472769 := bstep (se 2 (by rfl) ⟨177288, by rfl⟩ : syracuseStep 472769 = 354577) B354577
theorem B210635 : Blo 139791 210635 := bstep (se 1 (by rfl) ⟨157976, by rfl⟩ : syracuseStep 210635 = 315953) B315953
theorem B210647 : Blo 139791 210647 := bstep (se 1 (by rfl) ⟨157985, by rfl⟩ : syracuseStep 210647 = 315971) B315971
theorem B407261 : Blo 139791 407261 := bstep (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) B152723
theorem B341783 : Blo 139791 341783 := bstep (se 1 (by rfl) ⟨256337, by rfl⟩ : syracuseStep 341783 = 512675) B512675
theorem B210713 : Blo 139791 210713 := bstep (se 2 (by rfl) ⟨79017, by rfl⟩ : syracuseStep 210713 = 158035) B158035
theorem B2176885 : Blo 139791 2176885 := bstep (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) B204083
theorem B210827 : Blo 139791 210827 := bstep (se 1 (by rfl) ⟨158120, by rfl⟩ : syracuseStep 210827 = 316241) B316241
theorem B210839 : Blo 139791 210839 := bstep (se 1 (by rfl) ⟨158129, by rfl⟩ : syracuseStep 210839 = 316259) B316259
theorem B210905 : Blo 139791 210905 := bstep (se 2 (by rfl) ⟨79089, by rfl⟩ : syracuseStep 210905 = 158179) B158179
theorem B15677509 : Blo 139791 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B211019 : Blo 139791 211019 := bstep (se 1 (by rfl) ⟨158264, by rfl⟩ : syracuseStep 211019 = 316529) B316529
theorem B211031 : Blo 139791 211031 := bstep (se 1 (by rfl) ⟨158273, by rfl⟩ : syracuseStep 211031 = 316547) B316547
theorem B211097 : Blo 139791 211097 := bstep (se 2 (by rfl) ⟨79161, by rfl⟩ : syracuseStep 211097 = 158323) B158323
theorem B473309 : Blo 139791 473309 := bstep (se 3 (by rfl) ⟨88745, by rfl⟩ : syracuseStep 473309 = 177491) B177491
theorem B538883 : Blo 139791 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B211211 : Blo 139791 211211 := bstep (se 1 (by rfl) ⟨158408, by rfl⟩ : syracuseStep 211211 = 316817) B316817
theorem B211223 : Blo 139791 211223 := bstep (se 1 (by rfl) ⟨158417, by rfl⟩ : syracuseStep 211223 = 316835) B316835
theorem B178519 : Blo 139791 178519 := bstep (se 1 (by rfl) ⟨133889, by rfl⟩ : syracuseStep 178519 = 267779) B267779
theorem B211289 : Blo 139791 211289 := bstep (se 2 (by rfl) ⟨79233, by rfl⟩ : syracuseStep 211289 = 158467) B158467
theorem B211403 : Blo 139791 211403 := bstep (se 1 (by rfl) ⟨158552, by rfl⟩ : syracuseStep 211403 = 317105) B317105
theorem B211415 : Blo 139791 211415 := bstep (se 1 (by rfl) ⟨158561, by rfl⟩ : syracuseStep 211415 = 317123) B317123
theorem B10271245 : Blo 139791 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B342551 : Blo 139791 342551 := bstep (se 1 (by rfl) ⟨256913, by rfl⟩ : syracuseStep 342551 = 513827) B513827
theorem B211481 : Blo 139791 211481 := bstep (se 2 (by rfl) ⟨79305, by rfl⟩ : syracuseStep 211481 = 158611) B158611
theorem B899677 : Blo 139791 899677 := bstep (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) B337379
theorem B211595 : Blo 139791 211595 := bstep (se 1 (by rfl) ⟨158696, by rfl⟩ : syracuseStep 211595 = 317393) B317393
theorem B506519 : Blo 139791 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B211607 : Blo 139791 211607 := bstep (se 1 (by rfl) ⟨158705, by rfl⟩ : syracuseStep 211607 = 317411) B317411
theorem B211673 : Blo 139791 211673 := bstep (se 2 (by rfl) ⟨79377, by rfl⟩ : syracuseStep 211673 = 158755) B158755
theorem B604979 : Blo 139791 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B211787 : Blo 139791 211787 := bstep (se 1 (by rfl) ⟨158840, by rfl⟩ : syracuseStep 211787 = 317681) B317681
theorem B211799 : Blo 139791 211799 := bstep (se 1 (by rfl) ⟨158849, by rfl⟩ : syracuseStep 211799 = 317699) B317699
theorem B211865 : Blo 139791 211865 := bstep (se 2 (by rfl) ⟨79449, by rfl⟩ : syracuseStep 211865 = 158899) B158899
theorem B211979 : Blo 139791 211979 := bstep (se 1 (by rfl) ⟨158984, by rfl⟩ : syracuseStep 211979 = 317969) B317969
theorem B801809 : Blo 139791 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B211991 : Blo 139791 211991 := bstep (se 1 (by rfl) ⟨158993, by rfl⟩ : syracuseStep 211991 = 317987) B317987
theorem B212057 : Blo 139791 212057 := bstep (se 2 (by rfl) ⟨79521, by rfl⟩ : syracuseStep 212057 = 159043) B159043
theorem B212171 : Blo 139791 212171 := bstep (se 1 (by rfl) ⟨159128, by rfl⟩ : syracuseStep 212171 = 318257) B318257
theorem B212183 : Blo 139791 212183 := bstep (se 1 (by rfl) ⟨159137, by rfl⟩ : syracuseStep 212183 = 318275) B318275
theorem B212249 : Blo 139791 212249 := bstep (se 2 (by rfl) ⟨79593, by rfl⟩ : syracuseStep 212249 = 159187) B159187
theorem B474443 : Blo 139791 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B212363 : Blo 139791 212363 := bstep (se 1 (by rfl) ⟨159272, by rfl⟩ : syracuseStep 212363 = 318545) B318545
theorem B540049 : Blo 139791 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B4078997 : Blo 139791 4078997 := bstep (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) B191203
theorem B212375 : Blo 139791 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B1195469 : Blo 139791 1195469 := bstep (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) B448301
theorem B212441 : Blo 139791 212441 := bstep (se 2 (by rfl) ⟨79665, by rfl⟩ : syracuseStep 212441 = 159331) B159331
theorem B212555 : Blo 139791 212555 := bstep (se 1 (by rfl) ⟨159416, by rfl⟩ : syracuseStep 212555 = 318833) B318833
theorem B212567 : Blo 139791 212567 := bstep (se 1 (by rfl) ⟨159425, by rfl⟩ : syracuseStep 212567 = 318851) B318851
theorem B474713 : Blo 139791 474713 := bstep (se 2 (by rfl) ⟨178017, by rfl⟩ : syracuseStep 474713 = 356035) B356035
theorem B769637 : Blo 139791 769637 := bstep (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) B144307
theorem B212633 : Blo 139791 212633 := bstep (se 2 (by rfl) ⟨79737, by rfl⟩ : syracuseStep 212633 = 159475) B159475
theorem B212747 : Blo 139791 212747 := bstep (se 1 (by rfl) ⟨159560, by rfl⟩ : syracuseStep 212747 = 319121) B319121
theorem B212759 : Blo 139791 212759 := bstep (se 1 (by rfl) ⟨159569, by rfl⟩ : syracuseStep 212759 = 319139) B319139
theorem B212825 : Blo 139791 212825 := bstep (se 2 (by rfl) ⟨79809, by rfl⟩ : syracuseStep 212825 = 159619) B159619
theorem B212939 : Blo 139791 212939 := bstep (se 1 (by rfl) ⟨159704, by rfl⟩ : syracuseStep 212939 = 319409) B319409
theorem B212951 : Blo 139791 212951 := bstep (se 1 (by rfl) ⟨159713, by rfl⟩ : syracuseStep 212951 = 319427) B319427
theorem B180235 : Blo 139791 180235 := bstep (se 1 (by rfl) ⟨135176, by rfl⟩ : syracuseStep 180235 = 270353) B270353
theorem B213017 : Blo 139791 213017 := bstep (se 2 (by rfl) ⟨79881, by rfl⟩ : syracuseStep 213017 = 159763) B159763
theorem B901165 : Blo 139791 901165 := bstep (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) B337937
theorem B213131 : Blo 139791 213131 := bstep (se 1 (by rfl) ⟨159848, by rfl⟩ : syracuseStep 213131 = 319697) B319697
theorem B213143 : Blo 139791 213143 := bstep (se 1 (by rfl) ⟨159857, by rfl⟩ : syracuseStep 213143 = 319715) B319715
theorem B344243 : Blo 139791 344243 := bstep (se 1 (by rfl) ⟨258182, by rfl⟩ : syracuseStep 344243 = 516365) B516365
theorem B213209 : Blo 139791 213209 := bstep (se 2 (by rfl) ⟨79953, by rfl⟩ : syracuseStep 213209 = 159907) B159907
theorem B606467 : Blo 139791 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B475415 : Blo 139791 475415 := bstep (se 1 (by rfl) ⟨356561, by rfl⟩ : syracuseStep 475415 = 713123) B713123
theorem B213323 : Blo 139791 213323 := bstep (se 1 (by rfl) ⟨159992, by rfl⟩ : syracuseStep 213323 = 319985) B319985
theorem B213335 : Blo 139791 213335 := bstep (se 1 (by rfl) ⟨160001, by rfl⟩ : syracuseStep 213335 = 320003) B320003
theorem B213401 : Blo 139791 213401 := bstep (se 2 (by rfl) ⟨80025, by rfl⟩ : syracuseStep 213401 = 160051) B160051
theorem B213515 : Blo 139791 213515 := bstep (se 1 (by rfl) ⟨160136, by rfl⟩ : syracuseStep 213515 = 320273) B320273
theorem B213527 : Blo 139791 213527 := bstep (se 1 (by rfl) ⟨160145, by rfl⟩ : syracuseStep 213527 = 320291) B320291
theorem B1327691 : Blo 139791 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B213593 : Blo 139791 213593 := bstep (se 2 (by rfl) ⟨80097, by rfl⟩ : syracuseStep 213593 = 160195) B160195
theorem B213707 : Blo 139791 213707 := bstep (se 1 (by rfl) ⟨160280, by rfl⟩ : syracuseStep 213707 = 320561) B320561
theorem B213719 : Blo 139791 213719 := bstep (se 1 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 213719 = 320579) B320579
theorem B213785 : Blo 139791 213785 := bstep (se 2 (by rfl) ⟨80169, by rfl⟩ : syracuseStep 213785 = 160339) B160339
theorem B475955 : Blo 139791 475955 := bstep (se 1 (by rfl) ⟨356966, by rfl⟩ : syracuseStep 475955 = 713933) B713933
theorem B213899 : Blo 139791 213899 := bstep (se 1 (by rfl) ⟨160424, by rfl⟩ : syracuseStep 213899 = 320849) B320849
theorem B213911 : Blo 139791 213911 := bstep (se 1 (by rfl) ⟨160433, by rfl⟩ : syracuseStep 213911 = 320867) B320867
theorem B181207 : Blo 139791 181207 := bstep (se 1 (by rfl) ⟨135905, by rfl⟩ : syracuseStep 181207 = 271811) B271811
theorem B213977 : Blo 139791 213977 := bstep (se 2 (by rfl) ⟨80241, by rfl⟩ : syracuseStep 213977 = 160483) B160483
theorem B1557521 : Blo 139791 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B476225 : Blo 139791 476225 := bstep (se 2 (by rfl) ⟨178584, by rfl⟩ : syracuseStep 476225 = 357169) B357169
theorem B214091 : Blo 139791 214091 := bstep (se 1 (by rfl) ⟨160568, by rfl⟩ : syracuseStep 214091 = 321137) B321137
theorem B214103 : Blo 139791 214103 := bstep (se 1 (by rfl) ⟨160577, by rfl⟩ : syracuseStep 214103 = 321155) B321155
theorem B214169 : Blo 139791 214169 := bstep (se 2 (by rfl) ⟨80313, by rfl⟩ : syracuseStep 214169 = 160627) B160627
theorem B2802869 : Blo 139791 2802869 := bstep (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) B262769
theorem B214283 : Blo 139791 214283 := bstep (se 1 (by rfl) ⟨160712, by rfl⟩ : syracuseStep 214283 = 321425) B321425
theorem B214295 : Blo 139791 214295 := bstep (se 1 (by rfl) ⟨160721, by rfl⟩ : syracuseStep 214295 = 321443) B321443
theorem B541997 : Blo 139791 541997 := bstep (se 3 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 541997 = 203249) B203249
theorem B214361 : Blo 139791 214361 := bstep (se 2 (by rfl) ⟨80385, by rfl⟩ : syracuseStep 214361 = 160771) B160771
theorem B214475 : Blo 139791 214475 := bstep (se 1 (by rfl) ⟨160856, by rfl⟩ : syracuseStep 214475 = 321713) B321713
theorem B214487 : Blo 139791 214487 := bstep (se 1 (by rfl) ⟨160865, by rfl⟩ : syracuseStep 214487 = 321731) B321731
theorem B214553 : Blo 139791 214553 := bstep (se 2 (by rfl) ⟨80457, by rfl⟩ : syracuseStep 214553 = 160915) B160915
theorem B476765 : Blo 139791 476765 := bstep (se 3 (by rfl) ⟨89393, by rfl⟩ : syracuseStep 476765 = 178787) B178787
theorem B214667 : Blo 139791 214667 := bstep (se 1 (by rfl) ⟨161000, by rfl⟩ : syracuseStep 214667 = 322001) B322001
theorem B1328791 : Blo 139791 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B214679 : Blo 139791 214679 := bstep (se 1 (by rfl) ⟨161009, by rfl⟩ : syracuseStep 214679 = 322019) B322019
theorem B542387 : Blo 139791 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B214745 : Blo 139791 214745 := bstep (se 2 (by rfl) ⟨80529, by rfl⟩ : syracuseStep 214745 = 161059) B161059
theorem B1066769 : Blo 139791 1066769 := bstep (se 2 (by rfl) ⟨400038, by rfl⟩ : syracuseStep 1066769 = 800077) B800077
theorem B771905 : Blo 139791 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B214859 : Blo 139791 214859 := bstep (se 1 (by rfl) ⟨161144, by rfl⟩ : syracuseStep 214859 = 322289) B322289
theorem B214871 : Blo 139791 214871 := bstep (se 1 (by rfl) ⟨161153, by rfl⟩ : syracuseStep 214871 = 322307) B322307
theorem B214937 : Blo 139791 214937 := bstep (se 2 (by rfl) ⟨80601, by rfl⟩ : syracuseStep 214937 = 161203) B161203
theorem B575453 : Blo 139791 575453 := bstep (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) B215795
theorem B215051 : Blo 139791 215051 := bstep (se 1 (by rfl) ⟨161288, by rfl⟩ : syracuseStep 215051 = 322577) B322577
theorem B215063 : Blo 139791 215063 := bstep (se 1 (by rfl) ⟨161297, by rfl⟩ : syracuseStep 215063 = 322595) B322595
theorem B542771 : Blo 139791 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B215129 : Blo 139791 215129 := bstep (se 2 (by rfl) ⟨80673, by rfl⟩ : syracuseStep 215129 = 161347) B161347
theorem B149707 : Blo 139791 149707 := bstep (se 1 (by rfl) ⟨112280, by rfl⟩ : syracuseStep 149707 = 224561) B224561
theorem B215243 : Blo 139791 215243 := bstep (se 1 (by rfl) ⟨161432, by rfl⟩ : syracuseStep 215243 = 322865) B322865
theorem B215255 : Blo 139791 215255 := bstep (se 1 (by rfl) ⟨161441, by rfl⟩ : syracuseStep 215255 = 322883) B322883
theorem B215321 : Blo 139791 215321 := bstep (se 2 (by rfl) ⟨80745, by rfl⟩ : syracuseStep 215321 = 161491) B161491
theorem B2312549 : Blo 139791 2312549 := bstep (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) B433603
theorem B215435 : Blo 139791 215435 := bstep (se 1 (by rfl) ⟨161576, by rfl⟩ : syracuseStep 215435 = 323153) B323153
theorem B215447 : Blo 139791 215447 := bstep (se 1 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 215447 = 323171) B323171
theorem B608705 : Blo 139791 608705 := bstep (se 2 (by rfl) ⟨228264, by rfl⟩ : syracuseStep 608705 = 456529) B456529
theorem B215513 : Blo 139791 215513 := bstep (se 2 (by rfl) ⟨80817, by rfl⟩ : syracuseStep 215513 = 161635) B161635
theorem B379457 : Blo 139791 379457 := bstep (se 2 (by rfl) ⟨142296, by rfl⟩ : syracuseStep 379457 = 284593) B284593
theorem B215627 : Blo 139791 215627 := bstep (se 1 (by rfl) ⟨161720, by rfl⟩ : syracuseStep 215627 = 323441) B323441
theorem B215639 : Blo 139791 215639 := bstep (se 1 (by rfl) ⟨161729, by rfl⟩ : syracuseStep 215639 = 323459) B323459
theorem B477899 : Blo 139791 477899 := bstep (se 1 (by rfl) ⟨358424, by rfl⟩ : syracuseStep 477899 = 716849) B716849
theorem B150455 : Blo 139791 150455 := bstep (se 1 (by rfl) ⟨112841, by rfl⟩ : syracuseStep 150455 = 225683) B225683
theorem B478169 : Blo 139791 478169 := bstep (se 2 (by rfl) ⟨179313, by rfl⟩ : syracuseStep 478169 = 358627) B358627
theorem B314585 : Blo 139791 314585 := bstep (se 2 (by rfl) ⟨117969, by rfl⟩ : syracuseStep 314585 = 235939) B235939
theorem B314675 : Blo 139791 314675 := bstep (se 1 (by rfl) ⟨236006, by rfl⟩ : syracuseStep 314675 = 472013) B472013
theorem B314711 : Blo 139791 314711 := bstep (se 1 (by rfl) ⟨236033, by rfl⟩ : syracuseStep 314711 = 472067) B472067
theorem B544259 : Blo 139791 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B314891 : Blo 139791 314891 := bstep (se 1 (by rfl) ⟨236168, by rfl⟩ : syracuseStep 314891 = 472337) B472337
theorem B675373 : Blo 139791 675373 := bstep (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) B253265
theorem B314945 : Blo 139791 314945 := bstep (se 2 (by rfl) ⟨118104, by rfl⟩ : syracuseStep 314945 = 236209) B236209
theorem B478871 : Blo 139791 478871 := bstep (se 1 (by rfl) ⟨359153, by rfl⟩ : syracuseStep 478871 = 718307) B718307
theorem B1232563 : Blo 139791 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B315161 : Blo 139791 315161 := bstep (se 2 (by rfl) ⟨118185, by rfl⟩ : syracuseStep 315161 = 236371) B236371
theorem B347993 : Blo 139791 347993 := bstep (se 2 (by rfl) ⟨130497, by rfl⟩ : syracuseStep 347993 = 260995) B260995
theorem B315251 : Blo 139791 315251 := bstep (se 1 (by rfl) ⟨236438, by rfl⟩ : syracuseStep 315251 = 472877) B472877
theorem B315287 : Blo 139791 315287 := bstep (se 1 (by rfl) ⟨236465, by rfl⟩ : syracuseStep 315287 = 472931) B472931
theorem B511895 : Blo 139791 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B479155 : Blo 139791 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B544715 : Blo 139791 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B315467 : Blo 139791 315467 := bstep (se 1 (by rfl) ⟨236600, by rfl⟩ : syracuseStep 315467 = 473201) B473201
theorem B610379 : Blo 139791 610379 := bstep (se 1 (by rfl) ⟨457784, by rfl⟩ : syracuseStep 610379 = 915569) B915569
theorem B315521 : Blo 139791 315521 := bstep (se 2 (by rfl) ⟨118320, by rfl⟩ : syracuseStep 315521 = 236641) B236641
theorem B872579 : Blo 139791 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B544913 : Blo 139791 544913 := bstep (se 2 (by rfl) ⟨204342, by rfl⟩ : syracuseStep 544913 = 408685) B408685
theorem B479411 : Blo 139791 479411 := bstep (se 1 (by rfl) ⟨359558, by rfl⟩ : syracuseStep 479411 = 719117) B719117
theorem B807185 : Blo 139791 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B315737 : Blo 139791 315737 := bstep (se 2 (by rfl) ⟨118401, by rfl⟩ : syracuseStep 315737 = 236803) B236803
theorem B315827 : Blo 139791 315827 := bstep (se 1 (by rfl) ⟨236870, by rfl⟩ : syracuseStep 315827 = 473741) B473741
theorem B479681 : Blo 139791 479681 := bstep (se 2 (by rfl) ⟨179880, by rfl⟩ : syracuseStep 479681 = 359761) B359761
theorem B315863 : Blo 139791 315863 := bstep (se 1 (by rfl) ⟨236897, by rfl⟩ : syracuseStep 315863 = 473795) B473795
theorem B316043 : Blo 139791 316043 := bstep (se 1 (by rfl) ⟨237032, by rfl⟩ : syracuseStep 316043 = 474065) B474065
theorem B316097 : Blo 139791 316097 := bstep (se 2 (by rfl) ⟨118536, by rfl⟩ : syracuseStep 316097 = 237073) B237073
theorem B807641 : Blo 139791 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B611165 : Blo 139791 611165 := bstep (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) B229187
theorem B545687 : Blo 139791 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B316313 : Blo 139791 316313 := bstep (se 2 (by rfl) ⟨118617, by rfl⟩ : syracuseStep 316313 = 237235) B237235
theorem B873433 : Blo 139791 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B480221 : Blo 139791 480221 := bstep (se 3 (by rfl) ⟨90041, by rfl⟩ : syracuseStep 480221 = 180083) B180083
theorem B316403 : Blo 139791 316403 := bstep (se 1 (by rfl) ⟨237302, by rfl⟩ : syracuseStep 316403 = 474605) B474605
theorem B316439 : Blo 139791 316439 := bstep (se 1 (by rfl) ⟨237329, by rfl⟩ : syracuseStep 316439 = 474659) B474659
theorem B152663 : Blo 139791 152663 := bstep (se 1 (by rfl) ⟨114497, by rfl⟩ : syracuseStep 152663 = 228995) B228995
theorem B545885 : Blo 139791 545885 := bstep (se 3 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 545885 = 204707) B204707
theorem B316619 : Blo 139791 316619 := bstep (se 1 (by rfl) ⟨237464, by rfl⟩ : syracuseStep 316619 = 474929) B474929
theorem B316673 : Blo 139791 316673 := bstep (se 2 (by rfl) ⟨118752, by rfl⟩ : syracuseStep 316673 = 237505) B237505
theorem B972107 : Blo 139791 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B284033 : Blo 139791 284033 := bstep (se 2 (by rfl) ⟨106512, by rfl⟩ : syracuseStep 284033 = 213025) B213025
theorem B316889 : Blo 139791 316889 := bstep (se 2 (by rfl) ⟨118833, by rfl⟩ : syracuseStep 316889 = 237667) B237667
theorem B382429 : Blo 139791 382429 := bstep (se 3 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 382429 = 143411) B143411
theorem B513553 : Blo 139791 513553 := bstep (se 2 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 513553 = 385165) B385165
theorem B316979 : Blo 139791 316979 := bstep (se 1 (by rfl) ⟨237734, by rfl⟩ : syracuseStep 316979 = 475469) B475469
theorem B1070657 : Blo 139791 1070657 := bstep (se 2 (by rfl) ⟨401496, by rfl⟩ : syracuseStep 1070657 = 802993) B802993
theorem B317015 : Blo 139791 317015 := bstep (se 1 (by rfl) ⟨237761, by rfl⟩ : syracuseStep 317015 = 475523) B475523
theorem B382657 : Blo 139791 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B317195 : Blo 139791 317195 := bstep (se 1 (by rfl) ⟨237896, by rfl⟩ : syracuseStep 317195 = 475793) B475793
theorem B644915 : Blo 139791 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B317249 : Blo 139791 317249 := bstep (se 2 (by rfl) ⟨118968, by rfl⟩ : syracuseStep 317249 = 237937) B237937
theorem B710531 : Blo 139791 710531 := bstep (se 1 (by rfl) ⟨532898, by rfl⟩ : syracuseStep 710531 = 1065797) B1065797
theorem B317465 : Blo 139791 317465 := bstep (se 2 (by rfl) ⟨119049, by rfl⟩ : syracuseStep 317465 = 238099) B238099
theorem B481355 : Blo 139791 481355 := bstep (se 1 (by rfl) ⟨361016, by rfl⟩ : syracuseStep 481355 = 722033) B722033
theorem B317555 : Blo 139791 317555 := bstep (se 1 (by rfl) ⟨238166, by rfl⟩ : syracuseStep 317555 = 476333) B476333
theorem B2021507 : Blo 139791 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B612497 : Blo 139791 612497 := bstep (se 2 (by rfl) ⟨229686, by rfl⟩ : syracuseStep 612497 = 459373) B459373
theorem B317591 : Blo 139791 317591 := bstep (se 1 (by rfl) ⟨238193, by rfl⟩ : syracuseStep 317591 = 476387) B476387
theorem B1628461 : Blo 139791 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B2283821 : Blo 139791 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B317771 : Blo 139791 317771 := bstep (se 1 (by rfl) ⟨238328, by rfl⟩ : syracuseStep 317771 = 476657) B476657
theorem B481625 : Blo 139791 481625 := bstep (se 2 (by rfl) ⟨180609, by rfl⟩ : syracuseStep 481625 = 361219) B361219
theorem B317825 : Blo 139791 317825 := bstep (se 2 (by rfl) ⟨119184, by rfl⟩ : syracuseStep 317825 = 238369) B238369
theorem B645677 : Blo 139791 645677 := bstep (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) B242129
theorem B318041 : Blo 139791 318041 := bstep (se 2 (by rfl) ⟨119265, by rfl⟩ : syracuseStep 318041 = 238531) B238531
theorem B318131 : Blo 139791 318131 := bstep (se 1 (by rfl) ⟨238598, by rfl⟩ : syracuseStep 318131 = 477197) B477197
theorem B318167 : Blo 139791 318167 := bstep (se 1 (by rfl) ⟨238625, by rfl⟩ : syracuseStep 318167 = 477251) B477251
theorem B514777 : Blo 139791 514777 := bstep (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) B386083
theorem B318347 : Blo 139791 318347 := bstep (se 1 (by rfl) ⟨238760, by rfl⟩ : syracuseStep 318347 = 477521) B477521
theorem B318401 : Blo 139791 318401 := bstep (se 2 (by rfl) ⟨119400, by rfl⟩ : syracuseStep 318401 = 238801) B238801
theorem B482327 : Blo 139791 482327 := bstep (se 1 (by rfl) ⟨361745, by rfl⟩ : syracuseStep 482327 = 723491) B723491
theorem B285761 : Blo 139791 285761 := bstep (se 2 (by rfl) ⟨107160, by rfl⟩ : syracuseStep 285761 = 214321) B214321
theorem B1596509 : Blo 139791 1596509 := bstep (se 3 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 1596509 = 598691) B598691
theorem B318617 : Blo 139791 318617 := bstep (se 2 (by rfl) ⟨119481, by rfl⟩ : syracuseStep 318617 = 238963) B238963
theorem B318707 : Blo 139791 318707 := bstep (se 1 (by rfl) ⟨239030, by rfl⟩ : syracuseStep 318707 = 478061) B478061
theorem B318743 : Blo 139791 318743 := bstep (se 1 (by rfl) ⟨239057, by rfl⟩ : syracuseStep 318743 = 478115) B478115
theorem B613763 : Blo 139791 613763 := bstep (se 1 (by rfl) ⟨460322, by rfl⟩ : syracuseStep 613763 = 920645) B920645
theorem B318923 : Blo 139791 318923 := bstep (se 1 (by rfl) ⟨239192, by rfl⟩ : syracuseStep 318923 = 478385) B478385
theorem B1072601 : Blo 139791 1072601 := bstep (se 2 (by rfl) ⟨402225, by rfl⟩ : syracuseStep 1072601 = 804451) B804451
theorem B318977 : Blo 139791 318977 := bstep (se 2 (by rfl) ⟨119616, by rfl⟩ : syracuseStep 318977 = 239233) B239233
theorem B1138211 : Blo 139791 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B482867 : Blo 139791 482867 := bstep (se 1 (by rfl) ⟨362150, by rfl⟩ : syracuseStep 482867 = 724301) B724301
theorem B679603 : Blo 139791 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B319193 : Blo 139791 319193 := bstep (se 2 (by rfl) ⟨119697, by rfl⟩ : syracuseStep 319193 = 239395) B239395
theorem B319283 : Blo 139791 319283 := bstep (se 1 (by rfl) ⟨239462, by rfl⟩ : syracuseStep 319283 = 478925) B478925
theorem B483137 : Blo 139791 483137 := bstep (se 2 (by rfl) ⟨181176, by rfl⟩ : syracuseStep 483137 = 362353) B362353
theorem B319319 : Blo 139791 319319 := bstep (se 1 (by rfl) ⟨239489, by rfl⟩ : syracuseStep 319319 = 478979) B478979
theorem B319499 : Blo 139791 319499 := bstep (se 1 (by rfl) ⟨239624, by rfl⟩ : syracuseStep 319499 = 479249) B479249
theorem B221195 : Blo 139791 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B319553 : Blo 139791 319553 := bstep (se 2 (by rfl) ⟨119832, by rfl⟩ : syracuseStep 319553 = 239665) B239665
theorem B614621 : Blo 139791 614621 := bstep (se 3 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 614621 = 230483) B230483
theorem B319769 : Blo 139791 319769 := bstep (se 2 (by rfl) ⟨119913, by rfl⟩ : syracuseStep 319769 = 239827) B239827
theorem B483677 : Blo 139791 483677 := bstep (se 3 (by rfl) ⟨90689, by rfl⟩ : syracuseStep 483677 = 181379) B181379
theorem B319859 : Blo 139791 319859 := bstep (se 1 (by rfl) ⟨239894, by rfl⟩ : syracuseStep 319859 = 479789) B479789
theorem B319883 : Blo 139791 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B450967 : Blo 139791 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B319895 : Blo 139791 319895 := bstep (se 1 (by rfl) ⟨239921, by rfl⟩ : syracuseStep 319895 = 479843) B479843
theorem B320075 : Blo 139791 320075 := bstep (se 1 (by rfl) ⟨240056, by rfl⟩ : syracuseStep 320075 = 480113) B480113
theorem B320129 : Blo 139791 320129 := bstep (se 2 (by rfl) ⟨120048, by rfl⟩ : syracuseStep 320129 = 240097) B240097
theorem B451403 : Blo 139791 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B320345 : Blo 139791 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B320435 : Blo 139791 320435 := bstep (se 1 (by rfl) ⟨240326, by rfl⟩ : syracuseStep 320435 = 480653) B480653
theorem B320471 : Blo 139791 320471 := bstep (se 1 (by rfl) ⟨240353, by rfl⟩ : syracuseStep 320471 = 480707) B480707
theorem B1860569 : Blo 139791 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B320651 : Blo 139791 320651 := bstep (se 1 (by rfl) ⟨240488, by rfl⟩ : syracuseStep 320651 = 480977) B480977
theorem B320705 : Blo 139791 320705 := bstep (se 2 (by rfl) ⟨120264, by rfl⟩ : syracuseStep 320705 = 240529) B240529
theorem B320921 : Blo 139791 320921 := bstep (se 2 (by rfl) ⟨120345, by rfl⟩ : syracuseStep 320921 = 240691) B240691
theorem B484811 : Blo 139791 484811 := bstep (se 1 (by rfl) ⟨363608, by rfl⟩ : syracuseStep 484811 = 727217) B727217
theorem B321011 : Blo 139791 321011 := bstep (se 1 (by rfl) ⟨240758, by rfl⟩ : syracuseStep 321011 = 481517) B481517
theorem B714257 : Blo 139791 714257 := bstep (se 2 (by rfl) ⟨267846, by rfl⟩ : syracuseStep 714257 = 535693) B535693
theorem B321047 : Blo 139791 321047 := bstep (se 1 (by rfl) ⟨240785, by rfl⟩ : syracuseStep 321047 = 481571) B481571
theorem B714419 : Blo 139791 714419 := bstep (se 1 (by rfl) ⟨535814, by rfl⟩ : syracuseStep 714419 = 1071629) B1071629
theorem B157387 : Blo 139791 157387 := bstep (se 1 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 157387 = 236081) B236081
theorem B452299 : Blo 139791 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B321227 : Blo 139791 321227 := bstep (se 1 (by rfl) ⟨240920, by rfl⟩ : syracuseStep 321227 = 481841) B481841
theorem B1009369 : Blo 139791 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B485081 : Blo 139791 485081 := bstep (se 2 (by rfl) ⟨181905, by rfl⟩ : syracuseStep 485081 = 363811) B363811
theorem B321281 : Blo 139791 321281 := bstep (se 2 (by rfl) ⟨120480, by rfl⟩ : syracuseStep 321281 = 240961) B240961
theorem B354071 : Blo 139791 354071 := bstep (se 1 (by rfl) ⟨265553, by rfl⟩ : syracuseStep 354071 = 531107) B531107
theorem B157495 : Blo 139791 157495 := bstep (se 1 (by rfl) ⟨118121, by rfl⟩ : syracuseStep 157495 = 236243) B236243
theorem B813017 : Blo 139791 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B321497 : Blo 139791 321497 := bstep (se 2 (by rfl) ⟨120561, by rfl⟩ : syracuseStep 321497 = 241123) B241123
theorem B157675 : Blo 139791 157675 := bstep (se 1 (by rfl) ⟨118256, by rfl⟩ : syracuseStep 157675 = 236513) B236513
theorem B321587 : Blo 139791 321587 := bstep (se 1 (by rfl) ⟨241190, by rfl⟩ : syracuseStep 321587 = 482381) B482381
theorem B157783 : Blo 139791 157783 := bstep (se 1 (by rfl) ⟨118337, by rfl⟩ : syracuseStep 157783 = 236675) B236675
theorem B321623 : Blo 139791 321623 := bstep (se 1 (by rfl) ⟨241217, by rfl⟩ : syracuseStep 321623 = 482435) B482435
theorem B583811 : Blo 139791 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B288947 : Blo 139791 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B387251 : Blo 139791 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B3106997 : Blo 139791 3106997 := bstep (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) B291281
theorem B157963 : Blo 139791 157963 := bstep (se 1 (by rfl) ⟨118472, by rfl⟩ : syracuseStep 157963 = 236945) B236945
theorem B321803 : Blo 139791 321803 := bstep (se 1 (by rfl) ⟨241352, by rfl⟩ : syracuseStep 321803 = 482705) B482705
theorem B452915 : Blo 139791 452915 := bstep (se 1 (by rfl) ⟨339686, by rfl⟩ : syracuseStep 452915 = 679373) B679373
theorem B321857 : Blo 139791 321857 := bstep (se 2 (by rfl) ⟨120696, by rfl⟩ : syracuseStep 321857 = 241393) B241393
theorem B158071 : Blo 139791 158071 := bstep (se 1 (by rfl) ⟨118553, by rfl⟩ : syracuseStep 158071 = 237107) B237107
theorem B354739 : Blo 139791 354739 := bstep (se 1 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 354739 = 532109) B532109
theorem B453043 : Blo 139791 453043 := bstep (se 1 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 453043 = 679565) B679565
theorem B322073 : Blo 139791 322073 := bstep (se 2 (by rfl) ⟨120777, by rfl⟩ : syracuseStep 322073 = 241555) B241555
theorem B158251 : Blo 139791 158251 := bstep (se 1 (by rfl) ⟨118688, by rfl⟩ : syracuseStep 158251 = 237377) B237377
theorem B354881 : Blo 139791 354881 := bstep (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) B266161
theorem B322163 : Blo 139791 322163 := bstep (se 1 (by rfl) ⟨241622, by rfl⟩ : syracuseStep 322163 = 483245) B483245
theorem B158359 : Blo 139791 158359 := bstep (se 1 (by rfl) ⟨118769, by rfl⟩ : syracuseStep 158359 = 237539) B237539
theorem B322199 : Blo 139791 322199 := bstep (se 1 (by rfl) ⟨241649, by rfl⟩ : syracuseStep 322199 = 483299) B483299
theorem B1076003 : Blo 139791 1076003 := bstep (se 1 (by rfl) ⟨807002, by rfl⟩ : syracuseStep 1076003 = 1614005) B1614005
theorem B158539 : Blo 139791 158539 := bstep (se 1 (by rfl) ⟨118904, by rfl⟩ : syracuseStep 158539 = 237809) B237809
theorem B322379 : Blo 139791 322379 := bstep (se 1 (by rfl) ⟨241784, by rfl⟩ : syracuseStep 322379 = 483569) B483569
theorem B322433 : Blo 139791 322433 := bstep (se 2 (by rfl) ⟨120912, by rfl⟩ : syracuseStep 322433 = 241825) B241825
theorem B158647 : Blo 139791 158647 := bstep (se 1 (by rfl) ⟨118985, by rfl⟩ : syracuseStep 158647 = 237971) B237971
theorem B322649 : Blo 139791 322649 := bstep (se 2 (by rfl) ⟨120993, by rfl⟩ : syracuseStep 322649 = 241987) B241987
theorem B158827 : Blo 139791 158827 := bstep (se 1 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 158827 = 238241) B238241
theorem B224407 : Blo 139791 224407 := bstep (se 1 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 224407 = 336611) B336611
theorem B322739 : Blo 139791 322739 := bstep (se 1 (by rfl) ⟨242054, by rfl⟩ : syracuseStep 322739 = 484109) B484109
theorem B158935 : Blo 139791 158935 := bstep (se 1 (by rfl) ⟨119201, by rfl⟩ : syracuseStep 158935 = 238403) B238403
theorem B322775 : Blo 139791 322775 := bstep (se 1 (by rfl) ⟨242081, by rfl⟩ : syracuseStep 322775 = 484163) B484163
theorem B159115 : Blo 139791 159115 := bstep (se 1 (by rfl) ⟨119336, by rfl⟩ : syracuseStep 159115 = 238673) B238673
theorem B322955 : Blo 139791 322955 := bstep (se 1 (by rfl) ⟨242216, by rfl⟩ : syracuseStep 322955 = 484433) B484433
theorem B323009 : Blo 139791 323009 := bstep (se 2 (by rfl) ⟨121128, by rfl⟩ : syracuseStep 323009 = 242257) B242257
theorem B650713 : Blo 139791 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B159223 : Blo 139791 159223 := bstep (se 1 (by rfl) ⟨119417, by rfl⟩ : syracuseStep 159223 = 238835) B238835
theorem B192025 : Blo 139791 192025 := bstep (se 2 (by rfl) ⟨72009, by rfl⟩ : syracuseStep 192025 = 144019) B144019
theorem B814657 : Blo 139791 814657 := bstep (se 2 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 814657 = 610993) B610993
theorem B912971 : Blo 139791 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B716363 : Blo 139791 716363 := bstep (se 1 (by rfl) ⟨537272, by rfl⟩ : syracuseStep 716363 = 1074545) B1074545
theorem B323225 : Blo 139791 323225 := bstep (se 2 (by rfl) ⟨121209, by rfl⟩ : syracuseStep 323225 = 242419) B242419
theorem B159403 : Blo 139791 159403 := bstep (se 1 (by rfl) ⟨119552, by rfl⟩ : syracuseStep 159403 = 239105) B239105
theorem B323315 : Blo 139791 323315 := bstep (se 1 (by rfl) ⟨242486, by rfl⟩ : syracuseStep 323315 = 484973) B484973
theorem B159511 : Blo 139791 159511 := bstep (se 1 (by rfl) ⟨119633, by rfl⟩ : syracuseStep 159511 = 239267) B239267
theorem B323351 : Blo 139791 323351 := bstep (se 1 (by rfl) ⟨242513, by rfl⟩ : syracuseStep 323351 = 485027) B485027
theorem B356147 : Blo 139791 356147 := bstep (se 1 (by rfl) ⟨267110, by rfl⟩ : syracuseStep 356147 = 534221) B534221
theorem B225227 : Blo 139791 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B159691 : Blo 139791 159691 := bstep (se 1 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 159691 = 239537) B239537
theorem B323531 : Blo 139791 323531 := bstep (se 1 (by rfl) ⟨242648, by rfl⟩ : syracuseStep 323531 = 485297) B485297
theorem B192523 : Blo 139791 192523 := bstep (se 1 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 192523 = 288785) B288785
theorem B159799 : Blo 139791 159799 := bstep (se 1 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 159799 = 239699) B239699
theorem B192587 : Blo 139791 192587 := bstep (se 1 (by rfl) ⟨144440, by rfl⟩ : syracuseStep 192587 = 288881) B288881
theorem B323671 : Blo 139791 323671 := bstep (se 1 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 323671 = 485507) B485507
theorem B225497 : Blo 139791 225497 := bstep (se 2 (by rfl) ⟨84561, by rfl⟩ : syracuseStep 225497 = 169123) B169123
theorem B159979 : Blo 139791 159979 := bstep (se 1 (by rfl) ⟨119984, by rfl⟩ : syracuseStep 159979 = 239969) B239969
theorem B356683 : Blo 139791 356683 := bstep (se 1 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 356683 = 535025) B535025
theorem B160087 : Blo 139791 160087 := bstep (se 1 (by rfl) ⟨120065, by rfl⟩ : syracuseStep 160087 = 240131) B240131
theorem B258391 : Blo 139791 258391 := bstep (se 1 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 258391 = 387587) B387587
theorem B291251 : Blo 139791 291251 := bstep (se 1 (by rfl) ⟨218438, by rfl⟩ : syracuseStep 291251 = 436877) B436877
theorem B356825 : Blo 139791 356825 := bstep (se 2 (by rfl) ⟨133809, by rfl⟩ : syracuseStep 356825 = 267619) B267619
theorem B160267 : Blo 139791 160267 := bstep (se 1 (by rfl) ⟨120200, by rfl⟩ : syracuseStep 160267 = 240401) B240401
theorem B160375 : Blo 139791 160375 := bstep (se 1 (by rfl) ⟨120281, by rfl⟩ : syracuseStep 160375 = 240563) B240563
theorem B881425 : Blo 139791 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B160555 : Blo 139791 160555 := bstep (se 1 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 160555 = 240833) B240833
theorem B324481 : Blo 139791 324481 := bstep (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) B243361
theorem B160663 : Blo 139791 160663 := bstep (se 1 (by rfl) ⟨120497, by rfl⟩ : syracuseStep 160663 = 240995) B240995
theorem B226201 : Blo 139791 226201 := bstep (se 2 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 226201 = 169651) B169651
theorem B914449 : Blo 139791 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B160843 : Blo 139791 160843 := bstep (se 1 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 160843 = 241265) B241265
theorem B160951 : Blo 139791 160951 := bstep (se 1 (by rfl) ⟨120713, by rfl⟩ : syracuseStep 160951 = 241427) B241427
theorem B357655 : Blo 139791 357655 := bstep (se 1 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 357655 = 536483) B536483
theorem B1537325 : Blo 139791 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B718145 : Blo 139791 718145 := bstep (se 2 (by rfl) ⟨269304, by rfl⟩ : syracuseStep 718145 = 538609) B538609
theorem B161131 : Blo 139791 161131 := bstep (se 1 (by rfl) ⟨120848, by rfl⟩ : syracuseStep 161131 = 241697) B241697
theorem B161239 : Blo 139791 161239 := bstep (se 1 (by rfl) ⟨120929, by rfl⟩ : syracuseStep 161239 = 241859) B241859
theorem B1635875 : Blo 139791 1635875 := bstep (se 1 (by rfl) ⟨1226906, by rfl⟩ : syracuseStep 1635875 = 2453813) B2453813
theorem B161419 : Blo 139791 161419 := bstep (se 1 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 161419 = 242129) B242129
theorem B358091 : Blo 139791 358091 := bstep (se 1 (by rfl) ⟨268568, by rfl⟩ : syracuseStep 358091 = 537137) B537137
theorem B161527 : Blo 139791 161527 := bstep (se 1 (by rfl) ⟨121145, by rfl⟩ : syracuseStep 161527 = 242291) B242291
theorem B2094913 : Blo 139791 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B161707 : Blo 139791 161707 := bstep (se 1 (by rfl) ⟨121280, by rfl⟩ : syracuseStep 161707 = 242561) B242561
theorem B358465 : Blo 139791 358465 := bstep (se 2 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 358465 = 268849) B268849
theorem B489665 : Blo 139791 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B260377 : Blo 139791 260377 := bstep (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) B195283
theorem B391475 : Blo 139791 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B653633 : Blo 139791 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B162167 : Blo 139791 162167 := bstep (se 1 (by rfl) ⟨121625, by rfl⟩ : syracuseStep 162167 = 243251) B243251
theorem B359063 : Blo 139791 359063 := bstep (se 1 (by rfl) ⟨269297, by rfl⟩ : syracuseStep 359063 = 538595) B538595
theorem B359129 : Blo 139791 359129 := bstep (se 2 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 359129 = 269347) B269347
theorem B818099 : Blo 139791 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B293977 : Blo 139791 293977 := bstep (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) B220483
theorem B687197 : Blo 139791 687197 := bstep (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) B257699
theorem B720089 : Blo 139791 720089 := bstep (se 2 (by rfl) ⟨270033, by rfl⟩ : syracuseStep 720089 = 540067) B540067
theorem B2489777 : Blo 139791 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B359873 : Blo 139791 359873 := bstep (se 2 (by rfl) ⟨134952, by rfl⟩ : syracuseStep 359873 = 269905) B269905
theorem B3899011 : Blo 139791 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B327347 : Blo 139791 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B3112921 : Blo 139791 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B360409 : Blo 139791 360409 := bstep (se 2 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 360409 = 270307) B270307
theorem B720899 : Blo 139791 720899 := bstep (se 1 (by rfl) ⟨540674, by rfl⟩ : syracuseStep 720899 = 1081349) B1081349
theorem B589853 : Blo 139791 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B229495 : Blo 139791 229495 := bstep (se 1 (by rfl) ⟨172121, by rfl⟩ : syracuseStep 229495 = 344243) B344243
theorem B721133 : Blo 139791 721133 := bstep (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) B270425
theorem B2326877 : Blo 139791 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B885127 : Blo 139791 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B1868579 : Blo 139791 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B361331 : Blo 139791 361331 := bstep (se 1 (by rfl) ⟨270998, by rfl⟩ : syracuseStep 361331 = 541997) B541997
theorem B853021 : Blo 139791 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B361847 : Blo 139791 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B1541699 : Blo 139791 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B722519 : Blo 139791 722519 := bstep (se 1 (by rfl) ⟨541889, by rfl⟩ : syracuseStep 722519 = 1083779) B1083779
theorem B460603 : Blo 139791 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B1542041 : Blo 139791 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B723005 : Blo 139791 723005 := bstep (se 3 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 723005 = 271127) B271127
theorem B755905 : Blo 139791 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B1771721 : Blo 139791 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B1345825 : Blo 139791 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B362839 : Blo 139791 362839 := bstep (se 1 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 362839 = 544259) B544259
theorem B231995 : Blo 139791 231995 := bstep (se 1 (by rfl) ⟨173996, by rfl⟩ : syracuseStep 231995 = 347993) B347993
theorem B363143 : Blo 139791 363143 := bstep (se 1 (by rfl) ⟨272357, by rfl⟩ : syracuseStep 363143 = 544715) B544715
theorem B363275 : Blo 139791 363275 := bstep (se 1 (by rfl) ⟨272456, by rfl⟩ : syracuseStep 363275 = 544913) B544913
theorem B3083123 : Blo 139791 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B363791 : Blo 139791 363791 := bstep (se 1 (by rfl) ⟨272843, by rfl⟩ : syracuseStep 363791 = 545687) B545687
theorem B363809 : Blo 139791 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B265531 : Blo 139791 265531 := bstep (se 1 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 265531 = 398297) B398297
theorem B2035003 : Blo 139791 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B363923 : Blo 139791 363923 := bstep (se 1 (by rfl) ⟨272942, by rfl⟩ : syracuseStep 363923 = 545885) B545885
theorem B757421 : Blo 139791 757421 := bstep (se 3 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 757421 = 284033) B284033
theorem B266017 : Blo 139791 266017 := bstep (se 2 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 266017 = 199513) B199513
theorem B724787 : Blo 139791 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B429943 : Blo 139791 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B1347671 : Blo 139791 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B725111 : Blo 139791 725111 := bstep (se 1 (by rfl) ⟨543833, by rfl⟩ : syracuseStep 725111 = 1087667) B1087667
theorem B299209 : Blo 139791 299209 := bstep (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) B224407
theorem B430451 : Blo 139791 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B201079 : Blo 139791 201079 := bstep (se 1 (by rfl) ⟨150809, by rfl⟩ : syracuseStep 201079 = 301619) B301619
theorem B1151441 : Blo 139791 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B1446365 : Blo 139791 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B1086209 : Blo 139791 1086209 := bstep (se 2 (by rfl) ⟨407328, by rfl⟩ : syracuseStep 1086209 = 814657) B814657
theorem B1643417 : Blo 139791 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B267209 : Blo 139791 267209 := bstep (se 2 (by rfl) ⟨100203, by rfl⟩ : syracuseStep 267209 = 200407) B200407
theorem B758807 : Blo 139791 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B726083 : Blo 139791 726083 := bstep (se 1 (by rfl) ⟨544562, by rfl⟩ : syracuseStep 726083 = 1089125) B1089125
theorem B4658309 : Blo 139791 4658309 := bstep (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) B873433
theorem B201899 : Blo 139791 201899 := bstep (se 1 (by rfl) ⟨151424, by rfl⟩ : syracuseStep 201899 = 302849) B302849
theorem B726407 : Blo 139791 726407 := bstep (se 1 (by rfl) ⟨544805, by rfl⟩ : syracuseStep 726407 = 1089611) B1089611
theorem B431561 : Blo 139791 431561 := bstep (se 2 (by rfl) ⟨161835, by rfl⟩ : syracuseStep 431561 = 323671) B323671
theorem B267923 : Blo 139791 267923 := bstep (se 1 (by rfl) ⟨200942, by rfl⟩ : syracuseStep 267923 = 401885) B401885
theorem B267961 : Blo 139791 267961 := bstep (se 2 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 267961 = 200971) B200971
theorem B300935 : Blo 139791 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B432641 : Blo 139791 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B236047 : Blo 139791 236047 := bstep (se 1 (by rfl) ⟨177035, by rfl⟩ : syracuseStep 236047 = 354071) B354071
theorem B301601 : Blo 139791 301601 := bstep (se 2 (by rfl) ⟨113100, by rfl⟩ : syracuseStep 301601 = 226201) B226201
theorem B203323 : Blo 139791 203323 := bstep (se 1 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 203323 = 304985) B304985
theorem B1219265 : Blo 139791 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B2071331 : Blo 139791 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B301943 : Blo 139791 301943 := bstep (se 1 (by rfl) ⟨226457, by rfl⟩ : syracuseStep 301943 = 452915) B452915
theorem B236587 : Blo 139791 236587 := bstep (se 1 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 236587 = 354881) B354881
theorem B400427 : Blo 139791 400427 := bstep (se 1 (by rfl) ⟨300320, by rfl⟩ : syracuseStep 400427 = 600641) B600641
theorem B236729 : Blo 139791 236729 := bstep (se 2 (by rfl) ⟨88773, by rfl⟩ : syracuseStep 236729 = 177547) B177547
theorem B728605 : Blo 139791 728605 := bstep (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) B273227
theorem B269867 : Blo 139791 269867 := bstep (se 1 (by rfl) ⟨202400, by rfl⟩ : syracuseStep 269867 = 404801) B404801
theorem B2793217 : Blo 139791 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B401213 : Blo 139791 401213 := bstep (se 3 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 401213 = 150455) B150455
theorem B237431 : Blo 139791 237431 := bstep (se 1 (by rfl) ⟨178073, by rfl⟩ : syracuseStep 237431 = 356147) B356147
theorem B401543 : Blo 139791 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B237883 : Blo 139791 237883 := bstep (se 1 (by rfl) ⟨178412, by rfl⟩ : syracuseStep 237883 = 356825) B356825
theorem B2171281 : Blo 139791 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B238025 : Blo 139791 238025 := bstep (se 2 (by rfl) ⟨89259, by rfl⟩ : syracuseStep 238025 = 178519) B178519
theorem B270793 : Blo 139791 270793 := bstep (se 2 (by rfl) ⟨101547, by rfl⟩ : syracuseStep 270793 = 203095) B203095
theorem B139791 : Blo 139791 139791 := bstep (se 1 (by rfl) ⟨104843, by rfl⟩ : syracuseStep 139791 = 209687) B209687
theorem B139835 : Blo 139791 139835 := bstep (se 1 (by rfl) ⟨104876, by rfl⟩ : syracuseStep 139835 = 209753) B209753
theorem B139911 : Blo 139791 139911 := bstep (se 1 (by rfl) ⟨104933, by rfl⟩ : syracuseStep 139911 = 209867) B209867
theorem B139919 : Blo 139791 139919 := bstep (se 1 (by rfl) ⟨104939, by rfl⟩ : syracuseStep 139919 = 209879) B209879
theorem B139963 : Blo 139791 139963 := bstep (se 1 (by rfl) ⟨104972, by rfl⟩ : syracuseStep 139963 = 209945) B209945
theorem B533249 : Blo 139791 533249 := bstep (se 2 (by rfl) ⟨199968, by rfl⟩ : syracuseStep 533249 = 399937) B399937
theorem B140039 : Blo 139791 140039 := bstep (se 1 (by rfl) ⟨105029, by rfl⟩ : syracuseStep 140039 = 210059) B210059
theorem B140047 : Blo 139791 140047 := bstep (se 1 (by rfl) ⟨105035, by rfl⟩ : syracuseStep 140047 = 210071) B210071
theorem B533263 : Blo 139791 533263 := bstep (se 1 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 533263 = 799895) B799895
theorem B140091 : Blo 139791 140091 := bstep (se 1 (by rfl) ⟨105068, by rfl⟩ : syracuseStep 140091 = 210137) B210137
theorem B1024883 : Blo 139791 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B140167 : Blo 139791 140167 := bstep (se 1 (by rfl) ⟨105125, by rfl⟩ : syracuseStep 140167 = 210251) B210251
theorem B140175 : Blo 139791 140175 := bstep (se 1 (by rfl) ⟨105131, by rfl⟩ : syracuseStep 140175 = 210263) B210263
theorem B140219 : Blo 139791 140219 := bstep (se 1 (by rfl) ⟨105164, by rfl⟩ : syracuseStep 140219 = 210329) B210329
theorem B140295 : Blo 139791 140295 := bstep (se 1 (by rfl) ⟨105221, by rfl⟩ : syracuseStep 140295 = 210443) B210443
theorem B140303 : Blo 139791 140303 := bstep (se 1 (by rfl) ⟨105227, by rfl⟩ : syracuseStep 140303 = 210455) B210455
theorem B1090583 : Blo 139791 1090583 := bstep (se 1 (by rfl) ⟨817937, by rfl⟩ : syracuseStep 1090583 = 1635875) B1635875
theorem B140347 : Blo 139791 140347 := bstep (se 1 (by rfl) ⟨105260, by rfl⟩ : syracuseStep 140347 = 210521) B210521
theorem B664643 : Blo 139791 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B140423 : Blo 139791 140423 := bstep (se 1 (by rfl) ⟨105317, by rfl⟩ : syracuseStep 140423 = 210635) B210635
theorem B238727 : Blo 139791 238727 := bstep (se 1 (by rfl) ⟨179045, by rfl⟩ : syracuseStep 238727 = 358091) B358091
theorem B140431 : Blo 139791 140431 := bstep (se 1 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 140431 = 210647) B210647
theorem B271507 : Blo 139791 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B140475 : Blo 139791 140475 := bstep (se 1 (by rfl) ⟨105356, by rfl⟩ : syracuseStep 140475 = 210713) B210713
theorem B140551 : Blo 139791 140551 := bstep (se 1 (by rfl) ⟨105413, by rfl⟩ : syracuseStep 140551 = 210827) B210827
theorem B140559 : Blo 139791 140559 := bstep (se 1 (by rfl) ⟨105419, by rfl⟩ : syracuseStep 140559 = 210839) B210839
theorem B140603 : Blo 139791 140603 := bstep (se 1 (by rfl) ⟨105452, by rfl⟩ : syracuseStep 140603 = 210905) B210905
theorem B140679 : Blo 139791 140679 := bstep (se 1 (by rfl) ⟨105509, by rfl⟩ : syracuseStep 140679 = 211019) B211019
theorem B140687 : Blo 139791 140687 := bstep (se 1 (by rfl) ⟨105515, by rfl⟩ : syracuseStep 140687 = 211031) B211031
theorem B140731 : Blo 139791 140731 := bstep (se 1 (by rfl) ⟨105548, by rfl⟩ : syracuseStep 140731 = 211097) B211097
theorem B140807 : Blo 139791 140807 := bstep (se 1 (by rfl) ⟨105605, by rfl⟩ : syracuseStep 140807 = 211211) B211211
theorem B140815 : Blo 139791 140815 := bstep (se 1 (by rfl) ⟨105611, by rfl⟩ : syracuseStep 140815 = 211223) B211223
theorem B435755 : Blo 139791 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B140859 : Blo 139791 140859 := bstep (se 1 (by rfl) ⟨105644, by rfl⟩ : syracuseStep 140859 = 211289) B211289
theorem B140935 : Blo 139791 140935 := bstep (se 1 (by rfl) ⟨105701, by rfl⟩ : syracuseStep 140935 = 211403) B211403
theorem B140943 : Blo 139791 140943 := bstep (se 1 (by rfl) ⟨105707, by rfl⟩ : syracuseStep 140943 = 211415) B211415
theorem B140987 : Blo 139791 140987 := bstep (se 1 (by rfl) ⟨105740, by rfl⟩ : syracuseStep 140987 = 211481) B211481
theorem B141063 : Blo 139791 141063 := bstep (se 1 (by rfl) ⟨105797, by rfl⟩ : syracuseStep 141063 = 211595) B211595
theorem B337679 : Blo 139791 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B141071 : Blo 139791 141071 := bstep (se 1 (by rfl) ⟨105803, by rfl⟩ : syracuseStep 141071 = 211607) B211607
theorem B239375 : Blo 139791 239375 := bstep (se 1 (by rfl) ⟨179531, by rfl⟩ : syracuseStep 239375 = 359063) B359063
theorem B239419 : Blo 139791 239419 := bstep (se 1 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 239419 = 359129) B359129
theorem B141115 : Blo 139791 141115 := bstep (se 1 (by rfl) ⟨105836, by rfl⟩ : syracuseStep 141115 = 211673) B211673
theorem B403319 : Blo 139791 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B141191 : Blo 139791 141191 := bstep (se 1 (by rfl) ⟨105893, by rfl⟩ : syracuseStep 141191 = 211787) B211787
theorem B141199 : Blo 139791 141199 := bstep (se 1 (by rfl) ⟨105899, by rfl⟩ : syracuseStep 141199 = 211799) B211799
theorem B141243 : Blo 139791 141243 := bstep (se 1 (by rfl) ⟨105932, by rfl⟩ : syracuseStep 141243 = 211865) B211865
theorem B11610053 : Blo 139791 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B141319 : Blo 139791 141319 := bstep (se 1 (by rfl) ⟨105989, by rfl⟩ : syracuseStep 141319 = 211979) B211979
theorem B534539 : Blo 139791 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B141327 : Blo 139791 141327 := bstep (se 1 (by rfl) ⟨105995, by rfl⟩ : syracuseStep 141327 = 211991) B211991
theorem B141371 : Blo 139791 141371 := bstep (se 1 (by rfl) ⟨106028, by rfl⟩ : syracuseStep 141371 = 212057) B212057
theorem B141447 : Blo 139791 141447 := bstep (se 1 (by rfl) ⟨106085, by rfl⟩ : syracuseStep 141447 = 212171) B212171
theorem B141455 : Blo 139791 141455 := bstep (se 1 (by rfl) ⟨106091, by rfl⟩ : syracuseStep 141455 = 212183) B212183
theorem B141499 : Blo 139791 141499 := bstep (se 1 (by rfl) ⟨106124, by rfl⟩ : syracuseStep 141499 = 212249) B212249
theorem B272585 : Blo 139791 272585 := bstep (se 2 (by rfl) ⟨102219, by rfl⟩ : syracuseStep 272585 = 204439) B204439
theorem B141575 : Blo 139791 141575 := bstep (se 1 (by rfl) ⟨106181, by rfl⟩ : syracuseStep 141575 = 212363) B212363
theorem B141583 : Blo 139791 141583 := bstep (se 1 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 141583 = 212375) B212375
theorem B239915 : Blo 139791 239915 := bstep (se 1 (by rfl) ⟨179936, by rfl⟩ : syracuseStep 239915 = 359873) B359873
theorem B796979 : Blo 139791 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B141627 : Blo 139791 141627 := bstep (se 1 (by rfl) ⟨106220, by rfl⟩ : syracuseStep 141627 = 212441) B212441
theorem B141703 : Blo 139791 141703 := bstep (se 1 (by rfl) ⟨106277, by rfl⟩ : syracuseStep 141703 = 212555) B212555
theorem B141711 : Blo 139791 141711 := bstep (se 1 (by rfl) ⟨106283, by rfl⟩ : syracuseStep 141711 = 212567) B212567
theorem B141755 : Blo 139791 141755 := bstep (se 1 (by rfl) ⟨106316, by rfl⟩ : syracuseStep 141755 = 212633) B212633
theorem B141831 : Blo 139791 141831 := bstep (se 1 (by rfl) ⟨106373, by rfl⟩ : syracuseStep 141831 = 212747) B212747
theorem B141839 : Blo 139791 141839 := bstep (se 1 (by rfl) ⟨106379, by rfl⟩ : syracuseStep 141839 = 212759) B212759
theorem B600605 : Blo 139791 600605 := bstep (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) B225227
theorem B141883 : Blo 139791 141883 := bstep (se 1 (by rfl) ⟨106412, by rfl⟩ : syracuseStep 141883 = 212825) B212825
theorem B141959 : Blo 139791 141959 := bstep (se 1 (by rfl) ⟨106469, by rfl⟩ : syracuseStep 141959 = 212939) B212939
theorem B141967 : Blo 139791 141967 := bstep (se 1 (by rfl) ⟨106475, by rfl⟩ : syracuseStep 141967 = 212951) B212951
theorem B240313 : Blo 139791 240313 := bstep (se 2 (by rfl) ⟨90117, by rfl⟩ : syracuseStep 240313 = 180235) B180235
theorem B142011 : Blo 139791 142011 := bstep (se 1 (by rfl) ⟨106508, by rfl⟩ : syracuseStep 142011 = 213017) B213017
theorem B142087 : Blo 139791 142087 := bstep (se 1 (by rfl) ⟨106565, by rfl⟩ : syracuseStep 142087 = 213131) B213131
theorem B142095 : Blo 139791 142095 := bstep (se 1 (by rfl) ⟨106571, by rfl⟩ : syracuseStep 142095 = 213143) B213143
theorem B142139 : Blo 139791 142139 := bstep (se 1 (by rfl) ⟨106604, by rfl⟩ : syracuseStep 142139 = 213209) B213209
theorem B404311 : Blo 139791 404311 := bstep (se 1 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 404311 = 606467) B606467
theorem B142215 : Blo 139791 142215 := bstep (se 1 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 142215 = 213323) B213323
theorem B142223 : Blo 139791 142223 := bstep (se 1 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 142223 = 213335) B213335
theorem B535481 : Blo 139791 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B142267 : Blo 139791 142267 := bstep (se 1 (by rfl) ⟨106700, by rfl⟩ : syracuseStep 142267 = 213401) B213401
theorem B142343 : Blo 139791 142343 := bstep (se 1 (by rfl) ⟨106757, by rfl⟩ : syracuseStep 142343 = 213515) B213515
theorem B142351 : Blo 139791 142351 := bstep (se 1 (by rfl) ⟨106763, by rfl⟩ : syracuseStep 142351 = 213527) B213527
theorem B142395 : Blo 139791 142395 := bstep (se 1 (by rfl) ⟨106796, by rfl⟩ : syracuseStep 142395 = 213593) B213593
theorem B699479 : Blo 139791 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B142471 : Blo 139791 142471 := bstep (se 1 (by rfl) ⟨106853, by rfl⟩ : syracuseStep 142471 = 213707) B213707
theorem B142479 : Blo 139791 142479 := bstep (se 1 (by rfl) ⟨106859, by rfl⟩ : syracuseStep 142479 = 213719) B213719
theorem B142523 : Blo 139791 142523 := bstep (se 1 (by rfl) ⟨106892, by rfl⟩ : syracuseStep 142523 = 213785) B213785
theorem B601289 : Blo 139791 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B142599 : Blo 139791 142599 := bstep (se 1 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 142599 = 213899) B213899
theorem B142607 : Blo 139791 142607 := bstep (se 1 (by rfl) ⟨106955, by rfl⟩ : syracuseStep 142607 = 213911) B213911
theorem B142651 : Blo 139791 142651 := bstep (se 1 (by rfl) ⟨106988, by rfl⟩ : syracuseStep 142651 = 213977) B213977
theorem B241015 : Blo 139791 241015 := bstep (se 1 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 241015 = 361523) B361523
theorem B142727 : Blo 139791 142727 := bstep (se 1 (by rfl) ⟨107045, by rfl⟩ : syracuseStep 142727 = 214091) B214091
theorem B142735 : Blo 139791 142735 := bstep (se 1 (by rfl) ⟨107051, by rfl⟩ : syracuseStep 142735 = 214103) B214103
theorem B142779 : Blo 139791 142779 := bstep (se 1 (by rfl) ⟨107084, by rfl⟩ : syracuseStep 142779 = 214169) B214169
theorem B142855 : Blo 139791 142855 := bstep (se 1 (by rfl) ⟨107141, by rfl⟩ : syracuseStep 142855 = 214283) B214283
theorem B142863 : Blo 139791 142863 := bstep (se 1 (by rfl) ⟨107147, by rfl⟩ : syracuseStep 142863 = 214295) B214295
theorem B142907 : Blo 139791 142907 := bstep (se 1 (by rfl) ⟨107180, by rfl⟩ : syracuseStep 142907 = 214361) B214361
theorem B241211 : Blo 139791 241211 := bstep (se 1 (by rfl) ⟨180908, by rfl⟩ : syracuseStep 241211 = 361817) B361817
theorem B896579 : Blo 139791 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B142983 : Blo 139791 142983 := bstep (se 1 (by rfl) ⟨107237, by rfl⟩ : syracuseStep 142983 = 214475) B214475
theorem B142991 : Blo 139791 142991 := bstep (se 1 (by rfl) ⟨107243, by rfl⟩ : syracuseStep 142991 = 214487) B214487
theorem B143035 : Blo 139791 143035 := bstep (se 1 (by rfl) ⟨107276, by rfl⟩ : syracuseStep 143035 = 214553) B214553
theorem B798437 : Blo 139791 798437 := bstep (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) B149707
theorem B143111 : Blo 139791 143111 := bstep (se 1 (by rfl) ⟨107333, by rfl⟩ : syracuseStep 143111 = 214667) B214667
theorem B143119 : Blo 139791 143119 := bstep (se 1 (by rfl) ⟨107339, by rfl⟩ : syracuseStep 143119 = 214679) B214679
theorem B143163 : Blo 139791 143163 := bstep (se 1 (by rfl) ⟨107372, by rfl⟩ : syracuseStep 143163 = 214745) B214745
theorem B143239 : Blo 139791 143239 := bstep (se 1 (by rfl) ⟨107429, by rfl⟩ : syracuseStep 143239 = 214859) B214859
theorem B143247 : Blo 139791 143247 := bstep (se 1 (by rfl) ⟨107435, by rfl⟩ : syracuseStep 143247 = 214871) B214871
theorem B143291 : Blo 139791 143291 := bstep (se 1 (by rfl) ⟨107468, by rfl⟩ : syracuseStep 143291 = 214937) B214937
theorem B241609 : Blo 139791 241609 := bstep (se 2 (by rfl) ⟨90603, by rfl⟩ : syracuseStep 241609 = 181207) B181207
theorem B143367 : Blo 139791 143367 := bstep (se 1 (by rfl) ⟨107525, by rfl⟩ : syracuseStep 143367 = 215051) B215051
theorem B143375 : Blo 139791 143375 := bstep (se 1 (by rfl) ⟨107531, by rfl⟩ : syracuseStep 143375 = 215063) B215063
theorem B143419 : Blo 139791 143419 := bstep (se 1 (by rfl) ⟨107564, by rfl⟩ : syracuseStep 143419 = 215129) B215129
theorem B1388677 : Blo 139791 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B143495 : Blo 139791 143495 := bstep (se 1 (by rfl) ⟨107621, by rfl⟩ : syracuseStep 143495 = 215243) B215243
theorem B143503 : Blo 139791 143503 := bstep (se 1 (by rfl) ⟨107627, by rfl⟩ : syracuseStep 143503 = 215255) B215255
theorem B798893 : Blo 139791 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B143547 : Blo 139791 143547 := bstep (se 1 (by rfl) ⟨107660, by rfl⟩ : syracuseStep 143547 = 215321) B215321
theorem B143623 : Blo 139791 143623 := bstep (se 1 (by rfl) ⟨107717, by rfl⟩ : syracuseStep 143623 = 215435) B215435
theorem B143631 : Blo 139791 143631 := bstep (se 1 (by rfl) ⟨107723, by rfl⟩ : syracuseStep 143631 = 215447) B215447
theorem B405803 : Blo 139791 405803 := bstep (se 1 (by rfl) ⟨304352, by rfl⟩ : syracuseStep 405803 = 608705) B608705
theorem B143675 : Blo 139791 143675 := bstep (se 1 (by rfl) ⟨107756, by rfl⟩ : syracuseStep 143675 = 215513) B215513
theorem B143751 : Blo 139791 143751 := bstep (se 1 (by rfl) ⟨107813, by rfl⟩ : syracuseStep 143751 = 215627) B215627
theorem B143759 : Blo 139791 143759 := bstep (se 1 (by rfl) ⟨107819, by rfl⟩ : syracuseStep 143759 = 215639) B215639
theorem B569753 : Blo 139791 569753 := bstep (se 2 (by rfl) ⟨213657, by rfl⟩ : syracuseStep 569753 = 427315) B427315
theorem B307727 : Blo 139791 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B242311 : Blo 139791 242311 := bstep (se 1 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 242311 = 363467) B363467
theorem B209723 : Blo 139791 209723 := bstep (se 1 (by rfl) ⟨157292, by rfl⟩ : syracuseStep 209723 = 314585) B314585
theorem B799577 : Blo 139791 799577 := bstep (se 2 (by rfl) ⟨299841, by rfl⟩ : syracuseStep 799577 = 599683) B599683
theorem B209783 : Blo 139791 209783 := bstep (se 1 (by rfl) ⟨157337, by rfl⟩ : syracuseStep 209783 = 314675) B314675
theorem B209807 : Blo 139791 209807 := bstep (se 1 (by rfl) ⟨157355, by rfl⟩ : syracuseStep 209807 = 314711) B314711
theorem B209849 : Blo 139791 209849 := bstep (se 2 (by rfl) ⟨78693, by rfl⟩ : syracuseStep 209849 = 157387) B157387
theorem B603065 : Blo 139791 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B209927 : Blo 139791 209927 := bstep (se 1 (by rfl) ⟨157445, by rfl⟩ : syracuseStep 209927 = 314891) B314891
theorem B177167 : Blo 139791 177167 := bstep (se 1 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 177167 = 265751) B265751
theorem B406561 : Blo 139791 406561 := bstep (se 2 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 406561 = 304921) B304921
theorem B209963 : Blo 139791 209963 := bstep (se 1 (by rfl) ⟨157472, by rfl⟩ : syracuseStep 209963 = 314945) B314945
theorem B209993 : Blo 139791 209993 := bstep (se 2 (by rfl) ⟨78747, by rfl⟩ : syracuseStep 209993 = 157495) B157495
theorem B210107 : Blo 139791 210107 := bstep (se 1 (by rfl) ⟨157580, by rfl⟩ : syracuseStep 210107 = 315161) B315161
theorem B210167 : Blo 139791 210167 := bstep (se 1 (by rfl) ⟨157625, by rfl⟩ : syracuseStep 210167 = 315251) B315251
theorem B210191 : Blo 139791 210191 := bstep (se 1 (by rfl) ⟨157643, by rfl⟩ : syracuseStep 210191 = 315287) B315287
theorem B341263 : Blo 139791 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B210233 : Blo 139791 210233 := bstep (se 2 (by rfl) ⟨78837, by rfl⟩ : syracuseStep 210233 = 157675) B157675
theorem B210311 : Blo 139791 210311 := bstep (se 1 (by rfl) ⟨157733, by rfl⟩ : syracuseStep 210311 = 315467) B315467
theorem B406919 : Blo 139791 406919 := bstep (se 1 (by rfl) ⟨305189, by rfl⟩ : syracuseStep 406919 = 610379) B610379
theorem B210347 : Blo 139791 210347 := bstep (se 1 (by rfl) ⟨157760, by rfl⟩ : syracuseStep 210347 = 315521) B315521
theorem B210377 : Blo 139791 210377 := bstep (se 2 (by rfl) ⟨78891, by rfl⟩ : syracuseStep 210377 = 157783) B157783
theorem B538123 : Blo 139791 538123 := bstep (se 1 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 538123 = 807185) B807185
theorem B210491 : Blo 139791 210491 := bstep (se 1 (by rfl) ⟨157868, by rfl⟩ : syracuseStep 210491 = 315737) B315737
theorem B407101 : Blo 139791 407101 := bstep (se 3 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 407101 = 152663) B152663
theorem B210551 : Blo 139791 210551 := bstep (se 1 (by rfl) ⟨157913, by rfl⟩ : syracuseStep 210551 = 315827) B315827
theorem B308855 : Blo 139791 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B210575 : Blo 139791 210575 := bstep (se 1 (by rfl) ⟨157931, by rfl⟩ : syracuseStep 210575 = 315863) B315863
theorem B210617 : Blo 139791 210617 := bstep (se 2 (by rfl) ⟨78981, by rfl⟩ : syracuseStep 210617 = 157963) B157963
theorem B210695 : Blo 139791 210695 := bstep (se 1 (by rfl) ⟨158021, by rfl⟩ : syracuseStep 210695 = 316043) B316043
theorem B210731 : Blo 139791 210731 := bstep (se 1 (by rfl) ⟨158048, by rfl⟩ : syracuseStep 210731 = 316097) B316097
theorem B538427 : Blo 139791 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B210761 : Blo 139791 210761 := bstep (se 2 (by rfl) ⟨79035, by rfl⟩ : syracuseStep 210761 = 158071) B158071
theorem B407443 : Blo 139791 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B472985 : Blo 139791 472985 := bstep (se 2 (by rfl) ⟨177369, by rfl⟩ : syracuseStep 472985 = 354739) B354739
theorem B604057 : Blo 139791 604057 := bstep (se 2 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 604057 = 453043) B453043
theorem B210875 : Blo 139791 210875 := bstep (se 1 (by rfl) ⟨158156, by rfl⟩ : syracuseStep 210875 = 316313) B316313
theorem B210935 : Blo 139791 210935 := bstep (se 1 (by rfl) ⟨158201, by rfl⟩ : syracuseStep 210935 = 316403) B316403
theorem B210959 : Blo 139791 210959 := bstep (se 1 (by rfl) ⟨158219, by rfl⟩ : syracuseStep 210959 = 316439) B316439
theorem B211001 : Blo 139791 211001 := bstep (se 2 (by rfl) ⟨79125, by rfl⟩ : syracuseStep 211001 = 158251) B158251
theorem B1620101 : Blo 139791 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B211079 : Blo 139791 211079 := bstep (se 1 (by rfl) ⟨158309, by rfl⟩ : syracuseStep 211079 = 316619) B316619
theorem B211115 : Blo 139791 211115 := bstep (se 1 (by rfl) ⟨158336, by rfl⟩ : syracuseStep 211115 = 316673) B316673
theorem B211145 : Blo 139791 211145 := bstep (se 2 (by rfl) ⟨79179, by rfl⟩ : syracuseStep 211145 = 158359) B158359
theorem B538913 : Blo 139791 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B211259 : Blo 139791 211259 := bstep (se 1 (by rfl) ⟨158444, by rfl⟩ : syracuseStep 211259 = 316889) B316889
theorem B211319 : Blo 139791 211319 := bstep (se 1 (by rfl) ⟨158489, by rfl⟩ : syracuseStep 211319 = 316979) B316979
theorem B211343 : Blo 139791 211343 := bstep (se 1 (by rfl) ⟨158507, by rfl⟩ : syracuseStep 211343 = 317015) B317015
theorem B211385 : Blo 139791 211385 := bstep (se 2 (by rfl) ⟨79269, by rfl⟩ : syracuseStep 211385 = 158539) B158539
theorem B4143581 : Blo 139791 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B211463 : Blo 139791 211463 := bstep (se 1 (by rfl) ⟨158597, by rfl⟩ : syracuseStep 211463 = 317195) B317195
theorem B211499 : Blo 139791 211499 := bstep (se 1 (by rfl) ⟨158624, by rfl⟩ : syracuseStep 211499 = 317249) B317249
theorem B211529 : Blo 139791 211529 := bstep (se 2 (by rfl) ⟨79323, by rfl⟩ : syracuseStep 211529 = 158647) B158647
theorem B473687 : Blo 139791 473687 := bstep (se 1 (by rfl) ⟨355265, by rfl⟩ : syracuseStep 473687 = 710531) B710531
theorem B211643 : Blo 139791 211643 := bstep (se 1 (by rfl) ⟨158732, by rfl⟩ : syracuseStep 211643 = 317465) B317465
theorem B211703 : Blo 139791 211703 := bstep (se 1 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 211703 = 317555) B317555
theorem B408331 : Blo 139791 408331 := bstep (se 1 (by rfl) ⟨306248, by rfl⟩ : syracuseStep 408331 = 612497) B612497
theorem B211727 : Blo 139791 211727 := bstep (se 1 (by rfl) ⟨158795, by rfl⟩ : syracuseStep 211727 = 317591) B317591
theorem B211769 : Blo 139791 211769 := bstep (se 2 (by rfl) ⟨79413, by rfl⟩ : syracuseStep 211769 = 158827) B158827
theorem B1522547 : Blo 139791 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B211847 : Blo 139791 211847 := bstep (se 1 (by rfl) ⟨158885, by rfl⟩ : syracuseStep 211847 = 317771) B317771
theorem B211883 : Blo 139791 211883 := bstep (se 1 (by rfl) ⟨158912, by rfl⟩ : syracuseStep 211883 = 317825) B317825
theorem B211913 : Blo 139791 211913 := bstep (se 2 (by rfl) ⟨79467, by rfl⟩ : syracuseStep 211913 = 158935) B158935
theorem B1358795 : Blo 139791 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B212027 : Blo 139791 212027 := bstep (se 1 (by rfl) ⟨159020, by rfl⟩ : syracuseStep 212027 = 318041) B318041
theorem B474173 : Blo 139791 474173 := bstep (se 3 (by rfl) ⟨88907, by rfl⟩ : syracuseStep 474173 = 177815) B177815
theorem B212087 : Blo 139791 212087 := bstep (se 1 (by rfl) ⟨159065, by rfl⟩ : syracuseStep 212087 = 318131) B318131
theorem B212111 : Blo 139791 212111 := bstep (se 1 (by rfl) ⟨159083, by rfl⟩ : syracuseStep 212111 = 318167) B318167
theorem B212153 : Blo 139791 212153 := bstep (se 2 (by rfl) ⟨79557, by rfl⟩ : syracuseStep 212153 = 159115) B159115
theorem B277705 : Blo 139791 277705 := bstep (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) B208279
theorem B539885 : Blo 139791 539885 := bstep (se 3 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 539885 = 202457) B202457
theorem B408833 : Blo 139791 408833 := bstep (se 2 (by rfl) ⟨153312, by rfl⟩ : syracuseStep 408833 = 306625) B306625
theorem B212231 : Blo 139791 212231 := bstep (se 1 (by rfl) ⟨159173, by rfl⟩ : syracuseStep 212231 = 318347) B318347
theorem B867617 : Blo 139791 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B212267 : Blo 139791 212267 := bstep (se 1 (by rfl) ⟨159200, by rfl⟩ : syracuseStep 212267 = 318401) B318401
theorem B212297 : Blo 139791 212297 := bstep (se 2 (by rfl) ⟨79611, by rfl⟩ : syracuseStep 212297 = 159223) B159223
theorem B900497 : Blo 139791 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B1064339 : Blo 139791 1064339 := bstep (se 1 (by rfl) ⟨798254, by rfl⟩ : syracuseStep 1064339 = 1596509) B1596509
theorem B671129 : Blo 139791 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B212411 : Blo 139791 212411 := bstep (se 1 (by rfl) ⟨159308, by rfl⟩ : syracuseStep 212411 = 318617) B318617
theorem B212471 : Blo 139791 212471 := bstep (se 1 (by rfl) ⟨159353, by rfl⟩ : syracuseStep 212471 = 318707) B318707
theorem B212495 : Blo 139791 212495 := bstep (se 1 (by rfl) ⟨159371, by rfl⟩ : syracuseStep 212495 = 318743) B318743
theorem B212537 : Blo 139791 212537 := bstep (se 2 (by rfl) ⟨79701, by rfl⟩ : syracuseStep 212537 = 159403) B159403
theorem B409175 : Blo 139791 409175 := bstep (se 1 (by rfl) ⟨306881, by rfl⟩ : syracuseStep 409175 = 613763) B613763
theorem B212615 : Blo 139791 212615 := bstep (se 1 (by rfl) ⟨159461, by rfl⟩ : syracuseStep 212615 = 318923) B318923
theorem B212651 : Blo 139791 212651 := bstep (se 1 (by rfl) ⟨159488, by rfl⟩ : syracuseStep 212651 = 318977) B318977
theorem B212681 : Blo 139791 212681 := bstep (se 2 (by rfl) ⟨79755, by rfl⟩ : syracuseStep 212681 = 159511) B159511
theorem B179975 : Blo 139791 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B212795 : Blo 139791 212795 := bstep (se 1 (by rfl) ⟨159596, by rfl⟩ : syracuseStep 212795 = 319193) B319193
theorem B212855 : Blo 139791 212855 := bstep (se 1 (by rfl) ⟨159641, by rfl⟩ : syracuseStep 212855 = 319283) B319283
theorem B212879 : Blo 139791 212879 := bstep (se 1 (by rfl) ⟨159659, by rfl⟩ : syracuseStep 212879 = 319319) B319319
theorem B638873 : Blo 139791 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B180139 : Blo 139791 180139 := bstep (se 1 (by rfl) ⟨135104, by rfl⟩ : syracuseStep 180139 = 270209) B270209
theorem B212921 : Blo 139791 212921 := bstep (se 2 (by rfl) ⟨79845, by rfl⟩ : syracuseStep 212921 = 159691) B159691
theorem B212999 : Blo 139791 212999 := bstep (se 1 (by rfl) ⟨159749, by rfl⟩ : syracuseStep 212999 = 319499) B319499
theorem B213035 : Blo 139791 213035 := bstep (se 1 (by rfl) ⟨159776, by rfl⟩ : syracuseStep 213035 = 319553) B319553
theorem B213065 : Blo 139791 213065 := bstep (se 2 (by rfl) ⟨79899, by rfl⟩ : syracuseStep 213065 = 159799) B159799
theorem B409747 : Blo 139791 409747 := bstep (se 1 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 409747 = 614621) B614621
theorem B213179 : Blo 139791 213179 := bstep (se 1 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 213179 = 319769) B319769
theorem B213239 : Blo 139791 213239 := bstep (se 1 (by rfl) ⟨159929, by rfl⟩ : syracuseStep 213239 = 319859) B319859
theorem B213263 : Blo 139791 213263 := bstep (se 1 (by rfl) ⟨159947, by rfl⟩ : syracuseStep 213263 = 319895) B319895
theorem B213305 : Blo 139791 213305 := bstep (se 2 (by rfl) ⟨79989, by rfl⟩ : syracuseStep 213305 = 159979) B159979
theorem B213383 : Blo 139791 213383 := bstep (se 1 (by rfl) ⟨160037, by rfl⟩ : syracuseStep 213383 = 320075) B320075
theorem B901523 : Blo 139791 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B213419 : Blo 139791 213419 := bstep (se 1 (by rfl) ⟨160064, by rfl⟩ : syracuseStep 213419 = 320129) B320129
theorem B475577 : Blo 139791 475577 := bstep (se 2 (by rfl) ⟨178341, by rfl⟩ : syracuseStep 475577 = 356683) B356683
theorem B213449 : Blo 139791 213449 := bstep (se 2 (by rfl) ⟨80043, by rfl⟩ : syracuseStep 213449 = 160087) B160087
theorem B344521 : Blo 139791 344521 := bstep (se 2 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 344521 = 258391) B258391
theorem B573905 : Blo 139791 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B213563 : Blo 139791 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B213623 : Blo 139791 213623 := bstep (se 1 (by rfl) ⟨160217, by rfl⟩ : syracuseStep 213623 = 320435) B320435
theorem B213647 : Blo 139791 213647 := bstep (se 1 (by rfl) ⟨160235, by rfl⟩ : syracuseStep 213647 = 320471) B320471
theorem B213689 : Blo 139791 213689 := bstep (se 2 (by rfl) ⟨80133, by rfl⟩ : syracuseStep 213689 = 160267) B160267
theorem B213767 : Blo 139791 213767 := bstep (se 1 (by rfl) ⟨160325, by rfl⟩ : syracuseStep 213767 = 320651) B320651
theorem B213803 : Blo 139791 213803 := bstep (se 1 (by rfl) ⟨160352, by rfl⟩ : syracuseStep 213803 = 320705) B320705
theorem B770867 : Blo 139791 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B213833 : Blo 139791 213833 := bstep (se 2 (by rfl) ⟨80187, by rfl⟩ : syracuseStep 213833 = 160375) B160375
theorem B181111 : Blo 139791 181111 := bstep (se 1 (by rfl) ⟨135833, by rfl⟩ : syracuseStep 181111 = 271667) B271667
theorem B213947 : Blo 139791 213947 := bstep (se 1 (by rfl) ⟨160460, by rfl⟩ : syracuseStep 213947 = 320921) B320921
theorem B214007 : Blo 139791 214007 := bstep (se 1 (by rfl) ⟨160505, by rfl⟩ : syracuseStep 214007 = 321011) B321011
theorem B476171 : Blo 139791 476171 := bstep (se 1 (by rfl) ⟨357128, by rfl⟩ : syracuseStep 476171 = 714257) B714257
theorem B214031 : Blo 139791 214031 := bstep (se 1 (by rfl) ⟨160523, by rfl⟩ : syracuseStep 214031 = 321047) B321047
theorem B214073 : Blo 139791 214073 := bstep (se 2 (by rfl) ⟨80277, by rfl⟩ : syracuseStep 214073 = 160555) B160555
theorem B476279 : Blo 139791 476279 := bstep (se 1 (by rfl) ⟨357209, by rfl⟩ : syracuseStep 476279 = 714419) B714419
theorem B214151 : Blo 139791 214151 := bstep (se 1 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 214151 = 321227) B321227
theorem B214187 : Blo 139791 214187 := bstep (se 1 (by rfl) ⟨160640, by rfl⟩ : syracuseStep 214187 = 321281) B321281
theorem B181435 : Blo 139791 181435 := bstep (se 1 (by rfl) ⟨136076, by rfl⟩ : syracuseStep 181435 = 272153) B272153
theorem B214217 : Blo 139791 214217 := bstep (se 2 (by rfl) ⟨80331, by rfl⟩ : syracuseStep 214217 = 160663) B160663
theorem B542011 : Blo 139791 542011 := bstep (se 1 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 542011 = 813017) B813017
theorem B214331 : Blo 139791 214331 := bstep (se 1 (by rfl) ⟨160748, by rfl⟩ : syracuseStep 214331 = 321497) B321497
theorem B214391 : Blo 139791 214391 := bstep (se 1 (by rfl) ⟨160793, by rfl⟩ : syracuseStep 214391 = 321587) B321587
theorem B214415 : Blo 139791 214415 := bstep (se 1 (by rfl) ⟨160811, by rfl⟩ : syracuseStep 214415 = 321623) B321623
theorem B214457 : Blo 139791 214457 := bstep (se 2 (by rfl) ⟨80421, by rfl⟩ : syracuseStep 214457 = 160843) B160843
theorem B214535 : Blo 139791 214535 := bstep (se 1 (by rfl) ⟨160901, by rfl⟩ : syracuseStep 214535 = 321803) B321803
theorem B214571 : Blo 139791 214571 := bstep (se 1 (by rfl) ⟨160928, by rfl⟩ : syracuseStep 214571 = 321857) B321857
theorem B214601 : Blo 139791 214601 := bstep (se 2 (by rfl) ⟨80475, by rfl⟩ : syracuseStep 214601 = 160951) B160951
theorem B214715 : Blo 139791 214715 := bstep (se 1 (by rfl) ⟨161036, by rfl⟩ : syracuseStep 214715 = 322073) B322073
theorem B476873 : Blo 139791 476873 := bstep (se 2 (by rfl) ⟨178827, by rfl⟩ : syracuseStep 476873 = 357655) B357655
theorem B214775 : Blo 139791 214775 := bstep (se 1 (by rfl) ⟨161081, by rfl⟩ : syracuseStep 214775 = 322163) B322163
theorem B214799 : Blo 139791 214799 := bstep (se 1 (by rfl) ⟨161099, by rfl⟩ : syracuseStep 214799 = 322199) B322199
theorem B542497 : Blo 139791 542497 := bstep (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) B406873
theorem B214841 : Blo 139791 214841 := bstep (se 2 (by rfl) ⟨80565, by rfl⟩ : syracuseStep 214841 = 161131) B161131
theorem B214919 : Blo 139791 214919 := bstep (se 1 (by rfl) ⟨161189, by rfl⟩ : syracuseStep 214919 = 322379) B322379
theorem B214955 : Blo 139791 214955 := bstep (se 1 (by rfl) ⟨161216, by rfl⟩ : syracuseStep 214955 = 322433) B322433
theorem B214985 : Blo 139791 214985 := bstep (se 2 (by rfl) ⟨80619, by rfl⟩ : syracuseStep 214985 = 161239) B161239
theorem B509905 : Blo 139791 509905 := bstep (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) B382429
theorem B215099 : Blo 139791 215099 := bstep (se 1 (by rfl) ⟨161324, by rfl⟩ : syracuseStep 215099 = 322649) B322649
theorem B215159 : Blo 139791 215159 := bstep (se 1 (by rfl) ⟨161369, by rfl⟩ : syracuseStep 215159 = 322739) B322739
theorem B215183 : Blo 139791 215183 := bstep (se 1 (by rfl) ⟨161387, by rfl⟩ : syracuseStep 215183 = 322775) B322775
theorem B215225 : Blo 139791 215225 := bstep (se 2 (by rfl) ⟨80709, by rfl⟩ : syracuseStep 215225 = 161419) B161419
theorem B510209 : Blo 139791 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B215303 : Blo 139791 215303 := bstep (se 1 (by rfl) ⟨161477, by rfl⟩ : syracuseStep 215303 = 322955) B322955
theorem B215339 : Blo 139791 215339 := bstep (se 1 (by rfl) ⟨161504, by rfl⟩ : syracuseStep 215339 = 323009) B323009
theorem B215369 : Blo 139791 215369 := bstep (se 2 (by rfl) ⟨80763, by rfl⟩ : syracuseStep 215369 = 161527) B161527
theorem B608647 : Blo 139791 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B477575 : Blo 139791 477575 := bstep (se 1 (by rfl) ⟨358181, by rfl⟩ : syracuseStep 477575 = 716363) B716363
theorem B215483 : Blo 139791 215483 := bstep (se 1 (by rfl) ⟨161612, by rfl⟩ : syracuseStep 215483 = 323225) B323225
theorem B215543 : Blo 139791 215543 := bstep (se 1 (by rfl) ⟨161657, by rfl⟩ : syracuseStep 215543 = 323315) B323315
theorem B576011 : Blo 139791 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B215567 : Blo 139791 215567 := bstep (se 1 (by rfl) ⟨161675, by rfl⟩ : syracuseStep 215567 = 323351) B323351
theorem B215609 : Blo 139791 215609 := bstep (se 2 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 215609 = 161707) B161707
theorem B215687 : Blo 139791 215687 := bstep (se 1 (by rfl) ⟨161765, by rfl⟩ : syracuseStep 215687 = 323531) B323531
theorem B543469 : Blo 139791 543469 := bstep (se 3 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 543469 = 203801) B203801
theorem B477953 : Blo 139791 477953 := bstep (se 2 (by rfl) ⟨179232, by rfl⟩ : syracuseStep 477953 = 358465) B358465
theorem B150331 : Blo 139791 150331 := bstep (se 1 (by rfl) ⟨112748, by rfl⟩ : syracuseStep 150331 = 225497) B225497
theorem B543773 : Blo 139791 543773 := bstep (se 3 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 543773 = 203915) B203915
theorem B707777 : Blo 139791 707777 := bstep (se 2 (by rfl) ⟨265416, by rfl⟩ : syracuseStep 707777 = 530833) B530833
theorem B314639 : Blo 139791 314639 := bstep (se 1 (by rfl) ⟨235979, by rfl⟩ : syracuseStep 314639 = 471959) B471959
theorem B314657 : Blo 139791 314657 := bstep (se 2 (by rfl) ⟨117996, by rfl⟩ : syracuseStep 314657 = 235993) B235993
theorem B1199569 : Blo 139791 1199569 := bstep (se 2 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 1199569 = 899677) B899677
theorem B478763 : Blo 139791 478763 := bstep (se 1 (by rfl) ⟨359072, by rfl⟩ : syracuseStep 478763 = 718145) B718145
theorem B314999 : Blo 139791 314999 := bstep (se 1 (by rfl) ⟨236249, by rfl⟩ : syracuseStep 314999 = 472499) B472499
theorem B183979 : Blo 139791 183979 := bstep (se 1 (by rfl) ⟨137984, by rfl⟩ : syracuseStep 183979 = 275969) B275969
theorem B315179 : Blo 139791 315179 := bstep (se 1 (by rfl) ⟨236384, by rfl⟩ : syracuseStep 315179 = 472769) B472769
theorem B577489 : Blo 139791 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B315539 : Blo 139791 315539 := bstep (se 1 (by rfl) ⟨236654, by rfl⟩ : syracuseStep 315539 = 473309) B473309
theorem B315593 : Blo 139791 315593 := bstep (se 2 (by rfl) ⟨118347, by rfl⟩ : syracuseStep 315593 = 236695) B236695
theorem B2937073 : Blo 139791 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B709073 : Blo 139791 709073 := bstep (se 2 (by rfl) ⟨265902, by rfl⟩ : syracuseStep 709073 = 531805) B531805
theorem B545399 : Blo 139791 545399 := bstep (se 1 (by rfl) ⟨409049, by rfl⟩ : syracuseStep 545399 = 818099) B818099
theorem B480059 : Blo 139791 480059 := bstep (se 1 (by rfl) ⟨360044, by rfl⟩ : syracuseStep 480059 = 720089) B720089
theorem B5198681 : Blo 139791 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B316295 : Blo 139791 316295 := bstep (se 1 (by rfl) ⟨237221, by rfl⟩ : syracuseStep 316295 = 474443) B474443
theorem B906137 : Blo 139791 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B1659851 : Blo 139791 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B316475 : Blo 139791 316475 := bstep (se 1 (by rfl) ⟨237356, by rfl⟩ : syracuseStep 316475 = 474713) B474713
theorem B513091 : Blo 139791 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B218231 : Blo 139791 218231 := bstep (se 1 (by rfl) ⟨163673, by rfl⟩ : syracuseStep 218231 = 327347) B327347
theorem B316601 : Blo 139791 316601 := bstep (se 2 (by rfl) ⟨118725, by rfl⟩ : syracuseStep 316601 = 237451) B237451
theorem B4150561 : Blo 139791 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B1365281 : Blo 139791 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B480545 : Blo 139791 480545 := bstep (se 2 (by rfl) ⟨180204, by rfl⟩ : syracuseStep 480545 = 360409) B360409
theorem B1201553 : Blo 139791 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B316943 : Blo 139791 316943 := bstep (se 1 (by rfl) ⟨237707, by rfl⟩ : syracuseStep 316943 = 475415) B475415
theorem B316961 : Blo 139791 316961 := bstep (se 2 (by rfl) ⟨118860, by rfl⟩ : syracuseStep 316961 = 237721) B237721
theorem B481139 : Blo 139791 481139 := bstep (se 1 (by rfl) ⟨360854, by rfl⟩ : syracuseStep 481139 = 721709) B721709
theorem B317303 : Blo 139791 317303 := bstep (se 1 (by rfl) ⟨237977, by rfl⟩ : syracuseStep 317303 = 475955) B475955
theorem B1038347 : Blo 139791 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B317483 : Blo 139791 317483 := bstep (se 1 (by rfl) ⟨238112, by rfl⟩ : syracuseStep 317483 = 476225) B476225
theorem B2054261 : Blo 139791 2054261 := bstep (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) B192587
theorem B13031725 : Blo 139791 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B809351 : Blo 139791 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B317843 : Blo 139791 317843 := bstep (se 1 (by rfl) ⟨238382, by rfl⟩ : syracuseStep 317843 = 476765) B476765
theorem B612755 : Blo 139791 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B317897 : Blo 139791 317897 := bstep (se 2 (by rfl) ⟨119211, by rfl⟩ : syracuseStep 317897 = 238423) B238423
theorem B711179 : Blo 139791 711179 := bstep (se 1 (by rfl) ⟨533384, by rfl⟩ : syracuseStep 711179 = 1066769) B1066769
theorem B514603 : Blo 139791 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B383635 : Blo 139791 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B711341 : Blo 139791 711341 := bstep (se 3 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 711341 = 266753) B266753
theorem B252971 : Blo 139791 252971 := bstep (se 1 (by rfl) ⟨189728, by rfl⟩ : syracuseStep 252971 = 379457) B379457
theorem B318599 : Blo 139791 318599 := bstep (se 1 (by rfl) ⟨238949, by rfl⟩ : syracuseStep 318599 = 477899) B477899
theorem B482561 : Blo 139791 482561 := bstep (se 2 (by rfl) ⟨180960, by rfl⟩ : syracuseStep 482561 = 361921) B361921
theorem B318779 : Blo 139791 318779 := bstep (se 1 (by rfl) ⟨239084, by rfl⟩ : syracuseStep 318779 = 478169) B478169
theorem B318905 : Blo 139791 318905 := bstep (se 2 (by rfl) ⟨119589, by rfl⟩ : syracuseStep 318905 = 239179) B239179
theorem B810557 : Blo 139791 810557 := bstep (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) B303959
theorem B319247 : Blo 139791 319247 := bstep (se 1 (by rfl) ⟨239435, by rfl⟩ : syracuseStep 319247 = 478871) B478871
theorem B319265 : Blo 139791 319265 := bstep (se 2 (by rfl) ⟨119724, by rfl⟩ : syracuseStep 319265 = 239449) B239449
theorem B319607 : Blo 139791 319607 := bstep (se 1 (by rfl) ⟨239705, by rfl⟩ : syracuseStep 319607 = 479411) B479411
theorem B712961 : Blo 139791 712961 := bstep (se 2 (by rfl) ⟨267360, by rfl⟩ : syracuseStep 712961 = 534721) B534721
theorem B319787 : Blo 139791 319787 := bstep (se 1 (by rfl) ⟨239840, by rfl⟩ : syracuseStep 319787 = 479681) B479681
theorem B483731 : Blo 139791 483731 := bstep (se 1 (by rfl) ⟨362798, by rfl⟩ : syracuseStep 483731 = 725597) B725597
theorem B320147 : Blo 139791 320147 := bstep (se 1 (by rfl) ⟨240110, by rfl⟩ : syracuseStep 320147 = 480221) B480221
theorem B320201 : Blo 139791 320201 := bstep (se 2 (by rfl) ⟨120075, by rfl⟩ : syracuseStep 320201 = 240151) B240151
theorem B648071 : Blo 139791 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B713771 : Blo 139791 713771 := bstep (se 1 (by rfl) ⟨535328, by rfl⟩ : syracuseStep 713771 = 1070657) B1070657
theorem B681047 : Blo 139791 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B1729781 : Blo 139791 1729781 := bstep (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) B162167
theorem B320903 : Blo 139791 320903 := bstep (se 1 (by rfl) ⟨240677, by rfl⟩ : syracuseStep 320903 = 481355) B481355
theorem B321083 : Blo 139791 321083 := bstep (se 1 (by rfl) ⟨240812, by rfl⟩ : syracuseStep 321083 = 481625) B481625
theorem B353879 : Blo 139791 353879 := bstep (se 1 (by rfl) ⟨265409, by rfl⟩ : syracuseStep 353879 = 530819) B530819
theorem B353945 : Blo 139791 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B321209 : Blo 139791 321209 := bstep (se 2 (by rfl) ⟨120453, by rfl⟩ : syracuseStep 321209 = 240907) B240907
theorem B485135 : Blo 139791 485135 := bstep (se 1 (by rfl) ⟨363851, by rfl⟩ : syracuseStep 485135 = 727703) B727703
theorem B354091 : Blo 139791 354091 := bstep (se 1 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 354091 = 531137) B531137
theorem B419671 : Blo 139791 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B354233 : Blo 139791 354233 := bstep (se 2 (by rfl) ⟨132837, by rfl⟩ : syracuseStep 354233 = 265675) B265675
theorem B157711 : Blo 139791 157711 := bstep (se 1 (by rfl) ⟨118283, by rfl⟩ : syracuseStep 157711 = 236567) B236567
theorem B321551 : Blo 139791 321551 := bstep (se 1 (by rfl) ⟨241163, by rfl⟩ : syracuseStep 321551 = 482327) B482327
theorem B256033 : Blo 139791 256033 := bstep (se 2 (by rfl) ⟨96012, by rfl⟩ : syracuseStep 256033 = 192025) B192025
theorem B321569 : Blo 139791 321569 := bstep (se 2 (by rfl) ⟨120588, by rfl⟩ : syracuseStep 321569 = 241177) B241177
theorem B190507 : Blo 139791 190507 := bstep (se 1 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 190507 = 285761) B285761
theorem B715067 : Blo 139791 715067 := bstep (se 1 (by rfl) ⟨536300, by rfl⟩ : syracuseStep 715067 = 1072601) B1072601
theorem B190793 : Blo 139791 190793 := bstep (se 2 (by rfl) ⟨71547, by rfl⟩ : syracuseStep 190793 = 143095) B143095
theorem B321911 : Blo 139791 321911 := bstep (se 1 (by rfl) ⟨241433, by rfl⟩ : syracuseStep 321911 = 482867) B482867
theorem B715229 : Blo 139791 715229 := bstep (se 3 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 715229 = 268211) B268211
theorem B158215 : Blo 139791 158215 := bstep (se 1 (by rfl) ⟨118661, by rfl⟩ : syracuseStep 158215 = 237323) B237323
theorem B322091 : Blo 139791 322091 := bstep (se 1 (by rfl) ⟨241568, by rfl⟩ : syracuseStep 322091 = 483137) B483137
theorem B256697 : Blo 139791 256697 := bstep (se 2 (by rfl) ⟨96261, by rfl⟩ : syracuseStep 256697 = 192523) B192523
theorem B158395 : Blo 139791 158395 := bstep (se 1 (by rfl) ⟨118796, by rfl⟩ : syracuseStep 158395 = 237593) B237593
theorem B453377 : Blo 139791 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B715553 : Blo 139791 715553 := bstep (se 2 (by rfl) ⟨268332, by rfl⟩ : syracuseStep 715553 = 536665) B536665
theorem B322451 : Blo 139791 322451 := bstep (se 1 (by rfl) ⟨241838, by rfl⟩ : syracuseStep 322451 = 483677) B483677
theorem B355225 : Blo 139791 355225 := bstep (se 2 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 355225 = 266419) B266419
theorem B453529 : Blo 139791 453529 := bstep (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) B340147
theorem B322505 : Blo 139791 322505 := bstep (se 2 (by rfl) ⟨120939, by rfl⟩ : syracuseStep 322505 = 241879) B241879
theorem B224299 : Blo 139791 224299 := bstep (se 1 (by rfl) ⟨168224, by rfl⟩ : syracuseStep 224299 = 336449) B336449
theorem B355387 : Blo 139791 355387 := bstep (se 1 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 355387 = 533081) B533081
theorem B158863 : Blo 139791 158863 := bstep (se 1 (by rfl) ⟨119147, by rfl⟩ : syracuseStep 158863 = 238295) B238295
theorem B355529 : Blo 139791 355529 := bstep (se 2 (by rfl) ⟨133323, by rfl⟩ : syracuseStep 355529 = 266647) B266647
theorem B1240379 : Blo 139791 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B617843 : Blo 139791 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B355873 : Blo 139791 355873 := bstep (se 2 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 355873 = 266905) B266905
theorem B552491 : Blo 139791 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B159367 : Blo 139791 159367 := bstep (se 1 (by rfl) ⟨119525, by rfl⟩ : syracuseStep 159367 = 239051) B239051
theorem B323207 : Blo 139791 323207 := bstep (se 1 (by rfl) ⟨242405, by rfl⟩ : syracuseStep 323207 = 484811) B484811
theorem B1175233 : Blo 139791 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B716525 : Blo 139791 716525 := bstep (se 3 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 716525 = 268697) B268697
theorem B159547 : Blo 139791 159547 := bstep (se 1 (by rfl) ⟨119660, by rfl⟩ : syracuseStep 159547 = 239321) B239321
theorem B323387 : Blo 139791 323387 := bstep (se 1 (by rfl) ⟨242540, by rfl⟩ : syracuseStep 323387 = 485081) B485081
theorem B323513 : Blo 139791 323513 := bstep (se 2 (by rfl) ⟨121317, by rfl⟩ : syracuseStep 323513 = 242635) B242635
theorem B389207 : Blo 139791 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B356471 : Blo 139791 356471 := bstep (se 1 (by rfl) ⟨267353, by rfl⟩ : syracuseStep 356471 = 534707) B534707
theorem B192631 : Blo 139791 192631 := bstep (se 1 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 192631 = 288947) B288947
theorem B258167 : Blo 139791 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B160015 : Blo 139791 160015 := bstep (se 1 (by rfl) ⟨120011, by rfl⟩ : syracuseStep 160015 = 240023) B240023
theorem B291131 : Blo 139791 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B717335 : Blo 139791 717335 := bstep (se 1 (by rfl) ⟨538001, by rfl⟩ : syracuseStep 717335 = 1076003) B1076003
theorem B684737 : Blo 139791 684737 := bstep (se 2 (by rfl) ⟨256776, by rfl⟩ : syracuseStep 684737 = 513553) B513553
theorem B1372889 : Blo 139791 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B160519 : Blo 139791 160519 := bstep (se 1 (by rfl) ⟨120389, by rfl⟩ : syracuseStep 160519 = 240779) B240779
theorem B1602341 : Blo 139791 1602341 := bstep (se 4 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 1602341 = 300439) B300439
theorem B160699 : Blo 139791 160699 := bstep (se 1 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 160699 = 241049) B241049
theorem B619607 : Blo 139791 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B357767 : Blo 139791 357767 := bstep (se 1 (by rfl) ⟨268325, by rfl⟩ : syracuseStep 357767 = 536651) B536651
theorem B161167 : Blo 139791 161167 := bstep (se 1 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 161167 = 241751) B241751
theorem B20903345 : Blo 139791 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B357817 : Blo 139791 357817 := bstep (se 2 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 357817 = 268363) B268363
theorem B194167 : Blo 139791 194167 := bstep (se 1 (by rfl) ⟨145625, by rfl⟩ : syracuseStep 194167 = 291251) B291251
theorem B161671 : Blo 139791 161671 := bstep (se 1 (by rfl) ⟨121253, by rfl⟩ : syracuseStep 161671 = 242507) B242507
theorem B358415 : Blo 139791 358415 := bstep (se 1 (by rfl) ⟨268811, by rfl⟩ : syracuseStep 358415 = 537623) B537623
theorem B13694993 : Blo 139791 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B686369 : Blo 139791 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B2980313 : Blo 139791 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B227855 : Blo 139791 227855 := bstep (se 1 (by rfl) ⟨170891, by rfl⟩ : syracuseStep 227855 = 341783) B341783
theorem B359113 : Blo 139791 359113 := bstep (se 2 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 359113 = 269335) B269335
theorem B391969 : Blo 139791 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B326443 : Blo 139791 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B359255 : Blo 139791 359255 := bstep (se 1 (by rfl) ⟨269441, by rfl⟩ : syracuseStep 359255 = 538883) B538883
theorem B260983 : Blo 139791 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B228367 : Blo 139791 228367 := bstep (se 1 (by rfl) ⟨171275, by rfl⟩ : syracuseStep 228367 = 342551) B342551
theorem B720065 : Blo 139791 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B458131 : Blo 139791 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B720413 : Blo 139791 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B2719331 : Blo 139791 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B1572941 : Blo 139791 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B688445 : Blo 139791 688445 := bstep (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) B258167
theorem B1180169 : Blo 139791 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B1245719 : Blo 139791 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B361057 : Blo 139791 361057 := bstep (se 2 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 361057 = 270793) B270793
theorem B459361 : Blo 139791 459361 := bstep (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) B344521
theorem B1181147 : Blo 139791 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B362009 : Blo 139791 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B722681 : Blo 139791 722681 := bstep (se 2 (by rfl) ⟨271005, by rfl⟩ : syracuseStep 722681 = 542011) B542011
theorem B362515 : Blo 139791 362515 := bstep (se 1 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 362515 = 543773) B543773
theorem B723329 : Blo 139791 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B559561 : Blo 139791 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B1608173 : Blo 139791 1608173 := bstep (se 3 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 1608173 = 603065) B603065
theorem B1772381 : Blo 139791 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B363599 : Blo 139791 363599 := bstep (se 1 (by rfl) ⟨272699, by rfl⟩ : syracuseStep 363599 = 545399) B545399
theorem B724139 : Blo 139791 724139 := bstep (se 1 (by rfl) ⟨543104, by rfl⟩ : syracuseStep 724139 = 1086209) B1086209
theorem B724625 : Blo 139791 724625 := bstep (se 2 (by rfl) ⟨271734, by rfl⟩ : syracuseStep 724625 = 543469) B543469
theorem B200441 : Blo 139791 200441 := bstep (se 2 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 200441 = 150331) B150331
theorem B692231 : Blo 139791 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B299065 : Blo 139791 299065 := bstep (se 2 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 299065 = 224299) B224299
theorem B1380887 : Blo 139791 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B201295 : Blo 139791 201295 := bstep (se 1 (by rfl) ⟨150971, by rfl⟩ : syracuseStep 201295 = 301943) B301943
theorem B168647 : Blo 139791 168647 := bstep (se 1 (by rfl) ⟨126485, by rfl⟩ : syracuseStep 168647 = 252971) B252971
theorem B266951 : Blo 139791 266951 := bstep (se 1 (by rfl) ⟨200213, by rfl⟩ : syracuseStep 266951 = 400427) B400427
theorem B267475 : Blo 139791 267475 := bstep (se 1 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 267475 = 401213) B401213
theorem B267695 : Blo 139791 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B398945 : Blo 139791 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B268105 : Blo 139791 268105 := bstep (se 2 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 268105 = 201079) B201079
theorem B726893 : Blo 139791 726893 := bstep (se 3 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 726893 = 272585) B272585
theorem B432047 : Blo 139791 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B727055 : Blo 139791 727055 := bstep (se 1 (by rfl) ⟨545291, by rfl⟩ : syracuseStep 727055 = 1090583) B1090583
theorem B1153187 : Blo 139791 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B235919 : Blo 139791 235919 := bstep (se 1 (by rfl) ⟨176939, by rfl⟩ : syracuseStep 235919 = 353879) B353879
theorem B235963 : Blo 139791 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B236155 : Blo 139791 236155 := bstep (se 1 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 236155 = 354233) B354233
theorem B7740035 : Blo 139791 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B531319 : Blo 139791 531319 := bstep (se 1 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 531319 = 796979) B796979
theorem B400403 : Blo 139791 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B171131 : Blo 139791 171131 := bstep (se 1 (by rfl) ⟨128348, by rfl⟩ : syracuseStep 171131 = 256697) B256697
theorem B302251 : Blo 139791 302251 := bstep (se 1 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 302251 = 453377) B453377
theorem B466319 : Blo 139791 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B237019 : Blo 139791 237019 := bstep (se 1 (by rfl) ⟨177764, by rfl⟩ : syracuseStep 237019 = 355529) B355529
theorem B400859 : Blo 139791 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B826919 : Blo 139791 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B368327 : Blo 139791 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B597719 : Blo 139791 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B532291 : Blo 139791 532291 := bstep (se 1 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 532291 = 798437) B798437
theorem B237647 : Blo 139791 237647 := bstep (se 1 (by rfl) ⟨178235, by rfl⟩ : syracuseStep 237647 = 356471) B356471
theorem B532595 : Blo 139791 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B270535 : Blo 139791 270535 := bstep (se 1 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 270535 = 405803) B405803
theorem B205151 : Blo 139791 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B17375633 : Blo 139791 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B139815 : Blo 139791 139815 := bstep (se 1 (by rfl) ⟨104861, by rfl⟩ : syracuseStep 139815 = 209723) B209723
theorem B533051 : Blo 139791 533051 := bstep (se 1 (by rfl) ⟨399788, by rfl⟩ : syracuseStep 533051 = 799577) B799577
theorem B139855 : Blo 139791 139855 := bstep (se 1 (by rfl) ⟨104891, by rfl⟩ : syracuseStep 139855 = 209783) B209783
theorem B139871 : Blo 139791 139871 := bstep (se 1 (by rfl) ⟨104903, by rfl⟩ : syracuseStep 139871 = 209807) B209807
theorem B139899 : Blo 139791 139899 := bstep (se 1 (by rfl) ⟨104924, by rfl⟩ : syracuseStep 139899 = 209849) B209849
theorem B139951 : Blo 139791 139951 := bstep (se 1 (by rfl) ⟨104963, by rfl⟩ : syracuseStep 139951 = 209927) B209927
theorem B139975 : Blo 139791 139975 := bstep (se 1 (by rfl) ⟨104981, by rfl⟩ : syracuseStep 139975 = 209963) B209963
theorem B139995 : Blo 139791 139995 := bstep (se 1 (by rfl) ⟨104996, by rfl⟩ : syracuseStep 139995 = 209993) B209993
theorem B271097 : Blo 139791 271097 := bstep (se 2 (by rfl) ⟨101661, by rfl⟩ : syracuseStep 271097 = 203323) B203323
theorem B140071 : Blo 139791 140071 := bstep (se 1 (by rfl) ⟨105053, by rfl⟩ : syracuseStep 140071 = 210107) B210107
theorem B140111 : Blo 139791 140111 := bstep (se 1 (by rfl) ⟨105083, by rfl⟩ : syracuseStep 140111 = 210167) B210167
theorem B140127 : Blo 139791 140127 := bstep (se 1 (by rfl) ⟨105095, by rfl⟩ : syracuseStep 140127 = 210191) B210191
theorem B140155 : Blo 139791 140155 := bstep (se 1 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 140155 = 210233) B210233
theorem B140207 : Blo 139791 140207 := bstep (se 1 (by rfl) ⟨105155, by rfl⟩ : syracuseStep 140207 = 210311) B210311
theorem B238511 : Blo 139791 238511 := bstep (se 1 (by rfl) ⟨178883, by rfl⟩ : syracuseStep 238511 = 357767) B357767
theorem B271279 : Blo 139791 271279 := bstep (se 1 (by rfl) ⟨203459, by rfl⟩ : syracuseStep 271279 = 406919) B406919
theorem B140231 : Blo 139791 140231 := bstep (se 1 (by rfl) ⟨105173, by rfl⟩ : syracuseStep 140231 = 210347) B210347
theorem B13935563 : Blo 139791 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B140251 : Blo 139791 140251 := bstep (se 1 (by rfl) ⟨105188, by rfl⟩ : syracuseStep 140251 = 210377) B210377
theorem B140327 : Blo 139791 140327 := bstep (se 1 (by rfl) ⟨105245, by rfl⟩ : syracuseStep 140327 = 210491) B210491
theorem B2401325 : Blo 139791 2401325 := bstep (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) B900497
theorem B435257 : Blo 139791 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B140367 : Blo 139791 140367 := bstep (se 1 (by rfl) ⟨105275, by rfl⟩ : syracuseStep 140367 = 210551) B210551
theorem B205903 : Blo 139791 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B140383 : Blo 139791 140383 := bstep (se 1 (by rfl) ⟨105287, by rfl⟩ : syracuseStep 140383 = 210575) B210575
theorem B140411 : Blo 139791 140411 := bstep (se 1 (by rfl) ⟨105308, by rfl⟩ : syracuseStep 140411 = 210617) B210617
theorem B140463 : Blo 139791 140463 := bstep (se 1 (by rfl) ⟨105347, by rfl⟩ : syracuseStep 140463 = 210695) B210695
theorem B140487 : Blo 139791 140487 := bstep (se 1 (by rfl) ⟨105365, by rfl⟩ : syracuseStep 140487 = 210731) B210731
theorem B140507 : Blo 139791 140507 := bstep (se 1 (by rfl) ⟨105380, by rfl⟩ : syracuseStep 140507 = 210761) B210761
theorem B140583 : Blo 139791 140583 := bstep (se 1 (by rfl) ⟨105437, by rfl⟩ : syracuseStep 140583 = 210875) B210875
theorem B140623 : Blo 139791 140623 := bstep (se 1 (by rfl) ⟨105467, by rfl⟩ : syracuseStep 140623 = 210935) B210935
theorem B140639 : Blo 139791 140639 := bstep (se 1 (by rfl) ⟨105479, by rfl⟩ : syracuseStep 140639 = 210959) B210959
theorem B238943 : Blo 139791 238943 := bstep (se 1 (by rfl) ⟨179207, by rfl⟩ : syracuseStep 238943 = 358415) B358415
theorem B304489 : Blo 139791 304489 := bstep (se 2 (by rfl) ⟨114183, by rfl⟩ : syracuseStep 304489 = 228367) B228367
theorem B140667 : Blo 139791 140667 := bstep (se 1 (by rfl) ⟨105500, by rfl⟩ : syracuseStep 140667 = 211001) B211001
theorem B140719 : Blo 139791 140719 := bstep (se 1 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 140719 = 211079) B211079
theorem B140743 : Blo 139791 140743 := bstep (se 1 (by rfl) ⟨105557, by rfl⟩ : syracuseStep 140743 = 211115) B211115
theorem B140763 : Blo 139791 140763 := bstep (se 1 (by rfl) ⟨105572, by rfl⟩ : syracuseStep 140763 = 211145) B211145
theorem B140839 : Blo 139791 140839 := bstep (se 1 (by rfl) ⟨105629, by rfl⟩ : syracuseStep 140839 = 211259) B211259
theorem B140879 : Blo 139791 140879 := bstep (se 1 (by rfl) ⟨105659, by rfl⟩ : syracuseStep 140879 = 211319) B211319
theorem B140895 : Blo 139791 140895 := bstep (se 1 (by rfl) ⟨105671, by rfl⟩ : syracuseStep 140895 = 211343) B211343
theorem B370273 : Blo 139791 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B140923 : Blo 139791 140923 := bstep (se 1 (by rfl) ⟨105692, by rfl⟩ : syracuseStep 140923 = 211385) B211385
theorem B2762387 : Blo 139791 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B140975 : Blo 139791 140975 := bstep (se 1 (by rfl) ⟨105731, by rfl⟩ : syracuseStep 140975 = 211463) B211463
theorem B140999 : Blo 139791 140999 := bstep (se 1 (by rfl) ⟨105749, by rfl⟩ : syracuseStep 140999 = 211499) B211499
theorem B141019 : Blo 139791 141019 := bstep (se 1 (by rfl) ⟨105764, by rfl⟩ : syracuseStep 141019 = 211529) B211529
theorem B141095 : Blo 139791 141095 := bstep (se 1 (by rfl) ⟨105821, by rfl⟩ : syracuseStep 141095 = 211643) B211643
theorem B141135 : Blo 139791 141135 := bstep (se 1 (by rfl) ⟨105851, by rfl⟩ : syracuseStep 141135 = 211703) B211703
theorem B141151 : Blo 139791 141151 := bstep (se 1 (by rfl) ⟨105863, by rfl⟩ : syracuseStep 141151 = 211727) B211727
theorem B141179 : Blo 139791 141179 := bstep (se 1 (by rfl) ⟨105884, by rfl⟩ : syracuseStep 141179 = 211769) B211769
theorem B239503 : Blo 139791 239503 := bstep (se 1 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 239503 = 359255) B359255
theorem B141231 : Blo 139791 141231 := bstep (se 1 (by rfl) ⟨105923, by rfl⟩ : syracuseStep 141231 = 211847) B211847
theorem B141255 : Blo 139791 141255 := bstep (se 1 (by rfl) ⟨105941, by rfl⟩ : syracuseStep 141255 = 211883) B211883
theorem B141275 : Blo 139791 141275 := bstep (se 1 (by rfl) ⟨105956, by rfl⟩ : syracuseStep 141275 = 211913) B211913
theorem B141351 : Blo 139791 141351 := bstep (se 1 (by rfl) ⟨106013, by rfl⟩ : syracuseStep 141351 = 212027) B212027
theorem B141391 : Blo 139791 141391 := bstep (se 1 (by rfl) ⟨106043, by rfl⟩ : syracuseStep 141391 = 212087) B212087
theorem B141407 : Blo 139791 141407 := bstep (se 1 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 141407 = 212111) B212111
theorem B141435 : Blo 139791 141435 := bstep (se 1 (by rfl) ⟨106076, by rfl⟩ : syracuseStep 141435 = 212153) B212153
theorem B272555 : Blo 139791 272555 := bstep (se 1 (by rfl) ⟨204416, by rfl⟩ : syracuseStep 272555 = 408833) B408833
theorem B141487 : Blo 139791 141487 := bstep (se 1 (by rfl) ⟨106115, by rfl⟩ : syracuseStep 141487 = 212231) B212231
theorem B141511 : Blo 139791 141511 := bstep (se 1 (by rfl) ⟨106133, by rfl⟩ : syracuseStep 141511 = 212267) B212267
theorem B141531 : Blo 139791 141531 := bstep (se 1 (by rfl) ⟨106148, by rfl⟩ : syracuseStep 141531 = 212297) B212297
theorem B141607 : Blo 139791 141607 := bstep (se 1 (by rfl) ⟨106205, by rfl⟩ : syracuseStep 141607 = 212411) B212411
theorem B141647 : Blo 139791 141647 := bstep (se 1 (by rfl) ⟨106235, by rfl⟩ : syracuseStep 141647 = 212471) B212471
theorem B141663 : Blo 139791 141663 := bstep (se 1 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 141663 = 212495) B212495
theorem B141691 : Blo 139791 141691 := bstep (se 1 (by rfl) ⟨106268, by rfl⟩ : syracuseStep 141691 = 212537) B212537
theorem B272783 : Blo 139791 272783 := bstep (se 1 (by rfl) ⟨204587, by rfl⟩ : syracuseStep 272783 = 409175) B409175
theorem B1812887 : Blo 139791 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B141743 : Blo 139791 141743 := bstep (se 1 (by rfl) ⟨106307, by rfl⟩ : syracuseStep 141743 = 212615) B212615
theorem B141767 : Blo 139791 141767 := bstep (se 1 (by rfl) ⟨106325, by rfl⟩ : syracuseStep 141767 = 212651) B212651
theorem B141787 : Blo 139791 141787 := bstep (se 1 (by rfl) ⟨106340, by rfl⟩ : syracuseStep 141787 = 212681) B212681
theorem B141863 : Blo 139791 141863 := bstep (se 1 (by rfl) ⟨106397, by rfl⟩ : syracuseStep 141863 = 212795) B212795
theorem B240185 : Blo 139791 240185 := bstep (se 2 (by rfl) ⟨90069, by rfl⟩ : syracuseStep 240185 = 180139) B180139
theorem B141903 : Blo 139791 141903 := bstep (se 1 (by rfl) ⟨106427, by rfl⟩ : syracuseStep 141903 = 212855) B212855
theorem B141919 : Blo 139791 141919 := bstep (se 1 (by rfl) ⟨106439, by rfl⟩ : syracuseStep 141919 = 212879) B212879
theorem B141947 : Blo 139791 141947 := bstep (se 1 (by rfl) ⟨106460, by rfl⟩ : syracuseStep 141947 = 212921) B212921
theorem B141999 : Blo 139791 141999 := bstep (se 1 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 141999 = 212999) B212999
theorem B142023 : Blo 139791 142023 := bstep (se 1 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 142023 = 213035) B213035
theorem B142043 : Blo 139791 142043 := bstep (se 1 (by rfl) ⟨106532, by rfl⟩ : syracuseStep 142043 = 213065) B213065
theorem B142119 : Blo 139791 142119 := bstep (se 1 (by rfl) ⟨106589, by rfl⟩ : syracuseStep 142119 = 213179) B213179
theorem B305993 : Blo 139791 305993 := bstep (se 2 (by rfl) ⟨114747, by rfl⟩ : syracuseStep 305993 = 229495) B229495
theorem B142159 : Blo 139791 142159 := bstep (se 1 (by rfl) ⟨106619, by rfl⟩ : syracuseStep 142159 = 213239) B213239
theorem B142175 : Blo 139791 142175 := bstep (se 1 (by rfl) ⟨106631, by rfl⟩ : syracuseStep 142175 = 213263) B213263
theorem B142203 : Blo 139791 142203 := bstep (se 1 (by rfl) ⟨106652, by rfl⟩ : syracuseStep 142203 = 213305) B213305
theorem B1551251 : Blo 139791 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B142255 : Blo 139791 142255 := bstep (se 1 (by rfl) ⟨106691, by rfl⟩ : syracuseStep 142255 = 213383) B213383
theorem B601015 : Blo 139791 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B142279 : Blo 139791 142279 := bstep (se 1 (by rfl) ⟨106709, by rfl⟩ : syracuseStep 142279 = 213419) B213419
theorem B142299 : Blo 139791 142299 := bstep (se 1 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 142299 = 213449) B213449
theorem B142375 : Blo 139791 142375 := bstep (se 1 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 142375 = 213563) B213563
theorem B142415 : Blo 139791 142415 := bstep (se 1 (by rfl) ⟨106811, by rfl⟩ : syracuseStep 142415 = 213623) B213623
theorem B142431 : Blo 139791 142431 := bstep (se 1 (by rfl) ⟨106823, by rfl⟩ : syracuseStep 142431 = 213647) B213647
theorem B142459 : Blo 139791 142459 := bstep (se 1 (by rfl) ⟨106844, by rfl⟩ : syracuseStep 142459 = 213689) B213689
theorem B142511 : Blo 139791 142511 := bstep (se 1 (by rfl) ⟨106883, by rfl⟩ : syracuseStep 142511 = 213767) B213767
theorem B2895041 : Blo 139791 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B142535 : Blo 139791 142535 := bstep (se 1 (by rfl) ⟨106901, by rfl⟩ : syracuseStep 142535 = 213803) B213803
theorem B142555 : Blo 139791 142555 := bstep (se 1 (by rfl) ⟨106916, by rfl⟩ : syracuseStep 142555 = 213833) B213833
theorem B240887 : Blo 139791 240887 := bstep (se 1 (by rfl) ⟨180665, by rfl⟩ : syracuseStep 240887 = 361331) B361331
theorem B142631 : Blo 139791 142631 := bstep (se 1 (by rfl) ⟨106973, by rfl⟩ : syracuseStep 142631 = 213947) B213947
theorem B142671 : Blo 139791 142671 := bstep (se 1 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 142671 = 214007) B214007
theorem B142687 : Blo 139791 142687 := bstep (se 1 (by rfl) ⟨107015, by rfl⟩ : syracuseStep 142687 = 214031) B214031
theorem B142715 : Blo 139791 142715 := bstep (se 1 (by rfl) ⟨107036, by rfl⟩ : syracuseStep 142715 = 214073) B214073
theorem B142767 : Blo 139791 142767 := bstep (se 1 (by rfl) ⟨107075, by rfl⟩ : syracuseStep 142767 = 214151) B214151
theorem B142791 : Blo 139791 142791 := bstep (se 1 (by rfl) ⟨107093, by rfl⟩ : syracuseStep 142791 = 214187) B214187
theorem B142811 : Blo 139791 142811 := bstep (se 1 (by rfl) ⟨107108, by rfl⟩ : syracuseStep 142811 = 214217) B214217
theorem B142887 : Blo 139791 142887 := bstep (se 1 (by rfl) ⟨107165, by rfl⟩ : syracuseStep 142887 = 214331) B214331
theorem B142927 : Blo 139791 142927 := bstep (se 1 (by rfl) ⟨107195, by rfl⟩ : syracuseStep 142927 = 214391) B214391
theorem B241231 : Blo 139791 241231 := bstep (se 1 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 241231 = 361847) B361847
theorem B142943 : Blo 139791 142943 := bstep (se 1 (by rfl) ⟨107207, by rfl⟩ : syracuseStep 142943 = 214415) B214415
theorem B142971 : Blo 139791 142971 := bstep (se 1 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 142971 = 214457) B214457
theorem B143023 : Blo 139791 143023 := bstep (se 1 (by rfl) ⟨107267, by rfl⟩ : syracuseStep 143023 = 214535) B214535
theorem B143047 : Blo 139791 143047 := bstep (se 1 (by rfl) ⟨107285, by rfl⟩ : syracuseStep 143047 = 214571) B214571
theorem B1027799 : Blo 139791 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B143067 : Blo 139791 143067 := bstep (se 1 (by rfl) ⟨107300, by rfl⟩ : syracuseStep 143067 = 214601) B214601
theorem B143143 : Blo 139791 143143 := bstep (se 1 (by rfl) ⟨107357, by rfl⟩ : syracuseStep 143143 = 214715) B214715
theorem B241481 : Blo 139791 241481 := bstep (se 2 (by rfl) ⟨90555, by rfl⟩ : syracuseStep 241481 = 181111) B181111
theorem B143183 : Blo 139791 143183 := bstep (se 1 (by rfl) ⟨107387, by rfl⟩ : syracuseStep 143183 = 214775) B214775
theorem B143199 : Blo 139791 143199 := bstep (se 1 (by rfl) ⟨107399, by rfl⟩ : syracuseStep 143199 = 214799) B214799
theorem B143227 : Blo 139791 143227 := bstep (se 1 (by rfl) ⟨107420, by rfl⟩ : syracuseStep 143227 = 214841) B214841
theorem B143279 : Blo 139791 143279 := bstep (se 1 (by rfl) ⟨107459, by rfl⟩ : syracuseStep 143279 = 214919) B214919
theorem B1028027 : Blo 139791 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B143303 : Blo 139791 143303 := bstep (se 1 (by rfl) ⟨107477, by rfl⟩ : syracuseStep 143303 = 214955) B214955
theorem B143323 : Blo 139791 143323 := bstep (se 1 (by rfl) ⟨107492, by rfl⟩ : syracuseStep 143323 = 214985) B214985
theorem B143399 : Blo 139791 143399 := bstep (se 1 (by rfl) ⟨107549, by rfl⟩ : syracuseStep 143399 = 215099) B215099
theorem B143439 : Blo 139791 143439 := bstep (se 1 (by rfl) ⟨107579, by rfl⟩ : syracuseStep 143439 = 215159) B215159
theorem B143455 : Blo 139791 143455 := bstep (se 1 (by rfl) ⟨107591, by rfl⟩ : syracuseStep 143455 = 215183) B215183
theorem B143483 : Blo 139791 143483 := bstep (se 1 (by rfl) ⟨107612, by rfl⟩ : syracuseStep 143483 = 215225) B215225
theorem B340139 : Blo 139791 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B143535 : Blo 139791 143535 := bstep (se 1 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 143535 = 215303) B215303
theorem B143559 : Blo 139791 143559 := bstep (se 1 (by rfl) ⟨107669, by rfl⟩ : syracuseStep 143559 = 215339) B215339
theorem B143579 : Blo 139791 143579 := bstep (se 1 (by rfl) ⟨107684, by rfl⟩ : syracuseStep 143579 = 215369) B215369
theorem B241913 : Blo 139791 241913 := bstep (se 2 (by rfl) ⟨90717, by rfl⟩ : syracuseStep 241913 = 181435) B181435
theorem B143655 : Blo 139791 143655 := bstep (se 1 (by rfl) ⟨107741, by rfl⟩ : syracuseStep 143655 = 215483) B215483
theorem B143695 : Blo 139791 143695 := bstep (se 1 (by rfl) ⟨107771, by rfl⟩ : syracuseStep 143695 = 215543) B215543
theorem B143711 : Blo 139791 143711 := bstep (se 1 (by rfl) ⟨107783, by rfl⟩ : syracuseStep 143711 = 215567) B215567
theorem B143739 : Blo 139791 143739 := bstep (se 1 (by rfl) ⟨107804, by rfl⟩ : syracuseStep 143739 = 215609) B215609
theorem B242095 : Blo 139791 242095 := bstep (se 1 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 242095 = 363143) B363143
theorem B143791 : Blo 139791 143791 := bstep (se 1 (by rfl) ⟨107843, by rfl⟩ : syracuseStep 143791 = 215687) B215687
theorem B242183 : Blo 139791 242183 := bstep (se 1 (by rfl) ⟨181637, by rfl⟩ : syracuseStep 242183 = 363275) B363275
theorem B471851 : Blo 139791 471851 := bstep (se 1 (by rfl) ⟨353888, by rfl⟩ : syracuseStep 471851 = 707777) B707777
theorem B209759 : Blo 139791 209759 := bstep (se 1 (by rfl) ⟨157319, by rfl⟩ : syracuseStep 209759 = 314639) B314639
theorem B242527 : Blo 139791 242527 := bstep (se 1 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 242527 = 363791) B363791
theorem B209771 : Blo 139791 209771 := bstep (se 1 (by rfl) ⟨157328, by rfl⟩ : syracuseStep 209771 = 314657) B314657
theorem B242615 : Blo 139791 242615 := bstep (se 1 (by rfl) ⟨181961, by rfl⟩ : syracuseStep 242615 = 363923) B363923
theorem B472121 : Blo 139791 472121 := bstep (se 2 (by rfl) ⟨177045, by rfl⟩ : syracuseStep 472121 = 354091) B354091
theorem B209999 : Blo 139791 209999 := bstep (se 1 (by rfl) ⟨157499, by rfl⟩ : syracuseStep 209999 = 314999) B314999
theorem B504947 : Blo 139791 504947 := bstep (se 1 (by rfl) ⟨378710, by rfl⟩ : syracuseStep 504947 = 757421) B757421
theorem B210119 : Blo 139791 210119 := bstep (se 1 (by rfl) ⟨157589, by rfl⟩ : syracuseStep 210119 = 315179) B315179
theorem B210281 : Blo 139791 210281 := bstep (se 2 (by rfl) ⟨78855, by rfl⟩ : syracuseStep 210281 = 157711) B157711
theorem B472445 : Blo 139791 472445 := bstep (se 3 (by rfl) ⟨88583, by rfl⟩ : syracuseStep 472445 = 177167) B177167
theorem B341377 : Blo 139791 341377 := bstep (se 2 (by rfl) ⟨128016, by rfl⟩ : syracuseStep 341377 = 256033) B256033
theorem B898447 : Blo 139791 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B210359 : Blo 139791 210359 := bstep (se 1 (by rfl) ⟨157769, by rfl⟩ : syracuseStep 210359 = 315539) B315539
theorem B210395 : Blo 139791 210395 := bstep (se 1 (by rfl) ⟨157796, by rfl⟩ : syracuseStep 210395 = 315593) B315593
theorem B1652285 : Blo 139791 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B472715 : Blo 139791 472715 := bstep (se 1 (by rfl) ⟨354536, by rfl⟩ : syracuseStep 472715 = 709073) B709073
theorem B767627 : Blo 139791 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B964243 : Blo 139791 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B538397 : Blo 139791 538397 := bstep (se 3 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 538397 = 201899) B201899
theorem B210863 : Blo 139791 210863 := bstep (se 1 (by rfl) ⟨158147, by rfl⟩ : syracuseStep 210863 = 316295) B316295
theorem B604091 : Blo 139791 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B1095611 : Blo 139791 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B178139 : Blo 139791 178139 := bstep (se 1 (by rfl) ⟨133604, by rfl⟩ : syracuseStep 178139 = 267209) B267209
theorem B210953 : Blo 139791 210953 := bstep (se 2 (by rfl) ⟨79107, by rfl⟩ : syracuseStep 210953 = 158215) B158215
theorem B505871 : Blo 139791 505871 := bstep (se 1 (by rfl) ⟨379403, by rfl⟩ : syracuseStep 505871 = 758807) B758807
theorem B210983 : Blo 139791 210983 := bstep (se 1 (by rfl) ⟨158237, by rfl⟩ : syracuseStep 210983 = 316475) B316475
theorem B145487 : Blo 139791 145487 := bstep (se 1 (by rfl) ⟨109115, by rfl⟩ : syracuseStep 145487 = 218231) B218231
theorem B2046053 : Blo 139791 2046053 := bstep (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) B383635
theorem B211067 : Blo 139791 211067 := bstep (se 1 (by rfl) ⟨158300, by rfl⟩ : syracuseStep 211067 = 316601) B316601
theorem B211193 : Blo 139791 211193 := bstep (se 2 (by rfl) ⟨79197, by rfl⟩ : syracuseStep 211193 = 158395) B158395
theorem B801035 : Blo 139791 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B211295 : Blo 139791 211295 := bstep (se 1 (by rfl) ⟨158471, by rfl⟩ : syracuseStep 211295 = 316943) B316943
theorem B211307 : Blo 139791 211307 := bstep (se 1 (by rfl) ⟨158480, by rfl⟩ : syracuseStep 211307 = 316961) B316961
theorem B178615 : Blo 139791 178615 := bstep (se 1 (by rfl) ⟨133961, by rfl⟩ : syracuseStep 178615 = 267923) B267923
theorem B539081 : Blo 139791 539081 := bstep (se 2 (by rfl) ⟨202155, by rfl⟩ : syracuseStep 539081 = 404311) B404311
theorem B473633 : Blo 139791 473633 := bstep (se 2 (by rfl) ⟨177612, by rfl⟩ : syracuseStep 473633 = 355225) B355225
theorem B211535 : Blo 139791 211535 := bstep (se 1 (by rfl) ⟨158651, by rfl⟩ : syracuseStep 211535 = 317303) B317303
theorem B211655 : Blo 139791 211655 := bstep (se 1 (by rfl) ⟨158741, by rfl⟩ : syracuseStep 211655 = 317483) B317483
theorem B473849 : Blo 139791 473849 := bstep (se 2 (by rfl) ⟨177693, by rfl⟩ : syracuseStep 473849 = 355387) B355387
theorem B211817 : Blo 139791 211817 := bstep (se 2 (by rfl) ⟨79431, by rfl⟩ : syracuseStep 211817 = 158863) B158863
theorem B539567 : Blo 139791 539567 := bstep (se 1 (by rfl) ⟨404675, by rfl⟩ : syracuseStep 539567 = 809351) B809351
theorem B211895 : Blo 139791 211895 := bstep (se 1 (by rfl) ⟨158921, by rfl⟩ : syracuseStep 211895 = 317843) B317843
theorem B408503 : Blo 139791 408503 := bstep (se 1 (by rfl) ⟨306377, by rfl⟩ : syracuseStep 408503 = 612755) B612755
theorem B211931 : Blo 139791 211931 := bstep (se 1 (by rfl) ⟨158948, by rfl⟩ : syracuseStep 211931 = 317897) B317897
theorem B474119 : Blo 139791 474119 := bstep (se 1 (by rfl) ⟨355589, by rfl⟩ : syracuseStep 474119 = 711179) B711179
theorem B474227 : Blo 139791 474227 := bstep (se 1 (by rfl) ⟨355670, by rfl⟩ : syracuseStep 474227 = 711341) B711341
theorem B474497 : Blo 139791 474497 := bstep (se 2 (by rfl) ⟨177936, by rfl⟩ : syracuseStep 474497 = 355873) B355873
theorem B212399 : Blo 139791 212399 := bstep (se 1 (by rfl) ⟨159299, by rfl⟩ : syracuseStep 212399 = 318599) B318599
theorem B212489 : Blo 139791 212489 := bstep (se 2 (by rfl) ⟨79683, by rfl⟩ : syracuseStep 212489 = 159367) B159367
theorem B212519 : Blo 139791 212519 := bstep (se 1 (by rfl) ⟨159389, by rfl⟩ : syracuseStep 212519 = 318779) B318779
theorem B245305 : Blo 139791 245305 := bstep (se 2 (by rfl) ⟨91989, by rfl⟩ : syracuseStep 245305 = 183979) B183979
theorem B212603 : Blo 139791 212603 := bstep (se 1 (by rfl) ⟨159452, by rfl⟩ : syracuseStep 212603 = 318905) B318905
theorem B802493 : Blo 139791 802493 := bstep (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) B300935
theorem B179911 : Blo 139791 179911 := bstep (se 1 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 179911 = 269867) B269867
theorem B540371 : Blo 139791 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B212729 : Blo 139791 212729 := bstep (se 2 (by rfl) ⟨79773, by rfl⟩ : syracuseStep 212729 = 159547) B159547
theorem B573257 : Blo 139791 573257 := bstep (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) B429943
theorem B212831 : Blo 139791 212831 := bstep (se 1 (by rfl) ⟨159623, by rfl⟩ : syracuseStep 212831 = 319247) B319247
theorem B212843 : Blo 139791 212843 := bstep (se 1 (by rfl) ⟨159632, by rfl⟩ : syracuseStep 212843 = 319265) B319265
theorem B769985 : Blo 139791 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B213071 : Blo 139791 213071 := bstep (se 1 (by rfl) ⟨159803, by rfl⟩ : syracuseStep 213071 = 319607) B319607
theorem B475307 : Blo 139791 475307 := bstep (se 1 (by rfl) ⟨356480, by rfl⟩ : syracuseStep 475307 = 712961) B712961
theorem B1851569 : Blo 139791 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B213191 : Blo 139791 213191 := bstep (se 1 (by rfl) ⟨159893, by rfl⟩ : syracuseStep 213191 = 319787) B319787
theorem B3916097 : Blo 139791 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B213353 : Blo 139791 213353 := bstep (se 2 (by rfl) ⟨80007, by rfl⟩ : syracuseStep 213353 = 160015) B160015
theorem B213431 : Blo 139791 213431 := bstep (se 1 (by rfl) ⟨160073, by rfl⟩ : syracuseStep 213431 = 320147) B320147
theorem B213467 : Blo 139791 213467 := bstep (se 1 (by rfl) ⟨160100, by rfl⟩ : syracuseStep 213467 = 320201) B320201
theorem B475847 : Blo 139791 475847 := bstep (se 1 (by rfl) ⟨356885, by rfl⟩ : syracuseStep 475847 = 713771) B713771
theorem B508781 : Blo 139791 508781 := bstep (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) B190793
theorem B213935 : Blo 139791 213935 := bstep (se 1 (by rfl) ⟨160451, by rfl⟩ : syracuseStep 213935 = 320903) B320903
theorem B214025 : Blo 139791 214025 := bstep (se 2 (by rfl) ⟨80259, by rfl⟩ : syracuseStep 214025 = 160519) B160519
theorem B214055 : Blo 139791 214055 := bstep (se 1 (by rfl) ⟨160541, by rfl⟩ : syracuseStep 214055 = 321083) B321083
theorem B214139 : Blo 139791 214139 := bstep (se 1 (by rfl) ⟨160604, by rfl⟩ : syracuseStep 214139 = 321209) B321209
theorem B214265 : Blo 139791 214265 := bstep (se 2 (by rfl) ⟨80349, by rfl⟩ : syracuseStep 214265 = 160699) B160699
theorem B214367 : Blo 139791 214367 := bstep (se 1 (by rfl) ⟨160775, by rfl⟩ : syracuseStep 214367 = 321551) B321551
theorem B214379 : Blo 139791 214379 := bstep (se 1 (by rfl) ⟨160784, by rfl⟩ : syracuseStep 214379 = 321569) B321569
theorem B542081 : Blo 139791 542081 := bstep (se 2 (by rfl) ⟨203280, by rfl⟩ : syracuseStep 542081 = 406561) B406561
theorem B804269 : Blo 139791 804269 := bstep (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) B301601
theorem B476711 : Blo 139791 476711 := bstep (se 1 (by rfl) ⟨357533, by rfl⟩ : syracuseStep 476711 = 715067) B715067
theorem B214607 : Blo 139791 214607 := bstep (se 1 (by rfl) ⟨160955, by rfl⟩ : syracuseStep 214607 = 321911) B321911
theorem B476819 : Blo 139791 476819 := bstep (se 1 (by rfl) ⟨357614, by rfl⟩ : syracuseStep 476819 = 715229) B715229
theorem B214727 : Blo 139791 214727 := bstep (se 1 (by rfl) ⟨161045, by rfl⟩ : syracuseStep 214727 = 322091) B322091
theorem B477035 : Blo 139791 477035 := bstep (se 1 (by rfl) ⟨357776, by rfl⟩ : syracuseStep 477035 = 715553) B715553
theorem B214889 : Blo 139791 214889 := bstep (se 2 (by rfl) ⟨80583, by rfl⟩ : syracuseStep 214889 = 161167) B161167
theorem B477089 : Blo 139791 477089 := bstep (se 2 (by rfl) ⟨178908, by rfl⟩ : syracuseStep 477089 = 357817) B357817
theorem B214967 : Blo 139791 214967 := bstep (se 1 (by rfl) ⟨161225, by rfl⟩ : syracuseStep 214967 = 322451) B322451
theorem B215003 : Blo 139791 215003 := bstep (se 1 (by rfl) ⟨161252, by rfl⟩ : syracuseStep 215003 = 322505) B322505
theorem B542801 : Blo 139791 542801 := bstep (se 2 (by rfl) ⟨203550, by rfl⟩ : syracuseStep 542801 = 407101) B407101
theorem B411895 : Blo 139791 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B215471 : Blo 139791 215471 := bstep (se 1 (by rfl) ⟨161603, by rfl⟩ : syracuseStep 215471 = 323207) B323207
theorem B477683 : Blo 139791 477683 := bstep (se 1 (by rfl) ⟨358262, by rfl⟩ : syracuseStep 477683 = 716525) B716525
theorem B215561 : Blo 139791 215561 := bstep (se 2 (by rfl) ⟨80835, by rfl⟩ : syracuseStep 215561 = 161671) B161671
theorem B543257 : Blo 139791 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B805409 : Blo 139791 805409 := bstep (se 2 (by rfl) ⟨302028, by rfl⟩ : syracuseStep 805409 = 604057) B604057
theorem B215591 : Blo 139791 215591 := bstep (se 1 (by rfl) ⟨161693, by rfl⟩ : syracuseStep 215591 = 323387) B323387
theorem B215675 : Blo 139791 215675 := bstep (se 1 (by rfl) ⟨161756, by rfl⟩ : syracuseStep 215675 = 323513) B323513
theorem B379835 : Blo 139791 379835 := bstep (se 1 (by rfl) ⟨284876, by rfl⟩ : syracuseStep 379835 = 569753) B569753
theorem B478223 : Blo 139791 478223 := bstep (se 1 (by rfl) ⟨358667, by rfl⟩ : syracuseStep 478223 = 717335) B717335
theorem B1068227 : Blo 139791 1068227 := bstep (se 1 (by rfl) ⟨801170, by rfl⟩ : syracuseStep 1068227 = 1602341) B1602341
theorem B314729 : Blo 139791 314729 := bstep (se 2 (by rfl) ⟨118023, by rfl⟩ : syracuseStep 314729 = 236047) B236047
theorem B970157 : Blo 139791 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B478817 : Blo 139791 478817 := bstep (se 2 (by rfl) ⟨179556, by rfl⟩ : syracuseStep 478817 = 359113) B359113
theorem B544441 : Blo 139791 544441 := bstep (se 2 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 544441 = 408331) B408331
theorem B347977 : Blo 139791 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B315323 : Blo 139791 315323 := bstep (se 1 (by rfl) ⟨236492, by rfl⟩ : syracuseStep 315323 = 472985) B472985
theorem B9129995 : Blo 139791 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B315449 : Blo 139791 315449 := bstep (se 2 (by rfl) ⟨118293, by rfl⟩ : syracuseStep 315449 = 236587) B236587
theorem B1986875 : Blo 139791 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B151903 : Blo 139791 151903 := bstep (se 1 (by rfl) ⟨113927, by rfl⟩ : syracuseStep 151903 = 227855) B227855
theorem B315791 : Blo 139791 315791 := bstep (se 1 (by rfl) ⟨236843, by rfl⟩ : syracuseStep 315791 = 473687) B473687
theorem B610841 : Blo 139791 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B905863 : Blo 139791 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B479933 : Blo 139791 479933 := bstep (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) B179975
theorem B971473 : Blo 139791 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B316115 : Blo 139791 316115 := bstep (se 1 (by rfl) ⟨237086, by rfl⟩ : syracuseStep 316115 = 474173) B474173
theorem B480043 : Blo 139791 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B578411 : Blo 139791 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B709559 : Blo 139791 709559 := bstep (se 1 (by rfl) ⟨532169, by rfl⟩ : syracuseStep 709559 = 1064339) B1064339
theorem B447419 : Blo 139791 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B3724289 : Blo 139791 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B480275 : Blo 139791 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B480599 : Blo 139791 480599 := bstep (se 1 (by rfl) ⟨360449, by rfl⟩ : syracuseStep 480599 = 720899) B720899
theorem B480755 : Blo 139791 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B546329 : Blo 139791 546329 := bstep (se 2 (by rfl) ⟨204873, by rfl⟩ : syracuseStep 546329 = 409747) B409747
theorem B317051 : Blo 139791 317051 := bstep (se 1 (by rfl) ⟨237788, by rfl⟩ : syracuseStep 317051 = 475577) B475577
theorem B382603 : Blo 139791 382603 := bstep (se 1 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 382603 = 573905) B573905
theorem B317177 : Blo 139791 317177 := bstep (se 2 (by rfl) ⟨118941, by rfl⟩ : syracuseStep 317177 = 237883) B237883
theorem B513911 : Blo 139791 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B317447 : Blo 139791 317447 := bstep (se 1 (by rfl) ⟨238085, by rfl⟩ : syracuseStep 317447 = 476171) B476171
theorem B317519 : Blo 139791 317519 := bstep (se 1 (by rfl) ⟨238139, by rfl⟩ : syracuseStep 317519 = 476279) B476279
theorem B711017 : Blo 139791 711017 := bstep (se 2 (by rfl) ⟨266631, by rfl⟩ : syracuseStep 711017 = 533263) B533263
theorem B481679 : Blo 139791 481679 := bstep (se 1 (by rfl) ⟨361259, by rfl⟩ : syracuseStep 481679 = 722519) B722519
theorem B317915 : Blo 139791 317915 := bstep (se 1 (by rfl) ⟨238436, by rfl⟩ : syracuseStep 317915 = 476873) B476873
theorem B1137361 : Blo 139791 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B482003 : Blo 139791 482003 := bstep (se 1 (by rfl) ⟨361502, by rfl⟩ : syracuseStep 482003 = 723005) B723005
theorem B318383 : Blo 139791 318383 := bstep (se 1 (by rfl) ⟨238787, by rfl⟩ : syracuseStep 318383 = 477575) B477575
theorem B384007 : Blo 139791 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B318635 : Blo 139791 318635 := bstep (se 1 (by rfl) ⟨238976, by rfl⟩ : syracuseStep 318635 = 477953) B477953
theorem B3661037 : Blo 139791 3661037 := bstep (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) B1372889
theorem B2055415 : Blo 139791 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B319175 : Blo 139791 319175 := bstep (se 1 (by rfl) ⟨239381, by rfl⟩ : syracuseStep 319175 = 478763) B478763
theorem B614137 : Blo 139791 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B483191 : Blo 139791 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B679873 : Blo 139791 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B254009 : Blo 139791 254009 := bstep (se 2 (by rfl) ⟨95253, by rfl⟩ : syracuseStep 254009 = 190507) B190507
theorem B483407 : Blo 139791 483407 := bstep (se 1 (by rfl) ⟨362555, by rfl⟩ : syracuseStep 483407 = 725111) B725111
theorem B2744549 : Blo 139791 2744549 := bstep (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) B514603
theorem B286967 : Blo 139791 286967 := bstep (se 1 (by rfl) ⟨215225, by rfl⟩ : syracuseStep 286967 = 430451) B430451
theorem B1007873 : Blo 139791 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B1794433 : Blo 139791 1794433 := bstep (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) B1345825
theorem B483785 : Blo 139791 483785 := bstep (se 2 (by rfl) ⟨181419, by rfl⟩ : syracuseStep 483785 = 362839) B362839
theorem B811529 : Blo 139791 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B320039 : Blo 139791 320039 := bstep (se 1 (by rfl) ⟨240029, by rfl⟩ : syracuseStep 320039 = 480059) B480059
theorem B3465787 : Blo 139791 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B1106567 : Blo 139791 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B484055 : Blo 139791 484055 := bstep (se 1 (by rfl) ⟨363041, by rfl⟩ : syracuseStep 484055 = 726083) B726083
theorem B3105539 : Blo 139791 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B910187 : Blo 139791 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B320363 : Blo 139791 320363 := bstep (se 1 (by rfl) ⟨240272, by rfl⟩ : syracuseStep 320363 = 480545) B480545
theorem B320417 : Blo 139791 320417 := bstep (se 2 (by rfl) ⟨120156, by rfl⟩ : syracuseStep 320417 = 240313) B240313
theorem B484271 : Blo 139791 484271 := bstep (se 1 (by rfl) ⟨363203, by rfl⟩ : syracuseStep 484271 = 726407) B726407
theorem B287707 : Blo 139791 287707 := bstep (se 1 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 287707 = 431561) B431561
theorem B320759 : Blo 139791 320759 := bstep (se 1 (by rfl) ⟨240569, by rfl⟩ : syracuseStep 320759 = 481139) B481139
theorem B1369507 : Blo 139791 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B288427 : Blo 139791 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B354041 : Blo 139791 354041 := bstep (se 2 (by rfl) ⟨132765, by rfl⟩ : syracuseStep 354041 = 265531) B265531
theorem B2713337 : Blo 139791 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B812843 : Blo 139791 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B321353 : Blo 139791 321353 := bstep (se 2 (by rfl) ⟨120507, by rfl⟩ : syracuseStep 321353 = 241015) B241015
theorem B1599425 : Blo 139791 1599425 := bstep (se 2 (by rfl) ⟨599784, by rfl⟩ : syracuseStep 1599425 = 1199569) B1199569
theorem B157819 : Blo 139791 157819 := bstep (se 1 (by rfl) ⟨118364, by rfl⟩ : syracuseStep 157819 = 236729) B236729
theorem B2418821 : Blo 139791 2418821 := bstep (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) B453529
theorem B321707 : Blo 139791 321707 := bstep (se 1 (by rfl) ⟨241280, by rfl⟩ : syracuseStep 321707 = 482561) B482561
theorem B1566977 : Blo 139791 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1075517 : Blo 139791 1075517 := bstep (se 3 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 1075517 = 403319) B403319
theorem B354689 : Blo 139791 354689 := bstep (se 2 (by rfl) ⟨133008, by rfl⟩ : syracuseStep 354689 = 266017) B266017
theorem B158287 : Blo 139791 158287 := bstep (se 1 (by rfl) ⟨118715, by rfl⟩ : syracuseStep 158287 = 237431) B237431
theorem B322145 : Blo 139791 322145 := bstep (se 2 (by rfl) ⟨120804, by rfl⟩ : syracuseStep 322145 = 241609) B241609
theorem B256841 : Blo 139791 256841 := bstep (se 2 (by rfl) ⟨96315, by rfl⟩ : syracuseStep 256841 = 192631) B192631
theorem B322487 : Blo 139791 322487 := bstep (se 1 (by rfl) ⟨241865, by rfl⟩ : syracuseStep 322487 = 483731) B483731
theorem B158683 : Blo 139791 158683 := bstep (se 1 (by rfl) ⟨119012, by rfl⟩ : syracuseStep 158683 = 238025) B238025
theorem B355499 : Blo 139791 355499 := bstep (se 1 (by rfl) ⟨266624, by rfl⟩ : syracuseStep 355499 = 533249) B533249
theorem B683255 : Blo 139791 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B454031 : Blo 139791 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B159151 : Blo 139791 159151 := bstep (se 1 (by rfl) ⟨119363, by rfl⟩ : syracuseStep 159151 = 238727) B238727
theorem B323081 : Blo 139791 323081 := bstep (se 2 (by rfl) ⟨121155, by rfl⟩ : syracuseStep 323081 = 242311) B242311
theorem B290503 : Blo 139791 290503 := bstep (se 1 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 290503 = 435755) B435755
theorem B225119 : Blo 139791 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B159583 : Blo 139791 159583 := bstep (se 1 (by rfl) ⟨119687, by rfl⟩ : syracuseStep 159583 = 239375) B239375
theorem B323423 : Blo 139791 323423 := bstep (se 1 (by rfl) ⟨242567, by rfl⟩ : syracuseStep 323423 = 485135) B485135
theorem B356359 : Blo 139791 356359 := bstep (se 1 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 356359 = 534539) B534539
theorem B684121 : Blo 139791 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B618653 : Blo 139791 618653 := bstep (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) B231995
theorem B159943 : Blo 139791 159943 := bstep (se 1 (by rfl) ⟨119957, by rfl⟩ : syracuseStep 159943 = 239915) B239915
theorem B455017 : Blo 139791 455017 := bstep (se 2 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 455017 = 341263) B341263
theorem B5534081 : Blo 139791 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B356987 : Blo 139791 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B717497 : Blo 139791 717497 := bstep (se 2 (by rfl) ⟨269061, by rfl⟩ : syracuseStep 717497 = 538123) B538123
theorem B258889 : Blo 139791 258889 := bstep (se 2 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 258889 = 194167) B194167
theorem B357281 : Blo 139791 357281 := bstep (se 2 (by rfl) ⟨133980, by rfl⟩ : syracuseStep 357281 = 267961) B267961
theorem B160807 : Blo 139791 160807 := bstep (se 1 (by rfl) ⟨120605, by rfl⟩ : syracuseStep 160807 = 241211) B241211
theorem B259471 : Blo 139791 259471 := bstep (se 1 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 259471 = 389207) B389207
theorem B194087 : Blo 139791 194087 := bstep (se 1 (by rfl) ⟨145565, by rfl⟩ : syracuseStep 194087 = 291131) B291131
theorem B456491 : Blo 139791 456491 := bstep (se 1 (by rfl) ⟨342368, by rfl⟩ : syracuseStep 456491 = 684737) B684737
theorem B522625 : Blo 139791 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B358951 : Blo 139791 358951 := bstep (se 1 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 358951 = 538427) B538427
theorem B1080067 : Blo 139791 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B359275 : Blo 139791 359275 := bstep (se 1 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 359275 = 538913) B538913
theorem B457579 : Blo 139791 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B1276901 : Blo 139791 1276901 := bstep (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) B239419
theorem B1015031 : Blo 139791 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B359923 : Blo 139791 359923 := bstep (se 1 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 359923 = 539885) B539885
theorem B425915 : Blo 139791 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B1048627 : Blo 139791 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B458963 : Blo 139791 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B360713 : Blo 139791 360713 := bstep (se 2 (by rfl) ⟨135267, by rfl⟩ : syracuseStep 360713 = 270535) B270535
theorem B786779 : Blo 139791 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B2392577 : Blo 139791 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B4621049 : Blo 139791 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B361387 : Blo 139791 361387 := bstep (se 1 (by rfl) ⟨271040, by rfl⟩ : syracuseStep 361387 = 542081) B542081
theorem B361705 : Blo 139791 361705 := bstep (se 2 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 361705 = 271279) B271279
theorem B361867 : Blo 139791 361867 := bstep (se 1 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 361867 = 542801) B542801
theorem B362171 : Blo 139791 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B493697 : Blo 139791 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B16714421 : Blo 139791 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B920591 : Blo 139791 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B298279 : Blo 139791 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B364219 : Blo 139791 364219 := bstep (se 1 (by rfl) ⟨273164, by rfl⟩ : syracuseStep 364219 = 546329) B546329
theorem B3149725 : Blo 139791 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B725921 : Blo 139791 725921 := bstep (se 2 (by rfl) ⟨272220, by rfl⟩ : syracuseStep 725921 = 544441) B544441
theorem B267239 : Blo 139791 267239 := bstep (se 1 (by rfl) ⟨200429, by rfl⟩ : syracuseStep 267239 = 400859) B400859
theorem B463969 : Blo 139791 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B398479 : Blo 139791 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B169339 : Blo 139791 169339 := bstep (se 1 (by rfl) ⟨127004, by rfl⟩ : syracuseStep 169339 = 254009) B254009
theorem B398753 : Blo 139791 398753 := bstep (se 2 (by rfl) ⟨149532, by rfl⟩ : syracuseStep 398753 = 299065) B299065
theorem B202537 : Blo 139791 202537 := bstep (se 2 (by rfl) ⟨75951, by rfl⟩ : syracuseStep 202537 = 151903) B151903
theorem B2070359 : Blo 139791 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B1841591 : Blo 139791 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B236027 : Blo 139791 236027 := bstep (se 1 (by rfl) ⟨177020, by rfl⟩ : syracuseStep 236027 = 354041) B354041
theorem B1808891 : Blo 139791 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B1612547 : Blo 139791 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B236459 : Blo 139791 236459 := bstep (se 1 (by rfl) ⟨177344, by rfl⟩ : syracuseStep 236459 = 354689) B354689
theorem B171227 : Blo 139791 171227 := bstep (se 1 (by rfl) ⟨128420, by rfl⟩ : syracuseStep 171227 = 256841) B256841
theorem B203995 : Blo 139791 203995 := bstep (se 1 (by rfl) ⟨152996, by rfl⟩ : syracuseStep 203995 = 305993) B305993
theorem B236999 : Blo 139791 236999 := bstep (se 1 (by rfl) ⟨177749, by rfl⟩ : syracuseStep 236999 = 355499) B355499
theorem B4726349 : Blo 139791 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B302687 : Blo 139791 302687 := bstep (se 1 (by rfl) ⟨227015, by rfl⟩ : syracuseStep 302687 = 454031) B454031
theorem B237991 : Blo 139791 237991 := bstep (se 1 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 237991 = 356987) B356987
theorem B696833 : Blo 139791 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B139839 : Blo 139791 139839 := bstep (se 1 (by rfl) ⟨104879, by rfl⟩ : syracuseStep 139839 = 209759) B209759
theorem B139847 : Blo 139791 139847 := bstep (se 1 (by rfl) ⟨104885, by rfl⟩ : syracuseStep 139847 = 209771) B209771
theorem B238153 : Blo 139791 238153 := bstep (se 2 (by rfl) ⟨89307, by rfl⟩ : syracuseStep 238153 = 178615) B178615
theorem B238187 : Blo 139791 238187 := bstep (se 1 (by rfl) ⟨178640, by rfl⟩ : syracuseStep 238187 = 357281) B357281
theorem B139999 : Blo 139791 139999 := bstep (se 1 (by rfl) ⟨104999, by rfl⟩ : syracuseStep 139999 = 209999) B209999
theorem B336631 : Blo 139791 336631 := bstep (se 1 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 336631 = 504947) B504947
theorem B140079 : Blo 139791 140079 := bstep (se 1 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 140079 = 210119) B210119
theorem B140187 : Blo 139791 140187 := bstep (se 1 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 140187 = 210281) B210281
theorem B1516481 : Blo 139791 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B140239 : Blo 139791 140239 := bstep (se 1 (by rfl) ⟨105179, by rfl⟩ : syracuseStep 140239 = 210359) B210359
theorem B140263 : Blo 139791 140263 := bstep (se 1 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 140263 = 210395) B210395
theorem B304327 : Blo 139791 304327 := bstep (se 1 (by rfl) ⟨228245, by rfl⟩ : syracuseStep 304327 = 456491) B456491
theorem B140575 : Blo 139791 140575 := bstep (se 1 (by rfl) ⟨105431, by rfl⟩ : syracuseStep 140575 = 210863) B210863
theorem B402727 : Blo 139791 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B140635 : Blo 139791 140635 := bstep (se 1 (by rfl) ⟨105476, by rfl⟩ : syracuseStep 140635 = 210953) B210953
theorem B337247 : Blo 139791 337247 := bstep (se 1 (by rfl) ⟨252935, by rfl⟩ : syracuseStep 337247 = 505871) B505871
theorem B140655 : Blo 139791 140655 := bstep (se 1 (by rfl) ⟨105491, by rfl⟩ : syracuseStep 140655 = 210983) B210983
theorem B140711 : Blo 139791 140711 := bstep (se 1 (by rfl) ⟨105533, by rfl⟩ : syracuseStep 140711 = 211067) B211067
theorem B140795 : Blo 139791 140795 := bstep (se 1 (by rfl) ⟨105596, by rfl⟩ : syracuseStep 140795 = 211193) B211193
theorem B534023 : Blo 139791 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B403001 : Blo 139791 403001 := bstep (se 2 (by rfl) ⟨151125, by rfl⟩ : syracuseStep 403001 = 302251) B302251
theorem B140863 : Blo 139791 140863 := bstep (se 1 (by rfl) ⟨105647, by rfl⟩ : syracuseStep 140863 = 211295) B211295
theorem B140871 : Blo 139791 140871 := bstep (se 1 (by rfl) ⟨105653, by rfl⟩ : syracuseStep 140871 = 211307) B211307
theorem B141023 : Blo 139791 141023 := bstep (se 1 (by rfl) ⟨105767, by rfl⟩ : syracuseStep 141023 = 211535) B211535
theorem B141103 : Blo 139791 141103 := bstep (se 1 (by rfl) ⟨105827, by rfl⟩ : syracuseStep 141103 = 211655) B211655
theorem B141211 : Blo 139791 141211 := bstep (se 1 (by rfl) ⟨105908, by rfl⟩ : syracuseStep 141211 = 211817) B211817
theorem B141263 : Blo 139791 141263 := bstep (se 1 (by rfl) ⟨105947, by rfl⟩ : syracuseStep 141263 = 211895) B211895
theorem B272335 : Blo 139791 272335 := bstep (se 1 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 272335 = 408503) B408503
theorem B141287 : Blo 139791 141287 := bstep (se 1 (by rfl) ⟨105965, by rfl⟩ : syracuseStep 141287 = 211931) B211931
theorem B534509 : Blo 139791 534509 := bstep (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) B200441
theorem B600317 : Blo 139791 600317 := bstep (se 3 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 600317 = 225119) B225119
theorem B239881 : Blo 139791 239881 := bstep (se 2 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 239881 = 179911) B179911
theorem B141599 : Blo 139791 141599 := bstep (se 1 (by rfl) ⟨106199, by rfl⟩ : syracuseStep 141599 = 212399) B212399
theorem B141659 : Blo 139791 141659 := bstep (se 1 (by rfl) ⟨106244, by rfl⟩ : syracuseStep 141659 = 212489) B212489
theorem B141679 : Blo 139791 141679 := bstep (se 1 (by rfl) ⟨106259, by rfl⟩ : syracuseStep 141679 = 212519) B212519
theorem B141735 : Blo 139791 141735 := bstep (se 1 (by rfl) ⟨106301, by rfl⟩ : syracuseStep 141735 = 212603) B212603
theorem B534995 : Blo 139791 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B141819 : Blo 139791 141819 := bstep (se 1 (by rfl) ⟨106364, by rfl⟩ : syracuseStep 141819 = 212729) B212729
theorem B141887 : Blo 139791 141887 := bstep (se 1 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 141887 = 212831) B212831
theorem B141895 : Blo 139791 141895 := bstep (se 1 (by rfl) ⟨106421, by rfl⟩ : syracuseStep 141895 = 212843) B212843
theorem B1845949 : Blo 139791 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B142047 : Blo 139791 142047 := bstep (se 1 (by rfl) ⟨106535, by rfl⟩ : syracuseStep 142047 = 213071) B213071
theorem B142127 : Blo 139791 142127 := bstep (se 1 (by rfl) ⟨106595, by rfl⟩ : syracuseStep 142127 = 213191) B213191
theorem B142235 : Blo 139791 142235 := bstep (se 1 (by rfl) ⟨106676, by rfl⟩ : syracuseStep 142235 = 213353) B213353
theorem B142287 : Blo 139791 142287 := bstep (se 1 (by rfl) ⟨106715, by rfl⟩ : syracuseStep 142287 = 213431) B213431
theorem B142311 : Blo 139791 142311 := bstep (se 1 (by rfl) ⟨106733, by rfl⟩ : syracuseStep 142311 = 213467) B213467
theorem B339187 : Blo 139791 339187 := bstep (se 1 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 339187 = 508781) B508781
theorem B142623 : Blo 139791 142623 := bstep (se 1 (by rfl) ⟨106967, by rfl⟩ : syracuseStep 142623 = 213935) B213935
theorem B765245 : Blo 139791 765245 := bstep (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) B286967
theorem B142683 : Blo 139791 142683 := bstep (se 1 (by rfl) ⟨107012, by rfl⟩ : syracuseStep 142683 = 214025) B214025
theorem B142703 : Blo 139791 142703 := bstep (se 1 (by rfl) ⟨107027, by rfl⟩ : syracuseStep 142703 = 214055) B214055
theorem B142759 : Blo 139791 142759 := bstep (se 1 (by rfl) ⟨107069, by rfl⟩ : syracuseStep 142759 = 214139) B214139
theorem B142843 : Blo 139791 142843 := bstep (se 1 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 142843 = 214265) B214265
theorem B142911 : Blo 139791 142911 := bstep (se 1 (by rfl) ⟨107183, by rfl⟩ : syracuseStep 142911 = 214367) B214367
theorem B142919 : Blo 139791 142919 := bstep (se 1 (by rfl) ⟨107189, by rfl⟩ : syracuseStep 142919 = 214379) B214379
theorem B536179 : Blo 139791 536179 := bstep (se 1 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 536179 = 804269) B804269
theorem B241339 : Blo 139791 241339 := bstep (se 1 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 241339 = 362009) B362009
theorem B143071 : Blo 139791 143071 := bstep (se 1 (by rfl) ⟨107303, by rfl⟩ : syracuseStep 143071 = 214607) B214607
theorem B143151 : Blo 139791 143151 := bstep (se 1 (by rfl) ⟨107363, by rfl⟩ : syracuseStep 143151 = 214727) B214727
theorem B143259 : Blo 139791 143259 := bstep (se 1 (by rfl) ⟨107444, by rfl⟩ : syracuseStep 143259 = 214889) B214889
theorem B143311 : Blo 139791 143311 := bstep (se 1 (by rfl) ⟨107483, by rfl⟩ : syracuseStep 143311 = 214967) B214967
theorem B143335 : Blo 139791 143335 := bstep (se 1 (by rfl) ⟨107501, by rfl⟩ : syracuseStep 143335 = 215003) B215003
theorem B3321917 : Blo 139791 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B274537 : Blo 139791 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B143647 : Blo 139791 143647 := bstep (se 1 (by rfl) ⟨107735, by rfl⟩ : syracuseStep 143647 = 215471) B215471
theorem B143707 : Blo 139791 143707 := bstep (se 1 (by rfl) ⟨107780, by rfl⟩ : syracuseStep 143707 = 215561) B215561
theorem B536939 : Blo 139791 536939 := bstep (se 1 (by rfl) ⟨402704, by rfl⟩ : syracuseStep 536939 = 805409) B805409
theorem B143727 : Blo 139791 143727 := bstep (se 1 (by rfl) ⟨107795, by rfl⟩ : syracuseStep 143727 = 215591) B215591
theorem B143783 : Blo 139791 143783 := bstep (se 1 (by rfl) ⟨107837, by rfl⟩ : syracuseStep 143783 = 215675) B215675
theorem B405985 : Blo 139791 405985 := bstep (se 2 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 405985 = 304489) B304489
theorem B242399 : Blo 139791 242399 := bstep (se 1 (by rfl) ⟨181799, by rfl⟩ : syracuseStep 242399 = 363599) B363599
theorem B209819 : Blo 139791 209819 := bstep (se 1 (by rfl) ⟨157364, by rfl⟩ : syracuseStep 209819 = 314729) B314729
theorem B210215 : Blo 139791 210215 := bstep (se 1 (by rfl) ⟨157661, by rfl⟩ : syracuseStep 210215 = 315323) B315323
theorem B210299 : Blo 139791 210299 := bstep (se 1 (by rfl) ⟨157724, by rfl⟩ : syracuseStep 210299 = 315449) B315449
theorem B210425 : Blo 139791 210425 := bstep (se 2 (by rfl) ⟨78909, by rfl⟩ : syracuseStep 210425 = 157819) B157819
theorem B1324583 : Blo 139791 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B210527 : Blo 139791 210527 := bstep (se 1 (by rfl) ⟨157895, by rfl⟩ : syracuseStep 210527 = 315791) B315791
theorem B407227 : Blo 139791 407227 := bstep (se 1 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 407227 = 610841) B610841
theorem B177967 : Blo 139791 177967 := bstep (se 1 (by rfl) ⟨133475, by rfl⟩ : syracuseStep 177967 = 266951) B266951
theorem B210743 : Blo 139791 210743 := bstep (se 1 (by rfl) ⟨158057, by rfl⟩ : syracuseStep 210743 = 316115) B316115
theorem B473039 : Blo 139791 473039 := bstep (se 1 (by rfl) ⟨354779, by rfl⟩ : syracuseStep 473039 = 709559) B709559
theorem B211049 : Blo 139791 211049 := bstep (se 2 (by rfl) ⟨79143, by rfl⟩ : syracuseStep 211049 = 158287) B158287
theorem B178463 : Blo 139791 178463 := bstep (se 1 (by rfl) ⟨133847, by rfl⟩ : syracuseStep 178463 = 267695) B267695
theorem B211367 : Blo 139791 211367 := bstep (se 1 (by rfl) ⟨158525, by rfl⟩ : syracuseStep 211367 = 317051) B317051
theorem B211451 : Blo 139791 211451 := bstep (se 1 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 211451 = 317177) B317177
theorem B801353 : Blo 139791 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B211577 : Blo 139791 211577 := bstep (se 2 (by rfl) ⟨79341, by rfl⟩ : syracuseStep 211577 = 158683) B158683
theorem B211631 : Blo 139791 211631 := bstep (se 1 (by rfl) ⟨158723, by rfl⟩ : syracuseStep 211631 = 317447) B317447
theorem B211679 : Blo 139791 211679 := bstep (se 1 (by rfl) ⟨158759, by rfl⟩ : syracuseStep 211679 = 317519) B317519
theorem B768791 : Blo 139791 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B474011 : Blo 139791 474011 := bstep (se 1 (by rfl) ⟨355508, by rfl⟩ : syracuseStep 474011 = 711017) B711017
theorem B1063853 : Blo 139791 1063853 := bstep (se 3 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 1063853 = 398945) B398945
theorem B211943 : Blo 139791 211943 := bstep (se 1 (by rfl) ⟨158957, by rfl⟩ : syracuseStep 211943 = 317915) B317915
theorem B5160023 : Blo 139791 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B212201 : Blo 139791 212201 := bstep (se 2 (by rfl) ⟨79575, by rfl⟩ : syracuseStep 212201 = 159151) B159151
theorem B212255 : Blo 139791 212255 := bstep (se 1 (by rfl) ⟨159191, by rfl⟩ : syracuseStep 212255 = 318383) B318383
theorem B212423 : Blo 139791 212423 := bstep (se 1 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 212423 = 318635) B318635
theorem B2440691 : Blo 139791 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B310879 : Blo 139791 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B212777 : Blo 139791 212777 := bstep (se 2 (by rfl) ⟨79791, by rfl⟩ : syracuseStep 212777 = 159583) B159583
theorem B212783 : Blo 139791 212783 := bstep (se 1 (by rfl) ⟨159587, by rfl⟩ : syracuseStep 212783 = 319175) B319175
theorem B475037 : Blo 139791 475037 := bstep (se 3 (by rfl) ⟨89069, by rfl⟩ : syracuseStep 475037 = 178139) B178139
theorem B475145 : Blo 139791 475145 := bstep (se 2 (by rfl) ⟨178179, by rfl⟩ : syracuseStep 475145 = 356359) B356359
theorem B671915 : Blo 139791 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B213257 : Blo 139791 213257 := bstep (se 2 (by rfl) ⟨79971, by rfl⟩ : syracuseStep 213257 = 159943) B159943
theorem B11583755 : Blo 139791 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B541019 : Blo 139791 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B213359 : Blo 139791 213359 := bstep (se 1 (by rfl) ⟨160019, by rfl⟩ : syracuseStep 213359 = 320039) B320039
theorem B737711 : Blo 139791 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B606689 : Blo 139791 606689 := bstep (se 2 (by rfl) ⟨227508, by rfl⟩ : syracuseStep 606689 = 455017) B455017
theorem B180731 : Blo 139791 180731 := bstep (se 1 (by rfl) ⟨135548, by rfl⟩ : syracuseStep 180731 = 271097) B271097
theorem B606791 : Blo 139791 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B213575 : Blo 139791 213575 := bstep (se 1 (by rfl) ⟨160181, by rfl⟩ : syracuseStep 213575 = 320363) B320363
theorem B213611 : Blo 139791 213611 := bstep (se 1 (by rfl) ⟨160208, by rfl⟩ : syracuseStep 213611 = 320417) B320417
theorem B9290375 : Blo 139791 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B213839 : Blo 139791 213839 := bstep (se 1 (by rfl) ⟨160379, by rfl⟩ : syracuseStep 213839 = 320759) B320759
theorem B1295297 : Blo 139791 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B640057 : Blo 139791 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B345185 : Blo 139791 345185 := bstep (se 2 (by rfl) ⟨129444, by rfl⟩ : syracuseStep 345185 = 258889) B258889
theorem B541895 : Blo 139791 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B214235 : Blo 139791 214235 := bstep (se 1 (by rfl) ⟨160676, by rfl⟩ : syracuseStep 214235 = 321353) B321353
theorem B1066283 : Blo 139791 1066283 := bstep (se 1 (by rfl) ⟨799712, by rfl⟩ : syracuseStep 1066283 = 1599425) B1599425
theorem B214409 : Blo 139791 214409 := bstep (se 2 (by rfl) ⟨80403, by rfl⟩ : syracuseStep 214409 = 160807) B160807
theorem B214471 : Blo 139791 214471 := bstep (se 1 (by rfl) ⟨160853, by rfl⟩ : syracuseStep 214471 = 321707) B321707
theorem B181703 : Blo 139791 181703 := bstep (se 1 (by rfl) ⟨136277, by rfl⟩ : syracuseStep 181703 = 272555) B272555
theorem B181855 : Blo 139791 181855 := bstep (se 1 (by rfl) ⟨136391, by rfl⟩ : syracuseStep 181855 = 272783) B272783
theorem B214763 : Blo 139791 214763 := bstep (se 1 (by rfl) ⟨161072, by rfl⟩ : syracuseStep 214763 = 322145) B322145
theorem B345961 : Blo 139791 345961 := bstep (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) B259471
theorem B1197929 : Blo 139791 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B1034167 : Blo 139791 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B214991 : Blo 139791 214991 := bstep (se 1 (by rfl) ⟨161243, by rfl⟩ : syracuseStep 214991 = 322487) B322487
theorem B1820677 : Blo 139791 1820677 := bstep (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) B341377
theorem B510137 : Blo 139791 510137 := bstep (se 2 (by rfl) ⟨191301, by rfl⟩ : syracuseStep 510137 = 382603) B382603
theorem B215387 : Blo 139791 215387 := bstep (se 1 (by rfl) ⟨161540, by rfl⟩ : syracuseStep 215387 = 323081) B323081
theorem B215615 : Blo 139791 215615 := bstep (se 1 (by rfl) ⟨161711, by rfl⟩ : syracuseStep 215615 = 323423) B323423
theorem B1067741 : Blo 139791 1067741 := bstep (se 3 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 1067741 = 400403) B400403
theorem B412435 : Blo 139791 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B3689387 : Blo 139791 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B478331 : Blo 139791 478331 := bstep (se 1 (by rfl) ⟨358748, by rfl⟩ : syracuseStep 478331 = 717497) B717497
theorem B314567 : Blo 139791 314567 := bstep (se 1 (by rfl) ⟨235925, by rfl⟩ : syracuseStep 314567 = 471851) B471851
theorem B314617 : Blo 139791 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B1822013 : Blo 139791 1822013 := bstep (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) B683255
theorem B314747 : Blo 139791 314747 := bstep (se 1 (by rfl) ⟨236060, by rfl⟩ : syracuseStep 314747 = 472121) B472121
theorem B478601 : Blo 139791 478601 := bstep (se 2 (by rfl) ⟨179475, by rfl⟩ : syracuseStep 478601 = 358951) B358951
theorem B314873 : Blo 139791 314873 := bstep (se 2 (by rfl) ⟨118077, by rfl⟩ : syracuseStep 314873 = 236155) B236155
theorem B314963 : Blo 139791 314963 := bstep (se 1 (by rfl) ⟨236222, by rfl⟩ : syracuseStep 314963 = 472445) B472445
theorem B1101523 : Blo 139791 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B315143 : Blo 139791 315143 := bstep (se 1 (by rfl) ⟨236357, by rfl⟩ : syracuseStep 315143 = 472715) B472715
theorem B511751 : Blo 139791 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B479033 : Blo 139791 479033 := bstep (se 2 (by rfl) ⟨179637, by rfl⟩ : syracuseStep 479033 = 359275) B359275
theorem B610105 : Blo 139791 610105 := bstep (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) B457579
theorem B708425 : Blo 139791 708425 := bstep (se 2 (by rfl) ⟨265659, by rfl⟩ : syracuseStep 708425 = 531319) B531319
theorem B512009 : Blo 139791 512009 := bstep (se 2 (by rfl) ⟨192003, by rfl⟩ : syracuseStep 512009 = 384007) B384007
theorem B1364035 : Blo 139791 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B2740553 : Blo 139791 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B315755 : Blo 139791 315755 := bstep (se 1 (by rfl) ⟨236816, by rfl⟩ : syracuseStep 315755 = 473633) B473633
theorem B315899 : Blo 139791 315899 := bstep (se 1 (by rfl) ⟨236924, by rfl⟩ : syracuseStep 315899 = 473849) B473849
theorem B11686517 : Blo 139791 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B316025 : Blo 139791 316025 := bstep (se 2 (by rfl) ⟨118509, by rfl⟩ : syracuseStep 316025 = 237019) B237019
theorem B479897 : Blo 139791 479897 := bstep (se 2 (by rfl) ⟨179961, by rfl⟩ : syracuseStep 479897 = 359923) B359923
theorem B316079 : Blo 139791 316079 := bstep (se 1 (by rfl) ⟨237059, by rfl⟩ : syracuseStep 316079 = 474119) B474119
theorem B316151 : Blo 139791 316151 := bstep (se 1 (by rfl) ⟨237113, by rfl⟩ : syracuseStep 316151 = 474227) B474227
theorem B676687 : Blo 139791 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B316331 : Blo 139791 316331 := bstep (se 1 (by rfl) ⟨237248, by rfl⟩ : syracuseStep 316331 = 474497) B474497
theorem B709721 : Blo 139791 709721 := bstep (se 2 (by rfl) ⟨266145, by rfl⟩ : syracuseStep 709721 = 532291) B532291
theorem B382171 : Blo 139791 382171 := bstep (se 1 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 382171 = 573257) B573257
theorem B906497 : Blo 139791 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B283943 : Blo 139791 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B513323 : Blo 139791 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B316871 : Blo 139791 316871 := bstep (se 1 (by rfl) ⟨237653, by rfl⟩ : syracuseStep 316871 = 475307) B475307
theorem B1234379 : Blo 139791 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B2610731 : Blo 139791 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B907037 : Blo 139791 907037 := bstep (se 3 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 907037 = 340139) B340139
theorem B317231 : Blo 139791 317231 := bstep (se 1 (by rfl) ⟨237923, by rfl⟩ : syracuseStep 317231 = 475847) B475847
theorem B481409 : Blo 139791 481409 := bstep (se 2 (by rfl) ⟨180528, by rfl⟩ : syracuseStep 481409 = 361057) B361057
theorem B612481 : Blo 139791 612481 := bstep (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) B459361
theorem B547069 : Blo 139791 547069 := bstep (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) B205151
theorem B317807 : Blo 139791 317807 := bstep (se 1 (by rfl) ⟨238355, by rfl⟩ : syracuseStep 317807 = 476711) B476711
theorem B317879 : Blo 139791 317879 := bstep (se 1 (by rfl) ⟨238409, by rfl⟩ : syracuseStep 317879 = 476819) B476819
theorem B481787 : Blo 139791 481787 := bstep (se 1 (by rfl) ⟨361340, by rfl⟩ : syracuseStep 481787 = 722681) B722681
theorem B318023 : Blo 139791 318023 := bstep (se 1 (by rfl) ⟨238517, by rfl⟩ : syracuseStep 318023 = 477035) B477035
theorem B318059 : Blo 139791 318059 := bstep (se 1 (by rfl) ⟨238544, by rfl⟩ : syracuseStep 318059 = 477089) B477089
theorem B383609 : Blo 139791 383609 := bstep (se 2 (by rfl) ⟨143853, by rfl⟩ : syracuseStep 383609 = 287707) B287707
theorem B482219 : Blo 139791 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B1072115 : Blo 139791 1072115 := bstep (se 1 (by rfl) ⟨804086, by rfl⟩ : syracuseStep 1072115 = 1608173) B1608173
theorem B318455 : Blo 139791 318455 := bstep (se 1 (by rfl) ⟨238841, by rfl⟩ : syracuseStep 318455 = 477683) B477683
theorem B449725 : Blo 139791 449725 := bstep (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) B168647
theorem B1826009 : Blo 139791 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B253223 : Blo 139791 253223 := bstep (se 1 (by rfl) ⟨189917, by rfl⟩ : syracuseStep 253223 = 379835) B379835
theorem B318815 : Blo 139791 318815 := bstep (se 1 (by rfl) ⟨239111, by rfl⟩ : syracuseStep 318815 = 478223) B478223
theorem B482759 : Blo 139791 482759 := bstep (se 1 (by rfl) ⟨362069, by rfl⟩ : syracuseStep 482759 = 724139) B724139
theorem B712151 : Blo 139791 712151 := bstep (se 1 (by rfl) ⟨534113, by rfl⟩ : syracuseStep 712151 = 1068227) B1068227
theorem B384569 : Blo 139791 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B319211 : Blo 139791 319211 := bstep (se 1 (by rfl) ⟨239408, by rfl⟩ : syracuseStep 319211 = 478817) B478817
theorem B483083 : Blo 139791 483083 := bstep (se 1 (by rfl) ⟨362312, by rfl⟩ : syracuseStep 483083 = 724625) B724625
theorem B319337 : Blo 139791 319337 := bstep (se 2 (by rfl) ⟨119751, by rfl⟩ : syracuseStep 319337 = 239503) B239503
theorem B6086663 : Blo 139791 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B483353 : Blo 139791 483353 := bstep (se 2 (by rfl) ⟨181257, by rfl⟩ : syracuseStep 483353 = 362515) B362515
theorem B549193 : Blo 139791 549193 := bstep (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) B411895
theorem B1073573 : Blo 139791 1073573 := bstep (se 4 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 1073573 = 201295) B201295
theorem B319955 : Blo 139791 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B385607 : Blo 139791 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B746081 : Blo 139791 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B2482859 : Blo 139791 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B320183 : Blo 139791 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B320399 : Blo 139791 320399 := bstep (se 1 (by rfl) ⟨240299, by rfl⟩ : syracuseStep 320399 = 480599) B480599
theorem B320503 : Blo 139791 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B484595 : Blo 139791 484595 := bstep (se 1 (by rfl) ⟨363446, by rfl⟩ : syracuseStep 484595 = 726893) B726893
theorem B288031 : Blo 139791 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B484703 : Blo 139791 484703 := bstep (se 1 (by rfl) ⟨363527, by rfl⟩ : syracuseStep 484703 = 727055) B727055
theorem B517565 : Blo 139791 517565 := bstep (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) B194087
theorem B157279 : Blo 139791 157279 := bstep (se 1 (by rfl) ⟨117959, by rfl⟩ : syracuseStep 157279 = 235919) B235919
theorem B321119 : Blo 139791 321119 := bstep (se 1 (by rfl) ⟨240839, by rfl⟩ : syracuseStep 321119 = 481679) B481679
theorem B321335 : Blo 139791 321335 := bstep (se 1 (by rfl) ⟨241001, by rfl⟩ : syracuseStep 321335 = 482003) B482003
theorem B321641 : Blo 139791 321641 := bstep (se 2 (by rfl) ⟨120615, by rfl⟩ : syracuseStep 321641 = 241231) B241231
theorem B387337 : Blo 139791 387337 := bstep (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) B290503
theorem B1370429 : Blo 139791 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B551279 : Blo 139791 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B322127 : Blo 139791 322127 := bstep (se 1 (by rfl) ⟨241595, by rfl⟩ : syracuseStep 322127 = 483191) B483191
theorem B158431 : Blo 139791 158431 := bstep (se 1 (by rfl) ⟨118823, by rfl⟩ : syracuseStep 158431 = 237647) B237647
theorem B322271 : Blo 139791 322271 := bstep (se 1 (by rfl) ⟨241703, by rfl⟩ : syracuseStep 322271 = 483407) B483407
theorem B355063 : Blo 139791 355063 := bstep (se 1 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 355063 = 532595) B532595
theorem B912161 : Blo 139791 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B1829699 : Blo 139791 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B387965 : Blo 139791 387965 := bstep (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) B145487
theorem B322523 : Blo 139791 322523 := bstep (se 1 (by rfl) ⟨241892, by rfl⟩ : syracuseStep 322523 = 483785) B483785
theorem B355367 : Blo 139791 355367 := bstep (se 1 (by rfl) ⟨266525, by rfl⟩ : syracuseStep 355367 = 533051) B533051
theorem B322703 : Blo 139791 322703 := bstep (se 1 (by rfl) ⟨242027, by rfl⟩ : syracuseStep 322703 = 484055) B484055
theorem B322793 : Blo 139791 322793 := bstep (se 2 (by rfl) ⟨121047, by rfl⟩ : syracuseStep 322793 = 242095) B242095
theorem B159007 : Blo 139791 159007 := bstep (se 1 (by rfl) ⟨119255, by rfl⟩ : syracuseStep 159007 = 238511) B238511
theorem B322847 : Blo 139791 322847 := bstep (se 1 (by rfl) ⟨242135, by rfl⟩ : syracuseStep 322847 = 484271) B484271
theorem B1600883 : Blo 139791 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B290171 : Blo 139791 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B1207817 : Blo 139791 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B159295 : Blo 139791 159295 := bstep (se 1 (by rfl) ⟨119471, by rfl⟩ : syracuseStep 159295 = 238943) B238943
theorem B323369 : Blo 139791 323369 := bstep (se 2 (by rfl) ⟨121263, by rfl⟩ : syracuseStep 323369 = 242527) B242527
theorem B717011 : Blo 139791 717011 := bstep (se 1 (by rfl) ⟨537758, by rfl⟩ : syracuseStep 717011 = 1075517) B1075517
theorem B1208591 : Blo 139791 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B356633 : Blo 139791 356633 := bstep (se 2 (by rfl) ⟨133737, by rfl⟩ : syracuseStep 356633 = 267475) B267475
theorem B160123 : Blo 139791 160123 := bstep (se 1 (by rfl) ⟨120092, by rfl⟩ : syracuseStep 160123 = 240185) B240185
theorem B1930027 : Blo 139791 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B160591 : Blo 139791 160591 := bstep (se 1 (by rfl) ⟨120443, by rfl⟩ : syracuseStep 160591 = 240887) B240887
theorem B357473 : Blo 139791 357473 := bstep (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) B268105
theorem B685199 : Blo 139791 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B160987 : Blo 139791 160987 := bstep (se 1 (by rfl) ⟨120740, by rfl⟩ : syracuseStep 160987 = 241481) B241481
theorem B685351 : Blo 139791 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B161275 : Blo 139791 161275 := bstep (se 1 (by rfl) ⟨120956, by rfl⟩ : syracuseStep 161275 = 241913) B241913
theorem B456349 : Blo 139791 456349 := bstep (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) B171131
theorem B161455 : Blo 139791 161455 := bstep (se 1 (by rfl) ⟨121091, by rfl⟩ : syracuseStep 161455 = 242183) B242183
theorem B161743 : Blo 139791 161743 := bstep (se 1 (by rfl) ⟨121307, by rfl⟩ : syracuseStep 161743 = 242615) B242615
theorem B5142629 : Blo 139791 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B1440089 : Blo 139791 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B2587085 : Blo 139791 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B358931 : Blo 139791 358931 := bstep (se 1 (by rfl) ⟨269198, by rfl⟩ : syracuseStep 358931 = 538397) B538397
theorem B359387 : Blo 139791 359387 := bstep (se 1 (by rfl) ⟨269540, by rfl⟩ : syracuseStep 359387 = 539081) B539081
theorem B982205 : Blo 139791 982205 := bstep (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) B368327
theorem B359711 : Blo 139791 359711 := bstep (se 1 (by rfl) ⟨269783, by rfl⟩ : syracuseStep 359711 = 539567) B539567
theorem B851267 : Blo 139791 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B327073 : Blo 139791 327073 := bstep (se 2 (by rfl) ⟨122652, by rfl⟩ : syracuseStep 327073 = 245305) B245305
theorem B818849 : Blo 139791 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B360247 : Blo 139791 360247 := bstep (se 1 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 360247 = 540371) B540371
theorem B524519 : Blo 139791 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B491807 : Blo 139791 491807 := bstep (se 1 (by rfl) ⟨368855, by rfl⟩ : syracuseStep 491807 = 737711) B737711
theorem B6193583 : Blo 139791 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B3080699 : Blo 139791 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B230123 : Blo 139791 230123 := bstep (se 1 (by rfl) ⟨172592, by rfl⟩ : syracuseStep 230123 = 345185) B345185
theorem B1442717 : Blo 139791 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B853213 : Blo 139791 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B427337 : Blo 139791 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B853409 : Blo 139791 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B329131 : Blo 139791 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B6620957 : Blo 139791 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B11142947 : Blo 139791 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B2459591 : Blo 139791 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B1214675 : Blo 139791 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B1378889 : Blo 139791 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B363113 : Blo 139791 363113 := bstep (se 2 (by rfl) ⟨136167, by rfl⟩ : syracuseStep 363113 = 272335) B272335
theorem B2427569 : Blo 139791 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B1445053 : Blo 139791 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B757181 : Blo 139791 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B2461265 : Blo 139791 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B265835 : Blo 139791 265835 := bstep (se 1 (by rfl) ⟨199376, by rfl⟩ : syracuseStep 265835 = 398753) B398753
theorem B1740487 : Blo 139791 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B1380239 : Blo 139791 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B2199653 : Blo 139791 2199653 := bstep (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) B412435
theorem B1217339 : Blo 139791 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B168815 : Blo 139791 168815 := bstep (se 1 (by rfl) ⟨126611, by rfl⟩ : syracuseStep 168815 = 253223) B253223
theorem B3150899 : Blo 139791 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B201791 : Blo 139791 201791 := bstep (se 1 (by rfl) ⟨151343, by rfl⟩ : syracuseStep 201791 = 302687) B302687
theorem B4199633 : Blo 139791 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B366049 : Blo 139791 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B464555 : Blo 139791 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B497387 : Blo 139791 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B268667 : Blo 139791 268667 := bstep (se 1 (by rfl) ⟨201500, by rfl⟩ : syracuseStep 268667 = 403001) B403001
theorem B400211 : Blo 139791 400211 := bstep (se 1 (by rfl) ⟨300158, by rfl⟩ : syracuseStep 400211 = 600317) B600317
theorem B531305 : Blo 139791 531305 := bstep (se 2 (by rfl) ⟨199239, by rfl⟩ : syracuseStep 531305 = 398479) B398479
theorem B367519 : Blo 139791 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B1219799 : Blo 139791 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B236911 : Blo 139791 236911 := bstep (se 1 (by rfl) ⟨177683, by rfl⟩ : syracuseStep 236911 = 355367) B355367
theorem B270049 : Blo 139791 270049 := bstep (se 2 (by rfl) ⟨101268, by rfl⟩ : syracuseStep 270049 = 202537) B202537
theorem B237289 : Blo 139791 237289 := bstep (se 2 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 237289 = 177967) B177967
theorem B237755 : Blo 139791 237755 := bstep (se 1 (by rfl) ⟨178316, by rfl⟩ : syracuseStep 237755 = 356633) B356633
theorem B729425 : Blo 139791 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B139879 : Blo 139791 139879 := bstep (se 1 (by rfl) ⟨104909, by rfl⟩ : syracuseStep 139879 = 209819) B209819
theorem B238315 : Blo 139791 238315 := bstep (se 1 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 238315 = 357473) B357473
theorem B2040653 : Blo 139791 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B2270045 : Blo 139791 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B140143 : Blo 139791 140143 := bstep (se 1 (by rfl) ⟨105107, by rfl⟩ : syracuseStep 140143 = 210215) B210215
theorem B140199 : Blo 139791 140199 := bstep (se 1 (by rfl) ⟨105149, by rfl⟩ : syracuseStep 140199 = 210299) B210299
theorem B1942501 : Blo 139791 1942501 := bstep (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) B364219
theorem B140283 : Blo 139791 140283 := bstep (se 1 (by rfl) ⟨105212, by rfl⟩ : syracuseStep 140283 = 210425) B210425
theorem B140351 : Blo 139791 140351 := bstep (se 1 (by rfl) ⟨105263, by rfl⟩ : syracuseStep 140351 = 210527) B210527
theorem B140495 : Blo 139791 140495 := bstep (se 1 (by rfl) ⟨105371, by rfl⟩ : syracuseStep 140495 = 210743) B210743
theorem B140699 : Blo 139791 140699 := bstep (se 1 (by rfl) ⟨105524, by rfl⟩ : syracuseStep 140699 = 211049) B211049
theorem B960059 : Blo 139791 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B599633 : Blo 139791 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B140911 : Blo 139791 140911 := bstep (se 1 (by rfl) ⟨105683, by rfl⟩ : syracuseStep 140911 = 211367) B211367
theorem B271993 : Blo 139791 271993 := bstep (se 2 (by rfl) ⟨101997, by rfl⟩ : syracuseStep 271993 = 203995) B203995
theorem B140967 : Blo 139791 140967 := bstep (se 1 (by rfl) ⟨105725, by rfl⟩ : syracuseStep 140967 = 211451) B211451
theorem B239287 : Blo 139791 239287 := bstep (se 1 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 239287 = 358931) B358931
theorem B534235 : Blo 139791 534235 := bstep (se 1 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 534235 = 801353) B801353
theorem B141051 : Blo 139791 141051 := bstep (se 1 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 141051 = 211577) B211577
theorem B141087 : Blo 139791 141087 := bstep (se 1 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 141087 = 211631) B211631
theorem B141119 : Blo 139791 141119 := bstep (se 1 (by rfl) ⟨105839, by rfl⟩ : syracuseStep 141119 = 211679) B211679
theorem B436097 : Blo 139791 436097 := bstep (se 2 (by rfl) ⟨163536, by rfl⟩ : syracuseStep 436097 = 327073) B327073
theorem B1845125 : Blo 139791 1845125 := bstep (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) B345961
theorem B239591 : Blo 139791 239591 := bstep (se 1 (by rfl) ⟨179693, by rfl⟩ : syracuseStep 239591 = 359387) B359387
theorem B141295 : Blo 139791 141295 := bstep (se 1 (by rfl) ⟨105971, by rfl⟩ : syracuseStep 141295 = 211943) B211943
theorem B141467 : Blo 139791 141467 := bstep (se 1 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 141467 = 212201) B212201
theorem B141503 : Blo 139791 141503 := bstep (se 1 (by rfl) ⟨106127, by rfl⟩ : syracuseStep 141503 = 212255) B212255
theorem B239807 : Blo 139791 239807 := bstep (se 1 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 239807 = 359711) B359711
theorem B141615 : Blo 139791 141615 := bstep (se 1 (by rfl) ⟨106211, by rfl⟩ : syracuseStep 141615 = 212423) B212423
theorem B141851 : Blo 139791 141851 := bstep (se 1 (by rfl) ⟨106388, by rfl⟩ : syracuseStep 141851 = 212777) B212777
theorem B141855 : Blo 139791 141855 := bstep (se 1 (by rfl) ⟨106391, by rfl⟩ : syracuseStep 141855 = 212783) B212783
theorem B305975 : Blo 139791 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B142171 : Blo 139791 142171 := bstep (se 1 (by rfl) ⟨106628, by rfl⟩ : syracuseStep 142171 = 213257) B213257
theorem B240475 : Blo 139791 240475 := bstep (se 1 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 240475 = 360713) B360713
theorem B142239 : Blo 139791 142239 := bstep (se 1 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 142239 = 213359) B213359
theorem B404459 : Blo 139791 404459 := bstep (se 1 (by rfl) ⟨303344, by rfl⟩ : syracuseStep 404459 = 606689) B606689
theorem B404527 : Blo 139791 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B142383 : Blo 139791 142383 := bstep (se 1 (by rfl) ⟨106787, by rfl⟩ : syracuseStep 142383 = 213575) B213575
theorem B142407 : Blo 139791 142407 := bstep (se 1 (by rfl) ⟨106805, by rfl⟩ : syracuseStep 142407 = 213611) B213611
theorem B732257 : Blo 139791 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B142559 : Blo 139791 142559 := bstep (se 1 (by rfl) ⟨106919, by rfl⟩ : syracuseStep 142559 = 213839) B213839
theorem B863531 : Blo 139791 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B142823 : Blo 139791 142823 := bstep (se 1 (by rfl) ⟨107117, by rfl⟩ : syracuseStep 142823 = 214235) B214235
theorem B142939 : Blo 139791 142939 := bstep (se 1 (by rfl) ⟨107204, by rfl⟩ : syracuseStep 142939 = 214409) B214409
theorem B241447 : Blo 139791 241447 := bstep (se 1 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 241447 = 362171) B362171
theorem B143175 : Blo 139791 143175 := bstep (se 1 (by rfl) ⟨107381, by rfl⟩ : syracuseStep 143175 = 214763) B214763
theorem B798619 : Blo 139791 798619 := bstep (se 1 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 798619 = 1197929) B1197929
theorem B143327 : Blo 139791 143327 := bstep (se 1 (by rfl) ⟨107495, by rfl⟩ : syracuseStep 143327 = 214991) B214991
theorem B340091 : Blo 139791 340091 := bstep (se 1 (by rfl) ⟨255068, by rfl⟩ : syracuseStep 340091 = 510137) B510137
theorem B1028285 : Blo 139791 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B143591 : Blo 139791 143591 := bstep (se 1 (by rfl) ⟨107693, by rfl⟩ : syracuseStep 143591 = 215387) B215387
theorem B405769 : Blo 139791 405769 := bstep (se 2 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 405769 = 304327) B304327
theorem B143743 : Blo 139791 143743 := bstep (se 1 (by rfl) ⟨107807, by rfl⟩ : syracuseStep 143743 = 215615) B215615
theorem B536969 : Blo 139791 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B209705 : Blo 139791 209705 := bstep (se 2 (by rfl) ⟨78639, by rfl⟩ : syracuseStep 209705 = 157279) B157279
theorem B242473 : Blo 139791 242473 := bstep (se 2 (by rfl) ⟨90927, by rfl⟩ : syracuseStep 242473 = 181855) B181855
theorem B209711 : Blo 139791 209711 := bstep (se 1 (by rfl) ⟨157283, by rfl⟩ : syracuseStep 209711 = 314567) B314567
theorem B209831 : Blo 139791 209831 := bstep (se 1 (by rfl) ⟨157373, by rfl⟩ : syracuseStep 209831 = 314747) B314747
theorem B209915 : Blo 139791 209915 := bstep (se 1 (by rfl) ⟨157436, by rfl⟩ : syracuseStep 209915 = 314873) B314873
theorem B209975 : Blo 139791 209975 := bstep (se 1 (by rfl) ⟨157481, by rfl⟩ : syracuseStep 209975 = 314963) B314963
theorem B210095 : Blo 139791 210095 := bstep (se 1 (by rfl) ⟨157571, by rfl⟩ : syracuseStep 210095 = 315143) B315143
theorem B341167 : Blo 139791 341167 := bstep (se 1 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 341167 = 511751) B511751
theorem B472283 : Blo 139791 472283 := bstep (se 1 (by rfl) ⟨354212, by rfl⟩ : syracuseStep 472283 = 708425) B708425
theorem B341339 : Blo 139791 341339 := bstep (se 1 (by rfl) ⟨256004, by rfl⟩ : syracuseStep 341339 = 512009) B512009
theorem B210503 : Blo 139791 210503 := bstep (se 1 (by rfl) ⟨157877, by rfl⟩ : syracuseStep 210503 = 315755) B315755
theorem B210599 : Blo 139791 210599 := bstep (se 1 (by rfl) ⟨157949, by rfl⟩ : syracuseStep 210599 = 315899) B315899
theorem B210683 : Blo 139791 210683 := bstep (se 1 (by rfl) ⟨158012, by rfl⟩ : syracuseStep 210683 = 316025) B316025
theorem B210719 : Blo 139791 210719 := bstep (se 1 (by rfl) ⟨158039, by rfl⟩ : syracuseStep 210719 = 316079) B316079
theorem B210767 : Blo 139791 210767 := bstep (se 1 (by rfl) ⟨158075, by rfl⟩ : syracuseStep 210767 = 316151) B316151
theorem B210887 : Blo 139791 210887 := bstep (se 1 (by rfl) ⟨158165, by rfl⟩ : syracuseStep 210887 = 316331) B316331
theorem B473147 : Blo 139791 473147 := bstep (se 1 (by rfl) ⟨354860, by rfl⟩ : syracuseStep 473147 = 709721) B709721
theorem B604331 : Blo 139791 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B342215 : Blo 139791 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B211241 : Blo 139791 211241 := bstep (se 2 (by rfl) ⟨79215, by rfl⟩ : syracuseStep 211241 = 158431) B158431
theorem B211247 : Blo 139791 211247 := bstep (se 1 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 211247 = 316871) B316871
theorem B473417 : Blo 139791 473417 := bstep (se 2 (by rfl) ⟨177531, by rfl⟩ : syracuseStep 473417 = 355063) B355063
theorem B604691 : Blo 139791 604691 := bstep (se 1 (by rfl) ⟨453518, by rfl⟩ : syracuseStep 604691 = 907037) B907037
theorem B3291677 : Blo 139791 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B211487 : Blo 139791 211487 := bstep (se 1 (by rfl) ⟨158615, by rfl⟩ : syracuseStep 211487 = 317231) B317231
theorem B211871 : Blo 139791 211871 := bstep (se 1 (by rfl) ⟨158903, by rfl⟩ : syracuseStep 211871 = 317807) B317807
theorem B211919 : Blo 139791 211919 := bstep (se 1 (by rfl) ⟨158939, by rfl⟩ : syracuseStep 211919 = 317879) B317879
theorem B1227727 : Blo 139791 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B212009 : Blo 139791 212009 := bstep (se 2 (by rfl) ⟨79503, by rfl⟩ : syracuseStep 212009 = 159007) B159007
theorem B212015 : Blo 139791 212015 := bstep (se 1 (by rfl) ⟨159011, by rfl⟩ : syracuseStep 212015 = 318023) B318023
theorem B212039 : Blo 139791 212039 := bstep (se 1 (by rfl) ⟨159029, by rfl⟩ : syracuseStep 212039 = 318059) B318059
theorem B212303 : Blo 139791 212303 := bstep (se 1 (by rfl) ⟨159227, by rfl⟩ : syracuseStep 212303 = 318455) B318455
theorem B212393 : Blo 139791 212393 := bstep (se 2 (by rfl) ⟨79647, by rfl⟩ : syracuseStep 212393 = 159295) B159295
theorem B212543 : Blo 139791 212543 := bstep (se 1 (by rfl) ⟨159407, by rfl⟩ : syracuseStep 212543 = 318815) B318815
theorem B474767 : Blo 139791 474767 := bstep (se 1 (by rfl) ⟨356075, by rfl⟩ : syracuseStep 474767 = 712151) B712151
theorem B212807 : Blo 139791 212807 := bstep (se 1 (by rfl) ⟨159605, by rfl⟩ : syracuseStep 212807 = 319211) B319211
theorem B212891 : Blo 139791 212891 := bstep (se 1 (by rfl) ⟨159668, by rfl⟩ : syracuseStep 212891 = 319337) B319337
theorem B1818713 : Blo 139791 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B213455 : Blo 139791 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B213497 : Blo 139791 213497 := bstep (se 2 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 213497 = 160123) B160123
theorem B213599 : Blo 139791 213599 := bstep (se 1 (by rfl) ⟨160199, by rfl⟩ : syracuseStep 213599 = 320399) B320399
theorem B541313 : Blo 139791 541313 := bstep (se 2 (by rfl) ⟨202992, by rfl⟩ : syracuseStep 541313 = 405985) B405985
theorem B475901 : Blo 139791 475901 := bstep (se 3 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 475901 = 178463) B178463
theorem B345043 : Blo 139791 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B2573369 : Blo 139791 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B214079 : Blo 139791 214079 := bstep (se 1 (by rfl) ⟨160559, by rfl⟩ : syracuseStep 214079 = 321119) B321119
theorem B902249 : Blo 139791 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B214121 : Blo 139791 214121 := bstep (se 2 (by rfl) ⟨80295, by rfl⟩ : syracuseStep 214121 = 160591) B160591
theorem B214223 : Blo 139791 214223 := bstep (se 1 (by rfl) ⟨160667, by rfl⟩ : syracuseStep 214223 = 321335) B321335
theorem B214427 : Blo 139791 214427 := bstep (se 1 (by rfl) ⟨160820, by rfl⟩ : syracuseStep 214427 = 321641) B321641
theorem B1590821 : Blo 139791 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B509561 : Blo 139791 509561 := bstep (se 2 (by rfl) ⟨191085, by rfl⟩ : syracuseStep 509561 = 382171) B382171
theorem B214649 : Blo 139791 214649 := bstep (se 2 (by rfl) ⟨80493, by rfl⟩ : syracuseStep 214649 = 160987) B160987
theorem B214751 : Blo 139791 214751 := bstep (se 1 (by rfl) ⟨161063, by rfl⟩ : syracuseStep 214751 = 322127) B322127
theorem B214847 : Blo 139791 214847 := bstep (se 1 (by rfl) ⟨161135, by rfl⟩ : syracuseStep 214847 = 322271) B322271
theorem B608107 : Blo 139791 608107 := bstep (se 1 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 608107 = 912161) B912161
theorem B215015 : Blo 139791 215015 := bstep (se 1 (by rfl) ⟨161261, by rfl⟩ : syracuseStep 215015 = 322523) B322523
theorem B215033 : Blo 139791 215033 := bstep (se 2 (by rfl) ⟨80637, by rfl⟩ : syracuseStep 215033 = 161275) B161275
theorem B2050109 : Blo 139791 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B215135 : Blo 139791 215135 := bstep (se 1 (by rfl) ⟨161351, by rfl⟩ : syracuseStep 215135 = 322703) B322703
theorem B215195 : Blo 139791 215195 := bstep (se 1 (by rfl) ⟨161396, by rfl⟩ : syracuseStep 215195 = 322793) B322793
theorem B215231 : Blo 139791 215231 := bstep (se 1 (by rfl) ⟨161423, by rfl⟩ : syracuseStep 215231 = 322847) B322847
theorem B608465 : Blo 139791 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B215273 : Blo 139791 215273 := bstep (se 2 (by rfl) ⟨80727, by rfl⟩ : syracuseStep 215273 = 161455) B161455
theorem B1067255 : Blo 139791 1067255 := bstep (se 1 (by rfl) ⟨800441, by rfl⟩ : syracuseStep 1067255 = 1600883) B1600883
theorem B542969 : Blo 139791 542969 := bstep (se 2 (by rfl) ⟨203613, by rfl⟩ : syracuseStep 542969 = 407227) B407227
theorem B805211 : Blo 139791 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B215579 : Blo 139791 215579 := bstep (se 1 (by rfl) ⟨161684, by rfl⟩ : syracuseStep 215579 = 323369) B323369
theorem B215657 : Blo 139791 215657 := bstep (se 2 (by rfl) ⟨80871, by rfl⟩ : syracuseStep 215657 = 161743) B161743
theorem B2214611 : Blo 139791 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B478007 : Blo 139791 478007 := bstep (se 1 (by rfl) ⟨358505, by rfl⟩ : syracuseStep 478007 = 717011) B717011
theorem B805727 : Blo 139791 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B315359 : Blo 139791 315359 := bstep (se 1 (by rfl) ⟨236519, by rfl⟩ : syracuseStep 315359 = 473039) B473039
theorem B3428419 : Blo 139791 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B1724723 : Blo 139791 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B316007 : Blo 139791 316007 := bstep (se 1 (by rfl) ⟨237005, by rfl⟩ : syracuseStep 316007 = 474011) B474011
theorem B709235 : Blo 139791 709235 := bstep (se 1 (by rfl) ⟨531926, by rfl⟩ : syracuseStep 709235 = 1063853) B1063853
theorem B414505 : Blo 139791 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B1627127 : Blo 139791 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B480329 : Blo 139791 480329 := bstep (se 2 (by rfl) ⟨180123, by rfl⟩ : syracuseStep 480329 = 360247) B360247
theorem B545899 : Blo 139791 545899 := bstep (se 1 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 545899 = 818849) B818849
theorem B316691 : Blo 139791 316691 := bstep (se 1 (by rfl) ⟨237518, by rfl⟩ : syracuseStep 316691 = 475037) B475037
theorem B316763 : Blo 139791 316763 := bstep (se 1 (by rfl) ⟨237572, by rfl⟩ : syracuseStep 316763 = 475145) B475145
theorem B1398169 : Blo 139791 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B447943 : Blo 139791 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B7722503 : Blo 139791 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1595051 : Blo 139791 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B317321 : Blo 139791 317321 := bstep (se 2 (by rfl) ⟨118995, by rfl⟩ : syracuseStep 317321 = 237991) B237991
theorem B317537 : Blo 139791 317537 := bstep (se 2 (by rfl) ⟨119076, by rfl⟩ : syracuseStep 317537 = 238153) B238153
theorem B710855 : Blo 139791 710855 := bstep (se 1 (by rfl) ⟨533141, by rfl⟩ : syracuseStep 710855 = 1066283) B1066283
theorem B448841 : Blo 139791 448841 := bstep (se 2 (by rfl) ⟨168315, by rfl⟩ : syracuseStep 448841 = 336631) B336631
theorem B481949 : Blo 139791 481949 := bstep (se 3 (by rfl) ⟨90365, by rfl⟩ : syracuseStep 481949 = 180731) B180731
theorem B482273 : Blo 139791 482273 := bstep (se 2 (by rfl) ⟨180852, by rfl⟩ : syracuseStep 482273 = 361705) B361705
theorem B384041 : Blo 139791 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B711827 : Blo 139791 711827 := bstep (se 1 (by rfl) ⟨533870, by rfl⟩ : syracuseStep 711827 = 1067741) B1067741
theorem B482489 : Blo 139791 482489 := bstep (se 2 (by rfl) ⟨180933, by rfl⟩ : syracuseStep 482489 = 361867) B361867
theorem B613727 : Blo 139791 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B318887 : Blo 139791 318887 := bstep (se 1 (by rfl) ⟨239165, by rfl⟩ : syracuseStep 318887 = 478331) B478331
theorem B319067 : Blo 139791 319067 := bstep (se 1 (by rfl) ⟨239300, by rfl⟩ : syracuseStep 319067 = 478601) B478601
theorem B319355 : Blo 139791 319355 := bstep (se 1 (by rfl) ⟨239516, by rfl⟩ : syracuseStep 319355 = 479033) B479033
theorem B712637 : Blo 139791 712637 := bstep (se 3 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 712637 = 267239) B267239
theorem B1827035 : Blo 139791 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B319841 : Blo 139791 319841 := bstep (se 2 (by rfl) ⟨119940, by rfl⟩ : syracuseStep 319841 = 239881) B239881
theorem B516449 : Blo 139791 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B7791011 : Blo 139791 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B319931 : Blo 139791 319931 := bstep (se 1 (by rfl) ⟨239948, by rfl⟩ : syracuseStep 319931 = 479897) B479897
theorem B483947 : Blo 139791 483947 := bstep (se 1 (by rfl) ⟨362960, by rfl⟩ : syracuseStep 483947 = 725921) B725921
theorem B484541 : Blo 139791 484541 := bstep (se 3 (by rfl) ⟨90851, by rfl⟩ : syracuseStep 484541 = 181703) B181703
theorem B320939 : Blo 139791 320939 := bstep (se 1 (by rfl) ⟨240704, by rfl⟩ : syracuseStep 320939 = 481409) B481409
theorem B452249 : Blo 139791 452249 := bstep (se 2 (by rfl) ⟨169593, by rfl⟩ : syracuseStep 452249 = 339187) B339187
theorem B419489 : Blo 139791 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B157351 : Blo 139791 157351 := bstep (se 1 (by rfl) ⟨118013, by rfl⟩ : syracuseStep 157351 = 236027) B236027
theorem B1205927 : Blo 139791 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B321191 : Blo 139791 321191 := bstep (se 1 (by rfl) ⟨240893, by rfl⟩ : syracuseStep 321191 = 481787) B481787
theorem B255739 : Blo 139791 255739 := bstep (se 1 (by rfl) ⟨191804, by rfl⟩ : syracuseStep 255739 = 383609) B383609
theorem B1075031 : Blo 139791 1075031 := bstep (se 1 (by rfl) ⟨806273, by rfl⟩ : syracuseStep 1075031 = 1612547) B1612547
theorem B157639 : Blo 139791 157639 := bstep (se 1 (by rfl) ⟨118229, by rfl⟩ : syracuseStep 157639 = 236459) B236459
theorem B321479 : Blo 139791 321479 := bstep (se 1 (by rfl) ⟨241109, by rfl⟩ : syracuseStep 321479 = 482219) B482219
theorem B714743 : Blo 139791 714743 := bstep (se 1 (by rfl) ⟨536057, by rfl⟩ : syracuseStep 714743 = 1072115) B1072115
theorem B714905 : Blo 139791 714905 := bstep (se 2 (by rfl) ⟨268089, by rfl⟩ : syracuseStep 714905 = 536179) B536179
theorem B1927397 : Blo 139791 1927397 := bstep (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) B361387
theorem B321785 : Blo 139791 321785 := bstep (se 2 (by rfl) ⟨120669, by rfl⟩ : syracuseStep 321785 = 241339) B241339
theorem B1468697 : Blo 139791 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B157999 : Blo 139791 157999 := bstep (se 1 (by rfl) ⟨118499, by rfl⟩ : syracuseStep 157999 = 236999) B236999
theorem B321839 : Blo 139791 321839 := bstep (se 1 (by rfl) ⟨241379, by rfl⟩ : syracuseStep 321839 = 482759) B482759
theorem B256379 : Blo 139791 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B813473 : Blo 139791 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B322055 : Blo 139791 322055 := bstep (se 1 (by rfl) ⟨241541, by rfl⟩ : syracuseStep 322055 = 483083) B483083
theorem B4057775 : Blo 139791 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B322235 : Blo 139791 322235 := bstep (se 1 (by rfl) ⟨241676, by rfl⟩ : syracuseStep 322235 = 483353) B483353
theorem B715715 : Blo 139791 715715 := bstep (se 1 (by rfl) ⟨536786, by rfl⟩ : syracuseStep 715715 = 1073573) B1073573
theorem B158791 : Blo 139791 158791 := bstep (se 1 (by rfl) ⟨119093, by rfl⟩ : syracuseStep 158791 = 238187) B238187
theorem B1010987 : Blo 139791 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B323063 : Blo 139791 323063 := bstep (se 1 (by rfl) ⟨242297, by rfl⟩ : syracuseStep 323063 = 484595) B484595
theorem B224831 : Blo 139791 224831 := bstep (se 1 (by rfl) ⟨168623, by rfl⟩ : syracuseStep 224831 = 337247) B337247
theorem B323135 : Blo 139791 323135 := bstep (se 1 (by rfl) ⟨242351, by rfl⟩ : syracuseStep 323135 = 484703) B484703
theorem B356015 : Blo 139791 356015 := bstep (se 1 (by rfl) ⟨267011, by rfl⟩ : syracuseStep 356015 = 534023) B534023
theorem B356339 : Blo 139791 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B618625 : Blo 139791 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B913619 : Blo 139791 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B356663 : Blo 139791 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B913801 : Blo 139791 913801 := bstep (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) B685351
theorem B225785 : Blo 139791 225785 := bstep (se 2 (by rfl) ⟨84669, by rfl⟩ : syracuseStep 225785 = 169339) B169339
theorem B258643 : Blo 139791 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B193447 : Blo 139791 193447 := bstep (se 1 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 193447 = 290171) B290171
theorem B1143845 : Blo 139791 1143845 := bstep (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) B214471
theorem B816641 : Blo 139791 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B357959 : Blo 139791 357959 := bstep (se 1 (by rfl) ⟨268469, by rfl⟩ : syracuseStep 357959 = 536939) B536939
theorem B161599 : Blo 139791 161599 := bstep (se 1 (by rfl) ⟨121199, by rfl⟩ : syracuseStep 161599 = 242399) B242399
theorem B456605 : Blo 139791 456605 := bstep (se 3 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 456605 = 171227) B171227
theorem B456799 : Blo 139791 456799 := bstep (se 1 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 456799 = 685199) B685199
theorem B883055 : Blo 139791 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B3440015 : Blo 139791 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B654803 : Blo 139791 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B327871 : Blo 139791 327871 := bstep (se 1 (by rfl) ⟨245903, by rfl⟩ : syracuseStep 327871 = 491807) B491807
theorem B4849901 : Blo 139791 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B4129055 : Blo 139791 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B360875 : Blo 139791 360875 := bstep (se 1 (by rfl) ⟨270656, by rfl⟩ : syracuseStep 360875 = 541313) B541313
theorem B1639727 : Blo 139791 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B2590001 : Blo 139791 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B361979 : Blo 139791 361979 := bstep (se 1 (by rfl) ⟨271484, by rfl⟩ : syracuseStep 361979 = 542969) B542969
theorem B919259 : Blo 139791 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B1476407 : Blo 139791 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B362657 : Blo 139791 362657 := bstep (se 2 (by rfl) ⟨135996, by rfl⟩ : syracuseStep 362657 = 271993) B271993
theorem B1640843 : Blo 139791 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B920159 : Blo 139791 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B1149815 : Blo 139791 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B1379429 : Blo 139791 1379429 := bstep (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) B258643
theorem B1084751 : Blo 139791 1084751 := bstep (se 1 (by rfl) ⟨813563, by rfl⟩ : syracuseStep 1084751 = 1627127) B1627127
theorem B2100599 : Blo 139791 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B5148335 : Blo 139791 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B2560157 : Blo 139791 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B299227 : Blo 139791 299227 := bstep (se 1 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 299227 = 448841) B448841
theorem B266807 : Blo 139791 266807 := bstep (se 1 (by rfl) ⟨200105, by rfl⟩ : syracuseStep 266807 = 400211) B400211
theorem B1840229 : Blo 139791 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B1218023 : Blo 139791 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B824833 : Blo 139791 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B1218401 : Blo 139791 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B1513363 : Blo 139791 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B399755 : Blo 139791 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B301499 : Blo 139791 301499 := bstep (se 1 (by rfl) ⟨226124, by rfl⟩ : syracuseStep 301499 = 452249) B452249
theorem B727865 : Blo 139791 727865 := bstep (se 2 (by rfl) ⟨272949, by rfl⟩ : syracuseStep 727865 = 545899) B545899
theorem B1284931 : Blo 139791 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B597257 : Blo 139791 597257 := bstep (se 2 (by rfl) ⟨223971, by rfl⟩ : syracuseStep 597257 = 447943) B447943
theorem B269639 : Blo 139791 269639 := bstep (se 1 (by rfl) ⟨202229, by rfl⟩ : syracuseStep 269639 = 404459) B404459
theorem B237343 : Blo 139791 237343 := bstep (se 1 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 237343 = 356015) B356015
theorem B237559 : Blo 139791 237559 := bstep (se 1 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 237559 = 356339) B356339
theorem B1024109 : Blo 139791 1024109 := bstep (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) B384041
theorem B237775 : Blo 139791 237775 := bstep (se 1 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 237775 = 356663) B356663
theorem B139803 : Blo 139791 139803 := bstep (se 1 (by rfl) ⟨104852, by rfl⟩ : syracuseStep 139803 = 209705) B209705
theorem B139807 : Blo 139791 139807 := bstep (se 1 (by rfl) ⟨104855, by rfl⟩ : syracuseStep 139807 = 209711) B209711
theorem B139887 : Blo 139791 139887 := bstep (se 1 (by rfl) ⟨104915, by rfl⟩ : syracuseStep 139887 = 209831) B209831
theorem B139943 : Blo 139791 139943 := bstep (se 1 (by rfl) ⟨104957, by rfl⟩ : syracuseStep 139943 = 209915) B209915
theorem B762563 : Blo 139791 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B139983 : Blo 139791 139983 := bstep (se 1 (by rfl) ⟨104987, by rfl⟩ : syracuseStep 139983 = 209975) B209975
theorem B140063 : Blo 139791 140063 := bstep (se 1 (by rfl) ⟨105047, by rfl⟩ : syracuseStep 140063 = 210095) B210095
theorem B140335 : Blo 139791 140335 := bstep (se 1 (by rfl) ⟨105251, by rfl⟩ : syracuseStep 140335 = 210503) B210503
theorem B238639 : Blo 139791 238639 := bstep (se 1 (by rfl) ⟨178979, by rfl⟩ : syracuseStep 238639 = 357959) B357959
theorem B140399 : Blo 139791 140399 := bstep (se 1 (by rfl) ⟨105299, by rfl⟩ : syracuseStep 140399 = 210599) B210599
theorem B140455 : Blo 139791 140455 := bstep (se 1 (by rfl) ⟨105341, by rfl⟩ : syracuseStep 140455 = 210683) B210683
theorem B140479 : Blo 139791 140479 := bstep (se 1 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 140479 = 210719) B210719
theorem B140511 : Blo 139791 140511 := bstep (se 1 (by rfl) ⟨105383, by rfl⟩ : syracuseStep 140511 = 210767) B210767
theorem B304403 : Blo 139791 304403 := bstep (se 1 (by rfl) ⟨228302, by rfl⟩ : syracuseStep 304403 = 456605) B456605
theorem B140591 : Blo 139791 140591 := bstep (se 1 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 140591 = 210887) B210887
theorem B402887 : Blo 139791 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B140827 : Blo 139791 140827 := bstep (se 1 (by rfl) ⟨105620, by rfl⟩ : syracuseStep 140827 = 211241) B211241
theorem B140831 : Blo 139791 140831 := bstep (se 1 (by rfl) ⟨105623, by rfl⟩ : syracuseStep 140831 = 211247) B211247
theorem B403127 : Blo 139791 403127 := bstep (se 1 (by rfl) ⟨302345, by rfl⟩ : syracuseStep 403127 = 604691) B604691
theorem B140991 : Blo 139791 140991 := bstep (se 1 (by rfl) ⟨105743, by rfl⟩ : syracuseStep 140991 = 211487) B211487
theorem B141247 : Blo 139791 141247 := bstep (se 1 (by rfl) ⟨105935, by rfl⟩ : syracuseStep 141247 = 211871) B211871
theorem B141279 : Blo 139791 141279 := bstep (se 1 (by rfl) ⟨105959, by rfl⟩ : syracuseStep 141279 = 211919) B211919
theorem B141339 : Blo 139791 141339 := bstep (se 1 (by rfl) ⟨106004, by rfl⟩ : syracuseStep 141339 = 212009) B212009
theorem B141343 : Blo 139791 141343 := bstep (se 1 (by rfl) ⟨106007, by rfl⟩ : syracuseStep 141343 = 212015) B212015
theorem B141359 : Blo 139791 141359 := bstep (se 1 (by rfl) ⟨106019, by rfl⟩ : syracuseStep 141359 = 212039) B212039
theorem B141535 : Blo 139791 141535 := bstep (se 1 (by rfl) ⟨106151, by rfl⟩ : syracuseStep 141535 = 212303) B212303
theorem B141595 : Blo 139791 141595 := bstep (se 1 (by rfl) ⟨106196, by rfl⟩ : syracuseStep 141595 = 212393) B212393
theorem B436535 : Blo 139791 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B141695 : Blo 139791 141695 := bstep (se 1 (by rfl) ⟨106271, by rfl⟩ : syracuseStep 141695 = 212543) B212543
theorem B141871 : Blo 139791 141871 := bstep (se 1 (by rfl) ⟨106403, by rfl⟩ : syracuseStep 141871 = 212807) B212807
theorem B141927 : Blo 139791 141927 := bstep (se 1 (by rfl) ⟨106445, by rfl⟩ : syracuseStep 141927 = 212891) B212891
theorem B142303 : Blo 139791 142303 := bstep (se 1 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 142303 = 213455) B213455
theorem B142331 : Blo 139791 142331 := bstep (se 1 (by rfl) ⟨106748, by rfl⟩ : syracuseStep 142331 = 213497) B213497
theorem B142399 : Blo 139791 142399 := bstep (se 1 (by rfl) ⟨106799, by rfl⟩ : syracuseStep 142399 = 213599) B213599
theorem B2436317 : Blo 139791 2436317 := bstep (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) B913619
theorem B961811 : Blo 139791 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B1715579 : Blo 139791 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B142719 : Blo 139791 142719 := bstep (se 1 (by rfl) ⟨107039, by rfl⟩ : syracuseStep 142719 = 214079) B214079
theorem B601499 : Blo 139791 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B142747 : Blo 139791 142747 := bstep (se 1 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 142747 = 214121) B214121
theorem B142815 : Blo 139791 142815 := bstep (se 1 (by rfl) ⟨107111, by rfl⟩ : syracuseStep 142815 = 214223) B214223
theorem B1945133 : Blo 139791 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B142951 : Blo 139791 142951 := bstep (se 1 (by rfl) ⟨107213, by rfl⟩ : syracuseStep 142951 = 214427) B214427
theorem B568939 : Blo 139791 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B1060547 : Blo 139791 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B339707 : Blo 139791 339707 := bstep (se 1 (by rfl) ⟨254780, by rfl⟩ : syracuseStep 339707 = 509561) B509561
theorem B143099 : Blo 139791 143099 := bstep (se 1 (by rfl) ⟨107324, by rfl⟩ : syracuseStep 143099 = 214649) B214649
theorem B143167 : Blo 139791 143167 := bstep (se 1 (by rfl) ⟨107375, by rfl⟩ : syracuseStep 143167 = 214751) B214751
theorem B143231 : Blo 139791 143231 := bstep (se 1 (by rfl) ⟨107423, by rfl⟩ : syracuseStep 143231 = 214847) B214847
theorem B602093 : Blo 139791 602093 := bstep (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) B225785
theorem B143343 : Blo 139791 143343 := bstep (se 1 (by rfl) ⟨107507, by rfl⟩ : syracuseStep 143343 = 215015) B215015
theorem B143355 : Blo 139791 143355 := bstep (se 1 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 143355 = 215033) B215033
theorem B143423 : Blo 139791 143423 := bstep (se 1 (by rfl) ⟨107567, by rfl⟩ : syracuseStep 143423 = 215135) B215135
theorem B143463 : Blo 139791 143463 := bstep (se 1 (by rfl) ⟨107597, by rfl⟩ : syracuseStep 143463 = 215195) B215195
theorem B143487 : Blo 139791 143487 := bstep (se 1 (by rfl) ⟨107615, by rfl⟩ : syracuseStep 143487 = 215231) B215231
theorem B405643 : Blo 139791 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B143515 : Blo 139791 143515 := bstep (se 1 (by rfl) ⟨107636, by rfl⟩ : syracuseStep 143515 = 215273) B215273
theorem B536807 : Blo 139791 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B143719 : Blo 139791 143719 := bstep (se 1 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 143719 = 215579) B215579
theorem B242075 : Blo 139791 242075 := bstep (se 1 (by rfl) ⟨181556, by rfl⟩ : syracuseStep 242075 = 363113) B363113
theorem B143771 : Blo 139791 143771 := bstep (se 1 (by rfl) ⟨107828, by rfl⟩ : syracuseStep 143771 = 215657) B215657
theorem B1618379 : Blo 139791 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B438841 : Blo 139791 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B537151 : Blo 139791 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B209801 : Blo 139791 209801 := bstep (se 2 (by rfl) ⟨78675, by rfl⟩ : syracuseStep 209801 = 157351) B157351
theorem B504787 : Blo 139791 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B340985 : Blo 139791 340985 := bstep (se 2 (by rfl) ⟨127869, by rfl⟩ : syracuseStep 340985 = 255739) B255739
theorem B177223 : Blo 139791 177223 := bstep (se 1 (by rfl) ⟨132917, by rfl⟩ : syracuseStep 177223 = 265835) B265835
theorem B210185 : Blo 139791 210185 := bstep (se 2 (by rfl) ⟨78819, by rfl⟩ : syracuseStep 210185 = 157639) B157639
theorem B210239 : Blo 139791 210239 := bstep (se 1 (by rfl) ⟨157679, by rfl⟩ : syracuseStep 210239 = 315359) B315359
theorem B538109 : Blo 139791 538109 := bstep (se 3 (by rfl) ⟨100895, by rfl⟩ : syracuseStep 538109 = 201791) B201791
theorem B210665 : Blo 139791 210665 := bstep (se 2 (by rfl) ⟨78999, by rfl⟩ : syracuseStep 210665 = 157999) B157999
theorem B210671 : Blo 139791 210671 := bstep (se 1 (by rfl) ⟨158003, by rfl⟩ : syracuseStep 210671 = 316007) B316007
theorem B472823 : Blo 139791 472823 := bstep (se 1 (by rfl) ⟨354617, by rfl⟩ : syracuseStep 472823 = 709235) B709235
theorem B2799755 : Blo 139791 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B211127 : Blo 139791 211127 := bstep (se 1 (by rfl) ⟨158345, by rfl⟩ : syracuseStep 211127 = 316691) B316691
theorem B211175 : Blo 139791 211175 := bstep (se 1 (by rfl) ⟨158381, by rfl⟩ : syracuseStep 211175 = 316763) B316763
theorem B1063367 : Blo 139791 1063367 := bstep (se 1 (by rfl) ⟨797525, by rfl⟩ : syracuseStep 1063367 = 1595051) B1595051
theorem B211547 : Blo 139791 211547 := bstep (se 1 (by rfl) ⟨158660, by rfl⟩ : syracuseStep 211547 = 317321) B317321
theorem B539369 : Blo 139791 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B211691 : Blo 139791 211691 := bstep (se 1 (by rfl) ⟨158768, by rfl⟩ : syracuseStep 211691 = 317537) B317537
theorem B211721 : Blo 139791 211721 := bstep (se 2 (by rfl) ⟨79395, by rfl⟩ : syracuseStep 211721 = 158791) B158791
theorem B473903 : Blo 139791 473903 := bstep (se 1 (by rfl) ⟨355427, by rfl⟩ : syracuseStep 473903 = 710855) B710855
theorem B179111 : Blo 139791 179111 := bstep (se 1 (by rfl) ⟨134333, by rfl⟩ : syracuseStep 179111 = 268667) B268667
theorem B1326365 : Blo 139791 1326365 := bstep (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) B497387
theorem B474551 : Blo 139791 474551 := bstep (se 1 (by rfl) ⟨355913, by rfl⟩ : syracuseStep 474551 = 711827) B711827
theorem B1031717 : Blo 139791 1031717 := bstep (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) B193447
theorem B409151 : Blo 139791 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B212591 : Blo 139791 212591 := bstep (se 1 (by rfl) ⟨159443, by rfl⟩ : syracuseStep 212591 = 318887) B318887
theorem B212711 : Blo 139791 212711 := bstep (se 1 (by rfl) ⟨159533, by rfl⟩ : syracuseStep 212711 = 319067) B319067
theorem B1064825 : Blo 139791 1064825 := bstep (se 2 (by rfl) ⟨399309, by rfl⟩ : syracuseStep 1064825 = 798619) B798619
theorem B212903 : Blo 139791 212903 := bstep (se 1 (by rfl) ⟨159677, by rfl⟩ : syracuseStep 212903 = 319355) B319355
theorem B475091 : Blo 139791 475091 := bstep (se 1 (by rfl) ⟨356318, by rfl⟩ : syracuseStep 475091 = 712637) B712637
theorem B4571225 : Blo 139791 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B213227 : Blo 139791 213227 := bstep (se 1 (by rfl) ⟨159920, by rfl⟩ : syracuseStep 213227 = 319841) B319841
theorem B344299 : Blo 139791 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B5194007 : Blo 139791 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B213287 : Blo 139791 213287 := bstep (se 1 (by rfl) ⟨159965, by rfl⟩ : syracuseStep 213287 = 319931) B319931
theorem B541025 : Blo 139791 541025 := bstep (se 2 (by rfl) ⟨202884, by rfl⟩ : syracuseStep 541025 = 405769) B405769
theorem B1360435 : Blo 139791 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B3916525 : Blo 139791 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B213959 : Blo 139791 213959 := bstep (se 1 (by rfl) ⟨160469, by rfl⟩ : syracuseStep 213959 = 320939) B320939
theorem B279659 : Blo 139791 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B803951 : Blo 139791 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B214127 : Blo 139791 214127 := bstep (se 1 (by rfl) ⟨160595, by rfl⟩ : syracuseStep 214127 = 321191) B321191
theorem B1230083 : Blo 139791 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B214319 : Blo 139791 214319 := bstep (se 1 (by rfl) ⟨160739, by rfl⟩ : syracuseStep 214319 = 321479) B321479
theorem B476495 : Blo 139791 476495 := bstep (se 1 (by rfl) ⟨357371, by rfl⟩ : syracuseStep 476495 = 714743) B714743
theorem B476603 : Blo 139791 476603 := bstep (se 1 (by rfl) ⟨357452, by rfl⟩ : syracuseStep 476603 = 714905) B714905
theorem B214523 : Blo 139791 214523 := bstep (se 1 (by rfl) ⟨160892, by rfl⟩ : syracuseStep 214523 = 321785) B321785
theorem B214559 : Blo 139791 214559 := bstep (se 1 (by rfl) ⟨160919, by rfl⟩ : syracuseStep 214559 = 321839) B321839
theorem B542315 : Blo 139791 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B214703 : Blo 139791 214703 := bstep (se 1 (by rfl) ⟨161027, by rfl⟩ : syracuseStep 214703 = 322055) B322055
theorem B2705183 : Blo 139791 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B214823 : Blo 139791 214823 := bstep (se 1 (by rfl) ⟨161117, by rfl⟩ : syracuseStep 214823 = 322235) B322235
theorem B477143 : Blo 139791 477143 := bstep (se 1 (by rfl) ⟨357857, by rfl⟩ : syracuseStep 477143 = 715715) B715715
theorem B673991 : Blo 139791 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B575687 : Blo 139791 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B215375 : Blo 139791 215375 := bstep (se 1 (by rfl) ⟨161531, by rfl⟩ : syracuseStep 215375 = 323063) B323063
theorem B149887 : Blo 139791 149887 := bstep (se 1 (by rfl) ⟨112415, by rfl⟩ : syracuseStep 149887 = 224831) B224831
theorem B215423 : Blo 139791 215423 := bstep (se 1 (by rfl) ⟨161567, by rfl⟩ : syracuseStep 215423 = 323135) B323135
theorem B215465 : Blo 139791 215465 := bstep (se 2 (by rfl) ⟨80799, by rfl⟩ : syracuseStep 215465 = 161599) B161599
theorem B1952261 : Blo 139791 1952261 := bstep (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) B366049
theorem B609065 : Blo 139791 609065 := bstep (se 2 (by rfl) ⟨228399, by rfl⟩ : syracuseStep 609065 = 456799) B456799
theorem B314855 : Blo 139791 314855 := bstep (se 1 (by rfl) ⟨236141, by rfl⟩ : syracuseStep 314855 = 472283) B472283
theorem B544427 : Blo 139791 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B315431 : Blo 139791 315431 := bstep (se 1 (by rfl) ⟨236573, by rfl⟩ : syracuseStep 315431 = 473147) B473147
theorem B315611 : Blo 139791 315611 := bstep (se 1 (by rfl) ⟨236708, by rfl⟩ : syracuseStep 315611 = 473417) B473417
theorem B315881 : Blo 139791 315881 := bstep (se 2 (by rfl) ⟨118455, by rfl⟩ : syracuseStep 315881 = 236911) B236911
theorem B316385 : Blo 139791 316385 := bstep (se 2 (by rfl) ⟨118644, by rfl⟩ : syracuseStep 316385 = 237289) B237289
theorem B316511 : Blo 139791 316511 := bstep (se 1 (by rfl) ⟨237383, by rfl⟩ : syracuseStep 316511 = 474767) B474767
theorem B349679 : Blo 139791 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B2053799 : Blo 139791 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B153415 : Blo 139791 153415 := bstep (se 1 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 153415 = 230123) B230123
theorem B317267 : Blo 139791 317267 := bstep (se 1 (by rfl) ⟨237950, by rfl⟩ : syracuseStep 317267 = 475901) B475901
theorem B284891 : Blo 139791 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B317753 : Blo 139791 317753 := bstep (se 2 (by rfl) ⟨119157, by rfl⟩ : syracuseStep 317753 = 238315) B238315
theorem B4413971 : Blo 139791 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B7428631 : Blo 139791 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B1366739 : Blo 139791 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B809783 : Blo 139791 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B711503 : Blo 139791 711503 := bstep (se 1 (by rfl) ⟨533627, by rfl⟩ : syracuseStep 711503 = 1067255) B1067255
theorem B1137617 : Blo 139791 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B318671 : Blo 139791 318671 := bstep (se 1 (by rfl) ⟨239003, by rfl⟩ : syracuseStep 318671 = 478007) B478007
theorem B319049 : Blo 139791 319049 := bstep (se 2 (by rfl) ⟨119643, by rfl⟩ : syracuseStep 319049 = 239287) B239287
theorem B712313 : Blo 139791 712313 := bstep (se 2 (by rfl) ⟨267117, by rfl⟩ : syracuseStep 712313 = 534235) B534235
theorem B450173 : Blo 139791 450173 := bstep (se 3 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 450173 = 168815) B168815
theorem B810809 : Blo 139791 810809 := bstep (se 2 (by rfl) ⟨304053, by rfl⟩ : syracuseStep 810809 = 608107) B608107
theorem B1466435 : Blo 139791 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B811559 : Blo 139791 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B320219 : Blo 139791 320219 := bstep (se 1 (by rfl) ⟨240164, by rfl⟩ : syracuseStep 320219 = 480329) B480329
theorem B910237 : Blo 139791 910237 := bstep (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) B341339
theorem B320633 : Blo 139791 320633 := bstep (se 2 (by rfl) ⟨120237, by rfl⟩ : syracuseStep 320633 = 240475) B240475
theorem B1926737 : Blo 139791 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B321299 : Blo 139791 321299 := bstep (se 1 (by rfl) ⟨240974, by rfl⟩ : syracuseStep 321299 = 481949) B481949
theorem B1238813 : Blo 139791 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B354203 : Blo 139791 354203 := bstep (se 1 (by rfl) ⟨265652, by rfl⟩ : syracuseStep 354203 = 531305) B531305
theorem B321515 : Blo 139791 321515 := bstep (se 1 (by rfl) ⟨241136, by rfl⟩ : syracuseStep 321515 = 482273) B482273
theorem B321659 : Blo 139791 321659 := bstep (se 1 (by rfl) ⟨241244, by rfl⟩ : syracuseStep 321659 = 482489) B482489
theorem B813199 : Blo 139791 813199 := bstep (se 1 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 813199 = 1219799) B1219799
theorem B2320649 : Blo 139791 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B321929 : Blo 139791 321929 := bstep (se 2 (by rfl) ⟨120723, by rfl⟩ : syracuseStep 321929 = 241447) B241447
theorem B6547877 : Blo 139791 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B158503 : Blo 139791 158503 := bstep (se 1 (by rfl) ⟨118877, by rfl⟩ : syracuseStep 158503 = 237755) B237755
theorem B322631 : Blo 139791 322631 := bstep (se 1 (by rfl) ⟨241973, by rfl⟩ : syracuseStep 322631 = 483947) B483947
theorem B323027 : Blo 139791 323027 := bstep (se 1 (by rfl) ⟨242270, by rfl⟩ : syracuseStep 323027 = 484541) B484541
theorem B683677 : Blo 139791 683677 := bstep (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) B256379
theorem B552673 : Blo 139791 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B323297 : Blo 139791 323297 := bstep (se 2 (by rfl) ⟨121236, by rfl⟩ : syracuseStep 323297 = 242473) B242473
theorem B716687 : Blo 139791 716687 := bstep (se 1 (by rfl) ⟨537515, by rfl⟩ : syracuseStep 716687 = 1075031) B1075031
theorem B290731 : Blo 139791 290731 := bstep (se 1 (by rfl) ⟨218048, by rfl⟩ : syracuseStep 290731 = 436097) B436097
theorem B159727 : Blo 139791 159727 := bstep (se 1 (by rfl) ⟨119795, by rfl⟩ : syracuseStep 159727 = 239591) B239591
theorem B159871 : Blo 139791 159871 := bstep (se 1 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 159871 = 239807) B239807
theorem B454889 : Blo 139791 454889 := bstep (se 2 (by rfl) ⟨170583, by rfl⟩ : syracuseStep 454889 = 341167) B341167
theorem B1864225 : Blo 139791 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B488171 : Blo 139791 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B815933 : Blo 139791 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B226727 : Blo 139791 226727 := bstep (se 1 (by rfl) ⟨170045, by rfl⟩ : syracuseStep 226727 = 340091) B340091
theorem B685523 : Blo 139791 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B357979 : Blo 139791 357979 := bstep (se 1 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 357979 = 536969) B536969
theorem B490025 : Blo 139791 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B228143 : Blo 139791 228143 := bstep (se 1 (by rfl) ⟨171107, by rfl⟩ : syracuseStep 228143 = 342215) B342215
theorem B588703 : Blo 139791 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B2194451 : Blo 139791 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B2293343 : Blo 139791 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B360065 : Blo 139791 360065 := bstep (se 2 (by rfl) ⟨135024, by rfl⟩ : syracuseStep 360065 = 270049) B270049
theorem B3047483 : Blo 139791 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B2752703 : Blo 139791 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B360683 : Blo 139791 360683 := bstep (se 1 (by rfl) ⟨270512, by rfl⟩ : syracuseStep 360683 = 541025) B541025
theorem B459065 : Blo 139791 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B820055 : Blo 139791 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B361543 : Blo 139791 361543 := bstep (se 1 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 361543 = 542315) B542315
theorem B1803455 : Blo 139791 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B1213649 : Blo 139791 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B919619 : Blo 139791 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B723167 : Blo 139791 723167 := bstep (se 1 (by rfl) ⟨542375, by rfl⟩ : syracuseStep 723167 = 1084751) B1084751
theorem B362951 : Blo 139791 362951 := bstep (se 1 (by rfl) ⟨272213, by rfl⟩ : syracuseStep 362951 = 544427) B544427
theorem B1706771 : Blo 139791 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B1084265 : Blo 139791 1084265 := bstep (se 2 (by rfl) ⟨406599, by rfl⟩ : syracuseStep 1084265 = 813199) B813199
theorem B199849 : Blo 139791 199849 := bstep (se 2 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 199849 = 149887) B149887
theorem B233119 : Blo 139791 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B266503 : Blo 139791 266503 := bstep (se 1 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 266503 = 399755) B399755
theorem B200999 : Blo 139791 200999 := bstep (se 1 (by rfl) ⟨150749, by rfl⟩ : syracuseStep 200999 = 301499) B301499
theorem B758411 : Blo 139791 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B758585 : Blo 139791 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B3937085 : Blo 139791 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B398171 : Blo 139791 398171 := bstep (se 1 (by rfl) ⟨298628, by rfl⟩ : syracuseStep 398171 = 597257) B597257
theorem B300115 : Blo 139791 300115 := bstep (se 1 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 300115 = 450173) B450173
theorem B398969 : Blo 139791 398969 := bstep (se 2 (by rfl) ⟨149613, by rfl⟩ : syracuseStep 398969 = 299227) B299227
theorem B759709 : Blo 139791 759709 := bstep (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) B284891
theorem B268591 : Blo 139791 268591 := bstep (se 1 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 268591 = 402887) B402887
theorem B1284491 : Blo 139791 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B268751 : Blo 139791 268751 := bstep (se 1 (by rfl) ⟨201563, by rfl⟩ : syracuseStep 268751 = 403127) B403127
theorem B825875 : Blo 139791 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B236135 : Blo 139791 236135 := bstep (se 1 (by rfl) ⟨177101, by rfl⟩ : syracuseStep 236135 = 354203) B354203
theorem B11770589 : Blo 139791 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B236297 : Blo 139791 236297 := bstep (se 2 (by rfl) ⟨88611, by rfl⟩ : syracuseStep 236297 = 177223) B177223
theorem B1547099 : Blo 139791 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B4365251 : Blo 139791 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B204553 : Blo 139791 204553 := bstep (se 2 (by rfl) ⟨76707, by rfl⟩ : syracuseStep 204553 = 153415) B153415
theorem B401395 : Blo 139791 401395 := bstep (se 1 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 401395 = 602093) B602093
theorem B303259 : Blo 139791 303259 := bstep (se 1 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 303259 = 454889) B454889
theorem B139867 : Blo 139791 139867 := bstep (se 1 (by rfl) ⟨104900, by rfl⟩ : syracuseStep 139867 = 209801) B209801
theorem B9904841 : Blo 139791 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B140123 : Blo 139791 140123 := bstep (se 1 (by rfl) ⟨105092, by rfl⟩ : syracuseStep 140123 = 210185) B210185
theorem B140159 : Blo 139791 140159 := bstep (se 1 (by rfl) ⟨105119, by rfl⟩ : syracuseStep 140159 = 210239) B210239
theorem B1713241 : Blo 139791 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B140443 : Blo 139791 140443 := bstep (se 1 (by rfl) ⟨105332, by rfl⟩ : syracuseStep 140443 = 210665) B210665
theorem B140447 : Blo 139791 140447 := bstep (se 1 (by rfl) ⟨105335, by rfl⟩ : syracuseStep 140447 = 210671) B210671
theorem B140751 : Blo 139791 140751 := bstep (se 1 (by rfl) ⟨105563, by rfl⟩ : syracuseStep 140751 = 211127) B211127
theorem B140783 : Blo 139791 140783 := bstep (se 1 (by rfl) ⟨105587, by rfl⟩ : syracuseStep 140783 = 211175) B211175
theorem B1091069 : Blo 139791 1091069 := bstep (se 3 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 1091069 = 409151) B409151
theorem B141031 : Blo 139791 141031 := bstep (se 1 (by rfl) ⟨105773, by rfl⟩ : syracuseStep 141031 = 211547) B211547
theorem B141127 : Blo 139791 141127 := bstep (se 1 (by rfl) ⟨105845, by rfl⟩ : syracuseStep 141127 = 211691) B211691
theorem B141147 : Blo 139791 141147 := bstep (se 1 (by rfl) ⟨105860, by rfl⟩ : syracuseStep 141147 = 211721) B211721
theorem B2828125 : Blo 139791 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B141727 : Blo 139791 141727 := bstep (se 1 (by rfl) ⟨106295, by rfl⟩ : syracuseStep 141727 = 212591) B212591
theorem B240043 : Blo 139791 240043 := bstep (se 1 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 240043 = 360065) B360065
theorem B141807 : Blo 139791 141807 := bstep (se 1 (by rfl) ⟨106355, by rfl⟩ : syracuseStep 141807 = 212711) B212711
theorem B141935 : Blo 139791 141935 := bstep (se 1 (by rfl) ⟨106451, by rfl⟩ : syracuseStep 141935 = 212903) B212903
theorem B142151 : Blo 139791 142151 := bstep (se 1 (by rfl) ⟨106613, by rfl⟩ : syracuseStep 142151 = 213227) B213227
theorem B3910493 : Blo 139791 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B142191 : Blo 139791 142191 := bstep (se 1 (by rfl) ⟨106643, by rfl⟩ : syracuseStep 142191 = 213287) B213287
theorem B240583 : Blo 139791 240583 := bstep (se 1 (by rfl) ⟨180437, by rfl⟩ : syracuseStep 240583 = 360875) B360875
theorem B142639 : Blo 139791 142639 := bstep (se 1 (by rfl) ⟨106979, by rfl⟩ : syracuseStep 142639 = 213959) B213959
theorem B1813913 : Blo 139791 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B535967 : Blo 139791 535967 := bstep (se 1 (by rfl) ⟨401975, by rfl⟩ : syracuseStep 535967 = 803951) B803951
theorem B142751 : Blo 139791 142751 := bstep (se 1 (by rfl) ⟨107063, by rfl⟩ : syracuseStep 142751 = 214127) B214127
theorem B1093151 : Blo 139791 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B142879 : Blo 139791 142879 := bstep (se 1 (by rfl) ⟨107159, by rfl⟩ : syracuseStep 142879 = 214319) B214319
theorem B5222033 : Blo 139791 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B1748645 : Blo 139791 1748645 := bstep (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) B327871
theorem B241319 : Blo 139791 241319 := bstep (se 1 (by rfl) ⟨180989, by rfl⟩ : syracuseStep 241319 = 361979) B361979
theorem B143015 : Blo 139791 143015 := bstep (se 1 (by rfl) ⟨107261, by rfl⟩ : syracuseStep 143015 = 214523) B214523
theorem B143039 : Blo 139791 143039 := bstep (se 1 (by rfl) ⟨107279, by rfl⟩ : syracuseStep 143039 = 214559) B214559
theorem B143135 : Blo 139791 143135 := bstep (se 1 (by rfl) ⟨107351, by rfl⟩ : syracuseStep 143135 = 214703) B214703
theorem B143215 : Blo 139791 143215 := bstep (se 1 (by rfl) ⟨107411, by rfl⟩ : syracuseStep 143215 = 214823) B214823
theorem B241771 : Blo 139791 241771 := bstep (se 1 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 241771 = 362657) B362657
theorem B143583 : Blo 139791 143583 := bstep (se 1 (by rfl) ⟨107687, by rfl⟩ : syracuseStep 143583 = 215375) B215375
theorem B143615 : Blo 139791 143615 := bstep (se 1 (by rfl) ⟨107711, by rfl⟩ : syracuseStep 143615 = 215423) B215423
theorem B1093895 : Blo 139791 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B143643 : Blo 139791 143643 := bstep (se 1 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 143643 = 215465) B215465
theorem B406043 : Blo 139791 406043 := bstep (se 1 (by rfl) ⟨304532, by rfl⟩ : syracuseStep 406043 = 609065) B609065
theorem B209903 : Blo 139791 209903 := bstep (se 1 (by rfl) ⟨157427, by rfl⟩ : syracuseStep 209903 = 314855) B314855
theorem B210287 : Blo 139791 210287 := bstep (se 1 (by rfl) ⟨157715, by rfl⟩ : syracuseStep 210287 = 315431) B315431
theorem B210407 : Blo 139791 210407 := bstep (se 1 (by rfl) ⟨157805, by rfl⟩ : syracuseStep 210407 = 315611) B315611
theorem B2340485 : Blo 139791 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B210587 : Blo 139791 210587 := bstep (se 1 (by rfl) ⟨157940, by rfl⟩ : syracuseStep 210587 = 315881) B315881
theorem B177871 : Blo 139791 177871 := bstep (se 1 (by rfl) ⟨133403, by rfl⟩ : syracuseStep 177871 = 266807) B266807
theorem B210923 : Blo 139791 210923 := bstep (se 1 (by rfl) ⟨158192, by rfl⟩ : syracuseStep 210923 = 316385) B316385
theorem B211007 : Blo 139791 211007 := bstep (se 1 (by rfl) ⟨158255, by rfl⟩ : syracuseStep 211007 = 316511) B316511
theorem B1226819 : Blo 139791 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B211337 : Blo 139791 211337 := bstep (se 2 (by rfl) ⟨79251, by rfl⟩ : syracuseStep 211337 = 158503) B158503
theorem B211511 : Blo 139791 211511 := bstep (se 1 (by rfl) ⟨158633, by rfl⟩ : syracuseStep 211511 = 317267) B317267
theorem B211835 : Blo 139791 211835 := bstep (se 1 (by rfl) ⟨158876, by rfl⟩ : syracuseStep 211835 = 317753) B317753
theorem B539855 : Blo 139791 539855 := bstep (se 1 (by rfl) ⟨404891, by rfl⟩ : syracuseStep 539855 = 809783) B809783
theorem B474335 : Blo 139791 474335 := bstep (se 1 (by rfl) ⟨355751, by rfl⟩ : syracuseStep 474335 = 711503) B711503
theorem B212447 : Blo 139791 212447 := bstep (se 1 (by rfl) ⟨159335, by rfl⟩ : syracuseStep 212447 = 318671) B318671
theorem B179759 : Blo 139791 179759 := bstep (se 1 (by rfl) ⟨134819, by rfl⟩ : syracuseStep 179759 = 269639) B269639
theorem B736897 : Blo 139791 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B212699 : Blo 139791 212699 := bstep (se 1 (by rfl) ⟨159524, by rfl⟩ : syracuseStep 212699 = 319049) B319049
theorem B474875 : Blo 139791 474875 := bstep (se 1 (by rfl) ⟨356156, by rfl⟩ : syracuseStep 474875 = 712313) B712313
theorem B540539 : Blo 139791 540539 := bstep (se 1 (by rfl) ⟨405404, by rfl⟩ : syracuseStep 540539 = 810809) B810809
theorem B212969 : Blo 139791 212969 := bstep (se 2 (by rfl) ⟨79863, by rfl⟩ : syracuseStep 212969 = 159727) B159727
theorem B213161 : Blo 139791 213161 := bstep (se 2 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 213161 = 159871) B159871
theorem B540857 : Blo 139791 540857 := bstep (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) B405643
theorem B541039 : Blo 139791 541039 := bstep (se 1 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 541039 = 811559) B811559
theorem B508375 : Blo 139791 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B213479 : Blo 139791 213479 := bstep (se 1 (by rfl) ⟨160109, by rfl⟩ : syracuseStep 213479 = 320219) B320219
theorem B213755 : Blo 139791 213755 := bstep (se 1 (by rfl) ⟨160316, by rfl⟩ : syracuseStep 213755 = 320633) B320633
theorem B214199 : Blo 139791 214199 := bstep (se 1 (by rfl) ⟨160649, by rfl⟩ : syracuseStep 214199 = 321299) B321299
theorem B673049 : Blo 139791 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B214343 : Blo 139791 214343 := bstep (se 1 (by rfl) ⟨160757, by rfl⟩ : syracuseStep 214343 = 321515) B321515
theorem B214439 : Blo 139791 214439 := bstep (se 1 (by rfl) ⟨160829, by rfl⟩ : syracuseStep 214439 = 321659) B321659
theorem B214619 : Blo 139791 214619 := bstep (se 1 (by rfl) ⟨160964, by rfl⟩ : syracuseStep 214619 = 321929) B321929
theorem B1099777 : Blo 139791 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B215087 : Blo 139791 215087 := bstep (se 1 (by rfl) ⟨161315, by rfl⟩ : syracuseStep 215087 = 322631) B322631
theorem B477305 : Blo 139791 477305 := bstep (se 2 (by rfl) ⟨178989, by rfl⟩ : syracuseStep 477305 = 357979) B357979
theorem B608381 : Blo 139791 608381 := bstep (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) B228143
theorem B1624211 : Blo 139791 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B641207 : Blo 139791 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B215351 : Blo 139791 215351 := bstep (se 1 (by rfl) ⟨161513, by rfl⟩ : syracuseStep 215351 = 323027) B323027
theorem B3066173 : Blo 139791 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B1296755 : Blo 139791 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B477629 : Blo 139791 477629 := bstep (se 3 (by rfl) ⟨89555, by rfl⟩ : syracuseStep 477629 = 179111) B179111
theorem B215531 : Blo 139791 215531 := bstep (se 1 (by rfl) ⟨161648, by rfl⟩ : syracuseStep 215531 = 323297) B323297
theorem B2017817 : Blo 139791 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B477791 : Blo 139791 477791 := bstep (se 1 (by rfl) ⟨358343, by rfl⟩ : syracuseStep 477791 = 716687) B716687
theorem B543955 : Blo 139791 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B151151 : Blo 139791 151151 := bstep (se 1 (by rfl) ⟨113363, by rfl⟩ : syracuseStep 151151 = 226727) B226727
theorem B315215 : Blo 139791 315215 := bstep (se 1 (by rfl) ⟨236411, by rfl⟩ : syracuseStep 315215 = 472823) B472823
theorem B708911 : Blo 139791 708911 := bstep (se 1 (by rfl) ⟨531683, by rfl⟩ : syracuseStep 708911 = 1063367) B1063367
theorem B315935 : Blo 139791 315935 := bstep (se 1 (by rfl) ⟨236951, by rfl⟩ : syracuseStep 315935 = 473903) B473903
theorem B1462967 : Blo 139791 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B316367 : Blo 139791 316367 := bstep (se 1 (by rfl) ⟨237275, by rfl⟩ : syracuseStep 316367 = 474551) B474551
theorem B316457 : Blo 139791 316457 := bstep (se 2 (by rfl) ⟨118671, by rfl⟩ : syracuseStep 316457 = 237343) B237343
theorem B1528895 : Blo 139791 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B709883 : Blo 139791 709883 := bstep (se 1 (by rfl) ⟨532412, by rfl⟩ : syracuseStep 709883 = 1064825) B1064825
theorem B316727 : Blo 139791 316727 := bstep (se 1 (by rfl) ⟨237545, by rfl⟩ : syracuseStep 316727 = 475091) B475091
theorem B316745 : Blo 139791 316745 := bstep (se 2 (by rfl) ⟨118779, by rfl⟩ : syracuseStep 316745 = 237559) B237559
theorem B3233267 : Blo 139791 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B3462671 : Blo 139791 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B317033 : Blo 139791 317033 := bstep (se 2 (by rfl) ⟨118887, by rfl⟩ : syracuseStep 317033 = 237775) B237775
theorem B1726667 : Blo 139791 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B317663 : Blo 139791 317663 := bstep (se 1 (by rfl) ⟨238247, by rfl⟩ : syracuseStep 317663 = 476495) B476495
theorem B317735 : Blo 139791 317735 := bstep (se 1 (by rfl) ⟨238301, by rfl⟩ : syracuseStep 317735 = 476603) B476603
theorem B612839 : Blo 139791 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B318095 : Blo 139791 318095 := bstep (se 1 (by rfl) ⟨238571, by rfl⟩ : syracuseStep 318095 = 477143) B477143
theorem B318185 : Blo 139791 318185 := bstep (se 2 (by rfl) ⟨119319, by rfl⟩ : syracuseStep 318185 = 238639) B238639
theorem B449327 : Blo 139791 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B383791 : Blo 139791 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B1301507 : Blo 139791 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B613439 : Blo 139791 613439 := bstep (se 1 (by rfl) ⟨460079, by rfl⟩ : syracuseStep 613439 = 920159) B920159
theorem B1301789 : Blo 139791 1301789 := bstep (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) B488171
theorem B1400399 : Blo 139791 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B3432223 : Blo 139791 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B745757 : Blo 139791 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B811741 : Blo 139791 811741 := bstep (se 3 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 811741 = 304403) B304403
theorem B812015 : Blo 139791 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B1369199 : Blo 139791 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B812267 : Blo 139791 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B911159 : Blo 139791 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B485243 : Blo 139791 485243 := bstep (se 1 (by rfl) ⟨363932, by rfl⟩ : syracuseStep 485243 = 727865) B727865
theorem B911569 : Blo 139791 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B387641 : Blo 139791 387641 := bstep (se 2 (by rfl) ⟨145365, by rfl⟩ : syracuseStep 387641 = 290731) B290731
theorem B682739 : Blo 139791 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B2485633 : Blo 139791 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B716201 : Blo 139791 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B291023 : Blo 139791 291023 := bstep (se 1 (by rfl) ⟨218267, by rfl⟩ : syracuseStep 291023 = 436535) B436535
theorem B1143719 : Blo 139791 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B226471 : Blo 139791 226471 := bstep (se 1 (by rfl) ⟨169853, by rfl⟩ : syracuseStep 226471 = 339707) B339707
theorem B357871 : Blo 139791 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B161383 : Blo 139791 161383 := bstep (se 1 (by rfl) ⟨121037, by rfl⟩ : syracuseStep 161383 = 242075) B242075
theorem B1078919 : Blo 139791 1078919 := bstep (se 1 (by rfl) ⟨809189, by rfl⟩ : syracuseStep 1078919 = 1618379) B1618379
theorem B227323 : Blo 139791 227323 := bstep (se 1 (by rfl) ⟨170492, by rfl⟩ : syracuseStep 227323 = 340985) B340985
theorem B457015 : Blo 139791 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B358739 : Blo 139791 358739 := bstep (se 1 (by rfl) ⟨269054, by rfl⟩ : syracuseStep 358739 = 538109) B538109
theorem B1603997 : Blo 139791 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B784937 : Blo 139791 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B1866503 : Blo 139791 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B2751245 : Blo 139791 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B326683 : Blo 139791 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B359579 : Blo 139791 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B884243 : Blo 139791 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B2031655 : Blo 139791 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B360571 : Blo 139791 360571 := bstep (se 1 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 360571 = 540857) B540857
theorem B1835135 : Blo 139791 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B721385 : Blo 139791 721385 := bstep (se 2 (by rfl) ⟨270519, by rfl⟩ : syracuseStep 721385 = 541039) B541039
theorem B1082321 : Blo 139791 1082321 := bstep (se 2 (by rfl) ⟨405870, by rfl⟩ : syracuseStep 1082321 = 811741) B811741
theorem B1082807 : Blo 139791 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B1345211 : Blo 139791 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B722843 : Blo 139791 722843 := bstep (se 1 (by rfl) ⟨542132, by rfl⟩ : syracuseStep 722843 = 1084265) B1084265
theorem B3770833 : Blo 139791 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B1215425 : Blo 139791 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B2624723 : Blo 139791 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B265447 : Blo 139791 265447 := bstep (se 1 (by rfl) ⟨199085, by rfl⟩ : syracuseStep 265447 = 398171) B398171
theorem B1019263 : Blo 139791 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B265979 : Blo 139791 265979 := bstep (se 1 (by rfl) ⟨199484, by rfl⟩ : syracuseStep 265979 = 398969) B398969
theorem B1151111 : Blo 139791 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B266465 : Blo 139791 266465 := bstep (se 2 (by rfl) ⟨99924, by rfl⟩ : syracuseStep 266465 = 199849) B199849
theorem B856327 : Blo 139791 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B725273 : Blo 139791 725273 := bstep (se 2 (by rfl) ⟨271977, by rfl⟩ : syracuseStep 725273 = 543955) B543955
theorem B3314177 : Blo 139791 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B299551 : Blo 139791 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B1742309 : Blo 139791 1742309 := bstep (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) B326683
theorem B497171 : Blo 139791 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B1709885 : Blo 139791 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B727379 : Blo 139791 727379 := bstep (se 1 (by rfl) ⟨545534, by rfl⟩ : syracuseStep 727379 = 1091069) B1091069
theorem B400153 : Blo 139791 400153 := bstep (se 2 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 400153 = 300115) B300115
theorem B301961 : Blo 139791 301961 := bstep (se 2 (by rfl) ⟨113235, by rfl⟩ : syracuseStep 301961 = 226471) B226471
theorem B237161 : Blo 139791 237161 := bstep (se 2 (by rfl) ⟨88935, by rfl⟩ : syracuseStep 237161 = 177871) B177871
theorem B728767 : Blo 139791 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B3481355 : Blo 139791 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B303097 : Blo 139791 303097 := bstep (se 2 (by rfl) ⟨113661, by rfl⟩ : syracuseStep 303097 = 227323) B227323
theorem B729263 : Blo 139791 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B270695 : Blo 139791 270695 := bstep (se 1 (by rfl) ⟨203021, by rfl⟩ : syracuseStep 270695 = 406043) B406043
theorem B762479 : Blo 139791 762479 := bstep (se 1 (by rfl) ⟨571859, by rfl⟩ : syracuseStep 762479 = 1143719) B1143719
theorem B139935 : Blo 139791 139935 := bstep (se 1 (by rfl) ⟨104951, by rfl⟩ : syracuseStep 139935 = 209903) B209903
theorem B140191 : Blo 139791 140191 := bstep (se 1 (by rfl) ⟨105143, by rfl⟩ : syracuseStep 140191 = 210287) B210287
theorem B140271 : Blo 139791 140271 := bstep (se 1 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 140271 = 210407) B210407
theorem B140391 : Blo 139791 140391 := bstep (se 1 (by rfl) ⟨105293, by rfl⟩ : syracuseStep 140391 = 210587) B210587
theorem B140615 : Blo 139791 140615 := bstep (se 1 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 140615 = 210923) B210923
theorem B140671 : Blo 139791 140671 := bstep (se 1 (by rfl) ⟨105503, by rfl⟩ : syracuseStep 140671 = 211007) B211007
theorem B239159 : Blo 139791 239159 := bstep (se 1 (by rfl) ⟨179369, by rfl⟩ : syracuseStep 239159 = 358739) B358739
theorem B140891 : Blo 139791 140891 := bstep (se 1 (by rfl) ⟨105668, by rfl⟩ : syracuseStep 140891 = 211337) B211337
theorem B403069 : Blo 139791 403069 := bstep (se 3 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 403069 = 151151) B151151
theorem B141007 : Blo 139791 141007 := bstep (se 1 (by rfl) ⟨105755, by rfl⟩ : syracuseStep 141007 = 211511) B211511
theorem B141223 : Blo 139791 141223 := bstep (se 1 (by rfl) ⟨105917, by rfl⟩ : syracuseStep 141223 = 211835) B211835
theorem B239719 : Blo 139791 239719 := bstep (se 1 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 239719 = 359579) B359579
theorem B141631 : Blo 139791 141631 := bstep (se 1 (by rfl) ⟨106223, by rfl⟩ : syracuseStep 141631 = 212447) B212447
theorem B272737 : Blo 139791 272737 := bstep (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) B204553
theorem B141799 : Blo 139791 141799 := bstep (se 1 (by rfl) ⟨106349, by rfl⟩ : syracuseStep 141799 = 212699) B212699
theorem B535193 : Blo 139791 535193 := bstep (se 2 (by rfl) ⟨200697, by rfl⟩ : syracuseStep 535193 = 401395) B401395
theorem B141979 : Blo 139791 141979 := bstep (se 1 (by rfl) ⟨106484, by rfl⟩ : syracuseStep 141979 = 212969) B212969
theorem B142107 : Blo 139791 142107 := bstep (se 1 (by rfl) ⟨106580, by rfl⟩ : syracuseStep 142107 = 213161) B213161
theorem B240455 : Blo 139791 240455 := bstep (se 1 (by rfl) ⟨180341, by rfl⟩ : syracuseStep 240455 = 360683) B360683
theorem B404345 : Blo 139791 404345 := bstep (se 2 (by rfl) ⟨151629, by rfl⟩ : syracuseStep 404345 = 303259) B303259
theorem B142319 : Blo 139791 142319 := bstep (se 1 (by rfl) ⟨106739, by rfl⟩ : syracuseStep 142319 = 213479) B213479
theorem B142503 : Blo 139791 142503 := bstep (se 1 (by rfl) ⟨106877, by rfl⟩ : syracuseStep 142503 = 213755) B213755
theorem B535997 : Blo 139791 535997 := bstep (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) B200999
theorem B142799 : Blo 139791 142799 := bstep (se 1 (by rfl) ⟨107099, by rfl⟩ : syracuseStep 142799 = 214199) B214199
theorem B1224173 : Blo 139791 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B142895 : Blo 139791 142895 := bstep (se 1 (by rfl) ⟨107171, by rfl⟩ : syracuseStep 142895 = 214343) B214343
theorem B142959 : Blo 139791 142959 := bstep (se 1 (by rfl) ⟨107219, by rfl⟩ : syracuseStep 142959 = 214439) B214439
theorem B143079 : Blo 139791 143079 := bstep (se 1 (by rfl) ⟨107309, by rfl⟩ : syracuseStep 143079 = 214619) B214619
theorem B143391 : Blo 139791 143391 := bstep (se 1 (by rfl) ⟨107543, by rfl⟩ : syracuseStep 143391 = 215087) B215087
theorem B405587 : Blo 139791 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B143567 : Blo 139791 143567 := bstep (se 1 (by rfl) ⟨107675, by rfl⟩ : syracuseStep 143567 = 215351) B215351
theorem B2044115 : Blo 139791 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B864503 : Blo 139791 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B241967 : Blo 139791 241967 := bstep (se 1 (by rfl) ⟨181475, by rfl⟩ : syracuseStep 241967 = 362951) B362951
theorem B143687 : Blo 139791 143687 := bstep (se 1 (by rfl) ⟨107765, by rfl⟩ : syracuseStep 143687 = 215531) B215531
theorem B210143 : Blo 139791 210143 := bstep (se 1 (by rfl) ⟨157607, by rfl⟩ : syracuseStep 210143 = 315215) B315215
theorem B472607 : Blo 139791 472607 := bstep (se 1 (by rfl) ⟨354455, by rfl⟩ : syracuseStep 472607 = 708911) B708911
theorem B210623 : Blo 139791 210623 := bstep (se 1 (by rfl) ⟨157967, by rfl⟩ : syracuseStep 210623 = 315935) B315935
theorem B505607 : Blo 139791 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B210911 : Blo 139791 210911 := bstep (se 1 (by rfl) ⟨158183, by rfl⟩ : syracuseStep 210911 = 316367) B316367
theorem B210971 : Blo 139791 210971 := bstep (se 1 (by rfl) ⟨158228, by rfl⟩ : syracuseStep 210971 = 316457) B316457
theorem B473255 : Blo 139791 473255 := bstep (se 1 (by rfl) ⟨354941, by rfl⟩ : syracuseStep 473255 = 709883) B709883
theorem B211151 : Blo 139791 211151 := bstep (se 1 (by rfl) ⟨158363, by rfl⟩ : syracuseStep 211151 = 316727) B316727
theorem B211163 : Blo 139791 211163 := bstep (se 1 (by rfl) ⟨158372, by rfl⟩ : syracuseStep 211163 = 316745) B316745
theorem B2308447 : Blo 139791 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B211355 : Blo 139791 211355 := bstep (se 1 (by rfl) ⟨158516, by rfl⟩ : syracuseStep 211355 = 317033) B317033
theorem B211775 : Blo 139791 211775 := bstep (se 1 (by rfl) ⟨158831, by rfl⟩ : syracuseStep 211775 = 317663) B317663
theorem B211823 : Blo 139791 211823 := bstep (se 1 (by rfl) ⟨158867, by rfl⟩ : syracuseStep 211823 = 317735) B317735
theorem B179167 : Blo 139791 179167 := bstep (se 1 (by rfl) ⟨134375, by rfl⟩ : syracuseStep 179167 = 268751) B268751
theorem B408559 : Blo 139791 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B212063 : Blo 139791 212063 := bstep (se 1 (by rfl) ⟨159047, by rfl⟩ : syracuseStep 212063 = 318095) B318095
theorem B7847059 : Blo 139791 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B212123 : Blo 139791 212123 := bstep (se 1 (by rfl) ⟨159092, by rfl⟩ : syracuseStep 212123 = 318185) B318185
theorem B1031399 : Blo 139791 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B867671 : Blo 139791 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B408959 : Blo 139791 408959 := bstep (se 1 (by rfl) ⟨306719, by rfl⟩ : syracuseStep 408959 = 613439) B613439
theorem B310825 : Blo 139791 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B933599 : Blo 139791 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B6603227 : Blo 139791 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B541343 : Blo 139791 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B541511 : Blo 139791 541511 := bstep (se 1 (by rfl) ⟨406133, by rfl⟩ : syracuseStep 541511 = 812267) B812267
theorem B607439 : Blo 139791 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B2606995 : Blo 139791 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B477161 : Blo 139791 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B215177 : Blo 139791 215177 := bstep (se 2 (by rfl) ⟨80691, by rfl⟩ : syracuseStep 215177 = 161383) B161383
theorem B477467 : Blo 139791 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B1165763 : Blo 139791 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B609353 : Blo 139791 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B511721 : Blo 139791 511721 := bstep (se 2 (by rfl) ⟨191895, by rfl⟩ : syracuseStep 511721 = 383791) B383791
theorem B1560323 : Blo 139791 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B479357 : Blo 139791 479357 := bstep (se 3 (by rfl) ⟨89879, by rfl⟩ : syracuseStep 479357 = 179759) B179759
theorem B1069331 : Blo 139791 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B316223 : Blo 139791 316223 := bstep (se 1 (by rfl) ⟨237167, by rfl⟩ : syracuseStep 316223 = 474335) B474335
theorem B4051781 : Blo 139791 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B4576297 : Blo 139791 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B316583 : Blo 139791 316583 := bstep (se 1 (by rfl) ⟨237437, by rfl⟩ : syracuseStep 316583 = 474875) B474875
theorem B1202303 : Blo 139791 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B809099 : Blo 139791 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B613079 : Blo 139791 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B318203 : Blo 139791 318203 := bstep (se 1 (by rfl) ⟨238652, by rfl⟩ : syracuseStep 318203 = 477305) B477305
theorem B482057 : Blo 139791 482057 := bstep (se 2 (by rfl) ⟨180771, by rfl⟩ : syracuseStep 482057 = 361543) B361543
theorem B2284321 : Blo 139791 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B482111 : Blo 139791 482111 := bstep (se 1 (by rfl) ⟨361583, by rfl⟩ : syracuseStep 482111 = 723167) B723167
theorem B318419 : Blo 139791 318419 := bstep (se 1 (by rfl) ⟨238814, by rfl⟩ : syracuseStep 318419 = 477629) B477629
theorem B318527 : Blo 139791 318527 := bstep (se 1 (by rfl) ⟨238895, by rfl⟩ : syracuseStep 318527 = 477791) B477791
theorem B2022893 : Blo 139791 2022893 := bstep (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) B758585
theorem B2186813 : Blo 139791 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B2711333 : Blo 139791 2711333 := bstep (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) B508375
theorem B1466369 : Blo 139791 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B975311 : Blo 139791 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B320057 : Blo 139791 320057 := bstep (se 2 (by rfl) ⟨120021, by rfl⟩ : syracuseStep 320057 = 240043) B240043
theorem B1794797 : Blo 139791 1794797 := bstep (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) B673049
theorem B2155511 : Blo 139791 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B320777 : Blo 139791 320777 := bstep (se 2 (by rfl) ⟨120291, by rfl⟩ : syracuseStep 320777 = 240583) B240583
theorem B550583 : Blo 139791 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B157423 : Blo 139791 157423 := bstep (se 1 (by rfl) ⟨118067, by rfl⟩ : syracuseStep 157423 = 236135) B236135
theorem B157531 : Blo 139791 157531 := bstep (se 1 (by rfl) ⟨118148, by rfl⟩ : syracuseStep 157531 = 236297) B236297
theorem B2910167 : Blo 139791 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B322361 : Blo 139791 322361 := bstep (se 2 (by rfl) ⟨120885, by rfl⟩ : syracuseStep 322361 = 241771) B241771
theorem B355337 : Blo 139791 355337 := bstep (se 2 (by rfl) ⟨133251, by rfl⟩ : syracuseStep 355337 = 266503) B266503
theorem B912799 : Blo 139791 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B323495 : Blo 139791 323495 := bstep (se 1 (by rfl) ⟨242621, by rfl⟩ : syracuseStep 323495 = 485243) B485243
theorem B2093165 : Blo 139791 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B258427 : Blo 139791 258427 := bstep (se 1 (by rfl) ⟨193820, by rfl⟩ : syracuseStep 258427 = 387641) B387641
theorem B455159 : Blo 139791 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B4551389 : Blo 139791 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B1209275 : Blo 139791 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B357311 : Blo 139791 357311 := bstep (se 1 (by rfl) ⟨267983, by rfl⟩ : syracuseStep 357311 = 535967) B535967
theorem B160879 : Blo 139791 160879 := bstep (se 1 (by rfl) ⟨120659, by rfl⟩ : syracuseStep 160879 = 241319) B241319
theorem B194015 : Blo 139791 194015 := bstep (se 1 (by rfl) ⟨145511, by rfl⟩ : syracuseStep 194015 = 291023) B291023
theorem B358121 : Blo 139791 358121 := bstep (se 2 (by rfl) ⟨134295, by rfl⟩ : syracuseStep 358121 = 268591) B268591
theorem B3471437 : Blo 139791 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B719279 : Blo 139791 719279 := bstep (se 1 (by rfl) ⟨539459, by rfl⟩ : syracuseStep 719279 = 1078919) B1078919
theorem B817879 : Blo 139791 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B2357981 : Blo 139791 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B1244335 : Blo 139791 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B1834163 : Blo 139791 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B359903 : Blo 139791 359903 := bstep (se 1 (by rfl) ⟨269927, by rfl⟩ : syracuseStep 359903 = 539855) B539855
theorem B982529 : Blo 139791 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B360359 : Blo 139791 360359 := bstep (se 1 (by rfl) ⟨270269, by rfl⟩ : syracuseStep 360359 = 540539) B540539
theorem B360895 : Blo 139791 360895 := bstep (se 1 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 360895 = 541343) B541343
theorem B361007 : Blo 139791 361007 := bstep (se 1 (by rfl) ⟨270755, by rfl⟩ : syracuseStep 361007 = 541511) B541511
theorem B721547 : Blo 139791 721547 := bstep (se 1 (by rfl) ⟨541160, by rfl⟩ : syracuseStep 721547 = 1082321) B1082321
theorem B2851549 : Blo 139791 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B721871 : Blo 139791 721871 := bstep (se 1 (by rfl) ⟨541403, by rfl⟩ : syracuseStep 721871 = 1082807) B1082807
theorem B3475993 : Blo 139791 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B363649 : Blo 139791 363649 := bstep (se 2 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 363649 = 272737) B272737
theorem B331447 : Blo 139791 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B1217065 : Blo 139791 1217065 := bstep (se 2 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 1217065 = 912799) B912799
theorem B201307 : Blo 139791 201307 := bstep (se 1 (by rfl) ⟨150980, by rfl⟩ : syracuseStep 201307 = 301961) B301961
theorem B1348595 : Blo 139791 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B1807555 : Blo 139791 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B399401 : Blo 139791 399401 := bstep (se 2 (by rfl) ⟨149775, by rfl⟩ : syracuseStep 399401 = 299551) B299551
theorem B367055 : Blo 139791 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B1940111 : Blo 139791 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B6101729 : Blo 139791 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B269563 : Blo 139791 269563 := bstep (se 1 (by rfl) ⟨202172, by rfl⟩ : syracuseStep 269563 = 404345) B404345
theorem B236891 : Blo 139791 236891 := bstep (se 1 (by rfl) ⟨177668, by rfl⟩ : syracuseStep 236891 = 355337) B355337
theorem B270391 : Blo 139791 270391 := bstep (se 1 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 270391 = 405587) B405587
theorem B303439 : Blo 139791 303439 := bstep (se 1 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 303439 = 455159) B455159
theorem B238207 : Blo 139791 238207 := bstep (se 1 (by rfl) ⟨178655, by rfl⟩ : syracuseStep 238207 = 357311) B357311
theorem B140095 : Blo 139791 140095 := bstep (se 1 (by rfl) ⟨105071, by rfl⟩ : syracuseStep 140095 = 210143) B210143
theorem B1090505 : Blo 139791 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B533537 : Blo 139791 533537 := bstep (se 2 (by rfl) ⟨200076, by rfl⟩ : syracuseStep 533537 = 400153) B400153
theorem B140415 : Blo 139791 140415 := bstep (se 1 (by rfl) ⟨105311, by rfl⟩ : syracuseStep 140415 = 210623) B210623
theorem B238747 : Blo 139791 238747 := bstep (se 1 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 238747 = 358121) B358121
theorem B238889 : Blo 139791 238889 := bstep (se 2 (by rfl) ⟨89583, by rfl⟩ : syracuseStep 238889 = 179167) B179167
theorem B140607 : Blo 139791 140607 := bstep (se 1 (by rfl) ⟨105455, by rfl⟩ : syracuseStep 140607 = 210911) B210911
theorem B140647 : Blo 139791 140647 := bstep (se 1 (by rfl) ⟨105485, by rfl⟩ : syracuseStep 140647 = 210971) B210971
theorem B140767 : Blo 139791 140767 := bstep (se 1 (by rfl) ⟨105575, by rfl⟩ : syracuseStep 140767 = 211151) B211151
theorem B140775 : Blo 139791 140775 := bstep (se 1 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 140775 = 211163) B211163
theorem B10462745 : Blo 139791 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B140903 : Blo 139791 140903 := bstep (se 1 (by rfl) ⟨105677, by rfl⟩ : syracuseStep 140903 = 211355) B211355
theorem B141183 : Blo 139791 141183 := bstep (se 1 (by rfl) ⟨105887, by rfl⟩ : syracuseStep 141183 = 211775) B211775
theorem B141215 : Blo 139791 141215 := bstep (se 1 (by rfl) ⟨105911, by rfl⟩ : syracuseStep 141215 = 211823) B211823
theorem B141375 : Blo 139791 141375 := bstep (se 1 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 141375 = 212063) B212063
theorem B141415 : Blo 139791 141415 := bstep (se 1 (by rfl) ⟨106061, by rfl⟩ : syracuseStep 141415 = 212123) B212123
theorem B1222775 : Blo 139791 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B272639 : Blo 139791 272639 := bstep (se 1 (by rfl) ⟨204479, by rfl⟩ : syracuseStep 272639 = 408959) B408959
theorem B239935 : Blo 139791 239935 := bstep (se 1 (by rfl) ⟨179951, by rfl⟩ : syracuseStep 239935 = 359903) B359903
theorem B240239 : Blo 139791 240239 := bstep (se 1 (by rfl) ⟨180179, by rfl⟩ : syracuseStep 240239 = 360359) B360359
theorem B404129 : Blo 139791 404129 := bstep (se 2 (by rfl) ⟨151548, by rfl⟩ : syracuseStep 404129 = 303097) B303097
theorem B1223423 : Blo 139791 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B4402151 : Blo 139791 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B896807 : Blo 139791 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B143451 : Blo 139791 143451 := bstep (se 1 (by rfl) ⟨107588, by rfl⟩ : syracuseStep 143451 = 215177) B215177
theorem B406235 : Blo 139791 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B1749815 : Blo 139791 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B537425 : Blo 139791 537425 := bstep (se 2 (by rfl) ⟨201534, by rfl⟩ : syracuseStep 537425 = 403069) B403069
theorem B209897 : Blo 139791 209897 := bstep (se 2 (by rfl) ⟨78711, by rfl⟩ : syracuseStep 209897 = 157423) B157423
theorem B210041 : Blo 139791 210041 := bstep (se 2 (by rfl) ⟨78765, by rfl⟩ : syracuseStep 210041 = 157531) B157531
theorem B341147 : Blo 139791 341147 := bstep (se 1 (by rfl) ⟨255860, by rfl⟩ : syracuseStep 341147 = 511721) B511721
theorem B177319 : Blo 139791 177319 := bstep (se 1 (by rfl) ⟨132989, by rfl⟩ : syracuseStep 177319 = 265979) B265979
theorem B5748029 : Blo 139791 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B767407 : Blo 139791 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B177643 : Blo 139791 177643 := bstep (se 1 (by rfl) ⟨133232, by rfl⟩ : syracuseStep 177643 = 266465) B266465
theorem B2209451 : Blo 139791 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1619837 : Blo 139791 1619837 := bstep (se 3 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 1619837 = 607439) B607439
theorem B210815 : Blo 139791 210815 := bstep (se 1 (by rfl) ⟨158111, by rfl⟩ : syracuseStep 210815 = 316223) B316223
theorem B2701187 : Blo 139791 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B5027777 : Blo 139791 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B211055 : Blo 139791 211055 := bstep (se 1 (by rfl) ⟨158291, by rfl⟩ : syracuseStep 211055 = 316583) B316583
theorem B1161539 : Blo 139791 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B801535 : Blo 139791 801535 := bstep (se 1 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 801535 = 1202303) B1202303
theorem B539399 : Blo 139791 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B408719 : Blo 139791 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B212135 : Blo 139791 212135 := bstep (se 1 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 212135 = 318203) B318203
theorem B1359017 : Blo 139791 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B212279 : Blo 139791 212279 := bstep (se 1 (by rfl) ⟨159209, by rfl⟩ : syracuseStep 212279 = 318419) B318419
theorem B212351 : Blo 139791 212351 := bstep (se 1 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 212351 = 318527) B318527
theorem B1457875 : Blo 139791 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B180463 : Blo 139791 180463 := bstep (se 1 (by rfl) ⟨135347, by rfl⟩ : syracuseStep 180463 = 270695) B270695
theorem B213371 : Blo 139791 213371 := bstep (se 1 (by rfl) ⟨160028, by rfl⟩ : syracuseStep 213371 = 320057) B320057
theorem B508319 : Blo 139791 508319 := bstep (se 1 (by rfl) ⟨381239, by rfl⟩ : syracuseStep 508319 = 762479) B762479
theorem B1196531 : Blo 139791 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B344569 : Blo 139791 344569 := bstep (se 2 (by rfl) ⟨129213, by rfl⟩ : syracuseStep 344569 = 258427) B258427
theorem B213851 : Blo 139791 213851 := bstep (se 1 (by rfl) ⟨160388, by rfl⟩ : syracuseStep 213851 = 320777) B320777
theorem B214505 : Blo 139791 214505 := bstep (se 2 (by rfl) ⟨80439, by rfl⟩ : syracuseStep 214505 = 160879) B160879
theorem B214907 : Blo 139791 214907 := bstep (se 1 (by rfl) ⟨161180, by rfl⟩ : syracuseStep 214907 = 322361) B322361
theorem B215663 : Blo 139791 215663 := bstep (se 1 (by rfl) ⟨161747, by rfl⟩ : syracuseStep 215663 = 323495) B323495
theorem B1395443 : Blo 139791 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B5393141 : Blo 139791 5393141 := bstep (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) B505607
theorem B1362743 : Blo 139791 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B576335 : Blo 139791 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B3034259 : Blo 139791 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B806183 : Blo 139791 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B315071 : Blo 139791 315071 := bstep (se 1 (by rfl) ⟨236303, by rfl⟩ : syracuseStep 315071 = 472607) B472607
theorem B544745 : Blo 139791 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B2314291 : Blo 139791 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B315503 : Blo 139791 315503 := bstep (se 1 (by rfl) ⟨236627, by rfl⟩ : syracuseStep 315503 = 473255) B473255
theorem B1659113 : Blo 139791 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B479519 : Blo 139791 479519 := bstep (se 1 (by rfl) ⟨359639, by rfl⟩ : syracuseStep 479519 = 719279) B719279
theorem B414433 : Blo 139791 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B578447 : Blo 139791 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B971689 : Blo 139791 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B2708873 : Blo 139791 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B480761 : Blo 139791 480761 := bstep (se 2 (by rfl) ⟨180285, by rfl⟩ : syracuseStep 480761 = 360571) B360571
theorem B480923 : Blo 139791 480923 := bstep (se 1 (by rfl) ⟨360692, by rfl⟩ : syracuseStep 480923 = 721385) B721385
theorem B481895 : Blo 139791 481895 := bstep (se 1 (by rfl) ⟨361421, by rfl⟩ : syracuseStep 481895 = 722843) B722843
theorem B318107 : Blo 139791 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B318311 : Blo 139791 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B810283 : Blo 139791 810283 := bstep (se 1 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 810283 = 1215425) B1215425
theorem B1040215 : Blo 139791 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B319571 : Blo 139791 319571 := bstep (se 1 (by rfl) ⟨239678, by rfl⟩ : syracuseStep 319571 = 479357) B479357
theorem B319625 : Blo 139791 319625 := bstep (se 2 (by rfl) ⟨119859, by rfl⟩ : syracuseStep 319625 = 239719) B239719
theorem B483515 : Blo 139791 483515 := bstep (se 1 (by rfl) ⟨362636, by rfl⟩ : syracuseStep 483515 = 725273) B725273
theorem B1139923 : Blo 139791 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B517373 : Blo 139791 517373 := bstep (se 3 (by rfl) ⟨97007, by rfl⟩ : syracuseStep 517373 = 194015) B194015
theorem B484919 : Blo 139791 484919 := bstep (se 1 (by rfl) ⟨363689, by rfl⟩ : syracuseStep 484919 = 727379) B727379
theorem B353929 : Blo 139791 353929 := bstep (se 2 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 353929 = 265447) B265447
theorem B321371 : Blo 139791 321371 := bstep (se 1 (by rfl) ⟨241028, by rfl⟩ : syracuseStep 321371 = 482057) B482057
theorem B321407 : Blo 139791 321407 := bstep (se 1 (by rfl) ⟨241055, by rfl⟩ : syracuseStep 321407 = 482111) B482111
theorem B158107 : Blo 139791 158107 := bstep (se 1 (by rfl) ⟨118580, by rfl⟩ : syracuseStep 158107 = 237161) B237161
theorem B2320903 : Blo 139791 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B977579 : Blo 139791 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B486175 : Blo 139791 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B650207 : Blo 139791 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B1141769 : Blo 139791 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B159439 : Blo 139791 159439 := bstep (se 1 (by rfl) ⟨119579, by rfl⟩ : syracuseStep 159439 = 239159) B239159
theorem B3108701 : Blo 139791 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B356795 : Blo 139791 356795 := bstep (se 1 (by rfl) ⟨267596, by rfl⟩ : syracuseStep 356795 = 535193) B535193
theorem B160303 : Blo 139791 160303 := bstep (se 1 (by rfl) ⟨120227, by rfl⟩ : syracuseStep 160303 = 240455) B240455
theorem B357331 : Blo 139791 357331 := bstep (se 1 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 357331 = 535997) B535997
theorem B816115 : Blo 139791 816115 := bstep (se 1 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 816115 = 1224173) B1224173
theorem B161311 : Blo 139791 161311 := bstep (se 1 (by rfl) ⟨120983, by rfl⟩ : syracuseStep 161311 = 241967) B241967
theorem B3077929 : Blo 139791 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B3045761 : Blo 139791 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B1571987 : Blo 139791 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B687599 : Blo 139791 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B655019 : Blo 139791 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B622399 : Blo 139791 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B360521 : Blo 139791 360521 := bstep (se 2 (by rfl) ⟨135195, by rfl⟩ : syracuseStep 360521 = 270391) B270391
theorem B459425 : Blo 139791 459425 := bstep (se 2 (by rfl) ⟨172284, by rfl⟩ : syracuseStep 459425 = 344569) B344569
theorem B1083293 : Blo 139791 1083293 := bstep (se 3 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 1083293 = 406235) B406235
theorem B363163 : Blo 139791 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B1805915 : Blo 139791 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B266267 : Blo 139791 266267 := bstep (se 1 (by rfl) ⟨199700, by rfl⟩ : syracuseStep 266267 = 399401) B399401
theorem B4067819 : Blo 139791 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B3085721 : Blo 139791 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B727003 : Blo 139791 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B268409 : Blo 139791 268409 := bstep (se 2 (by rfl) ⟨100653, by rfl⟩ : syracuseStep 268409 = 201307) B201307
theorem B1088153 : Blo 139791 1088153 := bstep (se 2 (by rfl) ⟨408057, by rfl⟩ : syracuseStep 1088153 = 816115) B816115
theorem B236425 : Blo 139791 236425 := bstep (se 2 (by rfl) ⟨88659, by rfl⟩ : syracuseStep 236425 = 177319) B177319
theorem B269419 : Blo 139791 269419 := bstep (se 1 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 269419 = 404129) B404129
theorem B1023209 : Blo 139791 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B236857 : Blo 139791 236857 := bstep (se 2 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 236857 = 177643) B177643
theorem B433471 : Blo 139791 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B761179 : Blo 139791 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B4103905 : Blo 139791 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B597871 : Blo 139791 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B237863 : Blo 139791 237863 := bstep (se 1 (by rfl) ⟨178397, by rfl⟩ : syracuseStep 237863 = 356795) B356795
theorem B139931 : Blo 139791 139931 := bstep (se 1 (by rfl) ⟨104948, by rfl⟩ : syracuseStep 139931 = 209897) B209897
theorem B140027 : Blo 139791 140027 := bstep (se 1 (by rfl) ⟨105020, by rfl⟩ : syracuseStep 140027 = 210041) B210041
theorem B140543 : Blo 139791 140543 := bstep (se 1 (by rfl) ⟨105407, by rfl⟩ : syracuseStep 140543 = 210815) B210815
theorem B3351851 : Blo 139791 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B140703 : Blo 139791 140703 := bstep (se 1 (by rfl) ⟨105527, by rfl⟩ : syracuseStep 140703 = 211055) B211055
theorem B272479 : Blo 139791 272479 := bstep (se 1 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 272479 = 408719) B408719
theorem B141423 : Blo 139791 141423 := bstep (se 1 (by rfl) ⟨106067, by rfl⟩ : syracuseStep 141423 = 212135) B212135
theorem B141519 : Blo 139791 141519 := bstep (se 1 (by rfl) ⟨106139, by rfl⟩ : syracuseStep 141519 = 212279) B212279
theorem B141567 : Blo 139791 141567 := bstep (se 1 (by rfl) ⟨106175, by rfl⟩ : syracuseStep 141567 = 212351) B212351
theorem B1943833 : Blo 139791 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B829865 : Blo 139791 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B436679 : Blo 139791 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B1386953 : Blo 139791 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B142247 : Blo 139791 142247 := bstep (se 1 (by rfl) ⟨106685, by rfl⟩ : syracuseStep 142247 = 213371) B213371
theorem B338879 : Blo 139791 338879 := bstep (se 1 (by rfl) ⟨254159, by rfl⟩ : syracuseStep 338879 = 508319) B508319
theorem B240617 : Blo 139791 240617 := bstep (se 2 (by rfl) ⟨90231, by rfl⟩ : syracuseStep 240617 = 180463) B180463
theorem B797687 : Blo 139791 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B240671 : Blo 139791 240671 := bstep (se 1 (by rfl) ⟨180503, by rfl⟩ : syracuseStep 240671 = 361007) B361007
theorem B404585 : Blo 139791 404585 := bstep (se 2 (by rfl) ⟨151719, by rfl⟩ : syracuseStep 404585 = 303439) B303439
theorem B142567 : Blo 139791 142567 := bstep (se 1 (by rfl) ⟨106925, by rfl⟩ : syracuseStep 142567 = 213851) B213851
theorem B143003 : Blo 139791 143003 := bstep (se 1 (by rfl) ⟨107252, by rfl⟩ : syracuseStep 143003 = 214505) B214505
theorem B143271 : Blo 139791 143271 := bstep (se 1 (by rfl) ⟨107453, by rfl⟩ : syracuseStep 143271 = 214907) B214907
theorem B1519897 : Blo 139791 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B143775 : Blo 139791 143775 := bstep (se 1 (by rfl) ⟨107831, by rfl⟩ : syracuseStep 143775 = 215663) B215663
theorem B930295 : Blo 139791 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B471905 : Blo 139791 471905 := bstep (se 2 (by rfl) ⟨176964, by rfl⟩ : syracuseStep 471905 = 353929) B353929
theorem B537455 : Blo 139791 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B210047 : Blo 139791 210047 := bstep (se 1 (by rfl) ⟨157535, by rfl⟩ : syracuseStep 210047 = 315071) B315071
theorem B210335 : Blo 139791 210335 := bstep (se 1 (by rfl) ⟨157751, by rfl⟩ : syracuseStep 210335 = 315503) B315503
theorem B210809 : Blo 139791 210809 := bstep (se 2 (by rfl) ⟨79053, by rfl⟩ : syracuseStep 210809 = 158107) B158107
theorem B899063 : Blo 139791 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B3094537 : Blo 139791 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B4634657 : Blo 139791 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B244703 : Blo 139791 244703 := bstep (se 1 (by rfl) ⟨183527, by rfl⟩ : syracuseStep 244703 = 367055) B367055
theorem B1293407 : Blo 139791 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B212071 : Blo 139791 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B212207 : Blo 139791 212207 := bstep (se 1 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 212207 = 318311) B318311
theorem B60833045 : Blo 139791 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B441929 : Blo 139791 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B212585 : Blo 139791 212585 := bstep (se 2 (by rfl) ⟨79719, by rfl⟩ : syracuseStep 212585 = 159439) B159439
theorem B213047 : Blo 139791 213047 := bstep (se 1 (by rfl) ⟨159785, by rfl⟩ : syracuseStep 213047 = 319571) B319571
theorem B213083 : Blo 139791 213083 := bstep (se 1 (by rfl) ⟨159812, by rfl⟩ : syracuseStep 213083 = 319625) B319625
theorem B1622753 : Blo 139791 1622753 := bstep (se 2 (by rfl) ⟨608532, by rfl⟩ : syracuseStep 1622753 = 1217065) B1217065
theorem B213737 : Blo 139791 213737 := bstep (se 2 (by rfl) ⟨80151, by rfl⟩ : syracuseStep 213737 = 160303) B160303
theorem B344915 : Blo 139791 344915 := bstep (se 1 (by rfl) ⟨258686, by rfl⟩ : syracuseStep 344915 = 517373) B517373
theorem B1295585 : Blo 139791 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B214247 : Blo 139791 214247 := bstep (se 1 (by rfl) ⟨160685, by rfl⟩ : syracuseStep 214247 = 321371) B321371
theorem B214271 : Blo 139791 214271 := bstep (se 1 (by rfl) ⟨160703, by rfl⟩ : syracuseStep 214271 = 321407) B321407
theorem B476441 : Blo 139791 476441 := bstep (se 2 (by rfl) ⟨178665, by rfl⟩ : syracuseStep 476441 = 357331) B357331
theorem B181759 : Blo 139791 181759 := bstep (se 1 (by rfl) ⟨136319, by rfl⟩ : syracuseStep 181759 = 272639) B272639
theorem B2410073 : Blo 139791 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B2934767 : Blo 139791 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B215081 : Blo 139791 215081 := bstep (se 2 (by rfl) ⟨80655, by rfl⟩ : syracuseStep 215081 = 161311) B161311
theorem B1166543 : Blo 139791 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B1068713 : Blo 139791 1068713 := bstep (se 2 (by rfl) ⟨400767, by rfl⟩ : syracuseStep 1068713 = 801535) B801535
theorem B774359 : Blo 139791 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B906011 : Blo 139791 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B481031 : Blo 139791 481031 := bstep (se 1 (by rfl) ⟨360773, by rfl⟩ : syracuseStep 481031 = 721547) B721547
theorem B481193 : Blo 139791 481193 := bstep (se 2 (by rfl) ⟨180447, by rfl⟩ : syracuseStep 481193 = 360895) B360895
theorem B481247 : Blo 139791 481247 := bstep (se 1 (by rfl) ⟨360935, by rfl⟩ : syracuseStep 481247 = 721871) B721871
theorem B317609 : Blo 139791 317609 := bstep (se 2 (by rfl) ⟨119103, by rfl⟩ : syracuseStep 317609 = 238207) B238207
theorem B318329 : Blo 139791 318329 := bstep (se 2 (by rfl) ⟨119373, by rfl⟩ : syracuseStep 318329 = 238747) B238747
theorem B3595427 : Blo 139791 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B908495 : Blo 139791 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B2022839 : Blo 139791 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B1106075 : Blo 139791 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B319679 : Blo 139791 319679 := bstep (se 1 (by rfl) ⟨239759, by rfl⟩ : syracuseStep 319679 = 479519) B479519
theorem B319913 : Blo 139791 319913 := bstep (se 2 (by rfl) ⟨119967, by rfl⟩ : syracuseStep 319913 = 239935) B239935
theorem B385631 : Blo 139791 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B320507 : Blo 139791 320507 := bstep (se 1 (by rfl) ⟨240380, by rfl⟩ : syracuseStep 320507 = 480761) B480761
theorem B648233 : Blo 139791 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B320615 : Blo 139791 320615 := bstep (se 1 (by rfl) ⟨240461, by rfl⟩ : syracuseStep 320615 = 480923) B480923
theorem B484865 : Blo 139791 484865 := bstep (se 2 (by rfl) ⟨181824, by rfl⟩ : syracuseStep 484865 = 363649) B363649
theorem B321263 : Blo 139791 321263 := bstep (se 1 (by rfl) ⟨240947, by rfl⟩ : syracuseStep 321263 = 481895) B481895
theorem B5891869 : Blo 139791 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B157927 : Blo 139791 157927 := bstep (se 1 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 157927 = 236891) B236891
theorem B322343 : Blo 139791 322343 := bstep (se 1 (by rfl) ⟨241757, by rfl⟩ : syracuseStep 322343 = 483515) B483515
theorem B355691 : Blo 139791 355691 := bstep (se 1 (by rfl) ⟨266768, by rfl⟩ : syracuseStep 355691 = 533537) B533537
theorem B159259 : Blo 139791 159259 := bstep (se 1 (by rfl) ⟨119444, by rfl⟩ : syracuseStep 159259 = 238889) B238889
theorem B552577 : Blo 139791 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B6975163 : Blo 139791 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B323279 : Blo 139791 323279 := bstep (se 1 (by rfl) ⟨242459, by rfl⟩ : syracuseStep 323279 = 484919) B484919
theorem B815183 : Blo 139791 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B160159 : Blo 139791 160159 := bstep (se 1 (by rfl) ⟨120119, by rfl⟩ : syracuseStep 160159 = 240239) B240239
theorem B651719 : Blo 139791 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B815615 : Blo 139791 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B1536893 : Blo 139791 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B358283 : Blo 139791 358283 := bstep (se 1 (by rfl) ⟨268712, by rfl⟩ : syracuseStep 358283 = 537425) B537425
theorem B227431 : Blo 139791 227431 := bstep (se 1 (by rfl) ⟨170573, by rfl⟩ : syracuseStep 227431 = 341147) B341147
theorem B3832019 : Blo 139791 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B1079891 : Blo 139791 1079891 := bstep (se 1 (by rfl) ⟨809918, by rfl⟩ : syracuseStep 1079891 = 1619837) B1619837
theorem B1800791 : Blo 139791 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B2030507 : Blo 139791 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B359417 : Blo 139791 359417 := bstep (se 2 (by rfl) ⟨134781, by rfl⟩ : syracuseStep 359417 = 269563) B269563
theorem B1080377 : Blo 139791 1080377 := bstep (se 2 (by rfl) ⟨405141, by rfl⟩ : syracuseStep 1080377 = 810283) B810283
theorem B359599 : Blo 139791 359599 := bstep (se 1 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 359599 = 539399) B539399
theorem B1047991 : Blo 139791 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B8289869 : Blo 139791 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B458399 : Blo 139791 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B2949533 : Blo 139791 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B1081835 : Blo 139791 1081835 := bstep (se 1 (by rfl) ⟨811376, by rfl⟩ : syracuseStep 1081835 = 1622753) B1622753
theorem B1212965 : Blo 139791 1212965 := bstep (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) B227431
theorem B229943 : Blo 139791 229943 := bstep (se 1 (by rfl) ⟨172457, by rfl⟩ : syracuseStep 229943 = 344915) B344915
theorem B1606715 : Blo 139791 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B722195 : Blo 139791 722195 := bstep (se 1 (by rfl) ⟨541646, by rfl⟩ : syracuseStep 722195 = 1083293) B1083293
theorem B363305 : Blo 139791 363305 := bstep (se 2 (by rfl) ⟨136239, by rfl⟩ : syracuseStep 363305 = 272479) B272479
theorem B2591777 : Blo 139791 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B725435 : Blo 139791 725435 := bstep (se 1 (by rfl) ⟨544076, by rfl⟩ : syracuseStep 725435 = 1088153) B1088153
theorem B2396951 : Blo 139791 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B1348559 : Blo 139791 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B432155 : Blo 139791 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B2234567 : Blo 139791 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B924635 : Blo 139791 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B531791 : Blo 139791 531791 := bstep (se 1 (by rfl) ⟨398843, by rfl⟩ : syracuseStep 531791 = 797687) B797687
theorem B269723 : Blo 139791 269723 := bstep (se 1 (by rfl) ⟨202292, by rfl⟩ : syracuseStep 269723 = 404585) B404585
theorem B237127 : Blo 139791 237127 := bstep (se 1 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 237127 = 355691) B355691
theorem B434479 : Blo 139791 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B1024595 : Blo 139791 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B140031 : Blo 139791 140031 := bstep (se 1 (by rfl) ⟨105023, by rfl⟩ : syracuseStep 140031 = 210047) B210047
theorem B140223 : Blo 139791 140223 := bstep (se 1 (by rfl) ⟨105167, by rfl⟩ : syracuseStep 140223 = 210335) B210335
theorem B140539 : Blo 139791 140539 := bstep (se 1 (by rfl) ⟨105404, by rfl⟩ : syracuseStep 140539 = 210809) B210809
theorem B238855 : Blo 139791 238855 := bstep (se 1 (by rfl) ⟨179141, by rfl⟩ : syracuseStep 238855 = 358283) B358283
theorem B599375 : Blo 139791 599375 := bstep (se 1 (by rfl) ⟨449531, by rfl⟩ : syracuseStep 599375 = 899063) B899063
theorem B3089771 : Blo 139791 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B1222397 : Blo 139791 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B1353671 : Blo 139791 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B239611 : Blo 139791 239611 := bstep (se 1 (by rfl) ⟨179708, by rfl⟩ : syracuseStep 239611 = 359417) B359417
theorem B862271 : Blo 139791 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B141471 : Blo 139791 141471 := bstep (se 1 (by rfl) ⟨106103, by rfl⟩ : syracuseStep 141471 = 212207) B212207
theorem B141723 : Blo 139791 141723 := bstep (se 1 (by rfl) ⟨106292, by rfl⟩ : syracuseStep 141723 = 212585) B212585
theorem B797161 : Blo 139791 797161 := bstep (se 2 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 797161 = 597871) B597871
theorem B142031 : Blo 139791 142031 := bstep (se 1 (by rfl) ⟨106523, by rfl⟩ : syracuseStep 142031 = 213047) B213047
theorem B240347 : Blo 139791 240347 := bstep (se 1 (by rfl) ⟨180260, by rfl⟩ : syracuseStep 240347 = 360521) B360521
theorem B142055 : Blo 139791 142055 := bstep (se 1 (by rfl) ⟨106541, by rfl⟩ : syracuseStep 142055 = 213083) B213083
theorem B306283 : Blo 139791 306283 := bstep (se 1 (by rfl) ⟨229712, by rfl⟩ : syracuseStep 306283 = 459425) B459425
theorem B142491 : Blo 139791 142491 := bstep (se 1 (by rfl) ⟨106868, by rfl⟩ : syracuseStep 142491 = 213737) B213737
theorem B863723 : Blo 139791 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B142831 : Blo 139791 142831 := bstep (se 1 (by rfl) ⟨107123, by rfl⟩ : syracuseStep 142831 = 214247) B214247
theorem B142847 : Blo 139791 142847 := bstep (se 1 (by rfl) ⟨107135, by rfl⟩ : syracuseStep 142847 = 214271) B214271
theorem B143387 : Blo 139791 143387 := bstep (se 1 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 143387 = 215081) B215081
theorem B242345 : Blo 139791 242345 := bstep (se 2 (by rfl) ⟨90879, by rfl⟩ : syracuseStep 242345 = 181759) B181759
theorem B4961573 : Blo 139791 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B210569 : Blo 139791 210569 := bstep (se 2 (by rfl) ⟨78963, by rfl⟩ : syracuseStep 210569 = 157927) B157927
theorem B604007 : Blo 139791 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B178939 : Blo 139791 178939 := bstep (se 1 (by rfl) ⟨134204, by rfl⟩ : syracuseStep 178939 = 268409) B268409
theorem B211739 : Blo 139791 211739 := bstep (se 1 (by rfl) ⟨158804, by rfl⟩ : syracuseStep 211739 = 317609) B317609
theorem B212219 : Blo 139791 212219 := bstep (se 1 (by rfl) ⟨159164, by rfl⟩ : syracuseStep 212219 = 318329) B318329
theorem B212345 : Blo 139791 212345 := bstep (se 2 (by rfl) ⟨79629, by rfl⟩ : syracuseStep 212345 = 159259) B159259
theorem B605663 : Blo 139791 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B736769 : Blo 139791 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B213119 : Blo 139791 213119 := bstep (se 1 (by rfl) ⟨159839, by rfl⟩ : syracuseStep 213119 = 319679) B319679
theorem B213275 : Blo 139791 213275 := bstep (se 1 (by rfl) ⟨159956, by rfl⟩ : syracuseStep 213275 = 319913) B319913
theorem B213545 : Blo 139791 213545 := bstep (se 2 (by rfl) ⟨80079, by rfl⟩ : syracuseStep 213545 = 160159) B160159
theorem B213671 : Blo 139791 213671 := bstep (se 1 (by rfl) ⟨160253, by rfl⟩ : syracuseStep 213671 = 320507) B320507
theorem B213743 : Blo 139791 213743 := bstep (se 1 (by rfl) ⟨160307, by rfl⟩ : syracuseStep 213743 = 320615) B320615
theorem B214175 : Blo 139791 214175 := bstep (se 1 (by rfl) ⟨160631, by rfl⟩ : syracuseStep 214175 = 321263) B321263
theorem B214895 : Blo 139791 214895 := bstep (se 1 (by rfl) ⟨161171, by rfl⟩ : syracuseStep 214895 = 322343) B322343
theorem B215519 : Blo 139791 215519 := bstep (se 1 (by rfl) ⟨161639, by rfl⟩ : syracuseStep 215519 = 323279) B323279
theorem B969337 : Blo 139791 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B543455 : Blo 139791 543455 := bstep (se 1 (by rfl) ⟨407591, by rfl⟩ : syracuseStep 543455 = 815183) B815183
theorem B543743 : Blo 139791 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B314603 : Blo 139791 314603 := bstep (se 1 (by rfl) ⟨235952, by rfl⟩ : syracuseStep 314603 = 471905) B471905
theorem B315233 : Blo 139791 315233 := bstep (se 2 (by rfl) ⟨118212, by rfl⟩ : syracuseStep 315233 = 236425) B236425
theorem B282761 : Blo 139791 282761 := bstep (se 2 (by rfl) ⟨106035, by rfl⟩ : syracuseStep 282761 = 212071) B212071
theorem B22106317 : Blo 139791 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B479465 : Blo 139791 479465 := bstep (se 2 (by rfl) ⟨179799, by rfl⟩ : syracuseStep 479465 = 359599) B359599
theorem B1200527 : Blo 139791 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B315809 : Blo 139791 315809 := bstep (se 2 (by rfl) ⟨118428, by rfl⟩ : syracuseStep 315809 = 236857) B236857
theorem B577961 : Blo 139791 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B1397321 : Blo 139791 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B40555363 : Blo 139791 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B710045 : Blo 139791 710045 := bstep (se 3 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 710045 = 266267) B266267
theorem B317627 : Blo 139791 317627 := bstep (se 1 (by rfl) ⟨238220, by rfl⟩ : syracuseStep 317627 = 476441) B476441
theorem B1956511 : Blo 139791 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B777695 : Blo 139791 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B7855825 : Blo 139791 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B1203943 : Blo 139791 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B712475 : Blo 139791 712475 := bstep (se 1 (by rfl) ⟨534356, by rfl⟩ : syracuseStep 712475 = 1068713) B1068713
theorem B516239 : Blo 139791 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B2711879 : Blo 139791 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B484217 : Blo 139791 484217 := bstep (se 2 (by rfl) ⟨181581, by rfl⟩ : syracuseStep 484217 = 363163) B363163
theorem B2057147 : Blo 139791 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B320687 : Blo 139791 320687 := bstep (se 1 (by rfl) ⟨240515, by rfl⟩ : syracuseStep 320687 = 481031) B481031
theorem B320795 : Blo 139791 320795 := bstep (se 1 (by rfl) ⟨240596, by rfl⟩ : syracuseStep 320795 = 481193) B481193
theorem B320831 : Blo 139791 320831 := bstep (se 1 (by rfl) ⟨240623, by rfl⟩ : syracuseStep 320831 = 481247) B481247
theorem B682139 : Blo 139791 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B9300217 : Blo 139791 9300217 := bstep (se 2 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 9300217 = 6975163) B6975163
theorem B158575 : Blo 139791 158575 := bstep (se 1 (by rfl) ⟨118931, by rfl⟩ : syracuseStep 158575 = 237863) B237863
theorem B2026529 : Blo 139791 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B257087 : Blo 139791 257087 := bstep (se 1 (by rfl) ⟨192815, by rfl⟩ : syracuseStep 257087 = 385631) B385631
theorem B323243 : Blo 139791 323243 := bstep (se 1 (by rfl) ⟨242432, by rfl⟩ : syracuseStep 323243 = 484865) B484865
theorem B553243 : Blo 139791 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B291119 : Blo 139791 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B225919 : Blo 139791 225919 := bstep (se 1 (by rfl) ⟨169439, by rfl⟩ : syracuseStep 225919 = 338879) B338879
theorem B160411 : Blo 139791 160411 := bstep (se 1 (by rfl) ⟨120308, by rfl⟩ : syracuseStep 160411 = 240617) B240617
theorem B160447 : Blo 139791 160447 := bstep (se 1 (by rfl) ⟨120335, by rfl⟩ : syracuseStep 160447 = 240671) B240671
theorem B4126049 : Blo 139791 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B358303 : Blo 139791 358303 := bstep (se 1 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 358303 = 537455) B537455
theorem B2554679 : Blo 139791 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B359225 : Blo 139791 359225 := bstep (se 2 (by rfl) ⟨134709, by rfl⟩ : syracuseStep 359225 = 269419) B269419
theorem B719927 : Blo 139791 719927 := bstep (se 1 (by rfl) ⟨539945, by rfl⟩ : syracuseStep 719927 = 1079891) B1079891
theorem B1014905 : Blo 139791 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B163135 : Blo 139791 163135 := bstep (se 1 (by rfl) ⟨122351, by rfl⟩ : syracuseStep 163135 = 244703) B244703
theorem B720251 : Blo 139791 720251 := bstep (se 1 (by rfl) ⟨540188, by rfl⟩ : syracuseStep 720251 = 1080377) B1080377
theorem B5471873 : Blo 139791 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B294619 : Blo 139791 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B1966355 : Blo 139791 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B721223 : Blo 139791 721223 := bstep (se 1 (by rfl) ⟨540917, by rfl⟩ : syracuseStep 721223 = 1081835) B1081835
theorem B362303 : Blo 139791 362303 := bstep (se 1 (by rfl) ⟨271727, by rfl⟩ : syracuseStep 362303 = 543455) B543455
theorem B362495 : Blo 139791 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B1152413 : Blo 139791 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B1807919 : Blo 139791 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B399583 : Blo 139791 399583 := bstep (se 1 (by rfl) ⟨299687, by rfl⟩ : syracuseStep 399583 = 599375) B599375
theorem B54073817 : Blo 139791 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1351019 : Blo 139791 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B171391 : Blo 139791 171391 := bstep (se 1 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 171391 = 257087) B257087
theorem B238585 : Blo 139791 238585 := bstep (se 2 (by rfl) ⟨89469, by rfl⟩ : syracuseStep 238585 = 178939) B178939
theorem B140379 : Blo 139791 140379 := bstep (se 1 (by rfl) ⟨105284, by rfl⟩ : syracuseStep 140379 = 210569) B210569
theorem B402671 : Blo 139791 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B2073853 : Blo 139791 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B2303261 : Blo 139791 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B141159 : Blo 139791 141159 := bstep (se 1 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 141159 = 211739) B211739
theorem B239483 : Blo 139791 239483 := bstep (se 1 (by rfl) ⟨179612, by rfl⟩ : syracuseStep 239483 = 359225) B359225
theorem B141479 : Blo 139791 141479 := bstep (se 1 (by rfl) ⟨106109, by rfl⟩ : syracuseStep 141479 = 212219) B212219
theorem B141563 : Blo 139791 141563 := bstep (se 1 (by rfl) ⟨106172, by rfl⟩ : syracuseStep 141563 = 212345) B212345
theorem B403775 : Blo 139791 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B3647915 : Blo 139791 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B142079 : Blo 139791 142079 := bstep (se 1 (by rfl) ⟨106559, by rfl⟩ : syracuseStep 142079 = 213119) B213119
theorem B142183 : Blo 139791 142183 := bstep (se 1 (by rfl) ⟨106637, by rfl⟩ : syracuseStep 142183 = 213275) B213275
theorem B142363 : Blo 139791 142363 := bstep (se 1 (by rfl) ⟨106772, by rfl⟩ : syracuseStep 142363 = 213545) B213545
theorem B142447 : Blo 139791 142447 := bstep (se 1 (by rfl) ⟨106835, by rfl⟩ : syracuseStep 142447 = 213671) B213671
theorem B142495 : Blo 139791 142495 := bstep (se 1 (by rfl) ⟨106871, by rfl⟩ : syracuseStep 142495 = 213743) B213743
theorem B142783 : Blo 139791 142783 := bstep (se 1 (by rfl) ⟨107087, by rfl⟩ : syracuseStep 142783 = 214175) B214175
theorem B143263 : Blo 139791 143263 := bstep (se 1 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 143263 = 214895) B214895
theorem B143679 : Blo 139791 143679 := bstep (se 1 (by rfl) ⟨107759, by rfl⟩ : syracuseStep 143679 = 215519) B215519
theorem B242203 : Blo 139791 242203 := bstep (se 1 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 242203 = 363305) B363305
theorem B209735 : Blo 139791 209735 := bstep (se 1 (by rfl) ⟨157301, by rfl⟩ : syracuseStep 209735 = 314603) B314603
theorem B210155 : Blo 139791 210155 := bstep (se 1 (by rfl) ⟨157616, by rfl⟩ : syracuseStep 210155 = 315233) B315233
theorem B800351 : Blo 139791 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B210539 : Blo 139791 210539 := bstep (se 1 (by rfl) ⟨157904, by rfl⟩ : syracuseStep 210539 = 315809) B315809
theorem B12400289 : Blo 139791 12400289 := bstep (se 2 (by rfl) ⟨4650108, by rfl⟩ : syracuseStep 12400289 = 9300217) B9300217
theorem B931547 : Blo 139791 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B899039 : Blo 139791 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B1062881 : Blo 139791 1062881 := bstep (se 2 (by rfl) ⟨398580, by rfl⟩ : syracuseStep 1062881 = 797161) B797161
theorem B1292449 : Blo 139791 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B473363 : Blo 139791 473363 := bstep (se 1 (by rfl) ⟨355022, by rfl⟩ : syracuseStep 473363 = 710045) B710045
theorem B211433 : Blo 139791 211433 := bstep (se 2 (by rfl) ⟨79287, by rfl⟩ : syracuseStep 211433 = 158575) B158575
theorem B211751 : Blo 139791 211751 := bstep (se 1 (by rfl) ⟨158813, by rfl⟩ : syracuseStep 211751 = 317627) B317627
theorem B408377 : Blo 139791 408377 := bstep (se 2 (by rfl) ⟨153141, by rfl⟩ : syracuseStep 408377 = 306283) B306283
theorem B179815 : Blo 139791 179815 := bstep (se 1 (by rfl) ⟨134861, by rfl⟩ : syracuseStep 179815 = 269723) B269723
theorem B474983 : Blo 139791 474983 := bstep (se 1 (by rfl) ⟨356237, by rfl⟩ : syracuseStep 474983 = 712475) B712475
theorem B344159 : Blo 139791 344159 := bstep (se 1 (by rfl) ⟨258119, by rfl⟩ : syracuseStep 344159 = 516239) B516239
theorem B29475089 : Blo 139791 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B737657 : Blo 139791 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B1819037 : Blo 139791 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B213791 : Blo 139791 213791 := bstep (se 1 (by rfl) ⟨160343, by rfl⟩ : syracuseStep 213791 = 320687) B320687
theorem B213863 : Blo 139791 213863 := bstep (se 1 (by rfl) ⟨160397, by rfl⟩ : syracuseStep 213863 = 320795) B320795
theorem B213881 : Blo 139791 213881 := bstep (se 2 (by rfl) ⟨80205, by rfl⟩ : syracuseStep 213881 = 160411) B160411
theorem B213887 : Blo 139791 213887 := bstep (se 1 (by rfl) ⟨160415, by rfl⟩ : syracuseStep 213887 = 320831) B320831
theorem B213929 : Blo 139791 213929 := bstep (se 2 (by rfl) ⟨80223, by rfl⟩ : syracuseStep 213929 = 160447) B160447
theorem B902447 : Blo 139791 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B574847 : Blo 139791 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B215495 : Blo 139791 215495 := bstep (se 1 (by rfl) ⟨161621, by rfl⟩ : syracuseStep 215495 = 323243) B323243
theorem B477737 : Blo 139791 477737 := bstep (se 2 (by rfl) ⟨179151, by rfl⟩ : syracuseStep 477737 = 358303) B358303
theorem B2608681 : Blo 139791 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B217513 : Blo 139791 217513 := bstep (se 2 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 217513 = 163135) B163135
theorem B479951 : Blo 139791 479951 := bstep (se 1 (by rfl) ⟨359963, by rfl⟩ : syracuseStep 479951 = 719927) B719927
theorem B676603 : Blo 139791 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B316169 : Blo 139791 316169 := bstep (se 2 (by rfl) ⟨118563, by rfl⟩ : syracuseStep 316169 = 237127) B237127
theorem B480167 : Blo 139791 480167 := bstep (se 1 (by rfl) ⟨360125, by rfl⟩ : syracuseStep 480167 = 720251) B720251
theorem B10474433 : Blo 139791 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B808643 : Blo 139791 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B153295 : Blo 139791 153295 := bstep (se 1 (by rfl) ⟨114971, by rfl⟩ : syracuseStep 153295 = 229943) B229943
theorem B579305 : Blo 139791 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B1071143 : Blo 139791 1071143 := bstep (se 1 (by rfl) ⟨803357, by rfl⟩ : syracuseStep 1071143 = 1606715) B1606715
theorem B776317 : Blo 139791 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B481463 : Blo 139791 481463 := bstep (se 1 (by rfl) ⟨361097, by rfl⟩ : syracuseStep 481463 = 722195) B722195
theorem B318473 : Blo 139791 318473 := bstep (se 2 (by rfl) ⟨119427, by rfl⟩ : syracuseStep 318473 = 238855) B238855
theorem B1727851 : Blo 139791 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B319481 : Blo 139791 319481 := bstep (se 2 (by rfl) ⟨119805, by rfl⟩ : syracuseStep 319481 = 239611) B239611
theorem B188507 : Blo 139791 188507 := bstep (se 1 (by rfl) ⟨141380, by rfl⟩ : syracuseStep 188507 = 282761) B282761
theorem B319643 : Blo 139791 319643 := bstep (se 1 (by rfl) ⟨239732, by rfl⟩ : syracuseStep 319643 = 479465) B479465
theorem B385307 : Blo 139791 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B483623 : Blo 139791 483623 := bstep (se 1 (by rfl) ⟨362717, by rfl⟩ : syracuseStep 483623 = 725435) B725435
theorem B1597967 : Blo 139791 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B1204901 : Blo 139791 1204901 := bstep (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) B225919
theorem B616423 : Blo 139791 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B354527 : Blo 139791 354527 := bstep (se 1 (by rfl) ⟨265895, by rfl⟩ : syracuseStep 354527 = 531791) B531791
theorem B683063 : Blo 139791 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B5958845 : Blo 139791 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B322811 : Blo 139791 322811 := bstep (se 1 (by rfl) ⟨242108, by rfl⟩ : syracuseStep 322811 = 484217) B484217
theorem B1371431 : Blo 139791 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B2059847 : Blo 139791 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B814931 : Blo 139791 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B160231 : Blo 139791 160231 := bstep (se 1 (by rfl) ⟨120173, by rfl⟩ : syracuseStep 160231 = 240347) B240347
theorem B161563 : Blo 139791 161563 := bstep (se 1 (by rfl) ⟨121172, by rfl⟩ : syracuseStep 161563 = 242345) B242345
theorem B3307715 : Blo 139791 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B2750699 : Blo 139791 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B1703119 : Blo 139791 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B392825 : Blo 139791 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B1605257 : Blo 139791 1605257 := bstep (se 2 (by rfl) ⟨601971, by rfl⟩ : syracuseStep 1605257 = 1203943) B1203943
theorem B491179 : Blo 139791 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B229439 : Blo 139791 229439 := bstep (se 1 (by rfl) ⟨172079, by rfl⟩ : syracuseStep 229439 = 344159) B344159
theorem B1310903 : Blo 139791 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B491771 : Blo 139791 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B1212691 : Blo 139791 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B821897 : Blo 139791 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B6982955 : Blo 139791 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B3608549 : Blo 139791 3608549 := bstep (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) B676603
theorem B36049211 : Blo 139791 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B3478241 : Blo 139791 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B268447 : Blo 139791 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B236351 : Blo 139791 236351 := bstep (se 1 (by rfl) ⟨177263, by rfl⟩ : syracuseStep 236351 = 354527) B354527
theorem B269183 : Blo 139791 269183 := bstep (se 1 (by rfl) ⟨201887, by rfl⟩ : syracuseStep 269183 = 403775) B403775
theorem B2431943 : Blo 139791 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B3972563 : Blo 139791 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B532777 : Blo 139791 532777 := bstep (se 2 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 532777 = 399583) B399583
theorem B139823 : Blo 139791 139823 := bstep (se 1 (by rfl) ⟨104867, by rfl⟩ : syracuseStep 139823 = 209735) B209735
theorem B140103 : Blo 139791 140103 := bstep (se 1 (by rfl) ⟨105077, by rfl⟩ : syracuseStep 140103 = 210155) B210155
theorem B533567 : Blo 139791 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B140359 : Blo 139791 140359 := bstep (se 1 (by rfl) ⟨105269, by rfl⟩ : syracuseStep 140359 = 210539) B210539
theorem B8266859 : Blo 139791 8266859 := bstep (se 1 (by rfl) ⟨6200144, by rfl⟩ : syracuseStep 8266859 = 12400289) B12400289
theorem B599359 : Blo 139791 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B2205143 : Blo 139791 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B2270825 : Blo 139791 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B140955 : Blo 139791 140955 := bstep (se 1 (by rfl) ⟨105716, by rfl⟩ : syracuseStep 140955 = 211433) B211433
theorem B2303801 : Blo 139791 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B141167 : Blo 139791 141167 := bstep (se 1 (by rfl) ⟨105875, by rfl⟩ : syracuseStep 141167 = 211751) B211751
theorem B272251 : Blo 139791 272251 := bstep (se 1 (by rfl) ⟨204188, by rfl⟩ : syracuseStep 272251 = 408377) B408377
theorem B239753 : Blo 139791 239753 := bstep (se 2 (by rfl) ⟨89907, by rfl⟩ : syracuseStep 239753 = 179815) B179815
theorem B502685 : Blo 139791 502685 := bstep (se 3 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 502685 = 188507) B188507
theorem B142527 : Blo 139791 142527 := bstep (se 1 (by rfl) ⟨106895, by rfl⟩ : syracuseStep 142527 = 213791) B213791
theorem B142575 : Blo 139791 142575 := bstep (se 1 (by rfl) ⟨106931, by rfl⟩ : syracuseStep 142575 = 213863) B213863
theorem B142587 : Blo 139791 142587 := bstep (se 1 (by rfl) ⟨106940, by rfl⟩ : syracuseStep 142587 = 213881) B213881
theorem B142591 : Blo 139791 142591 := bstep (se 1 (by rfl) ⟨106943, by rfl⟩ : syracuseStep 142591 = 213887) B213887
theorem B142619 : Blo 139791 142619 := bstep (se 1 (by rfl) ⟨106964, by rfl⟩ : syracuseStep 142619 = 213929) B213929
theorem B601631 : Blo 139791 601631 := bstep (se 1 (by rfl) ⟨451223, by rfl⟩ : syracuseStep 601631 = 902447) B902447
theorem B241535 : Blo 139791 241535 := bstep (se 1 (by rfl) ⟨181151, by rfl⟩ : syracuseStep 241535 = 362303) B362303
theorem B241663 : Blo 139791 241663 := bstep (se 1 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 241663 = 362495) B362495
theorem B143663 : Blo 139791 143663 := bstep (se 1 (by rfl) ⟨107747, by rfl⟩ : syracuseStep 143663 = 215495) B215495
theorem B2765137 : Blo 139791 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B210779 : Blo 139791 210779 := bstep (se 1 (by rfl) ⟨158084, by rfl⟩ : syracuseStep 210779 = 316169) B316169
theorem B768275 : Blo 139791 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B539095 : Blo 139791 539095 := bstep (se 1 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 539095 = 808643) B808643
theorem B212315 : Blo 139791 212315 := bstep (se 1 (by rfl) ⟨159236, by rfl⟩ : syracuseStep 212315 = 318473) B318473
theorem B900679 : Blo 139791 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B212987 : Blo 139791 212987 := bstep (se 1 (by rfl) ⟨159740, by rfl⟩ : syracuseStep 212987 = 319481) B319481
theorem B213095 : Blo 139791 213095 := bstep (se 1 (by rfl) ⟨159821, by rfl⟩ : syracuseStep 213095 = 319643) B319643
theorem B1065311 : Blo 139791 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B803267 : Blo 139791 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B213641 : Blo 139791 213641 := bstep (se 2 (by rfl) ⟨80115, by rfl⟩ : syracuseStep 213641 = 160231) B160231
theorem B215207 : Blo 139791 215207 := bstep (se 1 (by rfl) ⟨161405, by rfl⟩ : syracuseStep 215207 = 322811) B322811
theorem B215417 : Blo 139791 215417 := bstep (se 2 (by rfl) ⟨80781, by rfl⟩ : syracuseStep 215417 = 161563) B161563
theorem B543287 : Blo 139791 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B1035089 : Blo 139791 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B1723265 : Blo 139791 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B708587 : Blo 139791 708587 := bstep (se 1 (by rfl) ⟨531440, by rfl⟩ : syracuseStep 708587 = 1062881) B1062881
theorem B315575 : Blo 139791 315575 := bstep (se 1 (by rfl) ⟨236681, by rfl⟩ : syracuseStep 315575 = 473363) B473363
theorem B1070171 : Blo 139791 1070171 := bstep (se 1 (by rfl) ⟨802628, by rfl⟩ : syracuseStep 1070171 = 1605257) B1605257
theorem B316655 : Blo 139791 316655 := bstep (se 1 (by rfl) ⟨237491, by rfl⟩ : syracuseStep 316655 = 474983) B474983
theorem B19650059 : Blo 139791 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B480815 : Blo 139791 480815 := bstep (se 1 (by rfl) ⟨360611, by rfl⟩ : syracuseStep 480815 = 721223) B721223
theorem B383231 : Blo 139791 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B318113 : Blo 139791 318113 := bstep (se 2 (by rfl) ⟨119292, by rfl⟩ : syracuseStep 318113 = 238585) B238585
theorem B318491 : Blo 139791 318491 := bstep (se 1 (by rfl) ⟨238868, by rfl⟩ : syracuseStep 318491 = 477737) B477737
theorem B319967 : Blo 139791 319967 := bstep (se 1 (by rfl) ⟨239975, by rfl⟩ : syracuseStep 319967 = 479951) B479951
theorem B320111 : Blo 139791 320111 := bstep (se 1 (by rfl) ⟨240083, by rfl⟩ : syracuseStep 320111 = 480167) B480167
theorem B1205279 : Blo 139791 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B386203 : Blo 139791 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B714095 : Blo 139791 714095 := bstep (se 1 (by rfl) ⟨535571, by rfl⟩ : syracuseStep 714095 = 1071143) B1071143
theorem B320975 : Blo 139791 320975 := bstep (se 1 (by rfl) ⟨240731, by rfl⟩ : syracuseStep 320975 = 481463) B481463
theorem B2484125 : Blo 139791 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B256871 : Blo 139791 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B322415 : Blo 139791 322415 := bstep (se 1 (by rfl) ⟨241811, by rfl⟩ : syracuseStep 322415 = 483623) B483623
theorem B290017 : Blo 139791 290017 := bstep (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) B217513
theorem B322937 : Blo 139791 322937 := bstep (se 2 (by rfl) ⟨121101, by rfl⟩ : syracuseStep 322937 = 242203) B242203
theorem B1535507 : Blo 139791 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B159655 : Blo 139791 159655 := bstep (se 1 (by rfl) ⟨119741, by rfl⟩ : syracuseStep 159655 = 239483) B239483
theorem B455375 : Blo 139791 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B914287 : Blo 139791 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B1373231 : Blo 139791 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B817573 : Blo 139791 817573 := bstep (se 4 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 817573 = 153295) B153295
theorem B1833799 : Blo 139791 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B228521 : Blo 139791 228521 := bstep (se 2 (by rfl) ⟨85695, by rfl⟩ : syracuseStep 228521 = 171391) B171391
theorem B654905 : Blo 139791 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B261883 : Blo 139791 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B1311389 : Blo 139791 1311389 := bstep (se 3 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 1311389 = 491771) B491771
theorem B362191 : Blo 139791 362191 := bstep (se 1 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 362191 = 543287) B543287
theorem B690059 : Blo 139791 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B1148843 : Blo 139791 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B9275309 : Blo 139791 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B4655303 : Blo 139791 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B363001 : Blo 139791 363001 := bstep (se 2 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 363001 = 272251) B272251
theorem B5511239 : Blo 139791 5511239 := bstep (se 1 (by rfl) ⟨4133429, by rfl⟩ : syracuseStep 5511239 = 8266859) B8266859
theorem B1513883 : Blo 139791 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B1219049 : Blo 139791 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B171247 : Blo 139791 171247 := bstep (se 1 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 171247 = 256871) B256871
theorem B335123 : Blo 139791 335123 := bstep (se 1 (by rfl) ⟨251342, by rfl⟩ : syracuseStep 335123 = 502685) B502685
theorem B1023671 : Blo 139791 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B401087 : Blo 139791 401087 := bstep (se 1 (by rfl) ⟨300815, by rfl⟩ : syracuseStep 401087 = 601631) B601631
theorem B303583 : Blo 139791 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B1090097 : Blo 139791 1090097 := bstep (se 2 (by rfl) ⟨408786, by rfl⟩ : syracuseStep 1090097 = 817573) B817573
theorem B140519 : Blo 139791 140519 := bstep (se 1 (by rfl) ⟨105389, by rfl⟩ : syracuseStep 140519 = 210779) B210779
theorem B141543 : Blo 139791 141543 := bstep (se 1 (by rfl) ⟨106157, by rfl⟩ : syracuseStep 141543 = 212315) B212315
theorem B436603 : Blo 139791 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B141991 : Blo 139791 141991 := bstep (se 1 (by rfl) ⟨106493, by rfl⟩ : syracuseStep 141991 = 212987) B212987
theorem B142063 : Blo 139791 142063 := bstep (se 1 (by rfl) ⟨106547, by rfl⟩ : syracuseStep 142063 = 213095) B213095
theorem B535511 : Blo 139791 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B1616921 : Blo 139791 1616921 := bstep (se 2 (by rfl) ⟨606345, by rfl⟩ : syracuseStep 1616921 = 1212691) B1212691
theorem B142427 : Blo 139791 142427 := bstep (se 1 (by rfl) ⟨106820, by rfl⟩ : syracuseStep 142427 = 213641) B213641
theorem B143471 : Blo 139791 143471 := bstep (se 1 (by rfl) ⟨107603, by rfl⟩ : syracuseStep 143471 = 215207) B215207
theorem B143611 : Blo 139791 143611 := bstep (se 1 (by rfl) ⟨107708, by rfl⟩ : syracuseStep 143611 = 215417) B215417
theorem B799145 : Blo 139791 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B2405699 : Blo 139791 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B472391 : Blo 139791 472391 := bstep (se 1 (by rfl) ⟨354293, by rfl⟩ : syracuseStep 472391 = 708587) B708587
theorem B210383 : Blo 139791 210383 := bstep (se 1 (by rfl) ⟨157787, by rfl⟩ : syracuseStep 210383 = 315575) B315575
theorem B24032807 : Blo 139791 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B211103 : Blo 139791 211103 := bstep (se 1 (by rfl) ⟨158327, by rfl⟩ : syracuseStep 211103 = 316655) B316655
theorem B212075 : Blo 139791 212075 := bstep (se 1 (by rfl) ⟨159056, by rfl⟩ : syracuseStep 212075 = 318113) B318113
theorem B1621295 : Blo 139791 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B212327 : Blo 139791 212327 := bstep (se 1 (by rfl) ⟨159245, by rfl⟩ : syracuseStep 212327 = 318491) B318491
theorem B212873 : Blo 139791 212873 := bstep (se 2 (by rfl) ⟨79827, by rfl⟩ : syracuseStep 212873 = 159655) B159655
theorem B213311 : Blo 139791 213311 := bstep (se 1 (by rfl) ⟨159983, by rfl⟩ : syracuseStep 213311 = 319967) B319967
theorem B213407 : Blo 139791 213407 := bstep (se 1 (by rfl) ⟨160055, by rfl⟩ : syracuseStep 213407 = 320111) B320111
theorem B3686849 : Blo 139791 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B803519 : Blo 139791 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B476063 : Blo 139791 476063 := bstep (se 1 (by rfl) ⟨357047, by rfl⟩ : syracuseStep 476063 = 714095) B714095
theorem B213983 : Blo 139791 213983 := bstep (se 1 (by rfl) ⟨160487, by rfl⟩ : syracuseStep 213983 = 320975) B320975
theorem B1656083 : Blo 139791 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B214943 : Blo 139791 214943 := bstep (se 1 (by rfl) ⟨161207, by rfl⟩ : syracuseStep 214943 = 322415) B322415
theorem B215291 : Blo 139791 215291 := bstep (se 1 (by rfl) ⟨161468, by rfl⟩ : syracuseStep 215291 = 322937) B322937
theorem B609389 : Blo 139791 609389 := bstep (se 3 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 609389 = 228521) B228521
theorem B2445065 : Blo 139791 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B512183 : Blo 139791 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B1200905 : Blo 139791 1200905 := bstep (se 2 (by rfl) ⟨450339, by rfl⟩ : syracuseStep 1200905 = 900679) B900679
theorem B349177 : Blo 139791 349177 := bstep (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) B261883
theorem B152959 : Blo 139791 152959 := bstep (se 1 (by rfl) ⟨114719, by rfl⟩ : syracuseStep 152959 = 229439) B229439
theorem B873935 : Blo 139791 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B710207 : Blo 139791 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B710369 : Blo 139791 710369 := bstep (se 2 (by rfl) ⟨266388, by rfl⟩ : syracuseStep 710369 = 532777) B532777
theorem B514937 : Blo 139791 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B547931 : Blo 139791 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B3661949 : Blo 139791 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B713447 : Blo 139791 713447 := bstep (se 1 (by rfl) ⟨535085, by rfl⟩ : syracuseStep 713447 = 1070171) B1070171
theorem B13100039 : Blo 139791 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B320543 : Blo 139791 320543 := bstep (se 1 (by rfl) ⟨240407, by rfl⟩ : syracuseStep 320543 = 480815) B480815
theorem B255487 : Blo 139791 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B386689 : Blo 139791 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B157567 : Blo 139791 157567 := bstep (se 1 (by rfl) ⟨118175, by rfl⟩ : syracuseStep 157567 = 236351) B236351
theorem B2648375 : Blo 139791 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B322217 : Blo 139791 322217 := bstep (se 2 (by rfl) ⟨120831, by rfl⟩ : syracuseStep 322217 = 241663) B241663
theorem B355711 : Blo 139791 355711 := bstep (se 1 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 355711 = 533567) B533567
theorem B1470095 : Blo 139791 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B1535867 : Blo 139791 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B159835 : Blo 139791 159835 := bstep (se 1 (by rfl) ⟨119876, by rfl⟩ : syracuseStep 159835 = 239753) B239753
theorem B717821 : Blo 139791 717821 := bstep (se 3 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 717821 = 269183) B269183
theorem B161023 : Blo 139791 161023 := bstep (se 1 (by rfl) ⟨120767, by rfl⟩ : syracuseStep 161023 = 241535) B241535
theorem B357929 : Blo 139791 357929 := bstep (se 2 (by rfl) ⟨134223, by rfl⟩ : syracuseStep 357929 = 268447) B268447
theorem B718793 : Blo 139791 718793 := bstep (se 2 (by rfl) ⟨269547, by rfl⟩ : syracuseStep 718793 = 539095) B539095
theorem B2457899 : Blo 139791 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B9765197 : Blo 139791 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B3674159 : Blo 139791 3674159 := bstep (se 1 (by rfl) ⟨2755619, by rfl⟩ : syracuseStep 3674159 = 5511239) B5511239
theorem B1840157 : Blo 139791 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B267391 : Blo 139791 267391 := bstep (se 1 (by rfl) ⟨200543, by rfl⟩ : syracuseStep 267391 = 401087) B401087
theorem B726731 : Blo 139791 726731 := bstep (se 1 (by rfl) ⟨545048, by rfl⟩ : syracuseStep 726731 = 1090097) B1090097
theorem B465569 : Blo 139791 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B1023911 : Blo 139791 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B532763 : Blo 139791 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B140255 : Blo 139791 140255 := bstep (se 1 (by rfl) ⟨105191, by rfl⟩ : syracuseStep 140255 = 210383) B210383
theorem B238619 : Blo 139791 238619 := bstep (se 1 (by rfl) ⟨178964, by rfl⟩ : syracuseStep 238619 = 357929) B357929
theorem B140735 : Blo 139791 140735 := bstep (se 1 (by rfl) ⟨105551, by rfl⟩ : syracuseStep 140735 = 211103) B211103
theorem B141383 : Blo 139791 141383 := bstep (se 1 (by rfl) ⟨106037, by rfl⟩ : syracuseStep 141383 = 212075) B212075
theorem B141551 : Blo 139791 141551 := bstep (se 1 (by rfl) ⟨106163, by rfl⟩ : syracuseStep 141551 = 212327) B212327
theorem B141915 : Blo 139791 141915 := bstep (se 1 (by rfl) ⟨106436, by rfl⟩ : syracuseStep 141915 = 212873) B212873
theorem B142207 : Blo 139791 142207 := bstep (se 1 (by rfl) ⟨106655, by rfl⟩ : syracuseStep 142207 = 213311) B213311
theorem B142271 : Blo 139791 142271 := bstep (se 1 (by rfl) ⟨106703, by rfl⟩ : syracuseStep 142271 = 213407) B213407
theorem B535679 : Blo 139791 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B404777 : Blo 139791 404777 := bstep (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) B303583
theorem B142655 : Blo 139791 142655 := bstep (se 1 (by rfl) ⟨106991, by rfl⟩ : syracuseStep 142655 = 213983) B213983
theorem B143295 : Blo 139791 143295 := bstep (se 1 (by rfl) ⟨107471, by rfl⟩ : syracuseStep 143295 = 214943) B214943
theorem B765895 : Blo 139791 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B143527 : Blo 139791 143527 := bstep (se 1 (by rfl) ⟨107645, by rfl⟩ : syracuseStep 143527 = 215291) B215291
theorem B340649 : Blo 139791 340649 := bstep (se 2 (by rfl) ⟨127743, by rfl⟩ : syracuseStep 340649 = 255487) B255487
theorem B406259 : Blo 139791 406259 := bstep (se 1 (by rfl) ⟨304694, by rfl⟩ : syracuseStep 406259 = 609389) B609389
theorem B210089 : Blo 139791 210089 := bstep (se 2 (by rfl) ⟨78783, by rfl⟩ : syracuseStep 210089 = 157567) B157567
theorem B341455 : Blo 139791 341455 := bstep (se 1 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 341455 = 512183) B512183
theorem B800603 : Blo 139791 800603 := bstep (se 1 (by rfl) ⟨600452, by rfl⟩ : syracuseStep 800603 = 1200905) B1200905
theorem B473471 : Blo 139791 473471 := bstep (se 1 (by rfl) ⟨355103, by rfl⟩ : syracuseStep 473471 = 710207) B710207
theorem B473579 : Blo 139791 473579 := bstep (se 1 (by rfl) ⟨355184, by rfl⟩ : syracuseStep 473579 = 710369) B710369
theorem B474281 : Blo 139791 474281 := bstep (se 2 (by rfl) ⟨177855, by rfl⟩ : syracuseStep 474281 = 355711) B355711
theorem B343291 : Blo 139791 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B213113 : Blo 139791 213113 := bstep (se 2 (by rfl) ⟨79917, by rfl⟩ : syracuseStep 213113 = 159835) B159835
theorem B475631 : Blo 139791 475631 := bstep (se 1 (by rfl) ⟨356723, by rfl⟩ : syracuseStep 475631 = 713447) B713447
theorem B8733359 : Blo 139791 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B213695 : Blo 139791 213695 := bstep (se 1 (by rfl) ⟨160271, by rfl⟩ : syracuseStep 213695 = 320543) B320543
theorem B214697 : Blo 139791 214697 := bstep (se 2 (by rfl) ⟨80511, by rfl⟩ : syracuseStep 214697 = 161023) B161023
theorem B214811 : Blo 139791 214811 := bstep (se 1 (by rfl) ⟨161108, by rfl⟩ : syracuseStep 214811 = 322217) B322217
theorem B3263125 : Blo 139791 3263125 := bstep (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) B152959
theorem B1461149 : Blo 139791 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B478547 : Blo 139791 478547 := bstep (se 1 (by rfl) ⟨358910, by rfl⟩ : syracuseStep 478547 = 717821) B717821
theorem B314927 : Blo 139791 314927 := bstep (se 1 (by rfl) ⟨236195, by rfl⟩ : syracuseStep 314927 = 472391) B472391
theorem B479195 : Blo 139791 479195 := bstep (se 1 (by rfl) ⟨359396, by rfl⟩ : syracuseStep 479195 = 718793) B718793
theorem B874259 : Blo 139791 874259 := bstep (se 1 (by rfl) ⟨655694, by rfl⟩ : syracuseStep 874259 = 1311389) B1311389
theorem B317375 : Blo 139791 317375 := bstep (se 1 (by rfl) ⟨238031, by rfl⟩ : syracuseStep 317375 = 476063) B476063
theorem B6183539 : Blo 139791 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B3103535 : Blo 139791 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B515585 : Blo 139791 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B482921 : Blo 139791 482921 := bstep (se 2 (by rfl) ⟨181095, by rfl⟩ : syracuseStep 482921 = 362191) B362191
theorem B1630043 : Blo 139791 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B582137 : Blo 139791 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B484001 : Blo 139791 484001 := bstep (se 2 (by rfl) ⟨181500, by rfl⟩ : syracuseStep 484001 = 363001) B363001
theorem B4416221 : Blo 139791 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B582623 : Blo 139791 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B1009255 : Blo 139791 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B812699 : Blo 139791 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B223415 : Blo 139791 223415 := bstep (se 1 (by rfl) ⟨167561, by rfl⟩ : syracuseStep 223415 = 335123) B335123
theorem B682447 : Blo 139791 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B1765583 : Blo 139791 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B357007 : Blo 139791 357007 := bstep (se 1 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 357007 = 535511) B535511
theorem B1077947 : Blo 139791 1077947 := bstep (se 1 (by rfl) ⟨808460, by rfl⟩ : syracuseStep 1077947 = 1616921) B1616921
theorem B980063 : Blo 139791 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B1603799 : Blo 139791 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B16021871 : Blo 139791 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B228329 : Blo 139791 228329 := bstep (se 2 (by rfl) ⟨85623, by rfl⟩ : syracuseStep 228329 = 171247) B171247
theorem B1080863 : Blo 139791 1080863 := bstep (se 1 (by rfl) ⟨810647, by rfl⟩ : syracuseStep 1080863 = 1621295) B1621295
theorem B1638599 : Blo 139791 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B1345673 : Blo 139791 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B2069023 : Blo 139791 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B1086695 : Blo 139791 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B1021193 : Blo 139791 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B270839 : Blo 139791 270839 := bstep (se 1 (by rfl) ⟨203129, by rfl⟩ : syracuseStep 270839 = 406259) B406259
theorem B140059 : Blo 139791 140059 := bstep (se 1 (by rfl) ⟨105044, by rfl⟩ : syracuseStep 140059 = 210089) B210089
theorem B533735 : Blo 139791 533735 := bstep (se 1 (by rfl) ⟨400301, by rfl⟩ : syracuseStep 533735 = 800603) B800603
theorem B142075 : Blo 139791 142075 := bstep (se 1 (by rfl) ⟨106556, by rfl⟩ : syracuseStep 142075 = 213113) B213113
theorem B142463 : Blo 139791 142463 := bstep (se 1 (by rfl) ⟨106847, by rfl⟩ : syracuseStep 142463 = 213695) B213695
theorem B143131 : Blo 139791 143131 := bstep (se 1 (by rfl) ⟨107348, by rfl⟩ : syracuseStep 143131 = 214697) B214697
theorem B143207 : Blo 139791 143207 := bstep (se 1 (by rfl) ⟨107405, by rfl⟩ : syracuseStep 143207 = 214811) B214811
theorem B209951 : Blo 139791 209951 := bstep (se 1 (by rfl) ⟨157463, by rfl⟩ : syracuseStep 209951 = 314927) B314927
theorem B1226771 : Blo 139791 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B211583 : Blo 139791 211583 := bstep (se 1 (by rfl) ⟨158687, by rfl⟩ : syracuseStep 211583 = 317375) B317375
theorem B476009 : Blo 139791 476009 := bstep (se 2 (by rfl) ⟨178503, by rfl⟩ : syracuseStep 476009 = 357007) B357007
theorem B541799 : Blo 139791 541799 := bstep (se 1 (by rfl) ⟨406349, by rfl⟩ : syracuseStep 541799 = 812699) B812699
theorem B148943 : Blo 139791 148943 := bstep (se 1 (by rfl) ⟨111707, by rfl⟩ : syracuseStep 148943 = 223415) B223415
theorem B4966069 : Blo 139791 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B1069199 : Blo 139791 1069199 := bstep (se 1 (by rfl) ⟨801899, by rfl⟩ : syracuseStep 1069199 = 1603799) B1603799
theorem B315647 : Blo 139791 315647 := bstep (se 1 (by rfl) ⟨236735, by rfl⟩ : syracuseStep 315647 = 473471) B473471
theorem B315719 : Blo 139791 315719 := bstep (se 1 (by rfl) ⟨236789, by rfl⟩ : syracuseStep 315719 = 473579) B473579
theorem B152219 : Blo 139791 152219 := bstep (se 1 (by rfl) ⟨114164, by rfl⟩ : syracuseStep 152219 = 228329) B228329
theorem B316187 : Blo 139791 316187 := bstep (se 1 (by rfl) ⟨237140, by rfl⟩ : syracuseStep 316187 = 474281) B474281
theorem B6510131 : Blo 139791 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B317087 : Blo 139791 317087 := bstep (se 1 (by rfl) ⟨237815, by rfl⟩ : syracuseStep 317087 = 475631) B475631
theorem B5822239 : Blo 139791 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B974099 : Blo 139791 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B319031 : Blo 139791 319031 := bstep (se 1 (by rfl) ⟨239273, by rfl⟩ : syracuseStep 319031 = 478547) B478547
theorem B319463 : Blo 139791 319463 := bstep (se 1 (by rfl) ⟨239597, by rfl⟩ : syracuseStep 319463 = 479195) B479195
theorem B2449439 : Blo 139791 2449439 := bstep (se 1 (by rfl) ⟨1837079, by rfl⟩ : syracuseStep 2449439 = 3674159) B3674159
theorem B909929 : Blo 139791 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B4350833 : Blo 139791 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B484487 : Blo 139791 484487 := bstep (se 1 (by rfl) ⟨363365, by rfl⟩ : syracuseStep 484487 = 726731) B726731
theorem B582839 : Blo 139791 582839 := bstep (se 1 (by rfl) ⟨437129, by rfl⟩ : syracuseStep 582839 = 874259) B874259
theorem B4122359 : Blo 139791 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B321947 : Blo 139791 321947 := bstep (se 1 (by rfl) ⟨241460, by rfl⟩ : syracuseStep 321947 = 482921) B482921
theorem B682607 : Blo 139791 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B355175 : Blo 139791 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B388091 : Blo 139791 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B322667 : Blo 139791 322667 := bstep (se 1 (by rfl) ⟨242000, by rfl⟩ : syracuseStep 322667 = 484001) B484001
theorem B2944147 : Blo 139791 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B388415 : Blo 139791 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B159079 : Blo 139791 159079 := bstep (se 1 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 159079 = 238619) B238619
theorem B356521 : Blo 139791 356521 := bstep (se 2 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 356521 = 267391) B267391
theorem B455273 : Blo 139791 455273 := bstep (se 2 (by rfl) ⟨170727, by rfl⟩ : syracuseStep 455273 = 341455) B341455
theorem B357119 : Blo 139791 357119 := bstep (se 1 (by rfl) ⟨267839, by rfl⟩ : syracuseStep 357119 = 535679) B535679
theorem B1177055 : Blo 139791 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B227099 : Blo 139791 227099 := bstep (se 1 (by rfl) ⟨170324, by rfl⟩ : syracuseStep 227099 = 340649) B340649
theorem B718631 : Blo 139791 718631 := bstep (se 1 (by rfl) ⟨538973, by rfl⟩ : syracuseStep 718631 = 1077947) B1077947
theorem B653375 : Blo 139791 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B1079405 : Blo 139791 1079405 := bstep (se 3 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 1079405 = 404777) B404777
theorem B1374893 : Blo 139791 1374893 := bstep (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) B515585
theorem B10681247 : Blo 139791 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B457721 : Blo 139791 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B720575 : Blo 139791 720575 := bstep (se 1 (by rfl) ⟨540431, by rfl⟩ : syracuseStep 720575 = 1080863) B1080863
theorem B361199 : Blo 139791 361199 := bstep (se 1 (by rfl) ⟨270899, by rfl⟩ : syracuseStep 361199 = 541799) B541799
theorem B6621425 : Blo 139791 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B724463 : Blo 139791 724463 := bstep (se 1 (by rfl) ⟨543347, by rfl⟩ : syracuseStep 724463 = 1086695) B1086695
theorem B397181 : Blo 139791 397181 := bstep (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) B148943
theorem B2758697 : Blo 139791 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B236783 : Blo 139791 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B303515 : Blo 139791 303515 := bstep (se 1 (by rfl) ⟨227636, by rfl⟩ : syracuseStep 303515 = 455273) B455273
theorem B238079 : Blo 139791 238079 := bstep (se 1 (by rfl) ⟨178559, by rfl⟩ : syracuseStep 238079 = 357119) B357119
theorem B139967 : Blo 139791 139967 := bstep (se 1 (by rfl) ⟨104975, by rfl⟩ : syracuseStep 139967 = 209951) B209951
theorem B435583 : Blo 139791 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B141055 : Blo 139791 141055 := bstep (se 1 (by rfl) ⟨105791, by rfl⟩ : syracuseStep 141055 = 211583) B211583
theorem B7120831 : Blo 139791 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B305147 : Blo 139791 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B897115 : Blo 139791 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B405917 : Blo 139791 405917 := bstep (se 3 (by rfl) ⟨76109, by rfl⟩ : syracuseStep 405917 = 152219) B152219
theorem B17478389 : Blo 139791 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B210431 : Blo 139791 210431 := bstep (se 1 (by rfl) ⟨157823, by rfl⟩ : syracuseStep 210431 = 315647) B315647
theorem B210479 : Blo 139791 210479 := bstep (se 1 (by rfl) ⟨157859, by rfl⟩ : syracuseStep 210479 = 315719) B315719
theorem B210791 : Blo 139791 210791 := bstep (se 1 (by rfl) ⟨158093, by rfl⟩ : syracuseStep 210791 = 316187) B316187
theorem B4340087 : Blo 139791 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B211391 : Blo 139791 211391 := bstep (se 1 (by rfl) ⟨158543, by rfl⟩ : syracuseStep 211391 = 317087) B317087
theorem B212105 : Blo 139791 212105 := bstep (se 2 (by rfl) ⟨79539, by rfl⟩ : syracuseStep 212105 = 159079) B159079
theorem B212687 : Blo 139791 212687 := bstep (se 1 (by rfl) ⟨159515, by rfl⟩ : syracuseStep 212687 = 319031) B319031
theorem B212975 : Blo 139791 212975 := bstep (se 1 (by rfl) ⟨159731, by rfl⟩ : syracuseStep 212975 = 319463) B319463
theorem B475361 : Blo 139791 475361 := bstep (se 2 (by rfl) ⟨178260, by rfl⟩ : syracuseStep 475361 = 356521) B356521
theorem B180559 : Blo 139791 180559 := bstep (se 1 (by rfl) ⟨135419, by rfl⟩ : syracuseStep 180559 = 270839) B270839
theorem B606619 : Blo 139791 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B2900555 : Blo 139791 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B214631 : Blo 139791 214631 := bstep (se 1 (by rfl) ⟨160973, by rfl⟩ : syracuseStep 214631 = 321947) B321947
theorem B215111 : Blo 139791 215111 := bstep (se 1 (by rfl) ⟨161333, by rfl⟩ : syracuseStep 215111 = 322667) B322667
theorem B1035773 : Blo 139791 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B151399 : Blo 139791 151399 := bstep (se 1 (by rfl) ⟨113549, by rfl⟩ : syracuseStep 151399 = 227099) B227099
theorem B479087 : Blo 139791 479087 := bstep (se 1 (by rfl) ⟨359315, by rfl⟩ : syracuseStep 479087 = 718631) B718631
theorem B480383 : Blo 139791 480383 := bstep (se 1 (by rfl) ⟨360287, by rfl⟩ : syracuseStep 480383 = 720575) B720575
theorem B317339 : Blo 139791 317339 := bstep (se 1 (by rfl) ⟨238004, by rfl⟩ : syracuseStep 317339 = 476009) B476009
theorem B712799 : Blo 139791 712799 := bstep (se 1 (by rfl) ⟨534599, by rfl⟩ : syracuseStep 712799 = 1069199) B1069199
theorem B680795 : Blo 139791 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B3925529 : Blo 139791 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B649399 : Blo 139791 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B1632959 : Blo 139791 1632959 := bstep (se 1 (by rfl) ⟨1224719, by rfl⟩ : syracuseStep 1632959 = 2449439) B2449439
theorem B322991 : Blo 139791 322991 := bstep (se 1 (by rfl) ⟨242243, by rfl⟩ : syracuseStep 322991 = 484487) B484487
theorem B388559 : Blo 139791 388559 := bstep (se 1 (by rfl) ⟨291419, by rfl⟩ : syracuseStep 388559 = 582839) B582839
theorem B355823 : Blo 139791 355823 := bstep (se 1 (by rfl) ⟨266867, by rfl⟩ : syracuseStep 355823 = 533735) B533735
theorem B2748239 : Blo 139791 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B455071 : Blo 139791 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B258727 : Blo 139791 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B7762985 : Blo 139791 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B784703 : Blo 139791 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B817847 : Blo 139791 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B719603 : Blo 139791 719603 := bstep (se 1 (by rfl) ⟨539702, by rfl⟩ : syracuseStep 719603 = 1079405) B1079405
theorem B916595 : Blo 139791 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B1933703 : Blo 139791 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B690515 : Blo 139791 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B1839131 : Blo 139791 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B201865 : Blo 139791 201865 := bstep (se 2 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 201865 = 151399) B151399
theorem B202343 : Blo 139791 202343 := bstep (se 1 (by rfl) ⟨151757, by rfl⟩ : syracuseStep 202343 = 303515) B303515
theorem B1088639 : Blo 139791 1088639 := bstep (se 1 (by rfl) ⟨816479, by rfl⟩ : syracuseStep 1088639 = 1632959) B1632959
theorem B237215 : Blo 139791 237215 := bstep (se 1 (by rfl) ⟨177911, by rfl⟩ : syracuseStep 237215 = 355823) B355823
theorem B270611 : Blo 139791 270611 := bstep (se 1 (by rfl) ⟨202958, by rfl⟩ : syracuseStep 270611 = 405917) B405917
theorem B140287 : Blo 139791 140287 := bstep (se 1 (by rfl) ⟨105215, by rfl⟩ : syracuseStep 140287 = 210431) B210431
theorem B140319 : Blo 139791 140319 := bstep (se 1 (by rfl) ⟨105239, by rfl⟩ : syracuseStep 140319 = 210479) B210479
theorem B140527 : Blo 139791 140527 := bstep (se 1 (by rfl) ⟨105395, by rfl⟩ : syracuseStep 140527 = 210791) B210791
theorem B2893391 : Blo 139791 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B140927 : Blo 139791 140927 := bstep (se 1 (by rfl) ⟨105695, by rfl⟩ : syracuseStep 140927 = 211391) B211391
theorem B141403 : Blo 139791 141403 := bstep (se 1 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 141403 = 212105) B212105
theorem B1059149 : Blo 139791 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B141791 : Blo 139791 141791 := bstep (se 1 (by rfl) ⟨106343, by rfl⟩ : syracuseStep 141791 = 212687) B212687
theorem B141983 : Blo 139791 141983 := bstep (se 1 (by rfl) ⟨106487, by rfl⟩ : syracuseStep 141983 = 212975) B212975
theorem B240745 : Blo 139791 240745 := bstep (se 2 (by rfl) ⟨90279, by rfl⟩ : syracuseStep 240745 = 180559) B180559
theorem B240799 : Blo 139791 240799 := bstep (se 1 (by rfl) ⟨180599, by rfl⟩ : syracuseStep 240799 = 361199) B361199
theorem B143087 : Blo 139791 143087 := bstep (se 1 (by rfl) ⟨107315, by rfl⟩ : syracuseStep 143087 = 214631) B214631
theorem B143407 : Blo 139791 143407 := bstep (se 1 (by rfl) ⟨107555, by rfl⟩ : syracuseStep 143407 = 215111) B215111
theorem B46609037 : Blo 139791 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B865865 : Blo 139791 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B211559 : Blo 139791 211559 := bstep (se 1 (by rfl) ⟨158669, by rfl⟩ : syracuseStep 211559 = 317339) B317339
theorem B475199 : Blo 139791 475199 := bstep (se 1 (by rfl) ⟨356399, by rfl⟩ : syracuseStep 475199 = 712799) B712799
theorem B1196153 : Blo 139791 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B606761 : Blo 139791 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B344969 : Blo 139791 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B215327 : Blo 139791 215327 := bstep (se 1 (by rfl) ⟨161495, by rfl⟩ : syracuseStep 215327 = 322991) B322991
theorem B545231 : Blo 139791 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B479735 : Blo 139791 479735 := bstep (se 1 (by rfl) ⟨359801, by rfl⟩ : syracuseStep 479735 = 719603) B719603
theorem B611063 : Blo 139791 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B316907 : Blo 139791 316907 := bstep (se 1 (by rfl) ⟨237680, by rfl⟩ : syracuseStep 316907 = 475361) B475361
theorem B808825 : Blo 139791 808825 := bstep (se 2 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 808825 = 606619) B606619
theorem B4414283 : Blo 139791 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B482975 : Blo 139791 482975 := bstep (se 1 (by rfl) ⟨362231, by rfl⟩ : syracuseStep 482975 = 724463) B724463
theorem B319391 : Blo 139791 319391 := bstep (se 1 (by rfl) ⟨239543, by rfl⟩ : syracuseStep 319391 = 479087) B479087
theorem B9494441 : Blo 139791 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B320255 : Blo 139791 320255 := bstep (se 1 (by rfl) ⟨240191, by rfl⟩ : syracuseStep 320255 = 480383) B480383
theorem B157855 : Blo 139791 157855 := bstep (se 1 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 157855 = 236783) B236783
theorem B813725 : Blo 139791 813725 := bstep (se 3 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 813725 = 305147) B305147
theorem B158719 : Blo 139791 158719 := bstep (se 1 (by rfl) ⟨119039, by rfl⟩ : syracuseStep 158719 = 238079) B238079
theorem B453863 : Blo 139791 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B2617019 : Blo 139791 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B2323109 : Blo 139791 2323109 := bstep (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) B435583
theorem B259039 : Blo 139791 259039 := bstep (se 1 (by rfl) ⟨194279, by rfl⟩ : syracuseStep 259039 = 388559) B388559
theorem B1832159 : Blo 139791 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B5175323 : Blo 139791 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B523135 : Blo 139791 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B229979 : Blo 139791 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B460343 : Blo 139791 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B363487 : Blo 139791 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B725759 : Blo 139791 725759 := bstep (se 1 (by rfl) ⟨544319, by rfl⟩ : syracuseStep 725759 = 1088639) B1088639
theorem B6329627 : Blo 139791 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B269153 : Blo 139791 269153 := bstep (se 2 (by rfl) ⟨100932, by rfl⟩ : syracuseStep 269153 = 201865) B201865
theorem B1744679 : Blo 139791 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B31072691 : Blo 139791 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B1548739 : Blo 139791 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1221439 : Blo 139791 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B697513 : Blo 139791 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B3450215 : Blo 139791 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B141039 : Blo 139791 141039 := bstep (se 1 (by rfl) ⟨105779, by rfl⟩ : syracuseStep 141039 = 211559) B211559
theorem B797435 : Blo 139791 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B1289135 : Blo 139791 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B404507 : Blo 139791 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B143551 : Blo 139791 143551 := bstep (se 1 (by rfl) ⟨107663, by rfl⟩ : syracuseStep 143551 = 215327) B215327
theorem B1226087 : Blo 139791 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B210473 : Blo 139791 210473 := bstep (se 2 (by rfl) ⟨78927, by rfl⟩ : syracuseStep 210473 = 157855) B157855
theorem B407375 : Blo 139791 407375 := bstep (se 1 (by rfl) ⟨305531, by rfl⟩ : syracuseStep 407375 = 611063) B611063
theorem B211271 : Blo 139791 211271 := bstep (se 1 (by rfl) ⟨158453, by rfl⟩ : syracuseStep 211271 = 316907) B316907
theorem B211625 : Blo 139791 211625 := bstep (se 2 (by rfl) ⟨79359, by rfl⟩ : syracuseStep 211625 = 158719) B158719
theorem B539581 : Blo 139791 539581 := bstep (se 3 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 539581 = 202343) B202343
theorem B212927 : Blo 139791 212927 := bstep (se 1 (by rfl) ⟨159695, by rfl⟩ : syracuseStep 212927 = 319391) B319391
theorem B180407 : Blo 139791 180407 := bstep (se 1 (by rfl) ⟨135305, by rfl⟩ : syracuseStep 180407 = 270611) B270611
theorem B213503 : Blo 139791 213503 := bstep (se 1 (by rfl) ⟨160127, by rfl⟩ : syracuseStep 213503 = 320255) B320255
theorem B345385 : Blo 139791 345385 := bstep (se 2 (by rfl) ⟨129519, by rfl⟩ : syracuseStep 345385 = 259039) B259039
theorem B706099 : Blo 139791 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B542483 : Blo 139791 542483 := bstep (se 1 (by rfl) ⟨406862, by rfl⟩ : syracuseStep 542483 = 813725) B813725
theorem B577243 : Blo 139791 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B316799 : Blo 139791 316799 := bstep (se 1 (by rfl) ⟨237599, by rfl⟩ : syracuseStep 316799 = 475199) B475199
theorem B319823 : Blo 139791 319823 := bstep (se 1 (by rfl) ⟨239867, by rfl⟩ : syracuseStep 319823 = 479735) B479735
theorem B320993 : Blo 139791 320993 := bstep (se 2 (by rfl) ⟨120372, by rfl⟩ : syracuseStep 320993 = 240745) B240745
theorem B321065 : Blo 139791 321065 := bstep (se 2 (by rfl) ⟨120399, by rfl⟩ : syracuseStep 321065 = 240799) B240799
theorem B2942855 : Blo 139791 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B158143 : Blo 139791 158143 := bstep (se 1 (by rfl) ⟨118607, by rfl⟩ : syracuseStep 158143 = 237215) B237215
theorem B321983 : Blo 139791 321983 := bstep (se 1 (by rfl) ⟨241487, by rfl⟩ : syracuseStep 321983 = 482975) B482975
theorem B1928927 : Blo 139791 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B1078433 : Blo 139791 1078433 := bstep (se 2 (by rfl) ⟨404412, by rfl⟩ : syracuseStep 1078433 = 808825) B808825
theorem B1210301 : Blo 139791 1210301 := bstep (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) B453863
theorem B361655 : Blo 139791 361655 := bstep (se 1 (by rfl) ⟨271241, by rfl⟩ : syracuseStep 361655 = 542483) B542483
theorem B460513 : Blo 139791 460513 := bstep (se 2 (by rfl) ⟨172692, by rfl⟩ : syracuseStep 460513 = 345385) B345385
theorem B8259941 : Blo 139791 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B531623 : Blo 139791 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B859423 : Blo 139791 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B269671 : Blo 139791 269671 := bstep (se 1 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 269671 = 404507) B404507
theorem B1285951 : Blo 139791 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B140315 : Blo 139791 140315 := bstep (se 1 (by rfl) ⟨105236, by rfl⟩ : syracuseStep 140315 = 210473) B210473
theorem B271583 : Blo 139791 271583 := bstep (se 1 (by rfl) ⟨203687, by rfl⟩ : syracuseStep 271583 = 407375) B407375
theorem B140847 : Blo 139791 140847 := bstep (se 1 (by rfl) ⟨105635, by rfl⟩ : syracuseStep 140847 = 211271) B211271
theorem B141083 : Blo 139791 141083 := bstep (se 1 (by rfl) ⟨105812, by rfl⟩ : syracuseStep 141083 = 211625) B211625
theorem B141951 : Blo 139791 141951 := bstep (se 1 (by rfl) ⟨106463, by rfl⟩ : syracuseStep 141951 = 212927) B212927
theorem B142335 : Blo 139791 142335 := bstep (se 1 (by rfl) ⟨106751, by rfl⟩ : syracuseStep 142335 = 213503) B213503
theorem B930017 : Blo 139791 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B210857 : Blo 139791 210857 := bstep (se 2 (by rfl) ⟨79071, by rfl⟩ : syracuseStep 210857 = 158143) B158143
theorem B211199 : Blo 139791 211199 := bstep (se 1 (by rfl) ⟨158399, by rfl⟩ : syracuseStep 211199 = 316799) B316799
theorem B1227581 : Blo 139791 1227581 := bstep (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) B460343
theorem B179435 : Blo 139791 179435 := bstep (se 1 (by rfl) ⟨134576, by rfl⟩ : syracuseStep 179435 = 269153) B269153
theorem B769657 : Blo 139791 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B1163119 : Blo 139791 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B213215 : Blo 139791 213215 := bstep (se 1 (by rfl) ⟨159911, by rfl⟩ : syracuseStep 213215 = 319823) B319823
theorem B213995 : Blo 139791 213995 := bstep (se 1 (by rfl) ⟨160496, by rfl⟩ : syracuseStep 213995 = 320993) B320993
theorem B214043 : Blo 139791 214043 := bstep (se 1 (by rfl) ⟨160532, by rfl⟩ : syracuseStep 214043 = 321065) B321065
theorem B214655 : Blo 139791 214655 := bstep (se 1 (by rfl) ⟨160991, by rfl⟩ : syracuseStep 214655 = 321983) B321983
theorem B806867 : Blo 139791 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B481085 : Blo 139791 481085 := bstep (se 3 (by rfl) ⟨90203, by rfl⟩ : syracuseStep 481085 = 180407) B180407
theorem B1628585 : Blo 139791 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B82860509 : Blo 139791 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B613277 : Blo 139791 613277 := bstep (se 3 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 613277 = 229979) B229979
theorem B941465 : Blo 139791 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B483839 : Blo 139791 483839 := bstep (se 1 (by rfl) ⟨362879, by rfl⟩ : syracuseStep 483839 = 725759) B725759
theorem B4219751 : Blo 139791 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B9200573 : Blo 139791 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B484649 : Blo 139791 484649 := bstep (se 2 (by rfl) ⟨181743, by rfl⟩ : syracuseStep 484649 = 363487) B363487
theorem B1961903 : Blo 139791 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B718955 : Blo 139791 718955 := bstep (se 1 (by rfl) ⟨539216, by rfl⟩ : syracuseStep 718955 = 1078433) B1078433
theorem B817391 : Blo 139791 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B719441 : Blo 139791 719441 := bstep (se 2 (by rfl) ⟨269790, by rfl⟩ : syracuseStep 719441 = 539581) B539581
theorem B5506627 : Blo 139791 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B1085723 : Blo 139791 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B627643 : Blo 139791 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B6133715 : Blo 139791 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B39297109 : Blo 139791 39297109 := bstep (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) B460513
theorem B140571 : Blo 139791 140571 := bstep (se 1 (by rfl) ⟨105428, by rfl⟩ : syracuseStep 140571 = 210857) B210857
theorem B140799 : Blo 139791 140799 := bstep (se 1 (by rfl) ⟨105599, by rfl⟩ : syracuseStep 140799 = 211199) B211199
theorem B1026209 : Blo 139791 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B1714601 : Blo 139791 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B1550825 : Blo 139791 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B142143 : Blo 139791 142143 := bstep (se 1 (by rfl) ⟨106607, by rfl⟩ : syracuseStep 142143 = 213215) B213215
theorem B142663 : Blo 139791 142663 := bstep (se 1 (by rfl) ⟨106997, by rfl⟩ : syracuseStep 142663 = 213995) B213995
theorem B142695 : Blo 139791 142695 := bstep (se 1 (by rfl) ⟨107021, by rfl⟩ : syracuseStep 142695 = 214043) B214043
theorem B241103 : Blo 139791 241103 := bstep (se 1 (by rfl) ⟨180827, by rfl⟩ : syracuseStep 241103 = 361655) B361655
theorem B143103 : Blo 139791 143103 := bstep (se 1 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 143103 = 214655) B214655
theorem B537911 : Blo 139791 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B180042709 : Blo 139791 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B408851 : Blo 139791 408851 := bstep (se 1 (by rfl) ⟨306638, by rfl⟩ : syracuseStep 408851 = 613277) B613277
theorem B181055 : Blo 139791 181055 := bstep (se 1 (by rfl) ⟨135791, by rfl⟩ : syracuseStep 181055 = 271583) B271583
theorem B478493 : Blo 139791 478493 := bstep (se 3 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 478493 = 179435) B179435
theorem B479303 : Blo 139791 479303 := bstep (se 1 (by rfl) ⟨359477, by rfl⟩ : syracuseStep 479303 = 718955) B718955
theorem B544927 : Blo 139791 544927 := bstep (se 1 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 544927 = 817391) B817391
theorem B479627 : Blo 139791 479627 := bstep (se 1 (by rfl) ⟨359720, by rfl⟩ : syracuseStep 479627 = 719441) B719441
theorem B320723 : Blo 139791 320723 := bstep (se 1 (by rfl) ⟨240542, by rfl⟩ : syracuseStep 320723 = 481085) B481085
theorem B55240339 : Blo 139791 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B354415 : Blo 139791 354415 := bstep (se 1 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 354415 = 531623) B531623
theorem B322559 : Blo 139791 322559 := bstep (se 1 (by rfl) ⟨241919, by rfl⟩ : syracuseStep 322559 = 483839) B483839
theorem B323099 : Blo 139791 323099 := bstep (se 1 (by rfl) ⟨242324, by rfl⟩ : syracuseStep 323099 = 484649) B484649
theorem B1307935 : Blo 139791 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B620011 : Blo 139791 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B1145897 : Blo 139791 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B359561 : Blo 139791 359561 := bstep (se 2 (by rfl) ⟨134835, by rfl⟩ : syracuseStep 359561 = 269671) B269671
theorem B818387 : Blo 139791 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B52396145 : Blo 139791 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B7342169 : Blo 139791 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B723815 : Blo 139791 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B726569 : Blo 139791 726569 := bstep (se 2 (by rfl) ⟨272463, by rfl⟩ : syracuseStep 726569 = 544927) B544927
theorem B1743913 : Blo 139791 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B826681 : Blo 139791 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B763931 : Blo 139791 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B239707 : Blo 139791 239707 := bstep (se 1 (by rfl) ⟨179780, by rfl⟩ : syracuseStep 239707 = 359561) B359561
theorem B272567 : Blo 139791 272567 := bstep (se 1 (by rfl) ⟨204425, by rfl⟩ : syracuseStep 272567 = 408851) B408851
theorem B472553 : Blo 139791 472553 := bstep (se 2 (by rfl) ⟨177207, by rfl⟩ : syracuseStep 472553 = 354415) B354415
theorem B213815 : Blo 139791 213815 := bstep (se 1 (by rfl) ⟨160361, by rfl⟩ : syracuseStep 213815 = 320723) B320723
theorem B836857 : Blo 139791 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B1033883 : Blo 139791 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B215039 : Blo 139791 215039 := bstep (se 1 (by rfl) ⟨161279, by rfl⟩ : syracuseStep 215039 = 322559) B322559
theorem B215399 : Blo 139791 215399 := bstep (se 1 (by rfl) ⟨161549, by rfl⟩ : syracuseStep 215399 = 323099) B323099
theorem B545591 : Blo 139791 545591 := bstep (se 1 (by rfl) ⟨409193, by rfl⟩ : syracuseStep 545591 = 818387) B818387
theorem B482813 : Blo 139791 482813 := bstep (se 3 (by rfl) ⟨90527, by rfl⟩ : syracuseStep 482813 = 181055) B181055
theorem B318995 : Blo 139791 318995 := bstep (se 1 (by rfl) ⟨239246, by rfl⟩ : syracuseStep 318995 = 478493) B478493
theorem B73653785 : Blo 139791 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B319535 : Blo 139791 319535 := bstep (se 1 (by rfl) ⟨239651, by rfl⟩ : syracuseStep 319535 = 479303) B479303
theorem B319751 : Blo 139791 319751 := bstep (se 1 (by rfl) ⟨239813, by rfl⟩ : syracuseStep 319751 = 479627) B479627
theorem B4089143 : Blo 139791 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B684139 : Blo 139791 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B1143067 : Blo 139791 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B160735 : Blo 139791 160735 := bstep (se 1 (by rfl) ⟨120551, by rfl⟩ : syracuseStep 160735 = 241103) B241103
theorem B358607 : Blo 139791 358607 := bstep (se 1 (by rfl) ⟨268955, by rfl⟩ : syracuseStep 358607 = 537911) B537911
theorem B240056945 : Blo 139791 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B34930763 : Blo 139791 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B689255 : Blo 139791 689255 := bstep (se 1 (by rfl) ⟨516941, by rfl⟩ : syracuseStep 689255 = 1033883) B1033883
theorem B363727 : Blo 139791 363727 := bstep (se 1 (by rfl) ⟨272795, by rfl⟩ : syracuseStep 363727 = 545591) B545591
theorem B2726095 : Blo 139791 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B4463237 : Blo 139791 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B239071 : Blo 139791 239071 := bstep (se 1 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 239071 = 358607) B358607
theorem B142543 : Blo 139791 142543 := bstep (se 1 (by rfl) ⟨106907, by rfl⟩ : syracuseStep 142543 = 213815) B213815
theorem B143359 : Blo 139791 143359 := bstep (se 1 (by rfl) ⟨107519, by rfl⟩ : syracuseStep 143359 = 215039) B215039
theorem B143599 : Blo 139791 143599 := bstep (se 1 (by rfl) ⟨107699, by rfl⟩ : syracuseStep 143599 = 215399) B215399
theorem B212663 : Blo 139791 212663 := bstep (se 1 (by rfl) ⟨159497, by rfl⟩ : syracuseStep 212663 = 318995) B318995
theorem B49102523 : Blo 139791 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B213023 : Blo 139791 213023 := bstep (se 1 (by rfl) ⟨159767, by rfl⟩ : syracuseStep 213023 = 319535) B319535
theorem B213167 : Blo 139791 213167 := bstep (se 1 (by rfl) ⟨159875, by rfl⟩ : syracuseStep 213167 = 319751) B319751
theorem B19579117 : Blo 139791 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B1524089 : Blo 139791 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B214313 : Blo 139791 214313 := bstep (se 2 (by rfl) ⟨80367, by rfl⟩ : syracuseStep 214313 = 160735) B160735
theorem B509287 : Blo 139791 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B181711 : Blo 139791 181711 := bstep (se 1 (by rfl) ⟨136283, by rfl⟩ : syracuseStep 181711 = 272567) B272567
theorem B315035 : Blo 139791 315035 := bstep (se 1 (by rfl) ⟨236276, by rfl⟩ : syracuseStep 315035 = 472553) B472553
theorem B1102241 : Blo 139791 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B482543 : Blo 139791 482543 := bstep (se 1 (by rfl) ⟨361907, by rfl⟩ : syracuseStep 482543 = 723815) B723815
theorem B319609 : Blo 139791 319609 := bstep (se 2 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 319609 = 239707) B239707
theorem B484379 : Blo 139791 484379 := bstep (se 1 (by rfl) ⟨363284, by rfl⟩ : syracuseStep 484379 = 726569) B726569
theorem B321875 : Blo 139791 321875 := bstep (se 1 (by rfl) ⟨241406, by rfl⟩ : syracuseStep 321875 = 482813) B482813
theorem B912185 : Blo 139791 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B2325217 : Blo 139791 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B160037963 : Blo 139791 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B426145 : Blo 139791 426145 := bstep (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) B319609
theorem B1016059 : Blo 139791 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B459503 : Blo 139791 459503 := bstep (se 1 (by rfl) ⟨344627, by rfl⟩ : syracuseStep 459503 = 689255) B689255
theorem B141775 : Blo 139791 141775 := bstep (se 1 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 141775 = 212663) B212663
theorem B142015 : Blo 139791 142015 := bstep (se 1 (by rfl) ⟨106511, by rfl⟩ : syracuseStep 142015 = 213023) B213023
theorem B142111 : Blo 139791 142111 := bstep (se 1 (by rfl) ⟨106583, by rfl⟩ : syracuseStep 142111 = 213167) B213167
theorem B142875 : Blo 139791 142875 := bstep (se 1 (by rfl) ⟨107156, by rfl⟩ : syracuseStep 142875 = 214313) B214313
theorem B242281 : Blo 139791 242281 := bstep (se 2 (by rfl) ⟨90855, by rfl⟩ : syracuseStep 242281 = 181711) B181711
theorem B210023 : Blo 139791 210023 := bstep (se 1 (by rfl) ⟨157517, by rfl⟩ : syracuseStep 210023 = 315035) B315035
theorem B734827 : Blo 139791 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B214583 : Blo 139791 214583 := bstep (se 1 (by rfl) ⟨160937, by rfl⟩ : syracuseStep 214583 = 321875) B321875
theorem B608123 : Blo 139791 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B3100289 : Blo 139791 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B23287175 : Blo 139791 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B26105489 : Blo 139791 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B679049 : Blo 139791 679049 := bstep (se 2 (by rfl) ⟨254643, by rfl⟩ : syracuseStep 679049 = 509287) B509287
theorem B318761 : Blo 139791 318761 := bstep (se 2 (by rfl) ⟨119535, by rfl⟩ : syracuseStep 318761 = 239071) B239071
theorem B484969 : Blo 139791 484969 := bstep (se 2 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 484969 = 363727) B363727
theorem B2975491 : Blo 139791 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B321695 : Blo 139791 321695 := bstep (se 1 (by rfl) ⟨241271, by rfl⟩ : syracuseStep 321695 = 482543) B482543
theorem B322919 : Blo 139791 322919 := bstep (se 1 (by rfl) ⟨242189, by rfl⟩ : syracuseStep 322919 = 484379) B484379
theorem B3634793 : Blo 139791 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B106691975 : Blo 139791 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B32735015 : Blo 139791 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B3967321 : Blo 139791 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B17403659 : Blo 139791 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B140015 : Blo 139791 140015 := bstep (se 1 (by rfl) ⟨105011, by rfl⟩ : syracuseStep 140015 = 210023) B210023
theorem B8267437 : Blo 139791 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B568193 : Blo 139791 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B1354745 : Blo 139791 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B306335 : Blo 139791 306335 := bstep (se 1 (by rfl) ⟨229751, by rfl⟩ : syracuseStep 306335 = 459503) B459503
theorem B143055 : Blo 139791 143055 := bstep (se 1 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 143055 = 214583) B214583
theorem B405415 : Blo 139791 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B212507 : Blo 139791 212507 := bstep (se 1 (by rfl) ⟨159380, by rfl⟩ : syracuseStep 212507 = 318761) B318761
theorem B214463 : Blo 139791 214463 := bstep (se 1 (by rfl) ⟨160847, by rfl⟩ : syracuseStep 214463 = 321695) B321695
theorem B215279 : Blo 139791 215279 := bstep (se 1 (by rfl) ⟨161459, by rfl⟩ : syracuseStep 215279 = 322919) B322919
theorem B71127983 : Blo 139791 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B646625 : Blo 139791 646625 := bstep (se 2 (by rfl) ⟨242484, by rfl⟩ : syracuseStep 646625 = 484969) B484969
theorem B15524783 : Blo 139791 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B452699 : Blo 139791 452699 := bstep (se 1 (by rfl) ⟨339524, by rfl⟩ : syracuseStep 452699 = 679049) B679049
theorem B323041 : Blo 139791 323041 := bstep (se 2 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 323041 = 242281) B242281
theorem B979769 : Blo 139791 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B2423195 : Blo 139791 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B21823343 : Blo 139791 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B11602439 : Blo 139791 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B47418655 : Blo 139791 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B430721 : Blo 139791 430721 := bstep (se 2 (by rfl) ⟨161520, by rfl⟩ : syracuseStep 430721 = 323041) B323041
theorem B431083 : Blo 139791 431083 := bstep (se 1 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 431083 = 646625) B646625
theorem B301799 : Blo 139791 301799 := bstep (se 1 (by rfl) ⟨226349, by rfl⟩ : syracuseStep 301799 = 452699) B452699
theorem B204223 : Blo 139791 204223 := bstep (se 1 (by rfl) ⟨153167, by rfl⟩ : syracuseStep 204223 = 306335) B306335
theorem B1515181 : Blo 139791 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B1615463 : Blo 139791 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B141671 : Blo 139791 141671 := bstep (se 1 (by rfl) ⟨106253, by rfl⟩ : syracuseStep 141671 = 212507) B212507
theorem B142975 : Blo 139791 142975 := bstep (se 1 (by rfl) ⟨107231, by rfl⟩ : syracuseStep 142975 = 214463) B214463
theorem B143519 : Blo 139791 143519 := bstep (se 1 (by rfl) ⟨107639, by rfl⟩ : syracuseStep 143519 = 215279) B215279
theorem B5289761 : Blo 139791 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B540553 : Blo 139791 540553 := bstep (se 2 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 540553 = 405415) B405415
theorem B903163 : Blo 139791 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B44092997 : Blo 139791 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B10349855 : Blo 139791 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B653179 : Blo 139791 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B14548895 : Blo 139791 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B7734959 : Blo 139791 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B29395331 : Blo 139791 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B201199 : Blo 139791 201199 := bstep (se 1 (by rfl) ⟨150899, by rfl⟩ : syracuseStep 201199 = 301799) B301799
theorem B272297 : Blo 139791 272297 := bstep (se 2 (by rfl) ⟨102111, by rfl⟩ : syracuseStep 272297 = 204223) B204223
theorem B63224873 : Blo 139791 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B574777 : Blo 139791 574777 := bstep (se 2 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 574777 = 431083) B431083
theorem B6899903 : Blo 139791 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B870905 : Blo 139791 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B3526507 : Blo 139791 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B2020241 : Blo 139791 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B1204217 : Blo 139791 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B287147 : Blo 139791 287147 := bstep (se 1 (by rfl) ⟨215360, by rfl⟩ : syracuseStep 287147 = 430721) B430721
theorem B1076975 : Blo 139791 1076975 := bstep (se 1 (by rfl) ⟨807731, by rfl⟩ : syracuseStep 1076975 = 1615463) B1615463
theorem B720737 : Blo 139791 720737 := bstep (se 2 (by rfl) ⟨270276, by rfl⟩ : syracuseStep 720737 = 540553) B540553
theorem B9699263 : Blo 139791 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B19596887 : Blo 139791 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B1346827 : Blo 139791 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B268265 : Blo 139791 268265 := bstep (se 2 (by rfl) ⟨100599, by rfl⟩ : syracuseStep 268265 = 201199) B201199
theorem B42149915 : Blo 139791 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B6466175 : Blo 139791 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B5156639 : Blo 139791 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B4599935 : Blo 139791 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B766369 : Blo 139791 766369 := bstep (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) B574777
theorem B4702009 : Blo 139791 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B802811 : Blo 139791 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B181531 : Blo 139791 181531 := bstep (se 1 (by rfl) ⟨136148, by rfl⟩ : syracuseStep 181531 = 272297) B272297
theorem B480491 : Blo 139791 480491 := bstep (se 1 (by rfl) ⟨360368, by rfl⟩ : syracuseStep 480491 = 720737) B720737
theorem B580603 : Blo 139791 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B191431 : Blo 139791 191431 := bstep (se 1 (by rfl) ⟨143573, by rfl⟩ : syracuseStep 191431 = 287147) B287147
theorem B717983 : Blo 139791 717983 := bstep (se 1 (by rfl) ⟨538487, by rfl⟩ : syracuseStep 717983 = 1076975) B1076975
theorem B1021825 : Blo 139791 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B6269345 : Blo 139791 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B535207 : Blo 139791 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B242041 : Blo 139791 242041 := bstep (se 2 (by rfl) ⟨90765, by rfl⟩ : syracuseStep 242041 = 181531) B181531
theorem B178843 : Blo 139791 178843 := bstep (se 1 (by rfl) ⟨134132, by rfl⟩ : syracuseStep 178843 = 268265) B268265
theorem B28099943 : Blo 139791 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B4310783 : Blo 139791 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B3066623 : Blo 139791 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B478655 : Blo 139791 478655 := bstep (se 1 (by rfl) ⟨358991, by rfl⟩ : syracuseStep 478655 = 717983) B717983
theorem B774137 : Blo 139791 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B13064591 : Blo 139791 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B320327 : Blo 139791 320327 := bstep (se 1 (by rfl) ⟨240245, by rfl⟩ : syracuseStep 320327 = 480491) B480491
theorem B255241 : Blo 139791 255241 := bstep (se 2 (by rfl) ⟨95715, by rfl⟩ : syracuseStep 255241 = 191431) B191431
theorem B1795769 : Blo 139791 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B3437759 : Blo 139791 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B238457 : Blo 139791 238457 := bstep (se 2 (by rfl) ⟨89421, by rfl⟩ : syracuseStep 238457 = 178843) B178843
theorem B2044415 : Blo 139791 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B213551 : Blo 139791 213551 := bstep (se 1 (by rfl) ⟨160163, by rfl⟩ : syracuseStep 213551 = 320327) B320327
theorem B1197179 : Blo 139791 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B1361285 : Blo 139791 1361285 := bstep (se 4 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 1361285 = 255241) B255241
theorem B4179563 : Blo 139791 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B1362433 : Blo 139791 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B18733295 : Blo 139791 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B2873855 : Blo 139791 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B319103 : Blo 139791 319103 := bstep (se 1 (by rfl) ⟨239327, by rfl⟩ : syracuseStep 319103 = 478655) B478655
theorem B516091 : Blo 139791 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B9167357 : Blo 139791 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B713609 : Blo 139791 713609 := bstep (se 2 (by rfl) ⟨267603, by rfl⟩ : syracuseStep 713609 = 535207) B535207
theorem B8709727 : Blo 139791 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B322721 : Blo 139791 322721 := bstep (se 2 (by rfl) ⟨121020, by rfl⟩ : syracuseStep 322721 = 242041) B242041
theorem B2786375 : Blo 139791 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B142367 : Blo 139791 142367 := bstep (se 1 (by rfl) ⟨106775, by rfl⟩ : syracuseStep 142367 = 213551) B213551
theorem B798119 : Blo 139791 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B11612969 : Blo 139791 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B1816577 : Blo 139791 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B1915903 : Blo 139791 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B212735 : Blo 139791 212735 := bstep (se 1 (by rfl) ⟨159551, by rfl⟩ : syracuseStep 212735 = 319103) B319103
theorem B6111571 : Blo 139791 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B475739 : Blo 139791 475739 := bstep (se 1 (by rfl) ⟨356804, by rfl⟩ : syracuseStep 475739 = 713609) B713609
theorem B49955453 : Blo 139791 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B215147 : Blo 139791 215147 := bstep (se 1 (by rfl) ⟨161360, by rfl⟩ : syracuseStep 215147 = 322721) B322721
theorem B1362943 : Blo 139791 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B907523 : Blo 139791 907523 := bstep (se 1 (by rfl) ⟨680642, by rfl⟩ : syracuseStep 907523 = 1361285) B1361285
theorem B158971 : Blo 139791 158971 := bstep (se 1 (by rfl) ⟨119228, by rfl⟩ : syracuseStep 158971 = 238457) B238457
theorem B688121 : Blo 139791 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B532079 : Blo 139791 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B7741979 : Blo 139791 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B141823 : Blo 139791 141823 := bstep (se 1 (by rfl) ⟨106367, by rfl⟩ : syracuseStep 141823 = 212735) B212735
theorem B33303635 : Blo 139791 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B143431 : Blo 139791 143431 := bstep (se 1 (by rfl) ⟨107573, by rfl⟩ : syracuseStep 143431 = 215147) B215147
theorem B1817257 : Blo 139791 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B605015 : Blo 139791 605015 := bstep (se 1 (by rfl) ⟨453761, by rfl⟩ : syracuseStep 605015 = 907523) B907523
theorem B211961 : Blo 139791 211961 := bstep (se 2 (by rfl) ⟨79485, by rfl⟩ : syracuseStep 211961 = 158971) B158971
theorem B317159 : Blo 139791 317159 := bstep (se 1 (by rfl) ⟨237869, by rfl⟩ : syracuseStep 317159 = 475739) B475739
theorem B8148761 : Blo 139791 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B1857583 : Blo 139791 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B2554537 : Blo 139791 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B1211051 : Blo 139791 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B458747 : Blo 139791 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B403343 : Blo 139791 403343 := bstep (se 1 (by rfl) ⟨302507, by rfl⟩ : syracuseStep 403343 = 605015) B605015
theorem B141307 : Blo 139791 141307 := bstep (se 1 (by rfl) ⟨105980, by rfl⟩ : syracuseStep 141307 = 211961) B211961
theorem B305831 : Blo 139791 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B211439 : Blo 139791 211439 := bstep (se 1 (by rfl) ⟨158579, by rfl⟩ : syracuseStep 211439 = 317159) B317159
theorem B5161319 : Blo 139791 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B22202423 : Blo 139791 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B2476777 : Blo 139791 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B807367 : Blo 139791 807367 := bstep (se 1 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 807367 = 1211051) B1211051
theorem B5432507 : Blo 139791 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B354719 : Blo 139791 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B2423009 : Blo 139791 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B3406049 : Blo 139791 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B3440879 : Blo 139791 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B268895 : Blo 139791 268895 := bstep (se 1 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 268895 = 403343) B403343
theorem B236479 : Blo 139791 236479 := bstep (se 1 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 236479 = 354719) B354719
theorem B203887 : Blo 139791 203887 := bstep (se 1 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 203887 = 305831) B305831
theorem B1615339 : Blo 139791 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B2270699 : Blo 139791 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B140959 : Blo 139791 140959 := bstep (se 1 (by rfl) ⟨105719, by rfl⟩ : syracuseStep 140959 = 211439) B211439
theorem B3621671 : Blo 139791 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B14801615 : Blo 139791 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B3302369 : Blo 139791 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B1076489 : Blo 139791 1076489 := bstep (se 2 (by rfl) ⟨403683, by rfl⟩ : syracuseStep 1076489 = 807367) B807367
theorem B2293919 : Blo 139791 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B9867743 : Blo 139791 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B2201579 : Blo 139791 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B1513799 : Blo 139791 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B271849 : Blo 139791 271849 := bstep (se 2 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 271849 = 203887) B203887
theorem B179263 : Blo 139791 179263 := bstep (se 1 (by rfl) ⟨134447, by rfl⟩ : syracuseStep 179263 = 268895) B268895
theorem B315305 : Blo 139791 315305 := bstep (se 2 (by rfl) ⟨118239, by rfl⟩ : syracuseStep 315305 = 236479) B236479
theorem B2414447 : Blo 139791 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B2153785 : Blo 139791 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B717659 : Blo 139791 717659 := bstep (se 1 (by rfl) ⟨538244, by rfl⟩ : syracuseStep 717659 = 1076489) B1076489
theorem B362465 : Blo 139791 362465 := bstep (se 2 (by rfl) ⟨135924, by rfl⟩ : syracuseStep 362465 = 271849) B271849
theorem B1609631 : Blo 139791 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B239017 : Blo 139791 239017 := bstep (se 2 (by rfl) ⟨89631, by rfl⟩ : syracuseStep 239017 = 179263) B179263
theorem B210203 : Blo 139791 210203 := bstep (se 1 (by rfl) ⟨157652, by rfl⟩ : syracuseStep 210203 = 315305) B315305
theorem B478439 : Blo 139791 478439 := bstep (se 1 (by rfl) ⟨358829, by rfl⟩ : syracuseStep 478439 = 717659) B717659
theorem B2871713 : Blo 139791 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1529279 : Blo 139791 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B6578495 : Blo 139791 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B1467719 : Blo 139791 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B1009199 : Blo 139791 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B1019519 : Blo 139791 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B140135 : Blo 139791 140135 := bstep (se 1 (by rfl) ⟨105101, by rfl⟩ : syracuseStep 140135 = 210203) B210203
theorem B241643 : Blo 139791 241643 := bstep (se 1 (by rfl) ⟨181232, by rfl⟩ : syracuseStep 241643 = 362465) B362465
theorem B1914475 : Blo 139791 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B672799 : Blo 139791 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B318689 : Blo 139791 318689 := bstep (se 2 (by rfl) ⟨119508, by rfl⟩ : syracuseStep 318689 = 239017) B239017
theorem B318959 : Blo 139791 318959 := bstep (se 1 (by rfl) ⟨239219, by rfl⟩ : syracuseStep 318959 = 478439) B478439
theorem B1073087 : Blo 139791 1073087 := bstep (se 1 (by rfl) ⟨804815, by rfl⟩ : syracuseStep 1073087 = 1609631) B1609631
theorem B4385663 : Blo 139791 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B978479 : Blo 139791 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B2923775 : Blo 139791 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B897065 : Blo 139791 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B212459 : Blo 139791 212459 := bstep (se 1 (by rfl) ⟨159344, by rfl⟩ : syracuseStep 212459 = 318689) B318689
theorem B212639 : Blo 139791 212639 := bstep (se 1 (by rfl) ⟨159479, by rfl⟩ : syracuseStep 212639 = 318959) B318959
theorem B679679 : Blo 139791 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B715391 : Blo 139791 715391 := bstep (se 1 (by rfl) ⟨536543, by rfl⟩ : syracuseStep 715391 = 1073087) B1073087
theorem B2552633 : Blo 139791 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B652319 : Blo 139791 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B161095 : Blo 139791 161095 := bstep (se 1 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 161095 = 241643) B241643
theorem B598043 : Blo 139791 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B434879 : Blo 139791 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B141639 : Blo 139791 141639 := bstep (se 1 (by rfl) ⟨106229, by rfl⟩ : syracuseStep 141639 = 212459) B212459
theorem B141759 : Blo 139791 141759 := bstep (se 1 (by rfl) ⟨106319, by rfl⟩ : syracuseStep 141759 = 212639) B212639
theorem B1949183 : Blo 139791 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B476927 : Blo 139791 476927 := bstep (se 1 (by rfl) ⟨357695, by rfl⟩ : syracuseStep 476927 = 715391) B715391
theorem B214793 : Blo 139791 214793 := bstep (se 2 (by rfl) ⟨80547, by rfl⟩ : syracuseStep 214793 = 161095) B161095
theorem B453119 : Blo 139791 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B1701755 : Blo 139791 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B398695 : Blo 139791 398695 := bstep (se 1 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 398695 = 598043) B598043
theorem B143195 : Blo 139791 143195 := bstep (se 1 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 143195 = 214793) B214793
theorem B1134503 : Blo 139791 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B1299455 : Blo 139791 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B317951 : Blo 139791 317951 := bstep (se 1 (by rfl) ⟨238463, by rfl⟩ : syracuseStep 317951 = 476927) B476927
theorem B289919 : Blo 139791 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B1208317 : Blo 139791 1208317 := bstep (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) B453119
theorem B756335 : Blo 139791 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B1611089 : Blo 139791 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B531593 : Blo 139791 531593 := bstep (se 2 (by rfl) ⟨199347, by rfl⟩ : syracuseStep 531593 = 398695) B398695
theorem B866303 : Blo 139791 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B211967 : Blo 139791 211967 := bstep (se 1 (by rfl) ⟨158975, by rfl⟩ : syracuseStep 211967 = 317951) B317951
theorem B773117 : Blo 139791 773117 := bstep (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) B289919
theorem B141311 : Blo 139791 141311 := bstep (se 1 (by rfl) ⟨105983, by rfl⟩ : syracuseStep 141311 = 211967) B211967
theorem B2016893 : Blo 139791 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B577535 : Blo 139791 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B515411 : Blo 139791 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B1074059 : Blo 139791 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B354395 : Blo 139791 354395 := bstep (se 1 (by rfl) ⟨265796, by rfl⟩ : syracuseStep 354395 = 531593) B531593
theorem B1344595 : Blo 139791 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B236263 : Blo 139791 236263 := bstep (se 1 (by rfl) ⟨177197, by rfl⟩ : syracuseStep 236263 = 354395) B354395
theorem B343607 : Blo 139791 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B716039 : Blo 139791 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B1540093 : Blo 139791 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B477359 : Blo 139791 477359 := bstep (se 1 (by rfl) ⟨358019, by rfl⟩ : syracuseStep 477359 = 716039) B716039
theorem B315017 : Blo 139791 315017 := bstep (se 2 (by rfl) ⟨118131, by rfl⟩ : syracuseStep 315017 = 236263) B236263
theorem B2053457 : Blo 139791 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B1792793 : Blo 139791 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B916285 : Blo 139791 916285 := bstep (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) B343607
theorem B1221713 : Blo 139791 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B210011 : Blo 139791 210011 := bstep (se 1 (by rfl) ⟨157508, by rfl⟩ : syracuseStep 210011 = 315017) B315017
theorem B1195195 : Blo 139791 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B318239 : Blo 139791 318239 := bstep (se 1 (by rfl) ⟨238679, by rfl⟩ : syracuseStep 318239 = 477359) B477359
theorem B1368971 : Blo 139791 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B140007 : Blo 139791 140007 := bstep (se 1 (by rfl) ⟨105005, by rfl⟩ : syracuseStep 140007 = 210011) B210011
theorem B212159 : Blo 139791 212159 := bstep (se 1 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 212159 = 318239) B318239
theorem B1593593 : Blo 139791 1593593 := bstep (se 2 (by rfl) ⟨597597, by rfl⟩ : syracuseStep 1593593 = 1195195) B1195195
theorem B912647 : Blo 139791 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B814475 : Blo 139791 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B141439 : Blo 139791 141439 := bstep (se 1 (by rfl) ⟨106079, by rfl⟩ : syracuseStep 141439 = 212159) B212159
theorem B1062395 : Blo 139791 1062395 := bstep (se 1 (by rfl) ⟨796796, by rfl⟩ : syracuseStep 1062395 = 1593593) B1593593
theorem B608431 : Blo 139791 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B542983 : Blo 139791 542983 := bstep (se 1 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 542983 = 814475) B814475
theorem B723977 : Blo 139791 723977 := bstep (se 2 (by rfl) ⟨271491, by rfl⟩ : syracuseStep 723977 = 542983) B542983
theorem B708263 : Blo 139791 708263 := bstep (se 1 (by rfl) ⟨531197, by rfl⟩ : syracuseStep 708263 = 1062395) B1062395
theorem B811241 : Blo 139791 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B472175 : Blo 139791 472175 := bstep (se 1 (by rfl) ⟨354131, by rfl⟩ : syracuseStep 472175 = 708263) B708263
theorem B540827 : Blo 139791 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B482651 : Blo 139791 482651 := bstep (se 1 (by rfl) ⟨361988, by rfl⟩ : syracuseStep 482651 = 723977) B723977
theorem B360551 : Blo 139791 360551 := bstep (se 1 (by rfl) ⟨270413, by rfl⟩ : syracuseStep 360551 = 540827) B540827
theorem B314783 : Blo 139791 314783 := bstep (se 1 (by rfl) ⟨236087, by rfl⟩ : syracuseStep 314783 = 472175) B472175
theorem B321767 : Blo 139791 321767 := bstep (se 1 (by rfl) ⟨241325, by rfl⟩ : syracuseStep 321767 = 482651) B482651
theorem B240367 : Blo 139791 240367 := bstep (se 1 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 240367 = 360551) B360551
theorem B209855 : Blo 139791 209855 := bstep (se 1 (by rfl) ⟨157391, by rfl⟩ : syracuseStep 209855 = 314783) B314783
theorem B214511 : Blo 139791 214511 := bstep (se 1 (by rfl) ⟨160883, by rfl⟩ : syracuseStep 214511 = 321767) B321767
theorem B139903 : Blo 139791 139903 := bstep (se 1 (by rfl) ⟨104927, by rfl⟩ : syracuseStep 139903 = 209855) B209855
theorem B143007 : Blo 139791 143007 := bstep (se 1 (by rfl) ⟨107255, by rfl⟩ : syracuseStep 143007 = 214511) B214511
theorem B320489 : Blo 139791 320489 := bstep (se 2 (by rfl) ⟨120183, by rfl⟩ : syracuseStep 320489 = 240367) B240367
theorem B213659 : Blo 139791 213659 := bstep (se 1 (by rfl) ⟨160244, by rfl⟩ : syracuseStep 213659 = 320489) B320489
theorem B142439 : Blo 139791 142439 := bstep (se 1 (by rfl) ⟨106829, by rfl⟩ : syracuseStep 142439 = 213659) B213659

theorem C0 (j : ℕ) (h1 : 34947 ≤ j) (h2 : j ≤ 35646) : Blo 139791 (4 * j + 3) := by
  interval_cases j
  · exact B139791
  · exact B139795
  · exact B139799
  · exact B139803
  · exact B139807
  · exact B139811
  · exact B139815
  · exact B139819
  · exact B139823
  · exact B139827
  · exact B139831
  · exact B139835
  · exact B139839
  · exact B139843
  · exact B139847
  · exact B139851
  · exact B139855
  · exact B139859
  · exact B139863
  · exact B139867
  · exact B139871
  · exact B139875
  · exact B139879
  · exact B139883
  · exact B139887
  · exact B139891
  · exact B139895
  · exact B139899
  · exact B139903
  · exact B139907
  · exact B139911
  · exact B139915
  · exact B139919
  · exact B139923
  · exact B139927
  · exact B139931
  · exact B139935
  · exact B139939
  · exact B139943
  · exact B139947
  · exact B139951
  · exact B139955
  · exact B139959
  · exact B139963
  · exact B139967
  · exact B139971
  · exact B139975
  · exact B139979
  · exact B139983
  · exact B139987
  · exact B139991
  · exact B139995
  · exact B139999
  · exact B140003
  · exact B140007
  · exact B140011
  · exact B140015
  · exact B140019
  · exact B140023
  · exact B140027
  · exact B140031
  · exact B140035
  · exact B140039
  · exact B140043
  · exact B140047
  · exact B140051
  · exact B140055
  · exact B140059
  · exact B140063
  · exact B140067
  · exact B140071
  · exact B140075
  · exact B140079
  · exact B140083
  · exact B140087
  · exact B140091
  · exact B140095
  · exact B140099
  · exact B140103
  · exact B140107
  · exact B140111
  · exact B140115
  · exact B140119
  · exact B140123
  · exact B140127
  · exact B140131
  · exact B140135
  · exact B140139
  · exact B140143
  · exact B140147
  · exact B140151
  · exact B140155
  · exact B140159
  · exact B140163
  · exact B140167
  · exact B140171
  · exact B140175
  · exact B140179
  · exact B140183
  · exact B140187
  · exact B140191
  · exact B140195
  · exact B140199
  · exact B140203
  · exact B140207
  · exact B140211
  · exact B140215
  · exact B140219
  · exact B140223
  · exact B140227
  · exact B140231
  · exact B140235
  · exact B140239
  · exact B140243
  · exact B140247
  · exact B140251
  · exact B140255
  · exact B140259
  · exact B140263
  · exact B140267
  · exact B140271
  · exact B140275
  · exact B140279
  · exact B140283
  · exact B140287
  · exact B140291
  · exact B140295
  · exact B140299
  · exact B140303
  · exact B140307
  · exact B140311
  · exact B140315
  · exact B140319
  · exact B140323
  · exact B140327
  · exact B140331
  · exact B140335
  · exact B140339
  · exact B140343
  · exact B140347
  · exact B140351
  · exact B140355
  · exact B140359
  · exact B140363
  · exact B140367
  · exact B140371
  · exact B140375
  · exact B140379
  · exact B140383
  · exact B140387
  · exact B140391
  · exact B140395
  · exact B140399
  · exact B140403
  · exact B140407
  · exact B140411
  · exact B140415
  · exact B140419
  · exact B140423
  · exact B140427
  · exact B140431
  · exact B140435
  · exact B140439
  · exact B140443
  · exact B140447
  · exact B140451
  · exact B140455
  · exact B140459
  · exact B140463
  · exact B140467
  · exact B140471
  · exact B140475
  · exact B140479
  · exact B140483
  · exact B140487
  · exact B140491
  · exact B140495
  · exact B140499
  · exact B140503
  · exact B140507
  · exact B140511
  · exact B140515
  · exact B140519
  · exact B140523
  · exact B140527
  · exact B140531
  · exact B140535
  · exact B140539
  · exact B140543
  · exact B140547
  · exact B140551
  · exact B140555
  · exact B140559
  · exact B140563
  · exact B140567
  · exact B140571
  · exact B140575
  · exact B140579
  · exact B140583
  · exact B140587
  · exact B140591
  · exact B140595
  · exact B140599
  · exact B140603
  · exact B140607
  · exact B140611
  · exact B140615
  · exact B140619
  · exact B140623
  · exact B140627
  · exact B140631
  · exact B140635
  · exact B140639
  · exact B140643
  · exact B140647
  · exact B140651
  · exact B140655
  · exact B140659
  · exact B140663
  · exact B140667
  · exact B140671
  · exact B140675
  · exact B140679
  · exact B140683
  · exact B140687
  · exact B140691
  · exact B140695
  · exact B140699
  · exact B140703
  · exact B140707
  · exact B140711
  · exact B140715
  · exact B140719
  · exact B140723
  · exact B140727
  · exact B140731
  · exact B140735
  · exact B140739
  · exact B140743
  · exact B140747
  · exact B140751
  · exact B140755
  · exact B140759
  · exact B140763
  · exact B140767
  · exact B140771
  · exact B140775
  · exact B140779
  · exact B140783
  · exact B140787
  · exact B140791
  · exact B140795
  · exact B140799
  · exact B140803
  · exact B140807
  · exact B140811
  · exact B140815
  · exact B140819
  · exact B140823
  · exact B140827
  · exact B140831
  · exact B140835
  · exact B140839
  · exact B140843
  · exact B140847
  · exact B140851
  · exact B140855
  · exact B140859
  · exact B140863
  · exact B140867
  · exact B140871
  · exact B140875
  · exact B140879
  · exact B140883
  · exact B140887
  · exact B140891
  · exact B140895
  · exact B140899
  · exact B140903
  · exact B140907
  · exact B140911
  · exact B140915
  · exact B140919
  · exact B140923
  · exact B140927
  · exact B140931
  · exact B140935
  · exact B140939
  · exact B140943
  · exact B140947
  · exact B140951
  · exact B140955
  · exact B140959
  · exact B140963
  · exact B140967
  · exact B140971
  · exact B140975
  · exact B140979
  · exact B140983
  · exact B140987
  · exact B140991
  · exact B140995
  · exact B140999
  · exact B141003
  · exact B141007
  · exact B141011
  · exact B141015
  · exact B141019
  · exact B141023
  · exact B141027
  · exact B141031
  · exact B141035
  · exact B141039
  · exact B141043
  · exact B141047
  · exact B141051
  · exact B141055
  · exact B141059
  · exact B141063
  · exact B141067
  · exact B141071
  · exact B141075
  · exact B141079
  · exact B141083
  · exact B141087
  · exact B141091
  · exact B141095
  · exact B141099
  · exact B141103
  · exact B141107
  · exact B141111
  · exact B141115
  · exact B141119
  · exact B141123
  · exact B141127
  · exact B141131
  · exact B141135
  · exact B141139
  · exact B141143
  · exact B141147
  · exact B141151
  · exact B141155
  · exact B141159
  · exact B141163
  · exact B141167
  · exact B141171
  · exact B141175
  · exact B141179
  · exact B141183
  · exact B141187
  · exact B141191
  · exact B141195
  · exact B141199
  · exact B141203
  · exact B141207
  · exact B141211
  · exact B141215
  · exact B141219
  · exact B141223
  · exact B141227
  · exact B141231
  · exact B141235
  · exact B141239
  · exact B141243
  · exact B141247
  · exact B141251
  · exact B141255
  · exact B141259
  · exact B141263
  · exact B141267
  · exact B141271
  · exact B141275
  · exact B141279
  · exact B141283
  · exact B141287
  · exact B141291
  · exact B141295
  · exact B141299
  · exact B141303
  · exact B141307
  · exact B141311
  · exact B141315
  · exact B141319
  · exact B141323
  · exact B141327
  · exact B141331
  · exact B141335
  · exact B141339
  · exact B141343
  · exact B141347
  · exact B141351
  · exact B141355
  · exact B141359
  · exact B141363
  · exact B141367
  · exact B141371
  · exact B141375
  · exact B141379
  · exact B141383
  · exact B141387
  · exact B141391
  · exact B141395
  · exact B141399
  · exact B141403
  · exact B141407
  · exact B141411
  · exact B141415
  · exact B141419
  · exact B141423
  · exact B141427
  · exact B141431
  · exact B141435
  · exact B141439
  · exact B141443
  · exact B141447
  · exact B141451
  · exact B141455
  · exact B141459
  · exact B141463
  · exact B141467
  · exact B141471
  · exact B141475
  · exact B141479
  · exact B141483
  · exact B141487
  · exact B141491
  · exact B141495
  · exact B141499
  · exact B141503
  · exact B141507
  · exact B141511
  · exact B141515
  · exact B141519
  · exact B141523
  · exact B141527
  · exact B141531
  · exact B141535
  · exact B141539
  · exact B141543
  · exact B141547
  · exact B141551
  · exact B141555
  · exact B141559
  · exact B141563
  · exact B141567
  · exact B141571
  · exact B141575
  · exact B141579
  · exact B141583
  · exact B141587
  · exact B141591
  · exact B141595
  · exact B141599
  · exact B141603
  · exact B141607
  · exact B141611
  · exact B141615
  · exact B141619
  · exact B141623
  · exact B141627
  · exact B141631
  · exact B141635
  · exact B141639
  · exact B141643
  · exact B141647
  · exact B141651
  · exact B141655
  · exact B141659
  · exact B141663
  · exact B141667
  · exact B141671
  · exact B141675
  · exact B141679
  · exact B141683
  · exact B141687
  · exact B141691
  · exact B141695
  · exact B141699
  · exact B141703
  · exact B141707
  · exact B141711
  · exact B141715
  · exact B141719
  · exact B141723
  · exact B141727
  · exact B141731
  · exact B141735
  · exact B141739
  · exact B141743
  · exact B141747
  · exact B141751
  · exact B141755
  · exact B141759
  · exact B141763
  · exact B141767
  · exact B141771
  · exact B141775
  · exact B141779
  · exact B141783
  · exact B141787
  · exact B141791
  · exact B141795
  · exact B141799
  · exact B141803
  · exact B141807
  · exact B141811
  · exact B141815
  · exact B141819
  · exact B141823
  · exact B141827
  · exact B141831
  · exact B141835
  · exact B141839
  · exact B141843
  · exact B141847
  · exact B141851
  · exact B141855
  · exact B141859
  · exact B141863
  · exact B141867
  · exact B141871
  · exact B141875
  · exact B141879
  · exact B141883
  · exact B141887
  · exact B141891
  · exact B141895
  · exact B141899
  · exact B141903
  · exact B141907
  · exact B141911
  · exact B141915
  · exact B141919
  · exact B141923
  · exact B141927
  · exact B141931
  · exact B141935
  · exact B141939
  · exact B141943
  · exact B141947
  · exact B141951
  · exact B141955
  · exact B141959
  · exact B141963
  · exact B141967
  · exact B141971
  · exact B141975
  · exact B141979
  · exact B141983
  · exact B141987
  · exact B141991
  · exact B141995
  · exact B141999
  · exact B142003
  · exact B142007
  · exact B142011
  · exact B142015
  · exact B142019
  · exact B142023
  · exact B142027
  · exact B142031
  · exact B142035
  · exact B142039
  · exact B142043
  · exact B142047
  · exact B142051
  · exact B142055
  · exact B142059
  · exact B142063
  · exact B142067
  · exact B142071
  · exact B142075
  · exact B142079
  · exact B142083
  · exact B142087
  · exact B142091
  · exact B142095
  · exact B142099
  · exact B142103
  · exact B142107
  · exact B142111
  · exact B142115
  · exact B142119
  · exact B142123
  · exact B142127
  · exact B142131
  · exact B142135
  · exact B142139
  · exact B142143
  · exact B142147
  · exact B142151
  · exact B142155
  · exact B142159
  · exact B142163
  · exact B142167
  · exact B142171
  · exact B142175
  · exact B142179
  · exact B142183
  · exact B142187
  · exact B142191
  · exact B142195
  · exact B142199
  · exact B142203
  · exact B142207
  · exact B142211
  · exact B142215
  · exact B142219
  · exact B142223
  · exact B142227
  · exact B142231
  · exact B142235
  · exact B142239
  · exact B142243
  · exact B142247
  · exact B142251
  · exact B142255
  · exact B142259
  · exact B142263
  · exact B142267
  · exact B142271
  · exact B142275
  · exact B142279
  · exact B142283
  · exact B142287
  · exact B142291
  · exact B142295
  · exact B142299
  · exact B142303
  · exact B142307
  · exact B142311
  · exact B142315
  · exact B142319
  · exact B142323
  · exact B142327
  · exact B142331
  · exact B142335
  · exact B142339
  · exact B142343
  · exact B142347
  · exact B142351
  · exact B142355
  · exact B142359
  · exact B142363
  · exact B142367
  · exact B142371
  · exact B142375
  · exact B142379
  · exact B142383
  · exact B142387
  · exact B142391
  · exact B142395
  · exact B142399
  · exact B142403
  · exact B142407
  · exact B142411
  · exact B142415
  · exact B142419
  · exact B142423
  · exact B142427
  · exact B142431
  · exact B142435
  · exact B142439
  · exact B142443
  · exact B142447
  · exact B142451
  · exact B142455
  · exact B142459
  · exact B142463
  · exact B142467
  · exact B142471
  · exact B142475
  · exact B142479
  · exact B142483
  · exact B142487
  · exact B142491
  · exact B142495
  · exact B142499
  · exact B142503
  · exact B142507
  · exact B142511
  · exact B142515
  · exact B142519
  · exact B142523
  · exact B142527
  · exact B142531
  · exact B142535
  · exact B142539
  · exact B142543
  · exact B142547
  · exact B142551
  · exact B142555
  · exact B142559
  · exact B142563
  · exact B142567
  · exact B142571
  · exact B142575
  · exact B142579
  · exact B142583
  · exact B142587

theorem C1 (j : ℕ) (h1 : 35647 ≤ j) (h2 : j ≤ 35947) : Blo 139791 (4 * j + 3) := by
  interval_cases j
  · exact B142591
  · exact B142595
  · exact B142599
  · exact B142603
  · exact B142607
  · exact B142611
  · exact B142615
  · exact B142619
  · exact B142623
  · exact B142627
  · exact B142631
  · exact B142635
  · exact B142639
  · exact B142643
  · exact B142647
  · exact B142651
  · exact B142655
  · exact B142659
  · exact B142663
  · exact B142667
  · exact B142671
  · exact B142675
  · exact B142679
  · exact B142683
  · exact B142687
  · exact B142691
  · exact B142695
  · exact B142699
  · exact B142703
  · exact B142707
  · exact B142711
  · exact B142715
  · exact B142719
  · exact B142723
  · exact B142727
  · exact B142731
  · exact B142735
  · exact B142739
  · exact B142743
  · exact B142747
  · exact B142751
  · exact B142755
  · exact B142759
  · exact B142763
  · exact B142767
  · exact B142771
  · exact B142775
  · exact B142779
  · exact B142783
  · exact B142787
  · exact B142791
  · exact B142795
  · exact B142799
  · exact B142803
  · exact B142807
  · exact B142811
  · exact B142815
  · exact B142819
  · exact B142823
  · exact B142827
  · exact B142831
  · exact B142835
  · exact B142839
  · exact B142843
  · exact B142847
  · exact B142851
  · exact B142855
  · exact B142859
  · exact B142863
  · exact B142867
  · exact B142871
  · exact B142875
  · exact B142879
  · exact B142883
  · exact B142887
  · exact B142891
  · exact B142895
  · exact B142899
  · exact B142903
  · exact B142907
  · exact B142911
  · exact B142915
  · exact B142919
  · exact B142923
  · exact B142927
  · exact B142931
  · exact B142935
  · exact B142939
  · exact B142943
  · exact B142947
  · exact B142951
  · exact B142955
  · exact B142959
  · exact B142963
  · exact B142967
  · exact B142971
  · exact B142975
  · exact B142979
  · exact B142983
  · exact B142987
  · exact B142991
  · exact B142995
  · exact B142999
  · exact B143003
  · exact B143007
  · exact B143011
  · exact B143015
  · exact B143019
  · exact B143023
  · exact B143027
  · exact B143031
  · exact B143035
  · exact B143039
  · exact B143043
  · exact B143047
  · exact B143051
  · exact B143055
  · exact B143059
  · exact B143063
  · exact B143067
  · exact B143071
  · exact B143075
  · exact B143079
  · exact B143083
  · exact B143087
  · exact B143091
  · exact B143095
  · exact B143099
  · exact B143103
  · exact B143107
  · exact B143111
  · exact B143115
  · exact B143119
  · exact B143123
  · exact B143127
  · exact B143131
  · exact B143135
  · exact B143139
  · exact B143143
  · exact B143147
  · exact B143151
  · exact B143155
  · exact B143159
  · exact B143163
  · exact B143167
  · exact B143171
  · exact B143175
  · exact B143179
  · exact B143183
  · exact B143187
  · exact B143191
  · exact B143195
  · exact B143199
  · exact B143203
  · exact B143207
  · exact B143211
  · exact B143215
  · exact B143219
  · exact B143223
  · exact B143227
  · exact B143231
  · exact B143235
  · exact B143239
  · exact B143243
  · exact B143247
  · exact B143251
  · exact B143255
  · exact B143259
  · exact B143263
  · exact B143267
  · exact B143271
  · exact B143275
  · exact B143279
  · exact B143283
  · exact B143287
  · exact B143291
  · exact B143295
  · exact B143299
  · exact B143303
  · exact B143307
  · exact B143311
  · exact B143315
  · exact B143319
  · exact B143323
  · exact B143327
  · exact B143331
  · exact B143335
  · exact B143339
  · exact B143343
  · exact B143347
  · exact B143351
  · exact B143355
  · exact B143359
  · exact B143363
  · exact B143367
  · exact B143371
  · exact B143375
  · exact B143379
  · exact B143383
  · exact B143387
  · exact B143391
  · exact B143395
  · exact B143399
  · exact B143403
  · exact B143407
  · exact B143411
  · exact B143415
  · exact B143419
  · exact B143423
  · exact B143427
  · exact B143431
  · exact B143435
  · exact B143439
  · exact B143443
  · exact B143447
  · exact B143451
  · exact B143455
  · exact B143459
  · exact B143463
  · exact B143467
  · exact B143471
  · exact B143475
  · exact B143479
  · exact B143483
  · exact B143487
  · exact B143491
  · exact B143495
  · exact B143499
  · exact B143503
  · exact B143507
  · exact B143511
  · exact B143515
  · exact B143519
  · exact B143523
  · exact B143527
  · exact B143531
  · exact B143535
  · exact B143539
  · exact B143543
  · exact B143547
  · exact B143551
  · exact B143555
  · exact B143559
  · exact B143563
  · exact B143567
  · exact B143571
  · exact B143575
  · exact B143579
  · exact B143583
  · exact B143587
  · exact B143591
  · exact B143595
  · exact B143599
  · exact B143603
  · exact B143607
  · exact B143611
  · exact B143615
  · exact B143619
  · exact B143623
  · exact B143627
  · exact B143631
  · exact B143635
  · exact B143639
  · exact B143643
  · exact B143647
  · exact B143651
  · exact B143655
  · exact B143659
  · exact B143663
  · exact B143667
  · exact B143671
  · exact B143675
  · exact B143679
  · exact B143683
  · exact B143687
  · exact B143691
  · exact B143695
  · exact B143699
  · exact B143703
  · exact B143707
  · exact B143711
  · exact B143715
  · exact B143719
  · exact B143723
  · exact B143727
  · exact B143731
  · exact B143735
  · exact B143739
  · exact B143743
  · exact B143747
  · exact B143751
  · exact B143755
  · exact B143759
  · exact B143763
  · exact B143767
  · exact B143771
  · exact B143775
  · exact B143779
  · exact B143783
  · exact B143787
  · exact B143791

theorem solution (m : ℕ) (hlo : 139791 ≤ m) (hhi : m ≤ 143791) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 34947 ≤ j := by omega
    have hj2 : j ≤ 35947 := by omega
    have hb : Blo 139791 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 35647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
