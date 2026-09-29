-- Prove2me | solution 1 for syracuse_descends_range_1327482_1328982
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:38.500674+00:00
-- url     : https://prove2.me/submissions/a0bf8a73-3cfc-44ae-9ef7-e1a33d6d2d5e

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


theorem B2990141 : Blo 1327482 2990141 := bbase (se 3 (by rfl) ⟨560651, by rfl⟩ : syracuseStep 2990141 = 1121303) (by norm_num)
theorem B2392229 : Blo 1327482 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B4481189 : Blo 1327482 4481189 := bbase (se 4 (by rfl) ⟨420111, by rfl⟩ : syracuseStep 4481189 = 840223) (by norm_num)
theorem B6472021 : Blo 1327482 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B8511925 : Blo 1327482 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B1794517 : Blo 1327482 1794517 := bbase (se 7 (by rfl) ⟨21029, by rfl⟩ : syracuseStep 1794517 = 42059) (by norm_num)
theorem B1417753 : Blo 1327482 1417753 := bbase (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) (by norm_num)
theorem B1417757 : Blo 1327482 1417757 := bbase (se 3 (by rfl) ⟨265829, by rfl⟩ : syracuseStep 1417757 = 531659) (by norm_num)
theorem B3408421 : Blo 1327482 3408421 := bbase (se 4 (by rfl) ⟨319539, by rfl⟩ : syracuseStep 3408421 = 639079) (by norm_num)
theorem B7561781 : Blo 1327482 7561781 := bbase (se 5 (by rfl) ⟨354458, by rfl⟩ : syracuseStep 7561781 = 708917) (by norm_num)
theorem B1991237 : Blo 1327482 1991237 := bbase (se 4 (by rfl) ⟨186678, by rfl⟩ : syracuseStep 1991237 = 373357) (by norm_num)
theorem B4481621 : Blo 1327482 4481621 := bbase (se 8 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 4481621 = 52519) (by norm_num)
theorem B1991261 : Blo 1327482 1991261 := bbase (se 3 (by rfl) ⟨373361, by rfl⟩ : syracuseStep 1991261 = 746723) (by norm_num)
theorem B1991285 : Blo 1327482 1991285 := bbase (se 5 (by rfl) ⟨93341, by rfl⟩ : syracuseStep 1991285 = 186683) (by norm_num)
theorem B1991309 : Blo 1327482 1991309 := bbase (se 3 (by rfl) ⟨373370, by rfl⟩ : syracuseStep 1991309 = 746741) (by norm_num)
theorem B20439701 : Blo 1327482 20439701 := bbase (se 6 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 20439701 = 958111) (by norm_num)
theorem B1991333 : Blo 1327482 1991333 := bbase (se 4 (by rfl) ⟨186687, by rfl⟩ : syracuseStep 1991333 = 373375) (by norm_num)
theorem B1991357 : Blo 1327482 1991357 := bbase (se 3 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 1991357 = 746759) (by norm_num)
theorem B1991381 : Blo 1327482 1991381 := bbase (se 7 (by rfl) ⟨23336, by rfl⟩ : syracuseStep 1991381 = 46673) (by norm_num)
theorem B1680097 : Blo 1327482 1680097 := bbase (se 2 (by rfl) ⟨630036, by rfl⟩ : syracuseStep 1680097 = 1260073) (by norm_num)
theorem B1991405 : Blo 1327482 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B1991429 : Blo 1327482 1991429 := bbase (se 4 (by rfl) ⟨186696, by rfl⟩ : syracuseStep 1991429 = 373393) (by norm_num)
theorem B1991453 : Blo 1327482 1991453 := bbase (se 3 (by rfl) ⟨373397, by rfl⟩ : syracuseStep 1991453 = 746795) (by norm_num)
theorem B1991477 : Blo 1327482 1991477 := bbase (se 5 (by rfl) ⟨93350, by rfl⟩ : syracuseStep 1991477 = 186701) (by norm_num)
theorem B1680193 : Blo 1327482 1680193 := bbase (se 2 (by rfl) ⟨630072, by rfl⟩ : syracuseStep 1680193 = 1260145) (by norm_num)
theorem B1991501 : Blo 1327482 1991501 := bbase (se 3 (by rfl) ⟨373406, by rfl⟩ : syracuseStep 1991501 = 746813) (by norm_num)
theorem B1991525 : Blo 1327482 1991525 := bbase (se 4 (by rfl) ⟨186705, by rfl⟩ : syracuseStep 1991525 = 373411) (by norm_num)
theorem B1991549 : Blo 1327482 1991549 := bbase (se 3 (by rfl) ⟨373415, by rfl⟩ : syracuseStep 1991549 = 746831) (by norm_num)
theorem B1991573 : Blo 1327482 1991573 := bbase (se 6 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 1991573 = 93355) (by norm_num)
theorem B1991597 : Blo 1327482 1991597 := bbase (se 3 (by rfl) ⟨373424, by rfl⟩ : syracuseStep 1991597 = 746849) (by norm_num)
theorem B1991621 : Blo 1327482 1991621 := bbase (se 4 (by rfl) ⟨186714, by rfl⟩ : syracuseStep 1991621 = 373429) (by norm_num)
theorem B1917901 : Blo 1327482 1917901 := bbase (se 3 (by rfl) ⟨359606, by rfl⟩ : syracuseStep 1917901 = 719213) (by norm_num)
theorem B1991645 : Blo 1327482 1991645 := bbase (se 3 (by rfl) ⟨373433, by rfl⟩ : syracuseStep 1991645 = 746867) (by norm_num)
theorem B1704925 : Blo 1327482 1704925 := bbase (se 3 (by rfl) ⟨319673, by rfl⟩ : syracuseStep 1704925 = 639347) (by norm_num)
theorem B1680365 : Blo 1327482 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B1991669 : Blo 1327482 1991669 := bbase (se 5 (by rfl) ⟨93359, by rfl⟩ : syracuseStep 1991669 = 186719) (by norm_num)
theorem B4482053 : Blo 1327482 4482053 := bbase (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) (by norm_num)
theorem B1991693 : Blo 1327482 1991693 := bbase (se 3 (by rfl) ⟨373442, by rfl⟩ : syracuseStep 1991693 = 746885) (by norm_num)
theorem B1680421 : Blo 1327482 1680421 := bbase (se 4 (by rfl) ⟨157539, by rfl⟩ : syracuseStep 1680421 = 315079) (by norm_num)
theorem B1991717 : Blo 1327482 1991717 := bbase (se 4 (by rfl) ⟨186723, by rfl⟩ : syracuseStep 1991717 = 373447) (by norm_num)
theorem B2155573 : Blo 1327482 2155573 := bbase (se 5 (by rfl) ⟨101042, by rfl⟩ : syracuseStep 2155573 = 202085) (by norm_num)
theorem B10921013 : Blo 1327482 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B1991741 : Blo 1327482 1991741 := bbase (se 3 (by rfl) ⟨373451, by rfl⟩ : syracuseStep 1991741 = 746903) (by norm_num)
theorem B6726725 : Blo 1327482 6726725 := bbase (se 4 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 6726725 = 1261261) (by norm_num)
theorem B1418321 : Blo 1327482 1418321 := bbase (se 2 (by rfl) ⟨531870, by rfl⟩ : syracuseStep 1418321 = 1063741) (by norm_num)
theorem B1991765 : Blo 1327482 1991765 := bbase (se 8 (by rfl) ⟨11670, by rfl⟩ : syracuseStep 1991765 = 23341) (by norm_num)
theorem B1991789 : Blo 1327482 1991789 := bbase (se 3 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 1991789 = 746921) (by norm_num)
theorem B1680517 : Blo 1327482 1680517 := bbase (se 4 (by rfl) ⟨157548, by rfl⟩ : syracuseStep 1680517 = 315097) (by norm_num)
theorem B1991813 : Blo 1327482 1991813 := bbase (se 4 (by rfl) ⟨186732, by rfl⟩ : syracuseStep 1991813 = 373465) (by norm_num)
theorem B1991837 : Blo 1327482 1991837 := bbase (se 3 (by rfl) ⟨373469, by rfl⟩ : syracuseStep 1991837 = 746939) (by norm_num)
theorem B1991861 : Blo 1327482 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B1991885 : Blo 1327482 1991885 := bbase (se 3 (by rfl) ⟨373478, by rfl⟩ : syracuseStep 1991885 = 746957) (by norm_num)
theorem B2835685 : Blo 1327482 2835685 := bbase (se 4 (by rfl) ⟨265845, by rfl⟩ : syracuseStep 2835685 = 531691) (by norm_num)
theorem B1991909 : Blo 1327482 1991909 := bbase (se 4 (by rfl) ⟨186741, by rfl⟩ : syracuseStep 1991909 = 373483) (by norm_num)
theorem B1991933 : Blo 1327482 1991933 := bbase (se 3 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 1991933 = 746975) (by norm_num)
theorem B1418509 : Blo 1327482 1418509 := bbase (se 3 (by rfl) ⟨265970, by rfl⟩ : syracuseStep 1418509 = 531941) (by norm_num)
theorem B1991957 : Blo 1327482 1991957 := bbase (se 6 (by rfl) ⟨46686, by rfl⟩ : syracuseStep 1991957 = 93373) (by norm_num)
theorem B1991981 : Blo 1327482 1991981 := bbase (se 3 (by rfl) ⟨373496, by rfl⟩ : syracuseStep 1991981 = 746993) (by norm_num)
theorem B1680689 : Blo 1327482 1680689 := bbase (se 2 (by rfl) ⟨630258, by rfl⟩ : syracuseStep 1680689 = 1260517) (by norm_num)
theorem B1992005 : Blo 1327482 1992005 := bbase (se 4 (by rfl) ⟨186750, by rfl⟩ : syracuseStep 1992005 = 373501) (by norm_num)
theorem B2835805 : Blo 1327482 2835805 := bbase (se 3 (by rfl) ⟨531713, by rfl⟩ : syracuseStep 2835805 = 1063427) (by norm_num)
theorem B1992029 : Blo 1327482 1992029 := bbase (se 3 (by rfl) ⟨373505, by rfl⟩ : syracuseStep 1992029 = 747011) (by norm_num)
theorem B1680745 : Blo 1327482 1680745 := bbase (se 2 (by rfl) ⟨630279, by rfl⟩ : syracuseStep 1680745 = 1260559) (by norm_num)
theorem B1992053 : Blo 1327482 1992053 := bbase (se 5 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 1992053 = 186755) (by norm_num)
theorem B1992077 : Blo 1327482 1992077 := bbase (se 3 (by rfl) ⟨373514, by rfl⟩ : syracuseStep 1992077 = 747029) (by norm_num)
theorem B10225045 : Blo 1327482 10225045 := bbase (se 6 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 10225045 = 479299) (by norm_num)
theorem B4253093 : Blo 1327482 4253093 := bbase (se 4 (by rfl) ⟨398727, by rfl⟩ : syracuseStep 4253093 = 797455) (by norm_num)
theorem B1992101 : Blo 1327482 1992101 := bbase (se 4 (by rfl) ⟨186759, by rfl⟩ : syracuseStep 1992101 = 373519) (by norm_num)
theorem B4482485 : Blo 1327482 4482485 := bbase (se 5 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 4482485 = 420233) (by norm_num)
theorem B2590141 : Blo 1327482 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B1992125 : Blo 1327482 1992125 := bbase (se 3 (by rfl) ⟨373523, by rfl⟩ : syracuseStep 1992125 = 747047) (by norm_num)
theorem B1680841 : Blo 1327482 1680841 := bbase (se 2 (by rfl) ⟨630315, by rfl⟩ : syracuseStep 1680841 = 1260631) (by norm_num)
theorem B1992149 : Blo 1327482 1992149 := bbase (se 7 (by rfl) ⟨23345, by rfl⟩ : syracuseStep 1992149 = 46691) (by norm_num)
theorem B1992173 : Blo 1327482 1992173 := bbase (se 3 (by rfl) ⟨373532, by rfl⟩ : syracuseStep 1992173 = 747065) (by norm_num)
theorem B1992197 : Blo 1327482 1992197 := bbase (se 4 (by rfl) ⟨186768, by rfl⟩ : syracuseStep 1992197 = 373537) (by norm_num)
theorem B1992221 : Blo 1327482 1992221 := bbase (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) (by norm_num)
theorem B1992245 : Blo 1327482 1992245 := bbase (se 5 (by rfl) ⟨93386, by rfl⟩ : syracuseStep 1992245 = 186773) (by norm_num)
theorem B3360325 : Blo 1327482 3360325 := bbase (se 4 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 3360325 = 630061) (by norm_num)
theorem B1992269 : Blo 1327482 1992269 := bbase (se 3 (by rfl) ⟨373550, by rfl⟩ : syracuseStep 1992269 = 747101) (by norm_num)
theorem B2836061 : Blo 1327482 2836061 := bbase (se 3 (by rfl) ⟨531761, by rfl⟩ : syracuseStep 2836061 = 1063523) (by norm_num)
theorem B1992293 : Blo 1327482 1992293 := bbase (se 4 (by rfl) ⟨186777, by rfl⟩ : syracuseStep 1992293 = 373555) (by norm_num)
theorem B1681013 : Blo 1327482 1681013 := bbase (se 5 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 1681013 = 157595) (by norm_num)
theorem B1992317 : Blo 1327482 1992317 := bbase (se 3 (by rfl) ⟨373559, by rfl⟩ : syracuseStep 1992317 = 747119) (by norm_num)
theorem B1992341 : Blo 1327482 1992341 := bbase (se 6 (by rfl) ⟨46695, by rfl⟩ : syracuseStep 1992341 = 93391) (by norm_num)
theorem B2393749 : Blo 1327482 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B1992365 : Blo 1327482 1992365 := bbase (se 3 (by rfl) ⟨373568, by rfl⟩ : syracuseStep 1992365 = 747137) (by norm_num)
theorem B1681069 : Blo 1327482 1681069 := bbase (se 3 (by rfl) ⟨315200, by rfl⟩ : syracuseStep 1681069 = 630401) (by norm_num)
theorem B3360437 : Blo 1327482 3360437 := bbase (se 5 (by rfl) ⟨157520, by rfl⟩ : syracuseStep 3360437 = 315041) (by norm_num)
theorem B1992389 : Blo 1327482 1992389 := bbase (se 4 (by rfl) ⟨186786, by rfl⟩ : syracuseStep 1992389 = 373573) (by norm_num)
theorem B1992413 : Blo 1327482 1992413 := bbase (se 3 (by rfl) ⟨373577, by rfl⟩ : syracuseStep 1992413 = 747155) (by norm_num)
theorem B1992437 : Blo 1327482 1992437 := bbase (se 5 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 1992437 = 186791) (by norm_num)
theorem B1992461 : Blo 1327482 1992461 := bbase (se 3 (by rfl) ⟨373586, by rfl⟩ : syracuseStep 1992461 = 747173) (by norm_num)
theorem B1681165 : Blo 1327482 1681165 := bbase (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) (by norm_num)
theorem B9086741 : Blo 1327482 9086741 := bbase (se 6 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 9086741 = 425941) (by norm_num)
theorem B7669525 : Blo 1327482 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B1992485 : Blo 1327482 1992485 := bbase (se 4 (by rfl) ⟨186795, by rfl⟩ : syracuseStep 1992485 = 373591) (by norm_num)
theorem B1992509 : Blo 1327482 1992509 := bbase (se 3 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 1992509 = 747191) (by norm_num)
theorem B1992533 : Blo 1327482 1992533 := bbase (se 9 (by rfl) ⟨5837, by rfl⟩ : syracuseStep 1992533 = 11675) (by norm_num)
theorem B6055781 : Blo 1327482 6055781 := bbase (se 4 (by rfl) ⟨567729, by rfl⟩ : syracuseStep 6055781 = 1135459) (by norm_num)
theorem B4482917 : Blo 1327482 4482917 := bbase (se 4 (by rfl) ⟨420273, by rfl⟩ : syracuseStep 4482917 = 840547) (by norm_num)
theorem B1992557 : Blo 1327482 1992557 := bbase (se 3 (by rfl) ⟨373604, by rfl⟩ : syracuseStep 1992557 = 747209) (by norm_num)
theorem B3360629 : Blo 1327482 3360629 := bbase (se 5 (by rfl) ⟨157529, by rfl⟩ : syracuseStep 3360629 = 315059) (by norm_num)
theorem B1992581 : Blo 1327482 1992581 := bbase (se 4 (by rfl) ⟨186804, by rfl⟩ : syracuseStep 1992581 = 373609) (by norm_num)
theorem B1992605 : Blo 1327482 1992605 := bbase (se 3 (by rfl) ⟨373613, by rfl⟩ : syracuseStep 1992605 = 747227) (by norm_num)
theorem B1992629 : Blo 1327482 1992629 := bbase (se 5 (by rfl) ⟨93404, by rfl⟩ : syracuseStep 1992629 = 186809) (by norm_num)
theorem B1681337 : Blo 1327482 1681337 := bbase (se 2 (by rfl) ⟨630501, by rfl⟩ : syracuseStep 1681337 = 1261003) (by norm_num)
theorem B1992653 : Blo 1327482 1992653 := bbase (se 3 (by rfl) ⟨373622, by rfl⟩ : syracuseStep 1992653 = 747245) (by norm_num)
theorem B1992677 : Blo 1327482 1992677 := bbase (se 4 (by rfl) ⟨186813, by rfl⟩ : syracuseStep 1992677 = 373627) (by norm_num)
theorem B1681393 : Blo 1327482 1681393 := bbase (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) (by norm_num)
theorem B1992701 : Blo 1327482 1992701 := bbase (se 3 (by rfl) ⟨373631, by rfl⟩ : syracuseStep 1992701 = 747263) (by norm_num)
theorem B1992725 : Blo 1327482 1992725 := bbase (se 6 (by rfl) ⟨46704, by rfl⟩ : syracuseStep 1992725 = 93409) (by norm_num)
theorem B1992749 : Blo 1327482 1992749 := bbase (se 3 (by rfl) ⟨373640, by rfl⟩ : syracuseStep 1992749 = 747281) (by norm_num)
theorem B1992773 : Blo 1327482 1992773 := bbase (se 4 (by rfl) ⟨186822, by rfl⟩ : syracuseStep 1992773 = 373645) (by norm_num)
theorem B1681489 : Blo 1327482 1681489 := bbase (se 2 (by rfl) ⟨630558, by rfl⟩ : syracuseStep 1681489 = 1261117) (by norm_num)
theorem B1992797 : Blo 1327482 1992797 := bbase (se 3 (by rfl) ⟨373649, by rfl⟩ : syracuseStep 1992797 = 747299) (by norm_num)
theorem B1992821 : Blo 1327482 1992821 := bbase (se 5 (by rfl) ⟨93413, by rfl⟩ : syracuseStep 1992821 = 186827) (by norm_num)
theorem B1992845 : Blo 1327482 1992845 := bbase (se 3 (by rfl) ⟨373658, by rfl⟩ : syracuseStep 1992845 = 747317) (by norm_num)
theorem B1992869 : Blo 1327482 1992869 := bbase (se 4 (by rfl) ⟨186831, by rfl⟩ : syracuseStep 1992869 = 373663) (by norm_num)
theorem B1992893 : Blo 1327482 1992893 := bbase (se 3 (by rfl) ⟨373667, by rfl⟩ : syracuseStep 1992893 = 747335) (by norm_num)
theorem B3360973 : Blo 1327482 3360973 := bbase (se 3 (by rfl) ⟨630182, by rfl⟩ : syracuseStep 3360973 = 1260365) (by norm_num)
theorem B1992917 : Blo 1327482 1992917 := bbase (se 7 (by rfl) ⟨23354, by rfl⟩ : syracuseStep 1992917 = 46709) (by norm_num)
theorem B1992941 : Blo 1327482 1992941 := bbase (se 3 (by rfl) ⟨373676, by rfl⟩ : syracuseStep 1992941 = 747353) (by norm_num)
theorem B1681661 : Blo 1327482 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B1992965 : Blo 1327482 1992965 := bbase (se 4 (by rfl) ⟨186840, by rfl⟩ : syracuseStep 1992965 = 373681) (by norm_num)
theorem B4483349 : Blo 1327482 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B1992989 : Blo 1327482 1992989 := bbase (se 3 (by rfl) ⟨373685, by rfl⟩ : syracuseStep 1992989 = 747371) (by norm_num)
theorem B1993013 : Blo 1327482 1993013 := bbase (se 5 (by rfl) ⟨93422, by rfl⟩ : syracuseStep 1993013 = 186845) (by norm_num)
theorem B1681717 : Blo 1327482 1681717 := bbase (se 5 (by rfl) ⟨78830, by rfl⟩ : syracuseStep 1681717 = 157661) (by norm_num)
theorem B3361085 : Blo 1327482 3361085 := bbase (se 3 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 3361085 = 1260407) (by norm_num)
theorem B1993037 : Blo 1327482 1993037 := bbase (se 3 (by rfl) ⟨373694, by rfl⟩ : syracuseStep 1993037 = 747389) (by norm_num)
theorem B1993061 : Blo 1327482 1993061 := bbase (se 4 (by rfl) ⟨186849, by rfl⟩ : syracuseStep 1993061 = 373699) (by norm_num)
theorem B1993085 : Blo 1327482 1993085 := bbase (se 3 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 1993085 = 747407) (by norm_num)
theorem B1993109 : Blo 1327482 1993109 := bbase (se 6 (by rfl) ⟨46713, by rfl⟩ : syracuseStep 1993109 = 93427) (by norm_num)
theorem B1681813 : Blo 1327482 1681813 := bbase (se 6 (by rfl) ⟨39417, by rfl⟩ : syracuseStep 1681813 = 78835) (by norm_num)
theorem B1993133 : Blo 1327482 1993133 := bbase (se 3 (by rfl) ⟨373712, by rfl⟩ : syracuseStep 1993133 = 747425) (by norm_num)
theorem B2394541 : Blo 1327482 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B1493437 : Blo 1327482 1493437 := bbase (se 3 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 1493437 = 560039) (by norm_num)
theorem B1993157 : Blo 1327482 1993157 := bbase (se 4 (by rfl) ⟨186858, by rfl⟩ : syracuseStep 1993157 = 373717) (by norm_num)
theorem B2836949 : Blo 1327482 2836949 := bbase (se 7 (by rfl) ⟨33245, by rfl⟩ : syracuseStep 2836949 = 66491) (by norm_num)
theorem B1993181 : Blo 1327482 1993181 := bbase (se 3 (by rfl) ⟨373721, by rfl⟩ : syracuseStep 1993181 = 747443) (by norm_num)
theorem B1493473 : Blo 1327482 1493473 := bbase (se 2 (by rfl) ⟨560052, by rfl⟩ : syracuseStep 1493473 = 1120105) (by norm_num)
theorem B1993205 : Blo 1327482 1993205 := bbase (se 5 (by rfl) ⟨93431, by rfl⟩ : syracuseStep 1993205 = 186863) (by norm_num)
theorem B3361277 : Blo 1327482 3361277 := bbase (se 3 (by rfl) ⟨630239, by rfl⟩ : syracuseStep 3361277 = 1260479) (by norm_num)
theorem B1493509 : Blo 1327482 1493509 := bbase (se 4 (by rfl) ⟨140016, by rfl⟩ : syracuseStep 1493509 = 280033) (by norm_num)
theorem B1993229 : Blo 1327482 1993229 := bbase (se 3 (by rfl) ⟨373730, by rfl⟩ : syracuseStep 1993229 = 747461) (by norm_num)
theorem B1993253 : Blo 1327482 1993253 := bbase (se 4 (by rfl) ⟨186867, by rfl⟩ : syracuseStep 1993253 = 373735) (by norm_num)
theorem B1493545 : Blo 1327482 1493545 := bbase (se 2 (by rfl) ⟨560079, by rfl⟩ : syracuseStep 1493545 = 1120159) (by norm_num)
theorem B1993277 : Blo 1327482 1993277 := bbase (se 3 (by rfl) ⟨373739, by rfl⟩ : syracuseStep 1993277 = 747479) (by norm_num)
theorem B1681985 : Blo 1327482 1681985 := bbase (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) (by norm_num)
theorem B1493581 : Blo 1327482 1493581 := bbase (se 3 (by rfl) ⟨280046, by rfl⟩ : syracuseStep 1493581 = 560093) (by norm_num)
theorem B1993301 : Blo 1327482 1993301 := bbase (se 8 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 1993301 = 23359) (by norm_num)
theorem B1993325 : Blo 1327482 1993325 := bbase (se 3 (by rfl) ⟨373748, by rfl⟩ : syracuseStep 1993325 = 747497) (by norm_num)
theorem B1493617 : Blo 1327482 1493617 := bbase (se 2 (by rfl) ⟨560106, by rfl⟩ : syracuseStep 1493617 = 1120213) (by norm_num)
theorem B1993349 : Blo 1327482 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B1493653 : Blo 1327482 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1993373 : Blo 1327482 1993373 := bbase (se 3 (by rfl) ⟨373757, by rfl⟩ : syracuseStep 1993373 = 747515) (by norm_num)
theorem B1993397 : Blo 1327482 1993397 := bbase (se 5 (by rfl) ⟨93440, by rfl⟩ : syracuseStep 1993397 = 186881) (by norm_num)
theorem B1493689 : Blo 1327482 1493689 := bbase (se 2 (by rfl) ⟨560133, by rfl⟩ : syracuseStep 1493689 = 1120267) (by norm_num)
theorem B2837189 : Blo 1327482 2837189 := bbase (se 4 (by rfl) ⟨265986, by rfl⟩ : syracuseStep 2837189 = 531973) (by norm_num)
theorem B4483781 : Blo 1327482 4483781 := bbase (se 4 (by rfl) ⟨420354, by rfl⟩ : syracuseStep 4483781 = 840709) (by norm_num)
theorem B1993421 : Blo 1327482 1993421 := bbase (se 3 (by rfl) ⟨373766, by rfl⟩ : syracuseStep 1993421 = 747533) (by norm_num)
theorem B1493725 : Blo 1327482 1493725 := bbase (se 3 (by rfl) ⟨280073, by rfl⟩ : syracuseStep 1493725 = 560147) (by norm_num)
theorem B1993445 : Blo 1327482 1993445 := bbase (se 4 (by rfl) ⟨186885, by rfl⟩ : syracuseStep 1993445 = 373771) (by norm_num)
theorem B1993469 : Blo 1327482 1993469 := bbase (se 3 (by rfl) ⟨373775, by rfl⟩ : syracuseStep 1993469 = 747551) (by norm_num)
theorem B1493761 : Blo 1327482 1493761 := bbase (se 2 (by rfl) ⟨560160, by rfl⟩ : syracuseStep 1493761 = 1120321) (by norm_num)
theorem B8506133 : Blo 1327482 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B1493797 : Blo 1327482 1493797 := bbase (se 4 (by rfl) ⟨140043, by rfl⟩ : syracuseStep 1493797 = 280087) (by norm_num)
theorem B1493833 : Blo 1327482 1493833 := bbase (se 2 (by rfl) ⟨560187, by rfl⟩ : syracuseStep 1493833 = 1120375) (by norm_num)
theorem B3361621 : Blo 1327482 3361621 := bbase (se 9 (by rfl) ⟨9848, by rfl⟩ : syracuseStep 3361621 = 19697) (by norm_num)
theorem B5671781 : Blo 1327482 5671781 := bbase (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) (by norm_num)
theorem B1493869 : Blo 1327482 1493869 := bbase (se 3 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 1493869 = 560201) (by norm_num)
theorem B1493905 : Blo 1327482 1493905 := bbase (se 2 (by rfl) ⟨560214, by rfl⟩ : syracuseStep 1493905 = 1120429) (by norm_num)
theorem B1493941 : Blo 1327482 1493941 := bbase (se 5 (by rfl) ⟨70028, by rfl⟩ : syracuseStep 1493941 = 140057) (by norm_num)
theorem B3361733 : Blo 1327482 3361733 := bbase (se 4 (by rfl) ⟨315162, by rfl⟩ : syracuseStep 3361733 = 630325) (by norm_num)
theorem B1493977 : Blo 1327482 1493977 := bbase (se 2 (by rfl) ⟨560241, by rfl⟩ : syracuseStep 1493977 = 1120483) (by norm_num)
theorem B1494013 : Blo 1327482 1494013 := bbase (se 3 (by rfl) ⟨280127, by rfl⟩ : syracuseStep 1494013 = 560255) (by norm_num)
theorem B1494049 : Blo 1327482 1494049 := bbase (se 2 (by rfl) ⟨560268, by rfl⟩ : syracuseStep 1494049 = 1120537) (by norm_num)
theorem B4787237 : Blo 1327482 4787237 := bbase (se 4 (by rfl) ⟨448803, by rfl⟩ : syracuseStep 4787237 = 897607) (by norm_num)
theorem B1494085 : Blo 1327482 1494085 := bbase (se 4 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 1494085 = 280141) (by norm_num)
theorem B1494121 : Blo 1327482 1494121 := bbase (se 2 (by rfl) ⟨560295, by rfl⟩ : syracuseStep 1494121 = 1120591) (by norm_num)
theorem B4484213 : Blo 1327482 4484213 := bbase (se 5 (by rfl) ⟨210197, by rfl⟩ : syracuseStep 4484213 = 420395) (by norm_num)
theorem B3361925 : Blo 1327482 3361925 := bbase (se 4 (by rfl) ⟨315180, by rfl⟩ : syracuseStep 3361925 = 630361) (by norm_num)
theorem B1494157 : Blo 1327482 1494157 := bbase (se 3 (by rfl) ⟨280154, by rfl⟩ : syracuseStep 1494157 = 560309) (by norm_num)
theorem B3591317 : Blo 1327482 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B1494193 : Blo 1327482 1494193 := bbase (se 2 (by rfl) ⟨560322, by rfl⟩ : syracuseStep 1494193 = 1120645) (by norm_num)
theorem B2837693 : Blo 1327482 2837693 := bbase (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) (by norm_num)
theorem B2837701 : Blo 1327482 2837701 := bbase (se 4 (by rfl) ⟨266034, by rfl⟩ : syracuseStep 2837701 = 532069) (by norm_num)
theorem B1494229 : Blo 1327482 1494229 := bbase (se 7 (by rfl) ⟨17510, by rfl⟩ : syracuseStep 1494229 = 35021) (by norm_num)
theorem B1494265 : Blo 1327482 1494265 := bbase (se 2 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 1494265 = 1120699) (by norm_num)
theorem B1494301 : Blo 1327482 1494301 := bbase (se 3 (by rfl) ⟨280181, by rfl⟩ : syracuseStep 1494301 = 560363) (by norm_num)
theorem B1346873 : Blo 1327482 1346873 := bbase (se 2 (by rfl) ⟨505077, by rfl⟩ : syracuseStep 1346873 = 1010155) (by norm_num)
theorem B1494337 : Blo 1327482 1494337 := bbase (se 2 (by rfl) ⟨560376, by rfl⟩ : syracuseStep 1494337 = 1120753) (by norm_num)
theorem B32320853 : Blo 1327482 32320853 := bbase (se 11 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 32320853 = 47345) (by norm_num)
theorem B1494373 : Blo 1327482 1494373 := bbase (se 4 (by rfl) ⟨140097, by rfl⟩ : syracuseStep 1494373 = 280195) (by norm_num)
theorem B1494409 : Blo 1327482 1494409 := bbase (se 2 (by rfl) ⟨560403, by rfl⟩ : syracuseStep 1494409 = 1120807) (by norm_num)
theorem B1494445 : Blo 1327482 1494445 := bbase (se 3 (by rfl) ⟨280208, by rfl⟩ : syracuseStep 1494445 = 560417) (by norm_num)
theorem B1494481 : Blo 1327482 1494481 := bbase (se 2 (by rfl) ⟨560430, by rfl⟩ : syracuseStep 1494481 = 1120861) (by norm_num)
theorem B3362269 : Blo 1327482 3362269 := bbase (se 3 (by rfl) ⟨630425, by rfl⟩ : syracuseStep 3362269 = 1260851) (by norm_num)
theorem B3190261 : Blo 1327482 3190261 := bbase (se 5 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 3190261 = 299087) (by norm_num)
theorem B1494517 : Blo 1327482 1494517 := bbase (se 5 (by rfl) ⟨70055, by rfl⟩ : syracuseStep 1494517 = 140111) (by norm_num)
theorem B15543829 : Blo 1327482 15543829 := bbase (se 6 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 15543829 = 728617) (by norm_num)
theorem B1494553 : Blo 1327482 1494553 := bbase (se 2 (by rfl) ⟨560457, by rfl⟩ : syracuseStep 1494553 = 1120915) (by norm_num)
theorem B4484645 : Blo 1327482 4484645 := bbase (se 4 (by rfl) ⟨420435, by rfl⟩ : syracuseStep 4484645 = 840871) (by norm_num)
theorem B1494589 : Blo 1327482 1494589 := bbase (se 3 (by rfl) ⟨280235, by rfl⟩ : syracuseStep 1494589 = 560471) (by norm_num)
theorem B3362381 : Blo 1327482 3362381 := bbase (se 3 (by rfl) ⟨630446, by rfl⟩ : syracuseStep 3362381 = 1260893) (by norm_num)
theorem B1494625 : Blo 1327482 1494625 := bbase (se 2 (by rfl) ⟨560484, by rfl⟩ : syracuseStep 1494625 = 1120969) (by norm_num)
theorem B1494661 : Blo 1327482 1494661 := bbase (se 4 (by rfl) ⟨140124, by rfl⟩ : syracuseStep 1494661 = 280249) (by norm_num)
theorem B2240149 : Blo 1327482 2240149 := bbase (se 6 (by rfl) ⟨52503, by rfl⟩ : syracuseStep 2240149 = 105007) (by norm_num)
theorem B1494697 : Blo 1327482 1494697 := bbase (se 2 (by rfl) ⟨560511, by rfl⟩ : syracuseStep 1494697 = 1121023) (by norm_num)
theorem B1494733 : Blo 1327482 1494733 := bbase (se 3 (by rfl) ⟨280262, by rfl⟩ : syracuseStep 1494733 = 560525) (by norm_num)
theorem B2240237 : Blo 1327482 2240237 := bbase (se 3 (by rfl) ⟨420044, by rfl⟩ : syracuseStep 2240237 = 840089) (by norm_num)
theorem B1494769 : Blo 1327482 1494769 := bbase (se 2 (by rfl) ⟨560538, by rfl⟩ : syracuseStep 1494769 = 1121077) (by norm_num)
theorem B3362573 : Blo 1327482 3362573 := bbase (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) (by norm_num)
theorem B1494805 : Blo 1327482 1494805 := bbase (se 6 (by rfl) ⟨35034, by rfl⟩ : syracuseStep 1494805 = 70069) (by norm_num)
theorem B2019125 : Blo 1327482 2019125 := bbase (se 5 (by rfl) ⟨94646, by rfl⟩ : syracuseStep 2019125 = 189293) (by norm_num)
theorem B1494841 : Blo 1327482 1494841 := bbase (se 2 (by rfl) ⟨560565, by rfl⟩ : syracuseStep 1494841 = 1121131) (by norm_num)
theorem B1494877 : Blo 1327482 1494877 := bbase (se 3 (by rfl) ⟨280289, by rfl⟩ : syracuseStep 1494877 = 560579) (by norm_num)
theorem B2240365 : Blo 1327482 2240365 := bbase (se 3 (by rfl) ⟨420068, by rfl⟩ : syracuseStep 2240365 = 840137) (by norm_num)
theorem B1494913 : Blo 1327482 1494913 := bbase (se 2 (by rfl) ⟨560592, by rfl⟩ : syracuseStep 1494913 = 1121185) (by norm_num)
theorem B15339413 : Blo 1327482 15339413 := bbase (se 6 (by rfl) ⟨359517, by rfl⟩ : syracuseStep 15339413 = 719035) (by norm_num)
theorem B1494949 : Blo 1327482 1494949 := bbase (se 4 (by rfl) ⟨140151, by rfl⟩ : syracuseStep 1494949 = 280303) (by norm_num)
theorem B2240453 : Blo 1327482 2240453 := bbase (se 4 (by rfl) ⟨210042, by rfl⟩ : syracuseStep 2240453 = 420085) (by norm_num)
theorem B1494985 : Blo 1327482 1494985 := bbase (se 2 (by rfl) ⟨560619, by rfl⟩ : syracuseStep 1494985 = 1121239) (by norm_num)
theorem B4485077 : Blo 1327482 4485077 := bbase (se 7 (by rfl) ⟨52559, by rfl⟩ : syracuseStep 4485077 = 105119) (by norm_num)
theorem B1495021 : Blo 1327482 1495021 := bbase (se 3 (by rfl) ⟨280316, by rfl⟩ : syracuseStep 1495021 = 560633) (by norm_num)
theorem B2019325 : Blo 1327482 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B6721541 : Blo 1327482 6721541 := bbase (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) (by norm_num)
theorem B1495057 : Blo 1327482 1495057 := bbase (se 2 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 1495057 = 1121293) (by norm_num)
theorem B1495093 : Blo 1327482 1495093 := bbase (se 5 (by rfl) ⟨70082, by rfl⟩ : syracuseStep 1495093 = 140165) (by norm_num)
theorem B2240581 : Blo 1327482 2240581 := bbase (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) (by norm_num)
theorem B3190877 : Blo 1327482 3190877 := bbase (se 3 (by rfl) ⟨598289, by rfl⟩ : syracuseStep 3190877 = 1196579) (by norm_num)
theorem B3362917 : Blo 1327482 3362917 := bbase (se 4 (by rfl) ⟨315273, by rfl⟩ : syracuseStep 3362917 = 630547) (by norm_num)
theorem B4255861 : Blo 1327482 4255861 := bbase (se 5 (by rfl) ⟨199493, by rfl⟩ : syracuseStep 4255861 = 398987) (by norm_num)
theorem B2240669 : Blo 1327482 2240669 := bbase (se 3 (by rfl) ⟨420125, by rfl⟩ : syracuseStep 2240669 = 840251) (by norm_num)
theorem B5042357 : Blo 1327482 5042357 := bbase (se 5 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 5042357 = 472721) (by norm_num)
theorem B3363029 : Blo 1327482 3363029 := bbase (se 7 (by rfl) ⟨39410, by rfl⟩ : syracuseStep 3363029 = 78821) (by norm_num)
theorem B2240797 : Blo 1327482 2240797 := bbase (se 3 (by rfl) ⟨420149, by rfl⟩ : syracuseStep 2240797 = 840299) (by norm_num)
theorem B3191069 : Blo 1327482 3191069 := bbase (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) (by norm_num)
theorem B3887461 : Blo 1327482 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B2240885 : Blo 1327482 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B3363221 : Blo 1327482 3363221 := bbase (se 6 (by rfl) ⟨78825, by rfl⟩ : syracuseStep 3363221 = 157651) (by norm_num)
theorem B5042645 : Blo 1327482 5042645 := bbase (se 7 (by rfl) ⟨59093, by rfl⟩ : syracuseStep 5042645 = 118187) (by norm_num)
theorem B2691557 : Blo 1327482 2691557 := bbase (se 4 (by rfl) ⟨252333, by rfl⟩ : syracuseStep 2691557 = 504667) (by norm_num)
theorem B2241013 : Blo 1327482 2241013 := bbase (se 5 (by rfl) ⟨105047, by rfl⟩ : syracuseStep 2241013 = 210095) (by norm_num)
theorem B10768949 : Blo 1327482 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B3191357 : Blo 1327482 3191357 := bbase (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) (by norm_num)
theorem B2241101 : Blo 1327482 2241101 := bbase (se 3 (by rfl) ⟨420206, by rfl⟩ : syracuseStep 2241101 = 840413) (by norm_num)
theorem B5673557 : Blo 1327482 5673557 := bbase (se 8 (by rfl) ⟨33243, by rfl⟩ : syracuseStep 5673557 = 66487) (by norm_num)
theorem B1364645 : Blo 1327482 1364645 := bbase (se 4 (by rfl) ⟨127935, by rfl⟩ : syracuseStep 1364645 = 255871) (by norm_num)
theorem B2241229 : Blo 1327482 2241229 := bbase (se 3 (by rfl) ⟨420230, by rfl⟩ : syracuseStep 2241229 = 840461) (by norm_num)
theorem B3363565 : Blo 1327482 3363565 := bbase (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) (by norm_num)
theorem B2241317 : Blo 1327482 2241317 := bbase (se 4 (by rfl) ⟨210123, by rfl⟩ : syracuseStep 2241317 = 420247) (by norm_num)
theorem B5673797 : Blo 1327482 5673797 := bbase (se 4 (by rfl) ⟨531918, by rfl⟩ : syracuseStep 5673797 = 1063837) (by norm_num)
theorem B3363677 : Blo 1327482 3363677 := bbase (se 3 (by rfl) ⟨630689, by rfl⟩ : syracuseStep 3363677 = 1261379) (by norm_num)
theorem B2986901 : Blo 1327482 2986901 := bbase (se 6 (by rfl) ⟨70005, by rfl⟩ : syracuseStep 2986901 = 140011) (by norm_num)
theorem B2241445 : Blo 1327482 2241445 := bbase (se 4 (by rfl) ⟨210135, by rfl⟩ : syracuseStep 2241445 = 420271) (by norm_num)
theorem B2986973 : Blo 1327482 2986973 := bbase (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) (by norm_num)
theorem B2241533 : Blo 1327482 2241533 := bbase (se 3 (by rfl) ⟨420287, by rfl⟩ : syracuseStep 2241533 = 840575) (by norm_num)
theorem B2692109 : Blo 1327482 2692109 := bbase (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) (by norm_num)
theorem B3363869 : Blo 1327482 3363869 := bbase (se 3 (by rfl) ⟨630725, by rfl⟩ : syracuseStep 3363869 = 1261451) (by norm_num)
theorem B2987045 : Blo 1327482 2987045 := bbase (se 4 (by rfl) ⟨280035, by rfl⟩ : syracuseStep 2987045 = 560071) (by norm_num)
theorem B2987117 : Blo 1327482 2987117 := bbase (se 3 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 2987117 = 1120169) (by norm_num)
theorem B2241661 : Blo 1327482 2241661 := bbase (se 3 (by rfl) ⟨420311, by rfl⟩ : syracuseStep 2241661 = 840623) (by norm_num)
theorem B2126989 : Blo 1327482 2126989 := bbase (se 3 (by rfl) ⟨398810, by rfl⟩ : syracuseStep 2126989 = 797621) (by norm_num)
theorem B2520229 : Blo 1327482 2520229 := bbase (se 4 (by rfl) ⟨236271, by rfl⟩ : syracuseStep 2520229 = 472543) (by norm_num)
theorem B2987189 : Blo 1327482 2987189 := bbase (se 5 (by rfl) ⟨140024, by rfl⟩ : syracuseStep 2987189 = 280049) (by norm_num)
theorem B2241749 : Blo 1327482 2241749 := bbase (se 7 (by rfl) ⟨26270, by rfl⟩ : syracuseStep 2241749 = 52541) (by norm_num)
theorem B2987261 : Blo 1327482 2987261 := bbase (se 3 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 2987261 = 1120223) (by norm_num)
theorem B6722837 : Blo 1327482 6722837 := bbase (se 6 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 6722837 = 315133) (by norm_num)
theorem B2520389 : Blo 1327482 2520389 := bbase (se 4 (by rfl) ⟨236286, by rfl⟩ : syracuseStep 2520389 = 472573) (by norm_num)
theorem B2987333 : Blo 1327482 2987333 := bbase (se 4 (by rfl) ⟨280062, by rfl⟩ : syracuseStep 2987333 = 560125) (by norm_num)
theorem B2241877 : Blo 1327482 2241877 := bbase (se 13 (by rfl) ⟨410, by rfl⟩ : syracuseStep 2241877 = 821) (by norm_num)
theorem B10089845 : Blo 1327482 10089845 := bbase (se 5 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 10089845 = 945923) (by norm_num)
theorem B2987405 : Blo 1327482 2987405 := bbase (se 3 (by rfl) ⟨560138, by rfl⟩ : syracuseStep 2987405 = 1120277) (by norm_num)
theorem B2241965 : Blo 1327482 2241965 := bbase (se 3 (by rfl) ⟨420368, by rfl⟩ : syracuseStep 2241965 = 840737) (by norm_num)
theorem B2520533 : Blo 1327482 2520533 := bbase (se 7 (by rfl) ⟨29537, by rfl⟩ : syracuseStep 2520533 = 59075) (by norm_num)
theorem B2987477 : Blo 1327482 2987477 := bbase (se 7 (by rfl) ⟨35009, by rfl⟩ : syracuseStep 2987477 = 70019) (by norm_num)
theorem B2987549 : Blo 1327482 2987549 := bbase (se 3 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 2987549 = 1120331) (by norm_num)
theorem B2242093 : Blo 1327482 2242093 := bbase (se 3 (by rfl) ⟨420392, by rfl⟩ : syracuseStep 2242093 = 840785) (by norm_num)
theorem B2692685 : Blo 1327482 2692685 := bbase (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) (by norm_num)
theorem B2987621 : Blo 1327482 2987621 := bbase (se 4 (by rfl) ⟨280089, by rfl⟩ : syracuseStep 2987621 = 560179) (by norm_num)
theorem B5043829 : Blo 1327482 5043829 := bbase (se 5 (by rfl) ⟨236429, by rfl⟩ : syracuseStep 5043829 = 472859) (by norm_num)
theorem B2242181 : Blo 1327482 2242181 := bbase (se 4 (by rfl) ⟨210204, by rfl⟩ : syracuseStep 2242181 = 420409) (by norm_num)
theorem B2692757 : Blo 1327482 2692757 := bbase (se 6 (by rfl) ⟨63111, by rfl⟩ : syracuseStep 2692757 = 126223) (by norm_num)
theorem B2987693 : Blo 1327482 2987693 := bbase (se 3 (by rfl) ⟨560192, by rfl⟩ : syracuseStep 2987693 = 1120385) (by norm_num)
theorem B2520821 : Blo 1327482 2520821 := bbase (se 5 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 2520821 = 236327) (by norm_num)
theorem B2987765 : Blo 1327482 2987765 := bbase (se 5 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 2987765 = 280103) (by norm_num)
theorem B2242309 : Blo 1327482 2242309 := bbase (se 4 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 2242309 = 420433) (by norm_num)
theorem B10082069 : Blo 1327482 10082069 := bbase (se 6 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 10082069 = 472597) (by norm_num)
theorem B2987837 : Blo 1327482 2987837 := bbase (se 3 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 2987837 = 1120439) (by norm_num)
theorem B2242397 : Blo 1327482 2242397 := bbase (se 3 (by rfl) ⟨420449, by rfl⟩ : syracuseStep 2242397 = 840899) (by norm_num)
theorem B2987909 : Blo 1327482 2987909 := bbase (se 4 (by rfl) ⟨280116, by rfl⟩ : syracuseStep 2987909 = 560233) (by norm_num)
theorem B2520973 : Blo 1327482 2520973 := bbase (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) (by norm_num)
theorem B5044133 : Blo 1327482 5044133 := bbase (se 4 (by rfl) ⟨472887, by rfl⟩ : syracuseStep 5044133 = 945775) (by norm_num)
theorem B6379445 : Blo 1327482 6379445 := bbase (se 5 (by rfl) ⟨299036, by rfl⟩ : syracuseStep 6379445 = 598073) (by norm_num)
theorem B1890229 : Blo 1327482 1890229 := bbase (se 5 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 1890229 = 177209) (by norm_num)
theorem B1595333 : Blo 1327482 1595333 := bbase (se 4 (by rfl) ⟨149562, by rfl⟩ : syracuseStep 1595333 = 299125) (by norm_num)
theorem B2987981 : Blo 1327482 2987981 := bbase (se 3 (by rfl) ⟨560246, by rfl⟩ : syracuseStep 2987981 = 1120493) (by norm_num)
theorem B2242525 : Blo 1327482 2242525 := bbase (se 3 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 2242525 = 840947) (by norm_num)
theorem B3782645 : Blo 1327482 3782645 := bbase (se 5 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 3782645 = 354623) (by norm_num)
theorem B2988053 : Blo 1327482 2988053 := bbase (se 6 (by rfl) ⟨70032, by rfl⟩ : syracuseStep 2988053 = 140065) (by norm_num)
theorem B2127917 : Blo 1327482 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B2242613 : Blo 1327482 2242613 := bbase (se 5 (by rfl) ⟨105122, by rfl⟩ : syracuseStep 2242613 = 210245) (by norm_num)
theorem B2988125 : Blo 1327482 2988125 := bbase (se 3 (by rfl) ⟨560273, by rfl⟩ : syracuseStep 2988125 = 1120547) (by norm_num)
theorem B2988197 : Blo 1327482 2988197 := bbase (se 4 (by rfl) ⟨280143, by rfl⟩ : syracuseStep 2988197 = 560287) (by norm_num)
theorem B2521277 : Blo 1327482 2521277 := bbase (se 3 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 2521277 = 945479) (by norm_num)
theorem B2988269 : Blo 1327482 2988269 := bbase (se 3 (by rfl) ⟨560300, by rfl⟩ : syracuseStep 2988269 = 1120601) (by norm_num)
theorem B1595641 : Blo 1327482 1595641 := bbase (se 2 (by rfl) ⟨598365, by rfl⟩ : syracuseStep 1595641 = 1196731) (by norm_num)
theorem B2988341 : Blo 1327482 2988341 := bbase (se 5 (by rfl) ⟨140078, by rfl⟩ : syracuseStep 2988341 = 280157) (by norm_num)
theorem B17733973 : Blo 1327482 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B1513837 : Blo 1327482 1513837 := bbase (se 3 (by rfl) ⟨283844, by rfl⟩ : syracuseStep 1513837 = 567689) (by norm_num)
theorem B2988413 : Blo 1327482 2988413 := bbase (se 3 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 2988413 = 1120655) (by norm_num)
theorem B2988485 : Blo 1327482 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B1595857 : Blo 1327482 1595857 := bbase (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) (by norm_num)
theorem B3791333 : Blo 1327482 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B2128373 : Blo 1327482 2128373 := bbase (se 5 (by rfl) ⟨99767, by rfl⟩ : syracuseStep 2128373 = 199535) (by norm_num)
theorem B1890821 : Blo 1327482 1890821 := bbase (se 4 (by rfl) ⟨177264, by rfl⟩ : syracuseStep 1890821 = 354529) (by norm_num)
theorem B2988557 : Blo 1327482 2988557 := bbase (se 3 (by rfl) ⟨560354, by rfl⟩ : syracuseStep 2988557 = 1120709) (by norm_num)
theorem B15120917 : Blo 1327482 15120917 := bbase (se 6 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 15120917 = 708793) (by norm_num)
theorem B6724133 : Blo 1327482 6724133 := bbase (se 4 (by rfl) ⟨630387, by rfl⟩ : syracuseStep 6724133 = 1260775) (by norm_num)
theorem B2988629 : Blo 1327482 2988629 := bbase (se 8 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 2988629 = 35023) (by norm_num)
theorem B1890901 : Blo 1327482 1890901 := bbase (se 8 (by rfl) ⟨11079, by rfl⟩ : syracuseStep 1890901 = 22159) (by norm_num)
theorem B2988701 : Blo 1327482 2988701 := bbase (se 3 (by rfl) ⟨560381, by rfl⟩ : syracuseStep 2988701 = 1120763) (by norm_num)
theorem B1891021 : Blo 1327482 1891021 := bbase (se 3 (by rfl) ⟨354566, by rfl⟩ : syracuseStep 1891021 = 709133) (by norm_num)
theorem B12761813 : Blo 1327482 12761813 := bbase (se 7 (by rfl) ⟨149552, by rfl⟩ : syracuseStep 12761813 = 299105) (by norm_num)
theorem B2988773 : Blo 1327482 2988773 := bbase (se 4 (by rfl) ⟨280197, by rfl⟩ : syracuseStep 2988773 = 560395) (by norm_num)
theorem B1891117 : Blo 1327482 1891117 := bbase (se 3 (by rfl) ⟨354584, by rfl⟩ : syracuseStep 1891117 = 709169) (by norm_num)
theorem B2988845 : Blo 1327482 2988845 := bbase (se 3 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 2988845 = 1120817) (by norm_num)
theorem B2693957 : Blo 1327482 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B17496917 : Blo 1327482 17496917 := bbase (se 9 (by rfl) ⟨51260, by rfl⟩ : syracuseStep 17496917 = 102521) (by norm_num)
theorem B2988917 : Blo 1327482 2988917 := bbase (se 5 (by rfl) ⟨140105, by rfl⟩ : syracuseStep 2988917 = 280211) (by norm_num)
theorem B5110661 : Blo 1327482 5110661 := bbase (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) (by norm_num)
theorem B2522029 : Blo 1327482 2522029 := bbase (se 3 (by rfl) ⟨472880, by rfl⟩ : syracuseStep 2522029 = 945761) (by norm_num)
theorem B2988989 : Blo 1327482 2988989 := bbase (se 3 (by rfl) ⟨560435, by rfl⟩ : syracuseStep 2988989 = 1120871) (by norm_num)
theorem B2989061 : Blo 1327482 2989061 := bbase (se 4 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 2989061 = 560449) (by norm_num)
theorem B7207957 : Blo 1327482 7207957 := bbase (se 6 (by rfl) ⟨168936, by rfl⟩ : syracuseStep 7207957 = 337873) (by norm_num)
theorem B1596457 : Blo 1327482 1596457 := bbase (se 2 (by rfl) ⟨598671, by rfl⟩ : syracuseStep 1596457 = 1197343) (by norm_num)
theorem B5676085 : Blo 1327482 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B2522173 : Blo 1327482 2522173 := bbase (se 3 (by rfl) ⟨472907, by rfl⟩ : syracuseStep 2522173 = 945815) (by norm_num)
theorem B2989133 : Blo 1327482 2989133 := bbase (se 3 (by rfl) ⟨560462, by rfl⟩ : syracuseStep 2989133 = 1120925) (by norm_num)
theorem B2104421 : Blo 1327482 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B3939445 : Blo 1327482 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B2989205 : Blo 1327482 2989205 := bbase (se 6 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 2989205 = 140119) (by norm_num)
theorem B3783829 : Blo 1327482 3783829 := bbase (se 6 (by rfl) ⟨88683, by rfl⟩ : syracuseStep 3783829 = 177367) (by norm_num)
theorem B2989277 : Blo 1327482 2989277 := bbase (se 3 (by rfl) ⟨560489, by rfl⟩ : syracuseStep 2989277 = 1120979) (by norm_num)
theorem B2522333 : Blo 1327482 2522333 := bbase (se 3 (by rfl) ⟨472937, by rfl⟩ : syracuseStep 2522333 = 945875) (by norm_num)
theorem B1891613 : Blo 1327482 1891613 := bbase (se 3 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 1891613 = 709355) (by norm_num)
theorem B2989349 : Blo 1327482 2989349 := bbase (se 4 (by rfl) ⟨280251, by rfl⟩ : syracuseStep 2989349 = 560503) (by norm_num)
theorem B3783989 : Blo 1327482 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B4480325 : Blo 1327482 4480325 := bbase (se 4 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 4480325 = 840061) (by norm_num)
theorem B6380869 : Blo 1327482 6380869 := bbase (se 4 (by rfl) ⟨598206, by rfl⟩ : syracuseStep 6380869 = 1196413) (by norm_num)
theorem B4545877 : Blo 1327482 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B2989421 : Blo 1327482 2989421 := bbase (se 3 (by rfl) ⟨560516, by rfl⟩ : syracuseStep 2989421 = 1121033) (by norm_num)
theorem B2522477 : Blo 1327482 2522477 := bbase (se 3 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 2522477 = 945929) (by norm_num)
theorem B2989493 : Blo 1327482 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B1916365 : Blo 1327482 1916365 := bbase (se 3 (by rfl) ⟨359318, by rfl⟩ : syracuseStep 1916365 = 718637) (by norm_num)
theorem B3071461 : Blo 1327482 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B2989565 : Blo 1327482 2989565 := bbase (se 3 (by rfl) ⟨560543, by rfl⟩ : syracuseStep 2989565 = 1121087) (by norm_num)
theorem B3784229 : Blo 1327482 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B2989637 : Blo 1327482 2989637 := bbase (se 4 (by rfl) ⟨280278, by rfl⟩ : syracuseStep 2989637 = 560557) (by norm_num)
theorem B2555477 : Blo 1327482 2555477 := bbase (se 8 (by rfl) ⟨14973, by rfl⟩ : syracuseStep 2555477 = 29947) (by norm_num)
theorem B13631093 : Blo 1327482 13631093 := bbase (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) (by norm_num)
theorem B2989709 : Blo 1327482 2989709 := bbase (se 3 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 2989709 = 1121141) (by norm_num)
theorem B2522765 : Blo 1327482 2522765 := bbase (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) (by norm_num)
theorem B2989781 : Blo 1327482 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B3784421 : Blo 1327482 3784421 := bbase (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) (by norm_num)
theorem B4480757 : Blo 1327482 4480757 := bbase (se 5 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 4480757 = 420071) (by norm_num)
theorem B2989853 : Blo 1327482 2989853 := bbase (se 3 (by rfl) ⟨560597, by rfl⟩ : syracuseStep 2989853 = 1121195) (by norm_num)
theorem B2522917 : Blo 1327482 2522917 := bbase (se 4 (by rfl) ⟨236523, by rfl⟩ : syracuseStep 2522917 = 473047) (by norm_num)
theorem B6725429 : Blo 1327482 6725429 := bbase (se 5 (by rfl) ⟨315254, by rfl⟩ : syracuseStep 6725429 = 630509) (by norm_num)
theorem B1892165 : Blo 1327482 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B2989925 : Blo 1327482 2989925 := bbase (se 4 (by rfl) ⟨280305, by rfl⟩ : syracuseStep 2989925 = 560611) (by norm_num)
theorem B2334629 : Blo 1327482 2334629 := bbase (se 4 (by rfl) ⟨218871, by rfl⟩ : syracuseStep 2334629 = 437743) (by norm_num)
theorem B2989997 : Blo 1327482 2989997 := bbase (se 3 (by rfl) ⟨560624, by rfl⟩ : syracuseStep 2989997 = 1121249) (by norm_num)
theorem B2990069 : Blo 1327482 2990069 := bbase (se 5 (by rfl) ⟨140159, by rfl⟩ : syracuseStep 2990069 = 280319) (by norm_num)
theorem B4481027 : Blo 1327482 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B7561349 : Blo 1327482 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B5611789 : Blo 1327482 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B4481297 : Blo 1327482 4481297 := bstep (se 2 (by rfl) ⟨1680486, by rfl⟩ : syracuseStep 4481297 = 3360973) B3360973
theorem B1794371 : Blo 1327482 1794371 := bstep (se 1 (by rfl) ⟨1345778, by rfl⟩ : syracuseStep 1794371 = 2691557) B2691557
theorem B1327491 : Blo 1327482 1327491 := bstep (se 1 (by rfl) ⟨995618, by rfl⟩ : syracuseStep 1327491 = 1991237) B1991237
theorem B1327507 : Blo 1327482 1327507 := bstep (se 1 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 1327507 = 1991261) B1991261
theorem B1327523 : Blo 1327482 1327523 := bstep (se 1 (by rfl) ⟨995642, by rfl⟩ : syracuseStep 1327523 = 1991285) B1991285
theorem B1327539 : Blo 1327482 1327539 := bstep (se 1 (by rfl) ⟨995654, by rfl⟩ : syracuseStep 1327539 = 1991309) B1991309
theorem B1327555 : Blo 1327482 1327555 := bstep (se 1 (by rfl) ⟨995666, by rfl⟩ : syracuseStep 1327555 = 1991333) B1991333
theorem B1327571 : Blo 1327482 1327571 := bstep (se 1 (by rfl) ⟨995678, by rfl⟩ : syracuseStep 1327571 = 1991357) B1991357
theorem B1327587 : Blo 1327482 1327587 := bstep (se 1 (by rfl) ⟨995690, by rfl⟩ : syracuseStep 1327587 = 1991381) B1991381
theorem B1327603 : Blo 1327482 1327603 := bstep (se 1 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 1327603 = 1991405) B1991405
theorem B1327619 : Blo 1327482 1327619 := bstep (se 1 (by rfl) ⟨995714, by rfl⟩ : syracuseStep 1327619 = 1991429) B1991429
theorem B1327635 : Blo 1327482 1327635 := bstep (se 1 (by rfl) ⟨995726, by rfl⟩ : syracuseStep 1327635 = 1991453) B1991453
theorem B1327651 : Blo 1327482 1327651 := bstep (se 1 (by rfl) ⟨995738, by rfl⟩ : syracuseStep 1327651 = 1991477) B1991477
theorem B1327667 : Blo 1327482 1327667 := bstep (se 1 (by rfl) ⟨995750, by rfl⟩ : syracuseStep 1327667 = 1991501) B1991501
theorem B1327683 : Blo 1327482 1327683 := bstep (se 1 (by rfl) ⟨995762, by rfl⟩ : syracuseStep 1327683 = 1991525) B1991525
theorem B1991249 : Blo 1327482 1991249 := bstep (se 2 (by rfl) ⟨746718, by rfl⟩ : syracuseStep 1991249 = 1493437) B1493437
theorem B1327699 : Blo 1327482 1327699 := bstep (se 1 (by rfl) ⟨995774, by rfl⟩ : syracuseStep 1327699 = 1991549) B1991549
theorem B1991267 : Blo 1327482 1991267 := bstep (se 1 (by rfl) ⟨1493450, by rfl⟩ : syracuseStep 1991267 = 2986901) B2986901
theorem B1327715 : Blo 1327482 1327715 := bstep (se 1 (by rfl) ⟨995786, by rfl⟩ : syracuseStep 1327715 = 1991573) B1991573
theorem B1327731 : Blo 1327482 1327731 := bstep (se 1 (by rfl) ⟨995798, by rfl⟩ : syracuseStep 1327731 = 1991597) B1991597
theorem B1991297 : Blo 1327482 1991297 := bstep (se 2 (by rfl) ⟨746736, by rfl⟩ : syracuseStep 1991297 = 1493473) B1493473
theorem B1327747 : Blo 1327482 1327747 := bstep (se 1 (by rfl) ⟨995810, by rfl⟩ : syracuseStep 1327747 = 1991621) B1991621
theorem B1991315 : Blo 1327482 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B1327763 : Blo 1327482 1327763 := bstep (se 1 (by rfl) ⟨995822, by rfl⟩ : syracuseStep 1327763 = 1991645) B1991645
theorem B1327779 : Blo 1327482 1327779 := bstep (se 1 (by rfl) ⟨995834, by rfl⟩ : syracuseStep 1327779 = 1991669) B1991669
theorem B1991345 : Blo 1327482 1991345 := bstep (se 2 (by rfl) ⟨746754, by rfl⟩ : syracuseStep 1991345 = 1493509) B1493509
theorem B1327795 : Blo 1327482 1327795 := bstep (se 1 (by rfl) ⟨995846, by rfl⟩ : syracuseStep 1327795 = 1991693) B1991693
theorem B1794739 : Blo 1327482 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B1991363 : Blo 1327482 1991363 := bstep (se 1 (by rfl) ⟨1493522, by rfl⟩ : syracuseStep 1991363 = 2987045) B2987045
theorem B1327811 : Blo 1327482 1327811 := bstep (se 1 (by rfl) ⟨995858, by rfl⟩ : syracuseStep 1327811 = 1991717) B1991717
theorem B1327827 : Blo 1327482 1327827 := bstep (se 1 (by rfl) ⟨995870, by rfl⟩ : syracuseStep 1327827 = 1991741) B1991741
theorem B1991393 : Blo 1327482 1991393 := bstep (se 2 (by rfl) ⟨746772, by rfl⟩ : syracuseStep 1991393 = 1493545) B1493545
theorem B1327843 : Blo 1327482 1327843 := bstep (se 1 (by rfl) ⟨995882, by rfl⟩ : syracuseStep 1327843 = 1991765) B1991765
theorem B1991411 : Blo 1327482 1991411 := bstep (se 1 (by rfl) ⟨1493558, by rfl⟩ : syracuseStep 1991411 = 2987117) B2987117
theorem B1327859 : Blo 1327482 1327859 := bstep (se 1 (by rfl) ⟨995894, by rfl⟩ : syracuseStep 1327859 = 1991789) B1991789
theorem B1327875 : Blo 1327482 1327875 := bstep (se 1 (by rfl) ⟨995906, by rfl⟩ : syracuseStep 1327875 = 1991813) B1991813
theorem B1991441 : Blo 1327482 1991441 := bstep (se 2 (by rfl) ⟨746790, by rfl⟩ : syracuseStep 1991441 = 1493581) B1493581
theorem B1327891 : Blo 1327482 1327891 := bstep (se 1 (by rfl) ⟨995918, by rfl⟩ : syracuseStep 1327891 = 1991837) B1991837
theorem B1991459 : Blo 1327482 1991459 := bstep (se 1 (by rfl) ⟨1493594, by rfl⟩ : syracuseStep 1991459 = 2987189) B2987189
theorem B1327907 : Blo 1327482 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B4481837 : Blo 1327482 4481837 := bstep (se 3 (by rfl) ⟨840344, by rfl⟩ : syracuseStep 4481837 = 1680689) B1680689
theorem B1327923 : Blo 1327482 1327923 := bstep (se 1 (by rfl) ⟨995942, by rfl⟩ : syracuseStep 1327923 = 1991885) B1991885
theorem B1991489 : Blo 1327482 1991489 := bstep (se 2 (by rfl) ⟨746808, by rfl⟩ : syracuseStep 1991489 = 1493617) B1493617
theorem B1327939 : Blo 1327482 1327939 := bstep (se 1 (by rfl) ⟨995954, by rfl⟩ : syracuseStep 1327939 = 1991909) B1991909
theorem B1991507 : Blo 1327482 1991507 := bstep (se 1 (by rfl) ⟨1493630, by rfl⟩ : syracuseStep 1991507 = 2987261) B2987261
theorem B1327955 : Blo 1327482 1327955 := bstep (se 1 (by rfl) ⟨995966, by rfl⟩ : syracuseStep 1327955 = 1991933) B1991933
theorem B4481891 : Blo 1327482 4481891 := bstep (se 1 (by rfl) ⟨3361418, by rfl⟩ : syracuseStep 4481891 = 6722837) B6722837
theorem B1327971 : Blo 1327482 1327971 := bstep (se 1 (by rfl) ⟨995978, by rfl⟩ : syracuseStep 1327971 = 1991957) B1991957
theorem B1991537 : Blo 1327482 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B1327987 : Blo 1327482 1327987 := bstep (se 1 (by rfl) ⟨995990, by rfl⟩ : syracuseStep 1327987 = 1991981) B1991981
theorem B1680259 : Blo 1327482 1680259 := bstep (se 1 (by rfl) ⟨1260194, by rfl⟩ : syracuseStep 1680259 = 2520389) B2520389
theorem B1991555 : Blo 1327482 1991555 := bstep (se 1 (by rfl) ⟨1493666, by rfl⟩ : syracuseStep 1991555 = 2987333) B2987333
theorem B1328003 : Blo 1327482 1328003 := bstep (se 1 (by rfl) ⟨996002, by rfl⟩ : syracuseStep 1328003 = 1992005) B1992005
theorem B1328019 : Blo 1327482 1328019 := bstep (se 1 (by rfl) ⟨996014, by rfl⟩ : syracuseStep 1328019 = 1992029) B1992029
theorem B1991585 : Blo 1327482 1991585 := bstep (se 2 (by rfl) ⟨746844, by rfl⟩ : syracuseStep 1991585 = 1493689) B1493689
theorem B1328035 : Blo 1327482 1328035 := bstep (se 1 (by rfl) ⟨996026, by rfl⟩ : syracuseStep 1328035 = 1992053) B1992053
theorem B6726563 : Blo 1327482 6726563 := bstep (se 1 (by rfl) ⟨5044922, by rfl⟩ : syracuseStep 6726563 = 10089845) B10089845
theorem B1991603 : Blo 1327482 1991603 := bstep (se 1 (by rfl) ⟨1493702, by rfl⟩ : syracuseStep 1991603 = 2987405) B2987405
theorem B1328051 : Blo 1327482 1328051 := bstep (se 1 (by rfl) ⟨996038, by rfl⟩ : syracuseStep 1328051 = 1992077) B1992077
theorem B2835395 : Blo 1327482 2835395 := bstep (se 1 (by rfl) ⟨2126546, by rfl⟩ : syracuseStep 2835395 = 4253093) B4253093
theorem B1328067 : Blo 1327482 1328067 := bstep (se 1 (by rfl) ⟨996050, by rfl⟩ : syracuseStep 1328067 = 1992101) B1992101
theorem B1991633 : Blo 1327482 1991633 := bstep (se 2 (by rfl) ⟨746862, by rfl⟩ : syracuseStep 1991633 = 1493725) B1493725
theorem B1328083 : Blo 1327482 1328083 := bstep (se 1 (by rfl) ⟨996062, by rfl⟩ : syracuseStep 1328083 = 1992125) B1992125
theorem B1680355 : Blo 1327482 1680355 := bstep (se 1 (by rfl) ⟨1260266, by rfl⟩ : syracuseStep 1680355 = 2520533) B2520533
theorem B1991651 : Blo 1327482 1991651 := bstep (se 1 (by rfl) ⟨1493738, by rfl⟩ : syracuseStep 1991651 = 2987477) B2987477
theorem B1328099 : Blo 1327482 1328099 := bstep (se 1 (by rfl) ⟨996074, by rfl⟩ : syracuseStep 1328099 = 1992149) B1992149
theorem B1328115 : Blo 1327482 1328115 := bstep (se 1 (by rfl) ⟨996086, by rfl⟩ : syracuseStep 1328115 = 1992173) B1992173
theorem B1991681 : Blo 1327482 1991681 := bstep (se 2 (by rfl) ⟨746880, by rfl⟩ : syracuseStep 1991681 = 1493761) B1493761
theorem B1328131 : Blo 1327482 1328131 := bstep (se 1 (by rfl) ⟨996098, by rfl⟩ : syracuseStep 1328131 = 1992197) B1992197
theorem B1991699 : Blo 1327482 1991699 := bstep (se 1 (by rfl) ⟨1493774, by rfl⟩ : syracuseStep 1991699 = 2987549) B2987549
theorem B1328147 : Blo 1327482 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B1328163 : Blo 1327482 1328163 := bstep (se 1 (by rfl) ⟨996122, by rfl⟩ : syracuseStep 1328163 = 1992245) B1992245
theorem B1991729 : Blo 1327482 1991729 := bstep (se 2 (by rfl) ⟨746898, by rfl⟩ : syracuseStep 1991729 = 1493797) B1493797
theorem B1328179 : Blo 1327482 1328179 := bstep (se 1 (by rfl) ⟨996134, by rfl⟩ : syracuseStep 1328179 = 1992269) B1992269
theorem B1795123 : Blo 1327482 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B1991747 : Blo 1327482 1991747 := bstep (se 1 (by rfl) ⟨1493810, by rfl⟩ : syracuseStep 1991747 = 2987621) B2987621
theorem B1328195 : Blo 1327482 1328195 := bstep (se 1 (by rfl) ⟨996146, by rfl⟩ : syracuseStep 1328195 = 1992293) B1992293
theorem B1328211 : Blo 1327482 1328211 := bstep (se 1 (by rfl) ⟨996158, by rfl⟩ : syracuseStep 1328211 = 1992317) B1992317
theorem B1991777 : Blo 1327482 1991777 := bstep (se 2 (by rfl) ⟨746916, by rfl⟩ : syracuseStep 1991777 = 1493833) B1493833
theorem B1328227 : Blo 1327482 1328227 := bstep (se 1 (by rfl) ⟨996170, by rfl⟩ : syracuseStep 1328227 = 1992341) B1992341
theorem B1795171 : Blo 1327482 1795171 := bstep (se 1 (by rfl) ⟨1346378, by rfl⟩ : syracuseStep 1795171 = 2692757) B2692757
theorem B4482161 : Blo 1327482 4482161 := bstep (se 2 (by rfl) ⟨1680810, by rfl⟩ : syracuseStep 4482161 = 3361621) B3361621
theorem B1991795 : Blo 1327482 1991795 := bstep (se 1 (by rfl) ⟨1493846, by rfl⟩ : syracuseStep 1991795 = 2987693) B2987693
theorem B1328243 : Blo 1327482 1328243 := bstep (se 1 (by rfl) ⟨996182, by rfl⟩ : syracuseStep 1328243 = 1992365) B1992365
theorem B1328259 : Blo 1327482 1328259 := bstep (se 1 (by rfl) ⟨996194, by rfl⟩ : syracuseStep 1328259 = 1992389) B1992389
theorem B1991825 : Blo 1327482 1991825 := bstep (se 2 (by rfl) ⟨746934, by rfl⟩ : syracuseStep 1991825 = 1493869) B1493869
theorem B1328275 : Blo 1327482 1328275 := bstep (se 1 (by rfl) ⟨996206, by rfl⟩ : syracuseStep 1328275 = 1992413) B1992413
theorem B1991843 : Blo 1327482 1991843 := bstep (se 1 (by rfl) ⟨1493882, by rfl⟩ : syracuseStep 1991843 = 2987765) B2987765
theorem B1328291 : Blo 1327482 1328291 := bstep (se 1 (by rfl) ⟨996218, by rfl⟩ : syracuseStep 1328291 = 1992437) B1992437
theorem B1328307 : Blo 1327482 1328307 := bstep (se 1 (by rfl) ⟨996230, by rfl⟩ : syracuseStep 1328307 = 1992461) B1992461
theorem B1991873 : Blo 1327482 1991873 := bstep (se 2 (by rfl) ⟨746952, by rfl⟩ : syracuseStep 1991873 = 1493905) B1493905
theorem B1328323 : Blo 1327482 1328323 := bstep (se 1 (by rfl) ⟨996242, by rfl⟩ : syracuseStep 1328323 = 1992485) B1992485
theorem B1991891 : Blo 1327482 1991891 := bstep (se 1 (by rfl) ⟨1493918, by rfl⟩ : syracuseStep 1991891 = 2987837) B2987837
theorem B1328339 : Blo 1327482 1328339 := bstep (se 1 (by rfl) ⟨996254, by rfl⟩ : syracuseStep 1328339 = 1992509) B1992509
theorem B1328355 : Blo 1327482 1328355 := bstep (se 1 (by rfl) ⟨996266, by rfl⟩ : syracuseStep 1328355 = 1992533) B1992533
theorem B1991921 : Blo 1327482 1991921 := bstep (se 2 (by rfl) ⟨746970, by rfl⟩ : syracuseStep 1991921 = 1493941) B1493941
theorem B1328371 : Blo 1327482 1328371 := bstep (se 1 (by rfl) ⟨996278, by rfl⟩ : syracuseStep 1328371 = 1992557) B1992557
theorem B1991939 : Blo 1327482 1991939 := bstep (se 1 (by rfl) ⟨1493954, by rfl⟩ : syracuseStep 1991939 = 2987909) B2987909
theorem B1328387 : Blo 1327482 1328387 := bstep (se 1 (by rfl) ⟨996290, by rfl⟩ : syracuseStep 1328387 = 1992581) B1992581
theorem B10110221 : Blo 1327482 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B1328403 : Blo 1327482 1328403 := bstep (se 1 (by rfl) ⟨996302, by rfl⟩ : syracuseStep 1328403 = 1992605) B1992605
theorem B1991969 : Blo 1327482 1991969 := bstep (se 2 (by rfl) ⟨746988, by rfl⟩ : syracuseStep 1991969 = 1493977) B1493977
theorem B1328419 : Blo 1327482 1328419 := bstep (se 1 (by rfl) ⟨996314, by rfl⟩ : syracuseStep 1328419 = 1992629) B1992629
theorem B1991987 : Blo 1327482 1991987 := bstep (se 1 (by rfl) ⟨1493990, by rfl⟩ : syracuseStep 1991987 = 2987981) B2987981
theorem B1328435 : Blo 1327482 1328435 := bstep (se 1 (by rfl) ⟨996326, by rfl⟩ : syracuseStep 1328435 = 1992653) B1992653
theorem B1328451 : Blo 1327482 1328451 := bstep (se 1 (by rfl) ⟨996338, by rfl⟩ : syracuseStep 1328451 = 1992677) B1992677
theorem B1992017 : Blo 1327482 1992017 := bstep (se 2 (by rfl) ⟨747006, by rfl⟩ : syracuseStep 1992017 = 1494013) B1494013
theorem B1328467 : Blo 1327482 1328467 := bstep (se 1 (by rfl) ⟨996350, by rfl⟩ : syracuseStep 1328467 = 1992701) B1992701
theorem B1992035 : Blo 1327482 1992035 := bstep (se 1 (by rfl) ⟨1494026, by rfl⟩ : syracuseStep 1992035 = 2988053) B2988053
theorem B1328483 : Blo 1327482 1328483 := bstep (se 1 (by rfl) ⟨996362, by rfl⟩ : syracuseStep 1328483 = 1992725) B1992725
theorem B9610609 : Blo 1327482 9610609 := bstep (se 2 (by rfl) ⟨3603978, by rfl⟩ : syracuseStep 9610609 = 7207957) B7207957
theorem B1328499 : Blo 1327482 1328499 := bstep (se 1 (by rfl) ⟨996374, by rfl⟩ : syracuseStep 1328499 = 1992749) B1992749
theorem B1992065 : Blo 1327482 1992065 := bstep (se 2 (by rfl) ⟨747024, by rfl⟩ : syracuseStep 1992065 = 1494049) B1494049
theorem B1328515 : Blo 1327482 1328515 := bstep (se 1 (by rfl) ⟨996386, by rfl⟩ : syracuseStep 1328515 = 1992773) B1992773
theorem B1992083 : Blo 1327482 1992083 := bstep (se 1 (by rfl) ⟨1494062, by rfl⟩ : syracuseStep 1992083 = 2988125) B2988125
theorem B1328531 : Blo 1327482 1328531 := bstep (se 1 (by rfl) ⟨996398, by rfl⟩ : syracuseStep 1328531 = 1992797) B1992797
theorem B1328547 : Blo 1327482 1328547 := bstep (se 1 (by rfl) ⟨996410, by rfl⟩ : syracuseStep 1328547 = 1992821) B1992821
theorem B1992113 : Blo 1327482 1992113 := bstep (se 2 (by rfl) ⟨747042, by rfl⟩ : syracuseStep 1992113 = 1494085) B1494085
theorem B1328563 : Blo 1327482 1328563 := bstep (se 1 (by rfl) ⟨996422, by rfl⟩ : syracuseStep 1328563 = 1992845) B1992845
theorem B1992131 : Blo 1327482 1992131 := bstep (se 1 (by rfl) ⟨1494098, by rfl⟩ : syracuseStep 1992131 = 2988197) B2988197
theorem B1328579 : Blo 1327482 1328579 := bstep (se 1 (by rfl) ⟨996434, by rfl⟩ : syracuseStep 1328579 = 1992869) B1992869
theorem B1680851 : Blo 1327482 1680851 := bstep (se 1 (by rfl) ⟨1260638, by rfl⟩ : syracuseStep 1680851 = 2521277) B2521277
theorem B1328595 : Blo 1327482 1328595 := bstep (se 1 (by rfl) ⟨996446, by rfl⟩ : syracuseStep 1328595 = 1992893) B1992893
theorem B1992161 : Blo 1327482 1992161 := bstep (se 2 (by rfl) ⟨747060, by rfl⟩ : syracuseStep 1992161 = 1494121) B1494121
theorem B1328611 : Blo 1327482 1328611 := bstep (se 1 (by rfl) ⟨996458, by rfl⟩ : syracuseStep 1328611 = 1992917) B1992917
theorem B1992179 : Blo 1327482 1992179 := bstep (se 1 (by rfl) ⟨1494134, by rfl⟩ : syracuseStep 1992179 = 2988269) B2988269
theorem B1328627 : Blo 1327482 1328627 := bstep (se 1 (by rfl) ⟨996470, by rfl⟩ : syracuseStep 1328627 = 1992941) B1992941
theorem B1328643 : Blo 1327482 1328643 := bstep (se 1 (by rfl) ⟨996482, by rfl⟩ : syracuseStep 1328643 = 1992965) B1992965
theorem B2835985 : Blo 1327482 2835985 := bstep (se 2 (by rfl) ⟨1063494, by rfl⟩ : syracuseStep 2835985 = 2126989) B2126989
theorem B1992209 : Blo 1327482 1992209 := bstep (se 2 (by rfl) ⟨747078, by rfl⟩ : syracuseStep 1992209 = 1494157) B1494157
theorem B1328659 : Blo 1327482 1328659 := bstep (se 1 (by rfl) ⟨996494, by rfl⟩ : syracuseStep 1328659 = 1992989) B1992989
theorem B1992227 : Blo 1327482 1992227 := bstep (se 1 (by rfl) ⟨1494170, by rfl⟩ : syracuseStep 1992227 = 2988341) B2988341
theorem B1328675 : Blo 1327482 1328675 := bstep (se 1 (by rfl) ⟨996506, by rfl⟩ : syracuseStep 1328675 = 1993013) B1993013
theorem B3360305 : Blo 1327482 3360305 := bstep (se 2 (by rfl) ⟨1260114, by rfl⟩ : syracuseStep 3360305 = 2520229) B2520229
theorem B1328691 : Blo 1327482 1328691 := bstep (se 1 (by rfl) ⟨996518, by rfl⟩ : syracuseStep 1328691 = 1993037) B1993037
theorem B1992257 : Blo 1327482 1992257 := bstep (se 2 (by rfl) ⟨747096, by rfl⟩ : syracuseStep 1992257 = 1494193) B1494193
theorem B1328707 : Blo 1327482 1328707 := bstep (se 1 (by rfl) ⟨996530, by rfl⟩ : syracuseStep 1328707 = 1993061) B1993061
theorem B10085957 : Blo 1327482 10085957 := bstep (se 4 (by rfl) ⟨945558, by rfl⟩ : syracuseStep 10085957 = 1891117) B1891117
theorem B1992275 : Blo 1327482 1992275 := bstep (se 1 (by rfl) ⟨1494206, by rfl⟩ : syracuseStep 1992275 = 2988413) B2988413
theorem B1328723 : Blo 1327482 1328723 := bstep (se 1 (by rfl) ⟨996542, by rfl⟩ : syracuseStep 1328723 = 1993085) B1993085
theorem B1328739 : Blo 1327482 1328739 := bstep (se 1 (by rfl) ⟨996554, by rfl⟩ : syracuseStep 1328739 = 1993109) B1993109
theorem B1992305 : Blo 1327482 1992305 := bstep (se 2 (by rfl) ⟨747114, by rfl⟩ : syracuseStep 1992305 = 1494229) B1494229
theorem B1328755 : Blo 1327482 1328755 := bstep (se 1 (by rfl) ⟨996566, by rfl⟩ : syracuseStep 1328755 = 1993133) B1993133
theorem B1992323 : Blo 1327482 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B1328771 : Blo 1327482 1328771 := bstep (se 1 (by rfl) ⟨996578, by rfl⟩ : syracuseStep 1328771 = 1993157) B1993157
theorem B4482701 : Blo 1327482 4482701 := bstep (se 3 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 4482701 = 1681013) B1681013
theorem B1328787 : Blo 1327482 1328787 := bstep (se 1 (by rfl) ⟨996590, by rfl⟩ : syracuseStep 1328787 = 1993181) B1993181
theorem B1992353 : Blo 1327482 1992353 := bstep (se 2 (by rfl) ⟨747132, by rfl⟩ : syracuseStep 1992353 = 1494265) B1494265
theorem B1418915 : Blo 1327482 1418915 := bstep (se 1 (by rfl) ⟨1064186, by rfl⟩ : syracuseStep 1418915 = 2128373) B2128373
theorem B1328803 : Blo 1327482 1328803 := bstep (se 1 (by rfl) ⟨996602, by rfl⟩ : syracuseStep 1328803 = 1993205) B1993205
theorem B1992371 : Blo 1327482 1992371 := bstep (se 1 (by rfl) ⟨1494278, by rfl⟩ : syracuseStep 1992371 = 2988557) B2988557
theorem B1328819 : Blo 1327482 1328819 := bstep (se 1 (by rfl) ⟨996614, by rfl⟩ : syracuseStep 1328819 = 1993229) B1993229
theorem B4482755 : Blo 1327482 4482755 := bstep (se 1 (by rfl) ⟨3362066, by rfl⟩ : syracuseStep 4482755 = 6724133) B6724133
theorem B1328835 : Blo 1327482 1328835 := bstep (se 1 (by rfl) ⟨996626, by rfl⟩ : syracuseStep 1328835 = 1993253) B1993253
theorem B6727373 : Blo 1327482 6727373 := bstep (se 3 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 6727373 = 2522765) B2522765
theorem B1992401 : Blo 1327482 1992401 := bstep (se 2 (by rfl) ⟨747150, by rfl⟩ : syracuseStep 1992401 = 1494301) B1494301
theorem B1328851 : Blo 1327482 1328851 := bstep (se 1 (by rfl) ⟨996638, by rfl⟩ : syracuseStep 1328851 = 1993277) B1993277
theorem B1992419 : Blo 1327482 1992419 := bstep (se 1 (by rfl) ⟨1494314, by rfl⟩ : syracuseStep 1992419 = 2988629) B2988629
theorem B1328867 : Blo 1327482 1328867 := bstep (se 1 (by rfl) ⟨996650, by rfl⟩ : syracuseStep 1328867 = 1993301) B1993301
theorem B1328883 : Blo 1327482 1328883 := bstep (se 1 (by rfl) ⟨996662, by rfl⟩ : syracuseStep 1328883 = 1993325) B1993325
theorem B1992449 : Blo 1327482 1992449 := bstep (se 2 (by rfl) ⟨747168, by rfl⟩ : syracuseStep 1992449 = 1494337) B1494337
theorem B1328899 : Blo 1327482 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B3639053 : Blo 1327482 3639053 := bstep (se 3 (by rfl) ⟨682322, by rfl⟩ : syracuseStep 3639053 = 1364645) B1364645
theorem B1992467 : Blo 1327482 1992467 := bstep (se 1 (by rfl) ⟨1494350, by rfl⟩ : syracuseStep 1992467 = 2988701) B2988701
theorem B1328915 : Blo 1327482 1328915 := bstep (se 1 (by rfl) ⟨996686, by rfl⟩ : syracuseStep 1328915 = 1993373) B1993373
theorem B1328931 : Blo 1327482 1328931 := bstep (se 1 (by rfl) ⟨996698, by rfl⟩ : syracuseStep 1328931 = 1993397) B1993397
theorem B1992497 : Blo 1327482 1992497 := bstep (se 2 (by rfl) ⟨747186, by rfl⟩ : syracuseStep 1992497 = 1494373) B1494373
theorem B1328947 : Blo 1327482 1328947 := bstep (se 1 (by rfl) ⟨996710, by rfl⟩ : syracuseStep 1328947 = 1993421) B1993421
theorem B1992515 : Blo 1327482 1992515 := bstep (se 1 (by rfl) ⟨1494386, by rfl⟩ : syracuseStep 1992515 = 2988773) B2988773
theorem B1328963 : Blo 1327482 1328963 := bstep (se 1 (by rfl) ⟨996722, by rfl⟩ : syracuseStep 1328963 = 1993445) B1993445
theorem B1328979 : Blo 1327482 1328979 := bstep (se 1 (by rfl) ⟨996734, by rfl⟩ : syracuseStep 1328979 = 1993469) B1993469
theorem B1992545 : Blo 1327482 1992545 := bstep (se 2 (by rfl) ⟨747204, by rfl⟩ : syracuseStep 1992545 = 1494409) B1494409
theorem B5670755 : Blo 1327482 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B13633393 : Blo 1327482 13633393 := bstep (se 2 (by rfl) ⟨5112522, by rfl⟩ : syracuseStep 13633393 = 10225045) B10225045
theorem B1992563 : Blo 1327482 1992563 := bstep (se 1 (by rfl) ⟨1494422, by rfl⟩ : syracuseStep 1992563 = 2988845) B2988845
theorem B1992593 : Blo 1327482 1992593 := bstep (se 2 (by rfl) ⟨747222, by rfl⟩ : syracuseStep 1992593 = 1494445) B1494445
theorem B1992611 : Blo 1327482 1992611 := bstep (se 1 (by rfl) ⟨1494458, by rfl⟩ : syracuseStep 1992611 = 2988917) B2988917
theorem B1992641 : Blo 1327482 1992641 := bstep (se 2 (by rfl) ⟨747240, by rfl⟩ : syracuseStep 1992641 = 1494481) B1494481
theorem B4483025 : Blo 1327482 4483025 := bstep (se 2 (by rfl) ⟨1681134, by rfl⟩ : syracuseStep 4483025 = 3362269) B3362269
theorem B1992659 : Blo 1327482 1992659 := bstep (se 1 (by rfl) ⟨1494494, by rfl⟩ : syracuseStep 1992659 = 2988989) B2988989
theorem B4253681 : Blo 1327482 4253681 := bstep (se 2 (by rfl) ⟨1595130, by rfl⟩ : syracuseStep 4253681 = 3190261) B3190261
theorem B1992689 : Blo 1327482 1992689 := bstep (se 2 (by rfl) ⟨747258, by rfl⟩ : syracuseStep 1992689 = 1494517) B1494517
theorem B1992707 : Blo 1327482 1992707 := bstep (se 1 (by rfl) ⟨1494530, by rfl⟩ : syracuseStep 1992707 = 2989061) B2989061
theorem B1992737 : Blo 1327482 1992737 := bstep (se 2 (by rfl) ⟨747276, by rfl⟩ : syracuseStep 1992737 = 1494553) B1494553
theorem B1992755 : Blo 1327482 1992755 := bstep (se 1 (by rfl) ⟨1494566, by rfl⟩ : syracuseStep 1992755 = 2989133) B2989133
theorem B1992785 : Blo 1327482 1992785 := bstep (se 2 (by rfl) ⟨747294, by rfl⟩ : syracuseStep 1992785 = 1494589) B1494589
theorem B1992803 : Blo 1327482 1992803 := bstep (se 1 (by rfl) ⟨1494602, by rfl⟩ : syracuseStep 1992803 = 2989205) B2989205
theorem B2394211 : Blo 1327482 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B1992833 : Blo 1327482 1992833 := bstep (se 2 (by rfl) ⟨747312, by rfl⟩ : syracuseStep 1992833 = 1494625) B1494625
theorem B5384333 : Blo 1327482 5384333 := bstep (se 3 (by rfl) ⟨1009562, by rfl⟩ : syracuseStep 5384333 = 2019125) B2019125
theorem B1992851 : Blo 1327482 1992851 := bstep (se 1 (by rfl) ⟨1494638, by rfl⟩ : syracuseStep 1992851 = 2989277) B2989277
theorem B1681555 : Blo 1327482 1681555 := bstep (se 1 (by rfl) ⟨1261166, by rfl⟩ : syracuseStep 1681555 = 2522333) B2522333
theorem B1992881 : Blo 1327482 1992881 := bstep (se 2 (by rfl) ⟨747330, by rfl⟩ : syracuseStep 1992881 = 1494661) B1494661
theorem B1992899 : Blo 1327482 1992899 := bstep (se 1 (by rfl) ⟨1494674, by rfl⟩ : syracuseStep 1992899 = 2989349) B2989349
theorem B1992929 : Blo 1327482 1992929 := bstep (se 2 (by rfl) ⟨747348, by rfl⟩ : syracuseStep 1992929 = 1494697) B1494697
theorem B21547235 : Blo 1327482 21547235 := bstep (se 1 (by rfl) ⟨16160426, by rfl⟩ : syracuseStep 21547235 = 32320853) B32320853
theorem B1992947 : Blo 1327482 1992947 := bstep (se 1 (by rfl) ⟨1494710, by rfl⟩ : syracuseStep 1992947 = 2989421) B2989421
theorem B1681651 : Blo 1327482 1681651 := bstep (se 1 (by rfl) ⟨1261238, by rfl⟩ : syracuseStep 1681651 = 2522477) B2522477
theorem B16148749 : Blo 1327482 16148749 := bstep (se 3 (by rfl) ⟨3027890, by rfl⟩ : syracuseStep 16148749 = 6055781) B6055781
theorem B1992977 : Blo 1327482 1992977 := bstep (se 2 (by rfl) ⟨747366, by rfl⟩ : syracuseStep 1992977 = 1494733) B1494733
theorem B1992995 : Blo 1327482 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B1993025 : Blo 1327482 1993025 := bstep (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) B1494769
theorem B1993043 : Blo 1327482 1993043 := bstep (se 1 (by rfl) ⟨1494782, by rfl⟩ : syracuseStep 1993043 = 2989565) B2989565
theorem B10226033 : Blo 1327482 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B1993073 : Blo 1327482 1993073 := bstep (se 2 (by rfl) ⟨747402, by rfl⟩ : syracuseStep 1993073 = 1494805) B1494805
theorem B1993091 : Blo 1327482 1993091 := bstep (se 1 (by rfl) ⟨1494818, by rfl⟩ : syracuseStep 1993091 = 2989637) B2989637
theorem B40905101 : Blo 1327482 40905101 := bstep (se 3 (by rfl) ⟨7669706, by rfl⟩ : syracuseStep 40905101 = 15339413) B15339413
theorem B1993121 : Blo 1327482 1993121 := bstep (se 2 (by rfl) ⟨747420, by rfl⟩ : syracuseStep 1993121 = 1494841) B1494841
theorem B9087395 : Blo 1327482 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B1993139 : Blo 1327482 1993139 := bstep (se 1 (by rfl) ⟨1494854, by rfl⟩ : syracuseStep 1993139 = 2989709) B2989709
theorem B9570757 : Blo 1327482 9570757 := bstep (se 4 (by rfl) ⟨897258, by rfl⟩ : syracuseStep 9570757 = 1794517) B1794517
theorem B1993169 : Blo 1327482 1993169 := bstep (se 2 (by rfl) ⟨747438, by rfl⟩ : syracuseStep 1993169 = 1494877) B1494877
theorem B1993187 : Blo 1327482 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B4483565 : Blo 1327482 4483565 := bstep (se 3 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 4483565 = 1681337) B1681337
theorem B1493491 : Blo 1327482 1493491 := bstep (se 1 (by rfl) ⟨1120118, by rfl⟩ : syracuseStep 1493491 = 2240237) B2240237
theorem B1993217 : Blo 1327482 1993217 := bstep (se 2 (by rfl) ⟨747456, by rfl⟩ : syracuseStep 1993217 = 1494913) B1494913
theorem B4254221 : Blo 1327482 4254221 := bstep (se 3 (by rfl) ⟨797666, by rfl⟩ : syracuseStep 4254221 = 1595333) B1595333
theorem B3361297 : Blo 1327482 3361297 := bstep (se 2 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 3361297 = 2520973) B2520973
theorem B1993235 : Blo 1327482 1993235 := bstep (se 1 (by rfl) ⟨1494926, by rfl⟩ : syracuseStep 1993235 = 2989853) B2989853
theorem B4483619 : Blo 1327482 4483619 := bstep (se 1 (by rfl) ⟨3362714, by rfl⟩ : syracuseStep 4483619 = 6725429) B6725429
theorem B1993265 : Blo 1327482 1993265 := bstep (se 2 (by rfl) ⟨747474, by rfl⟩ : syracuseStep 1993265 = 1494949) B1494949
theorem B1993283 : Blo 1327482 1993283 := bstep (se 1 (by rfl) ⟨1494962, by rfl⟩ : syracuseStep 1993283 = 2989925) B2989925
theorem B1993313 : Blo 1327482 1993313 := bstep (se 2 (by rfl) ⟨747492, by rfl⟩ : syracuseStep 1993313 = 1494985) B1494985
theorem B1993331 : Blo 1327482 1993331 := bstep (se 1 (by rfl) ⟨1494998, by rfl⟩ : syracuseStep 1993331 = 2989997) B2989997
theorem B1493635 : Blo 1327482 1493635 := bstep (se 1 (by rfl) ⟨1120226, by rfl⟩ : syracuseStep 1493635 = 2240453) B2240453
theorem B1993361 : Blo 1327482 1993361 := bstep (se 2 (by rfl) ⟨747510, by rfl⟩ : syracuseStep 1993361 = 1495021) B1495021
theorem B1993379 : Blo 1327482 1993379 := bstep (se 1 (by rfl) ⟨1495034, by rfl⟩ : syracuseStep 1993379 = 2990069) B2990069
theorem B1993409 : Blo 1327482 1993409 := bstep (se 2 (by rfl) ⟨747528, by rfl⟩ : syracuseStep 1993409 = 1495057) B1495057
theorem B1993427 : Blo 1327482 1993427 := bstep (se 1 (by rfl) ⟨1495070, by rfl⟩ : syracuseStep 1993427 = 2990141) B2990141
theorem B1993457 : Blo 1327482 1993457 := bstep (se 2 (by rfl) ⟨747546, by rfl⟩ : syracuseStep 1993457 = 1495093) B1495093
theorem B1493779 : Blo 1327482 1493779 := bstep (se 1 (by rfl) ⟨1120334, by rfl⟩ : syracuseStep 1493779 = 2240669) B2240669
theorem B3361571 : Blo 1327482 3361571 := bstep (se 1 (by rfl) ⟨2521178, by rfl⟩ : syracuseStep 3361571 = 5042357) B5042357
theorem B4483889 : Blo 1327482 4483889 := bstep (se 2 (by rfl) ⟨1681458, by rfl⟩ : syracuseStep 4483889 = 3362917) B3362917
theorem B1493923 : Blo 1327482 1493923 := bstep (se 1 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 1493923 = 2240885) B2240885
theorem B3361763 : Blo 1327482 3361763 := bstep (se 1 (by rfl) ⟨2521322, by rfl⟩ : syracuseStep 3361763 = 5042645) B5042645
theorem B5041187 : Blo 1327482 5041187 := bstep (se 1 (by rfl) ⟨3780890, by rfl⟩ : syracuseStep 5041187 = 7561781) B7561781
theorem B7179299 : Blo 1327482 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B1494067 : Blo 1327482 1494067 := bstep (se 1 (by rfl) ⟨1120550, by rfl⟩ : syracuseStep 1494067 = 2241101) B2241101
theorem B13626467 : Blo 1327482 13626467 := bstep (se 1 (by rfl) ⟨10219850, by rfl⟩ : syracuseStep 13626467 = 20439701) B20439701
theorem B8629361 : Blo 1327482 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B23645297 : Blo 1327482 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B2018449 : Blo 1327482 2018449 := bstep (se 2 (by rfl) ⟨756918, by rfl⟩ : syracuseStep 2018449 = 1513837) B1513837
theorem B1494211 : Blo 1327482 1494211 := bstep (se 1 (by rfl) ⟨1120658, by rfl⟩ : syracuseStep 1494211 = 2241317) B2241317
theorem B11349233 : Blo 1327482 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B4484429 : Blo 1327482 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1494355 : Blo 1327482 1494355 := bstep (se 1 (by rfl) ⟨1120766, by rfl⟩ : syracuseStep 1494355 = 2241533) B2241533
theorem B4484483 : Blo 1327482 4484483 := bstep (se 1 (by rfl) ⟨3363362, by rfl⟩ : syracuseStep 4484483 = 6726725) B6726725
theorem B1494499 : Blo 1327482 1494499 := bstep (se 1 (by rfl) ⟨1120874, by rfl⟩ : syracuseStep 1494499 = 2241749) B2241749
theorem B1494643 : Blo 1327482 1494643 := bstep (se 1 (by rfl) ⟨1120982, by rfl⟩ : syracuseStep 1494643 = 2241965) B2241965
theorem B2240129 : Blo 1327482 2240129 := bstep (se 2 (by rfl) ⟨840048, by rfl⟩ : syracuseStep 2240129 = 1680097) B1680097
theorem B4484753 : Blo 1327482 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B2240257 : Blo 1327482 2240257 := bstep (se 2 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 2240257 = 1680193) B1680193
theorem B1494787 : Blo 1327482 1494787 := bstep (se 1 (by rfl) ⟨1121090, by rfl⟩ : syracuseStep 1494787 = 2242181) B2242181
theorem B2240291 : Blo 1327482 2240291 := bstep (se 1 (by rfl) ⟨1680218, by rfl⟩ : syracuseStep 2240291 = 3360437) B3360437
theorem B6721379 : Blo 1327482 6721379 := bstep (se 1 (by rfl) ⟨5041034, by rfl⟩ : syracuseStep 6721379 = 10082069) B10082069
theorem B6057827 : Blo 1327482 6057827 := bstep (se 1 (by rfl) ⟨4543370, by rfl⟩ : syracuseStep 6057827 = 9086741) B9086741
theorem B7565197 : Blo 1327482 7565197 := bstep (se 3 (by rfl) ⟨1418474, by rfl⟩ : syracuseStep 7565197 = 2836949) B2836949
theorem B3362705 : Blo 1327482 3362705 := bstep (se 2 (by rfl) ⟨1261014, by rfl⟩ : syracuseStep 3362705 = 2522029) B2522029
theorem B1494931 : Blo 1327482 1494931 := bstep (se 1 (by rfl) ⟨1121198, by rfl⟩ : syracuseStep 1494931 = 2242397) B2242397
theorem B2240419 : Blo 1327482 2240419 := bstep (se 1 (by rfl) ⟨1680314, by rfl⟩ : syracuseStep 2240419 = 3360629) B3360629
theorem B3362755 : Blo 1327482 3362755 := bstep (se 1 (by rfl) ⟨2522066, by rfl⟩ : syracuseStep 3362755 = 5044133) B5044133
theorem B2273233 : Blo 1327482 2273233 := bstep (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) B1704925
theorem B5042189 : Blo 1327482 5042189 := bstep (se 3 (by rfl) ⟨945410, by rfl⟩ : syracuseStep 5042189 = 1890821) B1890821
theorem B1495075 : Blo 1327482 1495075 := bstep (se 1 (by rfl) ⟨1121306, by rfl⟩ : syracuseStep 1495075 = 2242613) B2242613
theorem B2240561 : Blo 1327482 2240561 := bstep (se 2 (by rfl) ⟨840210, by rfl⟩ : syracuseStep 2240561 = 1680421) B1680421
theorem B3780685 : Blo 1327482 3780685 := bstep (se 3 (by rfl) ⟨708878, by rfl⟩ : syracuseStep 3780685 = 1417757) B1417757
theorem B3362897 : Blo 1327482 3362897 := bstep (se 2 (by rfl) ⟨1261086, by rfl⟩ : syracuseStep 3362897 = 2522173) B2522173
theorem B4485293 : Blo 1327482 4485293 := bstep (se 3 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 4485293 = 1681985) B1681985
theorem B2240689 : Blo 1327482 2240689 := bstep (se 2 (by rfl) ⟨840258, by rfl⟩ : syracuseStep 2240689 = 1680517) B1680517
theorem B2240723 : Blo 1327482 2240723 := bstep (se 1 (by rfl) ⟨1680542, by rfl⟩ : syracuseStep 2240723 = 3361085) B3361085
theorem B3780913 : Blo 1327482 3780913 := bstep (se 2 (by rfl) ⟨1417842, by rfl⟩ : syracuseStep 3780913 = 2835685) B2835685
theorem B2240851 : Blo 1327482 2240851 := bstep (se 1 (by rfl) ⟨1680638, by rfl⟩ : syracuseStep 2240851 = 3361277) B3361277
theorem B10080611 : Blo 1327482 10080611 := bstep (se 1 (by rfl) ⟨7560458, by rfl⟩ : syracuseStep 10080611 = 15120917) B15120917
theorem B8507825 : Blo 1327482 8507825 := bstep (se 2 (by rfl) ⟨3190434, by rfl⟩ : syracuseStep 8507825 = 6380869) B6380869
theorem B3781073 : Blo 1327482 3781073 := bstep (se 2 (by rfl) ⟨1417902, by rfl⟩ : syracuseStep 3781073 = 2835805) B2835805
theorem B2240993 : Blo 1327482 2240993 := bstep (se 2 (by rfl) ⟨840372, by rfl⟩ : syracuseStep 2240993 = 1680745) B1680745
theorem B8507875 : Blo 1327482 8507875 := bstep (se 1 (by rfl) ⟨6380906, by rfl⟩ : syracuseStep 8507875 = 12761813) B12761813
theorem B3781187 : Blo 1327482 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B3453521 : Blo 1327482 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B2241121 : Blo 1327482 2241121 := bstep (se 2 (by rfl) ⟨840420, by rfl⟩ : syracuseStep 2241121 = 1680841) B1680841
theorem B2241155 : Blo 1327482 2241155 := bstep (se 1 (by rfl) ⟨1680866, by rfl⟩ : syracuseStep 2241155 = 3361733) B3361733
theorem B6722189 : Blo 1327482 6722189 := bstep (se 3 (by rfl) ⟨1260410, by rfl⟩ : syracuseStep 6722189 = 2520821) B2520821
theorem B3191491 : Blo 1327482 3191491 := bstep (se 1 (by rfl) ⟨2393618, by rfl⟩ : syracuseStep 3191491 = 4787237) B4787237
theorem B2241283 : Blo 1327482 2241283 := bstep (se 1 (by rfl) ⟨1680962, by rfl⟩ : syracuseStep 2241283 = 3361925) B3361925
theorem B2986865 : Blo 1327482 2986865 := bstep (se 2 (by rfl) ⟨1120074, by rfl⟩ : syracuseStep 2986865 = 2240149) B2240149
theorem B3191665 : Blo 1327482 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B2986883 : Blo 1327482 2986883 := bstep (se 1 (by rfl) ⟨2240162, by rfl⟩ : syracuseStep 2986883 = 4480325) B4480325
theorem B2241425 : Blo 1327482 2241425 := bstep (se 2 (by rfl) ⟨840534, by rfl⟩ : syracuseStep 2241425 = 1681069) B1681069
theorem B2241553 : Blo 1327482 2241553 := bstep (se 2 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 2241553 = 1681165) B1681165
theorem B3363889 : Blo 1327482 3363889 := bstep (se 2 (by rfl) ⟨1261458, by rfl⟩ : syracuseStep 3363889 = 2522917) B2522917
theorem B2241587 : Blo 1327482 2241587 := bstep (se 1 (by rfl) ⟨1681190, by rfl⟩ : syracuseStep 2241587 = 3362381) B3362381
theorem B10228805 : Blo 1327482 10228805 := bstep (se 4 (by rfl) ⟨958950, by rfl⟩ : syracuseStep 10228805 = 1917901) B1917901
theorem B17011853 : Blo 1327482 17011853 := bstep (se 3 (by rfl) ⟨3189722, by rfl⟩ : syracuseStep 17011853 = 6379445) B6379445
theorem B2987153 : Blo 1327482 2987153 := bstep (se 2 (by rfl) ⟨1120182, by rfl⟩ : syracuseStep 2987153 = 2240365) B2240365
theorem B2987171 : Blo 1327482 2987171 := bstep (se 1 (by rfl) ⟨2240378, by rfl⟩ : syracuseStep 2987171 = 4480757) B4480757
theorem B2241715 : Blo 1327482 2241715 := bstep (se 1 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 2241715 = 3362573) B3362573
theorem B2520305 : Blo 1327482 2520305 := bstep (se 2 (by rfl) ⟨945114, by rfl⟩ : syracuseStep 2520305 = 1890229) B1890229
theorem B2241857 : Blo 1327482 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B2692433 : Blo 1327482 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B2127251 : Blo 1327482 2127251 := bstep (se 1 (by rfl) ⟨1595438, by rfl⟩ : syracuseStep 2127251 = 3190877) B3190877
theorem B2987441 : Blo 1327482 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B2241985 : Blo 1327482 2241985 := bstep (se 2 (by rfl) ⟨840744, by rfl⟩ : syracuseStep 2241985 = 1681489) B1681489
theorem B1594819 : Blo 1327482 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B2987459 : Blo 1327482 2987459 := bstep (se 1 (by rfl) ⟨2240594, by rfl⟩ : syracuseStep 2987459 = 4481189) B4481189
theorem B82900421 : Blo 1327482 82900421 := bstep (se 4 (by rfl) ⟨7771914, by rfl⟩ : syracuseStep 82900421 = 15543829) B15543829
theorem B5674445 : Blo 1327482 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B2242019 : Blo 1327482 2242019 := bstep (se 1 (by rfl) ⟨1681514, by rfl⟩ : syracuseStep 2242019 = 3363029) B3363029
theorem B5674481 : Blo 1327482 5674481 := bstep (se 2 (by rfl) ⟨2127930, by rfl⟩ : syracuseStep 5674481 = 4255861) B4255861
theorem B2127379 : Blo 1327482 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B3782189 : Blo 1327482 3782189 := bstep (se 3 (by rfl) ⟨709160, by rfl⟩ : syracuseStep 3782189 = 1418321) B1418321
theorem B2242147 : Blo 1327482 2242147 := bstep (se 1 (by rfl) ⟨1681610, by rfl⟩ : syracuseStep 2242147 = 3363221) B3363221
theorem B2127521 : Blo 1327482 2127521 := bstep (se 2 (by rfl) ⟨797820, by rfl⟩ : syracuseStep 2127521 = 1595641) B1595641
theorem B2987729 : Blo 1327482 2987729 := bstep (se 2 (by rfl) ⟨1120398, by rfl⟩ : syracuseStep 2987729 = 2240797) B2240797
theorem B2987747 : Blo 1327482 2987747 := bstep (se 1 (by rfl) ⟨2240810, by rfl⟩ : syracuseStep 2987747 = 4481621) B4481621
theorem B3782371 : Blo 1327482 3782371 := bstep (se 1 (by rfl) ⟨2836778, by rfl⟩ : syracuseStep 3782371 = 5673557) B5673557
theorem B2242289 : Blo 1327482 2242289 := bstep (se 2 (by rfl) ⟨840858, by rfl⟩ : syracuseStep 2242289 = 1681717) B1681717
theorem B5183281 : Blo 1327482 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B7567181 : Blo 1327482 7567181 := bstep (se 3 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 7567181 = 2837693) B2837693
theorem B2242417 : Blo 1327482 2242417 := bstep (se 2 (by rfl) ⟨840906, by rfl⟩ : syracuseStep 2242417 = 1681813) B1681813
theorem B3782531 : Blo 1327482 3782531 := bstep (se 1 (by rfl) ⟨2836898, by rfl⟩ : syracuseStep 3782531 = 5673797) B5673797
theorem B2242451 : Blo 1327482 2242451 := bstep (se 1 (by rfl) ⟨1681838, by rfl⟩ : syracuseStep 2242451 = 3363677) B3363677
theorem B14366645 : Blo 1327482 14366645 := bstep (se 5 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 14366645 = 1346873) B1346873
theorem B2127809 : Blo 1327482 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B21010373 : Blo 1327482 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B2988017 : Blo 1327482 2988017 := bstep (se 2 (by rfl) ⟨1120506, by rfl⟩ : syracuseStep 2988017 = 2241013) B2241013
theorem B2988035 : Blo 1327482 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B2242579 : Blo 1327482 2242579 := bstep (se 1 (by rfl) ⟨1681934, by rfl⟩ : syracuseStep 2242579 = 3363869) B3363869
theorem B7280675 : Blo 1327482 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B4544561 : Blo 1327482 4544561 := bstep (se 2 (by rfl) ⟨1704210, by rfl⟩ : syracuseStep 4544561 = 3408421) B3408421
theorem B5044301 : Blo 1327482 5044301 := bstep (se 3 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 5044301 = 1891613) B1891613
theorem B2521201 : Blo 1327482 2521201 := bstep (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) B1890901
theorem B2521361 : Blo 1327482 2521361 := bstep (se 2 (by rfl) ⟨945510, by rfl⟩ : syracuseStep 2521361 = 1891021) B1891021
theorem B2988305 : Blo 1327482 2988305 := bstep (se 2 (by rfl) ⟨1120614, by rfl⟩ : syracuseStep 2988305 = 2241229) B2241229
theorem B2988323 : Blo 1327482 2988323 := bstep (se 1 (by rfl) ⟨2241242, by rfl⟩ : syracuseStep 2988323 = 4482485) B4482485
theorem B1890707 : Blo 1327482 1890707 := bstep (se 1 (by rfl) ⟨1418030, by rfl⟩ : syracuseStep 1890707 = 2836061) B2836061
theorem B2988593 : Blo 1327482 2988593 := bstep (se 2 (by rfl) ⟨1120722, by rfl⟩ : syracuseStep 2988593 = 2241445) B2241445
theorem B2988611 : Blo 1327482 2988611 := bstep (se 1 (by rfl) ⟨2241458, by rfl⟩ : syracuseStep 2988611 = 4482917) B4482917
theorem B2521763 : Blo 1327482 2521763 := bstep (se 1 (by rfl) ⟨1891322, by rfl⟩ : syracuseStep 2521763 = 3782645) B3782645
theorem B2128609 : Blo 1327482 2128609 := bstep (se 2 (by rfl) ⟨798228, by rfl⟩ : syracuseStep 2128609 = 1596457) B1596457
theorem B2874097 : Blo 1327482 2874097 := bstep (se 2 (by rfl) ⟨1077786, by rfl⟩ : syracuseStep 2874097 = 2155573) B2155573
theorem B7568113 : Blo 1327482 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B8510285 : Blo 1327482 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B2988881 : Blo 1327482 2988881 := bstep (se 2 (by rfl) ⟨1120830, by rfl⟩ : syracuseStep 2988881 = 2241661) B2241661
theorem B2988899 : Blo 1327482 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B5045105 : Blo 1327482 5045105 := bstep (se 2 (by rfl) ⟨1891914, by rfl⟩ : syracuseStep 5045105 = 3783829) B3783829
theorem B3783601 : Blo 1327482 3783601 := bstep (se 2 (by rfl) ⟨1418850, by rfl⟩ : syracuseStep 3783601 = 2837701) B2837701
theorem B1891345 : Blo 1327482 1891345 := bstep (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) B1418509
theorem B2989169 : Blo 1327482 2989169 := bstep (se 2 (by rfl) ⟨1120938, by rfl⟩ : syracuseStep 2989169 = 2241877) B2241877
theorem B6061169 : Blo 1327482 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B1891459 : Blo 1327482 1891459 := bstep (se 1 (by rfl) ⟨1418594, by rfl⟩ : syracuseStep 1891459 = 2837189) B2837189
theorem B2989187 : Blo 1327482 2989187 := bstep (se 1 (by rfl) ⟨2241890, by rfl⟩ : syracuseStep 2989187 = 4483781) B4483781
theorem B11664611 : Blo 1327482 11664611 := bstep (se 1 (by rfl) ⟨8748458, by rfl⟩ : syracuseStep 11664611 = 17496917) B17496917
theorem B3407107 : Blo 1327482 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B10091789 : Blo 1327482 10091789 := bstep (se 3 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 10091789 = 3784421) B3784421
theorem B2555153 : Blo 1327482 2555153 := bstep (se 2 (by rfl) ⟨958182, by rfl⟩ : syracuseStep 2555153 = 1916365) B1916365
theorem B4095281 : Blo 1327482 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B2989457 : Blo 1327482 2989457 := bstep (se 2 (by rfl) ⟨1121046, by rfl⟩ : syracuseStep 2989457 = 2242093) B2242093
theorem B2989475 : Blo 1327482 2989475 := bstep (se 1 (by rfl) ⟨2242106, by rfl⟩ : syracuseStep 2989475 = 4484213) B4484213
theorem B4480433 : Blo 1327482 4480433 := bstep (se 2 (by rfl) ⟨1680162, by rfl⟩ : syracuseStep 4480433 = 3360325) B3360325
theorem B6725105 : Blo 1327482 6725105 := bstep (se 2 (by rfl) ⟨2521914, by rfl⟩ : syracuseStep 6725105 = 5043829) B5043829
theorem B7183885 : Blo 1327482 7183885 := bstep (se 3 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 7183885 = 2693957) B2693957
theorem B5045773 : Blo 1327482 5045773 := bstep (se 3 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 5045773 = 1892165) B1892165
theorem B2522659 : Blo 1327482 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B12770885 : Blo 1327482 12770885 := bstep (se 4 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 12770885 = 2394541) B2394541
theorem B2989745 : Blo 1327482 2989745 := bstep (se 2 (by rfl) ⟨1121154, by rfl⟩ : syracuseStep 2989745 = 2242309) B2242309
theorem B2989763 : Blo 1327482 2989763 := bstep (se 1 (by rfl) ⟨2242322, by rfl⟩ : syracuseStep 2989763 = 4484645) B4484645
theorem B2522819 : Blo 1327482 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B1703651 : Blo 1327482 1703651 := bstep (se 1 (by rfl) ⟨1277738, by rfl⟩ : syracuseStep 1703651 = 2555477) B2555477
theorem B6225677 : Blo 1327482 6225677 := bstep (se 3 (by rfl) ⟨1167314, by rfl⟩ : syracuseStep 6225677 = 2334629) B2334629
theorem B4480973 : Blo 1327482 4480973 := bstep (se 3 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 4480973 = 1680365) B1680365
theorem B2990033 : Blo 1327482 2990033 := bstep (se 2 (by rfl) ⟨1121262, by rfl⟩ : syracuseStep 2990033 = 2242525) B2242525
theorem B2990051 : Blo 1327482 2990051 := bstep (se 1 (by rfl) ⟨2242538, by rfl⟩ : syracuseStep 2990051 = 4485077) B4485077
theorem B2990105 : Blo 1327482 2990105 := bstep (se 2 (by rfl) ⟨1121289, by rfl⟩ : syracuseStep 2990105 = 2242579) B2242579
theorem B2990195 : Blo 1327482 2990195 := bstep (se 1 (by rfl) ⟨2242646, by rfl⟩ : syracuseStep 2990195 = 4485293) B4485293
theorem B1327499 : Blo 1327482 1327499 := bstep (se 1 (by rfl) ⟨995624, by rfl⟩ : syracuseStep 1327499 = 1991249) B1991249
theorem B1327511 : Blo 1327482 1327511 := bstep (se 1 (by rfl) ⟨995633, by rfl⟩ : syracuseStep 1327511 = 1991267) B1991267
theorem B1327531 : Blo 1327482 1327531 := bstep (se 1 (by rfl) ⟨995648, by rfl⟩ : syracuseStep 1327531 = 1991297) B1991297
theorem B4481459 : Blo 1327482 4481459 := bstep (se 1 (by rfl) ⟨3361094, by rfl⟩ : syracuseStep 4481459 = 6722189) B6722189
theorem B1327543 : Blo 1327482 1327543 := bstep (se 1 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 1327543 = 1991315) B1991315
theorem B1327563 : Blo 1327482 1327563 := bstep (se 1 (by rfl) ⟨995672, by rfl⟩ : syracuseStep 1327563 = 1991345) B1991345
theorem B1327575 : Blo 1327482 1327575 := bstep (se 1 (by rfl) ⟨995681, by rfl⟩ : syracuseStep 1327575 = 1991363) B1991363
theorem B1327595 : Blo 1327482 1327595 := bstep (se 1 (by rfl) ⟨995696, by rfl⟩ : syracuseStep 1327595 = 1991393) B1991393
theorem B1327607 : Blo 1327482 1327607 := bstep (se 1 (by rfl) ⟨995705, by rfl⟩ : syracuseStep 1327607 = 1991411) B1991411
theorem B1327627 : Blo 1327482 1327627 := bstep (se 1 (by rfl) ⟨995720, by rfl⟩ : syracuseStep 1327627 = 1991441) B1991441
theorem B1327639 : Blo 1327482 1327639 := bstep (se 1 (by rfl) ⟨995729, by rfl⟩ : syracuseStep 1327639 = 1991459) B1991459
theorem B1327659 : Blo 1327482 1327659 := bstep (se 1 (by rfl) ⟨995744, by rfl⟩ : syracuseStep 1327659 = 1991489) B1991489
theorem B1327671 : Blo 1327482 1327671 := bstep (se 1 (by rfl) ⟨995753, by rfl⟩ : syracuseStep 1327671 = 1991507) B1991507
theorem B1991243 : Blo 1327482 1991243 := bstep (se 1 (by rfl) ⟨1493432, by rfl⟩ : syracuseStep 1991243 = 2986865) B2986865
theorem B1327691 : Blo 1327482 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B1991255 : Blo 1327482 1991255 := bstep (se 1 (by rfl) ⟨1493441, by rfl⟩ : syracuseStep 1991255 = 2986883) B2986883
theorem B1327703 : Blo 1327482 1327703 := bstep (se 1 (by rfl) ⟨995777, by rfl⟩ : syracuseStep 1327703 = 1991555) B1991555
theorem B57459293 : Blo 1327482 57459293 := bstep (se 3 (by rfl) ⟨10773617, by rfl⟩ : syracuseStep 57459293 = 21547235) B21547235
theorem B1327723 : Blo 1327482 1327723 := bstep (se 1 (by rfl) ⟨995792, by rfl⟩ : syracuseStep 1327723 = 1991585) B1991585
theorem B1327735 : Blo 1327482 1327735 := bstep (se 1 (by rfl) ⟨995801, by rfl⟩ : syracuseStep 1327735 = 1991603) B1991603
theorem B1327755 : Blo 1327482 1327755 := bstep (se 1 (by rfl) ⟨995816, by rfl⟩ : syracuseStep 1327755 = 1991633) B1991633
theorem B1327767 : Blo 1327482 1327767 := bstep (se 1 (by rfl) ⟨995825, by rfl⟩ : syracuseStep 1327767 = 1991651) B1991651
theorem B1991321 : Blo 1327482 1991321 := bstep (se 2 (by rfl) ⟨746745, by rfl⟩ : syracuseStep 1991321 = 1493491) B1493491
theorem B1327787 : Blo 1327482 1327787 := bstep (se 1 (by rfl) ⟨995840, by rfl⟩ : syracuseStep 1327787 = 1991681) B1991681
theorem B1327799 : Blo 1327482 1327799 := bstep (se 1 (by rfl) ⟨995849, by rfl⟩ : syracuseStep 1327799 = 1991699) B1991699
theorem B4481729 : Blo 1327482 4481729 := bstep (se 2 (by rfl) ⟨1680648, by rfl⟩ : syracuseStep 4481729 = 3361297) B3361297
theorem B1327819 : Blo 1327482 1327819 := bstep (se 1 (by rfl) ⟨995864, by rfl⟩ : syracuseStep 1327819 = 1991729) B1991729
theorem B1327831 : Blo 1327482 1327831 := bstep (se 1 (by rfl) ⟨995873, by rfl⟩ : syracuseStep 1327831 = 1991747) B1991747
theorem B1327851 : Blo 1327482 1327851 := bstep (se 1 (by rfl) ⟨995888, by rfl⟩ : syracuseStep 1327851 = 1991777) B1991777
theorem B1327863 : Blo 1327482 1327863 := bstep (se 1 (by rfl) ⟨995897, by rfl⟩ : syracuseStep 1327863 = 1991795) B1991795
theorem B1991435 : Blo 1327482 1991435 := bstep (se 1 (by rfl) ⟨1493576, by rfl⟩ : syracuseStep 1991435 = 2987153) B2987153
theorem B1327883 : Blo 1327482 1327883 := bstep (se 1 (by rfl) ⟨995912, by rfl⟩ : syracuseStep 1327883 = 1991825) B1991825
theorem B1991447 : Blo 1327482 1991447 := bstep (se 1 (by rfl) ⟨1493585, by rfl⟩ : syracuseStep 1991447 = 2987171) B2987171
theorem B1327895 : Blo 1327482 1327895 := bstep (se 1 (by rfl) ⟨995921, by rfl⟩ : syracuseStep 1327895 = 1991843) B1991843
theorem B1327915 : Blo 1327482 1327915 := bstep (se 1 (by rfl) ⟨995936, by rfl⟩ : syracuseStep 1327915 = 1991873) B1991873
theorem B1327927 : Blo 1327482 1327927 := bstep (se 1 (by rfl) ⟨995945, by rfl⟩ : syracuseStep 1327927 = 1991891) B1991891
theorem B1680203 : Blo 1327482 1680203 := bstep (se 1 (by rfl) ⟨1260152, by rfl⟩ : syracuseStep 1680203 = 2520305) B2520305
theorem B1327947 : Blo 1327482 1327947 := bstep (se 1 (by rfl) ⟨995960, by rfl⟩ : syracuseStep 1327947 = 1991921) B1991921
theorem B1327959 : Blo 1327482 1327959 := bstep (se 1 (by rfl) ⟨995969, by rfl⟩ : syracuseStep 1327959 = 1991939) B1991939
theorem B1991513 : Blo 1327482 1991513 := bstep (se 2 (by rfl) ⟨746817, by rfl⟩ : syracuseStep 1991513 = 1493635) B1493635
theorem B4784989 : Blo 1327482 4784989 := bstep (se 3 (by rfl) ⟨897185, by rfl⟩ : syracuseStep 4784989 = 1794371) B1794371
theorem B1327979 : Blo 1327482 1327979 := bstep (se 1 (by rfl) ⟨995984, by rfl⟩ : syracuseStep 1327979 = 1991969) B1991969
theorem B1327991 : Blo 1327482 1327991 := bstep (se 1 (by rfl) ⟨995993, by rfl⟩ : syracuseStep 1327991 = 1991987) B1991987
theorem B1328011 : Blo 1327482 1328011 := bstep (se 1 (by rfl) ⟨996008, by rfl⟩ : syracuseStep 1328011 = 1992017) B1992017
theorem B1794955 : Blo 1327482 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B1328023 : Blo 1327482 1328023 := bstep (se 1 (by rfl) ⟨996017, by rfl⟩ : syracuseStep 1328023 = 1992035) B1992035
theorem B2392985 : Blo 1327482 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B1328043 : Blo 1327482 1328043 := bstep (se 1 (by rfl) ⟨996032, by rfl⟩ : syracuseStep 1328043 = 1992065) B1992065
theorem B1418167 : Blo 1327482 1418167 := bstep (se 1 (by rfl) ⟨1063625, by rfl⟩ : syracuseStep 1418167 = 2127251) B2127251
theorem B1328055 : Blo 1327482 1328055 := bstep (se 1 (by rfl) ⟨996041, by rfl⟩ : syracuseStep 1328055 = 1992083) B1992083
theorem B1991627 : Blo 1327482 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B1328075 : Blo 1327482 1328075 := bstep (se 1 (by rfl) ⟨996056, by rfl⟩ : syracuseStep 1328075 = 1992113) B1992113
theorem B1991639 : Blo 1327482 1991639 := bstep (se 1 (by rfl) ⟨1493729, by rfl⟩ : syracuseStep 1991639 = 2987459) B2987459
theorem B1328087 : Blo 1327482 1328087 := bstep (se 1 (by rfl) ⟨996065, by rfl⟩ : syracuseStep 1328087 = 1992131) B1992131
theorem B1328107 : Blo 1327482 1328107 := bstep (se 1 (by rfl) ⟨996080, by rfl⟩ : syracuseStep 1328107 = 1992161) B1992161
theorem B1328119 : Blo 1327482 1328119 := bstep (se 1 (by rfl) ⟨996089, by rfl⟩ : syracuseStep 1328119 = 1992179) B1992179
theorem B1328139 : Blo 1327482 1328139 := bstep (se 1 (by rfl) ⟨996104, by rfl⟩ : syracuseStep 1328139 = 1992209) B1992209
theorem B1328151 : Blo 1327482 1328151 := bstep (se 1 (by rfl) ⟨996113, by rfl⟩ : syracuseStep 1328151 = 1992227) B1992227
theorem B1991705 : Blo 1327482 1991705 := bstep (se 2 (by rfl) ⟨746889, by rfl⟩ : syracuseStep 1991705 = 1493779) B1493779
theorem B1328171 : Blo 1327482 1328171 := bstep (se 1 (by rfl) ⟨996128, by rfl⟩ : syracuseStep 1328171 = 1992257) B1992257
theorem B1328183 : Blo 1327482 1328183 := bstep (se 1 (by rfl) ⟨996137, by rfl⟩ : syracuseStep 1328183 = 1992275) B1992275
theorem B1328203 : Blo 1327482 1328203 := bstep (se 1 (by rfl) ⟨996152, by rfl⟩ : syracuseStep 1328203 = 1992305) B1992305
theorem B1328215 : Blo 1327482 1328215 := bstep (se 1 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 1328215 = 1992323) B1992323
theorem B1418347 : Blo 1327482 1418347 := bstep (se 1 (by rfl) ⟨1063760, by rfl⟩ : syracuseStep 1418347 = 2127521) B2127521
theorem B1328235 : Blo 1327482 1328235 := bstep (se 1 (by rfl) ⟨996176, by rfl⟩ : syracuseStep 1328235 = 1992353) B1992353
theorem B1328247 : Blo 1327482 1328247 := bstep (se 1 (by rfl) ⟨996185, by rfl⟩ : syracuseStep 1328247 = 1992371) B1992371
theorem B1991819 : Blo 1327482 1991819 := bstep (se 1 (by rfl) ⟨1493864, by rfl⟩ : syracuseStep 1991819 = 2987729) B2987729
theorem B1328267 : Blo 1327482 1328267 := bstep (se 1 (by rfl) ⟨996200, by rfl⟩ : syracuseStep 1328267 = 1992401) B1992401
theorem B1991831 : Blo 1327482 1991831 := bstep (se 1 (by rfl) ⟨1493873, by rfl⟩ : syracuseStep 1991831 = 2987747) B2987747
theorem B1328279 : Blo 1327482 1328279 := bstep (se 1 (by rfl) ⟨996209, by rfl⟩ : syracuseStep 1328279 = 1992419) B1992419
theorem B1328299 : Blo 1327482 1328299 := bstep (se 1 (by rfl) ⟨996224, by rfl⟩ : syracuseStep 1328299 = 1992449) B1992449
theorem B1328311 : Blo 1327482 1328311 := bstep (se 1 (by rfl) ⟨996233, by rfl⟩ : syracuseStep 1328311 = 1992467) B1992467
theorem B1328331 : Blo 1327482 1328331 := bstep (se 1 (by rfl) ⟨996248, by rfl⟩ : syracuseStep 1328331 = 1992497) B1992497
theorem B1328343 : Blo 1327482 1328343 := bstep (se 1 (by rfl) ⟨996257, by rfl⟩ : syracuseStep 1328343 = 1992515) B1992515
theorem B1991897 : Blo 1327482 1991897 := bstep (se 2 (by rfl) ⟨746961, by rfl⟩ : syracuseStep 1991897 = 1493923) B1493923
theorem B4482269 : Blo 1327482 4482269 := bstep (se 3 (by rfl) ⟨840425, by rfl⟩ : syracuseStep 4482269 = 1680851) B1680851
theorem B1328363 : Blo 1327482 1328363 := bstep (se 1 (by rfl) ⟨996272, by rfl⟩ : syracuseStep 1328363 = 1992545) B1992545
theorem B1328375 : Blo 1327482 1328375 := bstep (se 1 (by rfl) ⟨996281, by rfl⟩ : syracuseStep 1328375 = 1992563) B1992563
theorem B1328395 : Blo 1327482 1328395 := bstep (se 1 (by rfl) ⟨996296, by rfl⟩ : syracuseStep 1328395 = 1992593) B1992593
theorem B1328407 : Blo 1327482 1328407 := bstep (se 1 (by rfl) ⟨996305, by rfl⟩ : syracuseStep 1328407 = 1992611) B1992611
theorem B9577763 : Blo 1327482 9577763 := bstep (se 1 (by rfl) ⟨7183322, by rfl⟩ : syracuseStep 9577763 = 14366645) B14366645
theorem B1328427 : Blo 1327482 1328427 := bstep (se 1 (by rfl) ⟨996320, by rfl⟩ : syracuseStep 1328427 = 1992641) B1992641
theorem B1328439 : Blo 1327482 1328439 := bstep (se 1 (by rfl) ⟨996329, by rfl⟩ : syracuseStep 1328439 = 1992659) B1992659
theorem B1992011 : Blo 1327482 1992011 := bstep (se 1 (by rfl) ⟨1494008, by rfl⟩ : syracuseStep 1992011 = 2988017) B2988017
theorem B1328459 : Blo 1327482 1328459 := bstep (se 1 (by rfl) ⟨996344, by rfl⟩ : syracuseStep 1328459 = 1992689) B1992689
theorem B1992023 : Blo 1327482 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B1328471 : Blo 1327482 1328471 := bstep (se 1 (by rfl) ⟨996353, by rfl⟩ : syracuseStep 1328471 = 1992707) B1992707
theorem B1328491 : Blo 1327482 1328491 := bstep (se 1 (by rfl) ⟨996368, by rfl⟩ : syracuseStep 1328491 = 1992737) B1992737
theorem B1328503 : Blo 1327482 1328503 := bstep (se 1 (by rfl) ⟨996377, by rfl⟩ : syracuseStep 1328503 = 1992755) B1992755
theorem B1328523 : Blo 1327482 1328523 := bstep (se 1 (by rfl) ⟨996392, by rfl⟩ : syracuseStep 1328523 = 1992785) B1992785
theorem B1328535 : Blo 1327482 1328535 := bstep (se 1 (by rfl) ⟨996401, by rfl⟩ : syracuseStep 1328535 = 1992803) B1992803
theorem B1992089 : Blo 1327482 1992089 := bstep (se 2 (by rfl) ⟨747033, by rfl⟩ : syracuseStep 1992089 = 1494067) B1494067
theorem B2393497 : Blo 1327482 2393497 := bstep (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) B1795123
theorem B1328555 : Blo 1327482 1328555 := bstep (se 1 (by rfl) ⟨996416, by rfl⟩ : syracuseStep 1328555 = 1992833) B1992833
theorem B3589555 : Blo 1327482 3589555 := bstep (se 1 (by rfl) ⟨2692166, by rfl⟩ : syracuseStep 3589555 = 5384333) B5384333
theorem B1328567 : Blo 1327482 1328567 := bstep (se 1 (by rfl) ⟨996425, by rfl⟩ : syracuseStep 1328567 = 1992851) B1992851
theorem B1328587 : Blo 1327482 1328587 := bstep (se 1 (by rfl) ⟨996440, by rfl⟩ : syracuseStep 1328587 = 1992881) B1992881
theorem B1328599 : Blo 1327482 1328599 := bstep (se 1 (by rfl) ⟨996449, by rfl⟩ : syracuseStep 1328599 = 1992899) B1992899
theorem B2393561 : Blo 1327482 2393561 := bstep (se 2 (by rfl) ⟨897585, by rfl⟩ : syracuseStep 2393561 = 1795171) B1795171
theorem B1328619 : Blo 1327482 1328619 := bstep (se 1 (by rfl) ⟨996464, by rfl⟩ : syracuseStep 1328619 = 1992929) B1992929
theorem B1328631 : Blo 1327482 1328631 := bstep (se 1 (by rfl) ⟨996473, by rfl⟩ : syracuseStep 1328631 = 1992947) B1992947
theorem B1680907 : Blo 1327482 1680907 := bstep (se 1 (by rfl) ⟨1260680, by rfl⟩ : syracuseStep 1680907 = 2521361) B2521361
theorem B1992203 : Blo 1327482 1992203 := bstep (se 1 (by rfl) ⟨1494152, by rfl⟩ : syracuseStep 1992203 = 2988305) B2988305
theorem B1328651 : Blo 1327482 1328651 := bstep (se 1 (by rfl) ⟨996488, by rfl⟩ : syracuseStep 1328651 = 1992977) B1992977
theorem B1992215 : Blo 1327482 1992215 := bstep (se 1 (by rfl) ⟨1494161, by rfl⟩ : syracuseStep 1992215 = 2988323) B2988323
theorem B1328663 : Blo 1327482 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B1328683 : Blo 1327482 1328683 := bstep (se 1 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 1328683 = 1993025) B1993025
theorem B9209389 : Blo 1327482 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B1328695 : Blo 1327482 1328695 := bstep (se 1 (by rfl) ⟨996521, by rfl⟩ : syracuseStep 1328695 = 1993043) B1993043
theorem B6817355 : Blo 1327482 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B1328715 : Blo 1327482 1328715 := bstep (se 1 (by rfl) ⟨996536, by rfl⟩ : syracuseStep 1328715 = 1993073) B1993073
theorem B1328727 : Blo 1327482 1328727 := bstep (se 1 (by rfl) ⟨996545, by rfl⟩ : syracuseStep 1328727 = 1993091) B1993091
theorem B1992281 : Blo 1327482 1992281 := bstep (se 2 (by rfl) ⟨747105, by rfl⟩ : syracuseStep 1992281 = 1494211) B1494211
theorem B1328747 : Blo 1327482 1328747 := bstep (se 1 (by rfl) ⟨996560, by rfl⟩ : syracuseStep 1328747 = 1993121) B1993121
theorem B1328759 : Blo 1327482 1328759 := bstep (se 1 (by rfl) ⟨996569, by rfl⟩ : syracuseStep 1328759 = 1993139) B1993139
theorem B1328779 : Blo 1327482 1328779 := bstep (se 1 (by rfl) ⟨996584, by rfl⟩ : syracuseStep 1328779 = 1993169) B1993169
theorem B1328791 : Blo 1327482 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B1328811 : Blo 1327482 1328811 := bstep (se 1 (by rfl) ⟨996608, by rfl⟩ : syracuseStep 1328811 = 1993217) B1993217
theorem B2836147 : Blo 1327482 2836147 := bstep (se 1 (by rfl) ⟨2127110, by rfl⟩ : syracuseStep 2836147 = 4254221) B4254221
theorem B1328823 : Blo 1327482 1328823 := bstep (se 1 (by rfl) ⟨996617, by rfl⟩ : syracuseStep 1328823 = 1993235) B1993235
theorem B1992395 : Blo 1327482 1992395 := bstep (se 1 (by rfl) ⟨1494296, by rfl⟩ : syracuseStep 1992395 = 2988593) B2988593
theorem B1328843 : Blo 1327482 1328843 := bstep (se 1 (by rfl) ⟨996632, by rfl⟩ : syracuseStep 1328843 = 1993265) B1993265
theorem B1992407 : Blo 1327482 1992407 := bstep (se 1 (by rfl) ⟨1494305, by rfl⟩ : syracuseStep 1992407 = 2988611) B2988611
theorem B1328855 : Blo 1327482 1328855 := bstep (se 1 (by rfl) ⟨996641, by rfl⟩ : syracuseStep 1328855 = 1993283) B1993283
theorem B1328875 : Blo 1327482 1328875 := bstep (se 1 (by rfl) ⟨996656, by rfl⟩ : syracuseStep 1328875 = 1993313) B1993313
theorem B1328887 : Blo 1327482 1328887 := bstep (se 1 (by rfl) ⟨996665, by rfl⟩ : syracuseStep 1328887 = 1993331) B1993331
theorem B1328907 : Blo 1327482 1328907 := bstep (se 1 (by rfl) ⟨996680, by rfl⟩ : syracuseStep 1328907 = 1993361) B1993361
theorem B1681175 : Blo 1327482 1681175 := bstep (se 1 (by rfl) ⟨1260881, by rfl⟩ : syracuseStep 1681175 = 2521763) B2521763
theorem B1992473 : Blo 1327482 1992473 := bstep (se 2 (by rfl) ⟨747177, by rfl⟩ : syracuseStep 1992473 = 1494355) B1494355
theorem B1328919 : Blo 1327482 1328919 := bstep (se 1 (by rfl) ⟨996689, by rfl⟩ : syracuseStep 1328919 = 1993379) B1993379
theorem B1328939 : Blo 1327482 1328939 := bstep (se 1 (by rfl) ⟨996704, by rfl⟩ : syracuseStep 1328939 = 1993409) B1993409
theorem B1328951 : Blo 1327482 1328951 := bstep (se 1 (by rfl) ⟨996713, by rfl⟩ : syracuseStep 1328951 = 1993427) B1993427
theorem B12814145 : Blo 1327482 12814145 := bstep (se 2 (by rfl) ⟨4805304, by rfl⟩ : syracuseStep 12814145 = 9610609) B9610609
theorem B1328971 : Blo 1327482 1328971 := bstep (se 1 (by rfl) ⟨996728, by rfl⟩ : syracuseStep 1328971 = 1993457) B1993457
theorem B1992587 : Blo 1327482 1992587 := bstep (se 1 (by rfl) ⟨1494440, by rfl⟩ : syracuseStep 1992587 = 2988881) B2988881
theorem B1992599 : Blo 1327482 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B1992665 : Blo 1327482 1992665 := bstep (se 2 (by rfl) ⟨747249, by rfl⟩ : syracuseStep 1992665 = 1494499) B1494499
theorem B9578513 : Blo 1327482 9578513 := bstep (se 2 (by rfl) ⟨3591942, by rfl⟩ : syracuseStep 9578513 = 7183885) B7183885
theorem B6727697 : Blo 1327482 6727697 := bstep (se 2 (by rfl) ⟨2522886, by rfl⟩ : syracuseStep 6727697 = 5045773) B5045773
theorem B3360791 : Blo 1327482 3360791 := bstep (se 1 (by rfl) ⟨2520593, by rfl⟩ : syracuseStep 3360791 = 5041187) B5041187
theorem B4786199 : Blo 1327482 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B2836505 : Blo 1327482 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1992779 : Blo 1327482 1992779 := bstep (se 1 (by rfl) ⟨1494584, by rfl⟩ : syracuseStep 1992779 = 2989169) B2989169
theorem B5752907 : Blo 1327482 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B15763531 : Blo 1327482 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B4040779 : Blo 1327482 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B1992791 : Blo 1327482 1992791 := bstep (se 1 (by rfl) ⟨1494593, by rfl⟩ : syracuseStep 1992791 = 2989187) B2989187
theorem B7776407 : Blo 1327482 7776407 := bstep (se 1 (by rfl) ⟨5832305, by rfl⟩ : syracuseStep 7776407 = 11664611) B11664611
theorem B1992857 : Blo 1327482 1992857 := bstep (se 2 (by rfl) ⟨747321, by rfl⟩ : syracuseStep 1992857 = 1494643) B1494643
theorem B6727859 : Blo 1327482 6727859 := bstep (se 1 (by rfl) ⟨5045894, by rfl⟩ : syracuseStep 6727859 = 10091789) B10091789
theorem B2730187 : Blo 1327482 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B1992971 : Blo 1327482 1992971 := bstep (se 1 (by rfl) ⟨1494728, by rfl⟩ : syracuseStep 1992971 = 2989457) B2989457
theorem B1992983 : Blo 1327482 1992983 := bstep (se 1 (by rfl) ⟨1494737, by rfl⟩ : syracuseStep 1992983 = 2989475) B2989475
theorem B4483403 : Blo 1327482 4483403 := bstep (se 1 (by rfl) ⟨3362552, by rfl⟩ : syracuseStep 4483403 = 6725105) B6725105
theorem B1993049 : Blo 1327482 1993049 := bstep (se 2 (by rfl) ⟨747393, by rfl⟩ : syracuseStep 1993049 = 1494787) B1494787
theorem B8513923 : Blo 1327482 8513923 := bstep (se 1 (by rfl) ⟨6385442, by rfl⟩ : syracuseStep 8513923 = 12770885) B12770885
theorem B1493419 : Blo 1327482 1493419 := bstep (se 1 (by rfl) ⟨1120064, by rfl⟩ : syracuseStep 1493419 = 2240129) B2240129
theorem B1993163 : Blo 1327482 1993163 := bstep (se 1 (by rfl) ⟨1494872, by rfl⟩ : syracuseStep 1993163 = 2989745) B2989745
theorem B1993175 : Blo 1327482 1993175 := bstep (se 1 (by rfl) ⟨1494881, by rfl⟩ : syracuseStep 1993175 = 2989763) B2989763
theorem B1681879 : Blo 1327482 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B10086929 : Blo 1327482 10086929 := bstep (se 2 (by rfl) ⟨3782598, by rfl⟩ : syracuseStep 10086929 = 7565197) B7565197
theorem B1493527 : Blo 1327482 1493527 := bstep (se 1 (by rfl) ⟨1120145, by rfl⟩ : syracuseStep 1493527 = 2240291) B2240291
theorem B1993241 : Blo 1327482 1993241 := bstep (se 2 (by rfl) ⟨747465, by rfl⟩ : syracuseStep 1993241 = 1494931) B1494931
theorem B4483673 : Blo 1327482 4483673 := bstep (se 2 (by rfl) ⟨1681377, by rfl⟩ : syracuseStep 4483673 = 3362755) B3362755
theorem B1993355 : Blo 1327482 1993355 := bstep (se 1 (by rfl) ⟨1495016, by rfl⟩ : syracuseStep 1993355 = 2990033) B2990033
theorem B1993367 : Blo 1327482 1993367 := bstep (se 1 (by rfl) ⟨1495025, by rfl⟩ : syracuseStep 1993367 = 2990051) B2990051
theorem B3361459 : Blo 1327482 3361459 := bstep (se 1 (by rfl) ⟨2521094, by rfl⟩ : syracuseStep 3361459 = 5042189) B5042189
theorem B1493707 : Blo 1327482 1493707 := bstep (se 1 (by rfl) ⟨1120280, by rfl⟩ : syracuseStep 1493707 = 2240561) B2240561
theorem B1993433 : Blo 1327482 1993433 := bstep (se 2 (by rfl) ⟨747537, by rfl⟩ : syracuseStep 1993433 = 1495075) B1495075
theorem B5040899 : Blo 1327482 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B5040913 : Blo 1327482 5040913 := bstep (se 2 (by rfl) ⟨1890342, by rfl⟩ : syracuseStep 5040913 = 3780685) B3780685
theorem B1493815 : Blo 1327482 1493815 := bstep (se 1 (by rfl) ⟨1120361, by rfl⟩ : syracuseStep 1493815 = 2240723) B2240723
theorem B3361601 : Blo 1327482 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B6720407 : Blo 1327482 6720407 := bstep (se 1 (by rfl) ⟨5040305, by rfl⟩ : syracuseStep 6720407 = 10080611) B10080611
theorem B5671883 : Blo 1327482 5671883 := bstep (se 1 (by rfl) ⟨4253912, by rfl⟩ : syracuseStep 5671883 = 8507825) B8507825
theorem B1493995 : Blo 1327482 1493995 := bstep (se 1 (by rfl) ⟨1120496, by rfl⟩ : syracuseStep 1493995 = 2240993) B2240993
theorem B21531665 : Blo 1327482 21531665 := bstep (se 2 (by rfl) ⟨8074374, by rfl⟩ : syracuseStep 21531665 = 16148749) B16148749
theorem B7482385 : Blo 1327482 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B5041217 : Blo 1327482 5041217 := bstep (se 2 (by rfl) ⟨1890456, by rfl⟩ : syracuseStep 5041217 = 3780913) B3780913
theorem B1494103 : Blo 1327482 1494103 := bstep (se 1 (by rfl) ⟨1120577, by rfl⟩ : syracuseStep 1494103 = 2241155) B2241155
theorem B1494283 : Blo 1327482 1494283 := bstep (se 1 (by rfl) ⟨1120712, by rfl⟩ : syracuseStep 1494283 = 2241425) B2241425
theorem B4484375 : Blo 1327482 4484375 := bstep (se 1 (by rfl) ⟨3363281, by rfl⟩ : syracuseStep 4484375 = 6726563) B6726563
theorem B1494391 : Blo 1327482 1494391 := bstep (se 1 (by rfl) ⟨1120793, by rfl⟩ : syracuseStep 1494391 = 2241587) B2241587
theorem B6819203 : Blo 1327482 6819203 := bstep (se 1 (by rfl) ⟨5114402, by rfl⟩ : syracuseStep 6819203 = 10228805) B10228805
theorem B11341235 : Blo 1327482 11341235 := bstep (se 1 (by rfl) ⟨8505926, by rfl⟩ : syracuseStep 11341235 = 17011853) B17011853
theorem B1494571 : Blo 1327482 1494571 := bstep (se 1 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 1494571 = 2241857) B2241857
theorem B55266947 : Blo 1327482 55266947 := bstep (se 1 (by rfl) ⟨41450210, by rfl⟩ : syracuseStep 55266947 = 82900421) B82900421
theorem B1494679 : Blo 1327482 1494679 := bstep (se 1 (by rfl) ⟨1121009, by rfl⟩ : syracuseStep 1494679 = 2242019) B2242019
theorem B2240203 : Blo 1327482 2240203 := bstep (se 1 (by rfl) ⟨1680152, by rfl⟩ : syracuseStep 2240203 = 3360305) B3360305
theorem B109080269 : Blo 1327482 109080269 := bstep (se 3 (by rfl) ⟨20452550, by rfl⟩ : syracuseStep 109080269 = 40905101) B40905101
theorem B5041885 : Blo 1327482 5041885 := bstep (se 3 (by rfl) ⟨945353, by rfl⟩ : syracuseStep 5041885 = 1890707) B1890707
theorem B4484915 : Blo 1327482 4484915 := bstep (se 1 (by rfl) ⟨3363686, by rfl⟩ : syracuseStep 4484915 = 6727373) B6727373
theorem B4255553 : Blo 1327482 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B1494859 : Blo 1327482 1494859 := bstep (se 1 (by rfl) ⟨1121144, by rfl⟩ : syracuseStep 1494859 = 2242289) B2242289
theorem B2240345 : Blo 1327482 2240345 := bstep (se 2 (by rfl) ⟨840129, by rfl⟩ : syracuseStep 2240345 = 1680259) B1680259
theorem B3780503 : Blo 1327482 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B1494967 : Blo 1327482 1494967 := bstep (se 1 (by rfl) ⟨1121225, by rfl⟩ : syracuseStep 1494967 = 2242451) B2242451
theorem B2240473 : Blo 1327482 2240473 := bstep (se 2 (by rfl) ⟨840177, by rfl⟩ : syracuseStep 2240473 = 1680355) B1680355
theorem B4853783 : Blo 1327482 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B3362867 : Blo 1327482 3362867 := bstep (se 1 (by rfl) ⟨2522150, by rfl⟩ : syracuseStep 3362867 = 5044301) B5044301
theorem B4485185 : Blo 1327482 4485185 := bstep (se 2 (by rfl) ⟨1681944, by rfl⟩ : syracuseStep 4485185 = 3363889) B3363889
theorem B2691265 : Blo 1327482 2691265 := bstep (se 2 (by rfl) ⟨1009224, by rfl⟩ : syracuseStep 2691265 = 2018449) B2018449
theorem B4542809 : Blo 1327482 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B96932213 : Blo 1327482 96932213 := bstep (se 5 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 96932213 = 9087395) B9087395
theorem B2241047 : Blo 1327482 2241047 := bstep (se 1 (by rfl) ⟨1680785, by rfl⟩ : syracuseStep 2241047 = 3361571) B3361571
theorem B5673523 : Blo 1327482 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B3363403 : Blo 1327482 3363403 := bstep (se 1 (by rfl) ⟨2522552, by rfl⟩ : syracuseStep 3363403 = 5045105) B5045105
theorem B2126425 : Blo 1327482 2126425 := bstep (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) B1594819
theorem B4543069 : Blo 1327482 4543069 := bstep (se 3 (by rfl) ⟨851825, by rfl⟩ : syracuseStep 4543069 = 1703651) B1703651
theorem B2241175 : Blo 1327482 2241175 := bstep (se 1 (by rfl) ⟨1680881, by rfl⟩ : syracuseStep 2241175 = 3361763) B3361763
theorem B3781313 : Blo 1327482 3781313 := bstep (se 2 (by rfl) ⟨1417992, by rfl⟩ : syracuseStep 3781313 = 2835985) B2835985
theorem B9704141 : Blo 1327482 9704141 := bstep (se 3 (by rfl) ⟨1819526, by rfl⟩ : syracuseStep 9704141 = 3639053) B3639053
theorem B3363545 : Blo 1327482 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B7566155 : Blo 1327482 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B2986955 : Blo 1327482 2986955 := bstep (se 1 (by rfl) ⟨2240216, by rfl⟩ : syracuseStep 2986955 = 4480433) B4480433
theorem B5043161 : Blo 1327482 5043161 := bstep (se 2 (by rfl) ⟨1891185, by rfl⟩ : syracuseStep 5043161 = 3782371) B3782371
theorem B2987009 : Blo 1327482 2987009 := bstep (se 2 (by rfl) ⟨1120128, by rfl⟩ : syracuseStep 2987009 = 2240257) B2240257
theorem B6911041 : Blo 1327482 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B5674157 : Blo 1327482 5674157 := bstep (se 3 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 5674157 = 2127809) B2127809
theorem B4150451 : Blo 1327482 4150451 := bstep (se 1 (by rfl) ⟨3112838, by rfl⟩ : syracuseStep 4150451 = 6225677) B6225677
theorem B2987225 : Blo 1327482 2987225 := bstep (se 2 (by rfl) ⟨1120209, by rfl⟩ : syracuseStep 2987225 = 2240419) B2240419
theorem B2241803 : Blo 1327482 2241803 := bstep (se 1 (by rfl) ⟨1681352, by rfl⟩ : syracuseStep 2241803 = 3362705) B3362705
theorem B11343149 : Blo 1327482 11343149 := bstep (se 3 (by rfl) ⟨2126840, by rfl⟩ : syracuseStep 11343149 = 4253681) B4253681
theorem B2987315 : Blo 1327482 2987315 := bstep (se 1 (by rfl) ⟨2240486, by rfl⟩ : syracuseStep 2987315 = 4480973) B4480973
theorem B2987351 : Blo 1327482 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B2241931 : Blo 1327482 2241931 := bstep (se 1 (by rfl) ⟨1681448, by rfl⟩ : syracuseStep 2241931 = 3362897) B3362897
theorem B3192281 : Blo 1327482 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B2987531 : Blo 1327482 2987531 := bstep (se 1 (by rfl) ⟨2240648, by rfl⟩ : syracuseStep 2987531 = 4481297) B4481297
theorem B2242073 : Blo 1327482 2242073 := bstep (se 2 (by rfl) ⟨840777, by rfl⟩ : syracuseStep 2242073 = 1681555) B1681555
theorem B2987585 : Blo 1327482 2987585 := bstep (se 2 (by rfl) ⟨1120344, by rfl⟩ : syracuseStep 2987585 = 2240689) B2240689
theorem B2520715 : Blo 1327482 2520715 := bstep (se 1 (by rfl) ⟨1890536, by rfl⟩ : syracuseStep 2520715 = 3781073) B3781073
theorem B2242201 : Blo 1327482 2242201 := bstep (se 2 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 2242201 = 1681651) B1681651
theorem B2520791 : Blo 1327482 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B2987801 : Blo 1327482 2987801 := bstep (se 2 (by rfl) ⟨1120425, by rfl⟩ : syracuseStep 2987801 = 2240851) B2240851
theorem B2987891 : Blo 1327482 2987891 := bstep (se 1 (by rfl) ⟨2240918, by rfl⟩ : syracuseStep 2987891 = 4481837) B4481837
theorem B2987927 : Blo 1327482 2987927 := bstep (se 1 (by rfl) ⟨2240945, by rfl⟩ : syracuseStep 2987927 = 4481891) B4481891
theorem B12761009 : Blo 1327482 12761009 := bstep (se 2 (by rfl) ⟨4785378, by rfl⟩ : syracuseStep 12761009 = 9570757) B9570757
theorem B1890263 : Blo 1327482 1890263 := bstep (se 1 (by rfl) ⟨1417697, by rfl⟩ : syracuseStep 1890263 = 2835395) B2835395
theorem B11343833 : Blo 1327482 11343833 := bstep (se 2 (by rfl) ⟨4253937, by rfl⟩ : syracuseStep 11343833 = 8507875) B8507875
theorem B2988107 : Blo 1327482 2988107 := bstep (se 1 (by rfl) ⟨2241080, by rfl⟩ : syracuseStep 2988107 = 4482161) B4482161
theorem B2988161 : Blo 1327482 2988161 := bstep (se 2 (by rfl) ⟨1120560, by rfl⟩ : syracuseStep 2988161 = 2241121) B2241121
theorem B6740147 : Blo 1327482 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B3782963 : Blo 1327482 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B3832129 : Blo 1327482 3832129 := bstep (se 2 (by rfl) ⟨1437048, by rfl⟩ : syracuseStep 3832129 = 2874097) B2874097
theorem B10090817 : Blo 1327482 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B3782987 : Blo 1327482 3782987 := bstep (se 1 (by rfl) ⟨2837240, by rfl⟩ : syracuseStep 3782987 = 5674481) B5674481
theorem B2988377 : Blo 1327482 2988377 := bstep (se 2 (by rfl) ⟨1120641, by rfl⟩ : syracuseStep 2988377 = 2241283) B2241283
theorem B17021285 : Blo 1327482 17021285 := bstep (se 4 (by rfl) ⟨1595745, by rfl⟩ : syracuseStep 17021285 = 3191491) B3191491
theorem B2521459 : Blo 1327482 2521459 := bstep (se 1 (by rfl) ⟨1891094, by rfl⟩ : syracuseStep 2521459 = 3782189) B3782189
theorem B6723971 : Blo 1327482 6723971 := bstep (se 1 (by rfl) ⟨5042978, by rfl⟩ : syracuseStep 6723971 = 10085957) B10085957
theorem B2988467 : Blo 1327482 2988467 := bstep (se 1 (by rfl) ⟨2241350, by rfl⟩ : syracuseStep 2988467 = 4482701) B4482701
theorem B2988503 : Blo 1327482 2988503 := bstep (se 1 (by rfl) ⟨2241377, by rfl⟩ : syracuseStep 2988503 = 4482755) B4482755
theorem B11352581 : Blo 1327482 11352581 := bstep (se 4 (by rfl) ⟨1064304, by rfl⟩ : syracuseStep 11352581 = 2128609) B2128609
theorem B5044787 : Blo 1327482 5044787 := bstep (se 1 (by rfl) ⟨3783590, by rfl⟩ : syracuseStep 5044787 = 7567181) B7567181
theorem B5044801 : Blo 1327482 5044801 := bstep (se 2 (by rfl) ⟨1891800, by rfl⟩ : syracuseStep 5044801 = 3783601) B3783601
theorem B2521687 : Blo 1327482 2521687 := bstep (se 1 (by rfl) ⟨1891265, by rfl⟩ : syracuseStep 2521687 = 3782531) B3782531
theorem B14006915 : Blo 1327482 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B2988683 : Blo 1327482 2988683 := bstep (se 1 (by rfl) ⟨2241512, by rfl⟩ : syracuseStep 2988683 = 4483025) B4483025
theorem B2988737 : Blo 1327482 2988737 := bstep (se 2 (by rfl) ⟨1120776, by rfl⟩ : syracuseStep 2988737 = 2241553) B2241553
theorem B2521793 : Blo 1327482 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B3029707 : Blo 1327482 3029707 := bstep (se 1 (by rfl) ⟨2272280, by rfl⟩ : syracuseStep 3029707 = 4544561) B4544561
theorem B2521945 : Blo 1327482 2521945 := bstep (se 2 (by rfl) ⟨945729, by rfl⟩ : syracuseStep 2521945 = 1891459) B1891459
theorem B2988953 : Blo 1327482 2988953 := bstep (se 2 (by rfl) ⟨1120857, by rfl⟩ : syracuseStep 2988953 = 2241715) B2241715
theorem B2989043 : Blo 1327482 2989043 := bstep (se 1 (by rfl) ⟨2241782, by rfl⟩ : syracuseStep 2989043 = 4483565) B4483565
theorem B2989079 : Blo 1327482 2989079 := bstep (se 1 (by rfl) ⟨2241809, by rfl⟩ : syracuseStep 2989079 = 4483619) B4483619
theorem B3783773 : Blo 1327482 3783773 := bstep (se 3 (by rfl) ⟨709457, by rfl⟩ : syracuseStep 3783773 = 1418915) B1418915
theorem B2989259 : Blo 1327482 2989259 := bstep (se 1 (by rfl) ⟨2241944, by rfl⟩ : syracuseStep 2989259 = 4483889) B4483889
theorem B2989313 : Blo 1327482 2989313 := bstep (se 2 (by rfl) ⟨1120992, by rfl⟩ : syracuseStep 2989313 = 2241985) B2241985
theorem B9084311 : Blo 1327482 9084311 := bstep (se 1 (by rfl) ⟨6813233, by rfl⟩ : syracuseStep 9084311 = 13626467) B13626467
theorem B2989529 : Blo 1327482 2989529 := bstep (se 2 (by rfl) ⟨1121073, by rfl⟩ : syracuseStep 2989529 = 2242147) B2242147
theorem B1703435 : Blo 1327482 1703435 := bstep (se 1 (by rfl) ⟨1277576, by rfl⟩ : syracuseStep 1703435 = 2555153) B2555153
theorem B2989619 : Blo 1327482 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B2989655 : Blo 1327482 2989655 := bstep (se 1 (by rfl) ⟨2242241, by rfl⟩ : syracuseStep 2989655 = 4484483) B4484483
theorem B2989835 : Blo 1327482 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B18177857 : Blo 1327482 18177857 := bstep (se 2 (by rfl) ⟨6816696, by rfl⟩ : syracuseStep 18177857 = 13633393) B13633393
theorem B2989889 : Blo 1327482 2989889 := bstep (se 2 (by rfl) ⟨1121208, by rfl⟩ : syracuseStep 2989889 = 2242417) B2242417
theorem B4480919 : Blo 1327482 4480919 := bstep (se 1 (by rfl) ⟨3360689, by rfl⟩ : syracuseStep 4480919 = 6721379) B6721379
theorem B4038551 : Blo 1327482 4038551 := bstep (se 1 (by rfl) ⟨3028913, by rfl⟩ : syracuseStep 4038551 = 6057827) B6057827
theorem B3030977 : Blo 1327482 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B3235855 : Blo 1327482 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B2990123 : Blo 1327482 2990123 := bstep (se 1 (by rfl) ⟨2242592, by rfl⟩ : syracuseStep 2990123 = 4485185) B4485185
theorem B18169973 : Blo 1327482 18169973 := bstep (se 5 (by rfl) ⟨851717, by rfl⟩ : syracuseStep 18169973 = 1703435) B1703435
theorem B3588353 : Blo 1327482 3588353 := bstep (se 2 (by rfl) ⟨1345632, by rfl⟩ : syracuseStep 3588353 = 2691265) B2691265
theorem B1327495 : Blo 1327482 1327495 := bstep (se 1 (by rfl) ⟨995621, by rfl⟩ : syracuseStep 1327495 = 1991243) B1991243
theorem B1327503 : Blo 1327482 1327503 := bstep (se 1 (by rfl) ⟨995627, by rfl⟩ : syracuseStep 1327503 = 1991255) B1991255
theorem B38306195 : Blo 1327482 38306195 := bstep (se 1 (by rfl) ⟨28729646, by rfl⟩ : syracuseStep 38306195 = 57459293) B57459293
theorem B1327547 : Blo 1327482 1327547 := bstep (se 1 (by rfl) ⟨995660, by rfl⟩ : syracuseStep 1327547 = 1991321) B1991321
theorem B1327623 : Blo 1327482 1327623 := bstep (se 1 (by rfl) ⟨995717, by rfl⟩ : syracuseStep 1327623 = 1991435) B1991435
theorem B1327631 : Blo 1327482 1327631 := bstep (se 1 (by rfl) ⟨995723, by rfl⟩ : syracuseStep 1327631 = 1991447) B1991447
theorem B1991225 : Blo 1327482 1991225 := bstep (se 2 (by rfl) ⟨746709, by rfl⟩ : syracuseStep 1991225 = 1493419) B1493419
theorem B1327675 : Blo 1327482 1327675 := bstep (se 1 (by rfl) ⟨995756, by rfl⟩ : syracuseStep 1327675 = 1991513) B1991513
theorem B1991303 : Blo 1327482 1991303 := bstep (se 1 (by rfl) ⟨1493477, by rfl⟩ : syracuseStep 1991303 = 2986955) B2986955
theorem B1327751 : Blo 1327482 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B1327759 : Blo 1327482 1327759 := bstep (se 1 (by rfl) ⟨995819, by rfl⟩ : syracuseStep 1327759 = 1991639) B1991639
theorem B1991339 : Blo 1327482 1991339 := bstep (se 1 (by rfl) ⟨1493504, by rfl⟩ : syracuseStep 1991339 = 2987009) B2987009
theorem B1327803 : Blo 1327482 1327803 := bstep (se 1 (by rfl) ⟨995852, by rfl⟩ : syracuseStep 1327803 = 1991705) B1991705
theorem B1991369 : Blo 1327482 1991369 := bstep (se 2 (by rfl) ⟨746763, by rfl⟩ : syracuseStep 1991369 = 1493527) B1493527
theorem B6726401 : Blo 1327482 6726401 := bstep (se 2 (by rfl) ⟨2522400, by rfl⟩ : syracuseStep 6726401 = 5044801) B5044801
theorem B1327879 : Blo 1327482 1327879 := bstep (se 1 (by rfl) ⟨995909, by rfl⟩ : syracuseStep 1327879 = 1991819) B1991819
theorem B1327887 : Blo 1327482 1327887 := bstep (se 1 (by rfl) ⟨995915, by rfl⟩ : syracuseStep 1327887 = 1991831) B1991831
theorem B2835233 : Blo 1327482 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B1991483 : Blo 1327482 1991483 := bstep (se 1 (by rfl) ⟨1493612, by rfl⟩ : syracuseStep 1991483 = 2987225) B2987225
theorem B1327931 : Blo 1327482 1327931 := bstep (se 1 (by rfl) ⟨995948, by rfl⟩ : syracuseStep 1327931 = 1991897) B1991897
theorem B7562099 : Blo 1327482 7562099 := bstep (se 1 (by rfl) ⟨5671574, by rfl⟩ : syracuseStep 7562099 = 11343149) B11343149
theorem B1991543 : Blo 1327482 1991543 := bstep (se 1 (by rfl) ⟨1493657, by rfl⟩ : syracuseStep 1991543 = 2987315) B2987315
theorem B1328007 : Blo 1327482 1328007 := bstep (se 1 (by rfl) ⟨996005, by rfl⟩ : syracuseStep 1328007 = 1992011) B1992011
theorem B1991567 : Blo 1327482 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B1328015 : Blo 1327482 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B4481945 : Blo 1327482 4481945 := bstep (se 2 (by rfl) ⟨1680729, by rfl⟩ : syracuseStep 4481945 = 3361459) B3361459
theorem B48456629 : Blo 1327482 48456629 := bstep (se 5 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 48456629 = 4542809) B4542809
theorem B1991609 : Blo 1327482 1991609 := bstep (se 2 (by rfl) ⟨746853, by rfl⟩ : syracuseStep 1991609 = 1493707) B1493707
theorem B1328059 : Blo 1327482 1328059 := bstep (se 1 (by rfl) ⟨996044, by rfl⟩ : syracuseStep 1328059 = 1992089) B1992089
theorem B1991687 : Blo 1327482 1991687 := bstep (se 1 (by rfl) ⟨1493765, by rfl⟩ : syracuseStep 1991687 = 2987531) B2987531
theorem B1328135 : Blo 1327482 1328135 := bstep (se 1 (by rfl) ⟨996101, by rfl⟩ : syracuseStep 1328135 = 1992203) B1992203
theorem B1328143 : Blo 1327482 1328143 := bstep (se 1 (by rfl) ⟨996107, by rfl⟩ : syracuseStep 1328143 = 1992215) B1992215
theorem B1991723 : Blo 1327482 1991723 := bstep (se 1 (by rfl) ⟨1493792, by rfl⟩ : syracuseStep 1991723 = 2987585) B2987585
theorem B1328187 : Blo 1327482 1328187 := bstep (se 1 (by rfl) ⟨996140, by rfl⟩ : syracuseStep 1328187 = 1992281) B1992281
theorem B1991753 : Blo 1327482 1991753 := bstep (se 2 (by rfl) ⟨746907, by rfl⟩ : syracuseStep 1991753 = 1493815) B1493815
theorem B1328263 : Blo 1327482 1328263 := bstep (se 1 (by rfl) ⟨996197, by rfl⟩ : syracuseStep 1328263 = 1992395) B1992395
theorem B1680527 : Blo 1327482 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B1328271 : Blo 1327482 1328271 := bstep (se 1 (by rfl) ⟨996203, by rfl⟩ : syracuseStep 1328271 = 1992407) B1992407
theorem B2393273 : Blo 1327482 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B1991867 : Blo 1327482 1991867 := bstep (se 1 (by rfl) ⟨1493900, by rfl⟩ : syracuseStep 1991867 = 2987801) B2987801
theorem B1328315 : Blo 1327482 1328315 := bstep (se 1 (by rfl) ⟨996236, by rfl⟩ : syracuseStep 1328315 = 1992473) B1992473
theorem B1991927 : Blo 1327482 1991927 := bstep (se 1 (by rfl) ⟨1493945, by rfl⟩ : syracuseStep 1991927 = 2987891) B2987891
theorem B1328391 : Blo 1327482 1328391 := bstep (se 1 (by rfl) ⟨996293, by rfl⟩ : syracuseStep 1328391 = 1992587) B1992587
theorem B1991951 : Blo 1327482 1991951 := bstep (se 1 (by rfl) ⟨1493963, by rfl⟩ : syracuseStep 1991951 = 2987927) B2987927
theorem B1328399 : Blo 1327482 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B1991993 : Blo 1327482 1991993 := bstep (se 2 (by rfl) ⟨746997, by rfl⟩ : syracuseStep 1991993 = 1493995) B1493995
theorem B7562555 : Blo 1327482 7562555 := bstep (se 1 (by rfl) ⟨5671916, by rfl⟩ : syracuseStep 7562555 = 11343833) B11343833
theorem B1328443 : Blo 1327482 1328443 := bstep (se 1 (by rfl) ⟨996332, by rfl⟩ : syracuseStep 1328443 = 1992665) B1992665
theorem B1992071 : Blo 1327482 1992071 := bstep (se 1 (by rfl) ⟨1494053, by rfl⟩ : syracuseStep 1992071 = 2988107) B2988107
theorem B1328519 : Blo 1327482 1328519 := bstep (se 1 (by rfl) ⟨996389, by rfl⟩ : syracuseStep 1328519 = 1992779) B1992779
theorem B3835271 : Blo 1327482 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B1328527 : Blo 1327482 1328527 := bstep (se 1 (by rfl) ⟨996395, by rfl⟩ : syracuseStep 1328527 = 1992791) B1992791
theorem B1992107 : Blo 1327482 1992107 := bstep (se 1 (by rfl) ⟨1494080, by rfl⟩ : syracuseStep 1992107 = 2988161) B2988161
theorem B1328571 : Blo 1327482 1328571 := bstep (se 1 (by rfl) ⟨996428, by rfl⟩ : syracuseStep 1328571 = 1992857) B1992857
theorem B1992137 : Blo 1327482 1992137 := bstep (se 2 (by rfl) ⟨747051, by rfl⟩ : syracuseStep 1992137 = 1494103) B1494103
theorem B1328647 : Blo 1327482 1328647 := bstep (se 1 (by rfl) ⟨996485, by rfl⟩ : syracuseStep 1328647 = 1992971) B1992971
theorem B1328655 : Blo 1327482 1328655 := bstep (se 1 (by rfl) ⟨996491, by rfl⟩ : syracuseStep 1328655 = 1992983) B1992983
theorem B6727211 : Blo 1327482 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B1992251 : Blo 1327482 1992251 := bstep (se 1 (by rfl) ⟨1494188, by rfl⟩ : syracuseStep 1992251 = 2988377) B2988377
theorem B1328699 : Blo 1327482 1328699 := bstep (se 1 (by rfl) ⟨996524, by rfl⟩ : syracuseStep 1328699 = 1993049) B1993049
theorem B11347523 : Blo 1327482 11347523 := bstep (se 1 (by rfl) ⟨8510642, by rfl⟩ : syracuseStep 11347523 = 17021285) B17021285
theorem B4482647 : Blo 1327482 4482647 := bstep (se 1 (by rfl) ⟨3361985, by rfl⟩ : syracuseStep 4482647 = 6723971) B6723971
theorem B1992311 : Blo 1327482 1992311 := bstep (se 1 (by rfl) ⟨1494233, by rfl⟩ : syracuseStep 1992311 = 2988467) B2988467
theorem B1328775 : Blo 1327482 1328775 := bstep (se 1 (by rfl) ⟨996581, by rfl⟩ : syracuseStep 1328775 = 1993163) B1993163
theorem B1992335 : Blo 1327482 1992335 := bstep (se 1 (by rfl) ⟨1494251, by rfl⟩ : syracuseStep 1992335 = 2988503) B2988503
theorem B1328783 : Blo 1327482 1328783 := bstep (se 1 (by rfl) ⟨996587, by rfl⟩ : syracuseStep 1328783 = 1993175) B1993175
theorem B1992377 : Blo 1327482 1992377 := bstep (se 2 (by rfl) ⟨747141, by rfl⟩ : syracuseStep 1992377 = 1494283) B1494283
theorem B1328827 : Blo 1327482 1328827 := bstep (se 1 (by rfl) ⟨996620, by rfl⟩ : syracuseStep 1328827 = 1993241) B1993241
theorem B1992455 : Blo 1327482 1992455 := bstep (se 1 (by rfl) ⟨1494341, by rfl⟩ : syracuseStep 1992455 = 2988683) B2988683
theorem B1328903 : Blo 1327482 1328903 := bstep (se 1 (by rfl) ⟨996677, by rfl⟩ : syracuseStep 1328903 = 1993355) B1993355
theorem B1328911 : Blo 1327482 1328911 := bstep (se 1 (by rfl) ⟨996683, by rfl⟩ : syracuseStep 1328911 = 1993367) B1993367
theorem B1992491 : Blo 1327482 1992491 := bstep (se 1 (by rfl) ⟨1494368, by rfl⟩ : syracuseStep 1992491 = 2988737) B2988737
theorem B1328955 : Blo 1327482 1328955 := bstep (se 1 (by rfl) ⟨996716, by rfl⟩ : syracuseStep 1328955 = 1993433) B1993433
theorem B1992521 : Blo 1327482 1992521 := bstep (se 2 (by rfl) ⟨747195, by rfl⟩ : syracuseStep 1992521 = 1494391) B1494391
theorem B3360599 : Blo 1327482 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B4786073 : Blo 1327482 4786073 := bstep (se 2 (by rfl) ⟨1794777, by rfl⟩ : syracuseStep 4786073 = 3589555) B3589555
theorem B1992635 : Blo 1327482 1992635 := bstep (se 1 (by rfl) ⟨1494476, by rfl⟩ : syracuseStep 1992635 = 2988953) B2988953
theorem B1992695 : Blo 1327482 1992695 := bstep (se 1 (by rfl) ⟨1494521, by rfl⟩ : syracuseStep 1992695 = 2989043) B2989043
theorem B14354443 : Blo 1327482 14354443 := bstep (se 1 (by rfl) ⟨10765832, by rfl⟩ : syracuseStep 14354443 = 21531665) B21531665
theorem B1992719 : Blo 1327482 1992719 := bstep (se 1 (by rfl) ⟨1494539, by rfl⟩ : syracuseStep 1992719 = 2989079) B2989079
theorem B3360811 : Blo 1327482 3360811 := bstep (se 1 (by rfl) ⟨2520608, by rfl⟩ : syracuseStep 3360811 = 5041217) B5041217
theorem B1992761 : Blo 1327482 1992761 := bstep (se 2 (by rfl) ⟨747285, by rfl⟩ : syracuseStep 1992761 = 1494571) B1494571
theorem B4483133 : Blo 1327482 4483133 := bstep (se 3 (by rfl) ⟨840587, by rfl⟩ : syracuseStep 4483133 = 1681175) B1681175
theorem B1992839 : Blo 1327482 1992839 := bstep (se 1 (by rfl) ⟨1494629, by rfl⟩ : syracuseStep 1992839 = 2989259) B2989259
theorem B1992875 : Blo 1327482 1992875 := bstep (se 1 (by rfl) ⟨1494656, by rfl⟩ : syracuseStep 1992875 = 2989313) B2989313
theorem B3360953 : Blo 1327482 3360953 := bstep (se 2 (by rfl) ⟨1260357, by rfl⟩ : syracuseStep 3360953 = 2520715) B2520715
theorem B1992905 : Blo 1327482 1992905 := bstep (se 2 (by rfl) ⟨747339, by rfl⟩ : syracuseStep 1992905 = 1494679) B1494679
theorem B6056207 : Blo 1327482 6056207 := bstep (se 1 (by rfl) ⟨4542155, by rfl⟩ : syracuseStep 6056207 = 9084311) B9084311
theorem B7563557 : Blo 1327482 7563557 := bstep (se 4 (by rfl) ⟨709083, by rfl⟩ : syracuseStep 7563557 = 1418167) B1418167
theorem B1993019 : Blo 1327482 1993019 := bstep (se 1 (by rfl) ⟨1494764, by rfl⟩ : syracuseStep 1993019 = 2989529) B2989529
theorem B1993079 : Blo 1327482 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B1993103 : Blo 1327482 1993103 := bstep (se 1 (by rfl) ⟨1494827, by rfl⟩ : syracuseStep 1993103 = 2989655) B2989655
theorem B1993145 : Blo 1327482 1993145 := bstep (se 2 (by rfl) ⟨747429, by rfl⟩ : syracuseStep 1993145 = 1494859) B1494859
theorem B1993223 : Blo 1327482 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B2837035 : Blo 1327482 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B12118571 : Blo 1327482 12118571 := bstep (se 1 (by rfl) ⟨9088928, by rfl⟩ : syracuseStep 12118571 = 18177857) B18177857
theorem B1993259 : Blo 1327482 1993259 := bstep (se 1 (by rfl) ⟨1494944, by rfl⟩ : syracuseStep 1993259 = 2989889) B2989889
theorem B1493563 : Blo 1327482 1493563 := bstep (se 1 (by rfl) ⟨1120172, by rfl⟩ : syracuseStep 1493563 = 2240345) B2240345
theorem B5040701 : Blo 1327482 5040701 := bstep (se 3 (by rfl) ⟨945131, by rfl⟩ : syracuseStep 5040701 = 1890263) B1890263
theorem B1993289 : Blo 1327482 1993289 := bstep (se 2 (by rfl) ⟨747483, by rfl⟩ : syracuseStep 1993289 = 1494967) B1494967
theorem B1993403 : Blo 1327482 1993403 := bstep (se 1 (by rfl) ⟨1495052, by rfl⟩ : syracuseStep 1993403 = 2990105) B2990105
theorem B7564013 : Blo 1327482 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B1993463 : Blo 1327482 1993463 := bstep (se 1 (by rfl) ⟨1495097, by rfl⟩ : syracuseStep 1993463 = 2990195) B2990195
theorem B39906053 : Blo 1327482 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B64621475 : Blo 1327482 64621475 := bstep (se 1 (by rfl) ⟨48466106, by rfl⟩ : syracuseStep 64621475 = 96932213) B96932213
theorem B3640249 : Blo 1327482 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B1494031 : Blo 1327482 1494031 := bstep (se 1 (by rfl) ⟨1120523, by rfl⟩ : syracuseStep 1494031 = 2241047) B2241047
theorem B3361945 : Blo 1327482 3361945 := bstep (se 2 (by rfl) ⟨1260729, by rfl⟩ : syracuseStep 3361945 = 2521459) B2521459
theorem B3362107 : Blo 1327482 3362107 := bstep (se 1 (by rfl) ⟨2521580, by rfl⟩ : syracuseStep 3362107 = 5043161) B5043161
theorem B7564697 : Blo 1327482 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B4484537 : Blo 1327482 4484537 := bstep (se 2 (by rfl) ⟨1681701, by rfl⟩ : syracuseStep 4484537 = 3363403) B3363403
theorem B3362249 : Blo 1327482 3362249 := bstep (se 2 (by rfl) ⟨1260843, by rfl⟩ : syracuseStep 3362249 = 2521687) B2521687
theorem B6057425 : Blo 1327482 6057425 := bstep (se 2 (by rfl) ⟨2271534, by rfl⟩ : syracuseStep 6057425 = 4543069) B4543069
theorem B10087901 : Blo 1327482 10087901 := bstep (se 3 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 10087901 = 3782963) B3782963
theorem B1494535 : Blo 1327482 1494535 := bstep (se 1 (by rfl) ⟨1120901, by rfl⟩ : syracuseStep 1494535 = 2241803) B2241803
theorem B6385175 : Blo 1327482 6385175 := bstep (se 1 (by rfl) ⟨4788881, by rfl⟩ : syracuseStep 6385175 = 9577763) B9577763
theorem B1494715 : Blo 1327482 1494715 := bstep (se 1 (by rfl) ⟨1121036, by rfl⟩ : syracuseStep 1494715 = 2242073) B2242073
theorem B6721217 : Blo 1327482 6721217 := bstep (se 2 (by rfl) ⟨2520456, by rfl⟩ : syracuseStep 6721217 = 5040913) B5040913
theorem B16158437 : Blo 1327482 16158437 := bstep (se 4 (by rfl) ⟨1514853, by rfl⟩ : syracuseStep 16158437 = 3029707) B3029707
theorem B3362593 : Blo 1327482 3362593 := bstep (se 2 (by rfl) ⟨1260972, by rfl⟩ : syracuseStep 3362593 = 2521945) B2521945
theorem B8507339 : Blo 1327482 8507339 := bstep (se 1 (by rfl) ⟨6380504, by rfl⟩ : syracuseStep 8507339 = 12761009) B12761009
theorem B6385675 : Blo 1327482 6385675 := bstep (se 1 (by rfl) ⟨4789256, by rfl⟩ : syracuseStep 6385675 = 9578513) B9578513
theorem B4485131 : Blo 1327482 4485131 := bstep (se 1 (by rfl) ⟨3363848, by rfl⟩ : syracuseStep 4485131 = 6727697) B6727697
theorem B2240527 : Blo 1327482 2240527 := bstep (se 1 (by rfl) ⟨1680395, by rfl⟩ : syracuseStep 2240527 = 3360791) B3360791
theorem B3190799 : Blo 1327482 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B4493431 : Blo 1327482 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B4485239 : Blo 1327482 4485239 := bstep (se 1 (by rfl) ⟨3363929, by rfl⟩ : syracuseStep 4485239 = 6727859) B6727859
theorem B3363191 : Blo 1327482 3363191 := bstep (se 1 (by rfl) ⟨2522393, by rfl⟩ : syracuseStep 3363191 = 5044787) B5044787
theorem B3191329 : Blo 1327482 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B2241067 : Blo 1327482 2241067 := bstep (se 1 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 2241067 = 3361601) B3361601
theorem B3781255 : Blo 1327482 3781255 := bstep (se 1 (by rfl) ⟨2835941, by rfl⟩ : syracuseStep 3781255 = 5671883) B5671883
theorem B2241209 : Blo 1327482 2241209 := bstep (se 2 (by rfl) ⟨840453, by rfl⟩ : syracuseStep 2241209 = 1680907) B1680907
theorem B3781529 : Blo 1327482 3781529 := bstep (se 2 (by rfl) ⟨1418073, by rfl⟩ : syracuseStep 3781529 = 2836147) B2836147
theorem B2986937 : Blo 1327482 2986937 := bstep (se 2 (by rfl) ⟨1120101, by rfl⟩ : syracuseStep 2986937 = 2240203) B2240203
theorem B6722513 : Blo 1327482 6722513 := bstep (se 2 (by rfl) ⟨2520942, by rfl⟩ : syracuseStep 6722513 = 5041885) B5041885
theorem B36844631 : Blo 1327482 36844631 := bstep (se 1 (by rfl) ⟨27633473, by rfl⟩ : syracuseStep 36844631 = 55266947) B55266947
theorem B8082605 : Blo 1327482 8082605 := bstep (se 3 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 8082605 = 3030977) B3030977
theorem B2520335 : Blo 1327482 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B2987279 : Blo 1327482 2987279 := bstep (se 1 (by rfl) ⟨2240459, by rfl⟩ : syracuseStep 2987279 = 4480919) B4480919
theorem B2692367 : Blo 1327482 2692367 := bstep (se 1 (by rfl) ⟨2019275, by rfl⟩ : syracuseStep 2692367 = 4038551) B4038551
theorem B2987297 : Blo 1327482 2987297 := bstep (se 2 (by rfl) ⟨1120236, by rfl⟩ : syracuseStep 2987297 = 2240473) B2240473
theorem B2241911 : Blo 1327482 2241911 := bstep (se 1 (by rfl) ⟨1681433, by rfl⟩ : syracuseStep 2241911 = 3362867) B3362867
theorem B21018041 : Blo 1327482 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B5387705 : Blo 1327482 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B2987639 : Blo 1327482 2987639 := bstep (se 1 (by rfl) ⟨2240729, by rfl⟩ : syracuseStep 2987639 = 4481459) B4481459
theorem B2520875 : Blo 1327482 2520875 := bstep (se 1 (by rfl) ⟨1890656, by rfl⟩ : syracuseStep 2520875 = 3781313) B3781313
theorem B2987819 : Blo 1327482 2987819 := bstep (se 1 (by rfl) ⟨2240864, by rfl⟩ : syracuseStep 2987819 = 4481729) B4481729
theorem B6469427 : Blo 1327482 6469427 := bstep (se 1 (by rfl) ⟨4852070, by rfl⟩ : syracuseStep 6469427 = 9704141) B9704141
theorem B2242363 : Blo 1327482 2242363 := bstep (se 1 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 2242363 = 3363545) B3363545
theorem B11351897 : Blo 1327482 11351897 := bstep (se 2 (by rfl) ⟨4256961, by rfl⟩ : syracuseStep 11351897 = 8513923) B8513923
theorem B5044103 : Blo 1327482 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B1595323 : Blo 1327482 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B2242505 : Blo 1327482 2242505 := bstep (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) B1681879
theorem B3782771 : Blo 1327482 3782771 := bstep (se 1 (by rfl) ⟨2837078, by rfl⟩ : syracuseStep 3782771 = 5674157) B5674157
theorem B2766967 : Blo 1327482 2766967 := bstep (se 1 (by rfl) ⟨2075225, by rfl⟩ : syracuseStep 2766967 = 4150451) B4150451
theorem B2988179 : Blo 1327482 2988179 := bstep (se 1 (by rfl) ⟨2241134, by rfl⟩ : syracuseStep 2988179 = 4482269) B4482269
theorem B2988233 : Blo 1327482 2988233 := bstep (se 2 (by rfl) ⟨1120587, by rfl⟩ : syracuseStep 2988233 = 2241175) B2241175
theorem B1595707 : Blo 1327482 1595707 := bstep (se 1 (by rfl) ⟨1196780, by rfl⟩ : syracuseStep 1595707 = 2393561) B2393561
theorem B2128187 : Blo 1327482 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B4544903 : Blo 1327482 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B6379985 : Blo 1327482 6379985 := bstep (se 2 (by rfl) ⟨2392494, by rfl⟩ : syracuseStep 6379985 = 4784989) B4784989
theorem B8542763 : Blo 1327482 8542763 := bstep (se 1 (by rfl) ⟨6407072, by rfl⟩ : syracuseStep 8542763 = 12814145) B12814145
theorem B9214721 : Blo 1327482 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B5184271 : Blo 1327482 5184271 := bstep (se 1 (by rfl) ⟨3888203, by rfl⟩ : syracuseStep 5184271 = 7776407) B7776407
theorem B1891129 : Blo 1327482 1891129 := bstep (se 2 (by rfl) ⟨709173, by rfl⟩ : syracuseStep 1891129 = 1418347) B1418347
theorem B2988935 : Blo 1327482 2988935 := bstep (se 1 (by rfl) ⟨2241701, by rfl⟩ : syracuseStep 2988935 = 4483403) B4483403
theorem B2521991 : Blo 1327482 2521991 := bstep (se 1 (by rfl) ⟨1891493, by rfl⟩ : syracuseStep 2521991 = 3782987) B3782987
theorem B7568387 : Blo 1327482 7568387 := bstep (se 1 (by rfl) ⟨5676290, by rfl⟩ : syracuseStep 7568387 = 11352581) B11352581
theorem B20438021 : Blo 1327482 20438021 := bstep (se 4 (by rfl) ⟨1916064, by rfl⟩ : syracuseStep 20438021 = 3832129) B3832129
theorem B6724619 : Blo 1327482 6724619 := bstep (se 1 (by rfl) ⟨5043464, by rfl⟩ : syracuseStep 6724619 = 10086929) B10086929
theorem B2989115 : Blo 1327482 2989115 := bstep (se 1 (by rfl) ⟨2241836, by rfl⟩ : syracuseStep 2989115 = 4483673) B4483673
theorem B9337943 : Blo 1327482 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B6724781 : Blo 1327482 6724781 := bstep (se 3 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 6724781 = 2521793) B2521793
theorem B2989241 : Blo 1327482 2989241 := bstep (se 2 (by rfl) ⟨1120965, by rfl⟩ : syracuseStep 2989241 = 2241931) B2241931
theorem B4480271 : Blo 1327482 4480271 := bstep (se 1 (by rfl) ⟨3360203, by rfl⟩ : syracuseStep 4480271 = 6720407) B6720407
theorem B12279185 : Blo 1327482 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B2522515 : Blo 1327482 2522515 := bstep (se 1 (by rfl) ⟨1891886, by rfl⟩ : syracuseStep 2522515 = 3783773) B3783773
theorem B2989583 : Blo 1327482 2989583 := bstep (se 1 (by rfl) ⟨2242187, by rfl⟩ : syracuseStep 2989583 = 4484375) B4484375
theorem B4480541 : Blo 1327482 4480541 := bstep (se 3 (by rfl) ⟨840101, by rfl⟩ : syracuseStep 4480541 = 1680203) B1680203
theorem B2989601 : Blo 1327482 2989601 := bstep (se 2 (by rfl) ⟨1121100, by rfl⟩ : syracuseStep 2989601 = 2242201) B2242201
theorem B4546135 : Blo 1327482 4546135 := bstep (se 1 (by rfl) ⟨3409601, by rfl⟩ : syracuseStep 4546135 = 6819203) B6819203
theorem B7560823 : Blo 1327482 7560823 := bstep (se 1 (by rfl) ⟨5670617, by rfl⟩ : syracuseStep 7560823 = 11341235) B11341235
theorem B72720179 : Blo 1327482 72720179 := bstep (se 1 (by rfl) ⟨54540134, by rfl⟩ : syracuseStep 72720179 = 109080269) B109080269
theorem B2989943 : Blo 1327482 2989943 := bstep (se 1 (by rfl) ⟨2242457, by rfl⟩ : syracuseStep 2989943 = 4484915) B4484915
theorem B2990087 : Blo 1327482 2990087 := bstep (se 1 (by rfl) ⟨2242565, by rfl⟩ : syracuseStep 2990087 = 4485131) B4485131
theorem B4481081 : Blo 1327482 4481081 := bstep (se 2 (by rfl) ⟨1680405, by rfl⟩ : syracuseStep 4481081 = 3360811) B3360811
theorem B2990159 : Blo 1327482 2990159 := bstep (se 1 (by rfl) ⟨2242619, by rfl⟩ : syracuseStep 2990159 = 4485239) B4485239
theorem B2392235 : Blo 1327482 2392235 := bstep (se 1 (by rfl) ⟨1794176, by rfl⟩ : syracuseStep 2392235 = 3588353) B3588353
theorem B1327483 : Blo 1327482 1327483 := bstep (se 1 (by rfl) ⟨995612, by rfl⟩ : syracuseStep 1327483 = 1991225) B1991225
theorem B4481405 : Blo 1327482 4481405 := bstep (se 3 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 4481405 = 1680527) B1680527
theorem B1327535 : Blo 1327482 1327535 := bstep (se 1 (by rfl) ⟨995651, by rfl⟩ : syracuseStep 1327535 = 1991303) B1991303
theorem B1327559 : Blo 1327482 1327559 := bstep (se 1 (by rfl) ⟨995669, by rfl⟩ : syracuseStep 1327559 = 1991339) B1991339
theorem B1327579 : Blo 1327482 1327579 := bstep (se 1 (by rfl) ⟨995684, by rfl⟩ : syracuseStep 1327579 = 1991369) B1991369
theorem B6382061 : Blo 1327482 6382061 := bstep (se 3 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 6382061 = 2393273) B2393273
theorem B1327655 : Blo 1327482 1327655 := bstep (se 1 (by rfl) ⟨995741, by rfl⟩ : syracuseStep 1327655 = 1991483) B1991483
theorem B1327695 : Blo 1327482 1327695 := bstep (se 1 (by rfl) ⟨995771, by rfl⟩ : syracuseStep 1327695 = 1991543) B1991543
theorem B1327711 : Blo 1327482 1327711 := bstep (se 1 (by rfl) ⟨995783, by rfl⟩ : syracuseStep 1327711 = 1991567) B1991567
theorem B1991291 : Blo 1327482 1991291 := bstep (se 1 (by rfl) ⟨1493468, by rfl⟩ : syracuseStep 1991291 = 2986937) B2986937
theorem B1327739 : Blo 1327482 1327739 := bstep (se 1 (by rfl) ⟨995804, by rfl⟩ : syracuseStep 1327739 = 1991609) B1991609
theorem B4481675 : Blo 1327482 4481675 := bstep (se 1 (by rfl) ⟨3361256, by rfl⟩ : syracuseStep 4481675 = 6722513) B6722513
theorem B1327791 : Blo 1327482 1327791 := bstep (se 1 (by rfl) ⟨995843, by rfl⟩ : syracuseStep 1327791 = 1991687) B1991687
theorem B1327815 : Blo 1327482 1327815 := bstep (se 1 (by rfl) ⟨995861, by rfl⟩ : syracuseStep 1327815 = 1991723) B1991723
theorem B1327835 : Blo 1327482 1327835 := bstep (se 1 (by rfl) ⟨995876, by rfl⟩ : syracuseStep 1327835 = 1991753) B1991753
theorem B1991417 : Blo 1327482 1991417 := bstep (se 2 (by rfl) ⟨746781, by rfl⟩ : syracuseStep 1991417 = 1493563) B1493563
theorem B1327911 : Blo 1327482 1327911 := bstep (se 1 (by rfl) ⟨995933, by rfl⟩ : syracuseStep 1327911 = 1991867) B1991867
theorem B1327951 : Blo 1327482 1327951 := bstep (se 1 (by rfl) ⟨995963, by rfl⟩ : syracuseStep 1327951 = 1991927) B1991927
theorem B1991519 : Blo 1327482 1991519 := bstep (se 1 (by rfl) ⟨1493639, by rfl⟩ : syracuseStep 1991519 = 2987279) B2987279
theorem B1327967 : Blo 1327482 1327967 := bstep (se 1 (by rfl) ⟨995975, by rfl⟩ : syracuseStep 1327967 = 1991951) B1991951
theorem B1794911 : Blo 1327482 1794911 := bstep (se 1 (by rfl) ⟨1346183, by rfl⟩ : syracuseStep 1794911 = 2692367) B2692367
theorem B1991531 : Blo 1327482 1991531 := bstep (se 1 (by rfl) ⟨1493648, by rfl⟩ : syracuseStep 1991531 = 2987297) B2987297
theorem B1327995 : Blo 1327482 1327995 := bstep (se 1 (by rfl) ⟨995996, by rfl⟩ : syracuseStep 1327995 = 1991993) B1991993
theorem B1328047 : Blo 1327482 1328047 := bstep (se 1 (by rfl) ⟨996035, by rfl⟩ : syracuseStep 1328047 = 1992071) B1992071
theorem B2556847 : Blo 1327482 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B1328071 : Blo 1327482 1328071 := bstep (se 1 (by rfl) ⟨996053, by rfl⟩ : syracuseStep 1328071 = 1992107) B1992107
theorem B1328091 : Blo 1327482 1328091 := bstep (se 1 (by rfl) ⟨996068, by rfl⟩ : syracuseStep 1328091 = 1992137) B1992137
theorem B1328167 : Blo 1327482 1328167 := bstep (se 1 (by rfl) ⟨996125, by rfl⟩ : syracuseStep 1328167 = 1992251) B1992251
theorem B1991759 : Blo 1327482 1991759 := bstep (se 1 (by rfl) ⟨1493819, by rfl⟩ : syracuseStep 1991759 = 2987639) B2987639
theorem B1328207 : Blo 1327482 1328207 := bstep (se 1 (by rfl) ⟨996155, by rfl⟩ : syracuseStep 1328207 = 1992311) B1992311
theorem B1328223 : Blo 1327482 1328223 := bstep (se 1 (by rfl) ⟨996167, by rfl⟩ : syracuseStep 1328223 = 1992335) B1992335
theorem B1328251 : Blo 1327482 1328251 := bstep (se 1 (by rfl) ⟨996188, by rfl⟩ : syracuseStep 1328251 = 1992377) B1992377
theorem B1328303 : Blo 1327482 1328303 := bstep (se 1 (by rfl) ⟨996227, by rfl⟩ : syracuseStep 1328303 = 1992455) B1992455
theorem B1680583 : Blo 1327482 1680583 := bstep (se 1 (by rfl) ⟨1260437, by rfl⟩ : syracuseStep 1680583 = 2520875) B2520875
theorem B1991879 : Blo 1327482 1991879 := bstep (se 1 (by rfl) ⟨1493909, by rfl⟩ : syracuseStep 1991879 = 2987819) B2987819
theorem B1328327 : Blo 1327482 1328327 := bstep (se 1 (by rfl) ⟨996245, by rfl⟩ : syracuseStep 1328327 = 1992491) B1992491
theorem B1328347 : Blo 1327482 1328347 := bstep (se 1 (by rfl) ⟨996260, by rfl⟩ : syracuseStep 1328347 = 1992521) B1992521
theorem B1328423 : Blo 1327482 1328423 := bstep (se 1 (by rfl) ⟨996317, by rfl⟩ : syracuseStep 1328423 = 1992635) B1992635
theorem B1328463 : Blo 1327482 1328463 := bstep (se 1 (by rfl) ⟨996347, by rfl⟩ : syracuseStep 1328463 = 1992695) B1992695
theorem B1328479 : Blo 1327482 1328479 := bstep (se 1 (by rfl) ⟨996359, by rfl⟩ : syracuseStep 1328479 = 1992719) B1992719
theorem B1992041 : Blo 1327482 1992041 := bstep (se 2 (by rfl) ⟨747015, by rfl⟩ : syracuseStep 1992041 = 1494031) B1494031
theorem B1328507 : Blo 1327482 1328507 := bstep (se 1 (by rfl) ⟨996380, by rfl⟩ : syracuseStep 1328507 = 1992761) B1992761
theorem B1328559 : Blo 1327482 1328559 := bstep (se 1 (by rfl) ⟨996419, by rfl⟩ : syracuseStep 1328559 = 1992839) B1992839
theorem B1992119 : Blo 1327482 1992119 := bstep (se 1 (by rfl) ⟨1494089, by rfl⟩ : syracuseStep 1992119 = 2988179) B2988179
theorem B1328583 : Blo 1327482 1328583 := bstep (se 1 (by rfl) ⟨996437, by rfl⟩ : syracuseStep 1328583 = 1992875) B1992875
theorem B1992155 : Blo 1327482 1992155 := bstep (se 1 (by rfl) ⟨1494116, by rfl⟩ : syracuseStep 1992155 = 2988233) B2988233
theorem B1328603 : Blo 1327482 1328603 := bstep (se 1 (by rfl) ⟨996452, by rfl⟩ : syracuseStep 1328603 = 1992905) B1992905
theorem B4482593 : Blo 1327482 4482593 := bstep (se 2 (by rfl) ⟨1680972, by rfl⟩ : syracuseStep 4482593 = 3361945) B3361945
theorem B1418791 : Blo 1327482 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B1328679 : Blo 1327482 1328679 := bstep (se 1 (by rfl) ⟨996509, by rfl⟩ : syracuseStep 1328679 = 1993019) B1993019
theorem B1328719 : Blo 1327482 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B1328735 : Blo 1327482 1328735 := bstep (se 1 (by rfl) ⟨996551, by rfl⟩ : syracuseStep 1328735 = 1993103) B1993103
theorem B1328763 : Blo 1327482 1328763 := bstep (se 1 (by rfl) ⟨996572, by rfl⟩ : syracuseStep 1328763 = 1993145) B1993145
theorem B4253323 : Blo 1327482 4253323 := bstep (se 1 (by rfl) ⟨3189992, by rfl⟩ : syracuseStep 4253323 = 6379985) B6379985
theorem B1328815 : Blo 1327482 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B5695175 : Blo 1327482 5695175 := bstep (se 1 (by rfl) ⟨4271381, by rfl⟩ : syracuseStep 5695175 = 8542763) B8542763
theorem B8079047 : Blo 1327482 8079047 := bstep (se 1 (by rfl) ⟨6059285, by rfl⟩ : syracuseStep 8079047 = 12118571) B12118571
theorem B1328839 : Blo 1327482 1328839 := bstep (se 1 (by rfl) ⟨996629, by rfl⟩ : syracuseStep 1328839 = 1993259) B1993259
theorem B3360467 : Blo 1327482 3360467 := bstep (se 1 (by rfl) ⟨2520350, by rfl⟩ : syracuseStep 3360467 = 5040701) B5040701
theorem B1328859 : Blo 1327482 1328859 := bstep (se 1 (by rfl) ⟨996644, by rfl⟩ : syracuseStep 1328859 = 1993289) B1993289
theorem B4482809 : Blo 1327482 4482809 := bstep (se 2 (by rfl) ⟨1681053, by rfl⟩ : syracuseStep 4482809 = 3362107) B3362107
theorem B1328935 : Blo 1327482 1328935 := bstep (se 1 (by rfl) ⟨996701, by rfl⟩ : syracuseStep 1328935 = 1993403) B1993403
theorem B1328975 : Blo 1327482 1328975 := bstep (se 1 (by rfl) ⟨996731, by rfl⟩ : syracuseStep 1328975 = 1993463) B1993463
theorem B1992623 : Blo 1327482 1992623 := bstep (se 1 (by rfl) ⟨1494467, by rfl⟩ : syracuseStep 1992623 = 2988935) B2988935
theorem B1681327 : Blo 1327482 1681327 := bstep (se 1 (by rfl) ⟨1260995, by rfl⟩ : syracuseStep 1681327 = 2521991) B2521991
theorem B13625347 : Blo 1327482 13625347 := bstep (se 1 (by rfl) ⟨10219010, by rfl⟩ : syracuseStep 13625347 = 20438021) B20438021
theorem B4483079 : Blo 1327482 4483079 := bstep (se 1 (by rfl) ⟨3362309, by rfl⟩ : syracuseStep 4483079 = 6724619) B6724619
theorem B1992713 : Blo 1327482 1992713 := bstep (se 2 (by rfl) ⟨747267, by rfl⟩ : syracuseStep 1992713 = 1494535) B1494535
theorem B1992743 : Blo 1327482 1992743 := bstep (se 1 (by rfl) ⟨1494557, by rfl⟩ : syracuseStep 1992743 = 2989115) B2989115
theorem B4483187 : Blo 1327482 4483187 := bstep (se 1 (by rfl) ⟨3362390, by rfl⟩ : syracuseStep 4483187 = 6724781) B6724781
theorem B1992827 : Blo 1327482 1992827 := bstep (se 1 (by rfl) ⟨1494620, by rfl⟩ : syracuseStep 1992827 = 2989241) B2989241
theorem B1992953 : Blo 1327482 1992953 := bstep (se 2 (by rfl) ⟨747357, by rfl⟩ : syracuseStep 1992953 = 1494715) B1494715
theorem B8186123 : Blo 1327482 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B1993055 : Blo 1327482 1993055 := bstep (se 1 (by rfl) ⟨1494791, by rfl⟩ : syracuseStep 1993055 = 2989583) B2989583
theorem B1993067 : Blo 1327482 1993067 := bstep (se 1 (by rfl) ⟨1494800, by rfl⟩ : syracuseStep 1993067 = 2989601) B2989601
theorem B4483457 : Blo 1327482 4483457 := bstep (se 2 (by rfl) ⟨1681296, by rfl⟩ : syracuseStep 4483457 = 3362593) B3362593
theorem B1993295 : Blo 1327482 1993295 := bstep (se 1 (by rfl) ⟨1494971, by rfl⟩ : syracuseStep 1993295 = 2989943) B2989943
theorem B5671559 : Blo 1327482 5671559 := bstep (se 1 (by rfl) ⟨4253669, by rfl⟩ : syracuseStep 5671559 = 8507339) B8507339
theorem B19139257 : Blo 1327482 19139257 := bstep (se 2 (by rfl) ⟨7177221, by rfl⟩ : syracuseStep 19139257 = 14354443) B14354443
theorem B8514233 : Blo 1327482 8514233 := bstep (se 2 (by rfl) ⟨3192837, by rfl⟩ : syracuseStep 8514233 = 6385675) B6385675
theorem B1993415 : Blo 1327482 1993415 := bstep (se 1 (by rfl) ⟨1495061, by rfl⟩ : syracuseStep 1993415 = 2990123) B2990123
theorem B5991241 : Blo 1327482 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B25537463 : Blo 1327482 25537463 := bstep (se 1 (by rfl) ⟨19153097, by rfl⟩ : syracuseStep 25537463 = 38306195) B38306195
theorem B1494139 : Blo 1327482 1494139 := bstep (se 1 (by rfl) ⟨1120604, by rfl⟩ : syracuseStep 1494139 = 2241209) B2241209
theorem B4484267 : Blo 1327482 4484267 := bstep (se 1 (by rfl) ⟨3363200, by rfl⟩ : syracuseStep 4484267 = 6726401) B6726401
theorem B5041399 : Blo 1327482 5041399 := bstep (se 1 (by rfl) ⟨3781049, by rfl⟩ : syracuseStep 5041399 = 7562099) B7562099
theorem B32304419 : Blo 1327482 32304419 := bstep (se 1 (by rfl) ⟨24228314, by rfl⟩ : syracuseStep 32304419 = 48456629) B48456629
theorem B14757157 : Blo 1327482 14757157 := bstep (se 4 (by rfl) ⟨1383483, by rfl⟩ : syracuseStep 14757157 = 2766967) B2766967
theorem B6720893 : Blo 1327482 6720893 := bstep (se 3 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 6720893 = 2520335) B2520335
theorem B4255105 : Blo 1327482 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B24563087 : Blo 1327482 24563087 := bstep (se 1 (by rfl) ⟨18422315, by rfl⟩ : syracuseStep 24563087 = 36844631) B36844631
theorem B5041673 : Blo 1327482 5041673 := bstep (se 2 (by rfl) ⟨1890627, by rfl⟩ : syracuseStep 5041673 = 3781255) B3781255
theorem B5041703 : Blo 1327482 5041703 := bstep (se 1 (by rfl) ⟨3781277, by rfl⟩ : syracuseStep 5041703 = 7562555) B7562555
theorem B1494607 : Blo 1327482 1494607 := bstep (se 1 (by rfl) ⟨1120955, by rfl⟩ : syracuseStep 1494607 = 2241911) B2241911
theorem B14012027 : Blo 1327482 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B3591803 : Blo 1327482 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B4484807 : Blo 1327482 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B7565015 : Blo 1327482 7565015 := bstep (se 1 (by rfl) ⟨5673761, by rfl⟩ : syracuseStep 7565015 = 11347523) B11347523
theorem B2240399 : Blo 1327482 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B4853665 : Blo 1327482 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B3362735 : Blo 1327482 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B3190715 : Blo 1327482 3190715 := bstep (se 1 (by rfl) ⟨2393036, by rfl⟩ : syracuseStep 3190715 = 4786073) B4786073
theorem B1495003 : Blo 1327482 1495003 := bstep (se 1 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 1495003 = 2242505) B2242505
theorem B2240635 : Blo 1327482 2240635 := bstep (se 1 (by rfl) ⟨1680476, by rfl⟩ : syracuseStep 2240635 = 3360953) B3360953
theorem B5042371 : Blo 1327482 5042371 := bstep (se 1 (by rfl) ⟨3781778, by rfl⟩ : syracuseStep 5042371 = 7563557) B7563557
theorem B5042675 : Blo 1327482 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B26604035 : Blo 1327482 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B3363353 : Blo 1327482 3363353 := bstep (se 2 (by rfl) ⟨1261257, by rfl⟩ : syracuseStep 3363353 = 2522515) B2522515
theorem B10081097 : Blo 1327482 10081097 := bstep (se 2 (by rfl) ⟨3780411, by rfl⟩ : syracuseStep 10081097 = 7560823) B7560823
theorem B2986847 : Blo 1327482 2986847 := bstep (se 1 (by rfl) ⟨2240135, by rfl⟩ : syracuseStep 2986847 = 4480271) B4480271
theorem B5043131 : Blo 1327482 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B2241499 : Blo 1327482 2241499 := bstep (se 1 (by rfl) ⟨1681124, by rfl⟩ : syracuseStep 2241499 = 3362249) B3362249
theorem B4256783 : Blo 1327482 4256783 := bstep (se 1 (by rfl) ⟨3192587, by rfl⟩ : syracuseStep 4256783 = 6385175) B6385175
theorem B2987027 : Blo 1327482 2987027 := bstep (se 1 (by rfl) ⟨2240270, by rfl⟩ : syracuseStep 2987027 = 4480541) B4480541
theorem B2127097 : Blo 1327482 2127097 := bstep (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) B1595323
theorem B2987369 : Blo 1327482 2987369 := bstep (se 2 (by rfl) ⟨1120263, by rfl⟩ : syracuseStep 2987369 = 2240527) B2240527
theorem B4314473 : Blo 1327482 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B8508797 : Blo 1327482 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B12113315 : Blo 1327482 12113315 := bstep (se 1 (by rfl) ⟨9084986, by rfl⟩ : syracuseStep 12113315 = 18169973) B18169973
theorem B2242127 : Blo 1327482 2242127 := bstep (se 1 (by rfl) ⟨1681595, by rfl⟩ : syracuseStep 2242127 = 3363191) B3363191
theorem B24246053 : Blo 1327482 24246053 := bstep (se 4 (by rfl) ⟨2273067, by rfl⟩ : syracuseStep 24246053 = 4546135) B4546135
theorem B1890155 : Blo 1327482 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B2521019 : Blo 1327482 2521019 := bstep (se 1 (by rfl) ⟨1890764, by rfl⟩ : syracuseStep 2521019 = 3781529) B3781529
theorem B2987963 : Blo 1327482 2987963 := bstep (se 1 (by rfl) ⟨2240972, by rfl⟩ : syracuseStep 2987963 = 4481945) B4481945
theorem B2988089 : Blo 1327482 2988089 := bstep (se 2 (by rfl) ⟨1120533, by rfl⟩ : syracuseStep 2988089 = 2241067) B2241067
theorem B3782713 : Blo 1327482 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B5388403 : Blo 1327482 5388403 := bstep (se 1 (by rfl) ⟨4041302, by rfl⟩ : syracuseStep 5388403 = 8082605) B8082605
theorem B6912361 : Blo 1327482 6912361 := bstep (se 2 (by rfl) ⟨2592135, by rfl⟩ : syracuseStep 6912361 = 5184271) B5184271
theorem B2988431 : Blo 1327482 2988431 := bstep (se 1 (by rfl) ⟨2241323, by rfl⟩ : syracuseStep 2988431 = 4482647) B4482647
theorem B2521505 : Blo 1327482 2521505 := bstep (se 2 (by rfl) ⟨945564, by rfl⟩ : syracuseStep 2521505 = 1891129) B1891129
theorem B7567931 : Blo 1327482 7567931 := bstep (se 1 (by rfl) ⟨5675948, by rfl⟩ : syracuseStep 7567931 = 11351897) B11351897
theorem B2988755 : Blo 1327482 2988755 := bstep (se 1 (by rfl) ⟨2241566, by rfl⟩ : syracuseStep 2988755 = 4483133) B4483133
theorem B2521847 : Blo 1327482 2521847 := bstep (se 1 (by rfl) ⟨1891385, by rfl⟩ : syracuseStep 2521847 = 3782771) B3782771
theorem B4037471 : Blo 1327482 4037471 := bstep (se 1 (by rfl) ⟨3028103, by rfl⟩ : syracuseStep 4037471 = 6056207) B6056207
theorem B3029935 : Blo 1327482 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B8510437 : Blo 1327482 8510437 := bstep (se 4 (by rfl) ⟨797853, by rfl⟩ : syracuseStep 8510437 = 1595707) B1595707
theorem B6143147 : Blo 1327482 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B43080983 : Blo 1327482 43080983 := bstep (se 1 (by rfl) ⟨32310737, by rfl⟩ : syracuseStep 43080983 = 64621475) B64621475
theorem B5045591 : Blo 1327482 5045591 := bstep (se 1 (by rfl) ⟨3784193, by rfl⟩ : syracuseStep 5045591 = 7568387) B7568387
theorem B6225295 : Blo 1327482 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B17251805 : Blo 1327482 17251805 := bstep (se 3 (by rfl) ⟨3234713, by rfl⟩ : syracuseStep 17251805 = 6469427) B6469427
theorem B2989691 : Blo 1327482 2989691 := bstep (se 1 (by rfl) ⟨2242268, by rfl⟩ : syracuseStep 2989691 = 4484537) B4484537
theorem B4038283 : Blo 1327482 4038283 := bstep (se 1 (by rfl) ⟨3028712, by rfl⟩ : syracuseStep 4038283 = 6057425) B6057425
theorem B6725267 : Blo 1327482 6725267 := bstep (se 1 (by rfl) ⟨5043950, by rfl⟩ : syracuseStep 6725267 = 10087901) B10087901
theorem B2989817 : Blo 1327482 2989817 := bstep (se 2 (by rfl) ⟨1121181, by rfl⟩ : syracuseStep 2989817 = 2242363) B2242363
theorem B4480811 : Blo 1327482 4480811 := bstep (se 1 (by rfl) ⟨3360608, by rfl⟩ : syracuseStep 4480811 = 6721217) B6721217
theorem B10772291 : Blo 1327482 10772291 := bstep (se 1 (by rfl) ⟨8079218, by rfl⟩ : syracuseStep 10772291 = 16158437) B16158437
theorem B48480119 : Blo 1327482 48480119 := bstep (se 1 (by rfl) ⟨36360089, by rfl⟩ : syracuseStep 48480119 = 72720179) B72720179
theorem B7184537 : Blo 1327482 7184537 := bstep (se 2 (by rfl) ⟨2694201, by rfl⟩ : syracuseStep 7184537 = 5388403) B5388403
theorem B17736023 : Blo 1327482 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B1327527 : Blo 1327482 1327527 := bstep (se 1 (by rfl) ⟨995645, by rfl⟩ : syracuseStep 1327527 = 1991291) B1991291
theorem B9216481 : Blo 1327482 9216481 := bstep (se 2 (by rfl) ⟨3456180, by rfl⟩ : syracuseStep 9216481 = 6912361) B6912361
theorem B1327611 : Blo 1327482 1327611 := bstep (se 1 (by rfl) ⟨995708, by rfl⟩ : syracuseStep 1327611 = 1991417) B1991417
theorem B1991231 : Blo 1327482 1991231 := bstep (se 1 (by rfl) ⟨1493423, by rfl⟩ : syracuseStep 1991231 = 2986847) B2986847
theorem B1327679 : Blo 1327482 1327679 := bstep (se 1 (by rfl) ⟨995759, by rfl⟩ : syracuseStep 1327679 = 1991519) B1991519
theorem B1327687 : Blo 1327482 1327687 := bstep (se 1 (by rfl) ⟨995765, by rfl⟩ : syracuseStep 1327687 = 1991531) B1991531
theorem B1991351 : Blo 1327482 1991351 := bstep (se 1 (by rfl) ⟨1493513, by rfl⟩ : syracuseStep 1991351 = 2987027) B2987027
theorem B1327839 : Blo 1327482 1327839 := bstep (se 1 (by rfl) ⟨995879, by rfl⟩ : syracuseStep 1327839 = 1991759) B1991759
theorem B1327919 : Blo 1327482 1327919 := bstep (se 1 (by rfl) ⟨995939, by rfl⟩ : syracuseStep 1327919 = 1991879) B1991879
theorem B1991579 : Blo 1327482 1991579 := bstep (se 1 (by rfl) ⟨1493684, by rfl⟩ : syracuseStep 1991579 = 2987369) B2987369
theorem B1328027 : Blo 1327482 1328027 := bstep (se 1 (by rfl) ⟨996020, by rfl⟩ : syracuseStep 1328027 = 1992041) B1992041
theorem B2876315 : Blo 1327482 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B25519009 : Blo 1327482 25519009 := bstep (se 2 (by rfl) ⟨9569628, by rfl⟩ : syracuseStep 25519009 = 19139257) B19139257
theorem B1328079 : Blo 1327482 1328079 := bstep (se 1 (by rfl) ⟨996059, by rfl⟩ : syracuseStep 1328079 = 1992119) B1992119
theorem B1328103 : Blo 1327482 1328103 := bstep (se 1 (by rfl) ⟨996077, by rfl⟩ : syracuseStep 1328103 = 1992155) B1992155
theorem B19145717 : Blo 1327482 19145717 := bstep (se 5 (by rfl) ⟨897455, by rfl⟩ : syracuseStep 19145717 = 1794911) B1794911
theorem B7988321 : Blo 1327482 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B16164035 : Blo 1327482 16164035 := bstep (se 1 (by rfl) ⟨12123026, by rfl⟩ : syracuseStep 16164035 = 24246053) B24246053
theorem B4039913 : Blo 1327482 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B3409129 : Blo 1327482 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B1328415 : Blo 1327482 1328415 := bstep (se 1 (by rfl) ⟨996311, by rfl⟩ : syracuseStep 1328415 = 1992623) B1992623
theorem B1680679 : Blo 1327482 1680679 := bstep (se 1 (by rfl) ⟨1260509, by rfl⟩ : syracuseStep 1680679 = 2521019) B2521019
theorem B1991975 : Blo 1327482 1991975 := bstep (se 1 (by rfl) ⟨1493981, by rfl⟩ : syracuseStep 1991975 = 2987963) B2987963
theorem B11347249 : Blo 1327482 11347249 := bstep (se 2 (by rfl) ⟨4255218, by rfl⟩ : syracuseStep 11347249 = 8510437) B8510437
theorem B1328475 : Blo 1327482 1328475 := bstep (se 1 (by rfl) ⟨996356, by rfl⟩ : syracuseStep 1328475 = 1992713) B1992713
theorem B1328495 : Blo 1327482 1328495 := bstep (se 1 (by rfl) ⟨996371, by rfl⟩ : syracuseStep 1328495 = 1992743) B1992743
theorem B1992059 : Blo 1327482 1992059 := bstep (se 1 (by rfl) ⟨1494044, by rfl⟩ : syracuseStep 1992059 = 2988089) B2988089
theorem B1328551 : Blo 1327482 1328551 := bstep (se 1 (by rfl) ⟨996413, by rfl⟩ : syracuseStep 1328551 = 1992827) B1992827
theorem B1992185 : Blo 1327482 1992185 := bstep (se 2 (by rfl) ⟨747069, by rfl⟩ : syracuseStep 1992185 = 1494139) B1494139
theorem B1328635 : Blo 1327482 1328635 := bstep (se 1 (by rfl) ⟨996476, by rfl⟩ : syracuseStep 1328635 = 1992953) B1992953
theorem B5457415 : Blo 1327482 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B1328703 : Blo 1327482 1328703 := bstep (se 1 (by rfl) ⟨996527, by rfl⟩ : syracuseStep 1328703 = 1993055) B1993055
theorem B1328711 : Blo 1327482 1328711 := bstep (se 1 (by rfl) ⟨996533, by rfl⟩ : syracuseStep 1328711 = 1993067) B1993067
theorem B1992287 : Blo 1327482 1992287 := bstep (se 1 (by rfl) ⟨1494215, by rfl⟩ : syracuseStep 1992287 = 2988431) B2988431
theorem B1681003 : Blo 1327482 1681003 := bstep (se 1 (by rfl) ⟨1260752, by rfl⟩ : syracuseStep 1681003 = 2521505) B2521505
theorem B2836129 : Blo 1327482 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B1328863 : Blo 1327482 1328863 := bstep (se 1 (by rfl) ⟨996647, by rfl⟩ : syracuseStep 1328863 = 1993295) B1993295
theorem B1328943 : Blo 1327482 1328943 := bstep (se 1 (by rfl) ⟨996707, by rfl⟩ : syracuseStep 1328943 = 1993415) B1993415
theorem B1992503 : Blo 1327482 1992503 := bstep (se 1 (by rfl) ⟨1494377, by rfl⟩ : syracuseStep 1992503 = 2988755) B2988755
theorem B1681231 : Blo 1327482 1681231 := bstep (se 1 (by rfl) ⟨1260923, by rfl⟩ : syracuseStep 1681231 = 2521847) B2521847
theorem B8300393 : Blo 1327482 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B17024975 : Blo 1327482 17024975 := bstep (se 1 (by rfl) ⟨12768731, by rfl⟩ : syracuseStep 17024975 = 25537463) B25537463
theorem B1992809 : Blo 1327482 1992809 := bstep (se 2 (by rfl) ⟨747303, by rfl⟩ : syracuseStep 1992809 = 1494607) B1494607
theorem B5671097 : Blo 1327482 5671097 := bstep (se 2 (by rfl) ⟨2126661, by rfl⟩ : syracuseStep 5671097 = 4253323) B4253323
theorem B5384377 : Blo 1327482 5384377 := bstep (se 2 (by rfl) ⟨2019141, by rfl⟩ : syracuseStep 5384377 = 4038283) B4038283
theorem B5040413 : Blo 1327482 5040413 := bstep (se 3 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 5040413 = 1890155) B1890155
theorem B3361115 : Blo 1327482 3361115 := bstep (se 1 (by rfl) ⟨2520836, by rfl⟩ : syracuseStep 3361115 = 5041673) B5041673
theorem B3361135 : Blo 1327482 3361135 := bstep (se 1 (by rfl) ⟨2520851, by rfl⟩ : syracuseStep 3361135 = 5041703) B5041703
theorem B1993127 : Blo 1327482 1993127 := bstep (se 1 (by rfl) ⟨1494845, by rfl⟩ : syracuseStep 1993127 = 2989691) B2989691
theorem B9341351 : Blo 1327482 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B2394535 : Blo 1327482 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B4483511 : Blo 1327482 4483511 := bstep (se 1 (by rfl) ⟨3362633, by rfl⟩ : syracuseStep 4483511 = 6725267) B6725267
theorem B1993211 : Blo 1327482 1993211 := bstep (se 1 (by rfl) ⟨1494908, by rfl⟩ : syracuseStep 1993211 = 2989817) B2989817
theorem B32320079 : Blo 1327482 32320079 := bstep (se 1 (by rfl) ⟨24240059, by rfl⟩ : syracuseStep 32320079 = 48480119) B48480119
theorem B1493599 : Blo 1327482 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B1993337 : Blo 1327482 1993337 := bstep (se 2 (by rfl) ⟨747501, by rfl⟩ : syracuseStep 1993337 = 1495003) B1495003
theorem B1993391 : Blo 1327482 1993391 := bstep (se 1 (by rfl) ⟨1495043, by rfl⟩ : syracuseStep 1993391 = 2990087) B2990087
theorem B1993439 : Blo 1327482 1993439 := bstep (se 1 (by rfl) ⟨1495079, by rfl⟩ : syracuseStep 1993439 = 2990159) B2990159
theorem B4254707 : Blo 1327482 4254707 := bstep (se 1 (by rfl) ⟨3191030, by rfl⟩ : syracuseStep 4254707 = 6382061) B6382061
theorem B3361783 : Blo 1327482 3361783 := bstep (se 1 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 3361783 = 5042675) B5042675
theorem B6720731 : Blo 1327482 6720731 := bstep (se 1 (by rfl) ⟨5040548, by rfl⟩ : syracuseStep 6720731 = 10081097) B10081097
theorem B3362087 : Blo 1327482 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B2837855 : Blo 1327482 2837855 := bstep (se 1 (by rfl) ⟨2128391, by rfl⟩ : syracuseStep 2837855 = 4256783) B4256783
theorem B5672531 : Blo 1327482 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B1494751 : Blo 1327482 1494751 := bstep (se 1 (by rfl) ⟨1121063, by rfl⟩ : syracuseStep 1494751 = 2242127) B2242127
theorem B3796783 : Blo 1327482 3796783 := bstep (se 1 (by rfl) ⟨2847587, by rfl⟩ : syracuseStep 3796783 = 5695175) B5695175
theorem B5386031 : Blo 1327482 5386031 := bstep (se 1 (by rfl) ⟨4039523, by rfl⟩ : syracuseStep 5386031 = 8079047) B8079047
theorem B2240311 : Blo 1327482 2240311 := bstep (se 1 (by rfl) ⟨1680233, by rfl⟩ : syracuseStep 2240311 = 3360467) B3360467
theorem B2240777 : Blo 1327482 2240777 := bstep (se 2 (by rfl) ⟨840291, by rfl⟩ : syracuseStep 2240777 = 1680583) B1680583
theorem B6721865 : Blo 1327482 6721865 := bstep (se 2 (by rfl) ⟨2520699, by rfl⟩ : syracuseStep 6721865 = 5041399) B5041399
theorem B3781039 : Blo 1327482 3781039 := bstep (se 1 (by rfl) ⟨2835779, by rfl⟩ : syracuseStep 3781039 = 5671559) B5671559
theorem B5673473 : Blo 1327482 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B2691647 : Blo 1327482 2691647 := bstep (se 1 (by rfl) ⟨2018735, by rfl⟩ : syracuseStep 2691647 = 4037471) B4037471
theorem B28726109 : Blo 1327482 28726109 := bstep (se 3 (by rfl) ⟨5386145, by rfl⟩ : syracuseStep 28726109 = 10772291) B10772291
theorem B3363727 : Blo 1327482 3363727 := bstep (se 1 (by rfl) ⟨2522795, by rfl⟩ : syracuseStep 3363727 = 5045591) B5045591
theorem B5043343 : Blo 1327482 5043343 := bstep (se 1 (by rfl) ⟨3782507, by rfl⟩ : syracuseStep 5043343 = 7565015) B7565015
theorem B2987207 : Blo 1327482 2987207 := bstep (se 1 (by rfl) ⟨2240405, by rfl⟩ : syracuseStep 2987207 = 4480811) B4480811
theorem B2241769 : Blo 1327482 2241769 := bstep (se 2 (by rfl) ⟨840663, by rfl⟩ : syracuseStep 2241769 = 1681327) B1681327
theorem B2241823 : Blo 1327482 2241823 := bstep (se 1 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 2241823 = 3362735) B3362735
theorem B2127143 : Blo 1327482 2127143 := bstep (se 1 (by rfl) ⟨1595357, by rfl⟩ : syracuseStep 2127143 = 3190715) B3190715
theorem B18167129 : Blo 1327482 18167129 := bstep (se 2 (by rfl) ⟨6812673, by rfl⟩ : syracuseStep 18167129 = 13625347) B13625347
theorem B2987387 : Blo 1327482 2987387 := bstep (se 1 (by rfl) ⟨2240540, by rfl⟩ : syracuseStep 2987387 = 4481081) B4481081
theorem B5043617 : Blo 1327482 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B1594823 : Blo 1327482 1594823 := bstep (se 1 (by rfl) ⟨1196117, by rfl⟩ : syracuseStep 1594823 = 2392235) B2392235
theorem B2987513 : Blo 1327482 2987513 := bstep (se 2 (by rfl) ⟨1120317, by rfl⟩ : syracuseStep 2987513 = 2240635) B2240635
theorem B2987603 : Blo 1327482 2987603 := bstep (se 1 (by rfl) ⟨2240702, by rfl⟩ : syracuseStep 2987603 = 4481405) B4481405
theorem B6723161 : Blo 1327482 6723161 := bstep (se 2 (by rfl) ⟨2521185, by rfl⟩ : syracuseStep 6723161 = 5042371) B5042371
theorem B2242235 : Blo 1327482 2242235 := bstep (se 1 (by rfl) ⟨1681676, by rfl⟩ : syracuseStep 2242235 = 3363353) B3363353
theorem B2987783 : Blo 1327482 2987783 := bstep (se 1 (by rfl) ⟨2240837, by rfl⟩ : syracuseStep 2987783 = 4481675) B4481675
theorem B8075543 : Blo 1327482 8075543 := bstep (se 1 (by rfl) ⟨6056657, by rfl⟩ : syracuseStep 8075543 = 12113315) B12113315
theorem B2988395 : Blo 1327482 2988395 := bstep (se 1 (by rfl) ⟨2241296, by rfl⟩ : syracuseStep 2988395 = 4482593) B4482593
theorem B2988539 : Blo 1327482 2988539 := bstep (se 1 (by rfl) ⟨2241404, by rfl⟩ : syracuseStep 2988539 = 4482809) B4482809
theorem B2988665 : Blo 1327482 2988665 := bstep (se 2 (by rfl) ⟨1120749, by rfl⟩ : syracuseStep 2988665 = 2241499) B2241499
theorem B2988719 : Blo 1327482 2988719 := bstep (se 1 (by rfl) ⟨2241539, by rfl⟩ : syracuseStep 2988719 = 4483079) B4483079
theorem B2988791 : Blo 1327482 2988791 := bstep (se 1 (by rfl) ⟨2241593, by rfl⟩ : syracuseStep 2988791 = 4483187) B4483187
theorem B2988971 : Blo 1327482 2988971 := bstep (se 1 (by rfl) ⟨2241728, by rfl⟩ : syracuseStep 2988971 = 4483457) B4483457
theorem B5045287 : Blo 1327482 5045287 := bstep (se 1 (by rfl) ⟨3783965, by rfl⟩ : syracuseStep 5045287 = 7567931) B7567931
theorem B19676209 : Blo 1327482 19676209 := bstep (se 2 (by rfl) ⟨7378578, by rfl⟩ : syracuseStep 19676209 = 14757157) B14757157
theorem B5676155 : Blo 1327482 5676155 := bstep (se 1 (by rfl) ⟨4257116, by rfl⟩ : syracuseStep 5676155 = 8514233) B8514233
theorem B1891721 : Blo 1327482 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B4095431 : Blo 1327482 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2989511 : Blo 1327482 2989511 := bstep (se 1 (by rfl) ⟨2242133, by rfl⟩ : syracuseStep 2989511 = 4484267) B4484267
theorem B25886213 : Blo 1327482 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B28720655 : Blo 1327482 28720655 := bstep (se 1 (by rfl) ⟨21540491, by rfl⟩ : syracuseStep 28720655 = 43080983) B43080983
theorem B21536279 : Blo 1327482 21536279 := bstep (se 1 (by rfl) ⟨16152209, by rfl⟩ : syracuseStep 21536279 = 32304419) B32304419
theorem B4480595 : Blo 1327482 4480595 := bstep (se 1 (by rfl) ⟨3360446, by rfl⟩ : syracuseStep 4480595 = 6720893) B6720893
theorem B16375391 : Blo 1327482 16375391 := bstep (se 1 (by rfl) ⟨12281543, by rfl⟩ : syracuseStep 16375391 = 24563087) B24563087
theorem B11501203 : Blo 1327482 11501203 := bstep (se 1 (by rfl) ⟨8625902, by rfl⟩ : syracuseStep 11501203 = 17251805) B17251805
theorem B2989871 : Blo 1327482 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B4481243 : Blo 1327482 4481243 := bstep (se 1 (by rfl) ⟨3360932, by rfl⟩ : syracuseStep 4481243 = 6721865) B6721865
theorem B1327487 : Blo 1327482 1327487 := bstep (se 1 (by rfl) ⟨995615, by rfl⟩ : syracuseStep 1327487 = 1991231) B1991231
theorem B1794431 : Blo 1327482 1794431 := bstep (se 1 (by rfl) ⟨1345823, by rfl⟩ : syracuseStep 1794431 = 2691647) B2691647
theorem B1327567 : Blo 1327482 1327567 := bstep (se 1 (by rfl) ⟨995675, by rfl⟩ : syracuseStep 1327567 = 1991351) B1991351
theorem B4481513 : Blo 1327482 4481513 := bstep (se 2 (by rfl) ⟨1680567, by rfl⟩ : syracuseStep 4481513 = 3361135) B3361135
theorem B1327719 : Blo 1327482 1327719 := bstep (se 1 (by rfl) ⟨995789, by rfl⟩ : syracuseStep 1327719 = 1991579) B1991579
theorem B10773101 : Blo 1327482 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B12288641 : Blo 1327482 12288641 := bstep (se 2 (by rfl) ⟨4608240, by rfl⟩ : syracuseStep 12288641 = 9216481) B9216481
theorem B12763811 : Blo 1327482 12763811 := bstep (se 1 (by rfl) ⟨9572858, by rfl⟩ : syracuseStep 12763811 = 19145717) B19145717
theorem B5325547 : Blo 1327482 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B1991465 : Blo 1327482 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B1991471 : Blo 1327482 1991471 := bstep (se 1 (by rfl) ⟨1493603, by rfl⟩ : syracuseStep 1991471 = 2987207) B2987207
theorem B1418095 : Blo 1327482 1418095 := bstep (se 1 (by rfl) ⟨1063571, by rfl⟩ : syracuseStep 1418095 = 2127143) B2127143
theorem B1327983 : Blo 1327482 1327983 := bstep (se 1 (by rfl) ⟨995987, by rfl⟩ : syracuseStep 1327983 = 1991975) B1991975
theorem B1991591 : Blo 1327482 1991591 := bstep (se 1 (by rfl) ⟨1493693, by rfl⟩ : syracuseStep 1991591 = 2987387) B2987387
theorem B1328039 : Blo 1327482 1328039 := bstep (se 1 (by rfl) ⟨996029, by rfl⟩ : syracuseStep 1328039 = 1992059) B1992059
theorem B1991675 : Blo 1327482 1991675 := bstep (se 1 (by rfl) ⟨1493756, by rfl⟩ : syracuseStep 1991675 = 2987513) B2987513
theorem B1328123 : Blo 1327482 1328123 := bstep (se 1 (by rfl) ⟨996092, by rfl⟩ : syracuseStep 1328123 = 1992185) B1992185
theorem B1991735 : Blo 1327482 1991735 := bstep (se 1 (by rfl) ⟨1493801, by rfl⟩ : syracuseStep 1991735 = 2987603) B2987603
theorem B4482107 : Blo 1327482 4482107 := bstep (se 1 (by rfl) ⟨3361580, by rfl⟩ : syracuseStep 4482107 = 6723161) B6723161
theorem B1328191 : Blo 1327482 1328191 := bstep (se 1 (by rfl) ⟨996143, by rfl⟩ : syracuseStep 1328191 = 1992287) B1992287
theorem B1991855 : Blo 1327482 1991855 := bstep (se 1 (by rfl) ⟨1493891, by rfl⟩ : syracuseStep 1991855 = 2987783) B2987783
theorem B4252861 : Blo 1327482 4252861 := bstep (se 3 (by rfl) ⟨797411, by rfl⟩ : syracuseStep 4252861 = 1594823) B1594823
theorem B1328335 : Blo 1327482 1328335 := bstep (se 1 (by rfl) ⟨996251, by rfl⟩ : syracuseStep 1328335 = 1992503) B1992503
theorem B4482377 : Blo 1327482 4482377 := bstep (se 2 (by rfl) ⟨1680891, by rfl⟩ : syracuseStep 4482377 = 3361783) B3361783
theorem B6727049 : Blo 1327482 6727049 := bstep (se 2 (by rfl) ⟨2522643, by rfl⟩ : syracuseStep 6727049 = 5045287) B5045287
theorem B1328539 : Blo 1327482 1328539 := bstep (se 1 (by rfl) ⟨996404, by rfl⟩ : syracuseStep 1328539 = 1992809) B1992809
theorem B3360275 : Blo 1327482 3360275 := bstep (se 1 (by rfl) ⟨2520206, by rfl⟩ : syracuseStep 3360275 = 5040413) B5040413
theorem B1992263 : Blo 1327482 1992263 := bstep (se 1 (by rfl) ⟨1494197, by rfl⟩ : syracuseStep 1992263 = 2988395) B2988395
theorem B1328751 : Blo 1327482 1328751 := bstep (se 1 (by rfl) ⟨996563, by rfl⟩ : syracuseStep 1328751 = 1993127) B1993127
theorem B6227567 : Blo 1327482 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B30680693 : Blo 1327482 30680693 := bstep (se 5 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 30680693 = 2876315) B2876315
theorem B1992359 : Blo 1327482 1992359 := bstep (se 1 (by rfl) ⟨1494269, by rfl⟩ : syracuseStep 1992359 = 2988539) B2988539
theorem B1328807 : Blo 1327482 1328807 := bstep (se 1 (by rfl) ⟨996605, by rfl⟩ : syracuseStep 1328807 = 1993211) B1993211
theorem B21546719 : Blo 1327482 21546719 := bstep (se 1 (by rfl) ⟨16160039, by rfl⟩ : syracuseStep 21546719 = 32320079) B32320079
theorem B1992443 : Blo 1327482 1992443 := bstep (se 1 (by rfl) ⟨1494332, by rfl⟩ : syracuseStep 1992443 = 2988665) B2988665
theorem B1328891 : Blo 1327482 1328891 := bstep (se 1 (by rfl) ⟨996668, by rfl⟩ : syracuseStep 1328891 = 1993337) B1993337
theorem B1992479 : Blo 1327482 1992479 := bstep (se 1 (by rfl) ⟨1494359, by rfl⟩ : syracuseStep 1992479 = 2988719) B2988719
theorem B1328927 : Blo 1327482 1328927 := bstep (se 1 (by rfl) ⟨996695, by rfl⟩ : syracuseStep 1328927 = 1993391) B1993391
theorem B1328959 : Blo 1327482 1328959 := bstep (se 1 (by rfl) ⟨996719, by rfl⟩ : syracuseStep 1328959 = 1993439) B1993439
theorem B1992527 : Blo 1327482 1992527 := bstep (se 1 (by rfl) ⟨1494395, by rfl⟩ : syracuseStep 1992527 = 2988791) B2988791
theorem B1992647 : Blo 1327482 1992647 := bstep (se 1 (by rfl) ⟨1494485, by rfl⟩ : syracuseStep 1992647 = 2988971) B2988971
theorem B2836471 : Blo 1327482 2836471 := bstep (se 1 (by rfl) ⟨2127353, by rfl⟩ : syracuseStep 2836471 = 4254707) B4254707
theorem B7276553 : Blo 1327482 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B1993001 : Blo 1327482 1993001 := bstep (se 2 (by rfl) ⟨747375, by rfl⟩ : syracuseStep 1993001 = 1494751) B1494751
theorem B2730287 : Blo 1327482 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B1993007 : Blo 1327482 1993007 := bstep (se 1 (by rfl) ⟨1494755, by rfl⟩ : syracuseStep 1993007 = 2989511) B2989511
theorem B19147103 : Blo 1327482 19147103 := bstep (se 1 (by rfl) ⟨14360327, by rfl⟩ : syracuseStep 19147103 = 28720655) B28720655
theorem B3590687 : Blo 1327482 3590687 := bstep (se 1 (by rfl) ⟨2693015, by rfl⟩ : syracuseStep 3590687 = 5386031) B5386031
theorem B1993247 : Blo 1327482 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B1493851 : Blo 1327482 1493851 := bstep (se 1 (by rfl) ⟨1120388, by rfl⟩ : syracuseStep 1493851 = 2240777) B2240777
theorem B11824015 : Blo 1327482 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B5041385 : Blo 1327482 5041385 := bstep (se 2 (by rfl) ⟨1890519, by rfl⟩ : syracuseStep 5041385 = 3781039) B3781039
theorem B10776023 : Blo 1327482 10776023 := bstep (se 1 (by rfl) ⟨8082017, by rfl⟩ : syracuseStep 10776023 = 16164035) B16164035
theorem B12111419 : Blo 1327482 12111419 := bstep (se 1 (by rfl) ⟨9083564, by rfl⟩ : syracuseStep 12111419 = 18167129) B18167129
theorem B3362411 : Blo 1327482 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B28716677 : Blo 1327482 28716677 := bstep (se 4 (by rfl) ⟨2692188, by rfl⟩ : syracuseStep 28716677 = 5384377) B5384377
theorem B1494823 : Blo 1327482 1494823 := bstep (se 1 (by rfl) ⟨1121117, by rfl⟩ : syracuseStep 1494823 = 2242235) B2242235
theorem B4484969 : Blo 1327482 4484969 := bstep (se 2 (by rfl) ⟨1681863, by rfl⟩ : syracuseStep 4484969 = 3363727) B3363727
theorem B34025345 : Blo 1327482 34025345 := bstep (se 2 (by rfl) ⟨12759504, by rfl⟩ : syracuseStep 34025345 = 25519009) B25519009
theorem B5533595 : Blo 1327482 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B11349983 : Blo 1327482 11349983 := bstep (se 1 (by rfl) ⟨8512487, by rfl⟩ : syracuseStep 11349983 = 17024975) B17024975
theorem B26234945 : Blo 1327482 26234945 := bstep (se 2 (by rfl) ⟨9838104, by rfl⟩ : syracuseStep 26234945 = 19676209) B19676209
theorem B3780731 : Blo 1327482 3780731 := bstep (se 1 (by rfl) ⟨2835548, by rfl⟩ : syracuseStep 3780731 = 5671097) B5671097
theorem B15126749 : Blo 1327482 15126749 := bstep (se 3 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 15126749 = 5672531) B5672531
theorem B2240743 : Blo 1327482 2240743 := bstep (se 1 (by rfl) ⟨1680557, by rfl⟩ : syracuseStep 2240743 = 3361115) B3361115
theorem B2240905 : Blo 1327482 2240905 := bstep (se 2 (by rfl) ⟨840339, by rfl⟩ : syracuseStep 2240905 = 1680679) B1680679
theorem B2241337 : Blo 1327482 2241337 := bstep (se 2 (by rfl) ⟨840501, by rfl⟩ : syracuseStep 2241337 = 1681003) B1681003
theorem B2241391 : Blo 1327482 2241391 := bstep (se 1 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 2241391 = 3362087) B3362087
theorem B3781505 : Blo 1327482 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B17257475 : Blo 1327482 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B14357519 : Blo 1327482 14357519 := bstep (se 1 (by rfl) ⟨10768139, by rfl⟩ : syracuseStep 14357519 = 21536279) B21536279
theorem B2987063 : Blo 1327482 2987063 := bstep (se 1 (by rfl) ⟨2240297, by rfl⟩ : syracuseStep 2987063 = 4480595) B4480595
theorem B10916927 : Blo 1327482 10916927 := bstep (se 1 (by rfl) ⟨8187695, by rfl⟩ : syracuseStep 10916927 = 16375391) B16375391
theorem B2987081 : Blo 1327482 2987081 := bstep (se 2 (by rfl) ⟨1120155, by rfl⟩ : syracuseStep 2987081 = 2240311) B2240311
theorem B2241641 : Blo 1327482 2241641 := bstep (se 2 (by rfl) ⟨840615, by rfl⟩ : syracuseStep 2241641 = 1681231) B1681231
theorem B4789691 : Blo 1327482 4789691 := bstep (se 1 (by rfl) ⟨3592268, by rfl⟩ : syracuseStep 4789691 = 7184537) B7184537
theorem B3782315 : Blo 1327482 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B3192713 : Blo 1327482 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B19150739 : Blo 1327482 19150739 := bstep (se 1 (by rfl) ⟨14363054, by rfl⟩ : syracuseStep 19150739 = 28726109) B28726109
theorem B21534781 : Blo 1327482 21534781 := bstep (se 3 (by rfl) ⟨4037771, by rfl⟩ : syracuseStep 21534781 = 8075543) B8075543
theorem B7567613 : Blo 1327482 7567613 := bstep (se 3 (by rfl) ⟨1418927, by rfl⟩ : syracuseStep 7567613 = 2837855) B2837855
theorem B5044589 : Blo 1327482 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B6724457 : Blo 1327482 6724457 := bstep (se 2 (by rfl) ⟨2521671, by rfl⟩ : syracuseStep 6724457 = 5043343) B5043343
theorem B20249509 : Blo 1327482 20249509 := bstep (se 4 (by rfl) ⟨1898391, by rfl⟩ : syracuseStep 20249509 = 3796783) B3796783
theorem B2989007 : Blo 1327482 2989007 := bstep (se 1 (by rfl) ⟨2241755, by rfl⟩ : syracuseStep 2989007 = 4483511) B4483511
theorem B2989025 : Blo 1327482 2989025 := bstep (se 2 (by rfl) ⟨1120884, by rfl⟩ : syracuseStep 2989025 = 2241769) B2241769
theorem B4545505 : Blo 1327482 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B2989097 : Blo 1327482 2989097 := bstep (se 2 (by rfl) ⟨1120911, by rfl⟩ : syracuseStep 2989097 = 2241823) B2241823
theorem B15129665 : Blo 1327482 15129665 := bstep (se 2 (by rfl) ⟨5673624, by rfl⟩ : syracuseStep 15129665 = 11347249) B11347249
theorem B3784103 : Blo 1327482 3784103 := bstep (se 1 (by rfl) ⟨2838077, by rfl⟩ : syracuseStep 3784103 = 5676155) B5676155
theorem B4480487 : Blo 1327482 4480487 := bstep (se 1 (by rfl) ⟨3360365, by rfl⟩ : syracuseStep 4480487 = 6720731) B6720731
theorem B15334937 : Blo 1327482 15334937 := bstep (se 2 (by rfl) ⟨5750601, by rfl⟩ : syracuseStep 15334937 = 11501203) B11501203
theorem B17489963 : Blo 1327482 17489963 := bstep (se 1 (by rfl) ⟨13117472, by rfl⟩ : syracuseStep 17489963 = 26234945) B26234945
theorem B28713041 : Blo 1327482 28713041 := bstep (se 2 (by rfl) ⟨10767390, by rfl⟩ : syracuseStep 28713041 = 21534781) B21534781
theorem B10084499 : Blo 1327482 10084499 := bstep (se 1 (by rfl) ⟨7563374, by rfl⟩ : syracuseStep 10084499 = 15126749) B15126749
theorem B1327643 : Blo 1327482 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B1327647 : Blo 1327482 1327647 := bstep (se 1 (by rfl) ⟨995735, by rfl⟩ : syracuseStep 1327647 = 1991471) B1991471
theorem B1327727 : Blo 1327482 1327727 := bstep (se 1 (by rfl) ⟨995795, by rfl⟩ : syracuseStep 1327727 = 1991591) B1991591
theorem B1327783 : Blo 1327482 1327783 := bstep (se 1 (by rfl) ⟨995837, by rfl⟩ : syracuseStep 1327783 = 1991675) B1991675
theorem B1991375 : Blo 1327482 1991375 := bstep (se 1 (by rfl) ⟨1493531, by rfl⟩ : syracuseStep 1991375 = 2987063) B2987063
theorem B1327823 : Blo 1327482 1327823 := bstep (se 1 (by rfl) ⟨995867, by rfl⟩ : syracuseStep 1327823 = 1991735) B1991735
theorem B1991387 : Blo 1327482 1991387 := bstep (se 1 (by rfl) ⟨1493540, by rfl⟩ : syracuseStep 1991387 = 2987081) B2987081
theorem B1327903 : Blo 1327482 1327903 := bstep (se 1 (by rfl) ⟨995927, by rfl⟩ : syracuseStep 1327903 = 1991855) B1991855
theorem B4785149 : Blo 1327482 4785149 := bstep (se 3 (by rfl) ⟨897215, by rfl⟩ : syracuseStep 4785149 = 1794431) B1794431
theorem B1328175 : Blo 1327482 1328175 := bstep (se 1 (by rfl) ⟨996131, by rfl⟩ : syracuseStep 1328175 = 1992263) B1992263
theorem B1328239 : Blo 1327482 1328239 := bstep (se 1 (by rfl) ⟨996179, by rfl⟩ : syracuseStep 1328239 = 1992359) B1992359
theorem B1991801 : Blo 1327482 1991801 := bstep (se 2 (by rfl) ⟨746925, by rfl⟩ : syracuseStep 1991801 = 1493851) B1493851
theorem B1328295 : Blo 1327482 1328295 := bstep (se 1 (by rfl) ⟨996221, by rfl⟩ : syracuseStep 1328295 = 1992443) B1992443
theorem B1328319 : Blo 1327482 1328319 := bstep (se 1 (by rfl) ⟨996239, by rfl⟩ : syracuseStep 1328319 = 1992479) B1992479
theorem B1328351 : Blo 1327482 1328351 := bstep (se 1 (by rfl) ⟨996263, by rfl⟩ : syracuseStep 1328351 = 1992527) B1992527
theorem B1328431 : Blo 1327482 1328431 := bstep (se 1 (by rfl) ⟨996323, by rfl⟩ : syracuseStep 1328431 = 1992647) B1992647
theorem B4851035 : Blo 1327482 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B1328667 : Blo 1327482 1328667 := bstep (se 1 (by rfl) ⟨996500, by rfl⟩ : syracuseStep 1328667 = 1993001) B1993001
theorem B1328671 : Blo 1327482 1328671 := bstep (se 1 (by rfl) ⟨996503, by rfl⟩ : syracuseStep 1328671 = 1993007) B1993007
theorem B12764735 : Blo 1327482 12764735 := bstep (se 1 (by rfl) ⟨9573551, by rfl⟩ : syracuseStep 12764735 = 19147103) B19147103
theorem B5670481 : Blo 1327482 5670481 := bstep (se 2 (by rfl) ⟨2126430, by rfl⟩ : syracuseStep 5670481 = 4252861) B4252861
theorem B1328831 : Blo 1327482 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B4482971 : Blo 1327482 4482971 := bstep (se 1 (by rfl) ⟨3362228, by rfl⟩ : syracuseStep 4482971 = 6724457) B6724457
theorem B1992671 : Blo 1327482 1992671 := bstep (se 1 (by rfl) ⟨1494503, by rfl⟩ : syracuseStep 1992671 = 2989007) B2989007
theorem B1992683 : Blo 1327482 1992683 := bstep (se 1 (by rfl) ⟨1494512, by rfl⟩ : syracuseStep 1992683 = 2989025) B2989025
theorem B1992731 : Blo 1327482 1992731 := bstep (se 1 (by rfl) ⟨1494548, by rfl⟩ : syracuseStep 1992731 = 2989097) B2989097
theorem B10086443 : Blo 1327482 10086443 := bstep (se 1 (by rfl) ⟨7564832, by rfl⟩ : syracuseStep 10086443 = 15129665) B15129665
theorem B3360923 : Blo 1327482 3360923 := bstep (se 1 (by rfl) ⟨2520692, by rfl⟩ : syracuseStep 3360923 = 5041385) B5041385
theorem B1993097 : Blo 1327482 1993097 := bstep (se 2 (by rfl) ⟨747411, by rfl⟩ : syracuseStep 1993097 = 1494823) B1494823
theorem B3689063 : Blo 1327482 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B9571679 : Blo 1327482 9571679 := bstep (se 1 (by rfl) ⟨7178759, by rfl⟩ : syracuseStep 9571679 = 14357519) B14357519
theorem B7277951 : Blo 1327482 7277951 := bstep (se 1 (by rfl) ⟨5458463, by rfl⟩ : syracuseStep 7277951 = 10916927) B10916927
theorem B1494427 : Blo 1327482 1494427 := bstep (se 1 (by rfl) ⟨1120820, by rfl⟩ : syracuseStep 1494427 = 2241641) B2241641
theorem B4484699 : Blo 1327482 4484699 := bstep (se 1 (by rfl) ⟨3363524, by rfl⟩ : syracuseStep 4484699 = 6727049) B6727049
theorem B2240183 : Blo 1327482 2240183 := bstep (se 1 (by rfl) ⟨1680137, by rfl⟩ : syracuseStep 2240183 = 3360275) B3360275
theorem B14364479 : Blo 1327482 14364479 := bstep (se 1 (by rfl) ⟨10773359, by rfl⟩ : syracuseStep 14364479 = 21546719) B21546719
theorem B15765353 : Blo 1327482 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B12767159 : Blo 1327482 12767159 := bstep (se 1 (by rfl) ⟨9575369, by rfl⟩ : syracuseStep 12767159 = 19150739) B19150739
theorem B3363059 : Blo 1327482 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B2986991 : Blo 1327482 2986991 := bstep (se 1 (by rfl) ⟨2240243, by rfl⟩ : syracuseStep 2986991 = 4480487) B4480487
theorem B8074279 : Blo 1327482 8074279 := bstep (se 1 (by rfl) ⟨6055709, by rfl⟩ : syracuseStep 8074279 = 12111419) B12111419
theorem B2241607 : Blo 1327482 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B7566655 : Blo 1327482 7566655 := bstep (se 1 (by rfl) ⟨5674991, by rfl⟩ : syracuseStep 7566655 = 11349983) B11349983
theorem B3781961 : Blo 1327482 3781961 := bstep (se 2 (by rfl) ⟨1418235, by rfl⟩ : syracuseStep 3781961 = 2836471) B2836471
theorem B46019933 : Blo 1327482 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B2520487 : Blo 1327482 2520487 := bstep (se 1 (by rfl) ⟨1890365, by rfl⟩ : syracuseStep 2520487 = 3780731) B3780731
theorem B2987495 : Blo 1327482 2987495 := bstep (se 1 (by rfl) ⟨2240621, by rfl⟩ : syracuseStep 2987495 = 4481243) B4481243
theorem B2987657 : Blo 1327482 2987657 := bstep (se 2 (by rfl) ⟨1120371, by rfl⟩ : syracuseStep 2987657 = 2240743) B2240743
theorem B2987675 : Blo 1327482 2987675 := bstep (se 1 (by rfl) ⟨2240756, by rfl⟩ : syracuseStep 2987675 = 4481513) B4481513
theorem B7182067 : Blo 1327482 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B8509207 : Blo 1327482 8509207 := bstep (se 1 (by rfl) ⟨6381905, by rfl⟩ : syracuseStep 8509207 = 12763811) B12763811
theorem B2987873 : Blo 1327482 2987873 := bstep (se 2 (by rfl) ⟨1120452, by rfl⟩ : syracuseStep 2987873 = 2240905) B2240905
theorem B2988071 : Blo 1327482 2988071 := bstep (se 1 (by rfl) ⟨2241053, by rfl⟩ : syracuseStep 2988071 = 4482107) B4482107
theorem B7280765 : Blo 1327482 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B2988251 : Blo 1327482 2988251 := bstep (se 1 (by rfl) ⟨2241188, by rfl⟩ : syracuseStep 2988251 = 4482377) B4482377
theorem B3193127 : Blo 1327482 3193127 := bstep (se 1 (by rfl) ⟨2394845, by rfl⟩ : syracuseStep 3193127 = 4789691) B4789691
theorem B7100729 : Blo 1327482 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B4151711 : Blo 1327482 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B2988449 : Blo 1327482 2988449 := bstep (se 2 (by rfl) ⟨1120668, by rfl⟩ : syracuseStep 2988449 = 2241337) B2241337
theorem B20453795 : Blo 1327482 20453795 := bstep (se 1 (by rfl) ⟨15340346, by rfl⟩ : syracuseStep 20453795 = 30680693) B30680693
theorem B2521543 : Blo 1327482 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B1890793 : Blo 1327482 1890793 := bstep (se 2 (by rfl) ⟨709047, by rfl⟩ : syracuseStep 1890793 = 1418095) B1418095
theorem B2988521 : Blo 1327482 2988521 := bstep (se 2 (by rfl) ⟨1120695, by rfl⟩ : syracuseStep 2988521 = 2241391) B2241391
theorem B26999345 : Blo 1327482 26999345 := bstep (se 2 (by rfl) ⟨10124754, by rfl⟩ : syracuseStep 26999345 = 20249509) B20249509
theorem B2128475 : Blo 1327482 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B6060673 : Blo 1327482 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B131078837 : Blo 1327482 131078837 := bstep (se 5 (by rfl) ⟨6144320, by rfl⟩ : syracuseStep 131078837 = 12288641) B12288641
theorem B9575165 : Blo 1327482 9575165 := bstep (se 3 (by rfl) ⟨1795343, by rfl⟩ : syracuseStep 9575165 = 3590687) B3590687
theorem B5045075 : Blo 1327482 5045075 := bstep (se 1 (by rfl) ⟨3783806, by rfl⟩ : syracuseStep 5045075 = 7567613) B7567613
theorem B2522735 : Blo 1327482 2522735 := bstep (se 1 (by rfl) ⟨1892051, by rfl⟩ : syracuseStep 2522735 = 3784103) B3784103
theorem B7184015 : Blo 1327482 7184015 := bstep (se 1 (by rfl) ⟨5388011, by rfl⟩ : syracuseStep 7184015 = 10776023) B10776023
theorem B10084013 : Blo 1327482 10084013 := bstep (se 3 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 10084013 = 3781505) B3781505
theorem B10223291 : Blo 1327482 10223291 := bstep (se 1 (by rfl) ⟨7667468, by rfl⟩ : syracuseStep 10223291 = 15334937) B15334937
theorem B19144451 : Blo 1327482 19144451 := bstep (se 1 (by rfl) ⟨14358338, by rfl⟩ : syracuseStep 19144451 = 28716677) B28716677
theorem B2989979 : Blo 1327482 2989979 := bstep (se 1 (by rfl) ⟨2242484, by rfl⟩ : syracuseStep 2989979 = 4484969) B4484969
theorem B22683563 : Blo 1327482 22683563 := bstep (se 1 (by rfl) ⟨17012672, by rfl⟩ : syracuseStep 22683563 = 34025345) B34025345
theorem B1327583 : Blo 1327482 1327583 := bstep (se 1 (by rfl) ⟨995687, by rfl⟩ : syracuseStep 1327583 = 1991375) B1991375
theorem B1327591 : Blo 1327482 1327591 := bstep (se 1 (by rfl) ⟨995693, by rfl⟩ : syracuseStep 1327591 = 1991387) B1991387
theorem B1991327 : Blo 1327482 1991327 := bstep (se 1 (by rfl) ⟨1493495, by rfl⟩ : syracuseStep 1991327 = 2986991) B2986991
theorem B1327867 : Blo 1327482 1327867 := bstep (se 1 (by rfl) ⟨995900, by rfl⟩ : syracuseStep 1327867 = 1991801) B1991801
theorem B30679955 : Blo 1327482 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B1991663 : Blo 1327482 1991663 := bstep (se 1 (by rfl) ⟨1493747, by rfl⟩ : syracuseStep 1991663 = 2987495) B2987495
theorem B1991771 : Blo 1327482 1991771 := bstep (se 1 (by rfl) ⟨1493828, by rfl⟩ : syracuseStep 1991771 = 2987657) B2987657
theorem B1991783 : Blo 1327482 1991783 := bstep (se 1 (by rfl) ⟨1493837, by rfl⟩ : syracuseStep 1991783 = 2987675) B2987675
theorem B1991915 : Blo 1327482 1991915 := bstep (se 1 (by rfl) ⟨1493936, by rfl⟩ : syracuseStep 1991915 = 2987873) B2987873
theorem B1328447 : Blo 1327482 1328447 := bstep (se 1 (by rfl) ⟨996335, by rfl⟩ : syracuseStep 1328447 = 1992671) B1992671
theorem B1328455 : Blo 1327482 1328455 := bstep (se 1 (by rfl) ⟨996341, by rfl⟩ : syracuseStep 1328455 = 1992683) B1992683
theorem B1328487 : Blo 1327482 1328487 := bstep (se 1 (by rfl) ⟨996365, by rfl⟩ : syracuseStep 1328487 = 1992731) B1992731
theorem B1992047 : Blo 1327482 1992047 := bstep (se 1 (by rfl) ⟨1494035, by rfl⟩ : syracuseStep 1992047 = 2988071) B2988071
theorem B10765705 : Blo 1327482 10765705 := bstep (se 2 (by rfl) ⟨4037139, by rfl⟩ : syracuseStep 10765705 = 8074279) B8074279
theorem B1992167 : Blo 1327482 1992167 := bstep (se 1 (by rfl) ⟨1494125, by rfl⟩ : syracuseStep 1992167 = 2988251) B2988251
theorem B1328731 : Blo 1327482 1328731 := bstep (se 1 (by rfl) ⟨996548, by rfl⟩ : syracuseStep 1328731 = 1993097) B1993097
theorem B1992299 : Blo 1327482 1992299 := bstep (se 1 (by rfl) ⟨1494224, by rfl⟩ : syracuseStep 1992299 = 2988449) B2988449
theorem B1992347 : Blo 1327482 1992347 := bstep (se 1 (by rfl) ⟨1494260, by rfl⟩ : syracuseStep 1992347 = 2988521) B2988521
theorem B17999563 : Blo 1327482 17999563 := bstep (se 1 (by rfl) ⟨13499672, by rfl⟩ : syracuseStep 17999563 = 26999345) B26999345
theorem B2459375 : Blo 1327482 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B87385891 : Blo 1327482 87385891 := bstep (se 1 (by rfl) ⟨65539418, by rfl⟩ : syracuseStep 87385891 = 131078837) B131078837
theorem B6383443 : Blo 1327482 6383443 := bstep (se 1 (by rfl) ⟨4787582, by rfl⟩ : syracuseStep 6383443 = 9575165) B9575165
theorem B1992569 : Blo 1327482 1992569 := bstep (se 2 (by rfl) ⟨747213, by rfl⟩ : syracuseStep 1992569 = 1494427) B1494427
theorem B3360649 : Blo 1327482 3360649 := bstep (se 2 (by rfl) ⟨1260243, by rfl⟩ : syracuseStep 3360649 = 2520487) B2520487
theorem B4851967 : Blo 1327482 4851967 := bstep (se 1 (by rfl) ⟨3638975, by rfl⟩ : syracuseStep 4851967 = 7277951) B7277951
theorem B1681823 : Blo 1327482 1681823 := bstep (se 1 (by rfl) ⟨1261367, by rfl⟩ : syracuseStep 1681823 = 2522735) B2522735
theorem B1493455 : Blo 1327482 1493455 := bstep (se 1 (by rfl) ⟨1120091, by rfl⟩ : syracuseStep 1493455 = 2240183) B2240183
theorem B1993319 : Blo 1327482 1993319 := bstep (se 1 (by rfl) ⟨1494989, by rfl⟩ : syracuseStep 1993319 = 2989979) B2989979
theorem B46639901 : Blo 1327482 46639901 := bstep (se 3 (by rfl) ⟨8744981, by rfl⟩ : syracuseStep 46639901 = 17489963) B17489963
theorem B3362057 : Blo 1327482 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B3190099 : Blo 1327482 3190099 := bstep (se 1 (by rfl) ⟨2392574, by rfl⟩ : syracuseStep 3190099 = 4785149) B4785149
theorem B8080897 : Blo 1327482 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B4853843 : Blo 1327482 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B2240615 : Blo 1327482 2240615 := bstep (se 1 (by rfl) ⟨1680461, by rfl⟩ : syracuseStep 2240615 = 3360923) B3360923
theorem B13635863 : Blo 1327482 13635863 := bstep (se 1 (by rfl) ⟨10226897, by rfl⟩ : syracuseStep 13635863 = 20453795) B20453795
theorem B10088873 : Blo 1327482 10088873 := bstep (se 2 (by rfl) ⟨3783327, by rfl⟩ : syracuseStep 10088873 = 7566655) B7566655
theorem B3363383 : Blo 1327482 3363383 := bstep (se 1 (by rfl) ⟨2522537, by rfl⟩ : syracuseStep 3363383 = 5045075) B5045075
theorem B4789343 : Blo 1327482 4789343 := bstep (se 1 (by rfl) ⟨3592007, by rfl⟩ : syracuseStep 4789343 = 7184015) B7184015
theorem B6722675 : Blo 1327482 6722675 := bstep (se 1 (by rfl) ⟨5042006, by rfl⟩ : syracuseStep 6722675 = 10084013) B10084013
theorem B19142027 : Blo 1327482 19142027 := bstep (se 1 (by rfl) ⟨14356520, by rfl⟩ : syracuseStep 19142027 = 28713041) B28713041
theorem B6722999 : Blo 1327482 6722999 := bstep (se 1 (by rfl) ⟨5042249, by rfl⟩ : syracuseStep 6722999 = 10084499) B10084499
theorem B2242039 : Blo 1327482 2242039 := bstep (se 1 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 2242039 = 3363059) B3363059
theorem B2521057 : Blo 1327482 2521057 := bstep (se 2 (by rfl) ⟨945396, by rfl⟩ : syracuseStep 2521057 = 1890793) B1890793
theorem B2521307 : Blo 1327482 2521307 := bstep (se 1 (by rfl) ⟨1890980, by rfl⟩ : syracuseStep 2521307 = 3781961) B3781961
theorem B3234023 : Blo 1327482 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B8509823 : Blo 1327482 8509823 := bstep (se 1 (by rfl) ⟨6382367, by rfl⟩ : syracuseStep 8509823 = 12764735) B12764735
theorem B2988647 : Blo 1327482 2988647 := bstep (se 1 (by rfl) ⟨2241485, by rfl⟩ : syracuseStep 2988647 = 4482971) B4482971
theorem B6724295 : Blo 1327482 6724295 := bstep (se 1 (by rfl) ⟨5043221, by rfl⟩ : syracuseStep 6724295 = 10086443) B10086443
theorem B2988809 : Blo 1327482 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B2128751 : Blo 1327482 2128751 := bstep (se 1 (by rfl) ⟨1596563, by rfl⟩ : syracuseStep 2128751 = 3193127) B3193127
theorem B4733819 : Blo 1327482 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B5675933 : Blo 1327482 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B2767807 : Blo 1327482 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B27262109 : Blo 1327482 27262109 := bstep (se 3 (by rfl) ⟨5111645, by rfl⟩ : syracuseStep 27262109 = 10223291) B10223291
theorem B7560641 : Blo 1327482 7560641 := bstep (se 2 (by rfl) ⟨2835240, by rfl⟩ : syracuseStep 7560641 = 5670481) B5670481
theorem B6381119 : Blo 1327482 6381119 := bstep (se 1 (by rfl) ⟨4785839, by rfl⟩ : syracuseStep 6381119 = 9571679) B9571679
theorem B9576089 : Blo 1327482 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B11345609 : Blo 1327482 11345609 := bstep (se 2 (by rfl) ⟨4254603, by rfl⟩ : syracuseStep 11345609 = 8509207) B8509207
theorem B2989799 : Blo 1327482 2989799 := bstep (se 1 (by rfl) ⟨2242349, by rfl⟩ : syracuseStep 2989799 = 4484699) B4484699
theorem B12762967 : Blo 1327482 12762967 := bstep (se 1 (by rfl) ⟨9572225, by rfl⟩ : syracuseStep 12762967 = 19144451) B19144451
theorem B9576319 : Blo 1327482 9576319 := bstep (se 1 (by rfl) ⟨7182239, by rfl⟩ : syracuseStep 9576319 = 14364479) B14364479
theorem B10510235 : Blo 1327482 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B15122375 : Blo 1327482 15122375 := bstep (se 1 (by rfl) ⟨11341781, by rfl⟩ : syracuseStep 15122375 = 22683563) B22683563
theorem B8511439 : Blo 1327482 8511439 := bstep (se 1 (by rfl) ⟨6383579, by rfl⟩ : syracuseStep 8511439 = 12767159) B12767159
theorem B3235895 : Blo 1327482 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B6725915 : Blo 1327482 6725915 := bstep (se 1 (by rfl) ⟨5044436, by rfl⟩ : syracuseStep 6725915 = 10088873) B10088873
theorem B1327551 : Blo 1327482 1327551 := bstep (se 1 (by rfl) ⟨995663, by rfl⟩ : syracuseStep 1327551 = 1991327) B1991327
theorem B1991273 : Blo 1327482 1991273 := bstep (se 2 (by rfl) ⟨746727, by rfl⟩ : syracuseStep 1991273 = 1493455) B1493455
theorem B1327775 : Blo 1327482 1327775 := bstep (se 1 (by rfl) ⟨995831, by rfl⟩ : syracuseStep 1327775 = 1991663) B1991663
theorem B1327847 : Blo 1327482 1327847 := bstep (se 1 (by rfl) ⟨995885, by rfl⟩ : syracuseStep 1327847 = 1991771) B1991771
theorem B1327855 : Blo 1327482 1327855 := bstep (se 1 (by rfl) ⟨995891, by rfl⟩ : syracuseStep 1327855 = 1991783) B1991783
theorem B4481783 : Blo 1327482 4481783 := bstep (se 1 (by rfl) ⟨3361337, by rfl⟩ : syracuseStep 4481783 = 6722675) B6722675
theorem B1327943 : Blo 1327482 1327943 := bstep (se 1 (by rfl) ⟨995957, by rfl⟩ : syracuseStep 1327943 = 1991915) B1991915
theorem B1328031 : Blo 1327482 1328031 := bstep (se 1 (by rfl) ⟨996023, by rfl⟩ : syracuseStep 1328031 = 1992047) B1992047
theorem B4481999 : Blo 1327482 4481999 := bstep (se 1 (by rfl) ⟨3361499, by rfl⟩ : syracuseStep 4481999 = 6722999) B6722999
theorem B1328111 : Blo 1327482 1328111 := bstep (se 1 (by rfl) ⟨996083, by rfl⟩ : syracuseStep 1328111 = 1992167) B1992167
theorem B1328199 : Blo 1327482 1328199 := bstep (se 1 (by rfl) ⟨996149, by rfl⟩ : syracuseStep 1328199 = 1992299) B1992299
theorem B1328231 : Blo 1327482 1328231 := bstep (se 1 (by rfl) ⟨996173, by rfl⟩ : syracuseStep 1328231 = 1992347) B1992347
theorem B1639583 : Blo 1327482 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B1328379 : Blo 1327482 1328379 := bstep (se 1 (by rfl) ⟨996284, by rfl⟩ : syracuseStep 1328379 = 1992569) B1992569
theorem B2156015 : Blo 1327482 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B17016317 : Blo 1327482 17016317 := bstep (se 3 (by rfl) ⟨3190559, by rfl⟩ : syracuseStep 17016317 = 6381119) B6381119
theorem B1992431 : Blo 1327482 1992431 := bstep (se 1 (by rfl) ⟨1494323, by rfl⟩ : syracuseStep 1992431 = 2988647) B2988647
theorem B1328879 : Blo 1327482 1328879 := bstep (se 1 (by rfl) ⟨996659, by rfl⟩ : syracuseStep 1328879 = 1993319) B1993319
theorem B4253465 : Blo 1327482 4253465 := bstep (se 2 (by rfl) ⟨1595049, by rfl⟩ : syracuseStep 4253465 = 3190099) B3190099
theorem B4482863 : Blo 1327482 4482863 := bstep (se 1 (by rfl) ⟨3362147, by rfl⟩ : syracuseStep 4482863 = 6724295) B6724295
theorem B1992539 : Blo 1327482 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B14354273 : Blo 1327482 14354273 := bstep (se 2 (by rfl) ⟨5382852, by rfl⟩ : syracuseStep 14354273 = 10765705) B10765705
theorem B1419167 : Blo 1327482 1419167 := bstep (se 1 (by rfl) ⟨1064375, by rfl⟩ : syracuseStep 1419167 = 2128751) B2128751
theorem B3155879 : Blo 1327482 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B10774529 : Blo 1327482 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B5040427 : Blo 1327482 5040427 := bstep (se 1 (by rfl) ⟨3780320, by rfl⟩ : syracuseStep 5040427 = 7560641) B7560641
theorem B6384059 : Blo 1327482 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B17017289 : Blo 1327482 17017289 := bstep (se 2 (by rfl) ⟨6381483, by rfl⟩ : syracuseStep 17017289 = 12762967) B12762967
theorem B7563739 : Blo 1327482 7563739 := bstep (se 1 (by rfl) ⟨5672804, by rfl⟩ : syracuseStep 7563739 = 11345609) B11345609
theorem B1993199 : Blo 1327482 1993199 := bstep (se 1 (by rfl) ⟨1494899, by rfl⟩ : syracuseStep 1993199 = 2989799) B2989799
theorem B11348585 : Blo 1327482 11348585 := bstep (se 2 (by rfl) ⟨4255719, by rfl⟩ : syracuseStep 11348585 = 8511439) B8511439
theorem B7006823 : Blo 1327482 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B3361409 : Blo 1327482 3361409 := bstep (se 2 (by rfl) ⟨1260528, by rfl⟩ : syracuseStep 3361409 = 2521057) B2521057
theorem B1493743 : Blo 1327482 1493743 := bstep (se 1 (by rfl) ⟨1120307, by rfl⟩ : syracuseStep 1493743 = 2240615) B2240615
theorem B72698957 : Blo 1327482 72698957 := bstep (se 3 (by rfl) ⟨13631054, by rfl⟩ : syracuseStep 72698957 = 27262109) B27262109
theorem B4484861 : Blo 1327482 4484861 := bstep (se 3 (by rfl) ⟨840911, by rfl⟩ : syracuseStep 4484861 = 1681823) B1681823
theorem B3690409 : Blo 1327482 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B5673215 : Blo 1327482 5673215 := bstep (se 1 (by rfl) ⟨4254911, by rfl⟩ : syracuseStep 5673215 = 8509823) B8509823
theorem B31093267 : Blo 1327482 31093267 := bstep (se 1 (by rfl) ⟨23319950, by rfl⟩ : syracuseStep 31093267 = 46639901) B46639901
theorem B2241371 : Blo 1327482 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B23999417 : Blo 1327482 23999417 := bstep (se 2 (by rfl) ⟨8999781, by rfl⟩ : syracuseStep 23999417 = 17999563) B17999563
theorem B12768425 : Blo 1327482 12768425 := bstep (se 2 (by rfl) ⟨4788159, by rfl⟩ : syracuseStep 12768425 = 9576319) B9576319
theorem B10081583 : Blo 1327482 10081583 := bstep (se 1 (by rfl) ⟨7561187, by rfl⟩ : syracuseStep 10081583 = 15122375) B15122375
theorem B9090575 : Blo 1327482 9090575 := bstep (se 1 (by rfl) ⟨6817931, by rfl⟩ : syracuseStep 9090575 = 13635863) B13635863
theorem B6469289 : Blo 1327482 6469289 := bstep (se 2 (by rfl) ⟨2425983, by rfl⟩ : syracuseStep 6469289 = 4851967) B4851967
theorem B2242255 : Blo 1327482 2242255 := bstep (se 1 (by rfl) ⟨1681691, by rfl⟩ : syracuseStep 2242255 = 3363383) B3363383
theorem B6723485 : Blo 1327482 6723485 := bstep (se 3 (by rfl) ⟨1260653, by rfl⟩ : syracuseStep 6723485 = 2521307) B2521307
theorem B20453303 : Blo 1327482 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B3192895 : Blo 1327482 3192895 := bstep (se 1 (by rfl) ⟨2394671, by rfl⟩ : syracuseStep 3192895 = 4789343) B4789343
theorem B12761351 : Blo 1327482 12761351 := bstep (se 1 (by rfl) ⟨9571013, by rfl⟩ : syracuseStep 12761351 = 19142027) B19142027
theorem B3783955 : Blo 1327482 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B2989385 : Blo 1327482 2989385 := bstep (se 2 (by rfl) ⟨1121019, by rfl⟩ : syracuseStep 2989385 = 2242039) B2242039
theorem B116514521 : Blo 1327482 116514521 := bstep (se 2 (by rfl) ⟨43692945, by rfl⟩ : syracuseStep 116514521 = 87385891) B87385891
theorem B8511257 : Blo 1327482 8511257 := bstep (se 2 (by rfl) ⟨3191721, by rfl⟩ : syracuseStep 8511257 = 6383443) B6383443
theorem B4480865 : Blo 1327482 4480865 := bstep (se 2 (by rfl) ⟨1680324, by rfl⟩ : syracuseStep 4480865 = 3360649) B3360649
theorem B1327515 : Blo 1327482 1327515 := bstep (se 1 (by rfl) ⟨995636, by rfl⟩ : syracuseStep 1327515 = 1991273) B1991273
theorem B10084985 : Blo 1327482 10084985 := bstep (se 2 (by rfl) ⟨3781869, by rfl⟩ : syracuseStep 10084985 = 7563739) B7563739
theorem B15999611 : Blo 1327482 15999611 := bstep (se 1 (by rfl) ⟨11999708, by rfl⟩ : syracuseStep 15999611 = 23999417) B23999417
theorem B8512283 : Blo 1327482 8512283 := bstep (se 1 (by rfl) ⟨6384212, by rfl⟩ : syracuseStep 8512283 = 12768425) B12768425
theorem B1991657 : Blo 1327482 1991657 := bstep (se 2 (by rfl) ⟨746871, by rfl⟩ : syracuseStep 1991657 = 1493743) B1493743
theorem B1328287 : Blo 1327482 1328287 := bstep (se 1 (by rfl) ⟨996215, by rfl⟩ : syracuseStep 1328287 = 1992431) B1992431
theorem B2835643 : Blo 1327482 2835643 := bstep (se 1 (by rfl) ⟨2126732, by rfl⟩ : syracuseStep 2835643 = 4253465) B4253465
theorem B1328359 : Blo 1327482 1328359 := bstep (se 1 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 1328359 = 1992539) B1992539
theorem B9569515 : Blo 1327482 9569515 := bstep (se 1 (by rfl) ⟨7177136, by rfl⟩ : syracuseStep 9569515 = 14354273) B14354273
theorem B4482323 : Blo 1327482 4482323 := bstep (se 1 (by rfl) ⟨3361742, by rfl⟩ : syracuseStep 4482323 = 6723485) B6723485
theorem B1328799 : Blo 1327482 1328799 := bstep (se 1 (by rfl) ⟨996599, by rfl⟩ : syracuseStep 1328799 = 1993199) B1993199
theorem B4671215 : Blo 1327482 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B48465971 : Blo 1327482 48465971 := bstep (se 1 (by rfl) ⟨36349478, by rfl⟩ : syracuseStep 48465971 = 72698957) B72698957
theorem B1992923 : Blo 1327482 1992923 := bstep (se 1 (by rfl) ⟨1494692, by rfl⟩ : syracuseStep 1992923 = 2989385) B2989385
theorem B8415677 : Blo 1327482 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B2157263 : Blo 1327482 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B4483943 : Blo 1327482 4483943 := bstep (se 1 (by rfl) ⟨3362957, by rfl⟩ : syracuseStep 4483943 = 6725915) B6725915
theorem B6720569 : Blo 1327482 6720569 := bstep (se 2 (by rfl) ⟨2520213, by rfl⟩ : syracuseStep 6720569 = 5040427) B5040427
theorem B1494247 : Blo 1327482 1494247 := bstep (se 1 (by rfl) ⟨1120685, by rfl⟩ : syracuseStep 1494247 = 2241371) B2241371
theorem B6721055 : Blo 1327482 6721055 := bstep (se 1 (by rfl) ⟨5040791, by rfl⟩ : syracuseStep 6721055 = 10081583) B10081583
theorem B4312859 : Blo 1327482 4312859 := bstep (se 1 (by rfl) ⟨3234644, by rfl⟩ : syracuseStep 4312859 = 6469289) B6469289
theorem B13635535 : Blo 1327482 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B8507567 : Blo 1327482 8507567 := bstep (se 1 (by rfl) ⟨6380675, by rfl⟩ : syracuseStep 8507567 = 12761351) B12761351
theorem B4256039 : Blo 1327482 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B7565723 : Blo 1327482 7565723 := bstep (se 1 (by rfl) ⟨5674292, by rfl⟩ : syracuseStep 7565723 = 11348585) B11348585
theorem B2240939 : Blo 1327482 2240939 := bstep (se 1 (by rfl) ⟨1680704, by rfl⟩ : syracuseStep 2240939 = 3361409) B3361409
theorem B22696685 : Blo 1327482 22696685 := bstep (se 3 (by rfl) ⟨4255628, by rfl⟩ : syracuseStep 22696685 = 8511257) B8511257
theorem B4920545 : Blo 1327482 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B2987243 : Blo 1327482 2987243 := bstep (se 1 (by rfl) ⟨2240432, by rfl⟩ : syracuseStep 2987243 = 4480865) B4480865
theorem B4257193 : Blo 1327482 4257193 := bstep (se 2 (by rfl) ⟨1596447, by rfl⟩ : syracuseStep 4257193 = 3192895) B3192895
theorem B3782143 : Blo 1327482 3782143 := bstep (se 1 (by rfl) ⟨2836607, by rfl⟩ : syracuseStep 3782143 = 5673215) B5673215
theorem B2987855 : Blo 1327482 2987855 := bstep (se 1 (by rfl) ⟨2240891, by rfl⟩ : syracuseStep 2987855 = 4481783) B4481783
theorem B2987999 : Blo 1327482 2987999 := bstep (se 1 (by rfl) ⟨2240999, by rfl⟩ : syracuseStep 2987999 = 4481999) B4481999
theorem B41457689 : Blo 1327482 41457689 := bstep (se 2 (by rfl) ⟨15546633, by rfl⟩ : syracuseStep 41457689 = 31093267) B31093267
theorem B11344211 : Blo 1327482 11344211 := bstep (se 1 (by rfl) ⟨8508158, by rfl⟩ : syracuseStep 11344211 = 17016317) B17016317
theorem B6060383 : Blo 1327482 6060383 := bstep (se 1 (by rfl) ⟨4545287, by rfl⟩ : syracuseStep 6060383 = 9090575) B9090575
theorem B2988575 : Blo 1327482 2988575 := bstep (se 1 (by rfl) ⟨2241431, by rfl⟩ : syracuseStep 2988575 = 4482863) B4482863
theorem B5749373 : Blo 1327482 5749373 := bstep (se 3 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 5749373 = 2156015) B2156015
theorem B7183019 : Blo 1327482 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B11344859 : Blo 1327482 11344859 := bstep (se 1 (by rfl) ⟨8508644, by rfl⟩ : syracuseStep 11344859 = 17017289) B17017289
theorem B17488885 : Blo 1327482 17488885 := bstep (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) B1639583
theorem B5045273 : Blo 1327482 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B2989673 : Blo 1327482 2989673 := bstep (se 2 (by rfl) ⟨1121127, by rfl⟩ : syracuseStep 2989673 = 2242255) B2242255
theorem B3784445 : Blo 1327482 3784445 := bstep (se 3 (by rfl) ⟨709583, by rfl⟩ : syracuseStep 3784445 = 1419167) B1419167
theorem B77676347 : Blo 1327482 77676347 := bstep (se 1 (by rfl) ⟨58257260, by rfl⟩ : syracuseStep 77676347 = 116514521) B116514521
theorem B2989907 : Blo 1327482 2989907 := bstep (se 1 (by rfl) ⟨2242430, by rfl⟩ : syracuseStep 2989907 = 4484861) B4484861
theorem B15131123 : Blo 1327482 15131123 := bstep (se 1 (by rfl) ⟨11348342, by rfl⟩ : syracuseStep 15131123 = 22696685) B22696685
theorem B1327771 : Blo 1327482 1327771 := bstep (se 1 (by rfl) ⟨995828, by rfl⟩ : syracuseStep 1327771 = 1991657) B1991657
theorem B1991495 : Blo 1327482 1991495 := bstep (se 1 (by rfl) ⟨1493621, by rfl⟩ : syracuseStep 1991495 = 2987243) B2987243
theorem B3114143 : Blo 1327482 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B1991903 : Blo 1327482 1991903 := bstep (se 1 (by rfl) ⟨1493927, by rfl⟩ : syracuseStep 1991903 = 2987855) B2987855
theorem B1991999 : Blo 1327482 1991999 := bstep (se 1 (by rfl) ⟨1493999, by rfl⟩ : syracuseStep 1991999 = 2987999) B2987999
theorem B32310647 : Blo 1327482 32310647 := bstep (se 1 (by rfl) ⟨24232985, by rfl⟩ : syracuseStep 32310647 = 48465971) B48465971
theorem B1328615 : Blo 1327482 1328615 := bstep (se 1 (by rfl) ⟨996461, by rfl⟩ : syracuseStep 1328615 = 1992923) B1992923
theorem B7562807 : Blo 1327482 7562807 := bstep (se 1 (by rfl) ⟨5672105, by rfl⟩ : syracuseStep 7562807 = 11344211) B11344211
theorem B4040255 : Blo 1327482 4040255 := bstep (se 1 (by rfl) ⟨3030191, by rfl⟩ : syracuseStep 4040255 = 6060383) B6060383
theorem B1992329 : Blo 1327482 1992329 := bstep (se 2 (by rfl) ⟨747123, by rfl⟩ : syracuseStep 1992329 = 1494247) B1494247
theorem B42665629 : Blo 1327482 42665629 := bstep (se 3 (by rfl) ⟨7999805, by rfl⟩ : syracuseStep 42665629 = 15999611) B15999611
theorem B1992383 : Blo 1327482 1992383 := bstep (se 1 (by rfl) ⟨1494287, by rfl⟩ : syracuseStep 1992383 = 2988575) B2988575
theorem B19154717 : Blo 1327482 19154717 := bstep (se 3 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 19154717 = 7183019) B7183019
theorem B7563239 : Blo 1327482 7563239 := bstep (se 1 (by rfl) ⟨5672429, by rfl⟩ : syracuseStep 7563239 = 11344859) B11344859
theorem B1993115 : Blo 1327482 1993115 := bstep (se 1 (by rfl) ⟨1494836, by rfl⟩ : syracuseStep 1993115 = 2989673) B2989673
theorem B51784231 : Blo 1327482 51784231 := bstep (se 1 (by rfl) ⟨38838173, by rfl⟩ : syracuseStep 51784231 = 77676347) B77676347
theorem B1993271 : Blo 1327482 1993271 := bstep (se 1 (by rfl) ⟨1494953, by rfl⟩ : syracuseStep 1993271 = 2989907) B2989907
theorem B18180713 : Blo 1327482 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B5671711 : Blo 1327482 5671711 := bstep (se 1 (by rfl) ⟨4253783, by rfl⟩ : syracuseStep 5671711 = 8507567) B8507567
theorem B2837359 : Blo 1327482 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B1493959 : Blo 1327482 1493959 := bstep (se 1 (by rfl) ⟨1120469, by rfl⟩ : syracuseStep 1493959 = 2240939) B2240939
theorem B23318513 : Blo 1327482 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B3780857 : Blo 1327482 3780857 := bstep (se 2 (by rfl) ⟨1417821, by rfl⟩ : syracuseStep 3780857 = 2835643) B2835643
theorem B12759353 : Blo 1327482 12759353 := bstep (se 2 (by rfl) ⟨4784757, by rfl⟩ : syracuseStep 12759353 = 9569515) B9569515
theorem B1438175 : Blo 1327482 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B5042857 : Blo 1327482 5042857 := bstep (se 2 (by rfl) ⟨1891071, by rfl⟩ : syracuseStep 5042857 = 3782143) B3782143
theorem B3363515 : Blo 1327482 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B5043815 : Blo 1327482 5043815 := bstep (se 1 (by rfl) ⟨3782861, by rfl⟩ : syracuseStep 5043815 = 7565723) B7565723
theorem B6723323 : Blo 1327482 6723323 := bstep (se 1 (by rfl) ⟨5042492, by rfl⟩ : syracuseStep 6723323 = 10084985) B10084985
theorem B5674855 : Blo 1327482 5674855 := bstep (se 1 (by rfl) ⟨4256141, by rfl⟩ : syracuseStep 5674855 = 8512283) B8512283
theorem B13121453 : Blo 1327482 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B2988215 : Blo 1327482 2988215 := bstep (se 1 (by rfl) ⟨2241161, by rfl⟩ : syracuseStep 2988215 = 4482323) B4482323
theorem B27638459 : Blo 1327482 27638459 := bstep (se 1 (by rfl) ⟨20728844, by rfl⟩ : syracuseStep 27638459 = 41457689) B41457689
theorem B5610451 : Blo 1327482 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B3832915 : Blo 1327482 3832915 := bstep (se 1 (by rfl) ⟨2874686, by rfl⟩ : syracuseStep 3832915 = 5749373) B5749373
theorem B5676257 : Blo 1327482 5676257 := bstep (se 2 (by rfl) ⟨2128596, by rfl⟩ : syracuseStep 5676257 = 4257193) B4257193
theorem B2989295 : Blo 1327482 2989295 := bstep (se 1 (by rfl) ⟨2241971, by rfl⟩ : syracuseStep 2989295 = 4483943) B4483943
theorem B4480379 : Blo 1327482 4480379 := bstep (se 1 (by rfl) ⟨3360284, by rfl⟩ : syracuseStep 4480379 = 6720569) B6720569
theorem B11500957 : Blo 1327482 11500957 := bstep (se 3 (by rfl) ⟨2156429, by rfl⟩ : syracuseStep 11500957 = 4312859) B4312859
theorem B4480703 : Blo 1327482 4480703 := bstep (se 1 (by rfl) ⟨3360527, by rfl⟩ : syracuseStep 4480703 = 6721055) B6721055
theorem B2522963 : Blo 1327482 2522963 := bstep (se 1 (by rfl) ⟨1892222, by rfl⟩ : syracuseStep 2522963 = 3784445) B3784445
theorem B1327663 : Blo 1327482 1327663 := bstep (se 1 (by rfl) ⟨995747, by rfl⟩ : syracuseStep 1327663 = 1991495) B1991495
theorem B1327935 : Blo 1327482 1327935 := bstep (se 1 (by rfl) ⟨995951, by rfl⟩ : syracuseStep 1327935 = 1991903) B1991903
theorem B1327999 : Blo 1327482 1327999 := bstep (se 1 (by rfl) ⟨995999, by rfl⟩ : syracuseStep 1327999 = 1991999) B1991999
theorem B7562281 : Blo 1327482 7562281 := bstep (se 2 (by rfl) ⟨2835855, by rfl⟩ : syracuseStep 7562281 = 5671711) B5671711
theorem B1328219 : Blo 1327482 1328219 := bstep (se 1 (by rfl) ⟨996164, by rfl⟩ : syracuseStep 1328219 = 1992329) B1992329
theorem B1328255 : Blo 1327482 1328255 := bstep (se 1 (by rfl) ⟨996191, by rfl⟩ : syracuseStep 1328255 = 1992383) B1992383
theorem B4482215 : Blo 1327482 4482215 := bstep (se 1 (by rfl) ⟨3361661, by rfl⟩ : syracuseStep 4482215 = 6723323) B6723323
theorem B3835133 : Blo 1327482 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B1991945 : Blo 1327482 1991945 := bstep (se 2 (by rfl) ⟨746979, by rfl⟩ : syracuseStep 1991945 = 1493959) B1493959
theorem B7480601 : Blo 1327482 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B1992143 : Blo 1327482 1992143 := bstep (se 1 (by rfl) ⟨1494107, by rfl⟩ : syracuseStep 1992143 = 2988215) B2988215
theorem B1328743 : Blo 1327482 1328743 := bstep (se 1 (by rfl) ⟨996557, by rfl⟩ : syracuseStep 1328743 = 1993115) B1993115
theorem B1328847 : Blo 1327482 1328847 := bstep (se 1 (by rfl) ⟨996635, by rfl⟩ : syracuseStep 1328847 = 1993271) B1993271
theorem B18425639 : Blo 1327482 18425639 := bstep (se 1 (by rfl) ⟨13819229, by rfl⟩ : syracuseStep 18425639 = 27638459) B27638459
theorem B15132581 : Blo 1327482 15132581 := bstep (se 4 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 15132581 = 2837359) B2837359
theorem B1992863 : Blo 1327482 1992863 := bstep (se 1 (by rfl) ⟨1494647, by rfl⟩ : syracuseStep 1992863 = 2989295) B2989295
theorem B56887505 : Blo 1327482 56887505 := bstep (se 2 (by rfl) ⟨21332814, by rfl⟩ : syracuseStep 56887505 = 42665629) B42665629
theorem B1681975 : Blo 1327482 1681975 := bstep (se 1 (by rfl) ⟨1261481, by rfl⟩ : syracuseStep 1681975 = 2522963) B2522963
theorem B8506235 : Blo 1327482 8506235 := bstep (se 1 (by rfl) ⟨6379676, by rfl⟩ : syracuseStep 8506235 = 12759353) B12759353
theorem B10087415 : Blo 1327482 10087415 := bstep (se 1 (by rfl) ⟨7565561, by rfl⟩ : syracuseStep 10087415 = 15131123) B15131123
theorem B69045641 : Blo 1327482 69045641 := bstep (se 2 (by rfl) ⟨25892115, by rfl⟩ : syracuseStep 69045641 = 51784231) B51784231
theorem B2076095 : Blo 1327482 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B21540431 : Blo 1327482 21540431 := bstep (se 1 (by rfl) ⟨16155323, by rfl⟩ : syracuseStep 21540431 = 32310647) B32310647
theorem B5041871 : Blo 1327482 5041871 := bstep (se 1 (by rfl) ⟨3781403, by rfl⟩ : syracuseStep 5041871 = 7562807) B7562807
theorem B3362543 : Blo 1327482 3362543 := bstep (se 1 (by rfl) ⟨2521907, by rfl⟩ : syracuseStep 3362543 = 5043815) B5043815
theorem B5042159 : Blo 1327482 5042159 := bstep (se 1 (by rfl) ⟨3781619, by rfl⟩ : syracuseStep 5042159 = 7563239) B7563239
theorem B12120475 : Blo 1327482 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B2986919 : Blo 1327482 2986919 := bstep (se 1 (by rfl) ⟨2240189, by rfl⟩ : syracuseStep 2986919 = 4480379) B4480379
theorem B2987135 : Blo 1327482 2987135 := bstep (se 1 (by rfl) ⟨2240351, by rfl⟩ : syracuseStep 2987135 = 4480703) B4480703
theorem B7566473 : Blo 1327482 7566473 := bstep (se 2 (by rfl) ⟨2837427, by rfl⟩ : syracuseStep 7566473 = 5674855) B5674855
theorem B15545675 : Blo 1327482 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B2520571 : Blo 1327482 2520571 := bstep (se 1 (by rfl) ⟨1890428, by rfl⟩ : syracuseStep 2520571 = 3780857) B3780857
theorem B2242343 : Blo 1327482 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B6723809 : Blo 1327482 6723809 := bstep (se 2 (by rfl) ⟨2521428, by rfl⟩ : syracuseStep 6723809 = 5042857) B5042857
theorem B2693503 : Blo 1327482 2693503 := bstep (se 1 (by rfl) ⟨2020127, by rfl⟩ : syracuseStep 2693503 = 4040255) B4040255
theorem B12769811 : Blo 1327482 12769811 := bstep (se 1 (by rfl) ⟨9577358, by rfl⟩ : syracuseStep 12769811 = 19154717) B19154717
theorem B8747635 : Blo 1327482 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B5110553 : Blo 1327482 5110553 := bstep (se 2 (by rfl) ⟨1916457, by rfl⟩ : syracuseStep 5110553 = 3832915) B3832915
theorem B15334609 : Blo 1327482 15334609 := bstep (se 2 (by rfl) ⟨5750478, by rfl⟩ : syracuseStep 15334609 = 11500957) B11500957
theorem B3784171 : Blo 1327482 3784171 := bstep (se 1 (by rfl) ⟨2838128, by rfl⟩ : syracuseStep 3784171 = 5676257) B5676257
theorem B1991279 : Blo 1327482 1991279 := bstep (se 1 (by rfl) ⟨1493459, by rfl⟩ : syracuseStep 1991279 = 2986919) B2986919
theorem B1991423 : Blo 1327482 1991423 := bstep (se 1 (by rfl) ⟨1493567, by rfl⟩ : syracuseStep 1991423 = 2987135) B2987135
theorem B2556755 : Blo 1327482 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B1327963 : Blo 1327482 1327963 := bstep (se 1 (by rfl) ⟨995972, by rfl⟩ : syracuseStep 1327963 = 1991945) B1991945
theorem B10363783 : Blo 1327482 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B1328095 : Blo 1327482 1328095 := bstep (se 1 (by rfl) ⟨996071, by rfl⟩ : syracuseStep 1328095 = 1992143) B1992143
theorem B1328575 : Blo 1327482 1328575 := bstep (se 1 (by rfl) ⟨996431, by rfl⟩ : syracuseStep 1328575 = 1992863) B1992863
theorem B4482539 : Blo 1327482 4482539 := bstep (se 1 (by rfl) ⟨3361904, by rfl⟩ : syracuseStep 4482539 = 6723809) B6723809
theorem B8513207 : Blo 1327482 8513207 := bstep (se 1 (by rfl) ⟨6384905, by rfl⟩ : syracuseStep 8513207 = 12769811) B12769811
theorem B5670823 : Blo 1327482 5670823 := bstep (se 1 (by rfl) ⟨4253117, by rfl⟩ : syracuseStep 5670823 = 8506235) B8506235
theorem B3360761 : Blo 1327482 3360761 := bstep (se 2 (by rfl) ⟨1260285, by rfl⟩ : syracuseStep 3360761 = 2520571) B2520571
theorem B3361247 : Blo 1327482 3361247 := bstep (se 1 (by rfl) ⟨2520935, by rfl⟩ : syracuseStep 3361247 = 5041871) B5041871
theorem B3361439 : Blo 1327482 3361439 := bstep (se 1 (by rfl) ⟨2521079, by rfl⟩ : syracuseStep 3361439 = 5042159) B5042159
theorem B3591337 : Blo 1327482 3591337 := bstep (se 2 (by rfl) ⟨1346751, by rfl⟩ : syracuseStep 3591337 = 2693503) B2693503
theorem B12283759 : Blo 1327482 12283759 := bstep (se 1 (by rfl) ⟨9212819, by rfl⟩ : syracuseStep 12283759 = 18425639) B18425639
theorem B1494895 : Blo 1327482 1494895 := bstep (se 1 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 1494895 = 2242343) B2242343
theorem B10088387 : Blo 1327482 10088387 := bstep (se 1 (by rfl) ⟨7566290, by rfl⟩ : syracuseStep 10088387 = 15132581) B15132581
theorem B37925003 : Blo 1327482 37925003 := bstep (se 1 (by rfl) ⟨28443752, by rfl⟩ : syracuseStep 37925003 = 56887505) B56887505
theorem B2241695 : Blo 1327482 2241695 := bstep (se 1 (by rfl) ⟨1681271, by rfl⟩ : syracuseStep 2241695 = 3362543) B3362543
theorem B16160633 : Blo 1327482 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B2242633 : Blo 1327482 2242633 := bstep (se 2 (by rfl) ⟨840987, by rfl⟩ : syracuseStep 2242633 = 1681975) B1681975
theorem B5044315 : Blo 1327482 5044315 := bstep (se 1 (by rfl) ⟨3783236, by rfl⟩ : syracuseStep 5044315 = 7566473) B7566473
theorem B2988143 : Blo 1327482 2988143 := bstep (se 1 (by rfl) ⟨2241107, by rfl⟩ : syracuseStep 2988143 = 4482215) B4482215
theorem B11663513 : Blo 1327482 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B4987067 : Blo 1327482 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B5536253 : Blo 1327482 5536253 := bstep (se 3 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 5536253 = 2076095) B2076095
theorem B10083041 : Blo 1327482 10083041 := bstep (se 2 (by rfl) ⟨3781140, by rfl⟩ : syracuseStep 10083041 = 7562281) B7562281
theorem B20446145 : Blo 1327482 20446145 := bstep (se 2 (by rfl) ⟨7667304, by rfl⟩ : syracuseStep 20446145 = 15334609) B15334609
theorem B3407035 : Blo 1327482 3407035 := bstep (se 1 (by rfl) ⟨2555276, by rfl⟩ : syracuseStep 3407035 = 5110553) B5110553
theorem B5045561 : Blo 1327482 5045561 := bstep (se 2 (by rfl) ⟨1892085, by rfl⟩ : syracuseStep 5045561 = 3784171) B3784171
theorem B6724943 : Blo 1327482 6724943 := bstep (se 1 (by rfl) ⟨5043707, by rfl⟩ : syracuseStep 6724943 = 10087415) B10087415
theorem B46030427 : Blo 1327482 46030427 := bstep (se 1 (by rfl) ⟨34522820, by rfl⟩ : syracuseStep 46030427 = 69045641) B69045641
theorem B14360287 : Blo 1327482 14360287 := bstep (se 1 (by rfl) ⟨10770215, by rfl⟩ : syracuseStep 14360287 = 21540431) B21540431
theorem B2990177 : Blo 1327482 2990177 := bstep (se 2 (by rfl) ⟨1121316, by rfl⟩ : syracuseStep 2990177 = 2242633) B2242633
theorem B6725753 : Blo 1327482 6725753 := bstep (se 2 (by rfl) ⟨2522157, by rfl⟩ : syracuseStep 6725753 = 5044315) B5044315
theorem B1327519 : Blo 1327482 1327519 := bstep (se 1 (by rfl) ⟨995639, by rfl⟩ : syracuseStep 1327519 = 1991279) B1991279
theorem B1327615 : Blo 1327482 1327615 := bstep (se 1 (by rfl) ⟨995711, by rfl⟩ : syracuseStep 1327615 = 1991423) B1991423
theorem B1704503 : Blo 1327482 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B10773755 : Blo 1327482 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B1992095 : Blo 1327482 1992095 := bstep (se 1 (by rfl) ⟨1494071, by rfl⟩ : syracuseStep 1992095 = 2988143) B2988143
theorem B7775675 : Blo 1327482 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B4483295 : Blo 1327482 4483295 := bstep (se 1 (by rfl) ⟨3362471, by rfl⟩ : syracuseStep 4483295 = 6724943) B6724943
theorem B19147049 : Blo 1327482 19147049 := bstep (se 2 (by rfl) ⟨7180143, by rfl⟩ : syracuseStep 19147049 = 14360287) B14360287
theorem B16378345 : Blo 1327482 16378345 := bstep (se 2 (by rfl) ⟨6141879, by rfl⟩ : syracuseStep 16378345 = 12283759) B12283759
theorem B1993193 : Blo 1327482 1993193 := bstep (se 2 (by rfl) ⟨747447, by rfl⟩ : syracuseStep 1993193 = 1494895) B1494895
theorem B25283335 : Blo 1327482 25283335 := bstep (se 1 (by rfl) ⟨18962501, by rfl⟩ : syracuseStep 25283335 = 37925003) B37925003
theorem B1494463 : Blo 1327482 1494463 := bstep (se 1 (by rfl) ⟨1120847, by rfl⟩ : syracuseStep 1494463 = 2241695) B2241695
theorem B2240507 : Blo 1327482 2240507 := bstep (se 1 (by rfl) ⟨1680380, by rfl⟩ : syracuseStep 2240507 = 3360761) B3360761
theorem B4788449 : Blo 1327482 4788449 := bstep (se 2 (by rfl) ⟨1795668, by rfl⟩ : syracuseStep 4788449 = 3591337) B3591337
theorem B4542713 : Blo 1327482 4542713 := bstep (se 2 (by rfl) ⟨1703517, by rfl⟩ : syracuseStep 4542713 = 3407035) B3407035
theorem B2240831 : Blo 1327482 2240831 := bstep (se 1 (by rfl) ⟨1680623, by rfl⟩ : syracuseStep 2240831 = 3361247) B3361247
theorem B3690835 : Blo 1327482 3690835 := bstep (se 1 (by rfl) ⟨2768126, by rfl⟩ : syracuseStep 3690835 = 5536253) B5536253
theorem B2240959 : Blo 1327482 2240959 := bstep (se 1 (by rfl) ⟨1680719, by rfl⟩ : syracuseStep 2240959 = 3361439) B3361439
theorem B6722027 : Blo 1327482 6722027 := bstep (se 1 (by rfl) ⟨5041520, by rfl⟩ : syracuseStep 6722027 = 10083041) B10083041
theorem B53195381 : Blo 1327482 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B3363707 : Blo 1327482 3363707 := bstep (se 1 (by rfl) ⟨2522780, by rfl⟩ : syracuseStep 3363707 = 5045561) B5045561
theorem B2988359 : Blo 1327482 2988359 := bstep (se 1 (by rfl) ⟨2241269, by rfl⟩ : syracuseStep 2988359 = 4482539) B4482539
theorem B5675471 : Blo 1327482 5675471 := bstep (se 1 (by rfl) ⟨4256603, by rfl⟩ : syracuseStep 5675471 = 8513207) B8513207
theorem B13818377 : Blo 1327482 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B13630763 : Blo 1327482 13630763 := bstep (se 1 (by rfl) ⟨10223072, by rfl⟩ : syracuseStep 13630763 = 20446145) B20446145
theorem B30686951 : Blo 1327482 30686951 := bstep (se 1 (by rfl) ⟨23015213, by rfl⟩ : syracuseStep 30686951 = 46030427) B46030427
theorem B7561097 : Blo 1327482 7561097 := bstep (se 2 (by rfl) ⟨2835411, by rfl⟩ : syracuseStep 7561097 = 5670823) B5670823
theorem B6725591 : Blo 1327482 6725591 := bstep (se 1 (by rfl) ⟨5044193, by rfl⟩ : syracuseStep 6725591 = 10088387) B10088387
theorem B4481351 : Blo 1327482 4481351 := bstep (se 1 (by rfl) ⟨3361013, by rfl⟩ : syracuseStep 4481351 = 6722027) B6722027
theorem B35463587 : Blo 1327482 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B1328063 : Blo 1327482 1328063 := bstep (se 1 (by rfl) ⟨996047, by rfl⟩ : syracuseStep 1328063 = 1992095) B1992095
theorem B33711113 : Blo 1327482 33711113 := bstep (se 2 (by rfl) ⟨12641667, by rfl⟩ : syracuseStep 33711113 = 25283335) B25283335
theorem B36849005 : Blo 1327482 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B12764699 : Blo 1327482 12764699 := bstep (se 1 (by rfl) ⟨9573524, by rfl⟩ : syracuseStep 12764699 = 19147049) B19147049
theorem B1992239 : Blo 1327482 1992239 := bstep (se 1 (by rfl) ⟨1494179, by rfl⟩ : syracuseStep 1992239 = 2988359) B2988359
theorem B1328795 : Blo 1327482 1328795 := bstep (se 1 (by rfl) ⟨996596, by rfl⟩ : syracuseStep 1328795 = 1993193) B1993193
theorem B1992617 : Blo 1327482 1992617 := bstep (se 2 (by rfl) ⟨747231, by rfl⟩ : syracuseStep 1992617 = 1494463) B1494463
theorem B81831869 : Blo 1327482 81831869 := bstep (se 3 (by rfl) ⟨15343475, by rfl⟩ : syracuseStep 81831869 = 30686951) B30686951
theorem B9087175 : Blo 1327482 9087175 := bstep (se 1 (by rfl) ⟨6815381, by rfl⟩ : syracuseStep 9087175 = 13630763) B13630763
theorem B5040731 : Blo 1327482 5040731 := bstep (se 1 (by rfl) ⟨3780548, by rfl⟩ : syracuseStep 5040731 = 7561097) B7561097
theorem B4483727 : Blo 1327482 4483727 := bstep (se 1 (by rfl) ⟨3362795, by rfl⟩ : syracuseStep 4483727 = 6725591) B6725591
theorem B1493671 : Blo 1327482 1493671 := bstep (se 1 (by rfl) ⟨1120253, by rfl⟩ : syracuseStep 1493671 = 2240507) B2240507
theorem B1993451 : Blo 1327482 1993451 := bstep (se 1 (by rfl) ⟨1495088, by rfl⟩ : syracuseStep 1993451 = 2990177) B2990177
theorem B4483835 : Blo 1327482 4483835 := bstep (se 1 (by rfl) ⟨3362876, by rfl⟩ : syracuseStep 4483835 = 6725753) B6725753
theorem B1493887 : Blo 1327482 1493887 := bstep (se 1 (by rfl) ⟨1120415, by rfl⟩ : syracuseStep 1493887 = 2240831) B2240831
theorem B3192299 : Blo 1327482 3192299 := bstep (se 1 (by rfl) ⟨2394224, by rfl⟩ : syracuseStep 3192299 = 4788449) B4788449
theorem B3028475 : Blo 1327482 3028475 := bstep (se 1 (by rfl) ⟨2271356, by rfl⟩ : syracuseStep 3028475 = 4542713) B4542713
theorem B2242471 : Blo 1327482 2242471 := bstep (se 1 (by rfl) ⟨1681853, by rfl⟩ : syracuseStep 2242471 = 3363707) B3363707
theorem B2987945 : Blo 1327482 2987945 := bstep (se 2 (by rfl) ⟨1120479, by rfl⟩ : syracuseStep 2987945 = 2240959) B2240959
theorem B7182503 : Blo 1327482 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B5183783 : Blo 1327482 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B4545341 : Blo 1327482 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B2988863 : Blo 1327482 2988863 := bstep (se 1 (by rfl) ⟨2241647, by rfl⟩ : syracuseStep 2988863 = 4483295) B4483295
theorem B3783647 : Blo 1327482 3783647 := bstep (se 1 (by rfl) ⟨2837735, by rfl⟩ : syracuseStep 3783647 = 5675471) B5675471
theorem B19684453 : Blo 1327482 19684453 := bstep (se 4 (by rfl) ⟨1845417, by rfl⟩ : syracuseStep 19684453 = 3690835) B3690835
theorem B87351173 : Blo 1327482 87351173 := bstep (se 4 (by rfl) ⟨8189172, by rfl⟩ : syracuseStep 87351173 = 16378345) B16378345
theorem B12116233 : Blo 1327482 12116233 := bstep (se 2 (by rfl) ⟨4543587, by rfl⟩ : syracuseStep 12116233 = 9087175) B9087175
theorem B1991561 : Blo 1327482 1991561 := bstep (se 2 (by rfl) ⟨746835, by rfl⟩ : syracuseStep 1991561 = 1493671) B1493671
theorem B1328159 : Blo 1327482 1328159 := bstep (se 1 (by rfl) ⟨996119, by rfl⟩ : syracuseStep 1328159 = 1992239) B1992239
theorem B1991849 : Blo 1327482 1991849 := bstep (se 2 (by rfl) ⟨746943, by rfl⟩ : syracuseStep 1991849 = 1493887) B1493887
theorem B1991963 : Blo 1327482 1991963 := bstep (se 1 (by rfl) ⟨1493972, by rfl⟩ : syracuseStep 1991963 = 2987945) B2987945
theorem B1328411 : Blo 1327482 1328411 := bstep (se 1 (by rfl) ⟨996308, by rfl⟩ : syracuseStep 1328411 = 1992617) B1992617
theorem B3360487 : Blo 1327482 3360487 := bstep (se 1 (by rfl) ⟨2520365, by rfl⟩ : syracuseStep 3360487 = 5040731) B5040731
theorem B1328967 : Blo 1327482 1328967 := bstep (se 1 (by rfl) ⟨996725, by rfl⟩ : syracuseStep 1328967 = 1993451) B1993451
theorem B1992575 : Blo 1327482 1992575 := bstep (se 1 (by rfl) ⟨1494431, by rfl⟩ : syracuseStep 1992575 = 2988863) B2988863
theorem B54554579 : Blo 1327482 54554579 := bstep (se 1 (by rfl) ⟨40915934, by rfl⟩ : syracuseStep 54554579 = 81831869) B81831869
theorem B4788335 : Blo 1327482 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B378278261 : Blo 1327482 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B58234115 : Blo 1327482 58234115 := bstep (se 1 (by rfl) ⟨43675586, by rfl⟩ : syracuseStep 58234115 = 87351173) B87351173
theorem B89896301 : Blo 1327482 89896301 := bstep (se 3 (by rfl) ⟨16855556, by rfl⟩ : syracuseStep 89896301 = 33711113) B33711113
theorem B2987567 : Blo 1327482 2987567 := bstep (se 1 (by rfl) ⟨2240675, by rfl⟩ : syracuseStep 2987567 = 4481351) B4481351
theorem B24566003 : Blo 1327482 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B2128199 : Blo 1327482 2128199 := bstep (se 1 (by rfl) ⟨1596149, by rfl⟩ : syracuseStep 2128199 = 3192299) B3192299
theorem B8509799 : Blo 1327482 8509799 := bstep (se 1 (by rfl) ⟨6382349, by rfl⟩ : syracuseStep 8509799 = 12764699) B12764699
theorem B8075933 : Blo 1327482 8075933 := bstep (se 3 (by rfl) ⟨1514237, by rfl⟩ : syracuseStep 8075933 = 3028475) B3028475
theorem B26245937 : Blo 1327482 26245937 := bstep (se 2 (by rfl) ⟨9842226, by rfl⟩ : syracuseStep 26245937 = 19684453) B19684453
theorem B3455855 : Blo 1327482 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B2989151 : Blo 1327482 2989151 := bstep (se 1 (by rfl) ⟨2241863, by rfl⟩ : syracuseStep 2989151 = 4483727) B4483727
theorem B2989223 : Blo 1327482 2989223 := bstep (se 1 (by rfl) ⟨2241917, by rfl⟩ : syracuseStep 2989223 = 4483835) B4483835
theorem B3030227 : Blo 1327482 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B2522431 : Blo 1327482 2522431 := bstep (se 1 (by rfl) ⟨1891823, by rfl⟩ : syracuseStep 2522431 = 3783647) B3783647
theorem B2989961 : Blo 1327482 2989961 := bstep (se 2 (by rfl) ⟨1121235, by rfl⟩ : syracuseStep 2989961 = 2242471) B2242471
theorem B16154977 : Blo 1327482 16154977 := bstep (se 2 (by rfl) ⟨6058116, by rfl⟩ : syracuseStep 16154977 = 12116233) B12116233
theorem B1327707 : Blo 1327482 1327707 := bstep (se 1 (by rfl) ⟨995780, by rfl⟩ : syracuseStep 1327707 = 1991561) B1991561
theorem B1327899 : Blo 1327482 1327899 := bstep (se 1 (by rfl) ⟨995924, by rfl⟩ : syracuseStep 1327899 = 1991849) B1991849
theorem B38822743 : Blo 1327482 38822743 := bstep (se 1 (by rfl) ⟨29117057, by rfl⟩ : syracuseStep 38822743 = 58234115) B58234115
theorem B1327975 : Blo 1327482 1327975 := bstep (se 1 (by rfl) ⟨995981, by rfl⟩ : syracuseStep 1327975 = 1991963) B1991963
theorem B1991711 : Blo 1327482 1991711 := bstep (se 1 (by rfl) ⟨1493783, by rfl⟩ : syracuseStep 1991711 = 2987567) B2987567
theorem B1328383 : Blo 1327482 1328383 := bstep (se 1 (by rfl) ⟨996287, by rfl⟩ : syracuseStep 1328383 = 1992575) B1992575
theorem B16377335 : Blo 1327482 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B5383955 : Blo 1327482 5383955 := bstep (se 1 (by rfl) ⟨4037966, by rfl⟩ : syracuseStep 5383955 = 8075933) B8075933
theorem B2303903 : Blo 1327482 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B1992767 : Blo 1327482 1992767 := bstep (se 1 (by rfl) ⟨1494575, by rfl⟩ : syracuseStep 1992767 = 2989151) B2989151
theorem B1992815 : Blo 1327482 1992815 := bstep (se 1 (by rfl) ⟨1494611, by rfl⟩ : syracuseStep 1992815 = 2989223) B2989223
theorem B1993307 : Blo 1327482 1993307 := bstep (se 1 (by rfl) ⟨1494980, by rfl⟩ : syracuseStep 1993307 = 2989961) B2989961
theorem B252185507 : Blo 1327482 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B5673199 : Blo 1327482 5673199 := bstep (se 1 (by rfl) ⟨4254899, by rfl⟩ : syracuseStep 5673199 = 8509799) B8509799
theorem B3363241 : Blo 1327482 3363241 := bstep (se 2 (by rfl) ⟨1261215, by rfl⟩ : syracuseStep 3363241 = 2522431) B2522431
theorem B2020151 : Blo 1327482 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B36369719 : Blo 1327482 36369719 := bstep (se 1 (by rfl) ⟨27277289, by rfl⟩ : syracuseStep 36369719 = 54554579) B54554579
theorem B3192223 : Blo 1327482 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B5675197 : Blo 1327482 5675197 := bstep (se 3 (by rfl) ⟨1064099, by rfl⟩ : syracuseStep 5675197 = 2128199) B2128199
theorem B59930867 : Blo 1327482 59930867 := bstep (se 1 (by rfl) ⟨44948150, by rfl⟩ : syracuseStep 59930867 = 89896301) B89896301
theorem B17497291 : Blo 1327482 17497291 := bstep (se 1 (by rfl) ⟨13122968, by rfl⟩ : syracuseStep 17497291 = 26245937) B26245937
theorem B4480649 : Blo 1327482 4480649 := bstep (se 2 (by rfl) ⟨1680243, by rfl⟩ : syracuseStep 4480649 = 3360487) B3360487
theorem B1327807 : Blo 1327482 1327807 := bstep (se 1 (by rfl) ⟨995855, by rfl⟩ : syracuseStep 1327807 = 1991711) B1991711
theorem B3589303 : Blo 1327482 3589303 := bstep (se 1 (by rfl) ⟨2691977, by rfl⟩ : syracuseStep 3589303 = 5383955) B5383955
theorem B1328511 : Blo 1327482 1328511 := bstep (se 1 (by rfl) ⟨996383, by rfl⟩ : syracuseStep 1328511 = 1992767) B1992767
theorem B1328543 : Blo 1327482 1328543 := bstep (se 1 (by rfl) ⟨996407, by rfl⟩ : syracuseStep 1328543 = 1992815) B1992815
theorem B39953911 : Blo 1327482 39953911 := bstep (se 1 (by rfl) ⟨29965433, by rfl⟩ : syracuseStep 39953911 = 59930867) B59930867
theorem B1328871 : Blo 1327482 1328871 := bstep (se 1 (by rfl) ⟨996653, by rfl⟩ : syracuseStep 1328871 = 1993307) B1993307
theorem B207054629 : Blo 1327482 207054629 := bstep (se 4 (by rfl) ⟨19411371, by rfl⟩ : syracuseStep 207054629 = 38822743) B38822743
theorem B7564265 : Blo 1327482 7564265 := bstep (se 2 (by rfl) ⟨2836599, by rfl⟩ : syracuseStep 7564265 = 5673199) B5673199
theorem B21539969 : Blo 1327482 21539969 := bstep (se 2 (by rfl) ⟨8077488, by rfl⟩ : syracuseStep 21539969 = 16154977) B16154977
theorem B4484321 : Blo 1327482 4484321 := bstep (se 2 (by rfl) ⟨1681620, by rfl⟩ : syracuseStep 4484321 = 3363241) B3363241
theorem B1535935 : Blo 1327482 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B4256297 : Blo 1327482 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B5387069 : Blo 1327482 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B2987099 : Blo 1327482 2987099 := bstep (se 1 (by rfl) ⟨2240324, by rfl⟩ : syracuseStep 2987099 = 4480649) B4480649
theorem B7566929 : Blo 1327482 7566929 := bstep (se 2 (by rfl) ⟨2837598, by rfl⟩ : syracuseStep 7566929 = 5675197) B5675197
theorem B24246479 : Blo 1327482 24246479 := bstep (se 1 (by rfl) ⟨18184859, by rfl⟩ : syracuseStep 24246479 = 36369719) B36369719
theorem B10918223 : Blo 1327482 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B23329721 : Blo 1327482 23329721 := bstep (se 2 (by rfl) ⟨8748645, by rfl⟩ : syracuseStep 23329721 = 17497291) B17497291
theorem B168123671 : Blo 1327482 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B1991399 : Blo 1327482 1991399 := bstep (se 1 (by rfl) ⟨1493549, by rfl⟩ : syracuseStep 1991399 = 2987099) B2987099
theorem B138036419 : Blo 1327482 138036419 := bstep (se 1 (by rfl) ⟨103527314, by rfl⟩ : syracuseStep 138036419 = 207054629) B207054629
theorem B16164319 : Blo 1327482 16164319 := bstep (se 1 (by rfl) ⟨12123239, by rfl⟩ : syracuseStep 16164319 = 24246479) B24246479
theorem B4785737 : Blo 1327482 4785737 := bstep (se 2 (by rfl) ⟨1794651, by rfl⟩ : syracuseStep 4785737 = 3589303) B3589303
theorem B2837531 : Blo 1327482 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B3591379 : Blo 1327482 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B7278815 : Blo 1327482 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B15553147 : Blo 1327482 15553147 := bstep (se 1 (by rfl) ⟨11664860, by rfl⟩ : syracuseStep 15553147 = 23329721) B23329721
theorem B5042843 : Blo 1327482 5042843 := bstep (se 1 (by rfl) ⟨3782132, by rfl⟩ : syracuseStep 5042843 = 7564265) B7564265
theorem B5044619 : Blo 1327482 5044619 := bstep (se 1 (by rfl) ⟨3783464, by rfl⟩ : syracuseStep 5044619 = 7566929) B7566929
theorem B53271881 : Blo 1327482 53271881 := bstep (se 2 (by rfl) ⟨19976955, by rfl⟩ : syracuseStep 53271881 = 39953911) B39953911
theorem B14359979 : Blo 1327482 14359979 := bstep (se 1 (by rfl) ⟨10769984, by rfl⟩ : syracuseStep 14359979 = 21539969) B21539969
theorem B2989547 : Blo 1327482 2989547 := bstep (se 1 (by rfl) ⟨2242160, by rfl⟩ : syracuseStep 2989547 = 4484321) B4484321
theorem B112082447 : Blo 1327482 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B2047913 : Blo 1327482 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B1327599 : Blo 1327482 1327599 := bstep (se 1 (by rfl) ⟨995699, by rfl⟩ : syracuseStep 1327599 = 1991399) B1991399
theorem B35514587 : Blo 1327482 35514587 := bstep (se 1 (by rfl) ⟨26635940, by rfl⟩ : syracuseStep 35514587 = 53271881) B53271881
theorem B1993031 : Blo 1327482 1993031 := bstep (se 1 (by rfl) ⟨1494773, by rfl⟩ : syracuseStep 1993031 = 2989547) B2989547
theorem B74721631 : Blo 1327482 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B4852543 : Blo 1327482 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B3361895 : Blo 1327482 3361895 := bstep (se 1 (by rfl) ⟨2521421, by rfl⟩ : syracuseStep 3361895 = 5042843) B5042843
theorem B92024279 : Blo 1327482 92024279 := bstep (se 1 (by rfl) ⟨69018209, by rfl⟩ : syracuseStep 92024279 = 138036419) B138036419
theorem B20737529 : Blo 1327482 20737529 := bstep (se 2 (by rfl) ⟨7776573, by rfl⟩ : syracuseStep 20737529 = 15553147) B15553147
theorem B3363079 : Blo 1327482 3363079 := bstep (se 1 (by rfl) ⟨2522309, by rfl⟩ : syracuseStep 3363079 = 5044619) B5044619
theorem B4788505 : Blo 1327482 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B9573319 : Blo 1327482 9573319 := bstep (se 1 (by rfl) ⟨7179989, by rfl⟩ : syracuseStep 9573319 = 14359979) B14359979
theorem B1365275 : Blo 1327482 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B12761965 : Blo 1327482 12761965 := bstep (se 3 (by rfl) ⟨2392868, by rfl⟩ : syracuseStep 12761965 = 4785737) B4785737
theorem B21552425 : Blo 1327482 21552425 := bstep (se 2 (by rfl) ⟨8082159, by rfl⟩ : syracuseStep 21552425 = 16164319) B16164319
theorem B1891687 : Blo 1327482 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B17015953 : Blo 1327482 17015953 := bstep (se 2 (by rfl) ⟨6380982, by rfl⟩ : syracuseStep 17015953 = 12761965) B12761965
theorem B23676391 : Blo 1327482 23676391 := bstep (se 1 (by rfl) ⟨17757293, by rfl⟩ : syracuseStep 23676391 = 35514587) B35514587
theorem B1328687 : Blo 1327482 1328687 := bstep (se 1 (by rfl) ⟨996515, by rfl⟩ : syracuseStep 1328687 = 1993031) B1993031
theorem B4484105 : Blo 1327482 4484105 := bstep (se 2 (by rfl) ⟨1681539, by rfl⟩ : syracuseStep 4484105 = 3363079) B3363079
theorem B6384673 : Blo 1327482 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B3640733 : Blo 1327482 3640733 := bstep (se 3 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 3640733 = 1365275) B1365275
theorem B2241263 : Blo 1327482 2241263 := bstep (se 1 (by rfl) ⟨1680947, by rfl⟩ : syracuseStep 2241263 = 3361895) B3361895
theorem B13825019 : Blo 1327482 13825019 := bstep (se 1 (by rfl) ⟨10368764, by rfl⟩ : syracuseStep 13825019 = 20737529) B20737529
theorem B51057701 : Blo 1327482 51057701 := bstep (se 4 (by rfl) ⟨4786659, by rfl⟩ : syracuseStep 51057701 = 9573319) B9573319
theorem B99628841 : Blo 1327482 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B6470057 : Blo 1327482 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B2522249 : Blo 1327482 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B14368283 : Blo 1327482 14368283 := bstep (se 1 (by rfl) ⟨10776212, by rfl⟩ : syracuseStep 14368283 = 21552425) B21552425
theorem B61349519 : Blo 1327482 61349519 := bstep (se 1 (by rfl) ⟨46012139, by rfl⟩ : syracuseStep 61349519 = 92024279) B92024279
theorem B9216679 : Blo 1327482 9216679 := bstep (se 1 (by rfl) ⟨6912509, by rfl⟩ : syracuseStep 9216679 = 13825019) B13825019
theorem B34038467 : Blo 1327482 34038467 := bstep (se 1 (by rfl) ⟨25528850, by rfl⟩ : syracuseStep 34038467 = 51057701) B51057701
theorem B17253485 : Blo 1327482 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B1681499 : Blo 1327482 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B2427155 : Blo 1327482 2427155 := bstep (se 1 (by rfl) ⟨1820366, by rfl⟩ : syracuseStep 2427155 = 3640733) B3640733
theorem B9578855 : Blo 1327482 9578855 := bstep (se 1 (by rfl) ⟨7184141, by rfl⟩ : syracuseStep 9578855 = 14368283) B14368283
theorem B1494175 : Blo 1327482 1494175 := bstep (se 1 (by rfl) ⟨1120631, by rfl⟩ : syracuseStep 1494175 = 2241263) B2241263
theorem B22687937 : Blo 1327482 22687937 := bstep (se 2 (by rfl) ⟨8507976, by rfl⟩ : syracuseStep 22687937 = 17015953) B17015953
theorem B163598717 : Blo 1327482 163598717 := bstep (se 3 (by rfl) ⟨30674759, by rfl⟩ : syracuseStep 163598717 = 61349519) B61349519
theorem B31568521 : Blo 1327482 31568521 := bstep (se 2 (by rfl) ⟨11838195, by rfl⟩ : syracuseStep 31568521 = 23676391) B23676391
theorem B34051589 : Blo 1327482 34051589 := bstep (se 4 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 34051589 = 6384673) B6384673
theorem B66419227 : Blo 1327482 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B2989403 : Blo 1327482 2989403 := bstep (se 1 (by rfl) ⟨2242052, by rfl⟩ : syracuseStep 2989403 = 4484105) B4484105
theorem B22692311 : Blo 1327482 22692311 := bstep (se 1 (by rfl) ⟨17019233, by rfl⟩ : syracuseStep 22692311 = 34038467) B34038467
theorem B11502323 : Blo 1327482 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B42091361 : Blo 1327482 42091361 := bstep (se 2 (by rfl) ⟨15784260, by rfl⟩ : syracuseStep 42091361 = 31568521) B31568521
theorem B12288905 : Blo 1327482 12288905 := bstep (se 2 (by rfl) ⟨4608339, by rfl⟩ : syracuseStep 12288905 = 9216679) B9216679
theorem B25543613 : Blo 1327482 25543613 := bstep (se 3 (by rfl) ⟨4789427, by rfl⟩ : syracuseStep 25543613 = 9578855) B9578855
theorem B22701059 : Blo 1327482 22701059 := bstep (se 1 (by rfl) ⟨17025794, by rfl⟩ : syracuseStep 22701059 = 34051589) B34051589
theorem B1992233 : Blo 1327482 1992233 := bstep (se 2 (by rfl) ⟨747087, by rfl⟩ : syracuseStep 1992233 = 1494175) B1494175
theorem B1992935 : Blo 1327482 1992935 := bstep (se 1 (by rfl) ⟨1494701, by rfl⟩ : syracuseStep 1992935 = 2989403) B2989403
theorem B15125291 : Blo 1327482 15125291 := bstep (se 1 (by rfl) ⟨11343968, by rfl⟩ : syracuseStep 15125291 = 22687937) B22687937
theorem B4483997 : Blo 1327482 4483997 := bstep (se 3 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 4483997 = 1681499) B1681499
theorem B88558969 : Blo 1327482 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B1618103 : Blo 1327482 1618103 := bstep (se 1 (by rfl) ⟨1213577, by rfl⟩ : syracuseStep 1618103 = 2427155) B2427155
theorem B109065811 : Blo 1327482 109065811 := bstep (se 1 (by rfl) ⟨81799358, by rfl⟩ : syracuseStep 109065811 = 163598717) B163598717
theorem B7668215 : Blo 1327482 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B8192603 : Blo 1327482 8192603 := bstep (se 1 (by rfl) ⟨6144452, by rfl⟩ : syracuseStep 8192603 = 12288905) B12288905
theorem B1328155 : Blo 1327482 1328155 := bstep (se 1 (by rfl) ⟨996116, by rfl⟩ : syracuseStep 1328155 = 1992233) B1992233
theorem B1328623 : Blo 1327482 1328623 := bstep (se 1 (by rfl) ⟨996467, by rfl⟩ : syracuseStep 1328623 = 1992935) B1992935
theorem B15134039 : Blo 1327482 15134039 := bstep (se 1 (by rfl) ⟨11350529, by rfl⟩ : syracuseStep 15134039 = 22701059) B22701059
theorem B448974517 : Blo 1327482 448974517 := bstep (se 5 (by rfl) ⟨21045680, by rfl⟩ : syracuseStep 448974517 = 42091361) B42091361
theorem B145421081 : Blo 1327482 145421081 := bstep (se 2 (by rfl) ⟨54532905, by rfl⟩ : syracuseStep 145421081 = 109065811) B109065811
theorem B15128207 : Blo 1327482 15128207 := bstep (se 1 (by rfl) ⟨11346155, by rfl⟩ : syracuseStep 15128207 = 22692311) B22692311
theorem B4314941 : Blo 1327482 4314941 := bstep (se 3 (by rfl) ⟨809051, by rfl⟩ : syracuseStep 4314941 = 1618103) B1618103
theorem B17029075 : Blo 1327482 17029075 := bstep (se 1 (by rfl) ⟨12771806, by rfl⟩ : syracuseStep 17029075 = 25543613) B25543613
theorem B118078625 : Blo 1327482 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B10083527 : Blo 1327482 10083527 := bstep (se 1 (by rfl) ⟨7562645, by rfl⟩ : syracuseStep 10083527 = 15125291) B15125291
theorem B2989331 : Blo 1327482 2989331 := bstep (se 1 (by rfl) ⟨2241998, by rfl⟩ : syracuseStep 2989331 = 4483997) B4483997
theorem B5112143 : Blo 1327482 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B10085471 : Blo 1327482 10085471 := bstep (se 1 (by rfl) ⟨7564103, by rfl⟩ : syracuseStep 10085471 = 15128207) B15128207
theorem B2876627 : Blo 1327482 2876627 := bstep (se 1 (by rfl) ⟨2157470, by rfl⟩ : syracuseStep 2876627 = 4314941) B4314941
theorem B78719083 : Blo 1327482 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B1992887 : Blo 1327482 1992887 := bstep (se 1 (by rfl) ⟨1494665, by rfl⟩ : syracuseStep 1992887 = 2989331) B2989331
theorem B598632689 : Blo 1327482 598632689 := bstep (se 2 (by rfl) ⟨224487258, by rfl⟩ : syracuseStep 598632689 = 448974517) B448974517
theorem B96947387 : Blo 1327482 96947387 := bstep (se 1 (by rfl) ⟨72710540, by rfl⟩ : syracuseStep 96947387 = 145421081) B145421081
theorem B6722351 : Blo 1327482 6722351 := bstep (se 1 (by rfl) ⟨5041763, by rfl⟩ : syracuseStep 6722351 = 10083527) B10083527
theorem B10089359 : Blo 1327482 10089359 := bstep (se 1 (by rfl) ⟨7567019, by rfl⟩ : syracuseStep 10089359 = 15134039) B15134039
theorem B22705433 : Blo 1327482 22705433 := bstep (se 2 (by rfl) ⟨8514537, by rfl⟩ : syracuseStep 22705433 = 17029075) B17029075
theorem B5461735 : Blo 1327482 5461735 := bstep (se 1 (by rfl) ⟨4096301, by rfl⟩ : syracuseStep 5461735 = 8192603) B8192603
theorem B3408095 : Blo 1327482 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B4481567 : Blo 1327482 4481567 := bstep (se 1 (by rfl) ⟨3361175, by rfl⟩ : syracuseStep 4481567 = 6722351) B6722351
theorem B6726239 : Blo 1327482 6726239 := bstep (se 1 (by rfl) ⟨5044679, by rfl⟩ : syracuseStep 6726239 = 10089359) B10089359
theorem B1917751 : Blo 1327482 1917751 := bstep (se 1 (by rfl) ⟨1438313, by rfl⟩ : syracuseStep 1917751 = 2876627) B2876627
theorem B1328591 : Blo 1327482 1328591 := bstep (se 1 (by rfl) ⟨996443, by rfl⟩ : syracuseStep 1328591 = 1992887) B1992887
theorem B419835109 : Blo 1327482 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B64631591 : Blo 1327482 64631591 := bstep (se 1 (by rfl) ⟨48473693, by rfl⟩ : syracuseStep 64631591 = 96947387) B96947387
theorem B6723647 : Blo 1327482 6723647 := bstep (se 1 (by rfl) ⟨5042735, by rfl⟩ : syracuseStep 6723647 = 10085471) B10085471
theorem B15136955 : Blo 1327482 15136955 := bstep (se 1 (by rfl) ⟨11352716, by rfl⟩ : syracuseStep 15136955 = 22705433) B22705433
theorem B399088459 : Blo 1327482 399088459 := bstep (se 1 (by rfl) ⟨299316344, by rfl⟩ : syracuseStep 399088459 = 598632689) B598632689
theorem B7282313 : Blo 1327482 7282313 := bstep (se 2 (by rfl) ⟨2730867, by rfl⟩ : syracuseStep 7282313 = 5461735) B5461735
theorem B2557001 : Blo 1327482 2557001 := bstep (se 2 (by rfl) ⟨958875, by rfl⟩ : syracuseStep 2557001 = 1917751) B1917751
theorem B4482431 : Blo 1327482 4482431 := bstep (se 1 (by rfl) ⟨3361823, by rfl⟩ : syracuseStep 4482431 = 6723647) B6723647
theorem B2272063 : Blo 1327482 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B4484159 : Blo 1327482 4484159 := bstep (se 1 (by rfl) ⟨3363119, by rfl⟩ : syracuseStep 4484159 = 6726239) B6726239
theorem B559780145 : Blo 1327482 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B4854875 : Blo 1327482 4854875 := bstep (se 1 (by rfl) ⟨3641156, by rfl⟩ : syracuseStep 4854875 = 7282313) B7282313
theorem B2987711 : Blo 1327482 2987711 := bstep (se 1 (by rfl) ⟨2240783, by rfl⟩ : syracuseStep 2987711 = 4481567) B4481567
theorem B43087727 : Blo 1327482 43087727 := bstep (se 1 (by rfl) ⟨32315795, by rfl⟩ : syracuseStep 43087727 = 64631591) B64631591
theorem B532117945 : Blo 1327482 532117945 := bstep (se 2 (by rfl) ⟨199544229, by rfl⟩ : syracuseStep 532117945 = 399088459) B399088459
theorem B10091303 : Blo 1327482 10091303 := bstep (se 1 (by rfl) ⟨7568477, by rfl⟩ : syracuseStep 10091303 = 15136955) B15136955
theorem B373186763 : Blo 1327482 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B1704667 : Blo 1327482 1704667 := bstep (se 1 (by rfl) ⟨1278500, by rfl⟩ : syracuseStep 1704667 = 2557001) B2557001
theorem B1991807 : Blo 1327482 1991807 := bstep (se 1 (by rfl) ⟨1493855, by rfl⟩ : syracuseStep 1991807 = 2987711) B2987711
theorem B6727535 : Blo 1327482 6727535 := bstep (se 1 (by rfl) ⟨5045651, by rfl⟩ : syracuseStep 6727535 = 10091303) B10091303
theorem B51785333 : Blo 1327482 51785333 := bstep (se 5 (by rfl) ⟨2427437, by rfl⟩ : syracuseStep 51785333 = 4854875) B4854875
theorem B28725151 : Blo 1327482 28725151 := bstep (se 1 (by rfl) ⟨21543863, by rfl⟩ : syracuseStep 28725151 = 43087727) B43087727
theorem B709490593 : Blo 1327482 709490593 := bstep (se 2 (by rfl) ⟨266058972, by rfl⟩ : syracuseStep 709490593 = 532117945) B532117945
theorem B2988287 : Blo 1327482 2988287 := bstep (se 1 (by rfl) ⟨2241215, by rfl⟩ : syracuseStep 2988287 = 4482431) B4482431
theorem B3029417 : Blo 1327482 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B2989439 : Blo 1327482 2989439 := bstep (se 1 (by rfl) ⟨2242079, by rfl⟩ : syracuseStep 2989439 = 4484159) B4484159
theorem B248791175 : Blo 1327482 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B1327871 : Blo 1327482 1327871 := bstep (se 1 (by rfl) ⟨995903, by rfl⟩ : syracuseStep 1327871 = 1991807) B1991807
theorem B1992191 : Blo 1327482 1992191 := bstep (se 1 (by rfl) ⟨1494143, by rfl⟩ : syracuseStep 1992191 = 2988287) B2988287
theorem B1992959 : Blo 1327482 1992959 := bstep (se 1 (by rfl) ⟨1494719, by rfl⟩ : syracuseStep 1992959 = 2989439) B2989439
theorem B34523555 : Blo 1327482 34523555 := bstep (se 1 (by rfl) ⟨25892666, by rfl⟩ : syracuseStep 34523555 = 51785333) B51785333
theorem B38300201 : Blo 1327482 38300201 := bstep (se 2 (by rfl) ⟨14362575, by rfl⟩ : syracuseStep 38300201 = 28725151) B28725151
theorem B2272889 : Blo 1327482 2272889 := bstep (se 2 (by rfl) ⟨852333, by rfl⟩ : syracuseStep 2272889 = 1704667) B1704667
theorem B4485023 : Blo 1327482 4485023 := bstep (se 1 (by rfl) ⟨3363767, by rfl⟩ : syracuseStep 4485023 = 6727535) B6727535
theorem B2019611 : Blo 1327482 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B945987457 : Blo 1327482 945987457 := bstep (se 2 (by rfl) ⟨354745296, by rfl⟩ : syracuseStep 945987457 = 709490593) B709490593
theorem B1328127 : Blo 1327482 1328127 := bstep (se 1 (by rfl) ⟨996095, by rfl⟩ : syracuseStep 1328127 = 1992191) B1992191
theorem B92062813 : Blo 1327482 92062813 := bstep (se 3 (by rfl) ⟨17261777, by rfl⟩ : syracuseStep 92062813 = 34523555) B34523555
theorem B1328639 : Blo 1327482 1328639 := bstep (se 1 (by rfl) ⟨996479, by rfl⟩ : syracuseStep 1328639 = 1992959) B1992959
theorem B1261316609 : Blo 1327482 1261316609 := bstep (se 2 (by rfl) ⟨472993728, by rfl⟩ : syracuseStep 1261316609 = 945987457) B945987457
theorem B5385629 : Blo 1327482 5385629 := bstep (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) B2019611
theorem B165860783 : Blo 1327482 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B25533467 : Blo 1327482 25533467 := bstep (se 1 (by rfl) ⟨19150100, by rfl⟩ : syracuseStep 25533467 = 38300201) B38300201
theorem B1515259 : Blo 1327482 1515259 := bstep (se 1 (by rfl) ⟨1136444, by rfl⟩ : syracuseStep 1515259 = 2272889) B2272889
theorem B2990015 : Blo 1327482 2990015 := bstep (se 1 (by rfl) ⟨2242511, by rfl⟩ : syracuseStep 2990015 = 4485023) B4485023
theorem B122750417 : Blo 1327482 122750417 := bstep (se 2 (by rfl) ⟨46031406, by rfl⟩ : syracuseStep 122750417 = 92062813) B92062813
theorem B840877739 : Blo 1327482 840877739 := bstep (se 1 (by rfl) ⟨630658304, by rfl⟩ : syracuseStep 840877739 = 1261316609) B1261316609
theorem B3590419 : Blo 1327482 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B1993343 : Blo 1327482 1993343 := bstep (se 1 (by rfl) ⟨1495007, by rfl⟩ : syracuseStep 1993343 = 2990015) B2990015
theorem B8081381 : Blo 1327482 8081381 := bstep (se 4 (by rfl) ⟨757629, by rfl⟩ : syracuseStep 8081381 = 1515259) B1515259
theorem B110573855 : Blo 1327482 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B17022311 : Blo 1327482 17022311 := bstep (se 1 (by rfl) ⟨12766733, by rfl⟩ : syracuseStep 17022311 = 25533467) B25533467
theorem B1328895 : Blo 1327482 1328895 := bstep (se 1 (by rfl) ⟨996671, by rfl⟩ : syracuseStep 1328895 = 1993343) B1993343
theorem B11348207 : Blo 1327482 11348207 := bstep (se 1 (by rfl) ⟨8511155, by rfl⟩ : syracuseStep 11348207 = 17022311) B17022311
theorem B4787225 : Blo 1327482 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B81833611 : Blo 1327482 81833611 := bstep (se 1 (by rfl) ⟨61375208, by rfl⟩ : syracuseStep 81833611 = 122750417) B122750417
theorem B73715903 : Blo 1327482 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B21550349 : Blo 1327482 21550349 := bstep (se 3 (by rfl) ⟨4040690, by rfl⟩ : syracuseStep 21550349 = 8081381) B8081381
theorem B560585159 : Blo 1327482 560585159 := bstep (se 1 (by rfl) ⟨420438869, by rfl⟩ : syracuseStep 560585159 = 840877739) B840877739
theorem B49143935 : Blo 1327482 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B109111481 : Blo 1327482 109111481 := bstep (se 2 (by rfl) ⟨40916805, by rfl⟩ : syracuseStep 109111481 = 81833611) B81833611
theorem B7565471 : Blo 1327482 7565471 := bstep (se 1 (by rfl) ⟨5674103, by rfl⟩ : syracuseStep 7565471 = 11348207) B11348207
theorem B373723439 : Blo 1327482 373723439 := bstep (se 1 (by rfl) ⟨280292579, by rfl⟩ : syracuseStep 373723439 = 560585159) B560585159
theorem B3191483 : Blo 1327482 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B14366899 : Blo 1327482 14366899 := bstep (se 1 (by rfl) ⟨10775174, by rfl⟩ : syracuseStep 14366899 = 21550349) B21550349
theorem B3986383349 : Blo 1327482 3986383349 := bstep (se 5 (by rfl) ⟨186861719, by rfl⟩ : syracuseStep 3986383349 = 373723439) B373723439
theorem B19155865 : Blo 1327482 19155865 := bstep (se 2 (by rfl) ⟨7183449, by rfl⟩ : syracuseStep 19155865 = 14366899) B14366899
theorem B131050493 : Blo 1327482 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B72740987 : Blo 1327482 72740987 := bstep (se 1 (by rfl) ⟨54555740, by rfl⟩ : syracuseStep 72740987 = 109111481) B109111481
theorem B5043647 : Blo 1327482 5043647 := bstep (se 1 (by rfl) ⟨3782735, by rfl⟩ : syracuseStep 5043647 = 7565471) B7565471
theorem B2127655 : Blo 1327482 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B2836873 : Blo 1327482 2836873 := bstep (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) B2127655
theorem B3362431 : Blo 1327482 3362431 := bstep (se 1 (by rfl) ⟨2521823, by rfl⟩ : syracuseStep 3362431 = 5043647) B5043647
theorem B48493991 : Blo 1327482 48493991 := bstep (se 1 (by rfl) ⟨36370493, by rfl⟩ : syracuseStep 48493991 = 72740987) B72740987
theorem B25541153 : Blo 1327482 25541153 := bstep (se 2 (by rfl) ⟨9577932, by rfl⟩ : syracuseStep 25541153 = 19155865) B19155865
theorem B10630355597 : Blo 1327482 10630355597 := bstep (se 3 (by rfl) ⟨1993191674, by rfl⟩ : syracuseStep 10630355597 = 3986383349) B3986383349
theorem B87366995 : Blo 1327482 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B4483241 : Blo 1327482 4483241 := bstep (se 2 (by rfl) ⟨1681215, by rfl⟩ : syracuseStep 4483241 = 3362431) B3362431
theorem B17027435 : Blo 1327482 17027435 := bstep (se 1 (by rfl) ⟨12770576, by rfl⟩ : syracuseStep 17027435 = 25541153) B25541153
theorem B7086903731 : Blo 1327482 7086903731 := bstep (se 1 (by rfl) ⟨5315177798, by rfl⟩ : syracuseStep 7086903731 = 10630355597) B10630355597
theorem B3782497 : Blo 1327482 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B129317309 : Blo 1327482 129317309 := bstep (se 3 (by rfl) ⟨24246995, by rfl⟩ : syracuseStep 129317309 = 48493991) B48493991
theorem B58244663 : Blo 1327482 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B5043329 : Blo 1327482 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B11351623 : Blo 1327482 11351623 := bstep (se 1 (by rfl) ⟨8513717, by rfl⟩ : syracuseStep 11351623 = 17027435) B17027435
theorem B4724602487 : Blo 1327482 4724602487 := bstep (se 1 (by rfl) ⟨3543451865, by rfl⟩ : syracuseStep 4724602487 = 7086903731) B7086903731
theorem B2988827 : Blo 1327482 2988827 := bstep (se 1 (by rfl) ⟨2241620, by rfl⟩ : syracuseStep 2988827 = 4483241) B4483241
theorem B86211539 : Blo 1327482 86211539 := bstep (se 1 (by rfl) ⟨64658654, by rfl⟩ : syracuseStep 86211539 = 129317309) B129317309
theorem B38829775 : Blo 1327482 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B3149734991 : Blo 1327482 3149734991 := bstep (se 1 (by rfl) ⟨2362301243, by rfl⟩ : syracuseStep 3149734991 = 4724602487) B4724602487
theorem B1992551 : Blo 1327482 1992551 := bstep (se 1 (by rfl) ⟨1494413, by rfl⟩ : syracuseStep 1992551 = 2988827) B2988827
theorem B3362219 : Blo 1327482 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B15135497 : Blo 1327482 15135497 := bstep (se 2 (by rfl) ⟨5675811, by rfl⟩ : syracuseStep 15135497 = 11351623) B11351623
theorem B57474359 : Blo 1327482 57474359 := bstep (se 1 (by rfl) ⟨43105769, by rfl⟩ : syracuseStep 57474359 = 86211539) B86211539
theorem B51773033 : Blo 1327482 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B1328367 : Blo 1327482 1328367 := bstep (se 1 (by rfl) ⟨996275, by rfl⟩ : syracuseStep 1328367 = 1992551) B1992551
theorem B38316239 : Blo 1327482 38316239 := bstep (se 1 (by rfl) ⟨28737179, by rfl⟩ : syracuseStep 38316239 = 57474359) B57474359
theorem B34515355 : Blo 1327482 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B8399293309 : Blo 1327482 8399293309 := bstep (se 3 (by rfl) ⟨1574867495, by rfl⟩ : syracuseStep 8399293309 = 3149734991) B3149734991
theorem B2241479 : Blo 1327482 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B10090331 : Blo 1327482 10090331 := bstep (se 1 (by rfl) ⟨7567748, by rfl⟩ : syracuseStep 10090331 = 15135497) B15135497
theorem B6726887 : Blo 1327482 6726887 := bstep (se 1 (by rfl) ⟨5045165, by rfl⟩ : syracuseStep 6726887 = 10090331) B10090331
theorem B25544159 : Blo 1327482 25544159 := bstep (se 1 (by rfl) ⟨19158119, by rfl⟩ : syracuseStep 25544159 = 38316239) B38316239
theorem B1494319 : Blo 1327482 1494319 := bstep (se 1 (by rfl) ⟨1120739, by rfl⟩ : syracuseStep 1494319 = 2241479) B2241479
theorem B11199057745 : Blo 1327482 11199057745 := bstep (se 2 (by rfl) ⟨4199646654, by rfl⟩ : syracuseStep 11199057745 = 8399293309) B8399293309
theorem B46020473 : Blo 1327482 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B30680315 : Blo 1327482 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B1992425 : Blo 1327482 1992425 := bstep (se 2 (by rfl) ⟨747159, by rfl⟩ : syracuseStep 1992425 = 1494319) B1494319
theorem B14932076993 : Blo 1327482 14932076993 := bstep (se 2 (by rfl) ⟨5599528872, by rfl⟩ : syracuseStep 14932076993 = 11199057745) B11199057745
theorem B4484591 : Blo 1327482 4484591 := bstep (se 1 (by rfl) ⟨3363443, by rfl⟩ : syracuseStep 4484591 = 6726887) B6726887
theorem B17029439 : Blo 1327482 17029439 := bstep (se 1 (by rfl) ⟨12772079, by rfl⟩ : syracuseStep 17029439 = 25544159) B25544159
theorem B1328283 : Blo 1327482 1328283 := bstep (se 1 (by rfl) ⟨996212, by rfl⟩ : syracuseStep 1328283 = 1992425) B1992425
theorem B9954717995 : Blo 1327482 9954717995 := bstep (se 1 (by rfl) ⟨7466038496, by rfl⟩ : syracuseStep 9954717995 = 14932076993) B14932076993
theorem B20453543 : Blo 1327482 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B11352959 : Blo 1327482 11352959 := bstep (se 1 (by rfl) ⟨8514719, by rfl⟩ : syracuseStep 11352959 = 17029439) B17029439
theorem B2989727 : Blo 1327482 2989727 := bstep (se 1 (by rfl) ⟨2242295, by rfl⟩ : syracuseStep 2989727 = 4484591) B4484591
theorem B6636478663 : Blo 1327482 6636478663 := bstep (se 1 (by rfl) ⟨4977358997, by rfl⟩ : syracuseStep 6636478663 = 9954717995) B9954717995
theorem B1993151 : Blo 1327482 1993151 := bstep (se 1 (by rfl) ⟨1494863, by rfl⟩ : syracuseStep 1993151 = 2989727) B2989727
theorem B13635695 : Blo 1327482 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B7568639 : Blo 1327482 7568639 := bstep (se 1 (by rfl) ⟨5676479, by rfl⟩ : syracuseStep 7568639 = 11352959) B11352959
theorem B8848638217 : Blo 1327482 8848638217 := bstep (se 2 (by rfl) ⟨3318239331, by rfl⟩ : syracuseStep 8848638217 = 6636478663) B6636478663
theorem B1328767 : Blo 1327482 1328767 := bstep (se 1 (by rfl) ⟨996575, by rfl⟩ : syracuseStep 1328767 = 1993151) B1993151
theorem B9090463 : Blo 1327482 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B5045759 : Blo 1327482 5045759 := bstep (se 1 (by rfl) ⟨3784319, by rfl⟩ : syracuseStep 5045759 = 7568639) B7568639
theorem B11798184289 : Blo 1327482 11798184289 := bstep (se 2 (by rfl) ⟨4424319108, by rfl⟩ : syracuseStep 11798184289 = 8848638217) B8848638217
theorem B12120617 : Blo 1327482 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B3363839 : Blo 1327482 3363839 := bstep (se 1 (by rfl) ⟨2522879, by rfl⟩ : syracuseStep 3363839 = 5045759) B5045759
theorem B8080411 : Blo 1327482 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B15730912385 : Blo 1327482 15730912385 := bstep (se 2 (by rfl) ⟨5899092144, by rfl⟩ : syracuseStep 15730912385 = 11798184289) B11798184289
theorem B2242559 : Blo 1327482 2242559 := bstep (se 1 (by rfl) ⟨1681919, by rfl⟩ : syracuseStep 2242559 = 3363839) B3363839
theorem B10773881 : Blo 1327482 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B1495039 : Blo 1327482 1495039 := bstep (se 1 (by rfl) ⟨1121279, by rfl⟩ : syracuseStep 1495039 = 2242559) B2242559
theorem B10487274923 : Blo 1327482 10487274923 := bstep (se 1 (by rfl) ⟨7865456192, by rfl⟩ : syracuseStep 10487274923 = 15730912385) B15730912385
theorem B1993385 : Blo 1327482 1993385 := bstep (se 2 (by rfl) ⟨747519, by rfl⟩ : syracuseStep 1993385 = 1495039) B1495039
theorem B6991516615 : Blo 1327482 6991516615 := bstep (se 1 (by rfl) ⟨5243637461, by rfl⟩ : syracuseStep 6991516615 = 10487274923) B10487274923
theorem B7182587 : Blo 1327482 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B9322022153 : Blo 1327482 9322022153 := bstep (se 2 (by rfl) ⟨3495758307, by rfl⟩ : syracuseStep 9322022153 = 6991516615) B6991516615
theorem B1328923 : Blo 1327482 1328923 := bstep (se 1 (by rfl) ⟨996692, by rfl⟩ : syracuseStep 1328923 = 1993385) B1993385
theorem B4788391 : Blo 1327482 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B6214681435 : Blo 1327482 6214681435 := bstep (se 1 (by rfl) ⟨4661011076, by rfl⟩ : syracuseStep 6214681435 = 9322022153) B9322022153
theorem B6384521 : Blo 1327482 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B8286241913 : Blo 1327482 8286241913 := bstep (se 2 (by rfl) ⟨3107340717, by rfl⟩ : syracuseStep 8286241913 = 6214681435) B6214681435
theorem B4256347 : Blo 1327482 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B5524161275 : Blo 1327482 5524161275 := bstep (se 1 (by rfl) ⟨4143120956, by rfl⟩ : syracuseStep 5524161275 = 8286241913) B8286241913
theorem B5675129 : Blo 1327482 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B3682774183 : Blo 1327482 3682774183 := bstep (se 1 (by rfl) ⟨2762080637, by rfl⟩ : syracuseStep 3682774183 = 5524161275) B5524161275
theorem B3783419 : Blo 1327482 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B4910365577 : Blo 1327482 4910365577 := bstep (se 2 (by rfl) ⟨1841387091, by rfl⟩ : syracuseStep 4910365577 = 3682774183) B3682774183
theorem B2522279 : Blo 1327482 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B6726077 : Blo 1327482 6726077 := bstep (se 3 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 6726077 = 2522279) B2522279
theorem B3273577051 : Blo 1327482 3273577051 := bstep (se 1 (by rfl) ⟨2455182788, by rfl⟩ : syracuseStep 3273577051 = 4910365577) B4910365577
theorem B4484051 : Blo 1327482 4484051 := bstep (se 1 (by rfl) ⟨3363038, by rfl⟩ : syracuseStep 4484051 = 6726077) B6726077
theorem B4364769401 : Blo 1327482 4364769401 := bstep (se 2 (by rfl) ⟨1636788525, by rfl⟩ : syracuseStep 4364769401 = 3273577051) B3273577051
theorem B2909846267 : Blo 1327482 2909846267 := bstep (se 1 (by rfl) ⟨2182384700, by rfl⟩ : syracuseStep 2909846267 = 4364769401) B4364769401
theorem B2989367 : Blo 1327482 2989367 := bstep (se 1 (by rfl) ⟨2242025, by rfl⟩ : syracuseStep 2989367 = 4484051) B4484051
theorem B1992911 : Blo 1327482 1992911 := bstep (se 1 (by rfl) ⟨1494683, by rfl⟩ : syracuseStep 1992911 = 2989367) B2989367
theorem B1939897511 : Blo 1327482 1939897511 := bstep (se 1 (by rfl) ⟨1454923133, by rfl⟩ : syracuseStep 1939897511 = 2909846267) B2909846267
theorem B1328607 : Blo 1327482 1328607 := bstep (se 1 (by rfl) ⟨996455, by rfl⟩ : syracuseStep 1328607 = 1992911) B1992911
theorem B1293265007 : Blo 1327482 1293265007 := bstep (se 1 (by rfl) ⟨969948755, by rfl⟩ : syracuseStep 1293265007 = 1939897511) B1939897511
theorem B862176671 : Blo 1327482 862176671 := bstep (se 1 (by rfl) ⟨646632503, by rfl⟩ : syracuseStep 862176671 = 1293265007) B1293265007
theorem B574784447 : Blo 1327482 574784447 := bstep (se 1 (by rfl) ⟨431088335, by rfl⟩ : syracuseStep 574784447 = 862176671) B862176671
theorem B6131034101 : Blo 1327482 6131034101 := bstep (se 5 (by rfl) ⟨287392223, by rfl⟩ : syracuseStep 6131034101 = 574784447) B574784447
theorem B4087356067 : Blo 1327482 4087356067 := bstep (se 1 (by rfl) ⟨3065517050, by rfl⟩ : syracuseStep 4087356067 = 6131034101) B6131034101
theorem B5449808089 : Blo 1327482 5449808089 := bstep (se 2 (by rfl) ⟨2043678033, by rfl⟩ : syracuseStep 5449808089 = 4087356067) B4087356067
theorem B7266410785 : Blo 1327482 7266410785 := bstep (se 2 (by rfl) ⟨2724904044, by rfl⟩ : syracuseStep 7266410785 = 5449808089) B5449808089
theorem B9688547713 : Blo 1327482 9688547713 := bstep (se 2 (by rfl) ⟨3633205392, by rfl⟩ : syracuseStep 9688547713 = 7266410785) B7266410785
theorem B12918063617 : Blo 1327482 12918063617 := bstep (se 2 (by rfl) ⟨4844273856, by rfl⟩ : syracuseStep 12918063617 = 9688547713) B9688547713
theorem B8612042411 : Blo 1327482 8612042411 := bstep (se 1 (by rfl) ⟨6459031808, by rfl⟩ : syracuseStep 8612042411 = 12918063617) B12918063617
theorem B5741361607 : Blo 1327482 5741361607 := bstep (se 1 (by rfl) ⟨4306021205, by rfl⟩ : syracuseStep 5741361607 = 8612042411) B8612042411
theorem B7655148809 : Blo 1327482 7655148809 := bstep (se 2 (by rfl) ⟨2870680803, by rfl⟩ : syracuseStep 7655148809 = 5741361607) B5741361607
theorem B5103432539 : Blo 1327482 5103432539 := bstep (se 1 (by rfl) ⟨3827574404, by rfl⟩ : syracuseStep 5103432539 = 7655148809) B7655148809
theorem B3402288359 : Blo 1327482 3402288359 := bstep (se 1 (by rfl) ⟨2551716269, by rfl⟩ : syracuseStep 3402288359 = 5103432539) B5103432539
theorem B2268192239 : Blo 1327482 2268192239 := bstep (se 1 (by rfl) ⟨1701144179, by rfl⟩ : syracuseStep 2268192239 = 3402288359) B3402288359
theorem B1512128159 : Blo 1327482 1512128159 := bstep (se 1 (by rfl) ⟨1134096119, by rfl⟩ : syracuseStep 1512128159 = 2268192239) B2268192239
theorem B1008085439 : Blo 1327482 1008085439 := bstep (se 1 (by rfl) ⟨756064079, by rfl⟩ : syracuseStep 1008085439 = 1512128159) B1512128159
theorem B2688227837 : Blo 1327482 2688227837 := bstep (se 3 (by rfl) ⟨504042719, by rfl⟩ : syracuseStep 2688227837 = 1008085439) B1008085439
theorem B1792151891 : Blo 1327482 1792151891 := bstep (se 1 (by rfl) ⟨1344113918, by rfl⟩ : syracuseStep 1792151891 = 2688227837) B2688227837
theorem B1194767927 : Blo 1327482 1194767927 := bstep (se 1 (by rfl) ⟨896075945, by rfl⟩ : syracuseStep 1194767927 = 1792151891) B1792151891
theorem B796511951 : Blo 1327482 796511951 := bstep (se 1 (by rfl) ⟨597383963, by rfl⟩ : syracuseStep 796511951 = 1194767927) B1194767927
theorem B531007967 : Blo 1327482 531007967 := bstep (se 1 (by rfl) ⟨398255975, by rfl⟩ : syracuseStep 531007967 = 796511951) B796511951
theorem B354005311 : Blo 1327482 354005311 := bstep (se 1 (by rfl) ⟨265503983, by rfl⟩ : syracuseStep 354005311 = 531007967) B531007967
theorem B472007081 : Blo 1327482 472007081 := bstep (se 2 (by rfl) ⟨177002655, by rfl⟩ : syracuseStep 472007081 = 354005311) B354005311
theorem B314671387 : Blo 1327482 314671387 := bstep (se 1 (by rfl) ⟨236003540, by rfl⟩ : syracuseStep 314671387 = 472007081) B472007081
theorem B419561849 : Blo 1327482 419561849 := bstep (se 2 (by rfl) ⟨157335693, by rfl⟩ : syracuseStep 419561849 = 314671387) B314671387
theorem B279707899 : Blo 1327482 279707899 := bstep (se 1 (by rfl) ⟨209780924, by rfl⟩ : syracuseStep 279707899 = 419561849) B419561849
theorem B372943865 : Blo 1327482 372943865 := bstep (se 2 (by rfl) ⟨139853949, by rfl⟩ : syracuseStep 372943865 = 279707899) B279707899
theorem B994516973 : Blo 1327482 994516973 := bstep (se 3 (by rfl) ⟨186471932, by rfl⟩ : syracuseStep 994516973 = 372943865) B372943865
theorem B663011315 : Blo 1327482 663011315 := bstep (se 1 (by rfl) ⟨497258486, by rfl⟩ : syracuseStep 663011315 = 994516973) B994516973
theorem B442007543 : Blo 1327482 442007543 := bstep (se 1 (by rfl) ⟨331505657, by rfl⟩ : syracuseStep 442007543 = 663011315) B663011315
theorem B294671695 : Blo 1327482 294671695 := bstep (se 1 (by rfl) ⟨221003771, by rfl⟩ : syracuseStep 294671695 = 442007543) B442007543
theorem B392895593 : Blo 1327482 392895593 := bstep (se 2 (by rfl) ⟨147335847, by rfl⟩ : syracuseStep 392895593 = 294671695) B294671695
theorem B261930395 : Blo 1327482 261930395 := bstep (se 1 (by rfl) ⟨196447796, by rfl⟩ : syracuseStep 261930395 = 392895593) B392895593
theorem B698481053 : Blo 1327482 698481053 := bstep (se 3 (by rfl) ⟨130965197, by rfl⟩ : syracuseStep 698481053 = 261930395) B261930395
theorem B465654035 : Blo 1327482 465654035 := bstep (se 1 (by rfl) ⟨349240526, by rfl⟩ : syracuseStep 465654035 = 698481053) B698481053
theorem B310436023 : Blo 1327482 310436023 := bstep (se 1 (by rfl) ⟨232827017, by rfl⟩ : syracuseStep 310436023 = 465654035) B465654035
theorem B413914697 : Blo 1327482 413914697 := bstep (se 2 (by rfl) ⟨155218011, by rfl⟩ : syracuseStep 413914697 = 310436023) B310436023
theorem B275943131 : Blo 1327482 275943131 := bstep (se 1 (by rfl) ⟨206957348, by rfl⟩ : syracuseStep 275943131 = 413914697) B413914697
theorem B183962087 : Blo 1327482 183962087 := bstep (se 1 (by rfl) ⟨137971565, by rfl⟩ : syracuseStep 183962087 = 275943131) B275943131
theorem B122641391 : Blo 1327482 122641391 := bstep (se 1 (by rfl) ⟨91981043, by rfl⟩ : syracuseStep 122641391 = 183962087) B183962087
theorem B81760927 : Blo 1327482 81760927 := bstep (se 1 (by rfl) ⟨61320695, by rfl⟩ : syracuseStep 81760927 = 122641391) B122641391
theorem B109014569 : Blo 1327482 109014569 := bstep (se 2 (by rfl) ⟨40880463, by rfl⟩ : syracuseStep 109014569 = 81760927) B81760927
theorem B72676379 : Blo 1327482 72676379 := bstep (se 1 (by rfl) ⟨54507284, by rfl⟩ : syracuseStep 72676379 = 109014569) B109014569
theorem B48450919 : Blo 1327482 48450919 := bstep (se 1 (by rfl) ⟨36338189, by rfl⟩ : syracuseStep 48450919 = 72676379) B72676379
theorem B64601225 : Blo 1327482 64601225 := bstep (se 2 (by rfl) ⟨24225459, by rfl⟩ : syracuseStep 64601225 = 48450919) B48450919
theorem B43067483 : Blo 1327482 43067483 := bstep (se 1 (by rfl) ⟨32300612, by rfl⟩ : syracuseStep 43067483 = 64601225) B64601225
theorem B28711655 : Blo 1327482 28711655 := bstep (se 1 (by rfl) ⟨21533741, by rfl⟩ : syracuseStep 28711655 = 43067483) B43067483
theorem B19141103 : Blo 1327482 19141103 := bstep (se 1 (by rfl) ⟨14355827, by rfl⟩ : syracuseStep 19141103 = 28711655) B28711655
theorem B12760735 : Blo 1327482 12760735 := bstep (se 1 (by rfl) ⟨9570551, by rfl⟩ : syracuseStep 12760735 = 19141103) B19141103
theorem B17014313 : Blo 1327482 17014313 := bstep (se 2 (by rfl) ⟨6380367, by rfl⟩ : syracuseStep 17014313 = 12760735) B12760735
theorem B11342875 : Blo 1327482 11342875 := bstep (se 1 (by rfl) ⟨8507156, by rfl⟩ : syracuseStep 11342875 = 17014313) B17014313
theorem B15123833 : Blo 1327482 15123833 := bstep (se 2 (by rfl) ⟨5671437, by rfl⟩ : syracuseStep 15123833 = 11342875) B11342875
theorem B10082555 : Blo 1327482 10082555 := bstep (se 1 (by rfl) ⟨7561916, by rfl⟩ : syracuseStep 10082555 = 15123833) B15123833
theorem B6721703 : Blo 1327482 6721703 := bstep (se 1 (by rfl) ⟨5041277, by rfl⟩ : syracuseStep 6721703 = 10082555) B10082555
theorem B4481135 : Blo 1327482 4481135 := bstep (se 1 (by rfl) ⟨3360851, by rfl⟩ : syracuseStep 4481135 = 6721703) B6721703
theorem B2987423 : Blo 1327482 2987423 := bstep (se 1 (by rfl) ⟨2240567, by rfl⟩ : syracuseStep 2987423 = 4481135) B4481135
theorem B1991615 : Blo 1327482 1991615 := bstep (se 1 (by rfl) ⟨1493711, by rfl⟩ : syracuseStep 1991615 = 2987423) B2987423
theorem B1327743 : Blo 1327482 1327743 := bstep (se 1 (by rfl) ⟨995807, by rfl⟩ : syracuseStep 1327743 = 1991615) B1991615

theorem C0 (j : ℕ) (h1 : 331870 ≤ j) (h2 : j ≤ 332244) : Blo 1327482 (4 * j + 3) := by
  interval_cases j
  · exact B1327483
  · exact B1327487
  · exact B1327491
  · exact B1327495
  · exact B1327499
  · exact B1327503
  · exact B1327507
  · exact B1327511
  · exact B1327515
  · exact B1327519
  · exact B1327523
  · exact B1327527
  · exact B1327531
  · exact B1327535
  · exact B1327539
  · exact B1327543
  · exact B1327547
  · exact B1327551
  · exact B1327555
  · exact B1327559
  · exact B1327563
  · exact B1327567
  · exact B1327571
  · exact B1327575
  · exact B1327579
  · exact B1327583
  · exact B1327587
  · exact B1327591
  · exact B1327595
  · exact B1327599
  · exact B1327603
  · exact B1327607
  · exact B1327611
  · exact B1327615
  · exact B1327619
  · exact B1327623
  · exact B1327627
  · exact B1327631
  · exact B1327635
  · exact B1327639
  · exact B1327643
  · exact B1327647
  · exact B1327651
  · exact B1327655
  · exact B1327659
  · exact B1327663
  · exact B1327667
  · exact B1327671
  · exact B1327675
  · exact B1327679
  · exact B1327683
  · exact B1327687
  · exact B1327691
  · exact B1327695
  · exact B1327699
  · exact B1327703
  · exact B1327707
  · exact B1327711
  · exact B1327715
  · exact B1327719
  · exact B1327723
  · exact B1327727
  · exact B1327731
  · exact B1327735
  · exact B1327739
  · exact B1327743
  · exact B1327747
  · exact B1327751
  · exact B1327755
  · exact B1327759
  · exact B1327763
  · exact B1327767
  · exact B1327771
  · exact B1327775
  · exact B1327779
  · exact B1327783
  · exact B1327787
  · exact B1327791
  · exact B1327795
  · exact B1327799
  · exact B1327803
  · exact B1327807
  · exact B1327811
  · exact B1327815
  · exact B1327819
  · exact B1327823
  · exact B1327827
  · exact B1327831
  · exact B1327835
  · exact B1327839
  · exact B1327843
  · exact B1327847
  · exact B1327851
  · exact B1327855
  · exact B1327859
  · exact B1327863
  · exact B1327867
  · exact B1327871
  · exact B1327875
  · exact B1327879
  · exact B1327883
  · exact B1327887
  · exact B1327891
  · exact B1327895
  · exact B1327899
  · exact B1327903
  · exact B1327907
  · exact B1327911
  · exact B1327915
  · exact B1327919
  · exact B1327923
  · exact B1327927
  · exact B1327931
  · exact B1327935
  · exact B1327939
  · exact B1327943
  · exact B1327947
  · exact B1327951
  · exact B1327955
  · exact B1327959
  · exact B1327963
  · exact B1327967
  · exact B1327971
  · exact B1327975
  · exact B1327979
  · exact B1327983
  · exact B1327987
  · exact B1327991
  · exact B1327995
  · exact B1327999
  · exact B1328003
  · exact B1328007
  · exact B1328011
  · exact B1328015
  · exact B1328019
  · exact B1328023
  · exact B1328027
  · exact B1328031
  · exact B1328035
  · exact B1328039
  · exact B1328043
  · exact B1328047
  · exact B1328051
  · exact B1328055
  · exact B1328059
  · exact B1328063
  · exact B1328067
  · exact B1328071
  · exact B1328075
  · exact B1328079
  · exact B1328083
  · exact B1328087
  · exact B1328091
  · exact B1328095
  · exact B1328099
  · exact B1328103
  · exact B1328107
  · exact B1328111
  · exact B1328115
  · exact B1328119
  · exact B1328123
  · exact B1328127
  · exact B1328131
  · exact B1328135
  · exact B1328139
  · exact B1328143
  · exact B1328147
  · exact B1328151
  · exact B1328155
  · exact B1328159
  · exact B1328163
  · exact B1328167
  · exact B1328171
  · exact B1328175
  · exact B1328179
  · exact B1328183
  · exact B1328187
  · exact B1328191
  · exact B1328195
  · exact B1328199
  · exact B1328203
  · exact B1328207
  · exact B1328211
  · exact B1328215
  · exact B1328219
  · exact B1328223
  · exact B1328227
  · exact B1328231
  · exact B1328235
  · exact B1328239
  · exact B1328243
  · exact B1328247
  · exact B1328251
  · exact B1328255
  · exact B1328259
  · exact B1328263
  · exact B1328267
  · exact B1328271
  · exact B1328275
  · exact B1328279
  · exact B1328283
  · exact B1328287
  · exact B1328291
  · exact B1328295
  · exact B1328299
  · exact B1328303
  · exact B1328307
  · exact B1328311
  · exact B1328315
  · exact B1328319
  · exact B1328323
  · exact B1328327
  · exact B1328331
  · exact B1328335
  · exact B1328339
  · exact B1328343
  · exact B1328347
  · exact B1328351
  · exact B1328355
  · exact B1328359
  · exact B1328363
  · exact B1328367
  · exact B1328371
  · exact B1328375
  · exact B1328379
  · exact B1328383
  · exact B1328387
  · exact B1328391
  · exact B1328395
  · exact B1328399
  · exact B1328403
  · exact B1328407
  · exact B1328411
  · exact B1328415
  · exact B1328419
  · exact B1328423
  · exact B1328427
  · exact B1328431
  · exact B1328435
  · exact B1328439
  · exact B1328443
  · exact B1328447
  · exact B1328451
  · exact B1328455
  · exact B1328459
  · exact B1328463
  · exact B1328467
  · exact B1328471
  · exact B1328475
  · exact B1328479
  · exact B1328483
  · exact B1328487
  · exact B1328491
  · exact B1328495
  · exact B1328499
  · exact B1328503
  · exact B1328507
  · exact B1328511
  · exact B1328515
  · exact B1328519
  · exact B1328523
  · exact B1328527
  · exact B1328531
  · exact B1328535
  · exact B1328539
  · exact B1328543
  · exact B1328547
  · exact B1328551
  · exact B1328555
  · exact B1328559
  · exact B1328563
  · exact B1328567
  · exact B1328571
  · exact B1328575
  · exact B1328579
  · exact B1328583
  · exact B1328587
  · exact B1328591
  · exact B1328595
  · exact B1328599
  · exact B1328603
  · exact B1328607
  · exact B1328611
  · exact B1328615
  · exact B1328619
  · exact B1328623
  · exact B1328627
  · exact B1328631
  · exact B1328635
  · exact B1328639
  · exact B1328643
  · exact B1328647
  · exact B1328651
  · exact B1328655
  · exact B1328659
  · exact B1328663
  · exact B1328667
  · exact B1328671
  · exact B1328675
  · exact B1328679
  · exact B1328683
  · exact B1328687
  · exact B1328691
  · exact B1328695
  · exact B1328699
  · exact B1328703
  · exact B1328707
  · exact B1328711
  · exact B1328715
  · exact B1328719
  · exact B1328723
  · exact B1328727
  · exact B1328731
  · exact B1328735
  · exact B1328739
  · exact B1328743
  · exact B1328747
  · exact B1328751
  · exact B1328755
  · exact B1328759
  · exact B1328763
  · exact B1328767
  · exact B1328771
  · exact B1328775
  · exact B1328779
  · exact B1328783
  · exact B1328787
  · exact B1328791
  · exact B1328795
  · exact B1328799
  · exact B1328803
  · exact B1328807
  · exact B1328811
  · exact B1328815
  · exact B1328819
  · exact B1328823
  · exact B1328827
  · exact B1328831
  · exact B1328835
  · exact B1328839
  · exact B1328843
  · exact B1328847
  · exact B1328851
  · exact B1328855
  · exact B1328859
  · exact B1328863
  · exact B1328867
  · exact B1328871
  · exact B1328875
  · exact B1328879
  · exact B1328883
  · exact B1328887
  · exact B1328891
  · exact B1328895
  · exact B1328899
  · exact B1328903
  · exact B1328907
  · exact B1328911
  · exact B1328915
  · exact B1328919
  · exact B1328923
  · exact B1328927
  · exact B1328931
  · exact B1328935
  · exact B1328939
  · exact B1328943
  · exact B1328947
  · exact B1328951
  · exact B1328955
  · exact B1328959
  · exact B1328963
  · exact B1328967
  · exact B1328971
  · exact B1328975
  · exact B1328979

theorem solution (m : ℕ) (hlo : 1327482 ≤ m) (hhi : m ≤ 1328982) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 331870 ≤ j := by omega
    have hj2 : j ≤ 332244 := by omega
    have hb : Blo 1327482 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
