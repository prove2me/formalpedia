-- Prove2me | solution 1 for syracuse_descends_range_1453546_1455546
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:43:42.449094+00:00
-- url     : https://prove2.me/submissions/a537eb2a-02c6-42a7-8ded-39790fe0d56f

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


theorem B4907141 : Blo 1453546 4907141 := bbase (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) (by norm_num)
theorem B9953525 : Blo 1453546 9953525 := bbase (se 5 (by rfl) ⟨466571, by rfl⟩ : syracuseStep 9953525 = 933143) (by norm_num)
theorem B2212157 : Blo 1453546 2212157 := bbase (se 3 (by rfl) ⟨414779, by rfl⟩ : syracuseStep 2212157 = 829559) (by norm_num)
theorem B4424021 : Blo 1453546 4424021 := bbase (se 10 (by rfl) ⟨6480, by rfl⟩ : syracuseStep 4424021 = 12961) (by norm_num)
theorem B25174421 : Blo 1453546 25174421 := bbase (se 6 (by rfl) ⟨590025, by rfl⟩ : syracuseStep 25174421 = 1180051) (by norm_num)
theorem B27959701 : Blo 1453546 27959701 := bbase (se 6 (by rfl) ⟨655305, by rfl⟩ : syracuseStep 27959701 = 1310611) (by norm_num)
theorem B2761141 : Blo 1453546 2761141 := bbase (se 5 (by rfl) ⟨129428, by rfl⟩ : syracuseStep 2761141 = 258857) (by norm_num)
theorem B4907573 : Blo 1453546 4907573 := bbase (se 5 (by rfl) ⟨230042, by rfl⟩ : syracuseStep 4907573 = 460085) (by norm_num)
theorem B2761285 : Blo 1453546 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B5522053 : Blo 1453546 5522053 := bbase (se 4 (by rfl) ⟨517692, by rfl⟩ : syracuseStep 5522053 = 1035385) (by norm_num)
theorem B12599957 : Blo 1453546 12599957 := bbase (se 6 (by rfl) ⟨295311, by rfl⟩ : syracuseStep 12599957 = 590623) (by norm_num)
theorem B1475245 : Blo 1453546 1475245 := bbase (se 3 (by rfl) ⟨276608, by rfl⟩ : syracuseStep 1475245 = 553217) (by norm_num)
theorem B2761445 : Blo 1453546 2761445 := bbase (se 4 (by rfl) ⟨258885, by rfl⟩ : syracuseStep 2761445 = 517771) (by norm_num)
theorem B1966837 : Blo 1453546 1966837 := bbase (se 5 (by rfl) ⟨92195, by rfl⟩ : syracuseStep 1966837 = 184391) (by norm_num)
theorem B3105533 : Blo 1453546 3105533 := bbase (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) (by norm_num)
theorem B2761589 : Blo 1453546 2761589 := bbase (se 5 (by rfl) ⟨129449, by rfl⟩ : syracuseStep 2761589 = 258899) (by norm_num)
theorem B3318653 : Blo 1453546 3318653 := bbase (se 3 (by rfl) ⟨622247, by rfl⟩ : syracuseStep 3318653 = 1244495) (by norm_num)
theorem B2950013 : Blo 1453546 2950013 := bbase (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) (by norm_num)
theorem B3105677 : Blo 1453546 3105677 := bbase (se 3 (by rfl) ⟨582314, by rfl⟩ : syracuseStep 3105677 = 1164629) (by norm_num)
theorem B5522357 : Blo 1453546 5522357 := bbase (se 5 (by rfl) ⟨258860, by rfl⟩ : syracuseStep 5522357 = 517721) (by norm_num)
theorem B1967053 : Blo 1453546 1967053 := bbase (se 3 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 1967053 = 737645) (by norm_num)
theorem B6210533 : Blo 1453546 6210533 := bbase (se 4 (by rfl) ⟨582237, by rfl⟩ : syracuseStep 6210533 = 1164475) (by norm_num)
theorem B4908005 : Blo 1453546 4908005 := bbase (se 4 (by rfl) ⟨460125, by rfl⟩ : syracuseStep 4908005 = 920251) (by norm_num)
theorem B7365653 : Blo 1453546 7365653 := bbase (se 6 (by rfl) ⟨172632, by rfl⟩ : syracuseStep 7365653 = 345265) (by norm_num)
theorem B6636613 : Blo 1453546 6636613 := bbase (se 4 (by rfl) ⟨622182, by rfl⟩ : syracuseStep 6636613 = 1244365) (by norm_num)
theorem B11658325 : Blo 1453546 11658325 := bbase (se 8 (by rfl) ⟨68310, by rfl⟩ : syracuseStep 11658325 = 136621) (by norm_num)
theorem B2761877 : Blo 1453546 2761877 := bbase (se 6 (by rfl) ⟨64731, by rfl⟩ : syracuseStep 2761877 = 129463) (by norm_num)
theorem B3679445 : Blo 1453546 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2180333 : Blo 1453546 2180333 := bbase (se 3 (by rfl) ⟨408812, by rfl⟩ : syracuseStep 2180333 = 817625) (by norm_num)
theorem B2180357 : Blo 1453546 2180357 := bbase (se 4 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 2180357 = 408817) (by norm_num)
theorem B13985045 : Blo 1453546 13985045 := bbase (se 6 (by rfl) ⟨327774, by rfl⟩ : syracuseStep 13985045 = 655549) (by norm_num)
theorem B2180381 : Blo 1453546 2180381 := bbase (se 3 (by rfl) ⟨408821, by rfl⟩ : syracuseStep 2180381 = 817643) (by norm_num)
theorem B2762029 : Blo 1453546 2762029 := bbase (se 3 (by rfl) ⟨517880, by rfl⟩ : syracuseStep 2762029 = 1035761) (by norm_num)
theorem B2180405 : Blo 1453546 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B2180429 : Blo 1453546 2180429 := bbase (se 3 (by rfl) ⟨408830, by rfl⟩ : syracuseStep 2180429 = 817661) (by norm_num)
theorem B2180453 : Blo 1453546 2180453 := bbase (se 4 (by rfl) ⟨204417, by rfl⟩ : syracuseStep 2180453 = 408835) (by norm_num)
theorem B2180477 : Blo 1453546 2180477 := bbase (se 3 (by rfl) ⟨408839, by rfl⟩ : syracuseStep 2180477 = 817679) (by norm_num)
theorem B2180501 : Blo 1453546 2180501 := bbase (se 6 (by rfl) ⟨51105, by rfl⟩ : syracuseStep 2180501 = 102211) (by norm_num)
theorem B4908437 : Blo 1453546 4908437 := bbase (se 6 (by rfl) ⟨115041, by rfl⟩ : syracuseStep 4908437 = 230083) (by norm_num)
theorem B2180525 : Blo 1453546 2180525 := bbase (se 3 (by rfl) ⟨408848, by rfl⟩ : syracuseStep 2180525 = 817697) (by norm_num)
theorem B2180549 : Blo 1453546 2180549 := bbase (se 4 (by rfl) ⟨204426, by rfl⟩ : syracuseStep 2180549 = 408853) (by norm_num)
theorem B2180573 : Blo 1453546 2180573 := bbase (se 3 (by rfl) ⟨408857, by rfl⟩ : syracuseStep 2180573 = 817715) (by norm_num)
theorem B2180597 : Blo 1453546 2180597 := bbase (se 5 (by rfl) ⟨102215, by rfl⟩ : syracuseStep 2180597 = 204431) (by norm_num)
theorem B2180621 : Blo 1453546 2180621 := bbase (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) (by norm_num)
theorem B2180645 : Blo 1453546 2180645 := bbase (se 4 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 2180645 = 408871) (by norm_num)
theorem B4662821 : Blo 1453546 4662821 := bbase (se 4 (by rfl) ⟨437139, by rfl⟩ : syracuseStep 4662821 = 874279) (by norm_num)
theorem B3679789 : Blo 1453546 3679789 := bbase (se 3 (by rfl) ⟨689960, by rfl⟩ : syracuseStep 3679789 = 1379921) (by norm_num)
theorem B2180669 : Blo 1453546 2180669 := bbase (se 3 (by rfl) ⟨408875, by rfl⟩ : syracuseStep 2180669 = 817751) (by norm_num)
theorem B4974149 : Blo 1453546 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B2180693 : Blo 1453546 2180693 := bbase (se 8 (by rfl) ⟨12777, by rfl⟩ : syracuseStep 2180693 = 25555) (by norm_num)
theorem B2762333 : Blo 1453546 2762333 := bbase (se 3 (by rfl) ⟨517937, by rfl⟩ : syracuseStep 2762333 = 1035875) (by norm_num)
theorem B2950757 : Blo 1453546 2950757 := bbase (se 4 (by rfl) ⟨276633, by rfl⟩ : syracuseStep 2950757 = 553267) (by norm_num)
theorem B2180717 : Blo 1453546 2180717 := bbase (se 3 (by rfl) ⟨408884, by rfl⟩ : syracuseStep 2180717 = 817769) (by norm_num)
theorem B3106421 : Blo 1453546 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2180741 : Blo 1453546 2180741 := bbase (se 4 (by rfl) ⟨204444, by rfl⟩ : syracuseStep 2180741 = 408889) (by norm_num)
theorem B3679901 : Blo 1453546 3679901 := bbase (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) (by norm_num)
theorem B2180765 : Blo 1453546 2180765 := bbase (se 3 (by rfl) ⟨408893, by rfl⟩ : syracuseStep 2180765 = 817787) (by norm_num)
theorem B2180789 : Blo 1453546 2180789 := bbase (se 5 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 2180789 = 204449) (by norm_num)
theorem B2180813 : Blo 1453546 2180813 := bbase (se 3 (by rfl) ⟨408902, by rfl⟩ : syracuseStep 2180813 = 817805) (by norm_num)
theorem B2180837 : Blo 1453546 2180837 := bbase (se 4 (by rfl) ⟨204453, by rfl⟩ : syracuseStep 2180837 = 408907) (by norm_num)
theorem B5596901 : Blo 1453546 5596901 := bbase (se 4 (by rfl) ⟨524709, by rfl⟩ : syracuseStep 5596901 = 1049419) (by norm_num)
theorem B2180861 : Blo 1453546 2180861 := bbase (se 3 (by rfl) ⟨408911, by rfl⟩ : syracuseStep 2180861 = 817823) (by norm_num)
theorem B2180885 : Blo 1453546 2180885 := bbase (se 6 (by rfl) ⟨51114, by rfl⟩ : syracuseStep 2180885 = 102229) (by norm_num)
theorem B2180909 : Blo 1453546 2180909 := bbase (se 3 (by rfl) ⟨408920, by rfl⟩ : syracuseStep 2180909 = 817841) (by norm_num)
theorem B2180933 : Blo 1453546 2180933 := bbase (se 4 (by rfl) ⟨204462, by rfl⟩ : syracuseStep 2180933 = 408925) (by norm_num)
theorem B4908869 : Blo 1453546 4908869 := bbase (se 4 (by rfl) ⟨460206, by rfl⟩ : syracuseStep 4908869 = 920413) (by norm_num)
theorem B3680093 : Blo 1453546 3680093 := bbase (se 3 (by rfl) ⟨690017, by rfl⟩ : syracuseStep 3680093 = 1380035) (by norm_num)
theorem B2180957 : Blo 1453546 2180957 := bbase (se 3 (by rfl) ⟨408929, by rfl⟩ : syracuseStep 2180957 = 817859) (by norm_num)
theorem B3270509 : Blo 1453546 3270509 := bbase (se 3 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 3270509 = 1226441) (by norm_num)
theorem B2180981 : Blo 1453546 2180981 := bbase (se 5 (by rfl) ⟨102233, by rfl⟩ : syracuseStep 2180981 = 204467) (by norm_num)
theorem B2181005 : Blo 1453546 2181005 := bbase (se 3 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 2181005 = 817877) (by norm_num)
theorem B2181029 : Blo 1453546 2181029 := bbase (se 4 (by rfl) ⟨204471, by rfl⟩ : syracuseStep 2181029 = 408943) (by norm_num)
theorem B3270581 : Blo 1453546 3270581 := bbase (se 5 (by rfl) ⟨153308, by rfl⟩ : syracuseStep 3270581 = 306617) (by norm_num)
theorem B2181053 : Blo 1453546 2181053 := bbase (se 3 (by rfl) ⟨408947, by rfl⟩ : syracuseStep 2181053 = 817895) (by norm_num)
theorem B6211525 : Blo 1453546 6211525 := bbase (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) (by norm_num)
theorem B2181077 : Blo 1453546 2181077 := bbase (se 7 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 2181077 = 51119) (by norm_num)
theorem B1746905 : Blo 1453546 1746905 := bbase (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) (by norm_num)
theorem B2181101 : Blo 1453546 2181101 := bbase (se 3 (by rfl) ⟨408956, by rfl⟩ : syracuseStep 2181101 = 817913) (by norm_num)
theorem B6989813 : Blo 1453546 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B3270653 : Blo 1453546 3270653 := bbase (se 3 (by rfl) ⟨613247, by rfl⟩ : syracuseStep 3270653 = 1226495) (by norm_num)
theorem B2181125 : Blo 1453546 2181125 := bbase (se 4 (by rfl) ⟨204480, by rfl⟩ : syracuseStep 2181125 = 408961) (by norm_num)
theorem B2328605 : Blo 1453546 2328605 := bbase (se 3 (by rfl) ⟨436613, by rfl⟩ : syracuseStep 2328605 = 873227) (by norm_num)
theorem B2181149 : Blo 1453546 2181149 := bbase (se 3 (by rfl) ⟨408965, by rfl⟩ : syracuseStep 2181149 = 817931) (by norm_num)
theorem B2426917 : Blo 1453546 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B2181173 : Blo 1453546 2181173 := bbase (se 5 (by rfl) ⟨102242, by rfl⟩ : syracuseStep 2181173 = 204485) (by norm_num)
theorem B3270725 : Blo 1453546 3270725 := bbase (se 4 (by rfl) ⟨306630, by rfl⟩ : syracuseStep 3270725 = 613261) (by norm_num)
theorem B2181197 : Blo 1453546 2181197 := bbase (se 3 (by rfl) ⟨408974, by rfl⟩ : syracuseStep 2181197 = 817949) (by norm_num)
theorem B2181221 : Blo 1453546 2181221 := bbase (se 4 (by rfl) ⟨204489, by rfl⟩ : syracuseStep 2181221 = 408979) (by norm_num)
theorem B2181245 : Blo 1453546 2181245 := bbase (se 3 (by rfl) ⟨408983, by rfl⟩ : syracuseStep 2181245 = 817967) (by norm_num)
theorem B4974725 : Blo 1453546 4974725 := bbase (se 4 (by rfl) ⟨466380, by rfl⟩ : syracuseStep 4974725 = 932761) (by norm_num)
theorem B3270797 : Blo 1453546 3270797 := bbase (se 3 (by rfl) ⟨613274, by rfl⟩ : syracuseStep 3270797 = 1226549) (by norm_num)
theorem B2181269 : Blo 1453546 2181269 := bbase (se 6 (by rfl) ⟨51123, by rfl⟩ : syracuseStep 2181269 = 102247) (by norm_num)
theorem B2181293 : Blo 1453546 2181293 := bbase (se 3 (by rfl) ⟨408992, by rfl⟩ : syracuseStep 2181293 = 817985) (by norm_num)
theorem B1747117 : Blo 1453546 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B3680437 : Blo 1453546 3680437 := bbase (se 5 (by rfl) ⟨172520, by rfl⟩ : syracuseStep 3680437 = 345041) (by norm_num)
theorem B3147973 : Blo 1453546 3147973 := bbase (se 4 (by rfl) ⟨295122, by rfl⟩ : syracuseStep 3147973 = 590245) (by norm_num)
theorem B2181317 : Blo 1453546 2181317 := bbase (se 4 (by rfl) ⟨204498, by rfl⟩ : syracuseStep 2181317 = 408997) (by norm_num)
theorem B3270869 : Blo 1453546 3270869 := bbase (se 7 (by rfl) ⟨38330, by rfl⟩ : syracuseStep 3270869 = 76661) (by norm_num)
theorem B6637781 : Blo 1453546 6637781 := bbase (se 7 (by rfl) ⟨77786, by rfl⟩ : syracuseStep 6637781 = 155573) (by norm_num)
theorem B2328797 : Blo 1453546 2328797 := bbase (se 3 (by rfl) ⟨436649, by rfl⟩ : syracuseStep 2328797 = 873299) (by norm_num)
theorem B2181341 : Blo 1453546 2181341 := bbase (se 3 (by rfl) ⟨409001, by rfl⟩ : syracuseStep 2181341 = 818003) (by norm_num)
theorem B2181365 : Blo 1453546 2181365 := bbase (se 5 (by rfl) ⟨102251, by rfl⟩ : syracuseStep 2181365 = 204503) (by norm_num)
theorem B4909301 : Blo 1453546 4909301 := bbase (se 5 (by rfl) ⟨230123, by rfl⟩ : syracuseStep 4909301 = 460247) (by norm_num)
theorem B2181389 : Blo 1453546 2181389 := bbase (se 3 (by rfl) ⟨409010, by rfl⟩ : syracuseStep 2181389 = 818021) (by norm_num)
theorem B9324821 : Blo 1453546 9324821 := bbase (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) (by norm_num)
theorem B3270941 : Blo 1453546 3270941 := bbase (se 3 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 3270941 = 1226603) (by norm_num)
theorem B7080229 : Blo 1453546 7080229 := bbase (se 4 (by rfl) ⟨663771, by rfl⟩ : syracuseStep 7080229 = 1327543) (by norm_num)
theorem B3680549 : Blo 1453546 3680549 := bbase (se 4 (by rfl) ⟨345051, by rfl⟩ : syracuseStep 3680549 = 690103) (by norm_num)
theorem B2181413 : Blo 1453546 2181413 := bbase (se 4 (by rfl) ⟨204507, by rfl⟩ : syracuseStep 2181413 = 409015) (by norm_num)
theorem B7366949 : Blo 1453546 7366949 := bbase (se 4 (by rfl) ⟨690651, by rfl⟩ : syracuseStep 7366949 = 1381303) (by norm_num)
theorem B2181437 : Blo 1453546 2181437 := bbase (se 3 (by rfl) ⟨409019, by rfl⟩ : syracuseStep 2181437 = 818039) (by norm_num)
theorem B1747261 : Blo 1453546 1747261 := bbase (se 3 (by rfl) ⟨327611, by rfl⟩ : syracuseStep 1747261 = 655223) (by norm_num)
theorem B2763085 : Blo 1453546 2763085 := bbase (se 3 (by rfl) ⟨518078, by rfl⟩ : syracuseStep 2763085 = 1036157) (by norm_num)
theorem B2181461 : Blo 1453546 2181461 := bbase (se 10 (by rfl) ⟨3195, by rfl⟩ : syracuseStep 2181461 = 6391) (by norm_num)
theorem B2328925 : Blo 1453546 2328925 := bbase (se 3 (by rfl) ⟨436673, by rfl⟩ : syracuseStep 2328925 = 873347) (by norm_num)
theorem B3271013 : Blo 1453546 3271013 := bbase (se 4 (by rfl) ⟨306657, by rfl⟩ : syracuseStep 3271013 = 613315) (by norm_num)
theorem B3107173 : Blo 1453546 3107173 := bbase (se 4 (by rfl) ⟨291297, by rfl⟩ : syracuseStep 3107173 = 582595) (by norm_num)
theorem B2181485 : Blo 1453546 2181485 := bbase (se 3 (by rfl) ⟨409028, by rfl⟩ : syracuseStep 2181485 = 818057) (by norm_num)
theorem B2181509 : Blo 1453546 2181509 := bbase (se 4 (by rfl) ⟨204516, by rfl⟩ : syracuseStep 2181509 = 409033) (by norm_num)
theorem B2181533 : Blo 1453546 2181533 := bbase (se 3 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 2181533 = 818075) (by norm_num)
theorem B3271085 : Blo 1453546 3271085 := bbase (se 3 (by rfl) ⟨613328, by rfl⟩ : syracuseStep 3271085 = 1226657) (by norm_num)
theorem B2181557 : Blo 1453546 2181557 := bbase (se 5 (by rfl) ⟨102260, by rfl⟩ : syracuseStep 2181557 = 204521) (by norm_num)
theorem B2181581 : Blo 1453546 2181581 := bbase (se 3 (by rfl) ⟨409046, by rfl⟩ : syracuseStep 2181581 = 818093) (by norm_num)
theorem B2763229 : Blo 1453546 2763229 := bbase (se 3 (by rfl) ⟨518105, by rfl⟩ : syracuseStep 2763229 = 1036211) (by norm_num)
theorem B3680741 : Blo 1453546 3680741 := bbase (se 4 (by rfl) ⟨345069, by rfl⟩ : syracuseStep 3680741 = 690139) (by norm_num)
theorem B2181605 : Blo 1453546 2181605 := bbase (se 4 (by rfl) ⟨204525, by rfl⟩ : syracuseStep 2181605 = 409051) (by norm_num)
theorem B3271157 : Blo 1453546 3271157 := bbase (se 5 (by rfl) ⟨153335, by rfl⟩ : syracuseStep 3271157 = 306671) (by norm_num)
theorem B3107317 : Blo 1453546 3107317 := bbase (se 5 (by rfl) ⟨145655, by rfl⟩ : syracuseStep 3107317 = 291311) (by norm_num)
theorem B2181629 : Blo 1453546 2181629 := bbase (se 3 (by rfl) ⟨409055, by rfl⟩ : syracuseStep 2181629 = 818111) (by norm_num)
theorem B4139525 : Blo 1453546 4139525 := bbase (se 4 (by rfl) ⟨388080, by rfl⟩ : syracuseStep 4139525 = 776161) (by norm_num)
theorem B2181653 : Blo 1453546 2181653 := bbase (se 6 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 2181653 = 102265) (by norm_num)
theorem B2181677 : Blo 1453546 2181677 := bbase (se 3 (by rfl) ⟨409064, by rfl⟩ : syracuseStep 2181677 = 818129) (by norm_num)
theorem B2656813 : Blo 1453546 2656813 := bbase (se 3 (by rfl) ⟨498152, by rfl⟩ : syracuseStep 2656813 = 996305) (by norm_num)
theorem B3271229 : Blo 1453546 3271229 := bbase (se 3 (by rfl) ⟨613355, by rfl⟩ : syracuseStep 3271229 = 1226711) (by norm_num)
theorem B2181701 : Blo 1453546 2181701 := bbase (se 4 (by rfl) ⟨204534, by rfl⟩ : syracuseStep 2181701 = 409069) (by norm_num)
theorem B7088725 : Blo 1453546 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B2181725 : Blo 1453546 2181725 := bbase (se 3 (by rfl) ⟨409073, by rfl⟩ : syracuseStep 2181725 = 818147) (by norm_num)
theorem B2181749 : Blo 1453546 2181749 := bbase (se 5 (by rfl) ⟨102269, by rfl⟩ : syracuseStep 2181749 = 204539) (by norm_num)
theorem B3271301 : Blo 1453546 3271301 := bbase (se 4 (by rfl) ⟨306684, by rfl⟩ : syracuseStep 3271301 = 613369) (by norm_num)
theorem B2181773 : Blo 1453546 2181773 := bbase (se 3 (by rfl) ⟨409082, by rfl⟩ : syracuseStep 2181773 = 818165) (by norm_num)
theorem B2181797 : Blo 1453546 2181797 := bbase (se 4 (by rfl) ⟨204543, by rfl⟩ : syracuseStep 2181797 = 409087) (by norm_num)
theorem B4909733 : Blo 1453546 4909733 := bbase (se 4 (by rfl) ⟨460287, by rfl⟩ : syracuseStep 4909733 = 920575) (by norm_num)
theorem B2181821 : Blo 1453546 2181821 := bbase (se 3 (by rfl) ⟨409091, by rfl⟩ : syracuseStep 2181821 = 818183) (by norm_num)
theorem B7359173 : Blo 1453546 7359173 := bbase (se 4 (by rfl) ⟨689922, by rfl⟩ : syracuseStep 7359173 = 1379845) (by norm_num)
theorem B3271373 : Blo 1453546 3271373 := bbase (se 3 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 3271373 = 1226765) (by norm_num)
theorem B2181845 : Blo 1453546 2181845 := bbase (se 7 (by rfl) ⟨25568, by rfl⟩ : syracuseStep 2181845 = 51137) (by norm_num)
theorem B2181869 : Blo 1453546 2181869 := bbase (se 3 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 2181869 = 818201) (by norm_num)
theorem B2181893 : Blo 1453546 2181893 := bbase (se 4 (by rfl) ⟨204552, by rfl⟩ : syracuseStep 2181893 = 409105) (by norm_num)
theorem B3271445 : Blo 1453546 3271445 := bbase (se 6 (by rfl) ⟨76674, by rfl⟩ : syracuseStep 3271445 = 153349) (by norm_num)
theorem B8284949 : Blo 1453546 8284949 := bbase (se 6 (by rfl) ⟨194178, by rfl⟩ : syracuseStep 8284949 = 388357) (by norm_num)
theorem B2181917 : Blo 1453546 2181917 := bbase (se 3 (by rfl) ⟨409109, by rfl⟩ : syracuseStep 2181917 = 818219) (by norm_num)
theorem B7858997 : Blo 1453546 7858997 := bbase (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) (by norm_num)
theorem B2181941 : Blo 1453546 2181941 := bbase (se 5 (by rfl) ⟨102278, by rfl⟩ : syracuseStep 2181941 = 204557) (by norm_num)
theorem B3681085 : Blo 1453546 3681085 := bbase (se 3 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 3681085 = 1380407) (by norm_num)
theorem B2181965 : Blo 1453546 2181965 := bbase (se 3 (by rfl) ⟨409118, by rfl⟩ : syracuseStep 2181965 = 818237) (by norm_num)
theorem B3271517 : Blo 1453546 3271517 := bbase (se 3 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 3271517 = 1226819) (by norm_num)
theorem B2181989 : Blo 1453546 2181989 := bbase (se 4 (by rfl) ⟨204561, by rfl⟩ : syracuseStep 2181989 = 409123) (by norm_num)
theorem B3107693 : Blo 1453546 3107693 := bbase (se 3 (by rfl) ⟨582692, by rfl⟩ : syracuseStep 3107693 = 1165385) (by norm_num)
theorem B2182013 : Blo 1453546 2182013 := bbase (se 3 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 2182013 = 818255) (by norm_num)
theorem B17935253 : Blo 1453546 17935253 := bbase (se 6 (by rfl) ⟨420357, by rfl⟩ : syracuseStep 17935253 = 840715) (by norm_num)
theorem B2182037 : Blo 1453546 2182037 := bbase (se 6 (by rfl) ⟨51141, by rfl⟩ : syracuseStep 2182037 = 102283) (by norm_num)
theorem B3492773 : Blo 1453546 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B3271589 : Blo 1453546 3271589 := bbase (se 4 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 3271589 = 613423) (by norm_num)
theorem B3681197 : Blo 1453546 3681197 := bbase (se 3 (by rfl) ⟨690224, by rfl⟩ : syracuseStep 3681197 = 1380449) (by norm_num)
theorem B2182061 : Blo 1453546 2182061 := bbase (se 3 (by rfl) ⟨409136, by rfl⟩ : syracuseStep 2182061 = 818273) (by norm_num)
theorem B2182085 : Blo 1453546 2182085 := bbase (se 4 (by rfl) ⟨204570, by rfl⟩ : syracuseStep 2182085 = 409141) (by norm_num)
theorem B1657813 : Blo 1453546 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B16567253 : Blo 1453546 16567253 := bbase (se 7 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 16567253 = 388295) (by norm_num)
theorem B2329565 : Blo 1453546 2329565 := bbase (se 3 (by rfl) ⟨436793, by rfl⟩ : syracuseStep 2329565 = 873587) (by norm_num)
theorem B2182109 : Blo 1453546 2182109 := bbase (se 3 (by rfl) ⟨409145, by rfl⟩ : syracuseStep 2182109 = 818291) (by norm_num)
theorem B3271661 : Blo 1453546 3271661 := bbase (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) (by norm_num)
theorem B5598197 : Blo 1453546 5598197 := bbase (se 5 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 5598197 = 524831) (by norm_num)
theorem B2182133 : Blo 1453546 2182133 := bbase (se 5 (by rfl) ⟨102287, by rfl⟩ : syracuseStep 2182133 = 204575) (by norm_num)
theorem B5524469 : Blo 1453546 5524469 := bbase (se 5 (by rfl) ⟨258959, by rfl⟩ : syracuseStep 5524469 = 517919) (by norm_num)
theorem B2182157 : Blo 1453546 2182157 := bbase (se 3 (by rfl) ⟨409154, by rfl⟩ : syracuseStep 2182157 = 818309) (by norm_num)
theorem B2182181 : Blo 1453546 2182181 := bbase (se 4 (by rfl) ⟨204579, by rfl⟩ : syracuseStep 2182181 = 409159) (by norm_num)
theorem B3271733 : Blo 1453546 3271733 := bbase (se 5 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 3271733 = 306725) (by norm_num)
theorem B2182205 : Blo 1453546 2182205 := bbase (se 3 (by rfl) ⟨409163, by rfl⟩ : syracuseStep 2182205 = 818327) (by norm_num)
theorem B2182229 : Blo 1453546 2182229 := bbase (se 8 (by rfl) ⟨12786, by rfl⟩ : syracuseStep 2182229 = 25573) (by norm_num)
theorem B4910165 : Blo 1453546 4910165 := bbase (se 8 (by rfl) ⟨28770, by rfl⟩ : syracuseStep 4910165 = 57541) (by norm_num)
theorem B3681389 : Blo 1453546 3681389 := bbase (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) (by norm_num)
theorem B2182253 : Blo 1453546 2182253 := bbase (se 3 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 2182253 = 818345) (by norm_num)
theorem B3271805 : Blo 1453546 3271805 := bbase (se 3 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 3271805 = 1226927) (by norm_num)
theorem B2182277 : Blo 1453546 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B2182301 : Blo 1453546 2182301 := bbase (se 3 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 2182301 = 818363) (by norm_num)
theorem B4140197 : Blo 1453546 4140197 := bbase (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) (by norm_num)
theorem B2182325 : Blo 1453546 2182325 := bbase (se 5 (by rfl) ⟨102296, by rfl⟩ : syracuseStep 2182325 = 204593) (by norm_num)
theorem B3493061 : Blo 1453546 3493061 := bbase (se 4 (by rfl) ⟨327474, by rfl⟩ : syracuseStep 3493061 = 654949) (by norm_num)
theorem B3271877 : Blo 1453546 3271877 := bbase (se 4 (by rfl) ⟨306738, by rfl⟩ : syracuseStep 3271877 = 613477) (by norm_num)
theorem B2100421 : Blo 1453546 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B2182349 : Blo 1453546 2182349 := bbase (se 3 (by rfl) ⟨409190, by rfl⟩ : syracuseStep 2182349 = 818381) (by norm_num)
theorem B3108061 : Blo 1453546 3108061 := bbase (se 3 (by rfl) ⟨582761, by rfl⟩ : syracuseStep 3108061 = 1165523) (by norm_num)
theorem B2182373 : Blo 1453546 2182373 := bbase (se 4 (by rfl) ⟨204597, by rfl⟩ : syracuseStep 2182373 = 409195) (by norm_num)
theorem B2182397 : Blo 1453546 2182397 := bbase (se 3 (by rfl) ⟨409199, by rfl⟩ : syracuseStep 2182397 = 818399) (by norm_num)
theorem B3271949 : Blo 1453546 3271949 := bbase (se 3 (by rfl) ⟨613490, by rfl⟩ : syracuseStep 3271949 = 1226981) (by norm_num)
theorem B2182421 : Blo 1453546 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B5524757 : Blo 1453546 5524757 := bbase (se 6 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 5524757 = 258973) (by norm_num)
theorem B3149093 : Blo 1453546 3149093 := bbase (se 4 (by rfl) ⟨295227, by rfl⟩ : syracuseStep 3149093 = 590455) (by norm_num)
theorem B2182445 : Blo 1453546 2182445 := bbase (se 3 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 2182445 = 818417) (by norm_num)
theorem B2182469 : Blo 1453546 2182469 := bbase (se 4 (by rfl) ⟨204606, by rfl⟩ : syracuseStep 2182469 = 409213) (by norm_num)
theorem B3272021 : Blo 1453546 3272021 := bbase (se 11 (by rfl) ⟨2396, by rfl⟩ : syracuseStep 3272021 = 4793) (by norm_num)
theorem B2182493 : Blo 1453546 2182493 := bbase (se 3 (by rfl) ⟨409217, by rfl⟩ : syracuseStep 2182493 = 818435) (by norm_num)
theorem B2182517 : Blo 1453546 2182517 := bbase (se 5 (by rfl) ⟨102305, by rfl⟩ : syracuseStep 2182517 = 204611) (by norm_num)
theorem B2182541 : Blo 1453546 2182541 := bbase (se 3 (by rfl) ⟨409226, by rfl⟩ : syracuseStep 2182541 = 818453) (by norm_num)
theorem B11046293 : Blo 1453546 11046293 := bbase (se 6 (by rfl) ⟨258897, by rfl⟩ : syracuseStep 11046293 = 517795) (by norm_num)
theorem B3272093 : Blo 1453546 3272093 := bbase (se 3 (by rfl) ⟨613517, by rfl⟩ : syracuseStep 3272093 = 1227035) (by norm_num)
theorem B2330021 : Blo 1453546 2330021 := bbase (se 4 (by rfl) ⟨218439, by rfl⟩ : syracuseStep 2330021 = 436879) (by norm_num)
theorem B2182565 : Blo 1453546 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B2452909 : Blo 1453546 2452909 := bbase (se 3 (by rfl) ⟨459920, by rfl⟩ : syracuseStep 2452909 = 919841) (by norm_num)
theorem B2182589 : Blo 1453546 2182589 := bbase (se 3 (by rfl) ⟨409235, by rfl⟩ : syracuseStep 2182589 = 818471) (by norm_num)
theorem B3681733 : Blo 1453546 3681733 := bbase (se 4 (by rfl) ⟨345162, by rfl⟩ : syracuseStep 3681733 = 690325) (by norm_num)
theorem B2182613 : Blo 1453546 2182613 := bbase (se 7 (by rfl) ⟨25577, by rfl⟩ : syracuseStep 2182613 = 51155) (by norm_num)
theorem B3272165 : Blo 1453546 3272165 := bbase (se 4 (by rfl) ⟨306765, by rfl⟩ : syracuseStep 3272165 = 613531) (by norm_num)
theorem B2182637 : Blo 1453546 2182637 := bbase (se 3 (by rfl) ⟨409244, by rfl⟩ : syracuseStep 2182637 = 818489) (by norm_num)
theorem B2452997 : Blo 1453546 2452997 := bbase (se 4 (by rfl) ⟨229968, by rfl⟩ : syracuseStep 2452997 = 459937) (by norm_num)
theorem B4910597 : Blo 1453546 4910597 := bbase (se 4 (by rfl) ⟨460368, by rfl⟩ : syracuseStep 4910597 = 920737) (by norm_num)
theorem B2182661 : Blo 1453546 2182661 := bbase (se 4 (by rfl) ⟨204624, by rfl⟩ : syracuseStep 2182661 = 409249) (by norm_num)
theorem B2182685 : Blo 1453546 2182685 := bbase (se 3 (by rfl) ⟨409253, by rfl⟩ : syracuseStep 2182685 = 818507) (by norm_num)
theorem B3272237 : Blo 1453546 3272237 := bbase (se 3 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 3272237 = 1227089) (by norm_num)
theorem B3681845 : Blo 1453546 3681845 := bbase (se 5 (by rfl) ⟨172586, by rfl⟩ : syracuseStep 3681845 = 345173) (by norm_num)
theorem B2182709 : Blo 1453546 2182709 := bbase (se 5 (by rfl) ⟨102314, by rfl⟩ : syracuseStep 2182709 = 204629) (by norm_num)
theorem B7368245 : Blo 1453546 7368245 := bbase (se 5 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 7368245 = 690773) (by norm_num)
theorem B2182733 : Blo 1453546 2182733 := bbase (se 3 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 2182733 = 818525) (by norm_num)
theorem B4140629 : Blo 1453546 4140629 := bbase (se 8 (by rfl) ⟨24261, by rfl⟩ : syracuseStep 4140629 = 48523) (by norm_num)
theorem B2182757 : Blo 1453546 2182757 := bbase (se 4 (by rfl) ⟨204633, by rfl⟩ : syracuseStep 2182757 = 409267) (by norm_num)
theorem B3272309 : Blo 1453546 3272309 := bbase (se 5 (by rfl) ⟨153389, by rfl⟩ : syracuseStep 3272309 = 306779) (by norm_num)
theorem B2182781 : Blo 1453546 2182781 := bbase (se 3 (by rfl) ⟨409271, by rfl⟩ : syracuseStep 2182781 = 818543) (by norm_num)
theorem B4656773 : Blo 1453546 4656773 := bbase (se 4 (by rfl) ⟨436572, by rfl⟩ : syracuseStep 4656773 = 873145) (by norm_num)
theorem B2453125 : Blo 1453546 2453125 := bbase (se 4 (by rfl) ⟨229980, by rfl⟩ : syracuseStep 2453125 = 459961) (by norm_num)
theorem B2330245 : Blo 1453546 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B2182805 : Blo 1453546 2182805 := bbase (se 6 (by rfl) ⟨51159, by rfl⟩ : syracuseStep 2182805 = 102319) (by norm_num)
theorem B2182829 : Blo 1453546 2182829 := bbase (se 3 (by rfl) ⟨409280, by rfl⟩ : syracuseStep 2182829 = 818561) (by norm_num)
theorem B3272381 : Blo 1453546 3272381 := bbase (se 3 (by rfl) ⟨613571, by rfl⟩ : syracuseStep 3272381 = 1227143) (by norm_num)
theorem B2330309 : Blo 1453546 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B2182853 : Blo 1453546 2182853 := bbase (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) (by norm_num)
theorem B2453213 : Blo 1453546 2453213 := bbase (se 3 (by rfl) ⟨459977, by rfl⟩ : syracuseStep 2453213 = 919955) (by norm_num)
theorem B2182877 : Blo 1453546 2182877 := bbase (se 3 (by rfl) ⟨409289, by rfl⟩ : syracuseStep 2182877 = 818579) (by norm_num)
theorem B3682037 : Blo 1453546 3682037 := bbase (se 5 (by rfl) ⟨172595, by rfl⟩ : syracuseStep 3682037 = 345191) (by norm_num)
theorem B2182901 : Blo 1453546 2182901 := bbase (se 5 (by rfl) ⟨102323, by rfl⟩ : syracuseStep 2182901 = 204647) (by norm_num)
theorem B3272453 : Blo 1453546 3272453 := bbase (se 4 (by rfl) ⟨306792, by rfl⟩ : syracuseStep 3272453 = 613585) (by norm_num)
theorem B2182925 : Blo 1453546 2182925 := bbase (se 3 (by rfl) ⟨409298, by rfl⟩ : syracuseStep 2182925 = 818597) (by norm_num)
theorem B1494817 : Blo 1453546 1494817 := bbase (se 2 (by rfl) ⟨560556, by rfl⟩ : syracuseStep 1494817 = 1121113) (by norm_num)
theorem B2182949 : Blo 1453546 2182949 := bbase (se 4 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 2182949 = 409303) (by norm_num)
theorem B11038517 : Blo 1453546 11038517 := bbase (se 5 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 11038517 = 1034861) (by norm_num)
theorem B2182973 : Blo 1453546 2182973 := bbase (se 3 (by rfl) ⟨409307, by rfl⟩ : syracuseStep 2182973 = 818615) (by norm_num)
theorem B2330437 : Blo 1453546 2330437 := bbase (se 4 (by rfl) ⟨218478, by rfl⟩ : syracuseStep 2330437 = 436957) (by norm_num)
theorem B3272525 : Blo 1453546 3272525 := bbase (se 3 (by rfl) ⟨613598, by rfl⟩ : syracuseStep 3272525 = 1227197) (by norm_num)
theorem B2182997 : Blo 1453546 2182997 := bbase (se 9 (by rfl) ⟨6395, by rfl⟩ : syracuseStep 2182997 = 12791) (by norm_num)
theorem B2453341 : Blo 1453546 2453341 := bbase (se 3 (by rfl) ⟨460001, by rfl⟩ : syracuseStep 2453341 = 920003) (by norm_num)
theorem B2183021 : Blo 1453546 2183021 := bbase (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) (by norm_num)
theorem B2183045 : Blo 1453546 2183045 := bbase (se 4 (by rfl) ⟨204660, by rfl⟩ : syracuseStep 2183045 = 409321) (by norm_num)
theorem B3272597 : Blo 1453546 3272597 := bbase (se 6 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 3272597 = 153403) (by norm_num)
theorem B2183069 : Blo 1453546 2183069 := bbase (se 3 (by rfl) ⟨409325, by rfl⟩ : syracuseStep 2183069 = 818651) (by norm_num)
theorem B2453429 : Blo 1453546 2453429 := bbase (se 5 (by rfl) ⟨115004, by rfl⟩ : syracuseStep 2453429 = 230009) (by norm_num)
theorem B4911029 : Blo 1453546 4911029 := bbase (se 5 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 4911029 = 460409) (by norm_num)
theorem B2183093 : Blo 1453546 2183093 := bbase (se 5 (by rfl) ⟨102332, by rfl⟩ : syracuseStep 2183093 = 204665) (by norm_num)
theorem B2183117 : Blo 1453546 2183117 := bbase (se 3 (by rfl) ⟨409334, by rfl⟩ : syracuseStep 2183117 = 818669) (by norm_num)
theorem B7360469 : Blo 1453546 7360469 := bbase (se 7 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 7360469 = 172511) (by norm_num)
theorem B47173589 : Blo 1453546 47173589 := bbase (se 7 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 47173589 = 1105631) (by norm_num)
theorem B3272669 : Blo 1453546 3272669 := bbase (se 3 (by rfl) ⟨613625, by rfl⟩ : syracuseStep 3272669 = 1227251) (by norm_num)
theorem B2183141 : Blo 1453546 2183141 := bbase (se 4 (by rfl) ⟨204669, by rfl⟩ : syracuseStep 2183141 = 409339) (by norm_num)
theorem B11800565 : Blo 1453546 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B2183165 : Blo 1453546 2183165 := bbase (se 3 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 2183165 = 818687) (by norm_num)
theorem B2183189 : Blo 1453546 2183189 := bbase (se 6 (by rfl) ⟨51168, by rfl⟩ : syracuseStep 2183189 = 102337) (by norm_num)
theorem B3272741 : Blo 1453546 3272741 := bbase (se 4 (by rfl) ⟨306819, by rfl⟩ : syracuseStep 3272741 = 613639) (by norm_num)
theorem B2183213 : Blo 1453546 2183213 := bbase (se 3 (by rfl) ⟨409352, by rfl⟩ : syracuseStep 2183213 = 818705) (by norm_num)
theorem B2453557 : Blo 1453546 2453557 := bbase (se 5 (by rfl) ⟨115010, by rfl⟩ : syracuseStep 2453557 = 230021) (by norm_num)
theorem B2183237 : Blo 1453546 2183237 := bbase (se 4 (by rfl) ⟨204678, by rfl⟩ : syracuseStep 2183237 = 409357) (by norm_num)
theorem B3682381 : Blo 1453546 3682381 := bbase (se 3 (by rfl) ⟨690446, by rfl⟩ : syracuseStep 3682381 = 1380893) (by norm_num)
theorem B12423253 : Blo 1453546 12423253 := bbase (se 8 (by rfl) ⟨72792, by rfl⟩ : syracuseStep 12423253 = 145585) (by norm_num)
theorem B2183261 : Blo 1453546 2183261 := bbase (se 3 (by rfl) ⟨409361, by rfl⟩ : syracuseStep 2183261 = 818723) (by norm_num)
theorem B1552493 : Blo 1453546 1552493 := bbase (se 3 (by rfl) ⟨291092, by rfl⟩ : syracuseStep 1552493 = 582185) (by norm_num)
theorem B3272813 : Blo 1453546 3272813 := bbase (se 3 (by rfl) ⟨613652, by rfl⟩ : syracuseStep 3272813 = 1227305) (by norm_num)
theorem B2183285 : Blo 1453546 2183285 := bbase (se 5 (by rfl) ⟨102341, by rfl⟩ : syracuseStep 2183285 = 204683) (by norm_num)
theorem B4657285 : Blo 1453546 4657285 := bbase (se 4 (by rfl) ⟨436620, by rfl⟩ : syracuseStep 4657285 = 873241) (by norm_num)
theorem B2453645 : Blo 1453546 2453645 := bbase (se 3 (by rfl) ⟨460058, by rfl⟩ : syracuseStep 2453645 = 920117) (by norm_num)
theorem B2183309 : Blo 1453546 2183309 := bbase (se 3 (by rfl) ⟨409370, by rfl⟩ : syracuseStep 2183309 = 818741) (by norm_num)
theorem B1552565 : Blo 1453546 1552565 := bbase (se 5 (by rfl) ⟨72776, by rfl⟩ : syracuseStep 1552565 = 145553) (by norm_num)
theorem B3272885 : Blo 1453546 3272885 := bbase (se 5 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 3272885 = 306833) (by norm_num)
theorem B3682493 : Blo 1453546 3682493 := bbase (se 3 (by rfl) ⟨690467, by rfl⟩ : syracuseStep 3682493 = 1380935) (by norm_num)
theorem B8392949 : Blo 1453546 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B4976885 : Blo 1453546 4976885 := bbase (se 5 (by rfl) ⟨233291, by rfl⟩ : syracuseStep 4976885 = 466583) (by norm_num)
theorem B3272957 : Blo 1453546 3272957 := bbase (se 3 (by rfl) ⟨613679, by rfl⟩ : syracuseStep 3272957 = 1227359) (by norm_num)
theorem B2453773 : Blo 1453546 2453773 := bbase (se 3 (by rfl) ⟨460082, by rfl⟩ : syracuseStep 2453773 = 920165) (by norm_num)
theorem B4141381 : Blo 1453546 4141381 := bbase (se 4 (by rfl) ⟨388254, by rfl⟩ : syracuseStep 4141381 = 776509) (by norm_num)
theorem B3273029 : Blo 1453546 3273029 := bbase (se 4 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 3273029 = 613693) (by norm_num)
theorem B2453861 : Blo 1453546 2453861 := bbase (se 4 (by rfl) ⟨230049, by rfl⟩ : syracuseStep 2453861 = 460099) (by norm_num)
theorem B4911461 : Blo 1453546 4911461 := bbase (se 4 (by rfl) ⟨460449, by rfl⟩ : syracuseStep 4911461 = 920899) (by norm_num)
theorem B1552753 : Blo 1453546 1552753 := bbase (se 2 (by rfl) ⟨582282, by rfl⟩ : syracuseStep 1552753 = 1164565) (by norm_num)
theorem B3682685 : Blo 1453546 3682685 := bbase (se 3 (by rfl) ⟨690503, by rfl⟩ : syracuseStep 3682685 = 1381007) (by norm_num)
theorem B3273101 : Blo 1453546 3273101 := bbase (se 3 (by rfl) ⟨613706, by rfl⟩ : syracuseStep 3273101 = 1227413) (by norm_num)
theorem B5525941 : Blo 1453546 5525941 := bbase (se 5 (by rfl) ⟨259028, by rfl⟩ : syracuseStep 5525941 = 518057) (by norm_num)
theorem B3273173 : Blo 1453546 3273173 := bbase (se 7 (by rfl) ⟨38357, by rfl⟩ : syracuseStep 3273173 = 76715) (by norm_num)
theorem B27652565 : Blo 1453546 27652565 := bbase (se 7 (by rfl) ⟨324053, by rfl⟩ : syracuseStep 27652565 = 648107) (by norm_num)
theorem B2453989 : Blo 1453546 2453989 := bbase (se 4 (by rfl) ⟨230061, by rfl⟩ : syracuseStep 2453989 = 460123) (by norm_num)
theorem B2486773 : Blo 1453546 2486773 := bbase (se 5 (by rfl) ⟨116567, by rfl⟩ : syracuseStep 2486773 = 233135) (by norm_num)
theorem B3273245 : Blo 1453546 3273245 := bbase (se 3 (by rfl) ⟨613733, by rfl⟩ : syracuseStep 3273245 = 1227467) (by norm_num)
theorem B1552937 : Blo 1453546 1552937 := bbase (se 2 (by rfl) ⟨582351, by rfl⟩ : syracuseStep 1552937 = 1164703) (by norm_num)
theorem B2454077 : Blo 1453546 2454077 := bbase (se 3 (by rfl) ⟨460139, by rfl⟩ : syracuseStep 2454077 = 920279) (by norm_num)
theorem B3273317 : Blo 1453546 3273317 := bbase (se 4 (by rfl) ⟨306873, by rfl⟩ : syracuseStep 3273317 = 613747) (by norm_num)
theorem B3592837 : Blo 1453546 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B1839773 : Blo 1453546 1839773 := bbase (se 3 (by rfl) ⟨344957, by rfl⟩ : syracuseStep 1839773 = 689915) (by norm_num)
theorem B3273389 : Blo 1453546 3273389 := bbase (se 3 (by rfl) ⟨613760, by rfl⟩ : syracuseStep 3273389 = 1227521) (by norm_num)
theorem B2454205 : Blo 1453546 2454205 := bbase (se 3 (by rfl) ⟨460163, by rfl⟩ : syracuseStep 2454205 = 920327) (by norm_num)
theorem B1839829 : Blo 1453546 1839829 := bbase (se 7 (by rfl) ⟨21560, by rfl⟩ : syracuseStep 1839829 = 43121) (by norm_num)
theorem B3683029 : Blo 1453546 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B5526245 : Blo 1453546 5526245 := bbase (se 4 (by rfl) ⟨518085, by rfl⟩ : syracuseStep 5526245 = 1036171) (by norm_num)
theorem B3273461 : Blo 1453546 3273461 := bbase (se 5 (by rfl) ⟨153443, by rfl⟩ : syracuseStep 3273461 = 306887) (by norm_num)
theorem B2454293 : Blo 1453546 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B4911893 : Blo 1453546 4911893 := bbase (se 6 (by rfl) ⟨115122, by rfl⟩ : syracuseStep 4911893 = 230245) (by norm_num)
theorem B1839925 : Blo 1453546 1839925 := bbase (se 5 (by rfl) ⟨86246, by rfl⟩ : syracuseStep 1839925 = 172493) (by norm_num)
theorem B3273533 : Blo 1453546 3273533 := bbase (se 3 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 3273533 = 1227575) (by norm_num)
theorem B3683141 : Blo 1453546 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B5895013 : Blo 1453546 5895013 := bbase (se 4 (by rfl) ⟨552657, by rfl⟩ : syracuseStep 5895013 = 1105315) (by norm_num)
theorem B3273605 : Blo 1453546 3273605 := bbase (se 4 (by rfl) ⟨306900, by rfl⟩ : syracuseStep 3273605 = 613801) (by norm_num)
theorem B4977541 : Blo 1453546 4977541 := bbase (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) (by norm_num)
theorem B2454421 : Blo 1453546 2454421 := bbase (se 6 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 2454421 = 115051) (by norm_num)
theorem B1635241 : Blo 1453546 1635241 := bbase (se 2 (by rfl) ⟨613215, by rfl⟩ : syracuseStep 1635241 = 1226431) (by norm_num)
theorem B1635277 : Blo 1453546 1635277 := bbase (se 3 (by rfl) ⟨306614, by rfl⟩ : syracuseStep 1635277 = 613229) (by norm_num)
theorem B3273677 : Blo 1453546 3273677 := bbase (se 3 (by rfl) ⟨613814, by rfl⟩ : syracuseStep 3273677 = 1227629) (by norm_num)
theorem B50361301 : Blo 1453546 50361301 := bbase (se 7 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 50361301 = 1180343) (by norm_num)
theorem B1840097 : Blo 1453546 1840097 := bbase (se 2 (by rfl) ⟨690036, by rfl⟩ : syracuseStep 1840097 = 1380073) (by norm_num)
theorem B2454509 : Blo 1453546 2454509 := bbase (se 3 (by rfl) ⟨460220, by rfl⟩ : syracuseStep 2454509 = 920441) (by norm_num)
theorem B1635313 : Blo 1453546 1635313 := bbase (se 2 (by rfl) ⟨613242, by rfl⟩ : syracuseStep 1635313 = 1226485) (by norm_num)
theorem B3683333 : Blo 1453546 3683333 := bbase (se 4 (by rfl) ⟨345312, by rfl⟩ : syracuseStep 3683333 = 690625) (by norm_num)
theorem B1635349 : Blo 1453546 1635349 := bbase (se 6 (by rfl) ⟨38328, by rfl⟩ : syracuseStep 1635349 = 76657) (by norm_num)
theorem B3273749 : Blo 1453546 3273749 := bbase (se 6 (by rfl) ⟨76728, by rfl⟩ : syracuseStep 3273749 = 153457) (by norm_num)
theorem B1840153 : Blo 1453546 1840153 := bbase (se 2 (by rfl) ⟨690057, by rfl⟩ : syracuseStep 1840153 = 1380115) (by norm_num)
theorem B1635385 : Blo 1453546 1635385 := bbase (se 2 (by rfl) ⟨613269, by rfl⟩ : syracuseStep 1635385 = 1226539) (by norm_num)
theorem B1635421 : Blo 1453546 1635421 := bbase (se 3 (by rfl) ⟨306641, by rfl⟩ : syracuseStep 1635421 = 613283) (by norm_num)
theorem B3273821 : Blo 1453546 3273821 := bbase (se 3 (by rfl) ⟨613841, by rfl⟩ : syracuseStep 3273821 = 1227683) (by norm_num)
theorem B2454637 : Blo 1453546 2454637 := bbase (se 3 (by rfl) ⟨460244, by rfl⟩ : syracuseStep 2454637 = 920489) (by norm_num)
theorem B1840249 : Blo 1453546 1840249 := bbase (se 2 (by rfl) ⟨690093, by rfl⟩ : syracuseStep 1840249 = 1380187) (by norm_num)
theorem B1635457 : Blo 1453546 1635457 := bbase (se 2 (by rfl) ⟨613296, by rfl⟩ : syracuseStep 1635457 = 1226593) (by norm_num)
theorem B1635493 : Blo 1453546 1635493 := bbase (se 4 (by rfl) ⟨153327, by rfl⟩ : syracuseStep 1635493 = 306655) (by norm_num)
theorem B3273893 : Blo 1453546 3273893 := bbase (se 4 (by rfl) ⟨306927, by rfl⟩ : syracuseStep 3273893 = 613855) (by norm_num)
theorem B2454725 : Blo 1453546 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B4912325 : Blo 1453546 4912325 := bbase (se 4 (by rfl) ⟨460530, by rfl⟩ : syracuseStep 4912325 = 921061) (by norm_num)
theorem B1635529 : Blo 1453546 1635529 := bbase (se 2 (by rfl) ⟨613323, by rfl⟩ : syracuseStep 1635529 = 1226647) (by norm_num)
theorem B7361765 : Blo 1453546 7361765 := bbase (se 4 (by rfl) ⟨690165, by rfl⟩ : syracuseStep 7361765 = 1380331) (by norm_num)
theorem B1635565 : Blo 1453546 1635565 := bbase (se 3 (by rfl) ⟨306668, by rfl⟩ : syracuseStep 1635565 = 613337) (by norm_num)
theorem B3273965 : Blo 1453546 3273965 := bbase (se 3 (by rfl) ⟨613868, by rfl⟩ : syracuseStep 3273965 = 1227737) (by norm_num)
theorem B1635601 : Blo 1453546 1635601 := bbase (se 2 (by rfl) ⟨613350, by rfl⟩ : syracuseStep 1635601 = 1226701) (by norm_num)
theorem B1553689 : Blo 1453546 1553689 := bbase (se 2 (by rfl) ⟨582633, by rfl⟩ : syracuseStep 1553689 = 1165267) (by norm_num)
theorem B1840421 : Blo 1453546 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B1635637 : Blo 1453546 1635637 := bbase (se 5 (by rfl) ⟨76670, by rfl⟩ : syracuseStep 1635637 = 153341) (by norm_num)
theorem B3274037 : Blo 1453546 3274037 := bbase (se 5 (by rfl) ⟨153470, by rfl⟩ : syracuseStep 3274037 = 306941) (by norm_num)
theorem B2454853 : Blo 1453546 2454853 := bbase (se 4 (by rfl) ⟨230142, by rfl⟩ : syracuseStep 2454853 = 460285) (by norm_num)
theorem B1635673 : Blo 1453546 1635673 := bbase (se 2 (by rfl) ⟨613377, by rfl⟩ : syracuseStep 1635673 = 1226755) (by norm_num)
theorem B1840477 : Blo 1453546 1840477 := bbase (se 3 (by rfl) ⟨345089, by rfl⟩ : syracuseStep 1840477 = 690179) (by norm_num)
theorem B3683677 : Blo 1453546 3683677 := bbase (se 3 (by rfl) ⟨690689, by rfl⟩ : syracuseStep 3683677 = 1381379) (by norm_num)
theorem B1553761 : Blo 1453546 1553761 := bbase (se 2 (by rfl) ⟨582660, by rfl⟩ : syracuseStep 1553761 = 1165321) (by norm_num)
theorem B1635709 : Blo 1453546 1635709 := bbase (se 3 (by rfl) ⟨306695, by rfl⟩ : syracuseStep 1635709 = 613391) (by norm_num)
theorem B3274109 : Blo 1453546 3274109 := bbase (se 3 (by rfl) ⟨613895, by rfl⟩ : syracuseStep 3274109 = 1227791) (by norm_num)
theorem B2454941 : Blo 1453546 2454941 := bbase (se 3 (by rfl) ⟨460301, by rfl⟩ : syracuseStep 2454941 = 920603) (by norm_num)
theorem B1635745 : Blo 1453546 1635745 := bbase (se 2 (by rfl) ⟨613404, by rfl⟩ : syracuseStep 1635745 = 1226809) (by norm_num)
theorem B1840573 : Blo 1453546 1840573 := bbase (se 3 (by rfl) ⟨345107, by rfl⟩ : syracuseStep 1840573 = 690215) (by norm_num)
theorem B1635781 : Blo 1453546 1635781 := bbase (se 4 (by rfl) ⟨153354, by rfl⟩ : syracuseStep 1635781 = 306709) (by norm_num)
theorem B3274181 : Blo 1453546 3274181 := bbase (se 4 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 3274181 = 613909) (by norm_num)
theorem B3683789 : Blo 1453546 3683789 := bbase (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) (by norm_num)
theorem B1635817 : Blo 1453546 1635817 := bbase (se 2 (by rfl) ⟨613431, by rfl⟩ : syracuseStep 1635817 = 1226863) (by norm_num)
theorem B1635853 : Blo 1453546 1635853 := bbase (se 3 (by rfl) ⟨306722, by rfl⟩ : syracuseStep 1635853 = 613445) (by norm_num)
theorem B3274253 : Blo 1453546 3274253 := bbase (se 3 (by rfl) ⟨613922, by rfl⟩ : syracuseStep 3274253 = 1227845) (by norm_num)
theorem B6985237 : Blo 1453546 6985237 := bbase (se 6 (by rfl) ⟨163716, by rfl⟩ : syracuseStep 6985237 = 327433) (by norm_num)
theorem B1553941 : Blo 1453546 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B2455069 : Blo 1453546 2455069 := bbase (se 3 (by rfl) ⟨460325, by rfl⟩ : syracuseStep 2455069 = 920651) (by norm_num)
theorem B1635889 : Blo 1453546 1635889 := bbase (se 2 (by rfl) ⟨613458, by rfl⟩ : syracuseStep 1635889 = 1226917) (by norm_num)
theorem B1635925 : Blo 1453546 1635925 := bbase (se 8 (by rfl) ⟨9585, by rfl⟩ : syracuseStep 1635925 = 19171) (by norm_num)
theorem B3274325 : Blo 1453546 3274325 := bbase (se 8 (by rfl) ⟨19185, by rfl⟩ : syracuseStep 3274325 = 38371) (by norm_num)
theorem B1840745 : Blo 1453546 1840745 := bbase (se 2 (by rfl) ⟨690279, by rfl⟩ : syracuseStep 1840745 = 1380559) (by norm_num)
theorem B2455157 : Blo 1453546 2455157 := bbase (se 5 (by rfl) ⟨115085, by rfl⟩ : syracuseStep 2455157 = 230171) (by norm_num)
theorem B1635961 : Blo 1453546 1635961 := bbase (se 2 (by rfl) ⟨613485, by rfl⟩ : syracuseStep 1635961 = 1226971) (by norm_num)
theorem B1595009 : Blo 1453546 1595009 := bbase (se 2 (by rfl) ⟨598128, by rfl⟩ : syracuseStep 1595009 = 1196257) (by norm_num)
theorem B3683981 : Blo 1453546 3683981 := bbase (se 3 (by rfl) ⟨690746, by rfl⟩ : syracuseStep 3683981 = 1381493) (by norm_num)
theorem B1635997 : Blo 1453546 1635997 := bbase (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) (by norm_num)
theorem B3274397 : Blo 1453546 3274397 := bbase (se 3 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 3274397 = 1227899) (by norm_num)
theorem B1840801 : Blo 1453546 1840801 := bbase (se 2 (by rfl) ⟨690300, by rfl⟩ : syracuseStep 1840801 = 1380601) (by norm_num)
theorem B1636033 : Blo 1453546 1636033 := bbase (se 2 (by rfl) ⟨613512, by rfl⟩ : syracuseStep 1636033 = 1227025) (by norm_num)
theorem B1636069 : Blo 1453546 1636069 := bbase (se 4 (by rfl) ⟨153381, by rfl⟩ : syracuseStep 1636069 = 306763) (by norm_num)
theorem B3274469 : Blo 1453546 3274469 := bbase (se 4 (by rfl) ⟨306981, by rfl⟩ : syracuseStep 3274469 = 613963) (by norm_num)
theorem B2455285 : Blo 1453546 2455285 := bbase (se 5 (by rfl) ⟨115091, by rfl⟩ : syracuseStep 2455285 = 230183) (by norm_num)
theorem B1840897 : Blo 1453546 1840897 := bbase (se 2 (by rfl) ⟨690336, by rfl⟩ : syracuseStep 1840897 = 1380673) (by norm_num)
theorem B1636105 : Blo 1453546 1636105 := bbase (se 2 (by rfl) ⟨613539, by rfl⟩ : syracuseStep 1636105 = 1227079) (by norm_num)
theorem B25196309 : Blo 1453546 25196309 := bbase (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) (by norm_num)
theorem B1636141 : Blo 1453546 1636141 := bbase (se 3 (by rfl) ⟨306776, by rfl⟩ : syracuseStep 1636141 = 613553) (by norm_num)
theorem B3274541 : Blo 1453546 3274541 := bbase (se 3 (by rfl) ⟨613976, by rfl⟩ : syracuseStep 3274541 = 1227953) (by norm_num)
theorem B2455373 : Blo 1453546 2455373 := bbase (se 3 (by rfl) ⟨460382, by rfl⟩ : syracuseStep 2455373 = 920765) (by norm_num)
theorem B1636177 : Blo 1453546 1636177 := bbase (se 2 (by rfl) ⟨613566, by rfl⟩ : syracuseStep 1636177 = 1227133) (by norm_num)
theorem B4659029 : Blo 1453546 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B1636213 : Blo 1453546 1636213 := bbase (se 5 (by rfl) ⟨76697, by rfl⟩ : syracuseStep 1636213 = 153395) (by norm_num)
theorem B3274613 : Blo 1453546 3274613 := bbase (se 5 (by rfl) ⟨153497, by rfl⟩ : syracuseStep 3274613 = 306995) (by norm_num)
theorem B1636249 : Blo 1453546 1636249 := bbase (se 2 (by rfl) ⟨613593, by rfl⟩ : syracuseStep 1636249 = 1227187) (by norm_num)
theorem B1841069 : Blo 1453546 1841069 := bbase (se 3 (by rfl) ⟨345200, by rfl⟩ : syracuseStep 1841069 = 690401) (by norm_num)
theorem B7862197 : Blo 1453546 7862197 := bbase (se 5 (by rfl) ⟨368540, by rfl⟩ : syracuseStep 7862197 = 737081) (by norm_num)
theorem B1636285 : Blo 1453546 1636285 := bbase (se 3 (by rfl) ⟨306803, by rfl⟩ : syracuseStep 1636285 = 613607) (by norm_num)
theorem B3274685 : Blo 1453546 3274685 := bbase (se 3 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 3274685 = 1228007) (by norm_num)
theorem B2455501 : Blo 1453546 2455501 := bbase (se 3 (by rfl) ⟨460406, by rfl⟩ : syracuseStep 2455501 = 920813) (by norm_num)
theorem B1636321 : Blo 1453546 1636321 := bbase (se 2 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 1636321 = 1227241) (by norm_num)
theorem B1841125 : Blo 1453546 1841125 := bbase (se 4 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 1841125 = 345211) (by norm_num)
theorem B3684325 : Blo 1453546 3684325 := bbase (se 4 (by rfl) ⟨345405, by rfl⟩ : syracuseStep 3684325 = 690811) (by norm_num)
theorem B1636357 : Blo 1453546 1636357 := bbase (se 4 (by rfl) ⟨153408, by rfl⟩ : syracuseStep 1636357 = 306817) (by norm_num)
theorem B3274757 : Blo 1453546 3274757 := bbase (se 4 (by rfl) ⟨307008, by rfl⟩ : syracuseStep 3274757 = 614017) (by norm_num)
theorem B2488333 : Blo 1453546 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B4659221 : Blo 1453546 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B12425237 : Blo 1453546 12425237 := bbase (se 6 (by rfl) ⟨291216, by rfl⟩ : syracuseStep 12425237 = 582433) (by norm_num)
theorem B2455589 : Blo 1453546 2455589 := bbase (se 4 (by rfl) ⟨230211, by rfl⟩ : syracuseStep 2455589 = 460423) (by norm_num)
theorem B1636393 : Blo 1453546 1636393 := bbase (se 2 (by rfl) ⟨613647, by rfl⟩ : syracuseStep 1636393 = 1227295) (by norm_num)
theorem B2947117 : Blo 1453546 2947117 := bbase (se 3 (by rfl) ⟨552584, by rfl⟩ : syracuseStep 2947117 = 1105169) (by norm_num)
theorem B2799677 : Blo 1453546 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B1841221 : Blo 1453546 1841221 := bbase (se 4 (by rfl) ⟨172614, by rfl⟩ : syracuseStep 1841221 = 345229) (by norm_num)
theorem B1636429 : Blo 1453546 1636429 := bbase (se 3 (by rfl) ⟨306830, by rfl⟩ : syracuseStep 1636429 = 613661) (by norm_num)
theorem B3274829 : Blo 1453546 3274829 := bbase (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) (by norm_num)
theorem B5240933 : Blo 1453546 5240933 := bbase (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) (by norm_num)
theorem B1636465 : Blo 1453546 1636465 := bbase (se 2 (by rfl) ⟨613674, by rfl⟩ : syracuseStep 1636465 = 1227349) (by norm_num)
theorem B1636501 : Blo 1453546 1636501 := bbase (se 6 (by rfl) ⟨38355, by rfl⟩ : syracuseStep 1636501 = 76711) (by norm_num)
theorem B3274901 : Blo 1453546 3274901 := bbase (se 6 (by rfl) ⟨76755, by rfl⟩ : syracuseStep 3274901 = 153511) (by norm_num)
theorem B3930277 : Blo 1453546 3930277 := bbase (se 4 (by rfl) ⟨368463, by rfl⟩ : syracuseStep 3930277 = 736927) (by norm_num)
theorem B2455717 : Blo 1453546 2455717 := bbase (se 4 (by rfl) ⟨230223, by rfl⟩ : syracuseStep 2455717 = 460447) (by norm_num)
theorem B3496117 : Blo 1453546 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B1636537 : Blo 1453546 1636537 := bbase (se 2 (by rfl) ⟨613701, by rfl⟩ : syracuseStep 1636537 = 1227403) (by norm_num)
theorem B6994117 : Blo 1453546 6994117 := bbase (se 4 (by rfl) ⟨655698, by rfl⟩ : syracuseStep 6994117 = 1311397) (by norm_num)
theorem B1636573 : Blo 1453546 1636573 := bbase (se 3 (by rfl) ⟨306857, by rfl⟩ : syracuseStep 1636573 = 613715) (by norm_num)
theorem B3274973 : Blo 1453546 3274973 := bbase (se 3 (by rfl) ⟨614057, by rfl⟩ : syracuseStep 3274973 = 1228115) (by norm_num)
theorem B1841393 : Blo 1453546 1841393 := bbase (se 2 (by rfl) ⟨690522, by rfl⟩ : syracuseStep 1841393 = 1381045) (by norm_num)
theorem B2455805 : Blo 1453546 2455805 := bbase (se 3 (by rfl) ⟨460463, by rfl⟩ : syracuseStep 2455805 = 920927) (by norm_num)
theorem B1636609 : Blo 1453546 1636609 := bbase (se 2 (by rfl) ⟨613728, by rfl⟩ : syracuseStep 1636609 = 1227457) (by norm_num)
theorem B1636645 : Blo 1453546 1636645 := bbase (se 4 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 1636645 = 306871) (by norm_num)
theorem B1841449 : Blo 1453546 1841449 := bbase (se 2 (by rfl) ⟨690543, by rfl⟩ : syracuseStep 1841449 = 1381087) (by norm_num)
theorem B3733813 : Blo 1453546 3733813 := bbase (se 5 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 3733813 = 350045) (by norm_num)
theorem B1636681 : Blo 1453546 1636681 := bbase (se 2 (by rfl) ⟨613755, by rfl⟩ : syracuseStep 1636681 = 1227511) (by norm_num)
theorem B1636717 : Blo 1453546 1636717 := bbase (se 3 (by rfl) ⟨306884, by rfl⟩ : syracuseStep 1636717 = 613769) (by norm_num)
theorem B2455933 : Blo 1453546 2455933 := bbase (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) (by norm_num)
theorem B1841545 : Blo 1453546 1841545 := bbase (se 2 (by rfl) ⟨690579, by rfl⟩ : syracuseStep 1841545 = 1381159) (by norm_num)
theorem B1636753 : Blo 1453546 1636753 := bbase (se 2 (by rfl) ⟨613782, by rfl⟩ : syracuseStep 1636753 = 1227565) (by norm_num)
theorem B1636789 : Blo 1453546 1636789 := bbase (se 5 (by rfl) ⟨76724, by rfl⟩ : syracuseStep 1636789 = 153449) (by norm_num)
theorem B3930581 : Blo 1453546 3930581 := bbase (se 7 (by rfl) ⟨46061, by rfl⟩ : syracuseStep 3930581 = 92123) (by norm_num)
theorem B2456021 : Blo 1453546 2456021 := bbase (se 7 (by rfl) ⟨28781, by rfl⟩ : syracuseStep 2456021 = 57563) (by norm_num)
theorem B1636825 : Blo 1453546 1636825 := bbase (se 2 (by rfl) ⟨613809, by rfl⟩ : syracuseStep 1636825 = 1227619) (by norm_num)
theorem B2071021 : Blo 1453546 2071021 := bbase (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) (by norm_num)
theorem B7363061 : Blo 1453546 7363061 := bbase (se 5 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 7363061 = 690287) (by norm_num)
theorem B1636861 : Blo 1453546 1636861 := bbase (se 3 (by rfl) ⟨306911, by rfl⟩ : syracuseStep 1636861 = 613823) (by norm_num)
theorem B1636897 : Blo 1453546 1636897 := bbase (se 2 (by rfl) ⟨613836, by rfl⟩ : syracuseStep 1636897 = 1227673) (by norm_num)
theorem B1841717 : Blo 1453546 1841717 := bbase (se 5 (by rfl) ⟨86330, by rfl⟩ : syracuseStep 1841717 = 172661) (by norm_num)
theorem B1636933 : Blo 1453546 1636933 := bbase (se 4 (by rfl) ⟨153462, by rfl⟩ : syracuseStep 1636933 = 306925) (by norm_num)
theorem B2947661 : Blo 1453546 2947661 := bbase (se 3 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 2947661 = 1105373) (by norm_num)
theorem B2456149 : Blo 1453546 2456149 := bbase (se 8 (by rfl) ⟨14391, by rfl⟩ : syracuseStep 2456149 = 28783) (by norm_num)
theorem B1636969 : Blo 1453546 1636969 := bbase (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) (by norm_num)
theorem B1841773 : Blo 1453546 1841773 := bbase (se 3 (by rfl) ⟨345332, by rfl⟩ : syracuseStep 1841773 = 690665) (by norm_num)
theorem B11188853 : Blo 1453546 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B1637005 : Blo 1453546 1637005 := bbase (se 3 (by rfl) ⟨306938, by rfl⟩ : syracuseStep 1637005 = 613877) (by norm_num)
theorem B1637041 : Blo 1453546 1637041 := bbase (se 2 (by rfl) ⟨613890, by rfl⟩ : syracuseStep 1637041 = 1227781) (by norm_num)
theorem B1841869 : Blo 1453546 1841869 := bbase (se 3 (by rfl) ⟨345350, by rfl⟩ : syracuseStep 1841869 = 690701) (by norm_num)
theorem B1637077 : Blo 1453546 1637077 := bbase (se 7 (by rfl) ⟨19184, by rfl⟩ : syracuseStep 1637077 = 38369) (by norm_num)
theorem B1637113 : Blo 1453546 1637113 := bbase (se 2 (by rfl) ⟨613917, by rfl⟩ : syracuseStep 1637113 = 1227835) (by norm_num)
theorem B1637149 : Blo 1453546 1637149 := bbase (se 3 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 1637149 = 613931) (by norm_num)
theorem B3496733 : Blo 1453546 3496733 := bbase (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) (by norm_num)
theorem B1637185 : Blo 1453546 1637185 := bbase (se 2 (by rfl) ⟨613944, by rfl⟩ : syracuseStep 1637185 = 1227889) (by norm_num)
theorem B2759501 : Blo 1453546 2759501 := bbase (se 3 (by rfl) ⟨517406, by rfl⟩ : syracuseStep 2759501 = 1034813) (by norm_num)
theorem B6216533 : Blo 1453546 6216533 := bbase (se 9 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 6216533 = 36425) (by norm_num)
theorem B3316573 : Blo 1453546 3316573 := bbase (se 3 (by rfl) ⟨621857, by rfl⟩ : syracuseStep 3316573 = 1243715) (by norm_num)
theorem B1637221 : Blo 1453546 1637221 := bbase (se 4 (by rfl) ⟨153489, by rfl⟩ : syracuseStep 1637221 = 306979) (by norm_num)
theorem B4905845 : Blo 1453546 4905845 := bbase (se 5 (by rfl) ⟨229961, by rfl⟩ : syracuseStep 4905845 = 459923) (by norm_num)
theorem B1964917 : Blo 1453546 1964917 := bbase (se 5 (by rfl) ⟨92105, by rfl⟩ : syracuseStep 1964917 = 184211) (by norm_num)
theorem B1842041 : Blo 1453546 1842041 := bbase (se 2 (by rfl) ⟨690765, by rfl⟩ : syracuseStep 1842041 = 1381531) (by norm_num)
theorem B1637257 : Blo 1453546 1637257 := bbase (se 2 (by rfl) ⟨613971, by rfl⟩ : syracuseStep 1637257 = 1227943) (by norm_num)
theorem B1637293 : Blo 1453546 1637293 := bbase (se 3 (by rfl) ⟨306992, by rfl⟩ : syracuseStep 1637293 = 613985) (by norm_num)
theorem B1842097 : Blo 1453546 1842097 := bbase (se 2 (by rfl) ⟨690786, by rfl⟩ : syracuseStep 1842097 = 1381573) (by norm_num)
theorem B1637329 : Blo 1453546 1637329 := bbase (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) (by norm_num)
theorem B2759645 : Blo 1453546 2759645 := bbase (se 3 (by rfl) ⟨517433, by rfl⟩ : syracuseStep 2759645 = 1034867) (by norm_num)
theorem B3496925 : Blo 1453546 3496925 := bbase (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) (by norm_num)
theorem B1637365 : Blo 1453546 1637365 := bbase (se 5 (by rfl) ⟨76751, by rfl⟩ : syracuseStep 1637365 = 153503) (by norm_num)
theorem B1637401 : Blo 1453546 1637401 := bbase (se 2 (by rfl) ⟨614025, by rfl⟩ : syracuseStep 1637401 = 1228051) (by norm_num)
theorem B2071613 : Blo 1453546 2071613 := bbase (se 3 (by rfl) ⟨388427, by rfl⟩ : syracuseStep 2071613 = 776855) (by norm_num)
theorem B1637437 : Blo 1453546 1637437 := bbase (se 3 (by rfl) ⟨307019, by rfl⟩ : syracuseStep 1637437 = 614039) (by norm_num)
theorem B39795797 : Blo 1453546 39795797 := bbase (se 8 (by rfl) ⟨233178, by rfl⟩ : syracuseStep 39795797 = 466357) (by norm_num)
theorem B1637473 : Blo 1453546 1637473 := bbase (se 2 (by rfl) ⟨614052, by rfl⟩ : syracuseStep 1637473 = 1228105) (by norm_num)
theorem B4144229 : Blo 1453546 4144229 := bbase (se 4 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 4144229 = 777043) (by norm_num)
theorem B6216821 : Blo 1453546 6216821 := bbase (se 5 (by rfl) ⟨291413, by rfl⟩ : syracuseStep 6216821 = 582827) (by norm_num)
theorem B2071693 : Blo 1453546 2071693 := bbase (se 3 (by rfl) ⟨388442, by rfl⟩ : syracuseStep 2071693 = 776885) (by norm_num)
theorem B5520581 : Blo 1453546 5520581 := bbase (se 4 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 5520581 = 1035109) (by norm_num)
theorem B2759933 : Blo 1453546 2759933 := bbase (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) (by norm_num)
theorem B2071813 : Blo 1453546 2071813 := bbase (se 4 (by rfl) ⟨194232, by rfl⟩ : syracuseStep 2071813 = 388465) (by norm_num)
theorem B4906277 : Blo 1453546 4906277 := bbase (se 4 (by rfl) ⟨459963, by rfl⟩ : syracuseStep 4906277 = 919927) (by norm_num)
theorem B2694485 : Blo 1453546 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B2071909 : Blo 1453546 2071909 := bbase (se 4 (by rfl) ⟨194241, by rfl⟩ : syracuseStep 2071909 = 388483) (by norm_num)
theorem B2760085 : Blo 1453546 2760085 := bbase (se 6 (by rfl) ⟨64689, by rfl⟩ : syracuseStep 2760085 = 129379) (by norm_num)
theorem B1965485 : Blo 1453546 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B5520869 : Blo 1453546 5520869 := bbase (se 4 (by rfl) ⟨517581, by rfl⟩ : syracuseStep 5520869 = 1035163) (by norm_num)
theorem B2211365 : Blo 1453546 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B1965637 : Blo 1453546 1965637 := bbase (se 4 (by rfl) ⟨184278, by rfl⟩ : syracuseStep 1965637 = 368557) (by norm_num)
theorem B2760389 : Blo 1453546 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B4906709 : Blo 1453546 4906709 := bbase (se 7 (by rfl) ⟨57500, by rfl⟩ : syracuseStep 4906709 = 115001) (by norm_num)
theorem B2621165 : Blo 1453546 2621165 := bbase (se 3 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 2621165 = 982937) (by norm_num)
theorem B7364357 : Blo 1453546 7364357 := bbase (se 4 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 7364357 = 1380817) (by norm_num)
theorem B10485557 : Blo 1453546 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B1474373 : Blo 1453546 1474373 := bbase (se 4 (by rfl) ⟨138222, by rfl⟩ : syracuseStep 1474373 = 276445) (by norm_num)
theorem B2072405 : Blo 1453546 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B2523005 : Blo 1453546 2523005 := bbase (se 3 (by rfl) ⟨473063, by rfl⟩ : syracuseStep 2523005 = 946127) (by norm_num)
theorem B3104669 : Blo 1453546 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B1966069 : Blo 1453546 1966069 := bbase (se 5 (by rfl) ⟨92159, by rfl⟩ : syracuseStep 1966069 = 184319) (by norm_num)
theorem B3317777 : Blo 1453546 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B3235889 : Blo 1453546 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B16564337 : Blo 1453546 16564337 := bstep (se 2 (by rfl) ⟨6211626, by rfl⟩ : syracuseStep 16564337 = 12423253) B12423253
theorem B5595299 : Blo 1453546 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B6635683 : Blo 1453546 6635683 := bstep (se 1 (by rfl) ⟨4976762, by rfl⟩ : syracuseStep 6635683 = 9953525) B9953525
theorem B3317923 : Blo 1453546 3317923 := bstep (se 1 (by rfl) ⟨2488442, by rfl⟩ : syracuseStep 3317923 = 4976885) B4976885
theorem B6209713 : Blo 1453546 6209713 := bstep (se 2 (by rfl) ⟨2328642, by rfl⟩ : syracuseStep 6209713 = 4657285) B4657285
theorem B1474771 : Blo 1453546 1474771 := bstep (se 1 (by rfl) ⟨1106078, by rfl⟩ : syracuseStep 1474771 = 2212157) B2212157
theorem B2949347 : Blo 1453546 2949347 := bstep (se 1 (by rfl) ⟨2212010, by rfl⟩ : syracuseStep 2949347 = 4424021) B4424021
theorem B4907249 : Blo 1453546 4907249 := bstep (se 2 (by rfl) ⟨1840218, by rfl⟩ : syracuseStep 4907249 = 3680437) B3680437
theorem B4661489 : Blo 1453546 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B7365005 : Blo 1453546 7365005 := bstep (se 3 (by rfl) ⟨1380938, by rfl⟩ : syracuseStep 7365005 = 2761877) B2761877
theorem B5521841 : Blo 1453546 5521841 := bstep (se 2 (by rfl) ⟨2070690, by rfl⟩ : syracuseStep 5521841 = 4141381) B4141381
theorem B37806533 : Blo 1453546 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B3105233 : Blo 1453546 3105233 := bstep (se 2 (by rfl) ⟨1164462, by rfl⟩ : syracuseStep 3105233 = 2328925) B2328925
theorem B2212435 : Blo 1453546 2212435 := bstep (se 1 (by rfl) ⟨1659326, by rfl⟩ : syracuseStep 2212435 = 3318653) B3318653
theorem B1966675 : Blo 1453546 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B2761361 : Blo 1453546 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B4907789 : Blo 1453546 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B4907843 : Blo 1453546 4907843 := bstep (se 1 (by rfl) ⟨3680882, by rfl⟩ : syracuseStep 4907843 = 7361765) B7361765
theorem B9323363 : Blo 1453546 9323363 := bstep (se 1 (by rfl) ⟨6992522, by rfl⟩ : syracuseStep 9323363 = 13985045) B13985045
theorem B1966993 : Blo 1453546 1966993 := bstep (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) B1475245
theorem B2622449 : Blo 1453546 2622449 := bstep (se 2 (by rfl) ⟨983418, by rfl⟩ : syracuseStep 2622449 = 1966837) B1966837
theorem B1967171 : Blo 1453546 1967171 := bstep (se 1 (by rfl) ⟨1475378, by rfl⟩ : syracuseStep 1967171 = 2950757) B2950757
theorem B4908113 : Blo 1453546 4908113 := bstep (se 2 (by rfl) ⟨1840542, by rfl⟩ : syracuseStep 4908113 = 3681085) B3681085
theorem B2180321 : Blo 1453546 2180321 := bstep (se 2 (by rfl) ⟨817620, by rfl⟩ : syracuseStep 2180321 = 1635241) B1635241
theorem B3106019 : Blo 1453546 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B2180339 : Blo 1453546 2180339 := bstep (se 1 (by rfl) ⟨1635254, by rfl⟩ : syracuseStep 2180339 = 3270509) B3270509
theorem B2180369 : Blo 1453546 2180369 := bstep (se 2 (by rfl) ⟨817638, by rfl⟩ : syracuseStep 2180369 = 1635277) B1635277
theorem B2622737 : Blo 1453546 2622737 := bstep (se 2 (by rfl) ⟨983526, by rfl⟩ : syracuseStep 2622737 = 1967053) B1967053
theorem B2180387 : Blo 1453546 2180387 := bstep (se 1 (by rfl) ⟨1635290, by rfl⟩ : syracuseStep 2180387 = 3270581) B3270581
theorem B2180417 : Blo 1453546 2180417 := bstep (se 2 (by rfl) ⟨817656, by rfl⟩ : syracuseStep 2180417 = 1635313) B1635313
theorem B2180435 : Blo 1453546 2180435 := bstep (se 1 (by rfl) ⟨1635326, by rfl⟩ : syracuseStep 2180435 = 3270653) B3270653
theorem B8283491 : Blo 1453546 8283491 := bstep (se 1 (by rfl) ⟨6212618, by rfl⟩ : syracuseStep 8283491 = 12425237) B12425237
theorem B2180465 : Blo 1453546 2180465 := bstep (se 2 (by rfl) ⟨817674, by rfl⟩ : syracuseStep 2180465 = 1635349) B1635349
theorem B2180483 : Blo 1453546 2180483 := bstep (se 1 (by rfl) ⟨1635362, by rfl⟩ : syracuseStep 2180483 = 3270725) B3270725
theorem B2180513 : Blo 1453546 2180513 := bstep (se 2 (by rfl) ⟨817692, by rfl⟩ : syracuseStep 2180513 = 1635385) B1635385
theorem B8848817 : Blo 1453546 8848817 := bstep (se 2 (by rfl) ⟨3318306, by rfl⟩ : syracuseStep 8848817 = 6636613) B6636613
theorem B2180531 : Blo 1453546 2180531 := bstep (se 1 (by rfl) ⟨1635398, by rfl⟩ : syracuseStep 2180531 = 3270797) B3270797
theorem B2180561 : Blo 1453546 2180561 := bstep (se 2 (by rfl) ⟨817710, by rfl⟩ : syracuseStep 2180561 = 1635421) B1635421
theorem B2180579 : Blo 1453546 2180579 := bstep (se 1 (by rfl) ⟨1635434, by rfl⟩ : syracuseStep 2180579 = 3270869) B3270869
theorem B4425187 : Blo 1453546 4425187 := bstep (se 1 (by rfl) ⟨3318890, by rfl⟩ : syracuseStep 4425187 = 6637781) B6637781
theorem B2180609 : Blo 1453546 2180609 := bstep (se 2 (by rfl) ⟨817728, by rfl⟩ : syracuseStep 2180609 = 1635457) B1635457
theorem B7972357 : Blo 1453546 7972357 := bstep (se 4 (by rfl) ⟨747408, by rfl⟩ : syracuseStep 7972357 = 1494817) B1494817
theorem B13264397 : Blo 1453546 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B2762257 : Blo 1453546 2762257 := bstep (se 2 (by rfl) ⟨1035846, by rfl⟩ : syracuseStep 2762257 = 2071693) B2071693
theorem B2180627 : Blo 1453546 2180627 := bstep (se 1 (by rfl) ⟨1635470, by rfl⟩ : syracuseStep 2180627 = 3270941) B3270941
theorem B2180657 : Blo 1453546 2180657 := bstep (se 2 (by rfl) ⟨817746, by rfl⟩ : syracuseStep 2180657 = 1635493) B1635493
theorem B2180675 : Blo 1453546 2180675 := bstep (se 1 (by rfl) ⟨1635506, by rfl⟩ : syracuseStep 2180675 = 3271013) B3271013
theorem B2180705 : Blo 1453546 2180705 := bstep (se 2 (by rfl) ⟨817764, by rfl⟩ : syracuseStep 2180705 = 1635529) B1635529
theorem B4908653 : Blo 1453546 4908653 := bstep (se 3 (by rfl) ⟨920372, by rfl⟩ : syracuseStep 4908653 = 1840745) B1840745
theorem B2180723 : Blo 1453546 2180723 := bstep (se 1 (by rfl) ⟨1635542, by rfl⟩ : syracuseStep 2180723 = 3271085) B3271085
theorem B2180753 : Blo 1453546 2180753 := bstep (se 2 (by rfl) ⟨817782, by rfl⟩ : syracuseStep 2180753 = 1635565) B1635565
theorem B2180771 : Blo 1453546 2180771 := bstep (se 1 (by rfl) ⟨1635578, by rfl⟩ : syracuseStep 2180771 = 3271157) B3271157
theorem B4908707 : Blo 1453546 4908707 := bstep (se 1 (by rfl) ⟨3681530, by rfl⟩ : syracuseStep 4908707 = 7363061) B7363061
theorem B4253357 : Blo 1453546 4253357 := bstep (se 3 (by rfl) ⟨797504, by rfl⟩ : syracuseStep 4253357 = 1595009) B1595009
theorem B2762417 : Blo 1453546 2762417 := bstep (se 2 (by rfl) ⟨1035906, by rfl⟩ : syracuseStep 2762417 = 2071813) B2071813
theorem B2180801 : Blo 1453546 2180801 := bstep (se 2 (by rfl) ⟨817800, by rfl⟩ : syracuseStep 2180801 = 1635601) B1635601
theorem B2180819 : Blo 1453546 2180819 := bstep (se 1 (by rfl) ⟨1635614, by rfl⟩ : syracuseStep 2180819 = 3271229) B3271229
theorem B2180849 : Blo 1453546 2180849 := bstep (se 2 (by rfl) ⟨817818, by rfl⟩ : syracuseStep 2180849 = 1635637) B1635637
theorem B2180867 : Blo 1453546 2180867 := bstep (se 1 (by rfl) ⟨1635650, by rfl⟩ : syracuseStep 2180867 = 3271301) B3271301
theorem B2180897 : Blo 1453546 2180897 := bstep (se 2 (by rfl) ⟨817836, by rfl⟩ : syracuseStep 2180897 = 1635673) B1635673
theorem B2180915 : Blo 1453546 2180915 := bstep (se 1 (by rfl) ⟨1635686, by rfl⟩ : syracuseStep 2180915 = 3271373) B3271373
theorem B2180945 : Blo 1453546 2180945 := bstep (se 2 (by rfl) ⟨817854, by rfl⟩ : syracuseStep 2180945 = 1635709) B1635709
theorem B2180963 : Blo 1453546 2180963 := bstep (se 1 (by rfl) ⟨1635722, by rfl⟩ : syracuseStep 2180963 = 3271445) B3271445
theorem B5523299 : Blo 1453546 5523299 := bstep (se 1 (by rfl) ⟨4142474, by rfl⟩ : syracuseStep 5523299 = 8284949) B8284949
theorem B3680113 : Blo 1453546 3680113 := bstep (se 2 (by rfl) ⟨1380042, by rfl⟩ : syracuseStep 3680113 = 2760085) B2760085
theorem B2180993 : Blo 1453546 2180993 := bstep (se 2 (by rfl) ⟨817872, by rfl⟩ : syracuseStep 2180993 = 1635745) B1635745
theorem B3270545 : Blo 1453546 3270545 := bstep (se 2 (by rfl) ⟨1226454, by rfl⟩ : syracuseStep 3270545 = 2452909) B2452909
theorem B2181011 : Blo 1453546 2181011 := bstep (se 1 (by rfl) ⟨1635758, by rfl⟩ : syracuseStep 2181011 = 3271517) B3271517
theorem B3270563 : Blo 1453546 3270563 := bstep (se 1 (by rfl) ⟨2452922, by rfl⟩ : syracuseStep 3270563 = 4905845) B4905845
theorem B2181041 : Blo 1453546 2181041 := bstep (se 2 (by rfl) ⟨817890, by rfl⟩ : syracuseStep 2181041 = 1635781) B1635781
theorem B4908977 : Blo 1453546 4908977 := bstep (se 2 (by rfl) ⟨1840866, by rfl⟩ : syracuseStep 4908977 = 3681733) B3681733
theorem B2328515 : Blo 1453546 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B2181059 : Blo 1453546 2181059 := bstep (se 1 (by rfl) ⟨1635794, by rfl⟩ : syracuseStep 2181059 = 3271589) B3271589
theorem B10479557 : Blo 1453546 10479557 := bstep (se 4 (by rfl) ⟨982458, by rfl⟩ : syracuseStep 10479557 = 1964917) B1964917
theorem B6989773 : Blo 1453546 6989773 := bstep (se 3 (by rfl) ⟨1310582, by rfl⟩ : syracuseStep 6989773 = 2621165) B2621165
theorem B2181089 : Blo 1453546 2181089 := bstep (se 2 (by rfl) ⟨817908, by rfl⟩ : syracuseStep 2181089 = 1635817) B1635817
theorem B11044835 : Blo 1453546 11044835 := bstep (se 1 (by rfl) ⟨8283626, by rfl⟩ : syracuseStep 11044835 = 16567253) B16567253
theorem B2181107 : Blo 1453546 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B2181137 : Blo 1453546 2181137 := bstep (se 2 (by rfl) ⟨817926, by rfl⟩ : syracuseStep 2181137 = 1635853) B1635853
theorem B2181155 : Blo 1453546 2181155 := bstep (se 1 (by rfl) ⟨1635866, by rfl⟩ : syracuseStep 2181155 = 3271733) B3271733
theorem B2181185 : Blo 1453546 2181185 := bstep (se 2 (by rfl) ⟨817944, by rfl⟩ : syracuseStep 2181185 = 1635889) B1635889
theorem B2762819 : Blo 1453546 2762819 := bstep (se 1 (by rfl) ⟨2072114, by rfl⟩ : syracuseStep 2762819 = 4144229) B4144229
theorem B2181203 : Blo 1453546 2181203 := bstep (se 1 (by rfl) ⟨1635902, by rfl⟩ : syracuseStep 2181203 = 3271805) B3271805
theorem B2181233 : Blo 1453546 2181233 := bstep (se 2 (by rfl) ⟨817962, by rfl⟩ : syracuseStep 2181233 = 1635925) B1635925
theorem B2328707 : Blo 1453546 2328707 := bstep (se 1 (by rfl) ⟨1746530, by rfl⟩ : syracuseStep 2328707 = 3493061) B3493061
theorem B3680387 : Blo 1453546 3680387 := bstep (se 1 (by rfl) ⟨2760290, by rfl⟩ : syracuseStep 3680387 = 5520581) B5520581
theorem B2181251 : Blo 1453546 2181251 := bstep (se 1 (by rfl) ⟨1635938, by rfl⟩ : syracuseStep 2181251 = 3271877) B3271877
theorem B2181281 : Blo 1453546 2181281 := bstep (se 2 (by rfl) ⟨817980, by rfl⟩ : syracuseStep 2181281 = 1635961) B1635961
theorem B3270833 : Blo 1453546 3270833 := bstep (se 2 (by rfl) ⟨1226562, by rfl⟩ : syracuseStep 3270833 = 2453125) B2453125
theorem B3106993 : Blo 1453546 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B2181299 : Blo 1453546 2181299 := bstep (se 1 (by rfl) ⟨1635974, by rfl⟩ : syracuseStep 2181299 = 3271949) B3271949
theorem B3270851 : Blo 1453546 3270851 := bstep (se 1 (by rfl) ⟨2453138, by rfl⟩ : syracuseStep 3270851 = 4906277) B4906277
theorem B2099395 : Blo 1453546 2099395 := bstep (se 1 (by rfl) ⟨1574546, by rfl⟩ : syracuseStep 2099395 = 3149093) B3149093
theorem B2181329 : Blo 1453546 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B2181347 : Blo 1453546 2181347 := bstep (se 1 (by rfl) ⟨1636010, by rfl⟩ : syracuseStep 2181347 = 3272021) B3272021
theorem B1796323 : Blo 1453546 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B2181377 : Blo 1453546 2181377 := bstep (se 2 (by rfl) ⟨818016, by rfl⟩ : syracuseStep 2181377 = 1636033) B1636033
theorem B2181395 : Blo 1453546 2181395 := bstep (se 1 (by rfl) ⟨1636046, by rfl⟩ : syracuseStep 2181395 = 3272093) B3272093
theorem B2181425 : Blo 1453546 2181425 := bstep (se 2 (by rfl) ⟨818034, by rfl⟩ : syracuseStep 2181425 = 1636069) B1636069
theorem B24848693 : Blo 1453546 24848693 := bstep (se 5 (by rfl) ⟨1164782, by rfl⟩ : syracuseStep 24848693 = 2329565) B2329565
theorem B3680579 : Blo 1453546 3680579 := bstep (se 1 (by rfl) ⟨2760434, by rfl⟩ : syracuseStep 3680579 = 5520869) B5520869
theorem B2181443 : Blo 1453546 2181443 := bstep (se 1 (by rfl) ⟨1636082, by rfl⟩ : syracuseStep 2181443 = 3272165) B3272165
theorem B2181473 : Blo 1453546 2181473 := bstep (se 2 (by rfl) ⟨818052, by rfl⟩ : syracuseStep 2181473 = 1636105) B1636105
theorem B2181491 : Blo 1453546 2181491 := bstep (se 1 (by rfl) ⟨1636118, by rfl⟩ : syracuseStep 2181491 = 3272237) B3272237
theorem B2181521 : Blo 1453546 2181521 := bstep (se 2 (by rfl) ⟨818070, by rfl⟩ : syracuseStep 2181521 = 1636141) B1636141
theorem B2181539 : Blo 1453546 2181539 := bstep (se 1 (by rfl) ⟨1636154, by rfl⟩ : syracuseStep 2181539 = 3272309) B3272309
theorem B3107249 : Blo 1453546 3107249 := bstep (se 2 (by rfl) ⟨1165218, by rfl⟩ : syracuseStep 3107249 = 2330437) B2330437
theorem B2181569 : Blo 1453546 2181569 := bstep (se 2 (by rfl) ⟨818088, by rfl⟩ : syracuseStep 2181569 = 1636177) B1636177
theorem B4909517 : Blo 1453546 4909517 := bstep (se 3 (by rfl) ⟨920534, by rfl⟩ : syracuseStep 4909517 = 1841069) B1841069
theorem B3271121 : Blo 1453546 3271121 := bstep (se 2 (by rfl) ⟨1226670, by rfl⟩ : syracuseStep 3271121 = 2453341) B2453341
theorem B2181587 : Blo 1453546 2181587 := bstep (se 1 (by rfl) ⟨1636190, by rfl⟩ : syracuseStep 2181587 = 3272381) B3272381
theorem B3271139 : Blo 1453546 3271139 := bstep (se 1 (by rfl) ⟨2453354, by rfl⟩ : syracuseStep 3271139 = 4906709) B4906709
theorem B2181617 : Blo 1453546 2181617 := bstep (se 2 (by rfl) ⟨818106, by rfl⟩ : syracuseStep 2181617 = 1636213) B1636213
theorem B2181635 : Blo 1453546 2181635 := bstep (se 1 (by rfl) ⟨1636226, by rfl⟩ : syracuseStep 2181635 = 3272453) B3272453
theorem B4909571 : Blo 1453546 4909571 := bstep (se 1 (by rfl) ⟨3682178, by rfl⟩ : syracuseStep 4909571 = 7364357) B7364357
theorem B2181665 : Blo 1453546 2181665 := bstep (se 2 (by rfl) ⟨818124, by rfl⟩ : syracuseStep 2181665 = 1636249) B1636249
theorem B7359011 : Blo 1453546 7359011 := bstep (se 1 (by rfl) ⟨5519258, by rfl⟩ : syracuseStep 7359011 = 11038517) B11038517
theorem B6990371 : Blo 1453546 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B2181683 : Blo 1453546 2181683 := bstep (se 1 (by rfl) ⟨1636262, by rfl⟩ : syracuseStep 2181683 = 3272525) B3272525
theorem B2181713 : Blo 1453546 2181713 := bstep (se 2 (by rfl) ⟨818142, by rfl⟩ : syracuseStep 2181713 = 1636285) B1636285
theorem B1682003 : Blo 1453546 1682003 := bstep (se 1 (by rfl) ⟨1261502, by rfl⟩ : syracuseStep 1682003 = 2523005) B2523005
theorem B2181731 : Blo 1453546 2181731 := bstep (se 1 (by rfl) ⟨1636298, by rfl⟩ : syracuseStep 2181731 = 3272597) B3272597
theorem B2181761 : Blo 1453546 2181761 := bstep (se 2 (by rfl) ⟨818160, by rfl⟩ : syracuseStep 2181761 = 1636321) B1636321
theorem B2181779 : Blo 1453546 2181779 := bstep (se 1 (by rfl) ⟨1636334, by rfl⟩ : syracuseStep 2181779 = 3272669) B3272669
theorem B7867043 : Blo 1453546 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B2181809 : Blo 1453546 2181809 := bstep (se 2 (by rfl) ⟨818178, by rfl⟩ : syracuseStep 2181809 = 1636357) B1636357
theorem B2181827 : Blo 1453546 2181827 := bstep (se 1 (by rfl) ⟨1636370, by rfl⟩ : syracuseStep 2181827 = 3272741) B3272741
theorem B2181857 : Blo 1453546 2181857 := bstep (se 2 (by rfl) ⟨818196, by rfl⟩ : syracuseStep 2181857 = 1636393) B1636393
theorem B3271409 : Blo 1453546 3271409 := bstep (se 2 (by rfl) ⟨1226778, by rfl⟩ : syracuseStep 3271409 = 2453557) B2453557
theorem B2181875 : Blo 1453546 2181875 := bstep (se 1 (by rfl) ⟨1636406, by rfl⟩ : syracuseStep 2181875 = 3272813) B3272813
theorem B3271427 : Blo 1453546 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B2181905 : Blo 1453546 2181905 := bstep (se 2 (by rfl) ⟨818214, by rfl⟩ : syracuseStep 2181905 = 1636429) B1636429
theorem B4909841 : Blo 1453546 4909841 := bstep (se 2 (by rfl) ⟨1841190, by rfl⟩ : syracuseStep 4909841 = 3682381) B3682381
theorem B2181923 : Blo 1453546 2181923 := bstep (se 1 (by rfl) ⟨1636442, by rfl⟩ : syracuseStep 2181923 = 3272885) B3272885
theorem B2181953 : Blo 1453546 2181953 := bstep (se 2 (by rfl) ⟨818232, by rfl⟩ : syracuseStep 2181953 = 1636465) B1636465
theorem B5524301 : Blo 1453546 5524301 := bstep (se 3 (by rfl) ⟨1035806, by rfl⟩ : syracuseStep 5524301 = 2071613) B2071613
theorem B2181971 : Blo 1453546 2181971 := bstep (se 1 (by rfl) ⟨1636478, by rfl⟩ : syracuseStep 2181971 = 3272957) B3272957
theorem B2182001 : Blo 1453546 2182001 := bstep (se 2 (by rfl) ⟨818250, by rfl⟩ : syracuseStep 2182001 = 1636501) B1636501
theorem B2182019 : Blo 1453546 2182019 := bstep (se 1 (by rfl) ⟨1636514, by rfl⟩ : syracuseStep 2182019 = 3273029) B3273029
theorem B106122125 : Blo 1453546 106122125 := bstep (se 3 (by rfl) ⟨19897898, by rfl⟩ : syracuseStep 106122125 = 39795797) B39795797
theorem B2329489 : Blo 1453546 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B2182049 : Blo 1453546 2182049 := bstep (se 2 (by rfl) ⟨818268, by rfl⟩ : syracuseStep 2182049 = 1636537) B1636537
theorem B9325489 : Blo 1453546 9325489 := bstep (se 2 (by rfl) ⟨3497058, by rfl⟩ : syracuseStep 9325489 = 6994117) B6994117
theorem B2182067 : Blo 1453546 2182067 := bstep (se 1 (by rfl) ⟨1636550, by rfl⟩ : syracuseStep 2182067 = 3273101) B3273101
theorem B4139981 : Blo 1453546 4139981 := bstep (se 3 (by rfl) ⟨776246, by rfl⟩ : syracuseStep 4139981 = 1552493) B1552493
theorem B2182097 : Blo 1453546 2182097 := bstep (se 2 (by rfl) ⟨818286, by rfl⟩ : syracuseStep 2182097 = 1636573) B1636573
theorem B2182115 : Blo 1453546 2182115 := bstep (se 1 (by rfl) ⟨1636586, by rfl⟩ : syracuseStep 2182115 = 3273173) B3273173
theorem B18435043 : Blo 1453546 18435043 := bstep (se 1 (by rfl) ⟨13826282, by rfl⟩ : syracuseStep 18435043 = 27652565) B27652565
theorem B2182145 : Blo 1453546 2182145 := bstep (se 2 (by rfl) ⟨818304, by rfl⟩ : syracuseStep 2182145 = 1636609) B1636609
theorem B3271697 : Blo 1453546 3271697 := bstep (se 2 (by rfl) ⟨1226886, by rfl⟩ : syracuseStep 3271697 = 2453773) B2453773
theorem B2182163 : Blo 1453546 2182163 := bstep (se 1 (by rfl) ⟨1636622, by rfl⟩ : syracuseStep 2182163 = 3273245) B3273245
theorem B3271715 : Blo 1453546 3271715 := bstep (se 1 (by rfl) ⟨2453786, by rfl⟩ : syracuseStep 3271715 = 4907573) B4907573
theorem B2182193 : Blo 1453546 2182193 := bstep (se 2 (by rfl) ⟨818322, by rfl⟩ : syracuseStep 2182193 = 1636645) B1636645
theorem B2182211 : Blo 1453546 2182211 := bstep (se 1 (by rfl) ⟨1636658, by rfl⟩ : syracuseStep 2182211 = 3273317) B3273317
theorem B2182241 : Blo 1453546 2182241 := bstep (se 2 (by rfl) ⟨818340, by rfl⟩ : syracuseStep 2182241 = 1636681) B1636681
theorem B8399971 : Blo 1453546 8399971 := bstep (se 1 (by rfl) ⟨6299978, by rfl⟩ : syracuseStep 8399971 = 12599957) B12599957
theorem B2182259 : Blo 1453546 2182259 := bstep (se 1 (by rfl) ⟨1636694, by rfl⟩ : syracuseStep 2182259 = 3273389) B3273389
theorem B4140173 : Blo 1453546 4140173 := bstep (se 3 (by rfl) ⟨776282, by rfl⟩ : syracuseStep 4140173 = 1552565) B1552565
theorem B2182289 : Blo 1453546 2182289 := bstep (se 2 (by rfl) ⟨818358, by rfl⟩ : syracuseStep 2182289 = 1636717) B1636717
theorem B2182307 : Blo 1453546 2182307 := bstep (se 1 (by rfl) ⟨1636730, by rfl⟩ : syracuseStep 2182307 = 3273461) B3273461
theorem B2182337 : Blo 1453546 2182337 := bstep (se 2 (by rfl) ⟨818376, by rfl⟩ : syracuseStep 2182337 = 1636753) B1636753
theorem B2182355 : Blo 1453546 2182355 := bstep (se 1 (by rfl) ⟨1636766, by rfl⟩ : syracuseStep 2182355 = 3273533) B3273533
theorem B3681521 : Blo 1453546 3681521 := bstep (se 2 (by rfl) ⟨1380570, by rfl⟩ : syracuseStep 3681521 = 2761141) B2761141
theorem B2182385 : Blo 1453546 2182385 := bstep (se 2 (by rfl) ⟨818394, by rfl⟩ : syracuseStep 2182385 = 1636789) B1636789
theorem B7367921 : Blo 1453546 7367921 := bstep (se 2 (by rfl) ⟨2762970, by rfl⟩ : syracuseStep 7367921 = 5525941) B5525941
theorem B2182403 : Blo 1453546 2182403 := bstep (se 1 (by rfl) ⟨1636802, by rfl⟩ : syracuseStep 2182403 = 3273605) B3273605
theorem B2182433 : Blo 1453546 2182433 := bstep (se 2 (by rfl) ⟨818412, by rfl⟩ : syracuseStep 2182433 = 1636825) B1636825
theorem B3681571 : Blo 1453546 3681571 := bstep (se 1 (by rfl) ⟨2761178, by rfl⟩ : syracuseStep 3681571 = 5522357) B5522357
theorem B4910381 : Blo 1453546 4910381 := bstep (se 3 (by rfl) ⟨920696, by rfl⟩ : syracuseStep 4910381 = 1841393) B1841393
theorem B3271985 : Blo 1453546 3271985 := bstep (se 2 (by rfl) ⟨1226994, by rfl⟩ : syracuseStep 3271985 = 2453989) B2453989
theorem B2182451 : Blo 1453546 2182451 := bstep (se 1 (by rfl) ⟨1636838, by rfl⟩ : syracuseStep 2182451 = 3273677) B3273677
theorem B3272003 : Blo 1453546 3272003 := bstep (se 1 (by rfl) ⟨2454002, by rfl⟩ : syracuseStep 3272003 = 4908005) B4908005
theorem B7359821 : Blo 1453546 7359821 := bstep (se 3 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 7359821 = 2759933) B2759933
theorem B2182481 : Blo 1453546 2182481 := bstep (se 2 (by rfl) ⟨818430, by rfl⟩ : syracuseStep 2182481 = 1636861) B1636861
theorem B4910435 : Blo 1453546 4910435 := bstep (se 1 (by rfl) ⟨3682826, by rfl⟩ : syracuseStep 4910435 = 7365653) B7365653
theorem B2182499 : Blo 1453546 2182499 := bstep (se 1 (by rfl) ⟨1636874, by rfl⟩ : syracuseStep 2182499 = 3273749) B3273749
theorem B2182529 : Blo 1453546 2182529 := bstep (se 2 (by rfl) ⟨818448, by rfl⟩ : syracuseStep 2182529 = 1636897) B1636897
theorem B24866189 : Blo 1453546 24866189 := bstep (se 3 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 24866189 = 9324821) B9324821
theorem B3542417 : Blo 1453546 3542417 := bstep (se 2 (by rfl) ⟨1328406, by rfl⟩ : syracuseStep 3542417 = 2656813) B2656813
theorem B2182547 : Blo 1453546 2182547 := bstep (se 1 (by rfl) ⟨1636910, by rfl⟩ : syracuseStep 2182547 = 3273821) B3273821
theorem B3681713 : Blo 1453546 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B2182577 : Blo 1453546 2182577 := bstep (se 2 (by rfl) ⟨818466, by rfl⟩ : syracuseStep 2182577 = 1636933) B1636933
theorem B2182595 : Blo 1453546 2182595 := bstep (se 1 (by rfl) ⟨1636946, by rfl⟩ : syracuseStep 2182595 = 3273893) B3273893
theorem B2182625 : Blo 1453546 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B2452963 : Blo 1453546 2452963 := bstep (se 1 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 2452963 = 3679445) B3679445
theorem B1453555 : Blo 1453546 1453555 := bstep (se 1 (by rfl) ⟨1090166, by rfl⟩ : syracuseStep 1453555 = 2180333) B2180333
theorem B2182643 : Blo 1453546 2182643 := bstep (se 1 (by rfl) ⟨1636982, by rfl⟩ : syracuseStep 2182643 = 3273965) B3273965
theorem B1453571 : Blo 1453546 1453571 := bstep (se 1 (by rfl) ⟨1090178, by rfl⟩ : syracuseStep 1453571 = 2180357) B2180357
theorem B2182673 : Blo 1453546 2182673 := bstep (se 2 (by rfl) ⟨818502, by rfl⟩ : syracuseStep 2182673 = 1637005) B1637005
theorem B1453587 : Blo 1453546 1453587 := bstep (se 1 (by rfl) ⟨1090190, by rfl⟩ : syracuseStep 1453587 = 2180381) B2180381
theorem B1453603 : Blo 1453546 1453603 := bstep (se 1 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 1453603 = 2180405) B2180405
theorem B2182691 : Blo 1453546 2182691 := bstep (se 1 (by rfl) ⟨1637018, by rfl⟩ : syracuseStep 2182691 = 3274037) B3274037
theorem B1453619 : Blo 1453546 1453619 := bstep (se 1 (by rfl) ⟨1090214, by rfl⟩ : syracuseStep 1453619 = 2180429) B2180429
theorem B2182721 : Blo 1453546 2182721 := bstep (se 2 (by rfl) ⟨818520, by rfl⟩ : syracuseStep 2182721 = 1637041) B1637041
theorem B1453635 : Blo 1453546 1453635 := bstep (se 1 (by rfl) ⟨1090226, by rfl⟩ : syracuseStep 1453635 = 2180453) B2180453
theorem B3272273 : Blo 1453546 3272273 := bstep (se 2 (by rfl) ⟨1227102, by rfl⟩ : syracuseStep 3272273 = 2454205) B2454205
theorem B1453651 : Blo 1453546 1453651 := bstep (se 1 (by rfl) ⟨1090238, by rfl⟩ : syracuseStep 1453651 = 2180477) B2180477
theorem B2182739 : Blo 1453546 2182739 := bstep (se 1 (by rfl) ⟨1637054, by rfl⟩ : syracuseStep 2182739 = 3274109) B3274109
theorem B1453667 : Blo 1453546 1453667 := bstep (se 1 (by rfl) ⟨1090250, by rfl⟩ : syracuseStep 1453667 = 2180501) B2180501
theorem B3272291 : Blo 1453546 3272291 := bstep (se 1 (by rfl) ⟨2454218, by rfl⟩ : syracuseStep 3272291 = 4908437) B4908437
theorem B2453105 : Blo 1453546 2453105 := bstep (se 2 (by rfl) ⟨919914, by rfl⟩ : syracuseStep 2453105 = 1839829) B1839829
theorem B4910705 : Blo 1453546 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B1453683 : Blo 1453546 1453683 := bstep (se 1 (by rfl) ⟨1090262, by rfl⟩ : syracuseStep 1453683 = 2180525) B2180525
theorem B2182769 : Blo 1453546 2182769 := bstep (se 2 (by rfl) ⟨818538, by rfl⟩ : syracuseStep 2182769 = 1637077) B1637077
theorem B1453699 : Blo 1453546 1453699 := bstep (se 1 (by rfl) ⟨1090274, by rfl⟩ : syracuseStep 1453699 = 2180549) B2180549
theorem B2182787 : Blo 1453546 2182787 := bstep (se 1 (by rfl) ⟨1637090, by rfl⟩ : syracuseStep 2182787 = 3274181) B3274181
theorem B1453715 : Blo 1453546 1453715 := bstep (se 1 (by rfl) ⟨1090286, by rfl⟩ : syracuseStep 1453715 = 2180573) B2180573
theorem B2182817 : Blo 1453546 2182817 := bstep (se 2 (by rfl) ⟨818556, by rfl⟩ : syracuseStep 2182817 = 1637113) B1637113
theorem B1453731 : Blo 1453546 1453731 := bstep (se 1 (by rfl) ⟨1090298, by rfl⟩ : syracuseStep 1453731 = 2180597) B2180597
theorem B1453747 : Blo 1453546 1453747 := bstep (se 1 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 1453747 = 2180621) B2180621
theorem B2182835 : Blo 1453546 2182835 := bstep (se 1 (by rfl) ⟨1637126, by rfl⟩ : syracuseStep 2182835 = 3274253) B3274253
theorem B1453763 : Blo 1453546 1453763 := bstep (se 1 (by rfl) ⟨1090322, by rfl⟩ : syracuseStep 1453763 = 2180645) B2180645
theorem B3108547 : Blo 1453546 3108547 := bstep (se 1 (by rfl) ⟨2331410, by rfl⟩ : syracuseStep 3108547 = 4662821) B4662821
theorem B16789189 : Blo 1453546 16789189 := bstep (se 4 (by rfl) ⟨1573986, by rfl⟩ : syracuseStep 16789189 = 3147973) B3147973
theorem B2182865 : Blo 1453546 2182865 := bstep (se 2 (by rfl) ⟨818574, by rfl⟩ : syracuseStep 2182865 = 1637149) B1637149
theorem B1453779 : Blo 1453546 1453779 := bstep (se 1 (by rfl) ⟨1090334, by rfl⟩ : syracuseStep 1453779 = 2180669) B2180669
theorem B1453795 : Blo 1453546 1453795 := bstep (se 1 (by rfl) ⟨1090346, by rfl⟩ : syracuseStep 1453795 = 2180693) B2180693
theorem B2182883 : Blo 1453546 2182883 := bstep (se 1 (by rfl) ⟨1637162, by rfl⟩ : syracuseStep 2182883 = 3274325) B3274325
theorem B2453233 : Blo 1453546 2453233 := bstep (se 2 (by rfl) ⟨919962, by rfl⟩ : syracuseStep 2453233 = 1839925) B1839925
theorem B1453811 : Blo 1453546 1453811 := bstep (se 1 (by rfl) ⟨1090358, by rfl⟩ : syracuseStep 1453811 = 2180717) B2180717
theorem B2182913 : Blo 1453546 2182913 := bstep (se 2 (by rfl) ⟨818592, by rfl⟩ : syracuseStep 2182913 = 1637185) B1637185
theorem B1453827 : Blo 1453546 1453827 := bstep (se 1 (by rfl) ⟨1090370, by rfl⟩ : syracuseStep 1453827 = 2180741) B2180741
theorem B2453267 : Blo 1453546 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B1453843 : Blo 1453546 1453843 := bstep (se 1 (by rfl) ⟨1090382, by rfl⟩ : syracuseStep 1453843 = 2180765) B2180765
theorem B2182931 : Blo 1453546 2182931 := bstep (se 1 (by rfl) ⟨1637198, by rfl⟩ : syracuseStep 2182931 = 3274397) B3274397
theorem B1453859 : Blo 1453546 1453859 := bstep (se 1 (by rfl) ⟨1090394, by rfl⟩ : syracuseStep 1453859 = 2180789) B2180789
theorem B7860017 : Blo 1453546 7860017 := bstep (se 2 (by rfl) ⟨2947506, by rfl⟩ : syracuseStep 7860017 = 5895013) B5895013
theorem B2182961 : Blo 1453546 2182961 := bstep (se 2 (by rfl) ⟨818610, by rfl⟩ : syracuseStep 2182961 = 1637221) B1637221
theorem B1453875 : Blo 1453546 1453875 := bstep (se 1 (by rfl) ⟨1090406, by rfl⟩ : syracuseStep 1453875 = 2180813) B2180813
theorem B1453891 : Blo 1453546 1453891 := bstep (se 1 (by rfl) ⟨1090418, by rfl⟩ : syracuseStep 1453891 = 2180837) B2180837
theorem B3731267 : Blo 1453546 3731267 := bstep (se 1 (by rfl) ⟨2798450, by rfl⟩ : syracuseStep 3731267 = 5596901) B5596901
theorem B2182979 : Blo 1453546 2182979 := bstep (se 1 (by rfl) ⟨1637234, by rfl⟩ : syracuseStep 2182979 = 3274469) B3274469
theorem B1453907 : Blo 1453546 1453907 := bstep (se 1 (by rfl) ⟨1090430, by rfl⟩ : syracuseStep 1453907 = 2180861) B2180861
theorem B1453923 : Blo 1453546 1453923 := bstep (se 1 (by rfl) ⟨1090442, by rfl⟩ : syracuseStep 1453923 = 2180885) B2180885
theorem B16797539 : Blo 1453546 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B2183009 : Blo 1453546 2183009 := bstep (se 2 (by rfl) ⟨818628, by rfl⟩ : syracuseStep 2183009 = 1637257) B1637257
theorem B3272561 : Blo 1453546 3272561 := bstep (se 2 (by rfl) ⟨1227210, by rfl⟩ : syracuseStep 3272561 = 2454421) B2454421
theorem B1453939 : Blo 1453546 1453939 := bstep (se 1 (by rfl) ⟨1090454, by rfl⟩ : syracuseStep 1453939 = 2180909) B2180909
theorem B2183027 : Blo 1453546 2183027 := bstep (se 1 (by rfl) ⟨1637270, by rfl⟩ : syracuseStep 2183027 = 3274541) B3274541
theorem B1453955 : Blo 1453546 1453955 := bstep (se 1 (by rfl) ⟨1090466, by rfl⟩ : syracuseStep 1453955 = 2180933) B2180933
theorem B3272579 : Blo 1453546 3272579 := bstep (se 1 (by rfl) ⟨2454434, by rfl⟩ : syracuseStep 3272579 = 4908869) B4908869
theorem B2183057 : Blo 1453546 2183057 := bstep (se 2 (by rfl) ⟨818646, by rfl⟩ : syracuseStep 2183057 = 1637293) B1637293
theorem B2453395 : Blo 1453546 2453395 := bstep (se 1 (by rfl) ⟨1840046, by rfl⟩ : syracuseStep 2453395 = 3680093) B3680093
theorem B1453971 : Blo 1453546 1453971 := bstep (se 1 (by rfl) ⟨1090478, by rfl⟩ : syracuseStep 1453971 = 2180957) B2180957
theorem B1453987 : Blo 1453546 1453987 := bstep (se 1 (by rfl) ⟨1090490, by rfl⟩ : syracuseStep 1453987 = 2180981) B2180981
theorem B2183075 : Blo 1453546 2183075 := bstep (se 1 (by rfl) ⟨1637306, by rfl⟩ : syracuseStep 2183075 = 3274613) B3274613
theorem B1454003 : Blo 1453546 1454003 := bstep (se 1 (by rfl) ⟨1090502, by rfl⟩ : syracuseStep 1454003 = 2181005) B2181005
theorem B2183105 : Blo 1453546 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1454019 : Blo 1453546 1454019 := bstep (se 1 (by rfl) ⟨1090514, by rfl⟩ : syracuseStep 1454019 = 2181029) B2181029
theorem B1454035 : Blo 1453546 1454035 := bstep (se 1 (by rfl) ⟨1090526, by rfl⟩ : syracuseStep 1454035 = 2181053) B2181053
theorem B2183123 : Blo 1453546 2183123 := bstep (se 1 (by rfl) ⟨1637342, by rfl⟩ : syracuseStep 2183123 = 3274685) B3274685
theorem B1454051 : Blo 1453546 1454051 := bstep (se 1 (by rfl) ⟨1090538, by rfl⟩ : syracuseStep 1454051 = 2181077) B2181077
theorem B2183153 : Blo 1453546 2183153 := bstep (se 2 (by rfl) ⟨818682, by rfl⟩ : syracuseStep 2183153 = 1637365) B1637365
theorem B1454067 : Blo 1453546 1454067 := bstep (se 1 (by rfl) ⟨1090550, by rfl⟩ : syracuseStep 1454067 = 2181101) B2181101
theorem B1454083 : Blo 1453546 1454083 := bstep (se 1 (by rfl) ⟨1090562, by rfl⟩ : syracuseStep 1454083 = 2181125) B2181125
theorem B2183171 : Blo 1453546 2183171 := bstep (se 1 (by rfl) ⟨1637378, by rfl⟩ : syracuseStep 2183171 = 3274757) B3274757
theorem B1552403 : Blo 1453546 1552403 := bstep (se 1 (by rfl) ⟨1164302, by rfl⟩ : syracuseStep 1552403 = 2328605) B2328605
theorem B1454099 : Blo 1453546 1454099 := bstep (se 1 (by rfl) ⟨1090574, by rfl⟩ : syracuseStep 1454099 = 2181149) B2181149
theorem B2453537 : Blo 1453546 2453537 := bstep (se 2 (by rfl) ⟨920076, by rfl⟩ : syracuseStep 2453537 = 1840153) B1840153
theorem B1454115 : Blo 1453546 1454115 := bstep (se 1 (by rfl) ⟨1090586, by rfl⟩ : syracuseStep 1454115 = 2181173) B2181173
theorem B2183201 : Blo 1453546 2183201 := bstep (se 2 (by rfl) ⟨818700, by rfl⟩ : syracuseStep 2183201 = 1637401) B1637401
theorem B1454131 : Blo 1453546 1454131 := bstep (se 1 (by rfl) ⟨1090598, by rfl⟩ : syracuseStep 1454131 = 2181197) B2181197
theorem B2183219 : Blo 1453546 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B1454147 : Blo 1453546 1454147 := bstep (se 1 (by rfl) ⟨1090610, by rfl⟩ : syracuseStep 1454147 = 2181221) B2181221
theorem B3493955 : Blo 1453546 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B2183249 : Blo 1453546 2183249 := bstep (se 2 (by rfl) ⟨818718, by rfl⟩ : syracuseStep 2183249 = 1637437) B1637437
theorem B1454163 : Blo 1453546 1454163 := bstep (se 1 (by rfl) ⟨1090622, by rfl⟩ : syracuseStep 1454163 = 2181245) B2181245
theorem B1454179 : Blo 1453546 1454179 := bstep (se 1 (by rfl) ⟨1090634, by rfl⟩ : syracuseStep 1454179 = 2181269) B2181269
theorem B2183267 : Blo 1453546 2183267 := bstep (se 1 (by rfl) ⟨1637450, by rfl⟩ : syracuseStep 2183267 = 3274901) B3274901
theorem B4141165 : Blo 1453546 4141165 := bstep (se 3 (by rfl) ⟨776468, by rfl⟩ : syracuseStep 4141165 = 1552937) B1552937
theorem B15544433 : Blo 1453546 15544433 := bstep (se 2 (by rfl) ⟨5829162, by rfl⟩ : syracuseStep 15544433 = 11658325) B11658325
theorem B1454195 : Blo 1453546 1454195 := bstep (se 1 (by rfl) ⟨1090646, by rfl⟩ : syracuseStep 1454195 = 2181293) B2181293
theorem B2183297 : Blo 1453546 2183297 := bstep (se 2 (by rfl) ⟨818736, by rfl⟩ : syracuseStep 2183297 = 1637473) B1637473
theorem B1454211 : Blo 1453546 1454211 := bstep (se 1 (by rfl) ⟨1090658, by rfl⟩ : syracuseStep 1454211 = 2181317) B2181317
theorem B4911245 : Blo 1453546 4911245 := bstep (se 3 (by rfl) ⟨920858, by rfl⟩ : syracuseStep 4911245 = 1841717) B1841717
theorem B3272849 : Blo 1453546 3272849 := bstep (se 2 (by rfl) ⟨1227318, by rfl⟩ : syracuseStep 3272849 = 2454637) B2454637
theorem B1552531 : Blo 1453546 1552531 := bstep (se 1 (by rfl) ⟨1164398, by rfl⟩ : syracuseStep 1552531 = 2328797) B2328797
theorem B1454227 : Blo 1453546 1454227 := bstep (se 1 (by rfl) ⟨1090670, by rfl⟩ : syracuseStep 1454227 = 2181341) B2181341
theorem B2183315 : Blo 1453546 2183315 := bstep (se 1 (by rfl) ⟨1637486, by rfl⟩ : syracuseStep 2183315 = 3274973) B3274973
theorem B2453665 : Blo 1453546 2453665 := bstep (se 2 (by rfl) ⟨920124, by rfl⟩ : syracuseStep 2453665 = 1840249) B1840249
theorem B1454243 : Blo 1453546 1454243 := bstep (se 1 (by rfl) ⟨1090682, by rfl⟩ : syracuseStep 1454243 = 2181365) B2181365
theorem B3272867 : Blo 1453546 3272867 := bstep (se 1 (by rfl) ⟨2454650, by rfl⟩ : syracuseStep 3272867 = 4909301) B4909301
theorem B1454259 : Blo 1453546 1454259 := bstep (se 1 (by rfl) ⟨1090694, by rfl⟩ : syracuseStep 1454259 = 2181389) B2181389
theorem B2453699 : Blo 1453546 2453699 := bstep (se 1 (by rfl) ⟨1840274, by rfl⟩ : syracuseStep 2453699 = 3680549) B3680549
theorem B1454275 : Blo 1453546 1454275 := bstep (se 1 (by rfl) ⟨1090706, by rfl⟩ : syracuseStep 1454275 = 2181413) B2181413
theorem B37761221 : Blo 1453546 37761221 := bstep (se 4 (by rfl) ⟨3540114, by rfl⟩ : syracuseStep 37761221 = 7080229) B7080229
theorem B4911299 : Blo 1453546 4911299 := bstep (se 1 (by rfl) ⟨3683474, by rfl⟩ : syracuseStep 4911299 = 7366949) B7366949
theorem B1454291 : Blo 1453546 1454291 := bstep (se 1 (by rfl) ⟨1090718, by rfl⟩ : syracuseStep 1454291 = 2181437) B2181437
theorem B1454307 : Blo 1453546 1454307 := bstep (se 1 (by rfl) ⟨1090730, by rfl⟩ : syracuseStep 1454307 = 2181461) B2181461
theorem B1454323 : Blo 1453546 1454323 := bstep (se 1 (by rfl) ⟨1090742, by rfl⟩ : syracuseStep 1454323 = 2181485) B2181485
theorem B1454339 : Blo 1453546 1454339 := bstep (se 1 (by rfl) ⟨1090754, by rfl⟩ : syracuseStep 1454339 = 2181509) B2181509
theorem B1454355 : Blo 1453546 1454355 := bstep (se 1 (by rfl) ⟨1090766, by rfl⟩ : syracuseStep 1454355 = 2181533) B2181533
theorem B1454371 : Blo 1453546 1454371 := bstep (se 1 (by rfl) ⟨1090778, by rfl⟩ : syracuseStep 1454371 = 2181557) B2181557
theorem B1454387 : Blo 1453546 1454387 := bstep (se 1 (by rfl) ⟨1090790, by rfl⟩ : syracuseStep 1454387 = 2181581) B2181581
theorem B2453827 : Blo 1453546 2453827 := bstep (se 1 (by rfl) ⟨1840370, by rfl⟩ : syracuseStep 2453827 = 3680741) B3680741
theorem B1454403 : Blo 1453546 1454403 := bstep (se 1 (by rfl) ⟨1090802, by rfl⟩ : syracuseStep 1454403 = 2181605) B2181605
theorem B9318725 : Blo 1453546 9318725 := bstep (se 4 (by rfl) ⟨873630, by rfl⟩ : syracuseStep 9318725 = 1747261) B1747261
theorem B1454419 : Blo 1453546 1454419 := bstep (se 1 (by rfl) ⟨1090814, by rfl⟩ : syracuseStep 1454419 = 2181629) B2181629
theorem B1454435 : Blo 1453546 1454435 := bstep (se 1 (by rfl) ⟨1090826, by rfl⟩ : syracuseStep 1454435 = 2181653) B2181653
theorem B1454451 : Blo 1453546 1454451 := bstep (se 1 (by rfl) ⟨1090838, by rfl⟩ : syracuseStep 1454451 = 2181677) B2181677
theorem B1454467 : Blo 1453546 1454467 := bstep (se 1 (by rfl) ⟨1090850, by rfl⟩ : syracuseStep 1454467 = 2181701) B2181701
theorem B3682705 : Blo 1453546 3682705 := bstep (se 2 (by rfl) ⟨1381014, by rfl⟩ : syracuseStep 3682705 = 2762029) B2762029
theorem B1454483 : Blo 1453546 1454483 := bstep (se 1 (by rfl) ⟨1090862, by rfl⟩ : syracuseStep 1454483 = 2181725) B2181725
theorem B7459235 : Blo 1453546 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B1454499 : Blo 1453546 1454499 := bstep (se 1 (by rfl) ⟨1090874, by rfl⟩ : syracuseStep 1454499 = 2181749) B2181749
theorem B3273137 : Blo 1453546 3273137 := bstep (se 2 (by rfl) ⟨1227426, by rfl⟩ : syracuseStep 3273137 = 2454853) B2454853
theorem B1454515 : Blo 1453546 1454515 := bstep (se 1 (by rfl) ⟨1090886, by rfl⟩ : syracuseStep 1454515 = 2181773) B2181773
theorem B1454531 : Blo 1453546 1454531 := bstep (se 1 (by rfl) ⟨1090898, by rfl⟩ : syracuseStep 1454531 = 2181797) B2181797
theorem B3273155 : Blo 1453546 3273155 := bstep (se 1 (by rfl) ⟨2454866, by rfl⟩ : syracuseStep 3273155 = 4909733) B4909733
theorem B2453969 : Blo 1453546 2453969 := bstep (se 2 (by rfl) ⟨920238, by rfl⟩ : syracuseStep 2453969 = 1840477) B1840477
theorem B4911569 : Blo 1453546 4911569 := bstep (se 2 (by rfl) ⟨1841838, by rfl⟩ : syracuseStep 4911569 = 3683677) B3683677
theorem B1454547 : Blo 1453546 1454547 := bstep (se 1 (by rfl) ⟨1090910, by rfl⟩ : syracuseStep 1454547 = 2181821) B2181821
theorem B1454563 : Blo 1453546 1454563 := bstep (se 1 (by rfl) ⟨1090922, by rfl⟩ : syracuseStep 1454563 = 2181845) B2181845
theorem B1454579 : Blo 1453546 1454579 := bstep (se 1 (by rfl) ⟨1090934, by rfl⟩ : syracuseStep 1454579 = 2181869) B2181869
theorem B1454595 : Blo 1453546 1454595 := bstep (se 1 (by rfl) ⟨1090946, by rfl⟩ : syracuseStep 1454595 = 2181893) B2181893
theorem B8286725 : Blo 1453546 8286725 := bstep (se 4 (by rfl) ⟨776880, by rfl⟩ : syracuseStep 8286725 = 1553761) B1553761
theorem B6214157 : Blo 1453546 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B1454611 : Blo 1453546 1454611 := bstep (se 1 (by rfl) ⟨1090958, by rfl⟩ : syracuseStep 1454611 = 2181917) B2181917
theorem B2331155 : Blo 1453546 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B5239331 : Blo 1453546 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B1454627 : Blo 1453546 1454627 := bstep (se 1 (by rfl) ⟨1090970, by rfl⟩ : syracuseStep 1454627 = 2181941) B2181941
theorem B1839667 : Blo 1453546 1839667 := bstep (se 1 (by rfl) ⟨1379750, by rfl⟩ : syracuseStep 1839667 = 2759501) B2759501
theorem B1454643 : Blo 1453546 1454643 := bstep (se 1 (by rfl) ⟨1090982, by rfl⟩ : syracuseStep 1454643 = 2181965) B2181965
theorem B1454659 : Blo 1453546 1454659 := bstep (se 1 (by rfl) ⟨1090994, by rfl⟩ : syracuseStep 1454659 = 2181989) B2181989
theorem B2454097 : Blo 1453546 2454097 := bstep (se 2 (by rfl) ⟨920286, by rfl⟩ : syracuseStep 2454097 = 1840573) B1840573
theorem B1454675 : Blo 1453546 1454675 := bstep (se 1 (by rfl) ⟨1091006, by rfl⟩ : syracuseStep 1454675 = 2182013) B2182013
theorem B11956835 : Blo 1453546 11956835 := bstep (se 1 (by rfl) ⟨8967626, by rfl⟩ : syracuseStep 11956835 = 17935253) B17935253
theorem B1454691 : Blo 1453546 1454691 := bstep (se 1 (by rfl) ⟨1091018, by rfl⟩ : syracuseStep 1454691 = 2182037) B2182037
theorem B2454131 : Blo 1453546 2454131 := bstep (se 1 (by rfl) ⟨1840598, by rfl⟩ : syracuseStep 2454131 = 3681197) B3681197
theorem B1454707 : Blo 1453546 1454707 := bstep (se 1 (by rfl) ⟨1091030, by rfl⟩ : syracuseStep 1454707 = 2182061) B2182061
theorem B1454723 : Blo 1453546 1454723 := bstep (se 1 (by rfl) ⟨1091042, by rfl⟩ : syracuseStep 1454723 = 2182085) B2182085
theorem B1839763 : Blo 1453546 1839763 := bstep (se 1 (by rfl) ⟨1379822, by rfl⟩ : syracuseStep 1839763 = 2759645) B2759645
theorem B1454739 : Blo 1453546 1454739 := bstep (se 1 (by rfl) ⟨1091054, by rfl⟩ : syracuseStep 1454739 = 2182109) B2182109
theorem B2331283 : Blo 1453546 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B3732131 : Blo 1453546 3732131 := bstep (se 1 (by rfl) ⟨2799098, by rfl⟩ : syracuseStep 3732131 = 5598197) B5598197
theorem B1454755 : Blo 1453546 1454755 := bstep (se 1 (by rfl) ⟨1091066, by rfl⟩ : syracuseStep 1454755 = 2182133) B2182133
theorem B3682979 : Blo 1453546 3682979 := bstep (se 1 (by rfl) ⟨2762234, by rfl⟩ : syracuseStep 3682979 = 5524469) B5524469
theorem B1454771 : Blo 1453546 1454771 := bstep (se 1 (by rfl) ⟨1091078, by rfl⟩ : syracuseStep 1454771 = 2182157) B2182157
theorem B1454787 : Blo 1453546 1454787 := bstep (se 1 (by rfl) ⟨1091090, by rfl⟩ : syracuseStep 1454787 = 2182181) B2182181
theorem B26546885 : Blo 1453546 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B3273425 : Blo 1453546 3273425 := bstep (se 2 (by rfl) ⟨1227534, by rfl⟩ : syracuseStep 3273425 = 2455069) B2455069
theorem B1454803 : Blo 1453546 1454803 := bstep (se 1 (by rfl) ⟨1091102, by rfl⟩ : syracuseStep 1454803 = 2182205) B2182205
theorem B1454819 : Blo 1453546 1454819 := bstep (se 1 (by rfl) ⟨1091114, by rfl⟩ : syracuseStep 1454819 = 2182229) B2182229
theorem B3273443 : Blo 1453546 3273443 := bstep (se 1 (by rfl) ⟨2455082, by rfl⟩ : syracuseStep 3273443 = 4910165) B4910165
theorem B2454259 : Blo 1453546 2454259 := bstep (se 1 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 2454259 = 3681389) B3681389
theorem B1454835 : Blo 1453546 1454835 := bstep (se 1 (by rfl) ⟨1091126, by rfl⟩ : syracuseStep 1454835 = 2182253) B2182253
theorem B1454851 : Blo 1453546 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B1454867 : Blo 1453546 1454867 := bstep (se 1 (by rfl) ⟨1091150, by rfl⟩ : syracuseStep 1454867 = 2182301) B2182301
theorem B1454883 : Blo 1453546 1454883 := bstep (se 1 (by rfl) ⟨1091162, by rfl⟩ : syracuseStep 1454883 = 2182325) B2182325
theorem B1454899 : Blo 1453546 1454899 := bstep (se 1 (by rfl) ⟨1091174, by rfl⟩ : syracuseStep 1454899 = 2182349) B2182349
theorem B1454915 : Blo 1453546 1454915 := bstep (se 1 (by rfl) ⟨1091186, by rfl⟩ : syracuseStep 1454915 = 2182373) B2182373
theorem B1454931 : Blo 1453546 1454931 := bstep (se 1 (by rfl) ⟨1091198, by rfl⟩ : syracuseStep 1454931 = 2182397) B2182397
theorem B1454947 : Blo 1453546 1454947 := bstep (se 1 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 1454947 = 2182421) B2182421
theorem B3683171 : Blo 1453546 3683171 := bstep (se 1 (by rfl) ⟨2762378, by rfl⟩ : syracuseStep 3683171 = 5524757) B5524757
theorem B1454963 : Blo 1453546 1454963 := bstep (se 1 (by rfl) ⟨1091222, by rfl⟩ : syracuseStep 1454963 = 2182445) B2182445
theorem B2454401 : Blo 1453546 2454401 := bstep (se 2 (by rfl) ⟨920400, by rfl⟩ : syracuseStep 2454401 = 1840801) B1840801
theorem B1454979 : Blo 1453546 1454979 := bstep (se 1 (by rfl) ⟨1091234, by rfl⟩ : syracuseStep 1454979 = 2182469) B2182469
theorem B5526413 : Blo 1453546 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B1454995 : Blo 1453546 1454995 := bstep (se 1 (by rfl) ⟨1091246, by rfl⟩ : syracuseStep 1454995 = 2182493) B2182493
theorem B1455011 : Blo 1453546 1455011 := bstep (se 1 (by rfl) ⟨1091258, by rfl⟩ : syracuseStep 1455011 = 2182517) B2182517
theorem B1455027 : Blo 1453546 1455027 := bstep (se 1 (by rfl) ⟨1091270, by rfl⟩ : syracuseStep 1455027 = 2182541) B2182541
theorem B1553347 : Blo 1453546 1553347 := bstep (se 1 (by rfl) ⟨1165010, by rfl⟩ : syracuseStep 1553347 = 2330021) B2330021
theorem B1455043 : Blo 1453546 1455043 := bstep (se 1 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 1455043 = 2182565) B2182565
theorem B8287181 : Blo 1453546 8287181 := bstep (se 3 (by rfl) ⟨1553846, by rfl⟩ : syracuseStep 8287181 = 3107693) B3107693
theorem B1455059 : Blo 1453546 1455059 := bstep (se 1 (by rfl) ⟨1091294, by rfl⟩ : syracuseStep 1455059 = 2182589) B2182589
theorem B1455075 : Blo 1453546 1455075 := bstep (se 1 (by rfl) ⟨1091306, by rfl⟩ : syracuseStep 1455075 = 2182613) B2182613
theorem B4912109 : Blo 1453546 4912109 := bstep (se 3 (by rfl) ⟨921020, by rfl⟩ : syracuseStep 4912109 = 1842041) B1842041
theorem B3273713 : Blo 1453546 3273713 := bstep (se 2 (by rfl) ⟨1227642, by rfl⟩ : syracuseStep 3273713 = 2455285) B2455285
theorem B1455091 : Blo 1453546 1455091 := bstep (se 1 (by rfl) ⟨1091318, by rfl⟩ : syracuseStep 1455091 = 2182637) B2182637
theorem B2454529 : Blo 1453546 2454529 := bstep (se 2 (by rfl) ⟨920448, by rfl⟩ : syracuseStep 2454529 = 1840897) B1840897
theorem B1635331 : Blo 1453546 1635331 := bstep (se 1 (by rfl) ⟨1226498, by rfl⟩ : syracuseStep 1635331 = 2452997) B2452997
theorem B3273731 : Blo 1453546 3273731 := bstep (se 1 (by rfl) ⟨2455298, by rfl⟩ : syracuseStep 3273731 = 4910597) B4910597
theorem B1455107 : Blo 1453546 1455107 := bstep (se 1 (by rfl) ⟨1091330, by rfl⟩ : syracuseStep 1455107 = 2182661) B2182661
theorem B1455123 : Blo 1453546 1455123 := bstep (se 1 (by rfl) ⟨1091342, by rfl⟩ : syracuseStep 1455123 = 2182685) B2182685
theorem B2454563 : Blo 1453546 2454563 := bstep (se 1 (by rfl) ⟨1840922, by rfl⟩ : syracuseStep 2454563 = 3681845) B3681845
theorem B1455139 : Blo 1453546 1455139 := bstep (se 1 (by rfl) ⟨1091354, by rfl⟩ : syracuseStep 1455139 = 2182709) B2182709
theorem B4912163 : Blo 1453546 4912163 := bstep (se 1 (by rfl) ⟨3684122, by rfl⟩ : syracuseStep 4912163 = 7368245) B7368245
theorem B1455155 : Blo 1453546 1455155 := bstep (se 1 (by rfl) ⟨1091366, by rfl⟩ : syracuseStep 1455155 = 2182733) B2182733
theorem B1455171 : Blo 1453546 1455171 := bstep (se 1 (by rfl) ⟨1091378, by rfl⟩ : syracuseStep 1455171 = 2182757) B2182757
theorem B8279117 : Blo 1453546 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B1455187 : Blo 1453546 1455187 := bstep (se 1 (by rfl) ⟨1091390, by rfl⟩ : syracuseStep 1455187 = 2182781) B2182781
theorem B1455203 : Blo 1453546 1455203 := bstep (se 1 (by rfl) ⟨1091402, by rfl⟩ : syracuseStep 1455203 = 2182805) B2182805
theorem B1455219 : Blo 1453546 1455219 := bstep (se 1 (by rfl) ⟨1091414, by rfl⟩ : syracuseStep 1455219 = 2182829) B2182829
theorem B1840259 : Blo 1453546 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B1455235 : Blo 1453546 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B1635475 : Blo 1453546 1635475 := bstep (se 1 (by rfl) ⟨1226606, by rfl⟩ : syracuseStep 1635475 = 2453213) B2453213
theorem B1455251 : Blo 1453546 1455251 := bstep (se 1 (by rfl) ⟨1091438, by rfl⟩ : syracuseStep 1455251 = 2182877) B2182877
theorem B2454691 : Blo 1453546 2454691 := bstep (se 1 (by rfl) ⟨1841018, by rfl⟩ : syracuseStep 2454691 = 3682037) B3682037
theorem B1455267 : Blo 1453546 1455267 := bstep (se 1 (by rfl) ⟨1091450, by rfl⟩ : syracuseStep 1455267 = 2182901) B2182901
theorem B1455283 : Blo 1453546 1455283 := bstep (se 1 (by rfl) ⟨1091462, by rfl⟩ : syracuseStep 1455283 = 2182925) B2182925
theorem B1455299 : Blo 1453546 1455299 := bstep (se 1 (by rfl) ⟨1091474, by rfl⟩ : syracuseStep 1455299 = 2182949) B2182949
theorem B1455315 : Blo 1453546 1455315 := bstep (se 1 (by rfl) ⟨1091486, by rfl⟩ : syracuseStep 1455315 = 2182973) B2182973
theorem B1455331 : Blo 1453546 1455331 := bstep (se 1 (by rfl) ⟨1091498, by rfl⟩ : syracuseStep 1455331 = 2182997) B2182997
theorem B4658413 : Blo 1453546 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B10482929 : Blo 1453546 10482929 := bstep (se 2 (by rfl) ⟨3931098, by rfl⟩ : syracuseStep 10482929 = 7862197) B7862197
theorem B1455347 : Blo 1453546 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B1455363 : Blo 1453546 1455363 := bstep (se 1 (by rfl) ⟨1091522, by rfl⟩ : syracuseStep 1455363 = 2183045) B2183045
theorem B16561421 : Blo 1453546 16561421 := bstep (se 3 (by rfl) ⟨3105266, by rfl⟩ : syracuseStep 16561421 = 6210533) B6210533
theorem B3274001 : Blo 1453546 3274001 := bstep (se 2 (by rfl) ⟨1227750, by rfl⟩ : syracuseStep 3274001 = 2455501) B2455501
theorem B1455379 : Blo 1453546 1455379 := bstep (se 1 (by rfl) ⟨1091534, by rfl⟩ : syracuseStep 1455379 = 2183069) B2183069
theorem B1635619 : Blo 1453546 1635619 := bstep (se 1 (by rfl) ⟨1226714, by rfl⟩ : syracuseStep 1635619 = 2453429) B2453429
theorem B3274019 : Blo 1453546 3274019 := bstep (se 1 (by rfl) ⟨2455514, by rfl⟩ : syracuseStep 3274019 = 4911029) B4911029
theorem B1455395 : Blo 1453546 1455395 := bstep (se 1 (by rfl) ⟨1091546, by rfl⟩ : syracuseStep 1455395 = 2183093) B2183093
theorem B2454833 : Blo 1453546 2454833 := bstep (se 2 (by rfl) ⟨920562, by rfl⟩ : syracuseStep 2454833 = 1841125) B1841125
theorem B4912433 : Blo 1453546 4912433 := bstep (se 2 (by rfl) ⟨1842162, by rfl⟩ : syracuseStep 4912433 = 3684325) B3684325
theorem B1455411 : Blo 1453546 1455411 := bstep (se 1 (by rfl) ⟨1091558, by rfl⟩ : syracuseStep 1455411 = 2183117) B2183117
theorem B1455427 : Blo 1453546 1455427 := bstep (se 1 (by rfl) ⟨1091570, by rfl⟩ : syracuseStep 1455427 = 2183141) B2183141
theorem B1455443 : Blo 1453546 1455443 := bstep (se 1 (by rfl) ⟨1091582, by rfl⟩ : syracuseStep 1455443 = 2183165) B2183165
theorem B1455459 : Blo 1453546 1455459 := bstep (se 1 (by rfl) ⟨1091594, by rfl⟩ : syracuseStep 1455459 = 2183189) B2183189
theorem B1455475 : Blo 1453546 1455475 := bstep (se 1 (by rfl) ⟨1091606, by rfl⟩ : syracuseStep 1455475 = 2183213) B2183213
theorem B1455491 : Blo 1453546 1455491 := bstep (se 1 (by rfl) ⟨1091618, by rfl⟩ : syracuseStep 1455491 = 2183237) B2183237
theorem B12424589 : Blo 1453546 12424589 := bstep (se 3 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 12424589 = 4659221) B4659221
theorem B3929489 : Blo 1453546 3929489 := bstep (se 2 (by rfl) ⟨1473558, by rfl⟩ : syracuseStep 3929489 = 2947117) B2947117
theorem B1455507 : Blo 1453546 1455507 := bstep (se 1 (by rfl) ⟨1091630, by rfl⟩ : syracuseStep 1455507 = 2183261) B2183261
theorem B1455523 : Blo 1453546 1455523 := bstep (se 1 (by rfl) ⟨1091642, by rfl⟩ : syracuseStep 1455523 = 2183285) B2183285
theorem B2454961 : Blo 1453546 2454961 := bstep (se 2 (by rfl) ⟨920610, by rfl⟩ : syracuseStep 2454961 = 1841221) B1841221
theorem B1635763 : Blo 1453546 1635763 := bstep (se 1 (by rfl) ⟨1226822, by rfl⟩ : syracuseStep 1635763 = 2453645) B2453645
theorem B1455539 : Blo 1453546 1455539 := bstep (se 1 (by rfl) ⟨1091654, by rfl⟩ : syracuseStep 1455539 = 2183309) B2183309
theorem B2454995 : Blo 1453546 2454995 := bstep (se 1 (by rfl) ⟨1841246, by rfl⟩ : syracuseStep 2454995 = 3682493) B3682493
theorem B5240369 : Blo 1453546 5240369 := bstep (se 2 (by rfl) ⟨1965138, by rfl⟩ : syracuseStep 5240369 = 3930277) B3930277
theorem B3274289 : Blo 1453546 3274289 := bstep (se 2 (by rfl) ⟨1227858, by rfl⟩ : syracuseStep 3274289 = 2455717) B2455717
theorem B1635907 : Blo 1453546 1635907 := bstep (se 1 (by rfl) ⟨1226930, by rfl⟩ : syracuseStep 1635907 = 2453861) B2453861
theorem B3274307 : Blo 1453546 3274307 := bstep (se 1 (by rfl) ⟨2455730, by rfl⟩ : syracuseStep 3274307 = 4911461) B4911461
theorem B2455123 : Blo 1453546 2455123 := bstep (se 1 (by rfl) ⟨1841342, by rfl⟩ : syracuseStep 2455123 = 3682685) B3682685
theorem B16782947 : Blo 1453546 16782947 := bstep (se 1 (by rfl) ⟨12587210, by rfl⟩ : syracuseStep 16782947 = 25174421) B25174421
theorem B1636051 : Blo 1453546 1636051 := bstep (se 1 (by rfl) ⟨1227038, by rfl⟩ : syracuseStep 1636051 = 2454077) B2454077
theorem B2455265 : Blo 1453546 2455265 := bstep (se 2 (by rfl) ⟨920724, by rfl⟩ : syracuseStep 2455265 = 1841449) B1841449
theorem B4978417 : Blo 1453546 4978417 := bstep (se 2 (by rfl) ⟨1866906, by rfl⟩ : syracuseStep 4978417 = 3733813) B3733813
theorem B3684113 : Blo 1453546 3684113 := bstep (se 2 (by rfl) ⟨1381542, by rfl⟩ : syracuseStep 3684113 = 2763085) B2763085
theorem B4142897 : Blo 1453546 4142897 := bstep (se 2 (by rfl) ⟨1553586, by rfl⟩ : syracuseStep 4142897 = 3107173) B3107173
theorem B1840963 : Blo 1453546 1840963 := bstep (se 1 (by rfl) ⟨1380722, by rfl⟩ : syracuseStep 1840963 = 2761445) B2761445
theorem B3684163 : Blo 1453546 3684163 := bstep (se 1 (by rfl) ⟨2763122, by rfl⟩ : syracuseStep 3684163 = 5526245) B5526245
theorem B3274577 : Blo 1453546 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B2070355 : Blo 1453546 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B2455393 : Blo 1453546 2455393 := bstep (se 2 (by rfl) ⟨920772, by rfl⟩ : syracuseStep 2455393 = 1841545) B1841545
theorem B1636195 : Blo 1453546 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B3274595 : Blo 1453546 3274595 := bstep (se 1 (by rfl) ⟨2455946, by rfl⟩ : syracuseStep 3274595 = 4911893) B4911893
theorem B37279601 : Blo 1453546 37279601 := bstep (se 2 (by rfl) ⟨13979850, by rfl⟩ : syracuseStep 37279601 = 27959701) B27959701
theorem B2455427 : Blo 1453546 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B1841059 : Blo 1453546 1841059 := bstep (se 1 (by rfl) ⟨1380794, by rfl⟩ : syracuseStep 1841059 = 2761589) B2761589
theorem B2070451 : Blo 1453546 2070451 := bstep (se 1 (by rfl) ⟨1552838, by rfl⟩ : syracuseStep 2070451 = 3105677) B3105677
theorem B3684305 : Blo 1453546 3684305 := bstep (se 2 (by rfl) ⟨1381614, by rfl⟩ : syracuseStep 3684305 = 2763229) B2763229
theorem B3315697 : Blo 1453546 3315697 := bstep (se 2 (by rfl) ⟨1243386, by rfl⟩ : syracuseStep 3315697 = 2486773) B2486773
theorem B4143089 : Blo 1453546 4143089 := bstep (se 2 (by rfl) ⟨1553658, by rfl⟩ : syracuseStep 4143089 = 3107317) B3107317
theorem B1636339 : Blo 1453546 1636339 := bstep (se 1 (by rfl) ⟨1227254, by rfl⟩ : syracuseStep 1636339 = 2454509) B2454509
theorem B2455555 : Blo 1453546 2455555 := bstep (se 1 (by rfl) ⟨1841666, by rfl⟩ : syracuseStep 2455555 = 3683333) B3683333
theorem B3274865 : Blo 1453546 3274865 := bstep (se 2 (by rfl) ⟨1228074, by rfl⟩ : syracuseStep 3274865 = 2456149) B2456149
theorem B1636483 : Blo 1453546 1636483 := bstep (se 1 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 1636483 = 2454725) B2454725
theorem B3274883 : Blo 1453546 3274883 := bstep (se 1 (by rfl) ⟨2456162, by rfl⟩ : syracuseStep 3274883 = 4912325) B4912325
theorem B2455697 : Blo 1453546 2455697 := bstep (se 2 (by rfl) ⟨920886, by rfl⟩ : syracuseStep 2455697 = 1841773) B1841773
theorem B7362737 : Blo 1453546 7362737 := bstep (se 2 (by rfl) ⟨2761026, by rfl⟩ : syracuseStep 7362737 = 5522053) B5522053
theorem B4790449 : Blo 1453546 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B2455825 : Blo 1453546 2455825 := bstep (se 2 (by rfl) ⟨920934, by rfl⟩ : syracuseStep 2455825 = 1841869) B1841869
theorem B1636627 : Blo 1453546 1636627 := bstep (se 1 (by rfl) ⟨1227470, by rfl⟩ : syracuseStep 1636627 = 2454941) B2454941
theorem B2455859 : Blo 1453546 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B1841555 : Blo 1453546 1841555 := bstep (se 1 (by rfl) ⟨1381166, by rfl⟩ : syracuseStep 1841555 = 2762333) B2762333
theorem B2070947 : Blo 1453546 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B1636771 : Blo 1453546 1636771 := bstep (se 1 (by rfl) ⟨1227578, by rfl⟩ : syracuseStep 1636771 = 2455157) B2455157
theorem B2455987 : Blo 1453546 2455987 := bstep (se 1 (by rfl) ⟨1841990, by rfl⟩ : syracuseStep 2455987 = 3683981) B3683981
theorem B5241293 : Blo 1453546 5241293 := bstep (se 3 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 5241293 = 1965485) B1965485
theorem B4422097 : Blo 1453546 4422097 := bstep (se 2 (by rfl) ⟨1658286, by rfl⟩ : syracuseStep 4422097 = 3316573) B3316573
theorem B1636915 : Blo 1453546 1636915 := bstep (se 1 (by rfl) ⟨1227686, by rfl⟩ : syracuseStep 1636915 = 2455373) B2455373
theorem B2456129 : Blo 1453546 2456129 := bstep (se 2 (by rfl) ⟨921048, by rfl⟩ : syracuseStep 2456129 = 1842097) B1842097
theorem B2210417 : Blo 1453546 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B67148401 : Blo 1453546 67148401 := bstep (se 2 (by rfl) ⟨25180650, by rfl⟩ : syracuseStep 67148401 = 50361301) B50361301
theorem B4659875 : Blo 1453546 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B1637059 : Blo 1453546 1637059 := bstep (se 1 (by rfl) ⟨1227794, by rfl⟩ : syracuseStep 1637059 = 2455589) B2455589
theorem B1866451 : Blo 1453546 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B3316483 : Blo 1453546 3316483 := bstep (se 1 (by rfl) ⟨2487362, by rfl⟩ : syracuseStep 3316483 = 4974725) B4974725
theorem B1637203 : Blo 1453546 1637203 := bstep (se 1 (by rfl) ⟨1227902, by rfl⟩ : syracuseStep 1637203 = 2455805) B2455805
theorem B2800561 : Blo 1453546 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B4144081 : Blo 1453546 4144081 := bstep (se 2 (by rfl) ⟨1554030, by rfl⟩ : syracuseStep 4144081 = 3108061) B3108061
theorem B2620387 : Blo 1453546 2620387 := bstep (se 1 (by rfl) ⟨1965290, by rfl⟩ : syracuseStep 2620387 = 3930581) B3930581
theorem B1637347 : Blo 1453546 1637347 := bstep (se 1 (by rfl) ⟨1228010, by rfl⟩ : syracuseStep 1637347 = 2456021) B2456021
theorem B2759683 : Blo 1453546 2759683 := bstep (se 1 (by rfl) ⟨2069762, by rfl⟩ : syracuseStep 2759683 = 4139525) B4139525
theorem B2071585 : Blo 1453546 2071585 := bstep (se 2 (by rfl) ⟨776844, by rfl⟩ : syracuseStep 2071585 = 1553689) B1553689
theorem B1965107 : Blo 1453546 1965107 := bstep (se 1 (by rfl) ⟨1473830, by rfl⟩ : syracuseStep 1965107 = 2947661) B2947661
theorem B4906061 : Blo 1453546 4906061 := bstep (se 3 (by rfl) ⟨919886, by rfl⟩ : syracuseStep 4906061 = 1839773) B1839773
theorem B4906115 : Blo 1453546 4906115 := bstep (se 1 (by rfl) ⟨3679586, by rfl⟩ : syracuseStep 4906115 = 7359173) B7359173
theorem B11050181 : Blo 1453546 11050181 := bstep (se 4 (by rfl) ⟨1035954, by rfl⟩ : syracuseStep 11050181 = 2071909) B2071909
theorem B4144355 : Blo 1453546 4144355 := bstep (se 1 (by rfl) ⟨3108266, by rfl⟩ : syracuseStep 4144355 = 6216533) B6216533
theorem B8281349 : Blo 1453546 8281349 := bstep (se 4 (by rfl) ⟨776376, by rfl⟩ : syracuseStep 8281349 = 1552753) B1552753
theorem B9313649 : Blo 1453546 9313649 := bstep (se 2 (by rfl) ⟨3492618, by rfl⟩ : syracuseStep 9313649 = 6985237) B6985237
theorem B2071921 : Blo 1453546 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B4906385 : Blo 1453546 4906385 := bstep (se 2 (by rfl) ⟨1839894, by rfl⟩ : syracuseStep 4906385 = 3679789) B3679789
theorem B4144547 : Blo 1453546 4144547 := bstep (se 1 (by rfl) ⟨3108410, by rfl⟩ : syracuseStep 4144547 = 6216821) B6216821
theorem B2620849 : Blo 1453546 2620849 := bstep (se 2 (by rfl) ⟨982818, by rfl⟩ : syracuseStep 2620849 = 1965637) B1965637
theorem B2760131 : Blo 1453546 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B3931661 : Blo 1453546 3931661 := bstep (se 3 (by rfl) ⟨737186, by rfl⟩ : syracuseStep 3931661 = 1474373) B1474373
theorem B7364195 : Blo 1453546 7364195 := bstep (se 1 (by rfl) ⟨5523146, by rfl⟩ : syracuseStep 7364195 = 11046293) B11046293
theorem B1474243 : Blo 1453546 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B2760419 : Blo 1453546 2760419 := bstep (se 1 (by rfl) ⟨2070314, by rfl⟩ : syracuseStep 2760419 = 4140629) B4140629
theorem B3104515 : Blo 1453546 3104515 := bstep (se 1 (by rfl) ⟨2328386, by rfl⟩ : syracuseStep 3104515 = 4656773) B4656773
theorem B4906925 : Blo 1453546 4906925 := bstep (se 3 (by rfl) ⟨920048, by rfl⟩ : syracuseStep 4906925 = 1840097) B1840097
theorem B8282033 : Blo 1453546 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B4906979 : Blo 1453546 4906979 := bstep (se 1 (by rfl) ⟨3680234, by rfl⟩ : syracuseStep 4906979 = 7360469) B7360469
theorem B31449059 : Blo 1453546 31449059 := bstep (se 1 (by rfl) ⟨23586794, by rfl⟩ : syracuseStep 31449059 = 47173589) B47173589
theorem B2621425 : Blo 1453546 2621425 := bstep (se 2 (by rfl) ⟨983034, by rfl⟩ : syracuseStep 2621425 = 1966069) B1966069
theorem B2211851 : Blo 1453546 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B11042891 : Blo 1453546 11042891 := bstep (se 1 (by rfl) ⟨8282168, by rfl⟩ : syracuseStep 11042891 = 16564337) B16564337
theorem B10362955 : Blo 1453546 10362955 := bstep (se 1 (by rfl) ⟨7772216, by rfl⟩ : syracuseStep 10362955 = 15544433) B15544433
theorem B25174147 : Blo 1453546 25174147 := bstep (se 1 (by rfl) ⟨18880610, by rfl⟩ : syracuseStep 25174147 = 37761221) B37761221
theorem B5521553 : Blo 1453546 5521553 := bstep (se 2 (by rfl) ⟨2070582, by rfl⟩ : syracuseStep 5521553 = 4141165) B4141165
theorem B1966231 : Blo 1453546 1966231 := bstep (se 1 (by rfl) ⟨1474673, by rfl⟩ : syracuseStep 1966231 = 2949347) B2949347
theorem B8847577 : Blo 1453546 8847577 := bstep (se 2 (by rfl) ⟨3317841, by rfl⟩ : syracuseStep 8847577 = 6635683) B6635683
theorem B4423897 : Blo 1453546 4423897 := bstep (se 2 (by rfl) ⟨1658961, by rfl⟩ : syracuseStep 4423897 = 3317923) B3317923
theorem B4972823 : Blo 1453546 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B1966361 : Blo 1453546 1966361 := bstep (se 2 (by rfl) ⟨737385, by rfl⟩ : syracuseStep 1966361 = 1474771) B1474771
theorem B6209885 : Blo 1453546 6209885 := bstep (se 3 (by rfl) ⟨1164353, by rfl⟩ : syracuseStep 6209885 = 2328707) B2328707
theorem B4907357 : Blo 1453546 4907357 := bstep (se 3 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 4907357 = 1840259) B1840259
theorem B7971223 : Blo 1453546 7971223 := bstep (se 1 (by rfl) ⟨5978417, by rfl⟩ : syracuseStep 7971223 = 11956835) B11956835
theorem B2949913 : Blo 1453546 2949913 := bstep (se 2 (by rfl) ⟨1106217, by rfl⟩ : syracuseStep 2949913 = 2212435) B2212435
theorem B2622233 : Blo 1453546 2622233 := bstep (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) B1966675
theorem B89531201 : Blo 1453546 89531201 := bstep (se 2 (by rfl) ⟨33574200, by rfl⟩ : syracuseStep 89531201 = 67148401) B67148401
theorem B6988619 : Blo 1453546 6988619 := bstep (se 1 (by rfl) ⟨5241464, by rfl⟩ : syracuseStep 6988619 = 10482929) B10482929
theorem B5522327 : Blo 1453546 5522327 := bstep (se 1 (by rfl) ⟨4141745, by rfl⟩ : syracuseStep 5522327 = 8283491) B8283491
theorem B8283059 : Blo 1453546 8283059 := bstep (se 1 (by rfl) ⟨6212294, by rfl⟩ : syracuseStep 8283059 = 12424589) B12424589
theorem B5899211 : Blo 1453546 5899211 := bstep (se 1 (by rfl) ⟨4424408, by rfl⟩ : syracuseStep 5899211 = 8848817) B8848817
theorem B5522525 : Blo 1453546 5522525 := bstep (se 3 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 5522525 = 2070947) B2070947
theorem B11052125 : Blo 1453546 11052125 := bstep (se 3 (by rfl) ⟨2072273, by rfl⟩ : syracuseStep 11052125 = 4144547) B4144547
theorem B2835571 : Blo 1453546 2835571 := bstep (se 1 (by rfl) ⟨2126678, by rfl⟩ : syracuseStep 2835571 = 4253357) B4253357
theorem B3105985 : Blo 1453546 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B2761931 : Blo 1453546 2761931 := bstep (se 1 (by rfl) ⟨2071448, by rfl⟩ : syracuseStep 2761931 = 4142897) B4142897
theorem B2180363 : Blo 1453546 2180363 := bstep (se 1 (by rfl) ⟨1635272, by rfl⟩ : syracuseStep 2180363 = 3270545) B3270545
theorem B2180375 : Blo 1453546 2180375 := bstep (se 1 (by rfl) ⟨1635281, by rfl⟩ : syracuseStep 2180375 = 3270563) B3270563
theorem B2180441 : Blo 1453546 2180441 := bstep (se 2 (by rfl) ⟨817665, by rfl⟩ : syracuseStep 2180441 = 1635331) B1635331
theorem B3679577 : Blo 1453546 3679577 := bstep (se 2 (by rfl) ⟨1379841, by rfl⟩ : syracuseStep 3679577 = 2759683) B2759683
theorem B17687909 : Blo 1453546 17687909 := bstep (se 4 (by rfl) ⟨1658241, by rfl⟩ : syracuseStep 17687909 = 3316483) B3316483
theorem B2762113 : Blo 1453546 2762113 := bstep (se 2 (by rfl) ⟨1035792, by rfl⟩ : syracuseStep 2762113 = 2071585) B2071585
theorem B31450517 : Blo 1453546 31450517 := bstep (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) B1474243
theorem B2180555 : Blo 1453546 2180555 := bstep (se 1 (by rfl) ⟨1635416, by rfl⟩ : syracuseStep 2180555 = 3270833) B3270833
theorem B4908491 : Blo 1453546 4908491 := bstep (se 1 (by rfl) ⟨3681368, by rfl⟩ : syracuseStep 4908491 = 7362737) B7362737
theorem B2180567 : Blo 1453546 2180567 := bstep (se 1 (by rfl) ⟨1635425, by rfl⟩ : syracuseStep 2180567 = 3270851) B3270851
theorem B11199961 : Blo 1453546 11199961 := bstep (se 2 (by rfl) ⟨4199985, by rfl⟩ : syracuseStep 11199961 = 8399971) B8399971
theorem B2180633 : Blo 1453546 2180633 := bstep (se 2 (by rfl) ⟨817737, by rfl⟩ : syracuseStep 2180633 = 1635475) B1635475
theorem B16565795 : Blo 1453546 16565795 := bstep (se 1 (by rfl) ⟨12424346, by rfl⟩ : syracuseStep 16565795 = 24848693) B24848693
theorem B2180747 : Blo 1453546 2180747 := bstep (se 1 (by rfl) ⟨1635560, by rfl⟩ : syracuseStep 2180747 = 3271121) B3271121
theorem B6211217 : Blo 1453546 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B2180759 : Blo 1453546 2180759 := bstep (se 1 (by rfl) ⟨1635569, by rfl⟩ : syracuseStep 2180759 = 3271139) B3271139
theorem B2180825 : Blo 1453546 2180825 := bstep (se 2 (by rfl) ⟨817809, by rfl⟩ : syracuseStep 2180825 = 1635619) B1635619
theorem B4908761 : Blo 1453546 4908761 := bstep (se 2 (by rfl) ⟨1840785, by rfl⟩ : syracuseStep 4908761 = 3681571) B3681571
theorem B3106583 : Blo 1453546 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B5244695 : Blo 1453546 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B2762561 : Blo 1453546 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B2180939 : Blo 1453546 2180939 := bstep (se 1 (by rfl) ⟨1635704, by rfl⟩ : syracuseStep 2180939 = 3271409) B3271409
theorem B2180951 : Blo 1453546 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B2181017 : Blo 1453546 2181017 := bstep (se 2 (by rfl) ⟨817881, by rfl⟩ : syracuseStep 2181017 = 1635763) B1635763
theorem B70748083 : Blo 1453546 70748083 := bstep (se 1 (by rfl) ⟨53061062, by rfl⟩ : syracuseStep 70748083 = 106122125) B106122125
theorem B3270617 : Blo 1453546 3270617 := bstep (se 2 (by rfl) ⟨1226481, by rfl⟩ : syracuseStep 3270617 = 2452963) B2452963
theorem B5900249 : Blo 1453546 5900249 := bstep (se 2 (by rfl) ⟨2212593, by rfl⟩ : syracuseStep 5900249 = 4425187) B4425187
theorem B2181131 : Blo 1453546 2181131 := bstep (se 1 (by rfl) ⟨1635848, by rfl⟩ : syracuseStep 2181131 = 3271697) B3271697
theorem B2181143 : Blo 1453546 2181143 := bstep (se 1 (by rfl) ⟨1635857, by rfl⟩ : syracuseStep 2181143 = 3271715) B3271715
theorem B3270707 : Blo 1453546 3270707 := bstep (se 1 (by rfl) ⟨2453030, by rfl⟩ : syracuseStep 3270707 = 4906061) B4906061
theorem B3270743 : Blo 1453546 3270743 := bstep (se 1 (by rfl) ⟨2453057, by rfl⟩ : syracuseStep 3270743 = 4906115) B4906115
theorem B2181209 : Blo 1453546 2181209 := bstep (se 2 (by rfl) ⟨817953, by rfl⟩ : syracuseStep 2181209 = 1635907) B1635907
theorem B7366787 : Blo 1453546 7366787 := bstep (se 1 (by rfl) ⟨5525090, by rfl⟩ : syracuseStep 7366787 = 11050181) B11050181
theorem B2762903 : Blo 1453546 2762903 := bstep (se 1 (by rfl) ⟨2072177, by rfl⟩ : syracuseStep 2762903 = 4144355) B4144355
theorem B2181323 : Blo 1453546 2181323 := bstep (se 1 (by rfl) ⟨1635992, by rfl⟩ : syracuseStep 2181323 = 3271985) B3271985
theorem B2181335 : Blo 1453546 2181335 := bstep (se 1 (by rfl) ⟨1636001, by rfl⟩ : syracuseStep 2181335 = 3272003) B3272003
theorem B3270923 : Blo 1453546 3270923 := bstep (se 1 (by rfl) ⟨2453192, by rfl⟩ : syracuseStep 3270923 = 4906385) B4906385
theorem B2361611 : Blo 1453546 2361611 := bstep (se 1 (by rfl) ⟨1771208, by rfl⟩ : syracuseStep 2361611 = 3542417) B3542417
theorem B2181401 : Blo 1453546 2181401 := bstep (se 2 (by rfl) ⟨818025, by rfl⟩ : syracuseStep 2181401 = 1636051) B1636051
theorem B3270977 : Blo 1453546 3270977 := bstep (se 2 (by rfl) ⟨1226616, by rfl⟩ : syracuseStep 3270977 = 2453233) B2453233
theorem B6637889 : Blo 1453546 6637889 := bstep (se 2 (by rfl) ⟨2489208, by rfl⟩ : syracuseStep 6637889 = 4978417) B4978417
theorem B4139353 : Blo 1453546 4139353 := bstep (se 2 (by rfl) ⟨1552257, by rfl⟩ : syracuseStep 4139353 = 3104515) B3104515
theorem B8284517 : Blo 1453546 8284517 := bstep (se 4 (by rfl) ⟨776673, by rfl⟩ : syracuseStep 8284517 = 1553347) B1553347
theorem B2181515 : Blo 1453546 2181515 := bstep (se 1 (by rfl) ⟨1636136, by rfl⟩ : syracuseStep 2181515 = 3272273) B3272273
theorem B2181527 : Blo 1453546 2181527 := bstep (se 1 (by rfl) ⟨1636145, by rfl⟩ : syracuseStep 2181527 = 3272291) B3272291
theorem B4909463 : Blo 1453546 4909463 := bstep (se 1 (by rfl) ⟨3682097, by rfl⟩ : syracuseStep 4909463 = 7364195) B7364195
theorem B2181593 : Blo 1453546 2181593 := bstep (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) B1636195
theorem B27945485 : Blo 1453546 27945485 := bstep (se 3 (by rfl) ⟨5239778, by rfl⟩ : syracuseStep 27945485 = 10479557) B10479557
theorem B3271193 : Blo 1453546 3271193 := bstep (se 2 (by rfl) ⟨1226697, by rfl⟩ : syracuseStep 3271193 = 2453395) B2453395
theorem B2181707 : Blo 1453546 2181707 := bstep (se 1 (by rfl) ⟨1636280, by rfl⟩ : syracuseStep 2181707 = 3272561) B3272561
theorem B2181719 : Blo 1453546 2181719 := bstep (se 1 (by rfl) ⟨1636289, by rfl⟩ : syracuseStep 2181719 = 3272579) B3272579
theorem B3271283 : Blo 1453546 3271283 := bstep (se 1 (by rfl) ⟨2453462, by rfl⟩ : syracuseStep 3271283 = 4906925) B4906925
theorem B3271319 : Blo 1453546 3271319 := bstep (se 1 (by rfl) ⟨2453489, by rfl⟩ : syracuseStep 3271319 = 4906979) B4906979
theorem B20966039 : Blo 1453546 20966039 := bstep (se 1 (by rfl) ⟨15724529, by rfl⟩ : syracuseStep 20966039 = 31449059) B31449059
theorem B2181785 : Blo 1453546 2181785 := bstep (se 2 (by rfl) ⟨818169, by rfl⟩ : syracuseStep 2181785 = 1636339) B1636339
theorem B2157259 : Blo 1453546 2157259 := bstep (se 1 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 2157259 = 3235889) B3235889
theorem B4139741 : Blo 1453546 4139741 := bstep (se 3 (by rfl) ⟨776201, by rfl⟩ : syracuseStep 4139741 = 1552403) B1552403
theorem B2181899 : Blo 1453546 2181899 := bstep (se 1 (by rfl) ⟨1636424, by rfl⟩ : syracuseStep 2181899 = 3272849) B3272849
theorem B2181911 : Blo 1453546 2181911 := bstep (se 1 (by rfl) ⟨1636433, by rfl⟩ : syracuseStep 2181911 = 3272867) B3272867
theorem B3271499 : Blo 1453546 3271499 := bstep (se 1 (by rfl) ⟨2453624, by rfl⟩ : syracuseStep 3271499 = 4907249) B4907249
theorem B3107659 : Blo 1453546 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B2181977 : Blo 1453546 2181977 := bstep (se 2 (by rfl) ⟨818241, by rfl⟩ : syracuseStep 2181977 = 1636483) B1636483
theorem B9317213 : Blo 1453546 9317213 := bstep (se 3 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 9317213 = 3493955) B3493955
theorem B3271553 : Blo 1453546 3271553 := bstep (se 2 (by rfl) ⟨1226832, by rfl⟩ : syracuseStep 3271553 = 2453665) B2453665
theorem B6212483 : Blo 1453546 6212483 := bstep (se 1 (by rfl) ⟨4659362, by rfl⟩ : syracuseStep 6212483 = 9318725) B9318725
theorem B4910003 : Blo 1453546 4910003 := bstep (se 1 (by rfl) ⟨3682502, by rfl⟩ : syracuseStep 4910003 = 7365005) B7365005
theorem B3681227 : Blo 1453546 3681227 := bstep (se 1 (by rfl) ⟨2760920, by rfl⟩ : syracuseStep 3681227 = 5521841) B5521841
theorem B2182091 : Blo 1453546 2182091 := bstep (se 1 (by rfl) ⟨1636568, by rfl⟩ : syracuseStep 2182091 = 3273137) B3273137
theorem B2182103 : Blo 1453546 2182103 := bstep (se 1 (by rfl) ⟨1636577, by rfl⟩ : syracuseStep 2182103 = 3273155) B3273155
theorem B2395097 : Blo 1453546 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B5524483 : Blo 1453546 5524483 := bstep (se 1 (by rfl) ⟨4143362, by rfl⟩ : syracuseStep 5524483 = 8286725) B8286725
theorem B3492887 : Blo 1453546 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B2182169 : Blo 1453546 2182169 := bstep (se 2 (by rfl) ⟨818313, by rfl⟩ : syracuseStep 2182169 = 1636627) B1636627
theorem B3271769 : Blo 1453546 3271769 := bstep (se 2 (by rfl) ⟨1226913, by rfl⟩ : syracuseStep 3271769 = 2453827) B2453827
theorem B17697923 : Blo 1453546 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B2182283 : Blo 1453546 2182283 := bstep (se 1 (by rfl) ⟨1636712, by rfl⟩ : syracuseStep 2182283 = 3273425) B3273425
theorem B2182295 : Blo 1453546 2182295 := bstep (se 1 (by rfl) ⟨1636721, by rfl⟩ : syracuseStep 2182295 = 3273443) B3273443
theorem B3271859 : Blo 1453546 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B4910273 : Blo 1453546 4910273 := bstep (se 2 (by rfl) ⟨1841352, by rfl⟩ : syracuseStep 4910273 = 3682705) B3682705
theorem B3271895 : Blo 1453546 3271895 := bstep (se 1 (by rfl) ⟨2453921, by rfl⟩ : syracuseStep 3271895 = 4907843) B4907843
theorem B2182361 : Blo 1453546 2182361 := bstep (se 2 (by rfl) ⟨818385, by rfl⟩ : syracuseStep 2182361 = 1636771) B1636771
theorem B5524787 : Blo 1453546 5524787 := bstep (se 1 (by rfl) ⟨4143590, by rfl⟩ : syracuseStep 5524787 = 8287181) B8287181
theorem B2182475 : Blo 1453546 2182475 := bstep (se 1 (by rfl) ⟨1636856, by rfl⟩ : syracuseStep 2182475 = 3273713) B3273713
theorem B1748299 : Blo 1453546 1748299 := bstep (se 1 (by rfl) ⟨1311224, by rfl⟩ : syracuseStep 1748299 = 2622449) B2622449
theorem B2182487 : Blo 1453546 2182487 := bstep (se 1 (by rfl) ⟨1636865, by rfl⟩ : syracuseStep 2182487 = 3273731) B3273731
theorem B20983157 : Blo 1453546 20983157 := bstep (se 5 (by rfl) ⟨983585, by rfl⟩ : syracuseStep 20983157 = 1967171) B1967171
theorem B3272075 : Blo 1453546 3272075 := bstep (se 1 (by rfl) ⟨2454056, by rfl⟩ : syracuseStep 3272075 = 4908113) B4908113
theorem B2452889 : Blo 1453546 2452889 := bstep (se 2 (by rfl) ⟨919833, by rfl⟩ : syracuseStep 2452889 = 1839667) B1839667
theorem B2182553 : Blo 1453546 2182553 := bstep (se 2 (by rfl) ⟨818457, by rfl⟩ : syracuseStep 2182553 = 1636915) B1636915
theorem B3272129 : Blo 1453546 3272129 := bstep (se 2 (by rfl) ⟨1227048, by rfl⟩ : syracuseStep 3272129 = 2454097) B2454097
theorem B1453547 : Blo 1453546 1453547 := bstep (se 1 (by rfl) ⟨1090160, by rfl⟩ : syracuseStep 1453547 = 2180321) B2180321
theorem B1453559 : Blo 1453546 1453559 := bstep (se 1 (by rfl) ⟨1090169, by rfl⟩ : syracuseStep 1453559 = 2180339) B2180339
theorem B1453579 : Blo 1453546 1453579 := bstep (se 1 (by rfl) ⟨1090184, by rfl⟩ : syracuseStep 1453579 = 2180369) B2180369
theorem B2182667 : Blo 1453546 2182667 := bstep (se 1 (by rfl) ⟨1637000, by rfl⟩ : syracuseStep 2182667 = 3274001) B3274001
theorem B1453591 : Blo 1453546 1453591 := bstep (se 1 (by rfl) ⟨1090193, by rfl⟩ : syracuseStep 1453591 = 2180387) B2180387
theorem B2453017 : Blo 1453546 2453017 := bstep (se 2 (by rfl) ⟨919881, by rfl⟩ : syracuseStep 2453017 = 1839763) B1839763
theorem B2182679 : Blo 1453546 2182679 := bstep (se 1 (by rfl) ⟨1637009, by rfl⟩ : syracuseStep 2182679 = 3274019) B3274019
theorem B3108377 : Blo 1453546 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B1453611 : Blo 1453546 1453611 := bstep (se 1 (by rfl) ⟨1090208, by rfl⟩ : syracuseStep 1453611 = 2180417) B2180417
theorem B1453623 : Blo 1453546 1453623 := bstep (se 1 (by rfl) ⟨1090217, by rfl⟩ : syracuseStep 1453623 = 2180435) B2180435
theorem B1453643 : Blo 1453546 1453643 := bstep (se 1 (by rfl) ⟨1090232, by rfl⟩ : syracuseStep 1453643 = 2180465) B2180465
theorem B1453655 : Blo 1453546 1453655 := bstep (se 1 (by rfl) ⟨1090241, by rfl⟩ : syracuseStep 1453655 = 2180483) B2180483
theorem B2182745 : Blo 1453546 2182745 := bstep (se 2 (by rfl) ⟨818529, by rfl⟩ : syracuseStep 2182745 = 1637059) B1637059
theorem B1453675 : Blo 1453546 1453675 := bstep (se 1 (by rfl) ⟨1090256, by rfl⟩ : syracuseStep 1453675 = 2180513) B2180513
theorem B1453687 : Blo 1453546 1453687 := bstep (se 1 (by rfl) ⟨1090265, by rfl⟩ : syracuseStep 1453687 = 2180531) B2180531
theorem B1453707 : Blo 1453546 1453707 := bstep (se 1 (by rfl) ⟨1090280, by rfl⟩ : syracuseStep 1453707 = 2180561) B2180561
theorem B1453719 : Blo 1453546 1453719 := bstep (se 1 (by rfl) ⟨1090289, by rfl⟩ : syracuseStep 1453719 = 2180579) B2180579
theorem B3272345 : Blo 1453546 3272345 := bstep (se 2 (by rfl) ⟨1227129, by rfl⟩ : syracuseStep 3272345 = 2454259) B2454259
theorem B1453739 : Blo 1453546 1453739 := bstep (se 1 (by rfl) ⟨1090304, by rfl⟩ : syracuseStep 1453739 = 2180609) B2180609
theorem B8842931 : Blo 1453546 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B1453751 : Blo 1453546 1453751 := bstep (se 1 (by rfl) ⟨1090313, by rfl⟩ : syracuseStep 1453751 = 2180627) B2180627
theorem B1453771 : Blo 1453546 1453771 := bstep (se 1 (by rfl) ⟨1090328, by rfl⟩ : syracuseStep 1453771 = 2180657) B2180657
theorem B3493579 : Blo 1453546 3493579 := bstep (se 1 (by rfl) ⟨2620184, by rfl⟩ : syracuseStep 3493579 = 5240369) B5240369
theorem B2182859 : Blo 1453546 2182859 := bstep (se 1 (by rfl) ⟨1637144, by rfl⟩ : syracuseStep 2182859 = 3274289) B3274289
theorem B1453783 : Blo 1453546 1453783 := bstep (se 1 (by rfl) ⟨1090337, by rfl⟩ : syracuseStep 1453783 = 2180675) B2180675
theorem B2182871 : Blo 1453546 2182871 := bstep (se 1 (by rfl) ⟨1637153, by rfl⟩ : syracuseStep 2182871 = 3274307) B3274307
theorem B4910813 : Blo 1453546 4910813 := bstep (se 3 (by rfl) ⟨920777, by rfl⟩ : syracuseStep 4910813 = 1841555) B1841555
theorem B1453803 : Blo 1453546 1453803 := bstep (se 1 (by rfl) ⟨1090352, by rfl⟩ : syracuseStep 1453803 = 2180705) B2180705
theorem B3272435 : Blo 1453546 3272435 := bstep (se 1 (by rfl) ⟨2454326, by rfl⟩ : syracuseStep 3272435 = 4908653) B4908653
theorem B1453815 : Blo 1453546 1453815 := bstep (se 1 (by rfl) ⟨1090361, by rfl⟩ : syracuseStep 1453815 = 2180723) B2180723
theorem B1453835 : Blo 1453546 1453835 := bstep (se 1 (by rfl) ⟨1090376, by rfl⟩ : syracuseStep 1453835 = 2180753) B2180753
theorem B1453847 : Blo 1453546 1453847 := bstep (se 1 (by rfl) ⟨1090385, by rfl⟩ : syracuseStep 1453847 = 2180771) B2180771
theorem B3272471 : Blo 1453546 3272471 := bstep (se 1 (by rfl) ⟨2454353, by rfl⟩ : syracuseStep 3272471 = 4908707) B4908707
theorem B2182937 : Blo 1453546 2182937 := bstep (se 2 (by rfl) ⟨818601, by rfl⟩ : syracuseStep 2182937 = 1637203) B1637203
theorem B1453867 : Blo 1453546 1453867 := bstep (se 1 (by rfl) ⟨1090400, by rfl⟩ : syracuseStep 1453867 = 2180801) B2180801
theorem B1453879 : Blo 1453546 1453879 := bstep (se 1 (by rfl) ⟨1090409, by rfl⟩ : syracuseStep 1453879 = 2180819) B2180819
theorem B1453899 : Blo 1453546 1453899 := bstep (se 1 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 1453899 = 2180849) B2180849
theorem B1453911 : Blo 1453546 1453911 := bstep (se 1 (by rfl) ⟨1090433, by rfl⟩ : syracuseStep 1453911 = 2180867) B2180867
theorem B1453931 : Blo 1453546 1453931 := bstep (se 1 (by rfl) ⟨1090448, by rfl⟩ : syracuseStep 1453931 = 2180897) B2180897
theorem B1453943 : Blo 1453546 1453943 := bstep (se 1 (by rfl) ⟨1090457, by rfl⟩ : syracuseStep 1453943 = 2180915) B2180915
theorem B1453963 : Blo 1453546 1453963 := bstep (se 1 (by rfl) ⟨1090472, by rfl⟩ : syracuseStep 1453963 = 2180945) B2180945
theorem B2183051 : Blo 1453546 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B1453975 : Blo 1453546 1453975 := bstep (se 1 (by rfl) ⟨1090481, by rfl⟩ : syracuseStep 1453975 = 2180963) B2180963
theorem B3682199 : Blo 1453546 3682199 := bstep (se 1 (by rfl) ⟨2761649, by rfl⟩ : syracuseStep 3682199 = 5523299) B5523299
theorem B2183063 : Blo 1453546 2183063 := bstep (se 1 (by rfl) ⟨1637297, by rfl⟩ : syracuseStep 2183063 = 3274595) B3274595
theorem B1453995 : Blo 1453546 1453995 := bstep (se 1 (by rfl) ⟨1090496, by rfl⟩ : syracuseStep 1453995 = 2180993) B2180993
theorem B1454007 : Blo 1453546 1454007 := bstep (se 1 (by rfl) ⟨1090505, by rfl⟩ : syracuseStep 1454007 = 2181011) B2181011
theorem B5525441 : Blo 1453546 5525441 := bstep (se 2 (by rfl) ⟨2072040, by rfl⟩ : syracuseStep 5525441 = 4144081) B4144081
theorem B1454027 : Blo 1453546 1454027 := bstep (se 1 (by rfl) ⟨1090520, by rfl⟩ : syracuseStep 1454027 = 2181041) B2181041
theorem B3272651 : Blo 1453546 3272651 := bstep (se 1 (by rfl) ⟨2454488, by rfl⟩ : syracuseStep 3272651 = 4908977) B4908977
theorem B1552343 : Blo 1453546 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1454039 : Blo 1453546 1454039 := bstep (se 1 (by rfl) ⟨1090529, by rfl⟩ : syracuseStep 1454039 = 2181059) B2181059
theorem B3493849 : Blo 1453546 3493849 := bstep (se 2 (by rfl) ⟨1310193, by rfl⟩ : syracuseStep 3493849 = 2620387) B2620387
theorem B2183129 : Blo 1453546 2183129 := bstep (se 2 (by rfl) ⟨818673, by rfl⟩ : syracuseStep 2183129 = 1637347) B1637347
theorem B1454059 : Blo 1453546 1454059 := bstep (se 1 (by rfl) ⟨1090544, by rfl⟩ : syracuseStep 1454059 = 2181089) B2181089
theorem B1454071 : Blo 1453546 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B3272705 : Blo 1453546 3272705 := bstep (se 2 (by rfl) ⟨1227264, by rfl⟩ : syracuseStep 3272705 = 2454529) B2454529
theorem B1454091 : Blo 1453546 1454091 := bstep (se 1 (by rfl) ⟨1090568, by rfl⟩ : syracuseStep 1454091 = 2181137) B2181137
theorem B1454103 : Blo 1453546 1454103 := bstep (se 1 (by rfl) ⟨1090577, by rfl⟩ : syracuseStep 1454103 = 2181155) B2181155
theorem B1454123 : Blo 1453546 1454123 := bstep (se 1 (by rfl) ⟨1090592, by rfl⟩ : syracuseStep 1454123 = 2181185) B2181185
theorem B1454135 : Blo 1453546 1454135 := bstep (se 1 (by rfl) ⟨1090601, by rfl⟩ : syracuseStep 1454135 = 2181203) B2181203
theorem B1454155 : Blo 1453546 1454155 := bstep (se 1 (by rfl) ⟨1090616, by rfl⟩ : syracuseStep 1454155 = 2181233) B2181233
theorem B2183243 : Blo 1453546 2183243 := bstep (se 1 (by rfl) ⟨1637432, by rfl⟩ : syracuseStep 2183243 = 3274865) B3274865
theorem B2453591 : Blo 1453546 2453591 := bstep (se 1 (by rfl) ⟨1840193, by rfl⟩ : syracuseStep 2453591 = 3680387) B3680387
theorem B1454167 : Blo 1453546 1454167 := bstep (se 1 (by rfl) ⟨1090625, by rfl⟩ : syracuseStep 1454167 = 2181251) B2181251
theorem B2183255 : Blo 1453546 2183255 := bstep (se 1 (by rfl) ⟨1637441, by rfl⟩ : syracuseStep 2183255 = 3274883) B3274883
theorem B1454187 : Blo 1453546 1454187 := bstep (se 1 (by rfl) ⟨1090640, by rfl⟩ : syracuseStep 1454187 = 2181281) B2181281
theorem B1454199 : Blo 1453546 1454199 := bstep (se 1 (by rfl) ⟨1090649, by rfl⟩ : syracuseStep 1454199 = 2181299) B2181299
theorem B1454219 : Blo 1453546 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B1454231 : Blo 1453546 1454231 := bstep (se 1 (by rfl) ⟨1090673, by rfl⟩ : syracuseStep 1454231 = 2181347) B2181347
theorem B1454251 : Blo 1453546 1454251 := bstep (se 1 (by rfl) ⟨1090688, by rfl⟩ : syracuseStep 1454251 = 2181377) B2181377
theorem B1454263 : Blo 1453546 1454263 := bstep (se 1 (by rfl) ⟨1090697, by rfl⟩ : syracuseStep 1454263 = 2181395) B2181395
theorem B1454283 : Blo 1453546 1454283 := bstep (se 1 (by rfl) ⟨1090712, by rfl⟩ : syracuseStep 1454283 = 2181425) B2181425
theorem B2453719 : Blo 1453546 2453719 := bstep (se 1 (by rfl) ⟨1840289, by rfl⟩ : syracuseStep 2453719 = 3680579) B3680579
theorem B1454295 : Blo 1453546 1454295 := bstep (se 1 (by rfl) ⟨1090721, by rfl⟩ : syracuseStep 1454295 = 2181443) B2181443
theorem B3272921 : Blo 1453546 3272921 := bstep (se 2 (by rfl) ⟨1227345, by rfl⟩ : syracuseStep 3272921 = 2454691) B2454691
theorem B4485341 : Blo 1453546 4485341 := bstep (se 3 (by rfl) ⟨841001, by rfl⟩ : syracuseStep 4485341 = 1682003) B1682003
theorem B1454315 : Blo 1453546 1454315 := bstep (se 1 (by rfl) ⟨1090736, by rfl⟩ : syracuseStep 1454315 = 2181473) B2181473
theorem B1454327 : Blo 1453546 1454327 := bstep (se 1 (by rfl) ⟨1090745, by rfl⟩ : syracuseStep 1454327 = 2181491) B2181491
theorem B1454347 : Blo 1453546 1454347 := bstep (se 1 (by rfl) ⟨1090760, by rfl⟩ : syracuseStep 1454347 = 2181521) B2181521
theorem B1454359 : Blo 1453546 1454359 := bstep (se 1 (by rfl) ⟨1090769, by rfl⟩ : syracuseStep 1454359 = 2181539) B2181539
theorem B1454379 : Blo 1453546 1454379 := bstep (se 1 (by rfl) ⟨1090784, by rfl⟩ : syracuseStep 1454379 = 2181569) B2181569
theorem B3494195 : Blo 1453546 3494195 := bstep (se 1 (by rfl) ⟨2620646, by rfl⟩ : syracuseStep 3494195 = 5241293) B5241293
theorem B3273011 : Blo 1453546 3273011 := bstep (se 1 (by rfl) ⟨2454758, by rfl⟩ : syracuseStep 3273011 = 4909517) B4909517
theorem B1454391 : Blo 1453546 1454391 := bstep (se 1 (by rfl) ⟨1090793, by rfl⟩ : syracuseStep 1454391 = 2181587) B2181587
theorem B1454411 : Blo 1453546 1454411 := bstep (se 1 (by rfl) ⟨1090808, by rfl⟩ : syracuseStep 1454411 = 2181617) B2181617
theorem B1454423 : Blo 1453546 1454423 := bstep (se 1 (by rfl) ⟨1090817, by rfl⟩ : syracuseStep 1454423 = 2181635) B2181635
theorem B3273047 : Blo 1453546 3273047 := bstep (se 1 (by rfl) ⟨2454785, by rfl⟩ : syracuseStep 3273047 = 4909571) B4909571
theorem B1454443 : Blo 1453546 1454443 := bstep (se 1 (by rfl) ⟨1090832, by rfl⟩ : syracuseStep 1454443 = 2181665) B2181665
theorem B59683189 : Blo 1453546 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B1454455 : Blo 1453546 1454455 := bstep (se 1 (by rfl) ⟨1090841, by rfl⟩ : syracuseStep 1454455 = 2181683) B2181683
theorem B1454475 : Blo 1453546 1454475 := bstep (se 1 (by rfl) ⟨1090856, by rfl⟩ : syracuseStep 1454475 = 2181713) B2181713
theorem B1454487 : Blo 1453546 1454487 := bstep (se 1 (by rfl) ⟨1090865, by rfl⟩ : syracuseStep 1454487 = 2181731) B2181731
theorem B1454507 : Blo 1453546 1454507 := bstep (se 1 (by rfl) ⟨1090880, by rfl⟩ : syracuseStep 1454507 = 2181761) B2181761
theorem B1454519 : Blo 1453546 1454519 := bstep (se 1 (by rfl) ⟨1090889, by rfl⟩ : syracuseStep 1454519 = 2181779) B2181779
theorem B1454539 : Blo 1453546 1454539 := bstep (se 1 (by rfl) ⟨1090904, by rfl⟩ : syracuseStep 1454539 = 2181809) B2181809
theorem B1454551 : Blo 1453546 1454551 := bstep (se 1 (by rfl) ⟨1090913, by rfl⟩ : syracuseStep 1454551 = 2181827) B2181827
theorem B1454571 : Blo 1453546 1454571 := bstep (se 1 (by rfl) ⟨1090928, by rfl⟩ : syracuseStep 1454571 = 2181857) B2181857
theorem B1454583 : Blo 1453546 1454583 := bstep (se 1 (by rfl) ⟨1090937, by rfl⟩ : syracuseStep 1454583 = 2181875) B2181875
theorem B1454603 : Blo 1453546 1454603 := bstep (se 1 (by rfl) ⟨1090952, by rfl⟩ : syracuseStep 1454603 = 2181905) B2181905
theorem B3273227 : Blo 1453546 3273227 := bstep (se 1 (by rfl) ⟨2454920, by rfl⟩ : syracuseStep 3273227 = 4909841) B4909841
theorem B1454615 : Blo 1453546 1454615 := bstep (se 1 (by rfl) ⟨1090961, by rfl⟩ : syracuseStep 1454615 = 2181923) B2181923
theorem B1454635 : Blo 1453546 1454635 := bstep (se 1 (by rfl) ⟨1090976, by rfl⟩ : syracuseStep 1454635 = 2181953) B2181953
theorem B3682867 : Blo 1453546 3682867 := bstep (se 1 (by rfl) ⟨2762150, by rfl⟩ : syracuseStep 3682867 = 5524301) B5524301
theorem B1454647 : Blo 1453546 1454647 := bstep (se 1 (by rfl) ⟨1090985, by rfl⟩ : syracuseStep 1454647 = 2181971) B2181971
theorem B3494465 : Blo 1453546 3494465 := bstep (se 2 (by rfl) ⟨1310424, by rfl⟩ : syracuseStep 3494465 = 2620849) B2620849
theorem B3273281 : Blo 1453546 3273281 := bstep (se 2 (by rfl) ⟨1227480, by rfl⟩ : syracuseStep 3273281 = 2454961) B2454961
theorem B1454667 : Blo 1453546 1454667 := bstep (se 1 (by rfl) ⟨1091000, by rfl⟩ : syracuseStep 1454667 = 2182001) B2182001
theorem B1454679 : Blo 1453546 1454679 := bstep (se 1 (by rfl) ⟨1091009, by rfl⟩ : syracuseStep 1454679 = 2182019) B2182019
theorem B7361117 : Blo 1453546 7361117 := bstep (se 3 (by rfl) ⟨1380209, by rfl⟩ : syracuseStep 7361117 = 2760419) B2760419
theorem B1454699 : Blo 1453546 1454699 := bstep (se 1 (by rfl) ⟨1091024, by rfl⟩ : syracuseStep 1454699 = 2182049) B2182049
theorem B1454711 : Blo 1453546 1454711 := bstep (se 1 (by rfl) ⟨1091033, by rfl⟩ : syracuseStep 1454711 = 2182067) B2182067
theorem B1454731 : Blo 1453546 1454731 := bstep (se 1 (by rfl) ⟨1091048, by rfl⟩ : syracuseStep 1454731 = 2182097) B2182097
theorem B1454743 : Blo 1453546 1454743 := bstep (se 1 (by rfl) ⟨1091057, by rfl⟩ : syracuseStep 1454743 = 2182115) B2182115
theorem B1454763 : Blo 1453546 1454763 := bstep (se 1 (by rfl) ⟨1091072, by rfl⟩ : syracuseStep 1454763 = 2182145) B2182145
theorem B10629809 : Blo 1453546 10629809 := bstep (se 2 (by rfl) ⟨3986178, by rfl⟩ : syracuseStep 10629809 = 7972357) B7972357
theorem B1454775 : Blo 1453546 1454775 := bstep (se 1 (by rfl) ⟨1091081, by rfl⟩ : syracuseStep 1454775 = 2182163) B2182163
theorem B3683009 : Blo 1453546 3683009 := bstep (se 2 (by rfl) ⟨1381128, by rfl⟩ : syracuseStep 3683009 = 2762257) B2762257
theorem B1454795 : Blo 1453546 1454795 := bstep (se 1 (by rfl) ⟨1091096, by rfl⟩ : syracuseStep 1454795 = 2182193) B2182193
theorem B1454807 : Blo 1453546 1454807 := bstep (se 1 (by rfl) ⟨1091105, by rfl⟩ : syracuseStep 1454807 = 2182211) B2182211
theorem B1454827 : Blo 1453546 1454827 := bstep (se 1 (by rfl) ⟨1091120, by rfl⟩ : syracuseStep 1454827 = 2182241) B2182241
theorem B1454839 : Blo 1453546 1454839 := bstep (se 1 (by rfl) ⟨1091129, by rfl⟩ : syracuseStep 1454839 = 2182259) B2182259
theorem B10490629 : Blo 1453546 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B1454859 : Blo 1453546 1454859 := bstep (se 1 (by rfl) ⟨1091144, by rfl⟩ : syracuseStep 1454859 = 2182289) B2182289
theorem B1454871 : Blo 1453546 1454871 := bstep (se 1 (by rfl) ⟨1091153, by rfl⟩ : syracuseStep 1454871 = 2182307) B2182307
theorem B3273497 : Blo 1453546 3273497 := bstep (se 2 (by rfl) ⟨1227561, by rfl⟩ : syracuseStep 3273497 = 2455123) B2455123
theorem B1454891 : Blo 1453546 1454891 := bstep (se 1 (by rfl) ⟨1091168, by rfl⟩ : syracuseStep 1454891 = 2182337) B2182337
theorem B1454903 : Blo 1453546 1454903 := bstep (se 1 (by rfl) ⟨1091177, by rfl⟩ : syracuseStep 1454903 = 2182355) B2182355
theorem B2454347 : Blo 1453546 2454347 := bstep (se 1 (by rfl) ⟨1840760, by rfl⟩ : syracuseStep 2454347 = 3681521) B3681521
theorem B1454923 : Blo 1453546 1454923 := bstep (se 1 (by rfl) ⟨1091192, by rfl⟩ : syracuseStep 1454923 = 2182385) B2182385
theorem B4911947 : Blo 1453546 4911947 := bstep (se 1 (by rfl) ⟨3683960, by rfl⟩ : syracuseStep 4911947 = 7367921) B7367921
theorem B1454935 : Blo 1453546 1454935 := bstep (se 1 (by rfl) ⟨1091201, by rfl⟩ : syracuseStep 1454935 = 2182403) B2182403
theorem B9950045 : Blo 1453546 9950045 := bstep (se 3 (by rfl) ⟨1865633, by rfl⟩ : syracuseStep 9950045 = 3731267) B3731267
theorem B1454955 : Blo 1453546 1454955 := bstep (se 1 (by rfl) ⟨1091216, by rfl⟩ : syracuseStep 1454955 = 2182433) B2182433
theorem B3273587 : Blo 1453546 3273587 := bstep (se 1 (by rfl) ⟨2455190, by rfl⟩ : syracuseStep 3273587 = 4910381) B4910381
theorem B1454967 : Blo 1453546 1454967 := bstep (se 1 (by rfl) ⟨1091225, by rfl⟩ : syracuseStep 1454967 = 2182451) B2182451
theorem B1454987 : Blo 1453546 1454987 := bstep (se 1 (by rfl) ⟨1091240, by rfl⟩ : syracuseStep 1454987 = 2182481) B2182481
theorem B3273623 : Blo 1453546 3273623 := bstep (se 1 (by rfl) ⟨2455217, by rfl⟩ : syracuseStep 3273623 = 4910435) B4910435
theorem B1454999 : Blo 1453546 1454999 := bstep (se 1 (by rfl) ⟨1091249, by rfl⟩ : syracuseStep 1454999 = 2182499) B2182499
theorem B1455019 : Blo 1453546 1455019 := bstep (se 1 (by rfl) ⟨1091264, by rfl⟩ : syracuseStep 1455019 = 2182529) B2182529
theorem B22385585 : Blo 1453546 22385585 := bstep (se 2 (by rfl) ⟨8394594, by rfl⟩ : syracuseStep 22385585 = 16789189) B16789189
theorem B16577459 : Blo 1453546 16577459 := bstep (se 1 (by rfl) ⟨12433094, by rfl⟩ : syracuseStep 16577459 = 24866189) B24866189
theorem B1455031 : Blo 1453546 1455031 := bstep (se 1 (by rfl) ⟨1091273, by rfl⟩ : syracuseStep 1455031 = 2182547) B2182547
theorem B2454475 : Blo 1453546 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B1455051 : Blo 1453546 1455051 := bstep (se 1 (by rfl) ⟨1091288, by rfl⟩ : syracuseStep 1455051 = 2182577) B2182577
theorem B1840087 : Blo 1453546 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B1455063 : Blo 1453546 1455063 := bstep (se 1 (by rfl) ⟨1091297, by rfl⟩ : syracuseStep 1455063 = 2182595) B2182595
theorem B1455083 : Blo 1453546 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B1455095 : Blo 1453546 1455095 := bstep (se 1 (by rfl) ⟨1091321, by rfl⟩ : syracuseStep 1455095 = 2182643) B2182643
theorem B1455115 : Blo 1453546 1455115 := bstep (se 1 (by rfl) ⟨1091336, by rfl⟩ : syracuseStep 1455115 = 2182673) B2182673
theorem B1455127 : Blo 1453546 1455127 := bstep (se 1 (by rfl) ⟨1091345, by rfl⟩ : syracuseStep 1455127 = 2182691) B2182691
theorem B1455147 : Blo 1453546 1455147 := bstep (se 1 (by rfl) ⟨1091360, by rfl⟩ : syracuseStep 1455147 = 2182721) B2182721
theorem B1455159 : Blo 1453546 1455159 := bstep (se 1 (by rfl) ⟨1091369, by rfl⟩ : syracuseStep 1455159 = 2182739) B2182739
theorem B1635403 : Blo 1453546 1635403 := bstep (se 1 (by rfl) ⟨1226552, by rfl⟩ : syracuseStep 1635403 = 2453105) B2453105
theorem B3273803 : Blo 1453546 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B1455179 : Blo 1453546 1455179 := bstep (se 1 (by rfl) ⟨1091384, by rfl⟩ : syracuseStep 1455179 = 2182769) B2182769
theorem B1455191 : Blo 1453546 1455191 := bstep (se 1 (by rfl) ⟨1091393, by rfl⟩ : syracuseStep 1455191 = 2182787) B2182787
theorem B2454617 : Blo 1453546 2454617 := bstep (se 2 (by rfl) ⟨920481, by rfl⟩ : syracuseStep 2454617 = 1840963) B1840963
theorem B4912217 : Blo 1453546 4912217 := bstep (se 2 (by rfl) ⟨1842081, by rfl⟩ : syracuseStep 4912217 = 3684163) B3684163
theorem B1455211 : Blo 1453546 1455211 := bstep (se 1 (by rfl) ⟨1091408, by rfl⟩ : syracuseStep 1455211 = 2182817) B2182817
theorem B1455223 : Blo 1453546 1455223 := bstep (se 1 (by rfl) ⟨1091417, by rfl⟩ : syracuseStep 1455223 = 2182835) B2182835
theorem B3273857 : Blo 1453546 3273857 := bstep (se 2 (by rfl) ⟨1227696, by rfl⟩ : syracuseStep 3273857 = 2455393) B2455393
theorem B1455243 : Blo 1453546 1455243 := bstep (se 1 (by rfl) ⟨1091432, by rfl⟩ : syracuseStep 1455243 = 2182865) B2182865
theorem B1455255 : Blo 1453546 1455255 := bstep (se 1 (by rfl) ⟨1091441, by rfl⟩ : syracuseStep 1455255 = 2182883) B2182883
theorem B1455275 : Blo 1453546 1455275 := bstep (se 1 (by rfl) ⟨1091456, by rfl⟩ : syracuseStep 1455275 = 2182913) B2182913
theorem B1635511 : Blo 1453546 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B1455287 : Blo 1453546 1455287 := bstep (se 1 (by rfl) ⟨1091465, by rfl⟩ : syracuseStep 1455287 = 2182931) B2182931
theorem B5240011 : Blo 1453546 5240011 := bstep (se 1 (by rfl) ⟨3930008, by rfl⟩ : syracuseStep 5240011 = 7860017) B7860017
theorem B1455307 : Blo 1453546 1455307 := bstep (se 1 (by rfl) ⟨1091480, by rfl⟩ : syracuseStep 1455307 = 2182961) B2182961
theorem B1455319 : Blo 1453546 1455319 := bstep (se 1 (by rfl) ⟨1091489, by rfl⟩ : syracuseStep 1455319 = 2182979) B2182979
theorem B2454745 : Blo 1453546 2454745 := bstep (se 2 (by rfl) ⟨920529, by rfl⟩ : syracuseStep 2454745 = 1841059) B1841059
theorem B1455339 : Blo 1453546 1455339 := bstep (se 1 (by rfl) ⟨1091504, by rfl⟩ : syracuseStep 1455339 = 2183009) B2183009
theorem B1455351 : Blo 1453546 1455351 := bstep (se 1 (by rfl) ⟨1091513, by rfl⟩ : syracuseStep 1455351 = 2183027) B2183027
theorem B17683717 : Blo 1453546 17683717 := bstep (se 4 (by rfl) ⟨1657848, by rfl⟩ : syracuseStep 17683717 = 3315697) B3315697
theorem B1455371 : Blo 1453546 1455371 := bstep (se 1 (by rfl) ⟨1091528, by rfl⟩ : syracuseStep 1455371 = 2183057) B2183057
theorem B9319697 : Blo 1453546 9319697 := bstep (se 2 (by rfl) ⟨3494886, by rfl⟩ : syracuseStep 9319697 = 6989773) B6989773
theorem B1455383 : Blo 1453546 1455383 := bstep (se 1 (by rfl) ⟨1091537, by rfl⟩ : syracuseStep 1455383 = 2183075) B2183075
theorem B1455403 : Blo 1453546 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B11048237 : Blo 1453546 11048237 := bstep (se 3 (by rfl) ⟨2071544, by rfl⟩ : syracuseStep 11048237 = 4143089) B4143089
theorem B1455415 : Blo 1453546 1455415 := bstep (se 1 (by rfl) ⟨1091561, by rfl⟩ : syracuseStep 1455415 = 2183123) B2183123
theorem B3495233 : Blo 1453546 3495233 := bstep (se 2 (by rfl) ⟨1310712, by rfl⟩ : syracuseStep 3495233 = 2621425) B2621425
theorem B1455435 : Blo 1453546 1455435 := bstep (se 1 (by rfl) ⟨1091576, by rfl⟩ : syracuseStep 1455435 = 2183153) B2183153
theorem B1455447 : Blo 1453546 1455447 := bstep (se 1 (by rfl) ⟨1091585, by rfl⟩ : syracuseStep 1455447 = 2183171) B2183171
theorem B3274073 : Blo 1453546 3274073 := bstep (se 2 (by rfl) ⟨1227777, by rfl⟩ : syracuseStep 3274073 = 2455555) B2455555
theorem B1635691 : Blo 1453546 1635691 := bstep (se 1 (by rfl) ⟨1226768, by rfl⟩ : syracuseStep 1635691 = 2453537) B2453537
theorem B1455467 : Blo 1453546 1455467 := bstep (se 1 (by rfl) ⟨1091600, by rfl⟩ : syracuseStep 1455467 = 2183201) B2183201
theorem B1455479 : Blo 1453546 1455479 := bstep (se 1 (by rfl) ⟨1091609, by rfl⟩ : syracuseStep 1455479 = 2183219) B2183219
theorem B1455499 : Blo 1453546 1455499 := bstep (se 1 (by rfl) ⟨1091624, by rfl⟩ : syracuseStep 1455499 = 2183249) B2183249
theorem B1455511 : Blo 1453546 1455511 := bstep (se 1 (by rfl) ⟨1091633, by rfl⟩ : syracuseStep 1455511 = 2183267) B2183267
theorem B1455531 : Blo 1453546 1455531 := bstep (se 1 (by rfl) ⟨1091648, by rfl⟩ : syracuseStep 1455531 = 2183297) B2183297
theorem B3274163 : Blo 1453546 3274163 := bstep (se 1 (by rfl) ⟨2455622, by rfl⟩ : syracuseStep 3274163 = 4911245) B4911245
theorem B1455543 : Blo 1453546 1455543 := bstep (se 1 (by rfl) ⟨1091657, by rfl⟩ : syracuseStep 1455543 = 2183315) B2183315
theorem B1635799 : Blo 1453546 1635799 := bstep (se 1 (by rfl) ⟨1226849, by rfl⟩ : syracuseStep 1635799 = 2453699) B2453699
theorem B3274199 : Blo 1453546 3274199 := bstep (se 1 (by rfl) ⟨2455649, by rfl⟩ : syracuseStep 3274199 = 4911299) B4911299
theorem B5240285 : Blo 1453546 5240285 := bstep (se 3 (by rfl) ⟨982553, by rfl⟩ : syracuseStep 5240285 = 1965107) B1965107
theorem B2070041 : Blo 1453546 2070041 := bstep (se 2 (by rfl) ⟨776265, by rfl⟩ : syracuseStep 2070041 = 1552531) B1552531
theorem B8279617 : Blo 1453546 8279617 := bstep (se 2 (by rfl) ⟨3104856, by rfl⟩ : syracuseStep 8279617 = 6209713) B6209713
theorem B4142657 : Blo 1453546 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B6387265 : Blo 1453546 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B2799193 : Blo 1453546 2799193 := bstep (se 2 (by rfl) ⟨1049697, by rfl⟩ : syracuseStep 2799193 = 2099395) B2099395
theorem B25204355 : Blo 1453546 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B2070155 : Blo 1453546 2070155 := bstep (se 1 (by rfl) ⟨1552616, by rfl⟩ : syracuseStep 2070155 = 3105233) B3105233
theorem B1635979 : Blo 1453546 1635979 := bstep (se 1 (by rfl) ⟨1226984, by rfl⟩ : syracuseStep 1635979 = 2453969) B2453969
theorem B3274379 : Blo 1453546 3274379 := bstep (se 1 (by rfl) ⟨2455784, by rfl⟩ : syracuseStep 3274379 = 4911569) B4911569
theorem B4142771 : Blo 1453546 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B1554103 : Blo 1453546 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B3274433 : Blo 1453546 3274433 := bstep (se 2 (by rfl) ⟨1227912, by rfl⟩ : syracuseStep 3274433 = 2455825) B2455825
theorem B11040461 : Blo 1453546 11040461 := bstep (se 3 (by rfl) ⟨2070086, by rfl⟩ : syracuseStep 11040461 = 4140173) B4140173
theorem B1636087 : Blo 1453546 1636087 := bstep (se 1 (by rfl) ⟨1227065, by rfl⟩ : syracuseStep 1636087 = 2454131) B2454131
theorem B1840907 : Blo 1453546 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B2488087 : Blo 1453546 2488087 := bstep (se 1 (by rfl) ⟨1866065, by rfl⟩ : syracuseStep 2488087 = 3732131) B3732131
theorem B2455319 : Blo 1453546 2455319 := bstep (se 1 (by rfl) ⟨1841489, by rfl⟩ : syracuseStep 2455319 = 3682979) B3682979
theorem B2455447 : Blo 1453546 2455447 := bstep (se 1 (by rfl) ⟨1841585, by rfl⟩ : syracuseStep 2455447 = 3683171) B3683171
theorem B6215575 : Blo 1453546 6215575 := bstep (se 1 (by rfl) ⟨4661681, by rfl⟩ : syracuseStep 6215575 = 9323363) B9323363
theorem B3274649 : Blo 1453546 3274649 := bstep (se 2 (by rfl) ⟨1227993, by rfl⟩ : syracuseStep 3274649 = 2455987) B2455987
theorem B1636267 : Blo 1453546 1636267 := bstep (se 1 (by rfl) ⟨1227200, by rfl⟩ : syracuseStep 1636267 = 2454401) B2454401
theorem B3684275 : Blo 1453546 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B3274739 : Blo 1453546 3274739 := bstep (se 1 (by rfl) ⟨2456054, by rfl⟩ : syracuseStep 3274739 = 4912109) B4912109
theorem B1636375 : Blo 1453546 1636375 := bstep (se 1 (by rfl) ⟨1227281, by rfl⟩ : syracuseStep 1636375 = 2454563) B2454563
theorem B3274775 : Blo 1453546 3274775 := bstep (se 1 (by rfl) ⟨2456081, by rfl⟩ : syracuseStep 3274775 = 4912163) B4912163
theorem B6993965 : Blo 1453546 6993965 := bstep (se 3 (by rfl) ⟨1311368, by rfl⟩ : syracuseStep 6993965 = 2622737) B2622737
theorem B5519411 : Blo 1453546 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B2070679 : Blo 1453546 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B11040947 : Blo 1453546 11040947 := bstep (se 1 (by rfl) ⟨8280710, by rfl⟩ : syracuseStep 11040947 = 16561421) B16561421
theorem B1636555 : Blo 1453546 1636555 := bstep (se 1 (by rfl) ⟨1227416, by rfl⟩ : syracuseStep 1636555 = 2454833) B2454833
theorem B3274955 : Blo 1453546 3274955 := bstep (se 1 (by rfl) ⟨2456216, by rfl⟩ : syracuseStep 3274955 = 4912433) B4912433
theorem B2619659 : Blo 1453546 2619659 := bstep (se 1 (by rfl) ⟨1964744, by rfl⟩ : syracuseStep 2619659 = 3929489) B3929489
theorem B2488601 : Blo 1453546 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B1636663 : Blo 1453546 1636663 := bstep (se 1 (by rfl) ⟨1227497, by rfl⟩ : syracuseStep 1636663 = 2454995) B2454995
theorem B16578917 : Blo 1453546 16578917 := bstep (se 4 (by rfl) ⟨1554273, by rfl⟩ : syracuseStep 16578917 = 3108547) B3108547
theorem B11188631 : Blo 1453546 11188631 := bstep (se 1 (by rfl) ⟨8391473, by rfl⟩ : syracuseStep 11188631 = 16782947) B16782947
theorem B1841611 : Blo 1453546 1841611 := bstep (se 1 (by rfl) ⟨1381208, by rfl⟩ : syracuseStep 1841611 = 2762417) B2762417
theorem B1636843 : Blo 1453546 1636843 := bstep (se 1 (by rfl) ⟨1227632, by rfl⟩ : syracuseStep 1636843 = 2455265) B2455265
theorem B2456075 : Blo 1453546 2456075 := bstep (se 1 (by rfl) ⟨1842056, by rfl⟩ : syracuseStep 2456075 = 3684113) B3684113
theorem B3734081 : Blo 1453546 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B12433985 : Blo 1453546 12433985 := bstep (se 2 (by rfl) ⟨4662744, by rfl⟩ : syracuseStep 12433985 = 9325489) B9325489
theorem B24853067 : Blo 1453546 24853067 := bstep (se 1 (by rfl) ⟨18639800, by rfl⟩ : syracuseStep 24853067 = 37279601) B37279601
theorem B1636951 : Blo 1453546 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B2456203 : Blo 1453546 2456203 := bstep (se 1 (by rfl) ⟨1842152, by rfl⟩ : syracuseStep 2456203 = 3684305) B3684305
theorem B7363223 : Blo 1453546 7363223 := bstep (se 1 (by rfl) ⟨5522417, by rfl⟩ : syracuseStep 7363223 = 11044835) B11044835
theorem B1841879 : Blo 1453546 1841879 := bstep (se 1 (by rfl) ⟨1381409, by rfl⟩ : syracuseStep 1841879 = 2762819) B2762819
theorem B1637131 : Blo 1453546 1637131 := bstep (se 1 (by rfl) ⟨1227848, by rfl⟩ : syracuseStep 1637131 = 2455697) B2455697
theorem B1637239 : Blo 1453546 1637239 := bstep (se 1 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 1637239 = 2455859) B2455859
theorem B2071499 : Blo 1453546 2071499 := bstep (se 1 (by rfl) ⟨1553624, by rfl⟩ : syracuseStep 2071499 = 3107249) B3107249
theorem B4906007 : Blo 1453546 4906007 := bstep (se 1 (by rfl) ⟨3679505, by rfl⟩ : syracuseStep 4906007 = 7359011) B7359011
theorem B4660247 : Blo 1453546 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B1637419 : Blo 1453546 1637419 := bstep (se 1 (by rfl) ⟨1228064, by rfl⟩ : syracuseStep 1637419 = 2456129) B2456129
theorem B1473611 : Blo 1453546 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B2759987 : Blo 1453546 2759987 := bstep (se 1 (by rfl) ⟨2069990, by rfl⟩ : syracuseStep 2759987 = 4139981) B4139981
theorem B5520899 : Blo 1453546 5520899 := bstep (se 1 (by rfl) ⟨4140674, by rfl⟩ : syracuseStep 5520899 = 8281349) B8281349
theorem B4906547 : Blo 1453546 4906547 := bstep (se 1 (by rfl) ⟨3679910, by rfl⟩ : syracuseStep 4906547 = 7359821) B7359821
theorem B6209099 : Blo 1453546 6209099 := bstep (se 1 (by rfl) ⟨4656824, by rfl⟩ : syracuseStep 6209099 = 9313649) B9313649
theorem B11042405 : Blo 1453546 11042405 := bstep (se 4 (by rfl) ⟨1035225, by rfl⟩ : syracuseStep 11042405 = 2070451) B2070451
theorem B2621107 : Blo 1453546 2621107 := bstep (se 1 (by rfl) ⟨1965830, by rfl⟩ : syracuseStep 2621107 = 3931661) B3931661
theorem B23584517 : Blo 1453546 23584517 := bstep (se 4 (by rfl) ⟨2211048, by rfl⟩ : syracuseStep 23584517 = 4422097) B4422097
theorem B2760473 : Blo 1453546 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B4906817 : Blo 1453546 4906817 := bstep (se 2 (by rfl) ⟨1840056, by rfl⟩ : syracuseStep 4906817 = 3680113) B3680113
theorem B98320229 : Blo 1453546 98320229 := bstep (se 4 (by rfl) ⟨9217521, by rfl⟩ : syracuseStep 98320229 = 18435043) B18435043
theorem B11198359 : Blo 1453546 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B5521355 : Blo 1453546 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B5898269 : Blo 1453546 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B9314365 : Blo 1453546 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B2760905 : Blo 1453546 2760905 := bstep (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) B2070679
theorem B2621641 : Blo 1453546 2621641 := bstep (se 2 (by rfl) ⟨983115, by rfl⟩ : syracuseStep 2621641 = 1966231) B1966231
theorem B11796769 : Blo 1453546 11796769 := bstep (se 2 (by rfl) ⟨4423788, by rfl⟩ : syracuseStep 11796769 = 8847577) B8847577
theorem B5898529 : Blo 1453546 5898529 := bstep (se 2 (by rfl) ⟨2211948, by rfl⟩ : syracuseStep 5898529 = 4423897) B4423897
theorem B4907411 : Blo 1453546 4907411 := bstep (se 1 (by rfl) ⟨3680558, by rfl⟩ : syracuseStep 4907411 = 7361117) B7361117
theorem B7086539 : Blo 1453546 7086539 := bstep (se 1 (by rfl) ⟨5314904, by rfl⟩ : syracuseStep 7086539 = 10629809) B10629809
theorem B79577585 : Blo 1453546 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B11960909 : Blo 1453546 11960909 := bstep (se 3 (by rfl) ⟨2242670, by rfl⟩ : syracuseStep 11960909 = 4485341) B4485341
theorem B5522039 : Blo 1453546 5522039 := bstep (se 1 (by rfl) ⟨4141529, by rfl⟩ : syracuseStep 5522039 = 8283059) B8283059
theorem B11051639 : Blo 1453546 11051639 := bstep (se 1 (by rfl) ⟨8288729, by rfl⟩ : syracuseStep 11051639 = 16577459) B16577459
theorem B3932807 : Blo 1453546 3932807 := bstep (se 1 (by rfl) ⟨2949605, by rfl⟩ : syracuseStep 3932807 = 5899211) B5899211
theorem B6636269 : Blo 1453546 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B5243629 : Blo 1453546 5243629 := bstep (se 3 (by rfl) ⟨983180, by rfl⟩ : syracuseStep 5243629 = 1966361) B1966361
theorem B7365491 : Blo 1453546 7365491 := bstep (se 1 (by rfl) ⟨5524118, by rfl⟩ : syracuseStep 7365491 = 11048237) B11048237
theorem B2876345 : Blo 1453546 2876345 := bstep (se 2 (by rfl) ⟨1078629, by rfl⟩ : syracuseStep 2876345 = 2157259) B2157259
theorem B11043863 : Blo 1453546 11043863 := bstep (se 1 (by rfl) ⟨8282897, by rfl⟩ : syracuseStep 11043863 = 16565795) B16565795
theorem B3933217 : Blo 1453546 3933217 := bstep (se 2 (by rfl) ⟨1474956, by rfl⟩ : syracuseStep 3933217 = 2949913) B2949913
theorem B2761771 : Blo 1453546 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B16802903 : Blo 1453546 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B2761847 : Blo 1453546 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B2180411 : Blo 1453546 2180411 := bstep (se 1 (by rfl) ⟨1635308, by rfl⟩ : syracuseStep 2180411 = 3270617) B3270617
theorem B7365977 : Blo 1453546 7365977 := bstep (se 2 (by rfl) ⟨2762241, by rfl⟩ : syracuseStep 7365977 = 5524483) B5524483
theorem B4662643 : Blo 1453546 4662643 := bstep (se 1 (by rfl) ⟨3496982, by rfl⟩ : syracuseStep 4662643 = 6993965) B6993965
theorem B2180471 : Blo 1453546 2180471 := bstep (se 1 (by rfl) ⟨1635353, by rfl⟩ : syracuseStep 2180471 = 3270707) B3270707
theorem B3679607 : Blo 1453546 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B2180495 : Blo 1453546 2180495 := bstep (se 1 (by rfl) ⟨1635371, by rfl⟩ : syracuseStep 2180495 = 3270743) B3270743
theorem B2180537 : Blo 1453546 2180537 := bstep (se 2 (by rfl) ⟨817701, by rfl⟩ : syracuseStep 2180537 = 1635403) B1635403
theorem B2180615 : Blo 1453546 2180615 := bstep (se 1 (by rfl) ⟨1635461, by rfl⟩ : syracuseStep 2180615 = 3270923) B3270923
theorem B1574407 : Blo 1453546 1574407 := bstep (se 1 (by rfl) ⟨1180805, by rfl⟩ : syracuseStep 1574407 = 2361611) B2361611
theorem B2180651 : Blo 1453546 2180651 := bstep (se 1 (by rfl) ⟨1635488, by rfl⟩ : syracuseStep 2180651 = 3270977) B3270977
theorem B5523011 : Blo 1453546 5523011 := bstep (se 1 (by rfl) ⟨4142258, by rfl⟩ : syracuseStep 5523011 = 8284517) B8284517
theorem B11052611 : Blo 1453546 11052611 := bstep (se 1 (by rfl) ⟨8289458, by rfl⟩ : syracuseStep 11052611 = 16578917) B16578917
theorem B2180681 : Blo 1453546 2180681 := bstep (se 2 (by rfl) ⟨817755, by rfl⟩ : syracuseStep 2180681 = 1635511) B1635511
theorem B23578289 : Blo 1453546 23578289 := bstep (se 2 (by rfl) ⟨8841858, by rfl⟩ : syracuseStep 23578289 = 17683717) B17683717
theorem B18630323 : Blo 1453546 18630323 := bstep (se 1 (by rfl) ⟨13972742, by rfl⟩ : syracuseStep 18630323 = 27945485) B27945485
theorem B2180795 : Blo 1453546 2180795 := bstep (se 1 (by rfl) ⟨1635596, by rfl⟩ : syracuseStep 2180795 = 3271193) B3271193
theorem B2180855 : Blo 1453546 2180855 := bstep (se 1 (by rfl) ⟨1635641, by rfl⟩ : syracuseStep 2180855 = 3271283) B3271283
theorem B13977359 : Blo 1453546 13977359 := bstep (se 1 (by rfl) ⟨10483019, by rfl⟩ : syracuseStep 13977359 = 20966039) B20966039
theorem B2180879 : Blo 1453546 2180879 := bstep (se 1 (by rfl) ⟨1635659, by rfl⟩ : syracuseStep 2180879 = 3271319) B3271319
theorem B4908815 : Blo 1453546 4908815 := bstep (se 1 (by rfl) ⟨3681611, by rfl⟩ : syracuseStep 4908815 = 7363223) B7363223
theorem B2180921 : Blo 1453546 2180921 := bstep (se 2 (by rfl) ⟨817845, by rfl⟩ : syracuseStep 2180921 = 1635691) B1635691
theorem B2180999 : Blo 1453546 2180999 := bstep (se 1 (by rfl) ⟨1635749, by rfl⟩ : syracuseStep 2180999 = 3271499) B3271499
theorem B6211475 : Blo 1453546 6211475 := bstep (se 1 (by rfl) ⟨4658606, by rfl⟩ : syracuseStep 6211475 = 9317213) B9317213
theorem B2181035 : Blo 1453546 2181035 := bstep (se 1 (by rfl) ⟨1635776, by rfl⟩ : syracuseStep 2181035 = 3271553) B3271553
theorem B2181065 : Blo 1453546 2181065 := bstep (se 2 (by rfl) ⟨817899, by rfl⟩ : syracuseStep 2181065 = 1635799) B1635799
theorem B3270671 : Blo 1453546 3270671 := bstep (se 1 (by rfl) ⟨2453003, by rfl⟩ : syracuseStep 3270671 = 4906007) B4906007
theorem B3106831 : Blo 1453546 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B4909085 : Blo 1453546 4909085 := bstep (se 3 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 4909085 = 1840907) B1840907
theorem B3270689 : Blo 1453546 3270689 := bstep (se 2 (by rfl) ⟨1226508, by rfl⟩ : syracuseStep 3270689 = 2453017) B2453017
theorem B2181179 : Blo 1453546 2181179 := bstep (se 1 (by rfl) ⟨1635884, by rfl⟩ : syracuseStep 2181179 = 3271769) B3271769
theorem B11798615 : Blo 1453546 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B2181239 : Blo 1453546 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B2181263 : Blo 1453546 2181263 := bstep (se 1 (by rfl) ⟨1635947, by rfl⟩ : syracuseStep 2181263 = 3271895) B3271895
theorem B238749869 : Blo 1453546 238749869 := bstep (se 3 (by rfl) ⟨44765600, by rfl⟩ : syracuseStep 238749869 = 89531201) B89531201
theorem B2181305 : Blo 1453546 2181305 := bstep (se 2 (by rfl) ⟨817989, by rfl⟩ : syracuseStep 2181305 = 1635979) B1635979
theorem B2181383 : Blo 1453546 2181383 := bstep (se 1 (by rfl) ⟨1636037, by rfl⟩ : syracuseStep 2181383 = 3272075) B3272075
theorem B2181419 : Blo 1453546 2181419 := bstep (se 1 (by rfl) ⟨1636064, by rfl⟩ : syracuseStep 2181419 = 3272129) B3272129
theorem B2181449 : Blo 1453546 2181449 := bstep (se 2 (by rfl) ⟨818043, by rfl⟩ : syracuseStep 2181449 = 1636087) B1636087
theorem B3680599 : Blo 1453546 3680599 := bstep (se 1 (by rfl) ⟨2760449, by rfl⟩ : syracuseStep 3680599 = 5520899) B5520899
theorem B3271031 : Blo 1453546 3271031 := bstep (se 1 (by rfl) ⟨2453273, by rfl⟩ : syracuseStep 3271031 = 4906547) B4906547
theorem B4139399 : Blo 1453546 4139399 := bstep (se 1 (by rfl) ⟨3104549, by rfl⟩ : syracuseStep 4139399 = 6209099) B6209099
theorem B2181563 : Blo 1453546 2181563 := bstep (se 1 (by rfl) ⟨1636172, by rfl⟩ : syracuseStep 2181563 = 3272345) B3272345
theorem B2181623 : Blo 1453546 2181623 := bstep (se 1 (by rfl) ⟨1636217, by rfl⟩ : syracuseStep 2181623 = 3272435) B3272435
theorem B15723011 : Blo 1453546 15723011 := bstep (se 1 (by rfl) ⟨11792258, by rfl⟩ : syracuseStep 15723011 = 23584517) B23584517
theorem B2181647 : Blo 1453546 2181647 := bstep (se 1 (by rfl) ⟨1636235, by rfl⟩ : syracuseStep 2181647 = 3272471) B3272471
theorem B5523997 : Blo 1453546 5523997 := bstep (se 3 (by rfl) ⟨1035749, by rfl⟩ : syracuseStep 5523997 = 2071499) B2071499
theorem B3271211 : Blo 1453546 3271211 := bstep (se 1 (by rfl) ⟨2453408, by rfl⟩ : syracuseStep 3271211 = 4906817) B4906817
theorem B2181689 : Blo 1453546 2181689 := bstep (se 2 (by rfl) ⟨818133, by rfl⟩ : syracuseStep 2181689 = 1636267) B1636267
theorem B4139581 : Blo 1453546 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B65546819 : Blo 1453546 65546819 := bstep (se 1 (by rfl) ⟨49160114, by rfl⟩ : syracuseStep 65546819 = 98320229) B98320229
theorem B3680903 : Blo 1453546 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B2181767 : Blo 1453546 2181767 := bstep (se 1 (by rfl) ⟨1636325, by rfl⟩ : syracuseStep 2181767 = 3272651) B3272651
theorem B2181803 : Blo 1453546 2181803 := bstep (se 1 (by rfl) ⟨1636352, by rfl⟩ : syracuseStep 2181803 = 3272705) B3272705
theorem B2181833 : Blo 1453546 2181833 := bstep (se 2 (by rfl) ⟨818187, by rfl⟩ : syracuseStep 2181833 = 1636375) B1636375
theorem B3681035 : Blo 1453546 3681035 := bstep (se 1 (by rfl) ⟨2760776, by rfl⟩ : syracuseStep 3681035 = 5521553) B5521553
theorem B2181947 : Blo 1453546 2181947 := bstep (se 1 (by rfl) ⟨1636460, by rfl⟩ : syracuseStep 2181947 = 3272921) B3272921
theorem B33565529 : Blo 1453546 33565529 := bstep (se 2 (by rfl) ⟨12587073, by rfl⟩ : syracuseStep 33565529 = 25174147) B25174147
theorem B2329463 : Blo 1453546 2329463 := bstep (se 1 (by rfl) ⟨1747097, by rfl⟩ : syracuseStep 2329463 = 3494195) B3494195
theorem B2182007 : Blo 1453546 2182007 := bstep (se 1 (by rfl) ⟨1636505, by rfl⟩ : syracuseStep 2182007 = 3273011) B3273011
theorem B2182031 : Blo 1453546 2182031 := bstep (se 1 (by rfl) ⟨1636523, by rfl⟩ : syracuseStep 2182031 = 3273047) B3273047
theorem B4139923 : Blo 1453546 4139923 := bstep (se 1 (by rfl) ⟨3104942, by rfl⟩ : syracuseStep 4139923 = 6209885) B6209885
theorem B3271571 : Blo 1453546 3271571 := bstep (se 1 (by rfl) ⟨2453678, by rfl⟩ : syracuseStep 3271571 = 4907357) B4907357
theorem B2182073 : Blo 1453546 2182073 := bstep (se 2 (by rfl) ⟨818277, by rfl⟩ : syracuseStep 2182073 = 1636555) B1636555
theorem B3271625 : Blo 1453546 3271625 := bstep (se 2 (by rfl) ⟨1226859, by rfl⟩ : syracuseStep 3271625 = 2453719) B2453719
theorem B2182151 : Blo 1453546 2182151 := bstep (se 1 (by rfl) ⟨1636613, by rfl⟩ : syracuseStep 2182151 = 3273227) B3273227
theorem B2329643 : Blo 1453546 2329643 := bstep (se 1 (by rfl) ⟨1747232, by rfl⟩ : syracuseStep 2329643 = 3494465) B3494465
theorem B2182187 : Blo 1453546 2182187 := bstep (se 1 (by rfl) ⟨1636640, by rfl⟩ : syracuseStep 2182187 = 3273281) B3273281
theorem B2182217 : Blo 1453546 2182217 := bstep (se 2 (by rfl) ⟨818331, by rfl⟩ : syracuseStep 2182217 = 1636663) B1636663
theorem B2182331 : Blo 1453546 2182331 := bstep (se 1 (by rfl) ⟨1636748, by rfl⟩ : syracuseStep 2182331 = 3273497) B3273497
theorem B1748155 : Blo 1453546 1748155 := bstep (se 1 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 1748155 = 2622233) B2622233
theorem B10628297 : Blo 1453546 10628297 := bstep (se 2 (by rfl) ⟨3985611, by rfl⟩ : syracuseStep 10628297 = 7971223) B7971223
theorem B2182391 : Blo 1453546 2182391 := bstep (se 1 (by rfl) ⟨1636793, by rfl⟩ : syracuseStep 2182391 = 3273587) B3273587
theorem B3681551 : Blo 1453546 3681551 := bstep (se 1 (by rfl) ⟨2761163, by rfl⟩ : syracuseStep 3681551 = 5522327) B5522327
theorem B2182415 : Blo 1453546 2182415 := bstep (se 1 (by rfl) ⟨1636811, by rfl⟩ : syracuseStep 2182415 = 3273623) B3273623
theorem B2182457 : Blo 1453546 2182457 := bstep (se 2 (by rfl) ⟨818421, by rfl⟩ : syracuseStep 2182457 = 1636843) B1636843
theorem B2182535 : Blo 1453546 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B3681683 : Blo 1453546 3681683 := bstep (se 1 (by rfl) ⟨2761262, by rfl⟩ : syracuseStep 3681683 = 5522525) B5522525
theorem B7368083 : Blo 1453546 7368083 := bstep (se 1 (by rfl) ⟨5526062, by rfl⟩ : syracuseStep 7368083 = 11052125) B11052125
theorem B4910489 : Blo 1453546 4910489 := bstep (se 2 (by rfl) ⟨1841433, by rfl⟩ : syracuseStep 4910489 = 3682867) B3682867
theorem B2182571 : Blo 1453546 2182571 := bstep (se 1 (by rfl) ⟨1636928, by rfl⟩ : syracuseStep 2182571 = 3273857) B3273857
theorem B2182601 : Blo 1453546 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B1453575 : Blo 1453546 1453575 := bstep (se 1 (by rfl) ⟨1090181, by rfl⟩ : syracuseStep 1453575 = 2180363) B2180363
theorem B6213131 : Blo 1453546 6213131 := bstep (se 1 (by rfl) ⟨4659848, by rfl⟩ : syracuseStep 6213131 = 9319697) B9319697
theorem B1453583 : Blo 1453546 1453583 := bstep (se 1 (by rfl) ⟨1090187, by rfl⟩ : syracuseStep 1453583 = 2180375) B2180375
theorem B2330155 : Blo 1453546 2330155 := bstep (se 1 (by rfl) ⟨1747616, by rfl⟩ : syracuseStep 2330155 = 3495233) B3495233
theorem B1453627 : Blo 1453546 1453627 := bstep (se 1 (by rfl) ⟨1090220, by rfl⟩ : syracuseStep 1453627 = 2180441) B2180441
theorem B2453051 : Blo 1453546 2453051 := bstep (se 1 (by rfl) ⟨1839788, by rfl⟩ : syracuseStep 2453051 = 3679577) B3679577
theorem B2182715 : Blo 1453546 2182715 := bstep (se 1 (by rfl) ⟨1637036, by rfl⟩ : syracuseStep 2182715 = 3274073) B3274073
theorem B11791939 : Blo 1453546 11791939 := bstep (se 1 (by rfl) ⟨8843954, by rfl⟩ : syracuseStep 11791939 = 17687909) B17687909
theorem B20967011 : Blo 1453546 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B2182775 : Blo 1453546 2182775 := bstep (se 1 (by rfl) ⟨1637081, by rfl⟩ : syracuseStep 2182775 = 3274163) B3274163
theorem B1453703 : Blo 1453546 1453703 := bstep (se 1 (by rfl) ⟨1090277, by rfl⟩ : syracuseStep 1453703 = 2180555) B2180555
theorem B3272327 : Blo 1453546 3272327 := bstep (se 1 (by rfl) ⟨2454245, by rfl⟩ : syracuseStep 3272327 = 4908491) B4908491
theorem B1453711 : Blo 1453546 1453711 := bstep (se 1 (by rfl) ⟨1090283, by rfl⟩ : syracuseStep 1453711 = 2180567) B2180567
theorem B2182799 : Blo 1453546 2182799 := bstep (se 1 (by rfl) ⟨1637099, by rfl⟩ : syracuseStep 2182799 = 3274199) B3274199
theorem B3493523 : Blo 1453546 3493523 := bstep (se 1 (by rfl) ⟨2620142, by rfl⟩ : syracuseStep 3493523 = 5240285) B5240285
theorem B13987505 : Blo 1453546 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B2182841 : Blo 1453546 2182841 := bstep (se 2 (by rfl) ⟨818565, by rfl⟩ : syracuseStep 2182841 = 1637131) B1637131
theorem B1453755 : Blo 1453546 1453755 := bstep (se 1 (by rfl) ⟨1090316, by rfl⟩ : syracuseStep 1453755 = 2180633) B2180633
theorem B1453831 : Blo 1453546 1453831 := bstep (se 1 (by rfl) ⟨1090373, by rfl⟩ : syracuseStep 1453831 = 2180747) B2180747
theorem B2182919 : Blo 1453546 2182919 := bstep (se 1 (by rfl) ⟨1637189, by rfl⟩ : syracuseStep 2182919 = 3274379) B3274379
theorem B4140811 : Blo 1453546 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B1453839 : Blo 1453546 1453839 := bstep (se 1 (by rfl) ⟨1090379, by rfl⟩ : syracuseStep 1453839 = 2180759) B2180759
theorem B2182955 : Blo 1453546 2182955 := bstep (se 1 (by rfl) ⟨1637216, by rfl⟩ : syracuseStep 2182955 = 3274433) B3274433
theorem B7360307 : Blo 1453546 7360307 := bstep (se 1 (by rfl) ⟨5520230, by rfl⟩ : syracuseStep 7360307 = 11040461) B11040461
theorem B1453883 : Blo 1453546 1453883 := bstep (se 1 (by rfl) ⟨1090412, by rfl⟩ : syracuseStep 1453883 = 2180825) B2180825
theorem B3272507 : Blo 1453546 3272507 := bstep (se 1 (by rfl) ⟨2454380, by rfl⟩ : syracuseStep 3272507 = 4908761) B4908761
theorem B2182985 : Blo 1453546 2182985 := bstep (se 2 (by rfl) ⟨818619, by rfl⟩ : syracuseStep 2182985 = 1637239) B1637239
theorem B1453959 : Blo 1453546 1453959 := bstep (se 1 (by rfl) ⟨1090469, by rfl⟩ : syracuseStep 1453959 = 2180939) B2180939
theorem B1453967 : Blo 1453546 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B3272633 : Blo 1453546 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B1454011 : Blo 1453546 1454011 := bstep (se 1 (by rfl) ⟨1090508, by rfl⟩ : syracuseStep 1454011 = 2181017) B2181017
theorem B2183099 : Blo 1453546 2183099 := bstep (se 1 (by rfl) ⟨1637324, by rfl⟩ : syracuseStep 2183099 = 3274649) B3274649
theorem B2453449 : Blo 1453546 2453449 := bstep (se 2 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 2453449 = 1840087) B1840087
theorem B2183159 : Blo 1453546 2183159 := bstep (se 1 (by rfl) ⟨1637369, by rfl⟩ : syracuseStep 2183159 = 3274739) B3274739
theorem B1454087 : Blo 1453546 1454087 := bstep (se 1 (by rfl) ⟨1090565, by rfl⟩ : syracuseStep 1454087 = 2181131) B2181131
theorem B1454095 : Blo 1453546 1454095 := bstep (se 1 (by rfl) ⟨1090571, by rfl⟩ : syracuseStep 1454095 = 2181143) B2181143
theorem B2183183 : Blo 1453546 2183183 := bstep (se 1 (by rfl) ⟨1637387, by rfl⟩ : syracuseStep 2183183 = 3274775) B3274775
theorem B2183225 : Blo 1453546 2183225 := bstep (se 2 (by rfl) ⟨818709, by rfl⟩ : syracuseStep 2183225 = 1637419) B1637419
theorem B1454139 : Blo 1453546 1454139 := bstep (se 1 (by rfl) ⟨1090604, by rfl⟩ : syracuseStep 1454139 = 2181209) B2181209
theorem B4911191 : Blo 1453546 4911191 := bstep (se 1 (by rfl) ⟨3683393, by rfl⟩ : syracuseStep 4911191 = 7366787) B7366787
theorem B7360631 : Blo 1453546 7360631 := bstep (se 1 (by rfl) ⟨5520473, by rfl⟩ : syracuseStep 7360631 = 11040947) B11040947
theorem B1454215 : Blo 1453546 1454215 := bstep (se 1 (by rfl) ⟨1090661, by rfl⟩ : syracuseStep 1454215 = 2181323) B2181323
theorem B2183303 : Blo 1453546 2183303 := bstep (se 1 (by rfl) ⟨1637477, by rfl⟩ : syracuseStep 2183303 = 3274955) B3274955
theorem B1454223 : Blo 1453546 1454223 := bstep (se 1 (by rfl) ⟨1090667, by rfl⟩ : syracuseStep 1454223 = 2181335) B2181335
theorem B3780761 : Blo 1453546 3780761 := bstep (se 2 (by rfl) ⟨1417785, by rfl⟩ : syracuseStep 3780761 = 2835571) B2835571
theorem B1454267 : Blo 1453546 1454267 := bstep (se 1 (by rfl) ⟨1090700, by rfl⟩ : syracuseStep 1454267 = 2181401) B2181401
theorem B4141313 : Blo 1453546 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B1454343 : Blo 1453546 1454343 := bstep (se 1 (by rfl) ⟨1090757, by rfl⟩ : syracuseStep 1454343 = 2181515) B2181515
theorem B7459087 : Blo 1453546 7459087 := bstep (se 1 (by rfl) ⟨5594315, by rfl⟩ : syracuseStep 7459087 = 11188631) B11188631
theorem B1454351 : Blo 1453546 1454351 := bstep (se 1 (by rfl) ⟨1090763, by rfl⟩ : syracuseStep 1454351 = 2181527) B2181527
theorem B3272975 : Blo 1453546 3272975 := bstep (se 1 (by rfl) ⟨2454731, by rfl⟩ : syracuseStep 3272975 = 4909463) B4909463
theorem B3272993 : Blo 1453546 3272993 := bstep (se 2 (by rfl) ⟨1227372, by rfl⟩ : syracuseStep 3272993 = 2454745) B2454745
theorem B1454395 : Blo 1453546 1454395 := bstep (se 1 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 1454395 = 2181593) B2181593
theorem B1454471 : Blo 1453546 1454471 := bstep (se 1 (by rfl) ⟨1090853, by rfl⟩ : syracuseStep 1454471 = 2181707) B2181707
theorem B16568711 : Blo 1453546 16568711 := bstep (se 1 (by rfl) ⟨12426533, by rfl⟩ : syracuseStep 16568711 = 24853067) B24853067
theorem B1454479 : Blo 1453546 1454479 := bstep (se 1 (by rfl) ⟨1090859, by rfl⟩ : syracuseStep 1454479 = 2181719) B2181719
theorem B2331065 : Blo 1453546 2331065 := bstep (se 2 (by rfl) ⟨874149, by rfl⟩ : syracuseStep 2331065 = 1748299) B1748299
theorem B1454523 : Blo 1453546 1454523 := bstep (se 1 (by rfl) ⟨1090892, by rfl⟩ : syracuseStep 1454523 = 2181785) B2181785
theorem B3682817 : Blo 1453546 3682817 := bstep (se 2 (by rfl) ⟨1381056, by rfl⟩ : syracuseStep 3682817 = 2762113) B2762113
theorem B1454599 : Blo 1453546 1454599 := bstep (se 1 (by rfl) ⟨1090949, by rfl⟩ : syracuseStep 1454599 = 2181899) B2181899
theorem B1454607 : Blo 1453546 1454607 := bstep (se 1 (by rfl) ⟨1090955, by rfl⟩ : syracuseStep 1454607 = 2181911) B2181911
theorem B1454651 : Blo 1453546 1454651 := bstep (se 1 (by rfl) ⟨1090988, by rfl⟩ : syracuseStep 1454651 = 2181977) B2181977
theorem B4911677 : Blo 1453546 4911677 := bstep (se 3 (by rfl) ⟨920939, by rfl⟩ : syracuseStep 4911677 = 1841879) B1841879
theorem B4141655 : Blo 1453546 4141655 := bstep (se 1 (by rfl) ⟨3106241, by rfl⟩ : syracuseStep 4141655 = 6212483) B6212483
theorem B3273335 : Blo 1453546 3273335 := bstep (se 1 (by rfl) ⟨2455001, by rfl⟩ : syracuseStep 3273335 = 4910003) B4910003
theorem B2454151 : Blo 1453546 2454151 := bstep (se 1 (by rfl) ⟨1840613, by rfl⟩ : syracuseStep 2454151 = 3681227) B3681227
theorem B1454727 : Blo 1453546 1454727 := bstep (se 1 (by rfl) ⟨1091045, by rfl⟩ : syracuseStep 1454727 = 2182091) B2182091
theorem B1454735 : Blo 1453546 1454735 := bstep (se 1 (by rfl) ⟨1091051, by rfl⟩ : syracuseStep 1454735 = 2182103) B2182103
theorem B1454779 : Blo 1453546 1454779 := bstep (se 1 (by rfl) ⟨1091084, by rfl⟩ : syracuseStep 1454779 = 2182169) B2182169
theorem B11039489 : Blo 1453546 11039489 := bstep (se 2 (by rfl) ⟨4139808, by rfl⟩ : syracuseStep 11039489 = 8279617) B8279617
theorem B8516353 : Blo 1453546 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B1454855 : Blo 1453546 1454855 := bstep (se 1 (by rfl) ⟨1091141, by rfl⟩ : syracuseStep 1454855 = 2182283) B2182283
theorem B1454863 : Blo 1453546 1454863 := bstep (se 1 (by rfl) ⟨1091147, by rfl⟩ : syracuseStep 1454863 = 2182295) B2182295
theorem B3732257 : Blo 1453546 3732257 := bstep (se 2 (by rfl) ⟨1399596, by rfl⟩ : syracuseStep 3732257 = 2799193) B2799193
theorem B3273515 : Blo 1453546 3273515 := bstep (se 1 (by rfl) ⟨2455136, by rfl⟩ : syracuseStep 3273515 = 4910273) B4910273
theorem B1454907 : Blo 1453546 1454907 := bstep (se 1 (by rfl) ⟨1091180, by rfl⟩ : syracuseStep 1454907 = 2182361) B2182361
theorem B1839991 : Blo 1453546 1839991 := bstep (se 1 (by rfl) ⟨1379993, by rfl⟩ : syracuseStep 1839991 = 2759987) B2759987
theorem B3683191 : Blo 1453546 3683191 := bstep (se 1 (by rfl) ⟨2762393, by rfl⟩ : syracuseStep 3683191 = 5524787) B5524787
theorem B1454983 : Blo 1453546 1454983 := bstep (se 1 (by rfl) ⟨1091237, by rfl⟩ : syracuseStep 1454983 = 2182475) B2182475
theorem B1454991 : Blo 1453546 1454991 := bstep (se 1 (by rfl) ⟨1091243, by rfl⟩ : syracuseStep 1454991 = 2182487) B2182487
theorem B3494809 : Blo 1453546 3494809 := bstep (se 2 (by rfl) ⟨1310553, by rfl⟩ : syracuseStep 3494809 = 2621107) B2621107
theorem B13988771 : Blo 1453546 13988771 := bstep (se 1 (by rfl) ⟨10491578, by rfl⟩ : syracuseStep 13988771 = 20983157) B20983157
theorem B4658105 : Blo 1453546 4658105 := bstep (se 2 (by rfl) ⟨1746789, by rfl⟩ : syracuseStep 4658105 = 3493579) B3493579
theorem B1635259 : Blo 1453546 1635259 := bstep (se 1 (by rfl) ⟨1226444, by rfl⟩ : syracuseStep 1635259 = 2452889) B2452889
theorem B1455035 : Blo 1453546 1455035 := bstep (se 1 (by rfl) ⟨1091276, by rfl⟩ : syracuseStep 1455035 = 2182553) B2182553
theorem B1455111 : Blo 1453546 1455111 := bstep (se 1 (by rfl) ⟨1091333, by rfl⟩ : syracuseStep 1455111 = 2182667) B2182667
theorem B1455119 : Blo 1453546 1455119 := bstep (se 1 (by rfl) ⟨1091339, by rfl⟩ : syracuseStep 1455119 = 2182679) B2182679
theorem B1455163 : Blo 1453546 1455163 := bstep (se 1 (by rfl) ⟨1091372, by rfl⟩ : syracuseStep 1455163 = 2182745) B2182745
theorem B7361603 : Blo 1453546 7361603 := bstep (se 1 (by rfl) ⟨5521202, by rfl⟩ : syracuseStep 7361603 = 11042405) B11042405
theorem B5895287 : Blo 1453546 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B1455239 : Blo 1453546 1455239 := bstep (se 1 (by rfl) ⟨1091429, by rfl⟩ : syracuseStep 1455239 = 2182859) B2182859
theorem B1455247 : Blo 1453546 1455247 := bstep (se 1 (by rfl) ⟨1091435, by rfl⟩ : syracuseStep 1455247 = 2182871) B2182871
theorem B3273875 : Blo 1453546 3273875 := bstep (se 1 (by rfl) ⟨2455406, by rfl⟩ : syracuseStep 3273875 = 4910813) B4910813
theorem B1840315 : Blo 1453546 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B1455291 : Blo 1453546 1455291 := bstep (se 1 (by rfl) ⟨1091468, by rfl⟩ : syracuseStep 1455291 = 2182937) B2182937
theorem B14931145 : Blo 1453546 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B3273929 : Blo 1453546 3273929 := bstep (se 2 (by rfl) ⟨1227723, by rfl⟩ : syracuseStep 3273929 = 2455447) B2455447
theorem B8287433 : Blo 1453546 8287433 := bstep (se 2 (by rfl) ⟨3107787, by rfl⟩ : syracuseStep 8287433 = 6215575) B6215575
theorem B15733997 : Blo 1453546 15733997 := bstep (se 3 (by rfl) ⟨2950124, by rfl⟩ : syracuseStep 15733997 = 5900249) B5900249
theorem B1455367 : Blo 1453546 1455367 := bstep (se 1 (by rfl) ⟨1091525, by rfl⟩ : syracuseStep 1455367 = 2183051) B2183051
theorem B2454799 : Blo 1453546 2454799 := bstep (se 1 (by rfl) ⟨1841099, by rfl⟩ : syracuseStep 2454799 = 3682199) B3682199
theorem B1455375 : Blo 1453546 1455375 := bstep (se 1 (by rfl) ⟨1091531, by rfl⟩ : syracuseStep 1455375 = 2183063) B2183063
theorem B4658465 : Blo 1453546 4658465 := bstep (se 2 (by rfl) ⟨1746924, by rfl⟩ : syracuseStep 4658465 = 3493849) B3493849
theorem B3683627 : Blo 1453546 3683627 := bstep (se 1 (by rfl) ⟨2762720, by rfl⟩ : syracuseStep 3683627 = 5525441) B5525441
theorem B1455419 : Blo 1453546 1455419 := bstep (se 1 (by rfl) ⟨1091564, by rfl⟩ : syracuseStep 1455419 = 2183129) B2183129
theorem B7361927 : Blo 1453546 7361927 := bstep (se 1 (by rfl) ⟨5521445, by rfl⟩ : syracuseStep 7361927 = 11042891) B11042891
theorem B1455495 : Blo 1453546 1455495 := bstep (se 1 (by rfl) ⟨1091621, by rfl⟩ : syracuseStep 1455495 = 2183243) B2183243
theorem B1635727 : Blo 1453546 1635727 := bstep (se 1 (by rfl) ⟨1226795, by rfl⟩ : syracuseStep 1635727 = 2453591) B2453591
theorem B1455503 : Blo 1453546 1455503 := bstep (se 1 (by rfl) ⟨1091627, by rfl⟩ : syracuseStep 1455503 = 2183255) B2183255
theorem B3315215 : Blo 1453546 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B3929629 : Blo 1453546 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B5519137 : Blo 1453546 5519137 := bstep (se 2 (by rfl) ⟨2069676, by rfl⟩ : syracuseStep 5519137 = 4139353) B4139353
theorem B2455339 : Blo 1453546 2455339 := bstep (se 1 (by rfl) ⟨1841504, by rfl⟩ : syracuseStep 2455339 = 3683009) B3683009
theorem B1636231 : Blo 1453546 1636231 := bstep (se 1 (by rfl) ⟨1227173, by rfl⟩ : syracuseStep 1636231 = 2454347) B2454347
theorem B3274631 : Blo 1453546 3274631 := bstep (se 1 (by rfl) ⟨2455973, by rfl⟩ : syracuseStep 3274631 = 4911947) B4911947
theorem B2455481 : Blo 1453546 2455481 := bstep (se 2 (by rfl) ⟨920805, by rfl⟩ : syracuseStep 2455481 = 1841611) B1841611
theorem B14923723 : Blo 1453546 14923723 := bstep (se 1 (by rfl) ⟨11192792, by rfl⟩ : syracuseStep 14923723 = 22385585) B22385585
theorem B6985757 : Blo 1453546 6985757 := bstep (se 3 (by rfl) ⟨1309829, by rfl⟩ : syracuseStep 6985757 = 2619659) B2619659
theorem B1636411 : Blo 1453546 1636411 := bstep (se 1 (by rfl) ⟨1227308, by rfl⟩ : syracuseStep 1636411 = 2454617) B2454617
theorem B3274811 : Blo 1453546 3274811 := bstep (se 1 (by rfl) ⟨2456108, by rfl⟩ : syracuseStep 3274811 = 4912217) B4912217
theorem B1841287 : Blo 1453546 1841287 := bstep (se 1 (by rfl) ⟨1380965, by rfl⟩ : syracuseStep 1841287 = 2761931) B2761931
theorem B17701037 : Blo 1453546 17701037 := bstep (se 3 (by rfl) ⟨3318944, by rfl⟩ : syracuseStep 17701037 = 6637889) B6637889
theorem B3274937 : Blo 1453546 3274937 := bstep (se 2 (by rfl) ⟨1228101, by rfl⟩ : syracuseStep 3274937 = 2456203) B2456203
theorem B106133813 : Blo 1453546 106133813 := bstep (se 5 (by rfl) ⟨4975022, by rfl⟩ : syracuseStep 106133813 = 9950045) B9950045
theorem B4143545 : Blo 1453546 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B2071055 : Blo 1453546 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B1636879 : Blo 1453546 1636879 := bstep (se 1 (by rfl) ⟨1227659, by rfl⟩ : syracuseStep 1636879 = 2455319) B2455319
theorem B3496463 : Blo 1453546 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B1841707 : Blo 1453546 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B2456183 : Blo 1453546 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B5520109 : Blo 1453546 5520109 := bstep (se 3 (by rfl) ⟨1035020, by rfl⟩ : syracuseStep 5520109 = 2070041) B2070041
theorem B1841935 : Blo 1453546 1841935 := bstep (se 1 (by rfl) ⟨1381451, by rfl⟩ : syracuseStep 1841935 = 2762903) B2762903
theorem B221076373 : Blo 1453546 221076373 := bstep (se 6 (by rfl) ⟨5181477, by rfl⟩ : syracuseStep 221076373 = 10362955) B10362955
theorem B6986681 : Blo 1453546 6986681 := bstep (se 2 (by rfl) ⟨2620005, by rfl⟩ : syracuseStep 6986681 = 5240011) B5240011
theorem B1637383 : Blo 1453546 1637383 := bstep (se 1 (by rfl) ⟨1228037, by rfl⟩ : syracuseStep 1637383 = 2456075) B2456075
theorem B5520413 : Blo 1453546 5520413 := bstep (se 3 (by rfl) ⟨1035077, by rfl⟩ : syracuseStep 5520413 = 2070155) B2070155
theorem B2489387 : Blo 1453546 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B8289323 : Blo 1453546 8289323 := bstep (se 1 (by rfl) ⟨6216992, by rfl⟩ : syracuseStep 8289323 = 12433985) B12433985
theorem B2759827 : Blo 1453546 2759827 := bstep (se 1 (by rfl) ⟨2069870, by rfl⟩ : syracuseStep 2759827 = 4139741) B4139741
theorem B14933281 : Blo 1453546 14933281 := bstep (se 2 (by rfl) ⟨5599980, by rfl⟩ : syracuseStep 14933281 = 11199961) B11199961
theorem B1596731 : Blo 1453546 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B18636317 : Blo 1453546 18636317 := bstep (se 3 (by rfl) ⟨3494309, by rfl⟩ : syracuseStep 18636317 = 6988619) B6988619
theorem B2072137 : Blo 1453546 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B2072251 : Blo 1453546 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B3317449 : Blo 1453546 3317449 := bstep (se 2 (by rfl) ⟨1244043, by rfl⟩ : syracuseStep 3317449 = 2488087) B2488087
theorem B94330777 : Blo 1453546 94330777 := bstep (se 2 (by rfl) ⟨35374041, by rfl⟩ : syracuseStep 94330777 = 70748083) B70748083
theorem B15728717 : Blo 1453546 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B4907087 : Blo 1453546 4907087 := bstep (se 1 (by rfl) ⟨3680315, by rfl⟩ : syracuseStep 4907087 = 7360631) B7360631
theorem B12419153 : Blo 1453546 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B2760875 : Blo 1453546 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B53051723 : Blo 1453546 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B9945449 : Blo 1453546 9945449 := bstep (se 2 (by rfl) ⟨3729543, by rfl⟩ : syracuseStep 9945449 = 7459087) B7459087
theorem B15729025 : Blo 1453546 15729025 := bstep (se 2 (by rfl) ⟨5898384, by rfl⟩ : syracuseStep 15729025 = 11796769) B11796769
theorem B7864705 : Blo 1453546 7864705 := bstep (se 2 (by rfl) ⟨2949264, by rfl⟩ : syracuseStep 7864705 = 5898529) B5898529
theorem B2761103 : Blo 1453546 2761103 := bstep (se 1 (by rfl) ⟨2070827, by rfl⟩ : syracuseStep 2761103 = 4141655) B4141655
theorem B4907465 : Blo 1453546 4907465 := bstep (se 2 (by rfl) ⟨1840299, by rfl⟩ : syracuseStep 4907465 = 3680599) B3680599
theorem B4424179 : Blo 1453546 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B7365329 : Blo 1453546 7365329 := bstep (se 2 (by rfl) ⟨2761998, by rfl⟩ : syracuseStep 7365329 = 5523997) B5523997
theorem B4907735 : Blo 1453546 4907735 := bstep (se 1 (by rfl) ⟨3680801, by rfl⟩ : syracuseStep 4907735 = 7361603) B7361603
theorem B3105643 : Blo 1453546 3105643 := bstep (se 1 (by rfl) ⟨2329232, by rfl⟩ : syracuseStep 3105643 = 4658465) B4658465
theorem B4907951 : Blo 1453546 4907951 := bstep (se 1 (by rfl) ⟨3680963, by rfl⟩ : syracuseStep 4907951 = 7361927) B7361927
theorem B11355137 : Blo 1453546 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B12420215 : Blo 1453546 12420215 := bstep (se 1 (by rfl) ⟨9315161, by rfl⟩ : syracuseStep 12420215 = 18630323) B18630323
theorem B2180345 : Blo 1453546 2180345 := bstep (se 2 (by rfl) ⟨817629, by rfl⟩ : syracuseStep 2180345 = 1635259) B1635259
theorem B2180447 : Blo 1453546 2180447 := bstep (se 1 (by rfl) ⟨1635335, by rfl⟩ : syracuseStep 2180447 = 3270671) B3270671
theorem B2180459 : Blo 1453546 2180459 := bstep (se 1 (by rfl) ⟨1635344, by rfl⟩ : syracuseStep 2180459 = 3270689) B3270689
theorem B8840573 : Blo 1453546 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B5522813 : Blo 1453546 5522813 := bstep (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) B2071055
theorem B7865743 : Blo 1453546 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B3679769 : Blo 1453546 3679769 := bstep (se 2 (by rfl) ⟨1379913, by rfl⟩ : syracuseStep 3679769 = 2759827) B2759827
theorem B70755875 : Blo 1453546 70755875 := bstep (se 1 (by rfl) ⟨53066906, by rfl⟩ : syracuseStep 70755875 = 106133813) B106133813
theorem B2180687 : Blo 1453546 2180687 := bstep (se 1 (by rfl) ⟨1635515, by rfl⟩ : syracuseStep 2180687 = 3271031) B3271031
theorem B19908193 : Blo 1453546 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B2762363 : Blo 1453546 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B10487485 : Blo 1453546 10487485 := bstep (se 3 (by rfl) ⟨1966403, by rfl⟩ : syracuseStep 10487485 = 3932807) B3932807
theorem B2180807 : Blo 1453546 2180807 := bstep (se 1 (by rfl) ⟨1635605, by rfl⟩ : syracuseStep 2180807 = 3271211) B3271211
theorem B43697879 : Blo 1453546 43697879 := bstep (se 1 (by rfl) ⟨32773409, by rfl⟩ : syracuseStep 43697879 = 65546819) B65546819
theorem B2180969 : Blo 1453546 2180969 := bstep (se 2 (by rfl) ⟨817863, by rfl⟩ : syracuseStep 2180969 = 1635727) B1635727
theorem B30681013 : Blo 1453546 30681013 := bstep (se 5 (by rfl) ⟨1438172, by rfl⟩ : syracuseStep 30681013 = 2876345) B2876345
theorem B2181047 : Blo 1453546 2181047 := bstep (se 1 (by rfl) ⟨1635785, by rfl⟩ : syracuseStep 2181047 = 3271571) B3271571
theorem B2181083 : Blo 1453546 2181083 := bstep (se 1 (by rfl) ⟨1635812, by rfl⟩ : syracuseStep 2181083 = 3271625) B3271625
theorem B2099209 : Blo 1453546 2099209 := bstep (se 2 (by rfl) ⟨787203, by rfl⟩ : syracuseStep 2099209 = 1574407) B1574407
theorem B3680275 : Blo 1453546 3680275 := bstep (se 1 (by rfl) ⟨2760206, by rfl⟩ : syracuseStep 3680275 = 5520413) B5520413
theorem B3106873 : Blo 1453546 3106873 := bstep (se 2 (by rfl) ⟨1165077, by rfl⟩ : syracuseStep 3106873 = 2330155) B2330155
theorem B15722585 : Blo 1453546 15722585 := bstep (se 2 (by rfl) ⟨5895969, by rfl⟩ : syracuseStep 15722585 = 11791939) B11791939
theorem B2762849 : Blo 1453546 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B18638981 : Blo 1453546 18638981 := bstep (se 4 (by rfl) ⟨1747404, by rfl⟩ : syracuseStep 18638981 = 3494809) B3494809
theorem B2763001 : Blo 1453546 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B7358849 : Blo 1453546 7358849 := bstep (se 2 (by rfl) ⟨2759568, by rfl⟩ : syracuseStep 7358849 = 5519137) B5519137
theorem B13978007 : Blo 1453546 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B2181551 : Blo 1453546 2181551 := bstep (se 1 (by rfl) ⟨1636163, by rfl⟩ : syracuseStep 2181551 = 3272327) B3272327
theorem B2329015 : Blo 1453546 2329015 := bstep (se 1 (by rfl) ⟨1746761, by rfl⟩ : syracuseStep 2329015 = 3493523) B3493523
theorem B9325003 : Blo 1453546 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B12421613 : Blo 1453546 12421613 := bstep (se 3 (by rfl) ⟨2329052, by rfl⟩ : syracuseStep 12421613 = 4658105) B4658105
theorem B2181641 : Blo 1453546 2181641 := bstep (se 2 (by rfl) ⟨818115, by rfl⟩ : syracuseStep 2181641 = 1636231) B1636231
theorem B125774369 : Blo 1453546 125774369 := bstep (se 2 (by rfl) ⟨47165388, by rfl⟩ : syracuseStep 125774369 = 94330777) B94330777
theorem B2181671 : Blo 1453546 2181671 := bstep (se 1 (by rfl) ⟨1636253, by rfl⟩ : syracuseStep 2181671 = 3272507) B3272507
theorem B3271265 : Blo 1453546 3271265 := bstep (se 2 (by rfl) ⟨1226724, by rfl⟩ : syracuseStep 3271265 = 2453449) B2453449
theorem B2181755 : Blo 1453546 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B2181881 : Blo 1453546 2181881 := bstep (se 2 (by rfl) ⟨818205, by rfl⟩ : syracuseStep 2181881 = 1636411) B1636411
theorem B6638365 : Blo 1453546 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B2181983 : Blo 1453546 2181983 := bstep (se 1 (by rfl) ⟨1636487, by rfl⟩ : syracuseStep 2181983 = 3272975) B3272975
theorem B2181995 : Blo 1453546 2181995 := bstep (se 1 (by rfl) ⟨1636496, by rfl⟩ : syracuseStep 2181995 = 3272993) B3272993
theorem B11045807 : Blo 1453546 11045807 := bstep (se 1 (by rfl) ⟨8284355, by rfl⟩ : syracuseStep 11045807 = 16568711) B16568711
theorem B3271607 : Blo 1453546 3271607 := bstep (se 1 (by rfl) ⟨2453705, by rfl⟩ : syracuseStep 3271607 = 4907411) B4907411
theorem B7973939 : Blo 1453546 7973939 := bstep (se 1 (by rfl) ⟨5980454, by rfl⟩ : syracuseStep 7973939 = 11960909) B11960909
theorem B3681359 : Blo 1453546 3681359 := bstep (se 1 (by rfl) ⟨2761019, by rfl⟩ : syracuseStep 3681359 = 5522039) B5522039
theorem B2182223 : Blo 1453546 2182223 := bstep (se 1 (by rfl) ⟨1636667, by rfl⟩ : syracuseStep 2182223 = 3273335) B3273335
theorem B7367759 : Blo 1453546 7367759 := bstep (se 1 (by rfl) ⟨5525819, by rfl⟩ : syracuseStep 7367759 = 11051639) B11051639
theorem B7359659 : Blo 1453546 7359659 := bstep (se 1 (by rfl) ⟨5519744, by rfl⟩ : syracuseStep 7359659 = 11039489) B11039489
theorem B2182343 : Blo 1453546 2182343 := bstep (se 1 (by rfl) ⟨1636757, by rfl⟩ : syracuseStep 2182343 = 3273515) B3273515
theorem B4910327 : Blo 1453546 4910327 := bstep (se 1 (by rfl) ⟨3682745, by rfl⟩ : syracuseStep 4910327 = 7365491) B7365491
theorem B9325847 : Blo 1453546 9325847 := bstep (se 1 (by rfl) ⟨6994385, by rfl⟩ : syracuseStep 9325847 = 13988771) B13988771
theorem B2182505 : Blo 1453546 2182505 := bstep (se 2 (by rfl) ⟨818439, by rfl⟩ : syracuseStep 2182505 = 1636879) B1636879
theorem B11201935 : Blo 1453546 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B2182583 : Blo 1453546 2182583 := bstep (se 1 (by rfl) ⟨1636937, by rfl⟩ : syracuseStep 2182583 = 3273875) B3273875
theorem B2182619 : Blo 1453546 2182619 := bstep (se 1 (by rfl) ⟨1636964, by rfl⟩ : syracuseStep 2182619 = 3273929) B3273929
theorem B5524955 : Blo 1453546 5524955 := bstep (se 1 (by rfl) ⟨4143716, by rfl⟩ : syracuseStep 5524955 = 8287433) B8287433
theorem B10489331 : Blo 1453546 10489331 := bstep (se 1 (by rfl) ⟨7866998, by rfl⟩ : syracuseStep 10489331 = 15733997) B15733997
theorem B3272201 : Blo 1453546 3272201 := bstep (se 2 (by rfl) ⟨1227075, by rfl⟩ : syracuseStep 3272201 = 2454151) B2454151
theorem B1453607 : Blo 1453546 1453607 := bstep (se 1 (by rfl) ⟨1090205, by rfl⟩ : syracuseStep 1453607 = 2180411) B2180411
theorem B4910651 : Blo 1453546 4910651 := bstep (se 1 (by rfl) ⟨3682988, by rfl⟩ : syracuseStep 4910651 = 7365977) B7365977
theorem B1453647 : Blo 1453546 1453647 := bstep (se 1 (by rfl) ⟨1090235, by rfl⟩ : syracuseStep 1453647 = 2180471) B2180471
theorem B2453071 : Blo 1453546 2453071 := bstep (se 1 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 2453071 = 3679607) B3679607
theorem B1453663 : Blo 1453546 1453663 := bstep (se 1 (by rfl) ⟨1090247, by rfl⟩ : syracuseStep 1453663 = 2180495) B2180495
theorem B1453691 : Blo 1453546 1453691 := bstep (se 1 (by rfl) ⟨1090268, by rfl⟩ : syracuseStep 1453691 = 2180537) B2180537
theorem B7360145 : Blo 1453546 7360145 := bstep (se 2 (by rfl) ⟨2760054, by rfl⟩ : syracuseStep 7360145 = 5520109) B5520109
theorem B6991505 : Blo 1453546 6991505 := bstep (se 2 (by rfl) ⟨2621814, by rfl⟩ : syracuseStep 6991505 = 5243629) B5243629
theorem B1453743 : Blo 1453546 1453743 := bstep (se 1 (by rfl) ⟨1090307, by rfl⟩ : syracuseStep 1453743 = 2180615) B2180615
theorem B1453767 : Blo 1453546 1453767 := bstep (se 1 (by rfl) ⟨1090325, by rfl⟩ : syracuseStep 1453767 = 2180651) B2180651
theorem B3682007 : Blo 1453546 3682007 := bstep (se 1 (by rfl) ⟨2761505, by rfl⟩ : syracuseStep 3682007 = 5523011) B5523011
theorem B7368407 : Blo 1453546 7368407 := bstep (se 1 (by rfl) ⟨5526305, by rfl⟩ : syracuseStep 7368407 = 11052611) B11052611
theorem B1453787 : Blo 1453546 1453787 := bstep (se 1 (by rfl) ⟨1090340, by rfl⟩ : syracuseStep 1453787 = 2180681) B2180681
theorem B1453863 : Blo 1453546 1453863 := bstep (se 1 (by rfl) ⟨1090397, by rfl⟩ : syracuseStep 1453863 = 2180795) B2180795
theorem B2453321 : Blo 1453546 2453321 := bstep (se 2 (by rfl) ⟨919995, by rfl⟩ : syracuseStep 2453321 = 1839991) B1839991
theorem B4910921 : Blo 1453546 4910921 := bstep (se 2 (by rfl) ⟨1841595, by rfl⟩ : syracuseStep 4910921 = 3683191) B3683191
theorem B1453903 : Blo 1453546 1453903 := bstep (se 1 (by rfl) ⟨1090427, by rfl⟩ : syracuseStep 1453903 = 2180855) B2180855
theorem B1453919 : Blo 1453546 1453919 := bstep (se 1 (by rfl) ⟨1090439, by rfl⟩ : syracuseStep 1453919 = 2180879) B2180879
theorem B9318239 : Blo 1453546 9318239 := bstep (se 1 (by rfl) ⟨6988679, by rfl⟩ : syracuseStep 9318239 = 13977359) B13977359
theorem B3272543 : Blo 1453546 3272543 := bstep (se 1 (by rfl) ⟨2454407, by rfl⟩ : syracuseStep 3272543 = 4908815) B4908815
theorem B294768497 : Blo 1453546 294768497 := bstep (se 2 (by rfl) ⟨110538186, by rfl⟩ : syracuseStep 294768497 = 221076373) B221076373
theorem B1453947 : Blo 1453546 1453947 := bstep (se 1 (by rfl) ⟨1090460, by rfl⟩ : syracuseStep 1453947 = 2180921) B2180921
theorem B1453999 : Blo 1453546 1453999 := bstep (se 1 (by rfl) ⟨1090499, by rfl⟩ : syracuseStep 1453999 = 2180999) B2180999
theorem B2183087 : Blo 1453546 2183087 := bstep (se 1 (by rfl) ⟨1637315, by rfl⟩ : syracuseStep 2183087 = 3274631) B3274631
theorem B4140983 : Blo 1453546 4140983 := bstep (se 1 (by rfl) ⟨3105737, by rfl⟩ : syracuseStep 4140983 = 6211475) B6211475
theorem B1454023 : Blo 1453546 1454023 := bstep (se 1 (by rfl) ⟨1090517, by rfl⟩ : syracuseStep 1454023 = 2181035) B2181035
theorem B1454043 : Blo 1453546 1454043 := bstep (se 1 (by rfl) ⟨1090532, by rfl⟩ : syracuseStep 1454043 = 2181065) B2181065
theorem B2183177 : Blo 1453546 2183177 := bstep (se 2 (by rfl) ⟨818691, by rfl⟩ : syracuseStep 2183177 = 1637383) B1637383
theorem B4657171 : Blo 1453546 4657171 := bstep (se 1 (by rfl) ⟨3492878, by rfl⟩ : syracuseStep 4657171 = 6985757) B6985757
theorem B3272723 : Blo 1453546 3272723 := bstep (se 1 (by rfl) ⟨2454542, by rfl⟩ : syracuseStep 3272723 = 4909085) B4909085
theorem B1454119 : Blo 1453546 1454119 := bstep (se 1 (by rfl) ⟨1090589, by rfl⟩ : syracuseStep 1454119 = 2181179) B2181179
theorem B2183207 : Blo 1453546 2183207 := bstep (se 1 (by rfl) ⟨1637405, by rfl⟩ : syracuseStep 2183207 = 3274811) B3274811
theorem B3682361 : Blo 1453546 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B1454159 : Blo 1453546 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B1454175 : Blo 1453546 1454175 := bstep (se 1 (by rfl) ⟨1090631, by rfl⟩ : syracuseStep 1454175 = 2181263) B2181263
theorem B159166579 : Blo 1453546 159166579 := bstep (se 1 (by rfl) ⟨119374934, by rfl⟩ : syracuseStep 159166579 = 238749869) B238749869
theorem B11800691 : Blo 1453546 11800691 := bstep (se 1 (by rfl) ⟨8850518, by rfl⟩ : syracuseStep 11800691 = 17701037) B17701037
theorem B1454203 : Blo 1453546 1454203 := bstep (se 1 (by rfl) ⟨1090652, by rfl⟩ : syracuseStep 1454203 = 2181305) B2181305
theorem B2183291 : Blo 1453546 2183291 := bstep (se 1 (by rfl) ⟨1637468, by rfl⟩ : syracuseStep 2183291 = 3274937) B3274937
theorem B1454255 : Blo 1453546 1454255 := bstep (se 1 (by rfl) ⟨1090691, by rfl⟩ : syracuseStep 1454255 = 2181383) B2181383
theorem B1454279 : Blo 1453546 1454279 := bstep (se 1 (by rfl) ⟨1090709, by rfl⟩ : syracuseStep 1454279 = 2181419) B2181419
theorem B1454299 : Blo 1453546 1454299 := bstep (se 1 (by rfl) ⟨1090724, by rfl⟩ : syracuseStep 1454299 = 2181449) B2181449
theorem B2453753 : Blo 1453546 2453753 := bstep (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) B1840315
theorem B2330873 : Blo 1453546 2330873 := bstep (se 2 (by rfl) ⟨874077, by rfl⟩ : syracuseStep 2330873 = 1748155) B1748155
theorem B1454375 : Blo 1453546 1454375 := bstep (se 1 (by rfl) ⟨1090781, by rfl⟩ : syracuseStep 1454375 = 2181563) B2181563
theorem B1454415 : Blo 1453546 1454415 := bstep (se 1 (by rfl) ⟨1090811, by rfl⟩ : syracuseStep 1454415 = 2181623) B2181623
theorem B10482007 : Blo 1453546 10482007 := bstep (se 1 (by rfl) ⟨7861505, by rfl⟩ : syracuseStep 10482007 = 15723011) B15723011
theorem B1454431 : Blo 1453546 1454431 := bstep (se 1 (by rfl) ⟨1090823, by rfl⟩ : syracuseStep 1454431 = 2181647) B2181647
theorem B2330975 : Blo 1453546 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B3273065 : Blo 1453546 3273065 := bstep (se 2 (by rfl) ⟨1227399, by rfl⟩ : syracuseStep 3273065 = 2454799) B2454799
theorem B1454459 : Blo 1453546 1454459 := bstep (se 1 (by rfl) ⟨1090844, by rfl⟩ : syracuseStep 1454459 = 2181689) B2181689
theorem B19911041 : Blo 1453546 19911041 := bstep (se 2 (by rfl) ⟨7466640, by rfl⟩ : syracuseStep 19911041 = 14933281) B14933281
theorem B2453935 : Blo 1453546 2453935 := bstep (se 1 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 2453935 = 3680903) B3680903
theorem B1454511 : Blo 1453546 1454511 := bstep (se 1 (by rfl) ⟨1090883, by rfl⟩ : syracuseStep 1454511 = 2181767) B2181767
theorem B1454535 : Blo 1453546 1454535 := bstep (se 1 (by rfl) ⟨1090901, by rfl⟩ : syracuseStep 1454535 = 2181803) B2181803
theorem B1454555 : Blo 1453546 1454555 := bstep (se 1 (by rfl) ⟨1090916, by rfl⟩ : syracuseStep 1454555 = 2181833) B2181833
theorem B2454023 : Blo 1453546 2454023 := bstep (se 1 (by rfl) ⟨1840517, by rfl⟩ : syracuseStep 2454023 = 3681035) B3681035
theorem B1454631 : Blo 1453546 1454631 := bstep (se 1 (by rfl) ⟨1090973, by rfl⟩ : syracuseStep 1454631 = 2181947) B2181947
theorem B22377019 : Blo 1453546 22377019 := bstep (se 1 (by rfl) ⟨16782764, by rfl⟩ : syracuseStep 22377019 = 33565529) B33565529
theorem B1552975 : Blo 1453546 1552975 := bstep (se 1 (by rfl) ⟨1164731, by rfl⟩ : syracuseStep 1552975 = 2329463) B2329463
theorem B1454671 : Blo 1453546 1454671 := bstep (se 1 (by rfl) ⟨1091003, by rfl⟩ : syracuseStep 1454671 = 2182007) B2182007
theorem B1454687 : Blo 1453546 1454687 := bstep (se 1 (by rfl) ⟨1091015, by rfl⟩ : syracuseStep 1454687 = 2182031) B2182031
theorem B4657787 : Blo 1453546 4657787 := bstep (se 1 (by rfl) ⟨3493340, by rfl⟩ : syracuseStep 4657787 = 6986681) B6986681
theorem B1454715 : Blo 1453546 1454715 := bstep (se 1 (by rfl) ⟨1091036, by rfl⟩ : syracuseStep 1454715 = 2182073) B2182073
theorem B1454767 : Blo 1453546 1454767 := bstep (se 1 (by rfl) ⟨1091075, by rfl⟩ : syracuseStep 1454767 = 2182151) B2182151
theorem B1553095 : Blo 1453546 1553095 := bstep (se 1 (by rfl) ⟨1164821, by rfl⟩ : syracuseStep 1553095 = 2329643) B2329643
theorem B1454791 : Blo 1453546 1454791 := bstep (se 1 (by rfl) ⟨1091093, by rfl⟩ : syracuseStep 1454791 = 2182187) B2182187
theorem B5526215 : Blo 1453546 5526215 := bstep (se 1 (by rfl) ⟨4144661, by rfl⟩ : syracuseStep 5526215 = 8289323) B8289323
theorem B5239505 : Blo 1453546 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B1454811 : Blo 1453546 1454811 := bstep (se 1 (by rfl) ⟨1091108, by rfl⟩ : syracuseStep 1454811 = 2182217) B2182217
theorem B1454887 : Blo 1453546 1454887 := bstep (se 1 (by rfl) ⟨1091165, by rfl⟩ : syracuseStep 1454887 = 2182331) B2182331
theorem B1454927 : Blo 1453546 1454927 := bstep (se 1 (by rfl) ⟨1091195, by rfl⟩ : syracuseStep 1454927 = 2182391) B2182391
theorem B2454367 : Blo 1453546 2454367 := bstep (se 1 (by rfl) ⟨1840775, by rfl⟩ : syracuseStep 2454367 = 3681551) B3681551
theorem B1454943 : Blo 1453546 1454943 := bstep (se 1 (by rfl) ⟨1091207, by rfl⟩ : syracuseStep 1454943 = 2182415) B2182415
theorem B1454971 : Blo 1453546 1454971 := bstep (se 1 (by rfl) ⟨1091228, by rfl⟩ : syracuseStep 1454971 = 2182457) B2182457
theorem B1455023 : Blo 1453546 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B2454455 : Blo 1453546 2454455 := bstep (se 1 (by rfl) ⟨1840841, by rfl⟩ : syracuseStep 2454455 = 3681683) B3681683
theorem B3273659 : Blo 1453546 3273659 := bstep (se 1 (by rfl) ⟨2455244, by rfl⟩ : syracuseStep 3273659 = 4910489) B4910489
theorem B1455047 : Blo 1453546 1455047 := bstep (se 1 (by rfl) ⟨1091285, by rfl⟩ : syracuseStep 1455047 = 2182571) B2182571
theorem B1455067 : Blo 1453546 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B4142087 : Blo 1453546 4142087 := bstep (se 1 (by rfl) ⟨3106565, by rfl⟩ : syracuseStep 4142087 = 6213131) B6213131
theorem B12424211 : Blo 1453546 12424211 := bstep (se 1 (by rfl) ⟨9318158, by rfl⟩ : syracuseStep 12424211 = 18636317) B18636317
theorem B1635367 : Blo 1453546 1635367 := bstep (se 1 (by rfl) ⟨1226525, by rfl⟩ : syracuseStep 1635367 = 2453051) B2453051
theorem B1455143 : Blo 1453546 1455143 := bstep (se 1 (by rfl) ⟨1091357, by rfl⟩ : syracuseStep 1455143 = 2182715) B2182715
theorem B3273785 : Blo 1453546 3273785 := bstep (se 2 (by rfl) ⟨1227669, by rfl⟩ : syracuseStep 3273785 = 2455339) B2455339
theorem B1455183 : Blo 1453546 1455183 := bstep (se 1 (by rfl) ⟨1091387, by rfl⟩ : syracuseStep 1455183 = 2182775) B2182775
theorem B1455199 : Blo 1453546 1455199 := bstep (se 1 (by rfl) ⟨1091399, by rfl⟩ : syracuseStep 1455199 = 2182799) B2182799
theorem B1455227 : Blo 1453546 1455227 := bstep (se 1 (by rfl) ⟨1091420, by rfl⟩ : syracuseStep 1455227 = 2182841) B2182841
theorem B1455279 : Blo 1453546 1455279 := bstep (se 1 (by rfl) ⟨1091459, by rfl⟩ : syracuseStep 1455279 = 2182919) B2182919
theorem B1455303 : Blo 1453546 1455303 := bstep (se 1 (by rfl) ⟨1091477, by rfl⟩ : syracuseStep 1455303 = 2182955) B2182955
theorem B1455323 : Blo 1453546 1455323 := bstep (se 1 (by rfl) ⟨1091492, by rfl⟩ : syracuseStep 1455323 = 2182985) B2182985
theorem B1455399 : Blo 1453546 1455399 := bstep (se 1 (by rfl) ⟨1091549, by rfl⟩ : syracuseStep 1455399 = 2183099) B2183099
theorem B1455439 : Blo 1453546 1455439 := bstep (se 1 (by rfl) ⟨1091579, by rfl⟩ : syracuseStep 1455439 = 2183159) B2183159
theorem B1455455 : Blo 1453546 1455455 := bstep (se 1 (by rfl) ⟨1091591, by rfl⟩ : syracuseStep 1455455 = 2183183) B2183183
theorem B4142441 : Blo 1453546 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B1455483 : Blo 1453546 1455483 := bstep (se 1 (by rfl) ⟨1091612, by rfl⟩ : syracuseStep 1455483 = 2183225) B2183225
theorem B3274127 : Blo 1453546 3274127 := bstep (se 1 (by rfl) ⟨2455595, by rfl⟩ : syracuseStep 3274127 = 4911191) B4911191
theorem B1455535 : Blo 1453546 1455535 := bstep (se 1 (by rfl) ⟨1091651, by rfl⟩ : syracuseStep 1455535 = 2183303) B2183303
theorem B20977157 : Blo 1453546 20977157 := bstep (se 4 (by rfl) ⟨1966608, by rfl⟩ : syracuseStep 20977157 = 3933217) B3933217
theorem B2455049 : Blo 1453546 2455049 := bstep (se 2 (by rfl) ⟨920643, by rfl⟩ : syracuseStep 2455049 = 1841287) B1841287
theorem B3495521 : Blo 1453546 3495521 := bstep (se 2 (by rfl) ⟨1310820, by rfl⟩ : syracuseStep 3495521 = 2621641) B2621641
theorem B2455211 : Blo 1453546 2455211 := bstep (se 1 (by rfl) ⟨1841408, by rfl⟩ : syracuseStep 2455211 = 3682817) B3682817
theorem B3274451 : Blo 1453546 3274451 := bstep (se 1 (by rfl) ⟨2455838, by rfl⟩ : syracuseStep 3274451 = 4911677) B4911677
theorem B10082029 : Blo 1453546 10082029 := bstep (se 3 (by rfl) ⟨1890380, by rfl⟩ : syracuseStep 10082029 = 3780761) B3780761
theorem B2488171 : Blo 1453546 2488171 := bstep (se 1 (by rfl) ⟨1866128, by rfl⟩ : syracuseStep 2488171 = 3732257) B3732257
theorem B7362413 : Blo 1453546 7362413 := bstep (se 3 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 7362413 = 2760905) B2760905
theorem B7362575 : Blo 1453546 7362575 := bstep (se 1 (by rfl) ⟨5521931, by rfl⟩ : syracuseStep 7362575 = 11043863) B11043863
theorem B2455609 : Blo 1453546 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B3930191 : Blo 1453546 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B5519441 : Blo 1453546 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B1841231 : Blo 1453546 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B4257949 : Blo 1453546 4257949 := bstep (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) B1596731
theorem B2455751 : Blo 1453546 2455751 := bstep (se 1 (by rfl) ⟨1841813, by rfl⟩ : syracuseStep 2455751 = 3683627) B3683627
theorem B2455913 : Blo 1453546 2455913 := bstep (se 2 (by rfl) ⟨920967, by rfl⟩ : syracuseStep 2455913 = 1841935) B1841935
theorem B15718859 : Blo 1453546 15718859 := bstep (se 1 (by rfl) ⟨11789144, by rfl⟩ : syracuseStep 15718859 = 23578289) B23578289
theorem B6216173 : Blo 1453546 6216173 := bstep (se 3 (by rfl) ⟨1165532, by rfl⟩ : syracuseStep 6216173 = 2331065) B2331065
theorem B5519897 : Blo 1453546 5519897 := bstep (se 2 (by rfl) ⟨2069961, by rfl⟩ : syracuseStep 5519897 = 4139923) B4139923
theorem B18897437 : Blo 1453546 18897437 := bstep (se 3 (by rfl) ⟨3543269, by rfl⟩ : syracuseStep 18897437 = 7086539) B7086539
theorem B4912055 : Blo 1453546 4912055 := bstep (se 1 (by rfl) ⟨3684041, by rfl⟩ : syracuseStep 4912055 = 7368083) B7368083
theorem B1636987 : Blo 1453546 1636987 := bstep (se 1 (by rfl) ⟨1227740, by rfl⟩ : syracuseStep 1636987 = 2455481) B2455481
theorem B2759599 : Blo 1453546 2759599 := bstep (se 1 (by rfl) ⟨2069699, by rfl⟩ : syracuseStep 2759599 = 4139399) B4139399
theorem B1637455 : Blo 1453546 1637455 := bstep (se 1 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 1637455 = 2456183) B2456183
theorem B6216857 : Blo 1453546 6216857 := bstep (se 2 (by rfl) ⟨2331321, by rfl⟩ : syracuseStep 6216857 = 4662643) B4662643
theorem B7085531 : Blo 1453546 7085531 := bstep (se 1 (by rfl) ⟨5314148, by rfl⟩ : syracuseStep 7085531 = 10628297) B10628297
theorem B4423265 : Blo 1453546 4423265 := bstep (se 2 (by rfl) ⟨1658724, by rfl⟩ : syracuseStep 4423265 = 3317449) B3317449
theorem B5521081 : Blo 1453546 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B4906871 : Blo 1453546 4906871 := bstep (se 1 (by rfl) ⟨3680153, by rfl⟩ : syracuseStep 4906871 = 7360307) B7360307
theorem B19898297 : Blo 1453546 19898297 := bstep (se 2 (by rfl) ⟨7461861, by rfl⟩ : syracuseStep 19898297 = 14923723) B14923723
theorem B6209561 : Blo 1453546 6209561 := bstep (se 2 (by rfl) ⟨2328585, by rfl⟩ : syracuseStep 6209561 = 4657171) B4657171
theorem B4907033 : Blo 1453546 4907033 := bstep (se 2 (by rfl) ⟨1840137, by rfl⟩ : syracuseStep 4907033 = 3680275) B3680275
theorem B10485811 : Blo 1453546 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B212222105 : Blo 1453546 212222105 := bstep (se 2 (by rfl) ⟨79583289, by rfl⟩ : syracuseStep 212222105 = 159166579) B159166579
theorem B5677265 : Blo 1453546 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B8282533 : Blo 1453546 8282533 := bstep (se 4 (by rfl) ⟨776487, by rfl⟩ : syracuseStep 8282533 = 1552975) B1552975
theorem B3105191 : Blo 1453546 3105191 := bstep (se 1 (by rfl) ⟨2328893, by rfl⟩ : syracuseStep 3105191 = 4657787) B4657787
theorem B13976009 : Blo 1453546 13976009 := bstep (se 2 (by rfl) ⟨5241003, by rfl⟩ : syracuseStep 13976009 = 10482007) B10482007
theorem B20972033 : Blo 1453546 20972033 := bstep (se 2 (by rfl) ⟨7864512, by rfl⟩ : syracuseStep 20972033 = 15729025) B15729025
theorem B10486273 : Blo 1453546 10486273 := bstep (se 2 (by rfl) ⟨3932352, by rfl⟩ : syracuseStep 10486273 = 7864705) B7864705
theorem B3105353 : Blo 1453546 3105353 := bstep (se 2 (by rfl) ⟨1164507, by rfl⟩ : syracuseStep 3105353 = 2329015) B2329015
theorem B5898905 : Blo 1453546 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B7570091 : Blo 1453546 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B2761391 : Blo 1453546 2761391 := bstep (se 1 (by rfl) ⟨2071043, by rfl⟩ : syracuseStep 2761391 = 4142087) B4142087
theorem B8282807 : Blo 1453546 8282807 := bstep (se 1 (by rfl) ⟨6212105, by rfl⟩ : syracuseStep 8282807 = 12424211) B12424211
theorem B29836025 : Blo 1453546 29836025 := bstep (se 2 (by rfl) ⟨11188509, by rfl⟩ : syracuseStep 29836025 = 22377019) B22377019
theorem B2761627 : Blo 1453546 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B47170583 : Blo 1453546 47170583 := bstep (se 1 (by rfl) ⟨35377937, by rfl⟩ : syracuseStep 47170583 = 70755875) B70755875
theorem B29131919 : Blo 1453546 29131919 := bstep (se 1 (by rfl) ⟨21848939, by rfl⟩ : syracuseStep 29131919 = 43697879) B43697879
theorem B3679465 : Blo 1453546 3679465 := bstep (se 2 (by rfl) ⟨1379799, by rfl⟩ : syracuseStep 3679465 = 2759599) B2759599
theorem B4908275 : Blo 1453546 4908275 := bstep (se 1 (by rfl) ⟨3681206, by rfl⟩ : syracuseStep 4908275 = 7362413) B7362413
theorem B4908383 : Blo 1453546 4908383 := bstep (se 1 (by rfl) ⟨3681287, by rfl⟩ : syracuseStep 4908383 = 7362575) B7362575
theorem B2180489 : Blo 1453546 2180489 := bstep (se 2 (by rfl) ⟨817683, by rfl⟩ : syracuseStep 2180489 = 1635367) B1635367
theorem B3679627 : Blo 1453546 3679627 := bstep (se 1 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 3679627 = 5519441) B5519441
theorem B10479239 : Blo 1453546 10479239 := bstep (se 1 (by rfl) ⟨7859429, by rfl⟩ : syracuseStep 10479239 = 15718859) B15718859
theorem B7366301 : Blo 1453546 7366301 := bstep (se 3 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 7366301 = 2762363) B2762363
theorem B3679931 : Blo 1453546 3679931 := bstep (se 1 (by rfl) ⟨2759948, by rfl⟩ : syracuseStep 3679931 = 5519897) B5519897
theorem B2180843 : Blo 1453546 2180843 := bstep (se 1 (by rfl) ⟨1635632, by rfl⟩ : syracuseStep 2180843 = 3271265) B3271265
theorem B10487657 : Blo 1453546 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B14935913 : Blo 1453546 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B2181071 : Blo 1453546 2181071 := bstep (se 1 (by rfl) ⟨1635803, by rfl⟩ : syracuseStep 2181071 = 3271607) B3271607
theorem B3270761 : Blo 1453546 3270761 := bstep (se 2 (by rfl) ⟨1226535, by rfl⟩ : syracuseStep 3270761 = 2453071) B2453071
theorem B26544257 : Blo 1453546 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B2181467 : Blo 1453546 2181467 := bstep (se 1 (by rfl) ⟨1636100, by rfl⟩ : syracuseStep 2181467 = 3272201) B3272201
theorem B6212159 : Blo 1453546 6212159 := bstep (se 1 (by rfl) ⟨4659119, by rfl⟩ : syracuseStep 6212159 = 9318239) B9318239
theorem B2181695 : Blo 1453546 2181695 := bstep (se 1 (by rfl) ⟨1636271, by rfl⟩ : syracuseStep 2181695 = 3272543) B3272543
theorem B196512331 : Blo 1453546 196512331 := bstep (se 1 (by rfl) ⟨147384248, by rfl⟩ : syracuseStep 196512331 = 294768497) B294768497
theorem B3271247 : Blo 1453546 3271247 := bstep (se 1 (by rfl) ⟨2453435, by rfl⟩ : syracuseStep 3271247 = 4906871) B4906871
theorem B13265531 : Blo 1453546 13265531 := bstep (se 1 (by rfl) ⟨9949148, by rfl⟩ : syracuseStep 13265531 = 19898297) B19898297
theorem B2181815 : Blo 1453546 2181815 := bstep (se 1 (by rfl) ⟨1636361, by rfl⟩ : syracuseStep 2181815 = 3272723) B3272723
theorem B3271391 : Blo 1453546 3271391 := bstep (se 1 (by rfl) ⟨2453543, by rfl⟩ : syracuseStep 3271391 = 4907087) B4907087
theorem B7867127 : Blo 1453546 7867127 := bstep (se 1 (by rfl) ⟨5900345, by rfl⟩ : syracuseStep 7867127 = 11800691) B11800691
theorem B4909949 : Blo 1453546 4909949 := bstep (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) B1841231
theorem B35367815 : Blo 1453546 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B6630299 : Blo 1453546 6630299 := bstep (se 1 (by rfl) ⟨4972724, by rfl⟩ : syracuseStep 6630299 = 9945449) B9945449
theorem B2182043 : Blo 1453546 2182043 := bstep (se 1 (by rfl) ⟨1636532, by rfl⟩ : syracuseStep 2182043 = 3273065) B3273065
theorem B13274027 : Blo 1453546 13274027 := bstep (se 1 (by rfl) ⟨9955520, by rfl⟩ : syracuseStep 13274027 = 19911041) B19911041
theorem B7367597 : Blo 1453546 7367597 := bstep (se 3 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 7367597 = 2762849) B2762849
theorem B3271643 : Blo 1453546 3271643 := bstep (se 1 (by rfl) ⟨2453732, by rfl⟩ : syracuseStep 3271643 = 4907465) B4907465
theorem B4910219 : Blo 1453546 4910219 := bstep (se 1 (by rfl) ⟨3682664, by rfl⟩ : syracuseStep 4910219 = 7365329) B7365329
theorem B3271823 : Blo 1453546 3271823 := bstep (se 1 (by rfl) ⟨2453867, by rfl⟩ : syracuseStep 3271823 = 4907735) B4907735
theorem B3271913 : Blo 1453546 3271913 := bstep (se 2 (by rfl) ⟨1226967, by rfl⟩ : syracuseStep 3271913 = 2453935) B2453935
theorem B3271967 : Blo 1453546 3271967 := bstep (se 1 (by rfl) ⟨2453975, by rfl⟩ : syracuseStep 3271967 = 4907951) B4907951
theorem B2182439 : Blo 1453546 2182439 := bstep (se 1 (by rfl) ⟨1636829, by rfl⟩ : syracuseStep 2182439 = 3273659) B3273659
theorem B2182523 : Blo 1453546 2182523 := bstep (se 1 (by rfl) ⟨1636892, by rfl⟩ : syracuseStep 2182523 = 3273785) B3273785
theorem B2182649 : Blo 1453546 2182649 := bstep (se 2 (by rfl) ⟨818493, by rfl⟩ : syracuseStep 2182649 = 1636987) B1636987
theorem B1453563 : Blo 1453546 1453563 := bstep (se 1 (by rfl) ⟨1090172, by rfl⟩ : syracuseStep 1453563 = 2180345) B2180345
theorem B1453631 : Blo 1453546 1453631 := bstep (se 1 (by rfl) ⟨1090223, by rfl⟩ : syracuseStep 1453631 = 2180447) B2180447
theorem B1453639 : Blo 1453546 1453639 := bstep (se 1 (by rfl) ⟨1090229, by rfl⟩ : syracuseStep 1453639 = 2180459) B2180459
theorem B5893715 : Blo 1453546 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3681875 : Blo 1453546 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B2182751 : Blo 1453546 2182751 := bstep (se 1 (by rfl) ⟨1637063, by rfl⟩ : syracuseStep 2182751 = 3274127) B3274127
theorem B2453179 : Blo 1453546 2453179 := bstep (se 1 (by rfl) ⟨1839884, by rfl⟩ : syracuseStep 2453179 = 3679769) B3679769
theorem B1453791 : Blo 1453546 1453791 := bstep (se 1 (by rfl) ⟨1090343, by rfl⟩ : syracuseStep 1453791 = 2180687) B2180687
theorem B3272489 : Blo 1453546 3272489 := bstep (se 2 (by rfl) ⟨1227183, by rfl⟩ : syracuseStep 3272489 = 2454367) B2454367
theorem B1453871 : Blo 1453546 1453871 := bstep (se 1 (by rfl) ⟨1090403, by rfl⟩ : syracuseStep 1453871 = 2180807) B2180807
theorem B2182967 : Blo 1453546 2182967 := bstep (se 1 (by rfl) ⟨1637225, by rfl⟩ : syracuseStep 2182967 = 3274451) B3274451
theorem B4140857 : Blo 1453546 4140857 := bstep (se 2 (by rfl) ⟨1552821, by rfl⟩ : syracuseStep 4140857 = 3105643) B3105643
theorem B1453979 : Blo 1453546 1453979 := bstep (se 1 (by rfl) ⟨1090484, by rfl⟩ : syracuseStep 1453979 = 2180969) B2180969
theorem B1454031 : Blo 1453546 1454031 := bstep (se 1 (by rfl) ⟨1090523, by rfl⟩ : syracuseStep 1454031 = 2181047) B2181047
theorem B1454055 : Blo 1453546 1454055 := bstep (se 1 (by rfl) ⟨1090541, by rfl⟩ : syracuseStep 1454055 = 2181083) B2181083
theorem B55939085 : Blo 1453546 55939085 := bstep (se 3 (by rfl) ⟨10488578, by rfl⟩ : syracuseStep 55939085 = 20977157) B20977157
theorem B10481723 : Blo 1453546 10481723 := bstep (se 1 (by rfl) ⟨7861292, by rfl⟩ : syracuseStep 10481723 = 15722585) B15722585
theorem B2183273 : Blo 1453546 2183273 := bstep (se 2 (by rfl) ⟨818727, by rfl⟩ : syracuseStep 2183273 = 1637455) B1637455
theorem B9318671 : Blo 1453546 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B1454367 : Blo 1453546 1454367 := bstep (se 1 (by rfl) ⟨1090775, by rfl⟩ : syracuseStep 1454367 = 2181551) B2181551
theorem B1454427 : Blo 1453546 1454427 := bstep (se 1 (by rfl) ⟨1090820, by rfl⟩ : syracuseStep 1454427 = 2181641) B2181641
theorem B83849579 : Blo 1453546 83849579 := bstep (se 1 (by rfl) ⟨62887184, by rfl⟩ : syracuseStep 83849579 = 125774369) B125774369
theorem B1454447 : Blo 1453546 1454447 := bstep (se 1 (by rfl) ⟨1090835, by rfl⟩ : syracuseStep 1454447 = 2181671) B2181671
theorem B1454503 : Blo 1453546 1454503 := bstep (se 1 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 1454503 = 2181755) B2181755
theorem B1454587 : Blo 1453546 1454587 := bstep (se 1 (by rfl) ⟨1090940, by rfl⟩ : syracuseStep 1454587 = 2181881) B2181881
theorem B13972013 : Blo 1453546 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B1454655 : Blo 1453546 1454655 := bstep (se 1 (by rfl) ⟨1090991, by rfl⟩ : syracuseStep 1454655 = 2181983) B2181983
theorem B1454663 : Blo 1453546 1454663 := bstep (se 1 (by rfl) ⟨1090997, by rfl⟩ : syracuseStep 1454663 = 2181995) B2181995
theorem B2454239 : Blo 1453546 2454239 := bstep (se 1 (by rfl) ⟨1840679, by rfl⟩ : syracuseStep 2454239 = 3681359) B3681359
theorem B1454815 : Blo 1453546 1454815 := bstep (se 1 (by rfl) ⟨1091111, by rfl⟩ : syracuseStep 1454815 = 2182223) B2182223
theorem B4911839 : Blo 1453546 4911839 := bstep (se 1 (by rfl) ⟨3683879, by rfl⟩ : syracuseStep 4911839 = 7367759) B7367759
theorem B1454895 : Blo 1453546 1454895 := bstep (se 1 (by rfl) ⟨1091171, by rfl⟩ : syracuseStep 1454895 = 2182343) B2182343
theorem B3273551 : Blo 1453546 3273551 := bstep (se 1 (by rfl) ⟨2455163, by rfl⟩ : syracuseStep 3273551 = 4910327) B4910327
theorem B1455003 : Blo 1453546 1455003 := bstep (se 1 (by rfl) ⟨1091252, by rfl⟩ : syracuseStep 1455003 = 2182505) B2182505
theorem B7361441 : Blo 1453546 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B1455055 : Blo 1453546 1455055 := bstep (se 1 (by rfl) ⟨1091291, by rfl⟩ : syracuseStep 1455055 = 2182583) B2182583
theorem B4723687 : Blo 1453546 4723687 := bstep (se 1 (by rfl) ⟨3542765, by rfl⟩ : syracuseStep 4723687 = 7085531) B7085531
theorem B1455079 : Blo 1453546 1455079 := bstep (se 1 (by rfl) ⟨1091309, by rfl⟩ : syracuseStep 1455079 = 2182619) B2182619
theorem B3683303 : Blo 1453546 3683303 := bstep (se 1 (by rfl) ⟨2762477, by rfl⟩ : syracuseStep 3683303 = 5524955) B5524955
theorem B6992887 : Blo 1453546 6992887 := bstep (se 1 (by rfl) ⟨5244665, by rfl⟩ : syracuseStep 6992887 = 10489331) B10489331
theorem B3273767 : Blo 1453546 3273767 := bstep (se 1 (by rfl) ⟨2455325, by rfl⟩ : syracuseStep 3273767 = 4910651) B4910651
theorem B2454671 : Blo 1453546 2454671 := bstep (se 1 (by rfl) ⟨1841003, by rfl⟩ : syracuseStep 2454671 = 3682007) B3682007
theorem B4912271 : Blo 1453546 4912271 := bstep (se 1 (by rfl) ⟨3684203, by rfl⟩ : syracuseStep 4912271 = 7368407) B7368407
theorem B1635547 : Blo 1453546 1635547 := bstep (se 1 (by rfl) ⟨1226660, by rfl⟩ : syracuseStep 1635547 = 2453321) B2453321
theorem B3273947 : Blo 1453546 3273947 := bstep (se 1 (by rfl) ⟨2455460, by rfl⟩ : syracuseStep 3273947 = 4910921) B4910921
theorem B40908017 : Blo 1453546 40908017 := bstep (se 2 (by rfl) ⟨15340506, by rfl⟩ : syracuseStep 40908017 = 30681013) B30681013
theorem B1455391 : Blo 1453546 1455391 := bstep (se 1 (by rfl) ⟨1091543, by rfl⟩ : syracuseStep 1455391 = 2183087) B2183087
theorem B1455451 : Blo 1453546 1455451 := bstep (se 1 (by rfl) ⟨1091588, by rfl⟩ : syracuseStep 1455451 = 2183177) B2183177
theorem B2798945 : Blo 1453546 2798945 := bstep (se 2 (by rfl) ⟨1049604, by rfl⟩ : syracuseStep 2798945 = 2099209) B2099209
theorem B1455471 : Blo 1453546 1455471 := bstep (se 1 (by rfl) ⟨1091603, by rfl⟩ : syracuseStep 1455471 = 2183207) B2183207
theorem B2454907 : Blo 1453546 2454907 := bstep (se 1 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 2454907 = 3682361) B3682361
theorem B8279435 : Blo 1453546 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B4142497 : Blo 1453546 4142497 := bstep (se 2 (by rfl) ⟨1553436, by rfl⟩ : syracuseStep 4142497 = 3106873) B3106873
theorem B3274145 : Blo 1453546 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B1455527 : Blo 1453546 1455527 := bstep (se 1 (by rfl) ⟨1091645, by rfl⟩ : syracuseStep 1455527 = 2183291) B2183291
theorem B1840583 : Blo 1453546 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B1635835 : Blo 1453546 1635835 := bstep (se 1 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 1635835 = 2453753) B2453753
theorem B1553915 : Blo 1453546 1553915 := bstep (se 1 (by rfl) ⟨1165436, by rfl⟩ : syracuseStep 1553915 = 2330873) B2330873
theorem B1840735 : Blo 1453546 1840735 := bstep (se 1 (by rfl) ⟨1380551, by rfl⟩ : syracuseStep 1840735 = 2761103) B2761103
theorem B3684001 : Blo 1453546 3684001 := bstep (se 2 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 3684001 = 2763001) B2763001
theorem B1636015 : Blo 1453546 1636015 := bstep (se 1 (by rfl) ⟨1227011, by rfl⟩ : syracuseStep 1636015 = 2454023) B2454023
theorem B3684143 : Blo 1453546 3684143 := bstep (se 1 (by rfl) ⟨2763107, by rfl⟩ : syracuseStep 3684143 = 5526215) B5526215
theorem B12433337 : Blo 1453546 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B1636303 : Blo 1453546 1636303 := bstep (se 1 (by rfl) ⟨1227227, by rfl⟩ : syracuseStep 1636303 = 2454455) B2454455
theorem B3274703 : Blo 1453546 3274703 := bstep (se 1 (by rfl) ⟨2456027, by rfl⟩ : syracuseStep 3274703 = 4912055) B4912055
theorem B8280143 : Blo 1453546 8280143 := bstep (se 1 (by rfl) ⟨6210107, by rfl⟩ : syracuseStep 8280143 = 12420215) B12420215
theorem B6215933 : Blo 1453546 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B2070793 : Blo 1453546 2070793 := bstep (se 2 (by rfl) ⟨776547, by rfl⟩ : syracuseStep 2070793 = 1553095) B1553095
theorem B1636699 : Blo 1453546 1636699 := bstep (se 1 (by rfl) ⟨1227524, by rfl⟩ : syracuseStep 1636699 = 2455049) B2455049
theorem B1636807 : Blo 1453546 1636807 := bstep (se 1 (by rfl) ⟨1227605, by rfl⟩ : syracuseStep 1636807 = 2455211) B2455211
theorem B2620127 : Blo 1453546 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B12425987 : Blo 1453546 12425987 := bstep (se 1 (by rfl) ⟨9319490, by rfl⟩ : syracuseStep 12425987 = 18638981) B18638981
theorem B1637167 : Blo 1453546 1637167 := bstep (se 1 (by rfl) ⟨1227875, by rfl⟩ : syracuseStep 1637167 = 2455751) B2455751
theorem B35404613 : Blo 1453546 35404613 := bstep (se 4 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 35404613 = 6638365) B6638365
theorem B1637275 : Blo 1453546 1637275 := bstep (se 1 (by rfl) ⟨1227956, by rfl⟩ : syracuseStep 1637275 = 2455913) B2455913
theorem B4905899 : Blo 1453546 4905899 := bstep (se 1 (by rfl) ⟨3679424, by rfl⟩ : syracuseStep 4905899 = 7358849) B7358849
theorem B9321389 : Blo 1453546 9321389 := bstep (se 3 (by rfl) ⟨1747760, by rfl⟩ : syracuseStep 9321389 = 3495521) B3495521
theorem B8281075 : Blo 1453546 8281075 := bstep (se 1 (by rfl) ⟨6210806, by rfl⟩ : syracuseStep 8281075 = 12421613) B12421613
theorem B4144115 : Blo 1453546 4144115 := bstep (se 1 (by rfl) ⟨3108086, by rfl⟩ : syracuseStep 4144115 = 6216173) B6216173
theorem B12598291 : Blo 1453546 12598291 := bstep (se 1 (by rfl) ⟨9448718, by rfl⟩ : syracuseStep 12598291 = 18897437) B18897437
theorem B7363871 : Blo 1453546 7363871 := bstep (se 1 (by rfl) ⟨5522903, by rfl⟩ : syracuseStep 7363871 = 11045807) B11045807
theorem B5315959 : Blo 1453546 5315959 := bstep (se 1 (by rfl) ⟨3986969, by rfl⟩ : syracuseStep 5315959 = 7973939) B7973939
theorem B4144571 : Blo 1453546 4144571 := bstep (se 1 (by rfl) ⟨3108428, by rfl⟩ : syracuseStep 4144571 = 6216857) B6216857
theorem B4906439 : Blo 1453546 4906439 := bstep (se 1 (by rfl) ⟨3679829, by rfl⟩ : syracuseStep 4906439 = 7359659) B7359659
theorem B6217231 : Blo 1453546 6217231 := bstep (se 1 (by rfl) ⟨4662923, by rfl⟩ : syracuseStep 6217231 = 9325847) B9325847
theorem B13983313 : Blo 1453546 13983313 := bstep (se 2 (by rfl) ⟨5243742, by rfl⟩ : syracuseStep 13983313 = 10487485) B10487485
theorem B13442705 : Blo 1453546 13442705 := bstep (se 2 (by rfl) ⟨5041014, by rfl⟩ : syracuseStep 13442705 = 10082029) B10082029
theorem B2948843 : Blo 1453546 2948843 := bstep (se 1 (by rfl) ⟨2211632, by rfl⟩ : syracuseStep 2948843 = 4423265) B4423265
theorem B4906763 : Blo 1453546 4906763 := bstep (se 1 (by rfl) ⟨3680072, by rfl⟩ : syracuseStep 4906763 = 7360145) B7360145
theorem B4661003 : Blo 1453546 4661003 := bstep (se 1 (by rfl) ⟨3495752, by rfl⟩ : syracuseStep 4661003 = 6991505) B6991505
theorem B3317561 : Blo 1453546 3317561 := bstep (se 2 (by rfl) ⟨1244085, by rfl⟩ : syracuseStep 3317561 = 2488171) B2488171
theorem B2760655 : Blo 1453546 2760655 := bstep (se 1 (by rfl) ⟨2070491, by rfl⟩ : syracuseStep 2760655 = 4140983) B4140983
theorem B6987815 : Blo 1453546 6987815 := bstep (se 1 (by rfl) ⟨5240861, by rfl⟩ : syracuseStep 6987815 = 10481723) B10481723
theorem B3784843 : Blo 1453546 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B2761057 : Blo 1453546 2761057 := bstep (se 2 (by rfl) ⟨1035396, by rfl⟩ : syracuseStep 2761057 = 2070793) B2070793
theorem B9314675 : Blo 1453546 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B3932603 : Blo 1453546 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B5521871 : Blo 1453546 5521871 := bstep (se 1 (by rfl) ⟨4141403, by rfl⟩ : syracuseStep 5521871 = 8282807) B8282807
theorem B19890683 : Blo 1453546 19890683 := bstep (se 1 (by rfl) ⟨14918012, by rfl⟩ : syracuseStep 19890683 = 29836025) B29836025
theorem B11043377 : Blo 1453546 11043377 := bstep (se 2 (by rfl) ⟨4141266, by rfl⟩ : syracuseStep 11043377 = 8282533) B8282533
theorem B4907627 : Blo 1453546 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B27272011 : Blo 1453546 27272011 := bstep (se 1 (by rfl) ⟨20454008, by rfl⟩ : syracuseStep 27272011 = 40908017) B40908017
theorem B4908221 : Blo 1453546 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B9323849 : Blo 1453546 9323849 := bstep (se 2 (by rfl) ⟨3496443, by rfl⟩ : syracuseStep 9323849 = 6992887) B6992887
theorem B2180507 : Blo 1453546 2180507 := bstep (se 1 (by rfl) ⟨1635380, by rfl⟩ : syracuseStep 2180507 = 3270761) B3270761
theorem B17696171 : Blo 1453546 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B2180729 : Blo 1453546 2180729 := bstep (se 2 (by rfl) ⟨817773, by rfl⟩ : syracuseStep 2180729 = 1635547) B1635547
theorem B2180831 : Blo 1453546 2180831 := bstep (se 1 (by rfl) ⟨1635623, by rfl⟩ : syracuseStep 2180831 = 3271247) B3271247
theorem B20186909 : Blo 1453546 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B2180927 : Blo 1453546 2180927 := bstep (se 1 (by rfl) ⟨1635695, by rfl⟩ : syracuseStep 2180927 = 3271391) B3271391
theorem B7087945 : Blo 1453546 7087945 := bstep (se 2 (by rfl) ⟨2657979, by rfl⟩ : syracuseStep 7087945 = 5315959) B5315959
theorem B5244751 : Blo 1453546 5244751 := bstep (se 1 (by rfl) ⟨3933563, by rfl⟩ : syracuseStep 5244751 = 7867127) B7867127
theorem B8283991 : Blo 1453546 8283991 := bstep (se 1 (by rfl) ⟨6212993, by rfl⟩ : syracuseStep 8283991 = 12425987) B12425987
theorem B5523329 : Blo 1453546 5523329 := bstep (se 2 (by rfl) ⟨2071248, by rfl⟩ : syracuseStep 5523329 = 4142497) B4142497
theorem B23603075 : Blo 1453546 23603075 := bstep (se 1 (by rfl) ⟨17702306, by rfl⟩ : syracuseStep 23603075 = 35404613) B35404613
theorem B23578543 : Blo 1453546 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B3270599 : Blo 1453546 3270599 := bstep (se 1 (by rfl) ⟨2452949, by rfl⟩ : syracuseStep 3270599 = 4905899) B4905899
theorem B8849351 : Blo 1453546 8849351 := bstep (se 1 (by rfl) ⟨6637013, by rfl⟩ : syracuseStep 8849351 = 13274027) B13274027
theorem B2181095 : Blo 1453546 2181095 := bstep (se 1 (by rfl) ⟨1635821, by rfl⟩ : syracuseStep 2181095 = 3271643) B3271643
theorem B2762743 : Blo 1453546 2762743 := bstep (se 1 (by rfl) ⟨2072057, by rfl⟩ : syracuseStep 2762743 = 4144115) B4144115
theorem B2181113 : Blo 1453546 2181113 := bstep (se 2 (by rfl) ⟨817917, by rfl⟩ : syracuseStep 2181113 = 1635835) B1635835
theorem B2181215 : Blo 1453546 2181215 := bstep (se 1 (by rfl) ⟨1635911, by rfl⟩ : syracuseStep 2181215 = 3271823) B3271823
theorem B2181275 : Blo 1453546 2181275 := bstep (se 1 (by rfl) ⟨1635956, by rfl⟩ : syracuseStep 2181275 = 3271913) B3271913
theorem B2181311 : Blo 1453546 2181311 := bstep (se 1 (by rfl) ⟨1635983, by rfl⟩ : syracuseStep 2181311 = 3271967) B3271967
theorem B4909247 : Blo 1453546 4909247 := bstep (se 1 (by rfl) ⟨3681935, by rfl⟩ : syracuseStep 4909247 = 7363871) B7363871
theorem B2181353 : Blo 1453546 2181353 := bstep (se 2 (by rfl) ⟨818007, by rfl⟩ : syracuseStep 2181353 = 1636015) B1636015
theorem B3270905 : Blo 1453546 3270905 := bstep (se 2 (by rfl) ⟨1226589, by rfl⟩ : syracuseStep 3270905 = 2453179) B2453179
theorem B2763047 : Blo 1453546 2763047 := bstep (se 1 (by rfl) ⟨2072285, by rfl⟩ : syracuseStep 2763047 = 4144571) B4144571
theorem B3270959 : Blo 1453546 3270959 := bstep (se 1 (by rfl) ⟨2453219, by rfl⟩ : syracuseStep 3270959 = 4906439) B4906439
theorem B3271175 : Blo 1453546 3271175 := bstep (se 1 (by rfl) ⟨2453381, by rfl⟩ : syracuseStep 3271175 = 4906763) B4906763
theorem B3107335 : Blo 1453546 3107335 := bstep (se 1 (by rfl) ⟨2330501, by rfl⟩ : syracuseStep 3107335 = 4661003) B4661003
theorem B2181659 : Blo 1453546 2181659 := bstep (se 1 (by rfl) ⟨1636244, by rfl⟩ : syracuseStep 2181659 = 3272489) B3272489
theorem B3680873 : Blo 1453546 3680873 := bstep (se 2 (by rfl) ⟨1380327, by rfl⟩ : syracuseStep 3680873 = 2760655) B2760655
theorem B2181737 : Blo 1453546 2181737 := bstep (se 2 (by rfl) ⟨818151, by rfl⟩ : syracuseStep 2181737 = 1636303) B1636303
theorem B37292723 : Blo 1453546 37292723 := bstep (se 1 (by rfl) ⟨27969542, by rfl⟩ : syracuseStep 37292723 = 55939085) B55939085
theorem B4139707 : Blo 1453546 4139707 := bstep (se 1 (by rfl) ⟨3104780, by rfl⟩ : syracuseStep 4139707 = 6209561) B6209561
theorem B3271355 : Blo 1453546 3271355 := bstep (se 1 (by rfl) ⟨2453516, by rfl⟩ : syracuseStep 3271355 = 4907033) B4907033
theorem B6212447 : Blo 1453546 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B9317339 : Blo 1453546 9317339 := bstep (se 1 (by rfl) ⟨6988004, by rfl⟩ : syracuseStep 9317339 = 13976009) B13976009
theorem B2182265 : Blo 1453546 2182265 := bstep (se 2 (by rfl) ⟨818349, by rfl⟩ : syracuseStep 2182265 = 1636699) B1636699
theorem B2182367 : Blo 1453546 2182367 := bstep (se 1 (by rfl) ⟨1636775, by rfl⟩ : syracuseStep 2182367 = 3273551) B3273551
theorem B2182409 : Blo 1453546 2182409 := bstep (se 2 (by rfl) ⟨818403, by rfl⟩ : syracuseStep 2182409 = 1636807) B1636807
theorem B2182511 : Blo 1453546 2182511 := bstep (se 1 (by rfl) ⟨1636883, by rfl⟩ : syracuseStep 2182511 = 3273767) B3273767
theorem B262016441 : Blo 1453546 262016441 := bstep (se 2 (by rfl) ⟨98256165, by rfl⟩ : syracuseStep 262016441 = 196512331) B196512331
theorem B2182631 : Blo 1453546 2182631 := bstep (se 1 (by rfl) ⟨1636973, by rfl⟩ : syracuseStep 2182631 = 3273947) B3273947
theorem B3272183 : Blo 1453546 3272183 := bstep (se 1 (by rfl) ⟨2454137, by rfl⟩ : syracuseStep 3272183 = 4908275) B4908275
theorem B3272255 : Blo 1453546 3272255 := bstep (se 1 (by rfl) ⟨2454191, by rfl⟩ : syracuseStep 3272255 = 4908383) B4908383
theorem B1453659 : Blo 1453546 1453659 := bstep (se 1 (by rfl) ⟨1090244, by rfl⟩ : syracuseStep 1453659 = 2180489) B2180489
theorem B2182763 : Blo 1453546 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B2182889 : Blo 1453546 2182889 := bstep (se 2 (by rfl) ⟨818583, by rfl⟩ : syracuseStep 2182889 = 1637167) B1637167
theorem B4910867 : Blo 1453546 4910867 := bstep (se 1 (by rfl) ⟨3683150, by rfl⟩ : syracuseStep 4910867 = 7366301) B7366301
theorem B2453287 : Blo 1453546 2453287 := bstep (se 1 (by rfl) ⟨1839965, by rfl⟩ : syracuseStep 2453287 = 3679931) B3679931
theorem B1453895 : Blo 1453546 1453895 := bstep (se 1 (by rfl) ⟨1090421, by rfl⟩ : syracuseStep 1453895 = 2180843) B2180843
theorem B3682169 : Blo 1453546 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B2183033 : Blo 1453546 2183033 := bstep (se 2 (by rfl) ⟨818637, by rfl⟩ : syracuseStep 2183033 = 1637275) B1637275
theorem B6991771 : Blo 1453546 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B9957275 : Blo 1453546 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B1454047 : Blo 1453546 1454047 := bstep (se 1 (by rfl) ⟨1090535, by rfl⟩ : syracuseStep 1454047 = 2181071) B2181071
theorem B2183135 : Blo 1453546 2183135 := bstep (se 1 (by rfl) ⟨1637351, by rfl⟩ : syracuseStep 2183135 = 3274703) B3274703
theorem B16797721 : Blo 1453546 16797721 := bstep (se 2 (by rfl) ⟨6299145, by rfl⟩ : syracuseStep 16797721 = 12598291) B12598291
theorem B1454311 : Blo 1453546 1454311 := bstep (se 1 (by rfl) ⟨1090733, by rfl⟩ : syracuseStep 1454311 = 2181467) B2181467
theorem B4141439 : Blo 1453546 4141439 := bstep (se 1 (by rfl) ⟨3106079, by rfl⟩ : syracuseStep 4141439 = 6212159) B6212159
theorem B1454463 : Blo 1453546 1454463 := bstep (se 1 (by rfl) ⟨1090847, by rfl⟩ : syracuseStep 1454463 = 2181695) B2181695
theorem B8843687 : Blo 1453546 8843687 := bstep (se 1 (by rfl) ⟨6632765, by rfl⟩ : syracuseStep 8843687 = 13265531) B13265531
theorem B1454543 : Blo 1453546 1454543 := bstep (se 1 (by rfl) ⟨1090907, by rfl⟩ : syracuseStep 1454543 = 2181815) B2181815
theorem B3273209 : Blo 1453546 3273209 := bstep (se 2 (by rfl) ⟨1227453, by rfl⟩ : syracuseStep 3273209 = 2454907) B2454907
theorem B3273299 : Blo 1453546 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B4420199 : Blo 1453546 4420199 := bstep (se 1 (by rfl) ⟨3315149, by rfl⟩ : syracuseStep 4420199 = 6630299) B6630299
theorem B1454695 : Blo 1453546 1454695 := bstep (se 1 (by rfl) ⟨1091021, by rfl⟩ : syracuseStep 1454695 = 2182043) B2182043
theorem B6214259 : Blo 1453546 6214259 := bstep (se 1 (by rfl) ⟨4660694, by rfl⟩ : syracuseStep 6214259 = 9321389) B9321389
theorem B4911731 : Blo 1453546 4911731 := bstep (se 1 (by rfl) ⟨3683798, by rfl⟩ : syracuseStep 4911731 = 7367597) B7367597
theorem B3273479 : Blo 1453546 3273479 := bstep (se 1 (by rfl) ⟨2455109, by rfl⟩ : syracuseStep 3273479 = 4910219) B4910219
theorem B2454313 : Blo 1453546 2454313 := bstep (se 2 (by rfl) ⟨920367, by rfl⟩ : syracuseStep 2454313 = 1840735) B1840735
theorem B1454959 : Blo 1453546 1454959 := bstep (se 1 (by rfl) ⟨1091219, by rfl⟩ : syracuseStep 1454959 = 2182439) B2182439
theorem B4912001 : Blo 1453546 4912001 := bstep (se 2 (by rfl) ⟨1842000, by rfl⟩ : syracuseStep 4912001 = 3684001) B3684001
theorem B1455015 : Blo 1453546 1455015 := bstep (se 1 (by rfl) ⟨1091261, by rfl⟩ : syracuseStep 1455015 = 2182523) B2182523
theorem B1455099 : Blo 1453546 1455099 := bstep (se 1 (by rfl) ⟨1091324, by rfl⟩ : syracuseStep 1455099 = 2182649) B2182649
theorem B3929143 : Blo 1453546 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B2454583 : Blo 1453546 2454583 := bstep (se 1 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 2454583 = 3681875) B3681875
theorem B1455167 : Blo 1453546 1455167 := bstep (se 1 (by rfl) ⟨1091375, by rfl⟩ : syracuseStep 1455167 = 2182751) B2182751
theorem B1455311 : Blo 1453546 1455311 := bstep (se 1 (by rfl) ⟨1091483, by rfl⟩ : syracuseStep 1455311 = 2182967) B2182967
theorem B13981081 : Blo 1453546 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B1455515 : Blo 1453546 1455515 := bstep (se 1 (by rfl) ⟨1091636, by rfl⟩ : syracuseStep 1455515 = 2183273) B2183273
theorem B141481403 : Blo 1453546 141481403 := bstep (se 1 (by rfl) ⟨106111052, by rfl⟩ : syracuseStep 141481403 = 212222105) B212222105
theorem B55899719 : Blo 1453546 55899719 := bstep (se 1 (by rfl) ⟨41924789, by rfl⟩ : syracuseStep 55899719 = 83849579) B83849579
theorem B2070127 : Blo 1453546 2070127 := bstep (se 1 (by rfl) ⟨1552595, by rfl⟩ : syracuseStep 2070127 = 3105191) B3105191
theorem B13981355 : Blo 1453546 13981355 := bstep (se 1 (by rfl) ⟨10486016, by rfl⟩ : syracuseStep 13981355 = 20972033) B20972033
theorem B2070235 : Blo 1453546 2070235 := bstep (se 1 (by rfl) ⟨1552676, by rfl⟩ : syracuseStep 2070235 = 3105353) B3105353
theorem B1636159 : Blo 1453546 1636159 := bstep (se 1 (by rfl) ⟨1227119, by rfl⟩ : syracuseStep 1636159 = 2454239) B2454239
theorem B3274559 : Blo 1453546 3274559 := bstep (se 1 (by rfl) ⟨2455919, by rfl⟩ : syracuseStep 3274559 = 4911839) B4911839
theorem B2455535 : Blo 1453546 2455535 := bstep (se 1 (by rfl) ⟨1841651, by rfl⟩ : syracuseStep 2455535 = 3683303) B3683303
theorem B13981697 : Blo 1453546 13981697 := bstep (se 2 (by rfl) ⟨5243136, by rfl⟩ : syracuseStep 13981697 = 10486273) B10486273
theorem B31447055 : Blo 1453546 31447055 := bstep (se 1 (by rfl) ⟨23585291, by rfl⟩ : syracuseStep 31447055 = 47170583) B47170583
theorem B1636447 : Blo 1453546 1636447 := bstep (se 1 (by rfl) ⟨1227335, by rfl⟩ : syracuseStep 1636447 = 2454671) B2454671
theorem B19421279 : Blo 1453546 19421279 := bstep (se 1 (by rfl) ⟨14565959, by rfl⟩ : syracuseStep 19421279 = 29131919) B29131919
theorem B3274847 : Blo 1453546 3274847 := bstep (se 1 (by rfl) ⟨2456135, by rfl⟩ : syracuseStep 3274847 = 4912271) B4912271
theorem B1865963 : Blo 1453546 1865963 := bstep (se 1 (by rfl) ⟨1399472, by rfl⟩ : syracuseStep 1865963 = 2798945) B2798945
theorem B5519623 : Blo 1453546 5519623 := bstep (se 1 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 5519623 = 8279435) B8279435
theorem B6986159 : Blo 1453546 6986159 := bstep (se 1 (by rfl) ⟨5239619, by rfl⟩ : syracuseStep 6986159 = 10479239) B10479239
theorem B2456095 : Blo 1453546 2456095 := bstep (se 1 (by rfl) ⟨1842071, by rfl⟩ : syracuseStep 2456095 = 3684143) B3684143
theorem B8288891 : Blo 1453546 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B6298249 : Blo 1453546 6298249 := bstep (se 2 (by rfl) ⟨2361843, by rfl⟩ : syracuseStep 6298249 = 4723687) B4723687
theorem B11041433 : Blo 1453546 11041433 := bstep (se 2 (by rfl) ⟨4140537, by rfl⟩ : syracuseStep 11041433 = 8281075) B8281075
theorem B4143773 : Blo 1453546 4143773 := bstep (se 3 (by rfl) ⟨776957, by rfl⟩ : syracuseStep 4143773 = 1553915) B1553915
theorem B5520095 : Blo 1453546 5520095 := bstep (se 1 (by rfl) ⟨4140071, by rfl⟩ : syracuseStep 5520095 = 8280143) B8280143
theorem B4143955 : Blo 1453546 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B4905953 : Blo 1453546 4905953 := bstep (se 2 (by rfl) ⟨1839732, by rfl⟩ : syracuseStep 4905953 = 3679465) B3679465
theorem B7363709 : Blo 1453546 7363709 := bstep (se 3 (by rfl) ⟨1380695, by rfl⟩ : syracuseStep 7363709 = 2761391) B2761391
theorem B4906169 : Blo 1453546 4906169 := bstep (se 2 (by rfl) ⟨1839813, by rfl⟩ : syracuseStep 4906169 = 3679627) B3679627
theorem B6987005 : Blo 1453546 6987005 := bstep (se 3 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 6987005 = 2620127) B2620127
theorem B7863581 : Blo 1453546 7863581 := bstep (se 3 (by rfl) ⟨1474421, by rfl⟩ : syracuseStep 7863581 = 2948843) B2948843
theorem B8289641 : Blo 1453546 8289641 := bstep (se 2 (by rfl) ⟨3108615, by rfl⟩ : syracuseStep 8289641 = 6217231) B6217231
theorem B18644417 : Blo 1453546 18644417 := bstep (se 2 (by rfl) ⟨6991656, by rfl⟩ : syracuseStep 18644417 = 13983313) B13983313
theorem B8961803 : Blo 1453546 8961803 := bstep (se 1 (by rfl) ⟨6721352, by rfl⟩ : syracuseStep 8961803 = 13442705) B13442705
theorem B2760571 : Blo 1453546 2760571 := bstep (se 1 (by rfl) ⟨2070428, by rfl⟩ : syracuseStep 2760571 = 4140857) B4140857
theorem B2211707 : Blo 1453546 2211707 := bstep (se 1 (by rfl) ⟨1658780, by rfl⟩ : syracuseStep 2211707 = 3317561) B3317561
theorem B22396961 : Blo 1453546 22396961 := bstep (se 2 (by rfl) ⟨8398860, by rfl⟩ : syracuseStep 22396961 = 16797721) B16797721
theorem B5046457 : Blo 1453546 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B6209783 : Blo 1453546 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B2760959 : Blo 1453546 2760959 := bstep (se 1 (by rfl) ⟨2070719, by rfl⟩ : syracuseStep 2760959 = 4141439) B4141439
theorem B2621735 : Blo 1453546 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B8397665 : Blo 1453546 8397665 := bstep (se 2 (by rfl) ⟨3149124, by rfl⟩ : syracuseStep 8397665 = 6298249) B6298249
theorem B37266479 : Blo 1453546 37266479 := bstep (se 1 (by rfl) ⟨27949859, by rfl⟩ : syracuseStep 37266479 = 55899719) B55899719
theorem B2180399 : Blo 1453546 2180399 := bstep (se 1 (by rfl) ⟨1635299, by rfl⟩ : syracuseStep 2180399 = 3270599) B3270599
theorem B5899567 : Blo 1453546 5899567 := bstep (se 1 (by rfl) ⟨4424675, by rfl⟩ : syracuseStep 5899567 = 8849351) B8849351
theorem B20964703 : Blo 1453546 20964703 := bstep (se 1 (by rfl) ⟨15723527, by rfl⟩ : syracuseStep 20964703 = 31447055) B31447055
theorem B2180603 : Blo 1453546 2180603 := bstep (se 1 (by rfl) ⟨1635452, by rfl⟩ : syracuseStep 2180603 = 3270905) B3270905
theorem B2180639 : Blo 1453546 2180639 := bstep (se 1 (by rfl) ⟨1635479, by rfl⟩ : syracuseStep 2180639 = 3270959) B3270959
theorem B2180783 : Blo 1453546 2180783 := bstep (se 1 (by rfl) ⟨1635587, by rfl⟩ : syracuseStep 2180783 = 3271175) B3271175
theorem B2762515 : Blo 1453546 2762515 := bstep (se 1 (by rfl) ⟨2071886, by rfl⟩ : syracuseStep 2762515 = 4143773) B4143773
theorem B2180903 : Blo 1453546 2180903 := bstep (se 1 (by rfl) ⟨1635677, by rfl⟩ : syracuseStep 2180903 = 3271355) B3271355
theorem B3680063 : Blo 1453546 3680063 := bstep (se 1 (by rfl) ⟨2760047, by rfl⟩ : syracuseStep 3680063 = 5520095) B5520095
theorem B6211559 : Blo 1453546 6211559 := bstep (se 1 (by rfl) ⟨4658669, by rfl⟩ : syracuseStep 6211559 = 9317339) B9317339
theorem B3270635 : Blo 1453546 3270635 := bstep (se 1 (by rfl) ⟨2452976, by rfl⟩ : syracuseStep 3270635 = 4905953) B4905953
theorem B4909139 : Blo 1453546 4909139 := bstep (se 1 (by rfl) ⟨3681854, by rfl⟩ : syracuseStep 4909139 = 7363709) B7363709
theorem B3270779 : Blo 1453546 3270779 := bstep (se 1 (by rfl) ⟨2453084, by rfl⟩ : syracuseStep 3270779 = 4906169) B4906169
theorem B12429611 : Blo 1453546 12429611 := bstep (se 1 (by rfl) ⟨9322208, by rfl⟩ : syracuseStep 12429611 = 18644417) B18644417
theorem B2181455 : Blo 1453546 2181455 := bstep (se 1 (by rfl) ⟨1636091, by rfl⟩ : syracuseStep 2181455 = 3272183) B3272183
theorem B2181503 : Blo 1453546 2181503 := bstep (se 1 (by rfl) ⟨1636127, by rfl⟩ : syracuseStep 2181503 = 3272255) B3272255
theorem B3271049 : Blo 1453546 3271049 := bstep (se 2 (by rfl) ⟨1226643, by rfl⟩ : syracuseStep 3271049 = 2453287) B2453287
theorem B2181545 : Blo 1453546 2181545 := bstep (se 2 (by rfl) ⟨818079, by rfl⟩ : syracuseStep 2181545 = 1636159) B1636159
theorem B11045321 : Blo 1453546 11045321 := bstep (se 2 (by rfl) ⟨4141995, by rfl⟩ : syracuseStep 11045321 = 8283991) B8283991
theorem B3680761 : Blo 1453546 3680761 := bstep (se 2 (by rfl) ⟨1380285, by rfl⟩ : syracuseStep 3680761 = 2760571) B2760571
theorem B5974535 : Blo 1453546 5974535 := bstep (se 1 (by rfl) ⟨4480901, by rfl⟩ : syracuseStep 5974535 = 8961803) B8961803
theorem B6638183 : Blo 1453546 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B2181929 : Blo 1453546 2181929 := bstep (se 2 (by rfl) ⟨818223, by rfl⟩ : syracuseStep 2181929 = 1636447) B1636447
theorem B3681247 : Blo 1453546 3681247 := bstep (se 1 (by rfl) ⟨2760935, by rfl⟩ : syracuseStep 3681247 = 5521871) B5521871
theorem B2182139 : Blo 1453546 2182139 := bstep (se 1 (by rfl) ⟨1636604, by rfl⟩ : syracuseStep 2182139 = 3273209) B3273209
theorem B7359497 : Blo 1453546 7359497 := bstep (se 2 (by rfl) ⟨2759811, by rfl⟩ : syracuseStep 7359497 = 5519623) B5519623
theorem B2182199 : Blo 1453546 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B3271751 : Blo 1453546 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B3681409 : Blo 1453546 3681409 := bstep (se 2 (by rfl) ⟨1380528, by rfl⟩ : syracuseStep 3681409 = 2761057) B2761057
theorem B2182319 : Blo 1453546 2182319 := bstep (se 1 (by rfl) ⟨1636739, by rfl⟩ : syracuseStep 2182319 = 3273479) B3273479
theorem B4975901 : Blo 1453546 4975901 := bstep (se 3 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 4975901 = 1865963) B1865963
theorem B3272147 : Blo 1453546 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B1453671 : Blo 1453546 1453671 := bstep (se 1 (by rfl) ⟨1090253, by rfl⟩ : syracuseStep 1453671 = 2180507) B2180507
theorem B3272417 : Blo 1453546 3272417 := bstep (se 2 (by rfl) ⟨1227156, by rfl⟩ : syracuseStep 3272417 = 2454313) B2454313
theorem B1453819 : Blo 1453546 1453819 := bstep (se 1 (by rfl) ⟨1090364, by rfl⟩ : syracuseStep 1453819 = 2180729) B2180729
theorem B5525273 : Blo 1453546 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B47189789 : Blo 1453546 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B1453887 : Blo 1453546 1453887 := bstep (se 1 (by rfl) ⟨1090415, by rfl⟩ : syracuseStep 1453887 = 2180831) B2180831
theorem B1453951 : Blo 1453546 1453951 := bstep (se 1 (by rfl) ⟨1090463, by rfl⟩ : syracuseStep 1453951 = 2180927) B2180927
theorem B2183039 : Blo 1453546 2183039 := bstep (se 1 (by rfl) ⟨1637279, by rfl⟩ : syracuseStep 2183039 = 3274559) B3274559
theorem B3682219 : Blo 1453546 3682219 := bstep (se 1 (by rfl) ⟨2761664, by rfl⟩ : syracuseStep 3682219 = 5523329) B5523329
theorem B1454063 : Blo 1453546 1454063 := bstep (se 1 (by rfl) ⟨1090547, by rfl⟩ : syracuseStep 1454063 = 2181095) B2181095
theorem B1454075 : Blo 1453546 1454075 := bstep (se 1 (by rfl) ⟨1090556, by rfl⟩ : syracuseStep 1454075 = 2181113) B2181113
theorem B1454143 : Blo 1453546 1454143 := bstep (se 1 (by rfl) ⟨1090607, by rfl⟩ : syracuseStep 1454143 = 2181215) B2181215
theorem B12947519 : Blo 1453546 12947519 := bstep (se 1 (by rfl) ⟨9710639, by rfl⟩ : syracuseStep 12947519 = 19421279) B19421279
theorem B2183231 : Blo 1453546 2183231 := bstep (se 1 (by rfl) ⟨1637423, by rfl⟩ : syracuseStep 2183231 = 3274847) B3274847
theorem B5238857 : Blo 1453546 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B3272777 : Blo 1453546 3272777 := bstep (se 2 (by rfl) ⟨1227291, by rfl⟩ : syracuseStep 3272777 = 2454583) B2454583
theorem B1454183 : Blo 1453546 1454183 := bstep (se 1 (by rfl) ⟨1090637, by rfl⟩ : syracuseStep 1454183 = 2181275) B2181275
theorem B1454207 : Blo 1453546 1454207 := bstep (se 1 (by rfl) ⟨1090655, by rfl⟩ : syracuseStep 1454207 = 2181311) B2181311
theorem B3272831 : Blo 1453546 3272831 := bstep (se 1 (by rfl) ⟨2454623, by rfl⟩ : syracuseStep 3272831 = 4909247) B4909247
theorem B1454235 : Blo 1453546 1454235 := bstep (se 1 (by rfl) ⟨1090676, by rfl⟩ : syracuseStep 1454235 = 2181353) B2181353
theorem B4657439 : Blo 1453546 4657439 := bstep (se 1 (by rfl) ⟨3493079, by rfl⟩ : syracuseStep 4657439 = 6986159) B6986159
theorem B1454439 : Blo 1453546 1454439 := bstep (se 1 (by rfl) ⟨1090829, by rfl⟩ : syracuseStep 1454439 = 2181659) B2181659
theorem B2453915 : Blo 1453546 2453915 := bstep (se 1 (by rfl) ⟨1840436, by rfl⟩ : syracuseStep 2453915 = 3680873) B3680873
theorem B1454491 : Blo 1453546 1454491 := bstep (se 1 (by rfl) ⟨1090868, by rfl⟩ : syracuseStep 1454491 = 2181737) B2181737
theorem B5525927 : Blo 1453546 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B7360955 : Blo 1453546 7360955 := bstep (se 1 (by rfl) ⟨5520716, by rfl⟩ : syracuseStep 7360955 = 11041433) B11041433
theorem B18641441 : Blo 1453546 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B4141631 : Blo 1453546 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B1454843 : Blo 1453546 1454843 := bstep (se 1 (by rfl) ⟨1091132, by rfl⟩ : syracuseStep 1454843 = 2182265) B2182265
theorem B1454911 : Blo 1453546 1454911 := bstep (se 1 (by rfl) ⟨1091183, by rfl⟩ : syracuseStep 1454911 = 2182367) B2182367
theorem B4658003 : Blo 1453546 4658003 := bstep (se 1 (by rfl) ⟨3493502, by rfl⟩ : syracuseStep 4658003 = 6987005) B6987005
theorem B1454939 : Blo 1453546 1454939 := bstep (se 1 (by rfl) ⟨1091204, by rfl⟩ : syracuseStep 1454939 = 2182409) B2182409
theorem B5526427 : Blo 1453546 5526427 := bstep (se 1 (by rfl) ⟨4144820, by rfl⟩ : syracuseStep 5526427 = 8289641) B8289641
theorem B1455007 : Blo 1453546 1455007 := bstep (se 1 (by rfl) ⟨1091255, by rfl⟩ : syracuseStep 1455007 = 2182511) B2182511
theorem B1455087 : Blo 1453546 1455087 := bstep (se 1 (by rfl) ⟨1091315, by rfl⟩ : syracuseStep 1455087 = 2182631) B2182631
theorem B1455175 : Blo 1453546 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B9450593 : Blo 1453546 9450593 := bstep (se 2 (by rfl) ⟨3543972, by rfl⟩ : syracuseStep 9450593 = 7087945) B7087945
theorem B6993001 : Blo 1453546 6993001 := bstep (se 2 (by rfl) ⟨2622375, by rfl⟩ : syracuseStep 6993001 = 5244751) B5244751
theorem B1455259 : Blo 1453546 1455259 := bstep (se 1 (by rfl) ⟨1091444, by rfl⟩ : syracuseStep 1455259 = 2182889) B2182889
theorem B3273911 : Blo 1453546 3273911 := bstep (se 1 (by rfl) ⟨2455433, by rfl⟩ : syracuseStep 3273911 = 4910867) B4910867
theorem B31438057 : Blo 1453546 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B2454779 : Blo 1453546 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B1455355 : Blo 1453546 1455355 := bstep (se 1 (by rfl) ⟨1091516, by rfl⟩ : syracuseStep 1455355 = 2183033) B2183033
theorem B1455423 : Blo 1453546 1455423 := bstep (se 1 (by rfl) ⟨1091567, by rfl⟩ : syracuseStep 1455423 = 2183135) B2183135
theorem B3683657 : Blo 1453546 3683657 := bstep (se 2 (by rfl) ⟨1381371, by rfl⟩ : syracuseStep 3683657 = 2762743) B2762743
theorem B4658543 : Blo 1453546 4658543 := bstep (se 1 (by rfl) ⟨3493907, by rfl⟩ : syracuseStep 4658543 = 6987815) B6987815
theorem B5895791 : Blo 1453546 5895791 := bstep (se 1 (by rfl) ⟨4421843, by rfl⟩ : syracuseStep 5895791 = 8843687) B8843687
theorem B13260455 : Blo 1453546 13260455 := bstep (se 1 (by rfl) ⟨9945341, by rfl⟩ : syracuseStep 13260455 = 19890683) B19890683
theorem B7362251 : Blo 1453546 7362251 := bstep (se 1 (by rfl) ⟨5521688, by rfl⟩ : syracuseStep 7362251 = 11043377) B11043377
theorem B2946799 : Blo 1453546 2946799 := bstep (se 1 (by rfl) ⟨2210099, by rfl⟩ : syracuseStep 2946799 = 4420199) B4420199
theorem B4142839 : Blo 1453546 4142839 := bstep (se 1 (by rfl) ⟨3107129, by rfl⟩ : syracuseStep 4142839 = 6214259) B6214259
theorem B3274487 : Blo 1453546 3274487 := bstep (se 1 (by rfl) ⟨2455865, by rfl⟩ : syracuseStep 3274487 = 4911731) B4911731
theorem B3274667 : Blo 1453546 3274667 := bstep (se 1 (by rfl) ⟨2456000, by rfl⟩ : syracuseStep 3274667 = 4912001) B4912001
theorem B4143113 : Blo 1453546 4143113 := bstep (se 2 (by rfl) ⟨1553667, by rfl⟩ : syracuseStep 4143113 = 3107335) B3107335
theorem B3274793 : Blo 1453546 3274793 := bstep (se 2 (by rfl) ⟨1228047, by rfl⟩ : syracuseStep 3274793 = 2456095) B2456095
theorem B20969549 : Blo 1453546 20969549 := bstep (se 3 (by rfl) ⟨3931790, by rfl⟩ : syracuseStep 20969549 = 7863581) B7863581
theorem B6215899 : Blo 1453546 6215899 := bstep (se 1 (by rfl) ⟨4661924, by rfl⟩ : syracuseStep 6215899 = 9323849) B9323849
theorem B5519609 : Blo 1453546 5519609 := bstep (se 2 (by rfl) ⟨2069853, by rfl⟩ : syracuseStep 5519609 = 4139707) B4139707
theorem B94320935 : Blo 1453546 94320935 := bstep (se 1 (by rfl) ⟨70740701, by rfl⟩ : syracuseStep 94320935 = 141481403) B141481403
theorem B36362681 : Blo 1453546 36362681 := bstep (se 2 (by rfl) ⟨13636005, by rfl⟩ : syracuseStep 36362681 = 27272011) B27272011
theorem B9320903 : Blo 1453546 9320903 := bstep (se 1 (by rfl) ⟨6990677, by rfl⟩ : syracuseStep 9320903 = 13981355) B13981355
theorem B13457939 : Blo 1453546 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B15735383 : Blo 1453546 15735383 := bstep (se 1 (by rfl) ⟨11801537, by rfl⟩ : syracuseStep 15735383 = 23603075) B23603075
theorem B1637023 : Blo 1453546 1637023 := bstep (se 1 (by rfl) ⟨1227767, by rfl⟩ : syracuseStep 1637023 = 2455535) B2455535
theorem B9321131 : Blo 1453546 9321131 := bstep (se 1 (by rfl) ⟨6990848, by rfl⟩ : syracuseStep 9321131 = 13981697) B13981697
theorem B1842031 : Blo 1453546 1842031 := bstep (se 1 (by rfl) ⟨1381523, by rfl⟩ : syracuseStep 1842031 = 2763047) B2763047
theorem B24861815 : Blo 1453546 24861815 := bstep (se 1 (by rfl) ⟨18646361, by rfl⟩ : syracuseStep 24861815 = 37292723) B37292723
theorem B2760169 : Blo 1453546 2760169 := bstep (se 2 (by rfl) ⟨1035063, by rfl⟩ : syracuseStep 2760169 = 2070127) B2070127
theorem B2760313 : Blo 1453546 2760313 := bstep (se 2 (by rfl) ⟨1035117, by rfl⟩ : syracuseStep 2760313 = 2070235) B2070235
theorem B174677627 : Blo 1453546 174677627 := bstep (se 1 (by rfl) ⟨131008220, by rfl⟩ : syracuseStep 174677627 = 262016441) B262016441
theorem B9322361 : Blo 1453546 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B1474471 : Blo 1453546 1474471 := bstep (se 1 (by rfl) ⟨1105853, by rfl⟩ : syracuseStep 1474471 = 2211707) B2211707
theorem B4907303 : Blo 1453546 4907303 := bstep (se 1 (by rfl) ⟨3680477, by rfl⟩ : syracuseStep 4907303 = 7360955) B7360955
theorem B12427627 : Blo 1453546 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B3105335 : Blo 1453546 3105335 := bstep (se 1 (by rfl) ⟨2329001, by rfl⟩ : syracuseStep 3105335 = 4658003) B4658003
theorem B4907681 : Blo 1453546 4907681 := bstep (se 2 (by rfl) ⟨1840380, by rfl⟩ : syracuseStep 4907681 = 3680761) B3680761
theorem B6300395 : Blo 1453546 6300395 := bstep (se 1 (by rfl) ⟨4725296, by rfl⟩ : syracuseStep 6300395 = 9450593) B9450593
theorem B12419837 : Blo 1453546 12419837 := bstep (se 3 (by rfl) ⟨2328719, by rfl⟩ : syracuseStep 12419837 = 4657439) B4657439
theorem B3105695 : Blo 1453546 3105695 := bstep (se 1 (by rfl) ⟨2329271, by rfl⟩ : syracuseStep 3105695 = 4658543) B4658543
theorem B8840303 : Blo 1453546 8840303 := bstep (se 1 (by rfl) ⟨6630227, by rfl⟩ : syracuseStep 8840303 = 13260455) B13260455
theorem B4908167 : Blo 1453546 4908167 := bstep (se 1 (by rfl) ⟨3681125, by rfl⟩ : syracuseStep 4908167 = 7362251) B7362251
theorem B4908329 : Blo 1453546 4908329 := bstep (se 2 (by rfl) ⟨1840623, by rfl⟩ : syracuseStep 4908329 = 3681247) B3681247
theorem B2180423 : Blo 1453546 2180423 := bstep (se 1 (by rfl) ⟨1635317, by rfl⟩ : syracuseStep 2180423 = 3270635) B3270635
theorem B2762075 : Blo 1453546 2762075 := bstep (se 1 (by rfl) ⟨2071556, by rfl⟩ : syracuseStep 2762075 = 4143113) B4143113
theorem B2180519 : Blo 1453546 2180519 := bstep (se 1 (by rfl) ⟨1635389, by rfl⟩ : syracuseStep 2180519 = 3270779) B3270779
theorem B9324001 : Blo 1453546 9324001 := bstep (se 2 (by rfl) ⟨3496500, by rfl⟩ : syracuseStep 9324001 = 6993001) B6993001
theorem B3679739 : Blo 1453546 3679739 := bstep (se 1 (by rfl) ⟨2759804, by rfl⟩ : syracuseStep 3679739 = 5519609) B5519609
theorem B11044349 : Blo 1453546 11044349 := bstep (se 3 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 11044349 = 4141631) B4141631
theorem B4908545 : Blo 1453546 4908545 := bstep (se 2 (by rfl) ⟨1840704, by rfl⟩ : syracuseStep 4908545 = 3681409) B3681409
theorem B2180699 : Blo 1453546 2180699 := bstep (se 1 (by rfl) ⟨1635524, by rfl⟩ : syracuseStep 2180699 = 3271049) B3271049
theorem B24241787 : Blo 1453546 24241787 := bstep (se 1 (by rfl) ⟨18181340, by rfl⟩ : syracuseStep 24241787 = 36362681) B36362681
theorem B3983023 : Blo 1453546 3983023 := bstep (se 1 (by rfl) ⟨2987267, by rfl⟩ : syracuseStep 3983023 = 5974535) B5974535
theorem B7866089 : Blo 1453546 7866089 := bstep (se 2 (by rfl) ⟨2949783, by rfl⟩ : syracuseStep 7866089 = 5899567) B5899567
theorem B4425455 : Blo 1453546 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B27952937 : Blo 1453546 27952937 := bstep (se 2 (by rfl) ⟨10482351, by rfl⟩ : syracuseStep 27952937 = 20964703) B20964703
theorem B3680225 : Blo 1453546 3680225 := bstep (se 2 (by rfl) ⟨1380084, by rfl⟩ : syracuseStep 3680225 = 2760169) B2760169
theorem B2181167 : Blo 1453546 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B16574543 : Blo 1453546 16574543 := bstep (se 1 (by rfl) ⟨12430907, by rfl⟩ : syracuseStep 16574543 = 24861815) B24861815
theorem B3680417 : Blo 1453546 3680417 := bstep (se 2 (by rfl) ⟨1380156, by rfl⟩ : syracuseStep 3680417 = 2760313) B2760313
theorem B2181431 : Blo 1453546 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B5523785 : Blo 1453546 5523785 := bstep (se 2 (by rfl) ⟨2071419, by rfl⟩ : syracuseStep 5523785 = 4142839) B4142839
theorem B116451751 : Blo 1453546 116451751 := bstep (se 1 (by rfl) ⟨87338813, by rfl⟩ : syracuseStep 116451751 = 174677627) B174677627
theorem B2181611 : Blo 1453546 2181611 := bstep (se 1 (by rfl) ⟨1636208, by rfl⟩ : syracuseStep 2181611 = 3272417) B3272417
theorem B31459859 : Blo 1453546 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B4909625 : Blo 1453546 4909625 := bstep (se 2 (by rfl) ⟨1841109, by rfl⟩ : syracuseStep 4909625 = 3682219) B3682219
theorem B3492571 : Blo 1453546 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B2181851 : Blo 1453546 2181851 := bstep (se 1 (by rfl) ⟨1636388, by rfl⟩ : syracuseStep 2181851 = 3272777) B3272777
theorem B2181887 : Blo 1453546 2181887 := bstep (se 1 (by rfl) ⟨1636415, by rfl⟩ : syracuseStep 2181887 = 3272831) B3272831
theorem B4139855 : Blo 1453546 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B1747823 : Blo 1453546 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B143551349 : Blo 1453546 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B6728609 : Blo 1453546 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B5598443 : Blo 1453546 5598443 := bstep (se 1 (by rfl) ⟨4198832, by rfl⟩ : syracuseStep 5598443 = 8397665) B8397665
theorem B2182607 : Blo 1453546 2182607 := bstep (se 1 (by rfl) ⟨1636955, by rfl⟩ : syracuseStep 2182607 = 3273911) B3273911
theorem B1453599 : Blo 1453546 1453599 := bstep (se 1 (by rfl) ⟨1090199, by rfl⟩ : syracuseStep 1453599 = 2180399) B2180399
theorem B2182697 : Blo 1453546 2182697 := bstep (se 2 (by rfl) ⟨818511, by rfl⟩ : syracuseStep 2182697 = 1637023) B1637023
theorem B1453735 : Blo 1453546 1453735 := bstep (se 1 (by rfl) ⟨1090301, by rfl⟩ : syracuseStep 1453735 = 2180603) B2180603
theorem B1453759 : Blo 1453546 1453759 := bstep (se 1 (by rfl) ⟨1090319, by rfl⟩ : syracuseStep 1453759 = 2180639) B2180639
theorem B1453855 : Blo 1453546 1453855 := bstep (se 1 (by rfl) ⟨1090391, by rfl⟩ : syracuseStep 1453855 = 2180783) B2180783
theorem B2182991 : Blo 1453546 2182991 := bstep (se 1 (by rfl) ⟨1637243, by rfl⟩ : syracuseStep 2182991 = 3274487) B3274487
theorem B1453935 : Blo 1453546 1453935 := bstep (se 1 (by rfl) ⟨1090451, by rfl⟩ : syracuseStep 1453935 = 2180903) B2180903
theorem B7368569 : Blo 1453546 7368569 := bstep (se 2 (by rfl) ⟨2763213, by rfl⟩ : syracuseStep 7368569 = 5526427) B5526427
theorem B2453375 : Blo 1453546 2453375 := bstep (se 1 (by rfl) ⟨1840031, by rfl⟩ : syracuseStep 2453375 = 3680063) B3680063
theorem B15716261 : Blo 1453546 15716261 := bstep (se 4 (by rfl) ⟨1473399, by rfl⟩ : syracuseStep 15716261 = 2946799) B2946799
theorem B2183111 : Blo 1453546 2183111 := bstep (se 1 (by rfl) ⟨1637333, by rfl⟩ : syracuseStep 2183111 = 3274667) B3274667
theorem B4141039 : Blo 1453546 4141039 := bstep (se 1 (by rfl) ⟨3105779, by rfl⟩ : syracuseStep 4141039 = 6211559) B6211559
theorem B2183195 : Blo 1453546 2183195 := bstep (se 1 (by rfl) ⟨1637396, by rfl⟩ : syracuseStep 2183195 = 3274793) B3274793
theorem B13979699 : Blo 1453546 13979699 := bstep (se 1 (by rfl) ⟨10484774, by rfl⟩ : syracuseStep 13979699 = 20969549) B20969549
theorem B3272759 : Blo 1453546 3272759 := bstep (se 1 (by rfl) ⟨2454569, by rfl⟩ : syracuseStep 3272759 = 4909139) B4909139
theorem B8286407 : Blo 1453546 8286407 := bstep (se 1 (by rfl) ⟨6214805, by rfl⟩ : syracuseStep 8286407 = 12429611) B12429611
theorem B1454303 : Blo 1453546 1454303 := bstep (se 1 (by rfl) ⟨1090727, by rfl⟩ : syracuseStep 1454303 = 2181455) B2181455
theorem B1454335 : Blo 1453546 1454335 := bstep (se 1 (by rfl) ⟨1090751, by rfl⟩ : syracuseStep 1454335 = 2181503) B2181503
theorem B1454363 : Blo 1453546 1454363 := bstep (se 1 (by rfl) ⟨1090772, by rfl⟩ : syracuseStep 1454363 = 2181545) B2181545
theorem B6213935 : Blo 1453546 6213935 := bstep (se 1 (by rfl) ⟨4660451, by rfl⟩ : syracuseStep 6213935 = 9320903) B9320903
theorem B10490255 : Blo 1453546 10490255 := bstep (se 1 (by rfl) ⟨7867691, by rfl⟩ : syracuseStep 10490255 = 15735383) B15735383
theorem B6214087 : Blo 1453546 6214087 := bstep (se 1 (by rfl) ⟨4660565, by rfl⟩ : syracuseStep 6214087 = 9321131) B9321131
theorem B1454619 : Blo 1453546 1454619 := bstep (se 1 (by rfl) ⟨1090964, by rfl⟩ : syracuseStep 1454619 = 2181929) B2181929
theorem B1454759 : Blo 1453546 1454759 := bstep (se 1 (by rfl) ⟨1091069, by rfl⟩ : syracuseStep 1454759 = 2182139) B2182139
theorem B1454799 : Blo 1453546 1454799 := bstep (se 1 (by rfl) ⟨1091099, by rfl⟩ : syracuseStep 1454799 = 2182199) B2182199
theorem B1454879 : Blo 1453546 1454879 := bstep (se 1 (by rfl) ⟨1091159, by rfl⟩ : syracuseStep 1454879 = 2182319) B2182319
theorem B3683353 : Blo 1453546 3683353 := bstep (se 2 (by rfl) ⟨1381257, by rfl⟩ : syracuseStep 3683353 = 2762515) B2762515
theorem B3683515 : Blo 1453546 3683515 := bstep (se 1 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 3683515 = 5525273) B5525273
theorem B6214907 : Blo 1453546 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B1455359 : Blo 1453546 1455359 := bstep (se 1 (by rfl) ⟨1091519, by rfl⟩ : syracuseStep 1455359 = 2183039) B2183039
theorem B14931307 : Blo 1453546 14931307 := bstep (se 1 (by rfl) ⟨11198480, by rfl⟩ : syracuseStep 14931307 = 22396961) B22396961
theorem B8631679 : Blo 1453546 8631679 := bstep (se 1 (by rfl) ⟨6473759, by rfl⟩ : syracuseStep 8631679 = 12947519) B12947519
theorem B1455487 : Blo 1453546 1455487 := bstep (se 1 (by rfl) ⟨1091615, by rfl⟩ : syracuseStep 1455487 = 2183231) B2183231
theorem B1840639 : Blo 1453546 1840639 := bstep (se 1 (by rfl) ⟨1380479, by rfl⟩ : syracuseStep 1840639 = 2760959) B2760959
theorem B1635943 : Blo 1453546 1635943 := bstep (se 1 (by rfl) ⟨1226957, by rfl⟩ : syracuseStep 1635943 = 2453915) B2453915
theorem B3683951 : Blo 1453546 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B8287865 : Blo 1453546 8287865 := bstep (se 2 (by rfl) ⟨3107949, by rfl⟩ : syracuseStep 8287865 = 6215899) B6215899
theorem B24844319 : Blo 1453546 24844319 := bstep (se 1 (by rfl) ⟨18633239, by rfl⟩ : syracuseStep 24844319 = 37266479) B37266479
theorem B1636519 : Blo 1453546 1636519 := bstep (se 1 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 1636519 = 2454779) B2454779
theorem B2455771 : Blo 1453546 2455771 := bstep (se 1 (by rfl) ⟨1841828, by rfl⟩ : syracuseStep 2455771 = 3683657) B3683657
theorem B3930527 : Blo 1453546 3930527 := bstep (se 1 (by rfl) ⟨2947895, by rfl⟩ : syracuseStep 3930527 = 5895791) B5895791
theorem B2456041 : Blo 1453546 2456041 := bstep (se 2 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 2456041 = 1842031) B1842031
theorem B62880623 : Blo 1453546 62880623 := bstep (se 1 (by rfl) ⟨47160467, by rfl⟩ : syracuseStep 62880623 = 94320935) B94320935
theorem B7363547 : Blo 1453546 7363547 := bstep (se 1 (by rfl) ⟨5522660, by rfl⟩ : syracuseStep 7363547 = 11045321) B11045321
theorem B41917409 : Blo 1453546 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B4906331 : Blo 1453546 4906331 := bstep (se 1 (by rfl) ⟨3679748, by rfl⟩ : syracuseStep 4906331 = 7359497) B7359497
theorem B3317267 : Blo 1453546 3317267 := bstep (se 1 (by rfl) ⟨2487950, by rfl⟩ : syracuseStep 3317267 = 4975901) B4975901
theorem B1965961 : Blo 1453546 1965961 := bstep (se 2 (by rfl) ⟨737235, by rfl⟩ : syracuseStep 1965961 = 1474471) B1474471
theorem B16573085 : Blo 1453546 16573085 := bstep (se 3 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 16573085 = 6214907) B6214907
theorem B5244059 : Blo 1453546 5244059 := bstep (se 1 (by rfl) ⟨3933044, by rfl⟩ : syracuseStep 5244059 = 7866089) B7866089
theorem B20973239 : Blo 1453546 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B41920415 : Blo 1453546 41920415 := bstep (se 1 (by rfl) ⟨31440311, by rfl⟩ : syracuseStep 41920415 = 62880623) B62880623
theorem B95700899 : Blo 1453546 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B4909031 : Blo 1453546 4909031 := bstep (se 1 (by rfl) ⟨3681773, by rfl⟩ : syracuseStep 4909031 = 7363547) B7363547
theorem B27944939 : Blo 1453546 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B2181257 : Blo 1453546 2181257 := bstep (se 2 (by rfl) ⟨817971, by rfl⟩ : syracuseStep 2181257 = 1635943) B1635943
theorem B3270887 : Blo 1453546 3270887 := bstep (se 1 (by rfl) ⟨2453165, by rfl⟩ : syracuseStep 3270887 = 4906331) B4906331
theorem B5310697 : Blo 1453546 5310697 := bstep (se 2 (by rfl) ⟨1991511, by rfl⟩ : syracuseStep 5310697 = 3983023) B3983023
theorem B2181839 : Blo 1453546 2181839 := bstep (se 1 (by rfl) ⟨1636379, by rfl⟩ : syracuseStep 2181839 = 3272759) B3272759
theorem B5524271 : Blo 1453546 5524271 := bstep (se 1 (by rfl) ⟨4143203, by rfl⟩ : syracuseStep 5524271 = 8286407) B8286407
theorem B3271535 : Blo 1453546 3271535 := bstep (se 1 (by rfl) ⟨2453651, by rfl⟩ : syracuseStep 3271535 = 4907303) B4907303
theorem B2182025 : Blo 1453546 2182025 := bstep (se 2 (by rfl) ⟨818259, by rfl⟩ : syracuseStep 2182025 = 1636519) B1636519
theorem B3271787 : Blo 1453546 3271787 := bstep (se 1 (by rfl) ⟨2453840, by rfl⟩ : syracuseStep 3271787 = 4907681) B4907681
theorem B8285449 : Blo 1453546 8285449 := bstep (se 2 (by rfl) ⟨3107043, by rfl⟩ : syracuseStep 8285449 = 6214087) B6214087
theorem B14929181 : Blo 1453546 14929181 := bstep (se 3 (by rfl) ⟨2799221, by rfl⟩ : syracuseStep 14929181 = 5598443) B5598443
theorem B5893535 : Blo 1453546 5893535 := bstep (se 1 (by rfl) ⟨4420151, by rfl⟩ : syracuseStep 5893535 = 8840303) B8840303
theorem B3272111 : Blo 1453546 3272111 := bstep (se 1 (by rfl) ⟨2454083, by rfl⟩ : syracuseStep 3272111 = 4908167) B4908167
theorem B3272219 : Blo 1453546 3272219 := bstep (se 1 (by rfl) ⟨2454164, by rfl⟩ : syracuseStep 3272219 = 4908329) B4908329
theorem B1453615 : Blo 1453546 1453615 := bstep (se 1 (by rfl) ⟨1090211, by rfl⟩ : syracuseStep 1453615 = 2180423) B2180423
theorem B1453679 : Blo 1453546 1453679 := bstep (se 1 (by rfl) ⟨1090259, by rfl⟩ : syracuseStep 1453679 = 2180519) B2180519
theorem B4656761 : Blo 1453546 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B2453159 : Blo 1453546 2453159 := bstep (se 1 (by rfl) ⟨1839869, by rfl⟩ : syracuseStep 2453159 = 3679739) B3679739
theorem B3272363 : Blo 1453546 3272363 := bstep (se 1 (by rfl) ⟨2454272, by rfl⟩ : syracuseStep 3272363 = 4908545) B4908545
theorem B1453799 : Blo 1453546 1453799 := bstep (se 1 (by rfl) ⟨1090349, by rfl⟩ : syracuseStep 1453799 = 2180699) B2180699
theorem B5525243 : Blo 1453546 5525243 := bstep (se 1 (by rfl) ⟨4143932, by rfl⟩ : syracuseStep 5525243 = 8287865) B8287865
theorem B2453483 : Blo 1453546 2453483 := bstep (se 1 (by rfl) ⟨1840112, by rfl⟩ : syracuseStep 2453483 = 3680225) B3680225
theorem B1454111 : Blo 1453546 1454111 := bstep (se 1 (by rfl) ⟨1090583, by rfl⟩ : syracuseStep 1454111 = 2181167) B2181167
theorem B4911137 : Blo 1453546 4911137 := bstep (se 2 (by rfl) ⟨1841676, by rfl⟩ : syracuseStep 4911137 = 3683353) B3683353
theorem B2453611 : Blo 1453546 2453611 := bstep (se 1 (by rfl) ⟨1840208, by rfl⟩ : syracuseStep 2453611 = 3680417) B3680417
theorem B1454287 : Blo 1453546 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B3682523 : Blo 1453546 3682523 := bstep (se 1 (by rfl) ⟨2761892, by rfl⟩ : syracuseStep 3682523 = 5523785) B5523785
theorem B4911353 : Blo 1453546 4911353 := bstep (se 2 (by rfl) ⟨1841757, by rfl⟩ : syracuseStep 4911353 = 3683515) B3683515
theorem B1454407 : Blo 1453546 1454407 := bstep (se 1 (by rfl) ⟨1090805, by rfl⟩ : syracuseStep 1454407 = 2181611) B2181611
theorem B3273083 : Blo 1453546 3273083 := bstep (se 1 (by rfl) ⟨2454812, by rfl⟩ : syracuseStep 3273083 = 4909625) B4909625
theorem B1454567 : Blo 1453546 1454567 := bstep (se 1 (by rfl) ⟨1090925, by rfl⟩ : syracuseStep 1454567 = 2181851) B2181851
theorem B1454591 : Blo 1453546 1454591 := bstep (se 1 (by rfl) ⟨1090943, by rfl⟩ : syracuseStep 1454591 = 2181887) B2181887
theorem B4485739 : Blo 1453546 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B11801213 : Blo 1453546 11801213 := bstep (se 3 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 11801213 = 4425455) B4425455
theorem B12432001 : Blo 1453546 12432001 := bstep (se 2 (by rfl) ⟨4662000, by rfl⟩ : syracuseStep 12432001 = 9324001) B9324001
theorem B2454185 : Blo 1453546 2454185 := bstep (se 2 (by rfl) ⟨920319, by rfl⟩ : syracuseStep 2454185 = 1840639) B1840639
theorem B1455071 : Blo 1453546 1455071 := bstep (se 1 (by rfl) ⟨1091303, by rfl⟩ : syracuseStep 1455071 = 2182607) B2182607
theorem B1455131 : Blo 1453546 1455131 := bstep (se 1 (by rfl) ⟨1091348, by rfl⟩ : syracuseStep 1455131 = 2182697) B2182697
theorem B1455327 : Blo 1453546 1455327 := bstep (se 1 (by rfl) ⟨1091495, by rfl⟩ : syracuseStep 1455327 = 2182991) B2182991
theorem B4912379 : Blo 1453546 4912379 := bstep (se 1 (by rfl) ⟨3684284, by rfl⟩ : syracuseStep 4912379 = 7368569) B7368569
theorem B1635583 : Blo 1453546 1635583 := bstep (se 1 (by rfl) ⟨1226687, by rfl⟩ : syracuseStep 1635583 = 2453375) B2453375
theorem B1455407 : Blo 1453546 1455407 := bstep (se 1 (by rfl) ⟨1091555, by rfl⟩ : syracuseStep 1455407 = 2183111) B2183111
theorem B1455463 : Blo 1453546 1455463 := bstep (se 1 (by rfl) ⟨1091597, by rfl⟩ : syracuseStep 1455463 = 2183195) B2183195
theorem B9319799 : Blo 1453546 9319799 := bstep (se 1 (by rfl) ⟨6989849, by rfl⟩ : syracuseStep 9319799 = 13979699) B13979699
theorem B4142623 : Blo 1453546 4142623 := bstep (se 1 (by rfl) ⟨3106967, by rfl⟩ : syracuseStep 4142623 = 6213935) B6213935
theorem B6993503 : Blo 1453546 6993503 := bstep (se 1 (by rfl) ⟨5245127, by rfl⟩ : syracuseStep 6993503 = 10490255) B10490255
theorem B3274361 : Blo 1453546 3274361 := bstep (se 2 (by rfl) ⟨1227885, by rfl⟩ : syracuseStep 3274361 = 2455771) B2455771
theorem B16570169 : Blo 1453546 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B4200263 : Blo 1453546 4200263 := bstep (se 1 (by rfl) ⟨3150197, by rfl⟩ : syracuseStep 4200263 = 6300395) B6300395
theorem B8279891 : Blo 1453546 8279891 := bstep (se 1 (by rfl) ⟨6209918, by rfl⟩ : syracuseStep 8279891 = 12419837) B12419837
theorem B155269001 : Blo 1453546 155269001 := bstep (se 2 (by rfl) ⟨58225875, by rfl⟩ : syracuseStep 155269001 = 116451751) B116451751
theorem B2070463 : Blo 1453546 2070463 := bstep (se 1 (by rfl) ⟨1552847, by rfl⟩ : syracuseStep 2070463 = 3105695) B3105695
theorem B3274721 : Blo 1453546 3274721 := bstep (se 2 (by rfl) ⟨1228020, by rfl⟩ : syracuseStep 3274721 = 2456041) B2456041
theorem B1841383 : Blo 1453546 1841383 := bstep (se 1 (by rfl) ⟨1381037, by rfl⟩ : syracuseStep 1841383 = 2762075) B2762075
theorem B7362899 : Blo 1453546 7362899 := bstep (se 1 (by rfl) ⟨5522174, by rfl⟩ : syracuseStep 7362899 = 11044349) B11044349
theorem B2455967 : Blo 1453546 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B16161191 : Blo 1453546 16161191 := bstep (se 1 (by rfl) ⟨12120893, by rfl⟩ : syracuseStep 16161191 = 24241787) B24241787
theorem B18643445 : Blo 1453546 18643445 := bstep (se 5 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 18643445 = 1747823) B1747823
theorem B18635291 : Blo 1453546 18635291 := bstep (se 1 (by rfl) ⟨13976468, by rfl⟩ : syracuseStep 18635291 = 27952937) B27952937
theorem B16562879 : Blo 1453546 16562879 := bstep (se 1 (by rfl) ⟨12422159, by rfl⟩ : syracuseStep 16562879 = 24844319) B24844319
theorem B11049695 : Blo 1453546 11049695 := bstep (se 1 (by rfl) ⟨8287271, by rfl⟩ : syracuseStep 11049695 = 16574543) B16574543
theorem B8280893 : Blo 1453546 8280893 := bstep (se 3 (by rfl) ⟨1552667, by rfl⟩ : syracuseStep 8280893 = 3105335) B3105335
theorem B2620351 : Blo 1453546 2620351 := bstep (se 1 (by rfl) ⟨1965263, by rfl⟩ : syracuseStep 2620351 = 3930527) B3930527
theorem B11508905 : Blo 1453546 11508905 := bstep (se 2 (by rfl) ⟨4315839, by rfl⟩ : syracuseStep 11508905 = 8631679) B8631679
theorem B2759903 : Blo 1453546 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B79633637 : Blo 1453546 79633637 := bstep (se 4 (by rfl) ⟨7465653, by rfl⟩ : syracuseStep 79633637 = 14931307) B14931307
theorem B2211511 : Blo 1453546 2211511 := bstep (se 1 (by rfl) ⟨1658633, by rfl⟩ : syracuseStep 2211511 = 3317267) B3317267
theorem B2621281 : Blo 1453546 2621281 := bstep (se 2 (by rfl) ⟨982980, by rfl⟩ : syracuseStep 2621281 = 1965961) B1965961
theorem B10477507 : Blo 1453546 10477507 := bstep (se 1 (by rfl) ⟨7858130, by rfl⟩ : syracuseStep 10477507 = 15716261) B15716261
theorem B5521385 : Blo 1453546 5521385 := bstep (se 2 (by rfl) ⟨2070519, by rfl⟩ : syracuseStep 5521385 = 4141039) B4141039
theorem B13984157 : Blo 1453546 13984157 := bstep (se 3 (by rfl) ⟨2622029, by rfl⟩ : syracuseStep 13984157 = 5244059) B5244059
theorem B5980985 : Blo 1453546 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B4662335 : Blo 1453546 4662335 := bstep (se 1 (by rfl) ⟨3496751, by rfl⟩ : syracuseStep 4662335 = 6993503) B6993503
theorem B18629959 : Blo 1453546 18629959 := bstep (se 1 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 18629959 = 27944939) B27944939
theorem B2180591 : Blo 1453546 2180591 := bstep (se 1 (by rfl) ⟨1635443, by rfl⟩ : syracuseStep 2180591 = 3270887) B3270887
theorem B4908599 : Blo 1453546 4908599 := bstep (se 1 (by rfl) ⟨3681449, by rfl⟩ : syracuseStep 4908599 = 7362899) B7362899
theorem B10774127 : Blo 1453546 10774127 := bstep (se 1 (by rfl) ⟨8080595, by rfl⟩ : syracuseStep 10774127 = 16161191) B16161191
theorem B12428963 : Blo 1453546 12428963 := bstep (se 1 (by rfl) ⟨9321722, by rfl⟩ : syracuseStep 12428963 = 18643445) B18643445
theorem B2180777 : Blo 1453546 2180777 := bstep (se 2 (by rfl) ⟨817791, by rfl⟩ : syracuseStep 2180777 = 1635583) B1635583
theorem B7366463 : Blo 1453546 7366463 := bstep (se 1 (by rfl) ⟨5524847, by rfl⟩ : syracuseStep 7366463 = 11049695) B11049695
theorem B2181023 : Blo 1453546 2181023 := bstep (se 1 (by rfl) ⟨1635767, by rfl⟩ : syracuseStep 2181023 = 3271535) B3271535
theorem B5523497 : Blo 1453546 5523497 := bstep (se 2 (by rfl) ⟨2071311, by rfl⟩ : syracuseStep 5523497 = 4142623) B4142623
theorem B2181191 : Blo 1453546 2181191 := bstep (se 1 (by rfl) ⟨1635893, by rfl⟩ : syracuseStep 2181191 = 3271787) B3271787
theorem B2181407 : Blo 1453546 2181407 := bstep (se 1 (by rfl) ⟨1636055, by rfl⟩ : syracuseStep 2181407 = 3272111) B3272111
theorem B2181479 : Blo 1453546 2181479 := bstep (se 1 (by rfl) ⟨1636109, by rfl⟩ : syracuseStep 2181479 = 3272219) B3272219
theorem B2181575 : Blo 1453546 2181575 := bstep (se 1 (by rfl) ⟨1636181, by rfl⟩ : syracuseStep 2181575 = 3272363) B3272363
theorem B13970009 : Blo 1453546 13970009 := bstep (se 2 (by rfl) ⟨5238753, by rfl⟩ : syracuseStep 13970009 = 10477507) B10477507
theorem B3680923 : Blo 1453546 3680923 := bstep (se 1 (by rfl) ⟨2760692, by rfl⟩ : syracuseStep 3680923 = 5521385) B5521385
theorem B3271481 : Blo 1453546 3271481 := bstep (se 2 (by rfl) ⟨1226805, by rfl⟩ : syracuseStep 3271481 = 2453611) B2453611
theorem B2182055 : Blo 1453546 2182055 := bstep (se 1 (by rfl) ⟨1636541, by rfl⟩ : syracuseStep 2182055 = 3273083) B3273083
theorem B7080929 : Blo 1453546 7080929 := bstep (se 2 (by rfl) ⟨2655348, by rfl⟩ : syracuseStep 7080929 = 5310697) B5310697
theorem B7867475 : Blo 1453546 7867475 := bstep (se 1 (by rfl) ⟨5900606, by rfl⟩ : syracuseStep 7867475 = 11801213) B11801213
theorem B30690413 : Blo 1453546 30690413 := bstep (se 3 (by rfl) ⟨5754452, by rfl⟩ : syracuseStep 30690413 = 11508905) B11508905
theorem B16576001 : Blo 1453546 16576001 := bstep (se 2 (by rfl) ⟨6216000, by rfl⟩ : syracuseStep 16576001 = 12432001) B12432001
theorem B6213199 : Blo 1453546 6213199 := bstep (se 1 (by rfl) ⟨4659899, by rfl⟩ : syracuseStep 6213199 = 9319799) B9319799
theorem B2182907 : Blo 1453546 2182907 := bstep (se 1 (by rfl) ⟨1637180, by rfl⟩ : syracuseStep 2182907 = 3274361) B3274361
theorem B11046779 : Blo 1453546 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B3493801 : Blo 1453546 3493801 := bstep (se 2 (by rfl) ⟨1310175, by rfl⟩ : syracuseStep 3493801 = 2620351) B2620351
theorem B27946943 : Blo 1453546 27946943 := bstep (se 1 (by rfl) ⟨20960207, by rfl⟩ : syracuseStep 27946943 = 41920415) B41920415
theorem B2183147 : Blo 1453546 2183147 := bstep (se 1 (by rfl) ⟨1637360, by rfl⟩ : syracuseStep 2183147 = 3274721) B3274721
theorem B3272687 : Blo 1453546 3272687 := bstep (se 1 (by rfl) ⟨2454515, by rfl⟩ : syracuseStep 3272687 = 4909031) B4909031
theorem B1454171 : Blo 1453546 1454171 := bstep (se 1 (by rfl) ⟨1090628, by rfl⟩ : syracuseStep 1454171 = 2181257) B2181257
theorem B11047265 : Blo 1453546 11047265 := bstep (se 2 (by rfl) ⟨4142724, by rfl⟩ : syracuseStep 11047265 = 8285449) B8285449
theorem B12423527 : Blo 1453546 12423527 := bstep (se 1 (by rfl) ⟨9317645, by rfl⟩ : syracuseStep 12423527 = 18635291) B18635291
theorem B1454559 : Blo 1453546 1454559 := bstep (se 1 (by rfl) ⟨1090919, by rfl⟩ : syracuseStep 1454559 = 2181839) B2181839
theorem B3682847 : Blo 1453546 3682847 := bstep (se 1 (by rfl) ⟨2762135, by rfl⟩ : syracuseStep 3682847 = 5524271) B5524271
theorem B1454683 : Blo 1453546 1454683 := bstep (se 1 (by rfl) ⟨1091012, by rfl⟩ : syracuseStep 1454683 = 2182025) B2182025
theorem B1839935 : Blo 1453546 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B53089091 : Blo 1453546 53089091 := bstep (se 1 (by rfl) ⟨39816818, by rfl⟩ : syracuseStep 53089091 = 79633637) B79633637
theorem B3929023 : Blo 1453546 3929023 := bstep (se 1 (by rfl) ⟨2946767, by rfl⟩ : syracuseStep 3929023 = 5893535) B5893535
theorem B255202397 : Blo 1453546 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B1635439 : Blo 1453546 1635439 := bstep (se 1 (by rfl) ⟨1226579, by rfl⟩ : syracuseStep 1635439 = 2453159) B2453159
theorem B3495041 : Blo 1453546 3495041 := bstep (se 2 (by rfl) ⟨1310640, by rfl⟩ : syracuseStep 3495041 = 2621281) B2621281
theorem B3683495 : Blo 1453546 3683495 := bstep (se 1 (by rfl) ⟨2762621, by rfl⟩ : syracuseStep 3683495 = 5525243) B5525243
theorem B1635655 : Blo 1453546 1635655 := bstep (se 1 (by rfl) ⟨1226741, by rfl⟩ : syracuseStep 1635655 = 2453483) B2453483
theorem B3274091 : Blo 1453546 3274091 := bstep (se 1 (by rfl) ⟨2455568, by rfl⟩ : syracuseStep 3274091 = 4911137) B4911137
theorem B2455015 : Blo 1453546 2455015 := bstep (se 1 (by rfl) ⟨1841261, by rfl⟩ : syracuseStep 2455015 = 3682523) B3682523
theorem B3274235 : Blo 1453546 3274235 := bstep (se 1 (by rfl) ⟨2455676, by rfl⟩ : syracuseStep 3274235 = 4911353) B4911353
theorem B2455177 : Blo 1453546 2455177 := bstep (se 2 (by rfl) ⟨920691, by rfl⟩ : syracuseStep 2455177 = 1841383) B1841383
theorem B11048723 : Blo 1453546 11048723 := bstep (se 1 (by rfl) ⟨8286542, by rfl⟩ : syracuseStep 11048723 = 16573085) B16573085
theorem B1636123 : Blo 1453546 1636123 := bstep (se 1 (by rfl) ⟨1227092, by rfl⟩ : syracuseStep 1636123 = 2454185) B2454185
theorem B3274919 : Blo 1453546 3274919 := bstep (se 1 (by rfl) ⟨2456189, by rfl⟩ : syracuseStep 3274919 = 4912379) B4912379
theorem B13982159 : Blo 1453546 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B2800175 : Blo 1453546 2800175 := bstep (se 1 (by rfl) ⟨2100131, by rfl⟩ : syracuseStep 2800175 = 4200263) B4200263
theorem B5519927 : Blo 1453546 5519927 := bstep (se 1 (by rfl) ⟨4139945, by rfl⟩ : syracuseStep 5519927 = 8279891) B8279891
theorem B103512667 : Blo 1453546 103512667 := bstep (se 1 (by rfl) ⟨77634500, by rfl⟩ : syracuseStep 103512667 = 155269001) B155269001
theorem B1637311 : Blo 1453546 1637311 := bstep (se 1 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 1637311 = 2455967) B2455967
theorem B11041919 : Blo 1453546 11041919 := bstep (se 1 (by rfl) ⟨8281439, by rfl⟩ : syracuseStep 11041919 = 16562879) B16562879
theorem B5520595 : Blo 1453546 5520595 := bstep (se 1 (by rfl) ⟨4140446, by rfl⟩ : syracuseStep 5520595 = 8280893) B8280893
theorem B9952787 : Blo 1453546 9952787 := bstep (se 1 (by rfl) ⟨7464590, by rfl⟩ : syracuseStep 9952787 = 14929181) B14929181
theorem B2948681 : Blo 1453546 2948681 := bstep (se 2 (by rfl) ⟨1105755, by rfl⟩ : syracuseStep 2948681 = 2211511) B2211511
theorem B3104507 : Blo 1453546 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B2760617 : Blo 1453546 2760617 := bstep (se 2 (by rfl) ⟨1035231, by rfl⟩ : syracuseStep 2760617 = 2070463) B2070463
theorem B7364843 : Blo 1453546 7364843 := bstep (se 1 (by rfl) ⟨5523632, by rfl⟩ : syracuseStep 7364843 = 11047265) B11047265
theorem B8282351 : Blo 1453546 8282351 := bstep (se 1 (by rfl) ⟨6211763, by rfl⟩ : syracuseStep 8282351 = 12423527) B12423527
theorem B9322771 : Blo 1453546 9322771 := bstep (se 1 (by rfl) ⟨6992078, by rfl⟩ : syracuseStep 9322771 = 13984157) B13984157
theorem B29868533 : Blo 1453546 29868533 := bstep (se 5 (by rfl) ⟨1400087, by rfl⟩ : syracuseStep 29868533 = 2800175) B2800175
theorem B4907897 : Blo 1453546 4907897 := bstep (se 2 (by rfl) ⟨1840461, by rfl⟩ : syracuseStep 4907897 = 3680923) B3680923
theorem B7365815 : Blo 1453546 7365815 := bstep (se 1 (by rfl) ⟨5524361, by rfl⟩ : syracuseStep 7365815 = 11048723) B11048723
theorem B2180585 : Blo 1453546 2180585 := bstep (se 2 (by rfl) ⟨817719, by rfl⟩ : syracuseStep 2180585 = 1635439) B1635439
theorem B3679951 : Blo 1453546 3679951 := bstep (se 1 (by rfl) ⟨2759963, by rfl⟩ : syracuseStep 3679951 = 5519927) B5519927
theorem B24839945 : Blo 1453546 24839945 := bstep (se 2 (by rfl) ⟨9314979, by rfl⟩ : syracuseStep 24839945 = 18629959) B18629959
theorem B2180873 : Blo 1453546 2180873 := bstep (se 2 (by rfl) ⟨817827, by rfl⟩ : syracuseStep 2180873 = 1635655) B1635655
theorem B2180987 : Blo 1453546 2180987 := bstep (se 1 (by rfl) ⟨1635740, by rfl⟩ : syracuseStep 2180987 = 3271481) B3271481
theorem B4720619 : Blo 1453546 4720619 := bstep (se 1 (by rfl) ⟨3540464, by rfl⟩ : syracuseStep 4720619 = 7080929) B7080929
theorem B5244983 : Blo 1453546 5244983 := bstep (se 1 (by rfl) ⟨3933737, by rfl⟩ : syracuseStep 5244983 = 7867475) B7867475
theorem B8284265 : Blo 1453546 8284265 := bstep (se 2 (by rfl) ⟨3106599, by rfl⟩ : syracuseStep 8284265 = 6213199) B6213199
theorem B2181497 : Blo 1453546 2181497 := bstep (se 2 (by rfl) ⟨818061, by rfl⟩ : syracuseStep 2181497 = 1636123) B1636123
theorem B18631295 : Blo 1453546 18631295 := bstep (se 1 (by rfl) ⟨13973471, by rfl⟩ : syracuseStep 18631295 = 27946943) B27946943
theorem B2181791 : Blo 1453546 2181791 := bstep (se 1 (by rfl) ⟨1636343, by rfl⟩ : syracuseStep 2181791 = 3272687) B3272687
theorem B35392727 : Blo 1453546 35392727 := bstep (se 1 (by rfl) ⟨26544545, by rfl⟩ : syracuseStep 35392727 = 53089091) B53089091
theorem B3108223 : Blo 1453546 3108223 := bstep (se 1 (by rfl) ⟨2331167, by rfl⟩ : syracuseStep 3108223 = 4662335) B4662335
theorem B170134931 : Blo 1453546 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B2330027 : Blo 1453546 2330027 := bstep (se 1 (by rfl) ⟨1747520, by rfl⟩ : syracuseStep 2330027 = 3495041) B3495041
theorem B2182727 : Blo 1453546 2182727 := bstep (se 1 (by rfl) ⟨1637045, by rfl⟩ : syracuseStep 2182727 = 3274091) B3274091
theorem B1453727 : Blo 1453546 1453727 := bstep (se 1 (by rfl) ⟨1090295, by rfl⟩ : syracuseStep 1453727 = 2180591) B2180591
theorem B2182823 : Blo 1453546 2182823 := bstep (se 1 (by rfl) ⟨1637117, by rfl⟩ : syracuseStep 2182823 = 3274235) B3274235
theorem B3272399 : Blo 1453546 3272399 := bstep (se 1 (by rfl) ⟨2454299, by rfl⟩ : syracuseStep 3272399 = 4908599) B4908599
theorem B8285975 : Blo 1453546 8285975 := bstep (se 1 (by rfl) ⟨6214481, by rfl⟩ : syracuseStep 8285975 = 12428963) B12428963
theorem B1453851 : Blo 1453546 1453851 := bstep (se 1 (by rfl) ⟨1090388, by rfl⟩ : syracuseStep 1453851 = 2180777) B2180777
theorem B4910975 : Blo 1453546 4910975 := bstep (se 1 (by rfl) ⟨3683231, by rfl⟩ : syracuseStep 4910975 = 7366463) B7366463
theorem B5238697 : Blo 1453546 5238697 := bstep (se 2 (by rfl) ⟨1964511, by rfl⟩ : syracuseStep 5238697 = 3929023) B3929023
theorem B2183081 : Blo 1453546 2183081 := bstep (se 2 (by rfl) ⟨818655, by rfl⟩ : syracuseStep 2183081 = 1637311) B1637311
theorem B1454015 : Blo 1453546 1454015 := bstep (se 1 (by rfl) ⟨1090511, by rfl⟩ : syracuseStep 1454015 = 2181023) B2181023
theorem B3682331 : Blo 1453546 3682331 := bstep (se 1 (by rfl) ⟨2761748, by rfl⟩ : syracuseStep 3682331 = 5523497) B5523497
theorem B1454127 : Blo 1453546 1454127 := bstep (se 1 (by rfl) ⟨1090595, by rfl⟩ : syracuseStep 1454127 = 2181191) B2181191
theorem B2183279 : Blo 1453546 2183279 := bstep (se 1 (by rfl) ⟨1637459, by rfl⟩ : syracuseStep 2183279 = 3274919) B3274919
theorem B1454271 : Blo 1453546 1454271 := bstep (se 1 (by rfl) ⟨1090703, by rfl⟩ : syracuseStep 1454271 = 2181407) B2181407
theorem B37253357 : Blo 1453546 37253357 := bstep (se 3 (by rfl) ⟨6985004, by rfl⟩ : syracuseStep 37253357 = 13970009) B13970009
theorem B1454319 : Blo 1453546 1454319 := bstep (se 1 (by rfl) ⟨1090739, by rfl⟩ : syracuseStep 1454319 = 2181479) B2181479
theorem B7360793 : Blo 1453546 7360793 := bstep (se 2 (by rfl) ⟨2760297, by rfl⟩ : syracuseStep 7360793 = 5520595) B5520595
theorem B1454383 : Blo 1453546 1454383 := bstep (se 1 (by rfl) ⟨1090787, by rfl⟩ : syracuseStep 1454383 = 2181575) B2181575
theorem B1454703 : Blo 1453546 1454703 := bstep (se 1 (by rfl) ⟨1091027, by rfl⟩ : syracuseStep 1454703 = 2182055) B2182055
theorem B3273353 : Blo 1453546 3273353 := bstep (se 2 (by rfl) ⟨1227507, by rfl⟩ : syracuseStep 3273353 = 2455015) B2455015
theorem B8278685 : Blo 1453546 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B20460275 : Blo 1453546 20460275 := bstep (se 1 (by rfl) ⟨15345206, by rfl⟩ : syracuseStep 20460275 = 30690413) B30690413
theorem B7361279 : Blo 1453546 7361279 := bstep (se 1 (by rfl) ⟨5520959, by rfl⟩ : syracuseStep 7361279 = 11041919) B11041919
theorem B3273569 : Blo 1453546 3273569 := bstep (se 2 (by rfl) ⟨1227588, by rfl⟩ : syracuseStep 3273569 = 2455177) B2455177
theorem B1455271 : Blo 1453546 1455271 := bstep (se 1 (by rfl) ⟨1091453, by rfl⟩ : syracuseStep 1455271 = 2182907) B2182907
theorem B4658401 : Blo 1453546 4658401 := bstep (se 2 (by rfl) ⟨1746900, by rfl⟩ : syracuseStep 4658401 = 3493801) B3493801
theorem B1840411 : Blo 1453546 1840411 := bstep (se 1 (by rfl) ⟨1380308, by rfl⟩ : syracuseStep 1840411 = 2760617) B2760617
theorem B1455431 : Blo 1453546 1455431 := bstep (se 1 (by rfl) ⟨1091573, by rfl⟩ : syracuseStep 1455431 = 2183147) B2183147
theorem B2455231 : Blo 1453546 2455231 := bstep (se 1 (by rfl) ⟨1841423, by rfl⟩ : syracuseStep 2455231 = 3682847) B3682847
theorem B3987323 : Blo 1453546 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B2455663 : Blo 1453546 2455663 := bstep (se 1 (by rfl) ⟨1841747, by rfl⟩ : syracuseStep 2455663 = 3683495) B3683495
theorem B138016889 : Blo 1453546 138016889 := bstep (se 2 (by rfl) ⟨51756333, by rfl⟩ : syracuseStep 138016889 = 103512667) B103512667
theorem B7182751 : Blo 1453546 7182751 := bstep (se 1 (by rfl) ⟨5387063, by rfl⟩ : syracuseStep 7182751 = 10774127) B10774127
theorem B7863149 : Blo 1453546 7863149 := bstep (se 3 (by rfl) ⟨1474340, by rfl⟩ : syracuseStep 7863149 = 2948681) B2948681
theorem B9321439 : Blo 1453546 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B4906493 : Blo 1453546 4906493 := bstep (se 3 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 4906493 = 1839935) B1839935
theorem B11050667 : Blo 1453546 11050667 := bstep (se 1 (by rfl) ⟨8288000, by rfl⟩ : syracuseStep 11050667 = 16576001) B16576001
theorem B6635191 : Blo 1453546 6635191 := bstep (se 1 (by rfl) ⟨4976393, by rfl⟩ : syracuseStep 6635191 = 9952787) B9952787
theorem B7364519 : Blo 1453546 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B5521567 : Blo 1453546 5521567 := bstep (se 1 (by rfl) ⟨4141175, by rfl⟩ : syracuseStep 5521567 = 8282351) B8282351
theorem B4907195 : Blo 1453546 4907195 := bstep (se 1 (by rfl) ⟨3680396, by rfl⟩ : syracuseStep 4907195 = 7360793) B7360793
theorem B13640183 : Blo 1453546 13640183 := bstep (se 1 (by rfl) ⟨10230137, by rfl⟩ : syracuseStep 13640183 = 20460275) B20460275
theorem B4907519 : Blo 1453546 4907519 := bstep (se 1 (by rfl) ⟨3680639, by rfl⟩ : syracuseStep 4907519 = 7361279) B7361279
theorem B9577001 : Blo 1453546 9577001 := bstep (se 2 (by rfl) ⟨3591375, by rfl⟩ : syracuseStep 9577001 = 7182751) B7182751
theorem B12428585 : Blo 1453546 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B5522843 : Blo 1453546 5522843 := bstep (se 1 (by rfl) ⟨4142132, by rfl⟩ : syracuseStep 5522843 = 8284265) B8284265
theorem B6211201 : Blo 1453546 6211201 := bstep (se 2 (by rfl) ⟨2329200, by rfl⟩ : syracuseStep 6211201 = 4658401) B4658401
theorem B12420863 : Blo 1453546 12420863 := bstep (se 1 (by rfl) ⟨9315647, by rfl⟩ : syracuseStep 12420863 = 18631295) B18631295
theorem B23595151 : Blo 1453546 23595151 := bstep (se 1 (by rfl) ⟨17696363, by rfl⟩ : syracuseStep 23595151 = 35392727) B35392727
theorem B3270995 : Blo 1453546 3270995 := bstep (se 1 (by rfl) ⟨2453246, by rfl⟩ : syracuseStep 3270995 = 4906493) B4906493
theorem B7367111 : Blo 1453546 7367111 := bstep (se 1 (by rfl) ⟨5525333, by rfl⟩ : syracuseStep 7367111 = 11050667) B11050667
theorem B2181599 : Blo 1453546 2181599 := bstep (se 1 (by rfl) ⟨1636199, by rfl⟩ : syracuseStep 2181599 = 3272399) B3272399
theorem B5523983 : Blo 1453546 5523983 := bstep (se 1 (by rfl) ⟨4142987, by rfl⟩ : syracuseStep 5523983 = 8285975) B8285975
theorem B4909679 : Blo 1453546 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B4909895 : Blo 1453546 4909895 := bstep (se 1 (by rfl) ⟨3682421, by rfl⟩ : syracuseStep 4909895 = 7364843) B7364843
theorem B12430361 : Blo 1453546 12430361 := bstep (se 2 (by rfl) ⟨4661385, by rfl⟩ : syracuseStep 12430361 = 9322771) B9322771
theorem B2182235 : Blo 1453546 2182235 := bstep (se 1 (by rfl) ⟨1636676, by rfl⟩ : syracuseStep 2182235 = 3273353) B3273353
theorem B2182379 : Blo 1453546 2182379 := bstep (se 1 (by rfl) ⟨1636784, by rfl⟩ : syracuseStep 2182379 = 3273569) B3273569
theorem B3271931 : Blo 1453546 3271931 := bstep (se 1 (by rfl) ⟨2453948, by rfl⟩ : syracuseStep 3271931 = 4907897) B4907897
theorem B4910543 : Blo 1453546 4910543 := bstep (se 1 (by rfl) ⟨3682907, by rfl⟩ : syracuseStep 4910543 = 7365815) B7365815
theorem B1453723 : Blo 1453546 1453723 := bstep (se 1 (by rfl) ⟨1090292, by rfl⟩ : syracuseStep 1453723 = 2180585) B2180585
theorem B16559963 : Blo 1453546 16559963 := bstep (se 1 (by rfl) ⟨12419972, by rfl⟩ : syracuseStep 16559963 = 24839945) B24839945
theorem B1453915 : Blo 1453546 1453915 := bstep (se 1 (by rfl) ⟨1090436, by rfl⟩ : syracuseStep 1453915 = 2180873) B2180873
theorem B1453991 : Blo 1453546 1453991 := bstep (se 1 (by rfl) ⟨1090493, by rfl⟩ : syracuseStep 1453991 = 2180987) B2180987
theorem B2658215 : Blo 1453546 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B1454331 : Blo 1453546 1454331 := bstep (se 1 (by rfl) ⟨1090748, by rfl⟩ : syracuseStep 1454331 = 2181497) B2181497
theorem B2453881 : Blo 1453546 2453881 := bstep (se 2 (by rfl) ⟨920205, by rfl⟩ : syracuseStep 2453881 = 1840411) B1840411
theorem B1454527 : Blo 1453546 1454527 := bstep (se 1 (by rfl) ⟨1090895, by rfl⟩ : syracuseStep 1454527 = 2181791) B2181791
theorem B3273641 : Blo 1453546 3273641 := bstep (se 2 (by rfl) ⟨1227615, by rfl⟩ : syracuseStep 3273641 = 2455231) B2455231
theorem B113423287 : Blo 1453546 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B1553351 : Blo 1453546 1553351 := bstep (se 1 (by rfl) ⟨1165013, by rfl⟩ : syracuseStep 1553351 = 2330027) B2330027
theorem B1455151 : Blo 1453546 1455151 := bstep (se 1 (by rfl) ⟨1091363, by rfl⟩ : syracuseStep 1455151 = 2182727) B2182727
theorem B1455215 : Blo 1453546 1455215 := bstep (se 1 (by rfl) ⟨1091411, by rfl⟩ : syracuseStep 1455215 = 2182823) B2182823
theorem B6984929 : Blo 1453546 6984929 := bstep (se 2 (by rfl) ⟨2619348, by rfl⟩ : syracuseStep 6984929 = 5238697) B5238697
theorem B3273983 : Blo 1453546 3273983 := bstep (se 1 (by rfl) ⟨2455487, by rfl⟩ : syracuseStep 3273983 = 4910975) B4910975
theorem B1455387 : Blo 1453546 1455387 := bstep (se 1 (by rfl) ⟨1091540, by rfl⟩ : syracuseStep 1455387 = 2183081) B2183081
theorem B12588317 : Blo 1453546 12588317 := bstep (se 3 (by rfl) ⟨2360309, by rfl⟩ : syracuseStep 12588317 = 4720619) B4720619
theorem B2454887 : Blo 1453546 2454887 := bstep (se 1 (by rfl) ⟨1841165, by rfl⟩ : syracuseStep 2454887 = 3682331) B3682331
theorem B1455519 : Blo 1453546 1455519 := bstep (se 1 (by rfl) ⟨1091639, by rfl⟩ : syracuseStep 1455519 = 2183279) B2183279
theorem B3274217 : Blo 1453546 3274217 := bstep (se 2 (by rfl) ⟨1227831, by rfl⟩ : syracuseStep 3274217 = 2455663) B2455663
theorem B24835571 : Blo 1453546 24835571 := bstep (se 1 (by rfl) ⟨18626678, by rfl⟩ : syracuseStep 24835571 = 37253357) B37253357
theorem B19912355 : Blo 1453546 19912355 := bstep (se 1 (by rfl) ⟨14934266, by rfl⟩ : syracuseStep 19912355 = 29868533) B29868533
theorem B5519123 : Blo 1453546 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B3496655 : Blo 1453546 3496655 := bstep (se 1 (by rfl) ⟨2622491, by rfl⟩ : syracuseStep 3496655 = 5244983) B5244983
theorem B92011259 : Blo 1453546 92011259 := bstep (se 1 (by rfl) ⟨69008444, by rfl⟩ : syracuseStep 92011259 = 138016889) B138016889
theorem B4144297 : Blo 1453546 4144297 := bstep (se 2 (by rfl) ⟨1554111, by rfl⟩ : syracuseStep 4144297 = 3108223) B3108223
theorem B5242099 : Blo 1453546 5242099 := bstep (se 1 (by rfl) ⟨3931574, by rfl⟩ : syracuseStep 5242099 = 7863149) B7863149
theorem B8846921 : Blo 1453546 8846921 := bstep (se 2 (by rfl) ⟨3317595, by rfl⟩ : syracuseStep 8846921 = 6635191) B6635191
theorem B4906601 : Blo 1453546 4906601 := bstep (se 2 (by rfl) ⟨1839975, by rfl⟩ : syracuseStep 4906601 = 3679951) B3679951
theorem B9093455 : Blo 1453546 9093455 := bstep (se 1 (by rfl) ⟨6820091, by rfl⟩ : syracuseStep 9093455 = 13640183) B13640183
theorem B16557047 : Blo 1453546 16557047 := bstep (se 1 (by rfl) ⟨12417785, by rfl⟩ : syracuseStep 16557047 = 24835571) B24835571
theorem B3679415 : Blo 1453546 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B2180663 : Blo 1453546 2180663 := bstep (se 1 (by rfl) ⟨1635497, by rfl⟩ : syracuseStep 2180663 = 3270995) B3270995
theorem B6989465 : Blo 1453546 6989465 := bstep (se 2 (by rfl) ⟨2621049, by rfl⟩ : syracuseStep 6989465 = 5242099) B5242099
theorem B2181287 : Blo 1453546 2181287 := bstep (se 1 (by rfl) ⟨1635965, by rfl⟩ : syracuseStep 2181287 = 3271931) B3271931
theorem B3271067 : Blo 1453546 3271067 := bstep (se 1 (by rfl) ⟨2453300, by rfl⟩ : syracuseStep 3271067 = 4906601) B4906601
theorem B7088573 : Blo 1453546 7088573 := bstep (se 3 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 7088573 = 2658215) B2658215
theorem B3271463 : Blo 1453546 3271463 := bstep (se 1 (by rfl) ⟨2453597, by rfl⟩ : syracuseStep 3271463 = 4907195) B4907195
theorem B31460201 : Blo 1453546 31460201 := bstep (se 2 (by rfl) ⟨11797575, by rfl⟩ : syracuseStep 31460201 = 23595151) B23595151
theorem B3271679 : Blo 1453546 3271679 := bstep (se 1 (by rfl) ⟨2453759, by rfl⟩ : syracuseStep 3271679 = 4907519) B4907519
theorem B6384667 : Blo 1453546 6384667 := bstep (se 1 (by rfl) ⟨4788500, by rfl⟩ : syracuseStep 6384667 = 9577001) B9577001
theorem B3271841 : Blo 1453546 3271841 := bstep (se 2 (by rfl) ⟨1226940, by rfl⟩ : syracuseStep 3271841 = 2453881) B2453881
theorem B2182427 : Blo 1453546 2182427 := bstep (se 1 (by rfl) ⟨1636820, by rfl⟩ : syracuseStep 2182427 = 3273641) B3273641
theorem B4656619 : Blo 1453546 4656619 := bstep (se 1 (by rfl) ⟨3492464, by rfl⟩ : syracuseStep 4656619 = 6984929) B6984929
theorem B2182655 : Blo 1453546 2182655 := bstep (se 1 (by rfl) ⟨1636991, by rfl⟩ : syracuseStep 2182655 = 3273983) B3273983
theorem B8392211 : Blo 1453546 8392211 := bstep (se 1 (by rfl) ⟨6294158, by rfl⟩ : syracuseStep 8392211 = 12588317) B12588317
theorem B8285723 : Blo 1453546 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B3681895 : Blo 1453546 3681895 := bstep (se 1 (by rfl) ⟨2761421, by rfl⟩ : syracuseStep 3681895 = 5522843) B5522843
theorem B2182811 : Blo 1453546 2182811 := bstep (se 1 (by rfl) ⟨1637108, by rfl⟩ : syracuseStep 2182811 = 3274217) B3274217
theorem B13274903 : Blo 1453546 13274903 := bstep (se 1 (by rfl) ⟨9956177, by rfl⟩ : syracuseStep 13274903 = 19912355) B19912355
theorem B5525729 : Blo 1453546 5525729 := bstep (se 2 (by rfl) ⟨2072148, by rfl⟩ : syracuseStep 5525729 = 4144297) B4144297
theorem B4911407 : Blo 1453546 4911407 := bstep (se 1 (by rfl) ⟨3683555, by rfl⟩ : syracuseStep 4911407 = 7367111) B7367111
theorem B1454399 : Blo 1453546 1454399 := bstep (se 1 (by rfl) ⟨1090799, by rfl⟩ : syracuseStep 1454399 = 2181599) B2181599
theorem B3682655 : Blo 1453546 3682655 := bstep (se 1 (by rfl) ⟨2761991, by rfl⟩ : syracuseStep 3682655 = 5523983) B5523983
theorem B3273119 : Blo 1453546 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B2331103 : Blo 1453546 2331103 := bstep (se 1 (by rfl) ⟨1748327, by rfl⟩ : syracuseStep 2331103 = 3496655) B3496655
theorem B3273263 : Blo 1453546 3273263 := bstep (se 1 (by rfl) ⟨2454947, by rfl⟩ : syracuseStep 3273263 = 4909895) B4909895
theorem B245363357 : Blo 1453546 245363357 := bstep (se 3 (by rfl) ⟨46005629, by rfl⟩ : syracuseStep 245363357 = 92011259) B92011259
theorem B8286907 : Blo 1453546 8286907 := bstep (se 1 (by rfl) ⟨6215180, by rfl⟩ : syracuseStep 8286907 = 12430361) B12430361
theorem B1454823 : Blo 1453546 1454823 := bstep (se 1 (by rfl) ⟨1091117, by rfl⟩ : syracuseStep 1454823 = 2182235) B2182235
theorem B1454919 : Blo 1453546 1454919 := bstep (se 1 (by rfl) ⟨1091189, by rfl⟩ : syracuseStep 1454919 = 2182379) B2182379
theorem B3273695 : Blo 1453546 3273695 := bstep (se 1 (by rfl) ⟨2455271, by rfl⟩ : syracuseStep 3273695 = 4910543) B4910543
theorem B4142269 : Blo 1453546 4142269 := bstep (se 3 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 4142269 = 1553351) B1553351
theorem B11039975 : Blo 1453546 11039975 := bstep (se 1 (by rfl) ⟨8279981, by rfl⟩ : syracuseStep 11039975 = 16559963) B16559963
theorem B7362089 : Blo 1453546 7362089 := bstep (se 2 (by rfl) ⟨2760783, by rfl⟩ : syracuseStep 7362089 = 5521567) B5521567
theorem B1636591 : Blo 1453546 1636591 := bstep (se 1 (by rfl) ⟨1227443, by rfl⟩ : syracuseStep 1636591 = 2454887) B2454887
theorem B8280575 : Blo 1453546 8280575 := bstep (se 1 (by rfl) ⟨6210431, by rfl⟩ : syracuseStep 8280575 = 12420863) B12420863
theorem B151231049 : Blo 1453546 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B8281601 : Blo 1453546 8281601 := bstep (se 2 (by rfl) ⟨3105600, by rfl⟩ : syracuseStep 8281601 = 6211201) B6211201
theorem B5897947 : Blo 1453546 5897947 := bstep (se 1 (by rfl) ⟨4423460, by rfl⟩ : syracuseStep 5897947 = 8846921) B8846921
theorem B6062303 : Blo 1453546 6062303 := bstep (se 1 (by rfl) ⟨4546727, by rfl⟩ : syracuseStep 6062303 = 9093455) B9093455
theorem B4908059 : Blo 1453546 4908059 := bstep (se 1 (by rfl) ⟨3681044, by rfl⟩ : syracuseStep 4908059 = 7362089) B7362089
theorem B8512889 : Blo 1453546 8512889 := bstep (se 2 (by rfl) ⟨3192333, by rfl⟩ : syracuseStep 8512889 = 6384667) B6384667
theorem B5523025 : Blo 1453546 5523025 := bstep (se 2 (by rfl) ⟨2071134, by rfl⟩ : syracuseStep 5523025 = 4142269) B4142269
theorem B2180711 : Blo 1453546 2180711 := bstep (se 1 (by rfl) ⟨1635533, by rfl⟩ : syracuseStep 2180711 = 3271067) B3271067
theorem B100820699 : Blo 1453546 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B2180975 : Blo 1453546 2180975 := bstep (se 1 (by rfl) ⟨1635731, by rfl⟩ : syracuseStep 2180975 = 3271463) B3271463
theorem B20973467 : Blo 1453546 20973467 := bstep (se 1 (by rfl) ⟨15730100, by rfl⟩ : syracuseStep 20973467 = 31460201) B31460201
theorem B2181119 : Blo 1453546 2181119 := bstep (se 1 (by rfl) ⟨1635839, by rfl⟩ : syracuseStep 2181119 = 3271679) B3271679
theorem B2181227 : Blo 1453546 2181227 := bstep (se 1 (by rfl) ⟨1635920, by rfl⟩ : syracuseStep 2181227 = 3271841) B3271841
theorem B4909193 : Blo 1453546 4909193 := bstep (se 2 (by rfl) ⟨1840947, by rfl⟩ : syracuseStep 4909193 = 3681895) B3681895
theorem B5523815 : Blo 1453546 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B8849935 : Blo 1453546 8849935 := bstep (se 1 (by rfl) ⟨6637451, by rfl⟩ : syracuseStep 8849935 = 13274903) B13274903
theorem B2182079 : Blo 1453546 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B2182121 : Blo 1453546 2182121 := bstep (se 2 (by rfl) ⟨818295, by rfl⟩ : syracuseStep 2182121 = 1636591) B1636591
theorem B2182175 : Blo 1453546 2182175 := bstep (se 1 (by rfl) ⟨1636631, by rfl⟩ : syracuseStep 2182175 = 3273263) B3273263
theorem B3108137 : Blo 1453546 3108137 := bstep (se 2 (by rfl) ⟨1165551, by rfl⟩ : syracuseStep 3108137 = 2331103) B2331103
theorem B2182463 : Blo 1453546 2182463 := bstep (se 1 (by rfl) ⟨1636847, by rfl⟩ : syracuseStep 2182463 = 3273695) B3273695
theorem B11038031 : Blo 1453546 11038031 := bstep (se 1 (by rfl) ⟨8278523, by rfl⟩ : syracuseStep 11038031 = 16557047) B16557047
theorem B2452943 : Blo 1453546 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B7359983 : Blo 1453546 7359983 := bstep (se 1 (by rfl) ⟨5519987, by rfl⟩ : syracuseStep 7359983 = 11039975) B11039975
theorem B1453775 : Blo 1453546 1453775 := bstep (se 1 (by rfl) ⟨1090331, by rfl⟩ : syracuseStep 1453775 = 2180663) B2180663
theorem B1454191 : Blo 1453546 1454191 := bstep (se 1 (by rfl) ⟨1090643, by rfl⟩ : syracuseStep 1454191 = 2181287) B2181287
theorem B1454951 : Blo 1453546 1454951 := bstep (se 1 (by rfl) ⟨1091213, by rfl⟩ : syracuseStep 1454951 = 2182427) B2182427
theorem B1455103 : Blo 1453546 1455103 := bstep (se 1 (by rfl) ⟨1091327, by rfl⟩ : syracuseStep 1455103 = 2182655) B2182655
theorem B1455207 : Blo 1453546 1455207 := bstep (se 1 (by rfl) ⟨1091405, by rfl⟩ : syracuseStep 1455207 = 2182811) B2182811
theorem B3683819 : Blo 1453546 3683819 := bstep (se 1 (by rfl) ⟨2762864, by rfl⟩ : syracuseStep 3683819 = 5525729) B5525729
theorem B3274271 : Blo 1453546 3274271 := bstep (se 1 (by rfl) ⟨2455703, by rfl⟩ : syracuseStep 3274271 = 4911407) B4911407
theorem B2455103 : Blo 1453546 2455103 := bstep (se 1 (by rfl) ⟨1841327, by rfl⟩ : syracuseStep 2455103 = 3682655) B3682655
theorem B163575571 : Blo 1453546 163575571 := bstep (se 1 (by rfl) ⟨122681678, by rfl⟩ : syracuseStep 163575571 = 245363357) B245363357
theorem B11049209 : Blo 1453546 11049209 := bstep (se 2 (by rfl) ⟨4143453, by rfl⟩ : syracuseStep 11049209 = 8286907) B8286907
theorem B4659643 : Blo 1453546 4659643 := bstep (se 1 (by rfl) ⟨3494732, by rfl⟩ : syracuseStep 4659643 = 6989465) B6989465
theorem B4725715 : Blo 1453546 4725715 := bstep (se 1 (by rfl) ⟨3544286, by rfl⟩ : syracuseStep 4725715 = 7088573) B7088573
theorem B5520383 : Blo 1453546 5520383 := bstep (se 1 (by rfl) ⟨4140287, by rfl⟩ : syracuseStep 5520383 = 8280575) B8280575
theorem B6208825 : Blo 1453546 6208825 := bstep (se 2 (by rfl) ⟨2328309, by rfl⟩ : syracuseStep 6208825 = 4656619) B4656619
theorem B7863929 : Blo 1453546 7863929 := bstep (se 2 (by rfl) ⟨2948973, by rfl⟩ : syracuseStep 7863929 = 5897947) B5897947
theorem B5521067 : Blo 1453546 5521067 := bstep (se 1 (by rfl) ⟨4140800, by rfl⟩ : syracuseStep 5521067 = 8281601) B8281601
theorem B5594807 : Blo 1453546 5594807 := bstep (se 1 (by rfl) ⟨4196105, by rfl⟩ : syracuseStep 5594807 = 8392211) B8392211
theorem B6300953 : Blo 1453546 6300953 := bstep (se 2 (by rfl) ⟨2362857, by rfl⟩ : syracuseStep 6300953 = 4725715) B4725715
theorem B7366139 : Blo 1453546 7366139 := bstep (se 1 (by rfl) ⟨5524604, by rfl⟩ : syracuseStep 7366139 = 11049209) B11049209
theorem B3680255 : Blo 1453546 3680255 := bstep (se 1 (by rfl) ⟨2760191, by rfl⟩ : syracuseStep 3680255 = 5520383) B5520383
theorem B7358687 : Blo 1453546 7358687 := bstep (se 1 (by rfl) ⟨5519015, by rfl⟩ : syracuseStep 7358687 = 11038031) B11038031
theorem B3680711 : Blo 1453546 3680711 := bstep (se 1 (by rfl) ⟨2760533, by rfl⟩ : syracuseStep 3680711 = 5521067) B5521067
theorem B3729871 : Blo 1453546 3729871 := bstep (se 1 (by rfl) ⟨2797403, by rfl⟩ : syracuseStep 3729871 = 5594807) B5594807
theorem B4041535 : Blo 1453546 4041535 := bstep (se 1 (by rfl) ⟨3031151, by rfl⟩ : syracuseStep 4041535 = 6062303) B6062303
theorem B6212857 : Blo 1453546 6212857 := bstep (se 2 (by rfl) ⟨2329821, by rfl⟩ : syracuseStep 6212857 = 4659643) B4659643
theorem B3272039 : Blo 1453546 3272039 := bstep (se 1 (by rfl) ⟨2454029, by rfl⟩ : syracuseStep 3272039 = 4908059) B4908059
theorem B11799913 : Blo 1453546 11799913 := bstep (se 2 (by rfl) ⟨4424967, by rfl⟩ : syracuseStep 11799913 = 8849935) B8849935
theorem B2182847 : Blo 1453546 2182847 := bstep (se 1 (by rfl) ⟨1637135, by rfl⟩ : syracuseStep 2182847 = 3274271) B3274271
theorem B1453807 : Blo 1453546 1453807 := bstep (se 1 (by rfl) ⟨1090355, by rfl⟩ : syracuseStep 1453807 = 2180711) B2180711
theorem B1453983 : Blo 1453546 1453983 := bstep (se 1 (by rfl) ⟨1090487, by rfl⟩ : syracuseStep 1453983 = 2180975) B2180975
theorem B90804149 : Blo 1453546 90804149 := bstep (se 5 (by rfl) ⟨4256444, by rfl⟩ : syracuseStep 90804149 = 8512889) B8512889
theorem B1454079 : Blo 1453546 1454079 := bstep (se 1 (by rfl) ⟨1090559, by rfl⟩ : syracuseStep 1454079 = 2181119) B2181119
theorem B1454151 : Blo 1453546 1454151 := bstep (se 1 (by rfl) ⟨1090613, by rfl⟩ : syracuseStep 1454151 = 2181227) B2181227
theorem B3272795 : Blo 1453546 3272795 := bstep (se 1 (by rfl) ⟨2454596, by rfl⟩ : syracuseStep 3272795 = 4909193) B4909193
theorem B3682543 : Blo 1453546 3682543 := bstep (se 1 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 3682543 = 5523815) B5523815
theorem B8278433 : Blo 1453546 8278433 := bstep (se 2 (by rfl) ⟨3104412, by rfl⟩ : syracuseStep 8278433 = 6208825) B6208825
theorem B1454719 : Blo 1453546 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B1454747 : Blo 1453546 1454747 := bstep (se 1 (by rfl) ⟨1091060, by rfl⟩ : syracuseStep 1454747 = 2182121) B2182121
theorem B1454783 : Blo 1453546 1454783 := bstep (se 1 (by rfl) ⟨1091087, by rfl⟩ : syracuseStep 1454783 = 2182175) B2182175
theorem B1454975 : Blo 1453546 1454975 := bstep (se 1 (by rfl) ⟨1091231, by rfl⟩ : syracuseStep 1454975 = 2182463) B2182463
theorem B1635295 : Blo 1453546 1635295 := bstep (se 1 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 1635295 = 2452943) B2452943
theorem B218100761 : Blo 1453546 218100761 := bstep (se 2 (by rfl) ⟨81787785, by rfl⟩ : syracuseStep 218100761 = 163575571) B163575571
theorem B8288365 : Blo 1453546 8288365 := bstep (se 3 (by rfl) ⟨1554068, by rfl⟩ : syracuseStep 8288365 = 3108137) B3108137
theorem B2455879 : Blo 1453546 2455879 := bstep (se 1 (by rfl) ⟨1841909, by rfl⟩ : syracuseStep 2455879 = 3683819) B3683819
theorem B1636735 : Blo 1453546 1636735 := bstep (se 1 (by rfl) ⟨1227551, by rfl⟩ : syracuseStep 1636735 = 2455103) B2455103
theorem B67213799 : Blo 1453546 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B13982311 : Blo 1453546 13982311 := bstep (se 1 (by rfl) ⟨10486733, by rfl⟩ : syracuseStep 13982311 = 20973467) B20973467
theorem B7364033 : Blo 1453546 7364033 := bstep (se 2 (by rfl) ⟨2761512, by rfl⟩ : syracuseStep 7364033 = 5523025) B5523025
theorem B4906655 : Blo 1453546 4906655 := bstep (se 1 (by rfl) ⟨3679991, by rfl⟩ : syracuseStep 4906655 = 7359983) B7359983
theorem B5242619 : Blo 1453546 5242619 := bstep (se 1 (by rfl) ⟨3931964, by rfl⟩ : syracuseStep 5242619 = 7863929) B7863929
theorem B11051153 : Blo 1453546 11051153 := bstep (se 2 (by rfl) ⟨4144182, by rfl⟩ : syracuseStep 11051153 = 8288365) B8288365
theorem B145400507 : Blo 1453546 145400507 := bstep (se 1 (by rfl) ⟨109050380, by rfl⟩ : syracuseStep 145400507 = 218100761) B218100761
theorem B2180393 : Blo 1453546 2180393 := bstep (se 2 (by rfl) ⟨817647, by rfl⟩ : syracuseStep 2180393 = 1635295) B1635295
theorem B8283809 : Blo 1453546 8283809 := bstep (se 2 (by rfl) ⟨3106428, by rfl⟩ : syracuseStep 8283809 = 6212857) B6212857
theorem B2181359 : Blo 1453546 2181359 := bstep (se 1 (by rfl) ⟨1636019, by rfl⟩ : syracuseStep 2181359 = 3272039) B3272039
theorem B4909355 : Blo 1453546 4909355 := bstep (se 1 (by rfl) ⟨3682016, by rfl⟩ : syracuseStep 4909355 = 7364033) B7364033
theorem B19892645 : Blo 1453546 19892645 := bstep (se 4 (by rfl) ⟨1864935, by rfl⟩ : syracuseStep 19892645 = 3729871) B3729871
theorem B3271103 : Blo 1453546 3271103 := bstep (se 1 (by rfl) ⟨2453327, by rfl⟩ : syracuseStep 3271103 = 4906655) B4906655
theorem B2181863 : Blo 1453546 2181863 := bstep (se 1 (by rfl) ⟨1636397, by rfl⟩ : syracuseStep 2181863 = 3272795) B3272795
theorem B4910057 : Blo 1453546 4910057 := bstep (se 2 (by rfl) ⟨1841271, by rfl⟩ : syracuseStep 4910057 = 3682543) B3682543
theorem B2182313 : Blo 1453546 2182313 := bstep (se 2 (by rfl) ⟨818367, by rfl⟩ : syracuseStep 2182313 = 1636735) B1636735
theorem B4910759 : Blo 1453546 4910759 := bstep (se 1 (by rfl) ⟨3683069, by rfl⟩ : syracuseStep 4910759 = 7366139) B7366139
theorem B2453503 : Blo 1453546 2453503 := bstep (se 1 (by rfl) ⟨1840127, by rfl⟩ : syracuseStep 2453503 = 3680255) B3680255
theorem B2453807 : Blo 1453546 2453807 := bstep (se 1 (by rfl) ⟨1840355, by rfl⟩ : syracuseStep 2453807 = 3680711) B3680711
theorem B15733217 : Blo 1453546 15733217 := bstep (se 2 (by rfl) ⟨5899956, by rfl⟩ : syracuseStep 15733217 = 11799913) B11799913
theorem B1455231 : Blo 1453546 1455231 := bstep (se 1 (by rfl) ⟨1091423, by rfl⟩ : syracuseStep 1455231 = 2182847) B2182847
theorem B3495079 : Blo 1453546 3495079 := bstep (se 1 (by rfl) ⟨2621309, by rfl⟩ : syracuseStep 3495079 = 5242619) B5242619
theorem B60536099 : Blo 1453546 60536099 := bstep (se 1 (by rfl) ⟨45402074, by rfl⟩ : syracuseStep 60536099 = 90804149) B90804149
theorem B5518955 : Blo 1453546 5518955 := bstep (se 1 (by rfl) ⟨4139216, by rfl⟩ : syracuseStep 5518955 = 8278433) B8278433
theorem B3274505 : Blo 1453546 3274505 := bstep (se 2 (by rfl) ⟨1227939, by rfl⟩ : syracuseStep 3274505 = 2455879) B2455879
theorem B18643081 : Blo 1453546 18643081 := bstep (se 2 (by rfl) ⟨6991155, by rfl⟩ : syracuseStep 18643081 = 13982311) B13982311
theorem B4200635 : Blo 1453546 4200635 := bstep (se 1 (by rfl) ⟨3150476, by rfl⟩ : syracuseStep 4200635 = 6300953) B6300953
theorem B5388713 : Blo 1453546 5388713 := bstep (se 2 (by rfl) ⟨2020767, by rfl⟩ : syracuseStep 5388713 = 4041535) B4041535
theorem B4905791 : Blo 1453546 4905791 := bstep (se 1 (by rfl) ⟨3679343, by rfl⟩ : syracuseStep 4905791 = 7358687) B7358687
theorem B44809199 : Blo 1453546 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B3679303 : Blo 1453546 3679303 := bstep (se 1 (by rfl) ⟨2759477, by rfl⟩ : syracuseStep 3679303 = 5518955) B5518955
theorem B5522539 : Blo 1453546 5522539 := bstep (se 1 (by rfl) ⟨4141904, by rfl⟩ : syracuseStep 5522539 = 8283809) B8283809
theorem B2180735 : Blo 1453546 2180735 := bstep (se 1 (by rfl) ⟨1635551, by rfl⟩ : syracuseStep 2180735 = 3271103) B3271103
theorem B3270527 : Blo 1453546 3270527 := bstep (se 1 (by rfl) ⟨2452895, by rfl⟩ : syracuseStep 3270527 = 4905791) B4905791
theorem B3271337 : Blo 1453546 3271337 := bstep (se 2 (by rfl) ⟨1226751, by rfl⟩ : syracuseStep 3271337 = 2453503) B2453503
theorem B7367435 : Blo 1453546 7367435 := bstep (se 1 (by rfl) ⟨5525576, by rfl⟩ : syracuseStep 7367435 = 11051153) B11051153
theorem B24857441 : Blo 1453546 24857441 := bstep (se 2 (by rfl) ⟨9321540, by rfl⟩ : syracuseStep 24857441 = 18643081) B18643081
theorem B10488811 : Blo 1453546 10488811 := bstep (se 1 (by rfl) ⟨7866608, by rfl⟩ : syracuseStep 10488811 = 15733217) B15733217
theorem B40357399 : Blo 1453546 40357399 := bstep (se 1 (by rfl) ⟨30268049, by rfl⟩ : syracuseStep 40357399 = 60536099) B60536099
theorem B1453595 : Blo 1453546 1453595 := bstep (se 1 (by rfl) ⟨1090196, by rfl⟩ : syracuseStep 1453595 = 2180393) B2180393
theorem B1454239 : Blo 1453546 1454239 := bstep (se 1 (by rfl) ⟨1090679, by rfl⟩ : syracuseStep 1454239 = 2181359) B2181359
theorem B3272903 : Blo 1453546 3272903 := bstep (se 1 (by rfl) ⟨2454677, by rfl⟩ : syracuseStep 3272903 = 4909355) B4909355
theorem B3592475 : Blo 1453546 3592475 := bstep (se 1 (by rfl) ⟨2694356, by rfl⟩ : syracuseStep 3592475 = 5388713) B5388713
theorem B1454575 : Blo 1453546 1454575 := bstep (se 1 (by rfl) ⟨1090931, by rfl⟩ : syracuseStep 1454575 = 2181863) B2181863
theorem B3273371 : Blo 1453546 3273371 := bstep (se 1 (by rfl) ⟨2455028, by rfl⟩ : syracuseStep 3273371 = 4910057) B4910057
theorem B29872799 : Blo 1453546 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B1454875 : Blo 1453546 1454875 := bstep (se 1 (by rfl) ⟨1091156, by rfl⟩ : syracuseStep 1454875 = 2182313) B2182313
theorem B3273839 : Blo 1453546 3273839 := bstep (se 1 (by rfl) ⟨2455379, by rfl⟩ : syracuseStep 3273839 = 4910759) B4910759
theorem B1635871 : Blo 1453546 1635871 := bstep (se 1 (by rfl) ⟨1226903, by rfl⟩ : syracuseStep 1635871 = 2453807) B2453807
theorem B96933671 : Blo 1453546 96933671 := bstep (se 1 (by rfl) ⟨72700253, by rfl⟩ : syracuseStep 96933671 = 145400507) B145400507
theorem B2183003 : Blo 1453546 2183003 := bstep (se 1 (by rfl) ⟨1637252, by rfl⟩ : syracuseStep 2183003 = 3274505) B3274505
theorem B2800423 : Blo 1453546 2800423 := bstep (se 1 (by rfl) ⟨2100317, by rfl⟩ : syracuseStep 2800423 = 4200635) B4200635
theorem B4660105 : Blo 1453546 4660105 := bstep (se 2 (by rfl) ⟨1747539, by rfl⟩ : syracuseStep 4660105 = 3495079) B3495079
theorem B13261763 : Blo 1453546 13261763 := bstep (se 1 (by rfl) ⟨9946322, by rfl⟩ : syracuseStep 13261763 = 19892645) B19892645
theorem B19915199 : Blo 1453546 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B2180351 : Blo 1453546 2180351 := bstep (se 1 (by rfl) ⟨1635263, by rfl⟩ : syracuseStep 2180351 = 3270527) B3270527
theorem B13985081 : Blo 1453546 13985081 := bstep (se 2 (by rfl) ⟨5244405, by rfl⟩ : syracuseStep 13985081 = 10488811) B10488811
theorem B2180891 : Blo 1453546 2180891 := bstep (se 1 (by rfl) ⟨1635668, by rfl⟩ : syracuseStep 2180891 = 3271337) B3271337
theorem B2181161 : Blo 1453546 2181161 := bstep (se 2 (by rfl) ⟨817935, by rfl⟩ : syracuseStep 2181161 = 1635871) B1635871
theorem B2181935 : Blo 1453546 2181935 := bstep (se 1 (by rfl) ⟨1636451, by rfl⟩ : syracuseStep 2181935 = 3272903) B3272903
theorem B2394983 : Blo 1453546 2394983 := bstep (se 1 (by rfl) ⟨1796237, by rfl⟩ : syracuseStep 2394983 = 3592475) B3592475
theorem B2182247 : Blo 1453546 2182247 := bstep (se 1 (by rfl) ⟨1636685, by rfl⟩ : syracuseStep 2182247 = 3273371) B3273371
theorem B2182559 : Blo 1453546 2182559 := bstep (se 1 (by rfl) ⟨1636919, by rfl⟩ : syracuseStep 2182559 = 3273839) B3273839
theorem B1453823 : Blo 1453546 1453823 := bstep (se 1 (by rfl) ⟨1090367, by rfl⟩ : syracuseStep 1453823 = 2180735) B2180735
theorem B6213473 : Blo 1453546 6213473 := bstep (se 2 (by rfl) ⟨2330052, by rfl⟩ : syracuseStep 6213473 = 4660105) B4660105
theorem B64622447 : Blo 1453546 64622447 := bstep (se 1 (by rfl) ⟨48466835, by rfl⟩ : syracuseStep 64622447 = 96933671) B96933671
theorem B4911623 : Blo 1453546 4911623 := bstep (se 1 (by rfl) ⟨3683717, by rfl⟩ : syracuseStep 4911623 = 7367435) B7367435
theorem B53809865 : Blo 1453546 53809865 := bstep (se 2 (by rfl) ⟨20178699, by rfl⟩ : syracuseStep 53809865 = 40357399) B40357399
theorem B1455335 : Blo 1453546 1455335 := bstep (se 1 (by rfl) ⟨1091501, by rfl⟩ : syracuseStep 1455335 = 2183003) B2183003
theorem B3733897 : Blo 1453546 3733897 := bstep (se 2 (by rfl) ⟨1400211, by rfl⟩ : syracuseStep 3733897 = 2800423) B2800423
theorem B4905737 : Blo 1453546 4905737 := bstep (se 2 (by rfl) ⟨1839651, by rfl⟩ : syracuseStep 4905737 = 3679303) B3679303
theorem B7363385 : Blo 1453546 7363385 := bstep (se 2 (by rfl) ⟨2761269, by rfl⟩ : syracuseStep 7363385 = 5522539) B5522539
theorem B16571627 : Blo 1453546 16571627 := bstep (se 1 (by rfl) ⟨12428720, by rfl⟩ : syracuseStep 16571627 = 24857441) B24857441
theorem B35364701 : Blo 1453546 35364701 := bstep (se 3 (by rfl) ⟨6630881, by rfl⟩ : syracuseStep 35364701 = 13261763) B13261763
theorem B35873243 : Blo 1453546 35873243 := bstep (se 1 (by rfl) ⟨26904932, by rfl⟩ : syracuseStep 35873243 = 53809865) B53809865
theorem B9323387 : Blo 1453546 9323387 := bstep (se 1 (by rfl) ⟨6992540, by rfl⟩ : syracuseStep 9323387 = 13985081) B13985081
theorem B3270491 : Blo 1453546 3270491 := bstep (se 1 (by rfl) ⟨2452868, by rfl⟩ : syracuseStep 3270491 = 4905737) B4905737
theorem B4908923 : Blo 1453546 4908923 := bstep (se 1 (by rfl) ⟨3681692, by rfl⟩ : syracuseStep 4908923 = 7363385) B7363385
theorem B1453567 : Blo 1453546 1453567 := bstep (se 1 (by rfl) ⟨1090175, by rfl⟩ : syracuseStep 1453567 = 2180351) B2180351
theorem B1453927 : Blo 1453546 1453927 := bstep (se 1 (by rfl) ⟨1090445, by rfl⟩ : syracuseStep 1453927 = 2180891) B2180891
theorem B1454107 : Blo 1453546 1454107 := bstep (se 1 (by rfl) ⟨1090580, by rfl⟩ : syracuseStep 1454107 = 2181161) B2181161
theorem B1454623 : Blo 1453546 1454623 := bstep (se 1 (by rfl) ⟨1090967, by rfl⟩ : syracuseStep 1454623 = 2181935) B2181935
theorem B1454831 : Blo 1453546 1454831 := bstep (se 1 (by rfl) ⟨1091123, by rfl⟩ : syracuseStep 1454831 = 2182247) B2182247
theorem B11047751 : Blo 1453546 11047751 := bstep (se 1 (by rfl) ⟨8285813, by rfl⟩ : syracuseStep 11047751 = 16571627) B16571627
theorem B1455039 : Blo 1453546 1455039 := bstep (se 1 (by rfl) ⟨1091279, by rfl⟩ : syracuseStep 1455039 = 2182559) B2182559
theorem B4142315 : Blo 1453546 4142315 := bstep (se 1 (by rfl) ⟨3106736, by rfl⟩ : syracuseStep 4142315 = 6213473) B6213473
theorem B13276799 : Blo 1453546 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B3274415 : Blo 1453546 3274415 := bstep (se 1 (by rfl) ⟨2455811, by rfl⟩ : syracuseStep 3274415 = 4911623) B4911623
theorem B4978529 : Blo 1453546 4978529 := bstep (se 2 (by rfl) ⟨1866948, by rfl⟩ : syracuseStep 4978529 = 3733897) B3733897
theorem B1596655 : Blo 1453546 1596655 := bstep (se 1 (by rfl) ⟨1197491, by rfl⟩ : syracuseStep 1596655 = 2394983) B2394983
theorem B94305869 : Blo 1453546 94305869 := bstep (se 3 (by rfl) ⟨17682350, by rfl⟩ : syracuseStep 94305869 = 35364701) B35364701
theorem B43081631 : Blo 1453546 43081631 := bstep (se 1 (by rfl) ⟨32311223, by rfl⟩ : syracuseStep 43081631 = 64622447) B64622447
theorem B7365167 : Blo 1453546 7365167 := bstep (se 1 (by rfl) ⟨5523875, by rfl⟩ : syracuseStep 7365167 = 11047751) B11047751
theorem B2761543 : Blo 1453546 2761543 := bstep (se 1 (by rfl) ⟨2071157, by rfl⟩ : syracuseStep 2761543 = 4142315) B4142315
theorem B2180327 : Blo 1453546 2180327 := bstep (se 1 (by rfl) ⟨1635245, by rfl⟩ : syracuseStep 2180327 = 3270491) B3270491
theorem B3319019 : Blo 1453546 3319019 := bstep (se 1 (by rfl) ⟨2489264, by rfl⟩ : syracuseStep 3319019 = 4978529) B4978529
theorem B23915495 : Blo 1453546 23915495 := bstep (se 1 (by rfl) ⟨17936621, by rfl⟩ : syracuseStep 23915495 = 35873243) B35873243
theorem B8851199 : Blo 1453546 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B2182943 : Blo 1453546 2182943 := bstep (se 1 (by rfl) ⟨1637207, by rfl⟩ : syracuseStep 2182943 = 3274415) B3274415
theorem B3272615 : Blo 1453546 3272615 := bstep (se 1 (by rfl) ⟨2454461, by rfl⟩ : syracuseStep 3272615 = 4908923) B4908923
theorem B62870579 : Blo 1453546 62870579 := bstep (se 1 (by rfl) ⟨47152934, by rfl⟩ : syracuseStep 62870579 = 94305869) B94305869
theorem B6215591 : Blo 1453546 6215591 := bstep (se 1 (by rfl) ⟨4661693, by rfl⟩ : syracuseStep 6215591 = 9323387) B9323387
theorem B2128873 : Blo 1453546 2128873 := bstep (se 2 (by rfl) ⟨798327, by rfl⟩ : syracuseStep 2128873 = 1596655) B1596655
theorem B28721087 : Blo 1453546 28721087 := bstep (se 1 (by rfl) ⟨21540815, by rfl⟩ : syracuseStep 28721087 = 43081631) B43081631
theorem B2212679 : Blo 1453546 2212679 := bstep (se 1 (by rfl) ⟨1659509, by rfl⟩ : syracuseStep 2212679 = 3319019) B3319019
theorem B15943663 : Blo 1453546 15943663 := bstep (se 1 (by rfl) ⟨11957747, by rfl⟩ : syracuseStep 15943663 = 23915495) B23915495
theorem B2181743 : Blo 1453546 2181743 := bstep (se 1 (by rfl) ⟨1636307, by rfl⟩ : syracuseStep 2181743 = 3272615) B3272615
theorem B19147391 : Blo 1453546 19147391 := bstep (se 1 (by rfl) ⟨14360543, by rfl⟩ : syracuseStep 19147391 = 28721087) B28721087
theorem B4910111 : Blo 1453546 4910111 := bstep (se 1 (by rfl) ⟨3682583, by rfl⟩ : syracuseStep 4910111 = 7365167) B7365167
theorem B41913719 : Blo 1453546 41913719 := bstep (se 1 (by rfl) ⟨31435289, by rfl⟩ : syracuseStep 41913719 = 62870579) B62870579
theorem B1453551 : Blo 1453546 1453551 := bstep (se 1 (by rfl) ⟨1090163, by rfl⟩ : syracuseStep 1453551 = 2180327) B2180327
theorem B3682057 : Blo 1453546 3682057 := bstep (se 2 (by rfl) ⟨1380771, by rfl⟩ : syracuseStep 3682057 = 2761543) B2761543
theorem B2838497 : Blo 1453546 2838497 := bstep (se 2 (by rfl) ⟨1064436, by rfl⟩ : syracuseStep 2838497 = 2128873) B2128873
theorem B1455295 : Blo 1453546 1455295 := bstep (se 1 (by rfl) ⟨1091471, by rfl⟩ : syracuseStep 1455295 = 2182943) B2182943
theorem B4143727 : Blo 1453546 4143727 := bstep (se 1 (by rfl) ⟨3107795, by rfl⟩ : syracuseStep 4143727 = 6215591) B6215591
theorem B94412789 : Blo 1453546 94412789 := bstep (se 5 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 94412789 = 8851199) B8851199
theorem B1475119 : Blo 1453546 1475119 := bstep (se 1 (by rfl) ⟨1106339, by rfl⟩ : syracuseStep 1475119 = 2212679) B2212679
theorem B12764927 : Blo 1453546 12764927 := bstep (se 1 (by rfl) ⟨9573695, by rfl⟩ : syracuseStep 12764927 = 19147391) B19147391
theorem B4909409 : Blo 1453546 4909409 := bstep (se 2 (by rfl) ⟨1841028, by rfl⟩ : syracuseStep 4909409 = 3682057) B3682057
theorem B62941859 : Blo 1453546 62941859 := bstep (se 1 (by rfl) ⟨47206394, by rfl⟩ : syracuseStep 62941859 = 94412789) B94412789
theorem B5524969 : Blo 1453546 5524969 := bstep (se 2 (by rfl) ⟨2071863, by rfl⟩ : syracuseStep 5524969 = 4143727) B4143727
theorem B1454495 : Blo 1453546 1454495 := bstep (se 1 (by rfl) ⟨1090871, by rfl⟩ : syracuseStep 1454495 = 2181743) B2181743
theorem B3273407 : Blo 1453546 3273407 := bstep (se 1 (by rfl) ⟨2455055, by rfl⟩ : syracuseStep 3273407 = 4910111) B4910111
theorem B27942479 : Blo 1453546 27942479 := bstep (se 1 (by rfl) ⟨20956859, by rfl⟩ : syracuseStep 27942479 = 41913719) B41913719
theorem B7569325 : Blo 1453546 7569325 := bstep (se 3 (by rfl) ⟨1419248, by rfl⟩ : syracuseStep 7569325 = 2838497) B2838497
theorem B21258217 : Blo 1453546 21258217 := bstep (se 2 (by rfl) ⟨7971831, by rfl⟩ : syracuseStep 21258217 = 15943663) B15943663
theorem B1966825 : Blo 1453546 1966825 := bstep (se 2 (by rfl) ⟨737559, by rfl⟩ : syracuseStep 1966825 = 1475119) B1475119
theorem B41961239 : Blo 1453546 41961239 := bstep (se 1 (by rfl) ⟨31470929, by rfl⟩ : syracuseStep 41961239 = 62941859) B62941859
theorem B7366625 : Blo 1453546 7366625 := bstep (se 2 (by rfl) ⟨2762484, by rfl⟩ : syracuseStep 7366625 = 5524969) B5524969
theorem B2182271 : Blo 1453546 2182271 := bstep (se 1 (by rfl) ⟨1636703, by rfl⟩ : syracuseStep 2182271 = 3273407) B3273407
theorem B3272939 : Blo 1453546 3272939 := bstep (se 1 (by rfl) ⟨2454704, by rfl⟩ : syracuseStep 3272939 = 4909409) B4909409
theorem B8509951 : Blo 1453546 8509951 := bstep (se 1 (by rfl) ⟨6382463, by rfl⟩ : syracuseStep 8509951 = 12764927) B12764927
theorem B18628319 : Blo 1453546 18628319 := bstep (se 1 (by rfl) ⟨13971239, by rfl⟩ : syracuseStep 18628319 = 27942479) B27942479
theorem B113377157 : Blo 1453546 113377157 := bstep (se 4 (by rfl) ⟨10629108, by rfl⟩ : syracuseStep 113377157 = 21258217) B21258217
theorem B10092433 : Blo 1453546 10092433 := bstep (se 2 (by rfl) ⟨3784662, by rfl⟩ : syracuseStep 10092433 = 7569325) B7569325
theorem B11346601 : Blo 1453546 11346601 := bstep (se 2 (by rfl) ⟨4254975, by rfl⟩ : syracuseStep 11346601 = 8509951) B8509951
theorem B2181959 : Blo 1453546 2181959 := bstep (se 1 (by rfl) ⟨1636469, by rfl⟩ : syracuseStep 2181959 = 3272939) B3272939
theorem B10489733 : Blo 1453546 10489733 := bstep (se 4 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 10489733 = 1966825) B1966825
theorem B4911083 : Blo 1453546 4911083 := bstep (se 1 (by rfl) ⟨3683312, by rfl⟩ : syracuseStep 4911083 = 7366625) B7366625
theorem B1454847 : Blo 1453546 1454847 := bstep (se 1 (by rfl) ⟨1091135, by rfl⟩ : syracuseStep 1454847 = 2182271) B2182271
theorem B13456577 : Blo 1453546 13456577 := bstep (se 2 (by rfl) ⟨5046216, by rfl⟩ : syracuseStep 13456577 = 10092433) B10092433
theorem B75584771 : Blo 1453546 75584771 := bstep (se 1 (by rfl) ⟨56688578, by rfl⟩ : syracuseStep 75584771 = 113377157) B113377157
theorem B27974159 : Blo 1453546 27974159 := bstep (se 1 (by rfl) ⟨20980619, by rfl⟩ : syracuseStep 27974159 = 41961239) B41961239
theorem B12418879 : Blo 1453546 12418879 := bstep (se 1 (by rfl) ⟨9314159, by rfl⟩ : syracuseStep 12418879 = 18628319) B18628319
theorem B50389847 : Blo 1453546 50389847 := bstep (se 1 (by rfl) ⟨37792385, by rfl⟩ : syracuseStep 50389847 = 75584771) B75584771
theorem B16558505 : Blo 1453546 16558505 := bstep (se 2 (by rfl) ⟨6209439, by rfl⟩ : syracuseStep 16558505 = 12418879) B12418879
theorem B35884205 : Blo 1453546 35884205 := bstep (se 3 (by rfl) ⟨6728288, by rfl⟩ : syracuseStep 35884205 = 13456577) B13456577
theorem B18649439 : Blo 1453546 18649439 := bstep (se 1 (by rfl) ⟨13987079, by rfl⟩ : syracuseStep 18649439 = 27974159) B27974159
theorem B1454639 : Blo 1453546 1454639 := bstep (se 1 (by rfl) ⟨1090979, by rfl⟩ : syracuseStep 1454639 = 2181959) B2181959
theorem B6993155 : Blo 1453546 6993155 := bstep (se 1 (by rfl) ⟨5244866, by rfl⟩ : syracuseStep 6993155 = 10489733) B10489733
theorem B3274055 : Blo 1453546 3274055 := bstep (se 1 (by rfl) ⟨2455541, by rfl⟩ : syracuseStep 3274055 = 4911083) B4911083
theorem B15128801 : Blo 1453546 15128801 := bstep (se 2 (by rfl) ⟨5673300, by rfl⟩ : syracuseStep 15128801 = 11346601) B11346601
theorem B10085867 : Blo 1453546 10085867 := bstep (se 1 (by rfl) ⟨7564400, by rfl⟩ : syracuseStep 10085867 = 15128801) B15128801
theorem B23922803 : Blo 1453546 23922803 := bstep (se 1 (by rfl) ⟨17942102, by rfl⟩ : syracuseStep 23922803 = 35884205) B35884205
theorem B18648413 : Blo 1453546 18648413 := bstep (se 3 (by rfl) ⟨3496577, by rfl⟩ : syracuseStep 18648413 = 6993155) B6993155
theorem B2182703 : Blo 1453546 2182703 := bstep (se 1 (by rfl) ⟨1637027, by rfl⟩ : syracuseStep 2182703 = 3274055) B3274055
theorem B11039003 : Blo 1453546 11039003 := bstep (se 1 (by rfl) ⟨8279252, by rfl⟩ : syracuseStep 11039003 = 16558505) B16558505
theorem B12432959 : Blo 1453546 12432959 := bstep (se 1 (by rfl) ⟨9324719, by rfl⟩ : syracuseStep 12432959 = 18649439) B18649439
theorem B33593231 : Blo 1453546 33593231 := bstep (se 1 (by rfl) ⟨25194923, by rfl⟩ : syracuseStep 33593231 = 50389847) B50389847
theorem B89581949 : Blo 1453546 89581949 := bstep (se 3 (by rfl) ⟨16796615, by rfl⟩ : syracuseStep 89581949 = 33593231) B33593231
theorem B7359335 : Blo 1453546 7359335 := bstep (se 1 (by rfl) ⟨5519501, by rfl⟩ : syracuseStep 7359335 = 11039003) B11039003
theorem B12432275 : Blo 1453546 12432275 := bstep (se 1 (by rfl) ⟨9324206, by rfl⟩ : syracuseStep 12432275 = 18648413) B18648413
theorem B1455135 : Blo 1453546 1455135 := bstep (se 1 (by rfl) ⟨1091351, by rfl⟩ : syracuseStep 1455135 = 2182703) B2182703
theorem B6723911 : Blo 1453546 6723911 := bstep (se 1 (by rfl) ⟨5042933, by rfl⟩ : syracuseStep 6723911 = 10085867) B10085867
theorem B8288639 : Blo 1453546 8288639 := bstep (se 1 (by rfl) ⟨6216479, by rfl⟩ : syracuseStep 8288639 = 12432959) B12432959
theorem B15948535 : Blo 1453546 15948535 := bstep (se 1 (by rfl) ⟨11961401, by rfl⟩ : syracuseStep 15948535 = 23922803) B23922803
theorem B59721299 : Blo 1453546 59721299 := bstep (se 1 (by rfl) ⟨44790974, by rfl⟩ : syracuseStep 59721299 = 89581949) B89581949
theorem B5525759 : Blo 1453546 5525759 := bstep (se 1 (by rfl) ⟨4144319, by rfl⟩ : syracuseStep 5525759 = 8288639) B8288639
theorem B8288183 : Blo 1453546 8288183 := bstep (se 1 (by rfl) ⟨6216137, by rfl⟩ : syracuseStep 8288183 = 12432275) B12432275
theorem B17930429 : Blo 1453546 17930429 := bstep (se 3 (by rfl) ⟨3361955, by rfl⟩ : syracuseStep 17930429 = 6723911) B6723911
theorem B21264713 : Blo 1453546 21264713 := bstep (se 2 (by rfl) ⟨7974267, by rfl⟩ : syracuseStep 21264713 = 15948535) B15948535
theorem B4906223 : Blo 1453546 4906223 := bstep (se 1 (by rfl) ⟨3679667, by rfl⟩ : syracuseStep 4906223 = 7359335) B7359335
theorem B39814199 : Blo 1453546 39814199 := bstep (se 1 (by rfl) ⟨29860649, by rfl⟩ : syracuseStep 39814199 = 59721299) B59721299
theorem B11953619 : Blo 1453546 11953619 := bstep (se 1 (by rfl) ⟨8965214, by rfl⟩ : syracuseStep 11953619 = 17930429) B17930429
theorem B3270815 : Blo 1453546 3270815 := bstep (se 1 (by rfl) ⟨2453111, by rfl⟩ : syracuseStep 3270815 = 4906223) B4906223
theorem B5525455 : Blo 1453546 5525455 := bstep (se 1 (by rfl) ⟨4144091, by rfl⟩ : syracuseStep 5525455 = 8288183) B8288183
theorem B14176475 : Blo 1453546 14176475 := bstep (se 1 (by rfl) ⟨10632356, by rfl⟩ : syracuseStep 14176475 = 21264713) B21264713
theorem B3683839 : Blo 1453546 3683839 := bstep (se 1 (by rfl) ⟨2762879, by rfl⟩ : syracuseStep 3683839 = 5525759) B5525759
theorem B26542799 : Blo 1453546 26542799 := bstep (se 1 (by rfl) ⟨19907099, by rfl⟩ : syracuseStep 26542799 = 39814199) B39814199
theorem B2180543 : Blo 1453546 2180543 := bstep (se 1 (by rfl) ⟨1635407, by rfl⟩ : syracuseStep 2180543 = 3270815) B3270815
theorem B7367273 : Blo 1453546 7367273 := bstep (se 2 (by rfl) ⟨2762727, by rfl⟩ : syracuseStep 7367273 = 5525455) B5525455
theorem B4911785 : Blo 1453546 4911785 := bstep (se 2 (by rfl) ⟨1841919, by rfl⟩ : syracuseStep 4911785 = 3683839) B3683839
theorem B9450983 : Blo 1453546 9450983 := bstep (se 1 (by rfl) ⟨7088237, by rfl⟩ : syracuseStep 9450983 = 14176475) B14176475
theorem B7969079 : Blo 1453546 7969079 := bstep (se 1 (by rfl) ⟨5976809, by rfl⟩ : syracuseStep 7969079 = 11953619) B11953619
theorem B17695199 : Blo 1453546 17695199 := bstep (se 1 (by rfl) ⟨13271399, by rfl⟩ : syracuseStep 17695199 = 26542799) B26542799
theorem B1453695 : Blo 1453546 1453695 := bstep (se 1 (by rfl) ⟨1090271, by rfl⟩ : syracuseStep 1453695 = 2180543) B2180543
theorem B25202621 : Blo 1453546 25202621 := bstep (se 3 (by rfl) ⟨4725491, by rfl⟩ : syracuseStep 25202621 = 9450983) B9450983
theorem B5312719 : Blo 1453546 5312719 := bstep (se 1 (by rfl) ⟨3984539, by rfl⟩ : syracuseStep 5312719 = 7969079) B7969079
theorem B4911515 : Blo 1453546 4911515 := bstep (se 1 (by rfl) ⟨3683636, by rfl⟩ : syracuseStep 4911515 = 7367273) B7367273
theorem B3274523 : Blo 1453546 3274523 := bstep (se 1 (by rfl) ⟨2455892, by rfl⟩ : syracuseStep 3274523 = 4911785) B4911785
theorem B11796799 : Blo 1453546 11796799 := bstep (se 1 (by rfl) ⟨8847599, by rfl⟩ : syracuseStep 11796799 = 17695199) B17695199
theorem B2183015 : Blo 1453546 2183015 := bstep (se 1 (by rfl) ⟨1637261, by rfl⟩ : syracuseStep 2183015 = 3274523) B3274523
theorem B3274343 : Blo 1453546 3274343 := bstep (se 1 (by rfl) ⟨2455757, by rfl⟩ : syracuseStep 3274343 = 4911515) B4911515
theorem B7083625 : Blo 1453546 7083625 := bstep (se 2 (by rfl) ⟨2656359, by rfl⟩ : syracuseStep 7083625 = 5312719) B5312719
theorem B67206989 : Blo 1453546 67206989 := bstep (se 3 (by rfl) ⟨12601310, by rfl⟩ : syracuseStep 67206989 = 25202621) B25202621
theorem B15729065 : Blo 1453546 15729065 := bstep (se 2 (by rfl) ⟨5898399, by rfl⟩ : syracuseStep 15729065 = 11796799) B11796799
theorem B44804659 : Blo 1453546 44804659 := bstep (se 1 (by rfl) ⟨33603494, by rfl⟩ : syracuseStep 44804659 = 67206989) B67206989
theorem B2182895 : Blo 1453546 2182895 := bstep (se 1 (by rfl) ⟨1637171, by rfl⟩ : syracuseStep 2182895 = 3274343) B3274343
theorem B1455343 : Blo 1453546 1455343 := bstep (se 1 (by rfl) ⟨1091507, by rfl⟩ : syracuseStep 1455343 = 2183015) B2183015
theorem B9444833 : Blo 1453546 9444833 := bstep (se 2 (by rfl) ⟨3541812, by rfl⟩ : syracuseStep 9444833 = 7083625) B7083625
theorem B10486043 : Blo 1453546 10486043 := bstep (se 1 (by rfl) ⟨7864532, by rfl⟩ : syracuseStep 10486043 = 15729065) B15729065
theorem B59739545 : Blo 1453546 59739545 := bstep (se 2 (by rfl) ⟨22402329, by rfl⟩ : syracuseStep 59739545 = 44804659) B44804659
theorem B6296555 : Blo 1453546 6296555 := bstep (se 1 (by rfl) ⟨4722416, by rfl⟩ : syracuseStep 6296555 = 9444833) B9444833
theorem B1455263 : Blo 1453546 1455263 := bstep (se 1 (by rfl) ⟨1091447, by rfl⟩ : syracuseStep 1455263 = 2182895) B2182895
theorem B6990695 : Blo 1453546 6990695 := bstep (se 1 (by rfl) ⟨5243021, by rfl⟩ : syracuseStep 6990695 = 10486043) B10486043
theorem B4197703 : Blo 1453546 4197703 := bstep (se 1 (by rfl) ⟨3148277, by rfl⟩ : syracuseStep 4197703 = 6296555) B6296555
theorem B39826363 : Blo 1453546 39826363 := bstep (se 1 (by rfl) ⟨29869772, by rfl⟩ : syracuseStep 39826363 = 59739545) B59739545
theorem B53101817 : Blo 1453546 53101817 := bstep (se 2 (by rfl) ⟨19913181, by rfl⟩ : syracuseStep 53101817 = 39826363) B39826363
theorem B5596937 : Blo 1453546 5596937 := bstep (se 2 (by rfl) ⟨2098851, by rfl⟩ : syracuseStep 5596937 = 4197703) B4197703
theorem B4660463 : Blo 1453546 4660463 := bstep (se 1 (by rfl) ⟨3495347, by rfl⟩ : syracuseStep 4660463 = 6990695) B6990695
theorem B12427901 : Blo 1453546 12427901 := bstep (se 3 (by rfl) ⟨2330231, by rfl⟩ : syracuseStep 12427901 = 4660463) B4660463
theorem B35401211 : Blo 1453546 35401211 := bstep (se 1 (by rfl) ⟨26550908, by rfl⟩ : syracuseStep 35401211 = 53101817) B53101817
theorem B3731291 : Blo 1453546 3731291 := bstep (se 1 (by rfl) ⟨2798468, by rfl⟩ : syracuseStep 3731291 = 5596937) B5596937
theorem B8285267 : Blo 1453546 8285267 := bstep (se 1 (by rfl) ⟨6213950, by rfl⟩ : syracuseStep 8285267 = 12427901) B12427901
theorem B2487527 : Blo 1453546 2487527 := bstep (se 1 (by rfl) ⟨1865645, by rfl⟩ : syracuseStep 2487527 = 3731291) B3731291
theorem B23600807 : Blo 1453546 23600807 := bstep (se 1 (by rfl) ⟨17700605, by rfl⟩ : syracuseStep 23600807 = 35401211) B35401211
theorem B5523511 : Blo 1453546 5523511 := bstep (se 1 (by rfl) ⟨4142633, by rfl⟩ : syracuseStep 5523511 = 8285267) B8285267
theorem B1658351 : Blo 1453546 1658351 := bstep (se 1 (by rfl) ⟨1243763, by rfl⟩ : syracuseStep 1658351 = 2487527) B2487527
theorem B15733871 : Blo 1453546 15733871 := bstep (se 1 (by rfl) ⟨11800403, by rfl⟩ : syracuseStep 15733871 = 23600807) B23600807
theorem B7364681 : Blo 1453546 7364681 := bstep (se 2 (by rfl) ⟨2761755, by rfl⟩ : syracuseStep 7364681 = 5523511) B5523511
theorem B10489247 : Blo 1453546 10489247 := bstep (se 1 (by rfl) ⟨7866935, by rfl⟩ : syracuseStep 10489247 = 15733871) B15733871
theorem B4422269 : Blo 1453546 4422269 := bstep (se 3 (by rfl) ⟨829175, by rfl⟩ : syracuseStep 4422269 = 1658351) B1658351
theorem B4909787 : Blo 1453546 4909787 := bstep (se 1 (by rfl) ⟨3682340, by rfl⟩ : syracuseStep 4909787 = 7364681) B7364681
theorem B6992831 : Blo 1453546 6992831 := bstep (se 1 (by rfl) ⟨5244623, by rfl⟩ : syracuseStep 6992831 = 10489247) B10489247
theorem B2948179 : Blo 1453546 2948179 := bstep (se 1 (by rfl) ⟨2211134, by rfl⟩ : syracuseStep 2948179 = 4422269) B4422269
theorem B4661887 : Blo 1453546 4661887 := bstep (se 1 (by rfl) ⟨3496415, by rfl⟩ : syracuseStep 4661887 = 6992831) B6992831
theorem B3273191 : Blo 1453546 3273191 := bstep (se 1 (by rfl) ⟨2454893, by rfl⟩ : syracuseStep 3273191 = 4909787) B4909787
theorem B3930905 : Blo 1453546 3930905 := bstep (se 2 (by rfl) ⟨1474089, by rfl⟩ : syracuseStep 3930905 = 2948179) B2948179
theorem B2182127 : Blo 1453546 2182127 := bstep (se 1 (by rfl) ⟨1636595, by rfl⟩ : syracuseStep 2182127 = 3273191) B3273191
theorem B6215849 : Blo 1453546 6215849 := bstep (se 2 (by rfl) ⟨2330943, by rfl⟩ : syracuseStep 6215849 = 4661887) B4661887
theorem B2620603 : Blo 1453546 2620603 := bstep (se 1 (by rfl) ⟨1965452, by rfl⟩ : syracuseStep 2620603 = 3930905) B3930905
theorem B13976549 : Blo 1453546 13976549 := bstep (se 4 (by rfl) ⟨1310301, by rfl⟩ : syracuseStep 13976549 = 2620603) B2620603
theorem B1454751 : Blo 1453546 1454751 := bstep (se 1 (by rfl) ⟨1091063, by rfl⟩ : syracuseStep 1454751 = 2182127) B2182127
theorem B4143899 : Blo 1453546 4143899 := bstep (se 1 (by rfl) ⟨3107924, by rfl⟩ : syracuseStep 4143899 = 6215849) B6215849
theorem B2762599 : Blo 1453546 2762599 := bstep (se 1 (by rfl) ⟨2071949, by rfl⟩ : syracuseStep 2762599 = 4143899) B4143899
theorem B9317699 : Blo 1453546 9317699 := bstep (se 1 (by rfl) ⟨6988274, by rfl⟩ : syracuseStep 9317699 = 13976549) B13976549
theorem B6211799 : Blo 1453546 6211799 := bstep (se 1 (by rfl) ⟨4658849, by rfl⟩ : syracuseStep 6211799 = 9317699) B9317699
theorem B3683465 : Blo 1453546 3683465 := bstep (se 2 (by rfl) ⟨1381299, by rfl⟩ : syracuseStep 3683465 = 2762599) B2762599
theorem B4141199 : Blo 1453546 4141199 := bstep (se 1 (by rfl) ⟨3105899, by rfl⟩ : syracuseStep 4141199 = 6211799) B6211799
theorem B2455643 : Blo 1453546 2455643 := bstep (se 1 (by rfl) ⟨1841732, by rfl⟩ : syracuseStep 2455643 = 3683465) B3683465
theorem B2760799 : Blo 1453546 2760799 := bstep (se 1 (by rfl) ⟨2070599, by rfl⟩ : syracuseStep 2760799 = 4141199) B4141199
theorem B1637095 : Blo 1453546 1637095 := bstep (se 1 (by rfl) ⟨1227821, by rfl⟩ : syracuseStep 1637095 = 2455643) B2455643
theorem B3681065 : Blo 1453546 3681065 := bstep (se 2 (by rfl) ⟨1380399, by rfl⟩ : syracuseStep 3681065 = 2760799) B2760799
theorem B2182793 : Blo 1453546 2182793 := bstep (se 2 (by rfl) ⟨818547, by rfl⟩ : syracuseStep 2182793 = 1637095) B1637095
theorem B2454043 : Blo 1453546 2454043 := bstep (se 1 (by rfl) ⟨1840532, by rfl⟩ : syracuseStep 2454043 = 3681065) B3681065
theorem B1455195 : Blo 1453546 1455195 := bstep (se 1 (by rfl) ⟨1091396, by rfl⟩ : syracuseStep 1455195 = 2182793) B2182793
theorem B3272057 : Blo 1453546 3272057 := bstep (se 2 (by rfl) ⟨1227021, by rfl⟩ : syracuseStep 3272057 = 2454043) B2454043
theorem B2181371 : Blo 1453546 2181371 := bstep (se 1 (by rfl) ⟨1636028, by rfl⟩ : syracuseStep 2181371 = 3272057) B3272057
theorem B1454247 : Blo 1453546 1454247 := bstep (se 1 (by rfl) ⟨1090685, by rfl⟩ : syracuseStep 1454247 = 2181371) B2181371

theorem C0 (j : ℕ) (h1 : 363386 ≤ j) (h2 : j ≤ 363885) : Blo 1453546 (4 * j + 3) := by
  interval_cases j
  · exact B1453547
  · exact B1453551
  · exact B1453555
  · exact B1453559
  · exact B1453563
  · exact B1453567
  · exact B1453571
  · exact B1453575
  · exact B1453579
  · exact B1453583
  · exact B1453587
  · exact B1453591
  · exact B1453595
  · exact B1453599
  · exact B1453603
  · exact B1453607
  · exact B1453611
  · exact B1453615
  · exact B1453619
  · exact B1453623
  · exact B1453627
  · exact B1453631
  · exact B1453635
  · exact B1453639
  · exact B1453643
  · exact B1453647
  · exact B1453651
  · exact B1453655
  · exact B1453659
  · exact B1453663
  · exact B1453667
  · exact B1453671
  · exact B1453675
  · exact B1453679
  · exact B1453683
  · exact B1453687
  · exact B1453691
  · exact B1453695
  · exact B1453699
  · exact B1453703
  · exact B1453707
  · exact B1453711
  · exact B1453715
  · exact B1453719
  · exact B1453723
  · exact B1453727
  · exact B1453731
  · exact B1453735
  · exact B1453739
  · exact B1453743
  · exact B1453747
  · exact B1453751
  · exact B1453755
  · exact B1453759
  · exact B1453763
  · exact B1453767
  · exact B1453771
  · exact B1453775
  · exact B1453779
  · exact B1453783
  · exact B1453787
  · exact B1453791
  · exact B1453795
  · exact B1453799
  · exact B1453803
  · exact B1453807
  · exact B1453811
  · exact B1453815
  · exact B1453819
  · exact B1453823
  · exact B1453827
  · exact B1453831
  · exact B1453835
  · exact B1453839
  · exact B1453843
  · exact B1453847
  · exact B1453851
  · exact B1453855
  · exact B1453859
  · exact B1453863
  · exact B1453867
  · exact B1453871
  · exact B1453875
  · exact B1453879
  · exact B1453883
  · exact B1453887
  · exact B1453891
  · exact B1453895
  · exact B1453899
  · exact B1453903
  · exact B1453907
  · exact B1453911
  · exact B1453915
  · exact B1453919
  · exact B1453923
  · exact B1453927
  · exact B1453931
  · exact B1453935
  · exact B1453939
  · exact B1453943
  · exact B1453947
  · exact B1453951
  · exact B1453955
  · exact B1453959
  · exact B1453963
  · exact B1453967
  · exact B1453971
  · exact B1453975
  · exact B1453979
  · exact B1453983
  · exact B1453987
  · exact B1453991
  · exact B1453995
  · exact B1453999
  · exact B1454003
  · exact B1454007
  · exact B1454011
  · exact B1454015
  · exact B1454019
  · exact B1454023
  · exact B1454027
  · exact B1454031
  · exact B1454035
  · exact B1454039
  · exact B1454043
  · exact B1454047
  · exact B1454051
  · exact B1454055
  · exact B1454059
  · exact B1454063
  · exact B1454067
  · exact B1454071
  · exact B1454075
  · exact B1454079
  · exact B1454083
  · exact B1454087
  · exact B1454091
  · exact B1454095
  · exact B1454099
  · exact B1454103
  · exact B1454107
  · exact B1454111
  · exact B1454115
  · exact B1454119
  · exact B1454123
  · exact B1454127
  · exact B1454131
  · exact B1454135
  · exact B1454139
  · exact B1454143
  · exact B1454147
  · exact B1454151
  · exact B1454155
  · exact B1454159
  · exact B1454163
  · exact B1454167
  · exact B1454171
  · exact B1454175
  · exact B1454179
  · exact B1454183
  · exact B1454187
  · exact B1454191
  · exact B1454195
  · exact B1454199
  · exact B1454203
  · exact B1454207
  · exact B1454211
  · exact B1454215
  · exact B1454219
  · exact B1454223
  · exact B1454227
  · exact B1454231
  · exact B1454235
  · exact B1454239
  · exact B1454243
  · exact B1454247
  · exact B1454251
  · exact B1454255
  · exact B1454259
  · exact B1454263
  · exact B1454267
  · exact B1454271
  · exact B1454275
  · exact B1454279
  · exact B1454283
  · exact B1454287
  · exact B1454291
  · exact B1454295
  · exact B1454299
  · exact B1454303
  · exact B1454307
  · exact B1454311
  · exact B1454315
  · exact B1454319
  · exact B1454323
  · exact B1454327
  · exact B1454331
  · exact B1454335
  · exact B1454339
  · exact B1454343
  · exact B1454347
  · exact B1454351
  · exact B1454355
  · exact B1454359
  · exact B1454363
  · exact B1454367
  · exact B1454371
  · exact B1454375
  · exact B1454379
  · exact B1454383
  · exact B1454387
  · exact B1454391
  · exact B1454395
  · exact B1454399
  · exact B1454403
  · exact B1454407
  · exact B1454411
  · exact B1454415
  · exact B1454419
  · exact B1454423
  · exact B1454427
  · exact B1454431
  · exact B1454435
  · exact B1454439
  · exact B1454443
  · exact B1454447
  · exact B1454451
  · exact B1454455
  · exact B1454459
  · exact B1454463
  · exact B1454467
  · exact B1454471
  · exact B1454475
  · exact B1454479
  · exact B1454483
  · exact B1454487
  · exact B1454491
  · exact B1454495
  · exact B1454499
  · exact B1454503
  · exact B1454507
  · exact B1454511
  · exact B1454515
  · exact B1454519
  · exact B1454523
  · exact B1454527
  · exact B1454531
  · exact B1454535
  · exact B1454539
  · exact B1454543
  · exact B1454547
  · exact B1454551
  · exact B1454555
  · exact B1454559
  · exact B1454563
  · exact B1454567
  · exact B1454571
  · exact B1454575
  · exact B1454579
  · exact B1454583
  · exact B1454587
  · exact B1454591
  · exact B1454595
  · exact B1454599
  · exact B1454603
  · exact B1454607
  · exact B1454611
  · exact B1454615
  · exact B1454619
  · exact B1454623
  · exact B1454627
  · exact B1454631
  · exact B1454635
  · exact B1454639
  · exact B1454643
  · exact B1454647
  · exact B1454651
  · exact B1454655
  · exact B1454659
  · exact B1454663
  · exact B1454667
  · exact B1454671
  · exact B1454675
  · exact B1454679
  · exact B1454683
  · exact B1454687
  · exact B1454691
  · exact B1454695
  · exact B1454699
  · exact B1454703
  · exact B1454707
  · exact B1454711
  · exact B1454715
  · exact B1454719
  · exact B1454723
  · exact B1454727
  · exact B1454731
  · exact B1454735
  · exact B1454739
  · exact B1454743
  · exact B1454747
  · exact B1454751
  · exact B1454755
  · exact B1454759
  · exact B1454763
  · exact B1454767
  · exact B1454771
  · exact B1454775
  · exact B1454779
  · exact B1454783
  · exact B1454787
  · exact B1454791
  · exact B1454795
  · exact B1454799
  · exact B1454803
  · exact B1454807
  · exact B1454811
  · exact B1454815
  · exact B1454819
  · exact B1454823
  · exact B1454827
  · exact B1454831
  · exact B1454835
  · exact B1454839
  · exact B1454843
  · exact B1454847
  · exact B1454851
  · exact B1454855
  · exact B1454859
  · exact B1454863
  · exact B1454867
  · exact B1454871
  · exact B1454875
  · exact B1454879
  · exact B1454883
  · exact B1454887
  · exact B1454891
  · exact B1454895
  · exact B1454899
  · exact B1454903
  · exact B1454907
  · exact B1454911
  · exact B1454915
  · exact B1454919
  · exact B1454923
  · exact B1454927
  · exact B1454931
  · exact B1454935
  · exact B1454939
  · exact B1454943
  · exact B1454947
  · exact B1454951
  · exact B1454955
  · exact B1454959
  · exact B1454963
  · exact B1454967
  · exact B1454971
  · exact B1454975
  · exact B1454979
  · exact B1454983
  · exact B1454987
  · exact B1454991
  · exact B1454995
  · exact B1454999
  · exact B1455003
  · exact B1455007
  · exact B1455011
  · exact B1455015
  · exact B1455019
  · exact B1455023
  · exact B1455027
  · exact B1455031
  · exact B1455035
  · exact B1455039
  · exact B1455043
  · exact B1455047
  · exact B1455051
  · exact B1455055
  · exact B1455059
  · exact B1455063
  · exact B1455067
  · exact B1455071
  · exact B1455075
  · exact B1455079
  · exact B1455083
  · exact B1455087
  · exact B1455091
  · exact B1455095
  · exact B1455099
  · exact B1455103
  · exact B1455107
  · exact B1455111
  · exact B1455115
  · exact B1455119
  · exact B1455123
  · exact B1455127
  · exact B1455131
  · exact B1455135
  · exact B1455139
  · exact B1455143
  · exact B1455147
  · exact B1455151
  · exact B1455155
  · exact B1455159
  · exact B1455163
  · exact B1455167
  · exact B1455171
  · exact B1455175
  · exact B1455179
  · exact B1455183
  · exact B1455187
  · exact B1455191
  · exact B1455195
  · exact B1455199
  · exact B1455203
  · exact B1455207
  · exact B1455211
  · exact B1455215
  · exact B1455219
  · exact B1455223
  · exact B1455227
  · exact B1455231
  · exact B1455235
  · exact B1455239
  · exact B1455243
  · exact B1455247
  · exact B1455251
  · exact B1455255
  · exact B1455259
  · exact B1455263
  · exact B1455267
  · exact B1455271
  · exact B1455275
  · exact B1455279
  · exact B1455283
  · exact B1455287
  · exact B1455291
  · exact B1455295
  · exact B1455299
  · exact B1455303
  · exact B1455307
  · exact B1455311
  · exact B1455315
  · exact B1455319
  · exact B1455323
  · exact B1455327
  · exact B1455331
  · exact B1455335
  · exact B1455339
  · exact B1455343
  · exact B1455347
  · exact B1455351
  · exact B1455355
  · exact B1455359
  · exact B1455363
  · exact B1455367
  · exact B1455371
  · exact B1455375
  · exact B1455379
  · exact B1455383
  · exact B1455387
  · exact B1455391
  · exact B1455395
  · exact B1455399
  · exact B1455403
  · exact B1455407
  · exact B1455411
  · exact B1455415
  · exact B1455419
  · exact B1455423
  · exact B1455427
  · exact B1455431
  · exact B1455435
  · exact B1455439
  · exact B1455443
  · exact B1455447
  · exact B1455451
  · exact B1455455
  · exact B1455459
  · exact B1455463
  · exact B1455467
  · exact B1455471
  · exact B1455475
  · exact B1455479
  · exact B1455483
  · exact B1455487
  · exact B1455491
  · exact B1455495
  · exact B1455499
  · exact B1455503
  · exact B1455507
  · exact B1455511
  · exact B1455515
  · exact B1455519
  · exact B1455523
  · exact B1455527
  · exact B1455531
  · exact B1455535
  · exact B1455539
  · exact B1455543

theorem solution (m : ℕ) (hlo : 1453546 ≤ m) (hhi : m ≤ 1455546) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 363386 ≤ j := by omega
    have hj2 : j ≤ 363885 := by omega
    have hb : Blo 1453546 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
