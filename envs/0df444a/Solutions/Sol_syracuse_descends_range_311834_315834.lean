-- Prove2me | solution 1 for syracuse_descends_range_311834_315834
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:23.022468+00:00
-- url     : https://prove2.me/submissions/c90ad333-b7bf-46ac-9635-dccb2730c90e

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


theorem B852133 : Blo 311834 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B1507733 : Blo 311834 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B1901045 : Blo 311834 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B951205 : Blo 311834 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B951301 : Blo 311834 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B361589 : Blo 311834 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B1344869 : Blo 311834 1344869 := bbase (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) (by norm_num)
theorem B820709 : Blo 311834 820709 := bbase (se 4 (by rfl) ⟨76941, by rfl⟩ : syracuseStep 820709 = 153883) (by norm_num)
theorem B394733 : Blo 311834 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B394789 : Blo 311834 394789 := bbase (se 4 (by rfl) ⟨37011, by rfl⟩ : syracuseStep 394789 = 74023) (by norm_num)
theorem B394885 : Blo 311834 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B395057 : Blo 311834 395057 := bbase (se 2 (by rfl) ⟨148146, by rfl⟩ : syracuseStep 395057 = 296293) (by norm_num)
theorem B395113 : Blo 311834 395113 := bbase (se 2 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 395113 = 296335) (by norm_num)
theorem B755605 : Blo 311834 755605 := bbase (se 6 (by rfl) ⟨17709, by rfl⟩ : syracuseStep 755605 = 35419) (by norm_num)
theorem B526277 : Blo 311834 526277 := bbase (se 4 (by rfl) ⟨49338, by rfl⟩ : syracuseStep 526277 = 98677) (by norm_num)
theorem B395209 : Blo 311834 395209 := bbase (se 2 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 395209 = 296407) (by norm_num)
theorem B3213269 : Blo 311834 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B3377173 : Blo 311834 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B526405 : Blo 311834 526405 := bbase (se 4 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 526405 = 98701) (by norm_num)
theorem B755797 : Blo 311834 755797 := bbase (se 8 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 755797 = 8857) (by norm_num)
theorem B395381 : Blo 311834 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B755837 : Blo 311834 755837 := bbase (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) (by norm_num)
theorem B526493 : Blo 311834 526493 := bbase (se 3 (by rfl) ⟨98717, by rfl⟩ : syracuseStep 526493 = 197435) (by norm_num)
theorem B395437 : Blo 311834 395437 := bbase (se 3 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 395437 = 148289) (by norm_num)
theorem B592085 : Blo 311834 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B395533 : Blo 311834 395533 := bbase (se 3 (by rfl) ⟨74162, by rfl⟩ : syracuseStep 395533 = 148325) (by norm_num)
theorem B526621 : Blo 311834 526621 := bbase (se 3 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 526621 = 197483) (by norm_num)
theorem B526709 : Blo 311834 526709 := bbase (se 5 (by rfl) ⟨24689, by rfl⟩ : syracuseStep 526709 = 49379) (by norm_num)
theorem B1509749 : Blo 311834 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B756125 : Blo 311834 756125 := bbase (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) (by norm_num)
theorem B395705 : Blo 311834 395705 := bbase (se 2 (by rfl) ⟨148389, by rfl⟩ : syracuseStep 395705 = 296779) (by norm_num)
theorem B395761 : Blo 311834 395761 := bbase (se 2 (by rfl) ⟨148410, by rfl⟩ : syracuseStep 395761 = 296821) (by norm_num)
theorem B592373 : Blo 311834 592373 := bbase (se 5 (by rfl) ⟨27767, by rfl⟩ : syracuseStep 592373 = 55535) (by norm_num)
theorem B526837 : Blo 311834 526837 := bbase (se 5 (by rfl) ⟨24695, by rfl⟩ : syracuseStep 526837 = 49391) (by norm_num)
theorem B2034229 : Blo 311834 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B1509941 : Blo 311834 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B526925 : Blo 311834 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B395857 : Blo 311834 395857 := bbase (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) (by norm_num)
theorem B592525 : Blo 311834 592525 := bbase (se 3 (by rfl) ⟨111098, by rfl⟩ : syracuseStep 592525 = 222197) (by norm_num)
theorem B527053 : Blo 311834 527053 := bbase (se 3 (by rfl) ⟨98822, by rfl⟩ : syracuseStep 527053 = 197645) (by norm_num)
theorem B396029 : Blo 311834 396029 := bbase (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) (by norm_num)
theorem B527141 : Blo 311834 527141 := bbase (se 4 (by rfl) ⟨49419, by rfl⟩ : syracuseStep 527141 = 98839) (by norm_num)
theorem B396085 : Blo 311834 396085 := bbase (se 5 (by rfl) ⟨18566, by rfl⟩ : syracuseStep 396085 = 37133) (by norm_num)
theorem B789365 : Blo 311834 789365 := bbase (se 5 (by rfl) ⟨37001, by rfl⟩ : syracuseStep 789365 = 74003) (by norm_num)
theorem B396181 : Blo 311834 396181 := bbase (se 6 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 396181 = 18571) (by norm_num)
theorem B527269 : Blo 311834 527269 := bbase (se 4 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 527269 = 98863) (by norm_num)
theorem B592829 : Blo 311834 592829 := bbase (se 3 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 592829 = 222311) (by norm_num)
theorem B527357 : Blo 311834 527357 := bbase (se 3 (by rfl) ⟨98879, by rfl⟩ : syracuseStep 527357 = 197759) (by norm_num)
theorem B396353 : Blo 311834 396353 := bbase (se 2 (by rfl) ⟨148632, by rfl⟩ : syracuseStep 396353 = 297265) (by norm_num)
theorem B1346645 : Blo 311834 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B396409 : Blo 311834 396409 := bbase (se 2 (by rfl) ⟨148653, by rfl⟩ : syracuseStep 396409 = 297307) (by norm_num)
theorem B527485 : Blo 311834 527485 := bbase (se 3 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 527485 = 197807) (by norm_num)
theorem B789709 : Blo 311834 789709 := bbase (se 3 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 789709 = 296141) (by norm_num)
theorem B527573 : Blo 311834 527573 := bbase (se 7 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 527573 = 12365) (by norm_num)
theorem B396505 : Blo 311834 396505 := bbase (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) (by norm_num)
theorem B789821 : Blo 311834 789821 := bbase (se 3 (by rfl) ⟨148091, by rfl⟩ : syracuseStep 789821 = 296183) (by norm_num)
theorem B527701 : Blo 311834 527701 := bbase (se 11 (by rfl) ⟨386, by rfl⟩ : syracuseStep 527701 = 773) (by norm_num)
theorem B396677 : Blo 311834 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B527789 : Blo 311834 527789 := bbase (se 3 (by rfl) ⟨98960, by rfl⟩ : syracuseStep 527789 = 197921) (by norm_num)
theorem B396733 : Blo 311834 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B790013 : Blo 311834 790013 := bbase (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) (by norm_num)
theorem B2559509 : Blo 311834 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B396829 : Blo 311834 396829 := bbase (se 3 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 396829 = 148811) (by norm_num)
theorem B527917 : Blo 311834 527917 := bbase (se 3 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 527917 = 197969) (by norm_num)
theorem B528005 : Blo 311834 528005 := bbase (se 4 (by rfl) ⟨49500, by rfl⟩ : syracuseStep 528005 = 99001) (by norm_num)
theorem B593581 : Blo 311834 593581 := bbase (se 3 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 593581 = 222593) (by norm_num)
theorem B397001 : Blo 311834 397001 := bbase (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) (by norm_num)
theorem B397057 : Blo 311834 397057 := bbase (se 2 (by rfl) ⟨148896, by rfl⟩ : syracuseStep 397057 = 297793) (by norm_num)
theorem B528133 : Blo 311834 528133 := bbase (se 4 (by rfl) ⟨49512, by rfl⟩ : syracuseStep 528133 = 99025) (by norm_num)
theorem B593725 : Blo 311834 593725 := bbase (se 3 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 593725 = 222647) (by norm_num)
theorem B790357 : Blo 311834 790357 := bbase (se 9 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 790357 = 4631) (by norm_num)
theorem B528221 : Blo 311834 528221 := bbase (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) (by norm_num)
theorem B397153 : Blo 311834 397153 := bbase (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) (by norm_num)
theorem B790469 : Blo 311834 790469 := bbase (se 4 (by rfl) ⟨74106, by rfl⟩ : syracuseStep 790469 = 148213) (by norm_num)
theorem B593885 : Blo 311834 593885 := bbase (se 3 (by rfl) ⟨111353, by rfl⟩ : syracuseStep 593885 = 222707) (by norm_num)
theorem B528349 : Blo 311834 528349 := bbase (se 3 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 528349 = 198131) (by norm_num)
theorem B397325 : Blo 311834 397325 := bbase (se 3 (by rfl) ⟨74498, by rfl⟩ : syracuseStep 397325 = 148997) (by norm_num)
theorem B528437 : Blo 311834 528437 := bbase (se 5 (by rfl) ⟨24770, by rfl⟩ : syracuseStep 528437 = 49541) (by norm_num)
theorem B1347637 : Blo 311834 1347637 := bbase (se 5 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 1347637 = 126341) (by norm_num)
theorem B397381 : Blo 311834 397381 := bbase (se 4 (by rfl) ⟨37254, by rfl⟩ : syracuseStep 397381 = 74509) (by norm_num)
theorem B13176917 : Blo 311834 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B594029 : Blo 311834 594029 := bbase (se 3 (by rfl) ⟨111380, by rfl⟩ : syracuseStep 594029 = 222761) (by norm_num)
theorem B790661 : Blo 311834 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B1052837 : Blo 311834 1052837 := bbase (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) (by norm_num)
theorem B397477 : Blo 311834 397477 := bbase (se 4 (by rfl) ⟨37263, by rfl⟩ : syracuseStep 397477 = 74527) (by norm_num)
theorem B528565 : Blo 311834 528565 := bbase (se 5 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 528565 = 49553) (by norm_num)
theorem B528653 : Blo 311834 528653 := bbase (se 3 (by rfl) ⟨99122, by rfl⟩ : syracuseStep 528653 = 198245) (by norm_num)
theorem B397649 : Blo 311834 397649 := bbase (se 2 (by rfl) ⟨149118, by rfl⟩ : syracuseStep 397649 = 298237) (by norm_num)
theorem B954757 : Blo 311834 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B397705 : Blo 311834 397705 := bbase (se 2 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 397705 = 298279) (by norm_num)
theorem B594317 : Blo 311834 594317 := bbase (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) (by norm_num)
theorem B528781 : Blo 311834 528781 := bbase (se 3 (by rfl) ⟨99146, by rfl⟩ : syracuseStep 528781 = 198293) (by norm_num)
theorem B2003413 : Blo 311834 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B791005 : Blo 311834 791005 := bbase (se 3 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 791005 = 296627) (by norm_num)
theorem B528869 : Blo 311834 528869 := bbase (se 4 (by rfl) ⟨49581, by rfl⟩ : syracuseStep 528869 = 99163) (by norm_num)
theorem B397801 : Blo 311834 397801 := bbase (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) (by norm_num)
theorem B594469 : Blo 311834 594469 := bbase (se 4 (by rfl) ⟨55731, by rfl⟩ : syracuseStep 594469 = 111463) (by norm_num)
theorem B791117 : Blo 311834 791117 := bbase (se 3 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 791117 = 296669) (by norm_num)
theorem B1053269 : Blo 311834 1053269 := bbase (se 8 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 1053269 = 12343) (by norm_num)
theorem B528997 : Blo 311834 528997 := bbase (se 4 (by rfl) ⟨49593, by rfl⟩ : syracuseStep 528997 = 99187) (by norm_num)
theorem B1512037 : Blo 311834 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B1217173 : Blo 311834 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B397973 : Blo 311834 397973 := bbase (se 6 (by rfl) ⟨9327, by rfl⟩ : syracuseStep 397973 = 18655) (by norm_num)
theorem B529085 : Blo 311834 529085 := bbase (se 3 (by rfl) ⟨99203, by rfl⟩ : syracuseStep 529085 = 198407) (by norm_num)
theorem B398029 : Blo 311834 398029 := bbase (se 3 (by rfl) ⟨74630, by rfl⟩ : syracuseStep 398029 = 149261) (by norm_num)
theorem B2888405 : Blo 311834 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B791309 : Blo 311834 791309 := bbase (se 3 (by rfl) ⟨148370, by rfl⟩ : syracuseStep 791309 = 296741) (by norm_num)
theorem B398125 : Blo 311834 398125 := bbase (se 3 (by rfl) ⟨74648, by rfl⟩ : syracuseStep 398125 = 149297) (by norm_num)
theorem B529213 : Blo 311834 529213 := bbase (se 3 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 529213 = 198455) (by norm_num)
theorem B594773 : Blo 311834 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B529301 : Blo 311834 529301 := bbase (se 6 (by rfl) ⟨12405, by rfl⟩ : syracuseStep 529301 = 24811) (by norm_num)
theorem B398297 : Blo 311834 398297 := bbase (se 2 (by rfl) ⟨149361, by rfl⟩ : syracuseStep 398297 = 298723) (by norm_num)
theorem B1053701 : Blo 311834 1053701 := bbase (se 4 (by rfl) ⟨98784, by rfl⟩ : syracuseStep 1053701 = 197569) (by norm_num)
theorem B398353 : Blo 311834 398353 := bbase (se 2 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 398353 = 298765) (by norm_num)
theorem B3052565 : Blo 311834 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B529429 : Blo 311834 529429 := bbase (se 6 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 529429 = 24817) (by norm_num)
theorem B791653 : Blo 311834 791653 := bbase (se 4 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 791653 = 148435) (by norm_num)
theorem B529517 : Blo 311834 529517 := bbase (se 3 (by rfl) ⟨99284, by rfl⟩ : syracuseStep 529517 = 198569) (by norm_num)
theorem B398449 : Blo 311834 398449 := bbase (se 2 (by rfl) ⟨149418, by rfl⟩ : syracuseStep 398449 = 298837) (by norm_num)
theorem B889973 : Blo 311834 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B333001 : Blo 311834 333001 := bbase (se 2 (by rfl) ⟨124875, by rfl⟩ : syracuseStep 333001 = 249751) (by norm_num)
theorem B333005 : Blo 311834 333005 := bbase (se 3 (by rfl) ⟨62438, by rfl⟩ : syracuseStep 333005 = 124877) (by norm_num)
theorem B791765 : Blo 311834 791765 := bbase (se 7 (by rfl) ⟨9278, by rfl⟩ : syracuseStep 791765 = 18557) (by norm_num)
theorem B529645 : Blo 311834 529645 := bbase (se 3 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 529645 = 198617) (by norm_num)
theorem B398621 : Blo 311834 398621 := bbase (se 3 (by rfl) ⟨74741, by rfl⟩ : syracuseStep 398621 = 149483) (by norm_num)
theorem B529733 : Blo 311834 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B398677 : Blo 311834 398677 := bbase (se 14 (by rfl) ⟨36, by rfl⟩ : syracuseStep 398677 = 73) (by norm_num)
theorem B1086821 : Blo 311834 1086821 := bbase (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) (by norm_num)
theorem B791957 : Blo 311834 791957 := bbase (se 6 (by rfl) ⟨18561, by rfl⟩ : syracuseStep 791957 = 37123) (by norm_num)
theorem B1054133 : Blo 311834 1054133 := bbase (se 5 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 1054133 = 98825) (by norm_num)
theorem B398773 : Blo 311834 398773 := bbase (se 5 (by rfl) ⟨18692, by rfl⟩ : syracuseStep 398773 = 37385) (by norm_num)
theorem B529861 : Blo 311834 529861 := bbase (se 4 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 529861 = 99349) (by norm_num)
theorem B1218053 : Blo 311834 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B955925 : Blo 311834 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B529949 : Blo 311834 529949 := bbase (se 3 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 529949 = 198731) (by norm_num)
theorem B595525 : Blo 311834 595525 := bbase (se 4 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 595525 = 111661) (by norm_num)
theorem B398945 : Blo 311834 398945 := bbase (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) (by norm_num)
theorem B399001 : Blo 311834 399001 := bbase (se 2 (by rfl) ⟨149625, by rfl⟩ : syracuseStep 399001 = 299251) (by norm_num)
theorem B530077 : Blo 311834 530077 := bbase (se 3 (by rfl) ⟨99389, by rfl⟩ : syracuseStep 530077 = 198779) (by norm_num)
theorem B1185461 : Blo 311834 1185461 := bbase (se 5 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 1185461 = 111137) (by norm_num)
theorem B595669 : Blo 311834 595669 := bbase (se 7 (by rfl) ⟨6980, by rfl⟩ : syracuseStep 595669 = 13961) (by norm_num)
theorem B792301 : Blo 311834 792301 := bbase (se 3 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 792301 = 297113) (by norm_num)
theorem B530165 : Blo 311834 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B399097 : Blo 311834 399097 := bbase (se 2 (by rfl) ⟨149661, by rfl⟩ : syracuseStep 399097 = 299323) (by norm_num)
theorem B333569 : Blo 311834 333569 := bbase (se 2 (by rfl) ⟨125088, by rfl⟩ : syracuseStep 333569 = 250177) (by norm_num)
theorem B5117717 : Blo 311834 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B792413 : Blo 311834 792413 := bbase (se 3 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 792413 = 297155) (by norm_num)
theorem B1054565 : Blo 311834 1054565 := bbase (se 4 (by rfl) ⟨98865, by rfl⟩ : syracuseStep 1054565 = 197731) (by norm_num)
theorem B595829 : Blo 311834 595829 := bbase (se 5 (by rfl) ⟨27929, by rfl⟩ : syracuseStep 595829 = 55859) (by norm_num)
theorem B530293 : Blo 311834 530293 := bbase (se 5 (by rfl) ⟨24857, by rfl⟩ : syracuseStep 530293 = 49715) (by norm_num)
theorem B399269 : Blo 311834 399269 := bbase (se 4 (by rfl) ⟨37431, by rfl⟩ : syracuseStep 399269 = 74863) (by norm_num)
theorem B333757 : Blo 311834 333757 := bbase (se 3 (by rfl) ⟨62579, by rfl⟩ : syracuseStep 333757 = 125159) (by norm_num)
theorem B530381 : Blo 311834 530381 := bbase (se 3 (by rfl) ⟨99446, by rfl⟩ : syracuseStep 530381 = 198893) (by norm_num)
theorem B1185749 : Blo 311834 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B399325 : Blo 311834 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B1579013 : Blo 311834 1579013 := bbase (se 4 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 1579013 = 296065) (by norm_num)
theorem B595973 : Blo 311834 595973 := bbase (se 4 (by rfl) ⟨55872, by rfl⟩ : syracuseStep 595973 = 111745) (by norm_num)
theorem B792605 : Blo 311834 792605 := bbase (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) (by norm_num)
theorem B399421 : Blo 311834 399421 := bbase (se 3 (by rfl) ⟨74891, by rfl⟩ : syracuseStep 399421 = 149783) (by norm_num)
theorem B530509 : Blo 311834 530509 := bbase (se 3 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 530509 = 198941) (by norm_num)
theorem B530597 : Blo 311834 530597 := bbase (se 4 (by rfl) ⟨49743, by rfl⟩ : syracuseStep 530597 = 99487) (by norm_num)
theorem B399593 : Blo 311834 399593 := bbase (se 2 (by rfl) ⟨149847, by rfl⟩ : syracuseStep 399593 = 299695) (by norm_num)
theorem B1054997 : Blo 311834 1054997 := bbase (se 6 (by rfl) ⟨24726, by rfl⟩ : syracuseStep 1054997 = 49453) (by norm_num)
theorem B891157 : Blo 311834 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B399649 : Blo 311834 399649 := bbase (se 2 (by rfl) ⟨149868, by rfl⟩ : syracuseStep 399649 = 299737) (by norm_num)
theorem B596261 : Blo 311834 596261 := bbase (se 4 (by rfl) ⟨55899, by rfl⟩ : syracuseStep 596261 = 111799) (by norm_num)
theorem B530725 : Blo 311834 530725 := bbase (se 4 (by rfl) ⟨49755, by rfl⟩ : syracuseStep 530725 = 99511) (by norm_num)
theorem B792949 : Blo 311834 792949 := bbase (se 5 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 792949 = 74339) (by norm_num)
theorem B530813 : Blo 311834 530813 := bbase (se 3 (by rfl) ⟨99527, by rfl⟩ : syracuseStep 530813 = 199055) (by norm_num)
theorem B891317 : Blo 311834 891317 := bbase (se 5 (by rfl) ⟨41780, by rfl⟩ : syracuseStep 891317 = 83561) (by norm_num)
theorem B596413 : Blo 311834 596413 := bbase (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) (by norm_num)
theorem B793061 : Blo 311834 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B530941 : Blo 311834 530941 := bbase (se 3 (by rfl) ⟨99551, by rfl⟩ : syracuseStep 530941 = 199103) (by norm_num)
theorem B531029 : Blo 311834 531029 := bbase (se 8 (by rfl) ⟨3111, by rfl⟩ : syracuseStep 531029 = 6223) (by norm_num)
theorem B3054229 : Blo 311834 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B891557 : Blo 311834 891557 := bbase (se 4 (by rfl) ⟨83583, by rfl⟩ : syracuseStep 891557 = 167167) (by norm_num)
theorem B793253 : Blo 311834 793253 := bbase (se 4 (by rfl) ⟨74367, by rfl⟩ : syracuseStep 793253 = 148735) (by norm_num)
theorem B1612469 : Blo 311834 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B1055429 : Blo 311834 1055429 := bbase (se 4 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 1055429 = 197893) (by norm_num)
theorem B531157 : Blo 311834 531157 := bbase (se 7 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 531157 = 12449) (by norm_num)
theorem B596717 : Blo 311834 596717 := bbase (se 3 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 596717 = 223769) (by norm_num)
theorem B334577 : Blo 311834 334577 := bbase (se 2 (by rfl) ⟨125466, by rfl⟩ : syracuseStep 334577 = 250933) (by norm_num)
theorem B531245 : Blo 311834 531245 := bbase (se 3 (by rfl) ⟨99608, by rfl⟩ : syracuseStep 531245 = 199217) (by norm_num)
theorem B1776437 : Blo 311834 1776437 := bbase (se 5 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 1776437 = 166541) (by norm_num)
theorem B891749 : Blo 311834 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B531373 : Blo 311834 531373 := bbase (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) (by norm_num)
theorem B1022933 : Blo 311834 1022933 := bbase (se 7 (by rfl) ⟨11987, by rfl⟩ : syracuseStep 1022933 = 23975) (by norm_num)
theorem B400345 : Blo 311834 400345 := bbase (se 2 (by rfl) ⟨150129, by rfl⟩ : syracuseStep 400345 = 300259) (by norm_num)
theorem B793597 : Blo 311834 793597 := bbase (se 3 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 793597 = 297599) (by norm_num)
theorem B531461 : Blo 311834 531461 := bbase (se 4 (by rfl) ⟨49824, by rfl⟩ : syracuseStep 531461 = 99649) (by norm_num)
theorem B400465 : Blo 311834 400465 := bbase (se 2 (by rfl) ⟨150174, by rfl⟩ : syracuseStep 400465 = 300349) (by norm_num)
theorem B793709 : Blo 311834 793709 := bbase (se 3 (by rfl) ⟨148820, by rfl⟩ : syracuseStep 793709 = 297641) (by norm_num)
theorem B1055861 : Blo 311834 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B1186933 : Blo 311834 1186933 := bbase (se 5 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 1186933 = 111275) (by norm_num)
theorem B531589 : Blo 311834 531589 := bbase (se 4 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 531589 = 99673) (by norm_num)
theorem B335021 : Blo 311834 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B531677 : Blo 311834 531677 := bbase (se 3 (by rfl) ⟨99689, by rfl⟩ : syracuseStep 531677 = 199379) (by norm_num)
theorem B1580309 : Blo 311834 1580309 := bbase (se 6 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 1580309 = 74077) (by norm_num)
theorem B793901 : Blo 311834 793901 := bbase (se 3 (by rfl) ⟨148856, by rfl⟩ : syracuseStep 793901 = 297713) (by norm_num)
theorem B531805 : Blo 311834 531805 := bbase (se 3 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 531805 = 199427) (by norm_num)
theorem B1187237 : Blo 311834 1187237 := bbase (se 4 (by rfl) ⟨111303, by rfl⟩ : syracuseStep 1187237 = 222607) (by norm_num)
theorem B335269 : Blo 311834 335269 := bbase (se 4 (by rfl) ⟨31431, by rfl⟩ : syracuseStep 335269 = 62863) (by norm_num)
theorem B531893 : Blo 311834 531893 := bbase (se 5 (by rfl) ⟨24932, by rfl⟩ : syracuseStep 531893 = 49865) (by norm_num)
theorem B597469 : Blo 311834 597469 := bbase (se 3 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 597469 = 224051) (by norm_num)
theorem B1056293 : Blo 311834 1056293 := bbase (se 4 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 1056293 = 198055) (by norm_num)
theorem B532021 : Blo 311834 532021 := bbase (se 5 (by rfl) ⟨24938, by rfl⟩ : syracuseStep 532021 = 49877) (by norm_num)
theorem B597613 : Blo 311834 597613 := bbase (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) (by norm_num)
theorem B794245 : Blo 311834 794245 := bbase (se 4 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 794245 = 148921) (by norm_num)
theorem B532109 : Blo 311834 532109 := bbase (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) (by norm_num)
theorem B794357 : Blo 311834 794357 := bbase (se 5 (by rfl) ⟨37235, by rfl⟩ : syracuseStep 794357 = 74471) (by norm_num)
theorem B597773 : Blo 311834 597773 := bbase (se 3 (by rfl) ⟨112082, by rfl⟩ : syracuseStep 597773 = 224165) (by norm_num)
theorem B532237 : Blo 311834 532237 := bbase (se 3 (by rfl) ⟨99794, by rfl⟩ : syracuseStep 532237 = 199589) (by norm_num)
theorem B892741 : Blo 311834 892741 := bbase (se 4 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 892741 = 167389) (by norm_num)
theorem B335701 : Blo 311834 335701 := bbase (se 9 (by rfl) ⟨983, by rfl⟩ : syracuseStep 335701 = 1967) (by norm_num)
theorem B532325 : Blo 311834 532325 := bbase (se 4 (by rfl) ⟨49905, by rfl⟩ : syracuseStep 532325 = 99811) (by norm_num)
theorem B335773 : Blo 311834 335773 := bbase (se 3 (by rfl) ⟨62957, by rfl⟩ : syracuseStep 335773 = 125915) (by norm_num)
theorem B597917 : Blo 311834 597917 := bbase (se 3 (by rfl) ⟨112109, by rfl⟩ : syracuseStep 597917 = 224219) (by norm_num)
theorem B794549 : Blo 311834 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B1056725 : Blo 311834 1056725 := bbase (se 7 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 1056725 = 24767) (by norm_num)
theorem B532453 : Blo 311834 532453 := bbase (se 4 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 532453 = 99835) (by norm_num)
theorem B532541 : Blo 311834 532541 := bbase (se 3 (by rfl) ⟨99851, by rfl⟩ : syracuseStep 532541 = 199703) (by norm_num)
theorem B499861 : Blo 311834 499861 := bbase (se 6 (by rfl) ⟨11715, by rfl⟩ : syracuseStep 499861 = 23431) (by norm_num)
theorem B598205 : Blo 311834 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B532669 : Blo 311834 532669 := bbase (se 3 (by rfl) ⟨99875, by rfl⟩ : syracuseStep 532669 = 199751) (by norm_num)
theorem B2728181 : Blo 311834 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B794893 : Blo 311834 794893 := bbase (se 3 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 794893 = 298085) (by norm_num)
theorem B336145 : Blo 311834 336145 := bbase (se 2 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 336145 = 252109) (by norm_num)
theorem B532757 : Blo 311834 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B2695477 : Blo 311834 2695477 := bbase (se 5 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 2695477 = 252701) (by norm_num)
theorem B598357 : Blo 311834 598357 := bbase (se 10 (by rfl) ⟨876, by rfl⟩ : syracuseStep 598357 = 1753) (by norm_num)
theorem B795005 : Blo 311834 795005 := bbase (se 3 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 795005 = 298127) (by norm_num)
theorem B1057157 : Blo 311834 1057157 := bbase (se 4 (by rfl) ⟨99108, by rfl⟩ : syracuseStep 1057157 = 198217) (by norm_num)
theorem B532885 : Blo 311834 532885 := bbase (se 6 (by rfl) ⟨12489, by rfl⟩ : syracuseStep 532885 = 24979) (by norm_num)
theorem B1515941 : Blo 311834 1515941 := bbase (se 4 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 1515941 = 284239) (by norm_num)
theorem B1581605 : Blo 311834 1581605 := bbase (se 4 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 1581605 = 296551) (by norm_num)
theorem B795197 : Blo 311834 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B565861 : Blo 311834 565861 := bbase (se 4 (by rfl) ⟨53049, by rfl⟩ : syracuseStep 565861 = 106099) (by norm_num)
theorem B1614437 : Blo 311834 1614437 := bbase (se 4 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 1614437 = 302707) (by norm_num)
theorem B598661 : Blo 311834 598661 := bbase (se 4 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 598661 = 112249) (by norm_num)
theorem B336521 : Blo 311834 336521 := bbase (se 2 (by rfl) ⟨126195, by rfl⟩ : syracuseStep 336521 = 252391) (by norm_num)
theorem B565925 : Blo 311834 565925 := bbase (se 4 (by rfl) ⟨53055, by rfl⟩ : syracuseStep 565925 = 106111) (by norm_num)
theorem B336593 : Blo 311834 336593 := bbase (se 2 (by rfl) ⟨126222, by rfl⟩ : syracuseStep 336593 = 252445) (by norm_num)
theorem B2138869 : Blo 311834 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B2368277 : Blo 311834 2368277 := bbase (se 6 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 2368277 = 111013) (by norm_num)
theorem B467765 : Blo 311834 467765 := bbase (se 5 (by rfl) ⟨21926, by rfl⟩ : syracuseStep 467765 = 43853) (by norm_num)
theorem B1057589 : Blo 311834 1057589 := bbase (se 5 (by rfl) ⟨49574, by rfl⟩ : syracuseStep 1057589 = 99149) (by norm_num)
theorem B467789 : Blo 311834 467789 := bbase (se 3 (by rfl) ⟨87710, by rfl⟩ : syracuseStep 467789 = 175421) (by norm_num)
theorem B467813 : Blo 311834 467813 := bbase (se 4 (by rfl) ⟨43857, by rfl⟩ : syracuseStep 467813 = 87715) (by norm_num)
theorem B467837 : Blo 311834 467837 := bbase (se 3 (by rfl) ⟨87719, by rfl⟩ : syracuseStep 467837 = 175439) (by norm_num)
theorem B336781 : Blo 311834 336781 := bbase (se 3 (by rfl) ⟨63146, by rfl⟩ : syracuseStep 336781 = 126293) (by norm_num)
theorem B467861 : Blo 311834 467861 := bbase (se 6 (by rfl) ⟨10965, by rfl⟩ : syracuseStep 467861 = 21931) (by norm_num)
theorem B893845 : Blo 311834 893845 := bbase (se 6 (by rfl) ⟨20949, by rfl⟩ : syracuseStep 893845 = 41899) (by norm_num)
theorem B795541 : Blo 311834 795541 := bbase (se 6 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 795541 = 37291) (by norm_num)
theorem B467885 : Blo 311834 467885 := bbase (se 3 (by rfl) ⟨87728, by rfl⟩ : syracuseStep 467885 = 175457) (by norm_num)
theorem B467909 : Blo 311834 467909 := bbase (se 4 (by rfl) ⟨43866, by rfl⟩ : syracuseStep 467909 = 87733) (by norm_num)
theorem B467933 : Blo 311834 467933 := bbase (se 3 (by rfl) ⟨87737, by rfl⟩ : syracuseStep 467933 = 175475) (by norm_num)
theorem B402409 : Blo 311834 402409 := bbase (se 2 (by rfl) ⟨150903, by rfl⟩ : syracuseStep 402409 = 301807) (by norm_num)
theorem B467957 : Blo 311834 467957 := bbase (se 5 (by rfl) ⟨21935, by rfl⟩ : syracuseStep 467957 = 43871) (by norm_num)
theorem B795653 : Blo 311834 795653 := bbase (se 4 (by rfl) ⟨74592, by rfl⟩ : syracuseStep 795653 = 149185) (by norm_num)
theorem B467981 : Blo 311834 467981 := bbase (se 3 (by rfl) ⟨87746, by rfl⟩ : syracuseStep 467981 = 175493) (by norm_num)
theorem B468005 : Blo 311834 468005 := bbase (se 4 (by rfl) ⟨43875, by rfl⟩ : syracuseStep 468005 = 87751) (by norm_num)
theorem B500789 : Blo 311834 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B468029 : Blo 311834 468029 := bbase (se 3 (by rfl) ⟨87755, by rfl⟩ : syracuseStep 468029 = 175511) (by norm_num)
theorem B336965 : Blo 311834 336965 := bbase (se 4 (by rfl) ⟨31590, by rfl⟩ : syracuseStep 336965 = 63181) (by norm_num)
theorem B468053 : Blo 311834 468053 := bbase (se 8 (by rfl) ⟨2742, by rfl⟩ : syracuseStep 468053 = 5485) (by norm_num)
theorem B468077 : Blo 311834 468077 := bbase (se 3 (by rfl) ⟨87764, by rfl⟩ : syracuseStep 468077 = 175529) (by norm_num)
theorem B468101 : Blo 311834 468101 := bbase (se 4 (by rfl) ⟨43884, by rfl⟩ : syracuseStep 468101 = 87769) (by norm_num)
theorem B468125 : Blo 311834 468125 := bbase (se 3 (by rfl) ⟨87773, by rfl⟩ : syracuseStep 468125 = 175547) (by norm_num)
theorem B468149 : Blo 311834 468149 := bbase (se 5 (by rfl) ⟨21944, by rfl⟩ : syracuseStep 468149 = 43889) (by norm_num)
theorem B795845 : Blo 311834 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B468173 : Blo 311834 468173 := bbase (se 3 (by rfl) ⟨87782, by rfl⟩ : syracuseStep 468173 = 175565) (by norm_num)
theorem B9086165 : Blo 311834 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B468197 : Blo 311834 468197 := bbase (se 4 (by rfl) ⟨43893, by rfl⟩ : syracuseStep 468197 = 87787) (by norm_num)
theorem B1058021 : Blo 311834 1058021 := bbase (se 4 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 1058021 = 198379) (by norm_num)
theorem B468221 : Blo 311834 468221 := bbase (se 3 (by rfl) ⟨87791, by rfl⟩ : syracuseStep 468221 = 175583) (by norm_num)
theorem B468245 : Blo 311834 468245 := bbase (se 6 (by rfl) ⟨10974, by rfl⟩ : syracuseStep 468245 = 21949) (by norm_num)
theorem B468269 : Blo 311834 468269 := bbase (se 3 (by rfl) ⟨87800, by rfl⟩ : syracuseStep 468269 = 175601) (by norm_num)
theorem B468293 : Blo 311834 468293 := bbase (se 4 (by rfl) ⟨43902, by rfl⟩ : syracuseStep 468293 = 87805) (by norm_num)
theorem B468317 : Blo 311834 468317 := bbase (se 3 (by rfl) ⟨87809, by rfl⟩ : syracuseStep 468317 = 175619) (by norm_num)
theorem B468341 : Blo 311834 468341 := bbase (se 5 (by rfl) ⟨21953, by rfl⟩ : syracuseStep 468341 = 43907) (by norm_num)
theorem B599413 : Blo 311834 599413 := bbase (se 5 (by rfl) ⟨28097, by rfl⟩ : syracuseStep 599413 = 56195) (by norm_num)
theorem B468365 : Blo 311834 468365 := bbase (se 3 (by rfl) ⟨87818, by rfl⟩ : syracuseStep 468365 = 175637) (by norm_num)
theorem B566669 : Blo 311834 566669 := bbase (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) (by norm_num)
theorem B468389 : Blo 311834 468389 := bbase (se 4 (by rfl) ⟨43911, by rfl⟩ : syracuseStep 468389 = 87823) (by norm_num)
theorem B468413 : Blo 311834 468413 := bbase (se 3 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 468413 = 175655) (by norm_num)
theorem B468437 : Blo 311834 468437 := bbase (se 7 (by rfl) ⟨5489, by rfl⟩ : syracuseStep 468437 = 10979) (by norm_num)
theorem B1189349 : Blo 311834 1189349 := bbase (se 4 (by rfl) ⟨111501, by rfl⟩ : syracuseStep 1189349 = 223003) (by norm_num)
theorem B468461 : Blo 311834 468461 := bbase (se 3 (by rfl) ⟨87836, by rfl⟩ : syracuseStep 468461 = 175673) (by norm_num)
theorem B501245 : Blo 311834 501245 := bbase (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) (by norm_num)
theorem B468485 : Blo 311834 468485 := bbase (se 4 (by rfl) ⟨43920, by rfl⟩ : syracuseStep 468485 = 87841) (by norm_num)
theorem B599557 : Blo 311834 599557 := bbase (se 4 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 599557 = 112417) (by norm_num)
theorem B468509 : Blo 311834 468509 := bbase (se 3 (by rfl) ⟨87845, by rfl⟩ : syracuseStep 468509 = 175691) (by norm_num)
theorem B796189 : Blo 311834 796189 := bbase (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) (by norm_num)
theorem B468533 : Blo 311834 468533 := bbase (se 5 (by rfl) ⟨21962, by rfl⟩ : syracuseStep 468533 = 43925) (by norm_num)
theorem B468557 : Blo 311834 468557 := bbase (se 3 (by rfl) ⟨87854, by rfl⟩ : syracuseStep 468557 = 175709) (by norm_num)
theorem B468581 : Blo 311834 468581 := bbase (se 4 (by rfl) ⟨43929, by rfl⟩ : syracuseStep 468581 = 87859) (by norm_num)
theorem B468605 : Blo 311834 468605 := bbase (se 3 (by rfl) ⟨87863, by rfl⟩ : syracuseStep 468605 = 175727) (by norm_num)
theorem B796301 : Blo 311834 796301 := bbase (se 3 (by rfl) ⟨149306, by rfl⟩ : syracuseStep 796301 = 298613) (by norm_num)
theorem B468629 : Blo 311834 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B1058453 : Blo 311834 1058453 := bbase (se 6 (by rfl) ⟨24807, by rfl⟩ : syracuseStep 1058453 = 49615) (by norm_num)
theorem B468653 : Blo 311834 468653 := bbase (se 3 (by rfl) ⟨87872, by rfl⟩ : syracuseStep 468653 = 175745) (by norm_num)
theorem B566957 : Blo 311834 566957 := bbase (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) (by norm_num)
theorem B534205 : Blo 311834 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B468677 : Blo 311834 468677 := bbase (se 4 (by rfl) ⟨43938, by rfl⟩ : syracuseStep 468677 = 87877) (by norm_num)
theorem B468701 : Blo 311834 468701 := bbase (se 3 (by rfl) ⟨87881, by rfl⟩ : syracuseStep 468701 = 175763) (by norm_num)
theorem B468725 : Blo 311834 468725 := bbase (se 5 (by rfl) ⟨21971, by rfl⟩ : syracuseStep 468725 = 43943) (by norm_num)
theorem B1189637 : Blo 311834 1189637 := bbase (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) (by norm_num)
theorem B468749 : Blo 311834 468749 := bbase (se 3 (by rfl) ⟨87890, by rfl⟩ : syracuseStep 468749 = 175781) (by norm_num)
theorem B4073237 : Blo 311834 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B468773 : Blo 311834 468773 := bbase (se 4 (by rfl) ⟨43947, by rfl⟩ : syracuseStep 468773 = 87895) (by norm_num)
theorem B1582901 : Blo 311834 1582901 := bbase (se 5 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 1582901 = 148397) (by norm_num)
theorem B468797 : Blo 311834 468797 := bbase (se 3 (by rfl) ⟨87899, by rfl⟩ : syracuseStep 468797 = 175799) (by norm_num)
theorem B796493 : Blo 311834 796493 := bbase (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) (by norm_num)
theorem B468821 : Blo 311834 468821 := bbase (se 9 (by rfl) ⟨1373, by rfl⟩ : syracuseStep 468821 = 2747) (by norm_num)
theorem B468845 : Blo 311834 468845 := bbase (se 3 (by rfl) ⟨87908, by rfl⟩ : syracuseStep 468845 = 175817) (by norm_num)
theorem B632701 : Blo 311834 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B468869 : Blo 311834 468869 := bbase (se 4 (by rfl) ⟨43956, by rfl⟩ : syracuseStep 468869 = 87913) (by norm_num)
theorem B468893 : Blo 311834 468893 := bbase (se 3 (by rfl) ⟨87917, by rfl⟩ : syracuseStep 468893 = 175835) (by norm_num)
theorem B468917 : Blo 311834 468917 := bbase (se 5 (by rfl) ⟨21980, by rfl⟩ : syracuseStep 468917 = 43961) (by norm_num)
theorem B468941 : Blo 311834 468941 := bbase (se 3 (by rfl) ⟨87926, by rfl⟩ : syracuseStep 468941 = 175853) (by norm_num)
theorem B468965 : Blo 311834 468965 := bbase (se 4 (by rfl) ⟨43965, by rfl⟩ : syracuseStep 468965 = 87931) (by norm_num)
theorem B468989 : Blo 311834 468989 := bbase (se 3 (by rfl) ⟨87935, by rfl⟩ : syracuseStep 468989 = 175871) (by norm_num)
theorem B403465 : Blo 311834 403465 := bbase (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) (by norm_num)
theorem B469013 : Blo 311834 469013 := bbase (se 6 (by rfl) ⟨10992, by rfl⟩ : syracuseStep 469013 = 21985) (by norm_num)
theorem B469037 : Blo 311834 469037 := bbase (se 3 (by rfl) ⟨87944, by rfl⟩ : syracuseStep 469037 = 175889) (by norm_num)
theorem B469061 : Blo 311834 469061 := bbase (se 4 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 469061 = 87949) (by norm_num)
theorem B1058885 : Blo 311834 1058885 := bbase (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) (by norm_num)
theorem B469085 : Blo 311834 469085 := bbase (se 3 (by rfl) ⟨87953, by rfl⟩ : syracuseStep 469085 = 175907) (by norm_num)
theorem B469109 : Blo 311834 469109 := bbase (se 5 (by rfl) ⟨21989, by rfl⟩ : syracuseStep 469109 = 43979) (by norm_num)
theorem B469133 : Blo 311834 469133 := bbase (se 3 (by rfl) ⟨87962, by rfl⟩ : syracuseStep 469133 = 175925) (by norm_num)
theorem B469157 : Blo 311834 469157 := bbase (se 4 (by rfl) ⟨43983, by rfl⟩ : syracuseStep 469157 = 87967) (by norm_num)
theorem B796837 : Blo 311834 796837 := bbase (se 4 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 796837 = 149407) (by norm_num)
theorem B469181 : Blo 311834 469181 := bbase (se 3 (by rfl) ⟨87971, by rfl⟩ : syracuseStep 469181 = 175943) (by norm_num)
theorem B469205 : Blo 311834 469205 := bbase (se 7 (by rfl) ⟨5498, by rfl⟩ : syracuseStep 469205 = 10997) (by norm_num)
theorem B469229 : Blo 311834 469229 := bbase (se 3 (by rfl) ⟨87980, by rfl⟩ : syracuseStep 469229 = 175961) (by norm_num)
theorem B2697461 : Blo 311834 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B469253 : Blo 311834 469253 := bbase (se 4 (by rfl) ⟨43992, by rfl⟩ : syracuseStep 469253 = 87985) (by norm_num)
theorem B796949 : Blo 311834 796949 := bbase (se 6 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 796949 = 37357) (by norm_num)
theorem B469277 : Blo 311834 469277 := bbase (se 3 (by rfl) ⟨87989, by rfl⟩ : syracuseStep 469277 = 175979) (by norm_num)
theorem B469301 : Blo 311834 469301 := bbase (se 5 (by rfl) ⟨21998, by rfl⟩ : syracuseStep 469301 = 43997) (by norm_num)
theorem B469325 : Blo 311834 469325 := bbase (se 3 (by rfl) ⟨87998, by rfl⟩ : syracuseStep 469325 = 175997) (by norm_num)
theorem B469349 : Blo 311834 469349 := bbase (se 4 (by rfl) ⟨44001, by rfl⟩ : syracuseStep 469349 = 88003) (by norm_num)
theorem B895349 : Blo 311834 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B469373 : Blo 311834 469373 := bbase (se 3 (by rfl) ⟨88007, by rfl⟩ : syracuseStep 469373 = 176015) (by norm_num)
theorem B469397 : Blo 311834 469397 := bbase (se 6 (by rfl) ⟨11001, by rfl⟩ : syracuseStep 469397 = 22003) (by norm_num)
theorem B469421 : Blo 311834 469421 := bbase (se 3 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 469421 = 176033) (by norm_num)
theorem B469445 : Blo 311834 469445 := bbase (se 4 (by rfl) ⟨44010, by rfl⟩ : syracuseStep 469445 = 88021) (by norm_num)
theorem B797141 : Blo 311834 797141 := bbase (se 7 (by rfl) ⟨9341, by rfl⟩ : syracuseStep 797141 = 18683) (by norm_num)
theorem B469469 : Blo 311834 469469 := bbase (se 3 (by rfl) ⟨88025, by rfl⟩ : syracuseStep 469469 = 176051) (by norm_num)
theorem B469493 : Blo 311834 469493 := bbase (se 5 (by rfl) ⟨22007, by rfl⟩ : syracuseStep 469493 = 44015) (by norm_num)
theorem B1059317 : Blo 311834 1059317 := bbase (se 5 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 1059317 = 99311) (by norm_num)
theorem B469517 : Blo 311834 469517 := bbase (se 3 (by rfl) ⟨88034, by rfl⟩ : syracuseStep 469517 = 176069) (by norm_num)
theorem B469541 : Blo 311834 469541 := bbase (se 4 (by rfl) ⟨44019, by rfl⟩ : syracuseStep 469541 = 88039) (by norm_num)
theorem B469565 : Blo 311834 469565 := bbase (se 3 (by rfl) ⟨88043, by rfl⟩ : syracuseStep 469565 = 176087) (by norm_num)
theorem B666181 : Blo 311834 666181 := bbase (se 4 (by rfl) ⟨62454, by rfl⟩ : syracuseStep 666181 = 124909) (by norm_num)
theorem B469589 : Blo 311834 469589 := bbase (se 8 (by rfl) ⟨2751, by rfl⟩ : syracuseStep 469589 = 5503) (by norm_num)
theorem B469613 : Blo 311834 469613 := bbase (se 3 (by rfl) ⟨88052, by rfl⟩ : syracuseStep 469613 = 176105) (by norm_num)
theorem B2009717 : Blo 311834 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B469637 : Blo 311834 469637 := bbase (se 4 (by rfl) ⟨44028, by rfl⟩ : syracuseStep 469637 = 88057) (by norm_num)
theorem B469661 : Blo 311834 469661 := bbase (se 3 (by rfl) ⟨88061, by rfl⟩ : syracuseStep 469661 = 176123) (by norm_num)
theorem B469685 : Blo 311834 469685 := bbase (se 5 (by rfl) ⟨22016, by rfl⟩ : syracuseStep 469685 = 44033) (by norm_num)
theorem B666301 : Blo 311834 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B469709 : Blo 311834 469709 := bbase (se 3 (by rfl) ⟨88070, by rfl⟩ : syracuseStep 469709 = 176141) (by norm_num)
theorem B469733 : Blo 311834 469733 := bbase (se 4 (by rfl) ⟨44037, by rfl⟩ : syracuseStep 469733 = 88075) (by norm_num)
theorem B469757 : Blo 311834 469757 := bbase (se 3 (by rfl) ⟨88079, by rfl⟩ : syracuseStep 469757 = 176159) (by norm_num)
theorem B469781 : Blo 311834 469781 := bbase (se 6 (by rfl) ⟨11010, by rfl⟩ : syracuseStep 469781 = 22021) (by norm_num)
theorem B469805 : Blo 311834 469805 := bbase (se 3 (by rfl) ⟨88088, by rfl⟩ : syracuseStep 469805 = 176177) (by norm_num)
theorem B797485 : Blo 311834 797485 := bbase (se 3 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 797485 = 299057) (by norm_num)
theorem B469829 : Blo 311834 469829 := bbase (se 4 (by rfl) ⟨44046, by rfl⟩ : syracuseStep 469829 = 88093) (by norm_num)
theorem B338761 : Blo 311834 338761 := bbase (se 2 (by rfl) ⟨127035, by rfl⟩ : syracuseStep 338761 = 254071) (by norm_num)
theorem B469853 : Blo 311834 469853 := bbase (se 3 (by rfl) ⟨88097, by rfl⟩ : syracuseStep 469853 = 176195) (by norm_num)
theorem B469877 : Blo 311834 469877 := bbase (se 5 (by rfl) ⟨22025, by rfl⟩ : syracuseStep 469877 = 44051) (by norm_num)
theorem B502661 : Blo 311834 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B469901 : Blo 311834 469901 := bbase (se 3 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 469901 = 176213) (by norm_num)
theorem B797597 : Blo 311834 797597 := bbase (se 3 (by rfl) ⟨149549, by rfl⟩ : syracuseStep 797597 = 299099) (by norm_num)
theorem B469925 : Blo 311834 469925 := bbase (se 4 (by rfl) ⟨44055, by rfl⟩ : syracuseStep 469925 = 88111) (by norm_num)
theorem B1190821 : Blo 311834 1190821 := bbase (se 4 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 1190821 = 223279) (by norm_num)
theorem B1059749 : Blo 311834 1059749 := bbase (se 4 (by rfl) ⟨99351, by rfl⟩ : syracuseStep 1059749 = 198703) (by norm_num)
theorem B666557 : Blo 311834 666557 := bbase (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) (by norm_num)
theorem B469949 : Blo 311834 469949 := bbase (se 3 (by rfl) ⟨88115, by rfl⟩ : syracuseStep 469949 = 176231) (by norm_num)
theorem B469973 : Blo 311834 469973 := bbase (se 7 (by rfl) ⟨5507, by rfl⟩ : syracuseStep 469973 = 11015) (by norm_num)
theorem B469997 : Blo 311834 469997 := bbase (se 3 (by rfl) ⟨88124, by rfl⟩ : syracuseStep 469997 = 176249) (by norm_num)
theorem B470021 : Blo 311834 470021 := bbase (se 4 (by rfl) ⟨44064, by rfl⟩ : syracuseStep 470021 = 88129) (by norm_num)
theorem B470045 : Blo 311834 470045 := bbase (se 3 (by rfl) ⟨88133, by rfl⟩ : syracuseStep 470045 = 176267) (by norm_num)
theorem B470069 : Blo 311834 470069 := bbase (se 5 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 470069 = 44069) (by norm_num)
theorem B1584197 : Blo 311834 1584197 := bbase (se 4 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 1584197 = 297037) (by norm_num)
theorem B470093 : Blo 311834 470093 := bbase (se 3 (by rfl) ⟨88142, by rfl⟩ : syracuseStep 470093 = 176285) (by norm_num)
theorem B568405 : Blo 311834 568405 := bbase (se 8 (by rfl) ⟨3330, by rfl⟩ : syracuseStep 568405 = 6661) (by norm_num)
theorem B797789 : Blo 311834 797789 := bbase (se 3 (by rfl) ⟨149585, by rfl⟩ : syracuseStep 797789 = 299171) (by norm_num)
theorem B470117 : Blo 311834 470117 := bbase (se 4 (by rfl) ⟨44073, by rfl⟩ : syracuseStep 470117 = 88147) (by norm_num)
theorem B502885 : Blo 311834 502885 := bbase (se 4 (by rfl) ⟨47145, by rfl⟩ : syracuseStep 502885 = 94291) (by norm_num)
theorem B470141 : Blo 311834 470141 := bbase (se 3 (by rfl) ⟨88151, by rfl⟩ : syracuseStep 470141 = 176303) (by norm_num)
theorem B470165 : Blo 311834 470165 := bbase (se 6 (by rfl) ⟨11019, by rfl⟩ : syracuseStep 470165 = 22039) (by norm_num)
theorem B470189 : Blo 311834 470189 := bbase (se 3 (by rfl) ⟨88160, by rfl⟩ : syracuseStep 470189 = 176321) (by norm_num)
theorem B765101 : Blo 311834 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B470213 : Blo 311834 470213 := bbase (se 4 (by rfl) ⟨44082, by rfl⟩ : syracuseStep 470213 = 88165) (by norm_num)
theorem B1191125 : Blo 311834 1191125 := bbase (se 7 (by rfl) ⟨13958, by rfl⟩ : syracuseStep 1191125 = 27917) (by norm_num)
theorem B470237 : Blo 311834 470237 := bbase (se 3 (by rfl) ⟨88169, by rfl⟩ : syracuseStep 470237 = 176339) (by norm_num)
theorem B568549 : Blo 311834 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B470261 : Blo 311834 470261 := bbase (se 5 (by rfl) ⟨22043, by rfl⟩ : syracuseStep 470261 = 44087) (by norm_num)
theorem B470285 : Blo 311834 470285 := bbase (se 3 (by rfl) ⟨88178, by rfl⟩ : syracuseStep 470285 = 176357) (by norm_num)
theorem B470309 : Blo 311834 470309 := bbase (se 4 (by rfl) ⟨44091, by rfl⟩ : syracuseStep 470309 = 88183) (by norm_num)
theorem B470333 : Blo 311834 470333 := bbase (se 3 (by rfl) ⟨88187, by rfl⟩ : syracuseStep 470333 = 176375) (by norm_num)
theorem B470357 : Blo 311834 470357 := bbase (se 11 (by rfl) ⟨344, by rfl⟩ : syracuseStep 470357 = 689) (by norm_num)
theorem B1060181 : Blo 311834 1060181 := bbase (se 11 (by rfl) ⟨776, by rfl⟩ : syracuseStep 1060181 = 1553) (by norm_num)
theorem B3026261 : Blo 311834 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B470381 : Blo 311834 470381 := bbase (se 3 (by rfl) ⟨88196, by rfl⟩ : syracuseStep 470381 = 176393) (by norm_num)
theorem B470405 : Blo 311834 470405 := bbase (se 4 (by rfl) ⟨44100, by rfl⟩ : syracuseStep 470405 = 88201) (by norm_num)
theorem B470429 : Blo 311834 470429 := bbase (se 3 (by rfl) ⟨88205, by rfl⟩ : syracuseStep 470429 = 176411) (by norm_num)
theorem B470453 : Blo 311834 470453 := bbase (se 5 (by rfl) ⟨22052, by rfl⟩ : syracuseStep 470453 = 44105) (by norm_num)
theorem B798133 : Blo 311834 798133 := bbase (se 5 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 798133 = 74825) (by norm_num)
theorem B470477 : Blo 311834 470477 := bbase (se 3 (by rfl) ⟨88214, by rfl⟩ : syracuseStep 470477 = 176429) (by norm_num)
theorem B470501 : Blo 311834 470501 := bbase (se 4 (by rfl) ⟨44109, by rfl⟩ : syracuseStep 470501 = 88219) (by norm_num)
theorem B470525 : Blo 311834 470525 := bbase (se 3 (by rfl) ⟨88223, by rfl⟩ : syracuseStep 470525 = 176447) (by norm_num)
theorem B470549 : Blo 311834 470549 := bbase (se 6 (by rfl) ⟨11028, by rfl⟩ : syracuseStep 470549 = 22057) (by norm_num)
theorem B798245 : Blo 311834 798245 := bbase (se 4 (by rfl) ⟨74835, by rfl⟩ : syracuseStep 798245 = 149671) (by norm_num)
theorem B470573 : Blo 311834 470573 := bbase (se 3 (by rfl) ⟨88232, by rfl⟩ : syracuseStep 470573 = 176465) (by norm_num)
theorem B405037 : Blo 311834 405037 := bbase (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) (by norm_num)
theorem B470597 : Blo 311834 470597 := bbase (se 4 (by rfl) ⟨44118, by rfl⟩ : syracuseStep 470597 = 88237) (by norm_num)
theorem B831061 : Blo 311834 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B470621 : Blo 311834 470621 := bbase (se 3 (by rfl) ⟨88241, by rfl⟩ : syracuseStep 470621 = 176483) (by norm_num)
theorem B470645 : Blo 311834 470645 := bbase (se 5 (by rfl) ⟨22061, by rfl⟩ : syracuseStep 470645 = 44123) (by norm_num)
theorem B470669 : Blo 311834 470669 := bbase (se 3 (by rfl) ⟨88250, by rfl⟩ : syracuseStep 470669 = 176501) (by norm_num)
theorem B470693 : Blo 311834 470693 := bbase (se 4 (by rfl) ⟨44127, by rfl⟩ : syracuseStep 470693 = 88255) (by norm_num)
theorem B470717 : Blo 311834 470717 := bbase (se 3 (by rfl) ⟨88259, by rfl⟩ : syracuseStep 470717 = 176519) (by norm_num)
theorem B470741 : Blo 311834 470741 := bbase (se 7 (by rfl) ⟨5516, by rfl⟩ : syracuseStep 470741 = 11033) (by norm_num)
theorem B798437 : Blo 311834 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B470765 : Blo 311834 470765 := bbase (se 3 (by rfl) ⟨88268, by rfl⟩ : syracuseStep 470765 = 176537) (by norm_num)
theorem B470789 : Blo 311834 470789 := bbase (se 4 (by rfl) ⟨44136, by rfl⟩ : syracuseStep 470789 = 88273) (by norm_num)
theorem B1060613 : Blo 311834 1060613 := bbase (se 4 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 1060613 = 198865) (by norm_num)
theorem B470813 : Blo 311834 470813 := bbase (se 3 (by rfl) ⟨88277, by rfl⟩ : syracuseStep 470813 = 176555) (by norm_num)
theorem B667445 : Blo 311834 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B470837 : Blo 311834 470837 := bbase (se 5 (by rfl) ⟨22070, by rfl⟩ : syracuseStep 470837 = 44141) (by norm_num)
theorem B470861 : Blo 311834 470861 := bbase (se 3 (by rfl) ⟨88286, by rfl⟩ : syracuseStep 470861 = 176573) (by norm_num)
theorem B470885 : Blo 311834 470885 := bbase (se 4 (by rfl) ⟨44145, by rfl⟩ : syracuseStep 470885 = 88291) (by norm_num)
theorem B470909 : Blo 311834 470909 := bbase (se 3 (by rfl) ⟨88295, by rfl⟩ : syracuseStep 470909 = 176591) (by norm_num)
theorem B470933 : Blo 311834 470933 := bbase (se 6 (by rfl) ⟨11037, by rfl⟩ : syracuseStep 470933 = 22075) (by norm_num)
theorem B896933 : Blo 311834 896933 := bbase (se 4 (by rfl) ⟨84087, by rfl⟩ : syracuseStep 896933 = 168175) (by norm_num)
theorem B470957 : Blo 311834 470957 := bbase (se 3 (by rfl) ⟨88304, by rfl⟩ : syracuseStep 470957 = 176609) (by norm_num)
theorem B470981 : Blo 311834 470981 := bbase (se 4 (by rfl) ⟨44154, by rfl⟩ : syracuseStep 470981 = 88309) (by norm_num)
theorem B471005 : Blo 311834 471005 := bbase (se 3 (by rfl) ⟨88313, by rfl⟩ : syracuseStep 471005 = 176627) (by norm_num)
theorem B471029 : Blo 311834 471029 := bbase (se 5 (by rfl) ⟨22079, by rfl⟩ : syracuseStep 471029 = 44159) (by norm_num)
theorem B471053 : Blo 311834 471053 := bbase (se 3 (by rfl) ⟨88322, by rfl⟩ : syracuseStep 471053 = 176645) (by norm_num)
theorem B667685 : Blo 311834 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B471077 : Blo 311834 471077 := bbase (se 4 (by rfl) ⟨44163, by rfl⟩ : syracuseStep 471077 = 88327) (by norm_num)
theorem B471101 : Blo 311834 471101 := bbase (se 3 (by rfl) ⟨88331, by rfl⟩ : syracuseStep 471101 = 176663) (by norm_num)
theorem B798781 : Blo 311834 798781 := bbase (se 3 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 798781 = 299543) (by norm_num)
theorem B471125 : Blo 311834 471125 := bbase (se 8 (by rfl) ⟨2760, by rfl⟩ : syracuseStep 471125 = 5521) (by norm_num)
theorem B471149 : Blo 311834 471149 := bbase (se 3 (by rfl) ⟨88340, by rfl⟩ : syracuseStep 471149 = 176681) (by norm_num)
theorem B471173 : Blo 311834 471173 := bbase (se 4 (by rfl) ⟨44172, by rfl⟩ : syracuseStep 471173 = 88345) (by norm_num)
theorem B471197 : Blo 311834 471197 := bbase (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) (by norm_num)
theorem B536749 : Blo 311834 536749 := bbase (se 3 (by rfl) ⟨100640, by rfl⟩ : syracuseStep 536749 = 201281) (by norm_num)
theorem B798893 : Blo 311834 798893 := bbase (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) (by norm_num)
theorem B471221 : Blo 311834 471221 := bbase (se 5 (by rfl) ⟨22088, by rfl⟩ : syracuseStep 471221 = 44177) (by norm_num)
theorem B1061045 : Blo 311834 1061045 := bbase (se 5 (by rfl) ⟨49736, by rfl⟩ : syracuseStep 1061045 = 99473) (by norm_num)
theorem B471245 : Blo 311834 471245 := bbase (se 3 (by rfl) ⟨88358, by rfl⟩ : syracuseStep 471245 = 176717) (by norm_num)
theorem B471269 : Blo 311834 471269 := bbase (se 4 (by rfl) ⟨44181, by rfl⟩ : syracuseStep 471269 = 88363) (by norm_num)
theorem B471293 : Blo 311834 471293 := bbase (se 3 (by rfl) ⟨88367, by rfl⟩ : syracuseStep 471293 = 176735) (by norm_num)
theorem B471317 : Blo 311834 471317 := bbase (se 6 (by rfl) ⟨11046, by rfl⟩ : syracuseStep 471317 = 22093) (by norm_num)
theorem B471341 : Blo 311834 471341 := bbase (se 3 (by rfl) ⟨88376, by rfl⟩ : syracuseStep 471341 = 176753) (by norm_num)
theorem B471365 : Blo 311834 471365 := bbase (se 4 (by rfl) ⟨44190, by rfl⟩ : syracuseStep 471365 = 88381) (by norm_num)
theorem B1585493 : Blo 311834 1585493 := bbase (se 10 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 1585493 = 4645) (by norm_num)
theorem B471389 : Blo 311834 471389 := bbase (se 3 (by rfl) ⟨88385, by rfl⟩ : syracuseStep 471389 = 176771) (by norm_num)
theorem B799085 : Blo 311834 799085 := bbase (se 3 (by rfl) ⟨149828, by rfl⟩ : syracuseStep 799085 = 299657) (by norm_num)
theorem B471413 : Blo 311834 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B471437 : Blo 311834 471437 := bbase (se 3 (by rfl) ⟨88394, by rfl⟩ : syracuseStep 471437 = 176789) (by norm_num)
theorem B471461 : Blo 311834 471461 := bbase (se 4 (by rfl) ⟨44199, by rfl⟩ : syracuseStep 471461 = 88399) (by norm_num)
theorem B471485 : Blo 311834 471485 := bbase (se 3 (by rfl) ⟨88403, by rfl⟩ : syracuseStep 471485 = 176807) (by norm_num)
theorem B471509 : Blo 311834 471509 := bbase (se 7 (by rfl) ⟨5525, by rfl⟩ : syracuseStep 471509 = 11051) (by norm_num)
theorem B471533 : Blo 311834 471533 := bbase (se 3 (by rfl) ⟨88412, by rfl⟩ : syracuseStep 471533 = 176825) (by norm_num)
theorem B504301 : Blo 311834 504301 := bbase (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) (by norm_num)
theorem B471557 : Blo 311834 471557 := bbase (se 4 (by rfl) ⟨44208, by rfl⟩ : syracuseStep 471557 = 88417) (by norm_num)
theorem B668189 : Blo 311834 668189 := bbase (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) (by norm_num)
theorem B471581 : Blo 311834 471581 := bbase (se 3 (by rfl) ⟨88421, by rfl⟩ : syracuseStep 471581 = 176843) (by norm_num)
theorem B668197 : Blo 311834 668197 := bbase (se 4 (by rfl) ⟨62643, by rfl⟩ : syracuseStep 668197 = 125287) (by norm_num)
theorem B471605 : Blo 311834 471605 := bbase (se 5 (by rfl) ⟨22106, by rfl⟩ : syracuseStep 471605 = 44213) (by norm_num)
theorem B897605 : Blo 311834 897605 := bbase (se 4 (by rfl) ⟨84150, by rfl⟩ : syracuseStep 897605 = 168301) (by norm_num)
theorem B471629 : Blo 311834 471629 := bbase (se 3 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 471629 = 176861) (by norm_num)
theorem B471653 : Blo 311834 471653 := bbase (se 4 (by rfl) ⟨44217, by rfl⟩ : syracuseStep 471653 = 88435) (by norm_num)
theorem B1061477 : Blo 311834 1061477 := bbase (se 4 (by rfl) ⟨99513, by rfl⟩ : syracuseStep 1061477 = 199027) (by norm_num)
theorem B471677 : Blo 311834 471677 := bbase (se 3 (by rfl) ⟨88439, by rfl⟩ : syracuseStep 471677 = 176879) (by norm_num)
theorem B471701 : Blo 311834 471701 := bbase (se 6 (by rfl) ⟨11055, by rfl⟩ : syracuseStep 471701 = 22111) (by norm_num)
theorem B471725 : Blo 311834 471725 := bbase (se 3 (by rfl) ⟨88448, by rfl⟩ : syracuseStep 471725 = 176897) (by norm_num)
theorem B471749 : Blo 311834 471749 := bbase (se 4 (by rfl) ⟨44226, by rfl⟩ : syracuseStep 471749 = 88453) (by norm_num)
theorem B799429 : Blo 311834 799429 := bbase (se 4 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 799429 = 149893) (by norm_num)
theorem B471773 : Blo 311834 471773 := bbase (se 3 (by rfl) ⟨88457, by rfl⟩ : syracuseStep 471773 = 176915) (by norm_num)
theorem B504557 : Blo 311834 504557 := bbase (se 3 (by rfl) ⟨94604, by rfl⟩ : syracuseStep 504557 = 189209) (by norm_num)
theorem B471797 : Blo 311834 471797 := bbase (se 5 (by rfl) ⟨22115, by rfl⟩ : syracuseStep 471797 = 44231) (by norm_num)
theorem B471821 : Blo 311834 471821 := bbase (se 3 (by rfl) ⟨88466, by rfl⟩ : syracuseStep 471821 = 176933) (by norm_num)
theorem B471845 : Blo 311834 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B471869 : Blo 311834 471869 := bbase (se 3 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 471869 = 176951) (by norm_num)
theorem B471893 : Blo 311834 471893 := bbase (se 9 (by rfl) ⟨1382, by rfl⟩ : syracuseStep 471893 = 2765) (by norm_num)
theorem B471917 : Blo 311834 471917 := bbase (se 3 (by rfl) ⟨88484, by rfl⟩ : syracuseStep 471917 = 176969) (by norm_num)
theorem B471941 : Blo 311834 471941 := bbase (se 4 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 471941 = 88489) (by norm_num)
theorem B471965 : Blo 311834 471965 := bbase (se 3 (by rfl) ⟨88493, by rfl⟩ : syracuseStep 471965 = 176987) (by norm_num)
theorem B504749 : Blo 311834 504749 := bbase (se 3 (by rfl) ⟨94640, by rfl⟩ : syracuseStep 504749 = 189281) (by norm_num)
theorem B471989 : Blo 311834 471989 := bbase (se 5 (by rfl) ⟨22124, by rfl⟩ : syracuseStep 471989 = 44249) (by norm_num)
theorem B472013 : Blo 311834 472013 := bbase (se 3 (by rfl) ⟨88502, by rfl⟩ : syracuseStep 472013 = 177005) (by norm_num)
theorem B472037 : Blo 311834 472037 := bbase (se 4 (by rfl) ⟨44253, by rfl⟩ : syracuseStep 472037 = 88507) (by norm_num)
theorem B898037 : Blo 311834 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B472061 : Blo 311834 472061 := bbase (se 3 (by rfl) ⟨88511, by rfl⟩ : syracuseStep 472061 = 177023) (by norm_num)
theorem B1061909 : Blo 311834 1061909 := bbase (se 6 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 1061909 = 49777) (by norm_num)
theorem B472085 : Blo 311834 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B472109 : Blo 311834 472109 := bbase (se 3 (by rfl) ⟨88520, by rfl⟩ : syracuseStep 472109 = 177041) (by norm_num)
theorem B472133 : Blo 311834 472133 := bbase (se 4 (by rfl) ⟨44262, by rfl⟩ : syracuseStep 472133 = 88525) (by norm_num)
theorem B341065 : Blo 311834 341065 := bbase (se 2 (by rfl) ⟨127899, by rfl⟩ : syracuseStep 341065 = 255799) (by norm_num)
theorem B472157 : Blo 311834 472157 := bbase (se 3 (by rfl) ⟨88529, by rfl⟩ : syracuseStep 472157 = 177059) (by norm_num)
theorem B472181 : Blo 311834 472181 := bbase (se 5 (by rfl) ⟨22133, by rfl⟩ : syracuseStep 472181 = 44267) (by norm_num)
theorem B472205 : Blo 311834 472205 := bbase (se 3 (by rfl) ⟨88538, by rfl⟩ : syracuseStep 472205 = 177077) (by norm_num)
theorem B472229 : Blo 311834 472229 := bbase (se 4 (by rfl) ⟨44271, by rfl⟩ : syracuseStep 472229 = 88543) (by norm_num)
theorem B472253 : Blo 311834 472253 := bbase (se 3 (by rfl) ⟨88547, by rfl⟩ : syracuseStep 472253 = 177095) (by norm_num)
theorem B472277 : Blo 311834 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B472301 : Blo 311834 472301 := bbase (se 3 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 472301 = 177113) (by norm_num)
theorem B701693 : Blo 311834 701693 := bbase (se 3 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 701693 = 263135) (by norm_num)
theorem B472325 : Blo 311834 472325 := bbase (se 4 (by rfl) ⟨44280, by rfl⟩ : syracuseStep 472325 = 88561) (by norm_num)
theorem B1193237 : Blo 311834 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B472349 : Blo 311834 472349 := bbase (se 3 (by rfl) ⟨88565, by rfl⟩ : syracuseStep 472349 = 177131) (by norm_num)
theorem B472373 : Blo 311834 472373 := bbase (se 5 (by rfl) ⟨22142, by rfl⟩ : syracuseStep 472373 = 44285) (by norm_num)
theorem B701765 : Blo 311834 701765 := bbase (se 4 (by rfl) ⟨65790, by rfl⟩ : syracuseStep 701765 = 131581) (by norm_num)
theorem B472397 : Blo 311834 472397 := bbase (se 3 (by rfl) ⟨88574, by rfl⟩ : syracuseStep 472397 = 177149) (by norm_num)
theorem B636245 : Blo 311834 636245 := bbase (se 13 (by rfl) ⟨116, by rfl⟩ : syracuseStep 636245 = 233) (by norm_num)
theorem B472421 : Blo 311834 472421 := bbase (se 4 (by rfl) ⟨44289, by rfl⟩ : syracuseStep 472421 = 88579) (by norm_num)
theorem B472445 : Blo 311834 472445 := bbase (se 3 (by rfl) ⟨88583, by rfl⟩ : syracuseStep 472445 = 177167) (by norm_num)
theorem B701837 : Blo 311834 701837 := bbase (se 3 (by rfl) ⟨131594, by rfl⟩ : syracuseStep 701837 = 263189) (by norm_num)
theorem B472469 : Blo 311834 472469 := bbase (se 6 (by rfl) ⟨11073, by rfl⟩ : syracuseStep 472469 = 22147) (by norm_num)
theorem B472493 : Blo 311834 472493 := bbase (se 3 (by rfl) ⟨88592, by rfl⟩ : syracuseStep 472493 = 177185) (by norm_num)
theorem B1062341 : Blo 311834 1062341 := bbase (se 4 (by rfl) ⟨99594, by rfl⟩ : syracuseStep 1062341 = 199189) (by norm_num)
theorem B472517 : Blo 311834 472517 := bbase (se 4 (by rfl) ⟨44298, by rfl⟩ : syracuseStep 472517 = 88597) (by norm_num)
theorem B701909 : Blo 311834 701909 := bbase (se 7 (by rfl) ⟨8225, by rfl⟩ : syracuseStep 701909 = 16451) (by norm_num)
theorem B472541 : Blo 311834 472541 := bbase (se 3 (by rfl) ⟨88601, by rfl⟩ : syracuseStep 472541 = 177203) (by norm_num)
theorem B472565 : Blo 311834 472565 := bbase (se 5 (by rfl) ⟨22151, by rfl⟩ : syracuseStep 472565 = 44303) (by norm_num)
theorem B472589 : Blo 311834 472589 := bbase (se 3 (by rfl) ⟨88610, by rfl⟩ : syracuseStep 472589 = 177221) (by norm_num)
theorem B701981 : Blo 311834 701981 := bbase (se 3 (by rfl) ⟨131621, by rfl⟩ : syracuseStep 701981 = 263243) (by norm_num)
theorem B472613 : Blo 311834 472613 := bbase (se 4 (by rfl) ⟨44307, by rfl⟩ : syracuseStep 472613 = 88615) (by norm_num)
theorem B1193525 : Blo 311834 1193525 := bbase (se 5 (by rfl) ⟨55946, by rfl⟩ : syracuseStep 1193525 = 111893) (by norm_num)
theorem B472637 : Blo 311834 472637 := bbase (se 3 (by rfl) ⟨88619, by rfl⟩ : syracuseStep 472637 = 177239) (by norm_num)
theorem B472661 : Blo 311834 472661 := bbase (se 8 (by rfl) ⟨2769, by rfl⟩ : syracuseStep 472661 = 5539) (by norm_num)
theorem B702053 : Blo 311834 702053 := bbase (se 4 (by rfl) ⟨65817, by rfl⟩ : syracuseStep 702053 = 131635) (by norm_num)
theorem B1586789 : Blo 311834 1586789 := bbase (se 4 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 1586789 = 297523) (by norm_num)
theorem B472685 : Blo 311834 472685 := bbase (se 3 (by rfl) ⟨88628, by rfl⟩ : syracuseStep 472685 = 177257) (by norm_num)
theorem B472709 : Blo 311834 472709 := bbase (se 4 (by rfl) ⟨44316, by rfl⟩ : syracuseStep 472709 = 88633) (by norm_num)
theorem B669325 : Blo 311834 669325 := bbase (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) (by norm_num)
theorem B472733 : Blo 311834 472733 := bbase (se 3 (by rfl) ⟨88637, by rfl⟩ : syracuseStep 472733 = 177275) (by norm_num)
theorem B702125 : Blo 311834 702125 := bbase (se 3 (by rfl) ⟨131648, by rfl⟩ : syracuseStep 702125 = 263297) (by norm_num)
theorem B472757 : Blo 311834 472757 := bbase (se 5 (by rfl) ⟨22160, by rfl⟩ : syracuseStep 472757 = 44321) (by norm_num)
theorem B472781 : Blo 311834 472781 := bbase (se 3 (by rfl) ⟨88646, by rfl⟩ : syracuseStep 472781 = 177293) (by norm_num)
theorem B472805 : Blo 311834 472805 := bbase (se 4 (by rfl) ⟨44325, by rfl⟩ : syracuseStep 472805 = 88651) (by norm_num)
theorem B898789 : Blo 311834 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B702197 : Blo 311834 702197 := bbase (se 5 (by rfl) ⟨32915, by rfl⟩ : syracuseStep 702197 = 65831) (by norm_num)
theorem B472829 : Blo 311834 472829 := bbase (se 3 (by rfl) ⟨88655, by rfl⟩ : syracuseStep 472829 = 177311) (by norm_num)
theorem B472853 : Blo 311834 472853 := bbase (se 6 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 472853 = 22165) (by norm_num)
theorem B472877 : Blo 311834 472877 := bbase (se 3 (by rfl) ⟨88664, by rfl⟩ : syracuseStep 472877 = 177329) (by norm_num)
theorem B702269 : Blo 311834 702269 := bbase (se 3 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 702269 = 263351) (by norm_num)
theorem B472901 : Blo 311834 472901 := bbase (se 4 (by rfl) ⟨44334, by rfl⟩ : syracuseStep 472901 = 88669) (by norm_num)
theorem B505685 : Blo 311834 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B472925 : Blo 311834 472925 := bbase (se 3 (by rfl) ⟨88673, by rfl⟩ : syracuseStep 472925 = 177347) (by norm_num)
theorem B1062773 : Blo 311834 1062773 := bbase (se 5 (by rfl) ⟨49817, by rfl⟩ : syracuseStep 1062773 = 99635) (by norm_num)
theorem B472949 : Blo 311834 472949 := bbase (se 5 (by rfl) ⟨22169, by rfl⟩ : syracuseStep 472949 = 44339) (by norm_num)
theorem B702341 : Blo 311834 702341 := bbase (se 4 (by rfl) ⟨65844, by rfl⟩ : syracuseStep 702341 = 131689) (by norm_num)
theorem B538501 : Blo 311834 538501 := bbase (se 4 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 538501 = 100969) (by norm_num)
theorem B472973 : Blo 311834 472973 := bbase (se 3 (by rfl) ⟨88682, by rfl⟩ : syracuseStep 472973 = 177365) (by norm_num)
theorem B472997 : Blo 311834 472997 := bbase (se 4 (by rfl) ⟨44343, by rfl⟩ : syracuseStep 472997 = 88687) (by norm_num)
theorem B636853 : Blo 311834 636853 := bbase (se 5 (by rfl) ⟨29852, by rfl⟩ : syracuseStep 636853 = 59705) (by norm_num)
theorem B473021 : Blo 311834 473021 := bbase (se 3 (by rfl) ⟨88691, by rfl⟩ : syracuseStep 473021 = 177383) (by norm_num)
theorem B702413 : Blo 311834 702413 := bbase (se 3 (by rfl) ⟨131702, by rfl⟩ : syracuseStep 702413 = 263405) (by norm_num)
theorem B473045 : Blo 311834 473045 := bbase (se 7 (by rfl) ⟨5543, by rfl⟩ : syracuseStep 473045 = 11087) (by norm_num)
theorem B473069 : Blo 311834 473069 := bbase (se 3 (by rfl) ⟨88700, by rfl⟩ : syracuseStep 473069 = 177401) (by norm_num)
theorem B669701 : Blo 311834 669701 := bbase (se 4 (by rfl) ⟨62784, by rfl⟩ : syracuseStep 669701 = 125569) (by norm_num)
theorem B473093 : Blo 311834 473093 := bbase (se 4 (by rfl) ⟨44352, by rfl⟩ : syracuseStep 473093 = 88705) (by norm_num)
theorem B702485 : Blo 311834 702485 := bbase (se 6 (by rfl) ⟨16464, by rfl⟩ : syracuseStep 702485 = 32929) (by norm_num)
theorem B473117 : Blo 311834 473117 := bbase (se 3 (by rfl) ⟨88709, by rfl⟩ : syracuseStep 473117 = 177419) (by norm_num)
theorem B473141 : Blo 311834 473141 := bbase (se 5 (by rfl) ⟨22178, by rfl⟩ : syracuseStep 473141 = 44357) (by norm_num)
theorem B473165 : Blo 311834 473165 := bbase (se 3 (by rfl) ⟨88718, by rfl⟩ : syracuseStep 473165 = 177437) (by norm_num)
theorem B702557 : Blo 311834 702557 := bbase (se 3 (by rfl) ⟨131729, by rfl⟩ : syracuseStep 702557 = 263459) (by norm_num)
theorem B473189 : Blo 311834 473189 := bbase (se 4 (by rfl) ⟨44361, by rfl⟩ : syracuseStep 473189 = 88723) (by norm_num)
theorem B473213 : Blo 311834 473213 := bbase (se 3 (by rfl) ⟨88727, by rfl⟩ : syracuseStep 473213 = 177455) (by norm_num)
theorem B1620101 : Blo 311834 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B473237 : Blo 311834 473237 := bbase (se 6 (by rfl) ⟨11091, by rfl⟩ : syracuseStep 473237 = 22183) (by norm_num)
theorem B702629 : Blo 311834 702629 := bbase (se 4 (by rfl) ⟨65871, by rfl⟩ : syracuseStep 702629 = 131743) (by norm_num)
theorem B473261 : Blo 311834 473261 := bbase (se 3 (by rfl) ⟨88736, by rfl⟩ : syracuseStep 473261 = 177473) (by norm_num)
theorem B374977 : Blo 311834 374977 := bbase (se 2 (by rfl) ⟨140616, by rfl⟩ : syracuseStep 374977 = 281233) (by norm_num)
theorem B473285 : Blo 311834 473285 := bbase (se 4 (by rfl) ⟨44370, by rfl⟩ : syracuseStep 473285 = 88741) (by norm_num)
theorem B2865365 : Blo 311834 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B473309 : Blo 311834 473309 := bbase (se 3 (by rfl) ⟨88745, by rfl⟩ : syracuseStep 473309 = 177491) (by norm_num)
theorem B702701 : Blo 311834 702701 := bbase (se 3 (by rfl) ⟨131756, by rfl⟩ : syracuseStep 702701 = 263513) (by norm_num)
theorem B473333 : Blo 311834 473333 := bbase (se 5 (by rfl) ⟨22187, by rfl⟩ : syracuseStep 473333 = 44375) (by norm_num)
theorem B473357 : Blo 311834 473357 := bbase (se 3 (by rfl) ⟨88754, by rfl⟩ : syracuseStep 473357 = 177509) (by norm_num)
theorem B1128725 : Blo 311834 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B1063205 : Blo 311834 1063205 := bbase (se 4 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 1063205 = 199351) (by norm_num)
theorem B473381 : Blo 311834 473381 := bbase (se 4 (by rfl) ⟨44379, by rfl⟩ : syracuseStep 473381 = 88759) (by norm_num)
theorem B702773 : Blo 311834 702773 := bbase (se 5 (by rfl) ⟨32942, by rfl⟩ : syracuseStep 702773 = 65885) (by norm_num)
theorem B473405 : Blo 311834 473405 := bbase (se 3 (by rfl) ⟨88763, by rfl⟩ : syracuseStep 473405 = 177527) (by norm_num)
theorem B473429 : Blo 311834 473429 := bbase (se 10 (by rfl) ⟨693, by rfl⟩ : syracuseStep 473429 = 1387) (by norm_num)
theorem B473453 : Blo 311834 473453 := bbase (se 3 (by rfl) ⟨88772, by rfl⟩ : syracuseStep 473453 = 177545) (by norm_num)
theorem B702845 : Blo 311834 702845 := bbase (se 3 (by rfl) ⟨131783, by rfl⟩ : syracuseStep 702845 = 263567) (by norm_num)
theorem B473477 : Blo 311834 473477 := bbase (se 4 (by rfl) ⟨44388, by rfl⟩ : syracuseStep 473477 = 88777) (by norm_num)
theorem B473501 : Blo 311834 473501 := bbase (se 3 (by rfl) ⟨88781, by rfl⟩ : syracuseStep 473501 = 177563) (by norm_num)
theorem B473525 : Blo 311834 473525 := bbase (se 5 (by rfl) ⟨22196, by rfl⟩ : syracuseStep 473525 = 44393) (by norm_num)
theorem B702917 : Blo 311834 702917 := bbase (se 4 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 702917 = 131797) (by norm_num)
theorem B473549 : Blo 311834 473549 := bbase (se 3 (by rfl) ⟨88790, by rfl⟩ : syracuseStep 473549 = 177581) (by norm_num)
theorem B473573 : Blo 311834 473573 := bbase (se 4 (by rfl) ⟨44397, by rfl⟩ : syracuseStep 473573 = 88795) (by norm_num)
theorem B473597 : Blo 311834 473597 := bbase (se 3 (by rfl) ⟨88799, by rfl⟩ : syracuseStep 473597 = 177599) (by norm_num)
theorem B702989 : Blo 311834 702989 := bbase (se 3 (by rfl) ⟨131810, by rfl⟩ : syracuseStep 702989 = 263621) (by norm_num)
theorem B473621 : Blo 311834 473621 := bbase (se 6 (by rfl) ⟨11100, by rfl⟩ : syracuseStep 473621 = 22201) (by norm_num)
theorem B473645 : Blo 311834 473645 := bbase (se 3 (by rfl) ⟨88808, by rfl⟩ : syracuseStep 473645 = 177617) (by norm_num)
theorem B375361 : Blo 311834 375361 := bbase (se 2 (by rfl) ⟨140760, by rfl⟩ : syracuseStep 375361 = 281521) (by norm_num)
theorem B473669 : Blo 311834 473669 := bbase (se 4 (by rfl) ⟨44406, by rfl⟩ : syracuseStep 473669 = 88813) (by norm_num)
theorem B703061 : Blo 311834 703061 := bbase (se 8 (by rfl) ⟨4119, by rfl⟩ : syracuseStep 703061 = 8239) (by norm_num)
theorem B473693 : Blo 311834 473693 := bbase (se 3 (by rfl) ⟨88817, by rfl⟩ : syracuseStep 473693 = 177635) (by norm_num)
theorem B473717 : Blo 311834 473717 := bbase (se 5 (by rfl) ⟨22205, by rfl⟩ : syracuseStep 473717 = 44411) (by norm_num)
theorem B473741 : Blo 311834 473741 := bbase (se 3 (by rfl) ⟨88826, by rfl⟩ : syracuseStep 473741 = 177653) (by norm_num)
theorem B506525 : Blo 311834 506525 := bbase (se 3 (by rfl) ⟨94973, by rfl⟩ : syracuseStep 506525 = 189947) (by norm_num)
theorem B703133 : Blo 311834 703133 := bbase (se 3 (by rfl) ⟨131837, by rfl⟩ : syracuseStep 703133 = 263675) (by norm_num)
theorem B604829 : Blo 311834 604829 := bbase (se 3 (by rfl) ⟨113405, by rfl⟩ : syracuseStep 604829 = 226811) (by norm_num)
theorem B1784501 : Blo 311834 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B1194709 : Blo 311834 1194709 := bbase (se 7 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 1194709 = 28001) (by norm_num)
theorem B1063637 : Blo 311834 1063637 := bbase (se 7 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 1063637 = 24929) (by norm_num)
theorem B703205 : Blo 311834 703205 := bbase (se 4 (by rfl) ⟨65925, by rfl⟩ : syracuseStep 703205 = 131851) (by norm_num)
theorem B703277 : Blo 311834 703277 := bbase (se 3 (by rfl) ⟨131864, by rfl⟩ : syracuseStep 703277 = 263729) (by norm_num)
theorem B703349 : Blo 311834 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B1588085 : Blo 311834 1588085 := bbase (se 5 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 1588085 = 148883) (by norm_num)
theorem B703421 : Blo 311834 703421 := bbase (se 3 (by rfl) ⟨131891, by rfl⟩ : syracuseStep 703421 = 263783) (by norm_num)
theorem B703493 : Blo 311834 703493 := bbase (se 4 (by rfl) ⟨65952, by rfl⟩ : syracuseStep 703493 = 131905) (by norm_num)
theorem B1195013 : Blo 311834 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B703565 : Blo 311834 703565 := bbase (se 3 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 703565 = 263837) (by norm_num)
theorem B638045 : Blo 311834 638045 := bbase (se 3 (by rfl) ⟨119633, by rfl⟩ : syracuseStep 638045 = 239267) (by norm_num)
theorem B1064069 : Blo 311834 1064069 := bbase (se 4 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 1064069 = 199513) (by norm_num)
theorem B703637 : Blo 311834 703637 := bbase (se 6 (by rfl) ⟨16491, by rfl⟩ : syracuseStep 703637 = 32983) (by norm_num)
theorem B703709 : Blo 311834 703709 := bbase (se 3 (by rfl) ⟨131945, by rfl⟩ : syracuseStep 703709 = 263891) (by norm_num)
theorem B572653 : Blo 311834 572653 := bbase (se 3 (by rfl) ⟨107372, by rfl⟩ : syracuseStep 572653 = 214745) (by norm_num)
theorem B1129717 : Blo 311834 1129717 := bbase (se 5 (by rfl) ⟨52955, by rfl⟩ : syracuseStep 1129717 = 105911) (by norm_num)
theorem B703781 : Blo 311834 703781 := bbase (se 4 (by rfl) ⟨65979, by rfl⟩ : syracuseStep 703781 = 131959) (by norm_num)
theorem B703853 : Blo 311834 703853 := bbase (se 3 (by rfl) ⟨131972, by rfl⟩ : syracuseStep 703853 = 263945) (by norm_num)
theorem B703925 : Blo 311834 703925 := bbase (se 5 (by rfl) ⟨32996, by rfl⟩ : syracuseStep 703925 = 65993) (by norm_num)
theorem B376265 : Blo 311834 376265 := bbase (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) (by norm_num)
theorem B703997 : Blo 311834 703997 := bbase (se 3 (by rfl) ⟨131999, by rfl⟩ : syracuseStep 703997 = 263999) (by norm_num)
theorem B802333 : Blo 311834 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B1064501 : Blo 311834 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B704069 : Blo 311834 704069 := bbase (se 4 (by rfl) ⟨66006, by rfl⟩ : syracuseStep 704069 = 132013) (by norm_num)
theorem B671341 : Blo 311834 671341 := bbase (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) (by norm_num)
theorem B704141 : Blo 311834 704141 := bbase (se 3 (by rfl) ⟨132026, by rfl⟩ : syracuseStep 704141 = 264053) (by norm_num)
theorem B376525 : Blo 311834 376525 := bbase (se 3 (by rfl) ⟨70598, by rfl⟩ : syracuseStep 376525 = 141197) (by norm_num)
theorem B704213 : Blo 311834 704213 := bbase (se 7 (by rfl) ⟨8252, by rfl⟩ : syracuseStep 704213 = 16505) (by norm_num)
theorem B802541 : Blo 311834 802541 := bbase (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) (by norm_num)
theorem B704285 : Blo 311834 704285 := bbase (se 3 (by rfl) ⟨132053, by rfl⟩ : syracuseStep 704285 = 264107) (by norm_num)
theorem B1785685 : Blo 311834 1785685 := bbase (se 9 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 1785685 = 10463) (by norm_num)
theorem B704357 : Blo 311834 704357 := bbase (se 4 (by rfl) ⟨66033, by rfl⟩ : syracuseStep 704357 = 132067) (by norm_num)
theorem B376717 : Blo 311834 376717 := bbase (se 3 (by rfl) ⟨70634, by rfl⟩ : syracuseStep 376717 = 141269) (by norm_num)
theorem B376741 : Blo 311834 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B376745 : Blo 311834 376745 := bbase (se 2 (by rfl) ⟨141279, by rfl⟩ : syracuseStep 376745 = 282559) (by norm_num)
theorem B704429 : Blo 311834 704429 := bbase (se 3 (by rfl) ⟨132080, by rfl⟩ : syracuseStep 704429 = 264161) (by norm_num)
theorem B1064933 : Blo 311834 1064933 := bbase (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) (by norm_num)
theorem B704501 : Blo 311834 704501 := bbase (se 5 (by rfl) ⟨33023, by rfl⟩ : syracuseStep 704501 = 66047) (by norm_num)
theorem B704573 : Blo 311834 704573 := bbase (se 3 (by rfl) ⟨132107, by rfl⟩ : syracuseStep 704573 = 264215) (by norm_num)
theorem B704645 : Blo 311834 704645 := bbase (se 4 (by rfl) ⟨66060, by rfl⟩ : syracuseStep 704645 = 132121) (by norm_num)
theorem B1589381 : Blo 311834 1589381 := bbase (se 4 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 1589381 = 298009) (by norm_num)
theorem B704717 : Blo 311834 704717 := bbase (se 3 (by rfl) ⟨132134, by rfl⟩ : syracuseStep 704717 = 264269) (by norm_num)
theorem B704789 : Blo 311834 704789 := bbase (se 6 (by rfl) ⟨16518, by rfl⟩ : syracuseStep 704789 = 33037) (by norm_num)
theorem B704861 : Blo 311834 704861 := bbase (se 3 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 704861 = 264323) (by norm_num)
theorem B2376053 : Blo 311834 2376053 := bbase (se 5 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 2376053 = 222755) (by norm_num)
theorem B1065365 : Blo 311834 1065365 := bbase (se 6 (by rfl) ⟨24969, by rfl⟩ : syracuseStep 1065365 = 49939) (by norm_num)
theorem B377245 : Blo 311834 377245 := bbase (se 3 (by rfl) ⟨70733, by rfl⟩ : syracuseStep 377245 = 141467) (by norm_num)
theorem B704933 : Blo 311834 704933 := bbase (se 4 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 704933 = 132175) (by norm_num)
theorem B672229 : Blo 311834 672229 := bbase (se 4 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 672229 = 126043) (by norm_num)
theorem B705005 : Blo 311834 705005 := bbase (se 3 (by rfl) ⟨132188, by rfl⟩ : syracuseStep 705005 = 264377) (by norm_num)
theorem B377341 : Blo 311834 377341 := bbase (se 3 (by rfl) ⟨70751, by rfl⟩ : syracuseStep 377341 = 141503) (by norm_num)
theorem B705077 : Blo 311834 705077 := bbase (se 5 (by rfl) ⟨33050, by rfl⟩ : syracuseStep 705077 = 66101) (by norm_num)
theorem B705149 : Blo 311834 705149 := bbase (se 3 (by rfl) ⟨132215, by rfl⟩ : syracuseStep 705149 = 264431) (by norm_num)
theorem B1917589 : Blo 311834 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B705221 : Blo 311834 705221 := bbase (se 4 (by rfl) ⟨66114, by rfl⟩ : syracuseStep 705221 = 132229) (by norm_num)
theorem B705293 : Blo 311834 705293 := bbase (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) (by norm_num)
theorem B1065797 : Blo 311834 1065797 := bbase (se 4 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 1065797 = 199837) (by norm_num)
theorem B705365 : Blo 311834 705365 := bbase (se 9 (by rfl) ⟨2066, by rfl⟩ : syracuseStep 705365 = 4133) (by norm_num)
theorem B705437 : Blo 311834 705437 := bbase (se 3 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 705437 = 264539) (by norm_num)
theorem B672725 : Blo 311834 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B705509 : Blo 311834 705509 := bbase (se 4 (by rfl) ⟨66141, by rfl⟩ : syracuseStep 705509 = 132283) (by norm_num)
theorem B705581 : Blo 311834 705581 := bbase (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) (by norm_num)
theorem B1197125 : Blo 311834 1197125 := bbase (se 4 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 1197125 = 224461) (by norm_num)
theorem B705653 : Blo 311834 705653 := bbase (se 5 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 705653 = 66155) (by norm_num)
theorem B705725 : Blo 311834 705725 := bbase (se 3 (by rfl) ⟨132323, by rfl⟩ : syracuseStep 705725 = 264647) (by norm_num)
theorem B705797 : Blo 311834 705797 := bbase (se 4 (by rfl) ⟨66168, by rfl⟩ : syracuseStep 705797 = 132337) (by norm_num)
theorem B345385 : Blo 311834 345385 := bbase (se 2 (by rfl) ⟨129519, by rfl⟩ : syracuseStep 345385 = 259039) (by norm_num)
theorem B705869 : Blo 311834 705869 := bbase (se 3 (by rfl) ⟨132350, by rfl⟩ : syracuseStep 705869 = 264701) (by norm_num)
theorem B1197413 : Blo 311834 1197413 := bbase (se 4 (by rfl) ⟨112257, by rfl⟩ : syracuseStep 1197413 = 224515) (by norm_num)
theorem B705941 : Blo 311834 705941 := bbase (se 6 (by rfl) ⟨16545, by rfl⟩ : syracuseStep 705941 = 33091) (by norm_num)
theorem B1590677 : Blo 311834 1590677 := bbase (se 6 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 1590677 = 74563) (by norm_num)
theorem B378317 : Blo 311834 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B706013 : Blo 311834 706013 := bbase (se 3 (by rfl) ⟨132377, by rfl⟩ : syracuseStep 706013 = 264755) (by norm_num)
theorem B706085 : Blo 311834 706085 := bbase (se 4 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 706085 = 132391) (by norm_num)
theorem B1132069 : Blo 311834 1132069 := bbase (se 4 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 1132069 = 212263) (by norm_num)
theorem B706157 : Blo 311834 706157 := bbase (se 3 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 706157 = 264809) (by norm_num)
theorem B706229 : Blo 311834 706229 := bbase (se 5 (by rfl) ⟨33104, by rfl⟩ : syracuseStep 706229 = 66209) (by norm_num)
theorem B706301 : Blo 311834 706301 := bbase (se 3 (by rfl) ⟨132431, by rfl⟩ : syracuseStep 706301 = 264863) (by norm_num)
theorem B1787669 : Blo 311834 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B673589 : Blo 311834 673589 := bbase (se 5 (by rfl) ⟨31574, by rfl⟩ : syracuseStep 673589 = 63149) (by norm_num)
theorem B706373 : Blo 311834 706373 := bbase (se 4 (by rfl) ⟨66222, by rfl⟩ : syracuseStep 706373 = 132445) (by norm_num)
theorem B706445 : Blo 311834 706445 := bbase (se 3 (by rfl) ⟨132458, by rfl⟩ : syracuseStep 706445 = 264917) (by norm_num)
theorem B378793 : Blo 311834 378793 := bbase (se 2 (by rfl) ⟨142047, by rfl⟩ : syracuseStep 378793 = 284095) (by norm_num)
theorem B378821 : Blo 311834 378821 := bbase (se 4 (by rfl) ⟨35514, by rfl⟩ : syracuseStep 378821 = 71029) (by norm_num)
theorem B673733 : Blo 311834 673733 := bbase (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) (by norm_num)
theorem B706517 : Blo 311834 706517 := bbase (se 7 (by rfl) ⟨8279, by rfl⟩ : syracuseStep 706517 = 16559) (by norm_num)
theorem B575453 : Blo 311834 575453 := bbase (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) (by norm_num)
theorem B477173 : Blo 311834 477173 := bbase (se 5 (by rfl) ⟨22367, by rfl⟩ : syracuseStep 477173 = 44735) (by norm_num)
theorem B706589 : Blo 311834 706589 := bbase (se 3 (by rfl) ⟨132485, by rfl⟩ : syracuseStep 706589 = 264971) (by norm_num)
theorem B444485 : Blo 311834 444485 := bbase (se 4 (by rfl) ⟨41670, by rfl⟩ : syracuseStep 444485 = 83341) (by norm_num)
theorem B12863573 : Blo 311834 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B706661 : Blo 311834 706661 := bbase (se 4 (by rfl) ⟨66249, by rfl⟩ : syracuseStep 706661 = 132499) (by norm_num)
theorem B379009 : Blo 311834 379009 := bbase (se 2 (by rfl) ⟨142128, by rfl⟩ : syracuseStep 379009 = 284257) (by norm_num)
theorem B1001605 : Blo 311834 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B444565 : Blo 311834 444565 := bbase (se 6 (by rfl) ⟨10419, by rfl⟩ : syracuseStep 444565 = 20839) (by norm_num)
theorem B706733 : Blo 311834 706733 := bbase (se 3 (by rfl) ⟨132512, by rfl⟩ : syracuseStep 706733 = 265025) (by norm_num)
theorem B706805 : Blo 311834 706805 := bbase (se 5 (by rfl) ⟨33131, by rfl⟩ : syracuseStep 706805 = 66263) (by norm_num)
theorem B379129 : Blo 311834 379129 := bbase (se 2 (by rfl) ⟨142173, by rfl⟩ : syracuseStep 379129 = 284347) (by norm_num)
theorem B444685 : Blo 311834 444685 := bbase (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) (by norm_num)
theorem B706877 : Blo 311834 706877 := bbase (se 3 (by rfl) ⟨132539, by rfl⟩ : syracuseStep 706877 = 265079) (by norm_num)
theorem B444781 : Blo 311834 444781 := bbase (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) (by norm_num)
theorem B706949 : Blo 311834 706949 := bbase (se 4 (by rfl) ⟨66276, by rfl⟩ : syracuseStep 706949 = 132553) (by norm_num)
theorem B707021 : Blo 311834 707021 := bbase (se 3 (by rfl) ⟨132566, by rfl⟩ : syracuseStep 707021 = 265133) (by norm_num)
theorem B1198597 : Blo 311834 1198597 := bbase (se 4 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 1198597 = 224737) (by norm_num)
theorem B707093 : Blo 311834 707093 := bbase (se 6 (by rfl) ⟨16572, by rfl⟩ : syracuseStep 707093 = 33145) (by norm_num)
theorem B707165 : Blo 311834 707165 := bbase (se 3 (by rfl) ⟨132593, by rfl⟩ : syracuseStep 707165 = 265187) (by norm_num)
theorem B707237 : Blo 311834 707237 := bbase (se 4 (by rfl) ⟨66303, by rfl⟩ : syracuseStep 707237 = 132607) (by norm_num)
theorem B1591973 : Blo 311834 1591973 := bbase (se 4 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 1591973 = 298495) (by norm_num)
theorem B674477 : Blo 311834 674477 := bbase (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) (by norm_num)
theorem B707309 : Blo 311834 707309 := bbase (se 3 (by rfl) ⟨132620, by rfl⟩ : syracuseStep 707309 = 265241) (by norm_num)
theorem B969509 : Blo 311834 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B707381 : Blo 311834 707381 := bbase (se 5 (by rfl) ⟨33158, by rfl⟩ : syracuseStep 707381 = 66317) (by norm_num)
theorem B1198901 : Blo 311834 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B445277 : Blo 311834 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B707453 : Blo 311834 707453 := bbase (se 3 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 707453 = 265295) (by norm_num)
theorem B707525 : Blo 311834 707525 := bbase (se 4 (by rfl) ⟨66330, by rfl⟩ : syracuseStep 707525 = 132661) (by norm_num)
theorem B8604629 : Blo 311834 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B707597 : Blo 311834 707597 := bbase (se 3 (by rfl) ⟨132674, by rfl⟩ : syracuseStep 707597 = 265349) (by norm_num)
theorem B1035301 : Blo 311834 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B707669 : Blo 311834 707669 := bbase (se 8 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 707669 = 8293) (by norm_num)
theorem B707741 : Blo 311834 707741 := bbase (se 3 (by rfl) ⟨132701, by rfl⟩ : syracuseStep 707741 = 265403) (by norm_num)
theorem B707813 : Blo 311834 707813 := bbase (se 4 (by rfl) ⟨66357, by rfl⟩ : syracuseStep 707813 = 132715) (by norm_num)
theorem B707885 : Blo 311834 707885 := bbase (se 3 (by rfl) ⟨132728, by rfl⟩ : syracuseStep 707885 = 265457) (by norm_num)
theorem B2149685 : Blo 311834 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B707957 : Blo 311834 707957 := bbase (se 5 (by rfl) ⟨33185, by rfl⟩ : syracuseStep 707957 = 66371) (by norm_num)
theorem B445829 : Blo 311834 445829 := bbase (se 4 (by rfl) ⟨41796, by rfl⟩ : syracuseStep 445829 = 83593) (by norm_num)
theorem B708029 : Blo 311834 708029 := bbase (se 3 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 708029 = 265511) (by norm_num)
theorem B806381 : Blo 311834 806381 := bbase (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) (by norm_num)
theorem B708101 : Blo 311834 708101 := bbase (se 4 (by rfl) ⟨66384, by rfl⟩ : syracuseStep 708101 = 132769) (by norm_num)
theorem B1134101 : Blo 311834 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B708173 : Blo 311834 708173 := bbase (se 3 (by rfl) ⟨132782, by rfl⟩ : syracuseStep 708173 = 265565) (by norm_num)
theorem B9064021 : Blo 311834 9064021 := bbase (se 8 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 9064021 = 106219) (by norm_num)
theorem B708245 : Blo 311834 708245 := bbase (se 6 (by rfl) ⟨16599, by rfl⟩ : syracuseStep 708245 = 33199) (by norm_num)
theorem B708317 : Blo 311834 708317 := bbase (se 3 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 708317 = 265619) (by norm_num)
theorem B1068821 : Blo 311834 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B708389 : Blo 311834 708389 := bbase (se 4 (by rfl) ⟨66411, by rfl⟩ : syracuseStep 708389 = 132823) (by norm_num)
theorem B708461 : Blo 311834 708461 := bbase (se 3 (by rfl) ⟨132836, by rfl⟩ : syracuseStep 708461 = 265673) (by norm_num)
theorem B1789877 : Blo 311834 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B1593269 : Blo 311834 1593269 := bbase (se 5 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 1593269 = 149369) (by norm_num)
theorem B708533 : Blo 311834 708533 := bbase (se 5 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 708533 = 66425) (by norm_num)
theorem B806869 : Blo 311834 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B479197 : Blo 311834 479197 := bbase (se 3 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 479197 = 179699) (by norm_num)
theorem B708605 : Blo 311834 708605 := bbase (se 3 (by rfl) ⟨132863, by rfl⟩ : syracuseStep 708605 = 265727) (by norm_num)
theorem B708677 : Blo 311834 708677 := bbase (se 4 (by rfl) ⟨66438, by rfl⟩ : syracuseStep 708677 = 132877) (by norm_num)
theorem B446581 : Blo 311834 446581 := bbase (se 5 (by rfl) ⟨20933, by rfl⟩ : syracuseStep 446581 = 41867) (by norm_num)
theorem B708749 : Blo 311834 708749 := bbase (se 3 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 708749 = 265781) (by norm_num)
theorem B708821 : Blo 311834 708821 := bbase (se 7 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 708821 = 16613) (by norm_num)
theorem B708893 : Blo 311834 708893 := bbase (se 3 (by rfl) ⟨132917, by rfl⟩ : syracuseStep 708893 = 265835) (by norm_num)
theorem B708965 : Blo 311834 708965 := bbase (se 4 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 708965 = 132931) (by norm_num)
theorem B1134965 : Blo 311834 1134965 := bbase (se 5 (by rfl) ⟨53201, by rfl⟩ : syracuseStep 1134965 = 106403) (by norm_num)
theorem B709037 : Blo 311834 709037 := bbase (se 3 (by rfl) ⟨132944, by rfl⟩ : syracuseStep 709037 = 265889) (by norm_num)
theorem B709109 : Blo 311834 709109 := bbase (se 5 (by rfl) ⟨33239, by rfl⟩ : syracuseStep 709109 = 66479) (by norm_num)
theorem B709181 : Blo 311834 709181 := bbase (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) (by norm_num)
theorem B479861 : Blo 311834 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B709253 : Blo 311834 709253 := bbase (se 4 (by rfl) ⟨66492, by rfl⟩ : syracuseStep 709253 = 132985) (by norm_num)
theorem B479933 : Blo 311834 479933 := bbase (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) (by norm_num)
theorem B709325 : Blo 311834 709325 := bbase (se 3 (by rfl) ⟨132998, by rfl⟩ : syracuseStep 709325 = 265997) (by norm_num)
theorem B709397 : Blo 311834 709397 := bbase (se 6 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 709397 = 33253) (by norm_num)
theorem B316225 : Blo 311834 316225 := bbase (se 2 (by rfl) ⟨118584, by rfl⟩ : syracuseStep 316225 = 237169) (by norm_num)
theorem B709469 : Blo 311834 709469 := bbase (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) (by norm_num)
theorem B447373 : Blo 311834 447373 := bbase (se 3 (by rfl) ⟨83882, by rfl⟩ : syracuseStep 447373 = 167765) (by norm_num)
theorem B971669 : Blo 311834 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B709541 : Blo 311834 709541 := bbase (se 4 (by rfl) ⟨66519, by rfl⟩ : syracuseStep 709541 = 133039) (by norm_num)
theorem B1135541 : Blo 311834 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B1004501 : Blo 311834 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B709613 : Blo 311834 709613 := bbase (se 3 (by rfl) ⟨133052, by rfl⟩ : syracuseStep 709613 = 266105) (by norm_num)
theorem B709685 : Blo 311834 709685 := bbase (se 5 (by rfl) ⟨33266, by rfl⟩ : syracuseStep 709685 = 66533) (by norm_num)
theorem B709757 : Blo 311834 709757 := bbase (se 3 (by rfl) ⟨133079, by rfl⟩ : syracuseStep 709757 = 266159) (by norm_num)
theorem B1594565 : Blo 311834 1594565 := bbase (se 4 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 1594565 = 298981) (by norm_num)
theorem B709829 : Blo 311834 709829 := bbase (se 4 (by rfl) ⟨66546, by rfl⟩ : syracuseStep 709829 = 133093) (by norm_num)
theorem B447709 : Blo 311834 447709 := bbase (se 3 (by rfl) ⟨83945, by rfl⟩ : syracuseStep 447709 = 167891) (by norm_num)
theorem B709901 : Blo 311834 709901 := bbase (se 3 (by rfl) ⟨133106, by rfl⟩ : syracuseStep 709901 = 266213) (by norm_num)
theorem B709973 : Blo 311834 709973 := bbase (se 15 (by rfl) ⟨32, by rfl⟩ : syracuseStep 709973 = 65) (by norm_num)
theorem B513389 : Blo 311834 513389 := bbase (se 3 (by rfl) ⟨96260, by rfl⟩ : syracuseStep 513389 = 192521) (by norm_num)
theorem B710045 : Blo 311834 710045 := bbase (se 3 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 710045 = 266267) (by norm_num)
theorem B447925 : Blo 311834 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B710117 : Blo 311834 710117 := bbase (se 4 (by rfl) ⟨66573, by rfl⟩ : syracuseStep 710117 = 133147) (by norm_num)
theorem B1332773 : Blo 311834 1332773 := bbase (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) (by norm_num)
theorem B710189 : Blo 311834 710189 := bbase (se 3 (by rfl) ⟨133160, by rfl⟩ : syracuseStep 710189 = 266321) (by norm_num)
theorem B3200629 : Blo 311834 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B2676341 : Blo 311834 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B710261 : Blo 311834 710261 := bbase (se 5 (by rfl) ⟨33293, by rfl⟩ : syracuseStep 710261 = 66587) (by norm_num)
theorem B710333 : Blo 311834 710333 := bbase (se 3 (by rfl) ⟨133187, by rfl⟩ : syracuseStep 710333 = 266375) (by norm_num)
theorem B710405 : Blo 311834 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B448301 : Blo 311834 448301 := bbase (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) (by norm_num)
theorem B710477 : Blo 311834 710477 := bbase (se 3 (by rfl) ⟨133214, by rfl⟩ : syracuseStep 710477 = 266429) (by norm_num)
theorem B710549 : Blo 311834 710549 := bbase (se 6 (by rfl) ⟨16653, by rfl⟩ : syracuseStep 710549 = 33307) (by norm_num)
theorem B710621 : Blo 311834 710621 := bbase (se 3 (by rfl) ⟨133241, by rfl⟩ : syracuseStep 710621 = 266483) (by norm_num)
theorem B317725 : Blo 311834 317725 := bbase (se 3 (by rfl) ⟨59573, by rfl⟩ : syracuseStep 317725 = 119147) (by norm_num)
theorem B1595861 : Blo 311834 1595861 := bbase (se 7 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 1595861 = 37403) (by norm_num)
theorem B350833 : Blo 311834 350833 := bbase (se 2 (by rfl) ⟨131562, by rfl⟩ : syracuseStep 350833 = 263125) (by norm_num)
theorem B350869 : Blo 311834 350869 := bbase (se 6 (by rfl) ⟨8223, by rfl⟩ : syracuseStep 350869 = 16447) (by norm_num)
theorem B350905 : Blo 311834 350905 := bbase (se 2 (by rfl) ⟨131589, by rfl⟩ : syracuseStep 350905 = 263179) (by norm_num)
theorem B350941 : Blo 311834 350941 := bbase (se 3 (by rfl) ⟨65801, by rfl⟩ : syracuseStep 350941 = 131603) (by norm_num)
theorem B350977 : Blo 311834 350977 := bbase (se 2 (by rfl) ⟨131616, by rfl⟩ : syracuseStep 350977 = 263233) (by norm_num)
theorem B351013 : Blo 311834 351013 := bbase (se 4 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 351013 = 65815) (by norm_num)
theorem B908101 : Blo 311834 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B351049 : Blo 311834 351049 := bbase (se 2 (by rfl) ⟨131643, by rfl⟩ : syracuseStep 351049 = 263287) (by norm_num)
theorem B351085 : Blo 311834 351085 := bbase (se 3 (by rfl) ⟨65828, by rfl⟩ : syracuseStep 351085 = 131657) (by norm_num)
theorem B1268597 : Blo 311834 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B351121 : Blo 311834 351121 := bbase (se 2 (by rfl) ⟨131670, by rfl⟩ : syracuseStep 351121 = 263341) (by norm_num)
theorem B351157 : Blo 311834 351157 := bbase (se 5 (by rfl) ⟨16460, by rfl⟩ : syracuseStep 351157 = 32921) (by norm_num)
theorem B351193 : Blo 311834 351193 := bbase (se 2 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 351193 = 263395) (by norm_num)
theorem B351229 : Blo 311834 351229 := bbase (se 3 (by rfl) ⟨65855, by rfl⟩ : syracuseStep 351229 = 131711) (by norm_num)
theorem B351265 : Blo 311834 351265 := bbase (se 2 (by rfl) ⟨131724, by rfl⟩ : syracuseStep 351265 = 263449) (by norm_num)
theorem B351301 : Blo 311834 351301 := bbase (se 4 (by rfl) ⟨32934, by rfl⟩ : syracuseStep 351301 = 65869) (by norm_num)
theorem B351337 : Blo 311834 351337 := bbase (se 2 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 351337 = 263503) (by norm_num)
theorem B351373 : Blo 311834 351373 := bbase (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) (by norm_num)
theorem B351409 : Blo 311834 351409 := bbase (se 2 (by rfl) ⟨131778, by rfl⟩ : syracuseStep 351409 = 263557) (by norm_num)
theorem B351445 : Blo 311834 351445 := bbase (se 7 (by rfl) ⟨4118, by rfl⟩ : syracuseStep 351445 = 8237) (by norm_num)
theorem B351481 : Blo 311834 351481 := bbase (se 2 (by rfl) ⟨131805, by rfl⟩ : syracuseStep 351481 = 263611) (by norm_num)
theorem B1334549 : Blo 311834 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B351517 : Blo 311834 351517 := bbase (se 3 (by rfl) ⟨65909, by rfl⟩ : syracuseStep 351517 = 131819) (by norm_num)
theorem B351553 : Blo 311834 351553 := bbase (se 2 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 351553 = 263665) (by norm_num)
theorem B15621461 : Blo 311834 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B351589 : Blo 311834 351589 := bbase (se 4 (by rfl) ⟨32961, by rfl⟩ : syracuseStep 351589 = 65923) (by norm_num)
theorem B351625 : Blo 311834 351625 := bbase (se 2 (by rfl) ⟨131859, by rfl⟩ : syracuseStep 351625 = 263719) (by norm_num)
theorem B351661 : Blo 311834 351661 := bbase (se 3 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 351661 = 131873) (by norm_num)
theorem B351697 : Blo 311834 351697 := bbase (se 2 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 351697 = 263773) (by norm_num)
theorem B351733 : Blo 311834 351733 := bbase (se 5 (by rfl) ⟨16487, by rfl⟩ : syracuseStep 351733 = 32975) (by norm_num)
theorem B1334789 : Blo 311834 1334789 := bbase (se 4 (by rfl) ⟨125136, by rfl⟩ : syracuseStep 1334789 = 250273) (by norm_num)
theorem B351769 : Blo 311834 351769 := bbase (se 2 (by rfl) ⟨131913, by rfl⟩ : syracuseStep 351769 = 263827) (by norm_num)
theorem B351805 : Blo 311834 351805 := bbase (se 3 (by rfl) ⟨65963, by rfl⟩ : syracuseStep 351805 = 131927) (by norm_num)
theorem B351841 : Blo 311834 351841 := bbase (se 2 (by rfl) ⟨131940, by rfl⟩ : syracuseStep 351841 = 263881) (by norm_num)
theorem B351877 : Blo 311834 351877 := bbase (se 4 (by rfl) ⟨32988, by rfl⟩ : syracuseStep 351877 = 65977) (by norm_num)
theorem B3399317 : Blo 311834 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B5758613 : Blo 311834 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B351913 : Blo 311834 351913 := bbase (se 2 (by rfl) ⟨131967, by rfl⟩ : syracuseStep 351913 = 263935) (by norm_num)
theorem B843461 : Blo 311834 843461 := bbase (se 4 (by rfl) ⟨79074, by rfl⟩ : syracuseStep 843461 = 158149) (by norm_num)
theorem B351949 : Blo 311834 351949 := bbase (se 3 (by rfl) ⟨65990, by rfl⟩ : syracuseStep 351949 = 131981) (by norm_num)
theorem B1597157 : Blo 311834 1597157 := bbase (se 4 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 1597157 = 299467) (by norm_num)
theorem B351985 : Blo 311834 351985 := bbase (se 2 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 351985 = 263989) (by norm_num)
theorem B352021 : Blo 311834 352021 := bbase (se 6 (by rfl) ⟨8250, by rfl⟩ : syracuseStep 352021 = 16501) (by norm_num)
theorem B352057 : Blo 311834 352057 := bbase (se 2 (by rfl) ⟨132021, by rfl⟩ : syracuseStep 352057 = 264043) (by norm_num)
theorem B352093 : Blo 311834 352093 := bbase (se 3 (by rfl) ⟨66017, by rfl⟩ : syracuseStep 352093 = 132035) (by norm_num)
theorem B352129 : Blo 311834 352129 := bbase (se 2 (by rfl) ⟨132048, by rfl⟩ : syracuseStep 352129 = 264097) (by norm_num)
theorem B352165 : Blo 311834 352165 := bbase (se 4 (by rfl) ⟨33015, by rfl⟩ : syracuseStep 352165 = 66031) (by norm_num)
theorem B352201 : Blo 311834 352201 := bbase (se 2 (by rfl) ⟨132075, by rfl⟩ : syracuseStep 352201 = 264151) (by norm_num)
theorem B2383829 : Blo 311834 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B352237 : Blo 311834 352237 := bbase (se 3 (by rfl) ⟨66044, by rfl⟩ : syracuseStep 352237 = 132089) (by norm_num)
theorem B319469 : Blo 311834 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B352273 : Blo 311834 352273 := bbase (se 2 (by rfl) ⟨132102, by rfl⟩ : syracuseStep 352273 = 264205) (by norm_num)
theorem B1007653 : Blo 311834 1007653 := bbase (se 4 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 1007653 = 188935) (by norm_num)
theorem B352309 : Blo 311834 352309 := bbase (se 5 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 352309 = 33029) (by norm_num)
theorem B352345 : Blo 311834 352345 := bbase (se 2 (by rfl) ⟨132129, by rfl⟩ : syracuseStep 352345 = 264259) (by norm_num)
theorem B352381 : Blo 311834 352381 := bbase (se 3 (by rfl) ⟨66071, by rfl⟩ : syracuseStep 352381 = 132143) (by norm_num)
theorem B352417 : Blo 311834 352417 := bbase (se 2 (by rfl) ⟨132156, by rfl⟩ : syracuseStep 352417 = 264313) (by norm_num)
theorem B352453 : Blo 311834 352453 := bbase (se 4 (by rfl) ⟨33042, by rfl⟩ : syracuseStep 352453 = 66085) (by norm_num)
theorem B352489 : Blo 311834 352489 := bbase (se 2 (by rfl) ⟨132183, by rfl⟩ : syracuseStep 352489 = 264367) (by norm_num)
theorem B352525 : Blo 311834 352525 := bbase (se 3 (by rfl) ⟨66098, by rfl⟩ : syracuseStep 352525 = 132197) (by norm_num)
theorem B5726485 : Blo 311834 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B352561 : Blo 311834 352561 := bbase (se 2 (by rfl) ⟨132210, by rfl⟩ : syracuseStep 352561 = 264421) (by norm_num)
theorem B352597 : Blo 311834 352597 := bbase (se 10 (by rfl) ⟨516, by rfl⟩ : syracuseStep 352597 = 1033) (by norm_num)
theorem B680293 : Blo 311834 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B352633 : Blo 311834 352633 := bbase (se 2 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 352633 = 264475) (by norm_num)
theorem B352669 : Blo 311834 352669 := bbase (se 3 (by rfl) ⟨66125, by rfl⟩ : syracuseStep 352669 = 132251) (by norm_num)
theorem B352705 : Blo 311834 352705 := bbase (se 2 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 352705 = 264529) (by norm_num)
theorem B352741 : Blo 311834 352741 := bbase (se 4 (by rfl) ⟨33069, by rfl⟩ : syracuseStep 352741 = 66139) (by norm_num)
theorem B352777 : Blo 311834 352777 := bbase (se 2 (by rfl) ⟨132291, by rfl⟩ : syracuseStep 352777 = 264583) (by norm_num)
theorem B2679317 : Blo 311834 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B352813 : Blo 311834 352813 := bbase (se 3 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 352813 = 132305) (by norm_num)
theorem B352849 : Blo 311834 352849 := bbase (se 2 (by rfl) ⟨132318, by rfl⟩ : syracuseStep 352849 = 264637) (by norm_num)
theorem B3596885 : Blo 311834 3596885 := bbase (se 8 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 3596885 = 42151) (by norm_num)
theorem B352885 : Blo 311834 352885 := bbase (se 5 (by rfl) ⟨16541, by rfl⟩ : syracuseStep 352885 = 33083) (by norm_num)
theorem B1532533 : Blo 311834 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B320117 : Blo 311834 320117 := bbase (se 5 (by rfl) ⟨15005, by rfl⟩ : syracuseStep 320117 = 30011) (by norm_num)
theorem B352921 : Blo 311834 352921 := bbase (se 2 (by rfl) ⟨132345, by rfl⟩ : syracuseStep 352921 = 264691) (by norm_num)
theorem B352957 : Blo 311834 352957 := bbase (se 3 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 352957 = 132359) (by norm_num)
theorem B352993 : Blo 311834 352993 := bbase (se 2 (by rfl) ⟨132372, by rfl⟩ : syracuseStep 352993 = 264745) (by norm_num)
theorem B353029 : Blo 311834 353029 := bbase (se 4 (by rfl) ⟨33096, by rfl⟩ : syracuseStep 353029 = 66193) (by norm_num)
theorem B353065 : Blo 311834 353065 := bbase (se 2 (by rfl) ⟨132399, by rfl⟩ : syracuseStep 353065 = 264799) (by norm_num)
theorem B1696565 : Blo 311834 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B353101 : Blo 311834 353101 := bbase (se 3 (by rfl) ⟨66206, by rfl⟩ : syracuseStep 353101 = 132413) (by norm_num)
theorem B353137 : Blo 311834 353137 := bbase (se 2 (by rfl) ⟨132426, by rfl⟩ : syracuseStep 353137 = 264853) (by norm_num)
theorem B353173 : Blo 311834 353173 := bbase (se 6 (by rfl) ⟨8277, by rfl⟩ : syracuseStep 353173 = 16555) (by norm_num)
theorem B353209 : Blo 311834 353209 := bbase (se 2 (by rfl) ⟨132453, by rfl⟩ : syracuseStep 353209 = 264907) (by norm_num)
theorem B3793877 : Blo 311834 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B353245 : Blo 311834 353245 := bbase (se 3 (by rfl) ⟨66233, by rfl⟩ : syracuseStep 353245 = 132467) (by norm_num)
theorem B1598453 : Blo 311834 1598453 := bbase (se 5 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 1598453 = 149855) (by norm_num)
theorem B353281 : Blo 311834 353281 := bbase (se 2 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 353281 = 264961) (by norm_num)
theorem B353317 : Blo 311834 353317 := bbase (se 4 (by rfl) ⟨33123, by rfl⟩ : syracuseStep 353317 = 66247) (by norm_num)
theorem B1270853 : Blo 311834 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B353353 : Blo 311834 353353 := bbase (se 2 (by rfl) ⟨132507, by rfl⟩ : syracuseStep 353353 = 265015) (by norm_num)
theorem B844901 : Blo 311834 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B353389 : Blo 311834 353389 := bbase (se 3 (by rfl) ⟨66260, by rfl⟩ : syracuseStep 353389 = 132521) (by norm_num)
theorem B353425 : Blo 311834 353425 := bbase (se 2 (by rfl) ⟨132534, by rfl⟩ : syracuseStep 353425 = 265069) (by norm_num)
theorem B353461 : Blo 311834 353461 := bbase (se 5 (by rfl) ⟨16568, by rfl⟩ : syracuseStep 353461 = 33137) (by norm_num)
theorem B1270997 : Blo 311834 1270997 := bbase (se 7 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 1270997 = 29789) (by norm_num)
theorem B353497 : Blo 311834 353497 := bbase (se 2 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 353497 = 265123) (by norm_num)
theorem B353533 : Blo 311834 353533 := bbase (se 3 (by rfl) ⟨66287, by rfl⟩ : syracuseStep 353533 = 132575) (by norm_num)
theorem B353569 : Blo 311834 353569 := bbase (se 2 (by rfl) ⟨132588, by rfl⟩ : syracuseStep 353569 = 265177) (by norm_num)
theorem B353605 : Blo 311834 353605 := bbase (se 4 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 353605 = 66301) (by norm_num)
theorem B353641 : Blo 311834 353641 := bbase (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) (by norm_num)
theorem B353677 : Blo 311834 353677 := bbase (se 3 (by rfl) ⟨66314, by rfl⟩ : syracuseStep 353677 = 132629) (by norm_num)
theorem B353713 : Blo 311834 353713 := bbase (se 2 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 353713 = 265285) (by norm_num)
theorem B353749 : Blo 311834 353749 := bbase (se 7 (by rfl) ⟨4145, by rfl⟩ : syracuseStep 353749 = 8291) (by norm_num)
theorem B353785 : Blo 311834 353785 := bbase (se 2 (by rfl) ⟨132669, by rfl⟩ : syracuseStep 353785 = 265339) (by norm_num)
theorem B1500677 : Blo 311834 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B353821 : Blo 311834 353821 := bbase (se 3 (by rfl) ⟨66341, by rfl⟩ : syracuseStep 353821 = 132683) (by norm_num)
theorem B353857 : Blo 311834 353857 := bbase (se 2 (by rfl) ⟨132696, by rfl⟩ : syracuseStep 353857 = 265393) (by norm_num)
theorem B353893 : Blo 311834 353893 := bbase (se 4 (by rfl) ⟨33177, by rfl⟩ : syracuseStep 353893 = 66355) (by norm_num)
theorem B3008117 : Blo 311834 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B353929 : Blo 311834 353929 := bbase (se 2 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 353929 = 265447) (by norm_num)
theorem B1697429 : Blo 311834 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B353965 : Blo 311834 353965 := bbase (se 3 (by rfl) ⟨66368, by rfl⟩ : syracuseStep 353965 = 132737) (by norm_num)
theorem B354001 : Blo 311834 354001 := bbase (se 2 (by rfl) ⟨132750, by rfl⟩ : syracuseStep 354001 = 265501) (by norm_num)
theorem B1337077 : Blo 311834 1337077 := bbase (se 5 (by rfl) ⟨62675, by rfl⟩ : syracuseStep 1337077 = 125351) (by norm_num)
theorem B354037 : Blo 311834 354037 := bbase (se 5 (by rfl) ⟨16595, by rfl⟩ : syracuseStep 354037 = 33191) (by norm_num)
theorem B354073 : Blo 311834 354073 := bbase (se 2 (by rfl) ⟨132777, by rfl⟩ : syracuseStep 354073 = 265555) (by norm_num)
theorem B354109 : Blo 311834 354109 := bbase (se 3 (by rfl) ⟨66395, by rfl⟩ : syracuseStep 354109 = 132791) (by norm_num)
theorem B354145 : Blo 311834 354145 := bbase (se 2 (by rfl) ⟨132804, by rfl⟩ : syracuseStep 354145 = 265609) (by norm_num)
theorem B354181 : Blo 311834 354181 := bbase (se 4 (by rfl) ⟨33204, by rfl⟩ : syracuseStep 354181 = 66409) (by norm_num)
theorem B354217 : Blo 311834 354217 := bbase (se 2 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 354217 = 265663) (by norm_num)
theorem B354253 : Blo 311834 354253 := bbase (se 3 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 354253 = 132845) (by norm_num)
theorem B354289 : Blo 311834 354289 := bbase (se 2 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 354289 = 265717) (by norm_num)
theorem B354325 : Blo 311834 354325 := bbase (se 6 (by rfl) ⟨8304, by rfl⟩ : syracuseStep 354325 = 16609) (by norm_num)
theorem B354361 : Blo 311834 354361 := bbase (se 2 (by rfl) ⟨132885, by rfl⟩ : syracuseStep 354361 = 265771) (by norm_num)
theorem B354397 : Blo 311834 354397 := bbase (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) (by norm_num)
theorem B354433 : Blo 311834 354433 := bbase (se 2 (by rfl) ⟨132912, by rfl⟩ : syracuseStep 354433 = 265825) (by norm_num)
theorem B354469 : Blo 311834 354469 := bbase (se 4 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 354469 = 66463) (by norm_num)
theorem B354505 : Blo 311834 354505 := bbase (se 2 (by rfl) ⟨132939, by rfl⟩ : syracuseStep 354505 = 265879) (by norm_num)
theorem B354541 : Blo 311834 354541 := bbase (se 3 (by rfl) ⟨66476, by rfl⟩ : syracuseStep 354541 = 132953) (by norm_num)
theorem B354577 : Blo 311834 354577 := bbase (se 2 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 354577 = 265933) (by norm_num)
theorem B354613 : Blo 311834 354613 := bbase (se 5 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 354613 = 33245) (by norm_num)
theorem B354649 : Blo 311834 354649 := bbase (se 2 (by rfl) ⟨132993, by rfl⟩ : syracuseStep 354649 = 265987) (by norm_num)
theorem B354685 : Blo 311834 354685 := bbase (se 3 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 354685 = 133007) (by norm_num)
theorem B846229 : Blo 311834 846229 := bbase (se 6 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 846229 = 39667) (by norm_num)
theorem B354721 : Blo 311834 354721 := bbase (se 2 (by rfl) ⟨133020, by rfl⟩ : syracuseStep 354721 = 266041) (by norm_num)
theorem B354757 : Blo 311834 354757 := bbase (se 4 (by rfl) ⟨33258, by rfl⟩ : syracuseStep 354757 = 66517) (by norm_num)
theorem B354793 : Blo 311834 354793 := bbase (se 2 (by rfl) ⟨133047, by rfl⟩ : syracuseStep 354793 = 266095) (by norm_num)
theorem B354829 : Blo 311834 354829 := bbase (se 3 (by rfl) ⟨66530, by rfl⟩ : syracuseStep 354829 = 133061) (by norm_num)
theorem B354865 : Blo 311834 354865 := bbase (se 2 (by rfl) ⟨133074, by rfl⟩ : syracuseStep 354865 = 266149) (by norm_num)
theorem B354901 : Blo 311834 354901 := bbase (se 8 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 354901 = 4159) (by norm_num)
theorem B354937 : Blo 311834 354937 := bbase (se 2 (by rfl) ⟨133101, by rfl⟩ : syracuseStep 354937 = 266203) (by norm_num)
theorem B354973 : Blo 311834 354973 := bbase (se 3 (by rfl) ⟨66557, by rfl⟩ : syracuseStep 354973 = 133115) (by norm_num)
theorem B355009 : Blo 311834 355009 := bbase (se 2 (by rfl) ⟨133128, by rfl⟩ : syracuseStep 355009 = 266257) (by norm_num)
theorem B355045 : Blo 311834 355045 := bbase (se 4 (by rfl) ⟨33285, by rfl⟩ : syracuseStep 355045 = 66571) (by norm_num)
theorem B355081 : Blo 311834 355081 := bbase (se 2 (by rfl) ⟨133155, by rfl⟩ : syracuseStep 355081 = 266311) (by norm_num)
theorem B355117 : Blo 311834 355117 := bbase (se 3 (by rfl) ⟨66584, by rfl⟩ : syracuseStep 355117 = 133169) (by norm_num)
theorem B1010485 : Blo 311834 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B355153 : Blo 311834 355153 := bbase (se 2 (by rfl) ⟨133182, by rfl⟩ : syracuseStep 355153 = 266365) (by norm_num)
theorem B4025173 : Blo 311834 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B1010549 : Blo 311834 1010549 := bbase (se 5 (by rfl) ⟨47369, by rfl⟩ : syracuseStep 1010549 = 94739) (by norm_num)
theorem B355189 : Blo 311834 355189 := bbase (se 5 (by rfl) ⟨16649, by rfl⟩ : syracuseStep 355189 = 33299) (by norm_num)
theorem B355225 : Blo 311834 355225 := bbase (se 2 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 355225 = 266419) (by norm_num)
theorem B519077 : Blo 311834 519077 := bbase (se 4 (by rfl) ⟨48663, by rfl⟩ : syracuseStep 519077 = 97327) (by norm_num)
theorem B355261 : Blo 311834 355261 := bbase (se 3 (by rfl) ⟨66611, by rfl⟩ : syracuseStep 355261 = 133223) (by norm_num)
theorem B355297 : Blo 311834 355297 := bbase (se 2 (by rfl) ⟨133236, by rfl⟩ : syracuseStep 355297 = 266473) (by norm_num)
theorem B1338565 : Blo 311834 1338565 := bbase (se 4 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 1338565 = 250981) (by norm_num)
theorem B1338581 : Blo 311834 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B3075317 : Blo 311834 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B3042613 : Blo 311834 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B716197 : Blo 311834 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B2256437 : Blo 311834 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B355981 : Blo 311834 355981 := bbase (se 3 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 355981 = 133493) (by norm_num)
theorem B356081 : Blo 311834 356081 := bbase (se 2 (by rfl) ⟨133530, by rfl⟩ : syracuseStep 356081 = 267061) (by norm_num)
theorem B421741 : Blo 311834 421741 := bbase (se 3 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 421741 = 158153) (by norm_num)
theorem B421861 : Blo 311834 421861 := bbase (se 4 (by rfl) ⟨39549, by rfl⟩ : syracuseStep 421861 = 79099) (by norm_num)
theorem B356333 : Blo 311834 356333 := bbase (se 3 (by rfl) ⟨66812, by rfl⟩ : syracuseStep 356333 = 133625) (by norm_num)
theorem B1929205 : Blo 311834 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B356629 : Blo 311834 356629 := bbase (se 6 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 356629 = 16717) (by norm_num)
theorem B356665 : Blo 311834 356665 := bbase (se 2 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 356665 = 267499) (by norm_num)
theorem B357149 : Blo 311834 357149 := bbase (se 3 (by rfl) ⟨66965, by rfl⟩ : syracuseStep 357149 = 133931) (by norm_num)
theorem B455557 : Blo 311834 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B1143733 : Blo 311834 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B848933 : Blo 311834 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B750637 : Blo 311834 750637 := bbase (se 3 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 750637 = 281489) (by norm_num)
theorem B423245 : Blo 311834 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B357733 : Blo 311834 357733 := bbase (se 4 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 357733 = 67075) (by norm_num)
theorem B750973 : Blo 311834 750973 := bbase (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) (by norm_num)
theorem B357797 : Blo 311834 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B1340837 : Blo 311834 1340837 := bbase (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) (by norm_num)
theorem B751589 : Blo 311834 751589 := bbase (se 4 (by rfl) ⟨70461, by rfl⟩ : syracuseStep 751589 = 140923) (by norm_num)
theorem B1603925 : Blo 311834 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B752021 : Blo 311834 752021 := bbase (se 6 (by rfl) ⟨17625, by rfl⟩ : syracuseStep 752021 = 35251) (by norm_num)
theorem B359257 : Blo 311834 359257 := bbase (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) (by norm_num)
theorem B1276901 : Blo 311834 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B687109 : Blo 311834 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B752645 : Blo 311834 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B687421 : Blo 311834 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B425309 : Blo 311834 425309 := bbase (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) (by norm_num)
theorem B1211813 : Blo 311834 1211813 := bbase (se 4 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 1211813 = 227215) (by norm_num)
theorem B2391605 : Blo 311834 2391605 := bbase (se 5 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 2391605 = 224213) (by norm_num)
theorem B425893 : Blo 311834 425893 := bbase (se 4 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 425893 = 79855) (by norm_num)
theorem B1343537 : Blo 311834 1343537 := bstep (se 2 (by rfl) ⟨503826, by rfl⟩ : syracuseStep 1343537 = 1007653) B1007653
theorem B7635313 : Blo 311834 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B754481 : Blo 311834 754481 := bstep (se 2 (by rfl) ⟨282930, by rfl⟩ : syracuseStep 754481 = 565861) B565861
theorem B2556785 : Blo 311834 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B394723 : Blo 311834 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B460513 : Blo 311834 460513 := bstep (se 2 (by rfl) ⟨172692, by rfl⟩ : syracuseStep 460513 = 345385) B345385
theorem B1509133 : Blo 311834 1509133 := bstep (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) B565925
theorem B3573557 : Blo 311834 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B526243 : Blo 311834 526243 := bstep (se 1 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 526243 = 789365) B789365
theorem B395219 : Blo 311834 395219 := bstep (se 1 (by rfl) ⟨296414, by rfl⟩ : syracuseStep 395219 = 592829) B592829
theorem B5736419 : Blo 311834 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B526385 : Blo 311834 526385 := bstep (se 2 (by rfl) ⟨197394, by rfl⟩ : syracuseStep 526385 = 394789) B394789
theorem B1509425 : Blo 311834 1509425 := bstep (se 2 (by rfl) ⟨566034, by rfl⟩ : syracuseStep 1509425 = 1132069) B1132069
theorem B952397 : Blo 311834 952397 := bstep (se 3 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 952397 = 357149) B357149
theorem B4524173 : Blo 311834 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B526513 : Blo 311834 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B526547 : Blo 311834 526547 := bstep (se 1 (by rfl) ⟨394910, by rfl⟩ : syracuseStep 526547 = 789821) B789821
theorem B526675 : Blo 311834 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B756067 : Blo 311834 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B1706339 : Blo 311834 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B2591117 : Blo 311834 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B1345997 : Blo 311834 1345997 := bstep (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) B504749
theorem B526817 : Blo 311834 526817 := bstep (se 2 (by rfl) ⟨197556, by rfl⟩ : syracuseStep 526817 = 395113) B395113
theorem B526945 : Blo 311834 526945 := bstep (se 2 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 526945 = 395209) B395209
theorem B526979 : Blo 311834 526979 := bstep (se 1 (by rfl) ⟨395234, by rfl⟩ : syracuseStep 526979 = 790469) B790469
theorem B395923 : Blo 311834 395923 := bstep (se 1 (by rfl) ⟨296942, by rfl⟩ : syracuseStep 395923 = 593885) B593885
theorem B8784611 : Blo 311834 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B396019 : Blo 311834 396019 := bstep (se 1 (by rfl) ⟨297014, by rfl⟩ : syracuseStep 396019 = 594029) B594029
theorem B527107 : Blo 311834 527107 := bstep (se 1 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 527107 = 790661) B790661
theorem B592753 : Blo 311834 592753 := bstep (se 2 (by rfl) ⟨222282, by rfl⟩ : syracuseStep 592753 = 444565) B444565
theorem B527249 : Blo 311834 527249 := bstep (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) B395437
theorem B756643 : Blo 311834 756643 := bstep (se 1 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 756643 = 1134965) B1134965
theorem B2001925 : Blo 311834 2001925 := bstep (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) B375361
theorem B592913 : Blo 311834 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B527377 : Blo 311834 527377 := bstep (se 2 (by rfl) ⟨197766, by rfl⟩ : syracuseStep 527377 = 395533) B395533
theorem B527411 : Blo 311834 527411 := bstep (se 1 (by rfl) ⟨395558, by rfl⟩ : syracuseStep 527411 = 791117) B791117
theorem B527539 : Blo 311834 527539 := bstep (se 1 (by rfl) ⟨395654, by rfl⟩ : syracuseStep 527539 = 791309) B791309
theorem B888013 : Blo 311834 888013 := bstep (se 3 (by rfl) ⟨166502, by rfl⟩ : syracuseStep 888013 = 333005) B333005
theorem B396515 : Blo 311834 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B757027 : Blo 311834 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B527681 : Blo 311834 527681 := bstep (se 2 (by rfl) ⟨197880, by rfl⟩ : syracuseStep 527681 = 395761) B395761
theorem B2035043 : Blo 311834 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B593315 : Blo 311834 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B888241 : Blo 311834 888241 := bstep (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) B666181
theorem B527809 : Blo 311834 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B16289221 : Blo 311834 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B527843 : Blo 311834 527843 := bstep (se 1 (by rfl) ⟨395882, by rfl⟩ : syracuseStep 527843 = 791765) B791765
theorem B790033 : Blo 311834 790033 := bstep (se 2 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 790033 = 592525) B592525
theorem B724547 : Blo 311834 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B888401 : Blo 311834 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B527971 : Blo 311834 527971 := bstep (se 1 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 527971 = 791957) B791957
theorem B888515 : Blo 311834 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B528113 : Blo 311834 528113 := bstep (se 2 (by rfl) ⟨198042, by rfl⟩ : syracuseStep 528113 = 396085) B396085
theorem B1347313 : Blo 311834 1347313 := bstep (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) B1010485
theorem B954125 : Blo 311834 954125 := bstep (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) B357797
theorem B790307 : Blo 311834 790307 := bstep (se 1 (by rfl) ⟨592730, by rfl⟩ : syracuseStep 790307 = 1185461) B1185461
theorem B3411811 : Blo 311834 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B528241 : Blo 311834 528241 := bstep (se 2 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 528241 = 396181) B396181
theorem B528275 : Blo 311834 528275 := bstep (se 1 (by rfl) ⟨396206, by rfl⟩ : syracuseStep 528275 = 792413) B792413
theorem B397219 : Blo 311834 397219 := bstep (se 1 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 397219 = 595829) B595829
theorem B11407301 : Blo 311834 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B1052621 : Blo 311834 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B790499 : Blo 311834 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B1052675 : Blo 311834 1052675 := bstep (se 1 (by rfl) ⟨789506, by rfl⟩ : syracuseStep 1052675 = 1579013) B1579013
theorem B397315 : Blo 311834 397315 := bstep (se 1 (by rfl) ⟨297986, by rfl⟩ : syracuseStep 397315 = 595973) B595973
theorem B528403 : Blo 311834 528403 := bstep (se 1 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 528403 = 792605) B792605
theorem B1380401 : Blo 311834 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B757873 : Blo 311834 757873 := bstep (se 2 (by rfl) ⟨284202, by rfl⟩ : syracuseStep 757873 = 568405) B568405
theorem B528545 : Blo 311834 528545 := bstep (se 2 (by rfl) ⟨198204, by rfl⟩ : syracuseStep 528545 = 396409) B396409
theorem B1052945 : Blo 311834 1052945 := bstep (se 2 (by rfl) ⟨394854, by rfl⟩ : syracuseStep 1052945 = 789709) B789709
theorem B528673 : Blo 311834 528673 := bstep (se 2 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 528673 = 396505) B396505
theorem B594211 : Blo 311834 594211 := bstep (se 1 (by rfl) ⟨445658, by rfl⟩ : syracuseStep 594211 = 891317) B891317
theorem B528707 : Blo 311834 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B594371 : Blo 311834 594371 := bstep (se 1 (by rfl) ⟨445778, by rfl⟩ : syracuseStep 594371 = 891557) B891557
theorem B528835 : Blo 311834 528835 := bstep (se 1 (by rfl) ⟨396626, by rfl⟩ : syracuseStep 528835 = 793253) B793253
theorem B1511885 : Blo 311834 1511885 := bstep (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) B566957
theorem B397811 : Blo 311834 397811 := bstep (se 1 (by rfl) ⟨298358, by rfl⟩ : syracuseStep 397811 = 596717) B596717
theorem B1184291 : Blo 311834 1184291 := bstep (se 1 (by rfl) ⟨888218, by rfl⟩ : syracuseStep 1184291 = 1776437) B1776437
theorem B954929 : Blo 311834 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B528977 : Blo 311834 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B889517 : Blo 311834 889517 := bstep (se 3 (by rfl) ⟨166784, by rfl⟩ : syracuseStep 889517 = 333569) B333569
theorem B529105 : Blo 311834 529105 := bstep (se 2 (by rfl) ⟨198414, by rfl⟩ : syracuseStep 529105 = 396829) B396829
theorem B529139 : Blo 311834 529139 := bstep (se 1 (by rfl) ⟨396854, by rfl⟩ : syracuseStep 529139 = 793709) B793709
theorem B1053485 : Blo 311834 1053485 := bstep (se 3 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 1053485 = 395057) B395057
theorem B1053539 : Blo 311834 1053539 := bstep (se 1 (by rfl) ⟨790154, by rfl⟩ : syracuseStep 1053539 = 1580309) B1580309
theorem B889699 : Blo 311834 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B529267 : Blo 311834 529267 := bstep (se 1 (by rfl) ⟨396950, by rfl⟩ : syracuseStep 529267 = 793901) B793901
theorem B791441 : Blo 311834 791441 := bstep (se 2 (by rfl) ⟨296790, by rfl⟩ : syracuseStep 791441 = 593581) B593581
theorem B791491 : Blo 311834 791491 := bstep (se 1 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 791491 = 1187237) B1187237
theorem B529409 : Blo 311834 529409 := bstep (se 2 (by rfl) ⟨198528, by rfl⟩ : syracuseStep 529409 = 397057) B397057
theorem B889859 : Blo 311834 889859 := bstep (se 1 (by rfl) ⟨667394, by rfl⟩ : syracuseStep 889859 = 1334789) B1334789
theorem B791633 : Blo 311834 791633 := bstep (se 2 (by rfl) ⟨296862, by rfl⟩ : syracuseStep 791633 = 593725) B593725
theorem B2266211 : Blo 311834 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B3839075 : Blo 311834 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B1053809 : Blo 311834 1053809 := bstep (se 2 (by rfl) ⟨395178, by rfl⟩ : syracuseStep 1053809 = 790357) B790357
theorem B529537 : Blo 311834 529537 := bstep (se 2 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 529537 = 397153) B397153
theorem B562307 : Blo 311834 562307 := bstep (se 1 (by rfl) ⟨421730, by rfl⟩ : syracuseStep 562307 = 843461) B843461
theorem B2135173 : Blo 311834 2135173 := bstep (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) B400345
theorem B562321 : Blo 311834 562321 := bstep (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) B421741
theorem B529571 : Blo 311834 529571 := bstep (se 1 (by rfl) ⟨397178, by rfl⟩ : syracuseStep 529571 = 794357) B794357
theorem B398515 : Blo 311834 398515 := bstep (se 1 (by rfl) ⟨298886, by rfl⟩ : syracuseStep 398515 = 597773) B597773
theorem B398611 : Blo 311834 398611 := bstep (se 1 (by rfl) ⟨298958, by rfl⟩ : syracuseStep 398611 = 597917) B597917
theorem B529699 : Blo 311834 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B562481 : Blo 311834 562481 := bstep (se 2 (by rfl) ⟨210930, by rfl⟩ : syracuseStep 562481 = 421861) B421861
theorem B529841 : Blo 311834 529841 := bstep (se 2 (by rfl) ⟨198690, by rfl⟩ : syracuseStep 529841 = 397381) B397381
theorem B595441 : Blo 311834 595441 := bstep (se 2 (by rfl) ⟨223290, by rfl⟩ : syracuseStep 595441 = 446581) B446581
theorem B1185293 : Blo 311834 1185293 := bstep (se 3 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 1185293 = 444485) B444485
theorem B529969 : Blo 311834 529969 := bstep (se 2 (by rfl) ⟨198738, by rfl⟩ : syracuseStep 529969 = 397477) B397477
theorem B530003 : Blo 311834 530003 := bstep (se 1 (by rfl) ⟨397502, by rfl⟩ : syracuseStep 530003 = 795005) B795005
theorem B1054349 : Blo 311834 1054349 := bstep (se 3 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 1054349 = 395381) B395381
theorem B1054403 : Blo 311834 1054403 := bstep (se 1 (by rfl) ⟨790802, by rfl⟩ : syracuseStep 1054403 = 1581605) B1581605
theorem B530131 : Blo 311834 530131 := bstep (se 1 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 530131 = 795197) B795197
theorem B2397923 : Blo 311834 2397923 := bstep (se 1 (by rfl) ⟨1798442, by rfl⟩ : syracuseStep 2397923 = 3596885) B3596885
theorem B399107 : Blo 311834 399107 := bstep (se 1 (by rfl) ⟨299330, by rfl⟩ : syracuseStep 399107 = 598661) B598661
theorem B530273 : Blo 311834 530273 := bstep (se 2 (by rfl) ⟨198852, by rfl⟩ : syracuseStep 530273 = 397705) B397705
theorem B1578851 : Blo 311834 1578851 := bstep (se 1 (by rfl) ⟨1184138, by rfl⟩ : syracuseStep 1578851 = 2368277) B2368277
theorem B1054673 : Blo 311834 1054673 := bstep (se 2 (by rfl) ⟨395502, by rfl⟩ : syracuseStep 1054673 = 791005) B791005
theorem B530401 : Blo 311834 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B2529251 : Blo 311834 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B530435 : Blo 311834 530435 := bstep (se 1 (by rfl) ⟨397826, by rfl⟩ : syracuseStep 530435 = 795653) B795653
theorem B890929 : Blo 311834 890929 := bstep (se 2 (by rfl) ⟨334098, by rfl⟩ : syracuseStep 890929 = 668197) B668197
theorem B792625 : Blo 311834 792625 := bstep (se 2 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 792625 = 594469) B594469
theorem B563267 : Blo 311834 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B530563 : Blo 311834 530563 := bstep (se 1 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 530563 = 795845) B795845
theorem B530705 : Blo 311834 530705 := bstep (se 2 (by rfl) ⟨199014, by rfl⟩ : syracuseStep 530705 = 398029) B398029
theorem B792899 : Blo 311834 792899 := bstep (se 1 (by rfl) ⟨594674, by rfl⟩ : syracuseStep 792899 = 1189349) B1189349
theorem B334163 : Blo 311834 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B1776005 : Blo 311834 1776005 := bstep (se 4 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 1776005 = 333001) B333001
theorem B530833 : Blo 311834 530833 := bstep (se 2 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 530833 = 398125) B398125
theorem B2005411 : Blo 311834 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B530867 : Blo 311834 530867 := bstep (se 1 (by rfl) ⟨398150, by rfl⟩ : syracuseStep 530867 = 796301) B796301
theorem B1055213 : Blo 311834 1055213 := bstep (se 3 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 1055213 = 395705) B395705
theorem B793091 : Blo 311834 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B596497 : Blo 311834 596497 := bstep (se 2 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 596497 = 447373) B447373
theorem B1055267 : Blo 311834 1055267 := bstep (se 1 (by rfl) ⟨791450, by rfl⟩ : syracuseStep 1055267 = 1582901) B1582901
theorem B530995 : Blo 311834 530995 := bstep (se 1 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 530995 = 796493) B796493
theorem B3414581 : Blo 311834 3414581 := bstep (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) B320117
theorem B1579661 : Blo 311834 1579661 := bstep (se 3 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 1579661 = 592373) B592373
theorem B531137 : Blo 311834 531137 := bstep (se 2 (by rfl) ⟨199176, by rfl⟩ : syracuseStep 531137 = 398353) B398353
theorem B1055537 : Blo 311834 1055537 := bstep (se 2 (by rfl) ⟨395826, by rfl⟩ : syracuseStep 1055537 = 791653) B791653
theorem B531265 : Blo 311834 531265 := bstep (se 2 (by rfl) ⟨199224, by rfl⟩ : syracuseStep 531265 = 398449) B398449
theorem B531299 : Blo 311834 531299 := bstep (se 1 (by rfl) ⟨398474, by rfl⟩ : syracuseStep 531299 = 796949) B796949
theorem B596899 : Blo 311834 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B596945 : Blo 311834 596945 := bstep (se 2 (by rfl) ⟨223854, by rfl⟩ : syracuseStep 596945 = 447709) B447709
theorem B531427 : Blo 311834 531427 := bstep (se 1 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 531427 = 797141) B797141
theorem B531569 : Blo 311834 531569 := bstep (se 2 (by rfl) ⟨199338, by rfl⟩ : syracuseStep 531569 = 398677) B398677
theorem B597233 : Blo 311834 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B531697 : Blo 311834 531697 := bstep (se 2 (by rfl) ⟨199386, by rfl⟩ : syracuseStep 531697 = 398773) B398773
theorem B335107 : Blo 311834 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B531731 : Blo 311834 531731 := bstep (se 1 (by rfl) ⟨398798, by rfl⟩ : syracuseStep 531731 = 797597) B797597
theorem B892205 : Blo 311834 892205 := bstep (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) B334577
theorem B1056077 : Blo 311834 1056077 := bstep (se 3 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 1056077 = 396029) B396029
theorem B1056131 : Blo 311834 1056131 := bstep (se 1 (by rfl) ⟨792098, by rfl⟩ : syracuseStep 1056131 = 1584197) B1584197
theorem B531859 : Blo 311834 531859 := bstep (se 1 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 531859 = 797789) B797789
theorem B794033 : Blo 311834 794033 := bstep (se 2 (by rfl) ⟨297762, by rfl⟩ : syracuseStep 794033 = 595525) B595525
theorem B892387 : Blo 311834 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B794083 : Blo 311834 794083 := bstep (se 1 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 794083 = 1191125) B1191125
theorem B4267505 : Blo 311834 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B892433 : Blo 311834 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B532001 : Blo 311834 532001 := bstep (se 2 (by rfl) ⟨199500, by rfl⟩ : syracuseStep 532001 = 399001) B399001
theorem B1187405 : Blo 311834 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B794225 : Blo 311834 794225 := bstep (se 2 (by rfl) ⟨297834, by rfl⟩ : syracuseStep 794225 = 595669) B595669
theorem B1056401 : Blo 311834 1056401 := bstep (se 2 (by rfl) ⟨396150, by rfl⟩ : syracuseStep 1056401 = 792301) B792301
theorem B532129 : Blo 311834 532129 := bstep (se 2 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 532129 = 399097) B399097
theorem B532163 : Blo 311834 532163 := bstep (se 1 (by rfl) ⟨399122, by rfl⟩ : syracuseStep 532163 = 798245) B798245
theorem B532291 : Blo 311834 532291 := bstep (se 1 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 532291 = 798437) B798437
theorem B597955 : Blo 311834 597955 := bstep (se 1 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 597955 = 896933) B896933
theorem B532433 : Blo 311834 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B532561 : Blo 311834 532561 := bstep (se 2 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 532561 = 399421) B399421
theorem B532595 : Blo 311834 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B1056941 : Blo 311834 1056941 := bstep (se 3 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 1056941 = 396353) B396353
theorem B1056995 : Blo 311834 1056995 := bstep (se 1 (by rfl) ⟨792746, by rfl⟩ : syracuseStep 1056995 = 1585493) B1585493
theorem B532723 : Blo 311834 532723 := bstep (se 1 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 532723 = 799085) B799085
theorem B499969 : Blo 311834 499969 := bstep (se 2 (by rfl) ⟨187488, by rfl⟩ : syracuseStep 499969 = 374977) B374977
theorem B1188209 : Blo 311834 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B532865 : Blo 311834 532865 := bstep (se 2 (by rfl) ⟨199824, by rfl⟩ : syracuseStep 532865 = 399649) B399649
theorem B598403 : Blo 311834 598403 := bstep (se 1 (by rfl) ⟨448802, by rfl⟩ : syracuseStep 598403 = 897605) B897605
theorem B1057265 : Blo 311834 1057265 := bstep (se 2 (by rfl) ⟨396474, by rfl⟩ : syracuseStep 1057265 = 792949) B792949
theorem B336371 : Blo 311834 336371 := bstep (se 1 (by rfl) ⟨252278, by rfl⟩ : syracuseStep 336371 = 504557) B504557
theorem B795217 : Blo 311834 795217 := bstep (se 2 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 795217 = 596413) B596413
theorem B598691 : Blo 311834 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B565955 : Blo 311834 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B467777 : Blo 311834 467777 := bstep (se 2 (by rfl) ⟨175416, by rfl⟩ : syracuseStep 467777 = 350833) B350833
theorem B467795 : Blo 311834 467795 := bstep (se 1 (by rfl) ⟨350846, by rfl⟩ : syracuseStep 467795 = 701693) B701693
theorem B795491 : Blo 311834 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B467825 : Blo 311834 467825 := bstep (se 2 (by rfl) ⟨175434, by rfl⟩ : syracuseStep 467825 = 350869) B350869
theorem B467843 : Blo 311834 467843 := bstep (se 1 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 467843 = 701765) B701765
theorem B8070029 : Blo 311834 8070029 := bstep (se 3 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 8070029 = 3026261) B3026261
theorem B467873 : Blo 311834 467873 := bstep (se 2 (by rfl) ⟨175452, by rfl⟩ : syracuseStep 467873 = 350905) B350905
theorem B467891 : Blo 311834 467891 := bstep (se 1 (by rfl) ⟨350918, by rfl⟩ : syracuseStep 467891 = 701837) B701837
theorem B893891 : Blo 311834 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B467921 : Blo 311834 467921 := bstep (se 2 (by rfl) ⟨175470, by rfl⟩ : syracuseStep 467921 = 350941) B350941
theorem B467939 : Blo 311834 467939 := bstep (se 1 (by rfl) ⟨350954, by rfl⟩ : syracuseStep 467939 = 701909) B701909
theorem B467969 : Blo 311834 467969 := bstep (se 2 (by rfl) ⟨175488, by rfl⟩ : syracuseStep 467969 = 350977) B350977
theorem B1188877 : Blo 311834 1188877 := bstep (se 3 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 1188877 = 445829) B445829
theorem B1057805 : Blo 311834 1057805 := bstep (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) B396677
theorem B467987 : Blo 311834 467987 := bstep (se 1 (by rfl) ⟨350990, by rfl⟩ : syracuseStep 467987 = 701981) B701981
theorem B795683 : Blo 311834 795683 := bstep (se 1 (by rfl) ⟨596762, by rfl⟩ : syracuseStep 795683 = 1193525) B1193525
theorem B468017 : Blo 311834 468017 := bstep (se 2 (by rfl) ⟨175506, by rfl⟩ : syracuseStep 468017 = 351013) B351013
theorem B468035 : Blo 311834 468035 := bstep (se 1 (by rfl) ⟨351026, by rfl⟩ : syracuseStep 468035 = 702053) B702053
theorem B1057859 : Blo 311834 1057859 := bstep (se 1 (by rfl) ⟨793394, by rfl⟩ : syracuseStep 1057859 = 1586789) B1586789
theorem B468065 : Blo 311834 468065 := bstep (se 2 (by rfl) ⟨175524, by rfl⟩ : syracuseStep 468065 = 351049) B351049
theorem B468083 : Blo 311834 468083 := bstep (se 1 (by rfl) ⟨351062, by rfl⟩ : syracuseStep 468083 = 702125) B702125
theorem B468113 : Blo 311834 468113 := bstep (se 2 (by rfl) ⟨175542, by rfl⟩ : syracuseStep 468113 = 351085) B351085
theorem B468131 : Blo 311834 468131 := bstep (se 1 (by rfl) ⟨351098, by rfl⟩ : syracuseStep 468131 = 702197) B702197
theorem B468161 : Blo 311834 468161 := bstep (se 2 (by rfl) ⟨175560, by rfl⟩ : syracuseStep 468161 = 351121) B351121
theorem B468179 : Blo 311834 468179 := bstep (se 1 (by rfl) ⟨351134, by rfl⟩ : syracuseStep 468179 = 702269) B702269
theorem B337123 : Blo 311834 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B468209 : Blo 311834 468209 := bstep (se 2 (by rfl) ⟨175578, by rfl⟩ : syracuseStep 468209 = 351157) B351157
theorem B468227 : Blo 311834 468227 := bstep (se 1 (by rfl) ⟨351170, by rfl⟩ : syracuseStep 468227 = 702341) B702341
theorem B468257 : Blo 311834 468257 := bstep (se 2 (by rfl) ⟨175596, by rfl⟩ : syracuseStep 468257 = 351193) B351193
theorem B468275 : Blo 311834 468275 := bstep (se 1 (by rfl) ⟨351206, by rfl⟩ : syracuseStep 468275 = 702413) B702413
theorem B501059 : Blo 311834 501059 := bstep (se 1 (by rfl) ⟨375794, by rfl⟩ : syracuseStep 501059 = 751589) B751589
theorem B468305 : Blo 311834 468305 := bstep (se 2 (by rfl) ⟨175614, by rfl⟩ : syracuseStep 468305 = 351229) B351229
theorem B1058129 : Blo 311834 1058129 := bstep (se 2 (by rfl) ⟨396798, by rfl⟩ : syracuseStep 1058129 = 793597) B793597
theorem B468323 : Blo 311834 468323 := bstep (se 1 (by rfl) ⟨351242, by rfl⟩ : syracuseStep 468323 = 702485) B702485
theorem B468353 : Blo 311834 468353 := bstep (se 2 (by rfl) ⟨175632, by rfl⟩ : syracuseStep 468353 = 351265) B351265
theorem B468371 : Blo 311834 468371 := bstep (se 1 (by rfl) ⟨351278, by rfl⟩ : syracuseStep 468371 = 702557) B702557
theorem B468401 : Blo 311834 468401 := bstep (se 2 (by rfl) ⟨175650, by rfl⟩ : syracuseStep 468401 = 351301) B351301
theorem B533953 : Blo 311834 533953 := bstep (se 2 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 533953 = 400465) B400465
theorem B468419 : Blo 311834 468419 := bstep (se 1 (by rfl) ⟨351314, by rfl⟩ : syracuseStep 468419 = 702629) B702629
theorem B468449 : Blo 311834 468449 := bstep (se 2 (by rfl) ⟨175668, by rfl⟩ : syracuseStep 468449 = 351337) B351337
theorem B1910243 : Blo 311834 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B1582577 : Blo 311834 1582577 := bstep (se 2 (by rfl) ⟨593466, by rfl⟩ : syracuseStep 1582577 = 1186933) B1186933
theorem B468467 : Blo 311834 468467 := bstep (se 1 (by rfl) ⟨351350, by rfl⟩ : syracuseStep 468467 = 702701) B702701
theorem B468497 : Blo 311834 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B468515 : Blo 311834 468515 := bstep (se 1 (by rfl) ⟨351386, by rfl⟩ : syracuseStep 468515 = 702773) B702773
theorem B468545 : Blo 311834 468545 := bstep (se 2 (by rfl) ⟨175704, by rfl⟩ : syracuseStep 468545 = 351409) B351409
theorem B468563 : Blo 311834 468563 := bstep (se 1 (by rfl) ⟨351422, by rfl⟩ : syracuseStep 468563 = 702845) B702845
theorem B501347 : Blo 311834 501347 := bstep (se 1 (by rfl) ⟨376010, by rfl⟩ : syracuseStep 501347 = 752021) B752021
theorem B468593 : Blo 311834 468593 := bstep (se 2 (by rfl) ⟨175722, by rfl⟩ : syracuseStep 468593 = 351445) B351445
theorem B468611 : Blo 311834 468611 := bstep (se 1 (by rfl) ⟨351458, by rfl⟩ : syracuseStep 468611 = 702917) B702917
theorem B763537 : Blo 311834 763537 := bstep (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) B572653
theorem B468641 : Blo 311834 468641 := bstep (se 2 (by rfl) ⟨175740, by rfl⟩ : syracuseStep 468641 = 351481) B351481
theorem B468659 : Blo 311834 468659 := bstep (se 1 (by rfl) ⟨351494, by rfl⟩ : syracuseStep 468659 = 702989) B702989
theorem B468689 : Blo 311834 468689 := bstep (se 2 (by rfl) ⟨175758, by rfl⟩ : syracuseStep 468689 = 351517) B351517
theorem B468707 : Blo 311834 468707 := bstep (se 1 (by rfl) ⟨351530, by rfl⟩ : syracuseStep 468707 = 703061) B703061
theorem B468737 : Blo 311834 468737 := bstep (se 2 (by rfl) ⟨175776, by rfl⟩ : syracuseStep 468737 = 351553) B351553
theorem B468755 : Blo 311834 468755 := bstep (se 1 (by rfl) ⟨351566, by rfl⟩ : syracuseStep 468755 = 703133) B703133
theorem B403219 : Blo 311834 403219 := bstep (se 1 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 403219 = 604829) B604829
theorem B1189667 : Blo 311834 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B468785 : Blo 311834 468785 := bstep (se 2 (by rfl) ⟨175794, by rfl⟩ : syracuseStep 468785 = 351589) B351589
theorem B468803 : Blo 311834 468803 := bstep (se 1 (by rfl) ⟨351602, by rfl⟩ : syracuseStep 468803 = 703205) B703205
theorem B468833 : Blo 311834 468833 := bstep (se 2 (by rfl) ⟨175812, by rfl⟩ : syracuseStep 468833 = 351625) B351625
theorem B1058669 : Blo 311834 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B468851 : Blo 311834 468851 := bstep (se 1 (by rfl) ⟨351638, by rfl⟩ : syracuseStep 468851 = 703277) B703277
theorem B468881 : Blo 311834 468881 := bstep (se 2 (by rfl) ⟨175830, by rfl⟩ : syracuseStep 468881 = 351661) B351661
theorem B468899 : Blo 311834 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B1058723 : Blo 311834 1058723 := bstep (se 1 (by rfl) ⟨794042, by rfl⟩ : syracuseStep 1058723 = 1588085) B1588085
theorem B468929 : Blo 311834 468929 := bstep (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) B351697
theorem B796625 : Blo 311834 796625 := bstep (se 2 (by rfl) ⟨298734, by rfl⟩ : syracuseStep 796625 = 597469) B597469
theorem B468947 : Blo 311834 468947 := bstep (se 1 (by rfl) ⟨351710, by rfl⟩ : syracuseStep 468947 = 703421) B703421
theorem B468977 : Blo 311834 468977 := bstep (se 2 (by rfl) ⟨175866, by rfl⟩ : syracuseStep 468977 = 351733) B351733
theorem B468995 : Blo 311834 468995 := bstep (se 1 (by rfl) ⟨351746, by rfl⟩ : syracuseStep 468995 = 703493) B703493
theorem B501763 : Blo 311834 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B796675 : Blo 311834 796675 := bstep (se 1 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 796675 = 1195013) B1195013
theorem B469025 : Blo 311834 469025 := bstep (se 2 (by rfl) ⟨175884, by rfl⟩ : syracuseStep 469025 = 351769) B351769
theorem B469043 : Blo 311834 469043 := bstep (se 1 (by rfl) ⟨351782, by rfl⟩ : syracuseStep 469043 = 703565) B703565
theorem B469073 : Blo 311834 469073 := bstep (se 2 (by rfl) ⟨175902, by rfl⟩ : syracuseStep 469073 = 351805) B351805
theorem B469091 : Blo 311834 469091 := bstep (se 1 (by rfl) ⟨351818, by rfl⟩ : syracuseStep 469091 = 703637) B703637
theorem B469121 : Blo 311834 469121 := bstep (se 2 (by rfl) ⟨175920, by rfl⟩ : syracuseStep 469121 = 351841) B351841
theorem B1779853 : Blo 311834 1779853 := bstep (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) B667445
theorem B895121 : Blo 311834 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B796817 : Blo 311834 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B469139 : Blo 311834 469139 := bstep (se 1 (by rfl) ⟨351854, by rfl⟩ : syracuseStep 469139 = 703709) B703709
theorem B469169 : Blo 311834 469169 := bstep (se 2 (by rfl) ⟨175938, by rfl⟩ : syracuseStep 469169 = 351877) B351877
theorem B1058993 : Blo 311834 1058993 := bstep (se 2 (by rfl) ⟨397122, by rfl⟩ : syracuseStep 1058993 = 794245) B794245
theorem B469187 : Blo 311834 469187 := bstep (se 1 (by rfl) ⟨351890, by rfl⟩ : syracuseStep 469187 = 703781) B703781
theorem B2009285 : Blo 311834 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B469217 : Blo 311834 469217 := bstep (se 2 (by rfl) ⟨175956, by rfl⟩ : syracuseStep 469217 = 351913) B351913
theorem B469235 : Blo 311834 469235 := bstep (se 1 (by rfl) ⟨351926, by rfl⟩ : syracuseStep 469235 = 703853) B703853
theorem B469265 : Blo 311834 469265 := bstep (se 2 (by rfl) ⟨175974, by rfl⟩ : syracuseStep 469265 = 351949) B351949
theorem B502033 : Blo 311834 502033 := bstep (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) B376525
theorem B469283 : Blo 311834 469283 := bstep (se 1 (by rfl) ⟨351962, by rfl⟩ : syracuseStep 469283 = 703925) B703925
theorem B469313 : Blo 311834 469313 := bstep (se 2 (by rfl) ⟨175992, by rfl⟩ : syracuseStep 469313 = 351985) B351985
theorem B469331 : Blo 311834 469331 := bstep (se 1 (by rfl) ⟨351998, by rfl⟩ : syracuseStep 469331 = 703997) B703997
theorem B469361 : Blo 311834 469361 := bstep (se 2 (by rfl) ⟨176010, by rfl⟩ : syracuseStep 469361 = 352021) B352021
theorem B469379 : Blo 311834 469379 := bstep (se 1 (by rfl) ⟨352034, by rfl⟩ : syracuseStep 469379 = 704069) B704069
theorem B469409 : Blo 311834 469409 := bstep (se 2 (by rfl) ⟨176028, by rfl⟩ : syracuseStep 469409 = 352057) B352057
theorem B1190321 : Blo 311834 1190321 := bstep (se 2 (by rfl) ⟨446370, by rfl⟩ : syracuseStep 1190321 = 892741) B892741
theorem B469427 : Blo 311834 469427 := bstep (se 1 (by rfl) ⟨352070, by rfl⟩ : syracuseStep 469427 = 704141) B704141
theorem B469457 : Blo 311834 469457 := bstep (se 2 (by rfl) ⟨176046, by rfl⟩ : syracuseStep 469457 = 352093) B352093
theorem B469475 : Blo 311834 469475 := bstep (se 1 (by rfl) ⟨352106, by rfl⟩ : syracuseStep 469475 = 704213) B704213
theorem B535027 : Blo 311834 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B469505 : Blo 311834 469505 := bstep (se 2 (by rfl) ⟨176064, by rfl⟩ : syracuseStep 469505 = 352129) B352129
theorem B502289 : Blo 311834 502289 := bstep (se 2 (by rfl) ⟨188358, by rfl⟩ : syracuseStep 502289 = 376717) B376717
theorem B469523 : Blo 311834 469523 := bstep (se 1 (by rfl) ⟨352142, by rfl⟩ : syracuseStep 469523 = 704285) B704285
theorem B469553 : Blo 311834 469553 := bstep (se 2 (by rfl) ⟨176082, by rfl⟩ : syracuseStep 469553 = 352165) B352165
theorem B567857 : Blo 311834 567857 := bstep (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) B425893
theorem B469571 : Blo 311834 469571 := bstep (se 1 (by rfl) ⟨352178, by rfl⟩ : syracuseStep 469571 = 704357) B704357
theorem B469601 : Blo 311834 469601 := bstep (se 2 (by rfl) ⟨176100, by rfl⟩ : syracuseStep 469601 = 352201) B352201
theorem B469619 : Blo 311834 469619 := bstep (se 1 (by rfl) ⟨352214, by rfl⟩ : syracuseStep 469619 = 704429) B704429
theorem B469649 : Blo 311834 469649 := bstep (se 2 (by rfl) ⟨176118, by rfl⟩ : syracuseStep 469649 = 352237) B352237
theorem B469667 : Blo 311834 469667 := bstep (se 1 (by rfl) ⟨352250, by rfl⟩ : syracuseStep 469667 = 704501) B704501
theorem B469697 : Blo 311834 469697 := bstep (se 2 (by rfl) ⟨176136, by rfl⟩ : syracuseStep 469697 = 352273) B352273
theorem B1059533 : Blo 311834 1059533 := bstep (se 3 (by rfl) ⟨198662, by rfl⟩ : syracuseStep 1059533 = 397325) B397325
theorem B469715 : Blo 311834 469715 := bstep (se 1 (by rfl) ⟨352286, by rfl⟩ : syracuseStep 469715 = 704573) B704573
theorem B469745 : Blo 311834 469745 := bstep (se 2 (by rfl) ⟨176154, by rfl⟩ : syracuseStep 469745 = 352309) B352309
theorem B469763 : Blo 311834 469763 := bstep (se 1 (by rfl) ⟨352322, by rfl⟩ : syracuseStep 469763 = 704645) B704645
theorem B1059587 : Blo 311834 1059587 := bstep (se 1 (by rfl) ⟨794690, by rfl⟩ : syracuseStep 1059587 = 1589381) B1589381
theorem B469793 : Blo 311834 469793 := bstep (se 2 (by rfl) ⟨176172, by rfl⟩ : syracuseStep 469793 = 352345) B352345
theorem B469811 : Blo 311834 469811 := bstep (se 1 (by rfl) ⟨352358, by rfl⟩ : syracuseStep 469811 = 704717) B704717
theorem B469841 : Blo 311834 469841 := bstep (se 2 (by rfl) ⟨176190, by rfl⟩ : syracuseStep 469841 = 352381) B352381
theorem B469859 : Blo 311834 469859 := bstep (se 1 (by rfl) ⟨352394, by rfl⟩ : syracuseStep 469859 = 704789) B704789
theorem B666481 : Blo 311834 666481 := bstep (se 2 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 666481 = 499861) B499861
theorem B469889 : Blo 311834 469889 := bstep (se 2 (by rfl) ⟨176208, by rfl⟩ : syracuseStep 469889 = 352417) B352417
theorem B469907 : Blo 311834 469907 := bstep (se 1 (by rfl) ⟨352430, by rfl⟩ : syracuseStep 469907 = 704861) B704861
theorem B1584035 : Blo 311834 1584035 := bstep (se 1 (by rfl) ⟨1188026, by rfl⟩ : syracuseStep 1584035 = 2376053) B2376053
theorem B469937 : Blo 311834 469937 := bstep (se 2 (by rfl) ⟨176226, by rfl⟩ : syracuseStep 469937 = 352453) B352453
theorem B469955 : Blo 311834 469955 := bstep (se 1 (by rfl) ⟨352466, by rfl⟩ : syracuseStep 469955 = 704933) B704933
theorem B469985 : Blo 311834 469985 := bstep (se 2 (by rfl) ⟨176244, by rfl⟩ : syracuseStep 469985 = 352489) B352489
theorem B470003 : Blo 311834 470003 := bstep (se 1 (by rfl) ⟨352502, by rfl⟩ : syracuseStep 470003 = 705005) B705005
theorem B470033 : Blo 311834 470033 := bstep (se 2 (by rfl) ⟨176262, by rfl⟩ : syracuseStep 470033 = 352525) B352525
theorem B1059857 : Blo 311834 1059857 := bstep (se 2 (by rfl) ⟨397446, by rfl⟩ : syracuseStep 1059857 = 794893) B794893
theorem B470051 : Blo 311834 470051 := bstep (se 1 (by rfl) ⟨352538, by rfl⟩ : syracuseStep 470051 = 705077) B705077
theorem B470081 : Blo 311834 470081 := bstep (se 2 (by rfl) ⟨176280, by rfl⟩ : syracuseStep 470081 = 352561) B352561
theorem B470099 : Blo 311834 470099 := bstep (se 1 (by rfl) ⟨352574, by rfl⟩ : syracuseStep 470099 = 705149) B705149
theorem B470129 : Blo 311834 470129 := bstep (se 2 (by rfl) ⟨176298, by rfl⟩ : syracuseStep 470129 = 352597) B352597
theorem B797809 : Blo 311834 797809 := bstep (se 2 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 797809 = 598357) B598357
theorem B470147 : Blo 311834 470147 := bstep (se 1 (by rfl) ⟨352610, by rfl⟩ : syracuseStep 470147 = 705221) B705221
theorem B470177 : Blo 311834 470177 := bstep (se 2 (by rfl) ⟨176316, by rfl⟩ : syracuseStep 470177 = 352633) B352633
theorem B470195 : Blo 311834 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B470225 : Blo 311834 470225 := bstep (se 2 (by rfl) ⟨176334, by rfl⟩ : syracuseStep 470225 = 352669) B352669
theorem B502993 : Blo 311834 502993 := bstep (se 2 (by rfl) ⟨188622, by rfl⟩ : syracuseStep 502993 = 377245) B377245
theorem B470243 : Blo 311834 470243 := bstep (se 1 (by rfl) ⟨352682, by rfl⟩ : syracuseStep 470243 = 705365) B705365
theorem B470273 : Blo 311834 470273 := bstep (se 2 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 470273 = 352705) B352705
theorem B470291 : Blo 311834 470291 := bstep (se 1 (by rfl) ⟨352718, by rfl⟩ : syracuseStep 470291 = 705437) B705437
theorem B470321 : Blo 311834 470321 := bstep (se 2 (by rfl) ⟨176370, by rfl⟩ : syracuseStep 470321 = 352741) B352741
theorem B470339 : Blo 311834 470339 := bstep (se 1 (by rfl) ⟨352754, by rfl⟩ : syracuseStep 470339 = 705509) B705509
theorem B470369 : Blo 311834 470369 := bstep (se 2 (by rfl) ⟨176388, by rfl⟩ : syracuseStep 470369 = 352777) B352777
theorem B470387 : Blo 311834 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B798083 : Blo 311834 798083 := bstep (se 1 (by rfl) ⟨598562, by rfl⟩ : syracuseStep 798083 = 1197125) B1197125
theorem B470417 : Blo 311834 470417 := bstep (se 2 (by rfl) ⟨176406, by rfl⟩ : syracuseStep 470417 = 352813) B352813
theorem B470435 : Blo 311834 470435 := bstep (se 1 (by rfl) ⟨352826, by rfl⟩ : syracuseStep 470435 = 705653) B705653
theorem B470465 : Blo 311834 470465 := bstep (se 2 (by rfl) ⟨176424, by rfl⟩ : syracuseStep 470465 = 352849) B352849
theorem B470483 : Blo 311834 470483 := bstep (se 1 (by rfl) ⟨352862, by rfl⟩ : syracuseStep 470483 = 705725) B705725
theorem B470513 : Blo 311834 470513 := bstep (se 2 (by rfl) ⟨176442, by rfl⟩ : syracuseStep 470513 = 352885) B352885
theorem B2043377 : Blo 311834 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B470531 : Blo 311834 470531 := bstep (se 1 (by rfl) ⟨352898, by rfl⟩ : syracuseStep 470531 = 705797) B705797
theorem B470561 : Blo 311834 470561 := bstep (se 2 (by rfl) ⟨176460, by rfl⟩ : syracuseStep 470561 = 352921) B352921
theorem B1060397 : Blo 311834 1060397 := bstep (se 3 (by rfl) ⟨198824, by rfl⟩ : syracuseStep 1060397 = 397649) B397649
theorem B470579 : Blo 311834 470579 := bstep (se 1 (by rfl) ⟨352934, by rfl⟩ : syracuseStep 470579 = 705869) B705869
theorem B896579 : Blo 311834 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B798275 : Blo 311834 798275 := bstep (se 1 (by rfl) ⟨598706, by rfl⟩ : syracuseStep 798275 = 1197413) B1197413
theorem B2862661 : Blo 311834 2862661 := bstep (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) B536749
theorem B470609 : Blo 311834 470609 := bstep (se 2 (by rfl) ⟨176478, by rfl⟩ : syracuseStep 470609 = 352957) B352957
theorem B470627 : Blo 311834 470627 := bstep (se 1 (by rfl) ⟨352970, by rfl⟩ : syracuseStep 470627 = 705941) B705941
theorem B1060451 : Blo 311834 1060451 := bstep (se 1 (by rfl) ⟨795338, by rfl⟩ : syracuseStep 1060451 = 1590677) B1590677
theorem B470657 : Blo 311834 470657 := bstep (se 2 (by rfl) ⟨176496, by rfl⟩ : syracuseStep 470657 = 352993) B352993
theorem B470675 : Blo 311834 470675 := bstep (se 1 (by rfl) ⟨353006, by rfl⟩ : syracuseStep 470675 = 706013) B706013
theorem B470705 : Blo 311834 470705 := bstep (se 2 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 470705 = 353029) B353029
theorem B470723 : Blo 311834 470723 := bstep (se 1 (by rfl) ⟨353042, by rfl⟩ : syracuseStep 470723 = 706085) B706085
theorem B1584845 : Blo 311834 1584845 := bstep (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) B594317
theorem B470753 : Blo 311834 470753 := bstep (se 2 (by rfl) ⟨176532, by rfl⟩ : syracuseStep 470753 = 353065) B353065
theorem B470771 : Blo 311834 470771 := bstep (se 1 (by rfl) ⟨353078, by rfl⟩ : syracuseStep 470771 = 706157) B706157
theorem B470801 : Blo 311834 470801 := bstep (se 2 (by rfl) ⟨176550, by rfl⟩ : syracuseStep 470801 = 353101) B353101
theorem B470819 : Blo 311834 470819 := bstep (se 1 (by rfl) ⟨353114, by rfl⟩ : syracuseStep 470819 = 706229) B706229
theorem B470849 : Blo 311834 470849 := bstep (se 2 (by rfl) ⟨176568, by rfl⟩ : syracuseStep 470849 = 353137) B353137
theorem B470867 : Blo 311834 470867 := bstep (se 1 (by rfl) ⟨353150, by rfl⟩ : syracuseStep 470867 = 706301) B706301
theorem B1191779 : Blo 311834 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B1191793 : Blo 311834 1191793 := bstep (se 2 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 1191793 = 893845) B893845
theorem B470897 : Blo 311834 470897 := bstep (se 2 (by rfl) ⟨176586, by rfl⟩ : syracuseStep 470897 = 353173) B353173
theorem B1060721 : Blo 311834 1060721 := bstep (se 2 (by rfl) ⟨397770, by rfl⟩ : syracuseStep 1060721 = 795541) B795541
theorem B470915 : Blo 311834 470915 := bstep (se 1 (by rfl) ⟨353186, by rfl⟩ : syracuseStep 470915 = 706373) B706373
theorem B470945 : Blo 311834 470945 := bstep (se 2 (by rfl) ⟨176604, by rfl⟩ : syracuseStep 470945 = 353209) B353209
theorem B470963 : Blo 311834 470963 := bstep (se 1 (by rfl) ⟨353222, by rfl⟩ : syracuseStep 470963 = 706445) B706445
theorem B470993 : Blo 311834 470993 := bstep (se 2 (by rfl) ⟨176622, by rfl⟩ : syracuseStep 470993 = 353245) B353245
theorem B536545 : Blo 311834 536545 := bstep (se 2 (by rfl) ⟨201204, by rfl⟩ : syracuseStep 536545 = 402409) B402409
theorem B2142179 : Blo 311834 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B471011 : Blo 311834 471011 := bstep (se 1 (by rfl) ⟨353258, by rfl⟩ : syracuseStep 471011 = 706517) B706517
theorem B471041 : Blo 311834 471041 := bstep (se 2 (by rfl) ⟨176640, by rfl⟩ : syracuseStep 471041 = 353281) B353281
theorem B471059 : Blo 311834 471059 := bstep (se 1 (by rfl) ⟨353294, by rfl⟩ : syracuseStep 471059 = 706589) B706589
theorem B471089 : Blo 311834 471089 := bstep (se 2 (by rfl) ⟨176658, by rfl⟩ : syracuseStep 471089 = 353317) B353317
theorem B471107 : Blo 311834 471107 := bstep (se 1 (by rfl) ⟨353330, by rfl⟩ : syracuseStep 471107 = 706661) B706661
theorem B1781837 : Blo 311834 1781837 := bstep (se 3 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 1781837 = 668189) B668189
theorem B503891 : Blo 311834 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B471137 : Blo 311834 471137 := bstep (se 2 (by rfl) ⟨176676, by rfl⟩ : syracuseStep 471137 = 353353) B353353
theorem B471155 : Blo 311834 471155 := bstep (se 1 (by rfl) ⟨353366, by rfl⟩ : syracuseStep 471155 = 706733) B706733
theorem B471185 : Blo 311834 471185 := bstep (se 2 (by rfl) ⟨176694, by rfl⟩ : syracuseStep 471185 = 353389) B353389
theorem B471203 : Blo 311834 471203 := bstep (se 1 (by rfl) ⟨353402, by rfl⟩ : syracuseStep 471203 = 706805) B706805
theorem B471233 : Blo 311834 471233 := bstep (se 2 (by rfl) ⟨176712, by rfl⟩ : syracuseStep 471233 = 353425) B353425
theorem B471251 : Blo 311834 471251 := bstep (se 1 (by rfl) ⟨353438, by rfl⟩ : syracuseStep 471251 = 706877) B706877
theorem B471281 : Blo 311834 471281 := bstep (se 2 (by rfl) ⟨176730, by rfl⟩ : syracuseStep 471281 = 353461) B353461
theorem B471299 : Blo 311834 471299 := bstep (se 1 (by rfl) ⟨353474, by rfl⟩ : syracuseStep 471299 = 706949) B706949
theorem B504083 : Blo 311834 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B471329 : Blo 311834 471329 := bstep (se 2 (by rfl) ⟨176748, by rfl⟩ : syracuseStep 471329 = 353497) B353497
theorem B471347 : Blo 311834 471347 := bstep (se 1 (by rfl) ⟨353510, by rfl⟩ : syracuseStep 471347 = 707021) B707021
theorem B471377 : Blo 311834 471377 := bstep (se 2 (by rfl) ⟨176766, by rfl⟩ : syracuseStep 471377 = 353533) B353533
theorem B471395 : Blo 311834 471395 := bstep (se 1 (by rfl) ⟨353546, by rfl⟩ : syracuseStep 471395 = 707093) B707093
theorem B897389 : Blo 311834 897389 := bstep (se 3 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 897389 = 336521) B336521
theorem B471425 : Blo 311834 471425 := bstep (se 2 (by rfl) ⟨176784, by rfl⟩ : syracuseStep 471425 = 353569) B353569
theorem B1061261 : Blo 311834 1061261 := bstep (se 3 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 1061261 = 397973) B397973
theorem B471443 : Blo 311834 471443 := bstep (se 1 (by rfl) ⟨353582, by rfl⟩ : syracuseStep 471443 = 707165) B707165
theorem B471473 : Blo 311834 471473 := bstep (se 2 (by rfl) ⟨176802, by rfl⟩ : syracuseStep 471473 = 353605) B353605
theorem B471491 : Blo 311834 471491 := bstep (se 1 (by rfl) ⟨353618, by rfl⟩ : syracuseStep 471491 = 707237) B707237
theorem B1061315 : Blo 311834 1061315 := bstep (se 1 (by rfl) ⟨795986, by rfl⟩ : syracuseStep 1061315 = 1591973) B1591973
theorem B471521 : Blo 311834 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B799217 : Blo 311834 799217 := bstep (se 2 (by rfl) ⟨299706, by rfl⟩ : syracuseStep 799217 = 599413) B599413
theorem B471539 : Blo 311834 471539 := bstep (se 1 (by rfl) ⟨353654, by rfl⟩ : syracuseStep 471539 = 707309) B707309
theorem B471569 : Blo 311834 471569 := bstep (se 2 (by rfl) ⟨176838, by rfl⟩ : syracuseStep 471569 = 353677) B353677
theorem B471587 : Blo 311834 471587 := bstep (se 1 (by rfl) ⟨353690, by rfl⟩ : syracuseStep 471587 = 707381) B707381
theorem B799267 : Blo 311834 799267 := bstep (se 1 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 799267 = 1198901) B1198901
theorem B897581 : Blo 311834 897581 := bstep (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) B336593
theorem B471617 : Blo 311834 471617 := bstep (se 2 (by rfl) ⟨176856, by rfl⟩ : syracuseStep 471617 = 353713) B353713
theorem B2372165 : Blo 311834 2372165 := bstep (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) B444781
theorem B471635 : Blo 311834 471635 := bstep (se 1 (by rfl) ⟨353726, by rfl⟩ : syracuseStep 471635 = 707453) B707453
theorem B471665 : Blo 311834 471665 := bstep (se 2 (by rfl) ⟨176874, by rfl⟩ : syracuseStep 471665 = 353749) B353749
theorem B471683 : Blo 311834 471683 := bstep (se 1 (by rfl) ⟨353762, by rfl⟩ : syracuseStep 471683 = 707525) B707525
theorem B471713 : Blo 311834 471713 := bstep (se 2 (by rfl) ⟨176892, by rfl⟩ : syracuseStep 471713 = 353785) B353785
theorem B799409 : Blo 311834 799409 := bstep (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) B599557
theorem B471731 : Blo 311834 471731 := bstep (se 1 (by rfl) ⟨353798, by rfl⟩ : syracuseStep 471731 = 707597) B707597
theorem B471761 : Blo 311834 471761 := bstep (se 2 (by rfl) ⟨176910, by rfl⟩ : syracuseStep 471761 = 353821) B353821
theorem B1061585 : Blo 311834 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B471779 : Blo 311834 471779 := bstep (se 1 (by rfl) ⟨353834, by rfl⟩ : syracuseStep 471779 = 707669) B707669
theorem B471809 : Blo 311834 471809 := bstep (se 2 (by rfl) ⟨176928, by rfl⟩ : syracuseStep 471809 = 353857) B353857
theorem B471827 : Blo 311834 471827 := bstep (se 1 (by rfl) ⟨353870, by rfl⟩ : syracuseStep 471827 = 707741) B707741
theorem B471857 : Blo 311834 471857 := bstep (se 2 (by rfl) ⟨176946, by rfl⟩ : syracuseStep 471857 = 353893) B353893
theorem B471875 : Blo 311834 471875 := bstep (se 1 (by rfl) ⟨353906, by rfl⟩ : syracuseStep 471875 = 707813) B707813
theorem B471905 : Blo 311834 471905 := bstep (se 2 (by rfl) ⟨176964, by rfl⟩ : syracuseStep 471905 = 353929) B353929
theorem B471923 : Blo 311834 471923 := bstep (se 1 (by rfl) ⟨353942, by rfl⟩ : syracuseStep 471923 = 707885) B707885
theorem B471953 : Blo 311834 471953 := bstep (se 2 (by rfl) ⟨176982, by rfl⟩ : syracuseStep 471953 = 353965) B353965
theorem B471971 : Blo 311834 471971 := bstep (se 1 (by rfl) ⟨353978, by rfl⟩ : syracuseStep 471971 = 707957) B707957
theorem B472001 : Blo 311834 472001 := bstep (se 2 (by rfl) ⟨177000, by rfl⟩ : syracuseStep 472001 = 354001) B354001
theorem B472019 : Blo 311834 472019 := bstep (se 1 (by rfl) ⟨354014, by rfl⟩ : syracuseStep 472019 = 708029) B708029
theorem B1782769 : Blo 311834 1782769 := bstep (se 2 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 1782769 = 1337077) B1337077
theorem B472049 : Blo 311834 472049 := bstep (se 2 (by rfl) ⟨177018, by rfl⟩ : syracuseStep 472049 = 354037) B354037
theorem B537587 : Blo 311834 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B472067 : Blo 311834 472067 := bstep (se 1 (by rfl) ⟨354050, by rfl⟩ : syracuseStep 472067 = 708101) B708101
theorem B472097 : Blo 311834 472097 := bstep (se 2 (by rfl) ⟨177036, by rfl⟩ : syracuseStep 472097 = 354073) B354073
theorem B472115 : Blo 311834 472115 := bstep (se 1 (by rfl) ⟨354086, by rfl⟩ : syracuseStep 472115 = 708173) B708173
theorem B472145 : Blo 311834 472145 := bstep (se 2 (by rfl) ⟨177054, by rfl⟩ : syracuseStep 472145 = 354109) B354109
theorem B472163 : Blo 311834 472163 := bstep (se 1 (by rfl) ⟨354122, by rfl⟩ : syracuseStep 472163 = 708245) B708245
theorem B472193 : Blo 311834 472193 := bstep (se 2 (by rfl) ⟨177072, by rfl⟩ : syracuseStep 472193 = 354145) B354145
theorem B472211 : Blo 311834 472211 := bstep (se 1 (by rfl) ⟨354158, by rfl⟩ : syracuseStep 472211 = 708317) B708317
theorem B472241 : Blo 311834 472241 := bstep (se 2 (by rfl) ⟨177090, by rfl⟩ : syracuseStep 472241 = 354181) B354181
theorem B472259 : Blo 311834 472259 := bstep (se 1 (by rfl) ⟨354194, by rfl⟩ : syracuseStep 472259 = 708389) B708389
theorem B3585221 : Blo 311834 3585221 := bstep (se 4 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 3585221 = 672229) B672229
theorem B472289 : Blo 311834 472289 := bstep (se 2 (by rfl) ⟨177108, by rfl⟩ : syracuseStep 472289 = 354217) B354217
theorem B505057 : Blo 311834 505057 := bstep (se 2 (by rfl) ⟨189396, by rfl⟩ : syracuseStep 505057 = 378793) B378793
theorem B1062125 : Blo 311834 1062125 := bstep (se 3 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 1062125 = 398297) B398297
theorem B472307 : Blo 311834 472307 := bstep (se 1 (by rfl) ⟨354230, by rfl⟩ : syracuseStep 472307 = 708461) B708461
theorem B472337 : Blo 311834 472337 := bstep (se 2 (by rfl) ⟨177126, by rfl⟩ : syracuseStep 472337 = 354253) B354253
theorem B1193251 : Blo 311834 1193251 := bstep (se 1 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 1193251 = 1789877) B1789877
theorem B1062179 : Blo 311834 1062179 := bstep (se 1 (by rfl) ⟨796634, by rfl⟩ : syracuseStep 1062179 = 1593269) B1593269
theorem B472355 : Blo 311834 472355 := bstep (se 1 (by rfl) ⟨354266, by rfl⟩ : syracuseStep 472355 = 708533) B708533
theorem B472385 : Blo 311834 472385 := bstep (se 2 (by rfl) ⟨177144, by rfl⟩ : syracuseStep 472385 = 354289) B354289
theorem B2012485 : Blo 311834 2012485 := bstep (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) B377341
theorem B472403 : Blo 311834 472403 := bstep (se 1 (by rfl) ⟨354302, by rfl⟩ : syracuseStep 472403 = 708605) B708605
theorem B537953 : Blo 311834 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B4502897 : Blo 311834 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B472433 : Blo 311834 472433 := bstep (se 2 (by rfl) ⟨177162, by rfl⟩ : syracuseStep 472433 = 354325) B354325
theorem B472451 : Blo 311834 472451 := bstep (se 1 (by rfl) ⟨354338, by rfl⟩ : syracuseStep 472451 = 708677) B708677
theorem B472481 : Blo 311834 472481 := bstep (se 2 (by rfl) ⟨177180, by rfl⟩ : syracuseStep 472481 = 354361) B354361
theorem B701873 : Blo 311834 701873 := bstep (se 2 (by rfl) ⟨263202, by rfl⟩ : syracuseStep 701873 = 526405) B526405
theorem B472499 : Blo 311834 472499 := bstep (se 1 (by rfl) ⟨354374, by rfl⟩ : syracuseStep 472499 = 708749) B708749
theorem B701891 : Blo 311834 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B472529 : Blo 311834 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B472547 : Blo 311834 472547 := bstep (se 1 (by rfl) ⟨354410, by rfl⟩ : syracuseStep 472547 = 708821) B708821
theorem B472577 : Blo 311834 472577 := bstep (se 2 (by rfl) ⟨177216, by rfl⟩ : syracuseStep 472577 = 354433) B354433
theorem B898573 : Blo 311834 898573 := bstep (se 3 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 898573 = 336965) B336965
theorem B472595 : Blo 311834 472595 := bstep (se 1 (by rfl) ⟨354446, by rfl⟩ : syracuseStep 472595 = 708893) B708893
theorem B1062449 : Blo 311834 1062449 := bstep (se 2 (by rfl) ⟨398418, by rfl⟩ : syracuseStep 1062449 = 796837) B796837
theorem B472625 : Blo 311834 472625 := bstep (se 2 (by rfl) ⟨177234, by rfl⟩ : syracuseStep 472625 = 354469) B354469
theorem B472643 : Blo 311834 472643 := bstep (se 1 (by rfl) ⟨354482, by rfl⟩ : syracuseStep 472643 = 708965) B708965
theorem B472673 : Blo 311834 472673 := bstep (se 2 (by rfl) ⟨177252, by rfl⟩ : syracuseStep 472673 = 354505) B354505
theorem B472691 : Blo 311834 472691 := bstep (se 1 (by rfl) ⟨354518, by rfl⟩ : syracuseStep 472691 = 709037) B709037
theorem B964237 : Blo 311834 964237 := bstep (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) B361589
theorem B472721 : Blo 311834 472721 := bstep (se 2 (by rfl) ⟨177270, by rfl⟩ : syracuseStep 472721 = 354541) B354541
theorem B505505 : Blo 311834 505505 := bstep (se 2 (by rfl) ⟨189564, by rfl⟩ : syracuseStep 505505 = 379129) B379129
theorem B472739 : Blo 311834 472739 := bstep (se 1 (by rfl) ⟨354554, by rfl⟩ : syracuseStep 472739 = 709109) B709109
theorem B472769 : Blo 311834 472769 := bstep (se 2 (by rfl) ⟨177288, by rfl⟩ : syracuseStep 472769 = 354577) B354577
theorem B702161 : Blo 311834 702161 := bstep (se 2 (by rfl) ⟨263310, by rfl⟩ : syracuseStep 702161 = 526621) B526621
theorem B472787 : Blo 311834 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B702179 : Blo 311834 702179 := bstep (se 1 (by rfl) ⟨526634, by rfl⟩ : syracuseStep 702179 = 1053269) B1053269
theorem B472817 : Blo 311834 472817 := bstep (se 2 (by rfl) ⟨177306, by rfl⟩ : syracuseStep 472817 = 354613) B354613
theorem B472835 : Blo 311834 472835 := bstep (se 1 (by rfl) ⟨354626, by rfl⟩ : syracuseStep 472835 = 709253) B709253
theorem B472865 : Blo 311834 472865 := bstep (se 2 (by rfl) ⟨177324, by rfl⟩ : syracuseStep 472865 = 354649) B354649
theorem B472883 : Blo 311834 472883 := bstep (se 1 (by rfl) ⟨354662, by rfl⟩ : syracuseStep 472883 = 709325) B709325
theorem B472913 : Blo 311834 472913 := bstep (se 2 (by rfl) ⟨177342, by rfl⟩ : syracuseStep 472913 = 354685) B354685
theorem B472931 : Blo 311834 472931 := bstep (se 1 (by rfl) ⟨354698, by rfl⟩ : syracuseStep 472931 = 709397) B709397
theorem B1128305 : Blo 311834 1128305 := bstep (se 2 (by rfl) ⟨423114, by rfl⟩ : syracuseStep 1128305 = 846229) B846229
theorem B472961 : Blo 311834 472961 := bstep (se 2 (by rfl) ⟨177360, by rfl⟩ : syracuseStep 472961 = 354721) B354721
theorem B472979 : Blo 311834 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B473009 : Blo 311834 473009 := bstep (se 2 (by rfl) ⟨177378, by rfl⟩ : syracuseStep 473009 = 354757) B354757
theorem B473027 : Blo 311834 473027 := bstep (se 1 (by rfl) ⟨354770, by rfl⟩ : syracuseStep 473027 = 709541) B709541
theorem B473057 : Blo 311834 473057 := bstep (se 2 (by rfl) ⟨177396, by rfl⟩ : syracuseStep 473057 = 354793) B354793
theorem B669667 : Blo 311834 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B702449 : Blo 311834 702449 := bstep (se 2 (by rfl) ⟨263418, by rfl⟩ : syracuseStep 702449 = 526837) B526837
theorem B473075 : Blo 311834 473075 := bstep (se 1 (by rfl) ⟨354806, by rfl⟩ : syracuseStep 473075 = 709613) B709613
theorem B702467 : Blo 311834 702467 := bstep (se 1 (by rfl) ⟨526850, by rfl⟩ : syracuseStep 702467 = 1053701) B1053701
theorem B473105 : Blo 311834 473105 := bstep (se 2 (by rfl) ⟨177414, by rfl⟩ : syracuseStep 473105 = 354829) B354829
theorem B473123 : Blo 311834 473123 := bstep (se 1 (by rfl) ⟨354842, by rfl⟩ : syracuseStep 473123 = 709685) B709685
theorem B473153 : Blo 311834 473153 := bstep (se 2 (by rfl) ⟨177432, by rfl⟩ : syracuseStep 473153 = 354865) B354865
theorem B1062989 : Blo 311834 1062989 := bstep (se 3 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 1062989 = 398621) B398621
theorem B473171 : Blo 311834 473171 := bstep (se 1 (by rfl) ⟨354878, by rfl⟩ : syracuseStep 473171 = 709757) B709757
theorem B473201 : Blo 311834 473201 := bstep (se 2 (by rfl) ⟨177450, by rfl⟩ : syracuseStep 473201 = 354901) B354901
theorem B1063043 : Blo 311834 1063043 := bstep (se 1 (by rfl) ⟨797282, by rfl⟩ : syracuseStep 1063043 = 1594565) B1594565
theorem B473219 : Blo 311834 473219 := bstep (se 1 (by rfl) ⟨354914, by rfl⟩ : syracuseStep 473219 = 709829) B709829
theorem B473249 : Blo 311834 473249 := bstep (se 2 (by rfl) ⟨177468, by rfl⟩ : syracuseStep 473249 = 354937) B354937
theorem B473267 : Blo 311834 473267 := bstep (se 1 (by rfl) ⟨354950, by rfl⟩ : syracuseStep 473267 = 709901) B709901
theorem B1128653 : Blo 311834 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B473297 : Blo 311834 473297 := bstep (se 2 (by rfl) ⟨177486, by rfl⟩ : syracuseStep 473297 = 354973) B354973
theorem B473315 : Blo 311834 473315 := bstep (se 1 (by rfl) ⟨354986, by rfl⟩ : syracuseStep 473315 = 709973) B709973
theorem B473345 : Blo 311834 473345 := bstep (se 2 (by rfl) ⟨177504, by rfl⟩ : syracuseStep 473345 = 355009) B355009
theorem B702737 : Blo 311834 702737 := bstep (se 2 (by rfl) ⟨263526, by rfl⟩ : syracuseStep 702737 = 527053) B527053
theorem B473363 : Blo 311834 473363 := bstep (se 1 (by rfl) ⟨355022, by rfl⟩ : syracuseStep 473363 = 710045) B710045
theorem B702755 : Blo 311834 702755 := bstep (se 1 (by rfl) ⟨527066, by rfl⟩ : syracuseStep 702755 = 1054133) B1054133
theorem B473393 : Blo 311834 473393 := bstep (se 2 (by rfl) ⟨177522, by rfl⟩ : syracuseStep 473393 = 355045) B355045
theorem B473411 : Blo 311834 473411 := bstep (se 1 (by rfl) ⟨355058, by rfl⟩ : syracuseStep 473411 = 710117) B710117
theorem B473441 : Blo 311834 473441 := bstep (se 2 (by rfl) ⟨177540, by rfl⟩ : syracuseStep 473441 = 355081) B355081
theorem B637283 : Blo 311834 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B473459 : Blo 311834 473459 := bstep (se 1 (by rfl) ⟨355094, by rfl⟩ : syracuseStep 473459 = 710189) B710189
theorem B1063313 : Blo 311834 1063313 := bstep (se 2 (by rfl) ⟨398742, by rfl⟩ : syracuseStep 1063313 = 797485) B797485
theorem B473489 : Blo 311834 473489 := bstep (se 2 (by rfl) ⟨177558, by rfl⟩ : syracuseStep 473489 = 355117) B355117
theorem B1784227 : Blo 311834 1784227 := bstep (se 1 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 1784227 = 2676341) B2676341
theorem B473507 : Blo 311834 473507 := bstep (se 1 (by rfl) ⟨355130, by rfl⟩ : syracuseStep 473507 = 710261) B710261
theorem B473537 : Blo 311834 473537 := bstep (se 2 (by rfl) ⟨177576, by rfl⟩ : syracuseStep 473537 = 355153) B355153
theorem B473555 : Blo 311834 473555 := bstep (se 1 (by rfl) ⟨355166, by rfl⟩ : syracuseStep 473555 = 710333) B710333
theorem B473585 : Blo 311834 473585 := bstep (se 2 (by rfl) ⟨177594, by rfl⟩ : syracuseStep 473585 = 355189) B355189
theorem B473603 : Blo 311834 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B473633 : Blo 311834 473633 := bstep (se 2 (by rfl) ⟨177612, by rfl⟩ : syracuseStep 473633 = 355225) B355225
theorem B703025 : Blo 311834 703025 := bstep (se 2 (by rfl) ⟨263634, by rfl⟩ : syracuseStep 703025 = 527269) B527269
theorem B1587761 : Blo 311834 1587761 := bstep (se 2 (by rfl) ⟨595410, by rfl⟩ : syracuseStep 1587761 = 1190821) B1190821
theorem B473651 : Blo 311834 473651 := bstep (se 1 (by rfl) ⟨355238, by rfl⟩ : syracuseStep 473651 = 710477) B710477
theorem B703043 : Blo 311834 703043 := bstep (se 1 (by rfl) ⟨527282, by rfl⟩ : syracuseStep 703043 = 1054565) B1054565
theorem B473681 : Blo 311834 473681 := bstep (se 2 (by rfl) ⟨177630, by rfl⟩ : syracuseStep 473681 = 355261) B355261
theorem B473699 : Blo 311834 473699 := bstep (se 1 (by rfl) ⟨355274, by rfl⟩ : syracuseStep 473699 = 710549) B710549
theorem B473729 : Blo 311834 473729 := bstep (se 2 (by rfl) ⟨177648, by rfl⟩ : syracuseStep 473729 = 355297) B355297
theorem B473747 : Blo 311834 473747 := bstep (se 1 (by rfl) ⟨355310, by rfl⟩ : syracuseStep 473747 = 710621) B710621
theorem B670513 : Blo 311834 670513 := bstep (se 2 (by rfl) ⟨251442, by rfl⟩ : syracuseStep 670513 = 502885) B502885
theorem B703313 : Blo 311834 703313 := bstep (se 2 (by rfl) ⟨263742, by rfl⟩ : syracuseStep 703313 = 527485) B527485
theorem B703331 : Blo 311834 703331 := bstep (se 1 (by rfl) ⟨527498, by rfl⟩ : syracuseStep 703331 = 1054997) B1054997
theorem B1063853 : Blo 311834 1063853 := bstep (se 3 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 1063853 = 398945) B398945
theorem B1784753 : Blo 311834 1784753 := bstep (se 2 (by rfl) ⟨669282, by rfl⟩ : syracuseStep 1784753 = 1338565) B1338565
theorem B1063907 : Blo 311834 1063907 := bstep (se 1 (by rfl) ⟨797930, by rfl⟩ : syracuseStep 1063907 = 1595861) B1595861
theorem B703601 : Blo 311834 703601 := bstep (se 2 (by rfl) ⟨263850, by rfl⟩ : syracuseStep 703601 = 527701) B527701
theorem B703619 : Blo 311834 703619 := bstep (se 1 (by rfl) ⟨527714, by rfl⟩ : syracuseStep 703619 = 1055429) B1055429
theorem B1064177 : Blo 311834 1064177 := bstep (se 2 (by rfl) ⟨399066, by rfl⟩ : syracuseStep 1064177 = 798133) B798133
theorem B703889 : Blo 311834 703889 := bstep (se 2 (by rfl) ⟨263958, by rfl⟩ : syracuseStep 703889 = 527917) B527917
theorem B540049 : Blo 311834 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B703907 : Blo 311834 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B1195469 : Blo 311834 1195469 := bstep (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) B448301
theorem B474641 : Blo 311834 474641 := bstep (se 2 (by rfl) ⟨177990, by rfl⟩ : syracuseStep 474641 = 355981) B355981
theorem B704177 : Blo 311834 704177 := bstep (se 2 (by rfl) ⟨264066, by rfl⟩ : syracuseStep 704177 = 528133) B528133
theorem B704195 : Blo 311834 704195 := bstep (se 1 (by rfl) ⟨528146, by rfl⟩ : syracuseStep 704195 = 1056293) B1056293
theorem B1064717 : Blo 311834 1064717 := bstep (se 3 (by rfl) ⟨199634, by rfl⟩ : syracuseStep 1064717 = 399269) B399269
theorem B1064771 : Blo 311834 1064771 := bstep (se 1 (by rfl) ⟨798578, by rfl⟩ : syracuseStep 1064771 = 1597157) B1597157
theorem B704465 : Blo 311834 704465 := bstep (se 2 (by rfl) ⟨264174, by rfl⟩ : syracuseStep 704465 = 528349) B528349
theorem B638929 : Blo 311834 638929 := bstep (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) B479197
theorem B704483 : Blo 311834 704483 := bstep (se 1 (by rfl) ⟨528362, by rfl⟩ : syracuseStep 704483 = 1056725) B1056725
theorem B1589219 : Blo 311834 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B2572273 : Blo 311834 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B1065041 : Blo 311834 1065041 := bstep (se 2 (by rfl) ⟨399390, by rfl⟩ : syracuseStep 1065041 = 798781) B798781
theorem B1818787 : Blo 311834 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B704753 : Blo 311834 704753 := bstep (se 2 (by rfl) ⟨264282, by rfl⟩ : syracuseStep 704753 = 528565) B528565
theorem B704771 : Blo 311834 704771 := bstep (se 1 (by rfl) ⟨528578, by rfl⟩ : syracuseStep 704771 = 1057157) B1057157
theorem B1786211 : Blo 311834 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B475505 : Blo 311834 475505 := bstep (se 2 (by rfl) ⟨178314, by rfl⟩ : syracuseStep 475505 = 356629) B356629
theorem B475553 : Blo 311834 475553 := bstep (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) B356665
theorem B705041 : Blo 311834 705041 := bstep (se 2 (by rfl) ⟨264390, by rfl⟩ : syracuseStep 705041 = 528781) B528781
theorem B311843 : Blo 311834 311843 := bstep (se 1 (by rfl) ⟨233882, by rfl⟩ : syracuseStep 311843 = 467765) B467765
theorem B705059 : Blo 311834 705059 := bstep (se 1 (by rfl) ⟨528794, by rfl⟩ : syracuseStep 705059 = 1057589) B1057589
theorem B311859 : Blo 311834 311859 := bstep (se 1 (by rfl) ⟨233894, by rfl⟩ : syracuseStep 311859 = 467789) B467789
theorem B311875 : Blo 311834 311875 := bstep (se 1 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 311875 = 467813) B467813
theorem B311891 : Blo 311834 311891 := bstep (se 1 (by rfl) ⟨233918, by rfl⟩ : syracuseStep 311891 = 467837) B467837
theorem B311907 : Blo 311834 311907 := bstep (se 1 (by rfl) ⟨233930, by rfl⟩ : syracuseStep 311907 = 467861) B467861
theorem B1065581 : Blo 311834 1065581 := bstep (se 3 (by rfl) ⟨199796, by rfl⟩ : syracuseStep 1065581 = 399593) B399593
theorem B2671217 : Blo 311834 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B311923 : Blo 311834 311923 := bstep (se 1 (by rfl) ⟨233942, by rfl⟩ : syracuseStep 311923 = 467885) B467885
theorem B311939 : Blo 311834 311939 := bstep (se 1 (by rfl) ⟨233954, by rfl⟩ : syracuseStep 311939 = 467909) B467909
theorem B672401 : Blo 311834 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B311955 : Blo 311834 311955 := bstep (se 1 (by rfl) ⟨233966, by rfl⟩ : syracuseStep 311955 = 467933) B467933
theorem B311971 : Blo 311834 311971 := bstep (se 1 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 311971 = 467957) B467957
theorem B1065635 : Blo 311834 1065635 := bstep (se 1 (by rfl) ⟨799226, by rfl⟩ : syracuseStep 1065635 = 1598453) B1598453
theorem B311987 : Blo 311834 311987 := bstep (se 1 (by rfl) ⟨233990, by rfl⟩ : syracuseStep 311987 = 467981) B467981
theorem B312003 : Blo 311834 312003 := bstep (se 1 (by rfl) ⟨234002, by rfl⟩ : syracuseStep 312003 = 468005) B468005
theorem B312019 : Blo 311834 312019 := bstep (se 1 (by rfl) ⟨234014, by rfl⟩ : syracuseStep 312019 = 468029) B468029
theorem B312035 : Blo 311834 312035 := bstep (se 1 (by rfl) ⟨234026, by rfl⟩ : syracuseStep 312035 = 468053) B468053
theorem B312051 : Blo 311834 312051 := bstep (se 1 (by rfl) ⟨234038, by rfl⟩ : syracuseStep 312051 = 468077) B468077
theorem B312067 : Blo 311834 312067 := bstep (se 1 (by rfl) ⟨234050, by rfl⟩ : syracuseStep 312067 = 468101) B468101
theorem B1590029 : Blo 311834 1590029 := bstep (se 3 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 1590029 = 596261) B596261
theorem B312083 : Blo 311834 312083 := bstep (se 1 (by rfl) ⟨234062, by rfl⟩ : syracuseStep 312083 = 468125) B468125
theorem B312099 : Blo 311834 312099 := bstep (se 1 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 312099 = 468149) B468149
theorem B705329 : Blo 311834 705329 := bstep (se 2 (by rfl) ⟨264498, by rfl⟩ : syracuseStep 705329 = 528997) B528997
theorem B2016049 : Blo 311834 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B312115 : Blo 311834 312115 := bstep (se 1 (by rfl) ⟨234086, by rfl⟩ : syracuseStep 312115 = 468173) B468173
theorem B312131 : Blo 311834 312131 := bstep (se 1 (by rfl) ⟨234098, by rfl⟩ : syracuseStep 312131 = 468197) B468197
theorem B705347 : Blo 311834 705347 := bstep (se 1 (by rfl) ⟨529010, by rfl⟩ : syracuseStep 705347 = 1058021) B1058021
theorem B312147 : Blo 311834 312147 := bstep (se 1 (by rfl) ⟨234110, by rfl⟩ : syracuseStep 312147 = 468221) B468221
theorem B312163 : Blo 311834 312163 := bstep (se 1 (by rfl) ⟨234122, by rfl⟩ : syracuseStep 312163 = 468245) B468245
theorem B1622897 : Blo 311834 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B312179 : Blo 311834 312179 := bstep (se 1 (by rfl) ⟨234134, by rfl⟩ : syracuseStep 312179 = 468269) B468269
theorem B312195 : Blo 311834 312195 := bstep (se 1 (by rfl) ⟨234146, by rfl⟩ : syracuseStep 312195 = 468293) B468293
theorem B312211 : Blo 311834 312211 := bstep (se 1 (by rfl) ⟨234158, by rfl⟩ : syracuseStep 312211 = 468317) B468317
theorem B312227 : Blo 311834 312227 := bstep (se 1 (by rfl) ⟨234170, by rfl⟩ : syracuseStep 312227 = 468341) B468341
theorem B1065905 : Blo 311834 1065905 := bstep (se 2 (by rfl) ⟨399714, by rfl⟩ : syracuseStep 1065905 = 799429) B799429
theorem B312243 : Blo 311834 312243 := bstep (se 1 (by rfl) ⟨234182, by rfl⟩ : syracuseStep 312243 = 468365) B468365
theorem B377779 : Blo 311834 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B312259 : Blo 311834 312259 := bstep (se 1 (by rfl) ⟨234194, by rfl⟩ : syracuseStep 312259 = 468389) B468389
theorem B312275 : Blo 311834 312275 := bstep (se 1 (by rfl) ⟨234206, by rfl⟩ : syracuseStep 312275 = 468413) B468413
theorem B312291 : Blo 311834 312291 := bstep (se 1 (by rfl) ⟨234218, by rfl⟩ : syracuseStep 312291 = 468437) B468437
theorem B312307 : Blo 311834 312307 := bstep (se 1 (by rfl) ⟨234230, by rfl⟩ : syracuseStep 312307 = 468461) B468461
theorem B1000451 : Blo 311834 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B312323 : Blo 311834 312323 := bstep (se 1 (by rfl) ⟨234242, by rfl⟩ : syracuseStep 312323 = 468485) B468485
theorem B312339 : Blo 311834 312339 := bstep (se 1 (by rfl) ⟨234254, by rfl⟩ : syracuseStep 312339 = 468509) B468509
theorem B312355 : Blo 311834 312355 := bstep (se 1 (by rfl) ⟨234266, by rfl⟩ : syracuseStep 312355 = 468533) B468533
theorem B312371 : Blo 311834 312371 := bstep (se 1 (by rfl) ⟨234278, by rfl⟩ : syracuseStep 312371 = 468557) B468557
theorem B312387 : Blo 311834 312387 := bstep (se 1 (by rfl) ⟨234290, by rfl⟩ : syracuseStep 312387 = 468581) B468581
theorem B705617 : Blo 311834 705617 := bstep (se 2 (by rfl) ⟨264606, by rfl⟩ : syracuseStep 705617 = 529213) B529213
theorem B312403 : Blo 311834 312403 := bstep (se 1 (by rfl) ⟨234302, by rfl⟩ : syracuseStep 312403 = 468605) B468605
theorem B312419 : Blo 311834 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B705635 : Blo 311834 705635 := bstep (se 1 (by rfl) ⟨529226, by rfl⟩ : syracuseStep 705635 = 1058453) B1058453
theorem B1131619 : Blo 311834 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B312435 : Blo 311834 312435 := bstep (se 1 (by rfl) ⟨234326, by rfl⟩ : syracuseStep 312435 = 468653) B468653
theorem B312451 : Blo 311834 312451 := bstep (se 1 (by rfl) ⟨234338, by rfl⟩ : syracuseStep 312451 = 468677) B468677
theorem B312467 : Blo 311834 312467 := bstep (se 1 (by rfl) ⟨234350, by rfl⟩ : syracuseStep 312467 = 468701) B468701
theorem B312483 : Blo 311834 312483 := bstep (se 1 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 312483 = 468725) B468725
theorem B607409 : Blo 311834 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B312499 : Blo 311834 312499 := bstep (se 1 (by rfl) ⟨234374, by rfl⟩ : syracuseStep 312499 = 468749) B468749
theorem B312515 : Blo 311834 312515 := bstep (se 1 (by rfl) ⟨234386, by rfl⟩ : syracuseStep 312515 = 468773) B468773
theorem B3032261 : Blo 311834 3032261 := bstep (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) B568549
theorem B312531 : Blo 311834 312531 := bstep (se 1 (by rfl) ⟨234398, by rfl⟩ : syracuseStep 312531 = 468797) B468797
theorem B312547 : Blo 311834 312547 := bstep (se 1 (by rfl) ⟨234410, by rfl⟩ : syracuseStep 312547 = 468821) B468821
theorem B1524977 : Blo 311834 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B312563 : Blo 311834 312563 := bstep (se 1 (by rfl) ⟨234422, by rfl⟩ : syracuseStep 312563 = 468845) B468845
theorem B312579 : Blo 311834 312579 := bstep (se 1 (by rfl) ⟨234434, by rfl⟩ : syracuseStep 312579 = 468869) B468869
theorem B312595 : Blo 311834 312595 := bstep (se 1 (by rfl) ⟨234446, by rfl⟩ : syracuseStep 312595 = 468893) B468893
theorem B312611 : Blo 311834 312611 := bstep (se 1 (by rfl) ⟨234458, by rfl⟩ : syracuseStep 312611 = 468917) B468917
theorem B312627 : Blo 311834 312627 := bstep (se 1 (by rfl) ⟨234470, by rfl⟩ : syracuseStep 312627 = 468941) B468941
theorem B312643 : Blo 311834 312643 := bstep (se 1 (by rfl) ⟨234482, by rfl⟩ : syracuseStep 312643 = 468965) B468965
theorem B312659 : Blo 311834 312659 := bstep (se 1 (by rfl) ⟨234494, by rfl⟩ : syracuseStep 312659 = 468989) B468989
theorem B312675 : Blo 311834 312675 := bstep (se 1 (by rfl) ⟨234506, by rfl⟩ : syracuseStep 312675 = 469013) B469013
theorem B705905 : Blo 311834 705905 := bstep (se 2 (by rfl) ⟨264714, by rfl⟩ : syracuseStep 705905 = 529429) B529429
theorem B312691 : Blo 311834 312691 := bstep (se 1 (by rfl) ⟨234518, by rfl⟩ : syracuseStep 312691 = 469037) B469037
theorem B312707 : Blo 311834 312707 := bstep (se 1 (by rfl) ⟨234530, by rfl⟩ : syracuseStep 312707 = 469061) B469061
theorem B705923 : Blo 311834 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B1000849 : Blo 311834 1000849 := bstep (se 2 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 1000849 = 750637) B750637
theorem B312723 : Blo 311834 312723 := bstep (se 1 (by rfl) ⟨234542, by rfl⟩ : syracuseStep 312723 = 469085) B469085
theorem B312739 : Blo 311834 312739 := bstep (se 1 (by rfl) ⟨234554, by rfl⟩ : syracuseStep 312739 = 469109) B469109
theorem B312755 : Blo 311834 312755 := bstep (se 1 (by rfl) ⟨234566, by rfl⟩ : syracuseStep 312755 = 469133) B469133
theorem B312771 : Blo 311834 312771 := bstep (se 1 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 312771 = 469157) B469157
theorem B312787 : Blo 311834 312787 := bstep (se 1 (by rfl) ⟨234590, by rfl⟩ : syracuseStep 312787 = 469181) B469181
theorem B312803 : Blo 311834 312803 := bstep (se 1 (by rfl) ⟨234602, by rfl⟩ : syracuseStep 312803 = 469205) B469205
theorem B312819 : Blo 311834 312819 := bstep (se 1 (by rfl) ⟨234614, by rfl⟩ : syracuseStep 312819 = 469229) B469229
theorem B312835 : Blo 311834 312835 := bstep (se 1 (by rfl) ⟨234626, by rfl⟩ : syracuseStep 312835 = 469253) B469253
theorem B312851 : Blo 311834 312851 := bstep (se 1 (by rfl) ⟨234638, by rfl⟩ : syracuseStep 312851 = 469277) B469277
theorem B312867 : Blo 311834 312867 := bstep (se 1 (by rfl) ⟨234650, by rfl⟩ : syracuseStep 312867 = 469301) B469301
theorem B312883 : Blo 311834 312883 := bstep (se 1 (by rfl) ⟨234662, by rfl⟩ : syracuseStep 312883 = 469325) B469325
theorem B312899 : Blo 311834 312899 := bstep (se 1 (by rfl) ⟨234674, by rfl⟩ : syracuseStep 312899 = 469349) B469349
theorem B312915 : Blo 311834 312915 := bstep (se 1 (by rfl) ⟨234686, by rfl⟩ : syracuseStep 312915 = 469373) B469373
theorem B312931 : Blo 311834 312931 := bstep (se 1 (by rfl) ⟨234698, by rfl⟩ : syracuseStep 312931 = 469397) B469397
theorem B312947 : Blo 311834 312947 := bstep (se 1 (by rfl) ⟨234710, by rfl⟩ : syracuseStep 312947 = 469421) B469421
theorem B312963 : Blo 311834 312963 := bstep (se 1 (by rfl) ⟨234722, by rfl⟩ : syracuseStep 312963 = 469445) B469445
theorem B706193 : Blo 311834 706193 := bstep (se 2 (by rfl) ⟨264822, by rfl⟩ : syracuseStep 706193 = 529645) B529645
theorem B312979 : Blo 311834 312979 := bstep (se 1 (by rfl) ⟨234734, by rfl⟩ : syracuseStep 312979 = 469469) B469469
theorem B312995 : Blo 311834 312995 := bstep (se 1 (by rfl) ⟨234746, by rfl⟩ : syracuseStep 312995 = 469493) B469493
theorem B706211 : Blo 311834 706211 := bstep (se 1 (by rfl) ⟨529658, by rfl⟩ : syracuseStep 706211 = 1059317) B1059317
theorem B313011 : Blo 311834 313011 := bstep (se 1 (by rfl) ⟨234758, by rfl⟩ : syracuseStep 313011 = 469517) B469517
theorem B313027 : Blo 311834 313027 := bstep (se 1 (by rfl) ⟨234770, by rfl⟩ : syracuseStep 313027 = 469541) B469541
theorem B313043 : Blo 311834 313043 := bstep (se 1 (by rfl) ⟨234782, by rfl⟩ : syracuseStep 313043 = 469565) B469565
theorem B313059 : Blo 311834 313059 := bstep (se 1 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 313059 = 469589) B469589
theorem B313075 : Blo 311834 313075 := bstep (se 1 (by rfl) ⟨234806, by rfl⟩ : syracuseStep 313075 = 469613) B469613
theorem B313091 : Blo 311834 313091 := bstep (se 1 (by rfl) ⟨234818, by rfl⟩ : syracuseStep 313091 = 469637) B469637
theorem B313107 : Blo 311834 313107 := bstep (se 1 (by rfl) ⟨234830, by rfl⟩ : syracuseStep 313107 = 469661) B469661
theorem B313123 : Blo 311834 313123 := bstep (se 1 (by rfl) ⟨234842, by rfl⟩ : syracuseStep 313123 = 469685) B469685
theorem B476977 : Blo 311834 476977 := bstep (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) B357733
theorem B313139 : Blo 311834 313139 := bstep (se 1 (by rfl) ⟨234854, by rfl⟩ : syracuseStep 313139 = 469709) B469709
theorem B313155 : Blo 311834 313155 := bstep (se 1 (by rfl) ⟨234866, by rfl⟩ : syracuseStep 313155 = 469733) B469733
theorem B1001297 : Blo 311834 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B313171 : Blo 311834 313171 := bstep (se 1 (by rfl) ⟨234878, by rfl⟩ : syracuseStep 313171 = 469757) B469757
theorem B313187 : Blo 311834 313187 := bstep (se 1 (by rfl) ⟨234890, by rfl⟩ : syracuseStep 313187 = 469781) B469781
theorem B313203 : Blo 311834 313203 := bstep (se 1 (by rfl) ⟨234902, by rfl⟩ : syracuseStep 313203 = 469805) B469805
theorem B313219 : Blo 311834 313219 := bstep (se 1 (by rfl) ⟨234914, by rfl⟩ : syracuseStep 313219 = 469829) B469829
theorem B313235 : Blo 311834 313235 := bstep (se 1 (by rfl) ⟨234926, by rfl⟩ : syracuseStep 313235 = 469853) B469853
theorem B313251 : Blo 311834 313251 := bstep (se 1 (by rfl) ⟨234938, by rfl⟩ : syracuseStep 313251 = 469877) B469877
theorem B673699 : Blo 311834 673699 := bstep (se 1 (by rfl) ⟨505274, by rfl⟩ : syracuseStep 673699 = 1010549) B1010549
theorem B706481 : Blo 311834 706481 := bstep (se 2 (by rfl) ⟨264930, by rfl⟩ : syracuseStep 706481 = 529861) B529861
theorem B313267 : Blo 311834 313267 := bstep (se 1 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 313267 = 469901) B469901
theorem B313283 : Blo 311834 313283 := bstep (se 1 (by rfl) ⟨234962, by rfl⟩ : syracuseStep 313283 = 469925) B469925
theorem B706499 : Blo 311834 706499 := bstep (se 1 (by rfl) ⟨529874, by rfl⟩ : syracuseStep 706499 = 1059749) B1059749
theorem B346051 : Blo 311834 346051 := bstep (se 1 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 346051 = 519077) B519077
theorem B444371 : Blo 311834 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B313299 : Blo 311834 313299 := bstep (se 1 (by rfl) ⟨234974, by rfl⟩ : syracuseStep 313299 = 469949) B469949
theorem B313315 : Blo 311834 313315 := bstep (se 1 (by rfl) ⟨234986, by rfl⟩ : syracuseStep 313315 = 469973) B469973
theorem B313331 : Blo 311834 313331 := bstep (se 1 (by rfl) ⟨234998, by rfl⟩ : syracuseStep 313331 = 469997) B469997
theorem B313347 : Blo 311834 313347 := bstep (se 1 (by rfl) ⟨235010, by rfl⟩ : syracuseStep 313347 = 470021) B470021
theorem B313363 : Blo 311834 313363 := bstep (se 1 (by rfl) ⟨235022, by rfl⟩ : syracuseStep 313363 = 470045) B470045
theorem B313379 : Blo 311834 313379 := bstep (se 1 (by rfl) ⟨235034, by rfl⟩ : syracuseStep 313379 = 470069) B470069
theorem B313395 : Blo 311834 313395 := bstep (se 1 (by rfl) ⟨235046, by rfl⟩ : syracuseStep 313395 = 470093) B470093
theorem B313411 : Blo 311834 313411 := bstep (se 1 (by rfl) ⟨235058, by rfl⟩ : syracuseStep 313411 = 470117) B470117
theorem B313427 : Blo 311834 313427 := bstep (se 1 (by rfl) ⟨235070, by rfl⟩ : syracuseStep 313427 = 470141) B470141
theorem B313443 : Blo 311834 313443 := bstep (se 1 (by rfl) ⟨235082, by rfl⟩ : syracuseStep 313443 = 470165) B470165
theorem B313459 : Blo 311834 313459 := bstep (se 1 (by rfl) ⟨235094, by rfl⟩ : syracuseStep 313459 = 470189) B470189
theorem B510067 : Blo 311834 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B313475 : Blo 311834 313475 := bstep (se 1 (by rfl) ⟨235106, by rfl⟩ : syracuseStep 313475 = 470213) B470213
theorem B313491 : Blo 311834 313491 := bstep (se 1 (by rfl) ⟨235118, by rfl⟩ : syracuseStep 313491 = 470237) B470237
theorem B313507 : Blo 311834 313507 := bstep (se 1 (by rfl) ⟨235130, by rfl⟩ : syracuseStep 313507 = 470261) B470261
theorem B2050211 : Blo 311834 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B313523 : Blo 311834 313523 := bstep (se 1 (by rfl) ⟨235142, by rfl⟩ : syracuseStep 313523 = 470285) B470285
theorem B313539 : Blo 311834 313539 := bstep (se 1 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 313539 = 470309) B470309
theorem B1788101 : Blo 311834 1788101 := bstep (se 4 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 1788101 = 335269) B335269
theorem B706769 : Blo 311834 706769 := bstep (se 2 (by rfl) ⟨265038, by rfl⟩ : syracuseStep 706769 = 530077) B530077
theorem B313555 : Blo 311834 313555 := bstep (se 1 (by rfl) ⟨235166, by rfl⟩ : syracuseStep 313555 = 470333) B470333
theorem B313571 : Blo 311834 313571 := bstep (se 1 (by rfl) ⟨235178, by rfl⟩ : syracuseStep 313571 = 470357) B470357
theorem B706787 : Blo 311834 706787 := bstep (se 1 (by rfl) ⟨530090, by rfl⟩ : syracuseStep 706787 = 1060181) B1060181
theorem B313587 : Blo 311834 313587 := bstep (se 1 (by rfl) ⟨235190, by rfl⟩ : syracuseStep 313587 = 470381) B470381
theorem B313603 : Blo 311834 313603 := bstep (se 1 (by rfl) ⟨235202, by rfl⟩ : syracuseStep 313603 = 470405) B470405
theorem B2377997 : Blo 311834 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B313619 : Blo 311834 313619 := bstep (se 1 (by rfl) ⟨235214, by rfl⟩ : syracuseStep 313619 = 470429) B470429
theorem B313635 : Blo 311834 313635 := bstep (se 1 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 313635 = 470453) B470453
theorem B1198385 : Blo 311834 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B313651 : Blo 311834 313651 := bstep (se 1 (by rfl) ⟨235238, by rfl⟩ : syracuseStep 313651 = 470477) B470477
theorem B313667 : Blo 311834 313667 := bstep (se 1 (by rfl) ⟨235250, by rfl⟩ : syracuseStep 313667 = 470501) B470501
theorem B313683 : Blo 311834 313683 := bstep (se 1 (by rfl) ⟨235262, by rfl⟩ : syracuseStep 313683 = 470525) B470525
theorem B313699 : Blo 311834 313699 := bstep (se 1 (by rfl) ⟨235274, by rfl⟩ : syracuseStep 313699 = 470549) B470549
theorem B313715 : Blo 311834 313715 := bstep (se 1 (by rfl) ⟨235286, by rfl⟩ : syracuseStep 313715 = 470573) B470573
theorem B313731 : Blo 311834 313731 := bstep (se 1 (by rfl) ⟨235298, by rfl⟩ : syracuseStep 313731 = 470597) B470597
theorem B313747 : Blo 311834 313747 := bstep (se 1 (by rfl) ⟨235310, by rfl⟩ : syracuseStep 313747 = 470621) B470621
theorem B313763 : Blo 311834 313763 := bstep (se 1 (by rfl) ⟨235322, by rfl⟩ : syracuseStep 313763 = 470645) B470645
theorem B313779 : Blo 311834 313779 := bstep (se 1 (by rfl) ⟨235334, by rfl⟩ : syracuseStep 313779 = 470669) B470669
theorem B313795 : Blo 311834 313795 := bstep (se 1 (by rfl) ⟨235346, by rfl⟩ : syracuseStep 313795 = 470693) B470693
theorem B313811 : Blo 311834 313811 := bstep (se 1 (by rfl) ⟨235358, by rfl⟩ : syracuseStep 313811 = 470717) B470717
theorem B313827 : Blo 311834 313827 := bstep (se 1 (by rfl) ⟨235370, by rfl⟩ : syracuseStep 313827 = 470741) B470741
theorem B707057 : Blo 311834 707057 := bstep (se 2 (by rfl) ⟨265146, by rfl⟩ : syracuseStep 707057 = 530293) B530293
theorem B313843 : Blo 311834 313843 := bstep (se 1 (by rfl) ⟨235382, by rfl⟩ : syracuseStep 313843 = 470765) B470765
theorem B313859 : Blo 311834 313859 := bstep (se 1 (by rfl) ⟨235394, by rfl⟩ : syracuseStep 313859 = 470789) B470789
theorem B707075 : Blo 311834 707075 := bstep (se 1 (by rfl) ⟨530306, by rfl⟩ : syracuseStep 707075 = 1060613) B1060613
theorem B313875 : Blo 311834 313875 := bstep (se 1 (by rfl) ⟨235406, by rfl⟩ : syracuseStep 313875 = 470813) B470813
theorem B313891 : Blo 311834 313891 := bstep (se 1 (by rfl) ⟨235418, by rfl⟩ : syracuseStep 313891 = 470837) B470837
theorem B313907 : Blo 311834 313907 := bstep (se 1 (by rfl) ⟨235430, by rfl⟩ : syracuseStep 313907 = 470861) B470861
theorem B313923 : Blo 311834 313923 := bstep (se 1 (by rfl) ⟨235442, by rfl⟩ : syracuseStep 313923 = 470885) B470885
theorem B445009 : Blo 311834 445009 := bstep (se 2 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 445009 = 333757) B333757
theorem B313939 : Blo 311834 313939 := bstep (se 1 (by rfl) ⟨235454, by rfl⟩ : syracuseStep 313939 = 470909) B470909
theorem B313955 : Blo 311834 313955 := bstep (se 1 (by rfl) ⟨235466, by rfl⟩ : syracuseStep 313955 = 470933) B470933
theorem B313971 : Blo 311834 313971 := bstep (se 1 (by rfl) ⟨235478, by rfl⟩ : syracuseStep 313971 = 470957) B470957
theorem B313987 : Blo 311834 313987 := bstep (se 1 (by rfl) ⟨235490, by rfl⟩ : syracuseStep 313987 = 470981) B470981
theorem B314003 : Blo 311834 314003 := bstep (se 1 (by rfl) ⟨235502, by rfl⟩ : syracuseStep 314003 = 471005) B471005
theorem B314019 : Blo 311834 314019 := bstep (se 1 (by rfl) ⟨235514, by rfl⟩ : syracuseStep 314019 = 471029) B471029
theorem B314035 : Blo 311834 314035 := bstep (se 1 (by rfl) ⟨235526, by rfl⟩ : syracuseStep 314035 = 471053) B471053
theorem B445123 : Blo 311834 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B314051 : Blo 311834 314051 := bstep (se 1 (by rfl) ⟨235538, by rfl⟩ : syracuseStep 314051 = 471077) B471077
theorem B314067 : Blo 311834 314067 := bstep (se 1 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 314067 = 471101) B471101
theorem B314083 : Blo 311834 314083 := bstep (se 1 (by rfl) ⟨235562, by rfl⟩ : syracuseStep 314083 = 471125) B471125
theorem B314099 : Blo 311834 314099 := bstep (se 1 (by rfl) ⟨235574, by rfl⟩ : syracuseStep 314099 = 471149) B471149
theorem B314115 : Blo 311834 314115 := bstep (se 1 (by rfl) ⟨235586, by rfl⟩ : syracuseStep 314115 = 471173) B471173
theorem B707345 : Blo 311834 707345 := bstep (se 2 (by rfl) ⟨265254, by rfl⟩ : syracuseStep 707345 = 530509) B530509
theorem B314131 : Blo 311834 314131 := bstep (se 1 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 314131 = 471197) B471197
theorem B314147 : Blo 311834 314147 := bstep (se 1 (by rfl) ⟨235610, by rfl⟩ : syracuseStep 314147 = 471221) B471221
theorem B707363 : Blo 311834 707363 := bstep (se 1 (by rfl) ⟨530522, by rfl⟩ : syracuseStep 707363 = 1061045) B1061045
theorem B314163 : Blo 311834 314163 := bstep (se 1 (by rfl) ⟨235622, by rfl⟩ : syracuseStep 314163 = 471245) B471245
theorem B314179 : Blo 311834 314179 := bstep (se 1 (by rfl) ⟨235634, by rfl⟩ : syracuseStep 314179 = 471269) B471269
theorem B314195 : Blo 311834 314195 := bstep (se 1 (by rfl) ⟨235646, by rfl⟩ : syracuseStep 314195 = 471293) B471293
theorem B314211 : Blo 311834 314211 := bstep (se 1 (by rfl) ⟨235658, by rfl⟩ : syracuseStep 314211 = 471317) B471317
theorem B314227 : Blo 311834 314227 := bstep (se 1 (by rfl) ⟨235670, by rfl⟩ : syracuseStep 314227 = 471341) B471341
theorem B314243 : Blo 311834 314243 := bstep (se 1 (by rfl) ⟨235682, by rfl⟩ : syracuseStep 314243 = 471365) B471365
theorem B3591053 : Blo 311834 3591053 := bstep (se 3 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 3591053 = 1346645) B1346645
theorem B314259 : Blo 311834 314259 := bstep (se 1 (by rfl) ⟨235694, by rfl⟩ : syracuseStep 314259 = 471389) B471389
theorem B314275 : Blo 311834 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B314291 : Blo 311834 314291 := bstep (se 1 (by rfl) ⟨235718, by rfl⟩ : syracuseStep 314291 = 471437) B471437
theorem B314307 : Blo 311834 314307 := bstep (se 1 (by rfl) ⟨235730, by rfl⟩ : syracuseStep 314307 = 471461) B471461
theorem B314323 : Blo 311834 314323 := bstep (se 1 (by rfl) ⟨235742, by rfl⟩ : syracuseStep 314323 = 471485) B471485
theorem B314339 : Blo 311834 314339 := bstep (se 1 (by rfl) ⟨235754, by rfl⟩ : syracuseStep 314339 = 471509) B471509
theorem B314355 : Blo 311834 314355 := bstep (se 1 (by rfl) ⟨235766, by rfl⟩ : syracuseStep 314355 = 471533) B471533
theorem B314371 : Blo 311834 314371 := bstep (se 1 (by rfl) ⟨235778, by rfl⟩ : syracuseStep 314371 = 471557) B471557
theorem B314387 : Blo 311834 314387 := bstep (se 1 (by rfl) ⟨235790, by rfl⟩ : syracuseStep 314387 = 471581) B471581
theorem B314403 : Blo 311834 314403 := bstep (se 1 (by rfl) ⟨235802, by rfl⟩ : syracuseStep 314403 = 471605) B471605
theorem B707633 : Blo 311834 707633 := bstep (se 2 (by rfl) ⟨265362, by rfl⟩ : syracuseStep 707633 = 530725) B530725
theorem B314419 : Blo 311834 314419 := bstep (se 1 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 314419 = 471629) B471629
theorem B314435 : Blo 311834 314435 := bstep (se 1 (by rfl) ⟨235826, by rfl⟩ : syracuseStep 314435 = 471653) B471653
theorem B707651 : Blo 311834 707651 := bstep (se 1 (by rfl) ⟨530738, by rfl⟩ : syracuseStep 707651 = 1061477) B1061477
theorem B314451 : Blo 311834 314451 := bstep (se 1 (by rfl) ⟨235838, by rfl⟩ : syracuseStep 314451 = 471677) B471677
theorem B314467 : Blo 311834 314467 := bstep (se 1 (by rfl) ⟨235850, by rfl⟩ : syracuseStep 314467 = 471701) B471701
theorem B314483 : Blo 311834 314483 := bstep (se 1 (by rfl) ⟨235862, by rfl⟩ : syracuseStep 314483 = 471725) B471725
theorem B314499 : Blo 311834 314499 := bstep (se 1 (by rfl) ⟨235874, by rfl⟩ : syracuseStep 314499 = 471749) B471749
theorem B314515 : Blo 311834 314515 := bstep (se 1 (by rfl) ⟨235886, by rfl⟩ : syracuseStep 314515 = 471773) B471773
theorem B314531 : Blo 311834 314531 := bstep (se 1 (by rfl) ⟨235898, by rfl⟩ : syracuseStep 314531 = 471797) B471797
theorem B314547 : Blo 311834 314547 := bstep (se 1 (by rfl) ⟨235910, by rfl⟩ : syracuseStep 314547 = 471821) B471821
theorem B314563 : Blo 311834 314563 := bstep (se 1 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 314563 = 471845) B471845
theorem B314579 : Blo 311834 314579 := bstep (se 1 (by rfl) ⟨235934, by rfl⟩ : syracuseStep 314579 = 471869) B471869
theorem B314595 : Blo 311834 314595 := bstep (se 1 (by rfl) ⟨235946, by rfl⟩ : syracuseStep 314595 = 471893) B471893
theorem B314611 : Blo 311834 314611 := bstep (se 1 (by rfl) ⟨235958, by rfl⟩ : syracuseStep 314611 = 471917) B471917
theorem B314627 : Blo 311834 314627 := bstep (se 1 (by rfl) ⟨235970, by rfl⟩ : syracuseStep 314627 = 471941) B471941
theorem B314643 : Blo 311834 314643 := bstep (se 1 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 314643 = 471965) B471965
theorem B314659 : Blo 311834 314659 := bstep (se 1 (by rfl) ⟨235994, by rfl⟩ : syracuseStep 314659 = 471989) B471989
theorem B314675 : Blo 311834 314675 := bstep (se 1 (by rfl) ⟨236006, by rfl⟩ : syracuseStep 314675 = 472013) B472013
theorem B314691 : Blo 311834 314691 := bstep (se 1 (by rfl) ⟨236018, by rfl⟩ : syracuseStep 314691 = 472037) B472037
theorem B707921 : Blo 311834 707921 := bstep (se 2 (by rfl) ⟨265470, by rfl⟩ : syracuseStep 707921 = 530941) B530941
theorem B314707 : Blo 311834 314707 := bstep (se 1 (by rfl) ⟨236030, by rfl⟩ : syracuseStep 314707 = 472061) B472061
theorem B707939 : Blo 311834 707939 := bstep (se 1 (by rfl) ⟨530954, by rfl⟩ : syracuseStep 707939 = 1061909) B1061909
theorem B314723 : Blo 311834 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B314739 : Blo 311834 314739 := bstep (se 1 (by rfl) ⟨236054, by rfl⟩ : syracuseStep 314739 = 472109) B472109
theorem B314755 : Blo 311834 314755 := bstep (se 1 (by rfl) ⟨236066, by rfl⟩ : syracuseStep 314755 = 472133) B472133
theorem B314771 : Blo 311834 314771 := bstep (se 1 (by rfl) ⟨236078, by rfl⟩ : syracuseStep 314771 = 472157) B472157
theorem B314787 : Blo 311834 314787 := bstep (se 1 (by rfl) ⟨236090, by rfl⟩ : syracuseStep 314787 = 472181) B472181
theorem B314803 : Blo 311834 314803 := bstep (se 1 (by rfl) ⟨236102, by rfl⟩ : syracuseStep 314803 = 472205) B472205
theorem B314819 : Blo 311834 314819 := bstep (se 1 (by rfl) ⟨236114, by rfl⟩ : syracuseStep 314819 = 472229) B472229
theorem B314835 : Blo 311834 314835 := bstep (se 1 (by rfl) ⟨236126, by rfl⟩ : syracuseStep 314835 = 472253) B472253
theorem B314851 : Blo 311834 314851 := bstep (se 1 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 314851 = 472277) B472277
theorem B314867 : Blo 311834 314867 := bstep (se 1 (by rfl) ⟨236150, by rfl⟩ : syracuseStep 314867 = 472301) B472301
theorem B314883 : Blo 311834 314883 := bstep (se 1 (by rfl) ⟨236162, by rfl⟩ : syracuseStep 314883 = 472325) B472325
theorem B314899 : Blo 311834 314899 := bstep (se 1 (by rfl) ⟨236174, by rfl⟩ : syracuseStep 314899 = 472349) B472349
theorem B314915 : Blo 311834 314915 := bstep (se 1 (by rfl) ⟨236186, by rfl⟩ : syracuseStep 314915 = 472373) B472373
theorem B314931 : Blo 311834 314931 := bstep (se 1 (by rfl) ⟨236198, by rfl⟩ : syracuseStep 314931 = 472397) B472397
theorem B314947 : Blo 311834 314947 := bstep (se 1 (by rfl) ⟨236210, by rfl⟩ : syracuseStep 314947 = 472421) B472421
theorem B1134157 : Blo 311834 1134157 := bstep (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) B425309
theorem B314963 : Blo 311834 314963 := bstep (se 1 (by rfl) ⟨236222, by rfl⟩ : syracuseStep 314963 = 472445) B472445
theorem B314979 : Blo 311834 314979 := bstep (se 1 (by rfl) ⟨236234, by rfl⟩ : syracuseStep 314979 = 472469) B472469
theorem B1592945 : Blo 311834 1592945 := bstep (se 2 (by rfl) ⟨597354, by rfl⟩ : syracuseStep 1592945 = 1194709) B1194709
theorem B708209 : Blo 311834 708209 := bstep (se 2 (by rfl) ⟨265578, by rfl⟩ : syracuseStep 708209 = 531157) B531157
theorem B314995 : Blo 311834 314995 := bstep (se 1 (by rfl) ⟨236246, by rfl⟩ : syracuseStep 314995 = 472493) B472493
theorem B708227 : Blo 311834 708227 := bstep (se 1 (by rfl) ⟨531170, by rfl⟩ : syracuseStep 708227 = 1062341) B1062341
theorem B315011 : Blo 311834 315011 := bstep (se 1 (by rfl) ⟨236258, by rfl⟩ : syracuseStep 315011 = 472517) B472517
theorem B315027 : Blo 311834 315027 := bstep (se 1 (by rfl) ⟨236270, by rfl⟩ : syracuseStep 315027 = 472541) B472541
theorem B315043 : Blo 311834 315043 := bstep (se 1 (by rfl) ⟨236282, by rfl⟩ : syracuseStep 315043 = 472565) B472565
theorem B315059 : Blo 311834 315059 := bstep (se 1 (by rfl) ⟨236294, by rfl⟩ : syracuseStep 315059 = 472589) B472589
theorem B315075 : Blo 311834 315075 := bstep (se 1 (by rfl) ⟨236306, by rfl⟩ : syracuseStep 315075 = 472613) B472613
theorem B315091 : Blo 311834 315091 := bstep (se 1 (by rfl) ⟨236318, by rfl⟩ : syracuseStep 315091 = 472637) B472637
theorem B315107 : Blo 311834 315107 := bstep (se 1 (by rfl) ⟨236330, by rfl⟩ : syracuseStep 315107 = 472661) B472661
theorem B315123 : Blo 311834 315123 := bstep (se 1 (by rfl) ⟨236342, by rfl⟩ : syracuseStep 315123 = 472685) B472685
theorem B315139 : Blo 311834 315139 := bstep (se 1 (by rfl) ⟨236354, by rfl⟩ : syracuseStep 315139 = 472709) B472709
theorem B315155 : Blo 311834 315155 := bstep (se 1 (by rfl) ⟨236366, by rfl⟩ : syracuseStep 315155 = 472733) B472733
theorem B479009 : Blo 311834 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B315171 : Blo 311834 315171 := bstep (se 1 (by rfl) ⟨236378, by rfl⟩ : syracuseStep 315171 = 472757) B472757
theorem B315187 : Blo 311834 315187 := bstep (se 1 (by rfl) ⟨236390, by rfl⟩ : syracuseStep 315187 = 472781) B472781
theorem B315203 : Blo 311834 315203 := bstep (se 1 (by rfl) ⟨236402, by rfl⟩ : syracuseStep 315203 = 472805) B472805
theorem B315219 : Blo 311834 315219 := bstep (se 1 (by rfl) ⟨236414, by rfl⟩ : syracuseStep 315219 = 472829) B472829
theorem B315235 : Blo 311834 315235 := bstep (se 1 (by rfl) ⟨236426, by rfl⟩ : syracuseStep 315235 = 472853) B472853
theorem B1003373 : Blo 311834 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B315251 : Blo 311834 315251 := bstep (se 1 (by rfl) ⟨236438, by rfl⟩ : syracuseStep 315251 = 472877) B472877
theorem B315267 : Blo 311834 315267 := bstep (se 1 (by rfl) ⟨236450, by rfl⟩ : syracuseStep 315267 = 472901) B472901
theorem B708497 : Blo 311834 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B315283 : Blo 311834 315283 := bstep (se 1 (by rfl) ⟨236462, by rfl⟩ : syracuseStep 315283 = 472925) B472925
theorem B708515 : Blo 311834 708515 := bstep (se 1 (by rfl) ⟨531386, by rfl⟩ : syracuseStep 708515 = 1062773) B1062773
theorem B315299 : Blo 311834 315299 := bstep (se 1 (by rfl) ⟨236474, by rfl⟩ : syracuseStep 315299 = 472949) B472949
theorem B315315 : Blo 311834 315315 := bstep (se 1 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 315315 = 472973) B472973
theorem B315331 : Blo 311834 315331 := bstep (se 1 (by rfl) ⟨236498, by rfl⟩ : syracuseStep 315331 = 472997) B472997
theorem B315347 : Blo 311834 315347 := bstep (se 1 (by rfl) ⟨236510, by rfl⟩ : syracuseStep 315347 = 473021) B473021
theorem B315363 : Blo 311834 315363 := bstep (se 1 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 315363 = 473045) B473045
theorem B315379 : Blo 311834 315379 := bstep (se 1 (by rfl) ⟨236534, by rfl⟩ : syracuseStep 315379 = 473069) B473069
theorem B446467 : Blo 311834 446467 := bstep (se 1 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 446467 = 669701) B669701
theorem B315395 : Blo 311834 315395 := bstep (se 1 (by rfl) ⟨236546, by rfl⟩ : syracuseStep 315395 = 473093) B473093
theorem B315411 : Blo 311834 315411 := bstep (se 1 (by rfl) ⟨236558, by rfl⟩ : syracuseStep 315411 = 473117) B473117
theorem B315427 : Blo 311834 315427 := bstep (se 1 (by rfl) ⟨236570, by rfl⟩ : syracuseStep 315427 = 473141) B473141
theorem B315443 : Blo 311834 315443 := bstep (se 1 (by rfl) ⟨236582, by rfl⟩ : syracuseStep 315443 = 473165) B473165
theorem B315459 : Blo 311834 315459 := bstep (se 1 (by rfl) ⟨236594, by rfl⟩ : syracuseStep 315459 = 473189) B473189
theorem B315475 : Blo 311834 315475 := bstep (se 1 (by rfl) ⟨236606, by rfl⟩ : syracuseStep 315475 = 473213) B473213
theorem B315491 : Blo 311834 315491 := bstep (se 1 (by rfl) ⟨236618, by rfl⟩ : syracuseStep 315491 = 473237) B473237
theorem B315507 : Blo 311834 315507 := bstep (se 1 (by rfl) ⟨236630, by rfl⟩ : syracuseStep 315507 = 473261) B473261
theorem B315523 : Blo 311834 315523 := bstep (se 1 (by rfl) ⟨236642, by rfl⟩ : syracuseStep 315523 = 473285) B473285
theorem B315539 : Blo 311834 315539 := bstep (se 1 (by rfl) ⟨236654, by rfl⟩ : syracuseStep 315539 = 473309) B473309
theorem B315555 : Blo 311834 315555 := bstep (se 1 (by rfl) ⟨236666, by rfl⟩ : syracuseStep 315555 = 473333) B473333
theorem B708785 : Blo 311834 708785 := bstep (se 2 (by rfl) ⟨265794, by rfl⟩ : syracuseStep 708785 = 531589) B531589
theorem B315571 : Blo 311834 315571 := bstep (se 1 (by rfl) ⟨236678, by rfl⟩ : syracuseStep 315571 = 473357) B473357
theorem B708803 : Blo 311834 708803 := bstep (se 1 (by rfl) ⟨531602, by rfl⟩ : syracuseStep 708803 = 1063205) B1063205
theorem B315587 : Blo 311834 315587 := bstep (se 1 (by rfl) ⟨236690, by rfl⟩ : syracuseStep 315587 = 473381) B473381
theorem B315603 : Blo 311834 315603 := bstep (se 1 (by rfl) ⟨236702, by rfl⟩ : syracuseStep 315603 = 473405) B473405
theorem B1069283 : Blo 311834 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B315619 : Blo 311834 315619 := bstep (se 1 (by rfl) ⟨236714, by rfl⟩ : syracuseStep 315619 = 473429) B473429
theorem B315635 : Blo 311834 315635 := bstep (se 1 (by rfl) ⟨236726, by rfl⟩ : syracuseStep 315635 = 473453) B473453
theorem B315651 : Blo 311834 315651 := bstep (se 1 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 315651 = 473477) B473477
theorem B315667 : Blo 311834 315667 := bstep (se 1 (by rfl) ⟨236750, by rfl⟩ : syracuseStep 315667 = 473501) B473501
theorem B315683 : Blo 311834 315683 := bstep (se 1 (by rfl) ⟨236762, by rfl⟩ : syracuseStep 315683 = 473525) B473525
theorem B315699 : Blo 311834 315699 := bstep (se 1 (by rfl) ⟨236774, by rfl⟩ : syracuseStep 315699 = 473549) B473549
theorem B315715 : Blo 311834 315715 := bstep (se 1 (by rfl) ⟨236786, by rfl⟩ : syracuseStep 315715 = 473573) B473573
theorem B315731 : Blo 311834 315731 := bstep (se 1 (by rfl) ⟨236798, by rfl⟩ : syracuseStep 315731 = 473597) B473597
theorem B315747 : Blo 311834 315747 := bstep (se 1 (by rfl) ⟨236810, by rfl⟩ : syracuseStep 315747 = 473621) B473621
theorem B315763 : Blo 311834 315763 := bstep (se 1 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 315763 = 473645) B473645
theorem B315779 : Blo 311834 315779 := bstep (se 1 (by rfl) ⟨236834, by rfl⟩ : syracuseStep 315779 = 473669) B473669
theorem B315795 : Blo 311834 315795 := bstep (se 1 (by rfl) ⟨236846, by rfl⟩ : syracuseStep 315795 = 473693) B473693
theorem B315811 : Blo 311834 315811 := bstep (se 1 (by rfl) ⟨236858, by rfl⟩ : syracuseStep 315811 = 473717) B473717
theorem B315827 : Blo 311834 315827 := bstep (se 1 (by rfl) ⟨236870, by rfl⟩ : syracuseStep 315827 = 473741) B473741
theorem B709073 : Blo 311834 709073 := bstep (se 2 (by rfl) ⟨265902, by rfl⟩ : syracuseStep 709073 = 531805) B531805
theorem B709091 : Blo 311834 709091 := bstep (se 1 (by rfl) ⟨531818, by rfl⟩ : syracuseStep 709091 = 1063637) B1063637
theorem B1069777 : Blo 311834 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B709361 : Blo 311834 709361 := bstep (se 2 (by rfl) ⟨266010, by rfl⟩ : syracuseStep 709361 = 532021) B532021
theorem B709379 : Blo 311834 709379 := bstep (se 1 (by rfl) ⟨532034, by rfl⟩ : syracuseStep 709379 = 1064069) B1064069
theorem B807875 : Blo 311834 807875 := bstep (se 1 (by rfl) ⟨605906, by rfl⟩ : syracuseStep 807875 = 1211813) B1211813
theorem B709649 : Blo 311834 709649 := bstep (se 2 (by rfl) ⟨266118, by rfl⟩ : syracuseStep 709649 = 532237) B532237
theorem B1594403 : Blo 311834 1594403 := bstep (se 1 (by rfl) ⟨1195802, by rfl⟩ : syracuseStep 1594403 = 2391605) B2391605
theorem B709667 : Blo 311834 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B1004653 : Blo 311834 1004653 := bstep (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) B376745
theorem B2380913 : Blo 311834 2380913 := bstep (se 2 (by rfl) ⟨892842, by rfl⟩ : syracuseStep 2380913 = 1785685) B1785685
theorem B447601 : Blo 311834 447601 := bstep (se 2 (by rfl) ⟨167850, by rfl⟩ : syracuseStep 447601 = 335701) B335701
theorem B447697 : Blo 311834 447697 := bstep (se 2 (by rfl) ⟨167886, by rfl⟩ : syracuseStep 447697 = 335773) B335773
theorem B709937 : Blo 311834 709937 := bstep (se 2 (by rfl) ⟨266226, by rfl⟩ : syracuseStep 709937 = 532453) B532453
theorem B709955 : Blo 311834 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B1136177 : Blo 311834 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B710225 : Blo 311834 710225 := bstep (se 2 (by rfl) ⟨266334, by rfl⟩ : syracuseStep 710225 = 532669) B532669
theorem B1005155 : Blo 311834 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B710243 : Blo 311834 710243 := bstep (se 1 (by rfl) ⟨532682, by rfl⟩ : syracuseStep 710243 = 1065365) B1065365
theorem B1267363 : Blo 311834 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B448193 : Blo 311834 448193 := bstep (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) B336145
theorem B3593969 : Blo 311834 3593969 := bstep (se 2 (by rfl) ⟨1347738, by rfl⟩ : syracuseStep 3593969 = 2695477) B2695477
theorem B907057 : Blo 311834 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B1595213 : Blo 311834 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B710513 : Blo 311834 710513 := bstep (se 2 (by rfl) ⟨266442, by rfl⟩ : syracuseStep 710513 = 532885) B532885
theorem B710531 : Blo 311834 710531 := bstep (se 1 (by rfl) ⟨532898, by rfl⟩ : syracuseStep 710531 = 1065797) B1065797
theorem B2021381 : Blo 311834 2021381 := bstep (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) B379009
theorem B547139 : Blo 311834 547139 := bstep (se 1 (by rfl) ⟨410354, by rfl⟩ : syracuseStep 547139 = 820709) B820709
theorem B449059 : Blo 311834 449059 := bstep (se 1 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 449059 = 673589) B673589
theorem B1268273 : Blo 311834 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B350851 : Blo 311834 350851 := bstep (se 1 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 350851 = 526277) B526277
theorem B449155 : Blo 311834 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B383635 : Blo 311834 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B318115 : Blo 311834 318115 := bstep (se 1 (by rfl) ⟨238586, by rfl⟩ : syracuseStep 318115 = 477173) B477173
theorem B1268401 : Blo 311834 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B8575715 : Blo 311834 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B350995 : Blo 311834 350995 := bstep (se 1 (by rfl) ⟨263246, by rfl⟩ : syracuseStep 350995 = 526493) B526493
theorem B1694533 : Blo 311834 1694533 := bstep (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) B317725
theorem B351139 : Blo 311834 351139 := bstep (se 1 (by rfl) ⟨263354, by rfl⟩ : syracuseStep 351139 = 526709) B526709
theorem B1006499 : Blo 311834 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B351283 : Blo 311834 351283 := bstep (se 1 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 351283 = 526925) B526925
theorem B449651 : Blo 311834 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B351427 : Blo 311834 351427 := bstep (se 1 (by rfl) ⟨263570, by rfl⟩ : syracuseStep 351427 = 527141) B527141
theorem B646339 : Blo 311834 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B351571 : Blo 311834 351571 := bstep (se 1 (by rfl) ⟨263678, by rfl⟩ : syracuseStep 351571 = 527357) B527357
theorem B351715 : Blo 311834 351715 := bstep (se 1 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 351715 = 527573) B527573
theorem B1433123 : Blo 311834 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B351859 : Blo 311834 351859 := bstep (se 1 (by rfl) ⟨263894, by rfl⟩ : syracuseStep 351859 = 527789) B527789
theorem B352003 : Blo 311834 352003 := bstep (se 1 (by rfl) ⟨264002, by rfl⟩ : syracuseStep 352003 = 528005) B528005
theorem B712547 : Blo 311834 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B1007473 : Blo 311834 1007473 := bstep (se 2 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 1007473 = 755605) B755605
theorem B1793933 : Blo 311834 1793933 := bstep (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) B672725
theorem B352147 : Blo 311834 352147 := bstep (se 1 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 352147 = 528221) B528221
theorem B352291 : Blo 311834 352291 := bstep (se 1 (by rfl) ⟨264218, by rfl⟩ : syracuseStep 352291 = 528437) B528437
theorem B1007729 : Blo 311834 1007729 := bstep (se 2 (by rfl) ⟨377898, by rfl⟩ : syracuseStep 1007729 = 755797) B755797
theorem B1335437 : Blo 311834 1335437 := bstep (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) B500789
theorem B1335473 : Blo 311834 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B352435 : Blo 311834 352435 := bstep (se 1 (by rfl) ⟨264326, by rfl⟩ : syracuseStep 352435 = 528653) B528653
theorem B352579 : Blo 311834 352579 := bstep (se 1 (by rfl) ⟨264434, by rfl⟩ : syracuseStep 352579 = 528869) B528869
theorem B319907 : Blo 311834 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B352723 : Blo 311834 352723 := bstep (se 1 (by rfl) ⟨264542, by rfl⟩ : syracuseStep 352723 = 529085) B529085
theorem B319955 : Blo 311834 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B1925603 : Blo 311834 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B352867 : Blo 311834 352867 := bstep (se 1 (by rfl) ⟨264650, by rfl⟩ : syracuseStep 352867 = 529301) B529301
theorem B1598129 : Blo 311834 1598129 := bstep (se 2 (by rfl) ⟨599298, by rfl⟩ : syracuseStep 1598129 = 1198597) B1198597
theorem B2712305 : Blo 311834 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B353011 : Blo 311834 353011 := bstep (se 1 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 353011 = 529517) B529517
theorem B353155 : Blo 311834 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B1369037 : Blo 311834 1369037 := bstep (se 3 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 1369037 = 513389) B513389
theorem B812035 : Blo 311834 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B353299 : Blo 311834 353299 := bstep (se 1 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 353299 = 529949) B529949
theorem B451681 : Blo 311834 451681 := bstep (se 2 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 451681 = 338761) B338761
theorem B5366897 : Blo 311834 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B353443 : Blo 311834 353443 := bstep (se 1 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 353443 = 530165) B530165
theorem B1008845 : Blo 311834 1008845 := bstep (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) B378317
theorem B353587 : Blo 311834 353587 := bstep (se 1 (by rfl) ⟨265190, by rfl⟩ : syracuseStep 353587 = 530381) B530381
theorem B353731 : Blo 311834 353731 := bstep (se 1 (by rfl) ⟨265298, by rfl⟩ : syracuseStep 353731 = 530597) B530597
theorem B353875 : Blo 311834 353875 := bstep (se 1 (by rfl) ⟨265406, by rfl⟩ : syracuseStep 353875 = 530813) B530813
theorem B354019 : Blo 311834 354019 := bstep (se 1 (by rfl) ⟨265514, by rfl⟩ : syracuseStep 354019 = 531029) B531029
theorem B4056817 : Blo 311834 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1074979 : Blo 311834 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B354163 : Blo 311834 354163 := bstep (se 1 (by rfl) ⟨265622, by rfl⟩ : syracuseStep 354163 = 531245) B531245
theorem B845731 : Blo 311834 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B681955 : Blo 311834 681955 := bstep (se 1 (by rfl) ⟨511466, by rfl⟩ : syracuseStep 681955 = 1022933) B1022933
theorem B354307 : Blo 311834 354307 := bstep (se 1 (by rfl) ⟨265730, by rfl⟩ : syracuseStep 354307 = 531461) B531461
theorem B1796165 : Blo 311834 1796165 := bstep (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) B336781
theorem B12085361 : Blo 311834 12085361 := bstep (se 2 (by rfl) ⟨4532010, by rfl⟩ : syracuseStep 12085361 = 9064021) B9064021
theorem B1108081 : Blo 311834 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B354451 : Blo 311834 354451 := bstep (se 1 (by rfl) ⟨265838, by rfl⟩ : syracuseStep 354451 = 531677) B531677
theorem B10414307 : Blo 311834 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B354595 : Blo 311834 354595 := bstep (se 1 (by rfl) ⟨265946, by rfl⟩ : syracuseStep 354595 = 531893) B531893
theorem B354739 : Blo 311834 354739 := bstep (se 1 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 354739 = 532109) B532109
theorem B1010189 : Blo 311834 1010189 := bstep (se 3 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 1010189 = 378821) B378821
theorem B354883 : Blo 311834 354883 := bstep (se 1 (by rfl) ⟨266162, by rfl⟩ : syracuseStep 354883 = 532325) B532325
theorem B1075825 : Blo 311834 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B355027 : Blo 311834 355027 := bstep (se 1 (by rfl) ⟨266270, by rfl⟩ : syracuseStep 355027 = 532541) B532541
theorem B1796849 : Blo 311834 1796849 := bstep (se 2 (by rfl) ⟨673818, by rfl⟩ : syracuseStep 1796849 = 1347637) B1347637
theorem B355171 : Blo 311834 355171 := bstep (se 1 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 355171 = 532757) B532757
theorem B1010627 : Blo 311834 1010627 := bstep (se 1 (by rfl) ⟨757970, by rfl⟩ : syracuseStep 1010627 = 1515941) B1515941
theorem B1076291 : Blo 311834 1076291 := bstep (se 1 (by rfl) ⟨807218, by rfl⟩ : syracuseStep 1076291 = 1614437) B1614437
theorem B1273009 : Blo 311834 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B847235 : Blo 311834 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B847331 : Blo 311834 847331 := bstep (se 1 (by rfl) ⟨635498, by rfl⟩ : syracuseStep 847331 = 1270997) B1270997
theorem B6057443 : Blo 311834 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B421633 : Blo 311834 421633 := bstep (se 2 (by rfl) ⟨158112, by rfl⟩ : syracuseStep 421633 = 316225) B316225
theorem B2715491 : Blo 311834 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B454753 : Blo 311834 454753 := bstep (se 2 (by rfl) ⟨170532, by rfl⟩ : syracuseStep 454753 = 341065) B341065
theorem B4026509 : Blo 311834 4026509 := bstep (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) B1509941
theorem B1798307 : Blo 311834 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B5402933 : Blo 311834 5402933 := bstep (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) B506525
theorem B1339811 : Blo 311834 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B1504291 : Blo 311834 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B718001 : Blo 311834 718001 := bstep (se 2 (by rfl) ⟨269250, by rfl⟩ : syracuseStep 718001 = 538501) B538501
theorem B3798197 : Blo 311834 3798197 := bstep (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) B356081
theorem B849137 : Blo 311834 849137 := bstep (se 2 (by rfl) ⟨318426, by rfl⟩ : syracuseStep 849137 = 636853) B636853
theorem B424163 : Blo 311834 424163 := bstep (se 1 (by rfl) ⟨318122, by rfl⟩ : syracuseStep 424163 = 636245) B636245
theorem B2849093 : Blo 311834 2849093 := bstep (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) B534205
theorem B1210801 : Blo 311834 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B916145 : Blo 311834 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B1080067 : Blo 311834 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B752483 : Blo 311834 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B1506289 : Blo 311834 1506289 := bstep (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) B1129717
theorem B916561 : Blo 311834 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B851267 : Blo 311834 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B3374405 : Blo 311834 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B425363 : Blo 311834 425363 := bstep (se 1 (by rfl) ⟨319022, by rfl⟩ : syracuseStep 425363 = 638045) B638045
theorem B950221 : Blo 311834 950221 := bstep (se 3 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 950221 = 356333) B356333
theorem B851917 : Blo 311834 851917 := bstep (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) B319469
theorem B2425049 : Blo 311834 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B2425349 : Blo 311834 2425349 := bstep (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) B454753
theorem B1081931 : Blo 311834 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1704523 : Blo 311834 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B2851421 : Blo 311834 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B1344221 : Blo 311834 1344221 := bstep (se 3 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 1344221 = 504083) B504083
theorem B1016651 : Blo 311834 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B2688065 : Blo 311834 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B853085 : Blo 311834 853085 := bstep (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) B319907
theorem B853213 : Blo 311834 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B3016115 : Blo 311834 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2393549 : Blo 311834 2393549 := bstep (se 3 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 2393549 = 897581) B897581
theorem B1508825 : Blo 311834 1508825 := bstep (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) B1131619
theorem B2394035 : Blo 311834 2394035 := bstep (se 1 (by rfl) ⟨1795526, by rfl⟩ : syracuseStep 2394035 = 3591053) B3591053
theorem B526297 : Blo 311834 526297 := bstep (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) B394723
theorem B395275 : Blo 311834 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B9635861 : Blo 311834 9635861 := bstep (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) B451681
theorem B1018049 : Blo 311834 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B395543 : Blo 311834 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B5409089 : Blo 311834 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B592267 : Blo 311834 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B592343 : Blo 311834 592343 := bstep (se 1 (by rfl) ⟨444257, by rfl⟩ : syracuseStep 592343 = 888515) B888515
theorem B526871 : Blo 311834 526871 := bstep (se 1 (by rfl) ⟨395153, by rfl⟩ : syracuseStep 526871 = 790307) B790307
theorem B7604867 : Blo 311834 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B526999 : Blo 311834 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B920267 : Blo 311834 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B1477441 : Blo 311834 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B396247 : Blo 311834 396247 := bstep (se 1 (by rfl) ⟨297185, by rfl⟩ : syracuseStep 396247 = 594371) B594371
theorem B789527 : Blo 311834 789527 := bstep (se 1 (by rfl) ⟨592145, by rfl⟩ : syracuseStep 789527 = 1184291) B1184291
theorem B593011 : Blo 311834 593011 := bstep (se 1 (by rfl) ⟨444758, by rfl⟩ : syracuseStep 593011 = 889517) B889517
theorem B527627 : Blo 311834 527627 := bstep (se 1 (by rfl) ⟨395720, by rfl⟩ : syracuseStep 527627 = 791441) B791441
theorem B2264365 : Blo 311834 2264365 := bstep (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) B849137
theorem B593239 : Blo 311834 593239 := bstep (se 1 (by rfl) ⟨444929, by rfl⟩ : syracuseStep 593239 = 889859) B889859
theorem B2395493 : Blo 311834 2395493 := bstep (se 4 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 2395493 = 449155) B449155
theorem B527755 : Blo 311834 527755 := bstep (se 1 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 527755 = 791633) B791633
theorem B1510807 : Blo 311834 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B2559383 : Blo 311834 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B593345 : Blo 311834 593345 := bstep (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) B445009
theorem B527897 : Blo 311834 527897 := bstep (se 2 (by rfl) ⟨197961, by rfl⟩ : syracuseStep 527897 = 395923) B395923
theorem B593497 : Blo 311834 593497 := bstep (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) B445123
theorem B528025 : Blo 311834 528025 := bstep (se 2 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 528025 = 396019) B396019
theorem B790195 : Blo 311834 790195 := bstep (se 1 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 790195 = 1185293) B1185293
theorem B5738165 : Blo 311834 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B757451 : Blo 311834 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B888641 : Blo 311834 888641 := bstep (se 2 (by rfl) ⟨333240, by rfl⟩ : syracuseStep 888641 = 666481) B666481
theorem B790337 : Blo 311834 790337 := bstep (se 2 (by rfl) ⟨296376, by rfl⟩ : syracuseStep 790337 = 592753) B592753
theorem B2395979 : Blo 311834 2395979 := bstep (se 1 (by rfl) ⟨1796984, by rfl⟩ : syracuseStep 2395979 = 3593969) B3593969
theorem B1052567 : Blo 311834 1052567 := bstep (se 1 (by rfl) ⟨789425, by rfl⟩ : syracuseStep 1052567 = 1578851) B1578851
theorem B1347587 : Blo 311834 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B528599 : Blo 311834 528599 := bstep (se 1 (by rfl) ⟨396449, by rfl⟩ : syracuseStep 528599 = 792899) B792899
theorem B1184003 : Blo 311834 1184003 := bstep (se 1 (by rfl) ⟨888002, by rfl⟩ : syracuseStep 1184003 = 1776005) B1776005
theorem B1184017 : Blo 311834 1184017 := bstep (se 2 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 1184017 = 888013) B888013
theorem B528727 : Blo 311834 528727 := bstep (se 1 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 528727 = 793091) B793091
theorem B1053107 : Blo 311834 1053107 := bstep (se 1 (by rfl) ⟨789830, by rfl⟩ : syracuseStep 1053107 = 1579661) B1579661
theorem B1184321 : Blo 311834 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B397963 : Blo 311834 397963 := bstep (se 1 (by rfl) ⟨298472, by rfl⟩ : syracuseStep 397963 = 596945) B596945
theorem B1053377 : Blo 311834 1053377 := bstep (se 2 (by rfl) ⟨395016, by rfl⟩ : syracuseStep 1053377 = 790033) B790033
theorem B1512209 : Blo 311834 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B594803 : Blo 311834 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B529355 : Blo 311834 529355 := bstep (se 1 (by rfl) ⟨397016, by rfl⟩ : syracuseStep 529355 = 794033) B794033
theorem B562177 : Blo 311834 562177 := bstep (se 2 (by rfl) ⟨210816, by rfl⟩ : syracuseStep 562177 = 421633) B421633
theorem B594955 : Blo 311834 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B955415 : Blo 311834 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B791603 : Blo 311834 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B529483 : Blo 311834 529483 := bstep (se 1 (by rfl) ⟨397112, by rfl⟩ : syracuseStep 529483 = 794225) B794225
theorem B529625 : Blo 311834 529625 := bstep (se 2 (by rfl) ⟨198609, by rfl⟩ : syracuseStep 529625 = 397219) B397219
theorem B1184989 : Blo 311834 1184989 := bstep (se 3 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 1184989 = 444371) B444371
theorem B1053917 : Blo 311834 1053917 := bstep (se 3 (by rfl) ⟨197609, by rfl⟩ : syracuseStep 1053917 = 395219) B395219
theorem B595289 : Blo 311834 595289 := bstep (se 2 (by rfl) ⟨223233, by rfl⟩ : syracuseStep 595289 = 446467) B446467
theorem B529753 : Blo 311834 529753 := bstep (se 2 (by rfl) ⟨198657, by rfl⟩ : syracuseStep 529753 = 397315) B397315
theorem B4330853 : Blo 311834 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B890291 : Blo 311834 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B890315 : Blo 311834 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B792139 : Blo 311834 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B398935 : Blo 311834 398935 := bstep (se 1 (by rfl) ⟨299201, by rfl⟩ : syracuseStep 398935 = 598403) B598403
theorem B1283735 : Blo 311834 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B792281 : Blo 311834 792281 := bstep (se 2 (by rfl) ⟨297105, by rfl⟩ : syracuseStep 792281 = 594211) B594211
theorem B4888325 : Blo 311834 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B530327 : Blo 311834 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B5380019 : Blo 311834 5380019 := bstep (se 1 (by rfl) ⟨4035014, by rfl⟩ : syracuseStep 5380019 = 8070029) B8070029
theorem B595927 : Blo 311834 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B530455 : Blo 311834 530455 := bstep (se 1 (by rfl) ⟨397841, by rfl⟩ : syracuseStep 530455 = 795683) B795683
theorem B3577931 : Blo 311834 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B334039 : Blo 311834 334039 := bstep (se 1 (by rfl) ⟨250529, by rfl⟩ : syracuseStep 334039 = 501059) B501059
theorem B891101 : Blo 311834 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B1055051 : Blo 311834 1055051 := bstep (se 1 (by rfl) ⟨791288, by rfl⟩ : syracuseStep 1055051 = 1582577) B1582577
theorem B1186265 : Blo 311834 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B793111 : Blo 311834 793111 := bstep (se 1 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 793111 = 1189667) B1189667
theorem B1055321 : Blo 311834 1055321 := bstep (se 2 (by rfl) ⟨395745, by rfl⟩ : syracuseStep 1055321 = 791491) B791491
theorem B531083 : Blo 311834 531083 := bstep (se 1 (by rfl) ⟨398312, by rfl⟩ : syracuseStep 531083 = 796625) B796625
theorem B2693837 : Blo 311834 2693837 := bstep (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) B1010189
theorem B2005721 : Blo 311834 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B596747 : Blo 311834 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B531211 : Blo 311834 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B1514285 : Blo 311834 1514285 := bstep (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) B567857
theorem B596801 : Blo 311834 596801 := bstep (se 2 (by rfl) ⟨223800, by rfl⟩ : syracuseStep 596801 = 447601) B447601
theorem B531353 : Blo 311834 531353 := bstep (se 2 (by rfl) ⟨199257, by rfl⟩ : syracuseStep 531353 = 398515) B398515
theorem B793547 : Blo 311834 793547 := bstep (se 1 (by rfl) ⟨595160, by rfl⟩ : syracuseStep 793547 = 1190321) B1190321
theorem B334859 : Blo 311834 334859 := bstep (se 1 (by rfl) ⟨251144, by rfl⟩ : syracuseStep 334859 = 502289) B502289
theorem B531481 : Blo 311834 531481 := bstep (se 2 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 531481 = 398611) B398611
theorem B1056023 : Blo 311834 1056023 := bstep (se 1 (by rfl) ⟨792017, by rfl⟩ : syracuseStep 1056023 = 1584035) B1584035
theorem B793921 : Blo 311834 793921 := bstep (se 2 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 793921 = 595441) B595441
theorem B1285649 : Blo 311834 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B564823 : Blo 311834 564823 := bstep (se 1 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 564823 = 847235) B847235
theorem B532055 : Blo 311834 532055 := bstep (se 1 (by rfl) ⟨399041, by rfl⟩ : syracuseStep 532055 = 798083) B798083
theorem B564887 : Blo 311834 564887 := bstep (se 1 (by rfl) ⟨423665, by rfl⟩ : syracuseStep 564887 = 847331) B847331
theorem B4038295 : Blo 311834 4038295 := bstep (se 1 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 4038295 = 6057443) B6057443
theorem B597719 : Blo 311834 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B532183 : Blo 311834 532183 := bstep (se 1 (by rfl) ⟨399137, by rfl⟩ : syracuseStep 532183 = 798275) B798275
theorem B1056563 : Blo 311834 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B794519 : Blo 311834 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B892889 : Blo 311834 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B1187891 : Blo 311834 1187891 := bstep (se 1 (by rfl) ⟨890918, by rfl⟩ : syracuseStep 1187891 = 1781837) B1781837
theorem B335927 : Blo 311834 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B1187905 : Blo 311834 1187905 := bstep (se 2 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 1187905 = 890929) B890929
theorem B1056833 : Blo 311834 1056833 := bstep (se 2 (by rfl) ⟨396312, by rfl⟩ : syracuseStep 1056833 = 792625) B792625
theorem B39297109 : Blo 311834 39297109 := bstep (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) B460513
theorem B598259 : Blo 311834 598259 := bstep (se 1 (by rfl) ⟨448694, by rfl⟩ : syracuseStep 598259 = 897389) B897389
theorem B893207 : Blo 311834 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B532811 : Blo 311834 532811 := bstep (se 1 (by rfl) ⟨399608, by rfl⟩ : syracuseStep 532811 = 799217) B799217
theorem B1581443 : Blo 311834 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B532939 : Blo 311834 532939 := bstep (se 1 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 532939 = 799409) B799409
theorem B1614401 : Blo 311834 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B1057373 : Blo 311834 1057373 := bstep (se 3 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 1057373 = 396515) B396515
theorem B795329 : Blo 311834 795329 := bstep (se 2 (by rfl) ⟨298248, by rfl⟩ : syracuseStep 795329 = 596497) B596497
theorem B598745 : Blo 311834 598745 := bstep (se 2 (by rfl) ⟨224529, by rfl⟩ : syracuseStep 598745 = 449059) B449059
theorem B2532131 : Blo 311834 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B467801 : Blo 311834 467801 := bstep (se 2 (by rfl) ⟨175425, by rfl⟩ : syracuseStep 467801 = 350851) B350851
theorem B2270045 : Blo 311834 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B467915 : Blo 311834 467915 := bstep (se 1 (by rfl) ⟨350936, by rfl⟩ : syracuseStep 467915 = 701873) B701873
theorem B467927 : Blo 311834 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B467993 : Blo 311834 467993 := bstep (se 2 (by rfl) ⟨175497, by rfl⟩ : syracuseStep 467993 = 350995) B350995
theorem B894017 : Blo 311834 894017 := bstep (se 2 (by rfl) ⟨335256, by rfl⟩ : syracuseStep 894017 = 670513) B670513
theorem B337003 : Blo 311834 337003 := bstep (se 1 (by rfl) ⟨252752, by rfl⟩ : syracuseStep 337003 = 505505) B505505
theorem B468107 : Blo 311834 468107 := bstep (se 1 (by rfl) ⟨351080, by rfl⟩ : syracuseStep 468107 = 702161) B702161
theorem B468119 : Blo 311834 468119 := bstep (se 1 (by rfl) ⟨351089, by rfl⟩ : syracuseStep 468119 = 702179) B702179
theorem B468185 : Blo 311834 468185 := bstep (se 2 (by rfl) ⟨175569, by rfl⟩ : syracuseStep 468185 = 351139) B351139
theorem B795865 : Blo 311834 795865 := bstep (se 2 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 795865 = 596899) B596899
theorem B2008385 : Blo 311834 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B468299 : Blo 311834 468299 := bstep (se 1 (by rfl) ⟨351224, by rfl⟩ : syracuseStep 468299 = 702449) B702449
theorem B468311 : Blo 311834 468311 := bstep (se 1 (by rfl) ⟨351233, by rfl⟩ : syracuseStep 468311 = 702467) B702467
theorem B468377 : Blo 311834 468377 := bstep (se 2 (by rfl) ⟨175641, by rfl⟩ : syracuseStep 468377 = 351283) B351283
theorem B468491 : Blo 311834 468491 := bstep (se 1 (by rfl) ⟨351368, by rfl⟩ : syracuseStep 468491 = 702737) B702737
theorem B468503 : Blo 311834 468503 := bstep (se 1 (by rfl) ⟨351377, by rfl⟩ : syracuseStep 468503 = 702755) B702755
theorem B468569 : Blo 311834 468569 := bstep (se 2 (by rfl) ⟨175713, by rfl⟩ : syracuseStep 468569 = 351427) B351427
theorem B861785 : Blo 311834 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B468683 : Blo 311834 468683 := bstep (se 1 (by rfl) ⟨351512, by rfl⟩ : syracuseStep 468683 = 703025) B703025
theorem B1058507 : Blo 311834 1058507 := bstep (se 1 (by rfl) ⟨793880, by rfl⟩ : syracuseStep 1058507 = 1587761) B1587761
theorem B468695 : Blo 311834 468695 := bstep (se 1 (by rfl) ⟨351521, by rfl⟩ : syracuseStep 468695 = 703043) B703043
theorem B468761 : Blo 311834 468761 := bstep (se 2 (by rfl) ⟨175785, by rfl⟩ : syracuseStep 468761 = 351571) B351571
theorem B468875 : Blo 311834 468875 := bstep (se 1 (by rfl) ⟨351656, by rfl⟩ : syracuseStep 468875 = 703313) B703313
theorem B468887 : Blo 311834 468887 := bstep (se 1 (by rfl) ⟨351665, by rfl⟩ : syracuseStep 468887 = 703331) B703331
theorem B501655 : Blo 311834 501655 := bstep (se 1 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 501655 = 752483) B752483
theorem B1189835 : Blo 311834 1189835 := bstep (se 1 (by rfl) ⟨892376, by rfl⟩ : syracuseStep 1189835 = 1784753) B1784753
theorem B468953 : Blo 311834 468953 := bstep (se 2 (by rfl) ⟨175857, by rfl⟩ : syracuseStep 468953 = 351715) B351715
theorem B1189849 : Blo 311834 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B1058777 : Blo 311834 1058777 := bstep (se 2 (by rfl) ⟨397041, by rfl⟩ : syracuseStep 1058777 = 794083) B794083
theorem B469067 : Blo 311834 469067 := bstep (se 1 (by rfl) ⟨351800, by rfl⟩ : syracuseStep 469067 = 703601) B703601
theorem B469079 : Blo 311834 469079 := bstep (se 1 (by rfl) ⟨351809, by rfl⟩ : syracuseStep 469079 = 703619) B703619
theorem B469145 : Blo 311834 469145 := bstep (se 2 (by rfl) ⟨175929, by rfl⟩ : syracuseStep 469145 = 351859) B351859
theorem B469259 : Blo 311834 469259 := bstep (se 1 (by rfl) ⟨351944, by rfl⟩ : syracuseStep 469259 = 703889) B703889
theorem B469271 : Blo 311834 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B796979 : Blo 311834 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B469337 : Blo 311834 469337 := bstep (se 2 (by rfl) ⟨176001, by rfl⟩ : syracuseStep 469337 = 352003) B352003
theorem B1845605 : Blo 311834 1845605 := bstep (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) B346051
theorem B469451 : Blo 311834 469451 := bstep (se 1 (by rfl) ⟨352088, by rfl⟩ : syracuseStep 469451 = 704177) B704177
theorem B469463 : Blo 311834 469463 := bstep (se 1 (by rfl) ⟨352097, by rfl⟩ : syracuseStep 469463 = 704195) B704195
theorem B469529 : Blo 311834 469529 := bstep (se 2 (by rfl) ⟨176073, by rfl⟩ : syracuseStep 469529 = 352147) B352147
theorem B797273 : Blo 311834 797273 := bstep (se 2 (by rfl) ⟨298977, by rfl⟩ : syracuseStep 797273 = 597955) B597955
theorem B469643 : Blo 311834 469643 := bstep (se 1 (by rfl) ⟨352232, by rfl⟩ : syracuseStep 469643 = 704465) B704465
theorem B469655 : Blo 311834 469655 := bstep (se 1 (by rfl) ⟨352241, by rfl⟩ : syracuseStep 469655 = 704483) B704483
theorem B1059479 : Blo 311834 1059479 := bstep (se 1 (by rfl) ⟨794609, by rfl⟩ : syracuseStep 1059479 = 1589219) B1589219
theorem B895691 : Blo 311834 895691 := bstep (se 1 (by rfl) ⟨671768, by rfl⟩ : syracuseStep 895691 = 1343537) B1343537
theorem B469721 : Blo 311834 469721 := bstep (se 2 (by rfl) ⟨176145, by rfl⟩ : syracuseStep 469721 = 352291) B352291
theorem B469835 : Blo 311834 469835 := bstep (se 1 (by rfl) ⟨352376, by rfl⟩ : syracuseStep 469835 = 704753) B704753
theorem B469847 : Blo 311834 469847 := bstep (se 1 (by rfl) ⟨352385, by rfl⟩ : syracuseStep 469847 = 704771) B704771
theorem B1190807 : Blo 311834 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B469913 : Blo 311834 469913 := bstep (se 2 (by rfl) ⟨176217, by rfl⟩ : syracuseStep 469913 = 352435) B352435
theorem B666625 : Blo 311834 666625 := bstep (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) B499969
theorem B470027 : Blo 311834 470027 := bstep (se 1 (by rfl) ⟨352520, by rfl⟩ : syracuseStep 470027 = 705041) B705041
theorem B470039 : Blo 311834 470039 := bstep (se 1 (by rfl) ⟨352529, by rfl⟩ : syracuseStep 470039 = 705059) B705059
theorem B1780811 : Blo 311834 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B470105 : Blo 311834 470105 := bstep (se 2 (by rfl) ⟨176289, by rfl⟩ : syracuseStep 470105 = 352579) B352579
theorem B1060019 : Blo 311834 1060019 := bstep (se 1 (by rfl) ⟨795014, by rfl⟩ : syracuseStep 1060019 = 1590029) B1590029
theorem B470219 : Blo 311834 470219 := bstep (se 1 (by rfl) ⟨352664, by rfl⟩ : syracuseStep 470219 = 705329) B705329
theorem B470231 : Blo 311834 470231 := bstep (se 1 (by rfl) ⟨352673, by rfl⟩ : syracuseStep 470231 = 705347) B705347
theorem B470297 : Blo 311834 470297 := bstep (se 2 (by rfl) ⟨176361, by rfl⟩ : syracuseStep 470297 = 352723) B352723
theorem B666967 : Blo 311834 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B470411 : Blo 311834 470411 := bstep (se 1 (by rfl) ⟨352808, by rfl⟩ : syracuseStep 470411 = 705617) B705617
theorem B470423 : Blo 311834 470423 := bstep (se 1 (by rfl) ⟨352817, by rfl⟩ : syracuseStep 470423 = 705635) B705635
theorem B1060289 : Blo 311834 1060289 := bstep (se 2 (by rfl) ⟨397608, by rfl⟩ : syracuseStep 1060289 = 795217) B795217
theorem B404939 : Blo 311834 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B470489 : Blo 311834 470489 := bstep (se 2 (by rfl) ⟨176433, by rfl⟩ : syracuseStep 470489 = 352867) B352867
theorem B470603 : Blo 311834 470603 := bstep (se 1 (by rfl) ⟨352952, by rfl⟩ : syracuseStep 470603 = 705905) B705905
theorem B470615 : Blo 311834 470615 := bstep (se 1 (by rfl) ⟨352961, by rfl⟩ : syracuseStep 470615 = 705923) B705923
theorem B470681 : Blo 311834 470681 := bstep (se 2 (by rfl) ⟨176505, by rfl⟩ : syracuseStep 470681 = 353011) B353011
theorem B470795 : Blo 311834 470795 := bstep (se 1 (by rfl) ⟨353096, by rfl⟩ : syracuseStep 470795 = 706193) B706193
theorem B470807 : Blo 311834 470807 := bstep (se 1 (by rfl) ⟨353105, by rfl⟩ : syracuseStep 470807 = 706211) B706211
theorem B470873 : Blo 311834 470873 := bstep (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) B353155
theorem B667531 : Blo 311834 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B503705 : Blo 311834 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B470987 : Blo 311834 470987 := bstep (se 1 (by rfl) ⟨353240, by rfl⟩ : syracuseStep 470987 = 706481) B706481
theorem B470999 : Blo 311834 470999 := bstep (se 1 (by rfl) ⟨353249, by rfl⟩ : syracuseStep 470999 = 706499) B706499
theorem B1060829 : Blo 311834 1060829 := bstep (se 3 (by rfl) ⟨198905, by rfl⟩ : syracuseStep 1060829 = 397811) B397811
theorem B896989 : Blo 311834 896989 := bstep (se 3 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 896989 = 336371) B336371
theorem B1585169 : Blo 311834 1585169 := bstep (se 2 (by rfl) ⟨594438, by rfl⟩ : syracuseStep 1585169 = 1188877) B1188877
theorem B471065 : Blo 311834 471065 := bstep (se 2 (by rfl) ⟨176649, by rfl⟩ : syracuseStep 471065 = 353299) B353299
theorem B634931 : Blo 311834 634931 := bstep (se 1 (by rfl) ⟨476198, by rfl⟩ : syracuseStep 634931 = 952397) B952397
theorem B1192067 : Blo 311834 1192067 := bstep (se 1 (by rfl) ⟨894050, by rfl⟩ : syracuseStep 1192067 = 1788101) B1788101
theorem B471179 : Blo 311834 471179 := bstep (se 1 (by rfl) ⟨353384, by rfl⟩ : syracuseStep 471179 = 706769) B706769
theorem B471191 : Blo 311834 471191 := bstep (se 1 (by rfl) ⟨353393, by rfl⟩ : syracuseStep 471191 = 706787) B706787
theorem B1585331 : Blo 311834 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B798923 : Blo 311834 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B471257 : Blo 311834 471257 := bstep (se 2 (by rfl) ⟨176721, by rfl⟩ : syracuseStep 471257 = 353443) B353443
theorem B897331 : Blo 311834 897331 := bstep (se 1 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 897331 = 1345997) B1345997
theorem B471371 : Blo 311834 471371 := bstep (se 1 (by rfl) ⟨353528, by rfl⟩ : syracuseStep 471371 = 707057) B707057
theorem B471383 : Blo 311834 471383 := bstep (se 1 (by rfl) ⟨353537, by rfl⟩ : syracuseStep 471383 = 707075) B707075
theorem B471449 : Blo 311834 471449 := bstep (se 2 (by rfl) ⟨176793, by rfl⟩ : syracuseStep 471449 = 353587) B353587
theorem B471563 : Blo 311834 471563 := bstep (se 1 (by rfl) ⟨353672, by rfl⟩ : syracuseStep 471563 = 707345) B707345
theorem B471575 : Blo 311834 471575 := bstep (se 1 (by rfl) ⟨353681, by rfl⟩ : syracuseStep 471575 = 707363) B707363
theorem B471641 : Blo 311834 471641 := bstep (se 2 (by rfl) ⟨176865, by rfl⟩ : syracuseStep 471641 = 353731) B353731
theorem B471755 : Blo 311834 471755 := bstep (se 1 (by rfl) ⟨353816, by rfl⟩ : syracuseStep 471755 = 707633) B707633
theorem B471767 : Blo 311834 471767 := bstep (se 1 (by rfl) ⟨353825, by rfl⟩ : syracuseStep 471767 = 707651) B707651
theorem B471833 : Blo 311834 471833 := bstep (se 2 (by rfl) ⟨176937, by rfl⟩ : syracuseStep 471833 = 353875) B353875
theorem B2011949 : Blo 311834 2011949 := bstep (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) B754481
theorem B471947 : Blo 311834 471947 := bstep (se 1 (by rfl) ⟨353960, by rfl⟩ : syracuseStep 471947 = 707921) B707921
theorem B1356695 : Blo 311834 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B471959 : Blo 311834 471959 := bstep (se 1 (by rfl) ⟨353969, by rfl⟩ : syracuseStep 471959 = 707939) B707939
theorem B472025 : Blo 311834 472025 := bstep (se 2 (by rfl) ⟨177009, by rfl⟩ : syracuseStep 472025 = 354019) B354019
theorem B2012177 : Blo 311834 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B537625 : Blo 311834 537625 := bstep (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) B403219
theorem B635969 : Blo 311834 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B1061963 : Blo 311834 1061963 := bstep (se 1 (by rfl) ⟨796472, by rfl⟩ : syracuseStep 1061963 = 1592945) B1592945
theorem B472139 : Blo 311834 472139 := bstep (se 1 (by rfl) ⟨354104, by rfl⟩ : syracuseStep 472139 = 708209) B708209
theorem B472151 : Blo 311834 472151 := bstep (se 1 (by rfl) ⟨354113, by rfl⟩ : syracuseStep 472151 = 708227) B708227
theorem B472217 : Blo 311834 472217 := bstep (se 2 (by rfl) ⟨177081, by rfl⟩ : syracuseStep 472217 = 354163) B354163
theorem B636083 : Blo 311834 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B701657 : Blo 311834 701657 := bstep (se 2 (by rfl) ⟨263121, by rfl⟩ : syracuseStep 701657 = 526243) B526243
theorem B898265 : Blo 311834 898265 := bstep (se 2 (by rfl) ⟨336849, by rfl⟩ : syracuseStep 898265 = 673699) B673699
theorem B668915 : Blo 311834 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B472331 : Blo 311834 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B472343 : Blo 311834 472343 := bstep (se 1 (by rfl) ⟨354257, by rfl⟩ : syracuseStep 472343 = 708515) B708515
theorem B701747 : Blo 311834 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B701783 : Blo 311834 701783 := bstep (se 1 (by rfl) ⟨526337, by rfl⟩ : syracuseStep 701783 = 1052675) B1052675
theorem B669017 : Blo 311834 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B1062233 : Blo 311834 1062233 := bstep (se 2 (by rfl) ⟨398337, by rfl⟩ : syracuseStep 1062233 = 796675) B796675
theorem B472409 : Blo 311834 472409 := bstep (se 2 (by rfl) ⟨177153, by rfl⟩ : syracuseStep 472409 = 354307) B354307
theorem B472523 : Blo 311834 472523 := bstep (se 1 (by rfl) ⟨354392, by rfl⟩ : syracuseStep 472523 = 708785) B708785
theorem B472535 : Blo 311834 472535 := bstep (se 1 (by rfl) ⟨354401, by rfl⟩ : syracuseStep 472535 = 708803) B708803
theorem B701963 : Blo 311834 701963 := bstep (se 1 (by rfl) ⟨526472, by rfl⟩ : syracuseStep 701963 = 1052945) B1052945
theorem B2373137 : Blo 311834 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B472601 : Blo 311834 472601 := bstep (se 2 (by rfl) ⟨177225, by rfl⟩ : syracuseStep 472601 = 354451) B354451
theorem B702017 : Blo 311834 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B472715 : Blo 311834 472715 := bstep (se 1 (by rfl) ⟨354536, by rfl⟩ : syracuseStep 472715 = 709073) B709073
theorem B472727 : Blo 311834 472727 := bstep (se 1 (by rfl) ⟨354545, by rfl⟩ : syracuseStep 472727 = 709091) B709091
theorem B669377 : Blo 311834 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B636619 : Blo 311834 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B472793 : Blo 311834 472793 := bstep (se 2 (by rfl) ⟨177297, by rfl⟩ : syracuseStep 472793 = 354595) B354595
theorem B702233 : Blo 311834 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B472907 : Blo 311834 472907 := bstep (se 1 (by rfl) ⟨354680, by rfl⟩ : syracuseStep 472907 = 709361) B709361
theorem B472919 : Blo 311834 472919 := bstep (se 1 (by rfl) ⟨354689, by rfl⟩ : syracuseStep 472919 = 709379) B709379
theorem B702323 : Blo 311834 702323 := bstep (se 1 (by rfl) ⟨526742, by rfl⟩ : syracuseStep 702323 = 1053485) B1053485
theorem B702359 : Blo 311834 702359 := bstep (se 1 (by rfl) ⟨526769, by rfl⟩ : syracuseStep 702359 = 1053539) B1053539
theorem B472985 : Blo 311834 472985 := bstep (se 2 (by rfl) ⟨177369, by rfl⟩ : syracuseStep 472985 = 354739) B354739
theorem B538583 : Blo 311834 538583 := bstep (se 1 (by rfl) ⟨403937, by rfl⟩ : syracuseStep 538583 = 807875) B807875
theorem B473099 : Blo 311834 473099 := bstep (se 1 (by rfl) ⟨354824, by rfl⟩ : syracuseStep 473099 = 709649) B709649
theorem B1062935 : Blo 311834 1062935 := bstep (se 1 (by rfl) ⟨797201, by rfl⟩ : syracuseStep 1062935 = 1594403) B1594403
theorem B473111 : Blo 311834 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B702539 : Blo 311834 702539 := bstep (se 1 (by rfl) ⟨526904, by rfl⟩ : syracuseStep 702539 = 1053809) B1053809
theorem B1587275 : Blo 311834 1587275 := bstep (se 1 (by rfl) ⟨1190456, by rfl⟩ : syracuseStep 1587275 = 2380913) B2380913
theorem B473177 : Blo 311834 473177 := bstep (se 2 (by rfl) ⟨177441, by rfl⟩ : syracuseStep 473177 = 354883) B354883
theorem B2046053 : Blo 311834 2046053 := bstep (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) B383635
theorem B702593 : Blo 311834 702593 := bstep (se 2 (by rfl) ⟨263472, by rfl⟩ : syracuseStep 702593 = 526945) B526945
theorem B374987 : Blo 311834 374987 := bstep (se 1 (by rfl) ⟨281240, by rfl⟩ : syracuseStep 374987 = 562481) B562481
theorem B473291 : Blo 311834 473291 := bstep (se 1 (by rfl) ⟨354968, by rfl⟩ : syracuseStep 473291 = 709937) B709937
theorem B473303 : Blo 311834 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B473369 : Blo 311834 473369 := bstep (se 2 (by rfl) ⟨177513, by rfl⟩ : syracuseStep 473369 = 355027) B355027
theorem B702809 : Blo 311834 702809 := bstep (se 2 (by rfl) ⟨263553, by rfl⟩ : syracuseStep 702809 = 527107) B527107
theorem B473483 : Blo 311834 473483 := bstep (se 1 (by rfl) ⟨355112, by rfl⟩ : syracuseStep 473483 = 710225) B710225
theorem B670103 : Blo 311834 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B473495 : Blo 311834 473495 := bstep (se 1 (by rfl) ⟨355121, by rfl⟩ : syracuseStep 473495 = 710243) B710243
theorem B702899 : Blo 311834 702899 := bstep (se 1 (by rfl) ⟨527174, by rfl⟩ : syracuseStep 702899 = 1054349) B1054349
theorem B702935 : Blo 311834 702935 := bstep (se 1 (by rfl) ⟨527201, by rfl⟩ : syracuseStep 702935 = 1054403) B1054403
theorem B473561 : Blo 311834 473561 := bstep (se 2 (by rfl) ⟨177585, by rfl⟩ : syracuseStep 473561 = 355171) B355171
theorem B1063475 : Blo 311834 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B473675 : Blo 311834 473675 := bstep (se 1 (by rfl) ⟨355256, by rfl⟩ : syracuseStep 473675 = 710513) B710513
theorem B473687 : Blo 311834 473687 := bstep (se 1 (by rfl) ⟨355265, by rfl⟩ : syracuseStep 473687 = 710531) B710531
theorem B703115 : Blo 311834 703115 := bstep (se 1 (by rfl) ⟨527336, by rfl⟩ : syracuseStep 703115 = 1054673) B1054673
theorem B1686167 : Blo 311834 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B2669233 : Blo 311834 2669233 := bstep (se 2 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 2669233 = 2001925) B2001925
theorem B703169 : Blo 311834 703169 := bstep (se 2 (by rfl) ⟨263688, by rfl⟩ : syracuseStep 703169 = 527377) B527377
theorem B375511 : Blo 311834 375511 := bstep (se 1 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 375511 = 563267) B563267
theorem B1063745 : Blo 311834 1063745 := bstep (se 2 (by rfl) ⟨398904, by rfl⟩ : syracuseStep 1063745 = 797809) B797809
theorem B4537205 : Blo 311834 4537205 := bstep (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) B425363
theorem B703385 : Blo 311834 703385 := bstep (se 2 (by rfl) ⟨263769, by rfl⟩ : syracuseStep 703385 = 527539) B527539
theorem B703475 : Blo 311834 703475 := bstep (se 1 (by rfl) ⟨527606, by rfl⟩ : syracuseStep 703475 = 1055213) B1055213
theorem B703511 : Blo 311834 703511 := bstep (se 1 (by rfl) ⟨527633, by rfl⟩ : syracuseStep 703511 = 1055267) B1055267
theorem B2276387 : Blo 311834 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B5717143 : Blo 311834 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B1195181 : Blo 311834 1195181 := bstep (se 3 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 1195181 = 448193) B448193
theorem B703691 : Blo 311834 703691 := bstep (se 1 (by rfl) ⟨527768, by rfl⟩ : syracuseStep 703691 = 1055537) B1055537
theorem B703745 : Blo 311834 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B670999 : Blo 311834 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B1064285 : Blo 311834 1064285 := bstep (se 3 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 1064285 = 399107) B399107
theorem B3816881 : Blo 311834 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B703961 : Blo 311834 703961 := bstep (se 2 (by rfl) ⟨263985, by rfl⟩ : syracuseStep 703961 = 527971) B527971
theorem B704051 : Blo 311834 704051 := bstep (se 1 (by rfl) ⟨528038, by rfl⟩ : syracuseStep 704051 = 1056077) B1056077
theorem B704087 : Blo 311834 704087 := bstep (se 1 (by rfl) ⟨528065, by rfl⟩ : syracuseStep 704087 = 1056131) B1056131
theorem B704267 : Blo 311834 704267 := bstep (se 1 (by rfl) ⟨528200, by rfl⟩ : syracuseStep 704267 = 1056401) B1056401
theorem B704321 : Blo 311834 704321 := bstep (se 2 (by rfl) ⟨264120, by rfl⟩ : syracuseStep 704321 = 528241) B528241
theorem B1589057 : Blo 311834 1589057 := bstep (se 2 (by rfl) ⟨595896, by rfl⟩ : syracuseStep 1589057 = 1191793) B1191793
theorem B475031 : Blo 311834 475031 := bstep (se 1 (by rfl) ⟨356273, by rfl⟩ : syracuseStep 475031 = 712547) B712547
theorem B1195955 : Blo 311834 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B704537 : Blo 311834 704537 := bstep (se 2 (by rfl) ⟨264201, by rfl⟩ : syracuseStep 704537 = 528403) B528403
theorem B671819 : Blo 311834 671819 := bstep (se 1 (by rfl) ⟨503864, by rfl⟩ : syracuseStep 671819 = 1007729) B1007729
theorem B704627 : Blo 311834 704627 := bstep (se 1 (by rfl) ⟨528470, by rfl⟩ : syracuseStep 704627 = 1056941) B1056941
theorem B704663 : Blo 311834 704663 := bstep (se 1 (by rfl) ⟨528497, by rfl⟩ : syracuseStep 704663 = 1056995) B1056995
theorem B5062837 : Blo 311834 5062837 := bstep (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) B474641
theorem B704843 : Blo 311834 704843 := bstep (se 1 (by rfl) ⟨528632, by rfl⟩ : syracuseStep 704843 = 1057265) B1057265
theorem B704897 : Blo 311834 704897 := bstep (se 2 (by rfl) ⟨264336, by rfl⟩ : syracuseStep 704897 = 528673) B528673
theorem B1065419 : Blo 311834 1065419 := bstep (se 1 (by rfl) ⟨799064, by rfl⟩ : syracuseStep 1065419 = 1598129) B1598129
theorem B377303 : Blo 311834 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B311851 : Blo 311834 311851 := bstep (se 1 (by rfl) ⟨233888, by rfl⟩ : syracuseStep 311851 = 467777) B467777
theorem B311863 : Blo 311834 311863 := bstep (se 1 (by rfl) ⟨233897, by rfl⟩ : syracuseStep 311863 = 467795) B467795
theorem B5358149 : Blo 311834 5358149 := bstep (se 4 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 5358149 = 1004653) B1004653
theorem B311883 : Blo 311834 311883 := bstep (se 1 (by rfl) ⟨233912, by rfl⟩ : syracuseStep 311883 = 467825) B467825
theorem B311895 : Blo 311834 311895 := bstep (se 1 (by rfl) ⟨233921, by rfl⟩ : syracuseStep 311895 = 467843) B467843
theorem B705113 : Blo 311834 705113 := bstep (se 2 (by rfl) ⟨264417, by rfl⟩ : syracuseStep 705113 = 528835) B528835
theorem B1131101 : Blo 311834 1131101 := bstep (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) B424163
theorem B311915 : Blo 311834 311915 := bstep (se 1 (by rfl) ⟨233936, by rfl⟩ : syracuseStep 311915 = 467873) B467873
theorem B311927 : Blo 311834 311927 := bstep (se 1 (by rfl) ⟨233945, by rfl⟩ : syracuseStep 311927 = 467891) B467891
theorem B311947 : Blo 311834 311947 := bstep (se 1 (by rfl) ⟨233960, by rfl⟩ : syracuseStep 311947 = 467921) B467921
theorem B311959 : Blo 311834 311959 := bstep (se 1 (by rfl) ⟨233969, by rfl⟩ : syracuseStep 311959 = 467939) B467939
theorem B311979 : Blo 311834 311979 := bstep (se 1 (by rfl) ⟨233984, by rfl⟩ : syracuseStep 311979 = 467969) B467969
theorem B705203 : Blo 311834 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B311991 : Blo 311834 311991 := bstep (se 1 (by rfl) ⟨233993, by rfl⟩ : syracuseStep 311991 = 467987) B467987
theorem B312011 : Blo 311834 312011 := bstep (se 1 (by rfl) ⟨234008, by rfl⟩ : syracuseStep 312011 = 468017) B468017
theorem B312023 : Blo 311834 312023 := bstep (se 1 (by rfl) ⟨234017, by rfl⟩ : syracuseStep 312023 = 468035) B468035
theorem B705239 : Blo 311834 705239 := bstep (se 1 (by rfl) ⟨528929, by rfl⟩ : syracuseStep 705239 = 1057859) B1057859
theorem B1065689 : Blo 311834 1065689 := bstep (se 2 (by rfl) ⟨399633, by rfl⟩ : syracuseStep 1065689 = 799267) B799267
theorem B312043 : Blo 311834 312043 := bstep (se 1 (by rfl) ⟨234032, by rfl⟩ : syracuseStep 312043 = 468065) B468065
theorem B312055 : Blo 311834 312055 := bstep (se 1 (by rfl) ⟨234041, by rfl⟩ : syracuseStep 312055 = 468083) B468083
theorem B2999045 : Blo 311834 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B312075 : Blo 311834 312075 := bstep (se 1 (by rfl) ⟨234056, by rfl⟩ : syracuseStep 312075 = 468113) B468113
theorem B312087 : Blo 311834 312087 := bstep (se 1 (by rfl) ⟨234065, by rfl⟩ : syracuseStep 312087 = 468131) B468131
theorem B312107 : Blo 311834 312107 := bstep (se 1 (by rfl) ⟨234080, by rfl⟩ : syracuseStep 312107 = 468161) B468161
theorem B672563 : Blo 311834 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B312119 : Blo 311834 312119 := bstep (se 1 (by rfl) ⟨234089, by rfl⟩ : syracuseStep 312119 = 468179) B468179
theorem B312139 : Blo 311834 312139 := bstep (se 1 (by rfl) ⟨234104, by rfl⟩ : syracuseStep 312139 = 468209) B468209
theorem B312151 : Blo 311834 312151 := bstep (se 1 (by rfl) ⟨234113, by rfl⟩ : syracuseStep 312151 = 468227) B468227
theorem B1459037 : Blo 311834 1459037 := bstep (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) B547139
theorem B312171 : Blo 311834 312171 := bstep (se 1 (by rfl) ⟨234128, by rfl⟩ : syracuseStep 312171 = 468257) B468257
theorem B312183 : Blo 311834 312183 := bstep (se 1 (by rfl) ⟨234137, by rfl⟩ : syracuseStep 312183 = 468275) B468275
theorem B312203 : Blo 311834 312203 := bstep (se 1 (by rfl) ⟨234152, by rfl⟩ : syracuseStep 312203 = 468305) B468305
theorem B705419 : Blo 311834 705419 := bstep (se 1 (by rfl) ⟨529064, by rfl⟩ : syracuseStep 705419 = 1058129) B1058129
theorem B312215 : Blo 311834 312215 := bstep (se 1 (by rfl) ⟨234161, by rfl⟩ : syracuseStep 312215 = 468323) B468323
theorem B312235 : Blo 311834 312235 := bstep (se 1 (by rfl) ⟨234176, by rfl⟩ : syracuseStep 312235 = 468353) B468353
theorem B312247 : Blo 311834 312247 := bstep (se 1 (by rfl) ⟨234185, by rfl⟩ : syracuseStep 312247 = 468371) B468371
theorem B1426369 : Blo 311834 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B705473 : Blo 311834 705473 := bstep (se 2 (by rfl) ⟨264552, by rfl⟩ : syracuseStep 705473 = 529105) B529105
theorem B312267 : Blo 311834 312267 := bstep (se 1 (by rfl) ⟨234200, by rfl⟩ : syracuseStep 312267 = 468401) B468401
theorem B312279 : Blo 311834 312279 := bstep (se 1 (by rfl) ⟨234209, by rfl⟩ : syracuseStep 312279 = 468419) B468419
theorem B312299 : Blo 311834 312299 := bstep (se 1 (by rfl) ⟨234224, by rfl⟩ : syracuseStep 312299 = 468449) B468449
theorem B312311 : Blo 311834 312311 := bstep (se 1 (by rfl) ⟨234233, by rfl⟩ : syracuseStep 312311 = 468467) B468467
theorem B312331 : Blo 311834 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B312343 : Blo 311834 312343 := bstep (se 1 (by rfl) ⟨234257, by rfl⟩ : syracuseStep 312343 = 468515) B468515
theorem B312363 : Blo 311834 312363 := bstep (se 1 (by rfl) ⟨234272, by rfl⟩ : syracuseStep 312363 = 468545) B468545
theorem B312375 : Blo 311834 312375 := bstep (se 1 (by rfl) ⟨234281, by rfl⟩ : syracuseStep 312375 = 468563) B468563
theorem B312395 : Blo 311834 312395 := bstep (se 1 (by rfl) ⟨234296, by rfl⟩ : syracuseStep 312395 = 468593) B468593
theorem B312407 : Blo 311834 312407 := bstep (se 1 (by rfl) ⟨234305, by rfl⟩ : syracuseStep 312407 = 468611) B468611
theorem B312427 : Blo 311834 312427 := bstep (se 1 (by rfl) ⟨234320, by rfl⟩ : syracuseStep 312427 = 468641) B468641
theorem B312439 : Blo 311834 312439 := bstep (se 1 (by rfl) ⟨234329, by rfl⟩ : syracuseStep 312439 = 468659) B468659
theorem B312459 : Blo 311834 312459 := bstep (se 1 (by rfl) ⟨234344, by rfl⟩ : syracuseStep 312459 = 468689) B468689
theorem B312471 : Blo 311834 312471 := bstep (se 1 (by rfl) ⟨234353, by rfl⟩ : syracuseStep 312471 = 468707) B468707
theorem B705689 : Blo 311834 705689 := bstep (se 2 (by rfl) ⟨264633, by rfl⟩ : syracuseStep 705689 = 529267) B529267
theorem B312491 : Blo 311834 312491 := bstep (se 1 (by rfl) ⟨234368, by rfl⟩ : syracuseStep 312491 = 468737) B468737
theorem B312503 : Blo 311834 312503 := bstep (se 1 (by rfl) ⟨234377, by rfl⟩ : syracuseStep 312503 = 468755) B468755
theorem B312523 : Blo 311834 312523 := bstep (se 1 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 312523 = 468785) B468785
theorem B312535 : Blo 311834 312535 := bstep (se 1 (by rfl) ⟨234401, by rfl⟩ : syracuseStep 312535 = 468803) B468803
theorem B312555 : Blo 311834 312555 := bstep (se 1 (by rfl) ⟨234416, by rfl⟩ : syracuseStep 312555 = 468833) B468833
theorem B705779 : Blo 311834 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B312567 : Blo 311834 312567 := bstep (se 1 (by rfl) ⟨234425, by rfl⟩ : syracuseStep 312567 = 468851) B468851
theorem B312587 : Blo 311834 312587 := bstep (se 1 (by rfl) ⟨234440, by rfl⟩ : syracuseStep 312587 = 468881) B468881
theorem B312599 : Blo 311834 312599 := bstep (se 1 (by rfl) ⟨234449, by rfl⟩ : syracuseStep 312599 = 468899) B468899
theorem B705815 : Blo 311834 705815 := bstep (se 1 (by rfl) ⟨529361, by rfl⟩ : syracuseStep 705815 = 1058723) B1058723
theorem B312619 : Blo 311834 312619 := bstep (se 1 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 312619 = 468929) B468929
theorem B312631 : Blo 311834 312631 := bstep (se 1 (by rfl) ⟨234473, by rfl⟩ : syracuseStep 312631 = 468947) B468947
theorem B2377025 : Blo 311834 2377025 := bstep (se 2 (by rfl) ⟨891384, by rfl⟩ : syracuseStep 2377025 = 1782769) B1782769
theorem B312651 : Blo 311834 312651 := bstep (se 1 (by rfl) ⟨234488, by rfl⟩ : syracuseStep 312651 = 468977) B468977
theorem B312663 : Blo 311834 312663 := bstep (se 1 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 312663 = 468995) B468995
theorem B312683 : Blo 311834 312683 := bstep (se 1 (by rfl) ⟨234512, by rfl⟩ : syracuseStep 312683 = 469025) B469025
theorem B312695 : Blo 311834 312695 := bstep (se 1 (by rfl) ⟨234521, by rfl⟩ : syracuseStep 312695 = 469043) B469043
theorem B1197443 : Blo 311834 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B312715 : Blo 311834 312715 := bstep (se 1 (by rfl) ⟨234536, by rfl⟩ : syracuseStep 312715 = 469073) B469073
theorem B312727 : Blo 311834 312727 := bstep (se 1 (by rfl) ⟨234545, by rfl⟩ : syracuseStep 312727 = 469091) B469091
theorem B312747 : Blo 311834 312747 := bstep (se 1 (by rfl) ⟨234560, by rfl⟩ : syracuseStep 312747 = 469121) B469121
theorem B312759 : Blo 311834 312759 := bstep (se 1 (by rfl) ⟨234569, by rfl⟩ : syracuseStep 312759 = 469139) B469139
theorem B312779 : Blo 311834 312779 := bstep (se 1 (by rfl) ⟨234584, by rfl⟩ : syracuseStep 312779 = 469169) B469169
theorem B705995 : Blo 311834 705995 := bstep (se 1 (by rfl) ⟨529496, by rfl⟩ : syracuseStep 705995 = 1058993) B1058993
theorem B312791 : Blo 311834 312791 := bstep (se 1 (by rfl) ⟨234593, by rfl⟩ : syracuseStep 312791 = 469187) B469187
theorem B312811 : Blo 311834 312811 := bstep (se 1 (by rfl) ⟨234608, by rfl⟩ : syracuseStep 312811 = 469217) B469217
theorem B312823 : Blo 311834 312823 := bstep (se 1 (by rfl) ⟨234617, by rfl⟩ : syracuseStep 312823 = 469235) B469235
theorem B706049 : Blo 311834 706049 := bstep (se 2 (by rfl) ⟨264768, by rfl⟩ : syracuseStep 706049 = 529537) B529537
theorem B312843 : Blo 311834 312843 := bstep (se 1 (by rfl) ⟨234632, by rfl⟩ : syracuseStep 312843 = 469265) B469265
theorem B312855 : Blo 311834 312855 := bstep (se 1 (by rfl) ⟨234641, by rfl⟩ : syracuseStep 312855 = 469283) B469283
theorem B312875 : Blo 311834 312875 := bstep (se 1 (by rfl) ⟨234656, by rfl⟩ : syracuseStep 312875 = 469313) B469313
theorem B312887 : Blo 311834 312887 := bstep (se 1 (by rfl) ⟨234665, by rfl⟩ : syracuseStep 312887 = 469331) B469331
theorem B312907 : Blo 311834 312907 := bstep (se 1 (by rfl) ⟨234680, by rfl⟩ : syracuseStep 312907 = 469361) B469361
theorem B312919 : Blo 311834 312919 := bstep (se 1 (by rfl) ⟨234689, by rfl⟩ : syracuseStep 312919 = 469379) B469379
theorem B312939 : Blo 311834 312939 := bstep (se 1 (by rfl) ⟨234704, by rfl⟩ : syracuseStep 312939 = 469409) B469409
theorem B312951 : Blo 311834 312951 := bstep (se 1 (by rfl) ⟨234713, by rfl⟩ : syracuseStep 312951 = 469427) B469427
theorem B673409 : Blo 311834 673409 := bstep (se 2 (by rfl) ⟨252528, by rfl⟩ : syracuseStep 673409 = 505057) B505057
theorem B312971 : Blo 311834 312971 := bstep (se 1 (by rfl) ⟨234728, by rfl⟩ : syracuseStep 312971 = 469457) B469457
theorem B312983 : Blo 311834 312983 := bstep (se 1 (by rfl) ⟨234737, by rfl⟩ : syracuseStep 312983 = 469475) B469475
theorem B313003 : Blo 311834 313003 := bstep (se 1 (by rfl) ⟨234752, by rfl⟩ : syracuseStep 313003 = 469505) B469505
theorem B313015 : Blo 311834 313015 := bstep (se 1 (by rfl) ⟨234761, by rfl⟩ : syracuseStep 313015 = 469523) B469523
theorem B313035 : Blo 311834 313035 := bstep (se 1 (by rfl) ⟨234776, by rfl⟩ : syracuseStep 313035 = 469553) B469553
theorem B313047 : Blo 311834 313047 := bstep (se 1 (by rfl) ⟨234785, by rfl⟩ : syracuseStep 313047 = 469571) B469571
theorem B706265 : Blo 311834 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B1591001 : Blo 311834 1591001 := bstep (se 2 (by rfl) ⟨596625, by rfl⟩ : syracuseStep 1591001 = 1193251) B1193251
theorem B313067 : Blo 311834 313067 := bstep (se 1 (by rfl) ⟨234800, by rfl⟩ : syracuseStep 313067 = 469601) B469601
theorem B313079 : Blo 311834 313079 := bstep (se 1 (by rfl) ⟨234809, by rfl⟩ : syracuseStep 313079 = 469619) B469619
theorem B313099 : Blo 311834 313099 := bstep (se 1 (by rfl) ⟨234824, by rfl⟩ : syracuseStep 313099 = 469649) B469649
theorem B313111 : Blo 311834 313111 := bstep (se 1 (by rfl) ⟨234833, by rfl⟩ : syracuseStep 313111 = 469667) B469667
theorem B313131 : Blo 311834 313131 := bstep (se 1 (by rfl) ⟨234848, by rfl⟩ : syracuseStep 313131 = 469697) B469697
theorem B706355 : Blo 311834 706355 := bstep (se 1 (by rfl) ⟨529766, by rfl⟩ : syracuseStep 706355 = 1059533) B1059533
theorem B313143 : Blo 311834 313143 := bstep (se 1 (by rfl) ⟨234857, by rfl⟩ : syracuseStep 313143 = 469715) B469715
theorem B313163 : Blo 311834 313163 := bstep (se 1 (by rfl) ⟨234872, by rfl⟩ : syracuseStep 313163 = 469745) B469745
theorem B1197899 : Blo 311834 1197899 := bstep (se 1 (by rfl) ⟨898424, by rfl⟩ : syracuseStep 1197899 = 1796849) B1796849
theorem B313175 : Blo 311834 313175 := bstep (se 1 (by rfl) ⟨234881, by rfl⟩ : syracuseStep 313175 = 469763) B469763
theorem B706391 : Blo 311834 706391 := bstep (se 1 (by rfl) ⟨529793, by rfl⟩ : syracuseStep 706391 = 1059587) B1059587
theorem B313195 : Blo 311834 313195 := bstep (se 1 (by rfl) ⟨234896, by rfl⟩ : syracuseStep 313195 = 469793) B469793
theorem B313207 : Blo 311834 313207 := bstep (se 1 (by rfl) ⟨234905, by rfl⟩ : syracuseStep 313207 = 469811) B469811
theorem B313227 : Blo 311834 313227 := bstep (se 1 (by rfl) ⟨234920, by rfl⟩ : syracuseStep 313227 = 469841) B469841
theorem B313239 : Blo 311834 313239 := bstep (se 1 (by rfl) ⟨234929, by rfl⟩ : syracuseStep 313239 = 469859) B469859
theorem B313259 : Blo 311834 313259 := bstep (se 1 (by rfl) ⟨234944, by rfl⟩ : syracuseStep 313259 = 469889) B469889
theorem B313271 : Blo 311834 313271 := bstep (se 1 (by rfl) ⟨234953, by rfl⟩ : syracuseStep 313271 = 469907) B469907
theorem B313291 : Blo 311834 313291 := bstep (se 1 (by rfl) ⟨234968, by rfl⟩ : syracuseStep 313291 = 469937) B469937
theorem B313303 : Blo 311834 313303 := bstep (se 1 (by rfl) ⟨234977, by rfl⟩ : syracuseStep 313303 = 469955) B469955
theorem B673751 : Blo 311834 673751 := bstep (se 1 (by rfl) ⟨505313, by rfl⟩ : syracuseStep 673751 = 1010627) B1010627
theorem B313323 : Blo 311834 313323 := bstep (se 1 (by rfl) ⟨234992, by rfl⟩ : syracuseStep 313323 = 469985) B469985
theorem B313335 : Blo 311834 313335 := bstep (se 1 (by rfl) ⟨235001, by rfl⟩ : syracuseStep 313335 = 470003) B470003
theorem B313355 : Blo 311834 313355 := bstep (se 1 (by rfl) ⟨235016, by rfl⟩ : syracuseStep 313355 = 470033) B470033
theorem B706571 : Blo 311834 706571 := bstep (se 1 (by rfl) ⟨529928, by rfl⟩ : syracuseStep 706571 = 1059857) B1059857
theorem B1198097 : Blo 311834 1198097 := bstep (se 2 (by rfl) ⟨449286, by rfl⟩ : syracuseStep 1198097 = 898573) B898573
theorem B313367 : Blo 311834 313367 := bstep (se 1 (by rfl) ⟨235025, by rfl⟩ : syracuseStep 313367 = 470051) B470051
theorem B313387 : Blo 311834 313387 := bstep (se 1 (by rfl) ⟨235040, by rfl⟩ : syracuseStep 313387 = 470081) B470081
theorem B313399 : Blo 311834 313399 := bstep (se 1 (by rfl) ⟨235049, by rfl⟩ : syracuseStep 313399 = 470099) B470099
theorem B706625 : Blo 311834 706625 := bstep (se 2 (by rfl) ⟨264984, by rfl⟩ : syracuseStep 706625 = 529969) B529969
theorem B313419 : Blo 311834 313419 := bstep (se 1 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 313419 = 470129) B470129
theorem B313431 : Blo 311834 313431 := bstep (se 1 (by rfl) ⟨235073, by rfl⟩ : syracuseStep 313431 = 470147) B470147
theorem B313451 : Blo 311834 313451 := bstep (se 1 (by rfl) ⟨235088, by rfl⟩ : syracuseStep 313451 = 470177) B470177
theorem B313463 : Blo 311834 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B313483 : Blo 311834 313483 := bstep (se 1 (by rfl) ⟨235112, by rfl⟩ : syracuseStep 313483 = 470225) B470225
theorem B313495 : Blo 311834 313495 := bstep (se 1 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 313495 = 470243) B470243
theorem B313515 : Blo 311834 313515 := bstep (se 1 (by rfl) ⟨235136, by rfl⟩ : syracuseStep 313515 = 470273) B470273
theorem B313527 : Blo 311834 313527 := bstep (se 1 (by rfl) ⟨235145, by rfl⟩ : syracuseStep 313527 = 470291) B470291
theorem B313547 : Blo 311834 313547 := bstep (se 1 (by rfl) ⟨235160, by rfl⟩ : syracuseStep 313547 = 470321) B470321
theorem B313559 : Blo 311834 313559 := bstep (se 1 (by rfl) ⟨235169, by rfl⟩ : syracuseStep 313559 = 470339) B470339
theorem B1689817 : Blo 311834 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B313579 : Blo 311834 313579 := bstep (se 1 (by rfl) ⟨235184, by rfl⟩ : syracuseStep 313579 = 470369) B470369
theorem B313591 : Blo 311834 313591 := bstep (se 1 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 313591 = 470387) B470387
theorem B313611 : Blo 311834 313611 := bstep (se 1 (by rfl) ⟨235208, by rfl⟩ : syracuseStep 313611 = 470417) B470417
theorem B313623 : Blo 311834 313623 := bstep (se 1 (by rfl) ⟨235217, by rfl⟩ : syracuseStep 313623 = 470435) B470435
theorem B706841 : Blo 311834 706841 := bstep (se 2 (by rfl) ⟨265065, by rfl⟩ : syracuseStep 706841 = 530131) B530131
theorem B313643 : Blo 311834 313643 := bstep (se 1 (by rfl) ⟨235232, by rfl⟩ : syracuseStep 313643 = 470465) B470465
theorem B313655 : Blo 311834 313655 := bstep (se 1 (by rfl) ⟨235241, by rfl⟩ : syracuseStep 313655 = 470483) B470483
theorem B313675 : Blo 311834 313675 := bstep (se 1 (by rfl) ⟨235256, by rfl⟩ : syracuseStep 313675 = 470513) B470513
theorem B1362251 : Blo 311834 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B313687 : Blo 311834 313687 := bstep (se 1 (by rfl) ⟨235265, by rfl⟩ : syracuseStep 313687 = 470531) B470531
theorem B313707 : Blo 311834 313707 := bstep (se 1 (by rfl) ⟨235280, by rfl⟩ : syracuseStep 313707 = 470561) B470561
theorem B706931 : Blo 311834 706931 := bstep (se 1 (by rfl) ⟨530198, by rfl⟩ : syracuseStep 706931 = 1060397) B1060397
theorem B313719 : Blo 311834 313719 := bstep (se 1 (by rfl) ⟨235289, by rfl⟩ : syracuseStep 313719 = 470579) B470579
theorem B313739 : Blo 311834 313739 := bstep (se 1 (by rfl) ⟨235304, by rfl⟩ : syracuseStep 313739 = 470609) B470609
theorem B313751 : Blo 311834 313751 := bstep (se 1 (by rfl) ⟨235313, by rfl⟩ : syracuseStep 313751 = 470627) B470627
theorem B706967 : Blo 311834 706967 := bstep (se 1 (by rfl) ⟨530225, by rfl⟩ : syracuseStep 706967 = 1060451) B1060451
theorem B313771 : Blo 311834 313771 := bstep (se 1 (by rfl) ⟨235328, by rfl⟩ : syracuseStep 313771 = 470657) B470657
theorem B313783 : Blo 311834 313783 := bstep (se 1 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 313783 = 470675) B470675
theorem B313803 : Blo 311834 313803 := bstep (se 1 (by rfl) ⟨235352, by rfl⟩ : syracuseStep 313803 = 470705) B470705
theorem B313815 : Blo 311834 313815 := bstep (se 1 (by rfl) ⟨235361, by rfl⟩ : syracuseStep 313815 = 470723) B470723
theorem B313835 : Blo 311834 313835 := bstep (se 1 (by rfl) ⟨235376, by rfl⟩ : syracuseStep 313835 = 470753) B470753
theorem B313847 : Blo 311834 313847 := bstep (se 1 (by rfl) ⟨235385, by rfl⟩ : syracuseStep 313847 = 470771) B470771
theorem B313867 : Blo 311834 313867 := bstep (se 1 (by rfl) ⟨235400, by rfl⟩ : syracuseStep 313867 = 470801) B470801
theorem B313879 : Blo 311834 313879 := bstep (se 1 (by rfl) ⟨235409, by rfl⟩ : syracuseStep 313879 = 470819) B470819
theorem B313899 : Blo 311834 313899 := bstep (se 1 (by rfl) ⟨235424, by rfl⟩ : syracuseStep 313899 = 470849) B470849
theorem B313911 : Blo 311834 313911 := bstep (se 1 (by rfl) ⟨235433, by rfl⟩ : syracuseStep 313911 = 470867) B470867
theorem B313931 : Blo 311834 313931 := bstep (se 1 (by rfl) ⟨235448, by rfl⟩ : syracuseStep 313931 = 470897) B470897
theorem B707147 : Blo 311834 707147 := bstep (se 1 (by rfl) ⟨530360, by rfl⟩ : syracuseStep 707147 = 1060721) B1060721
theorem B313943 : Blo 311834 313943 := bstep (se 1 (by rfl) ⟨235457, by rfl⟩ : syracuseStep 313943 = 470915) B470915
theorem B313963 : Blo 311834 313963 := bstep (se 1 (by rfl) ⟨235472, by rfl⟩ : syracuseStep 313963 = 470945) B470945
theorem B313975 : Blo 311834 313975 := bstep (se 1 (by rfl) ⟨235481, by rfl⟩ : syracuseStep 313975 = 470963) B470963
theorem B707201 : Blo 311834 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B313995 : Blo 311834 313995 := bstep (se 1 (by rfl) ⟨235496, by rfl⟩ : syracuseStep 313995 = 470993) B470993
theorem B1428119 : Blo 311834 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B314007 : Blo 311834 314007 := bstep (se 1 (by rfl) ⟨235505, by rfl⟩ : syracuseStep 314007 = 471011) B471011
theorem B314027 : Blo 311834 314027 := bstep (se 1 (by rfl) ⟨235520, by rfl⟩ : syracuseStep 314027 = 471041) B471041
theorem B314039 : Blo 311834 314039 := bstep (se 1 (by rfl) ⟨235529, by rfl⟩ : syracuseStep 314039 = 471059) B471059
theorem B314059 : Blo 311834 314059 := bstep (se 1 (by rfl) ⟨235544, by rfl⟩ : syracuseStep 314059 = 471089) B471089
theorem B314071 : Blo 311834 314071 := bstep (se 1 (by rfl) ⟨235553, by rfl⟩ : syracuseStep 314071 = 471107) B471107
theorem B314091 : Blo 311834 314091 := bstep (se 1 (by rfl) ⟨235568, by rfl⟩ : syracuseStep 314091 = 471137) B471137
theorem B314103 : Blo 311834 314103 := bstep (se 1 (by rfl) ⟨235577, by rfl⟩ : syracuseStep 314103 = 471155) B471155
theorem B314123 : Blo 311834 314123 := bstep (se 1 (by rfl) ⟨235592, by rfl⟩ : syracuseStep 314123 = 471185) B471185
theorem B314135 : Blo 311834 314135 := bstep (se 1 (by rfl) ⟨235601, by rfl⟩ : syracuseStep 314135 = 471203) B471203
theorem B1198871 : Blo 311834 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B314155 : Blo 311834 314155 := bstep (se 1 (by rfl) ⟨235616, by rfl⟩ : syracuseStep 314155 = 471233) B471233
theorem B314167 : Blo 311834 314167 := bstep (se 1 (by rfl) ⟨235625, by rfl⟩ : syracuseStep 314167 = 471251) B471251
theorem B314187 : Blo 311834 314187 := bstep (se 1 (by rfl) ⟨235640, by rfl⟩ : syracuseStep 314187 = 471281) B471281
theorem B314199 : Blo 311834 314199 := bstep (se 1 (by rfl) ⟨235649, by rfl⟩ : syracuseStep 314199 = 471299) B471299
theorem B707417 : Blo 311834 707417 := bstep (se 2 (by rfl) ⟨265281, by rfl⟩ : syracuseStep 707417 = 530563) B530563
theorem B314219 : Blo 311834 314219 := bstep (se 1 (by rfl) ⟨235664, by rfl⟩ : syracuseStep 314219 = 471329) B471329
theorem B314231 : Blo 311834 314231 := bstep (se 1 (by rfl) ⟨235673, by rfl⟩ : syracuseStep 314231 = 471347) B471347
theorem B314251 : Blo 311834 314251 := bstep (se 1 (by rfl) ⟨235688, by rfl⟩ : syracuseStep 314251 = 471377) B471377
theorem B314263 : Blo 311834 314263 := bstep (se 1 (by rfl) ⟨235697, by rfl⟩ : syracuseStep 314263 = 471395) B471395
theorem B314283 : Blo 311834 314283 := bstep (se 1 (by rfl) ⟨235712, by rfl⟩ : syracuseStep 314283 = 471425) B471425
theorem B707507 : Blo 311834 707507 := bstep (se 1 (by rfl) ⟨530630, by rfl⟩ : syracuseStep 707507 = 1061261) B1061261
theorem B314295 : Blo 311834 314295 := bstep (se 1 (by rfl) ⟨235721, by rfl⟩ : syracuseStep 314295 = 471443) B471443
theorem B314315 : Blo 311834 314315 := bstep (se 1 (by rfl) ⟨235736, by rfl⟩ : syracuseStep 314315 = 471473) B471473
theorem B314327 : Blo 311834 314327 := bstep (se 1 (by rfl) ⟨235745, by rfl⟩ : syracuseStep 314327 = 471491) B471491
theorem B707543 : Blo 311834 707543 := bstep (se 1 (by rfl) ⟨530657, by rfl⟩ : syracuseStep 707543 = 1061315) B1061315
theorem B1199069 : Blo 311834 1199069 := bstep (se 3 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 1199069 = 449651) B449651
theorem B314347 : Blo 311834 314347 := bstep (se 1 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 314347 = 471521) B471521
theorem B314359 : Blo 311834 314359 := bstep (se 1 (by rfl) ⟨235769, by rfl⟩ : syracuseStep 314359 = 471539) B471539
theorem B314379 : Blo 311834 314379 := bstep (se 1 (by rfl) ⟨235784, by rfl⟩ : syracuseStep 314379 = 471569) B471569
theorem B314391 : Blo 311834 314391 := bstep (se 1 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 314391 = 471587) B471587
theorem B314411 : Blo 311834 314411 := bstep (se 1 (by rfl) ⟨235808, by rfl⟩ : syracuseStep 314411 = 471617) B471617
theorem B314423 : Blo 311834 314423 := bstep (se 1 (by rfl) ⟨235817, by rfl⟩ : syracuseStep 314423 = 471635) B471635
theorem B314443 : Blo 311834 314443 := bstep (se 1 (by rfl) ⟨235832, by rfl⟩ : syracuseStep 314443 = 471665) B471665
theorem B314455 : Blo 311834 314455 := bstep (se 1 (by rfl) ⟨235841, by rfl⟩ : syracuseStep 314455 = 471683) B471683
theorem B314475 : Blo 311834 314475 := bstep (se 1 (by rfl) ⟨235856, by rfl⟩ : syracuseStep 314475 = 471713) B471713
theorem B314487 : Blo 311834 314487 := bstep (se 1 (by rfl) ⟨235865, by rfl⟩ : syracuseStep 314487 = 471731) B471731
theorem B314507 : Blo 311834 314507 := bstep (se 1 (by rfl) ⟨235880, by rfl⟩ : syracuseStep 314507 = 471761) B471761
theorem B707723 : Blo 311834 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B314519 : Blo 311834 314519 := bstep (se 1 (by rfl) ⟨235889, by rfl⟩ : syracuseStep 314519 = 471779) B471779
theorem B314539 : Blo 311834 314539 := bstep (se 1 (by rfl) ⟨235904, by rfl⟩ : syracuseStep 314539 = 471809) B471809
theorem B314551 : Blo 311834 314551 := bstep (se 1 (by rfl) ⟨235913, by rfl⟩ : syracuseStep 314551 = 471827) B471827
theorem B707777 : Blo 311834 707777 := bstep (se 2 (by rfl) ⟨265416, by rfl⟩ : syracuseStep 707777 = 530833) B530833
theorem B314571 : Blo 311834 314571 := bstep (se 1 (by rfl) ⟨235928, by rfl⟩ : syracuseStep 314571 = 471857) B471857
theorem B314583 : Blo 311834 314583 := bstep (se 1 (by rfl) ⟨235937, by rfl⟩ : syracuseStep 314583 = 471875) B471875
theorem B2673881 : Blo 311834 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B2378969 : Blo 311834 2378969 := bstep (se 2 (by rfl) ⟨892113, by rfl⟩ : syracuseStep 2378969 = 1784227) B1784227
theorem B314603 : Blo 311834 314603 := bstep (se 1 (by rfl) ⟨235952, by rfl⟩ : syracuseStep 314603 = 471905) B471905
theorem B314615 : Blo 311834 314615 := bstep (se 1 (by rfl) ⟨235961, by rfl⟩ : syracuseStep 314615 = 471923) B471923
theorem B314635 : Blo 311834 314635 := bstep (se 1 (by rfl) ⟨235976, by rfl⟩ : syracuseStep 314635 = 471953) B471953
theorem B314647 : Blo 311834 314647 := bstep (se 1 (by rfl) ⟨235985, by rfl⟩ : syracuseStep 314647 = 471971) B471971
theorem B314667 : Blo 311834 314667 := bstep (se 1 (by rfl) ⟨236000, by rfl⟩ : syracuseStep 314667 = 472001) B472001
theorem B1592621 : Blo 311834 1592621 := bstep (se 3 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 1592621 = 597233) B597233
theorem B314679 : Blo 311834 314679 := bstep (se 1 (by rfl) ⟨236009, by rfl⟩ : syracuseStep 314679 = 472019) B472019
theorem B314699 : Blo 311834 314699 := bstep (se 1 (by rfl) ⟨236024, by rfl⟩ : syracuseStep 314699 = 472049) B472049
theorem B314711 : Blo 311834 314711 := bstep (se 1 (by rfl) ⟨236033, by rfl⟩ : syracuseStep 314711 = 472067) B472067
theorem B314731 : Blo 311834 314731 := bstep (se 1 (by rfl) ⟨236048, by rfl⟩ : syracuseStep 314731 = 472097) B472097
theorem B314743 : Blo 311834 314743 := bstep (se 1 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 314743 = 472115) B472115
theorem B314763 : Blo 311834 314763 := bstep (se 1 (by rfl) ⟨236072, by rfl⟩ : syracuseStep 314763 = 472145) B472145
theorem B314775 : Blo 311834 314775 := bstep (se 1 (by rfl) ⟨236081, by rfl⟩ : syracuseStep 314775 = 472163) B472163
theorem B707993 : Blo 311834 707993 := bstep (se 2 (by rfl) ⟨265497, by rfl⟩ : syracuseStep 707993 = 530995) B530995
theorem B314795 : Blo 311834 314795 := bstep (se 1 (by rfl) ⟨236096, by rfl⟩ : syracuseStep 314795 = 472193) B472193
theorem B314807 : Blo 311834 314807 := bstep (se 1 (by rfl) ⟨236105, by rfl⟩ : syracuseStep 314807 = 472211) B472211
theorem B478667 : Blo 311834 478667 := bstep (se 1 (by rfl) ⟨359000, by rfl⟩ : syracuseStep 478667 = 718001) B718001
theorem B314827 : Blo 311834 314827 := bstep (se 1 (by rfl) ⟨236120, by rfl⟩ : syracuseStep 314827 = 472241) B472241
theorem B314839 : Blo 311834 314839 := bstep (se 1 (by rfl) ⟨236129, by rfl⟩ : syracuseStep 314839 = 472259) B472259
theorem B314859 : Blo 311834 314859 := bstep (se 1 (by rfl) ⟨236144, by rfl⟩ : syracuseStep 314859 = 472289) B472289
theorem B708083 : Blo 311834 708083 := bstep (se 1 (by rfl) ⟨531062, by rfl⟩ : syracuseStep 708083 = 1062125) B1062125
theorem B314871 : Blo 311834 314871 := bstep (se 1 (by rfl) ⟨236153, by rfl⟩ : syracuseStep 314871 = 472307) B472307
theorem B314891 : Blo 311834 314891 := bstep (se 1 (by rfl) ⟨236168, by rfl⟩ : syracuseStep 314891 = 472337) B472337
theorem B708119 : Blo 311834 708119 := bstep (se 1 (by rfl) ⟨531089, by rfl⟩ : syracuseStep 708119 = 1062179) B1062179
theorem B314903 : Blo 311834 314903 := bstep (se 1 (by rfl) ⟨236177, by rfl⟩ : syracuseStep 314903 = 472355) B472355
theorem B314923 : Blo 311834 314923 := bstep (se 1 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 314923 = 472385) B472385
theorem B314935 : Blo 311834 314935 := bstep (se 1 (by rfl) ⟨236201, by rfl⟩ : syracuseStep 314935 = 472403) B472403
theorem B1691201 : Blo 311834 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B3001931 : Blo 311834 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B314955 : Blo 311834 314955 := bstep (se 1 (by rfl) ⟨236216, by rfl⟩ : syracuseStep 314955 = 472433) B472433
theorem B314967 : Blo 311834 314967 := bstep (se 1 (by rfl) ⟨236225, by rfl⟩ : syracuseStep 314967 = 472451) B472451
theorem B314987 : Blo 311834 314987 := bstep (se 1 (by rfl) ⟨236240, by rfl⟩ : syracuseStep 314987 = 472481) B472481
theorem B314999 : Blo 311834 314999 := bstep (se 1 (by rfl) ⟨236249, by rfl⟩ : syracuseStep 314999 = 472499) B472499
theorem B315019 : Blo 311834 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B315031 : Blo 311834 315031 := bstep (se 1 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 315031 = 472547) B472547
theorem B315051 : Blo 311834 315051 := bstep (se 1 (by rfl) ⟨236288, by rfl⟩ : syracuseStep 315051 = 472577) B472577
theorem B315063 : Blo 311834 315063 := bstep (se 1 (by rfl) ⟨236297, by rfl⟩ : syracuseStep 315063 = 472595) B472595
theorem B708299 : Blo 311834 708299 := bstep (se 1 (by rfl) ⟨531224, by rfl⟩ : syracuseStep 708299 = 1062449) B1062449
theorem B315083 : Blo 311834 315083 := bstep (se 1 (by rfl) ⟨236312, by rfl⟩ : syracuseStep 315083 = 472625) B472625
theorem B315095 : Blo 311834 315095 := bstep (se 1 (by rfl) ⟨236321, by rfl⟩ : syracuseStep 315095 = 472643) B472643
theorem B315115 : Blo 311834 315115 := bstep (se 1 (by rfl) ⟨236336, by rfl⟩ : syracuseStep 315115 = 472673) B472673
theorem B315127 : Blo 311834 315127 := bstep (se 1 (by rfl) ⟨236345, by rfl⟩ : syracuseStep 315127 = 472691) B472691
theorem B708353 : Blo 311834 708353 := bstep (se 2 (by rfl) ⟨265632, by rfl⟩ : syracuseStep 708353 = 531265) B531265
theorem B315147 : Blo 311834 315147 := bstep (se 1 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 315147 = 472721) B472721
theorem B315159 : Blo 311834 315159 := bstep (se 1 (by rfl) ⟨236369, by rfl⟩ : syracuseStep 315159 = 472739) B472739
theorem B315179 : Blo 311834 315179 := bstep (se 1 (by rfl) ⟨236384, by rfl⟩ : syracuseStep 315179 = 472769) B472769
theorem B315191 : Blo 311834 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B315211 : Blo 311834 315211 := bstep (se 1 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 315211 = 472817) B472817
theorem B315223 : Blo 311834 315223 := bstep (se 1 (by rfl) ⟨236417, by rfl⟩ : syracuseStep 315223 = 472835) B472835
theorem B315243 : Blo 311834 315243 := bstep (se 1 (by rfl) ⟨236432, by rfl⟩ : syracuseStep 315243 = 472865) B472865
theorem B315255 : Blo 311834 315255 := bstep (se 1 (by rfl) ⟨236441, by rfl⟩ : syracuseStep 315255 = 472883) B472883
theorem B315275 : Blo 311834 315275 := bstep (se 1 (by rfl) ⟨236456, by rfl⟩ : syracuseStep 315275 = 472913) B472913
theorem B315287 : Blo 311834 315287 := bstep (se 1 (by rfl) ⟨236465, by rfl⟩ : syracuseStep 315287 = 472931) B472931
theorem B315307 : Blo 311834 315307 := bstep (se 1 (by rfl) ⟨236480, by rfl⟩ : syracuseStep 315307 = 472961) B472961
theorem B315319 : Blo 311834 315319 := bstep (se 1 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 315319 = 472979) B472979
theorem B315339 : Blo 311834 315339 := bstep (se 1 (by rfl) ⟨236504, by rfl⟩ : syracuseStep 315339 = 473009) B473009
theorem B315351 : Blo 311834 315351 := bstep (se 1 (by rfl) ⟨236513, by rfl⟩ : syracuseStep 315351 = 473027) B473027
theorem B708569 : Blo 311834 708569 := bstep (se 2 (by rfl) ⟨265713, by rfl⟩ : syracuseStep 708569 = 531427) B531427
theorem B315371 : Blo 311834 315371 := bstep (se 1 (by rfl) ⟨236528, by rfl⟩ : syracuseStep 315371 = 473057) B473057
theorem B315383 : Blo 311834 315383 := bstep (se 1 (by rfl) ⟨236537, by rfl⟩ : syracuseStep 315383 = 473075) B473075
theorem B315403 : Blo 311834 315403 := bstep (se 1 (by rfl) ⟨236552, by rfl⟩ : syracuseStep 315403 = 473105) B473105
theorem B315415 : Blo 311834 315415 := bstep (se 1 (by rfl) ⟨236561, by rfl⟩ : syracuseStep 315415 = 473123) B473123
theorem B315435 : Blo 311834 315435 := bstep (se 1 (by rfl) ⟨236576, by rfl⟩ : syracuseStep 315435 = 473153) B473153
theorem B708659 : Blo 311834 708659 := bstep (se 1 (by rfl) ⟨531494, by rfl⟩ : syracuseStep 708659 = 1062989) B1062989
theorem B315447 : Blo 311834 315447 := bstep (se 1 (by rfl) ⟨236585, by rfl⟩ : syracuseStep 315447 = 473171) B473171
theorem B315467 : Blo 311834 315467 := bstep (se 1 (by rfl) ⟨236600, by rfl⟩ : syracuseStep 315467 = 473201) B473201
theorem B708695 : Blo 311834 708695 := bstep (se 1 (by rfl) ⟨531521, by rfl⟩ : syracuseStep 708695 = 1063043) B1063043
theorem B315479 : Blo 311834 315479 := bstep (se 1 (by rfl) ⟨236609, by rfl⟩ : syracuseStep 315479 = 473219) B473219
theorem B315499 : Blo 311834 315499 := bstep (se 1 (by rfl) ⟨236624, by rfl⟩ : syracuseStep 315499 = 473249) B473249
theorem B315511 : Blo 311834 315511 := bstep (se 1 (by rfl) ⟨236633, by rfl⟩ : syracuseStep 315511 = 473267) B473267
theorem B315531 : Blo 311834 315531 := bstep (se 1 (by rfl) ⟨236648, by rfl⟩ : syracuseStep 315531 = 473297) B473297
theorem B315543 : Blo 311834 315543 := bstep (se 1 (by rfl) ⟨236657, by rfl⟩ : syracuseStep 315543 = 473315) B473315
theorem B315563 : Blo 311834 315563 := bstep (se 1 (by rfl) ⟨236672, by rfl⟩ : syracuseStep 315563 = 473345) B473345
theorem B315575 : Blo 311834 315575 := bstep (se 1 (by rfl) ⟨236681, by rfl⟩ : syracuseStep 315575 = 473363) B473363
theorem B315595 : Blo 311834 315595 := bstep (se 1 (by rfl) ⟨236696, by rfl⟩ : syracuseStep 315595 = 473393) B473393
theorem B315607 : Blo 311834 315607 := bstep (se 1 (by rfl) ⟨236705, by rfl⟩ : syracuseStep 315607 = 473411) B473411
theorem B315627 : Blo 311834 315627 := bstep (se 1 (by rfl) ⟨236720, by rfl⟩ : syracuseStep 315627 = 473441) B473441
theorem B315639 : Blo 311834 315639 := bstep (se 1 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 315639 = 473459) B473459
theorem B4837637 : Blo 311834 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B708875 : Blo 311834 708875 := bstep (se 1 (by rfl) ⟨531656, by rfl⟩ : syracuseStep 708875 = 1063313) B1063313
theorem B315659 : Blo 311834 315659 := bstep (se 1 (by rfl) ⟨236744, by rfl⟩ : syracuseStep 315659 = 473489) B473489
theorem B315671 : Blo 311834 315671 := bstep (se 1 (by rfl) ⟨236753, by rfl⟩ : syracuseStep 315671 = 473507) B473507
theorem B315691 : Blo 311834 315691 := bstep (se 1 (by rfl) ⟨236768, by rfl⟩ : syracuseStep 315691 = 473537) B473537
theorem B315703 : Blo 311834 315703 := bstep (se 1 (by rfl) ⟨236777, by rfl⟩ : syracuseStep 315703 = 473555) B473555
theorem B708929 : Blo 311834 708929 := bstep (se 2 (by rfl) ⟨265848, by rfl⟩ : syracuseStep 708929 = 531697) B531697
theorem B315723 : Blo 311834 315723 := bstep (se 1 (by rfl) ⟨236792, by rfl⟩ : syracuseStep 315723 = 473585) B473585
theorem B315735 : Blo 311834 315735 := bstep (se 1 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 315735 = 473603) B473603
theorem B446809 : Blo 311834 446809 := bstep (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) B335107
theorem B315755 : Blo 311834 315755 := bstep (se 1 (by rfl) ⟨236816, by rfl⟩ : syracuseStep 315755 = 473633) B473633
theorem B315767 : Blo 311834 315767 := bstep (se 1 (by rfl) ⟨236825, by rfl⟩ : syracuseStep 315767 = 473651) B473651
theorem B315787 : Blo 311834 315787 := bstep (se 1 (by rfl) ⟨236840, by rfl⟩ : syracuseStep 315787 = 473681) B473681
theorem B315799 : Blo 311834 315799 := bstep (se 1 (by rfl) ⟨236849, by rfl⟩ : syracuseStep 315799 = 473699) B473699
theorem B315819 : Blo 311834 315819 := bstep (se 1 (by rfl) ⟨236864, by rfl⟩ : syracuseStep 315819 = 473729) B473729
theorem B315831 : Blo 311834 315831 := bstep (se 1 (by rfl) ⟨236873, by rfl⟩ : syracuseStep 315831 = 473747) B473747
theorem B610763 : Blo 311834 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B709145 : Blo 311834 709145 := bstep (se 2 (by rfl) ⟨265929, by rfl⟩ : syracuseStep 709145 = 531859) B531859
theorem B709235 : Blo 311834 709235 := bstep (se 1 (by rfl) ⟨531926, by rfl⟩ : syracuseStep 709235 = 1063853) B1063853
theorem B709271 : Blo 311834 709271 := bstep (se 1 (by rfl) ⟨531953, by rfl⟩ : syracuseStep 709271 = 1063907) B1063907
theorem B709451 : Blo 311834 709451 := bstep (se 1 (by rfl) ⟨532088, by rfl⟩ : syracuseStep 709451 = 1064177) B1064177
theorem B4510565 : Blo 311834 4510565 := bstep (se 4 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 4510565 = 845731) B845731
theorem B709505 : Blo 311834 709505 := bstep (se 2 (by rfl) ⟨266064, by rfl⟩ : syracuseStep 709505 = 532129) B532129
theorem B2249603 : Blo 311834 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B709721 : Blo 311834 709721 := bstep (se 2 (by rfl) ⟨266145, by rfl⟩ : syracuseStep 709721 = 532291) B532291
theorem B709811 : Blo 311834 709811 := bstep (se 1 (by rfl) ⟨532358, by rfl⟩ : syracuseStep 709811 = 1064717) B1064717
theorem B709847 : Blo 311834 709847 := bstep (se 1 (by rfl) ⟨532385, by rfl⟩ : syracuseStep 709847 = 1064771) B1064771
theorem B1266961 : Blo 311834 1266961 := bstep (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) B950221
theorem B1135889 : Blo 311834 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B3429697 : Blo 311834 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B710027 : Blo 311834 710027 := bstep (se 1 (by rfl) ⟨532520, by rfl⟩ : syracuseStep 710027 = 1065041) B1065041
theorem B710081 : Blo 311834 710081 := bstep (se 2 (by rfl) ⟨266280, by rfl⟩ : syracuseStep 710081 = 532561) B532561
theorem B317003 : Blo 311834 317003 := bstep (se 1 (by rfl) ⟨237752, by rfl⟩ : syracuseStep 317003 = 475505) B475505
theorem B710297 : Blo 311834 710297 := bstep (se 2 (by rfl) ⟨266361, by rfl⟩ : syracuseStep 710297 = 532723) B532723
theorem B710387 : Blo 311834 710387 := bstep (se 1 (by rfl) ⟨532790, by rfl⟩ : syracuseStep 710387 = 1065581) B1065581
theorem B448267 : Blo 311834 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B710423 : Blo 311834 710423 := bstep (se 1 (by rfl) ⟨532817, by rfl⟩ : syracuseStep 710423 = 1065635) B1065635
theorem B10180417 : Blo 311834 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B710603 : Blo 311834 710603 := bstep (se 1 (by rfl) ⟨532952, by rfl⟩ : syracuseStep 710603 = 1065905) B1065905
theorem B2021507 : Blo 311834 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B1268141 : Blo 311834 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B2382371 : Blo 311834 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B3824279 : Blo 311834 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B350923 : Blo 311834 350923 := bstep (se 1 (by rfl) ⟨263192, by rfl⟩ : syracuseStep 350923 = 526385) B526385
theorem B1006283 : Blo 311834 1006283 := bstep (se 1 (by rfl) ⟨754712, by rfl⟩ : syracuseStep 1006283 = 1509425) B1509425
theorem B1366807 : Blo 311834 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B351031 : Blo 311834 351031 := bstep (se 1 (by rfl) ⟨263273, by rfl⟩ : syracuseStep 351031 = 526547) B526547
theorem B1137559 : Blo 311834 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B1727411 : Blo 311834 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B449497 : Blo 311834 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B351211 : Blo 311834 351211 := bstep (se 1 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 351211 = 526817) B526817
theorem B351319 : Blo 311834 351319 := bstep (se 1 (by rfl) ⟨263489, by rfl⟩ : syracuseStep 351319 = 526979) B526979
theorem B1596509 : Blo 311834 1596509 := bstep (se 3 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 1596509 = 598691) B598691
theorem B5856407 : Blo 311834 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B1334465 : Blo 311834 1334465 := bstep (se 2 (by rfl) ⟨500424, by rfl⟩ : syracuseStep 1334465 = 1000849) B1000849
theorem B711937 : Blo 311834 711937 := bstep (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) B533953
theorem B351499 : Blo 311834 351499 := bstep (se 1 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 351499 = 527249) B527249
theorem B7232813 : Blo 311834 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B351607 : Blo 311834 351607 := bstep (se 1 (by rfl) ⟨263705, by rfl⟩ : syracuseStep 351607 = 527411) B527411
theorem B351787 : Blo 311834 351787 := bstep (se 1 (by rfl) ⟨263840, by rfl⟩ : syracuseStep 351787 = 527681) B527681
theorem B351895 : Blo 311834 351895 := bstep (se 1 (by rfl) ⟨263921, by rfl⟩ : syracuseStep 351895 = 527843) B527843
theorem B483031 : Blo 311834 483031 := bstep (se 1 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 483031 = 724547) B724547
theorem B1433305 : Blo 311834 1433305 := bstep (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) B1074979
theorem B352075 : Blo 311834 352075 := bstep (se 1 (by rfl) ⟨264056, by rfl⟩ : syracuseStep 352075 = 528113) B528113
theorem B319339 : Blo 311834 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B352183 : Blo 311834 352183 := bstep (se 1 (by rfl) ⟨264137, by rfl⟩ : syracuseStep 352183 = 528275) B528275
theorem B352363 : Blo 311834 352363 := bstep (se 1 (by rfl) ⟨264272, by rfl⟩ : syracuseStep 352363 = 528545) B528545
theorem B680089 : Blo 311834 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B352471 : Blo 311834 352471 := bstep (se 1 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 352471 = 528707) B528707
theorem B1007923 : Blo 311834 1007923 := bstep (se 1 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 1007923 = 1511885) B1511885
theorem B1499485 : Blo 311834 1499485 := bstep (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) B562307
theorem B352651 : Blo 311834 352651 := bstep (se 1 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 352651 = 528977) B528977
theorem B1008089 : Blo 311834 1008089 := bstep (se 2 (by rfl) ⟨378033, by rfl⟩ : syracuseStep 1008089 = 756067) B756067
theorem B352759 : Blo 311834 352759 := bstep (se 1 (by rfl) ⟨264569, by rfl⟩ : syracuseStep 352759 = 529139) B529139
theorem B713369 : Blo 311834 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B352939 : Blo 311834 352939 := bstep (se 1 (by rfl) ⟨264704, by rfl⟩ : syracuseStep 352939 = 529409) B529409
theorem B353047 : Blo 311834 353047 := bstep (se 1 (by rfl) ⟨264785, by rfl⟩ : syracuseStep 353047 = 529571) B529571
theorem B1434433 : Blo 311834 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B353227 : Blo 311834 353227 := bstep (se 1 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 353227 = 529841) B529841
theorem B353335 : Blo 311834 353335 := bstep (se 1 (by rfl) ⟨265001, by rfl⟩ : syracuseStep 353335 = 530003) B530003
theorem B1598615 : Blo 311834 1598615 := bstep (se 1 (by rfl) ⟨1198961, by rfl⟩ : syracuseStep 1598615 = 2397923) B2397923
theorem B1008857 : Blo 311834 1008857 := bstep (se 2 (by rfl) ⟨378321, by rfl⟩ : syracuseStep 1008857 = 756643) B756643
theorem B353515 : Blo 311834 353515 := bstep (se 1 (by rfl) ⟨265136, by rfl⟩ : syracuseStep 353515 = 530273) B530273
theorem B353623 : Blo 311834 353623 := bstep (se 1 (by rfl) ⟨265217, by rfl⟩ : syracuseStep 353623 = 530435) B530435
theorem B353803 : Blo 311834 353803 := bstep (se 1 (by rfl) ⟨265352, by rfl⟩ : syracuseStep 353803 = 530705) B530705
theorem B1697345 : Blo 311834 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B1336925 : Blo 311834 1336925 := bstep (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) B501347
theorem B353911 : Blo 311834 353911 := bstep (se 1 (by rfl) ⟨265433, by rfl⟩ : syracuseStep 353911 = 530867) B530867
theorem B845515 : Blo 311834 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B1009369 : Blo 311834 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B354091 : Blo 311834 354091 := bstep (se 1 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 354091 = 531137) B531137
theorem B354199 : Blo 311834 354199 := bstep (se 1 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 354199 = 531299) B531299
theorem B21718961 : Blo 311834 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B354379 : Blo 311834 354379 := bstep (se 1 (by rfl) ⟨265784, by rfl⟩ : syracuseStep 354379 = 531569) B531569
theorem B354487 : Blo 311834 354487 := bstep (se 1 (by rfl) ⟨265865, by rfl⟩ : syracuseStep 354487 = 531731) B531731
theorem B1796417 : Blo 311834 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B2845003 : Blo 311834 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B354667 : Blo 311834 354667 := bstep (se 1 (by rfl) ⟨266000, by rfl⟩ : syracuseStep 354667 = 532001) B532001
theorem B354775 : Blo 311834 354775 := bstep (se 1 (by rfl) ⟨266081, by rfl⟩ : syracuseStep 354775 = 532163) B532163
theorem B4549081 : Blo 311834 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B715393 : Blo 311834 715393 := bstep (se 2 (by rfl) ⟨268272, by rfl⟩ : syracuseStep 715393 = 536545) B536545
theorem B354955 : Blo 311834 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B355063 : Blo 311834 355063 := bstep (se 1 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 355063 = 532595) B532595
theorem B1010497 : Blo 311834 1010497 := bstep (se 2 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 1010497 = 757873) B757873
theorem B355243 : Blo 311834 355243 := bstep (se 1 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 355243 = 532865) B532865
theorem B912691 : Blo 311834 912691 := bstep (se 1 (by rfl) ⟨684518, by rfl⟩ : syracuseStep 912691 = 1369037) B1369037
theorem B1273495 : Blo 311834 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2682629 : Blo 311834 2682629 := bstep (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) B502993
theorem B2387717 : Blo 311834 2387717 := bstep (se 4 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 2387717 = 447697) B447697
theorem B8056907 : Blo 311834 8056907 := bstep (se 1 (by rfl) ⟨6042680, by rfl⟩ : syracuseStep 8056907 = 12085361) B12085361
theorem B1339523 : Blo 311834 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B6942871 : Blo 311834 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B2846897 : Blo 311834 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B2683313 : Blo 311834 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B717527 : Blo 311834 717527 := bstep (se 1 (by rfl) ⟨538145, by rfl⟩ : syracuseStep 717527 = 1076291) B1076291
theorem B2684339 : Blo 311834 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B3601955 : Blo 311834 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B358391 : Blo 311834 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B2390147 : Blo 311834 2390147 := bstep (se 1 (by rfl) ⟨1792610, by rfl⟩ : syracuseStep 2390147 = 3585221) B3585221
theorem B424153 : Blo 311834 424153 := bstep (se 2 (by rfl) ⟨159057, by rfl⟩ : syracuseStep 424153 = 318115) B318115
theorem B1440089 : Blo 311834 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B2259377 : Blo 311834 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B752203 : Blo 311834 752203 := bstep (se 1 (by rfl) ⟨564152, by rfl⟩ : syracuseStep 752203 = 1128305) B1128305
theorem B752435 : Blo 311834 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B1899395 : Blo 311834 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B424855 : Blo 311834 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B720065 : Blo 311834 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B14548373 : Blo 311834 14548373 := bstep (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) B681955
theorem B7241309 : Blo 311834 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B1343297 : Blo 311834 1343297 := bstep (se 2 (by rfl) ⟨503736, by rfl⟩ : syracuseStep 1343297 = 1007473) B1007473
theorem B851905 : Blo 311834 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B52396145 : Blo 311834 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B6750449 : Blo 311834 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B3572099 : Blo 311834 3572099 := bstep (se 1 (by rfl) ⟨2679074, by rfl⟩ : syracuseStep 3572099 = 5358149) B5358149
theorem B754067 : Blo 311834 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B1343897 : Blo 311834 1343897 := bstep (se 2 (by rfl) ⟨503961, by rfl⟩ : syracuseStep 1343897 = 1007923) B1007923
theorem B1999313 : Blo 311834 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B1999363 : Blo 311834 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B1901825 : Blo 311834 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B6423907 : Blo 311834 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B2885149 : Blo 311834 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B3606059 : Blo 311834 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B7603789 : Blo 311834 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B394895 : Blo 311834 394895 := bstep (se 1 (by rfl) ⟨296171, by rfl⟩ : syracuseStep 394895 = 592343) B592343
theorem B952079 : Blo 311834 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B526351 : Blo 311834 526351 := bstep (se 1 (by rfl) ⟨394763, by rfl⟩ : syracuseStep 526351 = 789527) B789527
theorem B1706255 : Blo 311834 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1345825 : Blo 311834 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B2001287 : Blo 311834 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B592427 : Blo 311834 592427 := bstep (se 1 (by rfl) ⟨444320, by rfl⟩ : syracuseStep 592427 = 888641) B888641
theorem B526891 : Blo 311834 526891 := bstep (se 1 (by rfl) ⟨395168, by rfl⟩ : syracuseStep 526891 = 790337) B790337
theorem B527033 : Blo 311834 527033 := bstep (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) B395275
theorem B789335 : Blo 311834 789335 := bstep (se 1 (by rfl) ⟨592001, by rfl⟩ : syracuseStep 789335 = 1184003) B1184003
theorem B789547 : Blo 311834 789547 := bstep (se 1 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 789547 = 1184321) B1184321
theorem B789689 : Blo 311834 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B6065441 : Blo 311834 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B527735 : Blo 311834 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B953857 : Blo 311834 953857 := bstep (se 2 (by rfl) ⟨357696, by rfl⟩ : syracuseStep 953857 = 715393) B715393
theorem B757259 : Blo 311834 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B2887235 : Blo 311834 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B593543 : Blo 311834 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B1969921 : Blo 311834 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1347329 : Blo 311834 1347329 := bstep (se 2 (by rfl) ⟨505248, by rfl⟩ : syracuseStep 1347329 = 1010497) B1010497
theorem B528187 : Blo 311834 528187 := bstep (se 1 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 528187 = 792281) B792281
theorem B528329 : Blo 311834 528329 := bstep (se 2 (by rfl) ⟨198123, by rfl⟩ : syracuseStep 528329 = 396247) B396247
theorem B888833 : Blo 311834 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B1347671 : Blo 311834 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B9605213 : Blo 311834 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B594067 : Blo 311834 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B790681 : Blo 311834 790681 := bstep (se 2 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 790681 = 593011) B593011
theorem B790843 : Blo 311834 790843 := bstep (se 1 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 790843 = 1186265) B1186265
theorem B3019153 : Blo 311834 3019153 := bstep (se 2 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 3019153 = 2264365) B2264365
theorem B1216921 : Blo 311834 1216921 := bstep (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) B912691
theorem B889289 : Blo 311834 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B790985 : Blo 311834 790985 := bstep (se 2 (by rfl) ⟨296619, by rfl⟩ : syracuseStep 790985 = 593239) B593239
theorem B397867 : Blo 311834 397867 := bstep (se 1 (by rfl) ⟨298400, by rfl⟩ : syracuseStep 397867 = 596801) B596801
theorem B529031 : Blo 311834 529031 := bstep (se 1 (by rfl) ⟨396773, by rfl⟩ : syracuseStep 529031 = 793547) B793547
theorem B3904271 : Blo 311834 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B791329 : Blo 311834 791329 := bstep (se 2 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 791329 = 593497) B593497
theorem B2265893 : Blo 311834 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B889643 : Blo 311834 889643 := bstep (se 1 (by rfl) ⟨667232, by rfl⟩ : syracuseStep 889643 = 1334465) B1334465
theorem B4821875 : Blo 311834 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B1053593 : Blo 311834 1053593 := bstep (se 2 (by rfl) ⟨395097, by rfl⟩ : syracuseStep 1053593 = 790195) B790195
theorem B857099 : Blo 311834 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B890041 : Blo 311834 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B529679 : Blo 311834 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B595259 : Blo 311834 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B955709 : Blo 311834 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B791927 : Blo 311834 791927 := bstep (se 1 (by rfl) ⟨593945, by rfl⟩ : syracuseStep 791927 = 1187891) B1187891
theorem B398839 : Blo 311834 398839 := bstep (se 1 (by rfl) ⟨299129, by rfl⟩ : syracuseStep 398839 = 598259) B598259
theorem B1054295 : Blo 311834 1054295 := bstep (se 1 (by rfl) ⟨790721, by rfl⟩ : syracuseStep 1054295 = 1581443) B1581443
theorem B1578689 : Blo 311834 1578689 := bstep (se 2 (by rfl) ⟨592008, by rfl⟩ : syracuseStep 1578689 = 1184017) B1184017
theorem B595745 : Blo 311834 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B530219 : Blo 311834 530219 := bstep (se 1 (by rfl) ⟨397664, by rfl⟩ : syracuseStep 530219 = 795329) B795329
theorem B399163 : Blo 311834 399163 := bstep (se 1 (by rfl) ⟨299372, by rfl⟩ : syracuseStep 399163 = 598745) B598745
theorem B1513363 : Blo 311834 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B596011 : Blo 311834 596011 := bstep (se 1 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 596011 = 894017) B894017
theorem B1251389 : Blo 311834 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B1054781 : Blo 311834 1054781 := bstep (se 3 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 1054781 = 395543) B395543
theorem B3381365 : Blo 311834 3381365 := bstep (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) B317003
theorem B530617 : Blo 311834 530617 := bstep (se 2 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 530617 = 397963) B397963
theorem B4921613 : Blo 311834 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B891283 : Blo 311834 891283 := bstep (se 1 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 891283 = 1336925) B1336925
theorem B793223 : Blo 311834 793223 := bstep (se 1 (by rfl) ⟨594917, by rfl⟩ : syracuseStep 793223 = 1189835) B1189835
theorem B793273 : Blo 311834 793273 := bstep (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) B594955
theorem B531319 : Blo 311834 531319 := bstep (se 1 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 531319 = 796979) B796979
theorem B1579985 : Blo 311834 1579985 := bstep (se 2 (by rfl) ⟨592494, by rfl⟩ : syracuseStep 1579985 = 1184989) B1184989
theorem B531515 : Blo 311834 531515 := bstep (se 1 (by rfl) ⟨398636, by rfl⟩ : syracuseStep 531515 = 797273) B797273
theorem B597127 : Blo 311834 597127 := bstep (se 1 (by rfl) ⟨447845, by rfl⟩ : syracuseStep 597127 = 895691) B895691
theorem B793871 : Blo 311834 793871 := bstep (se 1 (by rfl) ⟨595403, by rfl⟩ : syracuseStep 793871 = 1190807) B1190807
theorem B1187207 : Blo 311834 1187207 := bstep (se 1 (by rfl) ⟨890405, by rfl⟩ : syracuseStep 1187207 = 1780811) B1780811
theorem B1056185 : Blo 311834 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B531913 : Blo 311834 531913 := bstep (se 2 (by rfl) ⟨199467, by rfl⟩ : syracuseStep 531913 = 398935) B398935
theorem B597689 : Blo 311834 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B13573889 : Blo 311834 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B794569 : Blo 311834 794569 := bstep (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) B595927
theorem B1056779 : Blo 311834 1056779 := bstep (se 1 (by rfl) ⟨792584, by rfl⟩ : syracuseStep 1056779 = 1585169) B1585169
theorem B892957 : Blo 311834 892957 := bstep (se 3 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 892957 = 334859) B334859
theorem B893015 : Blo 311834 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B794711 : Blo 311834 794711 := bstep (se 1 (by rfl) ⟨596033, by rfl⟩ : syracuseStep 794711 = 1192067) B1192067
theorem B1056887 : Blo 311834 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B532615 : Blo 311834 532615 := bstep (se 1 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 532615 = 798923) B798923
theorem B565537 : Blo 311834 565537 := bstep (se 2 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 565537 = 424153) B424153
theorem B1057481 : Blo 311834 1057481 := bstep (se 2 (by rfl) ⟨396555, by rfl⟩ : syracuseStep 1057481 = 793111) B793111
theorem B467771 : Blo 311834 467771 := bstep (se 1 (by rfl) ⟨350828, by rfl⟩ : syracuseStep 467771 = 701657) B701657
theorem B598843 : Blo 311834 598843 := bstep (se 1 (by rfl) ⟨449132, by rfl⟩ : syracuseStep 598843 = 898265) B898265
theorem B467831 : Blo 311834 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B467855 : Blo 311834 467855 := bstep (se 1 (by rfl) ⟨350891, by rfl⟩ : syracuseStep 467855 = 701783) B701783
theorem B467897 : Blo 311834 467897 := bstep (se 2 (by rfl) ⟨175461, by rfl⟩ : syracuseStep 467897 = 350923) B350923
theorem B500681 : Blo 311834 500681 := bstep (se 2 (by rfl) ⟨187755, by rfl⟩ : syracuseStep 500681 = 375511) B375511
theorem B467975 : Blo 311834 467975 := bstep (se 1 (by rfl) ⟨350981, by rfl⟩ : syracuseStep 467975 = 701963) B701963
theorem B1582091 : Blo 311834 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B468011 : Blo 311834 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B468041 : Blo 311834 468041 := bstep (se 2 (by rfl) ⟨175515, by rfl⟩ : syracuseStep 468041 = 351031) B351031
theorem B1582253 : Blo 311834 1582253 := bstep (se 3 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 1582253 = 593345) B593345
theorem B468155 : Blo 311834 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B1516745 : Blo 311834 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B468215 : Blo 311834 468215 := bstep (se 1 (by rfl) ⟨351161, by rfl⟩ : syracuseStep 468215 = 702323) B702323
theorem B468239 : Blo 311834 468239 := bstep (se 1 (by rfl) ⟨351179, by rfl⟩ : syracuseStep 468239 = 702359) B702359
theorem B599329 : Blo 311834 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B468281 : Blo 311834 468281 := bstep (se 2 (by rfl) ⟨175605, by rfl⟩ : syracuseStep 468281 = 351211) B351211
theorem B468359 : Blo 311834 468359 := bstep (se 1 (by rfl) ⟨351269, by rfl⟩ : syracuseStep 468359 = 702539) B702539
theorem B1058183 : Blo 311834 1058183 := bstep (se 1 (by rfl) ⟨793637, by rfl⟩ : syracuseStep 1058183 = 1587275) B1587275
theorem B468395 : Blo 311834 468395 := bstep (se 1 (by rfl) ⟨351296, by rfl⟩ : syracuseStep 468395 = 702593) B702593
theorem B468425 : Blo 311834 468425 := bstep (se 2 (by rfl) ⟨175659, by rfl⟩ : syracuseStep 468425 = 351319) B351319
theorem B468539 : Blo 311834 468539 := bstep (se 1 (by rfl) ⟨351404, by rfl⟩ : syracuseStep 468539 = 702809) B702809
theorem B960059 : Blo 311834 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B468599 : Blo 311834 468599 := bstep (se 1 (by rfl) ⟨351449, by rfl⟩ : syracuseStep 468599 = 702899) B702899
theorem B468623 : Blo 311834 468623 := bstep (se 1 (by rfl) ⟨351467, by rfl⟩ : syracuseStep 468623 = 702935) B702935
theorem B468665 : Blo 311834 468665 := bstep (se 2 (by rfl) ⟨175749, by rfl⟩ : syracuseStep 468665 = 351499) B351499
theorem B894665 : Blo 311834 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B1058561 : Blo 311834 1058561 := bstep (se 2 (by rfl) ⟨396960, by rfl⟩ : syracuseStep 1058561 = 793921) B793921
theorem B468743 : Blo 311834 468743 := bstep (se 1 (by rfl) ⟨351557, by rfl⟩ : syracuseStep 468743 = 703115) B703115
theorem B1124111 : Blo 311834 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B468779 : Blo 311834 468779 := bstep (se 1 (by rfl) ⟨351584, by rfl⟩ : syracuseStep 468779 = 703169) B703169
theorem B468809 : Blo 311834 468809 := bstep (se 2 (by rfl) ⟨175803, by rfl⟩ : syracuseStep 468809 = 351607) B351607
theorem B18425717 : Blo 311834 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B501623 : Blo 311834 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B3024803 : Blo 311834 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B468923 : Blo 311834 468923 := bstep (se 1 (by rfl) ⟨351692, by rfl⟩ : syracuseStep 468923 = 703385) B703385
theorem B468983 : Blo 311834 468983 := bstep (se 1 (by rfl) ⟨351737, by rfl⟩ : syracuseStep 468983 = 703475) B703475
theorem B469007 : Blo 311834 469007 := bstep (se 1 (by rfl) ⟨351755, by rfl⟩ : syracuseStep 469007 = 703511) B703511
theorem B1517591 : Blo 311834 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B469049 : Blo 311834 469049 := bstep (se 2 (by rfl) ⟨175893, by rfl⟩ : syracuseStep 469049 = 351787) B351787
theorem B796787 : Blo 311834 796787 := bstep (se 1 (by rfl) ⟨597590, by rfl⟩ : syracuseStep 796787 = 1195181) B1195181
theorem B469127 : Blo 311834 469127 := bstep (se 1 (by rfl) ⟨351845, by rfl⟩ : syracuseStep 469127 = 703691) B703691
theorem B469163 : Blo 311834 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B469193 : Blo 311834 469193 := bstep (se 2 (by rfl) ⟨175947, by rfl⟩ : syracuseStep 469193 = 351895) B351895
theorem B5384393 : Blo 311834 5384393 := bstep (se 2 (by rfl) ⟨2019147, by rfl⟩ : syracuseStep 5384393 = 4038295) B4038295
theorem B1911073 : Blo 311834 1911073 := bstep (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) B1433305
theorem B469307 : Blo 311834 469307 := bstep (se 1 (by rfl) ⟨351980, by rfl⟩ : syracuseStep 469307 = 703961) B703961
theorem B469367 : Blo 311834 469367 := bstep (se 1 (by rfl) ⟨352025, by rfl⟩ : syracuseStep 469367 = 704051) B704051
theorem B469391 : Blo 311834 469391 := bstep (se 1 (by rfl) ⟨352043, by rfl⟩ : syracuseStep 469391 = 704087) B704087
theorem B4827539 : Blo 311834 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B469433 : Blo 311834 469433 := bstep (se 2 (by rfl) ⟨176037, by rfl⟩ : syracuseStep 469433 = 352075) B352075
theorem B469511 : Blo 311834 469511 := bstep (se 1 (by rfl) ⟨352133, by rfl⟩ : syracuseStep 469511 = 704267) B704267
theorem B469547 : Blo 311834 469547 := bstep (se 1 (by rfl) ⟨352160, by rfl⟩ : syracuseStep 469547 = 704321) B704321
theorem B1059371 : Blo 311834 1059371 := bstep (se 1 (by rfl) ⟨794528, by rfl⟩ : syracuseStep 1059371 = 1589057) B1589057
theorem B895531 : Blo 311834 895531 := bstep (se 1 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 895531 = 1343297) B1343297
theorem B469577 : Blo 311834 469577 := bstep (se 2 (by rfl) ⟨176091, by rfl⟩ : syracuseStep 469577 = 352183) B352183
theorem B797303 : Blo 311834 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B469691 : Blo 311834 469691 := bstep (se 1 (by rfl) ⟨352268, by rfl⟩ : syracuseStep 469691 = 704537) B704537
theorem B469751 : Blo 311834 469751 := bstep (se 1 (by rfl) ⟨352313, by rfl⟩ : syracuseStep 469751 = 704627) B704627
theorem B1583873 : Blo 311834 1583873 := bstep (se 2 (by rfl) ⟨593952, by rfl⟩ : syracuseStep 1583873 = 1187905) B1187905
theorem B469775 : Blo 311834 469775 := bstep (se 1 (by rfl) ⟨352331, by rfl⟩ : syracuseStep 469775 = 704663) B704663
theorem B469817 : Blo 311834 469817 := bstep (se 2 (by rfl) ⟨176181, by rfl⟩ : syracuseStep 469817 = 352363) B352363
theorem B1616699 : Blo 311834 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B895805 : Blo 311834 895805 := bstep (se 3 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 895805 = 335927) B335927
theorem B469895 : Blo 311834 469895 := bstep (se 1 (by rfl) ⟨352421, by rfl⟩ : syracuseStep 469895 = 704843) B704843
theorem B469931 : Blo 311834 469931 := bstep (se 1 (by rfl) ⟨352448, by rfl⟩ : syracuseStep 469931 = 704897) B704897
theorem B469961 : Blo 311834 469961 := bstep (se 2 (by rfl) ⟨176235, by rfl⟩ : syracuseStep 469961 = 352471) B352471
theorem B470075 : Blo 311834 470075 := bstep (se 1 (by rfl) ⟨352556, by rfl⟩ : syracuseStep 470075 = 705113) B705113
theorem B470135 : Blo 311834 470135 := bstep (se 1 (by rfl) ⟨352601, by rfl⟩ : syracuseStep 470135 = 705203) B705203
theorem B470159 : Blo 311834 470159 := bstep (se 1 (by rfl) ⟨352619, by rfl⟩ : syracuseStep 470159 = 705239) B705239
theorem B896147 : Blo 311834 896147 := bstep (se 1 (by rfl) ⟨672110, by rfl⟩ : syracuseStep 896147 = 1344221) B1344221
theorem B470201 : Blo 311834 470201 := bstep (se 2 (by rfl) ⟨176325, by rfl⟩ : syracuseStep 470201 = 352651) B352651
theorem B470279 : Blo 311834 470279 := bstep (se 1 (by rfl) ⟨352709, by rfl⟩ : syracuseStep 470279 = 705419) B705419
theorem B470315 : Blo 311834 470315 := bstep (se 1 (by rfl) ⟨352736, by rfl⟩ : syracuseStep 470315 = 705473) B705473
theorem B470345 : Blo 311834 470345 := bstep (se 2 (by rfl) ⟨176379, by rfl⟩ : syracuseStep 470345 = 352759) B352759
theorem B568723 : Blo 311834 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B2272697 : Blo 311834 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B470459 : Blo 311834 470459 := bstep (se 1 (by rfl) ⟨352844, by rfl⟩ : syracuseStep 470459 = 705689) B705689
theorem B470519 : Blo 311834 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B470543 : Blo 311834 470543 := bstep (se 1 (by rfl) ⟨352907, by rfl⟩ : syracuseStep 470543 = 705815) B705815
theorem B1584683 : Blo 311834 1584683 := bstep (se 1 (by rfl) ⟨1188512, by rfl⟩ : syracuseStep 1584683 = 2377025) B2377025
theorem B470585 : Blo 311834 470585 := bstep (se 2 (by rfl) ⟨176469, by rfl⟩ : syracuseStep 470585 = 352939) B352939
theorem B798295 : Blo 311834 798295 := bstep (se 1 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 798295 = 1197443) B1197443
theorem B2010743 : Blo 311834 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B470663 : Blo 311834 470663 := bstep (se 1 (by rfl) ⟨352997, by rfl⟩ : syracuseStep 470663 = 705995) B705995
theorem B470699 : Blo 311834 470699 := bstep (se 1 (by rfl) ⟨353024, by rfl⟩ : syracuseStep 470699 = 706049) B706049
theorem B470729 : Blo 311834 470729 := bstep (se 2 (by rfl) ⟨176523, by rfl⟩ : syracuseStep 470729 = 353047) B353047
theorem B1912577 : Blo 311834 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B470843 : Blo 311834 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B1060667 : Blo 311834 1060667 := bstep (se 1 (by rfl) ⟨795500, by rfl⟩ : syracuseStep 1060667 = 1591001) B1591001
theorem B470903 : Blo 311834 470903 := bstep (se 1 (by rfl) ⟨353177, by rfl⟩ : syracuseStep 470903 = 706355) B706355
theorem B798599 : Blo 311834 798599 := bstep (se 1 (by rfl) ⟨598949, by rfl⟩ : syracuseStep 798599 = 1197899) B1197899
theorem B470927 : Blo 311834 470927 := bstep (se 1 (by rfl) ⟨353195, by rfl⟩ : syracuseStep 470927 = 706391) B706391
theorem B470969 : Blo 311834 470969 := bstep (se 2 (by rfl) ⟨176613, by rfl⟩ : syracuseStep 470969 = 353227) B353227
theorem B471047 : Blo 311834 471047 := bstep (se 1 (by rfl) ⟨353285, by rfl⟩ : syracuseStep 471047 = 706571) B706571
theorem B798731 : Blo 311834 798731 := bstep (se 1 (by rfl) ⟨599048, by rfl⟩ : syracuseStep 798731 = 1198097) B1198097
theorem B6467597 : Blo 311834 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B471083 : Blo 311834 471083 := bstep (se 1 (by rfl) ⟨353312, by rfl⟩ : syracuseStep 471083 = 706625) B706625
theorem B471113 : Blo 311834 471113 := bstep (se 2 (by rfl) ⟨176667, by rfl⟩ : syracuseStep 471113 = 353335) B353335
theorem B471227 : Blo 311834 471227 := bstep (se 1 (by rfl) ⟨353420, by rfl⟩ : syracuseStep 471227 = 706841) B706841
theorem B471287 : Blo 311834 471287 := bstep (se 1 (by rfl) ⟨353465, by rfl⟩ : syracuseStep 471287 = 706931) B706931
theorem B471311 : Blo 311834 471311 := bstep (se 1 (by rfl) ⟨353483, by rfl⟩ : syracuseStep 471311 = 706967) B706967
theorem B1061153 : Blo 311834 1061153 := bstep (se 2 (by rfl) ⟨397932, by rfl⟩ : syracuseStep 1061153 = 795865) B795865
theorem B471353 : Blo 311834 471353 := bstep (se 2 (by rfl) ⟨176757, by rfl⟩ : syracuseStep 471353 = 353515) B353515
theorem B471431 : Blo 311834 471431 := bstep (se 1 (by rfl) ⟨353573, by rfl⟩ : syracuseStep 471431 = 707147) B707147
theorem B471467 : Blo 311834 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B471497 : Blo 311834 471497 := bstep (se 2 (by rfl) ⟨176811, by rfl⟩ : syracuseStep 471497 = 353623) B353623
theorem B799247 : Blo 311834 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B471611 : Blo 311834 471611 := bstep (se 1 (by rfl) ⟨353708, by rfl⟩ : syracuseStep 471611 = 707417) B707417
theorem B471671 : Blo 311834 471671 := bstep (se 1 (by rfl) ⟨353753, by rfl⟩ : syracuseStep 471671 = 707507) B707507
theorem B471695 : Blo 311834 471695 := bstep (se 1 (by rfl) ⟨353771, by rfl⟩ : syracuseStep 471695 = 707543) B707543
theorem B799379 : Blo 311834 799379 := bstep (se 1 (by rfl) ⟨599534, by rfl⟩ : syracuseStep 799379 = 1199069) B1199069
theorem B471737 : Blo 311834 471737 := bstep (se 2 (by rfl) ⟨176901, by rfl⟩ : syracuseStep 471737 = 353803) B353803
theorem B471815 : Blo 311834 471815 := bstep (se 1 (by rfl) ⟨353861, by rfl⟩ : syracuseStep 471815 = 707723) B707723
theorem B471851 : Blo 311834 471851 := bstep (se 1 (by rfl) ⟨353888, by rfl⟩ : syracuseStep 471851 = 707777) B707777
theorem B1782587 : Blo 311834 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B1585979 : Blo 311834 1585979 := bstep (se 1 (by rfl) ⟨1189484, by rfl⟩ : syracuseStep 1585979 = 2378969) B2378969
theorem B471881 : Blo 311834 471881 := bstep (se 2 (by rfl) ⟨176955, by rfl⟩ : syracuseStep 471881 = 353911) B353911
theorem B1061747 : Blo 311834 1061747 := bstep (se 1 (by rfl) ⟨796310, by rfl⟩ : syracuseStep 1061747 = 1592621) B1592621
theorem B1127353 : Blo 311834 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B471995 : Blo 311834 471995 := bstep (se 1 (by rfl) ⟨353996, by rfl⟩ : syracuseStep 471995 = 707993) B707993
theorem B1586141 : Blo 311834 1586141 := bstep (se 3 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 1586141 = 594803) B594803
theorem B472055 : Blo 311834 472055 := bstep (se 1 (by rfl) ⟨354041, by rfl⟩ : syracuseStep 472055 = 708083) B708083
theorem B472079 : Blo 311834 472079 := bstep (se 1 (by rfl) ⟨354059, by rfl⟩ : syracuseStep 472079 = 708119) B708119
theorem B1127467 : Blo 311834 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B472121 : Blo 311834 472121 := bstep (se 2 (by rfl) ⟨177045, by rfl⟩ : syracuseStep 472121 = 354091) B354091
theorem B472199 : Blo 311834 472199 := bstep (se 1 (by rfl) ⟨354149, by rfl⟩ : syracuseStep 472199 = 708299) B708299
theorem B504967 : Blo 311834 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B472235 : Blo 311834 472235 := bstep (se 1 (by rfl) ⟨354176, by rfl⟩ : syracuseStep 472235 = 708353) B708353
theorem B668873 : Blo 311834 668873 := bstep (se 2 (by rfl) ⟨250827, by rfl⟩ : syracuseStep 668873 = 501655) B501655
theorem B472265 : Blo 311834 472265 := bstep (se 2 (by rfl) ⟨177099, by rfl⟩ : syracuseStep 472265 = 354199) B354199
theorem B701711 : Blo 311834 701711 := bstep (se 1 (by rfl) ⟨526283, by rfl⟩ : syracuseStep 701711 = 1052567) B1052567
theorem B701729 : Blo 311834 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B1586465 : Blo 311834 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B472379 : Blo 311834 472379 := bstep (se 1 (by rfl) ⟨354284, by rfl⟩ : syracuseStep 472379 = 708569) B708569
theorem B898391 : Blo 311834 898391 := bstep (se 1 (by rfl) ⟨673793, by rfl⟩ : syracuseStep 898391 = 1347587) B1347587
theorem B472439 : Blo 311834 472439 := bstep (se 1 (by rfl) ⟨354329, by rfl⟩ : syracuseStep 472439 = 708659) B708659
theorem B472463 : Blo 311834 472463 := bstep (se 1 (by rfl) ⟨354347, by rfl⟩ : syracuseStep 472463 = 708695) B708695
theorem B472505 : Blo 311834 472505 := bstep (se 2 (by rfl) ⟨177189, by rfl⟩ : syracuseStep 472505 = 354379) B354379
theorem B3225091 : Blo 311834 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B472583 : Blo 311834 472583 := bstep (se 1 (by rfl) ⟨354437, by rfl⟩ : syracuseStep 472583 = 708875) B708875
theorem B472619 : Blo 311834 472619 := bstep (se 1 (by rfl) ⟨354464, by rfl⟩ : syracuseStep 472619 = 708929) B708929
theorem B472649 : Blo 311834 472649 := bstep (se 2 (by rfl) ⟨177243, by rfl⟩ : syracuseStep 472649 = 354487) B354487
theorem B702071 : Blo 311834 702071 := bstep (se 1 (by rfl) ⟨526553, by rfl⟩ : syracuseStep 702071 = 1053107) B1053107
theorem B472763 : Blo 311834 472763 := bstep (se 1 (by rfl) ⟨354572, by rfl⟩ : syracuseStep 472763 = 709145) B709145
theorem B472823 : Blo 311834 472823 := bstep (se 1 (by rfl) ⟨354617, by rfl⟩ : syracuseStep 472823 = 709235) B709235
theorem B472847 : Blo 311834 472847 := bstep (se 1 (by rfl) ⟨354635, by rfl⟩ : syracuseStep 472847 = 709271) B709271
theorem B702251 : Blo 311834 702251 := bstep (se 1 (by rfl) ⟨526688, by rfl⟩ : syracuseStep 702251 = 1053377) B1053377
theorem B472889 : Blo 311834 472889 := bstep (se 2 (by rfl) ⟨177333, by rfl⟩ : syracuseStep 472889 = 354667) B354667
theorem B472967 : Blo 311834 472967 := bstep (se 1 (by rfl) ⟨354725, by rfl⟩ : syracuseStep 472967 = 709451) B709451
theorem B473003 : Blo 311834 473003 := bstep (se 1 (by rfl) ⟨354752, by rfl⟩ : syracuseStep 473003 = 709505) B709505
theorem B473033 : Blo 311834 473033 := bstep (se 2 (by rfl) ⟨177387, by rfl⟩ : syracuseStep 473033 = 354775) B354775
theorem B473147 : Blo 311834 473147 := bstep (se 1 (by rfl) ⟨354860, by rfl⟩ : syracuseStep 473147 = 709721) B709721
theorem B473207 : Blo 311834 473207 := bstep (se 1 (by rfl) ⟨354905, by rfl⟩ : syracuseStep 473207 = 709811) B709811
theorem B473231 : Blo 311834 473231 := bstep (se 1 (by rfl) ⟨354923, by rfl⟩ : syracuseStep 473231 = 709847) B709847
theorem B702611 : Blo 311834 702611 := bstep (se 1 (by rfl) ⟨526958, by rfl⟩ : syracuseStep 702611 = 1053917) B1053917
theorem B473273 : Blo 311834 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B702665 : Blo 311834 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B1784045 : Blo 311834 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B1587437 : Blo 311834 1587437 := bstep (se 3 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 1587437 = 595289) B595289
theorem B473351 : Blo 311834 473351 := bstep (se 1 (by rfl) ⟨355013, by rfl⟩ : syracuseStep 473351 = 710027) B710027
theorem B473387 : Blo 311834 473387 := bstep (se 1 (by rfl) ⟨355040, by rfl⟩ : syracuseStep 473387 = 710081) B710081
theorem B473417 : Blo 311834 473417 := bstep (se 2 (by rfl) ⟨177531, by rfl⟩ : syracuseStep 473417 = 355063) B355063
theorem B473531 : Blo 311834 473531 := bstep (se 1 (by rfl) ⟨355148, by rfl⟩ : syracuseStep 473531 = 710297) B710297
theorem B2374109 : Blo 311834 2374109 := bstep (se 3 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 2374109 = 890291) B890291
theorem B473591 : Blo 311834 473591 := bstep (se 1 (by rfl) ⟨355193, by rfl⟩ : syracuseStep 473591 = 710387) B710387
theorem B3258883 : Blo 311834 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B473615 : Blo 311834 473615 := bstep (se 1 (by rfl) ⟨355211, by rfl⟩ : syracuseStep 473615 = 710423) B710423
theorem B473657 : Blo 311834 473657 := bstep (se 2 (by rfl) ⟨177621, by rfl⟩ : syracuseStep 473657 = 355243) B355243
theorem B3586679 : Blo 311834 3586679 := bstep (se 1 (by rfl) ⟨2690009, by rfl⟩ : syracuseStep 3586679 = 5380019) B5380019
theorem B473735 : Blo 311834 473735 := bstep (se 1 (by rfl) ⟨355301, by rfl⟩ : syracuseStep 473735 = 710603) B710603
theorem B703367 : Blo 311834 703367 := bstep (se 1 (by rfl) ⟨527525, by rfl⟩ : syracuseStep 703367 = 1055051) B1055051
theorem B1588247 : Blo 311834 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B703547 : Blo 311834 703547 := bstep (se 1 (by rfl) ⟨527660, by rfl⟩ : syracuseStep 703547 = 1055321) B1055321
theorem B3423293 : Blo 311834 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B670855 : Blo 311834 670855 := bstep (se 1 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 670855 = 1006283) B1006283
theorem B703673 : Blo 311834 703673 := bstep (se 2 (by rfl) ⟨263877, by rfl⟩ : syracuseStep 703673 = 527755) B527755
theorem B2014409 : Blo 311834 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B1064339 : Blo 311834 1064339 := bstep (se 1 (by rfl) ⟨798254, by rfl⟩ : syracuseStep 1064339 = 1596509) B1596509
theorem B704015 : Blo 311834 704015 := bstep (se 1 (by rfl) ⟨528011, by rfl⟩ : syracuseStep 704015 = 1056023) B1056023
theorem B704033 : Blo 311834 704033 := bstep (se 2 (by rfl) ⟨264012, by rfl⟩ : syracuseStep 704033 = 528025) B528025
theorem B704375 : Blo 311834 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B1195985 : Blo 311834 1195985 := bstep (se 2 (by rfl) ⟨448494, by rfl⟩ : syracuseStep 1195985 = 896989) B896989
theorem B704555 : Blo 311834 704555 := bstep (se 1 (by rfl) ⟨528416, by rfl⟩ : syracuseStep 704555 = 1056833) B1056833
theorem B9257161 : Blo 311834 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B672059 : Blo 311834 672059 := bstep (se 1 (by rfl) ⟨504044, by rfl⟩ : syracuseStep 672059 = 1008089) B1008089
theorem B704915 : Blo 311834 704915 := bstep (se 1 (by rfl) ⟨528686, by rfl⟩ : syracuseStep 704915 = 1057373) B1057373
theorem B1196441 : Blo 311834 1196441 := bstep (se 2 (by rfl) ⟨448665, by rfl⟩ : syracuseStep 1196441 = 897331) B897331
theorem B475579 : Blo 311834 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B704969 : Blo 311834 704969 := bstep (se 2 (by rfl) ⟨264363, by rfl⟩ : syracuseStep 704969 = 528727) B528727
theorem B1688087 : Blo 311834 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B999965 : Blo 311834 999965 := bstep (se 3 (by rfl) ⟨187493, by rfl⟩ : syracuseStep 999965 = 374987) B374987
theorem B311867 : Blo 311834 311867 := bstep (se 1 (by rfl) ⟨233900, by rfl⟩ : syracuseStep 311867 = 467801) B467801
theorem B311943 : Blo 311834 311943 := bstep (se 1 (by rfl) ⟨233957, by rfl⟩ : syracuseStep 311943 = 467915) B467915
theorem B311951 : Blo 311834 311951 := bstep (se 1 (by rfl) ⟨233963, by rfl⟩ : syracuseStep 311951 = 467927) B467927
theorem B311995 : Blo 311834 311995 := bstep (se 1 (by rfl) ⟨233996, by rfl⟩ : syracuseStep 311995 = 467993) B467993
theorem B312071 : Blo 311834 312071 := bstep (se 1 (by rfl) ⟨234053, by rfl⟩ : syracuseStep 312071 = 468107) B468107
theorem B312079 : Blo 311834 312079 := bstep (se 1 (by rfl) ⟨234059, by rfl⟩ : syracuseStep 312079 = 468119) B468119
theorem B1065743 : Blo 311834 1065743 := bstep (se 1 (by rfl) ⟨799307, by rfl⟩ : syracuseStep 1065743 = 1598615) B1598615
theorem B312123 : Blo 311834 312123 := bstep (se 1 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 312123 = 468185) B468185
theorem B672571 : Blo 311834 672571 := bstep (se 1 (by rfl) ⟨504428, by rfl⟩ : syracuseStep 672571 = 1008857) B1008857
theorem B312199 : Blo 311834 312199 := bstep (se 1 (by rfl) ⟨234149, by rfl⟩ : syracuseStep 312199 = 468299) B468299
theorem B312207 : Blo 311834 312207 := bstep (se 1 (by rfl) ⟨234155, by rfl⟩ : syracuseStep 312207 = 468311) B468311
theorem B312251 : Blo 311834 312251 := bstep (se 1 (by rfl) ⟨234188, by rfl⟩ : syracuseStep 312251 = 468377) B468377
theorem B312327 : Blo 311834 312327 := bstep (se 1 (by rfl) ⟨234245, by rfl⟩ : syracuseStep 312327 = 468491) B468491
theorem B312335 : Blo 311834 312335 := bstep (se 1 (by rfl) ⟨234251, by rfl⟩ : syracuseStep 312335 = 468503) B468503
theorem B1131563 : Blo 311834 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B312379 : Blo 311834 312379 := bstep (se 1 (by rfl) ⟨234284, by rfl⟩ : syracuseStep 312379 = 468569) B468569
theorem B574523 : Blo 311834 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B312455 : Blo 311834 312455 := bstep (se 1 (by rfl) ⟨234341, by rfl⟩ : syracuseStep 312455 = 468683) B468683
theorem B705671 : Blo 311834 705671 := bstep (se 1 (by rfl) ⟨529253, by rfl⟩ : syracuseStep 705671 = 1058507) B1058507
theorem B312463 : Blo 311834 312463 := bstep (se 1 (by rfl) ⟨234347, by rfl⟩ : syracuseStep 312463 = 468695) B468695
theorem B312507 : Blo 311834 312507 := bstep (se 1 (by rfl) ⟨234380, by rfl⟩ : syracuseStep 312507 = 468761) B468761
theorem B312583 : Blo 311834 312583 := bstep (se 1 (by rfl) ⟨234437, by rfl⟩ : syracuseStep 312583 = 468875) B468875
theorem B312591 : Blo 311834 312591 := bstep (se 1 (by rfl) ⟨234443, by rfl⟩ : syracuseStep 312591 = 468887) B468887
theorem B312635 : Blo 311834 312635 := bstep (se 1 (by rfl) ⟨234476, by rfl⟩ : syracuseStep 312635 = 468953) B468953
theorem B705851 : Blo 311834 705851 := bstep (se 1 (by rfl) ⟨529388, by rfl⟩ : syracuseStep 705851 = 1058777) B1058777
theorem B312711 : Blo 311834 312711 := bstep (se 1 (by rfl) ⟨234533, by rfl⟩ : syracuseStep 312711 = 469067) B469067
theorem B312719 : Blo 311834 312719 := bstep (se 1 (by rfl) ⟨234539, by rfl⟩ : syracuseStep 312719 = 469079) B469079
theorem B705977 : Blo 311834 705977 := bstep (se 2 (by rfl) ⟨264741, by rfl⟩ : syracuseStep 705977 = 529483) B529483
theorem B312763 : Blo 311834 312763 := bstep (se 1 (by rfl) ⟨234572, by rfl⟩ : syracuseStep 312763 = 469145) B469145
theorem B312839 : Blo 311834 312839 := bstep (se 1 (by rfl) ⟨234629, by rfl⟩ : syracuseStep 312839 = 469259) B469259
theorem B312847 : Blo 311834 312847 := bstep (se 1 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 312847 = 469271) B469271
theorem B1197611 : Blo 311834 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B312891 : Blo 311834 312891 := bstep (se 1 (by rfl) ⟨234668, by rfl⟩ : syracuseStep 312891 = 469337) B469337
theorem B312967 : Blo 311834 312967 := bstep (se 1 (by rfl) ⟨234725, by rfl⟩ : syracuseStep 312967 = 469451) B469451
theorem B312975 : Blo 311834 312975 := bstep (se 1 (by rfl) ⟨234731, by rfl⟩ : syracuseStep 312975 = 469463) B469463
theorem B313019 : Blo 311834 313019 := bstep (se 1 (by rfl) ⟨234764, by rfl⟩ : syracuseStep 313019 = 469529) B469529
theorem B1689281 : Blo 311834 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B4572929 : Blo 311834 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B313095 : Blo 311834 313095 := bstep (se 1 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 313095 = 469643) B469643
theorem B313103 : Blo 311834 313103 := bstep (se 1 (by rfl) ⟨234827, by rfl⟩ : syracuseStep 313103 = 469655) B469655
theorem B706319 : Blo 311834 706319 := bstep (se 1 (by rfl) ⟨529739, by rfl⟩ : syracuseStep 706319 = 1059479) B1059479
theorem B706337 : Blo 311834 706337 := bstep (se 2 (by rfl) ⟨264876, by rfl⟩ : syracuseStep 706337 = 529753) B529753
theorem B313147 : Blo 311834 313147 := bstep (se 1 (by rfl) ⟨234860, by rfl⟩ : syracuseStep 313147 = 469721) B469721
theorem B313223 : Blo 311834 313223 := bstep (se 1 (by rfl) ⟨234917, by rfl⟩ : syracuseStep 313223 = 469835) B469835
theorem B313231 : Blo 311834 313231 := bstep (se 1 (by rfl) ⟨234923, by rfl⟩ : syracuseStep 313231 = 469847) B469847
theorem B313275 : Blo 311834 313275 := bstep (se 1 (by rfl) ⟨234956, by rfl⟩ : syracuseStep 313275 = 469913) B469913
theorem B313351 : Blo 311834 313351 := bstep (se 1 (by rfl) ⟨235013, by rfl⟩ : syracuseStep 313351 = 470027) B470027
theorem B313359 : Blo 311834 313359 := bstep (se 1 (by rfl) ⟨235019, by rfl⟩ : syracuseStep 313359 = 470039) B470039
theorem B1591325 : Blo 311834 1591325 := bstep (se 3 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 1591325 = 596747) B596747
theorem B313403 : Blo 311834 313403 := bstep (se 1 (by rfl) ⟨235052, by rfl⟩ : syracuseStep 313403 = 470105) B470105
theorem B706679 : Blo 311834 706679 := bstep (se 1 (by rfl) ⟨530009, by rfl⟩ : syracuseStep 706679 = 1060019) B1060019
theorem B313479 : Blo 311834 313479 := bstep (se 1 (by rfl) ⟨235109, by rfl⟩ : syracuseStep 313479 = 470219) B470219
theorem B313487 : Blo 311834 313487 := bstep (se 1 (by rfl) ⟨235115, by rfl⟩ : syracuseStep 313487 = 470231) B470231
theorem B313531 : Blo 311834 313531 := bstep (se 1 (by rfl) ⟨235148, by rfl⟩ : syracuseStep 313531 = 470297) B470297
theorem B313607 : Blo 311834 313607 := bstep (se 1 (by rfl) ⟨235205, by rfl⟩ : syracuseStep 313607 = 470411) B470411
theorem B313615 : Blo 311834 313615 := bstep (se 1 (by rfl) ⟨235211, by rfl⟩ : syracuseStep 313615 = 470423) B470423
theorem B706859 : Blo 311834 706859 := bstep (se 1 (by rfl) ⟨530144, by rfl⟩ : syracuseStep 706859 = 1060289) B1060289
theorem B313659 : Blo 311834 313659 := bstep (se 1 (by rfl) ⟨235244, by rfl⟩ : syracuseStep 313659 = 470489) B470489
theorem B313735 : Blo 311834 313735 := bstep (se 1 (by rfl) ⟨235301, by rfl⟩ : syracuseStep 313735 = 470603) B470603
theorem B313743 : Blo 311834 313743 := bstep (se 1 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 313743 = 470615) B470615
theorem B313787 : Blo 311834 313787 := bstep (se 1 (by rfl) ⟨235340, by rfl⟩ : syracuseStep 313787 = 470681) B470681
theorem B1788419 : Blo 311834 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B1591811 : Blo 311834 1591811 := bstep (se 1 (by rfl) ⟨1193858, by rfl⟩ : syracuseStep 1591811 = 2387717) B2387717
theorem B313863 : Blo 311834 313863 := bstep (se 1 (by rfl) ⟨235397, by rfl⟩ : syracuseStep 313863 = 470795) B470795
theorem B313871 : Blo 311834 313871 := bstep (se 1 (by rfl) ⟨235403, by rfl⟩ : syracuseStep 313871 = 470807) B470807
theorem B313915 : Blo 311834 313915 := bstep (se 1 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 313915 = 470873) B470873
theorem B313991 : Blo 311834 313991 := bstep (se 1 (by rfl) ⟨235493, by rfl⟩ : syracuseStep 313991 = 470987) B470987
theorem B313999 : Blo 311834 313999 := bstep (se 1 (by rfl) ⟨235499, by rfl⟩ : syracuseStep 313999 = 470999) B470999
theorem B707219 : Blo 311834 707219 := bstep (se 1 (by rfl) ⟨530414, by rfl⟩ : syracuseStep 707219 = 1060829) B1060829
theorem B314043 : Blo 311834 314043 := bstep (se 1 (by rfl) ⟨235532, by rfl⟩ : syracuseStep 314043 = 471065) B471065
theorem B707273 : Blo 311834 707273 := bstep (se 2 (by rfl) ⟨265227, by rfl⟩ : syracuseStep 707273 = 530455) B530455
theorem B314119 : Blo 311834 314119 := bstep (se 1 (by rfl) ⟨235589, by rfl⟩ : syracuseStep 314119 = 471179) B471179
theorem B314127 : Blo 311834 314127 := bstep (se 1 (by rfl) ⟨235595, by rfl⟩ : syracuseStep 314127 = 471191) B471191
theorem B314171 : Blo 311834 314171 := bstep (se 1 (by rfl) ⟨235628, by rfl⟩ : syracuseStep 314171 = 471257) B471257
theorem B314247 : Blo 311834 314247 := bstep (se 1 (by rfl) ⟨235685, by rfl⟩ : syracuseStep 314247 = 471371) B471371
theorem B314255 : Blo 311834 314255 := bstep (se 1 (by rfl) ⟨235691, by rfl⟩ : syracuseStep 314255 = 471383) B471383
theorem B314299 : Blo 311834 314299 := bstep (se 1 (by rfl) ⟨235724, by rfl⟩ : syracuseStep 314299 = 471449) B471449
theorem B445385 : Blo 311834 445385 := bstep (se 2 (by rfl) ⟨167019, by rfl⟩ : syracuseStep 445385 = 334039) B334039
theorem B1788875 : Blo 311834 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B314375 : Blo 311834 314375 := bstep (se 1 (by rfl) ⟨235781, by rfl⟩ : syracuseStep 314375 = 471563) B471563
theorem B314383 : Blo 311834 314383 := bstep (se 1 (by rfl) ⟨235787, by rfl⟩ : syracuseStep 314383 = 471575) B471575
theorem B314427 : Blo 311834 314427 := bstep (se 1 (by rfl) ⟨235820, by rfl⟩ : syracuseStep 314427 = 471641) B471641
theorem B314503 : Blo 311834 314503 := bstep (se 1 (by rfl) ⟨235877, by rfl⟩ : syracuseStep 314503 = 471755) B471755
theorem B314511 : Blo 311834 314511 := bstep (se 1 (by rfl) ⟨235883, by rfl⟩ : syracuseStep 314511 = 471767) B471767
theorem B478351 : Blo 311834 478351 := bstep (se 1 (by rfl) ⟨358763, by rfl⟩ : syracuseStep 478351 = 717527) B717527
theorem B314555 : Blo 311834 314555 := bstep (se 1 (by rfl) ⟨235916, by rfl⟩ : syracuseStep 314555 = 471833) B471833
theorem B314631 : Blo 311834 314631 := bstep (se 1 (by rfl) ⟨235973, by rfl⟩ : syracuseStep 314631 = 471947) B471947
theorem B904463 : Blo 311834 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B314639 : Blo 311834 314639 := bstep (se 1 (by rfl) ⟨235979, by rfl⟩ : syracuseStep 314639 = 471959) B471959
theorem B314683 : Blo 311834 314683 := bstep (se 1 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 314683 = 472025) B472025
theorem B707975 : Blo 311834 707975 := bstep (se 1 (by rfl) ⟨530981, by rfl⟩ : syracuseStep 707975 = 1061963) B1061963
theorem B314759 : Blo 311834 314759 := bstep (se 1 (by rfl) ⟨236069, by rfl⟩ : syracuseStep 314759 = 472139) B472139
theorem B314767 : Blo 311834 314767 := bstep (se 1 (by rfl) ⟨236075, by rfl⟩ : syracuseStep 314767 = 472151) B472151
theorem B1002937 : Blo 311834 1002937 := bstep (se 2 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 1002937 = 752203) B752203
theorem B314811 : Blo 311834 314811 := bstep (se 1 (by rfl) ⟨236108, by rfl⟩ : syracuseStep 314811 = 472217) B472217
theorem B445943 : Blo 311834 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B314887 : Blo 311834 314887 := bstep (se 1 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 314887 = 472331) B472331
theorem B314895 : Blo 311834 314895 := bstep (se 1 (by rfl) ⟨236171, by rfl⟩ : syracuseStep 314895 = 472343) B472343
theorem B708155 : Blo 311834 708155 := bstep (se 1 (by rfl) ⟨531116, by rfl⟩ : syracuseStep 708155 = 1062233) B1062233
theorem B314939 : Blo 311834 314939 := bstep (se 1 (by rfl) ⟨236204, by rfl⟩ : syracuseStep 314939 = 472409) B472409
theorem B3558977 : Blo 311834 3558977 := bstep (se 2 (by rfl) ⟨1334616, by rfl⟩ : syracuseStep 3558977 = 2669233) B2669233
theorem B1789559 : Blo 311834 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B315015 : Blo 311834 315015 := bstep (se 1 (by rfl) ⟨236261, by rfl⟩ : syracuseStep 315015 = 472523) B472523
theorem B315023 : Blo 311834 315023 := bstep (se 1 (by rfl) ⟨236267, by rfl⟩ : syracuseStep 315023 = 472535) B472535
theorem B708281 : Blo 311834 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B315067 : Blo 311834 315067 := bstep (se 1 (by rfl) ⟨236300, by rfl⟩ : syracuseStep 315067 = 472601) B472601
theorem B1822409 : Blo 311834 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B315143 : Blo 311834 315143 := bstep (se 1 (by rfl) ⟨236357, by rfl⟩ : syracuseStep 315143 = 472715) B472715
theorem B315151 : Blo 311834 315151 := bstep (se 1 (by rfl) ⟨236363, by rfl⟩ : syracuseStep 315151 = 472727) B472727
theorem B446251 : Blo 311834 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B315195 : Blo 311834 315195 := bstep (se 1 (by rfl) ⟨236396, by rfl⟩ : syracuseStep 315195 = 472793) B472793
theorem B315271 : Blo 311834 315271 := bstep (se 1 (by rfl) ⟨236453, by rfl⟩ : syracuseStep 315271 = 472907) B472907
theorem B315279 : Blo 311834 315279 := bstep (se 1 (by rfl) ⟨236459, by rfl⟩ : syracuseStep 315279 = 472919) B472919
theorem B315323 : Blo 311834 315323 := bstep (se 1 (by rfl) ⟨236492, by rfl⟩ : syracuseStep 315323 = 472985) B472985
theorem B315399 : Blo 311834 315399 := bstep (se 1 (by rfl) ⟨236549, by rfl⟩ : syracuseStep 315399 = 473099) B473099
theorem B708623 : Blo 311834 708623 := bstep (se 1 (by rfl) ⟨531467, by rfl⟩ : syracuseStep 708623 = 1062935) B1062935
theorem B315407 : Blo 311834 315407 := bstep (se 1 (by rfl) ⟨236555, by rfl⟩ : syracuseStep 315407 = 473111) B473111
theorem B708641 : Blo 311834 708641 := bstep (se 2 (by rfl) ⟨265740, by rfl⟩ : syracuseStep 708641 = 531481) B531481
theorem B315451 : Blo 311834 315451 := bstep (se 1 (by rfl) ⟨236588, by rfl⟩ : syracuseStep 315451 = 473177) B473177
theorem B1364035 : Blo 311834 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B1593431 : Blo 311834 1593431 := bstep (se 1 (by rfl) ⟨1195073, by rfl⟩ : syracuseStep 1593431 = 2390147) B2390147
theorem B315527 : Blo 311834 315527 := bstep (se 1 (by rfl) ⟨236645, by rfl⟩ : syracuseStep 315527 = 473291) B473291
theorem B315535 : Blo 311834 315535 := bstep (se 1 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 315535 = 473303) B473303
theorem B315579 : Blo 311834 315579 := bstep (se 1 (by rfl) ⟨236684, by rfl⟩ : syracuseStep 315579 = 473369) B473369
theorem B7622857 : Blo 311834 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B315655 : Blo 311834 315655 := bstep (se 1 (by rfl) ⟨236741, by rfl⟩ : syracuseStep 315655 = 473483) B473483
theorem B446735 : Blo 311834 446735 := bstep (se 1 (by rfl) ⟨335051, by rfl⟩ : syracuseStep 446735 = 670103) B670103
theorem B315663 : Blo 311834 315663 := bstep (se 1 (by rfl) ⟨236747, by rfl⟩ : syracuseStep 315663 = 473495) B473495
theorem B315707 : Blo 311834 315707 := bstep (se 1 (by rfl) ⟨236780, by rfl⟩ : syracuseStep 315707 = 473561) B473561
theorem B708983 : Blo 311834 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B315783 : Blo 311834 315783 := bstep (se 1 (by rfl) ⟨236837, by rfl⟩ : syracuseStep 315783 = 473675) B473675
theorem B315791 : Blo 311834 315791 := bstep (se 1 (by rfl) ⟨236843, by rfl⟩ : syracuseStep 315791 = 473687) B473687
theorem B709163 : Blo 311834 709163 := bstep (se 1 (by rfl) ⟨531872, by rfl⟩ : syracuseStep 709163 = 1063745) B1063745
theorem B1593917 : Blo 311834 1593917 := bstep (se 3 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 1593917 = 597719) B597719
theorem B1266263 : Blo 311834 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B480043 : Blo 311834 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B709523 : Blo 311834 709523 := bstep (se 1 (by rfl) ⟨532142, by rfl⟩ : syracuseStep 709523 = 1064285) B1064285
theorem B644041 : Blo 311834 644041 := bstep (se 2 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 644041 = 483031) B483031
theorem B709577 : Blo 311834 709577 := bstep (se 2 (by rfl) ⟨266091, by rfl⟩ : syracuseStep 709577 = 532183) B532183
theorem B2544587 : Blo 311834 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B1266749 : Blo 311834 1266749 := bstep (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) B475031
theorem B1135873 : Blo 311834 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B1791517 : Blo 311834 1791517 := bstep (se 3 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 1791517 = 671819) B671819
theorem B906785 : Blo 311834 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B710279 : Blo 311834 710279 := bstep (se 1 (by rfl) ⟨532709, by rfl⟩ : syracuseStep 710279 = 1065419) B1065419
theorem B710459 : Blo 311834 710459 := bstep (se 1 (by rfl) ⟨532844, by rfl⟩ : syracuseStep 710459 = 1065689) B1065689
theorem B972691 : Blo 311834 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B710585 : Blo 311834 710585 := bstep (se 2 (by rfl) ⟨266469, by rfl⟩ : syracuseStep 710585 = 532939) B532939
theorem B1792043 : Blo 311834 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B2381885 : Blo 311834 2381885 := bstep (se 3 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 2381885 = 893207) B893207
theorem B1595699 : Blo 311834 1595699 := bstep (se 1 (by rfl) ⟨1196774, by rfl⟩ : syracuseStep 1595699 = 2393549) B2393549
theorem B448939 : Blo 311834 448939 := bstep (se 1 (by rfl) ⟨336704, by rfl⟩ : syracuseStep 448939 = 673409) B673409
theorem B1006141 : Blo 311834 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B1596023 : Blo 311834 1596023 := bstep (se 1 (by rfl) ⟨1197017, by rfl⟩ : syracuseStep 1596023 = 2394035) B2394035
theorem B449167 : Blo 311834 449167 := bstep (se 1 (by rfl) ⟨336875, by rfl⟩ : syracuseStep 449167 = 673751) B673751
theorem B908167 : Blo 311834 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B1137617 : Blo 311834 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B351247 : Blo 311834 351247 := bstep (se 1 (by rfl) ⟨263435, by rfl⟩ : syracuseStep 351247 = 526871) B526871
theorem B5069911 : Blo 311834 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B613511 : Blo 311834 613511 := bstep (se 1 (by rfl) ⟨460133, by rfl⟩ : syracuseStep 613511 = 920267) B920267
theorem B1793501 : Blo 311834 1793501 := bstep (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) B672563
theorem B351751 : Blo 311834 351751 := bstep (se 1 (by rfl) ⟨263813, by rfl⟩ : syracuseStep 351751 = 527627) B527627
theorem B2711069 : Blo 311834 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B1596995 : Blo 311834 1596995 := bstep (se 1 (by rfl) ⟨1197746, by rfl⟩ : syracuseStep 1596995 = 2395493) B2395493
theorem B351931 : Blo 311834 351931 := bstep (se 1 (by rfl) ⟨263948, by rfl⟩ : syracuseStep 351931 = 527897) B527897
theorem B3825443 : Blo 311834 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B1597319 : Blo 311834 1597319 := bstep (se 1 (by rfl) ⟨1197989, by rfl⟩ : syracuseStep 1597319 = 2395979) B2395979
theorem B2547773 : Blo 311834 2547773 := bstep (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) B955415
theorem B352399 : Blo 311834 352399 := bstep (se 1 (by rfl) ⟨264299, by rfl⟩ : syracuseStep 352399 = 528599) B528599
theorem B1695917 : Blo 311834 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B2253089 : Blo 311834 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B3793337 : Blo 311834 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B1008139 : Blo 311834 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B3007043 : Blo 311834 3007043 := bstep (se 1 (by rfl) ⟨2255282, by rfl⟩ : syracuseStep 3007043 = 4510565) B4510565
theorem B1499735 : Blo 311834 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B352903 : Blo 311834 352903 := bstep (se 1 (by rfl) ⟨264677, by rfl⟩ : syracuseStep 352903 = 529355) B529355
theorem B353083 : Blo 311834 353083 := bstep (se 1 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 353083 = 529625) B529625
theorem B4023533 : Blo 311834 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B353551 : Blo 311834 353551 := bstep (se 1 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 353551 = 530327) B530327
theorem B2385287 : Blo 311834 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B354055 : Blo 311834 354055 := bstep (se 1 (by rfl) ⟨265541, by rfl⟩ : syracuseStep 354055 = 531083) B531083
theorem B2549519 : Blo 311834 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B1795891 : Blo 311834 1795891 := bstep (se 1 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 1795891 = 2693837) B2693837
theorem B13526837 : Blo 311834 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B1337147 : Blo 311834 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B1009523 : Blo 311834 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B354235 : Blo 311834 354235 := bstep (se 1 (by rfl) ⟨265676, by rfl⟩ : syracuseStep 354235 = 531353) B531353
theorem B6514805 : Blo 311834 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B1697993 : Blo 311834 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B354703 : Blo 311834 354703 := bstep (se 1 (by rfl) ⟨266027, by rfl⟩ : syracuseStep 354703 = 532055) B532055
theorem B1436221 : Blo 311834 1436221 := bstep (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) B538583
theorem B355207 : Blo 311834 355207 := bstep (se 1 (by rfl) ⟨266405, by rfl⟩ : syracuseStep 355207 = 532811) B532811
theorem B1076267 : Blo 311834 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B2714797 : Blo 311834 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B1797349 : Blo 311834 1797349 := bstep (se 4 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 1797349 = 337003) B337003
theorem B1338923 : Blo 311834 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B14479307 : Blo 311834 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B749569 : Blo 311834 749569 := bstep (se 2 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 749569 = 562177) B562177
theorem B716833 : Blo 311834 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B848825 : Blo 311834 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B423287 : Blo 311834 423287 := bstep (se 1 (by rfl) ⟨317465, by rfl⟩ : syracuseStep 423287 = 634931) B634931
theorem B5371271 : Blo 311834 5371271 := bstep (se 1 (by rfl) ⟨4028453, by rfl⟩ : syracuseStep 5371271 = 8056907) B8056907
theorem B1897931 : Blo 311834 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B3012389 : Blo 311834 3012389 := bstep (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) B564823
theorem B1341299 : Blo 311834 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1341451 : Blo 311834 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B424055 : Blo 311834 424055 := bstep (se 1 (by rfl) ⟨318041, by rfl⟩ : syracuseStep 424055 = 636083) B636083
theorem B1276445 : Blo 311834 1276445 := bstep (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) B478667
theorem B1079837 : Blo 311834 1079837 := bstep (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) B404939
theorem B1506251 : Blo 311834 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B949249 : Blo 311834 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B1506365 : Blo 311834 1506365 := bstep (se 3 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 1506365 = 564887) B564887
theorem B9698915 : Blo 311834 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B1343213 : Blo 311834 1343213 := bstep (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) B503705
theorem B425785 : Blo 311834 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B34930763 : Blo 311834 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B754049 : Blo 311834 754049 := bstep (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) B565537
theorem B6128245 : Blo 311834 6128245 := bstep (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) B574523
theorem B1344185 : Blo 311834 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B754375 : Blo 311834 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B3048619 : Blo 311834 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B3999293 : Blo 311834 3999293 := bstep (se 3 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 3999293 = 1499735) B1499735
theorem B394951 : Blo 311834 394951 := bstep (se 1 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 394951 = 592427) B592427
theorem B526223 : Blo 311834 526223 := bstep (se 1 (by rfl) ⟨394667, by rfl⟩ : syracuseStep 526223 = 789335) B789335
theorem B526459 : Blo 311834 526459 := bstep (se 1 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 526459 = 789689) B789689
theorem B2394521 : Blo 311834 2394521 := bstep (se 2 (by rfl) ⟨897945, by rfl⟩ : syracuseStep 2394521 = 1795891) B1795891
theorem B395695 : Blo 311834 395695 := bstep (se 1 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 395695 = 593543) B593543
theorem B1214939 : Blo 311834 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B592859 : Blo 311834 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B527323 : Blo 311834 527323 := bstep (se 1 (by rfl) ⟨395492, by rfl⟩ : syracuseStep 527323 = 790985) B790985
theorem B1510595 : Blo 311834 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B593095 : Blo 311834 593095 := bstep (se 1 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 593095 = 889643) B889643
theorem B3214583 : Blo 311834 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B396839 : Blo 311834 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B527951 : Blo 311834 527951 := bstep (se 1 (by rfl) ⟨395963, by rfl⟩ : syracuseStep 527951 = 791927) B791927
theorem B1052459 : Blo 311834 1052459 := bstep (se 1 (by rfl) ⟨789344, by rfl⟩ : syracuseStep 1052459 = 1578689) B1578689
theorem B397163 : Blo 311834 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B1052729 : Blo 311834 1052729 := bstep (se 2 (by rfl) ⟨394773, by rfl⟩ : syracuseStep 1052729 = 789547) B789547
theorem B2560157 : Blo 311834 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B3281075 : Blo 311834 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B2396465 : Blo 311834 2396465 := bstep (se 2 (by rfl) ⟨898674, by rfl⟩ : syracuseStep 2396465 = 1797349) B1797349
theorem B1053053 : Blo 311834 1053053 := bstep (se 3 (by rfl) ⟨197447, by rfl⟩ : syracuseStep 1053053 = 394895) B394895
theorem B528815 : Blo 311834 528815 := bstep (se 1 (by rfl) ⟨396611, by rfl⟩ : syracuseStep 528815 = 793223) B793223
theorem B758297 : Blo 311834 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B1053323 : Blo 311834 1053323 := bstep (se 1 (by rfl) ⟨789992, by rfl⟩ : syracuseStep 1053323 = 1579985) B1579985
theorem B758411 : Blo 311834 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B529247 : Blo 311834 529247 := bstep (se 1 (by rfl) ⟨396935, by rfl⟩ : syracuseStep 529247 = 793871) B793871
theorem B791471 : Blo 311834 791471 := bstep (se 1 (by rfl) ⟨593603, by rfl⟩ : syracuseStep 791471 = 1187207) B1187207
theorem B2692061 : Blo 311834 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B2626561 : Blo 311834 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B1807379 : Blo 311834 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B595001 : Blo 311834 595001 := bstep (se 2 (by rfl) ⟨223125, by rfl⟩ : syracuseStep 595001 = 446251) B446251
theorem B398459 : Blo 311834 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B9049259 : Blo 311834 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B595343 : Blo 311834 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B529807 : Blo 311834 529807 := bstep (se 1 (by rfl) ⟨397355, by rfl⟩ : syracuseStep 529807 = 794711) B794711
theorem B792089 : Blo 311834 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B1054241 : Blo 311834 1054241 := bstep (se 2 (by rfl) ⟨395340, by rfl⟩ : syracuseStep 1054241 = 790681) B790681
theorem B10163809 : Blo 311834 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B2528891 : Blo 311834 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B2004695 : Blo 311834 2004695 := bstep (se 1 (by rfl) ⟨1503521, by rfl⟩ : syracuseStep 2004695 = 3007043) B3007043
theorem B1054457 : Blo 311834 1054457 := bstep (se 2 (by rfl) ⟨395421, by rfl⟩ : syracuseStep 1054457 = 790843) B790843
theorem B1054727 : Blo 311834 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B530489 : Blo 311834 530489 := bstep (se 2 (by rfl) ⟨198933, by rfl⟩ : syracuseStep 530489 = 397867) B397867
theorem B1054835 : Blo 311834 1054835 := bstep (se 1 (by rfl) ⟨791126, by rfl⟩ : syracuseStep 1054835 = 1582253) B1582253
theorem B1055105 : Blo 311834 1055105 := bstep (se 2 (by rfl) ⟨395664, by rfl⟩ : syracuseStep 1055105 = 791329) B791329
theorem B9017891 : Blo 311834 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B891431 : Blo 311834 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B334415 : Blo 311834 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B858721 : Blo 311834 858721 := bstep (se 2 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 858721 = 644041) B644041
theorem B531191 : Blo 311834 531191 := bstep (se 1 (by rfl) ⟨398393, by rfl⟩ : syracuseStep 531191 = 796787) B796787
theorem B1186721 : Blo 311834 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B3218359 : Blo 311834 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B531535 : Blo 311834 531535 := bstep (se 1 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 531535 = 797303) B797303
theorem B1055915 : Blo 311834 1055915 := bstep (se 1 (by rfl) ⟨791936, by rfl⟩ : syracuseStep 1055915 = 1583873) B1583873
theorem B597203 : Blo 311834 597203 := bstep (se 1 (by rfl) ⟨447902, by rfl⟩ : syracuseStep 597203 = 895805) B895805
theorem B531785 : Blo 311834 531785 := bstep (se 2 (by rfl) ⟨199419, by rfl⟩ : syracuseStep 531785 = 398839) B398839
theorem B4300121 : Blo 311834 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B597431 : Blo 311834 597431 := bstep (se 1 (by rfl) ⟨448073, by rfl⟩ : syracuseStep 597431 = 896147) B896147
theorem B1515131 : Blo 311834 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B1056455 : Blo 311834 1056455 := bstep (se 1 (by rfl) ⟨792341, by rfl⟩ : syracuseStep 1056455 = 1584683) B1584683
theorem B892615 : Blo 311834 892615 := bstep (se 1 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 892615 = 1338923) B1338923
theorem B532217 : Blo 311834 532217 := bstep (se 2 (by rfl) ⟨199581, by rfl⟩ : syracuseStep 532217 = 399163) B399163
theorem B1187693 : Blo 311834 1187693 := bstep (se 3 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 1187693 = 445385) B445385
theorem B532399 : Blo 311834 532399 := bstep (se 1 (by rfl) ⟨399299, by rfl⟩ : syracuseStep 532399 = 798599) B798599
theorem B532487 : Blo 311834 532487 := bstep (se 1 (by rfl) ⟨399365, by rfl⟩ : syracuseStep 532487 = 798731) B798731
theorem B794681 : Blo 311834 794681 := bstep (se 2 (by rfl) ⟨298005, by rfl⟩ : syracuseStep 794681 = 596011) B596011
theorem B532831 : Blo 311834 532831 := bstep (se 1 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 532831 = 799247) B799247
theorem B532919 : Blo 311834 532919 := bstep (se 1 (by rfl) ⟨399689, by rfl⟩ : syracuseStep 532919 = 799379) B799379
theorem B25960981 : Blo 311834 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B1188377 : Blo 311834 1188377 := bstep (se 2 (by rfl) ⟨445641, by rfl⟩ : syracuseStep 1188377 = 891283) B891283
theorem B1188391 : Blo 311834 1188391 := bstep (se 1 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 1188391 = 1782587) B1782587
theorem B1057319 : Blo 311834 1057319 := bstep (se 1 (by rfl) ⟨792989, by rfl⟩ : syracuseStep 1057319 = 1585979) B1585979
theorem B598585 : Blo 311834 598585 := bstep (se 2 (by rfl) ⟨224469, by rfl⟩ : syracuseStep 598585 = 448939) B448939
theorem B565883 : Blo 311834 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B1057427 : Blo 311834 1057427 := bstep (se 1 (by rfl) ⟨793070, by rfl⟩ : syracuseStep 1057427 = 1586141) B1586141
theorem B467807 : Blo 311834 467807 := bstep (se 1 (by rfl) ⟨350855, by rfl⟩ : syracuseStep 467807 = 701711) B701711
theorem B598889 : Blo 311834 598889 := bstep (se 2 (by rfl) ⟨224583, by rfl⟩ : syracuseStep 598889 = 449167) B449167
theorem B467819 : Blo 311834 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B1057643 : Blo 311834 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B598927 : Blo 311834 598927 := bstep (se 1 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 598927 = 898391) B898391
theorem B1057697 : Blo 311834 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B3580847 : Blo 311834 3580847 := bstep (se 1 (by rfl) ⟨2685635, by rfl⟩ : syracuseStep 3580847 = 5371271) B5371271
theorem B468047 : Blo 311834 468047 := bstep (se 1 (by rfl) ⟨351035, by rfl⟩ : syracuseStep 468047 = 702071) B702071
theorem B2008259 : Blo 311834 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B468167 : Blo 311834 468167 := bstep (se 1 (by rfl) ⟨351125, by rfl⟩ : syracuseStep 468167 = 702251) B702251
theorem B894199 : Blo 311834 894199 := bstep (se 1 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 894199 = 1341299) B1341299
theorem B1189181 : Blo 311834 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B468329 : Blo 311834 468329 := bstep (se 2 (by rfl) ⟨175623, by rfl⟩ : syracuseStep 468329 = 351247) B351247
theorem B468407 : Blo 311834 468407 := bstep (se 1 (by rfl) ⟨351305, by rfl⟩ : syracuseStep 468407 = 702611) B702611
theorem B6759881 : Blo 311834 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B468443 : Blo 311834 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B1189363 : Blo 311834 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B1058291 : Blo 311834 1058291 := bstep (se 1 (by rfl) ⟨793718, by rfl⟩ : syracuseStep 1058291 = 1587437) B1587437
theorem B894473 : Blo 311834 894473 := bstep (se 2 (by rfl) ⟨335427, by rfl⟩ : syracuseStep 894473 = 670855) B670855
theorem B796169 : Blo 311834 796169 := bstep (se 2 (by rfl) ⟨298563, by rfl⟩ : syracuseStep 796169 = 597127) B597127
theorem B1582739 : Blo 311834 1582739 := bstep (se 1 (by rfl) ⟨1187054, by rfl⟩ : syracuseStep 1582739 = 2374109) B2374109
theorem B468911 : Blo 311834 468911 := bstep (se 1 (by rfl) ⟨351683, by rfl⟩ : syracuseStep 468911 = 703367) B703367
theorem B469001 : Blo 311834 469001 := bstep (se 2 (by rfl) ⟨175875, by rfl⟩ : syracuseStep 469001 = 351751) B351751
theorem B1058831 : Blo 311834 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B469031 : Blo 311834 469031 := bstep (se 1 (by rfl) ⟨351773, by rfl⟩ : syracuseStep 469031 = 703547) B703547
theorem B5187685 : Blo 311834 5187685 := bstep (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) B972691
theorem B469115 : Blo 311834 469115 := bstep (se 1 (by rfl) ⟨351836, by rfl⟩ : syracuseStep 469115 = 703673) B703673
theorem B469241 : Blo 311834 469241 := bstep (se 2 (by rfl) ⟨175965, by rfl⟩ : syracuseStep 469241 = 351931) B351931
theorem B469343 : Blo 311834 469343 := bstep (se 1 (by rfl) ⟨352007, by rfl⟩ : syracuseStep 469343 = 704015) B704015
theorem B469355 : Blo 311834 469355 := bstep (se 1 (by rfl) ⟨352016, by rfl⟩ : syracuseStep 469355 = 704033) B704033
theorem B6465943 : Blo 311834 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B567713 : Blo 311834 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B895475 : Blo 311834 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B469583 : Blo 311834 469583 := bstep (se 1 (by rfl) ⟨352187, by rfl⟩ : syracuseStep 469583 = 704375) B704375
theorem B1059425 : Blo 311834 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B797323 : Blo 311834 797323 := bstep (se 1 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 797323 = 1195985) B1195985
theorem B2370221 : Blo 311834 2370221 := bstep (se 3 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 2370221 = 888833) B888833
theorem B469703 : Blo 311834 469703 := bstep (se 1 (by rfl) ⟨352277, by rfl⟩ : syracuseStep 469703 = 704555) B704555
theorem B1190609 : Blo 311834 1190609 := bstep (se 2 (by rfl) ⟨446478, by rfl⟩ : syracuseStep 1190609 = 892957) B892957
theorem B4500299 : Blo 311834 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B469865 : Blo 311834 469865 := bstep (se 2 (by rfl) ⟨176199, by rfl⟩ : syracuseStep 469865 = 352399) B352399
theorem B469943 : Blo 311834 469943 := bstep (se 1 (by rfl) ⟨352457, by rfl⟩ : syracuseStep 469943 = 704915) B704915
theorem B895931 : Blo 311834 895931 := bstep (se 1 (by rfl) ⟨671948, by rfl⟩ : syracuseStep 895931 = 1343897) B1343897
theorem B797627 : Blo 311834 797627 := bstep (se 1 (by rfl) ⟨598220, by rfl⟩ : syracuseStep 797627 = 1196441) B1196441
theorem B469979 : Blo 311834 469979 := bstep (se 1 (by rfl) ⟨352484, by rfl⟩ : syracuseStep 469979 = 704969) B704969
theorem B666643 : Blo 311834 666643 := bstep (se 1 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 666643 = 999965) B999965
theorem B634105 : Blo 311834 634105 := bstep (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) B475579
theorem B2665817 : Blo 311834 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B1191293 : Blo 311834 1191293 := bstep (se 3 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 1191293 = 446735) B446735
theorem B470447 : Blo 311834 470447 := bstep (se 1 (by rfl) ⟨352835, by rfl⟩ : syracuseStep 470447 = 705671) B705671
theorem B470537 : Blo 311834 470537 := bstep (se 2 (by rfl) ⟨176451, by rfl⟩ : syracuseStep 470537 = 352903) B352903
theorem B470567 : Blo 311834 470567 := bstep (se 1 (by rfl) ⟨352925, by rfl⟩ : syracuseStep 470567 = 705851) B705851
theorem B470651 : Blo 311834 470651 := bstep (se 1 (by rfl) ⟨352988, by rfl⟩ : syracuseStep 470651 = 705977) B705977
theorem B798407 : Blo 311834 798407 := bstep (se 1 (by rfl) ⟨598805, by rfl⟩ : syracuseStep 798407 = 1197611) B1197611
theorem B2010845 : Blo 311834 2010845 := bstep (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) B754067
theorem B470777 : Blo 311834 470777 := bstep (se 2 (by rfl) ⟨176541, by rfl⟩ : syracuseStep 470777 = 353083) B353083
theorem B896761 : Blo 311834 896761 := bstep (se 2 (by rfl) ⟨336285, by rfl⟩ : syracuseStep 896761 = 672571) B672571
theorem B798457 : Blo 311834 798457 := bstep (se 2 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 798457 = 598843) B598843
theorem B1126187 : Blo 311834 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B470879 : Blo 311834 470879 := bstep (se 1 (by rfl) ⟨353159, by rfl⟩ : syracuseStep 470879 = 706319) B706319
theorem B470891 : Blo 311834 470891 := bstep (se 1 (by rfl) ⟨353168, by rfl⟩ : syracuseStep 470891 = 706337) B706337
theorem B1060883 : Blo 311834 1060883 := bstep (se 1 (by rfl) ⟨795662, by rfl⟩ : syracuseStep 1060883 = 1591325) B1591325
theorem B4501565 : Blo 311834 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B471119 : Blo 311834 471119 := bstep (se 1 (by rfl) ⟨353339, by rfl⟩ : syracuseStep 471119 = 706679) B706679
theorem B471239 : Blo 311834 471239 := bstep (se 1 (by rfl) ⟨353429, by rfl⟩ : syracuseStep 471239 = 706859) B706859
theorem B1192279 : Blo 311834 1192279 := bstep (se 1 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 1192279 = 1788419) B1788419
theorem B1061207 : Blo 311834 1061207 := bstep (se 1 (by rfl) ⟨795905, by rfl⟩ : syracuseStep 1061207 = 1591811) B1591811
theorem B471401 : Blo 311834 471401 := bstep (se 2 (by rfl) ⟨176775, by rfl⟩ : syracuseStep 471401 = 353551) B353551
theorem B799105 : Blo 311834 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B471479 : Blo 311834 471479 := bstep (se 1 (by rfl) ⟨353609, by rfl⟩ : syracuseStep 471479 = 707219) B707219
theorem B8565209 : Blo 311834 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B471515 : Blo 311834 471515 := bstep (se 1 (by rfl) ⟨353636, by rfl⟩ : syracuseStep 471515 = 707273) B707273
theorem B1192583 : Blo 311834 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B3846865 : Blo 311834 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B10138385 : Blo 311834 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B602975 : Blo 311834 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B4043627 : Blo 311834 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B471983 : Blo 311834 471983 := bstep (se 1 (by rfl) ⟨353987, by rfl⟩ : syracuseStep 471983 = 707975) B707975
theorem B504839 : Blo 311834 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B472073 : Blo 311834 472073 := bstep (se 2 (by rfl) ⟨177027, by rfl⟩ : syracuseStep 472073 = 354055) B354055
theorem B472103 : Blo 311834 472103 := bstep (se 1 (by rfl) ⟨354077, by rfl⟩ : syracuseStep 472103 = 708155) B708155
theorem B2372651 : Blo 311834 2372651 := bstep (se 1 (by rfl) ⟨1779488, by rfl⟩ : syracuseStep 2372651 = 3558977) B3558977
theorem B1193039 : Blo 311834 1193039 := bstep (se 1 (by rfl) ⟨894779, by rfl⟩ : syracuseStep 1193039 = 1789559) B1789559
theorem B472187 : Blo 311834 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B898219 : Blo 311834 898219 := bstep (se 1 (by rfl) ⟨673664, by rfl⟩ : syracuseStep 898219 = 1347329) B1347329
theorem B472313 : Blo 311834 472313 := bstep (se 2 (by rfl) ⟨177117, by rfl⟩ : syracuseStep 472313 = 354235) B354235
theorem B472415 : Blo 311834 472415 := bstep (se 1 (by rfl) ⟨354311, by rfl⟩ : syracuseStep 472415 = 708623) B708623
theorem B701801 : Blo 311834 701801 := bstep (se 2 (by rfl) ⟨263175, by rfl⟩ : syracuseStep 701801 = 526351) B526351
theorem B472427 : Blo 311834 472427 := bstep (se 1 (by rfl) ⟨354320, by rfl⟩ : syracuseStep 472427 = 708641) B708641
theorem B1062287 : Blo 311834 1062287 := bstep (se 1 (by rfl) ⟨796715, by rfl⟩ : syracuseStep 1062287 = 1593431) B1593431
theorem B898447 : Blo 311834 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B6403475 : Blo 311834 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B472655 : Blo 311834 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B472775 : Blo 311834 472775 := bstep (se 1 (by rfl) ⟨354581, by rfl⟩ : syracuseStep 472775 = 709163) B709163
theorem B1062611 : Blo 311834 1062611 := bstep (se 1 (by rfl) ⟨796958, by rfl⟩ : syracuseStep 1062611 = 1593917) B1593917
theorem B2602847 : Blo 311834 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B472937 : Blo 311834 472937 := bstep (se 2 (by rfl) ⟨177351, by rfl⟩ : syracuseStep 472937 = 354703) B354703
theorem B4044653 : Blo 311834 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B473015 : Blo 311834 473015 := bstep (se 1 (by rfl) ⟨354761, by rfl⟩ : syracuseStep 473015 = 709523) B709523
theorem B702395 : Blo 311834 702395 := bstep (se 1 (by rfl) ⟨526796, by rfl⟩ : syracuseStep 702395 = 1053593) B1053593
theorem B473051 : Blo 311834 473051 := bstep (se 1 (by rfl) ⟨354788, by rfl⟩ : syracuseStep 473051 = 709577) B709577
theorem B702521 : Blo 311834 702521 := bstep (se 2 (by rfl) ⟨263445, by rfl⟩ : syracuseStep 702521 = 526891) B526891
theorem B1194041 : Blo 311834 1194041 := bstep (se 2 (by rfl) ⟨447765, by rfl⟩ : syracuseStep 1194041 = 895531) B895531
theorem B637139 : Blo 311834 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B604523 : Blo 311834 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B702863 : Blo 311834 702863 := bstep (se 1 (by rfl) ⟨527147, by rfl⟩ : syracuseStep 702863 = 1054295) B1054295
theorem B473519 : Blo 311834 473519 := bstep (se 1 (by rfl) ⟨355139, by rfl⟩ : syracuseStep 473519 = 710279) B710279
theorem B473609 : Blo 311834 473609 := bstep (se 2 (by rfl) ⟨177603, by rfl⟩ : syracuseStep 473609 = 355207) B355207
theorem B473639 : Blo 311834 473639 := bstep (se 1 (by rfl) ⟨355229, by rfl⟩ : syracuseStep 473639 = 710459) B710459
theorem B473723 : Blo 311834 473723 := bstep (se 1 (by rfl) ⟨355292, by rfl⟩ : syracuseStep 473723 = 710585) B710585
theorem B1194695 : Blo 311834 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B703187 : Blo 311834 703187 := bstep (se 1 (by rfl) ⟨527390, by rfl⟩ : syracuseStep 703187 = 1054781) B1054781
theorem B1587923 : Blo 311834 1587923 := bstep (se 1 (by rfl) ⟨1190942, by rfl⟩ : syracuseStep 1587923 = 2381885) B2381885
theorem B9616157 : Blo 311834 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B637801 : Blo 311834 637801 := bstep (se 2 (by rfl) ⟨239175, by rfl⟩ : syracuseStep 637801 = 478351) B478351
theorem B1063799 : Blo 311834 1063799 := bstep (se 1 (by rfl) ⟨797849, by rfl⟩ : syracuseStep 1063799 = 1595699) B1595699
theorem B3619729 : Blo 311834 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B1064015 : Blo 311834 1064015 := bstep (se 1 (by rfl) ⟨798011, by rfl⟩ : syracuseStep 1064015 = 1596023) B1596023
theorem B2538877 : Blo 311834 2538877 := bstep (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) B952079
theorem B409007 : Blo 311834 409007 := bstep (se 1 (by rfl) ⟨306755, by rfl⟩ : syracuseStep 409007 = 613511) B613511
theorem B1064393 : Blo 311834 1064393 := bstep (se 2 (by rfl) ⟨399147, by rfl⟩ : syracuseStep 1064393 = 798295) B798295
theorem B704123 : Blo 311834 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B1195667 : Blo 311834 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B1064663 : Blo 311834 1064663 := bstep (se 1 (by rfl) ⟨798497, by rfl⟩ : syracuseStep 1064663 = 1596995) B1596995
theorem B704249 : Blo 311834 704249 := bstep (se 2 (by rfl) ⟨264093, by rfl⟩ : syracuseStep 704249 = 528187) B528187
theorem B1064879 : Blo 311834 1064879 := bstep (se 1 (by rfl) ⟨798659, by rfl⟩ : syracuseStep 1064879 = 1597319) B1597319
theorem B999425 : Blo 311834 999425 := bstep (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) B749569
theorem B704519 : Blo 311834 704519 := bstep (se 1 (by rfl) ⟨528389, by rfl⟩ : syracuseStep 704519 = 1056779) B1056779
theorem B704591 : Blo 311834 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B1818713 : Blo 311834 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1130611 : Blo 311834 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B1130813 : Blo 311834 1130813 := bstep (se 3 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 1130813 = 424055) B424055
theorem B704987 : Blo 311834 704987 := bstep (se 1 (by rfl) ⟨528740, by rfl⟩ : syracuseStep 704987 = 1057481) B1057481
theorem B311847 : Blo 311834 311847 := bstep (se 1 (by rfl) ⟨233885, by rfl⟩ : syracuseStep 311847 = 467771) B467771
theorem B311887 : Blo 311834 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B311903 : Blo 311834 311903 := bstep (se 1 (by rfl) ⟨233927, by rfl⟩ : syracuseStep 311903 = 467855) B467855
theorem B311931 : Blo 311834 311931 := bstep (se 1 (by rfl) ⟨233948, by rfl⟩ : syracuseStep 311931 = 467897) B467897
theorem B311983 : Blo 311834 311983 := bstep (se 1 (by rfl) ⟨233987, by rfl⟩ : syracuseStep 311983 = 467975) B467975
theorem B312007 : Blo 311834 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B312027 : Blo 311834 312027 := bstep (se 1 (by rfl) ⟨234020, by rfl⟩ : syracuseStep 312027 = 468041) B468041
theorem B312103 : Blo 311834 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B312143 : Blo 311834 312143 := bstep (se 1 (by rfl) ⟨234107, by rfl⟩ : syracuseStep 312143 = 468215) B468215
theorem B312159 : Blo 311834 312159 := bstep (se 1 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 312159 = 468239) B468239
theorem B312187 : Blo 311834 312187 := bstep (se 1 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 312187 = 468281) B468281
theorem B312239 : Blo 311834 312239 := bstep (se 1 (by rfl) ⟨234179, by rfl⟩ : syracuseStep 312239 = 468359) B468359
theorem B705455 : Blo 311834 705455 := bstep (se 1 (by rfl) ⟨529091, by rfl⟩ : syracuseStep 705455 = 1058183) B1058183
theorem B1590191 : Blo 311834 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B312263 : Blo 311834 312263 := bstep (se 1 (by rfl) ⟨234197, by rfl⟩ : syracuseStep 312263 = 468395) B468395
theorem B312283 : Blo 311834 312283 := bstep (se 1 (by rfl) ⟨234212, by rfl⟩ : syracuseStep 312283 = 468425) B468425
theorem B312359 : Blo 311834 312359 := bstep (se 1 (by rfl) ⟨234269, by rfl⟩ : syracuseStep 312359 = 468539) B468539
theorem B640057 : Blo 311834 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B312399 : Blo 311834 312399 := bstep (se 1 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 312399 = 468599) B468599
theorem B312415 : Blo 311834 312415 := bstep (se 1 (by rfl) ⟨234311, by rfl⟩ : syracuseStep 312415 = 468623) B468623
theorem B312443 : Blo 311834 312443 := bstep (se 1 (by rfl) ⟨234332, by rfl⟩ : syracuseStep 312443 = 468665) B468665
theorem B705707 : Blo 311834 705707 := bstep (se 1 (by rfl) ⟨529280, by rfl⟩ : syracuseStep 705707 = 1058561) B1058561
theorem B312495 : Blo 311834 312495 := bstep (se 1 (by rfl) ⟨234371, by rfl⟩ : syracuseStep 312495 = 468743) B468743
theorem B312519 : Blo 311834 312519 := bstep (se 1 (by rfl) ⟨234389, by rfl⟩ : syracuseStep 312519 = 468779) B468779
theorem B312539 : Blo 311834 312539 := bstep (se 1 (by rfl) ⟨234404, by rfl⟩ : syracuseStep 312539 = 468809) B468809
theorem B2016535 : Blo 311834 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B312615 : Blo 311834 312615 := bstep (se 1 (by rfl) ⟨234461, by rfl⟩ : syracuseStep 312615 = 468923) B468923
theorem B312655 : Blo 311834 312655 := bstep (se 1 (by rfl) ⟨234491, by rfl⟩ : syracuseStep 312655 = 468983) B468983
theorem B312671 : Blo 311834 312671 := bstep (se 1 (by rfl) ⟨234503, by rfl⟩ : syracuseStep 312671 = 469007) B469007
theorem B312699 : Blo 311834 312699 := bstep (se 1 (by rfl) ⟨234524, by rfl⟩ : syracuseStep 312699 = 469049) B469049
theorem B4343203 : Blo 311834 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B312751 : Blo 311834 312751 := bstep (se 1 (by rfl) ⟨234563, by rfl⟩ : syracuseStep 312751 = 469127) B469127
theorem B312775 : Blo 311834 312775 := bstep (se 1 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 312775 = 469163) B469163
theorem B312795 : Blo 311834 312795 := bstep (se 1 (by rfl) ⟨234596, by rfl⟩ : syracuseStep 312795 = 469193) B469193
theorem B1131995 : Blo 311834 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B3589595 : Blo 311834 3589595 := bstep (se 1 (by rfl) ⟨2692196, by rfl⟩ : syracuseStep 3589595 = 5384393) B5384393
theorem B673289 : Blo 311834 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B312871 : Blo 311834 312871 := bstep (se 1 (by rfl) ⟨234653, by rfl⟩ : syracuseStep 312871 = 469307) B469307
theorem B312911 : Blo 311834 312911 := bstep (se 1 (by rfl) ⟨234683, by rfl⟩ : syracuseStep 312911 = 469367) B469367
theorem B312927 : Blo 311834 312927 := bstep (se 1 (by rfl) ⟨234695, by rfl⟩ : syracuseStep 312927 = 469391) B469391
theorem B312955 : Blo 311834 312955 := bstep (se 1 (by rfl) ⟨234716, by rfl⟩ : syracuseStep 312955 = 469433) B469433
theorem B313007 : Blo 311834 313007 := bstep (se 1 (by rfl) ⟨234755, by rfl⟩ : syracuseStep 313007 = 469511) B469511
theorem B313031 : Blo 311834 313031 := bstep (se 1 (by rfl) ⟨234773, by rfl⟩ : syracuseStep 313031 = 469547) B469547
theorem B706247 : Blo 311834 706247 := bstep (se 1 (by rfl) ⟨529685, by rfl⟩ : syracuseStep 706247 = 1059371) B1059371
theorem B313051 : Blo 311834 313051 := bstep (se 1 (by rfl) ⟨234788, by rfl⟩ : syracuseStep 313051 = 469577) B469577
theorem B313127 : Blo 311834 313127 := bstep (se 1 (by rfl) ⟨234845, by rfl⟩ : syracuseStep 313127 = 469691) B469691
theorem B313167 : Blo 311834 313167 := bstep (se 1 (by rfl) ⟨234875, by rfl⟩ : syracuseStep 313167 = 469751) B469751
theorem B313183 : Blo 311834 313183 := bstep (se 1 (by rfl) ⟨234887, by rfl⟩ : syracuseStep 313183 = 469775) B469775
theorem B313211 : Blo 311834 313211 := bstep (se 1 (by rfl) ⟨234908, by rfl⟩ : syracuseStep 313211 = 469817) B469817
theorem B313263 : Blo 311834 313263 := bstep (se 1 (by rfl) ⟨234947, by rfl⟩ : syracuseStep 313263 = 469895) B469895
theorem B313287 : Blo 311834 313287 := bstep (se 1 (by rfl) ⟨234965, by rfl⟩ : syracuseStep 313287 = 469931) B469931
theorem B313307 : Blo 311834 313307 := bstep (se 1 (by rfl) ⟨234980, by rfl⟩ : syracuseStep 313307 = 469961) B469961
theorem B313383 : Blo 311834 313383 := bstep (se 1 (by rfl) ⟨235037, by rfl⟩ : syracuseStep 313383 = 470075) B470075
theorem B313423 : Blo 311834 313423 := bstep (se 1 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 313423 = 470135) B470135
theorem B313439 : Blo 311834 313439 := bstep (se 1 (by rfl) ⟨235079, by rfl⟩ : syracuseStep 313439 = 470159) B470159
theorem B313467 : Blo 311834 313467 := bstep (se 1 (by rfl) ⟨235100, by rfl⟩ : syracuseStep 313467 = 470201) B470201
theorem B313519 : Blo 311834 313519 := bstep (se 1 (by rfl) ⟨235139, by rfl⟩ : syracuseStep 313519 = 470279) B470279
theorem B313543 : Blo 311834 313543 := bstep (se 1 (by rfl) ⟨235157, by rfl⟩ : syracuseStep 313543 = 470315) B470315
theorem B313563 : Blo 311834 313563 := bstep (se 1 (by rfl) ⟨235172, by rfl⟩ : syracuseStep 313563 = 470345) B470345
theorem B313639 : Blo 311834 313639 := bstep (se 1 (by rfl) ⟨235229, by rfl⟩ : syracuseStep 313639 = 470459) B470459
theorem B313679 : Blo 311834 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B313695 : Blo 311834 313695 := bstep (se 1 (by rfl) ⟨235271, by rfl⟩ : syracuseStep 313695 = 470543) B470543
theorem B313723 : Blo 311834 313723 := bstep (se 1 (by rfl) ⟨235292, by rfl⟩ : syracuseStep 313723 = 470585) B470585
theorem B313775 : Blo 311834 313775 := bstep (se 1 (by rfl) ⟨235331, by rfl⟩ : syracuseStep 313775 = 470663) B470663
theorem B313799 : Blo 311834 313799 := bstep (se 1 (by rfl) ⟨235349, by rfl⟩ : syracuseStep 313799 = 470699) B470699
theorem B313819 : Blo 311834 313819 := bstep (se 1 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 313819 = 470729) B470729
theorem B2017817 : Blo 311834 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B313895 : Blo 311834 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B707111 : Blo 311834 707111 := bstep (se 1 (by rfl) ⟨530333, by rfl⟩ : syracuseStep 707111 = 1060667) B1060667
theorem B313935 : Blo 311834 313935 := bstep (se 1 (by rfl) ⟨235451, by rfl⟩ : syracuseStep 313935 = 470903) B470903
theorem B313951 : Blo 311834 313951 := bstep (se 1 (by rfl) ⟨235463, by rfl⟩ : syracuseStep 313951 = 470927) B470927
theorem B313979 : Blo 311834 313979 := bstep (se 1 (by rfl) ⟨235484, by rfl⟩ : syracuseStep 313979 = 470969) B470969
theorem B9652871 : Blo 311834 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B314031 : Blo 311834 314031 := bstep (se 1 (by rfl) ⟨235523, by rfl⟩ : syracuseStep 314031 = 471047) B471047
theorem B4311731 : Blo 311834 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B1788601 : Blo 311834 1788601 := bstep (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) B1341451
theorem B314055 : Blo 311834 314055 := bstep (se 1 (by rfl) ⟨235541, by rfl⟩ : syracuseStep 314055 = 471083) B471083
theorem B314075 : Blo 311834 314075 := bstep (se 1 (by rfl) ⟨235556, by rfl⟩ : syracuseStep 314075 = 471113) B471113
theorem B314151 : Blo 311834 314151 := bstep (se 1 (by rfl) ⟨235613, by rfl⟩ : syracuseStep 314151 = 471227) B471227
theorem B314191 : Blo 311834 314191 := bstep (se 1 (by rfl) ⟨235643, by rfl⟩ : syracuseStep 314191 = 471287) B471287
theorem B314207 : Blo 311834 314207 := bstep (se 1 (by rfl) ⟨235655, by rfl⟩ : syracuseStep 314207 = 471311) B471311
theorem B707435 : Blo 311834 707435 := bstep (se 1 (by rfl) ⟨530576, by rfl⟩ : syracuseStep 707435 = 1061153) B1061153
theorem B314235 : Blo 311834 314235 := bstep (se 1 (by rfl) ⟨235676, by rfl⟩ : syracuseStep 314235 = 471353) B471353
theorem B707489 : Blo 311834 707489 := bstep (se 2 (by rfl) ⟨265308, by rfl⟩ : syracuseStep 707489 = 530617) B530617
theorem B314287 : Blo 311834 314287 := bstep (se 1 (by rfl) ⟨235715, by rfl⟩ : syracuseStep 314287 = 471431) B471431
theorem B314311 : Blo 311834 314311 := bstep (se 1 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 314311 = 471467) B471467
theorem B314331 : Blo 311834 314331 := bstep (se 1 (by rfl) ⟨235748, by rfl⟩ : syracuseStep 314331 = 471497) B471497
theorem B314407 : Blo 311834 314407 := bstep (se 1 (by rfl) ⟨235805, by rfl⟩ : syracuseStep 314407 = 471611) B471611
theorem B314447 : Blo 311834 314447 := bstep (se 1 (by rfl) ⟨235835, by rfl⟩ : syracuseStep 314447 = 471671) B471671
theorem B314463 : Blo 311834 314463 := bstep (se 1 (by rfl) ⟨235847, by rfl⟩ : syracuseStep 314463 = 471695) B471695
theorem B314491 : Blo 311834 314491 := bstep (se 1 (by rfl) ⟨235868, by rfl⟩ : syracuseStep 314491 = 471737) B471737
theorem B314543 : Blo 311834 314543 := bstep (se 1 (by rfl) ⟨235907, by rfl⟩ : syracuseStep 314543 = 471815) B471815
theorem B314567 : Blo 311834 314567 := bstep (se 1 (by rfl) ⟨235925, by rfl⟩ : syracuseStep 314567 = 471851) B471851
theorem B314587 : Blo 311834 314587 := bstep (se 1 (by rfl) ⟨235940, by rfl⟩ : syracuseStep 314587 = 471881) B471881
theorem B707831 : Blo 311834 707831 := bstep (se 1 (by rfl) ⟨530873, by rfl⟩ : syracuseStep 707831 = 1061747) B1061747
theorem B314663 : Blo 311834 314663 := bstep (se 1 (by rfl) ⟨235997, by rfl⟩ : syracuseStep 314663 = 471995) B471995
theorem B314703 : Blo 311834 314703 := bstep (se 1 (by rfl) ⟨236027, by rfl⟩ : syracuseStep 314703 = 472055) B472055
theorem B4345177 : Blo 311834 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B314719 : Blo 311834 314719 := bstep (se 1 (by rfl) ⟨236039, by rfl⟩ : syracuseStep 314719 = 472079) B472079
theorem B314747 : Blo 311834 314747 := bstep (se 1 (by rfl) ⟨236060, by rfl⟩ : syracuseStep 314747 = 472121) B472121
theorem B314799 : Blo 311834 314799 := bstep (se 1 (by rfl) ⟨236099, by rfl⟩ : syracuseStep 314799 = 472199) B472199
theorem B314823 : Blo 311834 314823 := bstep (se 1 (by rfl) ⟨236117, by rfl⟩ : syracuseStep 314823 = 472235) B472235
theorem B445915 : Blo 311834 445915 := bstep (se 1 (by rfl) ⟨334436, by rfl⟩ : syracuseStep 445915 = 668873) B668873
theorem B314843 : Blo 311834 314843 := bstep (se 1 (by rfl) ⟨236132, by rfl⟩ : syracuseStep 314843 = 472265) B472265
theorem B314919 : Blo 311834 314919 := bstep (se 1 (by rfl) ⟨236189, by rfl⟩ : syracuseStep 314919 = 472379) B472379
theorem B314959 : Blo 311834 314959 := bstep (se 1 (by rfl) ⟨236219, by rfl⟩ : syracuseStep 314959 = 472439) B472439
theorem B314975 : Blo 311834 314975 := bstep (se 1 (by rfl) ⟨236231, by rfl⟩ : syracuseStep 314975 = 472463) B472463
theorem B315003 : Blo 311834 315003 := bstep (se 1 (by rfl) ⟨236252, by rfl⟩ : syracuseStep 315003 = 472505) B472505
theorem B1265287 : Blo 311834 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B315055 : Blo 311834 315055 := bstep (se 1 (by rfl) ⟨236291, by rfl⟩ : syracuseStep 315055 = 472583) B472583
theorem B315079 : Blo 311834 315079 := bstep (se 1 (by rfl) ⟨236309, by rfl⟩ : syracuseStep 315079 = 472619) B472619
theorem B315099 : Blo 311834 315099 := bstep (se 1 (by rfl) ⟨236324, by rfl⟩ : syracuseStep 315099 = 472649) B472649
theorem B315175 : Blo 311834 315175 := bstep (se 1 (by rfl) ⟨236381, by rfl⟩ : syracuseStep 315175 = 472763) B472763
theorem B708425 : Blo 311834 708425 := bstep (se 2 (by rfl) ⟨265659, by rfl⟩ : syracuseStep 708425 = 531319) B531319
theorem B315215 : Blo 311834 315215 := bstep (se 1 (by rfl) ⟨236411, by rfl⟩ : syracuseStep 315215 = 472823) B472823
theorem B315231 : Blo 311834 315231 := bstep (se 1 (by rfl) ⟨236423, by rfl⟩ : syracuseStep 315231 = 472847) B472847
theorem B315259 : Blo 311834 315259 := bstep (se 1 (by rfl) ⟨236444, by rfl⟩ : syracuseStep 315259 = 472889) B472889
theorem B315311 : Blo 311834 315311 := bstep (se 1 (by rfl) ⟨236483, by rfl⟩ : syracuseStep 315311 = 472967) B472967
theorem B315335 : Blo 311834 315335 := bstep (se 1 (by rfl) ⟨236501, by rfl⟩ : syracuseStep 315335 = 473003) B473003
theorem B315355 : Blo 311834 315355 := bstep (se 1 (by rfl) ⟨236516, by rfl⟩ : syracuseStep 315355 = 473033) B473033
theorem B1265665 : Blo 311834 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B315431 : Blo 311834 315431 := bstep (se 1 (by rfl) ⟨236573, by rfl⟩ : syracuseStep 315431 = 473147) B473147
theorem B315471 : Blo 311834 315471 := bstep (se 1 (by rfl) ⟨236603, by rfl⟩ : syracuseStep 315471 = 473207) B473207
theorem B315487 : Blo 311834 315487 := bstep (se 1 (by rfl) ⟨236615, by rfl⟩ : syracuseStep 315487 = 473231) B473231
theorem B315515 : Blo 311834 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B315567 : Blo 311834 315567 := bstep (se 1 (by rfl) ⟨236675, by rfl⟩ : syracuseStep 315567 = 473351) B473351
theorem B315591 : Blo 311834 315591 := bstep (se 1 (by rfl) ⟨236693, by rfl⟩ : syracuseStep 315591 = 473387) B473387
theorem B315611 : Blo 311834 315611 := bstep (se 1 (by rfl) ⟨236708, by rfl⟩ : syracuseStep 315611 = 473417) B473417
theorem B315687 : Blo 311834 315687 := bstep (se 1 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 315687 = 473531) B473531
theorem B315727 : Blo 311834 315727 := bstep (se 1 (by rfl) ⟨236795, by rfl⟩ : syracuseStep 315727 = 473591) B473591
theorem B315743 : Blo 311834 315743 := bstep (se 1 (by rfl) ⟨236807, by rfl⟩ : syracuseStep 315743 = 473615) B473615
theorem B315771 : Blo 311834 315771 := bstep (se 1 (by rfl) ⟨236828, by rfl⟩ : syracuseStep 315771 = 473657) B473657
theorem B315823 : Blo 311834 315823 := bstep (se 1 (by rfl) ⟨236867, by rfl⟩ : syracuseStep 315823 = 473735) B473735
theorem B709217 : Blo 311834 709217 := bstep (se 2 (by rfl) ⟨265956, by rfl⟩ : syracuseStep 709217 = 531913) B531913
theorem B1004167 : Blo 311834 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B5100205 : Blo 311834 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B2282195 : Blo 311834 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B1004243 : Blo 311834 1004243 := bstep (se 1 (by rfl) ⟨753182, by rfl⟩ : syracuseStep 1004243 = 1506365) B1506365
theorem B709559 : Blo 311834 709559 := bstep (se 1 (by rfl) ⟨532169, by rfl⟩ : syracuseStep 709559 = 1064339) B1064339
theorem B3823109 : Blo 311834 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B710153 : Blo 311834 710153 := bstep (se 2 (by rfl) ⟨266307, by rfl⟩ : syracuseStep 710153 = 532615) B532615
theorem B448039 : Blo 311834 448039 := bstep (se 1 (by rfl) ⟨336029, by rfl⟩ : syracuseStep 448039 = 672059) B672059
theorem B2381399 : Blo 311834 2381399 := bstep (se 1 (by rfl) ⟨1786049, by rfl⟩ : syracuseStep 2381399 = 3572099) B3572099
theorem B12342881 : Blo 311834 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B1332875 : Blo 311834 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B710495 : Blo 311834 710495 := bstep (se 1 (by rfl) ⟨532871, by rfl⟩ : syracuseStep 710495 = 1065743) B1065743
theorem B1267883 : Blo 311834 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1137503 : Blo 311834 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B1334191 : Blo 311834 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B351355 : Blo 311834 351355 := bstep (se 1 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 351355 = 527033) B527033
theorem B351823 : Blo 311834 351823 := bstep (se 1 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 351823 = 527735) B527735
theorem B1924823 : Blo 311834 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1335149 : Blo 311834 1335149 := bstep (se 3 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 1335149 = 500681) B500681
theorem B352219 : Blo 311834 352219 := bstep (se 1 (by rfl) ⟨264164, by rfl⟩ : syracuseStep 352219 = 528329) B528329
theorem B2285597 : Blo 311834 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B7659845 : Blo 311834 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B2548097 : Blo 311834 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B1794433 : Blo 311834 1794433 := bstep (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) B1345825
theorem B844175 : Blo 311834 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B352687 : Blo 311834 352687 := bstep (se 1 (by rfl) ⟨264515, by rfl⟩ : syracuseStep 352687 = 529031) B529031
theorem B1696391 : Blo 311834 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B844499 : Blo 311834 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B353119 : Blo 311834 353119 := bstep (se 1 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 353119 = 529679) B529679
theorem B353479 : Blo 311834 353479 := bstep (se 1 (by rfl) ⟨265109, by rfl⟩ : syracuseStep 353479 = 530219) B530219
theorem B4515061 : Blo 311834 4515061 := bstep (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) B423287
theorem B2254243 : Blo 311834 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B2385773 : Blo 311834 2385773 := bstep (se 3 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 2385773 = 894665) B894665
theorem B1337249 : Blo 311834 1337249 := bstep (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) B1002937
theorem B1271809 : Blo 311834 1271809 := bstep (se 2 (by rfl) ⟨476928, by rfl⟩ : syracuseStep 1271809 = 953857) B953857
theorem B354343 : Blo 311834 354343 := bstep (se 1 (by rfl) ⟨265757, by rfl⟩ : syracuseStep 354343 = 531515) B531515
theorem B2550295 : Blo 311834 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B1698515 : Blo 311834 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B3337037 : Blo 311834 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B1502059 : Blo 311834 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B4025537 : Blo 311834 4025537 := bstep (se 2 (by rfl) ⟨1509576, by rfl⟩ : syracuseStep 4025537 = 3019153) B3019153
theorem B2682355 : Blo 311834 2682355 := bstep (se 1 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 2682355 = 4023533) B4023533
theorem B749407 : Blo 311834 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B1699679 : Blo 311834 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B1503137 : Blo 311834 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B12283811 : Blo 311834 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B6057989 : Blo 311834 6057989 := bstep (se 4 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 6057989 = 1135873) B1135873
theorem B1011727 : Blo 311834 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B1503289 : Blo 311834 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B3403853 : Blo 311834 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B1077799 : Blo 311834 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B717511 : Blo 311834 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B2388689 : Blo 311834 2388689 := bstep (se 2 (by rfl) ⟨895758, by rfl⟩ : syracuseStep 2388689 = 1791517) B1791517
theorem B1340495 : Blo 311834 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B1341521 : Blo 311834 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B1210889 : Blo 311834 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B719891 : Blo 311834 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B2391119 : Blo 311834 2391119 := bstep (se 1 (by rfl) ⟨1793339, by rfl⟩ : syracuseStep 2391119 = 3586679) B3586679
theorem B1342939 : Blo 311834 1342939 := bstep (se 1 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 1342939 = 2014409) B2014409
theorem B1507481 : Blo 311834 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B753875 : Blo 311834 753875 := bstep (se 1 (by rfl) ⟨565406, by rfl⟩ : syracuseStep 753875 = 1130813) B1130813
theorem B4849901 : Blo 311834 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B2392577 : Blo 311834 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B2393063 : Blo 311834 2393063 := bstep (se 1 (by rfl) ⟨1794797, by rfl⟩ : syracuseStep 2393063 = 3589595) B3589595
theorem B853409 : Blo 311834 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B4064825 : Blo 311834 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B1345211 : Blo 311834 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B2688713 : Blo 311834 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B1607933 : Blo 311834 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B526601 : Blo 311834 526601 := bstep (se 2 (by rfl) ⟨197475, by rfl⟩ : syracuseStep 526601 = 394951) B394951
theorem B1706771 : Blo 311834 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B6916913 : Blo 311834 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B8621257 : Blo 311834 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B527593 : Blo 311834 527593 := bstep (se 2 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 527593 = 395695) B395695
theorem B527647 : Blo 311834 527647 := bstep (se 1 (by rfl) ⟨395735, by rfl⟩ : syracuseStep 527647 = 791471) B791471
theorem B396667 : Blo 311834 396667 := bstep (se 1 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 396667 = 595001) B595001
theorem B6032839 : Blo 311834 6032839 := bstep (se 1 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 6032839 = 9049259) B9049259
theorem B396895 : Blo 311834 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B528059 : Blo 311834 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B8228587 : Blo 311834 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B888583 : Blo 311834 888583 := bstep (se 1 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 888583 = 1332875) B1332875
theorem B2002745 : Blo 311834 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B3018653 : Blo 311834 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B888857 : Blo 311834 888857 := bstep (se 2 (by rfl) ⟨333321, by rfl⟩ : syracuseStep 888857 = 666643) B666643
theorem B790793 : Blo 311834 790793 := bstep (se 2 (by rfl) ⟨296547, by rfl⟩ : syracuseStep 790793 = 593095) B593095
theorem B594287 : Blo 311834 594287 := bstep (se 1 (by rfl) ⟨445715, by rfl⟩ : syracuseStep 594287 = 891431) B891431
theorem B758335 : Blo 311834 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B791147 : Blo 311834 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B594553 : Blo 311834 594553 := bstep (se 2 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 594553 = 445915) B445915
theorem B3576473 : Blo 311834 3576473 := bstep (se 2 (by rfl) ⟨1341177, by rfl⟩ : syracuseStep 3576473 = 2682355) B2682355
theorem B398135 : Blo 311834 398135 := bstep (se 1 (by rfl) ⟨298601, by rfl⟩ : syracuseStep 398135 = 597203) B597203
theorem B398287 : Blo 311834 398287 := bstep (se 1 (by rfl) ⟨298715, by rfl⟩ : syracuseStep 398287 = 597431) B597431
theorem B1283215 : Blo 311834 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B890099 : Blo 311834 890099 := bstep (se 1 (by rfl) ⟨667574, by rfl⟩ : syracuseStep 890099 = 1335149) B1335149
theorem B791795 : Blo 311834 791795 := bstep (se 1 (by rfl) ⟨593846, by rfl⟩ : syracuseStep 791795 = 1187693) B1187693
theorem B1348969 : Blo 311834 1348969 := bstep (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) B1011727
theorem B529787 : Blo 311834 529787 := bstep (se 1 (by rfl) ⟨397340, by rfl⟩ : syracuseStep 529787 = 794681) B794681
theorem B562783 : Blo 311834 562783 := bstep (se 1 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 562783 = 844175) B844175
theorem B792251 : Blo 311834 792251 := bstep (se 1 (by rfl) ⟨594188, by rfl⟩ : syracuseStep 792251 = 1188377) B1188377
theorem B562999 : Blo 311834 562999 := bstep (se 1 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 562999 = 844499) B844499
theorem B399259 : Blo 311834 399259 := bstep (se 1 (by rfl) ⟨299444, by rfl⟩ : syracuseStep 399259 = 598889) B598889
theorem B792787 : Blo 311834 792787 := bstep (se 1 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 792787 = 1189181) B1189181
theorem B956681 : Blo 311834 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B1612061 : Blo 311834 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B596315 : Blo 311834 596315 := bstep (se 1 (by rfl) ⟨447236, by rfl⟩ : syracuseStep 596315 = 894473) B894473
theorem B530779 : Blo 311834 530779 := bstep (se 1 (by rfl) ⟨398084, by rfl⟩ : syracuseStep 530779 = 796169) B796169
theorem B1055159 : Blo 311834 1055159 := bstep (se 1 (by rfl) ⟨791369, by rfl⟩ : syracuseStep 1055159 = 1582739) B1582739
theorem B891499 : Blo 311834 891499 := bstep (se 1 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 891499 = 1337249) B1337249
theorem B891773 : Blo 311834 891773 := bstep (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) B334415
theorem B596983 : Blo 311834 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B1580147 : Blo 311834 1580147 := bstep (se 1 (by rfl) ⟨1185110, by rfl⟩ : syracuseStep 1580147 = 2370221) B2370221
theorem B793739 : Blo 311834 793739 := bstep (se 1 (by rfl) ⟨595304, by rfl⟩ : syracuseStep 793739 = 1190609) B1190609
theorem B597287 : Blo 311834 597287 := bstep (se 1 (by rfl) ⟨447965, by rfl⟩ : syracuseStep 597287 = 895931) B895931
theorem B531751 : Blo 311834 531751 := bstep (se 1 (by rfl) ⟨398813, by rfl⟩ : syracuseStep 531751 = 797627) B797627
theorem B597385 : Blo 311834 597385 := bstep (se 2 (by rfl) ⟨224019, by rfl⟩ : syracuseStep 597385 = 448039) B448039
theorem B1777211 : Blo 311834 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B794195 : Blo 311834 794195 := bstep (se 1 (by rfl) ⟨595646, by rfl⟩ : syracuseStep 794195 = 1191293) B1191293
theorem B532271 : Blo 311834 532271 := bstep (se 1 (by rfl) ⟨399203, by rfl⟩ : syracuseStep 532271 = 798407) B798407
theorem B1580957 : Blo 311834 1580957 := bstep (se 3 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 1580957 = 592859) B592859
theorem B4038659 : Blo 311834 4038659 := bstep (se 1 (by rfl) ⟨3028994, by rfl⟩ : syracuseStep 4038659 = 6057989) B6057989
theorem B2269235 : Blo 311834 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B5710139 : Blo 311834 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B795055 : Blo 311834 795055 := bstep (se 1 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 795055 = 1192583) B1192583
theorem B6758923 : Blo 311834 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B2695751 : Blo 311834 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B336559 : Blo 311834 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B1581767 : Blo 311834 1581767 := bstep (se 1 (by rfl) ⟨1186325, by rfl⟩ : syracuseStep 1581767 = 2372651) B2372651
theorem B893663 : Blo 311834 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B795359 : Blo 311834 795359 := bstep (se 1 (by rfl) ⟨596519, by rfl⟩ : syracuseStep 795359 = 1193039) B1193039
theorem B467867 : Blo 311834 467867 := bstep (se 1 (by rfl) ⟨350900, by rfl⟩ : syracuseStep 467867 = 701801) B701801
theorem B4268983 : Blo 311834 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B1090685 : Blo 311834 1090685 := bstep (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) B409007
theorem B4826305 : Blo 311834 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1778921 : Blo 311834 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B2696435 : Blo 311834 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B468263 : Blo 311834 468263 := bstep (se 1 (by rfl) ⟨351197, by rfl⟩ : syracuseStep 468263 = 702395) B702395
theorem B468347 : Blo 311834 468347 := bstep (se 1 (by rfl) ⟨351260, by rfl⟩ : syracuseStep 468347 = 702521) B702521
theorem B796027 : Blo 311834 796027 := bstep (se 1 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 796027 = 1194041) B1194041
theorem B894347 : Blo 311834 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B1058237 : Blo 311834 1058237 := bstep (se 3 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 1058237 = 396839) B396839
theorem B468473 : Blo 311834 468473 := bstep (se 2 (by rfl) ⟨175677, by rfl⟩ : syracuseStep 468473 = 351355) B351355
theorem B468575 : Blo 311834 468575 := bstep (se 1 (by rfl) ⟨351431, by rfl⟩ : syracuseStep 468575 = 702863) B702863
theorem B796463 : Blo 311834 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B468791 : Blo 311834 468791 := bstep (se 1 (by rfl) ⟨351593, by rfl⟩ : syracuseStep 468791 = 703187) B703187
theorem B1058615 : Blo 311834 1058615 := bstep (se 1 (by rfl) ⟨793961, by rfl⟩ : syracuseStep 1058615 = 1587923) B1587923
theorem B3385169 : Blo 311834 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B469097 : Blo 311834 469097 := bstep (se 2 (by rfl) ⟨175911, by rfl⟩ : syracuseStep 469097 = 351823) B351823
theorem B1190153 : Blo 311834 1190153 := bstep (se 2 (by rfl) ⟨446307, by rfl⟩ : syracuseStep 1190153 = 892615) B892615
theorem B1059101 : Blo 311834 1059101 := bstep (se 3 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 1059101 = 397163) B397163
theorem B469415 : Blo 311834 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B797111 : Blo 311834 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B469499 : Blo 311834 469499 := bstep (se 1 (by rfl) ⟨352124, by rfl⟩ : syracuseStep 469499 = 704249) B704249
theorem B469625 : Blo 311834 469625 := bstep (se 2 (by rfl) ⟨176109, by rfl⟩ : syracuseStep 469625 = 352219) B352219
theorem B2665133 : Blo 311834 2665133 := bstep (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) B999425
theorem B469679 : Blo 311834 469679 := bstep (se 1 (by rfl) ⟨352259, by rfl⟩ : syracuseStep 469679 = 704519) B704519
theorem B469727 : Blo 311834 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B502699 : Blo 311834 502699 := bstep (se 1 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 502699 = 754049) B754049
theorem B469991 : Blo 311834 469991 := bstep (se 1 (by rfl) ⟨352493, by rfl⟩ : syracuseStep 469991 = 704987) B704987
theorem B896123 : Blo 311834 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B470249 : Blo 311834 470249 := bstep (se 2 (by rfl) ⟨176343, by rfl⟩ : syracuseStep 470249 = 352687) B352687
theorem B470303 : Blo 311834 470303 := bstep (se 1 (by rfl) ⟨352727, by rfl⟩ : syracuseStep 470303 = 705455) B705455
theorem B1060127 : Blo 311834 1060127 := bstep (se 1 (by rfl) ⟨795095, by rfl⟩ : syracuseStep 1060127 = 1590191) B1590191
theorem B34614641 : Blo 311834 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B1584521 : Blo 311834 1584521 := bstep (se 2 (by rfl) ⟨594195, by rfl⟩ : syracuseStep 1584521 = 1188391) B1188391
theorem B798113 : Blo 311834 798113 := bstep (se 2 (by rfl) ⟨299292, by rfl⟩ : syracuseStep 798113 = 598585) B598585
theorem B470471 : Blo 311834 470471 := bstep (se 1 (by rfl) ⟨352853, by rfl⟩ : syracuseStep 470471 = 705707) B705707
theorem B8170993 : Blo 311834 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B2666195 : Blo 311834 2666195 := bstep (se 1 (by rfl) ⟨1999646, by rfl⟩ : syracuseStep 2666195 = 3999293) B3999293
theorem B470825 : Blo 311834 470825 := bstep (se 2 (by rfl) ⟨176559, by rfl⟩ : syracuseStep 470825 = 353119) B353119
theorem B470831 : Blo 311834 470831 := bstep (se 1 (by rfl) ⟨353123, by rfl⟩ : syracuseStep 470831 = 706247) B706247
theorem B798569 : Blo 311834 798569 := bstep (se 2 (by rfl) ⟨299463, by rfl⟩ : syracuseStep 798569 = 598927) B598927
theorem B471305 : Blo 311834 471305 := bstep (se 2 (by rfl) ⟨176739, by rfl⟩ : syracuseStep 471305 = 353479) B353479
theorem B1192265 : Blo 311834 1192265 := bstep (se 2 (by rfl) ⟨447099, by rfl⟩ : syracuseStep 1192265 = 894199) B894199
theorem B471407 : Blo 311834 471407 := bstep (se 1 (by rfl) ⟨353555, by rfl⟩ : syracuseStep 471407 = 707111) B707111
theorem B471623 : Blo 311834 471623 := bstep (se 1 (by rfl) ⟨353717, by rfl⟩ : syracuseStep 471623 = 707435) B707435
theorem B471659 : Blo 311834 471659 := bstep (se 1 (by rfl) ⟨353744, by rfl⟩ : syracuseStep 471659 = 707489) B707489
theorem B1585817 : Blo 311834 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B2143055 : Blo 311834 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B471887 : Blo 311834 471887 := bstep (se 1 (by rfl) ⟨353915, by rfl⟩ : syracuseStep 471887 = 707831) B707831
theorem B701639 : Blo 311834 701639 := bstep (se 1 (by rfl) ⟨526229, by rfl⟩ : syracuseStep 701639 = 1052459) B1052459
theorem B472283 : Blo 311834 472283 := bstep (se 1 (by rfl) ⟨354212, by rfl⟩ : syracuseStep 472283 = 708425) B708425
theorem B701819 : Blo 311834 701819 := bstep (se 1 (by rfl) ⟨526364, by rfl⟩ : syracuseStep 701819 = 1052729) B1052729
theorem B472457 : Blo 311834 472457 := bstep (se 2 (by rfl) ⟨177171, by rfl⟩ : syracuseStep 472457 = 354343) B354343
theorem B701945 : Blo 311834 701945 := bstep (se 2 (by rfl) ⟨263229, by rfl⟩ : syracuseStep 701945 = 526459) B526459
theorem B702035 : Blo 311834 702035 := bstep (se 1 (by rfl) ⟨526526, by rfl⟩ : syracuseStep 702035 = 1053053) B1053053
theorem B1062557 : Blo 311834 1062557 := bstep (se 3 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 1062557 = 398459) B398459
theorem B505531 : Blo 311834 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B472811 : Blo 311834 472811 := bstep (se 1 (by rfl) ⟨354608, by rfl⟩ : syracuseStep 472811 = 709217) B709217
theorem B702215 : Blo 311834 702215 := bstep (se 1 (by rfl) ⟨526661, by rfl⟩ : syracuseStep 702215 = 1053323) B1053323
theorem B505607 : Blo 311834 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B473039 : Blo 311834 473039 := bstep (se 1 (by rfl) ⟨354779, by rfl⟩ : syracuseStep 473039 = 709559) B709559
theorem B1063097 : Blo 311834 1063097 := bstep (se 2 (by rfl) ⟨398661, by rfl⟩ : syracuseStep 1063097 = 797323) B797323
theorem B473435 : Blo 311834 473435 := bstep (se 1 (by rfl) ⟨355076, by rfl⟩ : syracuseStep 473435 = 710153) B710153
theorem B702827 : Blo 311834 702827 := bstep (se 1 (by rfl) ⟨527120, by rfl⟩ : syracuseStep 702827 = 1054241) B1054241
theorem B1587599 : Blo 311834 1587599 := bstep (se 1 (by rfl) ⟨1190699, by rfl⟩ : syracuseStep 1587599 = 2381399) B2381399
theorem B1685927 : Blo 311834 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B702971 : Blo 311834 702971 := bstep (se 1 (by rfl) ⟨527228, by rfl⟩ : syracuseStep 702971 = 1054457) B1054457
theorem B473663 : Blo 311834 473663 := bstep (se 1 (by rfl) ⟨355247, by rfl⟩ : syracuseStep 473663 = 710495) B710495
theorem B703097 : Blo 311834 703097 := bstep (se 2 (by rfl) ⟨263661, by rfl⟩ : syracuseStep 703097 = 527323) B527323
theorem B703151 : Blo 311834 703151 := bstep (se 1 (by rfl) ⟨527363, by rfl⟩ : syracuseStep 703151 = 1054727) B1054727
theorem B703223 : Blo 311834 703223 := bstep (se 1 (by rfl) ⟨527417, by rfl⟩ : syracuseStep 703223 = 1054835) B1054835
theorem B703403 : Blo 311834 703403 := bstep (se 1 (by rfl) ⟨527552, by rfl⟩ : syracuseStep 703403 = 1055105) B1055105
theorem B6011927 : Blo 311834 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B703943 : Blo 311834 703943 := bstep (se 1 (by rfl) ⟨527957, by rfl⟩ : syracuseStep 703943 = 1055915) B1055915
theorem B1687049 : Blo 311834 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B2866747 : Blo 311834 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1195681 : Blo 311834 1195681 := bstep (se 2 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 1195681 = 896761) B896761
theorem B1064609 : Blo 311834 1064609 := bstep (se 2 (by rfl) ⟨399228, by rfl⟩ : syracuseStep 1064609 = 798457) B798457
theorem B999209 : Blo 311834 999209 := bstep (se 2 (by rfl) ⟨374703, by rfl⟩ : syracuseStep 999209 = 749407) B749407
theorem B704303 : Blo 311834 704303 := bstep (se 1 (by rfl) ⟨528227, by rfl⟩ : syracuseStep 704303 = 1056455) B1056455
theorem B1687553 : Blo 311834 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B1523731 : Blo 311834 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B704879 : Blo 311834 704879 := bstep (se 1 (by rfl) ⟨528659, by rfl⟩ : syracuseStep 704879 = 1057319) B1057319
theorem B377255 : Blo 311834 377255 := bstep (se 1 (by rfl) ⟨282941, by rfl⟩ : syracuseStep 377255 = 565883) B565883
theorem B1130927 : Blo 311834 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B704951 : Blo 311834 704951 := bstep (se 1 (by rfl) ⟨528713, by rfl⟩ : syracuseStep 704951 = 1057427) B1057427
theorem B1589705 : Blo 311834 1589705 := bstep (se 2 (by rfl) ⟨596139, by rfl⟩ : syracuseStep 1589705 = 1192279) B1192279
theorem B1065473 : Blo 311834 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B311871 : Blo 311834 311871 := bstep (se 1 (by rfl) ⟨233903, by rfl⟩ : syracuseStep 311871 = 467807) B467807
theorem B311879 : Blo 311834 311879 := bstep (se 1 (by rfl) ⟨233909, by rfl⟩ : syracuseStep 311879 = 467819) B467819
theorem B705095 : Blo 311834 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B705131 : Blo 311834 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B312031 : Blo 311834 312031 := bstep (se 1 (by rfl) ⟨234023, by rfl⟩ : syracuseStep 312031 = 468047) B468047
theorem B312111 : Blo 311834 312111 := bstep (se 1 (by rfl) ⟨234083, by rfl⟩ : syracuseStep 312111 = 468167) B468167
theorem B6800273 : Blo 311834 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B312219 : Blo 311834 312219 := bstep (se 1 (by rfl) ⟨234164, by rfl⟩ : syracuseStep 312219 = 468329) B468329
theorem B5129153 : Blo 311834 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B312271 : Blo 311834 312271 := bstep (se 1 (by rfl) ⟨234203, by rfl⟩ : syracuseStep 312271 = 468407) B468407
theorem B4506587 : Blo 311834 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B312295 : Blo 311834 312295 := bstep (se 1 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 312295 = 468443) B468443
theorem B705527 : Blo 311834 705527 := bstep (se 1 (by rfl) ⟨529145, by rfl⟩ : syracuseStep 705527 = 1058291) B1058291
theorem B1590515 : Blo 311834 1590515 := bstep (se 1 (by rfl) ⟨1192886, by rfl⟩ : syracuseStep 1590515 = 2385773) B2385773
theorem B312607 : Blo 311834 312607 := bstep (se 1 (by rfl) ⟨234455, by rfl⟩ : syracuseStep 312607 = 468911) B468911
theorem B312667 : Blo 311834 312667 := bstep (se 1 (by rfl) ⟨234500, by rfl⟩ : syracuseStep 312667 = 469001) B469001
theorem B705887 : Blo 311834 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B312687 : Blo 311834 312687 := bstep (se 1 (by rfl) ⟨234515, by rfl⟩ : syracuseStep 312687 = 469031) B469031
theorem B312743 : Blo 311834 312743 := bstep (se 1 (by rfl) ⟨234557, by rfl⟩ : syracuseStep 312743 = 469115) B469115
theorem B312827 : Blo 311834 312827 := bstep (se 1 (by rfl) ⟨234620, by rfl⟩ : syracuseStep 312827 = 469241) B469241
theorem B1197625 : Blo 311834 1197625 := bstep (se 2 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 1197625 = 898219) B898219
theorem B312895 : Blo 311834 312895 := bstep (se 1 (by rfl) ⟨234671, by rfl⟩ : syracuseStep 312895 = 469343) B469343
theorem B312903 : Blo 311834 312903 := bstep (se 1 (by rfl) ⟨234677, by rfl⟩ : syracuseStep 312903 = 469355) B469355
theorem B378475 : Blo 311834 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B25740989 : Blo 311834 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B313055 : Blo 311834 313055 := bstep (se 1 (by rfl) ⟨234791, by rfl⟩ : syracuseStep 313055 = 469583) B469583
theorem B706283 : Blo 311834 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B313135 : Blo 311834 313135 := bstep (se 1 (by rfl) ⟨234851, by rfl⟩ : syracuseStep 313135 = 469703) B469703
theorem B1132343 : Blo 311834 1132343 := bstep (se 1 (by rfl) ⟨849257, by rfl⟩ : syracuseStep 1132343 = 1698515) B1698515
theorem B706409 : Blo 311834 706409 := bstep (se 2 (by rfl) ⟨264903, by rfl⟩ : syracuseStep 706409 = 529807) B529807
theorem B1197929 : Blo 311834 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B3000199 : Blo 311834 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B313243 : Blo 311834 313243 := bstep (se 1 (by rfl) ⟨234932, by rfl⟩ : syracuseStep 313243 = 469865) B469865
theorem B313295 : Blo 311834 313295 := bstep (se 1 (by rfl) ⟨234971, by rfl⟩ : syracuseStep 313295 = 469943) B469943
theorem B313319 : Blo 311834 313319 := bstep (se 1 (by rfl) ⟨234989, by rfl⟩ : syracuseStep 313319 = 469979) B469979
theorem B13551745 : Blo 311834 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B313631 : Blo 311834 313631 := bstep (se 1 (by rfl) ⟨235223, by rfl⟩ : syracuseStep 313631 = 470447) B470447
theorem B313691 : Blo 311834 313691 := bstep (se 1 (by rfl) ⟨235268, by rfl⟩ : syracuseStep 313691 = 470537) B470537
theorem B313711 : Blo 311834 313711 := bstep (se 1 (by rfl) ⟨235283, by rfl⟩ : syracuseStep 313711 = 470567) B470567
theorem B313767 : Blo 311834 313767 := bstep (se 1 (by rfl) ⟨235325, by rfl⟩ : syracuseStep 313767 = 470651) B470651
theorem B313851 : Blo 311834 313851 := bstep (se 1 (by rfl) ⟨235388, by rfl⟩ : syracuseStep 313851 = 470777) B470777
theorem B313919 : Blo 311834 313919 := bstep (se 1 (by rfl) ⟨235439, by rfl⟩ : syracuseStep 313919 = 470879) B470879
theorem B1133119 : Blo 311834 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B313927 : Blo 311834 313927 := bstep (se 1 (by rfl) ⟨235445, by rfl⟩ : syracuseStep 313927 = 470891) B470891
theorem B1002091 : Blo 311834 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B707255 : Blo 311834 707255 := bstep (se 1 (by rfl) ⟨530441, by rfl⟩ : syracuseStep 707255 = 1060883) B1060883
theorem B3001043 : Blo 311834 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B314079 : Blo 311834 314079 := bstep (se 1 (by rfl) ⟨235559, by rfl⟩ : syracuseStep 314079 = 471119) B471119
theorem B314159 : Blo 311834 314159 := bstep (se 1 (by rfl) ⟨235619, by rfl⟩ : syracuseStep 314159 = 471239) B471239
theorem B707471 : Blo 311834 707471 := bstep (se 1 (by rfl) ⟨530603, by rfl⟩ : syracuseStep 707471 = 1061207) B1061207
theorem B314267 : Blo 311834 314267 := bstep (se 1 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 314267 = 471401) B471401
theorem B314319 : Blo 311834 314319 := bstep (se 1 (by rfl) ⟨235739, by rfl⟩ : syracuseStep 314319 = 471479) B471479
theorem B314343 : Blo 311834 314343 := bstep (se 1 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 314343 = 471515) B471515
theorem B1592459 : Blo 311834 1592459 := bstep (se 1 (by rfl) ⟨1194344, by rfl⟩ : syracuseStep 1592459 = 2388689) B2388689
theorem B314655 : Blo 311834 314655 := bstep (se 1 (by rfl) ⟨235991, by rfl⟩ : syracuseStep 314655 = 471983) B471983
theorem B314715 : Blo 311834 314715 := bstep (se 1 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 314715 = 472073) B472073
theorem B314735 : Blo 311834 314735 := bstep (se 1 (by rfl) ⟨236051, by rfl⟩ : syracuseStep 314735 = 472103) B472103
theorem B314791 : Blo 311834 314791 := bstep (se 1 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 314791 = 472187) B472187
theorem B314875 : Blo 311834 314875 := bstep (se 1 (by rfl) ⟨236156, by rfl⟩ : syracuseStep 314875 = 472313) B472313
theorem B314943 : Blo 311834 314943 := bstep (se 1 (by rfl) ⟨236207, by rfl⟩ : syracuseStep 314943 = 472415) B472415
theorem B314951 : Blo 311834 314951 := bstep (se 1 (by rfl) ⟨236213, by rfl⟩ : syracuseStep 314951 = 472427) B472427
theorem B708191 : Blo 311834 708191 := bstep (se 1 (by rfl) ⟨531143, by rfl⟩ : syracuseStep 708191 = 1062287) B1062287
theorem B315103 : Blo 311834 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B315183 : Blo 311834 315183 := bstep (se 1 (by rfl) ⟨236387, by rfl⟩ : syracuseStep 315183 = 472775) B472775
theorem B708407 : Blo 311834 708407 := bstep (se 1 (by rfl) ⟨531305, by rfl⟩ : syracuseStep 708407 = 1062611) B1062611
theorem B315291 : Blo 311834 315291 := bstep (se 1 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 315291 = 472937) B472937
theorem B315343 : Blo 311834 315343 := bstep (se 1 (by rfl) ⟨236507, by rfl⟩ : syracuseStep 315343 = 473015) B473015
theorem B315367 : Blo 311834 315367 := bstep (se 1 (by rfl) ⟨236525, by rfl⟩ : syracuseStep 315367 = 473051) B473051
theorem B708713 : Blo 311834 708713 := bstep (se 2 (by rfl) ⟨265767, by rfl⟩ : syracuseStep 708713 = 531535) B531535
theorem B315679 : Blo 311834 315679 := bstep (se 1 (by rfl) ⟨236759, by rfl⟩ : syracuseStep 315679 = 473519) B473519
theorem B807259 : Blo 311834 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B315739 : Blo 311834 315739 := bstep (se 1 (by rfl) ⟨236804, by rfl⟩ : syracuseStep 315739 = 473609) B473609
theorem B315759 : Blo 311834 315759 := bstep (se 1 (by rfl) ⟨236819, by rfl⟩ : syracuseStep 315759 = 473639) B473639
theorem B315815 : Blo 311834 315815 := bstep (se 1 (by rfl) ⟨236861, by rfl⟩ : syracuseStep 315815 = 473723) B473723
theorem B6410771 : Blo 311834 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B709199 : Blo 311834 709199 := bstep (se 1 (by rfl) ⟨531899, by rfl⟩ : syracuseStep 709199 = 1063799) B1063799
theorem B1790585 : Blo 311834 1790585 := bstep (se 2 (by rfl) ⟨671469, by rfl⟩ : syracuseStep 1790585 = 1342939) B1342939
theorem B479927 : Blo 311834 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B1594079 : Blo 311834 1594079 := bstep (se 1 (by rfl) ⟨1195559, by rfl⟩ : syracuseStep 1594079 = 2391119) B2391119
theorem B709343 : Blo 311834 709343 := bstep (se 1 (by rfl) ⟨532007, by rfl⟩ : syracuseStep 709343 = 1064015) B1064015
theorem B709595 : Blo 311834 709595 := bstep (se 1 (by rfl) ⟨532196, by rfl⟩ : syracuseStep 709595 = 1064393) B1064393
theorem B709775 : Blo 311834 709775 := bstep (se 1 (by rfl) ⟨532331, by rfl⟩ : syracuseStep 709775 = 1064663) B1064663
theorem B709865 : Blo 311834 709865 := bstep (se 2 (by rfl) ⟨266199, by rfl⟩ : syracuseStep 709865 = 532399) B532399
theorem B709919 : Blo 311834 709919 := bstep (se 1 (by rfl) ⟨532439, by rfl⟩ : syracuseStep 709919 = 1064879) B1064879
theorem B23287175 : Blo 311834 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B8017541 : Blo 311834 8017541 := bstep (se 4 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 8017541 = 1503289) B1503289
theorem B710441 : Blo 311834 710441 := bstep (se 2 (by rfl) ⟨266415, by rfl⟩ : syracuseStep 710441 = 532831) B532831
theorem B1005833 : Blo 311834 1005833 := bstep (se 2 (by rfl) ⟨377187, by rfl⟩ : syracuseStep 1005833 = 754375) B754375
theorem B448859 : Blo 311834 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B350815 : Blo 311834 350815 := bstep (se 1 (by rfl) ⟨263111, by rfl⟩ : syracuseStep 350815 = 526223) B526223
theorem B1596347 : Blo 311834 1596347 := bstep (se 1 (by rfl) ⟨1197260, by rfl⟩ : syracuseStep 1596347 = 2394521) B2394521
theorem B6020081 : Blo 311834 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B3005657 : Blo 311834 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B5790937 : Blo 311834 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B6085853 : Blo 311834 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B2677981 : Blo 311834 2677981 := bstep (se 3 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 2677981 = 1004243) B1004243
theorem B1007063 : Blo 311834 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B351967 : Blo 311834 351967 := bstep (se 1 (by rfl) ⟨263975, by rfl⟩ : syracuseStep 351967 = 527951) B527951
theorem B1695745 : Blo 311834 1695745 := bstep (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) B1271809
theorem B2187383 : Blo 311834 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B1597643 : Blo 311834 1597643 := bstep (se 1 (by rfl) ⟨1198232, by rfl⟩ : syracuseStep 1597643 = 2396465) B2396465
theorem B352543 : Blo 311834 352543 := bstep (se 1 (by rfl) ⟨264407, by rfl⟩ : syracuseStep 352543 = 528815) B528815
theorem B352831 : Blo 311834 352831 := bstep (se 1 (by rfl) ⟨264623, by rfl⟩ : syracuseStep 352831 = 529247) B529247
theorem B1794707 : Blo 311834 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B1204919 : Blo 311834 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B3400393 : Blo 311834 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B2384801 : Blo 311834 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B2548739 : Blo 311834 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B1336463 : Blo 311834 1336463 := bstep (se 1 (by rfl) ⟨1002347, by rfl⟩ : syracuseStep 1336463 = 2004695) B2004695
theorem B353659 : Blo 311834 353659 := bstep (se 1 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 353659 = 530489) B530489
theorem B845255 : Blo 311834 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B845473 : Blo 311834 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B5793569 : Blo 311834 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B354127 : Blo 311834 354127 := bstep (se 1 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 354127 = 531191) B531191
theorem B3401605 : Blo 311834 3401605 := bstep (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) B637801
theorem B354523 : Blo 311834 354523 := bstep (se 1 (by rfl) ⟨265892, by rfl⟩ : syracuseStep 354523 = 531785) B531785
theorem B1010087 : Blo 311834 1010087 := bstep (se 1 (by rfl) ⟨757565, by rfl⟩ : syracuseStep 1010087 = 1515131) B1515131
theorem B354811 : Blo 311834 354811 := bstep (se 1 (by rfl) ⟨266108, by rfl⟩ : syracuseStep 354811 = 532217) B532217
theorem B354991 : Blo 311834 354991 := bstep (se 1 (by rfl) ⟨266243, by rfl⟩ : syracuseStep 354991 = 532487) B532487
theorem B5106563 : Blo 311834 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B1698731 : Blo 311834 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B355279 : Blo 311834 355279 := bstep (se 1 (by rfl) ⟨266459, by rfl⟩ : syracuseStep 355279 = 532919) B532919
theorem B2387231 : Blo 311834 2387231 := bstep (se 1 (by rfl) ⟨1790423, by rfl⟩ : syracuseStep 2387231 = 3580847) B3580847
theorem B1437065 : Blo 311834 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B1338839 : Blo 311834 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B1338889 : Blo 311834 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B3239837 : Blo 311834 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B3502081 : Blo 311834 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B11497949 : Blo 311834 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B2224691 : Blo 311834 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B2683691 : Blo 311834 2683691 := bstep (se 1 (by rfl) ⟨2012768, by rfl⟩ : syracuseStep 2683691 = 4025537) B4025537
theorem B1340563 : Blo 311834 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B750791 : Blo 311834 750791 := bstep (se 1 (by rfl) ⟨563093, by rfl⟩ : syracuseStep 750791 = 1126187) B1126187
theorem B8189207 : Blo 311834 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B1144961 : Blo 311834 1144961 := bstep (se 2 (by rfl) ⟨429360, by rfl⟩ : syracuseStep 1144961 = 858721) B858721
theorem B1735231 : Blo 311834 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B4291145 : Blo 311834 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B424759 : Blo 311834 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B2260993 : Blo 311834 2260993 := bstep (se 2 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 2260993 = 1695745) B1695745
theorem B18677765 : Blo 311834 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B2031641 : Blo 311834 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B5833021 : Blo 311834 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B9011897 : Blo 311834 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B3015805 : Blo 311834 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B754895 : Blo 311834 754895 := bstep (se 1 (by rfl) ⟨566171, by rfl⟩ : syracuseStep 754895 = 1132343) B1132343
theorem B2000695 : Blo 311834 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B1279805 : Blo 311834 1279805 := bstep (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) B479927
theorem B4000265 : Blo 311834 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B592571 : Blo 311834 592571 := bstep (se 1 (by rfl) ⟨444428, by rfl⟩ : syracuseStep 592571 = 888857) B888857
theorem B527195 : Blo 311834 527195 := bstep (se 1 (by rfl) ⟨395396, by rfl⟩ : syracuseStep 527195 = 790793) B790793
theorem B396191 : Blo 311834 396191 := bstep (se 1 (by rfl) ⟨297143, by rfl⟩ : syracuseStep 396191 = 594287) B594287
theorem B527431 : Blo 311834 527431 := bstep (se 1 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 527431 = 791147) B791147
theorem B1510825 : Blo 311834 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B593399 : Blo 311834 593399 := bstep (se 1 (by rfl) ⟨445049, by rfl⟩ : syracuseStep 593399 = 890099) B890099
theorem B527863 : Blo 311834 527863 := bstep (se 1 (by rfl) ⟨395897, by rfl⟩ : syracuseStep 527863 = 791795) B791795
theorem B5345027 : Blo 311834 5345027 := bstep (se 1 (by rfl) ⟨4008770, by rfl⟩ : syracuseStep 5345027 = 8017541) B8017541
theorem B528167 : Blo 311834 528167 := bstep (se 1 (by rfl) ⟨396125, by rfl⟩ : syracuseStep 528167 = 792251) B792251
theorem B397543 : Blo 311834 397543 := bstep (se 1 (by rfl) ⟨298157, by rfl⟩ : syracuseStep 397543 = 596315) B596315
theorem B528889 : Blo 311834 528889 := bstep (se 2 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 528889 = 396667) B396667
theorem B594515 : Blo 311834 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B1053431 : Blo 311834 1053431 := bstep (se 1 (by rfl) ⟨790073, by rfl⟩ : syracuseStep 1053431 = 1580147) B1580147
theorem B529159 : Blo 311834 529159 := bstep (se 1 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 529159 = 793739) B793739
theorem B529193 : Blo 311834 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B2003771 : Blo 311834 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B398191 : Blo 311834 398191 := bstep (se 1 (by rfl) ⟨298643, by rfl⟩ : syracuseStep 398191 = 597287) B597287
theorem B1184777 : Blo 311834 1184777 := bstep (se 2 (by rfl) ⟨444291, by rfl⟩ : syracuseStep 1184777 = 888583) B888583
theorem B1184807 : Blo 311834 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B529463 : Blo 311834 529463 := bstep (se 1 (by rfl) ⟨397097, by rfl⟩ : syracuseStep 529463 = 794195) B794195
theorem B1053971 : Blo 311834 1053971 := bstep (se 1 (by rfl) ⟨790478, by rfl⟩ : syracuseStep 1053971 = 1580957) B1580957
theorem B2692439 : Blo 311834 2692439 := bstep (se 1 (by rfl) ⟨2019329, by rfl⟩ : syracuseStep 2692439 = 4038659) B4038659
theorem B3806759 : Blo 311834 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B1054511 : Blo 311834 1054511 := bstep (se 1 (by rfl) ⟨790883, by rfl⟩ : syracuseStep 1054511 = 1581767) B1581767
theorem B595775 : Blo 311834 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B530239 : Blo 311834 530239 := bstep (se 1 (by rfl) ⟨397679, by rfl⟩ : syracuseStep 530239 = 795359) B795359
theorem B890975 : Blo 311834 890975 := bstep (se 1 (by rfl) ⟨668231, by rfl⟩ : syracuseStep 890975 = 1336463) B1336463
theorem B1185947 : Blo 311834 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B792737 : Blo 311834 792737 := bstep (se 2 (by rfl) ⟨297276, by rfl⟩ : syracuseStep 792737 = 594553) B594553
theorem B596231 : Blo 311834 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B530975 : Blo 311834 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B531049 : Blo 311834 531049 := bstep (se 2 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 531049 = 398287) B398287
theorem B793435 : Blo 311834 793435 := bstep (se 1 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 793435 = 1190153) B1190153
theorem B1710953 : Blo 311834 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B531407 : Blo 311834 531407 := bstep (se 1 (by rfl) ⟨398555, by rfl⟩ : syracuseStep 531407 = 797111) B797111
theorem B1776755 : Blo 311834 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B23076427 : Blo 311834 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B1056347 : Blo 311834 1056347 := bstep (se 1 (by rfl) ⟨792260, by rfl⟩ : syracuseStep 1056347 = 1584521) B1584521
theorem B958043 : Blo 311834 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B532075 : Blo 311834 532075 := bstep (se 1 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 532075 = 798113) B798113
theorem B892559 : Blo 311834 892559 := bstep (se 1 (by rfl) ⟨669419, by rfl⟩ : syracuseStep 892559 = 1338839) B1338839
theorem B1777463 : Blo 311834 1777463 := bstep (se 1 (by rfl) ⟨1333097, by rfl⟩ : syracuseStep 1777463 = 2666195) B2666195
theorem B532345 : Blo 311834 532345 := bstep (se 2 (by rfl) ⟨199629, by rfl⟩ : syracuseStep 532345 = 399259) B399259
theorem B532379 : Blo 311834 532379 := bstep (se 1 (by rfl) ⟨399284, by rfl⟩ : syracuseStep 532379 = 798569) B798569
theorem B794843 : Blo 311834 794843 := bstep (se 1 (by rfl) ⟨596132, by rfl⟩ : syracuseStep 794843 = 1192265) B1192265
theorem B1057049 : Blo 311834 1057049 := bstep (se 2 (by rfl) ⟨396393, by rfl⟩ : syracuseStep 1057049 = 792787) B792787
theorem B1483127 : Blo 311834 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B1057211 : Blo 311834 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B467753 : Blo 311834 467753 := bstep (se 2 (by rfl) ⟨175407, by rfl⟩ : syracuseStep 467753 = 350815) B350815
theorem B467759 : Blo 311834 467759 := bstep (se 1 (by rfl) ⟨350819, by rfl⟩ : syracuseStep 467759 = 701639) B701639
theorem B500527 : Blo 311834 500527 := bstep (se 1 (by rfl) ⟨375395, by rfl⟩ : syracuseStep 500527 = 750791) B750791
theorem B1188665 : Blo 311834 1188665 := bstep (se 2 (by rfl) ⟨445749, by rfl⟩ : syracuseStep 1188665 = 891499) B891499
theorem B467879 : Blo 311834 467879 := bstep (se 1 (by rfl) ⟨350909, by rfl⟩ : syracuseStep 467879 = 701819) B701819
theorem B467963 : Blo 311834 467963 := bstep (se 1 (by rfl) ⟨350972, by rfl⟩ : syracuseStep 467963 = 701945) B701945
theorem B468023 : Blo 311834 468023 := bstep (se 1 (by rfl) ⟨351017, by rfl⟩ : syracuseStep 468023 = 702035) B702035
theorem B566345 : Blo 311834 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B468143 : Blo 311834 468143 := bstep (se 1 (by rfl) ⟨351107, by rfl⟩ : syracuseStep 468143 = 702215) B702215
theorem B795977 : Blo 311834 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B763307 : Blo 311834 763307 := bstep (se 1 (by rfl) ⟨572480, by rfl⟩ : syracuseStep 763307 = 1144961) B1144961
theorem B468551 : Blo 311834 468551 := bstep (se 1 (by rfl) ⟨351413, by rfl⟩ : syracuseStep 468551 = 702827) B702827
theorem B1058399 : Blo 311834 1058399 := bstep (se 1 (by rfl) ⟨793799, by rfl⟩ : syracuseStep 1058399 = 1587599) B1587599
theorem B1123951 : Blo 311834 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B468647 : Blo 311834 468647 := bstep (se 1 (by rfl) ⟨351485, by rfl⟩ : syracuseStep 468647 = 702971) B702971
theorem B2860763 : Blo 311834 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B468731 : Blo 311834 468731 := bstep (se 1 (by rfl) ⟨351548, by rfl⟩ : syracuseStep 468731 = 703097) B703097
theorem B468767 : Blo 311834 468767 := bstep (se 1 (by rfl) ⟨351575, by rfl⟩ : syracuseStep 468767 = 703151) B703151
theorem B468815 : Blo 311834 468815 := bstep (se 1 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 468815 = 703223) B703223
theorem B796513 : Blo 311834 796513 := bstep (se 2 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 796513 = 597385) B597385
theorem B468935 : Blo 311834 468935 := bstep (se 1 (by rfl) ⟨351701, by rfl⟩ : syracuseStep 468935 = 703403) B703403
theorem B4007951 : Blo 311834 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B469289 : Blo 311834 469289 := bstep (se 2 (by rfl) ⟨175983, by rfl⟩ : syracuseStep 469289 = 351967) B351967
theorem B469295 : Blo 311834 469295 := bstep (se 1 (by rfl) ⟨351971, by rfl⟩ : syracuseStep 469295 = 703943) B703943
theorem B1124699 : Blo 311834 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B666139 : Blo 311834 666139 := bstep (se 1 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 666139 = 999209) B999209
theorem B469535 : Blo 311834 469535 := bstep (se 1 (by rfl) ⟨352151, by rfl⟩ : syracuseStep 469535 = 704303) B704303
theorem B1125035 : Blo 311834 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B502583 : Blo 311834 502583 := bstep (se 1 (by rfl) ⟨376937, by rfl⟩ : syracuseStep 502583 = 753875) B753875
theorem B469919 : Blo 311834 469919 := bstep (se 1 (by rfl) ⟨352439, by rfl⟩ : syracuseStep 469919 = 704879) B704879
theorem B469967 : Blo 311834 469967 := bstep (se 1 (by rfl) ⟨352475, by rfl⟩ : syracuseStep 469967 = 704951) B704951
theorem B1059803 : Blo 311834 1059803 := bstep (se 1 (by rfl) ⟨794852, by rfl⟩ : syracuseStep 1059803 = 1589705) B1589705
theorem B470057 : Blo 311834 470057 := bstep (se 2 (by rfl) ⟨176271, by rfl⟩ : syracuseStep 470057 = 352543) B352543
theorem B470063 : Blo 311834 470063 := bstep (se 1 (by rfl) ⟨352547, by rfl⟩ : syracuseStep 470063 = 705095) B705095
theorem B470087 : Blo 311834 470087 := bstep (se 1 (by rfl) ⟨352565, by rfl⟩ : syracuseStep 470087 = 705131) B705131
theorem B1060073 : Blo 311834 1060073 := bstep (se 2 (by rfl) ⟨397527, by rfl⟩ : syracuseStep 1060073 = 795055) B795055
theorem B4533515 : Blo 311834 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B3419435 : Blo 311834 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B470351 : Blo 311834 470351 := bstep (se 1 (by rfl) ⟨352763, by rfl⟩ : syracuseStep 470351 = 705527) B705527
theorem B470441 : Blo 311834 470441 := bstep (se 2 (by rfl) ⟨176415, by rfl⟩ : syracuseStep 470441 = 352831) B352831
theorem B1060343 : Blo 311834 1060343 := bstep (se 1 (by rfl) ⟨795257, by rfl⟩ : syracuseStep 1060343 = 1590515) B1590515
theorem B470591 : Blo 311834 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B4533857 : Blo 311834 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B568939 : Blo 311834 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B896807 : Blo 311834 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B470855 : Blo 311834 470855 := bstep (se 1 (by rfl) ⟨353141, by rfl⟩ : syracuseStep 470855 = 706283) B706283
theorem B470939 : Blo 311834 470939 := bstep (se 1 (by rfl) ⟨353204, by rfl⟩ : syracuseStep 470939 = 706409) B706409
theorem B798619 : Blo 311834 798619 := bstep (se 1 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 798619 = 1197929) B1197929
theorem B6435073 : Blo 311834 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B471503 : Blo 311834 471503 := bstep (se 1 (by rfl) ⟨353627, by rfl⟩ : syracuseStep 471503 = 707255) B707255
theorem B471545 : Blo 311834 471545 := bstep (se 2 (by rfl) ⟨176829, by rfl⟩ : syracuseStep 471545 = 353659) B353659
theorem B1061369 : Blo 311834 1061369 := bstep (se 2 (by rfl) ⟨398013, by rfl⟩ : syracuseStep 1061369 = 796027) B796027
theorem B471647 : Blo 311834 471647 := bstep (se 1 (by rfl) ⟨353735, by rfl⟩ : syracuseStep 471647 = 707471) B707471
theorem B1061639 : Blo 311834 1061639 := bstep (se 1 (by rfl) ⟨796229, by rfl⟩ : syracuseStep 1061639 = 1592459) B1592459
theorem B1061693 : Blo 311834 1061693 := bstep (se 3 (by rfl) ⟨199067, by rfl⟩ : syracuseStep 1061693 = 398135) B398135
theorem B5714813 : Blo 311834 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B1127297 : Blo 311834 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B472127 : Blo 311834 472127 := bstep (se 1 (by rfl) ⟨354095, by rfl⟩ : syracuseStep 472127 = 708191) B708191
theorem B472169 : Blo 311834 472169 := bstep (se 2 (by rfl) ⟨177063, by rfl⟩ : syracuseStep 472169 = 354127) B354127
theorem B4535473 : Blo 311834 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B472271 : Blo 311834 472271 := bstep (se 1 (by rfl) ⟨354203, by rfl⟩ : syracuseStep 472271 = 708407) B708407
theorem B2012435 : Blo 311834 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B472475 : Blo 311834 472475 := bstep (se 1 (by rfl) ⟨354356, by rfl⟩ : syracuseStep 472475 = 708713) B708713
theorem B18068993 : Blo 311834 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B472697 : Blo 311834 472697 := bstep (se 2 (by rfl) ⟨177261, by rfl⟩ : syracuseStep 472697 = 354523) B354523
theorem B4273847 : Blo 311834 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B472799 : Blo 311834 472799 := bstep (se 1 (by rfl) ⟨354599, by rfl⟩ : syracuseStep 472799 = 709199) B709199
theorem B1193723 : Blo 311834 1193723 := bstep (se 1 (by rfl) ⟨895292, by rfl⟩ : syracuseStep 1193723 = 1790585) B1790585
theorem B1062719 : Blo 311834 1062719 := bstep (se 1 (by rfl) ⟨797039, by rfl⟩ : syracuseStep 1062719 = 1594079) B1594079
theorem B472895 : Blo 311834 472895 := bstep (se 1 (by rfl) ⟨354671, by rfl⟩ : syracuseStep 472895 = 709343) B709343
theorem B473063 : Blo 311834 473063 := bstep (se 1 (by rfl) ⟨354797, by rfl⟩ : syracuseStep 473063 = 709595) B709595
theorem B473081 : Blo 311834 473081 := bstep (se 2 (by rfl) ⟨177405, by rfl⟩ : syracuseStep 473081 = 354811) B354811
theorem B473183 : Blo 311834 473183 := bstep (se 1 (by rfl) ⟨354887, by rfl⟩ : syracuseStep 473183 = 709775) B709775
theorem B473243 : Blo 311834 473243 := bstep (se 1 (by rfl) ⟨354932, by rfl⟩ : syracuseStep 473243 = 709865) B709865
theorem B473279 : Blo 311834 473279 := bstep (se 1 (by rfl) ⟨354959, by rfl⟩ : syracuseStep 473279 = 709919) B709919
theorem B473321 : Blo 311834 473321 := bstep (se 2 (by rfl) ⟨177495, by rfl⟩ : syracuseStep 473321 = 354991) B354991
theorem B473627 : Blo 311834 473627 := bstep (se 1 (by rfl) ⟨355220, by rfl⟩ : syracuseStep 473627 = 710441) B710441
theorem B670265 : Blo 311834 670265 := bstep (se 2 (by rfl) ⟨251349, by rfl⟩ : syracuseStep 670265 = 502699) B502699
theorem B473705 : Blo 311834 473705 := bstep (se 2 (by rfl) ⟨177639, by rfl⟩ : syracuseStep 473705 = 355279) B355279
theorem B670555 : Blo 311834 670555 := bstep (se 1 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 670555 = 1005833) B1005833
theorem B637787 : Blo 311834 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B703439 : Blo 311834 703439 := bstep (se 1 (by rfl) ⟨527579, by rfl⟩ : syracuseStep 703439 = 1055159) B1055159
theorem B703457 : Blo 311834 703457 := bstep (se 2 (by rfl) ⟨263796, by rfl⟩ : syracuseStep 703457 = 527593) B527593
theorem B703529 : Blo 311834 703529 := bstep (se 2 (by rfl) ⟨263823, by rfl⟩ : syracuseStep 703529 = 527647) B527647
theorem B8043785 : Blo 311834 8043785 := bstep (se 2 (by rfl) ⟨3016419, by rfl⟩ : syracuseStep 8043785 = 6032839) B6032839
theorem B1064231 : Blo 311834 1064231 := bstep (se 1 (by rfl) ⟨798173, by rfl⟩ : syracuseStep 1064231 = 1596347) B1596347
theorem B10894657 : Blo 311834 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B4013387 : Blo 311834 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B1785185 : Blo 311834 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B671375 : Blo 311834 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B1065095 : Blo 311834 1065095 := bstep (se 1 (by rfl) ⟨798821, by rfl⟩ : syracuseStep 1065095 = 1597643) B1597643
theorem B1196471 : Blo 311834 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B803279 : Blo 311834 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B311911 : Blo 311834 311911 := bstep (se 1 (by rfl) ⟨233933, by rfl⟩ : syracuseStep 311911 = 467867) B467867
theorem B1589867 : Blo 311834 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B312175 : Blo 311834 312175 := bstep (se 1 (by rfl) ⟨234131, by rfl⟩ : syracuseStep 312175 = 468263) B468263
theorem B1196957 : Blo 311834 1196957 := bstep (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) B448859
theorem B312231 : Blo 311834 312231 := bstep (se 1 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 312231 = 468347) B468347
theorem B705491 : Blo 311834 705491 := bstep (se 1 (by rfl) ⟨529118, by rfl⟩ : syracuseStep 705491 = 1058237) B1058237
theorem B312315 : Blo 311834 312315 := bstep (se 1 (by rfl) ⟨234236, by rfl⟩ : syracuseStep 312315 = 468473) B468473
theorem B312383 : Blo 311834 312383 := bstep (se 1 (by rfl) ⟨234287, by rfl⟩ : syracuseStep 312383 = 468575) B468575
theorem B312527 : Blo 311834 312527 := bstep (se 1 (by rfl) ⟨234395, by rfl⟩ : syracuseStep 312527 = 468791) B468791
theorem B705743 : Blo 311834 705743 := bstep (se 1 (by rfl) ⟨529307, by rfl⟩ : syracuseStep 705743 = 1058615) B1058615
theorem B312731 : Blo 311834 312731 := bstep (se 1 (by rfl) ⟨234548, by rfl⟩ : syracuseStep 312731 = 469097) B469097
theorem B706067 : Blo 311834 706067 := bstep (se 1 (by rfl) ⟨529550, by rfl⟩ : syracuseStep 706067 = 1059101) B1059101
theorem B1787417 : Blo 311834 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B312943 : Blo 311834 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B673391 : Blo 311834 673391 := bstep (se 1 (by rfl) ⟨505043, by rfl⟩ : syracuseStep 673391 = 1010087) B1010087
theorem B312999 : Blo 311834 312999 := bstep (se 1 (by rfl) ⟨234749, by rfl⟩ : syracuseStep 312999 = 469499) B469499
theorem B313083 : Blo 311834 313083 := bstep (se 1 (by rfl) ⟨234812, by rfl⟩ : syracuseStep 313083 = 469625) B469625
theorem B313119 : Blo 311834 313119 := bstep (se 1 (by rfl) ⟨234839, by rfl⟩ : syracuseStep 313119 = 469679) B469679
theorem B313151 : Blo 311834 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B1132487 : Blo 311834 1132487 := bstep (se 1 (by rfl) ⟨849365, by rfl⟩ : syracuseStep 1132487 = 1698731) B1698731
theorem B313327 : Blo 311834 313327 := bstep (se 1 (by rfl) ⟨234995, by rfl⟩ : syracuseStep 313327 = 469991) B469991
theorem B313499 : Blo 311834 313499 := bstep (se 1 (by rfl) ⟨235124, by rfl⟩ : syracuseStep 313499 = 470249) B470249
theorem B313535 : Blo 311834 313535 := bstep (se 1 (by rfl) ⟨235151, by rfl⟩ : syracuseStep 313535 = 470303) B470303
theorem B706751 : Blo 311834 706751 := bstep (se 1 (by rfl) ⟨530063, by rfl⟩ : syracuseStep 706751 = 1060127) B1060127
theorem B1591487 : Blo 311834 1591487 := bstep (se 1 (by rfl) ⟨1193615, by rfl⟩ : syracuseStep 1591487 = 2387231) B2387231
theorem B674041 : Blo 311834 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B313647 : Blo 311834 313647 := bstep (se 1 (by rfl) ⟨235235, by rfl⟩ : syracuseStep 313647 = 470471) B470471
theorem B313883 : Blo 311834 313883 := bstep (se 1 (by rfl) ⟨235412, by rfl⟩ : syracuseStep 313883 = 470825) B470825
theorem B313887 : Blo 311834 313887 := bstep (se 1 (by rfl) ⟨235415, by rfl⟩ : syracuseStep 313887 = 470831) B470831
theorem B5393141 : Blo 311834 5393141 := bstep (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) B505607
theorem B314203 : Blo 311834 314203 := bstep (se 1 (by rfl) ⟨235652, by rfl⟩ : syracuseStep 314203 = 471305) B471305
theorem B314271 : Blo 311834 314271 := bstep (se 1 (by rfl) ⟨235703, by rfl⟩ : syracuseStep 314271 = 471407) B471407
theorem B314415 : Blo 311834 314415 := bstep (se 1 (by rfl) ⟨235811, by rfl⟩ : syracuseStep 314415 = 471623) B471623
theorem B314439 : Blo 311834 314439 := bstep (se 1 (by rfl) ⟨235829, by rfl⟩ : syracuseStep 314439 = 471659) B471659
theorem B707705 : Blo 311834 707705 := bstep (se 2 (by rfl) ⟨265389, by rfl⟩ : syracuseStep 707705 = 530779) B530779
theorem B1789127 : Blo 311834 1789127 := bstep (se 1 (by rfl) ⟨1341845, by rfl⟩ : syracuseStep 1789127 = 2683691) B2683691
theorem B314591 : Blo 311834 314591 := bstep (se 1 (by rfl) ⟨235943, by rfl⟩ : syracuseStep 314591 = 471887) B471887
theorem B2018533 : Blo 311834 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B2313641 : Blo 311834 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B314855 : Blo 311834 314855 := bstep (se 1 (by rfl) ⟨236141, by rfl⟩ : syracuseStep 314855 = 472283) B472283
theorem B5459471 : Blo 311834 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B314971 : Blo 311834 314971 := bstep (se 1 (by rfl) ⟨236228, by rfl⟩ : syracuseStep 314971 = 472457) B472457
theorem B708371 : Blo 311834 708371 := bstep (se 1 (by rfl) ⟨531278, by rfl⟩ : syracuseStep 708371 = 1062557) B1062557
theorem B315207 : Blo 311834 315207 := bstep (se 1 (by rfl) ⟨236405, by rfl⟩ : syracuseStep 315207 = 472811) B472811
theorem B315359 : Blo 311834 315359 := bstep (se 1 (by rfl) ⟨236519, by rfl⟩ : syracuseStep 315359 = 473039) B473039
theorem B708731 : Blo 311834 708731 := bstep (se 1 (by rfl) ⟨531548, by rfl⟩ : syracuseStep 708731 = 1063097) B1063097
theorem B315623 : Blo 311834 315623 := bstep (se 1 (by rfl) ⟨236717, by rfl⟩ : syracuseStep 315623 = 473435) B473435
theorem B7721249 : Blo 311834 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B315775 : Blo 311834 315775 := bstep (se 1 (by rfl) ⟨236831, by rfl⟩ : syracuseStep 315775 = 473663) B473663
theorem B709001 : Blo 311834 709001 := bstep (se 2 (by rfl) ⟨265875, by rfl⟩ : syracuseStep 709001 = 531751) B531751
theorem B3822329 : Blo 311834 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1594241 : Blo 311834 1594241 := bstep (se 2 (by rfl) ⟨597840, by rfl⟩ : syracuseStep 1594241 = 1195681) B1195681
theorem B709739 : Blo 311834 709739 := bstep (se 1 (by rfl) ⟨532304, by rfl⟩ : syracuseStep 709739 = 1064609) B1064609
theorem B1004987 : Blo 311834 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B6051293 : Blo 311834 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B3233267 : Blo 311834 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1595051 : Blo 311834 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B710315 : Blo 311834 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B3004391 : Blo 311834 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B1595375 : Blo 311834 1595375 := bstep (se 1 (by rfl) ⟨1196531, by rfl⟩ : syracuseStep 1595375 = 2393063) B2393063
theorem B448745 : Blo 311834 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B2709883 : Blo 311834 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B1006013 : Blo 311834 1006013 := bstep (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) B377255
theorem B17160659 : Blo 311834 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B1792475 : Blo 311834 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B5691977 : Blo 311834 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B1071955 : Blo 311834 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B351067 : Blo 311834 351067 := bstep (se 1 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 351067 = 526601) B526601
theorem B4611275 : Blo 311834 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B1596833 : Blo 311834 1596833 := bstep (se 2 (by rfl) ⟨598812, by rfl⟩ : syracuseStep 1596833 = 1197625) B1197625
theorem B352039 : Blo 311834 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B2908493 : Blo 311834 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B2384315 : Blo 311834 2384315 := bstep (se 1 (by rfl) ⟨1788236, by rfl⟩ : syracuseStep 2384315 = 3576473) B3576473
theorem B1336121 : Blo 311834 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B353191 : Blo 311834 353191 := bstep (se 1 (by rfl) ⟨264893, by rfl⟩ : syracuseStep 353191 = 529787) B529787
theorem B15524783 : Blo 311834 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B2254013 : Blo 311834 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B1074707 : Blo 311834 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B11495009 : Blo 311834 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B4057235 : Blo 311834 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B10971449 : Blo 311834 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B354847 : Blo 311834 354847 := bstep (se 1 (by rfl) ⟨266135, by rfl⟩ : syracuseStep 354847 = 532271) B532271
theorem B1797167 : Blo 311834 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B1076345 : Blo 311834 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B1699159 : Blo 311834 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B1011113 : Blo 311834 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B1797623 : Blo 311834 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B3862379 : Blo 311834 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B2256779 : Blo 311834 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B1798625 : Blo 311834 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B3404375 : Blo 311834 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B4551389 : Blo 311834 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B750377 : Blo 311834 750377 := bstep (se 2 (by rfl) ⟨281391, by rfl⟩ : syracuseStep 750377 = 562783) B562783
theorem B750665 : Blo 311834 750665 := bstep (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) B562999
theorem B2159891 : Blo 311834 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B7665299 : Blo 311834 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B2389661 : Blo 311834 2389661 := bstep (se 3 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 2389661 = 896123) B896123
theorem B3570641 : Blo 311834 3570641 := bstep (se 2 (by rfl) ⟨1338990, by rfl⟩ : syracuseStep 3570641 = 2677981) B2677981
theorem B5340653 : Blo 311834 5340653 := bstep (se 3 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 5340653 = 2002745) B2002745
theorem B3014657 : Blo 311834 3014657 := bstep (se 2 (by rfl) ⟨1130496, by rfl⟩ : syracuseStep 3014657 = 2260993) B2260993
theorem B12451843 : Blo 311834 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B754991 : Blo 311834 754991 := bstep (se 1 (by rfl) ⟨566243, by rfl⟩ : syracuseStep 754991 = 1132487) B1132487
theorem B395047 : Blo 311834 395047 := bstep (se 1 (by rfl) ⟨296285, by rfl⟩ : syracuseStep 395047 = 592571) B592571
theorem B10192877 : Blo 311834 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B395599 : Blo 311834 395599 := bstep (se 1 (by rfl) ⟨296699, by rfl⟩ : syracuseStep 395599 = 593399) B593399
theorem B3639647 : Blo 311834 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B2001773 : Blo 311834 2001773 := bstep (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) B750665
theorem B396343 : Blo 311834 396343 := bstep (se 1 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 396343 = 594515) B594515
theorem B789851 : Blo 311834 789851 := bstep (se 1 (by rfl) ⟨592388, by rfl⟩ : syracuseStep 789851 = 1184777) B1184777
theorem B789871 : Blo 311834 789871 := bstep (se 1 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 789871 = 1184807) B1184807
theorem B888185 : Blo 311834 888185 := bstep (se 2 (by rfl) ⟨333069, by rfl⟩ : syracuseStep 888185 = 666139) B666139
theorem B4034195 : Blo 311834 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B2002927 : Blo 311834 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B593983 : Blo 311834 593983 := bstep (se 1 (by rfl) ⟨445487, by rfl⟩ : syracuseStep 593983 = 890975) B890975
theorem B790631 : Blo 311834 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B528491 : Blo 311834 528491 := bstep (se 1 (by rfl) ⟨396368, by rfl⟩ : syracuseStep 528491 = 792737) B792737
theorem B397487 : Blo 311834 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B2691377 : Blo 311834 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B11440439 : Blo 311834 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B2265545 : Blo 311834 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B1184503 : Blo 311834 1184503 := bstep (se 1 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 1184503 = 1776755) B1776755
theorem B758585 : Blo 311834 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B3412813 : Blo 311834 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B595039 : Blo 311834 595039 := bstep (se 1 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 595039 = 892559) B892559
theorem B1184975 : Blo 311834 1184975 := bstep (se 1 (by rfl) ⟨888731, by rfl⟩ : syracuseStep 1184975 = 1777463) B1777463
theorem B529895 : Blo 311834 529895 := bstep (se 1 (by rfl) ⟨397421, by rfl⟩ : syracuseStep 529895 = 794843) B794843
theorem B1938995 : Blo 311834 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B988751 : Blo 311834 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B530057 : Blo 311834 530057 := bstep (se 2 (by rfl) ⟨198771, by rfl⟩ : syracuseStep 530057 = 397543) B397543
theorem B890747 : Blo 311834 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B792443 : Blo 311834 792443 := bstep (se 1 (by rfl) ⟨594332, by rfl⟩ : syracuseStep 792443 = 1188665) B1188665
theorem B530651 : Blo 311834 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B530921 : Blo 311834 530921 := bstep (se 2 (by rfl) ⟨199095, by rfl⟩ : syracuseStep 530921 = 398191) B398191
theorem B7314299 : Blo 311834 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B3022343 : Blo 311834 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B3022571 : Blo 311834 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B1056509 : Blo 311834 1056509 := bstep (se 3 (by rfl) ⟨198095, by rfl⟩ : syracuseStep 1056509 = 396191) B396191
theorem B597871 : Blo 311834 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B2269583 : Blo 311834 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B3613177 : Blo 311834 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B500251 : Blo 311834 500251 := bstep (se 1 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 500251 = 750377) B750377
theorem B3809875 : Blo 311834 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B9118493 : Blo 311834 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B6169709 : Blo 311834 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B468089 : Blo 311834 468089 := bstep (se 2 (by rfl) ⟨175533, by rfl⟩ : syracuseStep 468089 = 351067) B351067
theorem B1057913 : Blo 311834 1057913 := bstep (se 2 (by rfl) ⟨396717, by rfl⟩ : syracuseStep 1057913 = 793435) B793435
theorem B894073 : Blo 311834 894073 := bstep (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) B670555
theorem B795815 : Blo 311834 795815 := bstep (se 1 (by rfl) ⟨596861, by rfl⟩ : syracuseStep 795815 = 1193723) B1193723
theorem B14526209 : Blo 311834 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B468959 : Blo 311834 468959 := bstep (se 1 (by rfl) ⟨351719, by rfl⟩ : syracuseStep 468959 = 703439) B703439
theorem B468971 : Blo 311834 468971 := bstep (se 1 (by rfl) ⟨351728, by rfl⟩ : syracuseStep 468971 = 703457) B703457
theorem B469019 : Blo 311834 469019 := bstep (se 1 (by rfl) ⟨351764, by rfl⟩ : syracuseStep 469019 = 703529) B703529
theorem B1190123 : Blo 311834 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B469385 : Blo 311834 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B1354427 : Blo 311834 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B797647 : Blo 311834 797647 := bstep (se 1 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 797647 = 1196471) B1196471
theorem B535519 : Blo 311834 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B1059911 : Blo 311834 1059911 := bstep (se 1 (by rfl) ⟨794933, by rfl⟩ : syracuseStep 1059911 = 1589867) B1589867
theorem B7777361 : Blo 311834 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B6007931 : Blo 311834 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B797971 : Blo 311834 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B470327 : Blo 311834 470327 := bstep (se 1 (by rfl) ⟨352745, by rfl⟩ : syracuseStep 470327 = 705491) B705491
theorem B20589997 : Blo 311834 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B470495 : Blo 311834 470495 := bstep (se 1 (by rfl) ⟨352871, by rfl⟩ : syracuseStep 470495 = 705743) B705743
theorem B503263 : Blo 311834 503263 := bstep (se 1 (by rfl) ⟨377447, by rfl⟩ : syracuseStep 503263 = 754895) B754895
theorem B470711 : Blo 311834 470711 := bstep (se 1 (by rfl) ⟨353033, by rfl⟩ : syracuseStep 470711 = 706067) B706067
theorem B1191611 : Blo 311834 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B667369 : Blo 311834 667369 := bstep (se 2 (by rfl) ⟨250263, by rfl⟩ : syracuseStep 667369 = 500527) B500527
theorem B470921 : Blo 311834 470921 := bstep (se 2 (by rfl) ⟨176595, by rfl⟩ : syracuseStep 470921 = 353191) B353191
theorem B471167 : Blo 311834 471167 := bstep (se 1 (by rfl) ⟨353375, by rfl⟩ : syracuseStep 471167 = 706751) B706751
theorem B1060991 : Blo 311834 1060991 := bstep (se 1 (by rfl) ⟨795743, by rfl⟩ : syracuseStep 1060991 = 1591487) B1591487
theorem B2666843 : Blo 311834 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B471803 : Blo 311834 471803 := bstep (se 1 (by rfl) ⟨353852, by rfl⟩ : syracuseStep 471803 = 707705) B707705
theorem B1192751 : Blo 311834 1192751 := bstep (se 1 (by rfl) ⟨894563, by rfl⟩ : syracuseStep 1192751 = 1789127) B1789127
theorem B2667593 : Blo 311834 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B1062017 : Blo 311834 1062017 := bstep (se 2 (by rfl) ⟨398256, by rfl⟩ : syracuseStep 1062017 = 796513) B796513
theorem B472247 : Blo 311834 472247 := bstep (se 1 (by rfl) ⟨354185, by rfl⟩ : syracuseStep 472247 = 708371) B708371
theorem B472487 : Blo 311834 472487 := bstep (se 1 (by rfl) ⟨354365, by rfl⟩ : syracuseStep 472487 = 708731) B708731
theorem B472667 : Blo 311834 472667 := bstep (se 1 (by rfl) ⟨354500, by rfl⟩ : syracuseStep 472667 = 709001) B709001
theorem B898721 : Blo 311834 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B702287 : Blo 311834 702287 := bstep (se 1 (by rfl) ⟨526715, by rfl⟩ : syracuseStep 702287 = 1053431) B1053431
theorem B1062827 : Blo 311834 1062827 := bstep (se 1 (by rfl) ⟨797120, by rfl⟩ : syracuseStep 1062827 = 1594241) B1594241
theorem B473129 : Blo 311834 473129 := bstep (se 2 (by rfl) ⟨177423, by rfl⟩ : syracuseStep 473129 = 354847) B354847
theorem B473159 : Blo 311834 473159 := bstep (se 1 (by rfl) ⟨354869, by rfl⟩ : syracuseStep 473159 = 709739) B709739
theorem B702647 : Blo 311834 702647 := bstep (se 1 (by rfl) ⟨526985, by rfl⟩ : syracuseStep 702647 = 1053971) B1053971
theorem B2537839 : Blo 311834 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B1063367 : Blo 311834 1063367 := bstep (se 1 (by rfl) ⟨797525, by rfl⟩ : syracuseStep 1063367 = 1595051) B1595051
theorem B473543 : Blo 311834 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B703007 : Blo 311834 703007 := bstep (se 1 (by rfl) ⟨527255, by rfl⟩ : syracuseStep 703007 = 1054511) B1054511
theorem B1063583 : Blo 311834 1063583 := bstep (se 1 (by rfl) ⟨797687, by rfl⟩ : syracuseStep 1063583 = 1595375) B1595375
theorem B703241 : Blo 311834 703241 := bstep (se 2 (by rfl) ⟨263715, by rfl⟩ : syracuseStep 703241 = 527431) B527431
theorem B670675 : Blo 311834 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B1194983 : Blo 311834 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B2014433 : Blo 311834 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B703817 : Blo 311834 703817 := bstep (se 2 (by rfl) ⟨263931, by rfl⟩ : syracuseStep 703817 = 527863) B527863
theorem B1588733 : Blo 311834 1588733 := bstep (se 3 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 1588733 = 595775) B595775
theorem B1064555 : Blo 311834 1064555 := bstep (se 1 (by rfl) ⟨798416, by rfl⟩ : syracuseStep 1064555 = 1596833) B1596833
theorem B704231 : Blo 311834 704231 := bstep (se 1 (by rfl) ⟨528173, by rfl⟩ : syracuseStep 704231 = 1056347) B1056347
theorem B638695 : Blo 311834 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B1064825 : Blo 311834 1064825 := bstep (se 2 (by rfl) ⟨399309, by rfl⟩ : syracuseStep 1064825 = 798619) B798619
theorem B704699 : Blo 311834 704699 := bstep (se 1 (by rfl) ⟨528524, by rfl⟩ : syracuseStep 704699 = 1057049) B1057049
theorem B704807 : Blo 311834 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B1589543 : Blo 311834 1589543 := bstep (se 1 (by rfl) ⟨1192157, by rfl⟩ : syracuseStep 1589543 = 2384315) B2384315
theorem B311835 : Blo 311834 311835 := bstep (se 1 (by rfl) ⟨233876, by rfl⟩ : syracuseStep 311835 = 467753) B467753
theorem B311839 : Blo 311834 311839 := bstep (se 1 (by rfl) ⟨233879, by rfl⟩ : syracuseStep 311839 = 467759) B467759
theorem B1196653 : Blo 311834 1196653 := bstep (se 3 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 1196653 = 448745) B448745
theorem B311919 : Blo 311834 311919 := bstep (se 1 (by rfl) ⟨233939, by rfl⟩ : syracuseStep 311919 = 467879) B467879
theorem B705185 : Blo 311834 705185 := bstep (se 2 (by rfl) ⟨264444, by rfl⟩ : syracuseStep 705185 = 528889) B528889
theorem B311975 : Blo 311834 311975 := bstep (se 1 (by rfl) ⟨233981, by rfl⟩ : syracuseStep 311975 = 467963) B467963
theorem B312015 : Blo 311834 312015 := bstep (se 1 (by rfl) ⟨234011, by rfl⟩ : syracuseStep 312015 = 468023) B468023
theorem B377563 : Blo 311834 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B312095 : Blo 311834 312095 := bstep (se 1 (by rfl) ⟨234071, by rfl⟩ : syracuseStep 312095 = 468143) B468143
theorem B2999197 : Blo 311834 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B508871 : Blo 311834 508871 := bstep (se 1 (by rfl) ⟨381653, by rfl⟩ : syracuseStep 508871 = 763307) B763307
theorem B705545 : Blo 311834 705545 := bstep (se 2 (by rfl) ⟨264579, by rfl⟩ : syracuseStep 705545 = 529159) B529159
theorem B312367 : Blo 311834 312367 := bstep (se 1 (by rfl) ⟨234275, by rfl⟩ : syracuseStep 312367 = 468551) B468551
theorem B705599 : Blo 311834 705599 := bstep (se 1 (by rfl) ⟨529199, by rfl⟩ : syracuseStep 705599 = 1058399) B1058399
theorem B312431 : Blo 311834 312431 := bstep (se 1 (by rfl) ⟨234323, by rfl⟩ : syracuseStep 312431 = 468647) B468647
theorem B312487 : Blo 311834 312487 := bstep (se 1 (by rfl) ⟨234365, by rfl⟩ : syracuseStep 312487 = 468731) B468731
theorem B312511 : Blo 311834 312511 := bstep (se 1 (by rfl) ⟨234383, by rfl⟩ : syracuseStep 312511 = 468767) B468767
theorem B312543 : Blo 311834 312543 := bstep (se 1 (by rfl) ⟨234407, by rfl⟩ : syracuseStep 312543 = 468815) B468815
theorem B312623 : Blo 311834 312623 := bstep (se 1 (by rfl) ⟨234467, by rfl⟩ : syracuseStep 312623 = 468935) B468935
theorem B2671967 : Blo 311834 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B2704823 : Blo 311834 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B312859 : Blo 311834 312859 := bstep (se 1 (by rfl) ⟨234644, by rfl⟩ : syracuseStep 312859 = 469289) B469289
theorem B312863 : Blo 311834 312863 := bstep (se 1 (by rfl) ⟨234647, by rfl⟩ : syracuseStep 312863 = 469295) B469295
theorem B6047297 : Blo 311834 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B313023 : Blo 311834 313023 := bstep (se 1 (by rfl) ⟨234767, by rfl⟩ : syracuseStep 313023 = 469535) B469535
theorem B313279 : Blo 311834 313279 := bstep (se 1 (by rfl) ⟨234959, by rfl⟩ : syracuseStep 313279 = 469919) B469919
theorem B313311 : Blo 311834 313311 := bstep (se 1 (by rfl) ⟨234983, by rfl⟩ : syracuseStep 313311 = 469967) B469967
theorem B706535 : Blo 311834 706535 := bstep (se 1 (by rfl) ⟨529901, by rfl⟩ : syracuseStep 706535 = 1059803) B1059803
theorem B313371 : Blo 311834 313371 := bstep (se 1 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 313371 = 470057) B470057
theorem B313375 : Blo 311834 313375 := bstep (se 1 (by rfl) ⟨235031, by rfl⟩ : syracuseStep 313375 = 470063) B470063
theorem B1198111 : Blo 311834 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B313391 : Blo 311834 313391 := bstep (se 1 (by rfl) ⟨235043, by rfl⟩ : syracuseStep 313391 = 470087) B470087
theorem B706715 : Blo 311834 706715 := bstep (se 1 (by rfl) ⟨530036, by rfl⟩ : syracuseStep 706715 = 1060073) B1060073
theorem B313567 : Blo 311834 313567 := bstep (se 1 (by rfl) ⟨235175, by rfl⟩ : syracuseStep 313567 = 470351) B470351
theorem B313627 : Blo 311834 313627 := bstep (se 1 (by rfl) ⟨235220, by rfl⟩ : syracuseStep 313627 = 470441) B470441
theorem B674075 : Blo 311834 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B706895 : Blo 311834 706895 := bstep (se 1 (by rfl) ⟨530171, by rfl⟩ : syracuseStep 706895 = 1060343) B1060343
theorem B1198415 : Blo 311834 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B313727 : Blo 311834 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B706985 : Blo 311834 706985 := bstep (se 2 (by rfl) ⟨265119, by rfl⟩ : syracuseStep 706985 = 530239) B530239
theorem B313903 : Blo 311834 313903 := bstep (se 1 (by rfl) ⟨235427, by rfl⟩ : syracuseStep 313903 = 470855) B470855
theorem B2574919 : Blo 311834 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B313959 : Blo 311834 313959 := bstep (se 1 (by rfl) ⟨235469, by rfl⟩ : syracuseStep 313959 = 470939) B470939
theorem B314335 : Blo 311834 314335 := bstep (se 1 (by rfl) ⟨235751, by rfl⟩ : syracuseStep 314335 = 471503) B471503
theorem B1199083 : Blo 311834 1199083 := bstep (se 1 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 1199083 = 1798625) B1798625
theorem B314363 : Blo 311834 314363 := bstep (se 1 (by rfl) ⟨235772, by rfl⟩ : syracuseStep 314363 = 471545) B471545
theorem B707579 : Blo 311834 707579 := bstep (se 1 (by rfl) ⟨530684, by rfl⟩ : syracuseStep 707579 = 1061369) B1061369
theorem B314431 : Blo 311834 314431 := bstep (se 1 (by rfl) ⟨235823, by rfl⟩ : syracuseStep 314431 = 471647) B471647
theorem B3034259 : Blo 311834 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B707759 : Blo 311834 707759 := bstep (se 1 (by rfl) ⟨530819, by rfl⟩ : syracuseStep 707759 = 1061639) B1061639
theorem B707795 : Blo 311834 707795 := bstep (se 1 (by rfl) ⟨530846, by rfl⟩ : syracuseStep 707795 = 1061693) B1061693
theorem B314751 : Blo 311834 314751 := bstep (se 1 (by rfl) ⟨236063, by rfl⟩ : syracuseStep 314751 = 472127) B472127
theorem B314779 : Blo 311834 314779 := bstep (se 1 (by rfl) ⟨236084, by rfl⟩ : syracuseStep 314779 = 472169) B472169
theorem B314847 : Blo 311834 314847 := bstep (se 1 (by rfl) ⟨236135, by rfl⟩ : syracuseStep 314847 = 472271) B472271
theorem B708065 : Blo 311834 708065 := bstep (se 2 (by rfl) ⟨265524, by rfl⟩ : syracuseStep 708065 = 531049) B531049
theorem B314983 : Blo 311834 314983 := bstep (se 1 (by rfl) ⟨236237, by rfl⟩ : syracuseStep 314983 = 472475) B472475
theorem B12045995 : Blo 311834 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B315131 : Blo 311834 315131 := bstep (se 1 (by rfl) ⟨236348, by rfl⟩ : syracuseStep 315131 = 472697) B472697
theorem B1593107 : Blo 311834 1593107 := bstep (se 1 (by rfl) ⟨1194830, by rfl⟩ : syracuseStep 1593107 = 2389661) B2389661
theorem B1429273 : Blo 311834 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B315199 : Blo 311834 315199 := bstep (se 1 (by rfl) ⟨236399, by rfl⟩ : syracuseStep 315199 = 472799) B472799
theorem B708479 : Blo 311834 708479 := bstep (se 1 (by rfl) ⟨531359, by rfl⟩ : syracuseStep 708479 = 1062719) B1062719
theorem B315263 : Blo 311834 315263 := bstep (se 1 (by rfl) ⟨236447, by rfl⟩ : syracuseStep 315263 = 472895) B472895
theorem B315375 : Blo 311834 315375 := bstep (se 1 (by rfl) ⟨236531, by rfl⟩ : syracuseStep 315375 = 473063) B473063
theorem B315387 : Blo 311834 315387 := bstep (se 1 (by rfl) ⟨236540, by rfl⟩ : syracuseStep 315387 = 473081) B473081
theorem B315455 : Blo 311834 315455 := bstep (se 1 (by rfl) ⟨236591, by rfl⟩ : syracuseStep 315455 = 473183) B473183
theorem B315495 : Blo 311834 315495 := bstep (se 1 (by rfl) ⟨236621, by rfl⟩ : syracuseStep 315495 = 473243) B473243
theorem B315519 : Blo 311834 315519 := bstep (se 1 (by rfl) ⟨236639, by rfl⟩ : syracuseStep 315519 = 473279) B473279
theorem B315547 : Blo 311834 315547 := bstep (se 1 (by rfl) ⟨236660, by rfl⟩ : syracuseStep 315547 = 473321) B473321
theorem B315751 : Blo 311834 315751 := bstep (se 1 (by rfl) ⟨236813, by rfl⟩ : syracuseStep 315751 = 473627) B473627
theorem B446843 : Blo 311834 446843 := bstep (se 1 (by rfl) ⟨335132, by rfl⟩ : syracuseStep 446843 = 670265) B670265
theorem B1790333 : Blo 311834 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B315803 : Blo 311834 315803 := bstep (se 1 (by rfl) ⟨236852, by rfl⟩ : syracuseStep 315803 = 473705) B473705
theorem B2380427 : Blo 311834 2380427 := bstep (se 1 (by rfl) ⟨1785320, by rfl⟩ : syracuseStep 2380427 = 3570641) B3570641
theorem B709433 : Blo 311834 709433 := bstep (se 2 (by rfl) ⟨266037, by rfl⟩ : syracuseStep 709433 = 532075) B532075
theorem B5362523 : Blo 311834 5362523 := bstep (se 1 (by rfl) ⟨4021892, by rfl⟩ : syracuseStep 5362523 = 8043785) B8043785
theorem B709487 : Blo 311834 709487 := bstep (se 1 (by rfl) ⟨532115, by rfl⟩ : syracuseStep 709487 = 1064231) B1064231
theorem B2675591 : Blo 311834 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B3560435 : Blo 311834 3560435 := bstep (se 1 (by rfl) ⟨2670326, by rfl⟩ : syracuseStep 3560435 = 5340653) B5340653
theorem B6018077 : Blo 311834 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B709793 : Blo 311834 709793 := bstep (se 2 (by rfl) ⟨266172, by rfl⟩ : syracuseStep 709793 = 532345) B532345
theorem B710063 : Blo 311834 710063 := bstep (se 1 (by rfl) ⟨532547, by rfl⟩ : syracuseStep 710063 = 1065095) B1065095
theorem B4021073 : Blo 311834 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B3595427 : Blo 311834 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B351463 : Blo 311834 351463 := bstep (se 1 (by rfl) ⟨263597, by rfl⟩ : syracuseStep 351463 = 527195) B527195
theorem B1498601 : Blo 311834 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B3563351 : Blo 311834 3563351 := bstep (se 1 (by rfl) ⟨2672513, by rfl⟩ : syracuseStep 3563351 = 5345027) B5345027
theorem B352111 : Blo 311834 352111 := bstep (se 1 (by rfl) ⟨264083, by rfl⟩ : syracuseStep 352111 = 528167) B528167
theorem B352795 : Blo 311834 352795 := bstep (se 1 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 352795 = 529193) B529193
theorem B1335847 : Blo 311834 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B352975 : Blo 311834 352975 := bstep (se 1 (by rfl) ⟨264731, by rfl⟩ : syracuseStep 352975 = 529463) B529463
theorem B1794959 : Blo 311834 1794959 := bstep (se 1 (by rfl) ⟨1346219, by rfl⟩ : syracuseStep 1794959 = 2692439) B2692439
theorem B2155511 : Blo 311834 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B2679965 : Blo 311834 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B1795709 : Blo 311834 1795709 := bstep (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) B673391
theorem B353983 : Blo 311834 353983 := bstep (se 1 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 353983 = 530975) B530975
theorem B3794651 : Blo 311834 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B1140635 : Blo 311834 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B7628701 : Blo 311834 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B354271 : Blo 311834 354271 := bstep (se 1 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 354271 = 531407) B531407
theorem B3074183 : Blo 311834 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B354919 : Blo 311834 354919 := bstep (se 1 (by rfl) ⟨266189, by rfl⟩ : syracuseStep 354919 = 532379) B532379
theorem B8580097 : Blo 311834 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B10349855 : Blo 311834 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B1502675 : Blo 311834 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B716471 : Blo 311834 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B7663339 : Blo 311834 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B750023 : Blo 311834 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B717563 : Blo 311834 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B1340221 : Blo 311834 1340221 := bstep (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) B502583
theorem B751531 : Blo 311834 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B1341623 : Blo 311834 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B1439927 : Blo 311834 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B5110199 : Blo 311834 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B2849231 : Blo 311834 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B425191 : Blo 311834 425191 := bstep (se 1 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 425191 = 637787) B637787
theorem B30768569 : Blo 311834 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B4817569 : Blo 311834 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B5079833 : Blo 311834 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B1803215 : Blo 311834 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B4031531 : Blo 311834 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B3998929 : Blo 311834 3998929 := bstep (se 2 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 3998929 = 2999197) B2999197
theorem B2426431 : Blo 311834 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B526567 : Blo 311834 526567 := bstep (se 1 (by rfl) ⟨394925, by rfl⟩ : syracuseStep 526567 = 789851) B789851
theorem B592123 : Blo 311834 592123 := bstep (se 1 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 592123 = 888185) B888185
theorem B526729 : Blo 311834 526729 := bstep (se 2 (by rfl) ⟨197523, by rfl⟩ : syracuseStep 526729 = 395047) B395047
theorem B2689463 : Blo 311834 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B8030663 : Blo 311834 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B527087 : Blo 311834 527087 := bstep (se 1 (by rfl) ⟨395315, by rfl⟩ : syracuseStep 527087 = 790631) B790631
theorem B1510363 : Blo 311834 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B527465 : Blo 311834 527465 := bstep (se 2 (by rfl) ⟨197799, by rfl⟩ : syracuseStep 527465 = 395599) B395599
theorem B3575015 : Blo 311834 3575015 := bstep (se 1 (by rfl) ⟨2681261, by rfl⟩ : syracuseStep 3575015 = 5362523) B5362523
theorem B789983 : Blo 311834 789983 := bstep (se 1 (by rfl) ⟨592487, by rfl⟩ : syracuseStep 789983 = 1184975) B1184975
theorem B659167 : Blo 311834 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B593831 : Blo 311834 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B528295 : Blo 311834 528295 := bstep (se 1 (by rfl) ⟨396221, by rfl⟩ : syracuseStep 528295 = 792443) B792443
theorem B11440129 : Blo 311834 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B528457 : Blo 311834 528457 := bstep (se 2 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 528457 = 396343) B396343
theorem B1053161 : Blo 311834 1053161 := bstep (se 2 (by rfl) ⟨394935, by rfl⟩ : syracuseStep 1053161 = 789871) B789871
theorem B2396951 : Blo 311834 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B889825 : Blo 311834 889825 := bstep (se 2 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 889825 = 667369) B667369
theorem B1905697 : Blo 311834 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B791977 : Blo 311834 791977 := bstep (se 2 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 791977 = 593983) B593983
theorem B1513055 : Blo 311834 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B530543 : Blo 311834 530543 := bstep (se 1 (by rfl) ⟨397907, by rfl⟩ : syracuseStep 530543 = 795815) B795815
theorem B1579337 : Blo 311834 1579337 := bstep (se 2 (by rfl) ⟨592251, by rfl⟩ : syracuseStep 1579337 = 1184503) B1184503
theorem B2529767 : Blo 311834 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B760423 : Blo 311834 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B793385 : Blo 311834 793385 := bstep (se 2 (by rfl) ⟨297519, by rfl⟩ : syracuseStep 793385 = 595039) B595039
theorem B793415 : Blo 311834 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B4005287 : Blo 311834 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B794407 : Blo 311834 794407 := bstep (se 1 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 794407 = 1191611) B1191611
theorem B1777895 : Blo 311834 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B500015 : Blo 311834 500015 := bstep (se 1 (by rfl) ⟨375011, by rfl⟩ : syracuseStep 500015 = 750023) B750023
theorem B3383785 : Blo 311834 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B795167 : Blo 311834 795167 := bstep (se 1 (by rfl) ⟨596375, by rfl⟩ : syracuseStep 795167 = 1192751) B1192751
theorem B1778395 : Blo 311834 1778395 := bstep (se 1 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 1778395 = 2667593) B2667593
theorem B599147 : Blo 311834 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B468191 : Blo 311834 468191 := bstep (se 1 (by rfl) ⟨351143, by rfl⟩ : syracuseStep 468191 = 702287) B702287
theorem B894233 : Blo 311834 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B468431 : Blo 311834 468431 := bstep (se 1 (by rfl) ⟨351323, by rfl⟩ : syracuseStep 468431 = 702647) B702647
theorem B894415 : Blo 311834 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B959951 : Blo 311834 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B468617 : Blo 311834 468617 := bstep (se 2 (by rfl) ⟨175731, by rfl⟩ : syracuseStep 468617 = 351463) B351463
theorem B566921 : Blo 311834 566921 := bstep (se 2 (by rfl) ⟨212595, by rfl⟩ : syracuseStep 566921 = 425191) B425191
theorem B468671 : Blo 311834 468671 := bstep (se 1 (by rfl) ⟨351503, by rfl⟩ : syracuseStep 468671 = 703007) B703007
theorem B468827 : Blo 311834 468827 := bstep (se 1 (by rfl) ⟨351620, by rfl⟩ : syracuseStep 468827 = 703241) B703241
theorem B796655 : Blo 311834 796655 := bstep (se 1 (by rfl) ⟨597491, by rfl⟩ : syracuseStep 796655 = 1194983) B1194983
theorem B469211 : Blo 311834 469211 := bstep (se 1 (by rfl) ⟨351908, by rfl⟩ : syracuseStep 469211 = 703817) B703817
theorem B1059155 : Blo 311834 1059155 := bstep (se 1 (by rfl) ⟨794366, by rfl⟩ : syracuseStep 1059155 = 1588733) B1588733
theorem B469481 : Blo 311834 469481 := bstep (se 2 (by rfl) ⟨176055, by rfl⟩ : syracuseStep 469481 = 352111) B352111
theorem B797161 : Blo 311834 797161 := bstep (se 2 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 797161 = 597871) B597871
theorem B469487 : Blo 311834 469487 := bstep (se 1 (by rfl) ⟨352115, by rfl⟩ : syracuseStep 469487 = 704231) B704231
theorem B2009771 : Blo 311834 2009771 := bstep (se 1 (by rfl) ⟨1507328, by rfl⟩ : syracuseStep 2009771 = 3014657) B3014657
theorem B469799 : Blo 311834 469799 := bstep (se 1 (by rfl) ⟨352349, by rfl⟩ : syracuseStep 469799 = 704699) B704699
theorem B469871 : Blo 311834 469871 := bstep (se 1 (by rfl) ⟨352403, by rfl⟩ : syracuseStep 469871 = 704807) B704807
theorem B1059695 : Blo 311834 1059695 := bstep (se 1 (by rfl) ⟨794771, by rfl⟩ : syracuseStep 1059695 = 1589543) B1589543
theorem B470123 : Blo 311834 470123 := bstep (se 1 (by rfl) ⟨352592, by rfl⟩ : syracuseStep 470123 = 705185) B705185
theorem B1059965 : Blo 311834 1059965 := bstep (se 3 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 1059965 = 397487) B397487
theorem B339247 : Blo 311834 339247 := bstep (se 1 (by rfl) ⟨254435, by rfl⟩ : syracuseStep 339247 = 508871) B508871
theorem B470363 : Blo 311834 470363 := bstep (se 1 (by rfl) ⟨352772, by rfl⟩ : syracuseStep 470363 = 705545) B705545
theorem B667001 : Blo 311834 667001 := bstep (se 2 (by rfl) ⟨250125, by rfl⟩ : syracuseStep 667001 = 500251) B500251
theorem B470393 : Blo 311834 470393 := bstep (se 2 (by rfl) ⟨176397, by rfl⟩ : syracuseStep 470393 = 352795) B352795
theorem B470399 : Blo 311834 470399 := bstep (se 1 (by rfl) ⟨352799, by rfl⟩ : syracuseStep 470399 = 705599) B705599
theorem B1781129 : Blo 311834 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B503327 : Blo 311834 503327 := bstep (se 1 (by rfl) ⟨377495, by rfl⟩ : syracuseStep 503327 = 754991) B754991
theorem B1781311 : Blo 311834 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B470633 : Blo 311834 470633 := bstep (se 2 (by rfl) ⟨176487, by rfl⟩ : syracuseStep 470633 = 352975) B352975
theorem B503417 : Blo 311834 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B1191581 : Blo 311834 1191581 := bstep (se 3 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 1191581 = 446843) B446843
theorem B471023 : Blo 311834 471023 := bstep (se 1 (by rfl) ⟨353267, by rfl⟩ : syracuseStep 471023 = 706535) B706535
theorem B6795251 : Blo 311834 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B471143 : Blo 311834 471143 := bstep (se 1 (by rfl) ⟨353357, by rfl⟩ : syracuseStep 471143 = 706715) B706715
theorem B1192097 : Blo 311834 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B471263 : Blo 311834 471263 := bstep (se 1 (by rfl) ⟨353447, by rfl⟩ : syracuseStep 471263 = 706895) B706895
theorem B798943 : Blo 311834 798943 := bstep (se 1 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 798943 = 1198415) B1198415
theorem B471323 : Blo 311834 471323 := bstep (se 1 (by rfl) ⟨353492, by rfl⟩ : syracuseStep 471323 = 706985) B706985
theorem B471719 : Blo 311834 471719 := bstep (se 1 (by rfl) ⟨353789, by rfl⟩ : syracuseStep 471719 = 707579) B707579
theorem B471839 : Blo 311834 471839 := bstep (se 1 (by rfl) ⟨353879, by rfl⟩ : syracuseStep 471839 = 707759) B707759
theorem B471863 : Blo 311834 471863 := bstep (se 1 (by rfl) ⟨353897, by rfl⟩ : syracuseStep 471863 = 707795) B707795
theorem B471977 : Blo 311834 471977 := bstep (se 2 (by rfl) ⟨176991, by rfl⟩ : syracuseStep 471977 = 353983) B353983
theorem B472043 : Blo 311834 472043 := bstep (se 1 (by rfl) ⟨354032, by rfl⟩ : syracuseStep 472043 = 708065) B708065
theorem B1062071 : Blo 311834 1062071 := bstep (se 1 (by rfl) ⟨796553, by rfl⟩ : syracuseStep 1062071 = 1593107) B1593107
theorem B10171601 : Blo 311834 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B472319 : Blo 311834 472319 := bstep (se 1 (by rfl) ⟨354239, by rfl⟩ : syracuseStep 472319 = 708479) B708479
theorem B472361 : Blo 311834 472361 := bstep (se 2 (by rfl) ⟨177135, by rfl⟩ : syracuseStep 472361 = 354271) B354271
theorem B5748029 : Blo 311834 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B1193555 : Blo 311834 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B1586951 : Blo 311834 1586951 := bstep (se 1 (by rfl) ⟨1190213, by rfl⟩ : syracuseStep 1586951 = 2380427) B2380427
theorem B472955 : Blo 311834 472955 := bstep (se 1 (by rfl) ⟨354716, by rfl⟩ : syracuseStep 472955 = 709433) B709433
theorem B472991 : Blo 311834 472991 := bstep (se 1 (by rfl) ⟨354743, by rfl⟩ : syracuseStep 472991 = 709487) B709487
theorem B1783727 : Blo 311834 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B2373623 : Blo 311834 2373623 := bstep (se 1 (by rfl) ⟨1780217, by rfl⟩ : syracuseStep 2373623 = 3560435) B3560435
theorem B4012051 : Blo 311834 4012051 := bstep (se 1 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 4012051 = 6018077) B6018077
theorem B473195 : Blo 311834 473195 := bstep (se 1 (by rfl) ⟨354896, by rfl⟩ : syracuseStep 473195 = 709793) B709793
theorem B473225 : Blo 311834 473225 := bstep (se 2 (by rfl) ⟨177459, by rfl⟩ : syracuseStep 473225 = 354919) B354919
theorem B473375 : Blo 311834 473375 := bstep (se 1 (by rfl) ⟨355031, by rfl⟩ : syracuseStep 473375 = 710063) B710063
theorem B1292663 : Blo 311834 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B1063529 : Blo 311834 1063529 := bstep (se 2 (by rfl) ⟨398823, by rfl⟩ : syracuseStep 1063529 = 797647) B797647
theorem B1063961 : Blo 311834 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B671017 : Blo 311834 671017 := bstep (se 2 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 671017 = 503263) B503263
theorem B999067 : Blo 311834 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B2014895 : Blo 311834 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B2015047 : Blo 311834 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B704339 : Blo 311834 704339 := bstep (se 1 (by rfl) ⟨528254, by rfl⟩ : syracuseStep 704339 = 1056509) B1056509
theorem B2375567 : Blo 311834 2375567 := bstep (se 1 (by rfl) ⟨1781675, by rfl⟩ : syracuseStep 2375567 = 3563351) B3563351
theorem B2670569 : Blo 311834 2670569 := bstep (se 2 (by rfl) ⟨1001463, by rfl⟩ : syracuseStep 2670569 = 2002927) B2002927
theorem B6078995 : Blo 311834 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B1196639 : Blo 311834 1196639 := bstep (se 1 (by rfl) ⟨897479, by rfl⟩ : syracuseStep 1196639 = 1794959) B1794959
theorem B4113139 : Blo 311834 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B312059 : Blo 311834 312059 := bstep (se 1 (by rfl) ⟨234044, by rfl⟩ : syracuseStep 312059 = 468089) B468089
theorem B705275 : Blo 311834 705275 := bstep (se 1 (by rfl) ⟨528956, by rfl⟩ : syracuseStep 705275 = 1057913) B1057913
theorem B1786643 : Blo 311834 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B1786961 : Blo 311834 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B1197139 : Blo 311834 1197139 := bstep (se 1 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 1197139 = 1795709) B1795709
theorem B9684139 : Blo 311834 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B312639 : Blo 311834 312639 := bstep (se 1 (by rfl) ⟨234479, by rfl⟩ : syracuseStep 312639 = 468959) B468959
theorem B312647 : Blo 311834 312647 := bstep (se 1 (by rfl) ⟨234485, by rfl⟩ : syracuseStep 312647 = 468971) B468971
theorem B312679 : Blo 311834 312679 := bstep (se 1 (by rfl) ⟨234509, by rfl⟩ : syracuseStep 312679 = 469019) B469019
theorem B2049455 : Blo 311834 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B312923 : Blo 311834 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B902951 : Blo 311834 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B706607 : Blo 311834 706607 := bstep (se 1 (by rfl) ⟨529955, by rfl⟩ : syracuseStep 706607 = 1059911) B1059911
theorem B6899903 : Blo 311834 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B313551 : Blo 311834 313551 := bstep (se 1 (by rfl) ⟨235163, by rfl⟩ : syracuseStep 313551 = 470327) B470327
theorem B1001783 : Blo 311834 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B313663 : Blo 311834 313663 := bstep (se 1 (by rfl) ⟨235247, by rfl⟩ : syracuseStep 313663 = 470495) B470495
theorem B313807 : Blo 311834 313807 := bstep (se 1 (by rfl) ⟨235355, by rfl⟩ : syracuseStep 313807 = 470711) B470711
theorem B477647 : Blo 311834 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B1002041 : Blo 311834 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B313947 : Blo 311834 313947 := bstep (se 1 (by rfl) ⟨235460, by rfl⟩ : syracuseStep 313947 = 470921) B470921
theorem B314111 : Blo 311834 314111 := bstep (se 1 (by rfl) ⟨235583, by rfl⟩ : syracuseStep 314111 = 471167) B471167
theorem B707327 : Blo 311834 707327 := bstep (se 1 (by rfl) ⟨530495, by rfl⟩ : syracuseStep 707327 = 1060991) B1060991
theorem B314535 : Blo 311834 314535 := bstep (se 1 (by rfl) ⟨235901, by rfl⟩ : syracuseStep 314535 = 471803) B471803
theorem B478375 : Blo 311834 478375 := bstep (se 1 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 478375 = 717563) B717563
theorem B708011 : Blo 311834 708011 := bstep (se 1 (by rfl) ⟨531008, by rfl⟩ : syracuseStep 708011 = 1062017) B1062017
theorem B314831 : Blo 311834 314831 := bstep (se 1 (by rfl) ⟨236123, by rfl⟩ : syracuseStep 314831 = 472247) B472247
theorem B314991 : Blo 311834 314991 := bstep (se 1 (by rfl) ⟨236243, by rfl⟩ : syracuseStep 314991 = 472487) B472487
theorem B315111 : Blo 311834 315111 := bstep (se 1 (by rfl) ⟨236333, by rfl⟩ : syracuseStep 315111 = 472667) B472667
theorem B708551 : Blo 311834 708551 := bstep (se 1 (by rfl) ⟨531413, by rfl⟩ : syracuseStep 708551 = 1062827) B1062827
theorem B315419 : Blo 311834 315419 := bstep (se 1 (by rfl) ⟨236564, by rfl⟩ : syracuseStep 315419 = 473129) B473129
theorem B315439 : Blo 311834 315439 := bstep (se 1 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 315439 = 473159) B473159
theorem B708911 : Blo 311834 708911 := bstep (se 1 (by rfl) ⟨531683, by rfl⟩ : syracuseStep 708911 = 1063367) B1063367
theorem B315695 : Blo 311834 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B709055 : Blo 311834 709055 := bstep (se 1 (by rfl) ⟨531791, by rfl⟩ : syracuseStep 709055 = 1063583) B1063583
theorem B709703 : Blo 311834 709703 := bstep (se 1 (by rfl) ⟨532277, by rfl⟩ : syracuseStep 709703 = 1064555) B1064555
theorem B709883 : Blo 311834 709883 := bstep (se 1 (by rfl) ⟨532412, by rfl⟩ : syracuseStep 709883 = 1064825) B1064825
theorem B16602457 : Blo 311834 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B1595537 : Blo 311834 1595537 := bstep (se 2 (by rfl) ⟨598326, by rfl⟩ : syracuseStep 1595537 = 1196653) B1196653
theorem B449383 : Blo 311834 449383 := bstep (se 1 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 449383 = 674075) B674075
theorem B1334515 : Blo 311834 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B2022839 : Blo 311834 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B2022893 : Blo 311834 2022893 := bstep (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) B758585
theorem B1597481 : Blo 311834 1597481 := bstep (se 2 (by rfl) ⟨599055, by rfl⟩ : syracuseStep 1597481 = 1198111) B1198111
theorem B352327 : Blo 311834 352327 := bstep (se 1 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 352327 = 528491) B528491
theorem B1794251 : Blo 311834 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B7626959 : Blo 311834 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B3433225 : Blo 311834 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B353263 : Blo 311834 353263 := bstep (se 1 (by rfl) ⟨264947, by rfl⟩ : syracuseStep 353263 = 529895) B529895
theorem B353371 : Blo 311834 353371 := bstep (se 1 (by rfl) ⟨265028, by rfl⟩ : syracuseStep 353371 = 530057) B530057
theorem B714025 : Blo 311834 714025 := bstep (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) B535519
theorem B1598777 : Blo 311834 1598777 := bstep (se 2 (by rfl) ⟨599541, by rfl⟩ : syracuseStep 1598777 = 1199083) B1199083
theorem B353767 : Blo 311834 353767 := bstep (se 1 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 353767 = 530651) B530651
theorem B353947 : Blo 311834 353947 := bstep (se 1 (by rfl) ⟨265460, by rfl⟩ : syracuseStep 353947 = 530921) B530921
theorem B2680715 : Blo 311834 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B27453329 : Blo 311834 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B4876199 : Blo 311834 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B10217785 : Blo 311834 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B4550417 : Blo 311834 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B20739629 : Blo 311834 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B3406799 : Blo 311834 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B1899487 : Blo 311834 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B1342955 : Blo 311834 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B20512379 : Blo 311834 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B851593 : Blo 311834 851593 := bstep (se 2 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 851593 = 638695) B638695
theorem B2687687 : Blo 311834 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B6423425 : Blo 311834 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B12912185 : Blo 311834 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B952033 : Blo 311834 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B526655 : Blo 311834 526655 := bstep (se 1 (by rfl) ⟨394991, by rfl⟩ : syracuseStep 526655 = 789983) B789983
theorem B789497 : Blo 311834 789497 := bstep (se 2 (by rfl) ⟨296061, by rfl⟩ : syracuseStep 789497 = 592123) B592123
theorem B2559869 : Blo 311834 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B1052891 : Blo 311834 1052891 := bstep (se 1 (by rfl) ⟨789668, by rfl⟩ : syracuseStep 1052891 = 1579337) B1579337
theorem B528923 : Blo 311834 528923 := bstep (se 1 (by rfl) ⟨396692, by rfl⟩ : syracuseStep 528923 = 793385) B793385
theorem B528943 : Blo 311834 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B1348559 : Blo 311834 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1348595 : Blo 311834 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B5084639 : Blo 311834 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B1185263 : Blo 311834 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B333343 : Blo 311834 333343 := bstep (se 1 (by rfl) ⟨250007, by rfl⟩ : syracuseStep 333343 = 500015) B500015
theorem B530111 : Blo 311834 530111 := bstep (se 1 (by rfl) ⟨397583, by rfl⟩ : syracuseStep 530111 = 795167) B795167
theorem B399431 : Blo 311834 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B596155 : Blo 311834 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B3447101 : Blo 311834 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B3250799 : Blo 311834 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B1186433 : Blo 311834 1186433 := bstep (se 2 (by rfl) ⟨444912, by rfl⟩ : syracuseStep 1186433 = 889825) B889825
theorem B531103 : Blo 311834 531103 := bstep (se 1 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 531103 = 796655) B796655
theorem B1809317 : Blo 311834 1809317 := bstep (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) B339247
theorem B1055969 : Blo 311834 1055969 := bstep (se 2 (by rfl) ⟨395988, by rfl⟩ : syracuseStep 1055969 = 791977) B791977
theorem B1187419 : Blo 311834 1187419 := bstep (se 1 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 1187419 = 1781129) B1781129
theorem B335551 : Blo 311834 335551 := bstep (se 1 (by rfl) ⟨251663, by rfl⟩ : syracuseStep 335551 = 503327) B503327
theorem B335611 : Blo 311834 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B794387 : Blo 311834 794387 := bstep (se 1 (by rfl) ⟨595790, by rfl⟩ : syracuseStep 794387 = 1191581) B1191581
theorem B4530167 : Blo 311834 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B5349401 : Blo 311834 5349401 := bstep (se 2 (by rfl) ⟨2006025, by rfl⟩ : syracuseStep 5349401 = 4012051) B4012051
theorem B794731 : Blo 311834 794731 := bstep (se 1 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 794731 = 1192097) B1192097
theorem B1778669 : Blo 311834 1778669 := bstep (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) B667001
theorem B795703 : Blo 311834 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B599177 : Blo 311834 599177 := bstep (se 2 (by rfl) ⟨224691, by rfl⟩ : syracuseStep 599177 = 449383) B449383
theorem B3515557 : Blo 311834 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B1057967 : Blo 311834 1057967 := bstep (se 1 (by rfl) ⟨793475, by rfl⟩ : syracuseStep 1057967 = 1586951) B1586951
theorem B1189151 : Blo 311834 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B2532649 : Blo 311834 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1582415 : Blo 311834 1582415 := bstep (se 1 (by rfl) ⟨1186811, by rfl⟩ : syracuseStep 1582415 = 2373623) B2373623
theorem B1779353 : Blo 311834 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B894689 : Blo 311834 894689 := bstep (se 2 (by rfl) ⟨335508, by rfl⟩ : syracuseStep 894689 = 671017) B671017
theorem B2271199 : Blo 311834 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B895303 : Blo 311834 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B1059209 : Blo 311834 1059209 := bstep (se 2 (by rfl) ⟨397203, by rfl⟩ : syracuseStep 1059209 = 794407) B794407
theorem B13674919 : Blo 311834 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B1583549 : Blo 311834 1583549 := bstep (se 3 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 1583549 = 593831) B593831
theorem B469559 : Blo 311834 469559 := bstep (se 1 (by rfl) ⟨352169, by rfl⟩ : syracuseStep 469559 = 704339) B704339
theorem B1583711 : Blo 311834 1583711 := bstep (se 1 (by rfl) ⟨1187783, by rfl⟩ : syracuseStep 1583711 = 2375567) B2375567
theorem B1780379 : Blo 311834 1780379 := bstep (se 1 (by rfl) ⟨1335284, by rfl⟩ : syracuseStep 1780379 = 2670569) B2670569
theorem B469769 : Blo 311834 469769 := bstep (se 2 (by rfl) ⟨176163, by rfl⟩ : syracuseStep 469769 = 352327) B352327
theorem B797759 : Blo 311834 797759 := bstep (se 1 (by rfl) ⟨598319, by rfl⟩ : syracuseStep 797759 = 1196639) B1196639
theorem B470183 : Blo 311834 470183 := bstep (se 1 (by rfl) ⟨352637, by rfl⟩ : syracuseStep 470183 = 705275) B705275
theorem B1191095 : Blo 311834 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B3386555 : Blo 311834 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B1191307 : Blo 311834 1191307 := bstep (se 1 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 1191307 = 1786961) B1786961
theorem B2371193 : Blo 311834 2371193 := bstep (se 2 (by rfl) ⟨889197, by rfl⟩ : syracuseStep 2371193 = 1778395) B1778395
theorem B5484185 : Blo 311834 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B601967 : Blo 311834 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B471017 : Blo 311834 471017 := bstep (se 2 (by rfl) ⟨176631, by rfl⟩ : syracuseStep 471017 = 353263) B353263
theorem B471071 : Blo 311834 471071 := bstep (se 1 (by rfl) ⟨353303, by rfl⟩ : syracuseStep 471071 = 706607) B706607
theorem B471161 : Blo 311834 471161 := bstep (se 2 (by rfl) ⟨176685, by rfl⟩ : syracuseStep 471161 = 353371) B353371
theorem B4599935 : Blo 311834 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B667855 : Blo 311834 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B5353775 : Blo 311834 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B668027 : Blo 311834 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B471551 : Blo 311834 471551 := bstep (se 1 (by rfl) ⟨353663, by rfl⟩ : syracuseStep 471551 = 707327) B707327
theorem B1192553 : Blo 311834 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B471689 : Blo 311834 471689 := bstep (se 2 (by rfl) ⟨176883, by rfl⟩ : syracuseStep 471689 = 353767) B353767
theorem B471929 : Blo 311834 471929 := bstep (se 2 (by rfl) ⟨176973, by rfl⟩ : syracuseStep 471929 = 353947) B353947
theorem B472007 : Blo 311834 472007 := bstep (se 1 (by rfl) ⟨354005, by rfl⟩ : syracuseStep 472007 = 708011) B708011
theorem B472367 : Blo 311834 472367 := bstep (se 1 (by rfl) ⟨354275, by rfl⟩ : syracuseStep 472367 = 708551) B708551
theorem B472607 : Blo 311834 472607 := bstep (se 1 (by rfl) ⟨354455, by rfl⟩ : syracuseStep 472607 = 708911) B708911
theorem B472703 : Blo 311834 472703 := bstep (se 1 (by rfl) ⟨354527, by rfl⟩ : syracuseStep 472703 = 709055) B709055
theorem B702089 : Blo 311834 702089 := bstep (se 2 (by rfl) ⟨263283, by rfl⟩ : syracuseStep 702089 = 526567) B526567
theorem B702107 : Blo 311834 702107 := bstep (se 1 (by rfl) ⟨526580, by rfl⟩ : syracuseStep 702107 = 1053161) B1053161
theorem B702305 : Blo 311834 702305 := bstep (se 2 (by rfl) ⟨263364, by rfl⟩ : syracuseStep 702305 = 526729) B526729
theorem B1062881 : Blo 311834 1062881 := bstep (se 2 (by rfl) ⟨398580, by rfl⟩ : syracuseStep 1062881 = 797161) B797161
theorem B473135 : Blo 311834 473135 := bstep (se 1 (by rfl) ⟨354851, by rfl⟩ : syracuseStep 473135 = 709703) B709703
theorem B473255 : Blo 311834 473255 := bstep (se 1 (by rfl) ⟨354941, by rfl⟩ : syracuseStep 473255 = 709883) B709883
theorem B2013817 : Blo 311834 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B1063691 : Blo 311834 1063691 := bstep (se 1 (by rfl) ⟨797768, by rfl⟩ : syracuseStep 1063691 = 1595537) B1595537
theorem B1686511 : Blo 311834 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B2375081 : Blo 311834 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B2670191 : Blo 311834 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B704393 : Blo 311834 704393 := bstep (se 2 (by rfl) ⟨264147, by rfl⟩ : syracuseStep 704393 = 528295) B528295
theorem B15253505 : Blo 311834 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B1064987 : Blo 311834 1064987 := bstep (se 1 (by rfl) ⟨798740, by rfl⟩ : syracuseStep 1064987 = 1597481) B1597481
theorem B704609 : Blo 311834 704609 := bstep (se 2 (by rfl) ⟨264228, by rfl⟩ : syracuseStep 704609 = 528457) B528457
theorem B1196167 : Blo 311834 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B1065257 : Blo 311834 1065257 := bstep (se 2 (by rfl) ⟨399471, by rfl⟩ : syracuseStep 1065257 = 798943) B798943
theorem B312127 : Blo 311834 312127 := bstep (se 1 (by rfl) ⟨234095, by rfl⟩ : syracuseStep 312127 = 468191) B468191
theorem B1065851 : Blo 311834 1065851 := bstep (se 1 (by rfl) ⟨799388, by rfl⟩ : syracuseStep 1065851 = 1598777) B1598777
theorem B312287 : Blo 311834 312287 := bstep (se 1 (by rfl) ⟨234215, by rfl⟩ : syracuseStep 312287 = 468431) B468431
theorem B312411 : Blo 311834 312411 := bstep (se 1 (by rfl) ⟨234308, by rfl⟩ : syracuseStep 312411 = 468617) B468617
theorem B377947 : Blo 311834 377947 := bstep (se 1 (by rfl) ⟨283460, by rfl⟩ : syracuseStep 377947 = 566921) B566921
theorem B312447 : Blo 311834 312447 := bstep (se 1 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 312447 = 468671) B468671
theorem B312551 : Blo 311834 312551 := bstep (se 1 (by rfl) ⟨234413, by rfl⟩ : syracuseStep 312551 = 468827) B468827
theorem B1787143 : Blo 311834 1787143 := bstep (se 1 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 1787143 = 2680715) B2680715
theorem B18302219 : Blo 311834 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B2540929 : Blo 311834 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B312807 : Blo 311834 312807 := bstep (se 1 (by rfl) ⟨234605, by rfl⟩ : syracuseStep 312807 = 469211) B469211
theorem B706103 : Blo 311834 706103 := bstep (se 1 (by rfl) ⟨529577, by rfl⟩ : syracuseStep 706103 = 1059155) B1059155
theorem B312987 : Blo 311834 312987 := bstep (se 1 (by rfl) ⟨234740, by rfl⟩ : syracuseStep 312987 = 469481) B469481
theorem B312991 : Blo 311834 312991 := bstep (se 1 (by rfl) ⟨234743, by rfl⟩ : syracuseStep 312991 = 469487) B469487
theorem B22136609 : Blo 311834 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B313199 : Blo 311834 313199 := bstep (se 1 (by rfl) ⟨234899, by rfl⟩ : syracuseStep 313199 = 469799) B469799
theorem B313247 : Blo 311834 313247 := bstep (se 1 (by rfl) ⟨234935, by rfl⟩ : syracuseStep 313247 = 469871) B469871
theorem B706463 : Blo 311834 706463 := bstep (se 1 (by rfl) ⟨529847, by rfl⟩ : syracuseStep 706463 = 1059695) B1059695
theorem B313415 : Blo 311834 313415 := bstep (se 1 (by rfl) ⟨235061, by rfl⟩ : syracuseStep 313415 = 470123) B470123
theorem B706643 : Blo 311834 706643 := bstep (se 1 (by rfl) ⟨529982, by rfl⟩ : syracuseStep 706643 = 1059965) B1059965
theorem B313575 : Blo 311834 313575 := bstep (se 1 (by rfl) ⟨235181, by rfl⟩ : syracuseStep 313575 = 470363) B470363
theorem B313595 : Blo 311834 313595 := bstep (se 1 (by rfl) ⟨235196, by rfl⟩ : syracuseStep 313595 = 470393) B470393
theorem B313599 : Blo 311834 313599 := bstep (se 1 (by rfl) ⟨235199, by rfl⟩ : syracuseStep 313599 = 470399) B470399
theorem B313755 : Blo 311834 313755 := bstep (se 1 (by rfl) ⟨235316, by rfl⟩ : syracuseStep 313755 = 470633) B470633
theorem B3033611 : Blo 311834 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B314015 : Blo 311834 314015 := bstep (se 1 (by rfl) ⟨235511, by rfl⟩ : syracuseStep 314015 = 471023) B471023
theorem B314095 : Blo 311834 314095 := bstep (se 1 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 314095 = 471143) B471143
theorem B314175 : Blo 311834 314175 := bstep (se 1 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 314175 = 471263) B471263
theorem B314215 : Blo 311834 314215 := bstep (se 1 (by rfl) ⟨235661, by rfl⟩ : syracuseStep 314215 = 471323) B471323
theorem B314479 : Blo 311834 314479 := bstep (se 1 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 314479 = 471719) B471719
theorem B314559 : Blo 311834 314559 := bstep (se 1 (by rfl) ⟨235919, by rfl⟩ : syracuseStep 314559 = 471839) B471839
theorem B314575 : Blo 311834 314575 := bstep (se 1 (by rfl) ⟨235931, by rfl⟩ : syracuseStep 314575 = 471863) B471863
theorem B314651 : Blo 311834 314651 := bstep (se 1 (by rfl) ⟨235988, by rfl⟩ : syracuseStep 314651 = 471977) B471977
theorem B314695 : Blo 311834 314695 := bstep (se 1 (by rfl) ⟨236021, by rfl⟩ : syracuseStep 314695 = 472043) B472043
theorem B708047 : Blo 311834 708047 := bstep (se 1 (by rfl) ⟨531035, by rfl⟩ : syracuseStep 708047 = 1062071) B1062071
theorem B314879 : Blo 311834 314879 := bstep (se 1 (by rfl) ⟨236159, by rfl⟩ : syracuseStep 314879 = 472319) B472319
theorem B314907 : Blo 311834 314907 := bstep (se 1 (by rfl) ⟨236180, by rfl⟩ : syracuseStep 314907 = 472361) B472361
theorem B315303 : Blo 311834 315303 := bstep (se 1 (by rfl) ⟨236477, by rfl⟩ : syracuseStep 315303 = 472955) B472955
theorem B315327 : Blo 311834 315327 := bstep (se 1 (by rfl) ⟨236495, by rfl⟩ : syracuseStep 315327 = 472991) B472991
theorem B315463 : Blo 311834 315463 := bstep (se 1 (by rfl) ⟨236597, by rfl⟩ : syracuseStep 315463 = 473195) B473195
theorem B315483 : Blo 311834 315483 := bstep (se 1 (by rfl) ⟨236612, by rfl⟩ : syracuseStep 315483 = 473225) B473225
theorem B315583 : Blo 311834 315583 := bstep (se 1 (by rfl) ⟨236687, by rfl⟩ : syracuseStep 315583 = 473375) B473375
theorem B709019 : Blo 311834 709019 := bstep (se 1 (by rfl) ⟨531764, by rfl⟩ : syracuseStep 709019 = 1063529) B1063529
theorem B709307 : Blo 311834 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B1135457 : Blo 311834 1135457 := bstep (se 2 (by rfl) ⟨425796, by rfl⟩ : syracuseStep 1135457 = 851593) B851593
theorem B1332089 : Blo 311834 1332089 := bstep (se 2 (by rfl) ⟨499533, by rfl⟩ : syracuseStep 1332089 = 999067) B999067
theorem B4052663 : Blo 311834 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B4511713 : Blo 311834 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B1366303 : Blo 311834 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B4577633 : Blo 311834 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B1596185 : Blo 311834 1596185 := bstep (se 2 (by rfl) ⟨598569, by rfl⟩ : syracuseStep 1596185 = 1197139) B1197139
theorem B5331905 : Blo 311834 5331905 := bstep (se 2 (by rfl) ⟨1999464, by rfl⟩ : syracuseStep 5331905 = 3998929) B3998929
theorem B1792975 : Blo 311834 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B318431 : Blo 311834 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B351391 : Blo 311834 351391 := bstep (se 1 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 351391 = 527087) B527087
theorem B351643 : Blo 311834 351643 := bstep (se 1 (by rfl) ⟨263732, by rfl⟩ : syracuseStep 351643 = 527465) B527465
theorem B3235241 : Blo 311834 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B2383343 : Blo 311834 2383343 := bstep (se 1 (by rfl) ⟨1787507, by rfl⟩ : syracuseStep 2383343 = 3575015) B3575015
theorem B4808573 : Blo 311834 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B13623713 : Blo 311834 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B1597967 : Blo 311834 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B1008703 : Blo 311834 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B353695 : Blo 311834 353695 := bstep (se 1 (by rfl) ⟨265271, by rfl⟩ : syracuseStep 353695 = 530543) B530543
theorem B2551333 : Blo 311834 2551333 := bstep (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) B478375
theorem B1339847 : Blo 311834 1339847 := bstep (se 1 (by rfl) ⟨1004885, by rfl⟩ : syracuseStep 1339847 = 2009771) B2009771
theorem B1013897 : Blo 311834 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B6781067 : Blo 311834 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B3832019 : Blo 311834 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B13826419 : Blo 311834 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B2686729 : Blo 311834 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B1343263 : Blo 311834 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B1344937 : Blo 311834 1344937 := bstep (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) B1008703
theorem B4687409 : Blo 311834 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B3376865 : Blo 311834 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B526331 : Blo 311834 526331 := bstep (se 1 (by rfl) ⟨394748, by rfl⟩ : syracuseStep 526331 = 789497) B789497
theorem B1706579 : Blo 311834 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B756971 : Blo 311834 756971 := bstep (se 1 (by rfl) ⟨567728, by rfl⟩ : syracuseStep 756971 = 1135457) B1135457
theorem B888059 : Blo 311834 888059 := bstep (se 1 (by rfl) ⟨666044, by rfl⟩ : syracuseStep 888059 = 1332089) B1332089
theorem B790175 : Blo 311834 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B3051755 : Blo 311834 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B2167199 : Blo 311834 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B790955 : Blo 311834 790955 := bstep (se 1 (by rfl) ⟨593216, by rfl⟩ : syracuseStep 790955 = 1186433) B1186433
theorem B529591 : Blo 311834 529591 := bstep (se 1 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 529591 = 794387) B794387
theorem B3020111 : Blo 311834 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B9082475 : Blo 311834 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B1185779 : Blo 311834 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B792767 : Blo 311834 792767 := bstep (se 1 (by rfl) ⟨594575, by rfl⟩ : syracuseStep 792767 = 1189151) B1189151
theorem B1054943 : Blo 311834 1054943 := bstep (se 1 (by rfl) ⟨791207, by rfl⟩ : syracuseStep 1054943 = 1582415) B1582415
theorem B1186235 : Blo 311834 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B596459 : Blo 311834 596459 := bstep (se 1 (by rfl) ⟨447344, by rfl⟩ : syracuseStep 596459 = 894689) B894689
theorem B1055699 : Blo 311834 1055699 := bstep (se 1 (by rfl) ⟨791774, by rfl⟩ : syracuseStep 1055699 = 1583549) B1583549
theorem B1055807 : Blo 311834 1055807 := bstep (se 1 (by rfl) ⟨791855, by rfl⟩ : syracuseStep 1055807 = 1583711) B1583711
theorem B1186919 : Blo 311834 1186919 := bstep (se 1 (by rfl) ⟨890189, by rfl⟩ : syracuseStep 1186919 = 1780379) B1780379
theorem B531839 : Blo 311834 531839 := bstep (se 1 (by rfl) ⟨398879, by rfl⟩ : syracuseStep 531839 = 797759) B797759
theorem B794063 : Blo 311834 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B1580795 : Blo 311834 1580795 := bstep (se 1 (by rfl) ⟨1185596, by rfl⟩ : syracuseStep 1580795 = 2371193) B2371193
theorem B401311 : Blo 311834 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B794873 : Blo 311834 794873 := bstep (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) B596155
theorem B893231 : Blo 311834 893231 := bstep (se 1 (by rfl) ⟨669923, by rfl⟩ : syracuseStep 893231 = 1339847) B1339847
theorem B795035 : Blo 311834 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B468059 : Blo 311834 468059 := bstep (se 1 (by rfl) ⟨351044, by rfl⟩ : syracuseStep 468059 = 702089) B702089
theorem B468071 : Blo 311834 468071 := bstep (se 1 (by rfl) ⟨351053, by rfl⟩ : syracuseStep 468071 = 702107) B702107
theorem B468203 : Blo 311834 468203 := bstep (se 1 (by rfl) ⟨351152, by rfl⟩ : syracuseStep 468203 = 702305) B702305
theorem B468521 : Blo 311834 468521 := bstep (se 2 (by rfl) ⟨175695, by rfl⟩ : syracuseStep 468521 = 351391) B351391
theorem B468857 : Blo 311834 468857 := bstep (se 2 (by rfl) ⟨175821, by rfl⟩ : syracuseStep 468857 = 351643) B351643
theorem B1583225 : Blo 311834 1583225 := bstep (se 2 (by rfl) ⟨593709, by rfl⟩ : syracuseStep 1583225 = 1187419) B1187419
theorem B1583387 : Blo 311834 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B3582305 : Blo 311834 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B1780127 : Blo 311834 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B469595 : Blo 311834 469595 := bstep (se 1 (by rfl) ⟨352196, by rfl⟩ : syracuseStep 469595 = 704393) B704393
theorem B10169003 : Blo 311834 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B469739 : Blo 311834 469739 := bstep (se 1 (by rfl) ⟨352304, by rfl⟩ : syracuseStep 469739 = 704609) B704609
theorem B1059641 : Blo 311834 1059641 := bstep (se 2 (by rfl) ⟨397365, by rfl⟩ : syracuseStep 1059641 = 794731) B794731
theorem B12201479 : Blo 311834 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B470735 : Blo 311834 470735 := bstep (se 1 (by rfl) ⟨353051, by rfl⟩ : syracuseStep 470735 = 706103) B706103
theorem B470975 : Blo 311834 470975 := bstep (se 1 (by rfl) ⟨353231, by rfl⟩ : syracuseStep 470975 = 706463) B706463
theorem B471095 : Blo 311834 471095 := bstep (se 1 (by rfl) ⟨353321, by rfl⟩ : syracuseStep 471095 = 706643) B706643
theorem B1060937 : Blo 311834 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B503929 : Blo 311834 503929 := bstep (se 2 (by rfl) ⟨188973, by rfl⟩ : syracuseStep 503929 = 377947) B377947
theorem B3387905 : Blo 311834 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B471593 : Blo 311834 471593 := bstep (se 2 (by rfl) ⟨176847, by rfl⟩ : syracuseStep 471593 = 353695) B353695
theorem B73740901 : Blo 311834 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B472031 : Blo 311834 472031 := bstep (se 1 (by rfl) ⟨354023, by rfl⟩ : syracuseStep 472031 = 708047) B708047
theorem B3028265 : Blo 311834 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B701927 : Blo 311834 701927 := bstep (se 1 (by rfl) ⟨526445, by rfl⟩ : syracuseStep 701927 = 1052891) B1052891
theorem B472679 : Blo 311834 472679 := bstep (se 1 (by rfl) ⟨354509, by rfl⟩ : syracuseStep 472679 = 709019) B709019
theorem B1193737 : Blo 311834 1193737 := bstep (se 2 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 1193737 = 895303) B895303
theorem B472871 : Blo 311834 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B18233225 : Blo 311834 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B899039 : Blo 311834 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B899063 : Blo 311834 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B3389759 : Blo 311834 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B2701775 : Blo 311834 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B1588409 : Blo 311834 1588409 := bstep (se 2 (by rfl) ⟨595653, by rfl⟩ : syracuseStep 1588409 = 1191307) B1191307
theorem B1064123 : Blo 311834 1064123 := bstep (se 1 (by rfl) ⟨798092, by rfl⟩ : syracuseStep 1064123 = 1596185) B1596185
theorem B3554603 : Blo 311834 3554603 := bstep (se 1 (by rfl) ⟨2665952, by rfl⟩ : syracuseStep 3554603 = 5331905) B5331905
theorem B59030957 : Blo 311834 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B703979 : Blo 311834 703979 := bstep (se 1 (by rfl) ⟨527984, by rfl⟩ : syracuseStep 703979 = 1055969) B1055969
theorem B1588895 : Blo 311834 1588895 := bstep (se 1 (by rfl) ⟨1191671, by rfl⟩ : syracuseStep 1588895 = 2383343) B2383343
theorem B1065149 : Blo 311834 1065149 := bstep (se 3 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 1065149 = 399431) B399431
theorem B1065311 : Blo 311834 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B2703725 : Blo 311834 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B705257 : Blo 311834 705257 := bstep (se 2 (by rfl) ⟨264471, by rfl⟩ : syracuseStep 705257 = 528943) B528943
theorem B705311 : Blo 311834 705311 := bstep (se 1 (by rfl) ⟨528983, by rfl⟩ : syracuseStep 705311 = 1057967) B1057967
theorem B9192269 : Blo 311834 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B706139 : Blo 311834 706139 := bstep (se 1 (by rfl) ⟨529604, by rfl⟩ : syracuseStep 706139 = 1059209) B1059209
theorem B313039 : Blo 311834 313039 := bstep (se 1 (by rfl) ⟨234779, by rfl⟩ : syracuseStep 313039 = 469559) B469559
theorem B313179 : Blo 311834 313179 := bstep (se 1 (by rfl) ⟨234884, by rfl⟩ : syracuseStep 313179 = 469769) B469769
theorem B444457 : Blo 311834 444457 := bstep (se 2 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 444457 = 333343) B333343
theorem B313455 : Blo 311834 313455 := bstep (se 1 (by rfl) ⟨235091, by rfl⟩ : syracuseStep 313455 = 470183) B470183
theorem B3656123 : Blo 311834 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B6015617 : Blo 311834 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B314011 : Blo 311834 314011 := bstep (se 1 (by rfl) ⟨235508, by rfl⟩ : syracuseStep 314011 = 471017) B471017
theorem B314047 : Blo 311834 314047 := bstep (se 1 (by rfl) ⟨235535, by rfl⟩ : syracuseStep 314047 = 471071) B471071
theorem B314107 : Blo 311834 314107 := bstep (se 1 (by rfl) ⟨235580, by rfl⟩ : syracuseStep 314107 = 471161) B471161
theorem B3066623 : Blo 311834 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B445351 : Blo 311834 445351 := bstep (se 1 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 445351 = 668027) B668027
theorem B314367 : Blo 311834 314367 := bstep (se 1 (by rfl) ⟨235775, by rfl⟩ : syracuseStep 314367 = 471551) B471551
theorem B1821737 : Blo 311834 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B314459 : Blo 311834 314459 := bstep (se 1 (by rfl) ⟨235844, by rfl⟩ : syracuseStep 314459 = 471689) B471689
theorem B314619 : Blo 311834 314619 := bstep (se 1 (by rfl) ⟨235964, by rfl⟩ : syracuseStep 314619 = 471929) B471929
theorem B314671 : Blo 311834 314671 := bstep (se 1 (by rfl) ⟨236003, by rfl⟩ : syracuseStep 314671 = 472007) B472007
theorem B314911 : Blo 311834 314911 := bstep (se 1 (by rfl) ⟨236183, by rfl⟩ : syracuseStep 314911 = 472367) B472367
theorem B708137 : Blo 311834 708137 := bstep (se 2 (by rfl) ⟨265551, by rfl⟩ : syracuseStep 708137 = 531103) B531103
theorem B315071 : Blo 311834 315071 := bstep (se 1 (by rfl) ⟨236303, by rfl⟩ : syracuseStep 315071 = 472607) B472607
theorem B315135 : Blo 311834 315135 := bstep (se 1 (by rfl) ⟨236351, by rfl⟩ : syracuseStep 315135 = 472703) B472703
theorem B2248681 : Blo 311834 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B708587 : Blo 311834 708587 := bstep (se 1 (by rfl) ⟨531440, by rfl⟩ : syracuseStep 708587 = 1062881) B1062881
theorem B315423 : Blo 311834 315423 := bstep (se 1 (by rfl) ⟨236567, by rfl⟩ : syracuseStep 315423 = 473135) B473135
theorem B315503 : Blo 311834 315503 := bstep (se 1 (by rfl) ⟨236627, by rfl⟩ : syracuseStep 315503 = 473255) B473255
theorem B709127 : Blo 311834 709127 := bstep (se 1 (by rfl) ⟨531845, by rfl⟩ : syracuseStep 709127 = 1063691) B1063691
theorem B447401 : Blo 311834 447401 := bstep (se 2 (by rfl) ⟨167775, by rfl⟩ : syracuseStep 447401 = 335551) B335551
theorem B447481 : Blo 311834 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B1791017 : Blo 311834 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B709991 : Blo 311834 709991 := bstep (se 1 (by rfl) ⟨532493, by rfl⟩ : syracuseStep 709991 = 1064987) B1064987
theorem B1594889 : Blo 311834 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B710171 : Blo 311834 710171 := bstep (se 1 (by rfl) ⟨532628, by rfl⟩ : syracuseStep 710171 = 1065257) B1065257
theorem B1791791 : Blo 311834 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B710567 : Blo 311834 710567 := bstep (se 1 (by rfl) ⟨532925, by rfl⟩ : syracuseStep 710567 = 1065851) B1065851
theorem B4282283 : Blo 311834 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B8608123 : Blo 311834 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B3561893 : Blo 311834 3561893 := bstep (se 4 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 3561893 = 667855) B667855
theorem B351103 : Blo 311834 351103 := bstep (se 1 (by rfl) ⟨263327, by rfl⟩ : syracuseStep 351103 = 526655) B526655
theorem B2022407 : Blo 311834 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B2382857 : Blo 311834 2382857 := bstep (se 2 (by rfl) ⟨893571, by rfl⟩ : syracuseStep 2382857 = 1787143) B1787143
theorem B1269377 : Blo 311834 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B352615 : Blo 311834 352615 := bstep (se 1 (by rfl) ⟨264461, by rfl⟩ : syracuseStep 352615 = 528923) B528923
theorem B1597805 : Blo 311834 1597805 := bstep (se 3 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 1597805 = 599177) B599177
theorem B353407 : Blo 311834 353407 := bstep (se 1 (by rfl) ⟨265055, by rfl⟩ : syracuseStep 353407 = 530111) B530111
theorem B1206211 : Blo 311834 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B3401777 : Blo 311834 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B2156827 : Blo 311834 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B3205715 : Blo 311834 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B3566267 : Blo 311834 3566267 := bstep (se 1 (by rfl) ⟨2674700, by rfl⟩ : syracuseStep 3566267 = 5349401) B5349401
theorem B2257703 : Blo 311834 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B849149 : Blo 311834 849149 := bstep (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) B318431
theorem B3569183 : Blo 311834 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B2685089 : Blo 311834 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B2390633 : Blo 311834 2390633 := bstep (se 2 (by rfl) ⟨896487, by rfl⟩ : syracuseStep 2390633 = 1792975) B1792975
theorem B4520711 : Blo 311834 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B2554679 : Blo 311834 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B1802483 : Blo 311834 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B6128179 : Blo 311834 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B592039 : Blo 311834 592039 := bstep (se 1 (by rfl) ⟨444029, by rfl⟩ : syracuseStep 592039 = 888059) B888059
theorem B526783 : Blo 311834 526783 := bstep (se 1 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 526783 = 790175) B790175
theorem B1608281 : Blo 311834 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B592609 : Blo 311834 592609 := bstep (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) B444457
theorem B2034503 : Blo 311834 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B1444799 : Blo 311834 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B527303 : Blo 311834 527303 := bstep (se 1 (by rfl) ⟨395477, by rfl⟩ : syracuseStep 527303 = 790955) B790955
theorem B593801 : Blo 311834 593801 := bstep (se 2 (by rfl) ⟨222675, by rfl⟩ : syracuseStep 593801 = 445351) B445351
theorem B2854855 : Blo 311834 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B790519 : Blo 311834 790519 := bstep (se 1 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 790519 = 1185779) B1185779
theorem B528511 : Blo 311834 528511 := bstep (se 1 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 528511 = 792767) B792767
theorem B790823 : Blo 311834 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B397639 : Blo 311834 397639 := bstep (se 1 (by rfl) ⟨298229, by rfl⟩ : syracuseStep 397639 = 596459) B596459
theorem B1348271 : Blo 311834 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B791279 : Blo 311834 791279 := bstep (se 1 (by rfl) ⟨593459, by rfl⟩ : syracuseStep 791279 = 1186919) B1186919
theorem B529375 : Blo 311834 529375 := bstep (se 1 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 529375 = 794063) B794063
theorem B1053863 : Blo 311834 1053863 := bstep (se 1 (by rfl) ⟨790397, by rfl⟩ : syracuseStep 1053863 = 1580795) B1580795
theorem B2397437 : Blo 311834 2397437 := bstep (se 3 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 2397437 = 899039) B899039
theorem B529915 : Blo 311834 529915 := bstep (se 1 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 529915 = 794873) B794873
theorem B595487 : Blo 311834 595487 := bstep (se 1 (by rfl) ⟨446615, by rfl⟩ : syracuseStep 595487 = 893231) B893231
theorem B530023 : Blo 311834 530023 := bstep (se 1 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 530023 = 795035) B795035
theorem B596641 : Blo 311834 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B2267851 : Blo 311834 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B1055483 : Blo 311834 1055483 := bstep (se 1 (by rfl) ⟨791612, by rfl⟩ : syracuseStep 1055483 = 1583225) B1583225
theorem B1055591 : Blo 311834 1055591 := bstep (se 1 (by rfl) ⟨791693, by rfl⟩ : syracuseStep 1055591 = 1583387) B1583387
theorem B1186751 : Blo 311834 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B8134319 : Blo 311834 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B4857965 : Blo 311834 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B11477497 : Blo 311834 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B566099 : Blo 311834 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B467951 : Blo 311834 467951 := bstep (se 1 (by rfl) ⟨350963, by rfl⟩ : syracuseStep 467951 = 701927) B701927
theorem B468137 : Blo 311834 468137 := bstep (se 2 (by rfl) ⟨175551, by rfl⟩ : syracuseStep 468137 = 351103) B351103
theorem B599375 : Blo 311834 599375 := bstep (se 1 (by rfl) ⟨449531, by rfl⟩ : syracuseStep 599375 = 899063) B899063
theorem B1058939 : Blo 311834 1058939 := bstep (se 1 (by rfl) ⟨794204, by rfl⟩ : syracuseStep 1058939 = 1588409) B1588409
theorem B2369735 : Blo 311834 2369735 := bstep (se 1 (by rfl) ⟨1777301, by rfl⟩ : syracuseStep 2369735 = 3554603) B3554603
theorem B469319 : Blo 311834 469319 := bstep (se 1 (by rfl) ⟨351989, by rfl⟩ : syracuseStep 469319 = 703979) B703979
theorem B1059263 : Blo 311834 1059263 := bstep (se 1 (by rfl) ⟨794447, by rfl⟩ : syracuseStep 1059263 = 1588895) B1588895
theorem B535081 : Blo 311834 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B470153 : Blo 311834 470153 := bstep (se 2 (by rfl) ⟨176307, by rfl⟩ : syracuseStep 470153 = 352615) B352615
theorem B470171 : Blo 311834 470171 := bstep (se 1 (by rfl) ⟨352628, by rfl⟩ : syracuseStep 470171 = 705257) B705257
theorem B470207 : Blo 311834 470207 := bstep (se 1 (by rfl) ⟨352655, by rfl⟩ : syracuseStep 470207 = 705311) B705311
theorem B3124939 : Blo 311834 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B470759 : Blo 311834 470759 := bstep (se 1 (by rfl) ⟨353069, by rfl⟩ : syracuseStep 470759 = 706139) B706139
theorem B471209 : Blo 311834 471209 := bstep (se 2 (by rfl) ⟨176703, by rfl⟩ : syracuseStep 471209 = 353407) B353407
theorem B2437415 : Blo 311834 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B4010411 : Blo 311834 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B2044415 : Blo 311834 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B504647 : Blo 311834 504647 := bstep (se 1 (by rfl) ⟨378485, by rfl⟩ : syracuseStep 504647 = 756971) B756971
theorem B472091 : Blo 311834 472091 := bstep (se 1 (by rfl) ⟨354068, by rfl⟩ : syracuseStep 472091 = 708137) B708137
theorem B1193069 : Blo 311834 1193069 := bstep (se 3 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 1193069 = 447401) B447401
theorem B472391 : Blo 311834 472391 := bstep (se 1 (by rfl) ⟨354293, by rfl⟩ : syracuseStep 472391 = 708587) B708587
theorem B472751 : Blo 311834 472751 := bstep (se 1 (by rfl) ⟨354563, by rfl⟩ : syracuseStep 472751 = 709127) B709127
theorem B1194011 : Blo 311834 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B2013407 : Blo 311834 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B473327 : Blo 311834 473327 := bstep (se 1 (by rfl) ⟨354995, by rfl⟩ : syracuseStep 473327 = 709991) B709991
theorem B1063259 : Blo 311834 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B473447 : Blo 311834 473447 := bstep (se 1 (by rfl) ⟨355085, by rfl⟩ : syracuseStep 473447 = 710171) B710171
theorem B1194527 : Blo 311834 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B473711 : Blo 311834 473711 := bstep (se 1 (by rfl) ⟨355283, by rfl⟩ : syracuseStep 473711 = 710567) B710567
theorem B703295 : Blo 311834 703295 := bstep (se 1 (by rfl) ⟨527471, by rfl⟩ : syracuseStep 703295 = 1054943) B1054943
theorem B2374595 : Blo 311834 2374595 := bstep (se 1 (by rfl) ⟨1780946, by rfl⟩ : syracuseStep 2374595 = 3561893) B3561893
theorem B703799 : Blo 311834 703799 := bstep (se 1 (by rfl) ⟨527849, by rfl⟩ : syracuseStep 703799 = 1055699) B1055699
theorem B1588571 : Blo 311834 1588571 := bstep (se 1 (by rfl) ⟨1191428, by rfl⟩ : syracuseStep 1588571 = 2382857) B2382857
theorem B703871 : Blo 311834 703871 := bstep (se 1 (by rfl) ⟨527903, by rfl⟩ : syracuseStep 703871 = 1055807) B1055807
theorem B2998241 : Blo 311834 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B671905 : Blo 311834 671905 := bstep (se 2 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 671905 = 503929) B503929
theorem B1065203 : Blo 311834 1065203 := bstep (se 1 (by rfl) ⟨798902, by rfl⟩ : syracuseStep 1065203 = 1597805) B1597805
theorem B312039 : Blo 311834 312039 := bstep (se 1 (by rfl) ⟨234029, by rfl⟩ : syracuseStep 312039 = 468059) B468059
theorem B312047 : Blo 311834 312047 := bstep (se 1 (by rfl) ⟨234035, by rfl⟩ : syracuseStep 312047 = 468071) B468071
theorem B98321201 : Blo 311834 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B312135 : Blo 311834 312135 := bstep (se 1 (by rfl) ⟨234101, by rfl⟩ : syracuseStep 312135 = 468203) B468203
theorem B312347 : Blo 311834 312347 := bstep (se 1 (by rfl) ⟨234260, by rfl⟩ : syracuseStep 312347 = 468521) B468521
theorem B312571 : Blo 311834 312571 := bstep (se 1 (by rfl) ⟨234428, by rfl⟩ : syracuseStep 312571 = 468857) B468857
theorem B706121 : Blo 311834 706121 := bstep (se 2 (by rfl) ⟨264795, by rfl⟩ : syracuseStep 706121 = 529591) B529591
theorem B313063 : Blo 311834 313063 := bstep (se 1 (by rfl) ⟨234797, by rfl⟩ : syracuseStep 313063 = 469595) B469595
theorem B2377511 : Blo 311834 2377511 := bstep (se 1 (by rfl) ⟨1783133, by rfl⟩ : syracuseStep 2377511 = 3566267) B3566267
theorem B313159 : Blo 311834 313159 := bstep (se 1 (by rfl) ⟨234869, by rfl⟩ : syracuseStep 313159 = 469739) B469739
theorem B706427 : Blo 311834 706427 := bstep (se 1 (by rfl) ⟨529820, by rfl⟩ : syracuseStep 706427 = 1059641) B1059641
theorem B1591649 : Blo 311834 1591649 := bstep (se 2 (by rfl) ⟨596868, by rfl⟩ : syracuseStep 1591649 = 1193737) B1193737
theorem B313823 : Blo 311834 313823 := bstep (se 1 (by rfl) ⟨235367, by rfl⟩ : syracuseStep 313823 = 470735) B470735
theorem B313983 : Blo 311834 313983 := bstep (se 1 (by rfl) ⟨235487, by rfl⟩ : syracuseStep 313983 = 470975) B470975
theorem B314063 : Blo 311834 314063 := bstep (se 1 (by rfl) ⟨235547, by rfl⟩ : syracuseStep 314063 = 471095) B471095
theorem B707291 : Blo 311834 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B314395 : Blo 311834 314395 := bstep (se 1 (by rfl) ⟨235796, by rfl⟩ : syracuseStep 314395 = 471593) B471593
theorem B314687 : Blo 311834 314687 := bstep (se 1 (by rfl) ⟨236015, by rfl⟩ : syracuseStep 314687 = 472031) B472031
theorem B2018843 : Blo 311834 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B2379455 : Blo 311834 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B315119 : Blo 311834 315119 := bstep (se 1 (by rfl) ⟨236339, by rfl⟩ : syracuseStep 315119 = 472679) B472679
theorem B315247 : Blo 311834 315247 := bstep (se 1 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 315247 = 472871) B472871
theorem B1790059 : Blo 311834 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B1593755 : Blo 311834 1593755 := bstep (se 1 (by rfl) ⟨1195316, by rfl⟩ : syracuseStep 1593755 = 2390633) B2390633
theorem B709415 : Blo 311834 709415 := bstep (se 1 (by rfl) ⟨532061, by rfl⟩ : syracuseStep 709415 = 1064123) B1064123
theorem B710099 : Blo 311834 710099 := bstep (se 1 (by rfl) ⟨532574, by rfl⟩ : syracuseStep 710099 = 1065149) B1065149
theorem B710207 : Blo 311834 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B2251243 : Blo 311834 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B350887 : Blo 311834 350887 := bstep (se 1 (by rfl) ⟨263165, by rfl⟩ : syracuseStep 350887 = 526331) B526331
theorem B1137719 : Blo 311834 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B1793249 : Blo 311834 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B2875769 : Blo 311834 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B6054983 : Blo 311834 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B354559 : Blo 311834 354559 := bstep (se 1 (by rfl) ⟨265919, by rfl⟩ : syracuseStep 354559 = 531839) B531839
theorem B846251 : Blo 311834 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B8548573 : Blo 311834 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B2388203 : Blo 311834 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B6779335 : Blo 311834 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B2258603 : Blo 311834 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B1505135 : Blo 311834 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B12155483 : Blo 311834 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B2259839 : Blo 311834 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B1801183 : Blo 311834 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B3013807 : Blo 311834 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B1703119 : Blo 311834 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B39353971 : Blo 311834 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B15303329 : Blo 311834 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B1345895 : Blo 311834 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B395867 : Blo 311834 395867 := bstep (se 1 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 395867 = 593801) B593801
theorem B527215 : Blo 311834 527215 := bstep (se 1 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 527215 = 790823) B790823
theorem B789385 : Blo 311834 789385 := bstep (se 2 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 789385 = 592039) B592039
theorem B527519 : Blo 311834 527519 := bstep (se 1 (by rfl) ⟨395639, by rfl⟩ : syracuseStep 527519 = 791279) B791279
theorem B790145 : Blo 311834 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B396991 : Blo 311834 396991 := bstep (se 1 (by rfl) ⟨297743, by rfl⟩ : syracuseStep 396991 = 595487) B595487
theorem B791167 : Blo 311834 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B758479 : Blo 311834 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B4166585 : Blo 311834 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B3806473 : Blo 311834 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B1054025 : Blo 311834 1054025 := bstep (se 2 (by rfl) ⟨395259, by rfl⟩ : syracuseStep 1054025 = 790519) B790519
theorem B530185 : Blo 311834 530185 := bstep (se 2 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 530185 = 397639) B397639
theorem B4036655 : Blo 311834 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B399583 : Blo 311834 399583 := bstep (se 1 (by rfl) ⟨299687, by rfl⟩ : syracuseStep 399583 = 599375) B599375
theorem B1579823 : Blo 311834 1579823 := bstep (se 1 (by rfl) ⟨1184867, by rfl⟩ : syracuseStep 1579823 = 2369735) B2369735
theorem B564167 : Blo 311834 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B336431 : Blo 311834 336431 := bstep (se 1 (by rfl) ⟨252323, by rfl⟩ : syracuseStep 336431 = 504647) B504647
theorem B795379 : Blo 311834 795379 := bstep (se 1 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 795379 = 1193069) B1193069
theorem B795521 : Blo 311834 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B467849 : Blo 311834 467849 := bstep (se 2 (by rfl) ⟨175443, by rfl⟩ : syracuseStep 467849 = 350887) B350887
theorem B3023801 : Blo 311834 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B2401577 : Blo 311834 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B796007 : Blo 311834 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B2270825 : Blo 311834 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B796351 : Blo 311834 796351 := bstep (se 1 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 796351 = 1194527) B1194527
theorem B8103655 : Blo 311834 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B468863 : Blo 311834 468863 := bstep (se 1 (by rfl) ⟨351647, by rfl⟩ : syracuseStep 468863 = 703295) B703295
theorem B1583063 : Blo 311834 1583063 := bstep (se 1 (by rfl) ⟨1187297, by rfl⟩ : syracuseStep 1583063 = 2374595) B2374595
theorem B52471961 : Blo 311834 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B469199 : Blo 311834 469199 := bstep (se 1 (by rfl) ⟨351899, by rfl⟩ : syracuseStep 469199 = 703799) B703799
theorem B1059047 : Blo 311834 1059047 := bstep (se 1 (by rfl) ⟨794285, by rfl⟩ : syracuseStep 1059047 = 1588571) B1588571
theorem B469247 : Blo 311834 469247 := bstep (se 1 (by rfl) ⟨351935, by rfl⟩ : syracuseStep 469247 = 703871) B703871
theorem B895873 : Blo 311834 895873 := bstep (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) B671905
theorem B65547467 : Blo 311834 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B470747 : Blo 311834 470747 := bstep (se 1 (by rfl) ⟨353060, by rfl⟩ : syracuseStep 470747 = 706121) B706121
theorem B1585007 : Blo 311834 1585007 := bstep (se 1 (by rfl) ⟨1188755, by rfl⟩ : syracuseStep 1585007 = 2377511) B2377511
theorem B470951 : Blo 311834 470951 := bstep (se 1 (by rfl) ⟨353213, by rfl⟩ : syracuseStep 470951 = 706427) B706427
theorem B1061099 : Blo 311834 1061099 := bstep (se 1 (by rfl) ⟨795824, by rfl⟩ : syracuseStep 1061099 = 1591649) B1591649
theorem B471527 : Blo 311834 471527 := bstep (se 1 (by rfl) ⟨353645, by rfl⟩ : syracuseStep 471527 = 707291) B707291
theorem B1356335 : Blo 311834 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B963199 : Blo 311834 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B1586303 : Blo 311834 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B12006629 : Blo 311834 12006629 := bstep (se 4 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 12006629 = 2251243) B2251243
theorem B1062503 : Blo 311834 1062503 := bstep (se 1 (by rfl) ⟨796877, by rfl⟩ : syracuseStep 1062503 = 1593755) B1593755
theorem B472745 : Blo 311834 472745 := bstep (se 2 (by rfl) ⟨177279, by rfl⟩ : syracuseStep 472745 = 354559) B354559
theorem B898847 : Blo 311834 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B472943 : Blo 311834 472943 := bstep (se 1 (by rfl) ⟨354707, by rfl⟩ : syracuseStep 472943 = 709415) B709415
theorem B702377 : Blo 311834 702377 := bstep (se 2 (by rfl) ⟨263391, by rfl⟩ : syracuseStep 702377 = 526783) B526783
theorem B702575 : Blo 311834 702575 := bstep (se 1 (by rfl) ⟨526931, by rfl⟩ : syracuseStep 702575 = 1053863) B1053863
theorem B473399 : Blo 311834 473399 := bstep (se 1 (by rfl) ⟨355049, by rfl⟩ : syracuseStep 473399 = 710099) B710099
theorem B473471 : Blo 311834 473471 := bstep (se 1 (by rfl) ⟨355103, by rfl⟩ : syracuseStep 473471 = 710207) B710207
theorem B703655 : Blo 311834 703655 := bstep (se 1 (by rfl) ⟨527741, by rfl⟩ : syracuseStep 703655 = 1055483) B1055483
theorem B703727 : Blo 311834 703727 := bstep (se 1 (by rfl) ⟨527795, by rfl⟩ : syracuseStep 703727 = 1055591) B1055591
theorem B1195499 : Blo 311834 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B5422879 : Blo 311834 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B704681 : Blo 311834 704681 := bstep (se 2 (by rfl) ⟨264255, by rfl⟩ : syracuseStep 704681 = 528511) B528511
theorem B1917179 : Blo 311834 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B377399 : Blo 311834 377399 := bstep (se 1 (by rfl) ⟨283049, by rfl⟩ : syracuseStep 377399 = 566099) B566099
theorem B311967 : Blo 311834 311967 := bstep (se 1 (by rfl) ⟨233975, by rfl⟩ : syracuseStep 311967 = 467951) B467951
theorem B312091 : Blo 311834 312091 := bstep (se 1 (by rfl) ⟨234068, by rfl⟩ : syracuseStep 312091 = 468137) B468137
theorem B705833 : Blo 311834 705833 := bstep (se 2 (by rfl) ⟨264687, by rfl⟩ : syracuseStep 705833 = 529375) B529375
theorem B705959 : Blo 311834 705959 := bstep (se 1 (by rfl) ⟨529469, by rfl⟩ : syracuseStep 705959 = 1058939) B1058939
theorem B312879 : Blo 311834 312879 := bstep (se 1 (by rfl) ⟨234659, by rfl⟩ : syracuseStep 312879 = 469319) B469319
theorem B706175 : Blo 311834 706175 := bstep (se 1 (by rfl) ⟨529631, by rfl⟩ : syracuseStep 706175 = 1059263) B1059263
theorem B706553 : Blo 311834 706553 := bstep (se 2 (by rfl) ⟨264957, by rfl⟩ : syracuseStep 706553 = 529915) B529915
theorem B313435 : Blo 311834 313435 := bstep (se 1 (by rfl) ⟨235076, by rfl⟩ : syracuseStep 313435 = 470153) B470153
theorem B313447 : Blo 311834 313447 := bstep (se 1 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 313447 = 470171) B470171
theorem B313471 : Blo 311834 313471 := bstep (se 1 (by rfl) ⟨235103, by rfl⟩ : syracuseStep 313471 = 470207) B470207
theorem B706697 : Blo 311834 706697 := bstep (se 2 (by rfl) ⟨265011, by rfl⟩ : syracuseStep 706697 = 530023) B530023
theorem B313839 : Blo 311834 313839 := bstep (se 1 (by rfl) ⟨235379, by rfl⟩ : syracuseStep 313839 = 470759) B470759
theorem B314139 : Blo 311834 314139 := bstep (se 1 (by rfl) ⟨235604, by rfl⟩ : syracuseStep 314139 = 471209) B471209
theorem B1592135 : Blo 311834 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B1624943 : Blo 311834 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B2673607 : Blo 311834 2673607 := bstep (se 1 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 2673607 = 4010411) B4010411
theorem B1362943 : Blo 311834 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B314727 : Blo 311834 314727 := bstep (se 1 (by rfl) ⟨236045, by rfl⟩ : syracuseStep 314727 = 472091) B472091
theorem B314927 : Blo 311834 314927 := bstep (se 1 (by rfl) ⟨236195, by rfl⟩ : syracuseStep 314927 = 472391) B472391
theorem B315167 : Blo 311834 315167 := bstep (se 1 (by rfl) ⟨236375, by rfl⟩ : syracuseStep 315167 = 472751) B472751
theorem B1003423 : Blo 311834 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B315551 : Blo 311834 315551 := bstep (se 1 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 315551 = 473327) B473327
theorem B708839 : Blo 311834 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B4018409 : Blo 311834 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B315631 : Blo 311834 315631 := bstep (se 1 (by rfl) ⟨236723, by rfl⟩ : syracuseStep 315631 = 473447) B473447
theorem B315807 : Blo 311834 315807 := bstep (se 1 (by rfl) ⟨236855, by rfl⟩ : syracuseStep 315807 = 473711) B473711
theorem B1201655 : Blo 311834 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B710135 : Blo 311834 710135 := bstep (se 1 (by rfl) ⟨532601, by rfl⟩ : syracuseStep 710135 = 1065203) B1065203
theorem B130734485 : Blo 311834 130734485 := bstep (se 6 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 130734485 = 6128179) B6128179
theorem B1072187 : Blo 311834 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B351535 : Blo 311834 351535 := bstep (se 1 (by rfl) ⟨263651, by rfl⟩ : syracuseStep 351535 = 527303) B527303
theorem B713441 : Blo 311834 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B1598291 : Blo 311834 1598291 := bstep (se 1 (by rfl) ⟨1198718, by rfl⟩ : syracuseStep 1598291 = 2397437) B2397437
theorem B3238643 : Blo 311834 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B2386745 : Blo 311834 2386745 := bstep (se 2 (by rfl) ⟨895029, by rfl⟩ : syracuseStep 2386745 = 1790059) B1790059
theorem B11398097 : Blo 311834 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B9039113 : Blo 311834 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B1505735 : Blo 311834 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B1342271 : Blo 311834 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B1506559 : Blo 311834 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B1998827 : Blo 311834 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B1278119 : Blo 311834 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B1083295 : Blo 311834 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B526763 : Blo 311834 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B1052513 : Blo 311834 1052513 := bstep (se 2 (by rfl) ⟨394692, by rfl⟩ : syracuseStep 1052513 = 789385) B789385
theorem B2691103 : Blo 311834 2691103 := bstep (se 1 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 2691103 = 4036655) B4036655
theorem B1053215 : Blo 311834 1053215 := bstep (se 1 (by rfl) ⟨789911, by rfl⟩ : syracuseStep 1053215 = 1579823) B1579823
theorem B529321 : Blo 311834 529321 := bstep (se 2 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 529321 = 396991) B396991
theorem B530347 : Blo 311834 530347 := bstep (se 1 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 530347 = 795521) B795521
theorem B1284265 : Blo 311834 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B1054889 : Blo 311834 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B530671 : Blo 311834 530671 := bstep (se 1 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 530671 = 796007) B796007
theorem B1513883 : Blo 311834 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B1055375 : Blo 311834 1055375 := bstep (se 1 (by rfl) ⟨791531, by rfl⟩ : syracuseStep 1055375 = 1583063) B1583063
theorem B1055645 : Blo 311834 1055645 := bstep (se 3 (by rfl) ⟨197933, by rfl⟩ : syracuseStep 1055645 = 395867) B395867
theorem B3579389 : Blo 311834 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1056671 : Blo 311834 1056671 := bstep (se 1 (by rfl) ⟨792503, by rfl⟩ : syracuseStep 1056671 = 1585007) B1585007
theorem B532777 : Blo 311834 532777 := bstep (se 2 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 532777 = 399583) B399583
theorem B1057535 : Blo 311834 1057535 := bstep (se 1 (by rfl) ⟨793151, by rfl⟩ : syracuseStep 1057535 = 1586303) B1586303
theorem B8004419 : Blo 311834 8004419 := bstep (se 1 (by rfl) ⟨6003314, by rfl⟩ : syracuseStep 8004419 = 12006629) B12006629
theorem B599231 : Blo 311834 599231 := bstep (se 1 (by rfl) ⟨449423, by rfl⟩ : syracuseStep 599231 = 898847) B898847
theorem B468251 : Blo 311834 468251 := bstep (se 1 (by rfl) ⟨351188, by rfl⟩ : syracuseStep 468251 = 702377) B702377
theorem B468383 : Blo 311834 468383 := bstep (se 1 (by rfl) ⟨351287, by rfl⟩ : syracuseStep 468383 = 702575) B702575
theorem B2008745 : Blo 311834 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B468713 : Blo 311834 468713 := bstep (se 2 (by rfl) ⟨175767, by rfl⟩ : syracuseStep 468713 = 351535) B351535
theorem B469103 : Blo 311834 469103 := bstep (se 1 (by rfl) ⟨351827, by rfl⟩ : syracuseStep 469103 = 703655) B703655
theorem B469151 : Blo 311834 469151 := bstep (se 1 (by rfl) ⟨351863, by rfl⟩ : syracuseStep 469151 = 703727) B703727
theorem B796999 : Blo 311834 796999 := bstep (se 1 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 796999 = 1195499) B1195499
theorem B469787 : Blo 311834 469787 := bstep (se 1 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 469787 = 704681) B704681
theorem B10202219 : Blo 311834 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B470555 : Blo 311834 470555 := bstep (se 1 (by rfl) ⟨352916, by rfl⟩ : syracuseStep 470555 = 705833) B705833
theorem B470639 : Blo 311834 470639 := bstep (se 1 (by rfl) ⟨352979, by rfl⟩ : syracuseStep 470639 = 705959) B705959
theorem B1060505 : Blo 311834 1060505 := bstep (se 2 (by rfl) ⟨397689, by rfl⟩ : syracuseStep 1060505 = 795379) B795379
theorem B470783 : Blo 311834 470783 := bstep (se 1 (by rfl) ⟨353087, by rfl⟩ : syracuseStep 470783 = 706175) B706175
theorem B471035 : Blo 311834 471035 := bstep (se 1 (by rfl) ⟨353276, by rfl⟩ : syracuseStep 471035 = 706553) B706553
theorem B471131 : Blo 311834 471131 := bstep (se 1 (by rfl) ⟨353348, by rfl⟩ : syracuseStep 471131 = 706697) B706697
theorem B897149 : Blo 311834 897149 := bstep (se 3 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 897149 = 336431) B336431
theorem B897263 : Blo 311834 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B1061423 : Blo 311834 1061423 := bstep (se 1 (by rfl) ⟨796067, by rfl⟩ : syracuseStep 1061423 = 1592135) B1592135
theorem B1061801 : Blo 311834 1061801 := bstep (se 2 (by rfl) ⟨398175, by rfl⟩ : syracuseStep 1061801 = 796351) B796351
theorem B472559 : Blo 311834 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B702683 : Blo 311834 702683 := bstep (se 1 (by rfl) ⟨527012, by rfl⟩ : syracuseStep 702683 = 1054025) B1054025
theorem B801103 : Blo 311834 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B473423 : Blo 311834 473423 := bstep (se 1 (by rfl) ⟨355067, by rfl⟩ : syracuseStep 473423 = 710135) B710135
theorem B702953 : Blo 311834 702953 := bstep (se 2 (by rfl) ⟨263607, by rfl⟩ : syracuseStep 702953 = 527215) B527215
theorem B1194497 : Blo 311834 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B1817257 : Blo 311834 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B376111 : Blo 311834 376111 := bstep (se 1 (by rfl) ⟨282083, by rfl⟩ : syracuseStep 376111 = 564167) B564167
theorem B475627 : Blo 311834 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B1065527 : Blo 311834 1065527 := bstep (se 1 (by rfl) ⟨799145, by rfl⟩ : syracuseStep 1065527 = 1598291) B1598291
theorem B311899 : Blo 311834 311899 := bstep (se 1 (by rfl) ⟨233924, by rfl⟩ : syracuseStep 311899 = 467849) B467849
theorem B2015867 : Blo 311834 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B312575 : Blo 311834 312575 := bstep (se 1 (by rfl) ⟨234431, by rfl⟩ : syracuseStep 312575 = 468863) B468863
theorem B34981307 : Blo 311834 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B312799 : Blo 311834 312799 := bstep (se 1 (by rfl) ⟨234599, by rfl⟩ : syracuseStep 312799 = 469199) B469199
theorem B706031 : Blo 311834 706031 := bstep (se 1 (by rfl) ⟨529523, by rfl⟩ : syracuseStep 706031 = 1059047) B1059047
theorem B312831 : Blo 311834 312831 := bstep (se 1 (by rfl) ⟨234623, by rfl⟩ : syracuseStep 312831 = 469247) B469247
theorem B1591163 : Blo 311834 1591163 := bstep (se 1 (by rfl) ⟨1193372, by rfl⟩ : syracuseStep 1591163 = 2386745) B2386745
theorem B8636381 : Blo 311834 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B43698311 : Blo 311834 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B706913 : Blo 311834 706913 := bstep (se 2 (by rfl) ⟨265092, by rfl⟩ : syracuseStep 706913 = 530185) B530185
theorem B313831 : Blo 311834 313831 := bstep (se 1 (by rfl) ⟨235373, by rfl⟩ : syracuseStep 313831 = 470747) B470747
theorem B313967 : Blo 311834 313967 := bstep (se 1 (by rfl) ⟨235475, by rfl⟩ : syracuseStep 313967 = 470951) B470951
theorem B707399 : Blo 311834 707399 := bstep (se 1 (by rfl) ⟨530549, by rfl⟩ : syracuseStep 707399 = 1061099) B1061099
theorem B314351 : Blo 311834 314351 := bstep (se 1 (by rfl) ⟨235763, by rfl⟩ : syracuseStep 314351 = 471527) B471527
theorem B904223 : Blo 311834 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B708335 : Blo 311834 708335 := bstep (se 1 (by rfl) ⟨531251, by rfl⟩ : syracuseStep 708335 = 1062503) B1062503
theorem B315163 : Blo 311834 315163 := bstep (se 1 (by rfl) ⟨236372, by rfl⟩ : syracuseStep 315163 = 472745) B472745
theorem B315295 : Blo 311834 315295 := bstep (se 1 (by rfl) ⟨236471, by rfl⟩ : syracuseStep 315295 = 472943) B472943
theorem B315599 : Blo 311834 315599 := bstep (se 1 (by rfl) ⟨236699, by rfl⟩ : syracuseStep 315599 = 473399) B473399
theorem B315647 : Blo 311834 315647 := bstep (se 1 (by rfl) ⟨236735, by rfl⟩ : syracuseStep 315647 = 473471) B473471
theorem B1003823 : Blo 311834 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B7230505 : Blo 311834 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1332551 : Blo 311834 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B1006397 : Blo 311834 1006397 := bstep (se 3 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 1006397 = 377399) B377399
theorem B351679 : Blo 311834 351679 := bstep (se 1 (by rfl) ⟨263759, by rfl⟩ : syracuseStep 351679 = 527519) B527519
theorem B2678939 : Blo 311834 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B2777723 : Blo 311834 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B3564809 : Blo 311834 3564809 := bstep (se 2 (by rfl) ⟨1336803, by rfl⟩ : syracuseStep 3564809 = 2673607) B2673607
theorem B87156323 : Blo 311834 87156323 := bstep (se 1 (by rfl) ⟨65367242, by rfl⟩ : syracuseStep 87156323 = 130734485) B130734485
theorem B714791 : Blo 311834 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B1337897 : Blo 311834 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B1601051 : Blo 311834 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B1011305 : Blo 311834 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B5075297 : Blo 311834 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B7598731 : Blo 311834 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B6026075 : Blo 311834 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B43219493 : Blo 311834 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B3408317 : Blo 311834 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B29132207 : Blo 311834 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B5375645 : Blo 311834 5375645 := bstep (se 3 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 5375645 = 2015867) B2015867
theorem B888367 : Blo 311834 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B399487 : Blo 311834 399487 := bstep (se 1 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 399487 = 599231) B599231
theorem B10131641 : Blo 311834 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B58104215 : Blo 311834 58104215 := bstep (se 1 (by rfl) ⟨43578161, by rfl⟩ : syracuseStep 58104215 = 87156323) B87156323
theorem B9640673 : Blo 311834 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B598099 : Blo 311834 598099 := bstep (se 1 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 598099 = 897149) B897149
theorem B598175 : Blo 311834 598175 := bstep (se 1 (by rfl) ⟨448631, by rfl⟩ : syracuseStep 598175 = 897263) B897263
theorem B1712353 : Blo 311834 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B3383531 : Blo 311834 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B4269469 : Blo 311834 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B468455 : Blo 311834 468455 := bstep (se 1 (by rfl) ⟨351341, by rfl⟩ : syracuseStep 468455 = 702683) B702683
theorem B2696813 : Blo 311834 2696813 := bstep (se 3 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 2696813 = 1011305) B1011305
theorem B468635 : Blo 311834 468635 := bstep (se 1 (by rfl) ⟨351476, by rfl⟩ : syracuseStep 468635 = 702953) B702953
theorem B796331 : Blo 311834 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B28812995 : Blo 311834 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B501481 : Blo 311834 501481 := bstep (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) B376111
theorem B468905 : Blo 311834 468905 := bstep (se 2 (by rfl) ⟨175839, by rfl⟩ : syracuseStep 468905 = 351679) B351679
theorem B5777573 : Blo 311834 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B634169 : Blo 311834 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B470687 : Blo 311834 470687 := bstep (se 1 (by rfl) ⟨353015, by rfl⟩ : syracuseStep 470687 = 706031) B706031
theorem B1060775 : Blo 311834 1060775 := bstep (se 1 (by rfl) ⟨795581, by rfl⟩ : syracuseStep 1060775 = 1591163) B1591163
theorem B471275 : Blo 311834 471275 := bstep (se 1 (by rfl) ⟨353456, by rfl⟩ : syracuseStep 471275 = 706913) B706913
theorem B471599 : Blo 311834 471599 := bstep (se 1 (by rfl) ⟨353699, by rfl⟩ : syracuseStep 471599 = 707399) B707399
theorem B602815 : Blo 311834 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B472223 : Blo 311834 472223 := bstep (se 1 (by rfl) ⟨354167, by rfl⟩ : syracuseStep 472223 = 708335) B708335
theorem B701675 : Blo 311834 701675 := bstep (se 1 (by rfl) ⟨526256, by rfl⟩ : syracuseStep 701675 = 1052513) B1052513
theorem B669215 : Blo 311834 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B702143 : Blo 311834 702143 := bstep (se 1 (by rfl) ⟨526607, by rfl⟩ : syracuseStep 702143 = 1053215) B1053215
theorem B1062665 : Blo 311834 1062665 := bstep (se 2 (by rfl) ⟨398499, by rfl⟩ : syracuseStep 1062665 = 796999) B796999
theorem B703259 : Blo 311834 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B703583 : Blo 311834 703583 := bstep (se 1 (by rfl) ⟨527687, by rfl⟩ : syracuseStep 703583 = 1055375) B1055375
theorem B670931 : Blo 311834 670931 := bstep (se 1 (by rfl) ⟨503198, by rfl⟩ : syracuseStep 670931 = 1006397) B1006397
theorem B703763 : Blo 311834 703763 := bstep (se 1 (by rfl) ⟨527822, by rfl⟩ : syracuseStep 703763 = 1055645) B1055645
theorem B704447 : Blo 311834 704447 := bstep (se 1 (by rfl) ⟨528335, by rfl⟩ : syracuseStep 704447 = 1056671) B1056671
theorem B3588137 : Blo 311834 3588137 := bstep (se 2 (by rfl) ⟨1345551, by rfl⟩ : syracuseStep 3588137 = 2691103) B2691103
theorem B1785959 : Blo 311834 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B1851815 : Blo 311834 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B705023 : Blo 311834 705023 := bstep (se 1 (by rfl) ⟨528767, by rfl⟩ : syracuseStep 705023 = 1057535) B1057535
theorem B2376539 : Blo 311834 2376539 := bstep (se 1 (by rfl) ⟨1782404, by rfl⟩ : syracuseStep 2376539 = 3564809) B3564809
theorem B312167 : Blo 311834 312167 := bstep (se 1 (by rfl) ⟨234125, by rfl⟩ : syracuseStep 312167 = 468251) B468251
theorem B312255 : Blo 311834 312255 := bstep (se 1 (by rfl) ⟨234191, by rfl⟩ : syracuseStep 312255 = 468383) B468383
theorem B312475 : Blo 311834 312475 := bstep (se 1 (by rfl) ⟨234356, by rfl⟩ : syracuseStep 312475 = 468713) B468713
theorem B705761 : Blo 311834 705761 := bstep (se 2 (by rfl) ⟨264660, by rfl⟩ : syracuseStep 705761 = 529321) B529321
theorem B476527 : Blo 311834 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B312735 : Blo 311834 312735 := bstep (se 1 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 312735 = 469103) B469103
theorem B312767 : Blo 311834 312767 := bstep (se 1 (by rfl) ⟨234575, by rfl⟩ : syracuseStep 312767 = 469151) B469151
theorem B313191 : Blo 311834 313191 := bstep (se 1 (by rfl) ⟨234893, by rfl⟩ : syracuseStep 313191 = 469787) B469787
theorem B6801479 : Blo 311834 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B313703 : Blo 311834 313703 := bstep (se 1 (by rfl) ⟨235277, by rfl⟩ : syracuseStep 313703 = 470555) B470555
theorem B313759 : Blo 311834 313759 := bstep (se 1 (by rfl) ⟨235319, by rfl⟩ : syracuseStep 313759 = 470639) B470639
theorem B707003 : Blo 311834 707003 := bstep (se 1 (by rfl) ⟨530252, by rfl⟩ : syracuseStep 707003 = 1060505) B1060505
theorem B313855 : Blo 311834 313855 := bstep (se 1 (by rfl) ⟨235391, by rfl⟩ : syracuseStep 313855 = 470783) B470783
theorem B707129 : Blo 311834 707129 := bstep (se 2 (by rfl) ⟨265173, by rfl⟩ : syracuseStep 707129 = 530347) B530347
theorem B314023 : Blo 311834 314023 := bstep (se 1 (by rfl) ⟨235517, by rfl⟩ : syracuseStep 314023 = 471035) B471035
theorem B314087 : Blo 311834 314087 := bstep (se 1 (by rfl) ⟨235565, by rfl⟩ : syracuseStep 314087 = 471131) B471131
theorem B707561 : Blo 311834 707561 := bstep (se 2 (by rfl) ⟨265335, by rfl⟩ : syracuseStep 707561 = 530671) B530671
theorem B707615 : Blo 311834 707615 := bstep (se 1 (by rfl) ⟨530711, by rfl⟩ : syracuseStep 707615 = 1061423) B1061423
theorem B1068137 : Blo 311834 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B4017383 : Blo 311834 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B707867 : Blo 311834 707867 := bstep (se 1 (by rfl) ⟨530900, by rfl⟩ : syracuseStep 707867 = 1061801) B1061801
theorem B315039 : Blo 311834 315039 := bstep (se 1 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 315039 = 472559) B472559
theorem B315615 : Blo 311834 315615 := bstep (se 1 (by rfl) ⟨236711, by rfl⟩ : syracuseStep 315615 = 473423) B473423
theorem B710351 : Blo 311834 710351 := bstep (se 1 (by rfl) ⟨532763, by rfl⟩ : syracuseStep 710351 = 1065527) B1065527
theorem B710369 : Blo 311834 710369 := bstep (se 2 (by rfl) ⟨266388, by rfl⟩ : syracuseStep 710369 = 532777) B532777
theorem B23320871 : Blo 311834 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B5757587 : Blo 311834 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B351175 : Blo 311834 351175 := bstep (se 1 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 351175 = 526763) B526763
theorem B1009255 : Blo 311834 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B2386259 : Blo 311834 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B5336279 : Blo 311834 5336279 := bstep (se 1 (by rfl) ⟨4002209, by rfl⟩ : syracuseStep 5336279 = 8004419) B8004419
theorem B1339163 : Blo 311834 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B3567725 : Blo 311834 3567725 := bstep (se 3 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 3567725 = 1337897) B1337897
theorem B2423009 : Blo 311834 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2392091 : Blo 311834 2392091 := bstep (se 1 (by rfl) ⟨1794068, by rfl⟩ : syracuseStep 2392091 = 3588137) B3588137
theorem B1345673 : Blo 311834 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B6754427 : Blo 311834 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B38736143 : Blo 311834 38736143 := bstep (se 1 (by rfl) ⟨29052107, by rfl⟩ : syracuseStep 38736143 = 58104215) B58104215
theorem B3838391 : Blo 311834 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B6427115 : Blo 311834 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B1184489 : Blo 311834 1184489 := bstep (se 2 (by rfl) ⟨444183, by rfl⟩ : syracuseStep 1184489 = 888367) B888367
theorem B398783 : Blo 311834 398783 := bstep (se 1 (by rfl) ⟨299087, by rfl⟩ : syracuseStep 398783 = 598175) B598175
theorem B15406861 : Blo 311834 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B530887 : Blo 311834 530887 := bstep (se 1 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 530887 = 796331) B796331
theorem B19208663 : Blo 311834 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B892775 : Blo 311834 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B532649 : Blo 311834 532649 := bstep (se 2 (by rfl) ⟨199743, by rfl⟩ : syracuseStep 532649 = 399487) B399487
theorem B467783 : Blo 311834 467783 := bstep (se 1 (by rfl) ⟨350837, by rfl⟩ : syracuseStep 467783 = 701675) B701675
theorem B468095 : Blo 311834 468095 := bstep (se 1 (by rfl) ⟨351071, by rfl⟩ : syracuseStep 468095 = 702143) B702143
theorem B468233 : Blo 311834 468233 := bstep (se 2 (by rfl) ⟨175587, by rfl⟩ : syracuseStep 468233 = 351175) B351175
theorem B1615339 : Blo 311834 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B468839 : Blo 311834 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B469055 : Blo 311834 469055 := bstep (se 1 (by rfl) ⟨351791, by rfl⟩ : syracuseStep 469055 = 703583) B703583
theorem B469175 : Blo 311834 469175 := bstep (se 1 (by rfl) ⟨351881, by rfl⟩ : syracuseStep 469175 = 703763) B703763
theorem B469631 : Blo 311834 469631 := bstep (se 1 (by rfl) ⟨352223, by rfl⟩ : syracuseStep 469631 = 704447) B704447
theorem B1190639 : Blo 311834 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B797465 : Blo 311834 797465 := bstep (se 2 (by rfl) ⟨299049, by rfl⟩ : syracuseStep 797465 = 598099) B598099
theorem B2272211 : Blo 311834 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B470015 : Blo 311834 470015 := bstep (se 1 (by rfl) ⟨352511, by rfl⟩ : syracuseStep 470015 = 705023) B705023
theorem B1584359 : Blo 311834 1584359 := bstep (se 1 (by rfl) ⟨1188269, by rfl⟩ : syracuseStep 1584359 = 2376539) B2376539
theorem B470507 : Blo 311834 470507 := bstep (se 1 (by rfl) ⟨352880, by rfl⟩ : syracuseStep 470507 = 705761) B705761
theorem B3583763 : Blo 311834 3583763 := bstep (se 1 (by rfl) ⟨2687822, by rfl⟩ : syracuseStep 3583763 = 5375645) B5375645
theorem B4534319 : Blo 311834 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B471335 : Blo 311834 471335 := bstep (se 1 (by rfl) ⟨353501, by rfl⟩ : syracuseStep 471335 = 707003) B707003
theorem B471419 : Blo 311834 471419 := bstep (se 1 (by rfl) ⟨353564, by rfl⟩ : syracuseStep 471419 = 707129) B707129
theorem B635369 : Blo 311834 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B471707 : Blo 311834 471707 := bstep (se 1 (by rfl) ⟨353780, by rfl⟩ : syracuseStep 471707 = 707561) B707561
theorem B471743 : Blo 311834 471743 := bstep (se 1 (by rfl) ⟨353807, by rfl⟩ : syracuseStep 471743 = 707615) B707615
theorem B471911 : Blo 311834 471911 := bstep (se 1 (by rfl) ⟨353933, by rfl⟩ : syracuseStep 471911 = 707867) B707867
theorem B473567 : Blo 311834 473567 := bstep (se 1 (by rfl) ⟨355175, by rfl⟩ : syracuseStep 473567 = 710351) B710351
theorem B473579 : Blo 311834 473579 := bstep (se 1 (by rfl) ⟨355184, by rfl⟩ : syracuseStep 473579 = 710369) B710369
theorem B15547247 : Blo 311834 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B803753 : Blo 311834 803753 := bstep (se 2 (by rfl) ⟨301407, by rfl⟩ : syracuseStep 803753 = 602815) B602815
theorem B312303 : Blo 311834 312303 := bstep (se 1 (by rfl) ⟨234227, by rfl⟩ : syracuseStep 312303 = 468455) B468455
theorem B312423 : Blo 311834 312423 := bstep (se 1 (by rfl) ⟨234317, by rfl⟩ : syracuseStep 312423 = 468635) B468635
theorem B312603 : Blo 311834 312603 := bstep (se 1 (by rfl) ⟨234452, by rfl⟩ : syracuseStep 312603 = 468905) B468905
theorem B1590839 : Blo 311834 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B3557519 : Blo 311834 3557519 := bstep (se 1 (by rfl) ⟨2668139, by rfl⟩ : syracuseStep 3557519 = 5336279) B5336279
theorem B313791 : Blo 311834 313791 := bstep (se 1 (by rfl) ⟨235343, by rfl⟩ : syracuseStep 313791 = 470687) B470687
theorem B707183 : Blo 311834 707183 := bstep (se 1 (by rfl) ⟨530387, by rfl⟩ : syracuseStep 707183 = 1060775) B1060775
theorem B2378483 : Blo 311834 2378483 := bstep (se 1 (by rfl) ⟨1783862, by rfl⟩ : syracuseStep 2378483 = 3567725) B3567725
theorem B314183 : Blo 311834 314183 := bstep (se 1 (by rfl) ⟨235637, by rfl⟩ : syracuseStep 314183 = 471275) B471275
theorem B314399 : Blo 311834 314399 := bstep (se 1 (by rfl) ⟨235799, by rfl⟩ : syracuseStep 314399 = 471599) B471599
theorem B314815 : Blo 311834 314815 := bstep (se 1 (by rfl) ⟨236111, by rfl⟩ : syracuseStep 314815 = 472223) B472223
theorem B1691117 : Blo 311834 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B446143 : Blo 311834 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B708443 : Blo 311834 708443 := bstep (se 1 (by rfl) ⟨531332, by rfl⟩ : syracuseStep 708443 = 1062665) B1062665
theorem B2674565 : Blo 311834 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B447287 : Blo 311834 447287 := bstep (se 1 (by rfl) ⟨335465, by rfl⟩ : syracuseStep 447287 = 670931) B670931
theorem B1234543 : Blo 311834 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B2283137 : Blo 311834 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B19421471 : Blo 311834 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B5692625 : Blo 311834 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B712091 : Blo 311834 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B2678255 : Blo 311834 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B2255687 : Blo 311834 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B1797875 : Blo 311834 1797875 := bstep (se 1 (by rfl) ⟨1348406, by rfl⟩ : syracuseStep 1797875 = 2696813) B2696813
theorem B25824095 : Blo 311834 25824095 := bstep (se 1 (by rfl) ⟨19368071, by rfl⟩ : syracuseStep 25824095 = 38736143) B38736143
theorem B2558927 : Blo 311834 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B789659 : Blo 311834 789659 := bstep (se 1 (by rfl) ⟨592244, by rfl⟩ : syracuseStep 789659 = 1184489) B1184489
theorem B594857 : Blo 311834 594857 := bstep (se 2 (by rfl) ⟨223071, by rfl⟩ : syracuseStep 594857 = 446143) B446143
theorem B595183 : Blo 311834 595183 := bstep (se 1 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 595183 = 892775) B892775
theorem B793759 : Blo 311834 793759 := bstep (se 1 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 793759 = 1190639) B1190639
theorem B531643 : Blo 311834 531643 := bstep (se 1 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 531643 = 797465) B797465
theorem B1514807 : Blo 311834 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B1646057 : Blo 311834 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1056239 : Blo 311834 1056239 := bstep (se 1 (by rfl) ⟨792179, by rfl⟩ : syracuseStep 1056239 = 1584359) B1584359
theorem B3022879 : Blo 311834 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B10364831 : Blo 311834 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B535835 : Blo 311834 535835 := bstep (se 1 (by rfl) ⟨401876, by rfl⟩ : syracuseStep 535835 = 803753) B803753
theorem B1060559 : Blo 311834 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B897115 : Blo 311834 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B2371679 : Blo 311834 2371679 := bstep (se 1 (by rfl) ⟨1778759, by rfl⟩ : syracuseStep 2371679 = 3557519) B3557519
theorem B471455 : Blo 311834 471455 := bstep (se 1 (by rfl) ⟨353591, by rfl⟩ : syracuseStep 471455 = 707183) B707183
theorem B1585655 : Blo 311834 1585655 := bstep (se 1 (by rfl) ⟨1189241, by rfl⟩ : syracuseStep 1585655 = 2378483) B2378483
theorem B1192765 : Blo 311834 1192765 := bstep (se 3 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 1192765 = 447287) B447287
theorem B1127411 : Blo 311834 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B472295 : Blo 311834 472295 := bstep (se 1 (by rfl) ⟨354221, by rfl⟩ : syracuseStep 472295 = 708443) B708443
theorem B1783043 : Blo 311834 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B4502951 : Blo 311834 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B1522091 : Blo 311834 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B1063421 : Blo 311834 1063421 := bstep (se 3 (by rfl) ⟨199391, by rfl⟩ : syracuseStep 1063421 = 398783) B398783
theorem B1785503 : Blo 311834 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B311855 : Blo 311834 311855 := bstep (se 1 (by rfl) ⟨233891, by rfl⟩ : syracuseStep 311855 = 467783) B467783
theorem B51790589 : Blo 311834 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B312063 : Blo 311834 312063 := bstep (se 1 (by rfl) ⟨234047, by rfl⟩ : syracuseStep 312063 = 468095) B468095
theorem B312155 : Blo 311834 312155 := bstep (se 1 (by rfl) ⟨234116, by rfl⟩ : syracuseStep 312155 = 468233) B468233
theorem B312559 : Blo 311834 312559 := bstep (se 1 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 312559 = 468839) B468839
theorem B312703 : Blo 311834 312703 := bstep (se 1 (by rfl) ⟨234527, by rfl⟩ : syracuseStep 312703 = 469055) B469055
theorem B312783 : Blo 311834 312783 := bstep (se 1 (by rfl) ⟨234587, by rfl⟩ : syracuseStep 312783 = 469175) B469175
theorem B313087 : Blo 311834 313087 := bstep (se 1 (by rfl) ⟨234815, by rfl⟩ : syracuseStep 313087 = 469631) B469631
theorem B313343 : Blo 311834 313343 := bstep (se 1 (by rfl) ⟨235007, by rfl⟩ : syracuseStep 313343 = 470015) B470015
theorem B313671 : Blo 311834 313671 := bstep (se 1 (by rfl) ⟨235253, by rfl⟩ : syracuseStep 313671 = 470507) B470507
theorem B1198583 : Blo 311834 1198583 := bstep (se 1 (by rfl) ⟨898937, by rfl⟩ : syracuseStep 1198583 = 1797875) B1797875
theorem B314223 : Blo 311834 314223 := bstep (se 1 (by rfl) ⟨235667, by rfl⟩ : syracuseStep 314223 = 471335) B471335
theorem B314279 : Blo 311834 314279 := bstep (se 1 (by rfl) ⟨235709, by rfl⟩ : syracuseStep 314279 = 471419) B471419
theorem B314471 : Blo 311834 314471 := bstep (se 1 (by rfl) ⟨235853, by rfl⟩ : syracuseStep 314471 = 471707) B471707
theorem B314495 : Blo 311834 314495 := bstep (se 1 (by rfl) ⟨235871, by rfl⟩ : syracuseStep 314495 = 471743) B471743
theorem B314607 : Blo 311834 314607 := bstep (se 1 (by rfl) ⟨235955, by rfl⟩ : syracuseStep 314607 = 471911) B471911
theorem B707849 : Blo 311834 707849 := bstep (se 2 (by rfl) ⟨265443, by rfl⟩ : syracuseStep 707849 = 530887) B530887
theorem B315711 : Blo 311834 315711 := bstep (se 1 (by rfl) ⟨236783, by rfl⟩ : syracuseStep 315711 = 473567) B473567
theorem B315719 : Blo 311834 315719 := bstep (se 1 (by rfl) ⟨236789, by rfl⟩ : syracuseStep 315719 = 473579) B473579
theorem B1594727 : Blo 311834 1594727 := bstep (se 1 (by rfl) ⟨1196045, by rfl⟩ : syracuseStep 1594727 = 2392091) B2392091
theorem B1694317 : Blo 311834 1694317 := bstep (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) B635369
theorem B2153785 : Blo 311834 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B4284743 : Blo 311834 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B12805775 : Blo 311834 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B3795083 : Blo 311834 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B355099 : Blo 311834 355099 := bstep (se 1 (by rfl) ⟨266324, by rfl⟩ : syracuseStep 355099 = 532649) B532649
theorem B1503791 : Blo 311834 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B20542481 : Blo 311834 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B2389175 : Blo 311834 2389175 := bstep (se 1 (by rfl) ⟨1791881, by rfl⟩ : syracuseStep 2389175 = 3583763) B3583763
theorem B1898909 : Blo 311834 1898909 := bstep (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) B712091
theorem B4030505 : Blo 311834 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B1705951 : Blo 311834 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B526439 : Blo 311834 526439 := bstep (se 1 (by rfl) ⟨394829, by rfl⟩ : syracuseStep 526439 = 789659) B789659
theorem B396571 : Blo 311834 396571 := bstep (se 1 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 396571 = 594857) B594857
theorem B2530055 : Blo 311834 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B793577 : Blo 311834 793577 := bstep (se 2 (by rfl) ⟨297591, by rfl⟩ : syracuseStep 793577 = 595183) B595183
theorem B1581119 : Blo 311834 1581119 := bstep (se 1 (by rfl) ⟨1185839, by rfl⟩ : syracuseStep 1581119 = 2371679) B2371679
theorem B1057103 : Blo 311834 1057103 := bstep (se 1 (by rfl) ⟨792827, by rfl⟩ : syracuseStep 1057103 = 1585655) B1585655
theorem B1188695 : Blo 311834 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B1058345 : Blo 311834 1058345 := bstep (se 2 (by rfl) ⟨396879, by rfl⟩ : syracuseStep 1058345 = 793759) B793759
theorem B1190335 : Blo 311834 1190335 := bstep (se 1 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 1190335 = 1785503) B1785503
theorem B799055 : Blo 311834 799055 := bstep (se 1 (by rfl) ⟨599291, by rfl⟩ : syracuseStep 799055 = 1198583) B1198583
theorem B17216063 : Blo 311834 17216063 := bstep (se 1 (by rfl) ⟨12912047, by rfl⟩ : syracuseStep 17216063 = 25824095) B25824095
theorem B471899 : Blo 311834 471899 := bstep (se 1 (by rfl) ⟨353924, by rfl⟩ : syracuseStep 471899 = 707849) B707849
theorem B1063151 : Blo 311834 1063151 := bstep (se 1 (by rfl) ⟨797363, by rfl⟩ : syracuseStep 1063151 = 1594727) B1594727
theorem B473465 : Blo 311834 473465 := bstep (se 2 (by rfl) ⟨177549, by rfl⟩ : syracuseStep 473465 = 355099) B355099
theorem B1097371 : Blo 311834 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B704159 : Blo 311834 704159 := bstep (se 1 (by rfl) ⟨528119, by rfl⟩ : syracuseStep 704159 = 1056239) B1056239
theorem B1196153 : Blo 311834 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B1590353 : Blo 311834 1590353 := bstep (se 2 (by rfl) ⟨596382, by rfl⟩ : syracuseStep 1590353 = 1192765) B1192765
theorem B8537183 : Blo 311834 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B707039 : Blo 311834 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B314303 : Blo 311834 314303 := bstep (se 1 (by rfl) ⟨235727, by rfl⟩ : syracuseStep 314303 = 471455) B471455
theorem B1002527 : Blo 311834 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B1592783 : Blo 311834 1592783 := bstep (se 1 (by rfl) ⟨1194587, by rfl⟩ : syracuseStep 1592783 = 2389175) B2389175
theorem B314863 : Blo 311834 314863 := bstep (se 1 (by rfl) ⟨236147, by rfl⟩ : syracuseStep 314863 = 472295) B472295
theorem B3001967 : Blo 311834 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B708857 : Blo 311834 708857 := bstep (se 2 (by rfl) ⟨265821, by rfl⟩ : syracuseStep 708857 = 531643) B531643
theorem B1265939 : Blo 311834 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B708947 : Blo 311834 708947 := bstep (se 1 (by rfl) ⟨531710, by rfl⟩ : syracuseStep 708947 = 1063421) B1063421
theorem B2871713 : Blo 311834 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B34527059 : Blo 311834 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B45703925 : Blo 311834 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B1009871 : Blo 311834 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B6909887 : Blo 311834 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B357223 : Blo 311834 357223 := bstep (se 1 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 357223 = 535835) B535835
theorem B751607 : Blo 311834 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B13694987 : Blo 311834 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B2259089 : Blo 311834 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B1014727 : Blo 311834 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B2687003 : Blo 311834 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B2001311 : Blo 311834 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B528761 : Blo 311834 528761 := bstep (se 2 (by rfl) ⟨198285, by rfl⟩ : syracuseStep 528761 = 396571) B396571
theorem B529051 : Blo 311834 529051 := bstep (se 1 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 529051 = 793577) B793577
theorem B1054079 : Blo 311834 1054079 := bstep (se 1 (by rfl) ⟨790559, by rfl⟩ : syracuseStep 1054079 = 1581119) B1581119
theorem B792463 : Blo 311834 792463 := bstep (se 1 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 792463 = 1188695) B1188695
theorem B532703 : Blo 311834 532703 := bstep (se 1 (by rfl) ⟨399527, by rfl⟩ : syracuseStep 532703 = 799055) B799055
theorem B11477375 : Blo 311834 11477375 := bstep (se 1 (by rfl) ⟨8608031, by rfl⟩ : syracuseStep 11477375 = 17216063) B17216063
theorem B1352969 : Blo 311834 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B501071 : Blo 311834 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B469439 : Blo 311834 469439 := bstep (se 1 (by rfl) ⟨352079, by rfl⟩ : syracuseStep 469439 = 704159) B704159
theorem B18426365 : Blo 311834 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B797435 : Blo 311834 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B1060235 : Blo 311834 1060235 := bstep (se 1 (by rfl) ⟨795176, by rfl⟩ : syracuseStep 1060235 = 1590353) B1590353
theorem B471359 : Blo 311834 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B668351 : Blo 311834 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B1061855 : Blo 311834 1061855 := bstep (se 1 (by rfl) ⟨796391, by rfl⟩ : syracuseStep 1061855 = 1592783) B1592783
theorem B2274601 : Blo 311834 2274601 := bstep (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) B1705951
theorem B472571 : Blo 311834 472571 := bstep (se 1 (by rfl) ⟨354428, by rfl⟩ : syracuseStep 472571 = 708857) B708857
theorem B472631 : Blo 311834 472631 := bstep (se 1 (by rfl) ⟨354473, by rfl⟩ : syracuseStep 472631 = 708947) B708947
theorem B1914475 : Blo 311834 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B1587113 : Blo 311834 1587113 := bstep (se 2 (by rfl) ⟨595167, by rfl⟩ : syracuseStep 1587113 = 1190335) B1190335
theorem B23018039 : Blo 311834 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B704735 : Blo 311834 704735 := bstep (se 1 (by rfl) ⟨528551, by rfl⟩ : syracuseStep 704735 = 1057103) B1057103
theorem B705563 : Blo 311834 705563 := bstep (se 1 (by rfl) ⟨529172, by rfl⟩ : syracuseStep 705563 = 1058345) B1058345
theorem B476297 : Blo 311834 476297 := bstep (se 2 (by rfl) ⟨178611, by rfl⟩ : syracuseStep 476297 = 357223) B357223
theorem B673247 : Blo 311834 673247 := bstep (se 1 (by rfl) ⟨504935, by rfl⟩ : syracuseStep 673247 = 1009871) B1009871
theorem B314599 : Blo 311834 314599 := bstep (se 1 (by rfl) ⟨235949, by rfl⟩ : syracuseStep 314599 = 471899) B471899
theorem B5852645 : Blo 311834 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B9129991 : Blo 311834 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B708767 : Blo 311834 708767 := bstep (se 1 (by rfl) ⟨531575, by rfl⟩ : syracuseStep 708767 = 1063151) B1063151
theorem B315643 : Blo 311834 315643 := bstep (se 1 (by rfl) ⟨236732, by rfl⟩ : syracuseStep 315643 = 473465) B473465
theorem B5691455 : Blo 311834 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B350959 : Blo 311834 350959 := bstep (se 1 (by rfl) ⟨263219, by rfl⟩ : syracuseStep 350959 = 526439) B526439
theorem B843959 : Blo 311834 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B30469283 : Blo 311834 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B6746813 : Blo 311834 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B1506059 : Blo 311834 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B3901763 : Blo 311834 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B562639 : Blo 311834 562639 := bstep (se 1 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 562639 = 843959) B843959
theorem B531623 : Blo 311834 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B1056617 : Blo 311834 1056617 := bstep (se 2 (by rfl) ⟨396231, by rfl⟩ : syracuseStep 1056617 = 792463) B792463
theorem B4497875 : Blo 311834 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B467945 : Blo 311834 467945 := bstep (se 2 (by rfl) ⟨175479, by rfl⟩ : syracuseStep 467945 = 350959) B350959
theorem B1058075 : Blo 311834 1058075 := bstep (se 1 (by rfl) ⟨793556, by rfl⟩ : syracuseStep 1058075 = 1587113) B1587113
theorem B15345359 : Blo 311834 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B469823 : Blo 311834 469823 := bstep (se 1 (by rfl) ⟨352367, by rfl⟩ : syracuseStep 469823 = 704735) B704735
theorem B470375 : Blo 311834 470375 := bstep (se 1 (by rfl) ⟨352781, by rfl⟩ : syracuseStep 470375 = 705563) B705563
theorem B1782269 : Blo 311834 1782269 := bstep (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) B668351
theorem B472511 : Blo 311834 472511 := bstep (se 1 (by rfl) ⟨354383, by rfl⟩ : syracuseStep 472511 = 708767) B708767
theorem B702719 : Blo 311834 702719 := bstep (se 1 (by rfl) ⟨527039, by rfl⟩ : syracuseStep 702719 = 1054079) B1054079
theorem B12173321 : Blo 311834 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B7651583 : Blo 311834 7651583 := bstep (se 1 (by rfl) ⟨5738687, by rfl⟩ : syracuseStep 7651583 = 11477375) B11477375
theorem B901979 : Blo 311834 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B705401 : Blo 311834 705401 := bstep (se 2 (by rfl) ⟨264525, by rfl⟩ : syracuseStep 705401 = 529051) B529051
theorem B312959 : Blo 311834 312959 := bstep (se 1 (by rfl) ⟨234719, by rfl⟩ : syracuseStep 312959 = 469439) B469439
theorem B3032801 : Blo 311834 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B706823 : Blo 311834 706823 := bstep (se 1 (by rfl) ⟨530117, by rfl⟩ : syracuseStep 706823 = 1060235) B1060235
theorem B314239 : Blo 311834 314239 := bstep (se 1 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 314239 = 471359) B471359
theorem B707903 : Blo 311834 707903 := bstep (se 1 (by rfl) ⟨530927, by rfl⟩ : syracuseStep 707903 = 1061855) B1061855
theorem B315047 : Blo 311834 315047 := bstep (se 1 (by rfl) ⟨236285, by rfl⟩ : syracuseStep 315047 = 472571) B472571
theorem B315087 : Blo 311834 315087 := bstep (se 1 (by rfl) ⟨236315, by rfl⟩ : syracuseStep 315087 = 472631) B472631
theorem B1004039 : Blo 311834 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B1791335 : Blo 311834 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B317531 : Blo 311834 317531 := bstep (se 1 (by rfl) ⟨238148, by rfl⟩ : syracuseStep 317531 = 476297) B476297
theorem B448831 : Blo 311834 448831 := bstep (se 1 (by rfl) ⟨336623, by rfl⟩ : syracuseStep 448831 = 673247) B673247
theorem B1334207 : Blo 311834 1334207 := bstep (se 1 (by rfl) ⟨1000655, by rfl⟩ : syracuseStep 1334207 = 2001311) B2001311
theorem B352507 : Blo 311834 352507 := bstep (se 1 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 352507 = 528761) B528761
theorem B1336189 : Blo 311834 1336189 := bstep (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) B501071
theorem B3794303 : Blo 311834 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B355135 : Blo 311834 355135 := bstep (se 1 (by rfl) ⟨266351, by rfl⟩ : syracuseStep 355135 = 532703) B532703
theorem B12284243 : Blo 311834 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B20312855 : Blo 311834 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B2552633 : Blo 311834 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B889471 : Blo 311834 889471 := bstep (se 1 (by rfl) ⟨667103, by rfl⟩ : syracuseStep 889471 = 1334207) B1334207
theorem B10230239 : Blo 311834 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B1188179 : Blo 311834 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B598441 : Blo 311834 598441 := bstep (se 2 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 598441 = 448831) B448831
theorem B13541903 : Blo 311834 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B468479 : Blo 311834 468479 := bstep (se 1 (by rfl) ⟨351359, by rfl⟩ : syracuseStep 468479 = 702719) B702719
theorem B470009 : Blo 311834 470009 := bstep (se 2 (by rfl) ⟨176253, by rfl⟩ : syracuseStep 470009 = 352507) B352507
theorem B601319 : Blo 311834 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B470267 : Blo 311834 470267 := bstep (se 1 (by rfl) ⟨352700, by rfl⟩ : syracuseStep 470267 = 705401) B705401
theorem B1781585 : Blo 311834 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B471215 : Blo 311834 471215 := bstep (se 1 (by rfl) ⟨353411, by rfl⟩ : syracuseStep 471215 = 706823) B706823
theorem B2601175 : Blo 311834 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B471935 : Blo 311834 471935 := bstep (se 1 (by rfl) ⟨353951, by rfl⟩ : syracuseStep 471935 = 707903) B707903
theorem B669359 : Blo 311834 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B1194223 : Blo 311834 1194223 := bstep (se 1 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 1194223 = 1791335) B1791335
theorem B473513 : Blo 311834 473513 := bstep (se 2 (by rfl) ⟨177567, by rfl⟩ : syracuseStep 473513 = 355135) B355135
theorem B704411 : Blo 311834 704411 := bstep (se 1 (by rfl) ⟨528308, by rfl⟩ : syracuseStep 704411 = 1056617) B1056617
theorem B2998583 : Blo 311834 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B311963 : Blo 311834 311963 := bstep (se 1 (by rfl) ⟨233972, by rfl⟩ : syracuseStep 311963 = 467945) B467945
theorem B705383 : Blo 311834 705383 := bstep (se 1 (by rfl) ⟨529037, by rfl⟩ : syracuseStep 705383 = 1058075) B1058075
theorem B313215 : Blo 311834 313215 := bstep (se 1 (by rfl) ⟨234911, by rfl⟩ : syracuseStep 313215 = 469823) B469823
theorem B313583 : Blo 311834 313583 := bstep (se 1 (by rfl) ⟨235187, by rfl⟩ : syracuseStep 313583 = 470375) B470375
theorem B315007 : Blo 311834 315007 := bstep (se 1 (by rfl) ⟨236255, by rfl⟩ : syracuseStep 315007 = 472511) B472511
theorem B8115547 : Blo 311834 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B5101055 : Blo 311834 5101055 := bstep (se 1 (by rfl) ⟨3825791, by rfl⟩ : syracuseStep 5101055 = 7651583) B7651583
theorem B2021867 : Blo 311834 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B10118141 : Blo 311834 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B354415 : Blo 311834 354415 := bstep (se 1 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 354415 = 531623) B531623
theorem B846749 : Blo 311834 846749 := bstep (se 3 (by rfl) ⟨158765, by rfl⟩ : syracuseStep 846749 = 317531) B317531
theorem B750185 : Blo 311834 750185 := bstep (se 2 (by rfl) ⟨281319, by rfl⟩ : syracuseStep 750185 = 562639) B562639
theorem B8189495 : Blo 311834 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B1701755 : Blo 311834 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B1999055 : Blo 311834 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B1347911 : Blo 311834 1347911 := bstep (se 1 (by rfl) ⟨1010933, by rfl⟩ : syracuseStep 1347911 = 2021867) B2021867
theorem B792119 : Blo 311834 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B1185961 : Blo 311834 1185961 := bstep (se 2 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 1185961 = 889471) B889471
theorem B10820729 : Blo 311834 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B564499 : Blo 311834 564499 := bstep (se 1 (by rfl) ⟨423374, by rfl⟩ : syracuseStep 564499 = 846749) B846749
theorem B400879 : Blo 311834 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B1187723 : Blo 311834 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B500123 : Blo 311834 500123 := bstep (se 1 (by rfl) ⟨375092, by rfl⟩ : syracuseStep 500123 = 750185) B750185
theorem B469607 : Blo 311834 469607 := bstep (se 1 (by rfl) ⟨352205, by rfl⟩ : syracuseStep 469607 = 704411) B704411
theorem B797921 : Blo 311834 797921 := bstep (se 2 (by rfl) ⟨299220, by rfl⟩ : syracuseStep 797921 = 598441) B598441
theorem B470255 : Blo 311834 470255 := bstep (se 1 (by rfl) ⟨352691, by rfl⟩ : syracuseStep 470255 = 705383) B705383
theorem B472553 : Blo 311834 472553 := bstep (se 2 (by rfl) ⟨177207, by rfl⟩ : syracuseStep 472553 = 354415) B354415
theorem B9027935 : Blo 311834 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B312319 : Blo 311834 312319 := bstep (se 1 (by rfl) ⟨234239, by rfl⟩ : syracuseStep 312319 = 468479) B468479
theorem B27280637 : Blo 311834 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B313339 : Blo 311834 313339 := bstep (se 1 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 313339 = 470009) B470009
theorem B313511 : Blo 311834 313511 := bstep (se 1 (by rfl) ⟨235133, by rfl⟩ : syracuseStep 313511 = 470267) B470267
theorem B314143 : Blo 311834 314143 := bstep (se 1 (by rfl) ⟨235607, by rfl⟩ : syracuseStep 314143 = 471215) B471215
theorem B1592297 : Blo 311834 1592297 := bstep (se 2 (by rfl) ⟨597111, by rfl⟩ : syracuseStep 1592297 = 1194223) B1194223
theorem B314623 : Blo 311834 314623 := bstep (se 1 (by rfl) ⟨235967, by rfl⟩ : syracuseStep 314623 = 471935) B471935
theorem B5459663 : Blo 311834 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B446239 : Blo 311834 446239 := bstep (se 1 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 446239 = 669359) B669359
theorem B1134503 : Blo 311834 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B315675 : Blo 311834 315675 := bstep (se 1 (by rfl) ⟨236756, by rfl⟩ : syracuseStep 315675 = 473513) B473513
theorem B3400703 : Blo 311834 3400703 := bstep (se 1 (by rfl) ⟨2550527, by rfl⟩ : syracuseStep 3400703 = 5101055) B5101055
theorem B3468233 : Blo 311834 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B6745427 : Blo 311834 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B18187091 : Blo 311834 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B756335 : Blo 311834 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B528079 : Blo 311834 528079 := bstep (se 1 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 528079 = 792119) B792119
theorem B7213819 : Blo 311834 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B791815 : Blo 311834 791815 := bstep (se 1 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 791815 = 1187723) B1187723
theorem B333415 : Blo 311834 333415 := bstep (se 1 (by rfl) ⟨250061, by rfl⟩ : syracuseStep 333415 = 500123) B500123
theorem B2267135 : Blo 311834 2267135 := bstep (se 1 (by rfl) ⟨1700351, by rfl⟩ : syracuseStep 2267135 = 3400703) B3400703
theorem B531947 : Blo 311834 531947 := bstep (se 1 (by rfl) ⟨398960, by rfl⟩ : syracuseStep 531947 = 797921) B797921
theorem B4496951 : Blo 311834 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B2138021 : Blo 311834 2138021 := bstep (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) B400879
theorem B1581281 : Blo 311834 1581281 := bstep (se 2 (by rfl) ⟨592980, by rfl⟩ : syracuseStep 1581281 = 1185961) B1185961
theorem B14559101 : Blo 311834 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B1061531 : Blo 311834 1061531 := bstep (se 1 (by rfl) ⟨796148, by rfl⟩ : syracuseStep 1061531 = 1592297) B1592297
theorem B898607 : Blo 311834 898607 := bstep (se 1 (by rfl) ⟨673955, by rfl⟩ : syracuseStep 898607 = 1347911) B1347911
theorem B313071 : Blo 311834 313071 := bstep (se 1 (by rfl) ⟨234803, by rfl⟩ : syracuseStep 313071 = 469607) B469607
theorem B2312155 : Blo 311834 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B313503 : Blo 311834 313503 := bstep (se 1 (by rfl) ⟨235127, by rfl⟩ : syracuseStep 313503 = 470255) B470255
theorem B315035 : Blo 311834 315035 := bstep (se 1 (by rfl) ⟨236276, by rfl⟩ : syracuseStep 315035 = 472553) B472553
theorem B2379941 : Blo 311834 2379941 := bstep (se 4 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 2379941 = 446239) B446239
theorem B1332703 : Blo 311834 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B6018623 : Blo 311834 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B752665 : Blo 311834 752665 := bstep (se 2 (by rfl) ⟨282249, by rfl⟩ : syracuseStep 752665 = 564499) B564499
theorem B12124727 : Blo 311834 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B3082873 : Blo 311834 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B1511423 : Blo 311834 1511423 := bstep (se 1 (by rfl) ⟨1133567, by rfl⟩ : syracuseStep 1511423 = 2267135) B2267135
theorem B1054187 : Blo 311834 1054187 := bstep (se 1 (by rfl) ⟨790640, by rfl⟩ : syracuseStep 1054187 = 1581281) B1581281
theorem B9706067 : Blo 311834 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B1055753 : Blo 311834 1055753 := bstep (se 2 (by rfl) ⟨395907, by rfl⟩ : syracuseStep 1055753 = 791815) B791815
theorem B1776937 : Blo 311834 1776937 := bstep (se 2 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 1776937 = 1332703) B1332703
theorem B1778213 : Blo 311834 1778213 := bstep (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) B333415
theorem B599071 : Blo 311834 599071 := bstep (se 1 (by rfl) ⟨449303, by rfl⟩ : syracuseStep 599071 = 898607) B898607
theorem B1586627 : Blo 311834 1586627 := bstep (se 1 (by rfl) ⟨1189970, by rfl⟩ : syracuseStep 1586627 = 2379941) B2379941
theorem B4012415 : Blo 311834 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B704105 : Blo 311834 704105 := bstep (se 2 (by rfl) ⟨264039, by rfl⟩ : syracuseStep 704105 = 528079) B528079
theorem B2997967 : Blo 311834 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B1425347 : Blo 311834 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B9618425 : Blo 311834 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B2016893 : Blo 311834 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B707687 : Blo 311834 707687 := bstep (se 1 (by rfl) ⟨530765, by rfl⟩ : syracuseStep 707687 = 1061531) B1061531
theorem B1003553 : Blo 311834 1003553 := bstep (se 2 (by rfl) ⟨376332, by rfl⟩ : syracuseStep 1003553 = 752665) B752665
theorem B354631 : Blo 311834 354631 := bstep (se 1 (by rfl) ⟨265973, by rfl⟩ : syracuseStep 354631 = 531947) B531947
theorem B1344595 : Blo 311834 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B1185475 : Blo 311834 1185475 := bstep (se 1 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 1185475 = 1778213) B1778213
theorem B1057751 : Blo 311834 1057751 := bstep (se 1 (by rfl) ⟨793313, by rfl⟩ : syracuseStep 1057751 = 1586627) B1586627
theorem B2369249 : Blo 311834 2369249 := bstep (se 2 (by rfl) ⟨888468, by rfl⟩ : syracuseStep 2369249 = 1776937) B1776937
theorem B469403 : Blo 311834 469403 := bstep (se 1 (by rfl) ⟨352052, by rfl⟩ : syracuseStep 469403 = 704105) B704105
theorem B798761 : Blo 311834 798761 := bstep (se 2 (by rfl) ⟨299535, by rfl⟩ : syracuseStep 798761 = 599071) B599071
theorem B471791 : Blo 311834 471791 := bstep (se 1 (by rfl) ⟨353843, by rfl⟩ : syracuseStep 471791 = 707687) B707687
theorem B669035 : Blo 311834 669035 := bstep (se 1 (by rfl) ⟨501776, by rfl⟩ : syracuseStep 669035 = 1003553) B1003553
theorem B472841 : Blo 311834 472841 := bstep (se 2 (by rfl) ⟨177315, by rfl⟩ : syracuseStep 472841 = 354631) B354631
theorem B4110497 : Blo 311834 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B702791 : Blo 311834 702791 := bstep (se 1 (by rfl) ⟨527093, by rfl⟩ : syracuseStep 702791 = 1054187) B1054187
theorem B6470711 : Blo 311834 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B703835 : Blo 311834 703835 := bstep (se 1 (by rfl) ⟨527876, by rfl⟩ : syracuseStep 703835 = 1055753) B1055753
theorem B2674943 : Blo 311834 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B8083151 : Blo 311834 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B6412283 : Blo 311834 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B1007615 : Blo 311834 1007615 := bstep (se 1 (by rfl) ⟨755711, by rfl⟩ : syracuseStep 1007615 = 1511423) B1511423
theorem B3997289 : Blo 311834 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B950231 : Blo 311834 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B1579499 : Blo 311834 1579499 := bstep (se 1 (by rfl) ⟨1184624, by rfl⟩ : syracuseStep 1579499 = 2369249) B2369249
theorem B1580633 : Blo 311834 1580633 := bstep (se 2 (by rfl) ⟨592737, by rfl⟩ : syracuseStep 1580633 = 1185475) B1185475
theorem B532507 : Blo 311834 532507 := bstep (se 1 (by rfl) ⟨399380, by rfl⟩ : syracuseStep 532507 = 798761) B798761
theorem B468527 : Blo 311834 468527 := bstep (se 1 (by rfl) ⟨351395, by rfl⟩ : syracuseStep 468527 = 702791) B702791
theorem B469223 : Blo 311834 469223 := bstep (se 1 (by rfl) ⟨351917, by rfl⟩ : syracuseStep 469223 = 703835) B703835
theorem B2664859 : Blo 311834 2664859 := bstep (se 1 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 2664859 = 3997289) B3997289
theorem B2533949 : Blo 311834 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B1783295 : Blo 311834 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B5388767 : Blo 311834 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B4274855 : Blo 311834 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B671743 : Blo 311834 671743 := bstep (se 1 (by rfl) ⟨503807, by rfl⟩ : syracuseStep 671743 = 1007615) B1007615
theorem B705167 : Blo 311834 705167 := bstep (se 1 (by rfl) ⟨528875, by rfl⟩ : syracuseStep 705167 = 1057751) B1057751
theorem B312935 : Blo 311834 312935 := bstep (se 1 (by rfl) ⟨234701, by rfl⟩ : syracuseStep 312935 = 469403) B469403
theorem B314527 : Blo 311834 314527 := bstep (se 1 (by rfl) ⟨235895, by rfl⟩ : syracuseStep 314527 = 471791) B471791
theorem B446023 : Blo 311834 446023 := bstep (se 1 (by rfl) ⟨334517, by rfl⟩ : syracuseStep 446023 = 669035) B669035
theorem B315227 : Blo 311834 315227 := bstep (se 1 (by rfl) ⟨236420, by rfl⟩ : syracuseStep 315227 = 472841) B472841
theorem B2740331 : Blo 311834 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B4313807 : Blo 311834 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B1792793 : Blo 311834 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B1052999 : Blo 311834 1052999 := bstep (se 1 (by rfl) ⟨789749, by rfl⟩ : syracuseStep 1052999 = 1579499) B1579499
theorem B594697 : Blo 311834 594697 := bstep (se 2 (by rfl) ⟨223011, by rfl⟩ : syracuseStep 594697 = 446023) B446023
theorem B1053755 : Blo 311834 1053755 := bstep (se 1 (by rfl) ⟨790316, by rfl⟩ : syracuseStep 1053755 = 1580633) B1580633
theorem B1188863 : Blo 311834 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B895657 : Blo 311834 895657 := bstep (se 2 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 895657 = 671743) B671743
theorem B470111 : Blo 311834 470111 := bstep (se 1 (by rfl) ⟨352583, by rfl⟩ : syracuseStep 470111 = 705167) B705167
theorem B3553145 : Blo 311834 3553145 := bstep (se 2 (by rfl) ⟨1332429, by rfl⟩ : syracuseStep 3553145 = 2664859) B2664859
theorem B1195195 : Blo 311834 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B312351 : Blo 311834 312351 := bstep (se 1 (by rfl) ⟨234263, by rfl⟩ : syracuseStep 312351 = 468527) B468527
theorem B312815 : Blo 311834 312815 := bstep (se 1 (by rfl) ⟨234611, by rfl⟩ : syracuseStep 312815 = 469223) B469223
theorem B1689299 : Blo 311834 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B3592511 : Blo 311834 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B710009 : Blo 311834 710009 := bstep (se 2 (by rfl) ⟨266253, by rfl⟩ : syracuseStep 710009 = 532507) B532507
theorem B1826887 : Blo 311834 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B2875871 : Blo 311834 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B2849903 : Blo 311834 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B7668989 : Blo 311834 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B2395007 : Blo 311834 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B792575 : Blo 311834 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B792929 : Blo 311834 792929 := bstep (se 2 (by rfl) ⟨297348, by rfl⟩ : syracuseStep 792929 = 594697) B594697
theorem B2368763 : Blo 311834 2368763 := bstep (se 1 (by rfl) ⟨1776572, by rfl⟩ : syracuseStep 2368763 = 3553145) B3553145
theorem B2435849 : Blo 311834 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B1126199 : Blo 311834 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B701999 : Blo 311834 701999 := bstep (se 1 (by rfl) ⟨526499, by rfl⟩ : syracuseStep 701999 = 1052999) B1052999
theorem B702503 : Blo 311834 702503 := bstep (se 1 (by rfl) ⟨526877, by rfl⟩ : syracuseStep 702503 = 1053755) B1053755
theorem B1194209 : Blo 311834 1194209 := bstep (se 2 (by rfl) ⟨447828, by rfl⟩ : syracuseStep 1194209 = 895657) B895657
theorem B473339 : Blo 311834 473339 := bstep (se 1 (by rfl) ⟨355004, by rfl⟩ : syracuseStep 473339 = 710009) B710009
theorem B313407 : Blo 311834 313407 := bstep (se 1 (by rfl) ⟨235055, by rfl⟩ : syracuseStep 313407 = 470111) B470111
theorem B1593593 : Blo 311834 1593593 := bstep (se 2 (by rfl) ⟨597597, by rfl⟩ : syracuseStep 1593593 = 1195195) B1195195
theorem B1899935 : Blo 311834 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B5112659 : Blo 311834 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B528383 : Blo 311834 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B528619 : Blo 311834 528619 := bstep (se 1 (by rfl) ⟨396464, by rfl⟩ : syracuseStep 528619 = 792929) B792929
theorem B1579175 : Blo 311834 1579175 := bstep (se 1 (by rfl) ⟨1184381, by rfl⟩ : syracuseStep 1579175 = 2368763) B2368763
theorem B467999 : Blo 311834 467999 := bstep (se 1 (by rfl) ⟨350999, by rfl⟩ : syracuseStep 467999 = 701999) B701999
theorem B468335 : Blo 311834 468335 := bstep (se 1 (by rfl) ⟨351251, by rfl⟩ : syracuseStep 468335 = 702503) B702503
theorem B796139 : Blo 311834 796139 := bstep (se 1 (by rfl) ⟨597104, by rfl⟩ : syracuseStep 796139 = 1194209) B1194209
theorem B1062395 : Blo 311834 1062395 := bstep (se 1 (by rfl) ⟨796796, by rfl⟩ : syracuseStep 1062395 = 1593593) B1593593
theorem B1623899 : Blo 311834 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B315559 : Blo 311834 315559 := bstep (se 1 (by rfl) ⟨236669, by rfl⟩ : syracuseStep 315559 = 473339) B473339
theorem B1266623 : Blo 311834 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B1596671 : Blo 311834 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B750799 : Blo 311834 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B13633757 : Blo 311834 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B1052783 : Blo 311834 1052783 := bstep (se 1 (by rfl) ⟨789587, by rfl⟩ : syracuseStep 1052783 = 1579175) B1579175
theorem B4330397 : Blo 311834 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B530759 : Blo 311834 530759 := bstep (se 1 (by rfl) ⟨398069, by rfl⟩ : syracuseStep 530759 = 796139) B796139
theorem B4004261 : Blo 311834 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B1064447 : Blo 311834 1064447 := bstep (se 1 (by rfl) ⟨798335, by rfl⟩ : syracuseStep 1064447 = 1596671) B1596671
theorem B704825 : Blo 311834 704825 := bstep (se 2 (by rfl) ⟨264309, by rfl⟩ : syracuseStep 704825 = 528619) B528619
theorem B311999 : Blo 311834 311999 := bstep (se 1 (by rfl) ⟨233999, by rfl⟩ : syracuseStep 311999 = 467999) B467999
theorem B312223 : Blo 311834 312223 := bstep (se 1 (by rfl) ⟨234167, by rfl⟩ : syracuseStep 312223 = 468335) B468335
theorem B708263 : Blo 311834 708263 := bstep (se 1 (by rfl) ⟨531197, by rfl⟩ : syracuseStep 708263 = 1062395) B1062395
theorem B352255 : Blo 311834 352255 := bstep (se 1 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 352255 = 528383) B528383
theorem B844415 : Blo 311834 844415 := bstep (se 1 (by rfl) ⟨633311, by rfl⟩ : syracuseStep 844415 = 1266623) B1266623
theorem B2886931 : Blo 311834 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B562943 : Blo 311834 562943 := bstep (se 1 (by rfl) ⟨422207, by rfl⟩ : syracuseStep 562943 = 844415) B844415
theorem B469673 : Blo 311834 469673 := bstep (se 2 (by rfl) ⟨176127, by rfl⟩ : syracuseStep 469673 = 352255) B352255
theorem B469883 : Blo 311834 469883 := bstep (se 1 (by rfl) ⟨352412, by rfl⟩ : syracuseStep 469883 = 704825) B704825
theorem B9089171 : Blo 311834 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B472175 : Blo 311834 472175 := bstep (se 1 (by rfl) ⟨354131, by rfl⟩ : syracuseStep 472175 = 708263) B708263
theorem B701855 : Blo 311834 701855 := bstep (se 1 (by rfl) ⟨526391, by rfl⟩ : syracuseStep 701855 = 1052783) B1052783
theorem B2669507 : Blo 311834 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B709631 : Blo 311834 709631 := bstep (se 1 (by rfl) ⟨532223, by rfl⟩ : syracuseStep 709631 = 1064447) B1064447
theorem B353839 : Blo 311834 353839 := bstep (se 1 (by rfl) ⟨265379, by rfl⟩ : syracuseStep 353839 = 530759) B530759
theorem B467903 : Blo 311834 467903 := bstep (se 1 (by rfl) ⟨350927, by rfl⟩ : syracuseStep 467903 = 701855) B701855
theorem B1779671 : Blo 311834 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B471785 : Blo 311834 471785 := bstep (se 2 (by rfl) ⟨176919, by rfl⟩ : syracuseStep 471785 = 353839) B353839
theorem B473087 : Blo 311834 473087 := bstep (se 1 (by rfl) ⟨354815, by rfl⟩ : syracuseStep 473087 = 709631) B709631
theorem B375295 : Blo 311834 375295 := bstep (se 1 (by rfl) ⟨281471, by rfl⟩ : syracuseStep 375295 = 562943) B562943
theorem B3849241 : Blo 311834 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B313115 : Blo 311834 313115 := bstep (se 1 (by rfl) ⟨234836, by rfl⟩ : syracuseStep 313115 = 469673) B469673
theorem B313255 : Blo 311834 313255 := bstep (se 1 (by rfl) ⟨234941, by rfl⟩ : syracuseStep 313255 = 469883) B469883
theorem B314783 : Blo 311834 314783 := bstep (se 1 (by rfl) ⟨236087, by rfl⟩ : syracuseStep 314783 = 472175) B472175
theorem B6059447 : Blo 311834 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B1186447 : Blo 311834 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B500393 : Blo 311834 500393 := bstep (se 2 (by rfl) ⟨187647, by rfl⟩ : syracuseStep 500393 = 375295) B375295
theorem B4039631 : Blo 311834 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B311935 : Blo 311834 311935 := bstep (se 1 (by rfl) ⟨233951, by rfl⟩ : syracuseStep 311935 = 467903) B467903
theorem B314523 : Blo 311834 314523 := bstep (se 1 (by rfl) ⟨235892, by rfl⟩ : syracuseStep 314523 = 471785) B471785
theorem B315391 : Blo 311834 315391 := bstep (se 1 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 315391 = 473087) B473087
theorem B5132321 : Blo 311834 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B333595 : Blo 311834 333595 := bstep (se 1 (by rfl) ⟨250196, by rfl⟩ : syracuseStep 333595 = 500393) B500393
theorem B2693087 : Blo 311834 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B1581929 : Blo 311834 1581929 := bstep (se 2 (by rfl) ⟨593223, by rfl⟩ : syracuseStep 1581929 = 1186447) B1186447
theorem B3421547 : Blo 311834 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1054619 : Blo 311834 1054619 := bstep (se 1 (by rfl) ⟨790964, by rfl⟩ : syracuseStep 1054619 = 1581929) B1581929
theorem B444793 : Blo 311834 444793 := bstep (se 2 (by rfl) ⟨166797, by rfl⟩ : syracuseStep 444793 = 333595) B333595
theorem B2281031 : Blo 311834 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B1795391 : Blo 311834 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B593057 : Blo 311834 593057 := bstep (se 2 (by rfl) ⟨222396, by rfl⟩ : syracuseStep 593057 = 444793) B444793
theorem B1520687 : Blo 311834 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B703079 : Blo 311834 703079 := bstep (se 1 (by rfl) ⟨527309, by rfl⟩ : syracuseStep 703079 = 1054619) B1054619
theorem B1196927 : Blo 311834 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B395371 : Blo 311834 395371 := bstep (se 1 (by rfl) ⟨296528, by rfl⟩ : syracuseStep 395371 = 593057) B593057
theorem B468719 : Blo 311834 468719 := bstep (se 1 (by rfl) ⟨351539, by rfl⟩ : syracuseStep 468719 = 703079) B703079
theorem B797951 : Blo 311834 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B1013791 : Blo 311834 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B527161 : Blo 311834 527161 := bstep (se 2 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 527161 = 395371) B395371
theorem B531967 : Blo 311834 531967 := bstep (se 1 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 531967 = 797951) B797951
theorem B1351721 : Blo 311834 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B312479 : Blo 311834 312479 := bstep (se 1 (by rfl) ⟨234359, by rfl⟩ : syracuseStep 312479 = 468719) B468719
theorem B702881 : Blo 311834 702881 := bstep (se 2 (by rfl) ⟨263580, by rfl⟩ : syracuseStep 702881 = 527161) B527161
theorem B901147 : Blo 311834 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B709289 : Blo 311834 709289 := bstep (se 2 (by rfl) ⟨265983, by rfl⟩ : syracuseStep 709289 = 531967) B531967
theorem B468587 : Blo 311834 468587 := bstep (se 1 (by rfl) ⟨351440, by rfl⟩ : syracuseStep 468587 = 702881) B702881
theorem B472859 : Blo 311834 472859 := bstep (se 1 (by rfl) ⟨354644, by rfl⟩ : syracuseStep 472859 = 709289) B709289
theorem B1201529 : Blo 311834 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B801019 : Blo 311834 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B312391 : Blo 311834 312391 := bstep (se 1 (by rfl) ⟨234293, by rfl⟩ : syracuseStep 312391 = 468587) B468587
theorem B315239 : Blo 311834 315239 := bstep (se 1 (by rfl) ⟨236429, by rfl⟩ : syracuseStep 315239 = 472859) B472859
theorem B4272101 : Blo 311834 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B2848067 : Blo 311834 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B1898711 : Blo 311834 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B1265807 : Blo 311834 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B843871 : Blo 311834 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B1125161 : Blo 311834 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B750107 : Blo 311834 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 311834 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B1333523 : Blo 311834 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B3556061 : Blo 311834 3556061 := bstep (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) B1333523
theorem B2370707 : Blo 311834 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B1580471 : Blo 311834 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B1053647 : Blo 311834 1053647 := bstep (se 1 (by rfl) ⟨790235, by rfl⟩ : syracuseStep 1053647 = 1580471) B1580471
theorem B702431 : Blo 311834 702431 := bstep (se 1 (by rfl) ⟨526823, by rfl⟩ : syracuseStep 702431 = 1053647) B1053647
theorem B468287 : Blo 311834 468287 := bstep (se 1 (by rfl) ⟨351215, by rfl⟩ : syracuseStep 468287 = 702431) B702431
theorem B312191 : Blo 311834 312191 := bstep (se 1 (by rfl) ⟨234143, by rfl⟩ : syracuseStep 312191 = 468287) B468287

theorem C0 (j : ℕ) (h1 : 77958 ≤ j) (h2 : j ≤ 78657) : Blo 311834 (4 * j + 3) := by
  interval_cases j
  · exact B311835
  · exact B311839
  · exact B311843
  · exact B311847
  · exact B311851
  · exact B311855
  · exact B311859
  · exact B311863
  · exact B311867
  · exact B311871
  · exact B311875
  · exact B311879
  · exact B311883
  · exact B311887
  · exact B311891
  · exact B311895
  · exact B311899
  · exact B311903
  · exact B311907
  · exact B311911
  · exact B311915
  · exact B311919
  · exact B311923
  · exact B311927
  · exact B311931
  · exact B311935
  · exact B311939
  · exact B311943
  · exact B311947
  · exact B311951
  · exact B311955
  · exact B311959
  · exact B311963
  · exact B311967
  · exact B311971
  · exact B311975
  · exact B311979
  · exact B311983
  · exact B311987
  · exact B311991
  · exact B311995
  · exact B311999
  · exact B312003
  · exact B312007
  · exact B312011
  · exact B312015
  · exact B312019
  · exact B312023
  · exact B312027
  · exact B312031
  · exact B312035
  · exact B312039
  · exact B312043
  · exact B312047
  · exact B312051
  · exact B312055
  · exact B312059
  · exact B312063
  · exact B312067
  · exact B312071
  · exact B312075
  · exact B312079
  · exact B312083
  · exact B312087
  · exact B312091
  · exact B312095
  · exact B312099
  · exact B312103
  · exact B312107
  · exact B312111
  · exact B312115
  · exact B312119
  · exact B312123
  · exact B312127
  · exact B312131
  · exact B312135
  · exact B312139
  · exact B312143
  · exact B312147
  · exact B312151
  · exact B312155
  · exact B312159
  · exact B312163
  · exact B312167
  · exact B312171
  · exact B312175
  · exact B312179
  · exact B312183
  · exact B312187
  · exact B312191
  · exact B312195
  · exact B312199
  · exact B312203
  · exact B312207
  · exact B312211
  · exact B312215
  · exact B312219
  · exact B312223
  · exact B312227
  · exact B312231
  · exact B312235
  · exact B312239
  · exact B312243
  · exact B312247
  · exact B312251
  · exact B312255
  · exact B312259
  · exact B312263
  · exact B312267
  · exact B312271
  · exact B312275
  · exact B312279
  · exact B312283
  · exact B312287
  · exact B312291
  · exact B312295
  · exact B312299
  · exact B312303
  · exact B312307
  · exact B312311
  · exact B312315
  · exact B312319
  · exact B312323
  · exact B312327
  · exact B312331
  · exact B312335
  · exact B312339
  · exact B312343
  · exact B312347
  · exact B312351
  · exact B312355
  · exact B312359
  · exact B312363
  · exact B312367
  · exact B312371
  · exact B312375
  · exact B312379
  · exact B312383
  · exact B312387
  · exact B312391
  · exact B312395
  · exact B312399
  · exact B312403
  · exact B312407
  · exact B312411
  · exact B312415
  · exact B312419
  · exact B312423
  · exact B312427
  · exact B312431
  · exact B312435
  · exact B312439
  · exact B312443
  · exact B312447
  · exact B312451
  · exact B312455
  · exact B312459
  · exact B312463
  · exact B312467
  · exact B312471
  · exact B312475
  · exact B312479
  · exact B312483
  · exact B312487
  · exact B312491
  · exact B312495
  · exact B312499
  · exact B312503
  · exact B312507
  · exact B312511
  · exact B312515
  · exact B312519
  · exact B312523
  · exact B312527
  · exact B312531
  · exact B312535
  · exact B312539
  · exact B312543
  · exact B312547
  · exact B312551
  · exact B312555
  · exact B312559
  · exact B312563
  · exact B312567
  · exact B312571
  · exact B312575
  · exact B312579
  · exact B312583
  · exact B312587
  · exact B312591
  · exact B312595
  · exact B312599
  · exact B312603
  · exact B312607
  · exact B312611
  · exact B312615
  · exact B312619
  · exact B312623
  · exact B312627
  · exact B312631
  · exact B312635
  · exact B312639
  · exact B312643
  · exact B312647
  · exact B312651
  · exact B312655
  · exact B312659
  · exact B312663
  · exact B312667
  · exact B312671
  · exact B312675
  · exact B312679
  · exact B312683
  · exact B312687
  · exact B312691
  · exact B312695
  · exact B312699
  · exact B312703
  · exact B312707
  · exact B312711
  · exact B312715
  · exact B312719
  · exact B312723
  · exact B312727
  · exact B312731
  · exact B312735
  · exact B312739
  · exact B312743
  · exact B312747
  · exact B312751
  · exact B312755
  · exact B312759
  · exact B312763
  · exact B312767
  · exact B312771
  · exact B312775
  · exact B312779
  · exact B312783
  · exact B312787
  · exact B312791
  · exact B312795
  · exact B312799
  · exact B312803
  · exact B312807
  · exact B312811
  · exact B312815
  · exact B312819
  · exact B312823
  · exact B312827
  · exact B312831
  · exact B312835
  · exact B312839
  · exact B312843
  · exact B312847
  · exact B312851
  · exact B312855
  · exact B312859
  · exact B312863
  · exact B312867
  · exact B312871
  · exact B312875
  · exact B312879
  · exact B312883
  · exact B312887
  · exact B312891
  · exact B312895
  · exact B312899
  · exact B312903
  · exact B312907
  · exact B312911
  · exact B312915
  · exact B312919
  · exact B312923
  · exact B312927
  · exact B312931
  · exact B312935
  · exact B312939
  · exact B312943
  · exact B312947
  · exact B312951
  · exact B312955
  · exact B312959
  · exact B312963
  · exact B312967
  · exact B312971
  · exact B312975
  · exact B312979
  · exact B312983
  · exact B312987
  · exact B312991
  · exact B312995
  · exact B312999
  · exact B313003
  · exact B313007
  · exact B313011
  · exact B313015
  · exact B313019
  · exact B313023
  · exact B313027
  · exact B313031
  · exact B313035
  · exact B313039
  · exact B313043
  · exact B313047
  · exact B313051
  · exact B313055
  · exact B313059
  · exact B313063
  · exact B313067
  · exact B313071
  · exact B313075
  · exact B313079
  · exact B313083
  · exact B313087
  · exact B313091
  · exact B313095
  · exact B313099
  · exact B313103
  · exact B313107
  · exact B313111
  · exact B313115
  · exact B313119
  · exact B313123
  · exact B313127
  · exact B313131
  · exact B313135
  · exact B313139
  · exact B313143
  · exact B313147
  · exact B313151
  · exact B313155
  · exact B313159
  · exact B313163
  · exact B313167
  · exact B313171
  · exact B313175
  · exact B313179
  · exact B313183
  · exact B313187
  · exact B313191
  · exact B313195
  · exact B313199
  · exact B313203
  · exact B313207
  · exact B313211
  · exact B313215
  · exact B313219
  · exact B313223
  · exact B313227
  · exact B313231
  · exact B313235
  · exact B313239
  · exact B313243
  · exact B313247
  · exact B313251
  · exact B313255
  · exact B313259
  · exact B313263
  · exact B313267
  · exact B313271
  · exact B313275
  · exact B313279
  · exact B313283
  · exact B313287
  · exact B313291
  · exact B313295
  · exact B313299
  · exact B313303
  · exact B313307
  · exact B313311
  · exact B313315
  · exact B313319
  · exact B313323
  · exact B313327
  · exact B313331
  · exact B313335
  · exact B313339
  · exact B313343
  · exact B313347
  · exact B313351
  · exact B313355
  · exact B313359
  · exact B313363
  · exact B313367
  · exact B313371
  · exact B313375
  · exact B313379
  · exact B313383
  · exact B313387
  · exact B313391
  · exact B313395
  · exact B313399
  · exact B313403
  · exact B313407
  · exact B313411
  · exact B313415
  · exact B313419
  · exact B313423
  · exact B313427
  · exact B313431
  · exact B313435
  · exact B313439
  · exact B313443
  · exact B313447
  · exact B313451
  · exact B313455
  · exact B313459
  · exact B313463
  · exact B313467
  · exact B313471
  · exact B313475
  · exact B313479
  · exact B313483
  · exact B313487
  · exact B313491
  · exact B313495
  · exact B313499
  · exact B313503
  · exact B313507
  · exact B313511
  · exact B313515
  · exact B313519
  · exact B313523
  · exact B313527
  · exact B313531
  · exact B313535
  · exact B313539
  · exact B313543
  · exact B313547
  · exact B313551
  · exact B313555
  · exact B313559
  · exact B313563
  · exact B313567
  · exact B313571
  · exact B313575
  · exact B313579
  · exact B313583
  · exact B313587
  · exact B313591
  · exact B313595
  · exact B313599
  · exact B313603
  · exact B313607
  · exact B313611
  · exact B313615
  · exact B313619
  · exact B313623
  · exact B313627
  · exact B313631
  · exact B313635
  · exact B313639
  · exact B313643
  · exact B313647
  · exact B313651
  · exact B313655
  · exact B313659
  · exact B313663
  · exact B313667
  · exact B313671
  · exact B313675
  · exact B313679
  · exact B313683
  · exact B313687
  · exact B313691
  · exact B313695
  · exact B313699
  · exact B313703
  · exact B313707
  · exact B313711
  · exact B313715
  · exact B313719
  · exact B313723
  · exact B313727
  · exact B313731
  · exact B313735
  · exact B313739
  · exact B313743
  · exact B313747
  · exact B313751
  · exact B313755
  · exact B313759
  · exact B313763
  · exact B313767
  · exact B313771
  · exact B313775
  · exact B313779
  · exact B313783
  · exact B313787
  · exact B313791
  · exact B313795
  · exact B313799
  · exact B313803
  · exact B313807
  · exact B313811
  · exact B313815
  · exact B313819
  · exact B313823
  · exact B313827
  · exact B313831
  · exact B313835
  · exact B313839
  · exact B313843
  · exact B313847
  · exact B313851
  · exact B313855
  · exact B313859
  · exact B313863
  · exact B313867
  · exact B313871
  · exact B313875
  · exact B313879
  · exact B313883
  · exact B313887
  · exact B313891
  · exact B313895
  · exact B313899
  · exact B313903
  · exact B313907
  · exact B313911
  · exact B313915
  · exact B313919
  · exact B313923
  · exact B313927
  · exact B313931
  · exact B313935
  · exact B313939
  · exact B313943
  · exact B313947
  · exact B313951
  · exact B313955
  · exact B313959
  · exact B313963
  · exact B313967
  · exact B313971
  · exact B313975
  · exact B313979
  · exact B313983
  · exact B313987
  · exact B313991
  · exact B313995
  · exact B313999
  · exact B314003
  · exact B314007
  · exact B314011
  · exact B314015
  · exact B314019
  · exact B314023
  · exact B314027
  · exact B314031
  · exact B314035
  · exact B314039
  · exact B314043
  · exact B314047
  · exact B314051
  · exact B314055
  · exact B314059
  · exact B314063
  · exact B314067
  · exact B314071
  · exact B314075
  · exact B314079
  · exact B314083
  · exact B314087
  · exact B314091
  · exact B314095
  · exact B314099
  · exact B314103
  · exact B314107
  · exact B314111
  · exact B314115
  · exact B314119
  · exact B314123
  · exact B314127
  · exact B314131
  · exact B314135
  · exact B314139
  · exact B314143
  · exact B314147
  · exact B314151
  · exact B314155
  · exact B314159
  · exact B314163
  · exact B314167
  · exact B314171
  · exact B314175
  · exact B314179
  · exact B314183
  · exact B314187
  · exact B314191
  · exact B314195
  · exact B314199
  · exact B314203
  · exact B314207
  · exact B314211
  · exact B314215
  · exact B314219
  · exact B314223
  · exact B314227
  · exact B314231
  · exact B314235
  · exact B314239
  · exact B314243
  · exact B314247
  · exact B314251
  · exact B314255
  · exact B314259
  · exact B314263
  · exact B314267
  · exact B314271
  · exact B314275
  · exact B314279
  · exact B314283
  · exact B314287
  · exact B314291
  · exact B314295
  · exact B314299
  · exact B314303
  · exact B314307
  · exact B314311
  · exact B314315
  · exact B314319
  · exact B314323
  · exact B314327
  · exact B314331
  · exact B314335
  · exact B314339
  · exact B314343
  · exact B314347
  · exact B314351
  · exact B314355
  · exact B314359
  · exact B314363
  · exact B314367
  · exact B314371
  · exact B314375
  · exact B314379
  · exact B314383
  · exact B314387
  · exact B314391
  · exact B314395
  · exact B314399
  · exact B314403
  · exact B314407
  · exact B314411
  · exact B314415
  · exact B314419
  · exact B314423
  · exact B314427
  · exact B314431
  · exact B314435
  · exact B314439
  · exact B314443
  · exact B314447
  · exact B314451
  · exact B314455
  · exact B314459
  · exact B314463
  · exact B314467
  · exact B314471
  · exact B314475
  · exact B314479
  · exact B314483
  · exact B314487
  · exact B314491
  · exact B314495
  · exact B314499
  · exact B314503
  · exact B314507
  · exact B314511
  · exact B314515
  · exact B314519
  · exact B314523
  · exact B314527
  · exact B314531
  · exact B314535
  · exact B314539
  · exact B314543
  · exact B314547
  · exact B314551
  · exact B314555
  · exact B314559
  · exact B314563
  · exact B314567
  · exact B314571
  · exact B314575
  · exact B314579
  · exact B314583
  · exact B314587
  · exact B314591
  · exact B314595
  · exact B314599
  · exact B314603
  · exact B314607
  · exact B314611
  · exact B314615
  · exact B314619
  · exact B314623
  · exact B314627
  · exact B314631

theorem C1 (j : ℕ) (h1 : 78658 ≤ j) (h2 : j ≤ 78957) : Blo 311834 (4 * j + 3) := by
  interval_cases j
  · exact B314635
  · exact B314639
  · exact B314643
  · exact B314647
  · exact B314651
  · exact B314655
  · exact B314659
  · exact B314663
  · exact B314667
  · exact B314671
  · exact B314675
  · exact B314679
  · exact B314683
  · exact B314687
  · exact B314691
  · exact B314695
  · exact B314699
  · exact B314703
  · exact B314707
  · exact B314711
  · exact B314715
  · exact B314719
  · exact B314723
  · exact B314727
  · exact B314731
  · exact B314735
  · exact B314739
  · exact B314743
  · exact B314747
  · exact B314751
  · exact B314755
  · exact B314759
  · exact B314763
  · exact B314767
  · exact B314771
  · exact B314775
  · exact B314779
  · exact B314783
  · exact B314787
  · exact B314791
  · exact B314795
  · exact B314799
  · exact B314803
  · exact B314807
  · exact B314811
  · exact B314815
  · exact B314819
  · exact B314823
  · exact B314827
  · exact B314831
  · exact B314835
  · exact B314839
  · exact B314843
  · exact B314847
  · exact B314851
  · exact B314855
  · exact B314859
  · exact B314863
  · exact B314867
  · exact B314871
  · exact B314875
  · exact B314879
  · exact B314883
  · exact B314887
  · exact B314891
  · exact B314895
  · exact B314899
  · exact B314903
  · exact B314907
  · exact B314911
  · exact B314915
  · exact B314919
  · exact B314923
  · exact B314927
  · exact B314931
  · exact B314935
  · exact B314939
  · exact B314943
  · exact B314947
  · exact B314951
  · exact B314955
  · exact B314959
  · exact B314963
  · exact B314967
  · exact B314971
  · exact B314975
  · exact B314979
  · exact B314983
  · exact B314987
  · exact B314991
  · exact B314995
  · exact B314999
  · exact B315003
  · exact B315007
  · exact B315011
  · exact B315015
  · exact B315019
  · exact B315023
  · exact B315027
  · exact B315031
  · exact B315035
  · exact B315039
  · exact B315043
  · exact B315047
  · exact B315051
  · exact B315055
  · exact B315059
  · exact B315063
  · exact B315067
  · exact B315071
  · exact B315075
  · exact B315079
  · exact B315083
  · exact B315087
  · exact B315091
  · exact B315095
  · exact B315099
  · exact B315103
  · exact B315107
  · exact B315111
  · exact B315115
  · exact B315119
  · exact B315123
  · exact B315127
  · exact B315131
  · exact B315135
  · exact B315139
  · exact B315143
  · exact B315147
  · exact B315151
  · exact B315155
  · exact B315159
  · exact B315163
  · exact B315167
  · exact B315171
  · exact B315175
  · exact B315179
  · exact B315183
  · exact B315187
  · exact B315191
  · exact B315195
  · exact B315199
  · exact B315203
  · exact B315207
  · exact B315211
  · exact B315215
  · exact B315219
  · exact B315223
  · exact B315227
  · exact B315231
  · exact B315235
  · exact B315239
  · exact B315243
  · exact B315247
  · exact B315251
  · exact B315255
  · exact B315259
  · exact B315263
  · exact B315267
  · exact B315271
  · exact B315275
  · exact B315279
  · exact B315283
  · exact B315287
  · exact B315291
  · exact B315295
  · exact B315299
  · exact B315303
  · exact B315307
  · exact B315311
  · exact B315315
  · exact B315319
  · exact B315323
  · exact B315327
  · exact B315331
  · exact B315335
  · exact B315339
  · exact B315343
  · exact B315347
  · exact B315351
  · exact B315355
  · exact B315359
  · exact B315363
  · exact B315367
  · exact B315371
  · exact B315375
  · exact B315379
  · exact B315383
  · exact B315387
  · exact B315391
  · exact B315395
  · exact B315399
  · exact B315403
  · exact B315407
  · exact B315411
  · exact B315415
  · exact B315419
  · exact B315423
  · exact B315427
  · exact B315431
  · exact B315435
  · exact B315439
  · exact B315443
  · exact B315447
  · exact B315451
  · exact B315455
  · exact B315459
  · exact B315463
  · exact B315467
  · exact B315471
  · exact B315475
  · exact B315479
  · exact B315483
  · exact B315487
  · exact B315491
  · exact B315495
  · exact B315499
  · exact B315503
  · exact B315507
  · exact B315511
  · exact B315515
  · exact B315519
  · exact B315523
  · exact B315527
  · exact B315531
  · exact B315535
  · exact B315539
  · exact B315543
  · exact B315547
  · exact B315551
  · exact B315555
  · exact B315559
  · exact B315563
  · exact B315567
  · exact B315571
  · exact B315575
  · exact B315579
  · exact B315583
  · exact B315587
  · exact B315591
  · exact B315595
  · exact B315599
  · exact B315603
  · exact B315607
  · exact B315611
  · exact B315615
  · exact B315619
  · exact B315623
  · exact B315627
  · exact B315631
  · exact B315635
  · exact B315639
  · exact B315643
  · exact B315647
  · exact B315651
  · exact B315655
  · exact B315659
  · exact B315663
  · exact B315667
  · exact B315671
  · exact B315675
  · exact B315679
  · exact B315683
  · exact B315687
  · exact B315691
  · exact B315695
  · exact B315699
  · exact B315703
  · exact B315707
  · exact B315711
  · exact B315715
  · exact B315719
  · exact B315723
  · exact B315727
  · exact B315731
  · exact B315735
  · exact B315739
  · exact B315743
  · exact B315747
  · exact B315751
  · exact B315755
  · exact B315759
  · exact B315763
  · exact B315767
  · exact B315771
  · exact B315775
  · exact B315779
  · exact B315783
  · exact B315787
  · exact B315791
  · exact B315795
  · exact B315799
  · exact B315803
  · exact B315807
  · exact B315811
  · exact B315815
  · exact B315819
  · exact B315823
  · exact B315827
  · exact B315831

theorem solution (m : ℕ) (hlo : 311834 ≤ m) (hhi : m ≤ 315834) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 77958 ≤ j := by omega
    have hj2 : j ≤ 78957 := by omega
    have hb : Blo 311834 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 78658 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
