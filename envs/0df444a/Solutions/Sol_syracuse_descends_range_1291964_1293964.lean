-- Prove2me | solution 1 for syracuse_descends_range_1291964_1293964
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:23.561028+00:00
-- url     : https://prove2.me/submissions/0f93d185-5c15-427b-a345-41858037c710

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


theorem B2908205 : Blo 1291964 2908205 := bbase (se 3 (by rfl) ⟨545288, by rfl⟩ : syracuseStep 2908205 = 1090577) (by norm_num)
theorem B83845205 : Blo 1291964 83845205 := bbase (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) (by norm_num)
theorem B10485845 : Blo 1291964 10485845 := bbase (se 8 (by rfl) ⟨61440, by rfl⟩ : syracuseStep 10485845 = 122881) (by norm_num)
theorem B2908277 : Blo 1291964 2908277 := bbase (se 5 (by rfl) ⟨136325, by rfl⟩ : syracuseStep 2908277 = 272651) (by norm_num)
theorem B2908349 : Blo 1291964 2908349 := bbase (se 3 (by rfl) ⟨545315, by rfl⟩ : syracuseStep 2908349 = 1090631) (by norm_num)
theorem B1310957 : Blo 1291964 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B2908421 : Blo 1291964 2908421 := bbase (se 4 (by rfl) ⟨272664, by rfl⟩ : syracuseStep 2908421 = 545329) (by norm_num)
theorem B2908493 : Blo 1291964 2908493 := bbase (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) (by norm_num)
theorem B2761037 : Blo 1291964 2761037 := bbase (se 3 (by rfl) ⟨517694, by rfl⟩ : syracuseStep 2761037 = 1035389) (by norm_num)
theorem B5521765 : Blo 1291964 5521765 := bbase (se 4 (by rfl) ⟨517665, by rfl⟩ : syracuseStep 5521765 = 1035331) (by norm_num)
theorem B2425205 : Blo 1291964 2425205 := bbase (se 5 (by rfl) ⟨113681, by rfl⟩ : syracuseStep 2425205 = 227363) (by norm_num)
theorem B4366709 : Blo 1291964 4366709 := bbase (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) (by norm_num)
theorem B25174421 : Blo 1291964 25174421 := bbase (se 6 (by rfl) ⟨590025, by rfl⟩ : syracuseStep 25174421 = 1180051) (by norm_num)
theorem B2908565 : Blo 1291964 2908565 := bbase (se 6 (by rfl) ⟨68169, by rfl⟩ : syracuseStep 2908565 = 136339) (by norm_num)
theorem B2621909 : Blo 1291964 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B2908637 : Blo 1291964 2908637 := bbase (se 3 (by rfl) ⟨545369, by rfl⟩ : syracuseStep 2908637 = 1090739) (by norm_num)
theorem B3105301 : Blo 1291964 3105301 := bbase (se 6 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 3105301 = 145561) (by norm_num)
theorem B1475101 : Blo 1291964 1475101 := bbase (se 3 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 1475101 = 553163) (by norm_num)
theorem B2908709 : Blo 1291964 2908709 := bbase (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) (by norm_num)
theorem B2761285 : Blo 1291964 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B2908781 : Blo 1291964 2908781 := bbase (se 3 (by rfl) ⟨545396, by rfl⟩ : syracuseStep 2908781 = 1090793) (by norm_num)
theorem B7365269 : Blo 1291964 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B2908853 : Blo 1291964 2908853 := bbase (se 5 (by rfl) ⟨136352, by rfl⟩ : syracuseStep 2908853 = 272705) (by norm_num)
theorem B4907749 : Blo 1291964 4907749 := bbase (se 4 (by rfl) ⟨460101, by rfl⟩ : syracuseStep 4907749 = 920203) (by norm_num)
theorem B3105533 : Blo 1291964 3105533 := bbase (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) (by norm_num)
theorem B2908925 : Blo 1291964 2908925 := bbase (se 3 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 2908925 = 1090847) (by norm_num)
theorem B1311509 : Blo 1291964 1311509 := bbase (se 6 (by rfl) ⟨30738, by rfl⟩ : syracuseStep 1311509 = 61477) (by norm_num)
theorem B2908997 : Blo 1291964 2908997 := bbase (se 4 (by rfl) ⟨272718, by rfl⟩ : syracuseStep 2908997 = 545437) (by norm_num)
theorem B2950013 : Blo 1291964 2950013 := bbase (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) (by norm_num)
theorem B3105677 : Blo 1291964 3105677 := bbase (se 3 (by rfl) ⟨582314, by rfl⟩ : syracuseStep 3105677 = 1164629) (by norm_num)
theorem B2909069 : Blo 1291964 2909069 := bbase (se 3 (by rfl) ⟨545450, by rfl⟩ : syracuseStep 2909069 = 1090901) (by norm_num)
theorem B1967021 : Blo 1291964 1967021 := bbase (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) (by norm_num)
theorem B2909141 : Blo 1291964 2909141 := bbase (se 7 (by rfl) ⟨34091, by rfl⟩ : syracuseStep 2909141 = 68183) (by norm_num)
theorem B1967069 : Blo 1291964 1967069 := bbase (se 3 (by rfl) ⟨368825, by rfl⟩ : syracuseStep 1967069 = 737651) (by norm_num)
theorem B1967117 : Blo 1291964 1967117 := bbase (se 3 (by rfl) ⟨368834, by rfl⟩ : syracuseStep 1967117 = 737669) (by norm_num)
theorem B3679253 : Blo 1291964 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B4908053 : Blo 1291964 4908053 := bbase (se 6 (by rfl) ⟨115032, by rfl⟩ : syracuseStep 4908053 = 230065) (by norm_num)
theorem B2909213 : Blo 1291964 2909213 := bbase (se 3 (by rfl) ⟨545477, by rfl⟩ : syracuseStep 2909213 = 1090955) (by norm_num)
theorem B2761789 : Blo 1291964 2761789 := bbase (se 3 (by rfl) ⟨517835, by rfl⟩ : syracuseStep 2761789 = 1035671) (by norm_num)
theorem B2909285 : Blo 1291964 2909285 := bbase (se 4 (by rfl) ⟨272745, by rfl⟩ : syracuseStep 2909285 = 545491) (by norm_num)
theorem B3105917 : Blo 1291964 3105917 := bbase (se 3 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 3105917 = 1164719) (by norm_num)
theorem B6546581 : Blo 1291964 6546581 := bbase (se 6 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 6546581 = 306871) (by norm_num)
theorem B2909357 : Blo 1291964 2909357 := bbase (se 3 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 2909357 = 1091009) (by norm_num)
theorem B1991861 : Blo 1291964 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B3679445 : Blo 1291964 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2180317 : Blo 1291964 2180317 := bbase (se 3 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 2180317 = 817619) (by norm_num)
theorem B1418473 : Blo 1291964 1418473 := bbase (se 2 (by rfl) ⟨531927, by rfl⟩ : syracuseStep 1418473 = 1063855) (by norm_num)
theorem B2909429 : Blo 1291964 2909429 := bbase (se 5 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 2909429 = 272759) (by norm_num)
theorem B1746181 : Blo 1291964 1746181 := bbase (se 4 (by rfl) ⟨163704, by rfl⟩ : syracuseStep 1746181 = 327409) (by norm_num)
theorem B2180405 : Blo 1291964 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B2909501 : Blo 1291964 2909501 := bbase (se 3 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 2909501 = 1091063) (by norm_num)
theorem B2909573 : Blo 1291964 2909573 := bbase (se 4 (by rfl) ⟨272772, by rfl⟩ : syracuseStep 2909573 = 545545) (by norm_num)
theorem B2180533 : Blo 1291964 2180533 := bbase (se 5 (by rfl) ⟨102212, by rfl⟩ : syracuseStep 2180533 = 204425) (by norm_num)
theorem B1746365 : Blo 1291964 1746365 := bbase (se 3 (by rfl) ⟨327443, by rfl⟩ : syracuseStep 1746365 = 654887) (by norm_num)
theorem B2950597 : Blo 1291964 2950597 := bbase (se 4 (by rfl) ⟨276618, by rfl⟩ : syracuseStep 2950597 = 553237) (by norm_num)
theorem B2909645 : Blo 1291964 2909645 := bbase (se 3 (by rfl) ⟨545558, by rfl⟩ : syracuseStep 2909645 = 1091117) (by norm_num)
theorem B2180621 : Blo 1291964 2180621 := bbase (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) (by norm_num)
theorem B2909717 : Blo 1291964 2909717 := bbase (se 6 (by rfl) ⟨68196, by rfl⟩ : syracuseStep 2909717 = 136393) (by norm_num)
theorem B1746517 : Blo 1291964 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B2909789 : Blo 1291964 2909789 := bbase (se 3 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 2909789 = 1091171) (by norm_num)
theorem B2180749 : Blo 1291964 2180749 := bbase (se 3 (by rfl) ⟨408890, by rfl⟩ : syracuseStep 2180749 = 817781) (by norm_num)
theorem B2909861 : Blo 1291964 2909861 := bbase (se 4 (by rfl) ⟨272799, by rfl⟩ : syracuseStep 2909861 = 545599) (by norm_num)
theorem B3147437 : Blo 1291964 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B8840917 : Blo 1291964 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B3270365 : Blo 1291964 3270365 := bbase (se 3 (by rfl) ⟨613193, by rfl⟩ : syracuseStep 3270365 = 1226387) (by norm_num)
theorem B2180837 : Blo 1291964 2180837 := bbase (se 4 (by rfl) ⟨204453, by rfl⟩ : syracuseStep 2180837 = 408907) (by norm_num)
theorem B2909933 : Blo 1291964 2909933 := bbase (se 3 (by rfl) ⟨545612, by rfl⟩ : syracuseStep 2909933 = 1091225) (by norm_num)
theorem B6637301 : Blo 1291964 6637301 := bbase (se 5 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 6637301 = 622247) (by norm_num)
theorem B2910005 : Blo 1291964 2910005 := bbase (se 5 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 2910005 = 272813) (by norm_num)
theorem B13985621 : Blo 1291964 13985621 := bbase (se 9 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 13985621 = 81947) (by norm_num)
theorem B2180965 : Blo 1291964 2180965 := bbase (se 4 (by rfl) ⟨204465, by rfl⟩ : syracuseStep 2180965 = 408931) (by norm_num)
theorem B3106685 : Blo 1291964 3106685 := bbase (se 3 (by rfl) ⟨582503, by rfl⟩ : syracuseStep 3106685 = 1165007) (by norm_num)
theorem B2910077 : Blo 1291964 2910077 := bbase (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) (by norm_num)
theorem B3270557 : Blo 1291964 3270557 := bbase (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) (by norm_num)
theorem B2762677 : Blo 1291964 2762677 := bbase (se 5 (by rfl) ⟨129500, by rfl⟩ : syracuseStep 2762677 = 259001) (by norm_num)
theorem B2181053 : Blo 1291964 2181053 := bbase (se 3 (by rfl) ⟨408947, by rfl⟩ : syracuseStep 2181053 = 817895) (by norm_num)
theorem B6211525 : Blo 1291964 6211525 := bbase (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) (by norm_num)
theorem B2910149 : Blo 1291964 2910149 := bbase (se 4 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 2910149 = 545653) (by norm_num)
theorem B2910221 : Blo 1291964 2910221 := bbase (se 3 (by rfl) ⟨545666, by rfl⟩ : syracuseStep 2910221 = 1091333) (by norm_num)
theorem B2181181 : Blo 1291964 2181181 := bbase (se 3 (by rfl) ⟨408971, by rfl⟩ : syracuseStep 2181181 = 817943) (by norm_num)
theorem B2910293 : Blo 1291964 2910293 := bbase (se 8 (by rfl) ⟨17052, by rfl⟩ : syracuseStep 2910293 = 34105) (by norm_num)
theorem B2181269 : Blo 1291964 2181269 := bbase (se 6 (by rfl) ⟨51123, by rfl⟩ : syracuseStep 2181269 = 102247) (by norm_num)
theorem B2910365 : Blo 1291964 2910365 := bbase (se 3 (by rfl) ⟨545693, by rfl⟩ : syracuseStep 2910365 = 1091387) (by norm_num)
theorem B1747117 : Blo 1291964 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B3680437 : Blo 1291964 3680437 := bbase (se 5 (by rfl) ⟨172520, by rfl⟩ : syracuseStep 3680437 = 345041) (by norm_num)
theorem B3147973 : Blo 1291964 3147973 := bbase (se 4 (by rfl) ⟨295122, by rfl⟩ : syracuseStep 3147973 = 590245) (by norm_num)
theorem B1575121 : Blo 1291964 1575121 := bbase (se 2 (by rfl) ⟨590670, by rfl⟩ : syracuseStep 1575121 = 1181341) (by norm_num)
theorem B2328797 : Blo 1291964 2328797 := bbase (se 3 (by rfl) ⟨436649, by rfl⟩ : syracuseStep 2328797 = 873299) (by norm_num)
theorem B2910437 : Blo 1291964 2910437 := bbase (se 4 (by rfl) ⟨272853, by rfl⟩ : syracuseStep 2910437 = 545707) (by norm_num)
theorem B3270901 : Blo 1291964 3270901 := bbase (se 5 (by rfl) ⟨153323, by rfl⟩ : syracuseStep 3270901 = 306647) (by norm_num)
theorem B2181397 : Blo 1291964 2181397 := bbase (se 6 (by rfl) ⟨51126, by rfl⟩ : syracuseStep 2181397 = 102253) (by norm_num)
theorem B2910509 : Blo 1291964 2910509 := bbase (se 3 (by rfl) ⟨545720, by rfl⟩ : syracuseStep 2910509 = 1091441) (by norm_num)
theorem B3271013 : Blo 1291964 3271013 := bbase (se 4 (by rfl) ⟨306657, by rfl⟩ : syracuseStep 3271013 = 613315) (by norm_num)
theorem B2181485 : Blo 1291964 2181485 := bbase (se 3 (by rfl) ⟨409028, by rfl⟩ : syracuseStep 2181485 = 818057) (by norm_num)
theorem B2910581 : Blo 1291964 2910581 := bbase (se 5 (by rfl) ⟨136433, by rfl⟩ : syracuseStep 2910581 = 272867) (by norm_num)
theorem B3148157 : Blo 1291964 3148157 := bbase (se 3 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 3148157 = 1180559) (by norm_num)
theorem B6547877 : Blo 1291964 6547877 := bbase (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) (by norm_num)
theorem B2763173 : Blo 1291964 2763173 := bbase (se 4 (by rfl) ⟨259047, by rfl⟩ : syracuseStep 2763173 = 518095) (by norm_num)
theorem B2910653 : Blo 1291964 2910653 := bbase (se 3 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 2910653 = 1091495) (by norm_num)
theorem B4360661 : Blo 1291964 4360661 := bbase (se 7 (by rfl) ⟨51101, by rfl⟩ : syracuseStep 4360661 = 102203) (by norm_num)
theorem B2181613 : Blo 1291964 2181613 := bbase (se 3 (by rfl) ⟨409052, by rfl⟩ : syracuseStep 2181613 = 818105) (by norm_num)
theorem B2910725 : Blo 1291964 2910725 := bbase (se 4 (by rfl) ⟨272880, by rfl⟩ : syracuseStep 2910725 = 545761) (by norm_num)
theorem B3271205 : Blo 1291964 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B2181701 : Blo 1291964 2181701 := bbase (se 4 (by rfl) ⟨204534, by rfl⟩ : syracuseStep 2181701 = 409069) (by norm_num)
theorem B2910797 : Blo 1291964 2910797 := bbase (se 3 (by rfl) ⟨545774, by rfl⟩ : syracuseStep 2910797 = 1091549) (by norm_num)
theorem B7088725 : Blo 1291964 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B1747597 : Blo 1291964 1747597 := bbase (se 3 (by rfl) ⟨327674, by rfl⟩ : syracuseStep 1747597 = 655349) (by norm_num)
theorem B2910869 : Blo 1291964 2910869 := bbase (se 6 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 2910869 = 136447) (by norm_num)
theorem B2181829 : Blo 1291964 2181829 := bbase (se 4 (by rfl) ⟨204546, by rfl⟩ : syracuseStep 2181829 = 409093) (by norm_num)
theorem B2656981 : Blo 1291964 2656981 := bbase (se 7 (by rfl) ⟨31136, by rfl⟩ : syracuseStep 2656981 = 62273) (by norm_num)
theorem B2910941 : Blo 1291964 2910941 := bbase (se 3 (by rfl) ⟨545801, by rfl⟩ : syracuseStep 2910941 = 1091603) (by norm_num)
theorem B2181917 : Blo 1291964 2181917 := bbase (se 3 (by rfl) ⟨409109, by rfl⟩ : syracuseStep 2181917 = 818219) (by norm_num)
theorem B2911013 : Blo 1291964 2911013 := bbase (se 4 (by rfl) ⟨272907, by rfl⟩ : syracuseStep 2911013 = 545815) (by norm_num)
theorem B11045717 : Blo 1291964 11045717 := bbase (se 9 (by rfl) ⟨32360, by rfl⟩ : syracuseStep 11045717 = 64721) (by norm_num)
theorem B2911085 : Blo 1291964 2911085 := bbase (se 3 (by rfl) ⟨545828, by rfl⟩ : syracuseStep 2911085 = 1091657) (by norm_num)
theorem B3271549 : Blo 1291964 3271549 := bbase (se 3 (by rfl) ⟨613415, by rfl⟩ : syracuseStep 3271549 = 1226831) (by norm_num)
theorem B4361093 : Blo 1291964 4361093 := bbase (se 4 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 4361093 = 817705) (by norm_num)
theorem B2182045 : Blo 1291964 2182045 := bbase (se 3 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 2182045 = 818267) (by norm_num)
theorem B3492773 : Blo 1291964 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B2911157 : Blo 1291964 2911157 := bbase (se 5 (by rfl) ⟨136460, by rfl⟩ : syracuseStep 2911157 = 272921) (by norm_num)
theorem B11037653 : Blo 1291964 11037653 := bbase (se 7 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 11037653 = 258695) (by norm_num)
theorem B3271661 : Blo 1291964 3271661 := bbase (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) (by norm_num)
theorem B5598197 : Blo 1291964 5598197 := bbase (se 5 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 5598197 = 524831) (by norm_num)
theorem B2182133 : Blo 1291964 2182133 := bbase (se 5 (by rfl) ⟨102287, by rfl⟩ : syracuseStep 2182133 = 204575) (by norm_num)
theorem B2911229 : Blo 1291964 2911229 := bbase (se 3 (by rfl) ⟨545855, by rfl⟩ : syracuseStep 2911229 = 1091711) (by norm_num)
theorem B5246021 : Blo 1291964 5246021 := bbase (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) (by norm_num)
theorem B2911301 : Blo 1291964 2911301 := bbase (se 4 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 2911301 = 545869) (by norm_num)
theorem B4910165 : Blo 1291964 4910165 := bbase (se 8 (by rfl) ⟨28770, by rfl⟩ : syracuseStep 4910165 = 57541) (by norm_num)
theorem B2182261 : Blo 1291964 2182261 := bbase (se 5 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 2182261 = 204587) (by norm_num)
theorem B2911373 : Blo 1291964 2911373 := bbase (se 3 (by rfl) ⟨545882, by rfl⟩ : syracuseStep 2911373 = 1091765) (by norm_num)
theorem B4140197 : Blo 1291964 4140197 := bbase (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) (by norm_num)
theorem B3271853 : Blo 1291964 3271853 := bbase (se 3 (by rfl) ⟨613472, by rfl⟩ : syracuseStep 3271853 = 1226945) (by norm_num)
theorem B9825461 : Blo 1291964 9825461 := bbase (se 5 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 9825461 = 921137) (by norm_num)
theorem B2100421 : Blo 1291964 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B2182349 : Blo 1291964 2182349 := bbase (se 3 (by rfl) ⟨409190, by rfl⟩ : syracuseStep 2182349 = 818381) (by norm_num)
theorem B3108061 : Blo 1291964 3108061 := bbase (se 3 (by rfl) ⟨582761, by rfl⟩ : syracuseStep 3108061 = 1165523) (by norm_num)
theorem B3681541 : Blo 1291964 3681541 := bbase (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) (by norm_num)
theorem B5524757 : Blo 1291964 5524757 := bbase (se 6 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 5524757 = 258973) (by norm_num)
theorem B4140325 : Blo 1291964 4140325 := bbase (se 4 (by rfl) ⟨388155, by rfl⟩ : syracuseStep 4140325 = 776311) (by norm_num)
theorem B2452781 : Blo 1291964 2452781 := bbase (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) (by norm_num)
theorem B4361525 : Blo 1291964 4361525 := bbase (se 5 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 4361525 = 408893) (by norm_num)
theorem B2182477 : Blo 1291964 2182477 := bbase (se 3 (by rfl) ⟨409214, by rfl⟩ : syracuseStep 2182477 = 818429) (by norm_num)
theorem B4910453 : Blo 1291964 4910453 := bbase (se 5 (by rfl) ⟨230177, by rfl⟩ : syracuseStep 4910453 = 460355) (by norm_num)
theorem B7359893 : Blo 1291964 7359893 := bbase (se 6 (by rfl) ⟨172497, by rfl⟩ : syracuseStep 7359893 = 344995) (by norm_num)
theorem B1453477 : Blo 1291964 1453477 := bbase (se 4 (by rfl) ⟨136263, by rfl⟩ : syracuseStep 1453477 = 272527) (by norm_num)
theorem B2182565 : Blo 1291964 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B2452933 : Blo 1291964 2452933 := bbase (se 4 (by rfl) ⟨229962, by rfl⟩ : syracuseStep 2452933 = 459925) (by norm_num)
theorem B1453513 : Blo 1291964 1453513 := bbase (se 2 (by rfl) ⟨545067, by rfl⟩ : syracuseStep 1453513 = 1090135) (by norm_num)
theorem B1379801 : Blo 1291964 1379801 := bbase (se 2 (by rfl) ⟨517425, by rfl⟩ : syracuseStep 1379801 = 1034851) (by norm_num)
theorem B1453549 : Blo 1291964 1453549 := bbase (se 3 (by rfl) ⟨272540, by rfl⟩ : syracuseStep 1453549 = 545081) (by norm_num)
theorem B3272197 : Blo 1291964 3272197 := bbase (se 4 (by rfl) ⟨306768, by rfl⟩ : syracuseStep 3272197 = 613537) (by norm_num)
theorem B1453585 : Blo 1291964 1453585 := bbase (se 2 (by rfl) ⟨545094, by rfl⟩ : syracuseStep 1453585 = 1090189) (by norm_num)
theorem B2182693 : Blo 1291964 2182693 := bbase (se 4 (by rfl) ⟨204627, by rfl⟩ : syracuseStep 2182693 = 409255) (by norm_num)
theorem B1453621 : Blo 1291964 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B9817685 : Blo 1291964 9817685 := bbase (se 8 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 9817685 = 115051) (by norm_num)
theorem B1453657 : Blo 1291964 1453657 := bbase (se 2 (by rfl) ⟨545121, by rfl⟩ : syracuseStep 1453657 = 1090243) (by norm_num)
theorem B3272309 : Blo 1291964 3272309 := bbase (se 5 (by rfl) ⟨153389, by rfl⟩ : syracuseStep 3272309 = 306779) (by norm_num)
theorem B1453693 : Blo 1291964 1453693 := bbase (se 3 (by rfl) ⟨272567, by rfl⟩ : syracuseStep 1453693 = 545135) (by norm_num)
theorem B2182781 : Blo 1291964 2182781 := bbase (se 3 (by rfl) ⟨409271, by rfl⟩ : syracuseStep 2182781 = 818543) (by norm_num)
theorem B2330245 : Blo 1291964 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B1453729 : Blo 1291964 1453729 := bbase (se 2 (by rfl) ⟨545148, by rfl⟩ : syracuseStep 1453729 = 1090297) (by norm_num)
theorem B6549173 : Blo 1291964 6549173 := bbase (se 5 (by rfl) ⟨306992, by rfl⟩ : syracuseStep 6549173 = 613985) (by norm_num)
theorem B1453765 : Blo 1291964 1453765 := bbase (se 4 (by rfl) ⟨136290, by rfl⟩ : syracuseStep 1453765 = 272581) (by norm_num)
theorem B2330317 : Blo 1291964 2330317 := bbase (se 3 (by rfl) ⟨436934, by rfl⟩ : syracuseStep 2330317 = 873869) (by norm_num)
theorem B4361957 : Blo 1291964 4361957 := bbase (se 4 (by rfl) ⟨408933, by rfl⟩ : syracuseStep 4361957 = 817867) (by norm_num)
theorem B1453801 : Blo 1291964 1453801 := bbase (se 2 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 1453801 = 1090351) (by norm_num)
theorem B2453237 : Blo 1291964 2453237 := bbase (se 5 (by rfl) ⟨114995, by rfl⟩ : syracuseStep 2453237 = 229991) (by norm_num)
theorem B5672693 : Blo 1291964 5672693 := bbase (se 5 (by rfl) ⟨265907, by rfl⟩ : syracuseStep 5672693 = 531815) (by norm_num)
theorem B2182909 : Blo 1291964 2182909 := bbase (se 3 (by rfl) ⟨409295, by rfl⟩ : syracuseStep 2182909 = 818591) (by norm_num)
theorem B1453837 : Blo 1291964 1453837 := bbase (se 3 (by rfl) ⟨272594, by rfl⟩ : syracuseStep 1453837 = 545189) (by norm_num)
theorem B1453873 : Blo 1291964 1453873 := bbase (se 2 (by rfl) ⟨545202, by rfl⟩ : syracuseStep 1453873 = 1090405) (by norm_num)
theorem B3272501 : Blo 1291964 3272501 := bbase (se 5 (by rfl) ⟨153398, by rfl⟩ : syracuseStep 3272501 = 306797) (by norm_num)
theorem B1453909 : Blo 1291964 1453909 := bbase (se 9 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 1453909 = 8519) (by norm_num)
theorem B2182997 : Blo 1291964 2182997 := bbase (se 9 (by rfl) ⟨6395, by rfl⟩ : syracuseStep 2182997 = 12791) (by norm_num)
theorem B1453945 : Blo 1291964 1453945 := bbase (se 2 (by rfl) ⟨545229, by rfl⟩ : syracuseStep 1453945 = 1090459) (by norm_num)
theorem B1380245 : Blo 1291964 1380245 := bbase (se 6 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 1380245 = 64699) (by norm_num)
theorem B1453981 : Blo 1291964 1453981 := bbase (se 3 (by rfl) ⟨272621, by rfl⟩ : syracuseStep 1453981 = 545243) (by norm_num)
theorem B8286133 : Blo 1291964 8286133 := bbase (se 5 (by rfl) ⟨388412, by rfl⟩ : syracuseStep 8286133 = 776825) (by norm_num)
theorem B1454017 : Blo 1291964 1454017 := bbase (se 2 (by rfl) ⟨545256, by rfl⟩ : syracuseStep 1454017 = 1090513) (by norm_num)
theorem B2183125 : Blo 1291964 2183125 := bbase (se 7 (by rfl) ⟨25583, by rfl⟩ : syracuseStep 2183125 = 51167) (by norm_num)
theorem B1454053 : Blo 1291964 1454053 := bbase (se 4 (by rfl) ⟨136317, by rfl⟩ : syracuseStep 1454053 = 272635) (by norm_num)
theorem B1454089 : Blo 1291964 1454089 := bbase (se 2 (by rfl) ⟨545283, by rfl⟩ : syracuseStep 1454089 = 1090567) (by norm_num)
theorem B8278037 : Blo 1291964 8278037 := bbase (se 6 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 8278037 = 388033) (by norm_num)
theorem B1454125 : Blo 1291964 1454125 := bbase (se 3 (by rfl) ⟨272648, by rfl⟩ : syracuseStep 1454125 = 545297) (by norm_num)
theorem B2183213 : Blo 1291964 2183213 := bbase (se 3 (by rfl) ⟨409352, by rfl⟩ : syracuseStep 2183213 = 818705) (by norm_num)
theorem B1454161 : Blo 1291964 1454161 := bbase (se 2 (by rfl) ⟨545310, by rfl⟩ : syracuseStep 1454161 = 1090621) (by norm_num)
theorem B6541397 : Blo 1291964 6541397 := bbase (se 8 (by rfl) ⟨38328, by rfl⟩ : syracuseStep 6541397 = 76657) (by norm_num)
theorem B1552493 : Blo 1291964 1552493 := bbase (se 3 (by rfl) ⟨291092, by rfl⟩ : syracuseStep 1552493 = 582185) (by norm_num)
theorem B1454197 : Blo 1291964 1454197 := bbase (se 5 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 1454197 = 136331) (by norm_num)
theorem B1380493 : Blo 1291964 1380493 := bbase (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) (by norm_num)
theorem B3272845 : Blo 1291964 3272845 := bbase (se 3 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 3272845 = 1227317) (by norm_num)
theorem B4362389 : Blo 1291964 4362389 := bbase (se 6 (by rfl) ⟨102243, by rfl⟩ : syracuseStep 4362389 = 204487) (by norm_num)
theorem B1454233 : Blo 1291964 1454233 := bbase (se 2 (by rfl) ⟨545337, by rfl⟩ : syracuseStep 1454233 = 1090675) (by norm_num)
theorem B2183341 : Blo 1291964 2183341 := bbase (se 3 (by rfl) ⟨409376, by rfl⟩ : syracuseStep 2183341 = 818753) (by norm_num)
theorem B1454269 : Blo 1291964 1454269 := bbase (se 3 (by rfl) ⟨272675, by rfl⟩ : syracuseStep 1454269 = 545351) (by norm_num)
theorem B2330821 : Blo 1291964 2330821 := bbase (se 4 (by rfl) ⟨218514, by rfl⟩ : syracuseStep 2330821 = 437029) (by norm_num)
theorem B1454305 : Blo 1291964 1454305 := bbase (se 2 (by rfl) ⟨545364, by rfl⟩ : syracuseStep 1454305 = 1090729) (by norm_num)
theorem B8392949 : Blo 1291964 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B3272957 : Blo 1291964 3272957 := bbase (se 3 (by rfl) ⟨613679, by rfl⟩ : syracuseStep 3272957 = 1227359) (by norm_num)
theorem B1454341 : Blo 1291964 1454341 := bbase (se 4 (by rfl) ⟨136344, by rfl⟩ : syracuseStep 1454341 = 272689) (by norm_num)
theorem B5525765 : Blo 1291964 5525765 := bbase (se 4 (by rfl) ⟨518040, by rfl⟩ : syracuseStep 5525765 = 1036081) (by norm_num)
theorem B2183429 : Blo 1291964 2183429 := bbase (se 4 (by rfl) ⟨204696, by rfl⟩ : syracuseStep 2183429 = 409393) (by norm_num)
theorem B1454377 : Blo 1291964 1454377 := bbase (se 2 (by rfl) ⟨545391, by rfl⟩ : syracuseStep 1454377 = 1090783) (by norm_num)
theorem B1454413 : Blo 1291964 1454413 := bbase (se 3 (by rfl) ⟨272702, by rfl⟩ : syracuseStep 1454413 = 545405) (by norm_num)
theorem B1454449 : Blo 1291964 1454449 := bbase (se 2 (by rfl) ⟨545418, by rfl⟩ : syracuseStep 1454449 = 1090837) (by norm_num)
theorem B2183557 : Blo 1291964 2183557 := bbase (se 4 (by rfl) ⟨204708, by rfl⟩ : syracuseStep 2183557 = 409417) (by norm_num)
theorem B1454485 : Blo 1291964 1454485 := bbase (se 6 (by rfl) ⟨34089, by rfl⟩ : syracuseStep 1454485 = 68179) (by norm_num)
theorem B22409621 : Blo 1291964 22409621 := bbase (se 6 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 22409621 = 1050451) (by norm_num)
theorem B1454521 : Blo 1291964 1454521 := bbase (se 2 (by rfl) ⟨545445, by rfl⟩ : syracuseStep 1454521 = 1090891) (by norm_num)
theorem B3273149 : Blo 1291964 3273149 := bbase (se 3 (by rfl) ⟨613715, by rfl⟩ : syracuseStep 3273149 = 1227431) (by norm_num)
theorem B1454557 : Blo 1291964 1454557 := bbase (se 3 (by rfl) ⟨272729, by rfl⟩ : syracuseStep 1454557 = 545459) (by norm_num)
theorem B2453989 : Blo 1291964 2453989 := bbase (se 4 (by rfl) ⟨230061, by rfl⟩ : syracuseStep 2453989 = 460123) (by norm_num)
theorem B1454593 : Blo 1291964 1454593 := bbase (se 2 (by rfl) ⟨545472, by rfl⟩ : syracuseStep 1454593 = 1090945) (by norm_num)
theorem B4911637 : Blo 1291964 4911637 := bbase (se 6 (by rfl) ⟨115116, by rfl⟩ : syracuseStep 4911637 = 230233) (by norm_num)
theorem B1937957 : Blo 1291964 1937957 := bbase (se 4 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 1937957 = 363367) (by norm_num)
theorem B1454629 : Blo 1291964 1454629 := bbase (se 4 (by rfl) ⟨136371, by rfl⟩ : syracuseStep 1454629 = 272743) (by norm_num)
theorem B7361077 : Blo 1291964 7361077 := bbase (se 5 (by rfl) ⟨345050, by rfl⟩ : syracuseStep 7361077 = 690101) (by norm_num)
theorem B1937981 : Blo 1291964 1937981 := bbase (se 3 (by rfl) ⟨363371, by rfl⟩ : syracuseStep 1937981 = 726743) (by norm_num)
theorem B1839677 : Blo 1291964 1839677 := bbase (se 3 (by rfl) ⟨344939, by rfl⟩ : syracuseStep 1839677 = 689879) (by norm_num)
theorem B4362821 : Blo 1291964 4362821 := bbase (se 4 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 4362821 = 818029) (by norm_num)
theorem B1454665 : Blo 1291964 1454665 := bbase (se 2 (by rfl) ⟨545499, by rfl⟩ : syracuseStep 1454665 = 1090999) (by norm_num)
theorem B1380937 : Blo 1291964 1380937 := bbase (se 2 (by rfl) ⟨517851, by rfl⟩ : syracuseStep 1380937 = 1035703) (by norm_num)
theorem B1938005 : Blo 1291964 1938005 := bbase (se 8 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 1938005 = 22711) (by norm_num)
theorem B1938029 : Blo 1291964 1938029 := bbase (se 3 (by rfl) ⟨363380, by rfl⟩ : syracuseStep 1938029 = 726761) (by norm_num)
theorem B1454701 : Blo 1291964 1454701 := bbase (se 3 (by rfl) ⟨272756, by rfl⟩ : syracuseStep 1454701 = 545513) (by norm_num)
theorem B2454133 : Blo 1291964 2454133 := bbase (se 5 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 2454133 = 230075) (by norm_num)
theorem B1938053 : Blo 1291964 1938053 := bbase (se 4 (by rfl) ⟨181692, by rfl⟩ : syracuseStep 1938053 = 363385) (by norm_num)
theorem B1380997 : Blo 1291964 1380997 := bbase (se 4 (by rfl) ⟨129468, by rfl⟩ : syracuseStep 1380997 = 258937) (by norm_num)
theorem B1454737 : Blo 1291964 1454737 := bbase (se 2 (by rfl) ⟨545526, by rfl⟩ : syracuseStep 1454737 = 1091053) (by norm_num)
theorem B1938077 : Blo 1291964 1938077 := bbase (se 3 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 1938077 = 726779) (by norm_num)
theorem B1938101 : Blo 1291964 1938101 := bbase (se 5 (by rfl) ⟨90848, by rfl⟩ : syracuseStep 1938101 = 181697) (by norm_num)
theorem B1454773 : Blo 1291964 1454773 := bbase (se 5 (by rfl) ⟨68192, by rfl⟩ : syracuseStep 1454773 = 136385) (by norm_num)
theorem B1938125 : Blo 1291964 1938125 := bbase (se 3 (by rfl) ⟨363398, by rfl⟩ : syracuseStep 1938125 = 726797) (by norm_num)
theorem B1454809 : Blo 1291964 1454809 := bbase (se 2 (by rfl) ⟨545553, by rfl⟩ : syracuseStep 1454809 = 1091107) (by norm_num)
theorem B1938149 : Blo 1291964 1938149 := bbase (se 4 (by rfl) ⟨181701, by rfl⟩ : syracuseStep 1938149 = 363403) (by norm_num)
theorem B3683045 : Blo 1291964 3683045 := bbase (se 4 (by rfl) ⟨345285, by rfl⟩ : syracuseStep 3683045 = 690571) (by norm_num)
theorem B1938173 : Blo 1291964 1938173 := bbase (se 3 (by rfl) ⟨363407, by rfl⟩ : syracuseStep 1938173 = 726815) (by norm_num)
theorem B1454845 : Blo 1291964 1454845 := bbase (se 3 (by rfl) ⟨272783, by rfl⟩ : syracuseStep 1454845 = 545567) (by norm_num)
theorem B1938197 : Blo 1291964 1938197 := bbase (se 6 (by rfl) ⟨45426, by rfl⟩ : syracuseStep 1938197 = 90853) (by norm_num)
theorem B2454293 : Blo 1291964 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B3273493 : Blo 1291964 3273493 := bbase (se 6 (by rfl) ⟨76722, by rfl⟩ : syracuseStep 3273493 = 153445) (by norm_num)
theorem B1454881 : Blo 1291964 1454881 := bbase (se 2 (by rfl) ⟨545580, by rfl⟩ : syracuseStep 1454881 = 1091161) (by norm_num)
theorem B1938221 : Blo 1291964 1938221 := bbase (se 3 (by rfl) ⟨363416, by rfl⟩ : syracuseStep 1938221 = 726833) (by norm_num)
theorem B1938245 : Blo 1291964 1938245 := bbase (se 4 (by rfl) ⟨181710, by rfl⟩ : syracuseStep 1938245 = 363421) (by norm_num)
theorem B1454917 : Blo 1291964 1454917 := bbase (se 4 (by rfl) ⟨136398, by rfl⟩ : syracuseStep 1454917 = 272797) (by norm_num)
theorem B4911941 : Blo 1291964 4911941 := bbase (se 4 (by rfl) ⟨460494, by rfl⟩ : syracuseStep 4911941 = 920989) (by norm_num)
theorem B1635157 : Blo 1291964 1635157 := bbase (se 9 (by rfl) ⟨4790, by rfl⟩ : syracuseStep 1635157 = 9581) (by norm_num)
theorem B1938269 : Blo 1291964 1938269 := bbase (se 3 (by rfl) ⟨363425, by rfl⟩ : syracuseStep 1938269 = 726851) (by norm_num)
theorem B2331485 : Blo 1291964 2331485 := bbase (se 3 (by rfl) ⟨437153, by rfl⟩ : syracuseStep 2331485 = 874307) (by norm_num)
theorem B1454953 : Blo 1291964 1454953 := bbase (se 2 (by rfl) ⟨545607, by rfl⟩ : syracuseStep 1454953 = 1091215) (by norm_num)
theorem B1938293 : Blo 1291964 1938293 := bbase (se 5 (by rfl) ⟨90857, by rfl⟩ : syracuseStep 1938293 = 181715) (by norm_num)
theorem B3273605 : Blo 1291964 3273605 := bbase (se 4 (by rfl) ⟨306900, by rfl⟩ : syracuseStep 3273605 = 613801) (by norm_num)
theorem B1938317 : Blo 1291964 1938317 := bbase (se 3 (by rfl) ⟨363434, by rfl⟩ : syracuseStep 1938317 = 726869) (by norm_num)
theorem B1454989 : Blo 1291964 1454989 := bbase (se 3 (by rfl) ⟨272810, by rfl⟩ : syracuseStep 1454989 = 545621) (by norm_num)
theorem B1938341 : Blo 1291964 1938341 := bbase (se 4 (by rfl) ⟨181719, by rfl⟩ : syracuseStep 1938341 = 363439) (by norm_num)
theorem B2454437 : Blo 1291964 2454437 := bbase (se 4 (by rfl) ⟨230103, by rfl⟩ : syracuseStep 2454437 = 460207) (by norm_num)
theorem B1455025 : Blo 1291964 1455025 := bbase (se 2 (by rfl) ⟨545634, by rfl⟩ : syracuseStep 1455025 = 1091269) (by norm_num)
theorem B1938365 : Blo 1291964 1938365 := bbase (se 3 (by rfl) ⟨363443, by rfl⟩ : syracuseStep 1938365 = 726887) (by norm_num)
theorem B1381313 : Blo 1291964 1381313 := bbase (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) (by norm_num)
theorem B6550469 : Blo 1291964 6550469 := bbase (se 4 (by rfl) ⟨614106, by rfl⟩ : syracuseStep 6550469 = 1228213) (by norm_num)
theorem B1938389 : Blo 1291964 1938389 := bbase (se 7 (by rfl) ⟨22715, by rfl⟩ : syracuseStep 1938389 = 45431) (by norm_num)
theorem B50361301 : Blo 1291964 50361301 := bbase (se 7 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 50361301 = 1180343) (by norm_num)
theorem B1455061 : Blo 1291964 1455061 := bbase (se 7 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 1455061 = 34103) (by norm_num)
theorem B1938413 : Blo 1291964 1938413 := bbase (se 3 (by rfl) ⟨363452, by rfl⟩ : syracuseStep 1938413 = 726905) (by norm_num)
theorem B4363253 : Blo 1291964 4363253 := bbase (se 5 (by rfl) ⟨204527, by rfl⟩ : syracuseStep 4363253 = 409055) (by norm_num)
theorem B1455097 : Blo 1291964 1455097 := bbase (se 2 (by rfl) ⟨545661, by rfl⟩ : syracuseStep 1455097 = 1091323) (by norm_num)
theorem B1635329 : Blo 1291964 1635329 := bbase (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) (by norm_num)
theorem B1938437 : Blo 1291964 1938437 := bbase (se 4 (by rfl) ⟨181728, by rfl⟩ : syracuseStep 1938437 = 363457) (by norm_num)
theorem B1938461 : Blo 1291964 1938461 := bbase (se 3 (by rfl) ⟨363461, by rfl⟩ : syracuseStep 1938461 = 726923) (by norm_num)
theorem B1455133 : Blo 1291964 1455133 := bbase (se 3 (by rfl) ⟨272837, by rfl⟩ : syracuseStep 1455133 = 545675) (by norm_num)
theorem B1938485 : Blo 1291964 1938485 := bbase (se 5 (by rfl) ⟨90866, by rfl⟩ : syracuseStep 1938485 = 181733) (by norm_num)
theorem B1635385 : Blo 1291964 1635385 := bbase (se 2 (by rfl) ⟨613269, by rfl⟩ : syracuseStep 1635385 = 1226539) (by norm_num)
theorem B1455169 : Blo 1291964 1455169 := bbase (se 2 (by rfl) ⟨545688, by rfl⟩ : syracuseStep 1455169 = 1091377) (by norm_num)
theorem B3273797 : Blo 1291964 3273797 := bbase (se 4 (by rfl) ⟨306918, by rfl⟩ : syracuseStep 3273797 = 613837) (by norm_num)
theorem B1938509 : Blo 1291964 1938509 := bbase (se 3 (by rfl) ⟨363470, by rfl⟩ : syracuseStep 1938509 = 726941) (by norm_num)
theorem B1938533 : Blo 1291964 1938533 := bbase (se 4 (by rfl) ⟨181737, by rfl⟩ : syracuseStep 1938533 = 363475) (by norm_num)
theorem B1455205 : Blo 1291964 1455205 := bbase (se 4 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 1455205 = 272851) (by norm_num)
theorem B1938557 : Blo 1291964 1938557 := bbase (se 3 (by rfl) ⟨363479, by rfl⟩ : syracuseStep 1938557 = 726959) (by norm_num)
theorem B1455241 : Blo 1291964 1455241 := bbase (se 2 (by rfl) ⟨545715, by rfl⟩ : syracuseStep 1455241 = 1091431) (by norm_num)
theorem B1938581 : Blo 1291964 1938581 := bbase (se 6 (by rfl) ⟨45435, by rfl⟩ : syracuseStep 1938581 = 90871) (by norm_num)
theorem B1635481 : Blo 1291964 1635481 := bbase (se 2 (by rfl) ⟨613305, by rfl⟩ : syracuseStep 1635481 = 1226611) (by norm_num)
theorem B1938605 : Blo 1291964 1938605 := bbase (se 3 (by rfl) ⟨363488, by rfl⟩ : syracuseStep 1938605 = 726977) (by norm_num)
theorem B1455277 : Blo 1291964 1455277 := bbase (se 3 (by rfl) ⟨272864, by rfl⟩ : syracuseStep 1455277 = 545729) (by norm_num)
theorem B1938629 : Blo 1291964 1938629 := bbase (se 4 (by rfl) ⟨181746, by rfl⟩ : syracuseStep 1938629 = 363493) (by norm_num)
theorem B2454725 : Blo 1291964 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B1455313 : Blo 1291964 1455313 := bbase (se 2 (by rfl) ⟨545742, by rfl⟩ : syracuseStep 1455313 = 1091485) (by norm_num)
theorem B1938653 : Blo 1291964 1938653 := bbase (se 3 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 1938653 = 726995) (by norm_num)
theorem B1938677 : Blo 1291964 1938677 := bbase (se 5 (by rfl) ⟨90875, by rfl⟩ : syracuseStep 1938677 = 181751) (by norm_num)
theorem B1455349 : Blo 1291964 1455349 := bbase (se 5 (by rfl) ⟨68219, by rfl⟩ : syracuseStep 1455349 = 136439) (by norm_num)
theorem B1938701 : Blo 1291964 1938701 := bbase (se 3 (by rfl) ⟨363506, by rfl⟩ : syracuseStep 1938701 = 727013) (by norm_num)
theorem B1553689 : Blo 1291964 1553689 := bbase (se 2 (by rfl) ⟨582633, by rfl⟩ : syracuseStep 1553689 = 1165267) (by norm_num)
theorem B1455385 : Blo 1291964 1455385 := bbase (se 2 (by rfl) ⟨545769, by rfl⟩ : syracuseStep 1455385 = 1091539) (by norm_num)
theorem B1938725 : Blo 1291964 1938725 := bbase (se 4 (by rfl) ⟨181755, by rfl⟩ : syracuseStep 1938725 = 363511) (by norm_num)
theorem B1840429 : Blo 1291964 1840429 := bbase (se 3 (by rfl) ⟨345080, by rfl⟩ : syracuseStep 1840429 = 690161) (by norm_num)
theorem B1938749 : Blo 1291964 1938749 := bbase (se 3 (by rfl) ⟨363515, by rfl⟩ : syracuseStep 1938749 = 727031) (by norm_num)
theorem B1455421 : Blo 1291964 1455421 := bbase (se 3 (by rfl) ⟨272891, by rfl⟩ : syracuseStep 1455421 = 545783) (by norm_num)
theorem B1635653 : Blo 1291964 1635653 := bbase (se 4 (by rfl) ⟨153342, by rfl⟩ : syracuseStep 1635653 = 306685) (by norm_num)
theorem B1938773 : Blo 1291964 1938773 := bbase (se 14 (by rfl) ⟨177, by rfl⟩ : syracuseStep 1938773 = 355) (by norm_num)
theorem B2454877 : Blo 1291964 2454877 := bbase (se 3 (by rfl) ⟨460289, by rfl⟩ : syracuseStep 2454877 = 920579) (by norm_num)
theorem B1553761 : Blo 1291964 1553761 := bbase (se 2 (by rfl) ⟨582660, by rfl⟩ : syracuseStep 1553761 = 1165321) (by norm_num)
theorem B1455457 : Blo 1291964 1455457 := bbase (se 2 (by rfl) ⟨545796, by rfl⟩ : syracuseStep 1455457 = 1091593) (by norm_num)
theorem B6542693 : Blo 1291964 6542693 := bbase (se 4 (by rfl) ⟨613377, by rfl⟩ : syracuseStep 6542693 = 1226755) (by norm_num)
theorem B1938797 : Blo 1291964 1938797 := bbase (se 3 (by rfl) ⟨363524, by rfl⟩ : syracuseStep 1938797 = 727049) (by norm_num)
theorem B1635709 : Blo 1291964 1635709 := bbase (se 3 (by rfl) ⟨306695, by rfl⟩ : syracuseStep 1635709 = 613391) (by norm_num)
theorem B1381757 : Blo 1291964 1381757 := bbase (se 3 (by rfl) ⟨259079, by rfl⟩ : syracuseStep 1381757 = 518159) (by norm_num)
theorem B3315077 : Blo 1291964 3315077 := bbase (se 4 (by rfl) ⟨310788, by rfl⟩ : syracuseStep 3315077 = 621577) (by norm_num)
theorem B2069893 : Blo 1291964 2069893 := bbase (se 4 (by rfl) ⟨194052, by rfl⟩ : syracuseStep 2069893 = 388105) (by norm_num)
theorem B1938821 : Blo 1291964 1938821 := bbase (se 4 (by rfl) ⟨181764, by rfl⟩ : syracuseStep 1938821 = 363529) (by norm_num)
theorem B1455493 : Blo 1291964 1455493 := bbase (se 4 (by rfl) ⟨136452, by rfl⟩ : syracuseStep 1455493 = 272905) (by norm_num)
theorem B1938845 : Blo 1291964 1938845 := bbase (se 3 (by rfl) ⟨363533, by rfl⟩ : syracuseStep 1938845 = 727067) (by norm_num)
theorem B3274141 : Blo 1291964 3274141 := bbase (se 3 (by rfl) ⟨613901, by rfl⟩ : syracuseStep 3274141 = 1227803) (by norm_num)
theorem B4363685 : Blo 1291964 4363685 := bbase (se 4 (by rfl) ⟨409095, by rfl⟩ : syracuseStep 4363685 = 818191) (by norm_num)
theorem B1455529 : Blo 1291964 1455529 := bbase (se 2 (by rfl) ⟨545823, by rfl⟩ : syracuseStep 1455529 = 1091647) (by norm_num)
theorem B1938869 : Blo 1291964 1938869 := bbase (se 5 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 1938869 = 181769) (by norm_num)
theorem B1938893 : Blo 1291964 1938893 := bbase (se 3 (by rfl) ⟨363542, by rfl⟩ : syracuseStep 1938893 = 727085) (by norm_num)
theorem B1455565 : Blo 1291964 1455565 := bbase (se 3 (by rfl) ⟨272918, by rfl⟩ : syracuseStep 1455565 = 545837) (by norm_num)
theorem B1635805 : Blo 1291964 1635805 := bbase (se 3 (by rfl) ⟨306713, by rfl⟩ : syracuseStep 1635805 = 613427) (by norm_num)
theorem B1938917 : Blo 1291964 1938917 := bbase (se 4 (by rfl) ⟨181773, by rfl⟩ : syracuseStep 1938917 = 363547) (by norm_num)
theorem B1455601 : Blo 1291964 1455601 := bbase (se 2 (by rfl) ⟨545850, by rfl⟩ : syracuseStep 1455601 = 1091701) (by norm_num)
theorem B1938941 : Blo 1291964 1938941 := bbase (se 3 (by rfl) ⟨363551, by rfl⟩ : syracuseStep 1938941 = 727103) (by norm_num)
theorem B3274253 : Blo 1291964 3274253 := bbase (se 3 (by rfl) ⟨613922, by rfl⟩ : syracuseStep 3274253 = 1227845) (by norm_num)
theorem B1938965 : Blo 1291964 1938965 := bbase (se 6 (by rfl) ⟨45444, by rfl⟩ : syracuseStep 1938965 = 90889) (by norm_num)
theorem B1455637 : Blo 1291964 1455637 := bbase (se 6 (by rfl) ⟨34116, by rfl⟩ : syracuseStep 1455637 = 68233) (by norm_num)
theorem B1938989 : Blo 1291964 1938989 := bbase (se 3 (by rfl) ⟨363560, by rfl⟩ : syracuseStep 1938989 = 727121) (by norm_num)
theorem B1455673 : Blo 1291964 1455673 := bbase (se 2 (by rfl) ⟨545877, by rfl⟩ : syracuseStep 1455673 = 1091755) (by norm_num)
theorem B1939013 : Blo 1291964 1939013 := bbase (se 4 (by rfl) ⟨181782, by rfl⟩ : syracuseStep 1939013 = 363565) (by norm_num)
theorem B1939037 : Blo 1291964 1939037 := bbase (se 3 (by rfl) ⟨363569, by rfl⟩ : syracuseStep 1939037 = 727139) (by norm_num)
theorem B1455709 : Blo 1291964 1455709 := bbase (se 3 (by rfl) ⟨272945, by rfl⟩ : syracuseStep 1455709 = 545891) (by norm_num)
theorem B4658789 : Blo 1291964 4658789 := bbase (se 4 (by rfl) ⟨436761, by rfl⟩ : syracuseStep 4658789 = 873523) (by norm_num)
theorem B1939061 : Blo 1291964 1939061 := bbase (se 5 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 1939061 = 181787) (by norm_num)
theorem B1635977 : Blo 1291964 1635977 := bbase (se 2 (by rfl) ⟨613491, by rfl⟩ : syracuseStep 1635977 = 1226983) (by norm_num)
theorem B1939085 : Blo 1291964 1939085 := bbase (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) (by norm_num)
theorem B2455181 : Blo 1291964 2455181 := bbase (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) (by norm_num)
theorem B1939109 : Blo 1291964 1939109 := bbase (se 4 (by rfl) ⟨181791, by rfl⟩ : syracuseStep 1939109 = 363583) (by norm_num)
theorem B2487989 : Blo 1291964 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B1939133 : Blo 1291964 1939133 := bbase (se 3 (by rfl) ⟨363587, by rfl⟩ : syracuseStep 1939133 = 727175) (by norm_num)
theorem B1636033 : Blo 1291964 1636033 := bbase (se 2 (by rfl) ⟨613512, by rfl⟩ : syracuseStep 1636033 = 1227025) (by norm_num)
theorem B3274445 : Blo 1291964 3274445 := bbase (se 3 (by rfl) ⟨613958, by rfl⟩ : syracuseStep 3274445 = 1227917) (by norm_num)
theorem B1939157 : Blo 1291964 1939157 := bbase (se 7 (by rfl) ⟨22724, by rfl⟩ : syracuseStep 1939157 = 45449) (by norm_num)
theorem B1939181 : Blo 1291964 1939181 := bbase (se 3 (by rfl) ⟨363596, by rfl⟩ : syracuseStep 1939181 = 727193) (by norm_num)
theorem B1939205 : Blo 1291964 1939205 := bbase (se 4 (by rfl) ⟨181800, by rfl⟩ : syracuseStep 1939205 = 363601) (by norm_num)
theorem B25196309 : Blo 1291964 25196309 := bbase (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) (by norm_num)
theorem B1939229 : Blo 1291964 1939229 := bbase (se 3 (by rfl) ⟨363605, by rfl⟩ : syracuseStep 1939229 = 727211) (by norm_num)
theorem B1636129 : Blo 1291964 1636129 := bbase (se 2 (by rfl) ⟨613548, by rfl⟩ : syracuseStep 1636129 = 1227097) (by norm_num)
theorem B1939253 : Blo 1291964 1939253 := bbase (se 5 (by rfl) ⟨90902, by rfl⟩ : syracuseStep 1939253 = 181805) (by norm_num)
theorem B1939277 : Blo 1291964 1939277 := bbase (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) (by norm_num)
theorem B4364117 : Blo 1291964 4364117 := bbase (se 9 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 4364117 = 25571) (by norm_num)
theorem B1939301 : Blo 1291964 1939301 := bbase (se 4 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 1939301 = 363619) (by norm_num)
theorem B1939325 : Blo 1291964 1939325 := bbase (se 3 (by rfl) ⟨363623, by rfl⟩ : syracuseStep 1939325 = 727247) (by norm_num)
theorem B1939349 : Blo 1291964 1939349 := bbase (se 6 (by rfl) ⟨45453, by rfl⟩ : syracuseStep 1939349 = 90907) (by norm_num)
theorem B1939373 : Blo 1291964 1939373 := bbase (se 3 (by rfl) ⟨363632, by rfl⟩ : syracuseStep 1939373 = 727265) (by norm_num)
theorem B1939397 : Blo 1291964 1939397 := bbase (se 4 (by rfl) ⟨181818, by rfl⟩ : syracuseStep 1939397 = 363637) (by norm_num)
theorem B1636301 : Blo 1291964 1636301 := bbase (se 3 (by rfl) ⟨306806, by rfl⟩ : syracuseStep 1636301 = 613613) (by norm_num)
theorem B13277141 : Blo 1291964 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B1939421 : Blo 1291964 1939421 := bbase (se 3 (by rfl) ⟨363641, by rfl⟩ : syracuseStep 1939421 = 727283) (by norm_num)
theorem B1939445 : Blo 1291964 1939445 := bbase (se 5 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 1939445 = 181823) (by norm_num)
theorem B1636357 : Blo 1291964 1636357 := bbase (se 4 (by rfl) ⟨153408, by rfl⟩ : syracuseStep 1636357 = 306817) (by norm_num)
theorem B1939469 : Blo 1291964 1939469 := bbase (se 3 (by rfl) ⟨363650, by rfl⟩ : syracuseStep 1939469 = 727301) (by norm_num)
theorem B2488333 : Blo 1291964 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B4659221 : Blo 1291964 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B1939493 : Blo 1291964 1939493 := bbase (se 4 (by rfl) ⟨181827, by rfl⟩ : syracuseStep 1939493 = 363655) (by norm_num)
theorem B3495973 : Blo 1291964 3495973 := bbase (se 4 (by rfl) ⟨327747, by rfl⟩ : syracuseStep 3495973 = 655495) (by norm_num)
theorem B6215717 : Blo 1291964 6215717 := bbase (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) (by norm_num)
theorem B3274789 : Blo 1291964 3274789 := bbase (se 4 (by rfl) ⟨307011, by rfl⟩ : syracuseStep 3274789 = 614023) (by norm_num)
theorem B1939517 : Blo 1291964 1939517 := bbase (se 3 (by rfl) ⟨363659, by rfl⟩ : syracuseStep 1939517 = 727319) (by norm_num)
theorem B1841221 : Blo 1291964 1841221 := bbase (se 4 (by rfl) ⟨172614, by rfl⟩ : syracuseStep 1841221 = 345229) (by norm_num)
theorem B1939541 : Blo 1291964 1939541 := bbase (se 8 (by rfl) ⟨11364, by rfl⟩ : syracuseStep 1939541 = 22729) (by norm_num)
theorem B1636453 : Blo 1291964 1636453 := bbase (se 4 (by rfl) ⟨153417, by rfl⟩ : syracuseStep 1636453 = 306835) (by norm_num)
theorem B1939565 : Blo 1291964 1939565 := bbase (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) (by norm_num)
theorem B4143221 : Blo 1291964 4143221 := bbase (se 5 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 4143221 = 388427) (by norm_num)
theorem B1939589 : Blo 1291964 1939589 := bbase (se 4 (by rfl) ⟨181836, by rfl⟩ : syracuseStep 1939589 = 363673) (by norm_num)
theorem B3274901 : Blo 1291964 3274901 := bbase (se 6 (by rfl) ⟨76755, by rfl⟩ : syracuseStep 3274901 = 153511) (by norm_num)
theorem B1939613 : Blo 1291964 1939613 := bbase (se 3 (by rfl) ⟨363677, by rfl⟩ : syracuseStep 1939613 = 727355) (by norm_num)
theorem B1939637 : Blo 1291964 1939637 := bbase (se 5 (by rfl) ⟨90920, by rfl⟩ : syracuseStep 1939637 = 181841) (by norm_num)
theorem B1939661 : Blo 1291964 1939661 := bbase (se 3 (by rfl) ⟨363686, by rfl⟩ : syracuseStep 1939661 = 727373) (by norm_num)
theorem B1939685 : Blo 1291964 1939685 := bbase (se 4 (by rfl) ⟨181845, by rfl⟩ : syracuseStep 1939685 = 363691) (by norm_num)
theorem B1939709 : Blo 1291964 1939709 := bbase (se 3 (by rfl) ⟨363695, by rfl⟩ : syracuseStep 1939709 = 727391) (by norm_num)
theorem B4364549 : Blo 1291964 4364549 := bbase (se 4 (by rfl) ⟨409176, by rfl⟩ : syracuseStep 4364549 = 818353) (by norm_num)
theorem B1636625 : Blo 1291964 1636625 := bbase (se 2 (by rfl) ⟨613734, by rfl⟩ : syracuseStep 1636625 = 1227469) (by norm_num)
theorem B1939733 : Blo 1291964 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B3684629 : Blo 1291964 3684629 := bbase (se 6 (by rfl) ⟨86358, by rfl⟩ : syracuseStep 3684629 = 172717) (by norm_num)
theorem B1939757 : Blo 1291964 1939757 := bbase (se 3 (by rfl) ⟨363704, by rfl⟩ : syracuseStep 1939757 = 727409) (by norm_num)
theorem B1939781 : Blo 1291964 1939781 := bbase (se 4 (by rfl) ⟨181854, by rfl⟩ : syracuseStep 1939781 = 363709) (by norm_num)
theorem B1636681 : Blo 1291964 1636681 := bbase (se 2 (by rfl) ⟨613755, by rfl⟩ : syracuseStep 1636681 = 1227511) (by norm_num)
theorem B3275093 : Blo 1291964 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B1939805 : Blo 1291964 1939805 := bbase (se 3 (by rfl) ⟨363713, by rfl⟩ : syracuseStep 1939805 = 727427) (by norm_num)
theorem B2070893 : Blo 1291964 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B1939829 : Blo 1291964 1939829 := bbase (se 5 (by rfl) ⟨90929, by rfl⟩ : syracuseStep 1939829 = 181859) (by norm_num)
theorem B2455933 : Blo 1291964 2455933 := bbase (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) (by norm_num)
theorem B1939853 : Blo 1291964 1939853 := bbase (se 3 (by rfl) ⟨363722, by rfl⟩ : syracuseStep 1939853 = 727445) (by norm_num)
theorem B1841557 : Blo 1291964 1841557 := bbase (se 6 (by rfl) ⟨43161, by rfl⟩ : syracuseStep 1841557 = 86323) (by norm_num)
theorem B1939877 : Blo 1291964 1939877 := bbase (se 4 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 1939877 = 363727) (by norm_num)
theorem B1636777 : Blo 1291964 1636777 := bbase (se 2 (by rfl) ⟨613791, by rfl⟩ : syracuseStep 1636777 = 1227583) (by norm_num)
theorem B1939901 : Blo 1291964 1939901 := bbase (se 3 (by rfl) ⟨363731, by rfl⟩ : syracuseStep 1939901 = 727463) (by norm_num)
theorem B1939925 : Blo 1291964 1939925 := bbase (se 7 (by rfl) ⟨22733, by rfl⟩ : syracuseStep 1939925 = 45467) (by norm_num)
theorem B2800093 : Blo 1291964 2800093 := bbase (se 3 (by rfl) ⟨525017, by rfl⟩ : syracuseStep 2800093 = 1050035) (by norm_num)
theorem B1939949 : Blo 1291964 1939949 := bbase (se 3 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 1939949 = 727481) (by norm_num)
theorem B7363061 : Blo 1291964 7363061 := bbase (se 5 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 7363061 = 690287) (by norm_num)
theorem B1939973 : Blo 1291964 1939973 := bbase (se 4 (by rfl) ⟨181872, by rfl⟩ : syracuseStep 1939973 = 363745) (by norm_num)
theorem B2456077 : Blo 1291964 2456077 := bbase (se 3 (by rfl) ⟨460514, by rfl⟩ : syracuseStep 2456077 = 921029) (by norm_num)
theorem B1939997 : Blo 1291964 1939997 := bbase (se 3 (by rfl) ⟨363749, by rfl⟩ : syracuseStep 1939997 = 727499) (by norm_num)
theorem B1940021 : Blo 1291964 1940021 := bbase (se 5 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 1940021 = 181877) (by norm_num)
theorem B1940045 : Blo 1291964 1940045 := bbase (se 3 (by rfl) ⟨363758, by rfl⟩ : syracuseStep 1940045 = 727517) (by norm_num)
theorem B4659797 : Blo 1291964 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B1636949 : Blo 1291964 1636949 := bbase (se 8 (by rfl) ⟨9591, by rfl⟩ : syracuseStep 1636949 = 19183) (by norm_num)
theorem B1940069 : Blo 1291964 1940069 := bbase (se 4 (by rfl) ⟨181881, by rfl⟩ : syracuseStep 1940069 = 363763) (by norm_num)
theorem B1841773 : Blo 1291964 1841773 := bbase (se 3 (by rfl) ⟨345332, by rfl⟩ : syracuseStep 1841773 = 690665) (by norm_num)
theorem B6543989 : Blo 1291964 6543989 := bbase (se 5 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 6543989 = 613499) (by norm_num)
theorem B1940093 : Blo 1291964 1940093 := bbase (se 3 (by rfl) ⟨363767, by rfl⟩ : syracuseStep 1940093 = 727535) (by norm_num)
theorem B1637005 : Blo 1291964 1637005 := bbase (se 3 (by rfl) ⟨306938, by rfl⟩ : syracuseStep 1637005 = 613877) (by norm_num)
theorem B5241493 : Blo 1291964 5241493 := bbase (se 6 (by rfl) ⟨122847, by rfl⟩ : syracuseStep 5241493 = 245695) (by norm_num)
theorem B1940117 : Blo 1291964 1940117 := bbase (se 6 (by rfl) ⟨45471, by rfl⟩ : syracuseStep 1940117 = 90943) (by norm_num)
theorem B1940141 : Blo 1291964 1940141 := bbase (se 3 (by rfl) ⟨363776, by rfl⟩ : syracuseStep 1940141 = 727553) (by norm_num)
theorem B2456237 : Blo 1291964 2456237 := bbase (se 3 (by rfl) ⟨460544, by rfl⟩ : syracuseStep 2456237 = 921089) (by norm_num)
theorem B4364981 : Blo 1291964 4364981 := bbase (se 5 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 4364981 = 409217) (by norm_num)
theorem B5896901 : Blo 1291964 5896901 := bbase (se 4 (by rfl) ⟨552834, by rfl⟩ : syracuseStep 5896901 = 1105669) (by norm_num)
theorem B1940165 : Blo 1291964 1940165 := bbase (se 4 (by rfl) ⟨181890, by rfl⟩ : syracuseStep 1940165 = 363781) (by norm_num)
theorem B1940189 : Blo 1291964 1940189 := bbase (se 3 (by rfl) ⟨363785, by rfl⟩ : syracuseStep 1940189 = 727571) (by norm_num)
theorem B1637101 : Blo 1291964 1637101 := bbase (se 3 (by rfl) ⟨306956, by rfl⟩ : syracuseStep 1637101 = 613913) (by norm_num)
theorem B1940213 : Blo 1291964 1940213 := bbase (se 5 (by rfl) ⟨90947, by rfl⟩ : syracuseStep 1940213 = 181895) (by norm_num)
theorem B3496709 : Blo 1291964 3496709 := bbase (se 4 (by rfl) ⟨327816, by rfl⟩ : syracuseStep 3496709 = 655633) (by norm_num)
theorem B1940237 : Blo 1291964 1940237 := bbase (se 3 (by rfl) ⟨363794, by rfl⟩ : syracuseStep 1940237 = 727589) (by norm_num)
theorem B2620181 : Blo 1291964 2620181 := bbase (se 6 (by rfl) ⟨61410, by rfl⟩ : syracuseStep 2620181 = 122821) (by norm_num)
theorem B1940261 : Blo 1291964 1940261 := bbase (se 4 (by rfl) ⟨181899, by rfl⟩ : syracuseStep 1940261 = 363799) (by norm_num)
theorem B1940285 : Blo 1291964 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B2456381 : Blo 1291964 2456381 := bbase (se 3 (by rfl) ⟨460571, by rfl⟩ : syracuseStep 2456381 = 921143) (by norm_num)
theorem B1940309 : Blo 1291964 1940309 := bbase (se 9 (by rfl) ⟨5684, by rfl⟩ : syracuseStep 1940309 = 11369) (by norm_num)
theorem B2906981 : Blo 1291964 2906981 := bbase (se 4 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 2906981 = 545059) (by norm_num)
theorem B1940333 : Blo 1291964 1940333 := bbase (se 3 (by rfl) ⟨363812, by rfl⟩ : syracuseStep 1940333 = 727625) (by norm_num)
theorem B1940357 : Blo 1291964 1940357 := bbase (se 4 (by rfl) ⟨181908, by rfl⟩ : syracuseStep 1940357 = 363817) (by norm_num)
theorem B1637273 : Blo 1291964 1637273 := bbase (se 2 (by rfl) ⟨613977, by rfl⟩ : syracuseStep 1637273 = 1227955) (by norm_num)
theorem B1940381 : Blo 1291964 1940381 := bbase (se 3 (by rfl) ⟨363821, by rfl⟩ : syracuseStep 1940381 = 727643) (by norm_num)
theorem B2907053 : Blo 1291964 2907053 := bbase (se 3 (by rfl) ⟨545072, by rfl⟩ : syracuseStep 2907053 = 1090145) (by norm_num)
theorem B1940405 : Blo 1291964 1940405 := bbase (se 5 (by rfl) ⟨90956, by rfl⟩ : syracuseStep 1940405 = 181913) (by norm_num)
theorem B1940429 : Blo 1291964 1940429 := bbase (se 3 (by rfl) ⟨363830, by rfl⟩ : syracuseStep 1940429 = 727661) (by norm_num)
theorem B2243533 : Blo 1291964 2243533 := bbase (se 3 (by rfl) ⟨420662, by rfl⟩ : syracuseStep 2243533 = 841325) (by norm_num)
theorem B1637329 : Blo 1291964 1637329 := bbase (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) (by norm_num)
theorem B2759645 : Blo 1291964 2759645 := bbase (se 3 (by rfl) ⟨517433, by rfl⟩ : syracuseStep 2759645 = 1034867) (by norm_num)
theorem B1940453 : Blo 1291964 1940453 := bbase (se 4 (by rfl) ⟨181917, by rfl⟩ : syracuseStep 1940453 = 363835) (by norm_num)
theorem B1842149 : Blo 1291964 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B2907125 : Blo 1291964 2907125 := bbase (se 5 (by rfl) ⟨136271, by rfl⟩ : syracuseStep 2907125 = 272543) (by norm_num)
theorem B1940477 : Blo 1291964 1940477 := bbase (se 3 (by rfl) ⟨363839, by rfl⟩ : syracuseStep 1940477 = 727679) (by norm_num)
theorem B1940501 : Blo 1291964 1940501 := bbase (se 6 (by rfl) ⟨45480, by rfl⟩ : syracuseStep 1940501 = 90961) (by norm_num)
theorem B3030053 : Blo 1291964 3030053 := bbase (se 4 (by rfl) ⟨284067, by rfl⟩ : syracuseStep 3030053 = 568135) (by norm_num)
theorem B1940525 : Blo 1291964 1940525 := bbase (se 3 (by rfl) ⟨363848, by rfl⟩ : syracuseStep 1940525 = 727697) (by norm_num)
theorem B1637425 : Blo 1291964 1637425 := bbase (se 2 (by rfl) ⟨614034, by rfl⟩ : syracuseStep 1637425 = 1228069) (by norm_num)
theorem B2907197 : Blo 1291964 2907197 := bbase (se 3 (by rfl) ⟨545099, by rfl⟩ : syracuseStep 2907197 = 1090199) (by norm_num)
theorem B1940549 : Blo 1291964 1940549 := bbase (se 4 (by rfl) ⟨181926, by rfl⟩ : syracuseStep 1940549 = 363853) (by norm_num)
theorem B1940573 : Blo 1291964 1940573 := bbase (se 3 (by rfl) ⟨363857, by rfl⟩ : syracuseStep 1940573 = 727715) (by norm_num)
theorem B4365413 : Blo 1291964 4365413 := bbase (se 4 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 4365413 = 818515) (by norm_num)
theorem B2759789 : Blo 1291964 2759789 := bbase (se 3 (by rfl) ⟨517460, by rfl⟩ : syracuseStep 2759789 = 1034921) (by norm_num)
theorem B1940597 : Blo 1291964 1940597 := bbase (se 5 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 1940597 = 181931) (by norm_num)
theorem B2907269 : Blo 1291964 2907269 := bbase (se 4 (by rfl) ⟨272556, by rfl⟩ : syracuseStep 2907269 = 545113) (by norm_num)
theorem B1965197 : Blo 1291964 1965197 := bbase (se 3 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 1965197 = 736949) (by norm_num)
theorem B1940621 : Blo 1291964 1940621 := bbase (se 3 (by rfl) ⟨363866, by rfl⟩ : syracuseStep 1940621 = 727733) (by norm_num)
theorem B1940645 : Blo 1291964 1940645 := bbase (se 4 (by rfl) ⟨181935, by rfl⟩ : syracuseStep 1940645 = 363871) (by norm_num)
theorem B1940669 : Blo 1291964 1940669 := bbase (se 3 (by rfl) ⟨363875, by rfl⟩ : syracuseStep 1940669 = 727751) (by norm_num)
theorem B1400005 : Blo 1291964 1400005 := bbase (se 4 (by rfl) ⟨131250, by rfl⟩ : syracuseStep 1400005 = 262501) (by norm_num)
theorem B2907341 : Blo 1291964 2907341 := bbase (se 3 (by rfl) ⟨545126, by rfl⟩ : syracuseStep 2907341 = 1090253) (by norm_num)
theorem B1965269 : Blo 1291964 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B1940693 : Blo 1291964 1940693 := bbase (se 7 (by rfl) ⟨22742, by rfl⟩ : syracuseStep 1940693 = 45485) (by norm_num)
theorem B1637597 : Blo 1291964 1637597 := bbase (se 3 (by rfl) ⟨307049, by rfl⟩ : syracuseStep 1637597 = 614099) (by norm_num)
theorem B1940717 : Blo 1291964 1940717 := bbase (se 3 (by rfl) ⟨363884, by rfl⟩ : syracuseStep 1940717 = 727769) (by norm_num)
theorem B1940741 : Blo 1291964 1940741 := bbase (se 4 (by rfl) ⟨181944, by rfl⟩ : syracuseStep 1940741 = 363889) (by norm_num)
theorem B1309969 : Blo 1291964 1309969 := bbase (se 2 (by rfl) ⟨491238, by rfl⟩ : syracuseStep 1309969 = 982477) (by norm_num)
theorem B2907413 : Blo 1291964 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B1637653 : Blo 1291964 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B1940765 : Blo 1291964 1940765 := bbase (se 3 (by rfl) ⟨363893, by rfl⟩ : syracuseStep 1940765 = 727787) (by norm_num)
theorem B4906277 : Blo 1291964 4906277 := bbase (se 4 (by rfl) ⟨459963, by rfl⟩ : syracuseStep 4906277 = 919927) (by norm_num)
theorem B1940789 : Blo 1291964 1940789 := bbase (se 5 (by rfl) ⟨90974, by rfl⟩ : syracuseStep 1940789 = 181949) (by norm_num)
theorem B1940813 : Blo 1291964 1940813 := bbase (se 3 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 1940813 = 727805) (by norm_num)
theorem B2694485 : Blo 1291964 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B2907485 : Blo 1291964 2907485 := bbase (se 3 (by rfl) ⟨545153, by rfl⟩ : syracuseStep 2907485 = 1090307) (by norm_num)
theorem B1940837 : Blo 1291964 1940837 := bbase (se 4 (by rfl) ⟨181953, by rfl⟩ : syracuseStep 1940837 = 363907) (by norm_num)
theorem B1940861 : Blo 1291964 1940861 := bbase (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) (by norm_num)
theorem B1940885 : Blo 1291964 1940885 := bbase (se 6 (by rfl) ⟨45489, by rfl⟩ : syracuseStep 1940885 = 90979) (by norm_num)
theorem B2907557 : Blo 1291964 2907557 := bbase (se 4 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 2907557 = 545167) (by norm_num)
theorem B1940909 : Blo 1291964 1940909 := bbase (se 3 (by rfl) ⟨363920, by rfl⟩ : syracuseStep 1940909 = 727841) (by norm_num)
theorem B1940933 : Blo 1291964 1940933 := bbase (se 4 (by rfl) ⟨181962, by rfl⟩ : syracuseStep 1940933 = 363925) (by norm_num)
theorem B2760149 : Blo 1291964 2760149 := bbase (se 7 (by rfl) ⟨32345, by rfl⟩ : syracuseStep 2760149 = 64691) (by norm_num)
theorem B18906581 : Blo 1291964 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B2907629 : Blo 1291964 2907629 := bbase (se 3 (by rfl) ⟨545180, by rfl⟩ : syracuseStep 2907629 = 1090361) (by norm_num)
theorem B4365845 : Blo 1291964 4365845 := bbase (se 6 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 4365845 = 204649) (by norm_num)
theorem B2907701 : Blo 1291964 2907701 := bbase (se 5 (by rfl) ⟨136298, by rfl⟩ : syracuseStep 2907701 = 272597) (by norm_num)
theorem B4906565 : Blo 1291964 4906565 := bbase (se 4 (by rfl) ⟨459990, by rfl⟩ : syracuseStep 4906565 = 919981) (by norm_num)
theorem B2907773 : Blo 1291964 2907773 := bbase (se 3 (by rfl) ⟨545207, by rfl⟩ : syracuseStep 2907773 = 1090415) (by norm_num)
theorem B2907845 : Blo 1291964 2907845 := bbase (se 4 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 2907845 = 545221) (by norm_num)
theorem B2211557 : Blo 1291964 2211557 := bbase (se 4 (by rfl) ⟨207333, by rfl⟩ : syracuseStep 2211557 = 414667) (by norm_num)
theorem B2907917 : Blo 1291964 2907917 := bbase (se 3 (by rfl) ⟨545234, by rfl⟩ : syracuseStep 2907917 = 1090469) (by norm_num)
theorem B10485557 : Blo 1291964 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B4972373 : Blo 1291964 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B2907989 : Blo 1291964 2907989 := bbase (se 9 (by rfl) ⟨8519, by rfl⟩ : syracuseStep 2907989 = 17039) (by norm_num)
theorem B2072405 : Blo 1291964 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B8290133 : Blo 1291964 8290133 := bbase (se 9 (by rfl) ⟨24287, by rfl⟩ : syracuseStep 8290133 = 48575) (by norm_num)
theorem B3932021 : Blo 1291964 3932021 := bbase (se 5 (by rfl) ⟨184313, by rfl⟩ : syracuseStep 3932021 = 368627) (by norm_num)
theorem B6545285 : Blo 1291964 6545285 := bbase (se 4 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 6545285 = 1227241) (by norm_num)
theorem B2908061 : Blo 1291964 2908061 := bbase (se 3 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 2908061 = 1090523) (by norm_num)
theorem B1474481 : Blo 1291964 1474481 := bbase (se 2 (by rfl) ⟨552930, by rfl⟩ : syracuseStep 1474481 = 1105861) (by norm_num)
theorem B4366277 : Blo 1291964 4366277 := bbase (se 4 (by rfl) ⟨409338, by rfl⟩ : syracuseStep 4366277 = 818677) (by norm_num)
theorem B2908133 : Blo 1291964 2908133 := bbase (se 4 (by rfl) ⟨272637, by rfl⟩ : syracuseStep 2908133 = 545275) (by norm_num)
theorem B3317777 : Blo 1291964 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B4661297 : Blo 1291964 4661297 := bstep (se 2 (by rfl) ⟨1747986, by rfl⟩ : syracuseStep 4661297 = 3495973) B3495973
theorem B4366385 : Blo 1291964 4366385 := bstep (se 2 (by rfl) ⟨1637394, by rfl⟩ : syracuseStep 4366385 = 3274789) B3274789
theorem B2908241 : Blo 1291964 2908241 := bstep (se 2 (by rfl) ⟨1090590, by rfl⟩ : syracuseStep 2908241 = 2181181) B2181181
theorem B2908259 : Blo 1291964 2908259 := bstep (se 1 (by rfl) ⟨2181194, by rfl⟩ : syracuseStep 2908259 = 4362389) B4362389
theorem B5595299 : Blo 1291964 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B4907249 : Blo 1291964 4907249 := bstep (se 2 (by rfl) ⟨1840218, by rfl⟩ : syracuseStep 4907249 = 3680437) B3680437
theorem B2908529 : Blo 1291964 2908529 := bstep (se 2 (by rfl) ⟨1090698, by rfl⟩ : syracuseStep 2908529 = 2181397) B2181397
theorem B2908547 : Blo 1291964 2908547 := bstep (se 1 (by rfl) ⟨2181410, by rfl⟩ : syracuseStep 2908547 = 4362821) B4362821
theorem B37806533 : Blo 1291964 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B6545933 : Blo 1291964 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B4366925 : Blo 1291964 4366925 := bstep (se 3 (by rfl) ⟨818798, by rfl⟩ : syracuseStep 4366925 = 1637597) B1637597
theorem B1966675 : Blo 1291964 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B1311347 : Blo 1291964 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B4366979 : Blo 1291964 4366979 := bstep (se 1 (by rfl) ⟨3275234, by rfl⟩ : syracuseStep 4366979 = 6550469) B6550469
theorem B2908817 : Blo 1291964 2908817 := bstep (se 2 (by rfl) ⟨1090806, by rfl⟩ : syracuseStep 2908817 = 2181613) B2181613
theorem B1311379 : Blo 1291964 1311379 := bstep (se 1 (by rfl) ⟨983534, by rfl⟩ : syracuseStep 1311379 = 1967069) B1967069
theorem B2908835 : Blo 1291964 2908835 := bstep (se 1 (by rfl) ⟨2181626, by rfl⟩ : syracuseStep 2908835 = 4363253) B4363253
theorem B9814769 : Blo 1291964 9814769 := bstep (se 2 (by rfl) ⟨3680538, by rfl⟩ : syracuseStep 9814769 = 7361077) B7361077
theorem B1327907 : Blo 1291964 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B2909105 : Blo 1291964 2909105 := bstep (se 2 (by rfl) ⟨1090914, by rfl⟩ : syracuseStep 2909105 = 2181829) B2181829
theorem B2909123 : Blo 1291964 2909123 := bstep (se 1 (by rfl) ⟨2181842, by rfl⟩ : syracuseStep 2909123 = 4363685) B4363685
theorem B5522381 : Blo 1291964 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B3105859 : Blo 1291964 3105859 := bstep (se 1 (by rfl) ⟨2329394, by rfl⟩ : syracuseStep 3105859 = 4658789) B4658789
theorem B2180209 : Blo 1291964 2180209 := bstep (se 2 (by rfl) ⟨817578, by rfl⟩ : syracuseStep 2180209 = 1635157) B1635157
theorem B2180243 : Blo 1291964 2180243 := bstep (se 1 (by rfl) ⟨1635182, by rfl⟩ : syracuseStep 2180243 = 3270365) B3270365
theorem B4424867 : Blo 1291964 4424867 := bstep (se 1 (by rfl) ⟨3318650, by rfl⟩ : syracuseStep 4424867 = 6637301) B6637301
theorem B2909393 : Blo 1291964 2909393 := bstep (se 2 (by rfl) ⟨1091022, by rfl⟩ : syracuseStep 2909393 = 2182045) B2182045
theorem B2909411 : Blo 1291964 2909411 := bstep (se 1 (by rfl) ⟨2182058, by rfl⟩ : syracuseStep 2909411 = 4364117) B4364117
theorem B9323747 : Blo 1291964 9323747 := bstep (se 1 (by rfl) ⟨6992810, by rfl⟩ : syracuseStep 9323747 = 13985621) B13985621
theorem B3679469 : Blo 1291964 3679469 := bstep (se 3 (by rfl) ⟨689900, by rfl⟩ : syracuseStep 3679469 = 1379801) B1379801
theorem B2991377 : Blo 1291964 2991377 := bstep (se 2 (by rfl) ⟨1121766, by rfl⟩ : syracuseStep 2991377 = 2243533) B2243533
theorem B2180371 : Blo 1291964 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B2180513 : Blo 1291964 2180513 := bstep (se 2 (by rfl) ⟨817692, by rfl⟩ : syracuseStep 2180513 = 1635385) B1635385
theorem B2762147 : Blo 1291964 2762147 := bstep (se 1 (by rfl) ⟨2071610, by rfl⟩ : syracuseStep 2762147 = 4143221) B4143221
theorem B2909681 : Blo 1291964 2909681 := bstep (se 2 (by rfl) ⟨1091130, by rfl⟩ : syracuseStep 2909681 = 2182261) B2182261
theorem B2909699 : Blo 1291964 2909699 := bstep (se 1 (by rfl) ⟨2182274, by rfl⟩ : syracuseStep 2909699 = 4364549) B4364549
theorem B2180641 : Blo 1291964 2180641 := bstep (se 2 (by rfl) ⟨817740, by rfl⟩ : syracuseStep 2180641 = 1635481) B1635481
theorem B2180675 : Blo 1291964 2180675 := bstep (se 1 (by rfl) ⟨1635506, by rfl⟩ : syracuseStep 2180675 = 3271013) B3271013
theorem B4908707 : Blo 1291964 4908707 := bstep (se 1 (by rfl) ⟨3681530, by rfl⟩ : syracuseStep 4908707 = 7363061) B7363061
theorem B4908721 : Blo 1291964 4908721 := bstep (se 2 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 4908721 = 3681541) B3681541
theorem B1746625 : Blo 1291964 1746625 := bstep (se 2 (by rfl) ⟨654984, by rfl⟩ : syracuseStep 1746625 = 1309969) B1309969
theorem B2180803 : Blo 1291964 2180803 := bstep (se 1 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 2180803 = 3271205) B3271205
theorem B3106531 : Blo 1291964 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B2909969 : Blo 1291964 2909969 := bstep (se 2 (by rfl) ⟨1091238, by rfl⟩ : syracuseStep 2909969 = 2182477) B2182477
theorem B2909987 : Blo 1291964 2909987 := bstep (se 1 (by rfl) ⟨2182490, by rfl⟩ : syracuseStep 2909987 = 4364981) B4364981
theorem B2180945 : Blo 1291964 2180945 := bstep (se 2 (by rfl) ⟨817854, by rfl⟩ : syracuseStep 2180945 = 1635709) B1635709
theorem B1746787 : Blo 1291964 1746787 := bstep (se 1 (by rfl) ⟨1310090, by rfl⟩ : syracuseStep 1746787 = 2620181) B2620181
theorem B3270577 : Blo 1291964 3270577 := bstep (se 2 (by rfl) ⟨1226466, by rfl⟩ : syracuseStep 3270577 = 2452933) B2452933
theorem B3934129 : Blo 1291964 3934129 := bstep (se 2 (by rfl) ⟨1475298, by rfl⟩ : syracuseStep 3934129 = 2950597) B2950597
theorem B2328515 : Blo 1291964 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B2181073 : Blo 1291964 2181073 := bstep (se 2 (by rfl) ⟨817902, by rfl⟩ : syracuseStep 2181073 = 1635805) B1635805
theorem B7358435 : Blo 1291964 7358435 := bstep (se 1 (by rfl) ⟨5518826, by rfl⟩ : syracuseStep 7358435 = 11037653) B11037653
theorem B2181107 : Blo 1291964 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B9324557 : Blo 1291964 9324557 := bstep (se 3 (by rfl) ⟨1748354, by rfl⟩ : syracuseStep 9324557 = 3496709) B3496709
theorem B2910257 : Blo 1291964 2910257 := bstep (se 2 (by rfl) ⟨1091346, by rfl⟩ : syracuseStep 2910257 = 2182693) B2182693
theorem B2910275 : Blo 1291964 2910275 := bstep (se 1 (by rfl) ⟨2182706, by rfl⟩ : syracuseStep 2910275 = 4365413) B4365413
theorem B2328689 : Blo 1291964 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B2181235 : Blo 1291964 2181235 := bstep (se 1 (by rfl) ⟨1635926, by rfl⟩ : syracuseStep 2181235 = 3271853) B3271853
theorem B3106993 : Blo 1291964 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B3270851 : Blo 1291964 3270851 := bstep (se 1 (by rfl) ⟨2453138, by rfl⟩ : syracuseStep 3270851 = 4906277) B4906277
theorem B1796323 : Blo 1291964 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B2181377 : Blo 1291964 2181377 := bstep (se 2 (by rfl) ⟨818016, by rfl⟩ : syracuseStep 2181377 = 1636033) B1636033
theorem B3107089 : Blo 1291964 3107089 := bstep (se 2 (by rfl) ⟨1165158, by rfl⟩ : syracuseStep 3107089 = 2330317) B2330317
theorem B8284493 : Blo 1291964 8284493 := bstep (se 3 (by rfl) ⟨1553342, by rfl⟩ : syracuseStep 8284493 = 3106685) B3106685
theorem B2910545 : Blo 1291964 2910545 := bstep (se 2 (by rfl) ⟨1091454, by rfl⟩ : syracuseStep 2910545 = 2182909) B2182909
theorem B2910563 : Blo 1291964 2910563 := bstep (se 1 (by rfl) ⟨2182922, by rfl⟩ : syracuseStep 2910563 = 4365845) B4365845
theorem B2181505 : Blo 1291964 2181505 := bstep (se 2 (by rfl) ⟨818064, by rfl⟩ : syracuseStep 2181505 = 1636129) B1636129
theorem B3271043 : Blo 1291964 3271043 := bstep (se 1 (by rfl) ⟨2453282, by rfl⟩ : syracuseStep 3271043 = 4906565) B4906565
theorem B3680653 : Blo 1291964 3680653 := bstep (se 3 (by rfl) ⟨690122, by rfl⟩ : syracuseStep 3680653 = 1380245) B1380245
theorem B2181539 : Blo 1291964 2181539 := bstep (se 1 (by rfl) ⟨1636154, by rfl⟩ : syracuseStep 2181539 = 3272309) B3272309
theorem B2181667 : Blo 1291964 2181667 := bstep (se 1 (by rfl) ⟨1636250, by rfl⟩ : syracuseStep 2181667 = 3272501) B3272501
theorem B6990371 : Blo 1291964 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B2910833 : Blo 1291964 2910833 := bstep (se 2 (by rfl) ⟨1091562, by rfl⟩ : syracuseStep 2910833 = 2183125) B2183125
theorem B2910851 : Blo 1291964 2910851 := bstep (se 1 (by rfl) ⟨2183138, by rfl⟩ : syracuseStep 2910851 = 4366277) B4366277
theorem B4360877 : Blo 1291964 4360877 := bstep (se 3 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 4360877 = 1635329) B1635329
theorem B2181809 : Blo 1291964 2181809 := bstep (se 2 (by rfl) ⟨818178, by rfl⟩ : syracuseStep 2181809 = 1636357) B1636357
theorem B5245645 : Blo 1291964 5245645 := bstep (se 3 (by rfl) ⟨983558, by rfl⟩ : syracuseStep 5245645 = 1967117) B1967117
theorem B4360931 : Blo 1291964 4360931 := bstep (se 1 (by rfl) ⟨3270698, by rfl⟩ : syracuseStep 4360931 = 6541397) B6541397
theorem B55896803 : Blo 1291964 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B6990563 : Blo 1291964 6990563 := bstep (se 1 (by rfl) ⟨5242922, by rfl⟩ : syracuseStep 6990563 = 10485845) B10485845
theorem B8080141 : Blo 1291964 8080141 := bstep (se 3 (by rfl) ⟨1515026, by rfl⟩ : syracuseStep 8080141 = 3030053) B3030053
theorem B2181937 : Blo 1291964 2181937 := bstep (se 2 (by rfl) ⟨818226, by rfl⟩ : syracuseStep 2181937 = 1636453) B1636453
theorem B7867205 : Blo 1291964 7867205 := bstep (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) B1475101
theorem B2181971 : Blo 1291964 2181971 := bstep (se 1 (by rfl) ⟨1636478, by rfl⟩ : syracuseStep 2181971 = 3272957) B3272957
theorem B2329489 : Blo 1291964 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B2911121 : Blo 1291964 2911121 := bstep (se 2 (by rfl) ⟨1091670, by rfl⟩ : syracuseStep 2911121 = 2183341) B2183341
theorem B1616803 : Blo 1291964 1616803 := bstep (se 1 (by rfl) ⟨1212602, by rfl⟩ : syracuseStep 1616803 = 2425205) B2425205
theorem B2911139 : Blo 1291964 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B2100161 : Blo 1291964 2100161 := bstep (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) B1575121
theorem B7359437 : Blo 1291964 7359437 := bstep (se 3 (by rfl) ⟨1379894, by rfl⟩ : syracuseStep 7359437 = 2759789) B2759789
theorem B4139981 : Blo 1291964 4139981 := bstep (se 3 (by rfl) ⟨776246, by rfl⟩ : syracuseStep 4139981 = 1552493) B1552493
theorem B2182099 : Blo 1291964 2182099 := bstep (se 1 (by rfl) ⟨1636574, by rfl⟩ : syracuseStep 2182099 = 3273149) B3273149
theorem B4361201 : Blo 1291964 4361201 := bstep (se 2 (by rfl) ⟨1635450, by rfl⟩ : syracuseStep 4361201 = 3270901) B3270901
theorem B2182241 : Blo 1291964 2182241 := bstep (se 2 (by rfl) ⟨818340, by rfl⟩ : syracuseStep 2182241 = 1636681) B1636681
theorem B4910179 : Blo 1291964 4910179 := bstep (se 1 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 4910179 = 7365269) B7365269
theorem B2911409 : Blo 1291964 2911409 := bstep (se 2 (by rfl) ⟨1091778, by rfl⟩ : syracuseStep 2911409 = 2183557) B2183557
theorem B2182369 : Blo 1291964 2182369 := bstep (se 2 (by rfl) ⟨818388, by rfl⟩ : syracuseStep 2182369 = 1636777) B1636777
theorem B2182403 : Blo 1291964 2182403 := bstep (se 1 (by rfl) ⟨1636802, by rfl⟩ : syracuseStep 2182403 = 3273605) B3273605
theorem B3271985 : Blo 1291964 3271985 := bstep (se 2 (by rfl) ⟨1226994, by rfl⟩ : syracuseStep 3271985 = 2453989) B2453989
theorem B2452835 : Blo 1291964 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B3272035 : Blo 1291964 3272035 := bstep (se 1 (by rfl) ⟨2454026, by rfl⟩ : syracuseStep 3272035 = 4908053) B4908053
theorem B4140401 : Blo 1291964 4140401 := bstep (se 2 (by rfl) ⟨1552650, by rfl⟩ : syracuseStep 4140401 = 3105301) B3105301
theorem B6548849 : Blo 1291964 6548849 := bstep (se 2 (by rfl) ⟨2455818, by rfl⟩ : syracuseStep 6548849 = 4911637) B4911637
theorem B2182531 : Blo 1291964 2182531 := bstep (se 1 (by rfl) ⟨1636898, by rfl⟩ : syracuseStep 2182531 = 3273797) B3273797
theorem B3681713 : Blo 1291964 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B27954629 : Blo 1291964 27954629 := bstep (se 4 (by rfl) ⟨2620746, by rfl⟩ : syracuseStep 27954629 = 5241493) B5241493
theorem B6540749 : Blo 1291964 6540749 := bstep (se 3 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 6540749 = 2452781) B2452781
theorem B3272177 : Blo 1291964 3272177 := bstep (se 2 (by rfl) ⟨1227066, by rfl⟩ : syracuseStep 3272177 = 2454133) B2454133
theorem B4361741 : Blo 1291964 4361741 := bstep (se 3 (by rfl) ⟨817826, by rfl⟩ : syracuseStep 4361741 = 1635653) B1635653
theorem B2330129 : Blo 1291964 2330129 := bstep (se 2 (by rfl) ⟨873798, by rfl⟩ : syracuseStep 2330129 = 1747597) B1747597
theorem B2182673 : Blo 1291964 2182673 := bstep (se 2 (by rfl) ⟨818502, by rfl⟩ : syracuseStep 2182673 = 1637005) B1637005
theorem B1453603 : Blo 1291964 1453603 := bstep (se 1 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 1453603 = 2180405) B2180405
theorem B4361795 : Blo 1291964 4361795 := bstep (se 1 (by rfl) ⟨3271346, by rfl⟩ : syracuseStep 4361795 = 6542693) B6542693
theorem B3542641 : Blo 1291964 3542641 := bstep (se 2 (by rfl) ⟨1328490, by rfl⟩ : syracuseStep 3542641 = 2656981) B2656981
theorem B2182801 : Blo 1291964 2182801 := bstep (se 2 (by rfl) ⟨818550, by rfl⟩ : syracuseStep 2182801 = 1637101) B1637101
theorem B1453747 : Blo 1291964 1453747 := bstep (se 1 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 1453747 = 2180621) B2180621
theorem B2182835 : Blo 1291964 2182835 := bstep (se 1 (by rfl) ⟨1637126, by rfl⟩ : syracuseStep 2182835 = 3274253) B3274253
theorem B16789189 : Blo 1291964 16789189 := bstep (se 4 (by rfl) ⟨1573986, by rfl⟩ : syracuseStep 16789189 = 3147973) B3147973
theorem B12431045 : Blo 1291964 12431045 := bstep (se 4 (by rfl) ⟨1165410, by rfl⟩ : syracuseStep 12431045 = 2330821) B2330821
theorem B1658659 : Blo 1291964 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B2182963 : Blo 1291964 2182963 := bstep (se 1 (by rfl) ⟨1637222, by rfl⟩ : syracuseStep 2182963 = 3274445) B3274445
theorem B1453891 : Blo 1291964 1453891 := bstep (se 1 (by rfl) ⟨1090418, by rfl⟩ : syracuseStep 1453891 = 2180837) B2180837
theorem B4656973 : Blo 1291964 4656973 := bstep (se 3 (by rfl) ⟨873182, by rfl⟩ : syracuseStep 4656973 = 1746365) B1746365
theorem B4362065 : Blo 1291964 4362065 := bstep (se 2 (by rfl) ⟨1635774, by rfl⟩ : syracuseStep 4362065 = 3271549) B3271549
theorem B16797539 : Blo 1291964 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B6991757 : Blo 1291964 6991757 := bstep (se 3 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 6991757 = 2621909) B2621909
theorem B50417549 : Blo 1291964 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B2183105 : Blo 1291964 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1454035 : Blo 1291964 1454035 := bstep (se 1 (by rfl) ⟨1090526, by rfl⟩ : syracuseStep 1454035 = 2181053) B2181053
theorem B8851427 : Blo 1291964 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B2183233 : Blo 1291964 2183233 := bstep (se 2 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 2183233 = 1637425) B1637425
theorem B3682385 : Blo 1291964 3682385 := bstep (se 2 (by rfl) ⟨1380894, by rfl⟩ : syracuseStep 3682385 = 2761789) B2761789
theorem B1454179 : Blo 1291964 1454179 := bstep (se 1 (by rfl) ⟨1090634, by rfl⟩ : syracuseStep 1454179 = 2181269) B2181269
theorem B2183267 : Blo 1291964 2183267 := bstep (se 1 (by rfl) ⟨1637450, by rfl⟩ : syracuseStep 2183267 = 3274901) B3274901
theorem B1552531 : Blo 1291964 1552531 := bstep (se 1 (by rfl) ⟨1164398, by rfl⟩ : syracuseStep 1552531 = 2328797) B2328797
theorem B2183395 : Blo 1291964 2183395 := bstep (se 1 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 2183395 = 3275093) B3275093
theorem B1454323 : Blo 1291964 1454323 := bstep (se 1 (by rfl) ⟨1090742, by rfl⟩ : syracuseStep 1454323 = 2181485) B2181485
theorem B4362605 : Blo 1291964 4362605 := bstep (se 3 (by rfl) ⟨817988, by rfl⟩ : syracuseStep 4362605 = 1635977) B1635977
theorem B2183537 : Blo 1291964 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B1454467 : Blo 1291964 1454467 := bstep (se 1 (by rfl) ⟨1090850, by rfl⟩ : syracuseStep 1454467 = 2181701) B2181701
theorem B2453905 : Blo 1291964 2453905 := bstep (se 2 (by rfl) ⟨920214, by rfl⟩ : syracuseStep 2453905 = 1840429) B1840429
theorem B4362659 : Blo 1291964 4362659 := bstep (se 1 (by rfl) ⟨3271994, by rfl⟩ : syracuseStep 4362659 = 6543989) B6543989
theorem B8393165 : Blo 1291964 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B3273169 : Blo 1291964 3273169 := bstep (se 2 (by rfl) ⟨1227438, by rfl⟩ : syracuseStep 3273169 = 2454877) B2454877
theorem B8286725 : Blo 1291964 8286725 := bstep (se 4 (by rfl) ⟨776880, by rfl⟩ : syracuseStep 8286725 = 1553761) B1553761
theorem B1454611 : Blo 1291964 1454611 := bstep (se 1 (by rfl) ⟨1090958, by rfl⟩ : syracuseStep 1454611 = 2181917) B2181917
theorem B1937969 : Blo 1291964 1937969 := bstep (se 2 (by rfl) ⟨726738, by rfl⟩ : syracuseStep 1937969 = 1453477) B1453477
theorem B1937987 : Blo 1291964 1937987 := bstep (se 1 (by rfl) ⟨1453490, by rfl⟩ : syracuseStep 1937987 = 2906981) B2906981
theorem B1938017 : Blo 1291964 1938017 := bstep (se 2 (by rfl) ⟨726756, by rfl⟩ : syracuseStep 1938017 = 1453513) B1453513
theorem B1938035 : Blo 1291964 1938035 := bstep (se 1 (by rfl) ⟨1453526, by rfl⟩ : syracuseStep 1938035 = 2907053) B2907053
theorem B15127181 : Blo 1291964 15127181 := bstep (se 3 (by rfl) ⟨2836346, by rfl⟩ : syracuseStep 15127181 = 5672693) B5672693
theorem B1938065 : Blo 1291964 1938065 := bstep (se 2 (by rfl) ⟨726774, by rfl⟩ : syracuseStep 1938065 = 1453549) B1453549
theorem B1839763 : Blo 1291964 1839763 := bstep (se 1 (by rfl) ⟨1379822, by rfl⟩ : syracuseStep 1839763 = 2759645) B2759645
theorem B1938083 : Blo 1291964 1938083 := bstep (se 1 (by rfl) ⟨1453562, by rfl⟩ : syracuseStep 1938083 = 2907125) B2907125
theorem B3732131 : Blo 1291964 3732131 := bstep (se 1 (by rfl) ⟨2799098, by rfl⟩ : syracuseStep 3732131 = 5598197) B5598197
theorem B1454755 : Blo 1291964 1454755 := bstep (se 1 (by rfl) ⟨1091066, by rfl⟩ : syracuseStep 1454755 = 2182133) B2182133
theorem B4362929 : Blo 1291964 4362929 := bstep (se 2 (by rfl) ⟨1636098, by rfl⟩ : syracuseStep 4362929 = 3272197) B3272197
theorem B1938113 : Blo 1291964 1938113 := bstep (se 2 (by rfl) ⟨726792, by rfl⟩ : syracuseStep 1938113 = 1453585) B1453585
theorem B11039429 : Blo 1291964 11039429 := bstep (se 4 (by rfl) ⟨1034946, by rfl⟩ : syracuseStep 11039429 = 2069893) B2069893
theorem B1938131 : Blo 1291964 1938131 := bstep (se 1 (by rfl) ⟨1453598, by rfl⟩ : syracuseStep 1938131 = 2907197) B2907197
theorem B3273443 : Blo 1291964 3273443 := bstep (se 1 (by rfl) ⟨2455082, by rfl⟩ : syracuseStep 3273443 = 4910165) B4910165
theorem B1938161 : Blo 1291964 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1938179 : Blo 1291964 1938179 := bstep (se 1 (by rfl) ⟨1453634, by rfl⟩ : syracuseStep 1938179 = 2907269) B2907269
theorem B1938209 : Blo 1291964 1938209 := bstep (se 2 (by rfl) ⟨726828, by rfl⟩ : syracuseStep 1938209 = 1453657) B1453657
theorem B6550307 : Blo 1291964 6550307 := bstep (se 1 (by rfl) ⟨4912730, by rfl⟩ : syracuseStep 6550307 = 9825461) B9825461
theorem B1938227 : Blo 1291964 1938227 := bstep (se 1 (by rfl) ⟨1453670, by rfl⟩ : syracuseStep 1938227 = 2907341) B2907341
theorem B1454899 : Blo 1291964 1454899 := bstep (se 1 (by rfl) ⟨1091174, by rfl⟩ : syracuseStep 1454899 = 2182349) B2182349
theorem B1938257 : Blo 1291964 1938257 := bstep (se 2 (by rfl) ⟨726846, by rfl⟩ : syracuseStep 1938257 = 1453693) B1453693
theorem B1938275 : Blo 1291964 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B3683171 : Blo 1291964 3683171 := bstep (se 1 (by rfl) ⟨2762378, by rfl⟩ : syracuseStep 3683171 = 5524757) B5524757
theorem B1938305 : Blo 1291964 1938305 := bstep (se 2 (by rfl) ⟨726864, by rfl⟩ : syracuseStep 1938305 = 1453729) B1453729
theorem B5526413 : Blo 1291964 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B1938323 : Blo 1291964 1938323 := bstep (se 1 (by rfl) ⟨1453742, by rfl⟩ : syracuseStep 1938323 = 2907485) B2907485
theorem B3273635 : Blo 1291964 3273635 := bstep (se 1 (by rfl) ⟨2455226, by rfl⟩ : syracuseStep 3273635 = 4910453) B4910453
theorem B1938353 : Blo 1291964 1938353 := bstep (se 2 (by rfl) ⟨726882, by rfl⟩ : syracuseStep 1938353 = 1453765) B1453765
theorem B1938371 : Blo 1291964 1938371 := bstep (se 1 (by rfl) ⟨1453778, by rfl⟩ : syracuseStep 1938371 = 2907557) B2907557
theorem B1455043 : Blo 1291964 1455043 := bstep (se 1 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 1455043 = 2182565) B2182565
theorem B1938401 : Blo 1291964 1938401 := bstep (se 2 (by rfl) ⟨726900, by rfl⟩ : syracuseStep 1938401 = 1453801) B1453801
theorem B1840099 : Blo 1291964 1840099 := bstep (se 1 (by rfl) ⟨1380074, by rfl⟩ : syracuseStep 1840099 = 2760149) B2760149
theorem B1938419 : Blo 1291964 1938419 := bstep (se 1 (by rfl) ⟨1453814, by rfl⟩ : syracuseStep 1938419 = 2907629) B2907629
theorem B1938449 : Blo 1291964 1938449 := bstep (se 2 (by rfl) ⟨726918, by rfl⟩ : syracuseStep 1938449 = 1453837) B1453837
theorem B1938467 : Blo 1291964 1938467 := bstep (se 1 (by rfl) ⟨1453850, by rfl⟩ : syracuseStep 1938467 = 2907701) B2907701
theorem B1938497 : Blo 1291964 1938497 := bstep (se 2 (by rfl) ⟨726936, by rfl⟩ : syracuseStep 1938497 = 1453873) B1453873
theorem B1938515 : Blo 1291964 1938515 := bstep (se 1 (by rfl) ⟨1453886, by rfl⟩ : syracuseStep 1938515 = 2907773) B2907773
theorem B1455187 : Blo 1291964 1455187 := bstep (se 1 (by rfl) ⟨1091390, by rfl⟩ : syracuseStep 1455187 = 2182781) B2182781
theorem B1938545 : Blo 1291964 1938545 := bstep (se 2 (by rfl) ⟨726954, by rfl⟩ : syracuseStep 1938545 = 1453909) B1453909
theorem B1938563 : Blo 1291964 1938563 := bstep (se 1 (by rfl) ⟨1453922, by rfl⟩ : syracuseStep 1938563 = 2907845) B2907845
theorem B1938593 : Blo 1291964 1938593 := bstep (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) B1453945
theorem B1635491 : Blo 1291964 1635491 := bstep (se 1 (by rfl) ⟨1226618, by rfl⟩ : syracuseStep 1635491 = 2453237) B2453237
theorem B3683501 : Blo 1291964 3683501 := bstep (se 3 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 3683501 = 1381313) B1381313
theorem B1938611 : Blo 1291964 1938611 := bstep (se 1 (by rfl) ⟨1453958, by rfl⟩ : syracuseStep 1938611 = 2907917) B2907917
theorem B4363469 : Blo 1291964 4363469 := bstep (se 3 (by rfl) ⟨818150, by rfl⟩ : syracuseStep 4363469 = 1636301) B1636301
theorem B1938641 : Blo 1291964 1938641 := bstep (se 2 (by rfl) ⟨726990, by rfl⟩ : syracuseStep 1938641 = 1453981) B1453981
theorem B3314915 : Blo 1291964 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B1938659 : Blo 1291964 1938659 := bstep (se 1 (by rfl) ⟨1453994, by rfl⟩ : syracuseStep 1938659 = 2907989) B2907989
theorem B1455331 : Blo 1291964 1455331 := bstep (se 1 (by rfl) ⟨1091498, by rfl⟩ : syracuseStep 1455331 = 2182997) B2182997
theorem B5526755 : Blo 1291964 5526755 := bstep (se 1 (by rfl) ⟨4145066, by rfl⟩ : syracuseStep 5526755 = 8290133) B8290133
theorem B11048177 : Blo 1291964 11048177 := bstep (se 2 (by rfl) ⟨4143066, by rfl⟩ : syracuseStep 11048177 = 8286133) B8286133
theorem B3683569 : Blo 1291964 3683569 := bstep (se 2 (by rfl) ⟨1381338, by rfl⟩ : syracuseStep 3683569 = 2762677) B2762677
theorem B1938689 : Blo 1291964 1938689 := bstep (se 2 (by rfl) ⟨727008, by rfl⟩ : syracuseStep 1938689 = 1454017) B1454017
theorem B4363523 : Blo 1291964 4363523 := bstep (se 1 (by rfl) ⟨3272642, by rfl⟩ : syracuseStep 4363523 = 6545285) B6545285
theorem B4912397 : Blo 1291964 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B1938707 : Blo 1291964 1938707 := bstep (se 1 (by rfl) ⟨1454030, by rfl⟩ : syracuseStep 1938707 = 2908061) B2908061
theorem B1938737 : Blo 1291964 1938737 := bstep (se 2 (by rfl) ⟨727026, by rfl⟩ : syracuseStep 1938737 = 1454053) B1454053
theorem B1938755 : Blo 1291964 1938755 := bstep (se 1 (by rfl) ⟨1454066, by rfl⟩ : syracuseStep 1938755 = 2908133) B2908133
theorem B1938785 : Blo 1291964 1938785 := bstep (se 2 (by rfl) ⟨727044, by rfl⟩ : syracuseStep 1938785 = 1454089) B1454089
theorem B5518691 : Blo 1291964 5518691 := bstep (se 1 (by rfl) ⟨4139018, by rfl⟩ : syracuseStep 5518691 = 8278037) B8278037
theorem B1938803 : Blo 1291964 1938803 := bstep (se 1 (by rfl) ⟨1454102, by rfl⟩ : syracuseStep 1938803 = 2908205) B2908205
theorem B1455475 : Blo 1291964 1455475 := bstep (se 1 (by rfl) ⟨1091606, by rfl⟩ : syracuseStep 1455475 = 2183213) B2183213
theorem B12424589 : Blo 1291964 12424589 := bstep (se 3 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 12424589 = 4659221) B4659221
theorem B1938833 : Blo 1291964 1938833 := bstep (se 2 (by rfl) ⟨727062, by rfl⟩ : syracuseStep 1938833 = 1454125) B1454125
theorem B1938851 : Blo 1291964 1938851 := bstep (se 1 (by rfl) ⟨1454138, by rfl⟩ : syracuseStep 1938851 = 2908277) B2908277
theorem B2454961 : Blo 1291964 2454961 := bstep (se 2 (by rfl) ⟨920610, by rfl⟩ : syracuseStep 2454961 = 1841221) B1841221
theorem B1938881 : Blo 1291964 1938881 := bstep (se 2 (by rfl) ⟨727080, by rfl⟩ : syracuseStep 1938881 = 1454161) B1454161
theorem B1938899 : Blo 1291964 1938899 := bstep (se 1 (by rfl) ⟨1454174, by rfl⟩ : syracuseStep 1938899 = 2908349) B2908349
theorem B1938929 : Blo 1291964 1938929 := bstep (se 2 (by rfl) ⟨727098, by rfl⟩ : syracuseStep 1938929 = 1454197) B1454197
theorem B1938947 : Blo 1291964 1938947 := bstep (se 1 (by rfl) ⟨1454210, by rfl⟩ : syracuseStep 1938947 = 2908421) B2908421
theorem B3683843 : Blo 1291964 3683843 := bstep (se 1 (by rfl) ⟨2762882, by rfl⟩ : syracuseStep 3683843 = 5525765) B5525765
theorem B1455619 : Blo 1291964 1455619 := bstep (se 1 (by rfl) ⟨1091714, by rfl⟩ : syracuseStep 1455619 = 2183429) B2183429
theorem B1840657 : Blo 1291964 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B4363793 : Blo 1291964 4363793 := bstep (se 2 (by rfl) ⟨1636422, by rfl⟩ : syracuseStep 4363793 = 3272845) B3272845
theorem B1938977 : Blo 1291964 1938977 := bstep (se 2 (by rfl) ⟨727116, by rfl⟩ : syracuseStep 1938977 = 1454233) B1454233
theorem B1938995 : Blo 1291964 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B1840691 : Blo 1291964 1840691 := bstep (se 1 (by rfl) ⟨1380518, by rfl⟩ : syracuseStep 1840691 = 2761037) B2761037
theorem B1939025 : Blo 1291964 1939025 := bstep (se 2 (by rfl) ⟨727134, by rfl⟩ : syracuseStep 1939025 = 1454269) B1454269
theorem B16782947 : Blo 1291964 16782947 := bstep (se 1 (by rfl) ⟨12587210, by rfl⟩ : syracuseStep 16782947 = 25174421) B25174421
theorem B1939043 : Blo 1291964 1939043 := bstep (se 1 (by rfl) ⟨1454282, by rfl⟩ : syracuseStep 1939043 = 2908565) B2908565
theorem B14939747 : Blo 1291964 14939747 := bstep (se 1 (by rfl) ⟨11204810, by rfl⟩ : syracuseStep 14939747 = 22409621) B22409621
theorem B1939073 : Blo 1291964 1939073 := bstep (se 2 (by rfl) ⟨727152, by rfl⟩ : syracuseStep 1939073 = 1454305) B1454305
theorem B1939091 : Blo 1291964 1939091 := bstep (se 1 (by rfl) ⟨1454318, by rfl⟩ : syracuseStep 1939091 = 2908637) B2908637
theorem B1939121 : Blo 1291964 1939121 := bstep (se 2 (by rfl) ⟨727170, by rfl⟩ : syracuseStep 1939121 = 1454341) B1454341
theorem B1291971 : Blo 1291964 1291971 := bstep (se 1 (by rfl) ⟨968978, by rfl⟩ : syracuseStep 1291971 = 1937957) B1937957
theorem B1939139 : Blo 1291964 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B1291987 : Blo 1291964 1291987 := bstep (se 1 (by rfl) ⟨968990, by rfl⟩ : syracuseStep 1291987 = 1937981) B1937981
theorem B1939169 : Blo 1291964 1939169 := bstep (se 2 (by rfl) ⟨727188, by rfl⟩ : syracuseStep 1939169 = 1454377) B1454377
theorem B1292003 : Blo 1291964 1292003 := bstep (se 1 (by rfl) ⟨969002, by rfl⟩ : syracuseStep 1292003 = 1938005) B1938005
theorem B1292019 : Blo 1291964 1292019 := bstep (se 1 (by rfl) ⟨969014, by rfl⟩ : syracuseStep 1292019 = 1938029) B1938029
theorem B1939187 : Blo 1291964 1939187 := bstep (se 1 (by rfl) ⟨1454390, by rfl⟩ : syracuseStep 1939187 = 2908781) B2908781
theorem B1292035 : Blo 1291964 1292035 := bstep (se 1 (by rfl) ⟨969026, by rfl⟩ : syracuseStep 1292035 = 1938053) B1938053
theorem B1939217 : Blo 1291964 1939217 := bstep (se 2 (by rfl) ⟨727206, by rfl⟩ : syracuseStep 1939217 = 1454413) B1454413
theorem B1292051 : Blo 1291964 1292051 := bstep (se 1 (by rfl) ⟨969038, by rfl⟩ : syracuseStep 1292051 = 1938077) B1938077
theorem B1292067 : Blo 1291964 1292067 := bstep (se 1 (by rfl) ⟨969050, by rfl⟩ : syracuseStep 1292067 = 1938101) B1938101
theorem B1939235 : Blo 1291964 1939235 := bstep (se 1 (by rfl) ⟨1454426, by rfl⟩ : syracuseStep 1939235 = 2908853) B2908853
theorem B7362353 : Blo 1291964 7362353 := bstep (se 2 (by rfl) ⟨2760882, by rfl⟩ : syracuseStep 7362353 = 5521765) B5521765
theorem B1292083 : Blo 1291964 1292083 := bstep (se 1 (by rfl) ⟨969062, by rfl⟩ : syracuseStep 1292083 = 1938125) B1938125
theorem B1939265 : Blo 1291964 1939265 := bstep (se 2 (by rfl) ⟨727224, by rfl⟩ : syracuseStep 1939265 = 1454449) B1454449
theorem B1292099 : Blo 1291964 1292099 := bstep (se 1 (by rfl) ⟨969074, by rfl⟩ : syracuseStep 1292099 = 1938149) B1938149
theorem B2455363 : Blo 1291964 2455363 := bstep (se 1 (by rfl) ⟨1841522, by rfl⟩ : syracuseStep 2455363 = 3683045) B3683045
theorem B3274577 : Blo 1291964 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B1292115 : Blo 1291964 1292115 := bstep (se 1 (by rfl) ⟨969086, by rfl⟩ : syracuseStep 1292115 = 1938173) B1938173
theorem B2070355 : Blo 1291964 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B1939283 : Blo 1291964 1939283 := bstep (se 1 (by rfl) ⟨1454462, by rfl⟩ : syracuseStep 1939283 = 2908925) B2908925
theorem B1292131 : Blo 1291964 1292131 := bstep (se 1 (by rfl) ⟨969098, by rfl⟩ : syracuseStep 1292131 = 1938197) B1938197
theorem B1636195 : Blo 1291964 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B1939313 : Blo 1291964 1939313 := bstep (se 2 (by rfl) ⟨727242, by rfl⟩ : syracuseStep 1939313 = 1454485) B1454485
theorem B2455409 : Blo 1291964 2455409 := bstep (se 2 (by rfl) ⟨920778, by rfl⟩ : syracuseStep 2455409 = 1841557) B1841557
theorem B1292147 : Blo 1291964 1292147 := bstep (se 1 (by rfl) ⟨969110, by rfl⟩ : syracuseStep 1292147 = 1938221) B1938221
theorem B1292163 : Blo 1291964 1292163 := bstep (se 1 (by rfl) ⟨969122, by rfl⟩ : syracuseStep 1292163 = 1938245) B1938245
theorem B1939331 : Blo 1291964 1939331 := bstep (se 1 (by rfl) ⟨1454498, by rfl⟩ : syracuseStep 1939331 = 2908997) B2908997
theorem B3274627 : Blo 1291964 3274627 := bstep (se 1 (by rfl) ⟨2455970, by rfl⟩ : syracuseStep 3274627 = 4911941) B4911941
theorem B9811853 : Blo 1291964 9811853 := bstep (se 3 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 9811853 = 3679445) B3679445
theorem B1292179 : Blo 1291964 1292179 := bstep (se 1 (by rfl) ⟨969134, by rfl⟩ : syracuseStep 1292179 = 1938269) B1938269
theorem B1554323 : Blo 1291964 1554323 := bstep (se 1 (by rfl) ⟨1165742, by rfl⟩ : syracuseStep 1554323 = 2331485) B2331485
theorem B1939361 : Blo 1291964 1939361 := bstep (se 2 (by rfl) ⟨727260, by rfl⟩ : syracuseStep 1939361 = 1454521) B1454521
theorem B1292195 : Blo 1291964 1292195 := bstep (se 1 (by rfl) ⟨969146, by rfl⟩ : syracuseStep 1292195 = 1938293) B1938293
theorem B1292211 : Blo 1291964 1292211 := bstep (se 1 (by rfl) ⟨969158, by rfl⟩ : syracuseStep 1292211 = 1938317) B1938317
theorem B2070451 : Blo 1291964 2070451 := bstep (se 1 (by rfl) ⟨1552838, by rfl⟩ : syracuseStep 2070451 = 3105677) B3105677
theorem B1939379 : Blo 1291964 1939379 := bstep (se 1 (by rfl) ⟨1454534, by rfl⟩ : syracuseStep 1939379 = 2909069) B2909069
theorem B1292227 : Blo 1291964 1292227 := bstep (se 1 (by rfl) ⟨969170, by rfl⟩ : syracuseStep 1292227 = 1938341) B1938341
theorem B1636291 : Blo 1291964 1636291 := bstep (se 1 (by rfl) ⟨1227218, by rfl⟩ : syracuseStep 1636291 = 2454437) B2454437
theorem B1939409 : Blo 1291964 1939409 := bstep (se 2 (by rfl) ⟨727278, by rfl⟩ : syracuseStep 1939409 = 1454557) B1454557
theorem B3733457 : Blo 1291964 3733457 := bstep (se 2 (by rfl) ⟨1400046, by rfl⟩ : syracuseStep 3733457 = 2800093) B2800093
theorem B1292243 : Blo 1291964 1292243 := bstep (se 1 (by rfl) ⟨969182, by rfl⟩ : syracuseStep 1292243 = 1938365) B1938365
theorem B1292259 : Blo 1291964 1292259 := bstep (se 1 (by rfl) ⟨969194, by rfl⟩ : syracuseStep 1292259 = 1938389) B1938389
theorem B1939427 : Blo 1291964 1939427 := bstep (se 1 (by rfl) ⟨1454570, by rfl⟩ : syracuseStep 1939427 = 2909141) B2909141
theorem B1292275 : Blo 1291964 1292275 := bstep (se 1 (by rfl) ⟨969206, by rfl⟩ : syracuseStep 1292275 = 1938413) B1938413
theorem B1939457 : Blo 1291964 1939457 := bstep (se 2 (by rfl) ⟨727296, by rfl⟩ : syracuseStep 1939457 = 1454593) B1454593
theorem B1292291 : Blo 1291964 1292291 := bstep (se 1 (by rfl) ⟨969218, by rfl⟩ : syracuseStep 1292291 = 1938437) B1938437
theorem B3274769 : Blo 1291964 3274769 := bstep (se 2 (by rfl) ⟨1228038, by rfl⟩ : syracuseStep 3274769 = 2456077) B2456077
theorem B1292307 : Blo 1291964 1292307 := bstep (se 1 (by rfl) ⟨969230, by rfl⟩ : syracuseStep 1292307 = 1938461) B1938461
theorem B1939475 : Blo 1291964 1939475 := bstep (se 1 (by rfl) ⟨1454606, by rfl⟩ : syracuseStep 1939475 = 2909213) B2909213
theorem B1292323 : Blo 1291964 1292323 := bstep (se 1 (by rfl) ⟨969242, by rfl⟩ : syracuseStep 1292323 = 1938485) B1938485
theorem B4364333 : Blo 1291964 4364333 := bstep (se 3 (by rfl) ⟨818312, by rfl⟩ : syracuseStep 4364333 = 1636625) B1636625
theorem B1939505 : Blo 1291964 1939505 := bstep (se 2 (by rfl) ⟨727314, by rfl⟩ : syracuseStep 1939505 = 1454629) B1454629
theorem B1292339 : Blo 1291964 1292339 := bstep (se 1 (by rfl) ⟨969254, by rfl⟩ : syracuseStep 1292339 = 1938509) B1938509
theorem B1292355 : Blo 1291964 1292355 := bstep (se 1 (by rfl) ⟨969266, by rfl⟩ : syracuseStep 1292355 = 1938533) B1938533
theorem B1939523 : Blo 1291964 1939523 := bstep (se 1 (by rfl) ⟨1454642, by rfl⟩ : syracuseStep 1939523 = 2909285) B2909285
theorem B1292371 : Blo 1291964 1292371 := bstep (se 1 (by rfl) ⟨969278, by rfl⟩ : syracuseStep 1292371 = 1938557) B1938557
theorem B2070611 : Blo 1291964 2070611 := bstep (se 1 (by rfl) ⟨1552958, by rfl⟩ : syracuseStep 2070611 = 3105917) B3105917
theorem B1939553 : Blo 1291964 1939553 := bstep (se 2 (by rfl) ⟨727332, by rfl⟩ : syracuseStep 1939553 = 1454665) B1454665
theorem B1841249 : Blo 1291964 1841249 := bstep (se 2 (by rfl) ⟨690468, by rfl⟩ : syracuseStep 1841249 = 1380937) B1380937
theorem B1292387 : Blo 1291964 1292387 := bstep (se 1 (by rfl) ⟨969290, by rfl⟩ : syracuseStep 1292387 = 1938581) B1938581
theorem B4364387 : Blo 1291964 4364387 := bstep (se 1 (by rfl) ⟨3273290, by rfl⟩ : syracuseStep 4364387 = 6546581) B6546581
theorem B1292403 : Blo 1291964 1292403 := bstep (se 1 (by rfl) ⟨969302, by rfl⟩ : syracuseStep 1292403 = 1938605) B1938605
theorem B1939571 : Blo 1291964 1939571 := bstep (se 1 (by rfl) ⟨1454678, by rfl⟩ : syracuseStep 1939571 = 2909357) B2909357
theorem B1292419 : Blo 1291964 1292419 := bstep (se 1 (by rfl) ⟨969314, by rfl⟩ : syracuseStep 1292419 = 1938629) B1938629
theorem B1939601 : Blo 1291964 1939601 := bstep (se 2 (by rfl) ⟨727350, by rfl⟩ : syracuseStep 1939601 = 1454701) B1454701
theorem B1292435 : Blo 1291964 1292435 := bstep (se 1 (by rfl) ⟨969326, by rfl⟩ : syracuseStep 1292435 = 1938653) B1938653
theorem B2455697 : Blo 1291964 2455697 := bstep (se 2 (by rfl) ⟨920886, by rfl⟩ : syracuseStep 2455697 = 1841773) B1841773
theorem B1292451 : Blo 1291964 1292451 := bstep (se 1 (by rfl) ⟨969338, by rfl⟩ : syracuseStep 1292451 = 1938677) B1938677
theorem B1939619 : Blo 1291964 1939619 := bstep (se 1 (by rfl) ⟨1454714, by rfl⟩ : syracuseStep 1939619 = 2909429) B2909429
theorem B1841329 : Blo 1291964 1841329 := bstep (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) B1380997
theorem B1292467 : Blo 1291964 1292467 := bstep (se 1 (by rfl) ⟨969350, by rfl⟩ : syracuseStep 1292467 = 1938701) B1938701
theorem B1939649 : Blo 1291964 1939649 := bstep (se 2 (by rfl) ⟨727368, by rfl⟩ : syracuseStep 1939649 = 1454737) B1454737
theorem B1292483 : Blo 1291964 1292483 := bstep (se 1 (by rfl) ⟨969362, by rfl⟩ : syracuseStep 1292483 = 1938725) B1938725
theorem B1292499 : Blo 1291964 1292499 := bstep (se 1 (by rfl) ⟨969374, by rfl⟩ : syracuseStep 1292499 = 1938749) B1938749
theorem B1939667 : Blo 1291964 1939667 := bstep (se 1 (by rfl) ⟨1454750, by rfl⟩ : syracuseStep 1939667 = 2909501) B2909501
theorem B1292515 : Blo 1291964 1292515 := bstep (se 1 (by rfl) ⟨969386, by rfl⟩ : syracuseStep 1292515 = 1938773) B1938773
theorem B1939697 : Blo 1291964 1939697 := bstep (se 2 (by rfl) ⟨727386, by rfl⟩ : syracuseStep 1939697 = 1454773) B1454773
theorem B1292531 : Blo 1291964 1292531 := bstep (se 1 (by rfl) ⟨969398, by rfl⟩ : syracuseStep 1292531 = 1938797) B1938797
theorem B2210051 : Blo 1291964 2210051 := bstep (se 1 (by rfl) ⟨1657538, by rfl⟩ : syracuseStep 2210051 = 3315077) B3315077
theorem B1292547 : Blo 1291964 1292547 := bstep (se 1 (by rfl) ⟨969410, by rfl⟩ : syracuseStep 1292547 = 1938821) B1938821
theorem B1939715 : Blo 1291964 1939715 := bstep (se 1 (by rfl) ⟨1454786, by rfl⟩ : syracuseStep 1939715 = 2909573) B2909573
theorem B1292563 : Blo 1291964 1292563 := bstep (se 1 (by rfl) ⟨969422, by rfl⟩ : syracuseStep 1292563 = 1938845) B1938845
theorem B1939745 : Blo 1291964 1939745 := bstep (se 2 (by rfl) ⟨727404, by rfl⟩ : syracuseStep 1939745 = 1454809) B1454809
theorem B1292579 : Blo 1291964 1292579 := bstep (se 1 (by rfl) ⟨969434, by rfl⟩ : syracuseStep 1292579 = 1938869) B1938869
theorem B6543665 : Blo 1291964 6543665 := bstep (se 2 (by rfl) ⟨2453874, by rfl⟩ : syracuseStep 6543665 = 4907749) B4907749
theorem B1292595 : Blo 1291964 1292595 := bstep (se 1 (by rfl) ⟨969446, by rfl⟩ : syracuseStep 1292595 = 1938893) B1938893
theorem B1939763 : Blo 1291964 1939763 := bstep (se 1 (by rfl) ⟨1454822, by rfl⟩ : syracuseStep 1939763 = 2909645) B2909645
theorem B1292611 : Blo 1291964 1292611 := bstep (se 1 (by rfl) ⟨969458, by rfl⟩ : syracuseStep 1292611 = 1938917) B1938917
theorem B8395085 : Blo 1291964 8395085 := bstep (se 3 (by rfl) ⟨1574078, by rfl⟩ : syracuseStep 8395085 = 3148157) B3148157
theorem B3684685 : Blo 1291964 3684685 := bstep (se 3 (by rfl) ⟨690878, by rfl⟩ : syracuseStep 3684685 = 1381757) B1381757
theorem B1939793 : Blo 1291964 1939793 := bstep (se 2 (by rfl) ⟨727422, by rfl⟩ : syracuseStep 1939793 = 1454845) B1454845
theorem B1292627 : Blo 1291964 1292627 := bstep (se 1 (by rfl) ⟨969470, by rfl⟩ : syracuseStep 1292627 = 1938941) B1938941
theorem B1292643 : Blo 1291964 1292643 := bstep (se 1 (by rfl) ⟨969482, by rfl⟩ : syracuseStep 1292643 = 1938965) B1938965
theorem B1939811 : Blo 1291964 1939811 := bstep (se 1 (by rfl) ⟨1454858, by rfl⟩ : syracuseStep 1939811 = 2909717) B2909717
theorem B4364657 : Blo 1291964 4364657 := bstep (se 2 (by rfl) ⟨1636746, by rfl⟩ : syracuseStep 4364657 = 3273493) B3273493
theorem B1292659 : Blo 1291964 1292659 := bstep (se 1 (by rfl) ⟨969494, by rfl⟩ : syracuseStep 1292659 = 1938989) B1938989
theorem B1939841 : Blo 1291964 1939841 := bstep (se 2 (by rfl) ⟨727440, by rfl⟩ : syracuseStep 1939841 = 1454881) B1454881
theorem B1292675 : Blo 1291964 1292675 := bstep (se 1 (by rfl) ⟨969506, by rfl⟩ : syracuseStep 1292675 = 1939013) B1939013
theorem B1292691 : Blo 1291964 1292691 := bstep (se 1 (by rfl) ⟨969518, by rfl⟩ : syracuseStep 1292691 = 1939037) B1939037
theorem B1939859 : Blo 1291964 1939859 := bstep (se 1 (by rfl) ⟨1454894, by rfl⟩ : syracuseStep 1939859 = 2909789) B2909789
theorem B1292707 : Blo 1291964 1292707 := bstep (se 1 (by rfl) ⟨969530, by rfl⟩ : syracuseStep 1292707 = 1939061) B1939061
theorem B1939889 : Blo 1291964 1939889 := bstep (se 2 (by rfl) ⟨727458, by rfl⟩ : syracuseStep 1939889 = 1454917) B1454917
theorem B1292723 : Blo 1291964 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B1636787 : Blo 1291964 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B1292739 : Blo 1291964 1292739 := bstep (se 1 (by rfl) ⟨969554, by rfl⟩ : syracuseStep 1292739 = 1939109) B1939109
theorem B1939907 : Blo 1291964 1939907 := bstep (se 1 (by rfl) ⟨1454930, by rfl⟩ : syracuseStep 1939907 = 2909861) B2909861
theorem B1292755 : Blo 1291964 1292755 := bstep (se 1 (by rfl) ⟨969566, by rfl⟩ : syracuseStep 1292755 = 1939133) B1939133
theorem B1939937 : Blo 1291964 1939937 := bstep (se 2 (by rfl) ⟨727476, by rfl⟩ : syracuseStep 1939937 = 1454953) B1454953
theorem B1292771 : Blo 1291964 1292771 := bstep (se 1 (by rfl) ⟨969578, by rfl⟩ : syracuseStep 1292771 = 1939157) B1939157
theorem B1292787 : Blo 1291964 1292787 := bstep (se 1 (by rfl) ⟨969590, by rfl⟩ : syracuseStep 1292787 = 1939181) B1939181
theorem B1939955 : Blo 1291964 1939955 := bstep (se 1 (by rfl) ⟨1454966, by rfl⟩ : syracuseStep 1939955 = 2909933) B2909933
theorem B1292803 : Blo 1291964 1292803 := bstep (se 1 (by rfl) ⟨969602, by rfl⟩ : syracuseStep 1292803 = 1939205) B1939205
theorem B1939985 : Blo 1291964 1939985 := bstep (se 2 (by rfl) ⟨727494, by rfl⟩ : syracuseStep 1939985 = 1454989) B1454989
theorem B1292819 : Blo 1291964 1292819 := bstep (se 1 (by rfl) ⟨969614, by rfl⟩ : syracuseStep 1292819 = 1939229) B1939229
theorem B1292835 : Blo 1291964 1292835 := bstep (se 1 (by rfl) ⟨969626, by rfl⟩ : syracuseStep 1292835 = 1939253) B1939253
theorem B1940003 : Blo 1291964 1940003 := bstep (se 1 (by rfl) ⟨1455002, by rfl⟩ : syracuseStep 1940003 = 2910005) B2910005
theorem B1292851 : Blo 1291964 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B1940033 : Blo 1291964 1940033 := bstep (se 2 (by rfl) ⟨727512, by rfl⟩ : syracuseStep 1940033 = 1455025) B1455025
theorem B1292867 : Blo 1291964 1292867 := bstep (se 1 (by rfl) ⟨969650, by rfl⟩ : syracuseStep 1292867 = 1939301) B1939301
theorem B1292883 : Blo 1291964 1292883 := bstep (se 1 (by rfl) ⟨969662, by rfl⟩ : syracuseStep 1292883 = 1939325) B1939325
theorem B1940051 : Blo 1291964 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B1292899 : Blo 1291964 1292899 := bstep (se 1 (by rfl) ⟨969674, by rfl⟩ : syracuseStep 1292899 = 1939349) B1939349
theorem B67148401 : Blo 1291964 67148401 := bstep (se 2 (by rfl) ⟨25180650, by rfl⟩ : syracuseStep 67148401 = 50361301) B50361301
theorem B1940081 : Blo 1291964 1940081 := bstep (se 2 (by rfl) ⟨727530, by rfl⟩ : syracuseStep 1940081 = 1455061) B1455061
theorem B1292915 : Blo 1291964 1292915 := bstep (se 1 (by rfl) ⟨969686, by rfl⟩ : syracuseStep 1292915 = 1939373) B1939373
theorem B1292931 : Blo 1291964 1292931 := bstep (se 1 (by rfl) ⟨969698, by rfl⟩ : syracuseStep 1292931 = 1939397) B1939397
theorem B1940099 : Blo 1291964 1940099 := bstep (se 1 (by rfl) ⟨1455074, by rfl⟩ : syracuseStep 1940099 = 2910149) B2910149
theorem B1292947 : Blo 1291964 1292947 := bstep (se 1 (by rfl) ⟨969710, by rfl⟩ : syracuseStep 1292947 = 1939421) B1939421
theorem B1940129 : Blo 1291964 1940129 := bstep (se 2 (by rfl) ⟨727548, by rfl⟩ : syracuseStep 1940129 = 1455097) B1455097
theorem B1292963 : Blo 1291964 1292963 := bstep (se 1 (by rfl) ⟨969722, by rfl⟩ : syracuseStep 1292963 = 1939445) B1939445
theorem B1292979 : Blo 1291964 1292979 := bstep (se 1 (by rfl) ⟨969734, by rfl⟩ : syracuseStep 1292979 = 1939469) B1939469
theorem B1940147 : Blo 1291964 1940147 := bstep (se 1 (by rfl) ⟨1455110, by rfl⟩ : syracuseStep 1940147 = 2910221) B2910221
theorem B1292995 : Blo 1291964 1292995 := bstep (se 1 (by rfl) ⟨969746, by rfl⟩ : syracuseStep 1292995 = 1939493) B1939493
theorem B4143811 : Blo 1291964 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B9312965 : Blo 1291964 9312965 := bstep (se 4 (by rfl) ⟨873090, by rfl⟩ : syracuseStep 9312965 = 1746181) B1746181
theorem B1940177 : Blo 1291964 1940177 := bstep (se 2 (by rfl) ⟨727566, by rfl⟩ : syracuseStep 1940177 = 1455133) B1455133
theorem B1293011 : Blo 1291964 1293011 := bstep (se 1 (by rfl) ⟨969758, by rfl⟩ : syracuseStep 1293011 = 1939517) B1939517
theorem B1293027 : Blo 1291964 1293027 := bstep (se 1 (by rfl) ⟨969770, by rfl⟩ : syracuseStep 1293027 = 1939541) B1939541
theorem B1940195 : Blo 1291964 1940195 := bstep (se 1 (by rfl) ⟨1455146, by rfl⟩ : syracuseStep 1940195 = 2910293) B2910293
theorem B1293043 : Blo 1291964 1293043 := bstep (se 1 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 1293043 = 1939565) B1939565
theorem B1940225 : Blo 1291964 1940225 := bstep (se 2 (by rfl) ⟨727584, by rfl⟩ : syracuseStep 1940225 = 1455169) B1455169
theorem B1293059 : Blo 1291964 1293059 := bstep (se 1 (by rfl) ⟨969794, by rfl⟩ : syracuseStep 1293059 = 1939589) B1939589
theorem B1293075 : Blo 1291964 1293075 := bstep (se 1 (by rfl) ⟨969806, by rfl⟩ : syracuseStep 1293075 = 1939613) B1939613
theorem B1940243 : Blo 1291964 1940243 := bstep (se 1 (by rfl) ⟨1455182, by rfl⟩ : syracuseStep 1940243 = 2910365) B2910365
theorem B1293091 : Blo 1291964 1293091 := bstep (se 1 (by rfl) ⟨969818, by rfl⟩ : syracuseStep 1293091 = 1939637) B1939637
theorem B1940273 : Blo 1291964 1940273 := bstep (se 2 (by rfl) ⟨727602, by rfl⟩ : syracuseStep 1940273 = 1455205) B1455205
theorem B1293107 : Blo 1291964 1293107 := bstep (se 1 (by rfl) ⟨969830, by rfl⟩ : syracuseStep 1293107 = 1939661) B1939661
theorem B1293123 : Blo 1291964 1293123 := bstep (se 1 (by rfl) ⟨969842, by rfl⟩ : syracuseStep 1293123 = 1939685) B1939685
theorem B1940291 : Blo 1291964 1940291 := bstep (se 1 (by rfl) ⟨1455218, by rfl⟩ : syracuseStep 1940291 = 2910437) B2910437
theorem B4905805 : Blo 1291964 4905805 := bstep (se 3 (by rfl) ⟨919838, by rfl⟩ : syracuseStep 4905805 = 1839677) B1839677
theorem B1293139 : Blo 1291964 1293139 := bstep (se 1 (by rfl) ⟨969854, by rfl⟩ : syracuseStep 1293139 = 1939709) B1939709
theorem B1940321 : Blo 1291964 1940321 := bstep (se 2 (by rfl) ⟨727620, by rfl⟩ : syracuseStep 1940321 = 1455241) B1455241
theorem B1293155 : Blo 1291964 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B2456419 : Blo 1291964 2456419 := bstep (se 1 (by rfl) ⟨1842314, by rfl⟩ : syracuseStep 2456419 = 3684629) B3684629
theorem B1293171 : Blo 1291964 1293171 := bstep (se 1 (by rfl) ⟨969878, by rfl⟩ : syracuseStep 1293171 = 1939757) B1939757
theorem B1940339 : Blo 1291964 1940339 := bstep (se 1 (by rfl) ⟨1455254, by rfl⟩ : syracuseStep 1940339 = 2910509) B2910509
theorem B1293187 : Blo 1291964 1293187 := bstep (se 1 (by rfl) ⟨969890, by rfl⟩ : syracuseStep 1293187 = 1939781) B1939781
theorem B4365197 : Blo 1291964 4365197 := bstep (se 3 (by rfl) ⟨818474, by rfl⟩ : syracuseStep 4365197 = 1636949) B1636949
theorem B1940369 : Blo 1291964 1940369 := bstep (se 2 (by rfl) ⟨727638, by rfl⟩ : syracuseStep 1940369 = 1455277) B1455277
theorem B1293203 : Blo 1291964 1293203 := bstep (se 1 (by rfl) ⟨969902, by rfl⟩ : syracuseStep 1293203 = 1939805) B1939805
theorem B1293219 : Blo 1291964 1293219 := bstep (se 1 (by rfl) ⟨969914, by rfl⟩ : syracuseStep 1293219 = 1939829) B1939829
theorem B1940387 : Blo 1291964 1940387 := bstep (se 1 (by rfl) ⟨1455290, by rfl⟩ : syracuseStep 1940387 = 2910581) B2910581
theorem B1866673 : Blo 1291964 1866673 := bstep (se 2 (by rfl) ⟨700002, by rfl⟩ : syracuseStep 1866673 = 1400005) B1400005
theorem B2800561 : Blo 1291964 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B1293235 : Blo 1291964 1293235 := bstep (se 1 (by rfl) ⟨969926, by rfl⟩ : syracuseStep 1293235 = 1939853) B1939853
theorem B1940417 : Blo 1291964 1940417 := bstep (se 2 (by rfl) ⟨727656, by rfl⟩ : syracuseStep 1940417 = 1455313) B1455313
theorem B1293251 : Blo 1291964 1293251 := bstep (se 1 (by rfl) ⟨969938, by rfl⟩ : syracuseStep 1293251 = 1939877) B1939877
theorem B4365251 : Blo 1291964 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B1842115 : Blo 1291964 1842115 := bstep (se 1 (by rfl) ⟨1381586, by rfl⟩ : syracuseStep 1842115 = 2763173) B2763173
theorem B2907089 : Blo 1291964 2907089 := bstep (se 2 (by rfl) ⟨1090158, by rfl⟩ : syracuseStep 2907089 = 2180317) B2180317
theorem B4144081 : Blo 1291964 4144081 := bstep (se 2 (by rfl) ⟨1554030, by rfl⟩ : syracuseStep 4144081 = 3108061) B3108061
theorem B1293267 : Blo 1291964 1293267 := bstep (se 1 (by rfl) ⟨969950, by rfl⟩ : syracuseStep 1293267 = 1939901) B1939901
theorem B1940435 : Blo 1291964 1940435 := bstep (se 1 (by rfl) ⟨1455326, by rfl⟩ : syracuseStep 1940435 = 2910653) B2910653
theorem B1891297 : Blo 1291964 1891297 := bstep (se 2 (by rfl) ⟨709236, by rfl⟩ : syracuseStep 1891297 = 1418473) B1418473
theorem B2907107 : Blo 1291964 2907107 := bstep (se 1 (by rfl) ⟨2180330, by rfl⟩ : syracuseStep 2907107 = 4360661) B4360661
theorem B1293283 : Blo 1291964 1293283 := bstep (se 1 (by rfl) ⟨969962, by rfl⟩ : syracuseStep 1293283 = 1939925) B1939925
theorem B1940465 : Blo 1291964 1940465 := bstep (se 2 (by rfl) ⟨727674, by rfl⟩ : syracuseStep 1940465 = 1455349) B1455349
theorem B1293299 : Blo 1291964 1293299 := bstep (se 1 (by rfl) ⟨969974, by rfl⟩ : syracuseStep 1293299 = 1939949) B1939949
theorem B1293315 : Blo 1291964 1293315 := bstep (se 1 (by rfl) ⟨969986, by rfl⟩ : syracuseStep 1293315 = 1939973) B1939973
theorem B1940483 : Blo 1291964 1940483 := bstep (se 1 (by rfl) ⟨1455362, by rfl⟩ : syracuseStep 1940483 = 2910725) B2910725
theorem B1293331 : Blo 1291964 1293331 := bstep (se 1 (by rfl) ⟨969998, by rfl⟩ : syracuseStep 1293331 = 1939997) B1939997
theorem B2071585 : Blo 1291964 2071585 := bstep (se 2 (by rfl) ⟨776844, by rfl⟩ : syracuseStep 2071585 = 1553689) B1553689
theorem B1940513 : Blo 1291964 1940513 := bstep (se 2 (by rfl) ⟨727692, by rfl⟩ : syracuseStep 1940513 = 1455385) B1455385
theorem B1293347 : Blo 1291964 1293347 := bstep (se 1 (by rfl) ⟨970010, by rfl⟩ : syracuseStep 1293347 = 1940021) B1940021
theorem B5520433 : Blo 1291964 5520433 := bstep (se 2 (by rfl) ⟨2070162, by rfl⟩ : syracuseStep 5520433 = 4140325) B4140325
theorem B1293363 : Blo 1291964 1293363 := bstep (se 1 (by rfl) ⟨970022, by rfl⟩ : syracuseStep 1293363 = 1940045) B1940045
theorem B1940531 : Blo 1291964 1940531 := bstep (se 1 (by rfl) ⟨1455398, by rfl⟩ : syracuseStep 1940531 = 2910797) B2910797
theorem B1293379 : Blo 1291964 1293379 := bstep (se 1 (by rfl) ⟨970034, by rfl⟩ : syracuseStep 1293379 = 1940069) B1940069
theorem B1940561 : Blo 1291964 1940561 := bstep (se 2 (by rfl) ⟨727710, by rfl⟩ : syracuseStep 1940561 = 1455421) B1455421
theorem B1293395 : Blo 1291964 1293395 := bstep (se 1 (by rfl) ⟨970046, by rfl⟩ : syracuseStep 1293395 = 1940093) B1940093
theorem B1293411 : Blo 1291964 1293411 := bstep (se 1 (by rfl) ⟨970058, by rfl⟩ : syracuseStep 1293411 = 1940117) B1940117
theorem B1940579 : Blo 1291964 1940579 := bstep (se 1 (by rfl) ⟨1455434, by rfl⟩ : syracuseStep 1940579 = 2910869) B2910869
theorem B1293427 : Blo 1291964 1293427 := bstep (se 1 (by rfl) ⟨970070, by rfl⟩ : syracuseStep 1293427 = 1940141) B1940141
theorem B1637491 : Blo 1291964 1637491 := bstep (se 1 (by rfl) ⟨1228118, by rfl⟩ : syracuseStep 1637491 = 2456237) B2456237
theorem B1940609 : Blo 1291964 1940609 := bstep (se 2 (by rfl) ⟨727728, by rfl⟩ : syracuseStep 1940609 = 1455457) B1455457
theorem B3931267 : Blo 1291964 3931267 := bstep (se 1 (by rfl) ⟨2948450, by rfl⟩ : syracuseStep 3931267 = 5896901) B5896901
theorem B1293443 : Blo 1291964 1293443 := bstep (se 1 (by rfl) ⟨970082, by rfl⟩ : syracuseStep 1293443 = 1940165) B1940165
theorem B1293459 : Blo 1291964 1293459 := bstep (se 1 (by rfl) ⟨970094, by rfl⟩ : syracuseStep 1293459 = 1940189) B1940189
theorem B1940627 : Blo 1291964 1940627 := bstep (se 1 (by rfl) ⟨1455470, by rfl⟩ : syracuseStep 1940627 = 2910941) B2910941
theorem B1293475 : Blo 1291964 1293475 := bstep (se 1 (by rfl) ⟨970106, by rfl⟩ : syracuseStep 1293475 = 1940213) B1940213
theorem B1940657 : Blo 1291964 1940657 := bstep (se 2 (by rfl) ⟨727746, by rfl⟩ : syracuseStep 1940657 = 1455493) B1455493
theorem B1293491 : Blo 1291964 1293491 := bstep (se 1 (by rfl) ⟨970118, by rfl⟩ : syracuseStep 1293491 = 1940237) B1940237
theorem B1293507 : Blo 1291964 1293507 := bstep (se 1 (by rfl) ⟨970130, by rfl⟩ : syracuseStep 1293507 = 1940261) B1940261
theorem B1940675 : Blo 1291964 1940675 := bstep (se 1 (by rfl) ⟨1455506, by rfl⟩ : syracuseStep 1940675 = 2911013) B2911013
theorem B4365521 : Blo 1291964 4365521 := bstep (se 2 (by rfl) ⟨1637070, by rfl⟩ : syracuseStep 4365521 = 3274141) B3274141
theorem B1293523 : Blo 1291964 1293523 := bstep (se 1 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 1293523 = 1940285) B1940285
theorem B1637587 : Blo 1291964 1637587 := bstep (se 1 (by rfl) ⟨1228190, by rfl⟩ : syracuseStep 1637587 = 2456381) B2456381
theorem B55934165 : Blo 1291964 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B1940705 : Blo 1291964 1940705 := bstep (se 2 (by rfl) ⟨727764, by rfl⟩ : syracuseStep 1940705 = 1455529) B1455529
theorem B7363811 : Blo 1291964 7363811 := bstep (se 1 (by rfl) ⟨5522858, by rfl⟩ : syracuseStep 7363811 = 11045717) B11045717
theorem B1293539 : Blo 1291964 1293539 := bstep (se 1 (by rfl) ⟨970154, by rfl⟩ : syracuseStep 1293539 = 1940309) B1940309
theorem B2907377 : Blo 1291964 2907377 := bstep (se 2 (by rfl) ⟨1090266, by rfl⟩ : syracuseStep 2907377 = 2180533) B2180533
theorem B1293555 : Blo 1291964 1293555 := bstep (se 1 (by rfl) ⟨970166, by rfl⟩ : syracuseStep 1293555 = 1940333) B1940333
theorem B1940723 : Blo 1291964 1940723 := bstep (se 1 (by rfl) ⟨1455542, by rfl⟩ : syracuseStep 1940723 = 2911085) B2911085
theorem B2907395 : Blo 1291964 2907395 := bstep (se 1 (by rfl) ⟨2180546, by rfl⟩ : syracuseStep 2907395 = 4361093) B4361093
theorem B1293571 : Blo 1291964 1293571 := bstep (se 1 (by rfl) ⟨970178, by rfl⟩ : syracuseStep 1293571 = 1940357) B1940357
theorem B5897485 : Blo 1291964 5897485 := bstep (se 3 (by rfl) ⟨1105778, by rfl⟩ : syracuseStep 5897485 = 2211557) B2211557
theorem B1293587 : Blo 1291964 1293587 := bstep (se 1 (by rfl) ⟨970190, by rfl⟩ : syracuseStep 1293587 = 1940381) B1940381
theorem B1940753 : Blo 1291964 1940753 := bstep (se 2 (by rfl) ⟨727782, by rfl⟩ : syracuseStep 1940753 = 1455565) B1455565
theorem B1293603 : Blo 1291964 1293603 := bstep (se 1 (by rfl) ⟨970202, by rfl⟩ : syracuseStep 1293603 = 1940405) B1940405
theorem B1940771 : Blo 1291964 1940771 := bstep (se 1 (by rfl) ⟨1455578, by rfl⟩ : syracuseStep 1940771 = 2911157) B2911157
theorem B1293619 : Blo 1291964 1293619 := bstep (se 1 (by rfl) ⟨970214, by rfl⟩ : syracuseStep 1293619 = 1940429) B1940429
theorem B1940801 : Blo 1291964 1940801 := bstep (se 2 (by rfl) ⟨727800, by rfl⟩ : syracuseStep 1940801 = 1455601) B1455601
theorem B1293635 : Blo 1291964 1293635 := bstep (se 1 (by rfl) ⟨970226, by rfl⟩ : syracuseStep 1293635 = 1940453) B1940453
theorem B1293651 : Blo 1291964 1293651 := bstep (se 1 (by rfl) ⟨970238, by rfl⟩ : syracuseStep 1293651 = 1940477) B1940477
theorem B1940819 : Blo 1291964 1940819 := bstep (se 1 (by rfl) ⟨1455614, by rfl⟩ : syracuseStep 1940819 = 2911229) B2911229
theorem B1293667 : Blo 1291964 1293667 := bstep (se 1 (by rfl) ⟨970250, by rfl⟩ : syracuseStep 1293667 = 1940501) B1940501
theorem B1940849 : Blo 1291964 1940849 := bstep (se 2 (by rfl) ⟨727818, by rfl⟩ : syracuseStep 1940849 = 1455637) B1455637
theorem B1293683 : Blo 1291964 1293683 := bstep (se 1 (by rfl) ⟨970262, by rfl⟩ : syracuseStep 1293683 = 1940525) B1940525
theorem B1293699 : Blo 1291964 1293699 := bstep (se 1 (by rfl) ⟨970274, by rfl⟩ : syracuseStep 1293699 = 1940549) B1940549
theorem B3497347 : Blo 1291964 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B1940867 : Blo 1291964 1940867 := bstep (se 1 (by rfl) ⟨1455650, by rfl⟩ : syracuseStep 1940867 = 2911301) B2911301
theorem B3497357 : Blo 1291964 3497357 := bstep (se 3 (by rfl) ⟨655754, by rfl⟩ : syracuseStep 3497357 = 1311509) B1311509
theorem B1293715 : Blo 1291964 1293715 := bstep (se 1 (by rfl) ⟨970286, by rfl⟩ : syracuseStep 1293715 = 1940573) B1940573
theorem B1940897 : Blo 1291964 1940897 := bstep (se 2 (by rfl) ⟨727836, by rfl⟩ : syracuseStep 1940897 = 1455673) B1455673
theorem B1293731 : Blo 1291964 1293731 := bstep (se 1 (by rfl) ⟨970298, by rfl⟩ : syracuseStep 1293731 = 1940597) B1940597
theorem B1310131 : Blo 1291964 1310131 := bstep (se 1 (by rfl) ⟨982598, by rfl⟩ : syracuseStep 1310131 = 1965197) B1965197
theorem B1293747 : Blo 1291964 1293747 := bstep (se 1 (by rfl) ⟨970310, by rfl⟩ : syracuseStep 1293747 = 1940621) B1940621
theorem B1940915 : Blo 1291964 1940915 := bstep (se 1 (by rfl) ⟨1455686, by rfl⟩ : syracuseStep 1940915 = 2911373) B2911373
theorem B2760131 : Blo 1291964 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B1293763 : Blo 1291964 1293763 := bstep (se 1 (by rfl) ⟨970322, by rfl⟩ : syracuseStep 1293763 = 1940645) B1940645
theorem B1940945 : Blo 1291964 1940945 := bstep (se 2 (by rfl) ⟨727854, by rfl⟩ : syracuseStep 1940945 = 1455709) B1455709
theorem B1293779 : Blo 1291964 1293779 := bstep (se 1 (by rfl) ⟨970334, by rfl⟩ : syracuseStep 1293779 = 1940669) B1940669
theorem B1310179 : Blo 1291964 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B1293795 : Blo 1291964 1293795 := bstep (se 1 (by rfl) ⟨970346, by rfl⟩ : syracuseStep 1293795 = 1940693) B1940693
theorem B1293811 : Blo 1291964 1293811 := bstep (se 1 (by rfl) ⟨970358, by rfl⟩ : syracuseStep 1293811 = 1940717) B1940717
theorem B1293827 : Blo 1291964 1293827 := bstep (se 1 (by rfl) ⟨970370, by rfl⟩ : syracuseStep 1293827 = 1940741) B1940741
theorem B2907665 : Blo 1291964 2907665 := bstep (se 2 (by rfl) ⟨1090374, by rfl⟩ : syracuseStep 2907665 = 2180749) B2180749
theorem B1293843 : Blo 1291964 1293843 := bstep (se 1 (by rfl) ⟨970382, by rfl⟩ : syracuseStep 1293843 = 1940765) B1940765
theorem B2907683 : Blo 1291964 2907683 := bstep (se 1 (by rfl) ⟨2180762, by rfl⟩ : syracuseStep 2907683 = 4361525) B4361525
theorem B1293859 : Blo 1291964 1293859 := bstep (se 1 (by rfl) ⟨970394, by rfl⟩ : syracuseStep 1293859 = 1940789) B1940789
theorem B1293875 : Blo 1291964 1293875 := bstep (se 1 (by rfl) ⟨970406, by rfl⟩ : syracuseStep 1293875 = 1940813) B1940813
theorem B1293891 : Blo 1291964 1293891 := bstep (se 1 (by rfl) ⟨970418, by rfl⟩ : syracuseStep 1293891 = 1940837) B1940837
theorem B1293907 : Blo 1291964 1293907 := bstep (se 1 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 1293907 = 1940861) B1940861
theorem B4906595 : Blo 1291964 4906595 := bstep (se 1 (by rfl) ⟨3679946, by rfl⟩ : syracuseStep 4906595 = 7359893) B7359893
theorem B1293923 : Blo 1291964 1293923 := bstep (se 1 (by rfl) ⟨970442, by rfl⟩ : syracuseStep 1293923 = 1940885) B1940885
theorem B11787889 : Blo 1291964 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B1293939 : Blo 1291964 1293939 := bstep (se 1 (by rfl) ⟨970454, by rfl⟩ : syracuseStep 1293939 = 1940909) B1940909
theorem B1293955 : Blo 1291964 1293955 := bstep (se 1 (by rfl) ⟨970466, by rfl⟩ : syracuseStep 1293955 = 1940933) B1940933
theorem B10485389 : Blo 1291964 10485389 := bstep (se 3 (by rfl) ⟨1966010, by rfl⟩ : syracuseStep 10485389 = 3932021) B3932021
theorem B6545123 : Blo 1291964 6545123 := bstep (se 1 (by rfl) ⟨4908842, by rfl⟩ : syracuseStep 6545123 = 9817685) B9817685
theorem B4366061 : Blo 1291964 4366061 := bstep (se 3 (by rfl) ⟨818636, by rfl⟩ : syracuseStep 4366061 = 1637273) B1637273
theorem B4366115 : Blo 1291964 4366115 := bstep (se 1 (by rfl) ⟨3274586, by rfl⟩ : syracuseStep 4366115 = 6549173) B6549173
theorem B3931949 : Blo 1291964 3931949 := bstep (se 3 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 3931949 = 1474481) B1474481
theorem B2907953 : Blo 1291964 2907953 := bstep (se 2 (by rfl) ⟨1090482, by rfl⟩ : syracuseStep 2907953 = 2180965) B2180965
theorem B2907971 : Blo 1291964 2907971 := bstep (se 1 (by rfl) ⟨2180978, by rfl⟩ : syracuseStep 2907971 = 4361957) B4361957
theorem B8282033 : Blo 1291964 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B2211851 : Blo 1291964 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B2908313 : Blo 1291964 2908313 := bstep (se 2 (by rfl) ⟨1090617, by rfl⟩ : syracuseStep 2908313 = 2181235) B2181235
theorem B2908403 : Blo 1291964 2908403 := bstep (se 1 (by rfl) ⟨2181302, by rfl⟩ : syracuseStep 2908403 = 4362605) B4362605
theorem B2908439 : Blo 1291964 2908439 := bstep (se 1 (by rfl) ⟨2181329, by rfl⟩ : syracuseStep 2908439 = 4362659) B4362659
theorem B5595443 : Blo 1291964 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B10084787 : Blo 1291964 10084787 := bstep (se 1 (by rfl) ⟨7563590, by rfl⟩ : syracuseStep 10084787 = 15127181) B15127181
theorem B2908619 : Blo 1291964 2908619 := bstep (se 1 (by rfl) ⟨2181464, by rfl⟩ : syracuseStep 2908619 = 4362929) B4362929
theorem B2908673 : Blo 1291964 2908673 := bstep (se 2 (by rfl) ⟨1090752, by rfl⟩ : syracuseStep 2908673 = 2181505) B2181505
theorem B4907537 : Blo 1291964 4907537 := bstep (se 2 (by rfl) ⟨1840326, by rfl⟩ : syracuseStep 4907537 = 3680653) B3680653
theorem B4366871 : Blo 1291964 4366871 := bstep (se 1 (by rfl) ⟨3275153, by rfl⟩ : syracuseStep 4366871 = 6550307) B6550307
theorem B2908889 : Blo 1291964 2908889 := bstep (se 2 (by rfl) ⟨1090833, by rfl⟩ : syracuseStep 2908889 = 2181667) B2181667
theorem B2949911 : Blo 1291964 2949911 := bstep (se 1 (by rfl) ⟨2212433, by rfl⟩ : syracuseStep 2949911 = 4424867) B4424867
theorem B2622233 : Blo 1291964 2622233 := bstep (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) B1966675
theorem B2908979 : Blo 1291964 2908979 := bstep (se 1 (by rfl) ⟨2181734, by rfl⟩ : syracuseStep 2908979 = 4363469) B4363469
theorem B89531201 : Blo 1291964 89531201 := bstep (se 2 (by rfl) ⟨33574200, by rfl⟩ : syracuseStep 89531201 = 67148401) B67148401
theorem B7365451 : Blo 1291964 7365451 := bstep (se 1 (by rfl) ⟨5524088, by rfl⟩ : syracuseStep 7365451 = 11048177) B11048177
theorem B2909015 : Blo 1291964 2909015 := bstep (se 1 (by rfl) ⟨2181761, by rfl⟩ : syracuseStep 2909015 = 4363523) B4363523
theorem B3679127 : Blo 1291964 3679127 := bstep (se 1 (by rfl) ⟨2759345, by rfl⟩ : syracuseStep 3679127 = 5518691) B5518691
theorem B8283059 : Blo 1291964 8283059 := bstep (se 1 (by rfl) ⟨6212294, by rfl⟩ : syracuseStep 8283059 = 12424589) B12424589
theorem B2909195 : Blo 1291964 2909195 := bstep (se 1 (by rfl) ⟨2181896, by rfl⟩ : syracuseStep 2909195 = 4363793) B4363793
theorem B10773521 : Blo 1291964 10773521 := bstep (se 2 (by rfl) ⟨4040070, by rfl⟩ : syracuseStep 10773521 = 8080141) B8080141
theorem B2909249 : Blo 1291964 2909249 := bstep (se 2 (by rfl) ⟨1090968, by rfl⟩ : syracuseStep 2909249 = 2181937) B2181937
theorem B7365725 : Blo 1291964 7365725 := bstep (se 3 (by rfl) ⟨1381073, by rfl⟩ : syracuseStep 7365725 = 2762147) B2762147
theorem B3105985 : Blo 1291964 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B4908235 : Blo 1291964 4908235 := bstep (se 1 (by rfl) ⟨3681176, by rfl⟩ : syracuseStep 4908235 = 7362353) B7362353
theorem B2909465 : Blo 1291964 2909465 := bstep (se 2 (by rfl) ⟨1091049, by rfl⟩ : syracuseStep 2909465 = 2182099) B2182099
theorem B2909555 : Blo 1291964 2909555 := bstep (se 1 (by rfl) ⟨2182166, by rfl⟩ : syracuseStep 2909555 = 4364333) B4364333
theorem B2762113 : Blo 1291964 2762113 := bstep (se 2 (by rfl) ⟨1035792, by rfl⟩ : syracuseStep 2762113 = 2071585) B2071585
theorem B2909591 : Blo 1291964 2909591 := bstep (se 1 (by rfl) ⟨2182193, by rfl⟩ : syracuseStep 2909591 = 4364387) B4364387
theorem B2180567 : Blo 1291964 2180567 := bstep (se 1 (by rfl) ⟨1635425, by rfl⟩ : syracuseStep 2180567 = 3270851) B3270851
theorem B6546905 : Blo 1291964 6546905 := bstep (se 2 (by rfl) ⟨2455089, by rfl⟩ : syracuseStep 6546905 = 4910179) B4910179
theorem B4908509 : Blo 1291964 4908509 := bstep (se 3 (by rfl) ⟨920345, by rfl⟩ : syracuseStep 4908509 = 1840691) B1840691
theorem B5596723 : Blo 1291964 5596723 := bstep (se 1 (by rfl) ⟨4197542, by rfl⟩ : syracuseStep 5596723 = 8395085) B8395085
theorem B5522995 : Blo 1291964 5522995 := bstep (se 1 (by rfl) ⟨4142246, by rfl⟩ : syracuseStep 5522995 = 8284493) B8284493
theorem B2909771 : Blo 1291964 2909771 := bstep (se 1 (by rfl) ⟨2182328, by rfl⟩ : syracuseStep 2909771 = 4364657) B4364657
theorem B2180695 : Blo 1291964 2180695 := bstep (se 1 (by rfl) ⟨1635521, by rfl⟩ : syracuseStep 2180695 = 3271043) B3271043
theorem B2909825 : Blo 1291964 2909825 := bstep (se 2 (by rfl) ⟨1091184, by rfl⟩ : syracuseStep 2909825 = 2182369) B2182369
theorem B27961037 : Blo 1291964 27961037 := bstep (se 3 (by rfl) ⟨5242694, by rfl⟩ : syracuseStep 27961037 = 10485389) B10485389
theorem B2910041 : Blo 1291964 2910041 := bstep (se 2 (by rfl) ⟨1091265, by rfl⟩ : syracuseStep 2910041 = 2182531) B2182531
theorem B4663129 : Blo 1291964 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B5244803 : Blo 1291964 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B1746841 : Blo 1291964 1746841 := bstep (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) B1310131
theorem B2910131 : Blo 1291964 2910131 := bstep (se 1 (by rfl) ⟨2182598, by rfl⟩ : syracuseStep 2910131 = 4365197) B4365197
theorem B2910167 : Blo 1291964 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B1746905 : Blo 1291964 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B3541085 : Blo 1291964 3541085 := bstep (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) B1327907
theorem B2910347 : Blo 1291964 2910347 := bstep (se 1 (by rfl) ⟨2182760, by rfl⟩ : syracuseStep 2910347 = 4365521) B4365521
theorem B4909207 : Blo 1291964 4909207 := bstep (se 1 (by rfl) ⟨3681905, by rfl⟩ : syracuseStep 4909207 = 7363811) B7363811
theorem B2910401 : Blo 1291964 2910401 := bstep (se 2 (by rfl) ⟨1091400, by rfl⟩ : syracuseStep 2910401 = 2182801) B2182801
theorem B2181323 : Blo 1291964 2181323 := bstep (se 1 (by rfl) ⟨1635992, by rfl⟩ : syracuseStep 2181323 = 3271985) B3271985
theorem B2328833 : Blo 1291964 2328833 := bstep (se 2 (by rfl) ⟨873312, by rfl⟩ : syracuseStep 2328833 = 1746625) B1746625
theorem B4360499 : Blo 1291964 4360499 := bstep (se 1 (by rfl) ⟨3270374, by rfl⟩ : syracuseStep 4360499 = 6540749) B6540749
theorem B2181451 : Blo 1291964 2181451 := bstep (se 1 (by rfl) ⟨1636088, by rfl⟩ : syracuseStep 2181451 = 3272177) B3272177
theorem B3271063 : Blo 1291964 3271063 := bstep (se 1 (by rfl) ⟨2453297, by rfl⟩ : syracuseStep 3271063 = 4906595) B4906595
theorem B2910617 : Blo 1291964 2910617 := bstep (se 2 (by rfl) ⟨1091481, by rfl⟩ : syracuseStep 2910617 = 2182963) B2182963
theorem B2329049 : Blo 1291964 2329049 := bstep (se 2 (by rfl) ⟨873393, by rfl⟩ : syracuseStep 2329049 = 1746787) B1746787
theorem B2181593 : Blo 1291964 2181593 := bstep (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) B1636195
theorem B2910707 : Blo 1291964 2910707 := bstep (se 1 (by rfl) ⟨2183030, by rfl⟩ : syracuseStep 2910707 = 4366061) B4366061
theorem B2910743 : Blo 1291964 2910743 := bstep (se 1 (by rfl) ⟨2183057, by rfl⟩ : syracuseStep 2910743 = 4366115) B4366115
theorem B9955885 : Blo 1291964 9955885 := bstep (se 3 (by rfl) ⟨1866728, by rfl⟩ : syracuseStep 9955885 = 3733457) B3733457
theorem B4360769 : Blo 1291964 4360769 := bstep (se 2 (by rfl) ⟨1635288, by rfl⟩ : syracuseStep 4360769 = 3270577) B3270577
theorem B5245505 : Blo 1291964 5245505 := bstep (se 2 (by rfl) ⟨1967064, by rfl⟩ : syracuseStep 5245505 = 3934129) B3934129
theorem B2181721 : Blo 1291964 2181721 := bstep (se 2 (by rfl) ⟨818145, by rfl⟩ : syracuseStep 2181721 = 1636291) B1636291
theorem B5900951 : Blo 1291964 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B3107531 : Blo 1291964 3107531 := bstep (se 1 (by rfl) ⟨2330648, by rfl⟩ : syracuseStep 3107531 = 4661297) B4661297
theorem B2910923 : Blo 1291964 2910923 := bstep (se 1 (by rfl) ⟨2183192, by rfl⟩ : syracuseStep 2910923 = 4366385) B4366385
theorem B2910977 : Blo 1291964 2910977 := bstep (se 2 (by rfl) ⟨1091616, by rfl⟩ : syracuseStep 2910977 = 2183233) B2183233
theorem B3271499 : Blo 1291964 3271499 := bstep (se 1 (by rfl) ⟨2453624, by rfl⟩ : syracuseStep 3271499 = 4907249) B4907249
theorem B4909997 : Blo 1291964 4909997 := bstep (se 3 (by rfl) ⟨920624, by rfl⟩ : syracuseStep 4909997 = 1841249) B1841249
theorem B2395097 : Blo 1291964 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B2911193 : Blo 1291964 2911193 := bstep (se 2 (by rfl) ⟨1091697, by rfl⟩ : syracuseStep 2911193 = 2183395) B2183395
theorem B5524483 : Blo 1291964 5524483 := bstep (se 1 (by rfl) ⟨4143362, by rfl⟩ : syracuseStep 5524483 = 8286725) B8286725
theorem B6548525 : Blo 1291964 6548525 := bstep (se 3 (by rfl) ⟨1227848, by rfl⟩ : syracuseStep 6548525 = 2455697) B2455697
theorem B2911283 : Blo 1291964 2911283 := bstep (se 1 (by rfl) ⟨2183462, by rfl⟩ : syracuseStep 2911283 = 4366925) B4366925
theorem B2911319 : Blo 1291964 2911319 := bstep (se 1 (by rfl) ⟨2183489, by rfl⟩ : syracuseStep 2911319 = 4366979) B4366979
theorem B4361309 : Blo 1291964 4361309 := bstep (se 3 (by rfl) ⟨817745, by rfl⟩ : syracuseStep 4361309 = 1635491) B1635491
theorem B7359619 : Blo 1291964 7359619 := bstep (se 1 (by rfl) ⟨5519714, by rfl⟩ : syracuseStep 7359619 = 11039429) B11039429
theorem B2182295 : Blo 1291964 2182295 := bstep (se 1 (by rfl) ⟨1636721, by rfl⟩ : syracuseStep 2182295 = 3273443) B3273443
theorem B3271873 : Blo 1291964 3271873 := bstep (se 2 (by rfl) ⟨1226952, by rfl⟩ : syracuseStep 3271873 = 2453905) B2453905
theorem B2182423 : Blo 1291964 2182423 := bstep (se 1 (by rfl) ⟨1636817, by rfl⟩ : syracuseStep 2182423 = 3273635) B3273635
theorem B3681587 : Blo 1291964 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B5893469 : Blo 1291964 5893469 := bstep (se 3 (by rfl) ⟨1105025, by rfl⟩ : syracuseStep 5893469 = 2210051) B2210051
theorem B1453495 : Blo 1291964 1453495 := bstep (se 1 (by rfl) ⟨1090121, by rfl⟩ : syracuseStep 1453495 = 2180243) B2180243
theorem B2452979 : Blo 1291964 2452979 := bstep (se 1 (by rfl) ⟨1839734, by rfl⟩ : syracuseStep 2452979 = 3679469) B3679469
theorem B2453017 : Blo 1291964 2453017 := bstep (se 2 (by rfl) ⟨919881, by rfl⟩ : syracuseStep 2453017 = 1839763) B1839763
theorem B5525081 : Blo 1291964 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B1453675 : Blo 1291964 1453675 := bstep (se 1 (by rfl) ⟨1090256, by rfl⟩ : syracuseStep 1453675 = 2180513) B2180513
theorem B9326285 : Blo 1291964 9326285 := bstep (se 3 (by rfl) ⟨1748678, by rfl⟩ : syracuseStep 9326285 = 3497357) B3497357
theorem B1453783 : Blo 1291964 1453783 := bstep (se 1 (by rfl) ⟨1090337, by rfl⟩ : syracuseStep 1453783 = 2180675) B2180675
theorem B6541073 : Blo 1291964 6541073 := bstep (se 2 (by rfl) ⟨2452902, by rfl⟩ : syracuseStep 6541073 = 4905805) B4905805
theorem B3272471 : Blo 1291964 3272471 := bstep (se 1 (by rfl) ⟨2454353, by rfl⟩ : syracuseStep 3272471 = 4908707) B4908707
theorem B16568165 : Blo 1291964 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B1453963 : Blo 1291964 1453963 := bstep (se 1 (by rfl) ⟨1090472, by rfl⟩ : syracuseStep 1453963 = 2180945) B2180945
theorem B2183051 : Blo 1291964 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B6541235 : Blo 1291964 6541235 := bstep (se 1 (by rfl) ⟨4905926, by rfl⟩ : syracuseStep 6541235 = 9811853) B9811853
theorem B5525441 : Blo 1291964 5525441 := bstep (se 2 (by rfl) ⟨2072040, by rfl⟩ : syracuseStep 5525441 = 4144081) B4144081
theorem B1552343 : Blo 1291964 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B2453465 : Blo 1291964 2453465 := bstep (se 2 (by rfl) ⟨920049, by rfl⟩ : syracuseStep 2453465 = 1840099) B1840099
theorem B1454071 : Blo 1291964 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B2183179 : Blo 1291964 2183179 := bstep (se 1 (by rfl) ⟨1637384, by rfl⟩ : syracuseStep 2183179 = 3274769) B3274769
theorem B6213677 : Blo 1291964 6213677 := bstep (se 3 (by rfl) ⟨1165064, by rfl⟩ : syracuseStep 6213677 = 2330129) B2330129
theorem B1380407 : Blo 1291964 1380407 := bstep (se 1 (by rfl) ⟨1035305, by rfl⟩ : syracuseStep 1380407 = 2070611) B2070611
theorem B7360577 : Blo 1291964 7360577 := bstep (se 2 (by rfl) ⟨2760216, by rfl⟩ : syracuseStep 7360577 = 5520433) B5520433
theorem B1552459 : Blo 1291964 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B4141145 : Blo 1291964 4141145 := bstep (se 2 (by rfl) ⟨1552929, by rfl⟩ : syracuseStep 4141145 = 3105859) B3105859
theorem B2183321 : Blo 1291964 2183321 := bstep (se 2 (by rfl) ⟨818745, by rfl⟩ : syracuseStep 2183321 = 1637491) B1637491
theorem B1454251 : Blo 1291964 1454251 := bstep (se 1 (by rfl) ⟨1090688, by rfl⟩ : syracuseStep 1454251 = 2181377) B2181377
theorem B4362443 : Blo 1291964 4362443 := bstep (se 1 (by rfl) ⟨3271832, by rfl⟩ : syracuseStep 4362443 = 6543665) B6543665
theorem B1454359 : Blo 1291964 1454359 := bstep (se 1 (by rfl) ⟨1090769, by rfl⟩ : syracuseStep 1454359 = 2181539) B2181539
theorem B2183449 : Blo 1291964 2183449 := bstep (se 2 (by rfl) ⟨818793, by rfl⟩ : syracuseStep 2183449 = 1637587) B1637587
theorem B4911425 : Blo 1291964 4911425 := bstep (se 2 (by rfl) ⟨1841784, by rfl⟩ : syracuseStep 4911425 = 3683569) B3683569
theorem B59683189 : Blo 1291964 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B1454539 : Blo 1291964 1454539 := bstep (se 1 (by rfl) ⟨1090904, by rfl⟩ : syracuseStep 1454539 = 2181809) B2181809
theorem B4362713 : Blo 1291964 4362713 := bstep (se 2 (by rfl) ⟨1636017, by rfl⟩ : syracuseStep 4362713 = 3272035) B3272035
theorem B1454647 : Blo 1291964 1454647 := bstep (se 1 (by rfl) ⟨1090985, by rfl⟩ : syracuseStep 1454647 = 2181971) B2181971
theorem B3273281 : Blo 1291964 3273281 := bstep (se 2 (by rfl) ⟨1227480, by rfl⟩ : syracuseStep 3273281 = 2454961) B2454961
theorem B1938059 : Blo 1291964 1938059 := bstep (se 1 (by rfl) ⟨1453544, by rfl⟩ : syracuseStep 1938059 = 2907089) B2907089
theorem B1938071 : Blo 1291964 1938071 := bstep (se 1 (by rfl) ⟨1453553, by rfl⟩ : syracuseStep 1938071 = 2907107) B2907107
theorem B2454209 : Blo 1291964 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B1938137 : Blo 1291964 1938137 := bstep (se 2 (by rfl) ⟨726801, by rfl⟩ : syracuseStep 1938137 = 1453603) B1453603
theorem B1454827 : Blo 1291964 1454827 := bstep (se 1 (by rfl) ⟨1091120, by rfl⟩ : syracuseStep 1454827 = 2182241) B2182241
theorem B15717185 : Blo 1291964 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B1938251 : Blo 1291964 1938251 := bstep (se 1 (by rfl) ⟨1453688, by rfl⟩ : syracuseStep 1938251 = 2907377) B2907377
theorem B1938263 : Blo 1291964 1938263 := bstep (se 1 (by rfl) ⟨1453697, by rfl⟩ : syracuseStep 1938263 = 2907395) B2907395
theorem B1454935 : Blo 1291964 1454935 := bstep (se 1 (by rfl) ⟨1091201, by rfl⟩ : syracuseStep 1454935 = 2182403) B2182403
theorem B8622949 : Blo 1291964 8622949 := bstep (se 4 (by rfl) ⟨808401, by rfl⟩ : syracuseStep 8622949 = 1616803) B1616803
theorem B1635223 : Blo 1291964 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B1938329 : Blo 1291964 1938329 := bstep (se 2 (by rfl) ⟨726873, by rfl⟩ : syracuseStep 1938329 = 1453747) B1453747
theorem B22385585 : Blo 1291964 22385585 := bstep (se 2 (by rfl) ⟨8394594, by rfl⟩ : syracuseStep 22385585 = 16789189) B16789189
theorem B2454475 : Blo 1291964 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B1840087 : Blo 1291964 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B1938443 : Blo 1291964 1938443 := bstep (se 1 (by rfl) ⟨1453832, by rfl⟩ : syracuseStep 1938443 = 2907665) B2907665
theorem B1455115 : Blo 1291964 1455115 := bstep (se 1 (by rfl) ⟨1091336, by rfl⟩ : syracuseStep 1455115 = 2182673) B2182673
theorem B75576341 : Blo 1291964 75576341 := bstep (se 6 (by rfl) ⟨1771320, by rfl⟩ : syracuseStep 75576341 = 3542641) B3542641
theorem B1938455 : Blo 1291964 1938455 := bstep (se 1 (by rfl) ⟨1453841, by rfl⟩ : syracuseStep 1938455 = 2907683) B2907683
theorem B1938521 : Blo 1291964 1938521 := bstep (se 2 (by rfl) ⟨726945, by rfl⟩ : syracuseStep 1938521 = 1453891) B1453891
theorem B3273817 : Blo 1291964 3273817 := bstep (se 2 (by rfl) ⟨1227681, by rfl⟩ : syracuseStep 3273817 = 2455363) B2455363
theorem B1455223 : Blo 1291964 1455223 := bstep (se 1 (by rfl) ⟨1091417, by rfl⟩ : syracuseStep 1455223 = 2182835) B2182835
theorem B8287363 : Blo 1291964 8287363 := bstep (se 1 (by rfl) ⟨6215522, by rfl⟩ : syracuseStep 8287363 = 12431045) B12431045
theorem B4363415 : Blo 1291964 4363415 := bstep (se 1 (by rfl) ⟨3272561, by rfl⟩ : syracuseStep 4363415 = 6545123) B6545123
theorem B1938635 : Blo 1291964 1938635 := bstep (se 1 (by rfl) ⟨1453976, by rfl⟩ : syracuseStep 1938635 = 2907953) B2907953
theorem B1938647 : Blo 1291964 1938647 := bstep (se 1 (by rfl) ⟨1453985, by rfl⟩ : syracuseStep 1938647 = 2907971) B2907971
theorem B1938713 : Blo 1291964 1938713 := bstep (se 2 (by rfl) ⟨727017, by rfl⟩ : syracuseStep 1938713 = 1454035) B1454035
theorem B1455403 : Blo 1291964 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B1938827 : Blo 1291964 1938827 := bstep (se 1 (by rfl) ⟨1454120, by rfl⟩ : syracuseStep 1938827 = 2908241) B2908241
theorem B2454923 : Blo 1291964 2454923 := bstep (se 1 (by rfl) ⟨1841192, by rfl⟩ : syracuseStep 2454923 = 3682385) B3682385
theorem B1938839 : Blo 1291964 1938839 := bstep (se 1 (by rfl) ⟨1454129, by rfl⟩ : syracuseStep 1938839 = 2908259) B2908259
theorem B1455511 : Blo 1291964 1455511 := bstep (se 1 (by rfl) ⟨1091633, by rfl⟩ : syracuseStep 1455511 = 2183267) B2183267
theorem B1938905 : Blo 1291964 1938905 := bstep (se 2 (by rfl) ⟨727089, by rfl⟩ : syracuseStep 1938905 = 1454179) B1454179
theorem B2070041 : Blo 1291964 2070041 := bstep (se 2 (by rfl) ⟨776265, by rfl⟩ : syracuseStep 2070041 = 1552531) B1552531
theorem B4142657 : Blo 1291964 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B2455105 : Blo 1291964 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B1939019 : Blo 1291964 1939019 := bstep (se 1 (by rfl) ⟨1454264, by rfl⟩ : syracuseStep 1939019 = 2908529) B2908529
theorem B1455691 : Blo 1291964 1455691 := bstep (se 1 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 1455691 = 2183537) B2183537
theorem B1939031 : Blo 1291964 1939031 := bstep (se 1 (by rfl) ⟨1454273, by rfl⟩ : syracuseStep 1939031 = 2908547) B2908547
theorem B25204355 : Blo 1291964 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B1939097 : Blo 1291964 1939097 := bstep (se 2 (by rfl) ⟨727161, by rfl⟩ : syracuseStep 1939097 = 1454323) B1454323
theorem B4363955 : Blo 1291964 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B1291979 : Blo 1291964 1291979 := bstep (se 1 (by rfl) ⟨968984, by rfl⟩ : syracuseStep 1291979 = 1937969) B1937969
theorem B1291991 : Blo 1291964 1291991 := bstep (se 1 (by rfl) ⟨968993, by rfl⟩ : syracuseStep 1291991 = 1937987) B1937987
theorem B1292011 : Blo 1291964 1292011 := bstep (se 1 (by rfl) ⟨969008, by rfl⟩ : syracuseStep 1292011 = 1938017) B1938017
theorem B1292023 : Blo 1291964 1292023 := bstep (se 1 (by rfl) ⟨969017, by rfl⟩ : syracuseStep 1292023 = 1938035) B1938035
theorem B1292043 : Blo 1291964 1292043 := bstep (se 1 (by rfl) ⟨969032, by rfl⟩ : syracuseStep 1292043 = 1938065) B1938065
theorem B1939211 : Blo 1291964 1939211 := bstep (se 1 (by rfl) ⟨1454408, by rfl⟩ : syracuseStep 1939211 = 2908817) B2908817
theorem B4912913 : Blo 1291964 4912913 := bstep (se 2 (by rfl) ⟨1842342, by rfl⟩ : syracuseStep 4912913 = 3684685) B3684685
theorem B1292055 : Blo 1291964 1292055 := bstep (se 1 (by rfl) ⟨969041, by rfl⟩ : syracuseStep 1292055 = 1938083) B1938083
theorem B1939223 : Blo 1291964 1939223 := bstep (se 1 (by rfl) ⟨1454417, by rfl⟩ : syracuseStep 1939223 = 2908835) B2908835
theorem B2488087 : Blo 1291964 2488087 := bstep (se 1 (by rfl) ⟨1866065, by rfl⟩ : syracuseStep 2488087 = 3732131) B3732131
theorem B1292075 : Blo 1291964 1292075 := bstep (se 1 (by rfl) ⟨969056, by rfl⟩ : syracuseStep 1292075 = 1938113) B1938113
theorem B1292087 : Blo 1291964 1292087 := bstep (se 1 (by rfl) ⟨969065, by rfl⟩ : syracuseStep 1292087 = 1938131) B1938131
theorem B1292107 : Blo 1291964 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B6543179 : Blo 1291964 6543179 := bstep (se 1 (by rfl) ⟨4907384, by rfl⟩ : syracuseStep 6543179 = 9814769) B9814769
theorem B1292119 : Blo 1291964 1292119 := bstep (se 1 (by rfl) ⟨969089, by rfl⟩ : syracuseStep 1292119 = 1938179) B1938179
theorem B1939289 : Blo 1291964 1939289 := bstep (se 2 (by rfl) ⟨727233, by rfl⟩ : syracuseStep 1939289 = 1454467) B1454467
theorem B1292139 : Blo 1291964 1292139 := bstep (se 1 (by rfl) ⟨969104, by rfl⟩ : syracuseStep 1292139 = 1938209) B1938209
theorem B1292151 : Blo 1291964 1292151 := bstep (se 1 (by rfl) ⟨969113, by rfl⟩ : syracuseStep 1292151 = 1938227) B1938227
theorem B1292171 : Blo 1291964 1292171 := bstep (se 1 (by rfl) ⟨969128, by rfl⟩ : syracuseStep 1292171 = 1938257) B1938257
theorem B1292183 : Blo 1291964 1292183 := bstep (se 1 (by rfl) ⟨969137, by rfl⟩ : syracuseStep 1292183 = 1938275) B1938275
theorem B2455447 : Blo 1291964 2455447 := bstep (se 1 (by rfl) ⟨1841585, by rfl⟩ : syracuseStep 2455447 = 3683171) B3683171
theorem B1292203 : Blo 1291964 1292203 := bstep (se 1 (by rfl) ⟨969152, by rfl⟩ : syracuseStep 1292203 = 1938305) B1938305
theorem B3684275 : Blo 1291964 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B1292215 : Blo 1291964 1292215 := bstep (se 1 (by rfl) ⟨969161, by rfl⟩ : syracuseStep 1292215 = 1938323) B1938323
theorem B4364225 : Blo 1291964 4364225 := bstep (se 2 (by rfl) ⟨1636584, by rfl⟩ : syracuseStep 4364225 = 3273169) B3273169
theorem B1292235 : Blo 1291964 1292235 := bstep (se 1 (by rfl) ⟨969176, by rfl⟩ : syracuseStep 1292235 = 1938353) B1938353
theorem B1939403 : Blo 1291964 1939403 := bstep (se 1 (by rfl) ⟨1454552, by rfl⟩ : syracuseStep 1939403 = 2909105) B2909105
theorem B1292247 : Blo 1291964 1292247 := bstep (se 1 (by rfl) ⟨969185, by rfl⟩ : syracuseStep 1292247 = 1938371) B1938371
theorem B1939415 : Blo 1291964 1939415 := bstep (se 1 (by rfl) ⟨1454561, by rfl⟩ : syracuseStep 1939415 = 2909123) B2909123
theorem B1292267 : Blo 1291964 1292267 := bstep (se 1 (by rfl) ⟨969200, by rfl⟩ : syracuseStep 1292267 = 1938401) B1938401
theorem B1292279 : Blo 1291964 1292279 := bstep (se 1 (by rfl) ⟨969209, by rfl⟩ : syracuseStep 1292279 = 1938419) B1938419
theorem B1292299 : Blo 1291964 1292299 := bstep (se 1 (by rfl) ⟨969224, by rfl⟩ : syracuseStep 1292299 = 1938449) B1938449
theorem B1292311 : Blo 1291964 1292311 := bstep (se 1 (by rfl) ⟨969233, by rfl⟩ : syracuseStep 1292311 = 1938467) B1938467
theorem B1939481 : Blo 1291964 1939481 := bstep (se 2 (by rfl) ⟨727305, by rfl⟩ : syracuseStep 1939481 = 1454611) B1454611
theorem B1292331 : Blo 1291964 1292331 := bstep (se 1 (by rfl) ⟨969248, by rfl⟩ : syracuseStep 1292331 = 1938497) B1938497
theorem B7977005 : Blo 1291964 7977005 := bstep (se 3 (by rfl) ⟨1495688, by rfl⟩ : syracuseStep 7977005 = 2991377) B2991377
theorem B1292343 : Blo 1291964 1292343 := bstep (se 1 (by rfl) ⟨969257, by rfl⟩ : syracuseStep 1292343 = 1938515) B1938515
theorem B1292363 : Blo 1291964 1292363 := bstep (se 1 (by rfl) ⟨969272, by rfl⟩ : syracuseStep 1292363 = 1938545) B1938545
theorem B1292375 : Blo 1291964 1292375 := bstep (se 1 (by rfl) ⟨969281, by rfl⟩ : syracuseStep 1292375 = 1938563) B1938563
theorem B6994021 : Blo 1291964 6994021 := bstep (se 4 (by rfl) ⟨655689, by rfl⟩ : syracuseStep 6994021 = 1311379) B1311379
theorem B1292395 : Blo 1291964 1292395 := bstep (se 1 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 1292395 = 1938593) B1938593
theorem B2455667 : Blo 1291964 2455667 := bstep (se 1 (by rfl) ⟨1841750, by rfl⟩ : syracuseStep 2455667 = 3683501) B3683501
theorem B1292407 : Blo 1291964 1292407 := bstep (se 1 (by rfl) ⟨969305, by rfl⟩ : syracuseStep 1292407 = 1938611) B1938611
theorem B1292427 : Blo 1291964 1292427 := bstep (se 1 (by rfl) ⟨969320, by rfl⟩ : syracuseStep 1292427 = 1938641) B1938641
theorem B1939595 : Blo 1291964 1939595 := bstep (se 1 (by rfl) ⟨1454696, by rfl⟩ : syracuseStep 1939595 = 2909393) B2909393
theorem B2209943 : Blo 1291964 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1292439 : Blo 1291964 1292439 := bstep (se 1 (by rfl) ⟨969329, by rfl⟩ : syracuseStep 1292439 = 1938659) B1938659
theorem B1939607 : Blo 1291964 1939607 := bstep (se 1 (by rfl) ⟨1454705, by rfl⟩ : syracuseStep 1939607 = 2909411) B2909411
theorem B6215831 : Blo 1291964 6215831 := bstep (se 1 (by rfl) ⟨4661873, by rfl⟩ : syracuseStep 6215831 = 9323747) B9323747
theorem B3684503 : Blo 1291964 3684503 := bstep (se 1 (by rfl) ⟨2763377, by rfl⟩ : syracuseStep 3684503 = 5526755) B5526755
theorem B1292459 : Blo 1291964 1292459 := bstep (se 1 (by rfl) ⟨969344, by rfl⟩ : syracuseStep 1292459 = 1938689) B1938689
theorem B3274931 : Blo 1291964 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B1292471 : Blo 1291964 1292471 := bstep (se 1 (by rfl) ⟨969353, by rfl⟩ : syracuseStep 1292471 = 1938707) B1938707
theorem B1292491 : Blo 1291964 1292491 := bstep (se 1 (by rfl) ⟨969368, by rfl⟩ : syracuseStep 1292491 = 1938737) B1938737
theorem B1292503 : Blo 1291964 1292503 := bstep (se 1 (by rfl) ⟨969377, by rfl⟩ : syracuseStep 1292503 = 1938755) B1938755
theorem B1939673 : Blo 1291964 1939673 := bstep (se 2 (by rfl) ⟨727377, by rfl⟩ : syracuseStep 1939673 = 1454755) B1454755
theorem B1292523 : Blo 1291964 1292523 := bstep (se 1 (by rfl) ⟨969392, by rfl⟩ : syracuseStep 1292523 = 1938785) B1938785
theorem B1292535 : Blo 1291964 1292535 := bstep (se 1 (by rfl) ⟨969401, by rfl⟩ : syracuseStep 1292535 = 1938803) B1938803
theorem B1292555 : Blo 1291964 1292555 := bstep (se 1 (by rfl) ⟨969416, by rfl⟩ : syracuseStep 1292555 = 1938833) B1938833
theorem B6994193 : Blo 1291964 6994193 := bstep (se 2 (by rfl) ⟨2622822, by rfl⟩ : syracuseStep 6994193 = 5245645) B5245645
theorem B1292567 : Blo 1291964 1292567 := bstep (se 1 (by rfl) ⟨969425, by rfl⟩ : syracuseStep 1292567 = 1938851) B1938851
theorem B1292587 : Blo 1291964 1292587 := bstep (se 1 (by rfl) ⟨969440, by rfl⟩ : syracuseStep 1292587 = 1938881) B1938881
theorem B11041069 : Blo 1291964 11041069 := bstep (se 3 (by rfl) ⟨2070200, by rfl⟩ : syracuseStep 11041069 = 4140401) B4140401
theorem B1292599 : Blo 1291964 1292599 := bstep (se 1 (by rfl) ⟨969449, by rfl⟩ : syracuseStep 1292599 = 1938899) B1938899
theorem B1292619 : Blo 1291964 1292619 := bstep (se 1 (by rfl) ⟨969464, by rfl⟩ : syracuseStep 1292619 = 1938929) B1938929
theorem B1939787 : Blo 1291964 1939787 := bstep (se 1 (by rfl) ⟨1454840, by rfl⟩ : syracuseStep 1939787 = 2909681) B2909681
theorem B1292631 : Blo 1291964 1292631 := bstep (se 1 (by rfl) ⟨969473, by rfl⟩ : syracuseStep 1292631 = 1938947) B1938947
theorem B1939799 : Blo 1291964 1939799 := bstep (se 1 (by rfl) ⟨1454849, by rfl⟩ : syracuseStep 1939799 = 2909699) B2909699
theorem B2455895 : Blo 1291964 2455895 := bstep (se 1 (by rfl) ⟨1841921, by rfl⟩ : syracuseStep 2455895 = 3683843) B3683843
theorem B1292651 : Blo 1291964 1292651 := bstep (se 1 (by rfl) ⟨969488, by rfl⟩ : syracuseStep 1292651 = 1938977) B1938977
theorem B1292663 : Blo 1291964 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B1292683 : Blo 1291964 1292683 := bstep (se 1 (by rfl) ⟨969512, by rfl⟩ : syracuseStep 1292683 = 1939025) B1939025
theorem B11188631 : Blo 1291964 11188631 := bstep (se 1 (by rfl) ⟨8391473, by rfl⟩ : syracuseStep 11188631 = 16782947) B16782947
theorem B1292695 : Blo 1291964 1292695 := bstep (se 1 (by rfl) ⟨969521, by rfl⟩ : syracuseStep 1292695 = 1939043) B1939043
theorem B1939865 : Blo 1291964 1939865 := bstep (se 2 (by rfl) ⟨727449, by rfl⟩ : syracuseStep 1939865 = 1454899) B1454899
theorem B9959831 : Blo 1291964 9959831 := bstep (se 1 (by rfl) ⟨7469873, by rfl⟩ : syracuseStep 9959831 = 14939747) B14939747
theorem B1292715 : Blo 1291964 1292715 := bstep (se 1 (by rfl) ⟨969536, by rfl⟩ : syracuseStep 1292715 = 1939073) B1939073
theorem B1292727 : Blo 1291964 1292727 := bstep (se 1 (by rfl) ⟨969545, by rfl⟩ : syracuseStep 1292727 = 1939091) B1939091
theorem B1292747 : Blo 1291964 1292747 := bstep (se 1 (by rfl) ⟨969560, by rfl⟩ : syracuseStep 1292747 = 1939121) B1939121
theorem B1292759 : Blo 1291964 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B3275225 : Blo 1291964 3275225 := bstep (se 2 (by rfl) ⟨1228209, by rfl⟩ : syracuseStep 3275225 = 2456419) B2456419
theorem B4364765 : Blo 1291964 4364765 := bstep (se 3 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 4364765 = 1636787) B1636787
theorem B1292779 : Blo 1291964 1292779 := bstep (se 1 (by rfl) ⟨969584, by rfl⟩ : syracuseStep 1292779 = 1939169) B1939169
theorem B1292791 : Blo 1291964 1292791 := bstep (se 1 (by rfl) ⟨969593, by rfl⟩ : syracuseStep 1292791 = 1939187) B1939187
theorem B1292811 : Blo 1291964 1292811 := bstep (se 1 (by rfl) ⟨969608, by rfl⟩ : syracuseStep 1292811 = 1939217) B1939217
theorem B1939979 : Blo 1291964 1939979 := bstep (se 1 (by rfl) ⟨1454984, by rfl⟩ : syracuseStep 1939979 = 2909969) B2909969
theorem B1292823 : Blo 1291964 1292823 := bstep (se 1 (by rfl) ⟨969617, by rfl⟩ : syracuseStep 1292823 = 1939235) B1939235
theorem B1939991 : Blo 1291964 1939991 := bstep (se 1 (by rfl) ⟨1454993, by rfl⟩ : syracuseStep 1939991 = 2909987) B2909987
theorem B1292843 : Blo 1291964 1292843 := bstep (se 1 (by rfl) ⟨969632, by rfl⟩ : syracuseStep 1292843 = 1939265) B1939265
theorem B1292855 : Blo 1291964 1292855 := bstep (se 1 (by rfl) ⟨969641, by rfl⟩ : syracuseStep 1292855 = 1939283) B1939283
theorem B2488897 : Blo 1291964 2488897 := bstep (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) B1866673
theorem B3734081 : Blo 1291964 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B1292875 : Blo 1291964 1292875 := bstep (se 1 (by rfl) ⟨969656, by rfl⟩ : syracuseStep 1292875 = 1939313) B1939313
theorem B1636939 : Blo 1291964 1636939 := bstep (se 1 (by rfl) ⟨1227704, by rfl⟩ : syracuseStep 1636939 = 2455409) B2455409
theorem B1292887 : Blo 1291964 1292887 := bstep (se 1 (by rfl) ⟨969665, by rfl⟩ : syracuseStep 1292887 = 1939331) B1939331
theorem B1940057 : Blo 1291964 1940057 := bstep (se 2 (by rfl) ⟨727521, by rfl⟩ : syracuseStep 1940057 = 1455043) B1455043
theorem B2456153 : Blo 1291964 2456153 := bstep (se 2 (by rfl) ⟨921057, by rfl⟩ : syracuseStep 2456153 = 1842115) B1842115
theorem B1292907 : Blo 1291964 1292907 := bstep (se 1 (by rfl) ⟨969680, by rfl⟩ : syracuseStep 1292907 = 1939361) B1939361
theorem B1292919 : Blo 1291964 1292919 := bstep (se 1 (by rfl) ⟨969689, by rfl⟩ : syracuseStep 1292919 = 1939379) B1939379
theorem B2521729 : Blo 1291964 2521729 := bstep (se 2 (by rfl) ⟨945648, by rfl⟩ : syracuseStep 2521729 = 1891297) B1891297
theorem B1292939 : Blo 1291964 1292939 := bstep (se 1 (by rfl) ⟨969704, by rfl⟩ : syracuseStep 1292939 = 1939409) B1939409
theorem B4905623 : Blo 1291964 4905623 := bstep (se 1 (by rfl) ⟨3679217, by rfl⟩ : syracuseStep 4905623 = 7358435) B7358435
theorem B1292951 : Blo 1291964 1292951 := bstep (se 1 (by rfl) ⟨969713, by rfl⟩ : syracuseStep 1292951 = 1939427) B1939427
theorem B1292971 : Blo 1291964 1292971 := bstep (se 1 (by rfl) ⟨969728, by rfl⟩ : syracuseStep 1292971 = 1939457) B1939457
theorem B6216371 : Blo 1291964 6216371 := bstep (se 1 (by rfl) ⟨4662278, by rfl⟩ : syracuseStep 6216371 = 9324557) B9324557
theorem B1292983 : Blo 1291964 1292983 := bstep (se 1 (by rfl) ⟨969737, by rfl⟩ : syracuseStep 1292983 = 1939475) B1939475
theorem B1293003 : Blo 1291964 1293003 := bstep (se 1 (by rfl) ⟨969752, by rfl⟩ : syracuseStep 1293003 = 1939505) B1939505
theorem B1940171 : Blo 1291964 1940171 := bstep (se 1 (by rfl) ⟨1455128, by rfl⟩ : syracuseStep 1940171 = 2910257) B2910257
theorem B1293015 : Blo 1291964 1293015 := bstep (se 1 (by rfl) ⟨969761, by rfl⟩ : syracuseStep 1293015 = 1939523) B1939523
theorem B1940183 : Blo 1291964 1940183 := bstep (se 1 (by rfl) ⟨1455137, by rfl⟩ : syracuseStep 1940183 = 2910275) B2910275
theorem B1293035 : Blo 1291964 1293035 := bstep (se 1 (by rfl) ⟨969776, by rfl⟩ : syracuseStep 1293035 = 1939553) B1939553
theorem B1293047 : Blo 1291964 1293047 := bstep (se 1 (by rfl) ⟨969785, by rfl⟩ : syracuseStep 1293047 = 1939571) B1939571
theorem B16571141 : Blo 1291964 16571141 := bstep (se 4 (by rfl) ⟨1553544, by rfl⟩ : syracuseStep 16571141 = 3107089) B3107089
theorem B1293067 : Blo 1291964 1293067 := bstep (se 1 (by rfl) ⟨969800, by rfl⟩ : syracuseStep 1293067 = 1939601) B1939601
theorem B1293079 : Blo 1291964 1293079 := bstep (se 1 (by rfl) ⟨969809, by rfl⟩ : syracuseStep 1293079 = 1939619) B1939619
theorem B1940249 : Blo 1291964 1940249 := bstep (se 2 (by rfl) ⟨727593, by rfl⟩ : syracuseStep 1940249 = 1455187) B1455187
theorem B1293099 : Blo 1291964 1293099 := bstep (se 1 (by rfl) ⟨969824, by rfl⟩ : syracuseStep 1293099 = 1939649) B1939649
theorem B1293111 : Blo 1291964 1293111 := bstep (se 1 (by rfl) ⟨969833, by rfl⟩ : syracuseStep 1293111 = 1939667) B1939667
theorem B2906945 : Blo 1291964 2906945 := bstep (se 2 (by rfl) ⟨1090104, by rfl⟩ : syracuseStep 2906945 = 2180209) B2180209
theorem B1293131 : Blo 1291964 1293131 := bstep (se 1 (by rfl) ⟨969848, by rfl⟩ : syracuseStep 1293131 = 1939697) B1939697
theorem B1293143 : Blo 1291964 1293143 := bstep (se 1 (by rfl) ⟨969857, by rfl⟩ : syracuseStep 1293143 = 1939715) B1939715
theorem B5241689 : Blo 1291964 5241689 := bstep (se 2 (by rfl) ⟨1965633, by rfl⟩ : syracuseStep 5241689 = 3931267) B3931267
theorem B1293163 : Blo 1291964 1293163 := bstep (se 1 (by rfl) ⟨969872, by rfl⟩ : syracuseStep 1293163 = 1939745) B1939745
theorem B1293175 : Blo 1291964 1293175 := bstep (se 1 (by rfl) ⟨969881, by rfl⟩ : syracuseStep 1293175 = 1939763) B1939763
theorem B1293195 : Blo 1291964 1293195 := bstep (se 1 (by rfl) ⟨969896, by rfl⟩ : syracuseStep 1293195 = 1939793) B1939793
theorem B1940363 : Blo 1291964 1940363 := bstep (se 1 (by rfl) ⟨1455272, by rfl⟩ : syracuseStep 1940363 = 2910545) B2910545
theorem B1293207 : Blo 1291964 1293207 := bstep (se 1 (by rfl) ⟨969905, by rfl⟩ : syracuseStep 1293207 = 1939811) B1939811
theorem B1940375 : Blo 1291964 1940375 := bstep (se 1 (by rfl) ⟨1455281, by rfl⟩ : syracuseStep 1940375 = 2910563) B2910563
theorem B1293227 : Blo 1291964 1293227 := bstep (se 1 (by rfl) ⟨969920, by rfl⟩ : syracuseStep 1293227 = 1939841) B1939841
theorem B1293239 : Blo 1291964 1293239 := bstep (se 1 (by rfl) ⟨969929, by rfl⟩ : syracuseStep 1293239 = 1939859) B1939859
theorem B1293259 : Blo 1291964 1293259 := bstep (se 1 (by rfl) ⟨969944, by rfl⟩ : syracuseStep 1293259 = 1939889) B1939889
theorem B1293271 : Blo 1291964 1293271 := bstep (se 1 (by rfl) ⟨969953, by rfl⟩ : syracuseStep 1293271 = 1939907) B1939907
theorem B1940441 : Blo 1291964 1940441 := bstep (se 2 (by rfl) ⟨727665, by rfl⟩ : syracuseStep 1940441 = 1455331) B1455331
theorem B3496925 : Blo 1291964 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B1293291 : Blo 1291964 1293291 := bstep (se 1 (by rfl) ⟨969968, by rfl⟩ : syracuseStep 1293291 = 1939937) B1939937
theorem B1293303 : Blo 1291964 1293303 := bstep (se 1 (by rfl) ⟨969977, by rfl⟩ : syracuseStep 1293303 = 1939955) B1939955
theorem B1293323 : Blo 1291964 1293323 := bstep (se 1 (by rfl) ⟨969992, by rfl⟩ : syracuseStep 1293323 = 1939985) B1939985
theorem B7863313 : Blo 1291964 7863313 := bstep (se 2 (by rfl) ⟨2948742, by rfl⟩ : syracuseStep 7863313 = 5897485) B5897485
theorem B4660247 : Blo 1291964 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B1293335 : Blo 1291964 1293335 := bstep (se 1 (by rfl) ⟨970001, by rfl⟩ : syracuseStep 1293335 = 1940003) B1940003
theorem B2907161 : Blo 1291964 2907161 := bstep (se 2 (by rfl) ⟨1090185, by rfl⟩ : syracuseStep 2907161 = 2180371) B2180371
theorem B1293355 : Blo 1291964 1293355 := bstep (se 1 (by rfl) ⟨970016, by rfl⟩ : syracuseStep 1293355 = 1940033) B1940033
theorem B1293367 : Blo 1291964 1293367 := bstep (se 1 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 1293367 = 1940051) B1940051
theorem B1293387 : Blo 1291964 1293387 := bstep (se 1 (by rfl) ⟨970040, by rfl⟩ : syracuseStep 1293387 = 1940081) B1940081
theorem B1940555 : Blo 1291964 1940555 := bstep (se 1 (by rfl) ⟨1455416, by rfl⟩ : syracuseStep 1940555 = 2910833) B2910833
theorem B1293399 : Blo 1291964 1293399 := bstep (se 1 (by rfl) ⟨970049, by rfl⟩ : syracuseStep 1293399 = 1940099) B1940099
theorem B1940567 : Blo 1291964 1940567 := bstep (se 1 (by rfl) ⟨1455425, by rfl⟩ : syracuseStep 1940567 = 2910851) B2910851
theorem B1293419 : Blo 1291964 1293419 := bstep (se 1 (by rfl) ⟨970064, by rfl⟩ : syracuseStep 1293419 = 1940129) B1940129
theorem B2907251 : Blo 1291964 2907251 := bstep (se 1 (by rfl) ⟨2180438, by rfl⟩ : syracuseStep 2907251 = 4360877) B4360877
theorem B1293431 : Blo 1291964 1293431 := bstep (se 1 (by rfl) ⟨970073, by rfl⟩ : syracuseStep 1293431 = 1940147) B1940147
theorem B6208643 : Blo 1291964 6208643 := bstep (se 1 (by rfl) ⟨4656482, by rfl⟩ : syracuseStep 6208643 = 9312965) B9312965
theorem B1293451 : Blo 1291964 1293451 := bstep (se 1 (by rfl) ⟨970088, by rfl⟩ : syracuseStep 1293451 = 1940177) B1940177
theorem B2907287 : Blo 1291964 2907287 := bstep (se 1 (by rfl) ⟨2180465, by rfl⟩ : syracuseStep 2907287 = 4360931) B4360931
theorem B37264535 : Blo 1291964 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B4660375 : Blo 1291964 4660375 := bstep (se 1 (by rfl) ⟨3495281, by rfl⟩ : syracuseStep 4660375 = 6990563) B6990563
theorem B1293463 : Blo 1291964 1293463 := bstep (se 1 (by rfl) ⟨970097, by rfl⟩ : syracuseStep 1293463 = 1940195) B1940195
theorem B1940633 : Blo 1291964 1940633 := bstep (se 2 (by rfl) ⟨727737, by rfl⟩ : syracuseStep 1940633 = 1455475) B1455475
theorem B1293483 : Blo 1291964 1293483 := bstep (se 1 (by rfl) ⟨970112, by rfl⟩ : syracuseStep 1293483 = 1940225) B1940225
theorem B1293495 : Blo 1291964 1293495 := bstep (se 1 (by rfl) ⟨970121, by rfl⟩ : syracuseStep 1293495 = 1940243) B1940243
theorem B1293515 : Blo 1291964 1293515 := bstep (se 1 (by rfl) ⟨970136, by rfl⟩ : syracuseStep 1293515 = 1940273) B1940273
theorem B1293527 : Blo 1291964 1293527 := bstep (se 1 (by rfl) ⟨970145, by rfl⟩ : syracuseStep 1293527 = 1940291) B1940291
theorem B1293547 : Blo 1291964 1293547 := bstep (se 1 (by rfl) ⟨970160, by rfl⟩ : syracuseStep 1293547 = 1940321) B1940321
theorem B1293559 : Blo 1291964 1293559 := bstep (se 1 (by rfl) ⟨970169, by rfl⟩ : syracuseStep 1293559 = 1940339) B1940339
theorem B1293579 : Blo 1291964 1293579 := bstep (se 1 (by rfl) ⟨970184, by rfl⟩ : syracuseStep 1293579 = 1940369) B1940369
theorem B1940747 : Blo 1291964 1940747 := bstep (se 1 (by rfl) ⟨1455560, by rfl⟩ : syracuseStep 1940747 = 2911121) B2911121
theorem B1293591 : Blo 1291964 1293591 := bstep (se 1 (by rfl) ⟨970193, by rfl⟩ : syracuseStep 1293591 = 1940387) B1940387
theorem B1940759 : Blo 1291964 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B1400107 : Blo 1291964 1400107 := bstep (se 1 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 1400107 = 2100161) B2100161
theorem B1293611 : Blo 1291964 1293611 := bstep (se 1 (by rfl) ⟨970208, by rfl⟩ : syracuseStep 1293611 = 1940417) B1940417
theorem B4906291 : Blo 1291964 4906291 := bstep (se 1 (by rfl) ⟨3679718, by rfl⟩ : syracuseStep 4906291 = 7359437) B7359437
theorem B2759987 : Blo 1291964 2759987 := bstep (se 1 (by rfl) ⟨2069990, by rfl⟩ : syracuseStep 2759987 = 4139981) B4139981
theorem B1293623 : Blo 1291964 1293623 := bstep (se 1 (by rfl) ⟨970217, by rfl⟩ : syracuseStep 1293623 = 1940435) B1940435
theorem B2907467 : Blo 1291964 2907467 := bstep (se 1 (by rfl) ⟨2180600, by rfl⟩ : syracuseStep 2907467 = 4361201) B4361201
theorem B1293643 : Blo 1291964 1293643 := bstep (se 1 (by rfl) ⟨970232, by rfl⟩ : syracuseStep 1293643 = 1940465) B1940465
theorem B1293655 : Blo 1291964 1293655 := bstep (se 1 (by rfl) ⟨970241, by rfl⟩ : syracuseStep 1293655 = 1940483) B1940483
theorem B1940825 : Blo 1291964 1940825 := bstep (se 2 (by rfl) ⟨727809, by rfl⟩ : syracuseStep 1940825 = 1455619) B1455619
theorem B1293675 : Blo 1291964 1293675 := bstep (se 1 (by rfl) ⟨970256, by rfl⟩ : syracuseStep 1293675 = 1940513) B1940513
theorem B1293687 : Blo 1291964 1293687 := bstep (se 1 (by rfl) ⟨970265, by rfl⟩ : syracuseStep 1293687 = 1940531) B1940531
theorem B2907521 : Blo 1291964 2907521 := bstep (se 2 (by rfl) ⟨1090320, by rfl⟩ : syracuseStep 2907521 = 2180641) B2180641
theorem B1293707 : Blo 1291964 1293707 := bstep (se 1 (by rfl) ⟨970280, by rfl⟩ : syracuseStep 1293707 = 1940561) B1940561
theorem B1293719 : Blo 1291964 1293719 := bstep (se 1 (by rfl) ⟨970289, by rfl⟩ : syracuseStep 1293719 = 1940579) B1940579
theorem B1293739 : Blo 1291964 1293739 := bstep (se 1 (by rfl) ⟨970304, by rfl⟩ : syracuseStep 1293739 = 1940609) B1940609
theorem B1293751 : Blo 1291964 1293751 := bstep (se 1 (by rfl) ⟨970313, by rfl⟩ : syracuseStep 1293751 = 1940627) B1940627
theorem B1293771 : Blo 1291964 1293771 := bstep (se 1 (by rfl) ⟨970328, by rfl⟩ : syracuseStep 1293771 = 1940657) B1940657
theorem B1940939 : Blo 1291964 1940939 := bstep (se 1 (by rfl) ⟨1455704, by rfl⟩ : syracuseStep 1940939 = 2911409) B2911409
theorem B10485197 : Blo 1291964 10485197 := bstep (se 3 (by rfl) ⟨1965974, by rfl⟩ : syracuseStep 10485197 = 3931949) B3931949
theorem B1293783 : Blo 1291964 1293783 := bstep (se 1 (by rfl) ⟨970337, by rfl⟩ : syracuseStep 1293783 = 1940675) B1940675
theorem B37289443 : Blo 1291964 37289443 := bstep (se 1 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 37289443 = 55934165) B55934165
theorem B1293803 : Blo 1291964 1293803 := bstep (se 1 (by rfl) ⟨970352, by rfl⟩ : syracuseStep 1293803 = 1940705) B1940705
theorem B1293815 : Blo 1291964 1293815 := bstep (se 1 (by rfl) ⟨970361, by rfl⟩ : syracuseStep 1293815 = 1940723) B1940723
theorem B1293835 : Blo 1291964 1293835 := bstep (se 1 (by rfl) ⟨970376, by rfl⟩ : syracuseStep 1293835 = 1940753) B1940753
theorem B1293847 : Blo 1291964 1293847 := bstep (se 1 (by rfl) ⟨970385, by rfl⟩ : syracuseStep 1293847 = 1940771) B1940771
theorem B1293867 : Blo 1291964 1293867 := bstep (se 1 (by rfl) ⟨970400, by rfl⟩ : syracuseStep 1293867 = 1940801) B1940801
theorem B1293879 : Blo 1291964 1293879 := bstep (se 1 (by rfl) ⟨970409, by rfl⟩ : syracuseStep 1293879 = 1940819) B1940819
theorem B6544961 : Blo 1291964 6544961 := bstep (se 2 (by rfl) ⟨2454360, by rfl⟩ : syracuseStep 6544961 = 4908721) B4908721
theorem B4365899 : Blo 1291964 4365899 := bstep (se 1 (by rfl) ⟨3274424, by rfl⟩ : syracuseStep 4365899 = 6548849) B6548849
theorem B1293899 : Blo 1291964 1293899 := bstep (se 1 (by rfl) ⟨970424, by rfl⟩ : syracuseStep 1293899 = 1940849) B1940849
theorem B1293911 : Blo 1291964 1293911 := bstep (se 1 (by rfl) ⟨970433, by rfl⟩ : syracuseStep 1293911 = 1940867) B1940867
theorem B2907737 : Blo 1291964 2907737 := bstep (se 2 (by rfl) ⟨1090401, by rfl⟩ : syracuseStep 2907737 = 2180803) B2180803
theorem B11042405 : Blo 1291964 11042405 := bstep (se 4 (by rfl) ⟨1035225, by rfl⟩ : syracuseStep 11042405 = 2070451) B2070451
theorem B1293931 : Blo 1291964 1293931 := bstep (se 1 (by rfl) ⟨970448, by rfl⟩ : syracuseStep 1293931 = 1940897) B1940897
theorem B1293943 : Blo 1291964 1293943 := bstep (se 1 (by rfl) ⟨970457, by rfl⟩ : syracuseStep 1293943 = 1940915) B1940915
theorem B18636419 : Blo 1291964 18636419 := bstep (se 1 (by rfl) ⟨13977314, by rfl⟩ : syracuseStep 18636419 = 27954629) B27954629
theorem B1293963 : Blo 1291964 1293963 := bstep (se 1 (by rfl) ⟨970472, by rfl⟩ : syracuseStep 1293963 = 1940945) B1940945
theorem B2907827 : Blo 1291964 2907827 := bstep (se 1 (by rfl) ⟨2180870, by rfl⟩ : syracuseStep 2907827 = 4361741) B4361741
theorem B2907863 : Blo 1291964 2907863 := bstep (se 1 (by rfl) ⟨2180897, by rfl⟩ : syracuseStep 2907863 = 4361795) B4361795
theorem B2211545 : Blo 1291964 2211545 := bstep (se 2 (by rfl) ⟨829329, by rfl⟩ : syracuseStep 2211545 = 1658659) B1658659
theorem B4144861 : Blo 1291964 4144861 := bstep (se 3 (by rfl) ⟨777161, by rfl⟩ : syracuseStep 4144861 = 1554323) B1554323
theorem B6209297 : Blo 1291964 6209297 := bstep (se 2 (by rfl) ⟨2328486, by rfl⟩ : syracuseStep 6209297 = 4656973) B4656973
theorem B2760473 : Blo 1291964 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B4366169 : Blo 1291964 4366169 := bstep (se 2 (by rfl) ⟨1637313, by rfl⟩ : syracuseStep 4366169 = 3274627) B3274627
theorem B2908043 : Blo 1291964 2908043 := bstep (se 1 (by rfl) ⟨2181032, by rfl⟩ : syracuseStep 2908043 = 4362065) B4362065
theorem B11198359 : Blo 1291964 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B4661171 : Blo 1291964 4661171 := bstep (se 1 (by rfl) ⟨3495878, by rfl⟩ : syracuseStep 4661171 = 6991757) B6991757
theorem B33611699 : Blo 1291964 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B2908097 : Blo 1291964 2908097 := bstep (se 2 (by rfl) ⟨1090536, by rfl⟩ : syracuseStep 2908097 = 2181073) B2181073
theorem B5521355 : Blo 1291964 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B5898269 : Blo 1291964 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B4907051 : Blo 1291964 4907051 := bstep (se 1 (by rfl) ⟨3680288, by rfl⟩ : syracuseStep 4907051 = 7360577) B7360577
theorem B2908295 : Blo 1291964 2908295 := bstep (se 1 (by rfl) ⟨2181221, by rfl⟩ : syracuseStep 2908295 = 4362443) B4362443
theorem B6545609 : Blo 1291964 6545609 := bstep (se 2 (by rfl) ⟨2454603, by rfl⟩ : syracuseStep 6545609 = 4909207) B4909207
theorem B11043053 : Blo 1291964 11043053 := bstep (se 3 (by rfl) ⟨2070572, by rfl⟩ : syracuseStep 11043053 = 4141145) B4141145
theorem B2908475 : Blo 1291964 2908475 := bstep (se 1 (by rfl) ⟨2181356, by rfl⟩ : syracuseStep 2908475 = 4362713) B4362713
theorem B14721425 : Blo 1291964 14721425 := bstep (se 2 (by rfl) ⟨5520534, by rfl⟩ : syracuseStep 14721425 = 11041069) B11041069
theorem B2908601 : Blo 1291964 2908601 := bstep (se 2 (by rfl) ⟨1090725, by rfl⟩ : syracuseStep 2908601 = 2181451) B2181451
theorem B79577585 : Blo 1291964 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B1966607 : Blo 1291964 1966607 := bstep (se 1 (by rfl) ⟨1474955, by rfl⟩ : syracuseStep 1966607 = 2949911) B2949911
theorem B10478123 : Blo 1291964 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B5522039 : Blo 1291964 5522039 := bstep (se 1 (by rfl) ⟨4141529, by rfl⟩ : syracuseStep 5522039 = 8283059) B8283059
theorem B3318529 : Blo 1291964 3318529 := bstep (se 2 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 3318529 = 2488897) B2488897
theorem B2908943 : Blo 1291964 2908943 := bstep (se 1 (by rfl) ⟨2181707, by rfl⟩ : syracuseStep 2908943 = 4363415) B4363415
theorem B2908961 : Blo 1291964 2908961 := bstep (se 2 (by rfl) ⟨1090860, by rfl⟩ : syracuseStep 2908961 = 2181721) B2181721
theorem B2761771 : Blo 1291964 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B16802903 : Blo 1291964 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B2909303 : Blo 1291964 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B2180297 : Blo 1291964 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B2909483 : Blo 1291964 2909483 := bstep (se 1 (by rfl) ⟨2182112, by rfl⟩ : syracuseStep 2909483 = 4364225) B4364225
theorem B7365977 : Blo 1291964 7365977 := bstep (se 2 (by rfl) ⟨2762241, by rfl⟩ : syracuseStep 7365977 = 5524483) B5524483
theorem B5318003 : Blo 1291964 5318003 := bstep (se 1 (by rfl) ⟨3988502, by rfl⟩ : syracuseStep 5318003 = 7977005) B7977005
theorem B2360723 : Blo 1291964 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B2909843 : Blo 1291964 2909843 := bstep (se 1 (by rfl) ⟨2182382, by rfl⟩ : syracuseStep 2909843 = 4364765) B4364765
theorem B2909897 : Blo 1291964 2909897 := bstep (se 2 (by rfl) ⟨1091211, by rfl⟩ : syracuseStep 2909897 = 2182423) B2182423
theorem B3270415 : Blo 1291964 3270415 := bstep (se 1 (by rfl) ⟨2452811, by rfl⟩ : syracuseStep 3270415 = 4905623) B4905623
theorem B2180999 : Blo 1291964 2180999 := bstep (se 1 (by rfl) ⟨1635749, by rfl⟩ : syracuseStep 2180999 = 3271499) B3271499
theorem B49719257 : Blo 1291964 49719257 := bstep (se 2 (by rfl) ⟨18644721, by rfl⟩ : syracuseStep 49719257 = 37289443) B37289443
theorem B3106831 : Blo 1291964 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B3270689 : Blo 1291964 3270689 := bstep (se 2 (by rfl) ⟨1226508, by rfl⟩ : syracuseStep 3270689 = 2453017) B2453017
theorem B4139095 : Blo 1291964 4139095 := bstep (se 1 (by rfl) ⟨3104321, by rfl⟩ : syracuseStep 4139095 = 6208643) B6208643
theorem B238749869 : Blo 1291964 238749869 := bstep (se 3 (by rfl) ⟨44765600, by rfl⟩ : syracuseStep 238749869 = 89531201) B89531201
theorem B6990131 : Blo 1291964 6990131 := bstep (se 1 (by rfl) ⟨5242598, by rfl⟩ : syracuseStep 6990131 = 10485197) B10485197
theorem B2910599 : Blo 1291964 2910599 := bstep (se 1 (by rfl) ⟨2182949, by rfl⟩ : syracuseStep 2910599 = 4365899) B4365899
theorem B89631197 : Blo 1291964 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B4360715 : Blo 1291964 4360715 := bstep (se 1 (by rfl) ⟨3270536, by rfl⟩ : syracuseStep 4360715 = 6541073) B6541073
theorem B4139531 : Blo 1291964 4139531 := bstep (se 1 (by rfl) ⟨3104648, by rfl⟩ : syracuseStep 4139531 = 6209297) B6209297
theorem B2181647 : Blo 1291964 2181647 := bstep (se 1 (by rfl) ⟨1636235, by rfl⟩ : syracuseStep 2181647 = 3272471) B3272471
theorem B2329121 : Blo 1291964 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B2910779 : Blo 1291964 2910779 := bstep (se 1 (by rfl) ⟨2183084, by rfl⟩ : syracuseStep 2910779 = 4366169) B4366169
theorem B4139581 : Blo 1291964 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B11045443 : Blo 1291964 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B4360823 : Blo 1291964 4360823 := bstep (se 1 (by rfl) ⟨3270617, by rfl⟩ : syracuseStep 4360823 = 6541235) B6541235
theorem B3107447 : Blo 1291964 3107447 := bstep (se 1 (by rfl) ⟨2330585, by rfl⟩ : syracuseStep 3107447 = 4661171) B4661171
theorem B3680903 : Blo 1291964 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B2910905 : Blo 1291964 2910905 := bstep (se 2 (by rfl) ⟨1091589, by rfl⟩ : syracuseStep 2910905 = 2183179) B2183179
theorem B9325361 : Blo 1291964 9325361 := bstep (se 2 (by rfl) ⟨3497010, by rfl⟩ : syracuseStep 9325361 = 6994021) B6994021
theorem B3730295 : Blo 1291964 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B3271691 : Blo 1291964 3271691 := bstep (se 1 (by rfl) ⟨2453768, by rfl⟩ : syracuseStep 3271691 = 4907537) B4907537
theorem B2911247 : Blo 1291964 2911247 := bstep (se 1 (by rfl) ⟨2183435, by rfl⟩ : syracuseStep 2911247 = 4366871) B4366871
theorem B2911265 : Blo 1291964 2911265 := bstep (se 2 (by rfl) ⟨1091724, by rfl⟩ : syracuseStep 2911265 = 2183449) B2183449
theorem B2182187 : Blo 1291964 2182187 := bstep (se 1 (by rfl) ⟨1636640, by rfl⟩ : syracuseStep 2182187 = 3273281) B3273281
theorem B5893181 : Blo 1291964 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B1748155 : Blo 1291964 1748155 := bstep (se 1 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 1748155 = 2622233) B2622233
theorem B4361417 : Blo 1291964 4361417 := bstep (se 2 (by rfl) ⟨1635531, by rfl⟩ : syracuseStep 4361417 = 3271063) B3271063
theorem B14724341 : Blo 1291964 14724341 := bstep (se 5 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 14724341 = 1380407) B1380407
theorem B2452751 : Blo 1291964 2452751 := bstep (se 1 (by rfl) ⟨1839563, by rfl⟩ : syracuseStep 2452751 = 3679127) B3679127
theorem B50384227 : Blo 1291964 50384227 := bstep (se 1 (by rfl) ⟨37788170, by rfl⟩ : syracuseStep 50384227 = 75576341) B75576341
theorem B13274513 : Blo 1291964 13274513 := bstep (se 2 (by rfl) ⟨4977942, by rfl⟩ : syracuseStep 13274513 = 9955885) B9955885
theorem B4910483 : Blo 1291964 4910483 := bstep (se 1 (by rfl) ⟨3682862, by rfl⟩ : syracuseStep 4910483 = 7365725) B7365725
theorem B2182585 : Blo 1291964 2182585 := bstep (se 2 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 2182585 = 1636939) B1636939
theorem B3362305 : Blo 1291964 3362305 := bstep (se 2 (by rfl) ⟨1260864, by rfl⟩ : syracuseStep 3362305 = 2521729) B2521729
theorem B1453711 : Blo 1291964 1453711 := bstep (se 1 (by rfl) ⟨1090283, by rfl⟩ : syracuseStep 1453711 = 2180567) B2180567
theorem B3272339 : Blo 1291964 3272339 := bstep (se 1 (by rfl) ⟨2454254, by rfl⟩ : syracuseStep 3272339 = 4908509) B4908509
theorem B11497265 : Blo 1291964 11497265 := bstep (se 2 (by rfl) ⟨4311474, by rfl⟩ : syracuseStep 11497265 = 8622949) B8622949
theorem B18640691 : Blo 1291964 18640691 := bstep (se 1 (by rfl) ⟨13980518, by rfl⟩ : syracuseStep 18640691 = 27961037) B27961037
theorem B4362119 : Blo 1291964 4362119 := bstep (se 1 (by rfl) ⟨3271589, by rfl⟩ : syracuseStep 4362119 = 6543179) B6543179
theorem B3272633 : Blo 1291964 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B2183287 : Blo 1291964 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B1454215 : Blo 1291964 1454215 := bstep (se 1 (by rfl) ⟨1090661, by rfl⟩ : syracuseStep 1454215 = 2181323) B2181323
theorem B1552555 : Blo 1291964 1552555 := bstep (se 1 (by rfl) ⟨1164416, by rfl⟩ : syracuseStep 1552555 = 2328833) B2328833
theorem B6213833 : Blo 1291964 6213833 := bstep (se 2 (by rfl) ⟨2330187, by rfl⟩ : syracuseStep 6213833 = 4660375) B4660375
theorem B4362497 : Blo 1291964 4362497 := bstep (se 2 (by rfl) ⟨1635936, by rfl⟩ : syracuseStep 4362497 = 3271873) B3271873
theorem B4141313 : Blo 1291964 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B7459087 : Blo 1291964 7459087 := bstep (se 1 (by rfl) ⟨5594315, by rfl⟩ : syracuseStep 7459087 = 11188631) B11188631
theorem B6639887 : Blo 1291964 6639887 := bstep (se 1 (by rfl) ⟨4979915, by rfl⟩ : syracuseStep 6639887 = 9959831) B9959831
theorem B1552699 : Blo 1291964 1552699 := bstep (se 1 (by rfl) ⟨1164524, by rfl⟩ : syracuseStep 1552699 = 2329049) B2329049
theorem B1454395 : Blo 1291964 1454395 := bstep (se 1 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 1454395 = 2181593) B2181593
theorem B2183483 : Blo 1291964 2183483 := bstep (se 1 (by rfl) ⟨1637612, by rfl⟩ : syracuseStep 2183483 = 3275225) B3275225
theorem B6541721 : Blo 1291964 6541721 := bstep (se 2 (by rfl) ⟨2453145, by rfl⟩ : syracuseStep 6541721 = 4906291) B4906291
theorem B3682817 : Blo 1291964 3682817 := bstep (se 2 (by rfl) ⟨1381056, by rfl⟩ : syracuseStep 3682817 = 2762113) B2762113
theorem B11047427 : Blo 1291964 11047427 := bstep (se 1 (by rfl) ⟨8285570, by rfl⟩ : syracuseStep 11047427 = 16571141) B16571141
theorem B8286749 : Blo 1291964 8286749 := bstep (se 3 (by rfl) ⟨1553765, by rfl⟩ : syracuseStep 8286749 = 3107531) B3107531
theorem B1937963 : Blo 1291964 1937963 := bstep (se 1 (by rfl) ⟨1453472, by rfl⟩ : syracuseStep 1937963 = 2906945) B2906945
theorem B3494459 : Blo 1291964 3494459 := bstep (se 1 (by rfl) ⟨2620844, by rfl⟩ : syracuseStep 3494459 = 5241689) B5241689
theorem B1937993 : Blo 1291964 1937993 := bstep (se 2 (by rfl) ⟨726747, by rfl⟩ : syracuseStep 1937993 = 1453495) B1453495
theorem B3273331 : Blo 1291964 3273331 := bstep (se 1 (by rfl) ⟨2454998, by rfl⟩ : syracuseStep 3273331 = 4909997) B4909997
theorem B2331283 : Blo 1291964 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B1938107 : Blo 1291964 1938107 := bstep (se 1 (by rfl) ⟨1453580, by rfl⟩ : syracuseStep 1938107 = 2907161) B2907161
theorem B1938167 : Blo 1291964 1938167 := bstep (se 1 (by rfl) ⟨1453625, by rfl⟩ : syracuseStep 1938167 = 2907251) B2907251
theorem B3273473 : Blo 1291964 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B1938191 : Blo 1291964 1938191 := bstep (se 1 (by rfl) ⟨1453643, by rfl⟩ : syracuseStep 1938191 = 2907287) B2907287
theorem B24843023 : Blo 1291964 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B1454863 : Blo 1291964 1454863 := bstep (se 1 (by rfl) ⟨1091147, by rfl⟩ : syracuseStep 1454863 = 2182295) B2182295
theorem B1938233 : Blo 1291964 1938233 := bstep (se 2 (by rfl) ⟨726837, by rfl⟩ : syracuseStep 1938233 = 1453675) B1453675
theorem B1839991 : Blo 1291964 1839991 := bstep (se 1 (by rfl) ⟨1379993, by rfl⟩ : syracuseStep 1839991 = 2759987) B2759987
theorem B2454391 : Blo 1291964 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B1938311 : Blo 1291964 1938311 := bstep (se 1 (by rfl) ⟨1453733, by rfl⟩ : syracuseStep 1938311 = 2907467) B2907467
theorem B3928979 : Blo 1291964 3928979 := bstep (se 1 (by rfl) ⟨2946734, by rfl⟩ : syracuseStep 3928979 = 5893469) B5893469
theorem B1938347 : Blo 1291964 1938347 := bstep (se 1 (by rfl) ⟨1453760, by rfl⟩ : syracuseStep 1938347 = 2907521) B2907521
theorem B1938377 : Blo 1291964 1938377 := bstep (se 2 (by rfl) ⟨726891, by rfl⟩ : syracuseStep 1938377 = 1453783) B1453783
theorem B5526481 : Blo 1291964 5526481 := bstep (se 2 (by rfl) ⟨2072430, by rfl⟩ : syracuseStep 5526481 = 4144861) B4144861
theorem B1635319 : Blo 1291964 1635319 := bstep (se 1 (by rfl) ⟨1226489, by rfl⟩ : syracuseStep 1635319 = 2452979) B2452979
theorem B4363307 : Blo 1291964 4363307 := bstep (se 1 (by rfl) ⟨3272480, by rfl⟩ : syracuseStep 4363307 = 6544961) B6544961
theorem B1938491 : Blo 1291964 1938491 := bstep (se 1 (by rfl) ⟨1453868, by rfl⟩ : syracuseStep 1938491 = 2907737) B2907737
theorem B3683387 : Blo 1291964 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B7361603 : Blo 1291964 7361603 := bstep (se 1 (by rfl) ⟨5521202, by rfl⟩ : syracuseStep 7361603 = 11042405) B11042405
theorem B12424279 : Blo 1291964 12424279 := bstep (se 1 (by rfl) ⟨9318209, by rfl⟩ : syracuseStep 12424279 = 18636419) B18636419
theorem B1938551 : Blo 1291964 1938551 := bstep (se 1 (by rfl) ⟨1453913, by rfl⟩ : syracuseStep 1938551 = 2907827) B2907827
theorem B1938575 : Blo 1291964 1938575 := bstep (se 1 (by rfl) ⟨1453931, by rfl⟩ : syracuseStep 1938575 = 2907863) B2907863
theorem B1938617 : Blo 1291964 1938617 := bstep (se 2 (by rfl) ⟨726981, by rfl⟩ : syracuseStep 1938617 = 1453963) B1453963
theorem B1840315 : Blo 1291964 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B14931145 : Blo 1291964 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B3273929 : Blo 1291964 3273929 := bstep (se 2 (by rfl) ⟨1227723, by rfl⟩ : syracuseStep 3273929 = 2455447) B2455447
theorem B4658413 : Blo 1291964 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B1938695 : Blo 1291964 1938695 := bstep (se 1 (by rfl) ⟨1454021, by rfl⟩ : syracuseStep 1938695 = 2908043) B2908043
theorem B1455367 : Blo 1291964 1455367 := bstep (se 1 (by rfl) ⟨1091525, by rfl⟩ : syracuseStep 1455367 = 2183051) B2183051
theorem B1938731 : Blo 1291964 1938731 := bstep (se 1 (by rfl) ⟨1454048, by rfl⟩ : syracuseStep 1938731 = 2908097) B2908097
theorem B3683627 : Blo 1291964 3683627 := bstep (se 1 (by rfl) ⟨2762720, by rfl⟩ : syracuseStep 3683627 = 5525441) B5525441
theorem B1635643 : Blo 1291964 1635643 := bstep (se 1 (by rfl) ⟨1226732, by rfl⟩ : syracuseStep 1635643 = 2453465) B2453465
theorem B1938761 : Blo 1291964 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B2069945 : Blo 1291964 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B1938875 : Blo 1291964 1938875 := bstep (se 1 (by rfl) ⟨1454156, by rfl⟩ : syracuseStep 1938875 = 2908313) B2908313
theorem B1455547 : Blo 1291964 1455547 := bstep (se 1 (by rfl) ⟨1091660, by rfl⟩ : syracuseStep 1455547 = 2183321) B2183321
theorem B16569805 : Blo 1291964 16569805 := bstep (se 3 (by rfl) ⟨3106838, by rfl⟩ : syracuseStep 16569805 = 6213677) B6213677
theorem B1938935 : Blo 1291964 1938935 := bstep (se 1 (by rfl) ⟨1454201, by rfl⟩ : syracuseStep 1938935 = 2908403) B2908403
theorem B1938959 : Blo 1291964 1938959 := bstep (se 1 (by rfl) ⟨1454219, by rfl⟩ : syracuseStep 1938959 = 2908439) B2908439
theorem B3274283 : Blo 1291964 3274283 := bstep (se 1 (by rfl) ⟨2455712, by rfl⟩ : syracuseStep 3274283 = 4911425) B4911425
theorem B1939001 : Blo 1291964 1939001 := bstep (se 2 (by rfl) ⟨727125, by rfl⟩ : syracuseStep 1939001 = 1454251) B1454251
theorem B6723191 : Blo 1291964 6723191 := bstep (se 1 (by rfl) ⟨5042393, by rfl⟩ : syracuseStep 6723191 = 10084787) B10084787
theorem B1939079 : Blo 1291964 1939079 := bstep (se 1 (by rfl) ⟨1454309, by rfl⟩ : syracuseStep 1939079 = 2908619) B2908619
theorem B1939115 : Blo 1291964 1939115 := bstep (se 1 (by rfl) ⟨1454336, by rfl⟩ : syracuseStep 1939115 = 2908673) B2908673
theorem B1939145 : Blo 1291964 1939145 := bstep (se 2 (by rfl) ⟨727179, by rfl⟩ : syracuseStep 1939145 = 1454359) B1454359
theorem B1292039 : Blo 1291964 1292039 := bstep (se 1 (by rfl) ⟨969029, by rfl⟩ : syracuseStep 1292039 = 1938059) B1938059
theorem B1292047 : Blo 1291964 1292047 := bstep (se 1 (by rfl) ⟨969035, by rfl⟩ : syracuseStep 1292047 = 1938071) B1938071
theorem B1636139 : Blo 1291964 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B1292091 : Blo 1291964 1292091 := bstep (se 1 (by rfl) ⟨969068, by rfl⟩ : syracuseStep 1292091 = 1938137) B1938137
theorem B1939259 : Blo 1291964 1939259 := bstep (se 1 (by rfl) ⟨1454444, by rfl⟩ : syracuseStep 1939259 = 2908889) B2908889
theorem B1939319 : Blo 1291964 1939319 := bstep (se 1 (by rfl) ⟨1454489, by rfl⟩ : syracuseStep 1939319 = 2908979) B2908979
theorem B1292167 : Blo 1291964 1292167 := bstep (se 1 (by rfl) ⟨969125, by rfl⟩ : syracuseStep 1292167 = 1938251) B1938251
theorem B1292175 : Blo 1291964 1292175 := bstep (se 1 (by rfl) ⟨969131, by rfl⟩ : syracuseStep 1292175 = 1938263) B1938263
theorem B1939343 : Blo 1291964 1939343 := bstep (se 1 (by rfl) ⟨1454507, by rfl⟩ : syracuseStep 1939343 = 2909015) B2909015
theorem B1939385 : Blo 1291964 1939385 := bstep (se 2 (by rfl) ⟨727269, by rfl⟩ : syracuseStep 1939385 = 1454539) B1454539
theorem B1292219 : Blo 1291964 1292219 := bstep (se 1 (by rfl) ⟨969164, by rfl⟩ : syracuseStep 1292219 = 1938329) B1938329
theorem B14923723 : Blo 1291964 14923723 := bstep (se 1 (by rfl) ⟨11192792, by rfl⟩ : syracuseStep 14923723 = 22385585) B22385585
theorem B1292295 : Blo 1291964 1292295 := bstep (se 1 (by rfl) ⟨969221, by rfl⟩ : syracuseStep 1292295 = 1938443) B1938443
theorem B1939463 : Blo 1291964 1939463 := bstep (se 1 (by rfl) ⟨1454597, by rfl⟩ : syracuseStep 1939463 = 2909195) B2909195
theorem B7182347 : Blo 1291964 7182347 := bstep (se 1 (by rfl) ⟨5386760, by rfl⟩ : syracuseStep 7182347 = 10773521) B10773521
theorem B1292303 : Blo 1291964 1292303 := bstep (se 1 (by rfl) ⟨969227, by rfl⟩ : syracuseStep 1292303 = 1938455) B1938455
theorem B1939499 : Blo 1291964 1939499 := bstep (se 1 (by rfl) ⟨1454624, by rfl⟩ : syracuseStep 1939499 = 2909249) B2909249
theorem B18651181 : Blo 1291964 18651181 := bstep (se 3 (by rfl) ⟨3497096, by rfl⟩ : syracuseStep 18651181 = 6994193) B6994193
theorem B1292347 : Blo 1291964 1292347 := bstep (se 1 (by rfl) ⟨969260, by rfl⟩ : syracuseStep 1292347 = 1938521) B1938521
theorem B1939529 : Blo 1291964 1939529 := bstep (se 2 (by rfl) ⟨727323, by rfl⟩ : syracuseStep 1939529 = 1454647) B1454647
theorem B1292423 : Blo 1291964 1292423 := bstep (se 1 (by rfl) ⟨969317, by rfl⟩ : syracuseStep 1292423 = 1938635) B1938635
theorem B1292431 : Blo 1291964 1292431 := bstep (se 1 (by rfl) ⟨969323, by rfl⟩ : syracuseStep 1292431 = 1938647) B1938647
theorem B1292475 : Blo 1291964 1292475 := bstep (se 1 (by rfl) ⟨969356, by rfl⟩ : syracuseStep 1292475 = 1938713) B1938713
theorem B1939643 : Blo 1291964 1939643 := bstep (se 1 (by rfl) ⟨1454732, by rfl⟩ : syracuseStep 1939643 = 2909465) B2909465
theorem B1939703 : Blo 1291964 1939703 := bstep (se 1 (by rfl) ⟨1454777, by rfl⟩ : syracuseStep 1939703 = 2909555) B2909555
theorem B1292551 : Blo 1291964 1292551 := bstep (se 1 (by rfl) ⟨969413, by rfl⟩ : syracuseStep 1292551 = 1938827) B1938827
theorem B1636615 : Blo 1291964 1636615 := bstep (se 1 (by rfl) ⟨1227461, by rfl⟩ : syracuseStep 1636615 = 2454923) B2454923
theorem B1292559 : Blo 1291964 1292559 := bstep (se 1 (by rfl) ⟨969419, by rfl⟩ : syracuseStep 1292559 = 1938839) B1938839
theorem B1939727 : Blo 1291964 1939727 := bstep (se 1 (by rfl) ⟨1454795, by rfl⟩ : syracuseStep 1939727 = 2909591) B2909591
theorem B1939769 : Blo 1291964 1939769 := bstep (se 2 (by rfl) ⟨727413, by rfl⟩ : syracuseStep 1939769 = 1454827) B1454827
theorem B1292603 : Blo 1291964 1292603 := bstep (se 1 (by rfl) ⟨969452, by rfl⟩ : syracuseStep 1292603 = 1938905) B1938905
theorem B4364603 : Blo 1291964 4364603 := bstep (se 1 (by rfl) ⟨3273452, by rfl⟩ : syracuseStep 4364603 = 6546905) B6546905
theorem B1292679 : Blo 1291964 1292679 := bstep (se 1 (by rfl) ⟨969509, by rfl⟩ : syracuseStep 1292679 = 1939019) B1939019
theorem B1939847 : Blo 1291964 1939847 := bstep (se 1 (by rfl) ⟨1454885, by rfl⟩ : syracuseStep 1939847 = 2909771) B2909771
theorem B1292687 : Blo 1291964 1292687 := bstep (se 1 (by rfl) ⟨969515, by rfl⟩ : syracuseStep 1292687 = 1939031) B1939031
theorem B1939883 : Blo 1291964 1939883 := bstep (se 1 (by rfl) ⟨1454912, by rfl⟩ : syracuseStep 1939883 = 2909825) B2909825
theorem B9820601 : Blo 1291964 9820601 := bstep (se 2 (by rfl) ⟨3682725, by rfl⟩ : syracuseStep 9820601 = 7365451) B7365451
theorem B1292731 : Blo 1291964 1292731 := bstep (se 1 (by rfl) ⟨969548, by rfl⟩ : syracuseStep 1292731 = 1939097) B1939097
theorem B1939913 : Blo 1291964 1939913 := bstep (se 2 (by rfl) ⟨727467, by rfl⟩ : syracuseStep 1939913 = 1454935) B1454935
theorem B1292807 : Blo 1291964 1292807 := bstep (se 1 (by rfl) ⟨969605, by rfl⟩ : syracuseStep 1292807 = 1939211) B1939211
theorem B3275275 : Blo 1291964 3275275 := bstep (se 1 (by rfl) ⟨2456456, by rfl⟩ : syracuseStep 3275275 = 4912913) B4912913
theorem B1292815 : Blo 1291964 1292815 := bstep (se 1 (by rfl) ⟨969611, by rfl⟩ : syracuseStep 1292815 = 1939223) B1939223
theorem B1292859 : Blo 1291964 1292859 := bstep (se 1 (by rfl) ⟨969644, by rfl⟩ : syracuseStep 1292859 = 1939289) B1939289
theorem B1940027 : Blo 1291964 1940027 := bstep (se 1 (by rfl) ⟨1455020, by rfl⟩ : syracuseStep 1940027 = 2910041) B2910041
theorem B3496535 : Blo 1291964 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B1940087 : Blo 1291964 1940087 := bstep (se 1 (by rfl) ⟨1455065, by rfl⟩ : syracuseStep 1940087 = 2910131) B2910131
theorem B2456183 : Blo 1291964 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B1292935 : Blo 1291964 1292935 := bstep (se 1 (by rfl) ⟨969701, by rfl⟩ : syracuseStep 1292935 = 1939403) B1939403
theorem B1292943 : Blo 1291964 1292943 := bstep (se 1 (by rfl) ⟨969707, by rfl⟩ : syracuseStep 1292943 = 1939415) B1939415
theorem B1940111 : Blo 1291964 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B1940153 : Blo 1291964 1940153 := bstep (se 2 (by rfl) ⟨727557, by rfl⟩ : syracuseStep 1940153 = 1455115) B1455115
theorem B1292987 : Blo 1291964 1292987 := bstep (se 1 (by rfl) ⟨969740, by rfl⟩ : syracuseStep 1292987 = 1939481) B1939481
theorem B10484417 : Blo 1291964 10484417 := bstep (se 2 (by rfl) ⟨3931656, by rfl⟩ : syracuseStep 10484417 = 7863313) B7863313
theorem B5520109 : Blo 1291964 5520109 := bstep (se 3 (by rfl) ⟨1035020, by rfl⟩ : syracuseStep 5520109 = 2070041) B2070041
theorem B1637111 : Blo 1291964 1637111 := bstep (se 1 (by rfl) ⟨1227833, by rfl⟩ : syracuseStep 1637111 = 2455667) B2455667
theorem B1293063 : Blo 1291964 1293063 := bstep (se 1 (by rfl) ⟨969797, by rfl⟩ : syracuseStep 1293063 = 1939595) B1939595
theorem B1940231 : Blo 1291964 1940231 := bstep (se 1 (by rfl) ⟨1455173, by rfl⟩ : syracuseStep 1940231 = 2910347) B2910347
theorem B1293071 : Blo 1291964 1293071 := bstep (se 1 (by rfl) ⟨969803, by rfl⟩ : syracuseStep 1293071 = 1939607) B1939607
theorem B4143887 : Blo 1291964 4143887 := bstep (se 1 (by rfl) ⟨3107915, by rfl⟩ : syracuseStep 4143887 = 6215831) B6215831
theorem B2456335 : Blo 1291964 2456335 := bstep (se 1 (by rfl) ⟨1842251, by rfl⟩ : syracuseStep 2456335 = 3684503) B3684503
theorem B4365089 : Blo 1291964 4365089 := bstep (se 2 (by rfl) ⟨1636908, by rfl⟩ : syracuseStep 4365089 = 3273817) B3273817
theorem B1940267 : Blo 1291964 1940267 := bstep (se 1 (by rfl) ⟨1455200, by rfl⟩ : syracuseStep 1940267 = 2910401) B2910401
theorem B1293115 : Blo 1291964 1293115 := bstep (se 1 (by rfl) ⟨969836, by rfl⟩ : syracuseStep 1293115 = 1939673) B1939673
theorem B1940297 : Blo 1291964 1940297 := bstep (se 2 (by rfl) ⟨727611, by rfl⟩ : syracuseStep 1940297 = 1455223) B1455223
theorem B9812825 : Blo 1291964 9812825 := bstep (se 2 (by rfl) ⟨3679809, by rfl⟩ : syracuseStep 9812825 = 7359619) B7359619
theorem B11049817 : Blo 1291964 11049817 := bstep (se 2 (by rfl) ⟨4143681, by rfl⟩ : syracuseStep 11049817 = 8287363) B8287363
theorem B2906999 : Blo 1291964 2906999 := bstep (se 1 (by rfl) ⟨2180249, by rfl⟩ : syracuseStep 2906999 = 4360499) B4360499
theorem B1293191 : Blo 1291964 1293191 := bstep (se 1 (by rfl) ⟨969893, by rfl⟩ : syracuseStep 1293191 = 1939787) B1939787
theorem B1293199 : Blo 1291964 1293199 := bstep (se 1 (by rfl) ⟨969899, by rfl⟩ : syracuseStep 1293199 = 1939799) B1939799
theorem B1637263 : Blo 1291964 1637263 := bstep (se 1 (by rfl) ⟨1227947, by rfl⟩ : syracuseStep 1637263 = 2455895) B2455895
theorem B6544313 : Blo 1291964 6544313 := bstep (se 2 (by rfl) ⟨2454117, by rfl⟩ : syracuseStep 6544313 = 4908235) B4908235
theorem B1293243 : Blo 1291964 1293243 := bstep (se 1 (by rfl) ⟨969932, by rfl⟩ : syracuseStep 1293243 = 1939865) B1939865
theorem B1940411 : Blo 1291964 1940411 := bstep (se 1 (by rfl) ⟨1455308, by rfl⟩ : syracuseStep 1940411 = 2910617) B2910617
theorem B1940471 : Blo 1291964 1940471 := bstep (se 1 (by rfl) ⟨1455353, by rfl⟩ : syracuseStep 1940471 = 2910707) B2910707
theorem B1293319 : Blo 1291964 1293319 := bstep (se 1 (by rfl) ⟨969989, by rfl⟩ : syracuseStep 1293319 = 1939979) B1939979
theorem B1293327 : Blo 1291964 1293327 := bstep (se 1 (by rfl) ⟨969995, by rfl⟩ : syracuseStep 1293327 = 1939991) B1939991
theorem B1940495 : Blo 1291964 1940495 := bstep (se 1 (by rfl) ⟨1455371, by rfl⟩ : syracuseStep 1940495 = 2910743) B2910743
theorem B2907179 : Blo 1291964 2907179 := bstep (se 1 (by rfl) ⟨2180384, by rfl⟩ : syracuseStep 2907179 = 4360769) B4360769
theorem B2489387 : Blo 1291964 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B3497003 : Blo 1291964 3497003 := bstep (se 1 (by rfl) ⟨2622752, by rfl⟩ : syracuseStep 3497003 = 5245505) B5245505
theorem B1866809 : Blo 1291964 1866809 := bstep (se 2 (by rfl) ⟨700053, by rfl⟩ : syracuseStep 1866809 = 1400107) B1400107
theorem B1940537 : Blo 1291964 1940537 := bstep (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) B1455403
theorem B1293371 : Blo 1291964 1293371 := bstep (se 1 (by rfl) ⟨970028, by rfl⟩ : syracuseStep 1293371 = 1940057) B1940057
theorem B1637435 : Blo 1291964 1637435 := bstep (se 1 (by rfl) ⟨1228076, by rfl⟩ : syracuseStep 1637435 = 2456153) B2456153
theorem B15735869 : Blo 1291964 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B4144247 : Blo 1291964 4144247 := bstep (se 1 (by rfl) ⟨3108185, by rfl⟩ : syracuseStep 4144247 = 6216371) B6216371
theorem B1293447 : Blo 1291964 1293447 := bstep (se 1 (by rfl) ⟨970085, by rfl⟩ : syracuseStep 1293447 = 1940171) B1940171
theorem B1940615 : Blo 1291964 1940615 := bstep (se 1 (by rfl) ⟨1455461, by rfl⟩ : syracuseStep 1940615 = 2910923) B2910923
theorem B1293455 : Blo 1291964 1293455 := bstep (se 1 (by rfl) ⟨970091, by rfl⟩ : syracuseStep 1293455 = 1940183) B1940183
theorem B1940651 : Blo 1291964 1940651 := bstep (se 1 (by rfl) ⟨1455488, by rfl⟩ : syracuseStep 1940651 = 2910977) B2910977
theorem B1293499 : Blo 1291964 1293499 := bstep (se 1 (by rfl) ⟨970124, by rfl⟩ : syracuseStep 1293499 = 1940249) B1940249
theorem B1940681 : Blo 1291964 1940681 := bstep (se 2 (by rfl) ⟨727755, by rfl⟩ : syracuseStep 1940681 = 1455511) B1455511
theorem B1293575 : Blo 1291964 1293575 := bstep (se 1 (by rfl) ⟨970181, by rfl⟩ : syracuseStep 1293575 = 1940363) B1940363
theorem B1293583 : Blo 1291964 1293583 := bstep (se 1 (by rfl) ⟨970187, by rfl⟩ : syracuseStep 1293583 = 1940375) B1940375
theorem B1596731 : Blo 1291964 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B1293627 : Blo 1291964 1293627 := bstep (se 1 (by rfl) ⟨970220, by rfl⟩ : syracuseStep 1293627 = 1940441) B1940441
theorem B1940795 : Blo 1291964 1940795 := bstep (se 1 (by rfl) ⟨1455596, by rfl⟩ : syracuseStep 1940795 = 2911193) B2911193
theorem B4365683 : Blo 1291964 4365683 := bstep (se 1 (by rfl) ⟨3274262, by rfl⟩ : syracuseStep 4365683 = 6548525) B6548525
theorem B1940855 : Blo 1291964 1940855 := bstep (se 1 (by rfl) ⟨1455641, by rfl⟩ : syracuseStep 1940855 = 2911283) B2911283
theorem B1293703 : Blo 1291964 1293703 := bstep (se 1 (by rfl) ⟨970277, by rfl⟩ : syracuseStep 1293703 = 1940555) B1940555
theorem B1293711 : Blo 1291964 1293711 := bstep (se 1 (by rfl) ⟨970283, by rfl⟩ : syracuseStep 1293711 = 1940567) B1940567
theorem B1940879 : Blo 1291964 1940879 := bstep (se 1 (by rfl) ⟨1455659, by rfl⟩ : syracuseStep 1940879 = 2911319) B2911319
theorem B2907539 : Blo 1291964 2907539 := bstep (se 1 (by rfl) ⟨2180654, by rfl⟩ : syracuseStep 2907539 = 4361309) B4361309
theorem B7462297 : Blo 1291964 7462297 := bstep (se 2 (by rfl) ⟨2798361, by rfl⟩ : syracuseStep 7462297 = 5596723) B5596723
theorem B7363993 : Blo 1291964 7363993 := bstep (se 2 (by rfl) ⟨2761497, by rfl⟩ : syracuseStep 7363993 = 5522995) B5522995
theorem B1940921 : Blo 1291964 1940921 := bstep (se 2 (by rfl) ⟨727845, by rfl⟩ : syracuseStep 1940921 = 1455691) B1455691
theorem B1293755 : Blo 1291964 1293755 := bstep (se 1 (by rfl) ⟨970316, by rfl⟩ : syracuseStep 1293755 = 1940633) B1940633
theorem B2907593 : Blo 1291964 2907593 := bstep (se 2 (by rfl) ⟨1090347, by rfl⟩ : syracuseStep 2907593 = 2180695) B2180695
theorem B1293831 : Blo 1291964 1293831 := bstep (se 1 (by rfl) ⟨970373, by rfl⟩ : syracuseStep 1293831 = 1940747) B1940747
theorem B1293839 : Blo 1291964 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B1293883 : Blo 1291964 1293883 := bstep (se 1 (by rfl) ⟨970412, by rfl⟩ : syracuseStep 1293883 = 1940825) B1940825
theorem B1293959 : Blo 1291964 1293959 := bstep (se 1 (by rfl) ⟨970469, by rfl⟩ : syracuseStep 1293959 = 1940939) B1940939
theorem B3317449 : Blo 1291964 3317449 := bstep (se 2 (by rfl) ⟨1244043, by rfl⟩ : syracuseStep 3317449 = 2488087) B2488087
theorem B6217505 : Blo 1291964 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B9813797 : Blo 1291964 9813797 := bstep (se 4 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 9813797 = 1840087) B1840087
theorem B6217523 : Blo 1291964 6217523 := bstep (se 1 (by rfl) ⟨4663142, by rfl⟩ : syracuseStep 6217523 = 9326285) B9326285
theorem B1474363 : Blo 1291964 1474363 := bstep (se 1 (by rfl) ⟨1105772, by rfl⟩ : syracuseStep 1474363 = 2211545) B2211545
theorem B19152925 : Blo 1291964 19152925 := bstep (se 3 (by rfl) ⟨3591173, by rfl⟩ : syracuseStep 19152925 = 7182347) B7182347
theorem B15728717 : Blo 1291964 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B4366493 : Blo 1291964 4366493 := bstep (se 3 (by rfl) ⟨818717, by rfl⟩ : syracuseStep 4366493 = 1637435) B1637435
theorem B2908331 : Blo 1291964 2908331 := bstep (se 1 (by rfl) ⟨2181248, by rfl⟩ : syracuseStep 2908331 = 4362497) B4362497
theorem B2760875 : Blo 1291964 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B9814283 : Blo 1291964 9814283 := bstep (se 1 (by rfl) ⟨7360712, by rfl⟩ : syracuseStep 9814283 = 14721425) B14721425
theorem B53051723 : Blo 1291964 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B7364951 : Blo 1291964 7364951 := bstep (se 1 (by rfl) ⟨5523713, by rfl⟩ : syracuseStep 7364951 = 11047427) B11047427
theorem B1311071 : Blo 1291964 1311071 := bstep (se 1 (by rfl) ⟨983303, by rfl⟩ : syracuseStep 1311071 = 1966607) B1966607
theorem B9945449 : Blo 1291964 9945449 := bstep (se 2 (by rfl) ⟨3729543, by rfl⟩ : syracuseStep 9945449 = 7459087) B7459087
theorem B4367033 : Blo 1291964 4367033 := bstep (se 2 (by rfl) ⟨1637637, by rfl⟩ : syracuseStep 4367033 = 3275275) B3275275
theorem B2908871 : Blo 1291964 2908871 := bstep (se 1 (by rfl) ⟨2181653, by rfl⟩ : syracuseStep 2908871 = 4363307) B4363307
theorem B4907735 : Blo 1291964 4907735 := bstep (se 1 (by rfl) ⟨3680801, by rfl⟩ : syracuseStep 4907735 = 7361603) B7361603
theorem B4424705 : Blo 1291964 4424705 := bstep (se 2 (by rfl) ⟨1659264, by rfl⟩ : syracuseStep 4424705 = 3318529) B3318529
theorem B4482127 : Blo 1291964 4482127 := bstep (se 1 (by rfl) ⟨3361595, by rfl⟩ : syracuseStep 4482127 = 6723191) B6723191
theorem B33146171 : Blo 1291964 33146171 := bstep (se 1 (by rfl) ⟨24859628, by rfl⟩ : syracuseStep 33146171 = 49719257) B49719257
theorem B2180425 : Blo 1291964 2180425 := bstep (se 2 (by rfl) ⟨817659, by rfl⟩ : syracuseStep 2180425 = 1635319) B1635319
theorem B2180459 : Blo 1291964 2180459 := bstep (se 1 (by rfl) ⟨1635344, by rfl⟩ : syracuseStep 2180459 = 3270689) B3270689
theorem B6210989 : Blo 1291964 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B16565705 : Blo 1291964 16565705 := bstep (se 2 (by rfl) ⟨6212139, by rfl⟩ : syracuseStep 16565705 = 12424279) B12424279
theorem B2909735 : Blo 1291964 2909735 := bstep (se 1 (by rfl) ⟨2182301, by rfl⟩ : syracuseStep 2909735 = 4364603) B4364603
theorem B19908193 : Blo 1291964 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B6547067 : Blo 1291964 6547067 := bstep (se 1 (by rfl) ⟨4910300, by rfl⟩ : syracuseStep 6547067 = 9820601) B9820601
theorem B6211217 : Blo 1291964 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B59754131 : Blo 1291964 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B9815741 : Blo 1291964 9815741 := bstep (se 3 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 9815741 = 3680903) B3680903
theorem B2180857 : Blo 1291964 2180857 := bstep (se 2 (by rfl) ⟨817821, by rfl⟩ : syracuseStep 2180857 = 1635643) B1635643
theorem B6989611 : Blo 1291964 6989611 := bstep (se 1 (by rfl) ⟨5242208, by rfl⟩ : syracuseStep 6989611 = 10484417) B10484417
theorem B2762591 : Blo 1291964 2762591 := bstep (se 1 (by rfl) ⟨2071943, by rfl⟩ : syracuseStep 2762591 = 4143887) B4143887
theorem B2910059 : Blo 1291964 2910059 := bstep (se 1 (by rfl) ⟨2182544, by rfl⟩ : syracuseStep 2910059 = 4365089) B4365089
theorem B2910113 : Blo 1291964 2910113 := bstep (se 2 (by rfl) ⟨1091292, by rfl⟩ : syracuseStep 2910113 = 2182585) B2182585
theorem B4483073 : Blo 1291964 4483073 := bstep (se 2 (by rfl) ⟨1681152, by rfl⟩ : syracuseStep 4483073 = 3362305) B3362305
theorem B2181127 : Blo 1291964 2181127 := bstep (se 1 (by rfl) ⟨1635845, by rfl⟩ : syracuseStep 2181127 = 3271691) B3271691
theorem B2762831 : Blo 1291964 2762831 := bstep (se 1 (by rfl) ⟨2072123, by rfl⟩ : syracuseStep 2762831 = 4144247) B4144247
theorem B9816227 : Blo 1291964 9816227 := bstep (se 1 (by rfl) ⟨7362170, by rfl⟩ : syracuseStep 9816227 = 14724341) B14724341
theorem B2910455 : Blo 1291964 2910455 := bstep (se 1 (by rfl) ⟨2182841, by rfl⟩ : syracuseStep 2910455 = 4365683) B4365683
theorem B8849675 : Blo 1291964 8849675 := bstep (se 1 (by rfl) ⟨6637256, by rfl⟩ : syracuseStep 8849675 = 13274513) B13274513
theorem B4360553 : Blo 1291964 4360553 := bstep (se 2 (by rfl) ⟨1635207, by rfl⟩ : syracuseStep 4360553 = 3270415) B3270415
theorem B2181559 : Blo 1291964 2181559 := bstep (se 1 (by rfl) ⟨1636169, by rfl⟩ : syracuseStep 2181559 = 3272339) B3272339
theorem B2181755 : Blo 1291964 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B3271367 : Blo 1291964 3271367 := bstep (se 1 (by rfl) ⟨2453525, by rfl⟩ : syracuseStep 3271367 = 4907051) B4907051
theorem B6638365 : Blo 1291964 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B2911049 : Blo 1291964 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B4426591 : Blo 1291964 4426591 := bstep (se 1 (by rfl) ⟨3319943, by rfl⟩ : syracuseStep 4426591 = 6639887) B6639887
theorem B4361147 : Blo 1291964 4361147 := bstep (se 1 (by rfl) ⟨3270860, by rfl⟩ : syracuseStep 4361147 = 6541721) B6541721
theorem B2182153 : Blo 1291964 2182153 := bstep (se 2 (by rfl) ⟨818307, by rfl⟩ : syracuseStep 2182153 = 1636615) B1636615
theorem B5524499 : Blo 1291964 5524499 := bstep (se 1 (by rfl) ⟨4143374, by rfl⟩ : syracuseStep 5524499 = 8286749) B8286749
theorem B3681359 : Blo 1291964 3681359 := bstep (se 1 (by rfl) ⟨2761019, by rfl⟩ : syracuseStep 3681359 = 5522039) B5522039
theorem B2182315 : Blo 1291964 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B11201935 : Blo 1291964 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B1453531 : Blo 1291964 1453531 := bstep (se 1 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 1453531 = 2180297) B2180297
theorem B2182619 : Blo 1291964 2182619 := bstep (se 1 (by rfl) ⟨1636964, by rfl⟩ : syracuseStep 2182619 = 3273929) B3273929
theorem B3108377 : Blo 1291964 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B4910651 : Blo 1291964 4910651 := bstep (se 1 (by rfl) ⟨3682988, by rfl⟩ : syracuseStep 4910651 = 7365977) B7365977
theorem B1379963 : Blo 1291964 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B7360145 : Blo 1291964 7360145 := bstep (se 2 (by rfl) ⟨2760054, by rfl⟩ : syracuseStep 7360145 = 5520109) B5520109
theorem B2182855 : Blo 1291964 2182855 := bstep (se 1 (by rfl) ⟨1637141, by rfl⟩ : syracuseStep 2182855 = 3274283) B3274283
theorem B6295261 : Blo 1291964 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B14733089 : Blo 1291964 14733089 := bstep (se 2 (by rfl) ⟨5524908, by rfl⟩ : syracuseStep 14733089 = 11049817) B11049817
theorem B2453321 : Blo 1291964 2453321 := bstep (se 2 (by rfl) ⟨919995, by rfl⟩ : syracuseStep 2453321 = 1839991) B1839991
theorem B3272521 : Blo 1291964 3272521 := bstep (se 2 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 3272521 = 2454391) B2454391
theorem B2183017 : Blo 1291964 2183017 := bstep (se 2 (by rfl) ⟨818631, by rfl⟩ : syracuseStep 2183017 = 1637263) B1637263
theorem B1453999 : Blo 1291964 1453999 := bstep (se 1 (by rfl) ⟨1090499, by rfl⟩ : syracuseStep 1453999 = 2180999) B2180999
theorem B7368641 : Blo 1291964 7368641 := bstep (se 2 (by rfl) ⟨2763240, by rfl⟩ : syracuseStep 7368641 = 5526481) B5526481
theorem B3682361 : Blo 1291964 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B159166579 : Blo 1291964 159166579 := bstep (se 1 (by rfl) ⟨119374934, by rfl⟩ : syracuseStep 159166579 = 238749869) B238749869
theorem B9318557 : Blo 1291964 9318557 := bstep (se 3 (by rfl) ⟨1747229, by rfl⟩ : syracuseStep 9318557 = 3494459) B3494459
theorem B2453753 : Blo 1291964 2453753 := bstep (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) B1840315
theorem B2330873 : Blo 1291964 2330873 := bstep (se 2 (by rfl) ⟨874077, by rfl⟩ : syracuseStep 2330873 = 1748155) B1748155
theorem B6549821 : Blo 1291964 6549821 := bstep (se 3 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 6549821 = 2456183) B2456183
theorem B1454431 : Blo 1291964 1454431 := bstep (se 1 (by rfl) ⟨1090823, by rfl⟩ : syracuseStep 1454431 = 2181647) B2181647
theorem B2331023 : Blo 1291964 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B67178969 : Blo 1291964 67178969 := bstep (se 2 (by rfl) ⟨25192113, by rfl⟩ : syracuseStep 67178969 = 50384227) B50384227
theorem B9949729 : Blo 1291964 9949729 := bstep (se 2 (by rfl) ⟨3731148, by rfl⟩ : syracuseStep 9949729 = 7462297) B7462297
theorem B9818657 : Blo 1291964 9818657 := bstep (se 2 (by rfl) ⟨3681996, by rfl⟩ : syracuseStep 9818657 = 7363993) B7363993
theorem B6541883 : Blo 1291964 6541883 := bstep (se 1 (by rfl) ⟨4906412, by rfl⟩ : syracuseStep 6541883 = 9812825) B9812825
theorem B1937999 : Blo 1291964 1937999 := bstep (se 1 (by rfl) ⟨1453499, by rfl⟩ : syracuseStep 1937999 = 2906999) B2906999
theorem B2486863 : Blo 1291964 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B4362875 : Blo 1291964 4362875 := bstep (se 1 (by rfl) ⟨3272156, by rfl⟩ : syracuseStep 4362875 = 6544313) B6544313
theorem B1938119 : Blo 1291964 1938119 := bstep (se 1 (by rfl) ⟨1453589, by rfl⟩ : syracuseStep 1938119 = 2907179) B2907179
theorem B1454791 : Blo 1291964 1454791 := bstep (se 1 (by rfl) ⟨1091093, by rfl⟩ : syracuseStep 1454791 = 2182187) B2182187
theorem B2331335 : Blo 1291964 2331335 := bstep (se 1 (by rfl) ⟨1748501, by rfl⟩ : syracuseStep 2331335 = 3497003) B3497003
theorem B3928787 : Blo 1291964 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B10490579 : Blo 1291964 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B4363037 : Blo 1291964 4363037 := bstep (se 3 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 4363037 = 1636139) B1636139
theorem B1635167 : Blo 1291964 1635167 := bstep (se 1 (by rfl) ⟨1226375, by rfl⟩ : syracuseStep 1635167 = 2452751) B2452751
theorem B1938281 : Blo 1291964 1938281 := bstep (se 2 (by rfl) ⟨726855, by rfl⟩ : syracuseStep 1938281 = 1453711) B1453711
theorem B1938359 : Blo 1291964 1938359 := bstep (se 1 (by rfl) ⟨1453769, by rfl⟩ : syracuseStep 1938359 = 2907539) B2907539
theorem B3273655 : Blo 1291964 3273655 := bstep (se 1 (by rfl) ⟨2455241, by rfl⟩ : syracuseStep 3273655 = 4910483) B4910483
theorem B1938395 : Blo 1291964 1938395 := bstep (se 1 (by rfl) ⟨1453796, by rfl⟩ : syracuseStep 1938395 = 2907593) B2907593
theorem B6542531 : Blo 1291964 6542531 := bstep (se 1 (by rfl) ⟨4906898, by rfl⟩ : syracuseStep 6542531 = 9813797) B9813797
theorem B7664843 : Blo 1291964 7664843 := bstep (se 1 (by rfl) ⟨5748632, by rfl⟩ : syracuseStep 7664843 = 11497265) B11497265
theorem B4142441 : Blo 1291964 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B24868241 : Blo 1291964 24868241 := bstep (se 2 (by rfl) ⟨9325590, by rfl⟩ : syracuseStep 24868241 = 18651181) B18651181
theorem B1938863 : Blo 1291964 1938863 := bstep (se 1 (by rfl) ⟨1454147, by rfl⟩ : syracuseStep 1938863 = 2908295) B2908295
theorem B5518793 : Blo 1291964 5518793 := bstep (se 2 (by rfl) ⟨2069547, by rfl⟩ : syracuseStep 5518793 = 4139095) B4139095
theorem B4363739 : Blo 1291964 4363739 := bstep (se 1 (by rfl) ⟨3272804, by rfl⟩ : syracuseStep 4363739 = 6545609) B6545609
theorem B4142555 : Blo 1291964 4142555 := bstep (se 1 (by rfl) ⟨3106916, by rfl⟩ : syracuseStep 4142555 = 6213833) B6213833
theorem B4978157 : Blo 1291964 4978157 := bstep (se 3 (by rfl) ⟨933404, by rfl⟩ : syracuseStep 4978157 = 1866809) B1866809
theorem B7362035 : Blo 1291964 7362035 := bstep (se 1 (by rfl) ⟨5521526, by rfl⟩ : syracuseStep 7362035 = 11043053) B11043053
theorem B1938953 : Blo 1291964 1938953 := bstep (se 2 (by rfl) ⟨727107, by rfl⟩ : syracuseStep 1938953 = 1454215) B1454215
theorem B1938983 : Blo 1291964 1938983 := bstep (se 1 (by rfl) ⟨1454237, by rfl⟩ : syracuseStep 1938983 = 2908475) B2908475
theorem B1455655 : Blo 1291964 1455655 := bstep (se 1 (by rfl) ⟨1091741, by rfl⟩ : syracuseStep 1455655 = 2183483) B2183483
theorem B2070073 : Blo 1291964 2070073 := bstep (se 2 (by rfl) ⟨776277, by rfl⟩ : syracuseStep 2070073 = 1552555) B1552555
theorem B1939067 : Blo 1291964 1939067 := bstep (se 1 (by rfl) ⟨1454300, by rfl⟩ : syracuseStep 1939067 = 2908601) B2908601
theorem B2455211 : Blo 1291964 2455211 := bstep (se 1 (by rfl) ⟨1841408, by rfl⟩ : syracuseStep 2455211 = 3682817) B3682817
theorem B1291975 : Blo 1291964 1291975 := bstep (se 1 (by rfl) ⟨968981, by rfl⟩ : syracuseStep 1291975 = 1937963) B1937963
theorem B6985415 : Blo 1291964 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B1291995 : Blo 1291964 1291995 := bstep (se 1 (by rfl) ⟨968996, by rfl⟩ : syracuseStep 1291995 = 1937993) B1937993
theorem B1939193 : Blo 1291964 1939193 := bstep (se 2 (by rfl) ⟨727197, by rfl⟩ : syracuseStep 1939193 = 1454395) B1454395
theorem B1292071 : Blo 1291964 1292071 := bstep (se 1 (by rfl) ⟨969053, by rfl⟩ : syracuseStep 1292071 = 1938107) B1938107
theorem B1292111 : Blo 1291964 1292111 := bstep (se 1 (by rfl) ⟨969083, by rfl⟩ : syracuseStep 1292111 = 1938167) B1938167
theorem B1292127 : Blo 1291964 1292127 := bstep (se 1 (by rfl) ⟨969095, by rfl⟩ : syracuseStep 1292127 = 1938191) B1938191
theorem B16562015 : Blo 1291964 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B1939295 : Blo 1291964 1939295 := bstep (se 1 (by rfl) ⟨1454471, by rfl⟩ : syracuseStep 1939295 = 2908943) B2908943
theorem B1939307 : Blo 1291964 1939307 := bstep (se 1 (by rfl) ⟨1454480, by rfl⟩ : syracuseStep 1939307 = 2908961) B2908961
theorem B1292155 : Blo 1291964 1292155 := bstep (se 1 (by rfl) ⟨969116, by rfl⟩ : syracuseStep 1292155 = 1938233) B1938233
theorem B1292207 : Blo 1291964 1292207 := bstep (se 1 (by rfl) ⟨969155, by rfl⟩ : syracuseStep 1292207 = 1938311) B1938311
theorem B1292231 : Blo 1291964 1292231 := bstep (se 1 (by rfl) ⟨969173, by rfl⟩ : syracuseStep 1292231 = 1938347) B1938347
theorem B1292251 : Blo 1291964 1292251 := bstep (se 1 (by rfl) ⟨969188, by rfl⟩ : syracuseStep 1292251 = 1938377) B1938377
theorem B1292327 : Blo 1291964 1292327 := bstep (se 1 (by rfl) ⟨969245, by rfl⟩ : syracuseStep 1292327 = 1938491) B1938491
theorem B2455591 : Blo 1291964 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B1292367 : Blo 1291964 1292367 := bstep (se 1 (by rfl) ⟨969275, by rfl⟩ : syracuseStep 1292367 = 1938551) B1938551
theorem B1939535 : Blo 1291964 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B5519441 : Blo 1291964 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B14727257 : Blo 1291964 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B1292383 : Blo 1291964 1292383 := bstep (se 1 (by rfl) ⟨969287, by rfl⟩ : syracuseStep 1292383 = 1938575) B1938575
theorem B1292411 : Blo 1291964 1292411 := bstep (se 1 (by rfl) ⟨969308, by rfl⟩ : syracuseStep 1292411 = 1938617) B1938617
theorem B4364441 : Blo 1291964 4364441 := bstep (se 2 (by rfl) ⟨1636665, by rfl⟩ : syracuseStep 4364441 = 3273331) B3273331
theorem B4257949 : Blo 1291964 4257949 := bstep (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) B1596731
theorem B1292463 : Blo 1291964 1292463 := bstep (se 1 (by rfl) ⟨969347, by rfl⟩ : syracuseStep 1292463 = 1938695) B1938695
theorem B1292487 : Blo 1291964 1292487 := bstep (se 1 (by rfl) ⟨969365, by rfl⟩ : syracuseStep 1292487 = 1938731) B1938731
theorem B1939655 : Blo 1291964 1939655 := bstep (se 1 (by rfl) ⟨1454741, by rfl⟩ : syracuseStep 1939655 = 2909483) B2909483
theorem B2455751 : Blo 1291964 2455751 := bstep (se 1 (by rfl) ⟨1841813, by rfl⟩ : syracuseStep 2455751 = 3683627) B3683627
theorem B1292507 : Blo 1291964 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B3545335 : Blo 1291964 3545335 := bstep (se 1 (by rfl) ⟨2659001, by rfl⟩ : syracuseStep 3545335 = 5318003) B5318003
theorem B1292583 : Blo 1291964 1292583 := bstep (se 1 (by rfl) ⟨969437, by rfl⟩ : syracuseStep 1292583 = 1938875) B1938875
theorem B1292623 : Blo 1291964 1292623 := bstep (se 1 (by rfl) ⟨969467, by rfl⟩ : syracuseStep 1292623 = 1938935) B1938935
theorem B1292639 : Blo 1291964 1292639 := bstep (se 1 (by rfl) ⟨969479, by rfl⟩ : syracuseStep 1292639 = 1938959) B1938959
theorem B1939817 : Blo 1291964 1939817 := bstep (se 2 (by rfl) ⟨727431, by rfl⟩ : syracuseStep 1939817 = 1454863) B1454863
theorem B3275113 : Blo 1291964 3275113 := bstep (se 2 (by rfl) ⟨1228167, by rfl⟩ : syracuseStep 3275113 = 2456335) B2456335
theorem B1292667 : Blo 1291964 1292667 := bstep (se 1 (by rfl) ⟨969500, by rfl⟩ : syracuseStep 1292667 = 1939001) B1939001
theorem B1292719 : Blo 1291964 1292719 := bstep (se 1 (by rfl) ⟨969539, by rfl⟩ : syracuseStep 1292719 = 1939079) B1939079
theorem B1939895 : Blo 1291964 1939895 := bstep (se 1 (by rfl) ⟨1454921, by rfl⟩ : syracuseStep 1939895 = 2909843) B2909843
theorem B1292743 : Blo 1291964 1292743 := bstep (se 1 (by rfl) ⟨969557, by rfl⟩ : syracuseStep 1292743 = 1939115) B1939115
theorem B1292763 : Blo 1291964 1292763 := bstep (se 1 (by rfl) ⟨969572, by rfl⟩ : syracuseStep 1292763 = 1939145) B1939145
theorem B1939931 : Blo 1291964 1939931 := bstep (se 1 (by rfl) ⟨1454948, by rfl⟩ : syracuseStep 1939931 = 2909897) B2909897
theorem B1292839 : Blo 1291964 1292839 := bstep (se 1 (by rfl) ⟨969629, by rfl⟩ : syracuseStep 1292839 = 1939259) B1939259
theorem B1292879 : Blo 1291964 1292879 := bstep (se 1 (by rfl) ⟨969659, by rfl⟩ : syracuseStep 1292879 = 1939319) B1939319
theorem B1292895 : Blo 1291964 1292895 := bstep (se 1 (by rfl) ⟨969671, by rfl⟩ : syracuseStep 1292895 = 1939343) B1939343
theorem B1292923 : Blo 1291964 1292923 := bstep (se 1 (by rfl) ⟨969692, by rfl⟩ : syracuseStep 1292923 = 1939385) B1939385
theorem B1292975 : Blo 1291964 1292975 := bstep (se 1 (by rfl) ⟨969731, by rfl⟩ : syracuseStep 1292975 = 1939463) B1939463
theorem B1292999 : Blo 1291964 1292999 := bstep (se 1 (by rfl) ⟨969749, by rfl⟩ : syracuseStep 1292999 = 1939499) B1939499
theorem B1293019 : Blo 1291964 1293019 := bstep (se 1 (by rfl) ⟨969764, by rfl⟩ : syracuseStep 1293019 = 1939529) B1939529
theorem B1293095 : Blo 1291964 1293095 := bstep (se 1 (by rfl) ⟨969821, by rfl⟩ : syracuseStep 1293095 = 1939643) B1939643
theorem B1293135 : Blo 1291964 1293135 := bstep (se 1 (by rfl) ⟨969851, by rfl⟩ : syracuseStep 1293135 = 1939703) B1939703
theorem B1293151 : Blo 1291964 1293151 := bstep (se 1 (by rfl) ⟨969863, by rfl⟩ : syracuseStep 1293151 = 1939727) B1939727
theorem B4660087 : Blo 1291964 4660087 := bstep (se 1 (by rfl) ⟨3495065, by rfl⟩ : syracuseStep 4660087 = 6990131) B6990131
theorem B1293179 : Blo 1291964 1293179 := bstep (se 1 (by rfl) ⟨969884, by rfl⟩ : syracuseStep 1293179 = 1939769) B1939769
theorem B1293231 : Blo 1291964 1293231 := bstep (se 1 (by rfl) ⟨969923, by rfl⟩ : syracuseStep 1293231 = 1939847) B1939847
theorem B1940399 : Blo 1291964 1940399 := bstep (se 1 (by rfl) ⟨1455299, by rfl⟩ : syracuseStep 1940399 = 2910599) B2910599
theorem B1293255 : Blo 1291964 1293255 := bstep (se 1 (by rfl) ⟨969941, by rfl⟩ : syracuseStep 1293255 = 1939883) B1939883
theorem B1293275 : Blo 1291964 1293275 := bstep (se 1 (by rfl) ⟨969956, by rfl⟩ : syracuseStep 1293275 = 1939913) B1939913
theorem B8281061 : Blo 1291964 8281061 := bstep (se 4 (by rfl) ⟨776349, by rfl⟩ : syracuseStep 8281061 = 1552699) B1552699
theorem B2907143 : Blo 1291964 2907143 := bstep (se 1 (by rfl) ⟨2180357, by rfl⟩ : syracuseStep 2907143 = 4360715) B4360715
theorem B2759687 : Blo 1291964 2759687 := bstep (se 1 (by rfl) ⟨2069765, by rfl⟩ : syracuseStep 2759687 = 4139531) B4139531
theorem B1940489 : Blo 1291964 1940489 := bstep (se 2 (by rfl) ⟨727683, by rfl⟩ : syracuseStep 1940489 = 1455367) B1455367
theorem B1293351 : Blo 1291964 1293351 := bstep (se 1 (by rfl) ⟨970013, by rfl⟩ : syracuseStep 1293351 = 1940027) B1940027
theorem B1940519 : Blo 1291964 1940519 := bstep (se 1 (by rfl) ⟨1455389, by rfl⟩ : syracuseStep 1940519 = 2910779) B2910779
theorem B2907215 : Blo 1291964 2907215 := bstep (se 1 (by rfl) ⟨2180411, by rfl⟩ : syracuseStep 2907215 = 4360823) B4360823
theorem B2071631 : Blo 1291964 2071631 := bstep (se 1 (by rfl) ⟨1553723, by rfl⟩ : syracuseStep 2071631 = 3107447) B3107447
theorem B1293391 : Blo 1291964 1293391 := bstep (se 1 (by rfl) ⟨970043, by rfl⟩ : syracuseStep 1293391 = 1940087) B1940087
theorem B1293407 : Blo 1291964 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B1293435 : Blo 1291964 1293435 := bstep (se 1 (by rfl) ⟨970076, by rfl⟩ : syracuseStep 1293435 = 1940153) B1940153
theorem B1940603 : Blo 1291964 1940603 := bstep (se 1 (by rfl) ⟨1455452, by rfl⟩ : syracuseStep 1940603 = 2910905) B2910905
theorem B1293487 : Blo 1291964 1293487 := bstep (se 1 (by rfl) ⟨970115, by rfl⟩ : syracuseStep 1293487 = 1940231) B1940231
theorem B1293511 : Blo 1291964 1293511 := bstep (se 1 (by rfl) ⟨970133, by rfl⟩ : syracuseStep 1293511 = 1940267) B1940267
theorem B6216907 : Blo 1291964 6216907 := bstep (se 1 (by rfl) ⟨4662680, by rfl⟩ : syracuseStep 6216907 = 9325361) B9325361
theorem B1293531 : Blo 1291964 1293531 := bstep (se 1 (by rfl) ⟨970148, by rfl⟩ : syracuseStep 1293531 = 1940297) B1940297
theorem B1940729 : Blo 1291964 1940729 := bstep (se 2 (by rfl) ⟨727773, by rfl⟩ : syracuseStep 1940729 = 1455547) B1455547
theorem B22093073 : Blo 1291964 22093073 := bstep (se 2 (by rfl) ⟨8284902, by rfl⟩ : syracuseStep 22093073 = 16569805) B16569805
theorem B1293607 : Blo 1291964 1293607 := bstep (se 1 (by rfl) ⟨970205, by rfl⟩ : syracuseStep 1293607 = 1940411) B1940411
theorem B4365629 : Blo 1291964 4365629 := bstep (se 3 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 4365629 = 1637111) B1637111
theorem B1293647 : Blo 1291964 1293647 := bstep (se 1 (by rfl) ⟨970235, by rfl⟩ : syracuseStep 1293647 = 1940471) B1940471
theorem B1293663 : Blo 1291964 1293663 := bstep (se 1 (by rfl) ⟨970247, by rfl⟩ : syracuseStep 1293663 = 1940495) B1940495
theorem B1940831 : Blo 1291964 1940831 := bstep (se 1 (by rfl) ⟨1455623, by rfl⟩ : syracuseStep 1940831 = 2911247) B2911247
theorem B1940843 : Blo 1291964 1940843 := bstep (se 1 (by rfl) ⟨1455632, by rfl⟩ : syracuseStep 1940843 = 2911265) B2911265
theorem B1293691 : Blo 1291964 1293691 := bstep (se 1 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 1293691 = 1940537) B1940537
theorem B1293743 : Blo 1291964 1293743 := bstep (se 1 (by rfl) ⟨970307, by rfl⟩ : syracuseStep 1293743 = 1940615) B1940615
theorem B1293767 : Blo 1291964 1293767 := bstep (se 1 (by rfl) ⟨970325, by rfl⟩ : syracuseStep 1293767 = 1940651) B1940651
theorem B2907611 : Blo 1291964 2907611 := bstep (se 1 (by rfl) ⟨2180708, by rfl⟩ : syracuseStep 2907611 = 4361417) B4361417
theorem B1293787 : Blo 1291964 1293787 := bstep (se 1 (by rfl) ⟨970340, by rfl⟩ : syracuseStep 1293787 = 1940681) B1940681
theorem B1293863 : Blo 1291964 1293863 := bstep (se 1 (by rfl) ⟨970397, by rfl⟩ : syracuseStep 1293863 = 1940795) B1940795
theorem B1293903 : Blo 1291964 1293903 := bstep (se 1 (by rfl) ⟨970427, by rfl⟩ : syracuseStep 1293903 = 1940855) B1940855
theorem B1293919 : Blo 1291964 1293919 := bstep (se 1 (by rfl) ⟨970439, by rfl⟩ : syracuseStep 1293919 = 1940879) B1940879
theorem B4423265 : Blo 1291964 4423265 := bstep (se 2 (by rfl) ⟨1658724, by rfl⟩ : syracuseStep 4423265 = 3317449) B3317449
theorem B1293947 : Blo 1291964 1293947 := bstep (se 1 (by rfl) ⟨970460, by rfl⟩ : syracuseStep 1293947 = 1940921) B1940921
theorem B10477277 : Blo 1291964 10477277 := bstep (se 3 (by rfl) ⟨1964489, by rfl⟩ : syracuseStep 10477277 = 3928979) B3928979
theorem B1965817 : Blo 1291964 1965817 := bstep (se 2 (by rfl) ⟨737181, by rfl⟩ : syracuseStep 1965817 = 1474363) B1474363
theorem B4145003 : Blo 1291964 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B12427127 : Blo 1291964 12427127 := bstep (se 1 (by rfl) ⟨9320345, by rfl⟩ : syracuseStep 12427127 = 18640691) B18640691
theorem B4145015 : Blo 1291964 4145015 := bstep (se 1 (by rfl) ⟨3108761, by rfl⟩ : syracuseStep 4145015 = 6217523) B6217523
theorem B2908079 : Blo 1291964 2908079 := bstep (se 1 (by rfl) ⟨2181059, by rfl⟩ : syracuseStep 2908079 = 4362119) B4362119
theorem B19898297 : Blo 1291964 19898297 := bstep (se 2 (by rfl) ⟨7461861, by rfl⟩ : syracuseStep 19898297 = 14923723) B14923723
theorem B2908169 : Blo 1291964 2908169 := bstep (se 2 (by rfl) ⟨1090563, by rfl⟩ : syracuseStep 2908169 = 2181127) B2181127
theorem B10485811 : Blo 1291964 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B212222105 : Blo 1291964 212222105 := bstep (se 2 (by rfl) ⟨79583289, by rfl⟩ : syracuseStep 212222105 = 159166579) B159166579
theorem B5677265 : Blo 1291964 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B4366547 : Blo 1291964 4366547 := bstep (se 1 (by rfl) ⟨3274910, by rfl⟩ : syracuseStep 4366547 = 6549821) B6549821
theorem B44785979 : Blo 1291964 44785979 := bstep (se 1 (by rfl) ⟨33589484, by rfl⟩ : syracuseStep 44785979 = 67178969) B67178969
theorem B6545771 : Blo 1291964 6545771 := bstep (se 1 (by rfl) ⟨4909328, by rfl⟩ : syracuseStep 6545771 = 9818657) B9818657
theorem B23904677 : Blo 1291964 23904677 := bstep (se 4 (by rfl) ⟨2241063, by rfl⟩ : syracuseStep 23904677 = 4482127) B4482127
theorem B2908583 : Blo 1291964 2908583 := bstep (se 1 (by rfl) ⟨2181437, by rfl⟩ : syracuseStep 2908583 = 4362875) B4362875
theorem B4366817 : Blo 1291964 4366817 := bstep (se 2 (by rfl) ⟨1637556, by rfl⟩ : syracuseStep 4366817 = 3275113) B3275113
theorem B2908691 : Blo 1291964 2908691 := bstep (se 1 (by rfl) ⟨2181518, by rfl⟩ : syracuseStep 2908691 = 4363037) B4363037
theorem B2908745 : Blo 1291964 2908745 := bstep (se 2 (by rfl) ⟨1090779, by rfl⟩ : syracuseStep 2908745 = 2181559) B2181559
theorem B2949803 : Blo 1291964 2949803 := bstep (se 1 (by rfl) ⟨2212352, by rfl⟩ : syracuseStep 2949803 = 4424705) B4424705
theorem B2761627 : Blo 1291964 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B3679195 : Blo 1291964 3679195 := bstep (se 1 (by rfl) ⟨2759396, by rfl⟩ : syracuseStep 3679195 = 5518793) B5518793
theorem B11043803 : Blo 1291964 11043803 := bstep (se 1 (by rfl) ⟨8282852, by rfl⟩ : syracuseStep 11043803 = 16565705) B16565705
theorem B2909159 : Blo 1291964 2909159 := bstep (se 1 (by rfl) ⟨2181869, by rfl⟩ : syracuseStep 2909159 = 4363739) B4363739
theorem B2761703 : Blo 1291964 2761703 := bstep (se 1 (by rfl) ⟨2071277, by rfl⟩ : syracuseStep 2761703 = 4142555) B4142555
theorem B13984757 : Blo 1291964 13984757 := bstep (se 5 (by rfl) ⟨655535, by rfl⟩ : syracuseStep 13984757 = 1311071) B1311071
theorem B4908023 : Blo 1291964 4908023 := bstep (se 1 (by rfl) ⟨3681017, by rfl⟩ : syracuseStep 4908023 = 7362035) B7362035
theorem B18908453 : Blo 1291964 18908453 := bstep (se 4 (by rfl) ⟨1772667, by rfl⟩ : syracuseStep 18908453 = 3545335) B3545335
theorem B2909537 : Blo 1291964 2909537 := bstep (se 2 (by rfl) ⟨1091076, by rfl⟩ : syracuseStep 2909537 = 2182153) B2182153
theorem B2909627 : Blo 1291964 2909627 := bstep (se 1 (by rfl) ⟨2182220, by rfl⟩ : syracuseStep 2909627 = 4364441) B4364441
theorem B24864245 : Blo 1291964 24864245 := bstep (se 5 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 24864245 = 2331023) B2331023
theorem B2909753 : Blo 1291964 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B3679901 : Blo 1291964 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B6547229 : Blo 1291964 6547229 := bstep (se 3 (by rfl) ⟨1227605, by rfl⟩ : syracuseStep 6547229 = 2455211) B2455211
theorem B2180911 : Blo 1291964 2180911 := bstep (se 1 (by rfl) ⟨1635683, by rfl⟩ : syracuseStep 2180911 = 3271367) B3271367
theorem B14935913 : Blo 1291964 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B26544257 : Blo 1291964 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B2910419 : Blo 1291964 2910419 := bstep (se 1 (by rfl) ⟨2182814, by rfl⟩ : syracuseStep 2910419 = 4365629) B4365629
theorem B4360445 : Blo 1291964 4360445 := bstep (se 3 (by rfl) ⟨817583, by rfl⟩ : syracuseStep 4360445 = 1635167) B1635167
theorem B7366909 : Blo 1291964 7366909 := bstep (se 3 (by rfl) ⟨1381295, by rfl⟩ : syracuseStep 7366909 = 2762591) B2762591
theorem B2910473 : Blo 1291964 2910473 := bstep (se 2 (by rfl) ⟨1091427, by rfl⟩ : syracuseStep 2910473 = 2182855) B2182855
theorem B2910689 : Blo 1291964 2910689 := bstep (se 2 (by rfl) ⟨1091508, by rfl⟩ : syracuseStep 2910689 = 2183017) B2183017
theorem B2763335 : Blo 1291964 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B8284751 : Blo 1291964 8284751 := bstep (se 1 (by rfl) ⟨6213563, by rfl⟩ : syracuseStep 8284751 = 12427127) B12427127
theorem B2763343 : Blo 1291964 2763343 := bstep (se 1 (by rfl) ⟨2072507, by rfl⟩ : syracuseStep 2763343 = 4145015) B4145015
theorem B13265531 : Blo 1291964 13265531 := bstep (se 1 (by rfl) ⟨9949148, by rfl⟩ : syracuseStep 13265531 = 19898297) B19898297
theorem B11954861 : Blo 1291964 11954861 := bstep (se 3 (by rfl) ⟨2241536, by rfl⟩ : syracuseStep 11954861 = 4483073) B4483073
theorem B6212371 : Blo 1291964 6212371 := bstep (se 1 (by rfl) ⟨4659278, by rfl⟩ : syracuseStep 6212371 = 9318557) B9318557
theorem B2910995 : Blo 1291964 2910995 := bstep (se 1 (by rfl) ⟨2183246, by rfl⟩ : syracuseStep 2910995 = 4366493) B4366493
theorem B102148933 : Blo 1291964 102148933 := bstep (se 4 (by rfl) ⟨9576462, by rfl⟩ : syracuseStep 102148933 = 19152925) B19152925
theorem B35367815 : Blo 1291964 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B4909967 : Blo 1291964 4909967 := bstep (se 1 (by rfl) ⟨3682475, by rfl⟩ : syracuseStep 4909967 = 7364951) B7364951
theorem B6630299 : Blo 1291964 6630299 := bstep (se 1 (by rfl) ⟨4972724, by rfl⟩ : syracuseStep 6630299 = 9945449) B9945449
theorem B4361255 : Blo 1291964 4361255 := bstep (se 1 (by rfl) ⟨3270941, by rfl⟩ : syracuseStep 4361255 = 6541883) B6541883
theorem B2911355 : Blo 1291964 2911355 := bstep (se 1 (by rfl) ⟨2183516, by rfl⟩ : syracuseStep 2911355 = 4367033) B4367033
theorem B3271823 : Blo 1291964 3271823 := bstep (se 1 (by rfl) ⟨2453867, by rfl⟩ : syracuseStep 3271823 = 4907735) B4907735
theorem B13266305 : Blo 1291964 13266305 := bstep (se 2 (by rfl) ⟨4974864, by rfl⟩ : syracuseStep 13266305 = 9949729) B9949729
theorem B4361687 : Blo 1291964 4361687 := bstep (se 1 (by rfl) ⟨3271265, by rfl⟩ : syracuseStep 4361687 = 6542531) B6542531
theorem B22097447 : Blo 1291964 22097447 := bstep (se 1 (by rfl) ⟨16573085, by rfl⟩ : syracuseStep 22097447 = 33146171) B33146171
theorem B1453639 : Blo 1291964 1453639 := bstep (se 1 (by rfl) ⟨1090229, by rfl⟩ : syracuseStep 1453639 = 2180459) B2180459
theorem B4140659 : Blo 1291964 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B4140811 : Blo 1291964 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B5902121 : Blo 1291964 5902121 := bstep (se 2 (by rfl) ⟨2213295, by rfl⟩ : syracuseStep 5902121 = 4426591) B4426591
theorem B4656943 : Blo 1291964 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B6213449 : Blo 1291964 6213449 := bstep (se 2 (by rfl) ⟨2330043, by rfl⟩ : syracuseStep 6213449 = 4660087) B4660087
theorem B13275085 : Blo 1291964 13275085 := bstep (se 3 (by rfl) ⟨2489078, by rfl⟩ : syracuseStep 13275085 = 4978157) B4978157
theorem B9818171 : Blo 1291964 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B1454503 : Blo 1291964 1454503 := bstep (se 1 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 1454503 = 2181755) B2181755
theorem B1938041 : Blo 1291964 1938041 := bstep (se 2 (by rfl) ⟨726765, by rfl⟩ : syracuseStep 1938041 = 1453531) B1453531
theorem B1938095 : Blo 1291964 1938095 := bstep (se 1 (by rfl) ⟨1453571, by rfl⟩ : syracuseStep 1938095 = 2907143) B2907143
theorem B1839791 : Blo 1291964 1839791 := bstep (se 1 (by rfl) ⟨1379843, by rfl⟩ : syracuseStep 1839791 = 2759687) B2759687
theorem B3682999 : Blo 1291964 3682999 := bstep (se 1 (by rfl) ⟨2762249, by rfl⟩ : syracuseStep 3682999 = 5524499) B5524499
theorem B1938143 : Blo 1291964 1938143 := bstep (se 1 (by rfl) ⟨1453607, by rfl⟩ : syracuseStep 1938143 = 2907215) B2907215
theorem B2454239 : Blo 1291964 2454239 := bstep (se 1 (by rfl) ⟨1840679, by rfl⟩ : syracuseStep 2454239 = 3681359) B3681359
theorem B1381087 : Blo 1291964 1381087 := bstep (se 1 (by rfl) ⟨1035815, by rfl⟩ : syracuseStep 1381087 = 2071631) B2071631
theorem B8393681 : Blo 1291964 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B1938407 : Blo 1291964 1938407 := bstep (se 1 (by rfl) ⟨1453805, by rfl⟩ : syracuseStep 1938407 = 2907611) B2907611
theorem B1455079 : Blo 1291964 1455079 := bstep (se 1 (by rfl) ⟨1091309, by rfl⟩ : syracuseStep 1455079 = 2182619) B2182619
theorem B3273767 : Blo 1291964 3273767 := bstep (se 1 (by rfl) ⟨2455325, by rfl⟩ : syracuseStep 3273767 = 4910651) B4910651
theorem B9319481 : Blo 1291964 9319481 := bstep (se 2 (by rfl) ⟨3494805, by rfl⟩ : syracuseStep 9319481 = 6989611) B6989611
theorem B4363361 : Blo 1291964 4363361 := bstep (se 2 (by rfl) ⟨1636260, by rfl⟩ : syracuseStep 4363361 = 3272521) B3272521
theorem B6984851 : Blo 1291964 6984851 := bstep (se 1 (by rfl) ⟨5238638, by rfl⟩ : syracuseStep 6984851 = 10477277) B10477277
theorem B1635547 : Blo 1291964 1635547 := bstep (se 1 (by rfl) ⟨1226660, by rfl⟩ : syracuseStep 1635547 = 2453321) B2453321
theorem B1938665 : Blo 1291964 1938665 := bstep (se 2 (by rfl) ⟨726999, by rfl⟩ : syracuseStep 1938665 = 1453999) B1453999
theorem B1938719 : Blo 1291964 1938719 := bstep (se 1 (by rfl) ⟨1454039, by rfl⟩ : syracuseStep 1938719 = 2908079) B2908079
theorem B4912427 : Blo 1291964 4912427 := bstep (se 1 (by rfl) ⟨3684320, by rfl⟩ : syracuseStep 4912427 = 7368641) B7368641
theorem B3274121 : Blo 1291964 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B1938887 : Blo 1291964 1938887 := bstep (se 1 (by rfl) ⟨1454165, by rfl⟩ : syracuseStep 1938887 = 2908331) B2908331
theorem B1840583 : Blo 1291964 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B9819629 : Blo 1291964 9819629 := bstep (se 3 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 9819629 = 3682361) B3682361
theorem B1553915 : Blo 1291964 1553915 := bstep (se 1 (by rfl) ⟨1165436, by rfl⟩ : syracuseStep 1553915 = 2330873) B2330873
theorem B6542855 : Blo 1291964 6542855 := bstep (se 1 (by rfl) ⟨4907141, by rfl⟩ : syracuseStep 6542855 = 9814283) B9814283
theorem B14718509 : Blo 1291964 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B1291999 : Blo 1291964 1291999 := bstep (se 1 (by rfl) ⟨968999, by rfl⟩ : syracuseStep 1291999 = 1937999) B1937999
theorem B1939241 : Blo 1291964 1939241 := bstep (se 2 (by rfl) ⟨727215, by rfl⟩ : syracuseStep 1939241 = 1454431) B1454431
theorem B1292079 : Blo 1291964 1292079 := bstep (se 1 (by rfl) ⟨969059, by rfl⟩ : syracuseStep 1292079 = 1938119) B1938119
theorem B1939247 : Blo 1291964 1939247 := bstep (se 1 (by rfl) ⟨1454435, by rfl⟩ : syracuseStep 1939247 = 2908871) B2908871
theorem B1554223 : Blo 1291964 1554223 := bstep (se 1 (by rfl) ⟨1165667, by rfl⟩ : syracuseStep 1554223 = 2331335) B2331335
theorem B2619191 : Blo 1291964 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B6993719 : Blo 1291964 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B1292187 : Blo 1291964 1292187 := bstep (se 1 (by rfl) ⟨969140, by rfl⟩ : syracuseStep 1292187 = 1938281) B1938281
theorem B1292239 : Blo 1291964 1292239 := bstep (se 1 (by rfl) ⟨969179, by rfl⟩ : syracuseStep 1292239 = 1938359) B1938359
theorem B1292263 : Blo 1291964 1292263 := bstep (se 1 (by rfl) ⟨969197, by rfl⟩ : syracuseStep 1292263 = 1938395) B1938395
theorem B6543341 : Blo 1291964 6543341 := bstep (se 3 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 6543341 = 2453753) B2453753
theorem B23599133 : Blo 1291964 23599133 := bstep (se 3 (by rfl) ⟨4424837, by rfl⟩ : syracuseStep 23599133 = 8849675) B8849675
theorem B3315817 : Blo 1291964 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B5109895 : Blo 1291964 5109895 := bstep (se 1 (by rfl) ⟨3832421, by rfl⟩ : syracuseStep 5109895 = 7664843) B7664843
theorem B1939721 : Blo 1291964 1939721 := bstep (se 2 (by rfl) ⟨727395, by rfl⟩ : syracuseStep 1939721 = 1454791) B1454791
theorem B16578827 : Blo 1291964 16578827 := bstep (se 1 (by rfl) ⟨12434120, by rfl⟩ : syracuseStep 16578827 = 24868241) B24868241
theorem B1292575 : Blo 1291964 1292575 := bstep (se 1 (by rfl) ⟨969431, by rfl⟩ : syracuseStep 1292575 = 1938863) B1938863
theorem B1292635 : Blo 1291964 1292635 := bstep (se 1 (by rfl) ⟨969476, by rfl⟩ : syracuseStep 1292635 = 1938953) B1938953
theorem B1292655 : Blo 1291964 1292655 := bstep (se 1 (by rfl) ⟨969491, by rfl⟩ : syracuseStep 1292655 = 1938983) B1938983
theorem B1939823 : Blo 1291964 1939823 := bstep (se 1 (by rfl) ⟨1454867, by rfl⟩ : syracuseStep 1939823 = 2909735) B2909735
theorem B1292711 : Blo 1291964 1292711 := bstep (se 1 (by rfl) ⟨969533, by rfl⟩ : syracuseStep 1292711 = 1939067) B1939067
theorem B4364711 : Blo 1291964 4364711 := bstep (se 1 (by rfl) ⟨3273533, by rfl⟩ : syracuseStep 4364711 = 6547067) B6547067
theorem B39836087 : Blo 1291964 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B6543827 : Blo 1291964 6543827 := bstep (se 1 (by rfl) ⟨4907870, by rfl⟩ : syracuseStep 6543827 = 9815741) B9815741
theorem B1292795 : Blo 1291964 1292795 := bstep (se 1 (by rfl) ⟨969596, by rfl⟩ : syracuseStep 1292795 = 1939193) B1939193
theorem B11041343 : Blo 1291964 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B1292863 : Blo 1291964 1292863 := bstep (se 1 (by rfl) ⟨969647, by rfl⟩ : syracuseStep 1292863 = 1939295) B1939295
theorem B1292871 : Blo 1291964 1292871 := bstep (se 1 (by rfl) ⟨969653, by rfl⟩ : syracuseStep 1292871 = 1939307) B1939307
theorem B1940039 : Blo 1291964 1940039 := bstep (se 1 (by rfl) ⟨1455029, by rfl⟩ : syracuseStep 1940039 = 2910059) B2910059
theorem B4364873 : Blo 1291964 4364873 := bstep (se 2 (by rfl) ⟨1636827, by rfl⟩ : syracuseStep 4364873 = 3273655) B3273655
theorem B1940075 : Blo 1291964 1940075 := bstep (se 1 (by rfl) ⟨1455056, by rfl⟩ : syracuseStep 1940075 = 2910113) B2910113
theorem B1293023 : Blo 1291964 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B1841887 : Blo 1291964 1841887 := bstep (se 1 (by rfl) ⟨1381415, by rfl⟩ : syracuseStep 1841887 = 2762831) B2762831
theorem B6544151 : Blo 1291964 6544151 := bstep (se 1 (by rfl) ⟨4908113, by rfl⟩ : syracuseStep 6544151 = 9816227) B9816227
theorem B1293103 : Blo 1291964 1293103 := bstep (se 1 (by rfl) ⟨969827, by rfl⟩ : syracuseStep 1293103 = 1939655) B1939655
theorem B1637167 : Blo 1291964 1637167 := bstep (se 1 (by rfl) ⟨1227875, by rfl⟩ : syracuseStep 1637167 = 2455751) B2455751
theorem B35404613 : Blo 1291964 35404613 := bstep (se 4 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 35404613 = 6638365) B6638365
theorem B1940303 : Blo 1291964 1940303 := bstep (se 1 (by rfl) ⟨1455227, by rfl⟩ : syracuseStep 1940303 = 2910455) B2910455
theorem B2907035 : Blo 1291964 2907035 := bstep (se 1 (by rfl) ⟨2180276, by rfl⟩ : syracuseStep 2907035 = 4360553) B4360553
theorem B1293211 : Blo 1291964 1293211 := bstep (se 1 (by rfl) ⟨969908, by rfl⟩ : syracuseStep 1293211 = 1939817) B1939817
theorem B8289209 : Blo 1291964 8289209 := bstep (se 2 (by rfl) ⟨3108453, by rfl⟩ : syracuseStep 8289209 = 6216907) B6216907
theorem B1293263 : Blo 1291964 1293263 := bstep (se 1 (by rfl) ⟨969947, by rfl⟩ : syracuseStep 1293263 = 1939895) B1939895
theorem B1293287 : Blo 1291964 1293287 := bstep (se 1 (by rfl) ⟨969965, by rfl⟩ : syracuseStep 1293287 = 1939931) B1939931
theorem B2907233 : Blo 1291964 2907233 := bstep (se 2 (by rfl) ⟨1090212, by rfl⟩ : syracuseStep 2907233 = 2180425) B2180425
theorem B1940699 : Blo 1291964 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B1293599 : Blo 1291964 1293599 := bstep (se 1 (by rfl) ⟨970199, by rfl⟩ : syracuseStep 1293599 = 1940399) B1940399
theorem B2907431 : Blo 1291964 2907431 := bstep (se 1 (by rfl) ⟨2180573, by rfl⟩ : syracuseStep 2907431 = 4361147) B4361147
theorem B5520707 : Blo 1291964 5520707 := bstep (se 1 (by rfl) ⟨4140530, by rfl⟩ : syracuseStep 5520707 = 8281061) B8281061
theorem B1293659 : Blo 1291964 1293659 := bstep (se 1 (by rfl) ⟨970244, by rfl⟩ : syracuseStep 1293659 = 1940489) B1940489
theorem B1293679 : Blo 1291964 1293679 := bstep (se 1 (by rfl) ⟨970259, by rfl⟩ : syracuseStep 1293679 = 1940519) B1940519
theorem B1940873 : Blo 1291964 1940873 := bstep (se 2 (by rfl) ⟨727827, by rfl⟩ : syracuseStep 1940873 = 1455655) B1455655
theorem B2760097 : Blo 1291964 2760097 := bstep (se 2 (by rfl) ⟨1035036, by rfl⟩ : syracuseStep 2760097 = 2070073) B2070073
theorem B1293735 : Blo 1291964 1293735 := bstep (se 1 (by rfl) ⟨970301, by rfl⟩ : syracuseStep 1293735 = 1940603) B1940603
theorem B1293819 : Blo 1291964 1293819 := bstep (se 1 (by rfl) ⟨970364, by rfl⟩ : syracuseStep 1293819 = 1940729) B1940729
theorem B14728715 : Blo 1291964 14728715 := bstep (se 1 (by rfl) ⟨11046536, by rfl⟩ : syracuseStep 14728715 = 22093073) B22093073
theorem B1293887 : Blo 1291964 1293887 := bstep (se 1 (by rfl) ⟨970415, by rfl⟩ : syracuseStep 1293887 = 1940831) B1940831
theorem B1293895 : Blo 1291964 1293895 := bstep (se 1 (by rfl) ⟨970421, by rfl⟩ : syracuseStep 1293895 = 1940843) B1940843
theorem B2907809 : Blo 1291964 2907809 := bstep (se 2 (by rfl) ⟨1090428, by rfl⟩ : syracuseStep 2907809 = 2180857) B2180857
theorem B2621089 : Blo 1291964 2621089 := bstep (se 2 (by rfl) ⟨982908, by rfl⟩ : syracuseStep 2621089 = 1965817) B1965817
theorem B2072251 : Blo 1291964 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B2948843 : Blo 1291964 2948843 := bstep (se 1 (by rfl) ⟨2211632, by rfl⟩ : syracuseStep 2948843 = 4423265) B4423265
theorem B4906763 : Blo 1291964 4906763 := bstep (se 1 (by rfl) ⟨3680072, by rfl⟩ : syracuseStep 4906763 = 7360145) B7360145
theorem B9822059 : Blo 1291964 9822059 := bstep (se 1 (by rfl) ⟨7366544, by rfl⟩ : syracuseStep 9822059 = 14733089) B14733089
theorem B6545447 : Blo 1291964 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B3784843 : Blo 1291964 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B9822545 : Blo 1291964 9822545 := bstep (se 2 (by rfl) ⟨3683454, by rfl⟩ : syracuseStep 9822545 = 7366909) B7366909
theorem B1966535 : Blo 1291964 1966535 := bstep (se 1 (by rfl) ⟨1474901, by rfl⟩ : syracuseStep 1966535 = 2949803) B2949803
theorem B5595787 : Blo 1291964 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B9323171 : Blo 1291964 9323171 := bstep (se 1 (by rfl) ⟨6992378, by rfl⟩ : syracuseStep 9323171 = 13984757) B13984757
theorem B2908907 : Blo 1291964 2908907 := bstep (se 1 (by rfl) ⟨2181680, by rfl⟩ : syracuseStep 2908907 = 4363361) B4363361
theorem B6546419 : Blo 1291964 6546419 := bstep (se 1 (by rfl) ⟨4909814, by rfl⟩ : syracuseStep 6546419 = 9819629) B9819629
theorem B8283161 : Blo 1291964 8283161 := bstep (se 2 (by rfl) ⟨3106185, by rfl⟩ : syracuseStep 8283161 = 6212371) B6212371
theorem B4908221 : Blo 1291964 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B1746127 : Blo 1291964 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B4662479 : Blo 1291964 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B17696171 : Blo 1291964 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B11052551 : Blo 1291964 11052551 := bstep (se 1 (by rfl) ⟨8289413, by rfl⟩ : syracuseStep 11052551 = 16578827) B16578827
theorem B2909807 : Blo 1291964 2909807 := bstep (se 1 (by rfl) ⟨2182355, by rfl⟩ : syracuseStep 2909807 = 4364711) B4364711
theorem B2180729 : Blo 1291964 2180729 := bstep (se 2 (by rfl) ⟨817773, by rfl⟩ : syracuseStep 2180729 = 1635547) B1635547
theorem B2909915 : Blo 1291964 2909915 := bstep (se 1 (by rfl) ⟨2182436, by rfl⟩ : syracuseStep 2909915 = 4364873) B4364873
theorem B5523167 : Blo 1291964 5523167 := bstep (se 1 (by rfl) ⟨4142375, by rfl⟩ : syracuseStep 5523167 = 8284751) B8284751
theorem B3680129 : Blo 1291964 3680129 := bstep (se 2 (by rfl) ⟨1380048, by rfl⟩ : syracuseStep 3680129 = 2760097) B2760097
theorem B23603075 : Blo 1291964 23603075 := bstep (se 1 (by rfl) ⟨17702306, by rfl⟩ : syracuseStep 23603075 = 35404613) B35404613
theorem B23578543 : Blo 1291964 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B2181215 : Blo 1291964 2181215 := bstep (se 1 (by rfl) ⟨1635911, by rfl⟩ : syracuseStep 2181215 = 3271823) B3271823
theorem B3680471 : Blo 1291964 3680471 := bstep (se 1 (by rfl) ⟨2760353, by rfl⟩ : syracuseStep 3680471 = 5520707) B5520707
theorem B2763001 : Blo 1291964 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B14731631 : Blo 1291964 14731631 := bstep (se 1 (by rfl) ⟨11048723, by rfl⟩ : syracuseStep 14731631 = 22097447) B22097447
theorem B3271175 : Blo 1291964 3271175 := bstep (se 1 (by rfl) ⟨2453381, by rfl⟩ : syracuseStep 3271175 = 4906763) B4906763
theorem B3934747 : Blo 1291964 3934747 := bstep (se 1 (by rfl) ⟨2951060, by rfl⟩ : syracuseStep 3934747 = 5902121) B5902121
theorem B6548039 : Blo 1291964 6548039 := bstep (se 1 (by rfl) ⟨4911029, by rfl⟩ : syracuseStep 6548039 = 9822059) B9822059
theorem B2911031 : Blo 1291964 2911031 := bstep (se 1 (by rfl) ⟨2183273, by rfl⟩ : syracuseStep 2911031 = 4366547) B4366547
theorem B2911211 : Blo 1291964 2911211 := bstep (se 1 (by rfl) ⟨2183408, by rfl⟩ : syracuseStep 2911211 = 4366817) B4366817
theorem B3272015 : Blo 1291964 3272015 := bstep (se 1 (by rfl) ⟨2454011, by rfl⟩ : syracuseStep 3272015 = 4908023) B4908023
theorem B2182511 : Blo 1291964 2182511 := bstep (se 1 (by rfl) ⟨1636883, by rfl⟩ : syracuseStep 2182511 = 3273767) B3273767
theorem B6212987 : Blo 1291964 6212987 := bstep (se 1 (by rfl) ⟨4659740, by rfl⟩ : syracuseStep 6212987 = 9319481) B9319481
theorem B4910665 : Blo 1291964 4910665 := bstep (se 2 (by rfl) ⟨1841499, by rfl⟩ : syracuseStep 4910665 = 3682999) B3682999
theorem B2182747 : Blo 1291964 2182747 := bstep (se 1 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 2182747 = 3274121) B3274121
theorem B16576163 : Blo 1291964 16576163 := bstep (se 1 (by rfl) ⟨12432122, by rfl⟩ : syracuseStep 16576163 = 24864245) B24864245
theorem B4361903 : Blo 1291964 4361903 := bstep (se 1 (by rfl) ⟨3271427, by rfl⟩ : syracuseStep 4361903 = 6542855) B6542855
theorem B2182889 : Blo 1291964 2182889 := bstep (se 2 (by rfl) ⟨818583, by rfl⟩ : syracuseStep 2182889 = 1637167) B1637167
theorem B63745805 : Blo 1291964 63745805 := bstep (se 3 (by rfl) ⟨11952338, by rfl⟩ : syracuseStep 63745805 = 23904677) B23904677
theorem B2453267 : Blo 1291964 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B3682169 : Blo 1291964 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B9957275 : Blo 1291964 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B4362227 : Blo 1291964 4362227 := bstep (se 1 (by rfl) ⟨3271670, by rfl⟩ : syracuseStep 4362227 = 6543341) B6543341
theorem B15732755 : Blo 1291964 15732755 := bstep (se 1 (by rfl) ⟨11799566, by rfl⟩ : syracuseStep 15732755 = 23599133) B23599133
theorem B7368893 : Blo 1291964 7368893 := bstep (se 3 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 7368893 = 2763335) B2763335
theorem B4362551 : Blo 1291964 4362551 := bstep (se 1 (by rfl) ⟨3271913, by rfl⟩ : syracuseStep 4362551 = 6543827) B6543827
theorem B7360895 : Blo 1291964 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B8843687 : Blo 1291964 8843687 := bstep (se 1 (by rfl) ⟨6632765, by rfl⟩ : syracuseStep 8843687 = 13265531) B13265531
theorem B4362767 : Blo 1291964 4362767 := bstep (se 1 (by rfl) ⟨3272075, by rfl⟩ : syracuseStep 4362767 = 6544151) B6544151
theorem B3273311 : Blo 1291964 3273311 := bstep (se 1 (by rfl) ⟨2454983, by rfl⟩ : syracuseStep 3273311 = 4909967) B4909967
theorem B1938023 : Blo 1291964 1938023 := bstep (se 1 (by rfl) ⟨1453517, by rfl⟩ : syracuseStep 1938023 = 2907035) B2907035
theorem B4420199 : Blo 1291964 4420199 := bstep (se 1 (by rfl) ⟨3315149, by rfl⟩ : syracuseStep 4420199 = 6630299) B6630299
theorem B5526139 : Blo 1291964 5526139 := bstep (se 1 (by rfl) ⟨4144604, by rfl⟩ : syracuseStep 5526139 = 8289209) B8289209
theorem B1938155 : Blo 1291964 1938155 := bstep (se 1 (by rfl) ⟨1453616, by rfl⟩ : syracuseStep 1938155 = 2907233) B2907233
theorem B1938185 : Blo 1291964 1938185 := bstep (se 2 (by rfl) ⟨726819, by rfl⟩ : syracuseStep 1938185 = 1453639) B1453639
theorem B1938287 : Blo 1291964 1938287 := bstep (se 1 (by rfl) ⟨1453715, by rfl⟩ : syracuseStep 1938287 = 2907431) B2907431
theorem B3494785 : Blo 1291964 3494785 := bstep (se 2 (by rfl) ⟨1310544, by rfl⟩ : syracuseStep 3494785 = 2621089) B2621089
theorem B8844203 : Blo 1291964 8844203 := bstep (se 1 (by rfl) ⟨6633152, by rfl⟩ : syracuseStep 8844203 = 13266305) B13266305
theorem B9819143 : Blo 1291964 9819143 := bstep (se 1 (by rfl) ⟨7364357, by rfl⟩ : syracuseStep 9819143 = 14728715) B14728715
theorem B1938539 : Blo 1291964 1938539 := bstep (se 1 (by rfl) ⟨1453904, by rfl⟩ : syracuseStep 1938539 = 2907809) B2907809
theorem B4142299 : Blo 1291964 4142299 := bstep (se 1 (by rfl) ⟨3106724, by rfl⟩ : syracuseStep 4142299 = 6213449) B6213449
theorem B17700113 : Blo 1291964 17700113 := bstep (se 2 (by rfl) ⟨6637542, by rfl⟩ : syracuseStep 17700113 = 13275085) B13275085
theorem B1938779 : Blo 1291964 1938779 := bstep (se 1 (by rfl) ⟨1454084, by rfl⟩ : syracuseStep 1938779 = 2908169) B2908169
theorem B13981081 : Blo 1291964 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B141481403 : Blo 1291964 141481403 := bstep (se 1 (by rfl) ⟨106111052, by rfl⟩ : syracuseStep 141481403 = 212222105) B212222105
theorem B4421089 : Blo 1291964 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B6813193 : Blo 1291964 6813193 := bstep (se 2 (by rfl) ⟨2554947, by rfl⟩ : syracuseStep 6813193 = 5109895) B5109895
theorem B29857319 : Blo 1291964 29857319 := bstep (se 1 (by rfl) ⟨22392989, by rfl⟩ : syracuseStep 29857319 = 44785979) B44785979
theorem B4363847 : Blo 1291964 4363847 := bstep (se 1 (by rfl) ⟨3272885, by rfl⟩ : syracuseStep 4363847 = 6545771) B6545771
theorem B1939055 : Blo 1291964 1939055 := bstep (se 1 (by rfl) ⟨1454291, by rfl⟩ : syracuseStep 1939055 = 2908583) B2908583
theorem B1939127 : Blo 1291964 1939127 := bstep (se 1 (by rfl) ⟨1454345, by rfl⟩ : syracuseStep 1939127 = 2908691) B2908691
theorem B1939163 : Blo 1291964 1939163 := bstep (se 1 (by rfl) ⟨1454372, by rfl⟩ : syracuseStep 1939163 = 2908745) B2908745
theorem B18626269 : Blo 1291964 18626269 := bstep (se 3 (by rfl) ⟨3492425, by rfl⟩ : syracuseStep 18626269 = 6984851) B6984851
theorem B1292027 : Blo 1291964 1292027 := bstep (se 1 (by rfl) ⟨969020, by rfl⟩ : syracuseStep 1292027 = 1938041) B1938041
theorem B1292063 : Blo 1291964 1292063 := bstep (se 1 (by rfl) ⟨969047, by rfl⟩ : syracuseStep 1292063 = 1938095) B1938095
theorem B1292095 : Blo 1291964 1292095 := bstep (se 1 (by rfl) ⟨969071, by rfl⟩ : syracuseStep 1292095 = 1938143) B1938143
theorem B1939337 : Blo 1291964 1939337 := bstep (se 2 (by rfl) ⟨727251, by rfl⟩ : syracuseStep 1939337 = 1454503) B1454503
theorem B7362535 : Blo 1291964 7362535 := bstep (se 1 (by rfl) ⟨5521901, by rfl⟩ : syracuseStep 7362535 = 11043803) B11043803
theorem B1292271 : Blo 1291964 1292271 := bstep (se 1 (by rfl) ⟨969203, by rfl⟩ : syracuseStep 1292271 = 1938407) B1938407
theorem B1939439 : Blo 1291964 1939439 := bstep (se 1 (by rfl) ⟨1454579, by rfl⟩ : syracuseStep 1939439 = 2909159) B2909159
theorem B1841135 : Blo 1291964 1841135 := bstep (se 1 (by rfl) ⟨1380851, by rfl⟩ : syracuseStep 1841135 = 2761703) B2761703
theorem B3684457 : Blo 1291964 3684457 := bstep (se 2 (by rfl) ⟨1381671, by rfl⟩ : syracuseStep 3684457 = 2763343) B2763343
theorem B1292443 : Blo 1291964 1292443 := bstep (se 1 (by rfl) ⟨969332, by rfl⟩ : syracuseStep 1292443 = 1938665) B1938665
theorem B1292479 : Blo 1291964 1292479 := bstep (se 1 (by rfl) ⟨969359, by rfl⟩ : syracuseStep 1292479 = 1938719) B1938719
theorem B12605635 : Blo 1291964 12605635 := bstep (se 1 (by rfl) ⟨9454226, by rfl⟩ : syracuseStep 12605635 = 18908453) B18908453
theorem B3274951 : Blo 1291964 3274951 := bstep (se 1 (by rfl) ⟨2456213, by rfl⟩ : syracuseStep 3274951 = 4912427) B4912427
theorem B1939691 : Blo 1291964 1939691 := bstep (se 1 (by rfl) ⟨1454768, by rfl⟩ : syracuseStep 1939691 = 2909537) B2909537
theorem B1939751 : Blo 1291964 1939751 := bstep (se 1 (by rfl) ⟨1454813, by rfl⟩ : syracuseStep 1939751 = 2909627) B2909627
theorem B1841449 : Blo 1291964 1841449 := bstep (se 2 (by rfl) ⟨690543, by rfl⟩ : syracuseStep 1841449 = 1381087) B1381087
theorem B2455849 : Blo 1291964 2455849 := bstep (se 2 (by rfl) ⟨920943, by rfl⟩ : syracuseStep 2455849 = 1841887) B1841887
theorem B1292591 : Blo 1291964 1292591 := bstep (se 1 (by rfl) ⟨969443, by rfl⟩ : syracuseStep 1292591 = 1938887) B1938887
theorem B9812339 : Blo 1291964 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B1939835 : Blo 1291964 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B136198577 : Blo 1291964 136198577 := bstep (se 2 (by rfl) ⟨51074466, by rfl⟩ : syracuseStep 136198577 = 102148933) B102148933
theorem B4364819 : Blo 1291964 4364819 := bstep (se 1 (by rfl) ⟨3273614, by rfl⟩ : syracuseStep 4364819 = 6547229) B6547229
theorem B1292827 : Blo 1291964 1292827 := bstep (se 1 (by rfl) ⟨969620, by rfl⟩ : syracuseStep 1292827 = 1939241) B1939241
theorem B1292831 : Blo 1291964 1292831 := bstep (se 1 (by rfl) ⟨969623, by rfl⟩ : syracuseStep 1292831 = 1939247) B1939247
theorem B4905593 : Blo 1291964 4905593 := bstep (se 2 (by rfl) ⟨1839597, by rfl⟩ : syracuseStep 4905593 = 3679195) B3679195
theorem B1940105 : Blo 1291964 1940105 := bstep (se 2 (by rfl) ⟨727539, by rfl⟩ : syracuseStep 1940105 = 1455079) B1455079
theorem B4143773 : Blo 1291964 4143773 := bstep (se 3 (by rfl) ⟨776957, by rfl⟩ : syracuseStep 4143773 = 1553915) B1553915
theorem B22084325 : Blo 1291964 22084325 := bstep (se 4 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 22084325 = 4140811) B4140811
theorem B1940279 : Blo 1291964 1940279 := bstep (se 1 (by rfl) ⟨1455209, by rfl⟩ : syracuseStep 1940279 = 2910419) B2910419
theorem B2906963 : Blo 1291964 2906963 := bstep (se 1 (by rfl) ⟨2180222, by rfl⟩ : syracuseStep 2906963 = 4360445) B4360445
theorem B1293147 : Blo 1291964 1293147 := bstep (se 1 (by rfl) ⟨969860, by rfl⟩ : syracuseStep 1293147 = 1939721) B1939721
theorem B1940315 : Blo 1291964 1940315 := bstep (se 1 (by rfl) ⟨1455236, by rfl⟩ : syracuseStep 1940315 = 2910473) B2910473
theorem B1293215 : Blo 1291964 1293215 := bstep (se 1 (by rfl) ⟨969911, by rfl⟩ : syracuseStep 1293215 = 1939823) B1939823
theorem B24837029 : Blo 1291964 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B26557391 : Blo 1291964 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B1940459 : Blo 1291964 1940459 := bstep (se 1 (by rfl) ⟨1455344, by rfl⟩ : syracuseStep 1940459 = 2910689) B2910689
theorem B1293359 : Blo 1291964 1293359 := bstep (se 1 (by rfl) ⟨970019, by rfl⟩ : syracuseStep 1293359 = 1940039) B1940039
theorem B1293383 : Blo 1291964 1293383 := bstep (se 1 (by rfl) ⟨970037, by rfl⟩ : syracuseStep 1293383 = 1940075) B1940075
theorem B7969907 : Blo 1291964 7969907 := bstep (se 1 (by rfl) ⟨5977430, by rfl⟩ : syracuseStep 7969907 = 11954861) B11954861
theorem B4906109 : Blo 1291964 4906109 := bstep (se 3 (by rfl) ⟨919895, by rfl⟩ : syracuseStep 4906109 = 1839791) B1839791
theorem B1940663 : Blo 1291964 1940663 := bstep (se 1 (by rfl) ⟨1455497, by rfl⟩ : syracuseStep 1940663 = 2910995) B2910995
theorem B1293535 : Blo 1291964 1293535 := bstep (se 1 (by rfl) ⟨970151, by rfl⟩ : syracuseStep 1293535 = 1940303) B1940303
theorem B6544637 : Blo 1291964 6544637 := bstep (se 3 (by rfl) ⟨1227119, by rfl⟩ : syracuseStep 6544637 = 2454239) B2454239
theorem B7863581 : Blo 1291964 7863581 := bstep (se 3 (by rfl) ⟨1474421, by rfl⟩ : syracuseStep 7863581 = 2948843) B2948843
theorem B2907503 : Blo 1291964 2907503 := bstep (se 1 (by rfl) ⟨2180627, by rfl⟩ : syracuseStep 2907503 = 4361255) B4361255
theorem B1940903 : Blo 1291964 1940903 := bstep (se 1 (by rfl) ⟨1455677, by rfl⟩ : syracuseStep 1940903 = 2911355) B2911355
theorem B1293799 : Blo 1291964 1293799 := bstep (se 1 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 1293799 = 1940699) B1940699
theorem B1293915 : Blo 1291964 1293915 := bstep (se 1 (by rfl) ⟨970436, by rfl⟩ : syracuseStep 1293915 = 1940873) B1940873
theorem B2907791 : Blo 1291964 2907791 := bstep (se 1 (by rfl) ⟨2180843, by rfl⟩ : syracuseStep 2907791 = 4361687) B4361687
theorem B2907881 : Blo 1291964 2907881 := bstep (se 2 (by rfl) ⟨1090455, by rfl⟩ : syracuseStep 2907881 = 2180911) B2180911
theorem B2072297 : Blo 1291964 2072297 := bstep (se 2 (by rfl) ⟨777111, by rfl⟩ : syracuseStep 2072297 = 1554223) B1554223
theorem B2760439 : Blo 1291964 2760439 := bstep (se 1 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 2760439 = 4140659) B4140659
theorem B5046457 : Blo 1291964 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B2908367 : Blo 1291964 2908367 := bstep (se 1 (by rfl) ⟨2181275, by rfl⟩ : syracuseStep 2908367 = 4362551) B4362551
theorem B4907263 : Blo 1291964 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B4366601 : Blo 1291964 4366601 := bstep (se 2 (by rfl) ⟨1637475, by rfl⟩ : syracuseStep 4366601 = 3274951) B3274951
theorem B1311023 : Blo 1291964 1311023 := bstep (se 1 (by rfl) ⟨983267, by rfl⟩ : syracuseStep 1311023 = 1966535) B1966535
theorem B2908511 : Blo 1291964 2908511 := bstep (se 1 (by rfl) ⟨2181383, by rfl⟩ : syracuseStep 2908511 = 4362767) B4362767
theorem B6546095 : Blo 1291964 6546095 := bstep (se 1 (by rfl) ⟨4909571, by rfl⟩ : syracuseStep 6546095 = 9819143) B9819143
theorem B5522107 : Blo 1291964 5522107 := bstep (se 1 (by rfl) ⟨4141580, by rfl⟩ : syracuseStep 5522107 = 8283161) B8283161
theorem B29844197 : Blo 1291964 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B2909231 : Blo 1291964 2909231 := bstep (se 1 (by rfl) ⟨2181923, by rfl⟩ : syracuseStep 2909231 = 4363847) B4363847
theorem B2328169 : Blo 1291964 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B5523065 : Blo 1291964 5523065 := bstep (se 2 (by rfl) ⟨2071149, by rfl⟩ : syracuseStep 5523065 = 4142299) B4142299
theorem B2180783 : Blo 1291964 2180783 := bstep (se 1 (by rfl) ⟨1635587, by rfl⟩ : syracuseStep 2180783 = 3271175) B3271175
theorem B2909879 : Blo 1291964 2909879 := bstep (se 1 (by rfl) ⟨2182409, by rfl⟩ : syracuseStep 2909879 = 4364819) B4364819
theorem B3270395 : Blo 1291964 3270395 := bstep (se 1 (by rfl) ⟨2452796, by rfl⟩ : syracuseStep 3270395 = 4905593) B4905593
theorem B2762515 : Blo 1291964 2762515 := bstep (se 1 (by rfl) ⟨2071886, by rfl⟩ : syracuseStep 2762515 = 4143773) B4143773
theorem B14722883 : Blo 1291964 14722883 := bstep (se 1 (by rfl) ⟨11042162, by rfl⟩ : syracuseStep 14722883 = 22084325) B22084325
theorem B16558019 : Blo 1291964 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B17704927 : Blo 1291964 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B3270739 : Blo 1291964 3270739 := bstep (se 1 (by rfl) ⟨2453054, by rfl⟩ : syracuseStep 3270739 = 4906109) B4906109
theorem B6547553 : Blo 1291964 6547553 := bstep (se 2 (by rfl) ⟨2455332, by rfl⟩ : syracuseStep 6547553 = 4910665) B4910665
theorem B2910329 : Blo 1291964 2910329 := bstep (se 2 (by rfl) ⟨1091373, by rfl⟩ : syracuseStep 2910329 = 2182747) B2182747
theorem B2181343 : Blo 1291964 2181343 := bstep (se 1 (by rfl) ⟨1636007, by rfl⟩ : syracuseStep 2181343 = 3272015) B3272015
theorem B3680585 : Blo 1291964 3680585 := bstep (se 2 (by rfl) ⟨1380219, by rfl⟩ : syracuseStep 3680585 = 2760439) B2760439
theorem B6638183 : Blo 1291964 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B4909693 : Blo 1291964 4909693 := bstep (se 3 (by rfl) ⟨920567, by rfl⟩ : syracuseStep 4909693 = 1841135) B1841135
theorem B9816713 : Blo 1291964 9816713 := bstep (se 2 (by rfl) ⟨3681267, by rfl⟩ : syracuseStep 9816713 = 7362535) B7362535
theorem B10488503 : Blo 1291964 10488503 := bstep (se 1 (by rfl) ⟨7866377, by rfl⟩ : syracuseStep 10488503 = 15732755) B15732755
theorem B6548363 : Blo 1291964 6548363 := bstep (se 1 (by rfl) ⟨4911272, by rfl⟩ : syracuseStep 6548363 = 9822545) B9822545
theorem B2182207 : Blo 1291964 2182207 := bstep (se 1 (by rfl) ⟨1636655, by rfl⟩ : syracuseStep 2182207 = 3273311) B3273311
theorem B5246329 : Blo 1291964 5246329 := bstep (se 2 (by rfl) ⟨1967373, by rfl⟩ : syracuseStep 5246329 = 3934747) B3934747
theorem B3272147 : Blo 1291964 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B7368185 : Blo 1291964 7368185 := bstep (se 2 (by rfl) ⟨2763069, by rfl⟩ : syracuseStep 7368185 = 5526139) B5526139
theorem B11800075 : Blo 1291964 11800075 := bstep (se 1 (by rfl) ⟨8850056, by rfl⟩ : syracuseStep 11800075 = 17700113) B17700113
theorem B7368367 : Blo 1291964 7368367 := bstep (se 1 (by rfl) ⟨5526275, by rfl⟩ : syracuseStep 7368367 = 11052551) B11052551
theorem B1453819 : Blo 1291964 1453819 := bstep (se 1 (by rfl) ⟨1090364, by rfl⟩ : syracuseStep 1453819 = 2180729) B2180729
theorem B47189789 : Blo 1291964 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B3682111 : Blo 1291964 3682111 := bstep (se 1 (by rfl) ⟨2761583, by rfl⟩ : syracuseStep 3682111 = 5523167) B5523167
theorem B2453419 : Blo 1291964 2453419 := bstep (se 1 (by rfl) ⟨1840064, by rfl⟩ : syracuseStep 2453419 = 3680129) B3680129
theorem B1454143 : Blo 1291964 1454143 := bstep (se 1 (by rfl) ⟨1090607, by rfl⟩ : syracuseStep 1454143 = 2181215) B2181215
theorem B2453647 : Blo 1291964 2453647 := bstep (se 1 (by rfl) ⟨1840235, by rfl⟩ : syracuseStep 2453647 = 3680471) B3680471
theorem B6541559 : Blo 1291964 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B18641441 : Blo 1291964 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B1937975 : Blo 1291964 1937975 := bstep (se 1 (by rfl) ⟨1453481, by rfl⟩ : syracuseStep 1937975 = 2906963) B2906963
theorem B5894785 : Blo 1291964 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B169988813 : Blo 1291964 169988813 := bstep (se 3 (by rfl) ⟨31872902, by rfl⟩ : syracuseStep 169988813 = 63745805) B63745805
theorem B6542045 : Blo 1291964 6542045 := bstep (se 3 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 6542045 = 2453267) B2453267
theorem B5313271 : Blo 1291964 5313271 := bstep (se 1 (by rfl) ⟨3984953, by rfl⟩ : syracuseStep 5313271 = 7969907) B7969907
theorem B4363091 : Blo 1291964 4363091 := bstep (se 1 (by rfl) ⟨3272318, by rfl⟩ : syracuseStep 4363091 = 6544637) B6544637
theorem B1938335 : Blo 1291964 1938335 := bstep (se 1 (by rfl) ⟨1453751, by rfl⟩ : syracuseStep 1938335 = 2907503) B2907503
theorem B1455007 : Blo 1291964 1455007 := bstep (se 1 (by rfl) ⟨1091255, by rfl⟩ : syracuseStep 1455007 = 2182511) B2182511
theorem B4141991 : Blo 1291964 4141991 := bstep (se 1 (by rfl) ⟨3106493, by rfl⟩ : syracuseStep 4141991 = 6212987) B6212987
theorem B24835025 : Blo 1291964 24835025 := bstep (se 2 (by rfl) ⟨9313134, by rfl⟩ : syracuseStep 24835025 = 18626269) B18626269
theorem B1938527 : Blo 1291964 1938527 := bstep (se 1 (by rfl) ⟨1453895, by rfl⟩ : syracuseStep 1938527 = 2907791) B2907791
theorem B1938587 : Blo 1291964 1938587 := bstep (se 1 (by rfl) ⟨1453940, by rfl⟩ : syracuseStep 1938587 = 2907881) B2907881
theorem B1455259 : Blo 1291964 1455259 := bstep (se 1 (by rfl) ⟨1091444, by rfl⟩ : syracuseStep 1455259 = 2182889) B2182889
theorem B1381531 : Blo 1291964 1381531 := bstep (se 1 (by rfl) ⟨1036148, by rfl⟩ : syracuseStep 1381531 = 2072297) B2072297
theorem B31438057 : Blo 1291964 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B2454779 : Blo 1291964 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B4363631 : Blo 1291964 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B4912595 : Blo 1291964 4912595 := bstep (se 1 (by rfl) ⟨3684446, by rfl⟩ : syracuseStep 4912595 = 7368893) B7368893
theorem B4912609 : Blo 1291964 4912609 := bstep (se 2 (by rfl) ⟨1842228, by rfl⟩ : syracuseStep 4912609 = 3684457) B3684457
theorem B16807513 : Blo 1291964 16807513 := bstep (se 2 (by rfl) ⟨6302817, by rfl⟩ : syracuseStep 16807513 = 12605635) B12605635
theorem B5895791 : Blo 1291964 5895791 := bstep (se 1 (by rfl) ⟨4421843, by rfl⟩ : syracuseStep 5895791 = 8843687) B8843687
theorem B2455265 : Blo 1291964 2455265 := bstep (se 2 (by rfl) ⟨920724, by rfl⟩ : syracuseStep 2455265 = 1841449) B1841449
theorem B3274465 : Blo 1291964 3274465 := bstep (se 2 (by rfl) ⟨1227924, by rfl⟩ : syracuseStep 3274465 = 2455849) B2455849
theorem B1292015 : Blo 1291964 1292015 := bstep (se 1 (by rfl) ⟨969011, by rfl⟩ : syracuseStep 1292015 = 1938023) B1938023
theorem B2946799 : Blo 1291964 2946799 := bstep (se 1 (by rfl) ⟨2210099, by rfl⟩ : syracuseStep 2946799 = 4420199) B4420199
theorem B6215447 : Blo 1291964 6215447 := bstep (se 1 (by rfl) ⟨4661585, by rfl⟩ : syracuseStep 6215447 = 9323171) B9323171
theorem B1292103 : Blo 1291964 1292103 := bstep (se 1 (by rfl) ⟨969077, by rfl⟩ : syracuseStep 1292103 = 1938155) B1938155
theorem B1939271 : Blo 1291964 1939271 := bstep (se 1 (by rfl) ⟨1454453, by rfl⟩ : syracuseStep 1939271 = 2908907) B2908907
theorem B1292123 : Blo 1291964 1292123 := bstep (se 1 (by rfl) ⟨969092, by rfl⟩ : syracuseStep 1292123 = 1938185) B1938185
theorem B12433277 : Blo 1291964 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B1292191 : Blo 1291964 1292191 := bstep (se 1 (by rfl) ⟨969143, by rfl⟩ : syracuseStep 1292191 = 1938287) B1938287
theorem B5896135 : Blo 1291964 5896135 := bstep (se 1 (by rfl) ⟨4422101, by rfl⟩ : syracuseStep 5896135 = 8844203) B8844203
theorem B4364279 : Blo 1291964 4364279 := bstep (se 1 (by rfl) ⟨3273209, by rfl⟩ : syracuseStep 4364279 = 6546419) B6546419
theorem B1292359 : Blo 1291964 1292359 := bstep (se 1 (by rfl) ⟨969269, by rfl⟩ : syracuseStep 1292359 = 1938539) B1938539
theorem B20969549 : Blo 1291964 20969549 := bstep (se 3 (by rfl) ⟨3931790, by rfl⟩ : syracuseStep 20969549 = 7863581) B7863581
theorem B1292519 : Blo 1291964 1292519 := bstep (se 1 (by rfl) ⟨969389, by rfl⟩ : syracuseStep 1292519 = 1938779) B1938779
theorem B94320935 : Blo 1291964 94320935 := bstep (se 1 (by rfl) ⟨70740701, by rfl⟩ : syracuseStep 94320935 = 141481403) B141481403
theorem B19904879 : Blo 1291964 19904879 := bstep (se 1 (by rfl) ⟨14928659, by rfl⟩ : syracuseStep 19904879 = 29857319) B29857319
theorem B1292703 : Blo 1291964 1292703 := bstep (se 1 (by rfl) ⟨969527, by rfl⟩ : syracuseStep 1292703 = 1939055) B1939055
theorem B1939871 : Blo 1291964 1939871 := bstep (se 1 (by rfl) ⟨1454903, by rfl⟩ : syracuseStep 1939871 = 2909807) B2909807
theorem B1292751 : Blo 1291964 1292751 := bstep (se 1 (by rfl) ⟨969563, by rfl⟩ : syracuseStep 1292751 = 1939127) B1939127
theorem B1292775 : Blo 1291964 1292775 := bstep (se 1 (by rfl) ⟨969581, by rfl⟩ : syracuseStep 1292775 = 1939163) B1939163
theorem B1939943 : Blo 1291964 1939943 := bstep (se 1 (by rfl) ⟨1454957, by rfl⟩ : syracuseStep 1939943 = 2909915) B2909915
theorem B4659713 : Blo 1291964 4659713 := bstep (se 2 (by rfl) ⟨1747392, by rfl⟩ : syracuseStep 4659713 = 3494785) B3494785
theorem B15735383 : Blo 1291964 15735383 := bstep (se 1 (by rfl) ⟨11801537, by rfl⟩ : syracuseStep 15735383 = 23603075) B23603075
theorem B1292891 : Blo 1291964 1292891 := bstep (se 1 (by rfl) ⟨969668, by rfl⟩ : syracuseStep 1292891 = 1939337) B1939337
theorem B14736005 : Blo 1291964 14736005 := bstep (se 4 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 14736005 = 2763001) B2763001
theorem B1292959 : Blo 1291964 1292959 := bstep (se 1 (by rfl) ⟨969719, by rfl⟩ : syracuseStep 1292959 = 1939439) B1939439
theorem B1293127 : Blo 1291964 1293127 := bstep (se 1 (by rfl) ⟨969845, by rfl⟩ : syracuseStep 1293127 = 1939691) B1939691
theorem B1293167 : Blo 1291964 1293167 := bstep (se 1 (by rfl) ⟨969875, by rfl⟩ : syracuseStep 1293167 = 1939751) B1939751
theorem B9821087 : Blo 1291964 9821087 := bstep (se 1 (by rfl) ⟨7365815, by rfl⟩ : syracuseStep 9821087 = 14731631) B14731631
theorem B1293223 : Blo 1291964 1293223 := bstep (se 1 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 1293223 = 1939835) B1939835
theorem B90799051 : Blo 1291964 90799051 := bstep (se 1 (by rfl) ⟨68099288, by rfl⟩ : syracuseStep 90799051 = 136198577) B136198577
theorem B4365359 : Blo 1291964 4365359 := bstep (se 1 (by rfl) ⟨3274019, by rfl⟩ : syracuseStep 4365359 = 6548039) B6548039
theorem B1293403 : Blo 1291964 1293403 := bstep (se 1 (by rfl) ⟨970052, by rfl⟩ : syracuseStep 1293403 = 1940105) B1940105
theorem B1293519 : Blo 1291964 1293519 := bstep (se 1 (by rfl) ⟨970139, by rfl⟩ : syracuseStep 1293519 = 1940279) B1940279
theorem B1940687 : Blo 1291964 1940687 := bstep (se 1 (by rfl) ⟨1455515, by rfl⟩ : syracuseStep 1940687 = 2911031) B2911031
theorem B1293543 : Blo 1291964 1293543 := bstep (se 1 (by rfl) ⟨970157, by rfl⟩ : syracuseStep 1293543 = 1940315) B1940315
theorem B1293639 : Blo 1291964 1293639 := bstep (se 1 (by rfl) ⟨970229, by rfl⟩ : syracuseStep 1293639 = 1940459) B1940459
theorem B1940807 : Blo 1291964 1940807 := bstep (se 1 (by rfl) ⟨1455605, by rfl⟩ : syracuseStep 1940807 = 2911211) B2911211
theorem B9084257 : Blo 1291964 9084257 := bstep (se 2 (by rfl) ⟨3406596, by rfl⟩ : syracuseStep 9084257 = 6813193) B6813193
theorem B1293775 : Blo 1291964 1293775 := bstep (se 1 (by rfl) ⟨970331, by rfl⟩ : syracuseStep 1293775 = 1940663) B1940663
theorem B1293935 : Blo 1291964 1293935 := bstep (se 1 (by rfl) ⟨970451, by rfl⟩ : syracuseStep 1293935 = 1940903) B1940903
theorem B11050775 : Blo 1291964 11050775 := bstep (se 1 (by rfl) ⟨8288081, by rfl⟩ : syracuseStep 11050775 = 16576163) B16576163
theorem B2907935 : Blo 1291964 2907935 := bstep (se 1 (by rfl) ⟨2180951, by rfl⟩ : syracuseStep 2907935 = 4361903) B4361903
theorem B2908151 : Blo 1291964 2908151 := bstep (se 1 (by rfl) ⟨2181113, by rfl⟩ : syracuseStep 2908151 = 4362227) B4362227
theorem B2908457 : Blo 1291964 2908457 := bstep (se 2 (by rfl) ⟨1090671, by rfl⟩ : syracuseStep 2908457 = 2181343) B2181343
theorem B12427627 : Blo 1291964 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B2908727 : Blo 1291964 2908727 := bstep (se 1 (by rfl) ⟨2181545, by rfl⟩ : syracuseStep 2908727 = 4363091) B4363091
theorem B2761327 : Blo 1291964 2761327 := bstep (se 1 (by rfl) ⟨2070995, by rfl⟩ : syracuseStep 2761327 = 4141991) B4141991
theorem B16556683 : Blo 1291964 16556683 := bstep (se 1 (by rfl) ⟨12417512, by rfl⟩ : syracuseStep 16556683 = 24835025) B24835025
theorem B6546257 : Blo 1291964 6546257 := bstep (se 2 (by rfl) ⟨2454846, by rfl⟩ : syracuseStep 6546257 = 4909693) B4909693
theorem B2909087 : Blo 1291964 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B2180263 : Blo 1291964 2180263 := bstep (se 1 (by rfl) ⟨1635197, by rfl⟩ : syracuseStep 2180263 = 3270395) B3270395
theorem B9815255 : Blo 1291964 9815255 := bstep (se 1 (by rfl) ⟨7361441, by rfl⟩ : syracuseStep 9815255 = 14722883) B14722883
theorem B2909519 : Blo 1291964 2909519 := bstep (se 1 (by rfl) ⟨2182139, by rfl⟩ : syracuseStep 2909519 = 4364279) B4364279
theorem B2909609 : Blo 1291964 2909609 := bstep (se 2 (by rfl) ⟨1091103, by rfl⟩ : syracuseStep 2909609 = 2182207) B2182207
theorem B3106475 : Blo 1291964 3106475 := bstep (se 1 (by rfl) ⟨2329856, by rfl⟩ : syracuseStep 3106475 = 4659713) B4659713
theorem B4425455 : Blo 1291964 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B9824003 : Blo 1291964 9824003 := bstep (se 1 (by rfl) ⟨7368002, by rfl⟩ : syracuseStep 9824003 = 14736005) B14736005
theorem B6547391 : Blo 1291964 6547391 := bstep (se 1 (by rfl) ⟨4910543, by rfl⟩ : syracuseStep 6547391 = 9821087) B9821087
theorem B2910239 : Blo 1291964 2910239 := bstep (se 1 (by rfl) ⟨2182679, by rfl⟩ : syracuseStep 2910239 = 4365359) B4365359
theorem B9824489 : Blo 1291964 9824489 := bstep (se 2 (by rfl) ⟨3684183, by rfl⟩ : syracuseStep 9824489 = 7368367) B7368367
theorem B6056171 : Blo 1291964 6056171 := bstep (se 1 (by rfl) ⟨4542128, by rfl⟩ : syracuseStep 6056171 = 9084257) B9084257
theorem B2181431 : Blo 1291964 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B4909481 : Blo 1291964 4909481 := bstep (se 2 (by rfl) ⟨1841055, by rfl⟩ : syracuseStep 4909481 = 3682111) B3682111
theorem B7367183 : Blo 1291964 7367183 := bstep (se 1 (by rfl) ⟨5525387, by rfl⟩ : syracuseStep 7367183 = 11050775) B11050775
theorem B31459859 : Blo 1291964 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B3271225 : Blo 1291964 3271225 := bstep (se 2 (by rfl) ⟨1226709, by rfl⟩ : syracuseStep 3271225 = 2453419) B2453419
theorem B4360985 : Blo 1291964 4360985 := bstep (se 2 (by rfl) ⟨1635369, by rfl⟩ : syracuseStep 4360985 = 3270739) B3270739
theorem B4361039 : Blo 1291964 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B2911067 : Blo 1291964 2911067 := bstep (se 1 (by rfl) ⟨2183300, by rfl⟩ : syracuseStep 2911067 = 4366601) B4366601
theorem B3271529 : Blo 1291964 3271529 := bstep (se 2 (by rfl) ⟨1226823, by rfl⟩ : syracuseStep 3271529 = 2453647) B2453647
theorem B6728609 : Blo 1291964 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B4361363 : Blo 1291964 4361363 := bstep (se 1 (by rfl) ⟨3271022, by rfl⟩ : syracuseStep 4361363 = 6542045) B6542045
theorem B7859713 : Blo 1291964 7859713 := bstep (se 2 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 7859713 = 5894785) B5894785
theorem B3682043 : Blo 1291964 3682043 := bstep (se 1 (by rfl) ⟨2761532, by rfl⟩ : syracuseStep 3682043 = 5523065) B5523065
theorem B1453855 : Blo 1291964 1453855 := bstep (se 1 (by rfl) ⟨1090391, by rfl⟩ : syracuseStep 1453855 = 2180783) B2180783
theorem B15716261 : Blo 1291964 15716261 := bstep (se 4 (by rfl) ⟨1473399, by rfl⟩ : syracuseStep 15716261 = 2946799) B2946799
theorem B121065401 : Blo 1291964 121065401 := bstep (se 2 (by rfl) ⟨45399525, by rfl⟩ : syracuseStep 121065401 = 90799051) B90799051
theorem B11038679 : Blo 1291964 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B13979699 : Blo 1291964 13979699 := bstep (se 1 (by rfl) ⟨10484774, by rfl⟩ : syracuseStep 13979699 = 20969549) B20969549
theorem B2453723 : Blo 1291964 2453723 := bstep (se 1 (by rfl) ⟨1840292, by rfl⟩ : syracuseStep 2453723 = 3680585) B3680585
theorem B10490255 : Blo 1291964 10490255 := bstep (se 1 (by rfl) ⟨7867691, by rfl⟩ : syracuseStep 10490255 = 15735383) B15735383
theorem B6992335 : Blo 1291964 6992335 := bstep (se 1 (by rfl) ⟨5244251, by rfl⟩ : syracuseStep 6992335 = 10488503) B10488503
theorem B6550145 : Blo 1291964 6550145 := bstep (se 2 (by rfl) ⟨2456304, by rfl⟩ : syracuseStep 6550145 = 4912609) B4912609
theorem B15733433 : Blo 1291964 15733433 := bstep (se 2 (by rfl) ⟨5900037, by rfl⟩ : syracuseStep 15733433 = 11800075) B11800075
theorem B22410017 : Blo 1291964 22410017 := bstep (se 2 (by rfl) ⟨8403756, by rfl⟩ : syracuseStep 22410017 = 16807513) B16807513
theorem B1938425 : Blo 1291964 1938425 := bstep (se 2 (by rfl) ⟨726909, by rfl⟩ : syracuseStep 1938425 = 1453819) B1453819
theorem B4912123 : Blo 1291964 4912123 := bstep (se 1 (by rfl) ⟨3684092, by rfl⟩ : syracuseStep 4912123 = 7368185) B7368185
theorem B3683353 : Blo 1291964 3683353 := bstep (se 2 (by rfl) ⟨1381257, by rfl⟩ : syracuseStep 3683353 = 2762515) B2762515
theorem B31446053 : Blo 1291964 31446053 := bstep (se 4 (by rfl) ⟨2948067, by rfl⟩ : syracuseStep 31446053 = 5896135) B5896135
theorem B1938623 : Blo 1291964 1938623 := bstep (se 1 (by rfl) ⟨1453967, by rfl⟩ : syracuseStep 1938623 = 2907935) B2907935
theorem B23606569 : Blo 1291964 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B1938767 : Blo 1291964 1938767 := bstep (se 1 (by rfl) ⟨1454075, by rfl⟩ : syracuseStep 1938767 = 2908151) B2908151
theorem B1938857 : Blo 1291964 1938857 := bstep (se 2 (by rfl) ⟨727071, by rfl⟩ : syracuseStep 1938857 = 1454143) B1454143
theorem B1938911 : Blo 1291964 1938911 := bstep (se 1 (by rfl) ⟨1454183, by rfl⟩ : syracuseStep 1938911 = 2908367) B2908367
theorem B1939007 : Blo 1291964 1939007 := bstep (se 1 (by rfl) ⟨1454255, by rfl⟩ : syracuseStep 1939007 = 2908511) B2908511
theorem B6543017 : Blo 1291964 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B1291983 : Blo 1291964 1291983 := bstep (se 1 (by rfl) ⟨968987, by rfl⟩ : syracuseStep 1291983 = 1937975) B1937975
theorem B4364063 : Blo 1291964 4364063 := bstep (se 1 (by rfl) ⟨3273047, by rfl⟩ : syracuseStep 4364063 = 6546095) B6546095
theorem B113325875 : Blo 1291964 113325875 := bstep (se 1 (by rfl) ⟨84994406, by rfl⟩ : syracuseStep 113325875 = 169988813) B169988813
theorem B19896131 : Blo 1291964 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B1292223 : Blo 1291964 1292223 := bstep (se 1 (by rfl) ⟨969167, by rfl⟩ : syracuseStep 1292223 = 1938335) B1938335
theorem B1939487 : Blo 1291964 1939487 := bstep (se 1 (by rfl) ⟨1454615, by rfl⟩ : syracuseStep 1939487 = 2909231) B2909231
theorem B1292351 : Blo 1291964 1292351 := bstep (se 1 (by rfl) ⟨969263, by rfl⟩ : syracuseStep 1292351 = 1938527) B1938527
theorem B1292391 : Blo 1291964 1292391 := bstep (se 1 (by rfl) ⟨969293, by rfl⟩ : syracuseStep 1292391 = 1938587) B1938587
theorem B3496061 : Blo 1291964 3496061 := bstep (se 3 (by rfl) ⟨655511, by rfl⟩ : syracuseStep 3496061 = 1311023) B1311023
theorem B1636519 : Blo 1291964 1636519 := bstep (se 1 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 1636519 = 2454779) B2454779
theorem B7362809 : Blo 1291964 7362809 := bstep (se 2 (by rfl) ⟨2761053, by rfl⟩ : syracuseStep 7362809 = 5522107) B5522107
theorem B3275063 : Blo 1291964 3275063 := bstep (se 1 (by rfl) ⟨2456297, by rfl⟩ : syracuseStep 3275063 = 4912595) B4912595
theorem B7084361 : Blo 1291964 7084361 := bstep (se 2 (by rfl) ⟨2656635, by rfl⟩ : syracuseStep 7084361 = 5313271) B5313271
theorem B3930527 : Blo 1291964 3930527 := bstep (se 1 (by rfl) ⟨2947895, by rfl⟩ : syracuseStep 3930527 = 5895791) B5895791
theorem B1939919 : Blo 1291964 1939919 := bstep (se 1 (by rfl) ⟨1454939, by rfl⟩ : syracuseStep 1939919 = 2909879) B2909879
theorem B1636843 : Blo 1291964 1636843 := bstep (se 1 (by rfl) ⟨1227632, by rfl⟩ : syracuseStep 1636843 = 2455265) B2455265
theorem B4143631 : Blo 1291964 4143631 := bstep (se 1 (by rfl) ⟨3107723, by rfl⟩ : syracuseStep 4143631 = 6215447) B6215447
theorem B1940009 : Blo 1291964 1940009 := bstep (se 2 (by rfl) ⟨727503, by rfl⟩ : syracuseStep 1940009 = 1455007) B1455007
theorem B1292847 : Blo 1291964 1292847 := bstep (se 1 (by rfl) ⟨969635, by rfl⟩ : syracuseStep 1292847 = 1939271) B1939271
theorem B8288851 : Blo 1291964 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B4365035 : Blo 1291964 4365035 := bstep (se 1 (by rfl) ⟨3273776, by rfl⟩ : syracuseStep 4365035 = 6547553) B6547553
theorem B1940219 : Blo 1291964 1940219 := bstep (se 1 (by rfl) ⟨1455164, by rfl⟩ : syracuseStep 1940219 = 2910329) B2910329
theorem B62880623 : Blo 1291964 62880623 := bstep (se 1 (by rfl) ⟨47160467, by rfl⟩ : syracuseStep 62880623 = 94320935) B94320935
theorem B1940345 : Blo 1291964 1940345 := bstep (se 2 (by rfl) ⟨727629, by rfl⟩ : syracuseStep 1940345 = 1455259) B1455259
theorem B1842041 : Blo 1291964 1842041 := bstep (se 2 (by rfl) ⟨690765, by rfl⟩ : syracuseStep 1842041 = 1381531) B1381531
theorem B13269919 : Blo 1291964 13269919 := bstep (se 1 (by rfl) ⟨9952439, by rfl⟩ : syracuseStep 13269919 = 19904879) B19904879
theorem B1293247 : Blo 1291964 1293247 := bstep (se 1 (by rfl) ⟨969935, by rfl⟩ : syracuseStep 1293247 = 1939871) B1939871
theorem B41917409 : Blo 1291964 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B1293295 : Blo 1291964 1293295 := bstep (se 1 (by rfl) ⟨969971, by rfl⟩ : syracuseStep 1293295 = 1939943) B1939943
theorem B6544475 : Blo 1291964 6544475 := bstep (se 1 (by rfl) ⟨4908356, by rfl⟩ : syracuseStep 6544475 = 9816713) B9816713
theorem B6995105 : Blo 1291964 6995105 := bstep (se 2 (by rfl) ⟨2623164, by rfl⟩ : syracuseStep 6995105 = 5246329) B5246329
theorem B4365575 : Blo 1291964 4365575 := bstep (se 1 (by rfl) ⟨3274181, by rfl⟩ : syracuseStep 4365575 = 6548363) B6548363
theorem B1293791 : Blo 1291964 1293791 := bstep (se 1 (by rfl) ⟨970343, by rfl⟩ : syracuseStep 1293791 = 1940687) B1940687
theorem B3104225 : Blo 1291964 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B1293871 : Blo 1291964 1293871 := bstep (se 1 (by rfl) ⟨970403, by rfl⟩ : syracuseStep 1293871 = 1940807) B1940807
theorem B4365953 : Blo 1291964 4365953 := bstep (se 2 (by rfl) ⟨1637232, by rfl⟩ : syracuseStep 4365953 = 3274465) B3274465
theorem B4366763 : Blo 1291964 4366763 := bstep (se 1 (by rfl) ⟨3275072, by rfl⟩ : syracuseStep 4366763 = 6550145) B6550145
theorem B9323113 : Blo 1291964 9323113 := bstep (se 2 (by rfl) ⟨3496167, by rfl⟩ : syracuseStep 9323113 = 6992335) B6992335
theorem B20964035 : Blo 1291964 20964035 := bstep (se 1 (by rfl) ⟨15723026, by rfl⟩ : syracuseStep 20964035 = 31446053) B31446053
theorem B11051801 : Blo 1291964 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B2909375 : Blo 1291964 2909375 := bstep (se 1 (by rfl) ⟨2182031, by rfl⟩ : syracuseStep 2909375 = 4364063) B4364063
theorem B13264087 : Blo 1291964 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B4908539 : Blo 1291964 4908539 := bstep (se 1 (by rfl) ⟨3681404, by rfl⟩ : syracuseStep 4908539 = 7362809) B7362809
theorem B20973239 : Blo 1291964 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B31475425 : Blo 1291964 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B2910023 : Blo 1291964 2910023 := bstep (se 1 (by rfl) ⟨2182517, by rfl⟩ : syracuseStep 2910023 = 4365035) B4365035
theorem B2181019 : Blo 1291964 2181019 := bstep (se 1 (by rfl) ⟨1635764, by rfl⟩ : syracuseStep 2181019 = 3271529) B3271529
theorem B41920415 : Blo 1291964 41920415 := bstep (se 1 (by rfl) ⟨31440311, by rfl⟩ : syracuseStep 41920415 = 62880623) B62880623
theorem B27944939 : Blo 1291964 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B10479617 : Blo 1291964 10479617 := bstep (se 2 (by rfl) ⟨3929856, by rfl⟩ : syracuseStep 10479617 = 7859713) B7859713
theorem B4663403 : Blo 1291964 4663403 := bstep (se 1 (by rfl) ⟨3497552, by rfl⟩ : syracuseStep 4663403 = 6995105) B6995105
theorem B2910383 : Blo 1291964 2910383 := bstep (se 1 (by rfl) ⟨2182787, by rfl⟩ : syracuseStep 2910383 = 4365575) B4365575
theorem B2910635 : Blo 1291964 2910635 := bstep (se 1 (by rfl) ⟨2182976, by rfl⟩ : syracuseStep 2910635 = 4365953) B4365953
theorem B80710267 : Blo 1291964 80710267 := bstep (se 1 (by rfl) ⟨60532700, by rfl⟩ : syracuseStep 80710267 = 121065401) B121065401
theorem B7359119 : Blo 1291964 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B2182025 : Blo 1291964 2182025 := bstep (se 2 (by rfl) ⟨818259, by rfl⟩ : syracuseStep 2182025 = 1636519) B1636519
theorem B10488955 : Blo 1291964 10488955 := bstep (se 1 (by rfl) ⟨7866716, by rfl⟩ : syracuseStep 10488955 = 15733433) B15733433
theorem B2182457 : Blo 1291964 2182457 := bstep (se 2 (by rfl) ⟨818421, by rfl⟩ : syracuseStep 2182457 = 1636843) B1636843
theorem B5524841 : Blo 1291964 5524841 := bstep (se 2 (by rfl) ⟨2071815, by rfl⟩ : syracuseStep 5524841 = 4143631) B4143631
theorem B4361633 : Blo 1291964 4361633 := bstep (se 2 (by rfl) ⟨1635612, by rfl⟩ : syracuseStep 4361633 = 3271225) B3271225
theorem B3681769 : Blo 1291964 3681769 := bstep (se 2 (by rfl) ⟨1380663, by rfl⟩ : syracuseStep 3681769 = 2761327) B2761327
theorem B4362011 : Blo 1291964 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B6549335 : Blo 1291964 6549335 := bstep (se 1 (by rfl) ⟨4912001, by rfl⟩ : syracuseStep 6549335 = 9824003) B9824003
theorem B75550583 : Blo 1291964 75550583 := bstep (se 1 (by rfl) ⟨56662937, by rfl⟩ : syracuseStep 75550583 = 113325875) B113325875
theorem B6549497 : Blo 1291964 6549497 := bstep (se 2 (by rfl) ⟨2456061, by rfl⟩ : syracuseStep 6549497 = 4912123) B4912123
theorem B4911137 : Blo 1291964 4911137 := bstep (se 2 (by rfl) ⟨1841676, by rfl⟩ : syracuseStep 4911137 = 3683353) B3683353
theorem B2330707 : Blo 1291964 2330707 := bstep (se 1 (by rfl) ⟨1748030, by rfl⟩ : syracuseStep 2330707 = 3496061) B3496061
theorem B6549659 : Blo 1291964 6549659 := bstep (se 1 (by rfl) ⟨4912244, by rfl⟩ : syracuseStep 6549659 = 9824489) B9824489
theorem B1454287 : Blo 1291964 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B2183375 : Blo 1291964 2183375 := bstep (se 1 (by rfl) ⟨1637531, by rfl⟩ : syracuseStep 2183375 = 3275063) B3275063
theorem B4722907 : Blo 1291964 4722907 := bstep (se 1 (by rfl) ⟨3542180, by rfl⟩ : syracuseStep 4722907 = 7084361) B7084361
theorem B3272987 : Blo 1291964 3272987 := bstep (se 1 (by rfl) ⟨2454740, by rfl⟩ : syracuseStep 3272987 = 4909481) B4909481
theorem B4911455 : Blo 1291964 4911455 := bstep (se 1 (by rfl) ⟨3683591, by rfl⟩ : syracuseStep 4911455 = 7367183) B7367183
theorem B4485739 : Blo 1291964 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B11801213 : Blo 1291964 11801213 := bstep (se 3 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 11801213 = 4425455) B4425455
theorem B4362983 : Blo 1291964 4362983 := bstep (se 1 (by rfl) ⟨3272237, by rfl⟩ : syracuseStep 4362983 = 6544475) B6544475
theorem B2069483 : Blo 1291964 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B4912109 : Blo 1291964 4912109 := bstep (se 3 (by rfl) ⟨921020, by rfl⟩ : syracuseStep 4912109 = 1842041) B1842041
theorem B1938473 : Blo 1291964 1938473 := bstep (se 2 (by rfl) ⟨726927, by rfl⟩ : syracuseStep 1938473 = 1453855) B1453855
theorem B2454695 : Blo 1291964 2454695 := bstep (se 1 (by rfl) ⟨1841021, by rfl⟩ : syracuseStep 2454695 = 3682043) B3682043
theorem B9319799 : Blo 1291964 9319799 := bstep (se 1 (by rfl) ⟨6989849, by rfl⟩ : syracuseStep 9319799 = 13979699) B13979699
theorem B1635815 : Blo 1291964 1635815 := bstep (se 1 (by rfl) ⟨1226861, by rfl⟩ : syracuseStep 1635815 = 2453723) B2453723
theorem B1938971 : Blo 1291964 1938971 := bstep (se 1 (by rfl) ⟨1454228, by rfl⟩ : syracuseStep 1938971 = 2908457) B2908457
theorem B6993503 : Blo 1291964 6993503 := bstep (se 1 (by rfl) ⟨5245127, by rfl⟩ : syracuseStep 6993503 = 10490255) B10490255
theorem B1939151 : Blo 1291964 1939151 := bstep (se 1 (by rfl) ⟨1454363, by rfl⟩ : syracuseStep 1939151 = 2908727) B2908727
theorem B16570169 : Blo 1291964 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B14940011 : Blo 1291964 14940011 := bstep (se 1 (by rfl) ⟨11205008, by rfl⟩ : syracuseStep 14940011 = 22410017) B22410017
theorem B4364171 : Blo 1291964 4364171 := bstep (se 1 (by rfl) ⟨3273128, by rfl⟩ : syracuseStep 4364171 = 6546257) B6546257
theorem B1939391 : Blo 1291964 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B1292283 : Blo 1291964 1292283 := bstep (se 1 (by rfl) ⟨969212, by rfl⟩ : syracuseStep 1292283 = 1938425) B1938425
theorem B1292415 : Blo 1291964 1292415 := bstep (se 1 (by rfl) ⟨969311, by rfl⟩ : syracuseStep 1292415 = 1938623) B1938623
theorem B6543503 : Blo 1291964 6543503 := bstep (se 1 (by rfl) ⟨4907627, by rfl⟩ : syracuseStep 6543503 = 9815255) B9815255
theorem B22075577 : Blo 1291964 22075577 := bstep (se 2 (by rfl) ⟨8278341, by rfl⟩ : syracuseStep 22075577 = 16556683) B16556683
theorem B1292511 : Blo 1291964 1292511 := bstep (se 1 (by rfl) ⟨969383, by rfl⟩ : syracuseStep 1292511 = 1938767) B1938767
theorem B1939679 : Blo 1291964 1939679 := bstep (se 1 (by rfl) ⟨1454759, by rfl⟩ : syracuseStep 1939679 = 2909519) B2909519
theorem B1292571 : Blo 1291964 1292571 := bstep (se 1 (by rfl) ⟨969428, by rfl⟩ : syracuseStep 1292571 = 1938857) B1938857
theorem B1939739 : Blo 1291964 1939739 := bstep (se 1 (by rfl) ⟨1454804, by rfl⟩ : syracuseStep 1939739 = 2909609) B2909609
theorem B1292607 : Blo 1291964 1292607 := bstep (se 1 (by rfl) ⟨969455, by rfl⟩ : syracuseStep 1292607 = 1938911) B1938911
theorem B1292671 : Blo 1291964 1292671 := bstep (se 1 (by rfl) ⟨969503, by rfl⟩ : syracuseStep 1292671 = 1939007) B1939007
theorem B2070983 : Blo 1291964 2070983 := bstep (se 1 (by rfl) ⟨1553237, by rfl⟩ : syracuseStep 2070983 = 3106475) B3106475
theorem B17693225 : Blo 1291964 17693225 := bstep (se 2 (by rfl) ⟨6634959, by rfl⟩ : syracuseStep 17693225 = 13269919) B13269919
theorem B4364927 : Blo 1291964 4364927 := bstep (se 1 (by rfl) ⟨3273695, by rfl⟩ : syracuseStep 4364927 = 6547391) B6547391
theorem B1292991 : Blo 1291964 1292991 := bstep (se 1 (by rfl) ⟨969743, by rfl⟩ : syracuseStep 1292991 = 1939487) B1939487
theorem B1940159 : Blo 1291964 1940159 := bstep (se 1 (by rfl) ⟨1455119, by rfl⟩ : syracuseStep 1940159 = 2910239) B2910239
theorem B4037447 : Blo 1291964 4037447 := bstep (se 1 (by rfl) ⟨3028085, by rfl⟩ : syracuseStep 4037447 = 6056171) B6056171
theorem B2907017 : Blo 1291964 2907017 := bstep (se 2 (by rfl) ⟨1090131, by rfl⟩ : syracuseStep 2907017 = 2180263) B2180263
theorem B2620351 : Blo 1291964 2620351 := bstep (se 1 (by rfl) ⟨1965263, by rfl⟩ : syracuseStep 2620351 = 3930527) B3930527
theorem B1293279 : Blo 1291964 1293279 := bstep (se 1 (by rfl) ⟨969959, by rfl⟩ : syracuseStep 1293279 = 1939919) B1939919
theorem B1293339 : Blo 1291964 1293339 := bstep (se 1 (by rfl) ⟨970004, by rfl⟩ : syracuseStep 1293339 = 1940009) B1940009
theorem B1293479 : Blo 1291964 1293479 := bstep (se 1 (by rfl) ⟨970109, by rfl⟩ : syracuseStep 1293479 = 1940219) B1940219
theorem B2907323 : Blo 1291964 2907323 := bstep (se 1 (by rfl) ⟨2180492, by rfl⟩ : syracuseStep 2907323 = 4360985) B4360985
theorem B2907359 : Blo 1291964 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B1940711 : Blo 1291964 1940711 := bstep (se 1 (by rfl) ⟨1455533, by rfl⟩ : syracuseStep 1940711 = 2911067) B2911067
theorem B1293563 : Blo 1291964 1293563 := bstep (se 1 (by rfl) ⟨970172, by rfl⟩ : syracuseStep 1293563 = 1940345) B1940345
theorem B2907575 : Blo 1291964 2907575 := bstep (se 1 (by rfl) ⟨2180681, by rfl⟩ : syracuseStep 2907575 = 4361363) B4361363
theorem B10477507 : Blo 1291964 10477507 := bstep (se 1 (by rfl) ⟨7858130, by rfl⟩ : syracuseStep 10477507 = 15716261) B15716261
theorem B4366439 : Blo 1291964 4366439 := bstep (se 1 (by rfl) ⟨3274829, by rfl⟩ : syracuseStep 4366439 = 6549659) B6549659
theorem B13976023 : Blo 1291964 13976023 := bstep (se 1 (by rfl) ⟨10482017, by rfl⟩ : syracuseStep 13976023 = 20964035) B20964035
theorem B2908655 : Blo 1291964 2908655 := bstep (se 1 (by rfl) ⟨2181491, by rfl⟩ : syracuseStep 2908655 = 4362983) B4362983
theorem B5980985 : Blo 1291964 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B4662335 : Blo 1291964 4662335 := bstep (se 1 (by rfl) ⟨3496751, by rfl⟩ : syracuseStep 4662335 = 6993503) B6993503
theorem B2909447 : Blo 1291964 2909447 := bstep (se 1 (by rfl) ⟨2182085, by rfl⟩ : syracuseStep 2909447 = 4364171) B4364171
theorem B13985273 : Blo 1291964 13985273 := bstep (se 2 (by rfl) ⟨5244477, by rfl⟩ : syracuseStep 13985273 = 10488955) B10488955
theorem B2909951 : Blo 1291964 2909951 := bstep (se 1 (by rfl) ⟨2182463, by rfl⟩ : syracuseStep 2909951 = 4364927) B4364927
theorem B4909025 : Blo 1291964 4909025 := bstep (se 2 (by rfl) ⟨1840884, by rfl⟩ : syracuseStep 4909025 = 3681769) B3681769
theorem B50367055 : Blo 1291964 50367055 := bstep (se 1 (by rfl) ⟨37775291, by rfl⟩ : syracuseStep 50367055 = 75550583) B75550583
theorem B13970009 : Blo 1291964 13970009 := bstep (se 2 (by rfl) ⟨5238753, by rfl⟩ : syracuseStep 13970009 = 10477507) B10477507
theorem B3107609 : Blo 1291964 3107609 := bstep (se 2 (by rfl) ⟨1165353, by rfl⟩ : syracuseStep 3107609 = 2330707) B2330707
theorem B2181991 : Blo 1291964 2181991 := bstep (se 1 (by rfl) ⟨1636493, by rfl⟩ : syracuseStep 2181991 = 3272987) B3272987
theorem B2911175 : Blo 1291964 2911175 := bstep (se 1 (by rfl) ⟨2183381, by rfl⟩ : syracuseStep 2911175 = 4366763) B4366763
theorem B7867475 : Blo 1291964 7867475 := bstep (se 1 (by rfl) ⟨5900606, by rfl⟩ : syracuseStep 7867475 = 11801213) B11801213
theorem B7367867 : Blo 1291964 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B12430817 : Blo 1291964 12430817 := bstep (se 2 (by rfl) ⟨4661556, by rfl⟩ : syracuseStep 12430817 = 9323113) B9323113
theorem B107613689 : Blo 1291964 107613689 := bstep (se 2 (by rfl) ⟨40355133, by rfl⟩ : syracuseStep 107613689 = 80710267) B80710267
theorem B6213199 : Blo 1291964 6213199 := bstep (se 1 (by rfl) ⟨4659899, by rfl⟩ : syracuseStep 6213199 = 9319799) B9319799
theorem B3272359 : Blo 1291964 3272359 := bstep (se 1 (by rfl) ⟨2454269, by rfl⟩ : syracuseStep 3272359 = 4908539) B4908539
theorem B11046779 : Blo 1291964 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B3493801 : Blo 1291964 3493801 := bstep (se 2 (by rfl) ⟨1310175, by rfl⟩ : syracuseStep 3493801 = 2620351) B2620351
theorem B4362173 : Blo 1291964 4362173 := bstep (se 3 (by rfl) ⟨817907, by rfl⟩ : syracuseStep 4362173 = 1635815) B1635815
theorem B27946943 : Blo 1291964 27946943 := bstep (se 1 (by rfl) ⟨20960207, by rfl⟩ : syracuseStep 27946943 = 41920415) B41920415
theorem B3108935 : Blo 1291964 3108935 := bstep (se 1 (by rfl) ⟨2331701, by rfl⟩ : syracuseStep 3108935 = 4663403) B4663403
theorem B4362335 : Blo 1291964 4362335 := bstep (se 1 (by rfl) ⟨3271751, by rfl⟩ : syracuseStep 4362335 = 6543503) B6543503
theorem B14717051 : Blo 1291964 14717051 := bstep (se 1 (by rfl) ⟨11037788, by rfl⟩ : syracuseStep 14717051 = 22075577) B22075577
theorem B1380655 : Blo 1291964 1380655 := bstep (se 1 (by rfl) ⟨1035491, by rfl⟩ : syracuseStep 1380655 = 2070983) B2070983
theorem B2691631 : Blo 1291964 2691631 := bstep (se 1 (by rfl) ⟨2018723, by rfl⟩ : syracuseStep 2691631 = 4037447) B4037447
theorem B1938011 : Blo 1291964 1938011 := bstep (se 1 (by rfl) ⟨1453508, by rfl⟩ : syracuseStep 1938011 = 2907017) B2907017
theorem B1454683 : Blo 1291964 1454683 := bstep (se 1 (by rfl) ⟨1091012, by rfl⟩ : syracuseStep 1454683 = 2182025) B2182025
theorem B1938215 : Blo 1291964 1938215 := bstep (se 1 (by rfl) ⟨1453661, by rfl⟩ : syracuseStep 1938215 = 2907323) B2907323
theorem B1938239 : Blo 1291964 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B1454971 : Blo 1291964 1454971 := bstep (se 1 (by rfl) ⟨1091228, by rfl⟩ : syracuseStep 1454971 = 2182457) B2182457
theorem B3683227 : Blo 1291964 3683227 := bstep (se 1 (by rfl) ⟨2762420, by rfl⟩ : syracuseStep 3683227 = 5524841) B5524841
theorem B1938383 : Blo 1291964 1938383 := bstep (se 1 (by rfl) ⟨1453787, by rfl⟩ : syracuseStep 1938383 = 2907575) B2907575
theorem B5518621 : Blo 1291964 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B74519837 : Blo 1291964 74519837 := bstep (se 3 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 74519837 = 27944939) B27944939
theorem B3274091 : Blo 1291964 3274091 := bstep (se 1 (by rfl) ⟨2455568, by rfl⟩ : syracuseStep 3274091 = 4911137) B4911137
theorem B1455583 : Blo 1291964 1455583 := bstep (se 1 (by rfl) ⟨1091687, by rfl⟩ : syracuseStep 1455583 = 2183375) B2183375
theorem B3274303 : Blo 1291964 3274303 := bstep (se 1 (by rfl) ⟨2455727, by rfl⟩ : syracuseStep 3274303 = 4911455) B4911455
theorem B1939049 : Blo 1291964 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B6297209 : Blo 1291964 6297209 := bstep (se 2 (by rfl) ⟨2361453, by rfl⟩ : syracuseStep 6297209 = 4722907) B4722907
theorem B3274739 : Blo 1291964 3274739 := bstep (se 1 (by rfl) ⟨2456054, by rfl⟩ : syracuseStep 3274739 = 4912109) B4912109
theorem B1292315 : Blo 1291964 1292315 := bstep (se 1 (by rfl) ⟨969236, by rfl⟩ : syracuseStep 1292315 = 1938473) B1938473
theorem B1636463 : Blo 1291964 1636463 := bstep (se 1 (by rfl) ⟨1227347, by rfl⟩ : syracuseStep 1636463 = 2454695) B2454695
theorem B1939583 : Blo 1291964 1939583 := bstep (se 1 (by rfl) ⟨1454687, by rfl⟩ : syracuseStep 1939583 = 2909375) B2909375
theorem B1292647 : Blo 1291964 1292647 := bstep (se 1 (by rfl) ⟨969485, by rfl⟩ : syracuseStep 1292647 = 1938971) B1938971
theorem B13982159 : Blo 1291964 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B1292767 : Blo 1291964 1292767 := bstep (se 1 (by rfl) ⟨969575, by rfl⟩ : syracuseStep 1292767 = 1939151) B1939151
theorem B1940015 : Blo 1291964 1940015 := bstep (se 1 (by rfl) ⟨1455011, by rfl⟩ : syracuseStep 1940015 = 2910023) B2910023
theorem B9960007 : Blo 1291964 9960007 := bstep (se 1 (by rfl) ⟨7470005, by rfl⟩ : syracuseStep 9960007 = 14940011) B14940011
theorem B1292927 : Blo 1291964 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B6986411 : Blo 1291964 6986411 := bstep (se 1 (by rfl) ⟨5239808, by rfl⟩ : syracuseStep 6986411 = 10479617) B10479617
theorem B1940255 : Blo 1291964 1940255 := bstep (se 1 (by rfl) ⟨1455191, by rfl⟩ : syracuseStep 1940255 = 2910383) B2910383
theorem B1293119 : Blo 1291964 1293119 := bstep (se 1 (by rfl) ⟨969839, by rfl⟩ : syracuseStep 1293119 = 1939679) B1939679
theorem B1293159 : Blo 1291964 1293159 := bstep (se 1 (by rfl) ⟨969869, by rfl⟩ : syracuseStep 1293159 = 1939739) B1939739
theorem B1940423 : Blo 1291964 1940423 := bstep (se 1 (by rfl) ⟨1455317, by rfl⟩ : syracuseStep 1940423 = 2910635) B2910635
theorem B17685449 : Blo 1291964 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B11795483 : Blo 1291964 11795483 := bstep (se 1 (by rfl) ⟨8846612, by rfl⟩ : syracuseStep 11795483 = 17693225) B17693225
theorem B4906079 : Blo 1291964 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B1293439 : Blo 1291964 1293439 := bstep (se 1 (by rfl) ⟨970079, by rfl⟩ : syracuseStep 1293439 = 1940159) B1940159
theorem B1293807 : Blo 1291964 1293807 := bstep (se 1 (by rfl) ⟨970355, by rfl⟩ : syracuseStep 1293807 = 1940711) B1940711
theorem B2907755 : Blo 1291964 2907755 := bstep (se 1 (by rfl) ⟨2180816, by rfl⟩ : syracuseStep 2907755 = 4361633) B4361633
theorem B41967233 : Blo 1291964 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B2908007 : Blo 1291964 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B2908025 : Blo 1291964 2908025 := bstep (se 2 (by rfl) ⟨1090509, by rfl⟩ : syracuseStep 2908025 = 2181019) B2181019
theorem B4366223 : Blo 1291964 4366223 := bstep (se 1 (by rfl) ⟨3274667, by rfl⟩ : syracuseStep 4366223 = 6549335) B6549335
theorem B4366331 : Blo 1291964 4366331 := bstep (se 1 (by rfl) ⟨3274748, by rfl⟩ : syracuseStep 4366331 = 6549497) B6549497
theorem B2072623 : Blo 1291964 2072623 := bstep (se 1 (by rfl) ⟨1554467, by rfl⟩ : syracuseStep 2072623 = 3108935) B3108935
theorem B2908223 : Blo 1291964 2908223 := bstep (se 1 (by rfl) ⟨2181167, by rfl⟩ : syracuseStep 2908223 = 4362335) B4362335
theorem B13280009 : Blo 1291964 13280009 := bstep (se 2 (by rfl) ⟨4980003, by rfl⟩ : syracuseStep 13280009 = 9960007) B9960007
theorem B9323515 : Blo 1291964 9323515 := bstep (se 1 (by rfl) ⟨6992636, by rfl⟩ : syracuseStep 9323515 = 13985273) B13985273
theorem B2909321 : Blo 1291964 2909321 := bstep (se 2 (by rfl) ⟨1090995, by rfl⟩ : syracuseStep 2909321 = 2181991) B2181991
theorem B7358161 : Blo 1291964 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B11790299 : Blo 1291964 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B5244983 : Blo 1291964 5244983 := bstep (se 1 (by rfl) ⟨3933737, by rfl⟩ : syracuseStep 5244983 = 7867475) B7867475
theorem B3270719 : Blo 1291964 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B8284265 : Blo 1291964 8284265 := bstep (se 2 (by rfl) ⟨3106599, by rfl⟩ : syracuseStep 8284265 = 6213199) B6213199
theorem B27978155 : Blo 1291964 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B2910815 : Blo 1291964 2910815 := bstep (se 1 (by rfl) ⟨2183111, by rfl⟩ : syracuseStep 2910815 = 4366223) B4366223
theorem B18631295 : Blo 1291964 18631295 := bstep (se 1 (by rfl) ⟨13973471, by rfl⟩ : syracuseStep 18631295 = 27946943) B27946943
theorem B2910887 : Blo 1291964 2910887 := bstep (se 1 (by rfl) ⟨2183165, by rfl⟩ : syracuseStep 2910887 = 4366331) B4366331
theorem B2910959 : Blo 1291964 2910959 := bstep (se 1 (by rfl) ⟨2183219, by rfl⟩ : syracuseStep 2910959 = 4366439) B4366439
theorem B14355365 : Blo 1291964 14355365 := bstep (se 4 (by rfl) ⟨1345815, by rfl⟩ : syracuseStep 14355365 = 2691631) B2691631
theorem B3108223 : Blo 1291964 3108223 := bstep (se 1 (by rfl) ⟨2331167, by rfl⟩ : syracuseStep 3108223 = 4662335) B4662335
theorem B49679891 : Blo 1291964 49679891 := bstep (se 1 (by rfl) ⟨37259918, by rfl⟩ : syracuseStep 49679891 = 74519837) B74519837
theorem B2182727 : Blo 1291964 2182727 := bstep (se 1 (by rfl) ⟨1637045, by rfl⟩ : syracuseStep 2182727 = 3274091) B3274091
theorem B4198139 : Blo 1291964 4198139 := bstep (se 1 (by rfl) ⟨3148604, by rfl⟩ : syracuseStep 4198139 = 6297209) B6297209
theorem B4910969 : Blo 1291964 4910969 := bstep (se 2 (by rfl) ⟨1841613, by rfl⟩ : syracuseStep 4910969 = 3683227) B3683227
theorem B3272683 : Blo 1291964 3272683 := bstep (se 1 (by rfl) ⟨2454512, by rfl⟩ : syracuseStep 3272683 = 4909025) B4909025
theorem B286969837 : Blo 1291964 286969837 := bstep (se 3 (by rfl) ⟨53806844, by rfl⟩ : syracuseStep 286969837 = 107613689) B107613689
theorem B2183159 : Blo 1291964 2183159 := bstep (se 1 (by rfl) ⟨1637369, by rfl⟩ : syracuseStep 2183159 = 3274739) B3274739
theorem B37253357 : Blo 1291964 37253357 := bstep (se 3 (by rfl) ⟨6985004, by rfl⟩ : syracuseStep 37253357 = 13970009) B13970009
theorem B4657607 : Blo 1291964 4657607 := bstep (se 1 (by rfl) ⟨3493205, by rfl⟩ : syracuseStep 4657607 = 6986411) B6986411
theorem B4911911 : Blo 1291964 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B4363145 : Blo 1291964 4363145 := bstep (se 2 (by rfl) ⟨1636179, by rfl⟩ : syracuseStep 4363145 = 3272359) B3272359
theorem B8287211 : Blo 1291964 8287211 := bstep (se 1 (by rfl) ⟨6215408, by rfl⟩ : syracuseStep 8287211 = 12430817) B12430817
theorem B1938503 : Blo 1291964 1938503 := bstep (se 1 (by rfl) ⟨1453877, by rfl⟩ : syracuseStep 1938503 = 2907755) B2907755
theorem B4658401 : Blo 1291964 4658401 := bstep (se 2 (by rfl) ⟨1746900, by rfl⟩ : syracuseStep 4658401 = 3493801) B3493801
theorem B1938671 : Blo 1291964 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B1938683 : Blo 1291964 1938683 := bstep (se 1 (by rfl) ⟨1454012, by rfl⟩ : syracuseStep 1938683 = 2908025) B2908025
theorem B9811367 : Blo 1291964 9811367 := bstep (se 1 (by rfl) ⟨7358525, by rfl⟩ : syracuseStep 9811367 = 14717051) B14717051
theorem B4363901 : Blo 1291964 4363901 := bstep (se 3 (by rfl) ⟨818231, by rfl⟩ : syracuseStep 4363901 = 1636463) B1636463
theorem B1939103 : Blo 1291964 1939103 := bstep (se 1 (by rfl) ⟨1454327, by rfl⟩ : syracuseStep 1939103 = 2908655) B2908655
theorem B1292007 : Blo 1291964 1292007 := bstep (se 1 (by rfl) ⟨969005, by rfl⟩ : syracuseStep 1292007 = 1938011) B1938011
theorem B1292143 : Blo 1291964 1292143 := bstep (se 1 (by rfl) ⟨969107, by rfl⟩ : syracuseStep 1292143 = 1938215) B1938215
theorem B3987323 : Blo 1291964 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B1292159 : Blo 1291964 1292159 := bstep (se 1 (by rfl) ⟨969119, by rfl⟩ : syracuseStep 1292159 = 1938239) B1938239
theorem B18634697 : Blo 1291964 18634697 := bstep (se 2 (by rfl) ⟨6988011, by rfl⟩ : syracuseStep 18634697 = 13976023) B13976023
theorem B1292255 : Blo 1291964 1292255 := bstep (se 1 (by rfl) ⟨969191, by rfl⟩ : syracuseStep 1292255 = 1938383) B1938383
theorem B67156073 : Blo 1291964 67156073 := bstep (se 2 (by rfl) ⟨25183527, by rfl⟩ : syracuseStep 67156073 = 50367055) B50367055
theorem B1939577 : Blo 1291964 1939577 := bstep (se 2 (by rfl) ⟨727341, by rfl⟩ : syracuseStep 1939577 = 1454683) B1454683
theorem B1939631 : Blo 1291964 1939631 := bstep (se 1 (by rfl) ⟨1454723, by rfl⟩ : syracuseStep 1939631 = 2909447) B2909447
theorem B1292699 : Blo 1291964 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B1939961 : Blo 1291964 1939961 := bstep (se 2 (by rfl) ⟨727485, by rfl⟩ : syracuseStep 1939961 = 1454971) B1454971
theorem B1939967 : Blo 1291964 1939967 := bstep (se 1 (by rfl) ⟨1454975, by rfl⟩ : syracuseStep 1939967 = 2909951) B2909951
theorem B1293055 : Blo 1291964 1293055 := bstep (se 1 (by rfl) ⟨969791, by rfl⟩ : syracuseStep 1293055 = 1939583) B1939583
theorem B7363493 : Blo 1291964 7363493 := bstep (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) B1380655
theorem B9321439 : Blo 1291964 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B1293343 : Blo 1291964 1293343 := bstep (se 1 (by rfl) ⟨970007, by rfl⟩ : syracuseStep 1293343 = 1940015) B1940015
theorem B2071739 : Blo 1291964 2071739 := bstep (se 1 (by rfl) ⟨1553804, by rfl⟩ : syracuseStep 2071739 = 3107609) B3107609
theorem B1293503 : Blo 1291964 1293503 := bstep (se 1 (by rfl) ⟨970127, by rfl⟩ : syracuseStep 1293503 = 1940255) B1940255
theorem B1940777 : Blo 1291964 1940777 := bstep (se 2 (by rfl) ⟨727791, by rfl⟩ : syracuseStep 1940777 = 1455583) B1455583
theorem B1293615 : Blo 1291964 1293615 := bstep (se 1 (by rfl) ⟨970211, by rfl⟩ : syracuseStep 1293615 = 1940423) B1940423
theorem B1940783 : Blo 1291964 1940783 := bstep (se 1 (by rfl) ⟨1455587, by rfl⟩ : syracuseStep 1940783 = 2911175) B2911175
theorem B7863655 : Blo 1291964 7863655 := bstep (se 1 (by rfl) ⟨5897741, by rfl⟩ : syracuseStep 7863655 = 11795483) B11795483
theorem B4365737 : Blo 1291964 4365737 := bstep (se 2 (by rfl) ⟨1637151, by rfl⟩ : syracuseStep 4365737 = 3274303) B3274303
theorem B7364519 : Blo 1291964 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B2908115 : Blo 1291964 2908115 := bstep (se 1 (by rfl) ⟨2181086, by rfl⟩ : syracuseStep 2908115 = 4362173) B4362173
theorem B3105071 : Blo 1291964 3105071 := bstep (se 1 (by rfl) ⟨2328803, by rfl⟩ : syracuseStep 3105071 = 4657607) B4657607
theorem B2908763 : Blo 1291964 2908763 := bstep (se 1 (by rfl) ⟨2181572, by rfl⟩ : syracuseStep 2908763 = 4363145) B4363145
theorem B2909267 : Blo 1291964 2909267 := bstep (se 1 (by rfl) ⟨2181950, by rfl⟩ : syracuseStep 2909267 = 4363901) B4363901
theorem B12428585 : Blo 1291964 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B2180479 : Blo 1291964 2180479 := bstep (se 1 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 2180479 = 3270719) B3270719
theorem B44770715 : Blo 1291964 44770715 := bstep (se 1 (by rfl) ⟨33578036, by rfl⟩ : syracuseStep 44770715 = 67156073) B67156073
theorem B5522843 : Blo 1291964 5522843 := bstep (se 1 (by rfl) ⟨4142132, by rfl⟩ : syracuseStep 5522843 = 8284265) B8284265
theorem B6211201 : Blo 1291964 6211201 := bstep (se 2 (by rfl) ⟨2329200, by rfl⟩ : syracuseStep 6211201 = 4658401) B4658401
theorem B12420863 : Blo 1291964 12420863 := bstep (se 1 (by rfl) ⟨9315647, by rfl⟩ : syracuseStep 12420863 = 18631295) B18631295
theorem B4908995 : Blo 1291964 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B2910491 : Blo 1291964 2910491 := bstep (se 1 (by rfl) ⟨2182868, by rfl⟩ : syracuseStep 2910491 = 4365737) B4365737
theorem B4909679 : Blo 1291964 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B382626449 : Blo 1291964 382626449 := bstep (se 2 (by rfl) ⟨143484918, by rfl⟩ : syracuseStep 382626449 = 286969837) B286969837
theorem B2763497 : Blo 1291964 2763497 := bstep (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) B2072623
theorem B5524807 : Blo 1291964 5524807 := bstep (se 1 (by rfl) ⟨4143605, by rfl⟩ : syracuseStep 5524807 = 8287211) B8287211
theorem B6540911 : Blo 1291964 6540911 := bstep (se 1 (by rfl) ⟨4905683, by rfl⟩ : syracuseStep 6540911 = 9811367) B9811367
theorem B2658215 : Blo 1291964 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B12423131 : Blo 1291964 12423131 := bstep (se 1 (by rfl) ⟨9317348, by rfl⟩ : syracuseStep 12423131 = 18634697) B18634697
theorem B7860199 : Blo 1291964 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B12431353 : Blo 1291964 12431353 := bstep (se 2 (by rfl) ⟨4661757, by rfl⟩ : syracuseStep 12431353 = 9323515) B9323515
theorem B1381159 : Blo 1291964 1381159 := bstep (se 1 (by rfl) ⟨1035869, by rfl⟩ : syracuseStep 1381159 = 2071739) B2071739
theorem B9810881 : Blo 1291964 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B1455151 : Blo 1291964 1455151 := bstep (se 1 (by rfl) ⟨1091363, by rfl⟩ : syracuseStep 1455151 = 2182727) B2182727
theorem B2798759 : Blo 1291964 2798759 := bstep (se 1 (by rfl) ⟨2099069, by rfl⟩ : syracuseStep 2798759 = 4198139) B4198139
theorem B3273979 : Blo 1291964 3273979 := bstep (se 1 (by rfl) ⟨2455484, by rfl⟩ : syracuseStep 3273979 = 4910969) B4910969
theorem B1938743 : Blo 1291964 1938743 := bstep (se 1 (by rfl) ⟨1454057, by rfl⟩ : syracuseStep 1938743 = 2908115) B2908115
theorem B4363577 : Blo 1291964 4363577 := bstep (se 2 (by rfl) ⟨1636341, by rfl⟩ : syracuseStep 4363577 = 3272683) B3272683
theorem B1455439 : Blo 1291964 1455439 := bstep (se 1 (by rfl) ⟨1091579, by rfl⟩ : syracuseStep 1455439 = 2183159) B2183159
theorem B1938815 : Blo 1291964 1938815 := bstep (se 1 (by rfl) ⟨1454111, by rfl⟩ : syracuseStep 1938815 = 2908223) B2908223
theorem B24835571 : Blo 1291964 24835571 := bstep (se 1 (by rfl) ⟨18626678, by rfl⟩ : syracuseStep 24835571 = 37253357) B37253357
theorem B3274607 : Blo 1291964 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B1292335 : Blo 1291964 1292335 := bstep (se 1 (by rfl) ⟨969251, by rfl⟩ : syracuseStep 1292335 = 1938503) B1938503
theorem B1939547 : Blo 1291964 1939547 := bstep (se 1 (by rfl) ⟨1454660, by rfl⟩ : syracuseStep 1939547 = 2909321) B2909321
theorem B1292447 : Blo 1291964 1292447 := bstep (se 1 (by rfl) ⟨969335, by rfl⟩ : syracuseStep 1292447 = 1938671) B1938671
theorem B1292455 : Blo 1291964 1292455 := bstep (se 1 (by rfl) ⟨969341, by rfl⟩ : syracuseStep 1292455 = 1938683) B1938683
theorem B1292735 : Blo 1291964 1292735 := bstep (se 1 (by rfl) ⟨969551, by rfl⟩ : syracuseStep 1292735 = 1939103) B1939103
theorem B3496655 : Blo 1291964 3496655 := bstep (se 1 (by rfl) ⟨2622491, by rfl⟩ : syracuseStep 3496655 = 5244983) B5244983
theorem B1293051 : Blo 1291964 1293051 := bstep (se 1 (by rfl) ⟨969788, by rfl⟩ : syracuseStep 1293051 = 1939577) B1939577
theorem B1293087 : Blo 1291964 1293087 := bstep (se 1 (by rfl) ⟨969815, by rfl⟩ : syracuseStep 1293087 = 1939631) B1939631
theorem B18652103 : Blo 1291964 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B1293307 : Blo 1291964 1293307 := bstep (se 1 (by rfl) ⟨969980, by rfl⟩ : syracuseStep 1293307 = 1939961) B1939961
theorem B1293311 : Blo 1291964 1293311 := bstep (se 1 (by rfl) ⟨969983, by rfl⟩ : syracuseStep 1293311 = 1939967) B1939967
theorem B1940543 : Blo 1291964 1940543 := bstep (se 1 (by rfl) ⟨1455407, by rfl⟩ : syracuseStep 1940543 = 2910815) B2910815
theorem B1940591 : Blo 1291964 1940591 := bstep (se 1 (by rfl) ⟨1455443, by rfl⟩ : syracuseStep 1940591 = 2910887) B2910887
theorem B10484873 : Blo 1291964 10484873 := bstep (se 2 (by rfl) ⟨3931827, by rfl⟩ : syracuseStep 10484873 = 7863655) B7863655
theorem B1940639 : Blo 1291964 1940639 := bstep (se 1 (by rfl) ⟨1455479, by rfl⟩ : syracuseStep 1940639 = 2910959) B2910959
theorem B4144297 : Blo 1291964 4144297 := bstep (se 2 (by rfl) ⟨1554111, by rfl⟩ : syracuseStep 4144297 = 3108223) B3108223
theorem B35413357 : Blo 1291964 35413357 := bstep (se 3 (by rfl) ⟨6640004, by rfl⟩ : syracuseStep 35413357 = 13280009) B13280009
theorem B1293851 : Blo 1291964 1293851 := bstep (se 1 (by rfl) ⟨970388, by rfl⟩ : syracuseStep 1293851 = 1940777) B1940777
theorem B1293855 : Blo 1291964 1293855 := bstep (se 1 (by rfl) ⟨970391, by rfl⟩ : syracuseStep 1293855 = 1940783) B1940783
theorem B33119927 : Blo 1291964 33119927 := bstep (se 1 (by rfl) ⟨24839945, by rfl⟩ : syracuseStep 33119927 = 49679891) B49679891
theorem B38280973 : Blo 1291964 38280973 := bstep (se 3 (by rfl) ⟨7177682, by rfl⟩ : syracuseStep 38280973 = 14355365) B14355365
theorem B2909051 : Blo 1291964 2909051 := bstep (se 1 (by rfl) ⟨2181788, by rfl⟩ : syracuseStep 2909051 = 4363577) B4363577
theorem B16557047 : Blo 1291964 16557047 := bstep (se 1 (by rfl) ⟨12417785, by rfl⟩ : syracuseStep 16557047 = 24835571) B24835571
theorem B7366409 : Blo 1291964 7366409 := bstep (se 2 (by rfl) ⟨2762403, by rfl⟩ : syracuseStep 7366409 = 5524807) B5524807
theorem B255084299 : Blo 1291964 255084299 := bstep (se 1 (by rfl) ⟨191313224, by rfl⟩ : syracuseStep 255084299 = 382626449) B382626449
theorem B6989915 : Blo 1291964 6989915 := bstep (se 1 (by rfl) ⟨5242436, by rfl⟩ : syracuseStep 6989915 = 10484873) B10484873
theorem B4360607 : Blo 1291964 4360607 := bstep (se 1 (by rfl) ⟨3270455, by rfl⟩ : syracuseStep 4360607 = 6540911) B6540911
theorem B7088573 : Blo 1291964 7088573 := bstep (se 3 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 7088573 = 2658215) B2658215
theorem B22079951 : Blo 1291964 22079951 := bstep (se 1 (by rfl) ⟨16559963, by rfl⟩ : syracuseStep 22079951 = 33119927) B33119927
theorem B10480265 : Blo 1291964 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B16575137 : Blo 1291964 16575137 := bstep (se 2 (by rfl) ⟨6215676, by rfl⟩ : syracuseStep 16575137 = 12431353) B12431353
theorem B6540587 : Blo 1291964 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B8285723 : Blo 1291964 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B29847143 : Blo 1291964 29847143 := bstep (se 1 (by rfl) ⟨22385357, by rfl⟩ : syracuseStep 29847143 = 44770715) B44770715
theorem B3681895 : Blo 1291964 3681895 := bstep (se 1 (by rfl) ⟨2761421, by rfl⟩ : syracuseStep 3681895 = 5522843) B5522843
theorem B2183071 : Blo 1291964 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B3272663 : Blo 1291964 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B5525729 : Blo 1291964 5525729 := bstep (se 2 (by rfl) ⟨2072148, by rfl⟩ : syracuseStep 5525729 = 4144297) B4144297
theorem B3273119 : Blo 1291964 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B2331103 : Blo 1291964 2331103 := bstep (se 1 (by rfl) ⟨1748327, by rfl⟩ : syracuseStep 2331103 = 3496655) B3496655
theorem B7369325 : Blo 1291964 7369325 := bstep (se 3 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 7369325 = 2763497) B2763497
theorem B51041297 : Blo 1291964 51041297 := bstep (se 2 (by rfl) ⟨19140486, by rfl⟩ : syracuseStep 51041297 = 38280973) B38280973
theorem B2070047 : Blo 1291964 2070047 := bstep (se 1 (by rfl) ⟨1552535, by rfl⟩ : syracuseStep 2070047 = 3105071) B3105071
theorem B1939175 : Blo 1291964 1939175 := bstep (se 1 (by rfl) ⟨1454381, by rfl⟩ : syracuseStep 1939175 = 2908763) B2908763
theorem B1939511 : Blo 1291964 1939511 := bstep (se 1 (by rfl) ⟨1454633, by rfl⟩ : syracuseStep 1939511 = 2909267) B2909267
theorem B1865839 : Blo 1291964 1865839 := bstep (se 1 (by rfl) ⟨1399379, by rfl⟩ : syracuseStep 1865839 = 2798759) B2798759
theorem B1292495 : Blo 1291964 1292495 := bstep (se 1 (by rfl) ⟨969371, by rfl⟩ : syracuseStep 1292495 = 1938743) B1938743
theorem B1292543 : Blo 1291964 1292543 := bstep (se 1 (by rfl) ⟨969407, by rfl⟩ : syracuseStep 1292543 = 1938815) B1938815
theorem B1841545 : Blo 1291964 1841545 := bstep (se 2 (by rfl) ⟨690579, by rfl⟩ : syracuseStep 1841545 = 1381159) B1381159
theorem B8280575 : Blo 1291964 8280575 := bstep (se 1 (by rfl) ⟨6210431, by rfl⟩ : syracuseStep 8280575 = 12420863) B12420863
theorem B1293031 : Blo 1291964 1293031 := bstep (se 1 (by rfl) ⟨969773, by rfl⟩ : syracuseStep 1293031 = 1939547) B1939547
theorem B1940201 : Blo 1291964 1940201 := bstep (se 2 (by rfl) ⟨727575, by rfl⟩ : syracuseStep 1940201 = 1455151) B1455151
theorem B1940327 : Blo 1291964 1940327 := bstep (se 1 (by rfl) ⟨1455245, by rfl⟩ : syracuseStep 1940327 = 2910491) B2910491
theorem B4365305 : Blo 1291964 4365305 := bstep (se 2 (by rfl) ⟨1636989, by rfl⟩ : syracuseStep 4365305 = 3273979) B3273979
theorem B1940585 : Blo 1291964 1940585 := bstep (se 2 (by rfl) ⟨727719, by rfl⟩ : syracuseStep 1940585 = 1455439) B1455439
theorem B47217809 : Blo 1291964 47217809 := bstep (se 2 (by rfl) ⟨17706678, by rfl⟩ : syracuseStep 47217809 = 35413357) B35413357
theorem B2907305 : Blo 1291964 2907305 := bstep (se 2 (by rfl) ⟨1090239, by rfl⟩ : syracuseStep 2907305 = 2180479) B2180479
theorem B12434735 : Blo 1291964 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B1293695 : Blo 1291964 1293695 := bstep (se 1 (by rfl) ⟨970271, by rfl⟩ : syracuseStep 1293695 = 1940543) B1940543
theorem B1293727 : Blo 1291964 1293727 := bstep (se 1 (by rfl) ⟨970295, by rfl⟩ : syracuseStep 1293727 = 1940591) B1940591
theorem B1293759 : Blo 1291964 1293759 := bstep (se 1 (by rfl) ⟨970319, by rfl⟩ : syracuseStep 1293759 = 1940639) B1940639
theorem B8281601 : Blo 1291964 8281601 := bstep (se 2 (by rfl) ⟨3105600, by rfl⟩ : syracuseStep 8281601 = 6211201) B6211201
theorem B8282087 : Blo 1291964 8282087 := bstep (se 1 (by rfl) ⟨6211565, by rfl⟩ : syracuseStep 8282087 = 12423131) B12423131
theorem B136110125 : Blo 1291964 136110125 := bstep (se 3 (by rfl) ⟨25520648, by rfl⟩ : syracuseStep 136110125 = 51041297) B51041297
theorem B2910203 : Blo 1291964 2910203 := bstep (se 1 (by rfl) ⟨2182652, by rfl⟩ : syracuseStep 2910203 = 4365305) B4365305
theorem B4909193 : Blo 1291964 4909193 := bstep (se 2 (by rfl) ⟨1840947, by rfl⟩ : syracuseStep 4909193 = 3681895) B3681895
theorem B4360391 : Blo 1291964 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B5523815 : Blo 1291964 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B2910761 : Blo 1291964 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B2181775 : Blo 1291964 2181775 := bstep (se 1 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 2181775 = 3272663) B3272663
theorem B2182079 : Blo 1291964 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B3108137 : Blo 1291964 3108137 := bstep (se 2 (by rfl) ⟨1165551, by rfl⟩ : syracuseStep 3108137 = 2331103) B2331103
theorem B11038031 : Blo 1291964 11038031 := bstep (se 1 (by rfl) ⟨8278523, by rfl⟩ : syracuseStep 11038031 = 16557047) B16557047
theorem B4910939 : Blo 1291964 4910939 := bstep (se 1 (by rfl) ⟨3683204, by rfl⟩ : syracuseStep 4910939 = 7366409) B7366409
theorem B31478539 : Blo 1291964 31478539 := bstep (se 1 (by rfl) ⟨23608904, by rfl⟩ : syracuseStep 31478539 = 47217809) B47217809
theorem B1938203 : Blo 1291964 1938203 := bstep (se 1 (by rfl) ⟨1453652, by rfl⟩ : syracuseStep 1938203 = 2907305) B2907305
theorem B2487785 : Blo 1291964 2487785 := bstep (se 2 (by rfl) ⟨932919, by rfl⟩ : syracuseStep 2487785 = 1865839) B1865839
theorem B3683819 : Blo 1291964 3683819 := bstep (se 1 (by rfl) ⟨2762864, by rfl⟩ : syracuseStep 3683819 = 5525729) B5525729
theorem B4912883 : Blo 1291964 4912883 := bstep (se 1 (by rfl) ⟨3684662, by rfl⟩ : syracuseStep 4912883 = 7369325) B7369325
theorem B1939367 : Blo 1291964 1939367 := bstep (se 1 (by rfl) ⟨1454525, by rfl⟩ : syracuseStep 1939367 = 2909051) B2909051
theorem B33159293 : Blo 1291964 33159293 := bstep (se 3 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 33159293 = 12434735) B12434735
theorem B1292783 : Blo 1291964 1292783 := bstep (se 1 (by rfl) ⟨969587, by rfl⟩ : syracuseStep 1292783 = 1939175) B1939175
theorem B170056199 : Blo 1291964 170056199 := bstep (se 1 (by rfl) ⟨127542149, by rfl⟩ : syracuseStep 170056199 = 255084299) B255084299
theorem B1293007 : Blo 1291964 1293007 := bstep (se 1 (by rfl) ⟨969755, by rfl⟩ : syracuseStep 1293007 = 1939511) B1939511
theorem B4659943 : Blo 1291964 4659943 := bstep (se 1 (by rfl) ⟨3494957, by rfl⟩ : syracuseStep 4659943 = 6989915) B6989915
theorem B5520125 : Blo 1291964 5520125 := bstep (se 3 (by rfl) ⟨1035023, by rfl⟩ : syracuseStep 5520125 = 2070047) B2070047
theorem B79592381 : Blo 1291964 79592381 := bstep (se 3 (by rfl) ⟨14923571, by rfl⟩ : syracuseStep 79592381 = 29847143) B29847143
theorem B2907071 : Blo 1291964 2907071 := bstep (se 1 (by rfl) ⟨2180303, by rfl⟩ : syracuseStep 2907071 = 4360607) B4360607
theorem B4725715 : Blo 1291964 4725715 := bstep (se 1 (by rfl) ⟨3544286, by rfl⟩ : syracuseStep 4725715 = 7088573) B7088573
theorem B14719967 : Blo 1291964 14719967 := bstep (se 1 (by rfl) ⟨11039975, by rfl⟩ : syracuseStep 14719967 = 22079951) B22079951
theorem B5520383 : Blo 1291964 5520383 := bstep (se 1 (by rfl) ⟨4140287, by rfl⟩ : syracuseStep 5520383 = 8280575) B8280575
theorem B6986843 : Blo 1291964 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B11050091 : Blo 1291964 11050091 := bstep (se 1 (by rfl) ⟨8287568, by rfl⟩ : syracuseStep 11050091 = 16575137) B16575137
theorem B1293467 : Blo 1291964 1293467 := bstep (se 1 (by rfl) ⟨970100, by rfl⟩ : syracuseStep 1293467 = 1940201) B1940201
theorem B1293551 : Blo 1291964 1293551 := bstep (se 1 (by rfl) ⟨970163, by rfl⟩ : syracuseStep 1293551 = 1940327) B1940327
theorem B9821573 : Blo 1291964 9821573 := bstep (se 4 (by rfl) ⟨920772, by rfl⟩ : syracuseStep 9821573 = 1841545) B1841545
theorem B1293723 : Blo 1291964 1293723 := bstep (se 1 (by rfl) ⟨970292, by rfl⟩ : syracuseStep 1293723 = 1940585) B1940585
theorem B5521067 : Blo 1291964 5521067 := bstep (se 1 (by rfl) ⟨4140800, by rfl⟩ : syracuseStep 5521067 = 8281601) B8281601
theorem B5521391 : Blo 1291964 5521391 := bstep (se 1 (by rfl) ⟨4141043, by rfl⟩ : syracuseStep 5521391 = 8282087) B8282087
theorem B2909033 : Blo 1291964 2909033 := bstep (se 2 (by rfl) ⟨1090887, by rfl⟩ : syracuseStep 2909033 = 2181775) B2181775
theorem B14730173 : Blo 1291964 14730173 := bstep (se 3 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 14730173 = 5523815) B5523815
theorem B6300953 : Blo 1291964 6300953 := bstep (se 2 (by rfl) ⟨2362857, by rfl⟩ : syracuseStep 6300953 = 4725715) B4725715
theorem B9823517 : Blo 1291964 9823517 := bstep (se 3 (by rfl) ⟨1841909, by rfl⟩ : syracuseStep 9823517 = 3683819) B3683819
theorem B113370799 : Blo 1291964 113370799 := bstep (se 1 (by rfl) ⟨85028099, by rfl⟩ : syracuseStep 113370799 = 170056199) B170056199
theorem B3680083 : Blo 1291964 3680083 := bstep (se 1 (by rfl) ⟨2760062, by rfl⟩ : syracuseStep 3680083 = 5520125) B5520125
theorem B53061587 : Blo 1291964 53061587 := bstep (se 1 (by rfl) ⟨39796190, by rfl⟩ : syracuseStep 53061587 = 79592381) B79592381
theorem B3680255 : Blo 1291964 3680255 := bstep (se 1 (by rfl) ⟨2760191, by rfl⟩ : syracuseStep 3680255 = 5520383) B5520383
theorem B7366727 : Blo 1291964 7366727 := bstep (se 1 (by rfl) ⟨5525045, by rfl⟩ : syracuseStep 7366727 = 11050091) B11050091
theorem B7358687 : Blo 1291964 7358687 := bstep (se 1 (by rfl) ⟨5519015, by rfl⟩ : syracuseStep 7358687 = 11038031) B11038031
theorem B6547715 : Blo 1291964 6547715 := bstep (se 1 (by rfl) ⟨4910786, by rfl⟩ : syracuseStep 6547715 = 9821573) B9821573
theorem B3680711 : Blo 1291964 3680711 := bstep (se 1 (by rfl) ⟨2760533, by rfl⟩ : syracuseStep 3680711 = 5521067) B5521067
theorem B3680927 : Blo 1291964 3680927 := bstep (se 1 (by rfl) ⟨2760695, by rfl⟩ : syracuseStep 3680927 = 5521391) B5521391
theorem B6213257 : Blo 1291964 6213257 := bstep (se 2 (by rfl) ⟨2329971, by rfl⟩ : syracuseStep 6213257 = 4659943) B4659943
theorem B41971385 : Blo 1291964 41971385 := bstep (se 2 (by rfl) ⟨15739269, by rfl⟩ : syracuseStep 41971385 = 31478539) B31478539
theorem B22106195 : Blo 1291964 22106195 := bstep (se 1 (by rfl) ⟨16579646, by rfl⟩ : syracuseStep 22106195 = 33159293) B33159293
theorem B3272795 : Blo 1291964 3272795 := bstep (se 1 (by rfl) ⟨2454596, by rfl⟩ : syracuseStep 3272795 = 4909193) B4909193
theorem B1938047 : Blo 1291964 1938047 := bstep (se 1 (by rfl) ⟨1453535, by rfl⟩ : syracuseStep 1938047 = 2907071) B2907071
theorem B1454719 : Blo 1291964 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B4657895 : Blo 1291964 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B3273959 : Blo 1291964 3273959 := bstep (se 1 (by rfl) ⟨2455469, by rfl⟩ : syracuseStep 3273959 = 4910939) B4910939
theorem B90740083 : Blo 1291964 90740083 := bstep (se 1 (by rfl) ⟨68055062, by rfl⟩ : syracuseStep 90740083 = 136110125) B136110125
theorem B1292135 : Blo 1291964 1292135 := bstep (se 1 (by rfl) ⟨969101, by rfl⟩ : syracuseStep 1292135 = 1938203) B1938203
theorem B8288365 : Blo 1291964 8288365 := bstep (se 3 (by rfl) ⟨1554068, by rfl⟩ : syracuseStep 8288365 = 3108137) B3108137
theorem B3275255 : Blo 1291964 3275255 := bstep (se 1 (by rfl) ⟨2456441, by rfl⟩ : syracuseStep 3275255 = 4912883) B4912883
theorem B6634093 : Blo 1291964 6634093 := bstep (se 3 (by rfl) ⟨1243892, by rfl⟩ : syracuseStep 6634093 = 2487785) B2487785
theorem B1292911 : Blo 1291964 1292911 := bstep (se 1 (by rfl) ⟨969683, by rfl⟩ : syracuseStep 1292911 = 1939367) B1939367
theorem B1940135 : Blo 1291964 1940135 := bstep (se 1 (by rfl) ⟨1455101, by rfl⟩ : syracuseStep 1940135 = 2910203) B2910203
theorem B2906927 : Blo 1291964 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B1940507 : Blo 1291964 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B9813311 : Blo 1291964 9813311 := bstep (se 1 (by rfl) ⟨7359983, by rfl⟩ : syracuseStep 9813311 = 14719967) B14719967
theorem B14737463 : Blo 1291964 14737463 := bstep (se 1 (by rfl) ⟨11053097, by rfl⟩ : syracuseStep 14737463 = 22106195) B22106195
theorem B11051153 : Blo 1291964 11051153 := bstep (se 2 (by rfl) ⟨4144182, by rfl⟩ : syracuseStep 11051153 = 8288365) B8288365
theorem B3105263 : Blo 1291964 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B35374391 : Blo 1291964 35374391 := bstep (se 1 (by rfl) ⟨26530793, by rfl⟩ : syracuseStep 35374391 = 53061587) B53061587
theorem B151161065 : Blo 1291964 151161065 := bstep (se 2 (by rfl) ⟨56685399, by rfl⟩ : syracuseStep 151161065 = 113370799) B113370799
theorem B2181863 : Blo 1291964 2181863 := bstep (se 1 (by rfl) ⟨1636397, by rfl⟩ : syracuseStep 2181863 = 3272795) B3272795
theorem B2182639 : Blo 1291964 2182639 := bstep (se 1 (by rfl) ⟨1636979, by rfl⟩ : syracuseStep 2182639 = 3273959) B3273959
theorem B6549011 : Blo 1291964 6549011 := bstep (se 1 (by rfl) ⟨4911758, by rfl⟩ : syracuseStep 6549011 = 9823517) B9823517
theorem B2453503 : Blo 1291964 2453503 := bstep (se 1 (by rfl) ⟨1840127, by rfl⟩ : syracuseStep 2453503 = 3680255) B3680255
theorem B4911151 : Blo 1291964 4911151 := bstep (se 1 (by rfl) ⟨3683363, by rfl⟩ : syracuseStep 4911151 = 7366727) B7366727
theorem B2453807 : Blo 1291964 2453807 := bstep (se 1 (by rfl) ⟨1840355, by rfl⟩ : syracuseStep 2453807 = 3680711) B3680711
theorem B2183503 : Blo 1291964 2183503 := bstep (se 1 (by rfl) ⟨1637627, by rfl⟩ : syracuseStep 2183503 = 3275255) B3275255
theorem B2453951 : Blo 1291964 2453951 := bstep (se 1 (by rfl) ⟨1840463, by rfl⟩ : syracuseStep 2453951 = 3680927) B3680927
theorem B1937951 : Blo 1291964 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B6542207 : Blo 1291964 6542207 := bstep (se 1 (by rfl) ⟨4906655, by rfl⟩ : syracuseStep 6542207 = 9813311) B9813311
theorem B4142171 : Blo 1291964 4142171 := bstep (se 1 (by rfl) ⟨3106628, by rfl⟩ : syracuseStep 4142171 = 6213257) B6213257
theorem B27980923 : Blo 1291964 27980923 := bstep (se 1 (by rfl) ⟨20985692, by rfl⟩ : syracuseStep 27980923 = 41971385) B41971385
theorem B1292031 : Blo 1291964 1292031 := bstep (se 1 (by rfl) ⟨969023, by rfl⟩ : syracuseStep 1292031 = 1938047) B1938047
theorem B1939355 : Blo 1291964 1939355 := bstep (se 1 (by rfl) ⟨1454516, by rfl⟩ : syracuseStep 1939355 = 2909033) B2909033
theorem B9820115 : Blo 1291964 9820115 := bstep (se 1 (by rfl) ⟨7365086, by rfl⟩ : syracuseStep 9820115 = 14730173) B14730173
theorem B8845457 : Blo 1291964 8845457 := bstep (se 2 (by rfl) ⟨3317046, by rfl⟩ : syracuseStep 8845457 = 6634093) B6634093
theorem B1939625 : Blo 1291964 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B4200635 : Blo 1291964 4200635 := bstep (se 1 (by rfl) ⟨3150476, by rfl⟩ : syracuseStep 4200635 = 6300953) B6300953
theorem B4905791 : Blo 1291964 4905791 := bstep (se 1 (by rfl) ⟨3679343, by rfl⟩ : syracuseStep 4905791 = 7358687) B7358687
theorem B4365143 : Blo 1291964 4365143 := bstep (se 1 (by rfl) ⟨3273857, by rfl⟩ : syracuseStep 4365143 = 6547715) B6547715
theorem B1293423 : Blo 1291964 1293423 := bstep (se 1 (by rfl) ⟨970067, by rfl⟩ : syracuseStep 1293423 = 1940135) B1940135
theorem B120986777 : Blo 1291964 120986777 := bstep (se 2 (by rfl) ⟨45370041, by rfl⟩ : syracuseStep 120986777 = 90740083) B90740083
theorem B1293671 : Blo 1291964 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B4906777 : Blo 1291964 4906777 := bstep (se 2 (by rfl) ⟨1840041, by rfl⟩ : syracuseStep 4906777 = 3680083) B3680083
theorem B2761447 : Blo 1291964 2761447 := bstep (se 1 (by rfl) ⟨2071085, by rfl⟩ : syracuseStep 2761447 = 4142171) B4142171
theorem B6546743 : Blo 1291964 6546743 := bstep (se 1 (by rfl) ⟨4910057, by rfl⟩ : syracuseStep 6546743 = 9820115) B9820115
theorem B37307897 : Blo 1291964 37307897 := bstep (se 2 (by rfl) ⟨13990461, by rfl⟩ : syracuseStep 37307897 = 27980923) B27980923
theorem B3270527 : Blo 1291964 3270527 := bstep (se 1 (by rfl) ⟨2452895, by rfl⟩ : syracuseStep 3270527 = 4905791) B4905791
theorem B2910095 : Blo 1291964 2910095 := bstep (se 1 (by rfl) ⟨2182571, by rfl⟩ : syracuseStep 2910095 = 4365143) B4365143
theorem B2910185 : Blo 1291964 2910185 := bstep (se 2 (by rfl) ⟨1091319, by rfl⟩ : syracuseStep 2910185 = 2182639) B2182639
theorem B3271337 : Blo 1291964 3271337 := bstep (se 2 (by rfl) ⟨1226751, by rfl⟩ : syracuseStep 3271337 = 2453503) B2453503
theorem B9824975 : Blo 1291964 9824975 := bstep (se 1 (by rfl) ⟨7368731, by rfl⟩ : syracuseStep 9824975 = 14737463) B14737463
theorem B6548201 : Blo 1291964 6548201 := bstep (se 2 (by rfl) ⟨2455575, by rfl⟩ : syracuseStep 6548201 = 4911151) B4911151
theorem B7367435 : Blo 1291964 7367435 := bstep (se 1 (by rfl) ⟨5525576, by rfl⟩ : syracuseStep 7367435 = 11051153) B11051153
theorem B23587885 : Blo 1291964 23587885 := bstep (se 3 (by rfl) ⟨4422728, by rfl⟩ : syracuseStep 23587885 = 8845457) B8845457
theorem B2911337 : Blo 1291964 2911337 := bstep (se 2 (by rfl) ⟨1091751, by rfl⟩ : syracuseStep 2911337 = 2183503) B2183503
theorem B4361471 : Blo 1291964 4361471 := bstep (se 1 (by rfl) ⟨3271103, by rfl⟩ : syracuseStep 4361471 = 6542207) B6542207
theorem B100774043 : Blo 1291964 100774043 := bstep (se 1 (by rfl) ⟨75580532, by rfl⟩ : syracuseStep 100774043 = 151161065) B151161065
theorem B1454575 : Blo 1291964 1454575 := bstep (se 1 (by rfl) ⟨1090931, by rfl⟩ : syracuseStep 1454575 = 2181863) B2181863
theorem B6542369 : Blo 1291964 6542369 := bstep (se 2 (by rfl) ⟨2453388, by rfl⟩ : syracuseStep 6542369 = 4906777) B4906777
theorem B1635871 : Blo 1291964 1635871 := bstep (se 1 (by rfl) ⟨1226903, by rfl⟩ : syracuseStep 1635871 = 2453807) B2453807
theorem B1635967 : Blo 1291964 1635967 := bstep (se 1 (by rfl) ⟨1226975, by rfl⟩ : syracuseStep 1635967 = 2453951) B2453951
theorem B1291967 : Blo 1291964 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B23582927 : Blo 1291964 23582927 := bstep (se 1 (by rfl) ⟨17687195, by rfl⟩ : syracuseStep 23582927 = 35374391) B35374391
theorem B1292903 : Blo 1291964 1292903 := bstep (se 1 (by rfl) ⟨969677, by rfl⟩ : syracuseStep 1292903 = 1939355) B1939355
theorem B8280701 : Blo 1291964 8280701 := bstep (se 3 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 8280701 = 3105263) B3105263
theorem B1293083 : Blo 1291964 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B2800423 : Blo 1291964 2800423 := bstep (se 1 (by rfl) ⟨2100317, by rfl⟩ : syracuseStep 2800423 = 4200635) B4200635
theorem B80657851 : Blo 1291964 80657851 := bstep (se 1 (by rfl) ⟨60493388, by rfl⟩ : syracuseStep 80657851 = 120986777) B120986777
theorem B4366007 : Blo 1291964 4366007 := bstep (se 1 (by rfl) ⟨3274505, by rfl⟩ : syracuseStep 4366007 = 6549011) B6549011
theorem B67182695 : Blo 1291964 67182695 := bstep (se 1 (by rfl) ⟨50387021, by rfl⟩ : syracuseStep 67182695 = 100774043) B100774043
theorem B24871931 : Blo 1291964 24871931 := bstep (se 1 (by rfl) ⟨18653948, by rfl⟩ : syracuseStep 24871931 = 37307897) B37307897
theorem B2180351 : Blo 1291964 2180351 := bstep (se 1 (by rfl) ⟨1635263, by rfl⟩ : syracuseStep 2180351 = 3270527) B3270527
theorem B31450513 : Blo 1291964 31450513 := bstep (se 2 (by rfl) ⟨11793942, by rfl⟩ : syracuseStep 31450513 = 23587885) B23587885
theorem B15721951 : Blo 1291964 15721951 := bstep (se 1 (by rfl) ⟨11791463, by rfl⟩ : syracuseStep 15721951 = 23582927) B23582927
theorem B2180891 : Blo 1291964 2180891 := bstep (se 1 (by rfl) ⟨1635668, by rfl⟩ : syracuseStep 2180891 = 3271337) B3271337
theorem B2181161 : Blo 1291964 2181161 := bstep (se 2 (by rfl) ⟨817935, by rfl⟩ : syracuseStep 2181161 = 1635871) B1635871
theorem B2181289 : Blo 1291964 2181289 := bstep (se 2 (by rfl) ⟨817983, by rfl⟩ : syracuseStep 2181289 = 1635967) B1635967
theorem B2910671 : Blo 1291964 2910671 := bstep (se 1 (by rfl) ⟨2183003, by rfl⟩ : syracuseStep 2910671 = 4366007) B4366007
theorem B4361579 : Blo 1291964 4361579 := bstep (se 1 (by rfl) ⟨3271184, by rfl⟩ : syracuseStep 4361579 = 6542369) B6542369
theorem B3681929 : Blo 1291964 3681929 := bstep (se 2 (by rfl) ⟨1380723, by rfl⟩ : syracuseStep 3681929 = 2761447) B2761447
theorem B6549983 : Blo 1291964 6549983 := bstep (se 1 (by rfl) ⟨4912487, by rfl⟩ : syracuseStep 6549983 = 9824975) B9824975
theorem B4911623 : Blo 1291964 4911623 := bstep (se 1 (by rfl) ⟨3683717, by rfl⟩ : syracuseStep 4911623 = 7367435) B7367435
theorem B1939433 : Blo 1291964 1939433 := bstep (se 2 (by rfl) ⟨727287, by rfl⟩ : syracuseStep 1939433 = 1454575) B1454575
theorem B4364495 : Blo 1291964 4364495 := bstep (se 1 (by rfl) ⟨3273371, by rfl⟩ : syracuseStep 4364495 = 6546743) B6546743
theorem B3733897 : Blo 1291964 3733897 := bstep (se 2 (by rfl) ⟨1400211, by rfl⟩ : syracuseStep 3733897 = 2800423) B2800423
theorem B1940063 : Blo 1291964 1940063 := bstep (se 1 (by rfl) ⟨1455047, by rfl⟩ : syracuseStep 1940063 = 2910095) B2910095
theorem B1940123 : Blo 1291964 1940123 := bstep (se 1 (by rfl) ⟨1455092, by rfl⟩ : syracuseStep 1940123 = 2910185) B2910185
theorem B5520467 : Blo 1291964 5520467 := bstep (se 1 (by rfl) ⟨4140350, by rfl⟩ : syracuseStep 5520467 = 8280701) B8280701
theorem B4365467 : Blo 1291964 4365467 := bstep (se 1 (by rfl) ⟨3274100, by rfl⟩ : syracuseStep 4365467 = 6548201) B6548201
theorem B107543801 : Blo 1291964 107543801 := bstep (se 2 (by rfl) ⟨40328925, by rfl⟩ : syracuseStep 107543801 = 80657851) B80657851
theorem B1940891 : Blo 1291964 1940891 := bstep (se 1 (by rfl) ⟨1455668, by rfl⟩ : syracuseStep 1940891 = 2911337) B2911337
theorem B2907647 : Blo 1291964 2907647 := bstep (se 1 (by rfl) ⟨2180735, by rfl⟩ : syracuseStep 2907647 = 4361471) B4361471
theorem B2908385 : Blo 1291964 2908385 := bstep (se 2 (by rfl) ⟨1090644, by rfl⟩ : syracuseStep 2908385 = 2181289) B2181289
theorem B4366655 : Blo 1291964 4366655 := bstep (se 1 (by rfl) ⟨3274991, by rfl⟩ : syracuseStep 4366655 = 6549983) B6549983
theorem B16581287 : Blo 1291964 16581287 := bstep (se 1 (by rfl) ⟨12435965, by rfl⟩ : syracuseStep 16581287 = 24871931) B24871931
theorem B2909663 : Blo 1291964 2909663 := bstep (se 1 (by rfl) ⟨2182247, by rfl⟩ : syracuseStep 2909663 = 4364495) B4364495
theorem B3680311 : Blo 1291964 3680311 := bstep (se 1 (by rfl) ⟨2760233, by rfl⟩ : syracuseStep 3680311 = 5520467) B5520467
theorem B2910311 : Blo 1291964 2910311 := bstep (se 1 (by rfl) ⟨2182733, by rfl⟩ : syracuseStep 2910311 = 4365467) B4365467
theorem B44788463 : Blo 1291964 44788463 := bstep (se 1 (by rfl) ⟨33591347, by rfl⟩ : syracuseStep 44788463 = 67182695) B67182695
theorem B1453567 : Blo 1291964 1453567 := bstep (se 1 (by rfl) ⟨1090175, by rfl⟩ : syracuseStep 1453567 = 2180351) B2180351
theorem B1453927 : Blo 1291964 1453927 := bstep (se 1 (by rfl) ⟨1090445, by rfl⟩ : syracuseStep 1453927 = 2180891) B2180891
theorem B1454107 : Blo 1291964 1454107 := bstep (se 1 (by rfl) ⟨1090580, by rfl⟩ : syracuseStep 1454107 = 2181161) B2181161
theorem B1938431 : Blo 1291964 1938431 := bstep (se 1 (by rfl) ⟨1453823, by rfl⟩ : syracuseStep 1938431 = 2907647) B2907647
theorem B2454619 : Blo 1291964 2454619 := bstep (se 1 (by rfl) ⟨1840964, by rfl⟩ : syracuseStep 2454619 = 3681929) B3681929
theorem B3274415 : Blo 1291964 3274415 := bstep (se 1 (by rfl) ⟨2455811, by rfl⟩ : syracuseStep 3274415 = 4911623) B4911623
theorem B4978529 : Blo 1291964 4978529 := bstep (se 2 (by rfl) ⟨1866948, by rfl⟩ : syracuseStep 4978529 = 3733897) B3733897
theorem B1292955 : Blo 1291964 1292955 := bstep (se 1 (by rfl) ⟨969716, by rfl⟩ : syracuseStep 1292955 = 1939433) B1939433
theorem B1940447 : Blo 1291964 1940447 := bstep (se 1 (by rfl) ⟨1455335, by rfl⟩ : syracuseStep 1940447 = 2910671) B2910671
theorem B1293375 : Blo 1291964 1293375 := bstep (se 1 (by rfl) ⟨970031, by rfl⟩ : syracuseStep 1293375 = 1940063) B1940063
theorem B1293415 : Blo 1291964 1293415 := bstep (se 1 (by rfl) ⟨970061, by rfl⟩ : syracuseStep 1293415 = 1940123) B1940123
theorem B41934017 : Blo 1291964 41934017 := bstep (se 2 (by rfl) ⟨15725256, by rfl⟩ : syracuseStep 41934017 = 31450513) B31450513
theorem B20962601 : Blo 1291964 20962601 := bstep (se 2 (by rfl) ⟨7860975, by rfl⟩ : syracuseStep 20962601 = 15721951) B15721951
theorem B71695867 : Blo 1291964 71695867 := bstep (se 1 (by rfl) ⟨53771900, by rfl⟩ : syracuseStep 71695867 = 107543801) B107543801
theorem B2907719 : Blo 1291964 2907719 := bstep (se 1 (by rfl) ⟨2180789, by rfl⟩ : syracuseStep 2907719 = 4361579) B4361579
theorem B1293927 : Blo 1291964 1293927 := bstep (se 1 (by rfl) ⟨970445, by rfl⟩ : syracuseStep 1293927 = 1940891) B1940891
theorem B4907081 : Blo 1291964 4907081 := bstep (se 2 (by rfl) ⟨1840155, by rfl⟩ : syracuseStep 4907081 = 3680311) B3680311
theorem B3319019 : Blo 1291964 3319019 := bstep (se 1 (by rfl) ⟨2489264, by rfl⟩ : syracuseStep 3319019 = 4978529) B4978529
theorem B95594489 : Blo 1291964 95594489 := bstep (se 2 (by rfl) ⟨35847933, by rfl⟩ : syracuseStep 95594489 = 71695867) B71695867
theorem B2911103 : Blo 1291964 2911103 := bstep (se 1 (by rfl) ⟨2183327, by rfl⟩ : syracuseStep 2911103 = 4366655) B4366655
theorem B11054191 : Blo 1291964 11054191 := bstep (se 1 (by rfl) ⟨8290643, by rfl⟩ : syracuseStep 11054191 = 16581287) B16581287
theorem B2182943 : Blo 1291964 2182943 := bstep (se 1 (by rfl) ⟨1637207, by rfl⟩ : syracuseStep 2182943 = 3274415) B3274415
theorem B3272825 : Blo 1291964 3272825 := bstep (se 2 (by rfl) ⟨1227309, by rfl⟩ : syracuseStep 3272825 = 2454619) B2454619
theorem B1938089 : Blo 1291964 1938089 := bstep (se 2 (by rfl) ⟨726783, by rfl⟩ : syracuseStep 1938089 = 1453567) B1453567
theorem B27956011 : Blo 1291964 27956011 := bstep (se 1 (by rfl) ⟨20967008, by rfl⟩ : syracuseStep 27956011 = 41934017) B41934017
theorem B1938479 : Blo 1291964 1938479 := bstep (se 1 (by rfl) ⟨1453859, by rfl⟩ : syracuseStep 1938479 = 2907719) B2907719
theorem B1938569 : Blo 1291964 1938569 := bstep (se 2 (by rfl) ⟨726963, by rfl⟩ : syracuseStep 1938569 = 1453927) B1453927
theorem B1938809 : Blo 1291964 1938809 := bstep (se 2 (by rfl) ⟨727053, by rfl⟩ : syracuseStep 1938809 = 1454107) B1454107
theorem B1938923 : Blo 1291964 1938923 := bstep (se 1 (by rfl) ⟨1454192, by rfl⟩ : syracuseStep 1938923 = 2908385) B2908385
theorem B1292287 : Blo 1291964 1292287 := bstep (se 1 (by rfl) ⟨969215, by rfl⟩ : syracuseStep 1292287 = 1938431) B1938431
theorem B1939775 : Blo 1291964 1939775 := bstep (se 1 (by rfl) ⟨1454831, by rfl⟩ : syracuseStep 1939775 = 2909663) B2909663
theorem B1940207 : Blo 1291964 1940207 := bstep (se 1 (by rfl) ⟨1455155, by rfl⟩ : syracuseStep 1940207 = 2910311) B2910311
theorem B29858975 : Blo 1291964 29858975 := bstep (se 1 (by rfl) ⟨22394231, by rfl⟩ : syracuseStep 29858975 = 44788463) B44788463
theorem B1293631 : Blo 1291964 1293631 := bstep (se 1 (by rfl) ⟨970223, by rfl⟩ : syracuseStep 1293631 = 1940447) B1940447
theorem B13975067 : Blo 1291964 13975067 := bstep (se 1 (by rfl) ⟨10481300, by rfl⟩ : syracuseStep 13975067 = 20962601) B20962601
theorem B2212679 : Blo 1291964 2212679 := bstep (se 1 (by rfl) ⟨1659509, by rfl⟩ : syracuseStep 2212679 = 3319019) B3319019
theorem B37274681 : Blo 1291964 37274681 := bstep (se 2 (by rfl) ⟨13978005, by rfl⟩ : syracuseStep 37274681 = 27956011) B27956011
theorem B14738921 : Blo 1291964 14738921 := bstep (se 2 (by rfl) ⟨5527095, by rfl⟩ : syracuseStep 14738921 = 11054191) B11054191
theorem B9316711 : Blo 1291964 9316711 := bstep (se 1 (by rfl) ⟨6987533, by rfl⟩ : syracuseStep 9316711 = 13975067) B13975067
theorem B3271387 : Blo 1291964 3271387 := bstep (se 1 (by rfl) ⟨2453540, by rfl⟩ : syracuseStep 3271387 = 4907081) B4907081
theorem B2181883 : Blo 1291964 2181883 := bstep (se 1 (by rfl) ⟨1636412, by rfl⟩ : syracuseStep 2181883 = 3272825) B3272825
theorem B63729659 : Blo 1291964 63729659 := bstep (se 1 (by rfl) ⟨47797244, by rfl⟩ : syracuseStep 63729659 = 95594489) B95594489
theorem B1455295 : Blo 1291964 1455295 := bstep (se 1 (by rfl) ⟨1091471, by rfl⟩ : syracuseStep 1455295 = 2182943) B2182943
theorem B1292059 : Blo 1291964 1292059 := bstep (se 1 (by rfl) ⟨969044, by rfl⟩ : syracuseStep 1292059 = 1938089) B1938089
theorem B1292319 : Blo 1291964 1292319 := bstep (se 1 (by rfl) ⟨969239, by rfl⟩ : syracuseStep 1292319 = 1938479) B1938479
theorem B1292379 : Blo 1291964 1292379 := bstep (se 1 (by rfl) ⟨969284, by rfl⟩ : syracuseStep 1292379 = 1938569) B1938569
theorem B1292539 : Blo 1291964 1292539 := bstep (se 1 (by rfl) ⟨969404, by rfl⟩ : syracuseStep 1292539 = 1938809) B1938809
theorem B1292615 : Blo 1291964 1292615 := bstep (se 1 (by rfl) ⟨969461, by rfl⟩ : syracuseStep 1292615 = 1938923) B1938923
theorem B1293183 : Blo 1291964 1293183 := bstep (se 1 (by rfl) ⟨969887, by rfl⟩ : syracuseStep 1293183 = 1939775) B1939775
theorem B1293471 : Blo 1291964 1293471 := bstep (se 1 (by rfl) ⟨970103, by rfl⟩ : syracuseStep 1293471 = 1940207) B1940207
theorem B1940735 : Blo 1291964 1940735 := bstep (se 1 (by rfl) ⟨1455551, by rfl⟩ : syracuseStep 1940735 = 2911103) B2911103
theorem B19905983 : Blo 1291964 19905983 := bstep (se 1 (by rfl) ⟨14929487, by rfl⟩ : syracuseStep 19905983 = 29858975) B29858975
theorem B1475119 : Blo 1291964 1475119 := bstep (se 1 (by rfl) ⟨1106339, by rfl⟩ : syracuseStep 1475119 = 2212679) B2212679
theorem B2909177 : Blo 1291964 2909177 := bstep (se 2 (by rfl) ⟨1090941, by rfl⟩ : syracuseStep 2909177 = 2181883) B2181883
theorem B42486439 : Blo 1291964 42486439 := bstep (se 1 (by rfl) ⟨31864829, by rfl⟩ : syracuseStep 42486439 = 63729659) B63729659
theorem B12422281 : Blo 1291964 12422281 := bstep (se 2 (by rfl) ⟨4658355, by rfl⟩ : syracuseStep 12422281 = 9316711) B9316711
theorem B24849787 : Blo 1291964 24849787 := bstep (se 1 (by rfl) ⟨18637340, by rfl⟩ : syracuseStep 24849787 = 37274681) B37274681
theorem B4361849 : Blo 1291964 4361849 := bstep (se 2 (by rfl) ⟨1635693, by rfl⟩ : syracuseStep 4361849 = 3271387) B3271387
theorem B9825947 : Blo 1291964 9825947 := bstep (se 1 (by rfl) ⟨7369460, by rfl⟩ : syracuseStep 9825947 = 14738921) B14738921
theorem B1940393 : Blo 1291964 1940393 := bstep (se 2 (by rfl) ⟨727647, by rfl⟩ : syracuseStep 1940393 = 1455295) B1455295
theorem B1293823 : Blo 1291964 1293823 := bstep (se 1 (by rfl) ⟨970367, by rfl⟩ : syracuseStep 1293823 = 1940735) B1940735
theorem B13270655 : Blo 1291964 13270655 := bstep (se 1 (by rfl) ⟨9952991, by rfl⟩ : syracuseStep 13270655 = 19905983) B19905983
theorem B1966825 : Blo 1291964 1966825 := bstep (se 2 (by rfl) ⟨737559, by rfl⟩ : syracuseStep 1966825 = 1475119) B1475119
theorem B56648585 : Blo 1291964 56648585 := bstep (se 2 (by rfl) ⟨21243219, by rfl⟩ : syracuseStep 56648585 = 42486439) B42486439
theorem B33133049 : Blo 1291964 33133049 := bstep (se 2 (by rfl) ⟨12424893, by rfl⟩ : syracuseStep 33133049 = 24849787) B24849787
theorem B6550631 : Blo 1291964 6550631 := bstep (se 1 (by rfl) ⟨4912973, by rfl⟩ : syracuseStep 6550631 = 9825947) B9825947
theorem B1939451 : Blo 1291964 1939451 := bstep (se 1 (by rfl) ⟨1454588, by rfl⟩ : syracuseStep 1939451 = 2909177) B2909177
theorem B16563041 : Blo 1291964 16563041 := bstep (se 2 (by rfl) ⟨6211140, by rfl⟩ : syracuseStep 16563041 = 12422281) B12422281
theorem B1293595 : Blo 1291964 1293595 := bstep (se 1 (by rfl) ⟨970196, by rfl⟩ : syracuseStep 1293595 = 1940393) B1940393
theorem B2907899 : Blo 1291964 2907899 := bstep (se 1 (by rfl) ⟨2180924, by rfl⟩ : syracuseStep 2907899 = 4361849) B4361849
theorem B8847103 : Blo 1291964 8847103 := bstep (se 1 (by rfl) ⟨6635327, by rfl⟩ : syracuseStep 8847103 = 13270655) B13270655
theorem B4367087 : Blo 1291964 4367087 := bstep (se 1 (by rfl) ⟨3275315, by rfl⟩ : syracuseStep 4367087 = 6550631) B6550631
theorem B151062893 : Blo 1291964 151062893 := bstep (se 3 (by rfl) ⟨28324292, by rfl⟩ : syracuseStep 151062893 = 56648585) B56648585
theorem B22088699 : Blo 1291964 22088699 := bstep (se 1 (by rfl) ⟨16566524, by rfl⟩ : syracuseStep 22088699 = 33133049) B33133049
theorem B10489733 : Blo 1291964 10489733 := bstep (se 4 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 10489733 = 1966825) B1966825
theorem B1938599 : Blo 1291964 1938599 := bstep (se 1 (by rfl) ⟨1453949, by rfl⟩ : syracuseStep 1938599 = 2907899) B2907899
theorem B1292967 : Blo 1291964 1292967 := bstep (se 1 (by rfl) ⟨969725, by rfl⟩ : syracuseStep 1292967 = 1939451) B1939451
theorem B11042027 : Blo 1291964 11042027 := bstep (se 1 (by rfl) ⟨8281520, by rfl⟩ : syracuseStep 11042027 = 16563041) B16563041
theorem B11796137 : Blo 1291964 11796137 := bstep (se 2 (by rfl) ⟨4423551, by rfl⟩ : syracuseStep 11796137 = 8847103) B8847103
theorem B2911391 : Blo 1291964 2911391 := bstep (se 1 (by rfl) ⟨2183543, by rfl⟩ : syracuseStep 2911391 = 4367087) B4367087
theorem B100708595 : Blo 1291964 100708595 := bstep (se 1 (by rfl) ⟨75531446, by rfl⟩ : syracuseStep 100708595 = 151062893) B151062893
theorem B14725799 : Blo 1291964 14725799 := bstep (se 1 (by rfl) ⟨11044349, by rfl⟩ : syracuseStep 14725799 = 22088699) B22088699
theorem B7361351 : Blo 1291964 7361351 := bstep (se 1 (by rfl) ⟨5521013, by rfl⟩ : syracuseStep 7361351 = 11042027) B11042027
theorem B6993155 : Blo 1291964 6993155 := bstep (se 1 (by rfl) ⟨5244866, by rfl⟩ : syracuseStep 6993155 = 10489733) B10489733
theorem B1292399 : Blo 1291964 1292399 := bstep (se 1 (by rfl) ⟨969299, by rfl⟩ : syracuseStep 1292399 = 1938599) B1938599
theorem B7864091 : Blo 1291964 7864091 := bstep (se 1 (by rfl) ⟨5898068, by rfl⟩ : syracuseStep 7864091 = 11796137) B11796137
theorem B4907567 : Blo 1291964 4907567 := bstep (se 1 (by rfl) ⟨3680675, by rfl⟩ : syracuseStep 4907567 = 7361351) B7361351
theorem B9817199 : Blo 1291964 9817199 := bstep (se 1 (by rfl) ⟨7362899, by rfl⟩ : syracuseStep 9817199 = 14725799) B14725799
theorem B18648413 : Blo 1291964 18648413 := bstep (se 3 (by rfl) ⟨3496577, by rfl⟩ : syracuseStep 18648413 = 6993155) B6993155
theorem B67139063 : Blo 1291964 67139063 := bstep (se 1 (by rfl) ⟨50354297, by rfl⟩ : syracuseStep 67139063 = 100708595) B100708595
theorem B1940927 : Blo 1291964 1940927 := bstep (se 1 (by rfl) ⟨1455695, by rfl⟩ : syracuseStep 1940927 = 2911391) B2911391
theorem B5242727 : Blo 1291964 5242727 := bstep (se 1 (by rfl) ⟨3932045, by rfl⟩ : syracuseStep 5242727 = 7864091) B7864091
theorem B3271711 : Blo 1291964 3271711 := bstep (se 1 (by rfl) ⟨2453783, by rfl⟩ : syracuseStep 3271711 = 4907567) B4907567
theorem B12432275 : Blo 1291964 12432275 := bstep (se 1 (by rfl) ⟨9324206, by rfl⟩ : syracuseStep 12432275 = 18648413) B18648413
theorem B3495151 : Blo 1291964 3495151 := bstep (se 1 (by rfl) ⟨2621363, by rfl⟩ : syracuseStep 3495151 = 5242727) B5242727
theorem B44759375 : Blo 1291964 44759375 := bstep (se 1 (by rfl) ⟨33569531, by rfl⟩ : syracuseStep 44759375 = 67139063) B67139063
theorem B6544799 : Blo 1291964 6544799 := bstep (se 1 (by rfl) ⟨4908599, by rfl⟩ : syracuseStep 6544799 = 9817199) B9817199
theorem B1293951 : Blo 1291964 1293951 := bstep (se 1 (by rfl) ⟨970463, by rfl⟩ : syracuseStep 1293951 = 1940927) B1940927
theorem B4362281 : Blo 1291964 4362281 := bstep (se 2 (by rfl) ⟨1635855, by rfl⟩ : syracuseStep 4362281 = 3271711) B3271711
theorem B29839583 : Blo 1291964 29839583 := bstep (se 1 (by rfl) ⟨22379687, by rfl⟩ : syracuseStep 29839583 = 44759375) B44759375
theorem B4363199 : Blo 1291964 4363199 := bstep (se 1 (by rfl) ⟨3272399, by rfl⟩ : syracuseStep 4363199 = 6544799) B6544799
theorem B8288183 : Blo 1291964 8288183 := bstep (se 1 (by rfl) ⟨6216137, by rfl⟩ : syracuseStep 8288183 = 12432275) B12432275
theorem B4660201 : Blo 1291964 4660201 := bstep (se 2 (by rfl) ⟨1747575, by rfl⟩ : syracuseStep 4660201 = 3495151) B3495151
theorem B2908187 : Blo 1291964 2908187 := bstep (se 1 (by rfl) ⟨2181140, by rfl⟩ : syracuseStep 2908187 = 4362281) B4362281
theorem B2908799 : Blo 1291964 2908799 := bstep (se 1 (by rfl) ⟨2181599, by rfl⟩ : syracuseStep 2908799 = 4363199) B4363199
theorem B19893055 : Blo 1291964 19893055 := bstep (se 1 (by rfl) ⟨14919791, by rfl⟩ : syracuseStep 19893055 = 29839583) B29839583
theorem B6213601 : Blo 1291964 6213601 := bstep (se 2 (by rfl) ⟨2330100, by rfl⟩ : syracuseStep 6213601 = 4660201) B4660201
theorem B22101821 : Blo 1291964 22101821 := bstep (se 3 (by rfl) ⟨4144091, by rfl⟩ : syracuseStep 22101821 = 8288183) B8288183
theorem B8284801 : Blo 1291964 8284801 := bstep (se 2 (by rfl) ⟨3106800, by rfl⟩ : syracuseStep 8284801 = 6213601) B6213601
theorem B14734547 : Blo 1291964 14734547 := bstep (se 1 (by rfl) ⟨11050910, by rfl⟩ : syracuseStep 14734547 = 22101821) B22101821
theorem B1938791 : Blo 1291964 1938791 := bstep (se 1 (by rfl) ⟨1454093, by rfl⟩ : syracuseStep 1938791 = 2908187) B2908187
theorem B1939199 : Blo 1291964 1939199 := bstep (se 1 (by rfl) ⟨1454399, by rfl⟩ : syracuseStep 1939199 = 2908799) B2908799
theorem B26524073 : Blo 1291964 26524073 := bstep (se 2 (by rfl) ⟨9946527, by rfl⟩ : syracuseStep 26524073 = 19893055) B19893055
theorem B9823031 : Blo 1291964 9823031 := bstep (se 1 (by rfl) ⟨7367273, by rfl⟩ : syracuseStep 9823031 = 14734547) B14734547
theorem B11046401 : Blo 1291964 11046401 := bstep (se 2 (by rfl) ⟨4142400, by rfl⟩ : syracuseStep 11046401 = 8284801) B8284801
theorem B17682715 : Blo 1291964 17682715 := bstep (se 1 (by rfl) ⟨13262036, by rfl⟩ : syracuseStep 17682715 = 26524073) B26524073
theorem B1292527 : Blo 1291964 1292527 := bstep (se 1 (by rfl) ⟨969395, by rfl⟩ : syracuseStep 1292527 = 1938791) B1938791
theorem B1292799 : Blo 1291964 1292799 := bstep (se 1 (by rfl) ⟨969599, by rfl⟩ : syracuseStep 1292799 = 1939199) B1939199
theorem B23576953 : Blo 1291964 23576953 := bstep (se 2 (by rfl) ⟨8841357, by rfl⟩ : syracuseStep 23576953 = 17682715) B17682715
theorem B6548687 : Blo 1291964 6548687 := bstep (se 1 (by rfl) ⟨4911515, by rfl⟩ : syracuseStep 6548687 = 9823031) B9823031
theorem B7364267 : Blo 1291964 7364267 := bstep (se 1 (by rfl) ⟨5523200, by rfl⟩ : syracuseStep 7364267 = 11046401) B11046401
theorem B4909511 : Blo 1291964 4909511 := bstep (se 1 (by rfl) ⟨3682133, by rfl⟩ : syracuseStep 4909511 = 7364267) B7364267
theorem B31435937 : Blo 1291964 31435937 := bstep (se 2 (by rfl) ⟨11788476, by rfl⟩ : syracuseStep 31435937 = 23576953) B23576953
theorem B4365791 : Blo 1291964 4365791 := bstep (se 1 (by rfl) ⟨3274343, by rfl⟩ : syracuseStep 4365791 = 6548687) B6548687
theorem B20957291 : Blo 1291964 20957291 := bstep (se 1 (by rfl) ⟨15717968, by rfl⟩ : syracuseStep 20957291 = 31435937) B31435937
theorem B2910527 : Blo 1291964 2910527 := bstep (se 1 (by rfl) ⟨2182895, by rfl⟩ : syracuseStep 2910527 = 4365791) B4365791
theorem B3273007 : Blo 1291964 3273007 := bstep (se 1 (by rfl) ⟨2454755, by rfl⟩ : syracuseStep 3273007 = 4909511) B4909511
theorem B13971527 : Blo 1291964 13971527 := bstep (se 1 (by rfl) ⟨10478645, by rfl⟩ : syracuseStep 13971527 = 20957291) B20957291
theorem B4364009 : Blo 1291964 4364009 := bstep (se 2 (by rfl) ⟨1636503, by rfl⟩ : syracuseStep 4364009 = 3273007) B3273007
theorem B1940351 : Blo 1291964 1940351 := bstep (se 1 (by rfl) ⟨1455263, by rfl⟩ : syracuseStep 1940351 = 2910527) B2910527
theorem B9314351 : Blo 1291964 9314351 := bstep (se 1 (by rfl) ⟨6985763, by rfl⟩ : syracuseStep 9314351 = 13971527) B13971527
theorem B2909339 : Blo 1291964 2909339 := bstep (se 1 (by rfl) ⟨2182004, by rfl⟩ : syracuseStep 2909339 = 4364009) B4364009
theorem B1293567 : Blo 1291964 1293567 := bstep (se 1 (by rfl) ⟨970175, by rfl⟩ : syracuseStep 1293567 = 1940351) B1940351
theorem B6209567 : Blo 1291964 6209567 := bstep (se 1 (by rfl) ⟨4657175, by rfl⟩ : syracuseStep 6209567 = 9314351) B9314351
theorem B1939559 : Blo 1291964 1939559 := bstep (se 1 (by rfl) ⟨1454669, by rfl⟩ : syracuseStep 1939559 = 2909339) B2909339
theorem B4139711 : Blo 1291964 4139711 := bstep (se 1 (by rfl) ⟨3104783, by rfl⟩ : syracuseStep 4139711 = 6209567) B6209567
theorem B1293039 : Blo 1291964 1293039 := bstep (se 1 (by rfl) ⟨969779, by rfl⟩ : syracuseStep 1293039 = 1939559) B1939559
theorem B2759807 : Blo 1291964 2759807 := bstep (se 1 (by rfl) ⟨2069855, by rfl⟩ : syracuseStep 2759807 = 4139711) B4139711
theorem B1839871 : Blo 1291964 1839871 := bstep (se 1 (by rfl) ⟨1379903, by rfl⟩ : syracuseStep 1839871 = 2759807) B2759807
theorem B2453161 : Blo 1291964 2453161 := bstep (se 2 (by rfl) ⟨919935, by rfl⟩ : syracuseStep 2453161 = 1839871) B1839871
theorem B3270881 : Blo 1291964 3270881 := bstep (se 2 (by rfl) ⟨1226580, by rfl⟩ : syracuseStep 3270881 = 2453161) B2453161
theorem B2180587 : Blo 1291964 2180587 := bstep (se 1 (by rfl) ⟨1635440, by rfl⟩ : syracuseStep 2180587 = 3270881) B3270881
theorem B2907449 : Blo 1291964 2907449 := bstep (se 2 (by rfl) ⟨1090293, by rfl⟩ : syracuseStep 2907449 = 2180587) B2180587
theorem B1938299 : Blo 1291964 1938299 := bstep (se 1 (by rfl) ⟨1453724, by rfl⟩ : syracuseStep 1938299 = 2907449) B2907449
theorem B1292199 : Blo 1291964 1292199 := bstep (se 1 (by rfl) ⟨969149, by rfl⟩ : syracuseStep 1292199 = 1938299) B1938299

theorem C0 (j : ℕ) (h1 : 322991 ≤ j) (h2 : j ≤ 323490) : Blo 1291964 (4 * j + 3) := by
  interval_cases j
  · exact B1291967
  · exact B1291971
  · exact B1291975
  · exact B1291979
  · exact B1291983
  · exact B1291987
  · exact B1291991
  · exact B1291995
  · exact B1291999
  · exact B1292003
  · exact B1292007
  · exact B1292011
  · exact B1292015
  · exact B1292019
  · exact B1292023
  · exact B1292027
  · exact B1292031
  · exact B1292035
  · exact B1292039
  · exact B1292043
  · exact B1292047
  · exact B1292051
  · exact B1292055
  · exact B1292059
  · exact B1292063
  · exact B1292067
  · exact B1292071
  · exact B1292075
  · exact B1292079
  · exact B1292083
  · exact B1292087
  · exact B1292091
  · exact B1292095
  · exact B1292099
  · exact B1292103
  · exact B1292107
  · exact B1292111
  · exact B1292115
  · exact B1292119
  · exact B1292123
  · exact B1292127
  · exact B1292131
  · exact B1292135
  · exact B1292139
  · exact B1292143
  · exact B1292147
  · exact B1292151
  · exact B1292155
  · exact B1292159
  · exact B1292163
  · exact B1292167
  · exact B1292171
  · exact B1292175
  · exact B1292179
  · exact B1292183
  · exact B1292187
  · exact B1292191
  · exact B1292195
  · exact B1292199
  · exact B1292203
  · exact B1292207
  · exact B1292211
  · exact B1292215
  · exact B1292219
  · exact B1292223
  · exact B1292227
  · exact B1292231
  · exact B1292235
  · exact B1292239
  · exact B1292243
  · exact B1292247
  · exact B1292251
  · exact B1292255
  · exact B1292259
  · exact B1292263
  · exact B1292267
  · exact B1292271
  · exact B1292275
  · exact B1292279
  · exact B1292283
  · exact B1292287
  · exact B1292291
  · exact B1292295
  · exact B1292299
  · exact B1292303
  · exact B1292307
  · exact B1292311
  · exact B1292315
  · exact B1292319
  · exact B1292323
  · exact B1292327
  · exact B1292331
  · exact B1292335
  · exact B1292339
  · exact B1292343
  · exact B1292347
  · exact B1292351
  · exact B1292355
  · exact B1292359
  · exact B1292363
  · exact B1292367
  · exact B1292371
  · exact B1292375
  · exact B1292379
  · exact B1292383
  · exact B1292387
  · exact B1292391
  · exact B1292395
  · exact B1292399
  · exact B1292403
  · exact B1292407
  · exact B1292411
  · exact B1292415
  · exact B1292419
  · exact B1292423
  · exact B1292427
  · exact B1292431
  · exact B1292435
  · exact B1292439
  · exact B1292443
  · exact B1292447
  · exact B1292451
  · exact B1292455
  · exact B1292459
  · exact B1292463
  · exact B1292467
  · exact B1292471
  · exact B1292475
  · exact B1292479
  · exact B1292483
  · exact B1292487
  · exact B1292491
  · exact B1292495
  · exact B1292499
  · exact B1292503
  · exact B1292507
  · exact B1292511
  · exact B1292515
  · exact B1292519
  · exact B1292523
  · exact B1292527
  · exact B1292531
  · exact B1292535
  · exact B1292539
  · exact B1292543
  · exact B1292547
  · exact B1292551
  · exact B1292555
  · exact B1292559
  · exact B1292563
  · exact B1292567
  · exact B1292571
  · exact B1292575
  · exact B1292579
  · exact B1292583
  · exact B1292587
  · exact B1292591
  · exact B1292595
  · exact B1292599
  · exact B1292603
  · exact B1292607
  · exact B1292611
  · exact B1292615
  · exact B1292619
  · exact B1292623
  · exact B1292627
  · exact B1292631
  · exact B1292635
  · exact B1292639
  · exact B1292643
  · exact B1292647
  · exact B1292651
  · exact B1292655
  · exact B1292659
  · exact B1292663
  · exact B1292667
  · exact B1292671
  · exact B1292675
  · exact B1292679
  · exact B1292683
  · exact B1292687
  · exact B1292691
  · exact B1292695
  · exact B1292699
  · exact B1292703
  · exact B1292707
  · exact B1292711
  · exact B1292715
  · exact B1292719
  · exact B1292723
  · exact B1292727
  · exact B1292731
  · exact B1292735
  · exact B1292739
  · exact B1292743
  · exact B1292747
  · exact B1292751
  · exact B1292755
  · exact B1292759
  · exact B1292763
  · exact B1292767
  · exact B1292771
  · exact B1292775
  · exact B1292779
  · exact B1292783
  · exact B1292787
  · exact B1292791
  · exact B1292795
  · exact B1292799
  · exact B1292803
  · exact B1292807
  · exact B1292811
  · exact B1292815
  · exact B1292819
  · exact B1292823
  · exact B1292827
  · exact B1292831
  · exact B1292835
  · exact B1292839
  · exact B1292843
  · exact B1292847
  · exact B1292851
  · exact B1292855
  · exact B1292859
  · exact B1292863
  · exact B1292867
  · exact B1292871
  · exact B1292875
  · exact B1292879
  · exact B1292883
  · exact B1292887
  · exact B1292891
  · exact B1292895
  · exact B1292899
  · exact B1292903
  · exact B1292907
  · exact B1292911
  · exact B1292915
  · exact B1292919
  · exact B1292923
  · exact B1292927
  · exact B1292931
  · exact B1292935
  · exact B1292939
  · exact B1292943
  · exact B1292947
  · exact B1292951
  · exact B1292955
  · exact B1292959
  · exact B1292963
  · exact B1292967
  · exact B1292971
  · exact B1292975
  · exact B1292979
  · exact B1292983
  · exact B1292987
  · exact B1292991
  · exact B1292995
  · exact B1292999
  · exact B1293003
  · exact B1293007
  · exact B1293011
  · exact B1293015
  · exact B1293019
  · exact B1293023
  · exact B1293027
  · exact B1293031
  · exact B1293035
  · exact B1293039
  · exact B1293043
  · exact B1293047
  · exact B1293051
  · exact B1293055
  · exact B1293059
  · exact B1293063
  · exact B1293067
  · exact B1293071
  · exact B1293075
  · exact B1293079
  · exact B1293083
  · exact B1293087
  · exact B1293091
  · exact B1293095
  · exact B1293099
  · exact B1293103
  · exact B1293107
  · exact B1293111
  · exact B1293115
  · exact B1293119
  · exact B1293123
  · exact B1293127
  · exact B1293131
  · exact B1293135
  · exact B1293139
  · exact B1293143
  · exact B1293147
  · exact B1293151
  · exact B1293155
  · exact B1293159
  · exact B1293163
  · exact B1293167
  · exact B1293171
  · exact B1293175
  · exact B1293179
  · exact B1293183
  · exact B1293187
  · exact B1293191
  · exact B1293195
  · exact B1293199
  · exact B1293203
  · exact B1293207
  · exact B1293211
  · exact B1293215
  · exact B1293219
  · exact B1293223
  · exact B1293227
  · exact B1293231
  · exact B1293235
  · exact B1293239
  · exact B1293243
  · exact B1293247
  · exact B1293251
  · exact B1293255
  · exact B1293259
  · exact B1293263
  · exact B1293267
  · exact B1293271
  · exact B1293275
  · exact B1293279
  · exact B1293283
  · exact B1293287
  · exact B1293291
  · exact B1293295
  · exact B1293299
  · exact B1293303
  · exact B1293307
  · exact B1293311
  · exact B1293315
  · exact B1293319
  · exact B1293323
  · exact B1293327
  · exact B1293331
  · exact B1293335
  · exact B1293339
  · exact B1293343
  · exact B1293347
  · exact B1293351
  · exact B1293355
  · exact B1293359
  · exact B1293363
  · exact B1293367
  · exact B1293371
  · exact B1293375
  · exact B1293379
  · exact B1293383
  · exact B1293387
  · exact B1293391
  · exact B1293395
  · exact B1293399
  · exact B1293403
  · exact B1293407
  · exact B1293411
  · exact B1293415
  · exact B1293419
  · exact B1293423
  · exact B1293427
  · exact B1293431
  · exact B1293435
  · exact B1293439
  · exact B1293443
  · exact B1293447
  · exact B1293451
  · exact B1293455
  · exact B1293459
  · exact B1293463
  · exact B1293467
  · exact B1293471
  · exact B1293475
  · exact B1293479
  · exact B1293483
  · exact B1293487
  · exact B1293491
  · exact B1293495
  · exact B1293499
  · exact B1293503
  · exact B1293507
  · exact B1293511
  · exact B1293515
  · exact B1293519
  · exact B1293523
  · exact B1293527
  · exact B1293531
  · exact B1293535
  · exact B1293539
  · exact B1293543
  · exact B1293547
  · exact B1293551
  · exact B1293555
  · exact B1293559
  · exact B1293563
  · exact B1293567
  · exact B1293571
  · exact B1293575
  · exact B1293579
  · exact B1293583
  · exact B1293587
  · exact B1293591
  · exact B1293595
  · exact B1293599
  · exact B1293603
  · exact B1293607
  · exact B1293611
  · exact B1293615
  · exact B1293619
  · exact B1293623
  · exact B1293627
  · exact B1293631
  · exact B1293635
  · exact B1293639
  · exact B1293643
  · exact B1293647
  · exact B1293651
  · exact B1293655
  · exact B1293659
  · exact B1293663
  · exact B1293667
  · exact B1293671
  · exact B1293675
  · exact B1293679
  · exact B1293683
  · exact B1293687
  · exact B1293691
  · exact B1293695
  · exact B1293699
  · exact B1293703
  · exact B1293707
  · exact B1293711
  · exact B1293715
  · exact B1293719
  · exact B1293723
  · exact B1293727
  · exact B1293731
  · exact B1293735
  · exact B1293739
  · exact B1293743
  · exact B1293747
  · exact B1293751
  · exact B1293755
  · exact B1293759
  · exact B1293763
  · exact B1293767
  · exact B1293771
  · exact B1293775
  · exact B1293779
  · exact B1293783
  · exact B1293787
  · exact B1293791
  · exact B1293795
  · exact B1293799
  · exact B1293803
  · exact B1293807
  · exact B1293811
  · exact B1293815
  · exact B1293819
  · exact B1293823
  · exact B1293827
  · exact B1293831
  · exact B1293835
  · exact B1293839
  · exact B1293843
  · exact B1293847
  · exact B1293851
  · exact B1293855
  · exact B1293859
  · exact B1293863
  · exact B1293867
  · exact B1293871
  · exact B1293875
  · exact B1293879
  · exact B1293883
  · exact B1293887
  · exact B1293891
  · exact B1293895
  · exact B1293899
  · exact B1293903
  · exact B1293907
  · exact B1293911
  · exact B1293915
  · exact B1293919
  · exact B1293923
  · exact B1293927
  · exact B1293931
  · exact B1293935
  · exact B1293939
  · exact B1293943
  · exact B1293947
  · exact B1293951
  · exact B1293955
  · exact B1293959
  · exact B1293963

theorem solution (m : ℕ) (hlo : 1291964 ≤ m) (hhi : m ≤ 1293964) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 322991 ≤ j := by omega
    have hj2 : j ≤ 323490 := by omega
    have hb : Blo 1291964 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
