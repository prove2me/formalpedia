-- Prove2me | solution 1 for syracuse_descends_range_1397518_1399518
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:47.138664+00:00
-- url     : https://prove2.me/submissions/eed18591-26fb-4e1a-ac48-f236cce0b703

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


theorem B3145733 : Blo 1397518 3145733 := bbase (se 4 (by rfl) ⟨294912, by rfl⟩ : syracuseStep 3145733 = 589825) (by norm_num)
theorem B2654221 : Blo 1397518 2654221 := bbase (se 3 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 2654221 = 995333) (by norm_num)
theorem B2097173 : Blo 1397518 2097173 := bbase (se 6 (by rfl) ⟨49152, by rfl⟩ : syracuseStep 2097173 = 98305) (by norm_num)
theorem B1572889 : Blo 1397518 1572889 := bbase (se 2 (by rfl) ⟨589833, by rfl⟩ : syracuseStep 1572889 = 1179667) (by norm_num)
theorem B2097197 : Blo 1397518 2097197 := bbase (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) (by norm_num)
theorem B1769521 : Blo 1397518 1769521 := bbase (se 2 (by rfl) ⟨663570, by rfl⟩ : syracuseStep 1769521 = 1327141) (by norm_num)
theorem B7077941 : Blo 1397518 7077941 := bbase (se 5 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 7077941 = 663557) (by norm_num)
theorem B1572925 : Blo 1397518 1572925 := bbase (se 3 (by rfl) ⟨294923, by rfl⟩ : syracuseStep 1572925 = 589847) (by norm_num)
theorem B2097221 : Blo 1397518 2097221 := bbase (se 4 (by rfl) ⟨196614, by rfl⟩ : syracuseStep 2097221 = 393229) (by norm_num)
theorem B1679437 : Blo 1397518 1679437 := bbase (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) (by norm_num)
theorem B3145805 : Blo 1397518 3145805 := bbase (se 3 (by rfl) ⟨589838, by rfl⟩ : syracuseStep 3145805 = 1179677) (by norm_num)
theorem B2359381 : Blo 1397518 2359381 := bbase (se 8 (by rfl) ⟨13824, by rfl⟩ : syracuseStep 2359381 = 27649) (by norm_num)
theorem B2097245 : Blo 1397518 2097245 := bbase (se 3 (by rfl) ⟨393233, by rfl⟩ : syracuseStep 2097245 = 786467) (by norm_num)
theorem B1572961 : Blo 1397518 1572961 := bbase (se 2 (by rfl) ⟨589860, by rfl⟩ : syracuseStep 1572961 = 1179721) (by norm_num)
theorem B5308517 : Blo 1397518 5308517 := bbase (se 4 (by rfl) ⟨497673, by rfl⟩ : syracuseStep 5308517 = 995347) (by norm_num)
theorem B1990757 : Blo 1397518 1990757 := bbase (se 4 (by rfl) ⟨186633, by rfl⟩ : syracuseStep 1990757 = 373267) (by norm_num)
theorem B1794161 : Blo 1397518 1794161 := bbase (se 2 (by rfl) ⟨672810, by rfl⟩ : syracuseStep 1794161 = 1345621) (by norm_num)
theorem B2097269 : Blo 1397518 2097269 := bbase (se 5 (by rfl) ⟨98309, by rfl⟩ : syracuseStep 2097269 = 196619) (by norm_num)
theorem B1572997 : Blo 1397518 1572997 := bbase (se 4 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 1572997 = 294937) (by norm_num)
theorem B2097293 : Blo 1397518 2097293 := bbase (se 3 (by rfl) ⟨393242, by rfl⟩ : syracuseStep 2097293 = 786485) (by norm_num)
theorem B1769617 : Blo 1397518 1769617 := bbase (se 2 (by rfl) ⟨663606, by rfl⟩ : syracuseStep 1769617 = 1327213) (by norm_num)
theorem B3145877 : Blo 1397518 3145877 := bbase (se 6 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 3145877 = 147463) (by norm_num)
theorem B2654365 : Blo 1397518 2654365 := bbase (se 3 (by rfl) ⟨497693, by rfl⟩ : syracuseStep 2654365 = 995387) (by norm_num)
theorem B2097317 : Blo 1397518 2097317 := bbase (se 4 (by rfl) ⟨196623, by rfl⟩ : syracuseStep 2097317 = 393247) (by norm_num)
theorem B1573033 : Blo 1397518 1573033 := bbase (se 2 (by rfl) ⟨589887, by rfl⟩ : syracuseStep 1573033 = 1179775) (by norm_num)
theorem B2359469 : Blo 1397518 2359469 := bbase (se 3 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 2359469 = 884801) (by norm_num)
theorem B2097341 : Blo 1397518 2097341 := bbase (se 3 (by rfl) ⟨393251, by rfl⟩ : syracuseStep 2097341 = 786503) (by norm_num)
theorem B4718789 : Blo 1397518 4718789 := bbase (se 4 (by rfl) ⟨442386, by rfl⟩ : syracuseStep 4718789 = 884773) (by norm_num)
theorem B1573069 : Blo 1397518 1573069 := bbase (se 3 (by rfl) ⟨294950, by rfl⟩ : syracuseStep 1573069 = 589901) (by norm_num)
theorem B2097365 : Blo 1397518 2097365 := bbase (se 7 (by rfl) ⟨24578, by rfl⟩ : syracuseStep 2097365 = 49157) (by norm_num)
theorem B3145949 : Blo 1397518 3145949 := bbase (se 3 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 3145949 = 1179731) (by norm_num)
theorem B3539173 : Blo 1397518 3539173 := bbase (se 4 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 3539173 = 663595) (by norm_num)
theorem B2097389 : Blo 1397518 2097389 := bbase (se 3 (by rfl) ⟨393260, by rfl⟩ : syracuseStep 2097389 = 786521) (by norm_num)
theorem B1573105 : Blo 1397518 1573105 := bbase (se 2 (by rfl) ⟨589914, by rfl⟩ : syracuseStep 1573105 = 1179829) (by norm_num)
theorem B2097413 : Blo 1397518 2097413 := bbase (se 4 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 2097413 = 393265) (by norm_num)
theorem B1573141 : Blo 1397518 1573141 := bbase (se 6 (by rfl) ⟨36870, by rfl⟩ : syracuseStep 1573141 = 73741) (by norm_num)
theorem B2097437 : Blo 1397518 2097437 := bbase (se 3 (by rfl) ⟨393269, by rfl⟩ : syracuseStep 2097437 = 786539) (by norm_num)
theorem B3146021 : Blo 1397518 3146021 := bbase (se 4 (by rfl) ⟨294939, by rfl⟩ : syracuseStep 3146021 = 589879) (by norm_num)
theorem B2359597 : Blo 1397518 2359597 := bbase (se 3 (by rfl) ⟨442424, by rfl⟩ : syracuseStep 2359597 = 884849) (by norm_num)
theorem B2097461 : Blo 1397518 2097461 := bbase (se 5 (by rfl) ⟨98318, by rfl⟩ : syracuseStep 2097461 = 196637) (by norm_num)
theorem B1573177 : Blo 1397518 1573177 := bbase (se 2 (by rfl) ⟨589941, by rfl⟩ : syracuseStep 1573177 = 1179883) (by norm_num)
theorem B2654525 : Blo 1397518 2654525 := bbase (se 3 (by rfl) ⟨497723, by rfl⟩ : syracuseStep 2654525 = 995447) (by norm_num)
theorem B1769789 : Blo 1397518 1769789 := bbase (se 3 (by rfl) ⟨331835, by rfl⟩ : syracuseStep 1769789 = 663671) (by norm_num)
theorem B2097485 : Blo 1397518 2097485 := bbase (se 3 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 2097485 = 786557) (by norm_num)
theorem B3539285 : Blo 1397518 3539285 := bbase (se 10 (by rfl) ⟨5184, by rfl⟩ : syracuseStep 3539285 = 10369) (by norm_num)
theorem B1573213 : Blo 1397518 1573213 := bbase (se 3 (by rfl) ⟨294977, by rfl⟩ : syracuseStep 1573213 = 589955) (by norm_num)
theorem B2097509 : Blo 1397518 2097509 := bbase (se 4 (by rfl) ⟨196641, by rfl⟩ : syracuseStep 2097509 = 393283) (by norm_num)
theorem B3146093 : Blo 1397518 3146093 := bbase (se 3 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 3146093 = 1179785) (by norm_num)
theorem B1417585 : Blo 1397518 1417585 := bbase (se 2 (by rfl) ⟨531594, by rfl⟩ : syracuseStep 1417585 = 1063189) (by norm_num)
theorem B1769845 : Blo 1397518 1769845 := bbase (se 5 (by rfl) ⟨82961, by rfl⟩ : syracuseStep 1769845 = 165923) (by norm_num)
theorem B2097533 : Blo 1397518 2097533 := bbase (se 3 (by rfl) ⟨393287, by rfl⟩ : syracuseStep 2097533 = 786575) (by norm_num)
theorem B1573249 : Blo 1397518 1573249 := bbase (se 2 (by rfl) ⟨589968, by rfl⟩ : syracuseStep 1573249 = 1179937) (by norm_num)
theorem B2359685 : Blo 1397518 2359685 := bbase (se 4 (by rfl) ⟨221220, by rfl⟩ : syracuseStep 2359685 = 442441) (by norm_num)
theorem B2097557 : Blo 1397518 2097557 := bbase (se 6 (by rfl) ⟨49161, by rfl⟩ : syracuseStep 2097557 = 98323) (by norm_num)
theorem B1573285 : Blo 1397518 1573285 := bbase (se 4 (by rfl) ⟨147495, by rfl⟩ : syracuseStep 1573285 = 294991) (by norm_num)
theorem B2097581 : Blo 1397518 2097581 := bbase (se 3 (by rfl) ⟨393296, by rfl⟩ : syracuseStep 2097581 = 786593) (by norm_num)
theorem B3146165 : Blo 1397518 3146165 := bbase (se 5 (by rfl) ⟨147476, by rfl⟩ : syracuseStep 3146165 = 294953) (by norm_num)
theorem B2097605 : Blo 1397518 2097605 := bbase (se 4 (by rfl) ⟨196650, by rfl⟩ : syracuseStep 2097605 = 393301) (by norm_num)
theorem B1573321 : Blo 1397518 1573321 := bbase (se 2 (by rfl) ⟨589995, by rfl⟩ : syracuseStep 1573321 = 1179991) (by norm_num)
theorem B1679821 : Blo 1397518 1679821 := bbase (se 3 (by rfl) ⟨314966, by rfl⟩ : syracuseStep 1679821 = 629933) (by norm_num)
theorem B2654669 : Blo 1397518 2654669 := bbase (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) (by norm_num)
theorem B1769941 : Blo 1397518 1769941 := bbase (se 7 (by rfl) ⟨20741, by rfl⟩ : syracuseStep 1769941 = 41483) (by norm_num)
theorem B1819093 : Blo 1397518 1819093 := bbase (se 7 (by rfl) ⟨21317, by rfl⟩ : syracuseStep 1819093 = 42635) (by norm_num)
theorem B2097629 : Blo 1397518 2097629 := bbase (se 3 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 2097629 = 786611) (by norm_num)
theorem B1573357 : Blo 1397518 1573357 := bbase (se 3 (by rfl) ⟨295004, by rfl⟩ : syracuseStep 1573357 = 590009) (by norm_num)
theorem B6717941 : Blo 1397518 6717941 := bbase (se 5 (by rfl) ⟨314903, by rfl⟩ : syracuseStep 6717941 = 629807) (by norm_num)
theorem B2097653 : Blo 1397518 2097653 := bbase (se 5 (by rfl) ⟨98327, by rfl⟩ : syracuseStep 2097653 = 196655) (by norm_num)
theorem B3146237 : Blo 1397518 3146237 := bbase (se 3 (by rfl) ⟨589919, by rfl⟩ : syracuseStep 3146237 = 1179839) (by norm_num)
theorem B2359813 : Blo 1397518 2359813 := bbase (se 4 (by rfl) ⟨221232, by rfl⟩ : syracuseStep 2359813 = 442465) (by norm_num)
theorem B2097677 : Blo 1397518 2097677 := bbase (se 3 (by rfl) ⟨393314, by rfl⟩ : syracuseStep 2097677 = 786629) (by norm_num)
theorem B1573393 : Blo 1397518 1573393 := bbase (se 2 (by rfl) ⟨590022, by rfl⟩ : syracuseStep 1573393 = 1180045) (by norm_num)
theorem B3539477 : Blo 1397518 3539477 := bbase (se 6 (by rfl) ⟨82956, by rfl⟩ : syracuseStep 3539477 = 165913) (by norm_num)
theorem B2097701 : Blo 1397518 2097701 := bbase (se 4 (by rfl) ⟨196659, by rfl⟩ : syracuseStep 2097701 = 393319) (by norm_num)
theorem B4481573 : Blo 1397518 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B1573429 : Blo 1397518 1573429 := bbase (se 5 (by rfl) ⟨73754, by rfl⟩ : syracuseStep 1573429 = 147509) (by norm_num)
theorem B2097725 : Blo 1397518 2097725 := bbase (se 3 (by rfl) ⟨393323, by rfl⟩ : syracuseStep 2097725 = 786647) (by norm_num)
theorem B3146309 : Blo 1397518 3146309 := bbase (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) (by norm_num)
theorem B2097749 : Blo 1397518 2097749 := bbase (se 8 (by rfl) ⟨12291, by rfl⟩ : syracuseStep 2097749 = 24583) (by norm_num)
theorem B1573465 : Blo 1397518 1573465 := bbase (se 2 (by rfl) ⟨590049, by rfl⟩ : syracuseStep 1573465 = 1180099) (by norm_num)
theorem B2359901 : Blo 1397518 2359901 := bbase (se 3 (by rfl) ⟨442481, by rfl⟩ : syracuseStep 2359901 = 884963) (by norm_num)
theorem B2097773 : Blo 1397518 2097773 := bbase (se 3 (by rfl) ⟨393332, by rfl⟩ : syracuseStep 2097773 = 786665) (by norm_num)
theorem B4719221 : Blo 1397518 4719221 := bbase (se 5 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 4719221 = 442427) (by norm_num)
theorem B1573501 : Blo 1397518 1573501 := bbase (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) (by norm_num)
theorem B1770113 : Blo 1397518 1770113 := bbase (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) (by norm_num)
theorem B2097797 : Blo 1397518 2097797 := bbase (se 4 (by rfl) ⟨196668, by rfl⟩ : syracuseStep 2097797 = 393337) (by norm_num)
theorem B3146381 : Blo 1397518 3146381 := bbase (se 3 (by rfl) ⟨589946, by rfl⟩ : syracuseStep 3146381 = 1179893) (by norm_num)
theorem B1991309 : Blo 1397518 1991309 := bbase (se 3 (by rfl) ⟨373370, by rfl⟩ : syracuseStep 1991309 = 746741) (by norm_num)
theorem B5972629 : Blo 1397518 5972629 := bbase (se 6 (by rfl) ⟨139983, by rfl⟩ : syracuseStep 5972629 = 279967) (by norm_num)
theorem B1819285 : Blo 1397518 1819285 := bbase (se 6 (by rfl) ⟨42639, by rfl⟩ : syracuseStep 1819285 = 85279) (by norm_num)
theorem B15131285 : Blo 1397518 15131285 := bbase (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) (by norm_num)
theorem B2097821 : Blo 1397518 2097821 := bbase (se 3 (by rfl) ⟨393341, by rfl⟩ : syracuseStep 2097821 = 786683) (by norm_num)
theorem B1573537 : Blo 1397518 1573537 := bbase (se 2 (by rfl) ⟨590076, by rfl⟩ : syracuseStep 1573537 = 1180153) (by norm_num)
theorem B2097845 : Blo 1397518 2097845 := bbase (se 5 (by rfl) ⟨98336, by rfl⟩ : syracuseStep 2097845 = 196673) (by norm_num)
theorem B1770169 : Blo 1397518 1770169 := bbase (se 2 (by rfl) ⟨663813, by rfl⟩ : syracuseStep 1770169 = 1327627) (by norm_num)
theorem B1573573 : Blo 1397518 1573573 := bbase (se 4 (by rfl) ⟨147522, by rfl⟩ : syracuseStep 1573573 = 295045) (by norm_num)
theorem B2097869 : Blo 1397518 2097869 := bbase (se 3 (by rfl) ⟨393350, by rfl⟩ : syracuseStep 2097869 = 786701) (by norm_num)
theorem B3146453 : Blo 1397518 3146453 := bbase (se 7 (by rfl) ⟨36872, by rfl⟩ : syracuseStep 3146453 = 73745) (by norm_num)
theorem B2360029 : Blo 1397518 2360029 := bbase (se 3 (by rfl) ⟨442505, by rfl⟩ : syracuseStep 2360029 = 885011) (by norm_num)
theorem B2097893 : Blo 1397518 2097893 := bbase (se 4 (by rfl) ⟨196677, by rfl⟩ : syracuseStep 2097893 = 393355) (by norm_num)
theorem B1573609 : Blo 1397518 1573609 := bbase (se 2 (by rfl) ⟨590103, by rfl⟩ : syracuseStep 1573609 = 1180207) (by norm_num)
theorem B2654957 : Blo 1397518 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B2097917 : Blo 1397518 2097917 := bbase (se 3 (by rfl) ⟨393359, by rfl⟩ : syracuseStep 2097917 = 786719) (by norm_num)
theorem B1573645 : Blo 1397518 1573645 := bbase (se 3 (by rfl) ⟨295058, by rfl⟩ : syracuseStep 1573645 = 590117) (by norm_num)
theorem B2097941 : Blo 1397518 2097941 := bbase (se 6 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 2097941 = 98341) (by norm_num)
theorem B1770265 : Blo 1397518 1770265 := bbase (se 2 (by rfl) ⟨663849, by rfl⟩ : syracuseStep 1770265 = 1327699) (by norm_num)
theorem B3146525 : Blo 1397518 3146525 := bbase (se 3 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 3146525 = 1179947) (by norm_num)
theorem B3982117 : Blo 1397518 3982117 := bbase (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) (by norm_num)
theorem B2097965 : Blo 1397518 2097965 := bbase (se 3 (by rfl) ⟨393368, by rfl⟩ : syracuseStep 2097965 = 786737) (by norm_num)
theorem B1573681 : Blo 1397518 1573681 := bbase (se 2 (by rfl) ⟨590130, by rfl⟩ : syracuseStep 1573681 = 1180261) (by norm_num)
theorem B2360117 : Blo 1397518 2360117 := bbase (se 5 (by rfl) ⟨110630, by rfl⟩ : syracuseStep 2360117 = 221261) (by norm_num)
theorem B2097989 : Blo 1397518 2097989 := bbase (se 4 (by rfl) ⟨196686, by rfl⟩ : syracuseStep 2097989 = 393373) (by norm_num)
theorem B1573717 : Blo 1397518 1573717 := bbase (se 9 (by rfl) ⟨4610, by rfl⟩ : syracuseStep 1573717 = 9221) (by norm_num)
theorem B1794901 : Blo 1397518 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B2098013 : Blo 1397518 2098013 := bbase (se 3 (by rfl) ⟨393377, by rfl⟩ : syracuseStep 2098013 = 786755) (by norm_num)
theorem B3146597 : Blo 1397518 3146597 := bbase (se 4 (by rfl) ⟨294993, by rfl⟩ : syracuseStep 3146597 = 589987) (by norm_num)
theorem B3539821 : Blo 1397518 3539821 := bbase (se 3 (by rfl) ⟨663716, by rfl⟩ : syracuseStep 3539821 = 1327433) (by norm_num)
theorem B2098037 : Blo 1397518 2098037 := bbase (se 5 (by rfl) ⟨98345, by rfl⟩ : syracuseStep 2098037 = 196691) (by norm_num)
theorem B1573753 : Blo 1397518 1573753 := bbase (se 2 (by rfl) ⟨590157, by rfl⟩ : syracuseStep 1573753 = 1180315) (by norm_num)
theorem B2655109 : Blo 1397518 2655109 := bbase (se 4 (by rfl) ⟨248916, by rfl⟩ : syracuseStep 2655109 = 497833) (by norm_num)
theorem B2098061 : Blo 1397518 2098061 := bbase (se 3 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 2098061 = 786773) (by norm_num)
theorem B1573789 : Blo 1397518 1573789 := bbase (se 3 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 1573789 = 590171) (by norm_num)
theorem B2098085 : Blo 1397518 2098085 := bbase (se 4 (by rfl) ⟨196695, by rfl⟩ : syracuseStep 2098085 = 393391) (by norm_num)
theorem B3146669 : Blo 1397518 3146669 := bbase (se 3 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 3146669 = 1180001) (by norm_num)
theorem B2360245 : Blo 1397518 2360245 := bbase (se 5 (by rfl) ⟨110636, by rfl⟩ : syracuseStep 2360245 = 221273) (by norm_num)
theorem B2098109 : Blo 1397518 2098109 := bbase (se 3 (by rfl) ⟨393395, by rfl⟩ : syracuseStep 2098109 = 786791) (by norm_num)
theorem B1573825 : Blo 1397518 1573825 := bbase (se 2 (by rfl) ⟨590184, by rfl⟩ : syracuseStep 1573825 = 1180369) (by norm_num)
theorem B3982277 : Blo 1397518 3982277 := bbase (se 4 (by rfl) ⟨373338, by rfl⟩ : syracuseStep 3982277 = 746677) (by norm_num)
theorem B1770437 : Blo 1397518 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B22668245 : Blo 1397518 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B2098133 : Blo 1397518 2098133 := bbase (se 7 (by rfl) ⟨24587, by rfl⟩ : syracuseStep 2098133 = 49175) (by norm_num)
theorem B3539933 : Blo 1397518 3539933 := bbase (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) (by norm_num)
theorem B1573861 : Blo 1397518 1573861 := bbase (se 4 (by rfl) ⟨147549, by rfl⟩ : syracuseStep 1573861 = 295099) (by norm_num)
theorem B2098157 : Blo 1397518 2098157 := bbase (se 3 (by rfl) ⟨393404, by rfl⟩ : syracuseStep 2098157 = 786809) (by norm_num)
theorem B3146741 : Blo 1397518 3146741 := bbase (se 5 (by rfl) ⟨147503, by rfl⟩ : syracuseStep 3146741 = 295007) (by norm_num)
theorem B1770493 : Blo 1397518 1770493 := bbase (se 3 (by rfl) ⟨331967, by rfl⟩ : syracuseStep 1770493 = 663935) (by norm_num)
theorem B2098181 : Blo 1397518 2098181 := bbase (se 4 (by rfl) ⟨196704, by rfl⟩ : syracuseStep 2098181 = 393409) (by norm_num)
theorem B1573897 : Blo 1397518 1573897 := bbase (se 2 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 1573897 = 1180423) (by norm_num)
theorem B2360333 : Blo 1397518 2360333 := bbase (se 3 (by rfl) ⟨442562, by rfl⟩ : syracuseStep 2360333 = 885125) (by norm_num)
theorem B2098205 : Blo 1397518 2098205 := bbase (se 3 (by rfl) ⟨393413, by rfl⟩ : syracuseStep 2098205 = 786827) (by norm_num)
theorem B4719653 : Blo 1397518 4719653 := bbase (se 4 (by rfl) ⟨442467, by rfl⟩ : syracuseStep 4719653 = 884935) (by norm_num)
theorem B1573933 : Blo 1397518 1573933 := bbase (se 3 (by rfl) ⟨295112, by rfl⟩ : syracuseStep 1573933 = 590225) (by norm_num)
theorem B2098229 : Blo 1397518 2098229 := bbase (se 5 (by rfl) ⟨98354, by rfl⟩ : syracuseStep 2098229 = 196709) (by norm_num)
theorem B3146813 : Blo 1397518 3146813 := bbase (se 3 (by rfl) ⟨590027, by rfl⟩ : syracuseStep 3146813 = 1180055) (by norm_num)
theorem B2098253 : Blo 1397518 2098253 := bbase (se 3 (by rfl) ⟨393422, by rfl⟩ : syracuseStep 2098253 = 786845) (by norm_num)
theorem B1573969 : Blo 1397518 1573969 := bbase (se 2 (by rfl) ⟨590238, by rfl⟩ : syracuseStep 1573969 = 1180477) (by norm_num)
theorem B1770589 : Blo 1397518 1770589 := bbase (se 3 (by rfl) ⟨331985, by rfl⟩ : syracuseStep 1770589 = 663971) (by norm_num)
theorem B2098277 : Blo 1397518 2098277 := bbase (se 4 (by rfl) ⟨196713, by rfl⟩ : syracuseStep 2098277 = 393427) (by norm_num)
theorem B1574005 : Blo 1397518 1574005 := bbase (se 5 (by rfl) ⟨73781, by rfl⟩ : syracuseStep 1574005 = 147563) (by norm_num)
theorem B2098301 : Blo 1397518 2098301 := bbase (se 3 (by rfl) ⟨393431, by rfl⟩ : syracuseStep 2098301 = 786863) (by norm_num)
theorem B3146885 : Blo 1397518 3146885 := bbase (se 4 (by rfl) ⟨295020, by rfl⟩ : syracuseStep 3146885 = 590041) (by norm_num)
theorem B2360461 : Blo 1397518 2360461 := bbase (se 3 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 2360461 = 885173) (by norm_num)
theorem B3359893 : Blo 1397518 3359893 := bbase (se 6 (by rfl) ⟨78747, by rfl⟩ : syracuseStep 3359893 = 157495) (by norm_num)
theorem B2098325 : Blo 1397518 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B1574041 : Blo 1397518 1574041 := bbase (se 2 (by rfl) ⟨590265, by rfl⟩ : syracuseStep 1574041 = 1180531) (by norm_num)
theorem B3540125 : Blo 1397518 3540125 := bbase (se 3 (by rfl) ⟨663773, by rfl⟩ : syracuseStep 3540125 = 1327547) (by norm_num)
theorem B2098349 : Blo 1397518 2098349 := bbase (se 3 (by rfl) ⟨393440, by rfl⟩ : syracuseStep 2098349 = 786881) (by norm_num)
theorem B3982517 : Blo 1397518 3982517 := bbase (se 5 (by rfl) ⟨186680, by rfl⟩ : syracuseStep 3982517 = 373361) (by norm_num)
theorem B2655413 : Blo 1397518 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B1574077 : Blo 1397518 1574077 := bbase (se 3 (by rfl) ⟨295139, by rfl⟩ : syracuseStep 1574077 = 590279) (by norm_num)
theorem B2098373 : Blo 1397518 2098373 := bbase (se 4 (by rfl) ⟨196722, by rfl⟩ : syracuseStep 2098373 = 393445) (by norm_num)
theorem B3146957 : Blo 1397518 3146957 := bbase (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) (by norm_num)
theorem B2098397 : Blo 1397518 2098397 := bbase (se 3 (by rfl) ⟨393449, by rfl⟩ : syracuseStep 2098397 = 786899) (by norm_num)
theorem B1574113 : Blo 1397518 1574113 := bbase (se 2 (by rfl) ⟨590292, by rfl⟩ : syracuseStep 1574113 = 1180585) (by norm_num)
theorem B2360549 : Blo 1397518 2360549 := bbase (se 4 (by rfl) ⟨221301, by rfl⟩ : syracuseStep 2360549 = 442603) (by norm_num)
theorem B2098421 : Blo 1397518 2098421 := bbase (se 5 (by rfl) ⟨98363, by rfl⟩ : syracuseStep 2098421 = 196727) (by norm_num)
theorem B1574149 : Blo 1397518 1574149 := bbase (se 4 (by rfl) ⟨147576, by rfl⟩ : syracuseStep 1574149 = 295153) (by norm_num)
theorem B1770761 : Blo 1397518 1770761 := bbase (se 2 (by rfl) ⟨664035, by rfl⟩ : syracuseStep 1770761 = 1328071) (by norm_num)
theorem B2098445 : Blo 1397518 2098445 := bbase (se 3 (by rfl) ⟨393458, by rfl⟩ : syracuseStep 2098445 = 786917) (by norm_num)
theorem B3147029 : Blo 1397518 3147029 := bbase (se 6 (by rfl) ⟨73758, by rfl⟩ : syracuseStep 3147029 = 147517) (by norm_num)
theorem B2098469 : Blo 1397518 2098469 := bbase (se 4 (by rfl) ⟨196731, by rfl⟩ : syracuseStep 2098469 = 393463) (by norm_num)
theorem B1574185 : Blo 1397518 1574185 := bbase (se 2 (by rfl) ⟨590319, by rfl⟩ : syracuseStep 1574185 = 1180639) (by norm_num)
theorem B2098493 : Blo 1397518 2098493 := bbase (se 3 (by rfl) ⟨393467, by rfl⟩ : syracuseStep 2098493 = 786935) (by norm_num)
theorem B1770817 : Blo 1397518 1770817 := bbase (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) (by norm_num)
theorem B7079237 : Blo 1397518 7079237 := bbase (se 4 (by rfl) ⟨663678, by rfl⟩ : syracuseStep 7079237 = 1327357) (by norm_num)
theorem B1574221 : Blo 1397518 1574221 := bbase (se 3 (by rfl) ⟨295166, by rfl⟩ : syracuseStep 1574221 = 590333) (by norm_num)
theorem B2098517 : Blo 1397518 2098517 := bbase (se 12 (by rfl) ⟨768, by rfl⟩ : syracuseStep 2098517 = 1537) (by norm_num)
theorem B10626389 : Blo 1397518 10626389 := bbase (se 12 (by rfl) ⟨3891, by rfl⟩ : syracuseStep 10626389 = 7783) (by norm_num)
theorem B3147101 : Blo 1397518 3147101 := bbase (se 3 (by rfl) ⟨590081, by rfl⟩ : syracuseStep 3147101 = 1180163) (by norm_num)
theorem B2360677 : Blo 1397518 2360677 := bbase (se 4 (by rfl) ⟨221313, by rfl⟩ : syracuseStep 2360677 = 442627) (by norm_num)
theorem B2098541 : Blo 1397518 2098541 := bbase (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) (by norm_num)
theorem B1574257 : Blo 1397518 1574257 := bbase (se 2 (by rfl) ⟨590346, by rfl⟩ : syracuseStep 1574257 = 1180693) (by norm_num)
theorem B5973365 : Blo 1397518 5973365 := bbase (se 5 (by rfl) ⟨280001, by rfl⟩ : syracuseStep 5973365 = 560003) (by norm_num)
theorem B3982709 : Blo 1397518 3982709 := bbase (se 5 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 3982709 = 373379) (by norm_num)
theorem B1992061 : Blo 1397518 1992061 := bbase (se 3 (by rfl) ⟨373511, by rfl⟩ : syracuseStep 1992061 = 747023) (by norm_num)
theorem B2098565 : Blo 1397518 2098565 := bbase (se 4 (by rfl) ⟨196740, by rfl⟩ : syracuseStep 2098565 = 393481) (by norm_num)
theorem B1574293 : Blo 1397518 1574293 := bbase (se 6 (by rfl) ⟨36897, by rfl⟩ : syracuseStep 1574293 = 73795) (by norm_num)
theorem B2098589 : Blo 1397518 2098589 := bbase (se 3 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 2098589 = 786971) (by norm_num)
theorem B1770913 : Blo 1397518 1770913 := bbase (se 2 (by rfl) ⟨664092, by rfl⟩ : syracuseStep 1770913 = 1328185) (by norm_num)
theorem B3147173 : Blo 1397518 3147173 := bbase (se 4 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 3147173 = 590095) (by norm_num)
theorem B2098613 : Blo 1397518 2098613 := bbase (se 5 (by rfl) ⟨98372, by rfl⟩ : syracuseStep 2098613 = 196745) (by norm_num)
theorem B4482485 : Blo 1397518 4482485 := bbase (se 5 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 4482485 = 420233) (by norm_num)
theorem B1574329 : Blo 1397518 1574329 := bbase (se 2 (by rfl) ⟨590373, by rfl⟩ : syracuseStep 1574329 = 1180747) (by norm_num)
theorem B2360765 : Blo 1397518 2360765 := bbase (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) (by norm_num)
theorem B2098637 : Blo 1397518 2098637 := bbase (se 3 (by rfl) ⟨393494, by rfl⟩ : syracuseStep 2098637 = 786989) (by norm_num)
theorem B4720085 : Blo 1397518 4720085 := bbase (se 7 (by rfl) ⟨55313, by rfl⟩ : syracuseStep 4720085 = 110627) (by norm_num)
theorem B15123925 : Blo 1397518 15123925 := bbase (se 7 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 15123925 = 354467) (by norm_num)
theorem B1574365 : Blo 1397518 1574365 := bbase (se 3 (by rfl) ⟨295193, by rfl⟩ : syracuseStep 1574365 = 590387) (by norm_num)
theorem B1492453 : Blo 1397518 1492453 := bbase (se 4 (by rfl) ⟨139917, by rfl⟩ : syracuseStep 1492453 = 279835) (by norm_num)
theorem B2098661 : Blo 1397518 2098661 := bbase (se 4 (by rfl) ⟨196749, by rfl⟩ : syracuseStep 2098661 = 393499) (by norm_num)
theorem B1680869 : Blo 1397518 1680869 := bbase (se 4 (by rfl) ⟨157581, by rfl⟩ : syracuseStep 1680869 = 315163) (by norm_num)
theorem B3147245 : Blo 1397518 3147245 := bbase (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) (by norm_num)
theorem B3540469 : Blo 1397518 3540469 := bbase (se 5 (by rfl) ⟨165959, by rfl⟩ : syracuseStep 3540469 = 331919) (by norm_num)
theorem B2835965 : Blo 1397518 2835965 := bbase (se 3 (by rfl) ⟨531743, by rfl⟩ : syracuseStep 2835965 = 1063487) (by norm_num)
theorem B2098685 : Blo 1397518 2098685 := bbase (se 3 (by rfl) ⟨393503, by rfl⟩ : syracuseStep 2098685 = 787007) (by norm_num)
theorem B1574401 : Blo 1397518 1574401 := bbase (se 2 (by rfl) ⟨590400, by rfl⟩ : syracuseStep 1574401 = 1180801) (by norm_num)
theorem B2098709 : Blo 1397518 2098709 := bbase (se 6 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 2098709 = 98377) (by norm_num)
theorem B1574437 : Blo 1397518 1574437 := bbase (se 4 (by rfl) ⟨147603, by rfl⟩ : syracuseStep 1574437 = 295207) (by norm_num)
theorem B1492525 : Blo 1397518 1492525 := bbase (se 3 (by rfl) ⟨279848, by rfl⟩ : syracuseStep 1492525 = 559697) (by norm_num)
theorem B2098733 : Blo 1397518 2098733 := bbase (se 3 (by rfl) ⟨393512, by rfl⟩ : syracuseStep 2098733 = 787025) (by norm_num)
theorem B3147317 : Blo 1397518 3147317 := bbase (se 5 (by rfl) ⟨147530, by rfl⟩ : syracuseStep 3147317 = 295061) (by norm_num)
theorem B2360893 : Blo 1397518 2360893 := bbase (se 3 (by rfl) ⟨442667, by rfl⟩ : syracuseStep 2360893 = 885335) (by norm_num)
theorem B2098757 : Blo 1397518 2098757 := bbase (se 4 (by rfl) ⟨196758, by rfl⟩ : syracuseStep 2098757 = 393517) (by norm_num)
theorem B1771085 : Blo 1397518 1771085 := bbase (se 3 (by rfl) ⟨332078, by rfl⟩ : syracuseStep 1771085 = 664157) (by norm_num)
theorem B2098781 : Blo 1397518 2098781 := bbase (se 3 (by rfl) ⟨393521, by rfl⟩ : syracuseStep 2098781 = 787043) (by norm_num)
theorem B3540581 : Blo 1397518 3540581 := bbase (se 4 (by rfl) ⟨331929, by rfl⟩ : syracuseStep 3540581 = 663859) (by norm_num)
theorem B2098805 : Blo 1397518 2098805 := bbase (se 5 (by rfl) ⟨98381, by rfl⟩ : syracuseStep 2098805 = 196763) (by norm_num)
theorem B3147389 : Blo 1397518 3147389 := bbase (se 3 (by rfl) ⟨590135, by rfl⟩ : syracuseStep 3147389 = 1180271) (by norm_num)
theorem B1771141 : Blo 1397518 1771141 := bbase (se 4 (by rfl) ⟨166044, by rfl⟩ : syracuseStep 1771141 = 332089) (by norm_num)
theorem B2098829 : Blo 1397518 2098829 := bbase (se 3 (by rfl) ⟨393530, by rfl⟩ : syracuseStep 2098829 = 787061) (by norm_num)
theorem B2360981 : Blo 1397518 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B2098853 : Blo 1397518 2098853 := bbase (se 4 (by rfl) ⟨196767, by rfl⟩ : syracuseStep 2098853 = 393535) (by norm_num)
theorem B2098877 : Blo 1397518 2098877 := bbase (se 3 (by rfl) ⟨393539, by rfl⟩ : syracuseStep 2098877 = 787079) (by norm_num)
theorem B3147461 : Blo 1397518 3147461 := bbase (se 4 (by rfl) ⟨295074, by rfl⟩ : syracuseStep 3147461 = 590149) (by norm_num)
theorem B2098901 : Blo 1397518 2098901 := bbase (se 7 (by rfl) ⟨24596, by rfl⟩ : syracuseStep 2098901 = 49193) (by norm_num)
theorem B1492705 : Blo 1397518 1492705 := bbase (se 2 (by rfl) ⟨559764, by rfl⟩ : syracuseStep 1492705 = 1119529) (by norm_num)
theorem B1771237 : Blo 1397518 1771237 := bbase (se 4 (by rfl) ⟨166053, by rfl⟩ : syracuseStep 1771237 = 332107) (by norm_num)
theorem B2098925 : Blo 1397518 2098925 := bbase (se 3 (by rfl) ⟨393548, by rfl⟩ : syracuseStep 2098925 = 787097) (by norm_num)
theorem B10618613 : Blo 1397518 10618613 := bbase (se 5 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 10618613 = 995495) (by norm_num)
theorem B2098949 : Blo 1397518 2098949 := bbase (se 4 (by rfl) ⟨196776, by rfl⟩ : syracuseStep 2098949 = 393553) (by norm_num)
theorem B3147533 : Blo 1397518 3147533 := bbase (se 3 (by rfl) ⟨590162, by rfl⟩ : syracuseStep 3147533 = 1180325) (by norm_num)
theorem B9086741 : Blo 1397518 9086741 := bbase (se 6 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 9086741 = 425941) (by norm_num)
theorem B2361109 : Blo 1397518 2361109 := bbase (se 6 (by rfl) ⟨55338, by rfl⟩ : syracuseStep 2361109 = 110677) (by norm_num)
theorem B1681177 : Blo 1397518 1681177 := bbase (se 2 (by rfl) ⟨630441, by rfl⟩ : syracuseStep 1681177 = 1260883) (by norm_num)
theorem B2098973 : Blo 1397518 2098973 := bbase (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) (by norm_num)
theorem B3540773 : Blo 1397518 3540773 := bbase (se 4 (by rfl) ⟨331947, by rfl⟩ : syracuseStep 3540773 = 663895) (by norm_num)
theorem B3360565 : Blo 1397518 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B2098997 : Blo 1397518 2098997 := bbase (se 5 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 2098997 = 196781) (by norm_num)
theorem B1681205 : Blo 1397518 1681205 := bbase (se 5 (by rfl) ⟨78806, by rfl⟩ : syracuseStep 1681205 = 157613) (by norm_num)
theorem B2099021 : Blo 1397518 2099021 := bbase (se 3 (by rfl) ⟨393566, by rfl⟩ : syracuseStep 2099021 = 787133) (by norm_num)
theorem B3147605 : Blo 1397518 3147605 := bbase (se 9 (by rfl) ⟨9221, by rfl⟩ : syracuseStep 3147605 = 18443) (by norm_num)
theorem B6055781 : Blo 1397518 6055781 := bbase (se 4 (by rfl) ⟨567729, by rfl⟩ : syracuseStep 6055781 = 1135459) (by norm_num)
theorem B2099045 : Blo 1397518 2099045 := bbase (se 4 (by rfl) ⟨196785, by rfl⟩ : syracuseStep 2099045 = 393571) (by norm_num)
theorem B2361197 : Blo 1397518 2361197 := bbase (se 3 (by rfl) ⟨442724, by rfl⟩ : syracuseStep 2361197 = 885449) (by norm_num)
theorem B2099069 : Blo 1397518 2099069 := bbase (se 3 (by rfl) ⟨393575, by rfl⟩ : syracuseStep 2099069 = 787151) (by norm_num)
theorem B4720517 : Blo 1397518 4720517 := bbase (se 4 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 4720517 = 885097) (by norm_num)
theorem B2099093 : Blo 1397518 2099093 := bbase (se 6 (by rfl) ⟨49197, by rfl⟩ : syracuseStep 2099093 = 98395) (by norm_num)
theorem B3147677 : Blo 1397518 3147677 := bbase (se 3 (by rfl) ⟨590189, by rfl⟩ : syracuseStep 3147677 = 1180379) (by norm_num)
theorem B2656165 : Blo 1397518 2656165 := bbase (se 4 (by rfl) ⟨249015, by rfl⟩ : syracuseStep 2656165 = 498031) (by norm_num)
theorem B2271149 : Blo 1397518 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B2099117 : Blo 1397518 2099117 := bbase (se 3 (by rfl) ⟨393584, by rfl⟩ : syracuseStep 2099117 = 787169) (by norm_num)
theorem B2099141 : Blo 1397518 2099141 := bbase (se 4 (by rfl) ⟨196794, by rfl⟩ : syracuseStep 2099141 = 393589) (by norm_num)
theorem B2099165 : Blo 1397518 2099165 := bbase (se 3 (by rfl) ⟨393593, by rfl⟩ : syracuseStep 2099165 = 787187) (by norm_num)
theorem B3147749 : Blo 1397518 3147749 := bbase (se 4 (by rfl) ⟨295101, by rfl⟩ : syracuseStep 3147749 = 590203) (by norm_num)
theorem B2361325 : Blo 1397518 2361325 := bbase (se 3 (by rfl) ⟨442748, by rfl⟩ : syracuseStep 2361325 = 885497) (by norm_num)
theorem B2099189 : Blo 1397518 2099189 := bbase (se 5 (by rfl) ⟨98399, by rfl⟩ : syracuseStep 2099189 = 196799) (by norm_num)
theorem B2099213 : Blo 1397518 2099213 := bbase (se 3 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 2099213 = 787205) (by norm_num)
theorem B3360797 : Blo 1397518 3360797 := bbase (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) (by norm_num)
theorem B2099237 : Blo 1397518 2099237 := bbase (se 4 (by rfl) ⟨196803, by rfl⟩ : syracuseStep 2099237 = 393607) (by norm_num)
theorem B3147821 : Blo 1397518 3147821 := bbase (se 3 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 3147821 = 1180433) (by norm_num)
theorem B2656309 : Blo 1397518 2656309 := bbase (se 5 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 2656309 = 249029) (by norm_num)
theorem B2099261 : Blo 1397518 2099261 := bbase (se 3 (by rfl) ⟨393611, by rfl⟩ : syracuseStep 2099261 = 787223) (by norm_num)
theorem B2361413 : Blo 1397518 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B3147893 : Blo 1397518 3147893 := bbase (se 5 (by rfl) ⟨147557, by rfl⟩ : syracuseStep 3147893 = 295115) (by norm_num)
theorem B3541117 : Blo 1397518 3541117 := bbase (se 3 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 3541117 = 1327919) (by norm_num)
theorem B1493149 : Blo 1397518 1493149 := bbase (se 3 (by rfl) ⟨279965, by rfl⟩ : syracuseStep 1493149 = 559931) (by norm_num)
theorem B5310629 : Blo 1397518 5310629 := bbase (se 4 (by rfl) ⟨497871, by rfl⟩ : syracuseStep 5310629 = 995743) (by norm_num)
theorem B3360941 : Blo 1397518 3360941 := bbase (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) (by norm_num)
theorem B3147965 : Blo 1397518 3147965 := bbase (se 3 (by rfl) ⟨590243, by rfl⟩ : syracuseStep 3147965 = 1180487) (by norm_num)
theorem B2361541 : Blo 1397518 2361541 := bbase (se 4 (by rfl) ⟨221394, by rfl⟩ : syracuseStep 2361541 = 442789) (by norm_num)
theorem B2656469 : Blo 1397518 2656469 := bbase (se 7 (by rfl) ⟨31130, by rfl⟩ : syracuseStep 2656469 = 62261) (by norm_num)
theorem B3360989 : Blo 1397518 3360989 := bbase (se 3 (by rfl) ⟨630185, by rfl⟩ : syracuseStep 3360989 = 1260371) (by norm_num)
theorem B3188965 : Blo 1397518 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B3541229 : Blo 1397518 3541229 := bbase (se 3 (by rfl) ⟨663980, by rfl⟩ : syracuseStep 3541229 = 1327961) (by norm_num)
theorem B3148037 : Blo 1397518 3148037 := bbase (se 4 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 3148037 = 590257) (by norm_num)
theorem B1493273 : Blo 1397518 1493273 := bbase (se 2 (by rfl) ⟨559977, by rfl⟩ : syracuseStep 1493273 = 1119955) (by norm_num)
theorem B2361629 : Blo 1397518 2361629 := bbase (se 3 (by rfl) ⟨442805, by rfl⟩ : syracuseStep 2361629 = 885611) (by norm_num)
theorem B4720949 : Blo 1397518 4720949 := bbase (se 5 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 4720949 = 442589) (by norm_num)
theorem B3148109 : Blo 1397518 3148109 := bbase (se 3 (by rfl) ⟨590270, by rfl⟩ : syracuseStep 3148109 = 1180541) (by norm_num)
theorem B3983701 : Blo 1397518 3983701 := bbase (se 10 (by rfl) ⟨5835, by rfl⟩ : syracuseStep 3983701 = 11671) (by norm_num)
theorem B2656613 : Blo 1397518 2656613 := bbase (se 4 (by rfl) ⟨249057, by rfl⟩ : syracuseStep 2656613 = 498115) (by norm_num)
theorem B3148181 : Blo 1397518 3148181 := bbase (se 6 (by rfl) ⟨73785, by rfl⟩ : syracuseStep 3148181 = 147571) (by norm_num)
theorem B3541421 : Blo 1397518 3541421 := bbase (se 3 (by rfl) ⟨664016, by rfl⟩ : syracuseStep 3541421 = 1328033) (by norm_num)
theorem B5310917 : Blo 1397518 5310917 := bbase (se 4 (by rfl) ⟨497898, by rfl⟩ : syracuseStep 5310917 = 995797) (by norm_num)
theorem B3148253 : Blo 1397518 3148253 := bbase (se 3 (by rfl) ⟨590297, by rfl⟩ : syracuseStep 3148253 = 1180595) (by norm_num)
theorem B3361277 : Blo 1397518 3361277 := bbase (se 3 (by rfl) ⟨630239, by rfl⟩ : syracuseStep 3361277 = 1260479) (by norm_num)
theorem B1436161 : Blo 1397518 1436161 := bbase (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) (by norm_num)
theorem B1493525 : Blo 1397518 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B3148325 : Blo 1397518 3148325 := bbase (se 4 (by rfl) ⟨295155, by rfl⟩ : syracuseStep 3148325 = 590311) (by norm_num)
theorem B3025493 : Blo 1397518 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B7080533 : Blo 1397518 7080533 := bbase (se 8 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 7080533 = 82975) (by norm_num)
theorem B3148397 : Blo 1397518 3148397 := bbase (se 3 (by rfl) ⟨590324, by rfl⟩ : syracuseStep 3148397 = 1180649) (by norm_num)
theorem B4254373 : Blo 1397518 4254373 := bbase (se 4 (by rfl) ⟨398847, by rfl⟩ : syracuseStep 4254373 = 797695) (by norm_num)
theorem B7277221 : Blo 1397518 7277221 := bbase (se 4 (by rfl) ⟨682239, by rfl⟩ : syracuseStep 7277221 = 1364479) (by norm_num)
theorem B3148469 : Blo 1397518 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B2837197 : Blo 1397518 2837197 := bbase (se 3 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 2837197 = 1063949) (by norm_num)
theorem B4721381 : Blo 1397518 4721381 := bbase (se 4 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 4721381 = 885259) (by norm_num)
theorem B3148541 : Blo 1397518 3148541 := bbase (se 3 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 3148541 = 1180703) (by norm_num)
theorem B3541765 : Blo 1397518 3541765 := bbase (se 4 (by rfl) ⟨332040, by rfl⟩ : syracuseStep 3541765 = 664081) (by norm_num)
theorem B2239301 : Blo 1397518 2239301 := bbase (se 4 (by rfl) ⟨209934, by rfl⟩ : syracuseStep 2239301 = 419869) (by norm_num)
theorem B3148613 : Blo 1397518 3148613 := bbase (se 4 (by rfl) ⟨295182, by rfl⟩ : syracuseStep 3148613 = 590365) (by norm_num)
theorem B3541877 : Blo 1397518 3541877 := bbase (se 5 (by rfl) ⟨166025, by rfl⟩ : syracuseStep 3541877 = 332051) (by norm_num)
theorem B2984845 : Blo 1397518 2984845 := bbase (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) (by norm_num)
theorem B3148685 : Blo 1397518 3148685 := bbase (se 3 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 3148685 = 1180757) (by norm_num)
theorem B2239429 : Blo 1397518 2239429 := bbase (se 4 (by rfl) ⟨209946, by rfl⟩ : syracuseStep 2239429 = 419893) (by norm_num)
theorem B1493969 : Blo 1397518 1493969 := bbase (se 2 (by rfl) ⟨560238, by rfl⟩ : syracuseStep 1493969 = 1120477) (by norm_num)
theorem B3148757 : Blo 1397518 3148757 := bbase (se 7 (by rfl) ⟨36899, by rfl⟩ : syracuseStep 3148757 = 73799) (by norm_num)
theorem B3148829 : Blo 1397518 3148829 := bbase (se 3 (by rfl) ⟨590405, by rfl⟩ : syracuseStep 3148829 = 1180811) (by norm_num)
theorem B3542069 : Blo 1397518 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B3148901 : Blo 1397518 3148901 := bbase (se 4 (by rfl) ⟨295209, by rfl⟩ : syracuseStep 3148901 = 590419) (by norm_num)
theorem B4721813 : Blo 1397518 4721813 := bbase (se 6 (by rfl) ⟨110667, by rfl⟩ : syracuseStep 4721813 = 221335) (by norm_num)
theorem B1494217 : Blo 1397518 1494217 := bbase (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) (by norm_num)
theorem B2985221 : Blo 1397518 2985221 := bbase (se 4 (by rfl) ⟨279864, by rfl⟩ : syracuseStep 2985221 = 559729) (by norm_num)
theorem B11955509 : Blo 1397518 11955509 := bbase (se 5 (by rfl) ⟨560414, by rfl⟩ : syracuseStep 11955509 = 1120829) (by norm_num)
theorem B2239813 : Blo 1397518 2239813 := bbase (se 4 (by rfl) ⟨209982, by rfl⟩ : syracuseStep 2239813 = 419965) (by norm_num)
theorem B5041541 : Blo 1397518 5041541 := bbase (se 4 (by rfl) ⟨472644, by rfl⟩ : syracuseStep 5041541 = 945289) (by norm_num)
theorem B3542413 : Blo 1397518 3542413 := bbase (se 3 (by rfl) ⟨664202, by rfl⟩ : syracuseStep 3542413 = 1328405) (by norm_num)
theorem B3984805 : Blo 1397518 3984805 := bbase (se 4 (by rfl) ⟨373575, by rfl⟩ : syracuseStep 3984805 = 747151) (by norm_num)
theorem B11947445 : Blo 1397518 11947445 := bbase (se 5 (by rfl) ⟨560036, by rfl⟩ : syracuseStep 11947445 = 1120073) (by norm_num)
theorem B3542525 : Blo 1397518 3542525 := bbase (se 3 (by rfl) ⟨664223, by rfl⟩ : syracuseStep 3542525 = 1328447) (by norm_num)
theorem B5041685 : Blo 1397518 5041685 := bbase (se 6 (by rfl) ⟨118164, by rfl⟩ : syracuseStep 5041685 = 236329) (by norm_num)
theorem B2240069 : Blo 1397518 2240069 := bbase (se 4 (by rfl) ⟨210006, by rfl⟩ : syracuseStep 2240069 = 420013) (by norm_num)
theorem B4722245 : Blo 1397518 4722245 := bbase (se 4 (by rfl) ⟨442710, by rfl⟩ : syracuseStep 4722245 = 885421) (by norm_num)
theorem B5312101 : Blo 1397518 5312101 := bbase (se 4 (by rfl) ⟨498009, by rfl⟩ : syracuseStep 5312101 = 996019) (by norm_num)
theorem B2985589 : Blo 1397518 2985589 := bbase (se 5 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 2985589 = 279899) (by norm_num)
theorem B7966421 : Blo 1397518 7966421 := bbase (se 7 (by rfl) ⟨93356, by rfl⟩ : syracuseStep 7966421 = 186713) (by norm_num)
theorem B6377237 : Blo 1397518 6377237 := bbase (se 6 (by rfl) ⟨149466, by rfl⟩ : syracuseStep 6377237 = 298933) (by norm_num)
theorem B7081829 : Blo 1397518 7081829 := bbase (se 4 (by rfl) ⟨663921, by rfl⟩ : syracuseStep 7081829 = 1327843) (by norm_num)
theorem B5312405 : Blo 1397518 5312405 := bbase (se 6 (by rfl) ⟨124509, by rfl⟩ : syracuseStep 5312405 = 249019) (by norm_num)
theorem B3026885 : Blo 1397518 3026885 := bbase (se 4 (by rfl) ⟨283770, by rfl⟩ : syracuseStep 3026885 = 567541) (by norm_num)
theorem B2518997 : Blo 1397518 2518997 := bbase (se 7 (by rfl) ⟨29519, by rfl⟩ : syracuseStep 2518997 = 59039) (by norm_num)
theorem B4722677 : Blo 1397518 4722677 := bbase (se 5 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 4722677 = 442751) (by norm_num)
theorem B1593725 : Blo 1397518 1593725 := bbase (se 3 (by rfl) ⟨298823, by rfl⟩ : syracuseStep 1593725 = 597647) (by norm_num)
theorem B1593761 : Blo 1397518 1593761 := bbase (se 2 (by rfl) ⟨597660, by rfl⟩ : syracuseStep 1593761 = 1195321) (by norm_num)
theorem B4723109 : Blo 1397518 4723109 := bbase (se 4 (by rfl) ⟨442791, by rfl⟩ : syracuseStep 4723109 = 885583) (by norm_num)
theorem B2240941 : Blo 1397518 2240941 := bbase (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) (by norm_num)
theorem B2126341 : Blo 1397518 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B2241037 : Blo 1397518 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B1888805 : Blo 1397518 1888805 := bbase (se 4 (by rfl) ⟨177075, by rfl⟩ : syracuseStep 1888805 = 354151) (by norm_num)
theorem B5976661 : Blo 1397518 5976661 := bbase (se 8 (by rfl) ⟨35019, by rfl⟩ : syracuseStep 5976661 = 70039) (by norm_num)
theorem B2241197 : Blo 1397518 2241197 := bbase (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) (by norm_num)
theorem B8966837 : Blo 1397518 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B1594117 : Blo 1397518 1594117 := bbase (se 4 (by rfl) ⟨149448, by rfl⟩ : syracuseStep 1594117 = 298897) (by norm_num)
theorem B4477781 : Blo 1397518 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B3232613 : Blo 1397518 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B7967605 : Blo 1397518 7967605 := bbase (se 5 (by rfl) ⟨373481, by rfl⟩ : syracuseStep 7967605 = 746963) (by norm_num)
theorem B1889173 : Blo 1397518 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B2184197 : Blo 1397518 2184197 := bbase (se 4 (by rfl) ⟨204768, by rfl⟩ : syracuseStep 2184197 = 409537) (by norm_num)
theorem B14357557 : Blo 1397518 14357557 := bbase (se 5 (by rfl) ⟨673010, by rfl⟩ : syracuseStep 14357557 = 1346021) (by norm_num)
theorem B1594445 : Blo 1397518 1594445 := bbase (se 3 (by rfl) ⟨298958, by rfl⟩ : syracuseStep 1594445 = 597917) (by norm_num)
theorem B2987093 : Blo 1397518 2987093 := bbase (se 8 (by rfl) ⟨17502, by rfl⟩ : syracuseStep 2987093 = 35005) (by norm_num)
theorem B7083125 : Blo 1397518 7083125 := bbase (se 5 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 7083125 = 664043) (by norm_num)
theorem B1889453 : Blo 1397518 1889453 := bbase (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) (by norm_num)
theorem B1594573 : Blo 1397518 1594573 := bbase (se 3 (by rfl) ⟨298982, by rfl⟩ : syracuseStep 1594573 = 597965) (by norm_num)
theorem B2987237 : Blo 1397518 2987237 := bbase (se 4 (by rfl) ⟨280053, by rfl⟩ : syracuseStep 2987237 = 560107) (by norm_num)
theorem B2553229 : Blo 1397518 2553229 := bbase (se 3 (by rfl) ⟨478730, by rfl⟩ : syracuseStep 2553229 = 957461) (by norm_num)
theorem B18175445 : Blo 1397518 18175445 := bbase (se 7 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 18175445 = 425987) (by norm_num)
theorem B2692597 : Blo 1397518 2692597 := bbase (se 5 (by rfl) ⟨126215, by rfl⟩ : syracuseStep 2692597 = 252431) (by norm_num)
theorem B7075349 : Blo 1397518 7075349 := bbase (se 6 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 7075349 = 331657) (by norm_num)
theorem B2987597 : Blo 1397518 2987597 := bbase (se 3 (by rfl) ⟨560174, by rfl⟩ : syracuseStep 2987597 = 1120349) (by norm_num)
theorem B2127557 : Blo 1397518 2127557 := bbase (se 4 (by rfl) ⟨199458, by rfl⟩ : syracuseStep 2127557 = 398917) (by norm_num)
theorem B2127581 : Blo 1397518 2127581 := bbase (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) (by norm_num)
theorem B1890373 : Blo 1397518 1890373 := bbase (se 4 (by rfl) ⟨177222, by rfl⟩ : syracuseStep 1890373 = 354445) (by norm_num)
theorem B4716629 : Blo 1397518 4716629 := bbase (se 8 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 4716629 = 55273) (by norm_num)
theorem B5380181 : Blo 1397518 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B3782789 : Blo 1397518 3782789 := bbase (se 4 (by rfl) ⟨354636, by rfl⟩ : syracuseStep 3782789 = 709273) (by norm_num)
theorem B5306741 : Blo 1397518 5306741 := bbase (se 5 (by rfl) ⟨248753, by rfl⟩ : syracuseStep 5306741 = 497507) (by norm_num)
theorem B7084421 : Blo 1397518 7084421 := bbase (se 4 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 7084421 = 1328329) (by norm_num)
theorem B2988485 : Blo 1397518 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B1513937 : Blo 1397518 1513937 := bbase (se 2 (by rfl) ⟨567726, by rfl⟩ : syracuseStep 1513937 = 1135453) (by norm_num)
theorem B4717061 : Blo 1397518 4717061 := bbase (se 4 (by rfl) ⟨442224, by rfl⟩ : syracuseStep 4717061 = 884449) (by norm_num)
theorem B22682197 : Blo 1397518 22682197 := bbase (se 8 (by rfl) ⟨132903, by rfl⟩ : syracuseStep 22682197 = 265807) (by norm_num)
theorem B6380117 : Blo 1397518 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B3537533 : Blo 1397518 3537533 := bbase (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) (by norm_num)
theorem B5307029 : Blo 1397518 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B1514137 : Blo 1397518 1514137 := bbase (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) (by norm_num)
theorem B12114613 : Blo 1397518 12114613 := bbase (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) (by norm_num)
theorem B2988733 : Blo 1397518 2988733 := bbase (se 3 (by rfl) ⟨560387, by rfl⟩ : syracuseStep 2988733 = 1120775) (by norm_num)
theorem B3144437 : Blo 1397518 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B7076645 : Blo 1397518 7076645 := bbase (se 4 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 7076645 = 1326871) (by norm_num)
theorem B7969589 : Blo 1397518 7969589 := bbase (se 5 (by rfl) ⟨373574, by rfl⟩ : syracuseStep 7969589 = 747149) (by norm_num)
theorem B10918709 : Blo 1397518 10918709 := bbase (se 5 (by rfl) ⟨511814, by rfl⟩ : syracuseStep 10918709 = 1023629) (by norm_num)
theorem B3144509 : Blo 1397518 3144509 := bbase (se 3 (by rfl) ⟨589595, by rfl⟩ : syracuseStep 3144509 = 1179191) (by norm_num)
theorem B3144581 : Blo 1397518 3144581 := bbase (se 4 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 3144581 = 589609) (by norm_num)
theorem B4717493 : Blo 1397518 4717493 := bbase (se 5 (by rfl) ⟨221132, by rfl⟩ : syracuseStep 4717493 = 442265) (by norm_num)
theorem B3144653 : Blo 1397518 3144653 := bbase (se 3 (by rfl) ⟨589622, by rfl⟩ : syracuseStep 3144653 = 1179245) (by norm_num)
theorem B3537877 : Blo 1397518 3537877 := bbase (se 7 (by rfl) ⟨41459, by rfl⟩ : syracuseStep 3537877 = 82919) (by norm_num)
theorem B2653165 : Blo 1397518 2653165 := bbase (se 3 (by rfl) ⟨497468, by rfl⟩ : syracuseStep 2653165 = 994937) (by norm_num)
theorem B3144725 : Blo 1397518 3144725 := bbase (se 6 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 3144725 = 147409) (by norm_num)
theorem B3537989 : Blo 1397518 3537989 := bbase (se 4 (by rfl) ⟨331686, by rfl⟩ : syracuseStep 3537989 = 663373) (by norm_num)
theorem B3144797 : Blo 1397518 3144797 := bbase (se 3 (by rfl) ⟨589649, by rfl⟩ : syracuseStep 3144797 = 1179299) (by norm_num)
theorem B5037157 : Blo 1397518 5037157 := bbase (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) (by norm_num)
theorem B2358389 : Blo 1397518 2358389 := bbase (se 5 (by rfl) ⟨110549, by rfl⟩ : syracuseStep 2358389 = 221099) (by norm_num)
theorem B3939445 : Blo 1397518 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B4603013 : Blo 1397518 4603013 := bbase (se 4 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 4603013 = 863065) (by norm_num)
theorem B2096285 : Blo 1397518 2096285 := bbase (se 3 (by rfl) ⟨393053, by rfl⟩ : syracuseStep 2096285 = 786107) (by norm_num)
theorem B3144869 : Blo 1397518 3144869 := bbase (se 4 (by rfl) ⟨294831, by rfl⟩ : syracuseStep 3144869 = 589663) (by norm_num)
theorem B2096309 : Blo 1397518 2096309 := bbase (se 5 (by rfl) ⟨98264, by rfl⟩ : syracuseStep 2096309 = 196529) (by norm_num)
theorem B2096333 : Blo 1397518 2096333 := bbase (se 3 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 2096333 = 786125) (by norm_num)
theorem B2096357 : Blo 1397518 2096357 := bbase (se 4 (by rfl) ⟨196533, by rfl⟩ : syracuseStep 2096357 = 393067) (by norm_num)
theorem B3144941 : Blo 1397518 3144941 := bbase (se 3 (by rfl) ⟨589676, by rfl⟩ : syracuseStep 3144941 = 1179353) (by norm_num)
theorem B2358517 : Blo 1397518 2358517 := bbase (se 5 (by rfl) ⟨110555, by rfl⟩ : syracuseStep 2358517 = 221111) (by norm_num)
theorem B2096381 : Blo 1397518 2096381 := bbase (se 3 (by rfl) ⟨393071, by rfl⟩ : syracuseStep 2096381 = 786143) (by norm_num)
theorem B3538181 : Blo 1397518 3538181 := bbase (se 4 (by rfl) ⟨331704, by rfl⟩ : syracuseStep 3538181 = 663409) (by norm_num)
theorem B2096405 : Blo 1397518 2096405 := bbase (se 6 (by rfl) ⟨49134, by rfl⟩ : syracuseStep 2096405 = 98269) (by norm_num)
theorem B2653469 : Blo 1397518 2653469 := bbase (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) (by norm_num)
theorem B2096429 : Blo 1397518 2096429 := bbase (se 3 (by rfl) ⟨393080, by rfl⟩ : syracuseStep 2096429 = 786161) (by norm_num)
theorem B3145013 : Blo 1397518 3145013 := bbase (se 5 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 3145013 = 294845) (by norm_num)
theorem B2096453 : Blo 1397518 2096453 := bbase (se 4 (by rfl) ⟨196542, by rfl⟩ : syracuseStep 2096453 = 393085) (by norm_num)
theorem B1989965 : Blo 1397518 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B2358605 : Blo 1397518 2358605 := bbase (se 3 (by rfl) ⟨442238, by rfl⟩ : syracuseStep 2358605 = 884477) (by norm_num)
theorem B2096477 : Blo 1397518 2096477 := bbase (se 3 (by rfl) ⟨393089, by rfl⟩ : syracuseStep 2096477 = 786179) (by norm_num)
theorem B4717925 : Blo 1397518 4717925 := bbase (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) (by norm_num)
theorem B1768817 : Blo 1397518 1768817 := bbase (se 2 (by rfl) ⟨663306, by rfl⟩ : syracuseStep 1768817 = 1326613) (by norm_num)
theorem B2096501 : Blo 1397518 2096501 := bbase (se 5 (by rfl) ⟨98273, by rfl⟩ : syracuseStep 2096501 = 196547) (by norm_num)
theorem B3145085 : Blo 1397518 3145085 := bbase (se 3 (by rfl) ⟨589703, by rfl⟩ : syracuseStep 3145085 = 1179407) (by norm_num)
theorem B2096525 : Blo 1397518 2096525 := bbase (se 3 (by rfl) ⟨393098, by rfl⟩ : syracuseStep 2096525 = 786197) (by norm_num)
theorem B1572241 : Blo 1397518 1572241 := bbase (se 2 (by rfl) ⟨589590, by rfl⟩ : syracuseStep 1572241 = 1179181) (by norm_num)
theorem B1990045 : Blo 1397518 1990045 := bbase (se 3 (by rfl) ⟨373133, by rfl⟩ : syracuseStep 1990045 = 746267) (by norm_num)
theorem B2096549 : Blo 1397518 2096549 := bbase (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) (by norm_num)
theorem B1768873 : Blo 1397518 1768873 := bbase (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) (by norm_num)
theorem B1572277 : Blo 1397518 1572277 := bbase (se 5 (by rfl) ⟨73700, by rfl⟩ : syracuseStep 1572277 = 147401) (by norm_num)
theorem B2096573 : Blo 1397518 2096573 := bbase (se 3 (by rfl) ⟨393107, by rfl⟩ : syracuseStep 2096573 = 786215) (by norm_num)
theorem B3145157 : Blo 1397518 3145157 := bbase (se 4 (by rfl) ⟨294858, by rfl⟩ : syracuseStep 3145157 = 589717) (by norm_num)
theorem B2358733 : Blo 1397518 2358733 := bbase (se 3 (by rfl) ⟨442262, by rfl⟩ : syracuseStep 2358733 = 884525) (by norm_num)
theorem B2096597 : Blo 1397518 2096597 := bbase (se 7 (by rfl) ⟨24569, by rfl⟩ : syracuseStep 2096597 = 49139) (by norm_num)
theorem B1572313 : Blo 1397518 1572313 := bbase (se 2 (by rfl) ⟨589617, by rfl⟩ : syracuseStep 1572313 = 1179235) (by norm_num)
theorem B2096621 : Blo 1397518 2096621 := bbase (se 3 (by rfl) ⟨393116, by rfl⟩ : syracuseStep 2096621 = 786233) (by norm_num)
theorem B1572349 : Blo 1397518 1572349 := bbase (se 3 (by rfl) ⟨294815, by rfl⟩ : syracuseStep 1572349 = 589631) (by norm_num)
theorem B2096645 : Blo 1397518 2096645 := bbase (se 4 (by rfl) ⟨196560, by rfl⟩ : syracuseStep 2096645 = 393121) (by norm_num)
theorem B1768969 : Blo 1397518 1768969 := bbase (se 2 (by rfl) ⟨663363, by rfl⟩ : syracuseStep 1768969 = 1326727) (by norm_num)
theorem B3145229 : Blo 1397518 3145229 := bbase (se 3 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 3145229 = 1179461) (by norm_num)
theorem B1990165 : Blo 1397518 1990165 := bbase (se 6 (by rfl) ⟨46644, by rfl⟩ : syracuseStep 1990165 = 93289) (by norm_num)
theorem B2096669 : Blo 1397518 2096669 := bbase (se 3 (by rfl) ⟨393125, by rfl⟩ : syracuseStep 2096669 = 786251) (by norm_num)
theorem B1572385 : Blo 1397518 1572385 := bbase (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) (by norm_num)
theorem B2358821 : Blo 1397518 2358821 := bbase (se 4 (by rfl) ⟨221139, by rfl⟩ : syracuseStep 2358821 = 442279) (by norm_num)
theorem B2096693 : Blo 1397518 2096693 := bbase (se 5 (by rfl) ⟨98282, by rfl⟩ : syracuseStep 2096693 = 196565) (by norm_num)
theorem B1572421 : Blo 1397518 1572421 := bbase (se 4 (by rfl) ⟨147414, by rfl⟩ : syracuseStep 1572421 = 294829) (by norm_num)
theorem B2096717 : Blo 1397518 2096717 := bbase (se 3 (by rfl) ⟨393134, by rfl⟩ : syracuseStep 2096717 = 786269) (by norm_num)
theorem B3145301 : Blo 1397518 3145301 := bbase (se 8 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 3145301 = 36859) (by norm_num)
theorem B3538525 : Blo 1397518 3538525 := bbase (se 3 (by rfl) ⟨663473, by rfl⟩ : syracuseStep 3538525 = 1326947) (by norm_num)
theorem B2096741 : Blo 1397518 2096741 := bbase (se 4 (by rfl) ⟨196569, by rfl⟩ : syracuseStep 2096741 = 393139) (by norm_num)
theorem B1572457 : Blo 1397518 1572457 := bbase (se 2 (by rfl) ⟨589671, by rfl⟩ : syracuseStep 1572457 = 1179343) (by norm_num)
theorem B1990261 : Blo 1397518 1990261 := bbase (se 5 (by rfl) ⟨93293, by rfl⟩ : syracuseStep 1990261 = 186587) (by norm_num)
theorem B1638005 : Blo 1397518 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B2096765 : Blo 1397518 2096765 := bbase (se 3 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 2096765 = 786287) (by norm_num)
theorem B3980933 : Blo 1397518 3980933 := bbase (se 4 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 3980933 = 746425) (by norm_num)
theorem B5971589 : Blo 1397518 5971589 := bbase (se 4 (by rfl) ⟨559836, by rfl⟩ : syracuseStep 5971589 = 1119673) (by norm_num)
theorem B1793669 : Blo 1397518 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B1572493 : Blo 1397518 1572493 := bbase (se 3 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 1572493 = 589685) (by norm_num)
theorem B2096789 : Blo 1397518 2096789 := bbase (se 6 (by rfl) ⟨49143, by rfl⟩ : syracuseStep 2096789 = 98287) (by norm_num)
theorem B3145373 : Blo 1397518 3145373 := bbase (se 3 (by rfl) ⟨589757, by rfl⟩ : syracuseStep 3145373 = 1179515) (by norm_num)
theorem B2358949 : Blo 1397518 2358949 := bbase (se 4 (by rfl) ⟨221151, by rfl⟩ : syracuseStep 2358949 = 442303) (by norm_num)
theorem B2096813 : Blo 1397518 2096813 := bbase (se 3 (by rfl) ⟨393152, by rfl⟩ : syracuseStep 2096813 = 786305) (by norm_num)
theorem B1572529 : Blo 1397518 1572529 := bbase (se 2 (by rfl) ⟨589698, by rfl⟩ : syracuseStep 1572529 = 1179397) (by norm_num)
theorem B1769141 : Blo 1397518 1769141 := bbase (se 5 (by rfl) ⟨82928, by rfl⟩ : syracuseStep 1769141 = 165857) (by norm_num)
theorem B2096837 : Blo 1397518 2096837 := bbase (se 4 (by rfl) ⟨196578, by rfl⟩ : syracuseStep 2096837 = 393157) (by norm_num)
theorem B3538637 : Blo 1397518 3538637 := bbase (se 3 (by rfl) ⟨663494, by rfl⟩ : syracuseStep 3538637 = 1326989) (by norm_num)
theorem B1572565 : Blo 1397518 1572565 := bbase (se 7 (by rfl) ⟨18428, by rfl⟩ : syracuseStep 1572565 = 36857) (by norm_num)
theorem B2096861 : Blo 1397518 2096861 := bbase (se 3 (by rfl) ⟨393161, by rfl⟩ : syracuseStep 2096861 = 786323) (by norm_num)
theorem B3145445 : Blo 1397518 3145445 := bbase (se 4 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 3145445 = 589771) (by norm_num)
theorem B1769197 : Blo 1397518 1769197 := bbase (se 3 (by rfl) ⟨331724, by rfl⟩ : syracuseStep 1769197 = 663449) (by norm_num)
theorem B1793773 : Blo 1397518 1793773 := bbase (se 3 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 1793773 = 672665) (by norm_num)
theorem B2096885 : Blo 1397518 2096885 := bbase (se 5 (by rfl) ⟨98291, by rfl⟩ : syracuseStep 2096885 = 196583) (by norm_num)
theorem B1572601 : Blo 1397518 1572601 := bbase (se 2 (by rfl) ⟨589725, by rfl⟩ : syracuseStep 1572601 = 1179451) (by norm_num)
theorem B2359037 : Blo 1397518 2359037 := bbase (se 3 (by rfl) ⟨442319, by rfl⟩ : syracuseStep 2359037 = 884639) (by norm_num)
theorem B2096909 : Blo 1397518 2096909 := bbase (se 3 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 2096909 = 786341) (by norm_num)
theorem B4718357 : Blo 1397518 4718357 := bbase (se 6 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 4718357 = 221173) (by norm_num)
theorem B1572637 : Blo 1397518 1572637 := bbase (se 3 (by rfl) ⟨294869, by rfl⟩ : syracuseStep 1572637 = 589739) (by norm_num)
theorem B2096933 : Blo 1397518 2096933 := bbase (se 4 (by rfl) ⟨196587, by rfl⟩ : syracuseStep 2096933 = 393175) (by norm_num)
theorem B3145517 : Blo 1397518 3145517 := bbase (se 3 (by rfl) ⟨589784, by rfl⟩ : syracuseStep 3145517 = 1179569) (by norm_num)
theorem B2154293 : Blo 1397518 2154293 := bbase (se 5 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 2154293 = 201965) (by norm_num)
theorem B5308213 : Blo 1397518 5308213 := bbase (se 5 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 5308213 = 497645) (by norm_num)
theorem B2096957 : Blo 1397518 2096957 := bbase (se 3 (by rfl) ⟨393179, by rfl⟩ : syracuseStep 2096957 = 786359) (by norm_num)
theorem B2834237 : Blo 1397518 2834237 := bbase (se 3 (by rfl) ⟨531419, by rfl⟩ : syracuseStep 2834237 = 1062839) (by norm_num)
theorem B1572673 : Blo 1397518 1572673 := bbase (se 2 (by rfl) ⟨589752, by rfl⟩ : syracuseStep 1572673 = 1179505) (by norm_num)
theorem B1769293 : Blo 1397518 1769293 := bbase (se 3 (by rfl) ⟨331742, by rfl⟩ : syracuseStep 1769293 = 663485) (by norm_num)
theorem B6717269 : Blo 1397518 6717269 := bbase (se 9 (by rfl) ⟨19679, by rfl⟩ : syracuseStep 6717269 = 39359) (by norm_num)
theorem B2096981 : Blo 1397518 2096981 := bbase (se 9 (by rfl) ⟨6143, by rfl⟩ : syracuseStep 2096981 = 12287) (by norm_num)
theorem B1572709 : Blo 1397518 1572709 := bbase (se 4 (by rfl) ⟨147441, by rfl⟩ : syracuseStep 1572709 = 294883) (by norm_num)
theorem B2097005 : Blo 1397518 2097005 := bbase (se 3 (by rfl) ⟨393188, by rfl⟩ : syracuseStep 2097005 = 786377) (by norm_num)
theorem B3145589 : Blo 1397518 3145589 := bbase (se 5 (by rfl) ⟨147449, by rfl⟩ : syracuseStep 3145589 = 294899) (by norm_num)
theorem B2359165 : Blo 1397518 2359165 := bbase (se 3 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 2359165 = 884687) (by norm_num)
theorem B2097029 : Blo 1397518 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B1572745 : Blo 1397518 1572745 := bbase (se 2 (by rfl) ⟨589779, by rfl⟩ : syracuseStep 1572745 = 1179559) (by norm_num)
theorem B3538829 : Blo 1397518 3538829 := bbase (se 3 (by rfl) ⟨663530, by rfl⟩ : syracuseStep 3538829 = 1327061) (by norm_num)
theorem B19136405 : Blo 1397518 19136405 := bbase (se 6 (by rfl) ⟨448509, by rfl⟩ : syracuseStep 19136405 = 897019) (by norm_num)
theorem B2097053 : Blo 1397518 2097053 := bbase (se 3 (by rfl) ⟨393197, by rfl⟩ : syracuseStep 2097053 = 786395) (by norm_num)
theorem B5971877 : Blo 1397518 5971877 := bbase (se 4 (by rfl) ⟨559863, by rfl⟩ : syracuseStep 5971877 = 1119727) (by norm_num)
theorem B1572781 : Blo 1397518 1572781 := bbase (se 3 (by rfl) ⟨294896, by rfl⟩ : syracuseStep 1572781 = 589793) (by norm_num)
theorem B2097077 : Blo 1397518 2097077 := bbase (se 5 (by rfl) ⟨98300, by rfl⟩ : syracuseStep 2097077 = 196601) (by norm_num)
theorem B3145661 : Blo 1397518 3145661 := bbase (se 3 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 3145661 = 1179623) (by norm_num)
theorem B2097101 : Blo 1397518 2097101 := bbase (se 3 (by rfl) ⟨393206, by rfl⟩ : syracuseStep 2097101 = 786413) (by norm_num)
theorem B1572817 : Blo 1397518 1572817 := bbase (se 2 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 1572817 = 1179613) (by norm_num)
theorem B2801621 : Blo 1397518 2801621 := bbase (se 7 (by rfl) ⟨32831, by rfl⟩ : syracuseStep 2801621 = 65663) (by norm_num)
theorem B2359253 : Blo 1397518 2359253 := bbase (se 7 (by rfl) ⟨27647, by rfl⟩ : syracuseStep 2359253 = 55295) (by norm_num)
theorem B2097125 : Blo 1397518 2097125 := bbase (se 4 (by rfl) ⟨196605, by rfl⟩ : syracuseStep 2097125 = 393211) (by norm_num)
theorem B1679341 : Blo 1397518 1679341 := bbase (se 3 (by rfl) ⟨314876, by rfl⟩ : syracuseStep 1679341 = 629753) (by norm_num)
theorem B1572853 : Blo 1397518 1572853 := bbase (se 5 (by rfl) ⟨73727, by rfl⟩ : syracuseStep 1572853 = 147455) (by norm_num)
theorem B1769465 : Blo 1397518 1769465 := bbase (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) (by norm_num)
theorem B2097149 : Blo 1397518 2097149 := bbase (se 3 (by rfl) ⟨393215, by rfl⟩ : syracuseStep 2097149 = 786431) (by norm_num)
theorem B2097155 : Blo 1397518 2097155 := bstep (se 1 (by rfl) ⟨1572866, by rfl⟩ : syracuseStep 2097155 = 3145733) B3145733
theorem B3538961 : Blo 1397518 3538961 := bstep (se 2 (by rfl) ⟨1327110, by rfl⟩ : syracuseStep 3538961 = 2654221) B2654221
theorem B2097185 : Blo 1397518 2097185 := bstep (se 2 (by rfl) ⟨786444, by rfl⟩ : syracuseStep 2097185 = 1572889) B1572889
theorem B4718627 : Blo 1397518 4718627 := bstep (se 1 (by rfl) ⟨3538970, by rfl⟩ : syracuseStep 4718627 = 7077941) B7077941
theorem B2097203 : Blo 1397518 2097203 := bstep (se 1 (by rfl) ⟨1572902, by rfl⟩ : syracuseStep 2097203 = 3145805) B3145805
theorem B23298101 : Blo 1397518 23298101 := bstep (se 5 (by rfl) ⟨1092098, by rfl⟩ : syracuseStep 23298101 = 2184197) B2184197
theorem B2359361 : Blo 1397518 2359361 := bstep (se 2 (by rfl) ⟨884760, by rfl⟩ : syracuseStep 2359361 = 1769521) B1769521
theorem B3539011 : Blo 1397518 3539011 := bstep (se 1 (by rfl) ⟨2654258, by rfl⟩ : syracuseStep 3539011 = 5308517) B5308517
theorem B11952197 : Blo 1397518 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2097233 : Blo 1397518 2097233 := bstep (se 2 (by rfl) ⟨786462, by rfl⟩ : syracuseStep 2097233 = 1572925) B1572925
theorem B2097251 : Blo 1397518 2097251 := bstep (se 1 (by rfl) ⟨1572938, by rfl⟩ : syracuseStep 2097251 = 3145877) B3145877
theorem B3145841 : Blo 1397518 3145841 := bstep (se 2 (by rfl) ⟨1179690, by rfl⟩ : syracuseStep 3145841 = 2359381) B2359381
theorem B1572979 : Blo 1397518 1572979 := bstep (se 1 (by rfl) ⟨1179734, by rfl⟩ : syracuseStep 1572979 = 2359469) B2359469
theorem B2097281 : Blo 1397518 2097281 := bstep (se 2 (by rfl) ⟨786480, by rfl⟩ : syracuseStep 2097281 = 1572961) B1572961
theorem B3145859 : Blo 1397518 3145859 := bstep (se 1 (by rfl) ⟨2359394, by rfl⟩ : syracuseStep 3145859 = 4718789) B4718789
theorem B2097299 : Blo 1397518 2097299 := bstep (se 1 (by rfl) ⟨1572974, by rfl⟩ : syracuseStep 2097299 = 3145949) B3145949
theorem B2097329 : Blo 1397518 2097329 := bstep (se 2 (by rfl) ⟨786498, by rfl⟩ : syracuseStep 2097329 = 1572997) B1572997
theorem B2359489 : Blo 1397518 2359489 := bstep (se 2 (by rfl) ⟨884808, by rfl⟩ : syracuseStep 2359489 = 1769617) B1769617
theorem B2097347 : Blo 1397518 2097347 := bstep (se 1 (by rfl) ⟨1573010, by rfl⟩ : syracuseStep 2097347 = 3146021) B3146021
theorem B4251853 : Blo 1397518 4251853 := bstep (se 3 (by rfl) ⟨797222, by rfl⟩ : syracuseStep 4251853 = 1594445) B1594445
theorem B3539153 : Blo 1397518 3539153 := bstep (se 2 (by rfl) ⟨1327182, by rfl⟩ : syracuseStep 3539153 = 2654365) B2654365
theorem B1990865 : Blo 1397518 1990865 := bstep (se 2 (by rfl) ⟨746574, by rfl⟩ : syracuseStep 1990865 = 1493149) B1493149
theorem B1769683 : Blo 1397518 1769683 := bstep (se 1 (by rfl) ⟨1327262, by rfl⟩ : syracuseStep 1769683 = 2654525) B2654525
theorem B2097377 : Blo 1397518 2097377 := bstep (se 2 (by rfl) ⟨786516, by rfl⟩ : syracuseStep 2097377 = 1573033) B1573033
theorem B2359523 : Blo 1397518 2359523 := bstep (se 1 (by rfl) ⟨1769642, by rfl⟩ : syracuseStep 2359523 = 3539285) B3539285
theorem B2097395 : Blo 1397518 2097395 := bstep (se 1 (by rfl) ⟨1573046, by rfl⟩ : syracuseStep 2097395 = 3146093) B3146093
theorem B1573123 : Blo 1397518 1573123 := bstep (se 1 (by rfl) ⟨1179842, by rfl⟩ : syracuseStep 1573123 = 2359685) B2359685
theorem B5308685 : Blo 1397518 5308685 := bstep (se 3 (by rfl) ⟨995378, by rfl⟩ : syracuseStep 5308685 = 1990757) B1990757
theorem B2097425 : Blo 1397518 2097425 := bstep (se 2 (by rfl) ⟨786534, by rfl⟩ : syracuseStep 2097425 = 1573069) B1573069
theorem B2097443 : Blo 1397518 2097443 := bstep (se 1 (by rfl) ⟨1573082, by rfl⟩ : syracuseStep 2097443 = 3146165) B3146165
theorem B4784429 : Blo 1397518 4784429 := bstep (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) B1794161
theorem B4718897 : Blo 1397518 4718897 := bstep (se 2 (by rfl) ⟨1769586, by rfl⟩ : syracuseStep 4718897 = 3539173) B3539173
theorem B4251953 : Blo 1397518 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B1769779 : Blo 1397518 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B2097473 : Blo 1397518 2097473 := bstep (se 2 (by rfl) ⟨786552, by rfl⟩ : syracuseStep 2097473 = 1573105) B1573105
theorem B2097491 : Blo 1397518 2097491 := bstep (se 1 (by rfl) ⟨1573118, by rfl⟩ : syracuseStep 2097491 = 3146237) B3146237
theorem B2359651 : Blo 1397518 2359651 := bstep (se 1 (by rfl) ⟨1769738, by rfl⟩ : syracuseStep 2359651 = 3539477) B3539477
theorem B2097521 : Blo 1397518 2097521 := bstep (se 2 (by rfl) ⟨786570, by rfl⟩ : syracuseStep 2097521 = 1573141) B1573141
theorem B2097539 : Blo 1397518 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B3146129 : Blo 1397518 3146129 := bstep (se 2 (by rfl) ⟨1179798, by rfl⟩ : syracuseStep 3146129 = 2359597) B2359597
theorem B1573267 : Blo 1397518 1573267 := bstep (se 1 (by rfl) ⟨1179950, by rfl⟩ : syracuseStep 1573267 = 2359901) B2359901
theorem B2097569 : Blo 1397518 2097569 := bstep (se 2 (by rfl) ⟨786588, by rfl⟩ : syracuseStep 2097569 = 1573177) B1573177
theorem B3146147 : Blo 1397518 3146147 := bstep (se 1 (by rfl) ⟨2359610, by rfl⟩ : syracuseStep 3146147 = 4719221) B4719221
theorem B2097587 : Blo 1397518 2097587 := bstep (se 1 (by rfl) ⟨1573190, by rfl⟩ : syracuseStep 2097587 = 3146381) B3146381
theorem B5038541 : Blo 1397518 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B2097617 : Blo 1397518 2097617 := bstep (se 2 (by rfl) ⟨786606, by rfl⟩ : syracuseStep 2097617 = 1573213) B1573213
theorem B2097635 : Blo 1397518 2097635 := bstep (se 1 (by rfl) ⟨1573226, by rfl⟩ : syracuseStep 2097635 = 3146453) B3146453
theorem B2359793 : Blo 1397518 2359793 := bstep (se 2 (by rfl) ⟨884922, by rfl⟩ : syracuseStep 2359793 = 1769845) B1769845
theorem B2097665 : Blo 1397518 2097665 := bstep (se 2 (by rfl) ⟨786624, by rfl⟩ : syracuseStep 2097665 = 1573249) B1573249
theorem B2097683 : Blo 1397518 2097683 := bstep (se 1 (by rfl) ⟨1573262, by rfl⟩ : syracuseStep 2097683 = 3146525) B3146525
theorem B1573411 : Blo 1397518 1573411 := bstep (se 1 (by rfl) ⟨1180058, by rfl⟩ : syracuseStep 1573411 = 2360117) B2360117
theorem B2097713 : Blo 1397518 2097713 := bstep (se 2 (by rfl) ⟨786642, by rfl⟩ : syracuseStep 2097713 = 1573285) B1573285
theorem B17932853 : Blo 1397518 17932853 := bstep (se 5 (by rfl) ⟨840602, by rfl⟩ : syracuseStep 17932853 = 1681205) B1681205
theorem B2155075 : Blo 1397518 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B2097731 : Blo 1397518 2097731 := bstep (se 1 (by rfl) ⟨1573298, by rfl⟩ : syracuseStep 2097731 = 3146597) B3146597
theorem B2097761 : Blo 1397518 2097761 := bstep (se 2 (by rfl) ⟨786660, by rfl⟩ : syracuseStep 2097761 = 1573321) B1573321
theorem B2359921 : Blo 1397518 2359921 := bstep (se 2 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 2359921 = 1769941) B1769941
theorem B2425457 : Blo 1397518 2425457 := bstep (se 2 (by rfl) ⟨909546, by rfl⟩ : syracuseStep 2425457 = 1819093) B1819093
theorem B2097779 : Blo 1397518 2097779 := bstep (se 1 (by rfl) ⟨1573334, by rfl⟩ : syracuseStep 2097779 = 3146669) B3146669
theorem B2654851 : Blo 1397518 2654851 := bstep (se 1 (by rfl) ⟨1991138, by rfl⟩ : syracuseStep 2654851 = 3982277) B3982277
theorem B2097809 : Blo 1397518 2097809 := bstep (se 2 (by rfl) ⟨786678, by rfl⟩ : syracuseStep 2097809 = 1573357) B1573357
theorem B2359955 : Blo 1397518 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B2097827 : Blo 1397518 2097827 := bstep (se 1 (by rfl) ⟨1573370, by rfl⟩ : syracuseStep 2097827 = 3146741) B3146741
theorem B3146417 : Blo 1397518 3146417 := bstep (se 2 (by rfl) ⟨1179906, by rfl⟩ : syracuseStep 3146417 = 2359813) B2359813
theorem B1573555 : Blo 1397518 1573555 := bstep (se 1 (by rfl) ⟨1180166, by rfl⟩ : syracuseStep 1573555 = 2360333) B2360333
theorem B3146435 : Blo 1397518 3146435 := bstep (se 1 (by rfl) ⟨2359826, by rfl⟩ : syracuseStep 3146435 = 4719653) B4719653
theorem B2097857 : Blo 1397518 2097857 := bstep (se 2 (by rfl) ⟨786696, by rfl⟩ : syracuseStep 2097857 = 1573393) B1573393
theorem B2097875 : Blo 1397518 2097875 := bstep (se 1 (by rfl) ⟨1573406, by rfl⟩ : syracuseStep 2097875 = 3146813) B3146813
theorem B1991395 : Blo 1397518 1991395 := bstep (se 1 (by rfl) ⟨1493546, by rfl⟩ : syracuseStep 1991395 = 2987093) B2987093
theorem B3982061 : Blo 1397518 3982061 := bstep (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) B1493273
theorem B2097905 : Blo 1397518 2097905 := bstep (se 2 (by rfl) ⟨786714, by rfl⟩ : syracuseStep 2097905 = 1573429) B1573429
theorem B2097923 : Blo 1397518 2097923 := bstep (se 1 (by rfl) ⟨1573442, by rfl⟩ : syracuseStep 2097923 = 3146885) B3146885
theorem B2360083 : Blo 1397518 2360083 := bstep (se 1 (by rfl) ⟨1770062, by rfl⟩ : syracuseStep 2360083 = 3540125) B3540125
theorem B2097953 : Blo 1397518 2097953 := bstep (se 2 (by rfl) ⟨786732, by rfl⟩ : syracuseStep 2097953 = 1573465) B1573465
theorem B2655011 : Blo 1397518 2655011 := bstep (se 1 (by rfl) ⟨1991258, by rfl⟩ : syracuseStep 2655011 = 3982517) B3982517
theorem B1770275 : Blo 1397518 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B2097971 : Blo 1397518 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1573699 : Blo 1397518 1573699 := bstep (se 1 (by rfl) ⟨1180274, by rfl⟩ : syracuseStep 1573699 = 2360549) B2360549
theorem B4719437 : Blo 1397518 4719437 := bstep (se 3 (by rfl) ⟨884894, by rfl⟩ : syracuseStep 4719437 = 1769789) B1769789
theorem B2098001 : Blo 1397518 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B2098019 : Blo 1397518 2098019 := bstep (se 1 (by rfl) ⟨1573514, by rfl⟩ : syracuseStep 2098019 = 3147029) B3147029
theorem B7963505 : Blo 1397518 7963505 := bstep (se 2 (by rfl) ⟨2986314, by rfl⟩ : syracuseStep 7963505 = 5972629) B5972629
theorem B2098049 : Blo 1397518 2098049 := bstep (se 2 (by rfl) ⟨786768, by rfl⟩ : syracuseStep 2098049 = 1573537) B1573537
theorem B4719491 : Blo 1397518 4719491 := bstep (se 1 (by rfl) ⟨3539618, by rfl⟩ : syracuseStep 4719491 = 7079237) B7079237
theorem B2098067 : Blo 1397518 2098067 := bstep (se 1 (by rfl) ⟨1573550, by rfl⟩ : syracuseStep 2098067 = 3147101) B3147101
theorem B2360225 : Blo 1397518 2360225 := bstep (se 2 (by rfl) ⟨885084, by rfl⟩ : syracuseStep 2360225 = 1770169) B1770169
theorem B3982243 : Blo 1397518 3982243 := bstep (se 1 (by rfl) ⟨2986682, by rfl⟩ : syracuseStep 3982243 = 5973365) B5973365
theorem B2098097 : Blo 1397518 2098097 := bstep (se 2 (by rfl) ⟨786786, by rfl⟩ : syracuseStep 2098097 = 1573573) B1573573
theorem B2098115 : Blo 1397518 2098115 := bstep (se 1 (by rfl) ⟨1573586, by rfl⟩ : syracuseStep 2098115 = 3147173) B3147173
theorem B3146705 : Blo 1397518 3146705 := bstep (se 2 (by rfl) ⟨1180014, by rfl⟩ : syracuseStep 3146705 = 2360029) B2360029
theorem B1573843 : Blo 1397518 1573843 := bstep (se 1 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 1573843 = 2360765) B2360765
theorem B2098145 : Blo 1397518 2098145 := bstep (se 2 (by rfl) ⟨786804, by rfl⟩ : syracuseStep 2098145 = 1573609) B1573609
theorem B3146723 : Blo 1397518 3146723 := bstep (se 1 (by rfl) ⟨2360042, by rfl⟩ : syracuseStep 3146723 = 4720085) B4720085
theorem B12116963 : Blo 1397518 12116963 := bstep (se 1 (by rfl) ⟨9087722, by rfl⟩ : syracuseStep 12116963 = 18175445) B18175445
theorem B2098163 : Blo 1397518 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B2098193 : Blo 1397518 2098193 := bstep (se 2 (by rfl) ⟨786822, by rfl⟩ : syracuseStep 2098193 = 1573645) B1573645
theorem B2360353 : Blo 1397518 2360353 := bstep (se 2 (by rfl) ⟨885132, by rfl⟩ : syracuseStep 2360353 = 1770265) B1770265
theorem B2098211 : Blo 1397518 2098211 := bstep (se 1 (by rfl) ⟨1573658, by rfl⟩ : syracuseStep 2098211 = 3147317) B3147317
theorem B5309489 : Blo 1397518 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B1991731 : Blo 1397518 1991731 := bstep (se 1 (by rfl) ⟨1493798, by rfl⟩ : syracuseStep 1991731 = 2987597) B2987597
theorem B2098241 : Blo 1397518 2098241 := bstep (se 2 (by rfl) ⟨786840, by rfl⟩ : syracuseStep 2098241 = 1573681) B1573681
theorem B2360387 : Blo 1397518 2360387 := bstep (se 1 (by rfl) ⟨1770290, by rfl⟩ : syracuseStep 2360387 = 3540581) B3540581
theorem B8504389 : Blo 1397518 8504389 := bstep (se 4 (by rfl) ⟨797286, by rfl⟩ : syracuseStep 8504389 = 1594573) B1594573
theorem B15131717 : Blo 1397518 15131717 := bstep (se 4 (by rfl) ⟨1418598, by rfl⟩ : syracuseStep 15131717 = 2837197) B2837197
theorem B2098259 : Blo 1397518 2098259 := bstep (se 1 (by rfl) ⟨1573694, by rfl⟩ : syracuseStep 2098259 = 3147389) B3147389
theorem B1573987 : Blo 1397518 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B2098289 : Blo 1397518 2098289 := bstep (se 2 (by rfl) ⟨786858, by rfl⟩ : syracuseStep 2098289 = 1573717) B1573717
theorem B2393201 : Blo 1397518 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B2098307 : Blo 1397518 2098307 := bstep (se 1 (by rfl) ⟨1573730, by rfl⟩ : syracuseStep 2098307 = 3147461) B3147461
theorem B4719761 : Blo 1397518 4719761 := bstep (se 2 (by rfl) ⟨1769910, by rfl⟩ : syracuseStep 4719761 = 3539821) B3539821
theorem B1418387 : Blo 1397518 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B2098337 : Blo 1397518 2098337 := bstep (se 2 (by rfl) ⟨786876, by rfl⟩ : syracuseStep 2098337 = 1573753) B1573753
theorem B7079075 : Blo 1397518 7079075 := bstep (se 1 (by rfl) ⟨5309306, by rfl⟩ : syracuseStep 7079075 = 10618613) B10618613
theorem B3540145 : Blo 1397518 3540145 := bstep (se 2 (by rfl) ⟨1327554, by rfl⟩ : syracuseStep 3540145 = 2655109) B2655109
theorem B2098355 : Blo 1397518 2098355 := bstep (se 1 (by rfl) ⟨1573766, by rfl⟩ : syracuseStep 2098355 = 3147533) B3147533
theorem B2360515 : Blo 1397518 2360515 := bstep (se 1 (by rfl) ⟨1770386, by rfl⟩ : syracuseStep 2360515 = 3540773) B3540773
theorem B2098385 : Blo 1397518 2098385 := bstep (se 2 (by rfl) ⟨786894, by rfl⟩ : syracuseStep 2098385 = 1573789) B1573789
theorem B2098403 : Blo 1397518 2098403 := bstep (se 1 (by rfl) ⟨1573802, by rfl⟩ : syracuseStep 2098403 = 3147605) B3147605
theorem B3146993 : Blo 1397518 3146993 := bstep (se 2 (by rfl) ⟨1180122, by rfl⟩ : syracuseStep 3146993 = 2360245) B2360245
theorem B1574131 : Blo 1397518 1574131 := bstep (se 1 (by rfl) ⟨1180598, by rfl⟩ : syracuseStep 1574131 = 2361197) B2361197
theorem B2098433 : Blo 1397518 2098433 := bstep (se 2 (by rfl) ⟨786912, by rfl⟩ : syracuseStep 2098433 = 1573825) B1573825
theorem B3147011 : Blo 1397518 3147011 := bstep (se 1 (by rfl) ⟨2360258, by rfl⟩ : syracuseStep 3147011 = 4720517) B4720517
theorem B4482317 : Blo 1397518 4482317 := bstep (se 3 (by rfl) ⟨840434, by rfl⟩ : syracuseStep 4482317 = 1680869) B1680869
theorem B2098451 : Blo 1397518 2098451 := bstep (se 1 (by rfl) ⟨1573838, by rfl⟩ : syracuseStep 2098451 = 3147677) B3147677
theorem B2098481 : Blo 1397518 2098481 := bstep (se 2 (by rfl) ⟨786930, by rfl⟩ : syracuseStep 2098481 = 1573861) B1573861
theorem B16999733 : Blo 1397518 16999733 := bstep (se 5 (by rfl) ⟨796862, by rfl⟩ : syracuseStep 16999733 = 1593725) B1593725
theorem B2098499 : Blo 1397518 2098499 := bstep (se 1 (by rfl) ⟨1573874, by rfl⟩ : syracuseStep 2098499 = 3147749) B3147749
theorem B8963405 : Blo 1397518 8963405 := bstep (se 3 (by rfl) ⟨1680638, by rfl⟩ : syracuseStep 8963405 = 3361277) B3361277
theorem B2360657 : Blo 1397518 2360657 := bstep (se 2 (by rfl) ⟨885246, by rfl⟩ : syracuseStep 2360657 = 1770493) B1770493
theorem B2098529 : Blo 1397518 2098529 := bstep (se 2 (by rfl) ⟨786948, by rfl⟩ : syracuseStep 2098529 = 1573897) B1573897
theorem B2098547 : Blo 1397518 2098547 := bstep (se 1 (by rfl) ⟨1573910, by rfl⟩ : syracuseStep 2098547 = 3147821) B3147821
theorem B1574275 : Blo 1397518 1574275 := bstep (se 1 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 1574275 = 2361413) B2361413
theorem B3982733 : Blo 1397518 3982733 := bstep (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) B1493525
theorem B2098577 : Blo 1397518 2098577 := bstep (se 2 (by rfl) ⟨786966, by rfl⟩ : syracuseStep 2098577 = 1573933) B1573933
theorem B2098595 : Blo 1397518 2098595 := bstep (se 1 (by rfl) ⟨1573946, by rfl⟩ : syracuseStep 2098595 = 3147893) B3147893
theorem B2098625 : Blo 1397518 2098625 := bstep (se 2 (by rfl) ⟨786984, by rfl⟩ : syracuseStep 2098625 = 1573969) B1573969
theorem B3540419 : Blo 1397518 3540419 := bstep (se 1 (by rfl) ⟨2655314, by rfl⟩ : syracuseStep 3540419 = 5310629) B5310629
theorem B2360785 : Blo 1397518 2360785 := bstep (se 2 (by rfl) ⟨885294, by rfl⟩ : syracuseStep 2360785 = 1770589) B1770589
theorem B2098643 : Blo 1397518 2098643 := bstep (se 1 (by rfl) ⟨1573982, by rfl⟩ : syracuseStep 2098643 = 3147965) B3147965
theorem B1770979 : Blo 1397518 1770979 := bstep (se 1 (by rfl) ⟨1328234, by rfl⟩ : syracuseStep 1770979 = 2656469) B2656469
theorem B2098673 : Blo 1397518 2098673 := bstep (se 2 (by rfl) ⟨787002, by rfl⟩ : syracuseStep 2098673 = 1574005) B1574005
theorem B2360819 : Blo 1397518 2360819 := bstep (se 1 (by rfl) ⟨1770614, by rfl⟩ : syracuseStep 2360819 = 3541229) B3541229
theorem B2098691 : Blo 1397518 2098691 := bstep (se 1 (by rfl) ⟨1574018, by rfl⟩ : syracuseStep 2098691 = 3148037) B3148037
theorem B5973517 : Blo 1397518 5973517 := bstep (se 3 (by rfl) ⟨1120034, by rfl⟩ : syracuseStep 5973517 = 2240069) B2240069
theorem B3147281 : Blo 1397518 3147281 := bstep (se 2 (by rfl) ⟨1180230, by rfl⟩ : syracuseStep 3147281 = 2360461) B2360461
theorem B1574419 : Blo 1397518 1574419 := bstep (se 1 (by rfl) ⟨1180814, by rfl⟩ : syracuseStep 1574419 = 2361629) B2361629
theorem B2098721 : Blo 1397518 2098721 := bstep (se 2 (by rfl) ⟨787020, by rfl⟩ : syracuseStep 2098721 = 1574041) B1574041
theorem B3147299 : Blo 1397518 3147299 := bstep (se 1 (by rfl) ⟨2360474, by rfl⟩ : syracuseStep 3147299 = 4720949) B4720949
theorem B2098739 : Blo 1397518 2098739 := bstep (se 1 (by rfl) ⟨1574054, by rfl⟩ : syracuseStep 2098739 = 3148109) B3148109
theorem B1771075 : Blo 1397518 1771075 := bstep (se 1 (by rfl) ⟨1328306, by rfl⟩ : syracuseStep 1771075 = 2656613) B2656613
theorem B2098769 : Blo 1397518 2098769 := bstep (se 2 (by rfl) ⟨787038, by rfl⟩ : syracuseStep 2098769 = 1574077) B1574077
theorem B1992289 : Blo 1397518 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B2098787 : Blo 1397518 2098787 := bstep (se 1 (by rfl) ⟨1574090, by rfl⟩ : syracuseStep 2098787 = 3148181) B3148181
theorem B2360947 : Blo 1397518 2360947 := bstep (se 1 (by rfl) ⟨1770710, by rfl⟩ : syracuseStep 2360947 = 3541421) B3541421
theorem B2098817 : Blo 1397518 2098817 := bstep (se 2 (by rfl) ⟨787056, by rfl⟩ : syracuseStep 2098817 = 1574113) B1574113
theorem B3540611 : Blo 1397518 3540611 := bstep (se 1 (by rfl) ⟨2655458, by rfl⟩ : syracuseStep 3540611 = 5310917) B5310917
theorem B1992323 : Blo 1397518 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B4368013 : Blo 1397518 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B2098835 : Blo 1397518 2098835 := bstep (se 1 (by rfl) ⟨1574126, by rfl⟩ : syracuseStep 2098835 = 3148253) B3148253
theorem B4720301 : Blo 1397518 4720301 := bstep (se 3 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 4720301 = 1770113) B1770113
theorem B2098865 : Blo 1397518 2098865 := bstep (se 2 (by rfl) ⟨787074, by rfl⟩ : syracuseStep 2098865 = 1574149) B1574149
theorem B17000117 : Blo 1397518 17000117 := bstep (se 5 (by rfl) ⟨796880, by rfl⟩ : syracuseStep 17000117 = 1593761) B1593761
theorem B2098883 : Blo 1397518 2098883 := bstep (se 1 (by rfl) ⟨1574162, by rfl⟩ : syracuseStep 2098883 = 3148325) B3148325
theorem B5310157 : Blo 1397518 5310157 := bstep (se 3 (by rfl) ⟨995654, by rfl⟩ : syracuseStep 5310157 = 1991309) B1991309
theorem B2098913 : Blo 1397518 2098913 := bstep (se 2 (by rfl) ⟨787092, by rfl⟩ : syracuseStep 2098913 = 1574185) B1574185
theorem B2016995 : Blo 1397518 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B4720355 : Blo 1397518 4720355 := bstep (se 1 (by rfl) ⟨3540266, by rfl⟩ : syracuseStep 4720355 = 7080533) B7080533
theorem B4253411 : Blo 1397518 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B2098931 : Blo 1397518 2098931 := bstep (se 1 (by rfl) ⟨1574198, by rfl⟩ : syracuseStep 2098931 = 3148397) B3148397
theorem B2361089 : Blo 1397518 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2098961 : Blo 1397518 2098961 := bstep (se 2 (by rfl) ⟨787110, by rfl⟩ : syracuseStep 2098961 = 1574221) B1574221
theorem B2098979 : Blo 1397518 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B3147569 : Blo 1397518 3147569 := bstep (se 2 (by rfl) ⟨1180338, by rfl⟩ : syracuseStep 3147569 = 2360677) B2360677
theorem B2099009 : Blo 1397518 2099009 := bstep (se 2 (by rfl) ⟨787128, by rfl⟩ : syracuseStep 2099009 = 1574257) B1574257
theorem B3147587 : Blo 1397518 3147587 := bstep (se 1 (by rfl) ⟨2360690, by rfl⟩ : syracuseStep 3147587 = 4721381) B4721381
theorem B2656081 : Blo 1397518 2656081 := bstep (se 2 (by rfl) ⟨996030, by rfl⟩ : syracuseStep 2656081 = 1992061) B1992061
theorem B2099027 : Blo 1397518 2099027 := bstep (se 1 (by rfl) ⟨1574270, by rfl⟩ : syracuseStep 2099027 = 3148541) B3148541
theorem B2099057 : Blo 1397518 2099057 := bstep (se 2 (by rfl) ⟨787146, by rfl⟩ : syracuseStep 2099057 = 1574293) B1574293
theorem B2361217 : Blo 1397518 2361217 := bstep (se 2 (by rfl) ⟨885456, by rfl⟩ : syracuseStep 2361217 = 1770913) B1770913
theorem B1492867 : Blo 1397518 1492867 := bstep (se 1 (by rfl) ⟨1119650, by rfl⟩ : syracuseStep 1492867 = 2239301) B2239301
theorem B2099075 : Blo 1397518 2099075 := bstep (se 1 (by rfl) ⟨1574306, by rfl⟩ : syracuseStep 2099075 = 3148613) B3148613
theorem B2099105 : Blo 1397518 2099105 := bstep (se 2 (by rfl) ⟨787164, by rfl⟩ : syracuseStep 2099105 = 1574329) B1574329
theorem B2361251 : Blo 1397518 2361251 := bstep (se 1 (by rfl) ⟨1770938, by rfl⟩ : syracuseStep 2361251 = 3541877) B3541877
theorem B2099123 : Blo 1397518 2099123 := bstep (se 1 (by rfl) ⟨1574342, by rfl⟩ : syracuseStep 2099123 = 3148685) B3148685
theorem B7079885 : Blo 1397518 7079885 := bstep (se 3 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 7079885 = 2654957) B2654957
theorem B2099153 : Blo 1397518 2099153 := bstep (se 2 (by rfl) ⟨787182, by rfl⟩ : syracuseStep 2099153 = 1574365) B1574365
theorem B2099171 : Blo 1397518 2099171 := bstep (se 1 (by rfl) ⟨1574378, by rfl⟩ : syracuseStep 2099171 = 3148757) B3148757
theorem B4720625 : Blo 1397518 4720625 := bstep (se 2 (by rfl) ⟨1770234, by rfl⟩ : syracuseStep 4720625 = 3540469) B3540469
theorem B3590129 : Blo 1397518 3590129 := bstep (se 2 (by rfl) ⟨1346298, by rfl⟩ : syracuseStep 3590129 = 2692597) B2692597
theorem B2099201 : Blo 1397518 2099201 := bstep (se 2 (by rfl) ⟨787200, by rfl⟩ : syracuseStep 2099201 = 1574401) B1574401
theorem B2099219 : Blo 1397518 2099219 := bstep (se 1 (by rfl) ⟨1574414, by rfl⟩ : syracuseStep 2099219 = 3148829) B3148829
theorem B2361379 : Blo 1397518 2361379 := bstep (se 1 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 2361379 = 3542069) B3542069
theorem B2099249 : Blo 1397518 2099249 := bstep (se 2 (by rfl) ⟨787218, by rfl⟩ : syracuseStep 2099249 = 1574437) B1574437
theorem B2099267 : Blo 1397518 2099267 := bstep (se 1 (by rfl) ⟨1574450, by rfl⟩ : syracuseStep 2099267 = 3148901) B3148901
theorem B3147857 : Blo 1397518 3147857 := bstep (se 2 (by rfl) ⟨1180446, by rfl⟩ : syracuseStep 3147857 = 2360893) B2360893
theorem B3147875 : Blo 1397518 3147875 := bstep (se 1 (by rfl) ⟨2360906, by rfl⟩ : syracuseStep 3147875 = 4721813) B4721813
theorem B2361521 : Blo 1397518 2361521 := bstep (se 2 (by rfl) ⟨885570, by rfl⟩ : syracuseStep 2361521 = 1771141) B1771141
theorem B3361027 : Blo 1397518 3361027 := bstep (se 1 (by rfl) ⟨2520770, by rfl⟩ : syracuseStep 3361027 = 5041541) B5041541
theorem B16148749 : Blo 1397518 16148749 := bstep (se 3 (by rfl) ⟨3027890, by rfl⟩ : syracuseStep 16148749 = 6055781) B6055781
theorem B7964963 : Blo 1397518 7964963 := bstep (se 1 (by rfl) ⟨5973722, by rfl⟩ : syracuseStep 7964963 = 11947445) B11947445
theorem B2361649 : Blo 1397518 2361649 := bstep (se 2 (by rfl) ⟨885618, by rfl⟩ : syracuseStep 2361649 = 1771237) B1771237
theorem B2361683 : Blo 1397518 2361683 := bstep (se 1 (by rfl) ⟨1771262, by rfl⟩ : syracuseStep 2361683 = 3542525) B3542525
theorem B3361123 : Blo 1397518 3361123 := bstep (se 1 (by rfl) ⟨2520842, by rfl⟩ : syracuseStep 3361123 = 5041685) B5041685
theorem B3148145 : Blo 1397518 3148145 := bstep (se 2 (by rfl) ⟨1180554, by rfl⟩ : syracuseStep 3148145 = 2361109) B2361109
theorem B3148163 : Blo 1397518 3148163 := bstep (se 1 (by rfl) ⟨2361122, by rfl⟩ : syracuseStep 3148163 = 4722245) B4722245
theorem B80660933 : Blo 1397518 80660933 := bstep (se 4 (by rfl) ⟨7561962, by rfl⟩ : syracuseStep 80660933 = 15123925) B15123925
theorem B5310947 : Blo 1397518 5310947 := bstep (se 1 (by rfl) ⟨3983210, by rfl⟩ : syracuseStep 5310947 = 7966421) B7966421
theorem B8071693 : Blo 1397518 8071693 := bstep (se 3 (by rfl) ⟨1513442, by rfl⟩ : syracuseStep 8071693 = 3026885) B3026885
theorem B4721165 : Blo 1397518 4721165 := bstep (se 3 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 4721165 = 1770437) B1770437
theorem B1436195 : Blo 1397518 1436195 := bstep (se 1 (by rfl) ⟨1077146, by rfl⟩ : syracuseStep 1436195 = 2154293) B2154293
theorem B3983917 : Blo 1397518 3983917 := bstep (se 3 (by rfl) ⟨746984, by rfl⟩ : syracuseStep 3983917 = 1493969) B1493969
theorem B3541553 : Blo 1397518 3541553 := bstep (se 2 (by rfl) ⟨1328082, by rfl⟩ : syracuseStep 3541553 = 2656165) B2656165
theorem B4721219 : Blo 1397518 4721219 := bstep (se 1 (by rfl) ⟨3540914, by rfl⟩ : syracuseStep 4721219 = 7081829) B7081829
theorem B12757603 : Blo 1397518 12757603 := bstep (se 1 (by rfl) ⟨9568202, by rfl⟩ : syracuseStep 12757603 = 19136405) B19136405
theorem B3541603 : Blo 1397518 3541603 := bstep (se 1 (by rfl) ⟨2656202, by rfl⟩ : syracuseStep 3541603 = 5312405) B5312405
theorem B2239121 : Blo 1397518 2239121 := bstep (se 2 (by rfl) ⟨839670, by rfl⟩ : syracuseStep 2239121 = 1679341) B1679341
theorem B3148433 : Blo 1397518 3148433 := bstep (se 2 (by rfl) ⟨1180662, by rfl⟩ : syracuseStep 3148433 = 2361325) B2361325
theorem B3148451 : Blo 1397518 3148451 := bstep (se 1 (by rfl) ⟨2361338, by rfl⟩ : syracuseStep 3148451 = 4722677) B4722677
theorem B11340485 : Blo 1397518 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B3541745 : Blo 1397518 3541745 := bstep (se 2 (by rfl) ⟨1328154, by rfl⟩ : syracuseStep 3541745 = 2656309) B2656309
theorem B2239249 : Blo 1397518 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B4721489 : Blo 1397518 4721489 := bstep (se 2 (by rfl) ⟨1770558, by rfl⟩ : syracuseStep 4721489 = 3541117) B3541117
theorem B3148721 : Blo 1397518 3148721 := bstep (se 2 (by rfl) ⟨1180770, by rfl⟩ : syracuseStep 3148721 = 2361541) B2361541
theorem B3148739 : Blo 1397518 3148739 := bstep (se 1 (by rfl) ⟨2361554, by rfl⟩ : syracuseStep 3148739 = 4723109) B4723109
theorem B76573637 : Blo 1397518 76573637 := bstep (se 4 (by rfl) ⟨7178778, by rfl⟩ : syracuseStep 76573637 = 14357557) B14357557
theorem B10087523 : Blo 1397518 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B5311601 : Blo 1397518 5311601 := bstep (se 2 (by rfl) ⟨1991850, by rfl⟩ : syracuseStep 5311601 = 3983701) B3983701
theorem B1494131 : Blo 1397518 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B2985187 : Blo 1397518 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B7965965 : Blo 1397518 7965965 := bstep (se 3 (by rfl) ⟨1493618, by rfl⟩ : syracuseStep 7965965 = 2987237) B2987237
theorem B4722029 : Blo 1397518 4722029 := bstep (se 3 (by rfl) ⟨885380, by rfl⟩ : syracuseStep 4722029 = 1770761) B1770761
theorem B4722083 : Blo 1397518 4722083 := bstep (se 1 (by rfl) ⟨3541562, by rfl⟩ : syracuseStep 4722083 = 7083125) B7083125
theorem B2018849 : Blo 1397518 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B3984977 : Blo 1397518 3984977 := bstep (se 2 (by rfl) ⟨1494366, by rfl⟩ : syracuseStep 3984977 = 2988733) B2988733
theorem B10620557 : Blo 1397518 10620557 := bstep (se 3 (by rfl) ⟨1991354, by rfl⟩ : syracuseStep 10620557 = 3982709) B3982709
theorem B2125489 : Blo 1397518 2125489 := bstep (se 2 (by rfl) ⟨797058, by rfl⟩ : syracuseStep 2125489 = 1594117) B1594117
theorem B4722353 : Blo 1397518 4722353 := bstep (se 2 (by rfl) ⟨1770882, by rfl⟩ : syracuseStep 4722353 = 3541765) B3541765
theorem B6057827 : Blo 1397518 6057827 := bstep (se 1 (by rfl) ⟨4543370, by rfl⟩ : syracuseStep 6057827 = 9086741) B9086741
theorem B2518897 : Blo 1397518 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B2985905 : Blo 1397518 2985905 := bstep (se 2 (by rfl) ⟨1119714, by rfl⟩ : syracuseStep 2985905 = 2239429) B2239429
theorem B2240531 : Blo 1397518 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B19132469 : Blo 1397518 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B2240627 : Blo 1397518 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B2240659 : Blo 1397518 2240659 := bstep (se 1 (by rfl) ⟨1680494, by rfl⟩ : syracuseStep 2240659 = 3360989) B3360989
theorem B4722893 : Blo 1397518 4722893 := bstep (se 3 (by rfl) ⟨885542, by rfl⟩ : syracuseStep 4722893 = 1771085) B1771085
theorem B4722947 : Blo 1397518 4722947 := bstep (se 1 (by rfl) ⟨3542210, by rfl⟩ : syracuseStep 4722947 = 7084421) B7084421
theorem B35836181 : Blo 1397518 35836181 := bstep (se 6 (by rfl) ⟨839910, by rfl⟩ : syracuseStep 35836181 = 1679821) B1679821
theorem B2986417 : Blo 1397518 2986417 := bstep (se 2 (by rfl) ⟨1119906, by rfl⟩ : syracuseStep 2986417 = 2239813) B2239813
theorem B5673485 : Blo 1397518 5673485 := bstep (se 3 (by rfl) ⟨1063778, by rfl⟩ : syracuseStep 5673485 = 2127557) B2127557
theorem B3404305 : Blo 1397518 3404305 := bstep (se 2 (by rfl) ⟨1276614, by rfl⟩ : syracuseStep 3404305 = 2553229) B2553229
theorem B4723217 : Blo 1397518 4723217 := bstep (se 2 (by rfl) ⟨1771206, by rfl⟩ : syracuseStep 4723217 = 3542413) B3542413
theorem B5313059 : Blo 1397518 5313059 := bstep (se 1 (by rfl) ⟨3984794, by rfl⟩ : syracuseStep 5313059 = 7969589) B7969589
theorem B7279139 : Blo 1397518 7279139 := bstep (se 1 (by rfl) ⟨5459354, by rfl⟩ : syracuseStep 7279139 = 10918709) B10918709
theorem B5313073 : Blo 1397518 5313073 := bstep (se 2 (by rfl) ⟨1992402, by rfl⟩ : syracuseStep 5313073 = 3984805) B3984805
theorem B3068675 : Blo 1397518 3068675 := bstep (se 1 (by rfl) ⟨2301506, by rfl⟩ : syracuseStep 3068675 = 4603013) B4603013
theorem B1397523 : Blo 1397518 1397523 := bstep (se 1 (by rfl) ⟨1048142, by rfl⟩ : syracuseStep 1397523 = 2096285) B2096285
theorem B1397539 : Blo 1397518 1397539 := bstep (se 1 (by rfl) ⟨1048154, by rfl⟩ : syracuseStep 1397539 = 2096309) B2096309
theorem B7082801 : Blo 1397518 7082801 := bstep (se 2 (by rfl) ⟨2656050, by rfl⟩ : syracuseStep 7082801 = 5312101) B5312101
theorem B1397555 : Blo 1397518 1397555 := bstep (se 1 (by rfl) ⟨1048166, by rfl⟩ : syracuseStep 1397555 = 2096333) B2096333
theorem B1397571 : Blo 1397518 1397571 := bstep (se 1 (by rfl) ⟨1048178, by rfl⟩ : syracuseStep 1397571 = 2096357) B2096357
theorem B7557965 : Blo 1397518 7557965 := bstep (se 3 (by rfl) ⟨1417118, by rfl⟩ : syracuseStep 7557965 = 2834237) B2834237
theorem B1397587 : Blo 1397518 1397587 := bstep (se 1 (by rfl) ⟨1048190, by rfl⟩ : syracuseStep 1397587 = 2096381) B2096381
theorem B1397603 : Blo 1397518 1397603 := bstep (se 1 (by rfl) ⟨1048202, by rfl⟩ : syracuseStep 1397603 = 2096405) B2096405
theorem B1397619 : Blo 1397518 1397619 := bstep (se 1 (by rfl) ⟨1048214, by rfl⟩ : syracuseStep 1397619 = 2096429) B2096429
theorem B1397635 : Blo 1397518 1397635 := bstep (se 1 (by rfl) ⟨1048226, by rfl⟩ : syracuseStep 1397635 = 2096453) B2096453
theorem B1397651 : Blo 1397518 1397651 := bstep (se 1 (by rfl) ⟨1048238, by rfl⟩ : syracuseStep 1397651 = 2096477) B2096477
theorem B1397667 : Blo 1397518 1397667 := bstep (se 1 (by rfl) ⟨1048250, by rfl⟩ : syracuseStep 1397667 = 2096501) B2096501
theorem B1397683 : Blo 1397518 1397683 := bstep (se 1 (by rfl) ⟨1048262, by rfl⟩ : syracuseStep 1397683 = 2096525) B2096525
theorem B1397699 : Blo 1397518 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B1397715 : Blo 1397518 1397715 := bstep (se 1 (by rfl) ⟨1048286, by rfl⟩ : syracuseStep 1397715 = 2096573) B2096573
theorem B1397731 : Blo 1397518 1397731 := bstep (se 1 (by rfl) ⟨1048298, by rfl⟩ : syracuseStep 1397731 = 2096597) B2096597
theorem B1397747 : Blo 1397518 1397747 := bstep (se 1 (by rfl) ⟨1048310, by rfl⟩ : syracuseStep 1397747 = 2096621) B2096621
theorem B1397763 : Blo 1397518 1397763 := bstep (se 1 (by rfl) ⟨1048322, by rfl⟩ : syracuseStep 1397763 = 2096645) B2096645
theorem B1397779 : Blo 1397518 1397779 := bstep (se 1 (by rfl) ⟨1048334, by rfl⟩ : syracuseStep 1397779 = 2096669) B2096669
theorem B2241569 : Blo 1397518 2241569 := bstep (se 2 (by rfl) ⟨840588, by rfl⟩ : syracuseStep 2241569 = 1681177) B1681177
theorem B1397795 : Blo 1397518 1397795 := bstep (se 1 (by rfl) ⟨1048346, by rfl⟩ : syracuseStep 1397795 = 2096693) B2096693
theorem B1397811 : Blo 1397518 1397811 := bstep (se 1 (by rfl) ⟨1048358, by rfl⟩ : syracuseStep 1397811 = 2096717) B2096717
theorem B1397827 : Blo 1397518 1397827 := bstep (se 1 (by rfl) ⟨1048370, by rfl⟩ : syracuseStep 1397827 = 2096741) B2096741
theorem B1397843 : Blo 1397518 1397843 := bstep (se 1 (by rfl) ⟨1048382, by rfl⟩ : syracuseStep 1397843 = 2096765) B2096765
theorem B1397859 : Blo 1397518 1397859 := bstep (se 1 (by rfl) ⟨1048394, by rfl⟩ : syracuseStep 1397859 = 2096789) B2096789
theorem B1397875 : Blo 1397518 1397875 := bstep (se 1 (by rfl) ⟨1048406, by rfl⟩ : syracuseStep 1397875 = 2096813) B2096813
theorem B1397891 : Blo 1397518 1397891 := bstep (se 1 (by rfl) ⟨1048418, by rfl⟩ : syracuseStep 1397891 = 2096837) B2096837
theorem B1397907 : Blo 1397518 1397907 := bstep (se 1 (by rfl) ⟨1048430, by rfl⟩ : syracuseStep 1397907 = 2096861) B2096861
theorem B1397923 : Blo 1397518 1397923 := bstep (se 1 (by rfl) ⟨1048442, by rfl⟩ : syracuseStep 1397923 = 2096885) B2096885
theorem B1397939 : Blo 1397518 1397939 := bstep (se 1 (by rfl) ⟨1048454, by rfl⟩ : syracuseStep 1397939 = 2096909) B2096909
theorem B1397955 : Blo 1397518 1397955 := bstep (se 1 (by rfl) ⟨1048466, by rfl⟩ : syracuseStep 1397955 = 2096933) B2096933
theorem B1397971 : Blo 1397518 1397971 := bstep (se 1 (by rfl) ⟨1048478, by rfl⟩ : syracuseStep 1397971 = 2096957) B2096957
theorem B4478179 : Blo 1397518 4478179 := bstep (se 1 (by rfl) ⟨3358634, by rfl⟩ : syracuseStep 4478179 = 6717269) B6717269
theorem B1397987 : Blo 1397518 1397987 := bstep (se 1 (by rfl) ⟨1048490, by rfl⟩ : syracuseStep 1397987 = 2096981) B2096981
theorem B1398003 : Blo 1397518 1398003 := bstep (se 1 (by rfl) ⟨1048502, by rfl⟩ : syracuseStep 1398003 = 2097005) B2097005
theorem B1398019 : Blo 1397518 1398019 := bstep (se 1 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 1398019 = 2097029) B2097029
theorem B1398035 : Blo 1397518 1398035 := bstep (se 1 (by rfl) ⟨1048526, by rfl⟩ : syracuseStep 1398035 = 2097053) B2097053
theorem B1398051 : Blo 1397518 1398051 := bstep (se 1 (by rfl) ⟨1048538, by rfl⟩ : syracuseStep 1398051 = 2097077) B2097077
theorem B1398067 : Blo 1397518 1398067 := bstep (se 1 (by rfl) ⟨1048550, by rfl⟩ : syracuseStep 1398067 = 2097101) B2097101
theorem B1398083 : Blo 1397518 1398083 := bstep (se 1 (by rfl) ⟨1048562, by rfl⟩ : syracuseStep 1398083 = 2097125) B2097125
theorem B1398099 : Blo 1397518 1398099 := bstep (se 1 (by rfl) ⟨1048574, by rfl⟩ : syracuseStep 1398099 = 2097149) B2097149
theorem B1398115 : Blo 1397518 1398115 := bstep (se 1 (by rfl) ⟨1048586, by rfl⟩ : syracuseStep 1398115 = 2097173) B2097173
theorem B1398131 : Blo 1397518 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B1398147 : Blo 1397518 1398147 := bstep (se 1 (by rfl) ⟨1048610, by rfl⟩ : syracuseStep 1398147 = 2097221) B2097221
theorem B1398163 : Blo 1397518 1398163 := bstep (se 1 (by rfl) ⟨1048622, by rfl⟩ : syracuseStep 1398163 = 2097245) B2097245
theorem B1398179 : Blo 1397518 1398179 := bstep (se 1 (by rfl) ⟨1048634, by rfl⟩ : syracuseStep 1398179 = 2097269) B2097269
theorem B2520497 : Blo 1397518 2520497 := bstep (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) B1890373
theorem B1398195 : Blo 1397518 1398195 := bstep (se 1 (by rfl) ⟨1048646, by rfl⟩ : syracuseStep 1398195 = 2097293) B2097293
theorem B1398211 : Blo 1397518 1398211 := bstep (se 1 (by rfl) ⟨1048658, by rfl⟩ : syracuseStep 1398211 = 2097317) B2097317
theorem B1398227 : Blo 1397518 1398227 := bstep (se 1 (by rfl) ⟨1048670, by rfl⟩ : syracuseStep 1398227 = 2097341) B2097341
theorem B1398243 : Blo 1397518 1398243 := bstep (se 1 (by rfl) ⟨1048682, by rfl⟩ : syracuseStep 1398243 = 2097365) B2097365
theorem B1398259 : Blo 1397518 1398259 := bstep (se 1 (by rfl) ⟨1048694, by rfl⟩ : syracuseStep 1398259 = 2097389) B2097389
theorem B1398275 : Blo 1397518 1398275 := bstep (se 1 (by rfl) ⟨1048706, by rfl⟩ : syracuseStep 1398275 = 2097413) B2097413
theorem B1398291 : Blo 1397518 1398291 := bstep (se 1 (by rfl) ⟨1048718, by rfl⟩ : syracuseStep 1398291 = 2097437) B2097437
theorem B1398307 : Blo 1397518 1398307 := bstep (se 1 (by rfl) ⟨1048730, by rfl⟩ : syracuseStep 1398307 = 2097461) B2097461
theorem B1398323 : Blo 1397518 1398323 := bstep (se 1 (by rfl) ⟨1048742, by rfl⟩ : syracuseStep 1398323 = 2097485) B2097485
theorem B1398339 : Blo 1397518 1398339 := bstep (se 1 (by rfl) ⟨1048754, by rfl⟩ : syracuseStep 1398339 = 2097509) B2097509
theorem B7960133 : Blo 1397518 7960133 := bstep (se 4 (by rfl) ⟨746262, by rfl⟩ : syracuseStep 7960133 = 1492525) B1492525
theorem B1398355 : Blo 1397518 1398355 := bstep (se 1 (by rfl) ⟨1048766, by rfl⟩ : syracuseStep 1398355 = 2097533) B2097533
theorem B1398371 : Blo 1397518 1398371 := bstep (se 1 (by rfl) ⟨1048778, by rfl⟩ : syracuseStep 1398371 = 2097557) B2097557
theorem B1398387 : Blo 1397518 1398387 := bstep (se 1 (by rfl) ⟨1048790, by rfl⟩ : syracuseStep 1398387 = 2097581) B2097581
theorem B1398403 : Blo 1397518 1398403 := bstep (se 1 (by rfl) ⟨1048802, by rfl⟩ : syracuseStep 1398403 = 2097605) B2097605
theorem B1398419 : Blo 1397518 1398419 := bstep (se 1 (by rfl) ⟨1048814, by rfl⟩ : syracuseStep 1398419 = 2097629) B2097629
theorem B4478627 : Blo 1397518 4478627 := bstep (se 1 (by rfl) ⟨3358970, by rfl⟩ : syracuseStep 4478627 = 6717941) B6717941
theorem B1398435 : Blo 1397518 1398435 := bstep (se 1 (by rfl) ⟨1048826, by rfl⟩ : syracuseStep 1398435 = 2097653) B2097653
theorem B1398451 : Blo 1397518 1398451 := bstep (se 1 (by rfl) ⟨1048838, by rfl⟩ : syracuseStep 1398451 = 2097677) B2097677
theorem B1398467 : Blo 1397518 1398467 := bstep (se 1 (by rfl) ⟨1048850, by rfl⟩ : syracuseStep 1398467 = 2097701) B2097701
theorem B1398483 : Blo 1397518 1398483 := bstep (se 1 (by rfl) ⟨1048862, by rfl⟩ : syracuseStep 1398483 = 2097725) B2097725
theorem B1398499 : Blo 1397518 1398499 := bstep (se 1 (by rfl) ⟨1048874, by rfl⟩ : syracuseStep 1398499 = 2097749) B2097749
theorem B1398515 : Blo 1397518 1398515 := bstep (se 1 (by rfl) ⟨1048886, by rfl⟩ : syracuseStep 1398515 = 2097773) B2097773
theorem B1398531 : Blo 1397518 1398531 := bstep (se 1 (by rfl) ⟨1048898, by rfl⟩ : syracuseStep 1398531 = 2097797) B2097797
theorem B1398547 : Blo 1397518 1398547 := bstep (se 1 (by rfl) ⟨1048910, by rfl⟩ : syracuseStep 1398547 = 2097821) B2097821
theorem B38811413 : Blo 1397518 38811413 := bstep (se 6 (by rfl) ⟨909642, by rfl⟩ : syracuseStep 38811413 = 1819285) B1819285
theorem B1398563 : Blo 1397518 1398563 := bstep (se 1 (by rfl) ⟨1048922, by rfl⟩ : syracuseStep 1398563 = 2097845) B2097845
theorem B5977891 : Blo 1397518 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B1398579 : Blo 1397518 1398579 := bstep (se 1 (by rfl) ⟨1048934, by rfl⟩ : syracuseStep 1398579 = 2097869) B2097869
theorem B1890113 : Blo 1397518 1890113 := bstep (se 2 (by rfl) ⟨708792, by rfl⟩ : syracuseStep 1890113 = 1417585) B1417585
theorem B1398595 : Blo 1397518 1398595 := bstep (se 1 (by rfl) ⟨1048946, by rfl⟩ : syracuseStep 1398595 = 2097893) B2097893
theorem B1398611 : Blo 1397518 1398611 := bstep (se 1 (by rfl) ⟨1048958, by rfl⟩ : syracuseStep 1398611 = 2097917) B2097917
theorem B1398627 : Blo 1397518 1398627 := bstep (se 1 (by rfl) ⟨1048970, by rfl⟩ : syracuseStep 1398627 = 2097941) B2097941
theorem B1398643 : Blo 1397518 1398643 := bstep (se 1 (by rfl) ⟨1048982, by rfl⟩ : syracuseStep 1398643 = 2097965) B2097965
theorem B1398659 : Blo 1397518 1398659 := bstep (se 1 (by rfl) ⟨1048994, by rfl⟩ : syracuseStep 1398659 = 2097989) B2097989
theorem B2987921 : Blo 1397518 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B1398675 : Blo 1397518 1398675 := bstep (se 1 (by rfl) ⟨1049006, by rfl⟩ : syracuseStep 1398675 = 2098013) B2098013
theorem B1398691 : Blo 1397518 1398691 := bstep (se 1 (by rfl) ⟨1049018, by rfl⟩ : syracuseStep 1398691 = 2098037) B2098037
theorem B1398707 : Blo 1397518 1398707 := bstep (se 1 (by rfl) ⟨1049030, by rfl⟩ : syracuseStep 1398707 = 2098061) B2098061
theorem B1398723 : Blo 1397518 1398723 := bstep (se 1 (by rfl) ⟨1049042, by rfl⟩ : syracuseStep 1398723 = 2098085) B2098085
theorem B10614725 : Blo 1397518 10614725 := bstep (se 4 (by rfl) ⟨995130, by rfl⟩ : syracuseStep 10614725 = 1990261) B1990261
theorem B21010373 : Blo 1397518 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B1398739 : Blo 1397518 1398739 := bstep (se 1 (by rfl) ⟨1049054, by rfl⟩ : syracuseStep 1398739 = 2098109) B2098109
theorem B15112163 : Blo 1397518 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B1398755 : Blo 1397518 1398755 := bstep (se 1 (by rfl) ⟨1049066, by rfl⟩ : syracuseStep 1398755 = 2098133) B2098133
theorem B1398771 : Blo 1397518 1398771 := bstep (se 1 (by rfl) ⟨1049078, by rfl⟩ : syracuseStep 1398771 = 2098157) B2098157
theorem B1914881 : Blo 1397518 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B1398787 : Blo 1397518 1398787 := bstep (se 1 (by rfl) ⟨1049090, by rfl⟩ : syracuseStep 1398787 = 2098181) B2098181
theorem B7960589 : Blo 1397518 7960589 := bstep (se 3 (by rfl) ⟨1492610, by rfl⟩ : syracuseStep 7960589 = 2985221) B2985221
theorem B1398803 : Blo 1397518 1398803 := bstep (se 1 (by rfl) ⟨1049102, by rfl⟩ : syracuseStep 1398803 = 2098205) B2098205
theorem B1398819 : Blo 1397518 1398819 := bstep (se 1 (by rfl) ⟨1049114, by rfl⟩ : syracuseStep 1398819 = 2098229) B2098229
theorem B1398835 : Blo 1397518 1398835 := bstep (se 1 (by rfl) ⟨1049126, by rfl⟩ : syracuseStep 1398835 = 2098253) B2098253
theorem B1398851 : Blo 1397518 1398851 := bstep (se 1 (by rfl) ⟨1049138, by rfl⟩ : syracuseStep 1398851 = 2098277) B2098277
theorem B1398867 : Blo 1397518 1398867 := bstep (se 1 (by rfl) ⟨1049150, by rfl⟩ : syracuseStep 1398867 = 2098301) B2098301
theorem B1398883 : Blo 1397518 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B30242929 : Blo 1397518 30242929 := bstep (se 2 (by rfl) ⟨11341098, by rfl⟩ : syracuseStep 30242929 = 22682197) B22682197
theorem B7968881 : Blo 1397518 7968881 := bstep (se 2 (by rfl) ⟨2988330, by rfl⟩ : syracuseStep 7968881 = 5976661) B5976661
theorem B1398899 : Blo 1397518 1398899 := bstep (se 1 (by rfl) ⟨1049174, by rfl⟩ : syracuseStep 1398899 = 2098349) B2098349
theorem B1398915 : Blo 1397518 1398915 := bstep (se 1 (by rfl) ⟨1049186, by rfl⟩ : syracuseStep 1398915 = 2098373) B2098373
theorem B1398931 : Blo 1397518 1398931 := bstep (se 1 (by rfl) ⟨1049198, by rfl⟩ : syracuseStep 1398931 = 2098397) B2098397
theorem B1398947 : Blo 1397518 1398947 := bstep (se 1 (by rfl) ⟨1049210, by rfl⟩ : syracuseStep 1398947 = 2098421) B2098421
theorem B1398963 : Blo 1397518 1398963 := bstep (se 1 (by rfl) ⟨1049222, by rfl⟩ : syracuseStep 1398963 = 2098445) B2098445
theorem B1398979 : Blo 1397518 1398979 := bstep (se 1 (by rfl) ⟨1049234, by rfl⟩ : syracuseStep 1398979 = 2098469) B2098469
theorem B22689989 : Blo 1397518 22689989 := bstep (se 4 (by rfl) ⟨2127186, by rfl⟩ : syracuseStep 22689989 = 4254373) B4254373
theorem B38811845 : Blo 1397518 38811845 := bstep (se 4 (by rfl) ⟨3638610, by rfl⟩ : syracuseStep 38811845 = 7277221) B7277221
theorem B5306573 : Blo 1397518 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B1398995 : Blo 1397518 1398995 := bstep (se 1 (by rfl) ⟨1049246, by rfl⟩ : syracuseStep 1398995 = 2098493) B2098493
theorem B1399011 : Blo 1397518 1399011 := bstep (se 1 (by rfl) ⟨1049258, by rfl⟩ : syracuseStep 1399011 = 2098517) B2098517
theorem B7084259 : Blo 1397518 7084259 := bstep (se 1 (by rfl) ⟨5313194, by rfl⟩ : syracuseStep 7084259 = 10626389) B10626389
theorem B16152817 : Blo 1397518 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1399027 : Blo 1397518 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B1399043 : Blo 1397518 1399043 := bstep (se 1 (by rfl) ⟨1049282, by rfl⟩ : syracuseStep 1399043 = 2098565) B2098565
theorem B1399059 : Blo 1397518 1399059 := bstep (se 1 (by rfl) ⟨1049294, by rfl⟩ : syracuseStep 1399059 = 2098589) B2098589
theorem B1399075 : Blo 1397518 1399075 := bstep (se 1 (by rfl) ⟨1049306, by rfl⟩ : syracuseStep 1399075 = 2098613) B2098613
theorem B2988323 : Blo 1397518 2988323 := bstep (se 1 (by rfl) ⟨2241242, by rfl⟩ : syracuseStep 2988323 = 4482485) B4482485
theorem B4716845 : Blo 1397518 4716845 := bstep (se 3 (by rfl) ⟨884408, by rfl⟩ : syracuseStep 4716845 = 1768817) B1768817
theorem B1399091 : Blo 1397518 1399091 := bstep (se 1 (by rfl) ⟨1049318, by rfl⟩ : syracuseStep 1399091 = 2098637) B2098637
theorem B1399107 : Blo 1397518 1399107 := bstep (se 1 (by rfl) ⟨1049330, by rfl⟩ : syracuseStep 1399107 = 2098661) B2098661
theorem B1890643 : Blo 1397518 1890643 := bstep (se 1 (by rfl) ⟨1417982, by rfl⟩ : syracuseStep 1890643 = 2835965) B2835965
theorem B1399123 : Blo 1397518 1399123 := bstep (se 1 (by rfl) ⟨1049342, by rfl⟩ : syracuseStep 1399123 = 2098685) B2098685
theorem B4716899 : Blo 1397518 4716899 := bstep (se 1 (by rfl) ⟨3537674, by rfl⟩ : syracuseStep 4716899 = 7075349) B7075349
theorem B1399139 : Blo 1397518 1399139 := bstep (se 1 (by rfl) ⟨1049354, by rfl⟩ : syracuseStep 1399139 = 2098709) B2098709
theorem B1399155 : Blo 1397518 1399155 := bstep (se 1 (by rfl) ⟨1049366, by rfl⟩ : syracuseStep 1399155 = 2098733) B2098733
theorem B1399171 : Blo 1397518 1399171 := bstep (se 1 (by rfl) ⟨1049378, by rfl⟩ : syracuseStep 1399171 = 2098757) B2098757
theorem B1399187 : Blo 1397518 1399187 := bstep (se 1 (by rfl) ⟨1049390, by rfl⟩ : syracuseStep 1399187 = 2098781) B2098781
theorem B1399203 : Blo 1397518 1399203 := bstep (se 1 (by rfl) ⟨1049402, by rfl⟩ : syracuseStep 1399203 = 2098805) B2098805
theorem B1399219 : Blo 1397518 1399219 := bstep (se 1 (by rfl) ⟨1049414, by rfl⟩ : syracuseStep 1399219 = 2098829) B2098829
theorem B1399235 : Blo 1397518 1399235 := bstep (se 1 (by rfl) ⟨1049426, by rfl⟩ : syracuseStep 1399235 = 2098853) B2098853
theorem B1399251 : Blo 1397518 1399251 := bstep (se 1 (by rfl) ⟨1049438, by rfl⟩ : syracuseStep 1399251 = 2098877) B2098877
theorem B1399267 : Blo 1397518 1399267 := bstep (se 1 (by rfl) ⟨1049450, by rfl⟩ : syracuseStep 1399267 = 2098901) B2098901
theorem B10623473 : Blo 1397518 10623473 := bstep (se 2 (by rfl) ⟨3983802, by rfl⟩ : syracuseStep 10623473 = 7967605) B7967605
theorem B1399283 : Blo 1397518 1399283 := bstep (se 1 (by rfl) ⟨1049462, by rfl⟩ : syracuseStep 1399283 = 2098925) B2098925
theorem B1399299 : Blo 1397518 1399299 := bstep (se 1 (by rfl) ⟨1049474, by rfl⟩ : syracuseStep 1399299 = 2098949) B2098949
theorem B3979793 : Blo 1397518 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B1399315 : Blo 1397518 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B1399331 : Blo 1397518 1399331 := bstep (se 1 (by rfl) ⟨1049498, by rfl⟩ : syracuseStep 1399331 = 2098997) B2098997
theorem B4037165 : Blo 1397518 4037165 := bstep (se 3 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 4037165 = 1513937) B1513937
theorem B1399347 : Blo 1397518 1399347 := bstep (se 1 (by rfl) ⟨1049510, by rfl⟩ : syracuseStep 1399347 = 2099021) B2099021
theorem B1399363 : Blo 1397518 1399363 := bstep (se 1 (by rfl) ⟨1049522, by rfl⟩ : syracuseStep 1399363 = 2099045) B2099045
theorem B1399379 : Blo 1397518 1399379 := bstep (se 1 (by rfl) ⟨1049534, by rfl⟩ : syracuseStep 1399379 = 2099069) B2099069
theorem B1399395 : Blo 1397518 1399395 := bstep (se 1 (by rfl) ⟨1049546, by rfl⟩ : syracuseStep 1399395 = 2099093) B2099093
theorem B4717169 : Blo 1397518 4717169 := bstep (se 2 (by rfl) ⟨1768938, by rfl⟩ : syracuseStep 4717169 = 3537877) B3537877
theorem B1514099 : Blo 1397518 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B1399411 : Blo 1397518 1399411 := bstep (se 1 (by rfl) ⟨1049558, by rfl⟩ : syracuseStep 1399411 = 2099117) B2099117
theorem B1399427 : Blo 1397518 1399427 := bstep (se 1 (by rfl) ⟨1049570, by rfl⟩ : syracuseStep 1399427 = 2099141) B2099141
theorem B3537553 : Blo 1397518 3537553 := bstep (se 2 (by rfl) ⟨1326582, by rfl⟩ : syracuseStep 3537553 = 2653165) B2653165
theorem B1399443 : Blo 1397518 1399443 := bstep (se 1 (by rfl) ⟨1049582, by rfl⟩ : syracuseStep 1399443 = 2099165) B2099165
theorem B1399459 : Blo 1397518 1399459 := bstep (se 1 (by rfl) ⟨1049594, by rfl⟩ : syracuseStep 1399459 = 2099189) B2099189
theorem B1399475 : Blo 1397518 1399475 := bstep (se 1 (by rfl) ⟨1049606, by rfl⟩ : syracuseStep 1399475 = 2099213) B2099213
theorem B1399491 : Blo 1397518 1399491 := bstep (se 1 (by rfl) ⟨1049618, by rfl⟩ : syracuseStep 1399491 = 2099237) B2099237
theorem B1399507 : Blo 1397518 1399507 := bstep (se 1 (by rfl) ⟨1049630, by rfl⟩ : syracuseStep 1399507 = 2099261) B2099261
theorem B3144419 : Blo 1397518 3144419 := bstep (se 1 (by rfl) ⟨2358314, by rfl⟩ : syracuseStep 3144419 = 4716629) B4716629
theorem B3586787 : Blo 1397518 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B2521859 : Blo 1397518 2521859 := bstep (se 1 (by rfl) ⟨1891394, by rfl⟩ : syracuseStep 2521859 = 3782789) B3782789
theorem B5036813 : Blo 1397518 5036813 := bstep (se 3 (by rfl) ⟨944402, by rfl⟩ : syracuseStep 5036813 = 1888805) B1888805
theorem B11950861 : Blo 1397518 11950861 := bstep (se 3 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 11950861 = 4481573) B4481573
theorem B6716209 : Blo 1397518 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B4479857 : Blo 1397518 4479857 := bstep (se 2 (by rfl) ⟨1679946, by rfl⟩ : syracuseStep 4479857 = 3359893) B3359893
theorem B3537827 : Blo 1397518 3537827 := bstep (se 1 (by rfl) ⟨2653370, by rfl⟩ : syracuseStep 3537827 = 5306741) B5306741
theorem B3144689 : Blo 1397518 3144689 := bstep (se 2 (by rfl) ⟨1179258, by rfl⟩ : syracuseStep 3144689 = 2358517) B2358517
theorem B3144707 : Blo 1397518 3144707 := bstep (se 1 (by rfl) ⟨2358530, by rfl⟩ : syracuseStep 3144707 = 4717061) B4717061
theorem B2358355 : Blo 1397518 2358355 := bstep (se 1 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 2358355 = 3537533) B3537533
theorem B3538019 : Blo 1397518 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B4717709 : Blo 1397518 4717709 := bstep (se 3 (by rfl) ⟨884570, by rfl⟩ : syracuseStep 4717709 = 1769141) B1769141
theorem B2096291 : Blo 1397518 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B2096321 : Blo 1397518 2096321 := bstep (se 2 (by rfl) ⟨786120, by rfl⟩ : syracuseStep 2096321 = 1572241) B1572241
theorem B4717763 : Blo 1397518 4717763 := bstep (se 1 (by rfl) ⟨3538322, by rfl⟩ : syracuseStep 4717763 = 7076645) B7076645
theorem B2653393 : Blo 1397518 2653393 := bstep (se 2 (by rfl) ⟨995022, by rfl⟩ : syracuseStep 2653393 = 1990045) B1990045
theorem B2096339 : Blo 1397518 2096339 := bstep (se 1 (by rfl) ⟨1572254, by rfl⟩ : syracuseStep 2096339 = 3144509) B3144509
theorem B2358497 : Blo 1397518 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B2096369 : Blo 1397518 2096369 := bstep (se 2 (by rfl) ⟨786138, by rfl⟩ : syracuseStep 2096369 = 1572277) B1572277
theorem B2096387 : Blo 1397518 2096387 := bstep (se 1 (by rfl) ⟨1572290, by rfl⟩ : syracuseStep 2096387 = 3144581) B3144581
theorem B3144977 : Blo 1397518 3144977 := bstep (se 2 (by rfl) ⟨1179366, by rfl⟩ : syracuseStep 3144977 = 2358733) B2358733
theorem B2096417 : Blo 1397518 2096417 := bstep (se 2 (by rfl) ⟨786156, by rfl⟩ : syracuseStep 2096417 = 1572313) B1572313
theorem B3144995 : Blo 1397518 3144995 := bstep (se 1 (by rfl) ⟨2358746, by rfl⟩ : syracuseStep 3144995 = 4717493) B4717493
theorem B1989937 : Blo 1397518 1989937 := bstep (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) B1492453
theorem B2096435 : Blo 1397518 2096435 := bstep (se 1 (by rfl) ⟨1572326, by rfl⟩ : syracuseStep 2096435 = 3144653) B3144653
theorem B2096465 : Blo 1397518 2096465 := bstep (se 2 (by rfl) ⟨786174, by rfl⟩ : syracuseStep 2096465 = 1572349) B1572349
theorem B2358625 : Blo 1397518 2358625 := bstep (se 2 (by rfl) ⟨884484, by rfl⟩ : syracuseStep 2358625 = 1768969) B1768969
theorem B2096483 : Blo 1397518 2096483 := bstep (se 1 (by rfl) ⟨1572362, by rfl⟩ : syracuseStep 2096483 = 3144725) B3144725
theorem B2653553 : Blo 1397518 2653553 := bstep (se 2 (by rfl) ⟨995082, by rfl⟩ : syracuseStep 2653553 = 1990165) B1990165
theorem B2096513 : Blo 1397518 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B2358659 : Blo 1397518 2358659 := bstep (se 1 (by rfl) ⟨1768994, by rfl⟩ : syracuseStep 2358659 = 3537989) B3537989
theorem B2096531 : Blo 1397518 2096531 := bstep (se 1 (by rfl) ⟨1572398, by rfl⟩ : syracuseStep 2096531 = 3144797) B3144797
theorem B1572259 : Blo 1397518 1572259 := bstep (se 1 (by rfl) ⟨1179194, by rfl⟩ : syracuseStep 1572259 = 2358389) B2358389
theorem B2096561 : Blo 1397518 2096561 := bstep (se 2 (by rfl) ⟨786210, by rfl⟩ : syracuseStep 2096561 = 1572421) B1572421
theorem B2096579 : Blo 1397518 2096579 := bstep (se 1 (by rfl) ⟨1572434, by rfl⟩ : syracuseStep 2096579 = 3144869) B3144869
theorem B4718033 : Blo 1397518 4718033 := bstep (se 2 (by rfl) ⟨1769262, by rfl⟩ : syracuseStep 4718033 = 3538525) B3538525
theorem B2096609 : Blo 1397518 2096609 := bstep (se 2 (by rfl) ⟨786228, by rfl⟩ : syracuseStep 2096609 = 1572457) B1572457
theorem B3980785 : Blo 1397518 3980785 := bstep (se 2 (by rfl) ⟨1492794, by rfl⟩ : syracuseStep 3980785 = 2985589) B2985589
theorem B2096627 : Blo 1397518 2096627 := bstep (se 1 (by rfl) ⟨1572470, by rfl⟩ : syracuseStep 2096627 = 3144941) B3144941
theorem B2358787 : Blo 1397518 2358787 := bstep (se 1 (by rfl) ⟨1769090, by rfl⟩ : syracuseStep 2358787 = 3538181) B3538181
theorem B2096657 : Blo 1397518 2096657 := bstep (se 2 (by rfl) ⟨786246, by rfl⟩ : syracuseStep 2096657 = 1572493) B1572493
theorem B1768979 : Blo 1397518 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B2096675 : Blo 1397518 2096675 := bstep (se 1 (by rfl) ⟨1572506, by rfl⟩ : syracuseStep 2096675 = 3145013) B3145013
theorem B7970339 : Blo 1397518 7970339 := bstep (se 1 (by rfl) ⟨5977754, by rfl⟩ : syracuseStep 7970339 = 11955509) B11955509
theorem B3145265 : Blo 1397518 3145265 := bstep (se 2 (by rfl) ⟨1179474, by rfl⟩ : syracuseStep 3145265 = 2358949) B2358949
theorem B1572403 : Blo 1397518 1572403 := bstep (se 1 (by rfl) ⟨1179302, by rfl⟩ : syracuseStep 1572403 = 2358605) B2358605
theorem B2096705 : Blo 1397518 2096705 := bstep (se 2 (by rfl) ⟨786264, by rfl⟩ : syracuseStep 2096705 = 1572529) B1572529
theorem B3145283 : Blo 1397518 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B2096723 : Blo 1397518 2096723 := bstep (se 1 (by rfl) ⟨1572542, by rfl⟩ : syracuseStep 2096723 = 3145085) B3145085
theorem B2096753 : Blo 1397518 2096753 := bstep (se 2 (by rfl) ⟨786282, by rfl⟩ : syracuseStep 2096753 = 1572565) B1572565
theorem B1990273 : Blo 1397518 1990273 := bstep (se 2 (by rfl) ⟨746352, by rfl⟩ : syracuseStep 1990273 = 1492705) B1492705
theorem B2096771 : Blo 1397518 2096771 := bstep (se 1 (by rfl) ⟨1572578, by rfl⟩ : syracuseStep 2096771 = 3145157) B3145157
theorem B2358929 : Blo 1397518 2358929 := bstep (se 2 (by rfl) ⟨884598, by rfl⟩ : syracuseStep 2358929 = 1769197) B1769197
theorem B2391697 : Blo 1397518 2391697 := bstep (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) B1793773
theorem B2096801 : Blo 1397518 2096801 := bstep (se 2 (by rfl) ⟨786300, by rfl⟩ : syracuseStep 2096801 = 1572601) B1572601
theorem B2096819 : Blo 1397518 2096819 := bstep (se 1 (by rfl) ⟨1572614, by rfl⟩ : syracuseStep 2096819 = 3145229) B3145229
theorem B1572547 : Blo 1397518 1572547 := bstep (se 1 (by rfl) ⟨1179410, by rfl⟩ : syracuseStep 1572547 = 2358821) B2358821
theorem B2096849 : Blo 1397518 2096849 := bstep (se 2 (by rfl) ⟨786318, by rfl⟩ : syracuseStep 2096849 = 1572637) B1572637
theorem B2096867 : Blo 1397518 2096867 := bstep (se 1 (by rfl) ⟨1572650, by rfl⟩ : syracuseStep 2096867 = 3145301) B3145301
theorem B7077617 : Blo 1397518 7077617 := bstep (se 2 (by rfl) ⟨2654106, by rfl⟩ : syracuseStep 7077617 = 5308213) B5308213
theorem B4480753 : Blo 1397518 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B2096897 : Blo 1397518 2096897 := bstep (se 2 (by rfl) ⟨786336, by rfl⟩ : syracuseStep 2096897 = 1572673) B1572673
theorem B2653955 : Blo 1397518 2653955 := bstep (se 1 (by rfl) ⟨1990466, by rfl⟩ : syracuseStep 2653955 = 3980933) B3980933
theorem B3981059 : Blo 1397518 3981059 := bstep (se 1 (by rfl) ⟨2985794, by rfl⟩ : syracuseStep 3981059 = 5971589) B5971589
theorem B2359057 : Blo 1397518 2359057 := bstep (se 2 (by rfl) ⟨884646, by rfl⟩ : syracuseStep 2359057 = 1769293) B1769293
theorem B2096915 : Blo 1397518 2096915 := bstep (se 1 (by rfl) ⟨1572686, by rfl⟩ : syracuseStep 2096915 = 3145373) B3145373
theorem B2096945 : Blo 1397518 2096945 := bstep (se 2 (by rfl) ⟨786354, by rfl⟩ : syracuseStep 2096945 = 1572709) B1572709
theorem B2359091 : Blo 1397518 2359091 := bstep (se 1 (by rfl) ⟨1769318, by rfl⟩ : syracuseStep 2359091 = 3538637) B3538637
theorem B2096963 : Blo 1397518 2096963 := bstep (se 1 (by rfl) ⟨1572722, by rfl⟩ : syracuseStep 2096963 = 3145445) B3145445
theorem B3145553 : Blo 1397518 3145553 := bstep (se 2 (by rfl) ⟨1179582, by rfl⟩ : syracuseStep 3145553 = 2359165) B2359165
theorem B1572691 : Blo 1397518 1572691 := bstep (se 1 (by rfl) ⟨1179518, by rfl⟩ : syracuseStep 1572691 = 2359037) B2359037
theorem B2096993 : Blo 1397518 2096993 := bstep (se 2 (by rfl) ⟨786372, by rfl⟩ : syracuseStep 2096993 = 1572745) B1572745
theorem B3145571 : Blo 1397518 3145571 := bstep (se 1 (by rfl) ⟨2359178, by rfl⟩ : syracuseStep 3145571 = 4718357) B4718357
theorem B4251491 : Blo 1397518 4251491 := bstep (se 1 (by rfl) ⟨3188618, by rfl⟩ : syracuseStep 4251491 = 6377237) B6377237
theorem B2097011 : Blo 1397518 2097011 := bstep (se 1 (by rfl) ⟨1572758, by rfl⟩ : syracuseStep 2097011 = 3145517) B3145517
theorem B6717325 : Blo 1397518 6717325 := bstep (se 3 (by rfl) ⟨1259498, by rfl⟩ : syracuseStep 6717325 = 2518997) B2518997
theorem B7470989 : Blo 1397518 7470989 := bstep (se 3 (by rfl) ⟨1400810, by rfl⟩ : syracuseStep 7470989 = 2801621) B2801621
theorem B2097041 : Blo 1397518 2097041 := bstep (se 2 (by rfl) ⟨786390, by rfl⟩ : syracuseStep 2097041 = 1572781) B1572781
theorem B2097059 : Blo 1397518 2097059 := bstep (se 1 (by rfl) ⟨1572794, by rfl⟩ : syracuseStep 2097059 = 3145589) B3145589
theorem B2359219 : Blo 1397518 2359219 := bstep (se 1 (by rfl) ⟨1769414, by rfl⟩ : syracuseStep 2359219 = 3538829) B3538829
theorem B2097089 : Blo 1397518 2097089 := bstep (se 2 (by rfl) ⟨786408, by rfl⟩ : syracuseStep 2097089 = 1572817) B1572817
theorem B3981251 : Blo 1397518 3981251 := bstep (se 1 (by rfl) ⟨2985938, by rfl⟩ : syracuseStep 3981251 = 5971877) B5971877
theorem B2097107 : Blo 1397518 2097107 := bstep (se 1 (by rfl) ⟨1572830, by rfl⟩ : syracuseStep 2097107 = 3145661) B3145661
theorem B1572835 : Blo 1397518 1572835 := bstep (se 1 (by rfl) ⟨1179626, by rfl⟩ : syracuseStep 1572835 = 2359253) B2359253
theorem B4718573 : Blo 1397518 4718573 := bstep (se 3 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 4718573 = 1769465) B1769465
theorem B2097137 : Blo 1397518 2097137 := bstep (se 2 (by rfl) ⟨786426, by rfl⟩ : syracuseStep 2097137 = 1572853) B1572853
theorem B2359307 : Blo 1397518 2359307 := bstep (se 1 (by rfl) ⟨1769480, by rfl⟩ : syracuseStep 2359307 = 3538961) B3538961
theorem B3145751 : Blo 1397518 3145751 := bstep (se 1 (by rfl) ⟨2359313, by rfl⟩ : syracuseStep 3145751 = 4718627) B4718627
theorem B15532067 : Blo 1397518 15532067 := bstep (se 1 (by rfl) ⟨11649050, by rfl⟩ : syracuseStep 15532067 = 23298101) B23298101
theorem B12754979 : Blo 1397518 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B1572907 : Blo 1397518 1572907 := bstep (se 1 (by rfl) ⟨1179680, by rfl⟩ : syracuseStep 1572907 = 2359361) B2359361
theorem B43049029 : Blo 1397518 43049029 := bstep (se 4 (by rfl) ⟨4035846, by rfl⟩ : syracuseStep 43049029 = 8071693) B8071693
theorem B2097227 : Blo 1397518 2097227 := bstep (se 1 (by rfl) ⟨1572920, by rfl⟩ : syracuseStep 2097227 = 3145841) B3145841
theorem B2097239 : Blo 1397518 2097239 := bstep (se 1 (by rfl) ⟨1572929, by rfl⟩ : syracuseStep 2097239 = 3145859) B3145859
theorem B4718681 : Blo 1397518 4718681 := bstep (se 2 (by rfl) ⟨1769505, by rfl⟩ : syracuseStep 4718681 = 3539011) B3539011
theorem B2359435 : Blo 1397518 2359435 := bstep (se 1 (by rfl) ⟨1769576, by rfl⟩ : syracuseStep 2359435 = 3539153) B3539153
theorem B1573015 : Blo 1397518 1573015 := bstep (se 1 (by rfl) ⟨1179761, by rfl⟩ : syracuseStep 1573015 = 2359523) B2359523
theorem B2097305 : Blo 1397518 2097305 := bstep (se 2 (by rfl) ⟨786489, by rfl⟩ : syracuseStep 2097305 = 1572979) B1572979
theorem B3539123 : Blo 1397518 3539123 := bstep (se 1 (by rfl) ⟨2654342, by rfl⟩ : syracuseStep 3539123 = 5308685) B5308685
theorem B3145931 : Blo 1397518 3145931 := bstep (se 1 (by rfl) ⟨2359448, by rfl⟩ : syracuseStep 3145931 = 4718897) B4718897
theorem B2834635 : Blo 1397518 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B3145985 : Blo 1397518 3145985 := bstep (se 2 (by rfl) ⟨1179744, by rfl⟩ : syracuseStep 3145985 = 2359489) B2359489
theorem B2097419 : Blo 1397518 2097419 := bstep (se 1 (by rfl) ⟨1573064, by rfl⟩ : syracuseStep 2097419 = 3146129) B3146129
theorem B5669137 : Blo 1397518 5669137 := bstep (se 2 (by rfl) ⟨2125926, by rfl⟩ : syracuseStep 5669137 = 4251853) B4251853
theorem B93184277 : Blo 1397518 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B2097431 : Blo 1397518 2097431 := bstep (se 1 (by rfl) ⟨1573073, by rfl⟩ : syracuseStep 2097431 = 3146147) B3146147
theorem B2359577 : Blo 1397518 2359577 := bstep (se 2 (by rfl) ⟨884841, by rfl⟩ : syracuseStep 2359577 = 1769683) B1769683
theorem B3359027 : Blo 1397518 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B21537089 : Blo 1397518 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B1573195 : Blo 1397518 1573195 := bstep (se 1 (by rfl) ⟨1179896, by rfl⟩ : syracuseStep 1573195 = 2359793) B2359793
theorem B2097497 : Blo 1397518 2097497 := bstep (se 2 (by rfl) ⟨786561, by rfl⟩ : syracuseStep 2097497 = 1573123) B1573123
theorem B4481369 : Blo 1397518 4481369 := bstep (se 2 (by rfl) ⟨1680513, by rfl⟩ : syracuseStep 4481369 = 3361027) B3361027
theorem B11493733 : Blo 1397518 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B2359705 : Blo 1397518 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B1573303 : Blo 1397518 1573303 := bstep (se 1 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 1573303 = 2359955) B2359955
theorem B2097611 : Blo 1397518 2097611 := bstep (se 1 (by rfl) ⟨1573208, by rfl⟩ : syracuseStep 2097611 = 3146417) B3146417
theorem B2097623 : Blo 1397518 2097623 := bstep (se 1 (by rfl) ⟨1573217, by rfl⟩ : syracuseStep 2097623 = 3146435) B3146435
theorem B3146201 : Blo 1397518 3146201 := bstep (se 2 (by rfl) ⟨1179825, by rfl⟩ : syracuseStep 3146201 = 2359651) B2359651
theorem B4481497 : Blo 1397518 4481497 := bstep (se 2 (by rfl) ⟨1680561, by rfl⟩ : syracuseStep 4481497 = 3361123) B3361123
theorem B2654707 : Blo 1397518 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B1770007 : Blo 1397518 1770007 := bstep (se 1 (by rfl) ⟨1327505, by rfl⟩ : syracuseStep 1770007 = 2655011) B2655011
theorem B2097689 : Blo 1397518 2097689 := bstep (se 2 (by rfl) ⟨786633, by rfl⟩ : syracuseStep 2097689 = 1573267) B1573267
theorem B5308973 : Blo 1397518 5308973 := bstep (se 3 (by rfl) ⟨995432, by rfl⟩ : syracuseStep 5308973 = 1990865) B1990865
theorem B5038643 : Blo 1397518 5038643 := bstep (se 1 (by rfl) ⟨3778982, by rfl⟩ : syracuseStep 5038643 = 7557965) B7557965
theorem B3146291 : Blo 1397518 3146291 := bstep (se 1 (by rfl) ⟨2359718, by rfl⟩ : syracuseStep 3146291 = 4719437) B4719437
theorem B3981889 : Blo 1397518 3981889 := bstep (se 2 (by rfl) ⟨1493208, by rfl⟩ : syracuseStep 3981889 = 2986417) B2986417
theorem B5309003 : Blo 1397518 5309003 := bstep (se 1 (by rfl) ⟨3981752, by rfl⟩ : syracuseStep 5309003 = 7963505) B7963505
theorem B3146327 : Blo 1397518 3146327 := bstep (se 1 (by rfl) ⟨2359745, by rfl⟩ : syracuseStep 3146327 = 4719491) B4719491
theorem B1573483 : Blo 1397518 1573483 := bstep (se 1 (by rfl) ⟨1180112, by rfl⟩ : syracuseStep 1573483 = 2360225) B2360225
theorem B2097803 : Blo 1397518 2097803 := bstep (se 1 (by rfl) ⟨1573352, by rfl⟩ : syracuseStep 2097803 = 3146705) B3146705
theorem B2097815 : Blo 1397518 2097815 := bstep (se 1 (by rfl) ⟨1573361, by rfl⟩ : syracuseStep 2097815 = 3146723) B3146723
theorem B8077975 : Blo 1397518 8077975 := bstep (se 1 (by rfl) ⟨6058481, by rfl⟩ : syracuseStep 8077975 = 12116963) B12116963
theorem B4539073 : Blo 1397518 4539073 := bstep (se 2 (by rfl) ⟨1702152, by rfl⟩ : syracuseStep 4539073 = 3404305) B3404305
theorem B3539659 : Blo 1397518 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B11952845 : Blo 1397518 11952845 := bstep (se 3 (by rfl) ⟨2241158, by rfl⟩ : syracuseStep 11952845 = 4482317) B4482317
theorem B1573591 : Blo 1397518 1573591 := bstep (se 1 (by rfl) ⟨1180193, by rfl⟩ : syracuseStep 1573591 = 2360387) B2360387
theorem B2097881 : Blo 1397518 2097881 := bstep (se 2 (by rfl) ⟨786705, by rfl⟩ : syracuseStep 2097881 = 1573411) B1573411
theorem B3146507 : Blo 1397518 3146507 := bstep (se 1 (by rfl) ⟨2359880, by rfl⟩ : syracuseStep 3146507 = 4719761) B4719761
theorem B4719383 : Blo 1397518 4719383 := bstep (se 1 (by rfl) ⟨3539537, by rfl⟩ : syracuseStep 4719383 = 7079075) B7079075
theorem B3146561 : Blo 1397518 3146561 := bstep (se 2 (by rfl) ⟨1179960, by rfl⟩ : syracuseStep 3146561 = 2359921) B2359921
theorem B2097995 : Blo 1397518 2097995 := bstep (se 1 (by rfl) ⟨1573496, by rfl⟩ : syracuseStep 2097995 = 3146993) B3146993
theorem B2098007 : Blo 1397518 2098007 := bstep (se 1 (by rfl) ⟨1573505, by rfl⟩ : syracuseStep 2098007 = 3147011) B3147011
theorem B3539801 : Blo 1397518 3539801 := bstep (se 2 (by rfl) ⟨1327425, by rfl⟩ : syracuseStep 3539801 = 2654851) B2654851
theorem B1573771 : Blo 1397518 1573771 := bstep (se 1 (by rfl) ⟨1180328, by rfl⟩ : syracuseStep 1573771 = 2360657) B2360657
theorem B2098073 : Blo 1397518 2098073 := bstep (se 2 (by rfl) ⟨786777, by rfl⟩ : syracuseStep 2098073 = 1573555) B1573555
theorem B2655155 : Blo 1397518 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B2360279 : Blo 1397518 2360279 := bstep (se 1 (by rfl) ⟨1770209, by rfl⟩ : syracuseStep 2360279 = 3540419) B3540419
theorem B2655193 : Blo 1397518 2655193 := bstep (se 2 (by rfl) ⟨995697, by rfl⟩ : syracuseStep 2655193 = 1991395) B1991395
theorem B1573879 : Blo 1397518 1573879 := bstep (se 1 (by rfl) ⟨1180409, by rfl⟩ : syracuseStep 1573879 = 2360819) B2360819
theorem B2098187 : Blo 1397518 2098187 := bstep (se 1 (by rfl) ⟨1573640, by rfl⟩ : syracuseStep 2098187 = 3147281) B3147281
theorem B15934481 : Blo 1397518 15934481 := bstep (se 2 (by rfl) ⟨5975430, by rfl⟩ : syracuseStep 15934481 = 11950861) B11950861
theorem B2098199 : Blo 1397518 2098199 := bstep (se 1 (by rfl) ⟨1573649, by rfl⟩ : syracuseStep 2098199 = 3147299) B3147299
theorem B3146777 : Blo 1397518 3146777 := bstep (se 2 (by rfl) ⟨1180041, by rfl⟩ : syracuseStep 3146777 = 2360083) B2360083
theorem B8954945 : Blo 1397518 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B2360407 : Blo 1397518 2360407 := bstep (se 1 (by rfl) ⟨1770305, by rfl⟩ : syracuseStep 2360407 = 3540611) B3540611
theorem B2098265 : Blo 1397518 2098265 := bstep (se 2 (by rfl) ⟨786849, by rfl⟩ : syracuseStep 2098265 = 1573699) B1573699
theorem B3146867 : Blo 1397518 3146867 := bstep (se 1 (by rfl) ⟨2360150, by rfl⟩ : syracuseStep 3146867 = 4720301) B4720301
theorem B3146903 : Blo 1397518 3146903 := bstep (se 1 (by rfl) ⟨2360177, by rfl⟩ : syracuseStep 3146903 = 4720355) B4720355
theorem B1574059 : Blo 1397518 1574059 := bstep (se 1 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 1574059 = 2361089) B2361089
theorem B2098379 : Blo 1397518 2098379 := bstep (se 1 (by rfl) ⟨1573784, by rfl⟩ : syracuseStep 2098379 = 3147569) B3147569
theorem B2098391 : Blo 1397518 2098391 := bstep (se 1 (by rfl) ⟨1573793, by rfl⟩ : syracuseStep 2098391 = 3147587) B3147587
theorem B5309657 : Blo 1397518 5309657 := bstep (se 2 (by rfl) ⟨1991121, by rfl⟩ : syracuseStep 5309657 = 3982243) B3982243
theorem B1991947 : Blo 1397518 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B1574167 : Blo 1397518 1574167 := bstep (se 1 (by rfl) ⟨1180625, by rfl⟩ : syracuseStep 1574167 = 2361251) B2361251
theorem B2098457 : Blo 1397518 2098457 := bstep (se 2 (by rfl) ⟨786921, by rfl⟩ : syracuseStep 2098457 = 1573843) B1573843
theorem B4719923 : Blo 1397518 4719923 := bstep (se 1 (by rfl) ⟨3539942, by rfl⟩ : syracuseStep 4719923 = 7079885) B7079885
theorem B3147083 : Blo 1397518 3147083 := bstep (se 1 (by rfl) ⟨2360312, by rfl⟩ : syracuseStep 3147083 = 4720625) B4720625
theorem B3147137 : Blo 1397518 3147137 := bstep (se 2 (by rfl) ⟨1180176, by rfl⟩ : syracuseStep 3147137 = 2360353) B2360353
theorem B2098571 : Blo 1397518 2098571 := bstep (se 1 (by rfl) ⟨1573928, by rfl⟩ : syracuseStep 2098571 = 3147857) B3147857
theorem B2098583 : Blo 1397518 2098583 := bstep (se 1 (by rfl) ⟨1573937, by rfl⟩ : syracuseStep 2098583 = 3147875) B3147875
theorem B2655641 : Blo 1397518 2655641 := bstep (se 2 (by rfl) ⟨995865, by rfl⟩ : syracuseStep 2655641 = 1991731) B1991731
theorem B5383597 : Blo 1397518 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B11339185 : Blo 1397518 11339185 := bstep (se 2 (by rfl) ⟨4252194, by rfl⟩ : syracuseStep 11339185 = 8504389) B8504389
theorem B1574347 : Blo 1397518 1574347 := bstep (se 1 (by rfl) ⟨1180760, by rfl⟩ : syracuseStep 1574347 = 2361521) B2361521
theorem B2098649 : Blo 1397518 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B5309975 : Blo 1397518 5309975 := bstep (se 1 (by rfl) ⟨3982481, by rfl⟩ : syracuseStep 5309975 = 7964963) B7964963
theorem B1992215 : Blo 1397518 1992215 := bstep (se 1 (by rfl) ⟨1494161, by rfl⟩ : syracuseStep 1992215 = 2988323) B2988323
theorem B1574455 : Blo 1397518 1574455 := bstep (se 1 (by rfl) ⟨1180841, by rfl⟩ : syracuseStep 1574455 = 2361683) B2361683
theorem B4720193 : Blo 1397518 4720193 := bstep (se 2 (by rfl) ⟨1770072, by rfl⟩ : syracuseStep 4720193 = 3540145) B3540145
theorem B2098763 : Blo 1397518 2098763 := bstep (se 1 (by rfl) ⟨1574072, by rfl⟩ : syracuseStep 2098763 = 3148145) B3148145
theorem B2098775 : Blo 1397518 2098775 := bstep (se 1 (by rfl) ⟨1574081, by rfl⟩ : syracuseStep 2098775 = 3148163) B3148163
theorem B3147353 : Blo 1397518 3147353 := bstep (se 2 (by rfl) ⟨1180257, by rfl⟩ : syracuseStep 3147353 = 2360515) B2360515
theorem B53773955 : Blo 1397518 53773955 := bstep (se 1 (by rfl) ⟨40330466, by rfl⟩ : syracuseStep 53773955 = 80660933) B80660933
theorem B3540631 : Blo 1397518 3540631 := bstep (se 1 (by rfl) ⟨2655473, by rfl⟩ : syracuseStep 3540631 = 5310947) B5310947
theorem B2098841 : Blo 1397518 2098841 := bstep (se 2 (by rfl) ⟨787065, by rfl⟩ : syracuseStep 2098841 = 1574131) B1574131
theorem B3147443 : Blo 1397518 3147443 := bstep (se 1 (by rfl) ⟨2360582, by rfl⟩ : syracuseStep 3147443 = 4721165) B4721165
theorem B2361035 : Blo 1397518 2361035 := bstep (se 1 (by rfl) ⟨1770776, by rfl⟩ : syracuseStep 2361035 = 3541553) B3541553
theorem B3147479 : Blo 1397518 3147479 := bstep (se 1 (by rfl) ⟨2360609, by rfl⟩ : syracuseStep 3147479 = 4721219) B4721219
theorem B2098955 : Blo 1397518 2098955 := bstep (se 1 (by rfl) ⟨1574216, by rfl⟩ : syracuseStep 2098955 = 3148433) B3148433
theorem B2098967 : Blo 1397518 2098967 := bstep (se 1 (by rfl) ⟨1574225, by rfl⟩ : syracuseStep 2098967 = 3148451) B3148451
theorem B2361163 : Blo 1397518 2361163 := bstep (se 1 (by rfl) ⟨1770872, by rfl⟩ : syracuseStep 2361163 = 3541745) B3541745
theorem B2099033 : Blo 1397518 2099033 := bstep (se 2 (by rfl) ⟨787137, by rfl⟩ : syracuseStep 2099033 = 1574275) B1574275
theorem B3147659 : Blo 1397518 3147659 := bstep (se 1 (by rfl) ⟨2360744, by rfl⟩ : syracuseStep 3147659 = 4721489) B4721489
theorem B3147713 : Blo 1397518 3147713 := bstep (se 2 (by rfl) ⟨1180392, by rfl⟩ : syracuseStep 3147713 = 2360785) B2360785
theorem B2099147 : Blo 1397518 2099147 := bstep (se 1 (by rfl) ⟨1574360, by rfl⟩ : syracuseStep 2099147 = 3148721) B3148721
theorem B2099159 : Blo 1397518 2099159 := bstep (se 1 (by rfl) ⟨1574369, by rfl⟩ : syracuseStep 2099159 = 3148739) B3148739
theorem B2361305 : Blo 1397518 2361305 := bstep (se 2 (by rfl) ⟨885489, by rfl⟩ : syracuseStep 2361305 = 1770979) B1770979
theorem B7964689 : Blo 1397518 7964689 := bstep (se 2 (by rfl) ⟨2986758, by rfl⟩ : syracuseStep 7964689 = 5973517) B5973517
theorem B2099225 : Blo 1397518 2099225 := bstep (se 2 (by rfl) ⟨787209, by rfl⟩ : syracuseStep 2099225 = 1574419) B1574419
theorem B3541067 : Blo 1397518 3541067 := bstep (se 1 (by rfl) ⟨2655800, by rfl⟩ : syracuseStep 3541067 = 5311601) B5311601
theorem B2361433 : Blo 1397518 2361433 := bstep (se 2 (by rfl) ⟨885537, by rfl⟩ : syracuseStep 2361433 = 1771075) B1771075
theorem B4720733 : Blo 1397518 4720733 := bstep (se 3 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 4720733 = 1770275) B1770275
theorem B2656385 : Blo 1397518 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B3147929 : Blo 1397518 3147929 := bstep (se 2 (by rfl) ⟨1180473, by rfl⟩ : syracuseStep 3147929 = 2360947) B2360947
theorem B5040301 : Blo 1397518 5040301 := bstep (se 3 (by rfl) ⟨945056, by rfl⟩ : syracuseStep 5040301 = 1890113) B1890113
theorem B5310643 : Blo 1397518 5310643 := bstep (se 1 (by rfl) ⟨3982982, by rfl⟩ : syracuseStep 5310643 = 7965965) B7965965
theorem B3188929 : Blo 1397518 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B3148019 : Blo 1397518 3148019 := bstep (se 1 (by rfl) ⟨2361014, by rfl⟩ : syracuseStep 3148019 = 4722029) B4722029
theorem B7080209 : Blo 1397518 7080209 := bstep (se 2 (by rfl) ⟨2655078, by rfl⟩ : syracuseStep 7080209 = 5310157) B5310157
theorem B3148055 : Blo 1397518 3148055 := bstep (se 1 (by rfl) ⟨2361041, by rfl⟩ : syracuseStep 3148055 = 4722083) B4722083
theorem B5974337 : Blo 1397518 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B2656651 : Blo 1397518 2656651 := bstep (se 1 (by rfl) ⟨1992488, by rfl⟩ : syracuseStep 2656651 = 3984977) B3984977
theorem B7080371 : Blo 1397518 7080371 := bstep (se 1 (by rfl) ⟨5310278, by rfl⟩ : syracuseStep 7080371 = 10620557) B10620557
theorem B3541441 : Blo 1397518 3541441 := bstep (se 2 (by rfl) ⟨1328040, by rfl⟩ : syracuseStep 3541441 = 2656081) B2656081
theorem B3148235 : Blo 1397518 3148235 := bstep (se 1 (by rfl) ⟨2361176, by rfl⟩ : syracuseStep 3148235 = 4722353) B4722353
theorem B3148289 : Blo 1397518 3148289 := bstep (se 2 (by rfl) ⟨1180608, by rfl⟩ : syracuseStep 3148289 = 2361217) B2361217
theorem B8956433 : Blo 1397518 8956433 := bstep (se 2 (by rfl) ⟨3358662, by rfl⟩ : syracuseStep 8956433 = 6717325) B6717325
theorem B5106349 : Blo 1397518 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B1493687 : Blo 1397518 1493687 := bstep (se 1 (by rfl) ⟨1120265, by rfl⟩ : syracuseStep 1493687 = 2240531) B2240531
theorem B3148505 : Blo 1397518 3148505 := bstep (se 2 (by rfl) ⟨1180689, by rfl⟩ : syracuseStep 3148505 = 2361379) B2361379
theorem B3148595 : Blo 1397518 3148595 := bstep (se 1 (by rfl) ⟨2361446, by rfl⟩ : syracuseStep 3148595 = 4722893) B4722893
theorem B40323905 : Blo 1397518 40323905 := bstep (se 2 (by rfl) ⟨15121464, by rfl⟩ : syracuseStep 40323905 = 30242929) B30242929
theorem B3148631 : Blo 1397518 3148631 := bstep (se 1 (by rfl) ⟨2361473, by rfl⟩ : syracuseStep 3148631 = 4722947) B4722947
theorem B23890787 : Blo 1397518 23890787 := bstep (se 1 (by rfl) ⟨17918090, by rfl⟩ : syracuseStep 23890787 = 35836181) B35836181
theorem B5975005 : Blo 1397518 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B3148811 : Blo 1397518 3148811 := bstep (se 1 (by rfl) ⟨2361608, by rfl⟩ : syracuseStep 3148811 = 4723217) B4723217
theorem B21531665 : Blo 1397518 21531665 := bstep (se 2 (by rfl) ⟨8074374, by rfl⟩ : syracuseStep 21531665 = 16148749) B16148749
theorem B3542039 : Blo 1397518 3542039 := bstep (se 1 (by rfl) ⟨2656529, by rfl⟩ : syracuseStep 3542039 = 5313059) B5313059
theorem B4852759 : Blo 1397518 4852759 := bstep (se 1 (by rfl) ⟨3639569, by rfl⟩ : syracuseStep 4852759 = 7279139) B7279139
theorem B11955235 : Blo 1397518 11955235 := bstep (se 1 (by rfl) ⟨8966426, by rfl⟩ : syracuseStep 11955235 = 17932853) B17932853
theorem B3148865 : Blo 1397518 3148865 := bstep (se 2 (by rfl) ⟨1180824, by rfl⟩ : syracuseStep 3148865 = 2361649) B2361649
theorem B4721867 : Blo 1397518 4721867 := bstep (se 1 (by rfl) ⟨3541400, by rfl⟩ : syracuseStep 4721867 = 7082801) B7082801
theorem B1494379 : Blo 1397518 1494379 := bstep (se 1 (by rfl) ⟨1120784, by rfl⟩ : syracuseStep 1494379 = 2241569) B2241569
theorem B10087811 : Blo 1397518 10087811 := bstep (se 1 (by rfl) ⟨7565858, by rfl⟩ : syracuseStep 10087811 = 15131717) B15131717
theorem B5311889 : Blo 1397518 5311889 := bstep (se 2 (by rfl) ⟨1991958, by rfl⟩ : syracuseStep 5311889 = 3983917) B3983917
theorem B12758477 : Blo 1397518 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B17010137 : Blo 1397518 17010137 := bstep (se 2 (by rfl) ⟨6378801, by rfl⟩ : syracuseStep 17010137 = 12757603) B12757603
theorem B4722137 : Blo 1397518 4722137 := bstep (se 2 (by rfl) ⟨1770801, by rfl⟩ : syracuseStep 4722137 = 3541603) B3541603
theorem B11333155 : Blo 1397518 11333155 := bstep (se 1 (by rfl) ⟨8499866, by rfl⟩ : syracuseStep 11333155 = 16999733) B16999733
theorem B5975603 : Blo 1397518 5975603 := bstep (se 1 (by rfl) ⟨4481702, by rfl⟩ : syracuseStep 5975603 = 8963405) B8963405
theorem B2985665 : Blo 1397518 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B2985751 : Blo 1397518 2985751 := bstep (se 1 (by rfl) ⟨2239313, by rfl⟩ : syracuseStep 2985751 = 4478627) B4478627
theorem B11333411 : Blo 1397518 11333411 := bstep (se 1 (by rfl) ⟨8500058, by rfl⟩ : syracuseStep 11333411 = 17000117) B17000117
theorem B6721325 : Blo 1397518 6721325 := bstep (se 3 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 6721325 = 2520497) B2520497
theorem B15937397 : Blo 1397518 15937397 := bstep (se 5 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 15937397 = 1494131) B1494131
theorem B10612781 : Blo 1397518 10612781 := bstep (se 3 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 10612781 = 3979793) B3979793
theorem B5312587 : Blo 1397518 5312587 := bstep (se 1 (by rfl) ⟨3984440, by rfl⟩ : syracuseStep 5312587 = 7968881) B7968881
theorem B3829853 : Blo 1397518 3829853 := bstep (se 3 (by rfl) ⟨718097, by rfl⟩ : syracuseStep 3829853 = 1436195) B1436195
theorem B15126659 : Blo 1397518 15126659 := bstep (se 1 (by rfl) ⟨11344994, by rfl⟩ : syracuseStep 15126659 = 22689989) B22689989
theorem B25874563 : Blo 1397518 25874563 := bstep (se 1 (by rfl) ⟨19405922, by rfl⟩ : syracuseStep 25874563 = 38811845) B38811845
theorem B4722839 : Blo 1397518 4722839 := bstep (se 1 (by rfl) ⟨3542129, by rfl⟩ : syracuseStep 4722839 = 7084259) B7084259
theorem B6467885 : Blo 1397518 6467885 := bstep (se 3 (by rfl) ⟨1212728, by rfl⟩ : syracuseStep 6467885 = 2425457) B2425457
theorem B7082315 : Blo 1397518 7082315 := bstep (se 1 (by rfl) ⟨5311736, by rfl⟩ : syracuseStep 7082315 = 10623473) B10623473
theorem B5312861 : Blo 1397518 5312861 := bstep (se 3 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 5312861 = 1992323) B1992323
theorem B2691443 : Blo 1397518 2691443 := bstep (se 1 (by rfl) ⟨2018582, by rfl⟩ : syracuseStep 2691443 = 4037165) B4037165
theorem B2986571 : Blo 1397518 2986571 := bstep (se 1 (by rfl) ⟨2239928, by rfl⟩ : syracuseStep 2986571 = 4479857) B4479857
theorem B5378653 : Blo 1397518 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B11342429 : Blo 1397518 11342429 := bstep (se 3 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 11342429 = 4253411) B4253411
theorem B51049091 : Blo 1397518 51049091 := bstep (se 1 (by rfl) ⟨38286818, by rfl⟩ : syracuseStep 51049091 = 76573637) B76573637
theorem B1397527 : Blo 1397518 1397527 := bstep (se 1 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 1397527 = 2096291) B2096291
theorem B1397547 : Blo 1397518 1397547 := bstep (se 1 (by rfl) ⟨1048160, by rfl⟩ : syracuseStep 1397547 = 2096321) B2096321
theorem B1397559 : Blo 1397518 1397559 := bstep (se 1 (by rfl) ⟨1048169, by rfl⟩ : syracuseStep 1397559 = 2096339) B2096339
theorem B1397579 : Blo 1397518 1397579 := bstep (se 1 (by rfl) ⟨1048184, by rfl⟩ : syracuseStep 1397579 = 2096369) B2096369
theorem B1397591 : Blo 1397518 1397591 := bstep (se 1 (by rfl) ⟨1048193, by rfl⟩ : syracuseStep 1397591 = 2096387) B2096387
theorem B1397611 : Blo 1397518 1397611 := bstep (se 1 (by rfl) ⟨1048208, by rfl⟩ : syracuseStep 1397611 = 2096417) B2096417
theorem B1397623 : Blo 1397518 1397623 := bstep (se 1 (by rfl) ⟨1048217, by rfl⟩ : syracuseStep 1397623 = 2096435) B2096435
theorem B1397643 : Blo 1397518 1397643 := bstep (se 1 (by rfl) ⟨1048232, by rfl⟩ : syracuseStep 1397643 = 2096465) B2096465
theorem B1397655 : Blo 1397518 1397655 := bstep (se 1 (by rfl) ⟨1048241, by rfl⟩ : syracuseStep 1397655 = 2096483) B2096483
theorem B1397675 : Blo 1397518 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B1397687 : Blo 1397518 1397687 := bstep (se 1 (by rfl) ⟨1048265, by rfl⟩ : syracuseStep 1397687 = 2096531) B2096531
theorem B1397707 : Blo 1397518 1397707 := bstep (se 1 (by rfl) ⟨1048280, by rfl⟩ : syracuseStep 1397707 = 2096561) B2096561
theorem B1397719 : Blo 1397518 1397719 := bstep (se 1 (by rfl) ⟨1048289, by rfl⟩ : syracuseStep 1397719 = 2096579) B2096579
theorem B1397739 : Blo 1397518 1397739 := bstep (se 1 (by rfl) ⟨1048304, by rfl⟩ : syracuseStep 1397739 = 2096609) B2096609
theorem B1397751 : Blo 1397518 1397751 := bstep (se 1 (by rfl) ⟨1048313, by rfl⟩ : syracuseStep 1397751 = 2096627) B2096627
theorem B1397771 : Blo 1397518 1397771 := bstep (se 1 (by rfl) ⟨1048328, by rfl⟩ : syracuseStep 1397771 = 2096657) B2096657
theorem B1397783 : Blo 1397518 1397783 := bstep (se 1 (by rfl) ⟨1048337, by rfl⟩ : syracuseStep 1397783 = 2096675) B2096675
theorem B5313559 : Blo 1397518 5313559 := bstep (se 1 (by rfl) ⟨3985169, by rfl⟩ : syracuseStep 5313559 = 7970339) B7970339
theorem B1397803 : Blo 1397518 1397803 := bstep (se 1 (by rfl) ⟨1048352, by rfl⟩ : syracuseStep 1397803 = 2096705) B2096705
theorem B1397815 : Blo 1397518 1397815 := bstep (se 1 (by rfl) ⟨1048361, by rfl⟩ : syracuseStep 1397815 = 2096723) B2096723
theorem B1397835 : Blo 1397518 1397835 := bstep (se 1 (by rfl) ⟨1048376, by rfl⟩ : syracuseStep 1397835 = 2096753) B2096753
theorem B1397847 : Blo 1397518 1397847 := bstep (se 1 (by rfl) ⟨1048385, by rfl⟩ : syracuseStep 1397847 = 2096771) B2096771
theorem B1397867 : Blo 1397518 1397867 := bstep (se 1 (by rfl) ⟨1048400, by rfl⟩ : syracuseStep 1397867 = 2096801) B2096801
theorem B1397879 : Blo 1397518 1397879 := bstep (se 1 (by rfl) ⟨1048409, by rfl⟩ : syracuseStep 1397879 = 2096819) B2096819
theorem B1397899 : Blo 1397518 1397899 := bstep (se 1 (by rfl) ⟨1048424, by rfl⟩ : syracuseStep 1397899 = 2096849) B2096849
theorem B1397911 : Blo 1397518 1397911 := bstep (se 1 (by rfl) ⟨1048433, by rfl⟩ : syracuseStep 1397911 = 2096867) B2096867
theorem B1397931 : Blo 1397518 1397931 := bstep (se 1 (by rfl) ⟨1048448, by rfl⟩ : syracuseStep 1397931 = 2096897) B2096897
theorem B1397943 : Blo 1397518 1397943 := bstep (se 1 (by rfl) ⟨1048457, by rfl⟩ : syracuseStep 1397943 = 2096915) B2096915
theorem B1397963 : Blo 1397518 1397963 := bstep (se 1 (by rfl) ⟨1048472, by rfl⟩ : syracuseStep 1397963 = 2096945) B2096945
theorem B1397975 : Blo 1397518 1397975 := bstep (se 1 (by rfl) ⟨1048481, by rfl⟩ : syracuseStep 1397975 = 2096963) B2096963
theorem B1397995 : Blo 1397518 1397995 := bstep (se 1 (by rfl) ⟨1048496, by rfl⟩ : syracuseStep 1397995 = 2096993) B2096993
theorem B1398007 : Blo 1397518 1398007 := bstep (se 1 (by rfl) ⟨1048505, by rfl⟩ : syracuseStep 1398007 = 2097011) B2097011
theorem B1398027 : Blo 1397518 1398027 := bstep (se 1 (by rfl) ⟨1048520, by rfl⟩ : syracuseStep 1398027 = 2097041) B2097041
theorem B1398039 : Blo 1397518 1398039 := bstep (se 1 (by rfl) ⟨1048529, by rfl⟩ : syracuseStep 1398039 = 2097059) B2097059
theorem B1398059 : Blo 1397518 1398059 := bstep (se 1 (by rfl) ⟨1048544, by rfl⟩ : syracuseStep 1398059 = 2097089) B2097089
theorem B9573677 : Blo 1397518 9573677 := bstep (se 3 (by rfl) ⟨1795064, by rfl⟩ : syracuseStep 9573677 = 3590129) B3590129
theorem B1398071 : Blo 1397518 1398071 := bstep (se 1 (by rfl) ⟨1048553, by rfl⟩ : syracuseStep 1398071 = 2097107) B2097107
theorem B1398091 : Blo 1397518 1398091 := bstep (se 1 (by rfl) ⟨1048568, by rfl⟩ : syracuseStep 1398091 = 2097137) B2097137
theorem B1398103 : Blo 1397518 1398103 := bstep (se 1 (by rfl) ⟨1048577, by rfl⟩ : syracuseStep 1398103 = 2097155) B2097155
theorem B1398123 : Blo 1397518 1398123 := bstep (se 1 (by rfl) ⟨1048592, by rfl⟩ : syracuseStep 1398123 = 2097185) B2097185
theorem B1398135 : Blo 1397518 1398135 := bstep (se 1 (by rfl) ⟨1048601, by rfl⟩ : syracuseStep 1398135 = 2097203) B2097203
theorem B7968131 : Blo 1397518 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1398155 : Blo 1397518 1398155 := bstep (se 1 (by rfl) ⟨1048616, by rfl⟩ : syracuseStep 1398155 = 2097233) B2097233
theorem B1398167 : Blo 1397518 1398167 := bstep (se 1 (by rfl) ⟨1048625, by rfl⟩ : syracuseStep 1398167 = 2097251) B2097251
theorem B1398187 : Blo 1397518 1398187 := bstep (se 1 (by rfl) ⟨1048640, by rfl⟩ : syracuseStep 1398187 = 2097281) B2097281
theorem B1398199 : Blo 1397518 1398199 := bstep (se 1 (by rfl) ⟨1048649, by rfl⟩ : syracuseStep 1398199 = 2097299) B2097299
theorem B1398219 : Blo 1397518 1398219 := bstep (se 1 (by rfl) ⟨1048664, by rfl⟩ : syracuseStep 1398219 = 2097329) B2097329
theorem B1398231 : Blo 1397518 1398231 := bstep (se 1 (by rfl) ⟨1048673, by rfl⟩ : syracuseStep 1398231 = 2097347) B2097347
theorem B1398251 : Blo 1397518 1398251 := bstep (se 1 (by rfl) ⟨1048688, by rfl⟩ : syracuseStep 1398251 = 2097377) B2097377
theorem B1398263 : Blo 1397518 1398263 := bstep (se 1 (by rfl) ⟨1048697, by rfl⟩ : syracuseStep 1398263 = 2097395) B2097395
theorem B1398283 : Blo 1397518 1398283 := bstep (se 1 (by rfl) ⟨1048712, by rfl⟩ : syracuseStep 1398283 = 2097425) B2097425
theorem B1398295 : Blo 1397518 1398295 := bstep (se 1 (by rfl) ⟨1048721, by rfl⟩ : syracuseStep 1398295 = 2097443) B2097443
theorem B2987545 : Blo 1397518 2987545 := bstep (se 2 (by rfl) ⟨1120329, by rfl⟩ : syracuseStep 2987545 = 2240659) B2240659
theorem B1398315 : Blo 1397518 1398315 := bstep (se 1 (by rfl) ⟨1048736, by rfl⟩ : syracuseStep 1398315 = 2097473) B2097473
theorem B1398327 : Blo 1397518 1398327 := bstep (se 1 (by rfl) ⟨1048745, by rfl⟩ : syracuseStep 1398327 = 2097491) B2097491
theorem B1398347 : Blo 1397518 1398347 := bstep (se 1 (by rfl) ⟨1048760, by rfl⟩ : syracuseStep 1398347 = 2097521) B2097521
theorem B1398359 : Blo 1397518 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B1398379 : Blo 1397518 1398379 := bstep (se 1 (by rfl) ⟨1048784, by rfl⟩ : syracuseStep 1398379 = 2097569) B2097569
theorem B1398391 : Blo 1397518 1398391 := bstep (se 1 (by rfl) ⟨1048793, by rfl⟩ : syracuseStep 1398391 = 2097587) B2097587
theorem B1398411 : Blo 1397518 1398411 := bstep (se 1 (by rfl) ⟨1048808, by rfl⟩ : syracuseStep 1398411 = 2097617) B2097617
theorem B1398423 : Blo 1397518 1398423 := bstep (se 1 (by rfl) ⟨1048817, by rfl⟩ : syracuseStep 1398423 = 2097635) B2097635
theorem B1398443 : Blo 1397518 1398443 := bstep (se 1 (by rfl) ⟨1048832, by rfl⟩ : syracuseStep 1398443 = 2097665) B2097665
theorem B3782323 : Blo 1397518 3782323 := bstep (se 1 (by rfl) ⟨2836742, by rfl⟩ : syracuseStep 3782323 = 5673485) B5673485
theorem B1398455 : Blo 1397518 1398455 := bstep (se 1 (by rfl) ⟨1048841, by rfl⟩ : syracuseStep 1398455 = 2097683) B2097683
theorem B1398475 : Blo 1397518 1398475 := bstep (se 1 (by rfl) ⟨1048856, by rfl⟩ : syracuseStep 1398475 = 2097713) B2097713
theorem B1398487 : Blo 1397518 1398487 := bstep (se 1 (by rfl) ⟨1048865, by rfl⟩ : syracuseStep 1398487 = 2097731) B2097731
theorem B1398507 : Blo 1397518 1398507 := bstep (se 1 (by rfl) ⟨1048880, by rfl⟩ : syracuseStep 1398507 = 2097761) B2097761
theorem B1398519 : Blo 1397518 1398519 := bstep (se 1 (by rfl) ⟨1048889, by rfl⟩ : syracuseStep 1398519 = 2097779) B2097779
theorem B1398539 : Blo 1397518 1398539 := bstep (se 1 (by rfl) ⟨1048904, by rfl⟩ : syracuseStep 1398539 = 2097809) B2097809
theorem B1398551 : Blo 1397518 1398551 := bstep (se 1 (by rfl) ⟨1048913, by rfl⟩ : syracuseStep 1398551 = 2097827) B2097827
theorem B2520857 : Blo 1397518 2520857 := bstep (se 2 (by rfl) ⟨945321, by rfl⟩ : syracuseStep 2520857 = 1890643) B1890643
theorem B1398571 : Blo 1397518 1398571 := bstep (se 1 (by rfl) ⟨1048928, by rfl⟩ : syracuseStep 1398571 = 2097857) B2097857
theorem B1398583 : Blo 1397518 1398583 := bstep (se 1 (by rfl) ⟨1048937, by rfl⟩ : syracuseStep 1398583 = 2097875) B2097875
theorem B1398603 : Blo 1397518 1398603 := bstep (se 1 (by rfl) ⟨1048952, by rfl⟩ : syracuseStep 1398603 = 2097905) B2097905
theorem B2045783 : Blo 1397518 2045783 := bstep (se 1 (by rfl) ⟨1534337, by rfl⟩ : syracuseStep 2045783 = 3068675) B3068675
theorem B1398615 : Blo 1397518 1398615 := bstep (se 1 (by rfl) ⟨1048961, by rfl⟩ : syracuseStep 1398615 = 2097923) B2097923
theorem B1398635 : Blo 1397518 1398635 := bstep (se 1 (by rfl) ⟨1048976, by rfl⟩ : syracuseStep 1398635 = 2097953) B2097953
theorem B1398647 : Blo 1397518 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1398667 : Blo 1397518 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B1398679 : Blo 1397518 1398679 := bstep (se 1 (by rfl) ⟨1049009, by rfl⟩ : syracuseStep 1398679 = 2098019) B2098019
theorem B1398699 : Blo 1397518 1398699 := bstep (se 1 (by rfl) ⟨1049024, by rfl⟩ : syracuseStep 1398699 = 2098049) B2098049
theorem B1398711 : Blo 1397518 1398711 := bstep (se 1 (by rfl) ⟨1049033, by rfl⟩ : syracuseStep 1398711 = 2098067) B2098067
theorem B1398731 : Blo 1397518 1398731 := bstep (se 1 (by rfl) ⟨1049048, by rfl⟩ : syracuseStep 1398731 = 2098097) B2098097
theorem B1398743 : Blo 1397518 1398743 := bstep (se 1 (by rfl) ⟨1049057, by rfl⟩ : syracuseStep 1398743 = 2098115) B2098115
theorem B1398763 : Blo 1397518 1398763 := bstep (se 1 (by rfl) ⟨1049072, by rfl⟩ : syracuseStep 1398763 = 2098145) B2098145
theorem B1398775 : Blo 1397518 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B1398795 : Blo 1397518 1398795 := bstep (se 1 (by rfl) ⟨1049096, by rfl⟩ : syracuseStep 1398795 = 2098193) B2098193
theorem B1398807 : Blo 1397518 1398807 := bstep (se 1 (by rfl) ⟨1049105, by rfl⟩ : syracuseStep 1398807 = 2098211) B2098211
theorem B1398827 : Blo 1397518 1398827 := bstep (se 1 (by rfl) ⟨1049120, by rfl⟩ : syracuseStep 1398827 = 2098241) B2098241
theorem B1398839 : Blo 1397518 1398839 := bstep (se 1 (by rfl) ⟨1049129, by rfl⟩ : syracuseStep 1398839 = 2098259) B2098259
theorem B7084097 : Blo 1397518 7084097 := bstep (se 2 (by rfl) ⟨2656536, by rfl⟩ : syracuseStep 7084097 = 5313073) B5313073
theorem B1398859 : Blo 1397518 1398859 := bstep (se 1 (by rfl) ⟨1049144, by rfl⟩ : syracuseStep 1398859 = 2098289) B2098289
theorem B1595467 : Blo 1397518 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1398871 : Blo 1397518 1398871 := bstep (se 1 (by rfl) ⟨1049153, by rfl⟩ : syracuseStep 1398871 = 2098307) B2098307
theorem B1398891 : Blo 1397518 1398891 := bstep (se 1 (by rfl) ⟨1049168, by rfl⟩ : syracuseStep 1398891 = 2098337) B2098337
theorem B1398903 : Blo 1397518 1398903 := bstep (se 1 (by rfl) ⟨1049177, by rfl⟩ : syracuseStep 1398903 = 2098355) B2098355
theorem B1398923 : Blo 1397518 1398923 := bstep (se 1 (by rfl) ⟨1049192, by rfl⟩ : syracuseStep 1398923 = 2098385) B2098385
theorem B1398935 : Blo 1397518 1398935 := bstep (se 1 (by rfl) ⟨1049201, by rfl⟩ : syracuseStep 1398935 = 2098403) B2098403
theorem B1398955 : Blo 1397518 1398955 := bstep (se 1 (by rfl) ⟨1049216, by rfl⟩ : syracuseStep 1398955 = 2098433) B2098433
theorem B1398967 : Blo 1397518 1398967 := bstep (se 1 (by rfl) ⟨1049225, by rfl⟩ : syracuseStep 1398967 = 2098451) B2098451
theorem B4716737 : Blo 1397518 4716737 := bstep (se 2 (by rfl) ⟨1768776, by rfl⟩ : syracuseStep 4716737 = 3537553) B3537553
theorem B1398987 : Blo 1397518 1398987 := bstep (se 1 (by rfl) ⟨1049240, by rfl⟩ : syracuseStep 1398987 = 2098481) B2098481
theorem B1398999 : Blo 1397518 1398999 := bstep (se 1 (by rfl) ⟨1049249, by rfl⟩ : syracuseStep 1398999 = 2098499) B2098499
theorem B1399019 : Blo 1397518 1399019 := bstep (se 1 (by rfl) ⟨1049264, by rfl⟩ : syracuseStep 1399019 = 2098529) B2098529
theorem B1399031 : Blo 1397518 1399031 := bstep (se 1 (by rfl) ⟨1049273, by rfl⟩ : syracuseStep 1399031 = 2098547) B2098547
theorem B1399051 : Blo 1397518 1399051 := bstep (se 1 (by rfl) ⟨1049288, by rfl⟩ : syracuseStep 1399051 = 2098577) B2098577
theorem B1399063 : Blo 1397518 1399063 := bstep (se 1 (by rfl) ⟨1049297, by rfl⟩ : syracuseStep 1399063 = 2098595) B2098595
theorem B1399083 : Blo 1397518 1399083 := bstep (se 1 (by rfl) ⟨1049312, by rfl⟩ : syracuseStep 1399083 = 2098625) B2098625
theorem B1399095 : Blo 1397518 1399095 := bstep (se 1 (by rfl) ⟨1049321, by rfl⟩ : syracuseStep 1399095 = 2098643) B2098643
theorem B1399115 : Blo 1397518 1399115 := bstep (se 1 (by rfl) ⟨1049336, by rfl⟩ : syracuseStep 1399115 = 2098673) B2098673
theorem B1399127 : Blo 1397518 1399127 := bstep (se 1 (by rfl) ⟨1049345, by rfl⟩ : syracuseStep 1399127 = 2098691) B2098691
theorem B1399147 : Blo 1397518 1399147 := bstep (se 1 (by rfl) ⟨1049360, by rfl⟩ : syracuseStep 1399147 = 2098721) B2098721
theorem B1399159 : Blo 1397518 1399159 := bstep (se 1 (by rfl) ⟨1049369, by rfl⟩ : syracuseStep 1399159 = 2098739) B2098739
theorem B5306755 : Blo 1397518 5306755 := bstep (se 1 (by rfl) ⟨3980066, by rfl⟩ : syracuseStep 5306755 = 7960133) B7960133
theorem B1399179 : Blo 1397518 1399179 := bstep (se 1 (by rfl) ⟨1049384, by rfl⟩ : syracuseStep 1399179 = 2098769) B2098769
theorem B1399191 : Blo 1397518 1399191 := bstep (se 1 (by rfl) ⟨1049393, by rfl⟩ : syracuseStep 1399191 = 2098787) B2098787
theorem B1399211 : Blo 1397518 1399211 := bstep (se 1 (by rfl) ⟨1049408, by rfl⟩ : syracuseStep 1399211 = 2098817) B2098817
theorem B1399223 : Blo 1397518 1399223 := bstep (se 1 (by rfl) ⟨1049417, by rfl⟩ : syracuseStep 1399223 = 2098835) B2098835
theorem B1399243 : Blo 1397518 1399243 := bstep (se 1 (by rfl) ⟨1049432, by rfl⟩ : syracuseStep 1399243 = 2098865) B2098865
theorem B1399255 : Blo 1397518 1399255 := bstep (se 1 (by rfl) ⟨1049441, by rfl⟩ : syracuseStep 1399255 = 2098883) B2098883
theorem B1399275 : Blo 1397518 1399275 := bstep (se 1 (by rfl) ⟨1049456, by rfl⟩ : syracuseStep 1399275 = 2098913) B2098913
theorem B1399287 : Blo 1397518 1399287 := bstep (se 1 (by rfl) ⟨1049465, by rfl⟩ : syracuseStep 1399287 = 2098931) B2098931
theorem B1399307 : Blo 1397518 1399307 := bstep (se 1 (by rfl) ⟨1049480, by rfl⟩ : syracuseStep 1399307 = 2098961) B2098961
theorem B1399319 : Blo 1397518 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B1399339 : Blo 1397518 1399339 := bstep (se 1 (by rfl) ⟨1049504, by rfl⟩ : syracuseStep 1399339 = 2099009) B2099009
theorem B1399351 : Blo 1397518 1399351 := bstep (se 1 (by rfl) ⟨1049513, by rfl⟩ : syracuseStep 1399351 = 2099027) B2099027
theorem B1399371 : Blo 1397518 1399371 := bstep (se 1 (by rfl) ⟨1049528, by rfl⟩ : syracuseStep 1399371 = 2099057) B2099057
theorem B1399383 : Blo 1397518 1399383 := bstep (se 1 (by rfl) ⟨1049537, by rfl⟩ : syracuseStep 1399383 = 2099075) B2099075
theorem B1399403 : Blo 1397518 1399403 := bstep (se 1 (by rfl) ⟨1049552, by rfl⟩ : syracuseStep 1399403 = 2099105) B2099105
theorem B1399415 : Blo 1397518 1399415 := bstep (se 1 (by rfl) ⟨1049561, by rfl⟩ : syracuseStep 1399415 = 2099123) B2099123
theorem B7076483 : Blo 1397518 7076483 := bstep (se 1 (by rfl) ⟨5307362, by rfl⟩ : syracuseStep 7076483 = 10614725) B10614725
theorem B14006915 : Blo 1397518 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B1399435 : Blo 1397518 1399435 := bstep (se 1 (by rfl) ⟨1049576, by rfl⟩ : syracuseStep 1399435 = 2099153) B2099153
theorem B10074775 : Blo 1397518 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B1399447 : Blo 1397518 1399447 := bstep (se 1 (by rfl) ⟨1049585, by rfl⟩ : syracuseStep 1399447 = 2099171) B2099171
theorem B1399467 : Blo 1397518 1399467 := bstep (se 1 (by rfl) ⟨1049600, by rfl⟩ : syracuseStep 1399467 = 2099201) B2099201
theorem B5307059 : Blo 1397518 5307059 := bstep (se 1 (by rfl) ⟨3980294, by rfl⟩ : syracuseStep 5307059 = 7960589) B7960589
theorem B1399479 : Blo 1397518 1399479 := bstep (se 1 (by rfl) ⟨1049609, by rfl⟩ : syracuseStep 1399479 = 2099219) B2099219
theorem B1399499 : Blo 1397518 1399499 := bstep (se 1 (by rfl) ⟨1049624, by rfl⟩ : syracuseStep 1399499 = 2099249) B2099249
theorem B1399511 : Blo 1397518 1399511 := bstep (se 1 (by rfl) ⟨1049633, by rfl⟩ : syracuseStep 1399511 = 2099267) B2099267
theorem B4717277 : Blo 1397518 4717277 := bstep (se 3 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 4717277 = 1768979) B1768979
theorem B3144473 : Blo 1397518 3144473 := bstep (se 2 (by rfl) ⟨1179177, by rfl⟩ : syracuseStep 3144473 = 2358355) B2358355
theorem B3537715 : Blo 1397518 3537715 := bstep (se 1 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 3537715 = 5306573) B5306573
theorem B3144563 : Blo 1397518 3144563 := bstep (se 1 (by rfl) ⟨2358422, by rfl⟩ : syracuseStep 3144563 = 4716845) B4716845
theorem B15129461 : Blo 1397518 15129461 := bstep (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) B1418387
theorem B3144599 : Blo 1397518 3144599 := bstep (se 1 (by rfl) ⟨2358449, by rfl⟩ : syracuseStep 3144599 = 4716899) B4716899
theorem B3537857 : Blo 1397518 3537857 := bstep (se 2 (by rfl) ⟨1326696, by rfl⟩ : syracuseStep 3537857 = 2653393) B2653393
theorem B3980249 : Blo 1397518 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B5970905 : Blo 1397518 5970905 := bstep (se 2 (by rfl) ⟨2239089, by rfl⟩ : syracuseStep 5970905 = 4478179) B4478179
theorem B4037597 : Blo 1397518 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B5970989 : Blo 1397518 5970989 := bstep (se 3 (by rfl) ⟨1119560, by rfl⟩ : syracuseStep 5970989 = 2239121) B2239121
theorem B2653249 : Blo 1397518 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B3144779 : Blo 1397518 3144779 := bstep (se 1 (by rfl) ⟨2358584, by rfl⟩ : syracuseStep 3144779 = 4717169) B4717169
theorem B3144833 : Blo 1397518 3144833 := bstep (se 2 (by rfl) ⟨1179312, by rfl⟩ : syracuseStep 3144833 = 2358625) B2358625
theorem B7560323 : Blo 1397518 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B2096279 : Blo 1397518 2096279 := bstep (se 1 (by rfl) ⟨1572209, by rfl⟩ : syracuseStep 2096279 = 3144419) B3144419
theorem B2391191 : Blo 1397518 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B3357875 : Blo 1397518 3357875 := bstep (se 1 (by rfl) ⟨2518406, by rfl⟩ : syracuseStep 3357875 = 5036813) B5036813
theorem B2096345 : Blo 1397518 2096345 := bstep (se 2 (by rfl) ⟨786129, by rfl⟩ : syracuseStep 2096345 = 1572259) B1572259
theorem B2358551 : Blo 1397518 2358551 := bstep (se 1 (by rfl) ⟨1768913, by rfl⟩ : syracuseStep 2358551 = 3537827) B3537827
theorem B5307713 : Blo 1397518 5307713 := bstep (se 2 (by rfl) ⟨1990392, by rfl⟩ : syracuseStep 5307713 = 3980785) B3980785
theorem B2096459 : Blo 1397518 2096459 := bstep (se 1 (by rfl) ⟨1572344, by rfl⟩ : syracuseStep 2096459 = 3144689) B3144689
theorem B2096471 : Blo 1397518 2096471 := bstep (se 1 (by rfl) ⟨1572353, by rfl⟩ : syracuseStep 2096471 = 3144707) B3144707
theorem B3145049 : Blo 1397518 3145049 := bstep (se 2 (by rfl) ⟨1179393, by rfl⟩ : syracuseStep 3145049 = 2358787) B2358787
theorem B6724957 : Blo 1397518 6724957 := bstep (se 3 (by rfl) ⟨1260929, by rfl⟩ : syracuseStep 6724957 = 2521859) B2521859
theorem B103497101 : Blo 1397518 103497101 := bstep (se 3 (by rfl) ⟨19405706, by rfl⟩ : syracuseStep 103497101 = 38811413) B38811413
theorem B2358679 : Blo 1397518 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B6725015 : Blo 1397518 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B2096537 : Blo 1397518 2096537 := bstep (se 2 (by rfl) ⟨786201, by rfl⟩ : syracuseStep 2096537 = 1572403) B1572403
theorem B3145139 : Blo 1397518 3145139 := bstep (se 1 (by rfl) ⟨2358854, by rfl⟩ : syracuseStep 3145139 = 4717709) B4717709
theorem B3145175 : Blo 1397518 3145175 := bstep (se 1 (by rfl) ⟨2358881, by rfl⟩ : syracuseStep 3145175 = 4717763) B4717763
theorem B1572331 : Blo 1397518 1572331 := bstep (se 1 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 1572331 = 2358497) B2358497
theorem B2653697 : Blo 1397518 2653697 := bstep (se 2 (by rfl) ⟨995136, by rfl⟩ : syracuseStep 2653697 = 1990273) B1990273
theorem B2096651 : Blo 1397518 2096651 := bstep (se 1 (by rfl) ⟨1572488, by rfl⟩ : syracuseStep 2096651 = 3144977) B3144977
theorem B2096663 : Blo 1397518 2096663 := bstep (se 1 (by rfl) ⟨1572497, by rfl⟩ : syracuseStep 2096663 = 3144995) B3144995
theorem B2833985 : Blo 1397518 2833985 := bstep (se 2 (by rfl) ⟨1062744, by rfl⟩ : syracuseStep 2833985 = 2125489) B2125489
theorem B1769035 : Blo 1397518 1769035 := bstep (se 1 (by rfl) ⟨1326776, by rfl⟩ : syracuseStep 1769035 = 2653553) B2653553
theorem B1572439 : Blo 1397518 1572439 := bstep (se 1 (by rfl) ⟨1179329, by rfl⟩ : syracuseStep 1572439 = 2358659) B2358659
theorem B2096729 : Blo 1397518 2096729 := bstep (se 2 (by rfl) ⟨786273, by rfl⟩ : syracuseStep 2096729 = 1572547) B1572547
theorem B3145355 : Blo 1397518 3145355 := bstep (se 1 (by rfl) ⟨2359016, by rfl⟩ : syracuseStep 3145355 = 4718033) B4718033
theorem B3145409 : Blo 1397518 3145409 := bstep (se 2 (by rfl) ⟨1179528, by rfl⟩ : syracuseStep 3145409 = 2359057) B2359057
theorem B2096843 : Blo 1397518 2096843 := bstep (se 1 (by rfl) ⟨1572632, by rfl⟩ : syracuseStep 2096843 = 3145265) B3145265
theorem B2096855 : Blo 1397518 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B7970521 : Blo 1397518 7970521 := bstep (se 2 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 7970521 = 5977891) B5977891
theorem B1572619 : Blo 1397518 1572619 := bstep (se 1 (by rfl) ⟨1179464, by rfl⟩ : syracuseStep 1572619 = 2358929) B2358929
theorem B2096921 : Blo 1397518 2096921 := bstep (se 2 (by rfl) ⟨786345, by rfl⟩ : syracuseStep 2096921 = 1572691) B1572691
theorem B3358529 : Blo 1397518 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B4718411 : Blo 1397518 4718411 := bstep (se 1 (by rfl) ⟨3538808, by rfl⟩ : syracuseStep 4718411 = 7077617) B7077617
theorem B1769303 : Blo 1397518 1769303 := bstep (se 1 (by rfl) ⟨1326977, by rfl⟩ : syracuseStep 1769303 = 2653955) B2653955
theorem B2654039 : Blo 1397518 2654039 := bstep (se 1 (by rfl) ⟨1990529, by rfl⟩ : syracuseStep 2654039 = 3981059) B3981059
theorem B1990489 : Blo 1397518 1990489 := bstep (se 2 (by rfl) ⟨746433, by rfl⟩ : syracuseStep 1990489 = 1492867) B1492867
theorem B10616669 : Blo 1397518 10616669 := bstep (se 3 (by rfl) ⟨1990625, by rfl⟩ : syracuseStep 10616669 = 3981251) B3981251
theorem B1572727 : Blo 1397518 1572727 := bstep (se 1 (by rfl) ⟨1179545, by rfl⟩ : syracuseStep 1572727 = 2359091) B2359091
theorem B2097035 : Blo 1397518 2097035 := bstep (se 1 (by rfl) ⟨1572776, by rfl⟩ : syracuseStep 2097035 = 3145553) B3145553
theorem B2097047 : Blo 1397518 2097047 := bstep (se 1 (by rfl) ⟨1572785, by rfl⟩ : syracuseStep 2097047 = 3145571) B3145571
theorem B2834327 : Blo 1397518 2834327 := bstep (se 1 (by rfl) ⟨2125745, by rfl⟩ : syracuseStep 2834327 = 4251491) B4251491
theorem B3145625 : Blo 1397518 3145625 := bstep (se 2 (by rfl) ⟨1179609, by rfl⟩ : syracuseStep 3145625 = 2359219) B2359219
theorem B4038551 : Blo 1397518 4038551 := bstep (se 1 (by rfl) ⟨3028913, by rfl⟩ : syracuseStep 4038551 = 6057827) B6057827
theorem B4980659 : Blo 1397518 4980659 := bstep (se 1 (by rfl) ⟨3735494, by rfl⟩ : syracuseStep 4980659 = 7470989) B7470989
theorem B1990603 : Blo 1397518 1990603 := bstep (se 1 (by rfl) ⟨1492952, by rfl⟩ : syracuseStep 1990603 = 2985905) B2985905
theorem B2097113 : Blo 1397518 2097113 := bstep (se 2 (by rfl) ⟨786417, by rfl⟩ : syracuseStep 2097113 = 1572835) B1572835
theorem B3145715 : Blo 1397518 3145715 := bstep (se 1 (by rfl) ⟨2359286, by rfl⟩ : syracuseStep 3145715 = 4718573) B4718573
theorem B1572871 : Blo 1397518 1572871 := bstep (se 1 (by rfl) ⟨1179653, by rfl⟩ : syracuseStep 1572871 = 2359307) B2359307
theorem B2097167 : Blo 1397518 2097167 := bstep (se 1 (by rfl) ⟨1572875, by rfl⟩ : syracuseStep 2097167 = 3145751) B3145751
theorem B10354711 : Blo 1397518 10354711 := bstep (se 1 (by rfl) ⟨7766033, by rfl⟩ : syracuseStep 10354711 = 15532067) B15532067
theorem B8503319 : Blo 1397518 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B2097209 : Blo 1397518 2097209 := bstep (se 2 (by rfl) ⟨786453, by rfl⟩ : syracuseStep 2097209 = 1572907) B1572907
theorem B3145787 : Blo 1397518 3145787 := bstep (se 1 (by rfl) ⟨2359340, by rfl⟩ : syracuseStep 3145787 = 4718681) B4718681
theorem B10084439 : Blo 1397518 10084439 := bstep (se 1 (by rfl) ⟨7563329, by rfl⟩ : syracuseStep 10084439 = 15126659) B15126659
theorem B2359415 : Blo 1397518 2359415 := bstep (se 1 (by rfl) ⟨1769561, by rfl⟩ : syracuseStep 2359415 = 3539123) B3539123
theorem B2097287 : Blo 1397518 2097287 := bstep (se 1 (by rfl) ⟨1572965, by rfl⟩ : syracuseStep 2097287 = 3145931) B3145931
theorem B2097323 : Blo 1397518 2097323 := bstep (se 1 (by rfl) ⟨1572992, by rfl⟩ : syracuseStep 2097323 = 3145985) B3145985
theorem B3145913 : Blo 1397518 3145913 := bstep (se 2 (by rfl) ⟨1179717, by rfl⟩ : syracuseStep 3145913 = 2359435) B2359435
theorem B1573051 : Blo 1397518 1573051 := bstep (se 1 (by rfl) ⟨1179788, by rfl⟩ : syracuseStep 1573051 = 2359577) B2359577
theorem B2097353 : Blo 1397518 2097353 := bstep (se 2 (by rfl) ⟨786507, by rfl⟩ : syracuseStep 2097353 = 1573015) B1573015
theorem B1794295 : Blo 1397518 1794295 := bstep (se 1 (by rfl) ⟨1345721, by rfl⟩ : syracuseStep 1794295 = 2691443) B2691443
theorem B4251905 : Blo 1397518 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B2097467 : Blo 1397518 2097467 := bstep (se 1 (by rfl) ⟨1573100, by rfl⟩ : syracuseStep 2097467 = 3146201) B3146201
theorem B3539315 : Blo 1397518 3539315 := bstep (se 1 (by rfl) ⟨2654486, by rfl⟩ : syracuseStep 3539315 = 5308973) B5308973
theorem B2097527 : Blo 1397518 2097527 := bstep (se 1 (by rfl) ⟨1573145, by rfl⟩ : syracuseStep 2097527 = 3146291) B3146291
theorem B3539335 : Blo 1397518 3539335 := bstep (se 1 (by rfl) ⟨2654501, by rfl⟩ : syracuseStep 3539335 = 5309003) B5309003
theorem B2097551 : Blo 1397518 2097551 := bstep (se 1 (by rfl) ⟨1573163, by rfl⟩ : syracuseStep 2097551 = 3146327) B3146327
theorem B7561619 : Blo 1397518 7561619 := bstep (se 1 (by rfl) ⟨5671214, by rfl⟩ : syracuseStep 7561619 = 11342429) B11342429
theorem B2097593 : Blo 1397518 2097593 := bstep (se 2 (by rfl) ⟨786597, by rfl⟩ : syracuseStep 2097593 = 1573195) B1573195
theorem B2097671 : Blo 1397518 2097671 := bstep (se 1 (by rfl) ⟨1573253, by rfl⟩ : syracuseStep 2097671 = 3146507) B3146507
theorem B3146255 : Blo 1397518 3146255 := bstep (se 1 (by rfl) ⟨2359691, by rfl⟩ : syracuseStep 3146255 = 4719383) B4719383
theorem B3146273 : Blo 1397518 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B2097707 : Blo 1397518 2097707 := bstep (se 1 (by rfl) ⟨1573280, by rfl⟩ : syracuseStep 2097707 = 3146561) B3146561
theorem B2359867 : Blo 1397518 2359867 := bstep (se 1 (by rfl) ⟨1769900, by rfl⟩ : syracuseStep 2359867 = 3539801) B3539801
theorem B2097737 : Blo 1397518 2097737 := bstep (se 2 (by rfl) ⟨786651, by rfl⟩ : syracuseStep 2097737 = 1573303) B1573303
theorem B1770103 : Blo 1397518 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B1573519 : Blo 1397518 1573519 := bstep (se 1 (by rfl) ⟨1180139, by rfl⟩ : syracuseStep 1573519 = 2360279) B2360279
theorem B3539609 : Blo 1397518 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B2097851 : Blo 1397518 2097851 := bstep (se 1 (by rfl) ⟨1573388, by rfl⟩ : syracuseStep 2097851 = 3146777) B3146777
theorem B2360009 : Blo 1397518 2360009 := bstep (se 2 (by rfl) ⟨885003, by rfl⟩ : syracuseStep 2360009 = 1770007) B1770007
theorem B2097911 : Blo 1397518 2097911 := bstep (se 1 (by rfl) ⟨1573433, by rfl⟩ : syracuseStep 2097911 = 3146867) B3146867
theorem B5309185 : Blo 1397518 5309185 := bstep (se 2 (by rfl) ⟨1990944, by rfl⟩ : syracuseStep 5309185 = 3981889) B3981889
theorem B2097935 : Blo 1397518 2097935 := bstep (se 1 (by rfl) ⟨1573451, by rfl⟩ : syracuseStep 2097935 = 3146903) B3146903
theorem B43082533 : Blo 1397518 43082533 := bstep (se 4 (by rfl) ⟨4038987, by rfl⟩ : syracuseStep 43082533 = 8077975) B8077975
theorem B2097977 : Blo 1397518 2097977 := bstep (se 2 (by rfl) ⟨786741, by rfl⟩ : syracuseStep 2097977 = 1573483) B1573483
theorem B3539771 : Blo 1397518 3539771 := bstep (se 1 (by rfl) ⟨2654828, by rfl⟩ : syracuseStep 3539771 = 5309657) B5309657
theorem B6382451 : Blo 1397518 6382451 := bstep (se 1 (by rfl) ⟨4786838, by rfl⟩ : syracuseStep 6382451 = 9573677) B9573677
theorem B3146615 : Blo 1397518 3146615 := bstep (se 1 (by rfl) ⟨2359961, by rfl⟩ : syracuseStep 3146615 = 4719923) B4719923
theorem B2098055 : Blo 1397518 2098055 := bstep (se 1 (by rfl) ⟨1573541, by rfl⟩ : syracuseStep 2098055 = 3147083) B3147083
theorem B6808465 : Blo 1397518 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B2098091 : Blo 1397518 2098091 := bstep (se 1 (by rfl) ⟨1573568, by rfl⟩ : syracuseStep 2098091 = 3147137) B3147137
theorem B4719545 : Blo 1397518 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B1770427 : Blo 1397518 1770427 := bstep (se 1 (by rfl) ⟨1327820, by rfl⟩ : syracuseStep 1770427 = 2655641) B2655641
theorem B2098121 : Blo 1397518 2098121 := bstep (se 2 (by rfl) ⟨786795, by rfl⟩ : syracuseStep 2098121 = 1573591) B1573591
theorem B3539983 : Blo 1397518 3539983 := bstep (se 1 (by rfl) ⟨2654987, by rfl⟩ : syracuseStep 3539983 = 5309975) B5309975
theorem B3146795 : Blo 1397518 3146795 := bstep (se 1 (by rfl) ⟨2360096, by rfl⟩ : syracuseStep 3146795 = 4720193) B4720193
theorem B2098235 : Blo 1397518 2098235 := bstep (se 1 (by rfl) ⟨1573676, by rfl⟩ : syracuseStep 2098235 = 3147353) B3147353
theorem B35849303 : Blo 1397518 35849303 := bstep (se 1 (by rfl) ⟨26886977, by rfl⟩ : syracuseStep 35849303 = 53773955) B53773955
theorem B2098295 : Blo 1397518 2098295 := bstep (se 1 (by rfl) ⟨1573721, by rfl⟩ : syracuseStep 2098295 = 3147443) B3147443
theorem B1574023 : Blo 1397518 1574023 := bstep (se 1 (by rfl) ⟨1180517, by rfl⟩ : syracuseStep 1574023 = 2361035) B2361035
theorem B2098319 : Blo 1397518 2098319 := bstep (se 1 (by rfl) ⟨1573739, by rfl⟩ : syracuseStep 2098319 = 3147479) B3147479
theorem B2098361 : Blo 1397518 2098361 := bstep (se 2 (by rfl) ⟨786885, by rfl⟩ : syracuseStep 2098361 = 1573771) B1573771
theorem B1680571 : Blo 1397518 1680571 := bstep (se 1 (by rfl) ⟨1260428, by rfl⟩ : syracuseStep 1680571 = 2520857) B2520857
theorem B34022605 : Blo 1397518 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B2098439 : Blo 1397518 2098439 := bstep (se 1 (by rfl) ⟨1573829, by rfl⟩ : syracuseStep 2098439 = 3147659) B3147659
theorem B3540257 : Blo 1397518 3540257 := bstep (se 2 (by rfl) ⟨1327596, by rfl⟩ : syracuseStep 3540257 = 2655193) B2655193
theorem B2098475 : Blo 1397518 2098475 := bstep (se 1 (by rfl) ⟨1573856, by rfl⟩ : syracuseStep 2098475 = 3147713) B3147713
theorem B1574203 : Blo 1397518 1574203 := bstep (se 1 (by rfl) ⟨1180652, by rfl⟩ : syracuseStep 1574203 = 2361305) B2361305
theorem B2098505 : Blo 1397518 2098505 := bstep (se 2 (by rfl) ⟨786939, by rfl⟩ : syracuseStep 2098505 = 1573879) B1573879
theorem B2360711 : Blo 1397518 2360711 := bstep (se 1 (by rfl) ⟨1770533, by rfl⟩ : syracuseStep 2360711 = 3541067) B3541067
theorem B3147155 : Blo 1397518 3147155 := bstep (se 1 (by rfl) ⟨2360366, by rfl⟩ : syracuseStep 3147155 = 4720733) B4720733
theorem B1770923 : Blo 1397518 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B2098619 : Blo 1397518 2098619 := bstep (se 1 (by rfl) ⟨1573964, by rfl⟩ : syracuseStep 2098619 = 3147929) B3147929
theorem B3147209 : Blo 1397518 3147209 := bstep (se 2 (by rfl) ⟨1180203, by rfl⟩ : syracuseStep 3147209 = 2360407) B2360407
theorem B13436381 : Blo 1397518 13436381 := bstep (se 3 (by rfl) ⟨2519321, by rfl⟩ : syracuseStep 13436381 = 5038643) B5038643
theorem B2098679 : Blo 1397518 2098679 := bstep (se 1 (by rfl) ⟨1574009, by rfl⟩ : syracuseStep 2098679 = 3148019) B3148019
theorem B4720139 : Blo 1397518 4720139 := bstep (se 1 (by rfl) ⟨3540104, by rfl⟩ : syracuseStep 4720139 = 7080209) B7080209
theorem B2098703 : Blo 1397518 2098703 := bstep (se 1 (by rfl) ⟨1574027, by rfl⟩ : syracuseStep 2098703 = 3148055) B3148055
theorem B7964189 : Blo 1397518 7964189 := bstep (se 3 (by rfl) ⟨1493285, by rfl⟩ : syracuseStep 7964189 = 2986571) B2986571
theorem B2098745 : Blo 1397518 2098745 := bstep (se 2 (by rfl) ⟨787029, by rfl⟩ : syracuseStep 2098745 = 1574059) B1574059
theorem B4720247 : Blo 1397518 4720247 := bstep (se 1 (by rfl) ⟨3540185, by rfl⟩ : syracuseStep 4720247 = 7080371) B7080371
theorem B2098823 : Blo 1397518 2098823 := bstep (se 1 (by rfl) ⟨1574117, by rfl⟩ : syracuseStep 2098823 = 3148235) B3148235
theorem B2098859 : Blo 1397518 2098859 := bstep (se 1 (by rfl) ⟨1574144, by rfl⟩ : syracuseStep 2098859 = 3148289) B3148289
theorem B2655929 : Blo 1397518 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B2098889 : Blo 1397518 2098889 := bstep (se 2 (by rfl) ⟨787083, by rfl⟩ : syracuseStep 2098889 = 1574167) B1574167
theorem B2099003 : Blo 1397518 2099003 := bstep (se 1 (by rfl) ⟨1574252, by rfl⟩ : syracuseStep 2099003 = 3148505) B3148505
theorem B3983165 : Blo 1397518 3983165 := bstep (se 3 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 3983165 = 1493687) B1493687
theorem B53127029 : Blo 1397518 53127029 := bstep (se 5 (by rfl) ⟨2490329, by rfl⟩ : syracuseStep 53127029 = 4980659) B4980659
theorem B2099063 : Blo 1397518 2099063 := bstep (se 1 (by rfl) ⟨1574297, by rfl⟩ : syracuseStep 2099063 = 3148595) B3148595
theorem B2099087 : Blo 1397518 2099087 := bstep (se 1 (by rfl) ⟨1574315, by rfl⟩ : syracuseStep 2099087 = 3148631) B3148631
theorem B7178129 : Blo 1397518 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B15927191 : Blo 1397518 15927191 := bstep (se 1 (by rfl) ⟨11945393, by rfl⟩ : syracuseStep 15927191 = 23890787) B23890787
theorem B2099129 : Blo 1397518 2099129 := bstep (se 2 (by rfl) ⟨787173, by rfl⟩ : syracuseStep 2099129 = 1574347) B1574347
theorem B2099207 : Blo 1397518 2099207 := bstep (se 1 (by rfl) ⟨1574405, by rfl⟩ : syracuseStep 2099207 = 3148811) B3148811
theorem B14354443 : Blo 1397518 14354443 := bstep (se 1 (by rfl) ⟨10765832, by rfl⟩ : syracuseStep 14354443 = 21531665) B21531665
theorem B2361359 : Blo 1397518 2361359 := bstep (se 1 (by rfl) ⟨1771019, by rfl⟩ : syracuseStep 2361359 = 3542039) B3542039
theorem B3983393 : Blo 1397518 3983393 := bstep (se 2 (by rfl) ⟨1493772, by rfl⟩ : syracuseStep 3983393 = 2987545) B2987545
theorem B2099243 : Blo 1397518 2099243 := bstep (se 1 (by rfl) ⟨1574432, by rfl⟩ : syracuseStep 2099243 = 3148865) B3148865
theorem B2099273 : Blo 1397518 2099273 := bstep (se 2 (by rfl) ⟨787227, by rfl⟩ : syracuseStep 2099273 = 1574455) B1574455
theorem B5040215 : Blo 1397518 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B2238583 : Blo 1397518 2238583 := bstep (se 1 (by rfl) ⟨1678937, by rfl⟩ : syracuseStep 2238583 = 3357875) B3357875
theorem B3147911 : Blo 1397518 3147911 := bstep (se 1 (by rfl) ⟨2360933, by rfl⟩ : syracuseStep 3147911 = 4721867) B4721867
theorem B4720841 : Blo 1397518 4720841 := bstep (se 2 (by rfl) ⟨1770315, by rfl⟩ : syracuseStep 4720841 = 3540631) B3540631
theorem B3541259 : Blo 1397518 3541259 := bstep (se 1 (by rfl) ⟨2655944, by rfl⟩ : syracuseStep 3541259 = 5311889) B5311889
theorem B4483343 : Blo 1397518 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B10627361 : Blo 1397518 10627361 := bstep (se 2 (by rfl) ⟨3985260, by rfl⟩ : syracuseStep 10627361 = 7970521) B7970521
theorem B11340091 : Blo 1397518 11340091 := bstep (se 1 (by rfl) ⟨8505068, by rfl⟩ : syracuseStep 11340091 = 17010137) B17010137
theorem B3148091 : Blo 1397518 3148091 := bstep (se 1 (by rfl) ⟨2361068, by rfl⟩ : syracuseStep 3148091 = 4722137) B4722137
theorem B3983735 : Blo 1397518 3983735 := bstep (se 1 (by rfl) ⟨2987801, by rfl⟩ : syracuseStep 3983735 = 5975603) B5975603
theorem B3148217 : Blo 1397518 3148217 := bstep (se 2 (by rfl) ⟨1180581, by rfl⟩ : syracuseStep 3148217 = 2361163) B2361163
theorem B7555607 : Blo 1397518 7555607 := bstep (se 1 (by rfl) ⟨5666705, by rfl⟩ : syracuseStep 7555607 = 11333411) B11333411
theorem B2239019 : Blo 1397518 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B10619585 : Blo 1397518 10619585 := bstep (se 2 (by rfl) ⟨3982344, by rfl⟩ : syracuseStep 10619585 = 7964689) B7964689
theorem B3148559 : Blo 1397518 3148559 := bstep (se 1 (by rfl) ⟨2361419, by rfl⟩ : syracuseStep 3148559 = 4722839) B4722839
theorem B3148577 : Blo 1397518 3148577 := bstep (se 2 (by rfl) ⟨1180716, by rfl⟩ : syracuseStep 3148577 = 2361433) B2361433
theorem B34499417 : Blo 1397518 34499417 := bstep (se 2 (by rfl) ⟨12937281, by rfl⟩ : syracuseStep 34499417 = 25874563) B25874563
theorem B4311923 : Blo 1397518 4311923 := bstep (se 1 (by rfl) ⟨3233942, by rfl⟩ : syracuseStep 4311923 = 6467885) B6467885
theorem B4721543 : Blo 1397518 4721543 := bstep (se 1 (by rfl) ⟨3541157, by rfl⟩ : syracuseStep 4721543 = 7082315) B7082315
theorem B6720401 : Blo 1397518 6720401 := bstep (se 2 (by rfl) ⟨2520150, by rfl⟩ : syracuseStep 6720401 = 5040301) B5040301
theorem B3541907 : Blo 1397518 3541907 := bstep (se 1 (by rfl) ⟨2656430, by rfl⟩ : syracuseStep 3541907 = 5312861) B5312861
theorem B7080857 : Blo 1397518 7080857 := bstep (se 2 (by rfl) ⟨2655321, by rfl⟩ : syracuseStep 7080857 = 5310643) B5310643
theorem B3779513 : Blo 1397518 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B34032727 : Blo 1397518 34032727 := bstep (se 1 (by rfl) ⟨25524545, by rfl⟩ : syracuseStep 34032727 = 51049091) B51049091
theorem B3542201 : Blo 1397518 3542201 := bstep (se 2 (by rfl) ⟨1328325, by rfl⟩ : syracuseStep 3542201 = 2656651) B2656651
theorem B4721921 : Blo 1397518 4721921 := bstep (se 2 (by rfl) ⟨1770720, by rfl⟩ : syracuseStep 4721921 = 3541441) B3541441
theorem B5975329 : Blo 1397518 5975329 := bstep (se 2 (by rfl) ⟨2240748, by rfl⟩ : syracuseStep 5975329 = 4481497) B4481497
theorem B248491405 : Blo 1397518 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B8957405 : Blo 1397518 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B5312087 : Blo 1397518 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B7966673 : Blo 1397518 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B4722731 : Blo 1397518 4722731 := bstep (se 1 (by rfl) ⟨3542048, by rfl⟩ : syracuseStep 4722731 = 7084097) B7084097
theorem B5312573 : Blo 1397518 5312573 := bstep (se 3 (by rfl) ⟨996107, by rfl⟩ : syracuseStep 5312573 = 1992215) B1992215
theorem B7557293 : Blo 1397518 7557293 := bstep (se 3 (by rfl) ⟨1416992, by rfl⟩ : syracuseStep 7557293 = 2833985) B2833985
theorem B8966609 : Blo 1397518 8966609 := bstep (se 2 (by rfl) ⟨3362478, by rfl⟩ : syracuseStep 8966609 = 6724957) B6724957
theorem B26882603 : Blo 1397518 26882603 := bstep (se 1 (by rfl) ⟨20161952, by rfl⟩ : syracuseStep 26882603 = 40323905) B40323905
theorem B15118913 : Blo 1397518 15118913 := bstep (se 2 (by rfl) ⟨5669592, by rfl⟩ : syracuseStep 15118913 = 11339185) B11339185
theorem B2691731 : Blo 1397518 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B15110873 : Blo 1397518 15110873 := bstep (se 2 (by rfl) ⟨5666577, by rfl⟩ : syracuseStep 15110873 = 11333155) B11333155
theorem B1397519 : Blo 1397518 1397519 := bstep (se 1 (by rfl) ⟨1048139, by rfl⟩ : syracuseStep 1397519 = 2096279) B2096279
theorem B1594127 : Blo 1397518 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B1397563 : Blo 1397518 1397563 := bstep (se 1 (by rfl) ⟨1048172, by rfl⟩ : syracuseStep 1397563 = 2096345) B2096345
theorem B1397639 : Blo 1397518 1397639 := bstep (se 1 (by rfl) ⟨1048229, by rfl⟩ : syracuseStep 1397639 = 2096459) B2096459
theorem B1397647 : Blo 1397518 1397647 := bstep (se 1 (by rfl) ⟨1048235, by rfl⟩ : syracuseStep 1397647 = 2096471) B2096471
theorem B5043097 : Blo 1397518 5043097 := bstep (se 2 (by rfl) ⟨1891161, by rfl⟩ : syracuseStep 5043097 = 3782323) B3782323
theorem B68998067 : Blo 1397518 68998067 := bstep (se 1 (by rfl) ⟨51748550, by rfl⟩ : syracuseStep 68998067 = 103497101) B103497101
theorem B1397691 : Blo 1397518 1397691 := bstep (se 1 (by rfl) ⟨1048268, by rfl⟩ : syracuseStep 1397691 = 2096537) B2096537
theorem B1397767 : Blo 1397518 1397767 := bstep (se 1 (by rfl) ⟨1048325, by rfl⟩ : syracuseStep 1397767 = 2096651) B2096651
theorem B1397775 : Blo 1397518 1397775 := bstep (se 1 (by rfl) ⟨1048331, by rfl⟩ : syracuseStep 1397775 = 2096663) B2096663
theorem B1397819 : Blo 1397518 1397819 := bstep (se 1 (by rfl) ⟨1048364, by rfl⟩ : syracuseStep 1397819 = 2096729) B2096729
theorem B1397895 : Blo 1397518 1397895 := bstep (se 1 (by rfl) ⟨1048421, by rfl⟩ : syracuseStep 1397895 = 2096843) B2096843
theorem B1397903 : Blo 1397518 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B1397947 : Blo 1397518 1397947 := bstep (se 1 (by rfl) ⟨1048460, by rfl⟩ : syracuseStep 1397947 = 2096921) B2096921
theorem B1398023 : Blo 1397518 1398023 := bstep (se 1 (by rfl) ⟨1048517, by rfl⟩ : syracuseStep 1398023 = 2097035) B2097035
theorem B1398031 : Blo 1397518 1398031 := bstep (se 1 (by rfl) ⟨1048523, by rfl⟩ : syracuseStep 1398031 = 2097047) B2097047
theorem B1889551 : Blo 1397518 1889551 := bstep (se 1 (by rfl) ⟨1417163, by rfl⟩ : syracuseStep 1889551 = 2834327) B2834327
theorem B2692367 : Blo 1397518 2692367 := bstep (se 1 (by rfl) ⟨2019275, by rfl⟩ : syracuseStep 2692367 = 4038551) B4038551
theorem B1398075 : Blo 1397518 1398075 := bstep (se 1 (by rfl) ⟨1048556, by rfl⟩ : syracuseStep 1398075 = 2097113) B2097113
theorem B7075187 : Blo 1397518 7075187 := bstep (se 1 (by rfl) ⟨5306390, by rfl⟩ : syracuseStep 7075187 = 10612781) B10612781
theorem B1398151 : Blo 1397518 1398151 := bstep (se 1 (by rfl) ⟨1048613, by rfl⟩ : syracuseStep 1398151 = 2097227) B2097227
theorem B1398159 : Blo 1397518 1398159 := bstep (se 1 (by rfl) ⟨1048619, by rfl⟩ : syracuseStep 1398159 = 2097239) B2097239
theorem B57398705 : Blo 1397518 57398705 := bstep (se 2 (by rfl) ⟨21524514, by rfl⟩ : syracuseStep 57398705 = 43049029) B43049029
theorem B7083449 : Blo 1397518 7083449 := bstep (se 2 (by rfl) ⟨2656293, by rfl⟩ : syracuseStep 7083449 = 5312587) B5312587
theorem B1398203 : Blo 1397518 1398203 := bstep (se 1 (by rfl) ⟨1048652, by rfl⟩ : syracuseStep 1398203 = 2097305) B2097305
theorem B1398279 : Blo 1397518 1398279 := bstep (se 1 (by rfl) ⟨1048709, by rfl⟩ : syracuseStep 1398279 = 2097419) B2097419
theorem B1398287 : Blo 1397518 1398287 := bstep (se 1 (by rfl) ⟨1048715, by rfl⟩ : syracuseStep 1398287 = 2097431) B2097431
theorem B14358059 : Blo 1397518 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1398331 : Blo 1397518 1398331 := bstep (se 1 (by rfl) ⟨1048748, by rfl⟩ : syracuseStep 1398331 = 2097497) B2097497
theorem B2987579 : Blo 1397518 2987579 := bstep (se 1 (by rfl) ⟨2240684, by rfl⟩ : syracuseStep 2987579 = 4481369) B4481369
theorem B10212941 : Blo 1397518 10212941 := bstep (se 3 (by rfl) ⟨1914926, by rfl⟩ : syracuseStep 10212941 = 3829853) B3829853
theorem B1398407 : Blo 1397518 1398407 := bstep (se 1 (by rfl) ⟨1048805, by rfl⟩ : syracuseStep 1398407 = 2097611) B2097611
theorem B1398415 : Blo 1397518 1398415 := bstep (se 1 (by rfl) ⟨1048811, by rfl⟩ : syracuseStep 1398415 = 2097623) B2097623
theorem B1398459 : Blo 1397518 1398459 := bstep (se 1 (by rfl) ⟨1048844, by rfl⟩ : syracuseStep 1398459 = 2097689) B2097689
theorem B7558849 : Blo 1397518 7558849 := bstep (se 2 (by rfl) ⟨2834568, by rfl⟩ : syracuseStep 7558849 = 5669137) B5669137
theorem B8509157 : Blo 1397518 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B1398535 : Blo 1397518 1398535 := bstep (se 1 (by rfl) ⟨1048901, by rfl⟩ : syracuseStep 1398535 = 2097803) B2097803
theorem B1398543 : Blo 1397518 1398543 := bstep (se 1 (by rfl) ⟨1048907, by rfl⟩ : syracuseStep 1398543 = 2097815) B2097815
theorem B15324977 : Blo 1397518 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B7968563 : Blo 1397518 7968563 := bstep (se 1 (by rfl) ⟨5976422, by rfl⟩ : syracuseStep 7968563 = 11952845) B11952845
theorem B1398587 : Blo 1397518 1398587 := bstep (se 1 (by rfl) ⟨1048940, by rfl⟩ : syracuseStep 1398587 = 2097881) B2097881
theorem B28686149 : Blo 1397518 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B7075673 : Blo 1397518 7075673 := bstep (se 2 (by rfl) ⟨2653377, by rfl⟩ : syracuseStep 7075673 = 5306755) B5306755
theorem B1398663 : Blo 1397518 1398663 := bstep (se 1 (by rfl) ⟨1048997, by rfl⟩ : syracuseStep 1398663 = 2097995) B2097995
theorem B1398671 : Blo 1397518 1398671 := bstep (se 1 (by rfl) ⟨1049003, by rfl⟩ : syracuseStep 1398671 = 2098007) B2098007
theorem B1398715 : Blo 1397518 1398715 := bstep (se 1 (by rfl) ⟨1049036, by rfl⟩ : syracuseStep 1398715 = 2098073) B2098073
theorem B1398791 : Blo 1397518 1398791 := bstep (se 1 (by rfl) ⟨1049093, by rfl⟩ : syracuseStep 1398791 = 2098187) B2098187
theorem B10622987 : Blo 1397518 10622987 := bstep (se 1 (by rfl) ⟨7967240, by rfl⟩ : syracuseStep 10622987 = 15934481) B15934481
theorem B1398799 : Blo 1397518 1398799 := bstep (se 1 (by rfl) ⟨1049099, by rfl⟩ : syracuseStep 1398799 = 2098199) B2098199
theorem B5969963 : Blo 1397518 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B1398843 : Blo 1397518 1398843 := bstep (se 1 (by rfl) ⟨1049132, by rfl⟩ : syracuseStep 1398843 = 2098265) B2098265
theorem B1398919 : Blo 1397518 1398919 := bstep (se 1 (by rfl) ⟨1049189, by rfl⟩ : syracuseStep 1398919 = 2098379) B2098379
theorem B1398927 : Blo 1397518 1398927 := bstep (se 1 (by rfl) ⟨1049195, by rfl⟩ : syracuseStep 1398927 = 2098391) B2098391
theorem B15931565 : Blo 1397518 15931565 := bstep (se 3 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 15931565 = 5974337) B5974337
theorem B1398971 : Blo 1397518 1398971 := bstep (se 1 (by rfl) ⟨1049228, by rfl⟩ : syracuseStep 1398971 = 2098457) B2098457
theorem B13433033 : Blo 1397518 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B6052097 : Blo 1397518 6052097 := bstep (se 2 (by rfl) ⟨2269536, by rfl⟩ : syracuseStep 6052097 = 4539073) B4539073
theorem B1399047 : Blo 1397518 1399047 := bstep (se 1 (by rfl) ⟨1049285, by rfl⟩ : syracuseStep 1399047 = 2098571) B2098571
theorem B1399055 : Blo 1397518 1399055 := bstep (se 1 (by rfl) ⟨1049291, by rfl⟩ : syracuseStep 1399055 = 2098583) B2098583
theorem B1399099 : Blo 1397518 1399099 := bstep (se 1 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 1399099 = 2098649) B2098649
theorem B1399175 : Blo 1397518 1399175 := bstep (se 1 (by rfl) ⟨1049381, by rfl⟩ : syracuseStep 1399175 = 2098763) B2098763
theorem B1399183 : Blo 1397518 1399183 := bstep (se 1 (by rfl) ⟨1049387, by rfl⟩ : syracuseStep 1399183 = 2098775) B2098775
theorem B4716953 : Blo 1397518 4716953 := bstep (se 2 (by rfl) ⟨1768857, by rfl⟩ : syracuseStep 4716953 = 3537715) B3537715
theorem B1399227 : Blo 1397518 1399227 := bstep (se 1 (by rfl) ⟨1049420, by rfl⟩ : syracuseStep 1399227 = 2098841) B2098841
theorem B1399303 : Blo 1397518 1399303 := bstep (se 1 (by rfl) ⟨1049477, by rfl⟩ : syracuseStep 1399303 = 2098955) B2098955
theorem B1399311 : Blo 1397518 1399311 := bstep (se 1 (by rfl) ⟨1049483, by rfl⟩ : syracuseStep 1399311 = 2098967) B2098967
theorem B1399355 : Blo 1397518 1399355 := bstep (se 1 (by rfl) ⟨1049516, by rfl⟩ : syracuseStep 1399355 = 2099033) B2099033
theorem B1399431 : Blo 1397518 1399431 := bstep (se 1 (by rfl) ⟨1049573, by rfl⟩ : syracuseStep 1399431 = 2099147) B2099147
theorem B1399439 : Blo 1397518 1399439 := bstep (se 1 (by rfl) ⟨1049579, by rfl⟩ : syracuseStep 1399439 = 2099159) B2099159
theorem B1399483 : Blo 1397518 1399483 := bstep (se 1 (by rfl) ⟨1049612, by rfl⟩ : syracuseStep 1399483 = 2099225) B2099225
theorem B6470345 : Blo 1397518 6470345 := bstep (se 2 (by rfl) ⟨2426379, by rfl⟩ : syracuseStep 6470345 = 4852759) B4852759
theorem B7084745 : Blo 1397518 7084745 := bstep (se 2 (by rfl) ⟨2656779, by rfl⟩ : syracuseStep 7084745 = 5313559) B5313559
theorem B15940313 : Blo 1397518 15940313 := bstep (se 2 (by rfl) ⟨5977617, by rfl⟩ : syracuseStep 15940313 = 11955235) B11955235
theorem B3537665 : Blo 1397518 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B3144491 : Blo 1397518 3144491 := bstep (se 1 (by rfl) ⟨2358368, by rfl⟩ : syracuseStep 3144491 = 4716737) B4716737
theorem B5970955 : Blo 1397518 5970955 := bstep (se 1 (by rfl) ⟨4478216, by rfl⟩ : syracuseStep 5970955 = 8956433) B8956433
theorem B4717655 : Blo 1397518 4717655 := bstep (se 1 (by rfl) ⟨3538241, by rfl⟩ : syracuseStep 4717655 = 7076483) B7076483
theorem B9337943 : Blo 1397518 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B3538039 : Blo 1397518 3538039 := bstep (se 1 (by rfl) ⟨2653529, by rfl⟩ : syracuseStep 3538039 = 5307059) B5307059
theorem B3144851 : Blo 1397518 3144851 := bstep (se 1 (by rfl) ⟨2358638, by rfl⟩ : syracuseStep 3144851 = 4717277) B4717277
theorem B7961773 : Blo 1397518 7961773 := bstep (se 3 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 7961773 = 2985665) B2985665
theorem B2096315 : Blo 1397518 2096315 := bstep (se 1 (by rfl) ⟨1572236, by rfl⟩ : syracuseStep 2096315 = 3144473) B3144473
theorem B3144905 : Blo 1397518 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B7970021 : Blo 1397518 7970021 := bstep (se 4 (by rfl) ⟨747189, by rfl⟩ : syracuseStep 7970021 = 1494379) B1494379
theorem B2096375 : Blo 1397518 2096375 := bstep (se 1 (by rfl) ⟨1572281, by rfl⟩ : syracuseStep 2096375 = 3144563) B3144563
theorem B2096399 : Blo 1397518 2096399 := bstep (se 1 (by rfl) ⟨1572299, by rfl⟩ : syracuseStep 2096399 = 3144599) B3144599
theorem B2358571 : Blo 1397518 2358571 := bstep (se 1 (by rfl) ⟨1768928, by rfl⟩ : syracuseStep 2358571 = 3537857) B3537857
theorem B2096441 : Blo 1397518 2096441 := bstep (se 2 (by rfl) ⟨786165, by rfl⟩ : syracuseStep 2096441 = 1572331) B1572331
theorem B2653499 : Blo 1397518 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B3980603 : Blo 1397518 3980603 := bstep (se 1 (by rfl) ⟨2985452, by rfl⟩ : syracuseStep 3980603 = 5970905) B5970905
theorem B3980659 : Blo 1397518 3980659 := bstep (se 1 (by rfl) ⟨2985494, by rfl⟩ : syracuseStep 3980659 = 5970989) B5970989
theorem B2096519 : Blo 1397518 2096519 := bstep (se 1 (by rfl) ⟨1572389, by rfl⟩ : syracuseStep 2096519 = 3144779) B3144779
theorem B2096555 : Blo 1397518 2096555 := bstep (se 1 (by rfl) ⟨1572416, by rfl⟩ : syracuseStep 2096555 = 3144833) B3144833
theorem B2358713 : Blo 1397518 2358713 := bstep (se 2 (by rfl) ⟨884517, by rfl⟩ : syracuseStep 2358713 = 1769035) B1769035
theorem B2096585 : Blo 1397518 2096585 := bstep (se 2 (by rfl) ⟨786219, by rfl⟩ : syracuseStep 2096585 = 1572439) B1572439
theorem B1572367 : Blo 1397518 1572367 := bstep (se 1 (by rfl) ⟨1179275, by rfl⟩ : syracuseStep 1572367 = 2358551) B2358551
theorem B3538475 : Blo 1397518 3538475 := bstep (se 1 (by rfl) ⟨2653856, by rfl⟩ : syracuseStep 3538475 = 5307713) B5307713
theorem B2096699 : Blo 1397518 2096699 := bstep (se 1 (by rfl) ⟨1572524, by rfl⟩ : syracuseStep 2096699 = 3145049) B3145049
theorem B4718141 : Blo 1397518 4718141 := bstep (se 3 (by rfl) ⟨884651, by rfl⟩ : syracuseStep 4718141 = 1769303) B1769303
theorem B5455421 : Blo 1397518 5455421 := bstep (se 3 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 5455421 = 2045783) B2045783
theorem B6725207 : Blo 1397518 6725207 := bstep (se 1 (by rfl) ⟨5043905, by rfl⟩ : syracuseStep 6725207 = 10087811) B10087811
theorem B2096759 : Blo 1397518 2096759 := bstep (se 1 (by rfl) ⟨1572569, by rfl⟩ : syracuseStep 2096759 = 3145139) B3145139
theorem B2096783 : Blo 1397518 2096783 := bstep (se 1 (by rfl) ⟨1572587, by rfl⟩ : syracuseStep 2096783 = 3145175) B3145175
theorem B40345229 : Blo 1397518 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B1769131 : Blo 1397518 1769131 := bstep (se 1 (by rfl) ⟨1326848, by rfl⟩ : syracuseStep 1769131 = 2653697) B2653697
theorem B2096825 : Blo 1397518 2096825 := bstep (se 2 (by rfl) ⟨786309, by rfl⟩ : syracuseStep 2096825 = 1572619) B1572619
theorem B3981001 : Blo 1397518 3981001 := bstep (se 2 (by rfl) ⟨1492875, by rfl⟩ : syracuseStep 3981001 = 2985751) B2985751
theorem B2096903 : Blo 1397518 2096903 := bstep (se 1 (by rfl) ⟨1572677, by rfl⟩ : syracuseStep 2096903 = 3145355) B3145355
theorem B2653985 : Blo 1397518 2653985 := bstep (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) B1990489
theorem B2096939 : Blo 1397518 2096939 := bstep (se 1 (by rfl) ⟨1572704, by rfl⟩ : syracuseStep 2096939 = 3145409) B3145409
theorem B2096969 : Blo 1397518 2096969 := bstep (se 2 (by rfl) ⟨786363, by rfl⟩ : syracuseStep 2096969 = 1572727) B1572727
theorem B4480883 : Blo 1397518 4480883 := bstep (se 1 (by rfl) ⟨3360662, by rfl⟩ : syracuseStep 4480883 = 6721325) B6721325
theorem B3145607 : Blo 1397518 3145607 := bstep (se 1 (by rfl) ⟨2359205, by rfl⟩ : syracuseStep 3145607 = 4718411) B4718411
theorem B1769359 : Blo 1397518 1769359 := bstep (se 1 (by rfl) ⟨1327019, by rfl⟩ : syracuseStep 1769359 = 2654039) B2654039
theorem B7077779 : Blo 1397518 7077779 := bstep (se 1 (by rfl) ⟨5308334, by rfl⟩ : syracuseStep 7077779 = 10616669) B10616669
theorem B10624931 : Blo 1397518 10624931 := bstep (se 1 (by rfl) ⟨7968698, by rfl⟩ : syracuseStep 10624931 = 15937397) B15937397
theorem B2654137 : Blo 1397518 2654137 := bstep (se 2 (by rfl) ⟨995301, by rfl⟩ : syracuseStep 2654137 = 1990603) B1990603
theorem B2097083 : Blo 1397518 2097083 := bstep (se 1 (by rfl) ⟨1572812, by rfl⟩ : syracuseStep 2097083 = 3145625) B3145625
theorem B2097143 : Blo 1397518 2097143 := bstep (se 1 (by rfl) ⟨1572857, by rfl⟩ : syracuseStep 2097143 = 3145715) B3145715
theorem B2097161 : Blo 1397518 2097161 := bstep (se 2 (by rfl) ⟨786435, by rfl⟩ : syracuseStep 2097161 = 1572871) B1572871
theorem B5668879 : Blo 1397518 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B2097191 : Blo 1397518 2097191 := bstep (se 1 (by rfl) ⟨1572893, by rfl⟩ : syracuseStep 2097191 = 3145787) B3145787
theorem B1572943 : Blo 1397518 1572943 := bstep (se 1 (by rfl) ⟨1179707, by rfl⟩ : syracuseStep 1572943 = 2359415) B2359415
theorem B5038195 : Blo 1397518 5038195 := bstep (se 1 (by rfl) ⟨3778646, by rfl⟩ : syracuseStep 5038195 = 7557293) B7557293
theorem B2097275 : Blo 1397518 2097275 := bstep (se 1 (by rfl) ⟨1572956, by rfl⟩ : syracuseStep 2097275 = 3145913) B3145913
theorem B2834603 : Blo 1397518 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B2359543 : Blo 1397518 2359543 := bstep (se 1 (by rfl) ⟨1769657, by rfl⟩ : syracuseStep 2359543 = 3539315) B3539315
theorem B2097401 : Blo 1397518 2097401 := bstep (se 2 (by rfl) ⟨786525, by rfl⟩ : syracuseStep 2097401 = 1573051) B1573051
theorem B2097503 : Blo 1397518 2097503 := bstep (se 1 (by rfl) ⟨1573127, by rfl⟩ : syracuseStep 2097503 = 3146255) B3146255
theorem B2097515 : Blo 1397518 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B1794487 : Blo 1397518 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B2359739 : Blo 1397518 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B1573339 : Blo 1397518 1573339 := bstep (se 1 (by rfl) ⟨1180004, by rfl⟩ : syracuseStep 1573339 = 2360009) B2360009
theorem B4719113 : Blo 1397518 4719113 := bstep (se 2 (by rfl) ⟨1769667, by rfl⟩ : syracuseStep 4719113 = 3539335) B3539335
theorem B2359847 : Blo 1397518 2359847 := bstep (se 1 (by rfl) ⟨1769885, by rfl⟩ : syracuseStep 2359847 = 3539771) B3539771
theorem B2097743 : Blo 1397518 2097743 := bstep (se 1 (by rfl) ⟨1573307, by rfl⟩ : syracuseStep 2097743 = 3146615) B3146615
theorem B45998711 : Blo 1397518 45998711 := bstep (se 1 (by rfl) ⟨34499033, by rfl⟩ : syracuseStep 45998711 = 68998067) B68998067
theorem B3146363 : Blo 1397518 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B2097863 : Blo 1397518 2097863 := bstep (se 1 (by rfl) ⟨1573397, by rfl⟩ : syracuseStep 2097863 = 3146795) B3146795
theorem B3146489 : Blo 1397518 3146489 := bstep (se 2 (by rfl) ⟨1179933, by rfl⟩ : syracuseStep 3146489 = 2359867) B2359867
theorem B2360137 : Blo 1397518 2360137 := bstep (se 2 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 2360137 = 1770103) B1770103
theorem B1794911 : Blo 1397518 1794911 := bstep (se 1 (by rfl) ⟨1346183, by rfl⟩ : syracuseStep 1794911 = 2692367) B2692367
theorem B2098025 : Blo 1397518 2098025 := bstep (se 2 (by rfl) ⟨786759, by rfl⟩ : syracuseStep 2098025 = 1573519) B1573519
theorem B2360171 : Blo 1397518 2360171 := bstep (se 1 (by rfl) ⟨1770128, by rfl⟩ : syracuseStep 2360171 = 3540257) B3540257
theorem B1573807 : Blo 1397518 1573807 := bstep (se 1 (by rfl) ⟨1180355, by rfl⟩ : syracuseStep 1573807 = 2360711) B2360711
theorem B2098103 : Blo 1397518 2098103 := bstep (se 1 (by rfl) ⟨1573577, by rfl⟩ : syracuseStep 2098103 = 3147155) B3147155
theorem B38265803 : Blo 1397518 38265803 := bstep (se 1 (by rfl) ⟨28699352, by rfl⟩ : syracuseStep 38265803 = 57398705) B57398705
theorem B2098139 : Blo 1397518 2098139 := bstep (se 1 (by rfl) ⟨1573604, by rfl⟩ : syracuseStep 2098139 = 3147209) B3147209
theorem B8963045 : Blo 1397518 8963045 := bstep (se 4 (by rfl) ⟨840285, by rfl⟩ : syracuseStep 8963045 = 1680571) B1680571
theorem B7078913 : Blo 1397518 7078913 := bstep (se 2 (by rfl) ⟨2654592, by rfl⟩ : syracuseStep 7078913 = 5309185) B5309185
theorem B40313861 : Blo 1397518 40313861 := bstep (se 4 (by rfl) ⟨3779424, by rfl⟩ : syracuseStep 40313861 = 7558849) B7558849
theorem B3146759 : Blo 1397518 3146759 := bstep (se 1 (by rfl) ⟨2360069, by rfl⟩ : syracuseStep 3146759 = 4720139) B4720139
theorem B5309459 : Blo 1397518 5309459 := bstep (se 1 (by rfl) ⟨3982094, by rfl⟩ : syracuseStep 5309459 = 7964189) B7964189
theorem B1991719 : Blo 1397518 1991719 := bstep (se 1 (by rfl) ⟨1493789, by rfl⟩ : syracuseStep 1991719 = 2987579) B2987579
theorem B57443377 : Blo 1397518 57443377 := bstep (se 2 (by rfl) ⟨21541266, by rfl⟩ : syracuseStep 57443377 = 43082533) B43082533
theorem B6808627 : Blo 1397518 6808627 := bstep (se 1 (by rfl) ⟨5106470, by rfl⟩ : syracuseStep 6808627 = 10212941) B10212941
theorem B3146831 : Blo 1397518 3146831 := bstep (se 1 (by rfl) ⟨2360123, by rfl⟩ : syracuseStep 3146831 = 4720247) B4720247
theorem B9077953 : Blo 1397518 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B10216651 : Blo 1397518 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B2655443 : Blo 1397518 2655443 := bstep (se 1 (by rfl) ⟨1991582, by rfl⟩ : syracuseStep 2655443 = 3983165) B3983165
theorem B2360569 : Blo 1397518 2360569 := bstep (se 2 (by rfl) ⟨885213, by rfl⟩ : syracuseStep 2360569 = 1770427) B1770427
theorem B4785419 : Blo 1397518 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B10618127 : Blo 1397518 10618127 := bstep (se 1 (by rfl) ⟨7963595, by rfl⟩ : syracuseStep 10618127 = 15927191) B15927191
theorem B9569573 : Blo 1397518 9569573 := bstep (se 4 (by rfl) ⟨897147, by rfl⟩ : syracuseStep 9569573 = 1794295) B1794295
theorem B1574239 : Blo 1397518 1574239 := bstep (se 1 (by rfl) ⟨1180679, by rfl⟩ : syracuseStep 1574239 = 2361359) B2361359
theorem B4719977 : Blo 1397518 4719977 := bstep (se 2 (by rfl) ⟨1769991, by rfl⟩ : syracuseStep 4719977 = 3539983) B3539983
theorem B2655595 : Blo 1397518 2655595 := bstep (se 1 (by rfl) ⟨1991696, by rfl⟩ : syracuseStep 2655595 = 3983393) B3983393
theorem B3360143 : Blo 1397518 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B10077605 : Blo 1397518 10077605 := bstep (se 4 (by rfl) ⟨944775, by rfl⟩ : syracuseStep 10077605 = 1889551) B1889551
theorem B2098607 : Blo 1397518 2098607 := bstep (se 1 (by rfl) ⟨1573955, by rfl⟩ : syracuseStep 2098607 = 3147911) B3147911
theorem B45376969 : Blo 1397518 45376969 := bstep (se 2 (by rfl) ⟨17016363, by rfl⟩ : syracuseStep 45376969 = 34032727) B34032727
theorem B8955355 : Blo 1397518 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B3147227 : Blo 1397518 3147227 := bstep (se 1 (by rfl) ⟨2360420, by rfl⟩ : syracuseStep 3147227 = 4720841) B4720841
theorem B2360839 : Blo 1397518 2360839 := bstep (se 1 (by rfl) ⟨1770629, by rfl⟩ : syracuseStep 2360839 = 3541259) B3541259
theorem B2098697 : Blo 1397518 2098697 := bstep (se 2 (by rfl) ⟨787011, by rfl⟩ : syracuseStep 2098697 = 1574023) B1574023
theorem B2098727 : Blo 1397518 2098727 := bstep (se 1 (by rfl) ⟨1574045, by rfl⟩ : syracuseStep 2098727 = 3148091) B3148091
theorem B2655823 : Blo 1397518 2655823 := bstep (se 1 (by rfl) ⟨1991867, by rfl⟩ : syracuseStep 2655823 = 3983735) B3983735
theorem B2098811 : Blo 1397518 2098811 := bstep (se 1 (by rfl) ⟨1574108, by rfl⟩ : syracuseStep 2098811 = 3148217) B3148217
theorem B1492679 : Blo 1397518 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B2098937 : Blo 1397518 2098937 := bstep (se 2 (by rfl) ⟨787101, by rfl⟩ : syracuseStep 2098937 = 1574203) B1574203
theorem B7079723 : Blo 1397518 7079723 := bstep (se 1 (by rfl) ⟨5309792, by rfl⟩ : syracuseStep 7079723 = 10619585) B10619585
theorem B10626875 : Blo 1397518 10626875 := bstep (se 1 (by rfl) ⟨7970156, by rfl⟩ : syracuseStep 10626875 = 15940313) B15940313
theorem B2099039 : Blo 1397518 2099039 := bstep (se 1 (by rfl) ⟨1574279, by rfl⟩ : syracuseStep 2099039 = 3148559) B3148559
theorem B2099051 : Blo 1397518 2099051 := bstep (se 1 (by rfl) ⟨1574288, by rfl⟩ : syracuseStep 2099051 = 3148577) B3148577
theorem B17254253 : Blo 1397518 17254253 := bstep (se 3 (by rfl) ⟨3235172, by rfl⟩ : syracuseStep 17254253 = 6470345) B6470345
theorem B3147695 : Blo 1397518 3147695 := bstep (se 1 (by rfl) ⟨2360771, by rfl⟩ : syracuseStep 3147695 = 4721543) B4721543
theorem B2361271 : Blo 1397518 2361271 := bstep (se 1 (by rfl) ⟨1770953, by rfl⟩ : syracuseStep 2361271 = 3541907) B3541907
theorem B4720571 : Blo 1397518 4720571 := bstep (se 1 (by rfl) ⟨3540428, by rfl⟩ : syracuseStep 4720571 = 7080857) B7080857
theorem B2361467 : Blo 1397518 2361467 := bstep (se 1 (by rfl) ⟨1771100, by rfl⟩ : syracuseStep 2361467 = 3542201) B3542201
theorem B3147947 : Blo 1397518 3147947 := bstep (se 1 (by rfl) ⟨2360960, by rfl⟩ : syracuseStep 3147947 = 4721921) B4721921
theorem B91998445 : Blo 1397518 91998445 := bstep (se 3 (by rfl) ⟨17249708, by rfl⟩ : syracuseStep 91998445 = 34499417) B34499417
theorem B3541391 : Blo 1397518 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B4483471 : Blo 1397518 4483471 := bstep (se 1 (by rfl) ⟨3362603, by rfl⟩ : syracuseStep 4483471 = 6725207) B6725207
theorem B26896819 : Blo 1397518 26896819 := bstep (se 1 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 26896819 = 40345229) B40345229
theorem B5311115 : Blo 1397518 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B19139257 : Blo 1397518 19139257 := bstep (se 2 (by rfl) ⟨7177221, by rfl⟩ : syracuseStep 19139257 = 14354443) B14354443
theorem B3148487 : Blo 1397518 3148487 := bstep (se 1 (by rfl) ⟨2361365, by rfl⟩ : syracuseStep 3148487 = 4722731) B4722731
theorem B13806281 : Blo 1397518 13806281 := bstep (se 2 (by rfl) ⟨5177355, by rfl⟩ : syracuseStep 13806281 = 10354711) B10354711
theorem B3541715 : Blo 1397518 3541715 := bstep (se 1 (by rfl) ⟨2656286, by rfl⟩ : syracuseStep 3541715 = 5312573) B5312573
theorem B15919901 : Blo 1397518 15919901 := bstep (se 3 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 15919901 = 5969963) B5969963
theorem B2984777 : Blo 1397518 2984777 := bstep (se 2 (by rfl) ⟨1119291, by rfl⟩ : syracuseStep 2984777 = 2238583) B2238583
theorem B5041079 : Blo 1397518 5041079 := bstep (se 1 (by rfl) ⟨3780809, by rfl⟩ : syracuseStep 5041079 = 7561619) B7561619
theorem B10079275 : Blo 1397518 10079275 := bstep (se 1 (by rfl) ⟨7559456, by rfl⟩ : syracuseStep 10079275 = 15118913) B15118913
theorem B4254967 : Blo 1397518 4254967 := bstep (se 1 (by rfl) ⟨3191225, by rfl⟩ : syracuseStep 4254967 = 6382451) B6382451
theorem B23899535 : Blo 1397518 23899535 := bstep (se 1 (by rfl) ⟨17924651, by rfl⟩ : syracuseStep 23899535 = 35849303) B35849303
theorem B4722299 : Blo 1397518 4722299 := bstep (se 1 (by rfl) ⟨3541724, by rfl⟩ : syracuseStep 4722299 = 7083449) B7083449
theorem B8957587 : Blo 1397518 8957587 := bstep (se 1 (by rfl) ⟨6718190, by rfl⟩ : syracuseStep 8957587 = 13436381) B13436381
theorem B9572039 : Blo 1397518 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B4722461 : Blo 1397518 4722461 := bstep (se 3 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 4722461 = 1770923) B1770923
theorem B5672771 : Blo 1397518 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B45993845 : Blo 1397518 45993845 := bstep (se 5 (by rfl) ⟨2155961, by rfl⟩ : syracuseStep 45993845 = 4311923) B4311923
theorem B5312375 : Blo 1397518 5312375 := bstep (se 1 (by rfl) ⟨3984281, by rfl⟩ : syracuseStep 5312375 = 7968563) B7968563
theorem B19124099 : Blo 1397518 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B7081991 : Blo 1397518 7081991 := bstep (se 1 (by rfl) ⟨5311493, by rfl⟩ : syracuseStep 7081991 = 10622987) B10622987
theorem B10621043 : Blo 1397518 10621043 := bstep (se 1 (by rfl) ⟨7965782, by rfl⟩ : syracuseStep 10621043 = 15931565) B15931565
theorem B4034731 : Blo 1397518 4034731 := bstep (se 1 (by rfl) ⟨3026048, by rfl⟩ : syracuseStep 4034731 = 6052097) B6052097
theorem B45363473 : Blo 1397518 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B7967105 : Blo 1397518 7967105 := bstep (se 2 (by rfl) ⟨2987664, by rfl⟩ : syracuseStep 7967105 = 5975329) B5975329
theorem B4723163 : Blo 1397518 4723163 := bstep (se 1 (by rfl) ⟨3542372, by rfl⟩ : syracuseStep 4723163 = 7084745) B7084745
theorem B7082477 : Blo 1397518 7082477 := bstep (se 3 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 7082477 = 2655929) B2655929
theorem B331321873 : Blo 1397518 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B2519675 : Blo 1397518 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B1397543 : Blo 1397518 1397543 := bstep (se 1 (by rfl) ⟨1048157, by rfl⟩ : syracuseStep 1397543 = 2096315) B2096315
theorem B5313347 : Blo 1397518 5313347 := bstep (se 1 (by rfl) ⟨3985010, by rfl⟩ : syracuseStep 5313347 = 7970021) B7970021
theorem B1397583 : Blo 1397518 1397583 := bstep (se 1 (by rfl) ⟨1048187, by rfl⟩ : syracuseStep 1397583 = 2096375) B2096375
theorem B1397599 : Blo 1397518 1397599 := bstep (se 1 (by rfl) ⟨1048199, by rfl⟩ : syracuseStep 1397599 = 2096399) B2096399
theorem B1397627 : Blo 1397518 1397627 := bstep (se 1 (by rfl) ⟨1048220, by rfl⟩ : syracuseStep 1397627 = 2096441) B2096441
theorem B1397679 : Blo 1397518 1397679 := bstep (se 1 (by rfl) ⟨1048259, by rfl⟩ : syracuseStep 1397679 = 2096519) B2096519
theorem B1397703 : Blo 1397518 1397703 := bstep (se 1 (by rfl) ⟨1048277, by rfl⟩ : syracuseStep 1397703 = 2096555) B2096555
theorem B1397723 : Blo 1397518 1397723 := bstep (se 1 (by rfl) ⟨1048292, by rfl⟩ : syracuseStep 1397723 = 2096585) B2096585
theorem B1397799 : Blo 1397518 1397799 := bstep (se 1 (by rfl) ⟨1048349, by rfl⟩ : syracuseStep 1397799 = 2096699) B2096699
theorem B1397839 : Blo 1397518 1397839 := bstep (se 1 (by rfl) ⟨1048379, by rfl⟩ : syracuseStep 1397839 = 2096759) B2096759
theorem B1397855 : Blo 1397518 1397855 := bstep (se 1 (by rfl) ⟨1048391, by rfl⟩ : syracuseStep 1397855 = 2096783) B2096783
theorem B1397883 : Blo 1397518 1397883 := bstep (se 1 (by rfl) ⟨1048412, by rfl⟩ : syracuseStep 1397883 = 2096825) B2096825
theorem B1397935 : Blo 1397518 1397935 := bstep (se 1 (by rfl) ⟨1048451, by rfl⟩ : syracuseStep 1397935 = 2096903) B2096903
theorem B1397959 : Blo 1397518 1397959 := bstep (se 1 (by rfl) ⟨1048469, by rfl⟩ : syracuseStep 1397959 = 2096939) B2096939
theorem B1397979 : Blo 1397518 1397979 := bstep (se 1 (by rfl) ⟨1048484, by rfl⟩ : syracuseStep 1397979 = 2096969) B2096969
theorem B2987255 : Blo 1397518 2987255 := bstep (se 1 (by rfl) ⟨2240441, by rfl⟩ : syracuseStep 2987255 = 4480883) B4480883
theorem B7083287 : Blo 1397518 7083287 := bstep (se 1 (by rfl) ⟨5312465, by rfl⟩ : syracuseStep 7083287 = 10624931) B10624931
theorem B1398055 : Blo 1397518 1398055 := bstep (se 1 (by rfl) ⟨1048541, by rfl⟩ : syracuseStep 1398055 = 2097083) B2097083
theorem B1398095 : Blo 1397518 1398095 := bstep (se 1 (by rfl) ⟨1048571, by rfl⟩ : syracuseStep 1398095 = 2097143) B2097143
theorem B1398111 : Blo 1397518 1398111 := bstep (se 1 (by rfl) ⟨1048583, by rfl⟩ : syracuseStep 1398111 = 2097167) B2097167
theorem B1398139 : Blo 1397518 1398139 := bstep (se 1 (by rfl) ⟨1048604, by rfl⟩ : syracuseStep 1398139 = 2097209) B2097209
theorem B6722959 : Blo 1397518 6722959 := bstep (se 1 (by rfl) ⟨5042219, by rfl⟩ : syracuseStep 6722959 = 10084439) B10084439
theorem B1398191 : Blo 1397518 1398191 := bstep (se 1 (by rfl) ⟨1048643, by rfl⟩ : syracuseStep 1398191 = 2097287) B2097287
theorem B1398215 : Blo 1397518 1398215 := bstep (se 1 (by rfl) ⟨1048661, by rfl⟩ : syracuseStep 1398215 = 2097323) B2097323
theorem B1398235 : Blo 1397518 1398235 := bstep (se 1 (by rfl) ⟨1048676, by rfl⟩ : syracuseStep 1398235 = 2097353) B2097353
theorem B1398311 : Blo 1397518 1398311 := bstep (se 1 (by rfl) ⟨1048733, by rfl⟩ : syracuseStep 1398311 = 2097467) B2097467
theorem B1398351 : Blo 1397518 1398351 := bstep (se 1 (by rfl) ⟨1048763, by rfl⟩ : syracuseStep 1398351 = 2097527) B2097527
theorem B1398367 : Blo 1397518 1398367 := bstep (se 1 (by rfl) ⟨1048775, by rfl⟩ : syracuseStep 1398367 = 2097551) B2097551
theorem B1398395 : Blo 1397518 1398395 := bstep (se 1 (by rfl) ⟨1048796, by rfl⟩ : syracuseStep 1398395 = 2097593) B2097593
theorem B5977739 : Blo 1397518 5977739 := bstep (se 1 (by rfl) ⟨4483304, by rfl⟩ : syracuseStep 5977739 = 8966609) B8966609
theorem B1398447 : Blo 1397518 1398447 := bstep (se 1 (by rfl) ⟨1048835, by rfl⟩ : syracuseStep 1398447 = 2097671) B2097671
theorem B1398471 : Blo 1397518 1398471 := bstep (se 1 (by rfl) ⟨1048853, by rfl⟩ : syracuseStep 1398471 = 2097707) B2097707
theorem B17921735 : Blo 1397518 17921735 := bstep (se 1 (by rfl) ⟨13441301, by rfl⟩ : syracuseStep 17921735 = 26882603) B26882603
theorem B1398491 : Blo 1397518 1398491 := bstep (se 1 (by rfl) ⟨1048868, by rfl⟩ : syracuseStep 1398491 = 2097737) B2097737
theorem B15120121 : Blo 1397518 15120121 := bstep (se 2 (by rfl) ⟨5670045, by rfl⟩ : syracuseStep 15120121 = 11340091) B11340091
theorem B1398567 : Blo 1397518 1398567 := bstep (se 1 (by rfl) ⟨1048925, by rfl⟩ : syracuseStep 1398567 = 2097851) B2097851
theorem B10073915 : Blo 1397518 10073915 := bstep (se 1 (by rfl) ⟨7555436, by rfl⟩ : syracuseStep 10073915 = 15110873) B15110873
theorem B1398607 : Blo 1397518 1398607 := bstep (se 1 (by rfl) ⟨1048955, by rfl⟩ : syracuseStep 1398607 = 2097911) B2097911
theorem B1398623 : Blo 1397518 1398623 := bstep (se 1 (by rfl) ⟨1048967, by rfl⟩ : syracuseStep 1398623 = 2097935) B2097935
theorem B1398651 : Blo 1397518 1398651 := bstep (se 1 (by rfl) ⟨1048988, by rfl⟩ : syracuseStep 1398651 = 2097977) B2097977
theorem B1398703 : Blo 1397518 1398703 := bstep (se 1 (by rfl) ⟨1049027, by rfl⟩ : syracuseStep 1398703 = 2098055) B2098055
theorem B1398727 : Blo 1397518 1398727 := bstep (se 1 (by rfl) ⟨1049045, by rfl⟩ : syracuseStep 1398727 = 2098091) B2098091
theorem B1398747 : Blo 1397518 1398747 := bstep (se 1 (by rfl) ⟨1049060, by rfl⟩ : syracuseStep 1398747 = 2098121) B2098121
theorem B1398823 : Blo 1397518 1398823 := bstep (se 1 (by rfl) ⟨1049117, by rfl⟩ : syracuseStep 1398823 = 2098235) B2098235
theorem B1398863 : Blo 1397518 1398863 := bstep (se 1 (by rfl) ⟨1049147, by rfl⟩ : syracuseStep 1398863 = 2098295) B2098295
theorem B1398879 : Blo 1397518 1398879 := bstep (se 1 (by rfl) ⟨1049159, by rfl⟩ : syracuseStep 1398879 = 2098319) B2098319
theorem B1398907 : Blo 1397518 1398907 := bstep (se 1 (by rfl) ⟨1049180, by rfl⟩ : syracuseStep 1398907 = 2098361) B2098361
theorem B7075997 : Blo 1397518 7075997 := bstep (se 3 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 7075997 = 2653499) B2653499
theorem B1398959 : Blo 1397518 1398959 := bstep (se 1 (by rfl) ⟨1049219, by rfl⟩ : syracuseStep 1398959 = 2098439) B2098439
theorem B1398983 : Blo 1397518 1398983 := bstep (se 1 (by rfl) ⟨1049237, by rfl⟩ : syracuseStep 1398983 = 2098475) B2098475
theorem B1399003 : Blo 1397518 1399003 := bstep (se 1 (by rfl) ⟨1049252, by rfl⟩ : syracuseStep 1399003 = 2098505) B2098505
theorem B4716791 : Blo 1397518 4716791 := bstep (se 1 (by rfl) ⟨3537593, by rfl⟩ : syracuseStep 4716791 = 7075187) B7075187
theorem B1399079 : Blo 1397518 1399079 := bstep (se 1 (by rfl) ⟨1049309, by rfl⟩ : syracuseStep 1399079 = 2098619) B2098619
theorem B1399119 : Blo 1397518 1399119 := bstep (se 1 (by rfl) ⟨1049339, by rfl⟩ : syracuseStep 1399119 = 2098679) B2098679
theorem B1399135 : Blo 1397518 1399135 := bstep (se 1 (by rfl) ⟨1049351, by rfl⟩ : syracuseStep 1399135 = 2098703) B2098703
theorem B1399163 : Blo 1397518 1399163 := bstep (se 1 (by rfl) ⟨1049372, by rfl⟩ : syracuseStep 1399163 = 2098745) B2098745
theorem B1399215 : Blo 1397518 1399215 := bstep (se 1 (by rfl) ⟨1049411, by rfl⟩ : syracuseStep 1399215 = 2098823) B2098823
theorem B1399239 : Blo 1397518 1399239 := bstep (se 1 (by rfl) ⟨1049429, by rfl⟩ : syracuseStep 1399239 = 2098859) B2098859
theorem B1399259 : Blo 1397518 1399259 := bstep (se 1 (by rfl) ⟨1049444, by rfl⟩ : syracuseStep 1399259 = 2098889) B2098889
theorem B6724129 : Blo 1397518 6724129 := bstep (se 2 (by rfl) ⟨2521548, by rfl⟩ : syracuseStep 6724129 = 5043097) B5043097
theorem B1399335 : Blo 1397518 1399335 := bstep (se 1 (by rfl) ⟨1049501, by rfl⟩ : syracuseStep 1399335 = 2099003) B2099003
theorem B4717115 : Blo 1397518 4717115 := bstep (se 1 (by rfl) ⟨3537836, by rfl⟩ : syracuseStep 4717115 = 7075673) B7075673
theorem B23886413 : Blo 1397518 23886413 := bstep (se 3 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 23886413 = 8957405) B8957405
theorem B1399375 : Blo 1397518 1399375 := bstep (se 1 (by rfl) ⟨1049531, by rfl⟩ : syracuseStep 1399375 = 2099063) B2099063
theorem B1399391 : Blo 1397518 1399391 := bstep (se 1 (by rfl) ⟨1049543, by rfl⟩ : syracuseStep 1399391 = 2099087) B2099087
theorem B1399419 : Blo 1397518 1399419 := bstep (se 1 (by rfl) ⟨1049564, by rfl⟩ : syracuseStep 1399419 = 2099129) B2099129
theorem B1399471 : Blo 1397518 1399471 := bstep (se 1 (by rfl) ⟨1049603, by rfl⟩ : syracuseStep 1399471 = 2099207) B2099207
theorem B7961273 : Blo 1397518 7961273 := bstep (se 2 (by rfl) ⟨2985477, by rfl⟩ : syracuseStep 7961273 = 5970955) B5970955
theorem B1399495 : Blo 1397518 1399495 := bstep (se 1 (by rfl) ⟨1049621, by rfl⟩ : syracuseStep 1399495 = 2099243) B2099243
theorem B1399515 : Blo 1397518 1399515 := bstep (se 1 (by rfl) ⟨1049636, by rfl⟩ : syracuseStep 1399515 = 2099273) B2099273
theorem B4717385 : Blo 1397518 4717385 := bstep (se 2 (by rfl) ⟨1769019, by rfl⟩ : syracuseStep 4717385 = 3538039) B3538039
theorem B2988895 : Blo 1397518 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B7084907 : Blo 1397518 7084907 := bstep (se 1 (by rfl) ⟨5313680, by rfl⟩ : syracuseStep 7084907 = 10627361) B10627361
theorem B10615697 : Blo 1397518 10615697 := bstep (se 2 (by rfl) ⟨3980886, by rfl⟩ : syracuseStep 10615697 = 7961773) B7961773
theorem B3144635 : Blo 1397518 3144635 := bstep (se 1 (by rfl) ⟨2358476, by rfl⟩ : syracuseStep 3144635 = 4716953) B4716953
theorem B5037071 : Blo 1397518 5037071 := bstep (se 1 (by rfl) ⟨3777803, by rfl⟩ : syracuseStep 5037071 = 7555607) B7555607
theorem B3144761 : Blo 1397518 3144761 := bstep (se 2 (by rfl) ⟨1179285, by rfl⟩ : syracuseStep 3144761 = 2358571) B2358571
theorem B5307545 : Blo 1397518 5307545 := bstep (se 2 (by rfl) ⟨1990329, by rfl⟩ : syracuseStep 5307545 = 3980659) B3980659
theorem B2358443 : Blo 1397518 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B2096327 : Blo 1397518 2096327 := bstep (se 1 (by rfl) ⟨1572245, by rfl⟩ : syracuseStep 2096327 = 3144491) B3144491
theorem B4480267 : Blo 1397518 4480267 := bstep (se 1 (by rfl) ⟨3360200, by rfl⟩ : syracuseStep 4480267 = 6720401) B6720401
theorem B2096489 : Blo 1397518 2096489 := bstep (se 2 (by rfl) ⟨786183, by rfl⟩ : syracuseStep 2096489 = 1572367) B1572367
theorem B4251005 : Blo 1397518 4251005 := bstep (se 3 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 4251005 = 1594127) B1594127
theorem B3145103 : Blo 1397518 3145103 := bstep (se 1 (by rfl) ⟨2358827, by rfl⟩ : syracuseStep 3145103 = 4717655) B4717655
theorem B6225295 : Blo 1397518 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B7077293 : Blo 1397518 7077293 := bstep (se 3 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 7077293 = 2653985) B2653985
theorem B2096567 : Blo 1397518 2096567 := bstep (se 1 (by rfl) ⟨1572425, by rfl⟩ : syracuseStep 2096567 = 3144851) B3144851
theorem B2096603 : Blo 1397518 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B2653735 : Blo 1397518 2653735 := bstep (se 1 (by rfl) ⟨1990301, by rfl⟩ : syracuseStep 2653735 = 3980603) B3980603
theorem B2358841 : Blo 1397518 2358841 := bstep (se 2 (by rfl) ⟨884565, by rfl⟩ : syracuseStep 2358841 = 1769131) B1769131
theorem B5308001 : Blo 1397518 5308001 := bstep (se 2 (by rfl) ⟨1990500, by rfl⟩ : syracuseStep 5308001 = 3981001) B3981001
theorem B1572475 : Blo 1397518 1572475 := bstep (se 1 (by rfl) ⟨1179356, by rfl⟩ : syracuseStep 1572475 = 2358713) B2358713
theorem B141672077 : Blo 1397518 141672077 := bstep (se 3 (by rfl) ⟨26563514, by rfl⟩ : syracuseStep 141672077 = 53127029) B53127029
theorem B2358983 : Blo 1397518 2358983 := bstep (se 1 (by rfl) ⟨1769237, by rfl⟩ : syracuseStep 2358983 = 3538475) B3538475
theorem B3145427 : Blo 1397518 3145427 := bstep (se 1 (by rfl) ⟨2359070, by rfl⟩ : syracuseStep 3145427 = 4718141) B4718141
theorem B3636947 : Blo 1397518 3636947 := bstep (se 1 (by rfl) ⟨2727710, by rfl⟩ : syracuseStep 3636947 = 5455421) B5455421
theorem B2359145 : Blo 1397518 2359145 := bstep (se 2 (by rfl) ⟨884679, by rfl⟩ : syracuseStep 2359145 = 1769359) B1769359
theorem B3538849 : Blo 1397518 3538849 := bstep (se 2 (by rfl) ⟨1327068, by rfl⟩ : syracuseStep 3538849 = 2654137) B2654137
theorem B2097071 : Blo 1397518 2097071 := bstep (se 1 (by rfl) ⟨1572803, by rfl⟩ : syracuseStep 2097071 = 3145607) B3145607
theorem B4718519 : Blo 1397518 4718519 := bstep (se 1 (by rfl) ⟨3538889, by rfl⟩ : syracuseStep 4718519 = 7077779) B7077779
theorem B2097257 : Blo 1397518 2097257 := bstep (se 2 (by rfl) ⟨786471, by rfl⟩ : syracuseStep 2097257 = 1572943) B1572943
theorem B6717593 : Blo 1397518 6717593 := bstep (se 2 (by rfl) ⟨2519097, by rfl⟩ : syracuseStep 6717593 = 5038195) B5038195
theorem B1573159 : Blo 1397518 1573159 := bstep (se 1 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 1573159 = 2359739) B2359739
theorem B3146057 : Blo 1397518 3146057 := bstep (se 2 (by rfl) ⟨1179771, by rfl⟩ : syracuseStep 3146057 = 2359543) B2359543
theorem B3146075 : Blo 1397518 3146075 := bstep (se 1 (by rfl) ⟨2359556, by rfl⟩ : syracuseStep 3146075 = 4719113) B4719113
theorem B1573231 : Blo 1397518 1573231 := bstep (se 1 (by rfl) ⟨1179923, by rfl⟩ : syracuseStep 1573231 = 2359847) B2359847
theorem B1679783 : Blo 1397518 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B2097575 : Blo 1397518 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B2097659 : Blo 1397518 2097659 := bstep (se 1 (by rfl) ⟨1573244, by rfl⟩ : syracuseStep 2097659 = 3146489) B3146489
theorem B1573447 : Blo 1397518 1573447 := bstep (se 1 (by rfl) ⟨1180085, by rfl⟩ : syracuseStep 1573447 = 2360171) B2360171
theorem B2392649 : Blo 1397518 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B2097785 : Blo 1397518 2097785 := bstep (se 2 (by rfl) ⟨786669, by rfl⟩ : syracuseStep 2097785 = 1573339) B1573339
theorem B25510535 : Blo 1397518 25510535 := bstep (se 1 (by rfl) ⟨19132901, by rfl⟩ : syracuseStep 25510535 = 38265803) B38265803
theorem B4719275 : Blo 1397518 4719275 := bstep (se 1 (by rfl) ⟨3539456, by rfl⟩ : syracuseStep 4719275 = 7078913) B7078913
theorem B2097839 : Blo 1397518 2097839 := bstep (se 1 (by rfl) ⟨1573379, by rfl⟩ : syracuseStep 2097839 = 3146759) B3146759
theorem B3539639 : Blo 1397518 3539639 := bstep (se 1 (by rfl) ⟨2654729, by rfl⟩ : syracuseStep 3539639 = 5309459) B5309459
theorem B441762497 : Blo 1397518 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B2097887 : Blo 1397518 2097887 := bstep (se 1 (by rfl) ⟨1573415, by rfl⟩ : syracuseStep 2097887 = 3146831) B3146831
theorem B1991503 : Blo 1397518 1991503 := bstep (se 1 (by rfl) ⟨1493627, by rfl⟩ : syracuseStep 1991503 = 2987255) B2987255
theorem B7078751 : Blo 1397518 7078751 := bstep (se 1 (by rfl) ⟨5309063, by rfl⟩ : syracuseStep 7078751 = 10618127) B10618127
theorem B3146651 : Blo 1397518 3146651 := bstep (se 1 (by rfl) ⟨2359988, by rfl⟩ : syracuseStep 3146651 = 4719977) B4719977
theorem B25519009 : Blo 1397518 25519009 := bstep (se 2 (by rfl) ⟨9569628, by rfl⟩ : syracuseStep 25519009 = 19139257) B19139257
theorem B6718403 : Blo 1397518 6718403 := bstep (se 1 (by rfl) ⟨5038802, by rfl⟩ : syracuseStep 6718403 = 10077605) B10077605
theorem B2098151 : Blo 1397518 2098151 := bstep (se 1 (by rfl) ⟨1573613, by rfl⟩ : syracuseStep 2098151 = 3147227) B3147227
theorem B19145717 : Blo 1397518 19145717 := bstep (se 5 (by rfl) ⟨897455, by rfl⟩ : syracuseStep 19145717 = 1794911) B1794911
theorem B3146849 : Blo 1397518 3146849 := bstep (se 2 (by rfl) ⟨1180068, by rfl⟩ : syracuseStep 3146849 = 2360137) B2360137
theorem B4719815 : Blo 1397518 4719815 := bstep (se 1 (by rfl) ⟨3539861, by rfl⟩ : syracuseStep 4719815 = 7079723) B7079723
theorem B2098409 : Blo 1397518 2098409 := bstep (se 2 (by rfl) ⟨786903, by rfl⟩ : syracuseStep 2098409 = 1573807) B1573807
theorem B2098463 : Blo 1397518 2098463 := bstep (se 1 (by rfl) ⟨1573847, by rfl⟩ : syracuseStep 2098463 = 3147695) B3147695
theorem B3147047 : Blo 1397518 3147047 := bstep (se 1 (by rfl) ⟨2360285, by rfl⟩ : syracuseStep 3147047 = 4720571) B4720571
theorem B9078169 : Blo 1397518 9078169 := bstep (se 2 (by rfl) ⟨3404313, by rfl⟩ : syracuseStep 9078169 = 6808627) B6808627
theorem B1574311 : Blo 1397518 1574311 := bstep (se 1 (by rfl) ⟨1180733, by rfl⟩ : syracuseStep 1574311 = 2361467) B2361467
theorem B2098631 : Blo 1397518 2098631 := bstep (se 1 (by rfl) ⟨1573973, by rfl⟩ : syracuseStep 2098631 = 3147947) B3147947
theorem B2360927 : Blo 1397518 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B3147425 : Blo 1397518 3147425 := bstep (se 2 (by rfl) ⟨1180284, by rfl⟩ : syracuseStep 3147425 = 2360569) B2360569
theorem B5973689 : Blo 1397518 5973689 := bstep (se 2 (by rfl) ⟨2240133, by rfl⟩ : syracuseStep 5973689 = 4480267) B4480267
theorem B3540743 : Blo 1397518 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B2098985 : Blo 1397518 2098985 := bstep (se 2 (by rfl) ⟨787119, by rfl⟩ : syracuseStep 2098985 = 1574239) B1574239
theorem B2098991 : Blo 1397518 2098991 := bstep (se 1 (by rfl) ⟨1574243, by rfl⟩ : syracuseStep 2098991 = 3148487) B3148487
theorem B2361143 : Blo 1397518 2361143 := bstep (se 1 (by rfl) ⟨1770857, by rfl⟩ : syracuseStep 2361143 = 3541715) B3541715
theorem B3540793 : Blo 1397518 3540793 := bstep (se 2 (by rfl) ⟨1327797, by rfl⟩ : syracuseStep 3540793 = 2655595) B2655595
theorem B8963945 : Blo 1397518 8963945 := bstep (se 2 (by rfl) ⟨3361479, by rfl⟩ : syracuseStep 8963945 = 6722959) B6722959
theorem B8300393 : Blo 1397518 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B3360719 : Blo 1397518 3360719 := bstep (se 1 (by rfl) ⟨2520539, by rfl⟩ : syracuseStep 3360719 = 5041079) B5041079
theorem B3147785 : Blo 1397518 3147785 := bstep (se 2 (by rfl) ⟨1180419, by rfl⟩ : syracuseStep 3147785 = 2360839) B2360839
theorem B3541097 : Blo 1397518 3541097 := bstep (se 2 (by rfl) ⟨1327911, by rfl⟩ : syracuseStep 3541097 = 2655823) B2655823
theorem B3148199 : Blo 1397518 3148199 := bstep (se 1 (by rfl) ⟨2361149, by rfl⟩ : syracuseStep 3148199 = 4722299) B4722299
theorem B94448051 : Blo 1397518 94448051 := bstep (se 1 (by rfl) ⟨70836038, by rfl⟩ : syracuseStep 94448051 = 141672077) B141672077
theorem B3148307 : Blo 1397518 3148307 := bstep (se 1 (by rfl) ⟨2361230, by rfl⟩ : syracuseStep 3148307 = 4722461) B4722461
theorem B3148361 : Blo 1397518 3148361 := bstep (se 2 (by rfl) ⟨1180635, by rfl⟩ : syracuseStep 3148361 = 2361271) B2361271
theorem B3541583 : Blo 1397518 3541583 := bstep (se 1 (by rfl) ⟨2656187, by rfl⟩ : syracuseStep 3541583 = 5312375) B5312375
theorem B12749399 : Blo 1397518 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B4721327 : Blo 1397518 4721327 := bstep (se 1 (by rfl) ⟨3540995, by rfl⟩ : syracuseStep 4721327 = 7081991) B7081991
theorem B7080695 : Blo 1397518 7080695 := bstep (se 1 (by rfl) ⟨5310521, by rfl⟩ : syracuseStep 7080695 = 10621043) B10621043
theorem B5311403 : Blo 1397518 5311403 := bstep (se 1 (by rfl) ⟨3983552, by rfl⟩ : syracuseStep 5311403 = 7967105) B7967105
theorem B3148775 : Blo 1397518 3148775 := bstep (se 1 (by rfl) ⟨2361581, by rfl⟩ : syracuseStep 3148775 = 4723163) B4723163
theorem B4721651 : Blo 1397518 4721651 := bstep (se 1 (by rfl) ⟨3541238, by rfl⟩ : syracuseStep 4721651 = 7082477) B7082477
theorem B30665807 : Blo 1397518 30665807 := bstep (se 1 (by rfl) ⟨22999355, by rfl⟩ : syracuseStep 30665807 = 45998711) B45998711
theorem B3542231 : Blo 1397518 3542231 := bstep (se 1 (by rfl) ⟨2656673, by rfl⟩ : syracuseStep 3542231 = 5313347) B5313347
theorem B7081181 : Blo 1397518 7081181 := bstep (se 3 (by rfl) ⟨1327721, by rfl⟩ : syracuseStep 7081181 = 2655443) B2655443
theorem B5975363 : Blo 1397518 5975363 := bstep (se 1 (by rfl) ⟨4481522, by rfl⟩ : syracuseStep 5975363 = 8963045) B8963045
theorem B8965505 : Blo 1397518 8965505 := bstep (se 2 (by rfl) ⟨3362064, by rfl⟩ : syracuseStep 8965505 = 6724129) B6724129
theorem B3190279 : Blo 1397518 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B4722191 : Blo 1397518 4722191 := bstep (se 1 (by rfl) ⟨3541643, by rfl⟩ : syracuseStep 4722191 = 7083287) B7083287
theorem B3985159 : Blo 1397518 3985159 := bstep (se 1 (by rfl) ⟨2988869, by rfl⟩ : syracuseStep 3985159 = 5977739) B5977739
theorem B3985193 : Blo 1397518 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B11947823 : Blo 1397518 11947823 := bstep (se 1 (by rfl) ⟨8960867, by rfl⟩ : syracuseStep 11947823 = 17921735) B17921735
theorem B13439033 : Blo 1397518 13439033 := bstep (se 2 (by rfl) ⟨5039637, by rfl⟩ : syracuseStep 13439033 = 10079275) B10079275
theorem B76591169 : Blo 1397518 76591169 := bstep (se 2 (by rfl) ⟨28721688, by rfl⟩ : syracuseStep 76591169 = 57443377) B57443377
theorem B12103937 : Blo 1397518 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B5673289 : Blo 1397518 5673289 := bstep (se 2 (by rfl) ⟨2127483, by rfl⟩ : syracuseStep 5673289 = 4254967) B4254967
theorem B9204187 : Blo 1397518 9204187 := bstep (se 1 (by rfl) ⟨6903140, by rfl⟩ : syracuseStep 9204187 = 13806281) B13806281
theorem B10613267 : Blo 1397518 10613267 := bstep (se 1 (by rfl) ⟨7959950, by rfl⟩ : syracuseStep 10613267 = 15919901) B15919901
theorem B4723271 : Blo 1397518 4723271 := bstep (se 1 (by rfl) ⟨3542453, by rfl⟩ : syracuseStep 4723271 = 7084907) B7084907
theorem B60502625 : Blo 1397518 60502625 := bstep (se 2 (by rfl) ⟨22688484, by rfl⟩ : syracuseStep 60502625 = 45376969) B45376969
theorem B11940473 : Blo 1397518 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B1397551 : Blo 1397518 1397551 := bstep (se 1 (by rfl) ⟨1048163, by rfl⟩ : syracuseStep 1397551 = 2096327) B2096327
theorem B1397659 : Blo 1397518 1397659 := bstep (se 1 (by rfl) ⟨1048244, by rfl⟩ : syracuseStep 1397659 = 2096489) B2096489
theorem B46011341 : Blo 1397518 46011341 := bstep (se 3 (by rfl) ⟨8627126, by rfl⟩ : syracuseStep 46011341 = 17254253) B17254253
theorem B1397711 : Blo 1397518 1397711 := bstep (se 1 (by rfl) ⟨1048283, by rfl⟩ : syracuseStep 1397711 = 2096567) B2096567
theorem B1397735 : Blo 1397518 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B3781847 : Blo 1397518 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B1398047 : Blo 1397518 1398047 := bstep (se 1 (by rfl) ⟨1048535, by rfl⟩ : syracuseStep 1398047 = 2097071) B2097071
theorem B1398107 : Blo 1397518 1398107 := bstep (se 1 (by rfl) ⟨1048580, by rfl⟩ : syracuseStep 1398107 = 2097161) B2097161
theorem B7558505 : Blo 1397518 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B1398127 : Blo 1397518 1398127 := bstep (se 1 (by rfl) ⟨1048595, by rfl⟩ : syracuseStep 1398127 = 2097191) B2097191
theorem B13432189 : Blo 1397518 13432189 := bstep (se 3 (by rfl) ⟨2518535, by rfl⟩ : syracuseStep 13432189 = 5037071) B5037071
theorem B1398183 : Blo 1397518 1398183 := bstep (se 1 (by rfl) ⟨1048637, by rfl⟩ : syracuseStep 1398183 = 2097275) B2097275
theorem B1889735 : Blo 1397518 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B1398267 : Blo 1397518 1398267 := bstep (se 1 (by rfl) ⟨1048700, by rfl⟩ : syracuseStep 1398267 = 2097401) B2097401
theorem B30242315 : Blo 1397518 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B10622501 : Blo 1397518 10622501 := bstep (se 4 (by rfl) ⟨995859, by rfl⟩ : syracuseStep 10622501 = 1991719) B1991719
theorem B5379641 : Blo 1397518 5379641 := bstep (se 2 (by rfl) ⟨2017365, by rfl⟩ : syracuseStep 5379641 = 4034731) B4034731
theorem B1398335 : Blo 1397518 1398335 := bstep (se 1 (by rfl) ⟨1048751, by rfl⟩ : syracuseStep 1398335 = 2097503) B2097503
theorem B1398343 : Blo 1397518 1398343 := bstep (se 1 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 1398343 = 2097515) B2097515
theorem B122664593 : Blo 1397518 122664593 := bstep (se 2 (by rfl) ⟨45999222, by rfl⟩ : syracuseStep 122664593 = 91998445) B91998445
theorem B1398495 : Blo 1397518 1398495 := bstep (se 1 (by rfl) ⟨1048871, by rfl⟩ : syracuseStep 1398495 = 2097743) B2097743
theorem B1398575 : Blo 1397518 1398575 := bstep (se 1 (by rfl) ⟨1048931, by rfl⟩ : syracuseStep 1398575 = 2097863) B2097863
theorem B5977961 : Blo 1397518 5977961 := bstep (se 2 (by rfl) ⟨2241735, by rfl⟩ : syracuseStep 5977961 = 4483471) B4483471
theorem B35862425 : Blo 1397518 35862425 := bstep (se 2 (by rfl) ⟨13448409, by rfl⟩ : syracuseStep 35862425 = 26896819) B26896819
theorem B1398683 : Blo 1397518 1398683 := bstep (se 1 (by rfl) ⟨1049012, by rfl⟩ : syracuseStep 1398683 = 2098025) B2098025
theorem B1398735 : Blo 1397518 1398735 := bstep (se 1 (by rfl) ⟨1049051, by rfl⟩ : syracuseStep 1398735 = 2098103) B2098103
theorem B1398759 : Blo 1397518 1398759 := bstep (se 1 (by rfl) ⟨1049069, by rfl⟩ : syracuseStep 1398759 = 2098139) B2098139
theorem B26875907 : Blo 1397518 26875907 := bstep (se 1 (by rfl) ⟨20156930, by rfl⟩ : syracuseStep 26875907 = 40313861) B40313861
theorem B6379715 : Blo 1397518 6379715 := bstep (se 1 (by rfl) ⟨4784786, by rfl⟩ : syracuseStep 6379715 = 9569573) B9569573
theorem B1399071 : Blo 1397518 1399071 := bstep (se 1 (by rfl) ⟨1049303, by rfl⟩ : syracuseStep 1399071 = 2098607) B2098607
theorem B1399131 : Blo 1397518 1399131 := bstep (se 1 (by rfl) ⟨1049348, by rfl⟩ : syracuseStep 1399131 = 2098697) B2098697
theorem B1399151 : Blo 1397518 1399151 := bstep (se 1 (by rfl) ⟨1049363, by rfl⟩ : syracuseStep 1399151 = 2098727) B2098727
theorem B8960381 : Blo 1397518 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B1399207 : Blo 1397518 1399207 := bstep (se 1 (by rfl) ⟨1049405, by rfl⟩ : syracuseStep 1399207 = 2098811) B2098811
theorem B1399291 : Blo 1397518 1399291 := bstep (se 1 (by rfl) ⟨1049468, by rfl⟩ : syracuseStep 1399291 = 2098937) B2098937
theorem B6715943 : Blo 1397518 6715943 := bstep (se 1 (by rfl) ⟨5036957, by rfl⟩ : syracuseStep 6715943 = 10073915) B10073915
theorem B7084583 : Blo 1397518 7084583 := bstep (se 1 (by rfl) ⟨5313437, by rfl⟩ : syracuseStep 7084583 = 10626875) B10626875
theorem B1399359 : Blo 1397518 1399359 := bstep (se 1 (by rfl) ⟨1049519, by rfl⟩ : syracuseStep 1399359 = 2099039) B2099039
theorem B1399367 : Blo 1397518 1399367 := bstep (se 1 (by rfl) ⟨1049525, by rfl⟩ : syracuseStep 1399367 = 2099051) B2099051
theorem B4717331 : Blo 1397518 4717331 := bstep (se 1 (by rfl) ⟨3537998, by rfl⟩ : syracuseStep 4717331 = 7075997) B7075997
theorem B3144527 : Blo 1397518 3144527 := bstep (se 1 (by rfl) ⟨2358395, by rfl⟩ : syracuseStep 3144527 = 4716791) B4716791
theorem B13622201 : Blo 1397518 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B3144743 : Blo 1397518 3144743 := bstep (se 1 (by rfl) ⟨2358557, by rfl⟩ : syracuseStep 3144743 = 4717115) B4717115
theorem B15924275 : Blo 1397518 15924275 := bstep (se 1 (by rfl) ⟨11943206, by rfl⟩ : syracuseStep 15924275 = 23886413) B23886413
theorem B5307515 : Blo 1397518 5307515 := bstep (se 1 (by rfl) ⟨3980636, by rfl⟩ : syracuseStep 5307515 = 7961273) B7961273
theorem B3980477 : Blo 1397518 3980477 := bstep (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) B1492679
theorem B1989851 : Blo 1397518 1989851 := bstep (se 1 (by rfl) ⟨1492388, by rfl⟩ : syracuseStep 1989851 = 2984777) B2984777
theorem B3144923 : Blo 1397518 3144923 := bstep (se 1 (by rfl) ⟨2358692, by rfl⟩ : syracuseStep 3144923 = 4717385) B4717385
theorem B7077131 : Blo 1397518 7077131 := bstep (se 1 (by rfl) ⟨5307848, by rfl⟩ : syracuseStep 7077131 = 10615697) B10615697
theorem B2096423 : Blo 1397518 2096423 := bstep (se 1 (by rfl) ⟨1572317, by rfl⟩ : syracuseStep 2096423 = 3144635) B3144635
theorem B2096507 : Blo 1397518 2096507 := bstep (se 1 (by rfl) ⟨1572380, by rfl⟩ : syracuseStep 2096507 = 3144761) B3144761
theorem B3538313 : Blo 1397518 3538313 := bstep (se 2 (by rfl) ⟨1326867, by rfl⟩ : syracuseStep 3538313 = 2653735) B2653735
theorem B3145121 : Blo 1397518 3145121 := bstep (se 2 (by rfl) ⟨1179420, by rfl⟩ : syracuseStep 3145121 = 2358841) B2358841
theorem B3538363 : Blo 1397518 3538363 := bstep (se 1 (by rfl) ⟨2653772, by rfl⟩ : syracuseStep 3538363 = 5307545) B5307545
theorem B1572295 : Blo 1397518 1572295 := bstep (se 1 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 1572295 = 2358443) B2358443
theorem B2096633 : Blo 1397518 2096633 := bstep (se 2 (by rfl) ⟨786237, by rfl⟩ : syracuseStep 2096633 = 1572475) B1572475
theorem B11943449 : Blo 1397518 11943449 := bstep (se 2 (by rfl) ⟨4478793, by rfl⟩ : syracuseStep 11943449 = 8957587) B8957587
theorem B2834003 : Blo 1397518 2834003 := bstep (se 1 (by rfl) ⟨2125502, by rfl⟩ : syracuseStep 2834003 = 4251005) B4251005
theorem B2096735 : Blo 1397518 2096735 := bstep (se 1 (by rfl) ⟨1572551, by rfl⟩ : syracuseStep 2096735 = 3145103) B3145103
theorem B15933023 : Blo 1397518 15933023 := bstep (se 1 (by rfl) ⟨11949767, by rfl⟩ : syracuseStep 15933023 = 23899535) B23899535
theorem B4718195 : Blo 1397518 4718195 := bstep (se 1 (by rfl) ⟨3538646, by rfl⟩ : syracuseStep 4718195 = 7077293) B7077293
theorem B122650253 : Blo 1397518 122650253 := bstep (se 3 (by rfl) ⟨22996922, by rfl⟩ : syracuseStep 122650253 = 45993845) B45993845
theorem B20160161 : Blo 1397518 20160161 := bstep (se 2 (by rfl) ⟨7560060, by rfl⟩ : syracuseStep 20160161 = 15120121) B15120121
theorem B3538667 : Blo 1397518 3538667 := bstep (se 1 (by rfl) ⟨2654000, by rfl⟩ : syracuseStep 3538667 = 5308001) B5308001
theorem B1572655 : Blo 1397518 1572655 := bstep (se 1 (by rfl) ⟨1179491, by rfl⟩ : syracuseStep 1572655 = 2358983) B2358983
theorem B6381359 : Blo 1397518 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B2096951 : Blo 1397518 2096951 := bstep (se 1 (by rfl) ⟨1572713, by rfl⟩ : syracuseStep 2096951 = 3145427) B3145427
theorem B2424631 : Blo 1397518 2424631 := bstep (se 1 (by rfl) ⟨1818473, by rfl⟩ : syracuseStep 2424631 = 3636947) B3636947
theorem B4718465 : Blo 1397518 4718465 := bstep (se 2 (by rfl) ⟨1769424, by rfl⟩ : syracuseStep 4718465 = 3538849) B3538849
theorem B1572763 : Blo 1397518 1572763 := bstep (se 1 (by rfl) ⟨1179572, by rfl⟩ : syracuseStep 1572763 = 2359145) B2359145
theorem B3145679 : Blo 1397518 3145679 := bstep (se 1 (by rfl) ⟨2359259, by rfl⟩ : syracuseStep 3145679 = 4718519) B4718519
theorem B51060779 : Blo 1397518 51060779 := bstep (se 1 (by rfl) ⟨38295584, by rfl⟩ : syracuseStep 51060779 = 76591169) B76591169
theorem B8069291 : Blo 1397518 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B2097371 : Blo 1397518 2097371 := bstep (se 1 (by rfl) ⟨1573028, by rfl⟩ : syracuseStep 2097371 = 3146057) B3146057
theorem B2097383 : Blo 1397518 2097383 := bstep (se 1 (by rfl) ⟨1573037, by rfl⟩ : syracuseStep 2097383 = 3146075) B3146075
theorem B2097545 : Blo 1397518 2097545 := bstep (se 2 (by rfl) ⟨786579, by rfl⟩ : syracuseStep 2097545 = 1573159) B1573159
theorem B17007023 : Blo 1397518 17007023 := bstep (se 1 (by rfl) ⟨12755267, by rfl⟩ : syracuseStep 17007023 = 25510535) B25510535
theorem B3146183 : Blo 1397518 3146183 := bstep (se 1 (by rfl) ⟨2359637, by rfl⟩ : syracuseStep 3146183 = 4719275) B4719275
theorem B2359759 : Blo 1397518 2359759 := bstep (se 1 (by rfl) ⟨1769819, by rfl⟩ : syracuseStep 2359759 = 3539639) B3539639
theorem B2097641 : Blo 1397518 2097641 := bstep (se 2 (by rfl) ⟨786615, by rfl⟩ : syracuseStep 2097641 = 1573231) B1573231
theorem B10084925 : Blo 1397518 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B4719167 : Blo 1397518 4719167 := bstep (se 1 (by rfl) ⟨3539375, by rfl⟩ : syracuseStep 4719167 = 7078751) B7078751
theorem B2097767 : Blo 1397518 2097767 := bstep (se 1 (by rfl) ⟨1573325, by rfl⟩ : syracuseStep 2097767 = 3146651) B3146651
theorem B12272249 : Blo 1397518 12272249 := bstep (se 2 (by rfl) ⟨4602093, by rfl⟩ : syracuseStep 12272249 = 9204187) B9204187
theorem B12763811 : Blo 1397518 12763811 := bstep (se 1 (by rfl) ⟨9572858, by rfl⟩ : syracuseStep 12763811 = 19145717) B19145717
theorem B2097899 : Blo 1397518 2097899 := bstep (se 1 (by rfl) ⟨1573424, by rfl⟩ : syracuseStep 2097899 = 3146849) B3146849
theorem B2097929 : Blo 1397518 2097929 := bstep (se 2 (by rfl) ⟨786723, by rfl⟩ : syracuseStep 2097929 = 1573447) B1573447
theorem B3146543 : Blo 1397518 3146543 := bstep (se 1 (by rfl) ⟨2359907, by rfl⟩ : syracuseStep 3146543 = 4719815) B4719815
theorem B2098031 : Blo 1397518 2098031 := bstep (se 1 (by rfl) ⟨1573523, by rfl⟩ : syracuseStep 2098031 = 3147047) B3147047
theorem B5039003 : Blo 1397518 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B20161543 : Blo 1397518 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B1573951 : Blo 1397518 1573951 := bstep (se 1 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 1573951 = 2360927) B2360927
theorem B2655337 : Blo 1397518 2655337 := bstep (se 2 (by rfl) ⟨995751, by rfl⟩ : syracuseStep 2655337 = 1991503) B1991503
theorem B2098283 : Blo 1397518 2098283 := bstep (se 1 (by rfl) ⟨1573712, by rfl⟩ : syracuseStep 2098283 = 3147425) B3147425
theorem B3982459 : Blo 1397518 3982459 := bstep (se 1 (by rfl) ⟨2986844, by rfl⟩ : syracuseStep 3982459 = 5973689) B5973689
theorem B2360495 : Blo 1397518 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B5039293 : Blo 1397518 5039293 := bstep (se 3 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 5039293 = 1889735) B1889735
theorem B1574095 : Blo 1397518 1574095 := bstep (se 1 (by rfl) ⟨1180571, by rfl⟩ : syracuseStep 1574095 = 2361143) B2361143
theorem B17917271 : Blo 1397518 17917271 := bstep (se 1 (by rfl) ⟨13437953, by rfl⟩ : syracuseStep 17917271 = 26875907) B26875907
theorem B2098523 : Blo 1397518 2098523 := bstep (se 1 (by rfl) ⟨1573892, by rfl⟩ : syracuseStep 2098523 = 3147785) B3147785
theorem B2360731 : Blo 1397518 2360731 := bstep (se 1 (by rfl) ⟨1770548, by rfl⟩ : syracuseStep 2360731 = 3541097) B3541097
theorem B4253143 : Blo 1397518 4253143 := bstep (se 1 (by rfl) ⟨3189857, by rfl⟩ : syracuseStep 4253143 = 6379715) B6379715
theorem B5973587 : Blo 1397518 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B2098799 : Blo 1397518 2098799 := bstep (se 1 (by rfl) ⟨1574099, by rfl⟩ : syracuseStep 2098799 = 3148199) B3148199
theorem B62965367 : Blo 1397518 62965367 := bstep (se 1 (by rfl) ⟨47224025, by rfl⟩ : syracuseStep 62965367 = 94448051) B94448051
theorem B2098871 : Blo 1397518 2098871 := bstep (se 1 (by rfl) ⟨1574153, by rfl⟩ : syracuseStep 2098871 = 3148307) B3148307
theorem B2098907 : Blo 1397518 2098907 := bstep (se 1 (by rfl) ⟨1574180, by rfl⟩ : syracuseStep 2098907 = 3148361) B3148361
theorem B2361055 : Blo 1397518 2361055 := bstep (se 1 (by rfl) ⟨1770791, by rfl⟩ : syracuseStep 2361055 = 3541583) B3541583
theorem B3147551 : Blo 1397518 3147551 := bstep (se 1 (by rfl) ⟨2360663, by rfl⟩ : syracuseStep 3147551 = 4721327) B4721327
theorem B4720463 : Blo 1397518 4720463 := bstep (se 1 (by rfl) ⟨3540347, by rfl⟩ : syracuseStep 4720463 = 7080695) B7080695
theorem B17909585 : Blo 1397518 17909585 := bstep (se 2 (by rfl) ⟨6716094, by rfl⟩ : syracuseStep 17909585 = 13432189) B13432189
theorem B2099081 : Blo 1397518 2099081 := bstep (se 2 (by rfl) ⟨787155, by rfl⟩ : syracuseStep 2099081 = 1574311) B1574311
theorem B3540935 : Blo 1397518 3540935 := bstep (se 1 (by rfl) ⟨2655701, by rfl⟩ : syracuseStep 3540935 = 5311403) B5311403
theorem B2099183 : Blo 1397518 2099183 := bstep (se 1 (by rfl) ⟨1574387, by rfl⟩ : syracuseStep 2099183 = 3148775) B3148775
theorem B3147767 : Blo 1397518 3147767 := bstep (se 1 (by rfl) ⟨2360825, by rfl⟩ : syracuseStep 3147767 = 4721651) B4721651
theorem B4253705 : Blo 1397518 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B2361487 : Blo 1397518 2361487 := bstep (se 1 (by rfl) ⟨1771115, by rfl⟩ : syracuseStep 2361487 = 3542231) B3542231
theorem B4720787 : Blo 1397518 4720787 := bstep (se 1 (by rfl) ⟨3540590, by rfl⟩ : syracuseStep 4720787 = 7081181) B7081181
theorem B3983575 : Blo 1397518 3983575 := bstep (se 1 (by rfl) ⟨2987681, by rfl⟩ : syracuseStep 3983575 = 5975363) B5975363
theorem B3148127 : Blo 1397518 3148127 := bstep (se 1 (by rfl) ⟨2361095, by rfl⟩ : syracuseStep 3148127 = 4722191) B4722191
theorem B4721057 : Blo 1397518 4721057 := bstep (se 2 (by rfl) ⟨1770396, by rfl⟩ : syracuseStep 4721057 = 3540793) B3540793
theorem B81766835 : Blo 1397518 81766835 := bstep (se 1 (by rfl) ⟨61325126, by rfl⟩ : syracuseStep 81766835 = 122650253) B122650253
theorem B2656795 : Blo 1397518 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B7965215 : Blo 1397518 7965215 := bstep (se 1 (by rfl) ⟨5973911, by rfl⟩ : syracuseStep 7965215 = 11947823) B11947823
theorem B4254239 : Blo 1397518 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B3148847 : Blo 1397518 3148847 := bstep (se 1 (by rfl) ⟨2361635, by rfl⟩ : syracuseStep 3148847 = 4723271) B4723271
theorem B7564385 : Blo 1397518 7564385 := bstep (se 2 (by rfl) ⟨2836644, by rfl⟩ : syracuseStep 7564385 = 5673289) B5673289
theorem B30674227 : Blo 1397518 30674227 := bstep (se 1 (by rfl) ⟨23005670, by rfl⟩ : syracuseStep 30674227 = 46011341) B46011341
theorem B7081667 : Blo 1397518 7081667 := bstep (se 1 (by rfl) ⟨5311250, by rfl⟩ : syracuseStep 7081667 = 10622501) B10622501
theorem B81776395 : Blo 1397518 81776395 := bstep (se 1 (by rfl) ⟨61332296, by rfl⟩ : syracuseStep 81776395 = 122664593) B122664593
theorem B34025345 : Blo 1397518 34025345 := bstep (se 2 (by rfl) ⟨12759504, by rfl⟩ : syracuseStep 34025345 = 25519009) B25519009
theorem B5975963 : Blo 1397518 5975963 := bstep (se 1 (by rfl) ⟨4481972, by rfl⟩ : syracuseStep 5975963 = 8963945) B8963945
theorem B5533595 : Blo 1397518 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B3985307 : Blo 1397518 3985307 := bstep (se 1 (by rfl) ⟨2988980, by rfl⟩ : syracuseStep 3985307 = 5977961) B5977961
theorem B23908283 : Blo 1397518 23908283 := bstep (se 1 (by rfl) ⟨17931212, by rfl⟩ : syracuseStep 23908283 = 35862425) B35862425
theorem B2240479 : Blo 1397518 2240479 := bstep (se 1 (by rfl) ⟨1680359, by rfl⟩ : syracuseStep 2240479 = 3360719) B3360719
theorem B4477295 : Blo 1397518 4477295 := bstep (se 1 (by rfl) ⟨3357971, by rfl⟩ : syracuseStep 4477295 = 6715943) B6715943
theorem B4723055 : Blo 1397518 4723055 := bstep (se 1 (by rfl) ⟨3542291, by rfl⟩ : syracuseStep 4723055 = 7084583) B7084583
theorem B8499599 : Blo 1397518 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B12104225 : Blo 1397518 12104225 := bstep (se 2 (by rfl) ⟨4539084, by rfl⟩ : syracuseStep 12104225 = 9078169) B9078169
theorem B9081467 : Blo 1397518 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B20443871 : Blo 1397518 20443871 := bstep (se 1 (by rfl) ⟨15332903, by rfl⟩ : syracuseStep 20443871 = 30665807) B30665807
theorem B1397615 : Blo 1397518 1397615 := bstep (se 1 (by rfl) ⟨1048211, by rfl⟩ : syracuseStep 1397615 = 2096423) B2096423
theorem B1397671 : Blo 1397518 1397671 := bstep (se 1 (by rfl) ⟨1048253, by rfl⟩ : syracuseStep 1397671 = 2096507) B2096507
theorem B5977003 : Blo 1397518 5977003 := bstep (se 1 (by rfl) ⟨4482752, by rfl⟩ : syracuseStep 5977003 = 8965505) B8965505
theorem B1397755 : Blo 1397518 1397755 := bstep (se 1 (by rfl) ⟨1048316, by rfl⟩ : syracuseStep 1397755 = 2096633) B2096633
theorem B5313545 : Blo 1397518 5313545 := bstep (se 2 (by rfl) ⟨1992579, by rfl⟩ : syracuseStep 5313545 = 3985159) B3985159
theorem B1889335 : Blo 1397518 1889335 := bstep (se 1 (by rfl) ⟨1417001, by rfl⟩ : syracuseStep 1889335 = 2834003) B2834003
theorem B1397823 : Blo 1397518 1397823 := bstep (se 1 (by rfl) ⟨1048367, by rfl⟩ : syracuseStep 1397823 = 2096735) B2096735
theorem B10622015 : Blo 1397518 10622015 := bstep (se 1 (by rfl) ⟨7966511, by rfl⟩ : syracuseStep 10622015 = 15933023) B15933023
theorem B3232841 : Blo 1397518 3232841 := bstep (se 2 (by rfl) ⟨1212315, by rfl⟩ : syracuseStep 3232841 = 2424631) B2424631
theorem B13440107 : Blo 1397518 13440107 := bstep (se 1 (by rfl) ⟨10080080, by rfl⟩ : syracuseStep 13440107 = 20160161) B20160161
theorem B1397967 : Blo 1397518 1397967 := bstep (se 1 (by rfl) ⟨1048475, by rfl⟩ : syracuseStep 1397967 = 2096951) B2096951
theorem B8959355 : Blo 1397518 8959355 := bstep (se 1 (by rfl) ⟨6719516, by rfl⟩ : syracuseStep 8959355 = 13439033) B13439033
theorem B1398171 : Blo 1397518 1398171 := bstep (se 1 (by rfl) ⟨1048628, by rfl⟩ : syracuseStep 1398171 = 2097257) B2097257
theorem B1398383 : Blo 1397518 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B1398439 : Blo 1397518 1398439 := bstep (se 1 (by rfl) ⟨1048829, by rfl⟩ : syracuseStep 1398439 = 2097659) B2097659
theorem B7075511 : Blo 1397518 7075511 := bstep (se 1 (by rfl) ⟨5306633, by rfl⟩ : syracuseStep 7075511 = 10613267) B10613267
theorem B1595099 : Blo 1397518 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B40335083 : Blo 1397518 40335083 := bstep (se 1 (by rfl) ⟨30251312, by rfl⟩ : syracuseStep 40335083 = 60502625) B60502625
theorem B17913581 : Blo 1397518 17913581 := bstep (se 3 (by rfl) ⟨3358796, by rfl⟩ : syracuseStep 17913581 = 6717593) B6717593
theorem B7960315 : Blo 1397518 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B1398523 : Blo 1397518 1398523 := bstep (se 1 (by rfl) ⟨1048892, by rfl⟩ : syracuseStep 1398523 = 2097785) B2097785
theorem B1398559 : Blo 1397518 1398559 := bstep (se 1 (by rfl) ⟨1048919, by rfl⟩ : syracuseStep 1398559 = 2097839) B2097839
theorem B294508331 : Blo 1397518 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B1398591 : Blo 1397518 1398591 := bstep (se 1 (by rfl) ⟨1048943, by rfl⟩ : syracuseStep 1398591 = 2097887) B2097887
theorem B5306269 : Blo 1397518 5306269 := bstep (se 3 (by rfl) ⟨994925, by rfl⟩ : syracuseStep 5306269 = 1989851) B1989851
theorem B4478935 : Blo 1397518 4478935 := bstep (se 1 (by rfl) ⟨3359201, by rfl⟩ : syracuseStep 4478935 = 6718403) B6718403
theorem B1398767 : Blo 1397518 1398767 := bstep (se 1 (by rfl) ⟨1049075, by rfl⟩ : syracuseStep 1398767 = 2098151) B2098151
theorem B1398939 : Blo 1397518 1398939 := bstep (se 1 (by rfl) ⟨1049204, by rfl⟩ : syracuseStep 1398939 = 2098409) B2098409
theorem B1398975 : Blo 1397518 1398975 := bstep (se 1 (by rfl) ⟨1049231, by rfl⟩ : syracuseStep 1398975 = 2098463) B2098463
theorem B1399087 : Blo 1397518 1399087 := bstep (se 1 (by rfl) ⟨1049315, by rfl⟩ : syracuseStep 1399087 = 2098631) B2098631
theorem B3586427 : Blo 1397518 3586427 := bstep (se 1 (by rfl) ⟨2689820, by rfl⟩ : syracuseStep 3586427 = 5379641) B5379641
theorem B4479421 : Blo 1397518 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B1399323 : Blo 1397518 1399323 := bstep (se 1 (by rfl) ⟨1049492, by rfl⟩ : syracuseStep 1399323 = 2098985) B2098985
theorem B1399327 : Blo 1397518 1399327 := bstep (se 1 (by rfl) ⟨1049495, by rfl⟩ : syracuseStep 1399327 = 2098991) B2098991
theorem B3144887 : Blo 1397518 3144887 := bstep (se 1 (by rfl) ⟨2358665, by rfl⟩ : syracuseStep 3144887 = 4717331) B4717331
theorem B2096351 : Blo 1397518 2096351 := bstep (se 1 (by rfl) ⟨1572263, by rfl⟩ : syracuseStep 2096351 = 3144527) B3144527
theorem B4717817 : Blo 1397518 4717817 := bstep (se 2 (by rfl) ⟨1769181, by rfl⟩ : syracuseStep 4717817 = 3538363) B3538363
theorem B2096393 : Blo 1397518 2096393 := bstep (se 2 (by rfl) ⟨786147, by rfl⟩ : syracuseStep 2096393 = 1572295) B1572295
theorem B2096495 : Blo 1397518 2096495 := bstep (se 1 (by rfl) ⟨1572371, by rfl⟩ : syracuseStep 2096495 = 3144743) B3144743
theorem B10616183 : Blo 1397518 10616183 := bstep (se 1 (by rfl) ⟨7962137, by rfl⟩ : syracuseStep 10616183 = 15924275) B15924275
theorem B3538343 : Blo 1397518 3538343 := bstep (se 1 (by rfl) ⟨2653757, by rfl⟩ : syracuseStep 3538343 = 5307515) B5307515
theorem B2653651 : Blo 1397518 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B2096615 : Blo 1397518 2096615 := bstep (se 1 (by rfl) ⟨1572461, by rfl⟩ : syracuseStep 2096615 = 3144923) B3144923
theorem B4718087 : Blo 1397518 4718087 := bstep (se 1 (by rfl) ⟨3538565, by rfl⟩ : syracuseStep 4718087 = 7077131) B7077131
theorem B2358875 : Blo 1397518 2358875 := bstep (se 1 (by rfl) ⟨1769156, by rfl⟩ : syracuseStep 2358875 = 3538313) B3538313
theorem B2096747 : Blo 1397518 2096747 := bstep (se 1 (by rfl) ⟨1572560, by rfl⟩ : syracuseStep 2096747 = 3145121) B3145121
theorem B7962299 : Blo 1397518 7962299 := bstep (se 1 (by rfl) ⟨5971724, by rfl⟩ : syracuseStep 7962299 = 11943449) B11943449
theorem B2096873 : Blo 1397518 2096873 := bstep (se 2 (by rfl) ⟨786327, by rfl⟩ : syracuseStep 2096873 = 1572655) B1572655
theorem B3145463 : Blo 1397518 3145463 := bstep (se 1 (by rfl) ⟨2359097, by rfl⟩ : syracuseStep 3145463 = 4718195) B4718195
theorem B2359111 : Blo 1397518 2359111 := bstep (se 1 (by rfl) ⟨1769333, by rfl⟩ : syracuseStep 2359111 = 3538667) B3538667
theorem B2097017 : Blo 1397518 2097017 := bstep (se 2 (by rfl) ⟨786381, by rfl⟩ : syracuseStep 2097017 = 1572763) B1572763
theorem B3145643 : Blo 1397518 3145643 := bstep (se 1 (by rfl) ⟨2359232, by rfl⟩ : syracuseStep 3145643 = 4718465) B4718465
theorem B2097119 : Blo 1397518 2097119 := bstep (se 1 (by rfl) ⟨1572839, by rfl⟩ : syracuseStep 2097119 = 3145679) B3145679
theorem B2097455 : Blo 1397518 2097455 := bstep (se 1 (by rfl) ⟨1573091, by rfl⟩ : syracuseStep 2097455 = 3146183) B3146183
theorem B8069483 : Blo 1397518 8069483 := bstep (se 1 (by rfl) ⟨6052112, by rfl⟩ : syracuseStep 8069483 = 12104225) B12104225
theorem B3146111 : Blo 1397518 3146111 := bstep (se 1 (by rfl) ⟨2359583, by rfl⟩ : syracuseStep 3146111 = 4719167) B4719167
theorem B6054311 : Blo 1397518 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B2097695 : Blo 1397518 2097695 := bstep (se 1 (by rfl) ⟨1573271, by rfl⟩ : syracuseStep 2097695 = 3146543) B3146543
theorem B5972561 : Blo 1397518 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B3359335 : Blo 1397518 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B3146345 : Blo 1397518 3146345 := bstep (se 2 (by rfl) ⟨1179879, by rfl⟩ : syracuseStep 3146345 = 2359759) B2359759
theorem B1573663 : Blo 1397518 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B11944847 : Blo 1397518 11944847 := bstep (se 1 (by rfl) ⟨8958635, by rfl⟩ : syracuseStep 11944847 = 17917271) B17917271
theorem B5972903 : Blo 1397518 5972903 := bstep (se 1 (by rfl) ⟨4479677, by rfl⟩ : syracuseStep 5972903 = 8959355) B8959355
theorem B3982391 : Blo 1397518 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B41976911 : Blo 1397518 41976911 := bstep (se 1 (by rfl) ⟨31482683, by rfl⟩ : syracuseStep 41976911 = 62965367) B62965367
theorem B45352061 : Blo 1397518 45352061 := bstep (se 3 (by rfl) ⟨8503511, by rfl⟩ : syracuseStep 45352061 = 17007023) B17007023
theorem B2098367 : Blo 1397518 2098367 := bstep (se 1 (by rfl) ⟨1573775, by rfl⟩ : syracuseStep 2098367 = 3147551) B3147551
theorem B196338887 : Blo 1397518 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B3146975 : Blo 1397518 3146975 := bstep (se 1 (by rfl) ⟨2360231, by rfl⟩ : syracuseStep 3146975 = 4720463) B4720463
theorem B2360623 : Blo 1397518 2360623 := bstep (se 1 (by rfl) ⟨1770467, by rfl⟩ : syracuseStep 2360623 = 3540935) B3540935
theorem B2098511 : Blo 1397518 2098511 := bstep (se 1 (by rfl) ⟨1573883, by rfl⟩ : syracuseStep 2098511 = 3147767) B3147767
theorem B2835803 : Blo 1397518 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B2098601 : Blo 1397518 2098601 := bstep (se 2 (by rfl) ⟨786975, by rfl⟩ : syracuseStep 2098601 = 1573951) B1573951
theorem B3147191 : Blo 1397518 3147191 := bstep (se 1 (by rfl) ⟨2360393, by rfl⟩ : syracuseStep 3147191 = 4720787) B4720787
theorem B3540449 : Blo 1397518 3540449 := bstep (se 2 (by rfl) ⟨1327668, by rfl⟩ : syracuseStep 3540449 = 2655337) B2655337
theorem B5309945 : Blo 1397518 5309945 := bstep (se 2 (by rfl) ⟨1991229, by rfl⟩ : syracuseStep 5309945 = 3982459) B3982459
theorem B2098751 : Blo 1397518 2098751 := bstep (se 1 (by rfl) ⟨1574063, by rfl⟩ : syracuseStep 2098751 = 3148127) B3148127
theorem B6719057 : Blo 1397518 6719057 := bstep (se 2 (by rfl) ⟨2519646, by rfl⟩ : syracuseStep 6719057 = 5039293) B5039293
theorem B2098793 : Blo 1397518 2098793 := bstep (se 2 (by rfl) ⟨787047, by rfl⟩ : syracuseStep 2098793 = 1574095) B1574095
theorem B3147371 : Blo 1397518 3147371 := bstep (se 1 (by rfl) ⟨2360528, by rfl⟩ : syracuseStep 3147371 = 4721057) B4721057
theorem B54511223 : Blo 1397518 54511223 := bstep (se 1 (by rfl) ⟨40883417, by rfl⟩ : syracuseStep 54511223 = 81766835) B81766835
theorem B5310143 : Blo 1397518 5310143 := bstep (se 1 (by rfl) ⟨3982607, by rfl⟩ : syracuseStep 5310143 = 7965215) B7965215
theorem B3147641 : Blo 1397518 3147641 := bstep (se 2 (by rfl) ⟨1180365, by rfl⟩ : syracuseStep 3147641 = 2360731) B2360731
theorem B4253597 : Blo 1397518 4253597 := bstep (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) B1595099
theorem B5670857 : Blo 1397518 5670857 := bstep (se 2 (by rfl) ⟨2126571, by rfl⟩ : syracuseStep 5670857 = 4253143) B4253143
theorem B2099231 : Blo 1397518 2099231 := bstep (se 1 (by rfl) ⟨1574423, by rfl⟩ : syracuseStep 2099231 = 3148847) B3148847
theorem B3148073 : Blo 1397518 3148073 := bstep (se 2 (by rfl) ⟨1180527, by rfl⟩ : syracuseStep 3148073 = 2361055) B2361055
theorem B4721111 : Blo 1397518 4721111 := bstep (se 1 (by rfl) ⟨3540833, by rfl⟩ : syracuseStep 4721111 = 7081667) B7081667
theorem B3983975 : Blo 1397518 3983975 := bstep (se 1 (by rfl) ⟨2987981, by rfl⟩ : syracuseStep 3983975 = 5975963) B5975963
theorem B3689063 : Blo 1397518 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B2656871 : Blo 1397518 2656871 := bstep (se 1 (by rfl) ⟨1992653, by rfl⟩ : syracuseStep 2656871 = 3985307) B3985307
theorem B34040519 : Blo 1397518 34040519 := bstep (se 1 (by rfl) ⟨25530389, by rfl⟩ : syracuseStep 34040519 = 51060779) B51060779
theorem B3148649 : Blo 1397518 3148649 := bstep (se 2 (by rfl) ⟨1180743, by rfl⟩ : syracuseStep 3148649 = 2361487) B2361487
theorem B2984863 : Blo 1397518 2984863 := bstep (se 1 (by rfl) ⟨2238647, by rfl⟩ : syracuseStep 2984863 = 4477295) B4477295
theorem B3148703 : Blo 1397518 3148703 := bstep (se 1 (by rfl) ⟨2361527, by rfl⟩ : syracuseStep 3148703 = 4723055) B4723055
theorem B20171693 : Blo 1397518 20171693 := bstep (se 3 (by rfl) ⟨3782192, by rfl⟩ : syracuseStep 20171693 = 7564385) B7564385
theorem B5311433 : Blo 1397518 5311433 := bstep (se 2 (by rfl) ⟨1991787, by rfl⟩ : syracuseStep 5311433 = 3983575) B3983575
theorem B3542363 : Blo 1397518 3542363 := bstep (se 1 (by rfl) ⟨2656772, by rfl⟩ : syracuseStep 3542363 = 5313545) B5313545
theorem B3542393 : Blo 1397518 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B7081343 : Blo 1397518 7081343 := bstep (se 1 (by rfl) ⟨5311007, by rfl⟩ : syracuseStep 7081343 = 10622015) B10622015
theorem B34483637 : Blo 1397518 34483637 := bstep (se 5 (by rfl) ⟨1616420, by rfl⟩ : syracuseStep 34483637 = 3232841) B3232841
theorem B26890055 : Blo 1397518 26890055 := bstep (se 1 (by rfl) ⟨20167541, by rfl⟩ : syracuseStep 26890055 = 40335083) B40335083
theorem B11939723 : Blo 1397518 11939723 := bstep (se 1 (by rfl) ⟨8954792, by rfl⟩ : syracuseStep 11939723 = 17909585) B17909585
theorem B26882057 : Blo 1397518 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B2519113 : Blo 1397518 2519113 := bstep (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) B1889335
theorem B40898969 : Blo 1397518 40898969 := bstep (se 2 (by rfl) ⟨15337113, by rfl⟩ : syracuseStep 40898969 = 30674227) B30674227
theorem B1397567 : Blo 1397518 1397567 := bstep (se 1 (by rfl) ⟨1048175, by rfl⟩ : syracuseStep 1397567 = 2096351) B2096351
theorem B1397595 : Blo 1397518 1397595 := bstep (se 1 (by rfl) ⟨1048196, by rfl⟩ : syracuseStep 1397595 = 2096393) B2096393
theorem B1397663 : Blo 1397518 1397663 := bstep (se 1 (by rfl) ⟨1048247, by rfl⟩ : syracuseStep 1397663 = 2096495) B2096495
theorem B1397743 : Blo 1397518 1397743 := bstep (se 1 (by rfl) ⟨1048307, by rfl⟩ : syracuseStep 1397743 = 2096615) B2096615
theorem B10613753 : Blo 1397518 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B1397831 : Blo 1397518 1397831 := bstep (se 1 (by rfl) ⟨1048373, by rfl⟩ : syracuseStep 1397831 = 2096747) B2096747
theorem B1397915 : Blo 1397518 1397915 := bstep (se 1 (by rfl) ⟨1048436, by rfl⟩ : syracuseStep 1397915 = 2096873) B2096873
theorem B11949221 : Blo 1397518 11949221 := bstep (se 4 (by rfl) ⟨1120239, by rfl⟩ : syracuseStep 11949221 = 2240479) B2240479
theorem B7075025 : Blo 1397518 7075025 := bstep (se 2 (by rfl) ⟨2653134, by rfl⟩ : syracuseStep 7075025 = 5306269) B5306269
theorem B1398011 : Blo 1397518 1398011 := bstep (se 1 (by rfl) ⟨1048508, by rfl⟩ : syracuseStep 1398011 = 2097017) B2097017
theorem B15938855 : Blo 1397518 15938855 := bstep (se 1 (by rfl) ⟨11954141, by rfl⟩ : syracuseStep 15938855 = 23908283) B23908283
theorem B1398079 : Blo 1397518 1398079 := bstep (se 1 (by rfl) ⟨1048559, by rfl⟩ : syracuseStep 1398079 = 2097119) B2097119
theorem B5379527 : Blo 1397518 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B1398247 : Blo 1397518 1398247 := bstep (se 1 (by rfl) ⟨1048685, by rfl⟩ : syracuseStep 1398247 = 2097371) B2097371
theorem B1398255 : Blo 1397518 1398255 := bstep (se 1 (by rfl) ⟨1048691, by rfl⟩ : syracuseStep 1398255 = 2097383) B2097383
theorem B1398363 : Blo 1397518 1398363 := bstep (se 1 (by rfl) ⟨1048772, by rfl⟩ : syracuseStep 1398363 = 2097545) B2097545
theorem B5666399 : Blo 1397518 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B1398427 : Blo 1397518 1398427 := bstep (se 1 (by rfl) ⟨1048820, by rfl⟩ : syracuseStep 1398427 = 2097641) B2097641
theorem B6723283 : Blo 1397518 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B1398511 : Blo 1397518 1398511 := bstep (se 1 (by rfl) ⟨1048883, by rfl⟩ : syracuseStep 1398511 = 2097767) B2097767
theorem B8181499 : Blo 1397518 8181499 := bstep (se 1 (by rfl) ⟨6136124, by rfl⟩ : syracuseStep 8181499 = 12272249) B12272249
theorem B8509207 : Blo 1397518 8509207 := bstep (se 1 (by rfl) ⟨6381905, by rfl⟩ : syracuseStep 8509207 = 12763811) B12763811
theorem B1398599 : Blo 1397518 1398599 := bstep (se 1 (by rfl) ⟨1048949, by rfl⟩ : syracuseStep 1398599 = 2097899) B2097899
theorem B1398619 : Blo 1397518 1398619 := bstep (se 1 (by rfl) ⟨1048964, by rfl⟩ : syracuseStep 1398619 = 2097929) B2097929
theorem B1398687 : Blo 1397518 1398687 := bstep (se 1 (by rfl) ⟨1049015, by rfl⟩ : syracuseStep 1398687 = 2098031) B2098031
theorem B8960071 : Blo 1397518 8960071 := bstep (se 1 (by rfl) ⟨6720053, by rfl⟩ : syracuseStep 8960071 = 13440107) B13440107
theorem B1398855 : Blo 1397518 1398855 := bstep (se 1 (by rfl) ⟨1049141, by rfl⟩ : syracuseStep 1398855 = 2098283) B2098283
theorem B1399015 : Blo 1397518 1399015 := bstep (se 1 (by rfl) ⟨1049261, by rfl⟩ : syracuseStep 1399015 = 2098523) B2098523
theorem B1399199 : Blo 1397518 1399199 := bstep (se 1 (by rfl) ⟨1049399, by rfl⟩ : syracuseStep 1399199 = 2098799) B2098799
theorem B4717007 : Blo 1397518 4717007 := bstep (se 1 (by rfl) ⟨3537755, by rfl⟩ : syracuseStep 4717007 = 7075511) B7075511
theorem B1399247 : Blo 1397518 1399247 := bstep (se 1 (by rfl) ⟨1049435, by rfl⟩ : syracuseStep 1399247 = 2098871) B2098871
theorem B1399271 : Blo 1397518 1399271 := bstep (se 1 (by rfl) ⟨1049453, by rfl⟩ : syracuseStep 1399271 = 2098907) B2098907
theorem B11942387 : Blo 1397518 11942387 := bstep (se 1 (by rfl) ⟨8956790, by rfl⟩ : syracuseStep 11942387 = 17913581) B17913581
theorem B7969337 : Blo 1397518 7969337 := bstep (se 2 (by rfl) ⟨2988501, by rfl⟩ : syracuseStep 7969337 = 5977003) B5977003
theorem B1399387 : Blo 1397518 1399387 := bstep (se 1 (by rfl) ⟨1049540, by rfl⟩ : syracuseStep 1399387 = 2099081) B2099081
theorem B1399455 : Blo 1397518 1399455 := bstep (se 1 (by rfl) ⟨1049591, by rfl⟩ : syracuseStep 1399455 = 2099183) B2099183
theorem B11344637 : Blo 1397518 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2390951 : Blo 1397518 2390951 := bstep (se 1 (by rfl) ⟨1793213, by rfl⟩ : syracuseStep 2390951 = 3586427) B3586427
theorem B54516989 : Blo 1397518 54516989 := bstep (se 3 (by rfl) ⟨10221935, by rfl⟩ : syracuseStep 54516989 = 20443871) B20443871
theorem B3538201 : Blo 1397518 3538201 := bstep (se 2 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 3538201 = 2653651) B2653651
theorem B2096591 : Blo 1397518 2096591 := bstep (se 1 (by rfl) ⟨1572443, by rfl⟩ : syracuseStep 2096591 = 3144887) B3144887
theorem B3145211 : Blo 1397518 3145211 := bstep (se 1 (by rfl) ⟨2358908, by rfl⟩ : syracuseStep 3145211 = 4717817) B4717817
theorem B7077455 : Blo 1397518 7077455 := bstep (se 1 (by rfl) ⟨5308091, by rfl⟩ : syracuseStep 7077455 = 10616183) B10616183
theorem B2358895 : Blo 1397518 2358895 := bstep (se 1 (by rfl) ⟨1769171, by rfl⟩ : syracuseStep 2358895 = 3538343) B3538343
theorem B3145391 : Blo 1397518 3145391 := bstep (se 1 (by rfl) ⟨2359043, by rfl⟩ : syracuseStep 3145391 = 4718087) B4718087
theorem B109035193 : Blo 1397518 109035193 := bstep (se 2 (by rfl) ⟨40888197, by rfl⟩ : syracuseStep 109035193 = 81776395) B81776395
theorem B1572583 : Blo 1397518 1572583 := bstep (se 1 (by rfl) ⟨1179437, by rfl⟩ : syracuseStep 1572583 = 2358875) B2358875
theorem B3145481 : Blo 1397518 3145481 := bstep (se 2 (by rfl) ⟨1179555, by rfl⟩ : syracuseStep 3145481 = 2359111) B2359111
theorem B5308199 : Blo 1397518 5308199 := bstep (se 1 (by rfl) ⟨3981149, by rfl⟩ : syracuseStep 5308199 = 7962299) B7962299
theorem B2096975 : Blo 1397518 2096975 := bstep (se 1 (by rfl) ⟨1572731, by rfl⟩ : syracuseStep 2096975 = 3145463) B3145463
theorem B22683563 : Blo 1397518 22683563 := bstep (se 1 (by rfl) ⟨17012672, by rfl⟩ : syracuseStep 22683563 = 34025345) B34025345
theorem B2097095 : Blo 1397518 2097095 := bstep (se 1 (by rfl) ⟨1572821, by rfl⟩ : syracuseStep 2097095 = 3145643) B3145643
theorem B5971913 : Blo 1397518 5971913 := bstep (se 2 (by rfl) ⟨2239467, by rfl⟩ : syracuseStep 5971913 = 4478935) B4478935
theorem B3358817 : Blo 1397518 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B2097407 : Blo 1397518 2097407 := bstep (se 1 (by rfl) ⟨1573055, by rfl⟩ : syracuseStep 2097407 = 3146111) B3146111
theorem B3981707 : Blo 1397518 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B2097563 : Blo 1397518 2097563 := bstep (se 1 (by rfl) ⟨1573172, by rfl⟩ : syracuseStep 2097563 = 3146345) B3146345
theorem B7963231 : Blo 1397518 7963231 := bstep (se 1 (by rfl) ⟨5972423, by rfl⟩ : syracuseStep 7963231 = 11944847) B11944847
theorem B3981935 : Blo 1397518 3981935 := bstep (se 1 (by rfl) ⟨2986451, by rfl⟩ : syracuseStep 3981935 = 5972903) B5972903
theorem B2654927 : Blo 1397518 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B130892591 : Blo 1397518 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B2097983 : Blo 1397518 2097983 := bstep (se 1 (by rfl) ⟨1573487, by rfl⟩ : syracuseStep 2097983 = 3146975) B3146975
theorem B10625903 : Blo 1397518 10625903 := bstep (se 1 (by rfl) ⟨7969427, by rfl⟩ : syracuseStep 10625903 = 15938855) B15938855
theorem B2098127 : Blo 1397518 2098127 := bstep (se 1 (by rfl) ⟨1573595, by rfl⟩ : syracuseStep 2098127 = 3147191) B3147191
theorem B2360299 : Blo 1397518 2360299 := bstep (se 1 (by rfl) ⟨1770224, by rfl⟩ : syracuseStep 2360299 = 3540449) B3540449
theorem B3539963 : Blo 1397518 3539963 := bstep (se 1 (by rfl) ⟨2654972, by rfl⟩ : syracuseStep 3539963 = 5309945) B5309945
theorem B2098217 : Blo 1397518 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B3777599 : Blo 1397518 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B2098247 : Blo 1397518 2098247 := bstep (se 1 (by rfl) ⟨1573685, by rfl⟩ : syracuseStep 2098247 = 3147371) B3147371
theorem B3540095 : Blo 1397518 3540095 := bstep (se 1 (by rfl) ⟨2655071, by rfl⟩ : syracuseStep 3540095 = 5310143) B5310143
theorem B14345405 : Blo 1397518 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B2098427 : Blo 1397518 2098427 := bstep (se 1 (by rfl) ⟨1573820, by rfl⟩ : syracuseStep 2098427 = 3147641) B3147641
theorem B2835731 : Blo 1397518 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B2098715 : Blo 1397518 2098715 := bstep (se 1 (by rfl) ⟨1574036, by rfl⟩ : syracuseStep 2098715 = 3148073) B3148073
theorem B3147407 : Blo 1397518 3147407 := bstep (se 1 (by rfl) ⟨2360555, by rfl⟩ : syracuseStep 3147407 = 4721111) B4721111
theorem B3147497 : Blo 1397518 3147497 := bstep (se 2 (by rfl) ⟨1180311, by rfl⟩ : syracuseStep 3147497 = 2360623) B2360623
theorem B2655983 : Blo 1397518 2655983 := bstep (se 1 (by rfl) ⟨1991987, by rfl⟩ : syracuseStep 2655983 = 3983975) B3983975
theorem B2459375 : Blo 1397518 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B1771247 : Blo 1397518 1771247 := bstep (se 1 (by rfl) ⟨1328435, by rfl⟩ : syracuseStep 1771247 = 2656871) B2656871
theorem B22693679 : Blo 1397518 22693679 := bstep (se 1 (by rfl) ⟨17020259, by rfl⟩ : syracuseStep 22693679 = 34040519) B34040519
theorem B7563091 : Blo 1397518 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B2099099 : Blo 1397518 2099099 := bstep (se 1 (by rfl) ⟨1574324, by rfl⟩ : syracuseStep 2099099 = 3148649) B3148649
theorem B2099135 : Blo 1397518 2099135 := bstep (se 1 (by rfl) ⟨1574351, by rfl⟩ : syracuseStep 2099135 = 3148703) B3148703
theorem B3540955 : Blo 1397518 3540955 := bstep (se 1 (by rfl) ⟨2655716, by rfl⟩ : syracuseStep 3540955 = 5311433) B5311433
theorem B2361575 : Blo 1397518 2361575 := bstep (se 1 (by rfl) ⟨1771181, by rfl⟩ : syracuseStep 2361575 = 3542363) B3542363
theorem B2361595 : Blo 1397518 2361595 := bstep (se 1 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 2361595 = 3542393) B3542393
theorem B4720895 : Blo 1397518 4720895 := bstep (se 1 (by rfl) ⟨3540671, by rfl⟩ : syracuseStep 4720895 = 7081343) B7081343
theorem B8964377 : Blo 1397518 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B22989091 : Blo 1397518 22989091 := bstep (se 1 (by rfl) ⟨17241818, by rfl⟩ : syracuseStep 22989091 = 34483637) B34483637
theorem B17926703 : Blo 1397518 17926703 := bstep (se 1 (by rfl) ⟨13445027, by rfl⟩ : syracuseStep 17926703 = 26890055) B26890055
theorem B11946761 : Blo 1397518 11946761 := bstep (se 2 (by rfl) ⟨4480035, by rfl⟩ : syracuseStep 11946761 = 8960071) B8960071
theorem B111938429 : Blo 1397518 111938429 := bstep (se 3 (by rfl) ⟨20988455, by rfl⟩ : syracuseStep 111938429 = 41976911) B41976911
theorem B27265979 : Blo 1397518 27265979 := bstep (se 1 (by rfl) ⟨20449484, by rfl⟩ : syracuseStep 27265979 = 40898969) B40898969
theorem B145378637 : Blo 1397518 145378637 := bstep (se 3 (by rfl) ⟨27258494, by rfl⟩ : syracuseStep 145378637 = 54516989) B54516989
theorem B7966147 : Blo 1397518 7966147 := bstep (se 1 (by rfl) ⟨5974610, by rfl⟩ : syracuseStep 7966147 = 11949221) B11949221
theorem B145363261 : Blo 1397518 145363261 := bstep (se 3 (by rfl) ⟨27255611, by rfl⟩ : syracuseStep 145363261 = 54511223) B54511223
theorem B5312891 : Blo 1397518 5312891 := bstep (se 1 (by rfl) ⟨3984668, by rfl⟩ : syracuseStep 5312891 = 7969337) B7969337
theorem B1593967 : Blo 1397518 1593967 := bstep (se 1 (by rfl) ⟨1195475, by rfl⟩ : syracuseStep 1593967 = 2390951) B2390951
theorem B13447795 : Blo 1397518 13447795 := bstep (se 1 (by rfl) ⟨10085846, by rfl⟩ : syracuseStep 13447795 = 20171693) B20171693
theorem B145380257 : Blo 1397518 145380257 := bstep (se 2 (by rfl) ⟨54517596, by rfl⟩ : syracuseStep 145380257 = 109035193) B109035193
theorem B1397727 : Blo 1397518 1397727 := bstep (se 1 (by rfl) ⟨1048295, by rfl⟩ : syracuseStep 1397727 = 2096591) B2096591
theorem B10908665 : Blo 1397518 10908665 := bstep (se 2 (by rfl) ⟨4090749, by rfl⟩ : syracuseStep 10908665 = 8181499) B8181499
theorem B1397983 : Blo 1397518 1397983 := bstep (se 1 (by rfl) ⟨1048487, by rfl⟩ : syracuseStep 1397983 = 2096975) B2096975
theorem B7959815 : Blo 1397518 7959815 := bstep (se 1 (by rfl) ⟨5969861, by rfl⟩ : syracuseStep 7959815 = 11939723) B11939723
theorem B1398063 : Blo 1397518 1398063 := bstep (se 1 (by rfl) ⟨1048547, by rfl⟩ : syracuseStep 1398063 = 2097095) B2097095
theorem B17921371 : Blo 1397518 17921371 := bstep (se 1 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 17921371 = 26882057) B26882057
theorem B1398303 : Blo 1397518 1398303 := bstep (se 1 (by rfl) ⟨1048727, by rfl⟩ : syracuseStep 1398303 = 2097455) B2097455
theorem B5379655 : Blo 1397518 5379655 := bstep (se 1 (by rfl) ⟨4034741, by rfl⟩ : syracuseStep 5379655 = 8069483) B8069483
theorem B1398463 : Blo 1397518 1398463 := bstep (se 1 (by rfl) ⟨1048847, by rfl⟩ : syracuseStep 1398463 = 2097695) B2097695
theorem B7075835 : Blo 1397518 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B30234707 : Blo 1397518 30234707 := bstep (se 1 (by rfl) ⟨22676030, by rfl⟩ : syracuseStep 30234707 = 45352061) B45352061
theorem B1398911 : Blo 1397518 1398911 := bstep (se 1 (by rfl) ⟨1049183, by rfl⟩ : syracuseStep 1398911 = 2098367) B2098367
theorem B4479113 : Blo 1397518 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B4716683 : Blo 1397518 4716683 := bstep (se 1 (by rfl) ⟨3537512, by rfl⟩ : syracuseStep 4716683 = 7075025) B7075025
theorem B1399007 : Blo 1397518 1399007 := bstep (se 1 (by rfl) ⟨1049255, by rfl⟩ : syracuseStep 1399007 = 2098511) B2098511
theorem B1890535 : Blo 1397518 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B1399067 : Blo 1397518 1399067 := bstep (se 1 (by rfl) ⟨1049300, by rfl⟩ : syracuseStep 1399067 = 2098601) B2098601
theorem B1399167 : Blo 1397518 1399167 := bstep (se 1 (by rfl) ⟨1049375, by rfl⟩ : syracuseStep 1399167 = 2098751) B2098751
theorem B4479371 : Blo 1397518 4479371 := bstep (se 1 (by rfl) ⟨3359528, by rfl⟩ : syracuseStep 4479371 = 6719057) B6719057
theorem B1399195 : Blo 1397518 1399195 := bstep (se 1 (by rfl) ⟨1049396, by rfl⟩ : syracuseStep 1399195 = 2098793) B2098793
theorem B16144829 : Blo 1397518 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B3979817 : Blo 1397518 3979817 := bstep (se 2 (by rfl) ⟨1492431, by rfl⟩ : syracuseStep 3979817 = 2984863) B2984863
theorem B1399487 : Blo 1397518 1399487 := bstep (se 1 (by rfl) ⟨1049615, by rfl⟩ : syracuseStep 1399487 = 2099231) B2099231
theorem B3144671 : Blo 1397518 3144671 := bstep (se 1 (by rfl) ⟨2358503, by rfl⟩ : syracuseStep 3144671 = 4717007) B4717007
theorem B7961591 : Blo 1397518 7961591 := bstep (se 1 (by rfl) ⟨5971193, by rfl⟩ : syracuseStep 7961591 = 11942387) B11942387
theorem B4717601 : Blo 1397518 4717601 := bstep (se 2 (by rfl) ⟨1769100, by rfl⟩ : syracuseStep 4717601 = 3538201) B3538201
theorem B3145193 : Blo 1397518 3145193 := bstep (se 2 (by rfl) ⟨1179447, by rfl⟩ : syracuseStep 3145193 = 2358895) B2358895
theorem B2096777 : Blo 1397518 2096777 := bstep (se 2 (by rfl) ⟨786291, by rfl⟩ : syracuseStep 2096777 = 1572583) B1572583
theorem B2096807 : Blo 1397518 2096807 := bstep (se 1 (by rfl) ⟨1572605, by rfl⟩ : syracuseStep 2096807 = 3145211) B3145211
theorem B11345609 : Blo 1397518 11345609 := bstep (se 2 (by rfl) ⟨4254603, by rfl⟩ : syracuseStep 11345609 = 8509207) B8509207
theorem B4718303 : Blo 1397518 4718303 := bstep (se 1 (by rfl) ⟨3538727, by rfl⟩ : syracuseStep 4718303 = 7077455) B7077455
theorem B2096927 : Blo 1397518 2096927 := bstep (se 1 (by rfl) ⟨1572695, by rfl⟩ : syracuseStep 2096927 = 3145391) B3145391
theorem B2096987 : Blo 1397518 2096987 := bstep (se 1 (by rfl) ⟨1572740, by rfl⟩ : syracuseStep 2096987 = 3145481) B3145481
theorem B15122285 : Blo 1397518 15122285 := bstep (se 3 (by rfl) ⟨2835428, by rfl⟩ : syracuseStep 15122285 = 5670857) B5670857
theorem B3538799 : Blo 1397518 3538799 := bstep (se 1 (by rfl) ⟨2654099, by rfl⟩ : syracuseStep 3538799 = 5308199) B5308199
theorem B15122375 : Blo 1397518 15122375 := bstep (se 1 (by rfl) ⟨11341781, by rfl⟩ : syracuseStep 15122375 = 22683563) B22683563
theorem B3981275 : Blo 1397518 3981275 := bstep (se 1 (by rfl) ⟨2985956, by rfl⟩ : syracuseStep 3981275 = 5971913) B5971913
theorem B2654471 : Blo 1397518 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B2654623 : Blo 1397518 2654623 := bstep (se 1 (by rfl) ⟨1990967, by rfl⟩ : syracuseStep 2654623 = 3981935) B3981935
theorem B1769951 : Blo 1397518 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B96920171 : Blo 1397518 96920171 := bstep (se 1 (by rfl) ⟨72690128, by rfl⟩ : syracuseStep 96920171 = 145380257) B145380257
theorem B2359975 : Blo 1397518 2359975 := bstep (se 1 (by rfl) ⟨1769981, by rfl⟩ : syracuseStep 2359975 = 3539963) B3539963
theorem B2360063 : Blo 1397518 2360063 := bstep (se 1 (by rfl) ⟨1770047, by rfl⟩ : syracuseStep 2360063 = 3540095) B3540095
theorem B10617641 : Blo 1397518 10617641 := bstep (se 2 (by rfl) ⟨3981615, by rfl⟩ : syracuseStep 10617641 = 7963231) B7963231
theorem B2098271 : Blo 1397518 2098271 := bstep (se 1 (by rfl) ⟨1573703, by rfl⟩ : syracuseStep 2098271 = 3147407) B3147407
theorem B2098331 : Blo 1397518 2098331 := bstep (se 1 (by rfl) ⟨1573748, by rfl⟩ : syracuseStep 2098331 = 3147497) B3147497
theorem B1770655 : Blo 1397518 1770655 := bstep (se 1 (by rfl) ⟨1327991, by rfl⟩ : syracuseStep 1770655 = 2655983) B2655983
theorem B1639583 : Blo 1397518 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B3147065 : Blo 1397518 3147065 := bstep (se 2 (by rfl) ⟨1180149, by rfl⟩ : syracuseStep 3147065 = 2360299) B2360299
theorem B1574383 : Blo 1397518 1574383 := bstep (se 1 (by rfl) ⟨1180787, by rfl⟩ : syracuseStep 1574383 = 2361575) B2361575
theorem B3147263 : Blo 1397518 3147263 := bstep (se 1 (by rfl) ⟨2360447, by rfl⟩ : syracuseStep 3147263 = 4720895) B4720895
theorem B7964507 : Blo 1397518 7964507 := bstep (se 1 (by rfl) ⟨5973380, by rfl⟩ : syracuseStep 7964507 = 11946761) B11946761
theorem B30254957 : Blo 1397518 30254957 := bstep (se 3 (by rfl) ⟨5672804, by rfl⟩ : syracuseStep 30254957 = 11345609) B11345609
theorem B349046909 : Blo 1397518 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B4721273 : Blo 1397518 4721273 := bstep (se 2 (by rfl) ⟨1770477, by rfl⟩ : syracuseStep 4721273 = 3540955) B3540955
theorem B2239211 : Blo 1397518 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B3541927 : Blo 1397518 3541927 := bstep (se 1 (by rfl) ⟨2656445, by rfl⟩ : syracuseStep 3541927 = 5312891) B5312891
theorem B3148793 : Blo 1397518 3148793 := bstep (se 2 (by rfl) ⟨1180797, by rfl⟩ : syracuseStep 3148793 = 2361595) B2361595
theorem B193817681 : Blo 1397518 193817681 := bstep (se 2 (by rfl) ⟨72681630, by rfl⟩ : syracuseStep 193817681 = 145363261) B145363261
theorem B2518399 : Blo 1397518 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B9563603 : Blo 1397518 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B2125289 : Blo 1397518 2125289 := bstep (se 2 (by rfl) ⟨796983, by rfl⟩ : syracuseStep 2125289 = 1593967) B1593967
theorem B20156471 : Blo 1397518 20156471 := bstep (se 1 (by rfl) ⟨15117353, by rfl⟩ : syracuseStep 20156471 = 30234707) B30234707
theorem B2986075 : Blo 1397518 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B5976251 : Blo 1397518 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B2986247 : Blo 1397518 2986247 := bstep (se 1 (by rfl) ⟨2239685, by rfl⟩ : syracuseStep 2986247 = 4479371) B4479371
theorem B74625619 : Blo 1397518 74625619 := bstep (se 1 (by rfl) ⟨55969214, by rfl⟩ : syracuseStep 74625619 = 111938429) B111938429
theorem B10621529 : Blo 1397518 10621529 := bstep (se 2 (by rfl) ⟨3983073, by rfl⟩ : syracuseStep 10621529 = 7966147) B7966147
theorem B4723325 : Blo 1397518 4723325 := bstep (se 3 (by rfl) ⟨885623, by rfl⟩ : syracuseStep 4723325 = 1771247) B1771247
theorem B7172873 : Blo 1397518 7172873 := bstep (se 2 (by rfl) ⟨2689827, by rfl⟩ : syracuseStep 7172873 = 5379655) B5379655
theorem B1397851 : Blo 1397518 1397851 := bstep (se 1 (by rfl) ⟨1048388, by rfl⟩ : syracuseStep 1397851 = 2096777) B2096777
theorem B1397871 : Blo 1397518 1397871 := bstep (se 1 (by rfl) ⟨1048403, by rfl⟩ : syracuseStep 1397871 = 2096807) B2096807
theorem B1397951 : Blo 1397518 1397951 := bstep (se 1 (by rfl) ⟨1048463, by rfl⟩ : syracuseStep 1397951 = 2096927) B2096927
theorem B1397991 : Blo 1397518 1397991 := bstep (se 1 (by rfl) ⟨1048493, by rfl⟩ : syracuseStep 1397991 = 2096987) B2096987
theorem B10081523 : Blo 1397518 10081523 := bstep (se 1 (by rfl) ⟨7561142, by rfl⟩ : syracuseStep 10081523 = 15122285) B15122285
theorem B10081583 : Blo 1397518 10081583 := bstep (se 1 (by rfl) ⟨7561187, by rfl⟩ : syracuseStep 10081583 = 15122375) B15122375
theorem B1398271 : Blo 1397518 1398271 := bstep (se 1 (by rfl) ⟨1048703, by rfl⟩ : syracuseStep 1398271 = 2097407) B2097407
theorem B1398375 : Blo 1397518 1398375 := bstep (se 1 (by rfl) ⟨1048781, by rfl⟩ : syracuseStep 1398375 = 2097563) B2097563
theorem B2520713 : Blo 1397518 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B30652121 : Blo 1397518 30652121 := bstep (se 2 (by rfl) ⟨11494545, by rfl⟩ : syracuseStep 30652121 = 22989091) B22989091
theorem B1398655 : Blo 1397518 1398655 := bstep (se 1 (by rfl) ⟨1048991, by rfl⟩ : syracuseStep 1398655 = 2097983) B2097983
theorem B7083935 : Blo 1397518 7083935 := bstep (se 1 (by rfl) ⟨5312951, by rfl⟩ : syracuseStep 7083935 = 10625903) B10625903
theorem B1398751 : Blo 1397518 1398751 := bstep (se 1 (by rfl) ⟨1049063, by rfl⟩ : syracuseStep 1398751 = 2098127) B2098127
theorem B7272443 : Blo 1397518 7272443 := bstep (se 1 (by rfl) ⟨5454332, by rfl⟩ : syracuseStep 7272443 = 10908665) B10908665
theorem B1398811 : Blo 1397518 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B1398831 : Blo 1397518 1398831 := bstep (se 1 (by rfl) ⟨1049123, by rfl⟩ : syracuseStep 1398831 = 2098247) B2098247
theorem B17930393 : Blo 1397518 17930393 := bstep (se 2 (by rfl) ⟨6723897, by rfl⟩ : syracuseStep 17930393 = 13447795) B13447795
theorem B1398951 : Blo 1397518 1398951 := bstep (se 1 (by rfl) ⟨1049213, by rfl⟩ : syracuseStep 1398951 = 2098427) B2098427
theorem B5306543 : Blo 1397518 5306543 := bstep (se 1 (by rfl) ⟨3979907, by rfl⟩ : syracuseStep 5306543 = 7959815) B7959815
theorem B1890487 : Blo 1397518 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B1399143 : Blo 1397518 1399143 := bstep (se 1 (by rfl) ⟨1049357, by rfl⟩ : syracuseStep 1399143 = 2098715) B2098715
theorem B15129119 : Blo 1397518 15129119 := bstep (se 1 (by rfl) ⟨11346839, by rfl⟩ : syracuseStep 15129119 = 22693679) B22693679
theorem B1399399 : Blo 1397518 1399399 := bstep (se 1 (by rfl) ⟨1049549, by rfl⟩ : syracuseStep 1399399 = 2099099) B2099099
theorem B1399423 : Blo 1397518 1399423 := bstep (se 1 (by rfl) ⟨1049567, by rfl⟩ : syracuseStep 1399423 = 2099135) B2099135
theorem B4717223 : Blo 1397518 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B3144455 : Blo 1397518 3144455 := bstep (se 1 (by rfl) ⟨2358341, by rfl⟩ : syracuseStep 3144455 = 4716683) B4716683
theorem B10763219 : Blo 1397518 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B2653211 : Blo 1397518 2653211 := bstep (se 1 (by rfl) ⟨1989908, by rfl⟩ : syracuseStep 2653211 = 3979817) B3979817
theorem B11951135 : Blo 1397518 11951135 := bstep (se 1 (by rfl) ⟨8963351, by rfl⟩ : syracuseStep 11951135 = 17926703) B17926703
theorem B23895161 : Blo 1397518 23895161 := bstep (se 2 (by rfl) ⟨8960685, by rfl⟩ : syracuseStep 23895161 = 17921371) B17921371
theorem B18177319 : Blo 1397518 18177319 := bstep (se 1 (by rfl) ⟨13632989, by rfl⟩ : syracuseStep 18177319 = 27265979) B27265979
theorem B2096447 : Blo 1397518 2096447 := bstep (se 1 (by rfl) ⟨1572335, by rfl⟩ : syracuseStep 2096447 = 3144671) B3144671
theorem B5307727 : Blo 1397518 5307727 := bstep (se 1 (by rfl) ⟨3980795, by rfl⟩ : syracuseStep 5307727 = 7961591) B7961591
theorem B3145067 : Blo 1397518 3145067 := bstep (se 1 (by rfl) ⟨2358800, by rfl⟩ : syracuseStep 3145067 = 4717601) B4717601
theorem B96919091 : Blo 1397518 96919091 := bstep (se 1 (by rfl) ⟨72689318, by rfl⟩ : syracuseStep 96919091 = 145378637) B145378637
theorem B2096795 : Blo 1397518 2096795 := bstep (se 1 (by rfl) ⟨1572596, by rfl⟩ : syracuseStep 2096795 = 3145193) B3145193
theorem B10084121 : Blo 1397518 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B3145535 : Blo 1397518 3145535 := bstep (se 1 (by rfl) ⟨2359151, by rfl⟩ : syracuseStep 3145535 = 4718303) B4718303
theorem B2359199 : Blo 1397518 2359199 := bstep (se 1 (by rfl) ⟨1769399, by rfl⟩ : syracuseStep 2359199 = 3538799) B3538799
theorem B2654183 : Blo 1397518 2654183 := bstep (se 1 (by rfl) ⟨1990637, by rfl⟩ : syracuseStep 2654183 = 3981275) B3981275
theorem B1990831 : Blo 1397518 1990831 := bstep (se 1 (by rfl) ⟨1493123, by rfl⟩ : syracuseStep 1990831 = 2986247) B2986247
theorem B15925733 : Blo 1397518 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B1573375 : Blo 1397518 1573375 := bstep (se 1 (by rfl) ⟨1180031, by rfl⟩ : syracuseStep 1573375 = 2360063) B2360063
theorem B7078427 : Blo 1397518 7078427 := bstep (se 1 (by rfl) ⟨5308820, by rfl⟩ : syracuseStep 7078427 = 10617641) B10617641
theorem B3539497 : Blo 1397518 3539497 := bstep (se 2 (by rfl) ⟨1327311, by rfl⟩ : syracuseStep 3539497 = 2654623) B2654623
theorem B7078589 : Blo 1397518 7078589 := bstep (se 3 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 7078589 = 2654471) B2654471
theorem B99500825 : Blo 1397518 99500825 := bstep (se 2 (by rfl) ⟨37312809, by rfl⟩ : syracuseStep 99500825 = 74625619) B74625619
theorem B2098043 : Blo 1397518 2098043 := bstep (se 1 (by rfl) ⟨1573532, by rfl⟩ : syracuseStep 2098043 = 3147065) B3147065
theorem B3146633 : Blo 1397518 3146633 := bstep (se 2 (by rfl) ⟨1179987, by rfl⟩ : syracuseStep 3146633 = 2359975) B2359975
theorem B2098175 : Blo 1397518 2098175 := bstep (se 1 (by rfl) ⟨1573631, by rfl⟩ : syracuseStep 2098175 = 3147263) B3147263
theorem B1680475 : Blo 1397518 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B25502941 : Blo 1397518 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B5309671 : Blo 1397518 5309671 := bstep (se 1 (by rfl) ⟨3982253, by rfl⟩ : syracuseStep 5309671 = 7964507) B7964507
theorem B20169971 : Blo 1397518 20169971 := bstep (se 1 (by rfl) ⟨15127478, by rfl⟩ : syracuseStep 20169971 = 30254957) B30254957
theorem B4719869 : Blo 1397518 4719869 := bstep (se 3 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 4719869 = 1769951) B1769951
theorem B11953595 : Blo 1397518 11953595 := bstep (se 1 (by rfl) ⟨8965196, by rfl⟩ : syracuseStep 11953595 = 17930393) B17930393
theorem B2360873 : Blo 1397518 2360873 := bstep (se 2 (by rfl) ⟨885327, by rfl⟩ : syracuseStep 2360873 = 1770655) B1770655
theorem B10086079 : Blo 1397518 10086079 := bstep (se 1 (by rfl) ⟨7564559, by rfl⟩ : syracuseStep 10086079 = 15129119) B15129119
theorem B3147515 : Blo 1397518 3147515 := bstep (se 1 (by rfl) ⟨2360636, by rfl⟩ : syracuseStep 3147515 = 4721273) B4721273
theorem B2099177 : Blo 1397518 2099177 := bstep (se 2 (by rfl) ⟨787191, by rfl⟩ : syracuseStep 2099177 = 1574383) B1574383
theorem B2099195 : Blo 1397518 2099195 := bstep (se 1 (by rfl) ⟨1574396, by rfl⟩ : syracuseStep 2099195 = 3148793) B3148793
theorem B64612727 : Blo 1397518 64612727 := bstep (se 1 (by rfl) ⟨48459545, by rfl⟩ : syracuseStep 64612727 = 96919091) B96919091
theorem B13437647 : Blo 1397518 13437647 := bstep (se 1 (by rfl) ⟨10078235, by rfl⟩ : syracuseStep 13437647 = 20156471) B20156471
theorem B3984167 : Blo 1397518 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B7081019 : Blo 1397518 7081019 := bstep (se 1 (by rfl) ⟨5310764, by rfl⟩ : syracuseStep 7081019 = 10621529) B10621529
theorem B64613447 : Blo 1397518 64613447 := bstep (se 1 (by rfl) ⟨48460085, by rfl⟩ : syracuseStep 64613447 = 96920171) B96920171
theorem B3148883 : Blo 1397518 3148883 := bstep (se 1 (by rfl) ⟨2361662, by rfl⟩ : syracuseStep 3148883 = 4723325) B4723325
theorem B6721055 : Blo 1397518 6721055 := bstep (se 1 (by rfl) ⟨5040791, by rfl⟩ : syracuseStep 6721055 = 10081583) B10081583
theorem B4722569 : Blo 1397518 4722569 := bstep (se 2 (by rfl) ⟨1770963, by rfl⟩ : syracuseStep 4722569 = 3541927) B3541927
theorem B4722623 : Blo 1397518 4722623 := bstep (se 1 (by rfl) ⟨3541967, by rfl⟩ : syracuseStep 4722623 = 7083935) B7083935
theorem B232697939 : Blo 1397518 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B24236425 : Blo 1397518 24236425 := bstep (se 2 (by rfl) ⟨9088659, by rfl⟩ : syracuseStep 24236425 = 18177319) B18177319
theorem B7967423 : Blo 1397518 7967423 := bstep (se 1 (by rfl) ⟨5975567, by rfl⟩ : syracuseStep 7967423 = 11951135) B11951135
theorem B15930107 : Blo 1397518 15930107 := bstep (se 1 (by rfl) ⟨11947580, by rfl⟩ : syracuseStep 15930107 = 23895161) B23895161
theorem B1397631 : Blo 1397518 1397631 := bstep (se 1 (by rfl) ⟨1048223, by rfl⟩ : syracuseStep 1397631 = 2096447) B2096447
theorem B1397863 : Blo 1397518 1397863 := bstep (se 1 (by rfl) ⟨1048397, by rfl⟩ : syracuseStep 1397863 = 2096795) B2096795
theorem B6722747 : Blo 1397518 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B2520649 : Blo 1397518 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B4781915 : Blo 1397518 4781915 := bstep (se 1 (by rfl) ⟨3586436, by rfl⟩ : syracuseStep 4781915 = 7172873) B7172873
theorem B26884061 : Blo 1397518 26884061 := bstep (se 3 (by rfl) ⟨5040761, by rfl⟩ : syracuseStep 26884061 = 10081523) B10081523
theorem B1398847 : Blo 1397518 1398847 := bstep (se 1 (by rfl) ⟨1049135, by rfl⟩ : syracuseStep 1398847 = 2098271) B2098271
theorem B1398887 : Blo 1397518 1398887 := bstep (se 1 (by rfl) ⟨1049165, by rfl⟩ : syracuseStep 1398887 = 2098331) B2098331
theorem B4848295 : Blo 1397518 4848295 := bstep (se 1 (by rfl) ⟨3636221, by rfl⟩ : syracuseStep 4848295 = 7272443) B7272443
theorem B3537695 : Blo 1397518 3537695 := bstep (se 1 (by rfl) ⟨2653271, by rfl⟩ : syracuseStep 3537695 = 5306543) B5306543
theorem B17488885 : Blo 1397518 17488885 := bstep (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) B1639583
theorem B7076969 : Blo 1397518 7076969 := bstep (se 2 (by rfl) ⟨2653863, by rfl⟩ : syracuseStep 7076969 = 5307727) B5307727
theorem B3144815 : Blo 1397518 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B3357865 : Blo 1397518 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B2096303 : Blo 1397518 2096303 := bstep (se 1 (by rfl) ⟨1572227, by rfl⟩ : syracuseStep 2096303 = 3144455) B3144455
theorem B81738989 : Blo 1397518 81738989 := bstep (se 3 (by rfl) ⟨15326060, by rfl⟩ : syracuseStep 81738989 = 30652121) B30652121
theorem B5971229 : Blo 1397518 5971229 := bstep (se 3 (by rfl) ⟨1119605, by rfl⟩ : syracuseStep 5971229 = 2239211) B2239211
theorem B7175479 : Blo 1397518 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B1768807 : Blo 1397518 1768807 := bstep (se 1 (by rfl) ⟨1326605, by rfl⟩ : syracuseStep 1768807 = 2653211) B2653211
theorem B129211787 : Blo 1397518 129211787 := bstep (se 1 (by rfl) ⟨96908840, by rfl⟩ : syracuseStep 129211787 = 193817681) B193817681
theorem B2096711 : Blo 1397518 2096711 := bstep (se 1 (by rfl) ⟨1572533, by rfl⟩ : syracuseStep 2096711 = 3145067) B3145067
theorem B1416859 : Blo 1397518 1416859 := bstep (se 1 (by rfl) ⟨1062644, by rfl⟩ : syracuseStep 1416859 = 2125289) B2125289
theorem B2097023 : Blo 1397518 2097023 := bstep (se 1 (by rfl) ⟨1572767, by rfl⟩ : syracuseStep 2097023 = 3145535) B3145535
theorem B1572799 : Blo 1397518 1572799 := bstep (se 1 (by rfl) ⟨1179599, by rfl⟩ : syracuseStep 1572799 = 2359199) B2359199
theorem B1769455 : Blo 1397518 1769455 := bstep (se 1 (by rfl) ⟨1327091, by rfl⟩ : syracuseStep 1769455 = 2654183) B2654183
theorem B620527837 : Blo 1397518 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B2654441 : Blo 1397518 2654441 := bstep (se 2 (by rfl) ⟨995415, by rfl⟩ : syracuseStep 2654441 = 1990831) B1990831
theorem B10617155 : Blo 1397518 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B4718951 : Blo 1397518 4718951 := bstep (se 1 (by rfl) ⟨3539213, by rfl⟩ : syracuseStep 4718951 = 7078427) B7078427
theorem B4719059 : Blo 1397518 4719059 := bstep (se 1 (by rfl) ⟨3539294, by rfl⟩ : syracuseStep 4719059 = 7078589) B7078589
theorem B2097755 : Blo 1397518 2097755 := bstep (se 1 (by rfl) ⟨1573316, by rfl⟩ : syracuseStep 2097755 = 3146633) B3146633
theorem B2097833 : Blo 1397518 2097833 := bstep (se 2 (by rfl) ⟨786687, by rfl⟩ : syracuseStep 2097833 = 1573375) B1573375
theorem B4719329 : Blo 1397518 4719329 := bstep (se 2 (by rfl) ⟨1769748, by rfl⟩ : syracuseStep 4719329 = 3539497) B3539497
theorem B4481831 : Blo 1397518 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B3146579 : Blo 1397518 3146579 := bstep (se 1 (by rfl) ⟨2359934, by rfl⟩ : syracuseStep 3146579 = 4719869) B4719869
theorem B17908613 : Blo 1397518 17908613 := bstep (se 4 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 17908613 = 3357865) B3357865
theorem B6464393 : Blo 1397518 6464393 := bstep (se 2 (by rfl) ⟨2424147, by rfl⟩ : syracuseStep 6464393 = 4848295) B4848295
theorem B1573915 : Blo 1397518 1573915 := bstep (se 1 (by rfl) ⟨1180436, by rfl⟩ : syracuseStep 1573915 = 2360873) B2360873
theorem B2098343 : Blo 1397518 2098343 := bstep (se 1 (by rfl) ⟨1573757, by rfl⟩ : syracuseStep 2098343 = 3147515) B3147515
theorem B3187943 : Blo 1397518 3187943 := bstep (se 1 (by rfl) ⟨2390957, by rfl⟩ : syracuseStep 3187943 = 4781915) B4781915
theorem B43075151 : Blo 1397518 43075151 := bstep (se 1 (by rfl) ⟨32306363, by rfl⟩ : syracuseStep 43075151 = 64612727) B64612727
theorem B7079561 : Blo 1397518 7079561 := bstep (se 2 (by rfl) ⟨2654835, by rfl⟩ : syracuseStep 7079561 = 5309671) B5309671
theorem B4720679 : Blo 1397518 4720679 := bstep (se 1 (by rfl) ⟨3540509, by rfl⟩ : syracuseStep 4720679 = 7081019) B7081019
theorem B43075631 : Blo 1397518 43075631 := bstep (se 1 (by rfl) ⟨32306723, by rfl⟩ : syracuseStep 43075631 = 64613447) B64613447
theorem B2099255 : Blo 1397518 2099255 := bstep (se 1 (by rfl) ⟨1574441, by rfl⟩ : syracuseStep 2099255 = 3148883) B3148883
theorem B3360865 : Blo 1397518 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B86141191 : Blo 1397518 86141191 := bstep (se 1 (by rfl) ⟨64605893, by rfl⟩ : syracuseStep 86141191 = 129211787) B129211787
theorem B3148379 : Blo 1397518 3148379 := bstep (se 1 (by rfl) ⟨2361284, by rfl⟩ : syracuseStep 3148379 = 4722569) B4722569
theorem B3148415 : Blo 1397518 3148415 := bstep (se 1 (by rfl) ⟨2361311, by rfl⟩ : syracuseStep 3148415 = 4722623) B4722623
theorem B5311615 : Blo 1397518 5311615 := bstep (se 1 (by rfl) ⟨3983711, by rfl⟩ : syracuseStep 5311615 = 7967423) B7967423
theorem B10620071 : Blo 1397518 10620071 := bstep (se 1 (by rfl) ⟨7965053, by rfl⟩ : syracuseStep 10620071 = 15930107) B15930107
theorem B7556581 : Blo 1397518 7556581 := bstep (se 4 (by rfl) ⟨708429, by rfl⟩ : syracuseStep 7556581 = 1416859) B1416859
theorem B13446647 : Blo 1397518 13446647 := bstep (se 1 (by rfl) ⟨10084985, by rfl⟩ : syracuseStep 13446647 = 20169971) B20169971
theorem B23318513 : Blo 1397518 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B2240633 : Blo 1397518 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B8958431 : Blo 1397518 8958431 := bstep (se 1 (by rfl) ⟨6718823, by rfl⟩ : syracuseStep 8958431 = 13437647) B13437647
theorem B265335533 : Blo 1397518 265335533 := bstep (se 3 (by rfl) ⟨49750412, by rfl⟩ : syracuseStep 265335533 = 99500825) B99500825
theorem B1397535 : Blo 1397518 1397535 := bstep (se 1 (by rfl) ⟨1048151, by rfl⟩ : syracuseStep 1397535 = 2096303) B2096303
theorem B13448105 : Blo 1397518 13448105 := bstep (se 2 (by rfl) ⟨5043039, by rfl⟩ : syracuseStep 13448105 = 10086079) B10086079
theorem B1397807 : Blo 1397518 1397807 := bstep (se 1 (by rfl) ⟨1048355, by rfl⟩ : syracuseStep 1397807 = 2096711) B2096711
theorem B1398015 : Blo 1397518 1398015 := bstep (se 1 (by rfl) ⟨1048511, by rfl⟩ : syracuseStep 1398015 = 2097023) B2097023
theorem B32315233 : Blo 1397518 32315233 := bstep (se 2 (by rfl) ⟨12118212, by rfl⟩ : syracuseStep 32315233 = 24236425) B24236425
theorem B1398695 : Blo 1397518 1398695 := bstep (se 1 (by rfl) ⟨1049021, by rfl⟩ : syracuseStep 1398695 = 2098043) B2098043
theorem B1398783 : Blo 1397518 1398783 := bstep (se 1 (by rfl) ⟨1049087, by rfl⟩ : syracuseStep 1398783 = 2098175) B2098175
theorem B7969063 : Blo 1397518 7969063 := bstep (se 1 (by rfl) ⟨5976797, by rfl⟩ : syracuseStep 7969063 = 11953595) B11953595
theorem B17922707 : Blo 1397518 17922707 := bstep (se 1 (by rfl) ⟨13442030, by rfl⟩ : syracuseStep 17922707 = 26884061) B26884061
theorem B1399451 : Blo 1397518 1399451 := bstep (se 1 (by rfl) ⟨1049588, by rfl⟩ : syracuseStep 1399451 = 2099177) B2099177
theorem B1399463 : Blo 1397518 1399463 := bstep (se 1 (by rfl) ⟨1049597, by rfl⟩ : syracuseStep 1399463 = 2099195) B2099195
theorem B34003921 : Blo 1397518 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B9567305 : Blo 1397518 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B2358409 : Blo 1397518 2358409 := bstep (se 2 (by rfl) ⟨884403, by rfl⟩ : syracuseStep 2358409 = 1768807) B1768807
theorem B2358463 : Blo 1397518 2358463 := bstep (se 1 (by rfl) ⟨1768847, by rfl⟩ : syracuseStep 2358463 = 3537695) B3537695
theorem B4717979 : Blo 1397518 4717979 := bstep (se 1 (by rfl) ⟨3538484, by rfl⟩ : syracuseStep 4717979 = 7076969) B7076969
theorem B2096543 : Blo 1397518 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B10624445 : Blo 1397518 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B54492659 : Blo 1397518 54492659 := bstep (se 1 (by rfl) ⟨40869494, by rfl⟩ : syracuseStep 54492659 = 81738989) B81738989
theorem B3980819 : Blo 1397518 3980819 := bstep (se 1 (by rfl) ⟨2985614, by rfl⟩ : syracuseStep 3980819 = 5971229) B5971229
theorem B4480703 : Blo 1397518 4480703 := bstep (se 1 (by rfl) ⟨3360527, by rfl⟩ : syracuseStep 4480703 = 6721055) B6721055
theorem B2097065 : Blo 1397518 2097065 := bstep (se 2 (by rfl) ⟨786399, by rfl⟩ : syracuseStep 2097065 = 1572799) B1572799
theorem B2359273 : Blo 1397518 2359273 := bstep (se 2 (by rfl) ⟨884727, by rfl⟩ : syracuseStep 2359273 = 1769455) B1769455
theorem B4481153 : Blo 1397518 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B1769627 : Blo 1397518 1769627 := bstep (se 1 (by rfl) ⟨1327220, by rfl⟩ : syracuseStep 1769627 = 2654441) B2654441
theorem B7078103 : Blo 1397518 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B3145967 : Blo 1397518 3145967 := bstep (se 1 (by rfl) ⟨2359475, by rfl⟩ : syracuseStep 3145967 = 4718951) B4718951
theorem B3146039 : Blo 1397518 3146039 := bstep (se 1 (by rfl) ⟨2359529, by rfl⟩ : syracuseStep 3146039 = 4719059) B4719059
theorem B5972287 : Blo 1397518 5972287 := bstep (se 1 (by rfl) ⟨4479215, by rfl⟩ : syracuseStep 5972287 = 8958431) B8958431
theorem B10625417 : Blo 1397518 10625417 := bstep (se 2 (by rfl) ⟨3984531, by rfl⟩ : syracuseStep 10625417 = 7969063) B7969063
theorem B3146219 : Blo 1397518 3146219 := bstep (se 1 (by rfl) ⟨2359664, by rfl⟩ : syracuseStep 3146219 = 4719329) B4719329
theorem B176890355 : Blo 1397518 176890355 := bstep (se 1 (by rfl) ⟨132667766, by rfl⟩ : syracuseStep 176890355 = 265335533) B265335533
theorem B2097719 : Blo 1397518 2097719 := bstep (se 1 (by rfl) ⟨1573289, by rfl⟩ : syracuseStep 2097719 = 3146579) B3146579
theorem B4309595 : Blo 1397518 4309595 := bstep (se 1 (by rfl) ⟨3232196, by rfl⟩ : syracuseStep 4309595 = 6464393) B6464393
theorem B4719707 : Blo 1397518 4719707 := bstep (se 1 (by rfl) ⟨3539780, by rfl⟩ : syracuseStep 4719707 = 7079561) B7079561
theorem B3147119 : Blo 1397518 3147119 := bstep (se 1 (by rfl) ⟨2360339, by rfl⟩ : syracuseStep 3147119 = 4720679) B4720679
theorem B2098553 : Blo 1397518 2098553 := bstep (se 2 (by rfl) ⟨786957, by rfl⟩ : syracuseStep 2098553 = 1573915) B1573915
theorem B2098919 : Blo 1397518 2098919 := bstep (se 1 (by rfl) ⟨1574189, by rfl⟩ : syracuseStep 2098919 = 3148379) B3148379
theorem B2098943 : Blo 1397518 2098943 := bstep (se 1 (by rfl) ⟨1574207, by rfl⟩ : syracuseStep 2098943 = 3148415) B3148415
theorem B7080047 : Blo 1397518 7080047 := bstep (se 1 (by rfl) ⟨5310035, by rfl⟩ : syracuseStep 7080047 = 10620071) B10620071
theorem B8964431 : Blo 1397518 8964431 := bstep (se 1 (by rfl) ⟨6723323, by rfl⟩ : syracuseStep 8964431 = 13446647) B13446647
theorem B827370449 : Blo 1397518 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B5975021 : Blo 1397518 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B114854921 : Blo 1397518 114854921 := bstep (se 2 (by rfl) ⟨43070595, by rfl⟩ : syracuseStep 114854921 = 86141191) B86141191
theorem B11939075 : Blo 1397518 11939075 := bstep (se 1 (by rfl) ⟨8954306, by rfl⟩ : syracuseStep 11939075 = 17908613) B17908613
theorem B8965403 : Blo 1397518 8965403 := bstep (se 1 (by rfl) ⟨6724052, by rfl⟩ : syracuseStep 8965403 = 13448105) B13448105
theorem B2125295 : Blo 1397518 2125295 := bstep (se 1 (by rfl) ⟨1593971, by rfl⟩ : syracuseStep 2125295 = 3187943) B3187943
theorem B28716767 : Blo 1397518 28716767 := bstep (se 1 (by rfl) ⟨21537575, by rfl⟩ : syracuseStep 28716767 = 43075151) B43075151
theorem B45338561 : Blo 1397518 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B28717087 : Blo 1397518 28717087 := bstep (se 1 (by rfl) ⟨21537815, by rfl⟩ : syracuseStep 28717087 = 43075631) B43075631
theorem B7082153 : Blo 1397518 7082153 := bstep (se 2 (by rfl) ⟨2655807, by rfl⟩ : syracuseStep 7082153 = 5311615) B5311615
theorem B11948471 : Blo 1397518 11948471 := bstep (se 1 (by rfl) ⟨8961353, by rfl⟩ : syracuseStep 11948471 = 17922707) B17922707
theorem B6378203 : Blo 1397518 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B1397695 : Blo 1397518 1397695 := bstep (se 1 (by rfl) ⟨1048271, by rfl⟩ : syracuseStep 1397695 = 2096543) B2096543
theorem B7082963 : Blo 1397518 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B36328439 : Blo 1397518 36328439 := bstep (se 1 (by rfl) ⟨27246329, by rfl⟩ : syracuseStep 36328439 = 54492659) B54492659
theorem B2987135 : Blo 1397518 2987135 := bstep (se 1 (by rfl) ⟨2240351, by rfl⟩ : syracuseStep 2987135 = 4480703) B4480703
theorem B43086977 : Blo 1397518 43086977 := bstep (se 2 (by rfl) ⟨16157616, by rfl⟩ : syracuseStep 43086977 = 32315233) B32315233
theorem B1398043 : Blo 1397518 1398043 := bstep (se 1 (by rfl) ⟨1048532, by rfl⟩ : syracuseStep 1398043 = 2097065) B2097065
theorem B15545675 : Blo 1397518 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B1398503 : Blo 1397518 1398503 := bstep (se 1 (by rfl) ⟨1048877, by rfl⟩ : syracuseStep 1398503 = 2097755) B2097755
theorem B1398555 : Blo 1397518 1398555 := bstep (se 1 (by rfl) ⟨1048916, by rfl⟩ : syracuseStep 1398555 = 2097833) B2097833
theorem B2987887 : Blo 1397518 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B1398895 : Blo 1397518 1398895 := bstep (se 1 (by rfl) ⟨1049171, by rfl⟩ : syracuseStep 1398895 = 2098343) B2098343
theorem B1399503 : Blo 1397518 1399503 := bstep (se 1 (by rfl) ⟨1049627, by rfl⟩ : syracuseStep 1399503 = 2099255) B2099255
theorem B3144545 : Blo 1397518 3144545 := bstep (se 2 (by rfl) ⟨1179204, by rfl⟩ : syracuseStep 3144545 = 2358409) B2358409
theorem B3144617 : Blo 1397518 3144617 := bstep (se 2 (by rfl) ⟨1179231, by rfl⟩ : syracuseStep 3144617 = 2358463) B2358463
theorem B10075441 : Blo 1397518 10075441 := bstep (se 2 (by rfl) ⟨3778290, by rfl⟩ : syracuseStep 10075441 = 7556581) B7556581
theorem B3145319 : Blo 1397518 3145319 := bstep (se 1 (by rfl) ⟨2358989, by rfl⟩ : syracuseStep 3145319 = 4717979) B4717979
theorem B2653879 : Blo 1397518 2653879 := bstep (se 1 (by rfl) ⟨1990409, by rfl⟩ : syracuseStep 2653879 = 3980819) B3980819
theorem B3145697 : Blo 1397518 3145697 := bstep (se 2 (by rfl) ⟨1179636, by rfl⟩ : syracuseStep 3145697 = 2359273) B2359273
theorem B38289449 : Blo 1397518 38289449 := bstep (se 2 (by rfl) ⟨14358543, by rfl⟩ : syracuseStep 38289449 = 28717087) B28717087
theorem B4718735 : Blo 1397518 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B2097311 : Blo 1397518 2097311 := bstep (se 1 (by rfl) ⟨1572983, by rfl⟩ : syracuseStep 2097311 = 3145967) B3145967
theorem B2097359 : Blo 1397518 2097359 := bstep (se 1 (by rfl) ⟨1573019, by rfl⟩ : syracuseStep 2097359 = 3146039) B3146039
theorem B2097479 : Blo 1397518 2097479 := bstep (se 1 (by rfl) ⟨1573109, by rfl⟩ : syracuseStep 2097479 = 3146219) B3146219
theorem B4719005 : Blo 1397518 4719005 := bstep (se 3 (by rfl) ⟨884813, by rfl⟩ : syracuseStep 4719005 = 1769627) B1769627
theorem B7963049 : Blo 1397518 7963049 := bstep (se 2 (by rfl) ⟨2986143, by rfl⟩ : syracuseStep 7963049 = 5972287) B5972287
theorem B3146471 : Blo 1397518 3146471 := bstep (se 1 (by rfl) ⟨2359853, by rfl⟩ : syracuseStep 3146471 = 4719707) B4719707
theorem B1991423 : Blo 1397518 1991423 := bstep (se 1 (by rfl) ⟨1493567, by rfl⟩ : syracuseStep 1991423 = 2987135) B2987135
theorem B10363783 : Blo 1397518 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B2098079 : Blo 1397518 2098079 := bstep (se 1 (by rfl) ⟨1573559, by rfl⟩ : syracuseStep 2098079 = 3147119) B3147119
theorem B4720031 : Blo 1397518 4720031 := bstep (se 1 (by rfl) ⟨3540023, by rfl⟩ : syracuseStep 4720031 = 7080047) B7080047
theorem B17008541 : Blo 1397518 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B3983347 : Blo 1397518 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B3983849 : Blo 1397518 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B4721435 : Blo 1397518 4721435 := bstep (se 1 (by rfl) ⟨3541076, by rfl⟩ : syracuseStep 4721435 = 7082153) B7082153
theorem B7965647 : Blo 1397518 7965647 := bstep (se 1 (by rfl) ⟨5974235, by rfl⟩ : syracuseStep 7965647 = 11948471) B11948471
theorem B117926903 : Blo 1397518 117926903 := bstep (se 1 (by rfl) ⟨88445177, by rfl⟩ : syracuseStep 117926903 = 176890355) B176890355
theorem B4721975 : Blo 1397518 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B24218959 : Blo 1397518 24218959 := bstep (se 1 (by rfl) ⟨18164219, by rfl⟩ : syracuseStep 24218959 = 36328439) B36328439
theorem B28724651 : Blo 1397518 28724651 := bstep (se 1 (by rfl) ⟨21543488, by rfl⟩ : syracuseStep 28724651 = 43086977) B43086977
theorem B5976287 : Blo 1397518 5976287 := bstep (se 1 (by rfl) ⟨4482215, by rfl⟩ : syracuseStep 5976287 = 8964431) B8964431
theorem B551580299 : Blo 1397518 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B7959383 : Blo 1397518 7959383 := bstep (se 1 (by rfl) ⟨5969537, by rfl⟩ : syracuseStep 7959383 = 11939075) B11939075
theorem B5976935 : Blo 1397518 5976935 := bstep (se 1 (by rfl) ⟨4482701, by rfl⟩ : syracuseStep 5976935 = 8965403) B8965403
theorem B30225707 : Blo 1397518 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B2987435 : Blo 1397518 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B7083611 : Blo 1397518 7083611 := bstep (se 1 (by rfl) ⟨5312708, by rfl⟩ : syracuseStep 7083611 = 10625417) B10625417
theorem B1398479 : Blo 1397518 1398479 := bstep (se 1 (by rfl) ⟨1048859, by rfl⟩ : syracuseStep 1398479 = 2097719) B2097719
theorem B2873063 : Blo 1397518 2873063 := bstep (se 1 (by rfl) ⟨2154797, by rfl⟩ : syracuseStep 2873063 = 4309595) B4309595
theorem B1399035 : Blo 1397518 1399035 := bstep (se 1 (by rfl) ⟨1049276, by rfl⟩ : syracuseStep 1399035 = 2098553) B2098553
theorem B1399279 : Blo 1397518 1399279 := bstep (se 1 (by rfl) ⟨1049459, by rfl⟩ : syracuseStep 1399279 = 2098919) B2098919
theorem B1399295 : Blo 1397518 1399295 := bstep (se 1 (by rfl) ⟨1049471, by rfl⟩ : syracuseStep 1399295 = 2098943) B2098943
theorem B13433921 : Blo 1397518 13433921 := bstep (se 2 (by rfl) ⟨5037720, by rfl⟩ : syracuseStep 13433921 = 10075441) B10075441
theorem B2096363 : Blo 1397518 2096363 := bstep (se 1 (by rfl) ⟨1572272, by rfl⟩ : syracuseStep 2096363 = 3144545) B3144545
theorem B2096411 : Blo 1397518 2096411 := bstep (se 1 (by rfl) ⟨1572308, by rfl⟩ : syracuseStep 2096411 = 3144617) B3144617
theorem B76569947 : Blo 1397518 76569947 := bstep (se 1 (by rfl) ⟨57427460, by rfl⟩ : syracuseStep 76569947 = 114854921) B114854921
theorem B3538505 : Blo 1397518 3538505 := bstep (se 2 (by rfl) ⟨1326939, by rfl⟩ : syracuseStep 3538505 = 2653879) B2653879
theorem B1416863 : Blo 1397518 1416863 := bstep (se 1 (by rfl) ⟨1062647, by rfl⟩ : syracuseStep 1416863 = 2125295) B2125295
theorem B2096879 : Blo 1397518 2096879 := bstep (se 1 (by rfl) ⟨1572659, by rfl⟩ : syracuseStep 2096879 = 3145319) B3145319
theorem B19144511 : Blo 1397518 19144511 := bstep (se 1 (by rfl) ⟨14358383, by rfl⟩ : syracuseStep 19144511 = 28716767) B28716767
theorem B2097131 : Blo 1397518 2097131 := bstep (se 1 (by rfl) ⟨1572848, by rfl⟩ : syracuseStep 2097131 = 3145697) B3145697
theorem B25526299 : Blo 1397518 25526299 := bstep (se 1 (by rfl) ⟨19144724, by rfl⟩ : syracuseStep 25526299 = 38289449) B38289449
theorem B3145823 : Blo 1397518 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B3146003 : Blo 1397518 3146003 := bstep (se 1 (by rfl) ⟨2359502, by rfl⟩ : syracuseStep 3146003 = 4719005) B4719005
theorem B5308699 : Blo 1397518 5308699 := bstep (se 1 (by rfl) ⟨3981524, by rfl⟩ : syracuseStep 5308699 = 7963049) B7963049
theorem B2097647 : Blo 1397518 2097647 := bstep (se 1 (by rfl) ⟨1573235, by rfl⟩ : syracuseStep 2097647 = 3146471) B3146471
theorem B3146687 : Blo 1397518 3146687 := bstep (se 1 (by rfl) ⟨2360015, by rfl⟩ : syracuseStep 3146687 = 4720031) B4720031
theorem B1991623 : Blo 1397518 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B11339027 : Blo 1397518 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B2655899 : Blo 1397518 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B3778301 : Blo 1397518 3778301 := bstep (se 3 (by rfl) ⟨708431, by rfl⟩ : syracuseStep 3778301 = 1416863) B1416863
theorem B3147623 : Blo 1397518 3147623 := bstep (se 1 (by rfl) ⟨2360717, by rfl⟩ : syracuseStep 3147623 = 4721435) B4721435
theorem B5310431 : Blo 1397518 5310431 := bstep (se 1 (by rfl) ⟨3982823, by rfl⟩ : syracuseStep 5310431 = 7965647) B7965647
theorem B5310461 : Blo 1397518 5310461 := bstep (se 3 (by rfl) ⟨995711, by rfl⟩ : syracuseStep 5310461 = 1991423) B1991423
theorem B8955947 : Blo 1397518 8955947 := bstep (se 1 (by rfl) ⟨6716960, by rfl⟩ : syracuseStep 8955947 = 13433921) B13433921
theorem B3147983 : Blo 1397518 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B51046631 : Blo 1397518 51046631 := bstep (se 1 (by rfl) ⟨38284973, by rfl⟩ : syracuseStep 51046631 = 76569947) B76569947
theorem B5311129 : Blo 1397518 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B3984191 : Blo 1397518 3984191 := bstep (se 1 (by rfl) ⟨2988143, by rfl⟩ : syracuseStep 3984191 = 5976287) B5976287
theorem B3984623 : Blo 1397518 3984623 := bstep (se 1 (by rfl) ⟨2988467, by rfl⟩ : syracuseStep 3984623 = 5976935) B5976935
theorem B4722407 : Blo 1397518 4722407 := bstep (se 1 (by rfl) ⟨3541805, by rfl⟩ : syracuseStep 4722407 = 7083611) B7083611
theorem B1397575 : Blo 1397518 1397575 := bstep (se 1 (by rfl) ⟨1048181, by rfl⟩ : syracuseStep 1397575 = 2096363) B2096363
theorem B1397607 : Blo 1397518 1397607 := bstep (se 1 (by rfl) ⟨1048205, by rfl⟩ : syracuseStep 1397607 = 2096411) B2096411
theorem B19149767 : Blo 1397518 19149767 := bstep (se 1 (by rfl) ⟨14362325, by rfl⟩ : syracuseStep 19149767 = 28724651) B28724651
theorem B1397919 : Blo 1397518 1397919 := bstep (se 1 (by rfl) ⟨1048439, by rfl⟩ : syracuseStep 1397919 = 2096879) B2096879
theorem B1398087 : Blo 1397518 1398087 := bstep (se 1 (by rfl) ⟨1048565, by rfl⟩ : syracuseStep 1398087 = 2097131) B2097131
theorem B1398207 : Blo 1397518 1398207 := bstep (se 1 (by rfl) ⟨1048655, by rfl⟩ : syracuseStep 1398207 = 2097311) B2097311
theorem B1398239 : Blo 1397518 1398239 := bstep (se 1 (by rfl) ⟨1048679, by rfl⟩ : syracuseStep 1398239 = 2097359) B2097359
theorem B1398319 : Blo 1397518 1398319 := bstep (se 1 (by rfl) ⟨1048739, by rfl⟩ : syracuseStep 1398319 = 2097479) B2097479
theorem B367720199 : Blo 1397518 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B5306255 : Blo 1397518 5306255 := bstep (se 1 (by rfl) ⟨3979691, by rfl⟩ : syracuseStep 5306255 = 7959383) B7959383
theorem B1398719 : Blo 1397518 1398719 := bstep (se 1 (by rfl) ⟨1049039, by rfl⟩ : syracuseStep 1398719 = 2098079) B2098079
theorem B20150471 : Blo 1397518 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B1915375 : Blo 1397518 1915375 := bstep (se 1 (by rfl) ⟨1436531, by rfl⟩ : syracuseStep 1915375 = 2873063) B2873063
theorem B13818377 : Blo 1397518 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B32291945 : Blo 1397518 32291945 := bstep (se 2 (by rfl) ⟨12109479, by rfl⟩ : syracuseStep 32291945 = 24218959) B24218959
theorem B78617935 : Blo 1397518 78617935 := bstep (se 1 (by rfl) ⟨58963451, by rfl⟩ : syracuseStep 78617935 = 117926903) B117926903
theorem B2359003 : Blo 1397518 2359003 := bstep (se 1 (by rfl) ⟨1769252, by rfl⟩ : syracuseStep 2359003 = 3538505) B3538505
theorem B12763007 : Blo 1397518 12763007 := bstep (se 1 (by rfl) ⟨9572255, by rfl⟩ : syracuseStep 12763007 = 19144511) B19144511
theorem B2097215 : Blo 1397518 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B2097335 : Blo 1397518 2097335 := bstep (se 1 (by rfl) ⟨1573001, by rfl⟩ : syracuseStep 2097335 = 3146003) B3146003
theorem B7078265 : Blo 1397518 7078265 := bstep (se 2 (by rfl) ⟨2654349, by rfl⟩ : syracuseStep 7078265 = 5308699) B5308699
theorem B2097791 : Blo 1397518 2097791 := bstep (se 1 (by rfl) ⟨1573343, by rfl⟩ : syracuseStep 2097791 = 3146687) B3146687
theorem B1770599 : Blo 1397518 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B245146799 : Blo 1397518 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B2098415 : Blo 1397518 2098415 := bstep (se 1 (by rfl) ⟨1573811, by rfl⟩ : syracuseStep 2098415 = 3147623) B3147623
theorem B2655497 : Blo 1397518 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B3540287 : Blo 1397518 3540287 := bstep (se 1 (by rfl) ⟨2655215, by rfl⟩ : syracuseStep 3540287 = 5310431) B5310431
theorem B3540307 : Blo 1397518 3540307 := bstep (se 1 (by rfl) ⟨2655230, by rfl⟩ : syracuseStep 3540307 = 5310461) B5310461
theorem B36849005 : Blo 1397518 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B2098655 : Blo 1397518 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B34031087 : Blo 1397518 34031087 := bstep (se 1 (by rfl) ⟨25523315, by rfl⟩ : syracuseStep 34031087 = 51046631) B51046631
theorem B2656127 : Blo 1397518 2656127 := bstep (se 1 (by rfl) ⟨1992095, by rfl⟩ : syracuseStep 2656127 = 3984191) B3984191
theorem B2656415 : Blo 1397518 2656415 := bstep (se 1 (by rfl) ⟨1992311, by rfl⟩ : syracuseStep 2656415 = 3984623) B3984623
theorem B3148271 : Blo 1397518 3148271 := bstep (se 1 (by rfl) ⟨2361203, by rfl⟩ : syracuseStep 3148271 = 4722407) B4722407
theorem B53734589 : Blo 1397518 53734589 := bstep (se 3 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 53734589 = 20150471) B20150471
theorem B12766511 : Blo 1397518 12766511 := bstep (se 1 (by rfl) ⟨9574883, by rfl⟩ : syracuseStep 12766511 = 19149767) B19149767
theorem B7081505 : Blo 1397518 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B2518867 : Blo 1397518 2518867 := bstep (se 1 (by rfl) ⟨1889150, by rfl⟩ : syracuseStep 2518867 = 3778301) B3778301
theorem B419295653 : Blo 1397518 419295653 := bstep (se 4 (by rfl) ⟨39308967, by rfl⟩ : syracuseStep 419295653 = 78617935) B78617935
theorem B8508671 : Blo 1397518 8508671 := bstep (se 1 (by rfl) ⟨6381503, by rfl⟩ : syracuseStep 8508671 = 12763007) B12763007
theorem B34035065 : Blo 1397518 34035065 := bstep (se 2 (by rfl) ⟨12763149, by rfl⟩ : syracuseStep 34035065 = 25526299) B25526299
theorem B1398431 : Blo 1397518 1398431 := bstep (se 1 (by rfl) ⟨1048823, by rfl⟩ : syracuseStep 1398431 = 2097647) B2097647
theorem B2553833 : Blo 1397518 2553833 := bstep (se 2 (by rfl) ⟨957687, by rfl⟩ : syracuseStep 2553833 = 1915375) B1915375
theorem B7559351 : Blo 1397518 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B3537503 : Blo 1397518 3537503 := bstep (se 1 (by rfl) ⟨2653127, by rfl⟩ : syracuseStep 3537503 = 5306255) B5306255
theorem B5970631 : Blo 1397518 5970631 := bstep (se 1 (by rfl) ⟨4477973, by rfl⟩ : syracuseStep 5970631 = 8955947) B8955947
theorem B21527963 : Blo 1397518 21527963 := bstep (se 1 (by rfl) ⟨16145972, by rfl⟩ : syracuseStep 21527963 = 32291945) B32291945
theorem B3145337 : Blo 1397518 3145337 := bstep (se 2 (by rfl) ⟨1179501, by rfl⟩ : syracuseStep 3145337 = 2359003) B2359003
theorem B4718843 : Blo 1397518 4718843 := bstep (se 1 (by rfl) ⟨3539132, by rfl⟩ : syracuseStep 4718843 = 7078265) B7078265
theorem B163431199 : Blo 1397518 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B1770331 : Blo 1397518 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B2360191 : Blo 1397518 2360191 := bstep (se 1 (by rfl) ⟨1770143, by rfl⟩ : syracuseStep 2360191 = 3540287) B3540287
theorem B1770751 : Blo 1397518 1770751 := bstep (se 1 (by rfl) ⟨1328063, by rfl⟩ : syracuseStep 1770751 = 2656127) B2656127
theorem B5039567 : Blo 1397518 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B2098847 : Blo 1397518 2098847 := bstep (se 1 (by rfl) ⟨1574135, by rfl⟩ : syracuseStep 2098847 = 3148271) B3148271
theorem B4720409 : Blo 1397518 4720409 := bstep (se 2 (by rfl) ⟨1770153, by rfl⟩ : syracuseStep 4720409 = 3540307) B3540307
theorem B4721003 : Blo 1397518 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B4721597 : Blo 1397518 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B279530435 : Blo 1397518 279530435 := bstep (se 1 (by rfl) ⟨209647826, by rfl⟩ : syracuseStep 279530435 = 419295653) B419295653
theorem B5672447 : Blo 1397518 5672447 := bstep (se 1 (by rfl) ⟨4254335, by rfl⟩ : syracuseStep 5672447 = 8508671) B8508671
theorem B22687391 : Blo 1397518 22687391 := bstep (se 1 (by rfl) ⟨17015543, by rfl⟩ : syracuseStep 22687391 = 34031087) B34031087
theorem B1398143 : Blo 1397518 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B1398223 : Blo 1397518 1398223 := bstep (se 1 (by rfl) ⟨1048667, by rfl⟩ : syracuseStep 1398223 = 2097335) B2097335
theorem B7083773 : Blo 1397518 7083773 := bstep (se 3 (by rfl) ⟨1328207, by rfl⟩ : syracuseStep 7083773 = 2656415) B2656415
theorem B1398527 : Blo 1397518 1398527 := bstep (se 1 (by rfl) ⟨1048895, by rfl⟩ : syracuseStep 1398527 = 2097791) B2097791
theorem B1398943 : Blo 1397518 1398943 := bstep (se 1 (by rfl) ⟨1049207, by rfl⟩ : syracuseStep 1398943 = 2098415) B2098415
theorem B24566003 : Blo 1397518 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B22690043 : Blo 1397518 22690043 := bstep (se 1 (by rfl) ⟨17017532, by rfl⟩ : syracuseStep 22690043 = 34035065) B34035065
theorem B7960841 : Blo 1397518 7960841 := bstep (se 2 (by rfl) ⟨2985315, by rfl⟩ : syracuseStep 7960841 = 5970631) B5970631
theorem B1399103 : Blo 1397518 1399103 := bstep (se 1 (by rfl) ⟨1049327, by rfl⟩ : syracuseStep 1399103 = 2098655) B2098655
theorem B1702555 : Blo 1397518 1702555 := bstep (se 1 (by rfl) ⟨1276916, by rfl⟩ : syracuseStep 1702555 = 2553833) B2553833
theorem B2358335 : Blo 1397518 2358335 := bstep (se 1 (by rfl) ⟨1768751, by rfl⟩ : syracuseStep 2358335 = 3537503) B3537503
theorem B13433957 : Blo 1397518 13433957 := bstep (se 4 (by rfl) ⟨1259433, by rfl⟩ : syracuseStep 13433957 = 2518867) B2518867
theorem B35823059 : Blo 1397518 35823059 := bstep (se 1 (by rfl) ⟨26867294, by rfl⟩ : syracuseStep 35823059 = 53734589) B53734589
theorem B8511007 : Blo 1397518 8511007 := bstep (se 1 (by rfl) ⟨6383255, by rfl⟩ : syracuseStep 8511007 = 12766511) B12766511
theorem B14351975 : Blo 1397518 14351975 := bstep (se 1 (by rfl) ⟨10763981, by rfl⟩ : syracuseStep 14351975 = 21527963) B21527963
theorem B2096891 : Blo 1397518 2096891 := bstep (se 1 (by rfl) ⟨1572668, by rfl⟩ : syracuseStep 2096891 = 3145337) B3145337
theorem B3145895 : Blo 1397518 3145895 := bstep (se 1 (by rfl) ⟨2359421, by rfl⟩ : syracuseStep 3145895 = 4718843) B4718843
theorem B3359711 : Blo 1397518 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B217908265 : Blo 1397518 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B2360441 : Blo 1397518 2360441 := bstep (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) B1770331
theorem B3146921 : Blo 1397518 3146921 := bstep (se 2 (by rfl) ⟨1180095, by rfl⟩ : syracuseStep 3146921 = 2360191) B2360191
theorem B3146939 : Blo 1397518 3146939 := bstep (se 1 (by rfl) ⟨2360204, by rfl⟩ : syracuseStep 3146939 = 4720409) B4720409
theorem B16377335 : Blo 1397518 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B3147335 : Blo 1397518 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B2361001 : Blo 1397518 2361001 := bstep (se 2 (by rfl) ⟨885375, by rfl⟩ : syracuseStep 2361001 = 1770751) B1770751
theorem B3147731 : Blo 1397518 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B186353623 : Blo 1397518 186353623 := bstep (se 1 (by rfl) ⟨139765217, by rfl⟩ : syracuseStep 186353623 = 279530435) B279530435
theorem B11348009 : Blo 1397518 11348009 := bstep (se 2 (by rfl) ⟨4255503, by rfl⟩ : syracuseStep 11348009 = 8511007) B8511007
theorem B8955971 : Blo 1397518 8955971 := bstep (se 1 (by rfl) ⟨6716978, by rfl⟩ : syracuseStep 8955971 = 13433957) B13433957
theorem B23882039 : Blo 1397518 23882039 := bstep (se 1 (by rfl) ⟨17911529, by rfl⟩ : syracuseStep 23882039 = 35823059) B35823059
theorem B15124927 : Blo 1397518 15124927 := bstep (se 1 (by rfl) ⟨11343695, by rfl⟩ : syracuseStep 15124927 = 22687391) B22687391
theorem B4722515 : Blo 1397518 4722515 := bstep (se 1 (by rfl) ⟨3541886, by rfl⟩ : syracuseStep 4722515 = 7083773) B7083773
theorem B15126695 : Blo 1397518 15126695 := bstep (se 1 (by rfl) ⟨11345021, by rfl⟩ : syracuseStep 15126695 = 22690043) B22690043
theorem B3781631 : Blo 1397518 3781631 := bstep (se 1 (by rfl) ⟨2836223, by rfl⟩ : syracuseStep 3781631 = 5672447) B5672447
theorem B1397927 : Blo 1397518 1397927 := bstep (se 1 (by rfl) ⟨1048445, by rfl⟩ : syracuseStep 1397927 = 2096891) B2096891
theorem B36321173 : Blo 1397518 36321173 := bstep (se 6 (by rfl) ⟨851277, by rfl⟩ : syracuseStep 36321173 = 1702555) B1702555
theorem B1399231 : Blo 1397518 1399231 := bstep (se 1 (by rfl) ⟨1049423, by rfl⟩ : syracuseStep 1399231 = 2098847) B2098847
theorem B5307227 : Blo 1397518 5307227 := bstep (se 1 (by rfl) ⟨3980420, by rfl⟩ : syracuseStep 5307227 = 7960841) B7960841
theorem B1572223 : Blo 1397518 1572223 := bstep (se 1 (by rfl) ⟨1179167, by rfl⟩ : syracuseStep 1572223 = 2358335) B2358335
theorem B9567983 : Blo 1397518 9567983 := bstep (se 1 (by rfl) ⟨7175987, by rfl⟩ : syracuseStep 9567983 = 14351975) B14351975
theorem B2097263 : Blo 1397518 2097263 := bstep (se 1 (by rfl) ⟨1572947, by rfl⟩ : syracuseStep 2097263 = 3145895) B3145895
theorem B10084463 : Blo 1397518 10084463 := bstep (se 1 (by rfl) ⟨7563347, by rfl⟩ : syracuseStep 10084463 = 15126695) B15126695
theorem B1573627 : Blo 1397518 1573627 := bstep (se 1 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 1573627 = 2360441) B2360441
theorem B2097947 : Blo 1397518 2097947 := bstep (se 1 (by rfl) ⟨1573460, by rfl⟩ : syracuseStep 2097947 = 3146921) B3146921
theorem B2097959 : Blo 1397518 2097959 := bstep (se 1 (by rfl) ⟨1573469, by rfl⟩ : syracuseStep 2097959 = 3146939) B3146939
theorem B2098223 : Blo 1397518 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B2098487 : Blo 1397518 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B3148001 : Blo 1397518 3148001 := bstep (se 2 (by rfl) ⟨1180500, by rfl⟩ : syracuseStep 3148001 = 2361001) B2361001
theorem B3148343 : Blo 1397518 3148343 := bstep (se 1 (by rfl) ⟨2361257, by rfl⟩ : syracuseStep 3148343 = 4722515) B4722515
theorem B2239807 : Blo 1397518 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B7565339 : Blo 1397518 7565339 := bstep (se 1 (by rfl) ⟨5674004, by rfl⟩ : syracuseStep 7565339 = 11348009) B11348009
theorem B15921359 : Blo 1397518 15921359 := bstep (se 1 (by rfl) ⟨11941019, by rfl⟩ : syracuseStep 15921359 = 23882039) B23882039
theorem B25514621 : Blo 1397518 25514621 := bstep (se 3 (by rfl) ⟨4783991, by rfl⟩ : syracuseStep 25514621 = 9567983) B9567983
theorem B20166569 : Blo 1397518 20166569 := bstep (se 2 (by rfl) ⟨7562463, by rfl⟩ : syracuseStep 20166569 = 15124927) B15124927
theorem B2521087 : Blo 1397518 2521087 := bstep (se 1 (by rfl) ⟨1890815, by rfl⟩ : syracuseStep 2521087 = 3781631) B3781631
theorem B10918223 : Blo 1397518 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B24214115 : Blo 1397518 24214115 := bstep (se 1 (by rfl) ⟨18160586, by rfl⟩ : syracuseStep 24214115 = 36321173) B36321173
theorem B5970647 : Blo 1397518 5970647 := bstep (se 1 (by rfl) ⟨4477985, by rfl⟩ : syracuseStep 5970647 = 8955971) B8955971
theorem B290544353 : Blo 1397518 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B2096297 : Blo 1397518 2096297 := bstep (se 2 (by rfl) ⟨786111, by rfl⟩ : syracuseStep 2096297 = 1572223) B1572223
theorem B3538151 : Blo 1397518 3538151 := bstep (se 1 (by rfl) ⟨2653613, by rfl⟩ : syracuseStep 3538151 = 5307227) B5307227
theorem B248471497 : Blo 1397518 248471497 := bstep (se 2 (by rfl) ⟨93176811, by rfl⟩ : syracuseStep 248471497 = 186353623) B186353623
theorem B2098169 : Blo 1397518 2098169 := bstep (se 2 (by rfl) ⟨786813, by rfl⟩ : syracuseStep 2098169 = 1573627) B1573627
theorem B13444379 : Blo 1397518 13444379 := bstep (se 1 (by rfl) ⟨10083284, by rfl⟩ : syracuseStep 13444379 = 20166569) B20166569
theorem B2098667 : Blo 1397518 2098667 := bstep (se 1 (by rfl) ⟨1574000, by rfl⟩ : syracuseStep 2098667 = 3148001) B3148001
theorem B2098895 : Blo 1397518 2098895 := bstep (se 1 (by rfl) ⟨1574171, by rfl⟩ : syracuseStep 2098895 = 3148343) B3148343
theorem B331295329 : Blo 1397518 331295329 := bstep (se 2 (by rfl) ⟨124235748, by rfl⟩ : syracuseStep 331295329 = 248471497) B248471497
theorem B13445797 : Blo 1397518 13445797 := bstep (se 4 (by rfl) ⟨1260543, by rfl⟩ : syracuseStep 13445797 = 2521087) B2521087
theorem B17009747 : Blo 1397518 17009747 := bstep (se 1 (by rfl) ⟨12757310, by rfl⟩ : syracuseStep 17009747 = 25514621) B25514621
theorem B7278815 : Blo 1397518 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B16142743 : Blo 1397518 16142743 := bstep (se 1 (by rfl) ⟨12107057, by rfl⟩ : syracuseStep 16142743 = 24214115) B24214115
theorem B2986409 : Blo 1397518 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B193696235 : Blo 1397518 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B1397531 : Blo 1397518 1397531 := bstep (se 1 (by rfl) ⟨1048148, by rfl⟩ : syracuseStep 1397531 = 2096297) B2096297
theorem B5043559 : Blo 1397518 5043559 := bstep (se 1 (by rfl) ⟨3782669, by rfl⟩ : syracuseStep 5043559 = 7565339) B7565339
theorem B1398175 : Blo 1397518 1398175 := bstep (se 1 (by rfl) ⟨1048631, by rfl⟩ : syracuseStep 1398175 = 2097263) B2097263
theorem B6722975 : Blo 1397518 6722975 := bstep (se 1 (by rfl) ⟨5042231, by rfl⟩ : syracuseStep 6722975 = 10084463) B10084463
theorem B10614239 : Blo 1397518 10614239 := bstep (se 1 (by rfl) ⟨7960679, by rfl⟩ : syracuseStep 10614239 = 15921359) B15921359
theorem B1398631 : Blo 1397518 1398631 := bstep (se 1 (by rfl) ⟨1048973, by rfl⟩ : syracuseStep 1398631 = 2097947) B2097947
theorem B1398639 : Blo 1397518 1398639 := bstep (se 1 (by rfl) ⟨1048979, by rfl⟩ : syracuseStep 1398639 = 2097959) B2097959
theorem B1398815 : Blo 1397518 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B1398991 : Blo 1397518 1398991 := bstep (se 1 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 1398991 = 2098487) B2098487
theorem B3980431 : Blo 1397518 3980431 := bstep (se 1 (by rfl) ⟨2985323, by rfl⟩ : syracuseStep 3980431 = 5970647) B5970647
theorem B2358767 : Blo 1397518 2358767 := bstep (se 1 (by rfl) ⟨1769075, by rfl⟩ : syracuseStep 2358767 = 3538151) B3538151
theorem B129130823 : Blo 1397518 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B8962919 : Blo 1397518 8962919 := bstep (se 1 (by rfl) ⟨6722189, by rfl⟩ : syracuseStep 8962919 = 13444379) B13444379
theorem B4481983 : Blo 1397518 4481983 := bstep (se 1 (by rfl) ⟨3361487, by rfl⟩ : syracuseStep 4481983 = 6722975) B6722975
theorem B7963757 : Blo 1397518 7963757 := bstep (se 3 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 7963757 = 2986409) B2986409
theorem B11339831 : Blo 1397518 11339831 := bstep (se 1 (by rfl) ⟨8504873, by rfl⟩ : syracuseStep 11339831 = 17009747) B17009747
theorem B4852543 : Blo 1397518 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B21523657 : Blo 1397518 21523657 := bstep (se 2 (by rfl) ⟨8071371, by rfl⟩ : syracuseStep 21523657 = 16142743) B16142743
theorem B17927729 : Blo 1397518 17927729 := bstep (se 2 (by rfl) ⟨6722898, by rfl⟩ : syracuseStep 17927729 = 13445797) B13445797
theorem B1398779 : Blo 1397518 1398779 := bstep (se 1 (by rfl) ⟨1049084, by rfl⟩ : syracuseStep 1398779 = 2098169) B2098169
theorem B441727105 : Blo 1397518 441727105 := bstep (se 2 (by rfl) ⟨165647664, by rfl⟩ : syracuseStep 441727105 = 331295329) B331295329
theorem B7076159 : Blo 1397518 7076159 := bstep (se 1 (by rfl) ⟨5307119, by rfl⟩ : syracuseStep 7076159 = 10614239) B10614239
theorem B1399111 : Blo 1397518 1399111 := bstep (se 1 (by rfl) ⟨1049333, by rfl⟩ : syracuseStep 1399111 = 2098667) B2098667
theorem B1399263 : Blo 1397518 1399263 := bstep (se 1 (by rfl) ⟨1049447, by rfl⟩ : syracuseStep 1399263 = 2098895) B2098895
theorem B5307241 : Blo 1397518 5307241 := bstep (se 2 (by rfl) ⟨1990215, by rfl⟩ : syracuseStep 5307241 = 3980431) B3980431
theorem B6724745 : Blo 1397518 6724745 := bstep (se 2 (by rfl) ⟨2521779, by rfl⟩ : syracuseStep 6724745 = 5043559) B5043559
theorem B1572511 : Blo 1397518 1572511 := bstep (se 1 (by rfl) ⟨1179383, by rfl⟩ : syracuseStep 1572511 = 2358767) B2358767
theorem B5309171 : Blo 1397518 5309171 := bstep (se 1 (by rfl) ⟨3981878, by rfl⟩ : syracuseStep 5309171 = 7963757) B7963757
theorem B28698209 : Blo 1397518 28698209 := bstep (se 2 (by rfl) ⟨10761828, by rfl⟩ : syracuseStep 28698209 = 21523657) B21523657
theorem B4483163 : Blo 1397518 4483163 := bstep (se 1 (by rfl) ⟨3362372, by rfl⟩ : syracuseStep 4483163 = 6724745) B6724745
theorem B5975279 : Blo 1397518 5975279 := bstep (se 1 (by rfl) ⟨4481459, by rfl⟩ : syracuseStep 5975279 = 8962919) B8962919
theorem B588969473 : Blo 1397518 588969473 := bstep (se 2 (by rfl) ⟨220863552, by rfl⟩ : syracuseStep 588969473 = 441727105) B441727105
theorem B86087215 : Blo 1397518 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B6470057 : Blo 1397518 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B7076321 : Blo 1397518 7076321 := bstep (se 2 (by rfl) ⟨2653620, by rfl⟩ : syracuseStep 7076321 = 5307241) B5307241
theorem B7559887 : Blo 1397518 7559887 := bstep (se 1 (by rfl) ⟨5669915, by rfl⟩ : syracuseStep 7559887 = 11339831) B11339831
theorem B4717439 : Blo 1397518 4717439 := bstep (se 1 (by rfl) ⟨3538079, by rfl⟩ : syracuseStep 4717439 = 7076159) B7076159
theorem B2096681 : Blo 1397518 2096681 := bstep (se 2 (by rfl) ⟨786255, by rfl⟩ : syracuseStep 2096681 = 1572511) B1572511
theorem B23903909 : Blo 1397518 23903909 := bstep (se 4 (by rfl) ⟨2240991, by rfl⟩ : syracuseStep 23903909 = 4481983) B4481983
theorem B11951819 : Blo 1397518 11951819 := bstep (se 1 (by rfl) ⟨8963864, by rfl⟩ : syracuseStep 11951819 = 17927729) B17927729
theorem B3539447 : Blo 1397518 3539447 := bstep (se 1 (by rfl) ⟨2654585, by rfl⟩ : syracuseStep 3539447 = 5309171) B5309171
theorem B17253485 : Blo 1397518 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B3983519 : Blo 1397518 3983519 := bstep (se 1 (by rfl) ⟨2987639, by rfl⟩ : syracuseStep 3983519 = 5975279) B5975279
theorem B15935939 : Blo 1397518 15935939 := bstep (se 1 (by rfl) ⟨11951954, by rfl⟩ : syracuseStep 15935939 = 23903909) B23903909
theorem B10079849 : Blo 1397518 10079849 := bstep (se 2 (by rfl) ⟨3779943, by rfl⟩ : syracuseStep 10079849 = 7559887) B7559887
theorem B19132139 : Blo 1397518 19132139 := bstep (se 1 (by rfl) ⟨14349104, by rfl⟩ : syracuseStep 19132139 = 28698209) B28698209
theorem B114782953 : Blo 1397518 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B1397787 : Blo 1397518 1397787 := bstep (se 1 (by rfl) ⟨1048340, by rfl⟩ : syracuseStep 1397787 = 2096681) B2096681
theorem B7967879 : Blo 1397518 7967879 := bstep (se 1 (by rfl) ⟨5975909, by rfl⟩ : syracuseStep 7967879 = 11951819) B11951819
theorem B1570585261 : Blo 1397518 1570585261 := bstep (se 3 (by rfl) ⟨294484736, by rfl⟩ : syracuseStep 1570585261 = 588969473) B588969473
theorem B2988775 : Blo 1397518 2988775 := bstep (se 1 (by rfl) ⟨2241581, by rfl⟩ : syracuseStep 2988775 = 4483163) B4483163
theorem B4717547 : Blo 1397518 4717547 := bstep (se 1 (by rfl) ⟨3538160, by rfl⟩ : syracuseStep 4717547 = 7076321) B7076321
theorem B3144959 : Blo 1397518 3144959 := bstep (se 1 (by rfl) ⟨2358719, by rfl⟩ : syracuseStep 3144959 = 4717439) B4717439
theorem B2359631 : Blo 1397518 2359631 := bstep (se 1 (by rfl) ⟨1769723, by rfl⟩ : syracuseStep 2359631 = 3539447) B3539447
theorem B11502323 : Blo 1397518 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B2094113681 : Blo 1397518 2094113681 := bstep (se 2 (by rfl) ⟨785292630, by rfl⟩ : syracuseStep 2094113681 = 1570585261) B1570585261
theorem B153043937 : Blo 1397518 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B2655679 : Blo 1397518 2655679 := bstep (se 1 (by rfl) ⟨1991759, by rfl⟩ : syracuseStep 2655679 = 3983519) B3983519
theorem B26879597 : Blo 1397518 26879597 := bstep (se 3 (by rfl) ⟨5039924, by rfl⟩ : syracuseStep 26879597 = 10079849) B10079849
theorem B5311919 : Blo 1397518 5311919 := bstep (se 1 (by rfl) ⟨3983939, by rfl⟩ : syracuseStep 5311919 = 7967879) B7967879
theorem B3985033 : Blo 1397518 3985033 := bstep (se 2 (by rfl) ⟨1494387, by rfl⟩ : syracuseStep 3985033 = 2988775) B2988775
theorem B10623959 : Blo 1397518 10623959 := bstep (se 1 (by rfl) ⟨7967969, by rfl⟩ : syracuseStep 10623959 = 15935939) B15935939
theorem B3145031 : Blo 1397518 3145031 := bstep (se 1 (by rfl) ⟨2358773, by rfl⟩ : syracuseStep 3145031 = 4717547) B4717547
theorem B2096639 : Blo 1397518 2096639 := bstep (se 1 (by rfl) ⟨1572479, by rfl⟩ : syracuseStep 2096639 = 3144959) B3144959
theorem B12754759 : Blo 1397518 12754759 := bstep (se 1 (by rfl) ⟨9566069, by rfl⟩ : syracuseStep 12754759 = 19132139) B19132139
theorem B1573087 : Blo 1397518 1573087 := bstep (se 1 (by rfl) ⟨1179815, by rfl⟩ : syracuseStep 1573087 = 2359631) B2359631
theorem B7668215 : Blo 1397518 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B3540905 : Blo 1397518 3540905 := bstep (se 2 (by rfl) ⟨1327839, by rfl⟩ : syracuseStep 3540905 = 2655679) B2655679
theorem B3541279 : Blo 1397518 3541279 := bstep (se 1 (by rfl) ⟨2655959, by rfl⟩ : syracuseStep 3541279 = 5311919) B5311919
theorem B1396075787 : Blo 1397518 1396075787 := bstep (se 1 (by rfl) ⟨1047056840, by rfl⟩ : syracuseStep 1396075787 = 2094113681) B2094113681
theorem B17919731 : Blo 1397518 17919731 := bstep (se 1 (by rfl) ⟨13439798, by rfl⟩ : syracuseStep 17919731 = 26879597) B26879597
theorem B7082639 : Blo 1397518 7082639 := bstep (se 1 (by rfl) ⟨5311979, by rfl⟩ : syracuseStep 7082639 = 10623959) B10623959
theorem B5313377 : Blo 1397518 5313377 := bstep (se 2 (by rfl) ⟨1992516, by rfl⟩ : syracuseStep 5313377 = 3985033) B3985033
theorem B1397759 : Blo 1397518 1397759 := bstep (se 1 (by rfl) ⟨1048319, by rfl⟩ : syracuseStep 1397759 = 2096639) B2096639
theorem B102029291 : Blo 1397518 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B2096687 : Blo 1397518 2096687 := bstep (se 1 (by rfl) ⟨1572515, by rfl⟩ : syracuseStep 2096687 = 3145031) B3145031
theorem B17006345 : Blo 1397518 17006345 := bstep (se 2 (by rfl) ⟨6377379, by rfl⟩ : syracuseStep 17006345 = 12754759) B12754759
theorem B2097449 : Blo 1397518 2097449 := bstep (se 2 (by rfl) ⟨786543, by rfl⟩ : syracuseStep 2097449 = 1573087) B1573087
theorem B5112143 : Blo 1397518 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B2360603 : Blo 1397518 2360603 := bstep (se 1 (by rfl) ⟨1770452, by rfl⟩ : syracuseStep 2360603 = 3540905) B3540905
theorem B68019527 : Blo 1397518 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B11946487 : Blo 1397518 11946487 := bstep (se 1 (by rfl) ⟨8959865, by rfl⟩ : syracuseStep 11946487 = 17919731) B17919731
theorem B4721705 : Blo 1397518 4721705 := bstep (se 2 (by rfl) ⟨1770639, by rfl⟩ : syracuseStep 4721705 = 3541279) B3541279
theorem B4721759 : Blo 1397518 4721759 := bstep (se 1 (by rfl) ⟨3541319, by rfl⟩ : syracuseStep 4721759 = 7082639) B7082639
theorem B3542251 : Blo 1397518 3542251 := bstep (se 1 (by rfl) ⟨2656688, by rfl⟩ : syracuseStep 3542251 = 5313377) B5313377
theorem B1397791 : Blo 1397518 1397791 := bstep (se 1 (by rfl) ⟨1048343, by rfl⟩ : syracuseStep 1397791 = 2096687) B2096687
theorem B930717191 : Blo 1397518 930717191 := bstep (se 1 (by rfl) ⟨698037893, by rfl⟩ : syracuseStep 930717191 = 1396075787) B1396075787
theorem B11337563 : Blo 1397518 11337563 := bstep (se 1 (by rfl) ⟨8503172, by rfl⟩ : syracuseStep 11337563 = 17006345) B17006345
theorem B3408095 : Blo 1397518 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B1573735 : Blo 1397518 1573735 := bstep (se 1 (by rfl) ⟨1180301, by rfl⟩ : syracuseStep 1573735 = 2360603) B2360603
theorem B3147803 : Blo 1397518 3147803 := bstep (se 1 (by rfl) ⟨2360852, by rfl⟩ : syracuseStep 3147803 = 4721705) B4721705
theorem B3147839 : Blo 1397518 3147839 := bstep (se 1 (by rfl) ⟨2360879, by rfl⟩ : syracuseStep 3147839 = 4721759) B4721759
theorem B15928649 : Blo 1397518 15928649 := bstep (se 2 (by rfl) ⟨5973243, by rfl⟩ : syracuseStep 15928649 = 11946487) B11946487
theorem B45346351 : Blo 1397518 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B4723001 : Blo 1397518 4723001 := bstep (se 2 (by rfl) ⟨1771125, by rfl⟩ : syracuseStep 4723001 = 3542251) B3542251
theorem B7558375 : Blo 1397518 7558375 := bstep (se 1 (by rfl) ⟨5668781, by rfl⟩ : syracuseStep 7558375 = 11337563) B11337563
theorem B1398299 : Blo 1397518 1398299 := bstep (se 1 (by rfl) ⟨1048724, by rfl⟩ : syracuseStep 1398299 = 2097449) B2097449
theorem B620478127 : Blo 1397518 620478127 := bstep (se 1 (by rfl) ⟨465358595, by rfl⟩ : syracuseStep 620478127 = 930717191) B930717191
theorem B3309216677 : Blo 1397518 3309216677 := bstep (se 4 (by rfl) ⟨310239063, by rfl⟩ : syracuseStep 3309216677 = 620478127) B620478127
theorem B2098313 : Blo 1397518 2098313 := bstep (se 2 (by rfl) ⟨786867, by rfl⟩ : syracuseStep 2098313 = 1573735) B1573735
theorem B2098535 : Blo 1397518 2098535 := bstep (se 1 (by rfl) ⟨1573901, by rfl⟩ : syracuseStep 2098535 = 3147803) B3147803
theorem B2098559 : Blo 1397518 2098559 := bstep (se 1 (by rfl) ⟨1573919, by rfl⟩ : syracuseStep 2098559 = 3147839) B3147839
theorem B10077833 : Blo 1397518 10077833 := bstep (se 2 (by rfl) ⟨3779187, by rfl⟩ : syracuseStep 10077833 = 7558375) B7558375
theorem B10619099 : Blo 1397518 10619099 := bstep (se 1 (by rfl) ⟨7964324, by rfl⟩ : syracuseStep 10619099 = 15928649) B15928649
theorem B2272063 : Blo 1397518 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B3148667 : Blo 1397518 3148667 := bstep (se 1 (by rfl) ⟨2361500, by rfl⟩ : syracuseStep 3148667 = 4723001) B4723001
theorem B60461801 : Blo 1397518 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B6718555 : Blo 1397518 6718555 := bstep (se 1 (by rfl) ⟨5038916, by rfl⟩ : syracuseStep 6718555 = 10077833) B10077833
theorem B7079399 : Blo 1397518 7079399 := bstep (se 1 (by rfl) ⟨5309549, by rfl⟩ : syracuseStep 7079399 = 10619099) B10619099
theorem B2099111 : Blo 1397518 2099111 := bstep (se 1 (by rfl) ⟨1574333, by rfl⟩ : syracuseStep 2099111 = 3148667) B3148667
theorem B40307867 : Blo 1397518 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B2206144451 : Blo 1397518 2206144451 := bstep (se 1 (by rfl) ⟨1654608338, by rfl⟩ : syracuseStep 2206144451 = 3309216677) B3309216677
theorem B1398875 : Blo 1397518 1398875 := bstep (se 1 (by rfl) ⟨1049156, by rfl⟩ : syracuseStep 1398875 = 2098313) B2098313
theorem B1399023 : Blo 1397518 1399023 := bstep (se 1 (by rfl) ⟨1049267, by rfl⟩ : syracuseStep 1399023 = 2098535) B2098535
theorem B1399039 : Blo 1397518 1399039 := bstep (se 1 (by rfl) ⟨1049279, by rfl⟩ : syracuseStep 1399039 = 2098559) B2098559
theorem B3029417 : Blo 1397518 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B4719599 : Blo 1397518 4719599 := bstep (se 1 (by rfl) ⟨3539699, by rfl⟩ : syracuseStep 4719599 = 7079399) B7079399
theorem B26871911 : Blo 1397518 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B1470762967 : Blo 1397518 1470762967 := bstep (se 1 (by rfl) ⟨1103072225, by rfl⟩ : syracuseStep 1470762967 = 2206144451) B2206144451
theorem B8958073 : Blo 1397518 8958073 := bstep (se 2 (by rfl) ⟨3359277, by rfl⟩ : syracuseStep 8958073 = 6718555) B6718555
theorem B2019611 : Blo 1397518 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B1399407 : Blo 1397518 1399407 := bstep (se 1 (by rfl) ⟨1049555, by rfl⟩ : syracuseStep 1399407 = 2099111) B2099111
theorem B11944097 : Blo 1397518 11944097 := bstep (se 2 (by rfl) ⟨4479036, by rfl⟩ : syracuseStep 11944097 = 8958073) B8958073
theorem B3146399 : Blo 1397518 3146399 := bstep (se 1 (by rfl) ⟨2359799, by rfl⟩ : syracuseStep 3146399 = 4719599) B4719599
theorem B5385629 : Blo 1397518 5385629 := bstep (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) B2019611
theorem B17914607 : Blo 1397518 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B1961017289 : Blo 1397518 1961017289 := bstep (se 2 (by rfl) ⟨735381483, by rfl⟩ : syracuseStep 1961017289 = 1470762967) B1470762967
theorem B7962731 : Blo 1397518 7962731 := bstep (se 1 (by rfl) ⟨5972048, by rfl⟩ : syracuseStep 7962731 = 11944097) B11944097
theorem B2097599 : Blo 1397518 2097599 := bstep (se 1 (by rfl) ⟨1573199, by rfl⟩ : syracuseStep 2097599 = 3146399) B3146399
theorem B3590419 : Blo 1397518 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B11943071 : Blo 1397518 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B1307344859 : Blo 1397518 1307344859 := bstep (se 1 (by rfl) ⟨980508644, by rfl⟩ : syracuseStep 1307344859 = 1961017289) B1961017289
theorem B5308487 : Blo 1397518 5308487 := bstep (se 1 (by rfl) ⟨3981365, by rfl⟩ : syracuseStep 5308487 = 7962731) B7962731
theorem B4787225 : Blo 1397518 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B1398399 : Blo 1397518 1398399 := bstep (se 1 (by rfl) ⟨1048799, by rfl⟩ : syracuseStep 1398399 = 2097599) B2097599
theorem B7962047 : Blo 1397518 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B871563239 : Blo 1397518 871563239 := bstep (se 1 (by rfl) ⟨653672429, by rfl⟩ : syracuseStep 871563239 = 1307344859) B1307344859
theorem B3538991 : Blo 1397518 3538991 := bstep (se 1 (by rfl) ⟨2654243, by rfl⟩ : syracuseStep 3538991 = 5308487) B5308487
theorem B3191483 : Blo 1397518 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B5308031 : Blo 1397518 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B581042159 : Blo 1397518 581042159 := bstep (se 1 (by rfl) ⟨435781619, by rfl⟩ : syracuseStep 581042159 = 871563239) B871563239
theorem B2359327 : Blo 1397518 2359327 := bstep (se 1 (by rfl) ⟨1769495, by rfl⟩ : syracuseStep 2359327 = 3538991) B3538991
theorem B387361439 : Blo 1397518 387361439 := bstep (se 1 (by rfl) ⟨290521079, by rfl⟩ : syracuseStep 387361439 = 581042159) B581042159
theorem B2127655 : Blo 1397518 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B3538687 : Blo 1397518 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B3145769 : Blo 1397518 3145769 := bstep (se 2 (by rfl) ⟨1179663, by rfl⟩ : syracuseStep 3145769 = 2359327) B2359327
theorem B2836873 : Blo 1397518 2836873 := bstep (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) B2127655
theorem B258240959 : Blo 1397518 258240959 := bstep (se 1 (by rfl) ⟨193680719, by rfl⟩ : syracuseStep 258240959 = 387361439) B387361439
theorem B4718249 : Blo 1397518 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B2097179 : Blo 1397518 2097179 := bstep (se 1 (by rfl) ⟨1572884, by rfl⟩ : syracuseStep 2097179 = 3145769) B3145769
theorem B172160639 : Blo 1397518 172160639 := bstep (se 1 (by rfl) ⟨129120479, by rfl⟩ : syracuseStep 172160639 = 258240959) B258240959
theorem B3782497 : Blo 1397518 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B3145499 : Blo 1397518 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B114773759 : Blo 1397518 114773759 := bstep (se 1 (by rfl) ⟨86080319, by rfl⟩ : syracuseStep 114773759 = 172160639) B172160639
theorem B5043329 : Blo 1397518 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B1398119 : Blo 1397518 1398119 := bstep (se 1 (by rfl) ⟨1048589, by rfl⟩ : syracuseStep 1398119 = 2097179) B2097179
theorem B2096999 : Blo 1397518 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B76515839 : Blo 1397518 76515839 := bstep (se 1 (by rfl) ⟨57386879, by rfl⟩ : syracuseStep 76515839 = 114773759) B114773759
theorem B3362219 : Blo 1397518 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B1397999 : Blo 1397518 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B2241479 : Blo 1397518 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B51010559 : Blo 1397518 51010559 := bstep (se 1 (by rfl) ⟨38257919, by rfl⟩ : syracuseStep 51010559 = 76515839) B76515839
theorem B34007039 : Blo 1397518 34007039 := bstep (se 1 (by rfl) ⟨25505279, by rfl⟩ : syracuseStep 34007039 = 51010559) B51010559
theorem B5977277 : Blo 1397518 5977277 := bstep (se 3 (by rfl) ⟨1120739, by rfl⟩ : syracuseStep 5977277 = 2241479) B2241479
theorem B3984851 : Blo 1397518 3984851 := bstep (se 1 (by rfl) ⟨2988638, by rfl⟩ : syracuseStep 3984851 = 5977277) B5977277
theorem B22671359 : Blo 1397518 22671359 := bstep (se 1 (by rfl) ⟨17003519, by rfl⟩ : syracuseStep 22671359 = 34007039) B34007039
theorem B2656567 : Blo 1397518 2656567 := bstep (se 1 (by rfl) ⟨1992425, by rfl⟩ : syracuseStep 2656567 = 3984851) B3984851
theorem B15114239 : Blo 1397518 15114239 := bstep (se 1 (by rfl) ⟨11335679, by rfl⟩ : syracuseStep 15114239 = 22671359) B22671359
theorem B3542089 : Blo 1397518 3542089 := bstep (se 2 (by rfl) ⟨1328283, by rfl⟩ : syracuseStep 3542089 = 2656567) B2656567
theorem B10076159 : Blo 1397518 10076159 := bstep (se 1 (by rfl) ⟨7557119, by rfl⟩ : syracuseStep 10076159 = 15114239) B15114239
theorem B4722785 : Blo 1397518 4722785 := bstep (se 2 (by rfl) ⟨1771044, by rfl⟩ : syracuseStep 4722785 = 3542089) B3542089
theorem B6717439 : Blo 1397518 6717439 := bstep (se 1 (by rfl) ⟨5038079, by rfl⟩ : syracuseStep 6717439 = 10076159) B10076159
theorem B8956585 : Blo 1397518 8956585 := bstep (se 2 (by rfl) ⟨3358719, by rfl⟩ : syracuseStep 8956585 = 6717439) B6717439
theorem B3148523 : Blo 1397518 3148523 := bstep (se 1 (by rfl) ⟨2361392, by rfl⟩ : syracuseStep 3148523 = 4722785) B4722785
theorem B2099015 : Blo 1397518 2099015 := bstep (se 1 (by rfl) ⟨1574261, by rfl⟩ : syracuseStep 2099015 = 3148523) B3148523
theorem B11942113 : Blo 1397518 11942113 := bstep (se 2 (by rfl) ⟨4478292, by rfl⟩ : syracuseStep 11942113 = 8956585) B8956585
theorem B15922817 : Blo 1397518 15922817 := bstep (se 2 (by rfl) ⟨5971056, by rfl⟩ : syracuseStep 15922817 = 11942113) B11942113
theorem B1399343 : Blo 1397518 1399343 := bstep (se 1 (by rfl) ⟨1049507, by rfl⟩ : syracuseStep 1399343 = 2099015) B2099015
theorem B10615211 : Blo 1397518 10615211 := bstep (se 1 (by rfl) ⟨7961408, by rfl⟩ : syracuseStep 10615211 = 15922817) B15922817
theorem B7076807 : Blo 1397518 7076807 := bstep (se 1 (by rfl) ⟨5307605, by rfl⟩ : syracuseStep 7076807 = 10615211) B10615211
theorem B4717871 : Blo 1397518 4717871 := bstep (se 1 (by rfl) ⟨3538403, by rfl⟩ : syracuseStep 4717871 = 7076807) B7076807
theorem B3145247 : Blo 1397518 3145247 := bstep (se 1 (by rfl) ⟨2358935, by rfl⟩ : syracuseStep 3145247 = 4717871) B4717871
theorem B2096831 : Blo 1397518 2096831 := bstep (se 1 (by rfl) ⟨1572623, by rfl⟩ : syracuseStep 2096831 = 3145247) B3145247
theorem B1397887 : Blo 1397518 1397887 := bstep (se 1 (by rfl) ⟨1048415, by rfl⟩ : syracuseStep 1397887 = 2096831) B2096831

theorem C0 (j : ℕ) (h1 : 349379 ≤ j) (h2 : j ≤ 349878) : Blo 1397518 (4 * j + 3) := by
  interval_cases j
  · exact B1397519
  · exact B1397523
  · exact B1397527
  · exact B1397531
  · exact B1397535
  · exact B1397539
  · exact B1397543
  · exact B1397547
  · exact B1397551
  · exact B1397555
  · exact B1397559
  · exact B1397563
  · exact B1397567
  · exact B1397571
  · exact B1397575
  · exact B1397579
  · exact B1397583
  · exact B1397587
  · exact B1397591
  · exact B1397595
  · exact B1397599
  · exact B1397603
  · exact B1397607
  · exact B1397611
  · exact B1397615
  · exact B1397619
  · exact B1397623
  · exact B1397627
  · exact B1397631
  · exact B1397635
  · exact B1397639
  · exact B1397643
  · exact B1397647
  · exact B1397651
  · exact B1397655
  · exact B1397659
  · exact B1397663
  · exact B1397667
  · exact B1397671
  · exact B1397675
  · exact B1397679
  · exact B1397683
  · exact B1397687
  · exact B1397691
  · exact B1397695
  · exact B1397699
  · exact B1397703
  · exact B1397707
  · exact B1397711
  · exact B1397715
  · exact B1397719
  · exact B1397723
  · exact B1397727
  · exact B1397731
  · exact B1397735
  · exact B1397739
  · exact B1397743
  · exact B1397747
  · exact B1397751
  · exact B1397755
  · exact B1397759
  · exact B1397763
  · exact B1397767
  · exact B1397771
  · exact B1397775
  · exact B1397779
  · exact B1397783
  · exact B1397787
  · exact B1397791
  · exact B1397795
  · exact B1397799
  · exact B1397803
  · exact B1397807
  · exact B1397811
  · exact B1397815
  · exact B1397819
  · exact B1397823
  · exact B1397827
  · exact B1397831
  · exact B1397835
  · exact B1397839
  · exact B1397843
  · exact B1397847
  · exact B1397851
  · exact B1397855
  · exact B1397859
  · exact B1397863
  · exact B1397867
  · exact B1397871
  · exact B1397875
  · exact B1397879
  · exact B1397883
  · exact B1397887
  · exact B1397891
  · exact B1397895
  · exact B1397899
  · exact B1397903
  · exact B1397907
  · exact B1397911
  · exact B1397915
  · exact B1397919
  · exact B1397923
  · exact B1397927
  · exact B1397931
  · exact B1397935
  · exact B1397939
  · exact B1397943
  · exact B1397947
  · exact B1397951
  · exact B1397955
  · exact B1397959
  · exact B1397963
  · exact B1397967
  · exact B1397971
  · exact B1397975
  · exact B1397979
  · exact B1397983
  · exact B1397987
  · exact B1397991
  · exact B1397995
  · exact B1397999
  · exact B1398003
  · exact B1398007
  · exact B1398011
  · exact B1398015
  · exact B1398019
  · exact B1398023
  · exact B1398027
  · exact B1398031
  · exact B1398035
  · exact B1398039
  · exact B1398043
  · exact B1398047
  · exact B1398051
  · exact B1398055
  · exact B1398059
  · exact B1398063
  · exact B1398067
  · exact B1398071
  · exact B1398075
  · exact B1398079
  · exact B1398083
  · exact B1398087
  · exact B1398091
  · exact B1398095
  · exact B1398099
  · exact B1398103
  · exact B1398107
  · exact B1398111
  · exact B1398115
  · exact B1398119
  · exact B1398123
  · exact B1398127
  · exact B1398131
  · exact B1398135
  · exact B1398139
  · exact B1398143
  · exact B1398147
  · exact B1398151
  · exact B1398155
  · exact B1398159
  · exact B1398163
  · exact B1398167
  · exact B1398171
  · exact B1398175
  · exact B1398179
  · exact B1398183
  · exact B1398187
  · exact B1398191
  · exact B1398195
  · exact B1398199
  · exact B1398203
  · exact B1398207
  · exact B1398211
  · exact B1398215
  · exact B1398219
  · exact B1398223
  · exact B1398227
  · exact B1398231
  · exact B1398235
  · exact B1398239
  · exact B1398243
  · exact B1398247
  · exact B1398251
  · exact B1398255
  · exact B1398259
  · exact B1398263
  · exact B1398267
  · exact B1398271
  · exact B1398275
  · exact B1398279
  · exact B1398283
  · exact B1398287
  · exact B1398291
  · exact B1398295
  · exact B1398299
  · exact B1398303
  · exact B1398307
  · exact B1398311
  · exact B1398315
  · exact B1398319
  · exact B1398323
  · exact B1398327
  · exact B1398331
  · exact B1398335
  · exact B1398339
  · exact B1398343
  · exact B1398347
  · exact B1398351
  · exact B1398355
  · exact B1398359
  · exact B1398363
  · exact B1398367
  · exact B1398371
  · exact B1398375
  · exact B1398379
  · exact B1398383
  · exact B1398387
  · exact B1398391
  · exact B1398395
  · exact B1398399
  · exact B1398403
  · exact B1398407
  · exact B1398411
  · exact B1398415
  · exact B1398419
  · exact B1398423
  · exact B1398427
  · exact B1398431
  · exact B1398435
  · exact B1398439
  · exact B1398443
  · exact B1398447
  · exact B1398451
  · exact B1398455
  · exact B1398459
  · exact B1398463
  · exact B1398467
  · exact B1398471
  · exact B1398475
  · exact B1398479
  · exact B1398483
  · exact B1398487
  · exact B1398491
  · exact B1398495
  · exact B1398499
  · exact B1398503
  · exact B1398507
  · exact B1398511
  · exact B1398515
  · exact B1398519
  · exact B1398523
  · exact B1398527
  · exact B1398531
  · exact B1398535
  · exact B1398539
  · exact B1398543
  · exact B1398547
  · exact B1398551
  · exact B1398555
  · exact B1398559
  · exact B1398563
  · exact B1398567
  · exact B1398571
  · exact B1398575
  · exact B1398579
  · exact B1398583
  · exact B1398587
  · exact B1398591
  · exact B1398595
  · exact B1398599
  · exact B1398603
  · exact B1398607
  · exact B1398611
  · exact B1398615
  · exact B1398619
  · exact B1398623
  · exact B1398627
  · exact B1398631
  · exact B1398635
  · exact B1398639
  · exact B1398643
  · exact B1398647
  · exact B1398651
  · exact B1398655
  · exact B1398659
  · exact B1398663
  · exact B1398667
  · exact B1398671
  · exact B1398675
  · exact B1398679
  · exact B1398683
  · exact B1398687
  · exact B1398691
  · exact B1398695
  · exact B1398699
  · exact B1398703
  · exact B1398707
  · exact B1398711
  · exact B1398715
  · exact B1398719
  · exact B1398723
  · exact B1398727
  · exact B1398731
  · exact B1398735
  · exact B1398739
  · exact B1398743
  · exact B1398747
  · exact B1398751
  · exact B1398755
  · exact B1398759
  · exact B1398763
  · exact B1398767
  · exact B1398771
  · exact B1398775
  · exact B1398779
  · exact B1398783
  · exact B1398787
  · exact B1398791
  · exact B1398795
  · exact B1398799
  · exact B1398803
  · exact B1398807
  · exact B1398811
  · exact B1398815
  · exact B1398819
  · exact B1398823
  · exact B1398827
  · exact B1398831
  · exact B1398835
  · exact B1398839
  · exact B1398843
  · exact B1398847
  · exact B1398851
  · exact B1398855
  · exact B1398859
  · exact B1398863
  · exact B1398867
  · exact B1398871
  · exact B1398875
  · exact B1398879
  · exact B1398883
  · exact B1398887
  · exact B1398891
  · exact B1398895
  · exact B1398899
  · exact B1398903
  · exact B1398907
  · exact B1398911
  · exact B1398915
  · exact B1398919
  · exact B1398923
  · exact B1398927
  · exact B1398931
  · exact B1398935
  · exact B1398939
  · exact B1398943
  · exact B1398947
  · exact B1398951
  · exact B1398955
  · exact B1398959
  · exact B1398963
  · exact B1398967
  · exact B1398971
  · exact B1398975
  · exact B1398979
  · exact B1398983
  · exact B1398987
  · exact B1398991
  · exact B1398995
  · exact B1398999
  · exact B1399003
  · exact B1399007
  · exact B1399011
  · exact B1399015
  · exact B1399019
  · exact B1399023
  · exact B1399027
  · exact B1399031
  · exact B1399035
  · exact B1399039
  · exact B1399043
  · exact B1399047
  · exact B1399051
  · exact B1399055
  · exact B1399059
  · exact B1399063
  · exact B1399067
  · exact B1399071
  · exact B1399075
  · exact B1399079
  · exact B1399083
  · exact B1399087
  · exact B1399091
  · exact B1399095
  · exact B1399099
  · exact B1399103
  · exact B1399107
  · exact B1399111
  · exact B1399115
  · exact B1399119
  · exact B1399123
  · exact B1399127
  · exact B1399131
  · exact B1399135
  · exact B1399139
  · exact B1399143
  · exact B1399147
  · exact B1399151
  · exact B1399155
  · exact B1399159
  · exact B1399163
  · exact B1399167
  · exact B1399171
  · exact B1399175
  · exact B1399179
  · exact B1399183
  · exact B1399187
  · exact B1399191
  · exact B1399195
  · exact B1399199
  · exact B1399203
  · exact B1399207
  · exact B1399211
  · exact B1399215
  · exact B1399219
  · exact B1399223
  · exact B1399227
  · exact B1399231
  · exact B1399235
  · exact B1399239
  · exact B1399243
  · exact B1399247
  · exact B1399251
  · exact B1399255
  · exact B1399259
  · exact B1399263
  · exact B1399267
  · exact B1399271
  · exact B1399275
  · exact B1399279
  · exact B1399283
  · exact B1399287
  · exact B1399291
  · exact B1399295
  · exact B1399299
  · exact B1399303
  · exact B1399307
  · exact B1399311
  · exact B1399315
  · exact B1399319
  · exact B1399323
  · exact B1399327
  · exact B1399331
  · exact B1399335
  · exact B1399339
  · exact B1399343
  · exact B1399347
  · exact B1399351
  · exact B1399355
  · exact B1399359
  · exact B1399363
  · exact B1399367
  · exact B1399371
  · exact B1399375
  · exact B1399379
  · exact B1399383
  · exact B1399387
  · exact B1399391
  · exact B1399395
  · exact B1399399
  · exact B1399403
  · exact B1399407
  · exact B1399411
  · exact B1399415
  · exact B1399419
  · exact B1399423
  · exact B1399427
  · exact B1399431
  · exact B1399435
  · exact B1399439
  · exact B1399443
  · exact B1399447
  · exact B1399451
  · exact B1399455
  · exact B1399459
  · exact B1399463
  · exact B1399467
  · exact B1399471
  · exact B1399475
  · exact B1399479
  · exact B1399483
  · exact B1399487
  · exact B1399491
  · exact B1399495
  · exact B1399499
  · exact B1399503
  · exact B1399507
  · exact B1399511
  · exact B1399515

theorem solution (m : ℕ) (hlo : 1397518 ≤ m) (hhi : m ≤ 1399518) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 349379 ≤ j := by omega
    have hj2 : j ≤ 349878 := by omega
    have hb : Blo 1397518 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
