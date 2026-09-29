-- Prove2me | solution 1 for syracuse_descends_range_1242439_1244439
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:11.087085+00:00
-- url     : https://prove2.me/submissions/e439cda3-9eba-4ab1-ac08-39593618e1ce

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


theorem B2097157 : Blo 1242439 2097157 := bbase (se 4 (by rfl) ⟨196608, by rfl⟩ : syracuseStep 2097157 = 393217) (by norm_num)
theorem B4194341 : Blo 1242439 4194341 := bbase (se 4 (by rfl) ⟨393219, by rfl⟩ : syracuseStep 4194341 = 786439) (by norm_num)
theorem B1679437 : Blo 1242439 1679437 := bbase (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) (by norm_num)
theorem B1572949 : Blo 1242439 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B2097245 : Blo 1242439 2097245 := bbase (se 3 (by rfl) ⟨393233, by rfl⟩ : syracuseStep 2097245 = 786467) (by norm_num)
theorem B5308517 : Blo 1242439 5308517 := bbase (se 4 (by rfl) ⟨497673, by rfl⟩ : syracuseStep 5308517 = 995347) (by norm_num)
theorem B3539045 : Blo 1242439 3539045 := bbase (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) (by norm_num)
theorem B3145837 : Blo 1242439 3145837 := bbase (se 3 (by rfl) ⟨589844, by rfl⟩ : syracuseStep 3145837 = 1179689) (by norm_num)
theorem B2359469 : Blo 1242439 2359469 := bbase (se 3 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 2359469 = 884801) (by norm_num)
theorem B1327313 : Blo 1242439 1327313 := bbase (se 2 (by rfl) ⟨497742, by rfl⟩ : syracuseStep 1327313 = 995485) (by norm_num)
theorem B40337621 : Blo 1242439 40337621 := bbase (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) (by norm_num)
theorem B3145949 : Blo 1242439 3145949 := bbase (se 3 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 3145949 = 1179731) (by norm_num)
theorem B2097373 : Blo 1242439 2097373 := bbase (se 3 (by rfl) ⟨393257, by rfl⟩ : syracuseStep 2097373 = 786515) (by norm_num)
theorem B1769693 : Blo 1242439 1769693 := bbase (se 3 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 1769693 = 663635) (by norm_num)
theorem B1573121 : Blo 1242439 1573121 := bbase (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) (by norm_num)
theorem B2097461 : Blo 1242439 2097461 := bbase (se 5 (by rfl) ⟨98318, by rfl⟩ : syracuseStep 2097461 = 196637) (by norm_num)
theorem B1573177 : Blo 1242439 1573177 := bbase (se 2 (by rfl) ⟨589941, by rfl⟩ : syracuseStep 1573177 = 1179883) (by norm_num)
theorem B1417537 : Blo 1242439 1417537 := bbase (se 2 (by rfl) ⟨531576, by rfl⟩ : syracuseStep 1417537 = 1063153) (by norm_num)
theorem B2359621 : Blo 1242439 2359621 := bbase (se 4 (by rfl) ⟨221214, by rfl⟩ : syracuseStep 2359621 = 442429) (by norm_num)
theorem B3539285 : Blo 1242439 3539285 := bbase (se 10 (by rfl) ⟨5184, by rfl⟩ : syracuseStep 3539285 = 10369) (by norm_num)
theorem B1573273 : Blo 1242439 1573273 := bbase (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) (by norm_num)
theorem B3146141 : Blo 1242439 3146141 := bbase (se 3 (by rfl) ⟨589901, by rfl⟩ : syracuseStep 3146141 = 1179803) (by norm_num)
theorem B2097589 : Blo 1242439 2097589 := bbase (se 5 (by rfl) ⟨98324, by rfl⟩ : syracuseStep 2097589 = 196649) (by norm_num)
theorem B1679821 : Blo 1242439 1679821 := bbase (se 3 (by rfl) ⟨314966, by rfl⟩ : syracuseStep 1679821 = 629933) (by norm_num)
theorem B2654669 : Blo 1242439 2654669 := bbase (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) (by norm_num)
theorem B4194773 : Blo 1242439 4194773 := bbase (se 7 (by rfl) ⟨49157, by rfl⟩ : syracuseStep 4194773 = 98315) (by norm_num)
theorem B2097677 : Blo 1242439 2097677 := bbase (se 3 (by rfl) ⟨393314, by rfl⟩ : syracuseStep 2097677 = 786629) (by norm_num)
theorem B3539477 : Blo 1242439 3539477 := bbase (se 6 (by rfl) ⟨82956, by rfl⟩ : syracuseStep 3539477 = 165913) (by norm_num)
theorem B1991213 : Blo 1242439 1991213 := bbase (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) (by norm_num)
theorem B1573445 : Blo 1242439 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B2654813 : Blo 1242439 2654813 := bbase (se 3 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 2654813 = 995555) (by norm_num)
theorem B2359925 : Blo 1242439 2359925 := bbase (se 5 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 2359925 = 221243) (by norm_num)
theorem B1573501 : Blo 1242439 1573501 := bbase (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) (by norm_num)
theorem B2097805 : Blo 1242439 2097805 := bbase (se 3 (by rfl) ⟨393338, by rfl⟩ : syracuseStep 2097805 = 786677) (by norm_num)
theorem B1991309 : Blo 1242439 1991309 := bbase (se 3 (by rfl) ⟨373370, by rfl⟩ : syracuseStep 1991309 = 746741) (by norm_num)
theorem B1327757 : Blo 1242439 1327757 := bbase (se 3 (by rfl) ⟨248954, by rfl⟩ : syracuseStep 1327757 = 497909) (by norm_num)
theorem B15131285 : Blo 1242439 15131285 := bbase (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) (by norm_num)
theorem B1991341 : Blo 1242439 1991341 := bbase (se 3 (by rfl) ⟨373376, by rfl⟩ : syracuseStep 1991341 = 746753) (by norm_num)
theorem B10076885 : Blo 1242439 10076885 := bbase (se 7 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 10076885 = 236177) (by norm_num)
theorem B1573597 : Blo 1242439 1573597 := bbase (se 3 (by rfl) ⟨295049, by rfl⟩ : syracuseStep 1573597 = 590099) (by norm_num)
theorem B2097893 : Blo 1242439 2097893 := bbase (se 4 (by rfl) ⟨196677, by rfl⟩ : syracuseStep 2097893 = 393355) (by norm_num)
theorem B3146485 : Blo 1242439 3146485 := bbase (se 5 (by rfl) ⟨147491, by rfl⟩ : syracuseStep 3146485 = 294983) (by norm_num)
theorem B3834629 : Blo 1242439 3834629 := bbase (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) (by norm_num)
theorem B10625813 : Blo 1242439 10625813 := bbase (se 6 (by rfl) ⟨249042, by rfl⟩ : syracuseStep 10625813 = 498085) (by norm_num)
theorem B3982117 : Blo 1242439 3982117 := bbase (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) (by norm_num)
theorem B3146597 : Blo 1242439 3146597 := bbase (se 4 (by rfl) ⟨294993, by rfl⟩ : syracuseStep 3146597 = 589987) (by norm_num)
theorem B2098021 : Blo 1242439 2098021 := bbase (se 4 (by rfl) ⟨196689, by rfl⟩ : syracuseStep 2098021 = 393379) (by norm_num)
theorem B4195205 : Blo 1242439 4195205 := bbase (se 4 (by rfl) ⟨393300, by rfl⟩ : syracuseStep 4195205 = 786601) (by norm_num)
theorem B1328005 : Blo 1242439 1328005 := bbase (se 4 (by rfl) ⟨124500, by rfl⟩ : syracuseStep 1328005 = 249001) (by norm_num)
theorem B1573769 : Blo 1242439 1573769 := bbase (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) (by norm_num)
theorem B10617749 : Blo 1242439 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B2098109 : Blo 1242439 2098109 := bbase (se 3 (by rfl) ⟨393395, by rfl⟩ : syracuseStep 2098109 = 786791) (by norm_num)
theorem B1573825 : Blo 1242439 1573825 := bbase (se 2 (by rfl) ⟨590184, by rfl⟩ : syracuseStep 1573825 = 1180369) (by norm_num)
theorem B2655173 : Blo 1242439 2655173 := bbase (se 4 (by rfl) ⟨248922, by rfl⟩ : syracuseStep 2655173 = 497845) (by norm_num)
theorem B1770445 : Blo 1242439 1770445 := bbase (se 3 (by rfl) ⟨331958, by rfl⟩ : syracuseStep 1770445 = 663917) (by norm_num)
theorem B7971797 : Blo 1242439 7971797 := bbase (se 7 (by rfl) ⟨93419, by rfl⟩ : syracuseStep 7971797 = 186839) (by norm_num)
theorem B10224629 : Blo 1242439 10224629 := bbase (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) (by norm_num)
theorem B1573921 : Blo 1242439 1573921 := bbase (se 2 (by rfl) ⟨590220, by rfl⟩ : syracuseStep 1573921 = 1180441) (by norm_num)
theorem B4719653 : Blo 1242439 4719653 := bbase (se 4 (by rfl) ⟨442467, by rfl⟩ : syracuseStep 4719653 = 884935) (by norm_num)
theorem B3146789 : Blo 1242439 3146789 := bbase (se 4 (by rfl) ⟨295011, by rfl⟩ : syracuseStep 3146789 = 590023) (by norm_num)
theorem B2098237 : Blo 1242439 2098237 := bbase (se 3 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 2098237 = 786839) (by norm_num)
theorem B1418321 : Blo 1242439 1418321 := bbase (se 2 (by rfl) ⟨531870, by rfl⟩ : syracuseStep 1418321 = 1063741) (by norm_num)
theorem B6292565 : Blo 1242439 6292565 := bbase (se 8 (by rfl) ⟨36870, by rfl⟩ : syracuseStep 6292565 = 73741) (by norm_num)
theorem B5670037 : Blo 1242439 5670037 := bbase (se 6 (by rfl) ⟨132891, by rfl⟩ : syracuseStep 5670037 = 265783) (by norm_num)
theorem B2098325 : Blo 1242439 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B3982517 : Blo 1242439 3982517 := bbase (se 5 (by rfl) ⟨186680, by rfl⟩ : syracuseStep 3982517 = 373361) (by norm_num)
theorem B1574093 : Blo 1242439 1574093 := bbase (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) (by norm_num)
theorem B1574149 : Blo 1242439 1574149 := bbase (se 4 (by rfl) ⟨147576, by rfl⟩ : syracuseStep 1574149 = 295153) (by norm_num)
theorem B2098453 : Blo 1242439 2098453 := bbase (se 6 (by rfl) ⟨49182, by rfl⟩ : syracuseStep 2098453 = 98365) (by norm_num)
theorem B4195637 : Blo 1242439 4195637 := bbase (se 5 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 4195637 = 393341) (by norm_num)
theorem B1328449 : Blo 1242439 1328449 := bbase (se 2 (by rfl) ⟨498168, by rfl⟩ : syracuseStep 1328449 = 996337) (by norm_num)
theorem B4719941 : Blo 1242439 4719941 := bbase (se 4 (by rfl) ⟨442494, by rfl⟩ : syracuseStep 4719941 = 884989) (by norm_num)
theorem B2360677 : Blo 1242439 2360677 := bbase (se 4 (by rfl) ⟨221313, by rfl⟩ : syracuseStep 2360677 = 442627) (by norm_num)
theorem B1574245 : Blo 1242439 1574245 := bbase (se 4 (by rfl) ⟨147585, by rfl⟩ : syracuseStep 1574245 = 295171) (by norm_num)
theorem B2098541 : Blo 1242439 2098541 := bbase (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) (by norm_num)
theorem B3147133 : Blo 1242439 3147133 := bbase (se 3 (by rfl) ⟨590087, by rfl⟩ : syracuseStep 3147133 = 1180175) (by norm_num)
theorem B1328509 : Blo 1242439 1328509 := bbase (se 3 (by rfl) ⟨249095, by rfl⟩ : syracuseStep 1328509 = 498191) (by norm_num)
theorem B3147245 : Blo 1242439 3147245 := bbase (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) (by norm_num)
theorem B2098669 : Blo 1242439 2098669 := bbase (se 3 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 2098669 = 787001) (by norm_num)
theorem B3540469 : Blo 1242439 3540469 := bbase (se 5 (by rfl) ⟨165959, by rfl⟩ : syracuseStep 3540469 = 331919) (by norm_num)
theorem B2360821 : Blo 1242439 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B1574417 : Blo 1242439 1574417 := bbase (se 2 (by rfl) ⟨590406, by rfl⟩ : syracuseStep 1574417 = 1180813) (by norm_num)
theorem B6809141 : Blo 1242439 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B2098757 : Blo 1242439 2098757 := bbase (se 4 (by rfl) ⟨196758, by rfl⟩ : syracuseStep 2098757 = 393517) (by norm_num)
theorem B1574473 : Blo 1242439 1574473 := bbase (se 2 (by rfl) ⟨590427, by rfl⟩ : syracuseStep 1574473 = 1180855) (by norm_num)
theorem B8619605 : Blo 1242439 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B15754837 : Blo 1242439 15754837 := bbase (se 8 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 15754837 = 184627) (by norm_num)
theorem B3884645 : Blo 1242439 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B2360981 : Blo 1242439 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B1418905 : Blo 1242439 1418905 := bbase (se 2 (by rfl) ⟨532089, by rfl⟩ : syracuseStep 1418905 = 1064179) (by norm_num)
theorem B1574569 : Blo 1242439 1574569 := bbase (se 2 (by rfl) ⟨590463, by rfl⟩ : syracuseStep 1574569 = 1180927) (by norm_num)
theorem B3147437 : Blo 1242439 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B6727349 : Blo 1242439 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B1328825 : Blo 1242439 1328825 := bbase (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) (by norm_num)
theorem B2098885 : Blo 1242439 2098885 := bbase (se 4 (by rfl) ⟨196770, by rfl⟩ : syracuseStep 2098885 = 393541) (by norm_num)
theorem B1418969 : Blo 1242439 1418969 := bbase (se 2 (by rfl) ⟨532113, by rfl⟩ : syracuseStep 1418969 = 1064227) (by norm_num)
theorem B4196069 : Blo 1242439 4196069 := bbase (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) (by norm_num)
theorem B1771237 : Blo 1242439 1771237 := bbase (se 4 (by rfl) ⟨166053, by rfl⟩ : syracuseStep 1771237 = 332107) (by norm_num)
theorem B2098973 : Blo 1242439 2098973 := bbase (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) (by norm_num)
theorem B2361125 : Blo 1242439 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B1681205 : Blo 1242439 1681205 := bbase (se 5 (by rfl) ⟨78806, by rfl⟩ : syracuseStep 1681205 = 157613) (by norm_num)
theorem B2656061 : Blo 1242439 2656061 := bbase (se 3 (by rfl) ⟨498011, by rfl⟩ : syracuseStep 2656061 = 996023) (by norm_num)
theorem B1574741 : Blo 1242439 1574741 := bbase (se 9 (by rfl) ⟨4613, by rfl⟩ : syracuseStep 1574741 = 9227) (by norm_num)
theorem B1574797 : Blo 1242439 1574797 := bbase (se 3 (by rfl) ⟨295274, by rfl⟩ : syracuseStep 1574797 = 590549) (by norm_num)
theorem B2099101 : Blo 1242439 2099101 := bbase (se 3 (by rfl) ⟨393581, by rfl⟩ : syracuseStep 2099101 = 787163) (by norm_num)
theorem B2271149 : Blo 1242439 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B1574893 : Blo 1242439 1574893 := bbase (se 3 (by rfl) ⟨295292, by rfl⟩ : syracuseStep 1574893 = 590585) (by norm_num)
theorem B2099189 : Blo 1242439 2099189 := bbase (se 5 (by rfl) ⟨98399, by rfl⟩ : syracuseStep 2099189 = 196799) (by norm_num)
theorem B2795525 : Blo 1242439 2795525 := bbase (se 4 (by rfl) ⟨262080, by rfl⟩ : syracuseStep 2795525 = 524161) (by norm_num)
theorem B3147781 : Blo 1242439 3147781 := bbase (se 4 (by rfl) ⟨295104, by rfl⟩ : syracuseStep 3147781 = 590209) (by norm_num)
theorem B12757013 : Blo 1242439 12757013 := bbase (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) (by norm_num)
theorem B7079957 : Blo 1242439 7079957 := bbase (se 6 (by rfl) ⟨165936, by rfl⟩ : syracuseStep 7079957 = 331873) (by norm_num)
theorem B2656309 : Blo 1242439 2656309 := bbase (se 5 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 2656309 = 249029) (by norm_num)
theorem B1771573 : Blo 1242439 1771573 := bbase (se 5 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 1771573 = 166085) (by norm_num)
theorem B2361413 : Blo 1242439 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B2795597 : Blo 1242439 2795597 := bbase (se 3 (by rfl) ⟨524174, by rfl⟩ : syracuseStep 2795597 = 1048349) (by norm_num)
theorem B1345621 : Blo 1242439 1345621 := bbase (se 8 (by rfl) ⟨7884, by rfl⟩ : syracuseStep 1345621 = 15769) (by norm_num)
theorem B3147893 : Blo 1242439 3147893 := bbase (se 5 (by rfl) ⟨147557, by rfl⟩ : syracuseStep 3147893 = 295115) (by norm_num)
theorem B2099317 : Blo 1242439 2099317 := bbase (se 5 (by rfl) ⟨98405, by rfl⟩ : syracuseStep 2099317 = 196811) (by norm_num)
theorem B2795669 : Blo 1242439 2795669 := bbase (se 6 (by rfl) ⟨65523, by rfl⟩ : syracuseStep 2795669 = 131047) (by norm_num)
theorem B4196501 : Blo 1242439 4196501 := bbase (se 6 (by rfl) ⟨98355, by rfl⟩ : syracuseStep 4196501 = 196711) (by norm_num)
theorem B1992853 : Blo 1242439 1992853 := bbase (se 6 (by rfl) ⟨46707, by rfl⟩ : syracuseStep 1992853 = 93415) (by norm_num)
theorem B2017445 : Blo 1242439 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B2099405 : Blo 1242439 2099405 := bbase (se 3 (by rfl) ⟨393638, by rfl⟩ : syracuseStep 2099405 = 787277) (by norm_num)
theorem B10774741 : Blo 1242439 10774741 := bbase (se 7 (by rfl) ⟨126266, by rfl⟩ : syracuseStep 10774741 = 252533) (by norm_num)
theorem B2795741 : Blo 1242439 2795741 := bbase (se 3 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 2795741 = 1048403) (by norm_num)
theorem B2361565 : Blo 1242439 2361565 := bbase (se 3 (by rfl) ⟨442793, by rfl⟩ : syracuseStep 2361565 = 885587) (by norm_num)
theorem B1771789 : Blo 1242439 1771789 := bbase (se 3 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 1771789 = 664421) (by norm_num)
theorem B2795813 : Blo 1242439 2795813 := bbase (se 4 (by rfl) ⟨262107, by rfl⟩ : syracuseStep 2795813 = 524215) (by norm_num)
theorem B3148085 : Blo 1242439 3148085 := bbase (se 5 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 3148085 = 295133) (by norm_num)
theorem B2099533 : Blo 1242439 2099533 := bbase (se 3 (by rfl) ⟨393662, by rfl⟩ : syracuseStep 2099533 = 787325) (by norm_num)
theorem B6293861 : Blo 1242439 6293861 := bbase (se 4 (by rfl) ⟨590049, by rfl⟩ : syracuseStep 6293861 = 1180099) (by norm_num)
theorem B2795885 : Blo 1242439 2795885 := bbase (se 3 (by rfl) ⟨524228, by rfl⟩ : syracuseStep 2795885 = 1048457) (by norm_num)
theorem B2099621 : Blo 1242439 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B2795957 : Blo 1242439 2795957 := bbase (se 5 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 2795957 = 262121) (by norm_num)
theorem B4721125 : Blo 1242439 4721125 := bbase (se 4 (by rfl) ⟨442605, by rfl⟩ : syracuseStep 4721125 = 885211) (by norm_num)
theorem B2796029 : Blo 1242439 2796029 := bbase (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) (by norm_num)
theorem B2361869 : Blo 1242439 2361869 := bbase (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) (by norm_num)
theorem B1493525 : Blo 1242439 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B2099749 : Blo 1242439 2099749 := bbase (se 4 (by rfl) ⟨196851, by rfl⟩ : syracuseStep 2099749 = 393703) (by norm_num)
theorem B2656813 : Blo 1242439 2656813 := bbase (se 3 (by rfl) ⟨498152, by rfl⟩ : syracuseStep 2656813 = 996305) (by norm_num)
theorem B2796101 : Blo 1242439 2796101 := bbase (se 4 (by rfl) ⟨262134, by rfl⟩ : syracuseStep 2796101 = 524269) (by norm_num)
theorem B1493573 : Blo 1242439 1493573 := bbase (se 4 (by rfl) ⟨140022, by rfl⟩ : syracuseStep 1493573 = 280045) (by norm_num)
theorem B4196933 : Blo 1242439 4196933 := bbase (se 4 (by rfl) ⟨393462, by rfl⟩ : syracuseStep 4196933 = 786925) (by norm_num)
theorem B3541573 : Blo 1242439 3541573 := bbase (se 4 (by rfl) ⟨332022, by rfl⟩ : syracuseStep 3541573 = 664045) (by norm_num)
theorem B2099837 : Blo 1242439 2099837 := bbase (se 3 (by rfl) ⟨393719, by rfl⟩ : syracuseStep 2099837 = 787439) (by norm_num)
theorem B2796173 : Blo 1242439 2796173 := bbase (se 3 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 2796173 = 1048565) (by norm_num)
theorem B3148429 : Blo 1242439 3148429 := bbase (se 3 (by rfl) ⟨590330, by rfl⟩ : syracuseStep 3148429 = 1180661) (by norm_num)
theorem B2796245 : Blo 1242439 2796245 := bbase (se 7 (by rfl) ⟨32768, by rfl⟩ : syracuseStep 2796245 = 65537) (by norm_num)
theorem B3148541 : Blo 1242439 3148541 := bbase (se 3 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 3148541 = 1180703) (by norm_num)
theorem B2099965 : Blo 1242439 2099965 := bbase (se 3 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 2099965 = 787487) (by norm_num)
theorem B4721429 : Blo 1242439 4721429 := bbase (se 6 (by rfl) ⟨110658, by rfl⟩ : syracuseStep 4721429 = 221317) (by norm_num)
theorem B2796317 : Blo 1242439 2796317 := bbase (se 3 (by rfl) ⟨524309, by rfl⟩ : syracuseStep 2796317 = 1048619) (by norm_num)
theorem B2239301 : Blo 1242439 2239301 := bbase (se 4 (by rfl) ⟨209934, by rfl⟩ : syracuseStep 2239301 = 419869) (by norm_num)
theorem B2796389 : Blo 1242439 2796389 := bbase (se 4 (by rfl) ⟨262161, by rfl⟩ : syracuseStep 2796389 = 524323) (by norm_num)
theorem B2796461 : Blo 1242439 2796461 := bbase (se 3 (by rfl) ⟨524336, by rfl⟩ : syracuseStep 2796461 = 1048673) (by norm_num)
theorem B3148733 : Blo 1242439 3148733 := bbase (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) (by norm_num)
theorem B2796533 : Blo 1242439 2796533 := bbase (se 5 (by rfl) ⟨131087, by rfl⟩ : syracuseStep 2796533 = 262175) (by norm_num)
theorem B4197365 : Blo 1242439 4197365 := bbase (se 5 (by rfl) ⟨196751, by rfl⟩ : syracuseStep 4197365 = 393503) (by norm_num)
theorem B2796605 : Blo 1242439 2796605 := bbase (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) (by norm_num)
theorem B1494121 : Blo 1242439 1494121 := bbase (se 2 (by rfl) ⟨560295, by rfl⟩ : syracuseStep 1494121 = 1120591) (by norm_num)
theorem B2796677 : Blo 1242439 2796677 := bbase (se 4 (by rfl) ⟨262188, by rfl⟩ : syracuseStep 2796677 = 524377) (by norm_num)
theorem B3361925 : Blo 1242439 3361925 := bbase (se 4 (by rfl) ⟨315180, by rfl⟩ : syracuseStep 3361925 = 630361) (by norm_num)
theorem B7081141 : Blo 1242439 7081141 := bbase (se 5 (by rfl) ⟨331928, by rfl⟩ : syracuseStep 7081141 = 663857) (by norm_num)
theorem B2837701 : Blo 1242439 2837701 := bbase (se 4 (by rfl) ⟨266034, by rfl⟩ : syracuseStep 2837701 = 532069) (by norm_num)
theorem B2796749 : Blo 1242439 2796749 := bbase (se 3 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 2796749 = 1048781) (by norm_num)
theorem B1346765 : Blo 1242439 1346765 := bbase (se 3 (by rfl) ⟨252518, by rfl⟩ : syracuseStep 1346765 = 505037) (by norm_num)
theorem B2796821 : Blo 1242439 2796821 := bbase (se 6 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 2796821 = 131101) (by norm_num)
theorem B3149077 : Blo 1242439 3149077 := bbase (se 6 (by rfl) ⟨73806, by rfl⟩ : syracuseStep 3149077 = 147613) (by norm_num)
theorem B5311813 : Blo 1242439 5311813 := bbase (se 4 (by rfl) ⟨497982, by rfl⟩ : syracuseStep 5311813 = 995965) (by norm_num)
theorem B2837845 : Blo 1242439 2837845 := bbase (se 11 (by rfl) ⟨2078, by rfl⟩ : syracuseStep 2837845 = 4157) (by norm_num)
theorem B2796893 : Blo 1242439 2796893 := bbase (se 3 (by rfl) ⟨524417, by rfl⟩ : syracuseStep 2796893 = 1048835) (by norm_num)
theorem B5041541 : Blo 1242439 5041541 := bbase (se 4 (by rfl) ⟨472644, by rfl⟩ : syracuseStep 5041541 = 945289) (by norm_num)
theorem B3149189 : Blo 1242439 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B2796965 : Blo 1242439 2796965 := bbase (se 4 (by rfl) ⟨262215, by rfl⟩ : syracuseStep 2796965 = 524431) (by norm_num)
theorem B4197797 : Blo 1242439 4197797 := bbase (se 4 (by rfl) ⟨393543, by rfl⟩ : syracuseStep 4197797 = 787087) (by norm_num)
theorem B2657701 : Blo 1242439 2657701 := bbase (se 4 (by rfl) ⟨249159, by rfl⟩ : syracuseStep 2657701 = 498319) (by norm_num)
theorem B7966133 : Blo 1242439 7966133 := bbase (se 5 (by rfl) ⟨373412, by rfl⟩ : syracuseStep 7966133 = 746825) (by norm_num)
theorem B11505077 : Blo 1242439 11505077 := bbase (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) (by norm_num)
theorem B2797037 : Blo 1242439 2797037 := bbase (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) (by norm_num)
theorem B5041685 : Blo 1242439 5041685 := bbase (se 6 (by rfl) ⟨118164, by rfl⟩ : syracuseStep 5041685 = 236329) (by norm_num)
theorem B13454869 : Blo 1242439 13454869 := bbase (se 6 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 13454869 = 630697) (by norm_num)
theorem B2797109 : Blo 1242439 2797109 := bbase (se 5 (by rfl) ⟨131114, by rfl⟩ : syracuseStep 2797109 = 262229) (by norm_num)
theorem B3149381 : Blo 1242439 3149381 := bbase (se 4 (by rfl) ⟨295254, by rfl⟩ : syracuseStep 3149381 = 590509) (by norm_num)
theorem B1494601 : Blo 1242439 1494601 := bbase (se 2 (by rfl) ⟨560475, by rfl⟩ : syracuseStep 1494601 = 1120951) (by norm_num)
theorem B2985589 : Blo 1242439 2985589 := bbase (se 5 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 2985589 = 279899) (by norm_num)
theorem B6295157 : Blo 1242439 6295157 := bbase (se 5 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 6295157 = 590171) (by norm_num)
theorem B2797181 : Blo 1242439 2797181 := bbase (se 3 (by rfl) ⟨524471, by rfl⟩ : syracuseStep 2797181 = 1048943) (by norm_num)
theorem B2797253 : Blo 1242439 2797253 := bbase (se 4 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 2797253 = 524485) (by norm_num)
theorem B2797325 : Blo 1242439 2797325 := bbase (se 3 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 2797325 = 1048997) (by norm_num)
theorem B2797397 : Blo 1242439 2797397 := bbase (se 9 (by rfl) ⟨8195, by rfl⟩ : syracuseStep 2797397 = 16391) (by norm_num)
theorem B4198229 : Blo 1242439 4198229 := bbase (se 9 (by rfl) ⟨12299, by rfl⟩ : syracuseStep 4198229 = 24599) (by norm_num)
theorem B2797469 : Blo 1242439 2797469 := bbase (se 3 (by rfl) ⟨524525, by rfl⟩ : syracuseStep 2797469 = 1049051) (by norm_num)
theorem B3149725 : Blo 1242439 3149725 := bbase (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) (by norm_num)
theorem B2797541 : Blo 1242439 2797541 := bbase (se 4 (by rfl) ⟨262269, by rfl⟩ : syracuseStep 2797541 = 524539) (by norm_num)
theorem B1863677 : Blo 1242439 1863677 := bbase (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) (by norm_num)
theorem B3149837 : Blo 1242439 3149837 := bbase (se 3 (by rfl) ⟨590594, by rfl⟩ : syracuseStep 3149837 = 1181189) (by norm_num)
theorem B1863701 : Blo 1242439 1863701 := bbase (se 6 (by rfl) ⟨43680, by rfl⟩ : syracuseStep 1863701 = 87361) (by norm_num)
theorem B5386261 : Blo 1242439 5386261 := bbase (se 6 (by rfl) ⟨126240, by rfl⟩ : syracuseStep 5386261 = 252481) (by norm_num)
theorem B3543077 : Blo 1242439 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B1863725 : Blo 1242439 1863725 := bbase (se 3 (by rfl) ⟨349448, by rfl⟩ : syracuseStep 1863725 = 698897) (by norm_num)
theorem B2797613 : Blo 1242439 2797613 := bbase (se 3 (by rfl) ⟨524552, by rfl⟩ : syracuseStep 2797613 = 1049105) (by norm_num)
theorem B1863749 : Blo 1242439 1863749 := bbase (se 4 (by rfl) ⟨174726, by rfl⟩ : syracuseStep 1863749 = 349453) (by norm_num)
theorem B1863773 : Blo 1242439 1863773 := bbase (se 3 (by rfl) ⟨349457, by rfl⟩ : syracuseStep 1863773 = 698915) (by norm_num)
theorem B1863797 : Blo 1242439 1863797 := bbase (se 5 (by rfl) ⟨87365, by rfl⟩ : syracuseStep 1863797 = 174731) (by norm_num)
theorem B2797685 : Blo 1242439 2797685 := bbase (se 5 (by rfl) ⟨131141, by rfl⟩ : syracuseStep 2797685 = 262283) (by norm_num)
theorem B1863821 : Blo 1242439 1863821 := bbase (se 3 (by rfl) ⟨349466, by rfl⟩ : syracuseStep 1863821 = 698933) (by norm_num)
theorem B3190933 : Blo 1242439 3190933 := bbase (se 6 (by rfl) ⟨74787, by rfl⟩ : syracuseStep 3190933 = 149575) (by norm_num)
theorem B1863845 : Blo 1242439 1863845 := bbase (se 4 (by rfl) ⟨174735, by rfl⟩ : syracuseStep 1863845 = 349471) (by norm_num)
theorem B1863869 : Blo 1242439 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B2797757 : Blo 1242439 2797757 := bbase (se 3 (by rfl) ⟨524579, by rfl⟩ : syracuseStep 2797757 = 1049159) (by norm_num)
theorem B1863893 : Blo 1242439 1863893 := bbase (se 7 (by rfl) ⟨21842, by rfl⟩ : syracuseStep 1863893 = 43685) (by norm_num)
theorem B1863917 : Blo 1242439 1863917 := bbase (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) (by norm_num)
theorem B1863941 : Blo 1242439 1863941 := bbase (se 4 (by rfl) ⟨174744, by rfl⟩ : syracuseStep 1863941 = 349489) (by norm_num)
theorem B2797829 : Blo 1242439 2797829 := bbase (se 4 (by rfl) ⟨262296, by rfl⟩ : syracuseStep 2797829 = 524593) (by norm_num)
theorem B4198661 : Blo 1242439 4198661 := bbase (se 4 (by rfl) ⟨393624, by rfl⟩ : syracuseStep 4198661 = 787249) (by norm_num)
theorem B23892245 : Blo 1242439 23892245 := bbase (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) (by norm_num)
theorem B6721813 : Blo 1242439 6721813 := bbase (se 6 (by rfl) ⟨157542, by rfl⟩ : syracuseStep 6721813 = 315085) (by norm_num)
theorem B1863965 : Blo 1242439 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B1863989 : Blo 1242439 1863989 := bbase (se 5 (by rfl) ⟨87374, by rfl⟩ : syracuseStep 1863989 = 174749) (by norm_num)
theorem B2240821 : Blo 1242439 2240821 := bbase (se 5 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 2240821 = 210077) (by norm_num)
theorem B1864013 : Blo 1242439 1864013 := bbase (se 3 (by rfl) ⟨349502, by rfl⟩ : syracuseStep 1864013 = 699005) (by norm_num)
theorem B2797901 : Blo 1242439 2797901 := bbase (se 3 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 2797901 = 1049213) (by norm_num)
theorem B1864037 : Blo 1242439 1864037 := bbase (se 4 (by rfl) ⟨174753, by rfl⟩ : syracuseStep 1864037 = 349507) (by norm_num)
theorem B1864061 : Blo 1242439 1864061 := bbase (se 3 (by rfl) ⟨349511, by rfl⟩ : syracuseStep 1864061 = 699023) (by norm_num)
theorem B1864085 : Blo 1242439 1864085 := bbase (se 6 (by rfl) ⟨43689, by rfl⟩ : syracuseStep 1864085 = 87379) (by norm_num)
theorem B2797973 : Blo 1242439 2797973 := bbase (se 6 (by rfl) ⟨65577, by rfl⟩ : syracuseStep 2797973 = 131155) (by norm_num)
theorem B1864109 : Blo 1242439 1864109 := bbase (se 3 (by rfl) ⟨349520, by rfl⟩ : syracuseStep 1864109 = 699041) (by norm_num)
theorem B1864133 : Blo 1242439 1864133 := bbase (se 4 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 1864133 = 349525) (by norm_num)
theorem B1864157 : Blo 1242439 1864157 := bbase (se 3 (by rfl) ⟨349529, by rfl⟩ : syracuseStep 1864157 = 699059) (by norm_num)
theorem B2798045 : Blo 1242439 2798045 := bbase (se 3 (by rfl) ⟨524633, by rfl⟩ : syracuseStep 2798045 = 1049267) (by norm_num)
theorem B1864181 : Blo 1242439 1864181 := bbase (se 5 (by rfl) ⟨87383, by rfl⟩ : syracuseStep 1864181 = 174767) (by norm_num)
theorem B1864205 : Blo 1242439 1864205 := bbase (se 3 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 1864205 = 699077) (by norm_num)
theorem B2241037 : Blo 1242439 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B1864229 : Blo 1242439 1864229 := bbase (se 4 (by rfl) ⟨174771, by rfl⟩ : syracuseStep 1864229 = 349543) (by norm_num)
theorem B2798117 : Blo 1242439 2798117 := bbase (se 4 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 2798117 = 524647) (by norm_num)
theorem B1864253 : Blo 1242439 1864253 := bbase (se 3 (by rfl) ⟨349547, by rfl⟩ : syracuseStep 1864253 = 699095) (by norm_num)
theorem B1864277 : Blo 1242439 1864277 := bbase (se 8 (by rfl) ⟨10923, by rfl⟩ : syracuseStep 1864277 = 21847) (by norm_num)
theorem B1864301 : Blo 1242439 1864301 := bbase (se 3 (by rfl) ⟨349556, by rfl⟩ : syracuseStep 1864301 = 699113) (by norm_num)
theorem B2798189 : Blo 1242439 2798189 := bbase (se 3 (by rfl) ⟨524660, by rfl⟩ : syracuseStep 2798189 = 1049321) (by norm_num)
theorem B1864325 : Blo 1242439 1864325 := bbase (se 4 (by rfl) ⟨174780, by rfl⟩ : syracuseStep 1864325 = 349561) (by norm_num)
theorem B1864349 : Blo 1242439 1864349 := bbase (se 3 (by rfl) ⟨349565, by rfl⟩ : syracuseStep 1864349 = 699131) (by norm_num)
theorem B1864373 : Blo 1242439 1864373 := bbase (se 5 (by rfl) ⟨87392, by rfl⟩ : syracuseStep 1864373 = 174785) (by norm_num)
theorem B2798261 : Blo 1242439 2798261 := bbase (se 5 (by rfl) ⟨131168, by rfl⟩ : syracuseStep 2798261 = 262337) (by norm_num)
theorem B4199093 : Blo 1242439 4199093 := bbase (se 5 (by rfl) ⟨196832, by rfl⟩ : syracuseStep 4199093 = 393665) (by norm_num)
theorem B1864397 : Blo 1242439 1864397 := bbase (se 3 (by rfl) ⟨349574, by rfl⟩ : syracuseStep 1864397 = 699149) (by norm_num)
theorem B1864421 : Blo 1242439 1864421 := bbase (se 4 (by rfl) ⟨174789, by rfl⟩ : syracuseStep 1864421 = 349579) (by norm_num)
theorem B1864445 : Blo 1242439 1864445 := bbase (se 3 (by rfl) ⟨349583, by rfl⟩ : syracuseStep 1864445 = 699167) (by norm_num)
theorem B2798333 : Blo 1242439 2798333 := bbase (se 3 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 2798333 = 1049375) (by norm_num)
theorem B1864469 : Blo 1242439 1864469 := bbase (se 6 (by rfl) ⟨43698, by rfl⟩ : syracuseStep 1864469 = 87397) (by norm_num)
theorem B1864493 : Blo 1242439 1864493 := bbase (se 3 (by rfl) ⟨349592, by rfl⟩ : syracuseStep 1864493 = 699185) (by norm_num)
theorem B2241325 : Blo 1242439 2241325 := bbase (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) (by norm_num)
theorem B1364797 : Blo 1242439 1364797 := bbase (se 3 (by rfl) ⟨255899, by rfl⟩ : syracuseStep 1364797 = 511799) (by norm_num)
theorem B1864517 : Blo 1242439 1864517 := bbase (se 4 (by rfl) ⟨174798, by rfl⟩ : syracuseStep 1864517 = 349597) (by norm_num)
theorem B2798405 : Blo 1242439 2798405 := bbase (se 4 (by rfl) ⟨262350, by rfl⟩ : syracuseStep 2798405 = 524701) (by norm_num)
theorem B4723541 : Blo 1242439 4723541 := bbase (se 9 (by rfl) ⟨13838, by rfl⟩ : syracuseStep 4723541 = 27677) (by norm_num)
theorem B1864541 : Blo 1242439 1864541 := bbase (se 3 (by rfl) ⟨349601, by rfl⟩ : syracuseStep 1864541 = 699203) (by norm_num)
theorem B1864565 : Blo 1242439 1864565 := bbase (se 5 (by rfl) ⟨87401, by rfl⟩ : syracuseStep 1864565 = 174803) (by norm_num)
theorem B6296453 : Blo 1242439 6296453 := bbase (se 4 (by rfl) ⟨590292, by rfl⟩ : syracuseStep 6296453 = 1180585) (by norm_num)
theorem B3986309 : Blo 1242439 3986309 := bbase (se 4 (by rfl) ⟨373716, by rfl⟩ : syracuseStep 3986309 = 747433) (by norm_num)
theorem B1864589 : Blo 1242439 1864589 := bbase (se 3 (by rfl) ⟨349610, by rfl⟩ : syracuseStep 1864589 = 699221) (by norm_num)
theorem B2798477 : Blo 1242439 2798477 := bbase (se 3 (by rfl) ⟨524714, by rfl⟩ : syracuseStep 2798477 = 1049429) (by norm_num)
theorem B1889173 : Blo 1242439 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B1864613 : Blo 1242439 1864613 := bbase (se 4 (by rfl) ⟨174807, by rfl⟩ : syracuseStep 1864613 = 349615) (by norm_num)
theorem B1864637 : Blo 1242439 1864637 := bbase (se 3 (by rfl) ⟨349619, by rfl⟩ : syracuseStep 1864637 = 699239) (by norm_num)
theorem B1864661 : Blo 1242439 1864661 := bbase (se 7 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 1864661 = 43703) (by norm_num)
theorem B2798549 : Blo 1242439 2798549 := bbase (se 7 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 2798549 = 65591) (by norm_num)
theorem B2986973 : Blo 1242439 2986973 := bbase (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) (by norm_num)
theorem B5977061 : Blo 1242439 5977061 := bbase (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) (by norm_num)
theorem B1864685 : Blo 1242439 1864685 := bbase (se 3 (by rfl) ⟨349628, by rfl⟩ : syracuseStep 1864685 = 699257) (by norm_num)
theorem B1397749 : Blo 1242439 1397749 := bbase (se 5 (by rfl) ⟨65519, by rfl⟩ : syracuseStep 1397749 = 131039) (by norm_num)
theorem B1889269 : Blo 1242439 1889269 := bbase (se 5 (by rfl) ⟨88559, by rfl⟩ : syracuseStep 1889269 = 177119) (by norm_num)
theorem B1864709 : Blo 1242439 1864709 := bbase (se 4 (by rfl) ⟨174816, by rfl⟩ : syracuseStep 1864709 = 349633) (by norm_num)
theorem B1397785 : Blo 1242439 1397785 := bbase (se 2 (by rfl) ⟨524169, by rfl⟩ : syracuseStep 1397785 = 1048339) (by norm_num)
theorem B1864733 : Blo 1242439 1864733 := bbase (se 3 (by rfl) ⟨349637, by rfl⟩ : syracuseStep 1864733 = 699275) (by norm_num)
theorem B2798621 : Blo 1242439 2798621 := bbase (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) (by norm_num)
theorem B1864757 : Blo 1242439 1864757 := bbase (se 5 (by rfl) ⟨87410, by rfl⟩ : syracuseStep 1864757 = 174821) (by norm_num)
theorem B1397821 : Blo 1242439 1397821 := bbase (se 3 (by rfl) ⟨262091, by rfl⟩ : syracuseStep 1397821 = 524183) (by norm_num)
theorem B1864781 : Blo 1242439 1864781 := bbase (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) (by norm_num)
theorem B1397857 : Blo 1242439 1397857 := bbase (se 2 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 1397857 = 1048393) (by norm_num)
theorem B1864805 : Blo 1242439 1864805 := bbase (se 4 (by rfl) ⟨174825, by rfl⟩ : syracuseStep 1864805 = 349651) (by norm_num)
theorem B2798693 : Blo 1242439 2798693 := bbase (se 4 (by rfl) ⟨262377, by rfl⟩ : syracuseStep 2798693 = 524755) (by norm_num)
theorem B4199525 : Blo 1242439 4199525 := bbase (se 4 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 4199525 = 787411) (by norm_num)
theorem B7083125 : Blo 1242439 7083125 := bbase (se 5 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 7083125 = 664043) (by norm_num)
theorem B4723829 : Blo 1242439 4723829 := bbase (se 5 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 4723829 = 442859) (by norm_num)
theorem B1864829 : Blo 1242439 1864829 := bbase (se 3 (by rfl) ⟨349655, by rfl⟩ : syracuseStep 1864829 = 699311) (by norm_num)
theorem B1397893 : Blo 1242439 1397893 := bbase (se 4 (by rfl) ⟨131052, by rfl⟩ : syracuseStep 1397893 = 262105) (by norm_num)
theorem B1864853 : Blo 1242439 1864853 := bbase (se 6 (by rfl) ⟨43707, by rfl⟩ : syracuseStep 1864853 = 87415) (by norm_num)
theorem B2987165 : Blo 1242439 2987165 := bbase (se 3 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 2987165 = 1120187) (by norm_num)
theorem B5977253 : Blo 1242439 5977253 := bbase (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) (by norm_num)
theorem B1397929 : Blo 1242439 1397929 := bbase (se 2 (by rfl) ⟨524223, by rfl⟩ : syracuseStep 1397929 = 1048447) (by norm_num)
theorem B1864877 : Blo 1242439 1864877 := bbase (se 3 (by rfl) ⟨349664, by rfl⟩ : syracuseStep 1864877 = 699329) (by norm_num)
theorem B2798765 : Blo 1242439 2798765 := bbase (se 3 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 2798765 = 1049537) (by norm_num)
theorem B3028157 : Blo 1242439 3028157 := bbase (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) (by norm_num)
theorem B1864901 : Blo 1242439 1864901 := bbase (se 4 (by rfl) ⟨174834, by rfl⟩ : syracuseStep 1864901 = 349669) (by norm_num)
theorem B1397965 : Blo 1242439 1397965 := bbase (se 3 (by rfl) ⟨262118, by rfl⟩ : syracuseStep 1397965 = 524237) (by norm_num)
theorem B1864925 : Blo 1242439 1864925 := bbase (se 3 (by rfl) ⟨349673, by rfl⟩ : syracuseStep 1864925 = 699347) (by norm_num)
theorem B1398001 : Blo 1242439 1398001 := bbase (se 2 (by rfl) ⟨524250, by rfl⟩ : syracuseStep 1398001 = 1048501) (by norm_num)
theorem B1864949 : Blo 1242439 1864949 := bbase (se 5 (by rfl) ⟨87419, by rfl⟩ : syracuseStep 1864949 = 174839) (by norm_num)
theorem B2798837 : Blo 1242439 2798837 := bbase (se 5 (by rfl) ⟨131195, by rfl⟩ : syracuseStep 2798837 = 262391) (by norm_num)
theorem B1864973 : Blo 1242439 1864973 := bbase (se 3 (by rfl) ⟨349682, by rfl⟩ : syracuseStep 1864973 = 699365) (by norm_num)
theorem B1398037 : Blo 1242439 1398037 := bbase (se 6 (by rfl) ⟨32766, by rfl⟩ : syracuseStep 1398037 = 65533) (by norm_num)
theorem B1864997 : Blo 1242439 1864997 := bbase (se 4 (by rfl) ⟨174843, by rfl⟩ : syracuseStep 1864997 = 349687) (by norm_num)
theorem B1398073 : Blo 1242439 1398073 := bbase (se 2 (by rfl) ⟨524277, by rfl⟩ : syracuseStep 1398073 = 1048555) (by norm_num)
theorem B1865021 : Blo 1242439 1865021 := bbase (se 3 (by rfl) ⟨349691, by rfl⟩ : syracuseStep 1865021 = 699383) (by norm_num)
theorem B2798909 : Blo 1242439 2798909 := bbase (se 3 (by rfl) ⟨524795, by rfl⟩ : syracuseStep 2798909 = 1049591) (by norm_num)
theorem B1865045 : Blo 1242439 1865045 := bbase (se 13 (by rfl) ⟨341, by rfl⟩ : syracuseStep 1865045 = 683) (by norm_num)
theorem B1398109 : Blo 1242439 1398109 := bbase (se 3 (by rfl) ⟨262145, by rfl⟩ : syracuseStep 1398109 = 524291) (by norm_num)
theorem B1865069 : Blo 1242439 1865069 := bbase (se 3 (by rfl) ⟨349700, by rfl⟩ : syracuseStep 1865069 = 699401) (by norm_num)
theorem B1398145 : Blo 1242439 1398145 := bbase (se 2 (by rfl) ⟨524304, by rfl⟩ : syracuseStep 1398145 = 1048609) (by norm_num)
theorem B1865093 : Blo 1242439 1865093 := bbase (se 4 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 1865093 = 349705) (by norm_num)
theorem B2798981 : Blo 1242439 2798981 := bbase (se 4 (by rfl) ⟨262404, by rfl⟩ : syracuseStep 2798981 = 524809) (by norm_num)
theorem B1865117 : Blo 1242439 1865117 := bbase (se 3 (by rfl) ⟨349709, by rfl⟩ : syracuseStep 1865117 = 699419) (by norm_num)
theorem B1398181 : Blo 1242439 1398181 := bbase (se 4 (by rfl) ⟨131079, by rfl⟩ : syracuseStep 1398181 = 262159) (by norm_num)
theorem B1865141 : Blo 1242439 1865141 := bbase (se 5 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 1865141 = 174857) (by norm_num)
theorem B2241989 : Blo 1242439 2241989 := bbase (se 4 (by rfl) ⟨210186, by rfl⟩ : syracuseStep 2241989 = 420373) (by norm_num)
theorem B1398217 : Blo 1242439 1398217 := bbase (se 2 (by rfl) ⟨524331, by rfl⟩ : syracuseStep 1398217 = 1048663) (by norm_num)
theorem B1865165 : Blo 1242439 1865165 := bbase (se 3 (by rfl) ⟨349718, by rfl⟩ : syracuseStep 1865165 = 699437) (by norm_num)
theorem B2799053 : Blo 1242439 2799053 := bbase (se 3 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 2799053 = 1049645) (by norm_num)
theorem B10221013 : Blo 1242439 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B1865189 : Blo 1242439 1865189 := bbase (se 4 (by rfl) ⟨174861, by rfl⟩ : syracuseStep 1865189 = 349723) (by norm_num)
theorem B1398253 : Blo 1242439 1398253 := bbase (se 3 (by rfl) ⟨262172, by rfl⟩ : syracuseStep 1398253 = 524345) (by norm_num)
theorem B1865213 : Blo 1242439 1865213 := bbase (se 3 (by rfl) ⟨349727, by rfl⟩ : syracuseStep 1865213 = 699455) (by norm_num)
theorem B1398289 : Blo 1242439 1398289 := bbase (se 2 (by rfl) ⟨524358, by rfl⟩ : syracuseStep 1398289 = 1048717) (by norm_num)
theorem B1865237 : Blo 1242439 1865237 := bbase (se 6 (by rfl) ⟨43716, by rfl⟩ : syracuseStep 1865237 = 87433) (by norm_num)
theorem B2799125 : Blo 1242439 2799125 := bbase (se 6 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 2799125 = 131209) (by norm_num)
theorem B4199957 : Blo 1242439 4199957 := bbase (se 6 (by rfl) ⟨98436, by rfl⟩ : syracuseStep 4199957 = 196873) (by norm_num)
theorem B5977637 : Blo 1242439 5977637 := bbase (se 4 (by rfl) ⟨560403, by rfl⟩ : syracuseStep 5977637 = 1120807) (by norm_num)
theorem B1865261 : Blo 1242439 1865261 := bbase (se 3 (by rfl) ⟨349736, by rfl⟩ : syracuseStep 1865261 = 699473) (by norm_num)
theorem B1398325 : Blo 1242439 1398325 := bbase (se 5 (by rfl) ⟨65546, by rfl⟩ : syracuseStep 1398325 = 131093) (by norm_num)
theorem B1865285 : Blo 1242439 1865285 := bbase (se 4 (by rfl) ⟨174870, by rfl⟩ : syracuseStep 1865285 = 349741) (by norm_num)
theorem B1398361 : Blo 1242439 1398361 := bbase (se 2 (by rfl) ⟨524385, by rfl⟩ : syracuseStep 1398361 = 1048771) (by norm_num)
theorem B1865309 : Blo 1242439 1865309 := bbase (se 3 (by rfl) ⟨349745, by rfl⟩ : syracuseStep 1865309 = 699491) (by norm_num)
theorem B2799197 : Blo 1242439 2799197 := bbase (se 3 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 2799197 = 1049699) (by norm_num)
theorem B1865333 : Blo 1242439 1865333 := bbase (se 5 (by rfl) ⟨87437, by rfl⟩ : syracuseStep 1865333 = 174875) (by norm_num)
theorem B1398397 : Blo 1242439 1398397 := bbase (se 3 (by rfl) ⟨262199, by rfl⟩ : syracuseStep 1398397 = 524399) (by norm_num)
theorem B1865357 : Blo 1242439 1865357 := bbase (se 3 (by rfl) ⟨349754, by rfl⟩ : syracuseStep 1865357 = 699509) (by norm_num)
theorem B1398433 : Blo 1242439 1398433 := bbase (se 2 (by rfl) ⟨524412, by rfl⟩ : syracuseStep 1398433 = 1048825) (by norm_num)
theorem B1865381 : Blo 1242439 1865381 := bbase (se 4 (by rfl) ⟨174879, by rfl⟩ : syracuseStep 1865381 = 349759) (by norm_num)
theorem B2799269 : Blo 1242439 2799269 := bbase (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) (by norm_num)
theorem B1865405 : Blo 1242439 1865405 := bbase (se 3 (by rfl) ⟨349763, by rfl⟩ : syracuseStep 1865405 = 699527) (by norm_num)
theorem B1398469 : Blo 1242439 1398469 := bbase (se 4 (by rfl) ⟨131106, by rfl⟩ : syracuseStep 1398469 = 262213) (by norm_num)
theorem B2127557 : Blo 1242439 2127557 := bbase (se 4 (by rfl) ⟨199458, by rfl⟩ : syracuseStep 2127557 = 398917) (by norm_num)
theorem B1865429 : Blo 1242439 1865429 := bbase (se 7 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 1865429 = 43721) (by norm_num)
theorem B1398505 : Blo 1242439 1398505 := bbase (se 2 (by rfl) ⟨524439, by rfl⟩ : syracuseStep 1398505 = 1048879) (by norm_num)
theorem B1865453 : Blo 1242439 1865453 := bbase (se 3 (by rfl) ⟨349772, by rfl⟩ : syracuseStep 1865453 = 699545) (by norm_num)
theorem B2799341 : Blo 1242439 2799341 := bbase (se 3 (by rfl) ⟨524876, by rfl⟩ : syracuseStep 2799341 = 1049753) (by norm_num)
theorem B1865477 : Blo 1242439 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B1398541 : Blo 1242439 1398541 := bbase (se 3 (by rfl) ⟨262226, by rfl⟩ : syracuseStep 1398541 = 524453) (by norm_num)
theorem B1865501 : Blo 1242439 1865501 := bbase (se 3 (by rfl) ⟨349781, by rfl⟩ : syracuseStep 1865501 = 699563) (by norm_num)
theorem B1398577 : Blo 1242439 1398577 := bbase (se 2 (by rfl) ⟨524466, by rfl⟩ : syracuseStep 1398577 = 1048933) (by norm_num)
theorem B1865525 : Blo 1242439 1865525 := bbase (se 5 (by rfl) ⟨87446, by rfl⟩ : syracuseStep 1865525 = 174893) (by norm_num)
theorem B2799413 : Blo 1242439 2799413 := bbase (se 5 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 2799413 = 262445) (by norm_num)
theorem B1865549 : Blo 1242439 1865549 := bbase (se 3 (by rfl) ⟨349790, by rfl⟩ : syracuseStep 1865549 = 699581) (by norm_num)
theorem B1398613 : Blo 1242439 1398613 := bbase (se 9 (by rfl) ⟨4097, by rfl⟩ : syracuseStep 1398613 = 8195) (by norm_num)
theorem B2127701 : Blo 1242439 2127701 := bbase (se 9 (by rfl) ⟨6233, by rfl⟩ : syracuseStep 2127701 = 12467) (by norm_num)
theorem B1865573 : Blo 1242439 1865573 := bbase (se 4 (by rfl) ⟨174897, by rfl⟩ : syracuseStep 1865573 = 349795) (by norm_num)
theorem B1398649 : Blo 1242439 1398649 := bbase (se 2 (by rfl) ⟨524493, by rfl⟩ : syracuseStep 1398649 = 1048987) (by norm_num)
theorem B1865597 : Blo 1242439 1865597 := bbase (se 3 (by rfl) ⟨349799, by rfl⟩ : syracuseStep 1865597 = 699599) (by norm_num)
theorem B2799485 : Blo 1242439 2799485 := bbase (se 3 (by rfl) ⟨524903, by rfl⟩ : syracuseStep 2799485 = 1049807) (by norm_num)
theorem B2520973 : Blo 1242439 2520973 := bbase (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) (by norm_num)
theorem B1865621 : Blo 1242439 1865621 := bbase (se 6 (by rfl) ⟨43725, by rfl⟩ : syracuseStep 1865621 = 87451) (by norm_num)
theorem B1398685 : Blo 1242439 1398685 := bbase (se 3 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 1398685 = 524507) (by norm_num)
theorem B1865645 : Blo 1242439 1865645 := bbase (se 3 (by rfl) ⟨349808, by rfl⟩ : syracuseStep 1865645 = 699617) (by norm_num)
theorem B1398721 : Blo 1242439 1398721 := bbase (se 2 (by rfl) ⟨524520, by rfl⟩ : syracuseStep 1398721 = 1049041) (by norm_num)
theorem B1865669 : Blo 1242439 1865669 := bbase (se 4 (by rfl) ⟨174906, by rfl⟩ : syracuseStep 1865669 = 349813) (by norm_num)
theorem B2799557 : Blo 1242439 2799557 := bbase (se 4 (by rfl) ⟨262458, by rfl⟩ : syracuseStep 2799557 = 524917) (by norm_num)
theorem B1865693 : Blo 1242439 1865693 := bbase (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) (by norm_num)
theorem B1398757 : Blo 1242439 1398757 := bbase (se 4 (by rfl) ⟨131133, by rfl⟩ : syracuseStep 1398757 = 262267) (by norm_num)
theorem B1865717 : Blo 1242439 1865717 := bbase (se 5 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 1865717 = 174911) (by norm_num)
theorem B1398793 : Blo 1242439 1398793 := bbase (se 2 (by rfl) ⟨524547, by rfl⟩ : syracuseStep 1398793 = 1049095) (by norm_num)
theorem B1865741 : Blo 1242439 1865741 := bbase (se 3 (by rfl) ⟨349826, by rfl⟩ : syracuseStep 1865741 = 699653) (by norm_num)
theorem B2799629 : Blo 1242439 2799629 := bbase (se 3 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 2799629 = 1049861) (by norm_num)
theorem B1865765 : Blo 1242439 1865765 := bbase (se 4 (by rfl) ⟨174915, by rfl⟩ : syracuseStep 1865765 = 349831) (by norm_num)
theorem B1398829 : Blo 1242439 1398829 := bbase (se 3 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 1398829 = 524561) (by norm_num)
theorem B1865789 : Blo 1242439 1865789 := bbase (se 3 (by rfl) ⟨349835, by rfl⟩ : syracuseStep 1865789 = 699671) (by norm_num)
theorem B1398865 : Blo 1242439 1398865 := bbase (se 2 (by rfl) ⟨524574, by rfl⟩ : syracuseStep 1398865 = 1049149) (by norm_num)
theorem B1865813 : Blo 1242439 1865813 := bbase (se 8 (by rfl) ⟨10932, by rfl⟩ : syracuseStep 1865813 = 21865) (by norm_num)
theorem B2799701 : Blo 1242439 2799701 := bbase (se 8 (by rfl) ⟨16404, by rfl⟩ : syracuseStep 2799701 = 32809) (by norm_num)
theorem B1865837 : Blo 1242439 1865837 := bbase (se 3 (by rfl) ⟨349844, by rfl⟩ : syracuseStep 1865837 = 699689) (by norm_num)
theorem B1398901 : Blo 1242439 1398901 := bbase (se 5 (by rfl) ⟨65573, by rfl⟩ : syracuseStep 1398901 = 131147) (by norm_num)
theorem B1865861 : Blo 1242439 1865861 := bbase (se 4 (by rfl) ⟨174924, by rfl⟩ : syracuseStep 1865861 = 349849) (by norm_num)
theorem B6297749 : Blo 1242439 6297749 := bbase (se 6 (by rfl) ⟨147603, by rfl⟩ : syracuseStep 6297749 = 295207) (by norm_num)
theorem B1398937 : Blo 1242439 1398937 := bbase (se 2 (by rfl) ⟨524601, by rfl⟩ : syracuseStep 1398937 = 1049203) (by norm_num)
theorem B1865885 : Blo 1242439 1865885 := bbase (se 3 (by rfl) ⟨349853, by rfl⟩ : syracuseStep 1865885 = 699707) (by norm_num)
theorem B2799773 : Blo 1242439 2799773 := bbase (se 3 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 2799773 = 1049915) (by norm_num)
theorem B1865909 : Blo 1242439 1865909 := bbase (se 5 (by rfl) ⟨87464, by rfl⟩ : syracuseStep 1865909 = 174929) (by norm_num)
theorem B1398973 : Blo 1242439 1398973 := bbase (se 3 (by rfl) ⟨262307, by rfl⟩ : syracuseStep 1398973 = 524615) (by norm_num)
theorem B1865933 : Blo 1242439 1865933 := bbase (se 3 (by rfl) ⟨349862, by rfl⟩ : syracuseStep 1865933 = 699725) (by norm_num)
theorem B1399009 : Blo 1242439 1399009 := bbase (se 2 (by rfl) ⟨524628, by rfl⟩ : syracuseStep 1399009 = 1049257) (by norm_num)
theorem B1865957 : Blo 1242439 1865957 := bbase (se 4 (by rfl) ⟨174933, by rfl⟩ : syracuseStep 1865957 = 349867) (by norm_num)
theorem B2799845 : Blo 1242439 2799845 := bbase (se 4 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 2799845 = 524971) (by norm_num)
theorem B5314805 : Blo 1242439 5314805 := bbase (se 5 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 5314805 = 498263) (by norm_num)
theorem B1865981 : Blo 1242439 1865981 := bbase (se 3 (by rfl) ⟨349871, by rfl⟩ : syracuseStep 1865981 = 699743) (by norm_num)
theorem B1399045 : Blo 1242439 1399045 := bbase (se 4 (by rfl) ⟨131160, by rfl⟩ : syracuseStep 1399045 = 262321) (by norm_num)
theorem B1866005 : Blo 1242439 1866005 := bbase (se 6 (by rfl) ⟨43734, by rfl⟩ : syracuseStep 1866005 = 87469) (by norm_num)
theorem B1399081 : Blo 1242439 1399081 := bbase (se 2 (by rfl) ⟨524655, by rfl⟩ : syracuseStep 1399081 = 1049311) (by norm_num)
theorem B1866029 : Blo 1242439 1866029 := bbase (se 3 (by rfl) ⟨349880, by rfl⟩ : syracuseStep 1866029 = 699761) (by norm_num)
theorem B2799917 : Blo 1242439 2799917 := bbase (se 3 (by rfl) ⟨524984, by rfl⟩ : syracuseStep 2799917 = 1049969) (by norm_num)
theorem B1259837 : Blo 1242439 1259837 := bbase (se 3 (by rfl) ⟨236219, by rfl⟩ : syracuseStep 1259837 = 472439) (by norm_num)
theorem B1866053 : Blo 1242439 1866053 := bbase (se 4 (by rfl) ⟨174942, by rfl⟩ : syracuseStep 1866053 = 349885) (by norm_num)
theorem B1399117 : Blo 1242439 1399117 := bbase (se 3 (by rfl) ⟨262334, by rfl⟩ : syracuseStep 1399117 = 524669) (by norm_num)
theorem B1866077 : Blo 1242439 1866077 := bbase (se 3 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 1866077 = 699779) (by norm_num)
theorem B1399153 : Blo 1242439 1399153 := bbase (se 2 (by rfl) ⟨524682, by rfl⟩ : syracuseStep 1399153 = 1049365) (by norm_num)
theorem B1866101 : Blo 1242439 1866101 := bbase (se 5 (by rfl) ⟨87473, by rfl⟩ : syracuseStep 1866101 = 174947) (by norm_num)
theorem B2799989 : Blo 1242439 2799989 := bbase (se 5 (by rfl) ⟨131249, by rfl⟩ : syracuseStep 2799989 = 262499) (by norm_num)
theorem B1866125 : Blo 1242439 1866125 := bbase (se 3 (by rfl) ⟨349898, by rfl⟩ : syracuseStep 1866125 = 699797) (by norm_num)
theorem B1399189 : Blo 1242439 1399189 := bbase (se 6 (by rfl) ⟨32793, by rfl⟩ : syracuseStep 1399189 = 65587) (by norm_num)
theorem B1866149 : Blo 1242439 1866149 := bbase (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) (by norm_num)
theorem B1399225 : Blo 1242439 1399225 := bbase (se 2 (by rfl) ⟨524709, by rfl⟩ : syracuseStep 1399225 = 1049419) (by norm_num)
theorem B1866173 : Blo 1242439 1866173 := bbase (se 3 (by rfl) ⟨349907, by rfl⟩ : syracuseStep 1866173 = 699815) (by norm_num)
theorem B1513937 : Blo 1242439 1513937 := bbase (se 2 (by rfl) ⟨567726, by rfl⟩ : syracuseStep 1513937 = 1135453) (by norm_num)
theorem B7174613 : Blo 1242439 7174613 := bbase (se 7 (by rfl) ⟨84077, by rfl⟩ : syracuseStep 7174613 = 168155) (by norm_num)
theorem B1866197 : Blo 1242439 1866197 := bbase (se 7 (by rfl) ⟨21869, by rfl⟩ : syracuseStep 1866197 = 43739) (by norm_num)
theorem B1399261 : Blo 1242439 1399261 := bbase (se 3 (by rfl) ⟨262361, by rfl⟩ : syracuseStep 1399261 = 524723) (by norm_num)
theorem B1866221 : Blo 1242439 1866221 := bbase (se 3 (by rfl) ⟨349916, by rfl⟩ : syracuseStep 1866221 = 699833) (by norm_num)
theorem B1399297 : Blo 1242439 1399297 := bbase (se 2 (by rfl) ⟨524736, by rfl⟩ : syracuseStep 1399297 = 1049473) (by norm_num)
theorem B1866245 : Blo 1242439 1866245 := bbase (se 4 (by rfl) ⟨174960, by rfl⟩ : syracuseStep 1866245 = 349921) (by norm_num)
theorem B2521621 : Blo 1242439 2521621 := bbase (se 6 (by rfl) ⟨59100, by rfl⟩ : syracuseStep 2521621 = 118201) (by norm_num)
theorem B1866269 : Blo 1242439 1866269 := bbase (se 3 (by rfl) ⟨349925, by rfl⟩ : syracuseStep 1866269 = 699851) (by norm_num)
theorem B1399333 : Blo 1242439 1399333 := bbase (se 4 (by rfl) ⟨131187, by rfl⟩ : syracuseStep 1399333 = 262375) (by norm_num)
theorem B6289973 : Blo 1242439 6289973 := bbase (se 5 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 6289973 = 589685) (by norm_num)
theorem B1866293 : Blo 1242439 1866293 := bbase (se 5 (by rfl) ⟨87482, by rfl⟩ : syracuseStep 1866293 = 174965) (by norm_num)
theorem B1399369 : Blo 1242439 1399369 := bbase (se 2 (by rfl) ⟨524763, by rfl⟩ : syracuseStep 1399369 = 1049527) (by norm_num)
theorem B1866317 : Blo 1242439 1866317 := bbase (se 3 (by rfl) ⟨349934, by rfl⟩ : syracuseStep 1866317 = 699869) (by norm_num)
theorem B1866341 : Blo 1242439 1866341 := bbase (se 4 (by rfl) ⟨174969, by rfl⟩ : syracuseStep 1866341 = 349939) (by norm_num)
theorem B1399405 : Blo 1242439 1399405 := bbase (se 3 (by rfl) ⟨262388, by rfl⟩ : syracuseStep 1399405 = 524777) (by norm_num)
theorem B1866365 : Blo 1242439 1866365 := bbase (se 3 (by rfl) ⟨349943, by rfl⟩ : syracuseStep 1866365 = 699887) (by norm_num)
theorem B1399441 : Blo 1242439 1399441 := bbase (se 2 (by rfl) ⟨524790, by rfl⟩ : syracuseStep 1399441 = 1049581) (by norm_num)
theorem B1866389 : Blo 1242439 1866389 := bbase (se 6 (by rfl) ⟨43743, by rfl⟩ : syracuseStep 1866389 = 87487) (by norm_num)
theorem B1514137 : Blo 1242439 1514137 := bbase (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) (by norm_num)
theorem B1866413 : Blo 1242439 1866413 := bbase (se 3 (by rfl) ⟨349952, by rfl⟩ : syracuseStep 1866413 = 699905) (by norm_num)
theorem B12114613 : Blo 1242439 12114613 := bbase (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) (by norm_num)
theorem B1399477 : Blo 1242439 1399477 := bbase (se 5 (by rfl) ⟨65600, by rfl⟩ : syracuseStep 1399477 = 131201) (by norm_num)
theorem B2988733 : Blo 1242439 2988733 := bbase (se 3 (by rfl) ⟨560387, by rfl⟩ : syracuseStep 2988733 = 1120775) (by norm_num)
theorem B1866437 : Blo 1242439 1866437 := bbase (se 4 (by rfl) ⟨174978, by rfl⟩ : syracuseStep 1866437 = 349957) (by norm_num)
theorem B1399513 : Blo 1242439 1399513 := bbase (se 2 (by rfl) ⟨524817, by rfl⟩ : syracuseStep 1399513 = 1049635) (by norm_num)
theorem B1866461 : Blo 1242439 1866461 := bbase (se 3 (by rfl) ⟨349961, by rfl⟩ : syracuseStep 1866461 = 699923) (by norm_num)
theorem B1866485 : Blo 1242439 1866485 := bbase (se 5 (by rfl) ⟨87491, by rfl⟩ : syracuseStep 1866485 = 174983) (by norm_num)
theorem B1399549 : Blo 1242439 1399549 := bbase (se 3 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 1399549 = 524831) (by norm_num)
theorem B1702669 : Blo 1242439 1702669 := bbase (se 3 (by rfl) ⟨319250, by rfl⟩ : syracuseStep 1702669 = 638501) (by norm_num)
theorem B1866509 : Blo 1242439 1866509 := bbase (se 3 (by rfl) ⟨349970, by rfl⟩ : syracuseStep 1866509 = 699941) (by norm_num)
theorem B1399585 : Blo 1242439 1399585 := bbase (se 2 (by rfl) ⟨524844, by rfl⟩ : syracuseStep 1399585 = 1049689) (by norm_num)
theorem B1866533 : Blo 1242439 1866533 := bbase (se 4 (by rfl) ⟨174987, by rfl⟩ : syracuseStep 1866533 = 349975) (by norm_num)
theorem B1866557 : Blo 1242439 1866557 := bbase (se 3 (by rfl) ⟨349979, by rfl⟩ : syracuseStep 1866557 = 699959) (by norm_num)
theorem B1260353 : Blo 1242439 1260353 := bbase (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) (by norm_num)
theorem B1399621 : Blo 1242439 1399621 := bbase (se 4 (by rfl) ⟨131214, by rfl⟩ : syracuseStep 1399621 = 262429) (by norm_num)
theorem B1866581 : Blo 1242439 1866581 := bbase (se 9 (by rfl) ⟨5468, by rfl⟩ : syracuseStep 1866581 = 10937) (by norm_num)
theorem B1399657 : Blo 1242439 1399657 := bbase (se 2 (by rfl) ⟨524871, by rfl⟩ : syracuseStep 1399657 = 1049743) (by norm_num)
theorem B1866605 : Blo 1242439 1866605 := bbase (se 3 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 1866605 = 699977) (by norm_num)
theorem B1866629 : Blo 1242439 1866629 := bbase (se 4 (by rfl) ⟨174996, by rfl⟩ : syracuseStep 1866629 = 349993) (by norm_num)
theorem B1399693 : Blo 1242439 1399693 := bbase (se 3 (by rfl) ⟨262442, by rfl⟩ : syracuseStep 1399693 = 524885) (by norm_num)
theorem B1866653 : Blo 1242439 1866653 := bbase (se 3 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 1866653 = 699995) (by norm_num)
theorem B1399729 : Blo 1242439 1399729 := bbase (se 2 (by rfl) ⟨524898, by rfl⟩ : syracuseStep 1399729 = 1049797) (by norm_num)
theorem B1399765 : Blo 1242439 1399765 := bbase (se 7 (by rfl) ⟨16403, by rfl⟩ : syracuseStep 1399765 = 32807) (by norm_num)
theorem B4717541 : Blo 1242439 4717541 := bbase (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) (by norm_num)
theorem B1399801 : Blo 1242439 1399801 := bbase (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) (by norm_num)
theorem B3890197 : Blo 1242439 3890197 := bbase (se 6 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 3890197 = 182353) (by norm_num)
theorem B1399837 : Blo 1242439 1399837 := bbase (se 3 (by rfl) ⟨262469, by rfl⟩ : syracuseStep 1399837 = 524939) (by norm_num)
theorem B1596449 : Blo 1242439 1596449 := bbase (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) (by norm_num)
theorem B1399873 : Blo 1242439 1399873 := bbase (se 2 (by rfl) ⟨524952, by rfl⟩ : syracuseStep 1399873 = 1049905) (by norm_num)
theorem B9444437 : Blo 1242439 9444437 := bbase (se 8 (by rfl) ⟨55338, by rfl⟩ : syracuseStep 9444437 = 110677) (by norm_num)
theorem B1399909 : Blo 1242439 1399909 := bbase (se 4 (by rfl) ⟨131241, by rfl⟩ : syracuseStep 1399909 = 262483) (by norm_num)
theorem B1399945 : Blo 1242439 1399945 := bbase (se 2 (by rfl) ⟨524979, by rfl⟩ : syracuseStep 1399945 = 1049959) (by norm_num)
theorem B1399981 : Blo 1242439 1399981 := bbase (se 3 (by rfl) ⟨262496, by rfl⟩ : syracuseStep 1399981 = 524993) (by norm_num)
theorem B4193477 : Blo 1242439 4193477 := bbase (se 4 (by rfl) ⟨393138, by rfl⟩ : syracuseStep 4193477 = 786277) (by norm_num)
theorem B11943125 : Blo 1242439 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B25509077 : Blo 1242439 25509077 := bbase (se 7 (by rfl) ⟨298934, by rfl⟩ : syracuseStep 25509077 = 597869) (by norm_num)
theorem B7085333 : Blo 1242439 7085333 := bbase (se 6 (by rfl) ⟨166062, by rfl⟩ : syracuseStep 7085333 = 332125) (by norm_num)
theorem B2989349 : Blo 1242439 2989349 := bbase (se 4 (by rfl) ⟨280251, by rfl⟩ : syracuseStep 2989349 = 560503) (by norm_num)
theorem B3783989 : Blo 1242439 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B5307781 : Blo 1242439 5307781 := bbase (se 4 (by rfl) ⟨497604, by rfl⟩ : syracuseStep 5307781 = 995209) (by norm_num)
theorem B6299045 : Blo 1242439 6299045 := bbase (se 4 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 6299045 = 1181071) (by norm_num)
theorem B2358733 : Blo 1242439 2358733 := bbase (se 3 (by rfl) ⟨442262, by rfl⟩ : syracuseStep 2358733 = 884525) (by norm_num)
theorem B3145189 : Blo 1242439 3145189 := bbase (se 4 (by rfl) ⟨294861, by rfl⟩ : syracuseStep 3145189 = 589723) (by norm_num)
theorem B9436661 : Blo 1242439 9436661 := bbase (se 5 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 9436661 = 884687) (by norm_num)
theorem B2096725 : Blo 1242439 2096725 := bbase (se 8 (by rfl) ⟨12285, by rfl⟩ : syracuseStep 2096725 = 24571) (by norm_num)
theorem B3145301 : Blo 1242439 3145301 := bbase (se 8 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 3145301 = 36859) (by norm_num)
theorem B2358877 : Blo 1242439 2358877 := bbase (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) (by norm_num)
theorem B4193909 : Blo 1242439 4193909 := bbase (se 5 (by rfl) ⟨196589, by rfl⟩ : syracuseStep 4193909 = 393179) (by norm_num)
theorem B1572473 : Blo 1242439 1572473 := bbase (se 2 (by rfl) ⟨589677, by rfl⟩ : syracuseStep 1572473 = 1179355) (by norm_num)
theorem B1793701 : Blo 1242439 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B2096813 : Blo 1242439 2096813 := bbase (se 3 (by rfl) ⟨393152, by rfl⟩ : syracuseStep 2096813 = 786305) (by norm_num)
theorem B1572529 : Blo 1242439 1572529 := bbase (se 2 (by rfl) ⟨589698, by rfl⟩ : syracuseStep 1572529 = 1179397) (by norm_num)
theorem B1769141 : Blo 1242439 1769141 := bbase (se 5 (by rfl) ⟨82928, by rfl⟩ : syracuseStep 1769141 = 165857) (by norm_num)
theorem B1261297 : Blo 1242439 1261297 := bbase (se 2 (by rfl) ⟨472986, by rfl⟩ : syracuseStep 1261297 = 945973) (by norm_num)
theorem B2359037 : Blo 1242439 2359037 := bbase (se 3 (by rfl) ⟨442319, by rfl⟩ : syracuseStep 2359037 = 884639) (by norm_num)
theorem B1572625 : Blo 1242439 1572625 := bbase (se 2 (by rfl) ⟨589734, by rfl⟩ : syracuseStep 1572625 = 1179469) (by norm_num)
theorem B3145493 : Blo 1242439 3145493 := bbase (se 6 (by rfl) ⟨73722, by rfl⟩ : syracuseStep 3145493 = 147445) (by norm_num)
theorem B4480805 : Blo 1242439 4480805 := bbase (se 4 (by rfl) ⟨420075, by rfl⟩ : syracuseStep 4480805 = 840151) (by norm_num)
theorem B2096941 : Blo 1242439 2096941 := bbase (se 3 (by rfl) ⟨393176, by rfl⟩ : syracuseStep 2096941 = 786353) (by norm_num)
theorem B6291269 : Blo 1242439 6291269 := bbase (se 4 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 6291269 = 1179613) (by norm_num)
theorem B1679189 : Blo 1242439 1679189 := bbase (se 9 (by rfl) ⟨4919, by rfl⟩ : syracuseStep 1679189 = 9839) (by norm_num)
theorem B1326937 : Blo 1242439 1326937 := bbase (se 2 (by rfl) ⟨497601, by rfl⟩ : syracuseStep 1326937 = 995203) (by norm_num)
theorem B2097029 : Blo 1242439 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B2359181 : Blo 1242439 2359181 := bbase (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) (by norm_num)
theorem B3981221 : Blo 1242439 3981221 := bbase (se 4 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 3981221 = 746479) (by norm_num)
theorem B1572797 : Blo 1242439 1572797 := bbase (se 3 (by rfl) ⟨294899, by rfl⟩ : syracuseStep 1572797 = 589799) (by norm_num)
theorem B3538885 : Blo 1242439 3538885 := bbase (se 4 (by rfl) ⟨331770, by rfl⟩ : syracuseStep 3538885 = 663541) (by norm_num)
theorem B1327061 : Blo 1242439 1327061 := bbase (se 7 (by rfl) ⟨15551, by rfl⟩ : syracuseStep 1327061 = 31103) (by norm_num)
theorem B1572853 : Blo 1242439 1572853 := bbase (se 5 (by rfl) ⟨73727, by rfl⟩ : syracuseStep 1572853 = 147455) (by norm_num)
theorem B3539011 : Blo 1242439 3539011 := bstep (se 1 (by rfl) ⟨2654258, by rfl⟩ : syracuseStep 3539011 = 5308517) B5308517
theorem B2359363 : Blo 1242439 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B11952197 : Blo 1242439 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2097265 : Blo 1242439 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1794161 : Blo 1242439 1794161 := bstep (se 2 (by rfl) ⟨672810, by rfl⟩ : syracuseStep 1794161 = 1345621) B1345621
theorem B4194449 : Blo 1242439 4194449 := bstep (se 2 (by rfl) ⟨1572918, by rfl⟩ : syracuseStep 4194449 = 3145837) B3145837
theorem B2097299 : Blo 1242439 2097299 := bstep (se 1 (by rfl) ⟨1572974, by rfl⟩ : syracuseStep 2097299 = 3145949) B3145949
theorem B2359523 : Blo 1242439 2359523 := bstep (se 1 (by rfl) ⟨1769642, by rfl⟩ : syracuseStep 2359523 = 3539285) B3539285
theorem B2097427 : Blo 1242439 2097427 := bstep (se 1 (by rfl) ⟨1573070, by rfl⟩ : syracuseStep 2097427 = 3146141) B3146141
theorem B1769779 : Blo 1242439 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B8962417 : Blo 1242439 8962417 := bstep (se 2 (by rfl) ⟨3360906, by rfl⟩ : syracuseStep 8962417 = 6721813) B6721813
theorem B1327475 : Blo 1242439 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B7971205 : Blo 1242439 7971205 := bstep (se 4 (by rfl) ⟨747300, by rfl⟩ : syracuseStep 7971205 = 1494601) B1494601
theorem B2097569 : Blo 1242439 2097569 := bstep (se 2 (by rfl) ⟨786588, by rfl⟩ : syracuseStep 2097569 = 1573177) B1573177
theorem B1573283 : Blo 1242439 1573283 := bstep (se 1 (by rfl) ⟨1179962, by rfl⟩ : syracuseStep 1573283 = 2359925) B2359925
theorem B3146161 : Blo 1242439 3146161 := bstep (se 2 (by rfl) ⟨1179810, by rfl⟩ : syracuseStep 3146161 = 2359621) B2359621
theorem B6291917 : Blo 1242439 6291917 := bstep (se 3 (by rfl) ⟨1179734, by rfl⟩ : syracuseStep 6291917 = 2359469) B2359469
theorem B6717923 : Blo 1242439 6717923 := bstep (se 1 (by rfl) ⟨5038442, by rfl⟩ : syracuseStep 6717923 = 10076885) B10076885
theorem B2556419 : Blo 1242439 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B2097697 : Blo 1242439 2097697 := bstep (se 2 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 2097697 = 1573273) B1573273
theorem B3539501 : Blo 1242439 3539501 := bstep (se 3 (by rfl) ⟨663656, by rfl⟩ : syracuseStep 3539501 = 1327313) B1327313
theorem B17932853 : Blo 1242439 17932853 := bstep (se 5 (by rfl) ⟨840602, by rfl⟩ : syracuseStep 17932853 = 1681205) B1681205
theorem B2097731 : Blo 1242439 2097731 := bstep (se 1 (by rfl) ⟨1573298, by rfl⟩ : syracuseStep 2097731 = 3146597) B3146597
theorem B4719181 : Blo 1242439 4719181 := bstep (se 3 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 4719181 = 1769693) B1769693
theorem B7078499 : Blo 1242439 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B1770115 : Blo 1242439 1770115 := bstep (se 1 (by rfl) ⟨1327586, by rfl⟩ : syracuseStep 1770115 = 2655173) B2655173
theorem B1991315 : Blo 1242439 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B6816419 : Blo 1242439 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B4194989 : Blo 1242439 4194989 := bstep (se 3 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 4194989 = 1573121) B1573121
theorem B3146435 : Blo 1242439 3146435 := bstep (se 1 (by rfl) ⟨2359826, by rfl⟩ : syracuseStep 3146435 = 4719653) B4719653
theorem B2097859 : Blo 1242439 2097859 := bstep (se 1 (by rfl) ⟨1573394, by rfl⟩ : syracuseStep 2097859 = 3146789) B3146789
theorem B4195043 : Blo 1242439 4195043 := bstep (se 1 (by rfl) ⟨3146282, by rfl⟩ : syracuseStep 4195043 = 6292565) B6292565
theorem B2655011 : Blo 1242439 2655011 := bstep (se 1 (by rfl) ⟨1991258, by rfl⟩ : syracuseStep 2655011 = 3982517) B3982517
theorem B2098001 : Blo 1242439 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B3146627 : Blo 1242439 3146627 := bstep (se 1 (by rfl) ⟨2359970, by rfl⟩ : syracuseStep 3146627 = 4719941) B4719941
theorem B2655121 : Blo 1242439 2655121 := bstep (se 2 (by rfl) ⟨995670, by rfl⟩ : syracuseStep 2655121 = 1991341) B1991341
theorem B2098129 : Blo 1242439 2098129 := bstep (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) B1573597
theorem B4195313 : Blo 1242439 4195313 := bstep (se 2 (by rfl) ⟨1573242, by rfl⟩ : syracuseStep 4195313 = 3146485) B3146485
theorem B2098163 : Blo 1242439 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B2270225 : Blo 1242439 2270225 := bstep (se 2 (by rfl) ⟨851334, by rfl⟩ : syracuseStep 2270225 = 1702669) B1702669
theorem B5309489 : Blo 1242439 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B2589763 : Blo 1242439 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B1573987 : Blo 1242439 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B2098291 : Blo 1242439 2098291 := bstep (se 1 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 2098291 = 3147437) B3147437
theorem B1770673 : Blo 1242439 1770673 := bstep (se 2 (by rfl) ⟨664002, by rfl⟩ : syracuseStep 1770673 = 1328005) B1328005
theorem B1574083 : Blo 1242439 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B1770707 : Blo 1242439 1770707 := bstep (se 1 (by rfl) ⟨1328030, by rfl⟩ : syracuseStep 1770707 = 2656061) B2656061
theorem B1418467 : Blo 1242439 1418467 := bstep (se 1 (by rfl) ⟨1063850, by rfl⟩ : syracuseStep 1418467 = 2127701) B2127701
theorem B2098433 : Blo 1242439 2098433 := bstep (se 2 (by rfl) ⟨786912, by rfl⟩ : syracuseStep 2098433 = 1573825) B1573825
theorem B2360593 : Blo 1242439 2360593 := bstep (se 2 (by rfl) ⟨885222, by rfl⟩ : syracuseStep 2360593 = 1770445) B1770445
theorem B8504675 : Blo 1242439 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B4719971 : Blo 1242439 4719971 := bstep (se 1 (by rfl) ⟨3539978, by rfl⟩ : syracuseStep 4719971 = 7079957) B7079957
theorem B5186929 : Blo 1242439 5186929 := bstep (se 2 (by rfl) ⟨1945098, by rfl⟩ : syracuseStep 5186929 = 3890197) B3890197
theorem B2098561 : Blo 1242439 2098561 := bstep (se 2 (by rfl) ⟨786960, by rfl⟩ : syracuseStep 2098561 = 1573921) B1573921
theorem B9438605 : Blo 1242439 9438605 := bstep (se 3 (by rfl) ⟨1769738, by rfl⟩ : syracuseStep 9438605 = 3539477) B3539477
theorem B3982733 : Blo 1242439 3982733 := bstep (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) B1493525
theorem B2098595 : Blo 1242439 2098595 := bstep (se 1 (by rfl) ⟨1573946, by rfl⟩ : syracuseStep 2098595 = 3147893) B3147893
theorem B1992161 : Blo 1242439 1992161 := bstep (se 2 (by rfl) ⟨747060, by rfl⟩ : syracuseStep 1992161 = 1494121) B1494121
theorem B4195853 : Blo 1242439 4195853 := bstep (se 3 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 4195853 = 1573445) B1573445
theorem B3982861 : Blo 1242439 3982861 := bstep (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) B1493573
theorem B2098723 : Blo 1242439 2098723 := bstep (se 1 (by rfl) ⟨1574042, by rfl⟩ : syracuseStep 2098723 = 3148085) B3148085
theorem B4195907 : Blo 1242439 4195907 := bstep (se 1 (by rfl) ⟨3146930, by rfl⟩ : syracuseStep 4195907 = 6293861) B6293861
theorem B7079501 : Blo 1242439 7079501 := bstep (se 3 (by rfl) ⟨1327406, by rfl⟩ : syracuseStep 7079501 = 2654813) B2654813
theorem B2098865 : Blo 1242439 2098865 := bstep (se 2 (by rfl) ⟨787074, by rfl⟩ : syracuseStep 2098865 = 1574149) B1574149
theorem B1574579 : Blo 1242439 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B5310157 : Blo 1242439 5310157 := bstep (se 3 (by rfl) ⟨995654, by rfl⟩ : syracuseStep 5310157 = 1991309) B1991309
theorem B3540685 : Blo 1242439 3540685 := bstep (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) B1327757
theorem B1771265 : Blo 1242439 1771265 := bstep (se 2 (by rfl) ⟨664224, by rfl⟩ : syracuseStep 1771265 = 1328449) B1328449
theorem B3147569 : Blo 1242439 3147569 := bstep (se 2 (by rfl) ⟨1180338, by rfl⟩ : syracuseStep 3147569 = 2360677) B2360677
theorem B2098993 : Blo 1242439 2098993 := bstep (se 2 (by rfl) ⟨787122, by rfl⟩ : syracuseStep 2098993 = 1574245) B1574245
theorem B4196177 : Blo 1242439 4196177 := bstep (se 2 (by rfl) ⟨1573566, by rfl⟩ : syracuseStep 4196177 = 3147133) B3147133
theorem B1771345 : Blo 1242439 1771345 := bstep (se 2 (by rfl) ⟨664254, by rfl⟩ : syracuseStep 1771345 = 1328509) B1328509
theorem B2099027 : Blo 1242439 2099027 := bstep (se 1 (by rfl) ⟨1574270, by rfl⟩ : syracuseStep 2099027 = 3148541) B3148541
theorem B3147619 : Blo 1242439 3147619 := bstep (se 1 (by rfl) ⟨2360714, by rfl⟩ : syracuseStep 3147619 = 4721429) B4721429
theorem B1492867 : Blo 1242439 1492867 := bstep (se 1 (by rfl) ⟨1119650, by rfl⟩ : syracuseStep 1492867 = 2239301) B2239301
theorem B2099155 : Blo 1242439 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B4720625 : Blo 1242439 4720625 := bstep (se 2 (by rfl) ⟨1770234, by rfl⟩ : syracuseStep 4720625 = 3540469) B3540469
theorem B3147761 : Blo 1242439 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B2099297 : Blo 1242439 2099297 := bstep (se 2 (by rfl) ⟨787236, by rfl⟩ : syracuseStep 2099297 = 1574473) B1574473
theorem B2795633 : Blo 1242439 2795633 := bstep (se 2 (by rfl) ⟨1048362, by rfl⟩ : syracuseStep 2795633 = 2096725) B2096725
theorem B21006449 : Blo 1242439 21006449 := bstep (se 2 (by rfl) ⟨7877418, by rfl⟩ : syracuseStep 21006449 = 15754837) B15754837
theorem B2795651 : Blo 1242439 2795651 := bstep (se 1 (by rfl) ⟨2096738, by rfl⟩ : syracuseStep 2795651 = 4193477) B4193477
theorem B3360941 : Blo 1242439 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B1992899 : Blo 1242439 1992899 := bstep (se 1 (by rfl) ⟨1494674, by rfl⟩ : syracuseStep 1992899 = 2989349) B2989349
theorem B2099425 : Blo 1242439 2099425 := bstep (se 2 (by rfl) ⟨787284, by rfl⟩ : syracuseStep 2099425 = 1574569) B1574569
theorem B3361027 : Blo 1242439 3361027 := bstep (se 1 (by rfl) ⟨2520770, by rfl⟩ : syracuseStep 3361027 = 5041541) B5041541
theorem B2099459 : Blo 1242439 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B5310755 : Blo 1242439 5310755 := bstep (se 1 (by rfl) ⟨3983066, by rfl⟩ : syracuseStep 5310755 = 7966133) B7966133
theorem B7670051 : Blo 1242439 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B2361649 : Blo 1242439 2361649 := bstep (se 2 (by rfl) ⟨885618, by rfl⟩ : syracuseStep 2361649 = 1771237) B1771237
theorem B1681729 : Blo 1242439 1681729 := bstep (se 2 (by rfl) ⟨630648, by rfl⟩ : syracuseStep 1681729 = 1261297) B1261297
theorem B3361123 : Blo 1242439 3361123 := bstep (se 1 (by rfl) ⟨2520842, by rfl⟩ : syracuseStep 3361123 = 5041685) B5041685
theorem B4196717 : Blo 1242439 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B2099587 : Blo 1242439 2099587 := bstep (se 1 (by rfl) ⟨1574690, by rfl⟩ : syracuseStep 2099587 = 3149381) B3149381
theorem B2795921 : Blo 1242439 2795921 := bstep (se 2 (by rfl) ⟨1048470, by rfl⟩ : syracuseStep 2795921 = 2096941) B2096941
theorem B2795939 : Blo 1242439 2795939 := bstep (se 1 (by rfl) ⟨2096954, by rfl⟩ : syracuseStep 2795939 = 4193909) B4193909
theorem B4196771 : Blo 1242439 4196771 := bstep (se 1 (by rfl) ⟨3147578, by rfl⟩ : syracuseStep 4196771 = 6295157) B6295157
theorem B3361297 : Blo 1242439 3361297 := bstep (se 2 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 3361297 = 2520973) B2520973
theorem B2099729 : Blo 1242439 2099729 := bstep (se 2 (by rfl) ⟨787398, by rfl⟩ : syracuseStep 2099729 = 1574797) B1574797
theorem B2099857 : Blo 1242439 2099857 := bstep (se 2 (by rfl) ⟨787446, by rfl⟩ : syracuseStep 2099857 = 1574893) B1574893
theorem B2796209 : Blo 1242439 2796209 := bstep (se 2 (by rfl) ⟨1048578, by rfl⟩ : syracuseStep 2796209 = 2097157) B2097157
theorem B4197041 : Blo 1242439 4197041 := bstep (se 2 (by rfl) ⟨1573890, by rfl⟩ : syracuseStep 4197041 = 3147781) B3147781
theorem B2099891 : Blo 1242439 2099891 := bstep (se 1 (by rfl) ⟨1574918, by rfl⟩ : syracuseStep 2099891 = 3149837) B3149837
theorem B2796227 : Blo 1242439 2796227 := bstep (se 1 (by rfl) ⟨2097170, by rfl⟩ : syracuseStep 2796227 = 4194341) B4194341
theorem B2362051 : Blo 1242439 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B3541745 : Blo 1242439 3541745 := bstep (se 2 (by rfl) ⟨1328154, by rfl⟩ : syracuseStep 3541745 = 2656309) B2656309
theorem B2362097 : Blo 1242439 2362097 := bstep (se 2 (by rfl) ⟨885786, by rfl⟩ : syracuseStep 2362097 = 1771573) B1771573
theorem B2239249 : Blo 1242439 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B15928163 : Blo 1242439 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B2657137 : Blo 1242439 2657137 := bstep (se 2 (by rfl) ⟨996426, by rfl⟩ : syracuseStep 2657137 = 1992853) B1992853
theorem B2796497 : Blo 1242439 2796497 := bstep (se 2 (by rfl) ⟨1048686, by rfl⟩ : syracuseStep 2796497 = 2097373) B2097373
theorem B3148753 : Blo 1242439 3148753 := bstep (se 2 (by rfl) ⟨1180782, by rfl⟩ : syracuseStep 3148753 = 2361565) B2361565
theorem B2796515 : Blo 1242439 2796515 := bstep (se 1 (by rfl) ⟨2097386, by rfl⟩ : syracuseStep 2796515 = 4194773) B4194773
theorem B2362385 : Blo 1242439 2362385 := bstep (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) B1771789
theorem B7965773 : Blo 1242439 7965773 := bstep (se 3 (by rfl) ⟨1493582, by rfl⟩ : syracuseStep 7965773 = 2987165) B2987165
theorem B10087523 : Blo 1242439 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B4197581 : Blo 1242439 4197581 := bstep (se 3 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 4197581 = 1574093) B1574093
theorem B3591373 : Blo 1242439 3591373 := bstep (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) B1346765
theorem B3149027 : Blo 1242439 3149027 := bstep (se 1 (by rfl) ⟨2361770, by rfl⟩ : syracuseStep 3149027 = 4723541) B4723541
theorem B2796785 : Blo 1242439 2796785 := bstep (se 2 (by rfl) ⟨1048794, by rfl⟩ : syracuseStep 2796785 = 2097589) B2097589
theorem B2796803 : Blo 1242439 2796803 := bstep (se 1 (by rfl) ⟨2097602, by rfl⟩ : syracuseStep 2796803 = 4195205) B4195205
theorem B4197635 : Blo 1242439 4197635 := bstep (se 1 (by rfl) ⟨3148226, by rfl⟩ : syracuseStep 4197635 = 6296453) B6296453
theorem B2657539 : Blo 1242439 2657539 := bstep (se 1 (by rfl) ⟨1993154, by rfl⟩ : syracuseStep 2657539 = 3986309) B3986309
theorem B6294833 : Blo 1242439 6294833 := bstep (se 2 (by rfl) ⟨2360562, by rfl⟩ : syracuseStep 6294833 = 4721125) B4721125
theorem B13438261 : Blo 1242439 13438261 := bstep (se 5 (by rfl) ⟨629918, by rfl⟩ : syracuseStep 13438261 = 1259837) B1259837
theorem B3984707 : Blo 1242439 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B3362161 : Blo 1242439 3362161 := bstep (se 2 (by rfl) ⟨1260810, by rfl⟩ : syracuseStep 3362161 = 2521621) B2521621
theorem B3542417 : Blo 1242439 3542417 := bstep (se 2 (by rfl) ⟨1328406, by rfl⟩ : syracuseStep 3542417 = 2656813) B2656813
theorem B4722083 : Blo 1242439 4722083 := bstep (se 1 (by rfl) ⟨3541562, by rfl⟩ : syracuseStep 4722083 = 7083125) B7083125
theorem B3149219 : Blo 1242439 3149219 := bstep (se 1 (by rfl) ⟨2361914, by rfl⟩ : syracuseStep 3149219 = 4723829) B4723829
theorem B4722097 : Blo 1242439 4722097 := bstep (se 2 (by rfl) ⟨1770786, by rfl⟩ : syracuseStep 4722097 = 3541573) B3541573
theorem B3984835 : Blo 1242439 3984835 := bstep (se 1 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 3984835 = 5977253) B5977253
theorem B17018309 : Blo 1242439 17018309 := bstep (se 4 (by rfl) ⟨1595466, by rfl⟩ : syracuseStep 17018309 = 3190933) B3190933
theorem B2018771 : Blo 1242439 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B2797073 : Blo 1242439 2797073 := bstep (se 2 (by rfl) ⟨1048902, by rfl⟩ : syracuseStep 2797073 = 2097805) B2097805
theorem B4197905 : Blo 1242439 4197905 := bstep (se 2 (by rfl) ⟨1574214, by rfl⟩ : syracuseStep 4197905 = 3148429) B3148429
theorem B2018849 : Blo 1242439 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B2797091 : Blo 1242439 2797091 := bstep (se 1 (by rfl) ⟨2097818, by rfl⟩ : syracuseStep 2797091 = 4195637) B4195637
theorem B3984977 : Blo 1242439 3984977 := bstep (se 2 (by rfl) ⟨1494366, by rfl⟩ : syracuseStep 3984977 = 2988733) B2988733
theorem B1494659 : Blo 1242439 1494659 := bstep (se 1 (by rfl) ⟨1120994, by rfl⟩ : syracuseStep 1494659 = 2241989) B2241989
theorem B3985091 : Blo 1242439 3985091 := bstep (se 1 (by rfl) ⟨2988818, by rfl⟩ : syracuseStep 3985091 = 5977637) B5977637
theorem B5746403 : Blo 1242439 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B4484899 : Blo 1242439 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B2797361 : Blo 1242439 2797361 := bstep (se 2 (by rfl) ⟨1049010, by rfl⟩ : syracuseStep 2797361 = 2098021) B2098021
theorem B2797379 : Blo 1242439 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B2518897 : Blo 1242439 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B19132301 : Blo 1242439 19132301 := bstep (se 3 (by rfl) ⟨3587306, by rfl⟩ : syracuseStep 19132301 = 7174613) B7174613
theorem B1863665 : Blo 1242439 1863665 := bstep (se 2 (by rfl) ⟨698874, by rfl⟩ : syracuseStep 1863665 = 1397749) B1397749
theorem B1863683 : Blo 1242439 1863683 := bstep (se 1 (by rfl) ⟨1397762, by rfl⟩ : syracuseStep 1863683 = 2795525) B2795525
theorem B1863713 : Blo 1242439 1863713 := bstep (se 2 (by rfl) ⟨698892, by rfl⟩ : syracuseStep 1863713 = 1397785) B1397785
theorem B4198445 : Blo 1242439 4198445 := bstep (se 3 (by rfl) ⟨787208, by rfl⟩ : syracuseStep 4198445 = 1574417) B1574417
theorem B1863731 : Blo 1242439 1863731 := bstep (se 1 (by rfl) ⟨1397798, by rfl⟩ : syracuseStep 1863731 = 2795597) B2795597
theorem B1863761 : Blo 1242439 1863761 := bstep (se 2 (by rfl) ⟨698910, by rfl⟩ : syracuseStep 1863761 = 1397821) B1397821
theorem B2797649 : Blo 1242439 2797649 := bstep (se 2 (by rfl) ⟨1049118, by rfl⟩ : syracuseStep 2797649 = 2098237) B2098237
theorem B1863779 : Blo 1242439 1863779 := bstep (se 1 (by rfl) ⟨1397834, by rfl⟩ : syracuseStep 1863779 = 2795669) B2795669
theorem B2797667 : Blo 1242439 2797667 := bstep (se 1 (by rfl) ⟨2098250, by rfl⟩ : syracuseStep 2797667 = 4196501) B4196501
theorem B4198499 : Blo 1242439 4198499 := bstep (se 1 (by rfl) ⟨3148874, by rfl⟩ : syracuseStep 4198499 = 6297749) B6297749
theorem B1863809 : Blo 1242439 1863809 := bstep (se 2 (by rfl) ⟨698928, by rfl⟩ : syracuseStep 1863809 = 1397857) B1397857
theorem B18157709 : Blo 1242439 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B1863827 : Blo 1242439 1863827 := bstep (se 1 (by rfl) ⟨1397870, by rfl⟩ : syracuseStep 1863827 = 2795741) B2795741
theorem B3543203 : Blo 1242439 3543203 := bstep (se 1 (by rfl) ⟨2657402, by rfl⟩ : syracuseStep 3543203 = 5314805) B5314805
theorem B1863857 : Blo 1242439 1863857 := bstep (se 2 (by rfl) ⟨698946, by rfl⟩ : syracuseStep 1863857 = 1397893) B1397893
theorem B1863875 : Blo 1242439 1863875 := bstep (se 1 (by rfl) ⟨1397906, by rfl⟩ : syracuseStep 1863875 = 2795813) B2795813
theorem B1863905 : Blo 1242439 1863905 := bstep (se 2 (by rfl) ⟨698964, by rfl⟩ : syracuseStep 1863905 = 1397929) B1397929
theorem B9441521 : Blo 1242439 9441521 := bstep (se 2 (by rfl) ⟨3540570, by rfl⟩ : syracuseStep 9441521 = 7081141) B7081141
theorem B1863923 : Blo 1242439 1863923 := bstep (se 1 (by rfl) ⟨1397942, by rfl⟩ : syracuseStep 1863923 = 2795885) B2795885
theorem B1863953 : Blo 1242439 1863953 := bstep (se 2 (by rfl) ⟨698982, by rfl⟩ : syracuseStep 1863953 = 1397965) B1397965
theorem B35836181 : Blo 1242439 35836181 := bstep (se 6 (by rfl) ⟨839910, by rfl⟩ : syracuseStep 35836181 = 1679821) B1679821
theorem B1863971 : Blo 1242439 1863971 := bstep (se 1 (by rfl) ⟨1397978, by rfl⟩ : syracuseStep 1863971 = 2795957) B2795957
theorem B1864001 : Blo 1242439 1864001 := bstep (se 2 (by rfl) ⟨699000, by rfl⟩ : syracuseStep 1864001 = 1398001) B1398001
theorem B7278917 : Blo 1242439 7278917 := bstep (se 4 (by rfl) ⟨682398, by rfl⟩ : syracuseStep 7278917 = 1364797) B1364797
theorem B1864019 : Blo 1242439 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B1864049 : Blo 1242439 1864049 := bstep (se 2 (by rfl) ⟨699018, by rfl⟩ : syracuseStep 1864049 = 1398037) B1398037
theorem B2797937 : Blo 1242439 2797937 := bstep (se 2 (by rfl) ⟨1049226, by rfl⟩ : syracuseStep 2797937 = 2098453) B2098453
theorem B4198769 : Blo 1242439 4198769 := bstep (se 2 (by rfl) ⟨1574538, by rfl⟩ : syracuseStep 4198769 = 3149077) B3149077
theorem B1864067 : Blo 1242439 1864067 := bstep (se 1 (by rfl) ⟨1398050, by rfl⟩ : syracuseStep 1864067 = 2796101) B2796101
theorem B2797955 : Blo 1242439 2797955 := bstep (se 1 (by rfl) ⟨2098466, by rfl⟩ : syracuseStep 2797955 = 4196933) B4196933
theorem B1864097 : Blo 1242439 1864097 := bstep (se 2 (by rfl) ⟨699036, by rfl⟩ : syracuseStep 1864097 = 1398073) B1398073
theorem B7082417 : Blo 1242439 7082417 := bstep (se 2 (by rfl) ⟨2655906, by rfl⟩ : syracuseStep 7082417 = 5311813) B5311813
theorem B1864115 : Blo 1242439 1864115 := bstep (se 1 (by rfl) ⟨1398086, by rfl⟩ : syracuseStep 1864115 = 2796173) B2796173
theorem B15135173 : Blo 1242439 15135173 := bstep (se 4 (by rfl) ⟨1418922, by rfl⟩ : syracuseStep 15135173 = 2837845) B2837845
theorem B1864145 : Blo 1242439 1864145 := bstep (se 2 (by rfl) ⟨699054, by rfl⟩ : syracuseStep 1864145 = 1398109) B1398109
theorem B1864163 : Blo 1242439 1864163 := bstep (se 1 (by rfl) ⟨1398122, by rfl⟩ : syracuseStep 1864163 = 2796245) B2796245
theorem B3543533 : Blo 1242439 3543533 := bstep (se 3 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 3543533 = 1328825) B1328825
theorem B1864193 : Blo 1242439 1864193 := bstep (se 2 (by rfl) ⟨699072, by rfl⟩ : syracuseStep 1864193 = 1398145) B1398145
theorem B5673485 : Blo 1242439 5673485 := bstep (se 3 (by rfl) ⟨1063778, by rfl⟩ : syracuseStep 5673485 = 2127557) B2127557
theorem B1864211 : Blo 1242439 1864211 := bstep (se 1 (by rfl) ⟨1398158, by rfl⟩ : syracuseStep 1864211 = 2796317) B2796317
theorem B1864241 : Blo 1242439 1864241 := bstep (se 2 (by rfl) ⟨699090, by rfl⟩ : syracuseStep 1864241 = 1398181) B1398181
theorem B3543601 : Blo 1242439 3543601 := bstep (se 2 (by rfl) ⟨1328850, by rfl⟩ : syracuseStep 3543601 = 2657701) B2657701
theorem B1864259 : Blo 1242439 1864259 := bstep (se 1 (by rfl) ⟨1398194, by rfl⟩ : syracuseStep 1864259 = 2796389) B2796389
theorem B1864289 : Blo 1242439 1864289 := bstep (se 2 (by rfl) ⟨699108, by rfl⟩ : syracuseStep 1864289 = 1398217) B1398217
theorem B13628017 : Blo 1242439 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B1864307 : Blo 1242439 1864307 := bstep (se 1 (by rfl) ⟨1398230, by rfl⟩ : syracuseStep 1864307 = 2796461) B2796461
theorem B1864337 : Blo 1242439 1864337 := bstep (se 2 (by rfl) ⟨699126, by rfl⟩ : syracuseStep 1864337 = 1398253) B1398253
theorem B2798225 : Blo 1242439 2798225 := bstep (se 2 (by rfl) ⟨1049334, by rfl⟩ : syracuseStep 2798225 = 2098669) B2098669
theorem B1864355 : Blo 1242439 1864355 := bstep (se 1 (by rfl) ⟨1398266, by rfl⟩ : syracuseStep 1864355 = 2796533) B2796533
theorem B2798243 : Blo 1242439 2798243 := bstep (se 1 (by rfl) ⟨2098682, by rfl⟩ : syracuseStep 2798243 = 4197365) B4197365
theorem B1864385 : Blo 1242439 1864385 := bstep (se 2 (by rfl) ⟨699144, by rfl⟩ : syracuseStep 1864385 = 1398289) B1398289
theorem B1864403 : Blo 1242439 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B6296291 : Blo 1242439 6296291 := bstep (se 1 (by rfl) ⟨4722218, by rfl⟩ : syracuseStep 6296291 = 9444437) B9444437
theorem B1864433 : Blo 1242439 1864433 := bstep (se 2 (by rfl) ⟨699162, by rfl⟩ : syracuseStep 1864433 = 1398325) B1398325
theorem B1864451 : Blo 1242439 1864451 := bstep (se 1 (by rfl) ⟨1398338, by rfl⟩ : syracuseStep 1864451 = 2796677) B2796677
theorem B2241283 : Blo 1242439 2241283 := bstep (se 1 (by rfl) ⟨1680962, by rfl⟩ : syracuseStep 2241283 = 3361925) B3361925
theorem B1864481 : Blo 1242439 1864481 := bstep (se 2 (by rfl) ⟨699180, by rfl⟩ : syracuseStep 1864481 = 1398361) B1398361
theorem B1864499 : Blo 1242439 1864499 := bstep (se 1 (by rfl) ⟨1398374, by rfl⟩ : syracuseStep 1864499 = 2796749) B2796749
theorem B1864529 : Blo 1242439 1864529 := bstep (se 2 (by rfl) ⟨699198, by rfl⟩ : syracuseStep 1864529 = 1398397) B1398397
theorem B1864547 : Blo 1242439 1864547 := bstep (se 1 (by rfl) ⟨1398410, by rfl⟩ : syracuseStep 1864547 = 2796821) B2796821
theorem B4723555 : Blo 1242439 4723555 := bstep (se 1 (by rfl) ⟨3542666, by rfl⟩ : syracuseStep 4723555 = 7085333) B7085333
theorem B1864577 : Blo 1242439 1864577 := bstep (se 2 (by rfl) ⟨699216, by rfl⟩ : syracuseStep 1864577 = 1398433) B1398433
theorem B4477837 : Blo 1242439 4477837 := bstep (se 3 (by rfl) ⟨839594, by rfl⟩ : syracuseStep 4477837 = 1679189) B1679189
theorem B4199309 : Blo 1242439 4199309 := bstep (se 3 (by rfl) ⟨787370, by rfl⟩ : syracuseStep 4199309 = 1574741) B1574741
theorem B1864595 : Blo 1242439 1864595 := bstep (se 1 (by rfl) ⟨1398446, by rfl⟩ : syracuseStep 1864595 = 2796893) B2796893
theorem B1864625 : Blo 1242439 1864625 := bstep (se 2 (by rfl) ⟨699234, by rfl⟩ : syracuseStep 1864625 = 1398469) B1398469
theorem B2798513 : Blo 1242439 2798513 := bstep (se 2 (by rfl) ⟨1049442, by rfl⟩ : syracuseStep 2798513 = 2098885) B2098885
theorem B1864643 : Blo 1242439 1864643 := bstep (se 1 (by rfl) ⟨1398482, by rfl⟩ : syracuseStep 1864643 = 2796965) B2796965
theorem B2798531 : Blo 1242439 2798531 := bstep (se 1 (by rfl) ⟨2098898, by rfl⟩ : syracuseStep 2798531 = 4197797) B4197797
theorem B4199363 : Blo 1242439 4199363 := bstep (se 1 (by rfl) ⟨3149522, by rfl⟩ : syracuseStep 4199363 = 6299045) B6299045
theorem B1864673 : Blo 1242439 1864673 := bstep (se 2 (by rfl) ⟨699252, by rfl⟩ : syracuseStep 1864673 = 1398505) B1398505
theorem B1864691 : Blo 1242439 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B1864721 : Blo 1242439 1864721 := bstep (se 2 (by rfl) ⟨699270, by rfl⟩ : syracuseStep 1864721 = 1398541) B1398541
theorem B1864739 : Blo 1242439 1864739 := bstep (se 1 (by rfl) ⟨1398554, by rfl⟩ : syracuseStep 1864739 = 2797109) B2797109
theorem B1864769 : Blo 1242439 1864769 := bstep (se 2 (by rfl) ⟨699288, by rfl⟩ : syracuseStep 1864769 = 1398577) B1398577
theorem B1864787 : Blo 1242439 1864787 := bstep (se 1 (by rfl) ⟨1398590, by rfl⟩ : syracuseStep 1864787 = 2797181) B2797181
theorem B1864817 : Blo 1242439 1864817 := bstep (se 2 (by rfl) ⟨699306, by rfl⟩ : syracuseStep 1864817 = 1398613) B1398613
theorem B1397875 : Blo 1242439 1397875 := bstep (se 1 (by rfl) ⟨1048406, by rfl⟩ : syracuseStep 1397875 = 2096813) B2096813
theorem B1864835 : Blo 1242439 1864835 := bstep (se 1 (by rfl) ⟨1398626, by rfl⟩ : syracuseStep 1864835 = 2797253) B2797253
theorem B1864865 : Blo 1242439 1864865 := bstep (se 2 (by rfl) ⟨699324, by rfl⟩ : syracuseStep 1864865 = 1398649) B1398649
theorem B1864883 : Blo 1242439 1864883 := bstep (se 1 (by rfl) ⟨1398662, by rfl⟩ : syracuseStep 1864883 = 2797325) B2797325
theorem B2987203 : Blo 1242439 2987203 := bstep (se 1 (by rfl) ⟨2240402, by rfl⟩ : syracuseStep 2987203 = 4480805) B4480805
theorem B1864913 : Blo 1242439 1864913 := bstep (se 2 (by rfl) ⟨699342, by rfl⟩ : syracuseStep 1864913 = 1398685) B1398685
theorem B2798801 : Blo 1242439 2798801 := bstep (se 2 (by rfl) ⟨1049550, by rfl⟩ : syracuseStep 2798801 = 2099101) B2099101
theorem B4199633 : Blo 1242439 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B1864931 : Blo 1242439 1864931 := bstep (se 1 (by rfl) ⟨1398698, by rfl⟩ : syracuseStep 1864931 = 2797397) B2797397
theorem B2798819 : Blo 1242439 2798819 := bstep (se 1 (by rfl) ⟨2099114, by rfl⟩ : syracuseStep 2798819 = 4198229) B4198229
theorem B1864961 : Blo 1242439 1864961 := bstep (se 2 (by rfl) ⟨699360, by rfl⟩ : syracuseStep 1864961 = 1398721) B1398721
theorem B1398019 : Blo 1242439 1398019 := bstep (se 1 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 1398019 = 2097029) B2097029
theorem B1864979 : Blo 1242439 1864979 := bstep (se 1 (by rfl) ⟨1398734, by rfl⟩ : syracuseStep 1864979 = 2797469) B2797469
theorem B1865009 : Blo 1242439 1865009 := bstep (se 2 (by rfl) ⟨699378, by rfl⟩ : syracuseStep 1865009 = 1398757) B1398757
theorem B1865027 : Blo 1242439 1865027 := bstep (se 1 (by rfl) ⟨1398770, by rfl⟩ : syracuseStep 1865027 = 2797541) B2797541
theorem B1242451 : Blo 1242439 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B1865057 : Blo 1242439 1865057 := bstep (se 2 (by rfl) ⟨699396, by rfl⟩ : syracuseStep 1865057 = 1398793) B1398793
theorem B1242467 : Blo 1242439 1242467 := bstep (se 1 (by rfl) ⟨931850, by rfl⟩ : syracuseStep 1242467 = 1863701) B1863701
theorem B7181681 : Blo 1242439 7181681 := bstep (se 2 (by rfl) ⟨2693130, by rfl⟩ : syracuseStep 7181681 = 5386261) B5386261
theorem B1242483 : Blo 1242439 1242483 := bstep (se 1 (by rfl) ⟨931862, by rfl⟩ : syracuseStep 1242483 = 1863725) B1863725
theorem B1865075 : Blo 1242439 1865075 := bstep (se 1 (by rfl) ⟨1398806, by rfl⟩ : syracuseStep 1865075 = 2797613) B2797613
theorem B1242499 : Blo 1242439 1242499 := bstep (se 1 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 1242499 = 1863749) B1863749
theorem B1865105 : Blo 1242439 1865105 := bstep (se 2 (by rfl) ⟨699414, by rfl⟩ : syracuseStep 1865105 = 1398829) B1398829
theorem B1242515 : Blo 1242439 1242515 := bstep (se 1 (by rfl) ⟨931886, by rfl⟩ : syracuseStep 1242515 = 1863773) B1863773
theorem B1398163 : Blo 1242439 1398163 := bstep (se 1 (by rfl) ⟨1048622, by rfl⟩ : syracuseStep 1398163 = 2097245) B2097245
theorem B1242531 : Blo 1242439 1242531 := bstep (se 1 (by rfl) ⟨931898, by rfl⟩ : syracuseStep 1242531 = 1863797) B1863797
theorem B1865123 : Blo 1242439 1865123 := bstep (se 1 (by rfl) ⟨1398842, by rfl⟩ : syracuseStep 1865123 = 2797685) B2797685
theorem B4257197 : Blo 1242439 4257197 := bstep (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) B1596449
theorem B1242547 : Blo 1242439 1242547 := bstep (se 1 (by rfl) ⟨931910, by rfl⟩ : syracuseStep 1242547 = 1863821) B1863821
theorem B1865153 : Blo 1242439 1865153 := bstep (se 2 (by rfl) ⟨699432, by rfl⟩ : syracuseStep 1865153 = 1398865) B1398865
theorem B1242563 : Blo 1242439 1242563 := bstep (se 1 (by rfl) ⟨931922, by rfl⟩ : syracuseStep 1242563 = 1863845) B1863845
theorem B1242579 : Blo 1242439 1242579 := bstep (se 1 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 1242579 = 1863869) B1863869
theorem B1865171 : Blo 1242439 1865171 := bstep (se 1 (by rfl) ⟨1398878, by rfl⟩ : syracuseStep 1865171 = 2797757) B2797757
theorem B1242595 : Blo 1242439 1242595 := bstep (se 1 (by rfl) ⟨931946, by rfl⟩ : syracuseStep 1242595 = 1863893) B1863893
theorem B26891747 : Blo 1242439 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1865201 : Blo 1242439 1865201 := bstep (se 2 (by rfl) ⟨699450, by rfl⟩ : syracuseStep 1865201 = 1398901) B1398901
theorem B2799089 : Blo 1242439 2799089 := bstep (se 2 (by rfl) ⟨1049658, by rfl⟩ : syracuseStep 2799089 = 2099317) B2099317
theorem B1242611 : Blo 1242439 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B1242627 : Blo 1242439 1242627 := bstep (se 1 (by rfl) ⟨931970, by rfl⟩ : syracuseStep 1242627 = 1863941) B1863941
theorem B1865219 : Blo 1242439 1865219 := bstep (se 1 (by rfl) ⟨1398914, by rfl⟩ : syracuseStep 1865219 = 2797829) B2797829
theorem B2799107 : Blo 1242439 2799107 := bstep (se 1 (by rfl) ⟨2099330, by rfl⟩ : syracuseStep 2799107 = 4198661) B4198661
theorem B6297101 : Blo 1242439 6297101 := bstep (se 3 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 6297101 = 2361413) B2361413
theorem B1242643 : Blo 1242439 1242643 := bstep (se 1 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 1242643 = 1863965) B1863965
theorem B1865249 : Blo 1242439 1865249 := bstep (se 2 (by rfl) ⟨699468, by rfl⟩ : syracuseStep 1865249 = 1398937) B1398937
theorem B1242659 : Blo 1242439 1242659 := bstep (se 1 (by rfl) ⟨931994, by rfl⟩ : syracuseStep 1242659 = 1863989) B1863989
theorem B1398307 : Blo 1242439 1398307 := bstep (se 1 (by rfl) ⟨1048730, by rfl⟩ : syracuseStep 1398307 = 2097461) B2097461
theorem B3782189 : Blo 1242439 3782189 := bstep (se 3 (by rfl) ⟨709160, by rfl⟩ : syracuseStep 3782189 = 1418321) B1418321
theorem B1242675 : Blo 1242439 1242675 := bstep (se 1 (by rfl) ⟨932006, by rfl⟩ : syracuseStep 1242675 = 1864013) B1864013
theorem B1865267 : Blo 1242439 1865267 := bstep (se 1 (by rfl) ⟨1398950, by rfl⟩ : syracuseStep 1865267 = 2797901) B2797901
theorem B1242691 : Blo 1242439 1242691 := bstep (se 1 (by rfl) ⟨932018, by rfl⟩ : syracuseStep 1242691 = 1864037) B1864037
theorem B1865297 : Blo 1242439 1865297 := bstep (se 2 (by rfl) ⟨699486, by rfl⟩ : syracuseStep 1865297 = 1398973) B1398973
theorem B1242707 : Blo 1242439 1242707 := bstep (se 1 (by rfl) ⟨932030, by rfl⟩ : syracuseStep 1242707 = 1864061) B1864061
theorem B1242723 : Blo 1242439 1242723 := bstep (se 1 (by rfl) ⟨932042, by rfl⟩ : syracuseStep 1242723 = 1864085) B1864085
theorem B1865315 : Blo 1242439 1865315 := bstep (se 1 (by rfl) ⟨1398986, by rfl⟩ : syracuseStep 1865315 = 2797973) B2797973
theorem B14366321 : Blo 1242439 14366321 := bstep (se 2 (by rfl) ⟨5387370, by rfl⟩ : syracuseStep 14366321 = 10774741) B10774741
theorem B1242739 : Blo 1242439 1242739 := bstep (se 1 (by rfl) ⟨932054, by rfl⟩ : syracuseStep 1242739 = 1864109) B1864109
theorem B1865345 : Blo 1242439 1865345 := bstep (se 2 (by rfl) ⟨699504, by rfl⟩ : syracuseStep 1865345 = 1399009) B1399009
theorem B1242755 : Blo 1242439 1242755 := bstep (se 1 (by rfl) ⟨932066, by rfl⟩ : syracuseStep 1242755 = 1864133) B1864133
theorem B1242771 : Blo 1242439 1242771 := bstep (se 1 (by rfl) ⟨932078, by rfl⟩ : syracuseStep 1242771 = 1864157) B1864157
theorem B1865363 : Blo 1242439 1865363 := bstep (se 1 (by rfl) ⟨1399022, by rfl⟩ : syracuseStep 1865363 = 2798045) B2798045
theorem B1242787 : Blo 1242439 1242787 := bstep (se 1 (by rfl) ⟨932090, by rfl⟩ : syracuseStep 1242787 = 1864181) B1864181
theorem B1865393 : Blo 1242439 1865393 := bstep (se 2 (by rfl) ⟨699522, by rfl⟩ : syracuseStep 1865393 = 1399045) B1399045
theorem B1242803 : Blo 1242439 1242803 := bstep (se 1 (by rfl) ⟨932102, by rfl⟩ : syracuseStep 1242803 = 1864205) B1864205
theorem B1398451 : Blo 1242439 1398451 := bstep (se 1 (by rfl) ⟨1048838, by rfl⟩ : syracuseStep 1398451 = 2097677) B2097677
theorem B1242819 : Blo 1242439 1242819 := bstep (se 1 (by rfl) ⟨932114, by rfl⟩ : syracuseStep 1242819 = 1864229) B1864229
theorem B1865411 : Blo 1242439 1865411 := bstep (se 1 (by rfl) ⟨1399058, by rfl⟩ : syracuseStep 1865411 = 2798117) B2798117
theorem B1242835 : Blo 1242439 1242835 := bstep (se 1 (by rfl) ⟨932126, by rfl⟩ : syracuseStep 1242835 = 1864253) B1864253
theorem B1865441 : Blo 1242439 1865441 := bstep (se 2 (by rfl) ⟨699540, by rfl⟩ : syracuseStep 1865441 = 1399081) B1399081
theorem B1242851 : Blo 1242439 1242851 := bstep (se 1 (by rfl) ⟨932138, by rfl⟩ : syracuseStep 1242851 = 1864277) B1864277
theorem B2987761 : Blo 1242439 2987761 := bstep (se 2 (by rfl) ⟨1120410, by rfl⟩ : syracuseStep 2987761 = 2240821) B2240821
theorem B1242867 : Blo 1242439 1242867 := bstep (se 1 (by rfl) ⟨932150, by rfl⟩ : syracuseStep 1242867 = 1864301) B1864301
theorem B1865459 : Blo 1242439 1865459 := bstep (se 1 (by rfl) ⟨1399094, by rfl⟩ : syracuseStep 1865459 = 2798189) B2798189
theorem B1890049 : Blo 1242439 1890049 := bstep (se 2 (by rfl) ⟨708768, by rfl⟩ : syracuseStep 1890049 = 1417537) B1417537
theorem B1242883 : Blo 1242439 1242883 := bstep (se 1 (by rfl) ⟨932162, by rfl⟩ : syracuseStep 1242883 = 1864325) B1864325
theorem B5379853 : Blo 1242439 5379853 := bstep (se 3 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 5379853 = 2017445) B2017445
theorem B1865489 : Blo 1242439 1865489 := bstep (se 2 (by rfl) ⟨699558, by rfl⟩ : syracuseStep 1865489 = 1399117) B1399117
theorem B2799377 : Blo 1242439 2799377 := bstep (se 2 (by rfl) ⟨1049766, by rfl⟩ : syracuseStep 2799377 = 2099533) B2099533
theorem B1242899 : Blo 1242439 1242899 := bstep (se 1 (by rfl) ⟨932174, by rfl⟩ : syracuseStep 1242899 = 1864349) B1864349
theorem B1242915 : Blo 1242439 1242915 := bstep (se 1 (by rfl) ⟨932186, by rfl⟩ : syracuseStep 1242915 = 1864373) B1864373
theorem B1865507 : Blo 1242439 1865507 := bstep (se 1 (by rfl) ⟨1399130, by rfl⟩ : syracuseStep 1865507 = 2798261) B2798261
theorem B2799395 : Blo 1242439 2799395 := bstep (se 1 (by rfl) ⟨2099546, by rfl⟩ : syracuseStep 2799395 = 4199093) B4199093
theorem B1242931 : Blo 1242439 1242931 := bstep (se 1 (by rfl) ⟨932198, by rfl⟩ : syracuseStep 1242931 = 1864397) B1864397
theorem B1865537 : Blo 1242439 1865537 := bstep (se 2 (by rfl) ⟨699576, by rfl⟩ : syracuseStep 1865537 = 1399153) B1399153
theorem B1242947 : Blo 1242439 1242947 := bstep (se 1 (by rfl) ⟨932210, by rfl⟩ : syracuseStep 1242947 = 1864421) B1864421
theorem B1398595 : Blo 1242439 1398595 := bstep (se 1 (by rfl) ⟨1048946, by rfl⟩ : syracuseStep 1398595 = 2097893) B2097893
theorem B1242963 : Blo 1242439 1242963 := bstep (se 1 (by rfl) ⟨932222, by rfl⟩ : syracuseStep 1242963 = 1864445) B1864445
theorem B1865555 : Blo 1242439 1865555 := bstep (se 1 (by rfl) ⟨1399166, by rfl⟩ : syracuseStep 1865555 = 2798333) B2798333
theorem B1242979 : Blo 1242439 1242979 := bstep (se 1 (by rfl) ⟨932234, by rfl⟩ : syracuseStep 1242979 = 1864469) B1864469
theorem B7083875 : Blo 1242439 7083875 := bstep (se 1 (by rfl) ⟨5312906, by rfl⟩ : syracuseStep 7083875 = 10625813) B10625813
theorem B1865585 : Blo 1242439 1865585 := bstep (se 2 (by rfl) ⟨699594, by rfl⟩ : syracuseStep 1865585 = 1399189) B1399189
theorem B1242995 : Blo 1242439 1242995 := bstep (se 1 (by rfl) ⟨932246, by rfl⟩ : syracuseStep 1242995 = 1864493) B1864493
theorem B1243011 : Blo 1242439 1243011 := bstep (se 1 (by rfl) ⟨932258, by rfl⟩ : syracuseStep 1243011 = 1864517) B1864517
theorem B1865603 : Blo 1242439 1865603 := bstep (se 1 (by rfl) ⟨1399202, by rfl⟩ : syracuseStep 1865603 = 2798405) B2798405
theorem B1243027 : Blo 1242439 1243027 := bstep (se 1 (by rfl) ⟨932270, by rfl⟩ : syracuseStep 1243027 = 1864541) B1864541
theorem B1865633 : Blo 1242439 1865633 := bstep (se 2 (by rfl) ⟨699612, by rfl⟩ : syracuseStep 1865633 = 1399225) B1399225
theorem B1243043 : Blo 1242439 1243043 := bstep (se 1 (by rfl) ⟨932282, by rfl⟩ : syracuseStep 1243043 = 1864565) B1864565
theorem B1243059 : Blo 1242439 1243059 := bstep (se 1 (by rfl) ⟨932294, by rfl⟩ : syracuseStep 1243059 = 1864589) B1864589
theorem B1865651 : Blo 1242439 1865651 := bstep (se 1 (by rfl) ⟨1399238, by rfl⟩ : syracuseStep 1865651 = 2798477) B2798477
theorem B1243075 : Blo 1242439 1243075 := bstep (se 1 (by rfl) ⟨932306, by rfl⟩ : syracuseStep 1243075 = 1864613) B1864613
theorem B1865681 : Blo 1242439 1865681 := bstep (se 2 (by rfl) ⟨699630, by rfl⟩ : syracuseStep 1865681 = 1399261) B1399261
theorem B1243091 : Blo 1242439 1243091 := bstep (se 1 (by rfl) ⟨932318, by rfl⟩ : syracuseStep 1243091 = 1864637) B1864637
theorem B1398739 : Blo 1242439 1398739 := bstep (se 1 (by rfl) ⟨1049054, by rfl⟩ : syracuseStep 1398739 = 2098109) B2098109
theorem B1243107 : Blo 1242439 1243107 := bstep (se 1 (by rfl) ⟨932330, by rfl⟩ : syracuseStep 1243107 = 1864661) B1864661
theorem B1865699 : Blo 1242439 1865699 := bstep (se 1 (by rfl) ⟨1399274, by rfl⟩ : syracuseStep 1865699 = 2798549) B2798549
theorem B5314531 : Blo 1242439 5314531 := bstep (se 1 (by rfl) ⟨3985898, by rfl⟩ : syracuseStep 5314531 = 7971797) B7971797
theorem B1243123 : Blo 1242439 1243123 := bstep (se 1 (by rfl) ⟨932342, by rfl⟩ : syracuseStep 1243123 = 1864685) B1864685
theorem B1865729 : Blo 1242439 1865729 := bstep (se 2 (by rfl) ⟨699648, by rfl⟩ : syracuseStep 1865729 = 1399297) B1399297
theorem B1243139 : Blo 1242439 1243139 := bstep (se 1 (by rfl) ⟨932354, by rfl⟩ : syracuseStep 1243139 = 1864709) B1864709
theorem B1243155 : Blo 1242439 1243155 := bstep (se 1 (by rfl) ⟨932366, by rfl⟩ : syracuseStep 1243155 = 1864733) B1864733
theorem B1865747 : Blo 1242439 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B1243171 : Blo 1242439 1243171 := bstep (se 1 (by rfl) ⟨932378, by rfl⟩ : syracuseStep 1243171 = 1864757) B1864757
theorem B1865777 : Blo 1242439 1865777 := bstep (se 2 (by rfl) ⟨699666, by rfl⟩ : syracuseStep 1865777 = 1399333) B1399333
theorem B2799665 : Blo 1242439 2799665 := bstep (se 2 (by rfl) ⟨1049874, by rfl⟩ : syracuseStep 2799665 = 2099749) B2099749
theorem B1243187 : Blo 1242439 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B1243203 : Blo 1242439 1243203 := bstep (se 1 (by rfl) ⟨932402, by rfl⟩ : syracuseStep 1243203 = 1864805) B1864805
theorem B1865795 : Blo 1242439 1865795 := bstep (se 1 (by rfl) ⟨1399346, by rfl⟩ : syracuseStep 1865795 = 2798693) B2798693
theorem B2799683 : Blo 1242439 2799683 := bstep (se 1 (by rfl) ⟨2099762, by rfl⟩ : syracuseStep 2799683 = 4199525) B4199525
theorem B1243219 : Blo 1242439 1243219 := bstep (se 1 (by rfl) ⟨932414, by rfl⟩ : syracuseStep 1243219 = 1864829) B1864829
theorem B1865825 : Blo 1242439 1865825 := bstep (se 2 (by rfl) ⟨699684, by rfl⟩ : syracuseStep 1865825 = 1399369) B1399369
theorem B1243235 : Blo 1242439 1243235 := bstep (se 1 (by rfl) ⟨932426, by rfl⟩ : syracuseStep 1243235 = 1864853) B1864853
theorem B1398883 : Blo 1242439 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B1243251 : Blo 1242439 1243251 := bstep (se 1 (by rfl) ⟨932438, by rfl⟩ : syracuseStep 1243251 = 1864877) B1864877
theorem B1865843 : Blo 1242439 1865843 := bstep (se 1 (by rfl) ⟨1399382, by rfl⟩ : syracuseStep 1865843 = 2798765) B2798765
theorem B1243267 : Blo 1242439 1243267 := bstep (se 1 (by rfl) ⟨932450, by rfl⟩ : syracuseStep 1243267 = 1864901) B1864901
theorem B1865873 : Blo 1242439 1865873 := bstep (se 2 (by rfl) ⟨699702, by rfl⟩ : syracuseStep 1865873 = 1399405) B1399405
theorem B1243283 : Blo 1242439 1243283 := bstep (se 1 (by rfl) ⟨932462, by rfl⟩ : syracuseStep 1243283 = 1864925) B1864925
theorem B1243299 : Blo 1242439 1243299 := bstep (se 1 (by rfl) ⟨932474, by rfl⟩ : syracuseStep 1243299 = 1864949) B1864949
theorem B1865891 : Blo 1242439 1865891 := bstep (se 1 (by rfl) ⟨1399418, by rfl⟩ : syracuseStep 1865891 = 2798837) B2798837
theorem B1243315 : Blo 1242439 1243315 := bstep (se 1 (by rfl) ⟨932486, by rfl⟩ : syracuseStep 1243315 = 1864973) B1864973
theorem B1865921 : Blo 1242439 1865921 := bstep (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) B1399441
theorem B1243331 : Blo 1242439 1243331 := bstep (se 1 (by rfl) ⟨932498, by rfl⟩ : syracuseStep 1243331 = 1864997) B1864997
theorem B1243347 : Blo 1242439 1243347 := bstep (se 1 (by rfl) ⟨932510, by rfl⟩ : syracuseStep 1243347 = 1865021) B1865021
theorem B1865939 : Blo 1242439 1865939 := bstep (se 1 (by rfl) ⟨1399454, by rfl⟩ : syracuseStep 1865939 = 2798909) B2798909
theorem B1243363 : Blo 1242439 1243363 := bstep (se 1 (by rfl) ⟨932522, by rfl⟩ : syracuseStep 1243363 = 1865045) B1865045
theorem B16152817 : Blo 1242439 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1865969 : Blo 1242439 1865969 := bstep (se 2 (by rfl) ⟨699738, by rfl⟩ : syracuseStep 1865969 = 1399477) B1399477
theorem B1243379 : Blo 1242439 1243379 := bstep (se 1 (by rfl) ⟨932534, by rfl⟩ : syracuseStep 1243379 = 1865069) B1865069
theorem B1399027 : Blo 1242439 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B1243395 : Blo 1242439 1243395 := bstep (se 1 (by rfl) ⟨932546, by rfl⟩ : syracuseStep 1243395 = 1865093) B1865093
theorem B1865987 : Blo 1242439 1865987 := bstep (se 1 (by rfl) ⟨1399490, by rfl⟩ : syracuseStep 1865987 = 2798981) B2798981
theorem B1243411 : Blo 1242439 1243411 := bstep (se 1 (by rfl) ⟨932558, by rfl⟩ : syracuseStep 1243411 = 1865117) B1865117
theorem B1866017 : Blo 1242439 1866017 := bstep (se 2 (by rfl) ⟨699756, by rfl⟩ : syracuseStep 1866017 = 1399513) B1399513
theorem B1243427 : Blo 1242439 1243427 := bstep (se 1 (by rfl) ⟨932570, by rfl⟩ : syracuseStep 1243427 = 1865141) B1865141
theorem B1243443 : Blo 1242439 1243443 := bstep (se 1 (by rfl) ⟨932582, by rfl⟩ : syracuseStep 1243443 = 1865165) B1865165
theorem B1866035 : Blo 1242439 1866035 := bstep (se 1 (by rfl) ⟨1399526, by rfl⟩ : syracuseStep 1866035 = 2799053) B2799053
theorem B1243459 : Blo 1242439 1243459 := bstep (se 1 (by rfl) ⟨932594, by rfl⟩ : syracuseStep 1243459 = 1865189) B1865189
theorem B1866065 : Blo 1242439 1866065 := bstep (se 2 (by rfl) ⟨699774, by rfl⟩ : syracuseStep 1866065 = 1399549) B1399549
theorem B1243475 : Blo 1242439 1243475 := bstep (se 1 (by rfl) ⟨932606, by rfl⟩ : syracuseStep 1243475 = 1865213) B1865213
theorem B2799953 : Blo 1242439 2799953 := bstep (se 2 (by rfl) ⟨1049982, by rfl⟩ : syracuseStep 2799953 = 2099965) B2099965
theorem B1243491 : Blo 1242439 1243491 := bstep (se 1 (by rfl) ⟨932618, by rfl⟩ : syracuseStep 1243491 = 1865237) B1865237
theorem B1866083 : Blo 1242439 1866083 := bstep (se 1 (by rfl) ⟨1399562, by rfl⟩ : syracuseStep 1866083 = 2799125) B2799125
theorem B2799971 : Blo 1242439 2799971 := bstep (se 1 (by rfl) ⟨2099978, by rfl⟩ : syracuseStep 2799971 = 4199957) B4199957
theorem B1243507 : Blo 1242439 1243507 := bstep (se 1 (by rfl) ⟨932630, by rfl⟩ : syracuseStep 1243507 = 1865261) B1865261
theorem B1866113 : Blo 1242439 1866113 := bstep (se 2 (by rfl) ⟨699792, by rfl⟩ : syracuseStep 1866113 = 1399585) B1399585
theorem B1243523 : Blo 1242439 1243523 := bstep (se 1 (by rfl) ⟨932642, by rfl⟩ : syracuseStep 1243523 = 1865285) B1865285
theorem B1399171 : Blo 1242439 1399171 := bstep (se 1 (by rfl) ⟨1049378, by rfl⟩ : syracuseStep 1399171 = 2098757) B2098757
theorem B2988433 : Blo 1242439 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B1243539 : Blo 1242439 1243539 := bstep (se 1 (by rfl) ⟨932654, by rfl⟩ : syracuseStep 1243539 = 1865309) B1865309
theorem B1866131 : Blo 1242439 1866131 := bstep (se 1 (by rfl) ⟨1399598, by rfl⟩ : syracuseStep 1866131 = 2799197) B2799197
theorem B1243555 : Blo 1242439 1243555 := bstep (se 1 (by rfl) ⟨932666, by rfl⟩ : syracuseStep 1243555 = 1865333) B1865333
theorem B1866161 : Blo 1242439 1866161 := bstep (se 2 (by rfl) ⟨699810, by rfl⟩ : syracuseStep 1866161 = 1399621) B1399621
theorem B1243571 : Blo 1242439 1243571 := bstep (se 1 (by rfl) ⟨932678, by rfl⟩ : syracuseStep 1243571 = 1865357) B1865357
theorem B1243587 : Blo 1242439 1243587 := bstep (se 1 (by rfl) ⟨932690, by rfl⟩ : syracuseStep 1243587 = 1865381) B1865381
theorem B1866179 : Blo 1242439 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1243603 : Blo 1242439 1243603 := bstep (se 1 (by rfl) ⟨932702, by rfl⟩ : syracuseStep 1243603 = 1865405) B1865405
theorem B1866209 : Blo 1242439 1866209 := bstep (se 2 (by rfl) ⟨699828, by rfl⟩ : syracuseStep 1866209 = 1399657) B1399657
theorem B1243619 : Blo 1242439 1243619 := bstep (se 1 (by rfl) ⟨932714, by rfl⟩ : syracuseStep 1243619 = 1865429) B1865429
theorem B1243635 : Blo 1242439 1243635 := bstep (se 1 (by rfl) ⟨932726, by rfl⟩ : syracuseStep 1243635 = 1865453) B1865453
theorem B1866227 : Blo 1242439 1866227 := bstep (se 1 (by rfl) ⟨1399670, by rfl⟩ : syracuseStep 1866227 = 2799341) B2799341
theorem B1243651 : Blo 1242439 1243651 := bstep (se 1 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 1243651 = 1865477) B1865477
theorem B1866257 : Blo 1242439 1866257 := bstep (se 2 (by rfl) ⟨699846, by rfl⟩ : syracuseStep 1866257 = 1399693) B1399693
theorem B1243667 : Blo 1242439 1243667 := bstep (se 1 (by rfl) ⟨932750, by rfl⟩ : syracuseStep 1243667 = 1865501) B1865501
theorem B1399315 : Blo 1242439 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B1243683 : Blo 1242439 1243683 := bstep (se 1 (by rfl) ⟨932762, by rfl⟩ : syracuseStep 1243683 = 1865525) B1865525
theorem B1866275 : Blo 1242439 1866275 := bstep (se 1 (by rfl) ⟨1399706, by rfl⟩ : syracuseStep 1866275 = 2799413) B2799413
theorem B4037165 : Blo 1242439 4037165 := bstep (se 3 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 4037165 = 1513937) B1513937
theorem B1243699 : Blo 1242439 1243699 := bstep (se 1 (by rfl) ⟨932774, by rfl⟩ : syracuseStep 1243699 = 1865549) B1865549
theorem B1866305 : Blo 1242439 1866305 := bstep (se 2 (by rfl) ⟨699864, by rfl⟩ : syracuseStep 1866305 = 1399729) B1399729
theorem B1243715 : Blo 1242439 1243715 := bstep (se 1 (by rfl) ⟨932786, by rfl⟩ : syracuseStep 1243715 = 1865573) B1865573
theorem B1243731 : Blo 1242439 1243731 := bstep (se 1 (by rfl) ⟨932798, by rfl⟩ : syracuseStep 1243731 = 1865597) B1865597
theorem B1866323 : Blo 1242439 1866323 := bstep (se 1 (by rfl) ⟨1399742, by rfl⟩ : syracuseStep 1866323 = 2799485) B2799485
theorem B1243747 : Blo 1242439 1243747 := bstep (se 1 (by rfl) ⟨932810, by rfl⟩ : syracuseStep 1243747 = 1865621) B1865621
theorem B1866353 : Blo 1242439 1866353 := bstep (se 2 (by rfl) ⟨699882, by rfl⟩ : syracuseStep 1866353 = 1399765) B1399765
theorem B1514099 : Blo 1242439 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B1243763 : Blo 1242439 1243763 := bstep (se 1 (by rfl) ⟨932822, by rfl⟩ : syracuseStep 1243763 = 1865645) B1865645
theorem B1243779 : Blo 1242439 1243779 := bstep (se 1 (by rfl) ⟨932834, by rfl⟩ : syracuseStep 1243779 = 1865669) B1865669
theorem B1866371 : Blo 1242439 1866371 := bstep (se 1 (by rfl) ⟨1399778, by rfl⟩ : syracuseStep 1866371 = 2799557) B2799557
theorem B1243795 : Blo 1242439 1243795 := bstep (se 1 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 1243795 = 1865693) B1865693
theorem B1866401 : Blo 1242439 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B1243811 : Blo 1242439 1243811 := bstep (se 1 (by rfl) ⟨932858, by rfl⟩ : syracuseStep 1243811 = 1865717) B1865717
theorem B1399459 : Blo 1242439 1399459 := bstep (se 1 (by rfl) ⟨1049594, by rfl⟩ : syracuseStep 1399459 = 2099189) B2099189
theorem B1243827 : Blo 1242439 1243827 := bstep (se 1 (by rfl) ⟨932870, by rfl⟩ : syracuseStep 1243827 = 1865741) B1865741
theorem B1866419 : Blo 1242439 1866419 := bstep (se 1 (by rfl) ⟨1399814, by rfl⟩ : syracuseStep 1866419 = 2799629) B2799629
theorem B1243843 : Blo 1242439 1243843 := bstep (se 1 (by rfl) ⟨932882, by rfl⟩ : syracuseStep 1243843 = 1865765) B1865765
theorem B1866449 : Blo 1242439 1866449 := bstep (se 2 (by rfl) ⟨699918, by rfl⟩ : syracuseStep 1866449 = 1399837) B1399837
theorem B1243859 : Blo 1242439 1243859 := bstep (se 1 (by rfl) ⟨932894, by rfl⟩ : syracuseStep 1243859 = 1865789) B1865789
theorem B1243875 : Blo 1242439 1243875 := bstep (se 1 (by rfl) ⟨932906, by rfl⟩ : syracuseStep 1243875 = 1865813) B1865813
theorem B1866467 : Blo 1242439 1866467 := bstep (se 1 (by rfl) ⟨1399850, by rfl⟩ : syracuseStep 1866467 = 2799701) B2799701
theorem B1243891 : Blo 1242439 1243891 := bstep (se 1 (by rfl) ⟨932918, by rfl⟩ : syracuseStep 1243891 = 1865837) B1865837
theorem B1866497 : Blo 1242439 1866497 := bstep (se 2 (by rfl) ⟨699936, by rfl⟩ : syracuseStep 1866497 = 1399873) B1399873
theorem B1243907 : Blo 1242439 1243907 := bstep (se 1 (by rfl) ⟨932930, by rfl⟩ : syracuseStep 1243907 = 1865861) B1865861
theorem B1243923 : Blo 1242439 1243923 := bstep (se 1 (by rfl) ⟨932942, by rfl⟩ : syracuseStep 1243923 = 1865885) B1865885
theorem B1866515 : Blo 1242439 1866515 := bstep (se 1 (by rfl) ⟨1399886, by rfl⟩ : syracuseStep 1866515 = 2799773) B2799773
theorem B1243939 : Blo 1242439 1243939 := bstep (se 1 (by rfl) ⟨932954, by rfl⟩ : syracuseStep 1243939 = 1865909) B1865909
theorem B1866545 : Blo 1242439 1866545 := bstep (se 2 (by rfl) ⟨699954, by rfl⟩ : syracuseStep 1866545 = 1399909) B1399909
theorem B1243955 : Blo 1242439 1243955 := bstep (se 1 (by rfl) ⟨932966, by rfl⟩ : syracuseStep 1243955 = 1865933) B1865933
theorem B1399603 : Blo 1242439 1399603 := bstep (se 1 (by rfl) ⟨1049702, by rfl⟩ : syracuseStep 1399603 = 2099405) B2099405
theorem B1243971 : Blo 1242439 1243971 := bstep (se 1 (by rfl) ⟨932978, by rfl⟩ : syracuseStep 1243971 = 1865957) B1865957
theorem B1866563 : Blo 1242439 1866563 := bstep (se 1 (by rfl) ⟨1399922, by rfl⟩ : syracuseStep 1866563 = 2799845) B2799845
theorem B1243987 : Blo 1242439 1243987 := bstep (se 1 (by rfl) ⟨932990, by rfl⟩ : syracuseStep 1243987 = 1865981) B1865981
theorem B1866593 : Blo 1242439 1866593 := bstep (se 2 (by rfl) ⟨699972, by rfl⟩ : syracuseStep 1866593 = 1399945) B1399945
theorem B1244003 : Blo 1242439 1244003 := bstep (se 1 (by rfl) ⟨933002, by rfl⟩ : syracuseStep 1244003 = 1866005) B1866005
theorem B7560049 : Blo 1242439 7560049 := bstep (se 2 (by rfl) ⟨2835018, by rfl⟩ : syracuseStep 7560049 = 5670037) B5670037
theorem B1244019 : Blo 1242439 1244019 := bstep (se 1 (by rfl) ⟨933014, by rfl⟩ : syracuseStep 1244019 = 1866029) B1866029
theorem B1866611 : Blo 1242439 1866611 := bstep (se 1 (by rfl) ⟨1399958, by rfl⟩ : syracuseStep 1866611 = 2799917) B2799917
theorem B1244035 : Blo 1242439 1244035 := bstep (se 1 (by rfl) ⟨933026, by rfl⟩ : syracuseStep 1244035 = 1866053) B1866053
theorem B1866641 : Blo 1242439 1866641 := bstep (se 2 (by rfl) ⟨699990, by rfl⟩ : syracuseStep 1866641 = 1399981) B1399981
theorem B1244051 : Blo 1242439 1244051 := bstep (se 1 (by rfl) ⟨933038, by rfl⟩ : syracuseStep 1244051 = 1866077) B1866077
theorem B1244067 : Blo 1242439 1244067 := bstep (se 1 (by rfl) ⟨933050, by rfl⟩ : syracuseStep 1244067 = 1866101) B1866101
theorem B1866659 : Blo 1242439 1866659 := bstep (se 1 (by rfl) ⟨1399994, by rfl⟩ : syracuseStep 1866659 = 2799989) B2799989
theorem B3783601 : Blo 1242439 3783601 := bstep (se 2 (by rfl) ⟨1418850, by rfl⟩ : syracuseStep 3783601 = 2837701) B2837701
theorem B1244083 : Blo 1242439 1244083 := bstep (se 1 (by rfl) ⟨933062, by rfl⟩ : syracuseStep 1244083 = 1866125) B1866125
theorem B1244099 : Blo 1242439 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B1399747 : Blo 1242439 1399747 := bstep (se 1 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 1399747 = 2099621) B2099621
theorem B1244115 : Blo 1242439 1244115 := bstep (se 1 (by rfl) ⟨933086, by rfl⟩ : syracuseStep 1244115 = 1866173) B1866173
theorem B1244131 : Blo 1242439 1244131 := bstep (se 1 (by rfl) ⟨933098, by rfl⟩ : syracuseStep 1244131 = 1866197) B1866197
theorem B4193261 : Blo 1242439 4193261 := bstep (se 3 (by rfl) ⟨786236, by rfl⟩ : syracuseStep 4193261 = 1572473) B1572473
theorem B1244147 : Blo 1242439 1244147 := bstep (se 1 (by rfl) ⟨933110, by rfl⟩ : syracuseStep 1244147 = 1866221) B1866221
theorem B1244163 : Blo 1242439 1244163 := bstep (se 1 (by rfl) ⟨933122, by rfl⟩ : syracuseStep 1244163 = 1866245) B1866245
theorem B1244179 : Blo 1242439 1244179 := bstep (se 1 (by rfl) ⟨933134, by rfl⟩ : syracuseStep 1244179 = 1866269) B1866269
theorem B4193315 : Blo 1242439 4193315 := bstep (se 1 (by rfl) ⟨3144986, by rfl⟩ : syracuseStep 4193315 = 6289973) B6289973
theorem B1244195 : Blo 1242439 1244195 := bstep (se 1 (by rfl) ⟨933146, by rfl⟩ : syracuseStep 1244195 = 1866293) B1866293
theorem B1244211 : Blo 1242439 1244211 := bstep (se 1 (by rfl) ⟨933158, by rfl⟩ : syracuseStep 1244211 = 1866317) B1866317
theorem B1244227 : Blo 1242439 1244227 := bstep (se 1 (by rfl) ⟨933170, by rfl⟩ : syracuseStep 1244227 = 1866341) B1866341
theorem B1244243 : Blo 1242439 1244243 := bstep (se 1 (by rfl) ⟨933182, by rfl⟩ : syracuseStep 1244243 = 1866365) B1866365
theorem B1399891 : Blo 1242439 1399891 := bstep (se 1 (by rfl) ⟨1049918, by rfl⟩ : syracuseStep 1399891 = 2099837) B2099837
theorem B1244259 : Blo 1242439 1244259 := bstep (se 1 (by rfl) ⟨933194, by rfl⟩ : syracuseStep 1244259 = 1866389) B1866389
theorem B1244275 : Blo 1242439 1244275 := bstep (se 1 (by rfl) ⟨933206, by rfl⟩ : syracuseStep 1244275 = 1866413) B1866413
theorem B1244291 : Blo 1242439 1244291 := bstep (se 1 (by rfl) ⟨933218, by rfl⟩ : syracuseStep 1244291 = 1866437) B1866437
theorem B4717709 : Blo 1242439 4717709 := bstep (se 3 (by rfl) ⟨884570, by rfl⟩ : syracuseStep 4717709 = 1769141) B1769141
theorem B1244307 : Blo 1242439 1244307 := bstep (se 1 (by rfl) ⟨933230, by rfl⟩ : syracuseStep 1244307 = 1866461) B1866461
theorem B1244323 : Blo 1242439 1244323 := bstep (se 1 (by rfl) ⟨933242, by rfl⟩ : syracuseStep 1244323 = 1866485) B1866485
theorem B7077041 : Blo 1242439 7077041 := bstep (se 2 (by rfl) ⟨2653890, by rfl⟩ : syracuseStep 7077041 = 5307781) B5307781
theorem B1244339 : Blo 1242439 1244339 := bstep (se 1 (by rfl) ⟨933254, by rfl⟩ : syracuseStep 1244339 = 1866509) B1866509
theorem B1244355 : Blo 1242439 1244355 := bstep (se 1 (by rfl) ⟨933266, by rfl⟩ : syracuseStep 1244355 = 1866533) B1866533
theorem B1244371 : Blo 1242439 1244371 := bstep (se 1 (by rfl) ⟨933278, by rfl⟩ : syracuseStep 1244371 = 1866557) B1866557
theorem B1244387 : Blo 1242439 1244387 := bstep (se 1 (by rfl) ⟨933290, by rfl⟩ : syracuseStep 1244387 = 1866581) B1866581
theorem B3783917 : Blo 1242439 3783917 := bstep (se 3 (by rfl) ⟨709484, by rfl⟩ : syracuseStep 3783917 = 1418969) B1418969
theorem B1244403 : Blo 1242439 1244403 := bstep (se 1 (by rfl) ⟨933302, by rfl⟩ : syracuseStep 1244403 = 1866605) B1866605
theorem B1244419 : Blo 1242439 1244419 := bstep (se 1 (by rfl) ⟨933314, by rfl⟩ : syracuseStep 1244419 = 1866629) B1866629
theorem B3144977 : Blo 1242439 3144977 := bstep (se 2 (by rfl) ⟨1179366, by rfl⟩ : syracuseStep 3144977 = 2358733) B2358733
theorem B1244435 : Blo 1242439 1244435 := bstep (se 1 (by rfl) ⟨933326, by rfl⟩ : syracuseStep 1244435 = 1866653) B1866653
theorem B4193585 : Blo 1242439 4193585 := bstep (se 2 (by rfl) ⟨1572594, by rfl⟩ : syracuseStep 4193585 = 3145189) B3145189
theorem B3145027 : Blo 1242439 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B17939825 : Blo 1242439 17939825 := bstep (se 2 (by rfl) ⟨6727434, by rfl⟩ : syracuseStep 17939825 = 13454869) B13454869
theorem B3145169 : Blo 1242439 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B7962083 : Blo 1242439 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B17006051 : Blo 1242439 17006051 := bstep (se 1 (by rfl) ⟨12754538, by rfl⟩ : syracuseStep 17006051 = 25509077) B25509077
theorem B3980785 : Blo 1242439 3980785 := bstep (se 2 (by rfl) ⟨1492794, by rfl⟩ : syracuseStep 3980785 = 2985589) B2985589
theorem B1891873 : Blo 1242439 1891873 := bstep (se 2 (by rfl) ⟨709452, by rfl⟩ : syracuseStep 1891873 = 1418905) B1418905
theorem B2522659 : Blo 1242439 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B2391601 : Blo 1242439 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B2096705 : Blo 1242439 2096705 := bstep (se 2 (by rfl) ⟨786264, by rfl⟩ : syracuseStep 2096705 = 1572529) B1572529
theorem B6291107 : Blo 1242439 6291107 := bstep (se 1 (by rfl) ⟨4718330, by rfl⟩ : syracuseStep 6291107 = 9436661) B9436661
theorem B2096833 : Blo 1242439 2096833 := bstep (se 2 (by rfl) ⟨786312, by rfl⟩ : syracuseStep 2096833 = 1572625) B1572625
theorem B2096867 : Blo 1242439 2096867 := bstep (se 1 (by rfl) ⟨1572650, by rfl⟩ : syracuseStep 2096867 = 3145301) B3145301
theorem B40304405 : Blo 1242439 40304405 := bstep (se 6 (by rfl) ⟨944634, by rfl⟩ : syracuseStep 40304405 = 1889269) B1889269
theorem B1769249 : Blo 1242439 1769249 := bstep (se 2 (by rfl) ⟨663468, by rfl⟩ : syracuseStep 1769249 = 1326937) B1326937
theorem B4194125 : Blo 1242439 4194125 := bstep (se 3 (by rfl) ⟨786398, by rfl⟩ : syracuseStep 4194125 = 1572797) B1572797
theorem B1572691 : Blo 1242439 1572691 := bstep (se 1 (by rfl) ⟨1179518, by rfl⟩ : syracuseStep 1572691 = 2359037) B2359037
theorem B2096995 : Blo 1242439 2096995 := bstep (se 1 (by rfl) ⟨1572746, by rfl⟩ : syracuseStep 2096995 = 3145493) B3145493
theorem B4194179 : Blo 1242439 4194179 := bstep (se 1 (by rfl) ⟨3145634, by rfl⟩ : syracuseStep 4194179 = 6291269) B6291269
theorem B3538829 : Blo 1242439 3538829 := bstep (se 3 (by rfl) ⟨663530, by rfl⟩ : syracuseStep 3538829 = 1327061) B1327061
theorem B4718513 : Blo 1242439 4718513 := bstep (se 2 (by rfl) ⟨1769442, by rfl⟩ : syracuseStep 4718513 = 3538885) B3538885
theorem B1572787 : Blo 1242439 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B2654147 : Blo 1242439 2654147 := bstep (se 1 (by rfl) ⟨1990610, by rfl⟩ : syracuseStep 2654147 = 3981221) B3981221
theorem B2097137 : Blo 1242439 2097137 := bstep (se 2 (by rfl) ⟨786426, by rfl⟩ : syracuseStep 2097137 = 1572853) B1572853
theorem B6053933 : Blo 1242439 6053933 := bstep (se 3 (by rfl) ⟨1135112, by rfl⟩ : syracuseStep 6053933 = 2270225) B2270225
theorem B6299693 : Blo 1242439 6299693 := bstep (se 3 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 6299693 = 2362385) B2362385
theorem B4718681 : Blo 1242439 4718681 := bstep (se 2 (by rfl) ⟨1769505, by rfl⟩ : syracuseStep 4718681 = 3539011) B3539011
theorem B3145817 : Blo 1242439 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B1573015 : Blo 1242439 1573015 := bstep (se 1 (by rfl) ⟨1179761, by rfl⟩ : syracuseStep 1573015 = 2359523) B2359523
theorem B4784429 : Blo 1242439 4784429 := bstep (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) B1794161
theorem B4194611 : Blo 1242439 4194611 := bstep (se 1 (by rfl) ⟨3145958, by rfl⟩ : syracuseStep 4194611 = 6291917) B6291917
theorem B21537089 : Blo 1242439 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B4481369 : Blo 1242439 4481369 := bstep (se 2 (by rfl) ⟨1680513, by rfl⟩ : syracuseStep 4481369 = 3361027) B3361027
theorem B2359667 : Blo 1242439 2359667 := bstep (se 1 (by rfl) ⟨1769750, by rfl⟩ : syracuseStep 2359667 = 3539501) B3539501
theorem B4718999 : Blo 1242439 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B2359705 : Blo 1242439 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B2097623 : Blo 1242439 2097623 := bstep (se 1 (by rfl) ⟨1573217, by rfl⟩ : syracuseStep 2097623 = 3146435) B3146435
theorem B4481497 : Blo 1242439 4481497 := bstep (se 2 (by rfl) ⟨1680561, by rfl⟩ : syracuseStep 4481497 = 3361123) B3361123
theorem B1770007 : Blo 1242439 1770007 := bstep (se 1 (by rfl) ⟨1327505, by rfl⟩ : syracuseStep 1770007 = 2655011) B2655011
theorem B4194881 : Blo 1242439 4194881 := bstep (se 2 (by rfl) ⟨1573080, by rfl⟩ : syracuseStep 4194881 = 3146161) B3146161
theorem B2097751 : Blo 1242439 2097751 := bstep (se 1 (by rfl) ⟨1573313, by rfl⟩ : syracuseStep 2097751 = 3146627) B3146627
theorem B4481729 : Blo 1242439 4481729 := bstep (se 2 (by rfl) ⟨1680648, by rfl⟩ : syracuseStep 4481729 = 3361297) B3361297
theorem B6292241 : Blo 1242439 6292241 := bstep (se 2 (by rfl) ⟨2359590, by rfl⟩ : syracuseStep 6292241 = 4719181) B4719181
theorem B2360153 : Blo 1242439 2360153 := bstep (se 2 (by rfl) ⟨885057, by rfl⟩ : syracuseStep 2360153 = 1770115) B1770115
theorem B5669783 : Blo 1242439 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B3146647 : Blo 1242439 3146647 := bstep (se 1 (by rfl) ⟨2359985, by rfl⟩ : syracuseStep 3146647 = 4719971) B4719971
theorem B6292403 : Blo 1242439 6292403 := bstep (se 1 (by rfl) ⟨4719302, by rfl⟩ : syracuseStep 6292403 = 9438605) B9438605
theorem B2655155 : Blo 1242439 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B3539933 : Blo 1242439 3539933 := bstep (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) B1327475
theorem B4719667 : Blo 1242439 4719667 := bstep (se 1 (by rfl) ⟨3539750, by rfl⟩ : syracuseStep 4719667 = 7079501) B7079501
theorem B9577547 : Blo 1242439 9577547 := bstep (se 1 (by rfl) ⟨7183160, by rfl⟩ : syracuseStep 9577547 = 14366321) B14366321
theorem B4195421 : Blo 1242439 4195421 := bstep (se 3 (by rfl) ⟨786641, by rfl⟩ : syracuseStep 4195421 = 1573283) B1573283
theorem B3540161 : Blo 1242439 3540161 := bstep (se 2 (by rfl) ⟨1327560, by rfl⟩ : syracuseStep 3540161 = 2655121) B2655121
theorem B2098379 : Blo 1242439 2098379 := bstep (se 1 (by rfl) ⟨1573784, by rfl⟩ : syracuseStep 2098379 = 3147569) B3147569
theorem B3147083 : Blo 1242439 3147083 := bstep (se 1 (by rfl) ⟨2360312, by rfl⟩ : syracuseStep 3147083 = 4720625) B4720625
theorem B2098507 : Blo 1242439 2098507 := bstep (se 1 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 2098507 = 3147761) B3147761
theorem B6817117 : Blo 1242439 6817117 := bstep (se 3 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 6817117 = 2556419) B2556419
theorem B55248277 : Blo 1242439 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B5383597 : Blo 1242439 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B2098649 : Blo 1242439 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B1328599 : Blo 1242439 1328599 := bstep (se 1 (by rfl) ⟨996449, by rfl⟩ : syracuseStep 1328599 = 1992899) B1992899
theorem B3540503 : Blo 1242439 3540503 := bstep (se 1 (by rfl) ⟨2655377, by rfl⟩ : syracuseStep 3540503 = 5310755) B5310755
theorem B5113367 : Blo 1242439 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B2360897 : Blo 1242439 2360897 := bstep (se 2 (by rfl) ⟨885336, by rfl⟩ : syracuseStep 2360897 = 1770673) B1770673
theorem B3982937 : Blo 1242439 3982937 := bstep (se 2 (by rfl) ⟨1493601, by rfl⟩ : syracuseStep 3982937 = 2987203) B2987203
theorem B2098777 : Blo 1242439 2098777 := bstep (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) B1574083
theorem B3147457 : Blo 1242439 3147457 := bstep (se 2 (by rfl) ⟨1180296, by rfl⟩ : syracuseStep 3147457 = 2360593) B2360593
theorem B5310173 : Blo 1242439 5310173 := bstep (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) B1991315
theorem B17917681 : Blo 1242439 17917681 := bstep (se 2 (by rfl) ⟨6719130, by rfl⟩ : syracuseStep 17917681 = 13438261) B13438261
theorem B6915905 : Blo 1242439 6915905 := bstep (se 2 (by rfl) ⟨2593464, by rfl⟩ : syracuseStep 6915905 = 5186929) B5186929
theorem B4482881 : Blo 1242439 4482881 := bstep (se 2 (by rfl) ⟨1681080, by rfl⟩ : syracuseStep 4482881 = 3362161) B3362161
theorem B2361163 : Blo 1242439 2361163 := bstep (se 1 (by rfl) ⟨1770872, by rfl⟩ : syracuseStep 2361163 = 3541745) B3541745
theorem B1574731 : Blo 1242439 1574731 := bstep (se 1 (by rfl) ⟨1181048, by rfl⟩ : syracuseStep 1574731 = 2362097) B2362097
theorem B10618775 : Blo 1242439 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B2795507 : Blo 1242439 2795507 := bstep (se 1 (by rfl) ⟨2096630, by rfl⟩ : syracuseStep 2795507 = 4193261) B4193261
theorem B5310481 : Blo 1242439 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B2795543 : Blo 1242439 2795543 := bstep (se 1 (by rfl) ⟨2096657, by rfl⟩ : syracuseStep 2795543 = 4193315) B4193315
theorem B5310515 : Blo 1242439 5310515 := bstep (se 1 (by rfl) ⟨3982886, by rfl⟩ : syracuseStep 5310515 = 7965773) B7965773
theorem B3188801 : Blo 1242439 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B2099351 : Blo 1242439 2099351 := bstep (se 1 (by rfl) ⟨1574513, by rfl⟩ : syracuseStep 2099351 = 3149027) B3149027
theorem B2795723 : Blo 1242439 2795723 := bstep (se 1 (by rfl) ⟨2096792, by rfl⟩ : syracuseStep 2795723 = 4193585) B4193585
theorem B4196555 : Blo 1242439 4196555 := bstep (se 1 (by rfl) ⟨3147416, by rfl⟩ : syracuseStep 4196555 = 6294833) B6294833
theorem B2656471 : Blo 1242439 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B2795777 : Blo 1242439 2795777 := bstep (se 2 (by rfl) ⟨1048416, by rfl⟩ : syracuseStep 2795777 = 2096833) B2096833
theorem B2361611 : Blo 1242439 2361611 := bstep (se 1 (by rfl) ⟨1771208, by rfl⟩ : syracuseStep 2361611 = 3542417) B3542417
theorem B7080209 : Blo 1242439 7080209 := bstep (se 2 (by rfl) ⟨2655078, by rfl⟩ : syracuseStep 7080209 = 5310157) B5310157
theorem B4720913 : Blo 1242439 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B3148055 : Blo 1242439 3148055 := bstep (se 1 (by rfl) ⟨2361041, by rfl⟩ : syracuseStep 3148055 = 4722083) B4722083
theorem B2099479 : Blo 1242439 2099479 := bstep (se 1 (by rfl) ⟨1574609, by rfl⟩ : syracuseStep 2099479 = 3149219) B3149219
theorem B1345847 : Blo 1242439 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B3983681 : Blo 1242439 3983681 := bstep (se 2 (by rfl) ⟨1493880, by rfl⟩ : syracuseStep 3983681 = 2987761) B2987761
theorem B2656651 : Blo 1242439 2656651 := bstep (se 1 (by rfl) ⟨1992488, by rfl⟩ : syracuseStep 2656651 = 3984977) B3984977
theorem B2361793 : Blo 1242439 2361793 := bstep (se 2 (by rfl) ⟨885672, by rfl⟩ : syracuseStep 2361793 = 1771345) B1771345
theorem B2795993 : Blo 1242439 2795993 := bstep (se 2 (by rfl) ⟨1048497, by rfl⟩ : syracuseStep 2795993 = 2096995) B2096995
theorem B4196825 : Blo 1242439 4196825 := bstep (se 2 (by rfl) ⟨1573809, by rfl⟩ : syracuseStep 4196825 = 3147619) B3147619
theorem B2656727 : Blo 1242439 2656727 := bstep (se 1 (by rfl) ⟨1992545, by rfl⟩ : syracuseStep 2656727 = 3985091) B3985091
theorem B2796083 : Blo 1242439 2796083 := bstep (se 1 (by rfl) ⟨2097062, by rfl⟩ : syracuseStep 2796083 = 4194125) B4194125
theorem B2796119 : Blo 1242439 2796119 := bstep (se 1 (by rfl) ⟨2097089, by rfl⟩ : syracuseStep 2796119 = 4194179) B4194179
theorem B2796299 : Blo 1242439 2796299 := bstep (se 1 (by rfl) ⟨2097224, by rfl⟩ : syracuseStep 2796299 = 4194449) B4194449
theorem B2362135 : Blo 1242439 2362135 := bstep (se 1 (by rfl) ⟨1771601, by rfl⟩ : syracuseStep 2362135 = 3543203) B3543203
theorem B14158637 : Blo 1242439 14158637 := bstep (se 3 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 14158637 = 5309489) B5309489
theorem B2796353 : Blo 1242439 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B6294347 : Blo 1242439 6294347 := bstep (se 1 (by rfl) ⟨4720760, by rfl⟩ : syracuseStep 6294347 = 9441521) B9441521
theorem B23890787 : Blo 1242439 23890787 := bstep (se 1 (by rfl) ⟨17918090, by rfl⟩ : syracuseStep 23890787 = 35836181) B35836181
theorem B4721611 : Blo 1242439 4721611 := bstep (se 1 (by rfl) ⟨3541208, by rfl⟩ : syracuseStep 4721611 = 7082417) B7082417
theorem B2362355 : Blo 1242439 2362355 := bstep (se 1 (by rfl) ⟨1771766, by rfl⟩ : syracuseStep 2362355 = 3543533) B3543533
theorem B2796569 : Blo 1242439 2796569 := bstep (se 2 (by rfl) ⟨1048713, by rfl⟩ : syracuseStep 2796569 = 2097427) B2097427
theorem B11955235 : Blo 1242439 11955235 := bstep (se 1 (by rfl) ⟨8966426, by rfl⟩ : syracuseStep 11955235 = 17932853) B17932853
theorem B3148865 : Blo 1242439 3148865 := bstep (se 2 (by rfl) ⟨1180824, by rfl⟩ : syracuseStep 3148865 = 2361649) B2361649
theorem B2796659 : Blo 1242439 2796659 := bstep (se 1 (by rfl) ⟨2097494, by rfl⟩ : syracuseStep 2796659 = 4194989) B4194989
theorem B2796695 : Blo 1242439 2796695 := bstep (se 1 (by rfl) ⟨2097521, by rfl⟩ : syracuseStep 2796695 = 4195043) B4195043
theorem B4197527 : Blo 1242439 4197527 := bstep (se 1 (by rfl) ⟨3148145, by rfl⟩ : syracuseStep 4197527 = 6296291) B6296291
theorem B10628273 : Blo 1242439 10628273 := bstep (se 2 (by rfl) ⟨3985602, by rfl⟩ : syracuseStep 10628273 = 7971205) B7971205
theorem B4721885 : Blo 1242439 4721885 := bstep (se 3 (by rfl) ⟨885353, by rfl⟩ : syracuseStep 4721885 = 1770707) B1770707
theorem B72682757 : Blo 1242439 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B2796875 : Blo 1242439 2796875 := bstep (se 1 (by rfl) ⟨2097656, by rfl⟩ : syracuseStep 2796875 = 4195313) B4195313
theorem B2796929 : Blo 1242439 2796929 := bstep (se 2 (by rfl) ⟨1048848, by rfl⟩ : syracuseStep 2796929 = 2097697) B2097697
theorem B19410445 : Blo 1242439 19410445 := bstep (se 3 (by rfl) ⟨3639458, by rfl⟩ : syracuseStep 19410445 = 7278917) B7278917
theorem B2797145 : Blo 1242439 2797145 := bstep (se 2 (by rfl) ⟨1048929, by rfl⟩ : syracuseStep 2797145 = 2097859) B2097859
theorem B3149401 : Blo 1242439 3149401 := bstep (se 2 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 3149401 = 2362051) B2362051
theorem B2838131 : Blo 1242439 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B17927831 : Blo 1242439 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B2797235 : Blo 1242439 2797235 := bstep (se 1 (by rfl) ⟨2097926, by rfl⟩ : syracuseStep 2797235 = 4195853) B4195853
theorem B4198067 : Blo 1242439 4198067 := bstep (se 1 (by rfl) ⟨3148550, by rfl⟩ : syracuseStep 4198067 = 6297101) B6297101
theorem B2985665 : Blo 1242439 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B2797271 : Blo 1242439 2797271 := bstep (se 1 (by rfl) ⟨2097953, by rfl⟩ : syracuseStep 2797271 = 4195907) B4195907
theorem B10080065 : Blo 1242439 10080065 := bstep (se 2 (by rfl) ⟨3780024, by rfl⟩ : syracuseStep 10080065 = 7560049) B7560049
theorem B3542849 : Blo 1242439 3542849 := bstep (se 2 (by rfl) ⟨1328568, by rfl⟩ : syracuseStep 3542849 = 2657137) B2657137
theorem B2797451 : Blo 1242439 2797451 := bstep (se 1 (by rfl) ⟨2098088, by rfl⟩ : syracuseStep 2797451 = 4196177) B4196177
theorem B4722583 : Blo 1242439 4722583 := bstep (se 1 (by rfl) ⟨3541937, by rfl⟩ : syracuseStep 4722583 = 7083875) B7083875
theorem B5312429 : Blo 1242439 5312429 := bstep (se 3 (by rfl) ⟨996080, by rfl⟩ : syracuseStep 5312429 = 1992161) B1992161
theorem B2797505 : Blo 1242439 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B4198337 : Blo 1242439 4198337 := bstep (se 2 (by rfl) ⟨1574376, by rfl⟩ : syracuseStep 4198337 = 3148753) B3148753
theorem B1863755 : Blo 1242439 1863755 := bstep (se 1 (by rfl) ⟨1397816, by rfl⟩ : syracuseStep 1863755 = 2795633) B2795633
theorem B14004299 : Blo 1242439 14004299 := bstep (se 1 (by rfl) ⟨10503224, by rfl⟩ : syracuseStep 14004299 = 21006449) B21006449
theorem B1863767 : Blo 1242439 1863767 := bstep (se 1 (by rfl) ⟨1397825, by rfl⟩ : syracuseStep 1863767 = 2795651) B2795651
theorem B2240627 : Blo 1242439 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B1863833 : Blo 1242439 1863833 := bstep (se 2 (by rfl) ⟨698937, by rfl⟩ : syracuseStep 1863833 = 1397875) B1397875
theorem B2797721 : Blo 1242439 2797721 := bstep (se 2 (by rfl) ⟨1049145, by rfl⟩ : syracuseStep 2797721 = 2098291) B2098291
theorem B2797811 : Blo 1242439 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B1863947 : Blo 1242439 1863947 := bstep (se 1 (by rfl) ⟨1397960, by rfl⟩ : syracuseStep 1863947 = 2795921) B2795921
theorem B4788497 : Blo 1242439 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B1863959 : Blo 1242439 1863959 := bstep (se 1 (by rfl) ⟨1397969, by rfl⟩ : syracuseStep 1863959 = 2795939) B2795939
theorem B2797847 : Blo 1242439 2797847 := bstep (se 1 (by rfl) ⟨2098385, by rfl⟩ : syracuseStep 2797847 = 4196771) B4196771
theorem B1864025 : Blo 1242439 1864025 := bstep (se 2 (by rfl) ⟨699009, by rfl⟩ : syracuseStep 1864025 = 1398019) B1398019
theorem B3543385 : Blo 1242439 3543385 := bstep (se 2 (by rfl) ⟨1328769, by rfl⟩ : syracuseStep 3543385 = 2657539) B2657539
theorem B3985757 : Blo 1242439 3985757 := bstep (se 3 (by rfl) ⟨747329, by rfl⟩ : syracuseStep 3985757 = 1494659) B1494659
theorem B2691443 : Blo 1242439 2691443 := bstep (se 1 (by rfl) ⟨2018582, by rfl⟩ : syracuseStep 2691443 = 4037165) B4037165
theorem B1864139 : Blo 1242439 1864139 := bstep (se 1 (by rfl) ⟨1398104, by rfl⟩ : syracuseStep 1864139 = 2796209) B2796209
theorem B2798027 : Blo 1242439 2798027 := bstep (se 1 (by rfl) ⟨2098520, by rfl⟩ : syracuseStep 2798027 = 4197041) B4197041
theorem B1864151 : Blo 1242439 1864151 := bstep (se 1 (by rfl) ⟨1398113, by rfl⟩ : syracuseStep 1864151 = 2796227) B2796227
theorem B4198877 : Blo 1242439 4198877 := bstep (se 3 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 4198877 = 1574579) B1574579
theorem B2798081 : Blo 1242439 2798081 := bstep (se 2 (by rfl) ⟨1049280, by rfl⟩ : syracuseStep 2798081 = 2098561) B2098561
theorem B1864217 : Blo 1242439 1864217 := bstep (se 2 (by rfl) ⟨699081, by rfl⟩ : syracuseStep 1864217 = 1398163) B1398163
theorem B6296129 : Blo 1242439 6296129 := bstep (se 2 (by rfl) ⟨2361048, by rfl⟩ : syracuseStep 6296129 = 4722097) B4722097
theorem B5313113 : Blo 1242439 5313113 := bstep (se 2 (by rfl) ⟨1992417, by rfl⟩ : syracuseStep 5313113 = 3984835) B3984835
theorem B15323741 : Blo 1242439 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B1864331 : Blo 1242439 1864331 := bstep (se 1 (by rfl) ⟨1398248, by rfl⟩ : syracuseStep 1864331 = 2796497) B2796497
theorem B1864343 : Blo 1242439 1864343 := bstep (se 1 (by rfl) ⟨1398257, by rfl⟩ : syracuseStep 1864343 = 2796515) B2796515
theorem B4723373 : Blo 1242439 4723373 := bstep (se 3 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 4723373 = 1771265) B1771265
theorem B1864409 : Blo 1242439 1864409 := bstep (se 2 (by rfl) ⟨699153, by rfl⟩ : syracuseStep 1864409 = 1398307) B1398307
theorem B2798297 : Blo 1242439 2798297 := bstep (se 2 (by rfl) ⟨1049361, by rfl⟩ : syracuseStep 2798297 = 2098723) B2098723
theorem B3363545 : Blo 1242439 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B15938309 : Blo 1242439 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B2798387 : Blo 1242439 2798387 := bstep (se 1 (by rfl) ⟨2098790, by rfl⟩ : syracuseStep 2798387 = 4197581) B4197581
theorem B1864523 : Blo 1242439 1864523 := bstep (se 1 (by rfl) ⟨1398392, by rfl⟩ : syracuseStep 1864523 = 2796785) B2796785
theorem B1864535 : Blo 1242439 1864535 := bstep (se 1 (by rfl) ⟨1398401, by rfl⟩ : syracuseStep 1864535 = 2796803) B2796803
theorem B2798423 : Blo 1242439 2798423 := bstep (se 1 (by rfl) ⟨2098817, by rfl⟩ : syracuseStep 2798423 = 4197635) B4197635
theorem B1864601 : Blo 1242439 1864601 := bstep (se 2 (by rfl) ⟨699225, by rfl⟩ : syracuseStep 1864601 = 1398451) B1398451
theorem B2520065 : Blo 1242439 2520065 := bstep (se 2 (by rfl) ⟨945024, by rfl⟩ : syracuseStep 2520065 = 1890049) B1890049
theorem B1864715 : Blo 1242439 1864715 := bstep (se 1 (by rfl) ⟨1398536, by rfl⟩ : syracuseStep 1864715 = 2797073) B2797073
theorem B2798603 : Blo 1242439 2798603 := bstep (se 1 (by rfl) ⟨2098952, by rfl⟩ : syracuseStep 2798603 = 4197905) B4197905
theorem B7173137 : Blo 1242439 7173137 := bstep (se 2 (by rfl) ⟨2689926, by rfl⟩ : syracuseStep 7173137 = 5379853) B5379853
theorem B1864727 : Blo 1242439 1864727 := bstep (se 1 (by rfl) ⟨1398545, by rfl⟩ : syracuseStep 1864727 = 2797091) B2797091
theorem B1397803 : Blo 1242439 1397803 := bstep (se 1 (by rfl) ⟨1048352, by rfl⟩ : syracuseStep 1397803 = 2096705) B2096705
theorem B2798657 : Blo 1242439 2798657 := bstep (se 2 (by rfl) ⟨1049496, by rfl⟩ : syracuseStep 2798657 = 2098993) B2098993
theorem B1864793 : Blo 1242439 1864793 := bstep (se 2 (by rfl) ⟨699297, by rfl⟩ : syracuseStep 1864793 = 1398595) B1398595
theorem B1397911 : Blo 1242439 1397911 := bstep (se 1 (by rfl) ⟨1048433, by rfl⟩ : syracuseStep 1397911 = 2096867) B2096867
theorem B1864907 : Blo 1242439 1864907 := bstep (se 1 (by rfl) ⟨1398680, by rfl⟩ : syracuseStep 1864907 = 2797361) B2797361
theorem B1864919 : Blo 1242439 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B1864985 : Blo 1242439 1864985 := bstep (se 2 (by rfl) ⟨699369, by rfl⟩ : syracuseStep 1864985 = 1398739) B1398739
theorem B2798873 : Blo 1242439 2798873 := bstep (se 2 (by rfl) ⟨1049577, by rfl⟩ : syracuseStep 2798873 = 2099155) B2099155
theorem B1242443 : Blo 1242439 1242443 := bstep (se 1 (by rfl) ⟨931832, by rfl⟩ : syracuseStep 1242443 = 1863665) B1863665
theorem B1398091 : Blo 1242439 1398091 := bstep (se 1 (by rfl) ⟨1048568, by rfl⟩ : syracuseStep 1398091 = 2097137) B2097137
theorem B1242455 : Blo 1242439 1242455 := bstep (se 1 (by rfl) ⟨931841, by rfl⟩ : syracuseStep 1242455 = 1863683) B1863683
theorem B1242475 : Blo 1242439 1242475 := bstep (se 1 (by rfl) ⟨931856, by rfl⟩ : syracuseStep 1242475 = 1863713) B1863713
theorem B2798963 : Blo 1242439 2798963 := bstep (se 1 (by rfl) ⟨2099222, by rfl⟩ : syracuseStep 2798963 = 4198445) B4198445
theorem B1242487 : Blo 1242439 1242487 := bstep (se 1 (by rfl) ⟨931865, by rfl⟩ : syracuseStep 1242487 = 1863731) B1863731
theorem B7968131 : Blo 1242439 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1242507 : Blo 1242439 1242507 := bstep (se 1 (by rfl) ⟨931880, by rfl⟩ : syracuseStep 1242507 = 1863761) B1863761
theorem B1865099 : Blo 1242439 1865099 := bstep (se 1 (by rfl) ⟨1398824, by rfl⟩ : syracuseStep 1865099 = 2797649) B2797649
theorem B1242519 : Blo 1242439 1242519 := bstep (se 1 (by rfl) ⟨931889, by rfl⟩ : syracuseStep 1242519 = 1863779) B1863779
theorem B1865111 : Blo 1242439 1865111 := bstep (se 1 (by rfl) ⟨1398833, by rfl⟩ : syracuseStep 1865111 = 2797667) B2797667
theorem B2798999 : Blo 1242439 2798999 := bstep (se 1 (by rfl) ⟨2099249, by rfl⟩ : syracuseStep 2798999 = 4198499) B4198499
theorem B1242539 : Blo 1242439 1242539 := bstep (se 1 (by rfl) ⟨931904, by rfl⟩ : syracuseStep 1242539 = 1863809) B1863809
theorem B1242551 : Blo 1242439 1242551 := bstep (se 1 (by rfl) ⟨931913, by rfl⟩ : syracuseStep 1242551 = 1863827) B1863827
theorem B1398199 : Blo 1242439 1398199 := bstep (se 1 (by rfl) ⟨1048649, by rfl⟩ : syracuseStep 1398199 = 2097299) B2097299
theorem B1242571 : Blo 1242439 1242571 := bstep (se 1 (by rfl) ⟨931928, by rfl⟩ : syracuseStep 1242571 = 1863857) B1863857
theorem B1242583 : Blo 1242439 1242583 := bstep (se 1 (by rfl) ⟨931937, by rfl⟩ : syracuseStep 1242583 = 1863875) B1863875
theorem B1865177 : Blo 1242439 1865177 := bstep (se 2 (by rfl) ⟨699441, by rfl⟩ : syracuseStep 1865177 = 1398883) B1398883
theorem B1242603 : Blo 1242439 1242603 := bstep (se 1 (by rfl) ⟨931952, by rfl⟩ : syracuseStep 1242603 = 1863905) B1863905
theorem B1242615 : Blo 1242439 1242615 := bstep (se 1 (by rfl) ⟨931961, by rfl⟩ : syracuseStep 1242615 = 1863923) B1863923
theorem B1242635 : Blo 1242439 1242635 := bstep (se 1 (by rfl) ⟨931976, by rfl⟩ : syracuseStep 1242635 = 1863953) B1863953
theorem B1242647 : Blo 1242439 1242647 := bstep (se 1 (by rfl) ⟨931985, by rfl⟩ : syracuseStep 1242647 = 1863971) B1863971
theorem B1242667 : Blo 1242439 1242667 := bstep (se 1 (by rfl) ⟨932000, by rfl⟩ : syracuseStep 1242667 = 1864001) B1864001
theorem B1242679 : Blo 1242439 1242679 := bstep (se 1 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 1242679 = 1864019) B1864019
theorem B1242699 : Blo 1242439 1242699 := bstep (se 1 (by rfl) ⟨932024, by rfl⟩ : syracuseStep 1242699 = 1864049) B1864049
theorem B1865291 : Blo 1242439 1865291 := bstep (se 1 (by rfl) ⟨1398968, by rfl⟩ : syracuseStep 1865291 = 2797937) B2797937
theorem B2799179 : Blo 1242439 2799179 := bstep (se 1 (by rfl) ⟨2099384, by rfl⟩ : syracuseStep 2799179 = 4198769) B4198769
theorem B1242711 : Blo 1242439 1242711 := bstep (se 1 (by rfl) ⟨932033, by rfl⟩ : syracuseStep 1242711 = 1864067) B1864067
theorem B1865303 : Blo 1242439 1865303 := bstep (se 1 (by rfl) ⟨1398977, by rfl⟩ : syracuseStep 1865303 = 2797955) B2797955
theorem B1242731 : Blo 1242439 1242731 := bstep (se 1 (by rfl) ⟨932048, by rfl⟩ : syracuseStep 1242731 = 1864097) B1864097
theorem B1398379 : Blo 1242439 1398379 := bstep (se 1 (by rfl) ⟨1048784, by rfl⟩ : syracuseStep 1398379 = 2097569) B2097569
theorem B1242743 : Blo 1242439 1242743 := bstep (se 1 (by rfl) ⟨932057, by rfl⟩ : syracuseStep 1242743 = 1864115) B1864115
theorem B2799233 : Blo 1242439 2799233 := bstep (se 2 (by rfl) ⟨1049712, by rfl⟩ : syracuseStep 2799233 = 2099425) B2099425
theorem B10090115 : Blo 1242439 10090115 := bstep (se 1 (by rfl) ⟨7567586, by rfl⟩ : syracuseStep 10090115 = 15135173) B15135173
theorem B1242763 : Blo 1242439 1242763 := bstep (se 1 (by rfl) ⟨932072, by rfl⟩ : syracuseStep 1242763 = 1864145) B1864145
theorem B4478615 : Blo 1242439 4478615 := bstep (se 1 (by rfl) ⟨3358961, by rfl⟩ : syracuseStep 4478615 = 6717923) B6717923
theorem B1242775 : Blo 1242439 1242775 := bstep (se 1 (by rfl) ⟨932081, by rfl⟩ : syracuseStep 1242775 = 1864163) B1864163
theorem B1865369 : Blo 1242439 1865369 := bstep (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) B1399027
theorem B1242795 : Blo 1242439 1242795 := bstep (se 1 (by rfl) ⟨932096, by rfl⟩ : syracuseStep 1242795 = 1864193) B1864193
theorem B3782323 : Blo 1242439 3782323 := bstep (se 1 (by rfl) ⟨2836742, by rfl⟩ : syracuseStep 3782323 = 5673485) B5673485
theorem B1242807 : Blo 1242439 1242807 := bstep (se 1 (by rfl) ⟨932105, by rfl⟩ : syracuseStep 1242807 = 1864211) B1864211
theorem B1242827 : Blo 1242439 1242827 := bstep (se 1 (by rfl) ⟨932120, by rfl⟩ : syracuseStep 1242827 = 1864241) B1864241
theorem B48420557 : Blo 1242439 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B1242839 : Blo 1242439 1242839 := bstep (se 1 (by rfl) ⟨932129, by rfl⟩ : syracuseStep 1242839 = 1864259) B1864259
theorem B1398487 : Blo 1242439 1398487 := bstep (se 1 (by rfl) ⟨1048865, by rfl⟩ : syracuseStep 1398487 = 2097731) B2097731
theorem B1242859 : Blo 1242439 1242859 := bstep (se 1 (by rfl) ⟨932144, by rfl⟩ : syracuseStep 1242859 = 1864289) B1864289
theorem B1242871 : Blo 1242439 1242871 := bstep (se 1 (by rfl) ⟨932153, by rfl⟩ : syracuseStep 1242871 = 1864307) B1864307
theorem B1242891 : Blo 1242439 1242891 := bstep (se 1 (by rfl) ⟨932168, by rfl⟩ : syracuseStep 1242891 = 1864337) B1864337
theorem B1865483 : Blo 1242439 1865483 := bstep (se 1 (by rfl) ⟨1399112, by rfl⟩ : syracuseStep 1865483 = 2798225) B2798225
theorem B1242903 : Blo 1242439 1242903 := bstep (se 1 (by rfl) ⟨932177, by rfl⟩ : syracuseStep 1242903 = 1864355) B1864355
theorem B1865495 : Blo 1242439 1865495 := bstep (se 1 (by rfl) ⟨1399121, by rfl⟩ : syracuseStep 1865495 = 2798243) B2798243
theorem B4544279 : Blo 1242439 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B1242923 : Blo 1242439 1242923 := bstep (se 1 (by rfl) ⟨932192, by rfl⟩ : syracuseStep 1242923 = 1864385) B1864385
theorem B1242935 : Blo 1242439 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B11949889 : Blo 1242439 11949889 := bstep (se 2 (by rfl) ⟨4481208, by rfl⟩ : syracuseStep 11949889 = 8962417) B8962417
theorem B1242955 : Blo 1242439 1242955 := bstep (se 1 (by rfl) ⟨932216, by rfl⟩ : syracuseStep 1242955 = 1864433) B1864433
theorem B1242967 : Blo 1242439 1242967 := bstep (se 1 (by rfl) ⟨932225, by rfl⟩ : syracuseStep 1242967 = 1864451) B1864451
theorem B1865561 : Blo 1242439 1865561 := bstep (se 2 (by rfl) ⟨699585, by rfl⟩ : syracuseStep 1865561 = 1399171) B1399171
theorem B2799449 : Blo 1242439 2799449 := bstep (se 2 (by rfl) ⟨1049793, by rfl⟩ : syracuseStep 2799449 = 2099587) B2099587
theorem B1242987 : Blo 1242439 1242987 := bstep (se 1 (by rfl) ⟨932240, by rfl⟩ : syracuseStep 1242987 = 1864481) B1864481
theorem B1242999 : Blo 1242439 1242999 := bstep (se 1 (by rfl) ⟨932249, by rfl⟩ : syracuseStep 1242999 = 1864499) B1864499
theorem B1243019 : Blo 1242439 1243019 := bstep (se 1 (by rfl) ⟨932264, by rfl⟩ : syracuseStep 1243019 = 1864529) B1864529
theorem B1398667 : Blo 1242439 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B1243031 : Blo 1242439 1243031 := bstep (se 1 (by rfl) ⟨932273, by rfl⟩ : syracuseStep 1243031 = 1864547) B1864547
theorem B1243051 : Blo 1242439 1243051 := bstep (se 1 (by rfl) ⟨932288, by rfl⟩ : syracuseStep 1243051 = 1864577) B1864577
theorem B2799539 : Blo 1242439 2799539 := bstep (se 1 (by rfl) ⟨2099654, by rfl⟩ : syracuseStep 2799539 = 4199309) B4199309
theorem B1243063 : Blo 1242439 1243063 := bstep (se 1 (by rfl) ⟨932297, by rfl⟩ : syracuseStep 1243063 = 1864595) B1864595
theorem B1243083 : Blo 1242439 1243083 := bstep (se 1 (by rfl) ⟨932312, by rfl⟩ : syracuseStep 1243083 = 1864625) B1864625
theorem B1865675 : Blo 1242439 1865675 := bstep (se 1 (by rfl) ⟨1399256, by rfl⟩ : syracuseStep 1865675 = 2798513) B2798513
theorem B1243095 : Blo 1242439 1243095 := bstep (se 1 (by rfl) ⟨932321, by rfl⟩ : syracuseStep 1243095 = 1864643) B1864643
theorem B1865687 : Blo 1242439 1865687 := bstep (se 1 (by rfl) ⟨1399265, by rfl⟩ : syracuseStep 1865687 = 2798531) B2798531
theorem B2799575 : Blo 1242439 2799575 := bstep (se 1 (by rfl) ⟨2099681, by rfl⟩ : syracuseStep 2799575 = 4199363) B4199363
theorem B1243115 : Blo 1242439 1243115 := bstep (se 1 (by rfl) ⟨932336, by rfl⟩ : syracuseStep 1243115 = 1864673) B1864673
theorem B1243127 : Blo 1242439 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B1398775 : Blo 1242439 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B1243147 : Blo 1242439 1243147 := bstep (se 1 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 1243147 = 1864721) B1864721
theorem B1243159 : Blo 1242439 1243159 := bstep (se 1 (by rfl) ⟨932369, by rfl⟩ : syracuseStep 1243159 = 1864739) B1864739
theorem B1865753 : Blo 1242439 1865753 := bstep (se 2 (by rfl) ⟨699657, by rfl⟩ : syracuseStep 1865753 = 1399315) B1399315
theorem B1243179 : Blo 1242439 1243179 := bstep (se 1 (by rfl) ⟨932384, by rfl⟩ : syracuseStep 1243179 = 1864769) B1864769
theorem B1243191 : Blo 1242439 1243191 := bstep (se 1 (by rfl) ⟨932393, by rfl⟩ : syracuseStep 1243191 = 1864787) B1864787
theorem B4724801 : Blo 1242439 4724801 := bstep (se 2 (by rfl) ⟨1771800, by rfl⟩ : syracuseStep 4724801 = 3543601) B3543601
theorem B1243211 : Blo 1242439 1243211 := bstep (se 1 (by rfl) ⟨932408, by rfl⟩ : syracuseStep 1243211 = 1864817) B1864817
theorem B1243223 : Blo 1242439 1243223 := bstep (se 1 (by rfl) ⟨932417, by rfl⟩ : syracuseStep 1243223 = 1864835) B1864835
theorem B1243243 : Blo 1242439 1243243 := bstep (se 1 (by rfl) ⟨932432, by rfl⟩ : syracuseStep 1243243 = 1864865) B1864865
theorem B1243255 : Blo 1242439 1243255 := bstep (se 1 (by rfl) ⟨932441, by rfl⟩ : syracuseStep 1243255 = 1864883) B1864883
theorem B1243275 : Blo 1242439 1243275 := bstep (se 1 (by rfl) ⟨932456, by rfl⟩ : syracuseStep 1243275 = 1864913) B1864913
theorem B1865867 : Blo 1242439 1865867 := bstep (se 1 (by rfl) ⟨1399400, by rfl⟩ : syracuseStep 1865867 = 2798801) B2798801
theorem B2799755 : Blo 1242439 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B1243287 : Blo 1242439 1243287 := bstep (se 1 (by rfl) ⟨932465, by rfl⟩ : syracuseStep 1243287 = 1864931) B1864931
theorem B1865879 : Blo 1242439 1865879 := bstep (se 1 (by rfl) ⟨1399409, by rfl⟩ : syracuseStep 1865879 = 2798819) B2798819
theorem B1243307 : Blo 1242439 1243307 := bstep (se 1 (by rfl) ⟨932480, by rfl⟩ : syracuseStep 1243307 = 1864961) B1864961
theorem B1398955 : Blo 1242439 1398955 := bstep (se 1 (by rfl) ⟨1049216, by rfl⟩ : syracuseStep 1398955 = 2098433) B2098433
theorem B1243319 : Blo 1242439 1243319 := bstep (se 1 (by rfl) ⟨932489, by rfl⟩ : syracuseStep 1243319 = 1864979) B1864979
theorem B2799809 : Blo 1242439 2799809 := bstep (se 2 (by rfl) ⟨1049928, by rfl⟩ : syracuseStep 2799809 = 2099857) B2099857
theorem B1243339 : Blo 1242439 1243339 := bstep (se 1 (by rfl) ⟨932504, by rfl⟩ : syracuseStep 1243339 = 1865009) B1865009
theorem B1243351 : Blo 1242439 1243351 := bstep (se 1 (by rfl) ⟨932513, by rfl⟩ : syracuseStep 1243351 = 1865027) B1865027
theorem B1865945 : Blo 1242439 1865945 := bstep (se 2 (by rfl) ⟨699729, by rfl⟩ : syracuseStep 1865945 = 1399459) B1399459
theorem B1243371 : Blo 1242439 1243371 := bstep (se 1 (by rfl) ⟨932528, by rfl⟩ : syracuseStep 1243371 = 1865057) B1865057
theorem B1243383 : Blo 1242439 1243383 := bstep (se 1 (by rfl) ⟨932537, by rfl⟩ : syracuseStep 1243383 = 1865075) B1865075
theorem B1243403 : Blo 1242439 1243403 := bstep (se 1 (by rfl) ⟨932552, by rfl⟩ : syracuseStep 1243403 = 1865105) B1865105
theorem B1243415 : Blo 1242439 1243415 := bstep (se 1 (by rfl) ⟨932561, by rfl⟩ : syracuseStep 1243415 = 1865123) B1865123
theorem B1399063 : Blo 1242439 1399063 := bstep (se 1 (by rfl) ⟨1049297, by rfl⟩ : syracuseStep 1399063 = 2098595) B2098595
theorem B1243435 : Blo 1242439 1243435 := bstep (se 1 (by rfl) ⟨932576, by rfl⟩ : syracuseStep 1243435 = 1865153) B1865153
theorem B19151149 : Blo 1242439 19151149 := bstep (se 3 (by rfl) ⟨3590840, by rfl⟩ : syracuseStep 19151149 = 7181681) B7181681
theorem B1243447 : Blo 1242439 1243447 := bstep (se 1 (by rfl) ⟨932585, by rfl⟩ : syracuseStep 1243447 = 1865171) B1865171
theorem B1243467 : Blo 1242439 1243467 := bstep (se 1 (by rfl) ⟨932600, by rfl⟩ : syracuseStep 1243467 = 1865201) B1865201
theorem B1866059 : Blo 1242439 1866059 := bstep (se 1 (by rfl) ⟨1399544, by rfl⟩ : syracuseStep 1866059 = 2799089) B2799089
theorem B1243479 : Blo 1242439 1243479 := bstep (se 1 (by rfl) ⟨932609, by rfl⟩ : syracuseStep 1243479 = 1865219) B1865219
theorem B1866071 : Blo 1242439 1866071 := bstep (se 1 (by rfl) ⟨1399553, by rfl⟩ : syracuseStep 1866071 = 2799107) B2799107
theorem B2988377 : Blo 1242439 2988377 := bstep (se 2 (by rfl) ⟨1120641, by rfl⟩ : syracuseStep 2988377 = 2241283) B2241283
theorem B1243499 : Blo 1242439 1243499 := bstep (se 1 (by rfl) ⟨932624, by rfl⟩ : syracuseStep 1243499 = 1865249) B1865249
theorem B2521459 : Blo 1242439 2521459 := bstep (se 1 (by rfl) ⟨1891094, by rfl⟩ : syracuseStep 2521459 = 3782189) B3782189
theorem B1243511 : Blo 1242439 1243511 := bstep (se 1 (by rfl) ⟨932633, by rfl⟩ : syracuseStep 1243511 = 1865267) B1865267
theorem B1243531 : Blo 1242439 1243531 := bstep (se 1 (by rfl) ⟨932648, by rfl⟩ : syracuseStep 1243531 = 1865297) B1865297
theorem B1243543 : Blo 1242439 1243543 := bstep (se 1 (by rfl) ⟨932657, by rfl⟩ : syracuseStep 1243543 = 1865315) B1865315
theorem B1866137 : Blo 1242439 1866137 := bstep (se 2 (by rfl) ⟨699801, by rfl⟩ : syracuseStep 1866137 = 1399603) B1399603
theorem B1243563 : Blo 1242439 1243563 := bstep (se 1 (by rfl) ⟨932672, by rfl⟩ : syracuseStep 1243563 = 1865345) B1865345
theorem B1243575 : Blo 1242439 1243575 := bstep (se 1 (by rfl) ⟨932681, by rfl⟩ : syracuseStep 1243575 = 1865363) B1865363
theorem B1243595 : Blo 1242439 1243595 := bstep (se 1 (by rfl) ⟨932696, by rfl⟩ : syracuseStep 1243595 = 1865393) B1865393
theorem B1399243 : Blo 1242439 1399243 := bstep (se 1 (by rfl) ⟨1049432, by rfl⟩ : syracuseStep 1399243 = 2098865) B2098865
theorem B1243607 : Blo 1242439 1243607 := bstep (se 1 (by rfl) ⟨932705, by rfl⟩ : syracuseStep 1243607 = 1865411) B1865411
theorem B6298073 : Blo 1242439 6298073 := bstep (se 2 (by rfl) ⟨2361777, by rfl⟩ : syracuseStep 6298073 = 4723555) B4723555
theorem B1243627 : Blo 1242439 1243627 := bstep (se 1 (by rfl) ⟨932720, by rfl⟩ : syracuseStep 1243627 = 1865441) B1865441
theorem B1243639 : Blo 1242439 1243639 := bstep (se 1 (by rfl) ⟨932729, by rfl⟩ : syracuseStep 1243639 = 1865459) B1865459
theorem B1243659 : Blo 1242439 1243659 := bstep (se 1 (by rfl) ⟨932744, by rfl⟩ : syracuseStep 1243659 = 1865489) B1865489
theorem B1866251 : Blo 1242439 1866251 := bstep (se 1 (by rfl) ⟨1399688, by rfl⟩ : syracuseStep 1866251 = 2799377) B2799377
theorem B45382157 : Blo 1242439 45382157 := bstep (se 3 (by rfl) ⟨8509154, by rfl⟩ : syracuseStep 45382157 = 17018309) B17018309
theorem B5970449 : Blo 1242439 5970449 := bstep (se 2 (by rfl) ⟨2238918, by rfl⟩ : syracuseStep 5970449 = 4477837) B4477837
theorem B1243671 : Blo 1242439 1243671 := bstep (se 1 (by rfl) ⟨932753, by rfl⟩ : syracuseStep 1243671 = 1865507) B1865507
theorem B1866263 : Blo 1242439 1866263 := bstep (se 1 (by rfl) ⟨1399697, by rfl⟩ : syracuseStep 1866263 = 2799395) B2799395
theorem B1243691 : Blo 1242439 1243691 := bstep (se 1 (by rfl) ⟨932768, by rfl⟩ : syracuseStep 1243691 = 1865537) B1865537
theorem B1243703 : Blo 1242439 1243703 := bstep (se 1 (by rfl) ⟨932777, by rfl⟩ : syracuseStep 1243703 = 1865555) B1865555
theorem B1399351 : Blo 1242439 1399351 := bstep (se 1 (by rfl) ⟨1049513, by rfl⟩ : syracuseStep 1399351 = 2099027) B2099027
theorem B5044801 : Blo 1242439 5044801 := bstep (se 2 (by rfl) ⟨1891800, by rfl⟩ : syracuseStep 5044801 = 3783601) B3783601
theorem B1243723 : Blo 1242439 1243723 := bstep (se 1 (by rfl) ⟨932792, by rfl⟩ : syracuseStep 1243723 = 1865585) B1865585
theorem B1243735 : Blo 1242439 1243735 := bstep (se 1 (by rfl) ⟨932801, by rfl⟩ : syracuseStep 1243735 = 1865603) B1865603
theorem B1866329 : Blo 1242439 1866329 := bstep (se 2 (by rfl) ⟨699873, by rfl⟩ : syracuseStep 1866329 = 1399747) B1399747
theorem B1243755 : Blo 1242439 1243755 := bstep (se 1 (by rfl) ⟨932816, by rfl⟩ : syracuseStep 1243755 = 1865633) B1865633
theorem B1243767 : Blo 1242439 1243767 := bstep (se 1 (by rfl) ⟨932825, by rfl⟩ : syracuseStep 1243767 = 1865651) B1865651
theorem B1243787 : Blo 1242439 1243787 := bstep (se 1 (by rfl) ⟨932840, by rfl⟩ : syracuseStep 1243787 = 1865681) B1865681
theorem B1243799 : Blo 1242439 1243799 := bstep (se 1 (by rfl) ⟨932849, by rfl⟩ : syracuseStep 1243799 = 1865699) B1865699
theorem B1243819 : Blo 1242439 1243819 := bstep (se 1 (by rfl) ⟨932864, by rfl⟩ : syracuseStep 1243819 = 1865729) B1865729
theorem B1243831 : Blo 1242439 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B1243851 : Blo 1242439 1243851 := bstep (se 1 (by rfl) ⟨932888, by rfl⟩ : syracuseStep 1243851 = 1865777) B1865777
theorem B1866443 : Blo 1242439 1866443 := bstep (se 1 (by rfl) ⟨1399832, by rfl⟩ : syracuseStep 1866443 = 2799665) B2799665
theorem B1243863 : Blo 1242439 1243863 := bstep (se 1 (by rfl) ⟨932897, by rfl⟩ : syracuseStep 1243863 = 1865795) B1865795
theorem B1866455 : Blo 1242439 1866455 := bstep (se 1 (by rfl) ⟨1399841, by rfl⟩ : syracuseStep 1866455 = 2799683) B2799683
theorem B1243883 : Blo 1242439 1243883 := bstep (se 1 (by rfl) ⟨932912, by rfl⟩ : syracuseStep 1243883 = 1865825) B1865825
theorem B1399531 : Blo 1242439 1399531 := bstep (se 1 (by rfl) ⟨1049648, by rfl⟩ : syracuseStep 1399531 = 2099297) B2099297
theorem B1243895 : Blo 1242439 1243895 := bstep (se 1 (by rfl) ⟨932921, by rfl⟩ : syracuseStep 1243895 = 1865843) B1865843
theorem B1243915 : Blo 1242439 1243915 := bstep (se 1 (by rfl) ⟨932936, by rfl⟩ : syracuseStep 1243915 = 1865873) B1865873
theorem B1243927 : Blo 1242439 1243927 := bstep (se 1 (by rfl) ⟨932945, by rfl⟩ : syracuseStep 1243927 = 1865891) B1865891
theorem B1866521 : Blo 1242439 1866521 := bstep (se 2 (by rfl) ⟨699945, by rfl⟩ : syracuseStep 1866521 = 1399891) B1399891
theorem B1243947 : Blo 1242439 1243947 := bstep (se 1 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 1243947 = 1865921) B1865921
theorem B1243959 : Blo 1242439 1243959 := bstep (se 1 (by rfl) ⟨932969, by rfl⟩ : syracuseStep 1243959 = 1865939) B1865939
theorem B1243979 : Blo 1242439 1243979 := bstep (se 1 (by rfl) ⟨932984, by rfl⟩ : syracuseStep 1243979 = 1865969) B1865969
theorem B1243991 : Blo 1242439 1243991 := bstep (se 1 (by rfl) ⟨932993, by rfl⟩ : syracuseStep 1243991 = 1865987) B1865987
theorem B1399639 : Blo 1242439 1399639 := bstep (se 1 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 1399639 = 2099459) B2099459
theorem B23919461 : Blo 1242439 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B1244011 : Blo 1242439 1244011 := bstep (se 1 (by rfl) ⟨933008, by rfl⟩ : syracuseStep 1244011 = 1866017) B1866017
theorem B1244023 : Blo 1242439 1244023 := bstep (se 1 (by rfl) ⟨933017, by rfl⟩ : syracuseStep 1244023 = 1866035) B1866035
theorem B1244043 : Blo 1242439 1244043 := bstep (se 1 (by rfl) ⟨933032, by rfl⟩ : syracuseStep 1244043 = 1866065) B1866065
theorem B1866635 : Blo 1242439 1866635 := bstep (se 1 (by rfl) ⟨1399976, by rfl⟩ : syracuseStep 1866635 = 2799953) B2799953
theorem B1244055 : Blo 1242439 1244055 := bstep (se 1 (by rfl) ⟨933041, by rfl⟩ : syracuseStep 1244055 = 1866083) B1866083
theorem B1866647 : Blo 1242439 1866647 := bstep (se 1 (by rfl) ⟨1399985, by rfl⟩ : syracuseStep 1866647 = 2799971) B2799971
theorem B1244075 : Blo 1242439 1244075 := bstep (se 1 (by rfl) ⟨933056, by rfl⟩ : syracuseStep 1244075 = 1866113) B1866113
theorem B1244087 : Blo 1242439 1244087 := bstep (se 1 (by rfl) ⟨933065, by rfl⟩ : syracuseStep 1244087 = 1866131) B1866131
theorem B1244107 : Blo 1242439 1244107 := bstep (se 1 (by rfl) ⟨933080, by rfl⟩ : syracuseStep 1244107 = 1866161) B1866161
theorem B1244119 : Blo 1242439 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B1891289 : Blo 1242439 1891289 := bstep (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) B1418467
theorem B4037597 : Blo 1242439 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B1244139 : Blo 1242439 1244139 := bstep (se 1 (by rfl) ⟨933104, by rfl⟩ : syracuseStep 1244139 = 1866209) B1866209
theorem B1244151 : Blo 1242439 1244151 := bstep (se 1 (by rfl) ⟨933113, by rfl⟩ : syracuseStep 1244151 = 1866227) B1866227
theorem B8969221 : Blo 1242439 8969221 := bstep (se 4 (by rfl) ⟨840864, by rfl⟩ : syracuseStep 8969221 = 1681729) B1681729
theorem B1244171 : Blo 1242439 1244171 := bstep (se 1 (by rfl) ⟨933128, by rfl⟩ : syracuseStep 1244171 = 1866257) B1866257
theorem B1399819 : Blo 1242439 1399819 := bstep (se 1 (by rfl) ⟨1049864, by rfl⟩ : syracuseStep 1399819 = 2099729) B2099729
theorem B1244183 : Blo 1242439 1244183 := bstep (se 1 (by rfl) ⟨933137, by rfl⟩ : syracuseStep 1244183 = 1866275) B1866275
theorem B1244203 : Blo 1242439 1244203 := bstep (se 1 (by rfl) ⟨933152, by rfl⟩ : syracuseStep 1244203 = 1866305) B1866305
theorem B1244215 : Blo 1242439 1244215 := bstep (se 1 (by rfl) ⟨933161, by rfl⟩ : syracuseStep 1244215 = 1866323) B1866323
theorem B1244235 : Blo 1242439 1244235 := bstep (se 1 (by rfl) ⟨933176, by rfl⟩ : syracuseStep 1244235 = 1866353) B1866353
theorem B1244247 : Blo 1242439 1244247 := bstep (se 1 (by rfl) ⟨933185, by rfl⟩ : syracuseStep 1244247 = 1866371) B1866371
theorem B4193369 : Blo 1242439 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B1244267 : Blo 1242439 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B1244279 : Blo 1242439 1244279 := bstep (se 1 (by rfl) ⟨933209, by rfl⟩ : syracuseStep 1244279 = 1866419) B1866419
theorem B1399927 : Blo 1242439 1399927 := bstep (se 1 (by rfl) ⟨1049945, by rfl⟩ : syracuseStep 1399927 = 2099891) B2099891
theorem B1244299 : Blo 1242439 1244299 := bstep (se 1 (by rfl) ⟨933224, by rfl⟩ : syracuseStep 1244299 = 1866449) B1866449
theorem B1244311 : Blo 1242439 1244311 := bstep (se 1 (by rfl) ⟨933233, by rfl⟩ : syracuseStep 1244311 = 1866467) B1866467
theorem B1244331 : Blo 1242439 1244331 := bstep (se 1 (by rfl) ⟨933248, by rfl⟩ : syracuseStep 1244331 = 1866497) B1866497
theorem B1244343 : Blo 1242439 1244343 := bstep (se 1 (by rfl) ⟨933257, by rfl⟩ : syracuseStep 1244343 = 1866515) B1866515
theorem B1244363 : Blo 1242439 1244363 := bstep (se 1 (by rfl) ⟨933272, by rfl⟩ : syracuseStep 1244363 = 1866545) B1866545
theorem B1244375 : Blo 1242439 1244375 := bstep (se 1 (by rfl) ⟨933281, by rfl⟩ : syracuseStep 1244375 = 1866563) B1866563
theorem B1244395 : Blo 1242439 1244395 := bstep (se 1 (by rfl) ⟨933296, by rfl⟩ : syracuseStep 1244395 = 1866593) B1866593
theorem B1244407 : Blo 1242439 1244407 := bstep (se 1 (by rfl) ⟨933305, by rfl⟩ : syracuseStep 1244407 = 1866611) B1866611
theorem B1244427 : Blo 1242439 1244427 := bstep (se 1 (by rfl) ⟨933320, by rfl⟩ : syracuseStep 1244427 = 1866641) B1866641
theorem B1244439 : Blo 1242439 1244439 := bstep (se 1 (by rfl) ⟨933329, by rfl⟩ : syracuseStep 1244439 = 1866659) B1866659
theorem B5307713 : Blo 1242439 5307713 := bstep (se 2 (by rfl) ⟨1990392, by rfl⟩ : syracuseStep 5307713 = 3980785) B3980785
theorem B2522497 : Blo 1242439 2522497 := bstep (se 2 (by rfl) ⟨945936, by rfl⟩ : syracuseStep 2522497 = 1891873) B1891873
theorem B6725015 : Blo 1242439 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B4717997 : Blo 1242439 4717997 := bstep (se 3 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 4717997 = 1769249) B1769249
theorem B3145139 : Blo 1242439 3145139 := bstep (se 1 (by rfl) ⟨2358854, by rfl⟩ : syracuseStep 3145139 = 4717709) B4717709
theorem B4718027 : Blo 1242439 4718027 := bstep (se 1 (by rfl) ⟨3538520, by rfl⟩ : syracuseStep 4718027 = 7077041) B7077041
theorem B2522611 : Blo 1242439 2522611 := bstep (se 1 (by rfl) ⟨1891958, by rfl⟩ : syracuseStep 2522611 = 3783917) B3783917
theorem B2096651 : Blo 1242439 2096651 := bstep (se 1 (by rfl) ⟨1572488, by rfl⟩ : syracuseStep 2096651 = 3144977) B3144977
theorem B11959883 : Blo 1242439 11959883 := bstep (se 1 (by rfl) ⟨8969912, by rfl⟩ : syracuseStep 11959883 = 17939825) B17939825
theorem B2096779 : Blo 1242439 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B5308055 : Blo 1242439 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B11337367 : Blo 1242439 11337367 := bstep (se 1 (by rfl) ⟨8503025, by rfl⟩ : syracuseStep 11337367 = 17006051) B17006051
theorem B4194071 : Blo 1242439 4194071 := bstep (se 1 (by rfl) ⟨3145553, by rfl⟩ : syracuseStep 4194071 = 6291107) B6291107
theorem B2096921 : Blo 1242439 2096921 := bstep (se 2 (by rfl) ⟨786345, by rfl⟩ : syracuseStep 2096921 = 1572691) B1572691
theorem B3358529 : Blo 1242439 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B1990489 : Blo 1242439 1990489 := bstep (se 2 (by rfl) ⟨746433, by rfl⟩ : syracuseStep 1990489 = 1492867) B1492867
theorem B7077725 : Blo 1242439 7077725 := bstep (se 3 (by rfl) ⟨1327073, by rfl⟩ : syracuseStep 7077725 = 2654147) B2654147
theorem B26869603 : Blo 1242439 26869603 := bstep (se 1 (by rfl) ⟨20152202, by rfl⟩ : syracuseStep 26869603 = 40304405) B40304405
theorem B2097049 : Blo 1242439 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B2359219 : Blo 1242439 2359219 := bstep (se 1 (by rfl) ⟨1769414, by rfl⟩ : syracuseStep 2359219 = 3538829) B3538829
theorem B12754867 : Blo 1242439 12754867 := bstep (se 1 (by rfl) ⟨9566150, by rfl⟩ : syracuseStep 12754867 = 19132301) B19132301
theorem B3145675 : Blo 1242439 3145675 := bstep (se 1 (by rfl) ⟨2359256, by rfl⟩ : syracuseStep 3145675 = 4718513) B4718513
theorem B7086041 : Blo 1242439 7086041 := bstep (se 2 (by rfl) ⟨2657265, by rfl⟩ : syracuseStep 7086041 = 5314531) B5314531
theorem B3145787 : Blo 1242439 3145787 := bstep (se 1 (by rfl) ⟨2359340, by rfl⟩ : syracuseStep 3145787 = 4718681) B4718681
theorem B2097211 : Blo 1242439 2097211 := bstep (se 1 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 2097211 = 3145817) B3145817
theorem B2097353 : Blo 1242439 2097353 := bstep (se 2 (by rfl) ⟨786507, by rfl⟩ : syracuseStep 2097353 = 1573015) B1573015
theorem B1573111 : Blo 1242439 1573111 := bstep (se 1 (by rfl) ⟨1179833, by rfl⟩ : syracuseStep 1573111 = 2359667) B2359667
theorem B1794295 : Blo 1242439 1794295 := bstep (se 1 (by rfl) ⟨1345721, by rfl⟩ : syracuseStep 1794295 = 2691443) B2691443
theorem B3145999 : Blo 1242439 3145999 := bstep (se 1 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 3145999 = 4718999) B4718999
theorem B25534865 : Blo 1242439 25534865 := bstep (se 2 (by rfl) ⟨9575574, by rfl⟩ : syracuseStep 25534865 = 19151149) B19151149
theorem B10215827 : Blo 1242439 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B10625539 : Blo 1242439 10625539 := bstep (se 1 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 10625539 = 15938309) B15938309
theorem B4194827 : Blo 1242439 4194827 := bstep (se 1 (by rfl) ⟨3146120, by rfl⟩ : syracuseStep 4194827 = 6292241) B6292241
theorem B3146273 : Blo 1242439 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B1573435 : Blo 1242439 1573435 := bstep (se 1 (by rfl) ⟨1180076, by rfl⟩ : syracuseStep 1573435 = 2360153) B2360153
theorem B4194935 : Blo 1242439 4194935 := bstep (se 1 (by rfl) ⟨3146201, by rfl⟩ : syracuseStep 4194935 = 6292403) B6292403
theorem B1770103 : Blo 1242439 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B2359955 : Blo 1242439 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B1680043 : Blo 1242439 1680043 := bstep (se 1 (by rfl) ⟨1260032, by rfl⟩ : syracuseStep 1680043 = 2520065) B2520065
theorem B2360009 : Blo 1242439 2360009 := bstep (se 2 (by rfl) ⟨885003, by rfl⟩ : syracuseStep 2360009 = 1770007) B1770007
theorem B6726401 : Blo 1242439 6726401 := bstep (se 2 (by rfl) ⟨2522400, by rfl⟩ : syracuseStep 6726401 = 5044801) B5044801
theorem B2360107 : Blo 1242439 2360107 := bstep (se 1 (by rfl) ⟨1770080, by rfl⟩ : syracuseStep 2360107 = 3540161) B3540161
theorem B2098055 : Blo 1242439 2098055 := bstep (se 1 (by rfl) ⟨1573541, by rfl⟩ : syracuseStep 2098055 = 3147083) B3147083
theorem B2360335 : Blo 1242439 2360335 := bstep (se 1 (by rfl) ⟨1770251, by rfl⟩ : syracuseStep 2360335 = 3540503) B3540503
theorem B3408911 : Blo 1242439 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B1573931 : Blo 1242439 1573931 := bstep (se 1 (by rfl) ⟨1180448, by rfl⟩ : syracuseStep 1573931 = 2360897) B2360897
theorem B6726743 : Blo 1242439 6726743 := bstep (se 1 (by rfl) ⟨5045057, by rfl⟩ : syracuseStep 6726743 = 10090115) B10090115
theorem B3540115 : Blo 1242439 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B4195529 : Blo 1242439 4195529 := bstep (se 2 (by rfl) ⟨1573323, by rfl⟩ : syracuseStep 4195529 = 3146647) B3146647
theorem B7079183 : Blo 1242439 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B3540343 : Blo 1242439 3540343 := bstep (se 1 (by rfl) ⟨2655257, by rfl⟩ : syracuseStep 3540343 = 5310515) B5310515
theorem B6292889 : Blo 1242439 6292889 := bstep (se 2 (by rfl) ⟨2359833, by rfl⟩ : syracuseStep 6292889 = 4719667) B4719667
theorem B1574407 : Blo 1242439 1574407 := bstep (se 1 (by rfl) ⟨1180805, by rfl⟩ : syracuseStep 1574407 = 2361611) B2361611
theorem B4720139 : Blo 1242439 4720139 := bstep (se 1 (by rfl) ⟨3540104, by rfl⟩ : syracuseStep 4720139 = 7080209) B7080209
theorem B3147275 : Blo 1242439 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B2098703 : Blo 1242439 2098703 := bstep (se 1 (by rfl) ⟨1574027, by rfl⟩ : syracuseStep 2098703 = 3148055) B3148055
theorem B1992251 : Blo 1242439 1992251 := bstep (se 1 (by rfl) ⟨1494188, by rfl⟩ : syracuseStep 1992251 = 2988377) B2988377
theorem B1771151 : Blo 1242439 1771151 := bstep (se 1 (by rfl) ⟨1328363, by rfl⟩ : syracuseStep 1771151 = 2656727) B2656727
theorem B30254771 : Blo 1242439 30254771 := bstep (se 1 (by rfl) ⟨22691078, by rfl⟩ : syracuseStep 30254771 = 45382157) B45382157
theorem B73664369 : Blo 1242439 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B9439091 : Blo 1242439 9439091 := bstep (se 1 (by rfl) ⟨7079318, by rfl⟩ : syracuseStep 9439091 = 14158637) B14158637
theorem B4196231 : Blo 1242439 4196231 := bstep (se 1 (by rfl) ⟨3147173, by rfl⟩ : syracuseStep 4196231 = 6294347) B6294347
theorem B7178129 : Blo 1242439 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B15927191 : Blo 1242439 15927191 := bstep (se 1 (by rfl) ⟨11945393, by rfl⟩ : syracuseStep 15927191 = 23890787) B23890787
theorem B1771465 : Blo 1242439 1771465 := bstep (se 2 (by rfl) ⟨664299, by rfl⟩ : syracuseStep 1771465 = 1328599) B1328599
theorem B1574903 : Blo 1242439 1574903 := bstep (se 1 (by rfl) ⟨1181177, by rfl⟩ : syracuseStep 1574903 = 2362355) B2362355
theorem B25880593 : Blo 1242439 25880593 := bstep (se 2 (by rfl) ⟨9705222, by rfl⟩ : syracuseStep 25880593 = 19410445) B19410445
theorem B2099243 : Blo 1242439 2099243 := bstep (se 1 (by rfl) ⟨1574432, by rfl⟩ : syracuseStep 2099243 = 3148865) B3148865
theorem B2795579 : Blo 1242439 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B3147923 : Blo 1242439 3147923 := bstep (se 1 (by rfl) ⟨2360942, by rfl⟩ : syracuseStep 3147923 = 4721885) B4721885
theorem B2795705 : Blo 1242439 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B15116489 : Blo 1242439 15116489 := bstep (se 2 (by rfl) ⟨5668683, by rfl⟩ : syracuseStep 15116489 = 11337367) B11337367
theorem B4196609 : Blo 1242439 4196609 := bstep (se 2 (by rfl) ⟨1573728, by rfl⟩ : syracuseStep 4196609 = 3147457) B3147457
theorem B4483343 : Blo 1242439 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B23890241 : Blo 1242439 23890241 := bstep (se 2 (by rfl) ⟨8958840, by rfl⟩ : syracuseStep 23890241 = 17917681) B17917681
theorem B7973255 : Blo 1242439 7973255 := bstep (se 1 (by rfl) ⟨5979941, by rfl⟩ : syracuseStep 7973255 = 11959883) B11959883
theorem B3148217 : Blo 1242439 3148217 := bstep (se 2 (by rfl) ⟨1180581, by rfl⟩ : syracuseStep 3148217 = 2361163) B2361163
theorem B2099641 : Blo 1242439 2099641 := bstep (se 2 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 2099641 = 1574731) B1574731
theorem B35826137 : Blo 1242439 35826137 := bstep (se 2 (by rfl) ⟨13434801, by rfl⟩ : syracuseStep 35826137 = 26869603) B26869603
theorem B2796047 : Blo 1242439 2796047 := bstep (se 1 (by rfl) ⟨2097035, by rfl⟩ : syracuseStep 2796047 = 4194071) B4194071
theorem B2796065 : Blo 1242439 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B2239019 : Blo 1242439 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B6720043 : Blo 1242439 6720043 := bstep (se 1 (by rfl) ⟨5040032, by rfl⟩ : syracuseStep 6720043 = 10080065) B10080065
theorem B2361899 : Blo 1242439 2361899 := bstep (se 1 (by rfl) ⟨1771424, by rfl⟩ : syracuseStep 2361899 = 3542849) B3542849
theorem B3541619 : Blo 1242439 3541619 := bstep (se 1 (by rfl) ⟨2656214, by rfl⟩ : syracuseStep 3541619 = 5312429) B5312429
theorem B7080641 : Blo 1242439 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B2796407 : Blo 1242439 2796407 := bstep (se 1 (by rfl) ⟨2097305, by rfl⟩ : syracuseStep 2796407 = 4194611) B4194611
theorem B2657171 : Blo 1242439 2657171 := bstep (se 1 (by rfl) ⟨1992878, by rfl⟩ : syracuseStep 2657171 = 3985757) B3985757
theorem B3541961 : Blo 1242439 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B5975005 : Blo 1242439 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B2796587 : Blo 1242439 2796587 := bstep (se 1 (by rfl) ⟨2097440, by rfl⟩ : syracuseStep 2796587 = 4194881) B4194881
theorem B4197419 : Blo 1242439 4197419 := bstep (se 1 (by rfl) ⟨3148064, by rfl⟩ : syracuseStep 4197419 = 6296129) B6296129
theorem B3542075 : Blo 1242439 3542075 := bstep (se 1 (by rfl) ⟨2656556, by rfl⟩ : syracuseStep 3542075 = 5313113) B5313113
theorem B3148915 : Blo 1242439 3148915 := bstep (se 1 (by rfl) ⟨2361686, by rfl⟩ : syracuseStep 3148915 = 4723373) B4723373
theorem B3542201 : Blo 1242439 3542201 := bstep (se 2 (by rfl) ⟨1328325, by rfl⟩ : syracuseStep 3542201 = 2656651) B2656651
theorem B14355701 : Blo 1242439 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B3149057 : Blo 1242439 3149057 := bstep (se 2 (by rfl) ⟨1180896, by rfl⟩ : syracuseStep 3149057 = 2361793) B2361793
theorem B3779855 : Blo 1242439 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B5975329 : Blo 1242439 5975329 := bstep (se 2 (by rfl) ⟨2240748, by rfl⟩ : syracuseStep 5975329 = 4481497) B4481497
theorem B6385031 : Blo 1242439 6385031 := bstep (se 1 (by rfl) ⟨4788773, by rfl⟩ : syracuseStep 6385031 = 9577547) B9577547
theorem B2796947 : Blo 1242439 2796947 := bstep (se 1 (by rfl) ⟨2097710, by rfl⟩ : syracuseStep 2796947 = 4195421) B4195421
theorem B2797001 : Blo 1242439 2797001 := bstep (se 2 (by rfl) ⟨1048875, by rfl⟩ : syracuseStep 2797001 = 2097751) B2097751
theorem B12758477 : Blo 1242439 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B5312087 : Blo 1242439 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B3149513 : Blo 1242439 3149513 := bstep (se 2 (by rfl) ⟨1181067, by rfl⟩ : syracuseStep 3149513 = 2362135) B2362135
theorem B2985743 : Blo 1242439 2985743 := bstep (se 1 (by rfl) ⟨2239307, by rfl⟩ : syracuseStep 2985743 = 4478615) B4478615
theorem B32280371 : Blo 1242439 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B6295481 : Blo 1242439 6295481 := bstep (se 2 (by rfl) ⟨2360805, by rfl⟩ : syracuseStep 6295481 = 4721611) B4721611
theorem B1863671 : Blo 1242439 1863671 := bstep (se 1 (by rfl) ⟨1397753, by rfl⟩ : syracuseStep 1863671 = 2795507) B2795507
theorem B1863695 : Blo 1242439 1863695 := bstep (se 1 (by rfl) ⟨1397771, by rfl⟩ : syracuseStep 1863695 = 2795543) B2795543
theorem B2125867 : Blo 1242439 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B3149867 : Blo 1242439 3149867 := bstep (se 1 (by rfl) ⟨2362400, by rfl⟩ : syracuseStep 3149867 = 4724801) B4724801
theorem B1863737 : Blo 1242439 1863737 := bstep (se 2 (by rfl) ⟨698901, by rfl⟩ : syracuseStep 1863737 = 1397803) B1397803
theorem B1863815 : Blo 1242439 1863815 := bstep (se 1 (by rfl) ⟨1397861, by rfl⟩ : syracuseStep 1863815 = 2795723) B2795723
theorem B2797703 : Blo 1242439 2797703 := bstep (se 1 (by rfl) ⟨2098277, by rfl⟩ : syracuseStep 2797703 = 4196555) B4196555
theorem B1863851 : Blo 1242439 1863851 := bstep (se 1 (by rfl) ⟨1397888, by rfl⟩ : syracuseStep 1863851 = 2795777) B2795777
theorem B1863881 : Blo 1242439 1863881 := bstep (se 2 (by rfl) ⟨698955, by rfl⟩ : syracuseStep 1863881 = 1397911) B1397911
theorem B10621165 : Blo 1242439 10621165 := bstep (se 3 (by rfl) ⟨1991468, by rfl⟩ : syracuseStep 10621165 = 3982937) B3982937
theorem B1863995 : Blo 1242439 1863995 := bstep (se 1 (by rfl) ⟨1397996, by rfl⟩ : syracuseStep 1863995 = 2795993) B2795993
theorem B2797883 : Blo 1242439 2797883 := bstep (se 1 (by rfl) ⟨2098412, by rfl⟩ : syracuseStep 2797883 = 4196825) B4196825
theorem B4198715 : Blo 1242439 4198715 := bstep (se 1 (by rfl) ⟨3149036, by rfl⟩ : syracuseStep 4198715 = 6298073) B6298073
theorem B1864055 : Blo 1242439 1864055 := bstep (se 1 (by rfl) ⟨1398041, by rfl⟩ : syracuseStep 1864055 = 2796083) B2796083
theorem B1864079 : Blo 1242439 1864079 := bstep (se 1 (by rfl) ⟨1398059, by rfl⟩ : syracuseStep 1864079 = 2796119) B2796119
theorem B1864121 : Blo 1242439 1864121 := bstep (se 2 (by rfl) ⟨699045, by rfl⟩ : syracuseStep 1864121 = 1398091) B1398091
theorem B2798009 : Blo 1242439 2798009 := bstep (se 2 (by rfl) ⟨1049253, by rfl⟩ : syracuseStep 2798009 = 2098507) B2098507
theorem B9089489 : Blo 1242439 9089489 := bstep (se 2 (by rfl) ⟨3408558, by rfl⟩ : syracuseStep 9089489 = 6817117) B6817117
theorem B3363329 : Blo 1242439 3363329 := bstep (se 2 (by rfl) ⟨1261248, by rfl⟩ : syracuseStep 3363329 = 2522497) B2522497
theorem B1864199 : Blo 1242439 1864199 := bstep (se 1 (by rfl) ⟨1398149, by rfl⟩ : syracuseStep 1864199 = 2796299) B2796299
theorem B1864235 : Blo 1242439 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B15946307 : Blo 1242439 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B1864265 : Blo 1242439 1864265 := bstep (se 2 (by rfl) ⟨699099, by rfl⟩ : syracuseStep 1864265 = 1398199) B1398199
theorem B13447781 : Blo 1242439 13447781 := bstep (se 4 (by rfl) ⟨1260729, by rfl⟩ : syracuseStep 13447781 = 2521459) B2521459
theorem B2691731 : Blo 1242439 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B3363481 : Blo 1242439 3363481 := bstep (se 2 (by rfl) ⟨1261305, by rfl⟩ : syracuseStep 3363481 = 2522611) B2522611
theorem B31847093 : Blo 1242439 31847093 := bstep (se 5 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 31847093 = 2985665) B2985665
theorem B1864379 : Blo 1242439 1864379 := bstep (se 1 (by rfl) ⟨1398284, by rfl⟩ : syracuseStep 1864379 = 2796569) B2796569
theorem B1864439 : Blo 1242439 1864439 := bstep (se 1 (by rfl) ⟨1398329, by rfl⟩ : syracuseStep 1864439 = 2796659) B2796659
theorem B1864463 : Blo 1242439 1864463 := bstep (se 1 (by rfl) ⟨1398347, by rfl⟩ : syracuseStep 1864463 = 2796695) B2796695
theorem B2798351 : Blo 1242439 2798351 := bstep (se 1 (by rfl) ⟨2098763, by rfl⟩ : syracuseStep 2798351 = 4197527) B4197527
theorem B2798369 : Blo 1242439 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B4199201 : Blo 1242439 4199201 := bstep (se 2 (by rfl) ⟨1574700, by rfl⟩ : syracuseStep 4199201 = 3149401) B3149401
theorem B1864505 : Blo 1242439 1864505 := bstep (se 2 (by rfl) ⟨699189, by rfl⟩ : syracuseStep 1864505 = 1398379) B1398379
theorem B1864583 : Blo 1242439 1864583 := bstep (se 1 (by rfl) ⟨1398437, by rfl⟩ : syracuseStep 1864583 = 2796875) B2796875
theorem B5043097 : Blo 1242439 5043097 := bstep (se 2 (by rfl) ⟨1891161, by rfl⟩ : syracuseStep 5043097 = 3782323) B3782323
theorem B1864619 : Blo 1242439 1864619 := bstep (se 1 (by rfl) ⟨1398464, by rfl⟩ : syracuseStep 1864619 = 2796929) B2796929
theorem B1864649 : Blo 1242439 1864649 := bstep (se 2 (by rfl) ⟨699243, by rfl⟩ : syracuseStep 1864649 = 1398487) B1398487
theorem B1397767 : Blo 1242439 1397767 := bstep (se 1 (by rfl) ⟨1048325, by rfl⟩ : syracuseStep 1397767 = 2096651) B2096651
theorem B1864763 : Blo 1242439 1864763 := bstep (se 1 (by rfl) ⟨1398572, by rfl⟩ : syracuseStep 1864763 = 2797145) B2797145
theorem B1864823 : Blo 1242439 1864823 := bstep (se 1 (by rfl) ⟨1398617, by rfl⟩ : syracuseStep 1864823 = 2797235) B2797235
theorem B2798711 : Blo 1242439 2798711 := bstep (se 1 (by rfl) ⟨2099033, by rfl⟩ : syracuseStep 2798711 = 4198067) B4198067
theorem B1864847 : Blo 1242439 1864847 := bstep (se 1 (by rfl) ⟨1398635, by rfl⟩ : syracuseStep 1864847 = 2797271) B2797271
theorem B1864889 : Blo 1242439 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B1397947 : Blo 1242439 1397947 := bstep (se 1 (by rfl) ⟨1048460, by rfl⟩ : syracuseStep 1397947 = 2096921) B2096921
theorem B6296777 : Blo 1242439 6296777 := bstep (se 2 (by rfl) ⟨2361291, by rfl⟩ : syracuseStep 6296777 = 4722583) B4722583
theorem B5043437 : Blo 1242439 5043437 := bstep (se 3 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 5043437 = 1891289) B1891289
theorem B1864967 : Blo 1242439 1864967 := bstep (se 1 (by rfl) ⟨1398725, by rfl⟩ : syracuseStep 1864967 = 2797451) B2797451
theorem B1865003 : Blo 1242439 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B2798891 : Blo 1242439 2798891 := bstep (se 1 (by rfl) ⟨2099168, by rfl⟩ : syracuseStep 2798891 = 4198337) B4198337
theorem B4724027 : Blo 1242439 4724027 := bstep (se 1 (by rfl) ⟨3543020, by rfl⟩ : syracuseStep 4724027 = 7086041) B7086041
theorem B1865033 : Blo 1242439 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B4035955 : Blo 1242439 4035955 := bstep (se 1 (by rfl) ⟨3026966, by rfl⟩ : syracuseStep 4035955 = 6053933) B6053933
theorem B4199795 : Blo 1242439 4199795 := bstep (se 1 (by rfl) ⟨3149846, by rfl⟩ : syracuseStep 4199795 = 6299693) B6299693
theorem B1242503 : Blo 1242439 1242503 := bstep (se 1 (by rfl) ⟨931877, by rfl⟩ : syracuseStep 1242503 = 1863755) B1863755
theorem B1242511 : Blo 1242439 1242511 := bstep (se 1 (by rfl) ⟨931883, by rfl⟩ : syracuseStep 1242511 = 1863767) B1863767
theorem B1242555 : Blo 1242439 1242555 := bstep (se 1 (by rfl) ⟨931916, by rfl⟩ : syracuseStep 1242555 = 1863833) B1863833
theorem B1865147 : Blo 1242439 1865147 := bstep (se 1 (by rfl) ⟨1398860, by rfl⟩ : syracuseStep 1865147 = 2797721) B2797721
theorem B1865207 : Blo 1242439 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B1242631 : Blo 1242439 1242631 := bstep (se 1 (by rfl) ⟨931973, by rfl⟩ : syracuseStep 1242631 = 1863947) B1863947
theorem B1242639 : Blo 1242439 1242639 := bstep (se 1 (by rfl) ⟨931979, by rfl⟩ : syracuseStep 1242639 = 1863959) B1863959
theorem B1865231 : Blo 1242439 1865231 := bstep (se 1 (by rfl) ⟨1398923, by rfl⟩ : syracuseStep 1865231 = 2797847) B2797847
theorem B37344797 : Blo 1242439 37344797 := bstep (se 3 (by rfl) ⟨7002149, by rfl⟩ : syracuseStep 37344797 = 14004299) B14004299
theorem B14358059 : Blo 1242439 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1865273 : Blo 1242439 1865273 := bstep (se 2 (by rfl) ⟨699477, by rfl⟩ : syracuseStep 1865273 = 1398955) B1398955
theorem B1242683 : Blo 1242439 1242683 := bstep (se 1 (by rfl) ⟨932012, by rfl⟩ : syracuseStep 1242683 = 1864025) B1864025
theorem B2987579 : Blo 1242439 2987579 := bstep (se 1 (by rfl) ⟨2240684, by rfl⟩ : syracuseStep 2987579 = 4481369) B4481369
theorem B1242759 : Blo 1242439 1242759 := bstep (se 1 (by rfl) ⟨932069, by rfl⟩ : syracuseStep 1242759 = 1864139) B1864139
theorem B1865351 : Blo 1242439 1865351 := bstep (se 1 (by rfl) ⟨1399013, by rfl⟩ : syracuseStep 1865351 = 2798027) B2798027
theorem B1242767 : Blo 1242439 1242767 := bstep (se 1 (by rfl) ⟨932075, by rfl⟩ : syracuseStep 1242767 = 1864151) B1864151
theorem B1398415 : Blo 1242439 1398415 := bstep (se 1 (by rfl) ⟨1048811, by rfl⟩ : syracuseStep 1398415 = 2097623) B2097623
theorem B2799251 : Blo 1242439 2799251 := bstep (se 1 (by rfl) ⟨2099438, by rfl⟩ : syracuseStep 2799251 = 4198877) B4198877
theorem B1865387 : Blo 1242439 1865387 := bstep (se 1 (by rfl) ⟨1399040, by rfl⟩ : syracuseStep 1865387 = 2798081) B2798081
theorem B1242811 : Blo 1242439 1242811 := bstep (se 1 (by rfl) ⟨932108, by rfl⟩ : syracuseStep 1242811 = 1864217) B1864217
theorem B1865417 : Blo 1242439 1865417 := bstep (se 2 (by rfl) ⟨699531, by rfl⟩ : syracuseStep 1865417 = 1399063) B1399063
theorem B2799305 : Blo 1242439 2799305 := bstep (se 2 (by rfl) ⟨1049739, by rfl⟩ : syracuseStep 2799305 = 2099479) B2099479
theorem B1242887 : Blo 1242439 1242887 := bstep (se 1 (by rfl) ⟨932165, by rfl⟩ : syracuseStep 1242887 = 1864331) B1864331
theorem B1242895 : Blo 1242439 1242895 := bstep (se 1 (by rfl) ⟨932171, by rfl⟩ : syracuseStep 1242895 = 1864343) B1864343
theorem B4724513 : Blo 1242439 4724513 := bstep (se 2 (by rfl) ⟨1771692, by rfl⟩ : syracuseStep 4724513 = 3543385) B3543385
theorem B2987819 : Blo 1242439 2987819 := bstep (se 1 (by rfl) ⟨2240864, by rfl⟩ : syracuseStep 2987819 = 4481729) B4481729
theorem B1242939 : Blo 1242439 1242939 := bstep (se 1 (by rfl) ⟨932204, by rfl⟩ : syracuseStep 1242939 = 1864409) B1864409
theorem B1865531 : Blo 1242439 1865531 := bstep (se 1 (by rfl) ⟨1399148, by rfl⟩ : syracuseStep 1865531 = 2798297) B2798297
theorem B1865591 : Blo 1242439 1865591 := bstep (se 1 (by rfl) ⟨1399193, by rfl⟩ : syracuseStep 1865591 = 2798387) B2798387
theorem B1243015 : Blo 1242439 1243015 := bstep (se 1 (by rfl) ⟨932261, by rfl⟩ : syracuseStep 1243015 = 1864523) B1864523
theorem B1243023 : Blo 1242439 1243023 := bstep (se 1 (by rfl) ⟨932267, by rfl⟩ : syracuseStep 1243023 = 1864535) B1864535
theorem B1865615 : Blo 1242439 1865615 := bstep (se 1 (by rfl) ⟨1399211, by rfl⟩ : syracuseStep 1865615 = 2798423) B2798423
theorem B1865657 : Blo 1242439 1865657 := bstep (se 2 (by rfl) ⟨699621, by rfl⟩ : syracuseStep 1865657 = 1399243) B1399243
theorem B1243067 : Blo 1242439 1243067 := bstep (se 1 (by rfl) ⟨932300, by rfl⟩ : syracuseStep 1243067 = 1864601) B1864601
theorem B1243143 : Blo 1242439 1243143 := bstep (se 1 (by rfl) ⟨932357, by rfl⟩ : syracuseStep 1243143 = 1864715) B1864715
theorem B1865735 : Blo 1242439 1865735 := bstep (se 1 (by rfl) ⟨1399301, by rfl⟩ : syracuseStep 1865735 = 2798603) B2798603
theorem B4782091 : Blo 1242439 4782091 := bstep (se 1 (by rfl) ⟨3586568, by rfl⟩ : syracuseStep 4782091 = 7173137) B7173137
theorem B1243151 : Blo 1242439 1243151 := bstep (se 1 (by rfl) ⟨932363, by rfl⟩ : syracuseStep 1243151 = 1864727) B1864727
theorem B1865771 : Blo 1242439 1865771 := bstep (se 1 (by rfl) ⟨1399328, by rfl⟩ : syracuseStep 1865771 = 2798657) B2798657
theorem B12769325 : Blo 1242439 12769325 := bstep (se 3 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 12769325 = 4788497) B4788497
theorem B1243195 : Blo 1242439 1243195 := bstep (se 1 (by rfl) ⟨932396, by rfl⟩ : syracuseStep 1243195 = 1864793) B1864793
theorem B1865801 : Blo 1242439 1865801 := bstep (se 2 (by rfl) ⟨699675, by rfl⟩ : syracuseStep 1865801 = 1399351) B1399351
theorem B1243271 : Blo 1242439 1243271 := bstep (se 1 (by rfl) ⟨932453, by rfl⟩ : syracuseStep 1243271 = 1864907) B1864907
theorem B1398919 : Blo 1242439 1398919 := bstep (se 1 (by rfl) ⟨1049189, by rfl⟩ : syracuseStep 1398919 = 2098379) B2098379
theorem B1243279 : Blo 1242439 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B10623149 : Blo 1242439 10623149 := bstep (se 3 (by rfl) ⟨1991840, by rfl⟩ : syracuseStep 10623149 = 3983681) B3983681
theorem B1243323 : Blo 1242439 1243323 := bstep (se 1 (by rfl) ⟨932492, by rfl⟩ : syracuseStep 1243323 = 1864985) B1864985
theorem B1865915 : Blo 1242439 1865915 := bstep (se 1 (by rfl) ⟨1399436, by rfl⟩ : syracuseStep 1865915 = 2798873) B2798873
theorem B1865975 : Blo 1242439 1865975 := bstep (se 1 (by rfl) ⟨1399481, by rfl⟩ : syracuseStep 1865975 = 2798963) B2798963
theorem B1243399 : Blo 1242439 1243399 := bstep (se 1 (by rfl) ⟨932549, by rfl⟩ : syracuseStep 1243399 = 1865099) B1865099
theorem B1243407 : Blo 1242439 1243407 := bstep (se 1 (by rfl) ⟨932555, by rfl⟩ : syracuseStep 1243407 = 1865111) B1865111
theorem B1865999 : Blo 1242439 1865999 := bstep (se 1 (by rfl) ⟨1399499, by rfl⟩ : syracuseStep 1865999 = 2798999) B2798999
theorem B1866041 : Blo 1242439 1866041 := bstep (se 2 (by rfl) ⟨699765, by rfl⟩ : syracuseStep 1866041 = 1399531) B1399531
theorem B1243451 : Blo 1242439 1243451 := bstep (se 1 (by rfl) ⟨932588, by rfl⟩ : syracuseStep 1243451 = 1865177) B1865177
theorem B1399099 : Blo 1242439 1399099 := bstep (se 1 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 1399099 = 2098649) B2098649
theorem B1243527 : Blo 1242439 1243527 := bstep (se 1 (by rfl) ⟨932645, by rfl⟩ : syracuseStep 1243527 = 1865291) B1865291
theorem B1866119 : Blo 1242439 1866119 := bstep (se 1 (by rfl) ⟨1399589, by rfl⟩ : syracuseStep 1866119 = 2799179) B2799179
theorem B1243535 : Blo 1242439 1243535 := bstep (se 1 (by rfl) ⟨932651, by rfl⟩ : syracuseStep 1243535 = 1865303) B1865303
theorem B1866155 : Blo 1242439 1866155 := bstep (se 1 (by rfl) ⟨1399616, by rfl⟩ : syracuseStep 1866155 = 2799233) B2799233
theorem B1243579 : Blo 1242439 1243579 := bstep (se 1 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 1243579 = 1865369) B1865369
theorem B1866185 : Blo 1242439 1866185 := bstep (se 2 (by rfl) ⟨699819, by rfl⟩ : syracuseStep 1866185 = 1399639) B1399639
theorem B1243655 : Blo 1242439 1243655 := bstep (se 1 (by rfl) ⟨932741, by rfl⟩ : syracuseStep 1243655 = 1865483) B1865483
theorem B1243663 : Blo 1242439 1243663 := bstep (se 1 (by rfl) ⟨932747, by rfl⟩ : syracuseStep 1243663 = 1865495) B1865495
theorem B3029519 : Blo 1242439 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B4610603 : Blo 1242439 4610603 := bstep (se 1 (by rfl) ⟨3457952, by rfl⟩ : syracuseStep 4610603 = 6915905) B6915905
theorem B2988587 : Blo 1242439 2988587 := bstep (se 1 (by rfl) ⟨2241440, by rfl⟩ : syracuseStep 2988587 = 4482881) B4482881
theorem B1243707 : Blo 1242439 1243707 := bstep (se 1 (by rfl) ⟨932780, by rfl⟩ : syracuseStep 1243707 = 1865561) B1865561
theorem B1866299 : Blo 1242439 1866299 := bstep (se 1 (by rfl) ⟨1399724, by rfl⟩ : syracuseStep 1866299 = 2799449) B2799449
theorem B1866359 : Blo 1242439 1866359 := bstep (se 1 (by rfl) ⟨1399769, by rfl⟩ : syracuseStep 1866359 = 2799539) B2799539
theorem B1243783 : Blo 1242439 1243783 := bstep (se 1 (by rfl) ⟨932837, by rfl⟩ : syracuseStep 1243783 = 1865675) B1865675
theorem B1243791 : Blo 1242439 1243791 := bstep (se 1 (by rfl) ⟨932843, by rfl⟩ : syracuseStep 1243791 = 1865687) B1865687
theorem B1866383 : Blo 1242439 1866383 := bstep (se 1 (by rfl) ⟨1399787, by rfl⟩ : syracuseStep 1866383 = 2799575) B2799575
theorem B11958961 : Blo 1242439 11958961 := bstep (se 2 (by rfl) ⟨4484610, by rfl⟩ : syracuseStep 11958961 = 8969221) B8969221
theorem B1866425 : Blo 1242439 1866425 := bstep (se 2 (by rfl) ⟨699909, by rfl⟩ : syracuseStep 1866425 = 1399819) B1399819
theorem B1243835 : Blo 1242439 1243835 := bstep (se 1 (by rfl) ⟨932876, by rfl⟩ : syracuseStep 1243835 = 1865753) B1865753
theorem B15940313 : Blo 1242439 15940313 := bstep (se 2 (by rfl) ⟨5977617, by rfl⟩ : syracuseStep 15940313 = 11955235) B11955235
theorem B1243911 : Blo 1242439 1243911 := bstep (se 1 (by rfl) ⟨932933, by rfl⟩ : syracuseStep 1243911 = 1865867) B1865867
theorem B1866503 : Blo 1242439 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1243919 : Blo 1242439 1243919 := bstep (se 1 (by rfl) ⟨932939, by rfl⟩ : syracuseStep 1243919 = 1865879) B1865879
theorem B1399567 : Blo 1242439 1399567 := bstep (se 1 (by rfl) ⟨1049675, by rfl⟩ : syracuseStep 1399567 = 2099351) B2099351
theorem B1866539 : Blo 1242439 1866539 := bstep (se 1 (by rfl) ⟨1399904, by rfl⟩ : syracuseStep 1866539 = 2799809) B2799809
theorem B1243963 : Blo 1242439 1243963 := bstep (se 1 (by rfl) ⟨932972, by rfl⟩ : syracuseStep 1243963 = 1865945) B1865945
theorem B1866569 : Blo 1242439 1866569 := bstep (se 2 (by rfl) ⟨699963, by rfl⟩ : syracuseStep 1866569 = 1399927) B1399927
theorem B1244039 : Blo 1242439 1244039 := bstep (se 1 (by rfl) ⟨933029, by rfl⟩ : syracuseStep 1244039 = 1866059) B1866059
theorem B1244047 : Blo 1242439 1244047 := bstep (se 1 (by rfl) ⟨933035, by rfl⟩ : syracuseStep 1244047 = 1866071) B1866071
theorem B1244091 : Blo 1242439 1244091 := bstep (se 1 (by rfl) ⟨933068, by rfl⟩ : syracuseStep 1244091 = 1866137) B1866137
theorem B1244167 : Blo 1242439 1244167 := bstep (se 1 (by rfl) ⟨933125, by rfl⟩ : syracuseStep 1244167 = 1866251) B1866251
theorem B3980299 : Blo 1242439 3980299 := bstep (se 1 (by rfl) ⟨2985224, by rfl⟩ : syracuseStep 3980299 = 5970449) B5970449
theorem B1244175 : Blo 1242439 1244175 := bstep (se 1 (by rfl) ⟨933131, by rfl⟩ : syracuseStep 1244175 = 1866263) B1866263
theorem B1244219 : Blo 1242439 1244219 := bstep (se 1 (by rfl) ⟨933164, by rfl⟩ : syracuseStep 1244219 = 1866329) B1866329
theorem B1244295 : Blo 1242439 1244295 := bstep (se 1 (by rfl) ⟨933221, by rfl⟩ : syracuseStep 1244295 = 1866443) B1866443
theorem B1244303 : Blo 1242439 1244303 := bstep (se 1 (by rfl) ⟨933227, by rfl⟩ : syracuseStep 1244303 = 1866455) B1866455
theorem B1244347 : Blo 1242439 1244347 := bstep (se 1 (by rfl) ⟨933260, by rfl⟩ : syracuseStep 1244347 = 1866521) B1866521
theorem B8969453 : Blo 1242439 8969453 := bstep (se 3 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 8969453 = 3363545) B3363545
theorem B1244423 : Blo 1242439 1244423 := bstep (se 1 (by rfl) ⟨933317, by rfl⟩ : syracuseStep 1244423 = 1866635) B1866635
theorem B1244431 : Blo 1242439 1244431 := bstep (se 1 (by rfl) ⟨933323, by rfl⟩ : syracuseStep 1244431 = 1866647) B1866647
theorem B7085515 : Blo 1242439 7085515 := bstep (se 1 (by rfl) ⟨5314136, by rfl⟩ : syracuseStep 7085515 = 10628273) B10628273
theorem B48455171 : Blo 1242439 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B3538475 : Blo 1242439 3538475 := bstep (se 1 (by rfl) ⟨2653856, by rfl⟩ : syracuseStep 3538475 = 5307713) B5307713
theorem B3145331 : Blo 1242439 3145331 := bstep (se 1 (by rfl) ⟨2358998, by rfl⟩ : syracuseStep 3145331 = 4717997) B4717997
theorem B2096759 : Blo 1242439 2096759 := bstep (se 1 (by rfl) ⟨1572569, by rfl⟩ : syracuseStep 2096759 = 3145139) B3145139
theorem B3145351 : Blo 1242439 3145351 := bstep (se 1 (by rfl) ⟨2359013, by rfl⟩ : syracuseStep 3145351 = 4718027) B4718027
theorem B1892087 : Blo 1242439 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B15933185 : Blo 1242439 15933185 := bstep (se 2 (by rfl) ⟨5974944, by rfl⟩ : syracuseStep 15933185 = 11949889) B11949889
theorem B3538703 : Blo 1242439 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B11951887 : Blo 1242439 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B2653985 : Blo 1242439 2653985 := bstep (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) B1990489
theorem B4718483 : Blo 1242439 4718483 := bstep (se 1 (by rfl) ⟨3538862, by rfl⟩ : syracuseStep 4718483 = 7077725) B7077725
theorem B3145625 : Blo 1242439 3145625 := bstep (se 2 (by rfl) ⟨1179609, by rfl⟩ : syracuseStep 3145625 = 2359219) B2359219
theorem B17006489 : Blo 1242439 17006489 := bstep (se 2 (by rfl) ⟨6377433, by rfl⟩ : syracuseStep 17006489 = 12754867) B12754867
theorem B4194233 : Blo 1242439 4194233 := bstep (se 2 (by rfl) ⟨1572837, by rfl⟩ : syracuseStep 4194233 = 3145675) B3145675
theorem B2097191 : Blo 1242439 2097191 := bstep (se 1 (by rfl) ⟨1572893, by rfl⟩ : syracuseStep 2097191 = 3145787) B3145787
theorem B2834489 : Blo 1242439 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B17023243 : Blo 1242439 17023243 := bstep (se 1 (by rfl) ⟨12767432, by rfl⟩ : syracuseStep 17023243 = 25534865) B25534865
theorem B2097481 : Blo 1242439 2097481 := bstep (se 2 (by rfl) ⟨786555, by rfl⟩ : syracuseStep 2097481 = 1573111) B1573111
theorem B4194665 : Blo 1242439 4194665 := bstep (se 2 (by rfl) ⟨1572999, by rfl⟩ : syracuseStep 4194665 = 3145999) B3145999
theorem B2097515 : Blo 1242439 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B1794487 : Blo 1242439 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B1573339 : Blo 1242439 1573339 := bstep (se 1 (by rfl) ⟨1180004, by rfl⟩ : syracuseStep 1573339 = 2360009) B2360009
theorem B2097913 : Blo 1242439 2097913 := bstep (se 2 (by rfl) ⟨786717, by rfl⟩ : syracuseStep 2097913 = 1573435) B1573435
theorem B4719455 : Blo 1242439 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B4195259 : Blo 1242439 4195259 := bstep (se 1 (by rfl) ⟨3146444, by rfl⟩ : syracuseStep 4195259 = 6292889) B6292889
theorem B3146759 : Blo 1242439 3146759 := bstep (se 1 (by rfl) ⟨2360069, by rfl⟩ : syracuseStep 3146759 = 4720139) B4720139
theorem B2098183 : Blo 1242439 2098183 := bstep (se 1 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 2098183 = 3147275) B3147275
theorem B24896531 : Blo 1242439 24896531 := bstep (se 1 (by rfl) ⟨18672398, by rfl⟩ : syracuseStep 24896531 = 37344797) B37344797
theorem B1991719 : Blo 1242439 1991719 := bstep (se 1 (by rfl) ⟨1493789, by rfl⟩ : syracuseStep 1991719 = 2987579) B2987579
theorem B1328167 : Blo 1242439 1328167 := bstep (se 1 (by rfl) ⟨996125, by rfl⟩ : syracuseStep 1328167 = 1992251) B1992251
theorem B3146809 : Blo 1242439 3146809 := bstep (se 2 (by rfl) ⟨1180053, by rfl⟩ : syracuseStep 3146809 = 2360107) B2360107
theorem B20169847 : Blo 1242439 20169847 := bstep (se 1 (by rfl) ⟨15127385, by rfl⟩ : syracuseStep 20169847 = 30254771) B30254771
theorem B1991879 : Blo 1242439 1991879 := bstep (se 1 (by rfl) ⟨1493909, by rfl⟩ : syracuseStep 1991879 = 2987819) B2987819
theorem B34022605 : Blo 1242439 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B6292727 : Blo 1242439 6292727 := bstep (se 1 (by rfl) ⟨4719545, by rfl⟩ : syracuseStep 6292727 = 9439091) B9439091
theorem B4785419 : Blo 1242439 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B10618127 : Blo 1242439 10618127 := bstep (se 1 (by rfl) ⟨7963595, by rfl⟩ : syracuseStep 10618127 = 15927191) B15927191
theorem B9569573 : Blo 1242439 9569573 := bstep (se 4 (by rfl) ⟨897147, by rfl⟩ : syracuseStep 9569573 = 1794295) B1794295
theorem B3147113 : Blo 1242439 3147113 := bstep (se 2 (by rfl) ⟨1180167, by rfl⟩ : syracuseStep 3147113 = 2360335) B2360335
theorem B8512883 : Blo 1242439 8512883 := bstep (se 1 (by rfl) ⟨6384662, by rfl⟩ : syracuseStep 8512883 = 12769325) B12769325
theorem B8078717 : Blo 1242439 8078717 := bstep (se 3 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 8078717 = 3029519) B3029519
theorem B2098615 : Blo 1242439 2098615 := bstep (se 1 (by rfl) ⟨1573961, by rfl⟩ : syracuseStep 2098615 = 3147923) B3147923
theorem B10077659 : Blo 1242439 10077659 := bstep (se 1 (by rfl) ⟨7558244, by rfl⟩ : syracuseStep 10077659 = 15116489) B15116489
theorem B4720153 : Blo 1242439 4720153 := bstep (se 2 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 4720153 = 3540115) B3540115
theorem B15926827 : Blo 1242439 15926827 := bstep (se 1 (by rfl) ⟨11945120, by rfl⟩ : syracuseStep 15926827 = 23890241) B23890241
theorem B2098811 : Blo 1242439 2098811 := bstep (se 1 (by rfl) ⟨1574108, by rfl⟩ : syracuseStep 2098811 = 3148217) B3148217
theorem B3073735 : Blo 1242439 3073735 := bstep (se 1 (by rfl) ⟨2305301, by rfl⟩ : syracuseStep 3073735 = 4610603) B4610603
theorem B1492679 : Blo 1242439 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B6293213 : Blo 1242439 6293213 := bstep (se 3 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 6293213 = 2359955) B2359955
theorem B2361079 : Blo 1242439 2361079 := bstep (se 1 (by rfl) ⟨1770809, by rfl⟩ : syracuseStep 2361079 = 3541619) B3541619
theorem B4720427 : Blo 1242439 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B10626875 : Blo 1242439 10626875 := bstep (se 1 (by rfl) ⟨7970156, by rfl⟩ : syracuseStep 10626875 = 15940313) B15940313
theorem B4720457 : Blo 1242439 4720457 := bstep (se 2 (by rfl) ⟨1770171, by rfl⟩ : syracuseStep 4720457 = 3540343) B3540343
theorem B9447353 : Blo 1242439 9447353 := bstep (se 2 (by rfl) ⟨3542757, by rfl⟩ : syracuseStep 9447353 = 7085515) B7085515
theorem B2361307 : Blo 1242439 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B2099209 : Blo 1242439 2099209 := bstep (se 2 (by rfl) ⟨787203, by rfl⟩ : syracuseStep 2099209 = 1574407) B1574407
theorem B2361383 : Blo 1242439 2361383 := bstep (se 1 (by rfl) ⟨1771037, by rfl⟩ : syracuseStep 2361383 = 3542075) B3542075
theorem B2361467 : Blo 1242439 2361467 := bstep (se 1 (by rfl) ⟨1771100, by rfl⟩ : syracuseStep 2361467 = 3542201) B3542201
theorem B9570467 : Blo 1242439 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B2099371 : Blo 1242439 2099371 := bstep (se 1 (by rfl) ⟨1574528, by rfl⟩ : syracuseStep 2099371 = 3149057) B3149057
theorem B32303447 : Blo 1242439 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B15935849 : Blo 1242439 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B3541391 : Blo 1242439 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B2099675 : Blo 1242439 2099675 := bstep (se 1 (by rfl) ⟨1574756, by rfl⟩ : syracuseStep 2099675 = 3149513) B3149513
theorem B2361953 : Blo 1242439 2361953 := bstep (se 2 (by rfl) ⟨885732, by rfl⟩ : syracuseStep 2361953 = 1771465) B1771465
theorem B2796155 : Blo 1242439 2796155 := bstep (se 1 (by rfl) ⟨2097116, by rfl⟩ : syracuseStep 2796155 = 4194233) B4194233
theorem B4196987 : Blo 1242439 4196987 := bstep (se 1 (by rfl) ⟨3147740, by rfl⟩ : syracuseStep 4196987 = 6295481) B6295481
theorem B6376121 : Blo 1242439 6376121 := bstep (se 2 (by rfl) ⟨2391045, by rfl⟩ : syracuseStep 6376121 = 4782091) B4782091
theorem B34507457 : Blo 1242439 34507457 := bstep (se 2 (by rfl) ⟨12940296, by rfl⟩ : syracuseStep 34507457 = 25880593) B25880593
theorem B2099911 : Blo 1242439 2099911 := bstep (se 1 (by rfl) ⟨1574933, by rfl⟩ : syracuseStep 2099911 = 3149867) B3149867
theorem B2796281 : Blo 1242439 2796281 := bstep (se 2 (by rfl) ⟨1048605, by rfl⟩ : syracuseStep 2796281 = 2097211) B2097211
theorem B4197149 : Blo 1242439 4197149 := bstep (se 3 (by rfl) ⟨786965, by rfl⟩ : syracuseStep 4197149 = 1573931) B1573931
theorem B6810551 : Blo 1242439 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B2796551 : Blo 1242439 2796551 := bstep (se 1 (by rfl) ⟨2097413, by rfl⟩ : syracuseStep 2796551 = 4194827) B4194827
theorem B8965187 : Blo 1242439 8965187 := bstep (se 1 (by rfl) ⟨6723890, by rfl⟩ : syracuseStep 8965187 = 13447781) B13447781
theorem B2796623 : Blo 1242439 2796623 := bstep (se 1 (by rfl) ⟨2097467, by rfl⟩ : syracuseStep 2796623 = 4194935) B4194935
theorem B4484267 : Blo 1242439 4484267 := bstep (se 1 (by rfl) ⟨3363200, by rfl⟩ : syracuseStep 4484267 = 6726401) B6726401
theorem B9440549 : Blo 1242439 9440549 := bstep (se 4 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 9440549 = 1770103) B1770103
theorem B14167385 : Blo 1242439 14167385 := bstep (se 2 (by rfl) ⟨5312769, by rfl⟩ : syracuseStep 14167385 = 10625539) B10625539
theorem B2272607 : Blo 1242439 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B4484495 : Blo 1242439 4484495 := bstep (se 1 (by rfl) ⟨3363371, by rfl⟩ : syracuseStep 4484495 = 6726743) B6726743
theorem B2797019 : Blo 1242439 2797019 := bstep (se 1 (by rfl) ⟨2097764, by rfl⟩ : syracuseStep 2797019 = 4195529) B4195529
theorem B4197851 : Blo 1242439 4197851 := bstep (se 1 (by rfl) ⟨3148388, by rfl⟩ : syracuseStep 4197851 = 6296777) B6296777
theorem B3362291 : Blo 1242439 3362291 := bstep (se 1 (by rfl) ⟨2521718, by rfl⟩ : syracuseStep 3362291 = 5043437) B5043437
theorem B4484641 : Blo 1242439 4484641 := bstep (se 2 (by rfl) ⟨1681740, by rfl⟩ : syracuseStep 4484641 = 3363481) B3363481
theorem B3149351 : Blo 1242439 3149351 := bstep (se 1 (by rfl) ⟨2362013, by rfl⟩ : syracuseStep 3149351 = 4724027) B4724027
theorem B2240057 : Blo 1242439 2240057 := bstep (se 2 (by rfl) ⟨840021, by rfl⟩ : syracuseStep 2240057 = 1680043) B1680043
theorem B15945281 : Blo 1242439 15945281 := bstep (se 2 (by rfl) ⟨5979480, by rfl⟩ : syracuseStep 15945281 = 11958961) B11958961
theorem B21262013 : Blo 1242439 21262013 := bstep (se 3 (by rfl) ⟨3986627, by rfl⟩ : syracuseStep 21262013 = 7973255) B7973255
theorem B9572039 : Blo 1242439 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B3149675 : Blo 1242439 3149675 := bstep (se 1 (by rfl) ⟨2362256, by rfl⟩ : syracuseStep 3149675 = 4724513) B4724513
theorem B2797487 : Blo 1242439 2797487 := bstep (se 1 (by rfl) ⟨2098115, by rfl⟩ : syracuseStep 2797487 = 4196231) B4196231
theorem B7966673 : Blo 1242439 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B1863689 : Blo 1242439 1863689 := bstep (se 2 (by rfl) ⟨698883, by rfl⟩ : syracuseStep 1863689 = 1397767) B1397767
theorem B1863719 : Blo 1242439 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B7082099 : Blo 1242439 7082099 := bstep (se 1 (by rfl) ⟨5311574, by rfl⟩ : syracuseStep 7082099 = 10623149) B10623149
theorem B1863803 : Blo 1242439 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B4198553 : Blo 1242439 4198553 := bstep (se 2 (by rfl) ⟨1574457, by rfl⟩ : syracuseStep 4198553 = 3148915) B3148915
theorem B2797739 : Blo 1242439 2797739 := bstep (se 1 (by rfl) ⟨2098304, by rfl⟩ : syracuseStep 2797739 = 4196609) B4196609
theorem B1863929 : Blo 1242439 1863929 := bstep (se 2 (by rfl) ⟨698973, by rfl⟩ : syracuseStep 1863929 = 1397947) B1397947
theorem B23884091 : Blo 1242439 23884091 := bstep (se 1 (by rfl) ⟨17913068, by rfl⟩ : syracuseStep 23884091 = 35826137) B35826137
theorem B1864031 : Blo 1242439 1864031 := bstep (se 1 (by rfl) ⟨1398023, by rfl⟩ : syracuseStep 1864031 = 2796047) B2796047
theorem B1864043 : Blo 1242439 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B4723069 : Blo 1242439 4723069 := bstep (se 3 (by rfl) ⟨885575, by rfl⟩ : syracuseStep 4723069 = 1771151) B1771151
theorem B7967105 : Blo 1242439 7967105 := bstep (se 2 (by rfl) ⟨2987664, by rfl⟩ : syracuseStep 7967105 = 5975329) B5975329
theorem B1864271 : Blo 1242439 1864271 := bstep (se 1 (by rfl) ⟨1398203, by rfl⟩ : syracuseStep 1864271 = 2796407) B2796407
theorem B1864391 : Blo 1242439 1864391 := bstep (se 1 (by rfl) ⟨1398293, by rfl⟩ : syracuseStep 1864391 = 2796587) B2796587
theorem B2798279 : Blo 1242439 2798279 := bstep (se 1 (by rfl) ⟨2098709, by rfl⟩ : syracuseStep 2798279 = 4197419) B4197419
theorem B2519903 : Blo 1242439 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B1864553 : Blo 1242439 1864553 := bstep (se 2 (by rfl) ⟨699207, by rfl⟩ : syracuseStep 1864553 = 1398415) B1398415
theorem B4256687 : Blo 1242439 4256687 := bstep (se 1 (by rfl) ⟨3192515, by rfl⟩ : syracuseStep 4256687 = 6385031) B6385031
theorem B1864631 : Blo 1242439 1864631 := bstep (se 1 (by rfl) ⟨1398473, by rfl⟩ : syracuseStep 1864631 = 2796947) B2796947
theorem B1864667 : Blo 1242439 1864667 := bstep (se 1 (by rfl) ⟨1398500, by rfl⟩ : syracuseStep 1864667 = 2797001) B2797001
theorem B1397839 : Blo 1242439 1397839 := bstep (se 1 (by rfl) ⟨1048379, by rfl⟩ : syracuseStep 1397839 = 2096759) B2096759
theorem B10622123 : Blo 1242439 10622123 := bstep (se 1 (by rfl) ⟨7966592, by rfl⟩ : syracuseStep 10622123 = 15933185) B15933185
theorem B4199741 : Blo 1242439 4199741 := bstep (se 3 (by rfl) ⟨787451, by rfl⟩ : syracuseStep 4199741 = 1574903) B1574903
theorem B1242447 : Blo 1242439 1242447 := bstep (se 1 (by rfl) ⟨931835, by rfl⟩ : syracuseStep 1242447 = 1863671) B1863671
theorem B1242463 : Blo 1242439 1242463 := bstep (se 1 (by rfl) ⟨931847, by rfl⟩ : syracuseStep 1242463 = 1863695) B1863695
theorem B1242491 : Blo 1242439 1242491 := bstep (se 1 (by rfl) ⟨931868, by rfl⟩ : syracuseStep 1242491 = 1863737) B1863737
theorem B1242543 : Blo 1242439 1242543 := bstep (se 1 (by rfl) ⟨931907, by rfl⟩ : syracuseStep 1242543 = 1863815) B1863815
theorem B1865135 : Blo 1242439 1865135 := bstep (se 1 (by rfl) ⟨1398851, by rfl⟩ : syracuseStep 1865135 = 2797703) B2797703
theorem B1242567 : Blo 1242439 1242567 := bstep (se 1 (by rfl) ⟨931925, by rfl⟩ : syracuseStep 1242567 = 1863851) B1863851
theorem B1242587 : Blo 1242439 1242587 := bstep (se 1 (by rfl) ⟨931940, by rfl⟩ : syracuseStep 1242587 = 1863881) B1863881
theorem B1398235 : Blo 1242439 1398235 := bstep (se 1 (by rfl) ⟨1048676, by rfl⟩ : syracuseStep 1398235 = 2097353) B2097353
theorem B1865225 : Blo 1242439 1865225 := bstep (se 2 (by rfl) ⟨699459, by rfl⟩ : syracuseStep 1865225 = 1398919) B1398919
theorem B1242663 : Blo 1242439 1242663 := bstep (se 1 (by rfl) ⟨931997, by rfl⟩ : syracuseStep 1242663 = 1863995) B1863995
theorem B1865255 : Blo 1242439 1865255 := bstep (se 1 (by rfl) ⟨1398941, by rfl⟩ : syracuseStep 1865255 = 2797883) B2797883
theorem B2799143 : Blo 1242439 2799143 := bstep (se 1 (by rfl) ⟨2099357, by rfl⟩ : syracuseStep 2799143 = 4198715) B4198715
theorem B1242703 : Blo 1242439 1242703 := bstep (se 1 (by rfl) ⟨932027, by rfl⟩ : syracuseStep 1242703 = 1864055) B1864055
theorem B1242719 : Blo 1242439 1242719 := bstep (se 1 (by rfl) ⟨932039, by rfl⟩ : syracuseStep 1242719 = 1864079) B1864079
theorem B1242747 : Blo 1242439 1242747 := bstep (se 1 (by rfl) ⟨932060, by rfl⟩ : syracuseStep 1242747 = 1864121) B1864121
theorem B1865339 : Blo 1242439 1865339 := bstep (se 1 (by rfl) ⟨1399004, by rfl⟩ : syracuseStep 1865339 = 2798009) B2798009
theorem B6059659 : Blo 1242439 6059659 := bstep (se 1 (by rfl) ⟨4544744, by rfl⟩ : syracuseStep 6059659 = 9089489) B9089489
theorem B14161553 : Blo 1242439 14161553 := bstep (se 2 (by rfl) ⟨5310582, by rfl⟩ : syracuseStep 14161553 = 10621165) B10621165
theorem B1242799 : Blo 1242439 1242799 := bstep (se 1 (by rfl) ⟨932099, by rfl⟩ : syracuseStep 1242799 = 1864199) B1864199
theorem B1242823 : Blo 1242439 1242823 := bstep (se 1 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 1242823 = 1864235) B1864235
theorem B10630871 : Blo 1242439 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B1242843 : Blo 1242439 1242843 := bstep (se 1 (by rfl) ⟨932132, by rfl⟩ : syracuseStep 1242843 = 1864265) B1864265
theorem B1865465 : Blo 1242439 1865465 := bstep (se 2 (by rfl) ⟨699549, by rfl⟩ : syracuseStep 1865465 = 1399099) B1399099
theorem B21231395 : Blo 1242439 21231395 := bstep (se 1 (by rfl) ⟨15923546, by rfl⟩ : syracuseStep 21231395 = 31847093) B31847093
theorem B1242919 : Blo 1242439 1242919 := bstep (se 1 (by rfl) ⟨932189, by rfl⟩ : syracuseStep 1242919 = 1864379) B1864379
theorem B1242959 : Blo 1242439 1242959 := bstep (se 1 (by rfl) ⟨932219, by rfl⟩ : syracuseStep 1242959 = 1864439) B1864439
theorem B1242975 : Blo 1242439 1242975 := bstep (se 1 (by rfl) ⟨932231, by rfl⟩ : syracuseStep 1242975 = 1864463) B1864463
theorem B1865567 : Blo 1242439 1865567 := bstep (se 1 (by rfl) ⟨1399175, by rfl⟩ : syracuseStep 1865567 = 2798351) B2798351
theorem B1865579 : Blo 1242439 1865579 := bstep (se 1 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 1865579 = 2798369) B2798369
theorem B2799467 : Blo 1242439 2799467 := bstep (se 1 (by rfl) ⟨2099600, by rfl⟩ : syracuseStep 2799467 = 4199201) B4199201
theorem B1243003 : Blo 1242439 1243003 := bstep (se 1 (by rfl) ⟨932252, by rfl⟩ : syracuseStep 1243003 = 1864505) B1864505
theorem B2799521 : Blo 1242439 2799521 := bstep (se 2 (by rfl) ⟨1049820, by rfl⟩ : syracuseStep 2799521 = 2099641) B2099641
theorem B1243055 : Blo 1242439 1243055 := bstep (se 1 (by rfl) ⟨932291, by rfl⟩ : syracuseStep 1243055 = 1864583) B1864583
theorem B1398703 : Blo 1242439 1398703 := bstep (se 1 (by rfl) ⟨1049027, by rfl⟩ : syracuseStep 1398703 = 2098055) B2098055
theorem B1243079 : Blo 1242439 1243079 := bstep (se 1 (by rfl) ⟨932309, by rfl⟩ : syracuseStep 1243079 = 1864619) B1864619
theorem B1243099 : Blo 1242439 1243099 := bstep (se 1 (by rfl) ⟨932324, by rfl⟩ : syracuseStep 1243099 = 1864649) B1864649
theorem B1243175 : Blo 1242439 1243175 := bstep (se 1 (by rfl) ⟨932381, by rfl⟩ : syracuseStep 1243175 = 1864763) B1864763
theorem B8960057 : Blo 1242439 8960057 := bstep (se 2 (by rfl) ⟨3360021, by rfl⟩ : syracuseStep 8960057 = 6720043) B6720043
theorem B1243215 : Blo 1242439 1243215 := bstep (se 1 (by rfl) ⟨932411, by rfl⟩ : syracuseStep 1243215 = 1864823) B1864823
theorem B1865807 : Blo 1242439 1865807 := bstep (se 1 (by rfl) ⟨1399355, by rfl⟩ : syracuseStep 1865807 = 2798711) B2798711
theorem B1243231 : Blo 1242439 1243231 := bstep (se 1 (by rfl) ⟨932423, by rfl⟩ : syracuseStep 1243231 = 1864847) B1864847
theorem B1243259 : Blo 1242439 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B1243311 : Blo 1242439 1243311 := bstep (se 1 (by rfl) ⟨932483, by rfl⟩ : syracuseStep 1243311 = 1864967) B1864967
theorem B1243335 : Blo 1242439 1243335 := bstep (se 1 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 1243335 = 1865003) B1865003
theorem B1865927 : Blo 1242439 1865927 := bstep (se 1 (by rfl) ⟨1399445, by rfl⟩ : syracuseStep 1865927 = 2798891) B2798891
theorem B1243355 : Blo 1242439 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B2799863 : Blo 1242439 2799863 := bstep (se 1 (by rfl) ⟨2099897, by rfl⟩ : syracuseStep 2799863 = 4199795) B4199795
theorem B1243431 : Blo 1242439 1243431 := bstep (se 1 (by rfl) ⟨932573, by rfl⟩ : syracuseStep 1243431 = 1865147) B1865147
theorem B1243471 : Blo 1242439 1243471 := bstep (se 1 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 1243471 = 1865207) B1865207
theorem B1243487 : Blo 1242439 1243487 := bstep (se 1 (by rfl) ⟨932615, by rfl⟩ : syracuseStep 1243487 = 1865231) B1865231
theorem B1399135 : Blo 1242439 1399135 := bstep (se 1 (by rfl) ⟨1049351, by rfl⟩ : syracuseStep 1399135 = 2098703) B2098703
theorem B1866089 : Blo 1242439 1866089 := bstep (se 2 (by rfl) ⟨699783, by rfl⟩ : syracuseStep 1866089 = 1399567) B1399567
theorem B1243515 : Blo 1242439 1243515 := bstep (se 1 (by rfl) ⟨932636, by rfl⟩ : syracuseStep 1243515 = 1865273) B1865273
theorem B1243567 : Blo 1242439 1243567 := bstep (se 1 (by rfl) ⟨932675, by rfl⟩ : syracuseStep 1243567 = 1865351) B1865351
theorem B1866167 : Blo 1242439 1866167 := bstep (se 1 (by rfl) ⟨1399625, by rfl⟩ : syracuseStep 1866167 = 2799251) B2799251
theorem B1243591 : Blo 1242439 1243591 := bstep (se 1 (by rfl) ⟨932693, by rfl⟩ : syracuseStep 1243591 = 1865387) B1865387
theorem B1243611 : Blo 1242439 1243611 := bstep (se 1 (by rfl) ⟨932708, by rfl⟩ : syracuseStep 1243611 = 1865417) B1865417
theorem B1866203 : Blo 1242439 1866203 := bstep (se 1 (by rfl) ⟨1399652, by rfl⟩ : syracuseStep 1866203 = 2799305) B2799305
theorem B6724129 : Blo 1242439 6724129 := bstep (se 2 (by rfl) ⟨2521548, by rfl⟩ : syracuseStep 6724129 = 5043097) B5043097
theorem B1243687 : Blo 1242439 1243687 := bstep (se 1 (by rfl) ⟨932765, by rfl⟩ : syracuseStep 1243687 = 1865531) B1865531
theorem B49109579 : Blo 1242439 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B1243727 : Blo 1242439 1243727 := bstep (se 1 (by rfl) ⟨932795, by rfl⟩ : syracuseStep 1243727 = 1865591) B1865591
theorem B1243743 : Blo 1242439 1243743 := bstep (se 1 (by rfl) ⟨932807, by rfl⟩ : syracuseStep 1243743 = 1865615) B1865615
theorem B1243771 : Blo 1242439 1243771 := bstep (se 1 (by rfl) ⟨932828, by rfl⟩ : syracuseStep 1243771 = 1865657) B1865657
theorem B8968877 : Blo 1242439 8968877 := bstep (se 3 (by rfl) ⟨1681664, by rfl⟩ : syracuseStep 8968877 = 3363329) B3363329
theorem B1243823 : Blo 1242439 1243823 := bstep (se 1 (by rfl) ⟨932867, by rfl⟩ : syracuseStep 1243823 = 1865735) B1865735
theorem B5307065 : Blo 1242439 5307065 := bstep (se 2 (by rfl) ⟨1990149, by rfl⟩ : syracuseStep 5307065 = 3980299) B3980299
theorem B1243847 : Blo 1242439 1243847 := bstep (se 1 (by rfl) ⟨932885, by rfl⟩ : syracuseStep 1243847 = 1865771) B1865771
theorem B1399495 : Blo 1242439 1399495 := bstep (se 1 (by rfl) ⟨1049621, by rfl⟩ : syracuseStep 1399495 = 2099243) B2099243
theorem B1243867 : Blo 1242439 1243867 := bstep (se 1 (by rfl) ⟨932900, by rfl⟩ : syracuseStep 1243867 = 1865801) B1865801
theorem B7969565 : Blo 1242439 7969565 := bstep (se 3 (by rfl) ⟨1494293, by rfl⟩ : syracuseStep 7969565 = 2988587) B2988587
theorem B6298397 : Blo 1242439 6298397 := bstep (se 3 (by rfl) ⟨1180949, by rfl⟩ : syracuseStep 6298397 = 2361899) B2361899
theorem B1243943 : Blo 1242439 1243943 := bstep (se 1 (by rfl) ⟨932957, by rfl⟩ : syracuseStep 1243943 = 1865915) B1865915
theorem B1243983 : Blo 1242439 1243983 := bstep (se 1 (by rfl) ⟨932987, by rfl⟩ : syracuseStep 1243983 = 1865975) B1865975
theorem B2988895 : Blo 1242439 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B1243999 : Blo 1242439 1243999 := bstep (se 1 (by rfl) ⟨932999, by rfl⟩ : syracuseStep 1243999 = 1865999) B1865999
theorem B1244027 : Blo 1242439 1244027 := bstep (se 1 (by rfl) ⟨933020, by rfl⟩ : syracuseStep 1244027 = 1866041) B1866041
theorem B1244079 : Blo 1242439 1244079 := bstep (se 1 (by rfl) ⟨933059, by rfl⟩ : syracuseStep 1244079 = 1866119) B1866119
theorem B1244103 : Blo 1242439 1244103 := bstep (se 1 (by rfl) ⟨933077, by rfl⟩ : syracuseStep 1244103 = 1866155) B1866155
theorem B1244123 : Blo 1242439 1244123 := bstep (se 1 (by rfl) ⟨933092, by rfl⟩ : syracuseStep 1244123 = 1866185) B1866185
theorem B1244199 : Blo 1242439 1244199 := bstep (se 1 (by rfl) ⟨933149, by rfl⟩ : syracuseStep 1244199 = 1866299) B1866299
theorem B1244239 : Blo 1242439 1244239 := bstep (se 1 (by rfl) ⟨933179, by rfl⟩ : syracuseStep 1244239 = 1866359) B1866359
theorem B1244255 : Blo 1242439 1244255 := bstep (se 1 (by rfl) ⟨933191, by rfl⟩ : syracuseStep 1244255 = 1866383) B1866383
theorem B1244283 : Blo 1242439 1244283 := bstep (se 1 (by rfl) ⟨933212, by rfl⟩ : syracuseStep 1244283 = 1866425) B1866425
theorem B5381273 : Blo 1242439 5381273 := bstep (se 2 (by rfl) ⟨2017977, by rfl⟩ : syracuseStep 5381273 = 4035955) B4035955
theorem B1244335 : Blo 1242439 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B1244359 : Blo 1242439 1244359 := bstep (se 1 (by rfl) ⟨933269, by rfl⟩ : syracuseStep 1244359 = 1866539) B1866539
theorem B1244379 : Blo 1242439 1244379 := bstep (se 1 (by rfl) ⟨933284, by rfl⟩ : syracuseStep 1244379 = 1866569) B1866569
theorem B7077293 : Blo 1242439 7077293 := bstep (se 3 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 7077293 = 2653985) B2653985
theorem B5979635 : Blo 1242439 5979635 := bstep (se 1 (by rfl) ⟨4484726, by rfl⟩ : syracuseStep 5979635 = 8969453) B8969453
theorem B4193801 : Blo 1242439 4193801 := bstep (se 2 (by rfl) ⟨1572675, by rfl⟩ : syracuseStep 4193801 = 3145351) B3145351
theorem B2358983 : Blo 1242439 2358983 := bstep (se 1 (by rfl) ⟨1769237, by rfl⟩ : syracuseStep 2358983 = 3538475) B3538475
theorem B7085789 : Blo 1242439 7085789 := bstep (se 3 (by rfl) ⟨1328585, by rfl⟩ : syracuseStep 7085789 = 2657171) B2657171
theorem B2096887 : Blo 1242439 2096887 := bstep (se 1 (by rfl) ⟨1572665, by rfl⟩ : syracuseStep 2096887 = 3145331) B3145331
theorem B1261391 : Blo 1242439 1261391 := bstep (se 1 (by rfl) ⟨946043, by rfl⟩ : syracuseStep 1261391 = 1892087) B1892087
theorem B1990495 : Blo 1242439 1990495 := bstep (se 1 (by rfl) ⟨1492871, by rfl⟩ : syracuseStep 1990495 = 2985743) B2985743
theorem B2359135 : Blo 1242439 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B21520247 : Blo 1242439 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B3145655 : Blo 1242439 3145655 := bstep (se 1 (by rfl) ⟨2359241, by rfl⟩ : syracuseStep 3145655 = 4718483) B4718483
theorem B2097083 : Blo 1242439 2097083 := bstep (se 1 (by rfl) ⟨1572812, by rfl⟩ : syracuseStep 2097083 = 3145625) B3145625
theorem B11337659 : Blo 1242439 11337659 := bstep (se 1 (by rfl) ⟨8503244, by rfl⟩ : syracuseStep 11337659 = 17006489) B17006489
theorem B3146303 : Blo 1242439 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B1679935 : Blo 1242439 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B2392649 : Blo 1242439 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B2097785 : Blo 1242439 2097785 := bstep (se 2 (by rfl) ⟨786669, by rfl⟩ : syracuseStep 2097785 = 1573339) B1573339
theorem B2097839 : Blo 1242439 2097839 := bstep (se 1 (by rfl) ⟨1573379, by rfl⟩ : syracuseStep 2097839 = 3146759) B3146759
theorem B1327919 : Blo 1242439 1327919 := bstep (se 1 (by rfl) ⟨995939, by rfl⟩ : syracuseStep 1327919 = 1991879) B1991879
theorem B4195151 : Blo 1242439 4195151 := bstep (se 1 (by rfl) ⟨3146363, by rfl⟩ : syracuseStep 4195151 = 6292727) B6292727
theorem B7078751 : Blo 1242439 7078751 := bstep (se 1 (by rfl) ⟨5309063, by rfl⟩ : syracuseStep 7078751 = 10618127) B10618127
theorem B2098075 : Blo 1242439 2098075 := bstep (se 1 (by rfl) ⟨1573556, by rfl⟩ : syracuseStep 2098075 = 3147113) B3147113
theorem B6718439 : Blo 1242439 6718439 := bstep (se 1 (by rfl) ⟨5038829, by rfl⟩ : syracuseStep 6718439 = 10077659) B10077659
theorem B7087247 : Blo 1242439 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B4195475 : Blo 1242439 4195475 := bstep (se 1 (by rfl) ⟨3146606, by rfl⟩ : syracuseStep 4195475 = 6293213) B6293213
theorem B3146951 : Blo 1242439 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B3146971 : Blo 1242439 3146971 := bstep (se 1 (by rfl) ⟨2360228, by rfl⟩ : syracuseStep 3146971 = 4720457) B4720457
theorem B1574255 : Blo 1242439 1574255 := bstep (se 1 (by rfl) ⟨1180691, by rfl⟩ : syracuseStep 1574255 = 2361383) B2361383
theorem B5973371 : Blo 1242439 5973371 := bstep (se 1 (by rfl) ⟨4480028, by rfl⟩ : syracuseStep 5973371 = 8960057) B8960057
theorem B4195745 : Blo 1242439 4195745 := bstep (se 2 (by rfl) ⟨1573404, by rfl⟩ : syracuseStep 4195745 = 3146809) B3146809
theorem B1574311 : Blo 1242439 1574311 := bstep (se 1 (by rfl) ⟨1180733, by rfl⟩ : syracuseStep 1574311 = 2361467) B2361467
theorem B2360927 : Blo 1242439 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B1574635 : Blo 1242439 1574635 := bstep (se 1 (by rfl) ⟨1180976, by rfl⟩ : syracuseStep 1574635 = 2361953) B2361953
theorem B23004971 : Blo 1242439 23004971 := bstep (se 1 (by rfl) ⟨17253728, by rfl⟩ : syracuseStep 23004971 = 34507457) B34507457
theorem B4540367 : Blo 1242439 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B6293537 : Blo 1242439 6293537 := bstep (se 2 (by rfl) ⟨2360076, by rfl⟩ : syracuseStep 6293537 = 4720153) B4720153
theorem B21235769 : Blo 1242439 21235769 := bstep (se 2 (by rfl) ⟨7963413, by rfl⟩ : syracuseStep 21235769 = 15926827) B15926827
theorem B8079545 : Blo 1242439 8079545 := bstep (se 2 (by rfl) ⟨3029829, by rfl⟩ : syracuseStep 8079545 = 6059659) B6059659
theorem B6293699 : Blo 1242439 6293699 := bstep (se 1 (by rfl) ⟨4720274, by rfl⟩ : syracuseStep 6293699 = 9440549) B9440549
theorem B4098313 : Blo 1242439 4098313 := bstep (se 2 (by rfl) ⟨1536867, by rfl⟩ : syracuseStep 4098313 = 3073735) B3073735
theorem B57387325 : Blo 1242439 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B2795849 : Blo 1242439 2795849 := bstep (se 2 (by rfl) ⟨1048443, by rfl⟩ : syracuseStep 2795849 = 2096887) B2096887
theorem B3148105 : Blo 1242439 3148105 := bstep (se 2 (by rfl) ⟨1180539, by rfl⟩ : syracuseStep 3148105 = 2361079) B2361079
theorem B2795867 : Blo 1242439 2795867 := bstep (se 1 (by rfl) ⟨2096900, by rfl⟩ : syracuseStep 2795867 = 4193801) B4193801
theorem B2099567 : Blo 1242439 2099567 := bstep (se 1 (by rfl) ⟨1574675, by rfl⟩ : syracuseStep 2099567 = 3149351) B3149351
theorem B1493371 : Blo 1242439 1493371 := bstep (se 1 (by rfl) ⟨1120028, by rfl⟩ : syracuseStep 1493371 = 2240057) B2240057
theorem B14174675 : Blo 1242439 14174675 := bstep (se 1 (by rfl) ⟨10631006, by rfl⟩ : syracuseStep 14174675 = 21262013) B21262013
theorem B2099783 : Blo 1242439 2099783 := bstep (se 1 (by rfl) ⟨1574837, by rfl⟩ : syracuseStep 2099783 = 3149675) B3149675
theorem B3148409 : Blo 1242439 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B5311115 : Blo 1242439 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B66390749 : Blo 1242439 66390749 := bstep (se 3 (by rfl) ⟨12448265, by rfl⟩ : syracuseStep 66390749 = 24896531) B24896531
theorem B4721399 : Blo 1242439 4721399 := bstep (se 1 (by rfl) ⟨3541049, by rfl⟩ : syracuseStep 4721399 = 7082099) B7082099
theorem B2796443 : Blo 1242439 2796443 := bstep (se 1 (by rfl) ⟨2097332, by rfl⟩ : syracuseStep 2796443 = 4194665) B4194665
theorem B5311403 : Blo 1242439 5311403 := bstep (se 1 (by rfl) ⟨3983552, by rfl⟩ : syracuseStep 5311403 = 7967105) B7967105
theorem B2796641 : Blo 1242439 2796641 := bstep (se 2 (by rfl) ⟨1048740, by rfl⟩ : syracuseStep 2796641 = 2097481) B2097481
theorem B2837791 : Blo 1242439 2837791 := bstep (se 1 (by rfl) ⟨2128343, by rfl⟩ : syracuseStep 2837791 = 4256687) B4256687
theorem B2796839 : Blo 1242439 2796839 := bstep (se 1 (by rfl) ⟨2097629, by rfl⟩ : syracuseStep 2796839 = 4195259) B4195259
theorem B8965505 : Blo 1242439 8965505 := bstep (se 2 (by rfl) ⟨3362064, by rfl⟩ : syracuseStep 8965505 = 6724129) B6724129
theorem B7081415 : Blo 1242439 7081415 := bstep (se 1 (by rfl) ⟨5311061, by rfl⟩ : syracuseStep 7081415 = 10622123) B10622123
theorem B3190279 : Blo 1242439 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B5385811 : Blo 1242439 5385811 := bstep (se 1 (by rfl) ⟨4039358, by rfl⟩ : syracuseStep 5385811 = 8078717) B8078717
theorem B2797217 : Blo 1242439 2797217 := bstep (se 2 (by rfl) ⟨1048956, by rfl⟩ : syracuseStep 2797217 = 2097913) B2097913
theorem B9441035 : Blo 1242439 9441035 := bstep (se 1 (by rfl) ⟨7080776, by rfl⟩ : syracuseStep 9441035 = 14161553) B14161553
theorem B3985193 : Blo 1242439 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B2797577 : Blo 1242439 2797577 := bstep (se 2 (by rfl) ⟨1049091, by rfl⟩ : syracuseStep 2797577 = 2098183) B2098183
theorem B1863785 : Blo 1242439 1863785 := bstep (se 2 (by rfl) ⟨698919, by rfl⟩ : syracuseStep 1863785 = 1397839) B1397839
theorem B45363473 : Blo 1242439 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B32739719 : Blo 1242439 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B1864103 : Blo 1242439 1864103 := bstep (se 1 (by rfl) ⟨1398077, by rfl⟩ : syracuseStep 1864103 = 2796155) B2796155
theorem B2797991 : Blo 1242439 2797991 := bstep (se 1 (by rfl) ⟨2098493, by rfl⟩ : syracuseStep 2797991 = 4196987) B4196987
theorem B1864187 : Blo 1242439 1864187 := bstep (se 1 (by rfl) ⟨1398140, by rfl⟩ : syracuseStep 1864187 = 2796281) B2796281
theorem B2798099 : Blo 1242439 2798099 := bstep (se 1 (by rfl) ⟨2098574, by rfl⟩ : syracuseStep 2798099 = 4197149) B4197149
theorem B5313043 : Blo 1242439 5313043 := bstep (se 1 (by rfl) ⟨3984782, by rfl⟩ : syracuseStep 5313043 = 7969565) B7969565
theorem B4198931 : Blo 1242439 4198931 := bstep (se 1 (by rfl) ⟨3149198, by rfl⟩ : syracuseStep 4198931 = 6298397) B6298397
theorem B2798153 : Blo 1242439 2798153 := bstep (se 2 (by rfl) ⟨1049307, by rfl⟩ : syracuseStep 2798153 = 2098615) B2098615
theorem B1864313 : Blo 1242439 1864313 := bstep (se 2 (by rfl) ⟨699117, by rfl⟩ : syracuseStep 1864313 = 1398235) B1398235
theorem B1864367 : Blo 1242439 1864367 := bstep (se 1 (by rfl) ⟨1398275, by rfl⟩ : syracuseStep 1864367 = 2796551) B2796551
theorem B5976791 : Blo 1242439 5976791 := bstep (se 1 (by rfl) ⟨4482593, by rfl⟩ : syracuseStep 5976791 = 8965187) B8965187
theorem B1864415 : Blo 1242439 1864415 := bstep (se 1 (by rfl) ⟨1398311, by rfl⟩ : syracuseStep 1864415 = 2796623) B2796623
theorem B3363709 : Blo 1242439 3363709 := bstep (se 3 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 3363709 = 1261391) B1261391
theorem B1864679 : Blo 1242439 1864679 := bstep (se 1 (by rfl) ⟨1398509, by rfl⟩ : syracuseStep 1864679 = 2797019) B2797019
theorem B2798567 : Blo 1242439 2798567 := bstep (se 1 (by rfl) ⟨2098925, by rfl⟩ : syracuseStep 2798567 = 4197851) B4197851
theorem B2241527 : Blo 1242439 2241527 := bstep (se 1 (by rfl) ⟨1681145, by rfl⟩ : syracuseStep 2241527 = 3362291) B3362291
theorem B3986423 : Blo 1242439 3986423 := bstep (se 1 (by rfl) ⟨2989817, by rfl⟩ : syracuseStep 3986423 = 5979635) B5979635
theorem B10630187 : Blo 1242439 10630187 := bstep (se 1 (by rfl) ⟨7972640, by rfl⟩ : syracuseStep 10630187 = 15945281) B15945281
theorem B4723859 : Blo 1242439 4723859 := bstep (se 1 (by rfl) ⟨3542894, by rfl⟩ : syracuseStep 4723859 = 7085789) B7085789
theorem B1864937 : Blo 1242439 1864937 := bstep (se 2 (by rfl) ⟨699351, by rfl⟩ : syracuseStep 1864937 = 1398703) B1398703
theorem B1864991 : Blo 1242439 1864991 := bstep (se 1 (by rfl) ⟨1398743, by rfl⟩ : syracuseStep 1864991 = 2797487) B2797487
theorem B1398055 : Blo 1242439 1398055 := bstep (se 1 (by rfl) ⟨1048541, by rfl⟩ : syracuseStep 1398055 = 2097083) B2097083
theorem B7558439 : Blo 1242439 7558439 := bstep (se 1 (by rfl) ⟨5668829, by rfl⟩ : syracuseStep 7558439 = 11337659) B11337659
theorem B1242459 : Blo 1242439 1242459 := bstep (se 1 (by rfl) ⟨931844, by rfl⟩ : syracuseStep 1242459 = 1863689) B1863689
theorem B2798945 : Blo 1242439 2798945 := bstep (se 2 (by rfl) ⟨1049604, by rfl⟩ : syracuseStep 2798945 = 2099209) B2099209
theorem B1242479 : Blo 1242439 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B1398127 : Blo 1242439 1398127 := bstep (se 1 (by rfl) ⟨1048595, by rfl⟩ : syracuseStep 1398127 = 2097191) B2097191
theorem B1889659 : Blo 1242439 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B1242535 : Blo 1242439 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B2799035 : Blo 1242439 2799035 := bstep (se 1 (by rfl) ⟨2099276, by rfl⟩ : syracuseStep 2799035 = 4198553) B4198553
theorem B1865159 : Blo 1242439 1865159 := bstep (se 1 (by rfl) ⟨1398869, by rfl⟩ : syracuseStep 1865159 = 2797739) B2797739
theorem B1242619 : Blo 1242439 1242619 := bstep (se 1 (by rfl) ⟨931964, by rfl⟩ : syracuseStep 1242619 = 1863929) B1863929
theorem B10622501 : Blo 1242439 10622501 := bstep (se 4 (by rfl) ⟨995859, by rfl⟩ : syracuseStep 10622501 = 1991719) B1991719
theorem B7083557 : Blo 1242439 7083557 := bstep (se 4 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 7083557 = 1328167) B1328167
theorem B15922727 : Blo 1242439 15922727 := bstep (se 1 (by rfl) ⟨11942045, by rfl⟩ : syracuseStep 15922727 = 23884091) B23884091
theorem B2799161 : Blo 1242439 2799161 := bstep (se 2 (by rfl) ⟨1049685, by rfl⟩ : syracuseStep 2799161 = 2099371) B2099371
theorem B1242687 : Blo 1242439 1242687 := bstep (se 1 (by rfl) ⟨932015, by rfl⟩ : syracuseStep 1242687 = 1864031) B1864031
theorem B1242695 : Blo 1242439 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B1398343 : Blo 1242439 1398343 := bstep (se 1 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 1398343 = 2097515) B2097515
theorem B22697657 : Blo 1242439 22697657 := bstep (se 2 (by rfl) ⟨8511621, by rfl⟩ : syracuseStep 22697657 = 17023243) B17023243
theorem B1242847 : Blo 1242439 1242847 := bstep (se 1 (by rfl) ⟨932135, by rfl⟩ : syracuseStep 1242847 = 1864271) B1864271
theorem B14350061 : Blo 1242439 14350061 := bstep (se 3 (by rfl) ⟨2690636, by rfl⟩ : syracuseStep 14350061 = 5381273) B5381273
theorem B1865513 : Blo 1242439 1865513 := bstep (se 2 (by rfl) ⟨699567, by rfl⟩ : syracuseStep 1865513 = 1399135) B1399135
theorem B1242927 : Blo 1242439 1242927 := bstep (se 1 (by rfl) ⟨932195, by rfl⟩ : syracuseStep 1242927 = 1864391) B1864391
theorem B1865519 : Blo 1242439 1865519 := bstep (se 1 (by rfl) ⟨1399139, by rfl⟩ : syracuseStep 1865519 = 2798279) B2798279
theorem B6297425 : Blo 1242439 6297425 := bstep (se 2 (by rfl) ⟨2361534, by rfl⟩ : syracuseStep 6297425 = 4723069) B4723069
theorem B1243035 : Blo 1242439 1243035 := bstep (se 1 (by rfl) ⟨932276, by rfl⟩ : syracuseStep 1243035 = 1864553) B1864553
theorem B1243087 : Blo 1242439 1243087 := bstep (se 1 (by rfl) ⟨932315, by rfl⟩ : syracuseStep 1243087 = 1864631) B1864631
theorem B1243111 : Blo 1242439 1243111 := bstep (se 1 (by rfl) ⟨932333, by rfl⟩ : syracuseStep 1243111 = 1864667) B1864667
theorem B6379715 : Blo 1242439 6379715 := bstep (se 1 (by rfl) ⟨4784786, by rfl⟩ : syracuseStep 6379715 = 9569573) B9569573
theorem B2799827 : Blo 1242439 2799827 := bstep (se 1 (by rfl) ⟨2099870, by rfl⟩ : syracuseStep 2799827 = 4199741) B4199741
theorem B5675255 : Blo 1242439 5675255 := bstep (se 1 (by rfl) ⟨4256441, by rfl⟩ : syracuseStep 5675255 = 8512883) B8512883
theorem B1865993 : Blo 1242439 1865993 := bstep (se 2 (by rfl) ⟨699747, by rfl⟩ : syracuseStep 1865993 = 1399495) B1399495
theorem B2799881 : Blo 1242439 2799881 := bstep (se 2 (by rfl) ⟨1049955, by rfl⟩ : syracuseStep 2799881 = 2099911) B2099911
theorem B1243423 : Blo 1242439 1243423 := bstep (se 1 (by rfl) ⟨932567, by rfl⟩ : syracuseStep 1243423 = 1865135) B1865135
theorem B1243483 : Blo 1242439 1243483 := bstep (se 1 (by rfl) ⟨932612, by rfl⟩ : syracuseStep 1243483 = 1865225) B1865225
theorem B1243503 : Blo 1242439 1243503 := bstep (se 1 (by rfl) ⟨932627, by rfl⟩ : syracuseStep 1243503 = 1865255) B1865255
theorem B1866095 : Blo 1242439 1866095 := bstep (se 1 (by rfl) ⟨1399571, by rfl⟩ : syracuseStep 1866095 = 2799143) B2799143
theorem B11958653 : Blo 1242439 11958653 := bstep (se 3 (by rfl) ⟨2242247, by rfl⟩ : syracuseStep 11958653 = 4484495) B4484495
theorem B1243559 : Blo 1242439 1243559 := bstep (se 1 (by rfl) ⟨932669, by rfl⟩ : syracuseStep 1243559 = 1865339) B1865339
theorem B1399207 : Blo 1242439 1399207 := bstep (se 1 (by rfl) ⟨1049405, by rfl⟩ : syracuseStep 1399207 = 2098811) B2098811
theorem B1243643 : Blo 1242439 1243643 := bstep (se 1 (by rfl) ⟨932732, by rfl⟩ : syracuseStep 1243643 = 1865465) B1865465
theorem B14154263 : Blo 1242439 14154263 := bstep (se 1 (by rfl) ⟨10615697, by rfl⟩ : syracuseStep 14154263 = 21231395) B21231395
theorem B7084583 : Blo 1242439 7084583 := bstep (se 1 (by rfl) ⟨5313437, by rfl⟩ : syracuseStep 7084583 = 10626875) B10626875
theorem B1243711 : Blo 1242439 1243711 := bstep (se 1 (by rfl) ⟨932783, by rfl⟩ : syracuseStep 1243711 = 1865567) B1865567
theorem B1243719 : Blo 1242439 1243719 := bstep (se 1 (by rfl) ⟨932789, by rfl⟩ : syracuseStep 1243719 = 1865579) B1865579
theorem B1866311 : Blo 1242439 1866311 := bstep (se 1 (by rfl) ⟨1399733, by rfl⟩ : syracuseStep 1866311 = 2799467) B2799467
theorem B1866347 : Blo 1242439 1866347 := bstep (se 1 (by rfl) ⟨1399760, by rfl⟩ : syracuseStep 1866347 = 2799521) B2799521
theorem B6298235 : Blo 1242439 6298235 := bstep (se 1 (by rfl) ⟨4723676, by rfl⟩ : syracuseStep 6298235 = 9447353) B9447353
theorem B1243871 : Blo 1242439 1243871 := bstep (se 1 (by rfl) ⟨932903, by rfl⟩ : syracuseStep 1243871 = 1865807) B1865807
theorem B6380311 : Blo 1242439 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B1243951 : Blo 1242439 1243951 := bstep (se 1 (by rfl) ⟨932963, by rfl⟩ : syracuseStep 1243951 = 1865927) B1865927
theorem B26893129 : Blo 1242439 26893129 := bstep (se 2 (by rfl) ⟨10084923, by rfl⟩ : syracuseStep 26893129 = 20169847) B20169847
theorem B1866575 : Blo 1242439 1866575 := bstep (se 1 (by rfl) ⟨1399931, by rfl⟩ : syracuseStep 1866575 = 2799863) B2799863
theorem B21535631 : Blo 1242439 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B10623899 : Blo 1242439 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B1244059 : Blo 1242439 1244059 := bstep (se 1 (by rfl) ⟨933044, by rfl⟩ : syracuseStep 1244059 = 1866089) B1866089
theorem B1244111 : Blo 1242439 1244111 := bstep (se 1 (by rfl) ⟨933083, by rfl⟩ : syracuseStep 1244111 = 1866167) B1866167
theorem B1244135 : Blo 1242439 1244135 := bstep (se 1 (by rfl) ⟨933101, by rfl⟩ : syracuseStep 1244135 = 1866203) B1866203
theorem B1399783 : Blo 1242439 1399783 := bstep (se 1 (by rfl) ⟨1049837, by rfl⟩ : syracuseStep 1399783 = 2099675) B2099675
theorem B5979251 : Blo 1242439 5979251 := bstep (se 1 (by rfl) ⟨4484438, by rfl⟩ : syracuseStep 5979251 = 8968877) B8968877
theorem B3538043 : Blo 1242439 3538043 := bstep (se 1 (by rfl) ⟨2653532, by rfl⟩ : syracuseStep 3538043 = 5307065) B5307065
theorem B4250747 : Blo 1242439 4250747 := bstep (se 1 (by rfl) ⟨3188060, by rfl⟩ : syracuseStep 4250747 = 6376121) B6376121
theorem B3980477 : Blo 1242439 3980477 := bstep (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) B1492679
theorem B6290621 : Blo 1242439 6290621 := bstep (se 3 (by rfl) ⟨1179491, by rfl⟩ : syracuseStep 6290621 = 2358983) B2358983
theorem B5979521 : Blo 1242439 5979521 := bstep (se 2 (by rfl) ⟨2242320, by rfl⟩ : syracuseStep 5979521 = 4484641) B4484641
theorem B2989511 : Blo 1242439 2989511 := bstep (se 1 (by rfl) ⟨2242133, by rfl⟩ : syracuseStep 2989511 = 4484267) B4484267
theorem B9444923 : Blo 1242439 9444923 := bstep (se 1 (by rfl) ⟨7083692, by rfl⟩ : syracuseStep 9444923 = 14167385) B14167385
theorem B1515071 : Blo 1242439 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B4718195 : Blo 1242439 4718195 := bstep (se 1 (by rfl) ⟨3538646, by rfl⟩ : syracuseStep 4718195 = 7077293) B7077293
theorem B2653993 : Blo 1242439 2653993 := bstep (se 2 (by rfl) ⟨995247, by rfl⟩ : syracuseStep 2653993 = 1990495) B1990495
theorem B3145513 : Blo 1242439 3145513 := bstep (se 2 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 3145513 = 2359135) B2359135
theorem B6381359 : Blo 1242439 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B2097103 : Blo 1242439 2097103 := bstep (se 1 (by rfl) ⟨1572827, by rfl⟩ : syracuseStep 2097103 = 3145655) B3145655
theorem B5464417 : Blo 1242439 5464417 := bstep (se 2 (by rfl) ⟨2049156, by rfl⟩ : syracuseStep 5464417 = 4098313) B4098313
theorem B2097535 : Blo 1242439 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B21545453 : Blo 1242439 21545453 := bstep (se 3 (by rfl) ⟨4039772, by rfl⟩ : syracuseStep 21545453 = 8079545) B8079545
theorem B14164469 : Blo 1242439 14164469 := bstep (se 5 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 14164469 = 1327919) B1327919
theorem B1991161 : Blo 1242439 1991161 := bstep (se 2 (by rfl) ⟨746685, by rfl⟩ : syracuseStep 1991161 = 1493371) B1493371
theorem B4719167 : Blo 1242439 4719167 := bstep (se 1 (by rfl) ⟨3539375, by rfl⟩ : syracuseStep 4719167 = 7078751) B7078751
theorem B7086791 : Blo 1242439 7086791 := bstep (se 1 (by rfl) ⟨5315093, by rfl⟩ : syracuseStep 7086791 = 10630187) B10630187
theorem B2097967 : Blo 1242439 2097967 := bstep (se 1 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 2097967 = 3146951) B3146951
theorem B3982247 : Blo 1242439 3982247 := bstep (se 1 (by rfl) ⟨2986685, by rfl⟩ : syracuseStep 3982247 = 5973371) B5973371
theorem B35857505 : Blo 1242439 35857505 := bstep (se 2 (by rfl) ⟨13446564, by rfl⟩ : syracuseStep 35857505 = 26893129) B26893129
theorem B15131771 : Blo 1242439 15131771 := bstep (se 1 (by rfl) ⟨11348828, by rfl⟩ : syracuseStep 15131771 = 22697657) B22697657
theorem B15336647 : Blo 1242439 15336647 := bstep (se 1 (by rfl) ⟨11502485, by rfl⟩ : syracuseStep 15336647 = 23004971) B23004971
theorem B4195691 : Blo 1242439 4195691 := bstep (se 1 (by rfl) ⟨3146768, by rfl⟩ : syracuseStep 4195691 = 6293537) B6293537
theorem B14157179 : Blo 1242439 14157179 := bstep (se 1 (by rfl) ⟨10617884, by rfl⟩ : syracuseStep 14157179 = 21235769) B21235769
theorem B4195799 : Blo 1242439 4195799 := bstep (se 1 (by rfl) ⟨3146849, by rfl⟩ : syracuseStep 4195799 = 6293699) B6293699
theorem B4253143 : Blo 1242439 4253143 := bstep (se 1 (by rfl) ⟨3189857, by rfl⟩ : syracuseStep 4253143 = 6379715) B6379715
theorem B4040189 : Blo 1242439 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B7972435 : Blo 1242439 7972435 := bstep (se 1 (by rfl) ⟨5979326, by rfl⟩ : syracuseStep 7972435 = 11958653) B11958653
theorem B4195961 : Blo 1242439 4195961 := bstep (se 2 (by rfl) ⟨1573485, by rfl⟩ : syracuseStep 4195961 = 3146971) B3146971
theorem B2098939 : Blo 1242439 2098939 := bstep (se 1 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 2098939 = 3148409) B3148409
theorem B3540743 : Blo 1242439 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B3147599 : Blo 1242439 3147599 := bstep (se 1 (by rfl) ⟨2360699, by rfl⟩ : syracuseStep 3147599 = 4721399) B4721399
theorem B2099081 : Blo 1242439 2099081 := bstep (se 2 (by rfl) ⟨787155, by rfl⟩ : syracuseStep 2099081 = 1574311) B1574311
theorem B3540935 : Blo 1242439 3540935 := bstep (se 1 (by rfl) ⟨2655701, by rfl⟩ : syracuseStep 3540935 = 5311403) B5311403
theorem B38266829 : Blo 1242439 38266829 := bstep (se 3 (by rfl) ⟨7175030, by rfl⟩ : syracuseStep 38266829 = 14350061) B14350061
theorem B10078181 : Blo 1242439 10078181 := bstep (se 4 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 10078181 = 1889659) B1889659
theorem B4253705 : Blo 1242439 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B4720943 : Blo 1242439 4720943 := bstep (se 1 (by rfl) ⟨3540707, by rfl⟩ : syracuseStep 4720943 = 7081415) B7081415
theorem B1993007 : Blo 1242439 1993007 := bstep (se 1 (by rfl) ⟨1494755, by rfl⟩ : syracuseStep 1993007 = 2989511) B2989511
theorem B2099513 : Blo 1242439 2099513 := bstep (se 2 (by rfl) ⟨787317, by rfl⟩ : syracuseStep 2099513 = 1574635) B1574635
theorem B6294023 : Blo 1242439 6294023 := bstep (se 1 (by rfl) ⟨4720517, by rfl⟩ : syracuseStep 6294023 = 9441035) B9441035
theorem B2656795 : Blo 1242439 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B4254239 : Blo 1242439 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B2796137 : Blo 1242439 2796137 := bstep (se 2 (by rfl) ⟨1048551, by rfl⟩ : syracuseStep 2796137 = 2097103) B2097103
theorem B76516433 : Blo 1242439 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B4197473 : Blo 1242439 4197473 := bstep (se 2 (by rfl) ⟨1574052, by rfl⟩ : syracuseStep 4197473 = 3148105) B3148105
theorem B3984527 : Blo 1242439 3984527 := bstep (se 1 (by rfl) ⟨2988395, by rfl⟩ : syracuseStep 3984527 = 5976791) B5976791
theorem B2796767 : Blo 1242439 2796767 := bstep (se 1 (by rfl) ⟨2097575, by rfl⟩ : syracuseStep 2796767 = 4195151) B4195151
theorem B2657615 : Blo 1242439 2657615 := bstep (se 1 (by rfl) ⟨1993211, by rfl⟩ : syracuseStep 2657615 = 3986423) B3986423
theorem B2239913 : Blo 1242439 2239913 := bstep (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) B1679935
theorem B2796983 : Blo 1242439 2796983 := bstep (se 1 (by rfl) ⟨2097737, by rfl⟩ : syracuseStep 2796983 = 4195475) B4195475
theorem B3149239 : Blo 1242439 3149239 := bstep (se 1 (by rfl) ⟨2361929, by rfl⟩ : syracuseStep 3149239 = 4723859) B4723859
theorem B20155837 : Blo 1242439 20155837 := bstep (se 3 (by rfl) ⟨3779219, by rfl⟩ : syracuseStep 20155837 = 7558439) B7558439
theorem B2797163 : Blo 1242439 2797163 := bstep (se 1 (by rfl) ⟨2097872, by rfl⟩ : syracuseStep 2797163 = 4195745) B4195745
theorem B4198013 : Blo 1242439 4198013 := bstep (se 3 (by rfl) ⟨787127, by rfl⟩ : syracuseStep 4198013 = 1574255) B1574255
theorem B7081667 : Blo 1242439 7081667 := bstep (se 1 (by rfl) ⟨5311250, by rfl⟩ : syracuseStep 7081667 = 10622501) B10622501
theorem B4722371 : Blo 1242439 4722371 := bstep (se 1 (by rfl) ⟨3541778, by rfl⟩ : syracuseStep 4722371 = 7083557) B7083557
theorem B8507081 : Blo 1242439 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B4484945 : Blo 1242439 4484945 := bstep (se 2 (by rfl) ⟨1681854, by rfl⟩ : syracuseStep 4484945 = 3363709) B3363709
theorem B2797433 : Blo 1242439 2797433 := bstep (se 2 (by rfl) ⟨1049037, by rfl⟩ : syracuseStep 2797433 = 2098075) B2098075
theorem B4198283 : Blo 1242439 4198283 := bstep (se 1 (by rfl) ⟨3148712, by rfl⟩ : syracuseStep 4198283 = 6297425) B6297425
theorem B3026911 : Blo 1242439 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B1863899 : Blo 1242439 1863899 := bstep (se 1 (by rfl) ⟨1397924, by rfl⟩ : syracuseStep 1863899 = 2795849) B2795849
theorem B1863911 : Blo 1242439 1863911 := bstep (se 1 (by rfl) ⟨1397933, by rfl⟩ : syracuseStep 1863911 = 2795867) B2795867
theorem B6295805 : Blo 1242439 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B9449783 : Blo 1242439 9449783 := bstep (se 1 (by rfl) ⟨7087337, by rfl⟩ : syracuseStep 9449783 = 14174675) B14174675
theorem B4723055 : Blo 1242439 4723055 := bstep (se 1 (by rfl) ⟨3542291, by rfl⟩ : syracuseStep 4723055 = 7084583) B7084583
theorem B1864073 : Blo 1242439 1864073 := bstep (se 2 (by rfl) ⟨699027, by rfl⟩ : syracuseStep 1864073 = 1398055) B1398055
theorem B4198823 : Blo 1242439 4198823 := bstep (se 1 (by rfl) ⟨3149117, by rfl⟩ : syracuseStep 4198823 = 6298235) B6298235
theorem B1864169 : Blo 1242439 1864169 := bstep (se 2 (by rfl) ⟨699063, by rfl⟩ : syracuseStep 1864169 = 1398127) B1398127
theorem B14357087 : Blo 1242439 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B1864295 : Blo 1242439 1864295 := bstep (se 1 (by rfl) ⟨1398221, by rfl⟩ : syracuseStep 1864295 = 2796443) B2796443
theorem B7082599 : Blo 1242439 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B1864427 : Blo 1242439 1864427 := bstep (se 1 (by rfl) ⟨1398320, by rfl⟩ : syracuseStep 1864427 = 2796641) B2796641
theorem B3986167 : Blo 1242439 3986167 := bstep (se 1 (by rfl) ⟨2989625, by rfl⟩ : syracuseStep 3986167 = 5979251) B5979251
theorem B1864457 : Blo 1242439 1864457 := bstep (se 2 (by rfl) ⟨699171, by rfl⟩ : syracuseStep 1864457 = 1398343) B1398343
theorem B7181081 : Blo 1242439 7181081 := bstep (se 2 (by rfl) ⟨2692905, by rfl⟩ : syracuseStep 7181081 = 5385811) B5385811
theorem B1864559 : Blo 1242439 1864559 := bstep (se 1 (by rfl) ⟨1398419, by rfl⟩ : syracuseStep 1864559 = 2796839) B2796839
theorem B5977003 : Blo 1242439 5977003 := bstep (se 1 (by rfl) ⟨4482752, by rfl⟩ : syracuseStep 5977003 = 8965505) B8965505
theorem B3986347 : Blo 1242439 3986347 := bstep (se 1 (by rfl) ⟨2989760, by rfl⟩ : syracuseStep 3986347 = 5979521) B5979521
theorem B6296615 : Blo 1242439 6296615 := bstep (se 1 (by rfl) ⟨4722461, by rfl⟩ : syracuseStep 6296615 = 9444923) B9444923
theorem B1864811 : Blo 1242439 1864811 := bstep (se 1 (by rfl) ⟨1398608, by rfl⟩ : syracuseStep 1864811 = 2797217) B2797217
theorem B5977405 : Blo 1242439 5977405 := bstep (se 3 (by rfl) ⟨1120763, by rfl⟩ : syracuseStep 5977405 = 2241527) B2241527
theorem B1865051 : Blo 1242439 1865051 := bstep (se 1 (by rfl) ⟨1398788, by rfl⟩ : syracuseStep 1865051 = 2797577) B2797577
theorem B1242523 : Blo 1242439 1242523 := bstep (se 1 (by rfl) ⟨931892, by rfl⟩ : syracuseStep 1242523 = 1863785) B1863785
theorem B30242315 : Blo 1242439 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B1242735 : Blo 1242439 1242735 := bstep (se 1 (by rfl) ⟨932051, by rfl⟩ : syracuseStep 1242735 = 1864103) B1864103
theorem B1865327 : Blo 1242439 1865327 := bstep (se 1 (by rfl) ⟨1398995, by rfl⟩ : syracuseStep 1865327 = 2797991) B2797991
theorem B1242791 : Blo 1242439 1242791 := bstep (se 1 (by rfl) ⟨932093, by rfl⟩ : syracuseStep 1242791 = 1864187) B1864187
theorem B1865399 : Blo 1242439 1865399 := bstep (se 1 (by rfl) ⟨1399049, by rfl⟩ : syracuseStep 1865399 = 2798099) B2798099
theorem B2799287 : Blo 1242439 2799287 := bstep (se 1 (by rfl) ⟨2099465, by rfl⟩ : syracuseStep 2799287 = 4198931) B4198931
theorem B1595099 : Blo 1242439 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B1865435 : Blo 1242439 1865435 := bstep (se 1 (by rfl) ⟨1399076, by rfl⟩ : syracuseStep 1865435 = 2798153) B2798153
theorem B1242875 : Blo 1242439 1242875 := bstep (se 1 (by rfl) ⟨932156, by rfl⟩ : syracuseStep 1242875 = 1864313) B1864313
theorem B1398523 : Blo 1242439 1398523 := bstep (se 1 (by rfl) ⟨1048892, by rfl⟩ : syracuseStep 1398523 = 2097785) B2097785
theorem B1242911 : Blo 1242439 1242911 := bstep (se 1 (by rfl) ⟨932183, by rfl⟩ : syracuseStep 1242911 = 1864367) B1864367
theorem B1398559 : Blo 1242439 1398559 := bstep (se 1 (by rfl) ⟨1048919, by rfl⟩ : syracuseStep 1398559 = 2097839) B2097839
theorem B1242943 : Blo 1242439 1242943 := bstep (se 1 (by rfl) ⟨932207, by rfl⟩ : syracuseStep 1242943 = 1864415) B1864415
theorem B1865609 : Blo 1242439 1865609 := bstep (se 2 (by rfl) ⟨699603, by rfl⟩ : syracuseStep 1865609 = 1399207) B1399207
theorem B4478959 : Blo 1242439 4478959 := bstep (se 1 (by rfl) ⟨3359219, by rfl⟩ : syracuseStep 4478959 = 6718439) B6718439
theorem B1243119 : Blo 1242439 1243119 := bstep (se 1 (by rfl) ⟨932339, by rfl⟩ : syracuseStep 1243119 = 1864679) B1864679
theorem B1865711 : Blo 1242439 1865711 := bstep (se 1 (by rfl) ⟨1399283, by rfl⟩ : syracuseStep 1865711 = 2798567) B2798567
theorem B7084057 : Blo 1242439 7084057 := bstep (se 2 (by rfl) ⟨2656521, by rfl⟩ : syracuseStep 7084057 = 5313043) B5313043
theorem B4724831 : Blo 1242439 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B1243291 : Blo 1242439 1243291 := bstep (se 1 (by rfl) ⟨932468, by rfl⟩ : syracuseStep 1243291 = 1864937) B1864937
theorem B1243327 : Blo 1242439 1243327 := bstep (se 1 (by rfl) ⟨932495, by rfl⟩ : syracuseStep 1243327 = 1864991) B1864991
theorem B1865963 : Blo 1242439 1865963 := bstep (se 1 (by rfl) ⟨1399472, by rfl⟩ : syracuseStep 1865963 = 2798945) B2798945
theorem B1866023 : Blo 1242439 1866023 := bstep (se 1 (by rfl) ⟨1399517, by rfl⟩ : syracuseStep 1866023 = 2799035) B2799035
theorem B1243439 : Blo 1242439 1243439 := bstep (se 1 (by rfl) ⟨932579, by rfl⟩ : syracuseStep 1243439 = 1865159) B1865159
theorem B10615151 : Blo 1242439 10615151 := bstep (se 1 (by rfl) ⟨7961363, by rfl⟩ : syracuseStep 10615151 = 15922727) B15922727
theorem B1866107 : Blo 1242439 1866107 := bstep (se 1 (by rfl) ⟨1399580, by rfl⟩ : syracuseStep 1866107 = 2799161) B2799161
theorem B1243675 : Blo 1242439 1243675 := bstep (se 1 (by rfl) ⟨932756, by rfl⟩ : syracuseStep 1243675 = 1865513) B1865513
theorem B1243679 : Blo 1242439 1243679 := bstep (se 1 (by rfl) ⟨932759, by rfl⟩ : syracuseStep 1243679 = 1865519) B1865519
theorem B1866377 : Blo 1242439 1866377 := bstep (se 2 (by rfl) ⟨699891, by rfl⟩ : syracuseStep 1866377 = 1399783) B1399783
theorem B349223669 : Blo 1242439 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B1866551 : Blo 1242439 1866551 := bstep (se 1 (by rfl) ⟨1399913, by rfl⟩ : syracuseStep 1866551 = 2799827) B2799827
theorem B3783503 : Blo 1242439 3783503 := bstep (se 1 (by rfl) ⟨2837627, by rfl⟩ : syracuseStep 3783503 = 5675255) B5675255
theorem B1243995 : Blo 1242439 1243995 := bstep (se 1 (by rfl) ⟨932996, by rfl⟩ : syracuseStep 1243995 = 1865993) B1865993
theorem B1866587 : Blo 1242439 1866587 := bstep (se 1 (by rfl) ⟨1399940, by rfl⟩ : syracuseStep 1866587 = 2799881) B2799881
theorem B1244063 : Blo 1242439 1244063 := bstep (se 1 (by rfl) ⟨933047, by rfl⟩ : syracuseStep 1244063 = 1866095) B1866095
theorem B1399711 : Blo 1242439 1399711 := bstep (se 1 (by rfl) ⟨1049783, by rfl⟩ : syracuseStep 1399711 = 2099567) B2099567
theorem B9436175 : Blo 1242439 9436175 := bstep (se 1 (by rfl) ⟨7077131, by rfl⟩ : syracuseStep 9436175 = 14154263) B14154263
theorem B3783721 : Blo 1242439 3783721 := bstep (se 2 (by rfl) ⟨1418895, by rfl⟩ : syracuseStep 3783721 = 2837791) B2837791
theorem B1244207 : Blo 1242439 1244207 := bstep (se 1 (by rfl) ⟨933155, by rfl⟩ : syracuseStep 1244207 = 1866311) B1866311
theorem B1399855 : Blo 1242439 1399855 := bstep (se 1 (by rfl) ⟨1049891, by rfl⟩ : syracuseStep 1399855 = 2099783) B2099783
theorem B1244231 : Blo 1242439 1244231 := bstep (se 1 (by rfl) ⟨933173, by rfl⟩ : syracuseStep 1244231 = 1866347) B1866347
theorem B44260499 : Blo 1242439 44260499 := bstep (se 1 (by rfl) ⟨33195374, by rfl⟩ : syracuseStep 44260499 = 66390749) B66390749
theorem B1244383 : Blo 1242439 1244383 := bstep (se 1 (by rfl) ⟨933287, by rfl⟩ : syracuseStep 1244383 = 1866575) B1866575
theorem B2358695 : Blo 1242439 2358695 := bstep (se 1 (by rfl) ⟨1769021, by rfl⟩ : syracuseStep 2358695 = 3538043) B3538043
theorem B2833831 : Blo 1242439 2833831 := bstep (se 1 (by rfl) ⟨2125373, by rfl⟩ : syracuseStep 2833831 = 4250747) B4250747
theorem B2653651 : Blo 1242439 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B4193747 : Blo 1242439 4193747 := bstep (se 1 (by rfl) ⟨3145310, by rfl⟩ : syracuseStep 4193747 = 6290621) B6290621
theorem B3538657 : Blo 1242439 3538657 := bstep (se 2 (by rfl) ⟨1326996, by rfl⟩ : syracuseStep 3538657 = 2653993) B2653993
theorem B4194017 : Blo 1242439 4194017 := bstep (se 2 (by rfl) ⟨1572756, by rfl⟩ : syracuseStep 4194017 = 3145513) B3145513
theorem B3145463 : Blo 1242439 3145463 := bstep (se 1 (by rfl) ⟨2359097, by rfl⟩ : syracuseStep 3145463 = 4718195) B4718195
theorem B9445409 : Blo 1242439 9445409 := bstep (se 2 (by rfl) ⟨3542028, by rfl⟩ : syracuseStep 9445409 = 7084057) B7084057
theorem B6299855 : Blo 1242439 6299855 := bstep (se 1 (by rfl) ⟨4724891, by rfl⟩ : syracuseStep 6299855 = 9449783) B9449783
theorem B3146111 : Blo 1242439 3146111 := bstep (se 1 (by rfl) ⟨2359583, by rfl⟩ : syracuseStep 3146111 = 4719167) B4719167
theorem B2654831 : Blo 1242439 2654831 := bstep (se 1 (by rfl) ⟨1991123, by rfl⟩ : syracuseStep 2654831 = 3982247) B3982247
theorem B23905003 : Blo 1242439 23905003 := bstep (se 1 (by rfl) ⟨17928752, by rfl⟩ : syracuseStep 23905003 = 35857505) B35857505
theorem B10224431 : Blo 1242439 10224431 := bstep (se 1 (by rfl) ⟨7668323, by rfl⟩ : syracuseStep 10224431 = 15336647) B15336647
theorem B7086973 : Blo 1242439 7086973 := bstep (se 3 (by rfl) ⟨1328807, by rfl⟩ : syracuseStep 7086973 = 2657615) B2657615
theorem B9438119 : Blo 1242439 9438119 := bstep (se 1 (by rfl) ⟨7078589, by rfl⟩ : syracuseStep 9438119 = 14157179) B14157179
theorem B20161543 : Blo 1242439 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B5973101 : Blo 1242439 5973101 := bstep (se 3 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 5973101 = 2239913) B2239913
theorem B2360495 : Blo 1242439 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B2098399 : Blo 1242439 2098399 := bstep (se 1 (by rfl) ⟨1573799, by rfl⟩ : syracuseStep 2098399 = 3147599) B3147599
theorem B25511219 : Blo 1242439 25511219 := bstep (se 1 (by rfl) ⟨19133414, by rfl⟩ : syracuseStep 25511219 = 38266829) B38266829
theorem B6718787 : Blo 1242439 6718787 := bstep (se 1 (by rfl) ⟨5039090, by rfl⟩ : syracuseStep 6718787 = 10078181) B10078181
theorem B2835803 : Blo 1242439 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B3147295 : Blo 1242439 3147295 := bstep (se 1 (by rfl) ⟨2360471, by rfl⟩ : syracuseStep 3147295 = 4720943) B4720943
theorem B1328671 : Blo 1242439 1328671 := bstep (se 1 (by rfl) ⟨996503, by rfl⟩ : syracuseStep 1328671 = 1993007) B1993007
theorem B4196015 : Blo 1242439 4196015 := bstep (se 1 (by rfl) ⟨3147011, by rfl⟩ : syracuseStep 4196015 = 6294023) B6294023
theorem B4253597 : Blo 1242439 4253597 := bstep (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) B1595099
theorem B5670857 : Blo 1242439 5670857 := bstep (se 2 (by rfl) ⟨2126571, by rfl⟩ : syracuseStep 5670857 = 4253143) B4253143
theorem B2656351 : Blo 1242439 2656351 := bstep (se 1 (by rfl) ⟨1992263, by rfl⟩ : syracuseStep 2656351 = 3984527) B3984527
theorem B2795831 : Blo 1242439 2795831 := bstep (se 1 (by rfl) ⟨2096873, by rfl⟩ : syracuseStep 2795831 = 4193747) B4193747
theorem B4721111 : Blo 1242439 4721111 := bstep (se 1 (by rfl) ⟨3540833, by rfl⟩ : syracuseStep 4721111 = 7081667) B7081667
theorem B3148247 : Blo 1242439 3148247 := bstep (se 1 (by rfl) ⟨2361185, by rfl⟩ : syracuseStep 3148247 = 4722371) B4722371
theorem B5671387 : Blo 1242439 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B2796011 : Blo 1242439 2796011 := bstep (se 1 (by rfl) ⟨2097008, by rfl⟩ : syracuseStep 2796011 = 4194017) B4194017
theorem B10619525 : Blo 1242439 10619525 := bstep (se 4 (by rfl) ⟨995580, by rfl⟩ : syracuseStep 10619525 = 1991161) B1991161
theorem B4197203 : Blo 1242439 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B3148703 : Blo 1242439 3148703 := bstep (se 1 (by rfl) ⟨2361527, by rfl⟩ : syracuseStep 3148703 = 4723055) B4723055
theorem B9571391 : Blo 1242439 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B7285889 : Blo 1242439 7285889 := bstep (se 2 (by rfl) ⟨2732208, by rfl⟩ : syracuseStep 7285889 = 5464417) B5464417
theorem B2796713 : Blo 1242439 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B4787387 : Blo 1242439 4787387 := bstep (se 1 (by rfl) ⟨3590540, by rfl⟩ : syracuseStep 4787387 = 7181081) B7181081
theorem B4197743 : Blo 1242439 4197743 := bstep (se 1 (by rfl) ⟨3148307, by rfl⟩ : syracuseStep 4197743 = 6296615) B6296615
theorem B3542393 : Blo 1242439 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B10087847 : Blo 1242439 10087847 := bstep (se 1 (by rfl) ⟨7565885, by rfl⟩ : syracuseStep 10087847 = 15131771) B15131771
theorem B2797127 : Blo 1242439 2797127 := bstep (se 1 (by rfl) ⟨2097845, by rfl⟩ : syracuseStep 2797127 = 4195691) B4195691
theorem B2797199 : Blo 1242439 2797199 := bstep (se 1 (by rfl) ⟨2097899, by rfl⟩ : syracuseStep 2797199 = 4195799) B4195799
theorem B2797289 : Blo 1242439 2797289 := bstep (se 2 (by rfl) ⟨1048983, by rfl⟩ : syracuseStep 2797289 = 2097967) B2097967
theorem B2797307 : Blo 1242439 2797307 := bstep (se 1 (by rfl) ⟨2097980, by rfl⟩ : syracuseStep 2797307 = 4195961) B4195961
theorem B57454541 : Blo 1242439 57454541 := bstep (se 3 (by rfl) ⟨10772726, by rfl⟩ : syracuseStep 57454541 = 21545453) B21545453
theorem B3149887 : Blo 1242439 3149887 := bstep (se 1 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 3149887 = 4724831) B4724831
theorem B1864091 : Blo 1242439 1864091 := bstep (se 1 (by rfl) ⟨1398068, by rfl⟩ : syracuseStep 1864091 = 2796137) B2796137
theorem B4198985 : Blo 1242439 4198985 := bstep (se 2 (by rfl) ⟨1574619, by rfl⟩ : syracuseStep 4198985 = 3149239) B3149239
theorem B26874449 : Blo 1242439 26874449 := bstep (se 2 (by rfl) ⟨10077918, by rfl⟩ : syracuseStep 26874449 = 20155837) B20155837
theorem B2798315 : Blo 1242439 2798315 := bstep (se 1 (by rfl) ⟨2098736, by rfl⟩ : syracuseStep 2798315 = 4197473) B4197473
theorem B10629913 : Blo 1242439 10629913 := bstep (se 2 (by rfl) ⟨3986217, by rfl⟩ : syracuseStep 10629913 = 7972435) B7972435
theorem B1864511 : Blo 1242439 1864511 := bstep (se 1 (by rfl) ⟨1398383, by rfl⟩ : syracuseStep 1864511 = 2796767) B2796767
theorem B1864655 : Blo 1242439 1864655 := bstep (se 1 (by rfl) ⟨1398491, by rfl⟩ : syracuseStep 1864655 = 2796983) B2796983
theorem B1864697 : Blo 1242439 1864697 := bstep (se 2 (by rfl) ⟨699261, by rfl⟩ : syracuseStep 1864697 = 1398523) B1398523
theorem B2798585 : Blo 1242439 2798585 := bstep (se 2 (by rfl) ⟨1049469, by rfl⟩ : syracuseStep 2798585 = 2098939) B2098939
theorem B1864745 : Blo 1242439 1864745 := bstep (se 2 (by rfl) ⟨699279, by rfl⟩ : syracuseStep 1864745 = 1398559) B1398559
theorem B1864775 : Blo 1242439 1864775 := bstep (se 1 (by rfl) ⟨1398581, by rfl⟩ : syracuseStep 1864775 = 2797163) B2797163
theorem B2798675 : Blo 1242439 2798675 := bstep (se 1 (by rfl) ⟨2099006, by rfl⟩ : syracuseStep 2798675 = 4198013) B4198013
theorem B14152805 : Blo 1242439 14152805 := bstep (se 4 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 14152805 = 2653651) B2653651
theorem B9442493 : Blo 1242439 9442493 := bstep (se 3 (by rfl) ⟨1770467, by rfl⟩ : syracuseStep 9442493 = 3540935) B3540935
theorem B1864955 : Blo 1242439 1864955 := bstep (se 1 (by rfl) ⟨1398716, by rfl⟩ : syracuseStep 1864955 = 2797433) B2797433
theorem B2798855 : Blo 1242439 2798855 := bstep (se 1 (by rfl) ⟨2099141, by rfl⟩ : syracuseStep 2798855 = 4198283) B4198283
theorem B4035881 : Blo 1242439 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B1242599 : Blo 1242439 1242599 := bstep (se 1 (by rfl) ⟨931949, by rfl⟩ : syracuseStep 1242599 = 1863899) B1863899
theorem B1242607 : Blo 1242439 1242607 := bstep (se 1 (by rfl) ⟨931955, by rfl⟩ : syracuseStep 1242607 = 1863911) B1863911
theorem B1242715 : Blo 1242439 1242715 := bstep (se 1 (by rfl) ⟨932036, by rfl⟩ : syracuseStep 1242715 = 1864073) B1864073
theorem B2799215 : Blo 1242439 2799215 := bstep (se 1 (by rfl) ⟨2099411, by rfl⟩ : syracuseStep 2799215 = 4198823) B4198823
theorem B1242779 : Blo 1242439 1242779 := bstep (se 1 (by rfl) ⟨932084, by rfl⟩ : syracuseStep 1242779 = 1864169) B1864169
theorem B9442979 : Blo 1242439 9442979 := bstep (se 1 (by rfl) ⟨7082234, by rfl⟩ : syracuseStep 9442979 = 14164469) B14164469
theorem B1242863 : Blo 1242439 1242863 := bstep (se 1 (by rfl) ⟨932147, by rfl⟩ : syracuseStep 1242863 = 1864295) B1864295
theorem B4724527 : Blo 1242439 4724527 := bstep (se 1 (by rfl) ⟨3543395, by rfl⟩ : syracuseStep 4724527 = 7086791) B7086791
theorem B1242951 : Blo 1242439 1242951 := bstep (se 1 (by rfl) ⟨932213, by rfl⟩ : syracuseStep 1242951 = 1864427) B1864427
theorem B1242971 : Blo 1242439 1242971 := bstep (se 1 (by rfl) ⟨932228, by rfl⟩ : syracuseStep 1242971 = 1864457) B1864457
theorem B1243039 : Blo 1242439 1243039 := bstep (se 1 (by rfl) ⟨932279, by rfl⟩ : syracuseStep 1243039 = 1864559) B1864559
theorem B1243207 : Blo 1242439 1243207 := bstep (se 1 (by rfl) ⟨932405, by rfl⟩ : syracuseStep 1243207 = 1864811) B1864811
theorem B9443465 : Blo 1242439 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B1243367 : Blo 1242439 1243367 := bstep (se 1 (by rfl) ⟨932525, by rfl⟩ : syracuseStep 1243367 = 1865051) B1865051
theorem B5314889 : Blo 1242439 5314889 := bstep (se 2 (by rfl) ⟨1993083, by rfl⟩ : syracuseStep 5314889 = 3986167) B3986167
theorem B2693459 : Blo 1242439 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B1243551 : Blo 1242439 1243551 := bstep (se 1 (by rfl) ⟨932663, by rfl⟩ : syracuseStep 1243551 = 1865327) B1865327
theorem B1243599 : Blo 1242439 1243599 := bstep (se 1 (by rfl) ⟨932699, by rfl⟩ : syracuseStep 1243599 = 1865399) B1865399
theorem B1866191 : Blo 1242439 1866191 := bstep (se 1 (by rfl) ⟨1399643, by rfl⟩ : syracuseStep 1866191 = 2799287) B2799287
theorem B1243623 : Blo 1242439 1243623 := bstep (se 1 (by rfl) ⟨932717, by rfl⟩ : syracuseStep 1243623 = 1865435) B1865435
theorem B1866281 : Blo 1242439 1866281 := bstep (se 2 (by rfl) ⟨699855, by rfl⟩ : syracuseStep 1866281 = 1399711) B1399711
theorem B7969337 : Blo 1242439 7969337 := bstep (se 2 (by rfl) ⟨2988501, by rfl⟩ : syracuseStep 7969337 = 5977003) B5977003
theorem B5315129 : Blo 1242439 5315129 := bstep (se 2 (by rfl) ⟨1993173, by rfl⟩ : syracuseStep 5315129 = 3986347) B3986347
theorem B1243739 : Blo 1242439 1243739 := bstep (se 1 (by rfl) ⟨932804, by rfl⟩ : syracuseStep 1243739 = 1865609) B1865609
theorem B1399387 : Blo 1242439 1399387 := bstep (se 1 (by rfl) ⟨1049540, by rfl⟩ : syracuseStep 1399387 = 2099081) B2099081
theorem B1243807 : Blo 1242439 1243807 := bstep (se 1 (by rfl) ⟨932855, by rfl⟩ : syracuseStep 1243807 = 1865711) B1865711
theorem B5044961 : Blo 1242439 5044961 := bstep (se 2 (by rfl) ⟨1891860, by rfl⟩ : syracuseStep 5044961 = 3783721) B3783721
theorem B1866473 : Blo 1242439 1866473 := bstep (se 2 (by rfl) ⟨699927, by rfl⟩ : syracuseStep 1866473 = 1399855) B1399855
theorem B11344637 : Blo 1242439 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B1243975 : Blo 1242439 1243975 := bstep (se 1 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 1243975 = 1865963) B1865963
theorem B1244015 : Blo 1242439 1244015 := bstep (se 1 (by rfl) ⟨933011, by rfl⟩ : syracuseStep 1244015 = 1866023) B1866023
theorem B1399675 : Blo 1242439 1399675 := bstep (se 1 (by rfl) ⟨1049756, by rfl⟩ : syracuseStep 1399675 = 2099513) B2099513
theorem B7076767 : Blo 1242439 7076767 := bstep (se 1 (by rfl) ⟨5307575, by rfl⟩ : syracuseStep 7076767 = 10615151) B10615151
theorem B1244071 : Blo 1242439 1244071 := bstep (se 1 (by rfl) ⟨933053, by rfl⟩ : syracuseStep 1244071 = 1866107) B1866107
theorem B7969873 : Blo 1242439 7969873 := bstep (se 2 (by rfl) ⟨2988702, by rfl⟩ : syracuseStep 7969873 = 5977405) B5977405
theorem B1244251 : Blo 1242439 1244251 := bstep (se 1 (by rfl) ⟨933188, by rfl⟩ : syracuseStep 1244251 = 1866377) B1866377
theorem B232815779 : Blo 1242439 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B1244367 : Blo 1242439 1244367 := bstep (se 1 (by rfl) ⟨933275, by rfl⟩ : syracuseStep 1244367 = 1866551) B1866551
theorem B2522335 : Blo 1242439 2522335 := bstep (se 1 (by rfl) ⟨1891751, by rfl⟩ : syracuseStep 2522335 = 3783503) B3783503
theorem B1244391 : Blo 1242439 1244391 := bstep (se 1 (by rfl) ⟨933293, by rfl⟩ : syracuseStep 1244391 = 1866587) B1866587
theorem B6290783 : Blo 1242439 6290783 := bstep (se 1 (by rfl) ⟨4718087, by rfl⟩ : syracuseStep 6290783 = 9436175) B9436175
theorem B51010955 : Blo 1242439 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B29506999 : Blo 1242439 29506999 := bstep (se 1 (by rfl) ⟨22130249, by rfl⟩ : syracuseStep 29506999 = 44260499) B44260499
theorem B15113765 : Blo 1242439 15113765 := bstep (se 4 (by rfl) ⟨1416915, by rfl⟩ : syracuseStep 15113765 = 2833831) B2833831
theorem B1572463 : Blo 1242439 1572463 := bstep (se 1 (by rfl) ⟨1179347, by rfl⟩ : syracuseStep 1572463 = 2358695) B2358695
theorem B4718209 : Blo 1242439 4718209 := bstep (se 2 (by rfl) ⟨1769328, by rfl⟩ : syracuseStep 4718209 = 3538657) B3538657
theorem B2096975 : Blo 1242439 2096975 := bstep (se 1 (by rfl) ⟨1572731, by rfl⟩ : syracuseStep 2096975 = 3145463) B3145463
theorem B2989963 : Blo 1242439 2989963 := bstep (se 1 (by rfl) ⟨2242472, by rfl⟩ : syracuseStep 2989963 = 4484945) B4484945
theorem B23887781 : Blo 1242439 23887781 := bstep (se 4 (by rfl) ⟨2239479, by rfl⟩ : syracuseStep 23887781 = 4478959) B4478959
theorem B2097407 : Blo 1242439 2097407 := bstep (se 1 (by rfl) ⟨1573055, by rfl⟩ : syracuseStep 2097407 = 3146111) B3146111
theorem B17916299 : Blo 1242439 17916299 := bstep (se 1 (by rfl) ⟨13437224, by rfl⟩ : syracuseStep 17916299 = 26874449) B26874449
theorem B1769887 : Blo 1242439 1769887 := bstep (se 1 (by rfl) ⟨1327415, by rfl⟩ : syracuseStep 1769887 = 2654831) B2654831
theorem B6816287 : Blo 1242439 6816287 := bstep (se 1 (by rfl) ⟨5112215, by rfl⟩ : syracuseStep 6816287 = 10224431) B10224431
theorem B6292079 : Blo 1242439 6292079 := bstep (se 1 (by rfl) ⟨4719059, by rfl⟩ : syracuseStep 6292079 = 9438119) B9438119
theorem B7561849 : Blo 1242439 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B3982067 : Blo 1242439 3982067 := bstep (se 1 (by rfl) ⟨2986550, by rfl⟩ : syracuseStep 3982067 = 5973101) B5973101
theorem B1573663 : Blo 1242439 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B17007479 : Blo 1242439 17007479 := bstep (se 1 (by rfl) ⟨12755609, by rfl⟩ : syracuseStep 17007479 = 25511219) B25511219
theorem B9446381 : Blo 1242439 9446381 := bstep (se 3 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 9446381 = 3542393) B3542393
theorem B14173217 : Blo 1242439 14173217 := bstep (se 2 (by rfl) ⟨5314956, by rfl⟩ : syracuseStep 14173217 = 10629913) B10629913
theorem B2835731 : Blo 1242439 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B10626497 : Blo 1242439 10626497 := bstep (se 2 (by rfl) ⟨3984936, by rfl⟩ : syracuseStep 10626497 = 7969873) B7969873
theorem B3147407 : Blo 1242439 3147407 := bstep (se 1 (by rfl) ⟨2360555, by rfl⟩ : syracuseStep 3147407 = 4721111) B4721111
theorem B2098831 : Blo 1242439 2098831 := bstep (se 1 (by rfl) ⟨1574123, by rfl⟩ : syracuseStep 2098831 = 3148247) B3148247
theorem B7079683 : Blo 1242439 7079683 := bstep (se 1 (by rfl) ⟨5309762, by rfl⟩ : syracuseStep 7079683 = 10619525) B10619525
theorem B7563091 : Blo 1242439 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B13453229 : Blo 1242439 13453229 := bstep (se 3 (by rfl) ⟨2522480, by rfl⟩ : syracuseStep 13453229 = 5044961) B5044961
theorem B2099135 : Blo 1242439 2099135 := bstep (se 1 (by rfl) ⟨1574351, by rfl⟩ : syracuseStep 2099135 = 3148703) B3148703
theorem B4196393 : Blo 1242439 4196393 := bstep (se 2 (by rfl) ⟨1573647, by rfl⟩ : syracuseStep 4196393 = 3147295) B3147295
theorem B1771561 : Blo 1242439 1771561 := bstep (se 2 (by rfl) ⟨664335, by rfl⟩ : syracuseStep 1771561 = 1328671) B1328671
theorem B34007303 : Blo 1242439 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B3541801 : Blo 1242439 3541801 := bstep (se 2 (by rfl) ⟨1328175, by rfl⟩ : syracuseStep 3541801 = 2656351) B2656351
theorem B6294995 : Blo 1242439 6294995 := bstep (se 1 (by rfl) ⟨4721246, by rfl⟩ : syracuseStep 6294995 = 9442493) B9442493
theorem B2690587 : Blo 1242439 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B6295319 : Blo 1242439 6295319 := bstep (se 1 (by rfl) ⟨4721489, by rfl⟩ : syracuseStep 6295319 = 9442979) B9442979
theorem B2797343 : Blo 1242439 2797343 := bstep (se 1 (by rfl) ⟨2098007, by rfl⟩ : syracuseStep 2797343 = 4196015) B4196015
theorem B9449297 : Blo 1242439 9449297 := bstep (se 2 (by rfl) ⟨3543486, by rfl⟩ : syracuseStep 9449297 = 7086973) B7086973
theorem B26882057 : Blo 1242439 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B6295643 : Blo 1242439 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B1863887 : Blo 1242439 1863887 := bstep (se 1 (by rfl) ⟨1397915, by rfl⟩ : syracuseStep 1863887 = 2795831) B2795831
theorem B3543259 : Blo 1242439 3543259 := bstep (se 1 (by rfl) ⟨2657444, by rfl⟩ : syracuseStep 3543259 = 5314889) B5314889
theorem B2797865 : Blo 1242439 2797865 := bstep (se 2 (by rfl) ⟨1049199, by rfl⟩ : syracuseStep 2797865 = 2098399) B2098399
theorem B3363113 : Blo 1242439 3363113 := bstep (se 2 (by rfl) ⟨1261167, by rfl⟩ : syracuseStep 3363113 = 2522335) B2522335
theorem B1864007 : Blo 1242439 1864007 := bstep (se 1 (by rfl) ⟨1398005, by rfl⟩ : syracuseStep 1864007 = 2796011) B2796011
theorem B5312891 : Blo 1242439 5312891 := bstep (se 1 (by rfl) ⟨3984668, by rfl⟩ : syracuseStep 5312891 = 7969337) B7969337
theorem B3543419 : Blo 1242439 3543419 := bstep (se 1 (by rfl) ⟨2657564, by rfl⟩ : syracuseStep 3543419 = 5315129) B5315129
theorem B2798135 : Blo 1242439 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B39342665 : Blo 1242439 39342665 := bstep (se 2 (by rfl) ⟨14753499, by rfl⟩ : syracuseStep 39342665 = 29506999) B29506999
theorem B155210519 : Blo 1242439 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1864475 : Blo 1242439 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B3191591 : Blo 1242439 3191591 := bstep (se 1 (by rfl) ⟨2393693, by rfl⟩ : syracuseStep 3191591 = 4787387) B4787387
theorem B2798495 : Blo 1242439 2798495 := bstep (se 1 (by rfl) ⟨2098871, by rfl⟩ : syracuseStep 2798495 = 4197743) B4197743
theorem B1864751 : Blo 1242439 1864751 := bstep (se 1 (by rfl) ⟨1398563, by rfl⟩ : syracuseStep 1864751 = 2797127) B2797127
theorem B1864799 : Blo 1242439 1864799 := bstep (se 1 (by rfl) ⟨1398599, by rfl⟩ : syracuseStep 1864799 = 2797199) B2797199
theorem B1864859 : Blo 1242439 1864859 := bstep (se 1 (by rfl) ⟨1398644, by rfl⟩ : syracuseStep 1864859 = 2797289) B2797289
theorem B1864871 : Blo 1242439 1864871 := bstep (se 1 (by rfl) ⟨1398653, by rfl⟩ : syracuseStep 1864871 = 2797307) B2797307
theorem B3986617 : Blo 1242439 3986617 := bstep (se 2 (by rfl) ⟨1494981, by rfl⟩ : syracuseStep 3986617 = 2989963) B2989963
theorem B1397983 : Blo 1242439 1397983 := bstep (se 1 (by rfl) ⟨1048487, by rfl⟩ : syracuseStep 1397983 = 2096975) B2096975
theorem B38303027 : Blo 1242439 38303027 := bstep (se 1 (by rfl) ⟨28727270, by rfl⟩ : syracuseStep 38303027 = 57454541) B57454541
theorem B6296939 : Blo 1242439 6296939 := bstep (se 1 (by rfl) ⟨4722704, by rfl⟩ : syracuseStep 6296939 = 9445409) B9445409
theorem B4199849 : Blo 1242439 4199849 := bstep (se 2 (by rfl) ⟨1574943, by rfl⟩ : syracuseStep 4199849 = 3149887) B3149887
theorem B4199903 : Blo 1242439 4199903 := bstep (se 1 (by rfl) ⟨3149927, by rfl⟩ : syracuseStep 4199903 = 6299855) B6299855
theorem B1242727 : Blo 1242439 1242727 := bstep (se 1 (by rfl) ⟨932045, by rfl⟩ : syracuseStep 1242727 = 1864091) B1864091
theorem B2799323 : Blo 1242439 2799323 := bstep (se 1 (by rfl) ⟨2099492, by rfl⟩ : syracuseStep 2799323 = 4198985) B4198985
theorem B1865543 : Blo 1242439 1865543 := bstep (se 1 (by rfl) ⟨1399157, by rfl⟩ : syracuseStep 1865543 = 2798315) B2798315
theorem B1243007 : Blo 1242439 1243007 := bstep (se 1 (by rfl) ⟨932255, by rfl⟩ : syracuseStep 1243007 = 1864511) B1864511
theorem B1243103 : Blo 1242439 1243103 := bstep (se 1 (by rfl) ⟨932327, by rfl⟩ : syracuseStep 1243103 = 1864655) B1864655
theorem B1243131 : Blo 1242439 1243131 := bstep (se 1 (by rfl) ⟨932348, by rfl⟩ : syracuseStep 1243131 = 1864697) B1864697
theorem B1865723 : Blo 1242439 1865723 := bstep (se 1 (by rfl) ⟨1399292, by rfl⟩ : syracuseStep 1865723 = 2798585) B2798585
theorem B1243163 : Blo 1242439 1243163 := bstep (se 1 (by rfl) ⟨932372, by rfl⟩ : syracuseStep 1243163 = 1864745) B1864745
theorem B1243183 : Blo 1242439 1243183 := bstep (se 1 (by rfl) ⟨932387, by rfl⟩ : syracuseStep 1243183 = 1864775) B1864775
theorem B1865783 : Blo 1242439 1865783 := bstep (se 1 (by rfl) ⟨1399337, by rfl⟩ : syracuseStep 1865783 = 2798675) B2798675
theorem B9435203 : Blo 1242439 9435203 := bstep (se 1 (by rfl) ⟨7076402, by rfl⟩ : syracuseStep 9435203 = 14152805) B14152805
theorem B1865849 : Blo 1242439 1865849 := bstep (se 2 (by rfl) ⟨699693, by rfl⟩ : syracuseStep 1865849 = 1399387) B1399387
theorem B1243303 : Blo 1242439 1243303 := bstep (se 1 (by rfl) ⟨932477, by rfl⟩ : syracuseStep 1243303 = 1864955) B1864955
theorem B1865903 : Blo 1242439 1865903 := bstep (se 1 (by rfl) ⟨1399427, by rfl⟩ : syracuseStep 1865903 = 2798855) B2798855
theorem B4479191 : Blo 1242439 4479191 := bstep (se 1 (by rfl) ⟨3359393, by rfl⟩ : syracuseStep 4479191 = 6718787) B6718787
theorem B7182557 : Blo 1242439 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B1890535 : Blo 1242439 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B31873337 : Blo 1242439 31873337 := bstep (se 2 (by rfl) ⟨11952501, by rfl⟩ : syracuseStep 31873337 = 23905003) B23905003
theorem B1866143 : Blo 1242439 1866143 := bstep (se 1 (by rfl) ⟨1399607, by rfl⟩ : syracuseStep 1866143 = 2799215) B2799215
theorem B1866233 : Blo 1242439 1866233 := bstep (se 2 (by rfl) ⟨699837, by rfl⟩ : syracuseStep 1866233 = 1399675) B1399675
theorem B9435689 : Blo 1242439 9435689 := bstep (se 2 (by rfl) ⟨3538383, by rfl⟩ : syracuseStep 9435689 = 7076767) B7076767
theorem B1244127 : Blo 1242439 1244127 := bstep (se 1 (by rfl) ⟨933095, by rfl⟩ : syracuseStep 1244127 = 1866191) B1866191
theorem B1244187 : Blo 1242439 1244187 := bstep (se 1 (by rfl) ⟨933140, by rfl⟩ : syracuseStep 1244187 = 1866281) B1866281
theorem B1244315 : Blo 1242439 1244315 := bstep (se 1 (by rfl) ⟨933236, by rfl⟩ : syracuseStep 1244315 = 1866473) B1866473
theorem B6380927 : Blo 1242439 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B4857259 : Blo 1242439 4857259 := bstep (se 1 (by rfl) ⟨3642944, by rfl⟩ : syracuseStep 4857259 = 7285889) B7285889
theorem B2096617 : Blo 1242439 2096617 := bstep (se 2 (by rfl) ⟨786231, by rfl⟩ : syracuseStep 2096617 = 1572463) B1572463
theorem B6290945 : Blo 1242439 6290945 := bstep (se 2 (by rfl) ⟨2359104, by rfl⟩ : syracuseStep 6290945 = 4718209) B4718209
theorem B4193855 : Blo 1242439 4193855 := bstep (se 1 (by rfl) ⟨3145391, by rfl⟩ : syracuseStep 4193855 = 6290783) B6290783
theorem B6725231 : Blo 1242439 6725231 := bstep (se 1 (by rfl) ⟨5043923, by rfl⟩ : syracuseStep 6725231 = 10087847) B10087847
theorem B10075843 : Blo 1242439 10075843 := bstep (se 1 (by rfl) ⟨7556882, by rfl⟩ : syracuseStep 10075843 = 15113765) B15113765
theorem B6299369 : Blo 1242439 6299369 := bstep (se 2 (by rfl) ⟨2362263, by rfl⟩ : syracuseStep 6299369 = 4724527) B4724527
theorem B15122285 : Blo 1242439 15122285 := bstep (se 3 (by rfl) ⟨2835428, by rfl⟩ : syracuseStep 15122285 = 5670857) B5670857
theorem B15925187 : Blo 1242439 15925187 := bstep (se 1 (by rfl) ⟨11943890, by rfl⟩ : syracuseStep 15925187 = 23887781) B23887781
theorem B11944199 : Blo 1242439 11944199 := bstep (se 1 (by rfl) ⟨8958149, by rfl⟩ : syracuseStep 11944199 = 17916299) B17916299
theorem B4194719 : Blo 1242439 4194719 := bstep (se 1 (by rfl) ⟨3146039, by rfl⟩ : syracuseStep 4194719 = 6292079) B6292079
theorem B2654711 : Blo 1242439 2654711 := bstep (se 1 (by rfl) ⟨1991033, by rfl⟩ : syracuseStep 2654711 = 3982067) B3982067
theorem B2359849 : Blo 1242439 2359849 := bstep (se 2 (by rfl) ⟨884943, by rfl⟩ : syracuseStep 2359849 = 1769887) B1769887
theorem B11338319 : Blo 1242439 11338319 := bstep (se 1 (by rfl) ⟨8503739, by rfl⟩ : syracuseStep 11338319 = 17007479) B17007479
theorem B25535351 : Blo 1242439 25535351 := bstep (se 1 (by rfl) ⟨19151513, by rfl⟩ : syracuseStep 25535351 = 38303027) B38303027
theorem B2098217 : Blo 1242439 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B2098271 : Blo 1242439 2098271 := bstep (se 1 (by rfl) ⟨1573703, by rfl⟩ : syracuseStep 2098271 = 3147407) B3147407
theorem B2795489 : Blo 1242439 2795489 := bstep (se 2 (by rfl) ⟨1048308, by rfl⟩ : syracuseStep 2795489 = 2096617) B2096617
theorem B413894717 : Blo 1242439 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B4253951 : Blo 1242439 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B4196663 : Blo 1242439 4196663 := bstep (se 1 (by rfl) ⟨3147497, by rfl⟩ : syracuseStep 4196663 = 6294995) B6294995
theorem B9439577 : Blo 1242439 9439577 := bstep (se 2 (by rfl) ⟨3539841, by rfl⟩ : syracuseStep 9439577 = 7079683) B7079683
theorem B2795903 : Blo 1242439 2795903 := bstep (se 1 (by rfl) ⟨2096927, by rfl⟩ : syracuseStep 2795903 = 4193855) B4193855
theorem B4483487 : Blo 1242439 4483487 := bstep (se 1 (by rfl) ⟨3362615, by rfl⟩ : syracuseStep 4483487 = 6725231) B6725231
theorem B4196879 : Blo 1242439 4196879 := bstep (se 1 (by rfl) ⟨3147659, by rfl⟩ : syracuseStep 4196879 = 6295319) B6295319
theorem B4197095 : Blo 1242439 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B9448325 : Blo 1242439 9448325 := bstep (se 4 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 9448325 = 1771561) B1771561
theorem B3541927 : Blo 1242439 3541927 := bstep (se 1 (by rfl) ⟨2656445, by rfl⟩ : syracuseStep 3541927 = 5312891) B5312891
theorem B2362279 : Blo 1242439 2362279 := bstep (se 1 (by rfl) ⟨1771709, by rfl⟩ : syracuseStep 2362279 = 3543419) B3543419
theorem B9448811 : Blo 1242439 9448811 := bstep (se 1 (by rfl) ⟨7086608, by rfl⟩ : syracuseStep 9448811 = 14173217) B14173217
theorem B4197959 : Blo 1242439 4197959 := bstep (se 1 (by rfl) ⟨3148469, by rfl⟩ : syracuseStep 4197959 = 6296939) B6296939
theorem B4722401 : Blo 1242439 4722401 := bstep (se 2 (by rfl) ⟨1770900, by rfl⟩ : syracuseStep 4722401 = 3541801) B3541801
theorem B2797595 : Blo 1242439 2797595 := bstep (se 1 (by rfl) ⟨2098196, by rfl⟩ : syracuseStep 2797595 = 4196393) B4196393
theorem B2986127 : Blo 1242439 2986127 := bstep (se 1 (by rfl) ⟨2239595, by rfl⟩ : syracuseStep 2986127 = 4479191) B4479191
theorem B4788371 : Blo 1242439 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B22671535 : Blo 1242439 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B1863977 : Blo 1242439 1863977 := bstep (se 2 (by rfl) ⟨698991, by rfl⟩ : syracuseStep 1863977 = 1397983) B1397983
theorem B6476345 : Blo 1242439 6476345 := bstep (se 2 (by rfl) ⟨2428629, by rfl⟩ : syracuseStep 6476345 = 4857259) B4857259
theorem B2798441 : Blo 1242439 2798441 := bstep (se 2 (by rfl) ⟨1049415, by rfl⟩ : syracuseStep 2798441 = 2098831) B2098831
theorem B4199579 : Blo 1242439 4199579 := bstep (se 1 (by rfl) ⟨3149684, by rfl⟩ : syracuseStep 4199579 = 6299369) B6299369
theorem B1864895 : Blo 1242439 1864895 := bstep (se 1 (by rfl) ⟨1398671, by rfl⟩ : syracuseStep 1864895 = 2797343) B2797343
theorem B10081523 : Blo 1242439 10081523 := bstep (se 1 (by rfl) ⟨7561142, by rfl⟩ : syracuseStep 10081523 = 15122285) B15122285
theorem B71685485 : Blo 1242439 71685485 := bstep (se 3 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 71685485 = 26882057) B26882057
theorem B1242591 : Blo 1242439 1242591 := bstep (se 1 (by rfl) ⟨931943, by rfl⟩ : syracuseStep 1242591 = 1863887) B1863887
theorem B14349797 : Blo 1242439 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B1398271 : Blo 1242439 1398271 := bstep (se 1 (by rfl) ⟨1048703, by rfl⟩ : syracuseStep 1398271 = 2097407) B2097407
theorem B1865243 : Blo 1242439 1865243 := bstep (se 1 (by rfl) ⟨1398932, by rfl⟩ : syracuseStep 1865243 = 2797865) B2797865
theorem B2242075 : Blo 1242439 2242075 := bstep (se 1 (by rfl) ⟨1681556, by rfl⟩ : syracuseStep 2242075 = 3363113) B3363113
theorem B1242671 : Blo 1242439 1242671 := bstep (se 1 (by rfl) ⟨932003, by rfl⟩ : syracuseStep 1242671 = 1864007) B1864007
theorem B4724345 : Blo 1242439 4724345 := bstep (se 2 (by rfl) ⟨1771629, by rfl⟩ : syracuseStep 4724345 = 3543259) B3543259
theorem B2520713 : Blo 1242439 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B4544191 : Blo 1242439 4544191 := bstep (se 1 (by rfl) ⟨3408143, by rfl⟩ : syracuseStep 4544191 = 6816287) B6816287
theorem B1865423 : Blo 1242439 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B1242983 : Blo 1242439 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B2127727 : Blo 1242439 2127727 := bstep (se 1 (by rfl) ⟨1595795, by rfl⟩ : syracuseStep 2127727 = 3191591) B3191591
theorem B1865663 : Blo 1242439 1865663 := bstep (se 1 (by rfl) ⟨1399247, by rfl⟩ : syracuseStep 1865663 = 2798495) B2798495
theorem B6297587 : Blo 1242439 6297587 := bstep (se 1 (by rfl) ⟨4723190, by rfl⟩ : syracuseStep 6297587 = 9446381) B9446381
theorem B1243167 : Blo 1242439 1243167 := bstep (se 1 (by rfl) ⟨932375, by rfl⟩ : syracuseStep 1243167 = 1864751) B1864751
theorem B1243199 : Blo 1242439 1243199 := bstep (se 1 (by rfl) ⟨932399, by rfl⟩ : syracuseStep 1243199 = 1864799) B1864799
theorem B1243239 : Blo 1242439 1243239 := bstep (se 1 (by rfl) ⟨932429, by rfl⟩ : syracuseStep 1243239 = 1864859) B1864859
theorem B1243247 : Blo 1242439 1243247 := bstep (se 1 (by rfl) ⟨932435, by rfl⟩ : syracuseStep 1243247 = 1864871) B1864871
theorem B10082465 : Blo 1242439 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B1890487 : Blo 1242439 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B2799899 : Blo 1242439 2799899 := bstep (se 1 (by rfl) ⟨2099924, by rfl⟩ : syracuseStep 2799899 = 4199849) B4199849
theorem B7084331 : Blo 1242439 7084331 := bstep (se 1 (by rfl) ⟨5313248, by rfl⟩ : syracuseStep 7084331 = 10626497) B10626497
theorem B2799935 : Blo 1242439 2799935 := bstep (se 1 (by rfl) ⟨2099951, by rfl⟩ : syracuseStep 2799935 = 4199903) B4199903
theorem B1866215 : Blo 1242439 1866215 := bstep (se 1 (by rfl) ⟨1399661, by rfl⟩ : syracuseStep 1866215 = 2799323) B2799323
theorem B1243695 : Blo 1242439 1243695 := bstep (se 1 (by rfl) ⟨932771, by rfl⟩ : syracuseStep 1243695 = 1865543) B1865543
theorem B8968819 : Blo 1242439 8968819 := bstep (se 1 (by rfl) ⟨6726614, by rfl⟩ : syracuseStep 8968819 = 13453229) B13453229
theorem B1399423 : Blo 1242439 1399423 := bstep (se 1 (by rfl) ⟨1049567, by rfl⟩ : syracuseStep 1399423 = 2099135) B2099135
theorem B1243815 : Blo 1242439 1243815 := bstep (se 1 (by rfl) ⟨932861, by rfl⟩ : syracuseStep 1243815 = 1865723) B1865723
theorem B1243855 : Blo 1242439 1243855 := bstep (se 1 (by rfl) ⟨932891, by rfl⟩ : syracuseStep 1243855 = 1865783) B1865783
theorem B6290135 : Blo 1242439 6290135 := bstep (se 1 (by rfl) ⟨4717601, by rfl⟩ : syracuseStep 6290135 = 9435203) B9435203
theorem B1243899 : Blo 1242439 1243899 := bstep (se 1 (by rfl) ⟨932924, by rfl⟩ : syracuseStep 1243899 = 1865849) B1865849
theorem B1243935 : Blo 1242439 1243935 := bstep (se 1 (by rfl) ⟨932951, by rfl⟩ : syracuseStep 1243935 = 1865903) B1865903
theorem B104913773 : Blo 1242439 104913773 := bstep (se 3 (by rfl) ⟨19671332, by rfl⟩ : syracuseStep 104913773 = 39342665) B39342665
theorem B21248891 : Blo 1242439 21248891 := bstep (se 1 (by rfl) ⟨15936668, by rfl⟩ : syracuseStep 21248891 = 31873337) B31873337
theorem B5315489 : Blo 1242439 5315489 := bstep (se 2 (by rfl) ⟨1993308, by rfl⟩ : syracuseStep 5315489 = 3986617) B3986617
theorem B1244095 : Blo 1242439 1244095 := bstep (se 1 (by rfl) ⟨933071, by rfl⟩ : syracuseStep 1244095 = 1866143) B1866143
theorem B1244155 : Blo 1242439 1244155 := bstep (se 1 (by rfl) ⟨933116, by rfl⟩ : syracuseStep 1244155 = 1866233) B1866233
theorem B6290459 : Blo 1242439 6290459 := bstep (se 1 (by rfl) ⟨4717844, by rfl⟩ : syracuseStep 6290459 = 9435689) B9435689
theorem B13434457 : Blo 1242439 13434457 := bstep (se 2 (by rfl) ⟨5037921, by rfl⟩ : syracuseStep 13434457 = 10075843) B10075843
theorem B4193963 : Blo 1242439 4193963 := bstep (se 1 (by rfl) ⟨3145472, by rfl⟩ : syracuseStep 4193963 = 6290945) B6290945
theorem B10084121 : Blo 1242439 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B6299531 : Blo 1242439 6299531 := bstep (se 1 (by rfl) ⟨4724648, by rfl⟩ : syracuseStep 6299531 = 9449297) B9449297
theorem B10616791 : Blo 1242439 10616791 := bstep (se 1 (by rfl) ⟨7962593, by rfl⟩ : syracuseStep 10616791 = 15925187) B15925187
theorem B1990751 : Blo 1242439 1990751 := bstep (se 1 (by rfl) ⟨1493063, by rfl⟩ : syracuseStep 1990751 = 2986127) B2986127
theorem B7962799 : Blo 1242439 7962799 := bstep (se 1 (by rfl) ⟨5972099, by rfl⟩ : syracuseStep 7962799 = 11944199) B11944199
theorem B30228713 : Blo 1242439 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B1769807 : Blo 1242439 1769807 := bstep (se 1 (by rfl) ⟨1327355, by rfl⟩ : syracuseStep 1769807 = 2654711) B2654711
theorem B4317563 : Blo 1242439 4317563 := bstep (se 1 (by rfl) ⟨3238172, by rfl⟩ : syracuseStep 4317563 = 6476345) B6476345
theorem B17023567 : Blo 1242439 17023567 := bstep (se 1 (by rfl) ⟨12767675, by rfl⟩ : syracuseStep 17023567 = 25535351) B25535351
theorem B3146465 : Blo 1242439 3146465 := bstep (se 2 (by rfl) ⟨1179924, by rfl⟩ : syracuseStep 3146465 = 2359849) B2359849
theorem B1680475 : Blo 1242439 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B2835967 : Blo 1242439 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B6293051 : Blo 1242439 6293051 := bstep (se 1 (by rfl) ⟨4719788, by rfl⟩ : syracuseStep 6293051 = 9439577) B9439577
theorem B11347877 : Blo 1242439 11347877 := bstep (se 4 (by rfl) ⟨1063863, by rfl⟩ : syracuseStep 11347877 = 2127727) B2127727
theorem B14165927 : Blo 1242439 14165927 := bstep (se 1 (by rfl) ⟨10624445, by rfl⟩ : syracuseStep 14165927 = 21248891) B21248891
theorem B2795975 : Blo 1242439 2795975 := bstep (se 1 (by rfl) ⟨2096981, by rfl⟩ : syracuseStep 2795975 = 4193963) B4193963
theorem B3148267 : Blo 1242439 3148267 := bstep (se 1 (by rfl) ⟨2361200, by rfl⟩ : syracuseStep 3148267 = 4722401) B4722401
theorem B2796479 : Blo 1242439 2796479 := bstep (se 1 (by rfl) ⟨2097359, by rfl⟩ : syracuseStep 2796479 = 4194719) B4194719
theorem B3149563 : Blo 1242439 3149563 := bstep (se 1 (by rfl) ⟨2362172, by rfl⟩ : syracuseStep 3149563 = 4724345) B4724345
theorem B4722569 : Blo 1242439 4722569 := bstep (se 2 (by rfl) ⟨1770963, by rfl⟩ : syracuseStep 4722569 = 3541927) B3541927
theorem B3149705 : Blo 1242439 3149705 := bstep (se 2 (by rfl) ⟨1181139, by rfl⟩ : syracuseStep 3149705 = 2362279) B2362279
theorem B1863659 : Blo 1242439 1863659 := bstep (se 1 (by rfl) ⟨1397744, by rfl⟩ : syracuseStep 1863659 = 2795489) B2795489
theorem B4198391 : Blo 1242439 4198391 := bstep (se 1 (by rfl) ⟨3148793, by rfl⟩ : syracuseStep 4198391 = 6297587) B6297587
theorem B6721643 : Blo 1242439 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B4722887 : Blo 1242439 4722887 := bstep (se 1 (by rfl) ⟨3542165, by rfl⟩ : syracuseStep 4722887 = 7084331) B7084331
theorem B2797775 : Blo 1242439 2797775 := bstep (se 1 (by rfl) ⟨2098331, by rfl⟩ : syracuseStep 2797775 = 4196663) B4196663
theorem B1863935 : Blo 1242439 1863935 := bstep (se 1 (by rfl) ⟨1397951, by rfl⟩ : syracuseStep 1863935 = 2795903) B2795903
theorem B2797919 : Blo 1242439 2797919 := bstep (se 1 (by rfl) ⟨2098439, by rfl⟩ : syracuseStep 2797919 = 4196879) B4196879
theorem B2798063 : Blo 1242439 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B3543659 : Blo 1242439 3543659 := bstep (se 1 (by rfl) ⟨2657744, by rfl⟩ : syracuseStep 3543659 = 5315489) B5315489
theorem B1864361 : Blo 1242439 1864361 := bstep (se 2 (by rfl) ⟨699135, by rfl⟩ : syracuseStep 1864361 = 1398271) B1398271
theorem B17912609 : Blo 1242439 17912609 := bstep (se 2 (by rfl) ⟨6717228, by rfl⟩ : syracuseStep 17912609 = 13434457) B13434457
theorem B6058921 : Blo 1242439 6058921 := bstep (se 2 (by rfl) ⟨2272095, by rfl⟩ : syracuseStep 6058921 = 4544191) B4544191
theorem B2798639 : Blo 1242439 2798639 := bstep (se 1 (by rfl) ⟨2098979, by rfl⟩ : syracuseStep 2798639 = 4197959) B4197959
theorem B6722747 : Blo 1242439 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B4199687 : Blo 1242439 4199687 := bstep (se 1 (by rfl) ⟨3149765, by rfl⟩ : syracuseStep 4199687 = 6299531) B6299531
theorem B1865063 : Blo 1242439 1865063 := bstep (se 1 (by rfl) ⟨1398797, by rfl⟩ : syracuseStep 1865063 = 2797595) B2797595
theorem B3192247 : Blo 1242439 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B1242651 : Blo 1242439 1242651 := bstep (se 1 (by rfl) ⟨931988, by rfl⟩ : syracuseStep 1242651 = 1863977) B1863977
theorem B2520649 : Blo 1242439 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B1865627 : Blo 1242439 1865627 := bstep (se 1 (by rfl) ⟨1399220, by rfl⟩ : syracuseStep 1865627 = 2798441) B2798441
theorem B26884061 : Blo 1242439 26884061 := bstep (se 3 (by rfl) ⟨5040761, by rfl⟩ : syracuseStep 26884061 = 10081523) B10081523
theorem B1398811 : Blo 1242439 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B1398847 : Blo 1242439 1398847 := bstep (se 1 (by rfl) ⟨1049135, by rfl⟩ : syracuseStep 1398847 = 2098271) B2098271
theorem B2799719 : Blo 1242439 2799719 := bstep (se 1 (by rfl) ⟨2099789, by rfl⟩ : syracuseStep 2799719 = 4199579) B4199579
theorem B1243263 : Blo 1242439 1243263 := bstep (se 1 (by rfl) ⟨932447, by rfl⟩ : syracuseStep 1243263 = 1864895) B1864895
theorem B11958425 : Blo 1242439 11958425 := bstep (se 2 (by rfl) ⟨4484409, by rfl⟩ : syracuseStep 11958425 = 8968819) B8968819
theorem B1865897 : Blo 1242439 1865897 := bstep (se 2 (by rfl) ⟨699711, by rfl⟩ : syracuseStep 1865897 = 1399423) B1399423
theorem B47790323 : Blo 1242439 47790323 := bstep (se 1 (by rfl) ⟨35842742, by rfl⟩ : syracuseStep 47790323 = 71685485) B71685485
theorem B9566531 : Blo 1242439 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B1243495 : Blo 1242439 1243495 := bstep (se 1 (by rfl) ⟨932621, by rfl⟩ : syracuseStep 1243495 = 1865243) B1865243
theorem B1243615 : Blo 1242439 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B1243775 : Blo 1242439 1243775 := bstep (se 1 (by rfl) ⟨932831, by rfl⟩ : syracuseStep 1243775 = 1865663) B1865663
theorem B275929811 : Blo 1242439 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B1866599 : Blo 1242439 1866599 := bstep (se 1 (by rfl) ⟨1399949, by rfl⟩ : syracuseStep 1866599 = 2799899) B2799899
theorem B30235517 : Blo 1242439 30235517 := bstep (se 3 (by rfl) ⟨5669159, by rfl⟩ : syracuseStep 30235517 = 11338319) B11338319
theorem B1866623 : Blo 1242439 1866623 := bstep (se 1 (by rfl) ⟨1399967, by rfl⟩ : syracuseStep 1866623 = 2799935) B2799935
theorem B2988991 : Blo 1242439 2988991 := bstep (se 1 (by rfl) ⟨2241743, by rfl⟩ : syracuseStep 2988991 = 4483487) B4483487
theorem B1244143 : Blo 1242439 1244143 := bstep (se 1 (by rfl) ⟨933107, by rfl⟩ : syracuseStep 1244143 = 1866215) B1866215
theorem B4193423 : Blo 1242439 4193423 := bstep (se 1 (by rfl) ⟨3145067, by rfl⟩ : syracuseStep 4193423 = 6290135) B6290135
theorem B4476320981 : Blo 1242439 4476320981 := bstep (se 7 (by rfl) ⟨52456886, by rfl⟩ : syracuseStep 4476320981 = 104913773) B104913773
theorem B6298883 : Blo 1242439 6298883 := bstep (se 1 (by rfl) ⟨4724162, by rfl⟩ : syracuseStep 6298883 = 9448325) B9448325
theorem B4193639 : Blo 1242439 4193639 := bstep (se 1 (by rfl) ⟨3145229, by rfl⟩ : syracuseStep 4193639 = 6290459) B6290459
theorem B2989433 : Blo 1242439 2989433 := bstep (se 2 (by rfl) ⟨1121037, by rfl⟩ : syracuseStep 2989433 = 2242075) B2242075
theorem B6299207 : Blo 1242439 6299207 := bstep (se 1 (by rfl) ⟨4724405, by rfl⟩ : syracuseStep 6299207 = 9448811) B9448811
theorem B14155721 : Blo 1242439 14155721 := bstep (se 2 (by rfl) ⟨5308395, by rfl⟩ : syracuseStep 14155721 = 10616791) B10616791
theorem B4481095 : Blo 1242439 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B20152475 : Blo 1242439 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B10617065 : Blo 1242439 10617065 := bstep (se 2 (by rfl) ⟨3981399, by rfl⟩ : syracuseStep 10617065 = 7962799) B7962799
theorem B5308669 : Blo 1242439 5308669 := bstep (se 3 (by rfl) ⟨995375, by rfl⟩ : syracuseStep 5308669 = 1990751) B1990751
theorem B2097643 : Blo 1242439 2097643 := bstep (se 1 (by rfl) ⟨1573232, by rfl⟩ : syracuseStep 2097643 = 3146465) B3146465
theorem B4481831 : Blo 1242439 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B4719485 : Blo 1242439 4719485 := bstep (se 3 (by rfl) ⟨884903, by rfl⟩ : syracuseStep 4719485 = 1769807) B1769807
theorem B7971821 : Blo 1242439 7971821 := bstep (se 3 (by rfl) ⟨1494716, by rfl⟩ : syracuseStep 7971821 = 2989433) B2989433
theorem B4195367 : Blo 1242439 4195367 := bstep (se 1 (by rfl) ⟨3146525, by rfl⟩ : syracuseStep 4195367 = 6293051) B6293051
theorem B8078561 : Blo 1242439 8078561 := bstep (se 2 (by rfl) ⟨3029460, by rfl⟩ : syracuseStep 8078561 = 6058921) B6058921
theorem B7972283 : Blo 1242439 7972283 := bstep (se 1 (by rfl) ⟨5979212, by rfl⟩ : syracuseStep 7972283 = 11958425) B11958425
theorem B31860215 : Blo 1242439 31860215 := bstep (se 1 (by rfl) ⟨23895161, by rfl⟩ : syracuseStep 31860215 = 47790323) B47790323
theorem B183953207 : Blo 1242439 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B2795615 : Blo 1242439 2795615 := bstep (se 1 (by rfl) ⟨2096711, by rfl⟩ : syracuseStep 2795615 = 4193423) B4193423
theorem B3360865 : Blo 1242439 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B2795759 : Blo 1242439 2795759 := bstep (se 1 (by rfl) ⟨2096819, by rfl⟩ : syracuseStep 2795759 = 4193639) B4193639
theorem B3148379 : Blo 1242439 3148379 := bstep (se 1 (by rfl) ⟨2361284, by rfl⟩ : syracuseStep 3148379 = 4722569) B4722569
theorem B2099803 : Blo 1242439 2099803 := bstep (se 1 (by rfl) ⟨1574852, by rfl⟩ : syracuseStep 2099803 = 3149705) B3149705
theorem B3148591 : Blo 1242439 3148591 := bstep (se 1 (by rfl) ⟨2361443, by rfl⟩ : syracuseStep 3148591 = 4722887) B4722887
theorem B2878375 : Blo 1242439 2878375 := bstep (se 1 (by rfl) ⟨2158781, by rfl⟩ : syracuseStep 2878375 = 4317563) B4317563
theorem B2362439 : Blo 1242439 2362439 := bstep (se 1 (by rfl) ⟨1771829, by rfl⟩ : syracuseStep 2362439 = 3543659) B3543659
theorem B4197689 : Blo 1242439 4197689 := bstep (se 2 (by rfl) ⟨1574133, by rfl⟩ : syracuseStep 4197689 = 3148267) B3148267
theorem B7565251 : Blo 1242439 7565251 := bstep (se 1 (by rfl) ⟨5673938, by rfl⟩ : syracuseStep 7565251 = 11347877) B11347877
theorem B2240633 : Blo 1242439 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B6377687 : Blo 1242439 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B1863983 : Blo 1242439 1863983 := bstep (se 1 (by rfl) ⟨1397987, by rfl⟩ : syracuseStep 1863983 = 2795975) B2795975
theorem B4256329 : Blo 1242439 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B20157011 : Blo 1242439 20157011 := bstep (se 1 (by rfl) ⟨15117758, by rfl⟩ : syracuseStep 20157011 = 30235517) B30235517
theorem B1864319 : Blo 1242439 1864319 := bstep (se 1 (by rfl) ⟨1398239, by rfl⟩ : syracuseStep 1864319 = 2796479) B2796479
theorem B3781289 : Blo 1242439 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B4199255 : Blo 1242439 4199255 := bstep (se 1 (by rfl) ⟨3149441, by rfl⟩ : syracuseStep 4199255 = 6298883) B6298883
theorem B4199417 : Blo 1242439 4199417 := bstep (se 2 (by rfl) ⟨1574781, by rfl⟩ : syracuseStep 4199417 = 3149563) B3149563
theorem B4199471 : Blo 1242439 4199471 := bstep (se 1 (by rfl) ⟨3149603, by rfl⟩ : syracuseStep 4199471 = 6299207) B6299207
theorem B1242439 : Blo 1242439 1242439 := bstep (se 1 (by rfl) ⟨931829, by rfl⟩ : syracuseStep 1242439 = 1863659) B1863659
theorem B2798927 : Blo 1242439 2798927 := bstep (se 1 (by rfl) ⟨2099195, by rfl⟩ : syracuseStep 2798927 = 4198391) B4198391
theorem B1865081 : Blo 1242439 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1865129 : Blo 1242439 1865129 := bstep (se 2 (by rfl) ⟨699423, by rfl⟩ : syracuseStep 1865129 = 1398847) B1398847
theorem B1865183 : Blo 1242439 1865183 := bstep (se 1 (by rfl) ⟨1398887, by rfl⟩ : syracuseStep 1865183 = 2797775) B2797775
theorem B1242623 : Blo 1242439 1242623 := bstep (se 1 (by rfl) ⟨931967, by rfl⟩ : syracuseStep 1242623 = 1863935) B1863935
theorem B1865279 : Blo 1242439 1865279 := bstep (se 1 (by rfl) ⟨1398959, by rfl⟩ : syracuseStep 1865279 = 2797919) B2797919
theorem B1865375 : Blo 1242439 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B1242907 : Blo 1242439 1242907 := bstep (se 1 (by rfl) ⟨932180, by rfl⟩ : syracuseStep 1242907 = 1864361) B1864361
theorem B11941739 : Blo 1242439 11941739 := bstep (se 1 (by rfl) ⟨8956304, by rfl⟩ : syracuseStep 11941739 = 17912609) B17912609
theorem B1865759 : Blo 1242439 1865759 := bstep (se 1 (by rfl) ⟨1399319, by rfl⟩ : syracuseStep 1865759 = 2798639) B2798639
theorem B22698089 : Blo 1242439 22698089 := bstep (se 2 (by rfl) ⟨8511783, by rfl⟩ : syracuseStep 22698089 = 17023567) B17023567
theorem B2799791 : Blo 1242439 2799791 := bstep (se 1 (by rfl) ⟨2099843, by rfl⟩ : syracuseStep 2799791 = 4199687) B4199687
theorem B1243375 : Blo 1242439 1243375 := bstep (se 1 (by rfl) ⟨932531, by rfl⟩ : syracuseStep 1243375 = 1865063) B1865063
theorem B1243751 : Blo 1242439 1243751 := bstep (se 1 (by rfl) ⟨932813, by rfl⟩ : syracuseStep 1243751 = 1865627) B1865627
theorem B9443951 : Blo 1242439 9443951 := bstep (se 1 (by rfl) ⟨7082963, by rfl⟩ : syracuseStep 9443951 = 14165927) B14165927
theorem B17922707 : Blo 1242439 17922707 := bstep (se 1 (by rfl) ⟨13442030, by rfl⟩ : syracuseStep 17922707 = 26884061) B26884061
theorem B1866479 : Blo 1242439 1866479 := bstep (se 1 (by rfl) ⟨1399859, by rfl⟩ : syracuseStep 1866479 = 2799719) B2799719
theorem B1243931 : Blo 1242439 1243931 := bstep (se 1 (by rfl) ⟨932948, by rfl⟩ : syracuseStep 1243931 = 1865897) B1865897
theorem B1244399 : Blo 1242439 1244399 := bstep (se 1 (by rfl) ⟨933299, by rfl⟩ : syracuseStep 1244399 = 1866599) B1866599
theorem B1244415 : Blo 1242439 1244415 := bstep (se 1 (by rfl) ⟨933311, by rfl⟩ : syracuseStep 1244415 = 1866623) B1866623
theorem B2984213987 : Blo 1242439 2984213987 := bstep (se 1 (by rfl) ⟨2238160490, by rfl⟩ : syracuseStep 2984213987 = 4476320981) B4476320981
theorem B15941285 : Blo 1242439 15941285 := bstep (se 4 (by rfl) ⟨1494495, by rfl⟩ : syracuseStep 15941285 = 2988991) B2988991
theorem B9437147 : Blo 1242439 9437147 := bstep (se 1 (by rfl) ⟨7077860, by rfl⟩ : syracuseStep 9437147 = 14155721) B14155721
theorem B13434983 : Blo 1242439 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B4481153 : Blo 1242439 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B4251791 : Blo 1242439 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B7078043 : Blo 1242439 7078043 := bstep (se 1 (by rfl) ⟨5308532, by rfl⟩ : syracuseStep 7078043 = 10617065) B10617065
theorem B7078225 : Blo 1242439 7078225 := bstep (se 2 (by rfl) ⟨2654334, by rfl⟩ : syracuseStep 7078225 = 5308669) B5308669
theorem B3146323 : Blo 1242439 3146323 := bstep (se 1 (by rfl) ⟨2359742, by rfl⟩ : syracuseStep 3146323 = 4719485) B4719485
theorem B122635471 : Blo 1242439 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B15132059 : Blo 1242439 15132059 := bstep (se 1 (by rfl) ⟨11349044, by rfl⟩ : syracuseStep 15132059 = 22698089) B22698089
theorem B2098919 : Blo 1242439 2098919 := bstep (se 1 (by rfl) ⟨1574189, by rfl⟩ : syracuseStep 2098919 = 3148379) B3148379
theorem B1574959 : Blo 1242439 1574959 := bstep (se 1 (by rfl) ⟨1181219, by rfl⟩ : syracuseStep 1574959 = 2362439) B2362439
theorem B10627523 : Blo 1242439 10627523 := bstep (se 1 (by rfl) ⟨7970642, by rfl⟩ : syracuseStep 10627523 = 15941285) B15941285
theorem B10087001 : Blo 1242439 10087001 := bstep (se 2 (by rfl) ⟨3782625, by rfl⟩ : syracuseStep 10087001 = 7565251) B7565251
theorem B5974793 : Blo 1242439 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B5975021 : Blo 1242439 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B13438007 : Blo 1242439 13438007 := bstep (se 1 (by rfl) ⟨10078505, by rfl⟩ : syracuseStep 13438007 = 20157011) B20157011
theorem B2796857 : Blo 1242439 2796857 := bstep (se 2 (by rfl) ⟨1048821, by rfl⟩ : syracuseStep 2796857 = 2097643) B2097643
theorem B2796911 : Blo 1242439 2796911 := bstep (se 1 (by rfl) ⟨2097683, by rfl⟩ : syracuseStep 2796911 = 4195367) B4195367
theorem B5385707 : Blo 1242439 5385707 := bstep (se 1 (by rfl) ⟨4039280, by rfl⟩ : syracuseStep 5385707 = 8078561) B8078561
theorem B4198121 : Blo 1242439 4198121 := bstep (se 2 (by rfl) ⟨1574295, by rfl⟩ : syracuseStep 4198121 = 3148591) B3148591
theorem B3837833 : Blo 1242439 3837833 := bstep (se 2 (by rfl) ⟨1439187, by rfl⟩ : syracuseStep 3837833 = 2878375) B2878375
theorem B1863743 : Blo 1242439 1863743 := bstep (se 1 (by rfl) ⟨1397807, by rfl⟩ : syracuseStep 1863743 = 2795615) B2795615
theorem B1863839 : Blo 1242439 1863839 := bstep (se 1 (by rfl) ⟨1397879, by rfl⟩ : syracuseStep 1863839 = 2795759) B2795759
theorem B6295967 : Blo 1242439 6295967 := bstep (se 1 (by rfl) ⟨4721975, by rfl⟩ : syracuseStep 6295967 = 9443951) B9443951
theorem B11948471 : Blo 1242439 11948471 := bstep (se 1 (by rfl) ⟨8961353, by rfl⟩ : syracuseStep 11948471 = 17922707) B17922707
theorem B2798459 : Blo 1242439 2798459 := bstep (se 1 (by rfl) ⟨2098844, by rfl⟩ : syracuseStep 2798459 = 4197689) B4197689
theorem B1242655 : Blo 1242439 1242655 := bstep (se 1 (by rfl) ⟨931991, by rfl⟩ : syracuseStep 1242655 = 1863983) B1863983
theorem B1242879 : Blo 1242439 1242879 := bstep (se 1 (by rfl) ⟨932159, by rfl⟩ : syracuseStep 1242879 = 1864319) B1864319
theorem B2987887 : Blo 1242439 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2799503 : Blo 1242439 2799503 := bstep (se 1 (by rfl) ⟨2099627, by rfl⟩ : syracuseStep 2799503 = 4199255) B4199255
theorem B5314547 : Blo 1242439 5314547 := bstep (se 1 (by rfl) ⟨3985910, by rfl⟩ : syracuseStep 5314547 = 7971821) B7971821
theorem B2799611 : Blo 1242439 2799611 := bstep (se 1 (by rfl) ⟨2099708, by rfl⟩ : syracuseStep 2799611 = 4199417) B4199417
theorem B2799647 : Blo 1242439 2799647 := bstep (se 1 (by rfl) ⟨2099735, by rfl⟩ : syracuseStep 2799647 = 4199471) B4199471
theorem B5675105 : Blo 1242439 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B2799737 : Blo 1242439 2799737 := bstep (se 2 (by rfl) ⟨1049901, by rfl⟩ : syracuseStep 2799737 = 2099803) B2099803
theorem B1865951 : Blo 1242439 1865951 := bstep (se 1 (by rfl) ⟨1399463, by rfl⟩ : syracuseStep 1865951 = 2798927) B2798927
theorem B1243387 : Blo 1242439 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B1243419 : Blo 1242439 1243419 := bstep (se 1 (by rfl) ⟨932564, by rfl⟩ : syracuseStep 1243419 = 1865129) B1865129
theorem B5314855 : Blo 1242439 5314855 := bstep (se 1 (by rfl) ⟨3986141, by rfl⟩ : syracuseStep 5314855 = 7972283) B7972283
theorem B1243455 : Blo 1242439 1243455 := bstep (se 1 (by rfl) ⟨932591, by rfl⟩ : syracuseStep 1243455 = 1865183) B1865183
theorem B21240143 : Blo 1242439 21240143 := bstep (se 1 (by rfl) ⟨15930107, by rfl⟩ : syracuseStep 21240143 = 31860215) B31860215
theorem B1243519 : Blo 1242439 1243519 := bstep (se 1 (by rfl) ⟨932639, by rfl⟩ : syracuseStep 1243519 = 1865279) B1865279
theorem B1243583 : Blo 1242439 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B7961159 : Blo 1242439 7961159 := bstep (se 1 (by rfl) ⟨5970869, by rfl⟩ : syracuseStep 7961159 = 11941739) B11941739
theorem B1243839 : Blo 1242439 1243839 := bstep (se 1 (by rfl) ⟨932879, by rfl⟩ : syracuseStep 1243839 = 1865759) B1865759
theorem B1866527 : Blo 1242439 1866527 := bstep (se 1 (by rfl) ⟨1399895, by rfl⟩ : syracuseStep 1866527 = 2799791) B2799791
theorem B10083437 : Blo 1242439 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B1244319 : Blo 1242439 1244319 := bstep (se 1 (by rfl) ⟨933239, by rfl⟩ : syracuseStep 1244319 = 1866479) B1866479
theorem B1989475991 : Blo 1242439 1989475991 := bstep (se 1 (by rfl) ⟨1492106993, by rfl⟩ : syracuseStep 1989475991 = 2984213987) B2984213987
theorem B6291431 : Blo 1242439 6291431 := bstep (se 1 (by rfl) ⟨4718573, by rfl⟩ : syracuseStep 6291431 = 9437147) B9437147
theorem B2834527 : Blo 1242439 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B4718695 : Blo 1242439 4718695 := bstep (se 1 (by rfl) ⟨3539021, by rfl⟩ : syracuseStep 4718695 = 7078043) B7078043
theorem B7086473 : Blo 1242439 7086473 := bstep (se 2 (by rfl) ⟨2657427, by rfl⟩ : syracuseStep 7086473 = 5314855) B5314855
theorem B9437633 : Blo 1242439 9437633 := bstep (se 2 (by rfl) ⟨3539112, by rfl⟩ : syracuseStep 9437633 = 7078225) B7078225
theorem B4195097 : Blo 1242439 4195097 := bstep (se 2 (by rfl) ⟨1573161, by rfl⟩ : syracuseStep 4195097 = 3146323) B3146323
theorem B163513961 : Blo 1242439 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B3983195 : Blo 1242439 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B3983347 : Blo 1242439 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B3590471 : Blo 1242439 3590471 := bstep (se 1 (by rfl) ⟨2692853, by rfl⟩ : syracuseStep 3590471 = 5385707) B5385707
theorem B3983849 : Blo 1242439 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B2558555 : Blo 1242439 2558555 := bstep (se 1 (by rfl) ⟨1918916, by rfl⟩ : syracuseStep 2558555 = 3837833) B3837833
theorem B2099945 : Blo 1242439 2099945 := bstep (se 2 (by rfl) ⟨787479, by rfl⟩ : syracuseStep 2099945 = 1574959) B1574959
theorem B8956655 : Blo 1242439 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B15133613 : Blo 1242439 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B4197311 : Blo 1242439 4197311 := bstep (se 1 (by rfl) ⟨3147983, by rfl⟩ : syracuseStep 4197311 = 6295967) B6295967
theorem B7965647 : Blo 1242439 7965647 := bstep (se 1 (by rfl) ⟨5974235, by rfl⟩ : syracuseStep 7965647 = 11948471) B11948471
theorem B10088039 : Blo 1242439 10088039 := bstep (se 1 (by rfl) ⟨7566029, by rfl⟩ : syracuseStep 10088039 = 15132059) B15132059
theorem B3543031 : Blo 1242439 3543031 := bstep (se 1 (by rfl) ⟨2657273, by rfl⟩ : syracuseStep 3543031 = 5314547) B5314547
theorem B14160095 : Blo 1242439 14160095 := bstep (se 1 (by rfl) ⟨10620071, by rfl⟩ : syracuseStep 14160095 = 21240143) B21240143
theorem B8958671 : Blo 1242439 8958671 := bstep (se 1 (by rfl) ⟨6719003, by rfl⟩ : syracuseStep 8958671 = 13438007) B13438007
theorem B6722291 : Blo 1242439 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B1864571 : Blo 1242439 1864571 := bstep (se 1 (by rfl) ⟨1398428, by rfl⟩ : syracuseStep 1864571 = 2796857) B2796857
theorem B1864607 : Blo 1242439 1864607 := bstep (se 1 (by rfl) ⟨1398455, by rfl⟩ : syracuseStep 1864607 = 2796911) B2796911
theorem B2798747 : Blo 1242439 2798747 := bstep (se 1 (by rfl) ⟨2099060, by rfl⟩ : syracuseStep 2798747 = 4198121) B4198121
theorem B1242495 : Blo 1242439 1242495 := bstep (se 1 (by rfl) ⟨931871, by rfl⟩ : syracuseStep 1242495 = 1863743) B1863743
theorem B2987435 : Blo 1242439 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B1242559 : Blo 1242439 1242559 := bstep (se 1 (by rfl) ⟨931919, by rfl⟩ : syracuseStep 1242559 = 1863839) B1863839
theorem B1865639 : Blo 1242439 1865639 := bstep (se 1 (by rfl) ⟨1399229, by rfl⟩ : syracuseStep 1865639 = 2798459) B2798459
theorem B1399279 : Blo 1242439 1399279 := bstep (se 1 (by rfl) ⟨1049459, by rfl⟩ : syracuseStep 1399279 = 2098919) B2098919
theorem B1866335 : Blo 1242439 1866335 := bstep (se 1 (by rfl) ⟨1399751, by rfl⟩ : syracuseStep 1866335 = 2799503) B2799503
theorem B1866407 : Blo 1242439 1866407 := bstep (se 1 (by rfl) ⟨1399805, by rfl⟩ : syracuseStep 1866407 = 2799611) B2799611
theorem B1866431 : Blo 1242439 1866431 := bstep (se 1 (by rfl) ⟨1399823, by rfl⟩ : syracuseStep 1866431 = 2799647) B2799647
theorem B1866491 : Blo 1242439 1866491 := bstep (se 1 (by rfl) ⟨1399868, by rfl⟩ : syracuseStep 1866491 = 2799737) B2799737
theorem B1243967 : Blo 1242439 1243967 := bstep (se 1 (by rfl) ⟨932975, by rfl⟩ : syracuseStep 1243967 = 1865951) B1865951
theorem B7085015 : Blo 1242439 7085015 := bstep (se 1 (by rfl) ⟨5313761, by rfl⟩ : syracuseStep 7085015 = 10627523) B10627523
theorem B5307439 : Blo 1242439 5307439 := bstep (se 1 (by rfl) ⟨3980579, by rfl⟩ : syracuseStep 5307439 = 7961159) B7961159
theorem B6724667 : Blo 1242439 6724667 := bstep (se 1 (by rfl) ⟨5043500, by rfl⟩ : syracuseStep 6724667 = 10087001) B10087001
theorem B1244351 : Blo 1242439 1244351 := bstep (se 1 (by rfl) ⟨933263, by rfl⟩ : syracuseStep 1244351 = 1866527) B1866527
theorem B1326317327 : Blo 1242439 1326317327 := bstep (se 1 (by rfl) ⟨994737995, by rfl⟩ : syracuseStep 1326317327 = 1989475991) B1989475991
theorem B4194287 : Blo 1242439 4194287 := bstep (se 1 (by rfl) ⟨3145715, by rfl⟩ : syracuseStep 4194287 = 6291431) B6291431
theorem B6291593 : Blo 1242439 6291593 := bstep (se 2 (by rfl) ⟨2359347, by rfl⟩ : syracuseStep 6291593 = 4718695) B4718695
theorem B6291755 : Blo 1242439 6291755 := bstep (se 1 (by rfl) ⟨4718816, by rfl⟩ : syracuseStep 6291755 = 9437633) B9437633
theorem B5972447 : Blo 1242439 5972447 := bstep (se 1 (by rfl) ⟨4479335, by rfl⟩ : syracuseStep 5972447 = 8958671) B8958671
theorem B1991623 : Blo 1242439 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B2655463 : Blo 1242439 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B2393647 : Blo 1242439 2393647 := bstep (se 1 (by rfl) ⟨1795235, by rfl⟩ : syracuseStep 2393647 = 3590471) B3590471
theorem B2655899 : Blo 1242439 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1705703 : Blo 1242439 1705703 := bstep (se 1 (by rfl) ⟨1279277, by rfl⟩ : syracuseStep 1705703 = 2558555) B2558555
theorem B17926109 : Blo 1242439 17926109 := bstep (se 3 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 17926109 = 6722291) B6722291
theorem B5310431 : Blo 1242439 5310431 := bstep (se 1 (by rfl) ⟨3982823, by rfl⟩ : syracuseStep 5310431 = 7965647) B7965647
theorem B4483111 : Blo 1242439 4483111 := bstep (se 1 (by rfl) ⟨3362333, by rfl⟩ : syracuseStep 4483111 = 6724667) B6724667
theorem B40356301 : Blo 1242439 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B21244517 : Blo 1242439 21244517 := bstep (se 4 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 21244517 = 3983347) B3983347
theorem B2796191 : Blo 1242439 2796191 := bstep (se 1 (by rfl) ⟨2097143, by rfl⟩ : syracuseStep 2796191 = 4194287) B4194287
theorem B3779369 : Blo 1242439 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B9440063 : Blo 1242439 9440063 := bstep (se 1 (by rfl) ⟨7080047, by rfl⟩ : syracuseStep 9440063 = 14160095) B14160095
theorem B2796731 : Blo 1242439 2796731 := bstep (se 1 (by rfl) ⟨2097548, by rfl⟩ : syracuseStep 2796731 = 4195097) B4195097
theorem B2798207 : Blo 1242439 2798207 := bstep (se 1 (by rfl) ⟨2098655, by rfl⟩ : syracuseStep 2798207 = 4197311) B4197311
theorem B4723343 : Blo 1242439 4723343 := bstep (se 1 (by rfl) ⟨3542507, by rfl⟩ : syracuseStep 4723343 = 7085015) B7085015
theorem B4724041 : Blo 1242439 4724041 := bstep (se 2 (by rfl) ⟨1771515, by rfl⟩ : syracuseStep 4724041 = 3543031) B3543031
theorem B4724315 : Blo 1242439 4724315 := bstep (se 1 (by rfl) ⟨3543236, by rfl⟩ : syracuseStep 4724315 = 7086473) B7086473
theorem B1243047 : Blo 1242439 1243047 := bstep (se 1 (by rfl) ⟨932285, by rfl⟩ : syracuseStep 1243047 = 1864571) B1864571
theorem B1243071 : Blo 1242439 1243071 := bstep (se 1 (by rfl) ⟨932303, by rfl⟩ : syracuseStep 1243071 = 1864607) B1864607
theorem B1865705 : Blo 1242439 1865705 := bstep (se 2 (by rfl) ⟨699639, by rfl⟩ : syracuseStep 1865705 = 1399279) B1399279
theorem B1865831 : Blo 1242439 1865831 := bstep (se 1 (by rfl) ⟨1399373, by rfl⟩ : syracuseStep 1865831 = 2798747) B2798747
theorem B109009307 : Blo 1242439 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B1243759 : Blo 1242439 1243759 := bstep (se 1 (by rfl) ⟨932819, by rfl⟩ : syracuseStep 1243759 = 1865639) B1865639
theorem B7076585 : Blo 1242439 7076585 := bstep (se 2 (by rfl) ⟨2653719, by rfl⟩ : syracuseStep 7076585 = 5307439) B5307439
theorem B1244223 : Blo 1242439 1244223 := bstep (se 1 (by rfl) ⟨933167, by rfl⟩ : syracuseStep 1244223 = 1866335) B1866335
theorem B1244271 : Blo 1242439 1244271 := bstep (se 1 (by rfl) ⟨933203, by rfl⟩ : syracuseStep 1244271 = 1866407) B1866407
theorem B1244287 : Blo 1242439 1244287 := bstep (se 1 (by rfl) ⟨933215, by rfl⟩ : syracuseStep 1244287 = 1866431) B1866431
theorem B1399963 : Blo 1242439 1399963 := bstep (se 1 (by rfl) ⟨1049972, by rfl⟩ : syracuseStep 1399963 = 2099945) B2099945
theorem B5971103 : Blo 1242439 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B1244327 : Blo 1242439 1244327 := bstep (se 1 (by rfl) ⟨933245, by rfl⟩ : syracuseStep 1244327 = 1866491) B1866491
theorem B6725359 : Blo 1242439 6725359 := bstep (se 1 (by rfl) ⟨5044019, by rfl⟩ : syracuseStep 6725359 = 10088039) B10088039
theorem B884211551 : Blo 1242439 884211551 := bstep (se 1 (by rfl) ⟨663158663, by rfl⟩ : syracuseStep 884211551 = 1326317327) B1326317327
theorem B4194395 : Blo 1242439 4194395 := bstep (se 1 (by rfl) ⟨3145796, by rfl⟩ : syracuseStep 4194395 = 6291593) B6291593
theorem B4194503 : Blo 1242439 4194503 := bstep (se 1 (by rfl) ⟨3145877, by rfl⟩ : syracuseStep 4194503 = 6291755) B6291755
theorem B3981631 : Blo 1242439 3981631 := bstep (se 1 (by rfl) ⟨2986223, by rfl⟩ : syracuseStep 3981631 = 5972447) B5972447
theorem B1770599 : Blo 1242439 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B2655497 : Blo 1242439 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B3540287 : Blo 1242439 3540287 := bstep (se 1 (by rfl) ⟨2655215, by rfl⟩ : syracuseStep 3540287 = 5310431) B5310431
theorem B72672871 : Blo 1242439 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B3540617 : Blo 1242439 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B6293375 : Blo 1242439 6293375 := bstep (se 1 (by rfl) ⟨4720031, by rfl⟩ : syracuseStep 6293375 = 9440063) B9440063
theorem B589474367 : Blo 1242439 589474367 := bstep (se 1 (by rfl) ⟨442105775, by rfl⟩ : syracuseStep 589474367 = 884211551) B884211551
theorem B3148895 : Blo 1242439 3148895 := bstep (se 1 (by rfl) ⟨2361671, by rfl⟩ : syracuseStep 3148895 = 4723343) B4723343
theorem B53808401 : Blo 1242439 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B51064469 : Blo 1242439 51064469 := bstep (se 6 (by rfl) ⟨1196823, by rfl⟩ : syracuseStep 51064469 = 2393647) B2393647
theorem B3149543 : Blo 1242439 3149543 := bstep (se 1 (by rfl) ⟨2362157, by rfl⟩ : syracuseStep 3149543 = 4724315) B4724315
theorem B1864127 : Blo 1242439 1864127 := bstep (se 1 (by rfl) ⟨1398095, by rfl⟩ : syracuseStep 1864127 = 2796191) B2796191
theorem B2519579 : Blo 1242439 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B1864487 : Blo 1242439 1864487 := bstep (se 1 (by rfl) ⟨1398365, by rfl⟩ : syracuseStep 1864487 = 2796731) B2796731
theorem B8967145 : Blo 1242439 8967145 := bstep (se 2 (by rfl) ⟨3362679, by rfl⟩ : syracuseStep 8967145 = 6725359) B6725359
theorem B5977481 : Blo 1242439 5977481 := bstep (se 2 (by rfl) ⟨2241555, by rfl⟩ : syracuseStep 5977481 = 4483111) B4483111
theorem B1865471 : Blo 1242439 1865471 := bstep (se 1 (by rfl) ⟨1399103, by rfl⟩ : syracuseStep 1865471 = 2798207) B2798207
theorem B11950739 : Blo 1242439 11950739 := bstep (se 1 (by rfl) ⟨8963054, by rfl⟩ : syracuseStep 11950739 = 17926109) B17926109
theorem B1243803 : Blo 1242439 1243803 := bstep (se 1 (by rfl) ⟨932852, by rfl⟩ : syracuseStep 1243803 = 1865705) B1865705
theorem B1243887 : Blo 1242439 1243887 := bstep (se 1 (by rfl) ⟨932915, by rfl⟩ : syracuseStep 1243887 = 1865831) B1865831
theorem B1866617 : Blo 1242439 1866617 := bstep (se 2 (by rfl) ⟨699981, by rfl⟩ : syracuseStep 1866617 = 1399963) B1399963
theorem B14163011 : Blo 1242439 14163011 := bstep (se 1 (by rfl) ⟨10622258, by rfl⟩ : syracuseStep 14163011 = 21244517) B21244517
theorem B6298721 : Blo 1242439 6298721 := bstep (se 2 (by rfl) ⟨2362020, by rfl⟩ : syracuseStep 6298721 = 4724041) B4724041
theorem B4717723 : Blo 1242439 4717723 := bstep (se 1 (by rfl) ⟨3538292, by rfl⟩ : syracuseStep 4717723 = 7076585) B7076585
theorem B3980735 : Blo 1242439 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B18194165 : Blo 1242439 18194165 := bstep (se 5 (by rfl) ⟨852851, by rfl⟩ : syracuseStep 18194165 = 1705703) B1705703
theorem B1679719 : Blo 1242439 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B5308841 : Blo 1242439 5308841 := bstep (se 2 (by rfl) ⟨1990815, by rfl⟩ : syracuseStep 5308841 = 3981631) B3981631
theorem B1770331 : Blo 1242439 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B2360191 : Blo 1242439 2360191 := bstep (se 1 (by rfl) ⟨1770143, by rfl⟩ : syracuseStep 2360191 = 3540287) B3540287
theorem B2360411 : Blo 1242439 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B4195583 : Blo 1242439 4195583 := bstep (se 1 (by rfl) ⟨3146687, by rfl⟩ : syracuseStep 4195583 = 6293375) B6293375
theorem B2099263 : Blo 1242439 2099263 := bstep (se 1 (by rfl) ⟨1574447, by rfl⟩ : syracuseStep 2099263 = 3148895) B3148895
theorem B96897161 : Blo 1242439 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B2099695 : Blo 1242439 2099695 := bstep (se 1 (by rfl) ⟨1574771, by rfl⟩ : syracuseStep 2099695 = 3149543) B3149543
theorem B2796263 : Blo 1242439 2796263 := bstep (se 1 (by rfl) ⟨2097197, by rfl⟩ : syracuseStep 2796263 = 4194395) B4194395
theorem B2796335 : Blo 1242439 2796335 := bstep (se 1 (by rfl) ⟨2097251, by rfl⟩ : syracuseStep 2796335 = 4194503) B4194503
theorem B4721597 : Blo 1242439 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B11956193 : Blo 1242439 11956193 := bstep (se 2 (by rfl) ⟨4483572, by rfl⟩ : syracuseStep 11956193 = 8967145) B8967145
theorem B392982911 : Blo 1242439 392982911 := bstep (se 1 (by rfl) ⟨294737183, by rfl⟩ : syracuseStep 392982911 = 589474367) B589474367
theorem B7967159 : Blo 1242439 7967159 := bstep (se 1 (by rfl) ⟨5975369, by rfl⟩ : syracuseStep 7967159 = 11950739) B11950739
theorem B9442007 : Blo 1242439 9442007 := bstep (se 1 (by rfl) ⟨7081505, by rfl⟩ : syracuseStep 9442007 = 14163011) B14163011
theorem B4199147 : Blo 1242439 4199147 := bstep (se 1 (by rfl) ⟨3149360, by rfl⟩ : syracuseStep 4199147 = 6298721) B6298721
theorem B34042979 : Blo 1242439 34042979 := bstep (se 1 (by rfl) ⟨25532234, by rfl⟩ : syracuseStep 34042979 = 51064469) B51064469
theorem B12129443 : Blo 1242439 12129443 := bstep (se 1 (by rfl) ⟨9097082, by rfl⟩ : syracuseStep 12129443 = 18194165) B18194165
theorem B1242751 : Blo 1242439 1242751 := bstep (se 1 (by rfl) ⟨932063, by rfl⟩ : syracuseStep 1242751 = 1864127) B1864127
theorem B1242991 : Blo 1242439 1242991 := bstep (se 1 (by rfl) ⟨932243, by rfl⟩ : syracuseStep 1242991 = 1864487) B1864487
theorem B15939949 : Blo 1242439 15939949 := bstep (se 3 (by rfl) ⟨2988740, by rfl⟩ : syracuseStep 15939949 = 5977481) B5977481
theorem B1243647 : Blo 1242439 1243647 := bstep (se 1 (by rfl) ⟨932735, by rfl⟩ : syracuseStep 1243647 = 1865471) B1865471
theorem B6290297 : Blo 1242439 6290297 := bstep (se 2 (by rfl) ⟨2358861, by rfl⟩ : syracuseStep 6290297 = 4717723) B4717723
theorem B1244411 : Blo 1242439 1244411 := bstep (se 1 (by rfl) ⟨933308, by rfl⟩ : syracuseStep 1244411 = 1866617) B1866617
theorem B35872267 : Blo 1242439 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B2653823 : Blo 1242439 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B261988607 : Blo 1242439 261988607 := bstep (se 1 (by rfl) ⟨196491455, by rfl⟩ : syracuseStep 261988607 = 392982911) B392982911
theorem B3539227 : Blo 1242439 3539227 := bstep (se 1 (by rfl) ⟨2654420, by rfl⟩ : syracuseStep 3539227 = 5308841) B5308841
theorem B258392429 : Blo 1242439 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B1573607 : Blo 1242439 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B8086295 : Blo 1242439 8086295 := bstep (se 1 (by rfl) ⟨6064721, by rfl⟩ : syracuseStep 8086295 = 12129443) B12129443
theorem B2360441 : Blo 1242439 2360441 := bstep (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) B1770331
theorem B3146921 : Blo 1242439 3146921 := bstep (se 2 (by rfl) ⟨1180095, by rfl⟩ : syracuseStep 3146921 = 2360191) B2360191
theorem B3147731 : Blo 1242439 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B5311439 : Blo 1242439 5311439 := bstep (se 1 (by rfl) ⟨3983579, by rfl⟩ : syracuseStep 5311439 = 7967159) B7967159
theorem B2239625 : Blo 1242439 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B6294671 : Blo 1242439 6294671 := bstep (se 1 (by rfl) ⟨4721003, by rfl⟩ : syracuseStep 6294671 = 9442007) B9442007
theorem B21253265 : Blo 1242439 21253265 := bstep (se 2 (by rfl) ⟨7969974, by rfl⟩ : syracuseStep 21253265 = 15939949) B15939949
theorem B22695319 : Blo 1242439 22695319 := bstep (se 1 (by rfl) ⟨17021489, by rfl⟩ : syracuseStep 22695319 = 34042979) B34042979
theorem B2797055 : Blo 1242439 2797055 := bstep (se 1 (by rfl) ⟨2097791, by rfl⟩ : syracuseStep 2797055 = 4195583) B4195583
theorem B1864175 : Blo 1242439 1864175 := bstep (se 1 (by rfl) ⟨1398131, by rfl⟩ : syracuseStep 1864175 = 2796263) B2796263
theorem B1864223 : Blo 1242439 1864223 := bstep (se 1 (by rfl) ⟨1398167, by rfl⟩ : syracuseStep 1864223 = 2796335) B2796335
theorem B47829689 : Blo 1242439 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B2799017 : Blo 1242439 2799017 := bstep (se 2 (by rfl) ⟨1049631, by rfl⟩ : syracuseStep 2799017 = 2099263) B2099263
theorem B2799431 : Blo 1242439 2799431 := bstep (se 1 (by rfl) ⟨2099573, by rfl⟩ : syracuseStep 2799431 = 4199147) B4199147
theorem B2799593 : Blo 1242439 2799593 := bstep (se 2 (by rfl) ⟨1049847, by rfl⟩ : syracuseStep 2799593 = 2099695) B2099695
theorem B4193531 : Blo 1242439 4193531 := bstep (se 1 (by rfl) ⟨3145148, by rfl⟩ : syracuseStep 4193531 = 6290297) B6290297
theorem B1769215 : Blo 1242439 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B7970795 : Blo 1242439 7970795 := bstep (se 1 (by rfl) ⟨5978096, by rfl⟩ : syracuseStep 7970795 = 11956193) B11956193
theorem B172261619 : Blo 1242439 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B4718969 : Blo 1242439 4718969 := bstep (se 2 (by rfl) ⟨1769613, by rfl⟩ : syracuseStep 4718969 = 3539227) B3539227
theorem B2097947 : Blo 1242439 2097947 := bstep (se 1 (by rfl) ⟨1573460, by rfl⟩ : syracuseStep 2097947 = 3146921) B3146921
theorem B2098487 : Blo 1242439 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B4196285 : Blo 1242439 4196285 := bstep (se 3 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 4196285 = 1573607) B1573607
theorem B3540959 : Blo 1242439 3540959 := bstep (se 1 (by rfl) ⟨2655719, by rfl⟩ : syracuseStep 3540959 = 5311439) B5311439
theorem B21563453 : Blo 1242439 21563453 := bstep (se 3 (by rfl) ⟨4043147, by rfl⟩ : syracuseStep 21563453 = 8086295) B8086295
theorem B1493083 : Blo 1242439 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B4196447 : Blo 1242439 4196447 := bstep (se 1 (by rfl) ⟨3147335, by rfl⟩ : syracuseStep 4196447 = 6294671) B6294671
theorem B2795687 : Blo 1242439 2795687 := bstep (se 1 (by rfl) ⟨2096765, by rfl⟩ : syracuseStep 2795687 = 4193531) B4193531
theorem B6294509 : Blo 1242439 6294509 := bstep (se 3 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 6294509 = 2360441) B2360441
theorem B31886459 : Blo 1242439 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B14168843 : Blo 1242439 14168843 := bstep (se 1 (by rfl) ⟨10626632, by rfl⟩ : syracuseStep 14168843 = 21253265) B21253265
theorem B1864703 : Blo 1242439 1864703 := bstep (se 1 (by rfl) ⟨1398527, by rfl⟩ : syracuseStep 1864703 = 2797055) B2797055
theorem B5313863 : Blo 1242439 5313863 := bstep (se 1 (by rfl) ⟨3985397, by rfl⟩ : syracuseStep 5313863 = 7970795) B7970795
theorem B1242783 : Blo 1242439 1242783 := bstep (se 1 (by rfl) ⟨932087, by rfl⟩ : syracuseStep 1242783 = 1864175) B1864175
theorem B1242815 : Blo 1242439 1242815 := bstep (se 1 (by rfl) ⟨932111, by rfl⟩ : syracuseStep 1242815 = 1864223) B1864223
theorem B698636285 : Blo 1242439 698636285 := bstep (se 3 (by rfl) ⟨130994303, by rfl⟩ : syracuseStep 698636285 = 261988607) B261988607
theorem B1866011 : Blo 1242439 1866011 := bstep (se 1 (by rfl) ⟨1399508, by rfl⟩ : syracuseStep 1866011 = 2799017) B2799017
theorem B1866287 : Blo 1242439 1866287 := bstep (se 1 (by rfl) ⟨1399715, by rfl⟩ : syracuseStep 1866287 = 2799431) B2799431
theorem B1866395 : Blo 1242439 1866395 := bstep (se 1 (by rfl) ⟨1399796, by rfl⟩ : syracuseStep 1866395 = 2799593) B2799593
theorem B30260425 : Blo 1242439 30260425 := bstep (se 2 (by rfl) ⟨11347659, by rfl⟩ : syracuseStep 30260425 = 22695319) B22695319
theorem B2358953 : Blo 1242439 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B3145979 : Blo 1242439 3145979 := bstep (se 1 (by rfl) ⟨2359484, by rfl⟩ : syracuseStep 3145979 = 4718969) B4718969
theorem B7963109 : Blo 1242439 7963109 := bstep (se 4 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 7963109 = 1493083) B1493083
theorem B9445895 : Blo 1242439 9445895 := bstep (se 1 (by rfl) ⟨7084421, by rfl⟩ : syracuseStep 9445895 = 14168843) B14168843
theorem B2360639 : Blo 1242439 2360639 := bstep (se 1 (by rfl) ⟨1770479, by rfl⟩ : syracuseStep 2360639 = 3540959) B3540959
theorem B465757523 : Blo 1242439 465757523 := bstep (se 1 (by rfl) ⟨349318142, by rfl⟩ : syracuseStep 465757523 = 698636285) B698636285
theorem B40347233 : Blo 1242439 40347233 := bstep (se 2 (by rfl) ⟨15130212, by rfl⟩ : syracuseStep 40347233 = 30260425) B30260425
theorem B4196339 : Blo 1242439 4196339 := bstep (se 1 (by rfl) ⟨3147254, by rfl⟩ : syracuseStep 4196339 = 6294509) B6294509
theorem B57502541 : Blo 1242439 57502541 := bstep (se 3 (by rfl) ⟨10781726, by rfl⟩ : syracuseStep 57502541 = 21563453) B21563453
theorem B2797523 : Blo 1242439 2797523 := bstep (se 1 (by rfl) ⟨2098142, by rfl⟩ : syracuseStep 2797523 = 4196285) B4196285
theorem B2797631 : Blo 1242439 2797631 := bstep (se 1 (by rfl) ⟨2098223, by rfl⟩ : syracuseStep 2797631 = 4196447) B4196447
theorem B1863791 : Blo 1242439 1863791 := bstep (se 1 (by rfl) ⟨1397843, by rfl⟩ : syracuseStep 1863791 = 2795687) B2795687
theorem B114841079 : Blo 1242439 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B1398631 : Blo 1242439 1398631 := bstep (se 1 (by rfl) ⟨1048973, by rfl⟩ : syracuseStep 1398631 = 2097947) B2097947
theorem B1243135 : Blo 1242439 1243135 := bstep (se 1 (by rfl) ⟨932351, by rfl⟩ : syracuseStep 1243135 = 1864703) B1864703
theorem B14170301 : Blo 1242439 14170301 := bstep (se 3 (by rfl) ⟨2656931, by rfl⟩ : syracuseStep 14170301 = 5313863) B5313863
theorem B1398991 : Blo 1242439 1398991 := bstep (se 1 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 1398991 = 2098487) B2098487
theorem B1244007 : Blo 1242439 1244007 := bstep (se 1 (by rfl) ⟨933005, by rfl⟩ : syracuseStep 1244007 = 1866011) B1866011
theorem B1244191 : Blo 1242439 1244191 := bstep (se 1 (by rfl) ⟨933143, by rfl⟩ : syracuseStep 1244191 = 1866287) B1866287
theorem B1244263 : Blo 1242439 1244263 := bstep (se 1 (by rfl) ⟨933197, by rfl⟩ : syracuseStep 1244263 = 1866395) B1866395
theorem B21257639 : Blo 1242439 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B1572635 : Blo 1242439 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B2097319 : Blo 1242439 2097319 := bstep (se 1 (by rfl) ⟨1572989, by rfl⟩ : syracuseStep 2097319 = 3145979) B3145979
theorem B5308739 : Blo 1242439 5308739 := bstep (se 1 (by rfl) ⟨3981554, by rfl⟩ : syracuseStep 5308739 = 7963109) B7963109
theorem B1573759 : Blo 1242439 1573759 := bstep (se 1 (by rfl) ⟨1180319, by rfl⟩ : syracuseStep 1573759 = 2360639) B2360639
theorem B9446867 : Blo 1242439 9446867 := bstep (se 1 (by rfl) ⟨7085150, by rfl⟩ : syracuseStep 9446867 = 14170301) B14170301
theorem B310505015 : Blo 1242439 310505015 := bstep (se 1 (by rfl) ⟨232878761, by rfl⟩ : syracuseStep 310505015 = 465757523) B465757523
theorem B26898155 : Blo 1242439 26898155 := bstep (se 1 (by rfl) ⟨20173616, by rfl⟩ : syracuseStep 26898155 = 40347233) B40347233
theorem B2797559 : Blo 1242439 2797559 := bstep (se 1 (by rfl) ⟨2098169, by rfl⟩ : syracuseStep 2797559 = 4196339) B4196339
theorem B38335027 : Blo 1242439 38335027 := bstep (se 1 (by rfl) ⟨28751270, by rfl⟩ : syracuseStep 38335027 = 57502541) B57502541
theorem B1864841 : Blo 1242439 1864841 := bstep (se 2 (by rfl) ⟨699315, by rfl⟩ : syracuseStep 1864841 = 1398631) B1398631
theorem B1865015 : Blo 1242439 1865015 := bstep (se 1 (by rfl) ⟨1398761, by rfl⟩ : syracuseStep 1865015 = 2797523) B2797523
theorem B1865087 : Blo 1242439 1865087 := bstep (se 1 (by rfl) ⟨1398815, by rfl⟩ : syracuseStep 1865087 = 2797631) B2797631
theorem B1242527 : Blo 1242439 1242527 := bstep (se 1 (by rfl) ⟨931895, by rfl⟩ : syracuseStep 1242527 = 1863791) B1863791
theorem B1865321 : Blo 1242439 1865321 := bstep (se 2 (by rfl) ⟨699495, by rfl⟩ : syracuseStep 1865321 = 1398991) B1398991
theorem B6297263 : Blo 1242439 6297263 := bstep (se 1 (by rfl) ⟨4722947, by rfl⟩ : syracuseStep 6297263 = 9445895) B9445895
theorem B76560719 : Blo 1242439 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B4193693 : Blo 1242439 4193693 := bstep (se 3 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 4193693 = 1572635) B1572635
theorem B14171759 : Blo 1242439 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B3539159 : Blo 1242439 3539159 := bstep (se 1 (by rfl) ⟨2654369, by rfl⟩ : syracuseStep 3539159 = 5308739) B5308739
theorem B204161917 : Blo 1242439 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B2098345 : Blo 1242439 2098345 := bstep (se 2 (by rfl) ⟨786879, by rfl⟩ : syracuseStep 2098345 = 1573759) B1573759
theorem B2795795 : Blo 1242439 2795795 := bstep (se 1 (by rfl) ⟨2096846, by rfl⟩ : syracuseStep 2795795 = 4193693) B4193693
theorem B9447839 : Blo 1242439 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B2796425 : Blo 1242439 2796425 := bstep (se 2 (by rfl) ⟨1048659, by rfl⟩ : syracuseStep 2796425 = 2097319) B2097319
theorem B51113369 : Blo 1242439 51113369 := bstep (se 2 (by rfl) ⟨19167513, by rfl⟩ : syracuseStep 51113369 = 38335027) B38335027
theorem B4198175 : Blo 1242439 4198175 := bstep (se 1 (by rfl) ⟨3148631, by rfl⟩ : syracuseStep 4198175 = 6297263) B6297263
theorem B1865039 : Blo 1242439 1865039 := bstep (se 1 (by rfl) ⟨1398779, by rfl⟩ : syracuseStep 1865039 = 2797559) B2797559
theorem B1243227 : Blo 1242439 1243227 := bstep (se 1 (by rfl) ⟨932420, by rfl⟩ : syracuseStep 1243227 = 1864841) B1864841
theorem B1243343 : Blo 1242439 1243343 := bstep (se 1 (by rfl) ⟨932507, by rfl⟩ : syracuseStep 1243343 = 1865015) B1865015
theorem B1243391 : Blo 1242439 1243391 := bstep (se 1 (by rfl) ⟨932543, by rfl⟩ : syracuseStep 1243391 = 1865087) B1865087
theorem B6297911 : Blo 1242439 6297911 := bstep (se 1 (by rfl) ⟨4723433, by rfl⟩ : syracuseStep 6297911 = 9446867) B9446867
theorem B1243547 : Blo 1242439 1243547 := bstep (se 1 (by rfl) ⟨932660, by rfl⟩ : syracuseStep 1243547 = 1865321) B1865321
theorem B828013373 : Blo 1242439 828013373 := bstep (se 3 (by rfl) ⟨155252507, by rfl⟩ : syracuseStep 828013373 = 310505015) B310505015
theorem B17932103 : Blo 1242439 17932103 := bstep (se 1 (by rfl) ⟨13449077, by rfl⟩ : syracuseStep 17932103 = 26898155) B26898155
theorem B2359439 : Blo 1242439 2359439 := bstep (se 1 (by rfl) ⟨1769579, by rfl⟩ : syracuseStep 2359439 = 3539159) B3539159
theorem B11954735 : Blo 1242439 11954735 := bstep (se 1 (by rfl) ⟨8966051, by rfl⟩ : syracuseStep 11954735 = 17932103) B17932103
theorem B272215889 : Blo 1242439 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B1863863 : Blo 1242439 1863863 := bstep (se 1 (by rfl) ⟨1397897, by rfl⟩ : syracuseStep 1863863 = 2795795) B2795795
theorem B4198607 : Blo 1242439 4198607 := bstep (se 1 (by rfl) ⟨3148955, by rfl⟩ : syracuseStep 4198607 = 6297911) B6297911
theorem B2797793 : Blo 1242439 2797793 := bstep (se 2 (by rfl) ⟨1049172, by rfl⟩ : syracuseStep 2797793 = 2098345) B2098345
theorem B1864283 : Blo 1242439 1864283 := bstep (se 1 (by rfl) ⟨1398212, by rfl⟩ : syracuseStep 1864283 = 2796425) B2796425
theorem B34075579 : Blo 1242439 34075579 := bstep (se 1 (by rfl) ⟨25556684, by rfl⟩ : syracuseStep 34075579 = 51113369) B51113369
theorem B2798783 : Blo 1242439 2798783 := bstep (se 1 (by rfl) ⟨2099087, by rfl⟩ : syracuseStep 2798783 = 4198175) B4198175
theorem B1243359 : Blo 1242439 1243359 := bstep (se 1 (by rfl) ⟨932519, by rfl⟩ : syracuseStep 1243359 = 1865039) B1865039
theorem B6298559 : Blo 1242439 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B552008915 : Blo 1242439 552008915 := bstep (se 1 (by rfl) ⟨414006686, by rfl⟩ : syracuseStep 552008915 = 828013373) B828013373
theorem B1572959 : Blo 1242439 1572959 := bstep (se 1 (by rfl) ⟨1179719, by rfl⟩ : syracuseStep 1572959 = 2359439) B2359439
theorem B45434105 : Blo 1242439 45434105 := bstep (se 2 (by rfl) ⟨17037789, by rfl⟩ : syracuseStep 45434105 = 34075579) B34075579
theorem B4199039 : Blo 1242439 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B368005943 : Blo 1242439 368005943 := bstep (se 1 (by rfl) ⟨276004457, by rfl⟩ : syracuseStep 368005943 = 552008915) B552008915
theorem B1242575 : Blo 1242439 1242575 := bstep (se 1 (by rfl) ⟨931931, by rfl⟩ : syracuseStep 1242575 = 1863863) B1863863
theorem B2799071 : Blo 1242439 2799071 := bstep (se 1 (by rfl) ⟨2099303, by rfl⟩ : syracuseStep 2799071 = 4198607) B4198607
theorem B1865195 : Blo 1242439 1865195 := bstep (se 1 (by rfl) ⟨1398896, by rfl⟩ : syracuseStep 1865195 = 2797793) B2797793
theorem B1242855 : Blo 1242439 1242855 := bstep (se 1 (by rfl) ⟨932141, by rfl⟩ : syracuseStep 1242855 = 1864283) B1864283
theorem B1865855 : Blo 1242439 1865855 := bstep (se 1 (by rfl) ⟨1399391, by rfl⟩ : syracuseStep 1865855 = 2798783) B2798783
theorem B7969823 : Blo 1242439 7969823 := bstep (se 1 (by rfl) ⟨5977367, by rfl⟩ : syracuseStep 7969823 = 11954735) B11954735
theorem B181477259 : Blo 1242439 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B4194557 : Blo 1242439 4194557 := bstep (se 3 (by rfl) ⟨786479, by rfl⟩ : syracuseStep 4194557 = 1572959) B1572959
theorem B245337295 : Blo 1242439 245337295 := bstep (se 1 (by rfl) ⟨184002971, by rfl⟩ : syracuseStep 245337295 = 368005943) B368005943
theorem B30289403 : Blo 1242439 30289403 := bstep (se 1 (by rfl) ⟨22717052, by rfl⟩ : syracuseStep 30289403 = 45434105) B45434105
theorem B5313215 : Blo 1242439 5313215 := bstep (se 1 (by rfl) ⟨3984911, by rfl⟩ : syracuseStep 5313215 = 7969823) B7969823
theorem B120984839 : Blo 1242439 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B2799359 : Blo 1242439 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B1866047 : Blo 1242439 1866047 := bstep (se 1 (by rfl) ⟨1399535, by rfl⟩ : syracuseStep 1866047 = 2799071) B2799071
theorem B1243463 : Blo 1242439 1243463 := bstep (se 1 (by rfl) ⟨932597, by rfl⟩ : syracuseStep 1243463 = 1865195) B1865195
theorem B1243903 : Blo 1242439 1243903 := bstep (se 1 (by rfl) ⟨932927, by rfl⟩ : syracuseStep 1243903 = 1865855) B1865855
theorem B327116393 : Blo 1242439 327116393 := bstep (se 2 (by rfl) ⟨122668647, by rfl⟩ : syracuseStep 327116393 = 245337295) B245337295
theorem B2796371 : Blo 1242439 2796371 := bstep (se 1 (by rfl) ⟨2097278, by rfl⟩ : syracuseStep 2796371 = 4194557) B4194557
theorem B3542143 : Blo 1242439 3542143 := bstep (se 1 (by rfl) ⟨2656607, by rfl⟩ : syracuseStep 3542143 = 5313215) B5313215
theorem B80656559 : Blo 1242439 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B1866239 : Blo 1242439 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B1244031 : Blo 1242439 1244031 := bstep (se 1 (by rfl) ⟨933023, by rfl⟩ : syracuseStep 1244031 = 1866047) B1866047
theorem B20192935 : Blo 1242439 20192935 := bstep (se 1 (by rfl) ⟨15144701, by rfl⟩ : syracuseStep 20192935 = 30289403) B30289403
theorem B4722857 : Blo 1242439 4722857 := bstep (se 2 (by rfl) ⟨1771071, by rfl⟩ : syracuseStep 4722857 = 3542143) B3542143
theorem B1864247 : Blo 1242439 1864247 := bstep (se 1 (by rfl) ⟨1398185, by rfl⟩ : syracuseStep 1864247 = 2796371) B2796371
theorem B26923913 : Blo 1242439 26923913 := bstep (se 2 (by rfl) ⟨10096467, by rfl⟩ : syracuseStep 26923913 = 20192935) B20192935
theorem B218077595 : Blo 1242439 218077595 := bstep (se 1 (by rfl) ⟨163558196, by rfl⟩ : syracuseStep 218077595 = 327116393) B327116393
theorem B53771039 : Blo 1242439 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B1244159 : Blo 1242439 1244159 := bstep (se 1 (by rfl) ⟨933119, by rfl⟩ : syracuseStep 1244159 = 1866239) B1866239
theorem B17949275 : Blo 1242439 17949275 := bstep (se 1 (by rfl) ⟨13461956, by rfl⟩ : syracuseStep 17949275 = 26923913) B26923913
theorem B145385063 : Blo 1242439 145385063 := bstep (se 1 (by rfl) ⟨109038797, by rfl⟩ : syracuseStep 145385063 = 218077595) B218077595
theorem B3148571 : Blo 1242439 3148571 := bstep (se 1 (by rfl) ⟨2361428, by rfl⟩ : syracuseStep 3148571 = 4722857) B4722857
theorem B1242831 : Blo 1242439 1242831 := bstep (se 1 (by rfl) ⟨932123, by rfl⟩ : syracuseStep 1242831 = 1864247) B1864247
theorem B35847359 : Blo 1242439 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B2099047 : Blo 1242439 2099047 := bstep (se 1 (by rfl) ⟨1574285, by rfl⟩ : syracuseStep 2099047 = 3148571) B3148571
theorem B23898239 : Blo 1242439 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B96923375 : Blo 1242439 96923375 := bstep (se 1 (by rfl) ⟨72692531, by rfl⟩ : syracuseStep 96923375 = 145385063) B145385063
theorem B11966183 : Blo 1242439 11966183 := bstep (se 1 (by rfl) ⟨8974637, by rfl⟩ : syracuseStep 11966183 = 17949275) B17949275
theorem B2798729 : Blo 1242439 2798729 := bstep (se 2 (by rfl) ⟨1049523, by rfl⟩ : syracuseStep 2798729 = 2099047) B2099047
theorem B64615583 : Blo 1242439 64615583 := bstep (se 1 (by rfl) ⟨48461687, by rfl⟩ : syracuseStep 64615583 = 96923375) B96923375
theorem B7977455 : Blo 1242439 7977455 := bstep (se 1 (by rfl) ⟨5983091, by rfl⟩ : syracuseStep 7977455 = 11966183) B11966183
theorem B15932159 : Blo 1242439 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B5318303 : Blo 1242439 5318303 := bstep (se 1 (by rfl) ⟨3988727, by rfl⟩ : syracuseStep 5318303 = 7977455) B7977455
theorem B43077055 : Blo 1242439 43077055 := bstep (se 1 (by rfl) ⟨32307791, by rfl⟩ : syracuseStep 43077055 = 64615583) B64615583
theorem B10621439 : Blo 1242439 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B1865819 : Blo 1242439 1865819 := bstep (se 1 (by rfl) ⟨1399364, by rfl⟩ : syracuseStep 1865819 = 2798729) B2798729
theorem B14182141 : Blo 1242439 14182141 := bstep (se 3 (by rfl) ⟨2659151, by rfl⟩ : syracuseStep 14182141 = 5318303) B5318303
theorem B57436073 : Blo 1242439 57436073 := bstep (se 2 (by rfl) ⟨21538527, by rfl⟩ : syracuseStep 57436073 = 43077055) B43077055
theorem B7080959 : Blo 1242439 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B1243879 : Blo 1242439 1243879 := bstep (se 1 (by rfl) ⟨932909, by rfl⟩ : syracuseStep 1243879 = 1865819) B1865819
theorem B38290715 : Blo 1242439 38290715 := bstep (se 1 (by rfl) ⟨28718036, by rfl⟩ : syracuseStep 38290715 = 57436073) B57436073
theorem B4720639 : Blo 1242439 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B18909521 : Blo 1242439 18909521 := bstep (se 2 (by rfl) ⟨7091070, by rfl⟩ : syracuseStep 18909521 = 14182141) B14182141
theorem B25527143 : Blo 1242439 25527143 := bstep (se 1 (by rfl) ⟨19145357, by rfl⟩ : syracuseStep 25527143 = 38290715) B38290715
theorem B6294185 : Blo 1242439 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B12606347 : Blo 1242439 12606347 := bstep (se 1 (by rfl) ⟨9454760, by rfl⟩ : syracuseStep 12606347 = 18909521) B18909521
theorem B4196123 : Blo 1242439 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B17018095 : Blo 1242439 17018095 := bstep (se 1 (by rfl) ⟨12763571, by rfl⟩ : syracuseStep 17018095 = 25527143) B25527143
theorem B8404231 : Blo 1242439 8404231 := bstep (se 1 (by rfl) ⟨6303173, by rfl⟩ : syracuseStep 8404231 = 12606347) B12606347
theorem B2797415 : Blo 1242439 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B22690793 : Blo 1242439 22690793 := bstep (se 2 (by rfl) ⟨8509047, by rfl⟩ : syracuseStep 22690793 = 17018095) B17018095
theorem B11205641 : Blo 1242439 11205641 := bstep (se 2 (by rfl) ⟨4202115, by rfl⟩ : syracuseStep 11205641 = 8404231) B8404231
theorem B15127195 : Blo 1242439 15127195 := bstep (se 1 (by rfl) ⟨11345396, by rfl⟩ : syracuseStep 15127195 = 22690793) B22690793
theorem B1864943 : Blo 1242439 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B7470427 : Blo 1242439 7470427 := bstep (se 1 (by rfl) ⟨5602820, by rfl⟩ : syracuseStep 7470427 = 11205641) B11205641
theorem B20169593 : Blo 1242439 20169593 := bstep (se 2 (by rfl) ⟨7563597, by rfl⟩ : syracuseStep 20169593 = 15127195) B15127195
theorem B1243295 : Blo 1242439 1243295 := bstep (se 1 (by rfl) ⟨932471, by rfl⟩ : syracuseStep 1243295 = 1864943) B1864943
theorem B9960569 : Blo 1242439 9960569 := bstep (se 2 (by rfl) ⟨3735213, by rfl⟩ : syracuseStep 9960569 = 7470427) B7470427
theorem B13446395 : Blo 1242439 13446395 := bstep (se 1 (by rfl) ⟨10084796, by rfl⟩ : syracuseStep 13446395 = 20169593) B20169593
theorem B6640379 : Blo 1242439 6640379 := bstep (se 1 (by rfl) ⟨4980284, by rfl⟩ : syracuseStep 6640379 = 9960569) B9960569
theorem B8964263 : Blo 1242439 8964263 := bstep (se 1 (by rfl) ⟨6723197, by rfl⟩ : syracuseStep 8964263 = 13446395) B13446395
theorem B4426919 : Blo 1242439 4426919 := bstep (se 1 (by rfl) ⟨3320189, by rfl⟩ : syracuseStep 4426919 = 6640379) B6640379
theorem B2951279 : Blo 1242439 2951279 := bstep (se 1 (by rfl) ⟨2213459, by rfl⟩ : syracuseStep 2951279 = 4426919) B4426919
theorem B5976175 : Blo 1242439 5976175 := bstep (se 1 (by rfl) ⟨4482131, by rfl⟩ : syracuseStep 5976175 = 8964263) B8964263
theorem B1967519 : Blo 1242439 1967519 := bstep (se 1 (by rfl) ⟨1475639, by rfl⟩ : syracuseStep 1967519 = 2951279) B2951279
theorem B7968233 : Blo 1242439 7968233 := bstep (se 2 (by rfl) ⟨2988087, by rfl⟩ : syracuseStep 7968233 = 5976175) B5976175
theorem B1311679 : Blo 1242439 1311679 := bstep (se 1 (by rfl) ⟨983759, by rfl⟩ : syracuseStep 1311679 = 1967519) B1967519
theorem B5312155 : Blo 1242439 5312155 := bstep (se 1 (by rfl) ⟨3984116, by rfl⟩ : syracuseStep 5312155 = 7968233) B7968233
theorem B7082873 : Blo 1242439 7082873 := bstep (se 2 (by rfl) ⟨2656077, by rfl⟩ : syracuseStep 7082873 = 5312155) B5312155
theorem B6995621 : Blo 1242439 6995621 := bstep (se 4 (by rfl) ⟨655839, by rfl⟩ : syracuseStep 6995621 = 1311679) B1311679
theorem B4663747 : Blo 1242439 4663747 := bstep (se 1 (by rfl) ⟨3497810, by rfl⟩ : syracuseStep 4663747 = 6995621) B6995621
theorem B4721915 : Blo 1242439 4721915 := bstep (se 1 (by rfl) ⟨3541436, by rfl⟩ : syracuseStep 4721915 = 7082873) B7082873
theorem B3147943 : Blo 1242439 3147943 := bstep (se 1 (by rfl) ⟨2360957, by rfl⟩ : syracuseStep 3147943 = 4721915) B4721915
theorem B24873317 : Blo 1242439 24873317 := bstep (se 4 (by rfl) ⟨2331873, by rfl⟩ : syracuseStep 24873317 = 4663747) B4663747
theorem B16582211 : Blo 1242439 16582211 := bstep (se 1 (by rfl) ⟨12436658, by rfl⟩ : syracuseStep 16582211 = 24873317) B24873317
theorem B4197257 : Blo 1242439 4197257 := bstep (se 2 (by rfl) ⟨1573971, by rfl⟩ : syracuseStep 4197257 = 3147943) B3147943
theorem B11054807 : Blo 1242439 11054807 := bstep (se 1 (by rfl) ⟨8291105, by rfl⟩ : syracuseStep 11054807 = 16582211) B16582211
theorem B2798171 : Blo 1242439 2798171 := bstep (se 1 (by rfl) ⟨2098628, by rfl⟩ : syracuseStep 2798171 = 4197257) B4197257
theorem B7369871 : Blo 1242439 7369871 := bstep (se 1 (by rfl) ⟨5527403, by rfl⟩ : syracuseStep 7369871 = 11054807) B11054807
theorem B1865447 : Blo 1242439 1865447 := bstep (se 1 (by rfl) ⟨1399085, by rfl⟩ : syracuseStep 1865447 = 2798171) B2798171
theorem B78611957 : Blo 1242439 78611957 := bstep (se 5 (by rfl) ⟨3684935, by rfl⟩ : syracuseStep 78611957 = 7369871) B7369871
theorem B1243631 : Blo 1242439 1243631 := bstep (se 1 (by rfl) ⟨932723, by rfl⟩ : syracuseStep 1243631 = 1865447) B1865447
theorem B52407971 : Blo 1242439 52407971 := bstep (se 1 (by rfl) ⟨39305978, by rfl⟩ : syracuseStep 52407971 = 78611957) B78611957
theorem B34938647 : Blo 1242439 34938647 := bstep (se 1 (by rfl) ⟨26203985, by rfl⟩ : syracuseStep 34938647 = 52407971) B52407971
theorem B23292431 : Blo 1242439 23292431 := bstep (se 1 (by rfl) ⟨17469323, by rfl⟩ : syracuseStep 23292431 = 34938647) B34938647
theorem B15528287 : Blo 1242439 15528287 := bstep (se 1 (by rfl) ⟨11646215, by rfl⟩ : syracuseStep 15528287 = 23292431) B23292431
theorem B41408765 : Blo 1242439 41408765 := bstep (se 3 (by rfl) ⟨7764143, by rfl⟩ : syracuseStep 41408765 = 15528287) B15528287
theorem B27605843 : Blo 1242439 27605843 := bstep (se 1 (by rfl) ⟨20704382, by rfl⟩ : syracuseStep 27605843 = 41408765) B41408765
theorem B18403895 : Blo 1242439 18403895 := bstep (se 1 (by rfl) ⟨13802921, by rfl⟩ : syracuseStep 18403895 = 27605843) B27605843
theorem B12269263 : Blo 1242439 12269263 := bstep (se 1 (by rfl) ⟨9201947, by rfl⟩ : syracuseStep 12269263 = 18403895) B18403895
theorem B16359017 : Blo 1242439 16359017 := bstep (se 2 (by rfl) ⟨6134631, by rfl⟩ : syracuseStep 16359017 = 12269263) B12269263
theorem B43624045 : Blo 1242439 43624045 := bstep (se 3 (by rfl) ⟨8179508, by rfl⟩ : syracuseStep 43624045 = 16359017) B16359017
theorem B58165393 : Blo 1242439 58165393 := bstep (se 2 (by rfl) ⟨21812022, by rfl⟩ : syracuseStep 58165393 = 43624045) B43624045
theorem B77553857 : Blo 1242439 77553857 := bstep (se 2 (by rfl) ⟨29082696, by rfl⟩ : syracuseStep 77553857 = 58165393) B58165393
theorem B51702571 : Blo 1242439 51702571 := bstep (se 1 (by rfl) ⟨38776928, by rfl⟩ : syracuseStep 51702571 = 77553857) B77553857
theorem B68936761 : Blo 1242439 68936761 := bstep (se 2 (by rfl) ⟨25851285, by rfl⟩ : syracuseStep 68936761 = 51702571) B51702571
theorem B91915681 : Blo 1242439 91915681 := bstep (se 2 (by rfl) ⟨34468380, by rfl⟩ : syracuseStep 91915681 = 68936761) B68936761
theorem B122554241 : Blo 1242439 122554241 := bstep (se 2 (by rfl) ⟨45957840, by rfl⟩ : syracuseStep 122554241 = 91915681) B91915681
theorem B81702827 : Blo 1242439 81702827 := bstep (se 1 (by rfl) ⟨61277120, by rfl⟩ : syracuseStep 81702827 = 122554241) B122554241
theorem B54468551 : Blo 1242439 54468551 := bstep (se 1 (by rfl) ⟨40851413, by rfl⟩ : syracuseStep 54468551 = 81702827) B81702827
theorem B145249469 : Blo 1242439 145249469 := bstep (se 3 (by rfl) ⟨27234275, by rfl⟩ : syracuseStep 145249469 = 54468551) B54468551
theorem B96832979 : Blo 1242439 96832979 := bstep (se 1 (by rfl) ⟨72624734, by rfl⟩ : syracuseStep 96832979 = 145249469) B145249469
theorem B64555319 : Blo 1242439 64555319 := bstep (se 1 (by rfl) ⟨48416489, by rfl⟩ : syracuseStep 64555319 = 96832979) B96832979
theorem B172147517 : Blo 1242439 172147517 := bstep (se 3 (by rfl) ⟨32277659, by rfl⟩ : syracuseStep 172147517 = 64555319) B64555319
theorem B114765011 : Blo 1242439 114765011 := bstep (se 1 (by rfl) ⟨86073758, by rfl⟩ : syracuseStep 114765011 = 172147517) B172147517
theorem B76510007 : Blo 1242439 76510007 := bstep (se 1 (by rfl) ⟨57382505, by rfl⟩ : syracuseStep 76510007 = 114765011) B114765011
theorem B51006671 : Blo 1242439 51006671 := bstep (se 1 (by rfl) ⟨38255003, by rfl⟩ : syracuseStep 51006671 = 76510007) B76510007
theorem B34004447 : Blo 1242439 34004447 := bstep (se 1 (by rfl) ⟨25503335, by rfl⟩ : syracuseStep 34004447 = 51006671) B51006671
theorem B22669631 : Blo 1242439 22669631 := bstep (se 1 (by rfl) ⟨17002223, by rfl⟩ : syracuseStep 22669631 = 34004447) B34004447
theorem B15113087 : Blo 1242439 15113087 := bstep (se 1 (by rfl) ⟨11334815, by rfl⟩ : syracuseStep 15113087 = 22669631) B22669631
theorem B10075391 : Blo 1242439 10075391 := bstep (se 1 (by rfl) ⟨7556543, by rfl⟩ : syracuseStep 10075391 = 15113087) B15113087
theorem B6716927 : Blo 1242439 6716927 := bstep (se 1 (by rfl) ⟨5037695, by rfl⟩ : syracuseStep 6716927 = 10075391) B10075391
theorem B4477951 : Blo 1242439 4477951 := bstep (se 1 (by rfl) ⟨3358463, by rfl⟩ : syracuseStep 4477951 = 6716927) B6716927
theorem B5970601 : Blo 1242439 5970601 := bstep (se 2 (by rfl) ⟨2238975, by rfl⟩ : syracuseStep 5970601 = 4477951) B4477951
theorem B7960801 : Blo 1242439 7960801 := bstep (se 2 (by rfl) ⟨2985300, by rfl⟩ : syracuseStep 7960801 = 5970601) B5970601
theorem B10614401 : Blo 1242439 10614401 := bstep (se 2 (by rfl) ⟨3980400, by rfl⟩ : syracuseStep 10614401 = 7960801) B7960801
theorem B7076267 : Blo 1242439 7076267 := bstep (se 1 (by rfl) ⟨5307200, by rfl⟩ : syracuseStep 7076267 = 10614401) B10614401
theorem B4717511 : Blo 1242439 4717511 := bstep (se 1 (by rfl) ⟨3538133, by rfl⟩ : syracuseStep 4717511 = 7076267) B7076267
theorem B3145007 : Blo 1242439 3145007 := bstep (se 1 (by rfl) ⟨2358755, by rfl⟩ : syracuseStep 3145007 = 4717511) B4717511
theorem B2096671 : Blo 1242439 2096671 := bstep (se 1 (by rfl) ⟨1572503, by rfl⟩ : syracuseStep 2096671 = 3145007) B3145007
theorem B2795561 : Blo 1242439 2795561 := bstep (se 2 (by rfl) ⟨1048335, by rfl⟩ : syracuseStep 2795561 = 2096671) B2096671
theorem B1863707 : Blo 1242439 1863707 := bstep (se 1 (by rfl) ⟨1397780, by rfl⟩ : syracuseStep 1863707 = 2795561) B2795561
theorem B1242471 : Blo 1242439 1242471 := bstep (se 1 (by rfl) ⟨931853, by rfl⟩ : syracuseStep 1242471 = 1863707) B1863707

theorem C0 (j : ℕ) (h1 : 310609 ≤ j) (h2 : j ≤ 311109) : Blo 1242439 (4 * j + 3) := by
  interval_cases j
  · exact B1242439
  · exact B1242443
  · exact B1242447
  · exact B1242451
  · exact B1242455
  · exact B1242459
  · exact B1242463
  · exact B1242467
  · exact B1242471
  · exact B1242475
  · exact B1242479
  · exact B1242483
  · exact B1242487
  · exact B1242491
  · exact B1242495
  · exact B1242499
  · exact B1242503
  · exact B1242507
  · exact B1242511
  · exact B1242515
  · exact B1242519
  · exact B1242523
  · exact B1242527
  · exact B1242531
  · exact B1242535
  · exact B1242539
  · exact B1242543
  · exact B1242547
  · exact B1242551
  · exact B1242555
  · exact B1242559
  · exact B1242563
  · exact B1242567
  · exact B1242571
  · exact B1242575
  · exact B1242579
  · exact B1242583
  · exact B1242587
  · exact B1242591
  · exact B1242595
  · exact B1242599
  · exact B1242603
  · exact B1242607
  · exact B1242611
  · exact B1242615
  · exact B1242619
  · exact B1242623
  · exact B1242627
  · exact B1242631
  · exact B1242635
  · exact B1242639
  · exact B1242643
  · exact B1242647
  · exact B1242651
  · exact B1242655
  · exact B1242659
  · exact B1242663
  · exact B1242667
  · exact B1242671
  · exact B1242675
  · exact B1242679
  · exact B1242683
  · exact B1242687
  · exact B1242691
  · exact B1242695
  · exact B1242699
  · exact B1242703
  · exact B1242707
  · exact B1242711
  · exact B1242715
  · exact B1242719
  · exact B1242723
  · exact B1242727
  · exact B1242731
  · exact B1242735
  · exact B1242739
  · exact B1242743
  · exact B1242747
  · exact B1242751
  · exact B1242755
  · exact B1242759
  · exact B1242763
  · exact B1242767
  · exact B1242771
  · exact B1242775
  · exact B1242779
  · exact B1242783
  · exact B1242787
  · exact B1242791
  · exact B1242795
  · exact B1242799
  · exact B1242803
  · exact B1242807
  · exact B1242811
  · exact B1242815
  · exact B1242819
  · exact B1242823
  · exact B1242827
  · exact B1242831
  · exact B1242835
  · exact B1242839
  · exact B1242843
  · exact B1242847
  · exact B1242851
  · exact B1242855
  · exact B1242859
  · exact B1242863
  · exact B1242867
  · exact B1242871
  · exact B1242875
  · exact B1242879
  · exact B1242883
  · exact B1242887
  · exact B1242891
  · exact B1242895
  · exact B1242899
  · exact B1242903
  · exact B1242907
  · exact B1242911
  · exact B1242915
  · exact B1242919
  · exact B1242923
  · exact B1242927
  · exact B1242931
  · exact B1242935
  · exact B1242939
  · exact B1242943
  · exact B1242947
  · exact B1242951
  · exact B1242955
  · exact B1242959
  · exact B1242963
  · exact B1242967
  · exact B1242971
  · exact B1242975
  · exact B1242979
  · exact B1242983
  · exact B1242987
  · exact B1242991
  · exact B1242995
  · exact B1242999
  · exact B1243003
  · exact B1243007
  · exact B1243011
  · exact B1243015
  · exact B1243019
  · exact B1243023
  · exact B1243027
  · exact B1243031
  · exact B1243035
  · exact B1243039
  · exact B1243043
  · exact B1243047
  · exact B1243051
  · exact B1243055
  · exact B1243059
  · exact B1243063
  · exact B1243067
  · exact B1243071
  · exact B1243075
  · exact B1243079
  · exact B1243083
  · exact B1243087
  · exact B1243091
  · exact B1243095
  · exact B1243099
  · exact B1243103
  · exact B1243107
  · exact B1243111
  · exact B1243115
  · exact B1243119
  · exact B1243123
  · exact B1243127
  · exact B1243131
  · exact B1243135
  · exact B1243139
  · exact B1243143
  · exact B1243147
  · exact B1243151
  · exact B1243155
  · exact B1243159
  · exact B1243163
  · exact B1243167
  · exact B1243171
  · exact B1243175
  · exact B1243179
  · exact B1243183
  · exact B1243187
  · exact B1243191
  · exact B1243195
  · exact B1243199
  · exact B1243203
  · exact B1243207
  · exact B1243211
  · exact B1243215
  · exact B1243219
  · exact B1243223
  · exact B1243227
  · exact B1243231
  · exact B1243235
  · exact B1243239
  · exact B1243243
  · exact B1243247
  · exact B1243251
  · exact B1243255
  · exact B1243259
  · exact B1243263
  · exact B1243267
  · exact B1243271
  · exact B1243275
  · exact B1243279
  · exact B1243283
  · exact B1243287
  · exact B1243291
  · exact B1243295
  · exact B1243299
  · exact B1243303
  · exact B1243307
  · exact B1243311
  · exact B1243315
  · exact B1243319
  · exact B1243323
  · exact B1243327
  · exact B1243331
  · exact B1243335
  · exact B1243339
  · exact B1243343
  · exact B1243347
  · exact B1243351
  · exact B1243355
  · exact B1243359
  · exact B1243363
  · exact B1243367
  · exact B1243371
  · exact B1243375
  · exact B1243379
  · exact B1243383
  · exact B1243387
  · exact B1243391
  · exact B1243395
  · exact B1243399
  · exact B1243403
  · exact B1243407
  · exact B1243411
  · exact B1243415
  · exact B1243419
  · exact B1243423
  · exact B1243427
  · exact B1243431
  · exact B1243435
  · exact B1243439
  · exact B1243443
  · exact B1243447
  · exact B1243451
  · exact B1243455
  · exact B1243459
  · exact B1243463
  · exact B1243467
  · exact B1243471
  · exact B1243475
  · exact B1243479
  · exact B1243483
  · exact B1243487
  · exact B1243491
  · exact B1243495
  · exact B1243499
  · exact B1243503
  · exact B1243507
  · exact B1243511
  · exact B1243515
  · exact B1243519
  · exact B1243523
  · exact B1243527
  · exact B1243531
  · exact B1243535
  · exact B1243539
  · exact B1243543
  · exact B1243547
  · exact B1243551
  · exact B1243555
  · exact B1243559
  · exact B1243563
  · exact B1243567
  · exact B1243571
  · exact B1243575
  · exact B1243579
  · exact B1243583
  · exact B1243587
  · exact B1243591
  · exact B1243595
  · exact B1243599
  · exact B1243603
  · exact B1243607
  · exact B1243611
  · exact B1243615
  · exact B1243619
  · exact B1243623
  · exact B1243627
  · exact B1243631
  · exact B1243635
  · exact B1243639
  · exact B1243643
  · exact B1243647
  · exact B1243651
  · exact B1243655
  · exact B1243659
  · exact B1243663
  · exact B1243667
  · exact B1243671
  · exact B1243675
  · exact B1243679
  · exact B1243683
  · exact B1243687
  · exact B1243691
  · exact B1243695
  · exact B1243699
  · exact B1243703
  · exact B1243707
  · exact B1243711
  · exact B1243715
  · exact B1243719
  · exact B1243723
  · exact B1243727
  · exact B1243731
  · exact B1243735
  · exact B1243739
  · exact B1243743
  · exact B1243747
  · exact B1243751
  · exact B1243755
  · exact B1243759
  · exact B1243763
  · exact B1243767
  · exact B1243771
  · exact B1243775
  · exact B1243779
  · exact B1243783
  · exact B1243787
  · exact B1243791
  · exact B1243795
  · exact B1243799
  · exact B1243803
  · exact B1243807
  · exact B1243811
  · exact B1243815
  · exact B1243819
  · exact B1243823
  · exact B1243827
  · exact B1243831
  · exact B1243835
  · exact B1243839
  · exact B1243843
  · exact B1243847
  · exact B1243851
  · exact B1243855
  · exact B1243859
  · exact B1243863
  · exact B1243867
  · exact B1243871
  · exact B1243875
  · exact B1243879
  · exact B1243883
  · exact B1243887
  · exact B1243891
  · exact B1243895
  · exact B1243899
  · exact B1243903
  · exact B1243907
  · exact B1243911
  · exact B1243915
  · exact B1243919
  · exact B1243923
  · exact B1243927
  · exact B1243931
  · exact B1243935
  · exact B1243939
  · exact B1243943
  · exact B1243947
  · exact B1243951
  · exact B1243955
  · exact B1243959
  · exact B1243963
  · exact B1243967
  · exact B1243971
  · exact B1243975
  · exact B1243979
  · exact B1243983
  · exact B1243987
  · exact B1243991
  · exact B1243995
  · exact B1243999
  · exact B1244003
  · exact B1244007
  · exact B1244011
  · exact B1244015
  · exact B1244019
  · exact B1244023
  · exact B1244027
  · exact B1244031
  · exact B1244035
  · exact B1244039
  · exact B1244043
  · exact B1244047
  · exact B1244051
  · exact B1244055
  · exact B1244059
  · exact B1244063
  · exact B1244067
  · exact B1244071
  · exact B1244075
  · exact B1244079
  · exact B1244083
  · exact B1244087
  · exact B1244091
  · exact B1244095
  · exact B1244099
  · exact B1244103
  · exact B1244107
  · exact B1244111
  · exact B1244115
  · exact B1244119
  · exact B1244123
  · exact B1244127
  · exact B1244131
  · exact B1244135
  · exact B1244139
  · exact B1244143
  · exact B1244147
  · exact B1244151
  · exact B1244155
  · exact B1244159
  · exact B1244163
  · exact B1244167
  · exact B1244171
  · exact B1244175
  · exact B1244179
  · exact B1244183
  · exact B1244187
  · exact B1244191
  · exact B1244195
  · exact B1244199
  · exact B1244203
  · exact B1244207
  · exact B1244211
  · exact B1244215
  · exact B1244219
  · exact B1244223
  · exact B1244227
  · exact B1244231
  · exact B1244235
  · exact B1244239
  · exact B1244243
  · exact B1244247
  · exact B1244251
  · exact B1244255
  · exact B1244259
  · exact B1244263
  · exact B1244267
  · exact B1244271
  · exact B1244275
  · exact B1244279
  · exact B1244283
  · exact B1244287
  · exact B1244291
  · exact B1244295
  · exact B1244299
  · exact B1244303
  · exact B1244307
  · exact B1244311
  · exact B1244315
  · exact B1244319
  · exact B1244323
  · exact B1244327
  · exact B1244331
  · exact B1244335
  · exact B1244339
  · exact B1244343
  · exact B1244347
  · exact B1244351
  · exact B1244355
  · exact B1244359
  · exact B1244363
  · exact B1244367
  · exact B1244371
  · exact B1244375
  · exact B1244379
  · exact B1244383
  · exact B1244387
  · exact B1244391
  · exact B1244395
  · exact B1244399
  · exact B1244403
  · exact B1244407
  · exact B1244411
  · exact B1244415
  · exact B1244419
  · exact B1244423
  · exact B1244427
  · exact B1244431
  · exact B1244435
  · exact B1244439

theorem solution (m : ℕ) (hlo : 1242439 ≤ m) (hhi : m ≤ 1244439) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 310609 ≤ j := by omega
    have hj2 : j ≤ 311109 := by omega
    have hb : Blo 1242439 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
