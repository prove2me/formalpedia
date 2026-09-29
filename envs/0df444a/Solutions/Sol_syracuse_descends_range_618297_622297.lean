-- Prove2me | solution 1 for syracuse_descends_range_618297_622297
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:32.662585+00:00
-- url     : https://prove2.me/submissions/f3068948-8e1d-402a-827a-11873e945982

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


theorem B786449 : Blo 618297 786449 := bbase (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) (by norm_num)
theorem B3964949 : Blo 618297 3964949 := bbase (se 6 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 3964949 = 185857) (by norm_num)
theorem B884773 : Blo 618297 884773 := bbase (se 4 (by rfl) ⟨82947, by rfl⟩ : syracuseStep 884773 = 165895) (by norm_num)
theorem B786505 : Blo 618297 786505 := bbase (se 2 (by rfl) ⟨294939, by rfl⟩ : syracuseStep 786505 = 589879) (by norm_num)
theorem B1048693 : Blo 618297 1048693 := bbase (se 5 (by rfl) ⟨49157, by rfl⟩ : syracuseStep 1048693 = 98315) (by norm_num)
theorem B3145877 : Blo 618297 3145877 := bbase (se 6 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 3145877 = 147463) (by norm_num)
theorem B786601 : Blo 618297 786601 := bbase (se 2 (by rfl) ⟨294975, by rfl⟩ : syracuseStep 786601 = 589951) (by norm_num)
theorem B1048781 : Blo 618297 1048781 := bbase (se 3 (by rfl) ⟨196646, by rfl⟩ : syracuseStep 1048781 = 393293) (by norm_num)
theorem B2097413 : Blo 618297 2097413 := bbase (se 4 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 2097413 = 393265) (by norm_num)
theorem B1179917 : Blo 618297 1179917 := bbase (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) (by norm_num)
theorem B1573141 : Blo 618297 1573141 := bbase (se 6 (by rfl) ⟨36870, by rfl⟩ : syracuseStep 1573141 = 73741) (by norm_num)
theorem B1048909 : Blo 618297 1048909 := bbase (se 3 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 1048909 = 393341) (by norm_num)
theorem B2359637 : Blo 618297 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B786773 : Blo 618297 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B885109 : Blo 618297 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B1573253 : Blo 618297 1573253 := bbase (se 4 (by rfl) ⟨147492, by rfl⟩ : syracuseStep 1573253 = 294985) (by norm_num)
theorem B786829 : Blo 618297 786829 := bbase (se 3 (by rfl) ⟨147530, by rfl⟩ : syracuseStep 786829 = 295061) (by norm_num)
theorem B1048997 : Blo 618297 1048997 := bbase (se 4 (by rfl) ⟨98343, by rfl⟩ : syracuseStep 1048997 = 196687) (by norm_num)
theorem B5374421 : Blo 618297 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B1671653 : Blo 618297 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B786925 : Blo 618297 786925 := bbase (se 3 (by rfl) ⟨147548, by rfl⟩ : syracuseStep 786925 = 295097) (by norm_num)
theorem B3539477 : Blo 618297 3539477 := bbase (se 6 (by rfl) ⟨82956, by rfl⟩ : syracuseStep 3539477 = 165913) (by norm_num)
theorem B1049125 : Blo 618297 1049125 := bbase (se 4 (by rfl) ⟨98355, by rfl⟩ : syracuseStep 1049125 = 196711) (by norm_num)
theorem B1573445 : Blo 618297 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B885325 : Blo 618297 885325 := bbase (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) (by norm_num)
theorem B1114717 : Blo 618297 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B2359925 : Blo 618297 2359925 := bbase (se 5 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 2359925 = 221243) (by norm_num)
theorem B1049213 : Blo 618297 1049213 := bbase (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) (by norm_num)
theorem B787097 : Blo 618297 787097 := bbase (se 2 (by rfl) ⟨295161, by rfl⟩ : syracuseStep 787097 = 590323) (by norm_num)
theorem B1770149 : Blo 618297 1770149 := bbase (se 4 (by rfl) ⟨165951, by rfl⟩ : syracuseStep 1770149 = 331903) (by norm_num)
theorem B2097845 : Blo 618297 2097845 := bbase (se 5 (by rfl) ⟨98336, by rfl⟩ : syracuseStep 2097845 = 196673) (by norm_num)
theorem B787153 : Blo 618297 787153 := bbase (se 2 (by rfl) ⟨295182, by rfl⟩ : syracuseStep 787153 = 590365) (by norm_num)
theorem B3572437 : Blo 618297 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B1049341 : Blo 618297 1049341 := bbase (se 3 (by rfl) ⟨196751, by rfl⟩ : syracuseStep 1049341 = 393503) (by norm_num)
theorem B787249 : Blo 618297 787249 := bbase (se 2 (by rfl) ⟨295218, by rfl⟩ : syracuseStep 787249 = 590437) (by norm_num)
theorem B1049429 : Blo 618297 1049429 := bbase (se 9 (by rfl) ⟨3074, by rfl⟩ : syracuseStep 1049429 = 6149) (by norm_num)
theorem B1573789 : Blo 618297 1573789 := bbase (se 3 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 1573789 = 590171) (by norm_num)
theorem B885701 : Blo 618297 885701 := bbase (se 4 (by rfl) ⟨83034, by rfl⟩ : syracuseStep 885701 = 166069) (by norm_num)
theorem B1049557 : Blo 618297 1049557 := bbase (se 7 (by rfl) ⟨12299, by rfl⟩ : syracuseStep 1049557 = 24599) (by norm_num)
theorem B787421 : Blo 618297 787421 := bbase (se 3 (by rfl) ⟨147641, by rfl⟩ : syracuseStep 787421 = 295283) (by norm_num)
theorem B1180669 : Blo 618297 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B1573901 : Blo 618297 1573901 := bbase (se 3 (by rfl) ⟨295106, by rfl⟩ : syracuseStep 1573901 = 590213) (by norm_num)
theorem B787477 : Blo 618297 787477 := bbase (se 6 (by rfl) ⟨18456, by rfl⟩ : syracuseStep 787477 = 36913) (by norm_num)
theorem B1049645 : Blo 618297 1049645 := bbase (se 3 (by rfl) ⟨196808, by rfl⟩ : syracuseStep 1049645 = 393617) (by norm_num)
theorem B2098277 : Blo 618297 2098277 := bbase (se 4 (by rfl) ⟨196713, by rfl⟩ : syracuseStep 2098277 = 393427) (by norm_num)
theorem B787573 : Blo 618297 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B1180813 : Blo 618297 1180813 := bbase (se 3 (by rfl) ⟨221402, by rfl⟩ : syracuseStep 1180813 = 442805) (by norm_num)
theorem B1049773 : Blo 618297 1049773 := bbase (se 3 (by rfl) ⟨196832, by rfl⟩ : syracuseStep 1049773 = 393665) (by norm_num)
theorem B2655413 : Blo 618297 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B1574093 : Blo 618297 1574093 := bbase (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) (by norm_num)
theorem B1049861 : Blo 618297 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B2983189 : Blo 618297 2983189 := bbase (se 6 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 2983189 = 139837) (by norm_num)
theorem B2983205 : Blo 618297 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B1180973 : Blo 618297 1180973 := bbase (se 3 (by rfl) ⟨221432, by rfl⟩ : syracuseStep 1180973 = 442865) (by norm_num)
theorem B1115525 : Blo 618297 1115525 := bbase (se 4 (by rfl) ⟨104580, by rfl⟩ : syracuseStep 1115525 = 209161) (by norm_num)
theorem B1049989 : Blo 618297 1049989 := bbase (se 4 (by rfl) ⟨98436, by rfl⟩ : syracuseStep 1049989 = 196873) (by norm_num)
theorem B3147173 : Blo 618297 3147173 := bbase (se 4 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 3147173 = 590095) (by norm_num)
theorem B1181117 : Blo 618297 1181117 := bbase (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) (by norm_num)
theorem B1050077 : Blo 618297 1050077 := bbase (se 3 (by rfl) ⟨196889, by rfl⟩ : syracuseStep 1050077 = 393779) (by norm_num)
theorem B2098709 : Blo 618297 2098709 := bbase (se 6 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 2098709 = 98377) (by norm_num)
theorem B1574437 : Blo 618297 1574437 := bbase (se 4 (by rfl) ⟨147603, by rfl⟩ : syracuseStep 1574437 = 295207) (by norm_num)
theorem B8619605 : Blo 618297 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B1574549 : Blo 618297 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B2066197 : Blo 618297 2066197 := bbase (se 6 (by rfl) ⟨48426, by rfl⟩ : syracuseStep 2066197 = 96853) (by norm_num)
theorem B2361109 : Blo 618297 2361109 := bbase (se 6 (by rfl) ⟨55338, by rfl⟩ : syracuseStep 2361109 = 110677) (by norm_num)
theorem B1574741 : Blo 618297 1574741 := bbase (se 9 (by rfl) ⟨4613, by rfl⟩ : syracuseStep 1574741 = 9227) (by norm_num)
theorem B2099141 : Blo 618297 2099141 := bbase (se 4 (by rfl) ⟨196794, by rfl⟩ : syracuseStep 2099141 = 393589) (by norm_num)
theorem B2361413 : Blo 618297 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B1345621 : Blo 618297 1345621 := bbase (se 8 (by rfl) ⟨7884, by rfl⟩ : syracuseStep 1345621 = 15769) (by norm_num)
theorem B2721925 : Blo 618297 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B2656421 : Blo 618297 2656421 := bbase (se 4 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 2656421 = 498079) (by norm_num)
theorem B1575085 : Blo 618297 1575085 := bbase (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) (by norm_num)
theorem B1411253 : Blo 618297 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1771733 : Blo 618297 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B2099573 : Blo 618297 2099573 := bbase (se 5 (by rfl) ⟨98417, by rfl⟩ : syracuseStep 2099573 = 196835) (by norm_num)
theorem B3148469 : Blo 618297 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B2100005 : Blo 618297 2100005 := bbase (se 4 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 2100005 = 393751) (by norm_num)
theorem B1117261 : Blo 618297 1117261 := bbase (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) (by norm_num)
theorem B1117405 : Blo 618297 1117405 := bbase (se 3 (by rfl) ⟨209513, by rfl⟩ : syracuseStep 1117405 = 419027) (by norm_num)
theorem B1609205 : Blo 618297 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B2985589 : Blo 618297 2985589 := bbase (se 5 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 2985589 = 279899) (by norm_num)
theorem B11308693 : Blo 618297 11308693 := bbase (se 6 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 11308693 = 530095) (by norm_num)
theorem B3149765 : Blo 618297 3149765 := bbase (se 4 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 3149765 = 590581) (by norm_num)
theorem B1118357 : Blo 618297 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B7049429 : Blo 618297 7049429 := bbase (se 7 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 7049429 = 165221) (by norm_num)
theorem B9539797 : Blo 618297 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B1118429 : Blo 618297 1118429 := bbase (se 3 (by rfl) ⟨209705, by rfl⟩ : syracuseStep 1118429 = 419411) (by norm_num)
theorem B2232677 : Blo 618297 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B2822597 : Blo 618297 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B5968565 : Blo 618297 5968565 := bbase (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) (by norm_num)
theorem B3773141 : Blo 618297 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B660269 : Blo 618297 660269 := bbase (se 3 (by rfl) ⟨123800, by rfl⟩ : syracuseStep 660269 = 247601) (by norm_num)
theorem B955181 : Blo 618297 955181 := bbase (se 3 (by rfl) ⟨179096, by rfl⟩ : syracuseStep 955181 = 358193) (by norm_num)
theorem B627625 : Blo 618297 627625 := bbase (se 2 (by rfl) ⟨235359, by rfl⟩ : syracuseStep 627625 = 470719) (by norm_num)
theorem B660457 : Blo 618297 660457 := bbase (se 2 (by rfl) ⟨247671, by rfl⟩ : syracuseStep 660457 = 495343) (by norm_num)
theorem B1414181 : Blo 618297 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B660641 : Blo 618297 660641 := bbase (se 2 (by rfl) ⟨247740, by rfl⟩ : syracuseStep 660641 = 495481) (by norm_num)
theorem B1414637 : Blo 618297 1414637 := bbase (se 3 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 1414637 = 530489) (by norm_num)
theorem B4724405 : Blo 618297 4724405 := bbase (se 5 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 4724405 = 442913) (by norm_num)
theorem B1677125 : Blo 618297 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B661393 : Blo 618297 661393 := bbase (se 2 (by rfl) ⟨248022, by rfl⟩ : syracuseStep 661393 = 496045) (by norm_num)
theorem B7935893 : Blo 618297 7935893 := bbase (se 6 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 7935893 = 371995) (by norm_num)
theorem B661465 : Blo 618297 661465 := bbase (se 2 (by rfl) ⟨248049, by rfl⟩ : syracuseStep 661465 = 496099) (by norm_num)
theorem B661645 : Blo 618297 661645 := bbase (se 3 (by rfl) ⟨124058, by rfl⟩ : syracuseStep 661645 = 248117) (by norm_num)
theorem B5019893 : Blo 618297 5019893 := bbase (se 5 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 5019893 = 470615) (by norm_num)
theorem B662089 : Blo 618297 662089 := bbase (se 2 (by rfl) ⟨248283, by rfl⟩ : syracuseStep 662089 = 496567) (by norm_num)
theorem B1677925 : Blo 618297 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B629429 : Blo 618297 629429 := bbase (se 5 (by rfl) ⟨29504, by rfl⟩ : syracuseStep 629429 = 59009) (by norm_num)
theorem B662213 : Blo 618297 662213 := bbase (se 4 (by rfl) ⟨62082, by rfl⟩ : syracuseStep 662213 = 124165) (by norm_num)
theorem B1416005 : Blo 618297 1416005 := bbase (se 4 (by rfl) ⟨132750, by rfl⟩ : syracuseStep 1416005 = 265501) (by norm_num)
theorem B1121197 : Blo 618297 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B662465 : Blo 618297 662465 := bbase (se 2 (by rfl) ⟨248424, by rfl⟩ : syracuseStep 662465 = 496849) (by norm_num)
theorem B629741 : Blo 618297 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B629789 : Blo 618297 629789 := bbase (se 3 (by rfl) ⟨118085, by rfl⟩ : syracuseStep 629789 = 236171) (by norm_num)
theorem B859229 : Blo 618297 859229 := bbase (se 3 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 859229 = 322211) (by norm_num)
theorem B2694293 : Blo 618297 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B695605 : Blo 618297 695605 := bbase (se 5 (by rfl) ⟨32606, by rfl⟩ : syracuseStep 695605 = 65213) (by norm_num)
theorem B695641 : Blo 618297 695641 := bbase (se 2 (by rfl) ⟨260865, by rfl⟩ : syracuseStep 695641 = 521731) (by norm_num)
theorem B695677 : Blo 618297 695677 := bbase (se 3 (by rfl) ⟨130439, by rfl⟩ : syracuseStep 695677 = 260879) (by norm_num)
theorem B662909 : Blo 618297 662909 := bbase (se 3 (by rfl) ⟨124295, by rfl⟩ : syracuseStep 662909 = 248591) (by norm_num)
theorem B695713 : Blo 618297 695713 := bbase (se 2 (by rfl) ⟨260892, by rfl⟩ : syracuseStep 695713 = 521785) (by norm_num)
theorem B2989493 : Blo 618297 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B695749 : Blo 618297 695749 := bbase (se 4 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 695749 = 130453) (by norm_num)
theorem B695785 : Blo 618297 695785 := bbase (se 2 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 695785 = 521839) (by norm_num)
theorem B695821 : Blo 618297 695821 := bbase (se 3 (by rfl) ⟨130466, by rfl⟩ : syracuseStep 695821 = 260933) (by norm_num)
theorem B695857 : Blo 618297 695857 := bbase (se 2 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 695857 = 521893) (by norm_num)
theorem B630337 : Blo 618297 630337 := bbase (se 2 (by rfl) ⟨236376, by rfl⟩ : syracuseStep 630337 = 472753) (by norm_num)
theorem B695893 : Blo 618297 695893 := bbase (se 8 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 695893 = 8155) (by norm_num)
theorem B663157 : Blo 618297 663157 := bbase (se 5 (by rfl) ⟨31085, by rfl⟩ : syracuseStep 663157 = 62171) (by norm_num)
theorem B695929 : Blo 618297 695929 := bbase (se 2 (by rfl) ⟨260973, by rfl⟩ : syracuseStep 695929 = 521947) (by norm_num)
theorem B695965 : Blo 618297 695965 := bbase (se 3 (by rfl) ⟨130493, by rfl⟩ : syracuseStep 695965 = 260987) (by norm_num)
theorem B3186341 : Blo 618297 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B696001 : Blo 618297 696001 := bbase (se 2 (by rfl) ⟨261000, by rfl⟩ : syracuseStep 696001 = 522001) (by norm_num)
theorem B696037 : Blo 618297 696037 := bbase (se 4 (by rfl) ⟨65253, by rfl⟩ : syracuseStep 696037 = 130507) (by norm_num)
theorem B696073 : Blo 618297 696073 := bbase (se 2 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 696073 = 522055) (by norm_num)
theorem B696109 : Blo 618297 696109 := bbase (se 3 (by rfl) ⟨130520, by rfl⟩ : syracuseStep 696109 = 261041) (by norm_num)
theorem B991045 : Blo 618297 991045 := bbase (se 4 (by rfl) ⟨92910, by rfl⟩ : syracuseStep 991045 = 185821) (by norm_num)
theorem B696145 : Blo 618297 696145 := bbase (se 2 (by rfl) ⟨261054, by rfl⟩ : syracuseStep 696145 = 522109) (by norm_num)
theorem B696181 : Blo 618297 696181 := bbase (se 5 (by rfl) ⟨32633, by rfl⟩ : syracuseStep 696181 = 65267) (by norm_num)
theorem B696217 : Blo 618297 696217 := bbase (se 2 (by rfl) ⟨261081, by rfl⟩ : syracuseStep 696217 = 522163) (by norm_num)
theorem B630697 : Blo 618297 630697 := bbase (se 2 (by rfl) ⟨236511, by rfl⟩ : syracuseStep 630697 = 473023) (by norm_num)
theorem B696253 : Blo 618297 696253 := bbase (se 3 (by rfl) ⟨130547, by rfl⟩ : syracuseStep 696253 = 261095) (by norm_num)
theorem B696289 : Blo 618297 696289 := bbase (se 2 (by rfl) ⟨261108, by rfl⟩ : syracuseStep 696289 = 522217) (by norm_num)
theorem B696325 : Blo 618297 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B696361 : Blo 618297 696361 := bbase (se 2 (by rfl) ⟨261135, by rfl⟩ : syracuseStep 696361 = 522271) (by norm_num)
theorem B663601 : Blo 618297 663601 := bbase (se 2 (by rfl) ⟨248850, by rfl⟩ : syracuseStep 663601 = 497701) (by norm_num)
theorem B1679429 : Blo 618297 1679429 := bbase (se 4 (by rfl) ⟨157446, by rfl⟩ : syracuseStep 1679429 = 314893) (by norm_num)
theorem B696397 : Blo 618297 696397 := bbase (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) (by norm_num)
theorem B663661 : Blo 618297 663661 := bbase (se 3 (by rfl) ⟨124436, by rfl⟩ : syracuseStep 663661 = 248873) (by norm_num)
theorem B696433 : Blo 618297 696433 := bbase (se 2 (by rfl) ⟨261162, by rfl⟩ : syracuseStep 696433 = 522325) (by norm_num)
theorem B696469 : Blo 618297 696469 := bbase (se 6 (by rfl) ⟨16323, by rfl⟩ : syracuseStep 696469 = 32647) (by norm_num)
theorem B1679525 : Blo 618297 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B696505 : Blo 618297 696505 := bbase (se 2 (by rfl) ⟨261189, by rfl⟩ : syracuseStep 696505 = 522379) (by norm_num)
theorem B696541 : Blo 618297 696541 := bbase (se 3 (by rfl) ⟨130601, by rfl⟩ : syracuseStep 696541 = 261203) (by norm_num)
theorem B696577 : Blo 618297 696577 := bbase (se 2 (by rfl) ⟨261216, by rfl⟩ : syracuseStep 696577 = 522433) (by norm_num)
theorem B696613 : Blo 618297 696613 := bbase (se 4 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 696613 = 130615) (by norm_num)
theorem B1253693 : Blo 618297 1253693 := bbase (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) (by norm_num)
theorem B696649 : Blo 618297 696649 := bbase (se 2 (by rfl) ⟨261243, by rfl⟩ : syracuseStep 696649 = 522487) (by norm_num)
theorem B696685 : Blo 618297 696685 := bbase (se 3 (by rfl) ⟨130628, by rfl⟩ : syracuseStep 696685 = 261257) (by norm_num)
theorem B696721 : Blo 618297 696721 := bbase (se 2 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 696721 = 522541) (by norm_num)
theorem B663977 : Blo 618297 663977 := bbase (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) (by norm_num)
theorem B696757 : Blo 618297 696757 := bbase (se 5 (by rfl) ⟨32660, by rfl⟩ : syracuseStep 696757 = 65321) (by norm_num)
theorem B696793 : Blo 618297 696793 := bbase (se 2 (by rfl) ⟨261297, by rfl⟩ : syracuseStep 696793 = 522595) (by norm_num)
theorem B696829 : Blo 618297 696829 := bbase (se 3 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 696829 = 261311) (by norm_num)
theorem B696865 : Blo 618297 696865 := bbase (se 2 (by rfl) ⟨261324, by rfl⟩ : syracuseStep 696865 = 522649) (by norm_num)
theorem B696901 : Blo 618297 696901 := bbase (se 4 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 696901 = 130669) (by norm_num)
theorem B1679957 : Blo 618297 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B696937 : Blo 618297 696937 := bbase (se 2 (by rfl) ⟨261351, by rfl⟩ : syracuseStep 696937 = 522703) (by norm_num)
theorem B893549 : Blo 618297 893549 := bbase (se 3 (by rfl) ⟨167540, by rfl⟩ : syracuseStep 893549 = 335081) (by norm_num)
theorem B696973 : Blo 618297 696973 := bbase (se 3 (by rfl) ⟨130682, by rfl⟩ : syracuseStep 696973 = 261365) (by norm_num)
theorem B697009 : Blo 618297 697009 := bbase (se 2 (by rfl) ⟨261378, by rfl⟩ : syracuseStep 697009 = 522757) (by norm_num)
theorem B697045 : Blo 618297 697045 := bbase (se 7 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 697045 = 16337) (by norm_num)
theorem B697081 : Blo 618297 697081 := bbase (se 2 (by rfl) ⟨261405, by rfl⟩ : syracuseStep 697081 = 522811) (by norm_num)
theorem B697117 : Blo 618297 697117 := bbase (se 3 (by rfl) ⟨130709, by rfl⟩ : syracuseStep 697117 = 261419) (by norm_num)
theorem B697153 : Blo 618297 697153 := bbase (se 2 (by rfl) ⟨261432, by rfl⟩ : syracuseStep 697153 = 522865) (by norm_num)
theorem B697189 : Blo 618297 697189 := bbase (se 4 (by rfl) ⟨65361, by rfl⟩ : syracuseStep 697189 = 130723) (by norm_num)
theorem B664421 : Blo 618297 664421 := bbase (se 4 (by rfl) ⟨62289, by rfl⟩ : syracuseStep 664421 = 124579) (by norm_num)
theorem B697225 : Blo 618297 697225 := bbase (se 2 (by rfl) ⟨261459, by rfl⟩ : syracuseStep 697225 = 522919) (by norm_num)
theorem B664481 : Blo 618297 664481 := bbase (se 2 (by rfl) ⟨249180, by rfl⟩ : syracuseStep 664481 = 498361) (by norm_num)
theorem B697261 : Blo 618297 697261 := bbase (se 3 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 697261 = 261473) (by norm_num)
theorem B1254325 : Blo 618297 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B697297 : Blo 618297 697297 := bbase (se 2 (by rfl) ⟨261486, by rfl⟩ : syracuseStep 697297 = 522973) (by norm_num)
theorem B697333 : Blo 618297 697333 := bbase (se 5 (by rfl) ⟨32687, by rfl⟩ : syracuseStep 697333 = 65375) (by norm_num)
theorem B1057789 : Blo 618297 1057789 := bbase (se 3 (by rfl) ⟨198335, by rfl⟩ : syracuseStep 1057789 = 396671) (by norm_num)
theorem B5284885 : Blo 618297 5284885 := bbase (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) (by norm_num)
theorem B697369 : Blo 618297 697369 := bbase (se 2 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 697369 = 523027) (by norm_num)
theorem B697405 : Blo 618297 697405 := bbase (se 3 (by rfl) ⟨130763, by rfl⟩ : syracuseStep 697405 = 261527) (by norm_num)
theorem B697441 : Blo 618297 697441 := bbase (se 2 (by rfl) ⟨261540, by rfl⟩ : syracuseStep 697441 = 523081) (by norm_num)
theorem B697477 : Blo 618297 697477 := bbase (se 4 (by rfl) ⟨65388, by rfl⟩ : syracuseStep 697477 = 130777) (by norm_num)
theorem B4465813 : Blo 618297 4465813 := bbase (se 6 (by rfl) ⟨104667, by rfl⟩ : syracuseStep 4465813 = 209335) (by norm_num)
theorem B697513 : Blo 618297 697513 := bbase (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) (by norm_num)
theorem B992429 : Blo 618297 992429 := bbase (se 3 (by rfl) ⟨186080, by rfl⟩ : syracuseStep 992429 = 372161) (by norm_num)
theorem B697549 : Blo 618297 697549 := bbase (se 3 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 697549 = 261581) (by norm_num)
theorem B697585 : Blo 618297 697585 := bbase (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) (by norm_num)
theorem B697621 : Blo 618297 697621 := bbase (se 6 (by rfl) ⟨16350, by rfl⟩ : syracuseStep 697621 = 32701) (by norm_num)
theorem B697657 : Blo 618297 697657 := bbase (se 2 (by rfl) ⟨261621, by rfl⟩ : syracuseStep 697657 = 523243) (by norm_num)
theorem B697693 : Blo 618297 697693 := bbase (se 3 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 697693 = 261635) (by norm_num)
theorem B992621 : Blo 618297 992621 := bbase (se 3 (by rfl) ⟨186116, by rfl⟩ : syracuseStep 992621 = 372233) (by norm_num)
theorem B697729 : Blo 618297 697729 := bbase (se 2 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 697729 = 523297) (by norm_num)
theorem B697765 : Blo 618297 697765 := bbase (se 4 (by rfl) ⟨65415, by rfl⟩ : syracuseStep 697765 = 130831) (by norm_num)
theorem B697801 : Blo 618297 697801 := bbase (se 2 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 697801 = 523351) (by norm_num)
theorem B697837 : Blo 618297 697837 := bbase (se 3 (by rfl) ⟨130844, by rfl⟩ : syracuseStep 697837 = 261689) (by norm_num)
theorem B894461 : Blo 618297 894461 := bbase (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) (by norm_num)
theorem B697873 : Blo 618297 697873 := bbase (se 2 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 697873 = 523405) (by norm_num)
theorem B697909 : Blo 618297 697909 := bbase (se 5 (by rfl) ⟨32714, by rfl⟩ : syracuseStep 697909 = 65429) (by norm_num)
theorem B697945 : Blo 618297 697945 := bbase (se 2 (by rfl) ⟨261729, by rfl⟩ : syracuseStep 697945 = 523459) (by norm_num)
theorem B697981 : Blo 618297 697981 := bbase (se 3 (by rfl) ⟨130871, by rfl⟩ : syracuseStep 697981 = 261743) (by norm_num)
theorem B698017 : Blo 618297 698017 := bbase (se 2 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 698017 = 523513) (by norm_num)
theorem B698053 : Blo 618297 698053 := bbase (se 4 (by rfl) ⟨65442, by rfl⟩ : syracuseStep 698053 = 130885) (by norm_num)
theorem B927461 : Blo 618297 927461 := bbase (se 4 (by rfl) ⟨86949, by rfl⟩ : syracuseStep 927461 = 173899) (by norm_num)
theorem B698089 : Blo 618297 698089 := bbase (se 2 (by rfl) ⟨261783, by rfl⟩ : syracuseStep 698089 = 523567) (by norm_num)
theorem B927485 : Blo 618297 927485 := bbase (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) (by norm_num)
theorem B698125 : Blo 618297 698125 := bbase (se 3 (by rfl) ⟨130898, by rfl⟩ : syracuseStep 698125 = 261797) (by norm_num)
theorem B927509 : Blo 618297 927509 := bbase (se 6 (by rfl) ⟨21738, by rfl⟩ : syracuseStep 927509 = 43477) (by norm_num)
theorem B927533 : Blo 618297 927533 := bbase (se 3 (by rfl) ⟨173912, by rfl⟩ : syracuseStep 927533 = 347825) (by norm_num)
theorem B698161 : Blo 618297 698161 := bbase (se 2 (by rfl) ⟨261810, by rfl⟩ : syracuseStep 698161 = 523621) (by norm_num)
theorem B927557 : Blo 618297 927557 := bbase (se 4 (by rfl) ⟨86958, by rfl⟩ : syracuseStep 927557 = 173917) (by norm_num)
theorem B698197 : Blo 618297 698197 := bbase (se 9 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 698197 = 4091) (by norm_num)
theorem B927581 : Blo 618297 927581 := bbase (se 3 (by rfl) ⟨173921, by rfl⟩ : syracuseStep 927581 = 347843) (by norm_num)
theorem B927605 : Blo 618297 927605 := bbase (se 5 (by rfl) ⟨43481, by rfl⟩ : syracuseStep 927605 = 86963) (by norm_num)
theorem B698233 : Blo 618297 698233 := bbase (se 2 (by rfl) ⟨261837, by rfl⟩ : syracuseStep 698233 = 523675) (by norm_num)
theorem B927629 : Blo 618297 927629 := bbase (se 3 (by rfl) ⟨173930, by rfl⟩ : syracuseStep 927629 = 347861) (by norm_num)
theorem B4532117 : Blo 618297 4532117 := bbase (se 6 (by rfl) ⟨106221, by rfl⟩ : syracuseStep 4532117 = 212443) (by norm_num)
theorem B698269 : Blo 618297 698269 := bbase (se 3 (by rfl) ⟨130925, by rfl⟩ : syracuseStep 698269 = 261851) (by norm_num)
theorem B927653 : Blo 618297 927653 := bbase (se 4 (by rfl) ⟨86967, by rfl⟩ : syracuseStep 927653 = 173935) (by norm_num)
theorem B927677 : Blo 618297 927677 := bbase (se 3 (by rfl) ⟨173939, by rfl⟩ : syracuseStep 927677 = 347879) (by norm_num)
theorem B698305 : Blo 618297 698305 := bbase (se 2 (by rfl) ⟨261864, by rfl⟩ : syracuseStep 698305 = 523729) (by norm_num)
theorem B927701 : Blo 618297 927701 := bbase (se 7 (by rfl) ⟨10871, by rfl⟩ : syracuseStep 927701 = 21743) (by norm_num)
theorem B698341 : Blo 618297 698341 := bbase (se 4 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 698341 = 130939) (by norm_num)
theorem B927725 : Blo 618297 927725 := bbase (se 3 (by rfl) ⟨173948, by rfl⟩ : syracuseStep 927725 = 347897) (by norm_num)
theorem B1320941 : Blo 618297 1320941 := bbase (se 3 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 1320941 = 495353) (by norm_num)
theorem B927749 : Blo 618297 927749 := bbase (se 4 (by rfl) ⟨86976, by rfl⟩ : syracuseStep 927749 = 173953) (by norm_num)
theorem B698377 : Blo 618297 698377 := bbase (se 2 (by rfl) ⟨261891, by rfl⟩ : syracuseStep 698377 = 523783) (by norm_num)
theorem B927773 : Blo 618297 927773 := bbase (se 3 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 927773 = 347915) (by norm_num)
theorem B698413 : Blo 618297 698413 := bbase (se 3 (by rfl) ⟨130952, by rfl⟩ : syracuseStep 698413 = 261905) (by norm_num)
theorem B927797 : Blo 618297 927797 := bbase (se 5 (by rfl) ⟨43490, by rfl⟩ : syracuseStep 927797 = 86981) (by norm_num)
theorem B1255493 : Blo 618297 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B927821 : Blo 618297 927821 := bbase (se 3 (by rfl) ⟨173966, by rfl⟩ : syracuseStep 927821 = 347933) (by norm_num)
theorem B698449 : Blo 618297 698449 := bbase (se 2 (by rfl) ⟨261918, by rfl⟩ : syracuseStep 698449 = 523837) (by norm_num)
theorem B927845 : Blo 618297 927845 := bbase (se 4 (by rfl) ⟨86985, by rfl⟩ : syracuseStep 927845 = 173971) (by norm_num)
theorem B698485 : Blo 618297 698485 := bbase (se 5 (by rfl) ⟨32741, by rfl⟩ : syracuseStep 698485 = 65483) (by norm_num)
theorem B1321085 : Blo 618297 1321085 := bbase (se 3 (by rfl) ⟨247703, by rfl⟩ : syracuseStep 1321085 = 495407) (by norm_num)
theorem B927869 : Blo 618297 927869 := bbase (se 3 (by rfl) ⟨173975, by rfl⟩ : syracuseStep 927869 = 347951) (by norm_num)
theorem B927893 : Blo 618297 927893 := bbase (se 6 (by rfl) ⟨21747, by rfl⟩ : syracuseStep 927893 = 43495) (by norm_num)
theorem B698521 : Blo 618297 698521 := bbase (se 2 (by rfl) ⟨261945, by rfl⟩ : syracuseStep 698521 = 523891) (by norm_num)
theorem B927917 : Blo 618297 927917 := bbase (se 3 (by rfl) ⟨173984, by rfl⟩ : syracuseStep 927917 = 347969) (by norm_num)
theorem B698557 : Blo 618297 698557 := bbase (se 3 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 698557 = 261959) (by norm_num)
theorem B927941 : Blo 618297 927941 := bbase (se 4 (by rfl) ⟨86994, by rfl⟩ : syracuseStep 927941 = 173989) (by norm_num)
theorem B927965 : Blo 618297 927965 := bbase (se 3 (by rfl) ⟨173993, by rfl⟩ : syracuseStep 927965 = 347987) (by norm_num)
theorem B698593 : Blo 618297 698593 := bbase (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) (by norm_num)
theorem B3188965 : Blo 618297 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B927989 : Blo 618297 927989 := bbase (se 5 (by rfl) ⟨43499, by rfl⟩ : syracuseStep 927989 = 86999) (by norm_num)
theorem B698629 : Blo 618297 698629 := bbase (se 4 (by rfl) ⟨65496, by rfl⟩ : syracuseStep 698629 = 130993) (by norm_num)
theorem B928013 : Blo 618297 928013 := bbase (se 3 (by rfl) ⟨174002, by rfl⟩ : syracuseStep 928013 = 348005) (by norm_num)
theorem B928037 : Blo 618297 928037 := bbase (se 4 (by rfl) ⟨87003, by rfl⟩ : syracuseStep 928037 = 174007) (by norm_num)
theorem B698665 : Blo 618297 698665 := bbase (se 2 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 698665 = 523999) (by norm_num)
theorem B928061 : Blo 618297 928061 := bbase (se 3 (by rfl) ⟨174011, by rfl⟩ : syracuseStep 928061 = 348023) (by norm_num)
theorem B698701 : Blo 618297 698701 := bbase (se 3 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 698701 = 262013) (by norm_num)
theorem B928085 : Blo 618297 928085 := bbase (se 10 (by rfl) ⟨1359, by rfl⟩ : syracuseStep 928085 = 2719) (by norm_num)
theorem B928109 : Blo 618297 928109 := bbase (se 3 (by rfl) ⟨174020, by rfl⟩ : syracuseStep 928109 = 348041) (by norm_num)
theorem B698737 : Blo 618297 698737 := bbase (se 2 (by rfl) ⟨262026, by rfl⟩ : syracuseStep 698737 = 524053) (by norm_num)
theorem B928133 : Blo 618297 928133 := bbase (se 4 (by rfl) ⟨87012, by rfl⟩ : syracuseStep 928133 = 174025) (by norm_num)
theorem B698773 : Blo 618297 698773 := bbase (se 6 (by rfl) ⟨16377, by rfl⟩ : syracuseStep 698773 = 32755) (by norm_num)
theorem B928157 : Blo 618297 928157 := bbase (se 3 (by rfl) ⟨174029, by rfl⟩ : syracuseStep 928157 = 348059) (by norm_num)
theorem B928181 : Blo 618297 928181 := bbase (se 5 (by rfl) ⟨43508, by rfl⟩ : syracuseStep 928181 = 87017) (by norm_num)
theorem B698809 : Blo 618297 698809 := bbase (se 2 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 698809 = 524107) (by norm_num)
theorem B928205 : Blo 618297 928205 := bbase (se 3 (by rfl) ⟨174038, by rfl⟩ : syracuseStep 928205 = 348077) (by norm_num)
theorem B698845 : Blo 618297 698845 := bbase (se 3 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 698845 = 262067) (by norm_num)
theorem B928229 : Blo 618297 928229 := bbase (se 4 (by rfl) ⟨87021, by rfl⟩ : syracuseStep 928229 = 174043) (by norm_num)
theorem B928253 : Blo 618297 928253 := bbase (se 3 (by rfl) ⟨174047, by rfl⟩ : syracuseStep 928253 = 348095) (by norm_num)
theorem B698881 : Blo 618297 698881 := bbase (se 2 (by rfl) ⟨262080, by rfl⟩ : syracuseStep 698881 = 524161) (by norm_num)
theorem B1190413 : Blo 618297 1190413 := bbase (se 3 (by rfl) ⟨223202, by rfl⟩ : syracuseStep 1190413 = 446405) (by norm_num)
theorem B928277 : Blo 618297 928277 := bbase (se 6 (by rfl) ⟨21756, by rfl⟩ : syracuseStep 928277 = 43513) (by norm_num)
theorem B698917 : Blo 618297 698917 := bbase (se 4 (by rfl) ⟨65523, by rfl⟩ : syracuseStep 698917 = 131047) (by norm_num)
theorem B928301 : Blo 618297 928301 := bbase (se 3 (by rfl) ⟨174056, by rfl⟩ : syracuseStep 928301 = 348113) (by norm_num)
theorem B928325 : Blo 618297 928325 := bbase (se 4 (by rfl) ⟨87030, by rfl⟩ : syracuseStep 928325 = 174061) (by norm_num)
theorem B698953 : Blo 618297 698953 := bbase (se 2 (by rfl) ⟨262107, by rfl⟩ : syracuseStep 698953 = 524215) (by norm_num)
theorem B928349 : Blo 618297 928349 := bbase (se 3 (by rfl) ⟨174065, by rfl⟩ : syracuseStep 928349 = 348131) (by norm_num)
theorem B764525 : Blo 618297 764525 := bbase (se 3 (by rfl) ⟨143348, by rfl⟩ : syracuseStep 764525 = 286697) (by norm_num)
theorem B698989 : Blo 618297 698989 := bbase (se 3 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 698989 = 262121) (by norm_num)
theorem B928373 : Blo 618297 928373 := bbase (se 5 (by rfl) ⟨43517, by rfl⟩ : syracuseStep 928373 = 87035) (by norm_num)
theorem B928397 : Blo 618297 928397 := bbase (se 3 (by rfl) ⟨174074, by rfl⟩ : syracuseStep 928397 = 348149) (by norm_num)
theorem B699025 : Blo 618297 699025 := bbase (se 2 (by rfl) ⟨262134, by rfl⟩ : syracuseStep 699025 = 524269) (by norm_num)
theorem B993941 : Blo 618297 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B1059485 : Blo 618297 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B928421 : Blo 618297 928421 := bbase (se 4 (by rfl) ⟨87039, by rfl⟩ : syracuseStep 928421 = 174079) (by norm_num)
theorem B699061 : Blo 618297 699061 := bbase (se 5 (by rfl) ⟨32768, by rfl⟩ : syracuseStep 699061 = 65537) (by norm_num)
theorem B928445 : Blo 618297 928445 := bbase (se 3 (by rfl) ⟨174083, by rfl⟩ : syracuseStep 928445 = 348167) (by norm_num)
theorem B928469 : Blo 618297 928469 := bbase (se 7 (by rfl) ⟨10880, by rfl⟩ : syracuseStep 928469 = 21761) (by norm_num)
theorem B699097 : Blo 618297 699097 := bbase (se 2 (by rfl) ⟨262161, by rfl⟩ : syracuseStep 699097 = 524323) (by norm_num)
theorem B928493 : Blo 618297 928493 := bbase (se 3 (by rfl) ⟨174092, by rfl⟩ : syracuseStep 928493 = 348185) (by norm_num)
theorem B994037 : Blo 618297 994037 := bbase (se 5 (by rfl) ⟨46595, by rfl⟩ : syracuseStep 994037 = 93191) (by norm_num)
theorem B699133 : Blo 618297 699133 := bbase (se 3 (by rfl) ⟨131087, by rfl⟩ : syracuseStep 699133 = 262175) (by norm_num)
theorem B928517 : Blo 618297 928517 := bbase (se 4 (by rfl) ⟨87048, by rfl⟩ : syracuseStep 928517 = 174097) (by norm_num)
theorem B994069 : Blo 618297 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B928541 : Blo 618297 928541 := bbase (se 3 (by rfl) ⟨174101, by rfl⟩ : syracuseStep 928541 = 348203) (by norm_num)
theorem B699169 : Blo 618297 699169 := bbase (se 2 (by rfl) ⟨262188, by rfl⟩ : syracuseStep 699169 = 524377) (by norm_num)
theorem B895789 : Blo 618297 895789 := bbase (se 3 (by rfl) ⟨167960, by rfl⟩ : syracuseStep 895789 = 335921) (by norm_num)
theorem B928565 : Blo 618297 928565 := bbase (se 5 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 928565 = 87053) (by norm_num)
theorem B699205 : Blo 618297 699205 := bbase (se 4 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 699205 = 131101) (by norm_num)
theorem B928589 : Blo 618297 928589 := bbase (se 3 (by rfl) ⟨174110, by rfl⟩ : syracuseStep 928589 = 348221) (by norm_num)
theorem B1321829 : Blo 618297 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B928613 : Blo 618297 928613 := bbase (se 4 (by rfl) ⟨87057, by rfl⟩ : syracuseStep 928613 = 174115) (by norm_num)
theorem B699241 : Blo 618297 699241 := bbase (se 2 (by rfl) ⟨262215, by rfl⟩ : syracuseStep 699241 = 524431) (by norm_num)
theorem B928637 : Blo 618297 928637 := bbase (se 3 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 928637 = 348239) (by norm_num)
theorem B699277 : Blo 618297 699277 := bbase (se 3 (by rfl) ⟨131114, by rfl⟩ : syracuseStep 699277 = 262229) (by norm_num)
theorem B928661 : Blo 618297 928661 := bbase (se 6 (by rfl) ⟨21765, by rfl⟩ : syracuseStep 928661 = 43531) (by norm_num)
theorem B928685 : Blo 618297 928685 := bbase (se 3 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 928685 = 348257) (by norm_num)
theorem B699313 : Blo 618297 699313 := bbase (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) (by norm_num)
theorem B928709 : Blo 618297 928709 := bbase (se 4 (by rfl) ⟨87066, by rfl⟩ : syracuseStep 928709 = 174133) (by norm_num)
theorem B5286869 : Blo 618297 5286869 := bbase (se 7 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 5286869 = 123911) (by norm_num)
theorem B699349 : Blo 618297 699349 := bbase (se 7 (by rfl) ⟨8195, by rfl⟩ : syracuseStep 699349 = 16391) (by norm_num)
theorem B928733 : Blo 618297 928733 := bbase (se 3 (by rfl) ⟨174137, by rfl⟩ : syracuseStep 928733 = 348275) (by norm_num)
theorem B928757 : Blo 618297 928757 := bbase (se 5 (by rfl) ⟨43535, by rfl⟩ : syracuseStep 928757 = 87071) (by norm_num)
theorem B699385 : Blo 618297 699385 := bbase (se 2 (by rfl) ⟨262269, by rfl⟩ : syracuseStep 699385 = 524539) (by norm_num)
theorem B928781 : Blo 618297 928781 := bbase (se 3 (by rfl) ⟨174146, by rfl⟩ : syracuseStep 928781 = 348293) (by norm_num)
theorem B699421 : Blo 618297 699421 := bbase (se 3 (by rfl) ⟨131141, by rfl⟩ : syracuseStep 699421 = 262283) (by norm_num)
theorem B928805 : Blo 618297 928805 := bbase (se 4 (by rfl) ⟨87075, by rfl⟩ : syracuseStep 928805 = 174151) (by norm_num)
theorem B928829 : Blo 618297 928829 := bbase (se 3 (by rfl) ⟨174155, by rfl⟩ : syracuseStep 928829 = 348311) (by norm_num)
theorem B699457 : Blo 618297 699457 := bbase (se 2 (by rfl) ⟨262296, by rfl⟩ : syracuseStep 699457 = 524593) (by norm_num)
theorem B928853 : Blo 618297 928853 := bbase (se 8 (by rfl) ⟨5442, by rfl⟩ : syracuseStep 928853 = 10885) (by norm_num)
theorem B699493 : Blo 618297 699493 := bbase (se 4 (by rfl) ⟨65577, by rfl⟩ : syracuseStep 699493 = 131155) (by norm_num)
theorem B928877 : Blo 618297 928877 := bbase (se 3 (by rfl) ⟨174164, by rfl⟩ : syracuseStep 928877 = 348329) (by norm_num)
theorem B928901 : Blo 618297 928901 := bbase (se 4 (by rfl) ⟨87084, by rfl⟩ : syracuseStep 928901 = 174169) (by norm_num)
theorem B699529 : Blo 618297 699529 := bbase (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) (by norm_num)
theorem B928925 : Blo 618297 928925 := bbase (se 3 (by rfl) ⟨174173, by rfl⟩ : syracuseStep 928925 = 348347) (by norm_num)
theorem B699565 : Blo 618297 699565 := bbase (se 3 (by rfl) ⟨131168, by rfl⟩ : syracuseStep 699565 = 262337) (by norm_num)
theorem B928949 : Blo 618297 928949 := bbase (se 5 (by rfl) ⟨43544, by rfl⟩ : syracuseStep 928949 = 87089) (by norm_num)
theorem B2829509 : Blo 618297 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B928973 : Blo 618297 928973 := bbase (se 3 (by rfl) ⟨174182, by rfl⟩ : syracuseStep 928973 = 348365) (by norm_num)
theorem B699601 : Blo 618297 699601 := bbase (se 2 (by rfl) ⟨262350, by rfl⟩ : syracuseStep 699601 = 524701) (by norm_num)
theorem B928997 : Blo 618297 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B699637 : Blo 618297 699637 := bbase (se 5 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 699637 = 65591) (by norm_num)
theorem B929021 : Blo 618297 929021 := bbase (se 3 (by rfl) ⟨174191, by rfl⟩ : syracuseStep 929021 = 348383) (by norm_num)
theorem B929045 : Blo 618297 929045 := bbase (se 6 (by rfl) ⟨21774, by rfl⟩ : syracuseStep 929045 = 43549) (by norm_num)
theorem B699673 : Blo 618297 699673 := bbase (se 2 (by rfl) ⟨262377, by rfl⟩ : syracuseStep 699673 = 524755) (by norm_num)
theorem B929069 : Blo 618297 929069 := bbase (se 3 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 929069 = 348401) (by norm_num)
theorem B699709 : Blo 618297 699709 := bbase (se 3 (by rfl) ⟨131195, by rfl⟩ : syracuseStep 699709 = 262391) (by norm_num)
theorem B929093 : Blo 618297 929093 := bbase (se 4 (by rfl) ⟨87102, by rfl⟩ : syracuseStep 929093 = 174205) (by norm_num)
theorem B929117 : Blo 618297 929117 := bbase (se 3 (by rfl) ⟨174209, by rfl⟩ : syracuseStep 929117 = 348419) (by norm_num)
theorem B699745 : Blo 618297 699745 := bbase (se 2 (by rfl) ⟨262404, by rfl⟩ : syracuseStep 699745 = 524809) (by norm_num)
theorem B929141 : Blo 618297 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B699781 : Blo 618297 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B929165 : Blo 618297 929165 := bbase (se 3 (by rfl) ⟨174218, by rfl⟩ : syracuseStep 929165 = 348437) (by norm_num)
theorem B929189 : Blo 618297 929189 := bbase (se 4 (by rfl) ⟨87111, by rfl⟩ : syracuseStep 929189 = 174223) (by norm_num)
theorem B699817 : Blo 618297 699817 := bbase (se 2 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 699817 = 524863) (by norm_num)
theorem B929213 : Blo 618297 929213 := bbase (se 3 (by rfl) ⟨174227, by rfl⟩ : syracuseStep 929213 = 348455) (by norm_num)
theorem B699853 : Blo 618297 699853 := bbase (se 3 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 699853 = 262445) (by norm_num)
theorem B929237 : Blo 618297 929237 := bbase (se 7 (by rfl) ⟨10889, by rfl⟩ : syracuseStep 929237 = 21779) (by norm_num)
theorem B929261 : Blo 618297 929261 := bbase (se 3 (by rfl) ⟨174236, by rfl⟩ : syracuseStep 929261 = 348473) (by norm_num)
theorem B699889 : Blo 618297 699889 := bbase (se 2 (by rfl) ⟨262458, by rfl⟩ : syracuseStep 699889 = 524917) (by norm_num)
theorem B929285 : Blo 618297 929285 := bbase (se 4 (by rfl) ⟨87120, by rfl⟩ : syracuseStep 929285 = 174241) (by norm_num)
theorem B699925 : Blo 618297 699925 := bbase (se 6 (by rfl) ⟨16404, by rfl⟩ : syracuseStep 699925 = 32809) (by norm_num)
theorem B929309 : Blo 618297 929309 := bbase (se 3 (by rfl) ⟨174245, by rfl⟩ : syracuseStep 929309 = 348491) (by norm_num)
theorem B929333 : Blo 618297 929333 := bbase (se 5 (by rfl) ⟨43562, by rfl⟩ : syracuseStep 929333 = 87125) (by norm_num)
theorem B699961 : Blo 618297 699961 := bbase (se 2 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 699961 = 524971) (by norm_num)
theorem B2862661 : Blo 618297 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B929357 : Blo 618297 929357 := bbase (se 3 (by rfl) ⟨174254, by rfl⟩ : syracuseStep 929357 = 348509) (by norm_num)
theorem B1322581 : Blo 618297 1322581 := bbase (se 8 (by rfl) ⟨7749, by rfl⟩ : syracuseStep 1322581 = 15499) (by norm_num)
theorem B699997 : Blo 618297 699997 := bbase (se 3 (by rfl) ⟨131249, by rfl⟩ : syracuseStep 699997 = 262499) (by norm_num)
theorem B929381 : Blo 618297 929381 := bbase (se 4 (by rfl) ⟨87129, by rfl⟩ : syracuseStep 929381 = 174259) (by norm_num)
theorem B1617509 : Blo 618297 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B929405 : Blo 618297 929405 := bbase (se 3 (by rfl) ⟨174263, by rfl⟩ : syracuseStep 929405 = 348527) (by norm_num)
theorem B700033 : Blo 618297 700033 := bbase (se 2 (by rfl) ⟨262512, by rfl⟩ : syracuseStep 700033 = 525025) (by norm_num)
theorem B929429 : Blo 618297 929429 := bbase (se 6 (by rfl) ⟨21783, by rfl⟩ : syracuseStep 929429 = 43567) (by norm_num)
theorem B700069 : Blo 618297 700069 := bbase (se 4 (by rfl) ⟨65631, by rfl⟩ : syracuseStep 700069 = 131263) (by norm_num)
theorem B929453 : Blo 618297 929453 := bbase (se 3 (by rfl) ⟨174272, by rfl⟩ : syracuseStep 929453 = 348545) (by norm_num)
theorem B929477 : Blo 618297 929477 := bbase (se 4 (by rfl) ⟨87138, by rfl⟩ : syracuseStep 929477 = 174277) (by norm_num)
theorem B1191629 : Blo 618297 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B929501 : Blo 618297 929501 := bbase (se 3 (by rfl) ⟨174281, by rfl⟩ : syracuseStep 929501 = 348563) (by norm_num)
theorem B1322725 : Blo 618297 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B929525 : Blo 618297 929525 := bbase (se 5 (by rfl) ⟨43571, by rfl⟩ : syracuseStep 929525 = 87143) (by norm_num)
theorem B929549 : Blo 618297 929549 := bbase (se 3 (by rfl) ⟨174290, by rfl⟩ : syracuseStep 929549 = 348581) (by norm_num)
theorem B2010901 : Blo 618297 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B929573 : Blo 618297 929573 := bbase (se 4 (by rfl) ⟨87147, by rfl⟩ : syracuseStep 929573 = 174295) (by norm_num)
theorem B929597 : Blo 618297 929597 := bbase (se 3 (by rfl) ⟨174299, by rfl⟩ : syracuseStep 929597 = 348599) (by norm_num)
theorem B929621 : Blo 618297 929621 := bbase (se 9 (by rfl) ⟨2723, by rfl⟩ : syracuseStep 929621 = 5447) (by norm_num)
theorem B3977045 : Blo 618297 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B929645 : Blo 618297 929645 := bbase (se 3 (by rfl) ⟨174308, by rfl⟩ : syracuseStep 929645 = 348617) (by norm_num)
theorem B929669 : Blo 618297 929669 := bbase (se 4 (by rfl) ⟨87156, by rfl⟩ : syracuseStep 929669 = 174313) (by norm_num)
theorem B2240405 : Blo 618297 2240405 := bbase (se 6 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 2240405 = 105019) (by norm_num)
theorem B929693 : Blo 618297 929693 := bbase (se 3 (by rfl) ⟨174317, by rfl⟩ : syracuseStep 929693 = 348635) (by norm_num)
theorem B1257373 : Blo 618297 1257373 := bbase (se 3 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 1257373 = 471515) (by norm_num)
theorem B929717 : Blo 618297 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B929741 : Blo 618297 929741 := bbase (se 3 (by rfl) ⟨174326, by rfl⟩ : syracuseStep 929741 = 348653) (by norm_num)
theorem B929765 : Blo 618297 929765 := bbase (se 4 (by rfl) ⟨87165, by rfl⟩ : syracuseStep 929765 = 174331) (by norm_num)
theorem B929789 : Blo 618297 929789 := bbase (se 3 (by rfl) ⟨174335, by rfl⟩ : syracuseStep 929789 = 348671) (by norm_num)
theorem B929813 : Blo 618297 929813 := bbase (se 6 (by rfl) ⟨21792, by rfl⟩ : syracuseStep 929813 = 43585) (by norm_num)
theorem B929837 : Blo 618297 929837 := bbase (se 3 (by rfl) ⟨174344, by rfl⟩ : syracuseStep 929837 = 348689) (by norm_num)
theorem B929861 : Blo 618297 929861 := bbase (se 4 (by rfl) ⟨87174, by rfl⟩ : syracuseStep 929861 = 174349) (by norm_num)
theorem B1323101 : Blo 618297 1323101 := bbase (se 3 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 1323101 = 496163) (by norm_num)
theorem B929885 : Blo 618297 929885 := bbase (se 3 (by rfl) ⟨174353, by rfl⟩ : syracuseStep 929885 = 348707) (by norm_num)
theorem B929909 : Blo 618297 929909 := bbase (se 5 (by rfl) ⟨43589, by rfl⟩ : syracuseStep 929909 = 87179) (by norm_num)
theorem B929933 : Blo 618297 929933 := bbase (se 3 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 929933 = 348725) (by norm_num)
theorem B929957 : Blo 618297 929957 := bbase (se 4 (by rfl) ⟨87183, by rfl⟩ : syracuseStep 929957 = 174367) (by norm_num)
theorem B929981 : Blo 618297 929981 := bbase (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) (by norm_num)
theorem B930005 : Blo 618297 930005 := bbase (se 7 (by rfl) ⟨10898, by rfl⟩ : syracuseStep 930005 = 21797) (by norm_num)
theorem B930029 : Blo 618297 930029 := bbase (se 3 (by rfl) ⟨174380, by rfl⟩ : syracuseStep 930029 = 348761) (by norm_num)
theorem B995581 : Blo 618297 995581 := bbase (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) (by norm_num)
theorem B930053 : Blo 618297 930053 := bbase (se 4 (by rfl) ⟨87192, by rfl⟩ : syracuseStep 930053 = 174385) (by norm_num)
theorem B930077 : Blo 618297 930077 := bbase (se 3 (by rfl) ⟨174389, by rfl⟩ : syracuseStep 930077 = 348779) (by norm_num)
theorem B930101 : Blo 618297 930101 := bbase (se 5 (by rfl) ⟨43598, by rfl⟩ : syracuseStep 930101 = 87197) (by norm_num)
theorem B930125 : Blo 618297 930125 := bbase (se 3 (by rfl) ⟨174398, by rfl⟩ : syracuseStep 930125 = 348797) (by norm_num)
theorem B930149 : Blo 618297 930149 := bbase (se 4 (by rfl) ⟨87201, by rfl⟩ : syracuseStep 930149 = 174403) (by norm_num)
theorem B930173 : Blo 618297 930173 := bbase (se 3 (by rfl) ⟨174407, by rfl⟩ : syracuseStep 930173 = 348815) (by norm_num)
theorem B930197 : Blo 618297 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B930221 : Blo 618297 930221 := bbase (se 3 (by rfl) ⟨174416, by rfl⟩ : syracuseStep 930221 = 348833) (by norm_num)
theorem B930245 : Blo 618297 930245 := bbase (se 4 (by rfl) ⟨87210, by rfl⟩ : syracuseStep 930245 = 174421) (by norm_num)
theorem B1323469 : Blo 618297 1323469 := bbase (se 3 (by rfl) ⟨248150, by rfl⟩ : syracuseStep 1323469 = 496301) (by norm_num)
theorem B930269 : Blo 618297 930269 := bbase (se 3 (by rfl) ⟨174425, by rfl⟩ : syracuseStep 930269 = 348851) (by norm_num)
theorem B930293 : Blo 618297 930293 := bbase (se 5 (by rfl) ⟨43607, by rfl⟩ : syracuseStep 930293 = 87215) (by norm_num)
theorem B930317 : Blo 618297 930317 := bbase (se 3 (by rfl) ⟨174434, by rfl⟩ : syracuseStep 930317 = 348869) (by norm_num)
theorem B930341 : Blo 618297 930341 := bbase (se 4 (by rfl) ⟨87219, by rfl⟩ : syracuseStep 930341 = 174439) (by norm_num)
theorem B1487413 : Blo 618297 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B930365 : Blo 618297 930365 := bbase (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) (by norm_num)
theorem B930389 : Blo 618297 930389 := bbase (se 8 (by rfl) ⟨5451, by rfl⟩ : syracuseStep 930389 = 10903) (by norm_num)
theorem B930413 : Blo 618297 930413 := bbase (se 3 (by rfl) ⟨174452, by rfl⟩ : syracuseStep 930413 = 348905) (by norm_num)
theorem B930437 : Blo 618297 930437 := bbase (se 4 (by rfl) ⟨87228, by rfl⟩ : syracuseStep 930437 = 174457) (by norm_num)
theorem B930461 : Blo 618297 930461 := bbase (se 3 (by rfl) ⟨174461, by rfl⟩ : syracuseStep 930461 = 348923) (by norm_num)
theorem B930485 : Blo 618297 930485 := bbase (se 5 (by rfl) ⟨43616, by rfl⟩ : syracuseStep 930485 = 87233) (by norm_num)
theorem B930509 : Blo 618297 930509 := bbase (se 3 (by rfl) ⟨174470, by rfl⟩ : syracuseStep 930509 = 348941) (by norm_num)
theorem B930533 : Blo 618297 930533 := bbase (se 4 (by rfl) ⟨87237, by rfl⟩ : syracuseStep 930533 = 174475) (by norm_num)
theorem B930557 : Blo 618297 930557 := bbase (se 3 (by rfl) ⟨174479, by rfl⟩ : syracuseStep 930557 = 348959) (by norm_num)
theorem B930581 : Blo 618297 930581 := bbase (se 6 (by rfl) ⟨21810, by rfl⟩ : syracuseStep 930581 = 43621) (by norm_num)
theorem B930605 : Blo 618297 930605 := bbase (se 3 (by rfl) ⟨174488, by rfl⟩ : syracuseStep 930605 = 348977) (by norm_num)
theorem B930629 : Blo 618297 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B8926037 : Blo 618297 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B930653 : Blo 618297 930653 := bbase (se 3 (by rfl) ⟨174497, by rfl⟩ : syracuseStep 930653 = 348995) (by norm_num)
theorem B930677 : Blo 618297 930677 := bbase (se 5 (by rfl) ⟨43625, by rfl⟩ : syracuseStep 930677 = 87251) (by norm_num)
theorem B930701 : Blo 618297 930701 := bbase (se 3 (by rfl) ⟨174506, by rfl⟩ : syracuseStep 930701 = 349013) (by norm_num)
theorem B930725 : Blo 618297 930725 := bbase (se 4 (by rfl) ⟨87255, by rfl⟩ : syracuseStep 930725 = 174511) (by norm_num)
theorem B930749 : Blo 618297 930749 := bbase (se 3 (by rfl) ⟨174515, by rfl⟩ : syracuseStep 930749 = 349031) (by norm_num)
theorem B996293 : Blo 618297 996293 := bbase (se 4 (by rfl) ⟨93402, by rfl⟩ : syracuseStep 996293 = 186805) (by norm_num)
theorem B930773 : Blo 618297 930773 := bbase (se 7 (by rfl) ⟨10907, by rfl⟩ : syracuseStep 930773 = 21815) (by norm_num)
theorem B930797 : Blo 618297 930797 := bbase (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) (by norm_num)
theorem B930821 : Blo 618297 930821 := bbase (se 4 (by rfl) ⟨87264, by rfl⟩ : syracuseStep 930821 = 174529) (by norm_num)
theorem B2241557 : Blo 618297 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B930845 : Blo 618297 930845 := bbase (se 3 (by rfl) ⟨174533, by rfl⟩ : syracuseStep 930845 = 349067) (by norm_num)
theorem B930869 : Blo 618297 930869 := bbase (se 5 (by rfl) ⟨43634, by rfl⟩ : syracuseStep 930869 = 87269) (by norm_num)
theorem B930893 : Blo 618297 930893 := bbase (se 3 (by rfl) ⟨174542, by rfl⟩ : syracuseStep 930893 = 349085) (by norm_num)
theorem B930917 : Blo 618297 930917 := bbase (se 4 (by rfl) ⟨87273, by rfl⟩ : syracuseStep 930917 = 174547) (by norm_num)
theorem B930941 : Blo 618297 930941 := bbase (se 3 (by rfl) ⟨174551, by rfl⟩ : syracuseStep 930941 = 349103) (by norm_num)
theorem B930965 : Blo 618297 930965 := bbase (se 6 (by rfl) ⟨21819, by rfl⟩ : syracuseStep 930965 = 43639) (by norm_num)
theorem B930989 : Blo 618297 930989 := bbase (se 3 (by rfl) ⟨174560, by rfl⟩ : syracuseStep 930989 = 349121) (by norm_num)
theorem B931013 : Blo 618297 931013 := bbase (se 4 (by rfl) ⟨87282, by rfl⟩ : syracuseStep 931013 = 174565) (by norm_num)
theorem B2831573 : Blo 618297 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B931037 : Blo 618297 931037 := bbase (se 3 (by rfl) ⟨174569, by rfl⟩ : syracuseStep 931037 = 349139) (by norm_num)
theorem B931061 : Blo 618297 931061 := bbase (se 5 (by rfl) ⟨43643, by rfl⟩ : syracuseStep 931061 = 87287) (by norm_num)
theorem B931085 : Blo 618297 931085 := bbase (se 3 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 931085 = 349157) (by norm_num)
theorem B931109 : Blo 618297 931109 := bbase (se 4 (by rfl) ⟨87291, by rfl⟩ : syracuseStep 931109 = 174583) (by norm_num)
theorem B931133 : Blo 618297 931133 := bbase (se 3 (by rfl) ⟨174587, by rfl⟩ : syracuseStep 931133 = 349175) (by norm_num)
theorem B931157 : Blo 618297 931157 := bbase (se 13 (by rfl) ⟨170, by rfl⟩ : syracuseStep 931157 = 341) (by norm_num)
theorem B931181 : Blo 618297 931181 := bbase (se 3 (by rfl) ⟨174596, by rfl⟩ : syracuseStep 931181 = 349193) (by norm_num)
theorem B931205 : Blo 618297 931205 := bbase (se 4 (by rfl) ⟨87300, by rfl⟩ : syracuseStep 931205 = 174601) (by norm_num)
theorem B931229 : Blo 618297 931229 := bbase (se 3 (by rfl) ⟨174605, by rfl⟩ : syracuseStep 931229 = 349211) (by norm_num)
theorem B931253 : Blo 618297 931253 := bbase (se 5 (by rfl) ⟨43652, by rfl⟩ : syracuseStep 931253 = 87305) (by norm_num)
theorem B931277 : Blo 618297 931277 := bbase (se 3 (by rfl) ⟨174614, by rfl⟩ : syracuseStep 931277 = 349229) (by norm_num)
theorem B931301 : Blo 618297 931301 := bbase (se 4 (by rfl) ⟨87309, by rfl⟩ : syracuseStep 931301 = 174619) (by norm_num)
theorem B931325 : Blo 618297 931325 := bbase (se 3 (by rfl) ⟨174623, by rfl⟩ : syracuseStep 931325 = 349247) (by norm_num)
theorem B931349 : Blo 618297 931349 := bbase (se 6 (by rfl) ⟨21828, by rfl⟩ : syracuseStep 931349 = 43657) (by norm_num)
theorem B931373 : Blo 618297 931373 := bbase (se 3 (by rfl) ⟨174632, by rfl⟩ : syracuseStep 931373 = 349265) (by norm_num)
theorem B931397 : Blo 618297 931397 := bbase (se 4 (by rfl) ⟨87318, by rfl⟩ : syracuseStep 931397 = 174637) (by norm_num)
theorem B931421 : Blo 618297 931421 := bbase (se 3 (by rfl) ⟨174641, by rfl⟩ : syracuseStep 931421 = 349283) (by norm_num)
theorem B931445 : Blo 618297 931445 := bbase (se 5 (by rfl) ⟨43661, by rfl⟩ : syracuseStep 931445 = 87323) (by norm_num)
theorem B931469 : Blo 618297 931469 := bbase (se 3 (by rfl) ⟨174650, by rfl⟩ : syracuseStep 931469 = 349301) (by norm_num)
theorem B931493 : Blo 618297 931493 := bbase (se 4 (by rfl) ⟨87327, by rfl⟩ : syracuseStep 931493 = 174655) (by norm_num)
theorem B1193645 : Blo 618297 1193645 := bbase (se 3 (by rfl) ⟨223808, by rfl⟩ : syracuseStep 1193645 = 447617) (by norm_num)
theorem B931517 : Blo 618297 931517 := bbase (se 3 (by rfl) ⟨174659, by rfl⟩ : syracuseStep 931517 = 349319) (by norm_num)
theorem B931541 : Blo 618297 931541 := bbase (se 7 (by rfl) ⟨10916, by rfl⟩ : syracuseStep 931541 = 21833) (by norm_num)
theorem B931565 : Blo 618297 931565 := bbase (se 3 (by rfl) ⟨174668, by rfl⟩ : syracuseStep 931565 = 349337) (by norm_num)
theorem B931589 : Blo 618297 931589 := bbase (se 4 (by rfl) ⟨87336, by rfl⟩ : syracuseStep 931589 = 174673) (by norm_num)
theorem B931613 : Blo 618297 931613 := bbase (se 3 (by rfl) ⟨174677, by rfl⟩ : syracuseStep 931613 = 349355) (by norm_num)
theorem B931637 : Blo 618297 931637 := bbase (se 5 (by rfl) ⟨43670, by rfl⟩ : syracuseStep 931637 = 87341) (by norm_num)
theorem B931661 : Blo 618297 931661 := bbase (se 3 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 931661 = 349373) (by norm_num)
theorem B931685 : Blo 618297 931685 := bbase (se 4 (by rfl) ⟨87345, by rfl⟩ : syracuseStep 931685 = 174691) (by norm_num)
theorem B931709 : Blo 618297 931709 := bbase (se 3 (by rfl) ⟨174695, by rfl⟩ : syracuseStep 931709 = 349391) (by norm_num)
theorem B931733 : Blo 618297 931733 := bbase (se 6 (by rfl) ⟨21837, by rfl⟩ : syracuseStep 931733 = 43675) (by norm_num)
theorem B1488797 : Blo 618297 1488797 := bbase (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) (by norm_num)
theorem B1324973 : Blo 618297 1324973 := bbase (se 3 (by rfl) ⟨248432, by rfl⟩ : syracuseStep 1324973 = 496865) (by norm_num)
theorem B931757 : Blo 618297 931757 := bbase (se 3 (by rfl) ⟨174704, by rfl⟩ : syracuseStep 931757 = 349409) (by norm_num)
theorem B931781 : Blo 618297 931781 := bbase (se 4 (by rfl) ⟨87354, by rfl⟩ : syracuseStep 931781 = 174709) (by norm_num)
theorem B931805 : Blo 618297 931805 := bbase (se 3 (by rfl) ⟨174713, by rfl⟩ : syracuseStep 931805 = 349427) (by norm_num)
theorem B931829 : Blo 618297 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B931853 : Blo 618297 931853 := bbase (se 3 (by rfl) ⟨174722, by rfl⟩ : syracuseStep 931853 = 349445) (by norm_num)
theorem B931877 : Blo 618297 931877 := bbase (se 4 (by rfl) ⟨87363, by rfl⟩ : syracuseStep 931877 = 174727) (by norm_num)
theorem B1325117 : Blo 618297 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B931901 : Blo 618297 931901 := bbase (se 3 (by rfl) ⟨174731, by rfl⟩ : syracuseStep 931901 = 349463) (by norm_num)
theorem B931925 : Blo 618297 931925 := bbase (se 8 (by rfl) ⟨5460, by rfl⟩ : syracuseStep 931925 = 10921) (by norm_num)
theorem B1488989 : Blo 618297 1488989 := bbase (se 3 (by rfl) ⟨279185, by rfl⟩ : syracuseStep 1488989 = 558371) (by norm_num)
theorem B931949 : Blo 618297 931949 := bbase (se 3 (by rfl) ⟨174740, by rfl⟩ : syracuseStep 931949 = 349481) (by norm_num)
theorem B931973 : Blo 618297 931973 := bbase (se 4 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 931973 = 174745) (by norm_num)
theorem B931997 : Blo 618297 931997 := bbase (se 3 (by rfl) ⟨174749, by rfl⟩ : syracuseStep 931997 = 349499) (by norm_num)
theorem B932021 : Blo 618297 932021 := bbase (se 5 (by rfl) ⟨43688, by rfl⟩ : syracuseStep 932021 = 87377) (by norm_num)
theorem B932045 : Blo 618297 932045 := bbase (se 3 (by rfl) ⟨174758, by rfl⟩ : syracuseStep 932045 = 349517) (by norm_num)
theorem B932069 : Blo 618297 932069 := bbase (se 4 (by rfl) ⟨87381, by rfl⟩ : syracuseStep 932069 = 174763) (by norm_num)
theorem B932093 : Blo 618297 932093 := bbase (se 3 (by rfl) ⟨174767, by rfl⟩ : syracuseStep 932093 = 349535) (by norm_num)
theorem B932117 : Blo 618297 932117 := bbase (se 6 (by rfl) ⟨21846, by rfl⟩ : syracuseStep 932117 = 43693) (by norm_num)
theorem B932141 : Blo 618297 932141 := bbase (se 3 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 932141 = 349553) (by norm_num)
theorem B932165 : Blo 618297 932165 := bbase (se 4 (by rfl) ⟨87390, by rfl⟩ : syracuseStep 932165 = 174781) (by norm_num)
theorem B932189 : Blo 618297 932189 := bbase (se 3 (by rfl) ⟨174785, by rfl⟩ : syracuseStep 932189 = 349571) (by norm_num)
theorem B932213 : Blo 618297 932213 := bbase (se 5 (by rfl) ⟨43697, by rfl⟩ : syracuseStep 932213 = 87395) (by norm_num)
theorem B932237 : Blo 618297 932237 := bbase (se 3 (by rfl) ⟨174794, by rfl⟩ : syracuseStep 932237 = 349589) (by norm_num)
theorem B1325477 : Blo 618297 1325477 := bbase (se 4 (by rfl) ⟨124263, by rfl⟩ : syracuseStep 1325477 = 248527) (by norm_num)
theorem B932261 : Blo 618297 932261 := bbase (se 4 (by rfl) ⟨87399, by rfl⟩ : syracuseStep 932261 = 174799) (by norm_num)
theorem B932285 : Blo 618297 932285 := bbase (se 3 (by rfl) ⟨174803, by rfl⟩ : syracuseStep 932285 = 349607) (by norm_num)
theorem B1194445 : Blo 618297 1194445 := bbase (se 3 (by rfl) ⟨223958, by rfl⟩ : syracuseStep 1194445 = 447917) (by norm_num)
theorem B932309 : Blo 618297 932309 := bbase (se 7 (by rfl) ⟨10925, by rfl⟩ : syracuseStep 932309 = 21851) (by norm_num)
theorem B932333 : Blo 618297 932333 := bbase (se 3 (by rfl) ⟨174812, by rfl⟩ : syracuseStep 932333 = 349625) (by norm_num)
theorem B932357 : Blo 618297 932357 := bbase (se 4 (by rfl) ⟨87408, by rfl⟩ : syracuseStep 932357 = 174817) (by norm_num)
theorem B932381 : Blo 618297 932381 := bbase (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) (by norm_num)
theorem B932405 : Blo 618297 932405 := bbase (se 5 (by rfl) ⟨43706, by rfl⟩ : syracuseStep 932405 = 87413) (by norm_num)
theorem B932429 : Blo 618297 932429 := bbase (se 3 (by rfl) ⟨174830, by rfl⟩ : syracuseStep 932429 = 349661) (by norm_num)
theorem B932453 : Blo 618297 932453 := bbase (se 4 (by rfl) ⟨87417, by rfl⟩ : syracuseStep 932453 = 174835) (by norm_num)
theorem B932477 : Blo 618297 932477 := bbase (se 3 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 932477 = 349679) (by norm_num)
theorem B1391237 : Blo 618297 1391237 := bbase (se 4 (by rfl) ⟨130428, by rfl⟩ : syracuseStep 1391237 = 260857) (by norm_num)
theorem B932501 : Blo 618297 932501 := bbase (se 6 (by rfl) ⟨21855, by rfl⟩ : syracuseStep 932501 = 43711) (by norm_num)
theorem B932525 : Blo 618297 932525 := bbase (se 3 (by rfl) ⟨174848, by rfl⟩ : syracuseStep 932525 = 349697) (by norm_num)
theorem B932549 : Blo 618297 932549 := bbase (se 4 (by rfl) ⟨87426, by rfl⟩ : syracuseStep 932549 = 174853) (by norm_num)
theorem B1391309 : Blo 618297 1391309 := bbase (se 3 (by rfl) ⟨260870, by rfl⟩ : syracuseStep 1391309 = 521741) (by norm_num)
theorem B932573 : Blo 618297 932573 := bbase (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) (by norm_num)
theorem B932597 : Blo 618297 932597 := bbase (se 5 (by rfl) ⟨43715, by rfl⟩ : syracuseStep 932597 = 87431) (by norm_num)
theorem B932621 : Blo 618297 932621 := bbase (se 3 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 932621 = 349733) (by norm_num)
theorem B1391381 : Blo 618297 1391381 := bbase (se 6 (by rfl) ⟨32610, by rfl⟩ : syracuseStep 1391381 = 65221) (by norm_num)
theorem B932645 : Blo 618297 932645 := bbase (se 4 (by rfl) ⟨87435, by rfl⟩ : syracuseStep 932645 = 174871) (by norm_num)
theorem B932669 : Blo 618297 932669 := bbase (se 3 (by rfl) ⟨174875, by rfl⟩ : syracuseStep 932669 = 349751) (by norm_num)
theorem B932693 : Blo 618297 932693 := bbase (se 9 (by rfl) ⟨2732, by rfl⟩ : syracuseStep 932693 = 5465) (by norm_num)
theorem B1391453 : Blo 618297 1391453 := bbase (se 3 (by rfl) ⟨260897, by rfl⟩ : syracuseStep 1391453 = 521795) (by norm_num)
theorem B1489757 : Blo 618297 1489757 := bbase (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) (by norm_num)
theorem B932717 : Blo 618297 932717 := bbase (se 3 (by rfl) ⟨174884, by rfl⟩ : syracuseStep 932717 = 349769) (by norm_num)
theorem B1882997 : Blo 618297 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B932741 : Blo 618297 932741 := bbase (se 4 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 932741 = 174889) (by norm_num)
theorem B4701077 : Blo 618297 4701077 := bbase (se 6 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 4701077 = 220363) (by norm_num)
theorem B932765 : Blo 618297 932765 := bbase (se 3 (by rfl) ⟨174893, by rfl⟩ : syracuseStep 932765 = 349787) (by norm_num)
theorem B1391525 : Blo 618297 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B932789 : Blo 618297 932789 := bbase (se 5 (by rfl) ⟨43724, by rfl⟩ : syracuseStep 932789 = 87449) (by norm_num)
theorem B932813 : Blo 618297 932813 := bbase (se 3 (by rfl) ⟨174902, by rfl⟩ : syracuseStep 932813 = 349805) (by norm_num)
theorem B932837 : Blo 618297 932837 := bbase (se 4 (by rfl) ⟨87453, by rfl⟩ : syracuseStep 932837 = 174907) (by norm_num)
theorem B1391597 : Blo 618297 1391597 := bbase (se 3 (by rfl) ⟨260924, by rfl⟩ : syracuseStep 1391597 = 521849) (by norm_num)
theorem B932861 : Blo 618297 932861 := bbase (se 3 (by rfl) ⟨174911, by rfl⟩ : syracuseStep 932861 = 349823) (by norm_num)
theorem B932885 : Blo 618297 932885 := bbase (se 6 (by rfl) ⟨21864, by rfl⟩ : syracuseStep 932885 = 43729) (by norm_num)
theorem B932909 : Blo 618297 932909 := bbase (se 3 (by rfl) ⟨174920, by rfl⟩ : syracuseStep 932909 = 349841) (by norm_num)
theorem B1391669 : Blo 618297 1391669 := bbase (se 5 (by rfl) ⟨65234, by rfl⟩ : syracuseStep 1391669 = 130469) (by norm_num)
theorem B932933 : Blo 618297 932933 := bbase (se 4 (by rfl) ⟨87462, by rfl⟩ : syracuseStep 932933 = 174925) (by norm_num)
theorem B1981525 : Blo 618297 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B932957 : Blo 618297 932957 := bbase (se 3 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 932957 = 349859) (by norm_num)
theorem B932981 : Blo 618297 932981 := bbase (se 5 (by rfl) ⟨43733, by rfl⟩ : syracuseStep 932981 = 87467) (by norm_num)
theorem B1391741 : Blo 618297 1391741 := bbase (se 3 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 1391741 = 521903) (by norm_num)
theorem B933005 : Blo 618297 933005 := bbase (se 3 (by rfl) ⟨174938, by rfl⟩ : syracuseStep 933005 = 349877) (by norm_num)
theorem B933029 : Blo 618297 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B933053 : Blo 618297 933053 := bbase (se 3 (by rfl) ⟨174947, by rfl⟩ : syracuseStep 933053 = 349895) (by norm_num)
theorem B1391813 : Blo 618297 1391813 := bbase (se 4 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 1391813 = 260965) (by norm_num)
theorem B933077 : Blo 618297 933077 := bbase (se 7 (by rfl) ⟨10934, by rfl⟩ : syracuseStep 933077 = 21869) (by norm_num)
theorem B933101 : Blo 618297 933101 := bbase (se 3 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 933101 = 349913) (by norm_num)
theorem B933125 : Blo 618297 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B1391885 : Blo 618297 1391885 := bbase (se 3 (by rfl) ⟨260978, by rfl⟩ : syracuseStep 1391885 = 521957) (by norm_num)
theorem B1326365 : Blo 618297 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B933149 : Blo 618297 933149 := bbase (se 3 (by rfl) ⟨174965, by rfl⟩ : syracuseStep 933149 = 349931) (by norm_num)
theorem B933173 : Blo 618297 933173 := bbase (se 5 (by rfl) ⟨43742, by rfl⟩ : syracuseStep 933173 = 87485) (by norm_num)
theorem B933197 : Blo 618297 933197 := bbase (se 3 (by rfl) ⟨174974, by rfl⟩ : syracuseStep 933197 = 349949) (by norm_num)
theorem B1391957 : Blo 618297 1391957 := bbase (se 11 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 1391957 = 2039) (by norm_num)
theorem B933221 : Blo 618297 933221 := bbase (se 4 (by rfl) ⟨87489, by rfl⟩ : syracuseStep 933221 = 174979) (by norm_num)
theorem B933245 : Blo 618297 933245 := bbase (se 3 (by rfl) ⟨174983, by rfl⟩ : syracuseStep 933245 = 349967) (by norm_num)
theorem B638357 : Blo 618297 638357 := bbase (se 6 (by rfl) ⟨14961, by rfl⟩ : syracuseStep 638357 = 29923) (by norm_num)
theorem B933269 : Blo 618297 933269 := bbase (se 6 (by rfl) ⟨21873, by rfl⟩ : syracuseStep 933269 = 43747) (by norm_num)
theorem B1392029 : Blo 618297 1392029 := bbase (se 3 (by rfl) ⟨261005, by rfl⟩ : syracuseStep 1392029 = 522011) (by norm_num)
theorem B933293 : Blo 618297 933293 := bbase (se 3 (by rfl) ⟨174992, by rfl⟩ : syracuseStep 933293 = 349985) (by norm_num)
theorem B933317 : Blo 618297 933317 := bbase (se 4 (by rfl) ⟨87498, by rfl⟩ : syracuseStep 933317 = 174997) (by norm_num)
theorem B933341 : Blo 618297 933341 := bbase (se 3 (by rfl) ⟨175001, by rfl⟩ : syracuseStep 933341 = 350003) (by norm_num)
theorem B1392101 : Blo 618297 1392101 := bbase (se 4 (by rfl) ⟨130509, by rfl⟩ : syracuseStep 1392101 = 261019) (by norm_num)
theorem B933365 : Blo 618297 933365 := bbase (se 5 (by rfl) ⟨43751, by rfl⟩ : syracuseStep 933365 = 87503) (by norm_num)
theorem B933389 : Blo 618297 933389 := bbase (se 3 (by rfl) ⟨175010, by rfl⟩ : syracuseStep 933389 = 350021) (by norm_num)
theorem B1326613 : Blo 618297 1326613 := bbase (se 6 (by rfl) ⟨31092, by rfl⟩ : syracuseStep 1326613 = 62185) (by norm_num)
theorem B933413 : Blo 618297 933413 := bbase (se 4 (by rfl) ⟨87507, by rfl⟩ : syracuseStep 933413 = 175015) (by norm_num)
theorem B1392173 : Blo 618297 1392173 := bbase (se 3 (by rfl) ⟨261032, by rfl⟩ : syracuseStep 1392173 = 522065) (by norm_num)
theorem B933437 : Blo 618297 933437 := bbase (se 3 (by rfl) ⟨175019, by rfl⟩ : syracuseStep 933437 = 350039) (by norm_num)
theorem B1392245 : Blo 618297 1392245 := bbase (se 5 (by rfl) ⟨65261, by rfl⟩ : syracuseStep 1392245 = 130523) (by norm_num)
theorem B1392317 : Blo 618297 1392317 := bbase (se 3 (by rfl) ⟨261059, by rfl⟩ : syracuseStep 1392317 = 522119) (by norm_num)
theorem B1392389 : Blo 618297 1392389 := bbase (se 4 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 1392389 = 261073) (by norm_num)
theorem B638761 : Blo 618297 638761 := bbase (se 2 (by rfl) ⟨239535, by rfl⟩ : syracuseStep 638761 = 479071) (by norm_num)
theorem B638777 : Blo 618297 638777 := bbase (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) (by norm_num)
theorem B1392461 : Blo 618297 1392461 := bbase (se 3 (by rfl) ⟨261086, by rfl⟩ : syracuseStep 1392461 = 522173) (by norm_num)
theorem B1884005 : Blo 618297 1884005 := bbase (se 4 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 1884005 = 353251) (by norm_num)
theorem B1261453 : Blo 618297 1261453 := bbase (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) (by norm_num)
theorem B1392533 : Blo 618297 1392533 := bbase (se 6 (by rfl) ⟨32637, by rfl⟩ : syracuseStep 1392533 = 65275) (by norm_num)
theorem B1392605 : Blo 618297 1392605 := bbase (se 3 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 1392605 = 522227) (by norm_num)
theorem B1327117 : Blo 618297 1327117 := bbase (se 3 (by rfl) ⟨248834, by rfl⟩ : syracuseStep 1327117 = 497669) (by norm_num)
theorem B1392677 : Blo 618297 1392677 := bbase (se 4 (by rfl) ⟨130563, by rfl⟩ : syracuseStep 1392677 = 261127) (by norm_num)
theorem B671825 : Blo 618297 671825 := bbase (se 2 (by rfl) ⟨251934, by rfl⟩ : syracuseStep 671825 = 503869) (by norm_num)
theorem B639073 : Blo 618297 639073 := bbase (se 2 (by rfl) ⟨239652, by rfl⟩ : syracuseStep 639073 = 479305) (by norm_num)
theorem B1392749 : Blo 618297 1392749 := bbase (se 3 (by rfl) ⟨261140, by rfl⟩ : syracuseStep 1392749 = 522281) (by norm_num)
theorem B1392821 : Blo 618297 1392821 := bbase (se 5 (by rfl) ⟨65288, by rfl⟩ : syracuseStep 1392821 = 130577) (by norm_num)
theorem B1392893 : Blo 618297 1392893 := bbase (se 3 (by rfl) ⟨261167, by rfl⟩ : syracuseStep 1392893 = 522335) (by norm_num)
theorem B1392965 : Blo 618297 1392965 := bbase (se 4 (by rfl) ⟨130590, by rfl⟩ : syracuseStep 1392965 = 261181) (by norm_num)
theorem B1818949 : Blo 618297 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B1393037 : Blo 618297 1393037 := bbase (se 3 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 1393037 = 522389) (by norm_num)
theorem B1393109 : Blo 618297 1393109 := bbase (se 7 (by rfl) ⟨16325, by rfl⟩ : syracuseStep 1393109 = 32651) (by norm_num)
theorem B1393181 : Blo 618297 1393181 := bbase (se 3 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 1393181 = 522443) (by norm_num)
theorem B836173 : Blo 618297 836173 := bbase (se 3 (by rfl) ⟨156782, by rfl⟩ : syracuseStep 836173 = 313565) (by norm_num)
theorem B1360469 : Blo 618297 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B1393253 : Blo 618297 1393253 := bbase (se 4 (by rfl) ⟨130617, by rfl⟩ : syracuseStep 1393253 = 261235) (by norm_num)
theorem B1393325 : Blo 618297 1393325 := bbase (se 3 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 1393325 = 522497) (by norm_num)
theorem B1393397 : Blo 618297 1393397 := bbase (se 5 (by rfl) ⟨65315, by rfl⟩ : syracuseStep 1393397 = 130631) (by norm_num)
theorem B1884917 : Blo 618297 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B1393469 : Blo 618297 1393469 := bbase (se 3 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 1393469 = 522551) (by norm_num)
theorem B2900821 : Blo 618297 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B705385 : Blo 618297 705385 := bbase (se 2 (by rfl) ⟨264519, by rfl⟩ : syracuseStep 705385 = 529039) (by norm_num)
theorem B1393541 : Blo 618297 1393541 := bbase (se 4 (by rfl) ⟨130644, by rfl⟩ : syracuseStep 1393541 = 261289) (by norm_num)
theorem B1328005 : Blo 618297 1328005 := bbase (se 4 (by rfl) ⟨124500, by rfl⟩ : syracuseStep 1328005 = 249001) (by norm_num)
theorem B1491853 : Blo 618297 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B1393613 : Blo 618297 1393613 := bbase (se 3 (by rfl) ⟨261302, by rfl⟩ : syracuseStep 1393613 = 522605) (by norm_num)
theorem B3130325 : Blo 618297 3130325 := bbase (se 7 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 3130325 = 73367) (by norm_num)
theorem B836573 : Blo 618297 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B1393685 : Blo 618297 1393685 := bbase (se 6 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 1393685 = 65329) (by norm_num)
theorem B1393757 : Blo 618297 1393757 := bbase (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) (by norm_num)
theorem B1393829 : Blo 618297 1393829 := bbase (se 4 (by rfl) ⟨130671, by rfl⟩ : syracuseStep 1393829 = 261343) (by norm_num)
theorem B836821 : Blo 618297 836821 := bbase (se 7 (by rfl) ⟨9806, by rfl⟩ : syracuseStep 836821 = 19613) (by norm_num)
theorem B1393901 : Blo 618297 1393901 := bbase (se 3 (by rfl) ⟨261356, by rfl⟩ : syracuseStep 1393901 = 522713) (by norm_num)
theorem B1393973 : Blo 618297 1393973 := bbase (se 5 (by rfl) ⟨65342, by rfl⟩ : syracuseStep 1393973 = 130685) (by norm_num)
theorem B3982709 : Blo 618297 3982709 := bbase (se 5 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 3982709 = 373379) (by norm_num)
theorem B1328501 : Blo 618297 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B1394045 : Blo 618297 1394045 := bbase (se 3 (by rfl) ⟨261383, by rfl⟩ : syracuseStep 1394045 = 522767) (by norm_num)
theorem B1394117 : Blo 618297 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B1590749 : Blo 618297 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1492469 : Blo 618297 1492469 := bbase (se 5 (by rfl) ⟨69959, by rfl⟩ : syracuseStep 1492469 = 139919) (by norm_num)
theorem B1394189 : Blo 618297 1394189 := bbase (se 3 (by rfl) ⟨261410, by rfl⟩ : syracuseStep 1394189 = 522821) (by norm_num)
theorem B1492525 : Blo 618297 1492525 := bbase (se 3 (by rfl) ⟨279848, by rfl⟩ : syracuseStep 1492525 = 559697) (by norm_num)
theorem B1394261 : Blo 618297 1394261 := bbase (se 8 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 1394261 = 16339) (by norm_num)
theorem B2508421 : Blo 618297 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B1394333 : Blo 618297 1394333 := bbase (se 3 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 1394333 = 522875) (by norm_num)
theorem B706261 : Blo 618297 706261 := bbase (se 7 (by rfl) ⟨8276, by rfl⟩ : syracuseStep 706261 = 16553) (by norm_num)
theorem B1394405 : Blo 618297 1394405 := bbase (se 4 (by rfl) ⟨130725, by rfl⟩ : syracuseStep 1394405 = 261451) (by norm_num)
theorem B1394477 : Blo 618297 1394477 := bbase (se 3 (by rfl) ⟨261464, by rfl⟩ : syracuseStep 1394477 = 522929) (by norm_num)
theorem B1394549 : Blo 618297 1394549 := bbase (se 5 (by rfl) ⟨65369, by rfl⟩ : syracuseStep 1394549 = 130739) (by norm_num)
theorem B706469 : Blo 618297 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B1394621 : Blo 618297 1394621 := bbase (se 3 (by rfl) ⟨261491, by rfl⟩ : syracuseStep 1394621 = 522983) (by norm_num)
theorem B1394693 : Blo 618297 1394693 := bbase (se 4 (by rfl) ⟨130752, by rfl⟩ : syracuseStep 1394693 = 261505) (by norm_num)
theorem B1394765 : Blo 618297 1394765 := bbase (se 3 (by rfl) ⟨261518, by rfl⟩ : syracuseStep 1394765 = 523037) (by norm_num)
theorem B1394837 : Blo 618297 1394837 := bbase (se 6 (by rfl) ⟨32691, by rfl⟩ : syracuseStep 1394837 = 65383) (by norm_num)
theorem B1394909 : Blo 618297 1394909 := bbase (se 3 (by rfl) ⟨261545, by rfl⟩ : syracuseStep 1394909 = 523091) (by norm_num)
theorem B3131621 : Blo 618297 3131621 := bbase (se 4 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 3131621 = 587179) (by norm_num)
theorem B706817 : Blo 618297 706817 := bbase (se 2 (by rfl) ⟨265056, by rfl⟩ : syracuseStep 706817 = 530113) (by norm_num)
theorem B1394981 : Blo 618297 1394981 := bbase (se 4 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 1394981 = 261559) (by norm_num)
theorem B1395053 : Blo 618297 1395053 := bbase (se 3 (by rfl) ⟨261572, by rfl⟩ : syracuseStep 1395053 = 523145) (by norm_num)
theorem B1395125 : Blo 618297 1395125 := bbase (se 5 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 1395125 = 130793) (by norm_num)
theorem B1395197 : Blo 618297 1395197 := bbase (se 3 (by rfl) ⟨261599, by rfl⟩ : syracuseStep 1395197 = 523199) (by norm_num)
theorem B1493525 : Blo 618297 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B1395269 : Blo 618297 1395269 := bbase (se 4 (by rfl) ⟨130806, by rfl⟩ : syracuseStep 1395269 = 261613) (by norm_num)
theorem B1395341 : Blo 618297 1395341 := bbase (se 3 (by rfl) ⟨261626, by rfl⟩ : syracuseStep 1395341 = 523253) (by norm_num)
theorem B1395413 : Blo 618297 1395413 := bbase (se 7 (by rfl) ⟨16352, by rfl⟩ : syracuseStep 1395413 = 32705) (by norm_num)
theorem B1395485 : Blo 618297 1395485 := bbase (se 3 (by rfl) ⟨261653, by rfl⟩ : syracuseStep 1395485 = 523307) (by norm_num)
theorem B1395557 : Blo 618297 1395557 := bbase (se 4 (by rfl) ⟨130833, by rfl⟩ : syracuseStep 1395557 = 261667) (by norm_num)
theorem B1395629 : Blo 618297 1395629 := bbase (se 3 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 1395629 = 523361) (by norm_num)
theorem B1395701 : Blo 618297 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B1395773 : Blo 618297 1395773 := bbase (se 3 (by rfl) ⟨261707, by rfl⟩ : syracuseStep 1395773 = 523415) (by norm_num)
theorem B1395845 : Blo 618297 1395845 := bbase (se 4 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 1395845 = 261721) (by norm_num)
theorem B2837701 : Blo 618297 2837701 := bbase (se 4 (by rfl) ⟨266034, by rfl⟩ : syracuseStep 2837701 = 532069) (by norm_num)
theorem B1395917 : Blo 618297 1395917 := bbase (se 3 (by rfl) ⟨261734, by rfl⟩ : syracuseStep 1395917 = 523469) (by norm_num)
theorem B1395989 : Blo 618297 1395989 := bbase (se 6 (by rfl) ⟨32718, by rfl⟩ : syracuseStep 1395989 = 65437) (by norm_num)
theorem B1396061 : Blo 618297 1396061 := bbase (se 3 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 1396061 = 523523) (by norm_num)
theorem B839005 : Blo 618297 839005 := bbase (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) (by norm_num)
theorem B3526037 : Blo 618297 3526037 := bbase (se 6 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 3526037 = 165283) (by norm_num)
theorem B1396133 : Blo 618297 1396133 := bbase (se 4 (by rfl) ⟨130887, by rfl⟩ : syracuseStep 1396133 = 261775) (by norm_num)
theorem B2641349 : Blo 618297 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B1396205 : Blo 618297 1396205 := bbase (se 3 (by rfl) ⟨261788, by rfl⟩ : syracuseStep 1396205 = 523577) (by norm_num)
theorem B3132917 : Blo 618297 3132917 := bbase (se 5 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 3132917 = 293711) (by norm_num)
theorem B1396277 : Blo 618297 1396277 := bbase (se 5 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 1396277 = 130901) (by norm_num)
theorem B1396349 : Blo 618297 1396349 := bbase (se 3 (by rfl) ⟨261815, by rfl⟩ : syracuseStep 1396349 = 523631) (by norm_num)
theorem B708277 : Blo 618297 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B1396421 : Blo 618297 1396421 := bbase (se 4 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 1396421 = 261829) (by norm_num)
theorem B708349 : Blo 618297 708349 := bbase (se 3 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 708349 = 265631) (by norm_num)
theorem B1396493 : Blo 618297 1396493 := bbase (se 3 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 1396493 = 523685) (by norm_num)
theorem B1396565 : Blo 618297 1396565 := bbase (se 9 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 1396565 = 8183) (by norm_num)
theorem B1396637 : Blo 618297 1396637 := bbase (se 3 (by rfl) ⟨261869, by rfl⟩ : syracuseStep 1396637 = 523739) (by norm_num)
theorem B708545 : Blo 618297 708545 := bbase (se 2 (by rfl) ⟨265704, by rfl⟩ : syracuseStep 708545 = 531409) (by norm_num)
theorem B1396709 : Blo 618297 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B1396781 : Blo 618297 1396781 := bbase (se 3 (by rfl) ⟨261896, by rfl⟩ : syracuseStep 1396781 = 523793) (by norm_num)
theorem B1986677 : Blo 618297 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B1396853 : Blo 618297 1396853 := bbase (se 5 (by rfl) ⟨65477, by rfl⟩ : syracuseStep 1396853 = 130955) (by norm_num)
theorem B1396925 : Blo 618297 1396925 := bbase (se 3 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 1396925 = 523847) (by norm_num)
theorem B1396997 : Blo 618297 1396997 := bbase (se 4 (by rfl) ⟨130968, by rfl⟩ : syracuseStep 1396997 = 261937) (by norm_num)
theorem B1397069 : Blo 618297 1397069 := bbase (se 3 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 1397069 = 523901) (by norm_num)
theorem B840061 : Blo 618297 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B708997 : Blo 618297 708997 := bbase (se 4 (by rfl) ⟨66468, by rfl⟩ : syracuseStep 708997 = 132937) (by norm_num)
theorem B1397141 : Blo 618297 1397141 := bbase (se 6 (by rfl) ⟨32745, by rfl⟩ : syracuseStep 1397141 = 65491) (by norm_num)
theorem B2642341 : Blo 618297 2642341 := bbase (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) (by norm_num)
theorem B1397213 : Blo 618297 1397213 := bbase (se 3 (by rfl) ⟨261977, by rfl⟩ : syracuseStep 1397213 = 523955) (by norm_num)
theorem B709093 : Blo 618297 709093 := bbase (se 4 (by rfl) ⟨66477, by rfl⟩ : syracuseStep 709093 = 132955) (by norm_num)
theorem B2413061 : Blo 618297 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B1397285 : Blo 618297 1397285 := bbase (se 4 (by rfl) ⟨130995, by rfl⟩ : syracuseStep 1397285 = 261991) (by norm_num)
theorem B1397357 : Blo 618297 1397357 := bbase (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) (by norm_num)
theorem B1397429 : Blo 618297 1397429 := bbase (se 5 (by rfl) ⟨65504, by rfl⟩ : syracuseStep 1397429 = 131009) (by norm_num)
theorem B840389 : Blo 618297 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B1397501 : Blo 618297 1397501 := bbase (se 3 (by rfl) ⟨262031, by rfl⟩ : syracuseStep 1397501 = 524063) (by norm_num)
theorem B3134213 : Blo 618297 3134213 := bbase (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) (by norm_num)
theorem B1397573 : Blo 618297 1397573 := bbase (se 4 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 1397573 = 262045) (by norm_num)
theorem B4477781 : Blo 618297 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B67982165 : Blo 618297 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B1397645 : Blo 618297 1397645 := bbase (se 3 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 1397645 = 524117) (by norm_num)
theorem B1889173 : Blo 618297 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B2347973 : Blo 618297 2347973 := bbase (se 4 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 2347973 = 440245) (by norm_num)
theorem B1397717 : Blo 618297 1397717 := bbase (se 7 (by rfl) ⟨16379, by rfl⟩ : syracuseStep 1397717 = 32759) (by norm_num)
theorem B1987573 : Blo 618297 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B1397789 : Blo 618297 1397789 := bbase (se 3 (by rfl) ⟨262085, by rfl⟩ : syracuseStep 1397789 = 524171) (by norm_num)
theorem B1397861 : Blo 618297 1397861 := bbase (se 4 (by rfl) ⟨131049, by rfl⟩ : syracuseStep 1397861 = 262099) (by norm_num)
theorem B1397933 : Blo 618297 1397933 := bbase (se 3 (by rfl) ⟨262112, by rfl⟩ : syracuseStep 1397933 = 524225) (by norm_num)
theorem B2348261 : Blo 618297 2348261 := bbase (se 4 (by rfl) ⟨220149, by rfl⟩ : syracuseStep 2348261 = 440299) (by norm_num)
theorem B1398005 : Blo 618297 1398005 := bbase (se 5 (by rfl) ⟨65531, by rfl⟩ : syracuseStep 1398005 = 131063) (by norm_num)
theorem B840973 : Blo 618297 840973 := bbase (se 3 (by rfl) ⟨157682, by rfl⟩ : syracuseStep 840973 = 315365) (by norm_num)
theorem B7165205 : Blo 618297 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B1398077 : Blo 618297 1398077 := bbase (se 3 (by rfl) ⟨262139, by rfl⟩ : syracuseStep 1398077 = 524279) (by norm_num)
theorem B1987973 : Blo 618297 1987973 := bbase (se 4 (by rfl) ⟨186372, by rfl⟩ : syracuseStep 1987973 = 372745) (by norm_num)
theorem B1398149 : Blo 618297 1398149 := bbase (se 4 (by rfl) ⟨131076, by rfl⟩ : syracuseStep 1398149 = 262153) (by norm_num)
theorem B742861 : Blo 618297 742861 := bbase (se 3 (by rfl) ⟨139286, by rfl⟩ : syracuseStep 742861 = 278573) (by norm_num)
theorem B1398221 : Blo 618297 1398221 := bbase (se 3 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 1398221 = 524333) (by norm_num)
theorem B1005061 : Blo 618297 1005061 := bbase (se 4 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 1005061 = 188449) (by norm_num)
theorem B1398293 : Blo 618297 1398293 := bbase (se 6 (by rfl) ⟨32772, by rfl⟩ : syracuseStep 1398293 = 65545) (by norm_num)
theorem B1398365 : Blo 618297 1398365 := bbase (se 3 (by rfl) ⟨262193, by rfl⟩ : syracuseStep 1398365 = 524387) (by norm_num)
theorem B1398437 : Blo 618297 1398437 := bbase (se 4 (by rfl) ⟨131103, by rfl⟩ : syracuseStep 1398437 = 262207) (by norm_num)
theorem B2971349 : Blo 618297 2971349 := bbase (se 7 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 2971349 = 69641) (by norm_num)
theorem B1398509 : Blo 618297 1398509 := bbase (se 3 (by rfl) ⟨262220, by rfl⟩ : syracuseStep 1398509 = 524441) (by norm_num)
theorem B1398581 : Blo 618297 1398581 := bbase (se 5 (by rfl) ⟨65558, by rfl⟩ : syracuseStep 1398581 = 131117) (by norm_num)
theorem B1398653 : Blo 618297 1398653 := bbase (se 3 (by rfl) ⟨262247, by rfl⟩ : syracuseStep 1398653 = 524495) (by norm_num)
theorem B743341 : Blo 618297 743341 := bbase (se 3 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 743341 = 278753) (by norm_num)
theorem B1398725 : Blo 618297 1398725 := bbase (se 4 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 1398725 = 262261) (by norm_num)
theorem B5953493 : Blo 618297 5953493 := bbase (se 7 (by rfl) ⟨69767, by rfl⟩ : syracuseStep 5953493 = 139535) (by norm_num)
theorem B1398797 : Blo 618297 1398797 := bbase (se 3 (by rfl) ⟨262274, by rfl⟩ : syracuseStep 1398797 = 524549) (by norm_num)
theorem B3135509 : Blo 618297 3135509 := bbase (se 6 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 3135509 = 146977) (by norm_num)
theorem B2119765 : Blo 618297 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B1398869 : Blo 618297 1398869 := bbase (se 8 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 1398869 = 16393) (by norm_num)
theorem B2087045 : Blo 618297 2087045 := bbase (se 4 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 2087045 = 391321) (by norm_num)
theorem B1398941 : Blo 618297 1398941 := bbase (se 3 (by rfl) ⟨262301, by rfl⟩ : syracuseStep 1398941 = 524603) (by norm_num)
theorem B1399013 : Blo 618297 1399013 := bbase (se 4 (by rfl) ⟨131157, by rfl⟩ : syracuseStep 1399013 = 262315) (by norm_num)
theorem B1399085 : Blo 618297 1399085 := bbase (se 3 (by rfl) ⟨262328, by rfl⟩ : syracuseStep 1399085 = 524657) (by norm_num)
theorem B1399157 : Blo 618297 1399157 := bbase (se 5 (by rfl) ⟨65585, by rfl⟩ : syracuseStep 1399157 = 131171) (by norm_num)
theorem B2349445 : Blo 618297 2349445 := bbase (se 4 (by rfl) ⟨220260, by rfl⟩ : syracuseStep 2349445 = 440521) (by norm_num)
theorem B3627413 : Blo 618297 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B1399229 : Blo 618297 1399229 := bbase (se 3 (by rfl) ⟨262355, by rfl⟩ : syracuseStep 1399229 = 524711) (by norm_num)
theorem B4708853 : Blo 618297 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B1399301 : Blo 618297 1399301 := bbase (se 4 (by rfl) ⟨131184, by rfl⟩ : syracuseStep 1399301 = 262369) (by norm_num)
theorem B2087477 : Blo 618297 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B1399373 : Blo 618297 1399373 := bbase (se 3 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 1399373 = 524765) (by norm_num)
theorem B940645 : Blo 618297 940645 := bbase (se 4 (by rfl) ⟨88185, by rfl⟩ : syracuseStep 940645 = 176371) (by norm_num)
theorem B1399445 : Blo 618297 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B2349749 : Blo 618297 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B3627733 : Blo 618297 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B1399517 : Blo 618297 1399517 := bbase (se 3 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 1399517 = 524819) (by norm_num)
theorem B1596125 : Blo 618297 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B5298965 : Blo 618297 5298965 := bbase (se 6 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 5298965 = 248389) (by norm_num)
theorem B1399589 : Blo 618297 1399589 := bbase (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) (by norm_num)
theorem B2448181 : Blo 618297 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B1399661 : Blo 618297 1399661 := bbase (se 3 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 1399661 = 524873) (by norm_num)
theorem B3234725 : Blo 618297 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B1399733 : Blo 618297 1399733 := bbase (se 5 (by rfl) ⟨65612, by rfl⟩ : syracuseStep 1399733 = 131225) (by norm_num)
theorem B2087909 : Blo 618297 2087909 := bbase (se 4 (by rfl) ⟨195741, by rfl⟩ : syracuseStep 2087909 = 391483) (by norm_num)
theorem B1399805 : Blo 618297 1399805 := bbase (se 3 (by rfl) ⟨262463, by rfl⟩ : syracuseStep 1399805 = 524927) (by norm_num)
theorem B1399877 : Blo 618297 1399877 := bbase (se 4 (by rfl) ⟨131238, by rfl⟩ : syracuseStep 1399877 = 262477) (by norm_num)
theorem B1399949 : Blo 618297 1399949 := bbase (se 3 (by rfl) ⟨262490, by rfl⟩ : syracuseStep 1399949 = 524981) (by norm_num)
theorem B1793173 : Blo 618297 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B1400021 : Blo 618297 1400021 := bbase (se 7 (by rfl) ⟨16406, by rfl⟩ : syracuseStep 1400021 = 32813) (by norm_num)
theorem B744725 : Blo 618297 744725 := bbase (se 6 (by rfl) ⟨17454, by rfl⟩ : syracuseStep 744725 = 34909) (by norm_num)
theorem B1400093 : Blo 618297 1400093 := bbase (se 3 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 1400093 = 525035) (by norm_num)
theorem B3136805 : Blo 618297 3136805 := bbase (se 4 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 3136805 = 588151) (by norm_num)
theorem B13557077 : Blo 618297 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B1400165 : Blo 618297 1400165 := bbase (se 4 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 1400165 = 262531) (by norm_num)
theorem B2088341 : Blo 618297 2088341 := bbase (se 6 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 2088341 = 97891) (by norm_num)
theorem B744913 : Blo 618297 744913 := bbase (se 2 (by rfl) ⟨279342, by rfl⟩ : syracuseStep 744913 = 558685) (by norm_num)
theorem B1760741 : Blo 618297 1760741 := bbase (se 4 (by rfl) ⟨165069, by rfl⟩ : syracuseStep 1760741 = 330139) (by norm_num)
theorem B2514485 : Blo 618297 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B745129 : Blo 618297 745129 := bbase (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) (by norm_num)
theorem B2088773 : Blo 618297 2088773 := bbase (se 4 (by rfl) ⟨195822, by rfl⟩ : syracuseStep 2088773 = 391645) (by norm_num)
theorem B5103445 : Blo 618297 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B1761173 : Blo 618297 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B745417 : Blo 618297 745417 := bbase (se 2 (by rfl) ⟨279531, by rfl⟩ : syracuseStep 745417 = 559063) (by norm_num)
theorem B942301 : Blo 618297 942301 := bbase (se 3 (by rfl) ⟨176681, by rfl⟩ : syracuseStep 942301 = 353363) (by norm_num)
theorem B2089205 : Blo 618297 2089205 := bbase (se 5 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 2089205 = 195863) (by norm_num)
theorem B942349 : Blo 618297 942349 := bbase (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) (by norm_num)
theorem B2974133 : Blo 618297 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B3138101 : Blo 618297 3138101 := bbase (se 5 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 3138101 = 294197) (by norm_num)
theorem B1761925 : Blo 618297 1761925 := bbase (se 4 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 1761925 = 330361) (by norm_num)
theorem B2089637 : Blo 618297 2089637 := bbase (se 4 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 2089637 = 391807) (by norm_num)
theorem B1565365 : Blo 618297 1565365 := bbase (se 5 (by rfl) ⟨73376, by rfl⟩ : syracuseStep 1565365 = 146753) (by norm_num)
theorem B2351861 : Blo 618297 2351861 := bbase (se 5 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 2351861 = 220487) (by norm_num)
theorem B1565477 : Blo 618297 1565477 := bbase (se 4 (by rfl) ⟨146763, by rfl⟩ : syracuseStep 1565477 = 293527) (by norm_num)
theorem B1794901 : Blo 618297 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B1565669 : Blo 618297 1565669 := bbase (se 4 (by rfl) ⟨146781, by rfl⟩ : syracuseStep 1565669 = 293563) (by norm_num)
theorem B2352149 : Blo 618297 2352149 := bbase (se 6 (by rfl) ⟨55128, by rfl⟩ : syracuseStep 2352149 = 110257) (by norm_num)
theorem B2090069 : Blo 618297 2090069 := bbase (se 8 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 2090069 = 24493) (by norm_num)
theorem B1991765 : Blo 618297 1991765 := bbase (se 8 (by rfl) ⟨11670, by rfl⟩ : syracuseStep 1991765 = 23341) (by norm_num)
theorem B746705 : Blo 618297 746705 := bbase (se 2 (by rfl) ⟨280014, by rfl⟩ : syracuseStep 746705 = 560029) (by norm_num)
theorem B2647349 : Blo 618297 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B1566013 : Blo 618297 1566013 := bbase (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) (by norm_num)
theorem B1566125 : Blo 618297 1566125 := bbase (se 3 (by rfl) ⟨293648, by rfl⟩ : syracuseStep 1566125 = 587297) (by norm_num)
theorem B2090501 : Blo 618297 2090501 := bbase (se 4 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 2090501 = 391969) (by norm_num)
theorem B2647637 : Blo 618297 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B1566317 : Blo 618297 1566317 := bbase (se 3 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 1566317 = 587369) (by norm_num)
theorem B747301 : Blo 618297 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B681781 : Blo 618297 681781 := bbase (se 5 (by rfl) ⟨31958, by rfl⟩ : syracuseStep 681781 = 63917) (by norm_num)
theorem B3139397 : Blo 618297 3139397 := bbase (se 4 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 3139397 = 588637) (by norm_num)
theorem B943949 : Blo 618297 943949 := bbase (se 3 (by rfl) ⟨176990, by rfl⟩ : syracuseStep 943949 = 353981) (by norm_num)
theorem B747397 : Blo 618297 747397 := bbase (se 4 (by rfl) ⟨70068, by rfl⟩ : syracuseStep 747397 = 140137) (by norm_num)
theorem B2090933 : Blo 618297 2090933 := bbase (se 5 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 2090933 = 196025) (by norm_num)
theorem B1566661 : Blo 618297 1566661 := bbase (se 4 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 1566661 = 293749) (by norm_num)
theorem B1566773 : Blo 618297 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B1992853 : Blo 618297 1992853 := bbase (se 6 (by rfl) ⟨46707, by rfl⟩ : syracuseStep 1992853 = 93415) (by norm_num)
theorem B1271965 : Blo 618297 1271965 := bbase (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) (by norm_num)
theorem B2353333 : Blo 618297 2353333 := bbase (se 5 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 2353333 = 220625) (by norm_num)
theorem B1566965 : Blo 618297 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B2648389 : Blo 618297 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B2091365 : Blo 618297 2091365 := bbase (se 4 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 2091365 = 392131) (by norm_num)
theorem B2353637 : Blo 618297 2353637 := bbase (se 4 (by rfl) ⟨220653, by rfl⟩ : syracuseStep 2353637 = 441307) (by norm_num)
theorem B1174085 : Blo 618297 1174085 := bbase (se 4 (by rfl) ⟨110070, by rfl⟩ : syracuseStep 1174085 = 220141) (by norm_num)
theorem B1567309 : Blo 618297 1567309 := bbase (se 3 (by rfl) ⟨293870, by rfl⟩ : syracuseStep 1567309 = 587741) (by norm_num)
theorem B1567421 : Blo 618297 1567421 := bbase (se 3 (by rfl) ⟨293891, by rfl⟩ : syracuseStep 1567421 = 587783) (by norm_num)
theorem B2091797 : Blo 618297 2091797 := bbase (se 6 (by rfl) ⟨49026, by rfl⟩ : syracuseStep 2091797 = 98053) (by norm_num)
theorem B1567613 : Blo 618297 1567613 := bbase (se 3 (by rfl) ⟨293927, by rfl⟩ : syracuseStep 1567613 = 587855) (by norm_num)
theorem B1043381 : Blo 618297 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B2649125 : Blo 618297 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B1043509 : Blo 618297 1043509 := bbase (se 5 (by rfl) ⟨48914, by rfl⟩ : syracuseStep 1043509 = 97829) (by norm_num)
theorem B3140693 : Blo 618297 3140693 := bbase (se 8 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 3140693 = 36805) (by norm_num)
theorem B2518117 : Blo 618297 2518117 := bbase (se 4 (by rfl) ⟨236073, by rfl⟩ : syracuseStep 2518117 = 472147) (by norm_num)
theorem B1043597 : Blo 618297 1043597 := bbase (se 3 (by rfl) ⟨195674, by rfl⟩ : syracuseStep 1043597 = 391349) (by norm_num)
theorem B2092229 : Blo 618297 2092229 := bbase (se 4 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 2092229 = 392293) (by norm_num)
theorem B1567957 : Blo 618297 1567957 := bbase (se 7 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 1567957 = 36749) (by norm_num)
theorem B945365 : Blo 618297 945365 := bbase (se 7 (by rfl) ⟨11078, by rfl⟩ : syracuseStep 945365 = 22157) (by norm_num)
theorem B1043725 : Blo 618297 1043725 := bbase (se 3 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 1043725 = 391397) (by norm_num)
theorem B3534101 : Blo 618297 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B1174837 : Blo 618297 1174837 := bbase (se 5 (by rfl) ⟨55070, by rfl⟩ : syracuseStep 1174837 = 110141) (by norm_num)
theorem B1568069 : Blo 618297 1568069 := bbase (se 4 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 1568069 = 294013) (by norm_num)
theorem B1043813 : Blo 618297 1043813 := bbase (se 4 (by rfl) ⟨97857, by rfl⟩ : syracuseStep 1043813 = 195715) (by norm_num)
theorem B1764773 : Blo 618297 1764773 := bbase (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) (by norm_num)
theorem B1174981 : Blo 618297 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B1043941 : Blo 618297 1043941 := bbase (se 4 (by rfl) ⟨97869, by rfl⟩ : syracuseStep 1043941 = 195739) (by norm_num)
theorem B1568261 : Blo 618297 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B5041685 : Blo 618297 5041685 := bbase (se 6 (by rfl) ⟨118164, by rfl⟩ : syracuseStep 5041685 = 236329) (by norm_num)
theorem B1044029 : Blo 618297 1044029 := bbase (se 3 (by rfl) ⟨195755, by rfl⟩ : syracuseStep 1044029 = 391511) (by norm_num)
theorem B1175141 : Blo 618297 1175141 := bbase (se 4 (by rfl) ⟨110169, by rfl⟩ : syracuseStep 1175141 = 220339) (by norm_num)
theorem B3174005 : Blo 618297 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B2092661 : Blo 618297 2092661 := bbase (se 5 (by rfl) ⟨98093, by rfl⟩ : syracuseStep 2092661 = 196187) (by norm_num)
theorem B1044157 : Blo 618297 1044157 := bbase (se 3 (by rfl) ⟨195779, by rfl⟩ : syracuseStep 1044157 = 391559) (by norm_num)
theorem B1175285 : Blo 618297 1175285 := bbase (se 5 (by rfl) ⟨55091, by rfl⟩ : syracuseStep 1175285 = 110183) (by norm_num)
theorem B1044245 : Blo 618297 1044245 := bbase (se 6 (by rfl) ⟨24474, by rfl⟩ : syracuseStep 1044245 = 48949) (by norm_num)
theorem B1568605 : Blo 618297 1568605 := bbase (se 3 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 1568605 = 588227) (by norm_num)
theorem B2977669 : Blo 618297 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1044373 : Blo 618297 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B1568717 : Blo 618297 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B1044461 : Blo 618297 1044461 := bbase (se 3 (by rfl) ⟨195836, by rfl⟩ : syracuseStep 1044461 = 391673) (by norm_num)
theorem B1175573 : Blo 618297 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B2093093 : Blo 618297 2093093 := bbase (se 4 (by rfl) ⟨196227, by rfl⟩ : syracuseStep 2093093 = 392455) (by norm_num)
theorem B1044589 : Blo 618297 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B1568909 : Blo 618297 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B1175725 : Blo 618297 1175725 := bbase (se 3 (by rfl) ⟨220448, by rfl⟩ : syracuseStep 1175725 = 440897) (by norm_num)
theorem B1044677 : Blo 618297 1044677 := bbase (se 4 (by rfl) ⟨97938, by rfl⟩ : syracuseStep 1044677 = 195877) (by norm_num)
theorem B782561 : Blo 618297 782561 := bbase (se 2 (by rfl) ⟨293460, by rfl⟩ : syracuseStep 782561 = 586921) (by norm_num)
theorem B782617 : Blo 618297 782617 := bbase (se 2 (by rfl) ⟨293481, by rfl⟩ : syracuseStep 782617 = 586963) (by norm_num)
theorem B1044805 : Blo 618297 1044805 := bbase (se 4 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 1044805 = 195901) (by norm_num)
theorem B3141989 : Blo 618297 3141989 := bbase (se 4 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 3141989 = 589123) (by norm_num)
theorem B782713 : Blo 618297 782713 := bbase (se 2 (by rfl) ⟨293517, by rfl⟩ : syracuseStep 782713 = 587035) (by norm_num)
theorem B1044893 : Blo 618297 1044893 := bbase (se 3 (by rfl) ⟨195917, by rfl⟩ : syracuseStep 1044893 = 391835) (by norm_num)
theorem B3535285 : Blo 618297 3535285 := bbase (se 5 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 3535285 = 331433) (by norm_num)
theorem B2093525 : Blo 618297 2093525 := bbase (se 7 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 2093525 = 49067) (by norm_num)
theorem B1176029 : Blo 618297 1176029 := bbase (se 3 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 1176029 = 441011) (by norm_num)
theorem B1569253 : Blo 618297 1569253 := bbase (se 4 (by rfl) ⟨147117, by rfl⟩ : syracuseStep 1569253 = 294235) (by norm_num)
theorem B1045021 : Blo 618297 1045021 := bbase (se 3 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 1045021 = 391883) (by norm_num)
theorem B782885 : Blo 618297 782885 := bbase (se 4 (by rfl) ⟨73395, by rfl⟩ : syracuseStep 782885 = 146791) (by norm_num)
theorem B2355749 : Blo 618297 2355749 := bbase (se 4 (by rfl) ⟨220851, by rfl⟩ : syracuseStep 2355749 = 441703) (by norm_num)
theorem B1765957 : Blo 618297 1765957 := bbase (se 4 (by rfl) ⟨165558, by rfl⟩ : syracuseStep 1765957 = 331117) (by norm_num)
theorem B1569365 : Blo 618297 1569365 := bbase (se 8 (by rfl) ⟨9195, by rfl⟩ : syracuseStep 1569365 = 18391) (by norm_num)
theorem B782941 : Blo 618297 782941 := bbase (se 3 (by rfl) ⟨146801, by rfl⟩ : syracuseStep 782941 = 293603) (by norm_num)
theorem B1045109 : Blo 618297 1045109 := bbase (se 5 (by rfl) ⟨48989, by rfl⟩ : syracuseStep 1045109 = 97979) (by norm_num)
theorem B881293 : Blo 618297 881293 := bbase (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) (by norm_num)
theorem B783037 : Blo 618297 783037 := bbase (se 3 (by rfl) ⟨146819, by rfl⟩ : syracuseStep 783037 = 293639) (by norm_num)
theorem B1766117 : Blo 618297 1766117 := bbase (se 4 (by rfl) ⟨165573, by rfl⟩ : syracuseStep 1766117 = 331147) (by norm_num)
theorem B1045237 : Blo 618297 1045237 := bbase (se 5 (by rfl) ⟨48995, by rfl⟩ : syracuseStep 1045237 = 97991) (by norm_num)
theorem B1569557 : Blo 618297 1569557 := bbase (se 6 (by rfl) ⟨36786, by rfl⟩ : syracuseStep 1569557 = 73573) (by norm_num)
theorem B2356037 : Blo 618297 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B1045325 : Blo 618297 1045325 := bbase (se 3 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 1045325 = 391997) (by norm_num)
theorem B5665621 : Blo 618297 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B783209 : Blo 618297 783209 := bbase (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) (by norm_num)
theorem B2093957 : Blo 618297 2093957 := bbase (se 4 (by rfl) ⟨196308, by rfl⟩ : syracuseStep 2093957 = 392617) (by norm_num)
theorem B783265 : Blo 618297 783265 := bbase (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) (by norm_num)
theorem B1045453 : Blo 618297 1045453 := bbase (se 3 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 1045453 = 392045) (by norm_num)
theorem B1766357 : Blo 618297 1766357 := bbase (se 7 (by rfl) ⟨20699, by rfl⟩ : syracuseStep 1766357 = 41399) (by norm_num)
theorem B783361 : Blo 618297 783361 := bbase (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) (by norm_num)
theorem B1045541 : Blo 618297 1045541 := bbase (se 4 (by rfl) ⟨98019, by rfl⟩ : syracuseStep 1045541 = 196039) (by norm_num)
theorem B816193 : Blo 618297 816193 := bbase (se 2 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 816193 = 612145) (by norm_num)
theorem B1569901 : Blo 618297 1569901 := bbase (se 3 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 1569901 = 588713) (by norm_num)
theorem B1766549 : Blo 618297 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B1045669 : Blo 618297 1045669 := bbase (se 4 (by rfl) ⟨98031, by rfl⟩ : syracuseStep 1045669 = 196063) (by norm_num)
theorem B783533 : Blo 618297 783533 := bbase (se 3 (by rfl) ⟨146912, by rfl⟩ : syracuseStep 783533 = 293825) (by norm_num)
theorem B1176781 : Blo 618297 1176781 := bbase (se 3 (by rfl) ⟨220646, by rfl⟩ : syracuseStep 1176781 = 441293) (by norm_num)
theorem B881885 : Blo 618297 881885 := bbase (se 3 (by rfl) ⟨165353, by rfl⟩ : syracuseStep 881885 = 330707) (by norm_num)
theorem B1570013 : Blo 618297 1570013 := bbase (se 3 (by rfl) ⟨294377, by rfl⟩ : syracuseStep 1570013 = 588755) (by norm_num)
theorem B783589 : Blo 618297 783589 := bbase (se 4 (by rfl) ⟨73461, by rfl⟩ : syracuseStep 783589 = 146923) (by norm_num)
theorem B1045757 : Blo 618297 1045757 := bbase (se 3 (by rfl) ⟨196079, by rfl⟩ : syracuseStep 1045757 = 392159) (by norm_num)
theorem B881965 : Blo 618297 881965 := bbase (se 3 (by rfl) ⟨165368, by rfl⟩ : syracuseStep 881965 = 330737) (by norm_num)
theorem B2094389 : Blo 618297 2094389 := bbase (se 5 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 2094389 = 196349) (by norm_num)
theorem B783685 : Blo 618297 783685 := bbase (se 4 (by rfl) ⟨73470, by rfl⟩ : syracuseStep 783685 = 146941) (by norm_num)
theorem B1176925 : Blo 618297 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B1045885 : Blo 618297 1045885 := bbase (se 3 (by rfl) ⟨196103, by rfl⟩ : syracuseStep 1045885 = 392207) (by norm_num)
theorem B1570205 : Blo 618297 1570205 := bbase (se 3 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 1570205 = 588827) (by norm_num)
theorem B882085 : Blo 618297 882085 := bbase (se 4 (by rfl) ⟨82695, by rfl⟩ : syracuseStep 882085 = 165391) (by norm_num)
theorem B1045973 : Blo 618297 1045973 := bbase (se 7 (by rfl) ⟨12257, by rfl⟩ : syracuseStep 1045973 = 24515) (by norm_num)
theorem B783857 : Blo 618297 783857 := bbase (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) (by norm_num)
theorem B1177085 : Blo 618297 1177085 := bbase (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) (by norm_num)
theorem B882181 : Blo 618297 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B783913 : Blo 618297 783913 := bbase (se 2 (by rfl) ⟨293967, by rfl⟩ : syracuseStep 783913 = 587935) (by norm_num)
theorem B1046101 : Blo 618297 1046101 := bbase (se 8 (by rfl) ⟨6129, by rfl⟩ : syracuseStep 1046101 = 12259) (by norm_num)
theorem B3143285 : Blo 618297 3143285 := bbase (se 5 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 3143285 = 294683) (by norm_num)
theorem B784009 : Blo 618297 784009 := bbase (se 2 (by rfl) ⟨294003, by rfl⟩ : syracuseStep 784009 = 588007) (by norm_num)
theorem B1177229 : Blo 618297 1177229 := bbase (se 3 (by rfl) ⟨220730, by rfl⟩ : syracuseStep 1177229 = 441461) (by norm_num)
theorem B1046189 : Blo 618297 1046189 := bbase (se 3 (by rfl) ⟨196160, by rfl⟩ : syracuseStep 1046189 = 392321) (by norm_num)
theorem B2094821 : Blo 618297 2094821 := bbase (se 4 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 2094821 = 392779) (by norm_num)
theorem B1570549 : Blo 618297 1570549 := bbase (se 5 (by rfl) ⟨73619, by rfl⟩ : syracuseStep 1570549 = 147239) (by norm_num)
theorem B1046317 : Blo 618297 1046317 := bbase (se 3 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 1046317 = 392369) (by norm_num)
theorem B784181 : Blo 618297 784181 := bbase (se 5 (by rfl) ⟨36758, by rfl⟩ : syracuseStep 784181 = 73517) (by norm_num)
theorem B1570661 : Blo 618297 1570661 := bbase (se 4 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 1570661 = 294499) (by norm_num)
theorem B784237 : Blo 618297 784237 := bbase (se 3 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 784237 = 294089) (by norm_num)
theorem B1046405 : Blo 618297 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B1177517 : Blo 618297 1177517 := bbase (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) (by norm_num)
theorem B1341389 : Blo 618297 1341389 := bbase (se 3 (by rfl) ⟨251510, by rfl⟩ : syracuseStep 1341389 = 503021) (by norm_num)
theorem B784333 : Blo 618297 784333 := bbase (se 3 (by rfl) ⟨147062, by rfl⟩ : syracuseStep 784333 = 294125) (by norm_num)
theorem B2357221 : Blo 618297 2357221 := bbase (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) (by norm_num)
theorem B882677 : Blo 618297 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B1046533 : Blo 618297 1046533 := bbase (se 4 (by rfl) ⟨98112, by rfl⟩ : syracuseStep 1046533 = 196225) (by norm_num)
theorem B1570853 : Blo 618297 1570853 := bbase (se 4 (by rfl) ⟨147267, by rfl⟩ : syracuseStep 1570853 = 294535) (by norm_num)
theorem B1177669 : Blo 618297 1177669 := bbase (se 4 (by rfl) ⟨110406, by rfl⟩ : syracuseStep 1177669 = 220813) (by norm_num)
theorem B4716629 : Blo 618297 4716629 := bbase (se 8 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 4716629 = 55273) (by norm_num)
theorem B1046621 : Blo 618297 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B1767541 : Blo 618297 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B784505 : Blo 618297 784505 := bbase (se 2 (by rfl) ⟨294189, by rfl⟩ : syracuseStep 784505 = 588379) (by norm_num)
theorem B718993 : Blo 618297 718993 := bbase (se 2 (by rfl) ⟨269622, by rfl⟩ : syracuseStep 718993 = 539245) (by norm_num)
theorem B2095253 : Blo 618297 2095253 := bbase (se 6 (by rfl) ⟨49107, by rfl⟩ : syracuseStep 2095253 = 98215) (by norm_num)
theorem B784561 : Blo 618297 784561 := bbase (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) (by norm_num)
theorem B1046749 : Blo 618297 1046749 := bbase (se 3 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 1046749 = 392531) (by norm_num)
theorem B2652421 : Blo 618297 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B784657 : Blo 618297 784657 := bbase (se 2 (by rfl) ⟨294246, by rfl⟩ : syracuseStep 784657 = 588493) (by norm_num)
theorem B2357525 : Blo 618297 2357525 := bbase (se 6 (by rfl) ⟨55254, by rfl⟩ : syracuseStep 2357525 = 110509) (by norm_num)
theorem B1046837 : Blo 618297 1046837 := bbase (se 5 (by rfl) ⟨49070, by rfl⟩ : syracuseStep 1046837 = 98141) (by norm_num)
theorem B1177973 : Blo 618297 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B3537269 : Blo 618297 3537269 := bbase (se 5 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 3537269 = 331619) (by norm_num)
theorem B1571197 : Blo 618297 1571197 := bbase (se 3 (by rfl) ⟨294599, by rfl⟩ : syracuseStep 1571197 = 589199) (by norm_num)
theorem B2521493 : Blo 618297 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B1046965 : Blo 618297 1046965 := bbase (se 5 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 1046965 = 98153) (by norm_num)
theorem B784829 : Blo 618297 784829 := bbase (se 3 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 784829 = 294311) (by norm_num)
theorem B1571309 : Blo 618297 1571309 := bbase (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) (by norm_num)
theorem B784885 : Blo 618297 784885 := bbase (se 5 (by rfl) ⟨36791, by rfl⟩ : syracuseStep 784885 = 73583) (by norm_num)
theorem B1047053 : Blo 618297 1047053 := bbase (se 3 (by rfl) ⟨196322, by rfl⟩ : syracuseStep 1047053 = 392645) (by norm_num)
theorem B883229 : Blo 618297 883229 := bbase (se 3 (by rfl) ⟨165605, by rfl⟩ : syracuseStep 883229 = 331211) (by norm_num)
theorem B2095685 : Blo 618297 2095685 := bbase (se 4 (by rfl) ⟨196470, by rfl⟩ : syracuseStep 2095685 = 392941) (by norm_num)
theorem B784981 : Blo 618297 784981 := bbase (se 8 (by rfl) ⟨4599, by rfl⟩ : syracuseStep 784981 = 9199) (by norm_num)
theorem B1047181 : Blo 618297 1047181 := bbase (se 3 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 1047181 = 392693) (by norm_num)
theorem B5307029 : Blo 618297 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B1571501 : Blo 618297 1571501 := bbase (se 3 (by rfl) ⟨294656, by rfl⟩ : syracuseStep 1571501 = 589313) (by norm_num)
theorem B1932005 : Blo 618297 1932005 := bbase (se 4 (by rfl) ⟨181125, by rfl⟩ : syracuseStep 1932005 = 362251) (by norm_num)
theorem B1047269 : Blo 618297 1047269 := bbase (se 4 (by rfl) ⟨98181, by rfl⟩ : syracuseStep 1047269 = 196363) (by norm_num)
theorem B785153 : Blo 618297 785153 := bbase (se 2 (by rfl) ⟨294432, by rfl⟩ : syracuseStep 785153 = 588865) (by norm_num)
theorem B785209 : Blo 618297 785209 := bbase (se 2 (by rfl) ⟨294453, by rfl⟩ : syracuseStep 785209 = 588907) (by norm_num)
theorem B1047397 : Blo 618297 1047397 := bbase (se 4 (by rfl) ⟨98193, by rfl⟩ : syracuseStep 1047397 = 196387) (by norm_num)
theorem B3144581 : Blo 618297 3144581 := bbase (se 4 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 3144581 = 589609) (by norm_num)
theorem B785305 : Blo 618297 785305 := bbase (se 2 (by rfl) ⟨294489, by rfl⟩ : syracuseStep 785305 = 588979) (by norm_num)
theorem B1047485 : Blo 618297 1047485 := bbase (se 3 (by rfl) ⟨196403, by rfl⟩ : syracuseStep 1047485 = 392807) (by norm_num)
theorem B2096117 : Blo 618297 2096117 := bbase (se 5 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 2096117 = 196511) (by norm_num)
theorem B1571845 : Blo 618297 1571845 := bbase (se 4 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 1571845 = 294721) (by norm_num)
theorem B1047613 : Blo 618297 1047613 := bbase (se 3 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 1047613 = 392855) (by norm_num)
theorem B785477 : Blo 618297 785477 := bbase (se 4 (by rfl) ⟨73638, by rfl⟩ : syracuseStep 785477 = 147277) (by norm_num)
theorem B1178725 : Blo 618297 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B1571957 : Blo 618297 1571957 := bbase (se 5 (by rfl) ⟨73685, by rfl⟩ : syracuseStep 1571957 = 147371) (by norm_num)
theorem B785533 : Blo 618297 785533 := bbase (se 3 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 785533 = 294575) (by norm_num)
theorem B1047701 : Blo 618297 1047701 := bbase (se 6 (by rfl) ⟨24555, by rfl⟩ : syracuseStep 1047701 = 49111) (by norm_num)
theorem B1768645 : Blo 618297 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B785629 : Blo 618297 785629 := bbase (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) (by norm_num)
theorem B1178869 : Blo 618297 1178869 := bbase (se 5 (by rfl) ⟨55259, by rfl⟩ : syracuseStep 1178869 = 110519) (by norm_num)
theorem B883981 : Blo 618297 883981 := bbase (se 3 (by rfl) ⟨165746, by rfl⟩ : syracuseStep 883981 = 331493) (by norm_num)
theorem B1047829 : Blo 618297 1047829 := bbase (se 6 (by rfl) ⟨24558, by rfl⟩ : syracuseStep 1047829 = 49117) (by norm_num)
theorem B1572149 : Blo 618297 1572149 := bbase (se 5 (by rfl) ⟨73694, by rfl⟩ : syracuseStep 1572149 = 147389) (by norm_num)
theorem B1047917 : Blo 618297 1047917 := bbase (se 3 (by rfl) ⟨196484, by rfl⟩ : syracuseStep 1047917 = 392969) (by norm_num)
theorem B785801 : Blo 618297 785801 := bbase (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) (by norm_num)
theorem B1179029 : Blo 618297 1179029 := bbase (se 6 (by rfl) ⟨27633, by rfl⟩ : syracuseStep 1179029 = 55267) (by norm_num)
theorem B2981285 : Blo 618297 2981285 := bbase (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) (by norm_num)
theorem B2096549 : Blo 618297 2096549 := bbase (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) (by norm_num)
theorem B785857 : Blo 618297 785857 := bbase (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) (by norm_num)
theorem B1048045 : Blo 618297 1048045 := bbase (se 3 (by rfl) ⟨196508, by rfl⟩ : syracuseStep 1048045 = 393017) (by norm_num)
theorem B785953 : Blo 618297 785953 := bbase (se 2 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 785953 = 589465) (by norm_num)
theorem B1179173 : Blo 618297 1179173 := bbase (se 4 (by rfl) ⟨110547, by rfl⟩ : syracuseStep 1179173 = 221095) (by norm_num)
theorem B1048133 : Blo 618297 1048133 := bbase (se 4 (by rfl) ⟨98262, by rfl⟩ : syracuseStep 1048133 = 196525) (by norm_num)
theorem B1572493 : Blo 618297 1572493 := bbase (se 3 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 1572493 = 589685) (by norm_num)
theorem B1048261 : Blo 618297 1048261 := bbase (se 4 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 1048261 = 196549) (by norm_num)
theorem B786125 : Blo 618297 786125 := bbase (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) (by norm_num)
theorem B1572605 : Blo 618297 1572605 := bbase (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) (by norm_num)
theorem B786181 : Blo 618297 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B1048349 : Blo 618297 1048349 := bbase (se 3 (by rfl) ⟨196565, by rfl⟩ : syracuseStep 1048349 = 393131) (by norm_num)
theorem B1179461 : Blo 618297 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B2096981 : Blo 618297 2096981 := bbase (se 9 (by rfl) ⟨6143, by rfl⟩ : syracuseStep 2096981 = 12287) (by norm_num)
theorem B786277 : Blo 618297 786277 := bbase (se 4 (by rfl) ⟨73713, by rfl⟩ : syracuseStep 786277 = 147427) (by norm_num)
theorem B1048477 : Blo 618297 1048477 := bbase (se 3 (by rfl) ⟨196589, by rfl⟩ : syracuseStep 1048477 = 393179) (by norm_num)
theorem B1343405 : Blo 618297 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B1572797 : Blo 618297 1572797 := bbase (se 3 (by rfl) ⟨294899, by rfl⟩ : syracuseStep 1572797 = 589799) (by norm_num)
theorem B5046229 : Blo 618297 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B1179613 : Blo 618297 1179613 := bbase (se 3 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 1179613 = 442355) (by norm_num)
theorem B1048565 : Blo 618297 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B1769489 : Blo 618297 1769489 := bstep (se 2 (by rfl) ⟨663558, by rfl⟩ : syracuseStep 1769489 = 1327117) B1327117
theorem B2097197 : Blo 618297 2097197 := bstep (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) B786449
theorem B1179697 : Blo 618297 1179697 := bstep (se 2 (by rfl) ⟨442386, by rfl⟩ : syracuseStep 1179697 = 884773) B884773
theorem B884801 : Blo 618297 884801 := bstep (se 2 (by rfl) ⟨331800, by rfl⟩ : syracuseStep 884801 = 663601) B663601
theorem B1048673 : Blo 618297 1048673 := bstep (se 2 (by rfl) ⟨393252, by rfl⟩ : syracuseStep 1048673 = 786505) B786505
theorem B2097251 : Blo 618297 2097251 := bstep (se 1 (by rfl) ⟨1572938, by rfl⟩ : syracuseStep 2097251 = 3145877) B3145877
theorem B884881 : Blo 618297 884881 := bstep (se 2 (by rfl) ⟨331830, by rfl⟩ : syracuseStep 884881 = 663661) B663661
theorem B786611 : Blo 618297 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B1048801 : Blo 618297 1048801 := bstep (se 2 (by rfl) ⟨393300, by rfl⟩ : syracuseStep 1048801 = 786601) B786601
theorem B1573091 : Blo 618297 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1048835 : Blo 618297 1048835 := bstep (se 1 (by rfl) ⟨786626, by rfl⟩ : syracuseStep 1048835 = 1573253) B1573253
theorem B1114435 : Blo 618297 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B2359651 : Blo 618297 2359651 := bstep (se 1 (by rfl) ⟨1769738, by rfl⟩ : syracuseStep 2359651 = 3539477) B3539477
theorem B2097521 : Blo 618297 2097521 := bstep (se 2 (by rfl) ⟨786570, by rfl⟩ : syracuseStep 2097521 = 1573141) B1573141
theorem B1048963 : Blo 618297 1048963 := bstep (se 1 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 1048963 = 1573445) B1573445
theorem B1573283 : Blo 618297 1573283 := bstep (se 1 (by rfl) ⟨1179962, by rfl⟩ : syracuseStep 1573283 = 2359925) B2359925
theorem B2425265 : Blo 618297 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B1180099 : Blo 618297 1180099 := bstep (se 1 (by rfl) ⟨885074, by rfl⟩ : syracuseStep 1180099 = 1770149) B1770149
theorem B1180145 : Blo 618297 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B3408389 : Blo 618297 3408389 := bstep (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) B639073
theorem B1049105 : Blo 618297 1049105 := bstep (se 2 (by rfl) ⟨393414, by rfl⟩ : syracuseStep 1049105 = 786829) B786829
theorem B1049233 : Blo 618297 1049233 := bstep (se 2 (by rfl) ⟨393462, by rfl⟩ : syracuseStep 1049233 = 786925) B786925
theorem B1049267 : Blo 618297 1049267 := bstep (se 1 (by rfl) ⟨786950, by rfl⟩ : syracuseStep 1049267 = 1573901) B1573901
theorem B3834629 : Blo 618297 3834629 := bstep (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) B718993
theorem B1114897 : Blo 618297 1114897 := bstep (se 2 (by rfl) ⟨418086, by rfl⟩ : syracuseStep 1114897 = 836173) B836173
theorem B1180433 : Blo 618297 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1770275 : Blo 618297 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B1049395 : Blo 618297 1049395 := bstep (se 1 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 1049395 = 1574093) B1574093
theorem B787315 : Blo 618297 787315 := bstep (se 1 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 787315 = 1180973) B1180973
theorem B2098061 : Blo 618297 2098061 := bstep (se 3 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 2098061 = 786773) B786773
theorem B2655139 : Blo 618297 2655139 := bstep (se 1 (by rfl) ⟨1991354, by rfl⟩ : syracuseStep 2655139 = 3982709) B3982709
theorem B885667 : Blo 618297 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B1049537 : Blo 618297 1049537 := bstep (se 2 (by rfl) ⟨393576, by rfl⟩ : syracuseStep 1049537 = 787153) B787153
theorem B2098115 : Blo 618297 2098115 := bstep (se 1 (by rfl) ⟨1573586, by rfl⟩ : syracuseStep 2098115 = 3147173) B3147173
theorem B787411 : Blo 618297 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B1049665 : Blo 618297 1049665 := bstep (se 2 (by rfl) ⟨393624, by rfl⟩ : syracuseStep 1049665 = 787249) B787249
theorem B1049699 : Blo 618297 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B1770605 : Blo 618297 1770605 := bstep (se 3 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 1770605 = 663977) B663977
theorem B3867761 : Blo 618297 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B2393201 : Blo 618297 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B1770673 : Blo 618297 1770673 := bstep (se 2 (by rfl) ⟨664002, by rfl⟩ : syracuseStep 1770673 = 1328005) B1328005
theorem B2098385 : Blo 618297 2098385 := bstep (se 2 (by rfl) ⟨786894, by rfl⟩ : syracuseStep 2098385 = 1573789) B1573789
theorem B1049827 : Blo 618297 1049827 := bstep (se 1 (by rfl) ⟨787370, by rfl⟩ : syracuseStep 1049827 = 1574741) B1574741
theorem B1672433 : Blo 618297 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B1410385 : Blo 618297 1410385 := bstep (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) B1057789
theorem B1574225 : Blo 618297 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B7046513 : Blo 618297 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B1049969 : Blo 618297 1049969 := bstep (se 2 (by rfl) ⟨393738, by rfl⟩ : syracuseStep 1049969 = 787477) B787477
theorem B1574275 : Blo 618297 1574275 := bstep (se 1 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 1574275 = 2361413) B2361413
theorem B1770947 : Blo 618297 1770947 := bstep (se 1 (by rfl) ⟨1328210, by rfl⟩ : syracuseStep 1770947 = 2656421) B2656421
theorem B1181155 : Blo 618297 1181155 := bstep (se 1 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 1181155 = 1771733) B1771733
theorem B1050097 : Blo 618297 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B1574417 : Blo 618297 1574417 := bstep (se 2 (by rfl) ⟨590406, by rfl⟩ : syracuseStep 1574417 = 1180813) B1180813
theorem B2098925 : Blo 618297 2098925 := bstep (se 3 (by rfl) ⟨393548, by rfl⟩ : syracuseStep 2098925 = 787097) B787097
theorem B2098979 : Blo 618297 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B2099249 : Blo 618297 2099249 := bstep (se 2 (by rfl) ⟨787218, by rfl⟩ : syracuseStep 2099249 = 1574437) B1574437
theorem B3344561 : Blo 618297 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B1771789 : Blo 618297 1771789 := bstep (se 3 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 1771789 = 664421) B664421
theorem B2754929 : Blo 618297 2754929 := bstep (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) B2066197
theorem B3148145 : Blo 618297 3148145 := bstep (se 2 (by rfl) ⟨1180554, by rfl⟩ : syracuseStep 3148145 = 2361109) B2361109
theorem B1771949 : Blo 618297 1771949 := bstep (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) B664481
theorem B2361869 : Blo 618297 2361869 := bstep (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) B885701
theorem B2230861 : Blo 618297 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B2099789 : Blo 618297 2099789 := bstep (se 3 (by rfl) ⟨393710, by rfl⟩ : syracuseStep 2099789 = 787421) B787421
theorem B2099843 : Blo 618297 2099843 := bstep (se 1 (by rfl) ⟨1574882, by rfl⟩ : syracuseStep 2099843 = 3149765) B3149765
theorem B2657137 : Blo 618297 2657137 := bstep (se 2 (by rfl) ⟨996426, by rfl⟩ : syracuseStep 2657137 = 1992853) B1992853
theorem B2100113 : Blo 618297 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B1608707 : Blo 618297 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B5016773 : Blo 618297 5016773 := bstep (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) B940645
theorem B45321443 : Blo 618297 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B2985187 : Blo 618297 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B3149603 : Blo 618297 3149603 := bstep (se 1 (by rfl) ⟨2362202, by rfl⟩ : syracuseStep 3149603 = 4724405) B4724405
theorem B3968995 : Blo 618297 3968995 := bstep (se 1 (by rfl) ⟨2976746, by rfl⟩ : syracuseStep 3968995 = 5953493) B5953493
theorem B3346595 : Blo 618297 3346595 := bstep (se 1 (by rfl) ⟨2509946, by rfl⟩ : syracuseStep 3346595 = 5019893) B5019893
theorem B15078257 : Blo 618297 15078257 := bstep (se 2 (by rfl) ⟨5654346, by rfl⟩ : syracuseStep 15078257 = 11308693) B11308693
theorem B1676323 : Blo 618297 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B3970225 : Blo 618297 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B1676497 : Blo 618297 1676497 := bstep (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) B1257373
theorem B1119619 : Blo 618297 1119619 := bstep (se 1 (by rfl) ⟨839714, by rfl⟩ : syracuseStep 1119619 = 1679429) B1679429
theorem B1119683 : Blo 618297 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B12719729 : Blo 618297 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B1119971 : Blo 618297 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B1120081 : Blo 618297 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B661619 : Blo 618297 661619 := bstep (se 1 (by rfl) ⟨496214, by rfl⟩ : syracuseStep 661619 = 992429) B992429
theorem B4463045 : Blo 618297 4463045 := bstep (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) B836821
theorem B629299 : Blo 618297 629299 := bstep (se 1 (by rfl) ⟨471974, by rfl⟩ : syracuseStep 629299 = 943949) B943949
theorem B1088257 : Blo 618297 1088257 := bstep (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) B816193
theorem B2038733 : Blo 618297 2038733 := bstep (se 3 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 2038733 = 764525) B764525
theorem B1121297 : Blo 618297 1121297 := bstep (se 2 (by rfl) ⟨420486, by rfl⟩ : syracuseStep 1121297 = 840973) B840973
theorem B2825293 : Blo 618297 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B662627 : Blo 618297 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B1678477 : Blo 618297 1678477 := bstep (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) B629429
theorem B990481 : Blo 618297 990481 := bstep (se 2 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 990481 = 742861) B742861
theorem B695587 : Blo 618297 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B695731 : Blo 618297 695731 := bstep (se 1 (by rfl) ⟨521798, by rfl⟩ : syracuseStep 695731 = 1043597) B1043597
theorem B695875 : Blo 618297 695875 := bstep (se 1 (by rfl) ⟨521906, by rfl⟩ : syracuseStep 695875 = 1043813) B1043813
theorem B696019 : Blo 618297 696019 := bstep (se 1 (by rfl) ⟨522014, by rfl⟩ : syracuseStep 696019 = 1044029) B1044029
theorem B696163 : Blo 618297 696163 := bstep (se 1 (by rfl) ⟨522122, by rfl⟩ : syracuseStep 696163 = 1044245) B1044245
theorem B991121 : Blo 618297 991121 := bstep (se 2 (by rfl) ⟨371670, by rfl⟩ : syracuseStep 991121 = 743341) B743341
theorem B1679309 : Blo 618297 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B696307 : Blo 618297 696307 := bstep (se 1 (by rfl) ⟨522230, by rfl⟩ : syracuseStep 696307 = 1044461) B1044461
theorem B1679437 : Blo 618297 1679437 := bstep (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) B629789
theorem B2826353 : Blo 618297 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B696451 : Blo 618297 696451 := bstep (se 1 (by rfl) ⟨522338, by rfl⟩ : syracuseStep 696451 = 1044677) B1044677
theorem B696595 : Blo 618297 696595 := bstep (se 1 (by rfl) ⟨522446, by rfl⟩ : syracuseStep 696595 = 1044893) B1044893
theorem B696739 : Blo 618297 696739 := bstep (se 1 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 696739 = 1045109) B1045109
theorem B696883 : Blo 618297 696883 := bstep (se 1 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 696883 = 1045325) B1045325
theorem B664195 : Blo 618297 664195 := bstep (se 1 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 664195 = 996293) B996293
theorem B697027 : Blo 618297 697027 := bstep (se 1 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 697027 = 1045541) B1045541
theorem B2237233 : Blo 618297 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B697171 : Blo 618297 697171 := bstep (se 1 (by rfl) ⟨522878, by rfl⟩ : syracuseStep 697171 = 1045757) B1045757
theorem B3974021 : Blo 618297 3974021 := bstep (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) B745129
theorem B697315 : Blo 618297 697315 := bstep (se 1 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 697315 = 1045973) B1045973
theorem B697459 : Blo 618297 697459 := bstep (se 1 (by rfl) ⟨523094, by rfl⟩ : syracuseStep 697459 = 1046189) B1046189
theorem B795763 : Blo 618297 795763 := bstep (se 1 (by rfl) ⟨596822, by rfl⟩ : syracuseStep 795763 = 1193645) B1193645
theorem B697603 : Blo 618297 697603 := bstep (se 1 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 697603 = 1046405) B1046405
theorem B992531 : Blo 618297 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B894259 : Blo 618297 894259 := bstep (se 1 (by rfl) ⟨670694, by rfl⟩ : syracuseStep 894259 = 1341389) B1341389
theorem B992659 : Blo 618297 992659 := bstep (se 1 (by rfl) ⟨744494, by rfl⟩ : syracuseStep 992659 = 1488989) B1488989
theorem B697747 : Blo 618297 697747 := bstep (se 1 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 697747 = 1046621) B1046621
theorem B697891 : Blo 618297 697891 := bstep (se 1 (by rfl) ⟨523418, by rfl⟩ : syracuseStep 697891 = 1046837) B1046837
theorem B48342581 : Blo 618297 48342581 := bstep (se 5 (by rfl) ⟨2266058, by rfl⟩ : syracuseStep 48342581 = 4532117) B4532117
theorem B1680995 : Blo 618297 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B698035 : Blo 618297 698035 := bstep (se 1 (by rfl) ⟨523526, by rfl⟩ : syracuseStep 698035 = 1047053) B1047053
theorem B927473 : Blo 618297 927473 := bstep (se 2 (by rfl) ⟨347802, by rfl⟩ : syracuseStep 927473 = 695605) B695605
theorem B927491 : Blo 618297 927491 := bstep (se 1 (by rfl) ⟨695618, by rfl⟩ : syracuseStep 927491 = 1391237) B1391237
theorem B927521 : Blo 618297 927521 := bstep (se 2 (by rfl) ⟨347820, by rfl⟩ : syracuseStep 927521 = 695641) B695641
theorem B927539 : Blo 618297 927539 := bstep (se 1 (by rfl) ⟨695654, by rfl⟩ : syracuseStep 927539 = 1391309) B1391309
theorem B1288003 : Blo 618297 1288003 := bstep (se 1 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 1288003 = 1932005) B1932005
theorem B698179 : Blo 618297 698179 := bstep (se 1 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 698179 = 1047269) B1047269
theorem B927569 : Blo 618297 927569 := bstep (se 2 (by rfl) ⟨347838, by rfl⟩ : syracuseStep 927569 = 695677) B695677
theorem B927587 : Blo 618297 927587 := bstep (se 1 (by rfl) ⟨695690, by rfl⟩ : syracuseStep 927587 = 1391381) B1391381
theorem B927617 : Blo 618297 927617 := bstep (se 2 (by rfl) ⟨347856, by rfl⟩ : syracuseStep 927617 = 695713) B695713
theorem B927635 : Blo 618297 927635 := bstep (se 1 (by rfl) ⟨695726, by rfl⟩ : syracuseStep 927635 = 1391453) B1391453
theorem B1255331 : Blo 618297 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B927665 : Blo 618297 927665 := bstep (se 2 (by rfl) ⟨347874, by rfl⟩ : syracuseStep 927665 = 695749) B695749
theorem B993217 : Blo 618297 993217 := bstep (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) B744913
theorem B927683 : Blo 618297 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B698323 : Blo 618297 698323 := bstep (se 1 (by rfl) ⟨523742, by rfl⟩ : syracuseStep 698323 = 1047485) B1047485
theorem B927713 : Blo 618297 927713 := bstep (se 2 (by rfl) ⟨347892, by rfl⟩ : syracuseStep 927713 = 695785) B695785
theorem B927731 : Blo 618297 927731 := bstep (se 1 (by rfl) ⟨695798, by rfl⟩ : syracuseStep 927731 = 1391597) B1391597
theorem B927761 : Blo 618297 927761 := bstep (se 2 (by rfl) ⟨347910, by rfl⟩ : syracuseStep 927761 = 695821) B695821
theorem B927779 : Blo 618297 927779 := bstep (se 1 (by rfl) ⟨695834, by rfl⟩ : syracuseStep 927779 = 1391669) B1391669
theorem B927809 : Blo 618297 927809 := bstep (se 2 (by rfl) ⟨347928, by rfl⟩ : syracuseStep 927809 = 695857) B695857
theorem B927827 : Blo 618297 927827 := bstep (se 1 (by rfl) ⟨695870, by rfl⟩ : syracuseStep 927827 = 1391741) B1391741
theorem B698467 : Blo 618297 698467 := bstep (se 1 (by rfl) ⟨523850, by rfl⟩ : syracuseStep 698467 = 1047701) B1047701
theorem B927857 : Blo 618297 927857 := bstep (se 2 (by rfl) ⟨347946, by rfl⟩ : syracuseStep 927857 = 695893) B695893
theorem B927875 : Blo 618297 927875 := bstep (se 1 (by rfl) ⟨695906, by rfl⟩ : syracuseStep 927875 = 1391813) B1391813
theorem B927905 : Blo 618297 927905 := bstep (se 2 (by rfl) ⟨347964, by rfl⟩ : syracuseStep 927905 = 695929) B695929
theorem B927923 : Blo 618297 927923 := bstep (se 1 (by rfl) ⟨695942, by rfl⟩ : syracuseStep 927923 = 1391885) B1391885
theorem B927953 : Blo 618297 927953 := bstep (se 2 (by rfl) ⟨347982, by rfl⟩ : syracuseStep 927953 = 695965) B695965
theorem B927971 : Blo 618297 927971 := bstep (se 1 (by rfl) ⟨695978, by rfl⟩ : syracuseStep 927971 = 1391957) B1391957
theorem B698611 : Blo 618297 698611 := bstep (se 1 (by rfl) ⟨523958, by rfl⟩ : syracuseStep 698611 = 1047917) B1047917
theorem B928001 : Blo 618297 928001 := bstep (se 2 (by rfl) ⟨348000, by rfl⟩ : syracuseStep 928001 = 696001) B696001
theorem B928019 : Blo 618297 928019 := bstep (se 1 (by rfl) ⟨696014, by rfl⟩ : syracuseStep 928019 = 1392029) B1392029
theorem B928049 : Blo 618297 928049 := bstep (se 2 (by rfl) ⟨348018, by rfl⟩ : syracuseStep 928049 = 696037) B696037
theorem B928067 : Blo 618297 928067 := bstep (se 1 (by rfl) ⟨696050, by rfl⟩ : syracuseStep 928067 = 1392101) B1392101
theorem B928097 : Blo 618297 928097 := bstep (se 2 (by rfl) ⟨348036, by rfl⟩ : syracuseStep 928097 = 696073) B696073
theorem B928115 : Blo 618297 928115 := bstep (se 1 (by rfl) ⟨696086, by rfl⟩ : syracuseStep 928115 = 1392173) B1392173
theorem B698755 : Blo 618297 698755 := bstep (se 1 (by rfl) ⟨524066, by rfl⟩ : syracuseStep 698755 = 1048133) B1048133
theorem B928145 : Blo 618297 928145 := bstep (se 2 (by rfl) ⟨348054, by rfl⟩ : syracuseStep 928145 = 696109) B696109
theorem B928163 : Blo 618297 928163 := bstep (se 1 (by rfl) ⟨696122, by rfl⟩ : syracuseStep 928163 = 1392245) B1392245
theorem B1321393 : Blo 618297 1321393 := bstep (se 2 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 1321393 = 991045) B991045
theorem B928193 : Blo 618297 928193 := bstep (se 2 (by rfl) ⟨348072, by rfl⟩ : syracuseStep 928193 = 696145) B696145
theorem B3582413 : Blo 618297 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B928211 : Blo 618297 928211 := bstep (se 1 (by rfl) ⟨696158, by rfl⟩ : syracuseStep 928211 = 1392317) B1392317
theorem B928241 : Blo 618297 928241 := bstep (se 2 (by rfl) ⟨348090, by rfl⟩ : syracuseStep 928241 = 696181) B696181
theorem B928259 : Blo 618297 928259 := bstep (se 1 (by rfl) ⟨696194, by rfl⟩ : syracuseStep 928259 = 1392389) B1392389
theorem B1681937 : Blo 618297 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B698899 : Blo 618297 698899 := bstep (se 1 (by rfl) ⟨524174, by rfl⟩ : syracuseStep 698899 = 1048349) B1048349
theorem B928289 : Blo 618297 928289 := bstep (se 2 (by rfl) ⟨348108, by rfl⟩ : syracuseStep 928289 = 696217) B696217
theorem B928307 : Blo 618297 928307 := bstep (se 1 (by rfl) ⟨696230, by rfl⟩ : syracuseStep 928307 = 1392461) B1392461
theorem B1256003 : Blo 618297 1256003 := bstep (se 1 (by rfl) ⟨942002, by rfl⟩ : syracuseStep 1256003 = 1884005) B1884005
theorem B928337 : Blo 618297 928337 := bstep (se 2 (by rfl) ⟨348126, by rfl⟩ : syracuseStep 928337 = 696253) B696253
theorem B993889 : Blo 618297 993889 := bstep (se 2 (by rfl) ⟨372708, by rfl⟩ : syracuseStep 993889 = 745417) B745417
theorem B928355 : Blo 618297 928355 := bstep (se 1 (by rfl) ⟨696266, by rfl⟩ : syracuseStep 928355 = 1392533) B1392533
theorem B6728305 : Blo 618297 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B928385 : Blo 618297 928385 := bstep (se 2 (by rfl) ⟨348144, by rfl⟩ : syracuseStep 928385 = 696289) B696289
theorem B928403 : Blo 618297 928403 := bstep (se 1 (by rfl) ⟨696302, by rfl⟩ : syracuseStep 928403 = 1392605) B1392605
theorem B699043 : Blo 618297 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B928433 : Blo 618297 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B928451 : Blo 618297 928451 := bstep (se 1 (by rfl) ⟨696338, by rfl⟩ : syracuseStep 928451 = 1392677) B1392677
theorem B928481 : Blo 618297 928481 := bstep (se 2 (by rfl) ⟨348180, by rfl⟩ : syracuseStep 928481 = 696361) B696361
theorem B928499 : Blo 618297 928499 := bstep (se 1 (by rfl) ⟨696374, by rfl⟩ : syracuseStep 928499 = 1392749) B1392749
theorem B928529 : Blo 618297 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B928547 : Blo 618297 928547 := bstep (se 1 (by rfl) ⟨696410, by rfl⟩ : syracuseStep 928547 = 1392821) B1392821
theorem B699187 : Blo 618297 699187 := bstep (se 1 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 699187 = 1048781) B1048781
theorem B928577 : Blo 618297 928577 := bstep (se 2 (by rfl) ⟨348216, by rfl⟩ : syracuseStep 928577 = 696433) B696433
theorem B928595 : Blo 618297 928595 := bstep (se 1 (by rfl) ⟨696446, by rfl⟩ : syracuseStep 928595 = 1392893) B1392893
theorem B928625 : Blo 618297 928625 := bstep (se 2 (by rfl) ⟨348234, by rfl⟩ : syracuseStep 928625 = 696469) B696469
theorem B928643 : Blo 618297 928643 := bstep (se 1 (by rfl) ⟨696482, by rfl⟩ : syracuseStep 928643 = 1392965) B1392965
theorem B928673 : Blo 618297 928673 := bstep (se 2 (by rfl) ⟨348252, by rfl⟩ : syracuseStep 928673 = 696505) B696505
theorem B928691 : Blo 618297 928691 := bstep (se 1 (by rfl) ⟨696518, by rfl⟩ : syracuseStep 928691 = 1393037) B1393037
theorem B699331 : Blo 618297 699331 := bstep (se 1 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 699331 = 1048997) B1048997
theorem B928721 : Blo 618297 928721 := bstep (se 2 (by rfl) ⟨348270, by rfl⟩ : syracuseStep 928721 = 696541) B696541
theorem B1256401 : Blo 618297 1256401 := bstep (se 2 (by rfl) ⟨471150, by rfl⟩ : syracuseStep 1256401 = 942301) B942301
theorem B928739 : Blo 618297 928739 := bstep (se 1 (by rfl) ⟨696554, by rfl⟩ : syracuseStep 928739 = 1393109) B1393109
theorem B3582947 : Blo 618297 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B928769 : Blo 618297 928769 := bstep (se 2 (by rfl) ⟨348288, by rfl⟩ : syracuseStep 928769 = 696577) B696577
theorem B1256465 : Blo 618297 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B928787 : Blo 618297 928787 := bstep (se 1 (by rfl) ⟨696590, by rfl⟩ : syracuseStep 928787 = 1393181) B1393181
theorem B928817 : Blo 618297 928817 := bstep (se 2 (by rfl) ⟨348306, by rfl⟩ : syracuseStep 928817 = 696613) B696613
theorem B928835 : Blo 618297 928835 := bstep (se 1 (by rfl) ⟨696626, by rfl⟩ : syracuseStep 928835 = 1393253) B1393253
theorem B699475 : Blo 618297 699475 := bstep (se 1 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 699475 = 1049213) B1049213
theorem B928865 : Blo 618297 928865 := bstep (se 2 (by rfl) ⟨348324, by rfl⟩ : syracuseStep 928865 = 696649) B696649
theorem B928883 : Blo 618297 928883 := bstep (se 1 (by rfl) ⟨696662, by rfl⟩ : syracuseStep 928883 = 1393325) B1393325
theorem B928913 : Blo 618297 928913 := bstep (se 2 (by rfl) ⟨348342, by rfl⟩ : syracuseStep 928913 = 696685) B696685
theorem B928931 : Blo 618297 928931 := bstep (se 1 (by rfl) ⟨696698, by rfl⟩ : syracuseStep 928931 = 1393397) B1393397
theorem B928961 : Blo 618297 928961 := bstep (se 2 (by rfl) ⟨348360, by rfl⟩ : syracuseStep 928961 = 696721) B696721
theorem B928979 : Blo 618297 928979 := bstep (se 1 (by rfl) ⟨696734, by rfl⟩ : syracuseStep 928979 = 1393469) B1393469
theorem B699619 : Blo 618297 699619 := bstep (se 1 (by rfl) ⟨524714, by rfl⟩ : syracuseStep 699619 = 1049429) B1049429
theorem B929009 : Blo 618297 929009 := bstep (se 2 (by rfl) ⟨348378, by rfl⟩ : syracuseStep 929009 = 696757) B696757
theorem B929027 : Blo 618297 929027 := bstep (se 1 (by rfl) ⟨696770, by rfl⟩ : syracuseStep 929027 = 1393541) B1393541
theorem B929057 : Blo 618297 929057 := bstep (se 2 (by rfl) ⟨348396, by rfl⟩ : syracuseStep 929057 = 696793) B696793
theorem B929075 : Blo 618297 929075 := bstep (se 1 (by rfl) ⟨696806, by rfl⟩ : syracuseStep 929075 = 1393613) B1393613
theorem B929105 : Blo 618297 929105 := bstep (se 2 (by rfl) ⟨348414, by rfl⟩ : syracuseStep 929105 = 696829) B696829
theorem B929123 : Blo 618297 929123 := bstep (se 1 (by rfl) ⟨696842, by rfl⟩ : syracuseStep 929123 = 1393685) B1393685
theorem B699763 : Blo 618297 699763 := bstep (se 1 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 699763 = 1049645) B1049645
theorem B929153 : Blo 618297 929153 := bstep (se 2 (by rfl) ⟨348432, by rfl⟩ : syracuseStep 929153 = 696865) B696865
theorem B929171 : Blo 618297 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B929201 : Blo 618297 929201 := bstep (se 2 (by rfl) ⟨348450, by rfl⟩ : syracuseStep 929201 = 696901) B696901
theorem B929219 : Blo 618297 929219 := bstep (se 1 (by rfl) ⟨696914, by rfl⟩ : syracuseStep 929219 = 1393829) B1393829
theorem B1486289 : Blo 618297 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B929249 : Blo 618297 929249 := bstep (se 2 (by rfl) ⟨348468, by rfl⟩ : syracuseStep 929249 = 696937) B696937
theorem B929267 : Blo 618297 929267 := bstep (se 1 (by rfl) ⟨696950, by rfl⟩ : syracuseStep 929267 = 1393901) B1393901
theorem B699907 : Blo 618297 699907 := bstep (se 1 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 699907 = 1049861) B1049861
theorem B929297 : Blo 618297 929297 := bstep (se 2 (by rfl) ⟨348486, by rfl⟩ : syracuseStep 929297 = 696973) B696973
theorem B929315 : Blo 618297 929315 := bstep (se 1 (by rfl) ⟨696986, by rfl⟩ : syracuseStep 929315 = 1393973) B1393973
theorem B929345 : Blo 618297 929345 := bstep (se 2 (by rfl) ⟨348504, by rfl⟩ : syracuseStep 929345 = 697009) B697009
theorem B929363 : Blo 618297 929363 := bstep (se 1 (by rfl) ⟨697022, by rfl⟩ : syracuseStep 929363 = 1394045) B1394045
theorem B4763249 : Blo 618297 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B929393 : Blo 618297 929393 := bstep (se 2 (by rfl) ⟨348522, by rfl⟩ : syracuseStep 929393 = 697045) B697045
theorem B929411 : Blo 618297 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B1060499 : Blo 618297 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B700051 : Blo 618297 700051 := bstep (se 1 (by rfl) ⟨525038, by rfl⟩ : syracuseStep 700051 = 1050077) B1050077
theorem B929441 : Blo 618297 929441 := bstep (se 2 (by rfl) ⟨348540, by rfl⟩ : syracuseStep 929441 = 697081) B697081
theorem B994979 : Blo 618297 994979 := bstep (se 1 (by rfl) ⟨746234, by rfl⟩ : syracuseStep 994979 = 1492469) B1492469
theorem B929459 : Blo 618297 929459 := bstep (se 1 (by rfl) ⟨697094, by rfl⟩ : syracuseStep 929459 = 1394189) B1394189
theorem B929489 : Blo 618297 929489 := bstep (se 2 (by rfl) ⟨348558, by rfl⟩ : syracuseStep 929489 = 697117) B697117
theorem B929507 : Blo 618297 929507 := bstep (se 1 (by rfl) ⟨697130, by rfl⟩ : syracuseStep 929507 = 1394261) B1394261
theorem B5746403 : Blo 618297 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B929537 : Blo 618297 929537 := bstep (se 2 (by rfl) ⟨348576, by rfl⟩ : syracuseStep 929537 = 697153) B697153
theorem B929555 : Blo 618297 929555 := bstep (se 1 (by rfl) ⟨697166, by rfl⟩ : syracuseStep 929555 = 1394333) B1394333
theorem B929585 : Blo 618297 929585 := bstep (se 2 (by rfl) ⟨348594, by rfl⟩ : syracuseStep 929585 = 697189) B697189
theorem B929603 : Blo 618297 929603 := bstep (se 1 (by rfl) ⟨697202, by rfl⟩ : syracuseStep 929603 = 1394405) B1394405
theorem B929633 : Blo 618297 929633 := bstep (se 2 (by rfl) ⟨348612, by rfl⟩ : syracuseStep 929633 = 697225) B697225
theorem B929651 : Blo 618297 929651 := bstep (se 1 (by rfl) ⟨697238, by rfl⟩ : syracuseStep 929651 = 1394477) B1394477
theorem B929681 : Blo 618297 929681 := bstep (se 2 (by rfl) ⟨348630, by rfl⟩ : syracuseStep 929681 = 697261) B697261
theorem B929699 : Blo 618297 929699 := bstep (se 1 (by rfl) ⟨697274, by rfl⟩ : syracuseStep 929699 = 1394549) B1394549
theorem B929729 : Blo 618297 929729 := bstep (se 2 (by rfl) ⟨348648, by rfl⟩ : syracuseStep 929729 = 697297) B697297
theorem B929747 : Blo 618297 929747 := bstep (se 1 (by rfl) ⟨697310, by rfl⟩ : syracuseStep 929747 = 1394621) B1394621
theorem B929777 : Blo 618297 929777 := bstep (se 2 (by rfl) ⟨348666, by rfl⟩ : syracuseStep 929777 = 697333) B697333
theorem B929795 : Blo 618297 929795 := bstep (se 1 (by rfl) ⟨697346, by rfl⟩ : syracuseStep 929795 = 1394693) B1394693
theorem B929825 : Blo 618297 929825 := bstep (se 2 (by rfl) ⟨348684, by rfl⟩ : syracuseStep 929825 = 697369) B697369
theorem B929843 : Blo 618297 929843 := bstep (se 1 (by rfl) ⟨697382, by rfl⟩ : syracuseStep 929843 = 1394765) B1394765
theorem B929873 : Blo 618297 929873 := bstep (se 2 (by rfl) ⟨348702, by rfl⟩ : syracuseStep 929873 = 697405) B697405
theorem B929891 : Blo 618297 929891 := bstep (se 1 (by rfl) ⟨697418, by rfl⟩ : syracuseStep 929891 = 1394837) B1394837
theorem B929921 : Blo 618297 929921 := bstep (se 2 (by rfl) ⟨348720, by rfl⟩ : syracuseStep 929921 = 697441) B697441
theorem B929939 : Blo 618297 929939 := bstep (se 1 (by rfl) ⟨697454, by rfl⟩ : syracuseStep 929939 = 1394909) B1394909
theorem B929969 : Blo 618297 929969 := bstep (se 2 (by rfl) ⟨348738, by rfl⟩ : syracuseStep 929969 = 697477) B697477
theorem B929987 : Blo 618297 929987 := bstep (se 1 (by rfl) ⟨697490, by rfl⟩ : syracuseStep 929987 = 1394981) B1394981
theorem B930017 : Blo 618297 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B930035 : Blo 618297 930035 := bstep (se 1 (by rfl) ⟨697526, by rfl⟩ : syracuseStep 930035 = 1395053) B1395053
theorem B930065 : Blo 618297 930065 := bstep (se 2 (by rfl) ⟨348774, by rfl⟩ : syracuseStep 930065 = 697549) B697549
theorem B930083 : Blo 618297 930083 := bstep (se 1 (by rfl) ⟨697562, by rfl⟩ : syracuseStep 930083 = 1395125) B1395125
theorem B930113 : Blo 618297 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B930131 : Blo 618297 930131 := bstep (se 1 (by rfl) ⟨697598, by rfl⟩ : syracuseStep 930131 = 1395197) B1395197
theorem B930161 : Blo 618297 930161 := bstep (se 2 (by rfl) ⟨348810, by rfl⟩ : syracuseStep 930161 = 697621) B697621
theorem B3977585 : Blo 618297 3977585 := bstep (se 2 (by rfl) ⟨1491594, by rfl⟩ : syracuseStep 3977585 = 2983189) B2983189
theorem B930179 : Blo 618297 930179 := bstep (se 1 (by rfl) ⟨697634, by rfl⟩ : syracuseStep 930179 = 1395269) B1395269
theorem B930209 : Blo 618297 930209 := bstep (se 2 (by rfl) ⟨348828, by rfl⟩ : syracuseStep 930209 = 697657) B697657
theorem B930227 : Blo 618297 930227 := bstep (se 1 (by rfl) ⟨697670, by rfl⟩ : syracuseStep 930227 = 1395341) B1395341
theorem B930257 : Blo 618297 930257 := bstep (se 2 (by rfl) ⟨348846, by rfl⟩ : syracuseStep 930257 = 697693) B697693
theorem B930275 : Blo 618297 930275 := bstep (se 1 (by rfl) ⟨697706, by rfl⟩ : syracuseStep 930275 = 1395413) B1395413
theorem B930305 : Blo 618297 930305 := bstep (se 2 (by rfl) ⟨348864, by rfl⟩ : syracuseStep 930305 = 697729) B697729
theorem B2241037 : Blo 618297 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B930323 : Blo 618297 930323 := bstep (se 1 (by rfl) ⟨697742, by rfl⟩ : syracuseStep 930323 = 1395485) B1395485
theorem B930353 : Blo 618297 930353 := bstep (se 2 (by rfl) ⟨348882, by rfl⟩ : syracuseStep 930353 = 697765) B697765
theorem B930371 : Blo 618297 930371 := bstep (se 1 (by rfl) ⟨697778, by rfl⟩ : syracuseStep 930371 = 1395557) B1395557
theorem B930401 : Blo 618297 930401 := bstep (se 2 (by rfl) ⟨348900, by rfl⟩ : syracuseStep 930401 = 697801) B697801
theorem B930419 : Blo 618297 930419 := bstep (se 1 (by rfl) ⟨697814, by rfl⟩ : syracuseStep 930419 = 1395629) B1395629
theorem B5026445 : Blo 618297 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B930449 : Blo 618297 930449 := bstep (se 2 (by rfl) ⟨348918, by rfl⟩ : syracuseStep 930449 = 697837) B697837
theorem B930467 : Blo 618297 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B930497 : Blo 618297 930497 := bstep (se 2 (by rfl) ⟨348936, by rfl⟩ : syracuseStep 930497 = 697873) B697873
theorem B930515 : Blo 618297 930515 := bstep (se 1 (by rfl) ⟨697886, by rfl⟩ : syracuseStep 930515 = 1395773) B1395773
theorem B930545 : Blo 618297 930545 := bstep (se 2 (by rfl) ⟨348954, by rfl⟩ : syracuseStep 930545 = 697909) B697909
theorem B930563 : Blo 618297 930563 := bstep (se 1 (by rfl) ⟨697922, by rfl⟩ : syracuseStep 930563 = 1395845) B1395845
theorem B930593 : Blo 618297 930593 := bstep (se 2 (by rfl) ⟨348972, by rfl⟩ : syracuseStep 930593 = 697945) B697945
theorem B930611 : Blo 618297 930611 := bstep (se 1 (by rfl) ⟨697958, by rfl⟩ : syracuseStep 930611 = 1395917) B1395917
theorem B930641 : Blo 618297 930641 := bstep (se 2 (by rfl) ⟨348990, by rfl⟩ : syracuseStep 930641 = 697981) B697981
theorem B930659 : Blo 618297 930659 := bstep (se 1 (by rfl) ⟨697994, by rfl⟩ : syracuseStep 930659 = 1395989) B1395989
theorem B930689 : Blo 618297 930689 := bstep (se 2 (by rfl) ⟨349008, by rfl⟩ : syracuseStep 930689 = 698017) B698017
theorem B930707 : Blo 618297 930707 := bstep (se 1 (by rfl) ⟨698030, by rfl⟩ : syracuseStep 930707 = 1396061) B1396061
theorem B930737 : Blo 618297 930737 := bstep (se 2 (by rfl) ⟨349026, by rfl⟩ : syracuseStep 930737 = 698053) B698053
theorem B930755 : Blo 618297 930755 := bstep (se 1 (by rfl) ⟨698066, by rfl⟩ : syracuseStep 930755 = 1396133) B1396133
theorem B930785 : Blo 618297 930785 := bstep (se 2 (by rfl) ⟨349044, by rfl⟩ : syracuseStep 930785 = 698089) B698089
theorem B930803 : Blo 618297 930803 := bstep (se 1 (by rfl) ⟨698102, by rfl⟩ : syracuseStep 930803 = 1396205) B1396205
theorem B930833 : Blo 618297 930833 := bstep (se 2 (by rfl) ⟨349062, by rfl⟩ : syracuseStep 930833 = 698125) B698125
theorem B930851 : Blo 618297 930851 := bstep (se 1 (by rfl) ⟨698138, by rfl⟩ : syracuseStep 930851 = 1396277) B1396277
theorem B996401 : Blo 618297 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B930881 : Blo 618297 930881 := bstep (se 2 (by rfl) ⟨349080, by rfl⟩ : syracuseStep 930881 = 698161) B698161
theorem B6370373 : Blo 618297 6370373 := bstep (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) B1194445
theorem B930899 : Blo 618297 930899 := bstep (se 1 (by rfl) ⟨698174, by rfl⟩ : syracuseStep 930899 = 1396349) B1396349
theorem B930929 : Blo 618297 930929 := bstep (se 2 (by rfl) ⟨349098, by rfl⟩ : syracuseStep 930929 = 698197) B698197
theorem B930947 : Blo 618297 930947 := bstep (se 1 (by rfl) ⟨698210, by rfl⟩ : syracuseStep 930947 = 1396421) B1396421
theorem B930977 : Blo 618297 930977 := bstep (se 2 (by rfl) ⟨349116, by rfl⟩ : syracuseStep 930977 = 698233) B698233
theorem B930995 : Blo 618297 930995 := bstep (se 1 (by rfl) ⟨698246, by rfl⟩ : syracuseStep 930995 = 1396493) B1396493
theorem B3781829 : Blo 618297 3781829 := bstep (se 4 (by rfl) ⟨354546, by rfl⟩ : syracuseStep 3781829 = 709093) B709093
theorem B931025 : Blo 618297 931025 := bstep (se 2 (by rfl) ⟨349134, by rfl⟩ : syracuseStep 931025 = 698269) B698269
theorem B931043 : Blo 618297 931043 := bstep (se 1 (by rfl) ⟨698282, by rfl⟩ : syracuseStep 931043 = 1396565) B1396565
theorem B931073 : Blo 618297 931073 := bstep (se 2 (by rfl) ⟨349152, by rfl⟩ : syracuseStep 931073 = 698305) B698305
theorem B931091 : Blo 618297 931091 := bstep (se 1 (by rfl) ⟨698318, by rfl⟩ : syracuseStep 931091 = 1396637) B1396637
theorem B931121 : Blo 618297 931121 := bstep (se 2 (by rfl) ⟨349170, by rfl⟩ : syracuseStep 931121 = 698341) B698341
theorem B931139 : Blo 618297 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B931169 : Blo 618297 931169 := bstep (se 2 (by rfl) ⟨349188, by rfl⟩ : syracuseStep 931169 = 698377) B698377
theorem B931187 : Blo 618297 931187 := bstep (se 1 (by rfl) ⟨698390, by rfl⟩ : syracuseStep 931187 = 1396781) B1396781
theorem B931217 : Blo 618297 931217 := bstep (se 2 (by rfl) ⟨349206, by rfl⟩ : syracuseStep 931217 = 698413) B698413
theorem B1324451 : Blo 618297 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B931235 : Blo 618297 931235 := bstep (se 1 (by rfl) ⟨698426, by rfl⟩ : syracuseStep 931235 = 1396853) B1396853
theorem B931265 : Blo 618297 931265 := bstep (se 2 (by rfl) ⟨349224, by rfl⟩ : syracuseStep 931265 = 698449) B698449
theorem B931283 : Blo 618297 931283 := bstep (se 1 (by rfl) ⟨698462, by rfl⟩ : syracuseStep 931283 = 1396925) B1396925
theorem B4699619 : Blo 618297 4699619 := bstep (se 1 (by rfl) ⟨3524714, by rfl⟩ : syracuseStep 4699619 = 7049429) B7049429
theorem B931313 : Blo 618297 931313 := bstep (se 2 (by rfl) ⟨349242, by rfl⟩ : syracuseStep 931313 = 698485) B698485
theorem B931331 : Blo 618297 931331 := bstep (se 1 (by rfl) ⟨698498, by rfl⟩ : syracuseStep 931331 = 1396997) B1396997
theorem B931361 : Blo 618297 931361 := bstep (se 2 (by rfl) ⟨349260, by rfl⟩ : syracuseStep 931361 = 698521) B698521
theorem B931379 : Blo 618297 931379 := bstep (se 1 (by rfl) ⟨698534, by rfl⟩ : syracuseStep 931379 = 1397069) B1397069
theorem B1488451 : Blo 618297 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B931409 : Blo 618297 931409 := bstep (se 2 (by rfl) ⟨349278, by rfl⟩ : syracuseStep 931409 = 698557) B698557
theorem B931427 : Blo 618297 931427 := bstep (se 1 (by rfl) ⟨698570, by rfl⟩ : syracuseStep 931427 = 1397141) B1397141
theorem B931457 : Blo 618297 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B1881731 : Blo 618297 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B931475 : Blo 618297 931475 := bstep (se 1 (by rfl) ⟨698606, by rfl⟩ : syracuseStep 931475 = 1397213) B1397213
theorem B931505 : Blo 618297 931505 := bstep (se 2 (by rfl) ⟨349314, by rfl⟩ : syracuseStep 931505 = 698629) B698629
theorem B931523 : Blo 618297 931523 := bstep (se 1 (by rfl) ⟨698642, by rfl⟩ : syracuseStep 931523 = 1397285) B1397285
theorem B931553 : Blo 618297 931553 := bstep (se 2 (by rfl) ⟨349332, by rfl⟩ : syracuseStep 931553 = 698665) B698665
theorem B931571 : Blo 618297 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B931601 : Blo 618297 931601 := bstep (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) B698701
theorem B3979043 : Blo 618297 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B931619 : Blo 618297 931619 := bstep (se 1 (by rfl) ⟨698714, by rfl⟩ : syracuseStep 931619 = 1397429) B1397429
theorem B931649 : Blo 618297 931649 := bstep (se 2 (by rfl) ⟨349368, by rfl⟩ : syracuseStep 931649 = 698737) B698737
theorem B931667 : Blo 618297 931667 := bstep (se 1 (by rfl) ⟨698750, by rfl⟩ : syracuseStep 931667 = 1397501) B1397501
theorem B931697 : Blo 618297 931697 := bstep (se 2 (by rfl) ⟨349386, by rfl⟩ : syracuseStep 931697 = 698773) B698773
theorem B636787 : Blo 618297 636787 := bstep (se 1 (by rfl) ⟨477590, by rfl⟩ : syracuseStep 636787 = 955181) B955181
theorem B931715 : Blo 618297 931715 := bstep (se 1 (by rfl) ⟨698786, by rfl⟩ : syracuseStep 931715 = 1397573) B1397573
theorem B931745 : Blo 618297 931745 := bstep (se 2 (by rfl) ⟨349404, by rfl⟩ : syracuseStep 931745 = 698809) B698809
theorem B931763 : Blo 618297 931763 := bstep (se 1 (by rfl) ⟨698822, by rfl⟩ : syracuseStep 931763 = 1397645) B1397645
theorem B931793 : Blo 618297 931793 := bstep (se 2 (by rfl) ⟨349422, by rfl⟩ : syracuseStep 931793 = 698845) B698845
theorem B931811 : Blo 618297 931811 := bstep (se 1 (by rfl) ⟨698858, by rfl⟩ : syracuseStep 931811 = 1397717) B1397717
theorem B931841 : Blo 618297 931841 := bstep (se 2 (by rfl) ⟨349440, by rfl⟩ : syracuseStep 931841 = 698881) B698881
theorem B1587217 : Blo 618297 1587217 := bstep (se 2 (by rfl) ⟨595206, by rfl⟩ : syracuseStep 1587217 = 1190413) B1190413
theorem B931859 : Blo 618297 931859 := bstep (se 1 (by rfl) ⟨698894, by rfl⟩ : syracuseStep 931859 = 1397789) B1397789
theorem B931889 : Blo 618297 931889 := bstep (se 2 (by rfl) ⟨349458, by rfl⟩ : syracuseStep 931889 = 698917) B698917
theorem B931907 : Blo 618297 931907 := bstep (se 1 (by rfl) ⟨698930, by rfl⟩ : syracuseStep 931907 = 1397861) B1397861
theorem B931937 : Blo 618297 931937 := bstep (se 2 (by rfl) ⟨349476, by rfl⟩ : syracuseStep 931937 = 698953) B698953
theorem B931955 : Blo 618297 931955 := bstep (se 1 (by rfl) ⟨698966, by rfl⟩ : syracuseStep 931955 = 1397933) B1397933
theorem B931985 : Blo 618297 931985 := bstep (se 2 (by rfl) ⟨349494, by rfl⟩ : syracuseStep 931985 = 698989) B698989
theorem B932003 : Blo 618297 932003 := bstep (se 1 (by rfl) ⟨699002, by rfl⟩ : syracuseStep 932003 = 1398005) B1398005
theorem B932033 : Blo 618297 932033 := bstep (se 2 (by rfl) ⟨349512, by rfl⟩ : syracuseStep 932033 = 699025) B699025
theorem B932051 : Blo 618297 932051 := bstep (se 1 (by rfl) ⟨699038, by rfl⟩ : syracuseStep 932051 = 1398077) B1398077
theorem B932081 : Blo 618297 932081 := bstep (se 2 (by rfl) ⟨349530, by rfl⟩ : syracuseStep 932081 = 699061) B699061
theorem B1325315 : Blo 618297 1325315 := bstep (se 1 (by rfl) ⟨993986, by rfl⟩ : syracuseStep 1325315 = 1987973) B1987973
theorem B932099 : Blo 618297 932099 := bstep (se 1 (by rfl) ⟨699074, by rfl⟩ : syracuseStep 932099 = 1398149) B1398149
theorem B932129 : Blo 618297 932129 := bstep (se 2 (by rfl) ⟨349548, by rfl⟩ : syracuseStep 932129 = 699097) B699097
theorem B932147 : Blo 618297 932147 := bstep (se 1 (by rfl) ⟨699110, by rfl⟩ : syracuseStep 932147 = 1398221) B1398221
theorem B932177 : Blo 618297 932177 := bstep (se 2 (by rfl) ⟨349566, by rfl⟩ : syracuseStep 932177 = 699133) B699133
theorem B932195 : Blo 618297 932195 := bstep (se 1 (by rfl) ⟨699146, by rfl⟩ : syracuseStep 932195 = 1398293) B1398293
theorem B1325425 : Blo 618297 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B932225 : Blo 618297 932225 := bstep (se 2 (by rfl) ⟨349584, by rfl⟩ : syracuseStep 932225 = 699169) B699169
theorem B1194385 : Blo 618297 1194385 := bstep (se 2 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 1194385 = 895789) B895789
theorem B932243 : Blo 618297 932243 := bstep (se 1 (by rfl) ⟨699182, by rfl⟩ : syracuseStep 932243 = 1398365) B1398365
theorem B932273 : Blo 618297 932273 := bstep (se 2 (by rfl) ⟨349602, by rfl⟩ : syracuseStep 932273 = 699205) B699205
theorem B932291 : Blo 618297 932291 := bstep (se 1 (by rfl) ⟨699218, by rfl⟩ : syracuseStep 932291 = 1398437) B1398437
theorem B932321 : Blo 618297 932321 := bstep (se 2 (by rfl) ⟨349620, by rfl⟩ : syracuseStep 932321 = 699241) B699241
theorem B1980899 : Blo 618297 1980899 := bstep (se 1 (by rfl) ⟨1485674, by rfl⟩ : syracuseStep 1980899 = 2971349) B2971349
theorem B932339 : Blo 618297 932339 := bstep (se 1 (by rfl) ⟨699254, by rfl⟩ : syracuseStep 932339 = 1398509) B1398509
theorem B932369 : Blo 618297 932369 := bstep (se 2 (by rfl) ⟨349638, by rfl⟩ : syracuseStep 932369 = 699277) B699277
theorem B932387 : Blo 618297 932387 := bstep (se 1 (by rfl) ⟨699290, by rfl⟩ : syracuseStep 932387 = 1398581) B1398581
theorem B932417 : Blo 618297 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B932435 : Blo 618297 932435 := bstep (se 1 (by rfl) ⟨699326, by rfl⟩ : syracuseStep 932435 = 1398653) B1398653
theorem B5290595 : Blo 618297 5290595 := bstep (se 1 (by rfl) ⟨3967946, by rfl⟩ : syracuseStep 5290595 = 7935893) B7935893
theorem B932465 : Blo 618297 932465 := bstep (se 2 (by rfl) ⟨349674, by rfl⟩ : syracuseStep 932465 = 699349) B699349
theorem B932483 : Blo 618297 932483 := bstep (se 1 (by rfl) ⟨699362, by rfl⟩ : syracuseStep 932483 = 1398725) B1398725
theorem B932513 : Blo 618297 932513 := bstep (se 2 (by rfl) ⟨349692, by rfl⟩ : syracuseStep 932513 = 699385) B699385
theorem B932531 : Blo 618297 932531 := bstep (se 1 (by rfl) ⟨699398, by rfl⟩ : syracuseStep 932531 = 1398797) B1398797
theorem B932561 : Blo 618297 932561 := bstep (se 2 (by rfl) ⟨349710, by rfl⟩ : syracuseStep 932561 = 699421) B699421
theorem B932579 : Blo 618297 932579 := bstep (se 1 (by rfl) ⟨699434, by rfl⟩ : syracuseStep 932579 = 1398869) B1398869
theorem B1391345 : Blo 618297 1391345 := bstep (se 2 (by rfl) ⟨521754, by rfl⟩ : syracuseStep 1391345 = 1043509) B1043509
theorem B932609 : Blo 618297 932609 := bstep (se 2 (by rfl) ⟨349728, by rfl⟩ : syracuseStep 932609 = 699457) B699457
theorem B1391363 : Blo 618297 1391363 := bstep (se 1 (by rfl) ⟨1043522, by rfl⟩ : syracuseStep 1391363 = 2087045) B2087045
theorem B1489681 : Blo 618297 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B932627 : Blo 618297 932627 := bstep (se 1 (by rfl) ⟨699470, by rfl⟩ : syracuseStep 932627 = 1398941) B1398941
theorem B932657 : Blo 618297 932657 := bstep (se 2 (by rfl) ⟨349746, by rfl⟩ : syracuseStep 932657 = 699493) B699493
theorem B932675 : Blo 618297 932675 := bstep (se 1 (by rfl) ⟨699506, by rfl⟩ : syracuseStep 932675 = 1399013) B1399013
theorem B932705 : Blo 618297 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B932723 : Blo 618297 932723 := bstep (se 1 (by rfl) ⟨699542, by rfl⟩ : syracuseStep 932723 = 1399085) B1399085
theorem B932753 : Blo 618297 932753 := bstep (se 2 (by rfl) ⟨349782, by rfl⟩ : syracuseStep 932753 = 699565) B699565
theorem B932771 : Blo 618297 932771 := bstep (se 1 (by rfl) ⟨699578, by rfl⟩ : syracuseStep 932771 = 1399157) B1399157
theorem B3783601 : Blo 618297 3783601 := bstep (se 2 (by rfl) ⟨1418850, by rfl⟩ : syracuseStep 3783601 = 2837701) B2837701
theorem B932801 : Blo 618297 932801 := bstep (se 2 (by rfl) ⟨349800, by rfl⟩ : syracuseStep 932801 = 699601) B699601
theorem B932819 : Blo 618297 932819 := bstep (se 1 (by rfl) ⟨699614, by rfl⟩ : syracuseStep 932819 = 1399229) B1399229
theorem B932849 : Blo 618297 932849 := bstep (se 2 (by rfl) ⟨349818, by rfl⟩ : syracuseStep 932849 = 699637) B699637
theorem B932867 : Blo 618297 932867 := bstep (se 1 (by rfl) ⟨699650, by rfl⟩ : syracuseStep 932867 = 1399301) B1399301
theorem B1391633 : Blo 618297 1391633 := bstep (se 2 (by rfl) ⟨521862, by rfl⟩ : syracuseStep 1391633 = 1043725) B1043725
theorem B932897 : Blo 618297 932897 := bstep (se 2 (by rfl) ⟨349836, by rfl⟩ : syracuseStep 932897 = 699673) B699673
theorem B1391651 : Blo 618297 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B932915 : Blo 618297 932915 := bstep (se 1 (by rfl) ⟨699686, by rfl⟩ : syracuseStep 932915 = 1399373) B1399373
theorem B932945 : Blo 618297 932945 := bstep (se 2 (by rfl) ⟨349854, by rfl⟩ : syracuseStep 932945 = 699709) B699709
theorem B932963 : Blo 618297 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B932993 : Blo 618297 932993 := bstep (se 2 (by rfl) ⟨349872, by rfl⟩ : syracuseStep 932993 = 699745) B699745
theorem B933011 : Blo 618297 933011 := bstep (se 1 (by rfl) ⟨699758, by rfl⟩ : syracuseStep 933011 = 1399517) B1399517
theorem B1064083 : Blo 618297 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B933041 : Blo 618297 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B933059 : Blo 618297 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B933089 : Blo 618297 933089 := bstep (se 2 (by rfl) ⟨349908, by rfl⟩ : syracuseStep 933089 = 699817) B699817
theorem B933107 : Blo 618297 933107 := bstep (se 1 (by rfl) ⟨699830, by rfl⟩ : syracuseStep 933107 = 1399661) B1399661
theorem B933137 : Blo 618297 933137 := bstep (se 2 (by rfl) ⟨349926, by rfl⟩ : syracuseStep 933137 = 699853) B699853
theorem B933155 : Blo 618297 933155 := bstep (se 1 (by rfl) ⟨699866, by rfl⟩ : syracuseStep 933155 = 1399733) B1399733
theorem B1391921 : Blo 618297 1391921 := bstep (se 2 (by rfl) ⟨521970, by rfl⟩ : syracuseStep 1391921 = 1043941) B1043941
theorem B933185 : Blo 618297 933185 := bstep (se 2 (by rfl) ⟨349944, by rfl⟩ : syracuseStep 933185 = 699889) B699889
theorem B1391939 : Blo 618297 1391939 := bstep (se 1 (by rfl) ⟨1043954, by rfl⟩ : syracuseStep 1391939 = 2087909) B2087909
theorem B933203 : Blo 618297 933203 := bstep (se 1 (by rfl) ⟨699902, by rfl⟩ : syracuseStep 933203 = 1399805) B1399805
theorem B933233 : Blo 618297 933233 := bstep (se 2 (by rfl) ⟨349962, by rfl⟩ : syracuseStep 933233 = 699925) B699925
theorem B933251 : Blo 618297 933251 := bstep (se 1 (by rfl) ⟨699938, by rfl⟩ : syracuseStep 933251 = 1399877) B1399877
theorem B933281 : Blo 618297 933281 := bstep (se 2 (by rfl) ⟨349980, by rfl⟩ : syracuseStep 933281 = 699961) B699961
theorem B3816881 : Blo 618297 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B933299 : Blo 618297 933299 := bstep (se 1 (by rfl) ⟨699974, by rfl⟩ : syracuseStep 933299 = 1399949) B1399949
theorem B933329 : Blo 618297 933329 := bstep (se 2 (by rfl) ⟨349998, by rfl⟩ : syracuseStep 933329 = 699997) B699997
theorem B933347 : Blo 618297 933347 := bstep (se 1 (by rfl) ⟨700010, by rfl⟩ : syracuseStep 933347 = 1400021) B1400021
theorem B3980785 : Blo 618297 3980785 := bstep (se 2 (by rfl) ⟨1492794, by rfl⟩ : syracuseStep 3980785 = 2985589) B2985589
theorem B933377 : Blo 618297 933377 := bstep (se 2 (by rfl) ⟨350016, by rfl⟩ : syracuseStep 933377 = 700033) B700033
theorem B4472333 : Blo 618297 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B933395 : Blo 618297 933395 := bstep (se 1 (by rfl) ⟨700046, by rfl⟩ : syracuseStep 933395 = 1400093) B1400093
theorem B933425 : Blo 618297 933425 := bstep (se 2 (by rfl) ⟨350034, by rfl⟩ : syracuseStep 933425 = 700069) B700069
theorem B933443 : Blo 618297 933443 := bstep (se 1 (by rfl) ⟨700082, by rfl⟩ : syracuseStep 933443 = 1400165) B1400165
theorem B1392209 : Blo 618297 1392209 := bstep (se 2 (by rfl) ⟨522078, by rfl⟩ : syracuseStep 1392209 = 1044157) B1044157
theorem B1392227 : Blo 618297 1392227 := bstep (se 1 (by rfl) ⟨1044170, by rfl⟩ : syracuseStep 1392227 = 2088341) B2088341
theorem B1883917 : Blo 618297 1883917 := bstep (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) B706469
theorem B1392497 : Blo 618297 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B1392515 : Blo 618297 1392515 := bstep (se 1 (by rfl) ⟨1044386, by rfl⟩ : syracuseStep 1392515 = 2088773) B2088773
theorem B3522437 : Blo 618297 3522437 := bstep (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) B660457
theorem B1392785 : Blo 618297 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B1392803 : Blo 618297 1392803 := bstep (se 1 (by rfl) ⟨1044602, by rfl⟩ : syracuseStep 1392803 = 2089205) B2089205
theorem B835795 : Blo 618297 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B1982755 : Blo 618297 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B1327441 : Blo 618297 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B1393073 : Blo 618297 1393073 := bstep (se 2 (by rfl) ⟨522402, by rfl⟩ : syracuseStep 1393073 = 1044805) B1044805
theorem B1393091 : Blo 618297 1393091 := bstep (se 1 (by rfl) ⟨1044818, by rfl⟩ : syracuseStep 1393091 = 2089637) B2089637
theorem B3523121 : Blo 618297 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B1884845 : Blo 618297 1884845 := bstep (se 3 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 1884845 = 706817) B706817
theorem B1393361 : Blo 618297 1393361 := bstep (se 2 (by rfl) ⟨522510, by rfl⟩ : syracuseStep 1393361 = 1045021) B1045021
theorem B1393379 : Blo 618297 1393379 := bstep (se 1 (by rfl) ⟨1045034, by rfl⟩ : syracuseStep 1393379 = 2090069) B2090069
theorem B1327843 : Blo 618297 1327843 := bstep (se 1 (by rfl) ⟨995882, by rfl⟩ : syracuseStep 1327843 = 1991765) B1991765
theorem B1983217 : Blo 618297 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B1393649 : Blo 618297 1393649 := bstep (se 2 (by rfl) ⟨522618, by rfl⟩ : syracuseStep 1393649 = 1045237) B1045237
theorem B1393667 : Blo 618297 1393667 := bstep (se 1 (by rfl) ⟨1045250, by rfl⟩ : syracuseStep 1393667 = 2090501) B2090501
theorem B7554161 : Blo 618297 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B836833 : Blo 618297 836833 := bstep (se 2 (by rfl) ⟨313812, by rfl⟩ : syracuseStep 836833 = 627625) B627625
theorem B1393937 : Blo 618297 1393937 := bstep (se 2 (by rfl) ⟨522726, by rfl⟩ : syracuseStep 1393937 = 1045453) B1045453
theorem B1393955 : Blo 618297 1393955 := bstep (se 1 (by rfl) ⟨1045466, by rfl⟩ : syracuseStep 1393955 = 2090933) B2090933
theorem B836995 : Blo 618297 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B3982733 : Blo 618297 3982733 := bstep (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) B1493525
theorem B1394225 : Blo 618297 1394225 := bstep (se 2 (by rfl) ⟨522834, by rfl⟩ : syracuseStep 1394225 = 1045669) B1045669
theorem B1394243 : Blo 618297 1394243 := bstep (se 1 (by rfl) ⟨1045682, by rfl⟩ : syracuseStep 1394243 = 2091365) B2091365
theorem B4474693 : Blo 618297 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B1394513 : Blo 618297 1394513 := bstep (se 2 (by rfl) ⟨522942, by rfl⟩ : syracuseStep 1394513 = 1045885) B1045885
theorem B1394531 : Blo 618297 1394531 := bstep (se 1 (by rfl) ⟨1045898, by rfl⟩ : syracuseStep 1394531 = 2091797) B2091797
theorem B3524579 : Blo 618297 3524579 := bstep (se 1 (by rfl) ⟨2643434, by rfl⟩ : syracuseStep 3524579 = 5286869) B5286869
theorem B1394801 : Blo 618297 1394801 := bstep (se 2 (by rfl) ⟨523050, by rfl⟩ : syracuseStep 1394801 = 1046101) B1046101
theorem B1394819 : Blo 618297 1394819 := bstep (se 1 (by rfl) ⟨1046114, by rfl⟩ : syracuseStep 1394819 = 2092229) B2092229
theorem B1886339 : Blo 618297 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B3361123 : Blo 618297 3361123 := bstep (se 1 (by rfl) ⟨2520842, by rfl⟩ : syracuseStep 3361123 = 5041685) B5041685
theorem B1395089 : Blo 618297 1395089 := bstep (se 2 (by rfl) ⟨523158, by rfl⟩ : syracuseStep 1395089 = 1046317) B1046317
theorem B2116003 : Blo 618297 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B1395107 : Blo 618297 1395107 := bstep (se 1 (by rfl) ⟨1046330, by rfl⟩ : syracuseStep 1395107 = 2092661) B2092661
theorem B1493603 : Blo 618297 1493603 := bstep (se 1 (by rfl) ⟨1120202, by rfl⟩ : syracuseStep 1493603 = 2240405) B2240405
theorem B1395377 : Blo 618297 1395377 := bstep (se 2 (by rfl) ⟨523266, by rfl⟩ : syracuseStep 1395377 = 1046533) B1046533
theorem B1395395 : Blo 618297 1395395 := bstep (se 1 (by rfl) ⟨1046546, by rfl⟩ : syracuseStep 1395395 = 2093093) B2093093
theorem B4704965 : Blo 618297 4704965 := bstep (se 4 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 4704965 = 882181) B882181
theorem B1395665 : Blo 618297 1395665 := bstep (se 2 (by rfl) ⟨523374, by rfl⟩ : syracuseStep 1395665 = 1046749) B1046749
theorem B1395683 : Blo 618297 1395683 := bstep (se 1 (by rfl) ⟨1046762, by rfl⟩ : syracuseStep 1395683 = 2093525) B2093525
theorem B3132593 : Blo 618297 3132593 := bstep (se 2 (by rfl) ⟨1174722, by rfl⟩ : syracuseStep 3132593 = 2349445) B2349445
theorem B5950691 : Blo 618297 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B1395953 : Blo 618297 1395953 := bstep (se 2 (by rfl) ⟨523482, by rfl⟩ : syracuseStep 1395953 = 1046965) B1046965
theorem B1395971 : Blo 618297 1395971 := bstep (se 1 (by rfl) ⟨1046978, by rfl⟩ : syracuseStep 1395971 = 2093957) B2093957
theorem B1494371 : Blo 618297 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B1985933 : Blo 618297 1985933 := bstep (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) B744725
theorem B1887715 : Blo 618297 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B1396241 : Blo 618297 1396241 := bstep (se 2 (by rfl) ⟨523590, by rfl⟩ : syracuseStep 1396241 = 1047181) B1047181
theorem B13454869 : Blo 618297 13454869 := bstep (se 6 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 13454869 = 630697) B630697
theorem B1396259 : Blo 618297 1396259 := bstep (se 1 (by rfl) ⟨1047194, by rfl⟩ : syracuseStep 1396259 = 2094389) B2094389
theorem B4836977 : Blo 618297 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B3264241 : Blo 618297 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B1396529 : Blo 618297 1396529 := bstep (se 2 (by rfl) ⟨523698, by rfl⟩ : syracuseStep 1396529 = 1047397) B1047397
theorem B1396547 : Blo 618297 1396547 := bstep (se 1 (by rfl) ⟨1047410, by rfl⟩ : syracuseStep 1396547 = 2094821) B2094821
theorem B1494929 : Blo 618297 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B1396817 : Blo 618297 1396817 := bstep (se 2 (by rfl) ⟨523806, by rfl⟩ : syracuseStep 1396817 = 1047613) B1047613
theorem B1396835 : Blo 618297 1396835 := bstep (se 1 (by rfl) ⟨1047626, by rfl⟩ : syracuseStep 1396835 = 2095253) B2095253
theorem B2642033 : Blo 618297 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B4313357 : Blo 618297 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B1397105 : Blo 618297 1397105 := bstep (se 2 (by rfl) ⟨523914, by rfl⟩ : syracuseStep 1397105 = 1047829) B1047829
theorem B1397123 : Blo 618297 1397123 := bstep (se 1 (by rfl) ⟨1047842, by rfl⟩ : syracuseStep 1397123 = 2095685) B2095685
theorem B3134051 : Blo 618297 3134051 := bstep (se 1 (by rfl) ⟨2350538, by rfl⟩ : syracuseStep 3134051 = 4701077) B4701077
theorem B1397393 : Blo 618297 1397393 := bstep (se 2 (by rfl) ⟨524022, by rfl⟩ : syracuseStep 1397393 = 1048045) B1048045
theorem B1397411 : Blo 618297 1397411 := bstep (se 1 (by rfl) ⟨1048058, by rfl⟩ : syracuseStep 1397411 = 2096117) B2096117
theorem B3986117 : Blo 618297 3986117 := bstep (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) B747397
theorem B840449 : Blo 618297 840449 := bstep (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) B630337
theorem B1397681 : Blo 618297 1397681 := bstep (se 2 (by rfl) ⟨524130, by rfl⟩ : syracuseStep 1397681 = 1048261) B1048261
theorem B1397699 : Blo 618297 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B1987523 : Blo 618297 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B6804593 : Blo 618297 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B3527813 : Blo 618297 3527813 := bstep (se 4 (by rfl) ⟨330732, by rfl⟩ : syracuseStep 3527813 = 661465) B661465
theorem B1889453 : Blo 618297 1889453 := bstep (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) B708545
theorem B1397969 : Blo 618297 1397969 := bstep (se 2 (by rfl) ⟨524238, by rfl⟩ : syracuseStep 1397969 = 1048477) B1048477
theorem B1397987 : Blo 618297 1397987 := bstep (se 1 (by rfl) ⟨1048490, by rfl⟩ : syracuseStep 1397987 = 2096981) B2096981
theorem B2643299 : Blo 618297 2643299 := bstep (se 1 (by rfl) ⟨1982474, by rfl⟩ : syracuseStep 2643299 = 3964949) B3964949
theorem B3134861 : Blo 618297 3134861 := bstep (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) B1175573
theorem B1398257 : Blo 618297 1398257 := bstep (se 2 (by rfl) ⟨524346, by rfl⟩ : syracuseStep 1398257 = 1048693) B1048693
theorem B1398275 : Blo 618297 1398275 := bstep (se 1 (by rfl) ⟨1048706, by rfl⟩ : syracuseStep 1398275 = 2097413) B2097413
theorem B1791533 : Blo 618297 1791533 := bstep (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) B671825
theorem B3528269 : Blo 618297 3528269 := bstep (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) B1323101
theorem B1398545 : Blo 618297 1398545 := bstep (se 2 (by rfl) ⟨524454, by rfl⟩ : syracuseStep 1398545 = 1048909) B1048909
theorem B1398563 : Blo 618297 1398563 := bstep (se 1 (by rfl) ⟨1048922, by rfl⟩ : syracuseStep 1398563 = 2097845) B2097845
theorem B2086829 : Blo 618297 2086829 := bstep (se 3 (by rfl) ⟨391280, by rfl⟩ : syracuseStep 2086829 = 782561) B782561
theorem B2086883 : Blo 618297 2086883 := bstep (se 1 (by rfl) ⟨1565162, by rfl⟩ : syracuseStep 2086883 = 3130325) B3130325
theorem B1398833 : Blo 618297 1398833 := bstep (se 2 (by rfl) ⟨524562, by rfl⟩ : syracuseStep 1398833 = 1049125) B1049125
theorem B1398851 : Blo 618297 1398851 := bstep (se 1 (by rfl) ⟨1049138, by rfl⟩ : syracuseStep 1398851 = 2098277) B2098277
theorem B2349233 : Blo 618297 2349233 := bstep (se 2 (by rfl) ⟨880962, by rfl⟩ : syracuseStep 2349233 = 1761925) B1761925
theorem B1988803 : Blo 618297 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B2087153 : Blo 618297 2087153 := bstep (se 2 (by rfl) ⟨782682, by rfl⟩ : syracuseStep 2087153 = 1565365) B1565365
theorem B743683 : Blo 618297 743683 := bstep (se 1 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 743683 = 1115525) B1115525
theorem B1399121 : Blo 618297 1399121 := bstep (se 2 (by rfl) ⟨524670, by rfl⟩ : syracuseStep 1399121 = 1049341) B1049341
theorem B1399139 : Blo 618297 1399139 := bstep (se 1 (by rfl) ⟨1049354, by rfl⟩ : syracuseStep 1399139 = 2098709) B2098709
theorem B940513 : Blo 618297 940513 := bstep (se 2 (by rfl) ⟨352692, by rfl⟩ : syracuseStep 940513 = 705385) B705385
theorem B1989137 : Blo 618297 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1399409 : Blo 618297 1399409 := bstep (se 2 (by rfl) ⟨524778, by rfl⟩ : syracuseStep 1399409 = 1049557) B1049557
theorem B1399427 : Blo 618297 1399427 := bstep (se 1 (by rfl) ⟨1049570, by rfl⟩ : syracuseStep 1399427 = 2099141) B2099141
theorem B2087693 : Blo 618297 2087693 := bstep (se 3 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 2087693 = 782885) B782885
theorem B940835 : Blo 618297 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B2087747 : Blo 618297 2087747 := bstep (se 1 (by rfl) ⟨1565810, by rfl⟩ : syracuseStep 2087747 = 3131621) B3131621
theorem B5954417 : Blo 618297 5954417 := bstep (se 2 (by rfl) ⟨2232906, by rfl⟩ : syracuseStep 5954417 = 4465813) B4465813
theorem B3627917 : Blo 618297 3627917 := bstep (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) B1360469
theorem B1399697 : Blo 618297 1399697 := bstep (se 2 (by rfl) ⟨524886, by rfl⟩ : syracuseStep 1399697 = 1049773) B1049773
theorem B1399715 : Blo 618297 1399715 := bstep (se 1 (by rfl) ⟨1049786, by rfl⟩ : syracuseStep 1399715 = 2099573) B2099573
theorem B2382797 : Blo 618297 2382797 := bstep (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) B893549
theorem B2088017 : Blo 618297 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B1399985 : Blo 618297 1399985 := bstep (se 2 (by rfl) ⟨524994, by rfl⟩ : syracuseStep 1399985 = 1049989) B1049989
theorem B1400003 : Blo 618297 1400003 := bstep (se 1 (by rfl) ⟨1050002, by rfl⟩ : syracuseStep 1400003 = 2100005) B2100005
theorem B1760717 : Blo 618297 1760717 := bstep (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) B660269
theorem B2350691 : Blo 618297 2350691 := bstep (se 1 (by rfl) ⟨1763018, by rfl⟩ : syracuseStep 2350691 = 3526037) B3526037
theorem B2088557 : Blo 618297 2088557 := bstep (se 3 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 2088557 = 783209) B783209
theorem B941681 : Blo 618297 941681 := bstep (se 2 (by rfl) ⟨353130, by rfl⟩ : syracuseStep 941681 = 706261) B706261
theorem B2088611 : Blo 618297 2088611 := bstep (se 1 (by rfl) ⟨1566458, by rfl⟩ : syracuseStep 2088611 = 3132917) B3132917
theorem B909041 : Blo 618297 909041 := bstep (se 2 (by rfl) ⟨340890, by rfl⟩ : syracuseStep 909041 = 681781) B681781
theorem B2088881 : Blo 618297 2088881 := bstep (se 2 (by rfl) ⟨783330, by rfl⟩ : syracuseStep 2088881 = 1566661) B1566661
theorem B745571 : Blo 618297 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B1794161 : Blo 618297 1794161 := bstep (se 2 (by rfl) ⟨672810, by rfl⟩ : syracuseStep 1794161 = 1345621) B1345621
theorem B745619 : Blo 618297 745619 := bstep (se 1 (by rfl) ⟨559214, by rfl⟩ : syracuseStep 745619 = 1118429) B1118429
theorem B3629233 : Blo 618297 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B1695953 : Blo 618297 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B3137777 : Blo 618297 3137777 := bstep (se 2 (by rfl) ⟨1176666, by rfl⟩ : syracuseStep 3137777 = 2353333) B2353333
theorem B4251953 : Blo 618297 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B4710797 : Blo 618297 4710797 := bstep (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) B1766549
theorem B1761709 : Blo 618297 1761709 := bstep (se 3 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 1761709 = 660641) B660641
theorem B3531185 : Blo 618297 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B2089421 : Blo 618297 2089421 := bstep (se 3 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 2089421 = 783533) B783533
theorem B2515427 : Blo 618297 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B2089475 : Blo 618297 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1991213 : Blo 618297 1991213 := bstep (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) B746705
theorem B2351693 : Blo 618297 2351693 := bstep (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) B881885
theorem B1565315 : Blo 618297 1565315 := bstep (se 1 (by rfl) ⟨1173986, by rfl⟩ : syracuseStep 1565315 = 2347973) B2347973
theorem B942787 : Blo 618297 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B2089745 : Blo 618297 2089745 := bstep (se 2 (by rfl) ⟨783654, by rfl⟩ : syracuseStep 2089745 = 1567309) B1567309
theorem B1565507 : Blo 618297 1565507 := bstep (se 1 (by rfl) ⟨1174130, by rfl⟩ : syracuseStep 1565507 = 2348261) B2348261
theorem B4776803 : Blo 618297 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B2646989 : Blo 618297 2646989 := bstep (se 3 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 2646989 = 992621) B992621
theorem B943091 : Blo 618297 943091 := bstep (se 1 (by rfl) ⟨707318, by rfl⟩ : syracuseStep 943091 = 1414637) B1414637
theorem B36660437 : Blo 618297 36660437 := bstep (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) B859229
theorem B2090285 : Blo 618297 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B2385229 : Blo 618297 2385229 := bstep (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) B894461
theorem B2090339 : Blo 618297 2090339 := bstep (se 1 (by rfl) ⟨1567754, by rfl⟩ : syracuseStep 2090339 = 3135509) B3135509
theorem B6809141 : Blo 618297 6809141 := bstep (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) B638357
theorem B2418275 : Blo 618297 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B2090609 : Blo 618297 2090609 := bstep (se 2 (by rfl) ⟨783978, by rfl⟩ : syracuseStep 2090609 = 1567957) B1567957
theorem B3139235 : Blo 618297 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B1566449 : Blo 618297 1566449 := bstep (se 2 (by rfl) ⟨587418, by rfl⟩ : syracuseStep 1566449 = 1174837) B1174837
theorem B1566499 : Blo 618297 1566499 := bstep (se 1 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 1566499 = 2349749) B2349749
theorem B3532643 : Blo 618297 3532643 := bstep (se 1 (by rfl) ⟨2649482, by rfl⟩ : syracuseStep 3532643 = 5298965) B5298965
theorem B944003 : Blo 618297 944003 := bstep (se 1 (by rfl) ⟨708002, by rfl⟩ : syracuseStep 944003 = 1416005) B1416005
theorem B1566641 : Blo 618297 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B2156483 : Blo 618297 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B1796195 : Blo 618297 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1763441 : Blo 618297 1763441 := bstep (se 2 (by rfl) ⟨661290, by rfl⟩ : syracuseStep 1763441 = 1322581) B1322581
theorem B2091149 : Blo 618297 2091149 := bstep (se 3 (by rfl) ⟨392090, by rfl⟩ : syracuseStep 2091149 = 784181) B784181
theorem B2091203 : Blo 618297 2091203 := bstep (se 1 (by rfl) ⟨1568402, by rfl⟩ : syracuseStep 2091203 = 3136805) B3136805
theorem B9038051 : Blo 618297 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B944369 : Blo 618297 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B1992995 : Blo 618297 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B1763633 : Blo 618297 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B1173827 : Blo 618297 1173827 := bstep (se 1 (by rfl) ⟨880370, by rfl⟩ : syracuseStep 1173827 = 1760741) B1760741
theorem B944465 : Blo 618297 944465 := bstep (se 2 (by rfl) ⟨354174, by rfl⟩ : syracuseStep 944465 = 708349) B708349
theorem B2681201 : Blo 618297 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B2124227 : Blo 618297 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B3140045 : Blo 618297 3140045 := bstep (se 3 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 3140045 = 1177517) B1177517
theorem B2091473 : Blo 618297 2091473 := bstep (se 2 (by rfl) ⟨784302, by rfl⟩ : syracuseStep 2091473 = 1568605) B1568605
theorem B1174115 : Blo 618297 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B2353805 : Blo 618297 2353805 := bstep (se 3 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 2353805 = 882677) B882677
theorem B3533645 : Blo 618297 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B1567633 : Blo 618297 1567633 := bstep (se 2 (by rfl) ⟨587862, by rfl⟩ : syracuseStep 1567633 = 1175725) B1175725
theorem B2092013 : Blo 618297 2092013 := bstep (se 3 (by rfl) ⟨392252, by rfl⟩ : syracuseStep 2092013 = 784505) B784505
theorem B1043489 : Blo 618297 1043489 := bstep (se 2 (by rfl) ⟨391308, by rfl⟩ : syracuseStep 1043489 = 782617) B782617
theorem B2092067 : Blo 618297 2092067 := bstep (se 1 (by rfl) ⟨1569050, by rfl⟩ : syracuseStep 2092067 = 3138101) B3138101
theorem B1043617 : Blo 618297 1043617 := bstep (se 2 (by rfl) ⟨391356, by rfl⟩ : syracuseStep 1043617 = 782713) B782713
theorem B1567907 : Blo 618297 1567907 := bstep (se 1 (by rfl) ⟨1175930, by rfl⟩ : syracuseStep 1567907 = 2351861) B2351861
theorem B945329 : Blo 618297 945329 := bstep (se 2 (by rfl) ⟨354498, by rfl⟩ : syracuseStep 945329 = 708997) B708997
theorem B1043651 : Blo 618297 1043651 := bstep (se 1 (by rfl) ⟨782738, by rfl⟩ : syracuseStep 1043651 = 1565477) B1565477
theorem B13429957 : Blo 618297 13429957 := bstep (se 4 (by rfl) ⟨1259058, by rfl⟩ : syracuseStep 13429957 = 2518117) B2518117
theorem B4713713 : Blo 618297 4713713 := bstep (se 2 (by rfl) ⟨1767642, by rfl⟩ : syracuseStep 4713713 = 3535285) B3535285
theorem B1764625 : Blo 618297 1764625 := bstep (se 2 (by rfl) ⟨661734, by rfl⟩ : syracuseStep 1764625 = 1323469) B1323469
theorem B2092337 : Blo 618297 2092337 := bstep (se 2 (by rfl) ⟨784626, by rfl⟩ : syracuseStep 2092337 = 1569253) B1569253
theorem B1043779 : Blo 618297 1043779 := bstep (se 1 (by rfl) ⟨782834, by rfl⟩ : syracuseStep 1043779 = 1565669) B1565669
theorem B1568099 : Blo 618297 1568099 := bstep (se 1 (by rfl) ⟨1176074, by rfl⟩ : syracuseStep 1568099 = 2352149) B2352149
theorem B2354609 : Blo 618297 2354609 := bstep (se 2 (by rfl) ⟨882978, by rfl⟩ : syracuseStep 2354609 = 1765957) B1765957
theorem B1043921 : Blo 618297 1043921 := bstep (se 2 (by rfl) ⟨391470, by rfl⟩ : syracuseStep 1043921 = 782941) B782941
theorem B1175057 : Blo 618297 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B1764899 : Blo 618297 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B1044049 : Blo 618297 1044049 := bstep (se 2 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 1044049 = 783037) B783037
theorem B1044083 : Blo 618297 1044083 := bstep (se 1 (by rfl) ⟨783062, by rfl⟩ : syracuseStep 1044083 = 1566125) B1566125
theorem B1765091 : Blo 618297 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B1044211 : Blo 618297 1044211 := bstep (se 1 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 1044211 = 1566317) B1566317
theorem B618307 : Blo 618297 618307 := bstep (se 1 (by rfl) ⟨463730, by rfl⟩ : syracuseStep 618307 = 927461) B927461
theorem B5959493 : Blo 618297 5959493 := bstep (se 4 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 5959493 = 1117405) B1117405
theorem B2092877 : Blo 618297 2092877 := bstep (se 3 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 2092877 = 784829) B784829
theorem B618323 : Blo 618297 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B618339 : Blo 618297 618339 := bstep (se 1 (by rfl) ⟨463754, by rfl⟩ : syracuseStep 618339 = 927509) B927509
theorem B2518897 : Blo 618297 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B618355 : Blo 618297 618355 := bstep (se 1 (by rfl) ⟨463766, by rfl⟩ : syracuseStep 618355 = 927533) B927533
theorem B1044353 : Blo 618297 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B618371 : Blo 618297 618371 := bstep (se 1 (by rfl) ⟨463778, by rfl⟩ : syracuseStep 618371 = 927557) B927557
theorem B2092931 : Blo 618297 2092931 := bstep (se 1 (by rfl) ⟨1569698, by rfl⟩ : syracuseStep 2092931 = 3139397) B3139397
theorem B618387 : Blo 618297 618387 := bstep (se 1 (by rfl) ⟨463790, by rfl⟩ : syracuseStep 618387 = 927581) B927581
theorem B618403 : Blo 618297 618403 := bstep (se 1 (by rfl) ⟨463802, by rfl⟩ : syracuseStep 618403 = 927605) B927605
theorem B618419 : Blo 618297 618419 := bstep (se 1 (by rfl) ⟨463814, by rfl⟩ : syracuseStep 618419 = 927629) B927629
theorem B618435 : Blo 618297 618435 := bstep (se 1 (by rfl) ⟨463826, by rfl⟩ : syracuseStep 618435 = 927653) B927653
theorem B618451 : Blo 618297 618451 := bstep (se 1 (by rfl) ⟨463838, by rfl⟩ : syracuseStep 618451 = 927677) B927677
theorem B618467 : Blo 618297 618467 := bstep (se 1 (by rfl) ⟨463850, by rfl⟩ : syracuseStep 618467 = 927701) B927701
theorem B2650097 : Blo 618297 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B618483 : Blo 618297 618483 := bstep (se 1 (by rfl) ⟨463862, by rfl⟩ : syracuseStep 618483 = 927725) B927725
theorem B880627 : Blo 618297 880627 := bstep (se 1 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 880627 = 1320941) B1320941
theorem B1044481 : Blo 618297 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B618499 : Blo 618297 618499 := bstep (se 1 (by rfl) ⟨463874, by rfl⟩ : syracuseStep 618499 = 927749) B927749
theorem B618515 : Blo 618297 618515 := bstep (se 1 (by rfl) ⟨463886, by rfl⟩ : syracuseStep 618515 = 927773) B927773
theorem B618531 : Blo 618297 618531 := bstep (se 1 (by rfl) ⟨463898, by rfl⟩ : syracuseStep 618531 = 927797) B927797
theorem B1044515 : Blo 618297 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B618547 : Blo 618297 618547 := bstep (se 1 (by rfl) ⟨463910, by rfl⟩ : syracuseStep 618547 = 927821) B927821
theorem B618563 : Blo 618297 618563 := bstep (se 1 (by rfl) ⟨463922, by rfl⟩ : syracuseStep 618563 = 927845) B927845
theorem B2355277 : Blo 618297 2355277 := bstep (se 3 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 2355277 = 883229) B883229
theorem B880723 : Blo 618297 880723 := bstep (se 1 (by rfl) ⟨660542, by rfl⟩ : syracuseStep 880723 = 1321085) B1321085
theorem B618579 : Blo 618297 618579 := bstep (se 1 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 618579 = 927869) B927869
theorem B618595 : Blo 618297 618595 := bstep (se 1 (by rfl) ⟨463946, by rfl⟩ : syracuseStep 618595 = 927893) B927893
theorem B618611 : Blo 618297 618611 := bstep (se 1 (by rfl) ⟨463958, by rfl⟩ : syracuseStep 618611 = 927917) B927917
theorem B618627 : Blo 618297 618627 := bstep (se 1 (by rfl) ⟨463970, by rfl⟩ : syracuseStep 618627 = 927941) B927941
theorem B2093201 : Blo 618297 2093201 := bstep (se 2 (by rfl) ⟨784950, by rfl⟩ : syracuseStep 2093201 = 1569901) B1569901
theorem B618643 : Blo 618297 618643 := bstep (se 1 (by rfl) ⟨463982, by rfl⟩ : syracuseStep 618643 = 927965) B927965
theorem B618659 : Blo 618297 618659 := bstep (se 1 (by rfl) ⟨463994, by rfl⟩ : syracuseStep 618659 = 927989) B927989
theorem B1044643 : Blo 618297 1044643 := bstep (se 1 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 1044643 = 1566965) B1566965
theorem B618675 : Blo 618297 618675 := bstep (se 1 (by rfl) ⟨464006, by rfl⟩ : syracuseStep 618675 = 928013) B928013
theorem B618691 : Blo 618297 618691 := bstep (se 1 (by rfl) ⟨464018, by rfl⟩ : syracuseStep 618691 = 928037) B928037
theorem B618707 : Blo 618297 618707 := bstep (se 1 (by rfl) ⟨464030, by rfl⟩ : syracuseStep 618707 = 928061) B928061
theorem B618723 : Blo 618297 618723 := bstep (se 1 (by rfl) ⟨464042, by rfl⟩ : syracuseStep 618723 = 928085) B928085
theorem B618739 : Blo 618297 618739 := bstep (se 1 (by rfl) ⟨464054, by rfl⟩ : syracuseStep 618739 = 928109) B928109
theorem B618755 : Blo 618297 618755 := bstep (se 1 (by rfl) ⟨464066, by rfl⟩ : syracuseStep 618755 = 928133) B928133
theorem B1569041 : Blo 618297 1569041 := bstep (se 2 (by rfl) ⟨588390, by rfl⟩ : syracuseStep 1569041 = 1176781) B1176781
theorem B618771 : Blo 618297 618771 := bstep (se 1 (by rfl) ⟨464078, by rfl⟩ : syracuseStep 618771 = 928157) B928157
theorem B618787 : Blo 618297 618787 := bstep (se 1 (by rfl) ⟨464090, by rfl⟩ : syracuseStep 618787 = 928181) B928181
theorem B1044785 : Blo 618297 1044785 := bstep (se 2 (by rfl) ⟨391794, by rfl⟩ : syracuseStep 1044785 = 783589) B783589
theorem B618803 : Blo 618297 618803 := bstep (se 1 (by rfl) ⟨464102, by rfl⟩ : syracuseStep 618803 = 928205) B928205
theorem B618819 : Blo 618297 618819 := bstep (se 1 (by rfl) ⟨464114, by rfl⟩ : syracuseStep 618819 = 928229) B928229
theorem B1569091 : Blo 618297 1569091 := bstep (se 1 (by rfl) ⟨1176818, by rfl⟩ : syracuseStep 1569091 = 2353637) B2353637
theorem B618835 : Blo 618297 618835 := bstep (se 1 (by rfl) ⟨464126, by rfl⟩ : syracuseStep 618835 = 928253) B928253
theorem B618851 : Blo 618297 618851 := bstep (se 1 (by rfl) ⟨464138, by rfl⟩ : syracuseStep 618851 = 928277) B928277
theorem B618867 : Blo 618297 618867 := bstep (se 1 (by rfl) ⟨464150, by rfl⟩ : syracuseStep 618867 = 928301) B928301
theorem B782723 : Blo 618297 782723 := bstep (se 1 (by rfl) ⟨587042, by rfl⟩ : syracuseStep 782723 = 1174085) B1174085
theorem B618883 : Blo 618297 618883 := bstep (se 1 (by rfl) ⟨464162, by rfl⟩ : syracuseStep 618883 = 928325) B928325
theorem B1175953 : Blo 618297 1175953 := bstep (se 2 (by rfl) ⟨440982, by rfl⟩ : syracuseStep 1175953 = 881965) B881965
theorem B618899 : Blo 618297 618899 := bstep (se 1 (by rfl) ⟨464174, by rfl⟩ : syracuseStep 618899 = 928349) B928349
theorem B618915 : Blo 618297 618915 := bstep (se 1 (by rfl) ⟨464186, by rfl⟩ : syracuseStep 618915 = 928373) B928373
theorem B1044913 : Blo 618297 1044913 := bstep (se 2 (by rfl) ⟨391842, by rfl⟩ : syracuseStep 1044913 = 783685) B783685
theorem B618931 : Blo 618297 618931 := bstep (se 1 (by rfl) ⟨464198, by rfl⟩ : syracuseStep 618931 = 928397) B928397
theorem B618947 : Blo 618297 618947 := bstep (se 1 (by rfl) ⟨464210, by rfl⟩ : syracuseStep 618947 = 928421) B928421
theorem B1569233 : Blo 618297 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B618963 : Blo 618297 618963 := bstep (se 1 (by rfl) ⟨464222, by rfl⟩ : syracuseStep 618963 = 928445) B928445
theorem B1044947 : Blo 618297 1044947 := bstep (se 1 (by rfl) ⟨783710, by rfl⟩ : syracuseStep 1044947 = 1567421) B1567421
theorem B618979 : Blo 618297 618979 := bstep (se 1 (by rfl) ⟨464234, by rfl⟩ : syracuseStep 618979 = 928469) B928469
theorem B618995 : Blo 618297 618995 := bstep (se 1 (by rfl) ⟨464246, by rfl⟩ : syracuseStep 618995 = 928493) B928493
theorem B619011 : Blo 618297 619011 := bstep (se 1 (by rfl) ⟨464258, by rfl⟩ : syracuseStep 619011 = 928517) B928517
theorem B1765901 : Blo 618297 1765901 := bstep (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) B662213
theorem B619027 : Blo 618297 619027 := bstep (se 1 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 619027 = 928541) B928541
theorem B619043 : Blo 618297 619043 := bstep (se 1 (by rfl) ⟨464282, by rfl⟩ : syracuseStep 619043 = 928565) B928565
theorem B1176113 : Blo 618297 1176113 := bstep (se 2 (by rfl) ⟨441042, by rfl⟩ : syracuseStep 1176113 = 882085) B882085
theorem B619059 : Blo 618297 619059 := bstep (se 1 (by rfl) ⟨464294, by rfl⟩ : syracuseStep 619059 = 928589) B928589
theorem B881219 : Blo 618297 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B619075 : Blo 618297 619075 := bstep (se 1 (by rfl) ⟨464306, by rfl⟩ : syracuseStep 619075 = 928613) B928613
theorem B619091 : Blo 618297 619091 := bstep (se 1 (by rfl) ⟨464318, by rfl⟩ : syracuseStep 619091 = 928637) B928637
theorem B1045075 : Blo 618297 1045075 := bstep (se 1 (by rfl) ⟨783806, by rfl⟩ : syracuseStep 1045075 = 1567613) B1567613
theorem B619107 : Blo 618297 619107 := bstep (se 1 (by rfl) ⟨464330, by rfl⟩ : syracuseStep 619107 = 928661) B928661
theorem B619123 : Blo 618297 619123 := bstep (se 1 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 619123 = 928685) B928685
theorem B619139 : Blo 618297 619139 := bstep (se 1 (by rfl) ⟨464354, by rfl⟩ : syracuseStep 619139 = 928709) B928709
theorem B2650765 : Blo 618297 2650765 := bstep (se 3 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 2650765 = 994037) B994037
theorem B619155 : Blo 618297 619155 := bstep (se 1 (by rfl) ⟨464366, by rfl⟩ : syracuseStep 619155 = 928733) B928733
theorem B619171 : Blo 618297 619171 := bstep (se 1 (by rfl) ⟨464378, by rfl⟩ : syracuseStep 619171 = 928757) B928757
theorem B2093741 : Blo 618297 2093741 := bstep (se 3 (by rfl) ⟨392576, by rfl⟩ : syracuseStep 2093741 = 785153) B785153
theorem B1340081 : Blo 618297 1340081 := bstep (se 2 (by rfl) ⟨502530, by rfl⟩ : syracuseStep 1340081 = 1005061) B1005061
theorem B619187 : Blo 618297 619187 := bstep (se 1 (by rfl) ⟨464390, by rfl⟩ : syracuseStep 619187 = 928781) B928781
theorem B619203 : Blo 618297 619203 := bstep (se 1 (by rfl) ⟨464402, by rfl⟩ : syracuseStep 619203 = 928805) B928805
theorem B1766083 : Blo 618297 1766083 := bstep (se 1 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 1766083 = 2649125) B2649125
theorem B619219 : Blo 618297 619219 := bstep (se 1 (by rfl) ⟨464414, by rfl⟩ : syracuseStep 619219 = 928829) B928829
theorem B1045217 : Blo 618297 1045217 := bstep (se 2 (by rfl) ⟨391956, by rfl⟩ : syracuseStep 1045217 = 783913) B783913
theorem B619235 : Blo 618297 619235 := bstep (se 1 (by rfl) ⟨464426, by rfl⟩ : syracuseStep 619235 = 928853) B928853
theorem B2093795 : Blo 618297 2093795 := bstep (se 1 (by rfl) ⟨1570346, by rfl⟩ : syracuseStep 2093795 = 3140693) B3140693
theorem B619251 : Blo 618297 619251 := bstep (se 1 (by rfl) ⟨464438, by rfl⟩ : syracuseStep 619251 = 928877) B928877
theorem B619267 : Blo 618297 619267 := bstep (se 1 (by rfl) ⟨464450, by rfl⟩ : syracuseStep 619267 = 928901) B928901
theorem B619283 : Blo 618297 619283 := bstep (se 1 (by rfl) ⟨464462, by rfl⟩ : syracuseStep 619283 = 928925) B928925
theorem B619299 : Blo 618297 619299 := bstep (se 1 (by rfl) ⟨464474, by rfl⟩ : syracuseStep 619299 = 928949) B928949
theorem B619315 : Blo 618297 619315 := bstep (se 1 (by rfl) ⟨464486, by rfl⟩ : syracuseStep 619315 = 928973) B928973
theorem B619331 : Blo 618297 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B619347 : Blo 618297 619347 := bstep (se 1 (by rfl) ⟨464510, by rfl⟩ : syracuseStep 619347 = 929021) B929021
theorem B1045345 : Blo 618297 1045345 := bstep (se 2 (by rfl) ⟨392004, by rfl⟩ : syracuseStep 1045345 = 784009) B784009
theorem B619363 : Blo 618297 619363 := bstep (se 1 (by rfl) ⟨464522, by rfl⟩ : syracuseStep 619363 = 929045) B929045
theorem B2356067 : Blo 618297 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B619379 : Blo 618297 619379 := bstep (se 1 (by rfl) ⟨464534, by rfl⟩ : syracuseStep 619379 = 929069) B929069
theorem B619395 : Blo 618297 619395 := bstep (se 1 (by rfl) ⟨464546, by rfl⟩ : syracuseStep 619395 = 929093) B929093
theorem B1045379 : Blo 618297 1045379 := bstep (se 1 (by rfl) ⟨784034, by rfl⟩ : syracuseStep 1045379 = 1568069) B1568069
theorem B619411 : Blo 618297 619411 := bstep (se 1 (by rfl) ⟨464558, by rfl⟩ : syracuseStep 619411 = 929117) B929117
theorem B619427 : Blo 618297 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B619443 : Blo 618297 619443 := bstep (se 1 (by rfl) ⟨464582, by rfl⟩ : syracuseStep 619443 = 929165) B929165
theorem B619459 : Blo 618297 619459 := bstep (se 1 (by rfl) ⟨464594, by rfl⟩ : syracuseStep 619459 = 929189) B929189
theorem B1176515 : Blo 618297 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B619475 : Blo 618297 619475 := bstep (se 1 (by rfl) ⟨464606, by rfl⟩ : syracuseStep 619475 = 929213) B929213
theorem B619491 : Blo 618297 619491 := bstep (se 1 (by rfl) ⟨464618, by rfl⟩ : syracuseStep 619491 = 929237) B929237
theorem B2094065 : Blo 618297 2094065 := bstep (se 2 (by rfl) ⟨785274, by rfl⟩ : syracuseStep 2094065 = 1570549) B1570549
theorem B619507 : Blo 618297 619507 := bstep (se 1 (by rfl) ⟨464630, by rfl⟩ : syracuseStep 619507 = 929261) B929261
theorem B619523 : Blo 618297 619523 := bstep (se 1 (by rfl) ⟨464642, by rfl⟩ : syracuseStep 619523 = 929285) B929285
theorem B1045507 : Blo 618297 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B619539 : Blo 618297 619539 := bstep (se 1 (by rfl) ⟨464654, by rfl⟩ : syracuseStep 619539 = 929309) B929309
theorem B619555 : Blo 618297 619555 := bstep (se 1 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 619555 = 929333) B929333
theorem B619571 : Blo 618297 619571 := bstep (se 1 (by rfl) ⟨464678, by rfl⟩ : syracuseStep 619571 = 929357) B929357
theorem B783427 : Blo 618297 783427 := bstep (se 1 (by rfl) ⟨587570, by rfl⟩ : syracuseStep 783427 = 1175141) B1175141
theorem B619587 : Blo 618297 619587 := bstep (se 1 (by rfl) ⟨464690, by rfl⟩ : syracuseStep 619587 = 929381) B929381
theorem B619603 : Blo 618297 619603 := bstep (se 1 (by rfl) ⟨464702, by rfl⟩ : syracuseStep 619603 = 929405) B929405
theorem B619619 : Blo 618297 619619 := bstep (se 1 (by rfl) ⟨464714, by rfl⟩ : syracuseStep 619619 = 929429) B929429
theorem B619635 : Blo 618297 619635 := bstep (se 1 (by rfl) ⟨464726, by rfl⟩ : syracuseStep 619635 = 929453) B929453
theorem B619651 : Blo 618297 619651 := bstep (se 1 (by rfl) ⟨464738, by rfl⟩ : syracuseStep 619651 = 929477) B929477
theorem B1045649 : Blo 618297 1045649 := bstep (se 2 (by rfl) ⟨392118, by rfl⟩ : syracuseStep 1045649 = 784237) B784237
theorem B619667 : Blo 618297 619667 := bstep (se 1 (by rfl) ⟨464750, by rfl⟩ : syracuseStep 619667 = 929501) B929501
theorem B783523 : Blo 618297 783523 := bstep (se 1 (by rfl) ⟨587642, by rfl⟩ : syracuseStep 783523 = 1175285) B1175285
theorem B619683 : Blo 618297 619683 := bstep (se 1 (by rfl) ⟨464762, by rfl⟩ : syracuseStep 619683 = 929525) B929525
theorem B1766573 : Blo 618297 1766573 := bstep (se 3 (by rfl) ⟨331232, by rfl⟩ : syracuseStep 1766573 = 662465) B662465
theorem B619699 : Blo 618297 619699 := bstep (se 1 (by rfl) ⟨464774, by rfl⟩ : syracuseStep 619699 = 929549) B929549
theorem B881857 : Blo 618297 881857 := bstep (se 2 (by rfl) ⟨330696, by rfl⟩ : syracuseStep 881857 = 661393) B661393
theorem B619715 : Blo 618297 619715 := bstep (se 1 (by rfl) ⟨464786, by rfl⟩ : syracuseStep 619715 = 929573) B929573
theorem B619731 : Blo 618297 619731 := bstep (se 1 (by rfl) ⟨464798, by rfl⟩ : syracuseStep 619731 = 929597) B929597
theorem B619747 : Blo 618297 619747 := bstep (se 1 (by rfl) ⟨464810, by rfl⟩ : syracuseStep 619747 = 929621) B929621
theorem B2651363 : Blo 618297 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B619763 : Blo 618297 619763 := bstep (se 1 (by rfl) ⟨464822, by rfl⟩ : syracuseStep 619763 = 929645) B929645
theorem B619779 : Blo 618297 619779 := bstep (se 1 (by rfl) ⟨464834, by rfl⟩ : syracuseStep 619779 = 929669) B929669
theorem B1045777 : Blo 618297 1045777 := bstep (se 2 (by rfl) ⟨392166, by rfl⟩ : syracuseStep 1045777 = 784333) B784333
theorem B619795 : Blo 618297 619795 := bstep (se 1 (by rfl) ⟨464846, by rfl⟩ : syracuseStep 619795 = 929693) B929693
theorem B619811 : Blo 618297 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B3142961 : Blo 618297 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B1045811 : Blo 618297 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B619827 : Blo 618297 619827 := bstep (se 1 (by rfl) ⟨464870, by rfl⟩ : syracuseStep 619827 = 929741) B929741
theorem B619843 : Blo 618297 619843 := bstep (se 1 (by rfl) ⟨464882, by rfl⟩ : syracuseStep 619843 = 929765) B929765
theorem B619859 : Blo 618297 619859 := bstep (se 1 (by rfl) ⟨464894, by rfl⟩ : syracuseStep 619859 = 929789) B929789
theorem B619875 : Blo 618297 619875 := bstep (se 1 (by rfl) ⟨464906, by rfl⟩ : syracuseStep 619875 = 929813) B929813
theorem B619891 : Blo 618297 619891 := bstep (se 1 (by rfl) ⟨464918, by rfl⟩ : syracuseStep 619891 = 929837) B929837
theorem B619907 : Blo 618297 619907 := bstep (se 1 (by rfl) ⟨464930, by rfl⟩ : syracuseStep 619907 = 929861) B929861
theorem B619923 : Blo 618297 619923 := bstep (se 1 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 619923 = 929885) B929885
theorem B619939 : Blo 618297 619939 := bstep (se 1 (by rfl) ⟨464954, by rfl⟩ : syracuseStep 619939 = 929909) B929909
theorem B1570225 : Blo 618297 1570225 := bstep (se 2 (by rfl) ⟨588834, by rfl⟩ : syracuseStep 1570225 = 1177669) B1177669
theorem B1045939 : Blo 618297 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B619955 : Blo 618297 619955 := bstep (se 1 (by rfl) ⟨464966, by rfl⟩ : syracuseStep 619955 = 929933) B929933
theorem B619971 : Blo 618297 619971 := bstep (se 1 (by rfl) ⟨464978, by rfl⟩ : syracuseStep 619971 = 929957) B929957
theorem B619987 : Blo 618297 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B620003 : Blo 618297 620003 := bstep (se 1 (by rfl) ⟨465002, by rfl⟩ : syracuseStep 620003 = 930005) B930005
theorem B2356721 : Blo 618297 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B620019 : Blo 618297 620019 := bstep (se 1 (by rfl) ⟨465014, by rfl⟩ : syracuseStep 620019 = 930029) B930029
theorem B620035 : Blo 618297 620035 := bstep (se 1 (by rfl) ⟨465026, by rfl⟩ : syracuseStep 620035 = 930053) B930053
theorem B2094605 : Blo 618297 2094605 := bstep (se 3 (by rfl) ⟨392738, by rfl⟩ : syracuseStep 2094605 = 785477) B785477
theorem B882193 : Blo 618297 882193 := bstep (se 2 (by rfl) ⟨330822, by rfl⟩ : syracuseStep 882193 = 661645) B661645
theorem B620051 : Blo 618297 620051 := bstep (se 1 (by rfl) ⟨465038, by rfl⟩ : syracuseStep 620051 = 930077) B930077
theorem B620067 : Blo 618297 620067 := bstep (se 1 (by rfl) ⟨465050, by rfl⟩ : syracuseStep 620067 = 930101) B930101
theorem B620083 : Blo 618297 620083 := bstep (se 1 (by rfl) ⟨465062, by rfl⟩ : syracuseStep 620083 = 930125) B930125
theorem B1046081 : Blo 618297 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B620099 : Blo 618297 620099 := bstep (se 1 (by rfl) ⟨465074, by rfl⟩ : syracuseStep 620099 = 930149) B930149
theorem B2094659 : Blo 618297 2094659 := bstep (se 1 (by rfl) ⟨1570994, by rfl⟩ : syracuseStep 2094659 = 3141989) B3141989
theorem B7960133 : Blo 618297 7960133 := bstep (se 4 (by rfl) ⟨746262, by rfl⟩ : syracuseStep 7960133 = 1492525) B1492525
theorem B620115 : Blo 618297 620115 := bstep (se 1 (by rfl) ⟨465086, by rfl⟩ : syracuseStep 620115 = 930173) B930173
theorem B620131 : Blo 618297 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B620147 : Blo 618297 620147 := bstep (se 1 (by rfl) ⟨465110, by rfl⟩ : syracuseStep 620147 = 930221) B930221
theorem B620163 : Blo 618297 620163 := bstep (se 1 (by rfl) ⟨465122, by rfl⟩ : syracuseStep 620163 = 930245) B930245
theorem B784019 : Blo 618297 784019 := bstep (se 1 (by rfl) ⟨588014, by rfl⟩ : syracuseStep 784019 = 1176029) B1176029
theorem B620179 : Blo 618297 620179 := bstep (se 1 (by rfl) ⟨465134, by rfl⟩ : syracuseStep 620179 = 930269) B930269
theorem B620195 : Blo 618297 620195 := bstep (se 1 (by rfl) ⟨465146, by rfl⟩ : syracuseStep 620195 = 930293) B930293
theorem B3536561 : Blo 618297 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B620211 : Blo 618297 620211 := bstep (se 1 (by rfl) ⟨465158, by rfl⟩ : syracuseStep 620211 = 930317) B930317
theorem B1046209 : Blo 618297 1046209 := bstep (se 2 (by rfl) ⟨392328, by rfl⟩ : syracuseStep 1046209 = 784657) B784657
theorem B620227 : Blo 618297 620227 := bstep (se 1 (by rfl) ⟨465170, by rfl⟩ : syracuseStep 620227 = 930341) B930341
theorem B1570499 : Blo 618297 1570499 := bstep (se 1 (by rfl) ⟨1177874, by rfl⟩ : syracuseStep 1570499 = 2355749) B2355749
theorem B620243 : Blo 618297 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B1046243 : Blo 618297 1046243 := bstep (se 1 (by rfl) ⟨784682, by rfl⟩ : syracuseStep 1046243 = 1569365) B1569365
theorem B620259 : Blo 618297 620259 := bstep (se 1 (by rfl) ⟨465194, by rfl⟩ : syracuseStep 620259 = 930389) B930389
theorem B620275 : Blo 618297 620275 := bstep (se 1 (by rfl) ⟨465206, by rfl⟩ : syracuseStep 620275 = 930413) B930413
theorem B620291 : Blo 618297 620291 := bstep (se 1 (by rfl) ⟨465218, by rfl⟩ : syracuseStep 620291 = 930437) B930437
theorem B620307 : Blo 618297 620307 := bstep (se 1 (by rfl) ⟨465230, by rfl⟩ : syracuseStep 620307 = 930461) B930461
theorem B620323 : Blo 618297 620323 := bstep (se 1 (by rfl) ⟨465242, by rfl⟩ : syracuseStep 620323 = 930485) B930485
theorem B620339 : Blo 618297 620339 := bstep (se 1 (by rfl) ⟨465254, by rfl⟩ : syracuseStep 620339 = 930509) B930509
theorem B1177411 : Blo 618297 1177411 := bstep (se 1 (by rfl) ⟨883058, by rfl⟩ : syracuseStep 1177411 = 1766117) B1766117
theorem B620355 : Blo 618297 620355 := bstep (se 1 (by rfl) ⟨465266, by rfl⟩ : syracuseStep 620355 = 930533) B930533
theorem B2094929 : Blo 618297 2094929 := bstep (se 2 (by rfl) ⟨785598, by rfl⟩ : syracuseStep 2094929 = 1571197) B1571197
theorem B620371 : Blo 618297 620371 := bstep (se 1 (by rfl) ⟨465278, by rfl⟩ : syracuseStep 620371 = 930557) B930557
theorem B1046371 : Blo 618297 1046371 := bstep (se 1 (by rfl) ⟨784778, by rfl⟩ : syracuseStep 1046371 = 1569557) B1569557
theorem B620387 : Blo 618297 620387 := bstep (se 1 (by rfl) ⟨465290, by rfl⟩ : syracuseStep 620387 = 930581) B930581
theorem B620403 : Blo 618297 620403 := bstep (se 1 (by rfl) ⟨465302, by rfl⟩ : syracuseStep 620403 = 930605) B930605
theorem B620419 : Blo 618297 620419 := bstep (se 1 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 620419 = 930629) B930629
theorem B1570691 : Blo 618297 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B2520973 : Blo 618297 2520973 := bstep (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) B945365
theorem B620435 : Blo 618297 620435 := bstep (se 1 (by rfl) ⟨465326, by rfl⟩ : syracuseStep 620435 = 930653) B930653
theorem B620451 : Blo 618297 620451 := bstep (se 1 (by rfl) ⟨465338, by rfl⟩ : syracuseStep 620451 = 930677) B930677
theorem B620467 : Blo 618297 620467 := bstep (se 1 (by rfl) ⟨465350, by rfl⟩ : syracuseStep 620467 = 930701) B930701
theorem B620483 : Blo 618297 620483 := bstep (se 1 (by rfl) ⟨465362, by rfl⟩ : syracuseStep 620483 = 930725) B930725
theorem B620499 : Blo 618297 620499 := bstep (se 1 (by rfl) ⟨465374, by rfl⟩ : syracuseStep 620499 = 930749) B930749
theorem B1177571 : Blo 618297 1177571 := bstep (se 1 (by rfl) ⟨883178, by rfl⟩ : syracuseStep 1177571 = 1766357) B1766357
theorem B620515 : Blo 618297 620515 := bstep (se 1 (by rfl) ⟨465386, by rfl⟩ : syracuseStep 620515 = 930773) B930773
theorem B1046513 : Blo 618297 1046513 := bstep (se 2 (by rfl) ⟨392442, by rfl⟩ : syracuseStep 1046513 = 784885) B784885
theorem B620531 : Blo 618297 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B620547 : Blo 618297 620547 := bstep (se 1 (by rfl) ⟨465410, by rfl⟩ : syracuseStep 620547 = 930821) B930821
theorem B620563 : Blo 618297 620563 := bstep (se 1 (by rfl) ⟨465422, by rfl⟩ : syracuseStep 620563 = 930845) B930845
theorem B620579 : Blo 618297 620579 := bstep (se 1 (by rfl) ⟨465434, by rfl⟩ : syracuseStep 620579 = 930869) B930869
theorem B620595 : Blo 618297 620595 := bstep (se 1 (by rfl) ⟨465446, by rfl⟩ : syracuseStep 620595 = 930893) B930893
theorem B620611 : Blo 618297 620611 := bstep (se 1 (by rfl) ⟨465458, by rfl⟩ : syracuseStep 620611 = 930917) B930917
theorem B620627 : Blo 618297 620627 := bstep (se 1 (by rfl) ⟨465470, by rfl⟩ : syracuseStep 620627 = 930941) B930941
theorem B882785 : Blo 618297 882785 := bstep (se 2 (by rfl) ⟨331044, by rfl⟩ : syracuseStep 882785 = 662089) B662089
theorem B620643 : Blo 618297 620643 := bstep (se 1 (by rfl) ⟨465482, by rfl⟩ : syracuseStep 620643 = 930965) B930965
theorem B1046641 : Blo 618297 1046641 := bstep (se 2 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 1046641 = 784981) B784981
theorem B620659 : Blo 618297 620659 := bstep (se 1 (by rfl) ⟨465494, by rfl⟩ : syracuseStep 620659 = 930989) B930989
theorem B620675 : Blo 618297 620675 := bstep (se 1 (by rfl) ⟨465506, by rfl⟩ : syracuseStep 620675 = 931013) B931013
theorem B1046675 : Blo 618297 1046675 := bstep (se 1 (by rfl) ⟨785006, by rfl⟩ : syracuseStep 1046675 = 1570013) B1570013
theorem B620691 : Blo 618297 620691 := bstep (se 1 (by rfl) ⟨465518, by rfl⟩ : syracuseStep 620691 = 931037) B931037
theorem B620707 : Blo 618297 620707 := bstep (se 1 (by rfl) ⟨465530, by rfl⟩ : syracuseStep 620707 = 931061) B931061
theorem B620723 : Blo 618297 620723 := bstep (se 1 (by rfl) ⟨465542, by rfl⟩ : syracuseStep 620723 = 931085) B931085
theorem B620739 : Blo 618297 620739 := bstep (se 1 (by rfl) ⟨465554, by rfl⟩ : syracuseStep 620739 = 931109) B931109
theorem B620755 : Blo 618297 620755 := bstep (se 1 (by rfl) ⟨465566, by rfl⟩ : syracuseStep 620755 = 931133) B931133
theorem B620771 : Blo 618297 620771 := bstep (se 1 (by rfl) ⟨465578, by rfl⟩ : syracuseStep 620771 = 931157) B931157
theorem B620787 : Blo 618297 620787 := bstep (se 1 (by rfl) ⟨465590, by rfl⟩ : syracuseStep 620787 = 931181) B931181
theorem B620803 : Blo 618297 620803 := bstep (se 1 (by rfl) ⟨465602, by rfl⟩ : syracuseStep 620803 = 931205) B931205
theorem B1046803 : Blo 618297 1046803 := bstep (se 1 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 1046803 = 1570205) B1570205
theorem B620819 : Blo 618297 620819 := bstep (se 1 (by rfl) ⟨465614, by rfl⟩ : syracuseStep 620819 = 931229) B931229
theorem B620835 : Blo 618297 620835 := bstep (se 1 (by rfl) ⟨465626, by rfl⟩ : syracuseStep 620835 = 931253) B931253
theorem B620851 : Blo 618297 620851 := bstep (se 1 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 620851 = 931277) B931277
theorem B15890741 : Blo 618297 15890741 := bstep (se 5 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 15890741 = 1489757) B1489757
theorem B620867 : Blo 618297 620867 := bstep (se 1 (by rfl) ⟨465650, by rfl⟩ : syracuseStep 620867 = 931301) B931301
theorem B1767757 : Blo 618297 1767757 := bstep (se 3 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 1767757 = 662909) B662909
theorem B784723 : Blo 618297 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B620883 : Blo 618297 620883 := bstep (se 1 (by rfl) ⟨465662, by rfl⟩ : syracuseStep 620883 = 931325) B931325
theorem B620899 : Blo 618297 620899 := bstep (se 1 (by rfl) ⟨465674, by rfl⟩ : syracuseStep 620899 = 931349) B931349
theorem B2095469 : Blo 618297 2095469 := bstep (se 3 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 2095469 = 785801) B785801
theorem B620915 : Blo 618297 620915 := bstep (se 1 (by rfl) ⟨465686, by rfl⟩ : syracuseStep 620915 = 931373) B931373
theorem B620931 : Blo 618297 620931 := bstep (se 1 (by rfl) ⟨465698, by rfl⟩ : syracuseStep 620931 = 931397) B931397
theorem B620947 : Blo 618297 620947 := bstep (se 1 (by rfl) ⟨465710, by rfl⟩ : syracuseStep 620947 = 931421) B931421
theorem B1046945 : Blo 618297 1046945 := bstep (se 2 (by rfl) ⟨392604, by rfl⟩ : syracuseStep 1046945 = 785209) B785209
theorem B2095523 : Blo 618297 2095523 := bstep (se 1 (by rfl) ⟨1571642, by rfl⟩ : syracuseStep 2095523 = 3143285) B3143285
theorem B620963 : Blo 618297 620963 := bstep (se 1 (by rfl) ⟨465722, by rfl⟩ : syracuseStep 620963 = 931445) B931445
theorem B784819 : Blo 618297 784819 := bstep (se 1 (by rfl) ⟨588614, by rfl⟩ : syracuseStep 784819 = 1177229) B1177229
theorem B620979 : Blo 618297 620979 := bstep (se 1 (by rfl) ⟨465734, by rfl⟩ : syracuseStep 620979 = 931469) B931469
theorem B620995 : Blo 618297 620995 := bstep (se 1 (by rfl) ⟨465746, by rfl⟩ : syracuseStep 620995 = 931493) B931493
theorem B621011 : Blo 618297 621011 := bstep (se 1 (by rfl) ⟨465758, by rfl⟩ : syracuseStep 621011 = 931517) B931517
theorem B621027 : Blo 618297 621027 := bstep (se 1 (by rfl) ⟨465770, by rfl⟩ : syracuseStep 621027 = 931541) B931541
theorem B621043 : Blo 618297 621043 := bstep (se 1 (by rfl) ⟨465782, by rfl⟩ : syracuseStep 621043 = 931565) B931565
theorem B621059 : Blo 618297 621059 := bstep (se 1 (by rfl) ⟨465794, by rfl⟩ : syracuseStep 621059 = 931589) B931589
theorem B7043597 : Blo 618297 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B621075 : Blo 618297 621075 := bstep (se 1 (by rfl) ⟨465806, by rfl⟩ : syracuseStep 621075 = 931613) B931613
theorem B1047073 : Blo 618297 1047073 := bstep (se 2 (by rfl) ⟨392652, by rfl⟩ : syracuseStep 1047073 = 785305) B785305
theorem B621091 : Blo 618297 621091 := bstep (se 1 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 621091 = 931637) B931637
theorem B621107 : Blo 618297 621107 := bstep (se 1 (by rfl) ⟨465830, by rfl⟩ : syracuseStep 621107 = 931661) B931661
theorem B1047107 : Blo 618297 1047107 := bstep (se 1 (by rfl) ⟨785330, by rfl⟩ : syracuseStep 1047107 = 1570661) B1570661
theorem B621123 : Blo 618297 621123 := bstep (se 1 (by rfl) ⟨465842, by rfl⟩ : syracuseStep 621123 = 931685) B931685
theorem B621139 : Blo 618297 621139 := bstep (se 1 (by rfl) ⟨465854, by rfl⟩ : syracuseStep 621139 = 931709) B931709
theorem B621155 : Blo 618297 621155 := bstep (se 1 (by rfl) ⟨465866, by rfl⟩ : syracuseStep 621155 = 931733) B931733
theorem B883315 : Blo 618297 883315 := bstep (se 1 (by rfl) ⟨662486, by rfl⟩ : syracuseStep 883315 = 1324973) B1324973
theorem B621171 : Blo 618297 621171 := bstep (se 1 (by rfl) ⟨465878, by rfl⟩ : syracuseStep 621171 = 931757) B931757
theorem B621187 : Blo 618297 621187 := bstep (se 1 (by rfl) ⟨465890, by rfl⟩ : syracuseStep 621187 = 931781) B931781
theorem B4291213 : Blo 618297 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B621203 : Blo 618297 621203 := bstep (se 1 (by rfl) ⟨465902, by rfl⟩ : syracuseStep 621203 = 931805) B931805
theorem B621219 : Blo 618297 621219 := bstep (se 1 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 621219 = 931829) B931829
theorem B2095793 : Blo 618297 2095793 := bstep (se 2 (by rfl) ⟨785922, by rfl⟩ : syracuseStep 2095793 = 1571845) B1571845
theorem B621235 : Blo 618297 621235 := bstep (se 1 (by rfl) ⟨465926, by rfl⟩ : syracuseStep 621235 = 931853) B931853
theorem B1047235 : Blo 618297 1047235 := bstep (se 1 (by rfl) ⟨785426, by rfl⟩ : syracuseStep 1047235 = 1570853) B1570853
theorem B621251 : Blo 618297 621251 := bstep (se 1 (by rfl) ⟨465938, by rfl⟩ : syracuseStep 621251 = 931877) B931877
theorem B621267 : Blo 618297 621267 := bstep (se 1 (by rfl) ⟨465950, by rfl⟩ : syracuseStep 621267 = 931901) B931901
theorem B3144419 : Blo 618297 3144419 := bstep (se 1 (by rfl) ⟨2358314, by rfl⟩ : syracuseStep 3144419 = 4716629) B4716629
theorem B621283 : Blo 618297 621283 := bstep (se 1 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 621283 = 931925) B931925
theorem B621299 : Blo 618297 621299 := bstep (se 1 (by rfl) ⟨465974, by rfl⟩ : syracuseStep 621299 = 931949) B931949
theorem B621315 : Blo 618297 621315 := bstep (se 1 (by rfl) ⟨465986, by rfl⟩ : syracuseStep 621315 = 931973) B931973
theorem B621331 : Blo 618297 621331 := bstep (se 1 (by rfl) ⟨465998, by rfl⟩ : syracuseStep 621331 = 931997) B931997
theorem B621347 : Blo 618297 621347 := bstep (se 1 (by rfl) ⟨466010, by rfl⟩ : syracuseStep 621347 = 932021) B932021
theorem B1571633 : Blo 618297 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B621363 : Blo 618297 621363 := bstep (se 1 (by rfl) ⟨466022, by rfl⟩ : syracuseStep 621363 = 932045) B932045
theorem B621379 : Blo 618297 621379 := bstep (se 1 (by rfl) ⟨466034, by rfl⟩ : syracuseStep 621379 = 932069) B932069
theorem B1047377 : Blo 618297 1047377 := bstep (se 2 (by rfl) ⟨392766, by rfl⟩ : syracuseStep 1047377 = 785533) B785533
theorem B621395 : Blo 618297 621395 := bstep (se 1 (by rfl) ⟨466046, by rfl⟩ : syracuseStep 621395 = 932093) B932093
theorem B1571683 : Blo 618297 1571683 := bstep (se 1 (by rfl) ⟨1178762, by rfl⟩ : syracuseStep 1571683 = 2357525) B2357525
theorem B621411 : Blo 618297 621411 := bstep (se 1 (by rfl) ⟨466058, by rfl⟩ : syracuseStep 621411 = 932117) B932117
theorem B2390897 : Blo 618297 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B621427 : Blo 618297 621427 := bstep (se 1 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 621427 = 932141) B932141
theorem B621443 : Blo 618297 621443 := bstep (se 1 (by rfl) ⟨466082, by rfl⟩ : syracuseStep 621443 = 932165) B932165
theorem B621459 : Blo 618297 621459 := bstep (se 1 (by rfl) ⟨466094, by rfl⟩ : syracuseStep 621459 = 932189) B932189
theorem B785315 : Blo 618297 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B2358179 : Blo 618297 2358179 := bstep (se 1 (by rfl) ⟨1768634, by rfl⟩ : syracuseStep 2358179 = 3537269) B3537269
theorem B621475 : Blo 618297 621475 := bstep (se 1 (by rfl) ⟨466106, by rfl⟩ : syracuseStep 621475 = 932213) B932213
theorem B2358193 : Blo 618297 2358193 := bstep (se 2 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 2358193 = 1768645) B1768645
theorem B621491 : Blo 618297 621491 := bstep (se 1 (by rfl) ⟨466118, by rfl⟩ : syracuseStep 621491 = 932237) B932237
theorem B883651 : Blo 618297 883651 := bstep (se 1 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 883651 = 1325477) B1325477
theorem B621507 : Blo 618297 621507 := bstep (se 1 (by rfl) ⟨466130, by rfl⟩ : syracuseStep 621507 = 932261) B932261
theorem B1047505 : Blo 618297 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B621523 : Blo 618297 621523 := bstep (se 1 (by rfl) ⟨466142, by rfl⟩ : syracuseStep 621523 = 932285) B932285
theorem B621539 : Blo 618297 621539 := bstep (se 1 (by rfl) ⟨466154, by rfl⟩ : syracuseStep 621539 = 932309) B932309
theorem B1571825 : Blo 618297 1571825 := bstep (se 2 (by rfl) ⟨589434, by rfl⟩ : syracuseStep 1571825 = 1178869) B1178869
theorem B1047539 : Blo 618297 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B621555 : Blo 618297 621555 := bstep (se 1 (by rfl) ⟨466166, by rfl⟩ : syracuseStep 621555 = 932333) B932333
theorem B621571 : Blo 618297 621571 := bstep (se 1 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 621571 = 932357) B932357
theorem B1178641 : Blo 618297 1178641 := bstep (se 2 (by rfl) ⟨441990, by rfl⟩ : syracuseStep 1178641 = 883981) B883981
theorem B621587 : Blo 618297 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B621603 : Blo 618297 621603 := bstep (se 1 (by rfl) ⟨466202, by rfl⟩ : syracuseStep 621603 = 932405) B932405
theorem B621619 : Blo 618297 621619 := bstep (se 1 (by rfl) ⟨466214, by rfl⟩ : syracuseStep 621619 = 932429) B932429
theorem B621635 : Blo 618297 621635 := bstep (se 1 (by rfl) ⟨466226, by rfl⟩ : syracuseStep 621635 = 932453) B932453
theorem B621651 : Blo 618297 621651 := bstep (se 1 (by rfl) ⟨466238, by rfl⟩ : syracuseStep 621651 = 932477) B932477
theorem B3538019 : Blo 618297 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B621667 : Blo 618297 621667 := bstep (se 1 (by rfl) ⟨466250, by rfl⟩ : syracuseStep 621667 = 932501) B932501
theorem B1047667 : Blo 618297 1047667 := bstep (se 1 (by rfl) ⟨785750, by rfl⟩ : syracuseStep 1047667 = 1571501) B1571501
theorem B621683 : Blo 618297 621683 := bstep (se 1 (by rfl) ⟨466262, by rfl⟩ : syracuseStep 621683 = 932525) B932525
theorem B621699 : Blo 618297 621699 := bstep (se 1 (by rfl) ⟨466274, by rfl⟩ : syracuseStep 621699 = 932549) B932549
theorem B621715 : Blo 618297 621715 := bstep (se 1 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 621715 = 932573) B932573
theorem B621731 : Blo 618297 621731 := bstep (se 1 (by rfl) ⟨466298, by rfl⟩ : syracuseStep 621731 = 932597) B932597
theorem B621747 : Blo 618297 621747 := bstep (se 1 (by rfl) ⟨466310, by rfl⟩ : syracuseStep 621747 = 932621) B932621
theorem B621763 : Blo 618297 621763 := bstep (se 1 (by rfl) ⟨466322, by rfl⟩ : syracuseStep 621763 = 932645) B932645
theorem B3177677 : Blo 618297 3177677 := bstep (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) B1191629
theorem B2096333 : Blo 618297 2096333 := bstep (se 3 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 2096333 = 786125) B786125
theorem B621779 : Blo 618297 621779 := bstep (se 1 (by rfl) ⟨466334, by rfl⟩ : syracuseStep 621779 = 932669) B932669
theorem B621795 : Blo 618297 621795 := bstep (se 1 (by rfl) ⟨466346, by rfl⟩ : syracuseStep 621795 = 932693) B932693
theorem B621811 : Blo 618297 621811 := bstep (se 1 (by rfl) ⟨466358, by rfl⟩ : syracuseStep 621811 = 932717) B932717
theorem B1047809 : Blo 618297 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B2096387 : Blo 618297 2096387 := bstep (se 1 (by rfl) ⟨1572290, by rfl⟩ : syracuseStep 2096387 = 3144581) B3144581
theorem B621827 : Blo 618297 621827 := bstep (se 1 (by rfl) ⟨466370, by rfl⟩ : syracuseStep 621827 = 932741) B932741
theorem B621843 : Blo 618297 621843 := bstep (se 1 (by rfl) ⟨466382, by rfl⟩ : syracuseStep 621843 = 932765) B932765
theorem B621859 : Blo 618297 621859 := bstep (se 1 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 621859 = 932789) B932789
theorem B621875 : Blo 618297 621875 := bstep (se 1 (by rfl) ⟨466406, by rfl⟩ : syracuseStep 621875 = 932813) B932813
theorem B621891 : Blo 618297 621891 := bstep (se 1 (by rfl) ⟨466418, by rfl⟩ : syracuseStep 621891 = 932837) B932837
theorem B621907 : Blo 618297 621907 := bstep (se 1 (by rfl) ⟨466430, by rfl⟩ : syracuseStep 621907 = 932861) B932861
theorem B621923 : Blo 618297 621923 := bstep (se 1 (by rfl) ⟨466442, by rfl⟩ : syracuseStep 621923 = 932885) B932885
theorem B1768817 : Blo 618297 1768817 := bstep (se 2 (by rfl) ⟨663306, by rfl⟩ : syracuseStep 1768817 = 1326613) B1326613
theorem B621939 : Blo 618297 621939 := bstep (se 1 (by rfl) ⟨466454, by rfl⟩ : syracuseStep 621939 = 932909) B932909
theorem B1047937 : Blo 618297 1047937 := bstep (se 2 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 1047937 = 785953) B785953
theorem B621955 : Blo 618297 621955 := bstep (se 1 (by rfl) ⟨466466, by rfl⟩ : syracuseStep 621955 = 932933) B932933
theorem B621971 : Blo 618297 621971 := bstep (se 1 (by rfl) ⟨466478, by rfl⟩ : syracuseStep 621971 = 932957) B932957
theorem B1047971 : Blo 618297 1047971 := bstep (se 1 (by rfl) ⟨785978, by rfl⟩ : syracuseStep 1047971 = 1571957) B1571957
theorem B621987 : Blo 618297 621987 := bstep (se 1 (by rfl) ⟨466490, by rfl⟩ : syracuseStep 621987 = 932981) B932981
theorem B622003 : Blo 618297 622003 := bstep (se 1 (by rfl) ⟨466502, by rfl⟩ : syracuseStep 622003 = 933005) B933005
theorem B622019 : Blo 618297 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B622035 : Blo 618297 622035 := bstep (se 1 (by rfl) ⟨466526, by rfl⟩ : syracuseStep 622035 = 933053) B933053
theorem B622051 : Blo 618297 622051 := bstep (se 1 (by rfl) ⟨466538, by rfl⟩ : syracuseStep 622051 = 933077) B933077
theorem B1703405 : Blo 618297 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B884209 : Blo 618297 884209 := bstep (se 2 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 884209 = 663157) B663157
theorem B622067 : Blo 618297 622067 := bstep (se 1 (by rfl) ⟨466550, by rfl⟩ : syracuseStep 622067 = 933101) B933101
theorem B622083 : Blo 618297 622083 := bstep (se 1 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 622083 = 933125) B933125
theorem B3145229 : Blo 618297 3145229 := bstep (se 3 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 3145229 = 1179461) B1179461
theorem B2096657 : Blo 618297 2096657 := bstep (se 2 (by rfl) ⟨786246, by rfl⟩ : syracuseStep 2096657 = 1572493) B1572493
theorem B884243 : Blo 618297 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B622099 : Blo 618297 622099 := bstep (se 1 (by rfl) ⟨466574, by rfl⟩ : syracuseStep 622099 = 933149) B933149
theorem B1048099 : Blo 618297 1048099 := bstep (se 1 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 1048099 = 1572149) B1572149
theorem B622115 : Blo 618297 622115 := bstep (se 1 (by rfl) ⟨466586, by rfl⟩ : syracuseStep 622115 = 933173) B933173
theorem B622131 : Blo 618297 622131 := bstep (se 1 (by rfl) ⟨466598, by rfl⟩ : syracuseStep 622131 = 933197) B933197
theorem B622147 : Blo 618297 622147 := bstep (se 1 (by rfl) ⟨466610, by rfl⟩ : syracuseStep 622147 = 933221) B933221
theorem B622163 : Blo 618297 622163 := bstep (se 1 (by rfl) ⟨466622, by rfl⟩ : syracuseStep 622163 = 933245) B933245
theorem B786019 : Blo 618297 786019 := bstep (se 1 (by rfl) ⟨589514, by rfl⟩ : syracuseStep 786019 = 1179029) B1179029
theorem B622179 : Blo 618297 622179 := bstep (se 1 (by rfl) ⟨466634, by rfl⟩ : syracuseStep 622179 = 933269) B933269
theorem B622195 : Blo 618297 622195 := bstep (se 1 (by rfl) ⟨466646, by rfl⟩ : syracuseStep 622195 = 933293) B933293
theorem B622211 : Blo 618297 622211 := bstep (se 1 (by rfl) ⟨466658, by rfl⟩ : syracuseStep 622211 = 933317) B933317
theorem B622227 : Blo 618297 622227 := bstep (se 1 (by rfl) ⟨466670, by rfl⟩ : syracuseStep 622227 = 933341) B933341
theorem B622243 : Blo 618297 622243 := bstep (se 1 (by rfl) ⟨466682, by rfl⟩ : syracuseStep 622243 = 933365) B933365
theorem B1048241 : Blo 618297 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B622259 : Blo 618297 622259 := bstep (se 1 (by rfl) ⟨466694, by rfl⟩ : syracuseStep 622259 = 933389) B933389
theorem B786115 : Blo 618297 786115 := bstep (se 1 (by rfl) ⟨589586, by rfl⟩ : syracuseStep 786115 = 1179173) B1179173
theorem B622275 : Blo 618297 622275 := bstep (se 1 (by rfl) ⟨466706, by rfl⟩ : syracuseStep 622275 = 933413) B933413
theorem B622291 : Blo 618297 622291 := bstep (se 1 (by rfl) ⟨466718, by rfl⟩ : syracuseStep 622291 = 933437) B933437
theorem B851681 : Blo 618297 851681 := bstep (se 2 (by rfl) ⟨319380, by rfl⟩ : syracuseStep 851681 = 638761) B638761
theorem B1048369 : Blo 618297 1048369 := bstep (se 2 (by rfl) ⟨393138, by rfl⟩ : syracuseStep 1048369 = 786277) B786277
theorem B1048403 : Blo 618297 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B1572817 : Blo 618297 1572817 := bstep (se 2 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 1572817 = 1179613) B1179613
theorem B1048531 : Blo 618297 1048531 := bstep (se 1 (by rfl) ⟨786398, by rfl⟩ : syracuseStep 1048531 = 1572797) B1572797
theorem B1179659 : Blo 618297 1179659 := bstep (se 1 (by rfl) ⟨884744, by rfl⟩ : syracuseStep 1179659 = 1769489) B1769489
theorem B1572929 : Blo 618297 1572929 := bstep (se 2 (by rfl) ⟨589848, by rfl⟩ : syracuseStep 1572929 = 1179697) B1179697
theorem B1048727 : Blo 618297 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B2359469 : Blo 618297 2359469 := bstep (se 3 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 2359469 = 884801) B884801
theorem B1179841 : Blo 618297 1179841 := bstep (se 2 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 1179841 = 884881) B884881
theorem B1048855 : Blo 618297 1048855 := bstep (se 1 (by rfl) ⟨786641, by rfl⟩ : syracuseStep 1048855 = 1573283) B1573283
theorem B1114393 : Blo 618297 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B4784429 : Blo 618297 4784429 := bstep (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) B1794161
theorem B786763 : Blo 618297 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B1769921 : Blo 618297 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B3146201 : Blo 618297 3146201 := bstep (se 2 (by rfl) ⟨1179825, by rfl⟩ : syracuseStep 3146201 = 2359651) B2359651
theorem B2097629 : Blo 618297 2097629 := bstep (se 3 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 2097629 = 786611) B786611
theorem B2556419 : Blo 618297 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B1180183 : Blo 618297 1180183 := bstep (se 1 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 1180183 = 1770275) B1770275
theorem B1573465 : Blo 618297 1573465 := bstep (se 2 (by rfl) ⟨590049, by rfl⟩ : syracuseStep 1573465 = 1180099) B1180099
theorem B1180403 : Blo 618297 1180403 := bstep (se 1 (by rfl) ⟨885302, by rfl⟩ : syracuseStep 1180403 = 1770605) B1770605
theorem B1114955 : Blo 618297 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B885593 : Blo 618297 885593 := bstep (se 2 (by rfl) ⟨332097, by rfl⟩ : syracuseStep 885593 = 664195) B664195
theorem B1049483 : Blo 618297 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B2655155 : Blo 618297 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B1180631 : Blo 618297 1180631 := bstep (se 1 (by rfl) ⟨885473, by rfl⟩ : syracuseStep 1180631 = 1770947) B1770947
theorem B1770457 : Blo 618297 1770457 := bstep (se 2 (by rfl) ⟨663921, by rfl⟩ : syracuseStep 1770457 = 1327843) B1327843
theorem B1049611 : Blo 618297 1049611 := bstep (se 1 (by rfl) ⟨787208, by rfl⟩ : syracuseStep 1049611 = 1574417) B1574417
theorem B2982977 : Blo 618297 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B1049753 : Blo 618297 1049753 := bstep (se 2 (by rfl) ⟨393657, by rfl⟩ : syracuseStep 1049753 = 787315) B787315
theorem B3540185 : Blo 618297 3540185 := bstep (se 2 (by rfl) ⟨1327569, by rfl⟩ : syracuseStep 3540185 = 2655139) B2655139
theorem B1180889 : Blo 618297 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B1049881 : Blo 618297 1049881 := bstep (se 2 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 1049881 = 787411) B787411
theorem B2229707 : Blo 618297 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B2360897 : Blo 618297 2360897 := bstep (se 2 (by rfl) ⟨885336, by rfl⟩ : syracuseStep 2360897 = 1770673) B1770673
theorem B2098763 : Blo 618297 2098763 := bstep (se 1 (by rfl) ⟨1574072, by rfl⟩ : syracuseStep 2098763 = 3148145) B3148145
theorem B1181299 : Blo 618297 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B1115777 : Blo 618297 1115777 := bstep (se 2 (by rfl) ⟨418416, by rfl⟩ : syracuseStep 1115777 = 836833) B836833
theorem B1574579 : Blo 618297 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B3180305 : Blo 618297 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B1115993 : Blo 618297 1115993 := bstep (se 2 (by rfl) ⟨418497, by rfl⟩ : syracuseStep 1115993 = 836995) B836995
theorem B2099033 : Blo 618297 2099033 := bstep (se 2 (by rfl) ⟨787137, by rfl⟩ : syracuseStep 2099033 = 1574275) B1574275
theorem B1574873 : Blo 618297 1574873 := bstep (se 2 (by rfl) ⟨590577, by rfl⟩ : syracuseStep 1574873 = 1181155) B1181155
theorem B3147821 : Blo 618297 3147821 := bstep (se 3 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 3147821 = 1180433) B1180433
theorem B3967127 : Blo 618297 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B30214295 : Blo 618297 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B5966257 : Blo 618297 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B2099735 : Blo 618297 2099735 := bstep (se 1 (by rfl) ⟨1574801, by rfl⟩ : syracuseStep 2099735 = 3149603) B3149603
theorem B2231063 : Blo 618297 2231063 := bstep (se 1 (by rfl) ⟨1673297, by rfl⟩ : syracuseStep 2231063 = 3346595) B3346595
theorem B2657069 : Blo 618297 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B2362385 : Blo 618297 2362385 := bstep (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) B1771789
theorem B2657411 : Blo 618297 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B2821337 : Blo 618297 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B3542849 : Blo 618297 3542849 := bstep (se 2 (by rfl) ⟨1328568, by rfl⟩ : syracuseStep 3542849 = 2657137) B2657137
theorem B2985821 : Blo 618297 2985821 := bstep (se 3 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 2985821 = 1119683) B1119683
theorem B1675201 : Blo 618297 1675201 := bstep (se 2 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 1675201 = 1256401) B1256401
theorem B18157709 : Blo 618297 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B5017949 : Blo 618297 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B3969611 : Blo 618297 3969611 := bstep (se 1 (by rfl) ⟨2977208, by rfl⟩ : syracuseStep 3969611 = 5954417) B5954417
theorem B627787 : Blo 618297 627787 := bstep (se 1 (by rfl) ⟨470840, by rfl⟩ : syracuseStep 627787 = 941681) B941681
theorem B1119539 : Blo 618297 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B4789853 : Blo 618297 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B1676951 : Blo 618297 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B3184535 : Blo 618297 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B628727 : Blo 618297 628727 := bstep (se 1 (by rfl) ⟨471545, by rfl⟩ : syracuseStep 628727 = 943091) B943091
theorem B7346477 : Blo 618297 7346477 := bstep (se 3 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 7346477 = 2754929) B2754929
theorem B1120663 : Blo 618297 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B629335 : Blo 618297 629335 := bstep (se 1 (by rfl) ⟨472001, by rfl⟩ : syracuseStep 629335 = 944003) B944003
theorem B2235097 : Blo 618297 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B629579 : Blo 618297 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B2235329 : Blo 618297 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B1416151 : Blo 618297 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B1121291 : Blo 618297 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B695659 : Blo 618297 695659 := bstep (se 1 (by rfl) ⟨521744, by rfl⟩ : syracuseStep 695659 = 1043489) B1043489
theorem B695767 : Blo 618297 695767 := bstep (se 1 (by rfl) ⟨521825, by rfl⟩ : syracuseStep 695767 = 1043651) B1043651
theorem B695947 : Blo 618297 695947 := bstep (se 1 (by rfl) ⟨521960, by rfl⟩ : syracuseStep 695947 = 1043921) B1043921
theorem B696055 : Blo 618297 696055 := bstep (se 1 (by rfl) ⟨522041, by rfl⟩ : syracuseStep 696055 = 1044083) B1044083
theorem B663319 : Blo 618297 663319 := bstep (se 1 (by rfl) ⟨497489, by rfl⟩ : syracuseStep 663319 = 994979) B994979
theorem B3972995 : Blo 618297 3972995 := bstep (se 1 (by rfl) ⟨2979746, by rfl⟩ : syracuseStep 3972995 = 5959493) B5959493
theorem B696235 : Blo 618297 696235 := bstep (se 1 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 696235 = 1044353) B1044353
theorem B696343 : Blo 618297 696343 := bstep (se 1 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 696343 = 1044515) B1044515
theorem B2990125 : Blo 618297 2990125 := bstep (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) B1121297
theorem B696523 : Blo 618297 696523 := bstep (se 1 (by rfl) ⟨522392, by rfl⟩ : syracuseStep 696523 = 1044785) B1044785
theorem B696631 : Blo 618297 696631 := bstep (se 1 (by rfl) ⟨522473, by rfl⟩ : syracuseStep 696631 = 1044947) B1044947
theorem B991577 : Blo 618297 991577 := bstep (se 2 (by rfl) ⟨371841, by rfl⟩ : syracuseStep 991577 = 743683) B743683
theorem B3350963 : Blo 618297 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B893387 : Blo 618297 893387 := bstep (se 1 (by rfl) ⟨670040, by rfl⟩ : syracuseStep 893387 = 1340081) B1340081
theorem B696811 : Blo 618297 696811 := bstep (se 1 (by rfl) ⟨522608, by rfl⟩ : syracuseStep 696811 = 1045217) B1045217
theorem B13378061 : Blo 618297 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B696919 : Blo 618297 696919 := bstep (se 1 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 696919 = 1045379) B1045379
theorem B1254017 : Blo 618297 1254017 := bstep (se 2 (by rfl) ⟨470256, by rfl⟩ : syracuseStep 1254017 = 940513) B940513
theorem B697099 : Blo 618297 697099 := bstep (se 1 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 697099 = 1045649) B1045649
theorem B697207 : Blo 618297 697207 := bstep (se 1 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 697207 = 1045811) B1045811
theorem B1451009 : Blo 618297 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B697387 : Blo 618297 697387 := bstep (se 1 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 697387 = 1046081) B1046081
theorem B697495 : Blo 618297 697495 := bstep (se 1 (by rfl) ⟨523121, by rfl⟩ : syracuseStep 697495 = 1046243) B1046243
theorem B4695245 : Blo 618297 4695245 := bstep (se 3 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 4695245 = 1760717) B1760717
theorem B697675 : Blo 618297 697675 := bstep (se 1 (by rfl) ⟨523256, by rfl⟩ : syracuseStep 697675 = 1046513) B1046513
theorem B697783 : Blo 618297 697783 := bstep (se 1 (by rfl) ⟨523337, by rfl⟩ : syracuseStep 697783 = 1046675) B1046675
theorem B2237969 : Blo 618297 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B1418777 : Blo 618297 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B10593827 : Blo 618297 10593827 := bstep (se 1 (by rfl) ⟨7945370, by rfl⟩ : syracuseStep 10593827 = 15890741) B15890741
theorem B697963 : Blo 618297 697963 := bstep (se 1 (by rfl) ⟨523472, by rfl⟩ : syracuseStep 697963 = 1046945) B1046945
theorem B1320599 : Blo 618297 1320599 := bstep (se 1 (by rfl) ⟨990449, by rfl⟩ : syracuseStep 1320599 = 1980899) B1980899
theorem B4695731 : Blo 618297 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B1320641 : Blo 618297 1320641 := bstep (se 2 (by rfl) ⟨495240, by rfl⟩ : syracuseStep 1320641 = 990481) B990481
theorem B698071 : Blo 618297 698071 := bstep (se 1 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 698071 = 1047107) B1047107
theorem B927449 : Blo 618297 927449 := bstep (se 2 (by rfl) ⟨347793, by rfl⟩ : syracuseStep 927449 = 695587) B695587
theorem B2827997 : Blo 618297 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B927563 : Blo 618297 927563 := bstep (se 1 (by rfl) ⟨695672, by rfl⟩ : syracuseStep 927563 = 1391345) B1391345
theorem B927575 : Blo 618297 927575 := bstep (se 1 (by rfl) ⟨695681, by rfl⟩ : syracuseStep 927575 = 1391363) B1391363
theorem B698251 : Blo 618297 698251 := bstep (se 1 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 698251 = 1047377) B1047377
theorem B927641 : Blo 618297 927641 := bstep (se 2 (by rfl) ⟨347865, by rfl⟩ : syracuseStep 927641 = 695731) B695731
theorem B2271149 : Blo 618297 2271149 := bstep (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) B851681
theorem B698359 : Blo 618297 698359 := bstep (se 1 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 698359 = 1047539) B1047539
theorem B927755 : Blo 618297 927755 := bstep (se 1 (by rfl) ⟨695816, by rfl⟩ : syracuseStep 927755 = 1391633) B1391633
theorem B927767 : Blo 618297 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B927833 : Blo 618297 927833 := bstep (se 2 (by rfl) ⟨347937, by rfl⟩ : syracuseStep 927833 = 695875) B695875
theorem B698539 : Blo 618297 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B927947 : Blo 618297 927947 := bstep (se 1 (by rfl) ⟨695960, by rfl⟩ : syracuseStep 927947 = 1391921) B1391921
theorem B927959 : Blo 618297 927959 := bstep (se 1 (by rfl) ⟨695969, by rfl⟩ : syracuseStep 927959 = 1391939) B1391939
theorem B698647 : Blo 618297 698647 := bstep (se 1 (by rfl) ⟨523985, by rfl⟩ : syracuseStep 698647 = 1047971) B1047971
theorem B928025 : Blo 618297 928025 := bstep (se 2 (by rfl) ⟨348009, by rfl⟩ : syracuseStep 928025 = 696019) B696019
theorem B928139 : Blo 618297 928139 := bstep (se 1 (by rfl) ⟨696104, by rfl⟩ : syracuseStep 928139 = 1392209) B1392209
theorem B928151 : Blo 618297 928151 := bstep (se 1 (by rfl) ⟨696113, by rfl⟩ : syracuseStep 928151 = 1392227) B1392227
theorem B698827 : Blo 618297 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B928217 : Blo 618297 928217 := bstep (se 2 (by rfl) ⟨348081, by rfl⟩ : syracuseStep 928217 = 696163) B696163
theorem B698935 : Blo 618297 698935 := bstep (se 1 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 698935 = 1048403) B1048403
theorem B928331 : Blo 618297 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B928343 : Blo 618297 928343 := bstep (se 1 (by rfl) ⟨696257, by rfl⟩ : syracuseStep 928343 = 1392515) B1392515
theorem B928409 : Blo 618297 928409 := bstep (se 2 (by rfl) ⟨348153, by rfl⟩ : syracuseStep 928409 = 696307) B696307
theorem B699115 : Blo 618297 699115 := bstep (se 1 (by rfl) ⟨524336, by rfl⟩ : syracuseStep 699115 = 1048673) B1048673
theorem B928523 : Blo 618297 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B2239249 : Blo 618297 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B928535 : Blo 618297 928535 := bstep (se 1 (by rfl) ⟨696401, by rfl⟩ : syracuseStep 928535 = 1392803) B1392803
theorem B699223 : Blo 618297 699223 := bstep (se 1 (by rfl) ⟨524417, by rfl⟩ : syracuseStep 699223 = 1048835) B1048835
theorem B928601 : Blo 618297 928601 := bstep (se 2 (by rfl) ⟨348225, by rfl⟩ : syracuseStep 928601 = 696451) B696451
theorem B928715 : Blo 618297 928715 := bstep (se 1 (by rfl) ⟨696536, by rfl⟩ : syracuseStep 928715 = 1393073) B1393073
theorem B1616843 : Blo 618297 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B928727 : Blo 618297 928727 := bstep (se 1 (by rfl) ⟨696545, by rfl⟩ : syracuseStep 928727 = 1393091) B1393091
theorem B2272259 : Blo 618297 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B699403 : Blo 618297 699403 := bstep (se 1 (by rfl) ⟨524552, by rfl⟩ : syracuseStep 699403 = 1049105) B1049105
theorem B928793 : Blo 618297 928793 := bstep (se 2 (by rfl) ⟨348297, by rfl⟩ : syracuseStep 928793 = 696595) B696595
theorem B1485913 : Blo 618297 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B4697189 : Blo 618297 4697189 := bstep (se 4 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 4697189 = 880723) B880723
theorem B1256563 : Blo 618297 1256563 := bstep (se 1 (by rfl) ⟨942422, by rfl⟩ : syracuseStep 1256563 = 1884845) B1884845
theorem B699511 : Blo 618297 699511 := bstep (se 1 (by rfl) ⟨524633, by rfl⟩ : syracuseStep 699511 = 1049267) B1049267
theorem B928907 : Blo 618297 928907 := bstep (se 1 (by rfl) ⟨696680, by rfl⟩ : syracuseStep 928907 = 1393361) B1393361
theorem B928919 : Blo 618297 928919 := bstep (se 1 (by rfl) ⟨696689, by rfl⟩ : syracuseStep 928919 = 1393379) B1393379
theorem B928985 : Blo 618297 928985 := bstep (se 2 (by rfl) ⟨348369, by rfl⟩ : syracuseStep 928985 = 696739) B696739
theorem B699691 : Blo 618297 699691 := bstep (se 1 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 699691 = 1049537) B1049537
theorem B929099 : Blo 618297 929099 := bstep (se 1 (by rfl) ⟨696824, by rfl⟩ : syracuseStep 929099 = 1393649) B1393649
theorem B929111 : Blo 618297 929111 := bstep (se 1 (by rfl) ⟨696833, by rfl⟩ : syracuseStep 929111 = 1393667) B1393667
theorem B699799 : Blo 618297 699799 := bstep (se 1 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 699799 = 1049699) B1049699
theorem B929177 : Blo 618297 929177 := bstep (se 2 (by rfl) ⟨348441, by rfl⟩ : syracuseStep 929177 = 696883) B696883
theorem B929291 : Blo 618297 929291 := bstep (se 1 (by rfl) ⟨696968, by rfl⟩ : syracuseStep 929291 = 1393937) B1393937
theorem B929303 : Blo 618297 929303 := bstep (se 1 (by rfl) ⟨696977, by rfl⟩ : syracuseStep 929303 = 1393955) B1393955
theorem B4697675 : Blo 618297 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B699979 : Blo 618297 699979 := bstep (se 1 (by rfl) ⟨524984, by rfl⟩ : syracuseStep 699979 = 1049969) B1049969
theorem B929369 : Blo 618297 929369 := bstep (se 2 (by rfl) ⟨348513, by rfl⟩ : syracuseStep 929369 = 697027) B697027
theorem B1257049 : Blo 618297 1257049 := bstep (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) B942787
theorem B1486529 : Blo 618297 1486529 := bstep (se 2 (by rfl) ⟨557448, by rfl⟩ : syracuseStep 1486529 = 1114897) B1114897
theorem B929483 : Blo 618297 929483 := bstep (se 1 (by rfl) ⟨697112, by rfl⟩ : syracuseStep 929483 = 1394225) B1394225
theorem B929495 : Blo 618297 929495 := bstep (se 1 (by rfl) ⟨697121, by rfl⟩ : syracuseStep 929495 = 1394243) B1394243
theorem B929561 : Blo 618297 929561 := bstep (se 2 (by rfl) ⟨348585, by rfl⟩ : syracuseStep 929561 = 697171) B697171
theorem B929675 : Blo 618297 929675 := bstep (se 1 (by rfl) ⟨697256, by rfl⟩ : syracuseStep 929675 = 1394513) B1394513
theorem B929687 : Blo 618297 929687 := bstep (se 1 (by rfl) ⟨697265, by rfl⟩ : syracuseStep 929687 = 1394531) B1394531
theorem B929753 : Blo 618297 929753 := bstep (se 2 (by rfl) ⟨348657, by rfl⟩ : syracuseStep 929753 = 697315) B697315
theorem B929867 : Blo 618297 929867 := bstep (se 1 (by rfl) ⟨697400, by rfl⟩ : syracuseStep 929867 = 1394801) B1394801
theorem B929879 : Blo 618297 929879 := bstep (se 1 (by rfl) ⟨697409, by rfl⟩ : syracuseStep 929879 = 1394819) B1394819
theorem B929945 : Blo 618297 929945 := bstep (se 2 (by rfl) ⟨348729, by rfl⟩ : syracuseStep 929945 = 697459) B697459
theorem B930059 : Blo 618297 930059 := bstep (se 1 (by rfl) ⟨697544, by rfl⟩ : syracuseStep 930059 = 1395089) B1395089
theorem B930071 : Blo 618297 930071 := bstep (se 1 (by rfl) ⟨697553, by rfl⟩ : syracuseStep 930071 = 1395107) B1395107
theorem B930137 : Blo 618297 930137 := bstep (se 2 (by rfl) ⟨348801, by rfl⟩ : syracuseStep 930137 = 697603) B697603
theorem B995735 : Blo 618297 995735 := bstep (se 1 (by rfl) ⟨746801, by rfl⟩ : syracuseStep 995735 = 1493603) B1493603
theorem B1880513 : Blo 618297 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B930251 : Blo 618297 930251 := bstep (se 1 (by rfl) ⟨697688, by rfl⟩ : syracuseStep 930251 = 1395377) B1395377
theorem B930263 : Blo 618297 930263 := bstep (se 1 (by rfl) ⟨697697, by rfl⟩ : syracuseStep 930263 = 1395395) B1395395
theorem B1323545 : Blo 618297 1323545 := bstep (se 2 (by rfl) ⟨496329, by rfl⟩ : syracuseStep 1323545 = 992659) B992659
theorem B930329 : Blo 618297 930329 := bstep (se 2 (by rfl) ⟨348873, by rfl⟩ : syracuseStep 930329 = 697747) B697747
theorem B930443 : Blo 618297 930443 := bstep (se 1 (by rfl) ⟨697832, by rfl⟩ : syracuseStep 930443 = 1395665) B1395665
theorem B930455 : Blo 618297 930455 := bstep (se 1 (by rfl) ⟨697841, by rfl⟩ : syracuseStep 930455 = 1395683) B1395683
theorem B2241197 : Blo 618297 2241197 := bstep (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) B840449
theorem B930521 : Blo 618297 930521 := bstep (se 2 (by rfl) ⟨348945, by rfl⟩ : syracuseStep 930521 = 697891) B697891
theorem B930635 : Blo 618297 930635 := bstep (se 1 (by rfl) ⟨697976, by rfl⟩ : syracuseStep 930635 = 1395953) B1395953
theorem B930647 : Blo 618297 930647 := bstep (se 1 (by rfl) ⟨697985, by rfl⟩ : syracuseStep 930647 = 1395971) B1395971
theorem B996247 : Blo 618297 996247 := bstep (se 1 (by rfl) ⟨747185, by rfl⟩ : syracuseStep 996247 = 1494371) B1494371
theorem B930713 : Blo 618297 930713 := bstep (se 2 (by rfl) ⟨349017, by rfl⟩ : syracuseStep 930713 = 698035) B698035
theorem B1323955 : Blo 618297 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B930827 : Blo 618297 930827 := bstep (se 1 (by rfl) ⟨698120, by rfl⟩ : syracuseStep 930827 = 1396241) B1396241
theorem B930839 : Blo 618297 930839 := bstep (se 1 (by rfl) ⟨698129, by rfl⟩ : syracuseStep 930839 = 1396259) B1396259
theorem B3224651 : Blo 618297 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B1717337 : Blo 618297 1717337 := bstep (se 2 (by rfl) ⟨644001, by rfl⟩ : syracuseStep 1717337 = 1288003) B1288003
theorem B930905 : Blo 618297 930905 := bstep (se 2 (by rfl) ⟨349089, by rfl⟩ : syracuseStep 930905 = 698179) B698179
theorem B931019 : Blo 618297 931019 := bstep (se 1 (by rfl) ⟨698264, by rfl⟩ : syracuseStep 931019 = 1396529) B1396529
theorem B931031 : Blo 618297 931031 := bstep (se 1 (by rfl) ⟨698273, by rfl⟩ : syracuseStep 931031 = 1396547) B1396547
theorem B1324289 : Blo 618297 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B996619 : Blo 618297 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B931097 : Blo 618297 931097 := bstep (se 2 (by rfl) ⟨349161, by rfl⟩ : syracuseStep 931097 = 698323) B698323
theorem B931211 : Blo 618297 931211 := bstep (se 1 (by rfl) ⟨698408, by rfl⟩ : syracuseStep 931211 = 1396817) B1396817
theorem B931223 : Blo 618297 931223 := bstep (se 1 (by rfl) ⟨698417, by rfl⟩ : syracuseStep 931223 = 1396835) B1396835
theorem B931289 : Blo 618297 931289 := bstep (se 2 (by rfl) ⟨349233, by rfl⟩ : syracuseStep 931289 = 698467) B698467
theorem B931403 : Blo 618297 931403 := bstep (se 1 (by rfl) ⟨698552, by rfl⟩ : syracuseStep 931403 = 1397105) B1397105
theorem B931415 : Blo 618297 931415 := bstep (se 1 (by rfl) ⟨698561, by rfl⟩ : syracuseStep 931415 = 1397123) B1397123
theorem B3356261 : Blo 618297 3356261 := bstep (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) B629299
theorem B931481 : Blo 618297 931481 := bstep (se 2 (by rfl) ⟨349305, by rfl⟩ : syracuseStep 931481 = 698611) B698611
theorem B931595 : Blo 618297 931595 := bstep (se 1 (by rfl) ⟨698696, by rfl⟩ : syracuseStep 931595 = 1397393) B1397393
theorem B931607 : Blo 618297 931607 := bstep (se 1 (by rfl) ⟨698705, by rfl⟩ : syracuseStep 931607 = 1397411) B1397411
theorem B931673 : Blo 618297 931673 := bstep (se 2 (by rfl) ⟨349377, by rfl⟩ : syracuseStep 931673 = 698755) B698755
theorem B931787 : Blo 618297 931787 := bstep (se 1 (by rfl) ⟨698840, by rfl⟩ : syracuseStep 931787 = 1397681) B1397681
theorem B1325015 : Blo 618297 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B931799 : Blo 618297 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B931865 : Blo 618297 931865 := bstep (se 2 (by rfl) ⟨349449, by rfl⟩ : syracuseStep 931865 = 698899) B698899
theorem B4536395 : Blo 618297 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B931979 : Blo 618297 931979 := bstep (se 1 (by rfl) ⟨698984, by rfl⟩ : syracuseStep 931979 = 1397969) B1397969
theorem B931991 : Blo 618297 931991 := bstep (se 1 (by rfl) ⟨698993, by rfl⟩ : syracuseStep 931991 = 1397987) B1397987
theorem B10074293 : Blo 618297 10074293 := bstep (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) B944465
theorem B932057 : Blo 618297 932057 := bstep (se 2 (by rfl) ⟨349521, by rfl⟩ : syracuseStep 932057 = 699043) B699043
theorem B932171 : Blo 618297 932171 := bstep (se 1 (by rfl) ⟨699128, by rfl⟩ : syracuseStep 932171 = 1398257) B1398257
theorem B932183 : Blo 618297 932183 := bstep (se 1 (by rfl) ⟨699137, by rfl⟩ : syracuseStep 932183 = 1398275) B1398275
theorem B1194355 : Blo 618297 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B932249 : Blo 618297 932249 := bstep (se 2 (by rfl) ⟨349593, by rfl⟩ : syracuseStep 932249 = 699187) B699187
theorem B932363 : Blo 618297 932363 := bstep (se 1 (by rfl) ⟨699272, by rfl⟩ : syracuseStep 932363 = 1398545) B1398545
theorem B932375 : Blo 618297 932375 := bstep (se 1 (by rfl) ⟨699281, by rfl⟩ : syracuseStep 932375 = 1398563) B1398563
theorem B932441 : Blo 618297 932441 := bstep (se 2 (by rfl) ⟨349665, by rfl⟩ : syracuseStep 932441 = 699331) B699331
theorem B1391219 : Blo 618297 1391219 := bstep (se 1 (by rfl) ⟨1043414, by rfl⟩ : syracuseStep 1391219 = 2086829) B2086829
theorem B1391255 : Blo 618297 1391255 := bstep (se 1 (by rfl) ⟨1043441, by rfl⟩ : syracuseStep 1391255 = 2086883) B2086883
theorem B932555 : Blo 618297 932555 := bstep (se 1 (by rfl) ⟨699416, by rfl⟩ : syracuseStep 932555 = 1398833) B1398833
theorem B932567 : Blo 618297 932567 := bstep (se 1 (by rfl) ⟨699425, by rfl⟩ : syracuseStep 932567 = 1398851) B1398851
theorem B932633 : Blo 618297 932633 := bstep (se 2 (by rfl) ⟨349737, by rfl⟩ : syracuseStep 932633 = 699475) B699475
theorem B1391435 : Blo 618297 1391435 := bstep (se 1 (by rfl) ⟨1043576, by rfl⟩ : syracuseStep 1391435 = 2087153) B2087153
theorem B1391489 : Blo 618297 1391489 := bstep (se 2 (by rfl) ⟨521808, by rfl⟩ : syracuseStep 1391489 = 1043617) B1043617
theorem B932747 : Blo 618297 932747 := bstep (se 1 (by rfl) ⟨699560, by rfl⟩ : syracuseStep 932747 = 1399121) B1399121
theorem B932759 : Blo 618297 932759 := bstep (se 1 (by rfl) ⟨699569, by rfl⟩ : syracuseStep 932759 = 1399139) B1399139
theorem B17906609 : Blo 618297 17906609 := bstep (se 2 (by rfl) ⟨6714978, by rfl⟩ : syracuseStep 17906609 = 13429957) B13429957
theorem B3980249 : Blo 618297 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B932825 : Blo 618297 932825 := bstep (se 2 (by rfl) ⟨349809, by rfl⟩ : syracuseStep 932825 = 699619) B699619
theorem B932939 : Blo 618297 932939 := bstep (se 1 (by rfl) ⟨699704, by rfl⟩ : syracuseStep 932939 = 1399409) B1399409
theorem B932951 : Blo 618297 932951 := bstep (se 1 (by rfl) ⟨699713, by rfl⟩ : syracuseStep 932951 = 1399427) B1399427
theorem B1391705 : Blo 618297 1391705 := bstep (se 2 (by rfl) ⟨521889, by rfl⟩ : syracuseStep 1391705 = 1043779) B1043779
theorem B933017 : Blo 618297 933017 := bstep (se 2 (by rfl) ⟨349881, by rfl⟩ : syracuseStep 933017 = 699763) B699763
theorem B1391795 : Blo 618297 1391795 := bstep (se 1 (by rfl) ⟨1043846, by rfl⟩ : syracuseStep 1391795 = 2087693) B2087693
theorem B1391831 : Blo 618297 1391831 := bstep (se 1 (by rfl) ⟨1043873, by rfl⟩ : syracuseStep 1391831 = 2087747) B2087747
theorem B933131 : Blo 618297 933131 := bstep (se 1 (by rfl) ⟨699848, by rfl⟩ : syracuseStep 933131 = 1399697) B1399697
theorem B933143 : Blo 618297 933143 := bstep (se 1 (by rfl) ⟨699857, by rfl⟩ : syracuseStep 933143 = 1399715) B1399715
theorem B1359155 : Blo 618297 1359155 := bstep (se 1 (by rfl) ⟨1019366, by rfl⟩ : syracuseStep 1359155 = 2038733) B2038733
theorem B933209 : Blo 618297 933209 := bstep (se 2 (by rfl) ⟨349953, by rfl⟩ : syracuseStep 933209 = 699907) B699907
theorem B17939825 : Blo 618297 17939825 := bstep (se 2 (by rfl) ⟨6727434, by rfl⟩ : syracuseStep 17939825 = 13454869) B13454869
theorem B1392011 : Blo 618297 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B1392065 : Blo 618297 1392065 := bstep (se 2 (by rfl) ⟨522024, by rfl⟩ : syracuseStep 1392065 = 1044049) B1044049
theorem B933323 : Blo 618297 933323 := bstep (se 1 (by rfl) ⟨699992, by rfl⟩ : syracuseStep 933323 = 1399985) B1399985
theorem B933335 : Blo 618297 933335 := bstep (se 1 (by rfl) ⟨700001, by rfl⟩ : syracuseStep 933335 = 1400003) B1400003
theorem B933401 : Blo 618297 933401 := bstep (se 2 (by rfl) ⟨350025, by rfl⟩ : syracuseStep 933401 = 700051) B700051
theorem B1392281 : Blo 618297 1392281 := bstep (se 2 (by rfl) ⟨522105, by rfl⟩ : syracuseStep 1392281 = 1044211) B1044211
theorem B1392371 : Blo 618297 1392371 := bstep (se 1 (by rfl) ⟨1044278, by rfl⟩ : syracuseStep 1392371 = 2088557) B2088557
theorem B1392407 : Blo 618297 1392407 := bstep (se 1 (by rfl) ⟨1044305, by rfl⟩ : syracuseStep 1392407 = 2088611) B2088611
theorem B3358529 : Blo 618297 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B1392587 : Blo 618297 1392587 := bstep (se 1 (by rfl) ⟨1044440, by rfl⟩ : syracuseStep 1392587 = 2088881) B2088881
theorem B5291993 : Blo 618297 5291993 := bstep (se 2 (by rfl) ⟨1984497, by rfl⟩ : syracuseStep 5291993 = 3968995) B3968995
theorem B1392641 : Blo 618297 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B1884235 : Blo 618297 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B1130635 : Blo 618297 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B2834635 : Blo 618297 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B1392857 : Blo 618297 1392857 := bstep (se 2 (by rfl) ⟨522321, by rfl⟩ : syracuseStep 1392857 = 1044643) B1044643
theorem B1392947 : Blo 618297 1392947 := bstep (se 1 (by rfl) ⟨1044710, by rfl⟩ : syracuseStep 1392947 = 2089421) B2089421
theorem B1392983 : Blo 618297 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B5030237 : Blo 618297 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B1327475 : Blo 618297 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B1393163 : Blo 618297 1393163 := bstep (se 1 (by rfl) ⟨1044872, by rfl⟩ : syracuseStep 1393163 = 2089745) B2089745
theorem B1393217 : Blo 618297 1393217 := bstep (se 2 (by rfl) ⟨522456, by rfl⟩ : syracuseStep 1393217 = 1044913) B1044913
theorem B4244069 : Blo 618297 4244069 := bstep (se 4 (by rfl) ⟨397881, by rfl⟩ : syracuseStep 4244069 = 795763) B795763
theorem B1393433 : Blo 618297 1393433 := bstep (se 2 (by rfl) ⟨522537, by rfl⟩ : syracuseStep 1393433 = 1045075) B1045075
theorem B4703021 : Blo 618297 4703021 := bstep (se 3 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 4703021 = 1763633) B1763633
theorem B1393523 : Blo 618297 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B1393559 : Blo 618297 1393559 := bstep (se 1 (by rfl) ⟨1045169, by rfl⟩ : syracuseStep 1393559 = 2090339) B2090339
theorem B32228387 : Blo 618297 32228387 := bstep (se 1 (by rfl) ⟨24171290, by rfl⟩ : syracuseStep 32228387 = 48342581) B48342581
theorem B1393739 : Blo 618297 1393739 := bstep (se 1 (by rfl) ⟨1045304, by rfl⟩ : syracuseStep 1393739 = 2090609) B2090609
theorem B1393793 : Blo 618297 1393793 := bstep (se 2 (by rfl) ⟨522672, by rfl⟩ : syracuseStep 1393793 = 1045345) B1045345
theorem B836887 : Blo 618297 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B1394009 : Blo 618297 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B1394099 : Blo 618297 1394099 := bstep (se 1 (by rfl) ⟨1045574, by rfl⟩ : syracuseStep 1394099 = 2091149) B2091149
theorem B1394135 : Blo 618297 1394135 := bstep (se 1 (by rfl) ⟨1045601, by rfl⟩ : syracuseStep 1394135 = 2091203) B2091203
theorem B1328663 : Blo 618297 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B5293633 : Blo 618297 5293633 := bstep (se 2 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 5293633 = 3970225) B3970225
theorem B1787467 : Blo 618297 1787467 := bstep (se 1 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 1787467 = 2681201) B2681201
theorem B3130973 : Blo 618297 3130973 := bstep (se 3 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 3130973 = 1174115) B1174115
theorem B4769381 : Blo 618297 4769381 := bstep (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) B894259
theorem B1394315 : Blo 618297 1394315 := bstep (se 1 (by rfl) ⟨1045736, by rfl⟩ : syracuseStep 1394315 = 2091473) B2091473
theorem B1394369 : Blo 618297 1394369 := bstep (se 2 (by rfl) ⟨522888, by rfl⟩ : syracuseStep 1394369 = 1045777) B1045777
theorem B837335 : Blo 618297 837335 := bstep (se 1 (by rfl) ⟨628001, by rfl⟩ : syracuseStep 837335 = 1256003) B1256003
theorem B1492825 : Blo 618297 1492825 := bstep (se 2 (by rfl) ⟨559809, by rfl⟩ : syracuseStep 1492825 = 1119619) B1119619
theorem B1394585 : Blo 618297 1394585 := bstep (se 2 (by rfl) ⟨522969, by rfl⟩ : syracuseStep 1394585 = 1045939) B1045939
theorem B1394675 : Blo 618297 1394675 := bstep (se 1 (by rfl) ⟨1046006, by rfl⟩ : syracuseStep 1394675 = 2092013) B2092013
theorem B837643 : Blo 618297 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B1394711 : Blo 618297 1394711 := bstep (se 1 (by rfl) ⟨1046033, by rfl⟩ : syracuseStep 1394711 = 2092067) B2092067
theorem B1984601 : Blo 618297 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B2508893 : Blo 618297 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B1394891 : Blo 618297 1394891 := bstep (se 1 (by rfl) ⟨1046168, by rfl⟩ : syracuseStep 1394891 = 2092337) B2092337
theorem B1394945 : Blo 618297 1394945 := bstep (se 2 (by rfl) ⟨523104, by rfl⟩ : syracuseStep 1394945 = 1046209) B1046209
theorem B1493441 : Blo 618297 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B1395161 : Blo 618297 1395161 := bstep (se 2 (by rfl) ⟨523185, by rfl⟩ : syracuseStep 1395161 = 1046371) B1046371
theorem B3361297 : Blo 618297 3361297 := bstep (se 2 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 3361297 = 2520973) B2520973
theorem B1395251 : Blo 618297 1395251 := bstep (se 1 (by rfl) ⟨1046438, by rfl⟩ : syracuseStep 1395251 = 2092877) B2092877
theorem B1395287 : Blo 618297 1395287 := bstep (se 1 (by rfl) ⟨1046465, by rfl⟩ : syracuseStep 1395287 = 2092931) B2092931
theorem B2116289 : Blo 618297 2116289 := bstep (se 2 (by rfl) ⟨793608, by rfl⟩ : syracuseStep 2116289 = 1587217) B1587217
theorem B1395467 : Blo 618297 1395467 := bstep (se 1 (by rfl) ⟨1046600, by rfl⟩ : syracuseStep 1395467 = 2093201) B2093201
theorem B1395521 : Blo 618297 1395521 := bstep (se 2 (by rfl) ⟨523320, by rfl⟩ : syracuseStep 1395521 = 1046641) B1046641
theorem B1395737 : Blo 618297 1395737 := bstep (se 2 (by rfl) ⟨523401, by rfl⟩ : syracuseStep 1395737 = 1046803) B1046803
theorem B1395827 : Blo 618297 1395827 := bstep (se 1 (by rfl) ⟨1046870, by rfl⟩ : syracuseStep 1395827 = 2093741) B2093741
theorem B1395863 : Blo 618297 1395863 := bstep (se 1 (by rfl) ⟨1046897, by rfl⟩ : syracuseStep 1395863 = 2093795) B2093795
theorem B1592513 : Blo 618297 1592513 := bstep (se 2 (by rfl) ⟨597192, by rfl⟩ : syracuseStep 1592513 = 1194385) B1194385
theorem B8473805 : Blo 618297 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B1396043 : Blo 618297 1396043 := bstep (se 1 (by rfl) ⟨1047032, by rfl⟩ : syracuseStep 1396043 = 2094065) B2094065
theorem B1396097 : Blo 618297 1396097 := bstep (se 2 (by rfl) ⟨523536, by rfl⟩ : syracuseStep 1396097 = 1047073) B1047073
theorem B4246915 : Blo 618297 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B5721617 : Blo 618297 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B1396313 : Blo 618297 1396313 := bstep (se 2 (by rfl) ⟨523617, by rfl⟩ : syracuseStep 1396313 = 1047235) B1047235
theorem B3133079 : Blo 618297 3133079 := bstep (se 1 (by rfl) ⟨2349809, by rfl⟩ : syracuseStep 3133079 = 4699619) B4699619
theorem B1396403 : Blo 618297 1396403 := bstep (se 1 (by rfl) ⟨1047302, by rfl⟩ : syracuseStep 1396403 = 2094605) B2094605
theorem B1986241 : Blo 618297 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B1396439 : Blo 618297 1396439 := bstep (se 1 (by rfl) ⟨1047329, by rfl⟩ : syracuseStep 1396439 = 2094659) B2094659
theorem B1396619 : Blo 618297 1396619 := bstep (se 1 (by rfl) ⟨1047464, by rfl⟩ : syracuseStep 1396619 = 2094929) B2094929
theorem B1396673 : Blo 618297 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B10047557 : Blo 618297 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B1396889 : Blo 618297 1396889 := bstep (se 2 (by rfl) ⟨523833, by rfl⟩ : syracuseStep 1396889 = 1047667) B1047667
theorem B10571957 : Blo 618297 10571957 := bstep (se 5 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 10571957 = 991121) B991121
theorem B1396979 : Blo 618297 1396979 := bstep (se 1 (by rfl) ⟨1047734, by rfl⟩ : syracuseStep 1396979 = 2095469) B2095469
theorem B1397015 : Blo 618297 1397015 := bstep (se 1 (by rfl) ⟨1047761, by rfl⟩ : syracuseStep 1397015 = 2095523) B2095523
theorem B3527063 : Blo 618297 3527063 := bstep (se 1 (by rfl) ⟨2645297, by rfl⟩ : syracuseStep 3527063 = 5290595) B5290595
theorem B1397195 : Blo 618297 1397195 := bstep (se 1 (by rfl) ⟨1047896, by rfl⟩ : syracuseStep 1397195 = 2095793) B2095793
theorem B1397249 : Blo 618297 1397249 := bstep (se 2 (by rfl) ⟨523968, by rfl⟩ : syracuseStep 1397249 = 1047937) B1047937
theorem B1593931 : Blo 618297 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B4706909 : Blo 618297 4706909 := bstep (se 3 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 4706909 = 1765091) B1765091
theorem B15323741 : Blo 618297 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B1397465 : Blo 618297 1397465 := bstep (se 2 (by rfl) ⟨524049, by rfl⟩ : syracuseStep 1397465 = 1048099) B1048099
theorem B1397555 : Blo 618297 1397555 := bstep (se 1 (by rfl) ⟨1048166, by rfl⟩ : syracuseStep 1397555 = 2096333) B2096333
theorem B1397591 : Blo 618297 1397591 := bstep (se 1 (by rfl) ⟨1048193, by rfl⟩ : syracuseStep 1397591 = 2096387) B2096387
theorem B2544587 : Blo 618297 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B1135603 : Blo 618297 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1397771 : Blo 618297 1397771 := bstep (se 1 (by rfl) ⟨1048328, by rfl⟩ : syracuseStep 1397771 = 2096657) B2096657
theorem B1397825 : Blo 618297 1397825 := bstep (se 2 (by rfl) ⟨524184, by rfl⟩ : syracuseStep 1397825 = 1048369) B1048369
theorem B2348291 : Blo 618297 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B1398041 : Blo 618297 1398041 := bstep (se 2 (by rfl) ⟨524265, by rfl⟩ : syracuseStep 1398041 = 1048531) B1048531
theorem B7066925 : Blo 618297 7066925 := bstep (se 3 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 7066925 = 2650097) B2650097
theorem B1398131 : Blo 618297 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B1398167 : Blo 618297 1398167 := bstep (se 1 (by rfl) ⟨1048625, by rfl⟩ : syracuseStep 1398167 = 2097251) B2097251
theorem B4838977 : Blo 618297 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B1398347 : Blo 618297 1398347 := bstep (se 1 (by rfl) ⟨1048760, by rfl⟩ : syracuseStep 1398347 = 2097521) B2097521
theorem B1988189 : Blo 618297 1988189 := bstep (se 3 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 1988189 = 745571) B745571
theorem B1398401 : Blo 618297 1398401 := bstep (se 2 (by rfl) ⟨524400, by rfl⟩ : syracuseStep 1398401 = 1048801) B1048801
theorem B2348747 : Blo 618297 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B2643673 : Blo 618297 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B1988317 : Blo 618297 1988317 := bstep (se 3 (by rfl) ⟨372809, by rfl⟩ : syracuseStep 1988317 = 745619) B745619
theorem B1398617 : Blo 618297 1398617 := bstep (se 2 (by rfl) ⟨524481, by rfl⟩ : syracuseStep 1398617 = 1048963) B1048963
theorem B2348945 : Blo 618297 2348945 := bstep (se 2 (by rfl) ⟨880854, by rfl⟩ : syracuseStep 2348945 = 1761709) B1761709
theorem B1398707 : Blo 618297 1398707 := bstep (se 1 (by rfl) ⟨1049030, by rfl⟩ : syracuseStep 1398707 = 2098061) B2098061
theorem B1398743 : Blo 618297 1398743 := bstep (se 1 (by rfl) ⟨1049057, by rfl⟩ : syracuseStep 1398743 = 2098115) B2098115
theorem B5036107 : Blo 618297 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B1595467 : Blo 618297 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1398923 : Blo 618297 1398923 := bstep (se 1 (by rfl) ⟨1049192, by rfl⟩ : syracuseStep 1398923 = 2098385) B2098385
theorem B1398977 : Blo 618297 1398977 := bstep (se 2 (by rfl) ⟨524616, by rfl⟩ : syracuseStep 1398977 = 1049233) B1049233
theorem B2644289 : Blo 618297 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B2087261 : Blo 618297 2087261 := bstep (se 3 (by rfl) ⟨391361, by rfl⟩ : syracuseStep 2087261 = 782723) B782723
theorem B10606949 : Blo 618297 10606949 := bstep (se 4 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 10606949 = 1988803) B1988803
theorem B1399193 : Blo 618297 1399193 := bstep (se 2 (by rfl) ⟨524697, by rfl⟩ : syracuseStep 1399193 = 1049395) B1049395
theorem B1399283 : Blo 618297 1399283 := bstep (se 1 (by rfl) ⟨1049462, by rfl⟩ : syracuseStep 1399283 = 2098925) B2098925
theorem B1399319 : Blo 618297 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B2349719 : Blo 618297 2349719 := bstep (se 1 (by rfl) ⟨1762289, by rfl⟩ : syracuseStep 2349719 = 3524579) B3524579
theorem B1399499 : Blo 618297 1399499 := bstep (se 1 (by rfl) ⟨1049624, by rfl⟩ : syracuseStep 1399499 = 2099249) B2099249
theorem B1399553 : Blo 618297 1399553 := bstep (se 2 (by rfl) ⟨524832, by rfl⟩ : syracuseStep 1399553 = 1049665) B1049665
theorem B2349917 : Blo 618297 2349917 := bstep (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) B881219
theorem B1399769 : Blo 618297 1399769 := bstep (se 2 (by rfl) ⟨524913, by rfl⟩ : syracuseStep 1399769 = 1049827) B1049827
theorem B1399859 : Blo 618297 1399859 := bstep (se 1 (by rfl) ⟨1049894, by rfl⟩ : syracuseStep 1399859 = 2099789) B2099789
theorem B1399895 : Blo 618297 1399895 := bstep (se 1 (by rfl) ⟨1049921, by rfl⟩ : syracuseStep 1399895 = 2099843) B2099843
theorem B3136643 : Blo 618297 3136643 := bstep (se 1 (by rfl) ⟨2352482, by rfl⟩ : syracuseStep 3136643 = 4704965) B4704965
theorem B1400075 : Blo 618297 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1400129 : Blo 618297 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B2088395 : Blo 618297 2088395 := bstep (se 1 (by rfl) ⟨1566296, by rfl⟩ : syracuseStep 2088395 = 3132593) B3132593
theorem B2088665 : Blo 618297 2088665 := bstep (se 2 (by rfl) ⟨783249, by rfl⟩ : syracuseStep 2088665 = 1566499) B1566499
theorem B11952197 : Blo 618297 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B1761355 : Blo 618297 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B2875571 : Blo 618297 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B10314029 : Blo 618297 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B2089367 : Blo 618297 2089367 := bstep (se 1 (by rfl) ⟨1567025, by rfl⟩ : syracuseStep 2089367 = 3134051) B3134051
theorem B5038541 : Blo 618297 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B4481497 : Blo 618297 4481497 := bstep (se 2 (by rfl) ⟨1680561, by rfl⟩ : syracuseStep 4481497 = 3361123) B3361123
theorem B5300741 : Blo 618297 5300741 := bstep (se 4 (by rfl) ⟨496944, by rfl⟩ : syracuseStep 5300741 = 993889) B993889
theorem B1761857 : Blo 618297 1761857 := bstep (se 2 (by rfl) ⟨660696, by rfl⟩ : syracuseStep 1761857 = 1321393) B1321393
theorem B10052171 : Blo 618297 10052171 := bstep (se 1 (by rfl) ⟨7539128, by rfl⟩ : syracuseStep 10052171 = 15078257) B15078257
theorem B2646749 : Blo 618297 2646749 := bstep (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) B992531
theorem B2351875 : Blo 618297 2351875 := bstep (se 1 (by rfl) ⟨1763906, by rfl⟩ : syracuseStep 2351875 = 3527813) B3527813
theorem B2974481 : Blo 618297 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B8971073 : Blo 618297 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B1762199 : Blo 618297 1762199 := bstep (se 1 (by rfl) ⟨1321649, by rfl⟩ : syracuseStep 1762199 = 2643299) B2643299
theorem B2089907 : Blo 618297 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B2352179 : Blo 618297 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B8479819 : Blo 618297 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B3531869 : Blo 618297 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B746647 : Blo 618297 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B2090177 : Blo 618297 2090177 := bstep (se 2 (by rfl) ⟨783816, by rfl⟩ : syracuseStep 2090177 = 1567633) B1567633
theorem B1566155 : Blo 618297 1566155 := bstep (se 1 (by rfl) ⟨1174616, by rfl⟩ : syracuseStep 1566155 = 2349233) B2349233
theorem B6448733 : Blo 618297 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B2975363 : Blo 618297 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B2352833 : Blo 618297 2352833 := bstep (se 2 (by rfl) ⟨882312, by rfl⟩ : syracuseStep 2352833 = 1764625) B1764625
theorem B2090717 : Blo 618297 2090717 := bstep (se 3 (by rfl) ⟨392009, by rfl⟩ : syracuseStep 2090717 = 784019) B784019
theorem B2418611 : Blo 618297 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B2516953 : Blo 618297 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B4352321 : Blo 618297 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B1567127 : Blo 618297 1567127 := bstep (se 1 (by rfl) ⟨1175345, by rfl⟩ : syracuseStep 1567127 = 2350691) B2350691
theorem B1174169 : Blo 618297 1174169 := bstep (se 2 (by rfl) ⟨440313, by rfl⟩ : syracuseStep 1174169 = 880627) B880627
theorem B3140369 : Blo 618297 3140369 := bstep (se 2 (by rfl) ⟨1177638, by rfl⟩ : syracuseStep 3140369 = 2355277) B2355277
theorem B2091851 : Blo 618297 2091851 := bstep (se 1 (by rfl) ⟨1568888, by rfl⟩ : syracuseStep 2091851 = 3137777) B3137777
theorem B2354093 : Blo 618297 2354093 := bstep (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) B882785
theorem B3140531 : Blo 618297 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B2354123 : Blo 618297 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B1764317 : Blo 618297 1764317 := bstep (se 3 (by rfl) ⟨330809, by rfl⟩ : syracuseStep 1764317 = 661619) B661619
theorem B1567795 : Blo 618297 1567795 := bstep (se 1 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 1567795 = 2351693) B2351693
theorem B1043543 : Blo 618297 1043543 := bstep (se 1 (by rfl) ⟨782657, by rfl⟩ : syracuseStep 1043543 = 1565315) B1565315
theorem B2092121 : Blo 618297 2092121 := bstep (se 2 (by rfl) ⟨784545, by rfl⟩ : syracuseStep 2092121 = 1569091) B1569091
theorem B1567937 : Blo 618297 1567937 := bstep (se 2 (by rfl) ⟨587976, by rfl⟩ : syracuseStep 1567937 = 1175953) B1175953
theorem B1043671 : Blo 618297 1043671 := bstep (se 1 (by rfl) ⟨782753, by rfl⟩ : syracuseStep 1043671 = 1565507) B1565507
theorem B2649347 : Blo 618297 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B1764659 : Blo 618297 1764659 := bstep (se 1 (by rfl) ⟨1323494, by rfl⟩ : syracuseStep 1764659 = 2646989) B2646989
theorem B24440291 : Blo 618297 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B3534353 : Blo 618297 3534353 := bstep (se 2 (by rfl) ⟨1325382, by rfl⟩ : syracuseStep 3534353 = 2650765) B2650765
theorem B2354777 : Blo 618297 2354777 := bstep (se 2 (by rfl) ⟨883041, by rfl⟩ : syracuseStep 2354777 = 1766083) B1766083
theorem B2092823 : Blo 618297 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B618315 : Blo 618297 618315 := bstep (se 1 (by rfl) ⟨463736, by rfl⟩ : syracuseStep 618315 = 927473) B927473
theorem B1044299 : Blo 618297 1044299 := bstep (se 1 (by rfl) ⟨783224, by rfl⟩ : syracuseStep 1044299 = 1566449) B1566449
theorem B618327 : Blo 618297 618327 := bstep (se 1 (by rfl) ⟨463745, by rfl⟩ : syracuseStep 618327 = 927491) B927491
theorem B618347 : Blo 618297 618347 := bstep (se 1 (by rfl) ⟨463760, by rfl⟩ : syracuseStep 618347 = 927521) B927521
theorem B618359 : Blo 618297 618359 := bstep (se 1 (by rfl) ⟨463769, by rfl⟩ : syracuseStep 618359 = 927539) B927539
theorem B618379 : Blo 618297 618379 := bstep (se 1 (by rfl) ⟨463784, by rfl⟩ : syracuseStep 618379 = 927569) B927569
theorem B618391 : Blo 618297 618391 := bstep (se 1 (by rfl) ⟨463793, by rfl⟩ : syracuseStep 618391 = 927587) B927587
theorem B2355095 : Blo 618297 2355095 := bstep (se 1 (by rfl) ⟨1766321, by rfl⟩ : syracuseStep 2355095 = 3532643) B3532643
theorem B618411 : Blo 618297 618411 := bstep (se 1 (by rfl) ⟨463808, by rfl⟩ : syracuseStep 618411 = 927617) B927617
theorem B618423 : Blo 618297 618423 := bstep (se 1 (by rfl) ⟨463817, by rfl⟩ : syracuseStep 618423 = 927635) B927635
theorem B618443 : Blo 618297 618443 := bstep (se 1 (by rfl) ⟨463832, by rfl⟩ : syracuseStep 618443 = 927665) B927665
theorem B1044427 : Blo 618297 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B618455 : Blo 618297 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B1437655 : Blo 618297 1437655 := bstep (se 1 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 1437655 = 2156483) B2156483
theorem B618475 : Blo 618297 618475 := bstep (se 1 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 618475 = 927713) B927713
theorem B618487 : Blo 618297 618487 := bstep (se 1 (by rfl) ⟨463865, by rfl⟩ : syracuseStep 618487 = 927731) B927731
theorem B618507 : Blo 618297 618507 := bstep (se 1 (by rfl) ⟨463880, by rfl⟩ : syracuseStep 618507 = 927761) B927761
theorem B618519 : Blo 618297 618519 := bstep (se 1 (by rfl) ⟨463889, by rfl⟩ : syracuseStep 618519 = 927779) B927779
theorem B618539 : Blo 618297 618539 := bstep (se 1 (by rfl) ⟨463904, by rfl⟩ : syracuseStep 618539 = 927809) B927809
theorem B5304365 : Blo 618297 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B618551 : Blo 618297 618551 := bstep (se 1 (by rfl) ⟨463913, by rfl⟩ : syracuseStep 618551 = 927827) B927827
theorem B618571 : Blo 618297 618571 := bstep (se 1 (by rfl) ⟨463928, by rfl⟩ : syracuseStep 618571 = 927857) B927857
theorem B1175627 : Blo 618297 1175627 := bstep (se 1 (by rfl) ⟨881720, by rfl⟩ : syracuseStep 1175627 = 1763441) B1763441
theorem B618583 : Blo 618297 618583 := bstep (se 1 (by rfl) ⟨463937, by rfl⟩ : syracuseStep 618583 = 927875) B927875
theorem B1044569 : Blo 618297 1044569 := bstep (se 2 (by rfl) ⟨391713, by rfl⟩ : syracuseStep 1044569 = 783427) B783427
theorem B618603 : Blo 618297 618603 := bstep (se 1 (by rfl) ⟨463952, by rfl⟩ : syracuseStep 618603 = 927905) B927905
theorem B618615 : Blo 618297 618615 := bstep (se 1 (by rfl) ⟨463961, by rfl⟩ : syracuseStep 618615 = 927923) B927923
theorem B618635 : Blo 618297 618635 := bstep (se 1 (by rfl) ⟨463976, by rfl⟩ : syracuseStep 618635 = 927953) B927953
theorem B6025367 : Blo 618297 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B618647 : Blo 618297 618647 := bstep (se 1 (by rfl) ⟨463985, by rfl⟩ : syracuseStep 618647 = 927971) B927971
theorem B618667 : Blo 618297 618667 := bstep (se 1 (by rfl) ⟨464000, by rfl⟩ : syracuseStep 618667 = 928001) B928001
theorem B618679 : Blo 618297 618679 := bstep (se 1 (by rfl) ⟨464009, by rfl⟩ : syracuseStep 618679 = 928019) B928019
theorem B618699 : Blo 618297 618699 := bstep (se 1 (by rfl) ⟨464024, by rfl⟩ : syracuseStep 618699 = 928049) B928049
theorem B782551 : Blo 618297 782551 := bstep (se 1 (by rfl) ⟨586913, by rfl⟩ : syracuseStep 782551 = 1173827) B1173827
theorem B618711 : Blo 618297 618711 := bstep (se 1 (by rfl) ⟨464033, by rfl⟩ : syracuseStep 618711 = 928067) B928067
theorem B1044697 : Blo 618297 1044697 := bstep (se 2 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 1044697 = 783523) B783523
theorem B618731 : Blo 618297 618731 := bstep (se 1 (by rfl) ⟨464048, by rfl⟩ : syracuseStep 618731 = 928097) B928097
theorem B618743 : Blo 618297 618743 := bstep (se 1 (by rfl) ⟨464057, by rfl⟩ : syracuseStep 618743 = 928115) B928115
theorem B1175809 : Blo 618297 1175809 := bstep (se 2 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 1175809 = 881857) B881857
theorem B618763 : Blo 618297 618763 := bstep (se 1 (by rfl) ⟨464072, by rfl⟩ : syracuseStep 618763 = 928145) B928145
theorem B618775 : Blo 618297 618775 := bstep (se 1 (by rfl) ⟨464081, by rfl⟩ : syracuseStep 618775 = 928163) B928163
theorem B618795 : Blo 618297 618795 := bstep (se 1 (by rfl) ⟨464096, by rfl⟩ : syracuseStep 618795 = 928193) B928193
theorem B2093363 : Blo 618297 2093363 := bstep (se 1 (by rfl) ⟨1570022, by rfl⟩ : syracuseStep 2093363 = 3140045) B3140045
theorem B2388275 : Blo 618297 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B618807 : Blo 618297 618807 := bstep (se 1 (by rfl) ⟨464105, by rfl⟩ : syracuseStep 618807 = 928211) B928211
theorem B618827 : Blo 618297 618827 := bstep (se 1 (by rfl) ⟨464120, by rfl⟩ : syracuseStep 618827 = 928241) B928241
theorem B618839 : Blo 618297 618839 := bstep (se 1 (by rfl) ⟨464129, by rfl⟩ : syracuseStep 618839 = 928259) B928259
theorem B618859 : Blo 618297 618859 := bstep (se 1 (by rfl) ⟨464144, by rfl⟩ : syracuseStep 618859 = 928289) B928289
theorem B618871 : Blo 618297 618871 := bstep (se 1 (by rfl) ⟨464153, by rfl⟩ : syracuseStep 618871 = 928307) B928307
theorem B618891 : Blo 618297 618891 := bstep (se 1 (by rfl) ⟨464168, by rfl⟩ : syracuseStep 618891 = 928337) B928337
theorem B618903 : Blo 618297 618903 := bstep (se 1 (by rfl) ⟨464177, by rfl⟩ : syracuseStep 618903 = 928355) B928355
theorem B618923 : Blo 618297 618923 := bstep (se 1 (by rfl) ⟨464192, by rfl⟩ : syracuseStep 618923 = 928385) B928385
theorem B1569203 : Blo 618297 1569203 := bstep (se 1 (by rfl) ⟨1176902, by rfl⟩ : syracuseStep 1569203 = 2353805) B2353805
theorem B618935 : Blo 618297 618935 := bstep (se 1 (by rfl) ⟨464201, by rfl⟩ : syracuseStep 618935 = 928403) B928403
theorem B618955 : Blo 618297 618955 := bstep (se 1 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 618955 = 928433) B928433
theorem B618967 : Blo 618297 618967 := bstep (se 1 (by rfl) ⟨464225, by rfl⟩ : syracuseStep 618967 = 928451) B928451
theorem B618987 : Blo 618297 618987 := bstep (se 1 (by rfl) ⟨464240, by rfl⟩ : syracuseStep 618987 = 928481) B928481
theorem B618999 : Blo 618297 618999 := bstep (se 1 (by rfl) ⟨464249, by rfl⟩ : syracuseStep 618999 = 928499) B928499
theorem B619019 : Blo 618297 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B619031 : Blo 618297 619031 := bstep (se 1 (by rfl) ⟨464273, by rfl⟩ : syracuseStep 619031 = 928547) B928547
theorem B619051 : Blo 618297 619051 := bstep (se 1 (by rfl) ⟨464288, by rfl⟩ : syracuseStep 619051 = 928577) B928577
theorem B2355763 : Blo 618297 2355763 := bstep (se 1 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 2355763 = 3533645) B3533645
theorem B619063 : Blo 618297 619063 := bstep (se 1 (by rfl) ⟨464297, by rfl⟩ : syracuseStep 619063 = 928595) B928595
theorem B2093633 : Blo 618297 2093633 := bstep (se 2 (by rfl) ⟨785112, by rfl⟩ : syracuseStep 2093633 = 1570225) B1570225
theorem B619083 : Blo 618297 619083 := bstep (se 1 (by rfl) ⟨464312, by rfl⟩ : syracuseStep 619083 = 928625) B928625
theorem B619095 : Blo 618297 619095 := bstep (se 1 (by rfl) ⟨464321, by rfl⟩ : syracuseStep 619095 = 928643) B928643
theorem B619115 : Blo 618297 619115 := bstep (se 1 (by rfl) ⟨464336, by rfl⟩ : syracuseStep 619115 = 928673) B928673
theorem B619127 : Blo 618297 619127 := bstep (se 1 (by rfl) ⟨464345, by rfl⟩ : syracuseStep 619127 = 928691) B928691
theorem B619147 : Blo 618297 619147 := bstep (se 1 (by rfl) ⟨464360, by rfl⟩ : syracuseStep 619147 = 928721) B928721
theorem B619159 : Blo 618297 619159 := bstep (se 1 (by rfl) ⟨464369, by rfl⟩ : syracuseStep 619159 = 928739) B928739
theorem B2388631 : Blo 618297 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B619179 : Blo 618297 619179 := bstep (se 1 (by rfl) ⟨464384, by rfl⟩ : syracuseStep 619179 = 928769) B928769
theorem B619191 : Blo 618297 619191 := bstep (se 1 (by rfl) ⟨464393, by rfl⟩ : syracuseStep 619191 = 928787) B928787
theorem B1176257 : Blo 618297 1176257 := bstep (se 2 (by rfl) ⟨441096, by rfl⟩ : syracuseStep 1176257 = 882193) B882193
theorem B619211 : Blo 618297 619211 := bstep (se 1 (by rfl) ⟨464408, by rfl⟩ : syracuseStep 619211 = 928817) B928817
theorem B619223 : Blo 618297 619223 := bstep (se 1 (by rfl) ⟨464417, by rfl⟩ : syracuseStep 619223 = 928835) B928835
theorem B619243 : Blo 618297 619243 := bstep (se 1 (by rfl) ⟨464432, by rfl⟩ : syracuseStep 619243 = 928865) B928865
theorem B619255 : Blo 618297 619255 := bstep (se 1 (by rfl) ⟨464441, by rfl⟩ : syracuseStep 619255 = 928883) B928883
theorem B619275 : Blo 618297 619275 := bstep (se 1 (by rfl) ⟨464456, by rfl⟩ : syracuseStep 619275 = 928913) B928913
theorem B619287 : Blo 618297 619287 := bstep (se 1 (by rfl) ⟨464465, by rfl⟩ : syracuseStep 619287 = 928931) B928931
theorem B1045271 : Blo 618297 1045271 := bstep (se 1 (by rfl) ⟨783953, by rfl⟩ : syracuseStep 1045271 = 1567907) B1567907
theorem B619307 : Blo 618297 619307 := bstep (se 1 (by rfl) ⟨464480, by rfl⟩ : syracuseStep 619307 = 928961) B928961
theorem B619319 : Blo 618297 619319 := bstep (se 1 (by rfl) ⟨464489, by rfl⟩ : syracuseStep 619319 = 928979) B928979
theorem B619339 : Blo 618297 619339 := bstep (se 1 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 619339 = 929009) B929009
theorem B3142475 : Blo 618297 3142475 := bstep (se 1 (by rfl) ⟨2356856, by rfl⟩ : syracuseStep 3142475 = 4713713) B4713713
theorem B619351 : Blo 618297 619351 := bstep (se 1 (by rfl) ⟨464513, by rfl⟩ : syracuseStep 619351 = 929027) B929027
theorem B619371 : Blo 618297 619371 := bstep (se 1 (by rfl) ⟨464528, by rfl⟩ : syracuseStep 619371 = 929057) B929057
theorem B619383 : Blo 618297 619383 := bstep (se 1 (by rfl) ⟨464537, by rfl⟩ : syracuseStep 619383 = 929075) B929075
theorem B619403 : Blo 618297 619403 := bstep (se 1 (by rfl) ⟨464552, by rfl⟩ : syracuseStep 619403 = 929105) B929105
theorem B619415 : Blo 618297 619415 := bstep (se 1 (by rfl) ⟨464561, by rfl⟩ : syracuseStep 619415 = 929123) B929123
theorem B1045399 : Blo 618297 1045399 := bstep (se 1 (by rfl) ⟨784049, by rfl⟩ : syracuseStep 1045399 = 1568099) B1568099
theorem B619435 : Blo 618297 619435 := bstep (se 1 (by rfl) ⟨464576, by rfl⟩ : syracuseStep 619435 = 929153) B929153
theorem B619447 : Blo 618297 619447 := bstep (se 1 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 619447 = 929171) B929171
theorem B619467 : Blo 618297 619467 := bstep (se 1 (by rfl) ⟨464600, by rfl⟩ : syracuseStep 619467 = 929201) B929201
theorem B1569739 : Blo 618297 1569739 := bstep (se 1 (by rfl) ⟨1177304, by rfl⟩ : syracuseStep 1569739 = 2354609) B2354609
theorem B619479 : Blo 618297 619479 := bstep (se 1 (by rfl) ⟨464609, by rfl⟩ : syracuseStep 619479 = 929219) B929219
theorem B619499 : Blo 618297 619499 := bstep (se 1 (by rfl) ⟨464624, by rfl⟩ : syracuseStep 619499 = 929249) B929249
theorem B619511 : Blo 618297 619511 := bstep (se 1 (by rfl) ⟨464633, by rfl⟩ : syracuseStep 619511 = 929267) B929267
theorem B783371 : Blo 618297 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B619531 : Blo 618297 619531 := bstep (se 1 (by rfl) ⟨464648, by rfl⟩ : syracuseStep 619531 = 929297) B929297
theorem B619543 : Blo 618297 619543 := bstep (se 1 (by rfl) ⟨464657, by rfl⟩ : syracuseStep 619543 = 929315) B929315
theorem B1176599 : Blo 618297 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B619563 : Blo 618297 619563 := bstep (se 1 (by rfl) ⟨464672, by rfl⟩ : syracuseStep 619563 = 929345) B929345
theorem B619575 : Blo 618297 619575 := bstep (se 1 (by rfl) ⟨464681, by rfl⟩ : syracuseStep 619575 = 929363) B929363
theorem B3175499 : Blo 618297 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B619595 : Blo 618297 619595 := bstep (se 1 (by rfl) ⟨464696, by rfl⟩ : syracuseStep 619595 = 929393) B929393
theorem B619607 : Blo 618297 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B1569881 : Blo 618297 1569881 := bstep (se 2 (by rfl) ⟨588705, by rfl⟩ : syracuseStep 1569881 = 1177411) B1177411
theorem B2094173 : Blo 618297 2094173 := bstep (se 3 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 2094173 = 785315) B785315
theorem B619627 : Blo 618297 619627 := bstep (se 1 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 619627 = 929441) B929441
theorem B619639 : Blo 618297 619639 := bstep (se 1 (by rfl) ⟨464729, by rfl⟩ : syracuseStep 619639 = 929459) B929459
theorem B619659 : Blo 618297 619659 := bstep (se 1 (by rfl) ⟨464744, by rfl⟩ : syracuseStep 619659 = 929489) B929489
theorem B619671 : Blo 618297 619671 := bstep (se 1 (by rfl) ⟨464753, by rfl⟩ : syracuseStep 619671 = 929507) B929507
theorem B849049 : Blo 618297 849049 := bstep (se 2 (by rfl) ⟨318393, by rfl⟩ : syracuseStep 849049 = 636787) B636787
theorem B619691 : Blo 618297 619691 := bstep (se 1 (by rfl) ⟨464768, by rfl⟩ : syracuseStep 619691 = 929537) B929537
theorem B619703 : Blo 618297 619703 := bstep (se 1 (by rfl) ⟨464777, by rfl⟩ : syracuseStep 619703 = 929555) B929555
theorem B619723 : Blo 618297 619723 := bstep (se 1 (by rfl) ⟨464792, by rfl⟩ : syracuseStep 619723 = 929585) B929585
theorem B6354125 : Blo 618297 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B619735 : Blo 618297 619735 := bstep (se 1 (by rfl) ⟨464801, by rfl⟩ : syracuseStep 619735 = 929603) B929603
theorem B619755 : Blo 618297 619755 := bstep (se 1 (by rfl) ⟨464816, by rfl⟩ : syracuseStep 619755 = 929633) B929633
theorem B619767 : Blo 618297 619767 := bstep (se 1 (by rfl) ⟨464825, by rfl⟩ : syracuseStep 619767 = 929651) B929651
theorem B619787 : Blo 618297 619787 := bstep (se 1 (by rfl) ⟨464840, by rfl⟩ : syracuseStep 619787 = 929681) B929681
theorem B619799 : Blo 618297 619799 := bstep (se 1 (by rfl) ⟨464849, by rfl⟩ : syracuseStep 619799 = 929699) B929699
theorem B619819 : Blo 618297 619819 := bstep (se 1 (by rfl) ⟨464864, by rfl⟩ : syracuseStep 619819 = 929729) B929729
theorem B619831 : Blo 618297 619831 := bstep (se 1 (by rfl) ⟨464873, by rfl⟩ : syracuseStep 619831 = 929747) B929747
theorem B619851 : Blo 618297 619851 := bstep (se 1 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 619851 = 929777) B929777
theorem B619863 : Blo 618297 619863 := bstep (se 1 (by rfl) ⟨464897, by rfl⟩ : syracuseStep 619863 = 929795) B929795
theorem B4289885 : Blo 618297 4289885 := bstep (se 3 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 4289885 = 1608707) B1608707
theorem B619883 : Blo 618297 619883 := bstep (se 1 (by rfl) ⟨464912, by rfl⟩ : syracuseStep 619883 = 929825) B929825
theorem B619895 : Blo 618297 619895 := bstep (se 1 (by rfl) ⟨464921, by rfl⟩ : syracuseStep 619895 = 929843) B929843
theorem B619915 : Blo 618297 619915 := bstep (se 1 (by rfl) ⟨464936, by rfl⟩ : syracuseStep 619915 = 929873) B929873
theorem B619927 : Blo 618297 619927 := bstep (se 1 (by rfl) ⟨464945, by rfl⟩ : syracuseStep 619927 = 929891) B929891
theorem B619947 : Blo 618297 619947 := bstep (se 1 (by rfl) ⟨464960, by rfl⟩ : syracuseStep 619947 = 929921) B929921
theorem B619959 : Blo 618297 619959 := bstep (se 1 (by rfl) ⟨464969, by rfl⟩ : syracuseStep 619959 = 929939) B929939
theorem B619979 : Blo 618297 619979 := bstep (se 1 (by rfl) ⟨464984, by rfl⟩ : syracuseStep 619979 = 929969) B929969
theorem B619991 : Blo 618297 619991 := bstep (se 1 (by rfl) ⟨464993, by rfl⟩ : syracuseStep 619991 = 929987) B929987
theorem B620011 : Blo 618297 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B620023 : Blo 618297 620023 := bstep (se 1 (by rfl) ⟨465017, by rfl⟩ : syracuseStep 620023 = 930035) B930035
theorem B1046027 : Blo 618297 1046027 := bstep (se 1 (by rfl) ⟨784520, by rfl⟩ : syracuseStep 1046027 = 1569041) B1569041
theorem B620043 : Blo 618297 620043 := bstep (se 1 (by rfl) ⟨465032, by rfl⟩ : syracuseStep 620043 = 930065) B930065
theorem B620055 : Blo 618297 620055 := bstep (se 1 (by rfl) ⟨465041, by rfl⟩ : syracuseStep 620055 = 930083) B930083
theorem B620075 : Blo 618297 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B620087 : Blo 618297 620087 := bstep (se 1 (by rfl) ⟨465065, by rfl⟩ : syracuseStep 620087 = 930131) B930131
theorem B620107 : Blo 618297 620107 := bstep (se 1 (by rfl) ⟨465080, by rfl⟩ : syracuseStep 620107 = 930161) B930161
theorem B2651723 : Blo 618297 2651723 := bstep (se 1 (by rfl) ⟨1988792, by rfl⟩ : syracuseStep 2651723 = 3977585) B3977585
theorem B620119 : Blo 618297 620119 := bstep (se 1 (by rfl) ⟨465089, by rfl⟩ : syracuseStep 620119 = 930179) B930179
theorem B1767005 : Blo 618297 1767005 := bstep (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) B662627
theorem B620139 : Blo 618297 620139 := bstep (se 1 (by rfl) ⟨465104, by rfl⟩ : syracuseStep 620139 = 930209) B930209
theorem B620151 : Blo 618297 620151 := bstep (se 1 (by rfl) ⟨465113, by rfl⟩ : syracuseStep 620151 = 930227) B930227
theorem B1046155 : Blo 618297 1046155 := bstep (se 1 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 1046155 = 1569233) B1569233
theorem B620171 : Blo 618297 620171 := bstep (se 1 (by rfl) ⟨465128, by rfl⟩ : syracuseStep 620171 = 930257) B930257
theorem B620183 : Blo 618297 620183 := bstep (se 1 (by rfl) ⟨465137, by rfl⟩ : syracuseStep 620183 = 930275) B930275
theorem B620203 : Blo 618297 620203 := bstep (se 1 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 620203 = 930305) B930305
theorem B1177267 : Blo 618297 1177267 := bstep (se 1 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 1177267 = 1765901) B1765901
theorem B620215 : Blo 618297 620215 := bstep (se 1 (by rfl) ⟨465161, by rfl⟩ : syracuseStep 620215 = 930323) B930323
theorem B784075 : Blo 618297 784075 := bstep (se 1 (by rfl) ⟨588056, by rfl⟩ : syracuseStep 784075 = 1176113) B1176113
theorem B620235 : Blo 618297 620235 := bstep (se 1 (by rfl) ⟨465176, by rfl⟩ : syracuseStep 620235 = 930353) B930353
theorem B620247 : Blo 618297 620247 := bstep (se 1 (by rfl) ⟨465185, by rfl⟩ : syracuseStep 620247 = 930371) B930371
theorem B620267 : Blo 618297 620267 := bstep (se 1 (by rfl) ⟨465200, by rfl⟩ : syracuseStep 620267 = 930401) B930401
theorem B620279 : Blo 618297 620279 := bstep (se 1 (by rfl) ⟨465209, by rfl⟩ : syracuseStep 620279 = 930419) B930419
theorem B620299 : Blo 618297 620299 := bstep (se 1 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 620299 = 930449) B930449
theorem B2357009 : Blo 618297 2357009 := bstep (se 2 (by rfl) ⟨883878, by rfl⟩ : syracuseStep 2357009 = 1767757) B1767757
theorem B620311 : Blo 618297 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B1046297 : Blo 618297 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B620331 : Blo 618297 620331 := bstep (se 1 (by rfl) ⟨465248, by rfl⟩ : syracuseStep 620331 = 930497) B930497
theorem B2520877 : Blo 618297 2520877 := bstep (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) B945329
theorem B620343 : Blo 618297 620343 := bstep (se 1 (by rfl) ⟨465257, by rfl⟩ : syracuseStep 620343 = 930515) B930515
theorem B1767233 : Blo 618297 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B620363 : Blo 618297 620363 := bstep (se 1 (by rfl) ⟨465272, by rfl⟩ : syracuseStep 620363 = 930545) B930545
theorem B620375 : Blo 618297 620375 := bstep (se 1 (by rfl) ⟨465281, by rfl⟩ : syracuseStep 620375 = 930563) B930563
theorem B620395 : Blo 618297 620395 := bstep (se 1 (by rfl) ⟨465296, by rfl⟩ : syracuseStep 620395 = 930593) B930593
theorem B620407 : Blo 618297 620407 := bstep (se 1 (by rfl) ⟨465305, by rfl⟩ : syracuseStep 620407 = 930611) B930611
theorem B620427 : Blo 618297 620427 := bstep (se 1 (by rfl) ⟨465320, by rfl⟩ : syracuseStep 620427 = 930641) B930641
theorem B620439 : Blo 618297 620439 := bstep (se 1 (by rfl) ⟨465329, by rfl⟩ : syracuseStep 620439 = 930659) B930659
theorem B1570711 : Blo 618297 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1046425 : Blo 618297 1046425 := bstep (se 2 (by rfl) ⟨392409, by rfl⟩ : syracuseStep 1046425 = 784819) B784819
theorem B620459 : Blo 618297 620459 := bstep (se 1 (by rfl) ⟨465344, by rfl⟩ : syracuseStep 620459 = 930689) B930689
theorem B620471 : Blo 618297 620471 := bstep (se 1 (by rfl) ⟨465353, by rfl⟩ : syracuseStep 620471 = 930707) B930707
theorem B620491 : Blo 618297 620491 := bstep (se 1 (by rfl) ⟨465368, by rfl⟩ : syracuseStep 620491 = 930737) B930737
theorem B784343 : Blo 618297 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B620503 : Blo 618297 620503 := bstep (se 1 (by rfl) ⟨465377, by rfl⟩ : syracuseStep 620503 = 930755) B930755
theorem B620523 : Blo 618297 620523 := bstep (se 1 (by rfl) ⟨465392, by rfl⟩ : syracuseStep 620523 = 930785) B930785
theorem B620535 : Blo 618297 620535 := bstep (se 1 (by rfl) ⟨465401, by rfl⟩ : syracuseStep 620535 = 930803) B930803
theorem B620555 : Blo 618297 620555 := bstep (se 1 (by rfl) ⟨465416, by rfl⟩ : syracuseStep 620555 = 930833) B930833
theorem B620567 : Blo 618297 620567 := bstep (se 1 (by rfl) ⟨465425, by rfl⟩ : syracuseStep 620567 = 930851) B930851
theorem B620587 : Blo 618297 620587 := bstep (se 1 (by rfl) ⟨465440, by rfl⟩ : syracuseStep 620587 = 930881) B930881
theorem B620599 : Blo 618297 620599 := bstep (se 1 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 620599 = 930899) B930899
theorem B620619 : Blo 618297 620619 := bstep (se 1 (by rfl) ⟨465464, by rfl⟩ : syracuseStep 620619 = 930929) B930929
theorem B620631 : Blo 618297 620631 := bstep (se 1 (by rfl) ⟨465473, by rfl⟩ : syracuseStep 620631 = 930947) B930947
theorem B620651 : Blo 618297 620651 := bstep (se 1 (by rfl) ⟨465488, by rfl⟩ : syracuseStep 620651 = 930977) B930977
theorem B1177715 : Blo 618297 1177715 := bstep (se 1 (by rfl) ⟨883286, by rfl⟩ : syracuseStep 1177715 = 1766573) B1766573
theorem B620663 : Blo 618297 620663 := bstep (se 1 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 620663 = 930995) B930995
theorem B2521219 : Blo 618297 2521219 := bstep (se 1 (by rfl) ⟨1890914, by rfl⟩ : syracuseStep 2521219 = 3781829) B3781829
theorem B620683 : Blo 618297 620683 := bstep (se 1 (by rfl) ⟨465512, by rfl⟩ : syracuseStep 620683 = 931025) B931025
theorem B620695 : Blo 618297 620695 := bstep (se 1 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 620695 = 931043) B931043
theorem B1767575 : Blo 618297 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B1177753 : Blo 618297 1177753 := bstep (se 2 (by rfl) ⟨441657, by rfl⟩ : syracuseStep 1177753 = 883315) B883315
theorem B620715 : Blo 618297 620715 := bstep (se 1 (by rfl) ⟨465536, by rfl⟩ : syracuseStep 620715 = 931073) B931073
theorem B620727 : Blo 618297 620727 := bstep (se 1 (by rfl) ⟨465545, by rfl⟩ : syracuseStep 620727 = 931091) B931091
theorem B620747 : Blo 618297 620747 := bstep (se 1 (by rfl) ⟨465560, by rfl⟩ : syracuseStep 620747 = 931121) B931121
theorem B2095307 : Blo 618297 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B620759 : Blo 618297 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B620779 : Blo 618297 620779 := bstep (se 1 (by rfl) ⟨465584, by rfl⟩ : syracuseStep 620779 = 931169) B931169
theorem B620791 : Blo 618297 620791 := bstep (se 1 (by rfl) ⟨465593, by rfl⟩ : syracuseStep 620791 = 931187) B931187
theorem B620811 : Blo 618297 620811 := bstep (se 1 (by rfl) ⟨465608, by rfl⟩ : syracuseStep 620811 = 931217) B931217
theorem B620823 : Blo 618297 620823 := bstep (se 1 (by rfl) ⟨465617, by rfl⟩ : syracuseStep 620823 = 931235) B931235
theorem B620843 : Blo 618297 620843 := bstep (se 1 (by rfl) ⟨465632, by rfl⟩ : syracuseStep 620843 = 931265) B931265
theorem B620855 : Blo 618297 620855 := bstep (se 1 (by rfl) ⟨465641, by rfl⟩ : syracuseStep 620855 = 931283) B931283
theorem B1571147 : Blo 618297 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B620875 : Blo 618297 620875 := bstep (se 1 (by rfl) ⟨465656, by rfl⟩ : syracuseStep 620875 = 931313) B931313
theorem B620887 : Blo 618297 620887 := bstep (se 1 (by rfl) ⟨465665, by rfl⟩ : syracuseStep 620887 = 931331) B931331
theorem B620907 : Blo 618297 620907 := bstep (se 1 (by rfl) ⟨465680, by rfl⟩ : syracuseStep 620907 = 931361) B931361
theorem B620919 : Blo 618297 620919 := bstep (se 1 (by rfl) ⟨465689, by rfl⟩ : syracuseStep 620919 = 931379) B931379
theorem B5306755 : Blo 618297 5306755 := bstep (se 1 (by rfl) ⟨3980066, by rfl⟩ : syracuseStep 5306755 = 7960133) B7960133
theorem B620939 : Blo 618297 620939 := bstep (se 1 (by rfl) ⟨465704, by rfl⟩ : syracuseStep 620939 = 931409) B931409
theorem B620951 : Blo 618297 620951 := bstep (se 1 (by rfl) ⟨465713, by rfl⟩ : syracuseStep 620951 = 931427) B931427
theorem B620971 : Blo 618297 620971 := bstep (se 1 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 620971 = 931457) B931457
theorem B620983 : Blo 618297 620983 := bstep (se 1 (by rfl) ⟨465737, by rfl⟩ : syracuseStep 620983 = 931475) B931475
theorem B2357707 : Blo 618297 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B621003 : Blo 618297 621003 := bstep (se 1 (by rfl) ⟨465752, by rfl⟩ : syracuseStep 621003 = 931505) B931505
theorem B1046999 : Blo 618297 1046999 := bstep (se 1 (by rfl) ⟨785249, by rfl⟩ : syracuseStep 1046999 = 1570499) B1570499
theorem B621015 : Blo 618297 621015 := bstep (se 1 (by rfl) ⟨465761, by rfl⟩ : syracuseStep 621015 = 931523) B931523
theorem B2095577 : Blo 618297 2095577 := bstep (se 2 (by rfl) ⟨785841, by rfl⟩ : syracuseStep 2095577 = 1571683) B1571683
theorem B621035 : Blo 618297 621035 := bstep (se 1 (by rfl) ⟨465776, by rfl⟩ : syracuseStep 621035 = 931553) B931553
theorem B621047 : Blo 618297 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B621067 : Blo 618297 621067 := bstep (se 1 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 621067 = 931601) B931601
theorem B2652695 : Blo 618297 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B621079 : Blo 618297 621079 := bstep (se 1 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 621079 = 931619) B931619
theorem B621099 : Blo 618297 621099 := bstep (se 1 (by rfl) ⟨465824, by rfl⟩ : syracuseStep 621099 = 931649) B931649
theorem B3963437 : Blo 618297 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B621111 : Blo 618297 621111 := bstep (se 1 (by rfl) ⟨465833, by rfl⟩ : syracuseStep 621111 = 931667) B931667
theorem B3144257 : Blo 618297 3144257 := bstep (se 2 (by rfl) ⟨1179096, by rfl⟩ : syracuseStep 3144257 = 2358193) B2358193
theorem B5044801 : Blo 618297 5044801 := bstep (se 2 (by rfl) ⟨1891800, by rfl⟩ : syracuseStep 5044801 = 3783601) B3783601
theorem B621131 : Blo 618297 621131 := bstep (se 1 (by rfl) ⟨465848, by rfl⟩ : syracuseStep 621131 = 931697) B931697
theorem B1047127 : Blo 618297 1047127 := bstep (se 1 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 1047127 = 1570691) B1570691
theorem B621143 : Blo 618297 621143 := bstep (se 1 (by rfl) ⟨465857, by rfl⟩ : syracuseStep 621143 = 931715) B931715
theorem B1178201 : Blo 618297 1178201 := bstep (se 2 (by rfl) ⟨441825, by rfl⟩ : syracuseStep 1178201 = 883651) B883651
theorem B621163 : Blo 618297 621163 := bstep (se 1 (by rfl) ⟨465872, by rfl⟩ : syracuseStep 621163 = 931745) B931745
theorem B621175 : Blo 618297 621175 := bstep (se 1 (by rfl) ⟨465881, by rfl⟩ : syracuseStep 621175 = 931763) B931763
theorem B621195 : Blo 618297 621195 := bstep (se 1 (by rfl) ⟨465896, by rfl⟩ : syracuseStep 621195 = 931793) B931793
theorem B785047 : Blo 618297 785047 := bstep (se 1 (by rfl) ⟨588785, by rfl⟩ : syracuseStep 785047 = 1177571) B1177571
theorem B621207 : Blo 618297 621207 := bstep (se 1 (by rfl) ⟨465905, by rfl⟩ : syracuseStep 621207 = 931811) B931811
theorem B621227 : Blo 618297 621227 := bstep (se 1 (by rfl) ⟨465920, by rfl⟩ : syracuseStep 621227 = 931841) B931841
theorem B621239 : Blo 618297 621239 := bstep (se 1 (by rfl) ⟨465929, by rfl⟩ : syracuseStep 621239 = 931859) B931859
theorem B1571521 : Blo 618297 1571521 := bstep (se 2 (by rfl) ⟨589320, by rfl⟩ : syracuseStep 1571521 = 1178641) B1178641
theorem B621259 : Blo 618297 621259 := bstep (se 1 (by rfl) ⟨465944, by rfl⟩ : syracuseStep 621259 = 931889) B931889
theorem B621271 : Blo 618297 621271 := bstep (se 1 (by rfl) ⟨465953, by rfl⟩ : syracuseStep 621271 = 931907) B931907
theorem B2357981 : Blo 618297 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B621291 : Blo 618297 621291 := bstep (se 1 (by rfl) ⟨465968, by rfl⟩ : syracuseStep 621291 = 931937) B931937
theorem B621303 : Blo 618297 621303 := bstep (se 1 (by rfl) ⟨465977, by rfl⟩ : syracuseStep 621303 = 931955) B931955
theorem B621323 : Blo 618297 621323 := bstep (se 1 (by rfl) ⟨465992, by rfl⟩ : syracuseStep 621323 = 931985) B931985
theorem B3767057 : Blo 618297 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B621335 : Blo 618297 621335 := bstep (se 1 (by rfl) ⟨466001, by rfl⟩ : syracuseStep 621335 = 932003) B932003
theorem B621355 : Blo 618297 621355 := bstep (se 1 (by rfl) ⟨466016, by rfl⟩ : syracuseStep 621355 = 932033) B932033
theorem B621367 : Blo 618297 621367 := bstep (se 1 (by rfl) ⟨466025, by rfl⟩ : syracuseStep 621367 = 932051) B932051
theorem B621387 : Blo 618297 621387 := bstep (se 1 (by rfl) ⟨466040, by rfl⟩ : syracuseStep 621387 = 932081) B932081
theorem B883543 : Blo 618297 883543 := bstep (se 1 (by rfl) ⟨662657, by rfl⟩ : syracuseStep 883543 = 1325315) B1325315
theorem B621399 : Blo 618297 621399 := bstep (se 1 (by rfl) ⟨466049, by rfl⟩ : syracuseStep 621399 = 932099) B932099
theorem B621419 : Blo 618297 621419 := bstep (se 1 (by rfl) ⟨466064, by rfl⟩ : syracuseStep 621419 = 932129) B932129
theorem B621431 : Blo 618297 621431 := bstep (se 1 (by rfl) ⟨466073, by rfl⟩ : syracuseStep 621431 = 932147) B932147
theorem B621451 : Blo 618297 621451 := bstep (se 1 (by rfl) ⟨466088, by rfl⟩ : syracuseStep 621451 = 932177) B932177
theorem B621463 : Blo 618297 621463 := bstep (se 1 (by rfl) ⟨466097, by rfl⟩ : syracuseStep 621463 = 932195) B932195
theorem B621483 : Blo 618297 621483 := bstep (se 1 (by rfl) ⟨466112, by rfl⟩ : syracuseStep 621483 = 932225) B932225
theorem B621495 : Blo 618297 621495 := bstep (se 1 (by rfl) ⟨466121, by rfl⟩ : syracuseStep 621495 = 932243) B932243
theorem B621515 : Blo 618297 621515 := bstep (se 1 (by rfl) ⟨466136, by rfl⟩ : syracuseStep 621515 = 932273) B932273
theorem B621527 : Blo 618297 621527 := bstep (se 1 (by rfl) ⟨466145, by rfl⟩ : syracuseStep 621527 = 932291) B932291
theorem B621547 : Blo 618297 621547 := bstep (se 1 (by rfl) ⟨466160, by rfl⟩ : syracuseStep 621547 = 932321) B932321
theorem B621559 : Blo 618297 621559 := bstep (se 1 (by rfl) ⟨466169, by rfl⟩ : syracuseStep 621559 = 932339) B932339
theorem B621579 : Blo 618297 621579 := bstep (se 1 (by rfl) ⟨466184, by rfl⟩ : syracuseStep 621579 = 932369) B932369
theorem B621591 : Blo 618297 621591 := bstep (se 1 (by rfl) ⟨466193, by rfl⟩ : syracuseStep 621591 = 932387) B932387
theorem B621611 : Blo 618297 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B621623 : Blo 618297 621623 := bstep (se 1 (by rfl) ⟨466217, by rfl⟩ : syracuseStep 621623 = 932435) B932435
theorem B621643 : Blo 618297 621643 := bstep (se 1 (by rfl) ⟨466232, by rfl⟩ : syracuseStep 621643 = 932465) B932465
theorem B621655 : Blo 618297 621655 := bstep (se 1 (by rfl) ⟨466241, by rfl⟩ : syracuseStep 621655 = 932483) B932483
theorem B621675 : Blo 618297 621675 := bstep (se 1 (by rfl) ⟨466256, by rfl⟩ : syracuseStep 621675 = 932513) B932513
theorem B621687 : Blo 618297 621687 := bstep (se 1 (by rfl) ⟨466265, by rfl⟩ : syracuseStep 621687 = 932531) B932531
theorem B621707 : Blo 618297 621707 := bstep (se 1 (by rfl) ⟨466280, by rfl⟩ : syracuseStep 621707 = 932561) B932561
theorem B2096279 : Blo 618297 2096279 := bstep (se 1 (by rfl) ⟨1572209, by rfl⟩ : syracuseStep 2096279 = 3144419) B3144419
theorem B621719 : Blo 618297 621719 := bstep (se 1 (by rfl) ⟨466289, by rfl⟩ : syracuseStep 621719 = 932579) B932579
theorem B621739 : Blo 618297 621739 := bstep (se 1 (by rfl) ⟨466304, by rfl⟩ : syracuseStep 621739 = 932609) B932609
theorem B621751 : Blo 618297 621751 := bstep (se 1 (by rfl) ⟨466313, by rfl⟩ : syracuseStep 621751 = 932627) B932627
theorem B1047755 : Blo 618297 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B621771 : Blo 618297 621771 := bstep (se 1 (by rfl) ⟨466328, by rfl⟩ : syracuseStep 621771 = 932657) B932657
theorem B621783 : Blo 618297 621783 := bstep (se 1 (by rfl) ⟨466337, by rfl⟩ : syracuseStep 621783 = 932675) B932675
theorem B621803 : Blo 618297 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B621815 : Blo 618297 621815 := bstep (se 1 (by rfl) ⟨466361, by rfl⟩ : syracuseStep 621815 = 932723) B932723
theorem B621835 : Blo 618297 621835 := bstep (se 1 (by rfl) ⟨466376, by rfl⟩ : syracuseStep 621835 = 932753) B932753
theorem B1572119 : Blo 618297 1572119 := bstep (se 1 (by rfl) ⟨1179089, by rfl⟩ : syracuseStep 1572119 = 2358179) B2358179
theorem B621847 : Blo 618297 621847 := bstep (se 1 (by rfl) ⟨466385, by rfl⟩ : syracuseStep 621847 = 932771) B932771
theorem B621867 : Blo 618297 621867 := bstep (se 1 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 621867 = 932801) B932801
theorem B2424109 : Blo 618297 2424109 := bstep (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) B909041
theorem B621879 : Blo 618297 621879 := bstep (se 1 (by rfl) ⟨466409, by rfl⟩ : syracuseStep 621879 = 932819) B932819
theorem B1178945 : Blo 618297 1178945 := bstep (se 2 (by rfl) ⟨442104, by rfl⟩ : syracuseStep 1178945 = 884209) B884209
theorem B5307713 : Blo 618297 5307713 := bstep (se 2 (by rfl) ⟨1990392, by rfl⟩ : syracuseStep 5307713 = 3980785) B3980785
theorem B1047883 : Blo 618297 1047883 := bstep (se 1 (by rfl) ⟨785912, by rfl⟩ : syracuseStep 1047883 = 1571825) B1571825
theorem B621899 : Blo 618297 621899 := bstep (se 1 (by rfl) ⟨466424, by rfl⟩ : syracuseStep 621899 = 932849) B932849
theorem B621911 : Blo 618297 621911 := bstep (se 1 (by rfl) ⟨466433, by rfl⟩ : syracuseStep 621911 = 932867) B932867
theorem B621931 : Blo 618297 621931 := bstep (se 1 (by rfl) ⟨466448, by rfl⟩ : syracuseStep 621931 = 932897) B932897
theorem B621943 : Blo 618297 621943 := bstep (se 1 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 621943 = 932915) B932915
theorem B621963 : Blo 618297 621963 := bstep (se 1 (by rfl) ⟨466472, by rfl⟩ : syracuseStep 621963 = 932945) B932945
theorem B2358679 : Blo 618297 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B621975 : Blo 618297 621975 := bstep (se 1 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 621975 = 932963) B932963
theorem B621995 : Blo 618297 621995 := bstep (se 1 (by rfl) ⟨466496, by rfl⟩ : syracuseStep 621995 = 932993) B932993
theorem B622007 : Blo 618297 622007 := bstep (se 1 (by rfl) ⟨466505, by rfl⟩ : syracuseStep 622007 = 933011) B933011
theorem B622027 : Blo 618297 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B622039 : Blo 618297 622039 := bstep (se 1 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 622039 = 933059) B933059
theorem B1048025 : Blo 618297 1048025 := bstep (se 2 (by rfl) ⟨393009, by rfl⟩ : syracuseStep 1048025 = 786019) B786019
theorem B622059 : Blo 618297 622059 := bstep (se 1 (by rfl) ⟨466544, by rfl⟩ : syracuseStep 622059 = 933089) B933089
theorem B622071 : Blo 618297 622071 := bstep (se 1 (by rfl) ⟨466553, by rfl⟩ : syracuseStep 622071 = 933107) B933107
theorem B622091 : Blo 618297 622091 := bstep (se 1 (by rfl) ⟨466568, by rfl⟩ : syracuseStep 622091 = 933137) B933137
theorem B622103 : Blo 618297 622103 := bstep (se 1 (by rfl) ⟨466577, by rfl⟩ : syracuseStep 622103 = 933155) B933155
theorem B622123 : Blo 618297 622123 := bstep (se 1 (by rfl) ⟨466592, by rfl⟩ : syracuseStep 622123 = 933185) B933185
theorem B622135 : Blo 618297 622135 := bstep (se 1 (by rfl) ⟨466601, by rfl⟩ : syracuseStep 622135 = 933203) B933203
theorem B1179211 : Blo 618297 1179211 := bstep (se 1 (by rfl) ⟨884408, by rfl⟩ : syracuseStep 1179211 = 1768817) B1768817
theorem B622155 : Blo 618297 622155 := bstep (se 1 (by rfl) ⟨466616, by rfl⟩ : syracuseStep 622155 = 933233) B933233
theorem B622167 : Blo 618297 622167 := bstep (se 1 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 622167 = 933251) B933251
theorem B1048153 : Blo 618297 1048153 := bstep (se 2 (by rfl) ⟨393057, by rfl⟩ : syracuseStep 1048153 = 786115) B786115
theorem B622187 : Blo 618297 622187 := bstep (se 1 (by rfl) ⟨466640, by rfl⟩ : syracuseStep 622187 = 933281) B933281
theorem B622199 : Blo 618297 622199 := bstep (se 1 (by rfl) ⟨466649, by rfl⟩ : syracuseStep 622199 = 933299) B933299
theorem B622219 : Blo 618297 622219 := bstep (se 1 (by rfl) ⟨466664, by rfl⟩ : syracuseStep 622219 = 933329) B933329
theorem B622231 : Blo 618297 622231 := bstep (se 1 (by rfl) ⟨466673, by rfl⟩ : syracuseStep 622231 = 933347) B933347
theorem B622251 : Blo 618297 622251 := bstep (se 1 (by rfl) ⟨466688, by rfl⟩ : syracuseStep 622251 = 933377) B933377
theorem B2981555 : Blo 618297 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B2096819 : Blo 618297 2096819 := bstep (se 1 (by rfl) ⟨1572614, by rfl⟩ : syracuseStep 2096819 = 3145229) B3145229
theorem B622263 : Blo 618297 622263 := bstep (se 1 (by rfl) ⟨466697, by rfl⟩ : syracuseStep 622263 = 933395) B933395
theorem B622283 : Blo 618297 622283 := bstep (se 1 (by rfl) ⟨466712, by rfl⟩ : syracuseStep 622283 = 933425) B933425
theorem B622295 : Blo 618297 622295 := bstep (se 1 (by rfl) ⟨466721, by rfl⟩ : syracuseStep 622295 = 933443) B933443
theorem B2097089 : Blo 618297 2097089 := bstep (se 2 (by rfl) ⟨786408, by rfl⟩ : syracuseStep 2097089 = 1572817) B1572817
theorem B786439 : Blo 618297 786439 := bstep (se 1 (by rfl) ⟨589829, by rfl⟩ : syracuseStep 786439 = 1179659) B1179659
theorem B1048619 : Blo 618297 1048619 := bstep (se 1 (by rfl) ⟨786464, by rfl⟩ : syracuseStep 1048619 = 1572929) B1572929
theorem B1572979 : Blo 618297 1572979 := bstep (se 1 (by rfl) ⟨1179734, by rfl⟩ : syracuseStep 1572979 = 2359469) B2359469
theorem B1507513 : Blo 618297 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B1573121 : Blo 618297 1573121 := bstep (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) B1179841
theorem B1179947 : Blo 618297 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B2097467 : Blo 618297 2097467 := bstep (se 1 (by rfl) ⟨1573100, by rfl⟩ : syracuseStep 2097467 = 3146201) B3146201
theorem B1049017 : Blo 618297 1049017 := bstep (se 2 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 1049017 = 786763) B786763
theorem B786935 : Blo 618297 786935 := bstep (se 1 (by rfl) ⟨590201, by rfl⟩ : syracuseStep 786935 = 1180403) B1180403
theorem B1770103 : Blo 618297 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B787087 : Blo 618297 787087 := bstep (se 1 (by rfl) ⟨590315, by rfl⟩ : syracuseStep 787087 = 1180631) B1180631
theorem B1573577 : Blo 618297 1573577 := bstep (se 2 (by rfl) ⟨590091, by rfl⟩ : syracuseStep 1573577 = 1180183) B1180183
theorem B2097953 : Blo 618297 2097953 := bstep (se 2 (by rfl) ⟨786732, by rfl⟩ : syracuseStep 2097953 = 1573465) B1573465
theorem B2360123 : Blo 618297 2360123 := bstep (se 1 (by rfl) ⟨1770092, by rfl⟩ : syracuseStep 2360123 = 3540185) B3540185
theorem B787259 : Blo 618297 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B3539933 : Blo 618297 3539933 := bstep (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) B1327475
theorem B1573931 : Blo 618297 1573931 := bstep (se 1 (by rfl) ⟨1180448, by rfl⟩ : syracuseStep 1573931 = 2360897) B2360897
theorem B3179587 : Blo 618297 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B1049719 : Blo 618297 1049719 := bstep (se 1 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 1049719 = 1574579) B1574579
theorem B2360609 : Blo 618297 2360609 := bstep (se 2 (by rfl) ⟨885228, by rfl⟩ : syracuseStep 2360609 = 1770457) B1770457
theorem B1049915 : Blo 618297 1049915 := bstep (se 1 (by rfl) ⟨787436, by rfl⟩ : syracuseStep 1049915 = 1574873) B1574873
theorem B6817117 : Blo 618297 6817117 := bstep (se 3 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 6817117 = 2556419) B2556419
theorem B2098547 : Blo 618297 2098547 := bstep (se 1 (by rfl) ⟨1573910, by rfl⟩ : syracuseStep 2098547 = 3147821) B3147821
theorem B1672595 : Blo 618297 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B11306425 : Blo 618297 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B1115849 : Blo 618297 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B1410859 : Blo 618297 1410859 := bstep (se 1 (by rfl) ⟨1058144, by rfl⟩ : syracuseStep 1410859 = 2116289) B2116289
theorem B1771379 : Blo 618297 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1574923 : Blo 618297 1574923 := bstep (se 1 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 1574923 = 2362385) B2362385
theorem B1771607 : Blo 618297 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B1575065 : Blo 618297 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B2361581 : Blo 618297 2361581 := bstep (se 3 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 2361581 = 885593) B885593
theorem B2361899 : Blo 618297 2361899 := bstep (se 1 (by rfl) ⟨1771424, by rfl⟩ : syracuseStep 2361899 = 3542849) B3542849
theorem B1116857 : Blo 618297 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B7047971 : Blo 618297 7047971 := bstep (se 1 (by rfl) ⟨5285978, by rfl⟩ : syracuseStep 7047971 = 10571957) B10571957
theorem B3345299 : Blo 618297 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B2985437 : Blo 618297 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B2985665 : Blo 618297 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B1117967 : Blo 618297 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B3543101 : Blo 618297 3543101 := bstep (se 3 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 3543101 = 1328663) B1328663
theorem B1675417 : Blo 618297 1675417 := bstep (se 2 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 1675417 = 1256563) B1256563
theorem B2232893 : Blo 618297 2232893 := bstep (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) B837335
theorem B1676065 : Blo 618297 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B2233601 : Blo 618297 2233601 := bstep (se 2 (by rfl) ⟨837600, by rfl⟩ : syracuseStep 2233601 = 1675201) B1675201
theorem B7968131 : Blo 618297 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B661051 : Blo 618297 661051 := bstep (se 1 (by rfl) ⟨495788, by rfl⟩ : syracuseStep 661051 = 991577) B991577
theorem B2233975 : Blo 618297 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B8918707 : Blo 618297 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B4528261 : Blo 618297 4528261 := bstep (se 4 (by rfl) ⟨424524, by rfl⟩ : syracuseStep 4528261 = 849049) B849049
theorem B3184841 : Blo 618297 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B4299155 : Blo 618297 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B1514099 : Blo 618297 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B1514137 : Blo 618297 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B695695 : Blo 618297 695695 := bstep (se 1 (by rfl) ⟨521771, by rfl⟩ : syracuseStep 695695 = 1043543) B1043543
theorem B1678877 : Blo 618297 1678877 := bstep (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) B629579
theorem B16293527 : Blo 618297 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B991019 : Blo 618297 991019 := bstep (se 1 (by rfl) ⟨743264, by rfl⟩ : syracuseStep 991019 = 1486529) B1486529
theorem B696199 : Blo 618297 696199 := bstep (se 1 (by rfl) ⟨522149, by rfl⟩ : syracuseStep 696199 = 1044299) B1044299
theorem B696379 : Blo 618297 696379 := bstep (se 1 (by rfl) ⟨522284, by rfl⟩ : syracuseStep 696379 = 1044569) B1044569
theorem B663823 : Blo 618297 663823 := bstep (se 1 (by rfl) ⟨497867, by rfl⟩ : syracuseStep 663823 = 995735) B995735
theorem B1253675 : Blo 618297 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B696847 : Blo 618297 696847 := bstep (se 1 (by rfl) ⟨522635, by rfl⟩ : syracuseStep 696847 = 1045271) B1045271
theorem B6726401 : Blo 618297 6726401 := bstep (se 2 (by rfl) ⟨2522400, by rfl⟩ : syracuseStep 6726401 = 5044801) B5044801
theorem B4236083 : Blo 618297 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B2859923 : Blo 618297 2859923 := bstep (se 1 (by rfl) ⟨2144942, by rfl⟩ : syracuseStep 2859923 = 4289885) B4289885
theorem B697351 : Blo 618297 697351 := bstep (se 1 (by rfl) ⟨523013, by rfl⟩ : syracuseStep 697351 = 1046027) B1046027
theorem B2237507 : Blo 618297 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B697531 : Blo 618297 697531 := bstep (se 1 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 697531 = 1046297) B1046297
theorem B3024263 : Blo 618297 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B697999 : Blo 618297 697999 := bstep (se 1 (by rfl) ⟨523499, by rfl⟩ : syracuseStep 697999 = 1046999) B1046999
theorem B927479 : Blo 618297 927479 := bstep (se 1 (by rfl) ⟨695609, by rfl⟩ : syracuseStep 927479 = 1391219) B1391219
theorem B927503 : Blo 618297 927503 := bstep (se 1 (by rfl) ⟨695627, by rfl⟩ : syracuseStep 927503 = 1391255) B1391255
theorem B927545 : Blo 618297 927545 := bstep (se 2 (by rfl) ⟨347829, by rfl⟩ : syracuseStep 927545 = 695659) B695659
theorem B927623 : Blo 618297 927623 := bstep (se 1 (by rfl) ⟨695717, by rfl⟩ : syracuseStep 927623 = 1391435) B1391435
theorem B927659 : Blo 618297 927659 := bstep (se 1 (by rfl) ⟨695744, by rfl⟩ : syracuseStep 927659 = 1391489) B1391489
theorem B927689 : Blo 618297 927689 := bstep (se 2 (by rfl) ⟨347883, by rfl⟩ : syracuseStep 927689 = 695767) B695767
theorem B11937739 : Blo 618297 11937739 := bstep (se 1 (by rfl) ⟨8953304, by rfl⟩ : syracuseStep 11937739 = 17906609) B17906609
theorem B927803 : Blo 618297 927803 := bstep (se 1 (by rfl) ⟨695852, by rfl⟩ : syracuseStep 927803 = 1391705) B1391705
theorem B927863 : Blo 618297 927863 := bstep (se 1 (by rfl) ⟨695897, by rfl⟩ : syracuseStep 927863 = 1391795) B1391795
theorem B698503 : Blo 618297 698503 := bstep (se 1 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 698503 = 1047755) B1047755
theorem B927887 : Blo 618297 927887 := bstep (se 1 (by rfl) ⟨695915, by rfl⟩ : syracuseStep 927887 = 1391831) B1391831
theorem B927929 : Blo 618297 927929 := bstep (se 2 (by rfl) ⟨347973, by rfl⟩ : syracuseStep 927929 = 695947) B695947
theorem B928007 : Blo 618297 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B928043 : Blo 618297 928043 := bstep (se 1 (by rfl) ⟨696032, by rfl⟩ : syracuseStep 928043 = 1392065) B1392065
theorem B698683 : Blo 618297 698683 := bstep (se 1 (by rfl) ⟨524012, by rfl⟩ : syracuseStep 698683 = 1048025) B1048025
theorem B928073 : Blo 618297 928073 := bstep (se 2 (by rfl) ⟨348027, by rfl⟩ : syracuseStep 928073 = 696055) B696055
theorem B928187 : Blo 618297 928187 := bstep (se 1 (by rfl) ⟨696140, by rfl⟩ : syracuseStep 928187 = 1392281) B1392281
theorem B928247 : Blo 618297 928247 := bstep (se 1 (by rfl) ⟨696185, by rfl⟩ : syracuseStep 928247 = 1392371) B1392371
theorem B928271 : Blo 618297 928271 := bstep (se 1 (by rfl) ⟨696203, by rfl⟩ : syracuseStep 928271 = 1392407) B1392407
theorem B2239019 : Blo 618297 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B928313 : Blo 618297 928313 := bstep (se 2 (by rfl) ⟨348117, by rfl⟩ : syracuseStep 928313 = 696235) B696235
theorem B928391 : Blo 618297 928391 := bstep (se 1 (by rfl) ⟨696293, by rfl⟩ : syracuseStep 928391 = 1392587) B1392587
theorem B928427 : Blo 618297 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B928457 : Blo 618297 928457 := bstep (se 2 (by rfl) ⟨348171, by rfl⟩ : syracuseStep 928457 = 696343) B696343
theorem B699151 : Blo 618297 699151 := bstep (se 1 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 699151 = 1048727) B1048727
theorem B928571 : Blo 618297 928571 := bstep (se 1 (by rfl) ⟨696428, by rfl⟩ : syracuseStep 928571 = 1392857) B1392857
theorem B928631 : Blo 618297 928631 := bstep (se 1 (by rfl) ⟨696473, by rfl⟩ : syracuseStep 928631 = 1392947) B1392947
theorem B928655 : Blo 618297 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B3353491 : Blo 618297 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B928697 : Blo 618297 928697 := bstep (se 2 (by rfl) ⟨348261, by rfl⟩ : syracuseStep 928697 = 696523) B696523
theorem B3779513 : Blo 618297 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B928775 : Blo 618297 928775 := bstep (se 1 (by rfl) ⟨696581, by rfl⟩ : syracuseStep 928775 = 1393163) B1393163
theorem B1485857 : Blo 618297 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B928811 : Blo 618297 928811 := bstep (se 1 (by rfl) ⟨696608, by rfl⟩ : syracuseStep 928811 = 1393217) B1393217
theorem B16067645 : Blo 618297 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B2829379 : Blo 618297 2829379 := bstep (se 1 (by rfl) ⟨2122034, by rfl⟩ : syracuseStep 2829379 = 4244069) B4244069
theorem B928841 : Blo 618297 928841 := bstep (se 2 (by rfl) ⟨348315, by rfl⟩ : syracuseStep 928841 = 696631) B696631
theorem B928955 : Blo 618297 928955 := bstep (se 1 (by rfl) ⟨696716, by rfl⟩ : syracuseStep 928955 = 1393433) B1393433
theorem B929015 : Blo 618297 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B699655 : Blo 618297 699655 := bstep (se 1 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 699655 = 1049483) B1049483
theorem B929039 : Blo 618297 929039 := bstep (se 1 (by rfl) ⟨696779, by rfl⟩ : syracuseStep 929039 = 1393559) B1393559
theorem B5975329 : Blo 618297 5975329 := bstep (se 2 (by rfl) ⟨2240748, by rfl⟩ : syracuseStep 5975329 = 4481497) B4481497
theorem B929081 : Blo 618297 929081 := bstep (se 2 (by rfl) ⟨348405, by rfl⟩ : syracuseStep 929081 = 696811) B696811
theorem B929159 : Blo 618297 929159 := bstep (se 1 (by rfl) ⟨696869, by rfl⟩ : syracuseStep 929159 = 1393739) B1393739
theorem B929195 : Blo 618297 929195 := bstep (se 1 (by rfl) ⟨696896, by rfl⟩ : syracuseStep 929195 = 1393793) B1393793
theorem B699835 : Blo 618297 699835 := bstep (se 1 (by rfl) ⟨524876, by rfl⟩ : syracuseStep 699835 = 1049753) B1049753
theorem B929225 : Blo 618297 929225 := bstep (se 2 (by rfl) ⟨348459, by rfl⟩ : syracuseStep 929225 = 696919) B696919
theorem B12758477 : Blo 618297 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B929339 : Blo 618297 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B929399 : Blo 618297 929399 := bstep (se 1 (by rfl) ⟨697049, by rfl⟩ : syracuseStep 929399 = 1394099) B1394099
theorem B929423 : Blo 618297 929423 := bstep (se 1 (by rfl) ⟨697067, by rfl⟩ : syracuseStep 929423 = 1394135) B1394135
theorem B929465 : Blo 618297 929465 := bstep (se 2 (by rfl) ⟨348549, by rfl⟩ : syracuseStep 929465 = 697099) B697099
theorem B929543 : Blo 618297 929543 := bstep (se 1 (by rfl) ⟨697157, by rfl⟩ : syracuseStep 929543 = 1394315) B1394315
theorem B929579 : Blo 618297 929579 := bstep (se 1 (by rfl) ⟨697184, by rfl⟩ : syracuseStep 929579 = 1394369) B1394369
theorem B929609 : Blo 618297 929609 := bstep (se 2 (by rfl) ⟨348603, by rfl⟩ : syracuseStep 929609 = 697207) B697207
theorem B929723 : Blo 618297 929723 := bstep (se 1 (by rfl) ⟨697292, by rfl⟩ : syracuseStep 929723 = 1394585) B1394585
theorem B929783 : Blo 618297 929783 := bstep (se 1 (by rfl) ⟨697337, by rfl⟩ : syracuseStep 929783 = 1394675) B1394675
theorem B929807 : Blo 618297 929807 := bstep (se 1 (by rfl) ⟨697355, by rfl⟩ : syracuseStep 929807 = 1394711) B1394711
theorem B929849 : Blo 618297 929849 := bstep (se 2 (by rfl) ⟨348693, by rfl⟩ : syracuseStep 929849 = 697387) B697387
theorem B1323067 : Blo 618297 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B929927 : Blo 618297 929927 := bstep (se 1 (by rfl) ⟨697445, by rfl⟩ : syracuseStep 929927 = 1394891) B1394891
theorem B929963 : Blo 618297 929963 := bstep (se 1 (by rfl) ⟨697472, by rfl⟩ : syracuseStep 929963 = 1394945) B1394945
theorem B929993 : Blo 618297 929993 := bstep (se 2 (by rfl) ⟨348747, by rfl⟩ : syracuseStep 929993 = 697495) B697495
theorem B995627 : Blo 618297 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B930107 : Blo 618297 930107 := bstep (se 1 (by rfl) ⟨697580, by rfl⟩ : syracuseStep 930107 = 1395161) B1395161
theorem B930167 : Blo 618297 930167 := bstep (se 1 (by rfl) ⟨697625, by rfl⟩ : syracuseStep 930167 = 1395251) B1395251
theorem B930191 : Blo 618297 930191 := bstep (se 1 (by rfl) ⟨697643, by rfl⟩ : syracuseStep 930191 = 1395287) B1395287
theorem B930233 : Blo 618297 930233 := bstep (se 2 (by rfl) ⟨348837, by rfl⟩ : syracuseStep 930233 = 697675) B697675
theorem B930311 : Blo 618297 930311 := bstep (se 1 (by rfl) ⟨697733, by rfl⟩ : syracuseStep 930311 = 1395467) B1395467
theorem B1487375 : Blo 618297 1487375 := bstep (se 1 (by rfl) ⟨1115531, by rfl⟩ : syracuseStep 1487375 = 2231063) B2231063
theorem B930347 : Blo 618297 930347 := bstep (se 1 (by rfl) ⟨697760, by rfl⟩ : syracuseStep 930347 = 1395521) B1395521
theorem B930377 : Blo 618297 930377 := bstep (se 2 (by rfl) ⟨348891, by rfl⟩ : syracuseStep 930377 = 697783) B697783
theorem B930491 : Blo 618297 930491 := bstep (se 1 (by rfl) ⟨697868, by rfl⟩ : syracuseStep 930491 = 1395737) B1395737
theorem B930551 : Blo 618297 930551 := bstep (se 1 (by rfl) ⟨697913, by rfl⟩ : syracuseStep 930551 = 1395827) B1395827
theorem B7058177 : Blo 618297 7058177 := bstep (se 2 (by rfl) ⟨2646816, by rfl⟩ : syracuseStep 7058177 = 5293633) B5293633
theorem B930575 : Blo 618297 930575 := bstep (se 1 (by rfl) ⟨697931, by rfl⟩ : syracuseStep 930575 = 1395863) B1395863
theorem B1061675 : Blo 618297 1061675 := bstep (se 1 (by rfl) ⟨796256, by rfl⟩ : syracuseStep 1061675 = 1592513) B1592513
theorem B5649203 : Blo 618297 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B930617 : Blo 618297 930617 := bstep (se 2 (by rfl) ⟨348981, by rfl⟩ : syracuseStep 930617 = 697963) B697963
theorem B1880891 : Blo 618297 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B930695 : Blo 618297 930695 := bstep (se 1 (by rfl) ⟨698021, by rfl⟩ : syracuseStep 930695 = 1396043) B1396043
theorem B930731 : Blo 618297 930731 := bstep (se 1 (by rfl) ⟨698048, by rfl⟩ : syracuseStep 930731 = 1396097) B1396097
theorem B930761 : Blo 618297 930761 := bstep (se 2 (by rfl) ⟨349035, by rfl⟩ : syracuseStep 930761 = 698071) B698071
theorem B3814411 : Blo 618297 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B930875 : Blo 618297 930875 := bstep (se 1 (by rfl) ⟨698156, by rfl⟩ : syracuseStep 930875 = 1396313) B1396313
theorem B930935 : Blo 618297 930935 := bstep (se 1 (by rfl) ⟨698201, by rfl⟩ : syracuseStep 930935 = 1396403) B1396403
theorem B930959 : Blo 618297 930959 := bstep (se 1 (by rfl) ⟨698219, by rfl⟩ : syracuseStep 930959 = 1396439) B1396439
theorem B931001 : Blo 618297 931001 := bstep (se 2 (by rfl) ⟨349125, by rfl⟩ : syracuseStep 931001 = 698251) B698251
theorem B931079 : Blo 618297 931079 := bstep (se 1 (by rfl) ⟨698309, by rfl⟩ : syracuseStep 931079 = 1396619) B1396619
theorem B3355937 : Blo 618297 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B931115 : Blo 618297 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B931145 : Blo 618297 931145 := bstep (se 2 (by rfl) ⟨349179, by rfl⟩ : syracuseStep 931145 = 698359) B698359
theorem B6698371 : Blo 618297 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B931259 : Blo 618297 931259 := bstep (se 1 (by rfl) ⟨698444, by rfl⟩ : syracuseStep 931259 = 1396889) B1396889
theorem B931319 : Blo 618297 931319 := bstep (se 1 (by rfl) ⟨698489, by rfl⟩ : syracuseStep 931319 = 1396979) B1396979
theorem B931343 : Blo 618297 931343 := bstep (se 1 (by rfl) ⟨698507, by rfl⟩ : syracuseStep 931343 = 1397015) B1397015
theorem B8599069 : Blo 618297 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B931385 : Blo 618297 931385 := bstep (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) B698539
theorem B931463 : Blo 618297 931463 := bstep (se 1 (by rfl) ⟨698597, by rfl⟩ : syracuseStep 931463 = 1397195) B1397195
theorem B931499 : Blo 618297 931499 := bstep (se 1 (by rfl) ⟨698624, by rfl⟩ : syracuseStep 931499 = 1397249) B1397249
theorem B931529 : Blo 618297 931529 := bstep (se 2 (by rfl) ⟨349323, by rfl⟩ : syracuseStep 931529 = 698647) B698647
theorem B3356453 : Blo 618297 3356453 := bstep (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) B629335
theorem B931643 : Blo 618297 931643 := bstep (se 1 (by rfl) ⟨698732, by rfl⟩ : syracuseStep 931643 = 1397465) B1397465
theorem B931703 : Blo 618297 931703 := bstep (se 1 (by rfl) ⟨698777, by rfl⟩ : syracuseStep 931703 = 1397555) B1397555
theorem B931727 : Blo 618297 931727 := bstep (se 1 (by rfl) ⟨698795, by rfl⟩ : syracuseStep 931727 = 1397591) B1397591
theorem B931769 : Blo 618297 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B931847 : Blo 618297 931847 := bstep (se 1 (by rfl) ⟨698885, by rfl⟩ : syracuseStep 931847 = 1397771) B1397771
theorem B931883 : Blo 618297 931883 := bstep (se 1 (by rfl) ⟨698912, by rfl⟩ : syracuseStep 931883 = 1397825) B1397825
theorem B931913 : Blo 618297 931913 := bstep (se 2 (by rfl) ⟨349467, by rfl⟩ : syracuseStep 931913 = 698935) B698935
theorem B932027 : Blo 618297 932027 := bstep (se 1 (by rfl) ⟨699020, by rfl⟩ : syracuseStep 932027 = 1398041) B1398041
theorem B932087 : Blo 618297 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B932111 : Blo 618297 932111 := bstep (se 1 (by rfl) ⟨699083, by rfl⟩ : syracuseStep 932111 = 1398167) B1398167
theorem B932153 : Blo 618297 932153 := bstep (se 2 (by rfl) ⟨349557, by rfl⟩ : syracuseStep 932153 = 699115) B699115
theorem B932231 : Blo 618297 932231 := bstep (se 1 (by rfl) ⟨699173, by rfl⟩ : syracuseStep 932231 = 1398347) B1398347
theorem B1325459 : Blo 618297 1325459 := bstep (se 1 (by rfl) ⟨994094, by rfl⟩ : syracuseStep 1325459 = 1988189) B1988189
theorem B3193235 : Blo 618297 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B932267 : Blo 618297 932267 := bstep (se 1 (by rfl) ⟨699200, by rfl⟩ : syracuseStep 932267 = 1398401) B1398401
theorem B932297 : Blo 618297 932297 := bstep (se 2 (by rfl) ⟨349611, by rfl⟩ : syracuseStep 932297 = 699223) B699223
theorem B5945885 : Blo 618297 5945885 := bstep (se 3 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 5945885 = 2229707) B2229707
theorem B932411 : Blo 618297 932411 := bstep (se 1 (by rfl) ⟨699308, by rfl⟩ : syracuseStep 932411 = 1398617) B1398617
theorem B932471 : Blo 618297 932471 := bstep (se 1 (by rfl) ⟨699353, by rfl⟩ : syracuseStep 932471 = 1398707) B1398707
theorem B932495 : Blo 618297 932495 := bstep (se 1 (by rfl) ⟨699371, by rfl⟩ : syracuseStep 932495 = 1398743) B1398743
theorem B932537 : Blo 618297 932537 := bstep (se 2 (by rfl) ⟨349701, by rfl⟩ : syracuseStep 932537 = 699403) B699403
theorem B932615 : Blo 618297 932615 := bstep (se 1 (by rfl) ⟨699461, by rfl⟩ : syracuseStep 932615 = 1398923) B1398923
theorem B1981217 : Blo 618297 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B932651 : Blo 618297 932651 := bstep (se 1 (by rfl) ⟨699488, by rfl⟩ : syracuseStep 932651 = 1398977) B1398977
theorem B932681 : Blo 618297 932681 := bstep (se 2 (by rfl) ⟨349755, by rfl⟩ : syracuseStep 932681 = 699511) B699511
theorem B1391507 : Blo 618297 1391507 := bstep (se 1 (by rfl) ⟨1043630, by rfl⟩ : syracuseStep 1391507 = 2087261) B2087261
theorem B932795 : Blo 618297 932795 := bstep (se 1 (by rfl) ⟨699596, by rfl⟩ : syracuseStep 932795 = 1399193) B1399193
theorem B1391561 : Blo 618297 1391561 := bstep (se 2 (by rfl) ⟨521835, by rfl⟩ : syracuseStep 1391561 = 1043671) B1043671
theorem B932855 : Blo 618297 932855 := bstep (se 1 (by rfl) ⟨699641, by rfl⟩ : syracuseStep 932855 = 1399283) B1399283
theorem B932879 : Blo 618297 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B932921 : Blo 618297 932921 := bstep (se 2 (by rfl) ⟨349845, by rfl⟩ : syracuseStep 932921 = 699691) B699691
theorem B932999 : Blo 618297 932999 := bstep (se 1 (by rfl) ⟨699749, by rfl⟩ : syracuseStep 932999 = 1399499) B1399499
theorem B933035 : Blo 618297 933035 := bstep (se 1 (by rfl) ⟨699776, by rfl⟩ : syracuseStep 933035 = 1399553) B1399553
theorem B933065 : Blo 618297 933065 := bstep (se 2 (by rfl) ⟨349899, by rfl⟩ : syracuseStep 933065 = 699799) B699799
theorem B1490219 : Blo 618297 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B933179 : Blo 618297 933179 := bstep (se 1 (by rfl) ⟨699884, by rfl⟩ : syracuseStep 933179 = 1399769) B1399769
theorem B933239 : Blo 618297 933239 := bstep (se 1 (by rfl) ⟨699929, by rfl⟩ : syracuseStep 933239 = 1399859) B1399859
theorem B933263 : Blo 618297 933263 := bstep (se 1 (by rfl) ⟨699947, by rfl⟩ : syracuseStep 933263 = 1399895) B1399895
theorem B933305 : Blo 618297 933305 := bstep (se 2 (by rfl) ⟨349989, by rfl⟩ : syracuseStep 933305 = 699979) B699979
theorem B933383 : Blo 618297 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B933419 : Blo 618297 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B7061093 : Blo 618297 7061093 := bstep (se 4 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 7061093 = 1323955) B1323955
theorem B1392263 : Blo 618297 1392263 := bstep (se 1 (by rfl) ⟨1044197, by rfl⟩ : syracuseStep 1392263 = 2088395) B2088395
theorem B1392443 : Blo 618297 1392443 := bstep (se 1 (by rfl) ⟨1044332, by rfl⟩ : syracuseStep 1392443 = 2088665) B2088665
theorem B1392569 : Blo 618297 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B1916873 : Blo 618297 1916873 := bstep (se 2 (by rfl) ⟨718827, by rfl⟩ : syracuseStep 1916873 = 1437655) B1437655
theorem B1917047 : Blo 618297 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1392911 : Blo 618297 1392911 := bstep (se 1 (by rfl) ⟨1044683, by rfl⟩ : syracuseStep 1392911 = 2089367) B2089367
theorem B1392929 : Blo 618297 1392929 := bstep (se 2 (by rfl) ⟨522348, by rfl⟩ : syracuseStep 1392929 = 1044697) B1044697
theorem B3359027 : Blo 618297 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B6701447 : Blo 618297 6701447 := bstep (se 1 (by rfl) ⟨5026085, by rfl⟩ : syracuseStep 6701447 = 10052171) B10052171
theorem B836011 : Blo 618297 836011 := bstep (se 1 (by rfl) ⟨627008, by rfl⟩ : syracuseStep 836011 = 1254017) B1254017
theorem B1982987 : Blo 618297 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B5980715 : Blo 618297 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B1393271 : Blo 618297 1393271 := bstep (se 1 (by rfl) ⟨1044953, by rfl⟩ : syracuseStep 1393271 = 2089907) B2089907
theorem B967339 : Blo 618297 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B3982117 : Blo 618297 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B1393451 : Blo 618297 1393451 := bstep (se 1 (by rfl) ⟨1045088, by rfl⟩ : syracuseStep 1393451 = 2090177) B2090177
theorem B3130163 : Blo 618297 3130163 := bstep (se 1 (by rfl) ⟨2347622, by rfl⟩ : syracuseStep 3130163 = 4695245) B4695245
theorem B1491979 : Blo 618297 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B7062551 : Blo 618297 7062551 := bstep (se 1 (by rfl) ⟨5296913, by rfl⟩ : syracuseStep 7062551 = 10593827) B10593827
theorem B1983575 : Blo 618297 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B3130487 : Blo 618297 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B1393811 : Blo 618297 1393811 := bstep (se 1 (by rfl) ⟨1045358, by rfl⟩ : syracuseStep 1393811 = 2090717) B2090717
theorem B1885331 : Blo 618297 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1393865 : Blo 618297 1393865 := bstep (se 2 (by rfl) ⟨522699, by rfl⟩ : syracuseStep 1393865 = 1045399) B1045399
theorem B1328329 : Blo 618297 1328329 := bstep (se 2 (by rfl) ⟨498123, by rfl⟩ : syracuseStep 1328329 = 996247) B996247
theorem B837049 : Blo 618297 837049 := bstep (se 2 (by rfl) ⟨313893, by rfl⟩ : syracuseStep 837049 = 627787) B627787
theorem B2901547 : Blo 618297 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B1328825 : Blo 618297 1328825 := bstep (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) B996619
theorem B1394567 : Blo 618297 1394567 := bstep (se 1 (by rfl) ⟨1045925, by rfl⟩ : syracuseStep 1394567 = 2091851) B2091851
theorem B1394747 : Blo 618297 1394747 := bstep (se 1 (by rfl) ⟨1046060, by rfl⟩ : syracuseStep 1394747 = 2092121) B2092121
theorem B3131459 : Blo 618297 3131459 := bstep (se 1 (by rfl) ⟨2348594, by rfl⟩ : syracuseStep 3131459 = 4697189) B4697189
theorem B1394873 : Blo 618297 1394873 := bstep (se 2 (by rfl) ⟨523077, by rfl⟩ : syracuseStep 1394873 = 1046155) B1046155
theorem B3524897 : Blo 618297 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B3131783 : Blo 618297 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B3361169 : Blo 618297 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1395215 : Blo 618297 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B1395233 : Blo 618297 1395233 := bstep (se 2 (by rfl) ⟨523212, by rfl⟩ : syracuseStep 1395233 = 1046425) B1046425
theorem B3361625 : Blo 618297 3361625 := bstep (se 2 (by rfl) ⟨1260609, by rfl⟩ : syracuseStep 3361625 = 2521219) B2521219
theorem B1395575 : Blo 618297 1395575 := bstep (se 1 (by rfl) ⟨1046681, by rfl⟩ : syracuseStep 1395575 = 2093363) B2093363
theorem B1592183 : Blo 618297 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B1395755 : Blo 618297 1395755 := bstep (se 1 (by rfl) ⟨1046816, by rfl⟩ : syracuseStep 1395755 = 2093633) B2093633
theorem B1494131 : Blo 618297 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B1592473 : Blo 618297 1592473 := bstep (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) B1194355
theorem B1494217 : Blo 618297 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B2116999 : Blo 618297 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B1396115 : Blo 618297 1396115 := bstep (se 1 (by rfl) ⟨1047086, by rfl⟩ : syracuseStep 1396115 = 2094173) B2094173
theorem B1396169 : Blo 618297 1396169 := bstep (se 2 (by rfl) ⟨523563, by rfl⟩ : syracuseStep 1396169 = 1047127) B1047127
theorem B1888201 : Blo 618297 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1396871 : Blo 618297 1396871 := bstep (se 1 (by rfl) ⟨1047653, by rfl⟩ : syracuseStep 1396871 = 2095307) B2095307
theorem B1397051 : Blo 618297 1397051 := bstep (se 1 (by rfl) ⟨1047788, by rfl⟩ : syracuseStep 1397051 = 2095577) B2095577
theorem B2642291 : Blo 618297 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B3232145 : Blo 618297 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B1397177 : Blo 618297 1397177 := bstep (se 2 (by rfl) ⟨523941, by rfl⟩ : syracuseStep 1397177 = 1047883) B1047883
theorem B2511371 : Blo 618297 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1397519 : Blo 618297 1397519 := bstep (se 1 (by rfl) ⟨1048139, by rfl⟩ : syracuseStep 1397519 = 2096279) B2096279
theorem B1397537 : Blo 618297 1397537 := bstep (se 2 (by rfl) ⟨524076, by rfl⟩ : syracuseStep 1397537 = 1048153) B1048153
theorem B906103 : Blo 618297 906103 := bstep (se 1 (by rfl) ⟨679577, by rfl⟩ : syracuseStep 906103 = 1359155) B1359155
theorem B1987703 : Blo 618297 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B1397879 : Blo 618297 1397879 := bstep (se 1 (by rfl) ⟨1048409, by rfl⟩ : syracuseStep 1397879 = 2096819) B2096819
theorem B6706421 : Blo 618297 6706421 := bstep (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) B628727
theorem B1398059 : Blo 618297 1398059 := bstep (se 1 (by rfl) ⟨1048544, by rfl⟩ : syracuseStep 1398059 = 2097089) B2097089
theorem B3527995 : Blo 618297 3527995 := bstep (se 1 (by rfl) ⟨2645996, by rfl⟩ : syracuseStep 3527995 = 5291993) B5291993
theorem B3986833 : Blo 618297 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B2348473 : Blo 618297 2348473 := bstep (se 2 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 2348473 = 1761355) B1761355
theorem B2512313 : Blo 618297 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B1398419 : Blo 618297 1398419 := bstep (se 1 (by rfl) ⟨1048814, by rfl⟩ : syracuseStep 1398419 = 2097629) B2097629
theorem B1398473 : Blo 618297 1398473 := bstep (se 2 (by rfl) ⟨524427, by rfl⟩ : syracuseStep 1398473 = 1048855) B1048855
theorem B48420557 : Blo 618297 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B8509157 : Blo 618297 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B3135347 : Blo 618297 3135347 := bstep (se 1 (by rfl) ⟨2351510, by rfl⟩ : syracuseStep 3135347 = 4703021) B4703021
theorem B743303 : Blo 618297 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B21485591 : Blo 618297 21485591 := bstep (se 1 (by rfl) ⟨16114193, by rfl⟩ : syracuseStep 21485591 = 32228387) B32228387
theorem B1988651 : Blo 618297 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B3135833 : Blo 618297 3135833 := bstep (se 2 (by rfl) ⟨1175937, by rfl⟩ : syracuseStep 3135833 = 2351875) B2351875
theorem B1399175 : Blo 618297 1399175 := bstep (se 1 (by rfl) ⟨1049381, by rfl⟩ : syracuseStep 1399175 = 2098763) B2098763
theorem B2087315 : Blo 618297 2087315 := bstep (se 1 (by rfl) ⟨1565486, by rfl⟩ : syracuseStep 2087315 = 3130973) B3130973
theorem B743851 : Blo 618297 743851 := bstep (se 1 (by rfl) ⟨557888, by rfl⟩ : syracuseStep 743851 = 1115777) B1115777
theorem B2120203 : Blo 618297 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B2382365 : Blo 618297 2382365 := bstep (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) B893387
theorem B743995 : Blo 618297 743995 := bstep (se 1 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 743995 = 1115993) B1115993
theorem B1399355 : Blo 618297 1399355 := bstep (se 1 (by rfl) ⟨1049516, by rfl⟩ : syracuseStep 1399355 = 2099033) B2099033
theorem B1399481 : Blo 618297 1399481 := bstep (se 2 (by rfl) ⟨524805, by rfl⟩ : syracuseStep 1399481 = 1049611) B1049611
theorem B3529453 : Blo 618297 3529453 := bstep (se 3 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 3529453 = 1323545) B1323545
theorem B2644751 : Blo 618297 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B20142863 : Blo 618297 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B1399823 : Blo 618297 1399823 := bstep (se 1 (by rfl) ⟨1049867, by rfl⟩ : syracuseStep 1399823 = 2099735) B2099735
theorem B1399841 : Blo 618297 1399841 := bstep (se 2 (by rfl) ⟨524940, by rfl⟩ : syracuseStep 1399841 = 1049881) B1049881
theorem B2383289 : Blo 618297 2383289 := bstep (se 2 (by rfl) ⟨893733, by rfl⟩ : syracuseStep 2383289 = 1787467) B1787467
theorem B2088719 : Blo 618297 2088719 := bstep (se 1 (by rfl) ⟨1566539, by rfl⟩ : syracuseStep 2088719 = 3133079) B3133079
theorem B1990433 : Blo 618297 1990433 := bstep (se 2 (by rfl) ⟨746412, by rfl⟩ : syracuseStep 1990433 = 1492825) B1492825
theorem B1990547 : Blo 618297 1990547 := bstep (se 1 (by rfl) ⟨1492910, by rfl⟩ : syracuseStep 1990547 = 2985821) B2985821
theorem B2088989 : Blo 618297 2088989 := bstep (se 3 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 2088989 = 783371) B783371
theorem B2351375 : Blo 618297 2351375 := bstep (se 1 (by rfl) ⟨1763531, by rfl⟩ : syracuseStep 2351375 = 3527063) B3527063
theorem B2646407 : Blo 618297 2646407 := bstep (se 1 (by rfl) ⟨1984805, by rfl⟩ : syracuseStep 2646407 = 3969611) B3969611
theorem B3137939 : Blo 618297 3137939 := bstep (se 1 (by rfl) ⟨2353454, by rfl⟩ : syracuseStep 3137939 = 4706909) B4706909
theorem B10215827 : Blo 618297 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B7955009 : Blo 618297 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B1696391 : Blo 618297 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B3531437 : Blo 618297 3531437 := bstep (se 3 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 3531437 = 1324289) B1324289
theorem B4481729 : Blo 618297 4481729 := bstep (se 2 (by rfl) ⟨1680648, by rfl⟩ : syracuseStep 4481729 = 3361297) B3361297
theorem B1565527 : Blo 618297 1565527 := bstep (se 1 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 1565527 = 2348291) B2348291
theorem B4711283 : Blo 618297 4711283 := bstep (se 1 (by rfl) ⟨3533462, by rfl⟩ : syracuseStep 4711283 = 7066925) B7066925
theorem B11920517 : Blo 618297 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B1565831 : Blo 618297 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B1565963 : Blo 618297 1565963 := bstep (se 1 (by rfl) ⟨1174472, by rfl⟩ : syracuseStep 1565963 = 2348945) B2348945
theorem B2123023 : Blo 618297 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B2090393 : Blo 618297 2090393 := bstep (se 2 (by rfl) ⟨783897, by rfl⟩ : syracuseStep 2090393 = 1567795) B1567795
theorem B1762859 : Blo 618297 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B7071299 : Blo 618297 7071299 := bstep (se 1 (by rfl) ⟨5303474, by rfl⟩ : syracuseStep 7071299 = 10606949) B10606949
theorem B1566479 : Blo 618297 1566479 := bstep (se 1 (by rfl) ⟨1174859, by rfl⟩ : syracuseStep 1566479 = 2349719) B2349719
theorem B5662553 : Blo 618297 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B1566611 : Blo 618297 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B747527 : Blo 618297 747527 := bstep (se 1 (by rfl) ⟨560645, by rfl⟩ : syracuseStep 747527 = 1121291) B1121291
theorem B2091095 : Blo 618297 2091095 := bstep (se 1 (by rfl) ⟨1568321, by rfl⟩ : syracuseStep 2091095 = 3136643) B3136643
theorem B2648321 : Blo 618297 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B6449629 : Blo 618297 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B2091581 : Blo 618297 2091581 := bstep (se 3 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 2091581 = 784343) B784343
theorem B2648663 : Blo 618297 2648663 := bstep (se 1 (by rfl) ⟨1986497, by rfl⟩ : syracuseStep 2648663 = 3972995) B3972995
theorem B6876019 : Blo 618297 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B1043401 : Blo 618297 1043401 := bstep (se 2 (by rfl) ⟨391275, by rfl⟩ : syracuseStep 1043401 = 782551) B782551
theorem B1567745 : Blo 618297 1567745 := bstep (se 2 (by rfl) ⟨587904, by rfl⟩ : syracuseStep 1567745 = 1175809) B1175809
theorem B3533827 : Blo 618297 3533827 := bstep (se 1 (by rfl) ⟨2650370, by rfl⟩ : syracuseStep 3533827 = 5300741) B5300741
theorem B1174571 : Blo 618297 1174571 := bstep (se 1 (by rfl) ⟨880928, by rfl⟩ : syracuseStep 1174571 = 1761857) B1761857
theorem B1764499 : Blo 618297 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B1174799 : Blo 618297 1174799 := bstep (se 1 (by rfl) ⟨881099, by rfl⟩ : syracuseStep 1174799 = 1762199) B1762199
theorem B1568119 : Blo 618297 1568119 := bstep (se 1 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 1568119 = 2352179) B2352179
theorem B2354579 : Blo 618297 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B3141017 : Blo 618297 3141017 := bstep (se 2 (by rfl) ⟨1177881, by rfl⟩ : syracuseStep 3141017 = 2355763) B2355763
theorem B2125241 : Blo 618297 2125241 := bstep (se 2 (by rfl) ⟨796965, by rfl⟩ : syracuseStep 2125241 = 1593931) B1593931
theorem B19590605 : Blo 618297 19590605 := bstep (se 3 (by rfl) ⟨3673238, by rfl⟩ : syracuseStep 19590605 = 7346477) B7346477
theorem B1044103 : Blo 618297 1044103 := bstep (se 1 (by rfl) ⟨783077, by rfl⟩ : syracuseStep 1044103 = 1566155) B1566155
theorem B945851 : Blo 618297 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B880399 : Blo 618297 880399 := bstep (se 1 (by rfl) ⟨660299, by rfl⟩ : syracuseStep 880399 = 1320599) B1320599
theorem B880427 : Blo 618297 880427 := bstep (se 1 (by rfl) ⟨660320, by rfl⟩ : syracuseStep 880427 = 1320641) B1320641
theorem B1568555 : Blo 618297 1568555 := bstep (se 1 (by rfl) ⟨1176416, by rfl⟩ : syracuseStep 1568555 = 2352833) B2352833
theorem B618299 : Blo 618297 618299 := bstep (se 1 (by rfl) ⟨463724, by rfl⟩ : syracuseStep 618299 = 927449) B927449
theorem B618375 : Blo 618297 618375 := bstep (se 1 (by rfl) ⟨463781, by rfl⟩ : syracuseStep 618375 = 927563) B927563
theorem B618383 : Blo 618297 618383 := bstep (se 1 (by rfl) ⟨463787, by rfl⟩ : syracuseStep 618383 = 927575) B927575
theorem B2092985 : Blo 618297 2092985 := bstep (se 2 (by rfl) ⟨784869, by rfl⟩ : syracuseStep 2092985 = 1569739) B1569739
theorem B618427 : Blo 618297 618427 := bstep (se 1 (by rfl) ⟨463820, by rfl⟩ : syracuseStep 618427 = 927641) B927641
theorem B618503 : Blo 618297 618503 := bstep (se 1 (by rfl) ⟨463877, by rfl⟩ : syracuseStep 618503 = 927755) B927755
theorem B618511 : Blo 618297 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B618555 : Blo 618297 618555 := bstep (se 1 (by rfl) ⟨463916, by rfl⟩ : syracuseStep 618555 = 927833) B927833
theorem B618631 : Blo 618297 618631 := bstep (se 1 (by rfl) ⟨463973, by rfl⟩ : syracuseStep 618631 = 927947) B927947
theorem B618639 : Blo 618297 618639 := bstep (se 1 (by rfl) ⟨463979, by rfl⟩ : syracuseStep 618639 = 927959) B927959
theorem B618683 : Blo 618297 618683 := bstep (se 1 (by rfl) ⟨464012, by rfl⟩ : syracuseStep 618683 = 928025) B928025
theorem B618759 : Blo 618297 618759 := bstep (se 1 (by rfl) ⟨464069, by rfl⟩ : syracuseStep 618759 = 928139) B928139
theorem B618767 : Blo 618297 618767 := bstep (se 1 (by rfl) ⟨464075, by rfl⟩ : syracuseStep 618767 = 928151) B928151
theorem B1044751 : Blo 618297 1044751 := bstep (se 1 (by rfl) ⟨783563, by rfl⟩ : syracuseStep 1044751 = 1567127) B1567127
theorem B618811 : Blo 618297 618811 := bstep (se 1 (by rfl) ⟨464108, by rfl⟩ : syracuseStep 618811 = 928217) B928217
theorem B618887 : Blo 618297 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B618895 : Blo 618297 618895 := bstep (se 1 (by rfl) ⟨464171, by rfl⟩ : syracuseStep 618895 = 928343) B928343
theorem B782779 : Blo 618297 782779 := bstep (se 1 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 782779 = 1174169) B1174169
theorem B618939 : Blo 618297 618939 := bstep (se 1 (by rfl) ⟨464204, by rfl⟩ : syracuseStep 618939 = 928409) B928409
theorem B619015 : Blo 618297 619015 := bstep (se 1 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 619015 = 928523) B928523
theorem B2093579 : Blo 618297 2093579 := bstep (se 1 (by rfl) ⟨1570184, by rfl⟩ : syracuseStep 2093579 = 3140369) B3140369
theorem B619023 : Blo 618297 619023 := bstep (se 1 (by rfl) ⟨464267, by rfl⟩ : syracuseStep 619023 = 928535) B928535
theorem B619067 : Blo 618297 619067 := bstep (se 1 (by rfl) ⟨464300, by rfl⟩ : syracuseStep 619067 = 928601) B928601
theorem B1569395 : Blo 618297 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B2093687 : Blo 618297 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B619143 : Blo 618297 619143 := bstep (se 1 (by rfl) ⟨464357, by rfl⟩ : syracuseStep 619143 = 928715) B928715
theorem B1569415 : Blo 618297 1569415 := bstep (se 1 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 1569415 = 2354123) B2354123
theorem B1077895 : Blo 618297 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B619151 : Blo 618297 619151 := bstep (se 1 (by rfl) ⟨464363, by rfl⟩ : syracuseStep 619151 = 928727) B928727
theorem B1176211 : Blo 618297 1176211 := bstep (se 1 (by rfl) ⟨882158, by rfl⟩ : syracuseStep 1176211 = 1764317) B1764317
theorem B619195 : Blo 618297 619195 := bstep (se 1 (by rfl) ⟨464396, by rfl⟩ : syracuseStep 619195 = 928793) B928793
theorem B6451969 : Blo 618297 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B619271 : Blo 618297 619271 := bstep (se 1 (by rfl) ⟨464453, by rfl⟩ : syracuseStep 619271 = 928907) B928907
theorem B619279 : Blo 618297 619279 := bstep (se 1 (by rfl) ⟨464459, by rfl⟩ : syracuseStep 619279 = 928919) B928919
theorem B1045291 : Blo 618297 1045291 := bstep (se 1 (by rfl) ⟨783968, by rfl⟩ : syracuseStep 1045291 = 1567937) B1567937
theorem B619323 : Blo 618297 619323 := bstep (se 1 (by rfl) ⟨464492, by rfl⟩ : syracuseStep 619323 = 928985) B928985
theorem B1766231 : Blo 618297 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B1176439 : Blo 618297 1176439 := bstep (se 1 (by rfl) ⟨882329, by rfl⟩ : syracuseStep 1176439 = 1764659) B1764659
theorem B619399 : Blo 618297 619399 := bstep (se 1 (by rfl) ⟨464549, by rfl⟩ : syracuseStep 619399 = 929099) B929099
theorem B619407 : Blo 618297 619407 := bstep (se 1 (by rfl) ⟨464555, by rfl⟩ : syracuseStep 619407 = 929111) B929111
theorem B1569689 : Blo 618297 1569689 := bstep (se 2 (by rfl) ⟨588633, by rfl⟩ : syracuseStep 1569689 = 1177267) B1177267
theorem B1045433 : Blo 618297 1045433 := bstep (se 2 (by rfl) ⟨392037, by rfl⟩ : syracuseStep 1045433 = 784075) B784075
theorem B619451 : Blo 618297 619451 := bstep (se 1 (by rfl) ⟨464588, by rfl⟩ : syracuseStep 619451 = 929177) B929177
theorem B2651089 : Blo 618297 2651089 := bstep (se 2 (by rfl) ⟨994158, by rfl⟩ : syracuseStep 2651089 = 1988317) B1988317
theorem B619527 : Blo 618297 619527 := bstep (se 1 (by rfl) ⟨464645, by rfl⟩ : syracuseStep 619527 = 929291) B929291
theorem B2356235 : Blo 618297 2356235 := bstep (se 1 (by rfl) ⟨1767176, by rfl⟩ : syracuseStep 2356235 = 3534353) B3534353
theorem B619535 : Blo 618297 619535 := bstep (se 1 (by rfl) ⟨464651, by rfl⟩ : syracuseStep 619535 = 929303) B929303
theorem B619579 : Blo 618297 619579 := bstep (se 1 (by rfl) ⟨464684, by rfl⟩ : syracuseStep 619579 = 929369) B929369
theorem B1569851 : Blo 618297 1569851 := bstep (se 1 (by rfl) ⟨1177388, by rfl⟩ : syracuseStep 1569851 = 2354777) B2354777
theorem B619655 : Blo 618297 619655 := bstep (se 1 (by rfl) ⟨464741, by rfl⟩ : syracuseStep 619655 = 929483) B929483
theorem B619663 : Blo 618297 619663 := bstep (se 1 (by rfl) ⟨464747, by rfl⟩ : syracuseStep 619663 = 929495) B929495
theorem B619707 : Blo 618297 619707 := bstep (se 1 (by rfl) ⟨464780, by rfl⟩ : syracuseStep 619707 = 929561) B929561
theorem B2094281 : Blo 618297 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B619783 : Blo 618297 619783 := bstep (se 1 (by rfl) ⟨464837, by rfl⟩ : syracuseStep 619783 = 929675) B929675
theorem B619791 : Blo 618297 619791 := bstep (se 1 (by rfl) ⟨464843, by rfl⟩ : syracuseStep 619791 = 929687) B929687
theorem B1570063 : Blo 618297 1570063 := bstep (se 1 (by rfl) ⟨1177547, by rfl⟩ : syracuseStep 1570063 = 2355095) B2355095
theorem B619835 : Blo 618297 619835 := bstep (se 1 (by rfl) ⟨464876, by rfl⟩ : syracuseStep 619835 = 929753) B929753
theorem B6059357 : Blo 618297 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B3536243 : Blo 618297 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B783751 : Blo 618297 783751 := bstep (se 1 (by rfl) ⟨587813, by rfl⟩ : syracuseStep 783751 = 1175627) B1175627
theorem B619911 : Blo 618297 619911 := bstep (se 1 (by rfl) ⟨464933, by rfl⟩ : syracuseStep 619911 = 929867) B929867
theorem B619919 : Blo 618297 619919 := bstep (se 1 (by rfl) ⟨464939, by rfl⟩ : syracuseStep 619919 = 929879) B929879
theorem B6714809 : Blo 618297 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B619963 : Blo 618297 619963 := bstep (se 1 (by rfl) ⟨464972, by rfl⟩ : syracuseStep 619963 = 929945) B929945
theorem B620039 : Blo 618297 620039 := bstep (se 1 (by rfl) ⟨465029, by rfl⟩ : syracuseStep 620039 = 930059) B930059
theorem B620047 : Blo 618297 620047 := bstep (se 1 (by rfl) ⟨465035, by rfl⟩ : syracuseStep 620047 = 930071) B930071
theorem B1570337 : Blo 618297 1570337 := bstep (se 2 (by rfl) ⟨588876, by rfl⟩ : syracuseStep 1570337 = 1177753) B1177753
theorem B620091 : Blo 618297 620091 := bstep (se 1 (by rfl) ⟨465068, by rfl⟩ : syracuseStep 620091 = 930137) B930137
theorem B1046135 : Blo 618297 1046135 := bstep (se 1 (by rfl) ⟨784601, by rfl⟩ : syracuseStep 1046135 = 1569203) B1569203
theorem B620167 : Blo 618297 620167 := bstep (se 1 (by rfl) ⟨465125, by rfl⟩ : syracuseStep 620167 = 930251) B930251
theorem B620175 : Blo 618297 620175 := bstep (se 1 (by rfl) ⟨465131, by rfl⟩ : syracuseStep 620175 = 930263) B930263
theorem B620219 : Blo 618297 620219 := bstep (se 1 (by rfl) ⟨465164, by rfl⟩ : syracuseStep 620219 = 930329) B930329
theorem B620295 : Blo 618297 620295 := bstep (se 1 (by rfl) ⟨465221, by rfl⟩ : syracuseStep 620295 = 930443) B930443
theorem B620303 : Blo 618297 620303 := bstep (se 1 (by rfl) ⟨465227, by rfl⟩ : syracuseStep 620303 = 930455) B930455
theorem B784171 : Blo 618297 784171 := bstep (se 1 (by rfl) ⟨588128, by rfl⟩ : syracuseStep 784171 = 1176257) B1176257
theorem B620347 : Blo 618297 620347 := bstep (se 1 (by rfl) ⟨465260, by rfl⟩ : syracuseStep 620347 = 930521) B930521
theorem B7075673 : Blo 618297 7075673 := bstep (se 2 (by rfl) ⟨2653377, by rfl⟩ : syracuseStep 7075673 = 5306755) B5306755
theorem B620423 : Blo 618297 620423 := bstep (se 1 (by rfl) ⟨465317, by rfl⟩ : syracuseStep 620423 = 930635) B930635
theorem B2094983 : Blo 618297 2094983 := bstep (se 1 (by rfl) ⟨1571237, by rfl⟩ : syracuseStep 2094983 = 3142475) B3142475
theorem B620431 : Blo 618297 620431 := bstep (se 1 (by rfl) ⟨465323, by rfl⟩ : syracuseStep 620431 = 930647) B930647
theorem B3143609 : Blo 618297 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B620475 : Blo 618297 620475 := bstep (se 1 (by rfl) ⟨465356, by rfl⟩ : syracuseStep 620475 = 930713) B930713
theorem B620551 : Blo 618297 620551 := bstep (se 1 (by rfl) ⟨465413, by rfl⟩ : syracuseStep 620551 = 930827) B930827
theorem B784399 : Blo 618297 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B620559 : Blo 618297 620559 := bstep (se 1 (by rfl) ⟨465419, by rfl⟩ : syracuseStep 620559 = 930839) B930839
theorem B1144891 : Blo 618297 1144891 := bstep (se 1 (by rfl) ⟨858668, by rfl⟩ : syracuseStep 1144891 = 1717337) B1717337
theorem B1046587 : Blo 618297 1046587 := bstep (se 1 (by rfl) ⟨784940, by rfl⟩ : syracuseStep 1046587 = 1569881) B1569881
theorem B620603 : Blo 618297 620603 := bstep (se 1 (by rfl) ⟨465452, by rfl⟩ : syracuseStep 620603 = 930905) B930905
theorem B620679 : Blo 618297 620679 := bstep (se 1 (by rfl) ⟨465509, by rfl⟩ : syracuseStep 620679 = 931019) B931019
theorem B620687 : Blo 618297 620687 := bstep (se 1 (by rfl) ⟨465515, by rfl⟩ : syracuseStep 620687 = 931031) B931031
theorem B620731 : Blo 618297 620731 := bstep (se 1 (by rfl) ⟨465548, by rfl⟩ : syracuseStep 620731 = 931097) B931097
theorem B1046729 : Blo 618297 1046729 := bstep (se 2 (by rfl) ⟨392523, by rfl⟩ : syracuseStep 1046729 = 785047) B785047
theorem B2095361 : Blo 618297 2095361 := bstep (se 2 (by rfl) ⟨785760, by rfl⟩ : syracuseStep 2095361 = 1571521) B1571521
theorem B620807 : Blo 618297 620807 := bstep (se 1 (by rfl) ⟨465605, by rfl⟩ : syracuseStep 620807 = 931211) B931211
theorem B620815 : Blo 618297 620815 := bstep (se 1 (by rfl) ⟨465611, by rfl⟩ : syracuseStep 620815 = 931223) B931223
theorem B620859 : Blo 618297 620859 := bstep (se 1 (by rfl) ⟨465644, by rfl⟩ : syracuseStep 620859 = 931289) B931289
theorem B1767815 : Blo 618297 1767815 := bstep (se 1 (by rfl) ⟨1325861, by rfl⟩ : syracuseStep 1767815 = 2651723) B2651723
theorem B620935 : Blo 618297 620935 := bstep (se 1 (by rfl) ⟨465701, by rfl⟩ : syracuseStep 620935 = 931403) B931403
theorem B620943 : Blo 618297 620943 := bstep (se 1 (by rfl) ⟨465707, by rfl⟩ : syracuseStep 620943 = 931415) B931415
theorem B1178003 : Blo 618297 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B620987 : Blo 618297 620987 := bstep (se 1 (by rfl) ⟨465740, by rfl⟩ : syracuseStep 620987 = 931481) B931481
theorem B1178057 : Blo 618297 1178057 := bstep (se 2 (by rfl) ⟨441771, by rfl⟩ : syracuseStep 1178057 = 883543) B883543
theorem B621063 : Blo 618297 621063 := bstep (se 1 (by rfl) ⟨465797, by rfl⟩ : syracuseStep 621063 = 931595) B931595
theorem B1571339 : Blo 618297 1571339 := bstep (se 1 (by rfl) ⟨1178504, by rfl⟩ : syracuseStep 1571339 = 2357009) B2357009
theorem B621071 : Blo 618297 621071 := bstep (se 1 (by rfl) ⟨465803, by rfl⟩ : syracuseStep 621071 = 931607) B931607
theorem B1178155 : Blo 618297 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B621115 : Blo 618297 621115 := bstep (se 1 (by rfl) ⟨465836, by rfl⟩ : syracuseStep 621115 = 931673) B931673
theorem B621191 : Blo 618297 621191 := bstep (se 1 (by rfl) ⟨465893, by rfl⟩ : syracuseStep 621191 = 931787) B931787
theorem B883343 : Blo 618297 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B621199 : Blo 618297 621199 := bstep (se 1 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 621199 = 931799) B931799
theorem B621243 : Blo 618297 621243 := bstep (se 1 (by rfl) ⟨465932, by rfl⟩ : syracuseStep 621243 = 931865) B931865
theorem B785143 : Blo 618297 785143 := bstep (se 1 (by rfl) ⟨588857, by rfl⟩ : syracuseStep 785143 = 1177715) B1177715
theorem B621319 : Blo 618297 621319 := bstep (se 1 (by rfl) ⟨465989, by rfl⟩ : syracuseStep 621319 = 931979) B931979
theorem B1178383 : Blo 618297 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B621327 : Blo 618297 621327 := bstep (se 1 (by rfl) ⟨465995, by rfl⟩ : syracuseStep 621327 = 931991) B931991
theorem B6716195 : Blo 618297 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B3537701 : Blo 618297 3537701 := bstep (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) B663319
theorem B621371 : Blo 618297 621371 := bstep (se 1 (by rfl) ⟨466028, by rfl⟩ : syracuseStep 621371 = 932057) B932057
theorem B1047431 : Blo 618297 1047431 := bstep (se 1 (by rfl) ⟨785573, by rfl⟩ : syracuseStep 1047431 = 1571147) B1571147
theorem B621447 : Blo 618297 621447 := bstep (se 1 (by rfl) ⟨466085, by rfl⟩ : syracuseStep 621447 = 932171) B932171
theorem B621455 : Blo 618297 621455 := bstep (se 1 (by rfl) ⟨466091, by rfl⟩ : syracuseStep 621455 = 932183) B932183
theorem B621499 : Blo 618297 621499 := bstep (se 1 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 621499 = 932249) B932249
theorem B621575 : Blo 618297 621575 := bstep (se 1 (by rfl) ⟨466181, by rfl⟩ : syracuseStep 621575 = 932363) B932363
theorem B1768463 : Blo 618297 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B621583 : Blo 618297 621583 := bstep (se 1 (by rfl) ⟨466187, by rfl⟩ : syracuseStep 621583 = 932375) B932375
theorem B2096171 : Blo 618297 2096171 := bstep (se 1 (by rfl) ⟨1572128, by rfl⟩ : syracuseStep 2096171 = 3144257) B3144257
theorem B785467 : Blo 618297 785467 := bstep (se 1 (by rfl) ⟨589100, by rfl⟩ : syracuseStep 785467 = 1178201) B1178201
theorem B621627 : Blo 618297 621627 := bstep (se 1 (by rfl) ⟨466220, by rfl⟩ : syracuseStep 621627 = 932441) B932441
theorem B621703 : Blo 618297 621703 := bstep (se 1 (by rfl) ⟨466277, by rfl⟩ : syracuseStep 621703 = 932555) B932555
theorem B621711 : Blo 618297 621711 := bstep (se 1 (by rfl) ⟨466283, by rfl⟩ : syracuseStep 621711 = 932567) B932567
theorem B1571987 : Blo 618297 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B621755 : Blo 618297 621755 := bstep (se 1 (by rfl) ⟨466316, by rfl⟩ : syracuseStep 621755 = 932633) B932633
theorem B3144905 : Blo 618297 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B621831 : Blo 618297 621831 := bstep (se 1 (by rfl) ⟨466373, by rfl⟩ : syracuseStep 621831 = 932747) B932747
theorem B621839 : Blo 618297 621839 := bstep (se 1 (by rfl) ⟨466379, by rfl⟩ : syracuseStep 621839 = 932759) B932759
theorem B2653499 : Blo 618297 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B621883 : Blo 618297 621883 := bstep (se 1 (by rfl) ⟨466412, by rfl⟩ : syracuseStep 621883 = 932825) B932825
theorem B621959 : Blo 618297 621959 := bstep (se 1 (by rfl) ⟨466469, by rfl⟩ : syracuseStep 621959 = 932939) B932939
theorem B621967 : Blo 618297 621967 := bstep (se 1 (by rfl) ⟨466475, by rfl⟩ : syracuseStep 621967 = 932951) B932951
theorem B1572281 : Blo 618297 1572281 := bstep (se 2 (by rfl) ⟨589605, by rfl⟩ : syracuseStep 1572281 = 1179211) B1179211
theorem B622011 : Blo 618297 622011 := bstep (se 1 (by rfl) ⟨466508, by rfl⟩ : syracuseStep 622011 = 933017) B933017
theorem B622087 : Blo 618297 622087 := bstep (se 1 (by rfl) ⟨466565, by rfl⟩ : syracuseStep 622087 = 933131) B933131
theorem B1048079 : Blo 618297 1048079 := bstep (se 1 (by rfl) ⟨786059, by rfl⟩ : syracuseStep 1048079 = 1572119) B1572119
theorem B622095 : Blo 618297 622095 := bstep (se 1 (by rfl) ⟨466571, by rfl⟩ : syracuseStep 622095 = 933143) B933143
theorem B785963 : Blo 618297 785963 := bstep (se 1 (by rfl) ⟨589472, by rfl⟩ : syracuseStep 785963 = 1178945) B1178945
theorem B3538475 : Blo 618297 3538475 := bstep (se 1 (by rfl) ⟨2653856, by rfl⟩ : syracuseStep 3538475 = 5307713) B5307713
theorem B622139 : Blo 618297 622139 := bstep (se 1 (by rfl) ⟨466604, by rfl⟩ : syracuseStep 622139 = 933209) B933209
theorem B11959883 : Blo 618297 11959883 := bstep (se 1 (by rfl) ⟨8969912, by rfl⟩ : syracuseStep 11959883 = 17939825) B17939825
theorem B622215 : Blo 618297 622215 := bstep (se 1 (by rfl) ⟨466661, by rfl⟩ : syracuseStep 622215 = 933323) B933323
theorem B622223 : Blo 618297 622223 := bstep (se 1 (by rfl) ⟨466667, by rfl⟩ : syracuseStep 622223 = 933335) B933335
theorem B622267 : Blo 618297 622267 := bstep (se 1 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 622267 = 933401) B933401
theorem B1048585 : Blo 618297 1048585 := bstep (se 2 (by rfl) ⟨393219, by rfl⟩ : syracuseStep 1048585 = 786439) B786439
theorem B1278031 : Blo 618297 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B2097305 : Blo 618297 2097305 := bstep (se 2 (by rfl) ⟨786489, by rfl⟩ : syracuseStep 2097305 = 1572979) B1572979
theorem B1048747 : Blo 618297 1048747 := bstep (se 1 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 1048747 = 1573121) B1573121
theorem B885097 : Blo 618297 885097 := bstep (se 2 (by rfl) ⟨331911, by rfl⟩ : syracuseStep 885097 = 663823) B663823
theorem B1049051 : Blo 618297 1049051 := bstep (se 1 (by rfl) ⟨786788, by rfl⟩ : syracuseStep 1049051 = 1573577) B1573577
theorem B1573415 : Blo 618297 1573415 := bstep (se 1 (by rfl) ⟨1180061, by rfl⟩ : syracuseStep 1573415 = 2360123) B2360123
theorem B2359955 : Blo 618297 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B1049287 : Blo 618297 1049287 := bstep (se 1 (by rfl) ⟨786965, by rfl⟩ : syracuseStep 1049287 = 1573931) B1573931
theorem B3343133 : Blo 618297 3343133 := bstep (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) B1253675
theorem B3146525 : Blo 618297 3146525 := bstep (se 3 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 3146525 = 1179947) B1179947
theorem B2360137 : Blo 618297 2360137 := bstep (se 2 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 2360137 = 1770103) B1770103
theorem B1049449 : Blo 618297 1049449 := bstep (se 2 (by rfl) ⟨393543, by rfl⟩ : syracuseStep 1049449 = 787087) B787087
theorem B1573739 : Blo 618297 1573739 := bstep (se 1 (by rfl) ⟨1180304, by rfl⟩ : syracuseStep 1573739 = 2360609) B2360609
theorem B1115063 : Blo 618297 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B5309489 : Blo 618297 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B1180919 : Blo 618297 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B2098493 : Blo 618297 2098493 := bstep (se 3 (by rfl) ⟨393467, by rfl⟩ : syracuseStep 2098493 = 786935) B786935
theorem B1181071 : Blo 618297 1181071 := bstep (se 1 (by rfl) ⟨885803, by rfl⟩ : syracuseStep 1181071 = 1771607) B1771607
theorem B1050043 : Blo 618297 1050043 := bstep (se 1 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 1050043 = 1575065) B1575065
theorem B1574387 : Blo 618297 1574387 := bstep (se 1 (by rfl) ⟨1180790, by rfl⟩ : syracuseStep 1574387 = 2361581) B2361581
theorem B1574599 : Blo 618297 1574599 := bstep (se 1 (by rfl) ⟨1180949, by rfl⟩ : syracuseStep 1574599 = 2361899) B2361899
theorem B1116065 : Blo 618297 1116065 := bstep (se 2 (by rfl) ⟨418524, by rfl⟩ : syracuseStep 1116065 = 837049) B837049
theorem B15075233 : Blo 618297 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B2230199 : Blo 618297 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B3868729 : Blo 618297 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B2099357 : Blo 618297 2099357 := bstep (se 3 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 2099357 = 787259) B787259
theorem B4458725 : Blo 618297 4458725 := bstep (se 4 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 4458725 = 836011) B836011
theorem B2099897 : Blo 618297 2099897 := bstep (se 2 (by rfl) ⟨787461, by rfl⟩ : syracuseStep 2099897 = 1574923) B1574923
theorem B2362067 : Blo 618297 2362067 := bstep (se 1 (by rfl) ⟨1771550, by rfl⟩ : syracuseStep 2362067 = 3543101) B3543101
theorem B5312087 : Blo 618297 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B1674875 : Blo 618297 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B32280371 : Blo 618297 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B5672771 : Blo 618297 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B14323727 : Blo 618297 14323727 := bstep (se 1 (by rfl) ⟨10742795, by rfl⟩ : syracuseStep 14323727 = 21485591) B21485591
theorem B3772505 : Blo 618297 3772505 := bstep (se 2 (by rfl) ⟨1414689, by rfl⟩ : syracuseStep 3772505 = 2829379) B2829379
theorem B7967105 : Blo 618297 7967105 := bstep (se 2 (by rfl) ⟨2987664, by rfl⟩ : syracuseStep 7967105 = 5975329) B5975329
theorem B3543533 : Blo 618297 3543533 := bstep (se 3 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 3543533 = 1328825) B1328825
theorem B1119251 : Blo 618297 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B660679 : Blo 618297 660679 := bstep (se 1 (by rfl) ⟨495509, by rfl⟩ : syracuseStep 660679 = 991019) B991019
theorem B2233889 : Blo 618297 2233889 := bstep (se 2 (by rfl) ⟨837708, by rfl⟩ : syracuseStep 2233889 = 1675417) B1675417
theorem B2987819 : Blo 618297 2987819 := bstep (se 1 (by rfl) ⟨2240864, by rfl⟩ : syracuseStep 2987819 = 4481729) B4481729
theorem B2824055 : Blo 618297 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B1906615 : Blo 618297 1906615 := bstep (se 1 (by rfl) ⟨1429961, by rfl⟩ : syracuseStep 1906615 = 2859923) B2859923
theorem B2234753 : Blo 618297 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B7084421 : Blo 618297 7084421 := bstep (se 4 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 7084421 = 1328329) B1328329
theorem B5085881 : Blo 618297 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B4037597 : Blo 618297 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B5315777 : Blo 618297 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B990571 : Blo 618297 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B5283245 : Blo 618297 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B1416827 : Blo 618297 1416827 := bstep (se 1 (by rfl) ⟨1062620, by rfl⟩ : syracuseStep 1416827 = 2125241) B2125241
theorem B6037681 : Blo 618297 6037681 := bstep (se 2 (by rfl) ⟨2264130, by rfl⟩ : syracuseStep 6037681 = 4528261) B4528261
theorem B663751 : Blo 618297 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B991583 : Blo 618297 991583 := bstep (se 1 (by rfl) ⟨743687, by rfl⟩ : syracuseStep 991583 = 1487375) B1487375
theorem B1253927 : Blo 618297 1253927 := bstep (se 1 (by rfl) ⟨940445, by rfl⟩ : syracuseStep 1253927 = 1880891) B1880891
theorem B991801 : Blo 618297 991801 := bstep (se 2 (by rfl) ⟨371925, by rfl⟩ : syracuseStep 991801 = 743851) B743851
theorem B696955 : Blo 618297 696955 := bstep (se 1 (by rfl) ⟨522716, by rfl⟩ : syracuseStep 696955 = 1045433) B1045433
theorem B2826937 : Blo 618297 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B991993 : Blo 618297 991993 := bstep (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) B743995
theorem B2237291 : Blo 618297 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B4039571 : Blo 618297 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B60400565 : Blo 618297 60400565 := bstep (se 5 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 60400565 = 5662553) B5662553
theorem B697423 : Blo 618297 697423 := bstep (se 1 (by rfl) ⟨523067, by rfl⟩ : syracuseStep 697423 = 1046135) B1046135
theorem B2237635 : Blo 618297 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B34022605 : Blo 618297 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B697819 : Blo 618297 697819 := bstep (se 1 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 697819 = 1046729) B1046729
theorem B927593 : Blo 618297 927593 := bstep (se 2 (by rfl) ⟨347847, by rfl⟩ : syracuseStep 927593 = 695695) B695695
theorem B698287 : Blo 618297 698287 := bstep (se 1 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 698287 = 1047431) B1047431
theorem B927671 : Blo 618297 927671 := bstep (se 1 (by rfl) ⟨695753, by rfl⟩ : syracuseStep 927671 = 1391507) B1391507
theorem B927707 : Blo 618297 927707 := bstep (se 1 (by rfl) ⟨695780, by rfl⟩ : syracuseStep 927707 = 1391561) B1391561
theorem B993479 : Blo 618297 993479 := bstep (se 1 (by rfl) ⟨745109, by rfl⟩ : syracuseStep 993479 = 1490219) B1490219
theorem B698719 : Blo 618297 698719 := bstep (se 1 (by rfl) ⟨524039, by rfl⟩ : syracuseStep 698719 = 1048079) B1048079
theorem B7973255 : Blo 618297 7973255 := bstep (se 1 (by rfl) ⟨5979941, by rfl⟩ : syracuseStep 7973255 = 11959883) B11959883
theorem B928175 : Blo 618297 928175 := bstep (se 1 (by rfl) ⟨696131, by rfl⟩ : syracuseStep 928175 = 1392263) B1392263
theorem B928265 : Blo 618297 928265 := bstep (se 2 (by rfl) ⟨348099, by rfl⟩ : syracuseStep 928265 = 696199) B696199
theorem B928295 : Blo 618297 928295 := bstep (se 1 (by rfl) ⟨696221, by rfl⟩ : syracuseStep 928295 = 1392443) B1392443
theorem B928379 : Blo 618297 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B699079 : Blo 618297 699079 := bstep (se 1 (by rfl) ⟨524309, by rfl⟩ : syracuseStep 699079 = 1048619) B1048619
theorem B928505 : Blo 618297 928505 := bstep (se 2 (by rfl) ⟨348189, by rfl⟩ : syracuseStep 928505 = 696379) B696379
theorem B928607 : Blo 618297 928607 := bstep (se 1 (by rfl) ⟨696455, by rfl⟩ : syracuseStep 928607 = 1392911) B1392911
theorem B928619 : Blo 618297 928619 := bstep (se 1 (by rfl) ⟨696464, by rfl⟩ : syracuseStep 928619 = 1392929) B1392929
theorem B2010017 : Blo 618297 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B4467631 : Blo 618297 4467631 := bstep (se 1 (by rfl) ⟨3350723, by rfl⟩ : syracuseStep 4467631 = 6701447) B6701447
theorem B1321991 : Blo 618297 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B928847 : Blo 618297 928847 := bstep (se 1 (by rfl) ⟨696635, by rfl⟩ : syracuseStep 928847 = 1393271) B1393271
theorem B928967 : Blo 618297 928967 := bstep (se 1 (by rfl) ⟨696725, by rfl⟩ : syracuseStep 928967 = 1393451) B1393451
theorem B929129 : Blo 618297 929129 := bstep (se 2 (by rfl) ⟨348423, by rfl⟩ : syracuseStep 929129 = 696847) B696847
theorem B929207 : Blo 618297 929207 := bstep (se 1 (by rfl) ⟨696905, by rfl⟩ : syracuseStep 929207 = 1393811) B1393811
theorem B1256887 : Blo 618297 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B929243 : Blo 618297 929243 := bstep (se 1 (by rfl) ⟨696932, by rfl⟩ : syracuseStep 929243 = 1393865) B1393865
theorem B8957405 : Blo 618297 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B699943 : Blo 618297 699943 := bstep (se 1 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 699943 = 1049915) B1049915
theorem B1289785 : Blo 618297 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B929711 : Blo 618297 929711 := bstep (se 1 (by rfl) ⟨697283, by rfl⟩ : syracuseStep 929711 = 1394567) B1394567
theorem B929801 : Blo 618297 929801 := bstep (se 2 (by rfl) ⟨348675, by rfl⟩ : syracuseStep 929801 = 697351) B697351
theorem B6696989 : Blo 618297 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B929831 : Blo 618297 929831 := bstep (se 1 (by rfl) ⟨697373, by rfl⟩ : syracuseStep 929831 = 1394747) B1394747
theorem B4239449 : Blo 618297 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B929915 : Blo 618297 929915 := bstep (se 1 (by rfl) ⟨697436, by rfl⟩ : syracuseStep 929915 = 1394873) B1394873
theorem B930041 : Blo 618297 930041 := bstep (se 2 (by rfl) ⟨348765, by rfl⟩ : syracuseStep 930041 = 697531) B697531
theorem B2240779 : Blo 618297 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B930143 : Blo 618297 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B2830697 : Blo 618297 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B930155 : Blo 618297 930155 := bstep (se 1 (by rfl) ⟨697616, by rfl⟩ : syracuseStep 930155 = 1395233) B1395233
theorem B9089489 : Blo 618297 9089489 := bstep (se 2 (by rfl) ⟨3408558, by rfl⟩ : syracuseStep 9089489 = 6817117) B6817117
theorem B4698647 : Blo 618297 4698647 := bstep (se 1 (by rfl) ⟨3523985, by rfl⟩ : syracuseStep 4698647 = 7047971) B7047971
theorem B2241083 : Blo 618297 2241083 := bstep (se 1 (by rfl) ⟨1680812, by rfl⟩ : syracuseStep 2241083 = 3361625) B3361625
theorem B930383 : Blo 618297 930383 := bstep (se 1 (by rfl) ⟨697787, by rfl⟩ : syracuseStep 930383 = 1395575) B1395575
theorem B930503 : Blo 618297 930503 := bstep (se 1 (by rfl) ⟨697877, by rfl⟩ : syracuseStep 930503 = 1395755) B1395755
theorem B930665 : Blo 618297 930665 := bstep (se 2 (by rfl) ⟨348999, by rfl⟩ : syracuseStep 930665 = 697999) B697999
theorem B930743 : Blo 618297 930743 := bstep (se 1 (by rfl) ⟨698057, by rfl⟩ : syracuseStep 930743 = 1396115) B1396115
theorem B930779 : Blo 618297 930779 := bstep (se 1 (by rfl) ⟨698084, by rfl⟩ : syracuseStep 930779 = 1396169) B1396169
theorem B1881145 : Blo 618297 1881145 := bstep (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) B1410859
theorem B931247 : Blo 618297 931247 := bstep (se 1 (by rfl) ⟨698435, by rfl⟩ : syracuseStep 931247 = 1396871) B1396871
theorem B931337 : Blo 618297 931337 := bstep (se 2 (by rfl) ⟨349251, by rfl⟩ : syracuseStep 931337 = 698503) B698503
theorem B931367 : Blo 618297 931367 := bstep (se 1 (by rfl) ⟨698525, by rfl⟩ : syracuseStep 931367 = 1397051) B1397051
theorem B5289533 : Blo 618297 5289533 := bstep (se 3 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 5289533 = 1983575) B1983575
theorem B931451 : Blo 618297 931451 := bstep (se 1 (by rfl) ⟨698588, by rfl⟩ : syracuseStep 931451 = 1397177) B1397177
theorem B931577 : Blo 618297 931577 := bstep (se 2 (by rfl) ⟨349341, by rfl⟩ : syracuseStep 931577 = 698683) B698683
theorem B931679 : Blo 618297 931679 := bstep (se 1 (by rfl) ⟨698759, by rfl⟩ : syracuseStep 931679 = 1397519) B1397519
theorem B931691 : Blo 618297 931691 := bstep (se 1 (by rfl) ⟨698768, by rfl⟩ : syracuseStep 931691 = 1397537) B1397537
theorem B8599505 : Blo 618297 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B1325135 : Blo 618297 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B931919 : Blo 618297 931919 := bstep (se 1 (by rfl) ⟨698939, by rfl⟩ : syracuseStep 931919 = 1397879) B1397879
theorem B4470947 : Blo 618297 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B1489067 : Blo 618297 1489067 := bstep (se 1 (by rfl) ⟨1116800, by rfl⟩ : syracuseStep 1489067 = 2233601) B2233601
theorem B932039 : Blo 618297 932039 := bstep (se 1 (by rfl) ⟨699029, by rfl⟩ : syracuseStep 932039 = 1398059) B1398059
theorem B932201 : Blo 618297 932201 := bstep (se 2 (by rfl) ⟨349575, by rfl⟩ : syracuseStep 932201 = 699151) B699151
theorem B932279 : Blo 618297 932279 := bstep (se 1 (by rfl) ⟨699209, by rfl⟩ : syracuseStep 932279 = 1398419) B1398419
theorem B932315 : Blo 618297 932315 := bstep (se 1 (by rfl) ⟨699236, by rfl⟩ : syracuseStep 932315 = 1398473) B1398473
theorem B1391201 : Blo 618297 1391201 := bstep (se 2 (by rfl) ⟨521700, by rfl⟩ : syracuseStep 1391201 = 1043401) B1043401
theorem B1325767 : Blo 618297 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B932783 : Blo 618297 932783 := bstep (se 1 (by rfl) ⟨699587, by rfl⟩ : syracuseStep 932783 = 1399175) B1399175
theorem B1391543 : Blo 618297 1391543 := bstep (se 1 (by rfl) ⟨1043657, by rfl⟩ : syracuseStep 1391543 = 2087315) B2087315
theorem B2866103 : Blo 618297 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B932873 : Blo 618297 932873 := bstep (se 2 (by rfl) ⟨349827, by rfl⟩ : syracuseStep 932873 = 699655) B699655
theorem B1588243 : Blo 618297 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B932903 : Blo 618297 932903 := bstep (se 1 (by rfl) ⟨699677, by rfl⟩ : syracuseStep 932903 = 1399355) B1399355
theorem B932987 : Blo 618297 932987 := bstep (se 1 (by rfl) ⟨699740, by rfl⟩ : syracuseStep 932987 = 1399481) B1399481
theorem B933113 : Blo 618297 933113 := bstep (se 2 (by rfl) ⟨349917, by rfl⟩ : syracuseStep 933113 = 699835) B699835
theorem B933215 : Blo 618297 933215 := bstep (se 1 (by rfl) ⟨699911, by rfl⟩ : syracuseStep 933215 = 1399823) B1399823
theorem B933227 : Blo 618297 933227 := bstep (se 1 (by rfl) ⟨699920, by rfl⟩ : syracuseStep 933227 = 1399841) B1399841
theorem B1392137 : Blo 618297 1392137 := bstep (se 2 (by rfl) ⟨522051, by rfl⟩ : syracuseStep 1392137 = 1044103) B1044103
theorem B1588859 : Blo 618297 1588859 := bstep (se 1 (by rfl) ⟨1191644, by rfl⟩ : syracuseStep 1588859 = 2383289) B2383289
theorem B1982141 : Blo 618297 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B10862351 : Blo 618297 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B1392479 : Blo 618297 1392479 := bstep (se 1 (by rfl) ⟨1044359, by rfl⟩ : syracuseStep 1392479 = 2088719) B2088719
theorem B1326955 : Blo 618297 1326955 := bstep (se 1 (by rfl) ⟨995216, by rfl⟩ : syracuseStep 1326955 = 1990433) B1990433
theorem B1327031 : Blo 618297 1327031 := bstep (se 1 (by rfl) ⟨995273, by rfl⟩ : syracuseStep 1327031 = 1990547) B1990547
theorem B1392659 : Blo 618297 1392659 := bstep (se 1 (by rfl) ⟨1044494, by rfl⟩ : syracuseStep 1392659 = 2088989) B2088989
theorem B1393001 : Blo 618297 1393001 := bstep (se 2 (by rfl) ⟨522375, by rfl⟩ : syracuseStep 1393001 = 1044751) B1044751
theorem B1130927 : Blo 618297 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B1491671 : Blo 618297 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B7947011 : Blo 618297 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B2016175 : Blo 618297 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B1393595 : Blo 618297 1393595 := bstep (se 1 (by rfl) ⟨1045196, by rfl⟩ : syracuseStep 1393595 = 2090393) B2090393
theorem B8602625 : Blo 618297 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B1393721 : Blo 618297 1393721 := bstep (se 2 (by rfl) ⟨522645, by rfl⟩ : syracuseStep 1393721 = 1045291) B1045291
theorem B1394063 : Blo 618297 1394063 := bstep (se 1 (by rfl) ⟨1045547, by rfl⟩ : syracuseStep 1394063 = 2091095) B2091095
theorem B1492679 : Blo 618297 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B1394387 : Blo 618297 1394387 := bstep (se 1 (by rfl) ⟨1045790, by rfl⟩ : syracuseStep 1394387 = 2091581) B2091581
theorem B4703993 : Blo 618297 4703993 := bstep (se 2 (by rfl) ⟨1763997, by rfl⟩ : syracuseStep 4703993 = 3527995) B3527995
theorem B8931161 : Blo 618297 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B3131297 : Blo 618297 3131297 := bstep (se 2 (by rfl) ⟨1174236, by rfl⟩ : syracuseStep 3131297 = 2348473) B2348473
theorem B11290661 : Blo 618297 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B13060403 : Blo 618297 13060403 := bstep (se 1 (by rfl) ⟨9795302, by rfl⟩ : syracuseStep 13060403 = 19590605) B19590605
theorem B4245821 : Blo 618297 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B1395323 : Blo 618297 1395323 := bstep (se 1 (by rfl) ⟨1046492, by rfl⟩ : syracuseStep 1395323 = 2092985) B2092985
theorem B1526521 : Blo 618297 1526521 := bstep (se 2 (by rfl) ⟨572445, by rfl⟩ : syracuseStep 1526521 = 1144891) B1144891
theorem B1395449 : Blo 618297 1395449 := bstep (se 2 (by rfl) ⟨523293, by rfl⟩ : syracuseStep 1395449 = 1046587) B1046587
theorem B3984349 : Blo 618297 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B3525605 : Blo 618297 3525605 := bstep (se 4 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 3525605 = 661051) B661051
theorem B1395719 : Blo 618297 1395719 := bstep (se 1 (by rfl) ⟨1046789, by rfl⟩ : syracuseStep 1395719 = 2093579) B2093579
theorem B1395791 : Blo 618297 1395791 := bstep (se 1 (by rfl) ⟨1046843, by rfl⟩ : syracuseStep 1395791 = 2093687) B2093687
theorem B4705451 : Blo 618297 4705451 := bstep (se 1 (by rfl) ⟨3529088, by rfl⟩ : syracuseStep 4705451 = 7058177) B7058177
theorem B707783 : Blo 618297 707783 := bstep (se 1 (by rfl) ⟨530837, by rfl⟩ : syracuseStep 707783 = 1061675) B1061675
theorem B1396187 : Blo 618297 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B2018849 : Blo 618297 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B4476539 : Blo 618297 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B4705937 : Blo 618297 4705937 := bstep (se 2 (by rfl) ⟨1764726, by rfl⟩ : syracuseStep 4705937 = 3529453) B3529453
theorem B1396655 : Blo 618297 1396655 := bstep (se 1 (by rfl) ⟨1047491, by rfl⟩ : syracuseStep 1396655 = 2094983) B2094983
theorem B1396907 : Blo 618297 1396907 := bstep (se 1 (by rfl) ⟨1047680, by rfl⟩ : syracuseStep 1396907 = 2095361) B2095361
theorem B4477463 : Blo 618297 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B1397447 : Blo 618297 1397447 := bstep (se 1 (by rfl) ⟨1048085, by rfl⟩ : syracuseStep 1397447 = 2096171) B2096171
theorem B2347805 : Blo 618297 2347805 := bstep (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) B880427
theorem B4707395 : Blo 618297 4707395 := bstep (se 1 (by rfl) ⟨3530546, by rfl⟩ : syracuseStep 4707395 = 7061093) B7061093
theorem B1398311 : Blo 618297 1398311 := bstep (se 1 (by rfl) ⟨1048733, by rfl⟩ : syracuseStep 1398311 = 2097467) B2097467
theorem B3987143 : Blo 618297 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B1398635 : Blo 618297 1398635 := bstep (se 1 (by rfl) ⟨1048976, by rfl⟩ : syracuseStep 1398635 = 2097953) B2097953
theorem B2086775 : Blo 618297 2086775 := bstep (se 1 (by rfl) ⟨1565081, by rfl⟩ : syracuseStep 2086775 = 3130163) B3130163
theorem B1398689 : Blo 618297 1398689 := bstep (se 2 (by rfl) ⟨524508, by rfl⟩ : syracuseStep 1398689 = 1049017) B1049017
theorem B4708367 : Blo 618297 4708367 := bstep (se 1 (by rfl) ⟨3531275, by rfl⟩ : syracuseStep 4708367 = 7062551) B7062551
theorem B2086991 : Blo 618297 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B1399031 : Blo 618297 1399031 := bstep (se 1 (by rfl) ⟨1049273, by rfl⟩ : syracuseStep 1399031 = 2098547) B2098547
theorem B2087369 : Blo 618297 2087369 := bstep (se 2 (by rfl) ⟨782763, by rfl⟩ : syracuseStep 2087369 = 1565527) B1565527
theorem B743899 : Blo 618297 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B1989305 : Blo 618297 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B2087639 : Blo 618297 2087639 := bstep (se 1 (by rfl) ⟨1565729, by rfl⟩ : syracuseStep 2087639 = 3131459) B3131459
theorem B1399625 : Blo 618297 1399625 := bstep (se 2 (by rfl) ⟨524859, by rfl⟩ : syracuseStep 1399625 = 1049719) B1049719
theorem B5954381 : Blo 618297 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B2349931 : Blo 618297 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B2087855 : Blo 618297 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B744571 : Blo 618297 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B1990291 : Blo 618297 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B15916985 : Blo 618297 15916985 := bstep (se 2 (by rfl) ⟨5968869, by rfl⟩ : syracuseStep 15916985 = 11937739) B11937739
theorem B1761527 : Blo 618297 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B2154763 : Blo 618297 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B9168025 : Blo 618297 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B2090231 : Blo 618297 2090231 := bstep (se 1 (by rfl) ⟨1567673, by rfl⟩ : syracuseStep 2090231 = 3135347) B3135347
theorem B4711769 : Blo 618297 4711769 := bstep (se 2 (by rfl) ⟨1766913, by rfl⟩ : syracuseStep 4711769 = 3533827) B3533827
theorem B2123227 : Blo 618297 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B2352665 : Blo 618297 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B2123297 : Blo 618297 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B2090555 : Blo 618297 2090555 := bstep (se 1 (by rfl) ⟨1567916, by rfl⟩ : syracuseStep 2090555 = 3135833) B3135833
theorem B1992289 : Blo 618297 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B2090825 : Blo 618297 2090825 := bstep (se 2 (by rfl) ⟨784059, by rfl⟩ : syracuseStep 2090825 = 1568119) B1568119
theorem B1763167 : Blo 618297 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B13428575 : Blo 618297 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B17885285 : Blo 618297 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B1173865 : Blo 618297 1173865 := bstep (se 2 (by rfl) ⟨440199, by rfl⟩ : syracuseStep 1173865 = 880399) B880399
theorem B2517601 : Blo 618297 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B1993405 : Blo 618297 1993405 := bstep (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) B747527
theorem B1764089 : Blo 618297 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B1567583 : Blo 618297 1567583 := bstep (se 1 (by rfl) ⟨1175687, by rfl⟩ : syracuseStep 1567583 = 2351375) B2351375
theorem B1764271 : Blo 618297 1764271 := bstep (se 1 (by rfl) ⟨1323203, by rfl⟩ : syracuseStep 1764271 = 2646407) B2646407
theorem B2091959 : Blo 618297 2091959 := bstep (se 1 (by rfl) ⟨1568969, by rfl⟩ : syracuseStep 2091959 = 3137939) B3137939
theorem B6810551 : Blo 618297 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B5303339 : Blo 618297 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B2354291 : Blo 618297 2354291 := bstep (se 1 (by rfl) ⟨1765718, by rfl⟩ : syracuseStep 2354291 = 3531437) B3531437
theorem B4484267 : Blo 618297 4484267 := bstep (se 1 (by rfl) ⟨3363200, by rfl⟩ : syracuseStep 4484267 = 6726401) B6726401
theorem B3140855 : Blo 618297 3140855 := bstep (se 1 (by rfl) ⟨2355641, by rfl⟩ : syracuseStep 3140855 = 4711283) B4711283
theorem B1043705 : Blo 618297 1043705 := bstep (se 2 (by rfl) ⟨391389, by rfl⟩ : syracuseStep 1043705 = 782779) B782779
theorem B1043887 : Blo 618297 1043887 := bstep (se 1 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 1043887 = 1565831) B1565831
theorem B1043975 : Blo 618297 1043975 := bstep (se 1 (by rfl) ⟨782981, by rfl⟩ : syracuseStep 1043975 = 1565963) B1565963
theorem B2092553 : Blo 618297 2092553 := bstep (se 2 (by rfl) ⟨784707, by rfl⟩ : syracuseStep 2092553 = 1569415) B1569415
theorem B1437193 : Blo 618297 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B1568281 : Blo 618297 1568281 := bstep (se 2 (by rfl) ⟨588105, by rfl⟩ : syracuseStep 1568281 = 1176211) B1176211
theorem B1175239 : Blo 618297 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B4714199 : Blo 618297 4714199 := bstep (se 1 (by rfl) ⟨3535649, by rfl⟩ : syracuseStep 4714199 = 7071299) B7071299
theorem B3141341 : Blo 618297 3141341 := bstep (se 3 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 3141341 = 1178003) B1178003
theorem B1208137 : Blo 618297 1208137 := bstep (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) B906103
theorem B1568585 : Blo 618297 1568585 := bstep (se 2 (by rfl) ⟨588219, by rfl⟩ : syracuseStep 1568585 = 1176439) B1176439
theorem B618319 : Blo 618297 618319 := bstep (se 1 (by rfl) ⟨463739, by rfl⟩ : syracuseStep 618319 = 927479) B927479
theorem B618335 : Blo 618297 618335 := bstep (se 1 (by rfl) ⟨463751, by rfl⟩ : syracuseStep 618335 = 927503) B927503
theorem B1044319 : Blo 618297 1044319 := bstep (se 1 (by rfl) ⟨783239, by rfl⟩ : syracuseStep 1044319 = 1566479) B1566479
theorem B618363 : Blo 618297 618363 := bstep (se 1 (by rfl) ⟨463772, by rfl⟩ : syracuseStep 618363 = 927545) B927545
theorem B618415 : Blo 618297 618415 := bstep (se 1 (by rfl) ⟨463811, by rfl⟩ : syracuseStep 618415 = 927623) B927623
theorem B1044407 : Blo 618297 1044407 := bstep (se 1 (by rfl) ⟨783305, by rfl⟩ : syracuseStep 1044407 = 1566611) B1566611
theorem B3534785 : Blo 618297 3534785 := bstep (se 2 (by rfl) ⟨1325544, by rfl⟩ : syracuseStep 3534785 = 2651089) B2651089
theorem B618439 : Blo 618297 618439 := bstep (se 1 (by rfl) ⟨463829, by rfl⟩ : syracuseStep 618439 = 927659) B927659
theorem B618459 : Blo 618297 618459 := bstep (se 1 (by rfl) ⟨463844, by rfl⟩ : syracuseStep 618459 = 927689) B927689
theorem B618535 : Blo 618297 618535 := bstep (se 1 (by rfl) ⟨463901, by rfl⟩ : syracuseStep 618535 = 927803) B927803
theorem B618575 : Blo 618297 618575 := bstep (se 1 (by rfl) ⟨463931, by rfl⟩ : syracuseStep 618575 = 927863) B927863
theorem B618591 : Blo 618297 618591 := bstep (se 1 (by rfl) ⟨463943, by rfl⟩ : syracuseStep 618591 = 927887) B927887
theorem B618619 : Blo 618297 618619 := bstep (se 1 (by rfl) ⟨463964, by rfl⟩ : syracuseStep 618619 = 927929) B927929
theorem B1765547 : Blo 618297 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B618671 : Blo 618297 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B618695 : Blo 618297 618695 := bstep (se 1 (by rfl) ⟨464021, by rfl⟩ : syracuseStep 618695 = 928043) B928043
theorem B618715 : Blo 618297 618715 := bstep (se 1 (by rfl) ⟨464036, by rfl⟩ : syracuseStep 618715 = 928073) B928073
theorem B618791 : Blo 618297 618791 := bstep (se 1 (by rfl) ⟨464093, by rfl⟩ : syracuseStep 618791 = 928187) B928187
theorem B618831 : Blo 618297 618831 := bstep (se 1 (by rfl) ⟨464123, by rfl⟩ : syracuseStep 618831 = 928247) B928247
theorem B618847 : Blo 618297 618847 := bstep (se 1 (by rfl) ⟨464135, by rfl⟩ : syracuseStep 618847 = 928271) B928271
theorem B2093417 : Blo 618297 2093417 := bstep (se 2 (by rfl) ⟨785031, by rfl⟩ : syracuseStep 2093417 = 1570063) B1570063
theorem B618875 : Blo 618297 618875 := bstep (se 1 (by rfl) ⟨464156, by rfl⟩ : syracuseStep 618875 = 928313) B928313
theorem B2355581 : Blo 618297 2355581 := bstep (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) B883343
theorem B1765775 : Blo 618297 1765775 := bstep (se 1 (by rfl) ⟨1324331, by rfl⟩ : syracuseStep 1765775 = 2648663) B2648663
theorem B618927 : Blo 618297 618927 := bstep (se 1 (by rfl) ⟨464195, by rfl⟩ : syracuseStep 618927 = 928391) B928391
theorem B618951 : Blo 618297 618951 := bstep (se 1 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 618951 = 928427) B928427
theorem B618971 : Blo 618297 618971 := bstep (se 1 (by rfl) ⟨464228, by rfl⟩ : syracuseStep 618971 = 928457) B928457
theorem B1045001 : Blo 618297 1045001 := bstep (se 2 (by rfl) ⟨391875, by rfl⟩ : syracuseStep 1045001 = 783751) B783751
theorem B619047 : Blo 618297 619047 := bstep (se 1 (by rfl) ⟨464285, by rfl⟩ : syracuseStep 619047 = 928571) B928571
theorem B619087 : Blo 618297 619087 := bstep (se 1 (by rfl) ⟨464315, by rfl⟩ : syracuseStep 619087 = 928631) B928631
theorem B619103 : Blo 618297 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B619131 : Blo 618297 619131 := bstep (se 1 (by rfl) ⟨464348, by rfl⟩ : syracuseStep 619131 = 928697) B928697
theorem B2519675 : Blo 618297 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B1045163 : Blo 618297 1045163 := bstep (se 1 (by rfl) ⟨783872, by rfl⟩ : syracuseStep 1045163 = 1567745) B1567745
theorem B619183 : Blo 618297 619183 := bstep (se 1 (by rfl) ⟨464387, by rfl⟩ : syracuseStep 619183 = 928775) B928775
theorem B783047 : Blo 618297 783047 := bstep (se 1 (by rfl) ⟨587285, by rfl⟩ : syracuseStep 783047 = 1174571) B1174571
theorem B619207 : Blo 618297 619207 := bstep (se 1 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 619207 = 928811) B928811
theorem B11465425 : Blo 618297 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B10711763 : Blo 618297 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B619227 : Blo 618297 619227 := bstep (se 1 (by rfl) ⟨464420, by rfl⟩ : syracuseStep 619227 = 928841) B928841
theorem B619303 : Blo 618297 619303 := bstep (se 1 (by rfl) ⟨464477, by rfl⟩ : syracuseStep 619303 = 928955) B928955
theorem B2978633 : Blo 618297 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B619343 : Blo 618297 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B783199 : Blo 618297 783199 := bstep (se 1 (by rfl) ⟨587399, by rfl⟩ : syracuseStep 783199 = 1174799) B1174799
theorem B619359 : Blo 618297 619359 := bstep (se 1 (by rfl) ⟨464519, by rfl⟩ : syracuseStep 619359 = 929039) B929039
theorem B619387 : Blo 618297 619387 := bstep (se 1 (by rfl) ⟨464540, by rfl⟩ : syracuseStep 619387 = 929081) B929081
theorem B11891609 : Blo 618297 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B619439 : Blo 618297 619439 := bstep (se 1 (by rfl) ⟨464579, by rfl⟩ : syracuseStep 619439 = 929159) B929159
theorem B1569719 : Blo 618297 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B2094011 : Blo 618297 2094011 := bstep (se 1 (by rfl) ⟨1570508, by rfl⟩ : syracuseStep 2094011 = 3141017) B3141017
theorem B619463 : Blo 618297 619463 := bstep (se 1 (by rfl) ⟨464597, by rfl⟩ : syracuseStep 619463 = 929195) B929195
theorem B619483 : Blo 618297 619483 := bstep (se 1 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 619483 = 929225) B929225
theorem B619559 : Blo 618297 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B1045561 : Blo 618297 1045561 := bstep (se 2 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 1045561 = 784171) B784171
theorem B619599 : Blo 618297 619599 := bstep (se 1 (by rfl) ⟨464699, by rfl⟩ : syracuseStep 619599 = 929399) B929399
theorem B619615 : Blo 618297 619615 := bstep (se 1 (by rfl) ⟨464711, by rfl⟩ : syracuseStep 619615 = 929423) B929423
theorem B619643 : Blo 618297 619643 := bstep (se 1 (by rfl) ⟨464732, by rfl⟩ : syracuseStep 619643 = 929465) B929465
theorem B619695 : Blo 618297 619695 := bstep (se 1 (by rfl) ⟨464771, by rfl⟩ : syracuseStep 619695 = 929543) B929543
theorem B1045703 : Blo 618297 1045703 := bstep (se 1 (by rfl) ⟨784277, by rfl⟩ : syracuseStep 1045703 = 1568555) B1568555
theorem B619719 : Blo 618297 619719 := bstep (se 1 (by rfl) ⟨464789, by rfl⟩ : syracuseStep 619719 = 929579) B929579
theorem B619739 : Blo 618297 619739 := bstep (se 1 (by rfl) ⟨464804, by rfl⟩ : syracuseStep 619739 = 929609) B929609
theorem B619815 : Blo 618297 619815 := bstep (se 1 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 619815 = 929723) B929723
theorem B619855 : Blo 618297 619855 := bstep (se 1 (by rfl) ⟨464891, by rfl⟩ : syracuseStep 619855 = 929783) B929783
theorem B619871 : Blo 618297 619871 := bstep (se 1 (by rfl) ⟨464903, by rfl⟩ : syracuseStep 619871 = 929807) B929807
theorem B1045865 : Blo 618297 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B619899 : Blo 618297 619899 := bstep (se 1 (by rfl) ⟨464924, by rfl⟩ : syracuseStep 619899 = 929849) B929849
theorem B619951 : Blo 618297 619951 := bstep (se 1 (by rfl) ⟨464963, by rfl⟩ : syracuseStep 619951 = 929927) B929927
theorem B619975 : Blo 618297 619975 := bstep (se 1 (by rfl) ⟨464981, by rfl⟩ : syracuseStep 619975 = 929963) B929963
theorem B619995 : Blo 618297 619995 := bstep (se 1 (by rfl) ⟨464996, by rfl⟩ : syracuseStep 619995 = 929993) B929993
theorem B11924981 : Blo 618297 11924981 := bstep (se 5 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 11924981 = 1117967) B1117967
theorem B620071 : Blo 618297 620071 := bstep (se 1 (by rfl) ⟨465053, by rfl⟩ : syracuseStep 620071 = 930107) B930107
theorem B620111 : Blo 618297 620111 := bstep (se 1 (by rfl) ⟨465083, by rfl⟩ : syracuseStep 620111 = 930167) B930167
theorem B620127 : Blo 618297 620127 := bstep (se 1 (by rfl) ⟨465095, by rfl⟩ : syracuseStep 620127 = 930191) B930191
theorem B620155 : Blo 618297 620155 := bstep (se 1 (by rfl) ⟨465116, by rfl⟩ : syracuseStep 620155 = 930233) B930233
theorem B620207 : Blo 618297 620207 := bstep (se 1 (by rfl) ⟨465155, by rfl⟩ : syracuseStep 620207 = 930311) B930311
theorem B620231 : Blo 618297 620231 := bstep (se 1 (by rfl) ⟨465173, by rfl⟩ : syracuseStep 620231 = 930347) B930347
theorem B620251 : Blo 618297 620251 := bstep (se 1 (by rfl) ⟨465188, by rfl⟩ : syracuseStep 620251 = 930377) B930377
theorem B1046263 : Blo 618297 1046263 := bstep (se 1 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 1046263 = 1569395) B1569395
theorem B620327 : Blo 618297 620327 := bstep (se 1 (by rfl) ⟨465245, by rfl⟩ : syracuseStep 620327 = 930491) B930491
theorem B620367 : Blo 618297 620367 := bstep (se 1 (by rfl) ⟨465275, by rfl⟩ : syracuseStep 620367 = 930551) B930551
theorem B620383 : Blo 618297 620383 := bstep (se 1 (by rfl) ⟨465287, by rfl⟩ : syracuseStep 620383 = 930575) B930575
theorem B3766135 : Blo 618297 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B620411 : Blo 618297 620411 := bstep (se 1 (by rfl) ⟨465308, by rfl⟩ : syracuseStep 620411 = 930617) B930617
theorem B1177487 : Blo 618297 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B620463 : Blo 618297 620463 := bstep (se 1 (by rfl) ⟨465347, by rfl⟩ : syracuseStep 620463 = 930695) B930695
theorem B1046459 : Blo 618297 1046459 := bstep (se 1 (by rfl) ⟨784844, by rfl⟩ : syracuseStep 1046459 = 1569689) B1569689
theorem B620487 : Blo 618297 620487 := bstep (se 1 (by rfl) ⟨465365, by rfl⟩ : syracuseStep 620487 = 930731) B930731
theorem B620507 : Blo 618297 620507 := bstep (se 1 (by rfl) ⟨465380, by rfl⟩ : syracuseStep 620507 = 930761) B930761
theorem B1570823 : Blo 618297 1570823 := bstep (se 1 (by rfl) ⟨1178117, by rfl⟩ : syracuseStep 1570823 = 2356235) B2356235
theorem B1046567 : Blo 618297 1046567 := bstep (se 1 (by rfl) ⟨784925, by rfl⟩ : syracuseStep 1046567 = 1569851) B1569851
theorem B620583 : Blo 618297 620583 := bstep (se 1 (by rfl) ⟨465437, by rfl⟩ : syracuseStep 620583 = 930875) B930875
theorem B1570873 : Blo 618297 1570873 := bstep (se 2 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 1570873 = 1178155) B1178155
theorem B620623 : Blo 618297 620623 := bstep (se 1 (by rfl) ⟨465467, by rfl⟩ : syracuseStep 620623 = 930935) B930935
theorem B620639 : Blo 618297 620639 := bstep (se 1 (by rfl) ⟨465479, by rfl⟩ : syracuseStep 620639 = 930959) B930959
theorem B620667 : Blo 618297 620667 := bstep (se 1 (by rfl) ⟨465500, by rfl⟩ : syracuseStep 620667 = 931001) B931001
theorem B620719 : Blo 618297 620719 := bstep (se 1 (by rfl) ⟨465539, by rfl⟩ : syracuseStep 620719 = 931079) B931079
theorem B620743 : Blo 618297 620743 := bstep (se 1 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 620743 = 931115) B931115
theorem B620763 : Blo 618297 620763 := bstep (se 1 (by rfl) ⟨465572, by rfl⟩ : syracuseStep 620763 = 931145) B931145
theorem B2357495 : Blo 618297 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B620839 : Blo 618297 620839 := bstep (se 1 (by rfl) ⟨465629, by rfl⟩ : syracuseStep 620839 = 931259) B931259
theorem B1046857 : Blo 618297 1046857 := bstep (se 2 (by rfl) ⟨392571, by rfl⟩ : syracuseStep 1046857 = 785143) B785143
theorem B620879 : Blo 618297 620879 := bstep (se 1 (by rfl) ⟨465659, by rfl⟩ : syracuseStep 620879 = 931319) B931319
theorem B620895 : Blo 618297 620895 := bstep (se 1 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 620895 = 931343) B931343
theorem B1571177 : Blo 618297 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B1046891 : Blo 618297 1046891 := bstep (se 1 (by rfl) ⟨785168, by rfl⟩ : syracuseStep 1046891 = 1570337) B1570337
theorem B620923 : Blo 618297 620923 := bstep (se 1 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 620923 = 931385) B931385
theorem B620975 : Blo 618297 620975 := bstep (se 1 (by rfl) ⟨465731, by rfl⟩ : syracuseStep 620975 = 931463) B931463
theorem B620999 : Blo 618297 620999 := bstep (se 1 (by rfl) ⟨465749, by rfl⟩ : syracuseStep 620999 = 931499) B931499
theorem B621019 : Blo 618297 621019 := bstep (se 1 (by rfl) ⟨465764, by rfl⟩ : syracuseStep 621019 = 931529) B931529
theorem B621095 : Blo 618297 621095 := bstep (se 1 (by rfl) ⟨465821, by rfl⟩ : syracuseStep 621095 = 931643) B931643
theorem B4717115 : Blo 618297 4717115 := bstep (se 1 (by rfl) ⟨3537836, by rfl⟩ : syracuseStep 4717115 = 7075673) B7075673
theorem B621135 : Blo 618297 621135 := bstep (se 1 (by rfl) ⟨465851, by rfl⟩ : syracuseStep 621135 = 931703) B931703
theorem B621151 : Blo 618297 621151 := bstep (se 1 (by rfl) ⟨465863, by rfl⟩ : syracuseStep 621151 = 931727) B931727
theorem B2095739 : Blo 618297 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B621179 : Blo 618297 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B621231 : Blo 618297 621231 := bstep (se 1 (by rfl) ⟨465923, by rfl⟩ : syracuseStep 621231 = 931847) B931847
theorem B621255 : Blo 618297 621255 := bstep (se 1 (by rfl) ⟨465941, by rfl⟩ : syracuseStep 621255 = 931883) B931883
theorem B621275 : Blo 618297 621275 := bstep (se 1 (by rfl) ⟨465956, by rfl⟩ : syracuseStep 621275 = 931913) B931913
theorem B1047289 : Blo 618297 1047289 := bstep (se 2 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 1047289 = 785467) B785467
theorem B2095901 : Blo 618297 2095901 := bstep (se 3 (by rfl) ⟨392981, by rfl⟩ : syracuseStep 2095901 = 785963) B785963
theorem B621351 : Blo 618297 621351 := bstep (se 1 (by rfl) ⟨466013, by rfl⟩ : syracuseStep 621351 = 932027) B932027
theorem B621391 : Blo 618297 621391 := bstep (se 1 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 621391 = 932087) B932087
theorem B621407 : Blo 618297 621407 := bstep (se 1 (by rfl) ⟨466055, by rfl⟩ : syracuseStep 621407 = 932111) B932111
theorem B621435 : Blo 618297 621435 := bstep (se 1 (by rfl) ⟨466076, by rfl⟩ : syracuseStep 621435 = 932153) B932153
theorem B1178543 : Blo 618297 1178543 := bstep (se 1 (by rfl) ⟨883907, by rfl⟩ : syracuseStep 1178543 = 1767815) B1767815
theorem B621487 : Blo 618297 621487 := bstep (se 1 (by rfl) ⟨466115, by rfl⟩ : syracuseStep 621487 = 932231) B932231
theorem B883639 : Blo 618297 883639 := bstep (se 1 (by rfl) ⟨662729, by rfl⟩ : syracuseStep 883639 = 1325459) B1325459
theorem B2128823 : Blo 618297 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B621511 : Blo 618297 621511 := bstep (se 1 (by rfl) ⟨466133, by rfl⟩ : syracuseStep 621511 = 932267) B932267
theorem B785371 : Blo 618297 785371 := bstep (se 1 (by rfl) ⟨589028, by rfl⟩ : syracuseStep 785371 = 1178057) B1178057
theorem B621531 : Blo 618297 621531 := bstep (se 1 (by rfl) ⟨466148, by rfl⟩ : syracuseStep 621531 = 932297) B932297
theorem B1047559 : Blo 618297 1047559 := bstep (se 1 (by rfl) ⟨785669, by rfl⟩ : syracuseStep 1047559 = 1571339) B1571339
theorem B3963923 : Blo 618297 3963923 := bstep (se 1 (by rfl) ⟨2972942, by rfl⟩ : syracuseStep 3963923 = 5945885) B5945885
theorem B621607 : Blo 618297 621607 := bstep (se 1 (by rfl) ⟨466205, by rfl⟩ : syracuseStep 621607 = 932411) B932411
theorem B621647 : Blo 618297 621647 := bstep (se 1 (by rfl) ⟨466235, by rfl⟩ : syracuseStep 621647 = 932471) B932471
theorem B621663 : Blo 618297 621663 := bstep (se 1 (by rfl) ⟨466247, by rfl⟩ : syracuseStep 621663 = 932495) B932495
theorem B621691 : Blo 618297 621691 := bstep (se 1 (by rfl) ⟨466268, by rfl⟩ : syracuseStep 621691 = 932537) B932537
theorem B2522269 : Blo 618297 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B7961773 : Blo 618297 7961773 := bstep (se 3 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 7961773 = 2985665) B2985665
theorem B621743 : Blo 618297 621743 := bstep (se 1 (by rfl) ⟨466307, by rfl⟩ : syracuseStep 621743 = 932615) B932615
theorem B2358467 : Blo 618297 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B621767 : Blo 618297 621767 := bstep (se 1 (by rfl) ⟨466325, by rfl⟩ : syracuseStep 621767 = 932651) B932651
theorem B621787 : Blo 618297 621787 := bstep (se 1 (by rfl) ⟨466340, by rfl⟩ : syracuseStep 621787 = 932681) B932681
theorem B621863 : Blo 618297 621863 := bstep (se 1 (by rfl) ⟨466397, by rfl⟩ : syracuseStep 621863 = 932795) B932795
theorem B621903 : Blo 618297 621903 := bstep (se 1 (by rfl) ⟨466427, by rfl⟩ : syracuseStep 621903 = 932855) B932855
theorem B1178975 : Blo 618297 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B621919 : Blo 618297 621919 := bstep (se 1 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 621919 = 932879) B932879
theorem B621947 : Blo 618297 621947 := bstep (se 1 (by rfl) ⟨466460, by rfl⟩ : syracuseStep 621947 = 932921) B932921
theorem B621999 : Blo 618297 621999 := bstep (se 1 (by rfl) ⟨466499, by rfl⟩ : syracuseStep 621999 = 932999) B932999
theorem B1047991 : Blo 618297 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B622023 : Blo 618297 622023 := bstep (se 1 (by rfl) ⟨466517, by rfl⟩ : syracuseStep 622023 = 933035) B933035
theorem B2096603 : Blo 618297 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B622043 : Blo 618297 622043 := bstep (se 1 (by rfl) ⟨466532, by rfl⟩ : syracuseStep 622043 = 933065) B933065
theorem B1768999 : Blo 618297 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B622119 : Blo 618297 622119 := bstep (se 1 (by rfl) ⟨466589, by rfl⟩ : syracuseStep 622119 = 933179) B933179
theorem B622159 : Blo 618297 622159 := bstep (se 1 (by rfl) ⟨466619, by rfl⟩ : syracuseStep 622159 = 933239) B933239
theorem B622175 : Blo 618297 622175 := bstep (se 1 (by rfl) ⟨466631, by rfl⟩ : syracuseStep 622175 = 933263) B933263
theorem B1048187 : Blo 618297 1048187 := bstep (se 1 (by rfl) ⟨786140, by rfl⟩ : syracuseStep 1048187 = 1572281) B1572281
theorem B622203 : Blo 618297 622203 := bstep (se 1 (by rfl) ⟨466652, by rfl⟩ : syracuseStep 622203 = 933305) B933305
theorem B622255 : Blo 618297 622255 := bstep (se 1 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 622255 = 933383) B933383
theorem B2358983 : Blo 618297 2358983 := bstep (se 1 (by rfl) ⟨1769237, by rfl⟩ : syracuseStep 2358983 = 3538475) B3538475
theorem B622279 : Blo 618297 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B1277915 : Blo 618297 1277915 := bstep (se 1 (by rfl) ⟨958436, by rfl⟩ : syracuseStep 1277915 = 1916873) B1916873
theorem B1704041 : Blo 618297 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B10060013 : Blo 618297 10060013 := bstep (se 3 (by rfl) ⟨1886252, by rfl⟩ : syracuseStep 10060013 = 3772505) B3772505
theorem B885001 : Blo 618297 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B1048943 : Blo 618297 1048943 := bstep (se 1 (by rfl) ⟨786707, by rfl⟩ : syracuseStep 1048943 = 1573415) B1573415
theorem B1573303 : Blo 618297 1573303 := bstep (se 1 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 1573303 = 2359955) B2359955
theorem B2228755 : Blo 618297 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B2097683 : Blo 618297 2097683 := bstep (se 1 (by rfl) ⟨1573262, by rfl⟩ : syracuseStep 2097683 = 3146525) B3146525
theorem B1049159 : Blo 618297 1049159 := bstep (se 1 (by rfl) ⟨786869, by rfl⟩ : syracuseStep 1049159 = 1573739) B1573739
theorem B3539659 : Blo 618297 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B3769249 : Blo 618297 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B1049591 : Blo 618297 1049591 := bstep (se 1 (by rfl) ⟨787193, by rfl⟩ : syracuseStep 1049591 = 1574387) B1574387
theorem B3146849 : Blo 618297 3146849 := bstep (se 2 (by rfl) ⟨1180068, by rfl⟩ : syracuseStep 3146849 = 2360137) B2360137
theorem B3015805 : Blo 618297 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B2688233 : Blo 618297 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B3343805 : Blo 618297 3343805 := bstep (se 3 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 3343805 = 1253927) B1253927
theorem B12224033 : Blo 618297 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B2983513 : Blo 618297 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B1574711 : Blo 618297 1574711 := bstep (se 1 (by rfl) ⟨1181033, by rfl⟩ : syracuseStep 1574711 = 2362067) B2362067
theorem B1574761 : Blo 618297 1574761 := bstep (se 2 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 1574761 = 1181071) B1181071
theorem B4720517 : Blo 618297 4720517 := bstep (se 4 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 4720517 = 885097) B885097
theorem B2656385 : Blo 618297 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B2099465 : Blo 618297 2099465 := bstep (se 2 (by rfl) ⟨787299, by rfl⟩ : syracuseStep 2099465 = 1574599) B1574599
theorem B3541391 : Blo 618297 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B2984359 : Blo 618297 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B22940333 : Blo 618297 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B5311403 : Blo 618297 5311403 := bstep (se 1 (by rfl) ⟨3983552, by rfl⟩ : syracuseStep 5311403 = 7967105) B7967105
theorem B2362355 : Blo 618297 2362355 := bstep (se 1 (by rfl) ⟨1771766, by rfl⟩ : syracuseStep 2362355 = 3543533) B3543533
theorem B2984975 : Blo 618297 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B3149117 : Blo 618297 3149117 := bstep (se 3 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 3149117 = 1180919) B1180919
theorem B2657873 : Blo 618297 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B2035361 : Blo 618297 2035361 := bstep (se 2 (by rfl) ⟨763260, by rfl⟩ : syracuseStep 2035361 = 1526521) B1526521
theorem B2658095 : Blo 618297 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B5312465 : Blo 618297 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B4722947 : Blo 618297 4722947 := bstep (se 1 (by rfl) ⟨3542210, by rfl⟩ : syracuseStep 4722947 = 7084421) B7084421
theorem B3969587 : Blo 618297 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B2691731 : Blo 618297 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B3543851 : Blo 618297 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B1610849 : Blo 618297 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B661055 : Blo 618297 661055 := bstep (se 1 (by rfl) ⟨495791, by rfl⟩ : syracuseStep 661055 = 991583) B991583
theorem B2987705 : Blo 618297 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B2693047 : Blo 618297 2693047 := bstep (se 1 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 2693047 = 4039571) B4039571
theorem B3971045 : Blo 618297 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B1415531 : Blo 618297 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B8952383 : Blo 618297 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B5315503 : Blo 618297 5315503 := bstep (se 1 (by rfl) ⟨3986627, by rfl⟩ : syracuseStep 5315503 = 7973255) B7973255
theorem B2989511 : Blo 618297 2989511 := bstep (se 1 (by rfl) ⟨2242133, by rfl⟩ : syracuseStep 2989511 = 4484267) B4484267
theorem B695803 : Blo 618297 695803 := bstep (se 1 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 695803 = 1043705) B1043705
theorem B5971603 : Blo 618297 5971603 := bstep (se 1 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 5971603 = 8957405) B8957405
theorem B695983 : Blo 618297 695983 := bstep (se 1 (by rfl) ⟨521987, by rfl⟩ : syracuseStep 695983 = 1043975) B1043975
theorem B5021513 : Blo 618297 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B696271 : Blo 618297 696271 := bstep (se 1 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 696271 = 1044407) B1044407
theorem B4464659 : Blo 618297 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B2826299 : Blo 618297 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B696667 : Blo 618297 696667 := bstep (se 1 (by rfl) ⟨522500, by rfl⟩ : syracuseStep 696667 = 1045001) B1045001
theorem B1679783 : Blo 618297 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B696775 : Blo 618297 696775 := bstep (se 1 (by rfl) ⟨522581, by rfl⟩ : syracuseStep 696775 = 1045163) B1045163
theorem B991865 : Blo 618297 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B697135 : Blo 618297 697135 := bstep (se 1 (by rfl) ⟨522851, by rfl⟩ : syracuseStep 697135 = 1045703) B1045703
theorem B697243 : Blo 618297 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B697639 : Blo 618297 697639 := bstep (se 1 (by rfl) ⟨523229, by rfl⟩ : syracuseStep 697639 = 1046459) B1046459
theorem B697711 : Blo 618297 697711 := bstep (se 1 (by rfl) ⟨523283, by rfl⟩ : syracuseStep 697711 = 1046567) B1046567
theorem B5383597 : Blo 618297 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B992711 : Blo 618297 992711 := bstep (se 1 (by rfl) ⟨744533, by rfl⟩ : syracuseStep 992711 = 1489067) B1489067
theorem B697927 : Blo 618297 697927 := bstep (se 1 (by rfl) ⟨523445, by rfl⟩ : syracuseStep 697927 = 1046891) B1046891
theorem B4466333 : Blo 618297 4466333 := bstep (se 3 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 4466333 = 1674875) B1674875
theorem B927467 : Blo 618297 927467 := bstep (se 1 (by rfl) ⟨695600, by rfl⟩ : syracuseStep 927467 = 1391201) B1391201
theorem B1320761 : Blo 618297 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B927695 : Blo 618297 927695 := bstep (se 1 (by rfl) ⟨695771, by rfl⟩ : syracuseStep 927695 = 1391543) B1391543
theorem B1910735 : Blo 618297 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B1419215 : Blo 618297 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B928091 : Blo 618297 928091 := bstep (se 1 (by rfl) ⟨696068, by rfl⟩ : syracuseStep 928091 = 1392137) B1392137
theorem B1059239 : Blo 618297 1059239 := bstep (se 1 (by rfl) ⟨794429, by rfl⟩ : syracuseStep 1059239 = 1588859) B1588859
theorem B698791 : Blo 618297 698791 := bstep (se 1 (by rfl) ⟨524093, by rfl⟩ : syracuseStep 698791 = 1048187) B1048187
theorem B1321427 : Blo 618297 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B928319 : Blo 618297 928319 := bstep (se 1 (by rfl) ⟨696239, by rfl⟩ : syracuseStep 928319 = 1392479) B1392479
theorem B928439 : Blo 618297 928439 := bstep (se 1 (by rfl) ⟨696329, by rfl⟩ : syracuseStep 928439 = 1392659) B1392659
theorem B928667 : Blo 618297 928667 := bstep (se 1 (by rfl) ⟨696500, by rfl⟩ : syracuseStep 928667 = 1393001) B1393001
theorem B699367 : Blo 618297 699367 := bstep (se 1 (by rfl) ⟨524525, by rfl⟩ : syracuseStep 699367 = 1049051) B1049051
theorem B994447 : Blo 618297 994447 := bstep (se 1 (by rfl) ⟨745835, by rfl⟩ : syracuseStep 994447 = 1491671) B1491671
theorem B929063 : Blo 618297 929063 := bstep (se 1 (by rfl) ⟨696797, by rfl⟩ : syracuseStep 929063 = 1393595) B1393595
theorem B929147 : Blo 618297 929147 := bstep (se 1 (by rfl) ⟨696860, by rfl⟩ : syracuseStep 929147 = 1393721) B1393721
theorem B1322401 : Blo 618297 1322401 := bstep (se 2 (by rfl) ⟨495900, by rfl⟩ : syracuseStep 1322401 = 991801) B991801
theorem B929273 : Blo 618297 929273 := bstep (se 2 (by rfl) ⟨348477, by rfl⟩ : syracuseStep 929273 = 696955) B696955
theorem B929375 : Blo 618297 929375 := bstep (se 1 (by rfl) ⟨697031, by rfl⟩ : syracuseStep 929375 = 1394063) B1394063
theorem B1322657 : Blo 618297 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B929591 : Blo 618297 929591 := bstep (se 1 (by rfl) ⟨697193, by rfl⟩ : syracuseStep 929591 = 1394387) B1394387
theorem B1486799 : Blo 618297 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B929897 : Blo 618297 929897 := bstep (se 2 (by rfl) ⟨348711, by rfl⟩ : syracuseStep 929897 = 697423) B697423
theorem B2830547 : Blo 618297 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B45363473 : Blo 618297 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B930215 : Blo 618297 930215 := bstep (se 1 (by rfl) ⟨697661, by rfl⟩ : syracuseStep 930215 = 1395323) B1395323
theorem B930299 : Blo 618297 930299 := bstep (se 1 (by rfl) ⟨697724, by rfl⟩ : syracuseStep 930299 = 1395449) B1395449
theorem B930425 : Blo 618297 930425 := bstep (se 2 (by rfl) ⟨348909, by rfl⟩ : syracuseStep 930425 = 697819) B697819
theorem B2830969 : Blo 618297 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B930479 : Blo 618297 930479 := bstep (se 1 (by rfl) ⟨697859, by rfl⟩ : syracuseStep 930479 = 1395719) B1395719
theorem B930527 : Blo 618297 930527 := bstep (se 1 (by rfl) ⟨697895, by rfl⟩ : syracuseStep 930527 = 1395791) B1395791
theorem B7549685 : Blo 618297 7549685 := bstep (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) B707783
theorem B930791 : Blo 618297 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B3781847 : Blo 618297 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B931049 : Blo 618297 931049 := bstep (se 2 (by rfl) ⟨349143, by rfl⟩ : syracuseStep 931049 = 698287) B698287
theorem B931103 : Blo 618297 931103 := bstep (se 1 (by rfl) ⟨698327, by rfl⟩ : syracuseStep 931103 = 1396655) B1396655
theorem B931271 : Blo 618297 931271 := bstep (se 1 (by rfl) ⟨698453, by rfl⟩ : syracuseStep 931271 = 1396907) B1396907
theorem B931625 : Blo 618297 931625 := bstep (se 2 (by rfl) ⟨349359, by rfl⟩ : syracuseStep 931625 = 698719) B698719
theorem B931631 : Blo 618297 931631 := bstep (se 1 (by rfl) ⟨698723, by rfl⟩ : syracuseStep 931631 = 1397447) B1397447
theorem B3356801 : Blo 618297 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B932105 : Blo 618297 932105 := bstep (se 2 (by rfl) ⟨349539, by rfl⟩ : syracuseStep 932105 = 699079) B699079
theorem B1489259 : Blo 618297 1489259 := bstep (se 1 (by rfl) ⟨1116944, by rfl⟩ : syracuseStep 1489259 = 2233889) B2233889
theorem B932207 : Blo 618297 932207 := bstep (se 1 (by rfl) ⟨699155, by rfl⟩ : syracuseStep 932207 = 1398311) B1398311
theorem B932423 : Blo 618297 932423 := bstep (se 1 (by rfl) ⟨699317, by rfl⟩ : syracuseStep 932423 = 1398635) B1398635
theorem B1391183 : Blo 618297 1391183 := bstep (se 1 (by rfl) ⟨1043387, by rfl⟩ : syracuseStep 1391183 = 2086775) B2086775
theorem B1882703 : Blo 618297 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B932459 : Blo 618297 932459 := bstep (se 1 (by rfl) ⟨699344, by rfl⟩ : syracuseStep 932459 = 1398689) B1398689
theorem B1391327 : Blo 618297 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B932687 : Blo 618297 932687 := bstep (se 1 (by rfl) ⟨699515, by rfl⟩ : syracuseStep 932687 = 1399031) B1399031
theorem B1489835 : Blo 618297 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B1391579 : Blo 618297 1391579 := bstep (se 1 (by rfl) ⟨1043684, by rfl⟩ : syracuseStep 1391579 = 2087369) B2087369
theorem B3390587 : Blo 618297 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B1326203 : Blo 618297 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B1391759 : Blo 618297 1391759 := bstep (se 1 (by rfl) ⟨1043819, by rfl⟩ : syracuseStep 1391759 = 2087639) B2087639
theorem B3980477 : Blo 618297 3980477 := bstep (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) B1492679
theorem B933083 : Blo 618297 933083 := bstep (se 1 (by rfl) ⟨699812, by rfl⟩ : syracuseStep 933083 = 1399625) B1399625
theorem B1391849 : Blo 618297 1391849 := bstep (se 2 (by rfl) ⟨521943, by rfl⟩ : syracuseStep 1391849 = 1043887) B1043887
theorem B1391903 : Blo 618297 1391903 := bstep (se 1 (by rfl) ⟨1043927, by rfl⟩ : syracuseStep 1391903 = 2087855) B2087855
theorem B1916257 : Blo 618297 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B933257 : Blo 618297 933257 := bstep (se 2 (by rfl) ⟨349971, by rfl⟩ : syracuseStep 933257 = 699943) B699943
theorem B1719713 : Blo 618297 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B3522163 : Blo 618297 3522163 := bstep (se 1 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 3522163 = 5283245) B5283245
theorem B1392425 : Blo 618297 1392425 := bstep (se 2 (by rfl) ⟨522159, by rfl⟩ : syracuseStep 1392425 = 1044319) B1044319
theorem B1491527 : Blo 618297 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B13452101 : Blo 618297 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B1393487 : Blo 618297 1393487 := bstep (se 1 (by rfl) ⟨1045115, by rfl⟩ : syracuseStep 1393487 = 2090231) B2090231
theorem B15287233 : Blo 618297 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B3523621 : Blo 618297 3523621 := bstep (se 4 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 3523621 = 660679) B660679
theorem B1393703 : Blo 618297 1393703 := bstep (se 1 (by rfl) ⟨1045277, by rfl⟩ : syracuseStep 1393703 = 2090555) B2090555
theorem B1393883 : Blo 618297 1393883 := bstep (se 1 (by rfl) ⟨1045412, by rfl⟩ : syracuseStep 1393883 = 2090825) B2090825
theorem B2508193 : Blo 618297 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B1394081 : Blo 618297 1394081 := bstep (se 2 (by rfl) ⟨522780, by rfl⟩ : syracuseStep 1394081 = 1045561) B1045561
theorem B1394639 : Blo 618297 1394639 := bstep (se 1 (by rfl) ⟨1045979, by rfl⟩ : syracuseStep 1394639 = 2091959) B2091959
theorem B4540367 : Blo 618297 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B6703397 : Blo 618297 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1395017 : Blo 618297 1395017 := bstep (se 2 (by rfl) ⟨523131, by rfl⟩ : syracuseStep 1395017 = 1046263) B1046263
theorem B1395035 : Blo 618297 1395035 := bstep (se 1 (by rfl) ⟨1046276, by rfl⟩ : syracuseStep 1395035 = 2092553) B2092553
theorem B2542153 : Blo 618297 2542153 := bstep (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) B1906615
theorem B1395611 : Blo 618297 1395611 := bstep (se 1 (by rfl) ⟨1046708, by rfl⟩ : syracuseStep 1395611 = 2093417) B2093417
theorem B1887131 : Blo 618297 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B3132431 : Blo 618297 3132431 := bstep (se 1 (by rfl) ⟨2349323, by rfl⟩ : syracuseStep 3132431 = 4698647) B4698647
theorem B1494055 : Blo 618297 1494055 := bstep (se 1 (by rfl) ⟨1120541, by rfl⟩ : syracuseStep 1494055 = 2241083) B2241083
theorem B1395809 : Blo 618297 1395809 := bstep (se 2 (by rfl) ⟨523428, by rfl⟩ : syracuseStep 1395809 = 1046857) B1046857
theorem B1985755 : Blo 618297 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B1396007 : Blo 618297 1396007 := bstep (se 1 (by rfl) ⟨1047005, by rfl⟩ : syracuseStep 1396007 = 2094011) B2094011
theorem B1396385 : Blo 618297 1396385 := bstep (se 2 (by rfl) ⟨523644, by rfl⟩ : syracuseStep 1396385 = 1047289) B1047289
theorem B7949987 : Blo 618297 7949987 := bstep (se 1 (by rfl) ⟨5962490, by rfl⟩ : syracuseStep 7949987 = 11924981) B11924981
theorem B3526355 : Blo 618297 3526355 := bstep (se 1 (by rfl) ⟨2644766, by rfl⟩ : syracuseStep 3526355 = 5289533) B5289533
theorem B3133241 : Blo 618297 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B1396745 : Blo 618297 1396745 := bstep (se 2 (by rfl) ⟨523779, by rfl⟩ : syracuseStep 1396745 = 1047559) B1047559
theorem B2117657 : Blo 618297 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B1397159 : Blo 618297 1397159 := bstep (se 1 (by rfl) ⟨1047869, by rfl⟩ : syracuseStep 1397159 = 2095739) B2095739
theorem B1397267 : Blo 618297 1397267 := bstep (se 1 (by rfl) ⟨1047950, by rfl⟩ : syracuseStep 1397267 = 2095901) B2095901
theorem B1397321 : Blo 618297 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B2642615 : Blo 618297 2642615 := bstep (se 1 (by rfl) ⟨1981961, by rfl⟩ : syracuseStep 2642615 = 3963923) B3963923
theorem B1397735 : Blo 618297 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B1398113 : Blo 618297 1398113 := bstep (se 2 (by rfl) ⟨524292, by rfl⟩ : syracuseStep 1398113 = 1048585) B1048585
theorem B38196605 : Blo 618297 38196605 := bstep (se 3 (by rfl) ⟨7161863, by rfl⟩ : syracuseStep 38196605 = 14323727) B14323727
theorem B1398203 : Blo 618297 1398203 := bstep (se 1 (by rfl) ⟨1048652, by rfl⟩ : syracuseStep 1398203 = 2097305) B2097305
theorem B1398329 : Blo 618297 1398329 := bstep (se 2 (by rfl) ⟨524373, by rfl⟩ : syracuseStep 1398329 = 1048747) B1048747
theorem B20633221 : Blo 618297 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B2873017 : Blo 618297 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B5298007 : Blo 618297 5298007 := bstep (se 1 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 5298007 = 7947011) B7947011
theorem B743375 : Blo 618297 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1398995 : Blo 618297 1398995 := bstep (se 1 (by rfl) ⟨1049246, by rfl⟩ : syracuseStep 1398995 = 2098493) B2098493
theorem B1399049 : Blo 618297 1399049 := bstep (se 2 (by rfl) ⟨524643, by rfl⟩ : syracuseStep 1399049 = 1049287) B1049287
theorem B1399265 : Blo 618297 1399265 := bstep (se 2 (by rfl) ⟨524724, by rfl⟩ : syracuseStep 1399265 = 1049449) B1049449
theorem B3135995 : Blo 618297 3135995 := bstep (se 1 (by rfl) ⟨2351996, by rfl⟩ : syracuseStep 3135995 = 4703993) B4703993
theorem B2087531 : Blo 618297 2087531 := bstep (se 1 (by rfl) ⟨1565648, by rfl⟩ : syracuseStep 2087531 = 3131297) B3131297
theorem B10050155 : Blo 618297 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B7527107 : Blo 618297 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1399571 : Blo 618297 1399571 := bstep (se 1 (by rfl) ⟨1049678, by rfl⟩ : syracuseStep 1399571 = 2099357) B2099357
theorem B2972483 : Blo 618297 2972483 := bstep (se 1 (by rfl) ⟨2229362, by rfl⟩ : syracuseStep 2972483 = 4458725) B4458725
theorem B8706935 : Blo 618297 8706935 := bstep (se 1 (by rfl) ⟨6530201, by rfl⟩ : syracuseStep 8706935 = 13060403) B13060403
theorem B1399931 : Blo 618297 1399931 := bstep (se 1 (by rfl) ⟨1049948, by rfl⟩ : syracuseStep 1399931 = 2099897) B2099897
theorem B2088125 : Blo 618297 2088125 := bstep (se 3 (by rfl) ⟨391523, by rfl⟩ : syracuseStep 2088125 = 783047) B783047
theorem B1400057 : Blo 618297 1400057 := bstep (se 2 (by rfl) ⟨525021, by rfl⟩ : syracuseStep 1400057 = 1050043) B1050043
theorem B2350403 : Blo 618297 2350403 := bstep (se 1 (by rfl) ⟨1762802, by rfl⟩ : syracuseStep 2350403 = 3525605) B3525605
theorem B3136967 : Blo 618297 3136967 := bstep (se 1 (by rfl) ⟨2352725, by rfl⟩ : syracuseStep 3136967 = 4705451) B4705451
theorem B3137291 : Blo 618297 3137291 := bstep (se 1 (by rfl) ⟨2352968, by rfl⟩ : syracuseStep 3137291 = 4705937) B4705937
theorem B2350889 : Blo 618297 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B21520247 : Blo 618297 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B1565153 : Blo 618297 1565153 := bstep (se 2 (by rfl) ⟨586932, by rfl⟩ : syracuseStep 1565153 = 1173865) B1173865
theorem B1565203 : Blo 618297 1565203 := bstep (se 1 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 1565203 = 2347805) B2347805
theorem B746167 : Blo 618297 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B3138263 : Blo 618297 3138263 := bstep (se 1 (by rfl) ⟨2353697, by rfl⟩ : syracuseStep 3138263 = 4707395) B4707395
theorem B128803861 : Blo 618297 128803861 := bstep (se 6 (by rfl) ⟨3018840, by rfl⟩ : syracuseStep 128803861 = 6037681) B6037681
theorem B1991879 : Blo 618297 1991879 := bstep (se 1 (by rfl) ⟨1493909, by rfl⟩ : syracuseStep 1991879 = 2987819) B2987819
theorem B2352361 : Blo 618297 2352361 := bstep (se 2 (by rfl) ⟨882135, by rfl⟩ : syracuseStep 2352361 = 1764271) B1764271
theorem B5956841 : Blo 618297 5956841 := bstep (se 2 (by rfl) ⟨2233815, by rfl⟩ : syracuseStep 5956841 = 4467631) B4467631
theorem B3138911 : Blo 618297 3138911 := bstep (se 1 (by rfl) ⟨2354183, by rfl⟩ : syracuseStep 3138911 = 4708367) B4708367
theorem B2091041 : Blo 618297 2091041 := bstep (se 2 (by rfl) ⟨784140, by rfl⟩ : syracuseStep 2091041 = 1568281) B1568281
theorem B23816429 : Blo 618297 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B1566985 : Blo 618297 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B4712741 : Blo 618297 4712741 := bstep (se 4 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 4712741 = 883639) B883639
theorem B944551 : Blo 618297 944551 := bstep (se 1 (by rfl) ⟨708413, by rfl⟩ : syracuseStep 944551 = 1416827) B1416827
theorem B2976173 : Blo 618297 2976173 := bstep (se 3 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 2976173 = 1116065) B1116065
theorem B22932013 : Blo 618297 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B10611323 : Blo 618297 10611323 := bstep (se 1 (by rfl) ⟨7958492, by rfl⟩ : syracuseStep 10611323 = 15916985) B15916985
theorem B1174351 : Blo 618297 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B2649277 : Blo 618297 2649277 := bstep (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) B993479
theorem B40267043 : Blo 618297 40267043 := bstep (se 1 (by rfl) ⟨30200282, by rfl⟩ : syracuseStep 40267043 = 60400565) B60400565
theorem B3141179 : Blo 618297 3141179 := bstep (se 1 (by rfl) ⟨2355884, by rfl⟩ : syracuseStep 3141179 = 4711769) B4711769
theorem B1568443 : Blo 618297 1568443 := bstep (se 1 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 1568443 = 2352665) B2352665
theorem B1044265 : Blo 618297 1044265 := bstep (se 2 (by rfl) ⟨391599, by rfl⟩ : syracuseStep 1044265 = 783199) B783199
theorem B618395 : Blo 618297 618395 := bstep (se 1 (by rfl) ⟨463796, by rfl⟩ : syracuseStep 618395 = 927593) B927593
theorem B618447 : Blo 618297 618447 := bstep (se 1 (by rfl) ⟨463835, by rfl⟩ : syracuseStep 618447 = 927671) B927671
theorem B618471 : Blo 618297 618471 := bstep (se 1 (by rfl) ⟨463853, by rfl⟩ : syracuseStep 618471 = 927707) B927707
theorem B11923523 : Blo 618297 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B618783 : Blo 618297 618783 := bstep (se 1 (by rfl) ⟨464087, by rfl⟩ : syracuseStep 618783 = 928175) B928175
theorem B618843 : Blo 618297 618843 := bstep (se 1 (by rfl) ⟨464132, by rfl⟩ : syracuseStep 618843 = 928265) B928265
theorem B618863 : Blo 618297 618863 := bstep (se 1 (by rfl) ⟨464147, by rfl⟩ : syracuseStep 618863 = 928295) B928295
theorem B618919 : Blo 618297 618919 := bstep (se 1 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 618919 = 928379) B928379
theorem B619003 : Blo 618297 619003 := bstep (se 1 (by rfl) ⟨464252, by rfl⟩ : syracuseStep 619003 = 928505) B928505
theorem B1176059 : Blo 618297 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B619071 : Blo 618297 619071 := bstep (se 1 (by rfl) ⟨464303, by rfl⟩ : syracuseStep 619071 = 928607) B928607
theorem B1045055 : Blo 618297 1045055 := bstep (se 1 (by rfl) ⟨783791, by rfl⟩ : syracuseStep 1045055 = 1567583) B1567583
theorem B619079 : Blo 618297 619079 := bstep (se 1 (by rfl) ⟨464309, by rfl⟩ : syracuseStep 619079 = 928619) B928619
theorem B1340011 : Blo 618297 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B881327 : Blo 618297 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B3535559 : Blo 618297 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B619231 : Blo 618297 619231 := bstep (se 1 (by rfl) ⟨464423, by rfl⟩ : syracuseStep 619231 = 928847) B928847
theorem B1569527 : Blo 618297 1569527 := bstep (se 1 (by rfl) ⟨1177145, by rfl⟩ : syracuseStep 1569527 = 2354291) B2354291
theorem B619311 : Blo 618297 619311 := bstep (se 1 (by rfl) ⟨464483, by rfl⟩ : syracuseStep 619311 = 928967) B928967
theorem B2093903 : Blo 618297 2093903 := bstep (se 1 (by rfl) ⟨1570427, by rfl⟩ : syracuseStep 2093903 = 3140855) B3140855
theorem B619419 : Blo 618297 619419 := bstep (se 1 (by rfl) ⟨464564, by rfl⟩ : syracuseStep 619419 = 929129) B929129
theorem B619471 : Blo 618297 619471 := bstep (se 1 (by rfl) ⟨464603, by rfl⟩ : syracuseStep 619471 = 929207) B929207
theorem B619495 : Blo 618297 619495 := bstep (se 1 (by rfl) ⟨464621, by rfl⟩ : syracuseStep 619495 = 929243) B929243
theorem B3142799 : Blo 618297 3142799 := bstep (se 1 (by rfl) ⟨2357099, by rfl⟩ : syracuseStep 3142799 = 4714199) B4714199
theorem B2094227 : Blo 618297 2094227 := bstep (se 1 (by rfl) ⟨1570670, by rfl⟩ : syracuseStep 2094227 = 3141341) B3141341
theorem B1045723 : Blo 618297 1045723 := bstep (se 1 (by rfl) ⟨784292, by rfl⟩ : syracuseStep 1045723 = 1568585) B1568585
theorem B619807 : Blo 618297 619807 := bstep (se 1 (by rfl) ⟨464855, by rfl⟩ : syracuseStep 619807 = 929711) B929711
theorem B2356523 : Blo 618297 2356523 := bstep (se 1 (by rfl) ⟨1767392, by rfl⟩ : syracuseStep 2356523 = 3534785) B3534785
theorem B619867 : Blo 618297 619867 := bstep (se 1 (by rfl) ⟨464900, by rfl⟩ : syracuseStep 619867 = 929801) B929801
theorem B619887 : Blo 618297 619887 := bstep (se 1 (by rfl) ⟨464915, by rfl⟩ : syracuseStep 619887 = 929831) B929831
theorem B2094497 : Blo 618297 2094497 := bstep (se 2 (by rfl) ⟨785436, by rfl⟩ : syracuseStep 2094497 = 1570873) B1570873
theorem B619943 : Blo 618297 619943 := bstep (se 1 (by rfl) ⟨464957, by rfl⟩ : syracuseStep 619943 = 929915) B929915
theorem B1177031 : Blo 618297 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B620027 : Blo 618297 620027 := bstep (se 1 (by rfl) ⟨465020, by rfl⟩ : syracuseStep 620027 = 930041) B930041
theorem B620095 : Blo 618297 620095 := bstep (se 1 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 620095 = 930143) B930143
theorem B620103 : Blo 618297 620103 := bstep (se 1 (by rfl) ⟨465077, by rfl⟩ : syracuseStep 620103 = 930155) B930155
theorem B1570387 : Blo 618297 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B1177183 : Blo 618297 1177183 := bstep (se 1 (by rfl) ⟨882887, by rfl⟩ : syracuseStep 1177183 = 1765775) B1765775
theorem B6059659 : Blo 618297 6059659 := bstep (se 1 (by rfl) ⟨4544744, by rfl⟩ : syracuseStep 6059659 = 9089489) B9089489
theorem B620255 : Blo 618297 620255 := bstep (se 1 (by rfl) ⟨465191, by rfl⟩ : syracuseStep 620255 = 930383) B930383
theorem B620335 : Blo 618297 620335 := bstep (se 1 (by rfl) ⟨465251, by rfl⟩ : syracuseStep 620335 = 930503) B930503
theorem B7141175 : Blo 618297 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B620443 : Blo 618297 620443 := bstep (se 1 (by rfl) ⟨465332, by rfl⟩ : syracuseStep 620443 = 930665) B930665
theorem B7927739 : Blo 618297 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B1046479 : Blo 618297 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B620495 : Blo 618297 620495 := bstep (se 1 (by rfl) ⟨465371, by rfl⟩ : syracuseStep 620495 = 930743) B930743
theorem B620519 : Blo 618297 620519 := bstep (se 1 (by rfl) ⟨465389, by rfl⟩ : syracuseStep 620519 = 930779) B930779
theorem B3143933 : Blo 618297 3143933 := bstep (se 3 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 3143933 = 1178975) B1178975
theorem B1767689 : Blo 618297 1767689 := bstep (se 2 (by rfl) ⟨662883, by rfl⟩ : syracuseStep 1767689 = 1325767) B1325767
theorem B620831 : Blo 618297 620831 := bstep (se 1 (by rfl) ⟨465623, by rfl⟩ : syracuseStep 620831 = 931247) B931247
theorem B620891 : Blo 618297 620891 := bstep (se 1 (by rfl) ⟨465668, by rfl⟩ : syracuseStep 620891 = 931337) B931337
theorem B620911 : Blo 618297 620911 := bstep (se 1 (by rfl) ⟨465683, by rfl⟩ : syracuseStep 620911 = 931367) B931367
theorem B620967 : Blo 618297 620967 := bstep (se 1 (by rfl) ⟨465725, by rfl⟩ : syracuseStep 620967 = 931451) B931451
theorem B621051 : Blo 618297 621051 := bstep (se 1 (by rfl) ⟨465788, by rfl⟩ : syracuseStep 621051 = 931577) B931577
theorem B621119 : Blo 618297 621119 := bstep (se 1 (by rfl) ⟨465839, by rfl⟩ : syracuseStep 621119 = 931679) B931679
theorem B621127 : Blo 618297 621127 := bstep (se 1 (by rfl) ⟨465845, by rfl⟩ : syracuseStep 621127 = 931691) B931691
theorem B784991 : Blo 618297 784991 := bstep (se 1 (by rfl) ⟨588743, by rfl⟩ : syracuseStep 784991 = 1177487) B1177487
theorem B1047161 : Blo 618297 1047161 := bstep (se 2 (by rfl) ⟨392685, by rfl⟩ : syracuseStep 1047161 = 785371) B785371
theorem B1047215 : Blo 618297 1047215 := bstep (se 1 (by rfl) ⟨785411, by rfl⟩ : syracuseStep 1047215 = 1570823) B1570823
theorem B883423 : Blo 618297 883423 := bstep (se 1 (by rfl) ⟨662567, by rfl⟩ : syracuseStep 883423 = 1325135) B1325135
theorem B621279 : Blo 618297 621279 := bstep (se 1 (by rfl) ⟨465959, by rfl⟩ : syracuseStep 621279 = 931919) B931919
theorem B2980631 : Blo 618297 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B621359 : Blo 618297 621359 := bstep (se 1 (by rfl) ⟨466019, by rfl⟩ : syracuseStep 621359 = 932039) B932039
theorem B1571663 : Blo 618297 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B10615697 : Blo 618297 10615697 := bstep (se 2 (by rfl) ⟨3980886, by rfl⟩ : syracuseStep 10615697 = 7961773) B7961773
theorem B1047451 : Blo 618297 1047451 := bstep (se 1 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 1047451 = 1571177) B1571177
theorem B621467 : Blo 618297 621467 := bstep (se 1 (by rfl) ⟨466100, by rfl⟩ : syracuseStep 621467 = 932201) B932201
theorem B621519 : Blo 618297 621519 := bstep (se 1 (by rfl) ⟨466139, by rfl⟩ : syracuseStep 621519 = 932279) B932279
theorem B621543 : Blo 618297 621543 := bstep (se 1 (by rfl) ⟨466157, by rfl⟩ : syracuseStep 621543 = 932315) B932315
theorem B3144743 : Blo 618297 3144743 := bstep (se 1 (by rfl) ⟨2358557, by rfl⟩ : syracuseStep 3144743 = 4717115) B4717115
theorem B785695 : Blo 618297 785695 := bstep (se 1 (by rfl) ⟨589271, by rfl⟩ : syracuseStep 785695 = 1178543) B1178543
theorem B621855 : Blo 618297 621855 := bstep (se 1 (by rfl) ⟨466391, by rfl⟩ : syracuseStep 621855 = 932783) B932783
theorem B621915 : Blo 618297 621915 := bstep (se 1 (by rfl) ⟨466436, by rfl⟩ : syracuseStep 621915 = 932873) B932873
theorem B621935 : Blo 618297 621935 := bstep (se 1 (by rfl) ⟨466451, by rfl⟩ : syracuseStep 621935 = 932903) B932903
theorem B2358665 : Blo 618297 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B621991 : Blo 618297 621991 := bstep (se 1 (by rfl) ⟨466493, by rfl⟩ : syracuseStep 621991 = 932987) B932987
theorem B1572311 : Blo 618297 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B622075 : Blo 618297 622075 := bstep (se 1 (by rfl) ⟨466556, by rfl⟩ : syracuseStep 622075 = 933113) B933113
theorem B2653721 : Blo 618297 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B622143 : Blo 618297 622143 := bstep (se 1 (by rfl) ⟨466607, by rfl⟩ : syracuseStep 622143 = 933215) B933215
theorem B622151 : Blo 618297 622151 := bstep (se 1 (by rfl) ⟨466613, by rfl⟩ : syracuseStep 622151 = 933227) B933227
theorem B13631093 : Blo 618297 13631093 := bstep (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) B1277915
theorem B1572655 : Blo 618297 1572655 := bstep (se 1 (by rfl) ⟨1179491, by rfl⟩ : syracuseStep 1572655 = 2358983) B2358983
theorem B1769273 : Blo 618297 1769273 := bstep (se 2 (by rfl) ⟨663477, by rfl⟩ : syracuseStep 1769273 = 1326955) B1326955
theorem B7241567 : Blo 618297 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B884687 : Blo 618297 884687 := bstep (se 1 (by rfl) ⟨663515, by rfl⟩ : syracuseStep 884687 = 1327031) B1327031
theorem B7536797 : Blo 618297 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B1180001 : Blo 618297 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B2097737 : Blo 618297 2097737 := bstep (se 2 (by rfl) ⟨786651, by rfl⟩ : syracuseStep 2097737 = 1573303) B1573303
theorem B2097899 : Blo 618297 2097899 := bstep (se 1 (by rfl) ⟨1573424, by rfl⟩ : syracuseStep 2097899 = 3146849) B3146849
theorem B4719545 : Blo 618297 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B2229203 : Blo 618297 2229203 := bstep (se 1 (by rfl) ⟨1671902, by rfl⟩ : syracuseStep 2229203 = 3343805) B3343805
theorem B1049807 : Blo 618297 1049807 := bstep (se 1 (by rfl) ⟨787355, by rfl⟩ : syracuseStep 1049807 = 1574711) B1574711
theorem B20382977 : Blo 618297 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B3147011 : Blo 618297 3147011 := bstep (se 1 (by rfl) ⟨2360258, by rfl⟩ : syracuseStep 3147011 = 4720517) B4720517
theorem B171738481 : Blo 618297 171738481 := bstep (se 2 (by rfl) ⟨64401930, by rfl⟩ : syracuseStep 171738481 = 128803861) B128803861
theorem B1770923 : Blo 618297 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B2360927 : Blo 618297 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B3344257 : Blo 618297 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B7178129 : Blo 618297 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B3540935 : Blo 618297 3540935 := bstep (se 1 (by rfl) ⟨2655701, by rfl⟩ : syracuseStep 3540935 = 5311403) B5311403
theorem B1574903 : Blo 618297 1574903 := bstep (se 1 (by rfl) ⟨1181177, by rfl⟩ : syracuseStep 1574903 = 2362355) B2362355
theorem B2099411 : Blo 618297 2099411 := bstep (se 1 (by rfl) ⟨1574558, by rfl⟩ : syracuseStep 2099411 = 3149117) B3149117
theorem B1771915 : Blo 618297 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B2099681 : Blo 618297 2099681 := bstep (se 2 (by rfl) ⟨787380, by rfl⟩ : syracuseStep 2099681 = 1574761) B1574761
theorem B1772063 : Blo 618297 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B3541643 : Blo 618297 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B1411771 : Blo 618297 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B3148631 : Blo 618297 3148631 := bstep (se 1 (by rfl) ⟨2361473, by rfl⟩ : syracuseStep 3148631 = 4722947) B4722947
theorem B2362567 : Blo 618297 2362567 := bstep (se 1 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 2362567 = 3543851) B3543851
theorem B30576017 : Blo 618297 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B25464403 : Blo 618297 25464403 := bstep (se 1 (by rfl) ⟨19098302, by rfl⟩ : syracuseStep 25464403 = 38196605) B38196605
theorem B5968255 : Blo 618297 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B5804623 : Blo 618297 5804623 := bstep (se 1 (by rfl) ⟨4353467, by rfl⟩ : syracuseStep 5804623 = 8706935) B8706935
theorem B3347675 : Blo 618297 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B10589453 : Blo 618297 10589453 := bstep (se 3 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 10589453 = 3971045) B3971045
theorem B3971227 : Blo 618297 3971227 := bstep (se 1 (by rfl) ⟨2978420, by rfl⟩ : syracuseStep 3971227 = 5956841) B5956841
theorem B661807 : Blo 618297 661807 := bstep (se 1 (by rfl) ⟨496355, by rfl⟩ : syracuseStep 661807 = 992711) B992711
theorem B5020541 : Blo 618297 5020541 := bstep (se 3 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 5020541 = 1882703) B1882703
theorem B26844695 : Blo 618297 26844695 := bstep (se 1 (by rfl) ⟨20133521, by rfl⟩ : syracuseStep 26844695 = 40267043) B40267043
theorem B991199 : Blo 618297 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B696703 : Blo 618297 696703 := bstep (se 1 (by rfl) ⟨522527, by rfl⟩ : syracuseStep 696703 = 1045055) B1045055
theorem B4760783 : Blo 618297 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B7087337 : Blo 618297 7087337 := bstep (se 2 (by rfl) ⟨2657751, by rfl⟩ : syracuseStep 7087337 = 5315503) B5315503
theorem B5285159 : Blo 618297 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B2237867 : Blo 618297 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B992839 : Blo 618297 992839 := bstep (se 1 (by rfl) ⟨744629, by rfl⟩ : syracuseStep 992839 = 1489259) B1489259
theorem B927455 : Blo 618297 927455 := bstep (se 1 (by rfl) ⟨695591, by rfl⟩ : syracuseStep 927455 = 1391183) B1391183
theorem B698107 : Blo 618297 698107 := bstep (se 1 (by rfl) ⟨523580, by rfl⟩ : syracuseStep 698107 = 1047161) B1047161
theorem B698143 : Blo 618297 698143 := bstep (se 1 (by rfl) ⟨523607, by rfl⟩ : syracuseStep 698143 = 1047215) B1047215
theorem B927551 : Blo 618297 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B993223 : Blo 618297 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B927719 : Blo 618297 927719 := bstep (se 1 (by rfl) ⟨695789, by rfl⟩ : syracuseStep 927719 = 1391579) B1391579
theorem B927737 : Blo 618297 927737 := bstep (se 2 (by rfl) ⟨347901, by rfl⟩ : syracuseStep 927737 = 695803) B695803
theorem B927839 : Blo 618297 927839 := bstep (se 1 (by rfl) ⟨695879, by rfl⟩ : syracuseStep 927839 = 1391759) B1391759
theorem B4696217 : Blo 618297 4696217 := bstep (se 2 (by rfl) ⟨1761081, by rfl⟩ : syracuseStep 4696217 = 3522163) B3522163
theorem B927899 : Blo 618297 927899 := bstep (se 1 (by rfl) ⟨695924, by rfl⟩ : syracuseStep 927899 = 1391849) B1391849
theorem B927935 : Blo 618297 927935 := bstep (se 1 (by rfl) ⟨695951, by rfl⟩ : syracuseStep 927935 = 1391903) B1391903
theorem B927977 : Blo 618297 927977 := bstep (se 2 (by rfl) ⟨347991, by rfl⟩ : syracuseStep 927977 = 695983) B695983
theorem B19310845 : Blo 618297 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B57387325 : Blo 618297 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B9087395 : Blo 618297 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B928283 : Blo 618297 928283 := bstep (se 1 (by rfl) ⟨696212, by rfl⟩ : syracuseStep 928283 = 1392425) B1392425
theorem B928361 : Blo 618297 928361 := bstep (se 2 (by rfl) ⟨348135, by rfl⟩ : syracuseStep 928361 = 696271) B696271
theorem B699295 : Blo 618297 699295 := bstep (se 1 (by rfl) ⟨524471, by rfl⟩ : syracuseStep 699295 = 1048943) B1048943
theorem B994351 : Blo 618297 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B699439 : Blo 618297 699439 := bstep (se 1 (by rfl) ⟨524579, by rfl⟩ : syracuseStep 699439 = 1049159) B1049159
theorem B928889 : Blo 618297 928889 := bstep (se 2 (by rfl) ⟨348333, by rfl⟩ : syracuseStep 928889 = 696667) B696667
theorem B928991 : Blo 618297 928991 := bstep (se 1 (by rfl) ⟨696743, by rfl⟩ : syracuseStep 928991 = 1393487) B1393487
theorem B929033 : Blo 618297 929033 := bstep (se 2 (by rfl) ⟨348387, by rfl⟩ : syracuseStep 929033 = 696775) B696775
theorem B699727 : Blo 618297 699727 := bstep (se 1 (by rfl) ⟨524795, by rfl⟩ : syracuseStep 699727 = 1049591) B1049591
theorem B929135 : Blo 618297 929135 := bstep (se 1 (by rfl) ⟨696851, by rfl⟩ : syracuseStep 929135 = 1393703) B1393703
theorem B929255 : Blo 618297 929255 := bstep (se 1 (by rfl) ⟨696941, by rfl⟩ : syracuseStep 929255 = 1393883) B1393883
theorem B994889 : Blo 618297 994889 := bstep (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) B746167
theorem B929387 : Blo 618297 929387 := bstep (se 1 (by rfl) ⟨697040, by rfl⟩ : syracuseStep 929387 = 1394081) B1394081
theorem B929513 : Blo 618297 929513 := bstep (se 2 (by rfl) ⟨348567, by rfl⟩ : syracuseStep 929513 = 697135) B697135
theorem B929657 : Blo 618297 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B5025665 : Blo 618297 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B3026911 : Blo 618297 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B929759 : Blo 618297 929759 := bstep (se 1 (by rfl) ⟨697319, by rfl⟩ : syracuseStep 929759 = 1394639) B1394639
theorem B4698161 : Blo 618297 4698161 := bstep (se 2 (by rfl) ⟨1761810, by rfl⟩ : syracuseStep 4698161 = 3523621) B3523621
theorem B4468931 : Blo 618297 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B930011 : Blo 618297 930011 := bstep (se 1 (by rfl) ⟨697508, by rfl⟩ : syracuseStep 930011 = 1395017) B1395017
theorem B930023 : Blo 618297 930023 := bstep (se 1 (by rfl) ⟨697517, by rfl⟩ : syracuseStep 930023 = 1395035) B1395035
theorem B930185 : Blo 618297 930185 := bstep (se 2 (by rfl) ⟨348819, by rfl⟩ : syracuseStep 930185 = 697639) B697639
theorem B930281 : Blo 618297 930281 := bstep (se 2 (by rfl) ⟨348855, by rfl⟩ : syracuseStep 930281 = 697711) B697711
theorem B930407 : Blo 618297 930407 := bstep (se 1 (by rfl) ⟨697805, by rfl⟩ : syracuseStep 930407 = 1395611) B1395611
theorem B1258087 : Blo 618297 1258087 := bstep (se 1 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 1258087 = 1887131) B1887131
theorem B930539 : Blo 618297 930539 := bstep (se 1 (by rfl) ⟨697904, by rfl⟩ : syracuseStep 930539 = 1395809) B1395809
theorem B930569 : Blo 618297 930569 := bstep (se 2 (by rfl) ⟨348963, by rfl⟩ : syracuseStep 930569 = 697927) B697927
theorem B3978017 : Blo 618297 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B930671 : Blo 618297 930671 := bstep (se 1 (by rfl) ⟨698003, by rfl⟩ : syracuseStep 930671 = 1396007) B1396007
theorem B1356907 : Blo 618297 1356907 := bstep (se 1 (by rfl) ⟨1017680, by rfl⟩ : syracuseStep 1356907 = 2035361) B2035361
theorem B930923 : Blo 618297 930923 := bstep (se 1 (by rfl) ⟨698192, by rfl⟩ : syracuseStep 930923 = 1396385) B1396385
theorem B931163 : Blo 618297 931163 := bstep (se 1 (by rfl) ⟨698372, by rfl⟩ : syracuseStep 931163 = 1396745) B1396745
theorem B931439 : Blo 618297 931439 := bstep (se 1 (by rfl) ⟨698579, by rfl⟩ : syracuseStep 931439 = 1397159) B1397159
theorem B931511 : Blo 618297 931511 := bstep (se 1 (by rfl) ⟨698633, by rfl⟩ : syracuseStep 931511 = 1397267) B1397267
theorem B931547 : Blo 618297 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B3979145 : Blo 618297 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B931721 : Blo 618297 931721 := bstep (se 2 (by rfl) ⟨349395, by rfl⟩ : syracuseStep 931721 = 698791) B698791
theorem B1259401 : Blo 618297 1259401 := bstep (se 2 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 1259401 = 944551) B944551
theorem B931823 : Blo 618297 931823 := bstep (se 1 (by rfl) ⟨698867, by rfl⟩ : syracuseStep 931823 = 1397735) B1397735
theorem B3389537 : Blo 618297 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B932075 : Blo 618297 932075 := bstep (se 1 (by rfl) ⟨699056, by rfl⟩ : syracuseStep 932075 = 1398113) B1398113
theorem B932135 : Blo 618297 932135 := bstep (se 1 (by rfl) ⟨699101, by rfl⟩ : syracuseStep 932135 = 1398203) B1398203
theorem B932219 : Blo 618297 932219 := bstep (se 1 (by rfl) ⟨699164, by rfl⟩ : syracuseStep 932219 = 1398329) B1398329
theorem B932489 : Blo 618297 932489 := bstep (se 2 (by rfl) ⟨349683, by rfl⟩ : syracuseStep 932489 = 699367) B699367
theorem B932663 : Blo 618297 932663 := bstep (se 1 (by rfl) ⟨699497, by rfl⟩ : syracuseStep 932663 = 1398995) B1398995
theorem B932699 : Blo 618297 932699 := bstep (se 1 (by rfl) ⟨699524, by rfl⟩ : syracuseStep 932699 = 1399049) B1399049
theorem B932843 : Blo 618297 932843 := bstep (se 1 (by rfl) ⟨699632, by rfl⟩ : syracuseStep 932843 = 1399265) B1399265
theorem B1391687 : Blo 618297 1391687 := bstep (se 1 (by rfl) ⟨1043765, by rfl⟩ : syracuseStep 1391687 = 2087531) B2087531
theorem B6700103 : Blo 618297 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B933047 : Blo 618297 933047 := bstep (se 1 (by rfl) ⟨699785, by rfl⟩ : syracuseStep 933047 = 1399571) B1399571
theorem B1981655 : Blo 618297 1981655 := bstep (se 1 (by rfl) ⟨1486241, by rfl⟩ : syracuseStep 1981655 = 2972483) B2972483
theorem B933287 : Blo 618297 933287 := bstep (se 1 (by rfl) ⟨699965, by rfl⟩ : syracuseStep 933287 = 1399931) B1399931
theorem B1392083 : Blo 618297 1392083 := bstep (se 1 (by rfl) ⟨1044062, by rfl⟩ : syracuseStep 1392083 = 2088125) B2088125
theorem B933371 : Blo 618297 933371 := bstep (se 1 (by rfl) ⟨700028, by rfl⟩ : syracuseStep 933371 = 1400057) B1400057
theorem B1392353 : Blo 618297 1392353 := bstep (se 2 (by rfl) ⟨522132, by rfl⟩ : syracuseStep 1392353 = 1044265) B1044265
theorem B1982333 : Blo 618297 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B3784573 : Blo 618297 3784573 := bstep (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) B1419215
theorem B1327919 : Blo 618297 1327919 := bstep (se 1 (by rfl) ⟨995939, by rfl⟩ : syracuseStep 1327919 = 1991879) B1991879
theorem B1786681 : Blo 618297 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B1394027 : Blo 618297 1394027 := bstep (se 1 (by rfl) ⟨1045520, by rfl⟩ : syracuseStep 1394027 = 2091041) B2091041
theorem B15877619 : Blo 618297 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B706159 : Blo 618297 706159 := bstep (se 1 (by rfl) ⟨529619, by rfl⟩ : syracuseStep 706159 = 1059239) B1059239
theorem B1984115 : Blo 618297 1984115 := bstep (se 1 (by rfl) ⟨1488086, by rfl⟩ : syracuseStep 1984115 = 2976173) B2976173
theorem B1394297 : Blo 618297 1394297 := bstep (se 2 (by rfl) ⟨522861, by rfl⟩ : syracuseStep 1394297 = 1045723) B1045723
theorem B20072285 : Blo 618297 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B27510961 : Blo 618297 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B8079545 : Blo 618297 8079545 := bstep (se 2 (by rfl) ⟨3029829, by rfl⟩ : syracuseStep 8079545 = 6059659) B6059659
theorem B7064009 : Blo 618297 7064009 := bstep (se 2 (by rfl) ⟨2649003, by rfl⟩ : syracuseStep 7064009 = 5298007) B5298007
theorem B3590729 : Blo 618297 3590729 := bstep (se 2 (by rfl) ⟨1346523, by rfl⟩ : syracuseStep 3590729 = 2693047) B2693047
theorem B1395305 : Blo 618297 1395305 := bstep (se 2 (by rfl) ⟨523239, by rfl⟩ : syracuseStep 1395305 = 1046479) B1046479
theorem B7949015 : Blo 618297 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B1887031 : Blo 618297 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B5033123 : Blo 618297 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B1395935 : Blo 618297 1395935 := bstep (se 1 (by rfl) ⟨1046951, by rfl⟩ : syracuseStep 1395935 = 2093903) B2093903
theorem B1396151 : Blo 618297 1396151 := bstep (se 1 (by rfl) ⟨1047113, by rfl⟩ : syracuseStep 1396151 = 2094227) B2094227
theorem B1396331 : Blo 618297 1396331 := bstep (se 1 (by rfl) ⟨1047248, by rfl⟩ : syracuseStep 1396331 = 2094497) B2094497
theorem B1396601 : Blo 618297 1396601 := bstep (se 2 (by rfl) ⟨523725, by rfl⟩ : syracuseStep 1396601 = 1047451) B1047451
theorem B1987087 : Blo 618297 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B1136027 : Blo 618297 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B6706675 : Blo 618297 6706675 := bstep (se 1 (by rfl) ⟨5030006, by rfl⟩ : syracuseStep 6706675 = 10060013) B10060013
theorem B1398455 : Blo 618297 1398455 := bstep (se 1 (by rfl) ⟨1048841, by rfl⟩ : syracuseStep 1398455 = 2097683) B2097683
theorem B8968067 : Blo 618297 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B2086937 : Blo 618297 2086937 := bstep (se 2 (by rfl) ⟨782601, by rfl⟩ : syracuseStep 2086937 = 1565203) B1565203
theorem B2971673 : Blo 618297 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B8149355 : Blo 618297 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B4479421 : Blo 618297 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B3136157 : Blo 618297 3136157 := bstep (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) B1176059
theorem B4021073 : Blo 618297 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B1399643 : Blo 618297 1399643 := bstep (se 1 (by rfl) ⟨1049732, by rfl⟩ : syracuseStep 1399643 = 2099465) B2099465
theorem B3136481 : Blo 618297 3136481 := bstep (se 2 (by rfl) ⟨1176180, by rfl⟩ : syracuseStep 3136481 = 2352361) B2352361
theorem B2644973 : Blo 618297 2644973 := bstep (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) B991865
theorem B15293555 : Blo 618297 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B2350205 : Blo 618297 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B2088287 : Blo 618297 2088287 := bstep (se 1 (by rfl) ⟨1566215, by rfl⟩ : syracuseStep 2088287 = 3132431) B3132431
theorem B1989983 : Blo 618297 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B5299991 : Blo 618297 5299991 := bstep (se 1 (by rfl) ⟨3974993, by rfl⟩ : syracuseStep 5299991 = 7949987) B7949987
theorem B2350903 : Blo 618297 2350903 := bstep (se 1 (by rfl) ⟨1763177, by rfl⟩ : syracuseStep 2350903 = 3526355) B3526355
theorem B2088827 : Blo 618297 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B2089313 : Blo 618297 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B2646391 : Blo 618297 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B1794487 : Blo 618297 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B1761743 : Blo 618297 1761743 := bstep (se 1 (by rfl) ⟨1321307, by rfl⟩ : syracuseStep 1761743 = 2642615) B2642615
theorem B10084925 : Blo 618297 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B7168621 : Blo 618297 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B15098501 : Blo 618297 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B1073899 : Blo 618297 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B1565801 : Blo 618297 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B1991803 : Blo 618297 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B3138749 : Blo 618297 3138749 := bstep (se 3 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 3138749 = 1177031) B1177031
theorem B1992073 : Blo 618297 1992073 := bstep (se 2 (by rfl) ⟨747027, by rfl⟩ : syracuseStep 1992073 = 1494055) B1494055
theorem B1762813 : Blo 618297 1762813 := bstep (se 3 (by rfl) ⟨330527, by rfl⟩ : syracuseStep 1762813 = 661055) B661055
theorem B943687 : Blo 618297 943687 := bstep (se 1 (by rfl) ⟨707765, by rfl⟩ : syracuseStep 943687 = 1415531) B1415531
theorem B3532369 : Blo 618297 3532369 := bstep (se 2 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 3532369 = 2649277) B2649277
theorem B2647673 : Blo 618297 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B2090663 : Blo 618297 2090663 := bstep (se 1 (by rfl) ⟨1567997, by rfl⟩ : syracuseStep 2090663 = 3135995) B3135995
theorem B1763201 : Blo 618297 1763201 := bstep (se 2 (by rfl) ⟨661200, by rfl⟩ : syracuseStep 1763201 = 1322401) B1322401
theorem B1566935 : Blo 618297 1566935 := bstep (se 1 (by rfl) ⟨1175201, by rfl⟩ : syracuseStep 1566935 = 2350403) B2350403
theorem B2091257 : Blo 618297 2091257 := bstep (se 2 (by rfl) ⟨784221, by rfl⟩ : syracuseStep 2091257 = 1568443) B1568443
theorem B2091311 : Blo 618297 2091311 := bstep (se 1 (by rfl) ⟨1568483, by rfl⟩ : syracuseStep 2091311 = 3136967) B3136967
theorem B1993007 : Blo 618297 1993007 := bstep (se 1 (by rfl) ⟨1494755, by rfl⟩ : syracuseStep 1993007 = 2989511) B2989511
theorem B2091527 : Blo 618297 2091527 := bstep (se 1 (by rfl) ⟨1568645, by rfl⟩ : syracuseStep 2091527 = 3137291) B3137291
theorem B1567259 : Blo 618297 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B2976439 : Blo 618297 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B1043435 : Blo 618297 1043435 := bstep (se 1 (by rfl) ⟨782576, by rfl⟩ : syracuseStep 1043435 = 1565153) B1565153
theorem B2092175 : Blo 618297 2092175 := bstep (se 1 (by rfl) ⟨1569131, by rfl⟩ : syracuseStep 2092175 = 3138263) B3138263
theorem B5303717 : Blo 618297 5303717 := bstep (se 4 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 5303717 = 994447) B994447
theorem B2092607 : Blo 618297 2092607 := bstep (se 1 (by rfl) ⟨1569455, by rfl⟩ : syracuseStep 2092607 = 3138911) B3138911
theorem B2977555 : Blo 618297 2977555 := bstep (se 1 (by rfl) ⟨2233166, by rfl⟩ : syracuseStep 2977555 = 4466333) B4466333
theorem B618311 : Blo 618297 618311 := bstep (se 1 (by rfl) ⟨463733, by rfl⟩ : syracuseStep 618311 = 927467) B927467
theorem B880507 : Blo 618297 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B618463 : Blo 618297 618463 := bstep (se 1 (by rfl) ⟨463847, by rfl⟩ : syracuseStep 618463 = 927695) B927695
theorem B1273823 : Blo 618297 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B3141827 : Blo 618297 3141827 := bstep (se 1 (by rfl) ⟨2356370, by rfl⟩ : syracuseStep 3141827 = 4712741) B4712741
theorem B618727 : Blo 618297 618727 := bstep (se 1 (by rfl) ⟨464045, by rfl⟩ : syracuseStep 618727 = 928091) B928091
theorem B2093309 : Blo 618297 2093309 := bstep (se 3 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 2093309 = 784991) B784991
theorem B880951 : Blo 618297 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B618879 : Blo 618297 618879 := bstep (se 1 (by rfl) ⟨464159, by rfl⟩ : syracuseStep 618879 = 928319) B928319
theorem B7074215 : Blo 618297 7074215 := bstep (se 1 (by rfl) ⟨5305661, by rfl⟩ : syracuseStep 7074215 = 10611323) B10611323
theorem B618959 : Blo 618297 618959 := bstep (se 1 (by rfl) ⟨464219, by rfl⟩ : syracuseStep 618959 = 928439) B928439
theorem B619111 : Blo 618297 619111 := bstep (se 1 (by rfl) ⟨464333, by rfl⟩ : syracuseStep 619111 = 928667) B928667
theorem B2093849 : Blo 618297 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B1569577 : Blo 618297 1569577 := bstep (se 2 (by rfl) ⟨588591, by rfl⟩ : syracuseStep 1569577 = 1177183) B1177183
theorem B619375 : Blo 618297 619375 := bstep (se 1 (by rfl) ⟨464531, by rfl⟩ : syracuseStep 619375 = 929063) B929063
theorem B3830689 : Blo 618297 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B619431 : Blo 618297 619431 := bstep (se 1 (by rfl) ⟨464573, by rfl⟩ : syracuseStep 619431 = 929147) B929147
theorem B619515 : Blo 618297 619515 := bstep (se 1 (by rfl) ⟨464636, by rfl⟩ : syracuseStep 619515 = 929273) B929273
theorem B2094119 : Blo 618297 2094119 := bstep (se 1 (by rfl) ⟨1570589, by rfl⟩ : syracuseStep 2094119 = 3141179) B3141179
theorem B619583 : Blo 618297 619583 := bstep (se 1 (by rfl) ⟨464687, by rfl⟩ : syracuseStep 619583 = 929375) B929375
theorem B881771 : Blo 618297 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B619727 : Blo 618297 619727 := bstep (se 1 (by rfl) ⟨464795, by rfl⟩ : syracuseStep 619727 = 929591) B929591
theorem B619931 : Blo 618297 619931 := bstep (se 1 (by rfl) ⟨464948, by rfl⟩ : syracuseStep 619931 = 929897) B929897
theorem B30242315 : Blo 618297 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B620143 : Blo 618297 620143 := bstep (se 1 (by rfl) ⟨465107, by rfl⟩ : syracuseStep 620143 = 930215) B930215
theorem B620199 : Blo 618297 620199 := bstep (se 1 (by rfl) ⟨465149, by rfl⟩ : syracuseStep 620199 = 930299) B930299
theorem B620283 : Blo 618297 620283 := bstep (se 1 (by rfl) ⟨465212, by rfl⟩ : syracuseStep 620283 = 930425) B930425
theorem B620319 : Blo 618297 620319 := bstep (se 1 (by rfl) ⟨465239, by rfl⟩ : syracuseStep 620319 = 930479) B930479
theorem B2357039 : Blo 618297 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B620351 : Blo 618297 620351 := bstep (se 1 (by rfl) ⟨465263, by rfl⟩ : syracuseStep 620351 = 930527) B930527
theorem B1046351 : Blo 618297 1046351 := bstep (se 1 (by rfl) ⟨784763, by rfl⟩ : syracuseStep 1046351 = 1569527) B1569527
theorem B620527 : Blo 618297 620527 := bstep (se 1 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 620527 = 930791) B930791
theorem B2095199 : Blo 618297 2095199 := bstep (se 1 (by rfl) ⟨1571399, by rfl⟩ : syracuseStep 2095199 = 3142799) B3142799
theorem B620699 : Blo 618297 620699 := bstep (se 1 (by rfl) ⟨465524, by rfl⟩ : syracuseStep 620699 = 931049) B931049
theorem B620735 : Blo 618297 620735 := bstep (se 1 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 620735 = 931103) B931103
theorem B1571015 : Blo 618297 1571015 := bstep (se 1 (by rfl) ⟨1178261, by rfl⟩ : syracuseStep 1571015 = 2356523) B2356523
theorem B1177897 : Blo 618297 1177897 := bstep (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) B883423
theorem B620847 : Blo 618297 620847 := bstep (se 1 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 620847 = 931271) B931271
theorem B621083 : Blo 618297 621083 := bstep (se 1 (by rfl) ⟨465812, by rfl⟩ : syracuseStep 621083 = 931625) B931625
theorem B621087 : Blo 618297 621087 := bstep (se 1 (by rfl) ⟨465815, by rfl⟩ : syracuseStep 621087 = 931631) B931631
theorem B2095955 : Blo 618297 2095955 := bstep (se 1 (by rfl) ⟨1571966, by rfl⟩ : syracuseStep 2095955 = 3143933) B3143933
theorem B1178459 : Blo 618297 1178459 := bstep (se 1 (by rfl) ⟨883844, by rfl⟩ : syracuseStep 1178459 = 1767689) B1767689
theorem B621403 : Blo 618297 621403 := bstep (se 1 (by rfl) ⟨466052, by rfl⟩ : syracuseStep 621403 = 932105) B932105
theorem B621471 : Blo 618297 621471 := bstep (se 1 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 621471 = 932207) B932207
theorem B1047593 : Blo 618297 1047593 := bstep (se 2 (by rfl) ⟨392847, by rfl⟩ : syracuseStep 1047593 = 785695) B785695
theorem B621615 : Blo 618297 621615 := bstep (se 1 (by rfl) ⟨466211, by rfl⟩ : syracuseStep 621615 = 932423) B932423
theorem B621639 : Blo 618297 621639 := bstep (se 1 (by rfl) ⟨466229, by rfl⟩ : syracuseStep 621639 = 932459) B932459
theorem B2555009 : Blo 618297 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B1047775 : Blo 618297 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B621791 : Blo 618297 621791 := bstep (se 1 (by rfl) ⟨466343, by rfl⟩ : syracuseStep 621791 = 932687) B932687
theorem B7077131 : Blo 618297 7077131 := bstep (se 1 (by rfl) ⟨5307848, by rfl⟩ : syracuseStep 7077131 = 10615697) B10615697
theorem B2096495 : Blo 618297 2096495 := bstep (se 1 (by rfl) ⟨1572371, by rfl⟩ : syracuseStep 2096495 = 3144743) B3144743
theorem B2260391 : Blo 618297 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B884135 : Blo 618297 884135 := bstep (se 1 (by rfl) ⟨663101, by rfl⟩ : syracuseStep 884135 = 1326203) B1326203
theorem B2653651 : Blo 618297 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B622055 : Blo 618297 622055 := bstep (se 1 (by rfl) ⟨466541, by rfl⟩ : syracuseStep 622055 = 933083) B933083
theorem B7962137 : Blo 618297 7962137 := bstep (se 2 (by rfl) ⟨2985801, by rfl⟩ : syracuseStep 7962137 = 5971603) B5971603
theorem B1572443 : Blo 618297 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B622171 : Blo 618297 622171 := bstep (se 1 (by rfl) ⟨466628, by rfl⟩ : syracuseStep 622171 = 933257) B933257
theorem B1146475 : Blo 618297 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B1048207 : Blo 618297 1048207 := bstep (se 1 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 1048207 = 1572311) B1572311
theorem B1769147 : Blo 618297 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B2096873 : Blo 618297 2096873 := bstep (se 2 (by rfl) ⟨786327, by rfl⟩ : syracuseStep 2096873 = 1572655) B1572655
theorem B1179515 : Blo 618297 1179515 := bstep (se 1 (by rfl) ⟨884636, by rfl⟩ : syracuseStep 1179515 = 1769273) B1769273
theorem B2359165 : Blo 618297 2359165 := bstep (se 3 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 2359165 = 884687) B884687
theorem B786667 : Blo 618297 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B2392649 : Blo 618297 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B3146363 : Blo 618297 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B2098007 : Blo 618297 2098007 := bstep (se 1 (by rfl) ⟨1573505, by rfl⟩ : syracuseStep 2098007 = 3147011) B3147011
theorem B10585079 : Blo 618297 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B1573951 : Blo 618297 1573951 := bstep (se 1 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 1573951 = 2360927) B2360927
theorem B4785419 : Blo 618297 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B2360623 : Blo 618297 2360623 := bstep (se 1 (by rfl) ⟨1770467, by rfl⟩ : syracuseStep 2360623 = 3540935) B3540935
theorem B1049935 : Blo 618297 1049935 := bstep (se 1 (by rfl) ⟨787451, by rfl⟩ : syracuseStep 1049935 = 1574903) B1574903
theorem B2655737 : Blo 618297 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B1181375 : Blo 618297 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B2393819 : Blo 618297 2393819 := bstep (se 1 (by rfl) ⟨1795364, by rfl⟩ : syracuseStep 2393819 = 3590729) B3590729
theorem B2361095 : Blo 618297 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B228984641 : Blo 618297 228984641 := bstep (se 2 (by rfl) ⟨85869240, by rfl⟩ : syracuseStep 228984641 = 171738481) B171738481
theorem B2656097 : Blo 618297 2656097 := bstep (se 2 (by rfl) ⟨996036, by rfl⟩ : syracuseStep 2656097 = 1992073) B1992073
theorem B2099087 : Blo 618297 2099087 := bstep (se 1 (by rfl) ⟨1574315, by rfl⟩ : syracuseStep 2099087 = 3148631) B3148631
theorem B3541117 : Blo 618297 3541117 := bstep (se 3 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 3541117 = 1327919) B1327919
theorem B20384011 : Blo 618297 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B4459009 : Blo 618297 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B76516433 : Blo 618297 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B2362553 : Blo 618297 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B2231783 : Blo 618297 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B3968585 : Blo 618297 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B4722461 : Blo 618297 4722461 := bstep (se 3 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 4722461 = 1770923) B1770923
theorem B3150089 : Blo 618297 3150089 := bstep (se 2 (by rfl) ⟨1181283, by rfl⟩ : syracuseStep 3150089 = 2362567) B2362567
theorem B96932213 : Blo 618297 96932213 := bstep (se 5 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 96932213 = 9087395) B9087395
theorem B3347027 : Blo 618297 3347027 := bstep (se 1 (by rfl) ⟨2510270, by rfl⟩ : syracuseStep 3347027 = 5020541) B5020541
theorem B10195703 : Blo 618297 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B33952537 : Blo 618297 33952537 := bstep (se 2 (by rfl) ⟨12732201, by rfl⟩ : syracuseStep 33952537 = 25464403) B25464403
theorem B17896463 : Blo 618297 17896463 := bstep (se 1 (by rfl) ⟨13422347, by rfl⟩ : syracuseStep 17896463 = 26844695) B26844695
theorem B3970073 : Blo 618297 3970073 := bstep (se 2 (by rfl) ⟨1488777, by rfl⟩ : syracuseStep 3970073 = 2977555) B2977555
theorem B4035881 : Blo 618297 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B660799 : Blo 618297 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B6723283 : Blo 618297 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B10065667 : Blo 618297 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B7739497 : Blo 618297 7739497 := bstep (se 2 (by rfl) ⟨2902311, by rfl⟩ : syracuseStep 7739497 = 5804623) B5804623
theorem B1677449 : Blo 618297 1677449 := bstep (se 2 (by rfl) ⟨629043, by rfl⟩ : syracuseStep 1677449 = 1258087) B1258087
theorem B4724891 : Blo 618297 4724891 := bstep (se 1 (by rfl) ⟨3543668, by rfl⟩ : syracuseStep 4724891 = 7087337) B7087337
theorem B1809209 : Blo 618297 1809209 := bstep (se 2 (by rfl) ⟨678453, by rfl⟩ : syracuseStep 1809209 = 1356907) B1356907
theorem B695623 : Blo 618297 695623 := bstep (se 1 (by rfl) ⟨521717, by rfl⟩ : syracuseStep 695623 = 1043435) B1043435
theorem B1679201 : Blo 618297 1679201 := bstep (se 2 (by rfl) ⟨629700, by rfl⟩ : syracuseStep 1679201 = 1259401) B1259401
theorem B3350443 : Blo 618297 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B5972561 : Blo 618297 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B20161543 : Blo 618297 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B697567 : Blo 618297 697567 := bstep (se 1 (by rfl) ⟨523175, by rfl⟩ : syracuseStep 697567 = 1046351) B1046351
theorem B698395 : Blo 618297 698395 := bstep (se 1 (by rfl) ⟨523796, by rfl⟩ : syracuseStep 698395 = 1047593) B1047593
theorem B927791 : Blo 618297 927791 := bstep (se 1 (by rfl) ⟨695843, by rfl⟩ : syracuseStep 927791 = 1391687) B1391687
theorem B4466735 : Blo 618297 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B1321103 : Blo 618297 1321103 := bstep (se 1 (by rfl) ⟨990827, by rfl⟩ : syracuseStep 1321103 = 1981655) B1981655
theorem B928055 : Blo 618297 928055 := bstep (se 1 (by rfl) ⟨696041, by rfl⟩ : syracuseStep 928055 = 1392083) B1392083
theorem B5286221 : Blo 618297 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B928235 : Blo 618297 928235 := bstep (se 1 (by rfl) ⟨696176, by rfl⟩ : syracuseStep 928235 = 1392353) B1392353
theorem B5024531 : Blo 618297 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B928937 : Blo 618297 928937 := bstep (se 2 (by rfl) ⟨348351, by rfl⟩ : syracuseStep 928937 = 696703) B696703
theorem B1486135 : Blo 618297 1486135 := bstep (se 1 (by rfl) ⟨1114601, by rfl⟩ : syracuseStep 1486135 = 2229203) B2229203
theorem B699871 : Blo 618297 699871 := bstep (se 1 (by rfl) ⟨524903, by rfl⟩ : syracuseStep 699871 = 1049807) B1049807
theorem B929351 : Blo 618297 929351 := bstep (se 1 (by rfl) ⟨697013, by rfl⟩ : syracuseStep 929351 = 1394027) B1394027
theorem B1322743 : Blo 618297 1322743 := bstep (se 1 (by rfl) ⟨992057, by rfl⟩ : syracuseStep 1322743 = 1984115) B1984115
theorem B929531 : Blo 618297 929531 := bstep (se 1 (by rfl) ⟨697148, by rfl⟩ : syracuseStep 929531 = 1394297) B1394297
theorem B13381523 : Blo 618297 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B930203 : Blo 618297 930203 := bstep (se 1 (by rfl) ⟨697652, by rfl⟩ : syracuseStep 930203 = 1395305) B1395305
theorem B1323785 : Blo 618297 1323785 := bstep (se 2 (by rfl) ⟨496419, by rfl⟩ : syracuseStep 1323785 = 992839) B992839
theorem B1258249 : Blo 618297 1258249 := bstep (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) B943687
theorem B3355415 : Blo 618297 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B930623 : Blo 618297 930623 := bstep (se 1 (by rfl) ⟨697967, by rfl⟩ : syracuseStep 930623 = 1395935) B1395935
theorem B930767 : Blo 618297 930767 := bstep (se 1 (by rfl) ⟨698075, by rfl⟩ : syracuseStep 930767 = 1396151) B1396151
theorem B930809 : Blo 618297 930809 := bstep (se 2 (by rfl) ⟨349053, by rfl⟩ : syracuseStep 930809 = 698107) B698107
theorem B930857 : Blo 618297 930857 := bstep (se 2 (by rfl) ⟨349071, by rfl⟩ : syracuseStep 930857 = 698143) B698143
theorem B930887 : Blo 618297 930887 := bstep (se 1 (by rfl) ⟨698165, by rfl⟩ : syracuseStep 930887 = 1396331) B1396331
theorem B931067 : Blo 618297 931067 := bstep (se 1 (by rfl) ⟨698300, by rfl⟩ : syracuseStep 931067 = 1396601) B1396601
theorem B1324297 : Blo 618297 1324297 := bstep (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) B993223
theorem B36681281 : Blo 618297 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B7059635 : Blo 618297 7059635 := bstep (se 1 (by rfl) ⟨5294726, by rfl⟩ : syracuseStep 7059635 = 10589453) B10589453
theorem B1882361 : Blo 618297 1882361 := bstep (se 2 (by rfl) ⟨705885, by rfl⟩ : syracuseStep 1882361 = 1411771) B1411771
theorem B3029405 : Blo 618297 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B932303 : Blo 618297 932303 := bstep (se 1 (by rfl) ⟨699227, by rfl⟩ : syracuseStep 932303 = 1398455) B1398455
theorem B932393 : Blo 618297 932393 := bstep (se 2 (by rfl) ⟨349647, by rfl⟩ : syracuseStep 932393 = 699295) B699295
theorem B5978711 : Blo 618297 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B1391291 : Blo 618297 1391291 := bstep (se 1 (by rfl) ⟨1043468, by rfl⟩ : syracuseStep 1391291 = 2086937) B2086937
theorem B1981115 : Blo 618297 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B1325801 : Blo 618297 1325801 := bstep (se 2 (by rfl) ⟨497175, by rfl⟩ : syracuseStep 1325801 = 994351) B994351
theorem B932585 : Blo 618297 932585 := bstep (se 2 (by rfl) ⟨349719, by rfl⟩ : syracuseStep 932585 = 699439) B699439
theorem B932969 : Blo 618297 932969 := bstep (se 2 (by rfl) ⟨349863, by rfl⟩ : syracuseStep 932969 = 699727) B699727
theorem B933095 : Blo 618297 933095 := bstep (se 1 (by rfl) ⟨699821, by rfl⟩ : syracuseStep 933095 = 1399643) B1399643
theorem B1392191 : Blo 618297 1392191 := bstep (se 1 (by rfl) ⟨1044143, by rfl⟩ : syracuseStep 1392191 = 2088287) B2088287
theorem B1326655 : Blo 618297 1326655 := bstep (se 1 (by rfl) ⟨994991, by rfl⟩ : syracuseStep 1326655 = 1989983) B1989983
theorem B1392551 : Blo 618297 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B1392875 : Blo 618297 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B21545453 : Blo 618297 21545453 := bstep (se 3 (by rfl) ⟨4039772, by rfl⟩ : syracuseStep 21545453 = 8079545) B8079545
theorem B3523439 : Blo 618297 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B1491911 : Blo 618297 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B1393775 : Blo 618297 1393775 := bstep (se 1 (by rfl) ⟨1045331, by rfl⟩ : syracuseStep 1393775 = 2090663) B2090663
theorem B3130811 : Blo 618297 3130811 := bstep (se 1 (by rfl) ⟨2348108, by rfl⟩ : syracuseStep 3130811 = 4696217) B4696217
theorem B1394171 : Blo 618297 1394171 := bstep (se 1 (by rfl) ⟨1045628, by rfl⟩ : syracuseStep 1394171 = 2091257) B2091257
theorem B1394207 : Blo 618297 1394207 := bstep (se 1 (by rfl) ⟨1045655, by rfl⟩ : syracuseStep 1394207 = 2091311) B2091311
theorem B1328671 : Blo 618297 1328671 := bstep (se 1 (by rfl) ⟨996503, by rfl⟩ : syracuseStep 1328671 = 1993007) B1993007
theorem B1394351 : Blo 618297 1394351 := bstep (se 1 (by rfl) ⟨1045763, by rfl⟩ : syracuseStep 1394351 = 2091527) B2091527
theorem B1394783 : Blo 618297 1394783 := bstep (se 1 (by rfl) ⟨1046087, by rfl⟩ : syracuseStep 1394783 = 2092175) B2092175
theorem B1395071 : Blo 618297 1395071 := bstep (se 1 (by rfl) ⟨1046303, by rfl⟩ : syracuseStep 1395071 = 2092607) B2092607
theorem B3132107 : Blo 618297 3132107 := bstep (se 1 (by rfl) ⟨2349080, by rfl⟩ : syracuseStep 3132107 = 4698161) B4698161
theorem B1395539 : Blo 618297 1395539 := bstep (se 1 (by rfl) ⟨1046654, by rfl⟩ : syracuseStep 1395539 = 2093309) B2093309
theorem B5294969 : Blo 618297 5294969 := bstep (se 2 (by rfl) ⟨1985613, by rfl⟩ : syracuseStep 5294969 = 3971227) B3971227
theorem B1395899 : Blo 618297 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B1396079 : Blo 618297 1396079 := bstep (se 1 (by rfl) ⟨1047059, by rfl⟩ : syracuseStep 1396079 = 2094119) B2094119
theorem B1396799 : Blo 618297 1396799 := bstep (se 1 (by rfl) ⟨1047599, by rfl⟩ : syracuseStep 1396799 = 2095199) B2095199
theorem B1397033 : Blo 618297 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B1397303 : Blo 618297 1397303 := bstep (se 1 (by rfl) ⟨1047977, by rfl⟩ : syracuseStep 1397303 = 2095955) B2095955
theorem B1528633 : Blo 618297 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B1397609 : Blo 618297 1397609 := bstep (se 2 (by rfl) ⟨524103, by rfl⟩ : syracuseStep 1397609 = 1048207) B1048207
theorem B1397663 : Blo 618297 1397663 := bstep (se 1 (by rfl) ⟨1048247, by rfl⟩ : syracuseStep 1397663 = 2096495) B2096495
theorem B3134537 : Blo 618297 3134537 := bstep (se 2 (by rfl) ⟨1175451, by rfl⟩ : syracuseStep 3134537 = 2350903) B2350903
theorem B1397915 : Blo 618297 1397915 := bstep (se 1 (by rfl) ⟨1048436, by rfl⟩ : syracuseStep 1397915 = 2096873) B2096873
theorem B1398491 : Blo 618297 1398491 := bstep (se 1 (by rfl) ⟨1048868, by rfl⟩ : syracuseStep 1398491 = 2097737) B2097737
theorem B1398599 : Blo 618297 1398599 := bstep (se 1 (by rfl) ⟨1048949, by rfl⟩ : syracuseStep 1398599 = 2097899) B2097899
theorem B3528521 : Blo 618297 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B9558161 : Blo 618297 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B13588651 : Blo 618297 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B1431865 : Blo 618297 1431865 := bstep (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) B1073899
theorem B1399607 : Blo 618297 1399607 := bstep (se 1 (by rfl) ⟨1049705, by rfl⟩ : syracuseStep 1399607 = 2099411) B2099411
theorem B4709339 : Blo 618297 4709339 := bstep (se 1 (by rfl) ⟨3532004, by rfl⟩ : syracuseStep 4709339 = 7064009) B7064009
theorem B1399787 : Blo 618297 1399787 := bstep (se 1 (by rfl) ⟨1049840, by rfl⟩ : syracuseStep 1399787 = 2099681) B2099681
theorem B5299343 : Blo 618297 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B2350417 : Blo 618297 2350417 := bstep (se 2 (by rfl) ⟨881406, by rfl⟩ : syracuseStep 2350417 = 1762813) B1762813
theorem B4709825 : Blo 618297 4709825 := bstep (se 2 (by rfl) ⟨1766184, by rfl⟩ : syracuseStep 4709825 = 3532369) B3532369
theorem B2351389 : Blo 618297 2351389 := bstep (se 3 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 2351389 = 881771) B881771
theorem B25747793 : Blo 618297 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B2516041 : Blo 618297 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B5432903 : Blo 618297 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B9528965 : Blo 618297 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B2090771 : Blo 618297 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B2680715 : Blo 618297 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B2090987 : Blo 618297 2090987 := bstep (se 1 (by rfl) ⟨1568240, by rfl⟩ : syracuseStep 2090987 = 3136481) B3136481
theorem B1763315 : Blo 618297 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B1566803 : Blo 618297 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1174009 : Blo 618297 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B3533327 : Blo 618297 3533327 := bstep (se 1 (by rfl) ⟨2649995, by rfl⟩ : syracuseStep 3533327 = 5299991) B5299991
theorem B9038765 : Blo 618297 9038765 := bstep (se 3 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 9038765 = 3389537) B3389537
theorem B1174495 : Blo 618297 1174495 := bstep (se 1 (by rfl) ⟨880871, by rfl⟩ : syracuseStep 1174495 = 1761743) B1761743
theorem B1174601 : Blo 618297 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B7957673 : Blo 618297 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B2649449 : Blo 618297 2649449 := bstep (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) B1987087
theorem B1043867 : Blo 618297 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B2092499 : Blo 618297 2092499 := bstep (se 1 (by rfl) ⟨1569374, by rfl⟩ : syracuseStep 2092499 = 3138749) B3138749
theorem B3173855 : Blo 618297 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B2092769 : Blo 618297 2092769 := bstep (se 2 (by rfl) ⟨784788, by rfl⟩ : syracuseStep 2092769 = 1569577) B1569577
theorem B1765115 : Blo 618297 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B618303 : Blo 618297 618303 := bstep (se 1 (by rfl) ⟨463727, by rfl⟩ : syracuseStep 618303 = 927455) B927455
theorem B618367 : Blo 618297 618367 := bstep (se 1 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 618367 = 927551) B927551
theorem B5107585 : Blo 618297 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B1175467 : Blo 618297 1175467 := bstep (se 1 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 1175467 = 1763201) B1763201
theorem B618479 : Blo 618297 618479 := bstep (se 1 (by rfl) ⟨463859, by rfl⟩ : syracuseStep 618479 = 927719) B927719
theorem B618491 : Blo 618297 618491 := bstep (se 1 (by rfl) ⟨463868, by rfl⟩ : syracuseStep 618491 = 927737) B927737
theorem B618559 : Blo 618297 618559 := bstep (se 1 (by rfl) ⟨463919, by rfl⟩ : syracuseStep 618559 = 927839) B927839
theorem B618599 : Blo 618297 618599 := bstep (se 1 (by rfl) ⟨463949, by rfl⟩ : syracuseStep 618599 = 927899) B927899
theorem B618623 : Blo 618297 618623 := bstep (se 1 (by rfl) ⟨463967, by rfl⟩ : syracuseStep 618623 = 927935) B927935
theorem B1044623 : Blo 618297 1044623 := bstep (se 1 (by rfl) ⟨783467, by rfl⟩ : syracuseStep 1044623 = 1566935) B1566935
theorem B618651 : Blo 618297 618651 := bstep (se 1 (by rfl) ⟨463988, by rfl⟩ : syracuseStep 618651 = 927977) B927977
theorem B618855 : Blo 618297 618855 := bstep (se 1 (by rfl) ⟨464141, by rfl⟩ : syracuseStep 618855 = 928283) B928283
theorem B1044839 : Blo 618297 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B618907 : Blo 618297 618907 := bstep (se 1 (by rfl) ⟨464180, by rfl⟩ : syracuseStep 618907 = 928361) B928361
theorem B8942233 : Blo 618297 8942233 := bstep (se 2 (by rfl) ⟨3353337, by rfl⟩ : syracuseStep 8942233 = 6706675) B6706675
theorem B619259 : Blo 618297 619259 := bstep (se 1 (by rfl) ⟨464444, by rfl⟩ : syracuseStep 619259 = 928889) B928889
theorem B619327 : Blo 618297 619327 := bstep (se 1 (by rfl) ⟨464495, by rfl⟩ : syracuseStep 619327 = 928991) B928991
theorem B619355 : Blo 618297 619355 := bstep (se 1 (by rfl) ⟨464516, by rfl⟩ : syracuseStep 619355 = 929033) B929033
theorem B619423 : Blo 618297 619423 := bstep (se 1 (by rfl) ⟨464567, by rfl⟩ : syracuseStep 619423 = 929135) B929135
theorem B3535811 : Blo 618297 3535811 := bstep (se 1 (by rfl) ⟨2651858, by rfl⟩ : syracuseStep 3535811 = 5303717) B5303717
theorem B619503 : Blo 618297 619503 := bstep (se 1 (by rfl) ⟨464627, by rfl⟩ : syracuseStep 619503 = 929255) B929255
theorem B619591 : Blo 618297 619591 := bstep (se 1 (by rfl) ⟨464693, by rfl⟩ : syracuseStep 619591 = 929387) B929387
theorem B619675 : Blo 618297 619675 := bstep (se 1 (by rfl) ⟨464756, by rfl⟩ : syracuseStep 619675 = 929513) B929513
theorem B619771 : Blo 618297 619771 := bstep (se 1 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 619771 = 929657) B929657
theorem B619839 : Blo 618297 619839 := bstep (se 1 (by rfl) ⟨464879, by rfl⟩ : syracuseStep 619839 = 929759) B929759
theorem B849215 : Blo 618297 849215 := bstep (se 1 (by rfl) ⟨636911, by rfl⟩ : syracuseStep 849215 = 1273823) B1273823
theorem B2979287 : Blo 618297 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B2094551 : Blo 618297 2094551 := bstep (se 1 (by rfl) ⟨1570913, by rfl⟩ : syracuseStep 2094551 = 3141827) B3141827
theorem B620007 : Blo 618297 620007 := bstep (se 1 (by rfl) ⟨465005, by rfl⟩ : syracuseStep 620007 = 930011) B930011
theorem B620015 : Blo 618297 620015 := bstep (se 1 (by rfl) ⟨465011, by rfl⟩ : syracuseStep 620015 = 930023) B930023
theorem B620123 : Blo 618297 620123 := bstep (se 1 (by rfl) ⟨465092, by rfl⟩ : syracuseStep 620123 = 930185) B930185
theorem B4716143 : Blo 618297 4716143 := bstep (se 1 (by rfl) ⟨3537107, by rfl⟩ : syracuseStep 4716143 = 7074215) B7074215
theorem B620187 : Blo 618297 620187 := bstep (se 1 (by rfl) ⟨465140, by rfl⟩ : syracuseStep 620187 = 930281) B930281
theorem B1570529 : Blo 618297 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B882409 : Blo 618297 882409 := bstep (se 2 (by rfl) ⟨330903, by rfl⟩ : syracuseStep 882409 = 661807) B661807
theorem B620271 : Blo 618297 620271 := bstep (se 1 (by rfl) ⟨465203, by rfl⟩ : syracuseStep 620271 = 930407) B930407
theorem B620359 : Blo 618297 620359 := bstep (se 1 (by rfl) ⟨465269, by rfl⟩ : syracuseStep 620359 = 930539) B930539
theorem B620379 : Blo 618297 620379 := bstep (se 1 (by rfl) ⟨465284, by rfl⟩ : syracuseStep 620379 = 930569) B930569
theorem B2652011 : Blo 618297 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B620447 : Blo 618297 620447 := bstep (se 1 (by rfl) ⟨465335, by rfl⟩ : syracuseStep 620447 = 930671) B930671
theorem B3766181 : Blo 618297 3766181 := bstep (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) B706159
theorem B620615 : Blo 618297 620615 := bstep (se 1 (by rfl) ⟨465461, by rfl⟩ : syracuseStep 620615 = 930923) B930923
theorem B620775 : Blo 618297 620775 := bstep (se 1 (by rfl) ⟨465581, by rfl⟩ : syracuseStep 620775 = 931163) B931163
theorem B620959 : Blo 618297 620959 := bstep (se 1 (by rfl) ⟨465719, by rfl⟩ : syracuseStep 620959 = 931439) B931439
theorem B6027709 : Blo 618297 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B2357693 : Blo 618297 2357693 := bstep (se 3 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 2357693 = 884135) B884135
theorem B621007 : Blo 618297 621007 := bstep (se 1 (by rfl) ⟨465755, by rfl⟩ : syracuseStep 621007 = 931511) B931511
theorem B621031 : Blo 618297 621031 := bstep (se 1 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 621031 = 931547) B931547
theorem B1571359 : Blo 618297 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B2652763 : Blo 618297 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B621147 : Blo 618297 621147 := bstep (se 1 (by rfl) ⟨465860, by rfl⟩ : syracuseStep 621147 = 931721) B931721
theorem B621215 : Blo 618297 621215 := bstep (se 1 (by rfl) ⟨465911, by rfl⟩ : syracuseStep 621215 = 931823) B931823
theorem B1047343 : Blo 618297 1047343 := bstep (se 1 (by rfl) ⟨785507, by rfl⟩ : syracuseStep 1047343 = 1571015) B1571015
theorem B621383 : Blo 618297 621383 := bstep (se 1 (by rfl) ⟨466037, by rfl⟩ : syracuseStep 621383 = 932075) B932075
theorem B2653037 : Blo 618297 2653037 := bstep (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) B994889
theorem B621423 : Blo 618297 621423 := bstep (se 1 (by rfl) ⟨466067, by rfl⟩ : syracuseStep 621423 = 932135) B932135
theorem B621479 : Blo 618297 621479 := bstep (se 1 (by rfl) ⟨466109, by rfl⟩ : syracuseStep 621479 = 932219) B932219
theorem B621659 : Blo 618297 621659 := bstep (se 1 (by rfl) ⟨466244, by rfl⟩ : syracuseStep 621659 = 932489) B932489
theorem B621775 : Blo 618297 621775 := bstep (se 1 (by rfl) ⟨466331, by rfl⟩ : syracuseStep 621775 = 932663) B932663
theorem B785639 : Blo 618297 785639 := bstep (se 1 (by rfl) ⟨589229, by rfl⟩ : syracuseStep 785639 = 1178459) B1178459
theorem B621799 : Blo 618297 621799 := bstep (se 1 (by rfl) ⟨466349, by rfl⟩ : syracuseStep 621799 = 932699) B932699
theorem B3538201 : Blo 618297 3538201 := bstep (se 2 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 3538201 = 2653651) B2653651
theorem B621895 : Blo 618297 621895 := bstep (se 1 (by rfl) ⟨466421, by rfl⟩ : syracuseStep 621895 = 932843) B932843
theorem B1703339 : Blo 618297 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B622031 : Blo 618297 622031 := bstep (se 1 (by rfl) ⟨466523, by rfl⟩ : syracuseStep 622031 = 933047) B933047
theorem B4718087 : Blo 618297 4718087 := bstep (se 1 (by rfl) ⟨3538565, by rfl⟩ : syracuseStep 4718087 = 7077131) B7077131
theorem B622191 : Blo 618297 622191 := bstep (se 1 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 622191 = 933287) B933287
theorem B622247 : Blo 618297 622247 := bstep (se 1 (by rfl) ⟨466685, by rfl⟩ : syracuseStep 622247 = 933371) B933371
theorem B5308091 : Blo 618297 5308091 := bstep (se 1 (by rfl) ⟨3981068, by rfl⟩ : syracuseStep 5308091 = 7962137) B7962137
theorem B1048295 : Blo 618297 1048295 := bstep (se 1 (by rfl) ⟨786221, by rfl⟩ : syracuseStep 1048295 = 1572443) B1572443
theorem B1179431 : Blo 618297 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B3145553 : Blo 618297 3145553 := bstep (se 2 (by rfl) ⟨1179582, by rfl⟩ : syracuseStep 3145553 = 2359165) B2359165
theorem B5046097 : Blo 618297 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B786343 : Blo 618297 786343 := bstep (se 1 (by rfl) ⟨589757, by rfl⟩ : syracuseStep 786343 = 1179515) B1179515
theorem B1048889 : Blo 618297 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B2097575 : Blo 618297 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B1770491 : Blo 618297 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B787583 : Blo 618297 787583 := bstep (se 1 (by rfl) ⟨590687, by rfl⟩ : syracuseStep 787583 = 1181375) B1181375
theorem B1574063 : Blo 618297 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B1770731 : Blo 618297 1770731 := bstep (se 1 (by rfl) ⟨1328048, by rfl⟩ : syracuseStep 1770731 = 2656097) B2656097
theorem B2098601 : Blo 618297 2098601 := bstep (se 2 (by rfl) ⟨786975, by rfl⟩ : syracuseStep 2098601 = 1573951) B1573951
theorem B3147497 : Blo 618297 3147497 := bstep (se 2 (by rfl) ⟨1180311, by rfl⟩ : syracuseStep 3147497 = 2360623) B2360623
theorem B1771561 : Blo 618297 1771561 := bstep (se 2 (by rfl) ⟨664335, by rfl⟩ : syracuseStep 1771561 = 1328671) B1328671
theorem B1575035 : Blo 618297 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B3148307 : Blo 618297 3148307 := bstep (se 1 (by rfl) ⟨2361230, by rfl⟩ : syracuseStep 3148307 = 4722461) B4722461
theorem B4721489 : Blo 618297 4721489 := bstep (se 2 (by rfl) ⟨1770558, by rfl⟩ : syracuseStep 4721489 = 3541117) B3541117
theorem B2100059 : Blo 618297 2100059 := bstep (se 1 (by rfl) ⟨1575044, by rfl⟩ : syracuseStep 2100059 = 3150089) B3150089
theorem B64621475 : Blo 618297 64621475 := bstep (se 1 (by rfl) ⟨48466106, by rfl⟩ : syracuseStep 64621475 = 96932213) B96932213
theorem B2231351 : Blo 618297 2231351 := bstep (se 1 (by rfl) ⟨1673513, by rfl⟩ : syracuseStep 2231351 = 3347027) B3347027
theorem B11930975 : Blo 618297 11930975 := bstep (se 1 (by rfl) ⟨8948231, by rfl⟩ : syracuseStep 11930975 = 17896463) B17896463
theorem B2264573 : Blo 618297 2264573 := bstep (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) B849215
theorem B2690587 : Blo 618297 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B1118299 : Blo 618297 1118299 := bstep (se 1 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 1118299 = 1677449) B1677449
theorem B3149927 : Blo 618297 3149927 := bstep (se 1 (by rfl) ⟨2362445, by rfl⟩ : syracuseStep 3149927 = 4724891) B4724891
theorem B181080197 : Blo 618297 181080197 := bstep (se 4 (by rfl) ⟨16976268, by rfl⟩ : syracuseStep 181080197 = 33952537) B33952537
theorem B33854453 : Blo 618297 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B7148573 : Blo 618297 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B1119467 : Blo 618297 1119467 := bstep (se 1 (by rfl) ⟨839600, by rfl⟩ : syracuseStep 1119467 = 1679201) B1679201
theorem B1677665 : Blo 618297 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B3349687 : Blo 618297 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B695911 : Blo 618297 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B8921015 : Blo 618297 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B696415 : Blo 618297 696415 := bstep (se 1 (by rfl) ⟨522311, by rfl⟩ : syracuseStep 696415 = 1044623) B1044623
theorem B696559 : Blo 618297 696559 := bstep (se 1 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 696559 = 1044839) B1044839
theorem B1909153 : Blo 618297 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B2236943 : Blo 618297 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B8036945 : Blo 618297 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B24454187 : Blo 618297 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B1254907 : Blo 618297 1254907 := bstep (se 1 (by rfl) ⟨941180, by rfl⟩ : syracuseStep 1254907 = 1882361) B1882361
theorem B927497 : Blo 618297 927497 := bstep (se 2 (by rfl) ⟨347811, by rfl⟩ : syracuseStep 927497 = 695623) B695623
theorem B927527 : Blo 618297 927527 := bstep (se 1 (by rfl) ⟨695645, by rfl⟩ : syracuseStep 927527 = 1391291) B1391291
theorem B1320743 : Blo 618297 1320743 := bstep (se 1 (by rfl) ⟨990557, by rfl⟩ : syracuseStep 1320743 = 1981115) B1981115
theorem B928127 : Blo 618297 928127 := bstep (se 1 (by rfl) ⟨696095, by rfl⟩ : syracuseStep 928127 = 1392191) B1392191
theorem B6728129 : Blo 618297 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B698863 : Blo 618297 698863 := bstep (se 1 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 698863 = 1048295) B1048295
theorem B4467257 : Blo 618297 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B928367 : Blo 618297 928367 := bstep (se 1 (by rfl) ⟨696275, by rfl⟩ : syracuseStep 928367 = 1392551) B1392551
theorem B928583 : Blo 618297 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B994607 : Blo 618297 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B7056719 : Blo 618297 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B929183 : Blo 618297 929183 := bstep (se 1 (by rfl) ⟨696887, by rfl⟩ : syracuseStep 929183 = 1393775) B1393775
theorem B3190279 : Blo 618297 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B929447 : Blo 618297 929447 := bstep (se 1 (by rfl) ⟨697085, by rfl⟩ : syracuseStep 929447 = 1394171) B1394171
theorem B929471 : Blo 618297 929471 := bstep (se 1 (by rfl) ⟨697103, by rfl⟩ : syracuseStep 929471 = 1394207) B1394207
theorem B929567 : Blo 618297 929567 := bstep (se 1 (by rfl) ⟨697175, by rfl⟩ : syracuseStep 929567 = 1394351) B1394351
theorem B57454541 : Blo 618297 57454541 := bstep (se 3 (by rfl) ⟨10772726, by rfl⟩ : syracuseStep 57454541 = 21545453) B21545453
theorem B26882057 : Blo 618297 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B929855 : Blo 618297 929855 := bstep (se 1 (by rfl) ⟨697391, by rfl⟩ : syracuseStep 929855 = 1394783) B1394783
theorem B930047 : Blo 618297 930047 := bstep (se 1 (by rfl) ⟨697535, by rfl⟩ : syracuseStep 930047 = 1395071) B1395071
theorem B930089 : Blo 618297 930089 := bstep (se 2 (by rfl) ⟨348783, by rfl⟩ : syracuseStep 930089 = 697567) B697567
theorem B930359 : Blo 618297 930359 := bstep (se 1 (by rfl) ⟨697769, by rfl⟩ : syracuseStep 930359 = 1395539) B1395539
theorem B930599 : Blo 618297 930599 := bstep (se 1 (by rfl) ⟨697949, by rfl⟩ : syracuseStep 930599 = 1395899) B1395899
theorem B930719 : Blo 618297 930719 := bstep (se 1 (by rfl) ⟨698039, by rfl⟩ : syracuseStep 930719 = 1396079) B1396079
theorem B1487855 : Blo 618297 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B931193 : Blo 618297 931193 := bstep (se 2 (by rfl) ⟨349197, by rfl⟩ : syracuseStep 931193 = 698395) B698395
theorem B931199 : Blo 618297 931199 := bstep (se 1 (by rfl) ⟨698399, by rfl⟩ : syracuseStep 931199 = 1396799) B1396799
theorem B931355 : Blo 618297 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B27178681 : Blo 618297 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B931535 : Blo 618297 931535 := bstep (se 1 (by rfl) ⟨698651, by rfl⟩ : syracuseStep 931535 = 1397303) B1397303
theorem B6797135 : Blo 618297 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B931739 : Blo 618297 931739 := bstep (se 1 (by rfl) ⟨698804, by rfl⟩ : syracuseStep 931739 = 1397609) B1397609
theorem B931775 : Blo 618297 931775 := bstep (se 1 (by rfl) ⟨698831, by rfl⟩ : syracuseStep 931775 = 1397663) B1397663
theorem B5945345 : Blo 618297 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B931943 : Blo 618297 931943 := bstep (se 1 (by rfl) ⟨698957, by rfl⟩ : syracuseStep 931943 = 1397915) B1397915
theorem B932327 : Blo 618297 932327 := bstep (se 1 (by rfl) ⟨699245, by rfl⟩ : syracuseStep 932327 = 1398491) B1398491
theorem B932399 : Blo 618297 932399 := bstep (se 1 (by rfl) ⟨699299, by rfl⟩ : syracuseStep 932399 = 1398599) B1398599
theorem B6372107 : Blo 618297 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B1981513 : Blo 618297 1981513 := bstep (se 2 (by rfl) ⟨743067, by rfl⟩ : syracuseStep 1981513 = 1486135) B1486135
theorem B933071 : Blo 618297 933071 := bstep (se 1 (by rfl) ⟨699803, by rfl⟩ : syracuseStep 933071 = 1399607) B1399607
theorem B933161 : Blo 618297 933161 := bstep (se 2 (by rfl) ⟨349935, by rfl⟩ : syracuseStep 933161 = 699871) B699871
theorem B933191 : Blo 618297 933191 := bstep (se 1 (by rfl) ⟨699893, by rfl⟩ : syracuseStep 933191 = 1399787) B1399787
theorem B10043149 : Blo 618297 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B13418885 : Blo 618297 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B3981707 : Blo 618297 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B3621935 : Blo 618297 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B8078413 : Blo 618297 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B1393847 : Blo 618297 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B1393991 : Blo 618297 1393991 := bstep (se 1 (by rfl) ⟨1045493, by rfl⟩ : syracuseStep 1393991 = 2090987) B2090987
theorem B3524147 : Blo 618297 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B15943229 : Blo 618297 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B8964377 : Blo 618297 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B1394999 : Blo 618297 1394999 := bstep (se 1 (by rfl) ⟨1046249, by rfl⟩ : syracuseStep 1394999 = 2092499) B2092499
theorem B13420889 : Blo 618297 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B1395179 : Blo 618297 1395179 := bstep (se 1 (by rfl) ⟨1046384, by rfl⟩ : syracuseStep 1395179 = 2092769) B2092769
theorem B3132269 : Blo 618297 3132269 := bstep (se 3 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 3132269 = 1174601) B1174601
theorem B1986191 : Blo 618297 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B1396367 : Blo 618297 1396367 := bstep (se 1 (by rfl) ⟨1047275, by rfl⟩ : syracuseStep 1396367 = 2094551) B2094551
theorem B1396457 : Blo 618297 1396457 := bstep (se 2 (by rfl) ⟨523671, by rfl⟩ : syracuseStep 1396457 = 1047343) B1047343
theorem B4706423 : Blo 618297 4706423 := bstep (se 1 (by rfl) ⟨3529817, by rfl⟩ : syracuseStep 4706423 = 7059635) B7059635
theorem B3133889 : Blo 618297 3133889 := bstep (se 2 (by rfl) ⟨1175208, by rfl⟩ : syracuseStep 3133889 = 2350417) B2350417
theorem B1135559 : Blo 618297 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B3135185 : Blo 618297 3135185 := bstep (se 2 (by rfl) ⟨1175694, by rfl⟩ : syracuseStep 3135185 = 2351389) B2351389
theorem B1595099 : Blo 618297 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B1398671 : Blo 618297 1398671 := bstep (se 1 (by rfl) ⟨1049003, by rfl⟩ : syracuseStep 1398671 = 2098007) B2098007
theorem B2348959 : Blo 618297 2348959 := bstep (se 1 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 2348959 = 3523439) B3523439
theorem B2087207 : Blo 618297 2087207 := bstep (se 1 (by rfl) ⟨1565405, by rfl⟩ : syracuseStep 2087207 = 3130811) B3130811
theorem B1595879 : Blo 618297 1595879 := bstep (se 1 (by rfl) ⟨1196909, by rfl⟩ : syracuseStep 1595879 = 2393819) B2393819
theorem B152656427 : Blo 618297 152656427 := bstep (se 1 (by rfl) ⟨114492320, by rfl⟩ : syracuseStep 152656427 = 228984641) B228984641
theorem B1399391 : Blo 618297 1399391 := bstep (se 1 (by rfl) ⟨1049543, by rfl⟩ : syracuseStep 1399391 = 2099087) B2099087
theorem B1399913 : Blo 618297 1399913 := bstep (se 2 (by rfl) ⟨524967, by rfl⟩ : syracuseStep 1399913 = 1049935) B1049935
theorem B2088071 : Blo 618297 2088071 := bstep (se 1 (by rfl) ⟨1566053, by rfl⟩ : syracuseStep 2088071 = 3132107) B3132107
theorem B3529979 : Blo 618297 3529979 := bstep (se 1 (by rfl) ⟨2647484, by rfl⟩ : syracuseStep 3529979 = 5294969) B5294969
theorem B51010955 : Blo 618297 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B2645723 : Blo 618297 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B1565345 : Blo 618297 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B2646715 : Blo 618297 2646715 := bstep (se 1 (by rfl) ⟨1985036, by rfl⟩ : syracuseStep 2646715 = 3970073) B3970073
theorem B2089691 : Blo 618297 2089691 := bstep (se 1 (by rfl) ⟨1567268, by rfl⟩ : syracuseStep 2089691 = 3134537) B3134537
theorem B2352347 : Blo 618297 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B1565993 : Blo 618297 1565993 := bstep (se 2 (by rfl) ⟨587247, by rfl⟩ : syracuseStep 1565993 = 1174495) B1174495
theorem B8152709 : Blo 618297 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B1206139 : Blo 618297 1206139 := bstep (se 1 (by rfl) ⟨904604, by rfl⟩ : syracuseStep 1206139 = 1809209) B1809209
theorem B3139559 : Blo 618297 3139559 := bstep (se 1 (by rfl) ⟨2354669, by rfl⟩ : syracuseStep 3139559 = 4709339) B4709339
theorem B3532895 : Blo 618297 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B3139883 : Blo 618297 3139883 := bstep (se 1 (by rfl) ⟨2354912, by rfl⟩ : syracuseStep 3139883 = 4709825) B4709825
theorem B1763657 : Blo 618297 1763657 := bstep (se 2 (by rfl) ⟨661371, by rfl⟩ : syracuseStep 1763657 = 1322743) B1322743
theorem B6810113 : Blo 618297 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B1567289 : Blo 618297 1567289 := bstep (se 2 (by rfl) ⟨587733, by rfl⟩ : syracuseStep 1567289 = 1175467) B1175467
theorem B17165195 : Blo 618297 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B11922977 : Blo 618297 11922977 := bstep (se 2 (by rfl) ⟨4471116, by rfl⟩ : syracuseStep 11922977 = 8942233) B8942233
theorem B6352643 : Blo 618297 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1175543 : Blo 618297 1175543 := bstep (se 1 (by rfl) ⟨881657, by rfl⟩ : syracuseStep 1175543 = 1763315) B1763315
theorem B618527 : Blo 618297 618527 := bstep (se 1 (by rfl) ⟨463895, by rfl⟩ : syracuseStep 618527 = 927791) B927791
theorem B2977823 : Blo 618297 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B1044535 : Blo 618297 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B880735 : Blo 618297 880735 := bstep (se 1 (by rfl) ⟨660551, by rfl⟩ : syracuseStep 880735 = 1321103) B1321103
theorem B618703 : Blo 618297 618703 := bstep (se 1 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 618703 = 928055) B928055
theorem B618823 : Blo 618297 618823 := bstep (se 1 (by rfl) ⟨464117, by rfl⟩ : syracuseStep 618823 = 928235) B928235
theorem B2355551 : Blo 618297 2355551 := bstep (se 1 (by rfl) ⟨1766663, by rfl⟩ : syracuseStep 2355551 = 3533327) B3533327
theorem B1765729 : Blo 618297 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B881065 : Blo 618297 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B6025843 : Blo 618297 6025843 := bstep (se 1 (by rfl) ⟨4519382, by rfl⟩ : syracuseStep 6025843 = 9038765) B9038765
theorem B619291 : Blo 618297 619291 := bstep (se 1 (by rfl) ⟨464468, by rfl⟩ : syracuseStep 619291 = 928937) B928937
theorem B5305115 : Blo 618297 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B1766299 : Blo 618297 1766299 := bstep (se 1 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 1766299 = 2649449) B2649449
theorem B1176545 : Blo 618297 1176545 := bstep (se 2 (by rfl) ⟨441204, by rfl⟩ : syracuseStep 1176545 = 882409) B882409
theorem B619567 : Blo 618297 619567 := bstep (se 1 (by rfl) ⟨464675, by rfl⟩ : syracuseStep 619567 = 929351) B929351
theorem B619687 : Blo 618297 619687 := bstep (se 1 (by rfl) ⟨464765, by rfl⟩ : syracuseStep 619687 = 929531) B929531
theorem B1176743 : Blo 618297 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B10319329 : Blo 618297 10319329 := bstep (se 2 (by rfl) ⟨3869748, by rfl⟩ : syracuseStep 10319329 = 7739497) B7739497
theorem B18118201 : Blo 618297 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B620135 : Blo 618297 620135 := bstep (se 1 (by rfl) ⟨465101, by rfl⟩ : syracuseStep 620135 = 930203) B930203
theorem B882523 : Blo 618297 882523 := bstep (se 1 (by rfl) ⟨661892, by rfl⟩ : syracuseStep 882523 = 1323785) B1323785
theorem B620415 : Blo 618297 620415 := bstep (se 1 (by rfl) ⟨465311, by rfl⟩ : syracuseStep 620415 = 930623) B930623
theorem B2095037 : Blo 618297 2095037 := bstep (se 3 (by rfl) ⟨392819, by rfl⟩ : syracuseStep 2095037 = 785639) B785639
theorem B2357207 : Blo 618297 2357207 := bstep (se 1 (by rfl) ⟨1767905, by rfl⟩ : syracuseStep 2357207 = 3535811) B3535811
theorem B620511 : Blo 618297 620511 := bstep (se 1 (by rfl) ⟨465383, by rfl⟩ : syracuseStep 620511 = 930767) B930767
theorem B620539 : Blo 618297 620539 := bstep (se 1 (by rfl) ⟨465404, by rfl⟩ : syracuseStep 620539 = 930809) B930809
theorem B620571 : Blo 618297 620571 := bstep (se 1 (by rfl) ⟨465428, by rfl⟩ : syracuseStep 620571 = 930857) B930857
theorem B2095145 : Blo 618297 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B620591 : Blo 618297 620591 := bstep (se 1 (by rfl) ⟨465443, by rfl⟩ : syracuseStep 620591 = 930887) B930887
theorem B3537017 : Blo 618297 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B620711 : Blo 618297 620711 := bstep (se 1 (by rfl) ⟨465533, by rfl⟩ : syracuseStep 620711 = 931067) B931067
theorem B3144095 : Blo 618297 3144095 := bstep (se 1 (by rfl) ⟨2358071, by rfl⟩ : syracuseStep 3144095 = 4716143) B4716143
theorem B1047019 : Blo 618297 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B1768007 : Blo 618297 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B1571795 : Blo 618297 1571795 := bstep (se 1 (by rfl) ⟨1178846, by rfl⟩ : syracuseStep 1571795 = 2357693) B2357693
theorem B621535 : Blo 618297 621535 := bstep (se 1 (by rfl) ⟨466151, by rfl⟩ : syracuseStep 621535 = 932303) B932303
theorem B621595 : Blo 618297 621595 := bstep (se 1 (by rfl) ⟨466196, by rfl⟩ : syracuseStep 621595 = 932393) B932393
theorem B4717601 : Blo 618297 4717601 := bstep (se 2 (by rfl) ⟨1769100, by rfl⟩ : syracuseStep 4717601 = 3538201) B3538201
theorem B883867 : Blo 618297 883867 := bstep (se 1 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 883867 = 1325801) B1325801
theorem B621723 : Blo 618297 621723 := bstep (se 1 (by rfl) ⟨466292, by rfl⟩ : syracuseStep 621723 = 932585) B932585
theorem B1768691 : Blo 618297 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B621979 : Blo 618297 621979 := bstep (se 1 (by rfl) ⟨466484, by rfl⟩ : syracuseStep 621979 = 932969) B932969
theorem B1768873 : Blo 618297 1768873 := bstep (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) B1326655
theorem B622063 : Blo 618297 622063 := bstep (se 1 (by rfl) ⟨466547, by rfl⟩ : syracuseStep 622063 = 933095) B933095
theorem B3145391 : Blo 618297 3145391 := bstep (se 1 (by rfl) ⟨2359043, by rfl⟩ : syracuseStep 3145391 = 4718087) B4718087
theorem B3538727 : Blo 618297 3538727 := bstep (se 1 (by rfl) ⟨2654045, by rfl⟩ : syracuseStep 3538727 = 5308091) B5308091
theorem B786287 : Blo 618297 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B1048457 : Blo 618297 1048457 := bstep (se 2 (by rfl) ⟨393171, by rfl⟩ : syracuseStep 1048457 = 786343) B786343
theorem B2097035 : Blo 618297 2097035 := bstep (se 1 (by rfl) ⟨1572776, by rfl⟩ : syracuseStep 2097035 = 3145553) B3145553
theorem B2654471 : Blo 618297 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B1180327 : Blo 618297 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B1049375 : Blo 618297 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B1180487 : Blo 618297 1180487 := bstep (se 1 (by rfl) ⟨885365, by rfl⟩ : syracuseStep 1180487 = 1770731) B1770731
theorem B35783693 : Blo 618297 35783693 := bstep (se 3 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 35783693 = 13418885) B13418885
theorem B2098331 : Blo 618297 2098331 := bstep (se 1 (by rfl) ⟨1573748, by rfl⟩ : syracuseStep 2098331 = 3147497) B3147497
theorem B1050023 : Blo 618297 1050023 := bstep (se 1 (by rfl) ⟨787517, by rfl⟩ : syracuseStep 1050023 = 1575035) B1575035
theorem B8947259 : Blo 618297 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B2098871 : Blo 618297 2098871 := bstep (se 1 (by rfl) ⟨1574153, by rfl⟩ : syracuseStep 2098871 = 3148307) B3148307
theorem B3147659 : Blo 618297 3147659 := bstep (se 1 (by rfl) ⟨2360744, by rfl⟩ : syracuseStep 3147659 = 4721489) B4721489
theorem B1673209 : Blo 618297 1673209 := bstep (se 2 (by rfl) ⟨627453, by rfl⟩ : syracuseStep 1673209 = 1254907) B1254907
theorem B1509715 : Blo 618297 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B1608185 : Blo 618297 1608185 := bstep (se 2 (by rfl) ⟨603069, by rfl⟩ : syracuseStep 1608185 = 1206139) B1206139
theorem B3967613 : Blo 618297 3967613 := bstep (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) B1487855
theorem B2362081 : Blo 618297 2362081 := bstep (se 2 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 2362081 = 1771561) B1771561
theorem B2099951 : Blo 618297 2099951 := bstep (se 1 (by rfl) ⟨1574963, by rfl⟩ : syracuseStep 2099951 = 3149927) B3149927
theorem B120720131 : Blo 618297 120720131 := bstep (se 1 (by rfl) ⟨90540098, by rfl⟩ : syracuseStep 120720131 = 181080197) B181080197
theorem B2100221 : Blo 618297 2100221 := bstep (se 3 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 2100221 = 787583) B787583
theorem B2985245 : Blo 618297 2985245 := bstep (se 3 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 2985245 = 1119467) B1119467
theorem B1118443 : Blo 618297 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B18160301 : Blo 618297 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B11443463 : Blo 618297 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B24157601 : Blo 618297 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B663071 : Blo 618297 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B4235095 : Blo 618297 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B4531423 : Blo 618297 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B4466249 : Blo 618297 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B7055261 : Blo 618297 7055261 := bstep (se 3 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 7055261 = 2645723) B2645723
theorem B927881 : Blo 618297 927881 := bstep (se 2 (by rfl) ⟨347955, by rfl⟩ : syracuseStep 927881 = 695911) B695911
theorem B698971 : Blo 618297 698971 := bstep (se 1 (by rfl) ⟨524228, by rfl⟩ : syracuseStep 698971 = 1048457) B1048457
theorem B7940861 : Blo 618297 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B928553 : Blo 618297 928553 := bstep (se 2 (by rfl) ⟨348207, by rfl⟩ : syracuseStep 928553 = 696415) B696415
theorem B699259 : Blo 618297 699259 := bstep (se 1 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 699259 = 1048889) B1048889
theorem B928745 : Blo 618297 928745 := bstep (se 2 (by rfl) ⟨348279, by rfl⟩ : syracuseStep 928745 = 696559) B696559
theorem B929231 : Blo 618297 929231 := bstep (se 1 (by rfl) ⟨696923, by rfl⟩ : syracuseStep 929231 = 1393847) B1393847
theorem B929327 : Blo 618297 929327 := bstep (se 1 (by rfl) ⟨696995, by rfl⟩ : syracuseStep 929327 = 1393991) B1393991
theorem B10628819 : Blo 618297 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B5976251 : Blo 618297 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B929999 : Blo 618297 929999 := bstep (se 1 (by rfl) ⟨697499, by rfl⟩ : syracuseStep 929999 = 1394999) B1394999
theorem B930119 : Blo 618297 930119 := bstep (se 1 (by rfl) ⟨697589, by rfl⟩ : syracuseStep 930119 = 1395179) B1395179
theorem B1487567 : Blo 618297 1487567 := bstep (se 1 (by rfl) ⟨1115675, by rfl⟩ : syracuseStep 1487567 = 2231351) B2231351
theorem B1324127 : Blo 618297 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B930911 : Blo 618297 930911 := bstep (se 1 (by rfl) ⟨698183, by rfl⟩ : syracuseStep 930911 = 1396367) B1396367
theorem B930971 : Blo 618297 930971 := bstep (se 1 (by rfl) ⟨698228, by rfl⟩ : syracuseStep 930971 = 1396457) B1396457
theorem B3028157 : Blo 618297 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B931817 : Blo 618297 931817 := bstep (se 2 (by rfl) ⟨349431, by rfl⟩ : syracuseStep 931817 = 698863) B698863
theorem B4765715 : Blo 618297 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B932447 : Blo 618297 932447 := bstep (se 1 (by rfl) ⟨699335, by rfl⟩ : syracuseStep 932447 = 1398671) B1398671
theorem B1391471 : Blo 618297 1391471 := bstep (se 1 (by rfl) ⟨1043603, by rfl⟩ : syracuseStep 1391471 = 2087207) B2087207
theorem B1063919 : Blo 618297 1063919 := bstep (se 1 (by rfl) ⟨797939, by rfl⟩ : syracuseStep 1063919 = 1595879) B1595879
theorem B21740557 : Blo 618297 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B932927 : Blo 618297 932927 := bstep (se 1 (by rfl) ⟨699695, by rfl⟩ : syracuseStep 932927 = 1399391) B1399391
theorem B933275 : Blo 618297 933275 := bstep (se 1 (by rfl) ⟨699956, by rfl⟩ : syracuseStep 933275 = 1399913) B1399913
theorem B1392047 : Blo 618297 1392047 := bstep (se 1 (by rfl) ⟨1044035, by rfl⟩ : syracuseStep 1392047 = 2088071) B2088071
theorem B3521981 : Blo 618297 3521981 := bstep (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) B1320743
theorem B5947343 : Blo 618297 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B1392713 : Blo 618297 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B1491065 : Blo 618297 1491065 := bstep (se 2 (by rfl) ⟨559149, by rfl⟩ : syracuseStep 1491065 = 1118299) B1118299
theorem B1491295 : Blo 618297 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B5357963 : Blo 618297 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1393127 : Blo 618297 1393127 := bstep (se 1 (by rfl) ⟨1044845, by rfl⟩ : syracuseStep 1393127 = 2089691) B2089691
theorem B16302791 : Blo 618297 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B4704479 : Blo 618297 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B7948651 : Blo 618297 7948651 := bstep (se 1 (by rfl) ⟨5961488, by rfl⟩ : syracuseStep 7948651 = 11922977) B11922977
theorem B3131945 : Blo 618297 3131945 := bstep (se 2 (by rfl) ⟨1174479, by rfl⟩ : syracuseStep 3131945 = 2348959) B2348959
theorem B1396025 : Blo 618297 1396025 := bstep (se 2 (by rfl) ⟨523509, by rfl⟩ : syracuseStep 1396025 = 1047019) B1047019
theorem B1396691 : Blo 618297 1396691 := bstep (se 1 (by rfl) ⟨1047518, by rfl⟩ : syracuseStep 1396691 = 2095037) B2095037
theorem B1396763 : Blo 618297 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B2642017 : Blo 618297 2642017 := bstep (se 2 (by rfl) ⟨990756, by rfl⟩ : syracuseStep 2642017 = 1981513) B1981513
theorem B4248071 : Blo 618297 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B13390865 : Blo 618297 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B1398023 : Blo 618297 1398023 := bstep (se 1 (by rfl) ⟨1048517, by rfl⟩ : syracuseStep 1398023 = 2097035) B2097035
theorem B1398383 : Blo 618297 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B2545537 : Blo 618297 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B2414623 : Blo 618297 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B3528953 : Blo 618297 3528953 := bstep (se 2 (by rfl) ⟨1323357, by rfl⟩ : syracuseStep 3528953 = 2646715) B2646715
theorem B1399067 : Blo 618297 1399067 := bstep (se 1 (by rfl) ⟨1049300, by rfl⟩ : syracuseStep 1399067 = 2098601) B2098601
theorem B2349431 : Blo 618297 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B10771217 : Blo 618297 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B1400039 : Blo 618297 1400039 := bstep (se 1 (by rfl) ⟨1050029, by rfl⟩ : syracuseStep 1400039 = 2100059) B2100059
theorem B2088179 : Blo 618297 2088179 := bstep (se 1 (by rfl) ⟨1566134, by rfl⟩ : syracuseStep 2088179 = 3132269) B3132269
theorem B43080983 : Blo 618297 43080983 := bstep (se 1 (by rfl) ⟨32310737, by rfl⟩ : syracuseStep 43080983 = 64621475) B64621475
theorem B7953983 : Blo 618297 7953983 := bstep (se 1 (by rfl) ⟨5965487, by rfl⟩ : syracuseStep 7953983 = 11930975) B11930975
theorem B3137453 : Blo 618297 3137453 := bstep (se 3 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 3137453 = 1176545) B1176545
theorem B3137615 : Blo 618297 3137615 := bstep (se 1 (by rfl) ⟨2353211, by rfl⟩ : syracuseStep 3137615 = 4706423) B4706423
theorem B2089259 : Blo 618297 2089259 := bstep (se 1 (by rfl) ⟨1566944, by rfl⟩ : syracuseStep 2089259 = 3133889) B3133889
theorem B32137829 : Blo 618297 32137829 := bstep (se 4 (by rfl) ⟨3012921, by rfl⟩ : syracuseStep 32137829 = 6025843) B6025843
theorem B22569635 : Blo 618297 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B2090123 : Blo 618297 2090123 := bstep (se 1 (by rfl) ⟨1567592, by rfl⟩ : syracuseStep 2090123 = 3135185) B3135185
theorem B101770951 : Blo 618297 101770951 := bstep (se 1 (by rfl) ⟨76328213, by rfl⟩ : syracuseStep 101770951 = 152656427) B152656427
theorem B4253597 : Blo 618297 4253597 := bstep (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) B1595099
theorem B4253705 : Blo 618297 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B2353319 : Blo 618297 2353319 := bstep (se 1 (by rfl) ⟨1764989, by rfl⟩ : syracuseStep 2353319 = 3529979) B3529979
theorem B34007303 : Blo 618297 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B1174313 : Blo 618297 1174313 := bstep (se 2 (by rfl) ⟨440367, by rfl⟩ : syracuseStep 1174313 = 880735) B880735
theorem B1043563 : Blo 618297 1043563 := bstep (se 1 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 1043563 = 1565345) B1565345
theorem B2354305 : Blo 618297 2354305 := bstep (se 2 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 2354305 = 1765729) B1765729
theorem B1174753 : Blo 618297 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B1568231 : Blo 618297 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B1043995 : Blo 618297 1043995 := bstep (se 1 (by rfl) ⟨782996, by rfl⟩ : syracuseStep 1043995 = 1565993) B1565993
theorem B618331 : Blo 618297 618331 := bstep (se 1 (by rfl) ⟨463748, by rfl⟩ : syracuseStep 618331 = 927497) B927497
theorem B618351 : Blo 618297 618351 := bstep (se 1 (by rfl) ⟨463763, by rfl⟩ : syracuseStep 618351 = 927527) B927527
theorem B2355065 : Blo 618297 2355065 := bstep (se 2 (by rfl) ⟨883149, by rfl⟩ : syracuseStep 2355065 = 1766299) B1766299
theorem B2093039 : Blo 618297 2093039 := bstep (se 1 (by rfl) ⟨1569779, by rfl⟩ : syracuseStep 2093039 = 3139559) B3139559
theorem B2355263 : Blo 618297 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B4714685 : Blo 618297 4714685 := bstep (se 3 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 4714685 = 1768007) B1768007
theorem B2093255 : Blo 618297 2093255 := bstep (se 1 (by rfl) ⟨1569941, by rfl⟩ : syracuseStep 2093255 = 3139883) B3139883
theorem B1175771 : Blo 618297 1175771 := bstep (se 1 (by rfl) ⟨881828, by rfl⟩ : syracuseStep 1175771 = 1763657) B1763657
theorem B618751 : Blo 618297 618751 := bstep (se 1 (by rfl) ⟨464063, by rfl⟩ : syracuseStep 618751 = 928127) B928127
theorem B4485419 : Blo 618297 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B1044859 : Blo 618297 1044859 := bstep (se 1 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 1044859 = 1567289) B1567289
theorem B2978171 : Blo 618297 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B618911 : Blo 618297 618911 := bstep (se 1 (by rfl) ⟨464183, by rfl⟩ : syracuseStep 618911 = 928367) B928367
theorem B619055 : Blo 618297 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B13759105 : Blo 618297 13759105 := bstep (se 2 (by rfl) ⟨5159664, by rfl⟩ : syracuseStep 13759105 = 10319329) B10319329
theorem B36238241 : Blo 618297 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B619455 : Blo 618297 619455 := bstep (se 1 (by rfl) ⟨464591, by rfl⟩ : syracuseStep 619455 = 929183) B929183
theorem B619631 : Blo 618297 619631 := bstep (se 1 (by rfl) ⟨464723, by rfl⟩ : syracuseStep 619631 = 929447) B929447
theorem B1176697 : Blo 618297 1176697 := bstep (se 2 (by rfl) ⟨441261, by rfl⟩ : syracuseStep 1176697 = 882523) B882523
theorem B619647 : Blo 618297 619647 := bstep (se 1 (by rfl) ⟨464735, by rfl⟩ : syracuseStep 619647 = 929471) B929471
theorem B619711 : Blo 618297 619711 := bstep (se 1 (by rfl) ⟨464783, by rfl⟩ : syracuseStep 619711 = 929567) B929567
theorem B38303027 : Blo 618297 38303027 := bstep (se 1 (by rfl) ⟨28727270, by rfl⟩ : syracuseStep 38303027 = 57454541) B57454541
theorem B783695 : Blo 618297 783695 := bstep (se 1 (by rfl) ⟨587771, by rfl⟩ : syracuseStep 783695 = 1175543) B1175543
theorem B17921371 : Blo 618297 17921371 := bstep (se 1 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 17921371 = 26882057) B26882057
theorem B619903 : Blo 618297 619903 := bstep (se 1 (by rfl) ⟨464927, by rfl⟩ : syracuseStep 619903 = 929855) B929855
theorem B14349797 : Blo 618297 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B620031 : Blo 618297 620031 := bstep (se 1 (by rfl) ⟨465023, by rfl⟩ : syracuseStep 620031 = 930047) B930047
theorem B620059 : Blo 618297 620059 := bstep (se 1 (by rfl) ⟨465044, by rfl⟩ : syracuseStep 620059 = 930089) B930089
theorem B1570367 : Blo 618297 1570367 := bstep (se 1 (by rfl) ⟨1177775, by rfl⟩ : syracuseStep 1570367 = 2355551) B2355551
theorem B620239 : Blo 618297 620239 := bstep (se 1 (by rfl) ⟨465179, by rfl⟩ : syracuseStep 620239 = 930359) B930359
theorem B3536743 : Blo 618297 3536743 := bstep (se 1 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 3536743 = 5305115) B5305115
theorem B620399 : Blo 618297 620399 := bstep (se 1 (by rfl) ⟨465299, by rfl⟩ : syracuseStep 620399 = 930599) B930599
theorem B620479 : Blo 618297 620479 := bstep (se 1 (by rfl) ⟨465359, by rfl⟩ : syracuseStep 620479 = 930719) B930719
theorem B784495 : Blo 618297 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B620795 : Blo 618297 620795 := bstep (se 1 (by rfl) ⟨465596, by rfl⟩ : syracuseStep 620795 = 931193) B931193
theorem B620799 : Blo 618297 620799 := bstep (se 1 (by rfl) ⟨465599, by rfl⟩ : syracuseStep 620799 = 931199) B931199
theorem B620903 : Blo 618297 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B621023 : Blo 618297 621023 := bstep (se 1 (by rfl) ⟨465767, by rfl⟩ : syracuseStep 621023 = 931535) B931535
theorem B621159 : Blo 618297 621159 := bstep (se 1 (by rfl) ⟨465869, by rfl⟩ : syracuseStep 621159 = 931739) B931739
theorem B621183 : Blo 618297 621183 := bstep (se 1 (by rfl) ⟨465887, by rfl⟩ : syracuseStep 621183 = 931775) B931775
theorem B1571471 : Blo 618297 1571471 := bstep (se 1 (by rfl) ⟨1178603, by rfl⟩ : syracuseStep 1571471 = 2357207) B2357207
theorem B3963563 : Blo 618297 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B621295 : Blo 618297 621295 := bstep (se 1 (by rfl) ⟨465971, by rfl⟩ : syracuseStep 621295 = 931943) B931943
theorem B2358011 : Blo 618297 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B1178489 : Blo 618297 1178489 := bstep (se 2 (by rfl) ⟨441933, by rfl⟩ : syracuseStep 1178489 = 883867) B883867
theorem B2096063 : Blo 618297 2096063 := bstep (se 1 (by rfl) ⟨1572047, by rfl⟩ : syracuseStep 2096063 = 3144095) B3144095
theorem B621551 : Blo 618297 621551 := bstep (se 1 (by rfl) ⟨466163, by rfl⟩ : syracuseStep 621551 = 932327) B932327
theorem B621599 : Blo 618297 621599 := bstep (se 1 (by rfl) ⟨466199, by rfl⟩ : syracuseStep 621599 = 932399) B932399
theorem B2358497 : Blo 618297 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B1047863 : Blo 618297 1047863 := bstep (se 1 (by rfl) ⟨785897, by rfl⟩ : syracuseStep 1047863 = 1571795) B1571795
theorem B3145067 : Blo 618297 3145067 := bstep (se 1 (by rfl) ⟨2358800, by rfl⟩ : syracuseStep 3145067 = 4717601) B4717601
theorem B622047 : Blo 618297 622047 := bstep (se 1 (by rfl) ⟨466535, by rfl⟩ : syracuseStep 622047 = 933071) B933071
theorem B1179127 : Blo 618297 1179127 := bstep (se 1 (by rfl) ⟨884345, by rfl⟩ : syracuseStep 1179127 = 1768691) B1768691
theorem B622107 : Blo 618297 622107 := bstep (se 1 (by rfl) ⟨466580, by rfl⟩ : syracuseStep 622107 = 933161) B933161
theorem B622127 : Blo 618297 622127 := bstep (se 1 (by rfl) ⟨466595, by rfl⟩ : syracuseStep 622127 = 933191) B933191
theorem B2096765 : Blo 618297 2096765 := bstep (se 3 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 2096765 = 786287) B786287
theorem B2096927 : Blo 618297 2096927 := bstep (se 1 (by rfl) ⟨1572695, by rfl⟩ : syracuseStep 2096927 = 3145391) B3145391
theorem B2359151 : Blo 618297 2359151 := bstep (se 1 (by rfl) ⟨1769363, by rfl⟩ : syracuseStep 2359151 = 3538727) B3538727
theorem B3571975 : Blo 618297 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B786991 : Blo 618297 786991 := bstep (se 1 (by rfl) ⟨590243, by rfl⟩ : syracuseStep 786991 = 1180487) B1180487
theorem B23855795 : Blo 618297 23855795 := bstep (se 1 (by rfl) ⟨17891846, by rfl⟩ : syracuseStep 23855795 = 35783693) B35783693
theorem B7078589 : Blo 618297 7078589 := bstep (se 3 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 7078589 = 2654471) B2654471
theorem B1573769 : Blo 618297 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B5964839 : Blo 618297 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B2098439 : Blo 618297 2098439 := bstep (se 1 (by rfl) ⟨1573829, by rfl⟩ : syracuseStep 2098439 = 3147659) B3147659
theorem B80480087 : Blo 618297 80480087 := bstep (se 1 (by rfl) ⟨60360065, by rfl⟩ : syracuseStep 80480087 = 120720131) B120720131
theorem B135694601 : Blo 618297 135694601 := bstep (se 2 (by rfl) ⟨50885475, by rfl⟩ : syracuseStep 135694601 = 101770951) B101770951
theorem B2230945 : Blo 618297 2230945 := bstep (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) B1673209
theorem B3149441 : Blo 618297 3149441 := bstep (se 2 (by rfl) ⟨1181040, by rfl⟩ : syracuseStep 3149441 = 2362081) B2362081
theorem B7180811 : Blo 618297 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B23895161 : Blo 618297 23895161 := bstep (se 2 (by rfl) ⟨8960685, by rfl⟩ : syracuseStep 23895161 = 17921371) B17921371
theorem B7085879 : Blo 618297 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B3219497 : Blo 618297 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B2990279 : Blo 618297 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B991711 : Blo 618297 991711 := bstep (se 1 (by rfl) ⟨743783, by rfl⟩ : syracuseStep 991711 = 1487567) B1487567
theorem B24158827 : Blo 618297 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B25535351 : Blo 618297 25535351 := bstep (se 1 (by rfl) ⟨19151513, by rfl⟩ : syracuseStep 25535351 = 38303027) B38303027
theorem B927647 : Blo 618297 927647 := bstep (se 1 (by rfl) ⟨695735, by rfl⟩ : syracuseStep 927647 = 1391471) B1391471
theorem B698575 : Blo 618297 698575 := bstep (se 1 (by rfl) ⟨523931, by rfl⟩ : syracuseStep 698575 = 1047863) B1047863
theorem B928031 : Blo 618297 928031 := bstep (se 1 (by rfl) ⟨696023, by rfl⟩ : syracuseStep 928031 = 1392047) B1392047
theorem B5646793 : Blo 618297 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B928475 : Blo 618297 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B994043 : Blo 618297 994043 := bstep (se 1 (by rfl) ⟨745532, by rfl⟩ : syracuseStep 994043 = 1491065) B1491065
theorem B928751 : Blo 618297 928751 := bstep (se 1 (by rfl) ⟨696563, by rfl⟩ : syracuseStep 928751 = 1393127) B1393127
theorem B699583 : Blo 618297 699583 := bstep (se 1 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 699583 = 1049375) B1049375
theorem B700015 : Blo 618297 700015 := bstep (se 1 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 700015 = 1050023) B1050023
theorem B6041897 : Blo 618297 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B930683 : Blo 618297 930683 := bstep (se 1 (by rfl) ⟨698012, by rfl⟩ : syracuseStep 930683 = 1396025) B1396025
theorem B931127 : Blo 618297 931127 := bstep (se 1 (by rfl) ⟨698345, by rfl⟩ : syracuseStep 931127 = 1396691) B1396691
theorem B931175 : Blo 618297 931175 := bstep (se 1 (by rfl) ⟨698381, by rfl⟩ : syracuseStep 931175 = 1396763) B1396763
theorem B2832047 : Blo 618297 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B2012953 : Blo 618297 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B10598201 : Blo 618297 10598201 := bstep (se 2 (by rfl) ⟨3974325, by rfl⟩ : syracuseStep 10598201 = 7948651) B7948651
theorem B8927243 : Blo 618297 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B931961 : Blo 618297 931961 := bstep (se 2 (by rfl) ⟨349485, by rfl⟩ : syracuseStep 931961 = 698971) B698971
theorem B932015 : Blo 618297 932015 := bstep (se 1 (by rfl) ⟨699011, by rfl⟩ : syracuseStep 932015 = 1398023) B1398023
theorem B932255 : Blo 618297 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B932345 : Blo 618297 932345 := bstep (se 2 (by rfl) ⟨349629, by rfl⟩ : syracuseStep 932345 = 699259) B699259
theorem B1391417 : Blo 618297 1391417 := bstep (se 2 (by rfl) ⟨521781, by rfl⟩ : syracuseStep 1391417 = 1043563) B1043563
theorem B932711 : Blo 618297 932711 := bstep (se 1 (by rfl) ⟨699533, by rfl⟩ : syracuseStep 932711 = 1399067) B1399067
theorem B12106867 : Blo 618297 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B1391993 : Blo 618297 1391993 := bstep (se 2 (by rfl) ⟨521997, by rfl⟩ : syracuseStep 1391993 = 1043995) B1043995
theorem B933359 : Blo 618297 933359 := bstep (se 1 (by rfl) ⟨700019, by rfl⟩ : syracuseStep 933359 = 1400039) B1400039
theorem B1392119 : Blo 618297 1392119 := bstep (se 1 (by rfl) ⟨1044089, by rfl⟩ : syracuseStep 1392119 = 2088179) B2088179
theorem B28720655 : Blo 618297 28720655 := bstep (se 1 (by rfl) ⟨21540491, by rfl⟩ : syracuseStep 28720655 = 43080983) B43080983
theorem B16105067 : Blo 618297 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B3522689 : Blo 618297 3522689 := bstep (se 2 (by rfl) ⟨1321008, by rfl⟩ : syracuseStep 3522689 = 2642017) B2642017
theorem B1392839 : Blo 618297 1392839 := bstep (se 1 (by rfl) ⟨1044629, by rfl⟩ : syracuseStep 1392839 = 2089259) B2089259
theorem B1491257 : Blo 618297 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B1393145 : Blo 618297 1393145 := bstep (se 2 (by rfl) ⟨522429, by rfl⟩ : syracuseStep 1393145 = 1044859) B1044859
theorem B1393415 : Blo 618297 1393415 := bstep (se 1 (by rfl) ⟨1045061, by rfl⟩ : syracuseStep 1393415 = 2090123) B2090123
theorem B4703507 : Blo 618297 4703507 := bstep (se 1 (by rfl) ⟨3527630, by rfl⟩ : syracuseStep 4703507 = 7055261) B7055261
theorem B2835731 : Blo 618297 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B2835803 : Blo 618297 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B5293907 : Blo 618297 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B3394049 : Blo 618297 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B1395359 : Blo 618297 1395359 := bstep (se 1 (by rfl) ⟨1046519, by rfl⟩ : syracuseStep 1395359 = 2093039) B2093039
theorem B3984167 : Blo 618297 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B1395503 : Blo 618297 1395503 := bstep (se 1 (by rfl) ⟨1046627, by rfl⟩ : syracuseStep 1395503 = 2093255) B2093255
theorem B1985447 : Blo 618297 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B2018771 : Blo 618297 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B28987409 : Blo 618297 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B2642375 : Blo 618297 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B1397375 : Blo 618297 1397375 := bstep (se 1 (by rfl) ⟨1048031, by rfl⟩ : syracuseStep 1397375 = 2096063) B2096063
theorem B709279 : Blo 618297 709279 := bstep (se 1 (by rfl) ⟨531959, by rfl⟩ : syracuseStep 709279 = 1063919) B1063919
theorem B2347987 : Blo 618297 2347987 := bstep (se 1 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 2347987 = 3521981) B3521981
theorem B1397843 : Blo 618297 1397843 := bstep (se 1 (by rfl) ⟨1048382, by rfl⟩ : syracuseStep 1397843 = 2096765) B2096765
theorem B1397951 : Blo 618297 1397951 := bstep (se 1 (by rfl) ⟨1048463, by rfl⟩ : syracuseStep 1397951 = 2096927) B2096927
theorem B1988393 : Blo 618297 1988393 := bstep (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) B1491295
theorem B10868527 : Blo 618297 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B1398887 : Blo 618297 1398887 := bstep (se 1 (by rfl) ⟨1049165, by rfl⟩ : syracuseStep 1398887 = 2098331) B2098331
theorem B1399247 : Blo 618297 1399247 := bstep (se 1 (by rfl) ⟨1049435, by rfl⟩ : syracuseStep 1399247 = 2098871) B2098871
theorem B3136319 : Blo 618297 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B1072123 : Blo 618297 1072123 := bstep (se 1 (by rfl) ⟨804092, by rfl⟩ : syracuseStep 1072123 = 1608185) B1608185
theorem B2087963 : Blo 618297 2087963 := bstep (se 1 (by rfl) ⟨1565972, by rfl⟩ : syracuseStep 2087963 = 3131945) B3131945
theorem B2645075 : Blo 618297 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B60185693 : Blo 618297 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B1399967 : Blo 618297 1399967 := bstep (se 1 (by rfl) ⟨1049975, by rfl⟩ : syracuseStep 1399967 = 2099951) B2099951
theorem B1400147 : Blo 618297 1400147 := bstep (se 1 (by rfl) ⟨1050110, by rfl⟩ : syracuseStep 1400147 = 2100221) B2100221
theorem B1990163 : Blo 618297 1990163 := bstep (se 1 (by rfl) ⟨1492622, by rfl⟩ : syracuseStep 1990163 = 2985245) B2985245
theorem B2089853 : Blo 618297 2089853 := bstep (se 3 (by rfl) ⟨391847, by rfl⟩ : syracuseStep 2089853 = 783695) B783695
theorem B2352635 : Blo 618297 2352635 := bstep (se 1 (by rfl) ⟨1764476, by rfl⟩ : syracuseStep 2352635 = 3528953) B3528953
theorem B3139073 : Blo 618297 3139073 := bstep (se 2 (by rfl) ⟨1177152, by rfl⟩ : syracuseStep 3139073 = 2354305) B2354305
theorem B1566287 : Blo 618297 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1566337 : Blo 618297 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B7628975 : Blo 618297 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B5302655 : Blo 618297 5302655 := bstep (se 1 (by rfl) ⟨3976991, by rfl⟩ : syracuseStep 5302655 = 7953983) B7953983
theorem B2091635 : Blo 618297 2091635 := bstep (se 1 (by rfl) ⟨1568726, by rfl⟩ : syracuseStep 2091635 = 3137453) B3137453
theorem B2091743 : Blo 618297 2091743 := bstep (se 1 (by rfl) ⟨1568807, by rfl⟩ : syracuseStep 2091743 = 3137615) B3137615
theorem B7072757 : Blo 618297 7072757 := bstep (se 5 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 7072757 = 663071) B663071
theorem B21425219 : Blo 618297 21425219 := bstep (se 1 (by rfl) ⟨16068914, by rfl⟩ : syracuseStep 21425219 = 32137829) B32137829
theorem B18345473 : Blo 618297 18345473 := bstep (se 2 (by rfl) ⟨6879552, by rfl⟩ : syracuseStep 18345473 = 13759105) B13759105
theorem B2977499 : Blo 618297 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B618587 : Blo 618297 618587 := bstep (se 1 (by rfl) ⟨463940, by rfl⟩ : syracuseStep 618587 = 927881) B927881
theorem B1568879 : Blo 618297 1568879 := bstep (se 1 (by rfl) ⟨1176659, by rfl⟩ : syracuseStep 1568879 = 2353319) B2353319
theorem B1568929 : Blo 618297 1568929 := bstep (se 2 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 1568929 = 1176697) B1176697
theorem B22671535 : Blo 618297 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B782875 : Blo 618297 782875 := bstep (se 1 (by rfl) ⟨587156, by rfl⟩ : syracuseStep 782875 = 1174313) B1174313
theorem B619035 : Blo 618297 619035 := bstep (se 1 (by rfl) ⟨464276, by rfl⟩ : syracuseStep 619035 = 928553) B928553
theorem B619163 : Blo 618297 619163 := bstep (se 1 (by rfl) ⟨464372, by rfl⟩ : syracuseStep 619163 = 928745) B928745
theorem B619487 : Blo 618297 619487 := bstep (se 1 (by rfl) ⟨464615, by rfl⟩ : syracuseStep 619487 = 929231) B929231
theorem B3142637 : Blo 618297 3142637 := bstep (se 3 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 3142637 = 1178489) B1178489
theorem B1045487 : Blo 618297 1045487 := bstep (se 1 (by rfl) ⟨784115, by rfl⟩ : syracuseStep 1045487 = 1568231) B1568231
theorem B619551 : Blo 618297 619551 := bstep (se 1 (by rfl) ⟨464663, by rfl⟩ : syracuseStep 619551 = 929327) B929327
theorem B4715657 : Blo 618297 4715657 := bstep (se 2 (by rfl) ⟨1768371, by rfl⟩ : syracuseStep 4715657 = 3536743) B3536743
theorem B1570043 : Blo 618297 1570043 := bstep (se 1 (by rfl) ⟨1177532, by rfl⟩ : syracuseStep 1570043 = 2355065) B2355065
theorem B1570175 : Blo 618297 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B3143123 : Blo 618297 3143123 := bstep (se 1 (by rfl) ⟨2357342, by rfl⟩ : syracuseStep 3143123 = 4714685) B4714685
theorem B619999 : Blo 618297 619999 := bstep (se 1 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 619999 = 929999) B929999
theorem B783847 : Blo 618297 783847 := bstep (se 1 (by rfl) ⟨587885, by rfl⟩ : syracuseStep 783847 = 1175771) B1175771
theorem B1045993 : Blo 618297 1045993 := bstep (se 2 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 1045993 = 784495) B784495
theorem B620079 : Blo 618297 620079 := bstep (se 1 (by rfl) ⟨465059, by rfl⟩ : syracuseStep 620079 = 930119) B930119
theorem B882751 : Blo 618297 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B620607 : Blo 618297 620607 := bstep (se 1 (by rfl) ⟨465455, by rfl⟩ : syracuseStep 620607 = 930911) B930911
theorem B620647 : Blo 618297 620647 := bstep (se 1 (by rfl) ⟨465485, by rfl⟩ : syracuseStep 620647 = 930971) B930971
theorem B9566531 : Blo 618297 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B1046911 : Blo 618297 1046911 := bstep (se 1 (by rfl) ⟨785183, by rfl⟩ : syracuseStep 1046911 = 1570367) B1570367
theorem B621211 : Blo 618297 621211 := bstep (se 1 (by rfl) ⟨465908, by rfl⟩ : syracuseStep 621211 = 931817) B931817
theorem B3177143 : Blo 618297 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B621631 : Blo 618297 621631 := bstep (se 1 (by rfl) ⟨466223, by rfl⟩ : syracuseStep 621631 = 932447) B932447
theorem B1047647 : Blo 618297 1047647 := bstep (se 1 (by rfl) ⟨785735, by rfl⟩ : syracuseStep 1047647 = 1571471) B1571471
theorem B1572007 : Blo 618297 1572007 := bstep (se 1 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 1572007 = 2358011) B2358011
theorem B1572169 : Blo 618297 1572169 := bstep (se 2 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 1572169 = 1179127) B1179127
theorem B621951 : Blo 618297 621951 := bstep (se 1 (by rfl) ⟨466463, by rfl⟩ : syracuseStep 621951 = 932927) B932927
theorem B1572331 : Blo 618297 1572331 := bstep (se 1 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 1572331 = 2358497) B2358497
theorem B2096711 : Blo 618297 2096711 := bstep (se 1 (by rfl) ⟨1572533, by rfl⟩ : syracuseStep 2096711 = 3145067) B3145067
theorem B622183 : Blo 618297 622183 := bstep (se 1 (by rfl) ⟨466637, by rfl⟩ : syracuseStep 622183 = 933275) B933275
theorem B1572767 : Blo 618297 1572767 := bstep (se 1 (by rfl) ⟨1179575, by rfl⟩ : syracuseStep 1572767 = 2359151) B2359151
theorem B3964895 : Blo 618297 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B77299757 : Blo 618297 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B4719059 : Blo 618297 4719059 := bstep (se 1 (by rfl) ⟨3539294, by rfl⟩ : syracuseStep 4719059 = 7078589) B7078589
theorem B1049179 : Blo 618297 1049179 := bstep (se 1 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 1049179 = 1573769) B1573769
theorem B1049321 : Blo 618297 1049321 := bstep (se 2 (by rfl) ⟨393495, by rfl⟩ : syracuseStep 1049321 = 786991) B786991
theorem B32211769 : Blo 618297 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B1345847 : Blo 618297 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B2099627 : Blo 618297 2099627 := bstep (se 1 (by rfl) ⟨1574720, by rfl⟩ : syracuseStep 2099627 = 3149441) B3149441
theorem B4787207 : Blo 618297 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B11898373 : Blo 618297 11898373 := bstep (se 4 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 11898373 = 2230945) B2230945
theorem B15930107 : Blo 618297 15930107 := bstep (se 1 (by rfl) ⟨11947580, by rfl⟩ : syracuseStep 15930107 = 23895161) B23895161
theorem B4723919 : Blo 618297 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B9050797 : Blo 618297 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B5085983 : Blo 618297 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B10624445 : Blo 618297 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B12230315 : Blo 618297 12230315 := bstep (se 1 (by rfl) ⟨9172736, by rfl⟩ : syracuseStep 12230315 = 18345473) B18345473
theorem B14491369 : Blo 618297 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B696991 : Blo 618297 696991 := bstep (se 1 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 696991 = 1045487) B1045487
theorem B927611 : Blo 618297 927611 := bstep (se 1 (by rfl) ⟨695708, by rfl⟩ : syracuseStep 927611 = 1391417) B1391417
theorem B698431 : Blo 618297 698431 := bstep (se 1 (by rfl) ⟨523823, by rfl⟩ : syracuseStep 698431 = 1047647) B1047647
theorem B927995 : Blo 618297 927995 := bstep (se 1 (by rfl) ⟨695996, by rfl⟩ : syracuseStep 927995 = 1391993) B1391993
theorem B928079 : Blo 618297 928079 := bstep (se 1 (by rfl) ⟨696059, by rfl⟩ : syracuseStep 928079 = 1392119) B1392119
theorem B19147103 : Blo 618297 19147103 := bstep (se 1 (by rfl) ⟨14360327, by rfl⟩ : syracuseStep 19147103 = 28720655) B28720655
theorem B928559 : Blo 618297 928559 := bstep (se 1 (by rfl) ⟨696419, by rfl⟩ : syracuseStep 928559 = 1392839) B1392839
theorem B928763 : Blo 618297 928763 := bstep (se 1 (by rfl) ⟨696572, by rfl⟩ : syracuseStep 928763 = 1393145) B1393145
theorem B4762633 : Blo 618297 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B15903863 : Blo 618297 15903863 := bstep (se 1 (by rfl) ⟨11927897, by rfl⟩ : syracuseStep 15903863 = 23855795) B23855795
theorem B928943 : Blo 618297 928943 := bstep (se 1 (by rfl) ⟨696707, by rfl⟩ : syracuseStep 928943 = 1393415) B1393415
theorem B1322281 : Blo 618297 1322281 := bstep (se 2 (by rfl) ⟨495855, by rfl⟩ : syracuseStep 1322281 = 991711) B991711
theorem B3976559 : Blo 618297 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B3976685 : Blo 618297 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B53653391 : Blo 618297 53653391 := bstep (se 1 (by rfl) ⟨40240043, by rfl⟩ : syracuseStep 53653391 = 80480087) B80480087
theorem B930239 : Blo 618297 930239 := bstep (se 1 (by rfl) ⟨697679, by rfl⟩ : syracuseStep 930239 = 1395359) B1395359
theorem B930335 : Blo 618297 930335 := bstep (se 1 (by rfl) ⟨697751, by rfl⟩ : syracuseStep 930335 = 1395503) B1395503
theorem B1323631 : Blo 618297 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B931433 : Blo 618297 931433 := bstep (se 2 (by rfl) ⟨349287, by rfl⟩ : syracuseStep 931433 = 698575) B698575
theorem B931583 : Blo 618297 931583 := bstep (se 1 (by rfl) ⟨698687, by rfl⟩ : syracuseStep 931583 = 1397375) B1397375
theorem B931895 : Blo 618297 931895 := bstep (se 1 (by rfl) ⟨698921, by rfl⟩ : syracuseStep 931895 = 1397843) B1397843
theorem B931967 : Blo 618297 931967 := bstep (se 1 (by rfl) ⟨698975, by rfl⟩ : syracuseStep 931967 = 1397951) B1397951
theorem B932591 : Blo 618297 932591 := bstep (se 1 (by rfl) ⟨699443, by rfl⟩ : syracuseStep 932591 = 1398887) B1398887
theorem B932777 : Blo 618297 932777 := bstep (se 2 (by rfl) ⟨349791, by rfl⟩ : syracuseStep 932777 = 699583) B699583
theorem B932831 : Blo 618297 932831 := bstep (se 1 (by rfl) ⟨699623, by rfl⟩ : syracuseStep 932831 = 1399247) B1399247
theorem B1391975 : Blo 618297 1391975 := bstep (se 1 (by rfl) ⟨1043981, by rfl⟩ : syracuseStep 1391975 = 2087963) B2087963
theorem B40123795 : Blo 618297 40123795 := bstep (se 1 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 40123795 = 60185693) B60185693
theorem B933311 : Blo 618297 933311 := bstep (se 1 (by rfl) ⟨699983, by rfl⟩ : syracuseStep 933311 = 1399967) B1399967
theorem B933353 : Blo 618297 933353 := bstep (se 2 (by rfl) ⟨350007, by rfl⟩ : syracuseStep 933353 = 700015) B700015
theorem B933431 : Blo 618297 933431 := bstep (se 1 (by rfl) ⟨700073, by rfl⟩ : syracuseStep 933431 = 1400147) B1400147
theorem B1326775 : Blo 618297 1326775 := bstep (se 1 (by rfl) ⟨995081, by rfl⟩ : syracuseStep 1326775 = 1990163) B1990163
theorem B5717989 : Blo 618297 5717989 := bstep (se 4 (by rfl) ⟨536061, by rfl⟩ : syracuseStep 5717989 = 1072123) B1072123
theorem B2146331 : Blo 618297 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B30228713 : Blo 618297 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B17023567 : Blo 618297 17023567 := bstep (se 1 (by rfl) ⟨12767675, by rfl⟩ : syracuseStep 17023567 = 25535351) B25535351
theorem B1393235 : Blo 618297 1393235 := bstep (se 1 (by rfl) ⟨1044926, by rfl⟩ : syracuseStep 1393235 = 2089853) B2089853
theorem B3130649 : Blo 618297 3130649 := bstep (se 2 (by rfl) ⟨1173993, by rfl⟩ : syracuseStep 3130649 = 2347987) B2347987
theorem B1394423 : Blo 618297 1394423 := bstep (se 1 (by rfl) ⟨1045817, by rfl⟩ : syracuseStep 1394423 = 2091635) B2091635
theorem B1394495 : Blo 618297 1394495 := bstep (se 1 (by rfl) ⟨1045871, by rfl⟩ : syracuseStep 1394495 = 2091743) B2091743
theorem B1394657 : Blo 618297 1394657 := bstep (se 2 (by rfl) ⟨522996, by rfl⟩ : syracuseStep 1394657 = 1045993) B1045993
theorem B1984999 : Blo 618297 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B1395881 : Blo 618297 1395881 := bstep (se 2 (by rfl) ⟨523455, by rfl⟩ : syracuseStep 1395881 = 1046911) B1046911
theorem B1888031 : Blo 618297 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B7065467 : Blo 618297 7065467 := bstep (se 1 (by rfl) ⟨5299100, by rfl⟩ : syracuseStep 7065467 = 10598201) B10598201
theorem B5951495 : Blo 618297 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B16142489 : Blo 618297 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B6377687 : Blo 618297 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B2118095 : Blo 618297 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B1397807 : Blo 618297 1397807 := bstep (se 1 (by rfl) ⟨1048355, by rfl⟩ : syracuseStep 1397807 = 2096711) B2096711
theorem B10736711 : Blo 618297 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B2643263 : Blo 618297 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B2348459 : Blo 618297 2348459 := bstep (se 1 (by rfl) ⟨1761344, by rfl⟩ : syracuseStep 2348459 = 3522689) B3522689
theorem B1398959 : Blo 618297 1398959 := bstep (se 1 (by rfl) ⟨1049219, by rfl⟩ : syracuseStep 1398959 = 2098439) B2098439
theorem B3135671 : Blo 618297 3135671 := bstep (se 1 (by rfl) ⟨2351753, by rfl⟩ : syracuseStep 3135671 = 4703507) B4703507
theorem B1890487 : Blo 618297 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B1890535 : Blo 618297 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B3529271 : Blo 618297 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B90463067 : Blo 618297 90463067 := bstep (se 1 (by rfl) ⟨67847300, by rfl⟩ : syracuseStep 90463067 = 135694601) B135694601
theorem B2088449 : Blo 618297 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B1761583 : Blo 618297 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B7529057 : Blo 618297 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B15131285 : Blo 618297 15131285 := bstep (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) B709279
theorem B2090879 : Blo 618297 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B1763383 : Blo 618297 1763383 := bstep (se 1 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 1763383 = 2645075) B2645075
theorem B5302381 : Blo 618297 5302381 := bstep (se 3 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 5302381 = 1988393) B1988393
theorem B1993519 : Blo 618297 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B2091905 : Blo 618297 2091905 := bstep (se 2 (by rfl) ⟨784464, by rfl⟩ : syracuseStep 2091905 = 1568929) B1568929
theorem B1043833 : Blo 618297 1043833 := bstep (se 2 (by rfl) ⟨391437, by rfl⟩ : syracuseStep 1043833 = 782875) B782875
theorem B1568423 : Blo 618297 1568423 := bstep (se 1 (by rfl) ⟨1176317, by rfl⟩ : syracuseStep 1568423 = 2352635) B2352635
theorem B2092715 : Blo 618297 2092715 := bstep (se 1 (by rfl) ⟨1569536, by rfl⟩ : syracuseStep 2092715 = 3139073) B3139073
theorem B1044191 : Blo 618297 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B618431 : Blo 618297 618431 := bstep (se 1 (by rfl) ⟨463823, by rfl⟩ : syracuseStep 618431 = 927647) B927647
theorem B618687 : Blo 618297 618687 := bstep (se 1 (by rfl) ⟨464015, by rfl⟩ : syracuseStep 618687 = 928031) B928031
theorem B3535103 : Blo 618297 3535103 := bstep (se 1 (by rfl) ⟨2651327, by rfl⟩ : syracuseStep 3535103 = 5302655) B5302655
theorem B618983 : Blo 618297 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B1045129 : Blo 618297 1045129 := bstep (se 2 (by rfl) ⟨391923, by rfl⟩ : syracuseStep 1045129 = 783847) B783847
theorem B2650781 : Blo 618297 2650781 := bstep (se 3 (by rfl) ⟨497021, by rfl⟩ : syracuseStep 2650781 = 994043) B994043
theorem B619167 : Blo 618297 619167 := bstep (se 1 (by rfl) ⟨464375, by rfl⟩ : syracuseStep 619167 = 928751) B928751
theorem B4715171 : Blo 618297 4715171 := bstep (se 1 (by rfl) ⟨3536378, by rfl⟩ : syracuseStep 4715171 = 7072757) B7072757
theorem B14283479 : Blo 618297 14283479 := bstep (se 1 (by rfl) ⟨10712609, by rfl⟩ : syracuseStep 14283479 = 21425219) B21425219
theorem B2683937 : Blo 618297 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B1045919 : Blo 618297 1045919 := bstep (se 1 (by rfl) ⟨784439, by rfl⟩ : syracuseStep 1045919 = 1568879) B1568879
theorem B1177001 : Blo 618297 1177001 := bstep (se 2 (by rfl) ⟨441375, by rfl⟩ : syracuseStep 1177001 = 882751) B882751
theorem B4027931 : Blo 618297 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B620455 : Blo 618297 620455 := bstep (se 1 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 620455 = 930683) B930683
theorem B2095091 : Blo 618297 2095091 := bstep (se 1 (by rfl) ⟨1571318, by rfl⟩ : syracuseStep 2095091 = 3142637) B3142637
theorem B3143771 : Blo 618297 3143771 := bstep (se 1 (by rfl) ⟨2357828, by rfl⟩ : syracuseStep 3143771 = 4715657) B4715657
theorem B1046695 : Blo 618297 1046695 := bstep (se 1 (by rfl) ⟨785021, by rfl⟩ : syracuseStep 1046695 = 1570043) B1570043
theorem B620751 : Blo 618297 620751 := bstep (se 1 (by rfl) ⟨465563, by rfl⟩ : syracuseStep 620751 = 931127) B931127
theorem B620783 : Blo 618297 620783 := bstep (se 1 (by rfl) ⟨465587, by rfl⟩ : syracuseStep 620783 = 931175) B931175
theorem B1046783 : Blo 618297 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B2095415 : Blo 618297 2095415 := bstep (se 1 (by rfl) ⟨1571561, by rfl⟩ : syracuseStep 2095415 = 3143123) B3143123
theorem B621307 : Blo 618297 621307 := bstep (se 1 (by rfl) ⟨465980, by rfl⟩ : syracuseStep 621307 = 931961) B931961
theorem B621343 : Blo 618297 621343 := bstep (se 1 (by rfl) ⟨466007, by rfl⟩ : syracuseStep 621343 = 932015) B932015
theorem B2096009 : Blo 618297 2096009 := bstep (se 2 (by rfl) ⟨786003, by rfl⟩ : syracuseStep 2096009 = 1572007) B1572007
theorem B621503 : Blo 618297 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B621563 : Blo 618297 621563 := bstep (se 1 (by rfl) ⟨466172, by rfl⟩ : syracuseStep 621563 = 932345) B932345
theorem B2096225 : Blo 618297 2096225 := bstep (se 2 (by rfl) ⟨786084, by rfl⟩ : syracuseStep 2096225 = 1572169) B1572169
theorem B621807 : Blo 618297 621807 := bstep (se 1 (by rfl) ⟨466355, by rfl⟩ : syracuseStep 621807 = 932711) B932711
theorem B2096441 : Blo 618297 2096441 := bstep (se 2 (by rfl) ⟨786165, by rfl⟩ : syracuseStep 2096441 = 1572331) B1572331
theorem B622239 : Blo 618297 622239 := bstep (se 1 (by rfl) ⟨466679, by rfl⟩ : syracuseStep 622239 = 933359) B933359
theorem B1048511 : Blo 618297 1048511 := bstep (se 1 (by rfl) ⟨786383, by rfl⟩ : syracuseStep 1048511 = 1572767) B1572767
theorem B20152475 : Blo 618297 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B3146039 : Blo 618297 3146039 := bstep (se 1 (by rfl) ⟨2359529, by rfl⟩ : syracuseStep 3146039 = 4719059) B4719059
theorem B3967663 : Blo 618297 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B1412063 : Blo 618297 1412063 := bstep (se 1 (by rfl) ⟨1059047, by rfl⟩ : syracuseStep 1412063 = 2118095) B2118095
theorem B10620071 : Blo 618297 10620071 := bstep (se 1 (by rfl) ⟨7965053, by rfl⟩ : syracuseStep 10620071 = 15930107) B15930107
theorem B14355701 : Blo 618297 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B3149279 : Blo 618297 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B48270917 : Blo 618297 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B2658025 : Blo 618297 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B15864497 : Blo 618297 15864497 := bstep (se 2 (by rfl) ⟨5949186, by rfl⟩ : syracuseStep 15864497 = 11898373) B11898373
theorem B7082963 : Blo 618297 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B5019371 : Blo 618297 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B696127 : Blo 618297 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B697279 : Blo 618297 697279 := bstep (se 1 (by rfl) ⟨522959, by rfl⟩ : syracuseStep 697279 = 1045919) B1045919
theorem B697855 : Blo 618297 697855 := bstep (se 1 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 697855 = 1046783) B1046783
theorem B927983 : Blo 618297 927983 := bstep (se 1 (by rfl) ⟨695987, by rfl⟩ : syracuseStep 927983 = 1391975) B1391975
theorem B699007 : Blo 618297 699007 := bstep (se 1 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 699007 = 1048511) B1048511
theorem B928823 : Blo 618297 928823 := bstep (se 1 (by rfl) ⟨696617, by rfl⟩ : syracuseStep 928823 = 1393235) B1393235
theorem B699547 : Blo 618297 699547 := bstep (se 1 (by rfl) ⟨524660, by rfl⟩ : syracuseStep 699547 = 1049321) B1049321
theorem B929321 : Blo 618297 929321 := bstep (se 2 (by rfl) ⟨348495, by rfl⟩ : syracuseStep 929321 = 696991) B696991
theorem B929615 : Blo 618297 929615 := bstep (se 1 (by rfl) ⟨697211, by rfl⟩ : syracuseStep 929615 = 1394423) B1394423
theorem B929663 : Blo 618297 929663 := bstep (se 1 (by rfl) ⟨697247, by rfl⟩ : syracuseStep 929663 = 1394495) B1394495
theorem B929771 : Blo 618297 929771 := bstep (se 1 (by rfl) ⟨697328, by rfl⟩ : syracuseStep 929771 = 1394657) B1394657
theorem B3191471 : Blo 618297 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B930587 : Blo 618297 930587 := bstep (se 1 (by rfl) ⟨697940, by rfl⟩ : syracuseStep 930587 = 1395881) B1395881
theorem B1258687 : Blo 618297 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B931241 : Blo 618297 931241 := bstep (se 2 (by rfl) ⟨349215, by rfl⟩ : syracuseStep 931241 = 698431) B698431
theorem B10761659 : Blo 618297 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B931871 : Blo 618297 931871 := bstep (se 1 (by rfl) ⟨698903, by rfl⟩ : syracuseStep 931871 = 1397807) B1397807
theorem B7157807 : Blo 618297 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B932639 : Blo 618297 932639 := bstep (se 1 (by rfl) ⟨699479, by rfl⟩ : syracuseStep 932639 = 1398959) B1398959
theorem B1391777 : Blo 618297 1391777 := bstep (se 2 (by rfl) ⟨521916, by rfl⟩ : syracuseStep 1391777 = 1043833) B1043833
theorem B3390655 : Blo 618297 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B60308711 : Blo 618297 60308711 := bstep (se 1 (by rfl) ⟨45231533, by rfl⟩ : syracuseStep 60308711 = 90463067) B90463067
theorem B1392299 : Blo 618297 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B1393505 : Blo 618297 1393505 := bstep (se 2 (by rfl) ⟨522564, by rfl⟩ : syracuseStep 1393505 = 1045129) B1045129
theorem B1393919 : Blo 618297 1393919 := bstep (se 1 (by rfl) ⟨1045439, by rfl⟩ : syracuseStep 1393919 = 2090879) B2090879
theorem B12764735 : Blo 618297 12764735 := bstep (se 1 (by rfl) ⟨9573551, by rfl⟩ : syracuseStep 12764735 = 19147103) B19147103
theorem B1394603 : Blo 618297 1394603 := bstep (se 1 (by rfl) ⟨1045952, by rfl⟩ : syracuseStep 1394603 = 2091905) B2091905
theorem B10602575 : Blo 618297 10602575 := bstep (se 1 (by rfl) ⟨7951931, by rfl⟩ : syracuseStep 10602575 = 15903863) B15903863
theorem B1395143 : Blo 618297 1395143 := bstep (se 1 (by rfl) ⟨1046357, by rfl⟩ : syracuseStep 1395143 = 2092715) B2092715
theorem B35768927 : Blo 618297 35768927 := bstep (se 1 (by rfl) ⟨26826695, by rfl⟩ : syracuseStep 35768927 = 53653391) B53653391
theorem B1395593 : Blo 618297 1395593 := bstep (se 2 (by rfl) ⟨523347, by rfl⟩ : syracuseStep 1395593 = 1046695) B1046695
theorem B9522319 : Blo 618297 9522319 := bstep (se 1 (by rfl) ⟨7141739, by rfl⟩ : syracuseStep 9522319 = 14283479) B14283479
theorem B1789291 : Blo 618297 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B1396727 : Blo 618297 1396727 := bstep (se 1 (by rfl) ⟨1047545, by rfl⟩ : syracuseStep 1396727 = 2095091) B2095091
theorem B1396943 : Blo 618297 1396943 := bstep (se 1 (by rfl) ⟨1047707, by rfl⟩ : syracuseStep 1396943 = 2095415) B2095415
theorem B53498393 : Blo 618297 53498393 := bstep (se 2 (by rfl) ⟨20061897, by rfl⟩ : syracuseStep 53498393 = 40123795) B40123795
theorem B1397339 : Blo 618297 1397339 := bstep (se 1 (by rfl) ⟨1048004, by rfl⟩ : syracuseStep 1397339 = 2096009) B2096009
theorem B1397483 : Blo 618297 1397483 := bstep (se 1 (by rfl) ⟨1048112, by rfl⟩ : syracuseStep 1397483 = 2096225) B2096225
theorem B1397627 : Blo 618297 1397627 := bstep (se 1 (by rfl) ⟨1048220, by rfl⟩ : syracuseStep 1397627 = 2096441) B2096441
theorem B19321825 : Blo 618297 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B7623985 : Blo 618297 7623985 := bstep (se 2 (by rfl) ⟨2858994, by rfl⟩ : syracuseStep 7623985 = 5717989) B5717989
theorem B1430887 : Blo 618297 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B51533171 : Blo 618297 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B2348777 : Blo 618297 2348777 := bstep (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) B1761583
theorem B22698089 : Blo 618297 22698089 := bstep (se 2 (by rfl) ⟨8511783, by rfl⟩ : syracuseStep 22698089 = 17023567) B17023567
theorem B1398905 : Blo 618297 1398905 := bstep (se 2 (by rfl) ⟨524589, by rfl⟩ : syracuseStep 1398905 = 1049179) B1049179
theorem B2087099 : Blo 618297 2087099 := bstep (se 1 (by rfl) ⟨1565324, by rfl⟩ : syracuseStep 2087099 = 3130649) B3130649
theorem B42949025 : Blo 618297 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B1399751 : Blo 618297 1399751 := bstep (se 1 (by rfl) ⟨1049813, by rfl⟩ : syracuseStep 1399751 = 2099627) B2099627
theorem B4710311 : Blo 618297 4710311 := bstep (se 1 (by rfl) ⟨3532733, by rfl⟩ : syracuseStep 4710311 = 7065467) B7065467
theorem B2351177 : Blo 618297 2351177 := bstep (se 2 (by rfl) ⟨881691, by rfl⟩ : syracuseStep 2351177 = 1763383) B1763383
theorem B4251791 : Blo 618297 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B7069841 : Blo 618297 7069841 := bstep (se 2 (by rfl) ⟨2651190, by rfl⟩ : syracuseStep 7069841 = 5302381) B5302381
theorem B2646665 : Blo 618297 2646665 := bstep (se 2 (by rfl) ⟨992499, by rfl⟩ : syracuseStep 2646665 = 1984999) B1984999
theorem B1762175 : Blo 618297 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1565639 : Blo 618297 1565639 := bstep (se 1 (by rfl) ⟨1174229, by rfl⟩ : syracuseStep 1565639 = 2348459) B2348459
theorem B6350177 : Blo 618297 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B2090447 : Blo 618297 2090447 := bstep (se 1 (by rfl) ⟨1567835, by rfl⟩ : syracuseStep 2090447 = 3135671) B3135671
theorem B2352847 : Blo 618297 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B1763041 : Blo 618297 1763041 := bstep (se 2 (by rfl) ⟨661140, by rfl⟩ : syracuseStep 1763041 = 1322281) B1322281
theorem B8153543 : Blo 618297 8153543 := bstep (se 1 (by rfl) ⟨6115157, by rfl⟩ : syracuseStep 8153543 = 12230315) B12230315
theorem B10087523 : Blo 618297 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B1764841 : Blo 618297 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B618407 : Blo 618297 618407 := bstep (se 1 (by rfl) ⟨463805, by rfl⟩ : syracuseStep 618407 = 927611) B927611
theorem B618663 : Blo 618297 618663 := bstep (se 1 (by rfl) ⟨463997, by rfl⟩ : syracuseStep 618663 = 927995) B927995
theorem B618719 : Blo 618297 618719 := bstep (se 1 (by rfl) ⟨464039, by rfl⟩ : syracuseStep 618719 = 928079) B928079
theorem B619039 : Blo 618297 619039 := bstep (se 1 (by rfl) ⟨464279, by rfl⟩ : syracuseStep 619039 = 928559) B928559
theorem B619175 : Blo 618297 619175 := bstep (se 1 (by rfl) ⟨464381, by rfl⟩ : syracuseStep 619175 = 928763) B928763
theorem B619295 : Blo 618297 619295 := bstep (se 1 (by rfl) ⟨464471, by rfl⟩ : syracuseStep 619295 = 928943) B928943
theorem B2651039 : Blo 618297 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B2651123 : Blo 618297 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B1045615 : Blo 618297 1045615 := bstep (se 1 (by rfl) ⟨784211, by rfl⟩ : syracuseStep 1045615 = 1568423) B1568423
theorem B2356735 : Blo 618297 2356735 := bstep (se 1 (by rfl) ⟨1767551, by rfl⟩ : syracuseStep 2356735 = 3535103) B3535103
theorem B2520649 : Blo 618297 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B620159 : Blo 618297 620159 := bstep (se 1 (by rfl) ⟨465119, by rfl⟩ : syracuseStep 620159 = 930239) B930239
theorem B2520713 : Blo 618297 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B620223 : Blo 618297 620223 := bstep (se 1 (by rfl) ⟨465167, by rfl⟩ : syracuseStep 620223 = 930335) B930335
theorem B1767187 : Blo 618297 1767187 := bstep (se 1 (by rfl) ⟨1325390, by rfl⟩ : syracuseStep 1767187 = 2650781) B2650781
theorem B3143447 : Blo 618297 3143447 := bstep (se 1 (by rfl) ⟨2357585, by rfl⟩ : syracuseStep 3143447 = 4715171) B4715171
theorem B784667 : Blo 618297 784667 := bstep (se 1 (by rfl) ⟨588500, by rfl⟩ : syracuseStep 784667 = 1177001) B1177001
theorem B2685287 : Blo 618297 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B620955 : Blo 618297 620955 := bstep (se 1 (by rfl) ⟨465716, by rfl⟩ : syracuseStep 620955 = 931433) B931433
theorem B621055 : Blo 618297 621055 := bstep (se 1 (by rfl) ⟨465791, by rfl⟩ : syracuseStep 621055 = 931583) B931583
theorem B621263 : Blo 618297 621263 := bstep (se 1 (by rfl) ⟨465947, by rfl⟩ : syracuseStep 621263 = 931895) B931895
theorem B2095847 : Blo 618297 2095847 := bstep (se 1 (by rfl) ⟨1571885, by rfl⟩ : syracuseStep 2095847 = 3143771) B3143771
theorem B621311 : Blo 618297 621311 := bstep (se 1 (by rfl) ⟨465983, by rfl⟩ : syracuseStep 621311 = 931967) B931967
theorem B621727 : Blo 618297 621727 := bstep (se 1 (by rfl) ⟨466295, by rfl⟩ : syracuseStep 621727 = 932591) B932591
theorem B621851 : Blo 618297 621851 := bstep (se 1 (by rfl) ⟨466388, by rfl⟩ : syracuseStep 621851 = 932777) B932777
theorem B621887 : Blo 618297 621887 := bstep (se 1 (by rfl) ⟨466415, by rfl⟩ : syracuseStep 621887 = 932831) B932831
theorem B1769033 : Blo 618297 1769033 := bstep (se 2 (by rfl) ⟨663387, by rfl⟩ : syracuseStep 1769033 = 1326775) B1326775
theorem B622207 : Blo 618297 622207 := bstep (se 1 (by rfl) ⟨466655, by rfl⟩ : syracuseStep 622207 = 933311) B933311
theorem B622235 : Blo 618297 622235 := bstep (se 1 (by rfl) ⟨466676, by rfl⟩ : syracuseStep 622235 = 933353) B933353
theorem B622287 : Blo 618297 622287 := bstep (se 1 (by rfl) ⟨466715, by rfl⟩ : syracuseStep 622287 = 933431) B933431
theorem B13434983 : Blo 618297 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B2097359 : Blo 618297 2097359 := bstep (se 1 (by rfl) ⟨1573019, by rfl⟩ : syracuseStep 2097359 = 3146039) B3146039
theorem B7080047 : Blo 618297 7080047 := bstep (se 1 (by rfl) ⟨5310035, by rfl⟩ : syracuseStep 7080047 = 10620071) B10620071
theorem B9570467 : Blo 618297 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B2099519 : Blo 618297 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B4721975 : Blo 618297 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B3346247 : Blo 618297 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B3544033 : Blo 618297 3544033 := bstep (se 2 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 3544033 = 2658025) B2658025
theorem B25762433 : Blo 618297 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B1678249 : Blo 618297 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B10165313 : Blo 618297 10165313 := bstep (se 2 (by rfl) ⟨3811992, by rfl⟩ : syracuseStep 10165313 = 7623985) B7623985
theorem B1907849 : Blo 618297 1907849 := bstep (se 2 (by rfl) ⟨715443, by rfl⟩ : syracuseStep 1907849 = 1430887) B1430887
theorem B6725015 : Blo 618297 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B1680475 : Blo 618297 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B128722445 : Blo 618297 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B927851 : Blo 618297 927851 := bstep (se 1 (by rfl) ⟨695888, by rfl⟩ : syracuseStep 927851 = 1391777) B1391777
theorem B928169 : Blo 618297 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B928199 : Blo 618297 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B929003 : Blo 618297 929003 := bstep (se 1 (by rfl) ⟨696752, by rfl⟩ : syracuseStep 929003 = 1393505) B1393505
theorem B929279 : Blo 618297 929279 := bstep (se 1 (by rfl) ⟨696959, by rfl⟩ : syracuseStep 929279 = 1393919) B1393919
theorem B929705 : Blo 618297 929705 := bstep (se 2 (by rfl) ⟨348639, by rfl⟩ : syracuseStep 929705 = 697279) B697279
theorem B929735 : Blo 618297 929735 := bstep (se 1 (by rfl) ⟨697301, by rfl⟩ : syracuseStep 929735 = 1394603) B1394603
theorem B930095 : Blo 618297 930095 := bstep (se 1 (by rfl) ⟨697571, by rfl⟩ : syracuseStep 930095 = 1395143) B1395143
theorem B930395 : Blo 618297 930395 := bstep (se 1 (by rfl) ⟨697796, by rfl⟩ : syracuseStep 930395 = 1395593) B1395593
theorem B930473 : Blo 618297 930473 := bstep (se 2 (by rfl) ⟨348927, by rfl⟩ : syracuseStep 930473 = 697855) B697855
theorem B4699133 : Blo 618297 4699133 := bstep (se 3 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 4699133 = 1762175) B1762175
theorem B931151 : Blo 618297 931151 := bstep (se 1 (by rfl) ⟨698363, by rfl⟩ : syracuseStep 931151 = 1396727) B1396727
theorem B931295 : Blo 618297 931295 := bstep (se 1 (by rfl) ⟨698471, by rfl⟩ : syracuseStep 931295 = 1396943) B1396943
theorem B35665595 : Blo 618297 35665595 := bstep (se 1 (by rfl) ⟨26749196, by rfl⟩ : syracuseStep 35665595 = 53498393) B53498393
theorem B931559 : Blo 618297 931559 := bstep (se 1 (by rfl) ⟨698669, by rfl⟩ : syracuseStep 931559 = 1397339) B1397339
theorem B931655 : Blo 618297 931655 := bstep (se 1 (by rfl) ⟨698741, by rfl⟩ : syracuseStep 931655 = 1397483) B1397483
theorem B931751 : Blo 618297 931751 := bstep (se 1 (by rfl) ⟨698813, by rfl⟩ : syracuseStep 931751 = 1397627) B1397627
theorem B932009 : Blo 618297 932009 := bstep (se 2 (by rfl) ⟨349503, by rfl⟩ : syracuseStep 932009 = 699007) B699007
theorem B5290217 : Blo 618297 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B34355447 : Blo 618297 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B932603 : Blo 618297 932603 := bstep (se 1 (by rfl) ⟨699452, by rfl⟩ : syracuseStep 932603 = 1398905) B1398905
theorem B1391399 : Blo 618297 1391399 := bstep (se 1 (by rfl) ⟨1043549, by rfl⟩ : syracuseStep 1391399 = 2087099) B2087099
theorem B12696425 : Blo 618297 12696425 := bstep (se 2 (by rfl) ⟨4761159, by rfl⟩ : syracuseStep 12696425 = 9522319) B9522319
theorem B932729 : Blo 618297 932729 := bstep (se 2 (by rfl) ⟨349773, by rfl⟩ : syracuseStep 932729 = 699547) B699547
theorem B933167 : Blo 618297 933167 := bstep (se 1 (by rfl) ⟨699875, by rfl⟩ : syracuseStep 933167 = 1399751) B1399751
theorem B2834527 : Blo 618297 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B1393631 : Blo 618297 1393631 := bstep (se 1 (by rfl) ⟨1045223, by rfl⟩ : syracuseStep 1393631 = 2090447) B2090447
theorem B1394153 : Blo 618297 1394153 := bstep (se 2 (by rfl) ⟨522807, by rfl⟩ : syracuseStep 1394153 = 1045615) B1045615
theorem B3360865 : Blo 618297 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B4771871 : Blo 618297 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B1790191 : Blo 618297 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B1397231 : Blo 618297 1397231 := bstep (se 1 (by rfl) ⟨1047923, by rfl⟩ : syracuseStep 1397231 = 2095847) B2095847
theorem B8509823 : Blo 618297 8509823 := bstep (se 1 (by rfl) ⟨6382367, by rfl⟩ : syracuseStep 8509823 = 12764735) B12764735
theorem B7068383 : Blo 618297 7068383 := bstep (se 1 (by rfl) ⟨5301287, by rfl⟩ : syracuseStep 7068383 = 10602575) B10602575
theorem B23845951 : Blo 618297 23845951 := bstep (se 1 (by rfl) ⟨17884463, by rfl⟩ : syracuseStep 23845951 = 35768927) B35768927
theorem B941375 : Blo 618297 941375 := bstep (se 1 (by rfl) ⟨706031, by rfl⟩ : syracuseStep 941375 = 1412063) B1412063
theorem B3137129 : Blo 618297 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B2350721 : Blo 618297 2350721 := bstep (se 2 (by rfl) ⟨881520, by rfl⟩ : syracuseStep 2350721 = 1763041) B1763041
theorem B10576331 : Blo 618297 10576331 := bstep (se 1 (by rfl) ⟨7932248, by rfl⟩ : syracuseStep 10576331 = 15864497) B15864497
theorem B16933805 : Blo 618297 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B1565851 : Blo 618297 1565851 := bstep (se 1 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 1565851 = 2348777) B2348777
theorem B15132059 : Blo 618297 15132059 := bstep (se 1 (by rfl) ⟨11349044, by rfl⟩ : syracuseStep 15132059 = 22698089) B22698089
theorem B28632683 : Blo 618297 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B2385721 : Blo 618297 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B2353121 : Blo 618297 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B3140207 : Blo 618297 3140207 := bstep (se 1 (by rfl) ⟨2355155, by rfl⟩ : syracuseStep 3140207 = 4710311) B4710311
theorem B1567451 : Blo 618297 1567451 := bstep (se 1 (by rfl) ⟨1175588, by rfl⟩ : syracuseStep 1567451 = 2351177) B2351177
theorem B4713227 : Blo 618297 4713227 := bstep (se 1 (by rfl) ⟨3534920, by rfl⟩ : syracuseStep 4713227 = 7069841) B7069841
theorem B1764443 : Blo 618297 1764443 := bstep (se 1 (by rfl) ⟨1323332, by rfl⟩ : syracuseStep 1764443 = 2646665) B2646665
theorem B1043759 : Blo 618297 1043759 := bstep (se 1 (by rfl) ⟨782819, by rfl⟩ : syracuseStep 1043759 = 1565639) B1565639
theorem B2092445 : Blo 618297 2092445 := bstep (se 3 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 2092445 = 784667) B784667
theorem B618655 : Blo 618297 618655 := bstep (se 1 (by rfl) ⟨463991, by rfl⟩ : syracuseStep 618655 = 927983) B927983
theorem B5435695 : Blo 618297 5435695 := bstep (se 1 (by rfl) ⟨4076771, by rfl⟩ : syracuseStep 5435695 = 8153543) B8153543
theorem B3142313 : Blo 618297 3142313 := bstep (se 2 (by rfl) ⟨1178367, by rfl⟩ : syracuseStep 3142313 = 2356735) B2356735
theorem B619215 : Blo 618297 619215 := bstep (se 1 (by rfl) ⟨464411, by rfl⟩ : syracuseStep 619215 = 928823) B928823
theorem B2356249 : Blo 618297 2356249 := bstep (se 2 (by rfl) ⟨883593, by rfl⟩ : syracuseStep 2356249 = 1767187) B1767187
theorem B619547 : Blo 618297 619547 := bstep (se 1 (by rfl) ⟨464660, by rfl⟩ : syracuseStep 619547 = 929321) B929321
theorem B619743 : Blo 618297 619743 := bstep (se 1 (by rfl) ⟨464807, by rfl⟩ : syracuseStep 619743 = 929615) B929615
theorem B619775 : Blo 618297 619775 := bstep (se 1 (by rfl) ⟨464831, by rfl⟩ : syracuseStep 619775 = 929663) B929663
theorem B619847 : Blo 618297 619847 := bstep (se 1 (by rfl) ⟨464885, by rfl⟩ : syracuseStep 619847 = 929771) B929771
theorem B2127647 : Blo 618297 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B620391 : Blo 618297 620391 := bstep (se 1 (by rfl) ⟨465293, by rfl⟩ : syracuseStep 620391 = 930587) B930587
theorem B1767359 : Blo 618297 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B1767415 : Blo 618297 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B620827 : Blo 618297 620827 := bstep (se 1 (by rfl) ⟨465620, by rfl⟩ : syracuseStep 620827 = 931241) B931241
theorem B7174439 : Blo 618297 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B2095631 : Blo 618297 2095631 := bstep (se 1 (by rfl) ⟨1571723, by rfl⟩ : syracuseStep 2095631 = 3143447) B3143447
theorem B621247 : Blo 618297 621247 := bstep (se 1 (by rfl) ⟨465935, by rfl⟩ : syracuseStep 621247 = 931871) B931871
theorem B4520873 : Blo 618297 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B621759 : Blo 618297 621759 := bstep (se 1 (by rfl) ⟨466319, by rfl⟩ : syracuseStep 621759 = 932639) B932639
theorem B40205807 : Blo 618297 40205807 := bstep (se 1 (by rfl) ⟨30154355, by rfl⟩ : syracuseStep 40205807 = 60308711) B60308711
theorem B1179355 : Blo 618297 1179355 := bstep (se 1 (by rfl) ⟨884516, by rfl⟩ : syracuseStep 1179355 = 1769033) B1769033
theorem B4720031 : Blo 618297 4720031 := bstep (se 1 (by rfl) ⟨3540023, by rfl⟩ : syracuseStep 4720031 = 7080047) B7080047
theorem B3147983 : Blo 618297 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B3180961 : Blo 618297 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B2230831 : Blo 618297 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B3181247 : Blo 618297 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B5673215 : Blo 618297 5673215 := bstep (se 1 (by rfl) ⟨4254911, by rfl⟩ : syracuseStep 5673215 = 8509823) B8509823
theorem B5673725 : Blo 618297 5673725 := bstep (se 3 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 5673725 = 2127647) B2127647
theorem B8950661 : Blo 618297 8950661 := bstep (se 4 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 8950661 = 1678249) B1678249
theorem B7050887 : Blo 618297 7050887 := bstep (se 1 (by rfl) ⟨5288165, by rfl⟩ : syracuseStep 7050887 = 10576331) B10576331
theorem B7247593 : Blo 618297 7247593 := bstep (se 2 (by rfl) ⟨2717847, by rfl⟩ : syracuseStep 7247593 = 5435695) B5435695
theorem B4725377 : Blo 618297 4725377 := bstep (se 2 (by rfl) ⟨1772016, by rfl⟩ : syracuseStep 4725377 = 3544033) B3544033
theorem B695839 : Blo 618297 695839 := bstep (se 1 (by rfl) ⟨521879, by rfl⟩ : syracuseStep 695839 = 1043759) B1043759
theorem B31794601 : Blo 618297 31794601 := bstep (se 2 (by rfl) ⟨11922975, by rfl⟩ : syracuseStep 31794601 = 23845951) B23845951
theorem B927599 : Blo 618297 927599 := bstep (se 1 (by rfl) ⟨695699, by rfl⟩ : syracuseStep 927599 = 1391399) B1391399
theorem B8464283 : Blo 618297 8464283 := bstep (se 1 (by rfl) ⟨6348212, by rfl⟩ : syracuseStep 8464283 = 12696425) B12696425
theorem B8956655 : Blo 618297 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B3779369 : Blo 618297 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B929087 : Blo 618297 929087 := bstep (se 1 (by rfl) ⟨696815, by rfl⟩ : syracuseStep 929087 = 1393631) B1393631
theorem B929435 : Blo 618297 929435 := bstep (se 1 (by rfl) ⟨697076, by rfl⟩ : syracuseStep 929435 = 1394153) B1394153
theorem B2240633 : Blo 618297 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B931487 : Blo 618297 931487 := bstep (se 1 (by rfl) ⟨698615, by rfl⟩ : syracuseStep 931487 = 1397231) B1397231
theorem B11289203 : Blo 618297 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B19088455 : Blo 618297 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B68699821 : Blo 618297 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B1394963 : Blo 618297 1394963 := bstep (se 1 (by rfl) ⟨1046222, by rfl⟩ : syracuseStep 1394963 = 2092445) B2092445
theorem B3132755 : Blo 618297 3132755 := bstep (se 1 (by rfl) ⟨2349566, by rfl⟩ : syracuseStep 3132755 = 4699133) B4699133
theorem B2510333 : Blo 618297 2510333 := bstep (se 3 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 2510333 = 941375) B941375
theorem B23777063 : Blo 618297 23777063 := bstep (se 1 (by rfl) ⟨17832797, by rfl⟩ : syracuseStep 23777063 = 35665595) B35665595
theorem B3526811 : Blo 618297 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B1397087 : Blo 618297 1397087 := bstep (se 1 (by rfl) ⟨1047815, by rfl⟩ : syracuseStep 1397087 = 2095631) B2095631
theorem B1398239 : Blo 618297 1398239 := bstep (se 1 (by rfl) ⟨1048679, by rfl⟩ : syracuseStep 1398239 = 2097359) B2097359
theorem B6380311 : Blo 618297 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B2087801 : Blo 618297 2087801 := bstep (se 2 (by rfl) ⟨782925, by rfl⟩ : syracuseStep 2087801 = 1565851) B1565851
theorem B1399679 : Blo 618297 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B4481153 : Blo 618297 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B4712255 : Blo 618297 4712255 := bstep (se 1 (by rfl) ⟨3534191, by rfl⟩ : syracuseStep 4712255 = 7068383) B7068383
theorem B6776875 : Blo 618297 6776875 := bstep (se 1 (by rfl) ⟨5082656, by rfl⟩ : syracuseStep 6776875 = 10165313) B10165313
theorem B1271899 : Blo 618297 1271899 := bstep (se 1 (by rfl) ⟨953924, by rfl⟩ : syracuseStep 1271899 = 1907849) B1907849
theorem B4483343 : Blo 618297 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B2091419 : Blo 618297 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B1567147 : Blo 618297 1567147 := bstep (se 1 (by rfl) ⟨1175360, by rfl⟩ : syracuseStep 1567147 = 2350721) B2350721
theorem B2386921 : Blo 618297 2386921 := bstep (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) B1790191
theorem B10088039 : Blo 618297 10088039 := bstep (se 1 (by rfl) ⟨7566029, by rfl⟩ : syracuseStep 10088039 = 15132059) B15132059
theorem B85814963 : Blo 618297 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B1568747 : Blo 618297 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B3141665 : Blo 618297 3141665 := bstep (se 2 (by rfl) ⟨1178124, by rfl⟩ : syracuseStep 3141665 = 2356249) B2356249
theorem B618567 : Blo 618297 618567 := bstep (se 1 (by rfl) ⟨463925, by rfl⟩ : syracuseStep 618567 = 927851) B927851
theorem B618779 : Blo 618297 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B618799 : Blo 618297 618799 := bstep (se 1 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 618799 = 928199) B928199
theorem B2093471 : Blo 618297 2093471 := bstep (se 1 (by rfl) ⟨1570103, by rfl⟩ : syracuseStep 2093471 = 3140207) B3140207
theorem B1044967 : Blo 618297 1044967 := bstep (se 1 (by rfl) ⟨783725, by rfl⟩ : syracuseStep 1044967 = 1567451) B1567451
theorem B3142151 : Blo 618297 3142151 := bstep (se 1 (by rfl) ⟨2356613, by rfl⟩ : syracuseStep 3142151 = 4713227) B4713227
theorem B1176295 : Blo 618297 1176295 := bstep (se 1 (by rfl) ⟨882221, by rfl⟩ : syracuseStep 1176295 = 1764443) B1764443
theorem B619335 : Blo 618297 619335 := bstep (se 1 (by rfl) ⟨464501, by rfl⟩ : syracuseStep 619335 = 929003) B929003
theorem B619519 : Blo 618297 619519 := bstep (se 1 (by rfl) ⟨464639, by rfl⟩ : syracuseStep 619519 = 929279) B929279
theorem B12055661 : Blo 618297 12055661 := bstep (se 3 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 12055661 = 4520873) B4520873
theorem B619803 : Blo 618297 619803 := bstep (se 1 (by rfl) ⟨464852, by rfl⟩ : syracuseStep 619803 = 929705) B929705
theorem B619823 : Blo 618297 619823 := bstep (se 1 (by rfl) ⟨464867, by rfl⟩ : syracuseStep 619823 = 929735) B929735
theorem B2356553 : Blo 618297 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B620063 : Blo 618297 620063 := bstep (se 1 (by rfl) ⟨465047, by rfl⟩ : syracuseStep 620063 = 930095) B930095
theorem B620263 : Blo 618297 620263 := bstep (se 1 (by rfl) ⟨465197, by rfl⟩ : syracuseStep 620263 = 930395) B930395
theorem B620315 : Blo 618297 620315 := bstep (se 1 (by rfl) ⟨465236, by rfl⟩ : syracuseStep 620315 = 930473) B930473
theorem B2094875 : Blo 618297 2094875 := bstep (se 1 (by rfl) ⟨1571156, by rfl⟩ : syracuseStep 2094875 = 3142313) B3142313
theorem B620767 : Blo 618297 620767 := bstep (se 1 (by rfl) ⟨465575, by rfl⟩ : syracuseStep 620767 = 931151) B931151
theorem B620863 : Blo 618297 620863 := bstep (se 1 (by rfl) ⟨465647, by rfl⟩ : syracuseStep 620863 = 931295) B931295
theorem B621039 : Blo 618297 621039 := bstep (se 1 (by rfl) ⟨465779, by rfl⟩ : syracuseStep 621039 = 931559) B931559
theorem B621103 : Blo 618297 621103 := bstep (se 1 (by rfl) ⟨465827, by rfl⟩ : syracuseStep 621103 = 931655) B931655
theorem B621167 : Blo 618297 621167 := bstep (se 1 (by rfl) ⟨465875, by rfl⟩ : syracuseStep 621167 = 931751) B931751
theorem B1178239 : Blo 618297 1178239 := bstep (se 1 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 1178239 = 1767359) B1767359
theorem B621339 : Blo 618297 621339 := bstep (se 1 (by rfl) ⟨466004, by rfl⟩ : syracuseStep 621339 = 932009) B932009
theorem B22903631 : Blo 618297 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B4782959 : Blo 618297 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B621735 : Blo 618297 621735 := bstep (se 1 (by rfl) ⟨466301, by rfl⟩ : syracuseStep 621735 = 932603) B932603
theorem B621819 : Blo 618297 621819 := bstep (se 1 (by rfl) ⟨466364, by rfl⟩ : syracuseStep 621819 = 932729) B932729
theorem B622111 : Blo 618297 622111 := bstep (se 1 (by rfl) ⟨466583, by rfl⟩ : syracuseStep 622111 = 933167) B933167
theorem B1572473 : Blo 618297 1572473 := bstep (se 2 (by rfl) ⟨589677, by rfl⟩ : syracuseStep 1572473 = 1179355) B1179355
theorem B26803871 : Blo 618297 26803871 := bstep (se 1 (by rfl) ⟨20102903, by rfl⟩ : syracuseStep 26803871 = 40205807) B40205807
theorem B36143333 : Blo 618297 36143333 := bstep (se 4 (by rfl) ⟨3388437, by rfl⟩ : syracuseStep 36143333 = 6776875) B6776875
theorem B3146687 : Blo 618297 3146687 := bstep (se 1 (by rfl) ⟨2360015, by rfl⟩ : syracuseStep 3146687 = 4720031) B4720031
theorem B2098655 : Blo 618297 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B1673555 : Blo 618297 1673555 := bstep (se 1 (by rfl) ⟨1255166, by rfl⟩ : syracuseStep 1673555 = 2510333) B2510333
theorem B5967107 : Blo 618297 5967107 := bstep (se 1 (by rfl) ⟨4475330, by rfl⟩ : syracuseStep 5967107 = 8950661) B8950661
theorem B3182561 : Blo 618297 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B3150251 : Blo 618297 3150251 := bstep (se 1 (by rfl) ⟨2362688, by rfl⟩ : syracuseStep 3150251 = 4725377) B4725377
theorem B2987435 : Blo 618297 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B5642855 : Blo 618297 5642855 := bstep (se 1 (by rfl) ⟨4232141, by rfl⟩ : syracuseStep 5642855 = 8464283) B8464283
theorem B2988895 : Blo 618297 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B5971103 : Blo 618297 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B6725359 : Blo 618297 6725359 := bstep (se 1 (by rfl) ⟨5044019, by rfl⟩ : syracuseStep 6725359 = 10088039) B10088039
theorem B8037107 : Blo 618297 8037107 := bstep (se 1 (by rfl) ⟨6027830, by rfl⟩ : syracuseStep 8037107 = 12055661) B12055661
theorem B3188639 : Blo 618297 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B927785 : Blo 618297 927785 := bstep (se 2 (by rfl) ⟨347919, by rfl⟩ : syracuseStep 927785 = 695839) B695839
theorem B17869247 : Blo 618297 17869247 := bstep (se 1 (by rfl) ⟨13401935, by rfl⟩ : syracuseStep 17869247 = 26803871) B26803871
theorem B5975021 : Blo 618297 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B929975 : Blo 618297 929975 := bstep (se 1 (by rfl) ⟨697481, by rfl⟩ : syracuseStep 929975 = 1394963) B1394963
theorem B91599761 : Blo 618297 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B3782143 : Blo 618297 3782143 := bstep (se 1 (by rfl) ⟨2836607, by rfl⟩ : syracuseStep 3782143 = 5673215) B5673215
theorem B931391 : Blo 618297 931391 := bstep (se 1 (by rfl) ⟨698543, by rfl⟩ : syracuseStep 931391 = 1397087) B1397087
theorem B3782483 : Blo 618297 3782483 := bstep (se 1 (by rfl) ⟨2836862, by rfl⟩ : syracuseStep 3782483 = 5673725) B5673725
theorem B4241281 : Blo 618297 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B932159 : Blo 618297 932159 := bstep (se 1 (by rfl) ⟨699119, by rfl⟩ : syracuseStep 932159 = 1398239) B1398239
theorem B4700591 : Blo 618297 4700591 := bstep (se 1 (by rfl) ⟨3525443, by rfl⟩ : syracuseStep 4700591 = 7050887) B7050887
theorem B1391867 : Blo 618297 1391867 := bstep (se 1 (by rfl) ⟨1043900, by rfl⟩ : syracuseStep 1391867 = 2087801) B2087801
theorem B933119 : Blo 618297 933119 := bstep (se 1 (by rfl) ⟨699839, by rfl⟩ : syracuseStep 933119 = 1399679) B1399679
theorem B1393289 : Blo 618297 1393289 := bstep (se 2 (by rfl) ⟨522483, by rfl⟩ : syracuseStep 1393289 = 1044967) B1044967
theorem B1394279 : Blo 618297 1394279 := bstep (se 1 (by rfl) ⟨1045709, by rfl⟩ : syracuseStep 1394279 = 2091419) B2091419
theorem B1395647 : Blo 618297 1395647 := bstep (se 1 (by rfl) ⟨1046735, by rfl⟩ : syracuseStep 1395647 = 2093471) B2093471
theorem B8507081 : Blo 618297 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B1396583 : Blo 618297 1396583 := bstep (se 1 (by rfl) ⟨1047437, by rfl⟩ : syracuseStep 1396583 = 2094875) B2094875
theorem B7526135 : Blo 618297 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B25451273 : Blo 618297 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B2120831 : Blo 618297 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B42392801 : Blo 618297 42392801 := bstep (se 2 (by rfl) ⟨15897300, by rfl⟩ : syracuseStep 42392801 = 31794601) B31794601
theorem B2088503 : Blo 618297 2088503 := bstep (se 1 (by rfl) ⟨1566377, by rfl⟩ : syracuseStep 2088503 = 3132755) B3132755
theorem B15851375 : Blo 618297 15851375 := bstep (se 1 (by rfl) ⟨11888531, by rfl⟩ : syracuseStep 15851375 = 23777063) B23777063
theorem B2351207 : Blo 618297 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B1695865 : Blo 618297 1695865 := bstep (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) B1271899
theorem B2089529 : Blo 618297 2089529 := bstep (se 2 (by rfl) ⟨783573, by rfl⟩ : syracuseStep 2089529 = 1567147) B1567147
theorem B2974441 : Blo 618297 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B1568393 : Blo 618297 1568393 := bstep (se 2 (by rfl) ⟨588147, by rfl⟩ : syracuseStep 1568393 = 1176295) B1176295
theorem B3141503 : Blo 618297 3141503 := bstep (se 1 (by rfl) ⟨2356127, by rfl⟩ : syracuseStep 3141503 = 4712255) B4712255
theorem B618399 : Blo 618297 618399 := bstep (se 1 (by rfl) ⟨463799, by rfl⟩ : syracuseStep 618399 = 927599) B927599
theorem B2519579 : Blo 618297 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B619391 : Blo 618297 619391 := bstep (se 1 (by rfl) ⟨464543, by rfl⟩ : syracuseStep 619391 = 929087) B929087
theorem B9663457 : Blo 618297 9663457 := bstep (se 2 (by rfl) ⟨3623796, by rfl⟩ : syracuseStep 9663457 = 7247593) B7247593
theorem B619623 : Blo 618297 619623 := bstep (se 1 (by rfl) ⟨464717, by rfl⟩ : syracuseStep 619623 = 929435) B929435
theorem B57209975 : Blo 618297 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B1045831 : Blo 618297 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B2094443 : Blo 618297 2094443 := bstep (se 1 (by rfl) ⟨1570832, by rfl⟩ : syracuseStep 2094443 = 3141665) B3141665
theorem B2094767 : Blo 618297 2094767 := bstep (se 1 (by rfl) ⟨1571075, by rfl⟩ : syracuseStep 2094767 = 3142151) B3142151
theorem B1570985 : Blo 618297 1570985 := bstep (se 2 (by rfl) ⟨589119, by rfl⟩ : syracuseStep 1570985 = 1178239) B1178239
theorem B1571035 : Blo 618297 1571035 := bstep (se 1 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 1571035 = 2356553) B2356553
theorem B620991 : Blo 618297 620991 := bstep (se 1 (by rfl) ⟨465743, by rfl⟩ : syracuseStep 620991 = 931487) B931487
theorem B15269087 : Blo 618297 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B1048315 : Blo 618297 1048315 := bstep (se 1 (by rfl) ⟨786236, by rfl⟩ : syracuseStep 1048315 = 1572473) B1572473
theorem B2261153 : Blo 618297 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B2097791 : Blo 618297 2097791 := bstep (se 1 (by rfl) ⟨1573343, by rfl⟩ : syracuseStep 2097791 = 3146687) B3146687
theorem B3965921 : Blo 618297 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B5671387 : Blo 618297 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B2100167 : Blo 618297 2100167 := bstep (se 1 (by rfl) ⟨1575125, by rfl⟩ : syracuseStep 2100167 = 3150251) B3150251
theorem B5017423 : Blo 618297 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B1413887 : Blo 618297 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B4462813 : Blo 618297 4462813 := bstep (se 3 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 4462813 = 1673555) B1673555
theorem B12884609 : Blo 618297 12884609 := bstep (se 2 (by rfl) ⟨4831728, by rfl⟩ : syracuseStep 12884609 = 9663457) B9663457
theorem B67870061 : Blo 618297 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B1679719 : Blo 618297 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B927911 : Blo 618297 927911 := bstep (se 1 (by rfl) ⟨695933, by rfl⟩ : syracuseStep 927911 = 1391867) B1391867
theorem B24095555 : Blo 618297 24095555 := bstep (se 1 (by rfl) ⟨18071666, by rfl⟩ : syracuseStep 24095555 = 36143333) B36143333
theorem B928859 : Blo 618297 928859 := bstep (se 1 (by rfl) ⟨696644, by rfl⟩ : syracuseStep 928859 = 1393289) B1393289
theorem B929519 : Blo 618297 929519 := bstep (se 1 (by rfl) ⟨697139, by rfl⟩ : syracuseStep 929519 = 1394279) B1394279
theorem B930431 : Blo 618297 930431 := bstep (se 1 (by rfl) ⟨697823, by rfl⟩ : syracuseStep 930431 = 1395647) B1395647
theorem B3978071 : Blo 618297 3978071 := bstep (se 1 (by rfl) ⟨2983553, by rfl⟩ : syracuseStep 3978071 = 5967107) B5967107
theorem B931055 : Blo 618297 931055 := bstep (se 1 (by rfl) ⟨698291, by rfl⟩ : syracuseStep 931055 = 1396583) B1396583
theorem B3980735 : Blo 618297 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B28261867 : Blo 618297 28261867 := bstep (se 1 (by rfl) ⟨21196400, by rfl⟩ : syracuseStep 28261867 = 42392801) B42392801
theorem B1392335 : Blo 618297 1392335 := bstep (se 1 (by rfl) ⟨1044251, by rfl⟩ : syracuseStep 1392335 = 2088503) B2088503
theorem B10567583 : Blo 618297 10567583 := bstep (se 1 (by rfl) ⟨7925687, by rfl⟩ : syracuseStep 10567583 = 15851375) B15851375
theorem B1393019 : Blo 618297 1393019 := bstep (se 1 (by rfl) ⟨1044764, by rfl⟩ : syracuseStep 1393019 = 2089529) B2089529
theorem B5358071 : Blo 618297 5358071 := bstep (se 1 (by rfl) ⟨4018553, by rfl⟩ : syracuseStep 5358071 = 8037107) B8037107
theorem B11912831 : Blo 618297 11912831 := bstep (se 1 (by rfl) ⟨8934623, by rfl⟩ : syracuseStep 11912831 = 17869247) B17869247
theorem B1394441 : Blo 618297 1394441 := bstep (se 2 (by rfl) ⟨522915, by rfl⟩ : syracuseStep 1394441 = 1045831) B1045831
theorem B3983347 : Blo 618297 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B5655041 : Blo 618297 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B40717565 : Blo 618297 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B61066507 : Blo 618297 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B1396295 : Blo 618297 1396295 := bstep (se 1 (by rfl) ⟨1047221, by rfl⟩ : syracuseStep 1396295 = 2094443) B2094443
theorem B1396511 : Blo 618297 1396511 := bstep (se 1 (by rfl) ⟨1047383, by rfl⟩ : syracuseStep 1396511 = 2094767) B2094767
theorem B3985193 : Blo 618297 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B3133727 : Blo 618297 3133727 := bstep (se 1 (by rfl) ⟨2350295, by rfl⟩ : syracuseStep 3133727 = 4700591) B4700591
theorem B8967145 : Blo 618297 8967145 := bstep (se 2 (by rfl) ⟨3362679, by rfl⟩ : syracuseStep 8967145 = 6725359) B6725359
theorem B1397753 : Blo 618297 1397753 := bstep (se 2 (by rfl) ⟨524157, by rfl⟩ : syracuseStep 1397753 = 1048315) B1048315
theorem B1399103 : Blo 618297 1399103 := bstep (se 1 (by rfl) ⟨1049327, by rfl⟩ : syracuseStep 1399103 = 2098655) B2098655
theorem B2121707 : Blo 618297 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B1991623 : Blo 618297 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B3761903 : Blo 618297 3761903 := bstep (se 1 (by rfl) ⟨2821427, by rfl⟩ : syracuseStep 3761903 = 5642855) B5642855
theorem B1567471 : Blo 618297 1567471 := bstep (se 1 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 1567471 = 2351207) B2351207
theorem B2125759 : Blo 618297 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B618523 : Blo 618297 618523 := bstep (se 1 (by rfl) ⟨463892, by rfl⟩ : syracuseStep 618523 = 927785) B927785
theorem B5042857 : Blo 618297 5042857 := bstep (se 2 (by rfl) ⟨1891071, by rfl⟩ : syracuseStep 5042857 = 3782143) B3782143
theorem B1045595 : Blo 618297 1045595 := bstep (se 1 (by rfl) ⟨784196, by rfl⟩ : syracuseStep 1045595 = 1568393) B1568393
theorem B2094335 : Blo 618297 2094335 := bstep (se 1 (by rfl) ⟨1570751, by rfl⟩ : syracuseStep 2094335 = 3141503) B3141503
theorem B619983 : Blo 618297 619983 := bstep (se 1 (by rfl) ⟨464987, by rfl⟩ : syracuseStep 619983 = 929975) B929975
theorem B2094713 : Blo 618297 2094713 := bstep (se 2 (by rfl) ⟨785517, by rfl⟩ : syracuseStep 2094713 = 1571035) B1571035
theorem B38139983 : Blo 618297 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B620927 : Blo 618297 620927 := bstep (se 1 (by rfl) ⟨465695, by rfl⟩ : syracuseStep 620927 = 931391) B931391
theorem B2521655 : Blo 618297 2521655 := bstep (se 1 (by rfl) ⟨1891241, by rfl⟩ : syracuseStep 2521655 = 3782483) B3782483
theorem B1047323 : Blo 618297 1047323 := bstep (se 1 (by rfl) ⟨785492, by rfl⟩ : syracuseStep 1047323 = 1570985) B1570985
theorem B621439 : Blo 618297 621439 := bstep (se 1 (by rfl) ⟨466079, by rfl⟩ : syracuseStep 621439 = 932159) B932159
theorem B622079 : Blo 618297 622079 := bstep (se 1 (by rfl) ⟨466559, by rfl⟩ : syracuseStep 622079 = 933119) B933119
theorem B3572047 : Blo 618297 3572047 := bstep (se 1 (by rfl) ⟨2679035, by rfl⟩ : syracuseStep 3572047 = 5358071) B5358071
theorem B6029741 : Blo 618297 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B2655497 : Blo 618297 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B3770027 : Blo 618297 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B2656795 : Blo 618297 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B5311129 : Blo 618297 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B6689897 : Blo 618297 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B1414471 : Blo 618297 1414471 := bstep (se 1 (by rfl) ⟨1060853, by rfl⟩ : syracuseStep 1414471 = 2121707) B2121707
theorem B6723809 : Blo 618297 6723809 := bstep (se 2 (by rfl) ⟨2521428, by rfl⟩ : syracuseStep 6723809 = 5042857) B5042857
theorem B16063703 : Blo 618297 16063703 := bstep (se 1 (by rfl) ⟨12047777, by rfl⟩ : syracuseStep 16063703 = 24095555) B24095555
theorem B15081461 : Blo 618297 15081461 := bstep (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) B1413887
theorem B697063 : Blo 618297 697063 := bstep (se 1 (by rfl) ⟨522797, by rfl⟩ : syracuseStep 697063 = 1045595) B1045595
theorem B1681103 : Blo 618297 1681103 := bstep (se 1 (by rfl) ⟨1260827, by rfl⟩ : syracuseStep 1681103 = 2521655) B2521655
theorem B698215 : Blo 618297 698215 := bstep (se 1 (by rfl) ⟨523661, by rfl⟩ : syracuseStep 698215 = 1047323) B1047323
theorem B928223 : Blo 618297 928223 := bstep (se 1 (by rfl) ⟨696167, by rfl⟩ : syracuseStep 928223 = 1392335) B1392335
theorem B928679 : Blo 618297 928679 := bstep (se 1 (by rfl) ⟨696509, by rfl⟩ : syracuseStep 928679 = 1393019) B1393019
theorem B2239625 : Blo 618297 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B7941887 : Blo 618297 7941887 := bstep (se 1 (by rfl) ⟨5956415, by rfl⟩ : syracuseStep 7941887 = 11912831) B11912831
theorem B929627 : Blo 618297 929627 := bstep (se 1 (by rfl) ⟨697220, by rfl⟩ : syracuseStep 929627 = 1394441) B1394441
theorem B27145043 : Blo 618297 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B930863 : Blo 618297 930863 := bstep (se 1 (by rfl) ⟨698147, by rfl⟩ : syracuseStep 930863 = 1396295) B1396295
theorem B931007 : Blo 618297 931007 := bstep (se 1 (by rfl) ⟨698255, by rfl⟩ : syracuseStep 931007 = 1396511) B1396511
theorem B931835 : Blo 618297 931835 := bstep (se 1 (by rfl) ⟨698876, by rfl⟩ : syracuseStep 931835 = 1397753) B1397753
theorem B932735 : Blo 618297 932735 := bstep (se 1 (by rfl) ⟨699551, by rfl⟩ : syracuseStep 932735 = 1399103) B1399103
theorem B2834345 : Blo 618297 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B2507935 : Blo 618297 2507935 := bstep (se 1 (by rfl) ⟨1880951, by rfl⟩ : syracuseStep 2507935 = 3761903) B3761903
theorem B34358957 : Blo 618297 34358957 := bstep (se 3 (by rfl) ⟨6442304, by rfl⟩ : syracuseStep 34358957 = 12884609) B12884609
theorem B5950417 : Blo 618297 5950417 := bstep (se 2 (by rfl) ⟨2231406, by rfl⟩ : syracuseStep 5950417 = 4462813) B4462813
theorem B1396223 : Blo 618297 1396223 := bstep (se 1 (by rfl) ⟨1047167, by rfl⟩ : syracuseStep 1396223 = 2094335) B2094335
theorem B1396475 : Blo 618297 1396475 := bstep (se 1 (by rfl) ⟨1047356, by rfl⟩ : syracuseStep 1396475 = 2094713) B2094713
theorem B1398527 : Blo 618297 1398527 := bstep (se 1 (by rfl) ⟨1048895, by rfl⟩ : syracuseStep 1398527 = 2097791) B2097791
theorem B2643947 : Blo 618297 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B1400111 : Blo 618297 1400111 := bstep (se 1 (by rfl) ⟨1050083, by rfl⟩ : syracuseStep 1400111 = 2100167) B2100167
theorem B2089151 : Blo 618297 2089151 := bstep (se 1 (by rfl) ⟨1566863, by rfl⟩ : syracuseStep 2089151 = 3133727) B3133727
theorem B7561849 : Blo 618297 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B2089961 : Blo 618297 2089961 := bstep (se 2 (by rfl) ⟨783735, by rfl⟩ : syracuseStep 2089961 = 1567471) B1567471
theorem B81422009 : Blo 618297 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B45246707 : Blo 618297 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B11956193 : Blo 618297 11956193 := bstep (se 2 (by rfl) ⟨4483572, by rfl⟩ : syracuseStep 11956193 = 8967145) B8967145
theorem B618607 : Blo 618297 618607 := bstep (se 1 (by rfl) ⟨463955, by rfl⟩ : syracuseStep 618607 = 927911) B927911
theorem B619239 : Blo 618297 619239 := bstep (se 1 (by rfl) ⟨464429, by rfl⟩ : syracuseStep 619239 = 928859) B928859
theorem B619679 : Blo 618297 619679 := bstep (se 1 (by rfl) ⟨464759, by rfl⟩ : syracuseStep 619679 = 929519) B929519
theorem B620287 : Blo 618297 620287 := bstep (se 1 (by rfl) ⟨465215, by rfl⟩ : syracuseStep 620287 = 930431) B930431
theorem B2652047 : Blo 618297 2652047 := bstep (se 1 (by rfl) ⟨1989035, by rfl⟩ : syracuseStep 2652047 = 3978071) B3978071
theorem B620703 : Blo 618297 620703 := bstep (se 1 (by rfl) ⟨465527, by rfl⟩ : syracuseStep 620703 = 931055) B931055
theorem B25426655 : Blo 618297 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B37682489 : Blo 618297 37682489 := bstep (se 2 (by rfl) ⟨14130933, by rfl⟩ : syracuseStep 37682489 = 28261867) B28261867
theorem B2653823 : Blo 618297 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B7045055 : Blo 618297 7045055 := bstep (se 1 (by rfl) ⟨5283791, by rfl⟩ : syracuseStep 7045055 = 10567583) B10567583
theorem B1770331 : Blo 618297 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B22905971 : Blo 618297 22905971 := bstep (se 1 (by rfl) ⟨17179478, by rfl⟩ : syracuseStep 22905971 = 34358957) B34358957
theorem B3343913 : Blo 618297 3343913 := bstep (se 2 (by rfl) ⟨1253967, by rfl⟩ : syracuseStep 3343913 = 2507935) B2507935
theorem B3542393 : Blo 618297 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B4459931 : Blo 618297 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B7081505 : Blo 618297 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B7933889 : Blo 618297 7933889 := bstep (se 2 (by rfl) ⟨2975208, by rfl⟩ : syracuseStep 7933889 = 5950417) B5950417
theorem B1120735 : Blo 618297 1120735 := bstep (se 1 (by rfl) ⟨840551, by rfl⟩ : syracuseStep 1120735 = 1681103) B1681103
theorem B7970795 : Blo 618297 7970795 := bstep (se 1 (by rfl) ⟨5978096, by rfl⟩ : syracuseStep 7970795 = 11956193) B11956193
theorem B18096695 : Blo 618297 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B16951103 : Blo 618297 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B4696703 : Blo 618297 4696703 := bstep (se 1 (by rfl) ⟨3522527, by rfl⟩ : syracuseStep 4696703 = 7045055) B7045055
theorem B4762729 : Blo 618297 4762729 := bstep (se 2 (by rfl) ⟨1786023, by rfl⟩ : syracuseStep 4762729 = 3572047) B3572047
theorem B929417 : Blo 618297 929417 := bstep (se 2 (by rfl) ⟨348531, by rfl⟩ : syracuseStep 929417 = 697063) B697063
theorem B930815 : Blo 618297 930815 := bstep (se 1 (by rfl) ⟨698111, by rfl⟩ : syracuseStep 930815 = 1396223) B1396223
theorem B930953 : Blo 618297 930953 := bstep (se 2 (by rfl) ⟨349107, by rfl⟩ : syracuseStep 930953 = 698215) B698215
theorem B930983 : Blo 618297 930983 := bstep (se 1 (by rfl) ⟨698237, by rfl⟩ : syracuseStep 930983 = 1396475) B1396475
theorem B932351 : Blo 618297 932351 := bstep (se 1 (by rfl) ⟨699263, by rfl⟩ : syracuseStep 932351 = 1398527) B1398527
theorem B933407 : Blo 618297 933407 := bstep (se 1 (by rfl) ⟨700055, by rfl⟩ : syracuseStep 933407 = 1400111) B1400111
theorem B1392767 : Blo 618297 1392767 := bstep (se 1 (by rfl) ⟨1044575, by rfl⟩ : syracuseStep 1392767 = 2089151) B2089151
theorem B1393307 : Blo 618297 1393307 := bstep (se 1 (by rfl) ⟨1044980, by rfl⟩ : syracuseStep 1393307 = 2089961) B2089961
theorem B54281339 : Blo 618297 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B30164471 : Blo 618297 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B1885961 : Blo 618297 1885961 := bstep (se 2 (by rfl) ⟨707235, by rfl⟩ : syracuseStep 1885961 = 1414471) B1414471
theorem B1493083 : Blo 618297 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B5294591 : Blo 618297 5294591 := bstep (se 1 (by rfl) ⟨3970943, by rfl⟩ : syracuseStep 5294591 = 7941887) B7941887
theorem B25121659 : Blo 618297 25121659 := bstep (se 1 (by rfl) ⟨18841244, by rfl⟩ : syracuseStep 25121659 = 37682489) B37682489
theorem B1889563 : Blo 618297 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B4019827 : Blo 618297 4019827 := bstep (se 1 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 4019827 = 6029741) B6029741
theorem B10082465 : Blo 618297 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B2513351 : Blo 618297 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B1762631 : Blo 618297 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B4482539 : Blo 618297 4482539 := bstep (se 1 (by rfl) ⟨3361904, by rfl⟩ : syracuseStep 4482539 = 6723809) B6723809
theorem B10709135 : Blo 618297 10709135 := bstep (se 1 (by rfl) ⟨8031851, by rfl⟩ : syracuseStep 10709135 = 16063703) B16063703
theorem B10054307 : Blo 618297 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B618815 : Blo 618297 618815 := bstep (se 1 (by rfl) ⟨464111, by rfl⟩ : syracuseStep 618815 = 928223) B928223
theorem B619119 : Blo 618297 619119 := bstep (se 1 (by rfl) ⟨464339, by rfl⟩ : syracuseStep 619119 = 928679) B928679
theorem B619751 : Blo 618297 619751 := bstep (se 1 (by rfl) ⟨464813, by rfl⟩ : syracuseStep 619751 = 929627) B929627
theorem B620575 : Blo 618297 620575 := bstep (se 1 (by rfl) ⟨465431, by rfl⟩ : syracuseStep 620575 = 930863) B930863
theorem B620671 : Blo 618297 620671 := bstep (se 1 (by rfl) ⟨465503, by rfl⟩ : syracuseStep 620671 = 931007) B931007
theorem B1768031 : Blo 618297 1768031 := bstep (se 1 (by rfl) ⟨1326023, by rfl⟩ : syracuseStep 1768031 = 2652047) B2652047
theorem B621223 : Blo 618297 621223 := bstep (se 1 (by rfl) ⟨465917, by rfl⟩ : syracuseStep 621223 = 931835) B931835
theorem B621823 : Blo 618297 621823 := bstep (se 1 (by rfl) ⟨466367, by rfl⟩ : syracuseStep 621823 = 932735) B932735
theorem B1769215 : Blo 618297 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B7963109 : Blo 618297 7963109 := bstep (se 4 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 7963109 = 1493083) B1493083
theorem B15270647 : Blo 618297 15270647 := bstep (se 1 (by rfl) ⟨11452985, by rfl⟩ : syracuseStep 15270647 = 22905971) B22905971
theorem B2229275 : Blo 618297 2229275 := bstep (se 1 (by rfl) ⟨1671956, by rfl⟩ : syracuseStep 2229275 = 3343913) B3343913
theorem B2360441 : Blo 618297 2360441 := bstep (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) B1770331
theorem B2361595 : Blo 618297 2361595 := bstep (se 1 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 2361595 = 3542393) B3542393
theorem B4721003 : Blo 618297 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B6721643 : Blo 618297 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B1675567 : Blo 618297 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B5313863 : Blo 618297 5313863 := bstep (se 1 (by rfl) ⟨3985397, by rfl⟩ : syracuseStep 5313863 = 7970795) B7970795
theorem B12064463 : Blo 618297 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B25401221 : Blo 618297 25401221 := bstep (se 4 (by rfl) ⟨2381364, by rfl⟩ : syracuseStep 25401221 = 4762729) B4762729
theorem B2988359 : Blo 618297 2988359 := bstep (se 1 (by rfl) ⟨2241269, by rfl⟩ : syracuseStep 2988359 = 4482539) B4482539
theorem B33495545 : Blo 618297 33495545 := bstep (se 2 (by rfl) ⟨12560829, by rfl⟩ : syracuseStep 33495545 = 25121659) B25121659
theorem B928511 : Blo 618297 928511 := bstep (se 1 (by rfl) ⟨696383, by rfl⟩ : syracuseStep 928511 = 1392767) B1392767
theorem B928871 : Blo 618297 928871 := bstep (se 1 (by rfl) ⟨696653, by rfl⟩ : syracuseStep 928871 = 1393307) B1393307
theorem B36187559 : Blo 618297 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B5977253 : Blo 618297 5977253 := bstep (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) B1120735
theorem B5289259 : Blo 618297 5289259 := bstep (se 1 (by rfl) ⟨3966944, by rfl⟩ : syracuseStep 5289259 = 7933889) B7933889
theorem B5029229 : Blo 618297 5029229 := bstep (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) B1885961
theorem B3131135 : Blo 618297 3131135 := bstep (se 1 (by rfl) ⟨2348351, by rfl⟩ : syracuseStep 3131135 = 4696703) B4696703
theorem B6702871 : Blo 618297 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B5359769 : Blo 618297 5359769 := bstep (se 2 (by rfl) ⟨2009913, by rfl⟩ : syracuseStep 5359769 = 4019827) B4019827
theorem B20109647 : Blo 618297 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B3529727 : Blo 618297 3529727 := bstep (se 1 (by rfl) ⟨2647295, by rfl⟩ : syracuseStep 3529727 = 5294591) B5294591
theorem B2973287 : Blo 618297 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B1175087 : Blo 618297 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B11300735 : Blo 618297 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B7139423 : Blo 618297 7139423 := bstep (se 1 (by rfl) ⟨5354567, by rfl⟩ : syracuseStep 7139423 = 10709135) B10709135
theorem B2519417 : Blo 618297 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B619611 : Blo 618297 619611 := bstep (se 1 (by rfl) ⟨464708, by rfl⟩ : syracuseStep 619611 = 929417) B929417
theorem B620543 : Blo 618297 620543 := bstep (se 1 (by rfl) ⟨465407, by rfl⟩ : syracuseStep 620543 = 930815) B930815
theorem B620635 : Blo 618297 620635 := bstep (se 1 (by rfl) ⟨465476, by rfl⟩ : syracuseStep 620635 = 930953) B930953
theorem B620655 : Blo 618297 620655 := bstep (se 1 (by rfl) ⟨465491, by rfl⟩ : syracuseStep 620655 = 930983) B930983
theorem B621567 : Blo 618297 621567 := bstep (se 1 (by rfl) ⟨466175, by rfl⟩ : syracuseStep 621567 = 932351) B932351
theorem B1178687 : Blo 618297 1178687 := bstep (se 1 (by rfl) ⟨884015, by rfl⟩ : syracuseStep 1178687 = 1768031) B1768031
theorem B2358953 : Blo 618297 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B622271 : Blo 618297 622271 := bstep (se 1 (by rfl) ⟨466703, by rfl⟩ : syracuseStep 622271 = 933407) B933407
theorem B5308739 : Blo 618297 5308739 := bstep (se 1 (by rfl) ⟨3981554, by rfl⟩ : syracuseStep 5308739 = 7963109) B7963109
theorem B1573627 : Blo 618297 1573627 := bstep (se 1 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 1573627 = 2360441) B2360441
theorem B3573179 : Blo 618297 3573179 := bstep (se 1 (by rfl) ⟨2679884, by rfl⟩ : syracuseStep 3573179 = 5359769) B5359769
theorem B3147335 : Blo 618297 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B3148793 : Blo 618297 3148793 := bstep (se 2 (by rfl) ⟨1180797, by rfl⟩ : syracuseStep 3148793 = 2361595) B2361595
theorem B3542575 : Blo 618297 3542575 := bstep (se 1 (by rfl) ⟨2656931, by rfl⟩ : syracuseStep 3542575 = 5313863) B5313863
theorem B13406431 : Blo 618297 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B2234089 : Blo 618297 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B7052345 : Blo 618297 7052345 := bstep (se 2 (by rfl) ⟨2644629, by rfl⟩ : syracuseStep 7052345 = 5289259) B5289259
theorem B24125039 : Blo 618297 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B4759615 : Blo 618297 4759615 := bstep (se 1 (by rfl) ⟨3569711, by rfl⟩ : syracuseStep 4759615 = 7139423) B7139423
theorem B1679611 : Blo 618297 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B13411277 : Blo 618297 13411277 := bstep (se 3 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 13411277 = 5029229) B5029229
theorem B1486183 : Blo 618297 1486183 := bstep (se 1 (by rfl) ⟨1114637, by rfl⟩ : syracuseStep 1486183 = 2229275) B2229275
theorem B8042975 : Blo 618297 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B22330363 : Blo 618297 22330363 := bstep (se 1 (by rfl) ⟨16747772, by rfl⟩ : syracuseStep 22330363 = 33495545) B33495545
theorem B3984835 : Blo 618297 3984835 := bstep (se 1 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 3984835 = 5977253) B5977253
theorem B3133565 : Blo 618297 3133565 := bstep (se 3 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 3133565 = 1175087) B1175087
theorem B2087423 : Blo 618297 2087423 := bstep (se 1 (by rfl) ⟨1565567, by rfl⟩ : syracuseStep 2087423 = 3131135) B3131135
theorem B40721725 : Blo 618297 40721725 := bstep (se 3 (by rfl) ⟨7635323, by rfl⟩ : syracuseStep 40721725 = 15270647) B15270647
theorem B8937161 : Blo 618297 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B4481095 : Blo 618297 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B16934147 : Blo 618297 16934147 := bstep (se 1 (by rfl) ⟨12700610, by rfl⟩ : syracuseStep 16934147 = 25401221) B25401221
theorem B1992239 : Blo 618297 1992239 := bstep (se 1 (by rfl) ⟨1494179, by rfl⟩ : syracuseStep 1992239 = 2988359) B2988359
theorem B2353151 : Blo 618297 2353151 := bstep (se 1 (by rfl) ⟨1764863, by rfl⟩ : syracuseStep 2353151 = 3529727) B3529727
theorem B619007 : Blo 618297 619007 := bstep (se 1 (by rfl) ⟨464255, by rfl⟩ : syracuseStep 619007 = 928511) B928511
theorem B619247 : Blo 618297 619247 := bstep (se 1 (by rfl) ⟨464435, by rfl⟩ : syracuseStep 619247 = 928871) B928871
theorem B7533823 : Blo 618297 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B7928765 : Blo 618297 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B785791 : Blo 618297 785791 := bstep (se 1 (by rfl) ⟨589343, by rfl⟩ : syracuseStep 785791 = 1178687) B1178687
theorem B1572635 : Blo 618297 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B3539159 : Blo 618297 3539159 := bstep (se 1 (by rfl) ⟨2654369, by rfl⟩ : syracuseStep 3539159 = 5308739) B5308739
theorem B2098169 : Blo 618297 2098169 := bstep (se 2 (by rfl) ⟨786813, by rfl⟩ : syracuseStep 2098169 = 1573627) B1573627
theorem B2098223 : Blo 618297 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B2099195 : Blo 618297 2099195 := bstep (se 1 (by rfl) ⟨1574396, by rfl⟩ : syracuseStep 2099195 = 3148793) B3148793
theorem B5313113 : Blo 618297 5313113 := bstep (se 2 (by rfl) ⟨1992417, by rfl⟩ : syracuseStep 5313113 = 3984835) B3984835
theorem B4723433 : Blo 618297 4723433 := bstep (se 2 (by rfl) ⟨1771287, by rfl⟩ : syracuseStep 4723433 = 3542575) B3542575
theorem B5285843 : Blo 618297 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B5974793 : Blo 618297 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B2239481 : Blo 618297 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B1391615 : Blo 618297 1391615 := bstep (se 1 (by rfl) ⟨1043711, by rfl⟩ : syracuseStep 1391615 = 2087423) B2087423
theorem B1981577 : Blo 618297 1981577 := bstep (se 2 (by rfl) ⟨743091, by rfl⟩ : syracuseStep 1981577 = 1486183) B1486183
theorem B4701563 : Blo 618297 4701563 := bstep (se 1 (by rfl) ⟨3526172, by rfl⟩ : syracuseStep 4701563 = 7052345) B7052345
theorem B17875241 : Blo 618297 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B11289431 : Blo 618297 11289431 := bstep (se 1 (by rfl) ⟨8467073, by rfl⟩ : syracuseStep 11289431 = 16934147) B16934147
theorem B1328159 : Blo 618297 1328159 := bstep (se 1 (by rfl) ⟨996119, by rfl⟩ : syracuseStep 1328159 = 1992239) B1992239
theorem B10045097 : Blo 618297 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B29773817 : Blo 618297 29773817 := bstep (se 2 (by rfl) ⟨11165181, by rfl⟩ : syracuseStep 29773817 = 22330363) B22330363
theorem B5361983 : Blo 618297 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B6346153 : Blo 618297 6346153 := bstep (se 2 (by rfl) ⟨2379807, by rfl⟩ : syracuseStep 6346153 = 4759615) B4759615
theorem B2382119 : Blo 618297 2382119 := bstep (se 1 (by rfl) ⟨1786589, by rfl⟩ : syracuseStep 2382119 = 3573179) B3573179
theorem B2089043 : Blo 618297 2089043 := bstep (se 1 (by rfl) ⟨1566782, by rfl⟩ : syracuseStep 2089043 = 3133565) B3133565
theorem B16083359 : Blo 618297 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B5958107 : Blo 618297 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B8940851 : Blo 618297 8940851 := bstep (se 1 (by rfl) ⟨6705638, by rfl⟩ : syracuseStep 8940851 = 13411277) B13411277
theorem B1568767 : Blo 618297 1568767 := bstep (se 1 (by rfl) ⟨1176575, by rfl⟩ : syracuseStep 1568767 = 2353151) B2353151
theorem B2978785 : Blo 618297 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B54295633 : Blo 618297 54295633 := bstep (se 2 (by rfl) ⟨20360862, by rfl⟩ : syracuseStep 54295633 = 40721725) B40721725
theorem B1047721 : Blo 618297 1047721 := bstep (se 2 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 1047721 = 785791) B785791
theorem B1048423 : Blo 618297 1048423 := bstep (se 1 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 1048423 = 1572635) B1572635
theorem B2359439 : Blo 618297 2359439 := bstep (se 1 (by rfl) ⟨1769579, by rfl⟩ : syracuseStep 2359439 = 3539159) B3539159
theorem B885439 : Blo 618297 885439 := bstep (se 1 (by rfl) ⟨664079, by rfl⟩ : syracuseStep 885439 = 1328159) B1328159
theorem B3574655 : Blo 618297 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B3542075 : Blo 618297 3542075 := bstep (se 1 (by rfl) ⟨2656556, by rfl⟩ : syracuseStep 3542075 = 5313113) B5313113
theorem B3148955 : Blo 618297 3148955 := bstep (se 1 (by rfl) ⟨2361716, by rfl⟩ : syracuseStep 3148955 = 4723433) B4723433
theorem B3971713 : Blo 618297 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B10722239 : Blo 618297 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B3972071 : Blo 618297 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B72394177 : Blo 618297 72394177 := bstep (se 2 (by rfl) ⟨27147816, by rfl⟩ : syracuseStep 72394177 = 54295633) B54295633
theorem B927743 : Blo 618297 927743 := bstep (se 1 (by rfl) ⟨695807, by rfl⟩ : syracuseStep 927743 = 1391615) B1391615
theorem B1321051 : Blo 618297 1321051 := bstep (se 1 (by rfl) ⟨990788, by rfl⟩ : syracuseStep 1321051 = 1981577) B1981577
theorem B6696731 : Blo 618297 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B1588079 : Blo 618297 1588079 := bstep (se 1 (by rfl) ⟨1191059, by rfl⟩ : syracuseStep 1588079 = 2382119) B2382119
theorem B1392695 : Blo 618297 1392695 := bstep (se 1 (by rfl) ⟨1044521, by rfl⟩ : syracuseStep 1392695 = 2089043) B2089043
theorem B3523895 : Blo 618297 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B3983195 : Blo 618297 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B1492987 : Blo 618297 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B1396961 : Blo 618297 1396961 := bstep (se 2 (by rfl) ⟨523860, by rfl⟩ : syracuseStep 1396961 = 1047721) B1047721
theorem B3134375 : Blo 618297 3134375 := bstep (se 1 (by rfl) ⟨2350781, by rfl⟩ : syracuseStep 3134375 = 4701563) B4701563
theorem B1397897 : Blo 618297 1397897 := bstep (se 2 (by rfl) ⟨524211, by rfl⟩ : syracuseStep 1397897 = 1048423) B1048423
theorem B11916827 : Blo 618297 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B7526287 : Blo 618297 7526287 := bstep (se 1 (by rfl) ⟨5644715, by rfl⟩ : syracuseStep 7526287 = 11289431) B11289431
theorem B1398779 : Blo 618297 1398779 := bstep (se 1 (by rfl) ⟨1049084, by rfl⟩ : syracuseStep 1398779 = 2098169) B2098169
theorem B1398815 : Blo 618297 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B1399463 : Blo 618297 1399463 := bstep (se 1 (by rfl) ⟨1049597, by rfl⟩ : syracuseStep 1399463 = 2099195) B2099195
theorem B19849211 : Blo 618297 19849211 := bstep (se 1 (by rfl) ⟨14886908, by rfl⟩ : syracuseStep 19849211 = 29773817) B29773817
theorem B2091689 : Blo 618297 2091689 := bstep (se 2 (by rfl) ⟨784383, by rfl⟩ : syracuseStep 2091689 = 1568767) B1568767
theorem B5960567 : Blo 618297 5960567 := bstep (se 1 (by rfl) ⟨4470425, by rfl⟩ : syracuseStep 5960567 = 8940851) B8940851
theorem B33846149 : Blo 618297 33846149 := bstep (se 4 (by rfl) ⟨3173076, by rfl⟩ : syracuseStep 33846149 = 6346153) B6346153
theorem B1572959 : Blo 618297 1572959 := bstep (se 1 (by rfl) ⟨1179719, by rfl⟩ : syracuseStep 1572959 = 2359439) B2359439
theorem B1180585 : Blo 618297 1180585 := bstep (se 2 (by rfl) ⟨442719, by rfl⟩ : syracuseStep 1180585 = 885439) B885439
theorem B2655463 : Blo 618297 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B2361383 : Blo 618297 2361383 := bstep (se 1 (by rfl) ⟨1771037, by rfl⟩ : syracuseStep 2361383 = 3542075) B3542075
theorem B2099303 : Blo 618297 2099303 := bstep (se 1 (by rfl) ⟨1574477, by rfl⟩ : syracuseStep 2099303 = 3148955) B3148955
theorem B7148159 : Blo 618297 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B4464487 : Blo 618297 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B10035049 : Blo 618297 10035049 := bstep (se 2 (by rfl) ⟨3763143, by rfl⟩ : syracuseStep 10035049 = 7526287) B7526287
theorem B3973711 : Blo 618297 3973711 := bstep (se 1 (by rfl) ⟨2980283, by rfl⟩ : syracuseStep 3973711 = 5960567) B5960567
theorem B1058719 : Blo 618297 1058719 := bstep (se 1 (by rfl) ⟨794039, by rfl⟩ : syracuseStep 1058719 = 1588079) B1588079
theorem B928463 : Blo 618297 928463 := bstep (se 1 (by rfl) ⟨696347, by rfl⟩ : syracuseStep 928463 = 1392695) B1392695
theorem B931307 : Blo 618297 931307 := bstep (se 1 (by rfl) ⟨698480, by rfl⟩ : syracuseStep 931307 = 1396961) B1396961
theorem B931931 : Blo 618297 931931 := bstep (se 1 (by rfl) ⟨698948, by rfl⟩ : syracuseStep 931931 = 1397897) B1397897
theorem B7944551 : Blo 618297 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B932519 : Blo 618297 932519 := bstep (se 1 (by rfl) ⟨699389, by rfl⟩ : syracuseStep 932519 = 1398779) B1398779
theorem B932543 : Blo 618297 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B932975 : Blo 618297 932975 := bstep (se 1 (by rfl) ⟨699731, by rfl⟩ : syracuseStep 932975 = 1399463) B1399463
theorem B1394459 : Blo 618297 1394459 := bstep (se 1 (by rfl) ⟨1045844, by rfl⟩ : syracuseStep 1394459 = 2091689) B2091689
theorem B22564099 : Blo 618297 22564099 := bstep (se 1 (by rfl) ⟨16923074, by rfl⟩ : syracuseStep 22564099 = 33846149) B33846149
theorem B5295617 : Blo 618297 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B2349263 : Blo 618297 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B2383103 : Blo 618297 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B96525569 : Blo 618297 96525569 := bstep (se 2 (by rfl) ⟨36197088, by rfl⟩ : syracuseStep 96525569 = 72394177) B72394177
theorem B1990649 : Blo 618297 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B1761401 : Blo 618297 1761401 := bstep (se 2 (by rfl) ⟨660525, by rfl⟩ : syracuseStep 1761401 = 1321051) B1321051
theorem B2089583 : Blo 618297 2089583 := bstep (se 1 (by rfl) ⟨1567187, by rfl⟩ : syracuseStep 2089583 = 3134375) B3134375
theorem B2648047 : Blo 618297 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B13232807 : Blo 618297 13232807 := bstep (se 1 (by rfl) ⟨9924605, by rfl⟩ : syracuseStep 13232807 = 19849211) B19849211
theorem B618495 : Blo 618297 618495 := bstep (se 1 (by rfl) ⟨463871, by rfl⟩ : syracuseStep 618495 = 927743) B927743
theorem B1048639 : Blo 618297 1048639 := bstep (se 1 (by rfl) ⟨786479, by rfl⟩ : syracuseStep 1048639 = 1572959) B1572959
theorem B1574113 : Blo 618297 1574113 := bstep (se 2 (by rfl) ⟨590292, by rfl⟩ : syracuseStep 1574113 = 1180585) B1180585
theorem B1574255 : Blo 618297 1574255 := bstep (se 1 (by rfl) ⟨1180691, by rfl⟩ : syracuseStep 1574255 = 2361383) B2361383
theorem B3540617 : Blo 618297 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B1411625 : Blo 618297 1411625 := bstep (se 2 (by rfl) ⟨529359, by rfl⟩ : syracuseStep 1411625 = 1058719) B1058719
theorem B30085465 : Blo 618297 30085465 := bstep (se 2 (by rfl) ⟨11282049, by rfl⟩ : syracuseStep 30085465 = 22564099) B22564099
theorem B8821871 : Blo 618297 8821871 := bstep (se 1 (by rfl) ⟨6616403, by rfl⟩ : syracuseStep 8821871 = 13232807) B13232807
theorem B13380065 : Blo 618297 13380065 := bstep (se 2 (by rfl) ⟨5017524, by rfl⟩ : syracuseStep 13380065 = 10035049) B10035049
theorem B929639 : Blo 618297 929639 := bstep (se 1 (by rfl) ⟨697229, by rfl⟩ : syracuseStep 929639 = 1394459) B1394459
theorem B4765439 : Blo 618297 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B1588735 : Blo 618297 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B1327099 : Blo 618297 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B1393055 : Blo 618297 1393055 := bstep (se 1 (by rfl) ⟨1044791, by rfl⟩ : syracuseStep 1393055 = 2089583) B2089583
theorem B5296367 : Blo 618297 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B5952649 : Blo 618297 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B5298281 : Blo 618297 5298281 := bstep (se 2 (by rfl) ⟨1986855, by rfl⟩ : syracuseStep 5298281 = 3973711) B3973711
theorem B1399535 : Blo 618297 1399535 := bstep (se 1 (by rfl) ⟨1049651, by rfl⟩ : syracuseStep 1399535 = 2099303) B2099303
theorem B3530411 : Blo 618297 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B3530729 : Blo 618297 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B1566175 : Blo 618297 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B64350379 : Blo 618297 64350379 := bstep (se 1 (by rfl) ⟨48262784, by rfl⟩ : syracuseStep 64350379 = 96525569) B96525569
theorem B1174267 : Blo 618297 1174267 := bstep (se 1 (by rfl) ⟨880700, by rfl⟩ : syracuseStep 1174267 = 1761401) B1761401
theorem B618975 : Blo 618297 618975 := bstep (se 1 (by rfl) ⟨464231, by rfl⟩ : syracuseStep 618975 = 928463) B928463
theorem B620871 : Blo 618297 620871 := bstep (se 1 (by rfl) ⟨465653, by rfl⟩ : syracuseStep 620871 = 931307) B931307
theorem B621287 : Blo 618297 621287 := bstep (se 1 (by rfl) ⟨465965, by rfl⟩ : syracuseStep 621287 = 931931) B931931
theorem B621679 : Blo 618297 621679 := bstep (se 1 (by rfl) ⟨466259, by rfl⟩ : syracuseStep 621679 = 932519) B932519
theorem B621695 : Blo 618297 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B621983 : Blo 618297 621983 := bstep (se 1 (by rfl) ⟨466487, by rfl⟩ : syracuseStep 621983 = 932975) B932975
theorem B1049503 : Blo 618297 1049503 := bstep (se 1 (by rfl) ⟨787127, by rfl⟩ : syracuseStep 1049503 = 1574255) B1574255
theorem B2360411 : Blo 618297 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B2098817 : Blo 618297 2098817 := bstep (se 2 (by rfl) ⟨787056, by rfl⟩ : syracuseStep 2098817 = 1574113) B1574113
theorem B40113953 : Blo 618297 40113953 := bstep (se 2 (by rfl) ⟨15042732, by rfl⟩ : syracuseStep 40113953 = 30085465) B30085465
theorem B7936865 : Blo 618297 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B8920043 : Blo 618297 8920043 := bstep (se 1 (by rfl) ⟨6690032, by rfl⟩ : syracuseStep 8920043 = 13380065) B13380065
theorem B928703 : Blo 618297 928703 := bstep (se 1 (by rfl) ⟨696527, by rfl⟩ : syracuseStep 928703 = 1393055) B1393055
theorem B85800505 : Blo 618297 85800505 := bstep (se 2 (by rfl) ⟨32175189, by rfl⟩ : syracuseStep 85800505 = 64350379) B64350379
theorem B933023 : Blo 618297 933023 := bstep (se 1 (by rfl) ⟨699767, by rfl⟩ : syracuseStep 933023 = 1399535) B1399535
theorem B5881247 : Blo 618297 5881247 := bstep (se 1 (by rfl) ⟨4410935, by rfl⟩ : syracuseStep 5881247 = 8821871) B8821871
theorem B2118313 : Blo 618297 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B1398185 : Blo 618297 1398185 := bstep (se 2 (by rfl) ⟨524319, by rfl⟩ : syracuseStep 1398185 = 1048639) B1048639
theorem B2088233 : Blo 618297 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B3530911 : Blo 618297 3530911 := bstep (se 1 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 3530911 = 5296367) B5296367
theorem B1565689 : Blo 618297 1565689 := bstep (se 2 (by rfl) ⟨587133, by rfl⟩ : syracuseStep 1565689 = 1174267) B1174267
theorem B3532187 : Blo 618297 3532187 := bstep (se 1 (by rfl) ⟨2649140, by rfl⟩ : syracuseStep 3532187 = 5298281) B5298281
theorem B12707837 : Blo 618297 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B2353607 : Blo 618297 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B2353819 : Blo 618297 2353819 := bstep (se 1 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 2353819 = 3530729) B3530729
theorem B3764333 : Blo 618297 3764333 := bstep (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) B1411625
theorem B619759 : Blo 618297 619759 := bstep (se 1 (by rfl) ⟨464819, by rfl⟩ : syracuseStep 619759 = 929639) B929639
theorem B1769465 : Blo 618297 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B1573607 : Blo 618297 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B26742635 : Blo 618297 26742635 := bstep (se 1 (by rfl) ⟨20056976, by rfl⟩ : syracuseStep 26742635 = 40113953) B40113953
theorem B2824417 : Blo 618297 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B114400673 : Blo 618297 114400673 := bstep (se 2 (by rfl) ⟨42900252, by rfl⟩ : syracuseStep 114400673 = 85800505) B85800505
theorem B932123 : Blo 618297 932123 := bstep (se 1 (by rfl) ⟨699092, by rfl⟩ : syracuseStep 932123 = 1398185) B1398185
theorem B5291243 : Blo 618297 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B5946695 : Blo 618297 5946695 := bstep (se 1 (by rfl) ⟨4460021, by rfl⟩ : syracuseStep 5946695 = 8920043) B8920043
theorem B1392155 : Blo 618297 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B8471891 : Blo 618297 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B2509555 : Blo 618297 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B3920831 : Blo 618297 3920831 := bstep (se 1 (by rfl) ⟨2940623, by rfl⟩ : syracuseStep 3920831 = 5881247) B5881247
theorem B4707881 : Blo 618297 4707881 := bstep (se 2 (by rfl) ⟨1765455, by rfl⟩ : syracuseStep 4707881 = 3530911) B3530911
theorem B1399211 : Blo 618297 1399211 := bstep (se 1 (by rfl) ⟨1049408, by rfl⟩ : syracuseStep 1399211 = 2098817) B2098817
theorem B1399337 : Blo 618297 1399337 := bstep (se 2 (by rfl) ⟨524751, by rfl⟩ : syracuseStep 1399337 = 1049503) B1049503
theorem B2087585 : Blo 618297 2087585 := bstep (se 2 (by rfl) ⟨782844, by rfl⟩ : syracuseStep 2087585 = 1565689) B1565689
theorem B3138425 : Blo 618297 3138425 := bstep (se 2 (by rfl) ⟨1176909, by rfl⟩ : syracuseStep 3138425 = 2353819) B2353819
theorem B2354791 : Blo 618297 2354791 := bstep (se 1 (by rfl) ⟨1766093, by rfl⟩ : syracuseStep 2354791 = 3532187) B3532187
theorem B1569071 : Blo 618297 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B619135 : Blo 618297 619135 := bstep (se 1 (by rfl) ⟨464351, by rfl⟩ : syracuseStep 619135 = 928703) B928703
theorem B622015 : Blo 618297 622015 := bstep (se 1 (by rfl) ⟨466511, by rfl⟩ : syracuseStep 622015 = 933023) B933023
theorem B4718573 : Blo 618297 4718573 := bstep (se 3 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 4718573 = 1769465) B1769465
theorem B1049071 : Blo 618297 1049071 := bstep (se 1 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 1049071 = 1573607) B1573607
theorem B17828423 : Blo 618297 17828423 := bstep (se 1 (by rfl) ⟨13371317, by rfl⟩ : syracuseStep 17828423 = 26742635) B26742635
theorem B3346073 : Blo 618297 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B928103 : Blo 618297 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B22591709 : Blo 618297 22591709 := bstep (se 3 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 22591709 = 8471891) B8471891
theorem B932807 : Blo 618297 932807 := bstep (se 1 (by rfl) ⟨699605, by rfl⟩ : syracuseStep 932807 = 1399211) B1399211
theorem B932891 : Blo 618297 932891 := bstep (se 1 (by rfl) ⟨699668, by rfl⟩ : syracuseStep 932891 = 1399337) B1399337
theorem B1391723 : Blo 618297 1391723 := bstep (se 1 (by rfl) ⟨1043792, by rfl⟩ : syracuseStep 1391723 = 2087585) B2087585
theorem B76267115 : Blo 618297 76267115 := bstep (se 1 (by rfl) ⟨57200336, by rfl⟩ : syracuseStep 76267115 = 114400673) B114400673
theorem B3527495 : Blo 618297 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B2613887 : Blo 618297 2613887 := bstep (se 1 (by rfl) ⟨1960415, by rfl⟩ : syracuseStep 2613887 = 3920831) B3920831
theorem B3138587 : Blo 618297 3138587 := bstep (se 1 (by rfl) ⟨2353940, by rfl⟩ : syracuseStep 3138587 = 4707881) B4707881
theorem B3139721 : Blo 618297 3139721 := bstep (se 2 (by rfl) ⟨1177395, by rfl⟩ : syracuseStep 3139721 = 2354791) B2354791
theorem B2092283 : Blo 618297 2092283 := bstep (se 1 (by rfl) ⟨1569212, by rfl⟩ : syracuseStep 2092283 = 3138425) B3138425
theorem B1046047 : Blo 618297 1046047 := bstep (se 1 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 1046047 = 1569071) B1569071
theorem B3765889 : Blo 618297 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B621415 : Blo 618297 621415 := bstep (se 1 (by rfl) ⟨466061, by rfl⟩ : syracuseStep 621415 = 932123) B932123
theorem B3964463 : Blo 618297 3964463 := bstep (se 1 (by rfl) ⟨2973347, by rfl⟩ : syracuseStep 3964463 = 5946695) B5946695
theorem B3145715 : Blo 618297 3145715 := bstep (se 1 (by rfl) ⟨2359286, by rfl⟩ : syracuseStep 3145715 = 4718573) B4718573
theorem B2230715 : Blo 618297 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B1742591 : Blo 618297 1742591 := bstep (se 1 (by rfl) ⟨1306943, by rfl⟩ : syracuseStep 1742591 = 2613887) B2613887
theorem B5021185 : Blo 618297 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B927815 : Blo 618297 927815 := bstep (se 1 (by rfl) ⟨695861, by rfl⟩ : syracuseStep 927815 = 1391723) B1391723
theorem B1394729 : Blo 618297 1394729 := bstep (se 2 (by rfl) ⟨523023, by rfl⟩ : syracuseStep 1394729 = 1046047) B1046047
theorem B1394855 : Blo 618297 1394855 := bstep (se 1 (by rfl) ⟨1046141, by rfl⟩ : syracuseStep 1394855 = 2092283) B2092283
theorem B15061139 : Blo 618297 15061139 := bstep (se 1 (by rfl) ⟨11295854, by rfl⟩ : syracuseStep 15061139 = 22591709) B22591709
theorem B2642975 : Blo 618297 2642975 := bstep (se 1 (by rfl) ⟨1982231, by rfl⟩ : syracuseStep 2642975 = 3964463) B3964463
theorem B50844743 : Blo 618297 50844743 := bstep (se 1 (by rfl) ⟨38133557, by rfl⟩ : syracuseStep 50844743 = 76267115) B76267115
theorem B1398761 : Blo 618297 1398761 := bstep (se 2 (by rfl) ⟨524535, by rfl⟩ : syracuseStep 1398761 = 1049071) B1049071
theorem B11885615 : Blo 618297 11885615 := bstep (se 1 (by rfl) ⟨8914211, by rfl⟩ : syracuseStep 11885615 = 17828423) B17828423
theorem B2351663 : Blo 618297 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B2092391 : Blo 618297 2092391 := bstep (se 1 (by rfl) ⟨1569293, by rfl⟩ : syracuseStep 2092391 = 3138587) B3138587
theorem B2093147 : Blo 618297 2093147 := bstep (se 1 (by rfl) ⟨1569860, by rfl⟩ : syracuseStep 2093147 = 3139721) B3139721
theorem B618735 : Blo 618297 618735 := bstep (se 1 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 618735 = 928103) B928103
theorem B621871 : Blo 618297 621871 := bstep (se 1 (by rfl) ⟨466403, by rfl⟩ : syracuseStep 621871 = 932807) B932807
theorem B621927 : Blo 618297 621927 := bstep (se 1 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 621927 = 932891) B932891
theorem B2097143 : Blo 618297 2097143 := bstep (se 1 (by rfl) ⟨1572857, by rfl⟩ : syracuseStep 2097143 = 3145715) B3145715
theorem B6694913 : Blo 618297 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B929819 : Blo 618297 929819 := bstep (se 1 (by rfl) ⟨697364, by rfl⟩ : syracuseStep 929819 = 1394729) B1394729
theorem B929903 : Blo 618297 929903 := bstep (se 1 (by rfl) ⟨697427, by rfl⟩ : syracuseStep 929903 = 1394855) B1394855
theorem B1487143 : Blo 618297 1487143 := bstep (se 1 (by rfl) ⟨1115357, by rfl⟩ : syracuseStep 1487143 = 2230715) B2230715
theorem B10040759 : Blo 618297 10040759 := bstep (se 1 (by rfl) ⟨7530569, by rfl⟩ : syracuseStep 10040759 = 15061139) B15061139
theorem B33896495 : Blo 618297 33896495 := bstep (se 1 (by rfl) ⟨25422371, by rfl⟩ : syracuseStep 33896495 = 50844743) B50844743
theorem B932507 : Blo 618297 932507 := bstep (se 1 (by rfl) ⟨699380, by rfl⟩ : syracuseStep 932507 = 1398761) B1398761
theorem B1394927 : Blo 618297 1394927 := bstep (se 1 (by rfl) ⟨1046195, by rfl⟩ : syracuseStep 1394927 = 2092391) B2092391
theorem B1395431 : Blo 618297 1395431 := bstep (se 1 (by rfl) ⟨1046573, by rfl⟩ : syracuseStep 1395431 = 2093147) B2093147
theorem B1398095 : Blo 618297 1398095 := bstep (se 1 (by rfl) ⟨1048571, by rfl⟩ : syracuseStep 1398095 = 2097143) B2097143
theorem B1761983 : Blo 618297 1761983 := bstep (se 1 (by rfl) ⟨1321487, by rfl⟩ : syracuseStep 1761983 = 2642975) B2642975
theorem B4646909 : Blo 618297 4646909 := bstep (se 3 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 4646909 = 1742591) B1742591
theorem B7923743 : Blo 618297 7923743 := bstep (se 1 (by rfl) ⟨5942807, by rfl⟩ : syracuseStep 7923743 = 11885615) B11885615
theorem B1567775 : Blo 618297 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B618543 : Blo 618297 618543 := bstep (se 1 (by rfl) ⟨463907, by rfl⟩ : syracuseStep 618543 = 927815) B927815
theorem B7931429 : Blo 618297 7931429 := bstep (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) B1487143
theorem B4463275 : Blo 618297 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B5282495 : Blo 618297 5282495 := bstep (se 1 (by rfl) ⟨3961871, by rfl⟩ : syracuseStep 5282495 = 7923743) B7923743
theorem B6693839 : Blo 618297 6693839 := bstep (se 1 (by rfl) ⟨5020379, by rfl⟩ : syracuseStep 6693839 = 10040759) B10040759
theorem B929951 : Blo 618297 929951 := bstep (se 1 (by rfl) ⟨697463, by rfl⟩ : syracuseStep 929951 = 1394927) B1394927
theorem B930287 : Blo 618297 930287 := bstep (se 1 (by rfl) ⟨697715, by rfl⟩ : syracuseStep 930287 = 1395431) B1395431
theorem B932063 : Blo 618297 932063 := bstep (se 1 (by rfl) ⟨699047, by rfl⟩ : syracuseStep 932063 = 1398095) B1398095
theorem B3097939 : Blo 618297 3097939 := bstep (se 1 (by rfl) ⟨2323454, by rfl⟩ : syracuseStep 3097939 = 4646909) B4646909
theorem B22597663 : Blo 618297 22597663 := bstep (se 1 (by rfl) ⟨16948247, by rfl⟩ : syracuseStep 22597663 = 33896495) B33896495
theorem B1174655 : Blo 618297 1174655 := bstep (se 1 (by rfl) ⟨880991, by rfl⟩ : syracuseStep 1174655 = 1761983) B1761983
theorem B1045183 : Blo 618297 1045183 := bstep (se 1 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 1045183 = 1567775) B1567775
theorem B619879 : Blo 618297 619879 := bstep (se 1 (by rfl) ⟨464909, by rfl⟩ : syracuseStep 619879 = 929819) B929819
theorem B619935 : Blo 618297 619935 := bstep (se 1 (by rfl) ⟨464951, by rfl⟩ : syracuseStep 619935 = 929903) B929903
theorem B621671 : Blo 618297 621671 := bstep (se 1 (by rfl) ⟨466253, by rfl⟩ : syracuseStep 621671 = 932507) B932507
theorem B4130585 : Blo 618297 4130585 := bstep (se 2 (by rfl) ⟨1548969, by rfl⟩ : syracuseStep 4130585 = 3097939) B3097939
theorem B4462559 : Blo 618297 4462559 := bstep (se 1 (by rfl) ⟨3346919, by rfl⟩ : syracuseStep 4462559 = 6693839) B6693839
theorem B5287619 : Blo 618297 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B3521663 : Blo 618297 3521663 := bstep (se 1 (by rfl) ⟨2641247, by rfl⟩ : syracuseStep 3521663 = 5282495) B5282495
theorem B30130217 : Blo 618297 30130217 := bstep (se 2 (by rfl) ⟨11298831, by rfl⟩ : syracuseStep 30130217 = 22597663) B22597663
theorem B1393577 : Blo 618297 1393577 := bstep (se 2 (by rfl) ⟨522591, by rfl⟩ : syracuseStep 1393577 = 1045183) B1045183
theorem B5951033 : Blo 618297 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B783103 : Blo 618297 783103 := bstep (se 1 (by rfl) ⟨587327, by rfl⟩ : syracuseStep 783103 = 1174655) B1174655
theorem B619967 : Blo 618297 619967 := bstep (se 1 (by rfl) ⟨464975, by rfl⟩ : syracuseStep 619967 = 929951) B929951
theorem B620191 : Blo 618297 620191 := bstep (se 1 (by rfl) ⟨465143, by rfl⟩ : syracuseStep 620191 = 930287) B930287
theorem B621375 : Blo 618297 621375 := bstep (se 1 (by rfl) ⟨466031, by rfl⟩ : syracuseStep 621375 = 932063) B932063
theorem B20086811 : Blo 618297 20086811 := bstep (se 1 (by rfl) ⟨15065108, by rfl⟩ : syracuseStep 20086811 = 30130217) B30130217
theorem B2753723 : Blo 618297 2753723 := bstep (se 1 (by rfl) ⟨2065292, by rfl⟩ : syracuseStep 2753723 = 4130585) B4130585
theorem B3967355 : Blo 618297 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B929051 : Blo 618297 929051 := bstep (se 1 (by rfl) ⟨696788, by rfl⟩ : syracuseStep 929051 = 1393577) B1393577
theorem B3525079 : Blo 618297 3525079 := bstep (se 1 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 3525079 = 5287619) B5287619
theorem B2347775 : Blo 618297 2347775 := bstep (se 1 (by rfl) ⟨1760831, by rfl⟩ : syracuseStep 2347775 = 3521663) B3521663
theorem B2975039 : Blo 618297 2975039 := bstep (se 1 (by rfl) ⟨2231279, by rfl⟩ : syracuseStep 2975039 = 4462559) B4462559
theorem B1044137 : Blo 618297 1044137 := bstep (se 2 (by rfl) ⟨391551, by rfl⟩ : syracuseStep 1044137 = 783103) B783103
theorem B7343261 : Blo 618297 7343261 := bstep (se 3 (by rfl) ⟨1376861, by rfl⟩ : syracuseStep 7343261 = 2753723) B2753723
theorem B696091 : Blo 618297 696091 := bstep (se 1 (by rfl) ⟨522068, by rfl⟩ : syracuseStep 696091 = 1044137) B1044137
theorem B4700105 : Blo 618297 4700105 := bstep (se 2 (by rfl) ⟨1762539, by rfl⟩ : syracuseStep 4700105 = 3525079) B3525079
theorem B1983359 : Blo 618297 1983359 := bstep (se 1 (by rfl) ⟨1487519, by rfl⟩ : syracuseStep 1983359 = 2975039) B2975039
theorem B13391207 : Blo 618297 13391207 := bstep (se 1 (by rfl) ⟨10043405, by rfl⟩ : syracuseStep 13391207 = 20086811) B20086811
theorem B2644903 : Blo 618297 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B1565183 : Blo 618297 1565183 := bstep (se 1 (by rfl) ⟨1173887, by rfl⟩ : syracuseStep 1565183 = 2347775) B2347775
theorem B619367 : Blo 618297 619367 := bstep (se 1 (by rfl) ⟨464525, by rfl⟩ : syracuseStep 619367 = 929051) B929051
theorem B928121 : Blo 618297 928121 := bstep (se 2 (by rfl) ⟨348045, by rfl⟩ : syracuseStep 928121 = 696091) B696091
theorem B1322239 : Blo 618297 1322239 := bstep (se 1 (by rfl) ⟨991679, by rfl⟩ : syracuseStep 1322239 = 1983359) B1983359
theorem B4895507 : Blo 618297 4895507 := bstep (se 1 (by rfl) ⟨3671630, by rfl⟩ : syracuseStep 4895507 = 7343261) B7343261
theorem B8927471 : Blo 618297 8927471 := bstep (se 1 (by rfl) ⟨6695603, by rfl⟩ : syracuseStep 8927471 = 13391207) B13391207
theorem B3526537 : Blo 618297 3526537 := bstep (se 2 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 3526537 = 2644903) B2644903
theorem B3133403 : Blo 618297 3133403 := bstep (se 1 (by rfl) ⟨2350052, by rfl⟩ : syracuseStep 3133403 = 4700105) B4700105
theorem B1043455 : Blo 618297 1043455 := bstep (se 1 (by rfl) ⟨782591, by rfl⟩ : syracuseStep 1043455 = 1565183) B1565183
theorem B1391273 : Blo 618297 1391273 := bstep (se 2 (by rfl) ⟨521727, by rfl⟩ : syracuseStep 1391273 = 1043455) B1043455
theorem B4702049 : Blo 618297 4702049 := bstep (se 2 (by rfl) ⟨1763268, by rfl⟩ : syracuseStep 4702049 = 3526537) B3526537
theorem B3263671 : Blo 618297 3263671 := bstep (se 1 (by rfl) ⟨2447753, by rfl⟩ : syracuseStep 3263671 = 4895507) B4895507
theorem B5951647 : Blo 618297 5951647 := bstep (se 1 (by rfl) ⟨4463735, by rfl⟩ : syracuseStep 5951647 = 8927471) B8927471
theorem B2088935 : Blo 618297 2088935 := bstep (se 1 (by rfl) ⟨1566701, by rfl⟩ : syracuseStep 2088935 = 3133403) B3133403
theorem B1762985 : Blo 618297 1762985 := bstep (se 2 (by rfl) ⟨661119, by rfl⟩ : syracuseStep 1762985 = 1322239) B1322239
theorem B618747 : Blo 618297 618747 := bstep (se 1 (by rfl) ⟨464060, by rfl⟩ : syracuseStep 618747 = 928121) B928121
theorem B7935529 : Blo 618297 7935529 := bstep (se 2 (by rfl) ⟨2975823, by rfl⟩ : syracuseStep 7935529 = 5951647) B5951647
theorem B17406245 : Blo 618297 17406245 := bstep (se 4 (by rfl) ⟨1631835, by rfl⟩ : syracuseStep 17406245 = 3263671) B3263671
theorem B927515 : Blo 618297 927515 := bstep (se 1 (by rfl) ⟨695636, by rfl⟩ : syracuseStep 927515 = 1391273) B1391273
theorem B1392623 : Blo 618297 1392623 := bstep (se 1 (by rfl) ⟨1044467, by rfl⟩ : syracuseStep 1392623 = 2088935) B2088935
theorem B3134699 : Blo 618297 3134699 := bstep (se 1 (by rfl) ⟨2351024, by rfl⟩ : syracuseStep 3134699 = 4702049) B4702049
theorem B1175323 : Blo 618297 1175323 := bstep (se 1 (by rfl) ⟨881492, by rfl⟩ : syracuseStep 1175323 = 1762985) B1762985
theorem B11604163 : Blo 618297 11604163 := bstep (se 1 (by rfl) ⟨8703122, by rfl⟩ : syracuseStep 11604163 = 17406245) B17406245
theorem B928415 : Blo 618297 928415 := bstep (se 1 (by rfl) ⟨696311, by rfl⟩ : syracuseStep 928415 = 1392623) B1392623
theorem B2089799 : Blo 618297 2089799 := bstep (se 1 (by rfl) ⟨1567349, by rfl⟩ : syracuseStep 2089799 = 3134699) B3134699
theorem B1567097 : Blo 618297 1567097 := bstep (se 2 (by rfl) ⟨587661, by rfl⟩ : syracuseStep 1567097 = 1175323) B1175323
theorem B618343 : Blo 618297 618343 := bstep (se 1 (by rfl) ⟨463757, by rfl⟩ : syracuseStep 618343 = 927515) B927515
theorem B10580705 : Blo 618297 10580705 := bstep (se 2 (by rfl) ⟨3967764, by rfl⟩ : syracuseStep 10580705 = 7935529) B7935529
theorem B15472217 : Blo 618297 15472217 := bstep (se 2 (by rfl) ⟨5802081, by rfl⟩ : syracuseStep 15472217 = 11604163) B11604163
theorem B7053803 : Blo 618297 7053803 := bstep (se 1 (by rfl) ⟨5290352, by rfl⟩ : syracuseStep 7053803 = 10580705) B10580705
theorem B1393199 : Blo 618297 1393199 := bstep (se 1 (by rfl) ⟨1044899, by rfl⟩ : syracuseStep 1393199 = 2089799) B2089799
theorem B1044731 : Blo 618297 1044731 := bstep (se 1 (by rfl) ⟨783548, by rfl⟩ : syracuseStep 1044731 = 1567097) B1567097
theorem B618943 : Blo 618297 618943 := bstep (se 1 (by rfl) ⟨464207, by rfl⟩ : syracuseStep 618943 = 928415) B928415
theorem B696487 : Blo 618297 696487 := bstep (se 1 (by rfl) ⟨522365, by rfl⟩ : syracuseStep 696487 = 1044731) B1044731
theorem B928799 : Blo 618297 928799 := bstep (se 1 (by rfl) ⟨696599, by rfl⟩ : syracuseStep 928799 = 1393199) B1393199
theorem B4702535 : Blo 618297 4702535 := bstep (se 1 (by rfl) ⟨3526901, by rfl⟩ : syracuseStep 4702535 = 7053803) B7053803
theorem B10314811 : Blo 618297 10314811 := bstep (se 1 (by rfl) ⟨7736108, by rfl⟩ : syracuseStep 10314811 = 15472217) B15472217
theorem B928649 : Blo 618297 928649 := bstep (se 2 (by rfl) ⟨348243, by rfl⟩ : syracuseStep 928649 = 696487) B696487
theorem B3135023 : Blo 618297 3135023 := bstep (se 1 (by rfl) ⟨2351267, by rfl⟩ : syracuseStep 3135023 = 4702535) B4702535
theorem B13753081 : Blo 618297 13753081 := bstep (se 2 (by rfl) ⟨5157405, by rfl⟩ : syracuseStep 13753081 = 10314811) B10314811
theorem B619199 : Blo 618297 619199 := bstep (se 1 (by rfl) ⟨464399, by rfl⟩ : syracuseStep 619199 = 928799) B928799
theorem B18337441 : Blo 618297 18337441 := bstep (se 2 (by rfl) ⟨6876540, by rfl⟩ : syracuseStep 18337441 = 13753081) B13753081
theorem B2090015 : Blo 618297 2090015 := bstep (se 1 (by rfl) ⟨1567511, by rfl⟩ : syracuseStep 2090015 = 3135023) B3135023
theorem B619099 : Blo 618297 619099 := bstep (se 1 (by rfl) ⟨464324, by rfl⟩ : syracuseStep 619099 = 928649) B928649
theorem B24449921 : Blo 618297 24449921 := bstep (se 2 (by rfl) ⟨9168720, by rfl⟩ : syracuseStep 24449921 = 18337441) B18337441
theorem B1393343 : Blo 618297 1393343 := bstep (se 1 (by rfl) ⟨1045007, by rfl⟩ : syracuseStep 1393343 = 2090015) B2090015
theorem B928895 : Blo 618297 928895 := bstep (se 1 (by rfl) ⟨696671, by rfl⟩ : syracuseStep 928895 = 1393343) B1393343
theorem B16299947 : Blo 618297 16299947 := bstep (se 1 (by rfl) ⟨12224960, by rfl⟩ : syracuseStep 16299947 = 24449921) B24449921
theorem B10866631 : Blo 618297 10866631 := bstep (se 1 (by rfl) ⟨8149973, by rfl⟩ : syracuseStep 10866631 = 16299947) B16299947
theorem B619263 : Blo 618297 619263 := bstep (se 1 (by rfl) ⟨464447, by rfl⟩ : syracuseStep 619263 = 928895) B928895
theorem B14488841 : Blo 618297 14488841 := bstep (se 2 (by rfl) ⟨5433315, by rfl⟩ : syracuseStep 14488841 = 10866631) B10866631
theorem B38636909 : Blo 618297 38636909 := bstep (se 3 (by rfl) ⟨7244420, by rfl⟩ : syracuseStep 38636909 = 14488841) B14488841
theorem B25757939 : Blo 618297 25757939 := bstep (se 1 (by rfl) ⟨19318454, by rfl⟩ : syracuseStep 25757939 = 38636909) B38636909
theorem B17171959 : Blo 618297 17171959 := bstep (se 1 (by rfl) ⟨12878969, by rfl⟩ : syracuseStep 17171959 = 25757939) B25757939
theorem B22895945 : Blo 618297 22895945 := bstep (se 2 (by rfl) ⟨8585979, by rfl⟩ : syracuseStep 22895945 = 17171959) B17171959
theorem B15263963 : Blo 618297 15263963 := bstep (se 1 (by rfl) ⟨11447972, by rfl⟩ : syracuseStep 15263963 = 22895945) B22895945
theorem B10175975 : Blo 618297 10175975 := bstep (se 1 (by rfl) ⟨7631981, by rfl⟩ : syracuseStep 10175975 = 15263963) B15263963
theorem B6783983 : Blo 618297 6783983 := bstep (se 1 (by rfl) ⟨5087987, by rfl⟩ : syracuseStep 6783983 = 10175975) B10175975
theorem B4522655 : Blo 618297 4522655 := bstep (se 1 (by rfl) ⟨3391991, by rfl⟩ : syracuseStep 4522655 = 6783983) B6783983
theorem B3015103 : Blo 618297 3015103 := bstep (se 1 (by rfl) ⟨2261327, by rfl⟩ : syracuseStep 3015103 = 4522655) B4522655
theorem B4020137 : Blo 618297 4020137 := bstep (se 2 (by rfl) ⟨1507551, by rfl⟩ : syracuseStep 4020137 = 3015103) B3015103
theorem B2680091 : Blo 618297 2680091 := bstep (se 1 (by rfl) ⟨2010068, by rfl⟩ : syracuseStep 2680091 = 4020137) B4020137
theorem B1786727 : Blo 618297 1786727 := bstep (se 1 (by rfl) ⟨1340045, by rfl⟩ : syracuseStep 1786727 = 2680091) B2680091
theorem B1191151 : Blo 618297 1191151 := bstep (se 1 (by rfl) ⟨893363, by rfl⟩ : syracuseStep 1191151 = 1786727) B1786727
theorem B6352805 : Blo 618297 6352805 := bstep (se 4 (by rfl) ⟨595575, by rfl⟩ : syracuseStep 6352805 = 1191151) B1191151
theorem B4235203 : Blo 618297 4235203 := bstep (se 1 (by rfl) ⟨3176402, by rfl⟩ : syracuseStep 4235203 = 6352805) B6352805
theorem B5646937 : Blo 618297 5646937 := bstep (se 2 (by rfl) ⟨2117601, by rfl⟩ : syracuseStep 5646937 = 4235203) B4235203
theorem B7529249 : Blo 618297 7529249 := bstep (se 2 (by rfl) ⟨2823468, by rfl⟩ : syracuseStep 7529249 = 5646937) B5646937
theorem B5019499 : Blo 618297 5019499 := bstep (se 1 (by rfl) ⟨3764624, by rfl⟩ : syracuseStep 5019499 = 7529249) B7529249
theorem B6692665 : Blo 618297 6692665 := bstep (se 2 (by rfl) ⟨2509749, by rfl⟩ : syracuseStep 6692665 = 5019499) B5019499
theorem B8923553 : Blo 618297 8923553 := bstep (se 2 (by rfl) ⟨3346332, by rfl⟩ : syracuseStep 8923553 = 6692665) B6692665
theorem B5949035 : Blo 618297 5949035 := bstep (se 1 (by rfl) ⟨4461776, by rfl⟩ : syracuseStep 5949035 = 8923553) B8923553
theorem B3966023 : Blo 618297 3966023 := bstep (se 1 (by rfl) ⟨2974517, by rfl⟩ : syracuseStep 3966023 = 5949035) B5949035
theorem B2644015 : Blo 618297 2644015 := bstep (se 1 (by rfl) ⟨1983011, by rfl⟩ : syracuseStep 2644015 = 3966023) B3966023
theorem B3525353 : Blo 618297 3525353 := bstep (se 2 (by rfl) ⟨1322007, by rfl⟩ : syracuseStep 3525353 = 2644015) B2644015
theorem B2350235 : Blo 618297 2350235 := bstep (se 1 (by rfl) ⟨1762676, by rfl⟩ : syracuseStep 2350235 = 3525353) B3525353
theorem B1566823 : Blo 618297 1566823 := bstep (se 1 (by rfl) ⟨1175117, by rfl⟩ : syracuseStep 1566823 = 2350235) B2350235
theorem B2089097 : Blo 618297 2089097 := bstep (se 2 (by rfl) ⟨783411, by rfl⟩ : syracuseStep 2089097 = 1566823) B1566823
theorem B1392731 : Blo 618297 1392731 := bstep (se 1 (by rfl) ⟨1044548, by rfl⟩ : syracuseStep 1392731 = 2089097) B2089097
theorem B928487 : Blo 618297 928487 := bstep (se 1 (by rfl) ⟨696365, by rfl⟩ : syracuseStep 928487 = 1392731) B1392731
theorem B618991 : Blo 618297 618991 := bstep (se 1 (by rfl) ⟨464243, by rfl⟩ : syracuseStep 618991 = 928487) B928487

theorem C0 (j : ℕ) (h1 : 154574 ≤ j) (h2 : j ≤ 155273) : Blo 618297 (4 * j + 3) := by
  interval_cases j
  · exact B618299
  · exact B618303
  · exact B618307
  · exact B618311
  · exact B618315
  · exact B618319
  · exact B618323
  · exact B618327
  · exact B618331
  · exact B618335
  · exact B618339
  · exact B618343
  · exact B618347
  · exact B618351
  · exact B618355
  · exact B618359
  · exact B618363
  · exact B618367
  · exact B618371
  · exact B618375
  · exact B618379
  · exact B618383
  · exact B618387
  · exact B618391
  · exact B618395
  · exact B618399
  · exact B618403
  · exact B618407
  · exact B618411
  · exact B618415
  · exact B618419
  · exact B618423
  · exact B618427
  · exact B618431
  · exact B618435
  · exact B618439
  · exact B618443
  · exact B618447
  · exact B618451
  · exact B618455
  · exact B618459
  · exact B618463
  · exact B618467
  · exact B618471
  · exact B618475
  · exact B618479
  · exact B618483
  · exact B618487
  · exact B618491
  · exact B618495
  · exact B618499
  · exact B618503
  · exact B618507
  · exact B618511
  · exact B618515
  · exact B618519
  · exact B618523
  · exact B618527
  · exact B618531
  · exact B618535
  · exact B618539
  · exact B618543
  · exact B618547
  · exact B618551
  · exact B618555
  · exact B618559
  · exact B618563
  · exact B618567
  · exact B618571
  · exact B618575
  · exact B618579
  · exact B618583
  · exact B618587
  · exact B618591
  · exact B618595
  · exact B618599
  · exact B618603
  · exact B618607
  · exact B618611
  · exact B618615
  · exact B618619
  · exact B618623
  · exact B618627
  · exact B618631
  · exact B618635
  · exact B618639
  · exact B618643
  · exact B618647
  · exact B618651
  · exact B618655
  · exact B618659
  · exact B618663
  · exact B618667
  · exact B618671
  · exact B618675
  · exact B618679
  · exact B618683
  · exact B618687
  · exact B618691
  · exact B618695
  · exact B618699
  · exact B618703
  · exact B618707
  · exact B618711
  · exact B618715
  · exact B618719
  · exact B618723
  · exact B618727
  · exact B618731
  · exact B618735
  · exact B618739
  · exact B618743
  · exact B618747
  · exact B618751
  · exact B618755
  · exact B618759
  · exact B618763
  · exact B618767
  · exact B618771
  · exact B618775
  · exact B618779
  · exact B618783
  · exact B618787
  · exact B618791
  · exact B618795
  · exact B618799
  · exact B618803
  · exact B618807
  · exact B618811
  · exact B618815
  · exact B618819
  · exact B618823
  · exact B618827
  · exact B618831
  · exact B618835
  · exact B618839
  · exact B618843
  · exact B618847
  · exact B618851
  · exact B618855
  · exact B618859
  · exact B618863
  · exact B618867
  · exact B618871
  · exact B618875
  · exact B618879
  · exact B618883
  · exact B618887
  · exact B618891
  · exact B618895
  · exact B618899
  · exact B618903
  · exact B618907
  · exact B618911
  · exact B618915
  · exact B618919
  · exact B618923
  · exact B618927
  · exact B618931
  · exact B618935
  · exact B618939
  · exact B618943
  · exact B618947
  · exact B618951
  · exact B618955
  · exact B618959
  · exact B618963
  · exact B618967
  · exact B618971
  · exact B618975
  · exact B618979
  · exact B618983
  · exact B618987
  · exact B618991
  · exact B618995
  · exact B618999
  · exact B619003
  · exact B619007
  · exact B619011
  · exact B619015
  · exact B619019
  · exact B619023
  · exact B619027
  · exact B619031
  · exact B619035
  · exact B619039
  · exact B619043
  · exact B619047
  · exact B619051
  · exact B619055
  · exact B619059
  · exact B619063
  · exact B619067
  · exact B619071
  · exact B619075
  · exact B619079
  · exact B619083
  · exact B619087
  · exact B619091
  · exact B619095
  · exact B619099
  · exact B619103
  · exact B619107
  · exact B619111
  · exact B619115
  · exact B619119
  · exact B619123
  · exact B619127
  · exact B619131
  · exact B619135
  · exact B619139
  · exact B619143
  · exact B619147
  · exact B619151
  · exact B619155
  · exact B619159
  · exact B619163
  · exact B619167
  · exact B619171
  · exact B619175
  · exact B619179
  · exact B619183
  · exact B619187
  · exact B619191
  · exact B619195
  · exact B619199
  · exact B619203
  · exact B619207
  · exact B619211
  · exact B619215
  · exact B619219
  · exact B619223
  · exact B619227
  · exact B619231
  · exact B619235
  · exact B619239
  · exact B619243
  · exact B619247
  · exact B619251
  · exact B619255
  · exact B619259
  · exact B619263
  · exact B619267
  · exact B619271
  · exact B619275
  · exact B619279
  · exact B619283
  · exact B619287
  · exact B619291
  · exact B619295
  · exact B619299
  · exact B619303
  · exact B619307
  · exact B619311
  · exact B619315
  · exact B619319
  · exact B619323
  · exact B619327
  · exact B619331
  · exact B619335
  · exact B619339
  · exact B619343
  · exact B619347
  · exact B619351
  · exact B619355
  · exact B619359
  · exact B619363
  · exact B619367
  · exact B619371
  · exact B619375
  · exact B619379
  · exact B619383
  · exact B619387
  · exact B619391
  · exact B619395
  · exact B619399
  · exact B619403
  · exact B619407
  · exact B619411
  · exact B619415
  · exact B619419
  · exact B619423
  · exact B619427
  · exact B619431
  · exact B619435
  · exact B619439
  · exact B619443
  · exact B619447
  · exact B619451
  · exact B619455
  · exact B619459
  · exact B619463
  · exact B619467
  · exact B619471
  · exact B619475
  · exact B619479
  · exact B619483
  · exact B619487
  · exact B619491
  · exact B619495
  · exact B619499
  · exact B619503
  · exact B619507
  · exact B619511
  · exact B619515
  · exact B619519
  · exact B619523
  · exact B619527
  · exact B619531
  · exact B619535
  · exact B619539
  · exact B619543
  · exact B619547
  · exact B619551
  · exact B619555
  · exact B619559
  · exact B619563
  · exact B619567
  · exact B619571
  · exact B619575
  · exact B619579
  · exact B619583
  · exact B619587
  · exact B619591
  · exact B619595
  · exact B619599
  · exact B619603
  · exact B619607
  · exact B619611
  · exact B619615
  · exact B619619
  · exact B619623
  · exact B619627
  · exact B619631
  · exact B619635
  · exact B619639
  · exact B619643
  · exact B619647
  · exact B619651
  · exact B619655
  · exact B619659
  · exact B619663
  · exact B619667
  · exact B619671
  · exact B619675
  · exact B619679
  · exact B619683
  · exact B619687
  · exact B619691
  · exact B619695
  · exact B619699
  · exact B619703
  · exact B619707
  · exact B619711
  · exact B619715
  · exact B619719
  · exact B619723
  · exact B619727
  · exact B619731
  · exact B619735
  · exact B619739
  · exact B619743
  · exact B619747
  · exact B619751
  · exact B619755
  · exact B619759
  · exact B619763
  · exact B619767
  · exact B619771
  · exact B619775
  · exact B619779
  · exact B619783
  · exact B619787
  · exact B619791
  · exact B619795
  · exact B619799
  · exact B619803
  · exact B619807
  · exact B619811
  · exact B619815
  · exact B619819
  · exact B619823
  · exact B619827
  · exact B619831
  · exact B619835
  · exact B619839
  · exact B619843
  · exact B619847
  · exact B619851
  · exact B619855
  · exact B619859
  · exact B619863
  · exact B619867
  · exact B619871
  · exact B619875
  · exact B619879
  · exact B619883
  · exact B619887
  · exact B619891
  · exact B619895
  · exact B619899
  · exact B619903
  · exact B619907
  · exact B619911
  · exact B619915
  · exact B619919
  · exact B619923
  · exact B619927
  · exact B619931
  · exact B619935
  · exact B619939
  · exact B619943
  · exact B619947
  · exact B619951
  · exact B619955
  · exact B619959
  · exact B619963
  · exact B619967
  · exact B619971
  · exact B619975
  · exact B619979
  · exact B619983
  · exact B619987
  · exact B619991
  · exact B619995
  · exact B619999
  · exact B620003
  · exact B620007
  · exact B620011
  · exact B620015
  · exact B620019
  · exact B620023
  · exact B620027
  · exact B620031
  · exact B620035
  · exact B620039
  · exact B620043
  · exact B620047
  · exact B620051
  · exact B620055
  · exact B620059
  · exact B620063
  · exact B620067
  · exact B620071
  · exact B620075
  · exact B620079
  · exact B620083
  · exact B620087
  · exact B620091
  · exact B620095
  · exact B620099
  · exact B620103
  · exact B620107
  · exact B620111
  · exact B620115
  · exact B620119
  · exact B620123
  · exact B620127
  · exact B620131
  · exact B620135
  · exact B620139
  · exact B620143
  · exact B620147
  · exact B620151
  · exact B620155
  · exact B620159
  · exact B620163
  · exact B620167
  · exact B620171
  · exact B620175
  · exact B620179
  · exact B620183
  · exact B620187
  · exact B620191
  · exact B620195
  · exact B620199
  · exact B620203
  · exact B620207
  · exact B620211
  · exact B620215
  · exact B620219
  · exact B620223
  · exact B620227
  · exact B620231
  · exact B620235
  · exact B620239
  · exact B620243
  · exact B620247
  · exact B620251
  · exact B620255
  · exact B620259
  · exact B620263
  · exact B620267
  · exact B620271
  · exact B620275
  · exact B620279
  · exact B620283
  · exact B620287
  · exact B620291
  · exact B620295
  · exact B620299
  · exact B620303
  · exact B620307
  · exact B620311
  · exact B620315
  · exact B620319
  · exact B620323
  · exact B620327
  · exact B620331
  · exact B620335
  · exact B620339
  · exact B620343
  · exact B620347
  · exact B620351
  · exact B620355
  · exact B620359
  · exact B620363
  · exact B620367
  · exact B620371
  · exact B620375
  · exact B620379
  · exact B620383
  · exact B620387
  · exact B620391
  · exact B620395
  · exact B620399
  · exact B620403
  · exact B620407
  · exact B620411
  · exact B620415
  · exact B620419
  · exact B620423
  · exact B620427
  · exact B620431
  · exact B620435
  · exact B620439
  · exact B620443
  · exact B620447
  · exact B620451
  · exact B620455
  · exact B620459
  · exact B620463
  · exact B620467
  · exact B620471
  · exact B620475
  · exact B620479
  · exact B620483
  · exact B620487
  · exact B620491
  · exact B620495
  · exact B620499
  · exact B620503
  · exact B620507
  · exact B620511
  · exact B620515
  · exact B620519
  · exact B620523
  · exact B620527
  · exact B620531
  · exact B620535
  · exact B620539
  · exact B620543
  · exact B620547
  · exact B620551
  · exact B620555
  · exact B620559
  · exact B620563
  · exact B620567
  · exact B620571
  · exact B620575
  · exact B620579
  · exact B620583
  · exact B620587
  · exact B620591
  · exact B620595
  · exact B620599
  · exact B620603
  · exact B620607
  · exact B620611
  · exact B620615
  · exact B620619
  · exact B620623
  · exact B620627
  · exact B620631
  · exact B620635
  · exact B620639
  · exact B620643
  · exact B620647
  · exact B620651
  · exact B620655
  · exact B620659
  · exact B620663
  · exact B620667
  · exact B620671
  · exact B620675
  · exact B620679
  · exact B620683
  · exact B620687
  · exact B620691
  · exact B620695
  · exact B620699
  · exact B620703
  · exact B620707
  · exact B620711
  · exact B620715
  · exact B620719
  · exact B620723
  · exact B620727
  · exact B620731
  · exact B620735
  · exact B620739
  · exact B620743
  · exact B620747
  · exact B620751
  · exact B620755
  · exact B620759
  · exact B620763
  · exact B620767
  · exact B620771
  · exact B620775
  · exact B620779
  · exact B620783
  · exact B620787
  · exact B620791
  · exact B620795
  · exact B620799
  · exact B620803
  · exact B620807
  · exact B620811
  · exact B620815
  · exact B620819
  · exact B620823
  · exact B620827
  · exact B620831
  · exact B620835
  · exact B620839
  · exact B620843
  · exact B620847
  · exact B620851
  · exact B620855
  · exact B620859
  · exact B620863
  · exact B620867
  · exact B620871
  · exact B620875
  · exact B620879
  · exact B620883
  · exact B620887
  · exact B620891
  · exact B620895
  · exact B620899
  · exact B620903
  · exact B620907
  · exact B620911
  · exact B620915
  · exact B620919
  · exact B620923
  · exact B620927
  · exact B620931
  · exact B620935
  · exact B620939
  · exact B620943
  · exact B620947
  · exact B620951
  · exact B620955
  · exact B620959
  · exact B620963
  · exact B620967
  · exact B620971
  · exact B620975
  · exact B620979
  · exact B620983
  · exact B620987
  · exact B620991
  · exact B620995
  · exact B620999
  · exact B621003
  · exact B621007
  · exact B621011
  · exact B621015
  · exact B621019
  · exact B621023
  · exact B621027
  · exact B621031
  · exact B621035
  · exact B621039
  · exact B621043
  · exact B621047
  · exact B621051
  · exact B621055
  · exact B621059
  · exact B621063
  · exact B621067
  · exact B621071
  · exact B621075
  · exact B621079
  · exact B621083
  · exact B621087
  · exact B621091
  · exact B621095

theorem C1 (j : ℕ) (h1 : 155274 ≤ j) (h2 : j ≤ 155573) : Blo 618297 (4 * j + 3) := by
  interval_cases j
  · exact B621099
  · exact B621103
  · exact B621107
  · exact B621111
  · exact B621115
  · exact B621119
  · exact B621123
  · exact B621127
  · exact B621131
  · exact B621135
  · exact B621139
  · exact B621143
  · exact B621147
  · exact B621151
  · exact B621155
  · exact B621159
  · exact B621163
  · exact B621167
  · exact B621171
  · exact B621175
  · exact B621179
  · exact B621183
  · exact B621187
  · exact B621191
  · exact B621195
  · exact B621199
  · exact B621203
  · exact B621207
  · exact B621211
  · exact B621215
  · exact B621219
  · exact B621223
  · exact B621227
  · exact B621231
  · exact B621235
  · exact B621239
  · exact B621243
  · exact B621247
  · exact B621251
  · exact B621255
  · exact B621259
  · exact B621263
  · exact B621267
  · exact B621271
  · exact B621275
  · exact B621279
  · exact B621283
  · exact B621287
  · exact B621291
  · exact B621295
  · exact B621299
  · exact B621303
  · exact B621307
  · exact B621311
  · exact B621315
  · exact B621319
  · exact B621323
  · exact B621327
  · exact B621331
  · exact B621335
  · exact B621339
  · exact B621343
  · exact B621347
  · exact B621351
  · exact B621355
  · exact B621359
  · exact B621363
  · exact B621367
  · exact B621371
  · exact B621375
  · exact B621379
  · exact B621383
  · exact B621387
  · exact B621391
  · exact B621395
  · exact B621399
  · exact B621403
  · exact B621407
  · exact B621411
  · exact B621415
  · exact B621419
  · exact B621423
  · exact B621427
  · exact B621431
  · exact B621435
  · exact B621439
  · exact B621443
  · exact B621447
  · exact B621451
  · exact B621455
  · exact B621459
  · exact B621463
  · exact B621467
  · exact B621471
  · exact B621475
  · exact B621479
  · exact B621483
  · exact B621487
  · exact B621491
  · exact B621495
  · exact B621499
  · exact B621503
  · exact B621507
  · exact B621511
  · exact B621515
  · exact B621519
  · exact B621523
  · exact B621527
  · exact B621531
  · exact B621535
  · exact B621539
  · exact B621543
  · exact B621547
  · exact B621551
  · exact B621555
  · exact B621559
  · exact B621563
  · exact B621567
  · exact B621571
  · exact B621575
  · exact B621579
  · exact B621583
  · exact B621587
  · exact B621591
  · exact B621595
  · exact B621599
  · exact B621603
  · exact B621607
  · exact B621611
  · exact B621615
  · exact B621619
  · exact B621623
  · exact B621627
  · exact B621631
  · exact B621635
  · exact B621639
  · exact B621643
  · exact B621647
  · exact B621651
  · exact B621655
  · exact B621659
  · exact B621663
  · exact B621667
  · exact B621671
  · exact B621675
  · exact B621679
  · exact B621683
  · exact B621687
  · exact B621691
  · exact B621695
  · exact B621699
  · exact B621703
  · exact B621707
  · exact B621711
  · exact B621715
  · exact B621719
  · exact B621723
  · exact B621727
  · exact B621731
  · exact B621735
  · exact B621739
  · exact B621743
  · exact B621747
  · exact B621751
  · exact B621755
  · exact B621759
  · exact B621763
  · exact B621767
  · exact B621771
  · exact B621775
  · exact B621779
  · exact B621783
  · exact B621787
  · exact B621791
  · exact B621795
  · exact B621799
  · exact B621803
  · exact B621807
  · exact B621811
  · exact B621815
  · exact B621819
  · exact B621823
  · exact B621827
  · exact B621831
  · exact B621835
  · exact B621839
  · exact B621843
  · exact B621847
  · exact B621851
  · exact B621855
  · exact B621859
  · exact B621863
  · exact B621867
  · exact B621871
  · exact B621875
  · exact B621879
  · exact B621883
  · exact B621887
  · exact B621891
  · exact B621895
  · exact B621899
  · exact B621903
  · exact B621907
  · exact B621911
  · exact B621915
  · exact B621919
  · exact B621923
  · exact B621927
  · exact B621931
  · exact B621935
  · exact B621939
  · exact B621943
  · exact B621947
  · exact B621951
  · exact B621955
  · exact B621959
  · exact B621963
  · exact B621967
  · exact B621971
  · exact B621975
  · exact B621979
  · exact B621983
  · exact B621987
  · exact B621991
  · exact B621995
  · exact B621999
  · exact B622003
  · exact B622007
  · exact B622011
  · exact B622015
  · exact B622019
  · exact B622023
  · exact B622027
  · exact B622031
  · exact B622035
  · exact B622039
  · exact B622043
  · exact B622047
  · exact B622051
  · exact B622055
  · exact B622059
  · exact B622063
  · exact B622067
  · exact B622071
  · exact B622075
  · exact B622079
  · exact B622083
  · exact B622087
  · exact B622091
  · exact B622095
  · exact B622099
  · exact B622103
  · exact B622107
  · exact B622111
  · exact B622115
  · exact B622119
  · exact B622123
  · exact B622127
  · exact B622131
  · exact B622135
  · exact B622139
  · exact B622143
  · exact B622147
  · exact B622151
  · exact B622155
  · exact B622159
  · exact B622163
  · exact B622167
  · exact B622171
  · exact B622175
  · exact B622179
  · exact B622183
  · exact B622187
  · exact B622191
  · exact B622195
  · exact B622199
  · exact B622203
  · exact B622207
  · exact B622211
  · exact B622215
  · exact B622219
  · exact B622223
  · exact B622227
  · exact B622231
  · exact B622235
  · exact B622239
  · exact B622243
  · exact B622247
  · exact B622251
  · exact B622255
  · exact B622259
  · exact B622263
  · exact B622267
  · exact B622271
  · exact B622275
  · exact B622279
  · exact B622283
  · exact B622287
  · exact B622291
  · exact B622295

theorem solution (m : ℕ) (hlo : 618297 ≤ m) (hhi : m ≤ 622297) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 154574 ≤ j := by omega
    have hj2 : j ≤ 155573 := by omega
    have hb : Blo 618297 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 155274 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
