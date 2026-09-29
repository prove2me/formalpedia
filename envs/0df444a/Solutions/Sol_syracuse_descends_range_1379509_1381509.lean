-- Prove2me | solution 1 for syracuse_descends_range_1379509_1381509
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:20.217036+00:00
-- url     : https://prove2.me/submissions/e725eba0-cd5c-4717-903c-7bc34de7189a

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


theorem B2621477 : Blo 1379509 2621477 := bbase (se 4 (by rfl) ⟨245763, by rfl⟩ : syracuseStep 2621477 = 491527) (by norm_num)
theorem B3104837 : Blo 1379509 3104837 := bbase (se 4 (by rfl) ⟨291078, by rfl⟩ : syracuseStep 3104837 = 582157) (by norm_num)
theorem B4661333 : Blo 1379509 4661333 := bbase (se 8 (by rfl) ⟨27312, by rfl⟩ : syracuseStep 4661333 = 54625) (by norm_num)
theorem B3317885 : Blo 1379509 3317885 := bbase (se 3 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 3317885 = 1244207) (by norm_num)
theorem B3104909 : Blo 1379509 3104909 := bbase (se 3 (by rfl) ⟨582170, by rfl⟩ : syracuseStep 3104909 = 1164341) (by norm_num)
theorem B2621621 : Blo 1379509 2621621 := bbase (se 5 (by rfl) ⟨122888, by rfl⟩ : syracuseStep 2621621 = 245777) (by norm_num)
theorem B3104981 : Blo 1379509 3104981 := bbase (se 7 (by rfl) ⟨36386, by rfl⟩ : syracuseStep 3104981 = 72773) (by norm_num)
theorem B4423909 : Blo 1379509 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B3105053 : Blo 1379509 3105053 := bbase (se 3 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 3105053 = 1164395) (by norm_num)
theorem B1417537 : Blo 1379509 1417537 := bbase (se 2 (by rfl) ⟨531576, by rfl⟩ : syracuseStep 1417537 = 1063153) (by norm_num)
theorem B3105125 : Blo 1379509 3105125 := bbase (se 4 (by rfl) ⟨291105, by rfl⟩ : syracuseStep 3105125 = 582211) (by norm_num)
theorem B1474957 : Blo 1379509 1474957 := bbase (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) (by norm_num)
theorem B3105197 : Blo 1379509 3105197 := bbase (se 3 (by rfl) ⟨582224, by rfl⟩ : syracuseStep 3105197 = 1164449) (by norm_num)
theorem B2097605 : Blo 1379509 2097605 := bbase (se 4 (by rfl) ⟨196650, by rfl⟩ : syracuseStep 2097605 = 393301) (by norm_num)
theorem B3318221 : Blo 1379509 3318221 := bbase (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) (by norm_num)
theorem B1769941 : Blo 1379509 1769941 := bbase (se 7 (by rfl) ⟨20741, by rfl⟩ : syracuseStep 1769941 = 41483) (by norm_num)
theorem B2621909 : Blo 1379509 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B1475029 : Blo 1379509 1475029 := bbase (se 7 (by rfl) ⟨17285, by rfl⟩ : syracuseStep 1475029 = 34571) (by norm_num)
theorem B5595637 : Blo 1379509 5595637 := bbase (se 5 (by rfl) ⟨262295, by rfl⟩ : syracuseStep 5595637 = 524591) (by norm_num)
theorem B3105269 : Blo 1379509 3105269 := bbase (se 5 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 3105269 = 291119) (by norm_num)
theorem B4661765 : Blo 1379509 4661765 := bbase (se 4 (by rfl) ⟨437040, by rfl⟩ : syracuseStep 4661765 = 874081) (by norm_num)
theorem B3318317 : Blo 1379509 3318317 := bbase (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) (by norm_num)
theorem B1966637 : Blo 1379509 1966637 := bbase (se 3 (by rfl) ⟨368744, by rfl⟩ : syracuseStep 1966637 = 737489) (by norm_num)
theorem B3105341 : Blo 1379509 3105341 := bbase (se 3 (by rfl) ⟨582251, by rfl⟩ : syracuseStep 3105341 = 1164503) (by norm_num)
theorem B2949709 : Blo 1379509 2949709 := bbase (se 3 (by rfl) ⟨553070, by rfl⟩ : syracuseStep 2949709 = 1106141) (by norm_num)
theorem B2622061 : Blo 1379509 2622061 := bbase (se 3 (by rfl) ⟨491636, by rfl⟩ : syracuseStep 2622061 = 983273) (by norm_num)
theorem B1966717 : Blo 1379509 1966717 := bbase (se 3 (by rfl) ⟨368759, by rfl⟩ : syracuseStep 1966717 = 737519) (by norm_num)
theorem B3105413 : Blo 1379509 3105413 := bbase (se 4 (by rfl) ⟨291132, by rfl⟩ : syracuseStep 3105413 = 582265) (by norm_num)
theorem B1475209 : Blo 1379509 1475209 := bbase (se 2 (by rfl) ⟨553203, by rfl⟩ : syracuseStep 1475209 = 1106407) (by norm_num)
theorem B10486421 : Blo 1379509 10486421 := bbase (se 6 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 10486421 = 491551) (by norm_num)
theorem B3105485 : Blo 1379509 3105485 := bbase (se 3 (by rfl) ⟨582278, by rfl⟩ : syracuseStep 3105485 = 1164557) (by norm_num)
theorem B7865045 : Blo 1379509 7865045 := bbase (se 7 (by rfl) ⟨92168, by rfl⟩ : syracuseStep 7865045 = 184337) (by norm_num)
theorem B2949853 : Blo 1379509 2949853 := bbase (se 3 (by rfl) ⟨553097, by rfl⟩ : syracuseStep 2949853 = 1106195) (by norm_num)
theorem B6988517 : Blo 1379509 6988517 := bbase (se 4 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 6988517 = 1310347) (by norm_num)
theorem B3318509 : Blo 1379509 3318509 := bbase (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) (by norm_num)
theorem B1966837 : Blo 1379509 1966837 := bbase (se 5 (by rfl) ⟨92195, by rfl⟩ : syracuseStep 1966837 = 184391) (by norm_num)
theorem B3539717 : Blo 1379509 3539717 := bbase (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) (by norm_num)
theorem B1573645 : Blo 1379509 1573645 := bbase (se 3 (by rfl) ⟨295058, by rfl⟩ : syracuseStep 1573645 = 590117) (by norm_num)
theorem B3105557 : Blo 1379509 3105557 := bbase (se 6 (by rfl) ⟨72786, by rfl⟩ : syracuseStep 3105557 = 145573) (by norm_num)
theorem B1966933 : Blo 1379509 1966933 := bbase (se 9 (by rfl) ⟨5762, by rfl⟩ : syracuseStep 1966933 = 11525) (by norm_num)
theorem B3105629 : Blo 1379509 3105629 := bbase (se 3 (by rfl) ⟨582305, by rfl⟩ : syracuseStep 3105629 = 1164611) (by norm_num)
theorem B2622365 : Blo 1379509 2622365 := bbase (se 3 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 2622365 = 983387) (by norm_num)
theorem B3105701 : Blo 1379509 3105701 := bbase (se 4 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 3105701 = 582319) (by norm_num)
theorem B4662197 : Blo 1379509 4662197 := bbase (se 5 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 4662197 = 437081) (by norm_num)
theorem B3105773 : Blo 1379509 3105773 := bbase (se 3 (by rfl) ⟨582332, by rfl⟩ : syracuseStep 3105773 = 1164665) (by norm_num)
theorem B2212877 : Blo 1379509 2212877 := bbase (se 3 (by rfl) ⟨414914, by rfl⟩ : syracuseStep 2212877 = 829829) (by norm_num)
theorem B26240021 : Blo 1379509 26240021 := bbase (se 6 (by rfl) ⟨615000, by rfl⟩ : syracuseStep 26240021 = 1230001) (by norm_num)
theorem B1745965 : Blo 1379509 1745965 := bbase (se 3 (by rfl) ⟨327368, by rfl⟩ : syracuseStep 1745965 = 654737) (by norm_num)
theorem B10478645 : Blo 1379509 10478645 := bbase (se 5 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 10478645 = 982373) (by norm_num)
theorem B3105845 : Blo 1379509 3105845 := bbase (se 5 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 3105845 = 291173) (by norm_num)
theorem B11658325 : Blo 1379509 11658325 := bbase (se 8 (by rfl) ⟨68310, by rfl⟩ : syracuseStep 11658325 = 136621) (by norm_num)
theorem B2950229 : Blo 1379509 2950229 := bbase (se 8 (by rfl) ⟨17286, by rfl⟩ : syracuseStep 2950229 = 34573) (by norm_num)
theorem B3105917 : Blo 1379509 3105917 := bbase (se 3 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 3105917 = 1164719) (by norm_num)
theorem B3105989 : Blo 1379509 3105989 := bbase (se 4 (by rfl) ⟨291186, by rfl⟩ : syracuseStep 3105989 = 582373) (by norm_num)
theorem B1746137 : Blo 1379509 1746137 := bbase (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) (by norm_num)
theorem B3106061 : Blo 1379509 3106061 := bbase (se 3 (by rfl) ⟨582386, by rfl⟩ : syracuseStep 3106061 = 1164773) (by norm_num)
theorem B1746193 : Blo 1379509 1746193 := bbase (se 2 (by rfl) ⟨654822, by rfl⟩ : syracuseStep 1746193 = 1309645) (by norm_num)
theorem B3106133 : Blo 1379509 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B1680733 : Blo 1379509 1680733 := bbase (se 3 (by rfl) ⟨315137, by rfl⟩ : syracuseStep 1680733 = 630275) (by norm_num)
theorem B1746289 : Blo 1379509 1746289 := bbase (se 2 (by rfl) ⟨654858, by rfl⟩ : syracuseStep 1746289 = 1309717) (by norm_num)
theorem B2327933 : Blo 1379509 2327933 := bbase (se 3 (by rfl) ⟨436487, by rfl⟩ : syracuseStep 2327933 = 872975) (by norm_num)
theorem B1992061 : Blo 1379509 1992061 := bbase (se 3 (by rfl) ⟨373511, by rfl⟩ : syracuseStep 1992061 = 747023) (by norm_num)
theorem B3106205 : Blo 1379509 3106205 := bbase (se 3 (by rfl) ⟨582413, by rfl⟩ : syracuseStep 3106205 = 1164827) (by norm_num)
theorem B7185829 : Blo 1379509 7185829 := bbase (se 4 (by rfl) ⟨673671, by rfl⟩ : syracuseStep 7185829 = 1347343) (by norm_num)
theorem B1574321 : Blo 1379509 1574321 := bbase (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) (by norm_num)
theorem B3106277 : Blo 1379509 3106277 := bbase (se 4 (by rfl) ⟨291213, by rfl⟩ : syracuseStep 3106277 = 582427) (by norm_num)
theorem B2328061 : Blo 1379509 2328061 := bbase (se 3 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 2328061 = 873023) (by norm_num)
theorem B1746461 : Blo 1379509 1746461 := bbase (se 3 (by rfl) ⟨327461, by rfl⟩ : syracuseStep 1746461 = 654923) (by norm_num)
theorem B3106349 : Blo 1379509 3106349 := bbase (se 3 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 3106349 = 1164881) (by norm_num)
theorem B1795649 : Blo 1379509 1795649 := bbase (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) (by norm_num)
theorem B2328149 : Blo 1379509 2328149 := bbase (se 8 (by rfl) ⟨13641, by rfl⟩ : syracuseStep 2328149 = 27283) (by norm_num)
theorem B1746517 : Blo 1379509 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B3106421 : Blo 1379509 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B5244533 : Blo 1379509 5244533 := bbase (se 5 (by rfl) ⟨245837, by rfl⟩ : syracuseStep 5244533 = 491675) (by norm_num)
theorem B3147437 : Blo 1379509 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B1746613 : Blo 1379509 1746613 := bbase (se 5 (by rfl) ⟨81872, by rfl⟩ : syracuseStep 1746613 = 163745) (by norm_num)
theorem B3106493 : Blo 1379509 3106493 := bbase (se 3 (by rfl) ⟨582467, by rfl⟩ : syracuseStep 3106493 = 1164935) (by norm_num)
theorem B2328277 : Blo 1379509 2328277 := bbase (se 7 (by rfl) ⟨27284, by rfl⟩ : syracuseStep 2328277 = 54569) (by norm_num)
theorem B3106565 : Blo 1379509 3106565 := bbase (se 4 (by rfl) ⟨291240, by rfl⟩ : syracuseStep 3106565 = 582481) (by norm_num)
theorem B2361125 : Blo 1379509 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B2328365 : Blo 1379509 2328365 := bbase (se 3 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 2328365 = 873137) (by norm_num)
theorem B3106637 : Blo 1379509 3106637 := bbase (se 3 (by rfl) ⟨582494, by rfl⟩ : syracuseStep 3106637 = 1164989) (by norm_num)
theorem B1746785 : Blo 1379509 1746785 := bbase (se 2 (by rfl) ⟨655044, by rfl⟩ : syracuseStep 1746785 = 1310089) (by norm_num)
theorem B3106709 : Blo 1379509 3106709 := bbase (se 6 (by rfl) ⟨72813, by rfl⟩ : syracuseStep 3106709 = 145627) (by norm_num)
theorem B5244821 : Blo 1379509 5244821 := bbase (se 6 (by rfl) ⟨122925, by rfl⟩ : syracuseStep 5244821 = 245851) (by norm_num)
theorem B1746841 : Blo 1379509 1746841 := bbase (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) (by norm_num)
theorem B1574813 : Blo 1379509 1574813 := bbase (se 3 (by rfl) ⟨295277, by rfl⟩ : syracuseStep 1574813 = 590555) (by norm_num)
theorem B6637477 : Blo 1379509 6637477 := bbase (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) (by norm_num)
theorem B2328493 : Blo 1379509 2328493 := bbase (se 3 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 2328493 = 873185) (by norm_num)
theorem B3106781 : Blo 1379509 3106781 := bbase (se 3 (by rfl) ⟨582521, by rfl⟩ : syracuseStep 3106781 = 1165043) (by norm_num)
theorem B6989813 : Blo 1379509 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B1746937 : Blo 1379509 1746937 := bbase (se 2 (by rfl) ⟨655101, by rfl⟩ : syracuseStep 1746937 = 1310203) (by norm_num)
theorem B2328581 : Blo 1379509 2328581 := bbase (se 4 (by rfl) ⟨218304, by rfl⟩ : syracuseStep 2328581 = 436609) (by norm_num)
theorem B13273109 : Blo 1379509 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B3106853 : Blo 1379509 3106853 := bbase (se 4 (by rfl) ⟨291267, by rfl⟩ : syracuseStep 3106853 = 582535) (by norm_num)
theorem B6383717 : Blo 1379509 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B3106925 : Blo 1379509 3106925 := bbase (se 3 (by rfl) ⟨582548, by rfl⟩ : syracuseStep 3106925 = 1165097) (by norm_num)
theorem B12585077 : Blo 1379509 12585077 := bbase (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) (by norm_num)
theorem B2328709 : Blo 1379509 2328709 := bbase (se 4 (by rfl) ⟨218316, by rfl⟩ : syracuseStep 2328709 = 436633) (by norm_num)
theorem B3491981 : Blo 1379509 3491981 := bbase (se 3 (by rfl) ⟨654746, by rfl⟩ : syracuseStep 3491981 = 1309493) (by norm_num)
theorem B1747109 : Blo 1379509 1747109 := bbase (se 4 (by rfl) ⟨163791, by rfl⟩ : syracuseStep 1747109 = 327583) (by norm_num)
theorem B3106997 : Blo 1379509 3106997 := bbase (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) (by norm_num)
theorem B23914709 : Blo 1379509 23914709 := bbase (se 7 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 23914709 = 560501) (by norm_num)
theorem B2328797 : Blo 1379509 2328797 := bbase (se 3 (by rfl) ⟨436649, by rfl⟩ : syracuseStep 2328797 = 873299) (by norm_num)
theorem B1747165 : Blo 1379509 1747165 := bbase (se 3 (by rfl) ⟨327593, by rfl⟩ : syracuseStep 1747165 = 655187) (by norm_num)
theorem B3107069 : Blo 1379509 3107069 := bbase (se 3 (by rfl) ⟨582575, by rfl⟩ : syracuseStep 3107069 = 1165151) (by norm_num)
theorem B1747261 : Blo 1379509 1747261 := bbase (se 3 (by rfl) ⟨327611, by rfl⟩ : syracuseStep 1747261 = 655223) (by norm_num)
theorem B3107141 : Blo 1379509 3107141 := bbase (se 4 (by rfl) ⟨291294, by rfl⟩ : syracuseStep 3107141 = 582589) (by norm_num)
theorem B3492173 : Blo 1379509 3492173 := bbase (se 3 (by rfl) ⟨654782, by rfl⟩ : syracuseStep 3492173 = 1309565) (by norm_num)
theorem B2656589 : Blo 1379509 2656589 := bbase (se 3 (by rfl) ⟨498110, by rfl⟩ : syracuseStep 2656589 = 996221) (by norm_num)
theorem B2328925 : Blo 1379509 2328925 := bbase (se 3 (by rfl) ⟨436673, by rfl⟩ : syracuseStep 2328925 = 873347) (by norm_num)
theorem B3107213 : Blo 1379509 3107213 := bbase (se 3 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 3107213 = 1165205) (by norm_num)
theorem B2329013 : Blo 1379509 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B3107285 : Blo 1379509 3107285 := bbase (se 7 (by rfl) ⟨36413, by rfl⟩ : syracuseStep 3107285 = 72827) (by norm_num)
theorem B1575397 : Blo 1379509 1575397 := bbase (se 4 (by rfl) ⟨147693, by rfl⟩ : syracuseStep 1575397 = 295387) (by norm_num)
theorem B1747433 : Blo 1379509 1747433 := bbase (se 2 (by rfl) ⟨655287, by rfl⟩ : syracuseStep 1747433 = 1310575) (by norm_num)
theorem B28355093 : Blo 1379509 28355093 := bbase (se 6 (by rfl) ⟨664572, by rfl⟩ : syracuseStep 28355093 = 1329145) (by norm_num)
theorem B3107357 : Blo 1379509 3107357 := bbase (se 3 (by rfl) ⟨582629, by rfl⟩ : syracuseStep 3107357 = 1165259) (by norm_num)
theorem B1747489 : Blo 1379509 1747489 := bbase (se 2 (by rfl) ⟨655308, by rfl⟩ : syracuseStep 1747489 = 1310617) (by norm_num)
theorem B4975141 : Blo 1379509 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B2329141 : Blo 1379509 2329141 := bbase (se 5 (by rfl) ⟨109178, by rfl⟩ : syracuseStep 2329141 = 218357) (by norm_num)
theorem B3107429 : Blo 1379509 3107429 := bbase (se 4 (by rfl) ⟨291321, by rfl⟩ : syracuseStep 3107429 = 582643) (by norm_num)
theorem B1747585 : Blo 1379509 1747585 := bbase (se 2 (by rfl) ⟨655344, by rfl⟩ : syracuseStep 1747585 = 1310689) (by norm_num)
theorem B2329229 : Blo 1379509 2329229 := bbase (se 3 (by rfl) ⟨436730, by rfl⟩ : syracuseStep 2329229 = 873461) (by norm_num)
theorem B3492517 : Blo 1379509 3492517 := bbase (se 4 (by rfl) ⟨327423, by rfl⟩ : syracuseStep 3492517 = 654847) (by norm_num)
theorem B3107501 : Blo 1379509 3107501 := bbase (se 3 (by rfl) ⟨582656, by rfl⟩ : syracuseStep 3107501 = 1165313) (by norm_num)
theorem B8841973 : Blo 1379509 8841973 := bbase (se 5 (by rfl) ⟨414467, by rfl⟩ : syracuseStep 8841973 = 828935) (by norm_num)
theorem B3107573 : Blo 1379509 3107573 := bbase (se 5 (by rfl) ⟨145667, by rfl⟩ : syracuseStep 3107573 = 291335) (by norm_num)
theorem B2329357 : Blo 1379509 2329357 := bbase (se 3 (by rfl) ⟨436754, by rfl⟩ : syracuseStep 2329357 = 873509) (by norm_num)
theorem B1657621 : Blo 1379509 1657621 := bbase (se 6 (by rfl) ⟨38850, by rfl⟩ : syracuseStep 1657621 = 77701) (by norm_num)
theorem B3492629 : Blo 1379509 3492629 := bbase (se 6 (by rfl) ⟨81858, by rfl⟩ : syracuseStep 3492629 = 163717) (by norm_num)
theorem B1747757 : Blo 1379509 1747757 := bbase (se 3 (by rfl) ⟨327704, by rfl⟩ : syracuseStep 1747757 = 655409) (by norm_num)
theorem B3107645 : Blo 1379509 3107645 := bbase (se 3 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 3107645 = 1165367) (by norm_num)
theorem B2329445 : Blo 1379509 2329445 := bbase (se 4 (by rfl) ⟨218385, by rfl⟩ : syracuseStep 2329445 = 436771) (by norm_num)
theorem B1747813 : Blo 1379509 1747813 := bbase (se 4 (by rfl) ⟨163857, by rfl⟩ : syracuseStep 1747813 = 327715) (by norm_num)
theorem B3107717 : Blo 1379509 3107717 := bbase (se 4 (by rfl) ⟨291348, by rfl⟩ : syracuseStep 3107717 = 582697) (by norm_num)
theorem B5041061 : Blo 1379509 5041061 := bbase (se 4 (by rfl) ⟨472599, by rfl⟩ : syracuseStep 5041061 = 945199) (by norm_num)
theorem B1747909 : Blo 1379509 1747909 := bbase (se 4 (by rfl) ⟨163866, by rfl⟩ : syracuseStep 1747909 = 327733) (by norm_num)
theorem B3107789 : Blo 1379509 3107789 := bbase (se 3 (by rfl) ⟨582710, by rfl⟩ : syracuseStep 3107789 = 1165421) (by norm_num)
theorem B3492821 : Blo 1379509 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B1657813 : Blo 1379509 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B2329573 : Blo 1379509 2329573 := bbase (se 4 (by rfl) ⟨218397, by rfl⟩ : syracuseStep 2329573 = 436795) (by norm_num)
theorem B4656149 : Blo 1379509 4656149 := bbase (se 6 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 4656149 = 218257) (by norm_num)
theorem B3107861 : Blo 1379509 3107861 := bbase (se 6 (by rfl) ⟨72840, by rfl⟩ : syracuseStep 3107861 = 145681) (by norm_num)
theorem B7965749 : Blo 1379509 7965749 := bbase (se 5 (by rfl) ⟨373394, by rfl⟩ : syracuseStep 7965749 = 746789) (by norm_num)
theorem B2329661 : Blo 1379509 2329661 := bbase (se 3 (by rfl) ⟨436811, by rfl⟩ : syracuseStep 2329661 = 873623) (by norm_num)
theorem B3107933 : Blo 1379509 3107933 := bbase (se 3 (by rfl) ⟨582737, by rfl⟩ : syracuseStep 3107933 = 1165475) (by norm_num)
theorem B1657957 : Blo 1379509 1657957 := bbase (se 4 (by rfl) ⟨155433, by rfl⟩ : syracuseStep 1657957 = 310867) (by norm_num)
theorem B1748081 : Blo 1379509 1748081 := bbase (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) (by norm_num)
theorem B3108005 : Blo 1379509 3108005 := bbase (se 4 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 3108005 = 582751) (by norm_num)
theorem B1748137 : Blo 1379509 1748137 := bbase (se 2 (by rfl) ⟨655551, by rfl⟩ : syracuseStep 1748137 = 1311103) (by norm_num)
theorem B2329789 : Blo 1379509 2329789 := bbase (se 3 (by rfl) ⟨436835, by rfl⟩ : syracuseStep 2329789 = 873671) (by norm_num)
theorem B3108077 : Blo 1379509 3108077 := bbase (se 3 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 3108077 = 1165529) (by norm_num)
theorem B6991109 : Blo 1379509 6991109 := bbase (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) (by norm_num)
theorem B1748233 : Blo 1379509 1748233 := bbase (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) (by norm_num)
theorem B2100493 : Blo 1379509 2100493 := bbase (se 3 (by rfl) ⟨393842, by rfl⟩ : syracuseStep 2100493 = 787685) (by norm_num)
theorem B4197653 : Blo 1379509 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B2329877 : Blo 1379509 2329877 := bbase (se 6 (by rfl) ⟨54606, by rfl⟩ : syracuseStep 2329877 = 109213) (by norm_num)
theorem B3493165 : Blo 1379509 3493165 := bbase (se 3 (by rfl) ⟨654968, by rfl⟩ : syracuseStep 3493165 = 1309937) (by norm_num)
theorem B3108149 : Blo 1379509 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B3108221 : Blo 1379509 3108221 := bbase (se 3 (by rfl) ⟨582791, by rfl⟩ : syracuseStep 3108221 = 1165583) (by norm_num)
theorem B3149189 : Blo 1379509 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B2330005 : Blo 1379509 2330005 := bbase (se 6 (by rfl) ⟨54609, by rfl⟩ : syracuseStep 2330005 = 109219) (by norm_num)
theorem B3493277 : Blo 1379509 3493277 := bbase (se 3 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 3493277 = 1309979) (by norm_num)
theorem B1748405 : Blo 1379509 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B4656581 : Blo 1379509 4656581 := bbase (se 4 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 4656581 = 873109) (by norm_num)
theorem B3108293 : Blo 1379509 3108293 := bbase (se 4 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 3108293 = 582805) (by norm_num)
theorem B5238229 : Blo 1379509 5238229 := bbase (se 7 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 5238229 = 122771) (by norm_num)
theorem B2330093 : Blo 1379509 2330093 := bbase (se 3 (by rfl) ⟨436892, by rfl⟩ : syracuseStep 2330093 = 873785) (by norm_num)
theorem B1748461 : Blo 1379509 1748461 := bbase (se 3 (by rfl) ⟨327836, by rfl⟩ : syracuseStep 1748461 = 655673) (by norm_num)
theorem B3108365 : Blo 1379509 3108365 := bbase (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) (by norm_num)
theorem B3493469 : Blo 1379509 3493469 := bbase (se 3 (by rfl) ⟨655025, by rfl⟩ : syracuseStep 3493469 = 1310051) (by norm_num)
theorem B1551973 : Blo 1379509 1551973 := bbase (se 4 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 1551973 = 290995) (by norm_num)
theorem B2330221 : Blo 1379509 2330221 := bbase (se 3 (by rfl) ⟨436916, by rfl⟩ : syracuseStep 2330221 = 873833) (by norm_num)
theorem B1552009 : Blo 1379509 1552009 := bbase (se 2 (by rfl) ⟨582003, by rfl⟩ : syracuseStep 1552009 = 1164007) (by norm_num)
theorem B1552045 : Blo 1379509 1552045 := bbase (se 3 (by rfl) ⟨291008, by rfl⟩ : syracuseStep 1552045 = 582017) (by norm_num)
theorem B5893829 : Blo 1379509 5893829 := bbase (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) (by norm_num)
theorem B2330309 : Blo 1379509 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B1552081 : Blo 1379509 1552081 := bbase (se 2 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 1552081 = 1164061) (by norm_num)
theorem B19910357 : Blo 1379509 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B1552117 : Blo 1379509 1552117 := bbase (se 5 (by rfl) ⟨72755, by rfl⟩ : syracuseStep 1552117 = 145511) (by norm_num)
theorem B5238533 : Blo 1379509 5238533 := bbase (se 4 (by rfl) ⟨491112, by rfl⟩ : syracuseStep 5238533 = 982225) (by norm_num)
theorem B2838277 : Blo 1379509 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B1552153 : Blo 1379509 1552153 := bbase (se 2 (by rfl) ⟨582057, by rfl⟩ : syracuseStep 1552153 = 1164115) (by norm_num)
theorem B3731237 : Blo 1379509 3731237 := bbase (se 4 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 3731237 = 699607) (by norm_num)
theorem B1552189 : Blo 1379509 1552189 := bbase (se 3 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 1552189 = 582071) (by norm_num)
theorem B2330437 : Blo 1379509 2330437 := bbase (se 4 (by rfl) ⟨218478, by rfl⟩ : syracuseStep 2330437 = 436957) (by norm_num)
theorem B1552225 : Blo 1379509 1552225 := bbase (se 2 (by rfl) ⟨582084, by rfl⟩ : syracuseStep 1552225 = 1164169) (by norm_num)
theorem B4657013 : Blo 1379509 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B1552261 : Blo 1379509 1552261 := bbase (se 4 (by rfl) ⟨145524, by rfl⟩ : syracuseStep 1552261 = 291049) (by norm_num)
theorem B2330525 : Blo 1379509 2330525 := bbase (se 3 (by rfl) ⟨436973, by rfl⟩ : syracuseStep 2330525 = 873947) (by norm_num)
theorem B1552297 : Blo 1379509 1552297 := bbase (se 2 (by rfl) ⟨582111, by rfl⟩ : syracuseStep 1552297 = 1164223) (by norm_num)
theorem B3493813 : Blo 1379509 3493813 := bbase (se 5 (by rfl) ⟨163772, by rfl⟩ : syracuseStep 3493813 = 327545) (by norm_num)
theorem B1552333 : Blo 1379509 1552333 := bbase (se 3 (by rfl) ⟨291062, by rfl⟩ : syracuseStep 1552333 = 582125) (by norm_num)
theorem B1552369 : Blo 1379509 1552369 := bbase (se 2 (by rfl) ⟨582138, by rfl⟩ : syracuseStep 1552369 = 1164277) (by norm_num)
theorem B1552405 : Blo 1379509 1552405 := bbase (se 6 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 1552405 = 72769) (by norm_num)
theorem B2330653 : Blo 1379509 2330653 := bbase (se 3 (by rfl) ⟨436997, by rfl⟩ : syracuseStep 2330653 = 873995) (by norm_num)
theorem B6295589 : Blo 1379509 6295589 := bbase (se 4 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 6295589 = 1180423) (by norm_num)
theorem B3493925 : Blo 1379509 3493925 := bbase (se 4 (by rfl) ⟨327555, by rfl⟩ : syracuseStep 3493925 = 655111) (by norm_num)
theorem B1552441 : Blo 1379509 1552441 := bbase (se 2 (by rfl) ⟨582165, by rfl⟩ : syracuseStep 1552441 = 1164331) (by norm_num)
theorem B1552477 : Blo 1379509 1552477 := bbase (se 3 (by rfl) ⟨291089, by rfl⟩ : syracuseStep 1552477 = 582179) (by norm_num)
theorem B3149917 : Blo 1379509 3149917 := bbase (se 3 (by rfl) ⟨590609, by rfl⟩ : syracuseStep 3149917 = 1181219) (by norm_num)
theorem B2330741 : Blo 1379509 2330741 := bbase (se 5 (by rfl) ⟨109253, by rfl⟩ : syracuseStep 2330741 = 218507) (by norm_num)
theorem B1552513 : Blo 1379509 1552513 := bbase (se 2 (by rfl) ⟨582192, by rfl⟩ : syracuseStep 1552513 = 1164385) (by norm_num)
theorem B1552549 : Blo 1379509 1552549 := bbase (se 4 (by rfl) ⟨145551, by rfl⟩ : syracuseStep 1552549 = 291103) (by norm_num)
theorem B1552585 : Blo 1379509 1552585 := bbase (se 2 (by rfl) ⟨582219, by rfl⟩ : syracuseStep 1552585 = 1164439) (by norm_num)
theorem B3494117 : Blo 1379509 3494117 := bbase (se 4 (by rfl) ⟨327573, by rfl⟩ : syracuseStep 3494117 = 655147) (by norm_num)
theorem B1552621 : Blo 1379509 1552621 := bbase (se 3 (by rfl) ⟨291116, by rfl⟩ : syracuseStep 1552621 = 582233) (by norm_num)
theorem B2330869 : Blo 1379509 2330869 := bbase (se 5 (by rfl) ⟨109259, by rfl⟩ : syracuseStep 2330869 = 218519) (by norm_num)
theorem B1552657 : Blo 1379509 1552657 := bbase (se 2 (by rfl) ⟨582246, by rfl⟩ : syracuseStep 1552657 = 1164493) (by norm_num)
theorem B4657445 : Blo 1379509 4657445 := bbase (se 4 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 4657445 = 873271) (by norm_num)
theorem B1552693 : Blo 1379509 1552693 := bbase (se 5 (by rfl) ⟨72782, by rfl⟩ : syracuseStep 1552693 = 145565) (by norm_num)
theorem B2330957 : Blo 1379509 2330957 := bbase (se 3 (by rfl) ⟨437054, by rfl⟩ : syracuseStep 2330957 = 874109) (by norm_num)
theorem B1552729 : Blo 1379509 1552729 := bbase (se 2 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 1552729 = 1164547) (by norm_num)
theorem B1552765 : Blo 1379509 1552765 := bbase (se 3 (by rfl) ⟨291143, by rfl⟩ : syracuseStep 1552765 = 582287) (by norm_num)
theorem B1552801 : Blo 1379509 1552801 := bbase (se 2 (by rfl) ⟨582300, by rfl⟩ : syracuseStep 1552801 = 1164601) (by norm_num)
theorem B11342261 : Blo 1379509 11342261 := bbase (se 5 (by rfl) ⟨531668, by rfl⟩ : syracuseStep 11342261 = 1063337) (by norm_num)
theorem B1438133 : Blo 1379509 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B1552837 : Blo 1379509 1552837 := bbase (se 4 (by rfl) ⟨145578, by rfl⟩ : syracuseStep 1552837 = 291157) (by norm_num)
theorem B2331085 : Blo 1379509 2331085 := bbase (se 3 (by rfl) ⟨437078, by rfl⟩ : syracuseStep 2331085 = 874157) (by norm_num)
theorem B3781093 : Blo 1379509 3781093 := bbase (se 4 (by rfl) ⟨354477, by rfl⟩ : syracuseStep 3781093 = 708955) (by norm_num)
theorem B1552873 : Blo 1379509 1552873 := bbase (se 2 (by rfl) ⟨582327, by rfl⟩ : syracuseStep 1552873 = 1164655) (by norm_num)
theorem B1552909 : Blo 1379509 1552909 := bbase (se 3 (by rfl) ⟨291170, by rfl⟩ : syracuseStep 1552909 = 582341) (by norm_num)
theorem B6992405 : Blo 1379509 6992405 := bbase (se 6 (by rfl) ⟨163884, by rfl⟩ : syracuseStep 6992405 = 327769) (by norm_num)
theorem B2486821 : Blo 1379509 2486821 := bbase (se 4 (by rfl) ⟨233139, by rfl⟩ : syracuseStep 2486821 = 466279) (by norm_num)
theorem B2331173 : Blo 1379509 2331173 := bbase (se 4 (by rfl) ⟨218547, by rfl⟩ : syracuseStep 2331173 = 437095) (by norm_num)
theorem B1552945 : Blo 1379509 1552945 := bbase (se 2 (by rfl) ⟨582354, by rfl⟩ : syracuseStep 1552945 = 1164709) (by norm_num)
theorem B3494461 : Blo 1379509 3494461 := bbase (se 3 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 3494461 = 1310423) (by norm_num)
theorem B7967317 : Blo 1379509 7967317 := bbase (se 8 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 7967317 = 93367) (by norm_num)
theorem B1552981 : Blo 1379509 1552981 := bbase (se 8 (by rfl) ⟨9099, by rfl⟩ : syracuseStep 1552981 = 18199) (by norm_num)
theorem B1659485 : Blo 1379509 1659485 := bbase (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) (by norm_num)
theorem B1553017 : Blo 1379509 1553017 := bbase (se 2 (by rfl) ⟨582381, by rfl⟩ : syracuseStep 1553017 = 1164763) (by norm_num)
theorem B4977301 : Blo 1379509 4977301 := bbase (se 6 (by rfl) ⟨116655, by rfl⟩ : syracuseStep 4977301 = 233311) (by norm_num)
theorem B3027613 : Blo 1379509 3027613 := bbase (se 3 (by rfl) ⟨567677, by rfl⟩ : syracuseStep 3027613 = 1135355) (by norm_num)
theorem B1553053 : Blo 1379509 1553053 := bbase (se 3 (by rfl) ⟨291197, by rfl⟩ : syracuseStep 1553053 = 582395) (by norm_num)
theorem B3494573 : Blo 1379509 3494573 := bbase (se 3 (by rfl) ⟨655232, by rfl⟩ : syracuseStep 3494573 = 1310465) (by norm_num)
theorem B1553089 : Blo 1379509 1553089 := bbase (se 2 (by rfl) ⟨582408, by rfl⟩ : syracuseStep 1553089 = 1164817) (by norm_num)
theorem B4657877 : Blo 1379509 4657877 := bbase (se 7 (by rfl) ⟨54584, by rfl⟩ : syracuseStep 4657877 = 109169) (by norm_num)
theorem B1553125 : Blo 1379509 1553125 := bbase (se 4 (by rfl) ⟨145605, by rfl⟩ : syracuseStep 1553125 = 291211) (by norm_num)
theorem B2487029 : Blo 1379509 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B2487037 : Blo 1379509 2487037 := bbase (se 3 (by rfl) ⟨466319, by rfl⟩ : syracuseStep 2487037 = 932639) (by norm_num)
theorem B1553161 : Blo 1379509 1553161 := bbase (se 2 (by rfl) ⟨582435, by rfl⟩ : syracuseStep 1553161 = 1164871) (by norm_num)
theorem B3150613 : Blo 1379509 3150613 := bbase (se 6 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 3150613 = 147685) (by norm_num)
theorem B2069285 : Blo 1379509 2069285 := bbase (se 4 (by rfl) ⟨193995, by rfl⟩ : syracuseStep 2069285 = 387991) (by norm_num)
theorem B1553197 : Blo 1379509 1553197 := bbase (se 3 (by rfl) ⟨291224, by rfl⟩ : syracuseStep 1553197 = 582449) (by norm_num)
theorem B2069309 : Blo 1379509 2069309 := bbase (se 3 (by rfl) ⟨387995, by rfl⟩ : syracuseStep 2069309 = 775991) (by norm_num)
theorem B1553233 : Blo 1379509 1553233 := bbase (se 2 (by rfl) ⟨582462, by rfl⟩ : syracuseStep 1553233 = 1164925) (by norm_num)
theorem B2069333 : Blo 1379509 2069333 := bbase (se 9 (by rfl) ⟨6062, by rfl⟩ : syracuseStep 2069333 = 12125) (by norm_num)
theorem B2069357 : Blo 1379509 2069357 := bbase (se 3 (by rfl) ⟨388004, by rfl⟩ : syracuseStep 2069357 = 776009) (by norm_num)
theorem B3494765 : Blo 1379509 3494765 := bbase (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) (by norm_num)
theorem B8967029 : Blo 1379509 8967029 := bbase (se 5 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 8967029 = 840659) (by norm_num)
theorem B1553269 : Blo 1379509 1553269 := bbase (se 5 (by rfl) ⟨72809, by rfl⟩ : syracuseStep 1553269 = 145619) (by norm_num)
theorem B2069381 : Blo 1379509 2069381 := bbase (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) (by norm_num)
theorem B2487181 : Blo 1379509 2487181 := bbase (se 3 (by rfl) ⟨466346, by rfl⟩ : syracuseStep 2487181 = 932693) (by norm_num)
theorem B1553305 : Blo 1379509 1553305 := bbase (se 2 (by rfl) ⟨582489, by rfl⟩ : syracuseStep 1553305 = 1164979) (by norm_num)
theorem B2069405 : Blo 1379509 2069405 := bbase (se 3 (by rfl) ⟨388013, by rfl⟩ : syracuseStep 2069405 = 776027) (by norm_num)
theorem B2069429 : Blo 1379509 2069429 := bbase (se 5 (by rfl) ⟨97004, by rfl⟩ : syracuseStep 2069429 = 194009) (by norm_num)
theorem B6984629 : Blo 1379509 6984629 := bbase (se 5 (by rfl) ⟨327404, by rfl⟩ : syracuseStep 6984629 = 654809) (by norm_num)
theorem B1553341 : Blo 1379509 1553341 := bbase (se 3 (by rfl) ⟨291251, by rfl⟩ : syracuseStep 1553341 = 582503) (by norm_num)
theorem B2069453 : Blo 1379509 2069453 := bbase (se 3 (by rfl) ⟨388022, by rfl⟩ : syracuseStep 2069453 = 776045) (by norm_num)
theorem B4420565 : Blo 1379509 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B1553377 : Blo 1379509 1553377 := bbase (se 2 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 1553377 = 1165033) (by norm_num)
theorem B2069477 : Blo 1379509 2069477 := bbase (se 4 (by rfl) ⟨194013, by rfl⟩ : syracuseStep 2069477 = 388027) (by norm_num)
theorem B11793397 : Blo 1379509 11793397 := bbase (se 5 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 11793397 = 1105631) (by norm_num)
theorem B2069501 : Blo 1379509 2069501 := bbase (se 3 (by rfl) ⟨388031, by rfl⟩ : syracuseStep 2069501 = 776063) (by norm_num)
theorem B2798597 : Blo 1379509 2798597 := bbase (se 4 (by rfl) ⟨262368, by rfl⟩ : syracuseStep 2798597 = 524737) (by norm_num)
theorem B1553413 : Blo 1379509 1553413 := bbase (se 4 (by rfl) ⟨145632, by rfl⟩ : syracuseStep 1553413 = 291265) (by norm_num)
theorem B2069525 : Blo 1379509 2069525 := bbase (se 6 (by rfl) ⟨48504, by rfl⟩ : syracuseStep 2069525 = 97009) (by norm_num)
theorem B1553449 : Blo 1379509 1553449 := bbase (se 2 (by rfl) ⟨582543, by rfl⟩ : syracuseStep 1553449 = 1165087) (by norm_num)
theorem B2069549 : Blo 1379509 2069549 := bbase (se 3 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 2069549 = 776081) (by norm_num)
theorem B2069573 : Blo 1379509 2069573 := bbase (se 4 (by rfl) ⟨194022, by rfl⟩ : syracuseStep 2069573 = 388045) (by norm_num)
theorem B1553485 : Blo 1379509 1553485 := bbase (se 3 (by rfl) ⟨291278, by rfl⟩ : syracuseStep 1553485 = 582557) (by norm_num)
theorem B4977749 : Blo 1379509 4977749 := bbase (se 8 (by rfl) ⟨29166, by rfl⟩ : syracuseStep 4977749 = 58333) (by norm_num)
theorem B2069597 : Blo 1379509 2069597 := bbase (se 3 (by rfl) ⟨388049, by rfl⟩ : syracuseStep 2069597 = 776099) (by norm_num)
theorem B1553521 : Blo 1379509 1553521 := bbase (se 2 (by rfl) ⟨582570, by rfl⟩ : syracuseStep 1553521 = 1165141) (by norm_num)
theorem B2069621 : Blo 1379509 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B4658309 : Blo 1379509 4658309 := bbase (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) (by norm_num)
theorem B2069645 : Blo 1379509 2069645 := bbase (se 3 (by rfl) ⟨388058, by rfl⟩ : syracuseStep 2069645 = 776117) (by norm_num)
theorem B1553557 : Blo 1379509 1553557 := bbase (se 6 (by rfl) ⟨36411, by rfl⟩ : syracuseStep 1553557 = 72823) (by norm_num)
theorem B2069669 : Blo 1379509 2069669 := bbase (se 4 (by rfl) ⟨194031, by rfl⟩ : syracuseStep 2069669 = 388063) (by norm_num)
theorem B1553593 : Blo 1379509 1553593 := bbase (se 2 (by rfl) ⟨582597, by rfl⟩ : syracuseStep 1553593 = 1165195) (by norm_num)
theorem B2069693 : Blo 1379509 2069693 := bbase (se 3 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 2069693 = 776135) (by norm_num)
theorem B3495109 : Blo 1379509 3495109 := bbase (se 4 (by rfl) ⟨327666, by rfl⟩ : syracuseStep 3495109 = 655333) (by norm_num)
theorem B2069717 : Blo 1379509 2069717 := bbase (se 7 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 2069717 = 48509) (by norm_num)
theorem B1553629 : Blo 1379509 1553629 := bbase (se 3 (by rfl) ⟨291305, by rfl⟩ : syracuseStep 1553629 = 582611) (by norm_num)
theorem B2069741 : Blo 1379509 2069741 := bbase (se 3 (by rfl) ⟨388076, by rfl⟩ : syracuseStep 2069741 = 776153) (by norm_num)
theorem B1553665 : Blo 1379509 1553665 := bbase (se 2 (by rfl) ⟨582624, by rfl⟩ : syracuseStep 1553665 = 1165249) (by norm_num)
theorem B2069765 : Blo 1379509 2069765 := bbase (se 4 (by rfl) ⟨194040, by rfl⟩ : syracuseStep 2069765 = 388081) (by norm_num)
theorem B2069789 : Blo 1379509 2069789 := bbase (se 3 (by rfl) ⟨388085, by rfl⟩ : syracuseStep 2069789 = 776171) (by norm_num)
theorem B1553701 : Blo 1379509 1553701 := bbase (se 4 (by rfl) ⟨145659, by rfl⟩ : syracuseStep 1553701 = 291319) (by norm_num)
theorem B2069813 : Blo 1379509 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B3495221 : Blo 1379509 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B1553737 : Blo 1379509 1553737 := bbase (se 2 (by rfl) ⟨582651, by rfl⟩ : syracuseStep 1553737 = 1165303) (by norm_num)
theorem B2069837 : Blo 1379509 2069837 := bbase (se 3 (by rfl) ⟨388094, by rfl⟩ : syracuseStep 2069837 = 776189) (by norm_num)
theorem B2069861 : Blo 1379509 2069861 := bbase (se 4 (by rfl) ⟨194049, by rfl⟩ : syracuseStep 2069861 = 388099) (by norm_num)
theorem B1553773 : Blo 1379509 1553773 := bbase (se 3 (by rfl) ⟨291332, by rfl⟩ : syracuseStep 1553773 = 582665) (by norm_num)
theorem B2069885 : Blo 1379509 2069885 := bbase (se 3 (by rfl) ⟨388103, by rfl⟩ : syracuseStep 2069885 = 776207) (by norm_num)
theorem B1553809 : Blo 1379509 1553809 := bbase (se 2 (by rfl) ⟨582678, by rfl⟩ : syracuseStep 1553809 = 1165357) (by norm_num)
theorem B2069909 : Blo 1379509 2069909 := bbase (se 6 (by rfl) ⟨48513, by rfl⟩ : syracuseStep 2069909 = 97027) (by norm_num)
theorem B2069933 : Blo 1379509 2069933 := bbase (se 3 (by rfl) ⟨388112, by rfl⟩ : syracuseStep 2069933 = 776225) (by norm_num)
theorem B5895605 : Blo 1379509 5895605 := bbase (se 5 (by rfl) ⟨276356, by rfl⟩ : syracuseStep 5895605 = 552713) (by norm_num)
theorem B3315125 : Blo 1379509 3315125 := bbase (se 5 (by rfl) ⟨155396, by rfl⟩ : syracuseStep 3315125 = 310793) (by norm_num)
theorem B1553845 : Blo 1379509 1553845 := bbase (se 5 (by rfl) ⟨72836, by rfl⟩ : syracuseStep 1553845 = 145673) (by norm_num)
theorem B2069957 : Blo 1379509 2069957 := bbase (se 4 (by rfl) ⟨194058, by rfl⟩ : syracuseStep 2069957 = 388117) (by norm_num)
theorem B1553881 : Blo 1379509 1553881 := bbase (se 2 (by rfl) ⟨582705, by rfl⟩ : syracuseStep 1553881 = 1165411) (by norm_num)
theorem B2069981 : Blo 1379509 2069981 := bbase (se 3 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 2069981 = 776243) (by norm_num)
theorem B3929573 : Blo 1379509 3929573 := bbase (se 4 (by rfl) ⟨368397, by rfl⟩ : syracuseStep 3929573 = 736795) (by norm_num)
theorem B2070005 : Blo 1379509 2070005 := bbase (se 5 (by rfl) ⟨97031, by rfl⟩ : syracuseStep 2070005 = 194063) (by norm_num)
theorem B3495413 : Blo 1379509 3495413 := bbase (se 5 (by rfl) ⟨163847, by rfl⟩ : syracuseStep 3495413 = 327695) (by norm_num)
theorem B1553917 : Blo 1379509 1553917 := bbase (se 3 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 1553917 = 582719) (by norm_num)
theorem B2070029 : Blo 1379509 2070029 := bbase (se 3 (by rfl) ⟨388130, by rfl⟩ : syracuseStep 2070029 = 776261) (by norm_num)
theorem B8844821 : Blo 1379509 8844821 := bbase (se 6 (by rfl) ⟨207300, by rfl⟩ : syracuseStep 8844821 = 414601) (by norm_num)
theorem B1553953 : Blo 1379509 1553953 := bbase (se 2 (by rfl) ⟨582732, by rfl⟩ : syracuseStep 1553953 = 1165465) (by norm_num)
theorem B2070053 : Blo 1379509 2070053 := bbase (se 4 (by rfl) ⟨194067, by rfl⟩ : syracuseStep 2070053 = 388135) (by norm_num)
theorem B4658741 : Blo 1379509 4658741 := bbase (se 5 (by rfl) ⟨218378, by rfl⟩ : syracuseStep 4658741 = 436757) (by norm_num)
theorem B2070077 : Blo 1379509 2070077 := bbase (se 3 (by rfl) ⟨388139, by rfl⟩ : syracuseStep 2070077 = 776279) (by norm_num)
theorem B1553989 : Blo 1379509 1553989 := bbase (se 4 (by rfl) ⟨145686, by rfl⟩ : syracuseStep 1553989 = 291373) (by norm_num)
theorem B14161493 : Blo 1379509 14161493 := bbase (se 8 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 14161493 = 165955) (by norm_num)
theorem B2070101 : Blo 1379509 2070101 := bbase (se 8 (by rfl) ⟨12129, by rfl⟩ : syracuseStep 2070101 = 24259) (by norm_num)
theorem B2487901 : Blo 1379509 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B1554025 : Blo 1379509 1554025 := bbase (se 2 (by rfl) ⟨582759, by rfl⟩ : syracuseStep 1554025 = 1165519) (by norm_num)
theorem B2070125 : Blo 1379509 2070125 := bbase (se 3 (by rfl) ⟨388148, by rfl⟩ : syracuseStep 2070125 = 776297) (by norm_num)
theorem B2070149 : Blo 1379509 2070149 := bbase (se 4 (by rfl) ⟨194076, by rfl⟩ : syracuseStep 2070149 = 388153) (by norm_num)
theorem B1554061 : Blo 1379509 1554061 := bbase (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) (by norm_num)
theorem B2946709 : Blo 1379509 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B2070173 : Blo 1379509 2070173 := bbase (se 3 (by rfl) ⟨388157, by rfl⟩ : syracuseStep 2070173 = 776315) (by norm_num)
theorem B1554097 : Blo 1379509 1554097 := bbase (se 2 (by rfl) ⟨582786, by rfl⟩ : syracuseStep 1554097 = 1165573) (by norm_num)
theorem B2070197 : Blo 1379509 2070197 := bbase (se 5 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 2070197 = 194081) (by norm_num)
theorem B2487989 : Blo 1379509 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B2070221 : Blo 1379509 2070221 := bbase (se 3 (by rfl) ⟨388166, by rfl⟩ : syracuseStep 2070221 = 776333) (by norm_num)
theorem B1554133 : Blo 1379509 1554133 := bbase (se 7 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 1554133 = 36425) (by norm_num)
theorem B2070245 : Blo 1379509 2070245 := bbase (se 4 (by rfl) ⟨194085, by rfl⟩ : syracuseStep 2070245 = 388171) (by norm_num)
theorem B1554169 : Blo 1379509 1554169 := bbase (se 2 (by rfl) ⟨582813, by rfl⟩ : syracuseStep 1554169 = 1165627) (by norm_num)
theorem B2070269 : Blo 1379509 2070269 := bbase (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) (by norm_num)
theorem B2070293 : Blo 1379509 2070293 := bbase (se 6 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 2070293 = 97045) (by norm_num)
theorem B6993701 : Blo 1379509 6993701 := bbase (se 4 (by rfl) ⟨655659, by rfl⟩ : syracuseStep 6993701 = 1311319) (by norm_num)
theorem B2070317 : Blo 1379509 2070317 := bbase (se 3 (by rfl) ⟨388184, by rfl⟩ : syracuseStep 2070317 = 776369) (by norm_num)
theorem B2070341 : Blo 1379509 2070341 := bbase (se 4 (by rfl) ⟨194094, by rfl⟩ : syracuseStep 2070341 = 388189) (by norm_num)
theorem B5240645 : Blo 1379509 5240645 := bbase (se 4 (by rfl) ⟨491310, by rfl⟩ : syracuseStep 5240645 = 982621) (by norm_num)
theorem B1398601 : Blo 1379509 1398601 := bbase (se 2 (by rfl) ⟨524475, by rfl⟩ : syracuseStep 1398601 = 1048951) (by norm_num)
theorem B3495757 : Blo 1379509 3495757 := bbase (se 3 (by rfl) ⟨655454, by rfl⟩ : syracuseStep 3495757 = 1310909) (by norm_num)
theorem B2619229 : Blo 1379509 2619229 := bbase (se 3 (by rfl) ⟨491105, by rfl⟩ : syracuseStep 2619229 = 982211) (by norm_num)
theorem B2070365 : Blo 1379509 2070365 := bbase (se 3 (by rfl) ⟨388193, by rfl⟩ : syracuseStep 2070365 = 776387) (by norm_num)
theorem B2070389 : Blo 1379509 2070389 := bbase (se 5 (by rfl) ⟨97049, by rfl⟩ : syracuseStep 2070389 = 194099) (by norm_num)
theorem B2070413 : Blo 1379509 2070413 := bbase (se 3 (by rfl) ⟨388202, by rfl⟩ : syracuseStep 2070413 = 776405) (by norm_num)
theorem B25188245 : Blo 1379509 25188245 := bbase (se 6 (by rfl) ⟨590349, by rfl⟩ : syracuseStep 25188245 = 1180699) (by norm_num)
theorem B2070437 : Blo 1379509 2070437 := bbase (se 4 (by rfl) ⟨194103, by rfl⟩ : syracuseStep 2070437 = 388207) (by norm_num)
theorem B2070461 : Blo 1379509 2070461 := bbase (se 3 (by rfl) ⟨388211, by rfl⟩ : syracuseStep 2070461 = 776423) (by norm_num)
theorem B3495869 : Blo 1379509 3495869 := bbase (se 3 (by rfl) ⟨655475, by rfl⟩ : syracuseStep 3495869 = 1310951) (by norm_num)
theorem B2070485 : Blo 1379509 2070485 := bbase (se 7 (by rfl) ⟨24263, by rfl⟩ : syracuseStep 2070485 = 48527) (by norm_num)
theorem B4659173 : Blo 1379509 4659173 := bbase (se 4 (by rfl) ⟨436797, by rfl⟩ : syracuseStep 4659173 = 873595) (by norm_num)
theorem B2619373 : Blo 1379509 2619373 := bbase (se 3 (by rfl) ⟨491132, by rfl⟩ : syracuseStep 2619373 = 982265) (by norm_num)
theorem B2070509 : Blo 1379509 2070509 := bbase (se 3 (by rfl) ⟨388220, by rfl⟩ : syracuseStep 2070509 = 776441) (by norm_num)
theorem B2209789 : Blo 1379509 2209789 := bbase (se 3 (by rfl) ⟨414335, by rfl⟩ : syracuseStep 2209789 = 828671) (by norm_num)
theorem B2070533 : Blo 1379509 2070533 := bbase (se 4 (by rfl) ⟨194112, by rfl⟩ : syracuseStep 2070533 = 388225) (by norm_num)
theorem B2070557 : Blo 1379509 2070557 := bbase (se 3 (by rfl) ⟨388229, by rfl⟩ : syracuseStep 2070557 = 776459) (by norm_num)
theorem B2070581 : Blo 1379509 2070581 := bbase (se 5 (by rfl) ⟨97058, by rfl⟩ : syracuseStep 2070581 = 194117) (by norm_num)
theorem B4790341 : Blo 1379509 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B2070605 : Blo 1379509 2070605 := bbase (se 3 (by rfl) ⟨388238, by rfl⟩ : syracuseStep 2070605 = 776477) (by norm_num)
theorem B19888213 : Blo 1379509 19888213 := bbase (se 8 (by rfl) ⟨116532, by rfl⟩ : syracuseStep 19888213 = 233065) (by norm_num)
theorem B1398877 : Blo 1379509 1398877 := bbase (se 3 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 1398877 = 524579) (by norm_num)
theorem B5240933 : Blo 1379509 5240933 := bbase (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) (by norm_num)
theorem B2070629 : Blo 1379509 2070629 := bbase (se 4 (by rfl) ⟨194121, by rfl⟩ : syracuseStep 2070629 = 388243) (by norm_num)
theorem B2488421 : Blo 1379509 2488421 := bbase (se 4 (by rfl) ⟨233289, by rfl⟩ : syracuseStep 2488421 = 466579) (by norm_num)
theorem B2070653 : Blo 1379509 2070653 := bbase (se 3 (by rfl) ⟨388247, by rfl⟩ : syracuseStep 2070653 = 776495) (by norm_num)
theorem B3496061 : Blo 1379509 3496061 := bbase (se 3 (by rfl) ⟨655511, by rfl⟩ : syracuseStep 3496061 = 1311023) (by norm_num)
theorem B2947205 : Blo 1379509 2947205 := bbase (se 4 (by rfl) ⟨276300, by rfl⟩ : syracuseStep 2947205 = 552601) (by norm_num)
theorem B3930245 : Blo 1379509 3930245 := bbase (se 4 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 3930245 = 736921) (by norm_num)
theorem B2619533 : Blo 1379509 2619533 := bbase (se 3 (by rfl) ⟨491162, by rfl⟩ : syracuseStep 2619533 = 982325) (by norm_num)
theorem B2070677 : Blo 1379509 2070677 := bbase (se 6 (by rfl) ⟨48531, by rfl⟩ : syracuseStep 2070677 = 97063) (by norm_num)
theorem B2070701 : Blo 1379509 2070701 := bbase (se 3 (by rfl) ⟨388256, by rfl⟩ : syracuseStep 2070701 = 776513) (by norm_num)
theorem B6985925 : Blo 1379509 6985925 := bbase (se 4 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 6985925 = 1309861) (by norm_num)
theorem B2070725 : Blo 1379509 2070725 := bbase (se 4 (by rfl) ⟨194130, by rfl⟩ : syracuseStep 2070725 = 388261) (by norm_num)
theorem B1964245 : Blo 1379509 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B2070749 : Blo 1379509 2070749 := bbase (se 3 (by rfl) ⟨388265, by rfl⟩ : syracuseStep 2070749 = 776531) (by norm_num)
theorem B2070773 : Blo 1379509 2070773 := bbase (se 5 (by rfl) ⟨97067, by rfl⟩ : syracuseStep 2070773 = 194135) (by norm_num)
theorem B2488565 : Blo 1379509 2488565 := bbase (se 5 (by rfl) ⟨116651, by rfl⟩ : syracuseStep 2488565 = 233303) (by norm_num)
theorem B2070797 : Blo 1379509 2070797 := bbase (se 3 (by rfl) ⟨388274, by rfl⟩ : syracuseStep 2070797 = 776549) (by norm_num)
theorem B4421909 : Blo 1379509 4421909 := bbase (se 6 (by rfl) ⟨103638, by rfl⟩ : syracuseStep 4421909 = 207277) (by norm_num)
theorem B2619677 : Blo 1379509 2619677 := bbase (se 3 (by rfl) ⟨491189, by rfl⟩ : syracuseStep 2619677 = 982379) (by norm_num)
theorem B2070821 : Blo 1379509 2070821 := bbase (se 4 (by rfl) ⟨194139, by rfl⟩ : syracuseStep 2070821 = 388279) (by norm_num)
theorem B2070845 : Blo 1379509 2070845 := bbase (se 3 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 2070845 = 776567) (by norm_num)
theorem B2070869 : Blo 1379509 2070869 := bbase (se 10 (by rfl) ⟨3033, by rfl⟩ : syracuseStep 2070869 = 6067) (by norm_num)
theorem B2070893 : Blo 1379509 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B2070917 : Blo 1379509 2070917 := bbase (se 4 (by rfl) ⟨194148, by rfl⟩ : syracuseStep 2070917 = 388297) (by norm_num)
theorem B5896597 : Blo 1379509 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B4659605 : Blo 1379509 4659605 := bbase (se 6 (by rfl) ⟨109209, by rfl⟩ : syracuseStep 4659605 = 218419) (by norm_num)
theorem B2070941 : Blo 1379509 2070941 := bbase (se 3 (by rfl) ⟨388301, by rfl⟩ : syracuseStep 2070941 = 776603) (by norm_num)
theorem B2070965 : Blo 1379509 2070965 := bbase (se 5 (by rfl) ⟨97076, by rfl⟩ : syracuseStep 2070965 = 194153) (by norm_num)
theorem B2070989 : Blo 1379509 2070989 := bbase (se 3 (by rfl) ⟨388310, by rfl⟩ : syracuseStep 2070989 = 776621) (by norm_num)
theorem B2488781 : Blo 1379509 2488781 := bbase (se 3 (by rfl) ⟨466646, by rfl⟩ : syracuseStep 2488781 = 933293) (by norm_num)
theorem B3496405 : Blo 1379509 3496405 := bbase (se 7 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 3496405 = 81947) (by norm_num)
theorem B2071013 : Blo 1379509 2071013 := bbase (se 4 (by rfl) ⟨194157, by rfl⟩ : syracuseStep 2071013 = 388315) (by norm_num)
theorem B2071037 : Blo 1379509 2071037 := bbase (se 3 (by rfl) ⟨388319, by rfl⟩ : syracuseStep 2071037 = 776639) (by norm_num)
theorem B2071061 : Blo 1379509 2071061 := bbase (se 6 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 2071061 = 97081) (by norm_num)
theorem B2071085 : Blo 1379509 2071085 := bbase (se 3 (by rfl) ⟨388328, by rfl⟩ : syracuseStep 2071085 = 776657) (by norm_num)
theorem B3930677 : Blo 1379509 3930677 := bbase (se 5 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 3930677 = 368501) (by norm_num)
theorem B2619965 : Blo 1379509 2619965 := bbase (se 3 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 2619965 = 982487) (by norm_num)
theorem B2071109 : Blo 1379509 2071109 := bbase (se 4 (by rfl) ⟨194166, by rfl⟩ : syracuseStep 2071109 = 388333) (by norm_num)
theorem B3496517 : Blo 1379509 3496517 := bbase (se 4 (by rfl) ⟨327798, by rfl⟩ : syracuseStep 3496517 = 655597) (by norm_num)
theorem B1964621 : Blo 1379509 1964621 := bbase (se 3 (by rfl) ⟨368366, by rfl⟩ : syracuseStep 1964621 = 736733) (by norm_num)
theorem B2071133 : Blo 1379509 2071133 := bbase (se 3 (by rfl) ⟨388337, by rfl⟩ : syracuseStep 2071133 = 776675) (by norm_num)
theorem B2071157 : Blo 1379509 2071157 := bbase (se 5 (by rfl) ⟨97085, by rfl⟩ : syracuseStep 2071157 = 194171) (by norm_num)
theorem B2071181 : Blo 1379509 2071181 := bbase (se 3 (by rfl) ⟨388346, by rfl⟩ : syracuseStep 2071181 = 776693) (by norm_num)
theorem B1399441 : Blo 1379509 1399441 := bbase (se 2 (by rfl) ⟨524790, by rfl⟩ : syracuseStep 1399441 = 1049581) (by norm_num)
theorem B1866397 : Blo 1379509 1866397 := bbase (se 3 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 1866397 = 699899) (by norm_num)
theorem B2071205 : Blo 1379509 2071205 := bbase (se 4 (by rfl) ⟨194175, by rfl⟩ : syracuseStep 2071205 = 388351) (by norm_num)
theorem B2071229 : Blo 1379509 2071229 := bbase (se 3 (by rfl) ⟨388355, by rfl⟩ : syracuseStep 2071229 = 776711) (by norm_num)
theorem B2620117 : Blo 1379509 2620117 := bbase (se 7 (by rfl) ⟨30704, by rfl⟩ : syracuseStep 2620117 = 61409) (by norm_num)
theorem B2071253 : Blo 1379509 2071253 := bbase (se 7 (by rfl) ⟨24272, by rfl⟩ : syracuseStep 2071253 = 48545) (by norm_num)
theorem B2071277 : Blo 1379509 2071277 := bbase (se 3 (by rfl) ⟨388364, by rfl⟩ : syracuseStep 2071277 = 776729) (by norm_num)
theorem B2071301 : Blo 1379509 2071301 := bbase (se 4 (by rfl) ⟨194184, by rfl⟩ : syracuseStep 2071301 = 388369) (by norm_num)
theorem B3496709 : Blo 1379509 3496709 := bbase (se 4 (by rfl) ⟨327816, by rfl⟩ : syracuseStep 3496709 = 655633) (by norm_num)
theorem B2071325 : Blo 1379509 2071325 := bbase (se 3 (by rfl) ⟨388373, by rfl⟩ : syracuseStep 2071325 = 776747) (by norm_num)
theorem B2071349 : Blo 1379509 2071349 := bbase (se 5 (by rfl) ⟨97094, by rfl⟩ : syracuseStep 2071349 = 194189) (by norm_num)
theorem B2800445 : Blo 1379509 2800445 := bbase (se 3 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 2800445 = 1050167) (by norm_num)
theorem B4660037 : Blo 1379509 4660037 := bbase (se 4 (by rfl) ⟨436878, by rfl⟩ : syracuseStep 4660037 = 873757) (by norm_num)
theorem B2071373 : Blo 1379509 2071373 := bbase (se 3 (by rfl) ⟨388382, by rfl⟩ : syracuseStep 2071373 = 776765) (by norm_num)
theorem B6634325 : Blo 1379509 6634325 := bbase (se 9 (by rfl) ⟨19436, by rfl⟩ : syracuseStep 6634325 = 38873) (by norm_num)
theorem B15727445 : Blo 1379509 15727445 := bbase (se 9 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 15727445 = 92153) (by norm_num)
theorem B2071397 : Blo 1379509 2071397 := bbase (se 4 (by rfl) ⟨194193, by rfl⟩ : syracuseStep 2071397 = 388387) (by norm_num)
theorem B1473385 : Blo 1379509 1473385 := bbase (se 2 (by rfl) ⟨552519, by rfl⟩ : syracuseStep 1473385 = 1105039) (by norm_num)
theorem B2071421 : Blo 1379509 2071421 := bbase (se 3 (by rfl) ⟨388391, by rfl⟩ : syracuseStep 2071421 = 776783) (by norm_num)
theorem B2071445 : Blo 1379509 2071445 := bbase (se 6 (by rfl) ⟨48549, by rfl⟩ : syracuseStep 2071445 = 97099) (by norm_num)
theorem B2071469 : Blo 1379509 2071469 := bbase (se 3 (by rfl) ⟨388400, by rfl⟩ : syracuseStep 2071469 = 776801) (by norm_num)
theorem B11795381 : Blo 1379509 11795381 := bbase (se 5 (by rfl) ⟨552908, by rfl⟩ : syracuseStep 11795381 = 1105817) (by norm_num)
theorem B2071493 : Blo 1379509 2071493 := bbase (se 4 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 2071493 = 388405) (by norm_num)
theorem B2071517 : Blo 1379509 2071517 := bbase (se 3 (by rfl) ⟨388409, by rfl⟩ : syracuseStep 2071517 = 776819) (by norm_num)
theorem B2948069 : Blo 1379509 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B2071541 : Blo 1379509 2071541 := bbase (se 5 (by rfl) ⟨97103, by rfl⟩ : syracuseStep 2071541 = 194207) (by norm_num)
theorem B2620421 : Blo 1379509 2620421 := bbase (se 4 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 2620421 = 491329) (by norm_num)
theorem B2071565 : Blo 1379509 2071565 := bbase (se 3 (by rfl) ⟨388418, by rfl⟩ : syracuseStep 2071565 = 776837) (by norm_num)
theorem B8969237 : Blo 1379509 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B2071589 : Blo 1379509 2071589 := bbase (se 4 (by rfl) ⟨194211, by rfl⟩ : syracuseStep 2071589 = 388423) (by norm_num)
theorem B2071613 : Blo 1379509 2071613 := bbase (se 3 (by rfl) ⟨388427, by rfl⟩ : syracuseStep 2071613 = 776855) (by norm_num)
theorem B2071637 : Blo 1379509 2071637 := bbase (se 8 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 2071637 = 24277) (by norm_num)
theorem B2210917 : Blo 1379509 2210917 := bbase (se 4 (by rfl) ⟨207273, by rfl⟩ : syracuseStep 2210917 = 414547) (by norm_num)
theorem B2071661 : Blo 1379509 2071661 := bbase (se 3 (by rfl) ⟨388436, by rfl⟩ : syracuseStep 2071661 = 776873) (by norm_num)
theorem B2948213 : Blo 1379509 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B1866877 : Blo 1379509 1866877 := bbase (se 3 (by rfl) ⟨350039, by rfl⟩ : syracuseStep 1866877 = 700079) (by norm_num)
theorem B2071685 : Blo 1379509 2071685 := bbase (se 4 (by rfl) ⟨194220, by rfl⟩ : syracuseStep 2071685 = 388441) (by norm_num)
theorem B3103901 : Blo 1379509 3103901 := bbase (se 3 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 3103901 = 1163963) (by norm_num)
theorem B2071709 : Blo 1379509 2071709 := bbase (se 3 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 2071709 = 776891) (by norm_num)
theorem B2071733 : Blo 1379509 2071733 := bbase (se 5 (by rfl) ⟨97112, by rfl⟩ : syracuseStep 2071733 = 194225) (by norm_num)
theorem B2071757 : Blo 1379509 2071757 := bbase (se 3 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 2071757 = 776909) (by norm_num)
theorem B1473761 : Blo 1379509 1473761 := bbase (se 2 (by rfl) ⟨552660, by rfl⟩ : syracuseStep 1473761 = 1105321) (by norm_num)
theorem B3103973 : Blo 1379509 3103973 := bbase (se 4 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 3103973 = 581995) (by norm_num)
theorem B2071781 : Blo 1379509 2071781 := bbase (se 4 (by rfl) ⟨194229, by rfl⟩ : syracuseStep 2071781 = 388459) (by norm_num)
theorem B4660469 : Blo 1379509 4660469 := bbase (se 5 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 4660469 = 436919) (by norm_num)
theorem B2071805 : Blo 1379509 2071805 := bbase (se 3 (by rfl) ⟨388463, by rfl⟩ : syracuseStep 2071805 = 776927) (by norm_num)
theorem B5242117 : Blo 1379509 5242117 := bbase (se 4 (by rfl) ⟨491448, by rfl⟩ : syracuseStep 5242117 = 982897) (by norm_num)
theorem B1400069 : Blo 1379509 1400069 := bbase (se 4 (by rfl) ⟨131256, by rfl⟩ : syracuseStep 1400069 = 262513) (by norm_num)
theorem B2071829 : Blo 1379509 2071829 := bbase (se 6 (by rfl) ⟨48558, by rfl⟩ : syracuseStep 2071829 = 97117) (by norm_num)
theorem B3931429 : Blo 1379509 3931429 := bbase (se 4 (by rfl) ⟨368571, by rfl⟩ : syracuseStep 3931429 = 737143) (by norm_num)
theorem B1473833 : Blo 1379509 1473833 := bbase (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) (by norm_num)
theorem B3104045 : Blo 1379509 3104045 := bbase (se 3 (by rfl) ⟨582008, by rfl⟩ : syracuseStep 3104045 = 1164017) (by norm_num)
theorem B2071853 : Blo 1379509 2071853 := bbase (se 3 (by rfl) ⟨388472, by rfl⟩ : syracuseStep 2071853 = 776945) (by norm_num)
theorem B2071877 : Blo 1379509 2071877 := bbase (se 4 (by rfl) ⟨194238, by rfl⟩ : syracuseStep 2071877 = 388477) (by norm_num)
theorem B2071901 : Blo 1379509 2071901 := bbase (se 3 (by rfl) ⟨388481, by rfl⟩ : syracuseStep 2071901 = 776963) (by norm_num)
theorem B3104117 : Blo 1379509 3104117 := bbase (se 5 (by rfl) ⟨145505, by rfl⟩ : syracuseStep 3104117 = 291011) (by norm_num)
theorem B2071925 : Blo 1379509 2071925 := bbase (se 5 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 2071925 = 194243) (by norm_num)
theorem B3317125 : Blo 1379509 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B2071949 : Blo 1379509 2071949 := bbase (se 3 (by rfl) ⟨388490, by rfl⟩ : syracuseStep 2071949 = 776981) (by norm_num)
theorem B4971941 : Blo 1379509 4971941 := bbase (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) (by norm_num)
theorem B2071973 : Blo 1379509 2071973 := bbase (se 4 (by rfl) ⟨194247, by rfl⟩ : syracuseStep 2071973 = 388495) (by norm_num)
theorem B3104189 : Blo 1379509 3104189 := bbase (se 3 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 3104189 = 1164071) (by norm_num)
theorem B2071997 : Blo 1379509 2071997 := bbase (se 3 (by rfl) ⟨388499, by rfl⟩ : syracuseStep 2071997 = 776999) (by norm_num)
theorem B6987221 : Blo 1379509 6987221 := bbase (se 7 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 6987221 = 163763) (by norm_num)
theorem B2072021 : Blo 1379509 2072021 := bbase (se 7 (by rfl) ⟨24281, by rfl⟩ : syracuseStep 2072021 = 48563) (by norm_num)
theorem B1474021 : Blo 1379509 1474021 := bbase (se 4 (by rfl) ⟨138189, by rfl⟩ : syracuseStep 1474021 = 276379) (by norm_num)
theorem B2072045 : Blo 1379509 2072045 := bbase (se 3 (by rfl) ⟨388508, by rfl⟩ : syracuseStep 2072045 = 777017) (by norm_num)
theorem B9952757 : Blo 1379509 9952757 := bbase (se 5 (by rfl) ⟨466535, by rfl⟩ : syracuseStep 9952757 = 933071) (by norm_num)
theorem B3104261 : Blo 1379509 3104261 := bbase (se 4 (by rfl) ⟨291024, by rfl⟩ : syracuseStep 3104261 = 582049) (by norm_num)
theorem B2072069 : Blo 1379509 2072069 := bbase (se 4 (by rfl) ⟨194256, by rfl⟩ : syracuseStep 2072069 = 388513) (by norm_num)
theorem B3317269 : Blo 1379509 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B2072093 : Blo 1379509 2072093 := bbase (se 3 (by rfl) ⟨388517, by rfl⟩ : syracuseStep 2072093 = 777035) (by norm_num)
theorem B2211365 : Blo 1379509 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B5242421 : Blo 1379509 5242421 := bbase (se 5 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 5242421 = 491477) (by norm_num)
theorem B2072117 : Blo 1379509 2072117 := bbase (se 5 (by rfl) ⟨97130, by rfl⟩ : syracuseStep 2072117 = 194261) (by norm_num)
theorem B3104333 : Blo 1379509 3104333 := bbase (se 3 (by rfl) ⟨582062, by rfl⟩ : syracuseStep 3104333 = 1164125) (by norm_num)
theorem B2072141 : Blo 1379509 2072141 := bbase (se 3 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 2072141 = 777053) (by norm_num)
theorem B2072165 : Blo 1379509 2072165 := bbase (se 4 (by rfl) ⟨194265, by rfl⟩ : syracuseStep 2072165 = 388531) (by norm_num)
theorem B2072189 : Blo 1379509 2072189 := bbase (se 3 (by rfl) ⟨388535, by rfl⟩ : syracuseStep 2072189 = 777071) (by norm_num)
theorem B3104405 : Blo 1379509 3104405 := bbase (se 6 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 3104405 = 145519) (by norm_num)
theorem B2072213 : Blo 1379509 2072213 := bbase (se 6 (by rfl) ⟨48567, by rfl⟩ : syracuseStep 2072213 = 97135) (by norm_num)
theorem B1474205 : Blo 1379509 1474205 := bbase (se 3 (by rfl) ⟨276413, by rfl⟩ : syracuseStep 1474205 = 552827) (by norm_num)
theorem B4660901 : Blo 1379509 4660901 := bbase (se 4 (by rfl) ⟨436959, by rfl⟩ : syracuseStep 4660901 = 873919) (by norm_num)
theorem B2072237 : Blo 1379509 2072237 := bbase (se 3 (by rfl) ⟨388544, by rfl⟩ : syracuseStep 2072237 = 777089) (by norm_num)
theorem B4972213 : Blo 1379509 4972213 := bbase (se 5 (by rfl) ⟨233072, by rfl⟩ : syracuseStep 4972213 = 466145) (by norm_num)
theorem B2072261 : Blo 1379509 2072261 := bbase (se 4 (by rfl) ⟨194274, by rfl⟩ : syracuseStep 2072261 = 388549) (by norm_num)
theorem B3104477 : Blo 1379509 3104477 := bbase (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) (by norm_num)
theorem B2621173 : Blo 1379509 2621173 := bbase (se 5 (by rfl) ⟨122867, by rfl⟩ : syracuseStep 2621173 = 245735) (by norm_num)
theorem B3104549 : Blo 1379509 3104549 := bbase (se 4 (by rfl) ⟨291051, by rfl⟩ : syracuseStep 3104549 = 582103) (by norm_num)
theorem B4972373 : Blo 1379509 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B2948957 : Blo 1379509 2948957 := bbase (se 3 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 2948957 = 1105859) (by norm_num)
theorem B3104621 : Blo 1379509 3104621 := bbase (se 3 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 3104621 = 1164233) (by norm_num)
theorem B2621317 : Blo 1379509 2621317 := bbase (se 4 (by rfl) ⟨245748, by rfl⟩ : syracuseStep 2621317 = 491497) (by norm_num)
theorem B3104693 : Blo 1379509 3104693 := bbase (se 5 (by rfl) ⟨145532, by rfl⟩ : syracuseStep 3104693 = 291065) (by norm_num)
theorem B1966045 : Blo 1379509 1966045 := bbase (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) (by norm_num)
theorem B3104765 : Blo 1379509 3104765 := bbase (se 3 (by rfl) ⟨582143, by rfl⟩ : syracuseStep 3104765 = 1164287) (by norm_num)
theorem B7462925 : Blo 1379509 7462925 := bstep (se 3 (by rfl) ⟨1399298, by rfl⟩ : syracuseStep 7462925 = 2798597) B2798597
theorem B2211923 : Blo 1379509 2211923 := bstep (se 1 (by rfl) ⟨1658942, by rfl⟩ : syracuseStep 2211923 = 3317885) B3317885
theorem B26517617 : Blo 1379509 26517617 := bstep (se 2 (by rfl) ⟨9944106, by rfl⟩ : syracuseStep 26517617 = 19888213) B19888213
theorem B21241997 : Blo 1379509 21241997 := bstep (se 3 (by rfl) ⟨3982874, by rfl⟩ : syracuseStep 21241997 = 7965749) B7965749
theorem B3104945 : Blo 1379509 3104945 := bstep (se 2 (by rfl) ⟨1164354, by rfl⟩ : syracuseStep 3104945 = 2328709) B2328709
theorem B3104963 : Blo 1379509 3104963 := bstep (se 1 (by rfl) ⟨2328722, by rfl⟩ : syracuseStep 3104963 = 4657445) B4657445
theorem B7561507 : Blo 1379509 7561507 := bstep (se 1 (by rfl) ⟨5671130, by rfl⟩ : syracuseStep 7561507 = 11342261) B11342261
theorem B4661549 : Blo 1379509 4661549 := bstep (se 3 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 4661549 = 1748081) B1748081
theorem B5898545 : Blo 1379509 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B2212147 : Blo 1379509 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B4661603 : Blo 1379509 4661603 := bstep (se 1 (by rfl) ⟨3496202, by rfl⟩ : syracuseStep 4661603 = 6992405) B6992405
theorem B2212211 : Blo 1379509 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B3105233 : Blo 1379509 3105233 := bstep (se 2 (by rfl) ⟨1164462, by rfl⟩ : syracuseStep 3105233 = 2328925) B2328925
theorem B3105251 : Blo 1379509 3105251 := bstep (se 1 (by rfl) ⟨2328938, by rfl⟩ : syracuseStep 3105251 = 4657877) B4657877
theorem B5243363 : Blo 1379509 5243363 := bstep (se 1 (by rfl) ⟨3932522, by rfl⟩ : syracuseStep 5243363 = 7865045) B7865045
theorem B2212339 : Blo 1379509 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B2359811 : Blo 1379509 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B1966609 : Blo 1379509 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B4661873 : Blo 1379509 4661873 := bstep (se 2 (by rfl) ⟨1748202, by rfl⟩ : syracuseStep 4661873 = 3496405) B3496405
theorem B3318499 : Blo 1379509 3318499 := bstep (se 1 (by rfl) ⟨2488874, by rfl⟩ : syracuseStep 3318499 = 4977749) B4977749
theorem B3105521 : Blo 1379509 3105521 := bstep (se 2 (by rfl) ⟨1164570, by rfl⟩ : syracuseStep 3105521 = 2329141) B2329141
theorem B3105539 : Blo 1379509 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B3932945 : Blo 1379509 3932945 := bstep (se 2 (by rfl) ⟨1474854, by rfl⟩ : syracuseStep 3932945 = 2949709) B2949709
theorem B28336949 : Blo 1379509 28336949 := bstep (se 5 (by rfl) ⟨1328294, by rfl⟩ : syracuseStep 28336949 = 2656589) B2656589
theorem B2622289 : Blo 1379509 2622289 := bstep (se 2 (by rfl) ⟨983358, by rfl⟩ : syracuseStep 2622289 = 1966717) B1966717
theorem B1966945 : Blo 1379509 1966945 := bstep (se 2 (by rfl) ⟨737604, by rfl⟩ : syracuseStep 1966945 = 1475209) B1475209
theorem B6636401 : Blo 1379509 6636401 := bstep (se 2 (by rfl) ⟨2488650, by rfl⟩ : syracuseStep 6636401 = 4977301) B4977301
theorem B3933137 : Blo 1379509 3933137 := bstep (se 2 (by rfl) ⟨1474926, by rfl⟩ : syracuseStep 3933137 = 2949853) B2949853
theorem B11789297 : Blo 1379509 11789297 := bstep (se 2 (by rfl) ⟨4420986, by rfl⟩ : syracuseStep 11789297 = 8841973) B8841973
theorem B2622449 : Blo 1379509 2622449 := bstep (se 2 (by rfl) ⟨983418, by rfl⟩ : syracuseStep 2622449 = 1966837) B1966837
theorem B2098193 : Blo 1379509 2098193 := bstep (se 2 (by rfl) ⟨786822, by rfl⟩ : syracuseStep 2098193 = 1573645) B1573645
theorem B3105809 : Blo 1379509 3105809 := bstep (se 2 (by rfl) ⟨1164678, by rfl⟩ : syracuseStep 3105809 = 2329357) B2329357
theorem B3105827 : Blo 1379509 3105827 := bstep (se 1 (by rfl) ⟨2329370, by rfl⟩ : syracuseStep 3105827 = 4658741) B4658741
theorem B8840333 : Blo 1379509 8840333 := bstep (se 3 (by rfl) ⟨1657562, by rfl⟩ : syracuseStep 8840333 = 3315125) B3315125
theorem B15721613 : Blo 1379509 15721613 := bstep (se 3 (by rfl) ⟨2947802, by rfl⟩ : syracuseStep 15721613 = 5895605) B5895605
theorem B4662413 : Blo 1379509 4662413 := bstep (se 3 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 4662413 = 1748405) B1748405
theorem B1574083 : Blo 1379509 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B4662467 : Blo 1379509 4662467 := bstep (se 1 (by rfl) ⟨3496850, by rfl⟩ : syracuseStep 4662467 = 6993701) B6993701
theorem B3106097 : Blo 1379509 3106097 := bstep (se 2 (by rfl) ⟨1164786, by rfl⟩ : syracuseStep 3106097 = 2329573) B2329573
theorem B3106115 : Blo 1379509 3106115 := bstep (se 1 (by rfl) ⟨2329586, by rfl⟩ : syracuseStep 3106115 = 4659173) B4659173
theorem B8848739 : Blo 1379509 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B2327953 : Blo 1379509 2327953 := bstep (se 2 (by rfl) ⟨872982, by rfl⟩ : syracuseStep 2327953 = 1745965) B1745965
theorem B8390051 : Blo 1379509 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B2327987 : Blo 1379509 2327987 := bstep (se 1 (by rfl) ⟨1745990, by rfl⟩ : syracuseStep 2327987 = 3491981) B3491981
theorem B1746355 : Blo 1379509 1746355 := bstep (se 1 (by rfl) ⟨1309766, by rfl⟩ : syracuseStep 1746355 = 2619533) B2619533
theorem B5244365 : Blo 1379509 5244365 := bstep (se 3 (by rfl) ⟨983318, by rfl⟩ : syracuseStep 5244365 = 1966637) B1966637
theorem B15943139 : Blo 1379509 15943139 := bstep (se 1 (by rfl) ⟨11957354, by rfl⟩ : syracuseStep 15943139 = 23914709) B23914709
theorem B1746451 : Blo 1379509 1746451 := bstep (se 1 (by rfl) ⟨1309838, by rfl⟩ : syracuseStep 1746451 = 2619677) B2619677
theorem B2328115 : Blo 1379509 2328115 := bstep (se 1 (by rfl) ⟨1746086, by rfl⟩ : syracuseStep 2328115 = 3492173) B3492173
theorem B4425293 : Blo 1379509 4425293 := bstep (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) B1659485
theorem B3106385 : Blo 1379509 3106385 := bstep (se 2 (by rfl) ⟨1164894, by rfl⟩ : syracuseStep 3106385 = 2329789) B2329789
theorem B3106403 : Blo 1379509 3106403 := bstep (se 1 (by rfl) ⟨2329802, by rfl⟩ : syracuseStep 3106403 = 4659605) B4659605
theorem B6989489 : Blo 1379509 6989489 := bstep (se 2 (by rfl) ⟨2621058, by rfl⟩ : syracuseStep 6989489 = 5242117) B5242117
theorem B2328257 : Blo 1379509 2328257 := bstep (se 2 (by rfl) ⟨873096, by rfl⟩ : syracuseStep 2328257 = 1746193) B1746193
theorem B2328385 : Blo 1379509 2328385 := bstep (se 2 (by rfl) ⟨873144, by rfl⟩ : syracuseStep 2328385 = 1746289) B1746289
theorem B8963909 : Blo 1379509 8963909 := bstep (se 4 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 8963909 = 1680733) B1680733
theorem B2656081 : Blo 1379509 2656081 := bstep (se 2 (by rfl) ⟨996030, by rfl⟩ : syracuseStep 2656081 = 1992061) B1992061
theorem B2328419 : Blo 1379509 2328419 := bstep (se 1 (by rfl) ⟨1746314, by rfl⟩ : syracuseStep 2328419 = 3492629) B3492629
theorem B3106673 : Blo 1379509 3106673 := bstep (se 2 (by rfl) ⟨1165002, by rfl⟩ : syracuseStep 3106673 = 2330005) B2330005
theorem B3106691 : Blo 1379509 3106691 := bstep (se 1 (by rfl) ⟨2330018, by rfl⟩ : syracuseStep 3106691 = 4660037) B4660037
theorem B3360707 : Blo 1379509 3360707 := bstep (se 1 (by rfl) ⟨2520530, by rfl⟩ : syracuseStep 3360707 = 5041061) B5041061
theorem B2328547 : Blo 1379509 2328547 := bstep (se 1 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 2328547 = 3492821) B3492821
theorem B1746947 : Blo 1379509 1746947 := bstep (se 1 (by rfl) ⟨1310210, by rfl⟩ : syracuseStep 1746947 = 2620421) B2620421
theorem B2328689 : Blo 1379509 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B3106961 : Blo 1379509 3106961 := bstep (se 2 (by rfl) ⟨1165110, by rfl⟩ : syracuseStep 3106961 = 2330221) B2330221
theorem B3106979 : Blo 1379509 3106979 := bstep (se 1 (by rfl) ⟨2330234, by rfl⟩ : syracuseStep 3106979 = 4660469) B4660469
theorem B6629617 : Blo 1379509 6629617 := bstep (se 2 (by rfl) ⟨2486106, by rfl⟩ : syracuseStep 6629617 = 4972213) B4972213
theorem B2328817 : Blo 1379509 2328817 := bstep (se 2 (by rfl) ⟨873306, by rfl⟩ : syracuseStep 2328817 = 1746613) B1746613
theorem B2099459 : Blo 1379509 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B2328851 : Blo 1379509 2328851 := bstep (se 1 (by rfl) ⟨1746638, by rfl⟩ : syracuseStep 2328851 = 3493277) B3493277
theorem B2328979 : Blo 1379509 2328979 := bstep (se 1 (by rfl) ⟨1746734, by rfl⟩ : syracuseStep 2328979 = 3493469) B3493469
theorem B3107249 : Blo 1379509 3107249 := bstep (se 2 (by rfl) ⟨1165218, by rfl⟩ : syracuseStep 3107249 = 2330437) B2330437
theorem B3107267 : Blo 1379509 3107267 := bstep (se 1 (by rfl) ⟨2330450, by rfl⟩ : syracuseStep 3107267 = 4660901) B4660901
theorem B9439685 : Blo 1379509 9439685 := bstep (se 4 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 9439685 = 1769941) B1769941
theorem B7866821 : Blo 1379509 7866821 := bstep (se 4 (by rfl) ⟨737514, by rfl⟩ : syracuseStep 7866821 = 1475029) B1475029
theorem B3492305 : Blo 1379509 3492305 := bstep (se 2 (by rfl) ⟨1309614, by rfl⟩ : syracuseStep 3492305 = 2619229) B2619229
theorem B13273571 : Blo 1379509 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B3492355 : Blo 1379509 3492355 := bstep (se 1 (by rfl) ⟨2619266, by rfl⟩ : syracuseStep 3492355 = 5238533) B5238533
theorem B2329121 : Blo 1379509 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B8849969 : Blo 1379509 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B26528309 : Blo 1379509 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B3492497 : Blo 1379509 3492497 := bstep (se 2 (by rfl) ⟨1309686, by rfl⟩ : syracuseStep 3492497 = 2619373) B2619373
theorem B2329249 : Blo 1379509 2329249 := bstep (se 2 (by rfl) ⟨873468, by rfl⟩ : syracuseStep 2329249 = 1746937) B1746937
theorem B4197059 : Blo 1379509 4197059 := bstep (se 1 (by rfl) ⟨3147794, by rfl⟩ : syracuseStep 4197059 = 6295589) B6295589
theorem B2329283 : Blo 1379509 2329283 := bstep (se 1 (by rfl) ⟨1746962, by rfl⟩ : syracuseStep 2329283 = 3493925) B3493925
theorem B1747651 : Blo 1379509 1747651 := bstep (se 1 (by rfl) ⟨1310738, by rfl⟩ : syracuseStep 1747651 = 2621477) B2621477
theorem B5901005 : Blo 1379509 5901005 := bstep (se 3 (by rfl) ⟨1106438, by rfl⟩ : syracuseStep 5901005 = 2212877) B2212877
theorem B3107537 : Blo 1379509 3107537 := bstep (se 2 (by rfl) ⟨1165326, by rfl⟩ : syracuseStep 3107537 = 2330653) B2330653
theorem B3107555 : Blo 1379509 3107555 := bstep (se 1 (by rfl) ⟨2330666, by rfl⟩ : syracuseStep 3107555 = 4661333) B4661333
theorem B1747747 : Blo 1379509 1747747 := bstep (se 1 (by rfl) ⟨1310810, by rfl⟩ : syracuseStep 1747747 = 2621621) B2621621
theorem B2329411 : Blo 1379509 2329411 := bstep (se 1 (by rfl) ⟨1747058, by rfl⟩ : syracuseStep 2329411 = 3494117) B3494117
theorem B7867277 : Blo 1379509 7867277 := bstep (se 3 (by rfl) ⟨1475114, by rfl⟩ : syracuseStep 7867277 = 2950229) B2950229
theorem B2329553 : Blo 1379509 2329553 := bstep (se 2 (by rfl) ⟨873582, by rfl⟩ : syracuseStep 2329553 = 1747165) B1747165
theorem B3107825 : Blo 1379509 3107825 := bstep (se 2 (by rfl) ⟨1165434, by rfl⟩ : syracuseStep 3107825 = 2330869) B2330869
theorem B3107843 : Blo 1379509 3107843 := bstep (se 1 (by rfl) ⟨2330882, by rfl⟩ : syracuseStep 3107843 = 4661765) B4661765
theorem B7859213 : Blo 1379509 7859213 := bstep (se 3 (by rfl) ⟨1473602, by rfl⟩ : syracuseStep 7859213 = 2947205) B2947205
theorem B2329681 : Blo 1379509 2329681 := bstep (se 2 (by rfl) ⟨873630, by rfl⟩ : syracuseStep 2329681 = 1747261) B1747261
theorem B6990947 : Blo 1379509 6990947 := bstep (se 1 (by rfl) ⟨5243210, by rfl⟩ : syracuseStep 6990947 = 10486421) B10486421
theorem B2329715 : Blo 1379509 2329715 := bstep (se 1 (by rfl) ⟨1747286, by rfl⟩ : syracuseStep 2329715 = 3494573) B3494573
theorem B1379523 : Blo 1379509 1379523 := bstep (se 1 (by rfl) ⟨1034642, by rfl⟩ : syracuseStep 1379523 = 2069285) B2069285
theorem B1379539 : Blo 1379509 1379539 := bstep (se 1 (by rfl) ⟨1034654, by rfl⟩ : syracuseStep 1379539 = 2069309) B2069309
theorem B1379555 : Blo 1379509 1379555 := bstep (se 1 (by rfl) ⟨1034666, by rfl⟩ : syracuseStep 1379555 = 2069333) B2069333
theorem B4656365 : Blo 1379509 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B1379571 : Blo 1379509 1379571 := bstep (se 1 (by rfl) ⟨1034678, by rfl⟩ : syracuseStep 1379571 = 2069357) B2069357
theorem B2329843 : Blo 1379509 2329843 := bstep (se 1 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 2329843 = 3494765) B3494765
theorem B1379587 : Blo 1379509 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B3108113 : Blo 1379509 3108113 := bstep (se 2 (by rfl) ⟨1165542, by rfl⟩ : syracuseStep 3108113 = 2331085) B2331085
theorem B1379603 : Blo 1379509 1379603 := bstep (se 1 (by rfl) ⟨1034702, by rfl⟩ : syracuseStep 1379603 = 2069405) B2069405
theorem B1748243 : Blo 1379509 1748243 := bstep (se 1 (by rfl) ⟨1311182, by rfl⟩ : syracuseStep 1748243 = 2622365) B2622365
theorem B1379619 : Blo 1379509 1379619 := bstep (se 1 (by rfl) ⟨1034714, by rfl⟩ : syracuseStep 1379619 = 2069429) B2069429
theorem B4656419 : Blo 1379509 4656419 := bstep (se 1 (by rfl) ⟨3492314, by rfl⟩ : syracuseStep 4656419 = 6984629) B6984629
theorem B3108131 : Blo 1379509 3108131 := bstep (se 1 (by rfl) ⟨2331098, by rfl⟩ : syracuseStep 3108131 = 4662197) B4662197
theorem B5041457 : Blo 1379509 5041457 := bstep (se 2 (by rfl) ⟨1890546, by rfl⟩ : syracuseStep 5041457 = 3781093) B3781093
theorem B2100529 : Blo 1379509 2100529 := bstep (se 2 (by rfl) ⟨787698, by rfl⟩ : syracuseStep 2100529 = 1575397) B1575397
theorem B1379635 : Blo 1379509 1379635 := bstep (se 1 (by rfl) ⟨1034726, by rfl⟩ : syracuseStep 1379635 = 2069453) B2069453
theorem B29871413 : Blo 1379509 29871413 := bstep (se 5 (by rfl) ⟨1400222, by rfl⟩ : syracuseStep 29871413 = 2800445) B2800445
theorem B1379651 : Blo 1379509 1379651 := bstep (se 1 (by rfl) ⟨1034738, by rfl⟩ : syracuseStep 1379651 = 2069477) B2069477
theorem B9956677 : Blo 1379509 9956677 := bstep (se 4 (by rfl) ⟨933438, by rfl⟩ : syracuseStep 9956677 = 1866877) B1866877
theorem B1379667 : Blo 1379509 1379667 := bstep (se 1 (by rfl) ⟨1034750, by rfl⟩ : syracuseStep 1379667 = 2069501) B2069501
theorem B1379683 : Blo 1379509 1379683 := bstep (se 1 (by rfl) ⟨1034762, by rfl⟩ : syracuseStep 1379683 = 2069525) B2069525
theorem B17493347 : Blo 1379509 17493347 := bstep (se 1 (by rfl) ⟨13120010, by rfl⟩ : syracuseStep 17493347 = 26240021) B26240021
theorem B1379699 : Blo 1379509 1379699 := bstep (se 1 (by rfl) ⟨1034774, by rfl⟩ : syracuseStep 1379699 = 2069549) B2069549
theorem B2329985 : Blo 1379509 2329985 := bstep (se 2 (by rfl) ⟨873744, by rfl⟩ : syracuseStep 2329985 = 1747489) B1747489
theorem B1379715 : Blo 1379509 1379715 := bstep (se 1 (by rfl) ⟨1034786, by rfl⟩ : syracuseStep 1379715 = 2069573) B2069573
theorem B11791757 : Blo 1379509 11791757 := bstep (se 3 (by rfl) ⟨2210954, by rfl⟩ : syracuseStep 11791757 = 4421909) B4421909
theorem B1379731 : Blo 1379509 1379731 := bstep (se 1 (by rfl) ⟨1034798, by rfl⟩ : syracuseStep 1379731 = 2069597) B2069597
theorem B1379747 : Blo 1379509 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B1379763 : Blo 1379509 1379763 := bstep (se 1 (by rfl) ⟨1034822, by rfl⟩ : syracuseStep 1379763 = 2069645) B2069645
theorem B1379779 : Blo 1379509 1379779 := bstep (se 1 (by rfl) ⟨1034834, by rfl⟩ : syracuseStep 1379779 = 2069669) B2069669
theorem B15715781 : Blo 1379509 15715781 := bstep (se 4 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 15715781 = 2946709) B2946709
theorem B1379795 : Blo 1379509 1379795 := bstep (se 1 (by rfl) ⟨1034846, by rfl⟩ : syracuseStep 1379795 = 2069693) B2069693
theorem B1379811 : Blo 1379509 1379811 := bstep (se 1 (by rfl) ⟨1034858, by rfl⟩ : syracuseStep 1379811 = 2069717) B2069717
theorem B1379827 : Blo 1379509 1379827 := bstep (se 1 (by rfl) ⟨1034870, by rfl⟩ : syracuseStep 1379827 = 2069741) B2069741
theorem B1379843 : Blo 1379509 1379843 := bstep (se 1 (by rfl) ⟨1034882, by rfl⟩ : syracuseStep 1379843 = 2069765) B2069765
theorem B2330113 : Blo 1379509 2330113 := bstep (se 2 (by rfl) ⟨873792, by rfl⟩ : syracuseStep 2330113 = 1747585) B1747585
theorem B1379859 : Blo 1379509 1379859 := bstep (se 1 (by rfl) ⟨1034894, by rfl⟩ : syracuseStep 1379859 = 2069789) B2069789
theorem B1379875 : Blo 1379509 1379875 := bstep (se 1 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 1379875 = 2069813) B2069813
theorem B2330147 : Blo 1379509 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B4656689 : Blo 1379509 4656689 := bstep (se 2 (by rfl) ⟨1746258, by rfl⟩ : syracuseStep 4656689 = 3492517) B3492517
theorem B1379891 : Blo 1379509 1379891 := bstep (se 1 (by rfl) ⟨1034918, by rfl⟩ : syracuseStep 1379891 = 2069837) B2069837
theorem B1379907 : Blo 1379509 1379907 := bstep (se 1 (by rfl) ⟨1034930, by rfl⟩ : syracuseStep 1379907 = 2069861) B2069861
theorem B1551955 : Blo 1379509 1551955 := bstep (se 1 (by rfl) ⟨1163966, by rfl⟩ : syracuseStep 1551955 = 2327933) B2327933
theorem B1379923 : Blo 1379509 1379923 := bstep (se 1 (by rfl) ⟨1034942, by rfl⟩ : syracuseStep 1379923 = 2069885) B2069885
theorem B1379939 : Blo 1379509 1379939 := bstep (se 1 (by rfl) ⟨1034954, by rfl⟩ : syracuseStep 1379939 = 2069909) B2069909
theorem B3493489 : Blo 1379509 3493489 := bstep (se 2 (by rfl) ⟨1310058, by rfl⟩ : syracuseStep 3493489 = 2620117) B2620117
theorem B1379955 : Blo 1379509 1379955 := bstep (se 1 (by rfl) ⟨1034966, by rfl⟩ : syracuseStep 1379955 = 2069933) B2069933
theorem B1379971 : Blo 1379509 1379971 := bstep (se 1 (by rfl) ⟨1034978, by rfl⟩ : syracuseStep 1379971 = 2069957) B2069957
theorem B1379987 : Blo 1379509 1379987 := bstep (se 1 (by rfl) ⟨1034990, by rfl⟩ : syracuseStep 1379987 = 2069981) B2069981
theorem B1380003 : Blo 1379509 1380003 := bstep (se 1 (by rfl) ⟨1035002, by rfl⟩ : syracuseStep 1380003 = 2070005) B2070005
theorem B2330275 : Blo 1379509 2330275 := bstep (se 1 (by rfl) ⟨1747706, by rfl⟩ : syracuseStep 2330275 = 3495413) B3495413
theorem B1380019 : Blo 1379509 1380019 := bstep (se 1 (by rfl) ⟨1035014, by rfl⟩ : syracuseStep 1380019 = 2070029) B2070029
theorem B1380035 : Blo 1379509 1380035 := bstep (se 1 (by rfl) ⟨1035026, by rfl⟩ : syracuseStep 1380035 = 2070053) B2070053
theorem B1380051 : Blo 1379509 1380051 := bstep (se 1 (by rfl) ⟨1035038, by rfl⟩ : syracuseStep 1380051 = 2070077) B2070077
theorem B1552099 : Blo 1379509 1552099 := bstep (se 1 (by rfl) ⟨1164074, by rfl⟩ : syracuseStep 1552099 = 2328149) B2328149
theorem B9440995 : Blo 1379509 9440995 := bstep (se 1 (by rfl) ⟨7080746, by rfl⟩ : syracuseStep 9440995 = 14161493) B14161493
theorem B1380067 : Blo 1379509 1380067 := bstep (se 1 (by rfl) ⟨1035050, by rfl⟩ : syracuseStep 1380067 = 2070101) B2070101
theorem B1380083 : Blo 1379509 1380083 := bstep (se 1 (by rfl) ⟨1035062, by rfl⟩ : syracuseStep 1380083 = 2070125) B2070125
theorem B1380099 : Blo 1379509 1380099 := bstep (se 1 (by rfl) ⟨1035074, by rfl⟩ : syracuseStep 1380099 = 2070149) B2070149
theorem B1380115 : Blo 1379509 1380115 := bstep (se 1 (by rfl) ⟨1035086, by rfl⟩ : syracuseStep 1380115 = 2070173) B2070173
theorem B1380131 : Blo 1379509 1380131 := bstep (se 1 (by rfl) ⟨1035098, by rfl⟩ : syracuseStep 1380131 = 2070197) B2070197
theorem B1658659 : Blo 1379509 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B2330417 : Blo 1379509 2330417 := bstep (se 2 (by rfl) ⟨873906, by rfl⟩ : syracuseStep 2330417 = 1747813) B1747813
theorem B1380147 : Blo 1379509 1380147 := bstep (se 1 (by rfl) ⟨1035110, by rfl⟩ : syracuseStep 1380147 = 2070221) B2070221
theorem B1380163 : Blo 1379509 1380163 := bstep (se 1 (by rfl) ⟨1035122, by rfl⟩ : syracuseStep 1380163 = 2070245) B2070245
theorem B1380179 : Blo 1379509 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B1380195 : Blo 1379509 1380195 := bstep (se 1 (by rfl) ⟨1035146, by rfl⟩ : syracuseStep 1380195 = 2070293) B2070293
theorem B1552243 : Blo 1379509 1552243 := bstep (se 1 (by rfl) ⟨1164182, by rfl⟩ : syracuseStep 1552243 = 2328365) B2328365
theorem B1380211 : Blo 1379509 1380211 := bstep (se 1 (by rfl) ⟨1035158, by rfl⟩ : syracuseStep 1380211 = 2070317) B2070317
theorem B1380227 : Blo 1379509 1380227 := bstep (se 1 (by rfl) ⟨1035170, by rfl⟩ : syracuseStep 1380227 = 2070341) B2070341
theorem B3493763 : Blo 1379509 3493763 := bstep (se 1 (by rfl) ⟨2620322, by rfl⟩ : syracuseStep 3493763 = 5240645) B5240645
theorem B6991757 : Blo 1379509 6991757 := bstep (se 3 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 6991757 = 2621909) B2621909
theorem B1380243 : Blo 1379509 1380243 := bstep (se 1 (by rfl) ⟨1035182, by rfl⟩ : syracuseStep 1380243 = 2070365) B2070365
theorem B1380259 : Blo 1379509 1380259 := bstep (se 1 (by rfl) ⟨1035194, by rfl⟩ : syracuseStep 1380259 = 2070389) B2070389
theorem B2330545 : Blo 1379509 2330545 := bstep (se 2 (by rfl) ⟨873954, by rfl⟩ : syracuseStep 2330545 = 1747909) B1747909
theorem B1380275 : Blo 1379509 1380275 := bstep (se 1 (by rfl) ⟨1035206, by rfl⟩ : syracuseStep 1380275 = 2070413) B2070413
theorem B1380291 : Blo 1379509 1380291 := bstep (se 1 (by rfl) ⟨1035218, by rfl⟩ : syracuseStep 1380291 = 2070437) B2070437
theorem B1380307 : Blo 1379509 1380307 := bstep (se 1 (by rfl) ⟨1035230, by rfl⟩ : syracuseStep 1380307 = 2070461) B2070461
theorem B2330579 : Blo 1379509 2330579 := bstep (se 1 (by rfl) ⟨1747934, by rfl⟩ : syracuseStep 2330579 = 3495869) B3495869
theorem B1380323 : Blo 1379509 1380323 := bstep (se 1 (by rfl) ⟨1035242, by rfl⟩ : syracuseStep 1380323 = 2070485) B2070485
theorem B15724529 : Blo 1379509 15724529 := bstep (se 2 (by rfl) ⟨5896698, by rfl⟩ : syracuseStep 15724529 = 11793397) B11793397
theorem B1380339 : Blo 1379509 1380339 := bstep (se 1 (by rfl) ⟨1035254, by rfl⟩ : syracuseStep 1380339 = 2070509) B2070509
theorem B1552387 : Blo 1379509 1552387 := bstep (se 1 (by rfl) ⟨1164290, by rfl⟩ : syracuseStep 1552387 = 2328581) B2328581
theorem B1380355 : Blo 1379509 1380355 := bstep (se 1 (by rfl) ⟨1035266, by rfl⟩ : syracuseStep 1380355 = 2070533) B2070533
theorem B1380371 : Blo 1379509 1380371 := bstep (se 1 (by rfl) ⟨1035278, by rfl⟩ : syracuseStep 1380371 = 2070557) B2070557
theorem B1380387 : Blo 1379509 1380387 := bstep (se 1 (by rfl) ⟨1035290, by rfl⟩ : syracuseStep 1380387 = 2070581) B2070581
theorem B1380403 : Blo 1379509 1380403 := bstep (se 1 (by rfl) ⟨1035302, by rfl⟩ : syracuseStep 1380403 = 2070605) B2070605
theorem B3493955 : Blo 1379509 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B1380419 : Blo 1379509 1380419 := bstep (se 1 (by rfl) ⟨1035314, by rfl⟩ : syracuseStep 1380419 = 2070629) B2070629
theorem B4255811 : Blo 1379509 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B1658947 : Blo 1379509 1658947 := bstep (se 1 (by rfl) ⟨1244210, by rfl⟩ : syracuseStep 1658947 = 2488421) B2488421
theorem B4657229 : Blo 1379509 4657229 := bstep (se 3 (by rfl) ⟨873230, by rfl⟩ : syracuseStep 4657229 = 1746461) B1746461
theorem B1380435 : Blo 1379509 1380435 := bstep (se 1 (by rfl) ⟨1035326, by rfl⟩ : syracuseStep 1380435 = 2070653) B2070653
theorem B2330707 : Blo 1379509 2330707 := bstep (se 1 (by rfl) ⟨1748030, by rfl⟩ : syracuseStep 2330707 = 3496061) B3496061
theorem B1380451 : Blo 1379509 1380451 := bstep (se 1 (by rfl) ⟨1035338, by rfl⟩ : syracuseStep 1380451 = 2070677) B2070677
theorem B15544433 : Blo 1379509 15544433 := bstep (se 2 (by rfl) ⟨5829162, by rfl⟩ : syracuseStep 15544433 = 11658325) B11658325
theorem B1380467 : Blo 1379509 1380467 := bstep (se 1 (by rfl) ⟨1035350, by rfl⟩ : syracuseStep 1380467 = 2070701) B2070701
theorem B4657283 : Blo 1379509 4657283 := bstep (se 1 (by rfl) ⟨3492962, by rfl⟩ : syracuseStep 4657283 = 6985925) B6985925
theorem B1380483 : Blo 1379509 1380483 := bstep (se 1 (by rfl) ⟨1035362, by rfl⟩ : syracuseStep 1380483 = 2070725) B2070725
theorem B1552531 : Blo 1379509 1552531 := bstep (se 1 (by rfl) ⟨1164398, by rfl⟩ : syracuseStep 1552531 = 2328797) B2328797
theorem B1380499 : Blo 1379509 1380499 := bstep (se 1 (by rfl) ⟨1035374, by rfl⟩ : syracuseStep 1380499 = 2070749) B2070749
theorem B1380515 : Blo 1379509 1380515 := bstep (se 1 (by rfl) ⟨1035386, by rfl⟩ : syracuseStep 1380515 = 2070773) B2070773
theorem B1659043 : Blo 1379509 1659043 := bstep (se 1 (by rfl) ⟨1244282, by rfl⟩ : syracuseStep 1659043 = 2488565) B2488565
theorem B4788397 : Blo 1379509 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B1380531 : Blo 1379509 1380531 := bstep (se 1 (by rfl) ⟨1035398, by rfl⟩ : syracuseStep 1380531 = 2070797) B2070797
theorem B1380547 : Blo 1379509 1380547 := bstep (se 1 (by rfl) ⟨1035410, by rfl⟩ : syracuseStep 1380547 = 2070821) B2070821
theorem B5238989 : Blo 1379509 5238989 := bstep (se 3 (by rfl) ⟨982310, by rfl⟩ : syracuseStep 5238989 = 1964621) B1964621
theorem B1380563 : Blo 1379509 1380563 := bstep (se 1 (by rfl) ⟨1035422, by rfl⟩ : syracuseStep 1380563 = 2070845) B2070845
theorem B2330849 : Blo 1379509 2330849 := bstep (se 2 (by rfl) ⟨874068, by rfl⟩ : syracuseStep 2330849 = 1748137) B1748137
theorem B1380579 : Blo 1379509 1380579 := bstep (se 1 (by rfl) ⟨1035434, by rfl⟩ : syracuseStep 1380579 = 2070869) B2070869
theorem B1380595 : Blo 1379509 1380595 := bstep (se 1 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 1380595 = 2070893) B2070893
theorem B1380611 : Blo 1379509 1380611 := bstep (se 1 (by rfl) ⟨1035458, by rfl⟩ : syracuseStep 1380611 = 2070917) B2070917
theorem B1380627 : Blo 1379509 1380627 := bstep (se 1 (by rfl) ⟨1035470, by rfl⟩ : syracuseStep 1380627 = 2070941) B2070941
theorem B1552675 : Blo 1379509 1552675 := bstep (se 1 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 1552675 = 2329013) B2329013
theorem B1380643 : Blo 1379509 1380643 := bstep (se 1 (by rfl) ⟨1035482, by rfl⟩ : syracuseStep 1380643 = 2070965) B2070965
theorem B1380659 : Blo 1379509 1380659 := bstep (se 1 (by rfl) ⟨1035494, by rfl⟩ : syracuseStep 1380659 = 2070989) B2070989
theorem B1659187 : Blo 1379509 1659187 := bstep (se 1 (by rfl) ⟨1244390, by rfl⟩ : syracuseStep 1659187 = 2488781) B2488781
theorem B1380675 : Blo 1379509 1380675 := bstep (se 1 (by rfl) ⟨1035506, by rfl⟩ : syracuseStep 1380675 = 2071013) B2071013
theorem B1380691 : Blo 1379509 1380691 := bstep (se 1 (by rfl) ⟨1035518, by rfl⟩ : syracuseStep 1380691 = 2071037) B2071037
theorem B2330977 : Blo 1379509 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B1380707 : Blo 1379509 1380707 := bstep (se 1 (by rfl) ⟨1035530, by rfl⟩ : syracuseStep 1380707 = 2071061) B2071061
theorem B18903395 : Blo 1379509 18903395 := bstep (se 1 (by rfl) ⟨14177546, by rfl⟩ : syracuseStep 18903395 = 28355093) B28355093
theorem B1380723 : Blo 1379509 1380723 := bstep (se 1 (by rfl) ⟨1035542, by rfl⟩ : syracuseStep 1380723 = 2071085) B2071085
theorem B1380739 : Blo 1379509 1380739 := bstep (se 1 (by rfl) ⟨1035554, by rfl⟩ : syracuseStep 1380739 = 2071109) B2071109
theorem B2331011 : Blo 1379509 2331011 := bstep (se 1 (by rfl) ⟨1748258, by rfl⟩ : syracuseStep 2331011 = 3496517) B3496517
theorem B4657553 : Blo 1379509 4657553 := bstep (se 2 (by rfl) ⟨1746582, by rfl⟩ : syracuseStep 4657553 = 3493165) B3493165
theorem B1380755 : Blo 1379509 1380755 := bstep (se 1 (by rfl) ⟨1035566, by rfl⟩ : syracuseStep 1380755 = 2071133) B2071133
theorem B1380771 : Blo 1379509 1380771 := bstep (se 1 (by rfl) ⟨1035578, by rfl⟩ : syracuseStep 1380771 = 2071157) B2071157
theorem B1552819 : Blo 1379509 1552819 := bstep (se 1 (by rfl) ⟨1164614, by rfl⟩ : syracuseStep 1552819 = 2329229) B2329229
theorem B1380787 : Blo 1379509 1380787 := bstep (se 1 (by rfl) ⟨1035590, by rfl⟩ : syracuseStep 1380787 = 2071181) B2071181
theorem B1380803 : Blo 1379509 1380803 := bstep (se 1 (by rfl) ⟨1035602, by rfl⟩ : syracuseStep 1380803 = 2071205) B2071205
theorem B10490309 : Blo 1379509 10490309 := bstep (se 4 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 10490309 = 1966933) B1966933
theorem B8393165 : Blo 1379509 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B1380819 : Blo 1379509 1380819 := bstep (se 1 (by rfl) ⟨1035614, by rfl⟩ : syracuseStep 1380819 = 2071229) B2071229
theorem B1380835 : Blo 1379509 1380835 := bstep (se 1 (by rfl) ⟨1035626, by rfl⟩ : syracuseStep 1380835 = 2071253) B2071253
theorem B1380851 : Blo 1379509 1380851 := bstep (se 1 (by rfl) ⟨1035638, by rfl⟩ : syracuseStep 1380851 = 2071277) B2071277
theorem B1380867 : Blo 1379509 1380867 := bstep (se 1 (by rfl) ⟨1035650, by rfl⟩ : syracuseStep 1380867 = 2071301) B2071301
theorem B2331139 : Blo 1379509 2331139 := bstep (se 1 (by rfl) ⟨1748354, by rfl⟩ : syracuseStep 2331139 = 3496709) B3496709
theorem B1380883 : Blo 1379509 1380883 := bstep (se 1 (by rfl) ⟨1035662, by rfl⟩ : syracuseStep 1380883 = 2071325) B2071325
theorem B1380899 : Blo 1379509 1380899 := bstep (se 1 (by rfl) ⟨1035674, by rfl⟩ : syracuseStep 1380899 = 2071349) B2071349
theorem B9581105 : Blo 1379509 9581105 := bstep (se 2 (by rfl) ⟨3592914, by rfl⟩ : syracuseStep 9581105 = 7185829) B7185829
theorem B1380915 : Blo 1379509 1380915 := bstep (se 1 (by rfl) ⟨1035686, by rfl⟩ : syracuseStep 1380915 = 2071373) B2071373
theorem B15340085 : Blo 1379509 15340085 := bstep (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) B1438133
theorem B1552963 : Blo 1379509 1552963 := bstep (se 1 (by rfl) ⟨1164722, by rfl⟩ : syracuseStep 1552963 = 2329445) B2329445
theorem B1380931 : Blo 1379509 1380931 := bstep (se 1 (by rfl) ⟨1035698, by rfl⟩ : syracuseStep 1380931 = 2071397) B2071397
theorem B1380947 : Blo 1379509 1380947 := bstep (se 1 (by rfl) ⟨1035710, by rfl⟩ : syracuseStep 1380947 = 2071421) B2071421
theorem B1380963 : Blo 1379509 1380963 := bstep (se 1 (by rfl) ⟨1035722, by rfl⟩ : syracuseStep 1380963 = 2071445) B2071445
theorem B6984305 : Blo 1379509 6984305 := bstep (se 2 (by rfl) ⟨2619114, by rfl⟩ : syracuseStep 6984305 = 5238229) B5238229
theorem B1380979 : Blo 1379509 1380979 := bstep (se 1 (by rfl) ⟨1035734, by rfl⟩ : syracuseStep 1380979 = 2071469) B2071469
theorem B1380995 : Blo 1379509 1380995 := bstep (se 1 (by rfl) ⟨1035746, by rfl⟩ : syracuseStep 1380995 = 2071493) B2071493
theorem B2331281 : Blo 1379509 2331281 := bstep (se 2 (by rfl) ⟨874230, by rfl⟩ : syracuseStep 2331281 = 1748461) B1748461
theorem B1381011 : Blo 1379509 1381011 := bstep (se 1 (by rfl) ⟨1035758, by rfl⟩ : syracuseStep 1381011 = 2071517) B2071517
theorem B1381027 : Blo 1379509 1381027 := bstep (se 1 (by rfl) ⟨1035770, by rfl⟩ : syracuseStep 1381027 = 2071541) B2071541
theorem B1381043 : Blo 1379509 1381043 := bstep (se 1 (by rfl) ⟨1035782, by rfl⟩ : syracuseStep 1381043 = 2071565) B2071565
theorem B1381059 : Blo 1379509 1381059 := bstep (se 1 (by rfl) ⟨1035794, by rfl⟩ : syracuseStep 1381059 = 2071589) B2071589
theorem B1553107 : Blo 1379509 1553107 := bstep (se 1 (by rfl) ⟨1164830, by rfl⟩ : syracuseStep 1553107 = 2329661) B2329661
theorem B1381075 : Blo 1379509 1381075 := bstep (se 1 (by rfl) ⟨1035806, by rfl⟩ : syracuseStep 1381075 = 2071613) B2071613
theorem B1381091 : Blo 1379509 1381091 := bstep (se 1 (by rfl) ⟨1035818, by rfl⟩ : syracuseStep 1381091 = 2071637) B2071637
theorem B1381107 : Blo 1379509 1381107 := bstep (se 1 (by rfl) ⟨1035830, by rfl⟩ : syracuseStep 1381107 = 2071661) B2071661
theorem B1381123 : Blo 1379509 1381123 := bstep (se 1 (by rfl) ⟨1035842, by rfl⟩ : syracuseStep 1381123 = 2071685) B2071685
theorem B2069267 : Blo 1379509 2069267 := bstep (se 1 (by rfl) ⟨1551950, by rfl⟩ : syracuseStep 2069267 = 3103901) B3103901
theorem B1381139 : Blo 1379509 1381139 := bstep (se 1 (by rfl) ⟨1035854, by rfl⟩ : syracuseStep 1381139 = 2071709) B2071709
theorem B1381155 : Blo 1379509 1381155 := bstep (se 1 (by rfl) ⟨1035866, by rfl⟩ : syracuseStep 1381155 = 2071733) B2071733
theorem B2069297 : Blo 1379509 2069297 := bstep (se 2 (by rfl) ⟨775986, by rfl⟩ : syracuseStep 2069297 = 1551973) B1551973
theorem B1381171 : Blo 1379509 1381171 := bstep (se 1 (by rfl) ⟨1035878, by rfl⟩ : syracuseStep 1381171 = 2071757) B2071757
theorem B2069315 : Blo 1379509 2069315 := bstep (se 1 (by rfl) ⟨1551986, by rfl⟩ : syracuseStep 2069315 = 3103973) B3103973
theorem B1381187 : Blo 1379509 1381187 := bstep (se 1 (by rfl) ⟨1035890, by rfl⟩ : syracuseStep 1381187 = 2071781) B2071781
theorem B1381203 : Blo 1379509 1381203 := bstep (se 1 (by rfl) ⟨1035902, by rfl⟩ : syracuseStep 1381203 = 2071805) B2071805
theorem B2069345 : Blo 1379509 2069345 := bstep (se 2 (by rfl) ⟨776004, by rfl⟩ : syracuseStep 2069345 = 1552009) B1552009
theorem B2798435 : Blo 1379509 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B1553251 : Blo 1379509 1553251 := bstep (se 1 (by rfl) ⟨1164938, by rfl⟩ : syracuseStep 1553251 = 2329877) B2329877
theorem B1381219 : Blo 1379509 1381219 := bstep (se 1 (by rfl) ⟨1035914, by rfl⟩ : syracuseStep 1381219 = 2071829) B2071829
theorem B2069363 : Blo 1379509 2069363 := bstep (se 1 (by rfl) ⟨1552022, by rfl⟩ : syracuseStep 2069363 = 3104045) B3104045
theorem B1381235 : Blo 1379509 1381235 := bstep (se 1 (by rfl) ⟨1035926, by rfl⟩ : syracuseStep 1381235 = 2071853) B2071853
theorem B1381251 : Blo 1379509 1381251 := bstep (se 1 (by rfl) ⟨1035938, by rfl⟩ : syracuseStep 1381251 = 2071877) B2071877
theorem B17691533 : Blo 1379509 17691533 := bstep (se 3 (by rfl) ⟨3317162, by rfl⟩ : syracuseStep 17691533 = 6634325) B6634325
theorem B2069393 : Blo 1379509 2069393 := bstep (se 2 (by rfl) ⟨776022, by rfl⟩ : syracuseStep 2069393 = 1552045) B1552045
theorem B1381267 : Blo 1379509 1381267 := bstep (se 1 (by rfl) ⟨1035950, by rfl⟩ : syracuseStep 1381267 = 2071901) B2071901
theorem B2069411 : Blo 1379509 2069411 := bstep (se 1 (by rfl) ⟨1552058, by rfl⟩ : syracuseStep 2069411 = 3104117) B3104117
theorem B1381283 : Blo 1379509 1381283 := bstep (se 1 (by rfl) ⟨1035962, by rfl⟩ : syracuseStep 1381283 = 2071925) B2071925
theorem B4658093 : Blo 1379509 4658093 := bstep (se 3 (by rfl) ⟨873392, by rfl⟩ : syracuseStep 4658093 = 1746785) B1746785
theorem B1381299 : Blo 1379509 1381299 := bstep (se 1 (by rfl) ⟨1035974, by rfl⟩ : syracuseStep 1381299 = 2071949) B2071949
theorem B2069441 : Blo 1379509 2069441 := bstep (se 2 (by rfl) ⟨776040, by rfl⟩ : syracuseStep 2069441 = 1552081) B1552081
theorem B3314627 : Blo 1379509 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B1381315 : Blo 1379509 1381315 := bstep (se 1 (by rfl) ⟨1035986, by rfl⟩ : syracuseStep 1381315 = 2071973) B2071973
theorem B2069459 : Blo 1379509 2069459 := bstep (se 1 (by rfl) ⟨1552094, by rfl⟩ : syracuseStep 2069459 = 3104189) B3104189
theorem B1381331 : Blo 1379509 1381331 := bstep (se 1 (by rfl) ⟨1035998, by rfl⟩ : syracuseStep 1381331 = 2071997) B2071997
theorem B4658147 : Blo 1379509 4658147 := bstep (se 1 (by rfl) ⟨3493610, by rfl⟩ : syracuseStep 4658147 = 6987221) B6987221
theorem B1381347 : Blo 1379509 1381347 := bstep (se 1 (by rfl) ⟨1036010, by rfl⟩ : syracuseStep 1381347 = 2072021) B2072021
theorem B2069489 : Blo 1379509 2069489 := bstep (se 2 (by rfl) ⟨776058, by rfl⟩ : syracuseStep 2069489 = 1552117) B1552117
theorem B3494897 : Blo 1379509 3494897 := bstep (se 2 (by rfl) ⟨1310586, by rfl⟩ : syracuseStep 3494897 = 2621173) B2621173
theorem B1553395 : Blo 1379509 1553395 := bstep (se 1 (by rfl) ⟨1165046, by rfl⟩ : syracuseStep 1553395 = 2330093) B2330093
theorem B1381363 : Blo 1379509 1381363 := bstep (se 1 (by rfl) ⟨1036022, by rfl⟩ : syracuseStep 1381363 = 2072045) B2072045
theorem B2069507 : Blo 1379509 2069507 := bstep (se 1 (by rfl) ⟨1552130, by rfl⟩ : syracuseStep 2069507 = 3104261) B3104261
theorem B1381379 : Blo 1379509 1381379 := bstep (se 1 (by rfl) ⟨1036034, by rfl⟩ : syracuseStep 1381379 = 2072069) B2072069
theorem B1381395 : Blo 1379509 1381395 := bstep (se 1 (by rfl) ⟨1036046, by rfl⟩ : syracuseStep 1381395 = 2072093) B2072093
theorem B2069537 : Blo 1379509 2069537 := bstep (se 2 (by rfl) ⟨776076, by rfl⟩ : syracuseStep 2069537 = 1552153) B1552153
theorem B3494947 : Blo 1379509 3494947 := bstep (se 1 (by rfl) ⟨2621210, by rfl⟩ : syracuseStep 3494947 = 5242421) B5242421
theorem B1381411 : Blo 1379509 1381411 := bstep (se 1 (by rfl) ⟨1036058, by rfl⟩ : syracuseStep 1381411 = 2072117) B2072117
theorem B2069555 : Blo 1379509 2069555 := bstep (se 1 (by rfl) ⟨1552166, by rfl⟩ : syracuseStep 2069555 = 3104333) B3104333
theorem B1381427 : Blo 1379509 1381427 := bstep (se 1 (by rfl) ⟨1036070, by rfl⟩ : syracuseStep 1381427 = 2072141) B2072141
theorem B1381443 : Blo 1379509 1381443 := bstep (se 1 (by rfl) ⟨1036082, by rfl⟩ : syracuseStep 1381443 = 2072165) B2072165
theorem B4199501 : Blo 1379509 4199501 := bstep (se 3 (by rfl) ⟨787406, by rfl⟩ : syracuseStep 4199501 = 1574813) B1574813
theorem B2069585 : Blo 1379509 2069585 := bstep (se 2 (by rfl) ⟨776094, by rfl⟩ : syracuseStep 2069585 = 1552189) B1552189
theorem B1381459 : Blo 1379509 1381459 := bstep (se 1 (by rfl) ⟨1036094, by rfl⟩ : syracuseStep 1381459 = 2072189) B2072189
theorem B1864801 : Blo 1379509 1864801 := bstep (se 2 (by rfl) ⟨699300, by rfl⟩ : syracuseStep 1864801 = 1398601) B1398601
theorem B2069603 : Blo 1379509 2069603 := bstep (se 1 (by rfl) ⟨1552202, by rfl⟩ : syracuseStep 2069603 = 3104405) B3104405
theorem B1381475 : Blo 1379509 1381475 := bstep (se 1 (by rfl) ⟨1036106, by rfl⟩ : syracuseStep 1381475 = 2072213) B2072213
theorem B1381491 : Blo 1379509 1381491 := bstep (se 1 (by rfl) ⟨1036118, by rfl⟩ : syracuseStep 1381491 = 2072237) B2072237
theorem B2069633 : Blo 1379509 2069633 := bstep (se 2 (by rfl) ⟨776112, by rfl⟩ : syracuseStep 2069633 = 1552225) B1552225
theorem B3929219 : Blo 1379509 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B1553539 : Blo 1379509 1553539 := bstep (se 1 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 1553539 = 2330309) B2330309
theorem B1381507 : Blo 1379509 1381507 := bstep (se 1 (by rfl) ⟨1036130, by rfl⟩ : syracuseStep 1381507 = 2072261) B2072261
theorem B2069651 : Blo 1379509 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B2069681 : Blo 1379509 2069681 := bstep (se 2 (by rfl) ⟨776130, by rfl⟩ : syracuseStep 2069681 = 1552261) B1552261
theorem B3495089 : Blo 1379509 3495089 := bstep (se 2 (by rfl) ⟨1310658, by rfl⟩ : syracuseStep 3495089 = 2621317) B2621317
theorem B2069699 : Blo 1379509 2069699 := bstep (se 1 (by rfl) ⟨1552274, by rfl⟩ : syracuseStep 2069699 = 3104549) B3104549
theorem B2487491 : Blo 1379509 2487491 := bstep (se 1 (by rfl) ⟨1865618, by rfl⟩ : syracuseStep 2487491 = 3731237) B3731237
theorem B7861445 : Blo 1379509 7861445 := bstep (se 4 (by rfl) ⟨737010, by rfl⟩ : syracuseStep 7861445 = 1474021) B1474021
theorem B2069729 : Blo 1379509 2069729 := bstep (se 2 (by rfl) ⟨776148, by rfl⟩ : syracuseStep 2069729 = 1552297) B1552297
theorem B3314915 : Blo 1379509 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B4658417 : Blo 1379509 4658417 := bstep (se 2 (by rfl) ⟨1746906, by rfl⟩ : syracuseStep 4658417 = 3493813) B3493813
theorem B2069747 : Blo 1379509 2069747 := bstep (se 1 (by rfl) ⟨1552310, by rfl⟩ : syracuseStep 2069747 = 3104621) B3104621
theorem B2069777 : Blo 1379509 2069777 := bstep (se 2 (by rfl) ⟨776166, by rfl⟩ : syracuseStep 2069777 = 1552333) B1552333
theorem B1553683 : Blo 1379509 1553683 := bstep (se 1 (by rfl) ⟨1165262, by rfl⟩ : syracuseStep 1553683 = 2330525) B2330525
theorem B2069795 : Blo 1379509 2069795 := bstep (se 1 (by rfl) ⟨1552346, by rfl⟩ : syracuseStep 2069795 = 3104693) B3104693
theorem B2069825 : Blo 1379509 2069825 := bstep (se 2 (by rfl) ⟨776184, by rfl⟩ : syracuseStep 2069825 = 1552369) B1552369
theorem B2946385 : Blo 1379509 2946385 := bstep (se 2 (by rfl) ⟨1104894, by rfl⟩ : syracuseStep 2946385 = 2209789) B2209789
theorem B2069843 : Blo 1379509 2069843 := bstep (se 1 (by rfl) ⟨1552382, by rfl⟩ : syracuseStep 2069843 = 3104765) B3104765
theorem B2069873 : Blo 1379509 2069873 := bstep (se 2 (by rfl) ⟨776202, by rfl⟩ : syracuseStep 2069873 = 1552405) B1552405
theorem B2069891 : Blo 1379509 2069891 := bstep (se 1 (by rfl) ⟨1552418, by rfl⟩ : syracuseStep 2069891 = 3104837) B3104837
theorem B2069921 : Blo 1379509 2069921 := bstep (se 2 (by rfl) ⟨776220, by rfl⟩ : syracuseStep 2069921 = 1552441) B1552441
theorem B1553827 : Blo 1379509 1553827 := bstep (se 1 (by rfl) ⟨1165370, by rfl⟩ : syracuseStep 1553827 = 2330741) B2330741
theorem B6387121 : Blo 1379509 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B2069939 : Blo 1379509 2069939 := bstep (se 1 (by rfl) ⟨1552454, by rfl⟩ : syracuseStep 2069939 = 3104909) B3104909
theorem B2069969 : Blo 1379509 2069969 := bstep (se 2 (by rfl) ⟨776238, by rfl⟩ : syracuseStep 2069969 = 1552477) B1552477
theorem B2069987 : Blo 1379509 2069987 := bstep (se 1 (by rfl) ⟨1552490, by rfl⟩ : syracuseStep 2069987 = 3104981) B3104981
theorem B2070017 : Blo 1379509 2070017 := bstep (se 2 (by rfl) ⟨776256, by rfl⟩ : syracuseStep 2070017 = 1552513) B1552513
theorem B2070035 : Blo 1379509 2070035 := bstep (se 1 (by rfl) ⟨1552526, by rfl⟩ : syracuseStep 2070035 = 3105053) B3105053
theorem B2070065 : Blo 1379509 2070065 := bstep (se 2 (by rfl) ⟨776274, by rfl⟩ : syracuseStep 2070065 = 1552549) B1552549
theorem B1553971 : Blo 1379509 1553971 := bstep (se 1 (by rfl) ⟨1165478, by rfl⟩ : syracuseStep 1553971 = 2330957) B2330957
theorem B2070083 : Blo 1379509 2070083 := bstep (se 1 (by rfl) ⟨1552562, by rfl⟩ : syracuseStep 2070083 = 3105125) B3105125
theorem B2070113 : Blo 1379509 2070113 := bstep (se 2 (by rfl) ⟨776292, by rfl⟩ : syracuseStep 2070113 = 1552585) B1552585
theorem B2618993 : Blo 1379509 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B2070131 : Blo 1379509 2070131 := bstep (se 1 (by rfl) ⟨1552598, by rfl⟩ : syracuseStep 2070131 = 3105197) B3105197
theorem B1398403 : Blo 1379509 1398403 := bstep (se 1 (by rfl) ⟨1048802, by rfl⟩ : syracuseStep 1398403 = 2097605) B2097605
theorem B2070161 : Blo 1379509 2070161 := bstep (se 2 (by rfl) ⟨776310, by rfl⟩ : syracuseStep 2070161 = 1552621) B1552621
theorem B2070179 : Blo 1379509 2070179 := bstep (se 1 (by rfl) ⟨1552634, by rfl⟩ : syracuseStep 2070179 = 3105269) B3105269
theorem B2070209 : Blo 1379509 2070209 := bstep (se 2 (by rfl) ⟨776328, by rfl⟩ : syracuseStep 2070209 = 1552657) B1552657
theorem B1554115 : Blo 1379509 1554115 := bstep (se 1 (by rfl) ⟨1165586, by rfl⟩ : syracuseStep 1554115 = 2331173) B2331173
theorem B2070227 : Blo 1379509 2070227 := bstep (se 1 (by rfl) ⟨1552670, by rfl⟩ : syracuseStep 2070227 = 3105341) B3105341
theorem B2070257 : Blo 1379509 2070257 := bstep (se 2 (by rfl) ⟨776346, by rfl⟩ : syracuseStep 2070257 = 1552693) B1552693
theorem B1890049 : Blo 1379509 1890049 := bstep (se 2 (by rfl) ⟨708768, by rfl⟩ : syracuseStep 1890049 = 1417537) B1417537
theorem B2070275 : Blo 1379509 2070275 := bstep (se 1 (by rfl) ⟨1552706, by rfl⟩ : syracuseStep 2070275 = 3105413) B3105413
theorem B4658957 : Blo 1379509 4658957 := bstep (se 3 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 4658957 = 1747109) B1747109
theorem B2070305 : Blo 1379509 2070305 := bstep (se 2 (by rfl) ⟨776364, by rfl⟩ : syracuseStep 2070305 = 1552729) B1552729
theorem B2070323 : Blo 1379509 2070323 := bstep (se 1 (by rfl) ⟨1552742, by rfl⟩ : syracuseStep 2070323 = 3105485) B3105485
theorem B4659011 : Blo 1379509 4659011 := bstep (se 1 (by rfl) ⟨3494258, by rfl⟩ : syracuseStep 4659011 = 6988517) B6988517
theorem B7460677 : Blo 1379509 7460677 := bstep (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) B1398877
theorem B16799557 : Blo 1379509 16799557 := bstep (se 4 (by rfl) ⟨1574958, by rfl⟩ : syracuseStep 16799557 = 3149917) B3149917
theorem B2070353 : Blo 1379509 2070353 := bstep (se 2 (by rfl) ⟨776382, by rfl⟩ : syracuseStep 2070353 = 1552765) B1552765
theorem B2070371 : Blo 1379509 2070371 := bstep (se 1 (by rfl) ⟨1552778, by rfl⟩ : syracuseStep 2070371 = 3105557) B3105557
theorem B7862129 : Blo 1379509 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B2070401 : Blo 1379509 2070401 := bstep (se 2 (by rfl) ⟨776400, by rfl⟩ : syracuseStep 2070401 = 1552801) B1552801
theorem B2070419 : Blo 1379509 2070419 := bstep (se 1 (by rfl) ⟨1552814, by rfl⟩ : syracuseStep 2070419 = 3105629) B3105629
theorem B3930029 : Blo 1379509 3930029 := bstep (se 3 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 3930029 = 1473761) B1473761
theorem B2070449 : Blo 1379509 2070449 := bstep (se 2 (by rfl) ⟨776418, by rfl⟩ : syracuseStep 2070449 = 1552837) B1552837
theorem B2070467 : Blo 1379509 2070467 := bstep (se 1 (by rfl) ⟨1552850, by rfl⟩ : syracuseStep 2070467 = 3105701) B3105701
theorem B2070497 : Blo 1379509 2070497 := bstep (se 2 (by rfl) ⟨776436, by rfl⟩ : syracuseStep 2070497 = 1552873) B1552873
theorem B2947043 : Blo 1379509 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B7460849 : Blo 1379509 7460849 := bstep (se 2 (by rfl) ⟨2797818, by rfl⟩ : syracuseStep 7460849 = 5595637) B5595637
theorem B2070515 : Blo 1379509 2070515 := bstep (se 1 (by rfl) ⟨1552886, by rfl⟩ : syracuseStep 2070515 = 3105773) B3105773
theorem B3733517 : Blo 1379509 3733517 := bstep (se 3 (by rfl) ⟨700034, by rfl⟩ : syracuseStep 3733517 = 1400069) B1400069
theorem B2070545 : Blo 1379509 2070545 := bstep (se 2 (by rfl) ⟨776454, by rfl⟩ : syracuseStep 2070545 = 1552909) B1552909
theorem B6985763 : Blo 1379509 6985763 := bstep (se 1 (by rfl) ⟨5239322, by rfl⟩ : syracuseStep 6985763 = 10478645) B10478645
theorem B2070563 : Blo 1379509 2070563 := bstep (se 1 (by rfl) ⟨1552922, by rfl⟩ : syracuseStep 2070563 = 3105845) B3105845
theorem B3315761 : Blo 1379509 3315761 := bstep (se 2 (by rfl) ⟨1243410, by rfl⟩ : syracuseStep 3315761 = 2486821) B2486821
theorem B6633521 : Blo 1379509 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B2070593 : Blo 1379509 2070593 := bstep (se 2 (by rfl) ⟨776472, by rfl⟩ : syracuseStep 2070593 = 1552945) B1552945
theorem B4659281 : Blo 1379509 4659281 := bstep (se 2 (by rfl) ⟨1747230, by rfl⟩ : syracuseStep 4659281 = 3494461) B3494461
theorem B2070611 : Blo 1379509 2070611 := bstep (se 1 (by rfl) ⟨1552958, by rfl⟩ : syracuseStep 2070611 = 3105917) B3105917
theorem B3930221 : Blo 1379509 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B10623089 : Blo 1379509 10623089 := bstep (se 2 (by rfl) ⟨3983658, by rfl⟩ : syracuseStep 10623089 = 7967317) B7967317
theorem B2070641 : Blo 1379509 2070641 := bstep (se 2 (by rfl) ⟨776490, by rfl⟩ : syracuseStep 2070641 = 1552981) B1552981
theorem B2070659 : Blo 1379509 2070659 := bstep (se 1 (by rfl) ⟨1552994, by rfl⟩ : syracuseStep 2070659 = 3105989) B3105989
theorem B3496081 : Blo 1379509 3496081 := bstep (se 2 (by rfl) ⟨1311030, by rfl⟩ : syracuseStep 3496081 = 2622061) B2622061
theorem B2070689 : Blo 1379509 2070689 := bstep (se 2 (by rfl) ⟨776508, by rfl⟩ : syracuseStep 2070689 = 1553017) B1553017
theorem B2070707 : Blo 1379509 2070707 := bstep (se 1 (by rfl) ⟨1553030, by rfl⟩ : syracuseStep 2070707 = 3106061) B3106061
theorem B1865921 : Blo 1379509 1865921 := bstep (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) B1399441
theorem B4036817 : Blo 1379509 4036817 := bstep (se 2 (by rfl) ⟨1513806, by rfl⟩ : syracuseStep 4036817 = 3027613) B3027613
theorem B2070737 : Blo 1379509 2070737 := bstep (se 2 (by rfl) ⟨776526, by rfl⟩ : syracuseStep 2070737 = 1553053) B1553053
theorem B2488529 : Blo 1379509 2488529 := bstep (se 2 (by rfl) ⟨933198, by rfl⟩ : syracuseStep 2488529 = 1866397) B1866397
theorem B2070755 : Blo 1379509 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B2070785 : Blo 1379509 2070785 := bstep (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) B1553089
theorem B2070803 : Blo 1379509 2070803 := bstep (se 1 (by rfl) ⟨1553102, by rfl⟩ : syracuseStep 2070803 = 3106205) B3106205
theorem B2070833 : Blo 1379509 2070833 := bstep (se 2 (by rfl) ⟨776562, by rfl⟩ : syracuseStep 2070833 = 1553125) B1553125
theorem B2619715 : Blo 1379509 2619715 := bstep (se 1 (by rfl) ⟨1964786, by rfl⟩ : syracuseStep 2619715 = 3929573) B3929573
theorem B2070851 : Blo 1379509 2070851 := bstep (se 1 (by rfl) ⟨1553138, by rfl⟩ : syracuseStep 2070851 = 3106277) B3106277
theorem B3316049 : Blo 1379509 3316049 := bstep (se 2 (by rfl) ⟨1243518, by rfl⟩ : syracuseStep 3316049 = 2487037) B2487037
theorem B2070881 : Blo 1379509 2070881 := bstep (se 2 (by rfl) ⟨776580, by rfl⟩ : syracuseStep 2070881 = 1553161) B1553161
theorem B5896547 : Blo 1379509 5896547 := bstep (se 1 (by rfl) ⟨4422410, by rfl⟩ : syracuseStep 5896547 = 8844821) B8844821
theorem B2210161 : Blo 1379509 2210161 := bstep (se 2 (by rfl) ⟨828810, by rfl⟩ : syracuseStep 2210161 = 1657621) B1657621
theorem B4200817 : Blo 1379509 4200817 := bstep (se 2 (by rfl) ⟨1575306, by rfl⟩ : syracuseStep 4200817 = 3150613) B3150613
theorem B2070899 : Blo 1379509 2070899 := bstep (se 1 (by rfl) ⟨1553174, by rfl⟩ : syracuseStep 2070899 = 3106349) B3106349
theorem B2070929 : Blo 1379509 2070929 := bstep (se 2 (by rfl) ⟨776598, by rfl⟩ : syracuseStep 2070929 = 1553197) B1553197
theorem B2070947 : Blo 1379509 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B3496355 : Blo 1379509 3496355 := bstep (se 1 (by rfl) ⟨2622266, by rfl⟩ : syracuseStep 3496355 = 5244533) B5244533
theorem B2070977 : Blo 1379509 2070977 := bstep (se 2 (by rfl) ⟨776616, by rfl⟩ : syracuseStep 2070977 = 1553233) B1553233
theorem B2070995 : Blo 1379509 2070995 := bstep (se 1 (by rfl) ⟨1553246, by rfl⟩ : syracuseStep 2070995 = 3106493) B3106493
theorem B1964513 : Blo 1379509 1964513 := bstep (se 2 (by rfl) ⟨736692, by rfl⟩ : syracuseStep 1964513 = 1473385) B1473385
theorem B2071025 : Blo 1379509 2071025 := bstep (se 2 (by rfl) ⟨776634, by rfl⟩ : syracuseStep 2071025 = 1553269) B1553269
theorem B2071043 : Blo 1379509 2071043 := bstep (se 1 (by rfl) ⟨1553282, by rfl⟩ : syracuseStep 2071043 = 3106565) B3106565
theorem B3316241 : Blo 1379509 3316241 := bstep (se 2 (by rfl) ⟨1243590, by rfl⟩ : syracuseStep 3316241 = 2487181) B2487181
theorem B2071073 : Blo 1379509 2071073 := bstep (se 2 (by rfl) ⟨776652, by rfl⟩ : syracuseStep 2071073 = 1553305) B1553305
theorem B2071091 : Blo 1379509 2071091 := bstep (se 1 (by rfl) ⟨1553318, by rfl⟩ : syracuseStep 2071091 = 3106637) B3106637
theorem B95648309 : Blo 1379509 95648309 := bstep (se 5 (by rfl) ⟨4483514, by rfl⟩ : syracuseStep 95648309 = 8967029) B8967029
theorem B2071121 : Blo 1379509 2071121 := bstep (se 2 (by rfl) ⟨776670, by rfl⟩ : syracuseStep 2071121 = 1553341) B1553341
theorem B16792163 : Blo 1379509 16792163 := bstep (se 1 (by rfl) ⟨12594122, by rfl⟩ : syracuseStep 16792163 = 25188245) B25188245
theorem B2071139 : Blo 1379509 2071139 := bstep (se 1 (by rfl) ⟨1553354, by rfl⟩ : syracuseStep 2071139 = 3106709) B3106709
theorem B3496547 : Blo 1379509 3496547 := bstep (se 1 (by rfl) ⟨2622410, by rfl⟩ : syracuseStep 3496547 = 5244821) B5244821
theorem B4659821 : Blo 1379509 4659821 := bstep (se 3 (by rfl) ⟨873716, by rfl⟩ : syracuseStep 4659821 = 1747433) B1747433
theorem B2210417 : Blo 1379509 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B2071169 : Blo 1379509 2071169 := bstep (se 2 (by rfl) ⟨776688, by rfl⟩ : syracuseStep 2071169 = 1553377) B1553377
theorem B2071187 : Blo 1379509 2071187 := bstep (se 1 (by rfl) ⟨1553390, by rfl⟩ : syracuseStep 2071187 = 3106781) B3106781
theorem B4659875 : Blo 1379509 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B2071217 : Blo 1379509 2071217 := bstep (se 2 (by rfl) ⟨776706, by rfl⟩ : syracuseStep 2071217 = 1553413) B1553413
theorem B2071235 : Blo 1379509 2071235 := bstep (se 1 (by rfl) ⟨1553426, by rfl⟩ : syracuseStep 2071235 = 3106853) B3106853
theorem B2071265 : Blo 1379509 2071265 := bstep (se 2 (by rfl) ⟨776724, by rfl⟩ : syracuseStep 2071265 = 1553449) B1553449
theorem B2071283 : Blo 1379509 2071283 := bstep (se 1 (by rfl) ⟨1553462, by rfl⟩ : syracuseStep 2071283 = 3106925) B3106925
theorem B2620163 : Blo 1379509 2620163 := bstep (se 1 (by rfl) ⟨1965122, by rfl⟩ : syracuseStep 2620163 = 3930245) B3930245
theorem B2071313 : Blo 1379509 2071313 := bstep (se 2 (by rfl) ⟨776742, by rfl⟩ : syracuseStep 2071313 = 1553485) B1553485
theorem B2071331 : Blo 1379509 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B2210609 : Blo 1379509 2210609 := bstep (se 2 (by rfl) ⟨828978, by rfl⟩ : syracuseStep 2210609 = 1657957) B1657957
theorem B2947889 : Blo 1379509 2947889 := bstep (se 2 (by rfl) ⟨1105458, by rfl⟩ : syracuseStep 2947889 = 2210917) B2210917
theorem B2071361 : Blo 1379509 2071361 := bstep (se 2 (by rfl) ⟨776760, by rfl⟩ : syracuseStep 2071361 = 1553521) B1553521
theorem B6986573 : Blo 1379509 6986573 := bstep (se 3 (by rfl) ⟨1309982, by rfl⟩ : syracuseStep 6986573 = 2619965) B2619965
theorem B2071379 : Blo 1379509 2071379 := bstep (se 1 (by rfl) ⟨1553534, by rfl⟩ : syracuseStep 2071379 = 3107069) B3107069
theorem B2071409 : Blo 1379509 2071409 := bstep (se 2 (by rfl) ⟨776778, by rfl⟩ : syracuseStep 2071409 = 1553557) B1553557
theorem B2071427 : Blo 1379509 2071427 := bstep (se 1 (by rfl) ⟨1553570, by rfl⟩ : syracuseStep 2071427 = 3107141) B3107141
theorem B2071457 : Blo 1379509 2071457 := bstep (se 2 (by rfl) ⟨776796, by rfl⟩ : syracuseStep 2071457 = 1553593) B1553593
theorem B4660145 : Blo 1379509 4660145 := bstep (se 2 (by rfl) ⟨1747554, by rfl⟩ : syracuseStep 4660145 = 3495109) B3495109
theorem B2071475 : Blo 1379509 2071475 := bstep (se 1 (by rfl) ⟨1553606, by rfl⟩ : syracuseStep 2071475 = 3107213) B3107213
theorem B2071505 : Blo 1379509 2071505 := bstep (se 2 (by rfl) ⟨776814, by rfl⟩ : syracuseStep 2071505 = 1553629) B1553629
theorem B2071523 : Blo 1379509 2071523 := bstep (se 1 (by rfl) ⟨1553642, by rfl⟩ : syracuseStep 2071523 = 3107285) B3107285
theorem B2071553 : Blo 1379509 2071553 := bstep (se 2 (by rfl) ⟨776832, by rfl⟩ : syracuseStep 2071553 = 1553665) B1553665
theorem B2800657 : Blo 1379509 2800657 := bstep (se 2 (by rfl) ⟨1050246, by rfl⟩ : syracuseStep 2800657 = 2100493) B2100493
theorem B2071571 : Blo 1379509 2071571 := bstep (se 1 (by rfl) ⟨1553678, by rfl⟩ : syracuseStep 2071571 = 3107357) B3107357
theorem B2620451 : Blo 1379509 2620451 := bstep (se 1 (by rfl) ⟨1965338, by rfl⟩ : syracuseStep 2620451 = 3930677) B3930677
theorem B5241905 : Blo 1379509 5241905 := bstep (se 2 (by rfl) ⟨1965714, by rfl⟩ : syracuseStep 5241905 = 3931429) B3931429
theorem B2071601 : Blo 1379509 2071601 := bstep (se 2 (by rfl) ⟨776850, by rfl⟩ : syracuseStep 2071601 = 1553701) B1553701
theorem B2071619 : Blo 1379509 2071619 := bstep (se 1 (by rfl) ⟨1553714, by rfl⟩ : syracuseStep 2071619 = 3107429) B3107429
theorem B3931213 : Blo 1379509 3931213 := bstep (se 3 (by rfl) ⟨737102, by rfl⟩ : syracuseStep 3931213 = 1474205) B1474205
theorem B2071649 : Blo 1379509 2071649 := bstep (se 2 (by rfl) ⟨776868, by rfl⟩ : syracuseStep 2071649 = 1553737) B1553737
theorem B2071667 : Blo 1379509 2071667 := bstep (se 1 (by rfl) ⟨1553750, by rfl⟩ : syracuseStep 2071667 = 3107501) B3107501
theorem B2071697 : Blo 1379509 2071697 := bstep (se 2 (by rfl) ⟨776886, by rfl⟩ : syracuseStep 2071697 = 1553773) B1553773
theorem B2071715 : Blo 1379509 2071715 := bstep (se 1 (by rfl) ⟨1553786, by rfl⟩ : syracuseStep 2071715 = 3107573) B3107573
theorem B4422833 : Blo 1379509 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B16792757 : Blo 1379509 16792757 := bstep (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) B1574321
theorem B2071745 : Blo 1379509 2071745 := bstep (se 2 (by rfl) ⟨776904, by rfl⟩ : syracuseStep 2071745 = 1553809) B1553809
theorem B2071763 : Blo 1379509 2071763 := bstep (se 1 (by rfl) ⟨1553822, by rfl⟩ : syracuseStep 2071763 = 3107645) B3107645
theorem B10484963 : Blo 1379509 10484963 := bstep (se 1 (by rfl) ⟨7863722, by rfl⟩ : syracuseStep 10484963 = 15727445) B15727445
theorem B2071793 : Blo 1379509 2071793 := bstep (se 2 (by rfl) ⟨776922, by rfl⟩ : syracuseStep 2071793 = 1553845) B1553845
theorem B2071811 : Blo 1379509 2071811 := bstep (se 1 (by rfl) ⟨1553858, by rfl⟩ : syracuseStep 2071811 = 3107717) B3107717
theorem B2071841 : Blo 1379509 2071841 := bstep (se 2 (by rfl) ⟨776940, by rfl⟩ : syracuseStep 2071841 = 1553881) B1553881
theorem B7863587 : Blo 1379509 7863587 := bstep (se 1 (by rfl) ⟨5897690, by rfl⟩ : syracuseStep 7863587 = 11795381) B11795381
theorem B2071859 : Blo 1379509 2071859 := bstep (se 1 (by rfl) ⟨1553894, by rfl⟩ : syracuseStep 2071859 = 3107789) B3107789
theorem B1965379 : Blo 1379509 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B3104081 : Blo 1379509 3104081 := bstep (se 2 (by rfl) ⟨1164030, by rfl⟩ : syracuseStep 3104081 = 2328061) B2328061
theorem B2071889 : Blo 1379509 2071889 := bstep (se 2 (by rfl) ⟨776958, by rfl⟩ : syracuseStep 2071889 = 1553917) B1553917
theorem B3104099 : Blo 1379509 3104099 := bstep (se 1 (by rfl) ⟨2328074, by rfl⟩ : syracuseStep 3104099 = 4656149) B4656149
theorem B5979491 : Blo 1379509 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B2071907 : Blo 1379509 2071907 := bstep (se 1 (by rfl) ⟨1553930, by rfl⟩ : syracuseStep 2071907 = 3107861) B3107861
theorem B4423025 : Blo 1379509 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B2071937 : Blo 1379509 2071937 := bstep (se 2 (by rfl) ⟨776976, by rfl⟩ : syracuseStep 2071937 = 1553953) B1553953
theorem B2071955 : Blo 1379509 2071955 := bstep (se 1 (by rfl) ⟨1553966, by rfl⟩ : syracuseStep 2071955 = 3107933) B3107933
theorem B1965475 : Blo 1379509 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B2071985 : Blo 1379509 2071985 := bstep (se 2 (by rfl) ⟨776994, by rfl⟩ : syracuseStep 2071985 = 1553989) B1553989
theorem B2072003 : Blo 1379509 2072003 := bstep (se 1 (by rfl) ⟨1554002, by rfl⟩ : syracuseStep 2072003 = 3108005) B3108005
theorem B4660685 : Blo 1379509 4660685 := bstep (se 3 (by rfl) ⟨873878, by rfl⟩ : syracuseStep 4660685 = 1747757) B1747757
theorem B3317201 : Blo 1379509 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B2072033 : Blo 1379509 2072033 := bstep (se 2 (by rfl) ⟨777012, by rfl⟩ : syracuseStep 2072033 = 1554025) B1554025
theorem B2072051 : Blo 1379509 2072051 := bstep (se 1 (by rfl) ⟨1554038, by rfl⟩ : syracuseStep 2072051 = 3108077) B3108077
theorem B4660739 : Blo 1379509 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B2072081 : Blo 1379509 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B2072099 : Blo 1379509 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B2072129 : Blo 1379509 2072129 := bstep (se 2 (by rfl) ⟨777048, by rfl⟩ : syracuseStep 2072129 = 1554097) B1554097
theorem B2072147 : Blo 1379509 2072147 := bstep (se 1 (by rfl) ⟨1554110, by rfl⟩ : syracuseStep 2072147 = 3108221) B3108221
theorem B3104369 : Blo 1379509 3104369 := bstep (se 2 (by rfl) ⟨1164138, by rfl⟩ : syracuseStep 3104369 = 2328277) B2328277
theorem B2072177 : Blo 1379509 2072177 := bstep (se 2 (by rfl) ⟨777066, by rfl⟩ : syracuseStep 2072177 = 1554133) B1554133
theorem B3104387 : Blo 1379509 3104387 := bstep (se 1 (by rfl) ⟨2328290, by rfl⟩ : syracuseStep 3104387 = 4656581) B4656581
theorem B2072195 : Blo 1379509 2072195 := bstep (se 1 (by rfl) ⟨1554146, by rfl⟩ : syracuseStep 2072195 = 3108293) B3108293
theorem B2072225 : Blo 1379509 2072225 := bstep (se 2 (by rfl) ⟨777084, by rfl⟩ : syracuseStep 2072225 = 1554169) B1554169
theorem B6635171 : Blo 1379509 6635171 := bstep (se 1 (by rfl) ⟨4976378, by rfl⟩ : syracuseStep 6635171 = 9952757) B9952757
theorem B3784369 : Blo 1379509 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B2072243 : Blo 1379509 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B1474243 : Blo 1379509 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B4661009 : Blo 1379509 4661009 := bstep (se 2 (by rfl) ⟨1747878, by rfl⟩ : syracuseStep 4661009 = 3495757) B3495757
theorem B3104657 : Blo 1379509 3104657 := bstep (se 2 (by rfl) ⟨1164246, by rfl⟩ : syracuseStep 3104657 = 2328493) B2328493
theorem B1965971 : Blo 1379509 1965971 := bstep (se 1 (by rfl) ⟨1474478, by rfl⟩ : syracuseStep 1965971 = 2948957) B2948957
theorem B3104675 : Blo 1379509 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B2621393 : Blo 1379509 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B3104819 : Blo 1379509 3104819 := bstep (se 1 (by rfl) ⟨2328614, by rfl⟩ : syracuseStep 3104819 = 4657229) B4657229
theorem B1474615 : Blo 1379509 1474615 := bstep (se 1 (by rfl) ⟨1105961, by rfl⟩ : syracuseStep 1474615 = 2211923) B2211923
theorem B17678411 : Blo 1379509 17678411 := bstep (se 1 (by rfl) ⟨13258808, by rfl⟩ : syracuseStep 17678411 = 26517617) B26517617
theorem B10362955 : Blo 1379509 10362955 := bstep (se 1 (by rfl) ⟨7772216, by rfl⟩ : syracuseStep 10362955 = 15544433) B15544433
theorem B3104855 : Blo 1379509 3104855 := bstep (se 1 (by rfl) ⟨2328641, by rfl⟩ : syracuseStep 3104855 = 4657283) B4657283
theorem B2211929 : Blo 1379509 2211929 := bstep (se 2 (by rfl) ⟨829473, by rfl⟩ : syracuseStep 2211929 = 1658947) B1658947
theorem B6987869 : Blo 1379509 6987869 := bstep (se 3 (by rfl) ⟨1310225, by rfl⟩ : syracuseStep 6987869 = 2620451) B2620451
theorem B22380725 : Blo 1379509 22380725 := bstep (se 5 (by rfl) ⟨1049096, by rfl⟩ : syracuseStep 22380725 = 2098193) B2098193
theorem B4661441 : Blo 1379509 4661441 := bstep (se 2 (by rfl) ⟨1748040, by rfl⟩ : syracuseStep 4661441 = 3496081) B3496081
theorem B3932363 : Blo 1379509 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B2212057 : Blo 1379509 2212057 := bstep (se 2 (by rfl) ⟨829521, by rfl⟩ : syracuseStep 2212057 = 1659043) B1659043
theorem B3105035 : Blo 1379509 3105035 := bstep (se 1 (by rfl) ⟨2328776, by rfl⟩ : syracuseStep 3105035 = 4657553) B4657553
theorem B5595443 : Blo 1379509 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B8839489 : Blo 1379509 8839489 := bstep (se 2 (by rfl) ⟨3314808, by rfl⟩ : syracuseStep 8839489 = 6629617) B6629617
theorem B3105089 : Blo 1379509 3105089 := bstep (se 2 (by rfl) ⟨1164408, by rfl⟩ : syracuseStep 3105089 = 2328817) B2328817
theorem B2949529 : Blo 1379509 2949529 := bstep (se 2 (by rfl) ⟨1106073, by rfl⟩ : syracuseStep 2949529 = 2212147) B2212147
theorem B9945605 : Blo 1379509 9945605 := bstep (se 4 (by rfl) ⟨932400, by rfl⟩ : syracuseStep 9945605 = 1864801) B1864801
theorem B2621963 : Blo 1379509 2621963 := bstep (se 1 (by rfl) ⟨1966472, by rfl⟩ : syracuseStep 2621963 = 3932945) B3932945
theorem B3105305 : Blo 1379509 3105305 := bstep (se 2 (by rfl) ⟨1164489, by rfl⟩ : syracuseStep 3105305 = 2328979) B2328979
theorem B18891299 : Blo 1379509 18891299 := bstep (se 1 (by rfl) ⟨14168474, by rfl⟩ : syracuseStep 18891299 = 28336949) B28336949
theorem B10764845 : Blo 1379509 10764845 := bstep (se 3 (by rfl) ⟨2018408, by rfl⟩ : syracuseStep 10764845 = 4036817) B4036817
theorem B6636077 : Blo 1379509 6636077 := bstep (se 3 (by rfl) ⟨1244264, by rfl⟩ : syracuseStep 6636077 = 2488529) B2488529
theorem B163627573 : Blo 1379509 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B4424267 : Blo 1379509 4424267 := bstep (se 1 (by rfl) ⟨3318200, by rfl⟩ : syracuseStep 4424267 = 6636401) B6636401
theorem B3105395 : Blo 1379509 3105395 := bstep (se 1 (by rfl) ⟨2329046, by rfl⟩ : syracuseStep 3105395 = 4658093) B4658093
theorem B3105431 : Blo 1379509 3105431 := bstep (se 1 (by rfl) ⟨2329073, by rfl⟩ : syracuseStep 3105431 = 4658147) B4658147
theorem B2949785 : Blo 1379509 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B2622145 : Blo 1379509 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B4661981 : Blo 1379509 4661981 := bstep (se 3 (by rfl) ⟨874121, by rfl⟩ : syracuseStep 4661981 = 1748243) B1748243
theorem B3105611 : Blo 1379509 3105611 := bstep (se 1 (by rfl) ⟨2329208, by rfl⟩ : syracuseStep 3105611 = 4658417) B4658417
theorem B3105665 : Blo 1379509 3105665 := bstep (se 2 (by rfl) ⟨1164624, by rfl⟩ : syracuseStep 3105665 = 2329249) B2329249
theorem B5899159 : Blo 1379509 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B5899229 : Blo 1379509 5899229 := bstep (se 3 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 5899229 = 2212211) B2212211
theorem B2950195 : Blo 1379509 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B3105881 : Blo 1379509 3105881 := bstep (se 2 (by rfl) ⟨1164705, by rfl⟩ : syracuseStep 3105881 = 2329411) B2329411
theorem B2622593 : Blo 1379509 2622593 := bstep (se 2 (by rfl) ⟨983472, by rfl⟩ : syracuseStep 2622593 = 1966945) B1966945
theorem B3105971 : Blo 1379509 3105971 := bstep (se 1 (by rfl) ⟨2329478, by rfl⟩ : syracuseStep 3105971 = 4658957) B4658957
theorem B3106007 : Blo 1379509 3106007 := bstep (se 1 (by rfl) ⟨2329505, by rfl⟩ : syracuseStep 3106007 = 4659011) B4659011
theorem B4973899 : Blo 1379509 4973899 := bstep (se 1 (by rfl) ⟨3730424, by rfl⟩ : syracuseStep 4973899 = 7460849) B7460849
theorem B6292829 : Blo 1379509 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B3106187 : Blo 1379509 3106187 := bstep (se 1 (by rfl) ⟨2329640, by rfl⟩ : syracuseStep 3106187 = 4659281) B4659281
theorem B3106241 : Blo 1379509 3106241 := bstep (se 2 (by rfl) ⟨1164840, by rfl⟩ : syracuseStep 3106241 = 2329681) B2329681
theorem B2098777 : Blo 1379509 2098777 := bstep (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) B1574083
theorem B8848997 : Blo 1379509 8848997 := bstep (se 4 (by rfl) ⟨829593, by rfl⟩ : syracuseStep 8848997 = 1659187) B1659187
theorem B6293123 : Blo 1379509 6293123 := bstep (se 1 (by rfl) ⟨4719842, by rfl⟩ : syracuseStep 6293123 = 9439685) B9439685
theorem B5244547 : Blo 1379509 5244547 := bstep (se 1 (by rfl) ⟨3933410, by rfl⟩ : syracuseStep 5244547 = 7866821) B7866821
theorem B2328203 : Blo 1379509 2328203 := bstep (se 1 (by rfl) ⟨1746152, by rfl⟩ : syracuseStep 2328203 = 3492305) B3492305
theorem B8849047 : Blo 1379509 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B3106457 : Blo 1379509 3106457 := bstep (se 2 (by rfl) ⟨1164921, by rfl⟩ : syracuseStep 3106457 = 2329843) B2329843
theorem B5899979 : Blo 1379509 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B3106547 : Blo 1379509 3106547 := bstep (se 1 (by rfl) ⟨2329910, by rfl⟩ : syracuseStep 3106547 = 4659821) B4659821
theorem B14165765 : Blo 1379509 14165765 := bstep (se 4 (by rfl) ⟨1328040, by rfl⟩ : syracuseStep 14165765 = 2656081) B2656081
theorem B2328331 : Blo 1379509 2328331 := bstep (se 1 (by rfl) ⟨1746248, by rfl⟩ : syracuseStep 2328331 = 3492497) B3492497
theorem B3106583 : Blo 1379509 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B3934003 : Blo 1379509 3934003 := bstep (se 1 (by rfl) ⟨2950502, by rfl⟩ : syracuseStep 3934003 = 5901005) B5901005
theorem B1746775 : Blo 1379509 1746775 := bstep (se 1 (by rfl) ⟨1310081, by rfl⟩ : syracuseStep 1746775 = 2620163) B2620163
theorem B2328473 : Blo 1379509 2328473 := bstep (se 2 (by rfl) ⟨873177, by rfl⟩ : syracuseStep 2328473 = 1746355) B1746355
theorem B5244851 : Blo 1379509 5244851 := bstep (se 1 (by rfl) ⟨3933638, by rfl⟩ : syracuseStep 5244851 = 7867277) B7867277
theorem B3106763 : Blo 1379509 3106763 := bstep (se 1 (by rfl) ⟨2330072, by rfl⟩ : syracuseStep 3106763 = 4660145) B4660145
theorem B3106817 : Blo 1379509 3106817 := bstep (se 2 (by rfl) ⟨1165056, by rfl⟩ : syracuseStep 3106817 = 2330113) B2330113
theorem B2328601 : Blo 1379509 2328601 := bstep (se 2 (by rfl) ⟨873225, by rfl⟩ : syracuseStep 2328601 = 1746451) B1746451
theorem B6989975 : Blo 1379509 6989975 := bstep (se 1 (by rfl) ⟨5242481, by rfl⟩ : syracuseStep 6989975 = 10484963) B10484963
theorem B3360971 : Blo 1379509 3360971 := bstep (se 1 (by rfl) ⟨2520728, by rfl⟩ : syracuseStep 3360971 = 5041457) B5041457
theorem B3107033 : Blo 1379509 3107033 := bstep (se 2 (by rfl) ⟨1165137, by rfl⟩ : syracuseStep 3107033 = 2330275) B2330275
theorem B3107123 : Blo 1379509 3107123 := bstep (se 1 (by rfl) ⟨2330342, by rfl⟩ : syracuseStep 3107123 = 4660685) B4660685
theorem B3107159 : Blo 1379509 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B9947569 : Blo 1379509 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B22399409 : Blo 1379509 22399409 := bstep (se 2 (by rfl) ⟨8399778, by rfl⟩ : syracuseStep 22399409 = 16799557) B16799557
theorem B3107339 : Blo 1379509 3107339 := bstep (se 1 (by rfl) ⟨2330504, by rfl⟩ : syracuseStep 3107339 = 4661009) B4661009
theorem B10488365 : Blo 1379509 10488365 := bstep (se 3 (by rfl) ⟨1966568, by rfl⟩ : syracuseStep 10488365 = 3933137) B3933137
theorem B3107393 : Blo 1379509 3107393 := bstep (se 2 (by rfl) ⟨1165272, by rfl⟩ : syracuseStep 3107393 = 2330545) B2330545
theorem B2329175 : Blo 1379509 2329175 := bstep (se 1 (by rfl) ⟨1746881, by rfl⟩ : syracuseStep 2329175 = 3493763) B3493763
theorem B7858781 : Blo 1379509 7858781 := bstep (se 3 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 7858781 = 2947043) B2947043
theorem B1747595 : Blo 1379509 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B4975283 : Blo 1379509 4975283 := bstep (se 1 (by rfl) ⟨3731462, by rfl⟩ : syracuseStep 4975283 = 7462925) B7462925
theorem B2329303 : Blo 1379509 2329303 := bstep (se 1 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 2329303 = 3493955) B3493955
theorem B2837207 : Blo 1379509 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B3107609 : Blo 1379509 3107609 := bstep (se 2 (by rfl) ⟨1165353, by rfl⟩ : syracuseStep 3107609 = 2330707) B2330707
theorem B3492659 : Blo 1379509 3492659 := bstep (se 1 (by rfl) ⟨2619494, by rfl⟩ : syracuseStep 3492659 = 5238989) B5238989
theorem B3107699 : Blo 1379509 3107699 := bstep (se 1 (by rfl) ⟨2330774, by rfl⟩ : syracuseStep 3107699 = 4661549) B4661549
theorem B6384529 : Blo 1379509 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B3107735 : Blo 1379509 3107735 := bstep (se 1 (by rfl) ⟨2330801, by rfl⟩ : syracuseStep 3107735 = 4661603) B4661603
theorem B10480589 : Blo 1379509 10480589 := bstep (se 3 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 10480589 = 3930221) B3930221
theorem B4656203 : Blo 1379509 4656203 := bstep (se 1 (by rfl) ⟨3492152, by rfl⟩ : syracuseStep 4656203 = 6984305) B6984305
theorem B3107915 : Blo 1379509 3107915 := bstep (se 1 (by rfl) ⟨2330936, by rfl⟩ : syracuseStep 3107915 = 4661873) B4661873
theorem B3492953 : Blo 1379509 3492953 := bstep (se 2 (by rfl) ⟨1309857, by rfl⟩ : syracuseStep 3492953 = 2619715) B2619715
theorem B3107969 : Blo 1379509 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B1379511 : Blo 1379509 1379511 := bstep (se 1 (by rfl) ⟨1034633, by rfl⟩ : syracuseStep 1379511 = 2069267) B2069267
theorem B1379531 : Blo 1379509 1379531 := bstep (se 1 (by rfl) ⟨1034648, by rfl⟩ : syracuseStep 1379531 = 2069297) B2069297
theorem B1379543 : Blo 1379509 1379543 := bstep (se 1 (by rfl) ⟨1034657, by rfl⟩ : syracuseStep 1379543 = 2069315) B2069315
theorem B1379563 : Blo 1379509 1379563 := bstep (se 1 (by rfl) ⟨1034672, by rfl⟩ : syracuseStep 1379563 = 2069345) B2069345
theorem B1379575 : Blo 1379509 1379575 := bstep (se 1 (by rfl) ⟨1034681, by rfl⟩ : syracuseStep 1379575 = 2069363) B2069363
theorem B1379595 : Blo 1379509 1379595 := bstep (se 1 (by rfl) ⟨1034696, by rfl⟩ : syracuseStep 1379595 = 2069393) B2069393
theorem B1379607 : Blo 1379509 1379607 := bstep (se 1 (by rfl) ⟨1034705, by rfl⟩ : syracuseStep 1379607 = 2069411) B2069411
theorem B1379627 : Blo 1379509 1379627 := bstep (se 1 (by rfl) ⟨1034720, by rfl⟩ : syracuseStep 1379627 = 2069441) B2069441
theorem B1379639 : Blo 1379509 1379639 := bstep (se 1 (by rfl) ⟨1034729, by rfl⟩ : syracuseStep 1379639 = 2069459) B2069459
theorem B1379659 : Blo 1379509 1379659 := bstep (se 1 (by rfl) ⟨1034744, by rfl⟩ : syracuseStep 1379659 = 2069489) B2069489
theorem B7859531 : Blo 1379509 7859531 := bstep (se 1 (by rfl) ⟨5894648, by rfl⟩ : syracuseStep 7859531 = 11789297) B11789297
theorem B2329931 : Blo 1379509 2329931 := bstep (se 1 (by rfl) ⟨1747448, by rfl⟩ : syracuseStep 2329931 = 3494897) B3494897
theorem B1748299 : Blo 1379509 1748299 := bstep (se 1 (by rfl) ⟨1311224, by rfl⟩ : syracuseStep 1748299 = 2622449) B2622449
theorem B1379671 : Blo 1379509 1379671 := bstep (se 1 (by rfl) ⟨1034753, by rfl⟩ : syracuseStep 1379671 = 2069507) B2069507
theorem B4656473 : Blo 1379509 4656473 := bstep (se 2 (by rfl) ⟨1746177, by rfl⟩ : syracuseStep 4656473 = 3492355) B3492355
theorem B3108185 : Blo 1379509 3108185 := bstep (se 2 (by rfl) ⟨1165569, by rfl⟩ : syracuseStep 3108185 = 2331139) B2331139
theorem B5598557 : Blo 1379509 5598557 := bstep (se 3 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 5598557 = 2099459) B2099459
theorem B7458149 : Blo 1379509 7458149 := bstep (se 4 (by rfl) ⟨699201, by rfl⟩ : syracuseStep 7458149 = 1398403) B1398403
theorem B1379691 : Blo 1379509 1379691 := bstep (se 1 (by rfl) ⟨1034768, by rfl⟩ : syracuseStep 1379691 = 2069537) B2069537
theorem B1379703 : Blo 1379509 1379703 := bstep (se 1 (by rfl) ⟨1034777, by rfl⟩ : syracuseStep 1379703 = 2069555) B2069555
theorem B1379723 : Blo 1379509 1379723 := bstep (se 1 (by rfl) ⟨1034792, by rfl⟩ : syracuseStep 1379723 = 2069585) B2069585
theorem B1379735 : Blo 1379509 1379735 := bstep (se 1 (by rfl) ⟨1034801, by rfl⟩ : syracuseStep 1379735 = 2069603) B2069603
theorem B1379755 : Blo 1379509 1379755 := bstep (se 1 (by rfl) ⟨1034816, by rfl⟩ : syracuseStep 1379755 = 2069633) B2069633
theorem B10481075 : Blo 1379509 10481075 := bstep (se 1 (by rfl) ⟨7860806, by rfl⟩ : syracuseStep 10481075 = 15721613) B15721613
theorem B5893555 : Blo 1379509 5893555 := bstep (se 1 (by rfl) ⟨4420166, by rfl⟩ : syracuseStep 5893555 = 8840333) B8840333
theorem B3108275 : Blo 1379509 3108275 := bstep (se 1 (by rfl) ⟨2331206, by rfl⟩ : syracuseStep 3108275 = 4662413) B4662413
theorem B1379767 : Blo 1379509 1379767 := bstep (se 1 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 1379767 = 2069651) B2069651
theorem B1379787 : Blo 1379509 1379787 := bstep (se 1 (by rfl) ⟨1034840, by rfl⟩ : syracuseStep 1379787 = 2069681) B2069681
theorem B2330059 : Blo 1379509 2330059 := bstep (se 1 (by rfl) ⟨1747544, by rfl⟩ : syracuseStep 2330059 = 3495089) B3495089
theorem B1379799 : Blo 1379509 1379799 := bstep (se 1 (by rfl) ⟨1034849, by rfl⟩ : syracuseStep 1379799 = 2069699) B2069699
theorem B1658327 : Blo 1379509 1658327 := bstep (se 1 (by rfl) ⟨1243745, by rfl⟩ : syracuseStep 1658327 = 2487491) B2487491
theorem B3108311 : Blo 1379509 3108311 := bstep (se 1 (by rfl) ⟨2331233, by rfl⟩ : syracuseStep 3108311 = 4662467) B4662467
theorem B1379819 : Blo 1379509 1379819 := bstep (se 1 (by rfl) ⟨1034864, by rfl⟩ : syracuseStep 1379819 = 2069729) B2069729
theorem B1379831 : Blo 1379509 1379831 := bstep (se 1 (by rfl) ⟨1034873, by rfl⟩ : syracuseStep 1379831 = 2069747) B2069747
theorem B1379851 : Blo 1379509 1379851 := bstep (se 1 (by rfl) ⟨1034888, by rfl⟩ : syracuseStep 1379851 = 2069777) B2069777
theorem B1379863 : Blo 1379509 1379863 := bstep (se 1 (by rfl) ⟨1034897, by rfl⟩ : syracuseStep 1379863 = 2069795) B2069795
theorem B1379883 : Blo 1379509 1379883 := bstep (se 1 (by rfl) ⟨1034912, by rfl⟩ : syracuseStep 1379883 = 2069825) B2069825
theorem B1379895 : Blo 1379509 1379895 := bstep (se 1 (by rfl) ⟨1034921, by rfl⟩ : syracuseStep 1379895 = 2069843) B2069843
theorem B1379915 : Blo 1379509 1379915 := bstep (se 1 (by rfl) ⟨1034936, by rfl⟩ : syracuseStep 1379915 = 2069873) B2069873
theorem B1379927 : Blo 1379509 1379927 := bstep (se 1 (by rfl) ⟨1034945, by rfl⟩ : syracuseStep 1379927 = 2069891) B2069891
theorem B2330201 : Blo 1379509 2330201 := bstep (se 2 (by rfl) ⟨873825, by rfl⟩ : syracuseStep 2330201 = 1747651) B1747651
theorem B50409053 : Blo 1379509 50409053 := bstep (se 3 (by rfl) ⟨9451697, by rfl⟩ : syracuseStep 50409053 = 18903395) B18903395
theorem B1379947 : Blo 1379509 1379947 := bstep (se 1 (by rfl) ⟨1034960, by rfl⟩ : syracuseStep 1379947 = 2069921) B2069921
theorem B1551991 : Blo 1379509 1551991 := bstep (se 1 (by rfl) ⟨1163993, by rfl⟩ : syracuseStep 1551991 = 2327987) B2327987
theorem B1379959 : Blo 1379509 1379959 := bstep (se 1 (by rfl) ⟨1034969, by rfl⟩ : syracuseStep 1379959 = 2069939) B2069939
theorem B1379979 : Blo 1379509 1379979 := bstep (se 1 (by rfl) ⟨1034984, by rfl⟩ : syracuseStep 1379979 = 2069969) B2069969
theorem B1379991 : Blo 1379509 1379991 := bstep (se 1 (by rfl) ⟨1034993, by rfl⟩ : syracuseStep 1379991 = 2069987) B2069987
theorem B10628759 : Blo 1379509 10628759 := bstep (se 1 (by rfl) ⟨7971569, by rfl⟩ : syracuseStep 10628759 = 15943139) B15943139
theorem B1380011 : Blo 1379509 1380011 := bstep (se 1 (by rfl) ⟨1035008, by rfl⟩ : syracuseStep 1380011 = 2070017) B2070017
theorem B1380023 : Blo 1379509 1380023 := bstep (se 1 (by rfl) ⟨1035017, by rfl⟩ : syracuseStep 1380023 = 2070035) B2070035
theorem B1380043 : Blo 1379509 1380043 := bstep (se 1 (by rfl) ⟨1035032, by rfl⟩ : syracuseStep 1380043 = 2070065) B2070065
theorem B1380055 : Blo 1379509 1380055 := bstep (se 1 (by rfl) ⟨1035041, by rfl⟩ : syracuseStep 1380055 = 2070083) B2070083
theorem B2330329 : Blo 1379509 2330329 := bstep (se 2 (by rfl) ⟨873873, by rfl⟩ : syracuseStep 2330329 = 1747747) B1747747
theorem B1380075 : Blo 1379509 1380075 := bstep (se 1 (by rfl) ⟨1035056, by rfl⟩ : syracuseStep 1380075 = 2070113) B2070113
theorem B1380087 : Blo 1379509 1380087 := bstep (se 1 (by rfl) ⟨1035065, by rfl⟩ : syracuseStep 1380087 = 2070131) B2070131
theorem B1380107 : Blo 1379509 1380107 := bstep (se 1 (by rfl) ⟨1035080, by rfl⟩ : syracuseStep 1380107 = 2070161) B2070161
theorem B1380119 : Blo 1379509 1380119 := bstep (se 1 (by rfl) ⟨1035089, by rfl⟩ : syracuseStep 1380119 = 2070179) B2070179
theorem B1552171 : Blo 1379509 1552171 := bstep (se 1 (by rfl) ⟨1164128, by rfl⟩ : syracuseStep 1552171 = 2328257) B2328257
theorem B1380139 : Blo 1379509 1380139 := bstep (se 1 (by rfl) ⟨1035104, by rfl⟩ : syracuseStep 1380139 = 2070209) B2070209
theorem B1380151 : Blo 1379509 1380151 := bstep (se 1 (by rfl) ⟨1035113, by rfl⟩ : syracuseStep 1380151 = 2070227) B2070227
theorem B1380171 : Blo 1379509 1380171 := bstep (se 1 (by rfl) ⟨1035128, by rfl⟩ : syracuseStep 1380171 = 2070257) B2070257
theorem B1380183 : Blo 1379509 1380183 := bstep (se 1 (by rfl) ⟨1035137, by rfl⟩ : syracuseStep 1380183 = 2070275) B2070275
theorem B17698661 : Blo 1379509 17698661 := bstep (se 4 (by rfl) ⟨1659249, by rfl⟩ : syracuseStep 17698661 = 3318499) B3318499
theorem B1380203 : Blo 1379509 1380203 := bstep (se 1 (by rfl) ⟨1035152, by rfl⟩ : syracuseStep 1380203 = 2070305) B2070305
theorem B1380215 : Blo 1379509 1380215 := bstep (se 1 (by rfl) ⟨1035161, by rfl⟩ : syracuseStep 1380215 = 2070323) B2070323
theorem B5975939 : Blo 1379509 5975939 := bstep (se 1 (by rfl) ⟨4481954, by rfl⟩ : syracuseStep 5975939 = 8963909) B8963909
theorem B1380235 : Blo 1379509 1380235 := bstep (se 1 (by rfl) ⟨1035176, by rfl⟩ : syracuseStep 1380235 = 2070353) B2070353
theorem B1552279 : Blo 1379509 1552279 := bstep (se 1 (by rfl) ⟨1164209, by rfl⟩ : syracuseStep 1552279 = 2328419) B2328419
theorem B1380247 : Blo 1379509 1380247 := bstep (se 1 (by rfl) ⟨1035185, by rfl⟩ : syracuseStep 1380247 = 2070371) B2070371
theorem B1380267 : Blo 1379509 1380267 := bstep (se 1 (by rfl) ⟨1035200, by rfl⟩ : syracuseStep 1380267 = 2070401) B2070401
theorem B5238701 : Blo 1379509 5238701 := bstep (se 3 (by rfl) ⟨982256, by rfl⟩ : syracuseStep 5238701 = 1964513) B1964513
theorem B1380279 : Blo 1379509 1380279 := bstep (se 1 (by rfl) ⟨1035209, by rfl⟩ : syracuseStep 1380279 = 2070419) B2070419
theorem B1380299 : Blo 1379509 1380299 := bstep (se 1 (by rfl) ⟨1035224, by rfl⟩ : syracuseStep 1380299 = 2070449) B2070449
theorem B2240471 : Blo 1379509 2240471 := bstep (se 1 (by rfl) ⟨1680353, by rfl⟩ : syracuseStep 2240471 = 3360707) B3360707
theorem B1380311 : Blo 1379509 1380311 := bstep (se 1 (by rfl) ⟨1035233, by rfl⟩ : syracuseStep 1380311 = 2070467) B2070467
theorem B1380331 : Blo 1379509 1380331 := bstep (se 1 (by rfl) ⟨1035248, by rfl⟩ : syracuseStep 1380331 = 2070497) B2070497
theorem B1380343 : Blo 1379509 1380343 := bstep (se 1 (by rfl) ⟨1035257, by rfl⟩ : syracuseStep 1380343 = 2070515) B2070515
theorem B1380363 : Blo 1379509 1380363 := bstep (se 1 (by rfl) ⟨1035272, by rfl⟩ : syracuseStep 1380363 = 2070545) B2070545
theorem B4657175 : Blo 1379509 4657175 := bstep (se 1 (by rfl) ⟨3492881, by rfl⟩ : syracuseStep 4657175 = 6985763) B6985763
theorem B1380375 : Blo 1379509 1380375 := bstep (se 1 (by rfl) ⟨1035281, by rfl⟩ : syracuseStep 1380375 = 2070563) B2070563
theorem B1380395 : Blo 1379509 1380395 := bstep (se 1 (by rfl) ⟨1035296, by rfl⟩ : syracuseStep 1380395 = 2070593) B2070593
theorem B1380407 : Blo 1379509 1380407 := bstep (se 1 (by rfl) ⟨1035305, by rfl⟩ : syracuseStep 1380407 = 2070611) B2070611
theorem B1552459 : Blo 1379509 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B7082059 : Blo 1379509 7082059 := bstep (se 1 (by rfl) ⟨5311544, by rfl⟩ : syracuseStep 7082059 = 10623089) B10623089
theorem B1380427 : Blo 1379509 1380427 := bstep (se 1 (by rfl) ⟨1035320, by rfl⟩ : syracuseStep 1380427 = 2070641) B2070641
theorem B1380439 : Blo 1379509 1380439 := bstep (se 1 (by rfl) ⟨1035329, by rfl⟩ : syracuseStep 1380439 = 2070659) B2070659
theorem B1380459 : Blo 1379509 1380459 := bstep (se 1 (by rfl) ⟨1035344, by rfl⟩ : syracuseStep 1380459 = 2070689) B2070689
theorem B1380471 : Blo 1379509 1380471 := bstep (se 1 (by rfl) ⟨1035353, by rfl⟩ : syracuseStep 1380471 = 2070707) B2070707
theorem B1380491 : Blo 1379509 1380491 := bstep (se 1 (by rfl) ⟨1035368, by rfl⟩ : syracuseStep 1380491 = 2070737) B2070737
theorem B1380503 : Blo 1379509 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B1380523 : Blo 1379509 1380523 := bstep (se 1 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 1380523 = 2070785) B2070785
theorem B1552567 : Blo 1379509 1552567 := bstep (se 1 (by rfl) ⟨1164425, by rfl⟩ : syracuseStep 1552567 = 2328851) B2328851
theorem B1380535 : Blo 1379509 1380535 := bstep (se 1 (by rfl) ⟨1035401, by rfl⟩ : syracuseStep 1380535 = 2070803) B2070803
theorem B1380555 : Blo 1379509 1380555 := bstep (se 1 (by rfl) ⟨1035416, by rfl⟩ : syracuseStep 1380555 = 2070833) B2070833
theorem B1380567 : Blo 1379509 1380567 := bstep (se 1 (by rfl) ⟨1035425, by rfl⟩ : syracuseStep 1380567 = 2070851) B2070851
theorem B1380587 : Blo 1379509 1380587 := bstep (se 1 (by rfl) ⟨1035440, by rfl⟩ : syracuseStep 1380587 = 2070881) B2070881
theorem B1380599 : Blo 1379509 1380599 := bstep (se 1 (by rfl) ⟨1035449, by rfl⟩ : syracuseStep 1380599 = 2070899) B2070899
theorem B1380619 : Blo 1379509 1380619 := bstep (se 1 (by rfl) ⟨1035464, by rfl⟩ : syracuseStep 1380619 = 2070929) B2070929
theorem B1380631 : Blo 1379509 1380631 := bstep (se 1 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 1380631 = 2070947) B2070947
theorem B2330903 : Blo 1379509 2330903 := bstep (se 1 (by rfl) ⟨1748177, by rfl⟩ : syracuseStep 2330903 = 3496355) B3496355
theorem B1380651 : Blo 1379509 1380651 := bstep (se 1 (by rfl) ⟨1035488, by rfl⟩ : syracuseStep 1380651 = 2070977) B2070977
theorem B6983981 : Blo 1379509 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B1380663 : Blo 1379509 1380663 := bstep (se 1 (by rfl) ⟨1035497, by rfl⟩ : syracuseStep 1380663 = 2070995) B2070995
theorem B1380683 : Blo 1379509 1380683 := bstep (se 1 (by rfl) ⟨1035512, by rfl⟩ : syracuseStep 1380683 = 2071025) B2071025
theorem B1380695 : Blo 1379509 1380695 := bstep (se 1 (by rfl) ⟨1035521, by rfl⟩ : syracuseStep 1380695 = 2071043) B2071043
theorem B1552747 : Blo 1379509 1552747 := bstep (se 1 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 1552747 = 2329121) B2329121
theorem B1380715 : Blo 1379509 1380715 := bstep (se 1 (by rfl) ⟨1035536, by rfl⟩ : syracuseStep 1380715 = 2071073) B2071073
theorem B1380727 : Blo 1379509 1380727 := bstep (se 1 (by rfl) ⟨1035545, by rfl⟩ : syracuseStep 1380727 = 2071091) B2071091
theorem B1380747 : Blo 1379509 1380747 := bstep (se 1 (by rfl) ⟨1035560, by rfl⟩ : syracuseStep 1380747 = 2071121) B2071121
theorem B11194775 : Blo 1379509 11194775 := bstep (se 1 (by rfl) ⟨8396081, by rfl⟩ : syracuseStep 11194775 = 16792163) B16792163
theorem B1380759 : Blo 1379509 1380759 := bstep (se 1 (by rfl) ⟨1035569, by rfl⟩ : syracuseStep 1380759 = 2071139) B2071139
theorem B2331031 : Blo 1379509 2331031 := bstep (se 1 (by rfl) ⟨1748273, by rfl⟩ : syracuseStep 2331031 = 3496547) B3496547
theorem B1380779 : Blo 1379509 1380779 := bstep (se 1 (by rfl) ⟨1035584, by rfl⟩ : syracuseStep 1380779 = 2071169) B2071169
theorem B13275569 : Blo 1379509 13275569 := bstep (se 2 (by rfl) ⟨4978338, by rfl⟩ : syracuseStep 13275569 = 9956677) B9956677
theorem B1380791 : Blo 1379509 1380791 := bstep (se 1 (by rfl) ⟨1035593, by rfl⟩ : syracuseStep 1380791 = 2071187) B2071187
theorem B3928513 : Blo 1379509 3928513 := bstep (se 2 (by rfl) ⟨1473192, by rfl⟩ : syracuseStep 3928513 = 2946385) B2946385
theorem B1380811 : Blo 1379509 1380811 := bstep (se 1 (by rfl) ⟨1035608, by rfl⟩ : syracuseStep 1380811 = 2071217) B2071217
theorem B2798039 : Blo 1379509 2798039 := bstep (se 1 (by rfl) ⟨2098529, by rfl⟩ : syracuseStep 2798039 = 4197059) B4197059
theorem B1552855 : Blo 1379509 1552855 := bstep (se 1 (by rfl) ⟨1164641, by rfl⟩ : syracuseStep 1552855 = 2329283) B2329283
theorem B1380823 : Blo 1379509 1380823 := bstep (se 1 (by rfl) ⟨1035617, by rfl⟩ : syracuseStep 1380823 = 2071235) B2071235
theorem B1380843 : Blo 1379509 1380843 := bstep (se 1 (by rfl) ⟨1035632, by rfl⟩ : syracuseStep 1380843 = 2071265) B2071265
theorem B1380855 : Blo 1379509 1380855 := bstep (se 1 (by rfl) ⟨1035641, by rfl⟩ : syracuseStep 1380855 = 2071283) B2071283
theorem B1380875 : Blo 1379509 1380875 := bstep (se 1 (by rfl) ⟨1035656, by rfl⟩ : syracuseStep 1380875 = 2071313) B2071313
theorem B1380887 : Blo 1379509 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B1380907 : Blo 1379509 1380907 := bstep (se 1 (by rfl) ⟨1035680, by rfl⟩ : syracuseStep 1380907 = 2071361) B2071361
theorem B4657715 : Blo 1379509 4657715 := bstep (se 1 (by rfl) ⟨3493286, by rfl⟩ : syracuseStep 4657715 = 6986573) B6986573
theorem B1380919 : Blo 1379509 1380919 := bstep (se 1 (by rfl) ⟨1035689, by rfl⟩ : syracuseStep 1380919 = 2071379) B2071379
theorem B8516161 : Blo 1379509 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B1380939 : Blo 1379509 1380939 := bstep (se 1 (by rfl) ⟨1035704, by rfl⟩ : syracuseStep 1380939 = 2071409) B2071409
theorem B1380951 : Blo 1379509 1380951 := bstep (se 1 (by rfl) ⟨1035713, by rfl⟩ : syracuseStep 1380951 = 2071427) B2071427
theorem B1380971 : Blo 1379509 1380971 := bstep (se 1 (by rfl) ⟨1035728, by rfl⟩ : syracuseStep 1380971 = 2071457) B2071457
theorem B1380983 : Blo 1379509 1380983 := bstep (se 1 (by rfl) ⟨1035737, by rfl⟩ : syracuseStep 1380983 = 2071475) B2071475
theorem B1553035 : Blo 1379509 1553035 := bstep (se 1 (by rfl) ⟨1164776, by rfl⟩ : syracuseStep 1553035 = 2329553) B2329553
theorem B1381003 : Blo 1379509 1381003 := bstep (se 1 (by rfl) ⟨1035752, by rfl⟩ : syracuseStep 1381003 = 2071505) B2071505
theorem B1381015 : Blo 1379509 1381015 := bstep (se 1 (by rfl) ⟨1035761, by rfl⟩ : syracuseStep 1381015 = 2071523) B2071523
theorem B1381035 : Blo 1379509 1381035 := bstep (se 1 (by rfl) ⟨1035776, by rfl⟩ : syracuseStep 1381035 = 2071553) B2071553
theorem B5239475 : Blo 1379509 5239475 := bstep (se 1 (by rfl) ⟨3929606, by rfl⟩ : syracuseStep 5239475 = 7859213) B7859213
theorem B19903157 : Blo 1379509 19903157 := bstep (se 5 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 19903157 = 1865921) B1865921
theorem B1381047 : Blo 1379509 1381047 := bstep (se 1 (by rfl) ⟨1035785, by rfl⟩ : syracuseStep 1381047 = 2071571) B2071571
theorem B3494603 : Blo 1379509 3494603 := bstep (se 1 (by rfl) ⟨2620952, by rfl⟩ : syracuseStep 3494603 = 5241905) B5241905
theorem B1381067 : Blo 1379509 1381067 := bstep (se 1 (by rfl) ⟨1035800, by rfl⟩ : syracuseStep 1381067 = 2071601) B2071601
theorem B1381079 : Blo 1379509 1381079 := bstep (se 1 (by rfl) ⟨1035809, by rfl⟩ : syracuseStep 1381079 = 2071619) B2071619
theorem B1381099 : Blo 1379509 1381099 := bstep (se 1 (by rfl) ⟨1035824, by rfl⟩ : syracuseStep 1381099 = 2071649) B2071649
theorem B1553143 : Blo 1379509 1553143 := bstep (se 1 (by rfl) ⟨1164857, by rfl⟩ : syracuseStep 1553143 = 2329715) B2329715
theorem B1381111 : Blo 1379509 1381111 := bstep (se 1 (by rfl) ⟨1035833, by rfl⟩ : syracuseStep 1381111 = 2071667) B2071667
theorem B1381131 : Blo 1379509 1381131 := bstep (se 1 (by rfl) ⟨1035848, by rfl⟩ : syracuseStep 1381131 = 2071697) B2071697
theorem B1381143 : Blo 1379509 1381143 := bstep (se 1 (by rfl) ⟨1035857, by rfl⟩ : syracuseStep 1381143 = 2071715) B2071715
theorem B2069273 : Blo 1379509 2069273 := bstep (se 2 (by rfl) ⟨775977, by rfl⟩ : syracuseStep 2069273 = 1551955) B1551955
theorem B11195171 : Blo 1379509 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B1381163 : Blo 1379509 1381163 := bstep (se 1 (by rfl) ⟨1035872, by rfl⟩ : syracuseStep 1381163 = 2071745) B2071745
theorem B5894957 : Blo 1379509 5894957 := bstep (se 3 (by rfl) ⟨1105304, by rfl⟩ : syracuseStep 5894957 = 2210609) B2210609
theorem B1381175 : Blo 1379509 1381175 := bstep (se 1 (by rfl) ⟨1035881, by rfl⟩ : syracuseStep 1381175 = 2071763) B2071763
theorem B4657985 : Blo 1379509 4657985 := bstep (se 2 (by rfl) ⟨1746744, by rfl⟩ : syracuseStep 4657985 = 3493489) B3493489
theorem B1381195 : Blo 1379509 1381195 := bstep (se 1 (by rfl) ⟨1035896, by rfl⟩ : syracuseStep 1381195 = 2071793) B2071793
theorem B1381207 : Blo 1379509 1381207 := bstep (se 1 (by rfl) ⟨1035905, by rfl⟩ : syracuseStep 1381207 = 2071811) B2071811
theorem B10482533 : Blo 1379509 10482533 := bstep (se 4 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 10482533 = 1965475) B1965475
theorem B1381227 : Blo 1379509 1381227 := bstep (se 1 (by rfl) ⟨1035920, by rfl⟩ : syracuseStep 1381227 = 2071841) B2071841
theorem B1381239 : Blo 1379509 1381239 := bstep (se 1 (by rfl) ⟨1035929, by rfl⟩ : syracuseStep 1381239 = 2071859) B2071859
theorem B2069387 : Blo 1379509 2069387 := bstep (se 1 (by rfl) ⟨1552040, by rfl⟩ : syracuseStep 2069387 = 3104081) B3104081
theorem B1381259 : Blo 1379509 1381259 := bstep (se 1 (by rfl) ⟨1035944, by rfl⟩ : syracuseStep 1381259 = 2071889) B2071889
theorem B2069399 : Blo 1379509 2069399 := bstep (se 1 (by rfl) ⟨1552049, by rfl⟩ : syracuseStep 2069399 = 3104099) B3104099
theorem B11662231 : Blo 1379509 11662231 := bstep (se 1 (by rfl) ⟨8746673, by rfl⟩ : syracuseStep 11662231 = 17493347) B17493347
theorem B3986327 : Blo 1379509 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B1381271 : Blo 1379509 1381271 := bstep (se 1 (by rfl) ⟨1035953, by rfl⟩ : syracuseStep 1381271 = 2071907) B2071907
theorem B1553323 : Blo 1379509 1553323 := bstep (se 1 (by rfl) ⟨1164992, by rfl⟩ : syracuseStep 1553323 = 2329985) B2329985
theorem B1381291 : Blo 1379509 1381291 := bstep (se 1 (by rfl) ⟨1035968, by rfl⟩ : syracuseStep 1381291 = 2071937) B2071937
theorem B7861171 : Blo 1379509 7861171 := bstep (se 1 (by rfl) ⟨5895878, by rfl⟩ : syracuseStep 7861171 = 11791757) B11791757
theorem B1381303 : Blo 1379509 1381303 := bstep (se 1 (by rfl) ⟨1035977, by rfl⟩ : syracuseStep 1381303 = 2071955) B2071955
theorem B1381323 : Blo 1379509 1381323 := bstep (se 1 (by rfl) ⟨1035992, by rfl⟩ : syracuseStep 1381323 = 2071985) B2071985
theorem B1381335 : Blo 1379509 1381335 := bstep (se 1 (by rfl) ⟨1036001, by rfl⟩ : syracuseStep 1381335 = 2072003) B2072003
theorem B2069465 : Blo 1379509 2069465 := bstep (se 2 (by rfl) ⟨776049, by rfl⟩ : syracuseStep 2069465 = 1552099) B1552099
theorem B12587993 : Blo 1379509 12587993 := bstep (se 2 (by rfl) ⟨4720497, by rfl⟩ : syracuseStep 12587993 = 9440995) B9440995
theorem B1381355 : Blo 1379509 1381355 := bstep (se 1 (by rfl) ⟨1036016, by rfl⟩ : syracuseStep 1381355 = 2072033) B2072033
theorem B1381367 : Blo 1379509 1381367 := bstep (se 1 (by rfl) ⟨1036025, by rfl⟩ : syracuseStep 1381367 = 2072051) B2072051
theorem B2520065 : Blo 1379509 2520065 := bstep (se 2 (by rfl) ⟨945024, by rfl⟩ : syracuseStep 2520065 = 1890049) B1890049
theorem B1381387 : Blo 1379509 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B1553431 : Blo 1379509 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B1381399 : Blo 1379509 1381399 := bstep (se 1 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 1381399 = 2072099) B2072099
theorem B1381419 : Blo 1379509 1381419 := bstep (se 1 (by rfl) ⟨1036064, by rfl⟩ : syracuseStep 1381419 = 2072129) B2072129
theorem B1381431 : Blo 1379509 1381431 := bstep (se 1 (by rfl) ⟨1036073, by rfl⟩ : syracuseStep 1381431 = 2072147) B2072147
theorem B2069579 : Blo 1379509 2069579 := bstep (se 1 (by rfl) ⟨1552184, by rfl⟩ : syracuseStep 2069579 = 3104369) B3104369
theorem B1381451 : Blo 1379509 1381451 := bstep (se 1 (by rfl) ⟨1036088, by rfl⟩ : syracuseStep 1381451 = 2072177) B2072177
theorem B2069591 : Blo 1379509 2069591 := bstep (se 1 (by rfl) ⟨1552193, by rfl⟩ : syracuseStep 2069591 = 3104387) B3104387
theorem B1381463 : Blo 1379509 1381463 := bstep (se 1 (by rfl) ⟨1036097, by rfl⟩ : syracuseStep 1381463 = 2072195) B2072195
theorem B1381483 : Blo 1379509 1381483 := bstep (se 1 (by rfl) ⟨1036112, by rfl⟩ : syracuseStep 1381483 = 2072225) B2072225
theorem B1381495 : Blo 1379509 1381495 := bstep (se 1 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 1381495 = 2072243) B2072243
theorem B2069657 : Blo 1379509 2069657 := bstep (se 2 (by rfl) ⟨776121, by rfl⟩ : syracuseStep 2069657 = 1552243) B1552243
theorem B1553611 : Blo 1379509 1553611 := bstep (se 1 (by rfl) ⟨1165208, by rfl⟩ : syracuseStep 1553611 = 2330417) B2330417
theorem B2069771 : Blo 1379509 2069771 := bstep (se 1 (by rfl) ⟨1552328, by rfl⟩ : syracuseStep 2069771 = 3104657) B3104657
theorem B2069783 : Blo 1379509 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B1553719 : Blo 1379509 1553719 := bstep (se 1 (by rfl) ⟨1165289, by rfl⟩ : syracuseStep 1553719 = 2330579) B2330579
theorem B10483019 : Blo 1379509 10483019 := bstep (se 1 (by rfl) ⟨7862264, by rfl⟩ : syracuseStep 10483019 = 15724529) B15724529
theorem B2069849 : Blo 1379509 2069849 := bstep (se 2 (by rfl) ⟨776193, by rfl⟩ : syracuseStep 2069849 = 1552387) B1552387
theorem B4658525 : Blo 1379509 4658525 := bstep (se 3 (by rfl) ⟨873473, by rfl⟩ : syracuseStep 4658525 = 1746947) B1746947
theorem B14161331 : Blo 1379509 14161331 := bstep (se 1 (by rfl) ⟨10620998, by rfl⟩ : syracuseStep 14161331 = 21241997) B21241997
theorem B2069963 : Blo 1379509 2069963 := bstep (se 1 (by rfl) ⟨1552472, by rfl⟩ : syracuseStep 2069963 = 3104945) B3104945
theorem B2069975 : Blo 1379509 2069975 := bstep (se 1 (by rfl) ⟨1552481, by rfl⟩ : syracuseStep 2069975 = 3104963) B3104963
theorem B1553899 : Blo 1379509 1553899 := bstep (se 1 (by rfl) ⟨1165424, by rfl⟩ : syracuseStep 1553899 = 2330849) B2330849
theorem B2070041 : Blo 1379509 2070041 := bstep (se 2 (by rfl) ⟨776265, by rfl⟩ : syracuseStep 2070041 = 1552531) B1552531
theorem B1554007 : Blo 1379509 1554007 := bstep (se 1 (by rfl) ⟨1165505, by rfl⟩ : syracuseStep 1554007 = 2331011) B2331011
theorem B6993539 : Blo 1379509 6993539 := bstep (se 1 (by rfl) ⟨5245154, by rfl⟩ : syracuseStep 6993539 = 10490309) B10490309
theorem B2070155 : Blo 1379509 2070155 := bstep (se 1 (by rfl) ⟨1552616, by rfl⟩ : syracuseStep 2070155 = 3105233) B3105233
theorem B2070167 : Blo 1379509 2070167 := bstep (se 1 (by rfl) ⟨1552625, by rfl⟩ : syracuseStep 2070167 = 3105251) B3105251
theorem B3495575 : Blo 1379509 3495575 := bstep (se 1 (by rfl) ⟨2621681, by rfl⟩ : syracuseStep 3495575 = 5243363) B5243363
theorem B10082009 : Blo 1379509 10082009 := bstep (se 2 (by rfl) ⟨3780753, by rfl⟩ : syracuseStep 10082009 = 7561507) B7561507
theorem B2070233 : Blo 1379509 2070233 := bstep (se 2 (by rfl) ⟨776337, by rfl⟩ : syracuseStep 2070233 = 1552675) B1552675
theorem B1554187 : Blo 1379509 1554187 := bstep (se 1 (by rfl) ⟨1165640, by rfl⟩ : syracuseStep 1554187 = 2331281) B2331281
theorem B2946881 : Blo 1379509 2946881 := bstep (se 2 (by rfl) ⟨1105080, by rfl⟩ : syracuseStep 2946881 = 2210161) B2210161
theorem B5601089 : Blo 1379509 5601089 := bstep (se 2 (by rfl) ⟨2100408, by rfl⟩ : syracuseStep 5601089 = 4200817) B4200817
theorem B2070347 : Blo 1379509 2070347 := bstep (se 1 (by rfl) ⟨1552760, by rfl⟩ : syracuseStep 2070347 = 3105521) B3105521
theorem B2070359 : Blo 1379509 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B2070425 : Blo 1379509 2070425 := bstep (se 2 (by rfl) ⟨776409, by rfl⟩ : syracuseStep 2070425 = 1552819) B1552819
theorem B11794355 : Blo 1379509 11794355 := bstep (se 1 (by rfl) ⟨8845766, by rfl⟩ : syracuseStep 11794355 = 17691533) B17691533
theorem B2209751 : Blo 1379509 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B2070539 : Blo 1379509 2070539 := bstep (se 1 (by rfl) ⟨1552904, by rfl⟩ : syracuseStep 2070539 = 3105809) B3105809
theorem B2070551 : Blo 1379509 2070551 := bstep (se 1 (by rfl) ⟨1552913, by rfl⟩ : syracuseStep 2070551 = 3105827) B3105827
theorem B2799667 : Blo 1379509 2799667 := bstep (se 1 (by rfl) ⟨2099750, by rfl⟩ : syracuseStep 2799667 = 4199501) B4199501
theorem B2619479 : Blo 1379509 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B2070617 : Blo 1379509 2070617 := bstep (se 2 (by rfl) ⟨776481, by rfl⟩ : syracuseStep 2070617 = 1552963) B1552963
theorem B5240963 : Blo 1379509 5240963 := bstep (se 1 (by rfl) ⟨3930722, by rfl⟩ : syracuseStep 5240963 = 7861445) B7861445
theorem B2209943 : Blo 1379509 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B2070731 : Blo 1379509 2070731 := bstep (se 1 (by rfl) ⟨1553048, by rfl⟩ : syracuseStep 2070731 = 3106097) B3106097
theorem B2070743 : Blo 1379509 2070743 := bstep (se 1 (by rfl) ⟨1553057, by rfl⟩ : syracuseStep 2070743 = 3106115) B3106115
theorem B5593367 : Blo 1379509 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B2070809 : Blo 1379509 2070809 := bstep (se 2 (by rfl) ⟨776553, by rfl⟩ : syracuseStep 2070809 = 1553107) B1553107
theorem B11794733 : Blo 1379509 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B3496243 : Blo 1379509 3496243 := bstep (se 1 (by rfl) ⟨2622182, by rfl⟩ : syracuseStep 3496243 = 5244365) B5244365
theorem B7862629 : Blo 1379509 7862629 := bstep (se 4 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 7862629 = 1474243) B1474243
theorem B2070923 : Blo 1379509 2070923 := bstep (se 1 (by rfl) ⟨1553192, by rfl⟩ : syracuseStep 2070923 = 3106385) B3106385
theorem B2070935 : Blo 1379509 2070935 := bstep (se 1 (by rfl) ⟨1553201, by rfl⟩ : syracuseStep 2070935 = 3106403) B3106403
theorem B3496385 : Blo 1379509 3496385 := bstep (se 2 (by rfl) ⟨1311144, by rfl⟩ : syracuseStep 3496385 = 2622289) B2622289
theorem B4659659 : Blo 1379509 4659659 := bstep (se 1 (by rfl) ⟨3494744, by rfl⟩ : syracuseStep 4659659 = 6989489) B6989489
theorem B2071001 : Blo 1379509 2071001 := bstep (se 2 (by rfl) ⟨776625, by rfl⟩ : syracuseStep 2071001 = 1553251) B1553251
theorem B5241419 : Blo 1379509 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B2071115 : Blo 1379509 2071115 := bstep (se 1 (by rfl) ⟨1553336, by rfl⟩ : syracuseStep 2071115 = 3106673) B3106673
theorem B2071127 : Blo 1379509 2071127 := bstep (se 1 (by rfl) ⟨1553345, by rfl⟩ : syracuseStep 2071127 = 3106691) B3106691
theorem B2620019 : Blo 1379509 2620019 := bstep (se 1 (by rfl) ⟨1965014, by rfl⟩ : syracuseStep 2620019 = 3930029) B3930029
theorem B2071193 : Blo 1379509 2071193 := bstep (se 2 (by rfl) ⟨776697, by rfl⟩ : syracuseStep 2071193 = 1553395) B1553395
theorem B2489011 : Blo 1379509 2489011 := bstep (se 1 (by rfl) ⟨1866758, by rfl⟩ : syracuseStep 2489011 = 3733517) B3733517
theorem B3734209 : Blo 1379509 3734209 := bstep (se 2 (by rfl) ⟨1400328, by rfl⟩ : syracuseStep 3734209 = 2800657) B2800657
theorem B2210507 : Blo 1379509 2210507 := bstep (se 1 (by rfl) ⟨1657880, by rfl⟩ : syracuseStep 2210507 = 3315761) B3315761
theorem B4422347 : Blo 1379509 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B4659929 : Blo 1379509 4659929 := bstep (se 2 (by rfl) ⟨1747473, by rfl⟩ : syracuseStep 4659929 = 3494947) B3494947
theorem B2071307 : Blo 1379509 2071307 := bstep (se 1 (by rfl) ⟨1553480, by rfl⟩ : syracuseStep 2071307 = 3106961) B3106961
theorem B5241617 : Blo 1379509 5241617 := bstep (se 2 (by rfl) ⟨1965606, by rfl⟩ : syracuseStep 5241617 = 3931213) B3931213
theorem B2071319 : Blo 1379509 2071319 := bstep (se 1 (by rfl) ⟨1553489, by rfl⟩ : syracuseStep 2071319 = 3106979) B3106979
theorem B25549613 : Blo 1379509 25549613 := bstep (se 3 (by rfl) ⟨4790552, by rfl⟩ : syracuseStep 25549613 = 9581105) B9581105
theorem B2071385 : Blo 1379509 2071385 := bstep (se 2 (by rfl) ⟨776769, by rfl⟩ : syracuseStep 2071385 = 1553539) B1553539
theorem B2210699 : Blo 1379509 2210699 := bstep (se 1 (by rfl) ⟨1658024, by rfl⟩ : syracuseStep 2210699 = 3316049) B3316049
theorem B3931031 : Blo 1379509 3931031 := bstep (se 1 (by rfl) ⟨2948273, by rfl⟩ : syracuseStep 3931031 = 5896547) B5896547
theorem B2071499 : Blo 1379509 2071499 := bstep (se 1 (by rfl) ⟨1553624, by rfl⟩ : syracuseStep 2071499 = 3107249) B3107249
theorem B2071511 : Blo 1379509 2071511 := bstep (se 1 (by rfl) ⟨1553633, by rfl⟩ : syracuseStep 2071511 = 3107267) B3107267
theorem B2210827 : Blo 1379509 2210827 := bstep (se 1 (by rfl) ⟨1658120, by rfl⟩ : syracuseStep 2210827 = 3316241) B3316241
theorem B2071577 : Blo 1379509 2071577 := bstep (se 2 (by rfl) ⟨776841, by rfl⟩ : syracuseStep 2071577 = 1553683) B1553683
theorem B17685539 : Blo 1379509 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B63765539 : Blo 1379509 63765539 := bstep (se 1 (by rfl) ⟨47824154, by rfl⟩ : syracuseStep 63765539 = 95648309) B95648309
theorem B2800705 : Blo 1379509 2800705 := bstep (se 2 (by rfl) ⟨1050264, by rfl⟩ : syracuseStep 2800705 = 2100529) B2100529
theorem B1473611 : Blo 1379509 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B2620505 : Blo 1379509 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B2071691 : Blo 1379509 2071691 := bstep (se 1 (by rfl) ⟨1553768, by rfl⟩ : syracuseStep 2071691 = 3107537) B3107537
theorem B2071703 : Blo 1379509 2071703 := bstep (se 1 (by rfl) ⟨1553777, by rfl⟩ : syracuseStep 2071703 = 3107555) B3107555
theorem B3103937 : Blo 1379509 3103937 := bstep (se 2 (by rfl) ⟨1163976, by rfl⟩ : syracuseStep 3103937 = 2327953) B2327953
theorem B1965259 : Blo 1379509 1965259 := bstep (se 1 (by rfl) ⟨1473944, by rfl⟩ : syracuseStep 1965259 = 2947889) B2947889
theorem B2071769 : Blo 1379509 2071769 := bstep (se 2 (by rfl) ⟨776913, by rfl⟩ : syracuseStep 2071769 = 1553827) B1553827
theorem B2071883 : Blo 1379509 2071883 := bstep (se 1 (by rfl) ⟨1553912, by rfl⟩ : syracuseStep 2071883 = 3107825) B3107825
theorem B2071895 : Blo 1379509 2071895 := bstep (se 1 (by rfl) ⟨1553921, by rfl⟩ : syracuseStep 2071895 = 3107843) B3107843
theorem B4660631 : Blo 1379509 4660631 := bstep (se 1 (by rfl) ⟨3495473, by rfl⟩ : syracuseStep 4660631 = 6990947) B6990947
theorem B3104153 : Blo 1379509 3104153 := bstep (se 2 (by rfl) ⟨1164057, by rfl⟩ : syracuseStep 3104153 = 2328115) B2328115
theorem B2071961 : Blo 1379509 2071961 := bstep (se 2 (by rfl) ⟨776985, by rfl⟩ : syracuseStep 2071961 = 1553971) B1553971
theorem B2948555 : Blo 1379509 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B3104243 : Blo 1379509 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B2072075 : Blo 1379509 2072075 := bstep (se 1 (by rfl) ⟨1554056, by rfl⟩ : syracuseStep 2072075 = 3108113) B3108113
theorem B3104279 : Blo 1379509 3104279 := bstep (se 1 (by rfl) ⟨2328209, by rfl⟩ : syracuseStep 3104279 = 4656419) B4656419
theorem B5242391 : Blo 1379509 5242391 := bstep (se 1 (by rfl) ⟨3931793, by rfl⟩ : syracuseStep 5242391 = 7863587) B7863587
theorem B2072087 : Blo 1379509 2072087 := bstep (se 1 (by rfl) ⟨1554065, by rfl⟩ : syracuseStep 2072087 = 3108131) B3108131
theorem B19914275 : Blo 1379509 19914275 := bstep (se 1 (by rfl) ⟨14935706, by rfl⟩ : syracuseStep 19914275 = 29871413) B29871413
theorem B5045825 : Blo 1379509 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B2072153 : Blo 1379509 2072153 := bstep (se 2 (by rfl) ⟨777057, by rfl⟩ : syracuseStep 2072153 = 1554115) B1554115
theorem B7462493 : Blo 1379509 7462493 := bstep (se 3 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 7462493 = 2798435) B2798435
theorem B10477187 : Blo 1379509 10477187 := bstep (se 1 (by rfl) ⟨7857890, by rfl⟩ : syracuseStep 10477187 = 15715781) B15715781
theorem B2211467 : Blo 1379509 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B3104459 : Blo 1379509 3104459 := bstep (se 1 (by rfl) ⟨2328344, by rfl⟩ : syracuseStep 3104459 = 4656689) B4656689
theorem B2211545 : Blo 1379509 2211545 := bstep (se 2 (by rfl) ⟨829329, by rfl⟩ : syracuseStep 2211545 = 1658659) B1658659
theorem B5242589 : Blo 1379509 5242589 := bstep (se 3 (by rfl) ⟨982985, by rfl⟩ : syracuseStep 5242589 = 1965971) B1965971
theorem B3104513 : Blo 1379509 3104513 := bstep (se 2 (by rfl) ⟨1164192, by rfl⟩ : syracuseStep 3104513 = 2328385) B2328385
theorem B4423447 : Blo 1379509 4423447 := bstep (se 1 (by rfl) ⟨3317585, by rfl⟩ : syracuseStep 4423447 = 6635171) B6635171
theorem B4661171 : Blo 1379509 4661171 := bstep (se 1 (by rfl) ⟨3495878, by rfl⟩ : syracuseStep 4661171 = 6991757) B6991757
theorem B3104729 : Blo 1379509 3104729 := bstep (se 2 (by rfl) ⟨1164273, by rfl⟩ : syracuseStep 3104729 = 2328547) B2328547
theorem B3104783 : Blo 1379509 3104783 := bstep (se 1 (by rfl) ⟨2328587, by rfl⟩ : syracuseStep 3104783 = 4657175) B4657175
theorem B3104801 : Blo 1379509 3104801 := bstep (se 2 (by rfl) ⟨1164300, by rfl⟩ : syracuseStep 3104801 = 2328601) B2328601
theorem B1474619 : Blo 1379509 1474619 := bstep (se 1 (by rfl) ⟨1105964, by rfl⟩ : syracuseStep 1474619 = 2211929) B2211929
theorem B2621575 : Blo 1379509 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B7463183 : Blo 1379509 7463183 := bstep (se 1 (by rfl) ⟨5597387, by rfl⟩ : syracuseStep 7463183 = 11194775) B11194775
theorem B2949409 : Blo 1379509 2949409 := bstep (se 2 (by rfl) ⟨1106028, by rfl⟩ : syracuseStep 2949409 = 2212057) B2212057
theorem B7864613 : Blo 1379509 7864613 := bstep (se 4 (by rfl) ⟨737307, by rfl⟩ : syracuseStep 7864613 = 1474615) B1474615
theorem B7176563 : Blo 1379509 7176563 := bstep (se 1 (by rfl) ⟨5382422, by rfl⟩ : syracuseStep 7176563 = 10764845) B10764845
theorem B4424051 : Blo 1379509 4424051 := bstep (se 1 (by rfl) ⟨3318038, by rfl⟩ : syracuseStep 4424051 = 6636077) B6636077
theorem B3105143 : Blo 1379509 3105143 := bstep (se 1 (by rfl) ⟨2328857, by rfl⟩ : syracuseStep 3105143 = 4657715) B4657715
theorem B4661657 : Blo 1379509 4661657 := bstep (se 2 (by rfl) ⟨1748121, by rfl⟩ : syracuseStep 4661657 = 3496243) B3496243
theorem B1966523 : Blo 1379509 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B7463447 : Blo 1379509 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B8962589 : Blo 1379509 8962589 := bstep (se 3 (by rfl) ⟨1680485, by rfl⟩ : syracuseStep 8962589 = 3360971) B3360971
theorem B3932705 : Blo 1379509 3932705 := bstep (se 2 (by rfl) ⟨1474764, by rfl⟩ : syracuseStep 3932705 = 2949529) B2949529
theorem B3105323 : Blo 1379509 3105323 := bstep (se 1 (by rfl) ⟨2328992, by rfl⟩ : syracuseStep 3105323 = 4657985) B4657985
theorem B13263425 : Blo 1379509 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B6988355 : Blo 1379509 6988355 := bstep (se 1 (by rfl) ⟨5241266, by rfl⟩ : syracuseStep 6988355 = 10482533) B10482533
theorem B3932819 : Blo 1379509 3932819 := bstep (se 1 (by rfl) ⟨2949614, by rfl⟩ : syracuseStep 3932819 = 5899229) B5899229
theorem B1680043 : Blo 1379509 1680043 := bstep (se 1 (by rfl) ⟨1260032, by rfl⟩ : syracuseStep 1680043 = 2520065) B2520065
theorem B218170097 : Blo 1379509 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B6988679 : Blo 1379509 6988679 := bstep (se 1 (by rfl) ⟨5241509, by rfl⟩ : syracuseStep 6988679 = 10483019) B10483019
theorem B4195219 : Blo 1379509 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B3105683 : Blo 1379509 3105683 := bstep (se 1 (by rfl) ⟨2329262, by rfl⟩ : syracuseStep 3105683 = 4658525) B4658525
theorem B3105737 : Blo 1379509 3105737 := bstep (se 2 (by rfl) ⟨1164651, by rfl⟩ : syracuseStep 3105737 = 2329303) B2329303
theorem B5899331 : Blo 1379509 5899331 := bstep (se 1 (by rfl) ⟨4424498, by rfl⟩ : syracuseStep 5899331 = 8848997) B8848997
theorem B4195415 : Blo 1379509 4195415 := bstep (se 1 (by rfl) ⟨3146561, by rfl⟩ : syracuseStep 4195415 = 6293123) B6293123
theorem B4662359 : Blo 1379509 4662359 := bstep (se 1 (by rfl) ⟨3496769, by rfl⟩ : syracuseStep 4662359 = 6993539) B6993539
theorem B8512705 : Blo 1379509 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B15549641 : Blo 1379509 15549641 := bstep (se 2 (by rfl) ⟨5831115, by rfl⟩ : syracuseStep 15549641 = 11662231) B11662231
theorem B7865545 : Blo 1379509 7865545 := bstep (se 2 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 7865545 = 5899159) B5899159
theorem B3933593 : Blo 1379509 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B3728911 : Blo 1379509 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B11798045 : Blo 1379509 11798045 := bstep (se 3 (by rfl) ⟨2212133, by rfl⟩ : syracuseStep 11798045 = 4424267) B4424267
theorem B3106439 : Blo 1379509 3106439 := bstep (se 1 (by rfl) ⟨2329829, by rfl⟩ : syracuseStep 3106439 = 4659659) B4659659
theorem B1746679 : Blo 1379509 1746679 := bstep (se 1 (by rfl) ⟨1310009, by rfl⟩ : syracuseStep 1746679 = 2620019) B2620019
theorem B3106619 : Blo 1379509 3106619 := bstep (se 1 (by rfl) ⟨2329964, by rfl⟩ : syracuseStep 3106619 = 4659929) B4659929
theorem B17033075 : Blo 1379509 17033075 := bstep (se 1 (by rfl) ⟨12774806, by rfl⟩ : syracuseStep 17033075 = 25549613) B25549613
theorem B2328439 : Blo 1379509 2328439 := bstep (se 1 (by rfl) ⟨1746329, by rfl⟩ : syracuseStep 2328439 = 3492659) B3492659
theorem B7858073 : Blo 1379509 7858073 := bstep (se 2 (by rfl) ⟨2946777, by rfl⟩ : syracuseStep 7858073 = 5893555) B5893555
theorem B3106745 : Blo 1379509 3106745 := bstep (se 2 (by rfl) ⟨1165029, by rfl⟩ : syracuseStep 3106745 = 2330059) B2330059
theorem B11790359 : Blo 1379509 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B42510359 : Blo 1379509 42510359 := bstep (se 1 (by rfl) ⟨31882769, by rfl⟩ : syracuseStep 42510359 = 63765539) B63765539
theorem B2328635 : Blo 1379509 2328635 := bstep (se 1 (by rfl) ⟨1746476, by rfl⟩ : syracuseStep 2328635 = 3492953) B3492953
theorem B1747003 : Blo 1379509 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B11798729 : Blo 1379509 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B3107087 : Blo 1379509 3107087 := bstep (se 1 (by rfl) ⟨2330315, by rfl⟩ : syracuseStep 3107087 = 4660631) B4660631
theorem B3107105 : Blo 1379509 3107105 := bstep (se 2 (by rfl) ⟨1165164, by rfl⟩ : syracuseStep 3107105 = 2330329) B2330329
theorem B4974995 : Blo 1379509 4974995 := bstep (se 1 (by rfl) ⟨3731246, by rfl⟩ : syracuseStep 4974995 = 7462493) B7462493
theorem B33606035 : Blo 1379509 33606035 := bstep (se 1 (by rfl) ⟨25204526, by rfl⟩ : syracuseStep 33606035 = 50409053) B50409053
theorem B5245337 : Blo 1379509 5245337 := bstep (se 2 (by rfl) ⟨1967001, by rfl⟩ : syracuseStep 5245337 = 3934003) B3934003
theorem B2329033 : Blo 1379509 2329033 := bstep (se 2 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 2329033 = 1746775) B1746775
theorem B5974589 : Blo 1379509 5974589 := bstep (se 3 (by rfl) ⟨1120235, by rfl⟩ : syracuseStep 5974589 = 2240471) B2240471
theorem B11799107 : Blo 1379509 11799107 := bstep (se 1 (by rfl) ⟨8849330, by rfl⟩ : syracuseStep 11799107 = 17698661) B17698661
theorem B3983959 : Blo 1379509 3983959 := bstep (se 1 (by rfl) ⟨2987969, by rfl⟩ : syracuseStep 3983959 = 5975939) B5975939
theorem B3492467 : Blo 1379509 3492467 := bstep (se 1 (by rfl) ⟨2619350, by rfl⟩ : syracuseStep 3492467 = 5238701) B5238701
theorem B3107447 : Blo 1379509 3107447 := bstep (se 1 (by rfl) ⟨2330585, by rfl⟩ : syracuseStep 3107447 = 4661171) B4661171
theorem B3107627 : Blo 1379509 3107627 := bstep (se 1 (by rfl) ⟨2330720, by rfl⟩ : syracuseStep 3107627 = 4661441) B4661441
theorem B4655987 : Blo 1379509 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B3730295 : Blo 1379509 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B8850379 : Blo 1379509 8850379 := bstep (se 1 (by rfl) ⟨6637784, by rfl⟩ : syracuseStep 8850379 = 13275569) B13275569
theorem B45419525 : Blo 1379509 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B1747975 : Blo 1379509 1747975 := bstep (se 1 (by rfl) ⟨1310981, by rfl⟩ : syracuseStep 1747975 = 2621963) B2621963
theorem B12594199 : Blo 1379509 12594199 := bstep (se 1 (by rfl) ⟨9445649, by rfl⟩ : syracuseStep 12594199 = 18891299) B18891299
theorem B5893181 : Blo 1379509 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B3492983 : Blo 1379509 3492983 := bstep (se 1 (by rfl) ⟨2619737, by rfl⟩ : syracuseStep 3492983 = 5239475) B5239475
theorem B2329735 : Blo 1379509 2329735 := bstep (se 1 (by rfl) ⟨1747301, by rfl⟩ : syracuseStep 2329735 = 3494603) B3494603
theorem B59681933 : Blo 1379509 59681933 := bstep (se 3 (by rfl) ⟨11190362, by rfl⟩ : syracuseStep 59681933 = 22380725) B22380725
theorem B3107987 : Blo 1379509 3107987 := bstep (se 1 (by rfl) ⟨2330990, by rfl⟩ : syracuseStep 3107987 = 4661981) B4661981
theorem B1379515 : Blo 1379509 1379515 := bstep (se 1 (by rfl) ⟨1034636, by rfl⟩ : syracuseStep 1379515 = 2069273) B2069273
theorem B3108041 : Blo 1379509 3108041 := bstep (se 2 (by rfl) ⟨1165515, by rfl⟩ : syracuseStep 3108041 = 2331031) B2331031
theorem B5238017 : Blo 1379509 5238017 := bstep (se 2 (by rfl) ⟨1964256, by rfl⟩ : syracuseStep 5238017 = 3928513) B3928513
theorem B1379591 : Blo 1379509 1379591 := bstep (se 1 (by rfl) ⟨1034693, by rfl⟩ : syracuseStep 1379591 = 2069387) B2069387
theorem B1379599 : Blo 1379509 1379599 := bstep (se 1 (by rfl) ⟨1034699, by rfl⟩ : syracuseStep 1379599 = 2069399) B2069399
theorem B2657551 : Blo 1379509 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B1379643 : Blo 1379509 1379643 := bstep (se 1 (by rfl) ⟨1034732, by rfl⟩ : syracuseStep 1379643 = 2069465) B2069465
theorem B8391995 : Blo 1379509 8391995 := bstep (se 1 (by rfl) ⟨6293996, by rfl⟩ : syracuseStep 8391995 = 12587993) B12587993
theorem B1379719 : Blo 1379509 1379719 := bstep (se 1 (by rfl) ⟨1034789, by rfl⟩ : syracuseStep 1379719 = 2069579) B2069579
theorem B1379727 : Blo 1379509 1379727 := bstep (se 1 (by rfl) ⟨1034795, by rfl⟩ : syracuseStep 1379727 = 2069591) B2069591
theorem B1748395 : Blo 1379509 1748395 := bstep (se 1 (by rfl) ⟨1311296, by rfl⟩ : syracuseStep 1748395 = 2622593) B2622593
theorem B1379771 : Blo 1379509 1379771 := bstep (se 1 (by rfl) ⟨1034828, by rfl⟩ : syracuseStep 1379771 = 2069657) B2069657
theorem B1379847 : Blo 1379509 1379847 := bstep (se 1 (by rfl) ⟨1034885, by rfl⟩ : syracuseStep 1379847 = 2069771) B2069771
theorem B1379855 : Blo 1379509 1379855 := bstep (se 1 (by rfl) ⟨1034891, by rfl⟩ : syracuseStep 1379855 = 2069783) B2069783
theorem B1379899 : Blo 1379509 1379899 := bstep (se 1 (by rfl) ⟨1034924, by rfl⟩ : syracuseStep 1379899 = 2069849) B2069849
theorem B13274725 : Blo 1379509 13274725 := bstep (se 4 (by rfl) ⟨1244505, by rfl⟩ : syracuseStep 13274725 = 2489011) B2489011
theorem B9440887 : Blo 1379509 9440887 := bstep (se 1 (by rfl) ⟨7080665, by rfl⟩ : syracuseStep 9440887 = 14161331) B14161331
theorem B1379975 : Blo 1379509 1379975 := bstep (se 1 (by rfl) ⟨1034981, by rfl⟩ : syracuseStep 1379975 = 2069963) B2069963
theorem B1379983 : Blo 1379509 1379983 := bstep (se 1 (by rfl) ⟨1034987, by rfl⟩ : syracuseStep 1379983 = 2069975) B2069975
theorem B1380027 : Blo 1379509 1380027 := bstep (se 1 (by rfl) ⟨1035020, by rfl⟩ : syracuseStep 1380027 = 2070041) B2070041
theorem B1552135 : Blo 1379509 1552135 := bstep (se 1 (by rfl) ⟨1164101, by rfl⟩ : syracuseStep 1552135 = 2328203) B2328203
theorem B1380103 : Blo 1379509 1380103 := bstep (se 1 (by rfl) ⟨1035077, by rfl⟩ : syracuseStep 1380103 = 2070155) B2070155
theorem B1380111 : Blo 1379509 1380111 := bstep (se 1 (by rfl) ⟨1035083, by rfl⟩ : syracuseStep 1380111 = 2070167) B2070167
theorem B2330383 : Blo 1379509 2330383 := bstep (se 1 (by rfl) ⟨1747787, by rfl⟩ : syracuseStep 2330383 = 3495575) B3495575
theorem B6721339 : Blo 1379509 6721339 := bstep (se 1 (by rfl) ⟨5041004, by rfl⟩ : syracuseStep 6721339 = 10082009) B10082009
theorem B1380155 : Blo 1379509 1380155 := bstep (se 1 (by rfl) ⟨1035116, by rfl⟩ : syracuseStep 1380155 = 2070233) B2070233
theorem B1380231 : Blo 1379509 1380231 := bstep (se 1 (by rfl) ⟨1035173, by rfl⟩ : syracuseStep 1380231 = 2070347) B2070347
theorem B1380239 : Blo 1379509 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B10481561 : Blo 1379509 10481561 := bstep (se 2 (by rfl) ⟨3930585, by rfl⟩ : syracuseStep 10481561 = 7861171) B7861171
theorem B1552315 : Blo 1379509 1552315 := bstep (se 1 (by rfl) ⟨1164236, by rfl⟩ : syracuseStep 1552315 = 2328473) B2328473
theorem B1380283 : Blo 1379509 1380283 := bstep (se 1 (by rfl) ⟨1035212, by rfl⟩ : syracuseStep 1380283 = 2070425) B2070425
theorem B1380359 : Blo 1379509 1380359 := bstep (se 1 (by rfl) ⟨1035269, by rfl⟩ : syracuseStep 1380359 = 2070539) B2070539
theorem B26521613 : Blo 1379509 26521613 := bstep (se 3 (by rfl) ⟨4972802, by rfl⟩ : syracuseStep 26521613 = 9945605) B9945605
theorem B1380367 : Blo 1379509 1380367 := bstep (se 1 (by rfl) ⟨1035275, by rfl⟩ : syracuseStep 1380367 = 2070551) B2070551
theorem B1380411 : Blo 1379509 1380411 := bstep (se 1 (by rfl) ⟨1035308, by rfl⟩ : syracuseStep 1380411 = 2070617) B2070617
theorem B3493975 : Blo 1379509 3493975 := bstep (se 1 (by rfl) ⟨2620481, by rfl⟩ : syracuseStep 3493975 = 5240963) B5240963
theorem B53104733 : Blo 1379509 53104733 := bstep (se 3 (by rfl) ⟨9957137, by rfl⟩ : syracuseStep 53104733 = 19914275) B19914275
theorem B23588981 : Blo 1379509 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B1380487 : Blo 1379509 1380487 := bstep (se 1 (by rfl) ⟨1035365, by rfl⟩ : syracuseStep 1380487 = 2070731) B2070731
theorem B1380495 : Blo 1379509 1380495 := bstep (se 1 (by rfl) ⟨1035371, by rfl⟩ : syracuseStep 1380495 = 2070743) B2070743
theorem B13455533 : Blo 1379509 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B1380539 : Blo 1379509 1380539 := bstep (se 1 (by rfl) ⟨1035404, by rfl⟩ : syracuseStep 1380539 = 2070809) B2070809
theorem B1380615 : Blo 1379509 1380615 := bstep (se 1 (by rfl) ⟨1035461, by rfl⟩ : syracuseStep 1380615 = 2070923) B2070923
theorem B1380623 : Blo 1379509 1380623 := bstep (se 1 (by rfl) ⟨1035467, by rfl⟩ : syracuseStep 1380623 = 2070935) B2070935
theorem B2330923 : Blo 1379509 2330923 := bstep (se 1 (by rfl) ⟨1748192, by rfl⟩ : syracuseStep 2330923 = 3496385) B3496385
theorem B1380667 : Blo 1379509 1380667 := bstep (se 1 (by rfl) ⟨1035500, by rfl⟩ : syracuseStep 1380667 = 2071001) B2071001
theorem B6992243 : Blo 1379509 6992243 := bstep (se 1 (by rfl) ⟨5244182, by rfl⟩ : syracuseStep 6992243 = 10488365) B10488365
theorem B3494279 : Blo 1379509 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B1380743 : Blo 1379509 1380743 := bstep (se 1 (by rfl) ⟨1035557, by rfl⟩ : syracuseStep 1380743 = 2071115) B2071115
theorem B1552783 : Blo 1379509 1552783 := bstep (se 1 (by rfl) ⟨1164587, by rfl⟩ : syracuseStep 1552783 = 2329175) B2329175
theorem B1380751 : Blo 1379509 1380751 := bstep (se 1 (by rfl) ⟨1035563, by rfl⟩ : syracuseStep 1380751 = 2071127) B2071127
theorem B5239187 : Blo 1379509 5239187 := bstep (se 1 (by rfl) ⟨3929390, by rfl⟩ : syracuseStep 5239187 = 7858781) B7858781
theorem B6631865 : Blo 1379509 6631865 := bstep (se 2 (by rfl) ⟨2486949, by rfl⟩ : syracuseStep 6631865 = 4973899) B4973899
theorem B2331065 : Blo 1379509 2331065 := bstep (se 2 (by rfl) ⟨874149, by rfl⟩ : syracuseStep 2331065 = 1748299) B1748299
theorem B1380795 : Blo 1379509 1380795 := bstep (se 1 (by rfl) ⟨1035596, by rfl⟩ : syracuseStep 1380795 = 2071193) B2071193
theorem B13267421 : Blo 1379509 13267421 := bstep (se 3 (by rfl) ⟨2487641, by rfl⟩ : syracuseStep 13267421 = 4975283) B4975283
theorem B1380871 : Blo 1379509 1380871 := bstep (se 1 (by rfl) ⟨1035653, by rfl⟩ : syracuseStep 1380871 = 2071307) B2071307
theorem B3494411 : Blo 1379509 3494411 := bstep (se 1 (by rfl) ⟨2620808, by rfl⟩ : syracuseStep 3494411 = 5241617) B5241617
theorem B1380879 : Blo 1379509 1380879 := bstep (se 1 (by rfl) ⟨1035659, by rfl⟩ : syracuseStep 1380879 = 2071319) B2071319
theorem B15733277 : Blo 1379509 15733277 := bstep (se 3 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 15733277 = 5899979) B5899979
theorem B1380923 : Blo 1379509 1380923 := bstep (se 1 (by rfl) ⟨1035692, by rfl⟩ : syracuseStep 1380923 = 2071385) B2071385
theorem B7565885 : Blo 1379509 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B1380999 : Blo 1379509 1380999 := bstep (se 1 (by rfl) ⟨1035749, by rfl⟩ : syracuseStep 1380999 = 2071499) B2071499
theorem B1381007 : Blo 1379509 1381007 := bstep (se 1 (by rfl) ⟨1035755, by rfl⟩ : syracuseStep 1381007 = 2071511) B2071511
theorem B1381051 : Blo 1379509 1381051 := bstep (se 1 (by rfl) ⟨1035788, by rfl⟩ : syracuseStep 1381051 = 2071577) B2071577
theorem B1381127 : Blo 1379509 1381127 := bstep (se 1 (by rfl) ⟨1035845, by rfl⟩ : syracuseStep 1381127 = 2071691) B2071691
theorem B1381135 : Blo 1379509 1381135 := bstep (se 1 (by rfl) ⟨1035851, by rfl⟩ : syracuseStep 1381135 = 2071703) B2071703
theorem B2798369 : Blo 1379509 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B2069291 : Blo 1379509 2069291 := bstep (se 1 (by rfl) ⟨1551968, by rfl⟩ : syracuseStep 2069291 = 3103937) B3103937
theorem B1381179 : Blo 1379509 1381179 := bstep (se 1 (by rfl) ⟨1035884, by rfl⟩ : syracuseStep 1381179 = 2071769) B2071769
theorem B2069321 : Blo 1379509 2069321 := bstep (se 2 (by rfl) ⟨775995, by rfl⟩ : syracuseStep 2069321 = 1551991) B1551991
theorem B6992729 : Blo 1379509 6992729 := bstep (se 2 (by rfl) ⟨2622273, by rfl⟩ : syracuseStep 6992729 = 5244547) B5244547
theorem B5239687 : Blo 1379509 5239687 := bstep (se 1 (by rfl) ⟨3929765, by rfl⟩ : syracuseStep 5239687 = 7859531) B7859531
theorem B1553287 : Blo 1379509 1553287 := bstep (se 1 (by rfl) ⟨1164965, by rfl⟩ : syracuseStep 1553287 = 2329931) B2329931
theorem B1381255 : Blo 1379509 1381255 := bstep (se 1 (by rfl) ⟨1035941, by rfl⟩ : syracuseStep 1381255 = 2071883) B2071883
theorem B1381263 : Blo 1379509 1381263 := bstep (se 1 (by rfl) ⟨1035947, by rfl⟩ : syracuseStep 1381263 = 2071895) B2071895
theorem B3732371 : Blo 1379509 3732371 := bstep (se 1 (by rfl) ⟨2799278, by rfl⟩ : syracuseStep 3732371 = 5598557) B5598557
theorem B2069435 : Blo 1379509 2069435 := bstep (se 1 (by rfl) ⟨1552076, by rfl⟩ : syracuseStep 2069435 = 3104153) B3104153
theorem B1381307 : Blo 1379509 1381307 := bstep (se 1 (by rfl) ⟨1035980, by rfl⟩ : syracuseStep 1381307 = 2071961) B2071961
theorem B2069495 : Blo 1379509 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B1381383 : Blo 1379509 1381383 := bstep (se 1 (by rfl) ⟨1036037, by rfl⟩ : syracuseStep 1381383 = 2072075) B2072075
theorem B2069519 : Blo 1379509 2069519 := bstep (se 1 (by rfl) ⟨1552139, by rfl⟩ : syracuseStep 2069519 = 3104279) B3104279
theorem B3494927 : Blo 1379509 3494927 := bstep (se 1 (by rfl) ⟨2621195, by rfl⟩ : syracuseStep 3494927 = 5242391) B5242391
theorem B1381391 : Blo 1379509 1381391 := bstep (se 1 (by rfl) ⟨1036043, by rfl⟩ : syracuseStep 1381391 = 2072087) B2072087
theorem B2069561 : Blo 1379509 2069561 := bstep (se 2 (by rfl) ⟨776085, by rfl⟩ : syracuseStep 2069561 = 1552171) B1552171
theorem B1553467 : Blo 1379509 1553467 := bstep (se 1 (by rfl) ⟨1165100, by rfl⟩ : syracuseStep 1553467 = 2330201) B2330201
theorem B1381435 : Blo 1379509 1381435 := bstep (se 1 (by rfl) ⟨1036076, by rfl⟩ : syracuseStep 1381435 = 2072153) B2072153
theorem B6984791 : Blo 1379509 6984791 := bstep (se 1 (by rfl) ⟨5238593, by rfl⟩ : syracuseStep 6984791 = 10477187) B10477187
theorem B2069639 : Blo 1379509 2069639 := bstep (se 1 (by rfl) ⟨1552229, by rfl⟩ : syracuseStep 2069639 = 3104459) B3104459
theorem B3495059 : Blo 1379509 3495059 := bstep (se 1 (by rfl) ⟨2621294, by rfl⟩ : syracuseStep 3495059 = 5242589) B5242589
theorem B2069675 : Blo 1379509 2069675 := bstep (se 1 (by rfl) ⟨1552256, by rfl⟩ : syracuseStep 2069675 = 3104513) B3104513
theorem B2069705 : Blo 1379509 2069705 := bstep (se 2 (by rfl) ⟨776139, by rfl⟩ : syracuseStep 2069705 = 1552279) B1552279
theorem B2069819 : Blo 1379509 2069819 := bstep (se 1 (by rfl) ⟨1552364, by rfl⟩ : syracuseStep 2069819 = 3104729) B3104729
theorem B2069879 : Blo 1379509 2069879 := bstep (se 1 (by rfl) ⟨1552409, by rfl⟩ : syracuseStep 2069879 = 3104819) B3104819
theorem B11785607 : Blo 1379509 11785607 := bstep (se 1 (by rfl) ⟨8839205, by rfl⟩ : syracuseStep 11785607 = 17678411) B17678411
theorem B2069903 : Blo 1379509 2069903 := bstep (se 1 (by rfl) ⟨1552427, by rfl⟩ : syracuseStep 2069903 = 3104855) B3104855
theorem B4658579 : Blo 1379509 4658579 := bstep (se 1 (by rfl) ⟨3493934, by rfl⟩ : syracuseStep 4658579 = 6987869) B6987869
theorem B3732889 : Blo 1379509 3732889 := bstep (se 2 (by rfl) ⟨1399833, by rfl⟩ : syracuseStep 3732889 = 2799667) B2799667
theorem B2069945 : Blo 1379509 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B9442745 : Blo 1379509 9442745 := bstep (se 2 (by rfl) ⟨3541029, by rfl⟩ : syracuseStep 9442745 = 7082059) B7082059
theorem B2070023 : Blo 1379509 2070023 := bstep (se 1 (by rfl) ⟨1552517, by rfl⟩ : syracuseStep 2070023 = 3105035) B3105035
theorem B1553935 : Blo 1379509 1553935 := bstep (se 1 (by rfl) ⟨1165451, by rfl⟩ : syracuseStep 1553935 = 2330903) B2330903
theorem B3929629 : Blo 1379509 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B2070059 : Blo 1379509 2070059 := bstep (se 1 (by rfl) ⟨1552544, by rfl⟩ : syracuseStep 2070059 = 3105089) B3105089
theorem B6985277 : Blo 1379509 6985277 := bstep (se 3 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 6985277 = 2619479) B2619479
theorem B2070089 : Blo 1379509 2070089 := bstep (se 2 (by rfl) ⟨776283, by rfl⟩ : syracuseStep 2070089 = 1552567) B1552567
theorem B1865359 : Blo 1379509 1865359 := bstep (se 1 (by rfl) ⟨1399019, by rfl⟩ : syracuseStep 1865359 = 2798039) B2798039
theorem B2070203 : Blo 1379509 2070203 := bstep (se 1 (by rfl) ⟨1552652, by rfl⟩ : syracuseStep 2070203 = 3105305) B3105305
theorem B2070263 : Blo 1379509 2070263 := bstep (se 1 (by rfl) ⟨1552697, by rfl⟩ : syracuseStep 2070263 = 3105395) B3105395
theorem B11785985 : Blo 1379509 11785985 := bstep (se 2 (by rfl) ⟨4419744, by rfl⟩ : syracuseStep 11785985 = 8839489) B8839489
theorem B2070287 : Blo 1379509 2070287 := bstep (se 1 (by rfl) ⟨1552715, by rfl⟩ : syracuseStep 2070287 = 3105431) B3105431
theorem B13268771 : Blo 1379509 13268771 := bstep (se 1 (by rfl) ⟨9951578, by rfl⟩ : syracuseStep 13268771 = 19903157) B19903157
theorem B10483505 : Blo 1379509 10483505 := bstep (se 2 (by rfl) ⟨3931314, by rfl⟩ : syracuseStep 10483505 = 7862629) B7862629
theorem B2070329 : Blo 1379509 2070329 := bstep (se 2 (by rfl) ⟨776373, by rfl⟩ : syracuseStep 2070329 = 1552747) B1552747
theorem B3929971 : Blo 1379509 3929971 := bstep (se 1 (by rfl) ⟨2947478, by rfl⟩ : syracuseStep 3929971 = 5894957) B5894957
theorem B2070407 : Blo 1379509 2070407 := bstep (se 1 (by rfl) ⟨1552805, by rfl⟩ : syracuseStep 2070407 = 3105611) B3105611
theorem B2070443 : Blo 1379509 2070443 := bstep (se 1 (by rfl) ⟨1552832, by rfl⟩ : syracuseStep 2070443 = 3105665) B3105665
theorem B2070473 : Blo 1379509 2070473 := bstep (se 2 (by rfl) ⟨776427, by rfl⟩ : syracuseStep 2070473 = 1552855) B1552855
theorem B2070587 : Blo 1379509 2070587 := bstep (se 1 (by rfl) ⟨1552940, by rfl⟩ : syracuseStep 2070587 = 3105881) B3105881
theorem B2070647 : Blo 1379509 2070647 := bstep (se 1 (by rfl) ⟨1552985, by rfl⟩ : syracuseStep 2070647 = 3105971) B3105971
theorem B2070671 : Blo 1379509 2070671 := bstep (se 1 (by rfl) ⟨1553003, by rfl⟩ : syracuseStep 2070671 = 3106007) B3106007
theorem B2070713 : Blo 1379509 2070713 := bstep (se 2 (by rfl) ⟨776517, by rfl⟩ : syracuseStep 2070713 = 1553035) B1553035
theorem B3496193 : Blo 1379509 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B4978945 : Blo 1379509 4978945 := bstep (se 2 (by rfl) ⟨1867104, by rfl⟩ : syracuseStep 4978945 = 3734209) B3734209
theorem B2070791 : Blo 1379509 2070791 := bstep (se 1 (by rfl) ⟨1553093, by rfl⟩ : syracuseStep 2070791 = 3106187) B3106187
theorem B2070827 : Blo 1379509 2070827 := bstep (se 1 (by rfl) ⟨1553120, by rfl⟩ : syracuseStep 2070827 = 3106241) B3106241
theorem B2070857 : Blo 1379509 2070857 := bstep (se 2 (by rfl) ⟨776571, by rfl⟩ : syracuseStep 2070857 = 1553143) B1553143
theorem B2070971 : Blo 1379509 2070971 := bstep (se 1 (by rfl) ⟨1553228, by rfl⟩ : syracuseStep 2070971 = 3106457) B3106457
theorem B2071031 : Blo 1379509 2071031 := bstep (se 1 (by rfl) ⟨1553273, by rfl⟩ : syracuseStep 2071031 = 3106547) B3106547
theorem B9443843 : Blo 1379509 9443843 := bstep (se 1 (by rfl) ⟨7082882, by rfl⟩ : syracuseStep 9443843 = 14165765) B14165765
theorem B2071055 : Blo 1379509 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B1964587 : Blo 1379509 1964587 := bstep (se 1 (by rfl) ⟨1473440, by rfl⟩ : syracuseStep 1964587 = 2946881) B2946881
theorem B3734059 : Blo 1379509 3734059 := bstep (se 1 (by rfl) ⟨2800544, by rfl⟩ : syracuseStep 3734059 = 5601089) B5601089
theorem B2071097 : Blo 1379509 2071097 := bstep (se 2 (by rfl) ⟨776661, by rfl⟩ : syracuseStep 2071097 = 1553323) B1553323
theorem B4422205 : Blo 1379509 4422205 := bstep (se 3 (by rfl) ⟨829163, by rfl⟩ : syracuseStep 4422205 = 1658327) B1658327
theorem B7862903 : Blo 1379509 7862903 := bstep (se 1 (by rfl) ⟨5897177, by rfl⟩ : syracuseStep 7862903 = 11794355) B11794355
theorem B3496567 : Blo 1379509 3496567 := bstep (se 1 (by rfl) ⟨2622425, by rfl⟩ : syracuseStep 3496567 = 5244851) B5244851
theorem B2071175 : Blo 1379509 2071175 := bstep (se 1 (by rfl) ⟨1553381, by rfl⟩ : syracuseStep 2071175 = 3106763) B3106763
theorem B1473167 : Blo 1379509 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B2071211 : Blo 1379509 2071211 := bstep (se 1 (by rfl) ⟨1553408, by rfl⟩ : syracuseStep 2071211 = 3106817) B3106817
theorem B2947769 : Blo 1379509 2947769 := bstep (se 2 (by rfl) ⟨1105413, by rfl⟩ : syracuseStep 2947769 = 2210827) B2210827
theorem B2071241 : Blo 1379509 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B3734273 : Blo 1379509 3734273 := bstep (se 2 (by rfl) ⟨1400352, by rfl⟩ : syracuseStep 3734273 = 2800705) B2800705
theorem B4659983 : Blo 1379509 4659983 := bstep (se 1 (by rfl) ⟨3494987, by rfl⟩ : syracuseStep 4659983 = 6989975) B6989975
theorem B2071355 : Blo 1379509 2071355 := bstep (se 1 (by rfl) ⟨1553516, by rfl⟩ : syracuseStep 2071355 = 3107033) B3107033
theorem B7863155 : Blo 1379509 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B2071415 : Blo 1379509 2071415 := bstep (se 1 (by rfl) ⟨1553561, by rfl⟩ : syracuseStep 2071415 = 3107123) B3107123
theorem B2071439 : Blo 1379509 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B221076373 : Blo 1379509 221076373 := bstep (se 6 (by rfl) ⟨5181477, by rfl⟩ : syracuseStep 221076373 = 10362955) B10362955
theorem B2620345 : Blo 1379509 2620345 := bstep (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) B1965259
theorem B2071481 : Blo 1379509 2071481 := bstep (se 2 (by rfl) ⟨776805, by rfl⟩ : syracuseStep 2071481 = 1553611) B1553611
theorem B14932939 : Blo 1379509 14932939 := bstep (se 1 (by rfl) ⟨11199704, by rfl⟩ : syracuseStep 14932939 = 22399409) B22399409
theorem B2071559 : Blo 1379509 2071559 := bstep (se 1 (by rfl) ⟨1553669, by rfl⟩ : syracuseStep 2071559 = 3107339) B3107339
theorem B4660253 : Blo 1379509 4660253 := bstep (se 3 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 4660253 = 1747595) B1747595
theorem B2071595 : Blo 1379509 2071595 := bstep (se 1 (by rfl) ⟨1553696, by rfl⟩ : syracuseStep 2071595 = 3107393) B3107393
theorem B2071625 : Blo 1379509 2071625 := bstep (se 2 (by rfl) ⟨776859, by rfl⟩ : syracuseStep 2071625 = 1553719) B1553719
theorem B1473671 : Blo 1379509 1473671 := bstep (se 1 (by rfl) ⟨1105253, by rfl⟩ : syracuseStep 1473671 = 2210507) B2210507
theorem B2948231 : Blo 1379509 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B2071739 : Blo 1379509 2071739 := bstep (se 1 (by rfl) ⟨1553804, by rfl⟩ : syracuseStep 2071739 = 3107609) B3107609
theorem B2071799 : Blo 1379509 2071799 := bstep (se 1 (by rfl) ⟨1553849, by rfl⟩ : syracuseStep 2071799 = 3107699) B3107699
theorem B1473799 : Blo 1379509 1473799 := bstep (se 1 (by rfl) ⟨1105349, by rfl⟩ : syracuseStep 1473799 = 2210699) B2210699
theorem B2620687 : Blo 1379509 2620687 := bstep (se 1 (by rfl) ⟨1965515, by rfl⟩ : syracuseStep 2620687 = 3931031) B3931031
theorem B2071823 : Blo 1379509 2071823 := bstep (se 1 (by rfl) ⟨1553867, by rfl⟩ : syracuseStep 2071823 = 3107735) B3107735
theorem B6987059 : Blo 1379509 6987059 := bstep (se 1 (by rfl) ⟨5240294, by rfl⟩ : syracuseStep 6987059 = 10480589) B10480589
theorem B2071865 : Blo 1379509 2071865 := bstep (se 2 (by rfl) ⟨776949, by rfl⟩ : syracuseStep 2071865 = 1553899) B1553899
theorem B3104135 : Blo 1379509 3104135 := bstep (se 1 (by rfl) ⟨2328101, by rfl⟩ : syracuseStep 3104135 = 4656203) B4656203
theorem B2071943 : Blo 1379509 2071943 := bstep (se 1 (by rfl) ⟨1553957, by rfl⟩ : syracuseStep 2071943 = 3107915) B3107915
theorem B2071979 : Blo 1379509 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B2072009 : Blo 1379509 2072009 := bstep (se 2 (by rfl) ⟨777003, by rfl⟩ : syracuseStep 2072009 = 1554007) B1554007
theorem B3104315 : Blo 1379509 3104315 := bstep (se 1 (by rfl) ⟨2328236, by rfl⟩ : syracuseStep 3104315 = 4656473) B4656473
theorem B2072123 : Blo 1379509 2072123 := bstep (se 1 (by rfl) ⟨1554092, by rfl⟩ : syracuseStep 2072123 = 3108185) B3108185
theorem B4972099 : Blo 1379509 4972099 := bstep (se 1 (by rfl) ⟨3729074, by rfl⟩ : syracuseStep 4972099 = 7458149) B7458149
theorem B6987383 : Blo 1379509 6987383 := bstep (se 1 (by rfl) ⟨5240537, by rfl⟩ : syracuseStep 6987383 = 10481075) B10481075
theorem B2072183 : Blo 1379509 2072183 := bstep (se 1 (by rfl) ⟨1554137, by rfl⟩ : syracuseStep 2072183 = 3108275) B3108275
theorem B1965703 : Blo 1379509 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B2072207 : Blo 1379509 2072207 := bstep (se 1 (by rfl) ⟨1554155, by rfl⟩ : syracuseStep 2072207 = 3108311) B3108311
theorem B3104441 : Blo 1379509 3104441 := bstep (se 2 (by rfl) ⟨1164165, by rfl⟩ : syracuseStep 3104441 = 2328331) B2328331
theorem B2072249 : Blo 1379509 2072249 := bstep (se 2 (by rfl) ⟨777093, by rfl⟩ : syracuseStep 2072249 = 1554187) B1554187
theorem B5897929 : Blo 1379509 5897929 := bstep (se 2 (by rfl) ⟨2211723, by rfl⟩ : syracuseStep 5897929 = 4423447) B4423447
theorem B7085839 : Blo 1379509 7085839 := bstep (se 1 (by rfl) ⟨5314379, by rfl⟩ : syracuseStep 7085839 = 10628759) B10628759
theorem B1474363 : Blo 1379509 1474363 := bstep (se 1 (by rfl) ⟨1105772, by rfl⟩ : syracuseStep 1474363 = 2211545) B2211545
theorem B8970355 : Blo 1379509 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B3932317 : Blo 1379509 3932317 := bstep (se 3 (by rfl) ⟨737309, by rfl⟩ : syracuseStep 3932317 = 1474619) B1474619
theorem B5243075 : Blo 1379509 5243075 := bstep (se 1 (by rfl) ⟨3932306, by rfl⟩ : syracuseStep 5243075 = 7864613) B7864613
theorem B4784375 : Blo 1379509 4784375 := bstep (se 1 (by rfl) ⟨3588281, by rfl⟩ : syracuseStep 4784375 = 7176563) B7176563
theorem B2949367 : Blo 1379509 2949367 := bstep (se 1 (by rfl) ⟨2212025, by rfl⟩ : syracuseStep 2949367 = 4424051) B4424051
theorem B4661495 : Blo 1379509 4661495 := bstep (se 1 (by rfl) ⟨3496121, by rfl⟩ : syracuseStep 4661495 = 6992243) B6992243
theorem B2621803 : Blo 1379509 2621803 := bstep (se 1 (by rfl) ⟨1966352, by rfl⟩ : syracuseStep 2621803 = 3932705) B3932705
theorem B3932545 : Blo 1379509 3932545 := bstep (se 2 (by rfl) ⟨1474704, by rfl⟩ : syracuseStep 3932545 = 2949409) B2949409
theorem B2621879 : Blo 1379509 2621879 := bstep (se 1 (by rfl) ⟨1966409, by rfl⟩ : syracuseStep 2621879 = 3932819) B3932819
theorem B4661819 : Blo 1379509 4661819 := bstep (se 1 (by rfl) ⟨3496364, by rfl⟩ : syracuseStep 4661819 = 6992729) B6992729
theorem B3105377 : Blo 1379509 3105377 := bstep (se 2 (by rfl) ⟨1164516, by rfl⟩ : syracuseStep 3105377 = 2329033) B2329033
theorem B3932887 : Blo 1379509 3932887 := bstep (se 1 (by rfl) ⟨2949665, by rfl⟩ : syracuseStep 3932887 = 5899331) B5899331
theorem B4662089 : Blo 1379509 4662089 := bstep (se 2 (by rfl) ⟨1748283, by rfl⟩ : syracuseStep 4662089 = 3496567) B3496567
theorem B7857071 : Blo 1379509 7857071 := bstep (se 1 (by rfl) ⟨5892803, by rfl⟩ : syracuseStep 7857071 = 11785607) B11785607
theorem B3105719 : Blo 1379509 3105719 := bstep (se 1 (by rfl) ⟨2329289, by rfl⟩ : syracuseStep 3105719 = 4658579) B4658579
theorem B2622395 : Blo 1379509 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B7865363 : Blo 1379509 7865363 := bstep (se 1 (by rfl) ⟨5899022, by rfl⟩ : syracuseStep 7865363 = 11798045) B11798045
theorem B5244061 : Blo 1379509 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B7857323 : Blo 1379509 7857323 := bstep (se 1 (by rfl) ⟨5892992, by rfl⟩ : syracuseStep 7857323 = 11785985) B11785985
theorem B6989003 : Blo 1379509 6989003 := bstep (se 1 (by rfl) ⟨5241752, by rfl⟩ : syracuseStep 6989003 = 10483505) B10483505
theorem B11355383 : Blo 1379509 11355383 := bstep (se 1 (by rfl) ⟨8516537, by rfl⟩ : syracuseStep 11355383 = 17033075) B17033075
theorem B7865819 : Blo 1379509 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B3106313 : Blo 1379509 3106313 := bstep (se 2 (by rfl) ⟨1164867, by rfl⟩ : syracuseStep 3106313 = 2329735) B2329735
theorem B10487393 : Blo 1379509 10487393 := bstep (se 2 (by rfl) ⟨3932772, by rfl⟩ : syracuseStep 10487393 = 7865545) B7865545
theorem B3983059 : Blo 1379509 3983059 := bstep (se 1 (by rfl) ⟨2987294, by rfl⟩ : syracuseStep 3983059 = 5974589) B5974589
theorem B7866071 : Blo 1379509 7866071 := bstep (se 1 (by rfl) ⟨5899553, by rfl⟩ : syracuseStep 7866071 = 11799107) B11799107
theorem B2328311 : Blo 1379509 2328311 := bstep (se 1 (by rfl) ⟨1746233, by rfl⟩ : syracuseStep 2328311 = 3492467) B3492467
theorem B3106655 : Blo 1379509 3106655 := bstep (se 1 (by rfl) ⟨2329991, by rfl⟩ : syracuseStep 3106655 = 4659983) B4659983
theorem B30279683 : Blo 1379509 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B3106835 : Blo 1379509 3106835 := bstep (se 1 (by rfl) ⟨2330126, by rfl⟩ : syracuseStep 3106835 = 4660253) B4660253
theorem B2328655 : Blo 1379509 2328655 := bstep (se 1 (by rfl) ⟨1746491, by rfl⟩ : syracuseStep 2328655 = 3492983) B3492983
theorem B6629465 : Blo 1379509 6629465 := bstep (se 2 (by rfl) ⟨2486049, by rfl⟩ : syracuseStep 6629465 = 4972099) B4972099
theorem B3492011 : Blo 1379509 3492011 := bstep (se 1 (by rfl) ⟨2619008, by rfl⟩ : syracuseStep 3492011 = 5238017) B5238017
theorem B2328905 : Blo 1379509 2328905 := bstep (se 2 (by rfl) ⟨873339, by rfl⟩ : syracuseStep 2328905 = 1746679) B1746679
theorem B9447785 : Blo 1379509 9447785 := bstep (se 2 (by rfl) ⟨3542919, by rfl⟩ : syracuseStep 9447785 = 7085839) B7085839
theorem B3107177 : Blo 1379509 3107177 := bstep (se 2 (by rfl) ⟨1165191, by rfl⟩ : syracuseStep 3107177 = 2330383) B2330383
theorem B17681075 : Blo 1379509 17681075 := bstep (se 1 (by rfl) ⟨13260806, by rfl⟩ : syracuseStep 17681075 = 26521613) B26521613
theorem B2329337 : Blo 1379509 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B2329519 : Blo 1379509 2329519 := bstep (se 1 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 2329519 = 3494279) B3494279
theorem B3492791 : Blo 1379509 3492791 := bstep (se 1 (by rfl) ⟨2619593, by rfl⟩ : syracuseStep 3492791 = 5239187) B5239187
theorem B3107771 : Blo 1379509 3107771 := bstep (se 1 (by rfl) ⟨2330828, by rfl⟩ : syracuseStep 3107771 = 4661657) B4661657
theorem B6638593 : Blo 1379509 6638593 := bstep (se 2 (by rfl) ⟨2489472, by rfl⟩ : syracuseStep 6638593 = 4978945) B4978945
theorem B2329607 : Blo 1379509 2329607 := bstep (se 1 (by rfl) ⟨1747205, by rfl⟩ : syracuseStep 2329607 = 3494411) B3494411
theorem B4975631 : Blo 1379509 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B5975059 : Blo 1379509 5975059 := bstep (se 1 (by rfl) ⟨4481294, by rfl⟩ : syracuseStep 5975059 = 8962589) B8962589
theorem B10488851 : Blo 1379509 10488851 := bstep (se 1 (by rfl) ⟨7866638, by rfl⟩ : syracuseStep 10488851 = 15733277) B15733277
theorem B8842283 : Blo 1379509 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B3107897 : Blo 1379509 3107897 := bstep (se 2 (by rfl) ⟨1165461, by rfl⟩ : syracuseStep 3107897 = 2330923) B2330923
theorem B1379527 : Blo 1379509 1379527 := bstep (se 1 (by rfl) ⟨1034645, by rfl⟩ : syracuseStep 1379527 = 2069291) B2069291
theorem B1379547 : Blo 1379509 1379547 := bstep (se 1 (by rfl) ⟨1034660, by rfl⟩ : syracuseStep 1379547 = 2069321) B2069321
theorem B1379623 : Blo 1379509 1379623 := bstep (se 1 (by rfl) ⟨1034717, by rfl⟩ : syracuseStep 1379623 = 2069435) B2069435
theorem B1379663 : Blo 1379509 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B1379679 : Blo 1379509 1379679 := bstep (se 1 (by rfl) ⟨1034759, by rfl⟩ : syracuseStep 1379679 = 2069519) B2069519
theorem B2329951 : Blo 1379509 2329951 := bstep (se 1 (by rfl) ⟨1747463, by rfl⟩ : syracuseStep 2329951 = 3494927) B3494927
theorem B1379707 : Blo 1379509 1379707 := bstep (se 1 (by rfl) ⟨1034780, by rfl⟩ : syracuseStep 1379707 = 2069561) B2069561
theorem B19901821 : Blo 1379509 19901821 := bstep (se 3 (by rfl) ⟨3731591, by rfl⟩ : syracuseStep 19901821 = 7463183) B7463183
theorem B2796943 : Blo 1379509 2796943 := bstep (se 1 (by rfl) ⟨2097707, by rfl⟩ : syracuseStep 2796943 = 4195415) B4195415
theorem B4656527 : Blo 1379509 4656527 := bstep (se 1 (by rfl) ⟨3492395, by rfl⟩ : syracuseStep 4656527 = 6984791) B6984791
theorem B3108239 : Blo 1379509 3108239 := bstep (se 1 (by rfl) ⟨2331179, by rfl⟩ : syracuseStep 3108239 = 4662359) B4662359
theorem B9948581 : Blo 1379509 9948581 := bstep (se 4 (by rfl) ⟨932679, by rfl⟩ : syracuseStep 9948581 = 1865359) B1865359
theorem B1379759 : Blo 1379509 1379759 := bstep (se 1 (by rfl) ⟨1034819, by rfl⟩ : syracuseStep 1379759 = 2069639) B2069639
theorem B2330039 : Blo 1379509 2330039 := bstep (se 1 (by rfl) ⟨1747529, by rfl⟩ : syracuseStep 2330039 = 3495059) B3495059
theorem B1379783 : Blo 1379509 1379783 := bstep (se 1 (by rfl) ⟨1034837, by rfl⟩ : syracuseStep 1379783 = 2069675) B2069675
theorem B5311945 : Blo 1379509 5311945 := bstep (se 2 (by rfl) ⟨1991979, by rfl⟩ : syracuseStep 5311945 = 3983959) B3983959
theorem B1379803 : Blo 1379509 1379803 := bstep (se 1 (by rfl) ⟨1034852, by rfl⟩ : syracuseStep 1379803 = 2069705) B2069705
theorem B10366427 : Blo 1379509 10366427 := bstep (se 1 (by rfl) ⟨7774820, by rfl⟩ : syracuseStep 10366427 = 15549641) B15549641
theorem B1379879 : Blo 1379509 1379879 := bstep (se 1 (by rfl) ⟨1034909, by rfl⟩ : syracuseStep 1379879 = 2069819) B2069819
theorem B2240057 : Blo 1379509 2240057 := bstep (se 2 (by rfl) ⟨840021, by rfl⟩ : syracuseStep 2240057 = 1680043) B1680043
theorem B1379919 : Blo 1379509 1379919 := bstep (se 1 (by rfl) ⟨1034939, by rfl⟩ : syracuseStep 1379919 = 2069879) B2069879
theorem B1379935 : Blo 1379509 1379935 := bstep (se 1 (by rfl) ⟨1034951, by rfl⟩ : syracuseStep 1379935 = 2069903) B2069903
theorem B1379963 : Blo 1379509 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B6295163 : Blo 1379509 6295163 := bstep (se 1 (by rfl) ⟨4721372, by rfl⟩ : syracuseStep 6295163 = 9442745) B9442745
theorem B1380015 : Blo 1379509 1380015 := bstep (se 1 (by rfl) ⟨1035011, by rfl⟩ : syracuseStep 1380015 = 2070023) B2070023
theorem B1380039 : Blo 1379509 1380039 := bstep (se 1 (by rfl) ⟨1035029, by rfl⟩ : syracuseStep 1380039 = 2070059) B2070059
theorem B4656851 : Blo 1379509 4656851 := bstep (se 1 (by rfl) ⟨3492638, by rfl⟩ : syracuseStep 4656851 = 6985277) B6985277
theorem B1380059 : Blo 1379509 1380059 := bstep (se 1 (by rfl) ⟨1035044, by rfl⟩ : syracuseStep 1380059 = 2070089) B2070089
theorem B1380135 : Blo 1379509 1380135 := bstep (se 1 (by rfl) ⟨1035101, by rfl⟩ : syracuseStep 1380135 = 2070203) B2070203
theorem B1380175 : Blo 1379509 1380175 := bstep (se 1 (by rfl) ⟨1035131, by rfl⟩ : syracuseStep 1380175 = 2070263) B2070263
theorem B1380191 : Blo 1379509 1380191 := bstep (se 1 (by rfl) ⟨1035143, by rfl⟩ : syracuseStep 1380191 = 2070287) B2070287
theorem B294768497 : Blo 1379509 294768497 := bstep (se 2 (by rfl) ⟨110538186, by rfl⟩ : syracuseStep 294768497 = 221076373) B221076373
theorem B1380219 : Blo 1379509 1380219 := bstep (se 1 (by rfl) ⟨1035164, by rfl⟩ : syracuseStep 1380219 = 2070329) B2070329
theorem B3493793 : Blo 1379509 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B1380271 : Blo 1379509 1380271 := bstep (se 1 (by rfl) ⟨1035203, by rfl⟩ : syracuseStep 1380271 = 2070407) B2070407
theorem B19910585 : Blo 1379509 19910585 := bstep (se 2 (by rfl) ⟨7466469, by rfl⟩ : syracuseStep 19910585 = 14932939) B14932939
theorem B11800505 : Blo 1379509 11800505 := bstep (se 2 (by rfl) ⟨4425189, by rfl⟩ : syracuseStep 11800505 = 8850379) B8850379
theorem B5238715 : Blo 1379509 5238715 := bstep (se 1 (by rfl) ⟨3929036, by rfl⟩ : syracuseStep 5238715 = 7858073) B7858073
theorem B1380295 : Blo 1379509 1380295 := bstep (se 1 (by rfl) ⟨1035221, by rfl⟩ : syracuseStep 1380295 = 2070443) B2070443
theorem B1380315 : Blo 1379509 1380315 := bstep (se 1 (by rfl) ⟨1035236, by rfl⟩ : syracuseStep 1380315 = 2070473) B2070473
theorem B2330633 : Blo 1379509 2330633 := bstep (se 2 (by rfl) ⟨873987, by rfl⟩ : syracuseStep 2330633 = 1747975) B1747975
theorem B7860239 : Blo 1379509 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B28340239 : Blo 1379509 28340239 := bstep (se 1 (by rfl) ⟨21255179, by rfl⟩ : syracuseStep 28340239 = 42510359) B42510359
theorem B1552423 : Blo 1379509 1552423 := bstep (se 1 (by rfl) ⟨1164317, by rfl⟩ : syracuseStep 1552423 = 2328635) B2328635
theorem B1380391 : Blo 1379509 1380391 := bstep (se 1 (by rfl) ⟨1035293, by rfl⟩ : syracuseStep 1380391 = 2070587) B2070587
theorem B1380431 : Blo 1379509 1380431 := bstep (se 1 (by rfl) ⟨1035323, by rfl⟩ : syracuseStep 1380431 = 2070647) B2070647
theorem B1380447 : Blo 1379509 1380447 := bstep (se 1 (by rfl) ⟨1035335, by rfl⟩ : syracuseStep 1380447 = 2070671) B2070671
theorem B1380475 : Blo 1379509 1380475 := bstep (se 1 (by rfl) ⟨1035356, by rfl⟩ : syracuseStep 1380475 = 2070713) B2070713
theorem B2330795 : Blo 1379509 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B1380527 : Blo 1379509 1380527 := bstep (se 1 (by rfl) ⟨1035395, by rfl⟩ : syracuseStep 1380527 = 2070791) B2070791
theorem B1380551 : Blo 1379509 1380551 := bstep (se 1 (by rfl) ⟨1035413, by rfl⟩ : syracuseStep 1380551 = 2070827) B2070827
theorem B1380571 : Blo 1379509 1380571 := bstep (se 1 (by rfl) ⟨1035428, by rfl⟩ : syracuseStep 1380571 = 2070857) B2070857
theorem B11350273 : Blo 1379509 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B1380647 : Blo 1379509 1380647 := bstep (se 1 (by rfl) ⟨1035485, by rfl⟩ : syracuseStep 1380647 = 2070971) B2070971
theorem B1380687 : Blo 1379509 1380687 := bstep (se 1 (by rfl) ⟨1035515, by rfl⟩ : syracuseStep 1380687 = 2071031) B2071031
theorem B6295895 : Blo 1379509 6295895 := bstep (se 1 (by rfl) ⟨4721921, by rfl⟩ : syracuseStep 6295895 = 9443843) B9443843
theorem B1380703 : Blo 1379509 1380703 := bstep (se 1 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 1380703 = 2071055) B2071055
theorem B3494249 : Blo 1379509 3494249 := bstep (se 2 (by rfl) ⟨1310343, by rfl⟩ : syracuseStep 3494249 = 2620687) B2620687
theorem B1380731 : Blo 1379509 1380731 := bstep (se 1 (by rfl) ⟨1035548, by rfl⟩ : syracuseStep 1380731 = 2071097) B2071097
theorem B3928445 : Blo 1379509 3928445 := bstep (se 3 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 3928445 = 1473167) B1473167
theorem B1380783 : Blo 1379509 1380783 := bstep (se 1 (by rfl) ⟨1035587, by rfl⟩ : syracuseStep 1380783 = 2071175) B2071175
theorem B1380807 : Blo 1379509 1380807 := bstep (se 1 (by rfl) ⟨1035605, by rfl⟩ : syracuseStep 1380807 = 2071211) B2071211
theorem B1380827 : Blo 1379509 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B4977185 : Blo 1379509 4977185 := bstep (se 2 (by rfl) ⟨1866444, by rfl⟩ : syracuseStep 4977185 = 3732889) B3732889
theorem B1380903 : Blo 1379509 1380903 := bstep (se 1 (by rfl) ⟨1035677, by rfl⟩ : syracuseStep 1380903 = 2071355) B2071355
theorem B2331193 : Blo 1379509 2331193 := bstep (se 2 (by rfl) ⟨874197, by rfl⟩ : syracuseStep 2331193 = 1748395) B1748395
theorem B2486863 : Blo 1379509 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B1380943 : Blo 1379509 1380943 := bstep (se 1 (by rfl) ⟨1035707, by rfl⟩ : syracuseStep 1380943 = 2071415) B2071415
theorem B1380959 : Blo 1379509 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B1380987 : Blo 1379509 1380987 := bstep (se 1 (by rfl) ⟨1035740, by rfl⟩ : syracuseStep 1380987 = 2071481) B2071481
theorem B9958061 : Blo 1379509 9958061 := bstep (se 3 (by rfl) ⟨1867136, by rfl⟩ : syracuseStep 9958061 = 3734273) B3734273
theorem B1381039 : Blo 1379509 1381039 := bstep (se 1 (by rfl) ⟨1035779, by rfl⟩ : syracuseStep 1381039 = 2071559) B2071559
theorem B1381063 : Blo 1379509 1381063 := bstep (se 1 (by rfl) ⟨1035797, by rfl⟩ : syracuseStep 1381063 = 2071595) B2071595
theorem B5239505 : Blo 1379509 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B3928787 : Blo 1379509 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B1381083 : Blo 1379509 1381083 := bstep (se 1 (by rfl) ⟨1035812, by rfl⟩ : syracuseStep 1381083 = 2071625) B2071625
theorem B1381159 : Blo 1379509 1381159 := bstep (se 1 (by rfl) ⟨1035869, by rfl⟩ : syracuseStep 1381159 = 2071739) B2071739
theorem B17699633 : Blo 1379509 17699633 := bstep (se 2 (by rfl) ⟨6637362, by rfl⟩ : syracuseStep 17699633 = 13274725) B13274725
theorem B12587849 : Blo 1379509 12587849 := bstep (se 2 (by rfl) ⟨4720443, by rfl⟩ : syracuseStep 12587849 = 9440887) B9440887
theorem B1381199 : Blo 1379509 1381199 := bstep (se 1 (by rfl) ⟨1035899, by rfl⟩ : syracuseStep 1381199 = 2071799) B2071799
theorem B1381215 : Blo 1379509 1381215 := bstep (se 1 (by rfl) ⟨1035911, by rfl⟩ : syracuseStep 1381215 = 2071823) B2071823
theorem B4658039 : Blo 1379509 4658039 := bstep (se 1 (by rfl) ⟨3493529, by rfl⟩ : syracuseStep 4658039 = 6987059) B6987059
theorem B1381243 : Blo 1379509 1381243 := bstep (se 1 (by rfl) ⟨1035932, by rfl⟩ : syracuseStep 1381243 = 2071865) B2071865
theorem B2069423 : Blo 1379509 2069423 := bstep (se 1 (by rfl) ⟨1552067, by rfl⟩ : syracuseStep 2069423 = 3104135) B3104135
theorem B1381295 : Blo 1379509 1381295 := bstep (se 1 (by rfl) ⟨1035971, by rfl⟩ : syracuseStep 1381295 = 2071943) B2071943
theorem B1381319 : Blo 1379509 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B1381339 : Blo 1379509 1381339 := bstep (se 1 (by rfl) ⟨1036004, by rfl⟩ : syracuseStep 1381339 = 2072009) B2072009
theorem B2069513 : Blo 1379509 2069513 := bstep (se 2 (by rfl) ⟨776067, by rfl⟩ : syracuseStep 2069513 = 1552135) B1552135
theorem B2069543 : Blo 1379509 2069543 := bstep (se 1 (by rfl) ⟨1552157, by rfl⟩ : syracuseStep 2069543 = 3104315) B3104315
theorem B1381415 : Blo 1379509 1381415 := bstep (se 1 (by rfl) ⟨1036061, by rfl⟩ : syracuseStep 1381415 = 2072123) B2072123
theorem B4658255 : Blo 1379509 4658255 := bstep (se 1 (by rfl) ⟨3493691, by rfl⟩ : syracuseStep 4658255 = 6987383) B6987383
theorem B1381455 : Blo 1379509 1381455 := bstep (se 1 (by rfl) ⟨1036091, by rfl⟩ : syracuseStep 1381455 = 2072183) B2072183
theorem B1381471 : Blo 1379509 1381471 := bstep (se 1 (by rfl) ⟨1036103, by rfl⟩ : syracuseStep 1381471 = 2072207) B2072207
theorem B2069627 : Blo 1379509 2069627 := bstep (se 1 (by rfl) ⟨1552220, by rfl⟩ : syracuseStep 2069627 = 3104441) B3104441
theorem B1381499 : Blo 1379509 1381499 := bstep (se 1 (by rfl) ⟨1036124, by rfl⟩ : syracuseStep 1381499 = 2072249) B2072249
theorem B5239961 : Blo 1379509 5239961 := bstep (se 2 (by rfl) ⟨1964985, by rfl⟩ : syracuseStep 5239961 = 3929971) B3929971
theorem B2069753 : Blo 1379509 2069753 := bstep (se 2 (by rfl) ⟨776157, by rfl⟩ : syracuseStep 2069753 = 1552315) B1552315
theorem B2069855 : Blo 1379509 2069855 := bstep (se 1 (by rfl) ⟨1552391, by rfl⟩ : syracuseStep 2069855 = 3104783) B3104783
theorem B2069867 : Blo 1379509 2069867 := bstep (se 1 (by rfl) ⟨1552400, by rfl⟩ : syracuseStep 2069867 = 3104801) B3104801
theorem B35403155 : Blo 1379509 35403155 := bstep (se 1 (by rfl) ⟨26552366, by rfl⟩ : syracuseStep 35403155 = 53104733) B53104733
theorem B15725987 : Blo 1379509 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B4658633 : Blo 1379509 4658633 := bstep (se 2 (by rfl) ⟨1746987, by rfl⟩ : syracuseStep 4658633 = 3493975) B3493975
theorem B3495433 : Blo 1379509 3495433 := bstep (se 2 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 3495433 = 2621575) B2621575
theorem B2070095 : Blo 1379509 2070095 := bstep (se 1 (by rfl) ⟨1552571, by rfl⟩ : syracuseStep 2070095 = 3105143) B3105143
theorem B4421243 : Blo 1379509 4421243 := bstep (se 1 (by rfl) ⟨3315932, by rfl⟩ : syracuseStep 4421243 = 6631865) B6631865
theorem B1554043 : Blo 1379509 1554043 := bstep (se 1 (by rfl) ⟨1165532, by rfl⟩ : syracuseStep 1554043 = 2331065) B2331065
theorem B8844947 : Blo 1379509 8844947 := bstep (se 1 (by rfl) ⟨6633710, by rfl⟩ : syracuseStep 8844947 = 13267421) B13267421
theorem B56694421 : Blo 1379509 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B3929789 : Blo 1379509 3929789 := bstep (se 3 (by rfl) ⟨736835, by rfl⟩ : syracuseStep 3929789 = 1473671) B1473671
theorem B2070215 : Blo 1379509 2070215 := bstep (se 1 (by rfl) ⟨1552661, by rfl⟩ : syracuseStep 2070215 = 3105323) B3105323
theorem B5043923 : Blo 1379509 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B4658903 : Blo 1379509 4658903 := bstep (se 1 (by rfl) ⟨3494177, by rfl⟩ : syracuseStep 4658903 = 6988355) B6988355
theorem B145446731 : Blo 1379509 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B2070377 : Blo 1379509 2070377 := bstep (se 2 (by rfl) ⟨776391, by rfl⟩ : syracuseStep 2070377 = 1552783) B1552783
theorem B4659119 : Blo 1379509 4659119 := bstep (se 1 (by rfl) ⟨3494339, by rfl⟩ : syracuseStep 4659119 = 6988679) B6988679
theorem B2070455 : Blo 1379509 2070455 := bstep (se 1 (by rfl) ⟨1552841, by rfl⟩ : syracuseStep 2070455 = 3105683) B3105683
theorem B2488247 : Blo 1379509 2488247 := bstep (se 1 (by rfl) ⟨1866185, by rfl⟩ : syracuseStep 2488247 = 3732371) B3732371
theorem B2070491 : Blo 1379509 2070491 := bstep (se 1 (by rfl) ⟨1552868, by rfl⟩ : syracuseStep 2070491 = 3105737) B3105737
theorem B2619449 : Blo 1379509 2619449 := bstep (se 2 (by rfl) ⟨982293, by rfl⟩ : syracuseStep 2619449 = 1964587) B1964587
theorem B4978745 : Blo 1379509 4978745 := bstep (se 2 (by rfl) ⟨1867029, by rfl⟩ : syracuseStep 4978745 = 3734059) B3734059
theorem B5896273 : Blo 1379509 5896273 := bstep (se 2 (by rfl) ⟨2211102, by rfl⟩ : syracuseStep 5896273 = 4422205) B4422205
theorem B2070959 : Blo 1379509 2070959 := bstep (se 1 (by rfl) ⟨1553219, by rfl⟩ : syracuseStep 2070959 = 3106439) B3106439
theorem B6986249 : Blo 1379509 6986249 := bstep (se 2 (by rfl) ⟨2619843, by rfl⟩ : syracuseStep 6986249 = 5239687) B5239687
theorem B2071049 : Blo 1379509 2071049 := bstep (se 2 (by rfl) ⟨776643, by rfl⟩ : syracuseStep 2071049 = 1553287) B1553287
theorem B8845847 : Blo 1379509 8845847 := bstep (se 1 (by rfl) ⟨6634385, by rfl⟩ : syracuseStep 8845847 = 13268771) B13268771
theorem B5593625 : Blo 1379509 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B2071079 : Blo 1379509 2071079 := bstep (se 1 (by rfl) ⟨1553309, by rfl⟩ : syracuseStep 2071079 = 3106619) B3106619
theorem B2071163 : Blo 1379509 2071163 := bstep (se 1 (by rfl) ⟨1553372, by rfl⟩ : syracuseStep 2071163 = 3106745) B3106745
theorem B16792265 : Blo 1379509 16792265 := bstep (se 2 (by rfl) ⟨6297099, by rfl⟩ : syracuseStep 16792265 = 12594199) B12594199
theorem B119397077 : Blo 1379509 119397077 := bstep (se 7 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 119397077 = 2798369) B2798369
theorem B2071289 : Blo 1379509 2071289 := bstep (se 2 (by rfl) ⟨776733, by rfl⟩ : syracuseStep 2071289 = 1553467) B1553467
theorem B2071391 : Blo 1379509 2071391 := bstep (se 1 (by rfl) ⟨1553543, by rfl⟩ : syracuseStep 2071391 = 3107087) B3107087
theorem B2071403 : Blo 1379509 2071403 := bstep (se 1 (by rfl) ⟨1553552, by rfl⟩ : syracuseStep 2071403 = 3107105) B3107105
theorem B3316663 : Blo 1379509 3316663 := bstep (se 1 (by rfl) ⟨2487497, by rfl⟩ : syracuseStep 3316663 = 4974995) B4974995
theorem B22404023 : Blo 1379509 22404023 := bstep (se 1 (by rfl) ⟨16803017, by rfl⟩ : syracuseStep 22404023 = 33606035) B33606035
theorem B3496891 : Blo 1379509 3496891 := bstep (se 1 (by rfl) ⟨2622668, by rfl⟩ : syracuseStep 3496891 = 5245337) B5245337
theorem B1965065 : Blo 1379509 1965065 := bstep (se 2 (by rfl) ⟨736899, by rfl⟩ : syracuseStep 1965065 = 1473799) B1473799
theorem B5241935 : Blo 1379509 5241935 := bstep (se 1 (by rfl) ⟨3931451, by rfl⟩ : syracuseStep 5241935 = 7862903) B7862903
theorem B2071631 : Blo 1379509 2071631 := bstep (se 1 (by rfl) ⟨1553723, by rfl⟩ : syracuseStep 2071631 = 3107447) B3107447
theorem B1965179 : Blo 1379509 1965179 := bstep (se 1 (by rfl) ⟨1473884, by rfl⟩ : syracuseStep 1965179 = 2947769) B2947769
theorem B2071751 : Blo 1379509 2071751 := bstep (se 1 (by rfl) ⟨1553813, by rfl⟩ : syracuseStep 2071751 = 3107627) B3107627
theorem B3103991 : Blo 1379509 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B5242103 : Blo 1379509 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B4971881 : Blo 1379509 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B2071913 : Blo 1379509 2071913 := bstep (se 2 (by rfl) ⟨776967, by rfl⟩ : syracuseStep 2071913 = 1553935) B1553935
theorem B1965487 : Blo 1379509 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B39787955 : Blo 1379509 39787955 := bstep (se 1 (by rfl) ⟨29840966, by rfl⟩ : syracuseStep 39787955 = 59681933) B59681933
theorem B2071991 : Blo 1379509 2071991 := bstep (se 1 (by rfl) ⟨1553993, by rfl⟩ : syracuseStep 2071991 = 3107987) B3107987
theorem B2072027 : Blo 1379509 2072027 := bstep (se 1 (by rfl) ⟨1554020, by rfl⟩ : syracuseStep 2072027 = 3108041) B3108041
theorem B2620937 : Blo 1379509 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B5594663 : Blo 1379509 5594663 := bstep (se 1 (by rfl) ⟨4195997, by rfl⟩ : syracuseStep 5594663 = 8391995) B8391995
theorem B7863905 : Blo 1379509 7863905 := bstep (se 2 (by rfl) ⟨2948964, by rfl⟩ : syracuseStep 7863905 = 5897929) B5897929
theorem B8961785 : Blo 1379509 8961785 := bstep (se 2 (by rfl) ⟨3360669, by rfl⟩ : syracuseStep 8961785 = 6721339) B6721339
theorem B1965817 : Blo 1379509 1965817 := bstep (se 2 (by rfl) ⟨737181, by rfl⟩ : syracuseStep 1965817 = 1474363) B1474363
theorem B3104585 : Blo 1379509 3104585 := bstep (se 2 (by rfl) ⟨1164219, by rfl⟩ : syracuseStep 3104585 = 2328439) B2328439
theorem B6987707 : Blo 1379509 6987707 := bstep (se 1 (by rfl) ⟨5240780, by rfl⟩ : syracuseStep 6987707 = 10481561) B10481561
theorem B3104873 : Blo 1379509 3104873 := bstep (se 2 (by rfl) ⟨1164327, by rfl⟩ : syracuseStep 3104873 = 2328655) B2328655
theorem B11960473 : Blo 1379509 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B5243089 : Blo 1379509 5243089 := bstep (se 2 (by rfl) ⟨1966158, by rfl⟩ : syracuseStep 5243089 = 3932317) B3932317
theorem B3932489 : Blo 1379509 3932489 := bstep (se 2 (by rfl) ⟨1474683, by rfl⟩ : syracuseStep 3932489 = 2949367) B2949367
theorem B5243393 : Blo 1379509 5243393 := bstep (se 2 (by rfl) ⟨1966272, by rfl⟩ : syracuseStep 5243393 = 3932545) B3932545
theorem B3105359 : Blo 1379509 3105359 := bstep (se 1 (by rfl) ⟨2329019, by rfl⟩ : syracuseStep 3105359 = 4658039) B4658039
theorem B5243575 : Blo 1379509 5243575 := bstep (se 1 (by rfl) ⟨3932681, by rfl⟩ : syracuseStep 5243575 = 7865363) B7865363
theorem B3105503 : Blo 1379509 3105503 := bstep (se 1 (by rfl) ⟨2329127, by rfl⟩ : syracuseStep 3105503 = 4658255) B4658255
theorem B7570255 : Blo 1379509 7570255 := bstep (se 1 (by rfl) ⟨5677691, by rfl⟩ : syracuseStep 7570255 = 11355383) B11355383
theorem B23602103 : Blo 1379509 23602103 := bstep (se 1 (by rfl) ⟨17701577, by rfl⟩ : syracuseStep 23602103 = 35403155) B35403155
theorem B5243849 : Blo 1379509 5243849 := bstep (se 2 (by rfl) ⟨1966443, by rfl⟩ : syracuseStep 5243849 = 3932887) B3932887
theorem B3105755 : Blo 1379509 3105755 := bstep (se 1 (by rfl) ⟨2329316, by rfl⟩ : syracuseStep 3105755 = 4658633) B4658633
theorem B5243879 : Blo 1379509 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B21242981 : Blo 1379509 21242981 := bstep (se 4 (by rfl) ⟨1991529, by rfl⟩ : syracuseStep 21242981 = 3983059) B3983059
theorem B3105935 : Blo 1379509 3105935 := bstep (se 1 (by rfl) ⟨2329451, by rfl⟩ : syracuseStep 3105935 = 4658903) B4658903
theorem B5244047 : Blo 1379509 5244047 := bstep (se 1 (by rfl) ⟨3933035, by rfl⟩ : syracuseStep 5244047 = 7866071) B7866071
theorem B3106025 : Blo 1379509 3106025 := bstep (se 2 (by rfl) ⟨1164759, by rfl⟩ : syracuseStep 3106025 = 2329519) B2329519
theorem B4662521 : Blo 1379509 4662521 := bstep (se 2 (by rfl) ⟨1748445, by rfl⟩ : syracuseStep 4662521 = 3496891) B3496891
theorem B3106079 : Blo 1379509 3106079 := bstep (se 1 (by rfl) ⟨2329559, by rfl⟩ : syracuseStep 3106079 = 4659119) B4659119
theorem B20186455 : Blo 1379509 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B6989165 : Blo 1379509 6989165 := bstep (se 3 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 6989165 = 2620937) B2620937
theorem B1746299 : Blo 1379509 1746299 := bstep (se 1 (by rfl) ⟨1309724, by rfl⟩ : syracuseStep 1746299 = 2619449) B2619449
theorem B3319163 : Blo 1379509 3319163 := bstep (se 1 (by rfl) ⟨2489372, by rfl⟩ : syracuseStep 3319163 = 4978745) B4978745
theorem B13272493 : Blo 1379509 13272493 := bstep (se 3 (by rfl) ⟨2488592, by rfl⟩ : syracuseStep 13272493 = 4977185) B4977185
theorem B2328007 : Blo 1379509 2328007 := bstep (se 1 (by rfl) ⟨1746005, by rfl⟩ : syracuseStep 2328007 = 3492011) B3492011
theorem B11789981 : Blo 1379509 11789981 := bstep (se 3 (by rfl) ⟨2210621, by rfl⟩ : syracuseStep 11789981 = 4421243) B4421243
theorem B16787101 : Blo 1379509 16787101 := bstep (se 3 (by rfl) ⟨3147581, by rfl⟩ : syracuseStep 16787101 = 6295163) B6295163
theorem B3729083 : Blo 1379509 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B3106601 : Blo 1379509 3106601 := bstep (se 2 (by rfl) ⟨1164975, by rfl⟩ : syracuseStep 3106601 = 2329951) B2329951
theorem B26535761 : Blo 1379509 26535761 := bstep (se 2 (by rfl) ⟨9950910, by rfl⟩ : syracuseStep 26535761 = 19901821) B19901821
theorem B3729257 : Blo 1379509 3729257 := bstep (se 2 (by rfl) ⟨1398471, by rfl⟩ : syracuseStep 3729257 = 2796943) B2796943
theorem B2328527 : Blo 1379509 2328527 := bstep (se 1 (by rfl) ⟨1746395, by rfl⟩ : syracuseStep 2328527 = 3492791) B3492791
theorem B14936015 : Blo 1379509 14936015 := bstep (se 1 (by rfl) ⟨11202011, by rfl⟩ : syracuseStep 14936015 = 22404023) B22404023
theorem B3729775 : Blo 1379509 3729775 := bstep (se 1 (by rfl) ⟨2797331, by rfl⟩ : syracuseStep 3729775 = 5594663) B5594663
theorem B1493371 : Blo 1379509 1493371 := bstep (se 1 (by rfl) ⟨1120028, by rfl⟩ : syracuseStep 1493371 = 2240057) B2240057
theorem B28330373 : Blo 1379509 28330373 := bstep (se 4 (by rfl) ⟨2655972, by rfl⟩ : syracuseStep 28330373 = 5311945) B5311945
theorem B5974523 : Blo 1379509 5974523 := bstep (se 1 (by rfl) ⟨4480892, by rfl⟩ : syracuseStep 5974523 = 8961785) B8961785
theorem B196512331 : Blo 1379509 196512331 := bstep (se 1 (by rfl) ⟨147384248, by rfl⟩ : syracuseStep 196512331 = 294768497) B294768497
theorem B2329195 : Blo 1379509 2329195 := bstep (se 1 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 2329195 = 3493793) B3493793
theorem B13273723 : Blo 1379509 13273723 := bstep (se 1 (by rfl) ⟨9955292, by rfl⟩ : syracuseStep 13273723 = 19910585) B19910585
theorem B7867003 : Blo 1379509 7867003 := bstep (se 1 (by rfl) ⟨5900252, by rfl⟩ : syracuseStep 7867003 = 11800505) B11800505
theorem B3189583 : Blo 1379509 3189583 := bstep (se 1 (by rfl) ⟨2392187, by rfl⟩ : syracuseStep 3189583 = 4784375) B4784375
theorem B3107663 : Blo 1379509 3107663 := bstep (se 1 (by rfl) ⟨2330747, by rfl⟩ : syracuseStep 3107663 = 4661495) B4661495
theorem B4197263 : Blo 1379509 4197263 := bstep (se 1 (by rfl) ⟨3147947, by rfl⟩ : syracuseStep 4197263 = 6295895) B6295895
theorem B2329499 : Blo 1379509 2329499 := bstep (se 1 (by rfl) ⟨1747124, by rfl⟩ : syracuseStep 2329499 = 3494249) B3494249
theorem B1747919 : Blo 1379509 1747919 := bstep (se 1 (by rfl) ⟨1310939, by rfl⟩ : syracuseStep 1747919 = 2621879) B2621879
theorem B15133697 : Blo 1379509 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B3107879 : Blo 1379509 3107879 := bstep (se 1 (by rfl) ⟨2330909, by rfl⟩ : syracuseStep 3107879 = 4661819) B4661819
theorem B6638707 : Blo 1379509 6638707 := bstep (se 1 (by rfl) ⟨4979030, by rfl⟩ : syracuseStep 6638707 = 9958061) B9958061
theorem B3493003 : Blo 1379509 3493003 := bstep (se 1 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 3493003 = 5239505) B5239505
theorem B11799755 : Blo 1379509 11799755 := bstep (se 1 (by rfl) ⟨8849816, by rfl⟩ : syracuseStep 11799755 = 17699633) B17699633
theorem B8391899 : Blo 1379509 8391899 := bstep (se 1 (by rfl) ⟨6293924, by rfl⟩ : syracuseStep 8391899 = 12587849) B12587849
theorem B3108059 : Blo 1379509 3108059 := bstep (se 1 (by rfl) ⟨2331044, by rfl⟩ : syracuseStep 3108059 = 4662089) B4662089
theorem B5238047 : Blo 1379509 5238047 := bstep (se 1 (by rfl) ⟨3928535, by rfl⟩ : syracuseStep 5238047 = 7857071) B7857071
theorem B1379615 : Blo 1379509 1379615 := bstep (se 1 (by rfl) ⟨1034711, by rfl⟩ : syracuseStep 1379615 = 2069423) B2069423
theorem B1379675 : Blo 1379509 1379675 := bstep (se 1 (by rfl) ⟨1034756, by rfl⟩ : syracuseStep 1379675 = 2069513) B2069513
theorem B1379695 : Blo 1379509 1379695 := bstep (se 1 (by rfl) ⟨1034771, by rfl⟩ : syracuseStep 1379695 = 2069543) B2069543
theorem B3108257 : Blo 1379509 3108257 := bstep (se 2 (by rfl) ⟨1165596, by rfl⟩ : syracuseStep 3108257 = 2331193) B2331193
theorem B1379751 : Blo 1379509 1379751 := bstep (se 1 (by rfl) ⟨1034813, by rfl⟩ : syracuseStep 1379751 = 2069627) B2069627
theorem B3493307 : Blo 1379509 3493307 := bstep (se 1 (by rfl) ⟨2619980, by rfl⟩ : syracuseStep 3493307 = 5239961) B5239961
theorem B5238215 : Blo 1379509 5238215 := bstep (se 1 (by rfl) ⟨3928661, by rfl⟩ : syracuseStep 5238215 = 7857323) B7857323
theorem B1379835 : Blo 1379509 1379835 := bstep (se 1 (by rfl) ⟨1034876, by rfl⟩ : syracuseStep 1379835 = 2069753) B2069753
theorem B1379903 : Blo 1379509 1379903 := bstep (se 1 (by rfl) ⟨1034927, by rfl⟩ : syracuseStep 1379903 = 2069855) B2069855
theorem B1379911 : Blo 1379509 1379911 := bstep (se 1 (by rfl) ⟨1034933, by rfl⟩ : syracuseStep 1379911 = 2069867) B2069867
theorem B1380063 : Blo 1379509 1380063 := bstep (se 1 (by rfl) ⟨1035047, by rfl⟩ : syracuseStep 1380063 = 2070095) B2070095
theorem B6991595 : Blo 1379509 6991595 := bstep (se 1 (by rfl) ⟨5243696, by rfl⟩ : syracuseStep 6991595 = 10487393) B10487393
theorem B1380143 : Blo 1379509 1380143 := bstep (se 1 (by rfl) ⟨1035107, by rfl⟩ : syracuseStep 1380143 = 2070215) B2070215
theorem B3362615 : Blo 1379509 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1552207 : Blo 1379509 1552207 := bstep (se 1 (by rfl) ⟨1164155, by rfl⟩ : syracuseStep 1552207 = 2328311) B2328311
theorem B96964487 : Blo 1379509 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B1380251 : Blo 1379509 1380251 := bstep (se 1 (by rfl) ⟨1035188, by rfl⟩ : syracuseStep 1380251 = 2070377) B2070377
theorem B1380303 : Blo 1379509 1380303 := bstep (se 1 (by rfl) ⟨1035227, by rfl⟩ : syracuseStep 1380303 = 2070455) B2070455
theorem B1658831 : Blo 1379509 1658831 := bstep (se 1 (by rfl) ⟨1244123, by rfl⟩ : syracuseStep 1658831 = 2488247) B2488247
theorem B1380327 : Blo 1379509 1380327 := bstep (se 1 (by rfl) ⟨1035245, by rfl⟩ : syracuseStep 1380327 = 2070491) B2070491
theorem B8851457 : Blo 1379509 8851457 := bstep (se 2 (by rfl) ⟨3319296, by rfl⟩ : syracuseStep 8851457 = 6638593) B6638593
theorem B7966745 : Blo 1379509 7966745 := bstep (se 2 (by rfl) ⟨2987529, by rfl⟩ : syracuseStep 7966745 = 5975059) B5975059
theorem B4419643 : Blo 1379509 4419643 := bstep (se 1 (by rfl) ⟨3314732, by rfl⟩ : syracuseStep 4419643 = 6629465) B6629465
theorem B6992081 : Blo 1379509 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B1552603 : Blo 1379509 1552603 := bstep (se 1 (by rfl) ⟨1164452, by rfl⟩ : syracuseStep 1552603 = 2328905) B2328905
theorem B1380639 : Blo 1379509 1380639 := bstep (se 1 (by rfl) ⟨1035479, by rfl⟩ : syracuseStep 1380639 = 2070959) B2070959
theorem B4657499 : Blo 1379509 4657499 := bstep (se 1 (by rfl) ⟨3493124, by rfl⟩ : syracuseStep 4657499 = 6986249) B6986249
theorem B1380699 : Blo 1379509 1380699 := bstep (se 1 (by rfl) ⟨1035524, by rfl⟩ : syracuseStep 1380699 = 2071049) B2071049
theorem B1380719 : Blo 1379509 1380719 := bstep (se 1 (by rfl) ⟨1035539, by rfl⟩ : syracuseStep 1380719 = 2071079) B2071079
theorem B1380775 : Blo 1379509 1380775 := bstep (se 1 (by rfl) ⟨1035581, by rfl⟩ : syracuseStep 1380775 = 2071163) B2071163
theorem B11194843 : Blo 1379509 11194843 := bstep (se 1 (by rfl) ⟨8396132, by rfl⟩ : syracuseStep 11194843 = 16792265) B16792265
theorem B79598051 : Blo 1379509 79598051 := bstep (se 1 (by rfl) ⟨59698538, by rfl⟩ : syracuseStep 79598051 = 119397077) B119397077
theorem B1552891 : Blo 1379509 1552891 := bstep (se 1 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 1552891 = 2329337) B2329337
theorem B1380859 : Blo 1379509 1380859 := bstep (se 1 (by rfl) ⟨1035644, by rfl⟩ : syracuseStep 1380859 = 2071289) B2071289
theorem B1380927 : Blo 1379509 1380927 := bstep (se 1 (by rfl) ⟨1035695, by rfl⟩ : syracuseStep 1380927 = 2071391) B2071391
theorem B1380935 : Blo 1379509 1380935 := bstep (se 1 (by rfl) ⟨1035701, by rfl⟩ : syracuseStep 1380935 = 2071403) B2071403
theorem B1553071 : Blo 1379509 1553071 := bstep (se 1 (by rfl) ⟨1164803, by rfl⟩ : syracuseStep 1553071 = 2329607) B2329607
theorem B6992567 : Blo 1379509 6992567 := bstep (se 1 (by rfl) ⟨5244425, by rfl⟩ : syracuseStep 6992567 = 10488851) B10488851
theorem B5894855 : Blo 1379509 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B3494623 : Blo 1379509 3494623 := bstep (se 1 (by rfl) ⟨2620967, by rfl⟩ : syracuseStep 3494623 = 5241935) B5241935
theorem B1381087 : Blo 1379509 1381087 := bstep (se 1 (by rfl) ⟨1035815, by rfl⟩ : syracuseStep 1381087 = 2071631) B2071631
theorem B1381167 : Blo 1379509 1381167 := bstep (se 1 (by rfl) ⟨1035875, by rfl⟩ : syracuseStep 1381167 = 2071751) B2071751
theorem B2069327 : Blo 1379509 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B3494735 : Blo 1379509 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B75592561 : Blo 1379509 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B3314587 : Blo 1379509 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B1381275 : Blo 1379509 1381275 := bstep (se 1 (by rfl) ⟨1035956, by rfl⟩ : syracuseStep 1381275 = 2071913) B2071913
theorem B6632387 : Blo 1379509 6632387 := bstep (se 1 (by rfl) ⟨4974290, by rfl⟩ : syracuseStep 6632387 = 9948581) B9948581
theorem B1553359 : Blo 1379509 1553359 := bstep (se 1 (by rfl) ⟨1165019, by rfl⟩ : syracuseStep 1553359 = 2330039) B2330039
theorem B1381327 : Blo 1379509 1381327 := bstep (se 1 (by rfl) ⟨1035995, by rfl⟩ : syracuseStep 1381327 = 2071991) B2071991
theorem B6910951 : Blo 1379509 6910951 := bstep (se 1 (by rfl) ⟨5183213, by rfl⟩ : syracuseStep 6910951 = 10366427) B10366427
theorem B1381351 : Blo 1379509 1381351 := bstep (se 1 (by rfl) ⟨1036013, by rfl⟩ : syracuseStep 1381351 = 2072027) B2072027
theorem B6993053 : Blo 1379509 6993053 := bstep (se 3 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 6993053 = 2622395) B2622395
theorem B2069723 : Blo 1379509 2069723 := bstep (se 1 (by rfl) ⟨1552292, by rfl⟩ : syracuseStep 2069723 = 3104585) B3104585
theorem B6984953 : Blo 1379509 6984953 := bstep (se 2 (by rfl) ⟨2619357, by rfl⟩ : syracuseStep 6984953 = 5238715) B5238715
theorem B4658471 : Blo 1379509 4658471 := bstep (se 1 (by rfl) ⟨3493853, by rfl⟩ : syracuseStep 4658471 = 6987707) B6987707
theorem B1553755 : Blo 1379509 1553755 := bstep (se 1 (by rfl) ⟨1165316, by rfl⟩ : syracuseStep 1553755 = 2330633) B2330633
theorem B5240159 : Blo 1379509 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B37786985 : Blo 1379509 37786985 := bstep (se 2 (by rfl) ⟨14170119, by rfl⟩ : syracuseStep 37786985 = 28340239) B28340239
theorem B5240173 : Blo 1379509 5240173 := bstep (se 3 (by rfl) ⟨982532, by rfl⟩ : syracuseStep 5240173 = 1965065) B1965065
theorem B2069897 : Blo 1379509 2069897 := bstep (se 2 (by rfl) ⟨776211, by rfl⟩ : syracuseStep 2069897 = 1552423) B1552423
theorem B7861697 : Blo 1379509 7861697 := bstep (se 2 (by rfl) ⟨2948136, by rfl⟩ : syracuseStep 7861697 = 5896273) B5896273
theorem B1553863 : Blo 1379509 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B3495383 : Blo 1379509 3495383 := bstep (se 1 (by rfl) ⟨2621537, by rfl⟩ : syracuseStep 3495383 = 5243075) B5243075
theorem B2618963 : Blo 1379509 2618963 := bstep (se 1 (by rfl) ⟨1964222, by rfl⟩ : syracuseStep 2618963 = 3928445) B3928445
theorem B5240477 : Blo 1379509 5240477 := bstep (se 3 (by rfl) ⟨982589, by rfl⟩ : syracuseStep 5240477 = 1965179) B1965179
theorem B2070251 : Blo 1379509 2070251 := bstep (se 1 (by rfl) ⟨1552688, by rfl⟩ : syracuseStep 2070251 = 3105377) B3105377
theorem B2619191 : Blo 1379509 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B3495737 : Blo 1379509 3495737 := bstep (se 2 (by rfl) ⟨1310901, by rfl⟩ : syracuseStep 3495737 = 2621803) B2621803
theorem B2070479 : Blo 1379509 2070479 := bstep (se 1 (by rfl) ⟨1552859, by rfl⟩ : syracuseStep 2070479 = 3105719) B3105719
theorem B3315817 : Blo 1379509 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B4659335 : Blo 1379509 4659335 := bstep (se 1 (by rfl) ⟨3494501, by rfl⟩ : syracuseStep 4659335 = 6989003) B6989003
theorem B10483991 : Blo 1379509 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B2070875 : Blo 1379509 2070875 := bstep (se 1 (by rfl) ⟨1553156, by rfl⟩ : syracuseStep 2070875 = 3106313) B3106313
theorem B5896631 : Blo 1379509 5896631 := bstep (se 1 (by rfl) ⟨4422473, by rfl⟩ : syracuseStep 5896631 = 8844947) B8844947
theorem B2619859 : Blo 1379509 2619859 := bstep (se 1 (by rfl) ⟨1964894, by rfl⟩ : syracuseStep 2619859 = 3929789) B3929789
theorem B2071103 : Blo 1379509 2071103 := bstep (se 1 (by rfl) ⟨1553327, by rfl⟩ : syracuseStep 2071103 = 3106655) B3106655
theorem B4422217 : Blo 1379509 4422217 := bstep (se 2 (by rfl) ⟨1658331, by rfl⟩ : syracuseStep 4422217 = 3316663) B3316663
theorem B2071223 : Blo 1379509 2071223 := bstep (se 1 (by rfl) ⟨1553417, by rfl⟩ : syracuseStep 2071223 = 3106835) B3106835
theorem B6298523 : Blo 1379509 6298523 := bstep (se 1 (by rfl) ⟨4723892, by rfl⟩ : syracuseStep 6298523 = 9447785) B9447785
theorem B2071451 : Blo 1379509 2071451 := bstep (se 1 (by rfl) ⟨1553588, by rfl⟩ : syracuseStep 2071451 = 3107177) B3107177
theorem B5897231 : Blo 1379509 5897231 := bstep (se 1 (by rfl) ⟨4422923, by rfl⟩ : syracuseStep 5897231 = 8845847) B8845847
theorem B11787383 : Blo 1379509 11787383 := bstep (se 1 (by rfl) ⟨8840537, by rfl⟩ : syracuseStep 11787383 = 17681075) B17681075
theorem B2620649 : Blo 1379509 2620649 := bstep (se 2 (by rfl) ⟨982743, by rfl⟩ : syracuseStep 2620649 = 1965487) B1965487
theorem B2071847 : Blo 1379509 2071847 := bstep (se 1 (by rfl) ⟨1553885, by rfl⟩ : syracuseStep 2071847 = 3107771) B3107771
theorem B3317087 : Blo 1379509 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B4660577 : Blo 1379509 4660577 := bstep (se 2 (by rfl) ⟨1747716, by rfl⟩ : syracuseStep 4660577 = 3495433) B3495433
theorem B2071931 : Blo 1379509 2071931 := bstep (se 1 (by rfl) ⟨1553948, by rfl⟩ : syracuseStep 2071931 = 3107897) B3107897
theorem B2072057 : Blo 1379509 2072057 := bstep (se 2 (by rfl) ⟨777021, by rfl⟩ : syracuseStep 2072057 = 1554043) B1554043
theorem B3104351 : Blo 1379509 3104351 := bstep (se 1 (by rfl) ⟨2328263, by rfl⟩ : syracuseStep 3104351 = 4656527) B4656527
theorem B2072159 : Blo 1379509 2072159 := bstep (se 1 (by rfl) ⟨1554119, by rfl⟩ : syracuseStep 2072159 = 3108239) B3108239
theorem B26525303 : Blo 1379509 26525303 := bstep (se 1 (by rfl) ⟨19893977, by rfl⟩ : syracuseStep 26525303 = 39787955) B39787955
theorem B2621089 : Blo 1379509 2621089 := bstep (se 2 (by rfl) ⟨982908, by rfl⟩ : syracuseStep 2621089 = 1965817) B1965817
theorem B5242603 : Blo 1379509 5242603 := bstep (se 1 (by rfl) ⟨3931952, by rfl⟩ : syracuseStep 5242603 = 7863905) B7863905
theorem B3104567 : Blo 1379509 3104567 := bstep (se 1 (by rfl) ⟨2328425, by rfl⟩ : syracuseStep 3104567 = 4656851) B4656851
theorem B4661387 : Blo 1379509 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B2621659 : Blo 1379509 2621659 := bstep (se 1 (by rfl) ⟨1966244, by rfl⟩ : syracuseStep 2621659 = 3932489) B3932489
theorem B3104999 : Blo 1379509 3104999 := bstep (se 1 (by rfl) ⟨2328749, by rfl⟩ : syracuseStep 3104999 = 4657499) B4657499
theorem B4661711 : Blo 1379509 4661711 := bstep (se 1 (by rfl) ⟨3496283, by rfl⟩ : syracuseStep 4661711 = 6992567) B6992567
theorem B4973033 : Blo 1379509 4973033 := bstep (se 2 (by rfl) ⟨1864887, by rfl⟩ : syracuseStep 4973033 = 3729775) B3729775
theorem B1991161 : Blo 1379509 1991161 := bstep (se 2 (by rfl) ⟨746685, by rfl⟩ : syracuseStep 1991161 = 1493371) B1493371
theorem B14926457 : Blo 1379509 14926457 := bstep (se 2 (by rfl) ⟨5597421, by rfl⟩ : syracuseStep 14926457 = 11194843) B11194843
theorem B4662035 : Blo 1379509 4662035 := bstep (se 1 (by rfl) ⟨3496526, by rfl⟩ : syracuseStep 4662035 = 6993053) B6993053
theorem B3105593 : Blo 1379509 3105593 := bstep (se 2 (by rfl) ⟨1164597, by rfl⟩ : syracuseStep 3105593 = 2329195) B2329195
theorem B3105647 : Blo 1379509 3105647 := bstep (se 1 (by rfl) ⟨2329235, by rfl⟩ : syracuseStep 3105647 = 4658471) B4658471
theorem B25191323 : Blo 1379509 25191323 := bstep (se 1 (by rfl) ⟨18893492, by rfl⟩ : syracuseStep 25191323 = 37786985) B37786985
theorem B2212775 : Blo 1379509 2212775 := bstep (se 1 (by rfl) ⟨1659581, by rfl⟩ : syracuseStep 2212775 = 3319163) B3319163
theorem B1745975 : Blo 1379509 1745975 := bstep (se 1 (by rfl) ⟨1309481, by rfl⟩ : syracuseStep 1745975 = 2618963) B2618963
theorem B10093673 : Blo 1379509 10093673 := bstep (se 2 (by rfl) ⟨3785127, by rfl⟩ : syracuseStep 10093673 = 7570255) B7570255
theorem B1746127 : Blo 1379509 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B3106223 : Blo 1379509 3106223 := bstep (se 1 (by rfl) ⟨2329667, by rfl⟩ : syracuseStep 3106223 = 4659335) B4659335
theorem B6989327 : Blo 1379509 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B3983015 : Blo 1379509 3983015 := bstep (se 1 (by rfl) ⟨2987261, by rfl⟩ : syracuseStep 3983015 = 5974523) B5974523
theorem B17696657 : Blo 1379509 17696657 := bstep (se 2 (by rfl) ⟨6636246, by rfl⟩ : syracuseStep 17696657 = 13272493) B13272493
theorem B7858255 : Blo 1379509 7858255 := bstep (se 1 (by rfl) ⟨5893691, by rfl⟩ : syracuseStep 7858255 = 11787383) B11787383
theorem B7866503 : Blo 1379509 7866503 := bstep (se 1 (by rfl) ⟨5899877, by rfl⟩ : syracuseStep 7866503 = 11799755) B11799755
theorem B147433621 : Blo 1379509 147433621 := bstep (se 6 (by rfl) ⟨3455475, by rfl⟩ : syracuseStep 147433621 = 6910951) B6910951
theorem B1747099 : Blo 1379509 1747099 := bstep (se 1 (by rfl) ⟨1310324, by rfl⟩ : syracuseStep 1747099 = 2620649) B2620649
theorem B3492031 : Blo 1379509 3492031 := bstep (se 1 (by rfl) ⟨2619023, by rfl⟩ : syracuseStep 3492031 = 5238047) B5238047
theorem B22382801 : Blo 1379509 22382801 := bstep (se 2 (by rfl) ⟨8393550, by rfl⟩ : syracuseStep 22382801 = 16787101) B16787101
theorem B3107051 : Blo 1379509 3107051 := bstep (se 1 (by rfl) ⟨2330288, by rfl⟩ : syracuseStep 3107051 = 4660577) B4660577
theorem B2328871 : Blo 1379509 2328871 := bstep (se 1 (by rfl) ⟨1746653, by rfl⟩ : syracuseStep 2328871 = 3493307) B3493307
theorem B3492143 : Blo 1379509 3492143 := bstep (se 1 (by rfl) ⟨2619107, by rfl⟩ : syracuseStep 3492143 = 5238215) B5238215
theorem B6990137 : Blo 1379509 6990137 := bstep (se 2 (by rfl) ⟨2621301, by rfl⟩ : syracuseStep 6990137 = 5242603) B5242603
theorem B11192701 : Blo 1379509 11192701 := bstep (se 3 (by rfl) ⟨2098631, by rfl⟩ : syracuseStep 11192701 = 4197263) B4197263
theorem B5900971 : Blo 1379509 5900971 := bstep (se 1 (by rfl) ⟨4425728, by rfl⟩ : syracuseStep 5900971 = 8851457) B8851457
theorem B5311163 : Blo 1379509 5311163 := bstep (se 1 (by rfl) ⟨3983372, by rfl⟩ : syracuseStep 5311163 = 7966745) B7966745
theorem B5892857 : Blo 1379509 5892857 := bstep (se 2 (by rfl) ⟨2209821, by rfl⟩ : syracuseStep 5892857 = 4419643) B4419643
theorem B6990785 : Blo 1379509 6990785 := bstep (se 2 (by rfl) ⟨2621544, by rfl⟩ : syracuseStep 6990785 = 5243089) B5243089
theorem B1379551 : Blo 1379509 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B2329823 : Blo 1379509 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B3493145 : Blo 1379509 3493145 := bstep (se 2 (by rfl) ⟨1309929, by rfl⟩ : syracuseStep 3493145 = 2619859) B2619859
theorem B262016441 : Blo 1379509 262016441 := bstep (se 2 (by rfl) ⟨98256165, by rfl⟩ : syracuseStep 262016441 = 196512331) B196512331
theorem B1379815 : Blo 1379509 1379815 := bstep (se 1 (by rfl) ⟨1034861, by rfl⟩ : syracuseStep 1379815 = 2069723) B2069723
theorem B17698297 : Blo 1379509 17698297 := bstep (se 2 (by rfl) ⟨6636861, by rfl⟩ : syracuseStep 17698297 = 13273723) B13273723
theorem B10489337 : Blo 1379509 10489337 := bstep (se 2 (by rfl) ⟨3933501, by rfl⟩ : syracuseStep 10489337 = 7867003) B7867003
theorem B4656635 : Blo 1379509 4656635 := bstep (se 1 (by rfl) ⟨3492476, by rfl⟩ : syracuseStep 4656635 = 6984953) B6984953
theorem B3108347 : Blo 1379509 3108347 := bstep (se 1 (by rfl) ⟨2331260, by rfl⟩ : syracuseStep 3108347 = 4662521) B4662521
theorem B3493439 : Blo 1379509 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B6991433 : Blo 1379509 6991433 := bstep (se 2 (by rfl) ⟨2621787, by rfl⟩ : syracuseStep 6991433 = 5243575) B5243575
theorem B1379931 : Blo 1379509 1379931 := bstep (se 1 (by rfl) ⟨1034948, by rfl⟩ : syracuseStep 1379931 = 2069897) B2069897
theorem B2330255 : Blo 1379509 2330255 := bstep (se 1 (by rfl) ⟨1747691, by rfl⟩ : syracuseStep 2330255 = 3495383) B3495383
theorem B4656797 : Blo 1379509 4656797 := bstep (se 3 (by rfl) ⟨873149, by rfl⟩ : syracuseStep 4656797 = 1746299) B1746299
theorem B7859987 : Blo 1379509 7859987 := bstep (se 1 (by rfl) ⟨5894990, by rfl⟩ : syracuseStep 7859987 = 11789981) B11789981
theorem B3493651 : Blo 1379509 3493651 := bstep (se 1 (by rfl) ⟨2620238, by rfl⟩ : syracuseStep 3493651 = 5240477) B5240477
theorem B100790081 : Blo 1379509 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B1380167 : Blo 1379509 1380167 := bstep (se 1 (by rfl) ⟨1035125, by rfl⟩ : syracuseStep 1380167 = 2070251) B2070251
theorem B4419449 : Blo 1379509 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B2330491 : Blo 1379509 2330491 := bstep (se 1 (by rfl) ⟨1747868, by rfl⟩ : syracuseStep 2330491 = 3495737) B3495737
theorem B17690507 : Blo 1379509 17690507 := bstep (se 1 (by rfl) ⟨13267880, by rfl⟩ : syracuseStep 17690507 = 26535761) B26535761
theorem B2486171 : Blo 1379509 2486171 := bstep (se 1 (by rfl) ⟨1864628, by rfl⟩ : syracuseStep 2486171 = 3729257) B3729257
theorem B1552351 : Blo 1379509 1552351 := bstep (se 1 (by rfl) ⟨1164263, by rfl⟩ : syracuseStep 1552351 = 2328527) B2328527
theorem B1380319 : Blo 1379509 1380319 := bstep (se 1 (by rfl) ⟨1035239, by rfl⟩ : syracuseStep 1380319 = 2070479) B2070479
theorem B9957343 : Blo 1379509 9957343 := bstep (se 1 (by rfl) ⟨7468007, by rfl⟩ : syracuseStep 9957343 = 14936015) B14936015
theorem B8851609 : Blo 1379509 8851609 := bstep (se 2 (by rfl) ⟨3319353, by rfl⟩ : syracuseStep 8851609 = 6638707) B6638707
theorem B4657337 : Blo 1379509 4657337 := bstep (se 2 (by rfl) ⟨1746501, by rfl⟩ : syracuseStep 4657337 = 3493003) B3493003
theorem B1380583 : Blo 1379509 1380583 := bstep (se 1 (by rfl) ⟨1035437, by rfl⟩ : syracuseStep 1380583 = 2070875) B2070875
theorem B18886915 : Blo 1379509 18886915 := bstep (se 1 (by rfl) ⟨14165186, by rfl⟩ : syracuseStep 18886915 = 28330373) B28330373
theorem B1380735 : Blo 1379509 1380735 := bstep (se 1 (by rfl) ⟨1035551, by rfl⟩ : syracuseStep 1380735 = 2071103) B2071103
theorem B17011109 : Blo 1379509 17011109 := bstep (se 4 (by rfl) ⟨1594791, by rfl⟩ : syracuseStep 17011109 = 3189583) B3189583
theorem B26915273 : Blo 1379509 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B1380815 : Blo 1379509 1380815 := bstep (se 1 (by rfl) ⟨1035611, by rfl⟩ : syracuseStep 1380815 = 2071223) B2071223
theorem B1552999 : Blo 1379509 1552999 := bstep (se 1 (by rfl) ⟨1164749, by rfl⟩ : syracuseStep 1552999 = 2329499) B2329499
theorem B4199015 : Blo 1379509 4199015 := bstep (se 1 (by rfl) ⟨3149261, by rfl⟩ : syracuseStep 4199015 = 6298523) B6298523
theorem B1380967 : Blo 1379509 1380967 := bstep (se 1 (by rfl) ⟨1035725, by rfl⟩ : syracuseStep 1380967 = 2071451) B2071451
theorem B10089131 : Blo 1379509 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B1381231 : Blo 1379509 1381231 := bstep (se 1 (by rfl) ⟨1035923, by rfl⟩ : syracuseStep 1381231 = 2071847) B2071847
theorem B3494785 : Blo 1379509 3494785 := bstep (se 2 (by rfl) ⟨1310544, by rfl⟩ : syracuseStep 3494785 = 2621089) B2621089
theorem B1381287 : Blo 1379509 1381287 := bstep (se 1 (by rfl) ⟨1035965, by rfl⟩ : syracuseStep 1381287 = 2071931) B2071931
theorem B143471573 : Blo 1379509 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B1381371 : Blo 1379509 1381371 := bstep (se 1 (by rfl) ⟨1036028, by rfl⟩ : syracuseStep 1381371 = 2072057) B2072057
theorem B2069567 : Blo 1379509 2069567 := bstep (se 1 (by rfl) ⟨1552175, by rfl⟩ : syracuseStep 2069567 = 3104351) B3104351
theorem B1381439 : Blo 1379509 1381439 := bstep (se 1 (by rfl) ⟨1036079, by rfl⟩ : syracuseStep 1381439 = 2072159) B2072159
theorem B17683535 : Blo 1379509 17683535 := bstep (se 1 (by rfl) ⟨13262651, by rfl⟩ : syracuseStep 17683535 = 26525303) B26525303
theorem B2069609 : Blo 1379509 2069609 := bstep (se 2 (by rfl) ⟨776103, by rfl⟩ : syracuseStep 2069609 = 1552207) B1552207
theorem B2069711 : Blo 1379509 2069711 := bstep (se 1 (by rfl) ⟨1552283, by rfl⟩ : syracuseStep 2069711 = 3104567) B3104567
theorem B2069915 : Blo 1379509 2069915 := bstep (se 1 (by rfl) ⟨1552436, by rfl⟩ : syracuseStep 2069915 = 3104873) B3104873
theorem B4421089 : Blo 1379509 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B15947297 : Blo 1379509 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B2070137 : Blo 1379509 2070137 := bstep (se 2 (by rfl) ⟨776301, by rfl⟩ : syracuseStep 2070137 = 1552603) B1552603
theorem B53065367 : Blo 1379509 53065367 := bstep (se 1 (by rfl) ⟨39799025, by rfl⟩ : syracuseStep 53065367 = 79598051) B79598051
theorem B3495595 : Blo 1379509 3495595 := bstep (se 1 (by rfl) ⟨2621696, by rfl⟩ : syracuseStep 3495595 = 5243393) B5243393
theorem B2070239 : Blo 1379509 2070239 := bstep (se 1 (by rfl) ⟨1552679, by rfl⟩ : syracuseStep 2070239 = 3105359) B3105359
theorem B3929903 : Blo 1379509 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B2070335 : Blo 1379509 2070335 := bstep (se 1 (by rfl) ⟨1552751, by rfl⟩ : syracuseStep 2070335 = 3105503) B3105503
theorem B15734735 : Blo 1379509 15734735 := bstep (se 1 (by rfl) ⟨11801051, by rfl⟩ : syracuseStep 15734735 = 23602103) B23602103
theorem B4421591 : Blo 1379509 4421591 := bstep (se 1 (by rfl) ⟨3316193, by rfl⟩ : syracuseStep 4421591 = 6632387) B6632387
theorem B3495899 : Blo 1379509 3495899 := bstep (se 1 (by rfl) ⟨2621924, by rfl⟩ : syracuseStep 3495899 = 5243849) B5243849
theorem B2070503 : Blo 1379509 2070503 := bstep (se 1 (by rfl) ⟨1552877, by rfl⟩ : syracuseStep 2070503 = 3105755) B3105755
theorem B3495919 : Blo 1379509 3495919 := bstep (se 1 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 3495919 = 5243879) B5243879
theorem B2070521 : Blo 1379509 2070521 := bstep (se 2 (by rfl) ⟨776445, by rfl⟩ : syracuseStep 2070521 = 1552891) B1552891
theorem B14161987 : Blo 1379509 14161987 := bstep (se 1 (by rfl) ⟨10621490, by rfl⟩ : syracuseStep 14161987 = 21242981) B21242981
theorem B2070623 : Blo 1379509 2070623 := bstep (se 1 (by rfl) ⟨1552967, by rfl⟩ : syracuseStep 2070623 = 3105935) B3105935
theorem B3496031 : Blo 1379509 3496031 := bstep (se 1 (by rfl) ⟨2622023, by rfl⟩ : syracuseStep 3496031 = 5244047) B5244047
theorem B5896289 : Blo 1379509 5896289 := bstep (se 2 (by rfl) ⟨2211108, by rfl⟩ : syracuseStep 5896289 = 4422217) B4422217
theorem B2070683 : Blo 1379509 2070683 := bstep (se 1 (by rfl) ⟨1553012, by rfl⟩ : syracuseStep 2070683 = 3106025) B3106025
theorem B2070719 : Blo 1379509 2070719 := bstep (se 1 (by rfl) ⟨1553039, by rfl⟩ : syracuseStep 2070719 = 3106079) B3106079
theorem B2070761 : Blo 1379509 2070761 := bstep (se 2 (by rfl) ⟨776535, by rfl⟩ : syracuseStep 2070761 = 1553071) B1553071
theorem B4659443 : Blo 1379509 4659443 := bstep (se 1 (by rfl) ⟨3494582, by rfl⟩ : syracuseStep 4659443 = 6989165) B6989165
theorem B4659497 : Blo 1379509 4659497 := bstep (se 2 (by rfl) ⟨1747311, by rfl⟩ : syracuseStep 4659497 = 3494623) B3494623
theorem B5241131 : Blo 1379509 5241131 := bstep (se 1 (by rfl) ⟨3930848, by rfl⟩ : syracuseStep 5241131 = 7861697) B7861697
theorem B2071067 : Blo 1379509 2071067 := bstep (se 1 (by rfl) ⟨1553300, by rfl⟩ : syracuseStep 2071067 = 3106601) B3106601
theorem B2071145 : Blo 1379509 2071145 := bstep (se 2 (by rfl) ⟨776679, by rfl⟩ : syracuseStep 2071145 = 1553359) B1553359
theorem B3931087 : Blo 1379509 3931087 := bstep (se 1 (by rfl) ⟨2948315, by rfl⟩ : syracuseStep 3931087 = 5896631) B5896631
theorem B2071673 : Blo 1379509 2071673 := bstep (se 2 (by rfl) ⟨776877, by rfl⟩ : syracuseStep 2071673 = 1553755) B1553755
theorem B6986897 : Blo 1379509 6986897 := bstep (se 2 (by rfl) ⟨2620086, by rfl⟩ : syracuseStep 6986897 = 5240173) B5240173
theorem B9944221 : Blo 1379509 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B2071775 : Blo 1379509 2071775 := bstep (se 1 (by rfl) ⟨1553831, by rfl⟩ : syracuseStep 2071775 = 3107663) B3107663
theorem B3104009 : Blo 1379509 3104009 := bstep (se 2 (by rfl) ⟨1164003, by rfl⟩ : syracuseStep 3104009 = 2328007) B2328007
theorem B2071817 : Blo 1379509 2071817 := bstep (se 2 (by rfl) ⟨776931, by rfl⟩ : syracuseStep 2071817 = 1553863) B1553863
theorem B3931487 : Blo 1379509 3931487 := bstep (se 1 (by rfl) ⟨2948615, by rfl⟩ : syracuseStep 3931487 = 5897231) B5897231
theorem B2071919 : Blo 1379509 2071919 := bstep (se 1 (by rfl) ⟨1553939, by rfl⟩ : syracuseStep 2071919 = 3107879) B3107879
theorem B5594599 : Blo 1379509 5594599 := bstep (se 1 (by rfl) ⟨4195949, by rfl⟩ : syracuseStep 5594599 = 8391899) B8391899
theorem B2072039 : Blo 1379509 2072039 := bstep (se 1 (by rfl) ⟨1554029, by rfl⟩ : syracuseStep 2072039 = 3108059) B3108059
theorem B17694197 : Blo 1379509 17694197 := bstep (se 5 (by rfl) ⟨829415, by rfl⟩ : syracuseStep 17694197 = 1658831) B1658831
theorem B2211391 : Blo 1379509 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B2072171 : Blo 1379509 2072171 := bstep (se 1 (by rfl) ⟨1554128, by rfl⟩ : syracuseStep 2072171 = 3108257) B3108257
theorem B4661063 : Blo 1379509 4661063 := bstep (se 1 (by rfl) ⟨3495797, by rfl⟩ : syracuseStep 4661063 = 6991595) B6991595
theorem B4661117 : Blo 1379509 4661117 := bstep (se 3 (by rfl) ⟨873959, by rfl⟩ : syracuseStep 4661117 = 1747919) B1747919
theorem B64642991 : Blo 1379509 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B18882649 : Blo 1379509 18882649 := bstep (se 2 (by rfl) ⟨7080993, by rfl⟩ : syracuseStep 18882649 = 14161987) B14161987
theorem B10477673 : Blo 1379509 10477673 := bstep (se 2 (by rfl) ⟨3929127, by rfl⟩ : syracuseStep 10477673 = 7858255) B7858255
theorem B3104891 : Blo 1379509 3104891 := bstep (se 1 (by rfl) ⟨2328668, by rfl⟩ : syracuseStep 3104891 = 4657337) B4657337
theorem B3105161 : Blo 1379509 3105161 := bstep (se 2 (by rfl) ⟨1164435, by rfl⟩ : syracuseStep 3105161 = 2328871) B2328871
theorem B16794215 : Blo 1379509 16794215 := bstep (se 1 (by rfl) ⟨12595661, by rfl⟩ : syracuseStep 16794215 = 25191323) B25191323
theorem B1475183 : Blo 1379509 1475183 := bstep (se 1 (by rfl) ⟨1106387, by rfl⟩ : syracuseStep 1475183 = 2212775) B2212775
theorem B11789023 : Blo 1379509 11789023 := bstep (se 1 (by rfl) ⟨8841767, by rfl⟩ : syracuseStep 11789023 = 17683535) B17683535
theorem B2655343 : Blo 1379509 2655343 := bstep (se 1 (by rfl) ⟨1991507, by rfl⟩ : syracuseStep 2655343 = 3983015) B3983015
theorem B11797771 : Blo 1379509 11797771 := bstep (se 1 (by rfl) ⟨8848328, by rfl⟩ : syracuseStep 11797771 = 17696657) B17696657
theorem B100730213 : Blo 1379509 100730213 := bstep (se 4 (by rfl) ⟨9443457, by rfl⟩ : syracuseStep 100730213 = 18886915) B18886915
theorem B5244335 : Blo 1379509 5244335 := bstep (se 1 (by rfl) ⟨3933251, by rfl⟩ : syracuseStep 5244335 = 7866503) B7866503
theorem B3106295 : Blo 1379509 3106295 := bstep (se 1 (by rfl) ⟨2329721, by rfl⟩ : syracuseStep 3106295 = 4659443) B4659443
theorem B3106331 : Blo 1379509 3106331 := bstep (se 1 (by rfl) ⟨2329748, by rfl⟩ : syracuseStep 3106331 = 4659497) B4659497
theorem B2328095 : Blo 1379509 2328095 := bstep (se 1 (by rfl) ⟨1746071, by rfl⟩ : syracuseStep 2328095 = 3492143) B3492143
theorem B2328169 : Blo 1379509 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B26904349 : Blo 1379509 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B3540775 : Blo 1379509 3540775 := bstep (se 1 (by rfl) ⟨2655581, by rfl⟩ : syracuseStep 3540775 = 5311163) B5311163
theorem B2328763 : Blo 1379509 2328763 := bstep (se 1 (by rfl) ⟨1746572, by rfl⟩ : syracuseStep 2328763 = 3493145) B3493145
theorem B2328959 : Blo 1379509 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B6629789 : Blo 1379509 6629789 := bstep (se 3 (by rfl) ⟨1243085, by rfl⟩ : syracuseStep 6629789 = 2486171) B2486171
theorem B3107321 : Blo 1379509 3107321 := bstep (se 2 (by rfl) ⟨1165245, by rfl⟩ : syracuseStep 3107321 = 2330491) B2330491
theorem B67193387 : Blo 1379509 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B3107375 : Blo 1379509 3107375 := bstep (se 1 (by rfl) ⟨2330531, by rfl⟩ : syracuseStep 3107375 = 4661063) B4661063
theorem B3107411 : Blo 1379509 3107411 := bstep (se 1 (by rfl) ⟨2330558, by rfl⟩ : syracuseStep 3107411 = 4661117) B4661117
theorem B10619525 : Blo 1379509 10619525 := bstep (se 4 (by rfl) ⟨995580, by rfl⟩ : syracuseStep 10619525 = 1991161) B1991161
theorem B3107591 : Blo 1379509 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B4655933 : Blo 1379509 4655933 := bstep (se 3 (by rfl) ⟨872987, by rfl⟩ : syracuseStep 4655933 = 1745975) B1745975
theorem B196578161 : Blo 1379509 196578161 := bstep (se 2 (by rfl) ⟨73716810, by rfl⟩ : syracuseStep 196578161 = 147433621) B147433621
theorem B2329465 : Blo 1379509 2329465 := bstep (se 2 (by rfl) ⟨873549, by rfl⟩ : syracuseStep 2329465 = 1747099) B1747099
theorem B4656041 : Blo 1379509 4656041 := bstep (se 2 (by rfl) ⟨1746015, by rfl⟩ : syracuseStep 4656041 = 3492031) B3492031
theorem B11340739 : Blo 1379509 11340739 := bstep (se 1 (by rfl) ⟨8505554, by rfl⟩ : syracuseStep 11340739 = 17011109) B17011109
theorem B17943515 : Blo 1379509 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B3107807 : Blo 1379509 3107807 := bstep (se 1 (by rfl) ⟨2330855, by rfl⟩ : syracuseStep 3107807 = 4661711) B4661711
theorem B3108023 : Blo 1379509 3108023 := bstep (se 1 (by rfl) ⟨2331017, by rfl⟩ : syracuseStep 3108023 = 4662035) B4662035
theorem B1379711 : Blo 1379509 1379711 := bstep (se 1 (by rfl) ⟨1034783, by rfl⟩ : syracuseStep 1379711 = 2069567) B2069567
theorem B1379739 : Blo 1379509 1379739 := bstep (se 1 (by rfl) ⟨1034804, by rfl⟩ : syracuseStep 1379739 = 2069609) B2069609
theorem B6729115 : Blo 1379509 6729115 := bstep (se 1 (by rfl) ⟨5046836, by rfl⟩ : syracuseStep 6729115 = 10093673) B10093673
theorem B1379807 : Blo 1379509 1379807 := bstep (se 1 (by rfl) ⟨1034855, by rfl⟩ : syracuseStep 1379807 = 2069711) B2069711
theorem B7867961 : Blo 1379509 7867961 := bstep (se 2 (by rfl) ⟨2950485, by rfl⟩ : syracuseStep 7867961 = 5900971) B5900971
theorem B1379943 : Blo 1379509 1379943 := bstep (se 1 (by rfl) ⟨1034957, by rfl⟩ : syracuseStep 1379943 = 2069915) B2069915
theorem B1380091 : Blo 1379509 1380091 := bstep (se 1 (by rfl) ⟨1035068, by rfl⟩ : syracuseStep 1380091 = 2070137) B2070137
theorem B35376911 : Blo 1379509 35376911 := bstep (se 1 (by rfl) ⟨26532683, by rfl⟩ : syracuseStep 35376911 = 53065367) B53065367
theorem B1380159 : Blo 1379509 1380159 := bstep (se 1 (by rfl) ⟨1035119, by rfl⟩ : syracuseStep 1380159 = 2070239) B2070239
theorem B1380223 : Blo 1379509 1380223 := bstep (se 1 (by rfl) ⟨1035167, by rfl⟩ : syracuseStep 1380223 = 2070335) B2070335
theorem B10489823 : Blo 1379509 10489823 := bstep (se 1 (by rfl) ⟨7867367, by rfl⟩ : syracuseStep 10489823 = 15734735) B15734735
theorem B2330599 : Blo 1379509 2330599 := bstep (se 1 (by rfl) ⟨1747949, by rfl⟩ : syracuseStep 2330599 = 3495899) B3495899
theorem B1380335 : Blo 1379509 1380335 := bstep (se 1 (by rfl) ⟨1035251, by rfl⟩ : syracuseStep 1380335 = 2070503) B2070503
theorem B1380347 : Blo 1379509 1380347 := bstep (se 1 (by rfl) ⟨1035260, by rfl⟩ : syracuseStep 1380347 = 2070521) B2070521
theorem B1380415 : Blo 1379509 1380415 := bstep (se 1 (by rfl) ⟨1035311, by rfl⟩ : syracuseStep 1380415 = 2070623) B2070623
theorem B2330687 : Blo 1379509 2330687 := bstep (se 1 (by rfl) ⟨1748015, by rfl⟩ : syracuseStep 2330687 = 3496031) B3496031
theorem B1380455 : Blo 1379509 1380455 := bstep (se 1 (by rfl) ⟨1035341, by rfl⟩ : syracuseStep 1380455 = 2070683) B2070683
theorem B1380479 : Blo 1379509 1380479 := bstep (se 1 (by rfl) ⟨1035359, by rfl⟩ : syracuseStep 1380479 = 2070719) B2070719
theorem B14921867 : Blo 1379509 14921867 := bstep (se 1 (by rfl) ⟨11191400, by rfl⟩ : syracuseStep 14921867 = 22382801) B22382801
theorem B1380507 : Blo 1379509 1380507 := bstep (se 1 (by rfl) ⟨1035380, by rfl⟩ : syracuseStep 1380507 = 2070761) B2070761
theorem B3494087 : Blo 1379509 3494087 := bstep (se 1 (by rfl) ⟨2620565, by rfl⟩ : syracuseStep 3494087 = 5241131) B5241131
theorem B13258961 : Blo 1379509 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B1380711 : Blo 1379509 1380711 := bstep (se 1 (by rfl) ⟨1035533, by rfl⟩ : syracuseStep 1380711 = 2071067) B2071067
theorem B1380763 : Blo 1379509 1380763 := bstep (se 1 (by rfl) ⟨1035572, by rfl⟩ : syracuseStep 1380763 = 2071145) B2071145
theorem B689525237 : Blo 1379509 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B3928571 : Blo 1379509 3928571 := bstep (se 1 (by rfl) ⟨2946428, by rfl⟩ : syracuseStep 3928571 = 5892857) B5892857
theorem B5894785 : Blo 1379509 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B7459465 : Blo 1379509 7459465 := bstep (se 2 (by rfl) ⟨2797299, by rfl⟩ : syracuseStep 7459465 = 5594599) B5594599
theorem B23597729 : Blo 1379509 23597729 := bstep (se 2 (by rfl) ⟨8849148, by rfl⟩ : syracuseStep 23597729 = 17698297) B17698297
theorem B1381115 : Blo 1379509 1381115 := bstep (se 1 (by rfl) ⟨1035836, by rfl⟩ : syracuseStep 1381115 = 2071673) B2071673
theorem B4657931 : Blo 1379509 4657931 := bstep (se 1 (by rfl) ⟨3493448, by rfl⟩ : syracuseStep 4657931 = 6986897) B6986897
theorem B1553215 : Blo 1379509 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B1381183 : Blo 1379509 1381183 := bstep (se 1 (by rfl) ⟨1035887, by rfl⟩ : syracuseStep 1381183 = 2071775) B2071775
theorem B2069339 : Blo 1379509 2069339 := bstep (se 1 (by rfl) ⟨1552004, by rfl⟩ : syracuseStep 2069339 = 3104009) B3104009
theorem B1381211 : Blo 1379509 1381211 := bstep (se 1 (by rfl) ⟨1035908, by rfl⟩ : syracuseStep 1381211 = 2071817) B2071817
theorem B1381279 : Blo 1379509 1381279 := bstep (se 1 (by rfl) ⟨1035959, by rfl⟩ : syracuseStep 1381279 = 2071919) B2071919
theorem B1381359 : Blo 1379509 1381359 := bstep (se 1 (by rfl) ⟨1036019, by rfl⟩ : syracuseStep 1381359 = 2072039) B2072039
theorem B6992891 : Blo 1379509 6992891 := bstep (se 1 (by rfl) ⟨5244668, by rfl⟩ : syracuseStep 6992891 = 10489337) B10489337
theorem B4658201 : Blo 1379509 4658201 := bstep (se 2 (by rfl) ⟨1746825, by rfl⟩ : syracuseStep 4658201 = 3493651) B3493651
theorem B1381447 : Blo 1379509 1381447 := bstep (se 1 (by rfl) ⟨1036085, by rfl⟩ : syracuseStep 1381447 = 2072171) B2072171
theorem B1553503 : Blo 1379509 1553503 := bstep (se 1 (by rfl) ⟨1165127, by rfl⟩ : syracuseStep 1553503 = 2330255) B2330255
theorem B5239991 : Blo 1379509 5239991 := bstep (se 1 (by rfl) ⟨3929993, by rfl⟩ : syracuseStep 5239991 = 7859987) B7859987
theorem B2946299 : Blo 1379509 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B11793671 : Blo 1379509 11793671 := bstep (se 1 (by rfl) ⟨8845253, by rfl⟩ : syracuseStep 11793671 = 17690507) B17690507
theorem B2069801 : Blo 1379509 2069801 := bstep (se 2 (by rfl) ⟨776175, by rfl⟩ : syracuseStep 2069801 = 1552351) B1552351
theorem B13276457 : Blo 1379509 13276457 := bstep (se 2 (by rfl) ⟨4978671, by rfl⟩ : syracuseStep 13276457 = 9957343) B9957343
theorem B2069999 : Blo 1379509 2069999 := bstep (se 1 (by rfl) ⟨1552499, by rfl⟩ : syracuseStep 2069999 = 3104999) B3104999
theorem B11802145 : Blo 1379509 11802145 := bstep (se 2 (by rfl) ⟨4425804, by rfl⟩ : syracuseStep 11802145 = 8851609) B8851609
theorem B3495545 : Blo 1379509 3495545 := bstep (se 2 (by rfl) ⟨1310829, by rfl⟩ : syracuseStep 3495545 = 2621659) B2621659
theorem B2799343 : Blo 1379509 2799343 := bstep (se 1 (by rfl) ⟨2099507, by rfl⟩ : syracuseStep 2799343 = 4199015) B4199015
theorem B9950971 : Blo 1379509 9950971 := bstep (se 1 (by rfl) ⟨7463228, by rfl⟩ : syracuseStep 9950971 = 14926457) B14926457
theorem B14923601 : Blo 1379509 14923601 := bstep (se 2 (by rfl) ⟨5596350, by rfl⟩ : syracuseStep 14923601 = 11192701) B11192701
theorem B2070395 : Blo 1379509 2070395 := bstep (se 1 (by rfl) ⟨1552796, by rfl⟩ : syracuseStep 2070395 = 3105593) B3105593
theorem B2070431 : Blo 1379509 2070431 := bstep (se 1 (by rfl) ⟨1552823, by rfl⟩ : syracuseStep 2070431 = 3105647) B3105647
theorem B95647715 : Blo 1379509 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B2070665 : Blo 1379509 2070665 := bstep (se 2 (by rfl) ⟨776499, by rfl⟩ : syracuseStep 2070665 = 1552999) B1552999
theorem B2070815 : Blo 1379509 2070815 := bstep (se 1 (by rfl) ⟨1553111, by rfl⟩ : syracuseStep 2070815 = 3106223) B3106223
theorem B4659551 : Blo 1379509 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B10631531 : Blo 1379509 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B4659713 : Blo 1379509 4659713 := bstep (se 2 (by rfl) ⟨1747392, by rfl⟩ : syracuseStep 4659713 = 3494785) B3494785
theorem B2619935 : Blo 1379509 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B5241449 : Blo 1379509 5241449 := bstep (se 2 (by rfl) ⟨1965543, by rfl⟩ : syracuseStep 5241449 = 3931087) B3931087
theorem B13261421 : Blo 1379509 13261421 := bstep (se 3 (by rfl) ⟨2486516, by rfl⟩ : syracuseStep 13261421 = 4973033) B4973033
theorem B2947727 : Blo 1379509 2947727 := bstep (se 1 (by rfl) ⟨2210795, by rfl⟩ : syracuseStep 2947727 = 4421591) B4421591
theorem B3930859 : Blo 1379509 3930859 := bstep (se 1 (by rfl) ⟨2948144, by rfl⟩ : syracuseStep 3930859 = 5896289) B5896289
theorem B2071367 : Blo 1379509 2071367 := bstep (se 1 (by rfl) ⟨1553525, by rfl⟩ : syracuseStep 2071367 = 3107051) B3107051
theorem B4660091 : Blo 1379509 4660091 := bstep (se 1 (by rfl) ⟨3495068, by rfl⟩ : syracuseStep 4660091 = 6990137) B6990137
theorem B4660523 : Blo 1379509 4660523 := bstep (se 1 (by rfl) ⟨3495392, by rfl⟩ : syracuseStep 4660523 = 6990785) B6990785
theorem B2948521 : Blo 1379509 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B4660793 : Blo 1379509 4660793 := bstep (se 2 (by rfl) ⟨1747797, by rfl⟩ : syracuseStep 4660793 = 3495595) B3495595
theorem B2620991 : Blo 1379509 2620991 := bstep (se 1 (by rfl) ⟨1965743, by rfl⟩ : syracuseStep 2620991 = 3931487) B3931487
theorem B174677627 : Blo 1379509 174677627 := bstep (se 1 (by rfl) ⟨131008220, by rfl⟩ : syracuseStep 174677627 = 262016441) B262016441
theorem B11796131 : Blo 1379509 11796131 := bstep (se 1 (by rfl) ⟨8847098, by rfl⟩ : syracuseStep 11796131 = 17694197) B17694197
theorem B3104423 : Blo 1379509 3104423 := bstep (se 1 (by rfl) ⟨2328317, by rfl⟩ : syracuseStep 3104423 = 4656635) B4656635
theorem B2072231 : Blo 1379509 2072231 := bstep (se 1 (by rfl) ⟨1554173, by rfl⟩ : syracuseStep 2072231 = 3108347) B3108347
theorem B4660955 : Blo 1379509 4660955 := bstep (se 1 (by rfl) ⟨3495716, by rfl⟩ : syracuseStep 4660955 = 6991433) B6991433
theorem B3104531 : Blo 1379509 3104531 := bstep (se 1 (by rfl) ⟨2328398, by rfl⟩ : syracuseStep 3104531 = 4656797) B4656797
theorem B4661225 : Blo 1379509 4661225 := bstep (se 2 (by rfl) ⟨1747959, by rfl⟩ : syracuseStep 4661225 = 3495919) B3495919
theorem B8839307 : Blo 1379509 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B3105017 : Blo 1379509 3105017 := bstep (se 2 (by rfl) ⟨1164381, by rfl⟩ : syracuseStep 3105017 = 2328763) B2328763
theorem B3105287 : Blo 1379509 3105287 := bstep (se 1 (by rfl) ⟨2328965, by rfl⟩ : syracuseStep 3105287 = 4657931) B4657931
theorem B7856797 : Blo 1379509 7856797 := bstep (se 3 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 7856797 = 2946299) B2946299
theorem B4661927 : Blo 1379509 4661927 := bstep (se 1 (by rfl) ⟨3496445, by rfl⟩ : syracuseStep 4661927 = 6992891) B6992891
theorem B3105467 : Blo 1379509 3105467 := bstep (se 1 (by rfl) ⟨2329100, by rfl⟩ : syracuseStep 3105467 = 4658201) B4658201
theorem B9945953 : Blo 1379509 9945953 := bstep (se 2 (by rfl) ⟨3729732, by rfl⟩ : syracuseStep 9945953 = 7459465) B7459465
theorem B3105953 : Blo 1379509 3105953 := bstep (se 2 (by rfl) ⟨1164732, by rfl⟩ : syracuseStep 3105953 = 2329465) B2329465
theorem B3540457 : Blo 1379509 3540457 := bstep (se 2 (by rfl) ⟨1327671, by rfl⟩ : syracuseStep 3540457 = 2655343) B2655343
theorem B3106367 : Blo 1379509 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B3933821 : Blo 1379509 3933821 := bstep (se 3 (by rfl) ⟨737591, by rfl⟩ : syracuseStep 3933821 = 1475183) B1475183
theorem B3106475 : Blo 1379509 3106475 := bstep (se 1 (by rfl) ⟨2329856, by rfl⟩ : syracuseStep 3106475 = 4659713) B4659713
theorem B15730361 : Blo 1379509 15730361 := bstep (se 2 (by rfl) ⟨5898885, by rfl⟩ : syracuseStep 15730361 = 11797771) B11797771
theorem B1746623 : Blo 1379509 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B44795591 : Blo 1379509 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B8972153 : Blo 1379509 8972153 := bstep (se 2 (by rfl) ⟨3364557, by rfl⟩ : syracuseStep 8972153 = 6729115) B6729115
theorem B3106727 : Blo 1379509 3106727 := bstep (se 1 (by rfl) ⟨2330045, by rfl⟩ : syracuseStep 3106727 = 4660091) B4660091
theorem B11962343 : Blo 1379509 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B3107015 : Blo 1379509 3107015 := bstep (se 1 (by rfl) ⟨2330261, by rfl⟩ : syracuseStep 3107015 = 4660523) B4660523
theorem B3107195 : Blo 1379509 3107195 := bstep (se 1 (by rfl) ⟨2330396, by rfl⟩ : syracuseStep 3107195 = 4660793) B4660793
theorem B5245307 : Blo 1379509 5245307 := bstep (se 1 (by rfl) ⟨3933980, by rfl⟩ : syracuseStep 5245307 = 7867961) B7867961
theorem B1747327 : Blo 1379509 1747327 := bstep (se 1 (by rfl) ⟨1310495, by rfl⟩ : syracuseStep 1747327 = 2620991) B2620991
theorem B4721033 : Blo 1379509 4721033 := bstep (se 2 (by rfl) ⟨1770387, by rfl⟩ : syracuseStep 4721033 = 3540775) B3540775
theorem B116451751 : Blo 1379509 116451751 := bstep (se 1 (by rfl) ⟨87338813, by rfl⟩ : syracuseStep 116451751 = 174677627) B174677627
theorem B3107303 : Blo 1379509 3107303 := bstep (se 1 (by rfl) ⟨2330477, by rfl⟩ : syracuseStep 3107303 = 4660955) B4660955
theorem B3107465 : Blo 1379509 3107465 := bstep (se 2 (by rfl) ⟨1165299, by rfl⟩ : syracuseStep 3107465 = 2330599) B2330599
theorem B3107483 : Blo 1379509 3107483 := bstep (se 1 (by rfl) ⟨2330612, by rfl⟩ : syracuseStep 3107483 = 4661225) B4661225
theorem B25176865 : Blo 1379509 25176865 := bstep (se 2 (by rfl) ⟨9441324, by rfl⟩ : syracuseStep 25176865 = 18882649) B18882649
theorem B2329391 : Blo 1379509 2329391 := bstep (se 1 (by rfl) ⟨1747043, by rfl⟩ : syracuseStep 2329391 = 3494087) B3494087
theorem B39791645 : Blo 1379509 39791645 := bstep (se 3 (by rfl) ⟨7460933, by rfl⟩ : syracuseStep 39791645 = 14921867) B14921867
theorem B15731819 : Blo 1379509 15731819 := bstep (se 1 (by rfl) ⟨11798864, by rfl⟩ : syracuseStep 15731819 = 23597729) B23597729
theorem B1379559 : Blo 1379509 1379559 := bstep (se 1 (by rfl) ⟨1034669, by rfl⟩ : syracuseStep 1379559 = 2069339) B2069339
theorem B3493327 : Blo 1379509 3493327 := bstep (se 1 (by rfl) ⟨2619995, by rfl⟩ : syracuseStep 3493327 = 5239991) B5239991
theorem B7859713 : Blo 1379509 7859713 := bstep (se 2 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 7859713 = 5894785) B5894785
theorem B1379867 : Blo 1379509 1379867 := bstep (se 1 (by rfl) ⟨1034900, by rfl⟩ : syracuseStep 1379867 = 2069801) B2069801
theorem B8850971 : Blo 1379509 8850971 := bstep (se 1 (by rfl) ⟨6638228, by rfl⟩ : syracuseStep 8850971 = 13276457) B13276457
theorem B67153475 : Blo 1379509 67153475 := bstep (se 1 (by rfl) ⟨50365106, by rfl⟩ : syracuseStep 67153475 = 100730213) B100730213
theorem B1379999 : Blo 1379509 1379999 := bstep (se 1 (by rfl) ⟨1034999, by rfl⟩ : syracuseStep 1379999 = 2069999) B2069999
theorem B1552063 : Blo 1379509 1552063 := bstep (se 1 (by rfl) ⟨1164047, by rfl⟩ : syracuseStep 1552063 = 2328095) B2328095
theorem B2330363 : Blo 1379509 2330363 := bstep (se 1 (by rfl) ⟨1747772, by rfl⟩ : syracuseStep 2330363 = 3495545) B3495545
theorem B9949067 : Blo 1379509 9949067 := bstep (se 1 (by rfl) ⟨7461800, by rfl⟩ : syracuseStep 9949067 = 14923601) B14923601
theorem B14929829 : Blo 1379509 14929829 := bstep (se 4 (by rfl) ⟨1399671, by rfl⟩ : syracuseStep 14929829 = 2799343) B2799343
theorem B1380263 : Blo 1379509 1380263 := bstep (se 1 (by rfl) ⟨1035197, by rfl⟩ : syracuseStep 1380263 = 2070395) B2070395
theorem B1380287 : Blo 1379509 1380287 := bstep (se 1 (by rfl) ⟨1035215, by rfl⟩ : syracuseStep 1380287 = 2070431) B2070431
theorem B1380443 : Blo 1379509 1380443 := bstep (se 1 (by rfl) ⟨1035332, by rfl⟩ : syracuseStep 1380443 = 2070665) B2070665
theorem B1380543 : Blo 1379509 1380543 := bstep (se 1 (by rfl) ⟨1035407, by rfl⟩ : syracuseStep 1380543 = 2070815) B2070815
theorem B1552639 : Blo 1379509 1552639 := bstep (se 1 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 1552639 = 2328959) B2328959
theorem B4419859 : Blo 1379509 4419859 := bstep (se 1 (by rfl) ⟨3314894, by rfl⟩ : syracuseStep 4419859 = 6629789) B6629789
theorem B3494299 : Blo 1379509 3494299 := bstep (se 1 (by rfl) ⟨2620724, by rfl⟩ : syracuseStep 3494299 = 5241449) B5241449
theorem B1380911 : Blo 1379509 1380911 := bstep (se 1 (by rfl) ⟨1035683, by rfl⟩ : syracuseStep 1380911 = 2071367) B2071367
theorem B131052107 : Blo 1379509 131052107 := bstep (se 1 (by rfl) ⟨98289080, by rfl⟩ : syracuseStep 131052107 = 196578161) B196578161
theorem B13267961 : Blo 1379509 13267961 := bstep (se 2 (by rfl) ⟨4975485, by rfl⟩ : syracuseStep 13267961 = 9950971) B9950971
theorem B2069615 : Blo 1379509 2069615 := bstep (se 1 (by rfl) ⟨1552211, by rfl⟩ : syracuseStep 2069615 = 3104423) B3104423
theorem B1381487 : Blo 1379509 1381487 := bstep (se 1 (by rfl) ⟨1036115, by rfl⟩ : syracuseStep 1381487 = 2072231) B2072231
theorem B2069687 : Blo 1379509 2069687 := bstep (se 1 (by rfl) ⟨1552265, by rfl⟩ : syracuseStep 2069687 = 3104531) B3104531
theorem B6993215 : Blo 1379509 6993215 := bstep (se 1 (by rfl) ⟨5244911, by rfl⟩ : syracuseStep 6993215 = 10489823) B10489823
theorem B1553791 : Blo 1379509 1553791 := bstep (se 1 (by rfl) ⟨1165343, by rfl⟩ : syracuseStep 1553791 = 2330687) B2330687
theorem B6985115 : Blo 1379509 6985115 := bstep (se 1 (by rfl) ⟨5238836, by rfl⟩ : syracuseStep 6985115 = 10477673) B10477673
theorem B2069927 : Blo 1379509 2069927 := bstep (se 1 (by rfl) ⟨1552445, by rfl⟩ : syracuseStep 2069927 = 3104891) B3104891
theorem B2070107 : Blo 1379509 2070107 := bstep (se 1 (by rfl) ⟨1552580, by rfl⟩ : syracuseStep 2070107 = 3105161) B3105161
theorem B2619047 : Blo 1379509 2619047 := bstep (se 1 (by rfl) ⟨1964285, by rfl⟩ : syracuseStep 2619047 = 3928571) B3928571
theorem B11196143 : Blo 1379509 11196143 := bstep (se 1 (by rfl) ⟨8397107, by rfl⟩ : syracuseStep 11196143 = 16794215) B16794215
theorem B7862447 : Blo 1379509 7862447 := bstep (se 1 (by rfl) ⟨5896835, by rfl⟩ : syracuseStep 7862447 = 11793671) B11793671
theorem B28350749 : Blo 1379509 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B3496223 : Blo 1379509 3496223 := bstep (se 1 (by rfl) ⟨2622167, by rfl⟩ : syracuseStep 3496223 = 5244335) B5244335
theorem B15718697 : Blo 1379509 15718697 := bstep (se 2 (by rfl) ⟨5894511, by rfl⟩ : syracuseStep 15718697 = 11789023) B11789023
theorem B5241145 : Blo 1379509 5241145 := bstep (se 2 (by rfl) ⟨1965429, by rfl⟩ : syracuseStep 5241145 = 3930859) B3930859
theorem B2070863 : Blo 1379509 2070863 := bstep (se 1 (by rfl) ⟨1553147, by rfl⟩ : syracuseStep 2070863 = 3106295) B3106295
theorem B2070887 : Blo 1379509 2070887 := bstep (se 1 (by rfl) ⟨1553165, by rfl⟩ : syracuseStep 2070887 = 3106331) B3106331
theorem B2070953 : Blo 1379509 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B15120985 : Blo 1379509 15120985 := bstep (se 2 (by rfl) ⟨5670369, by rfl⟩ : syracuseStep 15120985 = 11340739) B11340739
theorem B1838733965 : Blo 1379509 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B63765143 : Blo 1379509 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B2071337 : Blo 1379509 2071337 := bstep (se 2 (by rfl) ⟨776751, by rfl⟩ : syracuseStep 2071337 = 1553503) B1553503
theorem B35363789 : Blo 1379509 35363789 := bstep (se 3 (by rfl) ⟨6630710, by rfl⟩ : syracuseStep 35363789 = 13261421) B13261421
theorem B2071547 : Blo 1379509 2071547 := bstep (se 1 (by rfl) ⟨1553660, by rfl⟩ : syracuseStep 2071547 = 3107321) B3107321
theorem B28318733 : Blo 1379509 28318733 := bstep (se 3 (by rfl) ⟨5309762, by rfl⟩ : syracuseStep 28318733 = 10619525) B10619525
theorem B2071583 : Blo 1379509 2071583 := bstep (se 1 (by rfl) ⟨1553687, by rfl⟩ : syracuseStep 2071583 = 3107375) B3107375
theorem B2071607 : Blo 1379509 2071607 := bstep (se 1 (by rfl) ⟨1553705, by rfl⟩ : syracuseStep 2071607 = 3107411) B3107411
theorem B1965151 : Blo 1379509 1965151 := bstep (se 1 (by rfl) ⟨1473863, by rfl⟩ : syracuseStep 1965151 = 2947727) B2947727
theorem B2071727 : Blo 1379509 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B3103955 : Blo 1379509 3103955 := bstep (se 1 (by rfl) ⟨2327966, by rfl⟩ : syracuseStep 3103955 = 4655933) B4655933
theorem B3931361 : Blo 1379509 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B3104027 : Blo 1379509 3104027 := bstep (se 1 (by rfl) ⟨2328020, by rfl⟩ : syracuseStep 3104027 = 4656041) B4656041
theorem B2071871 : Blo 1379509 2071871 := bstep (se 1 (by rfl) ⟨1553903, by rfl⟩ : syracuseStep 2071871 = 3107807) B3107807
theorem B15736193 : Blo 1379509 15736193 := bstep (se 2 (by rfl) ⟨5901072, by rfl⟩ : syracuseStep 15736193 = 11802145) B11802145
theorem B2072015 : Blo 1379509 2072015 := bstep (se 1 (by rfl) ⟨1554011, by rfl⟩ : syracuseStep 2072015 = 3108023) B3108023
theorem B3104225 : Blo 1379509 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B35872465 : Blo 1379509 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B7864087 : Blo 1379509 7864087 := bstep (se 1 (by rfl) ⟨5898065, by rfl⟩ : syracuseStep 7864087 = 11796131) B11796131
theorem B23584607 : Blo 1379509 23584607 := bstep (se 1 (by rfl) ⟨17688455, by rfl⟩ : syracuseStep 23584607 = 35376911) B35376911
theorem B87368071 : Blo 1379509 87368071 := bstep (se 1 (by rfl) ⟨65526053, by rfl⟩ : syracuseStep 87368071 = 131052107) B131052107
theorem B6988193 : Blo 1379509 6988193 := bstep (se 2 (by rfl) ⟨2620572, by rfl⟩ : syracuseStep 6988193 = 5241145) B5241145
theorem B20161313 : Blo 1379509 20161313 := bstep (se 2 (by rfl) ⟨7560492, by rfl⟩ : syracuseStep 20161313 = 15120985) B15120985
theorem B4662143 : Blo 1379509 4662143 := bstep (se 1 (by rfl) ⟨3496607, by rfl⟩ : syracuseStep 4662143 = 6993215) B6993215
theorem B2622547 : Blo 1379509 2622547 := bstep (se 1 (by rfl) ⟨1966910, by rfl⟩ : syracuseStep 2622547 = 3933821) B3933821
theorem B1746031 : Blo 1379509 1746031 := bstep (se 1 (by rfl) ⟨1309523, by rfl⟩ : syracuseStep 1746031 = 2619047) B2619047
theorem B10486907 : Blo 1379509 10486907 := bstep (se 1 (by rfl) ⟨7865180, by rfl⟩ : syracuseStep 10486907 = 15730361) B15730361
theorem B7464095 : Blo 1379509 7464095 := bstep (se 1 (by rfl) ⟨5598071, by rfl⟩ : syracuseStep 7464095 = 11196143) B11196143
theorem B5981435 : Blo 1379509 5981435 := bstep (se 1 (by rfl) ⟨4486076, by rfl⟩ : syracuseStep 5981435 = 8972153) B8972153
theorem B18900499 : Blo 1379509 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B10479131 : Blo 1379509 10479131 := bstep (se 1 (by rfl) ⟨7859348, by rfl⟩ : syracuseStep 10479131 = 15718697) B15718697
theorem B3147355 : Blo 1379509 3147355 := bstep (se 1 (by rfl) ⟨2360516, by rfl⟩ : syracuseStep 3147355 = 4721033) B4721033
theorem B42510095 : Blo 1379509 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B4720609 : Blo 1379509 4720609 := bstep (se 2 (by rfl) ⟨1770228, by rfl⟩ : syracuseStep 4720609 = 3540457) B3540457
theorem B10479617 : Blo 1379509 10479617 := bstep (se 2 (by rfl) ⟨3929856, by rfl⟩ : syracuseStep 10479617 = 7859713) B7859713
theorem B26527763 : Blo 1379509 26527763 := bstep (se 1 (by rfl) ⟨19895822, by rfl⟩ : syracuseStep 26527763 = 39791645) B39791645
theorem B10487879 : Blo 1379509 10487879 := bstep (se 1 (by rfl) ⟨7865909, by rfl⟩ : syracuseStep 10487879 = 15731819) B15731819
theorem B5900647 : Blo 1379509 5900647 := bstep (se 1 (by rfl) ⟨4425485, by rfl⟩ : syracuseStep 5900647 = 8850971) B8850971
theorem B15723071 : Blo 1379509 15723071 := bstep (se 1 (by rfl) ⟨11792303, by rfl⟩ : syracuseStep 15723071 = 23584607) B23584607
theorem B5893145 : Blo 1379509 5893145 := bstep (se 2 (by rfl) ⟨2209929, by rfl⟩ : syracuseStep 5893145 = 4419859) B4419859
theorem B23571485 : Blo 1379509 23571485 := bstep (se 3 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 23571485 = 8839307) B8839307
theorem B3107951 : Blo 1379509 3107951 := bstep (se 1 (by rfl) ⟨2330963, by rfl⟩ : syracuseStep 3107951 = 4661927) B4661927
theorem B2329769 : Blo 1379509 2329769 := bstep (se 2 (by rfl) ⟨873663, by rfl⟩ : syracuseStep 2329769 = 1747327) B1747327
theorem B6630635 : Blo 1379509 6630635 := bstep (se 1 (by rfl) ⟨4972976, by rfl⟩ : syracuseStep 6630635 = 9945953) B9945953
theorem B1379743 : Blo 1379509 1379743 := bstep (se 1 (by rfl) ⟨1034807, by rfl⟩ : syracuseStep 1379743 = 2069615) B2069615
theorem B1379791 : Blo 1379509 1379791 := bstep (se 1 (by rfl) ⟨1034843, by rfl⟩ : syracuseStep 1379791 = 2069687) B2069687
theorem B4656743 : Blo 1379509 4656743 := bstep (se 1 (by rfl) ⟨3492557, by rfl⟩ : syracuseStep 4656743 = 6985115) B6985115
theorem B1379951 : Blo 1379509 1379951 := bstep (se 1 (by rfl) ⟨1034963, by rfl⟩ : syracuseStep 1379951 = 2069927) B2069927
theorem B1380071 : Blo 1379509 1380071 := bstep (se 1 (by rfl) ⟨1035053, by rfl⟩ : syracuseStep 1380071 = 2070107) B2070107
theorem B29863727 : Blo 1379509 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B2330815 : Blo 1379509 2330815 := bstep (se 1 (by rfl) ⟨1748111, by rfl⟩ : syracuseStep 2330815 = 3496223) B3496223
theorem B1380575 : Blo 1379509 1380575 := bstep (se 1 (by rfl) ⟨1035431, by rfl⟩ : syracuseStep 1380575 = 2070863) B2070863
theorem B1380591 : Blo 1379509 1380591 := bstep (se 1 (by rfl) ⟨1035443, by rfl⟩ : syracuseStep 1380591 = 2070887) B2070887
theorem B1380635 : Blo 1379509 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B1225822643 : Blo 1379509 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B4657661 : Blo 1379509 4657661 := bstep (se 3 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 4657661 = 1746623) B1746623
theorem B1380891 : Blo 1379509 1380891 := bstep (se 1 (by rfl) ⟨1035668, by rfl⟩ : syracuseStep 1380891 = 2071337) B2071337
theorem B1552927 : Blo 1379509 1552927 := bstep (se 1 (by rfl) ⟨1164695, by rfl⟩ : syracuseStep 1552927 = 2329391) B2329391
theorem B4657769 : Blo 1379509 4657769 := bstep (se 2 (by rfl) ⟨1746663, by rfl⟩ : syracuseStep 4657769 = 3493327) B3493327
theorem B1381031 : Blo 1379509 1381031 := bstep (se 1 (by rfl) ⟨1035773, by rfl⟩ : syracuseStep 1381031 = 2071547) B2071547
theorem B18879155 : Blo 1379509 18879155 := bstep (se 1 (by rfl) ⟨14159366, by rfl⟩ : syracuseStep 18879155 = 28318733) B28318733
theorem B1381055 : Blo 1379509 1381055 := bstep (se 1 (by rfl) ⟨1035791, by rfl⟩ : syracuseStep 1381055 = 2071583) B2071583
theorem B1381071 : Blo 1379509 1381071 := bstep (se 1 (by rfl) ⟨1035803, by rfl⟩ : syracuseStep 1381071 = 2071607) B2071607
theorem B1381151 : Blo 1379509 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B2069303 : Blo 1379509 2069303 := bstep (se 1 (by rfl) ⟨1551977, by rfl⟩ : syracuseStep 2069303 = 3103955) B3103955
theorem B2069351 : Blo 1379509 2069351 := bstep (se 1 (by rfl) ⟨1552013, by rfl⟩ : syracuseStep 2069351 = 3104027) B3104027
theorem B1381247 : Blo 1379509 1381247 := bstep (se 1 (by rfl) ⟨1035935, by rfl⟩ : syracuseStep 1381247 = 2071871) B2071871
theorem B2069417 : Blo 1379509 2069417 := bstep (se 2 (by rfl) ⟨776031, by rfl⟩ : syracuseStep 2069417 = 1552063) B1552063
theorem B10490795 : Blo 1379509 10490795 := bstep (se 1 (by rfl) ⟨7868096, by rfl⟩ : syracuseStep 10490795 = 15736193) B15736193
theorem B47829953 : Blo 1379509 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B1381343 : Blo 1379509 1381343 := bstep (se 1 (by rfl) ⟨1036007, by rfl⟩ : syracuseStep 1381343 = 2072015) B2072015
theorem B2069483 : Blo 1379509 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B1553575 : Blo 1379509 1553575 := bstep (se 1 (by rfl) ⟨1165181, by rfl⟩ : syracuseStep 1553575 = 2330363) B2330363
theorem B6632711 : Blo 1379509 6632711 := bstep (se 1 (by rfl) ⟨4974533, by rfl⟩ : syracuseStep 6632711 = 9949067) B9949067
theorem B2070011 : Blo 1379509 2070011 := bstep (se 1 (by rfl) ⟨1552508, by rfl⟩ : syracuseStep 2070011 = 3105017) B3105017
theorem B2070185 : Blo 1379509 2070185 := bstep (se 2 (by rfl) ⟨776319, by rfl⟩ : syracuseStep 2070185 = 1552639) B1552639
theorem B2070191 : Blo 1379509 2070191 := bstep (se 1 (by rfl) ⟨1552643, by rfl⟩ : syracuseStep 2070191 = 3105287) B3105287
theorem B2070311 : Blo 1379509 2070311 := bstep (se 1 (by rfl) ⟨1552733, by rfl⟩ : syracuseStep 2070311 = 3105467) B3105467
theorem B4659065 : Blo 1379509 4659065 := bstep (se 2 (by rfl) ⟨1747149, by rfl⟩ : syracuseStep 4659065 = 3494299) B3494299
theorem B155269001 : Blo 1379509 155269001 := bstep (se 2 (by rfl) ⟨58225875, by rfl⟩ : syracuseStep 155269001 = 116451751) B116451751
theorem B8845307 : Blo 1379509 8845307 := bstep (se 1 (by rfl) ⟨6633980, by rfl⟩ : syracuseStep 8845307 = 13267961) B13267961
theorem B2070635 : Blo 1379509 2070635 := bstep (se 1 (by rfl) ⟨1552976, by rfl⟩ : syracuseStep 2070635 = 3105953) B3105953
theorem B10475729 : Blo 1379509 10475729 := bstep (se 2 (by rfl) ⟨3928398, by rfl⟩ : syracuseStep 10475729 = 7856797) B7856797
theorem B2070911 : Blo 1379509 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B33569153 : Blo 1379509 33569153 := bstep (se 2 (by rfl) ⟨12588432, by rfl⟩ : syracuseStep 33569153 = 25176865) B25176865
theorem B2070983 : Blo 1379509 2070983 := bstep (se 1 (by rfl) ⟨1553237, by rfl⟩ : syracuseStep 2070983 = 3106475) B3106475
theorem B2071151 : Blo 1379509 2071151 := bstep (se 1 (by rfl) ⟨1553363, by rfl⟩ : syracuseStep 2071151 = 3106727) B3106727
theorem B5241631 : Blo 1379509 5241631 := bstep (se 1 (by rfl) ⟨3931223, by rfl⟩ : syracuseStep 5241631 = 7862447) B7862447
theorem B2620201 : Blo 1379509 2620201 := bstep (se 2 (by rfl) ⟨982575, by rfl⟩ : syracuseStep 2620201 = 1965151) B1965151
theorem B2071343 : Blo 1379509 2071343 := bstep (se 1 (by rfl) ⟨1553507, by rfl⟩ : syracuseStep 2071343 = 3107015) B3107015
theorem B2071463 : Blo 1379509 2071463 := bstep (se 1 (by rfl) ⟨1553597, by rfl⟩ : syracuseStep 2071463 = 3107195) B3107195
theorem B3496871 : Blo 1379509 3496871 := bstep (se 1 (by rfl) ⟨2622653, by rfl⟩ : syracuseStep 3496871 = 5245307) B5245307
theorem B2071535 : Blo 1379509 2071535 := bstep (se 1 (by rfl) ⟨1553651, by rfl⟩ : syracuseStep 2071535 = 3107303) B3107303
theorem B2071643 : Blo 1379509 2071643 := bstep (se 1 (by rfl) ⟨1553732, by rfl⟩ : syracuseStep 2071643 = 3107465) B3107465
theorem B2071655 : Blo 1379509 2071655 := bstep (se 1 (by rfl) ⟨1553741, by rfl⟩ : syracuseStep 2071655 = 3107483) B3107483
theorem B2071721 : Blo 1379509 2071721 := bstep (se 2 (by rfl) ⟨776895, by rfl⟩ : syracuseStep 2071721 = 1553791) B1553791
theorem B23575859 : Blo 1379509 23575859 := bstep (se 1 (by rfl) ⟨17681894, by rfl⟩ : syracuseStep 23575859 = 35363789) B35363789
theorem B2620907 : Blo 1379509 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B10485449 : Blo 1379509 10485449 := bstep (se 2 (by rfl) ⟨3932043, by rfl⟩ : syracuseStep 10485449 = 7864087) B7864087
theorem B44768983 : Blo 1379509 44768983 := bstep (se 1 (by rfl) ⟨33576737, by rfl⟩ : syracuseStep 44768983 = 67153475) B67153475
theorem B31899581 : Blo 1379509 31899581 := bstep (se 3 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 31899581 = 11962343) B11962343
theorem B9953219 : Blo 1379509 9953219 := bstep (se 1 (by rfl) ⟨7464914, by rfl⟩ : syracuseStep 9953219 = 14929829) B14929829
theorem B3105107 : Blo 1379509 3105107 := bstep (se 1 (by rfl) ⟨2328830, by rfl⟩ : syracuseStep 3105107 = 4657661) B4657661
theorem B3105179 : Blo 1379509 3105179 := bstep (se 1 (by rfl) ⟨2328884, by rfl⟩ : syracuseStep 3105179 = 4657769) B4657769
theorem B16785893 : Blo 1379509 16785893 := bstep (se 4 (by rfl) ⟨1573677, by rfl⟩ : syracuseStep 16785893 = 3147355) B3147355
theorem B116490761 : Blo 1379509 116490761 := bstep (se 2 (by rfl) ⟨43684035, by rfl⟩ : syracuseStep 116490761 = 87368071) B87368071
theorem B6988841 : Blo 1379509 6988841 := bstep (se 2 (by rfl) ⟨2620815, by rfl⟩ : syracuseStep 6988841 = 5241631) B5241631
theorem B3106043 : Blo 1379509 3106043 := bstep (se 1 (by rfl) ⟨2329532, by rfl⟩ : syracuseStep 3106043 = 4659065) B4659065
theorem B2328041 : Blo 1379509 2328041 := bstep (se 2 (by rfl) ⟨873015, by rfl⟩ : syracuseStep 2328041 = 1746031) B1746031
theorem B15714323 : Blo 1379509 15714323 := bstep (se 1 (by rfl) ⟨11785742, by rfl⟩ : syracuseStep 15714323 = 23571485) B23571485
theorem B25200665 : Blo 1379509 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B1747271 : Blo 1379509 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B6990299 : Blo 1379509 6990299 := bstep (se 1 (by rfl) ⟨5242724, by rfl⟩ : syracuseStep 6990299 = 10485449) B10485449
theorem B19909151 : Blo 1379509 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B6294145 : Blo 1379509 6294145 := bstep (se 2 (by rfl) ⟨2360304, by rfl⟩ : syracuseStep 6294145 = 4720609) B4720609
theorem B3107753 : Blo 1379509 3107753 := bstep (se 2 (by rfl) ⟨1165407, by rfl⟩ : syracuseStep 3107753 = 2330815) B2330815
theorem B12586103 : Blo 1379509 12586103 := bstep (se 1 (by rfl) ⟨9439577, by rfl⟩ : syracuseStep 12586103 = 18879155) B18879155
theorem B7867529 : Blo 1379509 7867529 := bstep (se 2 (by rfl) ⟨2950323, by rfl⟩ : syracuseStep 7867529 = 5900647) B5900647
theorem B1379535 : Blo 1379509 1379535 := bstep (se 1 (by rfl) ⟨1034651, by rfl⟩ : syracuseStep 1379535 = 2069303) B2069303
theorem B1379567 : Blo 1379509 1379567 := bstep (se 1 (by rfl) ⟨1034675, by rfl⟩ : syracuseStep 1379567 = 2069351) B2069351
theorem B3108095 : Blo 1379509 3108095 := bstep (se 1 (by rfl) ⟨2331071, by rfl⟩ : syracuseStep 3108095 = 4662143) B4662143
theorem B1379611 : Blo 1379509 1379611 := bstep (se 1 (by rfl) ⟨1034708, by rfl⟩ : syracuseStep 1379611 = 2069417) B2069417
theorem B31886635 : Blo 1379509 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B1379655 : Blo 1379509 1379655 := bstep (se 1 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 1379655 = 2069483) B2069483
theorem B6991271 : Blo 1379509 6991271 := bstep (se 1 (by rfl) ⟨5243453, by rfl⟩ : syracuseStep 6991271 = 10486907) B10486907
theorem B4976063 : Blo 1379509 4976063 := bstep (se 1 (by rfl) ⟨3732047, by rfl⟩ : syracuseStep 4976063 = 7464095) B7464095
theorem B1380007 : Blo 1379509 1380007 := bstep (se 1 (by rfl) ⟨1035005, by rfl⟩ : syracuseStep 1380007 = 2070011) B2070011
theorem B3493601 : Blo 1379509 3493601 := bstep (se 2 (by rfl) ⟨1310100, by rfl⟩ : syracuseStep 3493601 = 2620201) B2620201
theorem B1380123 : Blo 1379509 1380123 := bstep (se 1 (by rfl) ⟨1035092, by rfl⟩ : syracuseStep 1380123 = 2070185) B2070185
theorem B1380127 : Blo 1379509 1380127 := bstep (se 1 (by rfl) ⟨1035095, by rfl⟩ : syracuseStep 1380127 = 2070191) B2070191
theorem B28340063 : Blo 1379509 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B1380207 : Blo 1379509 1380207 := bstep (se 1 (by rfl) ⟨1035155, by rfl⟩ : syracuseStep 1380207 = 2070311) B2070311
theorem B6991919 : Blo 1379509 6991919 := bstep (se 1 (by rfl) ⟨5243939, by rfl⟩ : syracuseStep 6991919 = 10487879) B10487879
theorem B1380423 : Blo 1379509 1380423 := bstep (se 1 (by rfl) ⟨1035317, by rfl⟩ : syracuseStep 1380423 = 2070635) B2070635
theorem B6983819 : Blo 1379509 6983819 := bstep (se 1 (by rfl) ⟨5237864, by rfl⟩ : syracuseStep 6983819 = 10475729) B10475729
theorem B1380607 : Blo 1379509 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B1380655 : Blo 1379509 1380655 := bstep (se 1 (by rfl) ⟨1035491, by rfl⟩ : syracuseStep 1380655 = 2070983) B2070983
theorem B10482047 : Blo 1379509 10482047 := bstep (se 1 (by rfl) ⟨7861535, by rfl⟩ : syracuseStep 10482047 = 15723071) B15723071
theorem B1380767 : Blo 1379509 1380767 := bstep (se 1 (by rfl) ⟨1035575, by rfl⟩ : syracuseStep 1380767 = 2071151) B2071151
theorem B1380895 : Blo 1379509 1380895 := bstep (se 1 (by rfl) ⟨1035671, by rfl⟩ : syracuseStep 1380895 = 2071343) B2071343
theorem B1380975 : Blo 1379509 1380975 := bstep (se 1 (by rfl) ⟨1035731, by rfl⟩ : syracuseStep 1380975 = 2071463) B2071463
theorem B2331247 : Blo 1379509 2331247 := bstep (se 1 (by rfl) ⟨1748435, by rfl⟩ : syracuseStep 2331247 = 3496871) B3496871
theorem B1381023 : Blo 1379509 1381023 := bstep (se 1 (by rfl) ⟨1035767, by rfl⟩ : syracuseStep 1381023 = 2071535) B2071535
theorem B3928763 : Blo 1379509 3928763 := bstep (se 1 (by rfl) ⟨2946572, by rfl⟩ : syracuseStep 3928763 = 5893145) B5893145
theorem B1381095 : Blo 1379509 1381095 := bstep (se 1 (by rfl) ⟨1035821, by rfl⟩ : syracuseStep 1381095 = 2071643) B2071643
theorem B1381103 : Blo 1379509 1381103 := bstep (se 1 (by rfl) ⟨1035827, by rfl⟩ : syracuseStep 1381103 = 2071655) B2071655
theorem B1553179 : Blo 1379509 1553179 := bstep (se 1 (by rfl) ⟨1164884, by rfl⟩ : syracuseStep 1553179 = 2329769) B2329769
theorem B1381147 : Blo 1379509 1381147 := bstep (se 1 (by rfl) ⟨1035860, by rfl⟩ : syracuseStep 1381147 = 2071721) B2071721
theorem B4420423 : Blo 1379509 4420423 := bstep (se 1 (by rfl) ⟨3315317, by rfl⟩ : syracuseStep 4420423 = 6630635) B6630635
theorem B15717239 : Blo 1379509 15717239 := bstep (se 1 (by rfl) ⟨11787929, by rfl⟩ : syracuseStep 15717239 = 23575859) B23575859
theorem B59691977 : Blo 1379509 59691977 := bstep (se 2 (by rfl) ⟨22384491, by rfl⟩ : syracuseStep 59691977 = 44768983) B44768983
theorem B4658795 : Blo 1379509 4658795 := bstep (se 1 (by rfl) ⟨3494096, by rfl⟩ : syracuseStep 4658795 = 6988193) B6988193
theorem B817215095 : Blo 1379509 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B13440875 : Blo 1379509 13440875 := bstep (se 1 (by rfl) ⟨10080656, by rfl⟩ : syracuseStep 13440875 = 20161313) B20161313
theorem B6993863 : Blo 1379509 6993863 := bstep (se 1 (by rfl) ⟨5245397, by rfl⟩ : syracuseStep 6993863 = 10490795) B10490795
theorem B2070569 : Blo 1379509 2070569 := bstep (se 2 (by rfl) ⟨776463, by rfl⟩ : syracuseStep 2070569 = 1552927) B1552927
theorem B3987623 : Blo 1379509 3987623 := bstep (se 1 (by rfl) ⟨2990717, by rfl⟩ : syracuseStep 3987623 = 5981435) B5981435
theorem B4421807 : Blo 1379509 4421807 := bstep (se 1 (by rfl) ⟨3316355, by rfl⟩ : syracuseStep 4421807 = 6632711) B6632711
theorem B6986087 : Blo 1379509 6986087 := bstep (se 1 (by rfl) ⟨5239565, by rfl⟩ : syracuseStep 6986087 = 10479131) B10479131
theorem B103512667 : Blo 1379509 103512667 := bstep (se 1 (by rfl) ⟨77634500, by rfl⟩ : syracuseStep 103512667 = 155269001) B155269001
theorem B5896871 : Blo 1379509 5896871 := bstep (se 1 (by rfl) ⟨4422653, by rfl⟩ : syracuseStep 5896871 = 8845307) B8845307
theorem B6986411 : Blo 1379509 6986411 := bstep (se 1 (by rfl) ⟨5239808, by rfl⟩ : syracuseStep 6986411 = 10479617) B10479617
theorem B17685175 : Blo 1379509 17685175 := bstep (se 1 (by rfl) ⟨13263881, by rfl⟩ : syracuseStep 17685175 = 26527763) B26527763
theorem B3496729 : Blo 1379509 3496729 := bstep (se 2 (by rfl) ⟨1311273, by rfl⟩ : syracuseStep 3496729 = 2622547) B2622547
theorem B2071433 : Blo 1379509 2071433 := bstep (se 2 (by rfl) ⟨776787, by rfl⟩ : syracuseStep 2071433 = 1553575) B1553575
theorem B22379435 : Blo 1379509 22379435 := bstep (se 1 (by rfl) ⟨16784576, by rfl⟩ : syracuseStep 22379435 = 33569153) B33569153
theorem B2071967 : Blo 1379509 2071967 := bstep (se 1 (by rfl) ⟨1553975, by rfl⟩ : syracuseStep 2071967 = 3107951) B3107951
theorem B3104495 : Blo 1379509 3104495 := bstep (se 1 (by rfl) ⟨2328371, by rfl⟩ : syracuseStep 3104495 = 4656743) B4656743
theorem B21266387 : Blo 1379509 21266387 := bstep (se 1 (by rfl) ⟨15949790, by rfl⟩ : syracuseStep 21266387 = 31899581) B31899581
theorem B6635479 : Blo 1379509 6635479 := bstep (se 1 (by rfl) ⟨4976609, by rfl⟩ : syracuseStep 6635479 = 9953219) B9953219
theorem B4661279 : Blo 1379509 4661279 := bstep (se 1 (by rfl) ⟨3495959, by rfl⟩ : syracuseStep 4661279 = 6991919) B6991919
theorem B6988031 : Blo 1379509 6988031 := bstep (se 1 (by rfl) ⟨5241023, by rfl⟩ : syracuseStep 6988031 = 10482047) B10482047
theorem B11190595 : Blo 1379509 11190595 := bstep (se 1 (by rfl) ⟨8392946, by rfl⟩ : syracuseStep 11190595 = 16785893) B16785893
theorem B77660507 : Blo 1379509 77660507 := bstep (se 1 (by rfl) ⟨58245380, by rfl⟩ : syracuseStep 77660507 = 116490761) B116490761
theorem B10478159 : Blo 1379509 10478159 := bstep (se 1 (by rfl) ⟨7858619, by rfl⟩ : syracuseStep 10478159 = 15717239) B15717239
theorem B4662305 : Blo 1379509 4662305 := bstep (se 2 (by rfl) ⟨1748364, by rfl⟩ : syracuseStep 4662305 = 3496729) B3496729
theorem B3105863 : Blo 1379509 3105863 := bstep (se 1 (by rfl) ⟨2329397, by rfl⟩ : syracuseStep 3105863 = 4658795) B4658795
theorem B544810063 : Blo 1379509 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B4662575 : Blo 1379509 4662575 := bstep (se 1 (by rfl) ⟨3496931, by rfl⟩ : syracuseStep 4662575 = 6993863) B6993863
theorem B13272767 : Blo 1379509 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B14919623 : Blo 1379509 14919623 := bstep (se 1 (by rfl) ⟨11189717, by rfl⟩ : syracuseStep 14919623 = 22379435) B22379435
theorem B8390735 : Blo 1379509 8390735 := bstep (se 1 (by rfl) ⟨6293051, by rfl⟩ : syracuseStep 8390735 = 12586103) B12586103
theorem B5245019 : Blo 1379509 5245019 := bstep (se 1 (by rfl) ⟨3933764, by rfl⟩ : syracuseStep 5245019 = 7867529) B7867529
theorem B35842333 : Blo 1379509 35842333 := bstep (se 3 (by rfl) ⟨6720437, by rfl⟩ : syracuseStep 35842333 = 13440875) B13440875
theorem B2329067 : Blo 1379509 2329067 := bstep (se 1 (by rfl) ⟨1746800, by rfl⟩ : syracuseStep 2329067 = 3493601) B3493601
theorem B18893375 : Blo 1379509 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B4655879 : Blo 1379509 4655879 := bstep (se 1 (by rfl) ⟨3491909, by rfl⟩ : syracuseStep 4655879 = 6983819) B6983819
theorem B3108329 : Blo 1379509 3108329 := bstep (se 2 (by rfl) ⟨1165623, by rfl⟩ : syracuseStep 3108329 = 2331247) B2331247
theorem B8392193 : Blo 1379509 8392193 := bstep (se 2 (by rfl) ⟨3147072, by rfl⟩ : syracuseStep 8392193 = 6294145) B6294145
theorem B23580233 : Blo 1379509 23580233 := bstep (se 2 (by rfl) ⟨8842587, by rfl⟩ : syracuseStep 23580233 = 17685175) B17685175
theorem B1552027 : Blo 1379509 1552027 := bstep (se 1 (by rfl) ⟨1164020, by rfl⟩ : syracuseStep 1552027 = 2328041) B2328041
theorem B5893897 : Blo 1379509 5893897 := bstep (se 2 (by rfl) ⟨2210211, by rfl⟩ : syracuseStep 5893897 = 4420423) B4420423
theorem B1380379 : Blo 1379509 1380379 := bstep (se 1 (by rfl) ⟨1035284, by rfl⟩ : syracuseStep 1380379 = 2070569) B2070569
theorem B2658415 : Blo 1379509 2658415 := bstep (se 1 (by rfl) ⟨1993811, by rfl⟩ : syracuseStep 2658415 = 3987623) B3987623
theorem B4657391 : Blo 1379509 4657391 := bstep (se 1 (by rfl) ⟨3493043, by rfl⟩ : syracuseStep 4657391 = 6986087) B6986087
theorem B4657607 : Blo 1379509 4657607 := bstep (se 1 (by rfl) ⟨3493205, by rfl⟩ : syracuseStep 4657607 = 6986411) B6986411
theorem B1380955 : Blo 1379509 1380955 := bstep (se 1 (by rfl) ⟨1035716, by rfl⟩ : syracuseStep 1380955 = 2071433) B2071433
theorem B1381311 : Blo 1379509 1381311 := bstep (se 1 (by rfl) ⟨1035983, by rfl⟩ : syracuseStep 1381311 = 2071967) B2071967
theorem B2069663 : Blo 1379509 2069663 := bstep (se 1 (by rfl) ⟨1552247, by rfl⟩ : syracuseStep 2069663 = 3104495) B3104495
theorem B14177591 : Blo 1379509 14177591 := bstep (se 1 (by rfl) ⟨10633193, by rfl⟩ : syracuseStep 14177591 = 21266387) B21266387
theorem B2070071 : Blo 1379509 2070071 := bstep (se 1 (by rfl) ⟨1552553, by rfl⟩ : syracuseStep 2070071 = 3105107) B3105107
theorem B2070119 : Blo 1379509 2070119 := bstep (se 1 (by rfl) ⟨1552589, by rfl⟩ : syracuseStep 2070119 = 3105179) B3105179
theorem B39794651 : Blo 1379509 39794651 := bstep (se 1 (by rfl) ⟨29845988, by rfl⟩ : syracuseStep 39794651 = 59691977) B59691977
theorem B4659227 : Blo 1379509 4659227 := bstep (se 1 (by rfl) ⟨3494420, by rfl⟩ : syracuseStep 4659227 = 6988841) B6988841
theorem B138016889 : Blo 1379509 138016889 := bstep (se 2 (by rfl) ⟨51756333, by rfl⟩ : syracuseStep 138016889 = 103512667) B103512667
theorem B2070695 : Blo 1379509 2070695 := bstep (se 1 (by rfl) ⟨1553021, by rfl⟩ : syracuseStep 2070695 = 3106043) B3106043
theorem B4659389 : Blo 1379509 4659389 := bstep (se 3 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 4659389 = 1747271) B1747271
theorem B2070905 : Blo 1379509 2070905 := bstep (se 2 (by rfl) ⟨776589, by rfl⟩ : syracuseStep 2070905 = 1553179) B1553179
theorem B10476215 : Blo 1379509 10476215 := bstep (se 1 (by rfl) ⟨7857161, by rfl⟩ : syracuseStep 10476215 = 15714323) B15714323
theorem B16800443 : Blo 1379509 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B2947871 : Blo 1379509 2947871 := bstep (se 1 (by rfl) ⟨2210903, by rfl⟩ : syracuseStep 2947871 = 4421807) B4421807
theorem B4660199 : Blo 1379509 4660199 := bstep (se 1 (by rfl) ⟨3495149, by rfl⟩ : syracuseStep 4660199 = 6990299) B6990299
theorem B42515513 : Blo 1379509 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B3931247 : Blo 1379509 3931247 := bstep (se 1 (by rfl) ⟨2948435, by rfl⟩ : syracuseStep 3931247 = 5896871) B5896871
theorem B10476701 : Blo 1379509 10476701 := bstep (se 3 (by rfl) ⟨1964381, by rfl⟩ : syracuseStep 10476701 = 3928763) B3928763
theorem B2071835 : Blo 1379509 2071835 := bstep (se 1 (by rfl) ⟨1553876, by rfl⟩ : syracuseStep 2071835 = 3107753) B3107753
theorem B2072063 : Blo 1379509 2072063 := bstep (se 1 (by rfl) ⟨1554047, by rfl⟩ : syracuseStep 2072063 = 3108095) B3108095
theorem B4660847 : Blo 1379509 4660847 := bstep (se 1 (by rfl) ⟨3495635, by rfl⟩ : syracuseStep 4660847 = 6991271) B6991271
theorem B3317375 : Blo 1379509 3317375 := bstep (se 1 (by rfl) ⟨2488031, by rfl⟩ : syracuseStep 3317375 = 4976063) B4976063
theorem B8847305 : Blo 1379509 8847305 := bstep (se 2 (by rfl) ⟨3317739, by rfl⟩ : syracuseStep 8847305 = 6635479) B6635479
theorem B3104927 : Blo 1379509 3104927 := bstep (se 1 (by rfl) ⟨2328695, by rfl⟩ : syracuseStep 3104927 = 4657391) B4657391
theorem B51773671 : Blo 1379509 51773671 := bstep (se 1 (by rfl) ⟨38830253, by rfl⟩ : syracuseStep 51773671 = 77660507) B77660507
theorem B3105071 : Blo 1379509 3105071 := bstep (se 1 (by rfl) ⟨2328803, by rfl⟩ : syracuseStep 3105071 = 4657607) B4657607
theorem B8848511 : Blo 1379509 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B9946415 : Blo 1379509 9946415 := bstep (se 1 (by rfl) ⟨7459811, by rfl⟩ : syracuseStep 9946415 = 14919623) B14919623
theorem B3106151 : Blo 1379509 3106151 := bstep (se 1 (by rfl) ⟨2329613, by rfl⟩ : syracuseStep 3106151 = 4659227) B4659227
theorem B3106259 : Blo 1379509 3106259 := bstep (se 1 (by rfl) ⟨2329694, by rfl⟩ : syracuseStep 3106259 = 4659389) B4659389
theorem B11200295 : Blo 1379509 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B3106799 : Blo 1379509 3106799 := bstep (se 1 (by rfl) ⟨2330099, by rfl⟩ : syracuseStep 3106799 = 4660199) B4660199
theorem B7858529 : Blo 1379509 7858529 := bstep (se 2 (by rfl) ⟨2946948, by rfl⟩ : syracuseStep 7858529 = 5893897) B5893897
theorem B3107231 : Blo 1379509 3107231 := bstep (se 1 (by rfl) ⟨2330423, by rfl⟩ : syracuseStep 3107231 = 4660847) B4660847
theorem B3107519 : Blo 1379509 3107519 := bstep (se 1 (by rfl) ⟨2330639, by rfl⟩ : syracuseStep 3107519 = 4661279) B4661279
theorem B14920793 : Blo 1379509 14920793 := bstep (se 2 (by rfl) ⟨5595297, by rfl⟩ : syracuseStep 14920793 = 11190595) B11190595
theorem B3108203 : Blo 1379509 3108203 := bstep (se 1 (by rfl) ⟨2331152, by rfl⟩ : syracuseStep 3108203 = 4662305) B4662305
theorem B1379775 : Blo 1379509 1379775 := bstep (se 1 (by rfl) ⟨1034831, by rfl⟩ : syracuseStep 1379775 = 2069663) B2069663
theorem B3108383 : Blo 1379509 3108383 := bstep (se 1 (by rfl) ⟨2331287, by rfl⟩ : syracuseStep 3108383 = 4662575) B4662575
theorem B1380047 : Blo 1379509 1380047 := bstep (se 1 (by rfl) ⟨1035035, by rfl⟩ : syracuseStep 1380047 = 2070071) B2070071
theorem B1380079 : Blo 1379509 1380079 := bstep (se 1 (by rfl) ⟨1035059, by rfl⟩ : syracuseStep 1380079 = 2070119) B2070119
theorem B26529767 : Blo 1379509 26529767 := bstep (se 1 (by rfl) ⟨19897325, by rfl⟩ : syracuseStep 26529767 = 39794651) B39794651
theorem B726413417 : Blo 1379509 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B1380463 : Blo 1379509 1380463 := bstep (se 1 (by rfl) ⟨1035347, by rfl⟩ : syracuseStep 1380463 = 2070695) B2070695
theorem B1380603 : Blo 1379509 1380603 := bstep (se 1 (by rfl) ⟨1035452, by rfl⟩ : syracuseStep 1380603 = 2070905) B2070905
theorem B1552711 : Blo 1379509 1552711 := bstep (se 1 (by rfl) ⟨1164533, by rfl⟩ : syracuseStep 1552711 = 2329067) B2329067
theorem B12595583 : Blo 1379509 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B6984143 : Blo 1379509 6984143 := bstep (se 1 (by rfl) ⟨5238107, by rfl⟩ : syracuseStep 6984143 = 10476215) B10476215
theorem B7860989 : Blo 1379509 7860989 := bstep (se 3 (by rfl) ⟨1473935, by rfl⟩ : syracuseStep 7860989 = 2947871) B2947871
theorem B6984467 : Blo 1379509 6984467 := bstep (se 1 (by rfl) ⟨5238350, by rfl⟩ : syracuseStep 6984467 = 10476701) B10476701
theorem B1381223 : Blo 1379509 1381223 := bstep (se 1 (by rfl) ⟨1035917, by rfl⟩ : syracuseStep 1381223 = 2071835) B2071835
theorem B2069369 : Blo 1379509 2069369 := bstep (se 2 (by rfl) ⟨776013, by rfl⟩ : syracuseStep 2069369 = 1552027) B1552027
theorem B1381375 : Blo 1379509 1381375 := bstep (se 1 (by rfl) ⟨1036031, by rfl⟩ : syracuseStep 1381375 = 2072063) B2072063
theorem B3544553 : Blo 1379509 3544553 := bstep (se 2 (by rfl) ⟨1329207, by rfl⟩ : syracuseStep 3544553 = 2658415) B2658415
theorem B4658687 : Blo 1379509 4658687 := bstep (se 1 (by rfl) ⟨3494015, by rfl⟩ : syracuseStep 4658687 = 6988031) B6988031
theorem B47789777 : Blo 1379509 47789777 := bstep (se 2 (by rfl) ⟨17921166, by rfl⟩ : syracuseStep 47789777 = 35842333) B35842333
theorem B6985439 : Blo 1379509 6985439 := bstep (se 1 (by rfl) ⟨5239079, by rfl⟩ : syracuseStep 6985439 = 10478159) B10478159
theorem B2070575 : Blo 1379509 2070575 := bstep (se 1 (by rfl) ⟨1552931, by rfl⟩ : syracuseStep 2070575 = 3105863) B3105863
theorem B9451727 : Blo 1379509 9451727 := bstep (se 1 (by rfl) ⟨7088795, by rfl⟩ : syracuseStep 9451727 = 14177591) B14177591
theorem B5593823 : Blo 1379509 5593823 := bstep (se 1 (by rfl) ⟨4195367, by rfl⟩ : syracuseStep 5593823 = 8390735) B8390735
theorem B3496679 : Blo 1379509 3496679 := bstep (se 1 (by rfl) ⟨2622509, by rfl⟩ : syracuseStep 3496679 = 5245019) B5245019
theorem B92011259 : Blo 1379509 92011259 := bstep (se 1 (by rfl) ⟨69008444, by rfl⟩ : syracuseStep 92011259 = 138016889) B138016889
theorem B8846333 : Blo 1379509 8846333 := bstep (se 3 (by rfl) ⟨1658687, by rfl⟩ : syracuseStep 8846333 = 3317375) B3317375
theorem B3103919 : Blo 1379509 3103919 := bstep (se 1 (by rfl) ⟨2327939, by rfl⟩ : syracuseStep 3103919 = 4655879) B4655879
theorem B28343675 : Blo 1379509 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B2620831 : Blo 1379509 2620831 := bstep (se 1 (by rfl) ⟨1965623, by rfl⟩ : syracuseStep 2620831 = 3931247) B3931247
theorem B2072219 : Blo 1379509 2072219 := bstep (se 1 (by rfl) ⟨1554164, by rfl⟩ : syracuseStep 2072219 = 3108329) B3108329
theorem B5594795 : Blo 1379509 5594795 := bstep (se 1 (by rfl) ⟨4196096, by rfl⟩ : syracuseStep 5594795 = 8392193) B8392193
theorem B15720155 : Blo 1379509 15720155 := bstep (se 1 (by rfl) ⟨11790116, by rfl⟩ : syracuseStep 15720155 = 23580233) B23580233
theorem B5898203 : Blo 1379509 5898203 := bstep (se 1 (by rfl) ⟨4423652, by rfl⟩ : syracuseStep 5898203 = 8847305) B8847305
theorem B8397055 : Blo 1379509 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B5899007 : Blo 1379509 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B3105791 : Blo 1379509 3105791 := bstep (se 1 (by rfl) ⟨2329343, by rfl⟩ : syracuseStep 3105791 = 4658687) B4658687
theorem B31859851 : Blo 1379509 31859851 := bstep (se 1 (by rfl) ⟨23894888, by rfl⟩ : syracuseStep 31859851 = 47789777) B47789777
theorem B6301151 : Blo 1379509 6301151 := bstep (se 1 (by rfl) ⟨4725863, by rfl⟩ : syracuseStep 6301151 = 9451727) B9451727
theorem B3729215 : Blo 1379509 3729215 := bstep (se 1 (by rfl) ⟨2796911, by rfl⟩ : syracuseStep 3729215 = 5593823) B5593823
theorem B9947195 : Blo 1379509 9947195 := bstep (se 1 (by rfl) ⟨7460396, by rfl⟩ : syracuseStep 9947195 = 14920793) B14920793
theorem B3729863 : Blo 1379509 3729863 := bstep (se 1 (by rfl) ⟨2797397, by rfl⟩ : syracuseStep 3729863 = 5594795) B5594795
theorem B10480103 : Blo 1379509 10480103 := bstep (se 1 (by rfl) ⟨7860077, by rfl⟩ : syracuseStep 10480103 = 15720155) B15720155
theorem B4656095 : Blo 1379509 4656095 := bstep (se 1 (by rfl) ⟨3492071, by rfl⟩ : syracuseStep 4656095 = 6984143) B6984143
theorem B4656311 : Blo 1379509 4656311 := bstep (se 1 (by rfl) ⟨3492233, by rfl⟩ : syracuseStep 4656311 = 6984467) B6984467
theorem B1379579 : Blo 1379509 1379579 := bstep (se 1 (by rfl) ⟨1034684, by rfl⟩ : syracuseStep 1379579 = 2069369) B2069369
theorem B6630943 : Blo 1379509 6630943 := bstep (se 1 (by rfl) ⟨4973207, by rfl⟩ : syracuseStep 6630943 = 9946415) B9946415
theorem B2363035 : Blo 1379509 2363035 := bstep (se 1 (by rfl) ⟨1772276, by rfl⟩ : syracuseStep 2363035 = 3544553) B3544553
theorem B4656959 : Blo 1379509 4656959 := bstep (se 1 (by rfl) ⟨3492719, by rfl⟩ : syracuseStep 4656959 = 6985439) B6985439
theorem B7466863 : Blo 1379509 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B1380383 : Blo 1379509 1380383 := bstep (se 1 (by rfl) ⟨1035287, by rfl⟩ : syracuseStep 1380383 = 2070575) B2070575
theorem B5239019 : Blo 1379509 5239019 := bstep (se 1 (by rfl) ⟨3929264, by rfl⟩ : syracuseStep 5239019 = 7858529) B7858529
theorem B2331119 : Blo 1379509 2331119 := bstep (se 1 (by rfl) ⟨1748339, by rfl⟩ : syracuseStep 2331119 = 3496679) B3496679
theorem B3494441 : Blo 1379509 3494441 := bstep (se 2 (by rfl) ⟨1310415, by rfl⟩ : syracuseStep 3494441 = 2620831) B2620831
theorem B245363357 : Blo 1379509 245363357 := bstep (se 3 (by rfl) ⟨46005629, by rfl⟩ : syracuseStep 245363357 = 92011259) B92011259
theorem B2069279 : Blo 1379509 2069279 := bstep (se 1 (by rfl) ⟨1551959, by rfl⟩ : syracuseStep 2069279 = 3103919) B3103919
theorem B18895783 : Blo 1379509 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B1381479 : Blo 1379509 1381479 := bstep (se 1 (by rfl) ⟨1036109, by rfl⟩ : syracuseStep 1381479 = 2072219) B2072219
theorem B484275611 : Blo 1379509 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B2069951 : Blo 1379509 2069951 := bstep (se 1 (by rfl) ⟨1552463, by rfl⟩ : syracuseStep 2069951 = 3104927) B3104927
theorem B2070047 : Blo 1379509 2070047 := bstep (se 1 (by rfl) ⟨1552535, by rfl⟩ : syracuseStep 2070047 = 3105071) B3105071
theorem B69031561 : Blo 1379509 69031561 := bstep (se 2 (by rfl) ⟨25886835, by rfl⟩ : syracuseStep 69031561 = 51773671) B51773671
theorem B2070281 : Blo 1379509 2070281 := bstep (se 2 (by rfl) ⟨776355, by rfl⟩ : syracuseStep 2070281 = 1552711) B1552711
theorem B5240659 : Blo 1379509 5240659 := bstep (se 1 (by rfl) ⟨3930494, by rfl⟩ : syracuseStep 5240659 = 7860989) B7860989
theorem B2070767 : Blo 1379509 2070767 := bstep (se 1 (by rfl) ⟨1553075, by rfl⟩ : syracuseStep 2070767 = 3106151) B3106151
theorem B2070839 : Blo 1379509 2070839 := bstep (se 1 (by rfl) ⟨1553129, by rfl⟩ : syracuseStep 2070839 = 3106259) B3106259
theorem B2071199 : Blo 1379509 2071199 := bstep (se 1 (by rfl) ⟨1553399, by rfl⟩ : syracuseStep 2071199 = 3106799) B3106799
theorem B2071487 : Blo 1379509 2071487 := bstep (se 1 (by rfl) ⟨1553615, by rfl⟩ : syracuseStep 2071487 = 3107231) B3107231
theorem B2071679 : Blo 1379509 2071679 := bstep (se 1 (by rfl) ⟨1553759, by rfl⟩ : syracuseStep 2071679 = 3107519) B3107519
theorem B5897555 : Blo 1379509 5897555 := bstep (se 1 (by rfl) ⟨4423166, by rfl⟩ : syracuseStep 5897555 = 8846333) B8846333
theorem B2072135 : Blo 1379509 2072135 := bstep (se 1 (by rfl) ⟨1554101, by rfl⟩ : syracuseStep 2072135 = 3108203) B3108203
theorem B2072255 : Blo 1379509 2072255 := bstep (se 1 (by rfl) ⟨1554191, by rfl⟩ : syracuseStep 2072255 = 3108383) B3108383
theorem B3932135 : Blo 1379509 3932135 := bstep (se 1 (by rfl) ⟨2949101, by rfl⟩ : syracuseStep 3932135 = 5898203) B5898203
theorem B17686511 : Blo 1379509 17686511 := bstep (se 1 (by rfl) ⟨13264883, by rfl⟩ : syracuseStep 17686511 = 26529767) B26529767
theorem B3932671 : Blo 1379509 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B8841257 : Blo 1379509 8841257 := bstep (se 2 (by rfl) ⟨3315471, by rfl⟩ : syracuseStep 8841257 = 6630943) B6630943
theorem B9955817 : Blo 1379509 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B11791007 : Blo 1379509 11791007 := bstep (se 1 (by rfl) ⟨8843255, by rfl⟩ : syracuseStep 11791007 = 17686511) B17686511
theorem B3492679 : Blo 1379509 3492679 := bstep (se 1 (by rfl) ⟨2619509, by rfl⟩ : syracuseStep 3492679 = 5239019) B5239019
theorem B2329627 : Blo 1379509 2329627 := bstep (se 1 (by rfl) ⟨1747220, by rfl⟩ : syracuseStep 2329627 = 3494441) B3494441
theorem B1379519 : Blo 1379509 1379519 := bstep (se 1 (by rfl) ⟨1034639, by rfl⟩ : syracuseStep 1379519 = 2069279) B2069279
theorem B1379967 : Blo 1379509 1379967 := bstep (se 1 (by rfl) ⟨1034975, by rfl⟩ : syracuseStep 1379967 = 2069951) B2069951
theorem B1380031 : Blo 1379509 1380031 := bstep (se 1 (by rfl) ⟨1035023, by rfl⟩ : syracuseStep 1380031 = 2070047) B2070047
theorem B1380187 : Blo 1379509 1380187 := bstep (se 1 (by rfl) ⟨1035140, by rfl⟩ : syracuseStep 1380187 = 2070281) B2070281
theorem B2486143 : Blo 1379509 2486143 := bstep (se 1 (by rfl) ⟨1864607, by rfl⟩ : syracuseStep 2486143 = 3729215) B3729215
theorem B25194377 : Blo 1379509 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B6631463 : Blo 1379509 6631463 := bstep (se 1 (by rfl) ⟨4973597, by rfl⟩ : syracuseStep 6631463 = 9947195) B9947195
theorem B1380511 : Blo 1379509 1380511 := bstep (se 1 (by rfl) ⟨1035383, by rfl⟩ : syracuseStep 1380511 = 2070767) B2070767
theorem B42479801 : Blo 1379509 42479801 := bstep (se 2 (by rfl) ⟨15929925, by rfl⟩ : syracuseStep 42479801 = 31859851) B31859851
theorem B1380559 : Blo 1379509 1380559 := bstep (se 1 (by rfl) ⟨1035419, by rfl⟩ : syracuseStep 1380559 = 2070839) B2070839
theorem B2486575 : Blo 1379509 2486575 := bstep (se 1 (by rfl) ⟨1864931, by rfl⟩ : syracuseStep 2486575 = 3729863) B3729863
theorem B1380799 : Blo 1379509 1380799 := bstep (se 1 (by rfl) ⟨1035599, by rfl⟩ : syracuseStep 1380799 = 2071199) B2071199
theorem B1380991 : Blo 1379509 1380991 := bstep (se 1 (by rfl) ⟨1035743, by rfl⟩ : syracuseStep 1380991 = 2071487) B2071487
theorem B1381119 : Blo 1379509 1381119 := bstep (se 1 (by rfl) ⟨1035839, by rfl⟩ : syracuseStep 1381119 = 2071679) B2071679
theorem B92042081 : Blo 1379509 92042081 := bstep (se 2 (by rfl) ⟨34515780, by rfl⟩ : syracuseStep 92042081 = 69031561) B69031561
theorem B3150713 : Blo 1379509 3150713 := bstep (se 2 (by rfl) ⟨1181517, by rfl⟩ : syracuseStep 3150713 = 2363035) B2363035
theorem B1381423 : Blo 1379509 1381423 := bstep (se 1 (by rfl) ⟨1036067, by rfl⟩ : syracuseStep 1381423 = 2072135) B2072135
theorem B1381503 : Blo 1379509 1381503 := bstep (se 1 (by rfl) ⟨1036127, by rfl⟩ : syracuseStep 1381503 = 2072255) B2072255
theorem B1554079 : Blo 1379509 1554079 := bstep (se 1 (by rfl) ⟨1165559, by rfl⟩ : syracuseStep 1554079 = 2331119) B2331119
theorem B11196073 : Blo 1379509 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B163575571 : Blo 1379509 163575571 := bstep (se 1 (by rfl) ⟨122681678, by rfl⟩ : syracuseStep 163575571 = 245363357) B245363357
theorem B2070527 : Blo 1379509 2070527 := bstep (se 1 (by rfl) ⟨1552895, by rfl⟩ : syracuseStep 2070527 = 3105791) B3105791
theorem B4200767 : Blo 1379509 4200767 := bstep (se 1 (by rfl) ⟨3150575, by rfl⟩ : syracuseStep 4200767 = 6301151) B6301151
theorem B1291401629 : Blo 1379509 1291401629 := bstep (se 3 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 1291401629 = 484275611) B484275611
theorem B6986735 : Blo 1379509 6986735 := bstep (se 1 (by rfl) ⟨5240051, by rfl⟩ : syracuseStep 6986735 = 10480103) B10480103
theorem B3104063 : Blo 1379509 3104063 := bstep (se 1 (by rfl) ⟨2328047, by rfl⟩ : syracuseStep 3104063 = 4656095) B4656095
theorem B3104207 : Blo 1379509 3104207 := bstep (se 1 (by rfl) ⟨2328155, by rfl⟩ : syracuseStep 3104207 = 4656311) B4656311
theorem B3931703 : Blo 1379509 3931703 := bstep (se 1 (by rfl) ⟨2948777, by rfl⟩ : syracuseStep 3931703 = 5897555) B5897555
theorem B6987545 : Blo 1379509 6987545 := bstep (se 2 (by rfl) ⟨2620329, by rfl⟩ : syracuseStep 6987545 = 5240659) B5240659
theorem B3104639 : Blo 1379509 3104639 := bstep (se 1 (by rfl) ⟨2328479, by rfl⟩ : syracuseStep 3104639 = 4656959) B4656959
theorem B2621423 : Blo 1379509 2621423 := bstep (se 1 (by rfl) ⟨1966067, by rfl⟩ : syracuseStep 2621423 = 3932135) B3932135
theorem B28319867 : Blo 1379509 28319867 := bstep (se 1 (by rfl) ⟨21239900, by rfl⟩ : syracuseStep 28319867 = 42479801) B42479801
theorem B5243561 : Blo 1379509 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B3106169 : Blo 1379509 3106169 := bstep (se 2 (by rfl) ⟨1164813, by rfl⟩ : syracuseStep 3106169 = 2329627) B2329627
theorem B6637211 : Blo 1379509 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B14928097 : Blo 1379509 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B16796251 : Blo 1379509 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B6990461 : Blo 1379509 6990461 := bstep (se 3 (by rfl) ⟨1310711, by rfl⟩ : syracuseStep 6990461 = 2621423) B2621423
theorem B61361387 : Blo 1379509 61361387 := bstep (se 1 (by rfl) ⟨46021040, by rfl⟩ : syracuseStep 61361387 = 92042081) B92042081
theorem B2100475 : Blo 1379509 2100475 := bstep (se 1 (by rfl) ⟨1575356, by rfl⟩ : syracuseStep 2100475 = 3150713) B3150713
theorem B4656905 : Blo 1379509 4656905 := bstep (se 2 (by rfl) ⟨1746339, by rfl⟩ : syracuseStep 4656905 = 3492679) B3492679
theorem B1380351 : Blo 1379509 1380351 := bstep (se 1 (by rfl) ⟨1035263, by rfl⟩ : syracuseStep 1380351 = 2070527) B2070527
theorem B5894171 : Blo 1379509 5894171 := bstep (se 1 (by rfl) ⟨4420628, by rfl⟩ : syracuseStep 5894171 = 8841257) B8841257
theorem B860934419 : Blo 1379509 860934419 := bstep (se 1 (by rfl) ⟨645700814, by rfl⟩ : syracuseStep 860934419 = 1291401629) B1291401629
theorem B7860671 : Blo 1379509 7860671 := bstep (se 1 (by rfl) ⟨5895503, by rfl⟩ : syracuseStep 7860671 = 11791007) B11791007
theorem B4657823 : Blo 1379509 4657823 := bstep (se 1 (by rfl) ⟨3493367, by rfl⟩ : syracuseStep 4657823 = 6986735) B6986735
theorem B2069375 : Blo 1379509 2069375 := bstep (se 1 (by rfl) ⟨1552031, by rfl⟩ : syracuseStep 2069375 = 3104063) B3104063
theorem B2069471 : Blo 1379509 2069471 := bstep (se 1 (by rfl) ⟨1552103, by rfl⟩ : syracuseStep 2069471 = 3104207) B3104207
theorem B218100761 : Blo 1379509 218100761 := bstep (se 2 (by rfl) ⟨81787785, by rfl⟩ : syracuseStep 218100761 = 163575571) B163575571
theorem B3314857 : Blo 1379509 3314857 := bstep (se 2 (by rfl) ⟨1243071, by rfl⟩ : syracuseStep 3314857 = 2486143) B2486143
theorem B4658363 : Blo 1379509 4658363 := bstep (se 1 (by rfl) ⟨3493772, by rfl⟩ : syracuseStep 4658363 = 6987545) B6987545
theorem B2069759 : Blo 1379509 2069759 := bstep (se 1 (by rfl) ⟨1552319, by rfl⟩ : syracuseStep 2069759 = 3104639) B3104639
theorem B4420975 : Blo 1379509 4420975 := bstep (se 1 (by rfl) ⟨3315731, by rfl⟩ : syracuseStep 4420975 = 6631463) B6631463
theorem B3315433 : Blo 1379509 3315433 := bstep (se 2 (by rfl) ⟨1243287, by rfl⟩ : syracuseStep 3315433 = 2486575) B2486575
theorem B2800511 : Blo 1379509 2800511 := bstep (se 1 (by rfl) ⟨2100383, by rfl⟩ : syracuseStep 2800511 = 4200767) B4200767
theorem B2072105 : Blo 1379509 2072105 := bstep (se 2 (by rfl) ⟨777039, by rfl⟩ : syracuseStep 2072105 = 1554079) B1554079
theorem B2621135 : Blo 1379509 2621135 := bstep (se 1 (by rfl) ⟨1965851, by rfl⟩ : syracuseStep 2621135 = 3931703) B3931703
theorem B573956279 : Blo 1379509 573956279 := bstep (se 1 (by rfl) ⟨430467209, by rfl⟩ : syracuseStep 573956279 = 860934419) B860934419
theorem B3105215 : Blo 1379509 3105215 := bstep (se 1 (by rfl) ⟨2328911, by rfl⟩ : syracuseStep 3105215 = 4657823) B4657823
theorem B145400507 : Blo 1379509 145400507 := bstep (se 1 (by rfl) ⟨109050380, by rfl⟩ : syracuseStep 145400507 = 218100761) B218100761
theorem B3105575 : Blo 1379509 3105575 := bstep (se 1 (by rfl) ⟨2329181, by rfl⟩ : syracuseStep 3105575 = 4658363) B4658363
theorem B4424807 : Blo 1379509 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B1747423 : Blo 1379509 1747423 := bstep (se 1 (by rfl) ⟨1310567, by rfl⟩ : syracuseStep 1747423 = 2621135) B2621135
theorem B1379583 : Blo 1379509 1379583 := bstep (se 1 (by rfl) ⟨1034687, by rfl⟩ : syracuseStep 1379583 = 2069375) B2069375
theorem B1379647 : Blo 1379509 1379647 := bstep (se 1 (by rfl) ⟨1034735, by rfl⟩ : syracuseStep 1379647 = 2069471) B2069471
theorem B1379839 : Blo 1379509 1379839 := bstep (se 1 (by rfl) ⟨1034879, by rfl⟩ : syracuseStep 1379839 = 2069759) B2069759
theorem B11202533 : Blo 1379509 11202533 := bstep (se 4 (by rfl) ⟨1050237, by rfl⟩ : syracuseStep 11202533 = 2100475) B2100475
theorem B4419809 : Blo 1379509 4419809 := bstep (se 2 (by rfl) ⟨1657428, by rfl⟩ : syracuseStep 4419809 = 3314857) B3314857
theorem B5894633 : Blo 1379509 5894633 := bstep (se 2 (by rfl) ⟨2210487, by rfl⟩ : syracuseStep 5894633 = 4420975) B4420975
theorem B40907591 : Blo 1379509 40907591 := bstep (se 1 (by rfl) ⟨30680693, by rfl⟩ : syracuseStep 40907591 = 61361387) B61361387
theorem B4420577 : Blo 1379509 4420577 := bstep (se 2 (by rfl) ⟨1657716, by rfl⟩ : syracuseStep 4420577 = 3315433) B3315433
theorem B1381403 : Blo 1379509 1381403 := bstep (se 1 (by rfl) ⟨1036052, by rfl⟩ : syracuseStep 1381403 = 2072105) B2072105
theorem B3929447 : Blo 1379509 3929447 := bstep (se 1 (by rfl) ⟨2947085, by rfl⟩ : syracuseStep 3929447 = 5894171) B5894171
theorem B18879911 : Blo 1379509 18879911 := bstep (se 1 (by rfl) ⟨14159933, by rfl⟩ : syracuseStep 18879911 = 28319867) B28319867
theorem B5240447 : Blo 1379509 5240447 := bstep (se 1 (by rfl) ⟨3930335, by rfl⟩ : syracuseStep 5240447 = 7860671) B7860671
theorem B19904129 : Blo 1379509 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B3495707 : Blo 1379509 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B22395001 : Blo 1379509 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B2070779 : Blo 1379509 2070779 := bstep (se 1 (by rfl) ⟨1553084, by rfl⟩ : syracuseStep 2070779 = 3106169) B3106169
theorem B4660307 : Blo 1379509 4660307 := bstep (se 1 (by rfl) ⟨3495230, by rfl⟩ : syracuseStep 4660307 = 6990461) B6990461
theorem B1867007 : Blo 1379509 1867007 := bstep (se 1 (by rfl) ⟨1400255, by rfl⟩ : syracuseStep 1867007 = 2800511) B2800511
theorem B3104603 : Blo 1379509 3104603 := bstep (se 1 (by rfl) ⟨2328452, by rfl⟩ : syracuseStep 3104603 = 4656905) B4656905
theorem B29860001 : Blo 1379509 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B27271727 : Blo 1379509 27271727 := bstep (se 1 (by rfl) ⟨20453795, by rfl⟩ : syracuseStep 27271727 = 40907591) B40907591
theorem B2949871 : Blo 1379509 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B3106871 : Blo 1379509 3106871 := bstep (se 1 (by rfl) ⟨2330153, by rfl⟩ : syracuseStep 3106871 = 4660307) B4660307
theorem B2329897 : Blo 1379509 2329897 := bstep (se 2 (by rfl) ⟨873711, by rfl⟩ : syracuseStep 2329897 = 1747423) B1747423
theorem B12586607 : Blo 1379509 12586607 := bstep (se 1 (by rfl) ⟨9439955, by rfl⟩ : syracuseStep 12586607 = 18879911) B18879911
theorem B3493631 : Blo 1379509 3493631 := bstep (se 1 (by rfl) ⟨2620223, by rfl⟩ : syracuseStep 3493631 = 5240447) B5240447
theorem B2330471 : Blo 1379509 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B1380519 : Blo 1379509 1380519 := bstep (se 1 (by rfl) ⟨1035389, by rfl⟩ : syracuseStep 1380519 = 2070779) B2070779
theorem B2069735 : Blo 1379509 2069735 := bstep (se 1 (by rfl) ⟨1552301, by rfl⟩ : syracuseStep 2069735 = 3104603) B3104603
theorem B7468355 : Blo 1379509 7468355 := bstep (se 1 (by rfl) ⟨5601266, by rfl⟩ : syracuseStep 7468355 = 11202533) B11202533
theorem B382637519 : Blo 1379509 382637519 := bstep (se 1 (by rfl) ⟨286978139, by rfl⟩ : syracuseStep 382637519 = 573956279) B573956279
theorem B2946539 : Blo 1379509 2946539 := bstep (se 1 (by rfl) ⟨2209904, by rfl⟩ : syracuseStep 2946539 = 4419809) B4419809
theorem B2070143 : Blo 1379509 2070143 := bstep (se 1 (by rfl) ⟨1552607, by rfl⟩ : syracuseStep 2070143 = 3105215) B3105215
theorem B3929755 : Blo 1379509 3929755 := bstep (se 1 (by rfl) ⟨2947316, by rfl⟩ : syracuseStep 3929755 = 5894633) B5894633
theorem B96933671 : Blo 1379509 96933671 := bstep (se 1 (by rfl) ⟨72700253, by rfl⟩ : syracuseStep 96933671 = 145400507) B145400507
theorem B2070383 : Blo 1379509 2070383 := bstep (se 1 (by rfl) ⟨1552787, by rfl⟩ : syracuseStep 2070383 = 3105575) B3105575
theorem B2947051 : Blo 1379509 2947051 := bstep (se 1 (by rfl) ⟨2210288, by rfl⟩ : syracuseStep 2947051 = 4420577) B4420577
theorem B4978685 : Blo 1379509 4978685 := bstep (se 3 (by rfl) ⟨933503, by rfl⟩ : syracuseStep 4978685 = 1867007) B1867007
theorem B2619631 : Blo 1379509 2619631 := bstep (se 1 (by rfl) ⟨1964723, by rfl⟩ : syracuseStep 2619631 = 3929447) B3929447
theorem B13269419 : Blo 1379509 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B19906667 : Blo 1379509 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B255091679 : Blo 1379509 255091679 := bstep (se 1 (by rfl) ⟨191318759, by rfl⟩ : syracuseStep 255091679 = 382637519) B382637519
theorem B3933161 : Blo 1379509 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B3106529 : Blo 1379509 3106529 := bstep (se 2 (by rfl) ⟨1164948, by rfl⟩ : syracuseStep 3106529 = 2329897) B2329897
theorem B8391071 : Blo 1379509 8391071 := bstep (se 1 (by rfl) ⟨6293303, by rfl⟩ : syracuseStep 8391071 = 12586607) B12586607
theorem B2329087 : Blo 1379509 2329087 := bstep (se 1 (by rfl) ⟨1746815, by rfl⟩ : syracuseStep 2329087 = 3493631) B3493631
theorem B3492841 : Blo 1379509 3492841 := bstep (se 2 (by rfl) ⟨1309815, by rfl⟩ : syracuseStep 3492841 = 2619631) B2619631
theorem B18181151 : Blo 1379509 18181151 := bstep (se 1 (by rfl) ⟨13635863, by rfl⟩ : syracuseStep 18181151 = 27271727) B27271727
theorem B1379823 : Blo 1379509 1379823 := bstep (se 1 (by rfl) ⟨1034867, by rfl⟩ : syracuseStep 1379823 = 2069735) B2069735
theorem B1380095 : Blo 1379509 1380095 := bstep (se 1 (by rfl) ⟨1035071, by rfl⟩ : syracuseStep 1380095 = 2070143) B2070143
theorem B64622447 : Blo 1379509 64622447 := bstep (se 1 (by rfl) ⟨48466835, by rfl⟩ : syracuseStep 64622447 = 96933671) B96933671
theorem B1380255 : Blo 1379509 1380255 := bstep (se 1 (by rfl) ⟨1035191, by rfl⟩ : syracuseStep 1380255 = 2070383) B2070383
theorem B5239673 : Blo 1379509 5239673 := bstep (se 2 (by rfl) ⟨1964877, by rfl⟩ : syracuseStep 5239673 = 3929755) B3929755
theorem B1553647 : Blo 1379509 1553647 := bstep (se 1 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 1553647 = 2330471) B2330471
theorem B3929401 : Blo 1379509 3929401 := bstep (se 2 (by rfl) ⟨1473525, by rfl⟩ : syracuseStep 3929401 = 2947051) B2947051
theorem B13276493 : Blo 1379509 13276493 := bstep (se 3 (by rfl) ⟨2489342, by rfl⟩ : syracuseStep 13276493 = 4978685) B4978685
theorem B4978903 : Blo 1379509 4978903 := bstep (se 1 (by rfl) ⟨3734177, by rfl⟩ : syracuseStep 4978903 = 7468355) B7468355
theorem B1964359 : Blo 1379509 1964359 := bstep (se 1 (by rfl) ⟨1473269, by rfl⟩ : syracuseStep 1964359 = 2946539) B2946539
theorem B2071247 : Blo 1379509 2071247 := bstep (se 1 (by rfl) ⟨1553435, by rfl⟩ : syracuseStep 2071247 = 3106871) B3106871
theorem B8846279 : Blo 1379509 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B13271111 : Blo 1379509 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B2622107 : Blo 1379509 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B3105449 : Blo 1379509 3105449 := bstep (se 2 (by rfl) ⟨1164543, by rfl⟩ : syracuseStep 3105449 = 2329087) B2329087
theorem B6638537 : Blo 1379509 6638537 := bstep (se 2 (by rfl) ⟨2489451, by rfl⟩ : syracuseStep 6638537 = 4978903) B4978903
theorem B3493115 : Blo 1379509 3493115 := bstep (se 1 (by rfl) ⟨2619836, by rfl⟩ : syracuseStep 3493115 = 5239673) B5239673
theorem B170061119 : Blo 1379509 170061119 := bstep (se 1 (by rfl) ⟨127545839, by rfl⟩ : syracuseStep 170061119 = 255091679) B255091679
theorem B8850995 : Blo 1379509 8850995 := bstep (se 1 (by rfl) ⟨6638246, by rfl⟩ : syracuseStep 8850995 = 13276493) B13276493
theorem B22376189 : Blo 1379509 22376189 := bstep (se 3 (by rfl) ⟨4195535, by rfl⟩ : syracuseStep 22376189 = 8391071) B8391071
theorem B4657121 : Blo 1379509 4657121 := bstep (se 2 (by rfl) ⟨1746420, by rfl⟩ : syracuseStep 4657121 = 3492841) B3492841
theorem B5239201 : Blo 1379509 5239201 := bstep (se 2 (by rfl) ⟨1964700, by rfl⟩ : syracuseStep 5239201 = 3929401) B3929401
theorem B1380831 : Blo 1379509 1380831 := bstep (se 1 (by rfl) ⟨1035623, by rfl⟩ : syracuseStep 1380831 = 2071247) B2071247
theorem B12120767 : Blo 1379509 12120767 := bstep (se 1 (by rfl) ⟨9090575, by rfl⟩ : syracuseStep 12120767 = 18181151) B18181151
theorem B2619145 : Blo 1379509 2619145 := bstep (se 2 (by rfl) ⟨982179, by rfl⟩ : syracuseStep 2619145 = 1964359) B1964359
theorem B2071019 : Blo 1379509 2071019 := bstep (se 1 (by rfl) ⟨1553264, by rfl⟩ : syracuseStep 2071019 = 3106529) B3106529
theorem B2071529 : Blo 1379509 2071529 := bstep (se 2 (by rfl) ⟨776823, by rfl⟩ : syracuseStep 2071529 = 1553647) B1553647
theorem B5897519 : Blo 1379509 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B43081631 : Blo 1379509 43081631 := bstep (se 1 (by rfl) ⟨32311223, by rfl⟩ : syracuseStep 43081631 = 64622447) B64622447
theorem B8847407 : Blo 1379509 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B4425691 : Blo 1379509 4425691 := bstep (se 1 (by rfl) ⟨3319268, by rfl⟩ : syracuseStep 4425691 = 6638537) B6638537
theorem B2328743 : Blo 1379509 2328743 := bstep (se 1 (by rfl) ⟨1746557, by rfl⟩ : syracuseStep 2328743 = 3493115) B3493115
theorem B3492193 : Blo 1379509 3492193 := bstep (se 2 (by rfl) ⟨1309572, by rfl⟩ : syracuseStep 3492193 = 2619145) B2619145
theorem B5900663 : Blo 1379509 5900663 := bstep (se 1 (by rfl) ⟨4425497, by rfl⟩ : syracuseStep 5900663 = 8850995) B8850995
theorem B1748071 : Blo 1379509 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B8080511 : Blo 1379509 8080511 := bstep (se 1 (by rfl) ⟨6060383, by rfl⟩ : syracuseStep 8080511 = 12120767) B12120767
theorem B1380679 : Blo 1379509 1380679 := bstep (se 1 (by rfl) ⟨1035509, by rfl⟩ : syracuseStep 1380679 = 2071019) B2071019
theorem B1381019 : Blo 1379509 1381019 := bstep (se 1 (by rfl) ⟨1035764, by rfl⟩ : syracuseStep 1381019 = 2071529) B2071529
theorem B113374079 : Blo 1379509 113374079 := bstep (se 1 (by rfl) ⟨85030559, by rfl⟩ : syracuseStep 113374079 = 170061119) B170061119
theorem B2070299 : Blo 1379509 2070299 := bstep (se 1 (by rfl) ⟨1552724, by rfl⟩ : syracuseStep 2070299 = 3105449) B3105449
theorem B6985601 : Blo 1379509 6985601 := bstep (se 2 (by rfl) ⟨2619600, by rfl⟩ : syracuseStep 6985601 = 5239201) B5239201
theorem B3931679 : Blo 1379509 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B14917459 : Blo 1379509 14917459 := bstep (se 1 (by rfl) ⟨11188094, by rfl⟩ : syracuseStep 14917459 = 22376189) B22376189
theorem B28721087 : Blo 1379509 28721087 := bstep (se 1 (by rfl) ⟨21540815, by rfl⟩ : syracuseStep 28721087 = 43081631) B43081631
theorem B3104747 : Blo 1379509 3104747 := bstep (se 1 (by rfl) ⟨2328560, by rfl⟩ : syracuseStep 3104747 = 4657121) B4657121
theorem B5898271 : Blo 1379509 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B3933775 : Blo 1379509 3933775 := bstep (se 1 (by rfl) ⟨2950331, by rfl⟩ : syracuseStep 3933775 = 5900663) B5900663
theorem B5900921 : Blo 1379509 5900921 := bstep (se 2 (by rfl) ⟨2212845, by rfl⟩ : syracuseStep 5900921 = 4425691) B4425691
theorem B19147391 : Blo 1379509 19147391 := bstep (se 1 (by rfl) ⟨14360543, by rfl⟩ : syracuseStep 19147391 = 28721087) B28721087
theorem B21548029 : Blo 1379509 21548029 := bstep (se 3 (by rfl) ⟨4040255, by rfl⟩ : syracuseStep 21548029 = 8080511) B8080511
theorem B4656257 : Blo 1379509 4656257 := bstep (se 2 (by rfl) ⟨1746096, by rfl⟩ : syracuseStep 4656257 = 3492193) B3492193
theorem B75582719 : Blo 1379509 75582719 := bstep (se 1 (by rfl) ⟨56687039, by rfl⟩ : syracuseStep 75582719 = 113374079) B113374079
theorem B1380199 : Blo 1379509 1380199 := bstep (se 1 (by rfl) ⟨1035149, by rfl⟩ : syracuseStep 1380199 = 2070299) B2070299
theorem B4657067 : Blo 1379509 4657067 := bstep (se 1 (by rfl) ⟨3492800, by rfl⟩ : syracuseStep 4657067 = 6985601) B6985601
theorem B1552495 : Blo 1379509 1552495 := bstep (se 1 (by rfl) ⟨1164371, by rfl⟩ : syracuseStep 1552495 = 2328743) B2328743
theorem B2330761 : Blo 1379509 2330761 := bstep (se 2 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 2330761 = 1748071) B1748071
theorem B2069831 : Blo 1379509 2069831 := bstep (se 1 (by rfl) ⟨1552373, by rfl⟩ : syracuseStep 2069831 = 3104747) B3104747
theorem B10484477 : Blo 1379509 10484477 := bstep (se 3 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 10484477 = 3931679) B3931679
theorem B19889945 : Blo 1379509 19889945 := bstep (se 2 (by rfl) ⟨7458729, by rfl⟩ : syracuseStep 19889945 = 14917459) B14917459
theorem B7864361 : Blo 1379509 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B28730705 : Blo 1379509 28730705 := bstep (se 2 (by rfl) ⟨10774014, by rfl⟩ : syracuseStep 28730705 = 21548029) B21548029
theorem B3933947 : Blo 1379509 3933947 := bstep (se 1 (by rfl) ⟨2950460, by rfl⟩ : syracuseStep 3933947 = 5900921) B5900921
theorem B12764927 : Blo 1379509 12764927 := bstep (se 1 (by rfl) ⟨9573695, by rfl⟩ : syracuseStep 12764927 = 19147391) B19147391
theorem B6989651 : Blo 1379509 6989651 := bstep (se 1 (by rfl) ⟨5242238, by rfl⟩ : syracuseStep 6989651 = 10484477) B10484477
theorem B5245033 : Blo 1379509 5245033 := bstep (se 2 (by rfl) ⟨1966887, by rfl⟩ : syracuseStep 5245033 = 3933775) B3933775
theorem B3107681 : Blo 1379509 3107681 := bstep (se 2 (by rfl) ⟨1165380, by rfl⟩ : syracuseStep 3107681 = 2330761) B2330761
theorem B1379887 : Blo 1379509 1379887 := bstep (se 1 (by rfl) ⟨1034915, by rfl⟩ : syracuseStep 1379887 = 2069831) B2069831
theorem B13259963 : Blo 1379509 13259963 := bstep (se 1 (by rfl) ⟨9944972, by rfl⟩ : syracuseStep 13259963 = 19889945) B19889945
theorem B2069993 : Blo 1379509 2069993 := bstep (se 2 (by rfl) ⟨776247, by rfl⟩ : syracuseStep 2069993 = 1552495) B1552495
theorem B3104171 : Blo 1379509 3104171 := bstep (se 1 (by rfl) ⟨2328128, by rfl⟩ : syracuseStep 3104171 = 4656257) B4656257
theorem B50388479 : Blo 1379509 50388479 := bstep (se 1 (by rfl) ⟨37791359, by rfl⟩ : syracuseStep 50388479 = 75582719) B75582719
theorem B3104711 : Blo 1379509 3104711 := bstep (se 1 (by rfl) ⟨2328533, by rfl⟩ : syracuseStep 3104711 = 4657067) B4657067
theorem B5242907 : Blo 1379509 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B8839975 : Blo 1379509 8839975 := bstep (se 1 (by rfl) ⟨6629981, by rfl⟩ : syracuseStep 8839975 = 13259963) B13259963
theorem B2622631 : Blo 1379509 2622631 := bstep (se 1 (by rfl) ⟨1966973, by rfl⟩ : syracuseStep 2622631 = 3933947) B3933947
theorem B1379995 : Blo 1379509 1379995 := bstep (se 1 (by rfl) ⟨1034996, by rfl⟩ : syracuseStep 1379995 = 2069993) B2069993
theorem B2069447 : Blo 1379509 2069447 := bstep (se 1 (by rfl) ⟨1552085, by rfl⟩ : syracuseStep 2069447 = 3104171) B3104171
theorem B33592319 : Blo 1379509 33592319 := bstep (se 1 (by rfl) ⟨25194239, by rfl⟩ : syracuseStep 33592319 = 50388479) B50388479
theorem B2069807 : Blo 1379509 2069807 := bstep (se 1 (by rfl) ⟨1552355, by rfl⟩ : syracuseStep 2069807 = 3104711) B3104711
theorem B6993377 : Blo 1379509 6993377 := bstep (se 2 (by rfl) ⟨2622516, by rfl⟩ : syracuseStep 6993377 = 5245033) B5245033
theorem B306460853 : Blo 1379509 306460853 := bstep (se 5 (by rfl) ⟨14365352, by rfl⟩ : syracuseStep 306460853 = 28730705) B28730705
theorem B8509951 : Blo 1379509 8509951 := bstep (se 1 (by rfl) ⟨6382463, by rfl⟩ : syracuseStep 8509951 = 12764927) B12764927
theorem B4659767 : Blo 1379509 4659767 := bstep (se 1 (by rfl) ⟨3494825, by rfl⟩ : syracuseStep 4659767 = 6989651) B6989651
theorem B2071787 : Blo 1379509 2071787 := bstep (se 1 (by rfl) ⟨1553840, by rfl⟩ : syracuseStep 2071787 = 3107681) B3107681
theorem B11346601 : Blo 1379509 11346601 := bstep (se 2 (by rfl) ⟨4254975, by rfl⟩ : syracuseStep 11346601 = 8509951) B8509951
theorem B4662251 : Blo 1379509 4662251 := bstep (se 1 (by rfl) ⟨3496688, by rfl⟩ : syracuseStep 4662251 = 6993377) B6993377
theorem B3106511 : Blo 1379509 3106511 := bstep (se 1 (by rfl) ⟨2329883, by rfl⟩ : syracuseStep 3106511 = 4659767) B4659767
theorem B1379631 : Blo 1379509 1379631 := bstep (se 1 (by rfl) ⟨1034723, by rfl⟩ : syracuseStep 1379631 = 2069447) B2069447
theorem B1379871 : Blo 1379509 1379871 := bstep (se 1 (by rfl) ⟨1034903, by rfl⟩ : syracuseStep 1379871 = 2069807) B2069807
theorem B1381191 : Blo 1379509 1381191 := bstep (se 1 (by rfl) ⟨1035893, by rfl⟩ : syracuseStep 1381191 = 2071787) B2071787
theorem B3495271 : Blo 1379509 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B22394879 : Blo 1379509 22394879 := bstep (se 1 (by rfl) ⟨16796159, by rfl⟩ : syracuseStep 22394879 = 33592319) B33592319
theorem B11786633 : Blo 1379509 11786633 := bstep (se 2 (by rfl) ⟨4419987, by rfl⟩ : syracuseStep 11786633 = 8839975) B8839975
theorem B204307235 : Blo 1379509 204307235 := bstep (se 1 (by rfl) ⟨153230426, by rfl⟩ : syracuseStep 204307235 = 306460853) B306460853
theorem B3496841 : Blo 1379509 3496841 := bstep (se 2 (by rfl) ⟨1311315, by rfl⟩ : syracuseStep 3496841 = 2622631) B2622631
theorem B7857755 : Blo 1379509 7857755 := bstep (se 1 (by rfl) ⟨5893316, by rfl⟩ : syracuseStep 7857755 = 11786633) B11786633
theorem B3108167 : Blo 1379509 3108167 := bstep (se 1 (by rfl) ⟨2331125, by rfl⟩ : syracuseStep 3108167 = 4662251) B4662251
theorem B14929919 : Blo 1379509 14929919 := bstep (se 1 (by rfl) ⟨11197439, by rfl⟩ : syracuseStep 14929919 = 22394879) B22394879
theorem B136204823 : Blo 1379509 136204823 := bstep (se 1 (by rfl) ⟨102153617, by rfl⟩ : syracuseStep 136204823 = 204307235) B204307235
theorem B2331227 : Blo 1379509 2331227 := bstep (se 1 (by rfl) ⟨1748420, by rfl⟩ : syracuseStep 2331227 = 3496841) B3496841
theorem B15128801 : Blo 1379509 15128801 := bstep (se 2 (by rfl) ⟨5673300, by rfl⟩ : syracuseStep 15128801 = 11346601) B11346601
theorem B2071007 : Blo 1379509 2071007 := bstep (se 1 (by rfl) ⟨1553255, by rfl⟩ : syracuseStep 2071007 = 3106511) B3106511
theorem B4660361 : Blo 1379509 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B10085867 : Blo 1379509 10085867 := bstep (se 1 (by rfl) ⟨7564400, by rfl⟩ : syracuseStep 10085867 = 15128801) B15128801
theorem B3106907 : Blo 1379509 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B90803215 : Blo 1379509 90803215 := bstep (se 1 (by rfl) ⟨68102411, by rfl⟩ : syracuseStep 90803215 = 136204823) B136204823
theorem B5238503 : Blo 1379509 5238503 := bstep (se 1 (by rfl) ⟨3928877, by rfl⟩ : syracuseStep 5238503 = 7857755) B7857755
theorem B1380671 : Blo 1379509 1380671 := bstep (se 1 (by rfl) ⟨1035503, by rfl⟩ : syracuseStep 1380671 = 2071007) B2071007
theorem B1554151 : Blo 1379509 1554151 := bstep (se 1 (by rfl) ⟨1165613, by rfl⟩ : syracuseStep 1554151 = 2331227) B2331227
theorem B2072111 : Blo 1379509 2072111 := bstep (se 1 (by rfl) ⟨1554083, by rfl⟩ : syracuseStep 2072111 = 3108167) B3108167
theorem B9953279 : Blo 1379509 9953279 := bstep (se 1 (by rfl) ⟨7464959, by rfl⟩ : syracuseStep 9953279 = 14929919) B14929919
theorem B121070953 : Blo 1379509 121070953 := bstep (se 2 (by rfl) ⟨45401607, by rfl⟩ : syracuseStep 121070953 = 90803215) B90803215
theorem B3492335 : Blo 1379509 3492335 := bstep (se 1 (by rfl) ⟨2619251, by rfl⟩ : syracuseStep 3492335 = 5238503) B5238503
theorem B6635519 : Blo 1379509 6635519 := bstep (se 1 (by rfl) ⟨4976639, by rfl⟩ : syracuseStep 6635519 = 9953279) B9953279
theorem B1381407 : Blo 1379509 1381407 := bstep (se 1 (by rfl) ⟨1036055, by rfl⟩ : syracuseStep 1381407 = 2072111) B2072111
theorem B6723911 : Blo 1379509 6723911 := bstep (se 1 (by rfl) ⟨5042933, by rfl⟩ : syracuseStep 6723911 = 10085867) B10085867
theorem B2071271 : Blo 1379509 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B2072201 : Blo 1379509 2072201 := bstep (se 2 (by rfl) ⟨777075, by rfl⟩ : syracuseStep 2072201 = 1554151) B1554151
theorem B2328223 : Blo 1379509 2328223 := bstep (se 1 (by rfl) ⟨1746167, by rfl⟩ : syracuseStep 2328223 = 3492335) B3492335
theorem B161427937 : Blo 1379509 161427937 := bstep (se 2 (by rfl) ⟨60535476, by rfl⟩ : syracuseStep 161427937 = 121070953) B121070953
theorem B1380847 : Blo 1379509 1380847 := bstep (se 1 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 1380847 = 2071271) B2071271
theorem B1381467 : Blo 1379509 1381467 := bstep (se 1 (by rfl) ⟨1036100, by rfl⟩ : syracuseStep 1381467 = 2072201) B2072201
theorem B17930429 : Blo 1379509 17930429 := bstep (se 3 (by rfl) ⟨3361955, by rfl⟩ : syracuseStep 17930429 = 6723911) B6723911
theorem B4423679 : Blo 1379509 4423679 := bstep (se 1 (by rfl) ⟨3317759, by rfl⟩ : syracuseStep 4423679 = 6635519) B6635519
theorem B215237249 : Blo 1379509 215237249 := bstep (se 2 (by rfl) ⟨80713968, by rfl⟩ : syracuseStep 215237249 = 161427937) B161427937
theorem B11953619 : Blo 1379509 11953619 := bstep (se 1 (by rfl) ⟨8965214, by rfl⟩ : syracuseStep 11953619 = 17930429) B17930429
theorem B2949119 : Blo 1379509 2949119 := bstep (se 1 (by rfl) ⟨2211839, by rfl⟩ : syracuseStep 2949119 = 4423679) B4423679
theorem B3104297 : Blo 1379509 3104297 := bstep (se 2 (by rfl) ⟨1164111, by rfl⟩ : syracuseStep 3104297 = 2328223) B2328223
theorem B143491499 : Blo 1379509 143491499 := bstep (se 1 (by rfl) ⟨107618624, by rfl⟩ : syracuseStep 143491499 = 215237249) B215237249
theorem B2069531 : Blo 1379509 2069531 := bstep (se 1 (by rfl) ⟨1552148, by rfl⟩ : syracuseStep 2069531 = 3104297) B3104297
theorem B7969079 : Blo 1379509 7969079 := bstep (se 1 (by rfl) ⟨5976809, by rfl⟩ : syracuseStep 7969079 = 11953619) B11953619
theorem B1966079 : Blo 1379509 1966079 := bstep (se 1 (by rfl) ⟨1474559, by rfl⟩ : syracuseStep 1966079 = 2949119) B2949119
theorem B95660999 : Blo 1379509 95660999 := bstep (se 1 (by rfl) ⟨71745749, by rfl⟩ : syracuseStep 95660999 = 143491499) B143491499
theorem B1379687 : Blo 1379509 1379687 := bstep (se 1 (by rfl) ⟨1034765, by rfl⟩ : syracuseStep 1379687 = 2069531) B2069531
theorem B5312719 : Blo 1379509 5312719 := bstep (se 1 (by rfl) ⟨3984539, by rfl⟩ : syracuseStep 5312719 = 7969079) B7969079
theorem B5242877 : Blo 1379509 5242877 := bstep (se 3 (by rfl) ⟨983039, by rfl⟩ : syracuseStep 5242877 = 1966079) B1966079
theorem B3495251 : Blo 1379509 3495251 := bstep (se 1 (by rfl) ⟨2621438, by rfl⟩ : syracuseStep 3495251 = 5242877) B5242877
theorem B7083625 : Blo 1379509 7083625 := bstep (se 2 (by rfl) ⟨2656359, by rfl⟩ : syracuseStep 7083625 = 5312719) B5312719
theorem B63773999 : Blo 1379509 63773999 := bstep (se 1 (by rfl) ⟨47830499, by rfl⟩ : syracuseStep 63773999 = 95660999) B95660999
theorem B2330167 : Blo 1379509 2330167 := bstep (se 1 (by rfl) ⟨1747625, by rfl⟩ : syracuseStep 2330167 = 3495251) B3495251
theorem B9444833 : Blo 1379509 9444833 := bstep (se 2 (by rfl) ⟨3541812, by rfl⟩ : syracuseStep 9444833 = 7083625) B7083625
theorem B42515999 : Blo 1379509 42515999 := bstep (se 1 (by rfl) ⟨31886999, by rfl⟩ : syracuseStep 42515999 = 63773999) B63773999
theorem B3106889 : Blo 1379509 3106889 := bstep (se 2 (by rfl) ⟨1165083, by rfl⟩ : syracuseStep 3106889 = 2330167) B2330167
theorem B6296555 : Blo 1379509 6296555 := bstep (se 1 (by rfl) ⟨4722416, by rfl⟩ : syracuseStep 6296555 = 9444833) B9444833
theorem B28343999 : Blo 1379509 28343999 := bstep (se 1 (by rfl) ⟨21257999, by rfl⟩ : syracuseStep 28343999 = 42515999) B42515999
theorem B4197703 : Blo 1379509 4197703 := bstep (se 1 (by rfl) ⟨3148277, by rfl⟩ : syracuseStep 4197703 = 6296555) B6296555
theorem B18895999 : Blo 1379509 18895999 := bstep (se 1 (by rfl) ⟨14171999, by rfl⟩ : syracuseStep 18895999 = 28343999) B28343999
theorem B2071259 : Blo 1379509 2071259 := bstep (se 1 (by rfl) ⟨1553444, by rfl⟩ : syracuseStep 2071259 = 3106889) B3106889
theorem B5596937 : Blo 1379509 5596937 := bstep (se 2 (by rfl) ⟨2098851, by rfl⟩ : syracuseStep 5596937 = 4197703) B4197703
theorem B25194665 : Blo 1379509 25194665 := bstep (se 2 (by rfl) ⟨9447999, by rfl⟩ : syracuseStep 25194665 = 18895999) B18895999
theorem B1380839 : Blo 1379509 1380839 := bstep (se 1 (by rfl) ⟨1035629, by rfl⟩ : syracuseStep 1380839 = 2071259) B2071259
theorem B16796443 : Blo 1379509 16796443 := bstep (se 1 (by rfl) ⟨12597332, by rfl⟩ : syracuseStep 16796443 = 25194665) B25194665
theorem B3731291 : Blo 1379509 3731291 := bstep (se 1 (by rfl) ⟨2798468, by rfl⟩ : syracuseStep 3731291 = 5596937) B5596937
theorem B2487527 : Blo 1379509 2487527 := bstep (se 1 (by rfl) ⟨1865645, by rfl⟩ : syracuseStep 2487527 = 3731291) B3731291
theorem B22395257 : Blo 1379509 22395257 := bstep (se 2 (by rfl) ⟨8398221, by rfl⟩ : syracuseStep 22395257 = 16796443) B16796443
theorem B1658351 : Blo 1379509 1658351 := bstep (se 1 (by rfl) ⟨1243763, by rfl⟩ : syracuseStep 1658351 = 2487527) B2487527
theorem B14930171 : Blo 1379509 14930171 := bstep (se 1 (by rfl) ⟨11197628, by rfl⟩ : syracuseStep 14930171 = 22395257) B22395257
theorem B9953447 : Blo 1379509 9953447 := bstep (se 1 (by rfl) ⟨7465085, by rfl⟩ : syracuseStep 9953447 = 14930171) B14930171
theorem B4422269 : Blo 1379509 4422269 := bstep (se 3 (by rfl) ⟨829175, by rfl⟩ : syracuseStep 4422269 = 1658351) B1658351
theorem B26542525 : Blo 1379509 26542525 := bstep (se 3 (by rfl) ⟨4976723, by rfl⟩ : syracuseStep 26542525 = 9953447) B9953447
theorem B2948179 : Blo 1379509 2948179 := bstep (se 1 (by rfl) ⟨2211134, by rfl⟩ : syracuseStep 2948179 = 4422269) B4422269
theorem B35390033 : Blo 1379509 35390033 := bstep (se 2 (by rfl) ⟨13271262, by rfl⟩ : syracuseStep 35390033 = 26542525) B26542525
theorem B3930905 : Blo 1379509 3930905 := bstep (se 2 (by rfl) ⟨1474089, by rfl⟩ : syracuseStep 3930905 = 2948179) B2948179
theorem B23593355 : Blo 1379509 23593355 := bstep (se 1 (by rfl) ⟨17695016, by rfl⟩ : syracuseStep 23593355 = 35390033) B35390033
theorem B2620603 : Blo 1379509 2620603 := bstep (se 1 (by rfl) ⟨1965452, by rfl⟩ : syracuseStep 2620603 = 3930905) B3930905
theorem B15728903 : Blo 1379509 15728903 := bstep (se 1 (by rfl) ⟨11796677, by rfl⟩ : syracuseStep 15728903 = 23593355) B23593355
theorem B3494137 : Blo 1379509 3494137 := bstep (se 2 (by rfl) ⟨1310301, by rfl⟩ : syracuseStep 3494137 = 2620603) B2620603
theorem B10485935 : Blo 1379509 10485935 := bstep (se 1 (by rfl) ⟨7864451, by rfl⟩ : syracuseStep 10485935 = 15728903) B15728903
theorem B4658849 : Blo 1379509 4658849 := bstep (se 2 (by rfl) ⟨1747068, by rfl⟩ : syracuseStep 4658849 = 3494137) B3494137
theorem B3105899 : Blo 1379509 3105899 := bstep (se 1 (by rfl) ⟨2329424, by rfl⟩ : syracuseStep 3105899 = 4658849) B4658849
theorem B6990623 : Blo 1379509 6990623 := bstep (se 1 (by rfl) ⟨5242967, by rfl⟩ : syracuseStep 6990623 = 10485935) B10485935
theorem B2070599 : Blo 1379509 2070599 := bstep (se 1 (by rfl) ⟨1552949, by rfl⟩ : syracuseStep 2070599 = 3105899) B3105899
theorem B4660415 : Blo 1379509 4660415 := bstep (se 1 (by rfl) ⟨3495311, by rfl⟩ : syracuseStep 4660415 = 6990623) B6990623
theorem B3106943 : Blo 1379509 3106943 := bstep (se 1 (by rfl) ⟨2330207, by rfl⟩ : syracuseStep 3106943 = 4660415) B4660415
theorem B1380399 : Blo 1379509 1380399 := bstep (se 1 (by rfl) ⟨1035299, by rfl⟩ : syracuseStep 1380399 = 2070599) B2070599
theorem B2071295 : Blo 1379509 2071295 := bstep (se 1 (by rfl) ⟨1553471, by rfl⟩ : syracuseStep 2071295 = 3106943) B3106943
theorem B1380863 : Blo 1379509 1380863 := bstep (se 1 (by rfl) ⟨1035647, by rfl⟩ : syracuseStep 1380863 = 2071295) B2071295

theorem C0 (j : ℕ) (h1 : 344877 ≤ j) (h2 : j ≤ 345376) : Blo 1379509 (4 * j + 3) := by
  interval_cases j
  · exact B1379511
  · exact B1379515
  · exact B1379519
  · exact B1379523
  · exact B1379527
  · exact B1379531
  · exact B1379535
  · exact B1379539
  · exact B1379543
  · exact B1379547
  · exact B1379551
  · exact B1379555
  · exact B1379559
  · exact B1379563
  · exact B1379567
  · exact B1379571
  · exact B1379575
  · exact B1379579
  · exact B1379583
  · exact B1379587
  · exact B1379591
  · exact B1379595
  · exact B1379599
  · exact B1379603
  · exact B1379607
  · exact B1379611
  · exact B1379615
  · exact B1379619
  · exact B1379623
  · exact B1379627
  · exact B1379631
  · exact B1379635
  · exact B1379639
  · exact B1379643
  · exact B1379647
  · exact B1379651
  · exact B1379655
  · exact B1379659
  · exact B1379663
  · exact B1379667
  · exact B1379671
  · exact B1379675
  · exact B1379679
  · exact B1379683
  · exact B1379687
  · exact B1379691
  · exact B1379695
  · exact B1379699
  · exact B1379703
  · exact B1379707
  · exact B1379711
  · exact B1379715
  · exact B1379719
  · exact B1379723
  · exact B1379727
  · exact B1379731
  · exact B1379735
  · exact B1379739
  · exact B1379743
  · exact B1379747
  · exact B1379751
  · exact B1379755
  · exact B1379759
  · exact B1379763
  · exact B1379767
  · exact B1379771
  · exact B1379775
  · exact B1379779
  · exact B1379783
  · exact B1379787
  · exact B1379791
  · exact B1379795
  · exact B1379799
  · exact B1379803
  · exact B1379807
  · exact B1379811
  · exact B1379815
  · exact B1379819
  · exact B1379823
  · exact B1379827
  · exact B1379831
  · exact B1379835
  · exact B1379839
  · exact B1379843
  · exact B1379847
  · exact B1379851
  · exact B1379855
  · exact B1379859
  · exact B1379863
  · exact B1379867
  · exact B1379871
  · exact B1379875
  · exact B1379879
  · exact B1379883
  · exact B1379887
  · exact B1379891
  · exact B1379895
  · exact B1379899
  · exact B1379903
  · exact B1379907
  · exact B1379911
  · exact B1379915
  · exact B1379919
  · exact B1379923
  · exact B1379927
  · exact B1379931
  · exact B1379935
  · exact B1379939
  · exact B1379943
  · exact B1379947
  · exact B1379951
  · exact B1379955
  · exact B1379959
  · exact B1379963
  · exact B1379967
  · exact B1379971
  · exact B1379975
  · exact B1379979
  · exact B1379983
  · exact B1379987
  · exact B1379991
  · exact B1379995
  · exact B1379999
  · exact B1380003
  · exact B1380007
  · exact B1380011
  · exact B1380015
  · exact B1380019
  · exact B1380023
  · exact B1380027
  · exact B1380031
  · exact B1380035
  · exact B1380039
  · exact B1380043
  · exact B1380047
  · exact B1380051
  · exact B1380055
  · exact B1380059
  · exact B1380063
  · exact B1380067
  · exact B1380071
  · exact B1380075
  · exact B1380079
  · exact B1380083
  · exact B1380087
  · exact B1380091
  · exact B1380095
  · exact B1380099
  · exact B1380103
  · exact B1380107
  · exact B1380111
  · exact B1380115
  · exact B1380119
  · exact B1380123
  · exact B1380127
  · exact B1380131
  · exact B1380135
  · exact B1380139
  · exact B1380143
  · exact B1380147
  · exact B1380151
  · exact B1380155
  · exact B1380159
  · exact B1380163
  · exact B1380167
  · exact B1380171
  · exact B1380175
  · exact B1380179
  · exact B1380183
  · exact B1380187
  · exact B1380191
  · exact B1380195
  · exact B1380199
  · exact B1380203
  · exact B1380207
  · exact B1380211
  · exact B1380215
  · exact B1380219
  · exact B1380223
  · exact B1380227
  · exact B1380231
  · exact B1380235
  · exact B1380239
  · exact B1380243
  · exact B1380247
  · exact B1380251
  · exact B1380255
  · exact B1380259
  · exact B1380263
  · exact B1380267
  · exact B1380271
  · exact B1380275
  · exact B1380279
  · exact B1380283
  · exact B1380287
  · exact B1380291
  · exact B1380295
  · exact B1380299
  · exact B1380303
  · exact B1380307
  · exact B1380311
  · exact B1380315
  · exact B1380319
  · exact B1380323
  · exact B1380327
  · exact B1380331
  · exact B1380335
  · exact B1380339
  · exact B1380343
  · exact B1380347
  · exact B1380351
  · exact B1380355
  · exact B1380359
  · exact B1380363
  · exact B1380367
  · exact B1380371
  · exact B1380375
  · exact B1380379
  · exact B1380383
  · exact B1380387
  · exact B1380391
  · exact B1380395
  · exact B1380399
  · exact B1380403
  · exact B1380407
  · exact B1380411
  · exact B1380415
  · exact B1380419
  · exact B1380423
  · exact B1380427
  · exact B1380431
  · exact B1380435
  · exact B1380439
  · exact B1380443
  · exact B1380447
  · exact B1380451
  · exact B1380455
  · exact B1380459
  · exact B1380463
  · exact B1380467
  · exact B1380471
  · exact B1380475
  · exact B1380479
  · exact B1380483
  · exact B1380487
  · exact B1380491
  · exact B1380495
  · exact B1380499
  · exact B1380503
  · exact B1380507
  · exact B1380511
  · exact B1380515
  · exact B1380519
  · exact B1380523
  · exact B1380527
  · exact B1380531
  · exact B1380535
  · exact B1380539
  · exact B1380543
  · exact B1380547
  · exact B1380551
  · exact B1380555
  · exact B1380559
  · exact B1380563
  · exact B1380567
  · exact B1380571
  · exact B1380575
  · exact B1380579
  · exact B1380583
  · exact B1380587
  · exact B1380591
  · exact B1380595
  · exact B1380599
  · exact B1380603
  · exact B1380607
  · exact B1380611
  · exact B1380615
  · exact B1380619
  · exact B1380623
  · exact B1380627
  · exact B1380631
  · exact B1380635
  · exact B1380639
  · exact B1380643
  · exact B1380647
  · exact B1380651
  · exact B1380655
  · exact B1380659
  · exact B1380663
  · exact B1380667
  · exact B1380671
  · exact B1380675
  · exact B1380679
  · exact B1380683
  · exact B1380687
  · exact B1380691
  · exact B1380695
  · exact B1380699
  · exact B1380703
  · exact B1380707
  · exact B1380711
  · exact B1380715
  · exact B1380719
  · exact B1380723
  · exact B1380727
  · exact B1380731
  · exact B1380735
  · exact B1380739
  · exact B1380743
  · exact B1380747
  · exact B1380751
  · exact B1380755
  · exact B1380759
  · exact B1380763
  · exact B1380767
  · exact B1380771
  · exact B1380775
  · exact B1380779
  · exact B1380783
  · exact B1380787
  · exact B1380791
  · exact B1380795
  · exact B1380799
  · exact B1380803
  · exact B1380807
  · exact B1380811
  · exact B1380815
  · exact B1380819
  · exact B1380823
  · exact B1380827
  · exact B1380831
  · exact B1380835
  · exact B1380839
  · exact B1380843
  · exact B1380847
  · exact B1380851
  · exact B1380855
  · exact B1380859
  · exact B1380863
  · exact B1380867
  · exact B1380871
  · exact B1380875
  · exact B1380879
  · exact B1380883
  · exact B1380887
  · exact B1380891
  · exact B1380895
  · exact B1380899
  · exact B1380903
  · exact B1380907
  · exact B1380911
  · exact B1380915
  · exact B1380919
  · exact B1380923
  · exact B1380927
  · exact B1380931
  · exact B1380935
  · exact B1380939
  · exact B1380943
  · exact B1380947
  · exact B1380951
  · exact B1380955
  · exact B1380959
  · exact B1380963
  · exact B1380967
  · exact B1380971
  · exact B1380975
  · exact B1380979
  · exact B1380983
  · exact B1380987
  · exact B1380991
  · exact B1380995
  · exact B1380999
  · exact B1381003
  · exact B1381007
  · exact B1381011
  · exact B1381015
  · exact B1381019
  · exact B1381023
  · exact B1381027
  · exact B1381031
  · exact B1381035
  · exact B1381039
  · exact B1381043
  · exact B1381047
  · exact B1381051
  · exact B1381055
  · exact B1381059
  · exact B1381063
  · exact B1381067
  · exact B1381071
  · exact B1381075
  · exact B1381079
  · exact B1381083
  · exact B1381087
  · exact B1381091
  · exact B1381095
  · exact B1381099
  · exact B1381103
  · exact B1381107
  · exact B1381111
  · exact B1381115
  · exact B1381119
  · exact B1381123
  · exact B1381127
  · exact B1381131
  · exact B1381135
  · exact B1381139
  · exact B1381143
  · exact B1381147
  · exact B1381151
  · exact B1381155
  · exact B1381159
  · exact B1381163
  · exact B1381167
  · exact B1381171
  · exact B1381175
  · exact B1381179
  · exact B1381183
  · exact B1381187
  · exact B1381191
  · exact B1381195
  · exact B1381199
  · exact B1381203
  · exact B1381207
  · exact B1381211
  · exact B1381215
  · exact B1381219
  · exact B1381223
  · exact B1381227
  · exact B1381231
  · exact B1381235
  · exact B1381239
  · exact B1381243
  · exact B1381247
  · exact B1381251
  · exact B1381255
  · exact B1381259
  · exact B1381263
  · exact B1381267
  · exact B1381271
  · exact B1381275
  · exact B1381279
  · exact B1381283
  · exact B1381287
  · exact B1381291
  · exact B1381295
  · exact B1381299
  · exact B1381303
  · exact B1381307
  · exact B1381311
  · exact B1381315
  · exact B1381319
  · exact B1381323
  · exact B1381327
  · exact B1381331
  · exact B1381335
  · exact B1381339
  · exact B1381343
  · exact B1381347
  · exact B1381351
  · exact B1381355
  · exact B1381359
  · exact B1381363
  · exact B1381367
  · exact B1381371
  · exact B1381375
  · exact B1381379
  · exact B1381383
  · exact B1381387
  · exact B1381391
  · exact B1381395
  · exact B1381399
  · exact B1381403
  · exact B1381407
  · exact B1381411
  · exact B1381415
  · exact B1381419
  · exact B1381423
  · exact B1381427
  · exact B1381431
  · exact B1381435
  · exact B1381439
  · exact B1381443
  · exact B1381447
  · exact B1381451
  · exact B1381455
  · exact B1381459
  · exact B1381463
  · exact B1381467
  · exact B1381471
  · exact B1381475
  · exact B1381479
  · exact B1381483
  · exact B1381487
  · exact B1381491
  · exact B1381495
  · exact B1381499
  · exact B1381503
  · exact B1381507

theorem solution (m : ℕ) (hlo : 1379509 ≤ m) (hhi : m ≤ 1381509) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 344877 ≤ j := by omega
    have hj2 : j ≤ 345376 := by omega
    have hb : Blo 1379509 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
