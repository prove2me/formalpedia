-- Prove2me | solution 1 for syracuse_descends_range_463784_467784
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:02.432973+00:00
-- url     : https://prove2.me/submissions/ca836cb0-1a3f-4679-9a39-bdbd38683d69

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


theorem B1048589 : Blo 463784 1048589 := bbase (se 3 (by rfl) ⟨196610, by rfl⟩ : syracuseStep 1048589 = 393221) (by norm_num)
theorem B589837 : Blo 463784 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B524317 : Blo 463784 524317 := bbase (se 3 (by rfl) ⟨98309, by rfl⟩ : syracuseStep 524317 = 196619) (by norm_num)
theorem B786469 : Blo 463784 786469 := bbase (se 4 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 786469 = 147463) (by norm_num)
theorem B524353 : Blo 463784 524353 := bbase (se 2 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 524353 = 393265) (by norm_num)
theorem B1048661 : Blo 463784 1048661 := bbase (se 8 (by rfl) ⟨6144, by rfl⟩ : syracuseStep 1048661 = 12289) (by norm_num)
theorem B1572965 : Blo 463784 1572965 := bbase (se 4 (by rfl) ⟨147465, by rfl⟩ : syracuseStep 1572965 = 294931) (by norm_num)
theorem B524389 : Blo 463784 524389 := bbase (se 4 (by rfl) ⟨49161, by rfl⟩ : syracuseStep 524389 = 98323) (by norm_num)
theorem B589933 : Blo 463784 589933 := bbase (se 3 (by rfl) ⟨110612, by rfl⟩ : syracuseStep 589933 = 221225) (by norm_num)
theorem B786557 : Blo 463784 786557 := bbase (se 3 (by rfl) ⟨147479, by rfl⟩ : syracuseStep 786557 = 294959) (by norm_num)
theorem B524425 : Blo 463784 524425 := bbase (se 2 (by rfl) ⟨196659, by rfl⟩ : syracuseStep 524425 = 393319) (by norm_num)
theorem B1179805 : Blo 463784 1179805 := bbase (se 3 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 1179805 = 442427) (by norm_num)
theorem B1048733 : Blo 463784 1048733 := bbase (se 3 (by rfl) ⟨196637, by rfl⟩ : syracuseStep 1048733 = 393275) (by norm_num)
theorem B524461 : Blo 463784 524461 := bbase (se 3 (by rfl) ⟨98336, by rfl⟩ : syracuseStep 524461 = 196673) (by norm_num)
theorem B557237 : Blo 463784 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B524497 : Blo 463784 524497 := bbase (se 2 (by rfl) ⟨196686, by rfl⟩ : syracuseStep 524497 = 393373) (by norm_num)
theorem B1048805 : Blo 463784 1048805 := bbase (se 4 (by rfl) ⟨98325, by rfl⟩ : syracuseStep 1048805 = 196651) (by norm_num)
theorem B524533 : Blo 463784 524533 := bbase (se 5 (by rfl) ⟨24587, by rfl⟩ : syracuseStep 524533 = 49175) (by norm_num)
theorem B786685 : Blo 463784 786685 := bbase (se 3 (by rfl) ⟨147503, by rfl⟩ : syracuseStep 786685 = 295007) (by norm_num)
theorem B1179917 : Blo 463784 1179917 := bbase (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) (by norm_num)
theorem B590105 : Blo 463784 590105 := bbase (se 2 (by rfl) ⟨221289, by rfl⟩ : syracuseStep 590105 = 442579) (by norm_num)
theorem B524569 : Blo 463784 524569 := bbase (se 2 (by rfl) ⟨196713, by rfl⟩ : syracuseStep 524569 = 393427) (by norm_num)
theorem B1048877 : Blo 463784 1048877 := bbase (se 3 (by rfl) ⟨196664, by rfl⟩ : syracuseStep 1048877 = 393329) (by norm_num)
theorem B524605 : Blo 463784 524605 := bbase (se 3 (by rfl) ⟨98363, by rfl⟩ : syracuseStep 524605 = 196727) (by norm_num)
theorem B590161 : Blo 463784 590161 := bbase (se 2 (by rfl) ⟨221310, by rfl⟩ : syracuseStep 590161 = 442621) (by norm_num)
theorem B786773 : Blo 463784 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B524641 : Blo 463784 524641 := bbase (se 2 (by rfl) ⟨196740, by rfl⟩ : syracuseStep 524641 = 393481) (by norm_num)
theorem B1048949 : Blo 463784 1048949 := bbase (se 5 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 1048949 = 98339) (by norm_num)
theorem B524677 : Blo 463784 524677 := bbase (se 4 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 524677 = 98377) (by norm_num)
theorem B524713 : Blo 463784 524713 := bbase (se 2 (by rfl) ⟨196767, by rfl⟩ : syracuseStep 524713 = 393535) (by norm_num)
theorem B590257 : Blo 463784 590257 := bbase (se 2 (by rfl) ⟨221346, by rfl⟩ : syracuseStep 590257 = 442693) (by norm_num)
theorem B1049021 : Blo 463784 1049021 := bbase (se 3 (by rfl) ⟨196691, by rfl⟩ : syracuseStep 1049021 = 393383) (by norm_num)
theorem B885181 : Blo 463784 885181 := bbase (se 3 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 885181 = 331943) (by norm_num)
theorem B1180109 : Blo 463784 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B524749 : Blo 463784 524749 := bbase (se 3 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 524749 = 196781) (by norm_num)
theorem B786901 : Blo 463784 786901 := bbase (se 7 (by rfl) ⟨9221, by rfl⟩ : syracuseStep 786901 = 18443) (by norm_num)
theorem B557545 : Blo 463784 557545 := bbase (se 2 (by rfl) ⟨209079, by rfl⟩ : syracuseStep 557545 = 418159) (by norm_num)
theorem B524785 : Blo 463784 524785 := bbase (se 2 (by rfl) ⟨196794, by rfl⟩ : syracuseStep 524785 = 393589) (by norm_num)
theorem B1049093 : Blo 463784 1049093 := bbase (se 4 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 1049093 = 196705) (by norm_num)
theorem B1573397 : Blo 463784 1573397 := bbase (se 6 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 1573397 = 73753) (by norm_num)
theorem B524821 : Blo 463784 524821 := bbase (se 6 (by rfl) ⟨12300, by rfl⟩ : syracuseStep 524821 = 24601) (by norm_num)
theorem B786989 : Blo 463784 786989 := bbase (se 3 (by rfl) ⟨147560, by rfl⟩ : syracuseStep 786989 = 295121) (by norm_num)
theorem B524857 : Blo 463784 524857 := bbase (se 2 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 524857 = 393643) (by norm_num)
theorem B557641 : Blo 463784 557641 := bbase (se 2 (by rfl) ⟨209115, by rfl⟩ : syracuseStep 557641 = 418231) (by norm_num)
theorem B1049165 : Blo 463784 1049165 := bbase (se 3 (by rfl) ⟨196718, by rfl⟩ : syracuseStep 1049165 = 393437) (by norm_num)
theorem B885325 : Blo 463784 885325 := bbase (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) (by norm_num)
theorem B590429 : Blo 463784 590429 := bbase (se 3 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 590429 = 221411) (by norm_num)
theorem B524893 : Blo 463784 524893 := bbase (se 3 (by rfl) ⟨98417, by rfl⟩ : syracuseStep 524893 = 196835) (by norm_num)
theorem B524929 : Blo 463784 524929 := bbase (se 2 (by rfl) ⟨196848, by rfl⟩ : syracuseStep 524929 = 393697) (by norm_num)
theorem B1770133 : Blo 463784 1770133 := bbase (se 6 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 1770133 = 82975) (by norm_num)
theorem B1049237 : Blo 463784 1049237 := bbase (se 6 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 1049237 = 49183) (by norm_num)
theorem B590485 : Blo 463784 590485 := bbase (se 6 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 590485 = 27679) (by norm_num)
theorem B524965 : Blo 463784 524965 := bbase (se 4 (by rfl) ⟨49215, by rfl⟩ : syracuseStep 524965 = 98431) (by norm_num)
theorem B787117 : Blo 463784 787117 := bbase (se 3 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 787117 = 295169) (by norm_num)
theorem B525001 : Blo 463784 525001 := bbase (se 2 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 525001 = 393751) (by norm_num)
theorem B3572437 : Blo 463784 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B1049309 : Blo 463784 1049309 := bbase (se 3 (by rfl) ⟨196745, by rfl⟩ : syracuseStep 1049309 = 393491) (by norm_num)
theorem B885485 : Blo 463784 885485 := bbase (se 3 (by rfl) ⟨166028, by rfl⟩ : syracuseStep 885485 = 332057) (by norm_num)
theorem B525037 : Blo 463784 525037 := bbase (se 3 (by rfl) ⟨98444, by rfl⟩ : syracuseStep 525037 = 196889) (by norm_num)
theorem B590581 : Blo 463784 590581 := bbase (se 5 (by rfl) ⟨27683, by rfl⟩ : syracuseStep 590581 = 55367) (by norm_num)
theorem B1671941 : Blo 463784 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B787205 : Blo 463784 787205 := bbase (se 4 (by rfl) ⟨73800, by rfl⟩ : syracuseStep 787205 = 147601) (by norm_num)
theorem B525073 : Blo 463784 525073 := bbase (se 2 (by rfl) ⟨196902, by rfl⟩ : syracuseStep 525073 = 393805) (by norm_num)
theorem B1180453 : Blo 463784 1180453 := bbase (se 4 (by rfl) ⟨110667, by rfl⟩ : syracuseStep 1180453 = 221335) (by norm_num)
theorem B1049381 : Blo 463784 1049381 := bbase (se 4 (by rfl) ⟨98379, by rfl⟩ : syracuseStep 1049381 = 196759) (by norm_num)
theorem B525109 : Blo 463784 525109 := bbase (se 5 (by rfl) ⟨24614, by rfl⟩ : syracuseStep 525109 = 49229) (by norm_num)
theorem B3343189 : Blo 463784 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B525145 : Blo 463784 525145 := bbase (se 2 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 525145 = 393859) (by norm_num)
theorem B557929 : Blo 463784 557929 := bbase (se 2 (by rfl) ⟨209223, by rfl⟩ : syracuseStep 557929 = 418447) (by norm_num)
theorem B1049453 : Blo 463784 1049453 := bbase (se 3 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 1049453 = 393545) (by norm_num)
theorem B885629 : Blo 463784 885629 := bbase (se 3 (by rfl) ⟨166055, by rfl⟩ : syracuseStep 885629 = 332111) (by norm_num)
theorem B525181 : Blo 463784 525181 := bbase (se 3 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 525181 = 196943) (by norm_num)
theorem B787333 : Blo 463784 787333 := bbase (se 4 (by rfl) ⟨73812, by rfl⟩ : syracuseStep 787333 = 147625) (by norm_num)
theorem B1180565 : Blo 463784 1180565 := bbase (se 6 (by rfl) ⟨27669, by rfl⟩ : syracuseStep 1180565 = 55339) (by norm_num)
theorem B590753 : Blo 463784 590753 := bbase (se 2 (by rfl) ⟨221532, by rfl⟩ : syracuseStep 590753 = 443065) (by norm_num)
theorem B525217 : Blo 463784 525217 := bbase (se 2 (by rfl) ⟨196956, by rfl⟩ : syracuseStep 525217 = 393913) (by norm_num)
theorem B1049525 : Blo 463784 1049525 := bbase (se 5 (by rfl) ⟨49196, by rfl⟩ : syracuseStep 1049525 = 98393) (by norm_num)
theorem B1770437 : Blo 463784 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B1573829 : Blo 463784 1573829 := bbase (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) (by norm_num)
theorem B525253 : Blo 463784 525253 := bbase (se 4 (by rfl) ⟨49242, by rfl⟩ : syracuseStep 525253 = 98485) (by norm_num)
theorem B590809 : Blo 463784 590809 := bbase (se 2 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 590809 = 443107) (by norm_num)
theorem B787421 : Blo 463784 787421 := bbase (se 3 (by rfl) ⟨147641, by rfl⟩ : syracuseStep 787421 = 295283) (by norm_num)
theorem B525289 : Blo 463784 525289 := bbase (se 2 (by rfl) ⟨196983, by rfl⟩ : syracuseStep 525289 = 393967) (by norm_num)
theorem B1049597 : Blo 463784 1049597 := bbase (se 3 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 1049597 = 393599) (by norm_num)
theorem B525325 : Blo 463784 525325 := bbase (se 3 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 525325 = 196997) (by norm_num)
theorem B1115165 : Blo 463784 1115165 := bbase (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) (by norm_num)
theorem B558121 : Blo 463784 558121 := bbase (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) (by norm_num)
theorem B525361 : Blo 463784 525361 := bbase (se 2 (by rfl) ⟨197010, by rfl⟩ : syracuseStep 525361 = 394021) (by norm_num)
theorem B590905 : Blo 463784 590905 := bbase (se 2 (by rfl) ⟨221589, by rfl⟩ : syracuseStep 590905 = 443179) (by norm_num)
theorem B1049669 : Blo 463784 1049669 := bbase (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) (by norm_num)
theorem B1180757 : Blo 463784 1180757 := bbase (se 8 (by rfl) ⟨6918, by rfl⟩ : syracuseStep 1180757 = 13837) (by norm_num)
theorem B525397 : Blo 463784 525397 := bbase (se 8 (by rfl) ⟨3078, by rfl⟩ : syracuseStep 525397 = 6157) (by norm_num)
theorem B787549 : Blo 463784 787549 := bbase (se 3 (by rfl) ⟨147665, by rfl⟩ : syracuseStep 787549 = 295331) (by norm_num)
theorem B525433 : Blo 463784 525433 := bbase (se 2 (by rfl) ⟨197037, by rfl⟩ : syracuseStep 525433 = 394075) (by norm_num)
theorem B1049741 : Blo 463784 1049741 := bbase (se 3 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 1049741 = 393653) (by norm_num)
theorem B885917 : Blo 463784 885917 := bbase (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) (by norm_num)
theorem B525469 : Blo 463784 525469 := bbase (se 3 (by rfl) ⟨98525, by rfl⟩ : syracuseStep 525469 = 197051) (by norm_num)
theorem B2360501 : Blo 463784 2360501 := bbase (se 5 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 2360501 = 221297) (by norm_num)
theorem B787637 : Blo 463784 787637 := bbase (se 5 (by rfl) ⟨36920, by rfl⟩ : syracuseStep 787637 = 73841) (by norm_num)
theorem B525505 : Blo 463784 525505 := bbase (se 2 (by rfl) ⟨197064, by rfl⟩ : syracuseStep 525505 = 394129) (by norm_num)
theorem B1049813 : Blo 463784 1049813 := bbase (se 7 (by rfl) ⟨12302, by rfl⟩ : syracuseStep 1049813 = 24605) (by norm_num)
theorem B591077 : Blo 463784 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B525541 : Blo 463784 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B525577 : Blo 463784 525577 := bbase (se 2 (by rfl) ⟨197091, by rfl⟩ : syracuseStep 525577 = 394183) (by norm_num)
theorem B1049885 : Blo 463784 1049885 := bbase (se 3 (by rfl) ⟨196853, by rfl⟩ : syracuseStep 1049885 = 393707) (by norm_num)
theorem B591133 : Blo 463784 591133 := bbase (se 3 (by rfl) ⟨110837, by rfl⟩ : syracuseStep 591133 = 221675) (by norm_num)
theorem B525613 : Blo 463784 525613 := bbase (se 3 (by rfl) ⟨98552, by rfl⟩ : syracuseStep 525613 = 197105) (by norm_num)
theorem B886069 : Blo 463784 886069 := bbase (se 5 (by rfl) ⟨41534, by rfl⟩ : syracuseStep 886069 = 83069) (by norm_num)
theorem B787765 : Blo 463784 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B525649 : Blo 463784 525649 := bbase (se 2 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 525649 = 394237) (by norm_num)
theorem B1049957 : Blo 463784 1049957 := bbase (se 4 (by rfl) ⟨98433, by rfl⟩ : syracuseStep 1049957 = 196867) (by norm_num)
theorem B1574261 : Blo 463784 1574261 := bbase (se 5 (by rfl) ⟨73793, by rfl⟩ : syracuseStep 1574261 = 147587) (by norm_num)
theorem B525685 : Blo 463784 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B591229 : Blo 463784 591229 := bbase (se 3 (by rfl) ⟨110855, by rfl⟩ : syracuseStep 591229 = 221711) (by norm_num)
theorem B787853 : Blo 463784 787853 := bbase (se 3 (by rfl) ⟨147722, by rfl⟩ : syracuseStep 787853 = 295445) (by norm_num)
theorem B525721 : Blo 463784 525721 := bbase (se 2 (by rfl) ⟨197145, by rfl⟩ : syracuseStep 525721 = 394291) (by norm_num)
theorem B1181101 : Blo 463784 1181101 := bbase (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) (by norm_num)
theorem B1050029 : Blo 463784 1050029 := bbase (se 3 (by rfl) ⟨196880, by rfl⟩ : syracuseStep 1050029 = 393761) (by norm_num)
theorem B525757 : Blo 463784 525757 := bbase (se 3 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 525757 = 197159) (by norm_num)
theorem B3179989 : Blo 463784 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B525793 : Blo 463784 525793 := bbase (se 2 (by rfl) ⟨197172, by rfl⟩ : syracuseStep 525793 = 394345) (by norm_num)
theorem B755173 : Blo 463784 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B1050101 : Blo 463784 1050101 := bbase (se 5 (by rfl) ⟨49223, by rfl⟩ : syracuseStep 1050101 = 98447) (by norm_num)
theorem B525829 : Blo 463784 525829 := bbase (se 4 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 525829 = 98593) (by norm_num)
theorem B787981 : Blo 463784 787981 := bbase (se 3 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 787981 = 295493) (by norm_num)
theorem B1181213 : Blo 463784 1181213 := bbase (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) (by norm_num)
theorem B591401 : Blo 463784 591401 := bbase (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) (by norm_num)
theorem B525865 : Blo 463784 525865 := bbase (se 2 (by rfl) ⟨197199, by rfl⟩ : syracuseStep 525865 = 394399) (by norm_num)
theorem B1050173 : Blo 463784 1050173 := bbase (se 3 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 1050173 = 393815) (by norm_num)
theorem B525901 : Blo 463784 525901 := bbase (se 3 (by rfl) ⟨98606, by rfl⟩ : syracuseStep 525901 = 197213) (by norm_num)
theorem B591457 : Blo 463784 591457 := bbase (se 2 (by rfl) ⟨221796, by rfl⟩ : syracuseStep 591457 = 443593) (by norm_num)
theorem B886373 : Blo 463784 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B788069 : Blo 463784 788069 := bbase (se 4 (by rfl) ⟨73881, by rfl⟩ : syracuseStep 788069 = 147763) (by norm_num)
theorem B525937 : Blo 463784 525937 := bbase (se 2 (by rfl) ⟨197226, by rfl⟩ : syracuseStep 525937 = 394453) (by norm_num)
theorem B1050245 : Blo 463784 1050245 := bbase (se 4 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 1050245 = 196921) (by norm_num)
theorem B525973 : Blo 463784 525973 := bbase (se 6 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 525973 = 24655) (by norm_num)
theorem B526009 : Blo 463784 526009 := bbase (se 2 (by rfl) ⟨197253, by rfl⟩ : syracuseStep 526009 = 394507) (by norm_num)
theorem B591553 : Blo 463784 591553 := bbase (se 2 (by rfl) ⟨221832, by rfl⟩ : syracuseStep 591553 = 443665) (by norm_num)
theorem B1050317 : Blo 463784 1050317 := bbase (se 3 (by rfl) ⟨196934, by rfl⟩ : syracuseStep 1050317 = 393869) (by norm_num)
theorem B1181405 : Blo 463784 1181405 := bbase (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) (by norm_num)
theorem B526045 : Blo 463784 526045 := bbase (se 3 (by rfl) ⟨98633, by rfl⟩ : syracuseStep 526045 = 197267) (by norm_num)
theorem B788197 : Blo 463784 788197 := bbase (se 4 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 788197 = 147787) (by norm_num)
theorem B526081 : Blo 463784 526081 := bbase (se 2 (by rfl) ⟨197280, by rfl⟩ : syracuseStep 526081 = 394561) (by norm_num)
theorem B5965589 : Blo 463784 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B1050389 : Blo 463784 1050389 := bbase (se 6 (by rfl) ⟨24618, by rfl⟩ : syracuseStep 1050389 = 49237) (by norm_num)
theorem B1574693 : Blo 463784 1574693 := bbase (se 4 (by rfl) ⟨147627, by rfl⟩ : syracuseStep 1574693 = 295255) (by norm_num)
theorem B526117 : Blo 463784 526117 := bbase (se 4 (by rfl) ⟨49323, by rfl⟩ : syracuseStep 526117 = 98647) (by norm_num)
theorem B788285 : Blo 463784 788285 := bbase (se 3 (by rfl) ⟨147803, by rfl⟩ : syracuseStep 788285 = 295607) (by norm_num)
theorem B526153 : Blo 463784 526153 := bbase (se 2 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 526153 = 394615) (by norm_num)
theorem B1509205 : Blo 463784 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B1050461 : Blo 463784 1050461 := bbase (se 3 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 1050461 = 393923) (by norm_num)
theorem B624493 : Blo 463784 624493 := bbase (se 3 (by rfl) ⟨117092, by rfl⟩ : syracuseStep 624493 = 234185) (by norm_num)
theorem B591725 : Blo 463784 591725 := bbase (se 3 (by rfl) ⟨110948, by rfl⟩ : syracuseStep 591725 = 221897) (by norm_num)
theorem B526189 : Blo 463784 526189 := bbase (se 3 (by rfl) ⟨98660, by rfl⟩ : syracuseStep 526189 = 197321) (by norm_num)
theorem B526225 : Blo 463784 526225 := bbase (se 2 (by rfl) ⟨197334, by rfl⟩ : syracuseStep 526225 = 394669) (by norm_num)
theorem B559001 : Blo 463784 559001 := bbase (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) (by norm_num)
theorem B1050533 : Blo 463784 1050533 := bbase (se 4 (by rfl) ⟨98487, by rfl⟩ : syracuseStep 1050533 = 196975) (by norm_num)
theorem B591781 : Blo 463784 591781 := bbase (se 4 (by rfl) ⟨55479, by rfl⟩ : syracuseStep 591781 = 110959) (by norm_num)
theorem B788413 : Blo 463784 788413 := bbase (se 3 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 788413 = 295655) (by norm_num)
theorem B1050605 : Blo 463784 1050605 := bbase (se 3 (by rfl) ⟨196988, by rfl⟩ : syracuseStep 1050605 = 393977) (by norm_num)
theorem B591877 : Blo 463784 591877 := bbase (se 4 (by rfl) ⟨55488, by rfl⟩ : syracuseStep 591877 = 110977) (by norm_num)
theorem B788501 : Blo 463784 788501 := bbase (se 6 (by rfl) ⟨18480, by rfl⟩ : syracuseStep 788501 = 36961) (by norm_num)
theorem B2066485 : Blo 463784 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1181749 : Blo 463784 1181749 := bbase (se 5 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 1181749 = 110789) (by norm_num)
theorem B1050677 : Blo 463784 1050677 := bbase (se 5 (by rfl) ⟨49250, by rfl⟩ : syracuseStep 1050677 = 98501) (by norm_num)
theorem B1050749 : Blo 463784 1050749 := bbase (se 3 (by rfl) ⟨197015, by rfl⟩ : syracuseStep 1050749 = 394031) (by norm_num)
theorem B788629 : Blo 463784 788629 := bbase (se 6 (by rfl) ⟨18483, by rfl⟩ : syracuseStep 788629 = 36967) (by norm_num)
theorem B1181861 : Blo 463784 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B1050821 : Blo 463784 1050821 := bbase (se 4 (by rfl) ⟨98514, by rfl⟩ : syracuseStep 1050821 = 197029) (by norm_num)
theorem B1575125 : Blo 463784 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B788717 : Blo 463784 788717 := bbase (se 3 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 788717 = 295769) (by norm_num)
theorem B1050893 : Blo 463784 1050893 := bbase (se 3 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 1050893 = 394085) (by norm_num)
theorem B1050965 : Blo 463784 1050965 := bbase (se 10 (by rfl) ⟨1539, by rfl⟩ : syracuseStep 1050965 = 3079) (by norm_num)
theorem B887125 : Blo 463784 887125 := bbase (se 10 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 887125 = 2599) (by norm_num)
theorem B1182053 : Blo 463784 1182053 := bbase (se 4 (by rfl) ⟨110817, by rfl⟩ : syracuseStep 1182053 = 221635) (by norm_num)
theorem B788845 : Blo 463784 788845 := bbase (se 3 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 788845 = 295817) (by norm_num)
theorem B559505 : Blo 463784 559505 := bbase (se 2 (by rfl) ⟨209814, by rfl⟩ : syracuseStep 559505 = 419629) (by norm_num)
theorem B1051037 : Blo 463784 1051037 := bbase (se 3 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 1051037 = 394139) (by norm_num)
theorem B559553 : Blo 463784 559553 := bbase (se 2 (by rfl) ⟨209832, by rfl⟩ : syracuseStep 559553 = 419665) (by norm_num)
theorem B2361797 : Blo 463784 2361797 := bbase (se 4 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 2361797 = 442837) (by norm_num)
theorem B788933 : Blo 463784 788933 := bbase (se 4 (by rfl) ⟨73962, by rfl⟩ : syracuseStep 788933 = 147925) (by norm_num)
theorem B1051109 : Blo 463784 1051109 := bbase (se 4 (by rfl) ⟨98541, by rfl⟩ : syracuseStep 1051109 = 197083) (by norm_num)
theorem B887269 : Blo 463784 887269 := bbase (se 4 (by rfl) ⟨83181, by rfl⟩ : syracuseStep 887269 = 166363) (by norm_num)
theorem B1051181 : Blo 463784 1051181 := bbase (se 3 (by rfl) ⟨197096, by rfl⟩ : syracuseStep 1051181 = 394193) (by norm_num)
theorem B789061 : Blo 463784 789061 := bbase (se 4 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 789061 = 147949) (by norm_num)
theorem B1051253 : Blo 463784 1051253 := bbase (se 5 (by rfl) ⟨49277, by rfl⟩ : syracuseStep 1051253 = 98555) (by norm_num)
theorem B1575557 : Blo 463784 1575557 := bbase (se 4 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 1575557 = 295417) (by norm_num)
theorem B887429 : Blo 463784 887429 := bbase (se 4 (by rfl) ⟨83196, by rfl⟩ : syracuseStep 887429 = 166393) (by norm_num)
theorem B789149 : Blo 463784 789149 := bbase (se 3 (by rfl) ⟨147965, by rfl⟩ : syracuseStep 789149 = 295931) (by norm_num)
theorem B1182397 : Blo 463784 1182397 := bbase (se 3 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 1182397 = 443399) (by norm_num)
theorem B1051325 : Blo 463784 1051325 := bbase (se 3 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 1051325 = 394247) (by norm_num)
theorem B559813 : Blo 463784 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B1051397 : Blo 463784 1051397 := bbase (se 4 (by rfl) ⟨98568, by rfl⟩ : syracuseStep 1051397 = 197137) (by norm_num)
theorem B887573 : Blo 463784 887573 := bbase (se 6 (by rfl) ⟨20802, by rfl⟩ : syracuseStep 887573 = 41605) (by norm_num)
theorem B789277 : Blo 463784 789277 := bbase (se 3 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 789277 = 295979) (by norm_num)
theorem B1182509 : Blo 463784 1182509 := bbase (se 3 (by rfl) ⟨221720, by rfl⟩ : syracuseStep 1182509 = 443441) (by norm_num)
theorem B1051469 : Blo 463784 1051469 := bbase (se 3 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 1051469 = 394301) (by norm_num)
theorem B2132837 : Blo 463784 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B789365 : Blo 463784 789365 := bbase (se 5 (by rfl) ⟨37001, by rfl⟩ : syracuseStep 789365 = 74003) (by norm_num)
theorem B1051541 : Blo 463784 1051541 := bbase (se 6 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 1051541 = 49291) (by norm_num)
theorem B560077 : Blo 463784 560077 := bbase (se 3 (by rfl) ⟨105014, by rfl⟩ : syracuseStep 560077 = 210029) (by norm_num)
theorem B1051613 : Blo 463784 1051613 := bbase (se 3 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 1051613 = 394355) (by norm_num)
theorem B1117165 : Blo 463784 1117165 := bbase (se 3 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 1117165 = 418937) (by norm_num)
theorem B1182701 : Blo 463784 1182701 := bbase (se 3 (by rfl) ⟨221756, by rfl⟩ : syracuseStep 1182701 = 443513) (by norm_num)
theorem B1772549 : Blo 463784 1772549 := bbase (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) (by norm_num)
theorem B2231333 : Blo 463784 2231333 := bbase (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) (by norm_num)
theorem B1051685 : Blo 463784 1051685 := bbase (se 4 (by rfl) ⟨98595, by rfl⟩ : syracuseStep 1051685 = 197191) (by norm_num)
theorem B1575989 : Blo 463784 1575989 := bbase (se 5 (by rfl) ⟨73874, by rfl⟩ : syracuseStep 1575989 = 147749) (by norm_num)
theorem B887861 : Blo 463784 887861 := bbase (se 5 (by rfl) ⟨41618, by rfl⟩ : syracuseStep 887861 = 83237) (by norm_num)
theorem B560197 : Blo 463784 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B1117261 : Blo 463784 1117261 := bbase (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) (by norm_num)
theorem B2821205 : Blo 463784 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B1051757 : Blo 463784 1051757 := bbase (se 3 (by rfl) ⟨197204, by rfl⟩ : syracuseStep 1051757 = 394409) (by norm_num)
theorem B1051829 : Blo 463784 1051829 := bbase (se 5 (by rfl) ⟨49304, by rfl⟩ : syracuseStep 1051829 = 98609) (by norm_num)
theorem B888013 : Blo 463784 888013 := bbase (se 3 (by rfl) ⟨166502, by rfl⟩ : syracuseStep 888013 = 333005) (by norm_num)
theorem B1051901 : Blo 463784 1051901 := bbase (se 3 (by rfl) ⟨197231, by rfl⟩ : syracuseStep 1051901 = 394463) (by norm_num)
theorem B1772837 : Blo 463784 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B1183045 : Blo 463784 1183045 := bbase (se 4 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 1183045 = 221821) (by norm_num)
theorem B1051973 : Blo 463784 1051973 := bbase (se 4 (by rfl) ⟨98622, by rfl⟩ : syracuseStep 1051973 = 197245) (by norm_num)
theorem B1052045 : Blo 463784 1052045 := bbase (se 3 (by rfl) ⟨197258, by rfl⟩ : syracuseStep 1052045 = 394517) (by norm_num)
theorem B3542453 : Blo 463784 3542453 := bbase (se 5 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 3542453 = 332105) (by norm_num)
theorem B1183157 : Blo 463784 1183157 := bbase (se 5 (by rfl) ⟨55460, by rfl⟩ : syracuseStep 1183157 = 110921) (by norm_num)
theorem B1052117 : Blo 463784 1052117 := bbase (se 7 (by rfl) ⟨12329, by rfl⟩ : syracuseStep 1052117 = 24659) (by norm_num)
theorem B1576421 : Blo 463784 1576421 := bbase (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) (by norm_num)
theorem B2985461 : Blo 463784 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B1052189 : Blo 463784 1052189 := bbase (se 3 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 1052189 = 394571) (by norm_num)
theorem B1052261 : Blo 463784 1052261 := bbase (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) (by norm_num)
theorem B1183349 : Blo 463784 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B1052333 : Blo 463784 1052333 := bbase (se 3 (by rfl) ⟨197312, by rfl⟩ : syracuseStep 1052333 = 394625) (by norm_num)
theorem B2363093 : Blo 463784 2363093 := bbase (se 7 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 2363093 = 55385) (by norm_num)
theorem B1052405 : Blo 463784 1052405 := bbase (se 5 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 1052405 = 98663) (by norm_num)
theorem B1052477 : Blo 463784 1052477 := bbase (se 3 (by rfl) ⟨197339, by rfl⟩ : syracuseStep 1052477 = 394679) (by norm_num)
theorem B495433 : Blo 463784 495433 := bbase (se 2 (by rfl) ⟨185787, by rfl⟩ : syracuseStep 495433 = 371575) (by norm_num)
theorem B1576853 : Blo 463784 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B561053 : Blo 463784 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B1183693 : Blo 463784 1183693 := bbase (se 3 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 1183693 = 443885) (by norm_num)
theorem B1183805 : Blo 463784 1183805 := bbase (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) (by norm_num)
theorem B1118357 : Blo 463784 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B3969269 : Blo 463784 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B1183997 : Blo 463784 1183997 := bbase (se 3 (by rfl) ⟨221999, by rfl⟩ : syracuseStep 1183997 = 443999) (by norm_num)
theorem B495877 : Blo 463784 495877 := bbase (se 4 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 495877 = 92977) (by norm_num)
theorem B1577285 : Blo 463784 1577285 := bbase (se 4 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 1577285 = 295741) (by norm_num)
theorem B2232677 : Blo 463784 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B496001 : Blo 463784 496001 := bbase (se 2 (by rfl) ⟨186000, by rfl⟩ : syracuseStep 496001 = 372001) (by norm_num)
theorem B1774021 : Blo 463784 1774021 := bbase (se 4 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 1774021 = 332629) (by norm_num)
theorem B561773 : Blo 463784 561773 := bbase (se 3 (by rfl) ⟨105332, by rfl⟩ : syracuseStep 561773 = 210665) (by norm_num)
theorem B496253 : Blo 463784 496253 := bbase (se 3 (by rfl) ⟨93047, by rfl⟩ : syracuseStep 496253 = 186095) (by norm_num)
theorem B1774325 : Blo 463784 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B1577717 : Blo 463784 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B529301 : Blo 463784 529301 := bbase (se 6 (by rfl) ⟨12405, by rfl⟩ : syracuseStep 529301 = 24811) (by norm_num)
theorem B2364389 : Blo 463784 2364389 := bbase (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) (by norm_num)
theorem B660469 : Blo 463784 660469 := bbase (se 5 (by rfl) ⟨30959, by rfl⟩ : syracuseStep 660469 = 61919) (by norm_num)
theorem B496697 : Blo 463784 496697 := bbase (se 2 (by rfl) ⟨186261, by rfl⟩ : syracuseStep 496697 = 372523) (by norm_num)
theorem B660565 : Blo 463784 660565 := bbase (se 8 (by rfl) ⟨3870, by rfl⟩ : syracuseStep 660565 = 7741) (by norm_num)
theorem B1119317 : Blo 463784 1119317 := bbase (se 8 (by rfl) ⟨6558, by rfl⟩ : syracuseStep 1119317 = 13117) (by norm_num)
theorem B1578149 : Blo 463784 1578149 := bbase (se 4 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 1578149 = 295903) (by norm_num)
theorem B955685 : Blo 463784 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B496945 : Blo 463784 496945 := bbase (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) (by norm_num)
theorem B5019029 : Blo 463784 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B595397 : Blo 463784 595397 := bbase (se 4 (by rfl) ⟨55818, by rfl⟩ : syracuseStep 595397 = 111637) (by norm_num)
theorem B661061 : Blo 463784 661061 := bbase (se 4 (by rfl) ⟨61974, by rfl⟩ : syracuseStep 661061 = 123949) (by norm_num)
theorem B1578581 : Blo 463784 1578581 := bbase (se 8 (by rfl) ⟨9249, by rfl⟩ : syracuseStep 1578581 = 18499) (by norm_num)
theorem B497389 : Blo 463784 497389 := bbase (se 3 (by rfl) ⟨93260, by rfl⟩ : syracuseStep 497389 = 186521) (by norm_num)
theorem B497449 : Blo 463784 497449 := bbase (se 2 (by rfl) ⟨186543, by rfl⟩ : syracuseStep 497449 = 373087) (by norm_num)
theorem B595817 : Blo 463784 595817 := bbase (se 2 (by rfl) ⟨223431, by rfl⟩ : syracuseStep 595817 = 446863) (by norm_num)
theorem B1513333 : Blo 463784 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B9050069 : Blo 463784 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B530401 : Blo 463784 530401 := bbase (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) (by norm_num)
theorem B497765 : Blo 463784 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B661613 : Blo 463784 661613 := bbase (se 3 (by rfl) ⟨124052, by rfl⟩ : syracuseStep 661613 = 248105) (by norm_num)
theorem B2365685 : Blo 463784 2365685 := bbase (se 5 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 2365685 = 221783) (by norm_num)
theorem B498209 : Blo 463784 498209 := bbase (se 2 (by rfl) ⟨186828, by rfl⟩ : syracuseStep 498209 = 373657) (by norm_num)
theorem B498269 : Blo 463784 498269 := bbase (se 3 (by rfl) ⟨93425, by rfl⟩ : syracuseStep 498269 = 186851) (by norm_num)
theorem B1677925 : Blo 463784 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B11901653 : Blo 463784 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B498397 : Blo 463784 498397 := bbase (se 3 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 498397 = 186899) (by norm_num)
theorem B1121077 : Blo 463784 1121077 := bbase (se 5 (by rfl) ⟨52550, by rfl⟩ : syracuseStep 1121077 = 105101) (by norm_num)
theorem B1416005 : Blo 463784 1416005 := bbase (se 4 (by rfl) ⟨132750, by rfl⟩ : syracuseStep 1416005 = 265501) (by norm_num)
theorem B662365 : Blo 463784 662365 := bbase (se 3 (by rfl) ⟨124193, by rfl⟩ : syracuseStep 662365 = 248387) (by norm_num)
theorem B629741 : Blo 463784 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B1121309 : Blo 463784 1121309 := bbase (se 3 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 1121309 = 420491) (by norm_num)
theorem B498841 : Blo 463784 498841 := bbase (se 2 (by rfl) ⟨187065, by rfl⟩ : syracuseStep 498841 = 374131) (by norm_num)
theorem B498961 : Blo 463784 498961 := bbase (se 2 (by rfl) ⟨187110, by rfl⟩ : syracuseStep 498961 = 374221) (by norm_num)
theorem B695693 : Blo 463784 695693 := bbase (se 3 (by rfl) ⟨130442, by rfl⟩ : syracuseStep 695693 = 260885) (by norm_num)
theorem B695717 : Blo 463784 695717 := bbase (se 4 (by rfl) ⟨65223, by rfl⟩ : syracuseStep 695717 = 130447) (by norm_num)
theorem B1121701 : Blo 463784 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B695741 : Blo 463784 695741 := bbase (se 3 (by rfl) ⟨130451, by rfl⟩ : syracuseStep 695741 = 260903) (by norm_num)
theorem B695765 : Blo 463784 695765 := bbase (se 7 (by rfl) ⟨8153, by rfl⟩ : syracuseStep 695765 = 16307) (by norm_num)
theorem B990677 : Blo 463784 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B695789 : Blo 463784 695789 := bbase (se 3 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 695789 = 260921) (by norm_num)
theorem B695813 : Blo 463784 695813 := bbase (se 4 (by rfl) ⟨65232, by rfl⟩ : syracuseStep 695813 = 130465) (by norm_num)
theorem B2366981 : Blo 463784 2366981 := bbase (se 4 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 2366981 = 443809) (by norm_num)
theorem B499213 : Blo 463784 499213 := bbase (se 3 (by rfl) ⟨93602, by rfl⟩ : syracuseStep 499213 = 187205) (by norm_num)
theorem B499217 : Blo 463784 499217 := bbase (se 2 (by rfl) ⟨187206, by rfl⟩ : syracuseStep 499217 = 374413) (by norm_num)
theorem B695837 : Blo 463784 695837 := bbase (se 3 (by rfl) ⟨130469, by rfl⟩ : syracuseStep 695837 = 260939) (by norm_num)
theorem B695861 : Blo 463784 695861 := bbase (se 5 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 695861 = 65237) (by norm_num)
theorem B695885 : Blo 463784 695885 := bbase (se 3 (by rfl) ⟨130478, by rfl⟩ : syracuseStep 695885 = 260957) (by norm_num)
theorem B695909 : Blo 463784 695909 := bbase (se 4 (by rfl) ⟨65241, by rfl⟩ : syracuseStep 695909 = 130483) (by norm_num)
theorem B663157 : Blo 463784 663157 := bbase (se 5 (by rfl) ⟨31085, by rfl⟩ : syracuseStep 663157 = 62171) (by norm_num)
theorem B695933 : Blo 463784 695933 := bbase (se 3 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 695933 = 260975) (by norm_num)
theorem B695957 : Blo 463784 695957 := bbase (se 6 (by rfl) ⟨16311, by rfl⟩ : syracuseStep 695957 = 32623) (by norm_num)
theorem B532133 : Blo 463784 532133 := bbase (se 4 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 532133 = 99775) (by norm_num)
theorem B695981 : Blo 463784 695981 := bbase (se 3 (by rfl) ⟨130496, by rfl⟩ : syracuseStep 695981 = 260993) (by norm_num)
theorem B564913 : Blo 463784 564913 := bbase (se 2 (by rfl) ⟨211842, by rfl⟩ : syracuseStep 564913 = 423685) (by norm_num)
theorem B696005 : Blo 463784 696005 := bbase (se 4 (by rfl) ⟨65250, by rfl⟩ : syracuseStep 696005 = 130501) (by norm_num)
theorem B696029 : Blo 463784 696029 := bbase (se 3 (by rfl) ⟨130505, by rfl⟩ : syracuseStep 696029 = 261011) (by norm_num)
theorem B696053 : Blo 463784 696053 := bbase (se 5 (by rfl) ⟨32627, by rfl⟩ : syracuseStep 696053 = 65255) (by norm_num)
theorem B1679093 : Blo 463784 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B696077 : Blo 463784 696077 := bbase (se 3 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 696077 = 261029) (by norm_num)
theorem B696101 : Blo 463784 696101 := bbase (se 4 (by rfl) ⟨65259, by rfl⟩ : syracuseStep 696101 = 130519) (by norm_num)
theorem B696125 : Blo 463784 696125 := bbase (se 3 (by rfl) ⟨130523, by rfl⟩ : syracuseStep 696125 = 261047) (by norm_num)
theorem B991045 : Blo 463784 991045 := bbase (se 4 (by rfl) ⟨92910, by rfl⟩ : syracuseStep 991045 = 185821) (by norm_num)
theorem B696149 : Blo 463784 696149 := bbase (se 9 (by rfl) ⟨2039, by rfl⟩ : syracuseStep 696149 = 4079) (by norm_num)
theorem B696173 : Blo 463784 696173 := bbase (se 3 (by rfl) ⟨130532, by rfl⟩ : syracuseStep 696173 = 261065) (by norm_num)
theorem B696197 : Blo 463784 696197 := bbase (se 4 (by rfl) ⟨65268, by rfl⟩ : syracuseStep 696197 = 130537) (by norm_num)
theorem B696221 : Blo 463784 696221 := bbase (se 3 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 696221 = 261083) (by norm_num)
theorem B696245 : Blo 463784 696245 := bbase (se 5 (by rfl) ⟨32636, by rfl⟩ : syracuseStep 696245 = 65273) (by norm_num)
theorem B663493 : Blo 463784 663493 := bbase (se 4 (by rfl) ⟨62202, by rfl⟩ : syracuseStep 663493 = 124405) (by norm_num)
theorem B696269 : Blo 463784 696269 := bbase (se 3 (by rfl) ⟨130550, by rfl⟩ : syracuseStep 696269 = 261101) (by norm_num)
theorem B696293 : Blo 463784 696293 := bbase (se 4 (by rfl) ⟨65277, by rfl⟩ : syracuseStep 696293 = 130555) (by norm_num)
theorem B2236405 : Blo 463784 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B2400245 : Blo 463784 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B696317 : Blo 463784 696317 := bbase (se 3 (by rfl) ⟨130559, by rfl⟩ : syracuseStep 696317 = 261119) (by norm_num)
theorem B696341 : Blo 463784 696341 := bbase (se 6 (by rfl) ⟨16320, by rfl⟩ : syracuseStep 696341 = 32641) (by norm_num)
theorem B892957 : Blo 463784 892957 := bbase (se 3 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 892957 = 334859) (by norm_num)
theorem B696365 : Blo 463784 696365 := bbase (se 3 (by rfl) ⟨130568, by rfl⟩ : syracuseStep 696365 = 261137) (by norm_num)
theorem B696389 : Blo 463784 696389 := bbase (se 4 (by rfl) ⟨65286, by rfl⟩ : syracuseStep 696389 = 130573) (by norm_num)
theorem B696413 : Blo 463784 696413 := bbase (se 3 (by rfl) ⟨130577, by rfl⟩ : syracuseStep 696413 = 261155) (by norm_num)
theorem B532585 : Blo 463784 532585 := bbase (se 2 (by rfl) ⟨199719, by rfl⟩ : syracuseStep 532585 = 399439) (by norm_num)
theorem B696437 : Blo 463784 696437 := bbase (se 5 (by rfl) ⟨32645, by rfl⟩ : syracuseStep 696437 = 65291) (by norm_num)
theorem B696461 : Blo 463784 696461 := bbase (se 3 (by rfl) ⟨130586, by rfl⟩ : syracuseStep 696461 = 261173) (by norm_num)
theorem B663709 : Blo 463784 663709 := bbase (se 3 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 663709 = 248891) (by norm_num)
theorem B696485 : Blo 463784 696485 := bbase (se 4 (by rfl) ⟨65295, by rfl⟩ : syracuseStep 696485 = 130591) (by norm_num)
theorem B696509 : Blo 463784 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B696533 : Blo 463784 696533 := bbase (se 7 (by rfl) ⟨8162, by rfl⟩ : syracuseStep 696533 = 16325) (by norm_num)
theorem B696557 : Blo 463784 696557 := bbase (se 3 (by rfl) ⟨130604, by rfl⟩ : syracuseStep 696557 = 261209) (by norm_num)
theorem B598261 : Blo 463784 598261 := bbase (se 5 (by rfl) ⟨28043, by rfl⟩ : syracuseStep 598261 = 56087) (by norm_num)
theorem B696581 : Blo 463784 696581 := bbase (se 4 (by rfl) ⟨65304, by rfl⟩ : syracuseStep 696581 = 130609) (by norm_num)
theorem B696605 : Blo 463784 696605 := bbase (se 3 (by rfl) ⟨130613, by rfl⟩ : syracuseStep 696605 = 261227) (by norm_num)
theorem B696629 : Blo 463784 696629 := bbase (se 5 (by rfl) ⟨32654, by rfl⟩ : syracuseStep 696629 = 65309) (by norm_num)
theorem B696653 : Blo 463784 696653 := bbase (se 3 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 696653 = 261245) (by norm_num)
theorem B696677 : Blo 463784 696677 := bbase (se 4 (by rfl) ⟨65313, by rfl⟩ : syracuseStep 696677 = 130627) (by norm_num)
theorem B696701 : Blo 463784 696701 := bbase (se 3 (by rfl) ⟨130631, by rfl⟩ : syracuseStep 696701 = 261263) (by norm_num)
theorem B696725 : Blo 463784 696725 := bbase (se 6 (by rfl) ⟨16329, by rfl⟩ : syracuseStep 696725 = 32659) (by norm_num)
theorem B696749 : Blo 463784 696749 := bbase (se 3 (by rfl) ⟨130640, by rfl⟩ : syracuseStep 696749 = 261281) (by norm_num)
theorem B696773 : Blo 463784 696773 := bbase (se 4 (by rfl) ⟨65322, by rfl⟩ : syracuseStep 696773 = 130645) (by norm_num)
theorem B696797 : Blo 463784 696797 := bbase (se 3 (by rfl) ⟨130649, by rfl⟩ : syracuseStep 696797 = 261299) (by norm_num)
theorem B1122797 : Blo 463784 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B696821 : Blo 463784 696821 := bbase (se 5 (by rfl) ⟨32663, by rfl⟩ : syracuseStep 696821 = 65327) (by norm_num)
theorem B2662901 : Blo 463784 2662901 := bbase (se 5 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 2662901 = 249647) (by norm_num)
theorem B696845 : Blo 463784 696845 := bbase (se 3 (by rfl) ⟨130658, by rfl⟩ : syracuseStep 696845 = 261317) (by norm_num)
theorem B664085 : Blo 463784 664085 := bbase (se 6 (by rfl) ⟨15564, by rfl⟩ : syracuseStep 664085 = 31129) (by norm_num)
theorem B696869 : Blo 463784 696869 := bbase (se 4 (by rfl) ⟨65331, by rfl⟩ : syracuseStep 696869 = 130663) (by norm_num)
theorem B696893 : Blo 463784 696893 := bbase (se 3 (by rfl) ⟨130667, by rfl⟩ : syracuseStep 696893 = 261335) (by norm_num)
theorem B696917 : Blo 463784 696917 := bbase (se 8 (by rfl) ⟨4083, by rfl⟩ : syracuseStep 696917 = 8167) (by norm_num)
theorem B696941 : Blo 463784 696941 := bbase (se 3 (by rfl) ⟨130676, by rfl⟩ : syracuseStep 696941 = 261353) (by norm_num)
theorem B696965 : Blo 463784 696965 := bbase (se 4 (by rfl) ⟨65340, by rfl⟩ : syracuseStep 696965 = 130681) (by norm_num)
theorem B696989 : Blo 463784 696989 := bbase (se 3 (by rfl) ⟨130685, by rfl⟩ : syracuseStep 696989 = 261371) (by norm_num)
theorem B697013 : Blo 463784 697013 := bbase (se 5 (by rfl) ⟨32672, by rfl⟩ : syracuseStep 697013 = 65345) (by norm_num)
theorem B697037 : Blo 463784 697037 := bbase (se 3 (by rfl) ⟨130694, by rfl⟩ : syracuseStep 697037 = 261389) (by norm_num)
theorem B697061 : Blo 463784 697061 := bbase (se 4 (by rfl) ⟨65349, by rfl⟩ : syracuseStep 697061 = 130699) (by norm_num)
theorem B697085 : Blo 463784 697085 := bbase (se 3 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 697085 = 261407) (by norm_num)
theorem B1123085 : Blo 463784 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B697109 : Blo 463784 697109 := bbase (se 6 (by rfl) ⟨16338, by rfl⟩ : syracuseStep 697109 = 32677) (by norm_num)
theorem B697133 : Blo 463784 697133 := bbase (se 3 (by rfl) ⟨130712, by rfl⟩ : syracuseStep 697133 = 261425) (by norm_num)
theorem B697157 : Blo 463784 697157 := bbase (se 4 (by rfl) ⟨65358, by rfl⟩ : syracuseStep 697157 = 130717) (by norm_num)
theorem B697181 : Blo 463784 697181 := bbase (se 3 (by rfl) ⟨130721, by rfl⟩ : syracuseStep 697181 = 261443) (by norm_num)
theorem B697205 : Blo 463784 697205 := bbase (se 5 (by rfl) ⟨32681, by rfl⟩ : syracuseStep 697205 = 65363) (by norm_num)
theorem B697229 : Blo 463784 697229 := bbase (se 3 (by rfl) ⟨130730, by rfl⟩ : syracuseStep 697229 = 261461) (by norm_num)
theorem B697253 : Blo 463784 697253 := bbase (se 4 (by rfl) ⟨65367, by rfl⟩ : syracuseStep 697253 = 130735) (by norm_num)
theorem B1254325 : Blo 463784 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B697277 : Blo 463784 697277 := bbase (se 3 (by rfl) ⟨130739, by rfl⟩ : syracuseStep 697277 = 261479) (by norm_num)
theorem B631757 : Blo 463784 631757 := bbase (se 3 (by rfl) ⟨118454, by rfl⟩ : syracuseStep 631757 = 236909) (by norm_num)
theorem B697301 : Blo 463784 697301 := bbase (se 7 (by rfl) ⟨8171, by rfl⟩ : syracuseStep 697301 = 16343) (by norm_num)
theorem B697325 : Blo 463784 697325 := bbase (se 3 (by rfl) ⟨130748, by rfl⟩ : syracuseStep 697325 = 261497) (by norm_num)
theorem B697349 : Blo 463784 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B697373 : Blo 463784 697373 := bbase (se 3 (by rfl) ⟨130757, by rfl⟩ : syracuseStep 697373 = 261515) (by norm_num)
theorem B697397 : Blo 463784 697397 := bbase (se 5 (by rfl) ⟨32690, by rfl⟩ : syracuseStep 697397 = 65381) (by norm_num)
theorem B697421 : Blo 463784 697421 := bbase (se 3 (by rfl) ⟨130766, by rfl⟩ : syracuseStep 697421 = 261533) (by norm_num)
theorem B697445 : Blo 463784 697445 := bbase (se 4 (by rfl) ⟨65385, by rfl⟩ : syracuseStep 697445 = 130771) (by norm_num)
theorem B697469 : Blo 463784 697469 := bbase (se 3 (by rfl) ⟨130775, by rfl⟩ : syracuseStep 697469 = 261551) (by norm_num)
theorem B697493 : Blo 463784 697493 := bbase (se 6 (by rfl) ⟨16347, by rfl⟩ : syracuseStep 697493 = 32695) (by norm_num)
theorem B697517 : Blo 463784 697517 := bbase (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) (by norm_num)
theorem B697541 : Blo 463784 697541 := bbase (se 4 (by rfl) ⟨65394, by rfl⟩ : syracuseStep 697541 = 130789) (by norm_num)
theorem B697565 : Blo 463784 697565 := bbase (se 3 (by rfl) ⟨130793, by rfl⟩ : syracuseStep 697565 = 261587) (by norm_num)
theorem B697589 : Blo 463784 697589 := bbase (se 5 (by rfl) ⟨32699, by rfl⟩ : syracuseStep 697589 = 65399) (by norm_num)
theorem B697613 : Blo 463784 697613 := bbase (se 3 (by rfl) ⟨130802, by rfl⟩ : syracuseStep 697613 = 261605) (by norm_num)
theorem B992549 : Blo 463784 992549 := bbase (se 4 (by rfl) ⟨93051, by rfl⟩ : syracuseStep 992549 = 186103) (by norm_num)
theorem B697637 : Blo 463784 697637 := bbase (se 4 (by rfl) ⟨65403, by rfl⟩ : syracuseStep 697637 = 130807) (by norm_num)
theorem B697661 : Blo 463784 697661 := bbase (se 3 (by rfl) ⟨130811, by rfl⟩ : syracuseStep 697661 = 261623) (by norm_num)
theorem B697685 : Blo 463784 697685 := bbase (se 12 (by rfl) ⟨255, by rfl⟩ : syracuseStep 697685 = 511) (by norm_num)
theorem B697709 : Blo 463784 697709 := bbase (se 3 (by rfl) ⟨130820, by rfl⟩ : syracuseStep 697709 = 261641) (by norm_num)
theorem B599405 : Blo 463784 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B697733 : Blo 463784 697733 := bbase (se 4 (by rfl) ⟨65412, by rfl⟩ : syracuseStep 697733 = 130825) (by norm_num)
theorem B697757 : Blo 463784 697757 := bbase (se 3 (by rfl) ⟨130829, by rfl⟩ : syracuseStep 697757 = 261659) (by norm_num)
theorem B992693 : Blo 463784 992693 := bbase (se 5 (by rfl) ⟨46532, by rfl⟩ : syracuseStep 992693 = 93065) (by norm_num)
theorem B697781 : Blo 463784 697781 := bbase (se 5 (by rfl) ⟨32708, by rfl⟩ : syracuseStep 697781 = 65417) (by norm_num)
theorem B697805 : Blo 463784 697805 := bbase (se 3 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 697805 = 261677) (by norm_num)
theorem B697829 : Blo 463784 697829 := bbase (se 4 (by rfl) ⟨65421, by rfl⟩ : syracuseStep 697829 = 130843) (by norm_num)
theorem B697853 : Blo 463784 697853 := bbase (se 3 (by rfl) ⟨130847, by rfl⟩ : syracuseStep 697853 = 261695) (by norm_num)
theorem B697877 : Blo 463784 697877 := bbase (se 6 (by rfl) ⟨16356, by rfl⟩ : syracuseStep 697877 = 32713) (by norm_num)
theorem B697901 : Blo 463784 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B697925 : Blo 463784 697925 := bbase (se 4 (by rfl) ⟨65430, by rfl⟩ : syracuseStep 697925 = 130861) (by norm_num)
theorem B697949 : Blo 463784 697949 := bbase (se 3 (by rfl) ⟨130865, by rfl⟩ : syracuseStep 697949 = 261731) (by norm_num)
theorem B697973 : Blo 463784 697973 := bbase (se 5 (by rfl) ⟨32717, by rfl⟩ : syracuseStep 697973 = 65435) (by norm_num)
theorem B697997 : Blo 463784 697997 := bbase (se 3 (by rfl) ⟨130874, by rfl⟩ : syracuseStep 697997 = 261749) (by norm_num)
theorem B698021 : Blo 463784 698021 := bbase (se 4 (by rfl) ⟨65439, by rfl⟩ : syracuseStep 698021 = 130879) (by norm_num)
theorem B698045 : Blo 463784 698045 := bbase (se 3 (by rfl) ⟨130883, by rfl⟩ : syracuseStep 698045 = 261767) (by norm_num)
theorem B698069 : Blo 463784 698069 := bbase (se 7 (by rfl) ⟨8180, by rfl⟩ : syracuseStep 698069 = 16361) (by norm_num)
theorem B7186133 : Blo 463784 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B698093 : Blo 463784 698093 := bbase (se 3 (by rfl) ⟨130892, by rfl⟩ : syracuseStep 698093 = 261785) (by norm_num)
theorem B698117 : Blo 463784 698117 := bbase (se 4 (by rfl) ⟨65448, by rfl⟩ : syracuseStep 698117 = 130897) (by norm_num)
theorem B993053 : Blo 463784 993053 := bbase (se 3 (by rfl) ⟨186197, by rfl⟩ : syracuseStep 993053 = 372395) (by norm_num)
theorem B698141 : Blo 463784 698141 := bbase (se 3 (by rfl) ⟨130901, by rfl⟩ : syracuseStep 698141 = 261803) (by norm_num)
theorem B698165 : Blo 463784 698165 := bbase (se 5 (by rfl) ⟨32726, by rfl⟩ : syracuseStep 698165 = 65453) (by norm_num)
theorem B894797 : Blo 463784 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B698189 : Blo 463784 698189 := bbase (se 3 (by rfl) ⟨130910, by rfl⟩ : syracuseStep 698189 = 261821) (by norm_num)
theorem B698213 : Blo 463784 698213 := bbase (se 4 (by rfl) ⟨65457, by rfl⟩ : syracuseStep 698213 = 130915) (by norm_num)
theorem B698237 : Blo 463784 698237 := bbase (se 3 (by rfl) ⟨130919, by rfl⟩ : syracuseStep 698237 = 261839) (by norm_num)
theorem B698261 : Blo 463784 698261 := bbase (se 6 (by rfl) ⟨16365, by rfl⟩ : syracuseStep 698261 = 32731) (by norm_num)
theorem B665509 : Blo 463784 665509 := bbase (se 4 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 665509 = 124783) (by norm_num)
theorem B698285 : Blo 463784 698285 := bbase (se 3 (by rfl) ⟨130928, by rfl⟩ : syracuseStep 698285 = 261857) (by norm_num)
theorem B698309 : Blo 463784 698309 := bbase (se 4 (by rfl) ⟨65466, by rfl⟩ : syracuseStep 698309 = 130933) (by norm_num)
theorem B698333 : Blo 463784 698333 := bbase (se 3 (by rfl) ⟨130937, by rfl⟩ : syracuseStep 698333 = 261875) (by norm_num)
theorem B698357 : Blo 463784 698357 := bbase (se 5 (by rfl) ⟨32735, by rfl⟩ : syracuseStep 698357 = 65471) (by norm_num)
theorem B698381 : Blo 463784 698381 := bbase (se 3 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 698381 = 261893) (by norm_num)
theorem B698405 : Blo 463784 698405 := bbase (se 4 (by rfl) ⟨65475, by rfl⟩ : syracuseStep 698405 = 130951) (by norm_num)
theorem B698429 : Blo 463784 698429 := bbase (se 3 (by rfl) ⟨130955, by rfl⟩ : syracuseStep 698429 = 261911) (by norm_num)
theorem B698453 : Blo 463784 698453 := bbase (se 8 (by rfl) ⟨4092, by rfl⟩ : syracuseStep 698453 = 8185) (by norm_num)
theorem B698477 : Blo 463784 698477 := bbase (se 3 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 698477 = 261929) (by norm_num)
theorem B698501 : Blo 463784 698501 := bbase (se 4 (by rfl) ⟨65484, by rfl⟩ : syracuseStep 698501 = 130969) (by norm_num)
theorem B698525 : Blo 463784 698525 := bbase (se 3 (by rfl) ⟨130973, by rfl⟩ : syracuseStep 698525 = 261947) (by norm_num)
theorem B698549 : Blo 463784 698549 := bbase (se 5 (by rfl) ⟨32744, by rfl⟩ : syracuseStep 698549 = 65489) (by norm_num)
theorem B698573 : Blo 463784 698573 := bbase (se 3 (by rfl) ⟨130982, by rfl⟩ : syracuseStep 698573 = 261965) (by norm_num)
theorem B698597 : Blo 463784 698597 := bbase (se 4 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 698597 = 130987) (by norm_num)
theorem B698621 : Blo 463784 698621 := bbase (se 3 (by rfl) ⟨130991, by rfl⟩ : syracuseStep 698621 = 261983) (by norm_num)
theorem B3352853 : Blo 463784 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B698645 : Blo 463784 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B698669 : Blo 463784 698669 := bbase (se 3 (by rfl) ⟨131000, by rfl⟩ : syracuseStep 698669 = 262001) (by norm_num)
theorem B698693 : Blo 463784 698693 := bbase (se 4 (by rfl) ⟨65502, by rfl⟩ : syracuseStep 698693 = 131005) (by norm_num)
theorem B698717 : Blo 463784 698717 := bbase (se 3 (by rfl) ⟨131009, by rfl⟩ : syracuseStep 698717 = 262019) (by norm_num)
theorem B698741 : Blo 463784 698741 := bbase (se 5 (by rfl) ⟨32753, by rfl⟩ : syracuseStep 698741 = 65507) (by norm_num)
theorem B567685 : Blo 463784 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B698765 : Blo 463784 698765 := bbase (se 3 (by rfl) ⟨131018, by rfl⟩ : syracuseStep 698765 = 262037) (by norm_num)
theorem B698789 : Blo 463784 698789 := bbase (se 4 (by rfl) ⟨65511, by rfl⟩ : syracuseStep 698789 = 131023) (by norm_num)
theorem B698813 : Blo 463784 698813 := bbase (se 3 (by rfl) ⟨131027, by rfl⟩ : syracuseStep 698813 = 262055) (by norm_num)
theorem B698837 : Blo 463784 698837 := bbase (se 7 (by rfl) ⟨8189, by rfl⟩ : syracuseStep 698837 = 16379) (by norm_num)
theorem B698861 : Blo 463784 698861 := bbase (se 3 (by rfl) ⟨131036, by rfl⟩ : syracuseStep 698861 = 262073) (by norm_num)
theorem B698885 : Blo 463784 698885 := bbase (se 4 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 698885 = 131041) (by norm_num)
theorem B698909 : Blo 463784 698909 := bbase (se 3 (by rfl) ⟨131045, by rfl⟩ : syracuseStep 698909 = 262091) (by norm_num)
theorem B698933 : Blo 463784 698933 := bbase (se 5 (by rfl) ⟨32762, by rfl⟩ : syracuseStep 698933 = 65525) (by norm_num)
theorem B1321541 : Blo 463784 1321541 := bbase (se 4 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 1321541 = 247789) (by norm_num)
theorem B698957 : Blo 463784 698957 := bbase (se 3 (by rfl) ⟨131054, by rfl⟩ : syracuseStep 698957 = 262109) (by norm_num)
theorem B698981 : Blo 463784 698981 := bbase (se 4 (by rfl) ⟨65529, by rfl⟩ : syracuseStep 698981 = 131059) (by norm_num)
theorem B699005 : Blo 463784 699005 := bbase (se 3 (by rfl) ⟨131063, by rfl⟩ : syracuseStep 699005 = 262127) (by norm_num)
theorem B993941 : Blo 463784 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B699029 : Blo 463784 699029 := bbase (se 6 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 699029 = 32767) (by norm_num)
theorem B1059485 : Blo 463784 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B699053 : Blo 463784 699053 := bbase (se 3 (by rfl) ⟨131072, by rfl⟩ : syracuseStep 699053 = 262145) (by norm_num)
theorem B699077 : Blo 463784 699077 := bbase (se 4 (by rfl) ⟨65538, by rfl⟩ : syracuseStep 699077 = 131077) (by norm_num)
theorem B699101 : Blo 463784 699101 := bbase (se 3 (by rfl) ⟨131081, by rfl⟩ : syracuseStep 699101 = 262163) (by norm_num)
theorem B699125 : Blo 463784 699125 := bbase (se 5 (by rfl) ⟨32771, by rfl⟩ : syracuseStep 699125 = 65543) (by norm_num)
theorem B699149 : Blo 463784 699149 := bbase (se 3 (by rfl) ⟨131090, by rfl⟩ : syracuseStep 699149 = 262181) (by norm_num)
theorem B699173 : Blo 463784 699173 := bbase (se 4 (by rfl) ⟨65547, by rfl⟩ : syracuseStep 699173 = 131095) (by norm_num)
theorem B699197 : Blo 463784 699197 := bbase (se 3 (by rfl) ⟨131099, by rfl⟩ : syracuseStep 699197 = 262199) (by norm_num)
theorem B699221 : Blo 463784 699221 := bbase (se 9 (by rfl) ⟨2048, by rfl⟩ : syracuseStep 699221 = 4097) (by norm_num)
theorem B699245 : Blo 463784 699245 := bbase (se 3 (by rfl) ⟨131108, by rfl⟩ : syracuseStep 699245 = 262217) (by norm_num)
theorem B699269 : Blo 463784 699269 := bbase (se 4 (by rfl) ⟨65556, by rfl⟩ : syracuseStep 699269 = 131113) (by norm_num)
theorem B1682309 : Blo 463784 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B994189 : Blo 463784 994189 := bbase (se 3 (by rfl) ⟨186410, by rfl⟩ : syracuseStep 994189 = 372821) (by norm_num)
theorem B699293 : Blo 463784 699293 := bbase (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) (by norm_num)
theorem B699317 : Blo 463784 699317 := bbase (se 5 (by rfl) ⟨32780, by rfl⟩ : syracuseStep 699317 = 65561) (by norm_num)
theorem B699341 : Blo 463784 699341 := bbase (se 3 (by rfl) ⟨131126, by rfl⟩ : syracuseStep 699341 = 262253) (by norm_num)
theorem B699365 : Blo 463784 699365 := bbase (se 4 (by rfl) ⟨65565, by rfl⟩ : syracuseStep 699365 = 131131) (by norm_num)
theorem B699389 : Blo 463784 699389 := bbase (se 3 (by rfl) ⟨131135, by rfl⟩ : syracuseStep 699389 = 262271) (by norm_num)
theorem B699413 : Blo 463784 699413 := bbase (se 6 (by rfl) ⟨16392, by rfl⟩ : syracuseStep 699413 = 32785) (by norm_num)
theorem B3550229 : Blo 463784 3550229 := bbase (se 6 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 3550229 = 166417) (by norm_num)
theorem B699437 : Blo 463784 699437 := bbase (se 3 (by rfl) ⟨131144, by rfl⟩ : syracuseStep 699437 = 262289) (by norm_num)
theorem B699461 : Blo 463784 699461 := bbase (se 4 (by rfl) ⟨65574, by rfl⟩ : syracuseStep 699461 = 131149) (by norm_num)
theorem B699485 : Blo 463784 699485 := bbase (se 3 (by rfl) ⟨131153, by rfl⟩ : syracuseStep 699485 = 262307) (by norm_num)
theorem B699509 : Blo 463784 699509 := bbase (se 5 (by rfl) ⟨32789, by rfl⟩ : syracuseStep 699509 = 65579) (by norm_num)
theorem B699533 : Blo 463784 699533 := bbase (se 3 (by rfl) ⟨131162, by rfl⟩ : syracuseStep 699533 = 262325) (by norm_num)
theorem B699557 : Blo 463784 699557 := bbase (se 4 (by rfl) ⟨65583, by rfl⟩ : syracuseStep 699557 = 131167) (by norm_num)
theorem B1256629 : Blo 463784 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B699581 : Blo 463784 699581 := bbase (se 3 (by rfl) ⟨131171, by rfl⟩ : syracuseStep 699581 = 262343) (by norm_num)
theorem B699605 : Blo 463784 699605 := bbase (se 7 (by rfl) ⟨8198, by rfl⟩ : syracuseStep 699605 = 16397) (by norm_num)
theorem B699629 : Blo 463784 699629 := bbase (se 3 (by rfl) ⟨131180, by rfl⟩ : syracuseStep 699629 = 262361) (by norm_num)
theorem B699653 : Blo 463784 699653 := bbase (se 4 (by rfl) ⟨65592, by rfl⟩ : syracuseStep 699653 = 131185) (by norm_num)
theorem B699677 : Blo 463784 699677 := bbase (se 3 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 699677 = 262379) (by norm_num)
theorem B699701 : Blo 463784 699701 := bbase (se 5 (by rfl) ⟨32798, by rfl⟩ : syracuseStep 699701 = 65597) (by norm_num)
theorem B699725 : Blo 463784 699725 := bbase (se 3 (by rfl) ⟨131198, by rfl⟩ : syracuseStep 699725 = 262397) (by norm_num)
theorem B699749 : Blo 463784 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B699773 : Blo 463784 699773 := bbase (se 3 (by rfl) ⟨131207, by rfl⟩ : syracuseStep 699773 = 262415) (by norm_num)
theorem B994693 : Blo 463784 994693 := bbase (se 4 (by rfl) ⟨93252, by rfl⟩ : syracuseStep 994693 = 186505) (by norm_num)
theorem B699797 : Blo 463784 699797 := bbase (se 6 (by rfl) ⟨16401, by rfl⟩ : syracuseStep 699797 = 32803) (by norm_num)
theorem B699821 : Blo 463784 699821 := bbase (se 3 (by rfl) ⟨131216, by rfl⟩ : syracuseStep 699821 = 262433) (by norm_num)
theorem B699845 : Blo 463784 699845 := bbase (se 4 (by rfl) ⟨65610, by rfl⟩ : syracuseStep 699845 = 131221) (by norm_num)
theorem B2076101 : Blo 463784 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B699869 : Blo 463784 699869 := bbase (se 3 (by rfl) ⟨131225, by rfl⟩ : syracuseStep 699869 = 262451) (by norm_num)
theorem B699893 : Blo 463784 699893 := bbase (se 5 (by rfl) ⟨32807, by rfl⟩ : syracuseStep 699893 = 65615) (by norm_num)
theorem B699917 : Blo 463784 699917 := bbase (se 3 (by rfl) ⟨131234, by rfl⟩ : syracuseStep 699917 = 262469) (by norm_num)
theorem B699941 : Blo 463784 699941 := bbase (se 4 (by rfl) ⟨65619, by rfl⟩ : syracuseStep 699941 = 131239) (by norm_num)
theorem B699965 : Blo 463784 699965 := bbase (se 3 (by rfl) ⟨131243, by rfl⟩ : syracuseStep 699965 = 262487) (by norm_num)
theorem B1683013 : Blo 463784 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B699989 : Blo 463784 699989 := bbase (se 8 (by rfl) ⟨4101, by rfl⟩ : syracuseStep 699989 = 8203) (by norm_num)
theorem B700013 : Blo 463784 700013 := bbase (se 3 (by rfl) ⟨131252, by rfl⟩ : syracuseStep 700013 = 262505) (by norm_num)
theorem B700037 : Blo 463784 700037 := bbase (se 4 (by rfl) ⟨65628, by rfl⟩ : syracuseStep 700037 = 131257) (by norm_num)
theorem B700061 : Blo 463784 700061 := bbase (se 3 (by rfl) ⟨131261, by rfl⟩ : syracuseStep 700061 = 262523) (by norm_num)
theorem B700085 : Blo 463784 700085 := bbase (se 5 (by rfl) ⟨32816, by rfl⟩ : syracuseStep 700085 = 65633) (by norm_num)
theorem B700109 : Blo 463784 700109 := bbase (se 3 (by rfl) ⟨131270, by rfl⟩ : syracuseStep 700109 = 262541) (by norm_num)
theorem B1322725 : Blo 463784 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B700133 : Blo 463784 700133 := bbase (se 4 (by rfl) ⟨65637, by rfl⟩ : syracuseStep 700133 = 131275) (by norm_num)
theorem B700157 : Blo 463784 700157 := bbase (se 3 (by rfl) ⟨131279, by rfl⟩ : syracuseStep 700157 = 262559) (by norm_num)
theorem B6893333 : Blo 463784 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B700181 : Blo 463784 700181 := bbase (se 6 (by rfl) ⟨16410, by rfl⟩ : syracuseStep 700181 = 32821) (by norm_num)
theorem B700205 : Blo 463784 700205 := bbase (se 3 (by rfl) ⟨131288, by rfl⟩ : syracuseStep 700205 = 262577) (by norm_num)
theorem B700229 : Blo 463784 700229 := bbase (se 4 (by rfl) ⟨65646, by rfl⟩ : syracuseStep 700229 = 131293) (by norm_num)
theorem B700253 : Blo 463784 700253 := bbase (se 3 (by rfl) ⟨131297, by rfl⟩ : syracuseStep 700253 = 262595) (by norm_num)
theorem B700277 : Blo 463784 700277 := bbase (se 5 (by rfl) ⟨32825, by rfl⟩ : syracuseStep 700277 = 65651) (by norm_num)
theorem B1322885 : Blo 463784 1322885 := bbase (se 4 (by rfl) ⟨124020, by rfl⟩ : syracuseStep 1322885 = 248041) (by norm_num)
theorem B700301 : Blo 463784 700301 := bbase (se 3 (by rfl) ⟨131306, by rfl⟩ : syracuseStep 700301 = 262613) (by norm_num)
theorem B2240405 : Blo 463784 2240405 := bbase (se 6 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 2240405 = 105019) (by norm_num)
theorem B700325 : Blo 463784 700325 := bbase (se 4 (by rfl) ⟨65655, by rfl⟩ : syracuseStep 700325 = 131311) (by norm_num)
theorem B700349 : Blo 463784 700349 := bbase (se 3 (by rfl) ⟨131315, by rfl⟩ : syracuseStep 700349 = 262631) (by norm_num)
theorem B700373 : Blo 463784 700373 := bbase (se 7 (by rfl) ⟨8207, by rfl⟩ : syracuseStep 700373 = 16415) (by norm_num)
theorem B503777 : Blo 463784 503777 := bbase (se 2 (by rfl) ⟨188916, by rfl⟩ : syracuseStep 503777 = 377833) (by norm_num)
theorem B700397 : Blo 463784 700397 := bbase (se 3 (by rfl) ⟨131324, by rfl⟩ : syracuseStep 700397 = 262649) (by norm_num)
theorem B700421 : Blo 463784 700421 := bbase (se 4 (by rfl) ⟨65664, by rfl⟩ : syracuseStep 700421 = 131329) (by norm_num)
theorem B700445 : Blo 463784 700445 := bbase (se 3 (by rfl) ⟨131333, by rfl⟩ : syracuseStep 700445 = 262667) (by norm_num)
theorem B471085 : Blo 463784 471085 := bbase (se 3 (by rfl) ⟨88328, by rfl⟩ : syracuseStep 471085 = 176657) (by norm_num)
theorem B897077 : Blo 463784 897077 := bbase (se 5 (by rfl) ⟨42050, by rfl⟩ : syracuseStep 897077 = 84101) (by norm_num)
theorem B700469 : Blo 463784 700469 := bbase (se 5 (by rfl) ⟨32834, by rfl⟩ : syracuseStep 700469 = 65669) (by norm_num)
theorem B700493 : Blo 463784 700493 := bbase (se 3 (by rfl) ⟨131342, by rfl⟩ : syracuseStep 700493 = 262685) (by norm_num)
theorem B700517 : Blo 463784 700517 := bbase (se 4 (by rfl) ⟨65673, by rfl⟩ : syracuseStep 700517 = 131347) (by norm_num)
theorem B1323125 : Blo 463784 1323125 := bbase (se 5 (by rfl) ⟨62021, by rfl⟩ : syracuseStep 1323125 = 124043) (by norm_num)
theorem B3977333 : Blo 463784 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B700541 : Blo 463784 700541 := bbase (se 3 (by rfl) ⟨131351, by rfl⟩ : syracuseStep 700541 = 262703) (by norm_num)
theorem B569477 : Blo 463784 569477 := bbase (se 4 (by rfl) ⟨53388, by rfl⟩ : syracuseStep 569477 = 106777) (by norm_num)
theorem B700565 : Blo 463784 700565 := bbase (se 6 (by rfl) ⟨16419, by rfl⟩ : syracuseStep 700565 = 32839) (by norm_num)
theorem B700589 : Blo 463784 700589 := bbase (se 3 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 700589 = 262721) (by norm_num)
theorem B700613 : Blo 463784 700613 := bbase (se 4 (by rfl) ⟨65682, by rfl⟩ : syracuseStep 700613 = 131365) (by norm_num)
theorem B700637 : Blo 463784 700637 := bbase (se 3 (by rfl) ⟨131369, by rfl⟩ : syracuseStep 700637 = 262739) (by norm_num)
theorem B700661 : Blo 463784 700661 := bbase (se 5 (by rfl) ⟨32843, by rfl⟩ : syracuseStep 700661 = 65687) (by norm_num)
theorem B995581 : Blo 463784 995581 := bbase (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) (by norm_num)
theorem B700685 : Blo 463784 700685 := bbase (se 3 (by rfl) ⟨131378, by rfl⟩ : syracuseStep 700685 = 262757) (by norm_num)
theorem B700709 : Blo 463784 700709 := bbase (se 4 (by rfl) ⟨65691, by rfl⟩ : syracuseStep 700709 = 131383) (by norm_num)
theorem B1323317 : Blo 463784 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B700733 : Blo 463784 700733 := bbase (se 3 (by rfl) ⟨131387, by rfl⟩ : syracuseStep 700733 = 262775) (by norm_num)
theorem B700757 : Blo 463784 700757 := bbase (se 10 (by rfl) ⟨1026, by rfl⟩ : syracuseStep 700757 = 2053) (by norm_num)
theorem B471401 : Blo 463784 471401 := bbase (se 2 (by rfl) ⟨176775, by rfl⟩ : syracuseStep 471401 = 353551) (by norm_num)
theorem B700781 : Blo 463784 700781 := bbase (se 3 (by rfl) ⟨131396, by rfl⟩ : syracuseStep 700781 = 262793) (by norm_num)
theorem B700805 : Blo 463784 700805 := bbase (se 4 (by rfl) ⟨65700, by rfl⟩ : syracuseStep 700805 = 131401) (by norm_num)
theorem B700829 : Blo 463784 700829 := bbase (se 3 (by rfl) ⟨131405, by rfl⟩ : syracuseStep 700829 = 262811) (by norm_num)
theorem B700853 : Blo 463784 700853 := bbase (se 5 (by rfl) ⟨32852, by rfl⟩ : syracuseStep 700853 = 65705) (by norm_num)
theorem B700877 : Blo 463784 700877 := bbase (se 3 (by rfl) ⟨131414, by rfl⟩ : syracuseStep 700877 = 262829) (by norm_num)
theorem B700901 : Blo 463784 700901 := bbase (se 4 (by rfl) ⟨65709, by rfl⟩ : syracuseStep 700901 = 131419) (by norm_num)
theorem B700925 : Blo 463784 700925 := bbase (se 3 (by rfl) ⟨131423, by rfl⟩ : syracuseStep 700925 = 262847) (by norm_num)
theorem B700949 : Blo 463784 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B864805 : Blo 463784 864805 := bbase (se 4 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 864805 = 162151) (by norm_num)
theorem B700973 : Blo 463784 700973 := bbase (se 3 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 700973 = 262865) (by norm_num)
theorem B700997 : Blo 463784 700997 := bbase (se 4 (by rfl) ⟨65718, by rfl⟩ : syracuseStep 700997 = 131437) (by norm_num)
theorem B471629 : Blo 463784 471629 := bbase (se 3 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 471629 = 176861) (by norm_num)
theorem B701021 : Blo 463784 701021 := bbase (se 3 (by rfl) ⟨131441, by rfl⟩ : syracuseStep 701021 = 262883) (by norm_num)
theorem B701045 : Blo 463784 701045 := bbase (se 5 (by rfl) ⟨32861, by rfl⟩ : syracuseStep 701045 = 65723) (by norm_num)
theorem B701069 : Blo 463784 701069 := bbase (se 3 (by rfl) ⟨131450, by rfl⟩ : syracuseStep 701069 = 262901) (by norm_num)
theorem B701093 : Blo 463784 701093 := bbase (se 4 (by rfl) ⟨65727, by rfl⟩ : syracuseStep 701093 = 131455) (by norm_num)
theorem B504505 : Blo 463784 504505 := bbase (se 2 (by rfl) ⟨189189, by rfl⟩ : syracuseStep 504505 = 378379) (by norm_num)
theorem B701117 : Blo 463784 701117 := bbase (se 3 (by rfl) ⟨131459, by rfl⟩ : syracuseStep 701117 = 262919) (by norm_num)
theorem B701141 : Blo 463784 701141 := bbase (se 7 (by rfl) ⟨8216, by rfl⟩ : syracuseStep 701141 = 16433) (by norm_num)
theorem B996077 : Blo 463784 996077 := bbase (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) (by norm_num)
theorem B701165 : Blo 463784 701165 := bbase (se 3 (by rfl) ⟨131468, by rfl⟩ : syracuseStep 701165 = 262937) (by norm_num)
theorem B1487605 : Blo 463784 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B701189 : Blo 463784 701189 := bbase (se 4 (by rfl) ⟨65736, by rfl⟩ : syracuseStep 701189 = 131473) (by norm_num)
theorem B897821 : Blo 463784 897821 := bbase (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) (by norm_num)
theorem B701213 : Blo 463784 701213 := bbase (se 3 (by rfl) ⟨131477, by rfl⟩ : syracuseStep 701213 = 262955) (by norm_num)
theorem B537377 : Blo 463784 537377 := bbase (se 2 (by rfl) ⟨201516, by rfl⟩ : syracuseStep 537377 = 403033) (by norm_num)
theorem B701237 : Blo 463784 701237 := bbase (se 5 (by rfl) ⟨32870, by rfl⟩ : syracuseStep 701237 = 65741) (by norm_num)
theorem B701261 : Blo 463784 701261 := bbase (se 3 (by rfl) ⟨131486, by rfl⟩ : syracuseStep 701261 = 262973) (by norm_num)
theorem B1258325 : Blo 463784 1258325 := bbase (se 9 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 1258325 = 7373) (by norm_num)
theorem B701285 : Blo 463784 701285 := bbase (se 4 (by rfl) ⟨65745, by rfl⟩ : syracuseStep 701285 = 131491) (by norm_num)
theorem B701309 : Blo 463784 701309 := bbase (se 3 (by rfl) ⟨131495, by rfl⟩ : syracuseStep 701309 = 262991) (by norm_num)
theorem B471953 : Blo 463784 471953 := bbase (se 2 (by rfl) ⟨176982, by rfl⟩ : syracuseStep 471953 = 353965) (by norm_num)
theorem B701333 : Blo 463784 701333 := bbase (se 6 (by rfl) ⟨16437, by rfl⟩ : syracuseStep 701333 = 32875) (by norm_num)
theorem B701357 : Blo 463784 701357 := bbase (se 3 (by rfl) ⟨131504, by rfl⟩ : syracuseStep 701357 = 263009) (by norm_num)
theorem B701381 : Blo 463784 701381 := bbase (se 4 (by rfl) ⟨65754, by rfl⟩ : syracuseStep 701381 = 131509) (by norm_num)
theorem B701405 : Blo 463784 701405 := bbase (se 3 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 701405 = 263027) (by norm_num)
theorem B701429 : Blo 463784 701429 := bbase (se 5 (by rfl) ⟨32879, by rfl⟩ : syracuseStep 701429 = 65759) (by norm_num)
theorem B701453 : Blo 463784 701453 := bbase (se 3 (by rfl) ⟨131522, by rfl⟩ : syracuseStep 701453 = 263045) (by norm_num)
theorem B2241557 : Blo 463784 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B701477 : Blo 463784 701477 := bbase (se 4 (by rfl) ⟨65763, by rfl⟩ : syracuseStep 701477 = 131527) (by norm_num)
theorem B701501 : Blo 463784 701501 := bbase (se 3 (by rfl) ⟨131531, by rfl⟩ : syracuseStep 701501 = 263063) (by norm_num)
theorem B701525 : Blo 463784 701525 := bbase (se 8 (by rfl) ⟨4110, by rfl⟩ : syracuseStep 701525 = 8221) (by norm_num)
theorem B701549 : Blo 463784 701549 := bbase (se 3 (by rfl) ⟨131540, by rfl⟩ : syracuseStep 701549 = 263081) (by norm_num)
theorem B701573 : Blo 463784 701573 := bbase (se 4 (by rfl) ⟨65772, by rfl⟩ : syracuseStep 701573 = 131545) (by norm_num)
theorem B701597 : Blo 463784 701597 := bbase (se 3 (by rfl) ⟨131549, by rfl⟩ : syracuseStep 701597 = 263099) (by norm_num)
theorem B701621 : Blo 463784 701621 := bbase (se 5 (by rfl) ⟨32888, by rfl⟩ : syracuseStep 701621 = 65777) (by norm_num)
theorem B701645 : Blo 463784 701645 := bbase (se 3 (by rfl) ⟨131558, by rfl⟩ : syracuseStep 701645 = 263117) (by norm_num)
theorem B2831573 : Blo 463784 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B701669 : Blo 463784 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B1324309 : Blo 463784 1324309 := bbase (se 6 (by rfl) ⟨31038, by rfl⟩ : syracuseStep 1324309 = 62077) (by norm_num)
theorem B6305365 : Blo 463784 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B996965 : Blo 463784 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B997085 : Blo 463784 997085 := bbase (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) (by norm_num)
theorem B472825 : Blo 463784 472825 := bbase (se 2 (by rfl) ⟨177309, by rfl⟩ : syracuseStep 472825 = 354619) (by norm_num)
theorem B2242325 : Blo 463784 2242325 := bbase (se 6 (by rfl) ⟨52554, by rfl⟩ : syracuseStep 2242325 = 105109) (by norm_num)
theorem B1718101 : Blo 463784 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B669637 : Blo 463784 669637 := bbase (se 4 (by rfl) ⟨62778, by rfl⟩ : syracuseStep 669637 = 125557) (by norm_num)
theorem B604157 : Blo 463784 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B1816757 : Blo 463784 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B997717 : Blo 463784 997717 := bbase (se 10 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 997717 = 2923) (by norm_num)
theorem B1325413 : Blo 463784 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B473477 : Blo 463784 473477 := bbase (se 4 (by rfl) ⟨44388, by rfl⟩ : syracuseStep 473477 = 88777) (by norm_num)
theorem B5323157 : Blo 463784 5323157 := bbase (se 6 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 5323157 = 249523) (by norm_num)
theorem B506341 : Blo 463784 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B7191061 : Blo 463784 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B473737 : Blo 463784 473737 := bbase (se 2 (by rfl) ⟨177651, by rfl⟩ : syracuseStep 473737 = 355303) (by norm_num)
theorem B1882997 : Blo 463784 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B7551893 : Blo 463784 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B998605 : Blo 463784 998605 := bbase (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) (by norm_num)
theorem B7552277 : Blo 463784 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B998725 : Blo 463784 998725 := bbase (se 4 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 998725 = 187261) (by norm_num)
theorem B7585109 : Blo 463784 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B6733205 : Blo 463784 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B1490501 : Blo 463784 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B998981 : Blo 463784 998981 := bbase (se 4 (by rfl) ⟨93654, by rfl⟩ : syracuseStep 998981 = 187309) (by norm_num)
theorem B605881 : Blo 463784 605881 := bbase (se 2 (by rfl) ⟨227205, by rfl⟩ : syracuseStep 605881 = 454411) (by norm_num)
theorem B1326917 : Blo 463784 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B606085 : Blo 463784 606085 := bbase (se 4 (by rfl) ⟨56820, by rfl⟩ : syracuseStep 606085 = 113641) (by norm_num)
theorem B606133 : Blo 463784 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B524281 : Blo 463784 524281 := bbase (se 2 (by rfl) ⟨196605, by rfl⟩ : syracuseStep 524281 = 393211) (by norm_num)
theorem B1982501 : Blo 463784 1982501 := bbase (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) (by norm_num)
theorem B1982789 : Blo 463784 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B1720709 : Blo 463784 1720709 := bbase (se 4 (by rfl) ⟨161316, by rfl⟩ : syracuseStep 1720709 = 322633) (by norm_num)
theorem B1491797 : Blo 463784 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B1065901 : Blo 463784 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B836605 : Blo 463784 836605 := bbase (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) (by norm_num)
theorem B1983541 : Blo 463784 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B607541 : Blo 463784 607541 := bbase (se 5 (by rfl) ⟨28478, by rfl⟩ : syracuseStep 607541 = 56957) (by norm_num)
theorem B1197421 : Blo 463784 1197421 := bbase (se 3 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 1197421 = 449033) (by norm_num)
theorem B1328501 : Blo 463784 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B1263061 : Blo 463784 1263061 := bbase (se 7 (by rfl) ⟨14801, by rfl⟩ : syracuseStep 1263061 = 29603) (by norm_num)
theorem B3032821 : Blo 463784 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B1984277 : Blo 463784 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B706469 : Blo 463784 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B1329173 : Blo 463784 1329173 := bbase (se 6 (by rfl) ⟨31152, by rfl⟩ : syracuseStep 1329173 = 62305) (by norm_num)
theorem B804917 : Blo 463784 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B837989 : Blo 463784 837989 := bbase (se 4 (by rfl) ⟨78561, by rfl⟩ : syracuseStep 837989 = 157123) (by norm_num)
theorem B1329605 : Blo 463784 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B510449 : Blo 463784 510449 := bbase (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) (by norm_num)
theorem B510581 : Blo 463784 510581 := bbase (se 5 (by rfl) ⟨23933, by rfl⟩ : syracuseStep 510581 = 47867) (by norm_num)
theorem B1493653 : Blo 463784 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1198901 : Blo 463784 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B576377 : Blo 463784 576377 := bbase (se 2 (by rfl) ⟨216141, by rfl⟩ : syracuseStep 576377 = 432283) (by norm_num)
theorem B576437 : Blo 463784 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B1330357 : Blo 463784 1330357 := bbase (se 5 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 1330357 = 124721) (by norm_num)
theorem B2837749 : Blo 463784 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B7982549 : Blo 463784 7982549 := bbase (se 7 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 7982549 = 187091) (by norm_num)
theorem B708221 : Blo 463784 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B1887877 : Blo 463784 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B5820245 : Blo 463784 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B2019541 : Blo 463784 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B3526901 : Blo 463784 3526901 := bbase (se 5 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 3526901 = 330647) (by norm_num)
theorem B1430245 : Blo 463784 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B1889045 : Blo 463784 1889045 := bbase (se 6 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 1889045 = 88549) (by norm_num)
theorem B840469 : Blo 463784 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B840613 : Blo 463784 840613 := bbase (se 4 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 840613 = 157615) (by norm_num)
theorem B1987573 : Blo 463784 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B480349 : Blo 463784 480349 := bbase (se 3 (by rfl) ⟨90065, by rfl⟩ : syracuseStep 480349 = 180131) (by norm_num)
theorem B3200629 : Blo 463784 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B841421 : Blo 463784 841421 := bbase (se 3 (by rfl) ⟨157766, by rfl⟩ : syracuseStep 841421 = 315533) (by norm_num)
theorem B2348837 : Blo 463784 2348837 := bbase (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) (by norm_num)
theorem B743213 : Blo 463784 743213 := bbase (se 3 (by rfl) ⟨139352, by rfl⟩ : syracuseStep 743213 = 278705) (by norm_num)
theorem B841565 : Blo 463784 841565 := bbase (se 3 (by rfl) ⟨157793, by rfl⟩ : syracuseStep 841565 = 315587) (by norm_num)
theorem B841637 : Blo 463784 841637 := bbase (se 4 (by rfl) ⟨78903, by rfl⟩ : syracuseStep 841637 = 157807) (by norm_num)
theorem B743341 : Blo 463784 743341 := bbase (se 3 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 743341 = 278753) (by norm_num)
theorem B841853 : Blo 463784 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1136773 : Blo 463784 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B5986709 : Blo 463784 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B940501 : Blo 463784 940501 := bbase (se 7 (by rfl) ⟨11021, by rfl⟩ : syracuseStep 940501 = 22043) (by norm_num)
theorem B3365333 : Blo 463784 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B2513429 : Blo 463784 2513429 := bbase (se 6 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 2513429 = 117817) (by norm_num)
theorem B1497845 : Blo 463784 1497845 := bbase (se 5 (by rfl) ⟨70211, by rfl⟩ : syracuseStep 1497845 = 140423) (by norm_num)
theorem B842653 : Blo 463784 842653 := bbase (se 3 (by rfl) ⟨157997, by rfl⟩ : syracuseStep 842653 = 315995) (by norm_num)
theorem B2350133 : Blo 463784 2350133 := bbase (se 5 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 2350133 = 220325) (by norm_num)
theorem B744725 : Blo 463784 744725 := bbase (se 6 (by rfl) ⟨17454, by rfl⟩ : syracuseStep 744725 = 34909) (by norm_num)
theorem B1793669 : Blo 463784 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B1761173 : Blo 463784 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B1990565 : Blo 463784 1990565 := bbase (se 4 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 1990565 = 373231) (by norm_num)
theorem B745661 : Blo 463784 745661 := bbase (se 3 (by rfl) ⟨139811, by rfl⟩ : syracuseStep 745661 = 279623) (by norm_num)
theorem B942301 : Blo 463784 942301 := bbase (se 3 (by rfl) ⟨176681, by rfl⟩ : syracuseStep 942301 = 353363) (by norm_num)
theorem B942349 : Blo 463784 942349 := bbase (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) (by norm_num)
theorem B2351429 : Blo 463784 2351429 := bbase (se 4 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 2351429 = 440893) (by norm_num)
theorem B746309 : Blo 463784 746309 := bbase (se 4 (by rfl) ⟨69966, by rfl⟩ : syracuseStep 746309 = 139933) (by norm_num)
theorem B1794901 : Blo 463784 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B942965 : Blo 463784 942965 := bbase (se 5 (by rfl) ⟨44201, by rfl⟩ : syracuseStep 942965 = 88403) (by norm_num)
theorem B942997 : Blo 463784 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B1991573 : Blo 463784 1991573 := bbase (se 6 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 1991573 = 93355) (by norm_num)
theorem B1565621 : Blo 463784 1565621 := bbase (se 5 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 1565621 = 146777) (by norm_num)
theorem B1762357 : Blo 463784 1762357 := bbase (se 5 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 1762357 = 165221) (by norm_num)
theorem B1566053 : Blo 463784 1566053 := bbase (se 4 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 1566053 = 293635) (by norm_num)
theorem B1762661 : Blo 463784 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B2352725 : Blo 463784 2352725 := bbase (se 8 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 2352725 = 27571) (by norm_num)
theorem B2647637 : Blo 463784 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B1074869 : Blo 463784 1074869 := bbase (se 5 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 1074869 = 100769) (by norm_num)
theorem B1566485 : Blo 463784 1566485 := bbase (se 6 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 1566485 = 73429) (by norm_num)
theorem B747301 : Blo 463784 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B681781 : Blo 463784 681781 := bbase (se 5 (by rfl) ⟨31958, by rfl⟩ : syracuseStep 681781 = 63917) (by norm_num)
theorem B1632101 : Blo 463784 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B1566917 : Blo 463784 1566917 := bbase (se 4 (by rfl) ⟨146898, by rfl⟩ : syracuseStep 1566917 = 293797) (by norm_num)
theorem B747749 : Blo 463784 747749 := bbase (se 4 (by rfl) ⟨70101, by rfl⟩ : syracuseStep 747749 = 140203) (by norm_num)
theorem B747949 : Blo 463784 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B1173973 : Blo 463784 1173973 := bbase (se 7 (by rfl) ⟨13757, by rfl⟩ : syracuseStep 1173973 = 27515) (by norm_num)
theorem B1174085 : Blo 463784 1174085 := bbase (se 4 (by rfl) ⟨110070, by rfl⟩ : syracuseStep 1174085 = 220141) (by norm_num)
theorem B1567349 : Blo 463784 1567349 := bbase (se 5 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 1567349 = 146939) (by norm_num)
theorem B1993349 : Blo 463784 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B748205 : Blo 463784 748205 := bbase (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) (by norm_num)
theorem B2648821 : Blo 463784 2648821 := bbase (se 5 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 2648821 = 248327) (by norm_num)
theorem B1174277 : Blo 463784 1174277 := bbase (se 4 (by rfl) ⟨110088, by rfl⟩ : syracuseStep 1174277 = 220177) (by norm_num)
theorem B2354021 : Blo 463784 2354021 := bbase (se 4 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 2354021 = 441379) (by norm_num)
theorem B1534997 : Blo 463784 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B1567781 : Blo 463784 1567781 := bbase (se 4 (by rfl) ⟨146979, by rfl⟩ : syracuseStep 1567781 = 293959) (by norm_num)
theorem B1043549 : Blo 463784 1043549 := bbase (se 3 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 1043549 = 391331) (by norm_num)
theorem B1174621 : Blo 463784 1174621 := bbase (se 3 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 1174621 = 440483) (by norm_num)
theorem B1043621 : Blo 463784 1043621 := bbase (se 4 (by rfl) ⟨97839, by rfl⟩ : syracuseStep 1043621 = 195679) (by norm_num)
theorem B1174733 : Blo 463784 1174733 := bbase (se 3 (by rfl) ⟨220262, by rfl⟩ : syracuseStep 1174733 = 440525) (by norm_num)
theorem B1043693 : Blo 463784 1043693 := bbase (se 3 (by rfl) ⟨195692, by rfl⟩ : syracuseStep 1043693 = 391385) (by norm_num)
theorem B1043765 : Blo 463784 1043765 := bbase (se 5 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 1043765 = 97853) (by norm_num)
theorem B1043837 : Blo 463784 1043837 := bbase (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) (by norm_num)
theorem B1174925 : Blo 463784 1174925 := bbase (se 3 (by rfl) ⟨220298, by rfl⟩ : syracuseStep 1174925 = 440597) (by norm_num)
theorem B1764773 : Blo 463784 1764773 := bbase (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) (by norm_num)
theorem B1043909 : Blo 463784 1043909 := bbase (se 4 (by rfl) ⟨97866, by rfl⟩ : syracuseStep 1043909 = 195733) (by norm_num)
theorem B1568213 : Blo 463784 1568213 := bbase (se 7 (by rfl) ⟨18377, by rfl⟩ : syracuseStep 1568213 = 36755) (by norm_num)
theorem B585185 : Blo 463784 585185 := bbase (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) (by norm_num)
theorem B1043981 : Blo 463784 1043981 := bbase (se 3 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 1043981 = 391493) (by norm_num)
theorem B1044053 : Blo 463784 1044053 := bbase (se 8 (by rfl) ⟨6117, by rfl⟩ : syracuseStep 1044053 = 12235) (by norm_num)
theorem B1044125 : Blo 463784 1044125 := bbase (se 3 (by rfl) ⟨195773, by rfl⟩ : syracuseStep 1044125 = 391547) (by norm_num)
theorem B1765061 : Blo 463784 1765061 := bbase (se 4 (by rfl) ⟨165474, by rfl⟩ : syracuseStep 1765061 = 330949) (by norm_num)
theorem B1044197 : Blo 463784 1044197 := bbase (se 4 (by rfl) ⟨97893, by rfl⟩ : syracuseStep 1044197 = 195787) (by norm_num)
theorem B1175269 : Blo 463784 1175269 := bbase (se 4 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 1175269 = 220363) (by norm_num)
theorem B1044269 : Blo 463784 1044269 := bbase (se 3 (by rfl) ⟨195800, by rfl⟩ : syracuseStep 1044269 = 391601) (by norm_num)
theorem B1175381 : Blo 463784 1175381 := bbase (se 9 (by rfl) ⟨3443, by rfl⟩ : syracuseStep 1175381 = 6887) (by norm_num)
theorem B3534677 : Blo 463784 3534677 := bbase (se 9 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 3534677 = 20711) (by norm_num)
theorem B1044341 : Blo 463784 1044341 := bbase (se 5 (by rfl) ⟨48953, by rfl⟩ : syracuseStep 1044341 = 97907) (by norm_num)
theorem B1568645 : Blo 463784 1568645 := bbase (se 4 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 1568645 = 294121) (by norm_num)
theorem B880541 : Blo 463784 880541 := bbase (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) (by norm_num)
theorem B1896373 : Blo 463784 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1044413 : Blo 463784 1044413 := bbase (se 3 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 1044413 = 391655) (by norm_num)
theorem B1044485 : Blo 463784 1044485 := bbase (se 4 (by rfl) ⟨97920, by rfl⟩ : syracuseStep 1044485 = 195841) (by norm_num)
theorem B1175573 : Blo 463784 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B1044557 : Blo 463784 1044557 := bbase (se 3 (by rfl) ⟨195854, by rfl⟩ : syracuseStep 1044557 = 391709) (by norm_num)
theorem B2355317 : Blo 463784 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B1044629 : Blo 463784 1044629 := bbase (se 6 (by rfl) ⟨24483, by rfl⟩ : syracuseStep 1044629 = 48967) (by norm_num)
theorem B1044701 : Blo 463784 1044701 := bbase (se 3 (by rfl) ⟨195881, by rfl⟩ : syracuseStep 1044701 = 391763) (by norm_num)
theorem B1011989 : Blo 463784 1011989 := bbase (se 6 (by rfl) ⟨23718, by rfl⟩ : syracuseStep 1011989 = 47437) (by norm_num)
theorem B1044773 : Blo 463784 1044773 := bbase (se 4 (by rfl) ⟨97947, by rfl⟩ : syracuseStep 1044773 = 195895) (by norm_num)
theorem B1569077 : Blo 463784 1569077 := bbase (se 5 (by rfl) ⟨73550, by rfl⟩ : syracuseStep 1569077 = 147101) (by norm_num)
theorem B782669 : Blo 463784 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B1044845 : Blo 463784 1044845 := bbase (se 3 (by rfl) ⟨195908, by rfl⟩ : syracuseStep 1044845 = 391817) (by norm_num)
theorem B1175917 : Blo 463784 1175917 := bbase (se 3 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 1175917 = 440969) (by norm_num)
theorem B1044917 : Blo 463784 1044917 := bbase (se 5 (by rfl) ⟨48980, by rfl⟩ : syracuseStep 1044917 = 97961) (by norm_num)
theorem B782797 : Blo 463784 782797 := bbase (se 3 (by rfl) ⟨146774, by rfl⟩ : syracuseStep 782797 = 293549) (by norm_num)
theorem B1176029 : Blo 463784 1176029 := bbase (se 3 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 1176029 = 441011) (by norm_num)
theorem B1044989 : Blo 463784 1044989 := bbase (se 3 (by rfl) ⟨195935, by rfl⟩ : syracuseStep 1044989 = 391871) (by norm_num)
theorem B2126341 : Blo 463784 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B782885 : Blo 463784 782885 := bbase (se 4 (by rfl) ⟨73395, by rfl⟩ : syracuseStep 782885 = 146791) (by norm_num)
theorem B1045061 : Blo 463784 1045061 := bbase (se 4 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 1045061 = 195949) (by norm_num)
theorem B881293 : Blo 463784 881293 := bbase (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) (by norm_num)
theorem B1045133 : Blo 463784 1045133 := bbase (se 3 (by rfl) ⟨195962, by rfl⟩ : syracuseStep 1045133 = 391925) (by norm_num)
theorem B1176221 : Blo 463784 1176221 := bbase (se 3 (by rfl) ⟨220541, by rfl⟩ : syracuseStep 1176221 = 441083) (by norm_num)
theorem B783013 : Blo 463784 783013 := bbase (se 4 (by rfl) ⟨73407, by rfl⟩ : syracuseStep 783013 = 146815) (by norm_num)
theorem B2650805 : Blo 463784 2650805 := bbase (se 5 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 2650805 = 248513) (by norm_num)
theorem B1045205 : Blo 463784 1045205 := bbase (se 7 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 1045205 = 24497) (by norm_num)
theorem B1569509 : Blo 463784 1569509 := bbase (se 4 (by rfl) ⟨147141, by rfl⟩ : syracuseStep 1569509 = 294283) (by norm_num)
theorem B3764981 : Blo 463784 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B783101 : Blo 463784 783101 := bbase (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) (by norm_num)
theorem B881437 : Blo 463784 881437 := bbase (se 3 (by rfl) ⟨165269, by rfl⟩ : syracuseStep 881437 = 330539) (by norm_num)
theorem B1045277 : Blo 463784 1045277 := bbase (se 3 (by rfl) ⟨195989, by rfl⟩ : syracuseStep 1045277 = 391979) (by norm_num)
theorem B1045349 : Blo 463784 1045349 := bbase (se 4 (by rfl) ⟨98001, by rfl⟩ : syracuseStep 1045349 = 196003) (by norm_num)
theorem B1766245 : Blo 463784 1766245 := bbase (se 4 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 1766245 = 331171) (by norm_num)
theorem B783229 : Blo 463784 783229 := bbase (se 3 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 783229 = 293711) (by norm_num)
theorem B1045421 : Blo 463784 1045421 := bbase (se 3 (by rfl) ⟨196016, by rfl⟩ : syracuseStep 1045421 = 392033) (by norm_num)
theorem B881597 : Blo 463784 881597 := bbase (se 3 (by rfl) ⟨165299, by rfl⟩ : syracuseStep 881597 = 330599) (by norm_num)
theorem B783317 : Blo 463784 783317 := bbase (se 7 (by rfl) ⟨9179, by rfl⟩ : syracuseStep 783317 = 18359) (by norm_num)
theorem B1045493 : Blo 463784 1045493 := bbase (se 5 (by rfl) ⟨49007, by rfl⟩ : syracuseStep 1045493 = 98015) (by norm_num)
theorem B1176565 : Blo 463784 1176565 := bbase (se 5 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 1176565 = 110303) (by norm_num)
theorem B1045565 : Blo 463784 1045565 := bbase (se 3 (by rfl) ⟨196043, by rfl⟩ : syracuseStep 1045565 = 392087) (by norm_num)
theorem B881741 : Blo 463784 881741 := bbase (se 3 (by rfl) ⟨165326, by rfl⟩ : syracuseStep 881741 = 330653) (by norm_num)
theorem B783445 : Blo 463784 783445 := bbase (se 8 (by rfl) ⟨4590, by rfl⟩ : syracuseStep 783445 = 9181) (by norm_num)
theorem B1176677 : Blo 463784 1176677 := bbase (se 4 (by rfl) ⟨110313, by rfl⟩ : syracuseStep 1176677 = 220627) (by norm_num)
theorem B1045637 : Blo 463784 1045637 := bbase (se 4 (by rfl) ⟨98028, by rfl⟩ : syracuseStep 1045637 = 196057) (by norm_num)
theorem B1569941 : Blo 463784 1569941 := bbase (se 6 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 1569941 = 73591) (by norm_num)
theorem B1766549 : Blo 463784 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B783533 : Blo 463784 783533 := bbase (se 3 (by rfl) ⟨146912, by rfl⟩ : syracuseStep 783533 = 293825) (by norm_num)
theorem B1045709 : Blo 463784 1045709 := bbase (se 3 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 1045709 = 392141) (by norm_num)
theorem B849133 : Blo 463784 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B587017 : Blo 463784 587017 := bbase (se 2 (by rfl) ⟨220131, by rfl⟩ : syracuseStep 587017 = 440263) (by norm_num)
theorem B1045781 : Blo 463784 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B1176869 : Blo 463784 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B783661 : Blo 463784 783661 := bbase (se 3 (by rfl) ⟨146936, by rfl⟩ : syracuseStep 783661 = 293873) (by norm_num)
theorem B1045853 : Blo 463784 1045853 := bbase (se 3 (by rfl) ⟨196097, by rfl⟩ : syracuseStep 1045853 = 392195) (by norm_num)
theorem B882029 : Blo 463784 882029 := bbase (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) (by norm_num)
theorem B783749 : Blo 463784 783749 := bbase (se 4 (by rfl) ⟨73476, by rfl⟩ : syracuseStep 783749 = 146953) (by norm_num)
theorem B2356613 : Blo 463784 2356613 := bbase (se 4 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 2356613 = 441865) (by norm_num)
theorem B1045925 : Blo 463784 1045925 := bbase (se 4 (by rfl) ⟨98055, by rfl⟩ : syracuseStep 1045925 = 196111) (by norm_num)
theorem B947621 : Blo 463784 947621 := bbase (se 4 (by rfl) ⟨88839, by rfl⟩ : syracuseStep 947621 = 177679) (by norm_num)
theorem B587189 : Blo 463784 587189 := bbase (se 5 (by rfl) ⟨27524, by rfl⟩ : syracuseStep 587189 = 55049) (by norm_num)
theorem B587245 : Blo 463784 587245 := bbase (se 3 (by rfl) ⟨110108, by rfl⟩ : syracuseStep 587245 = 220217) (by norm_num)
theorem B1045997 : Blo 463784 1045997 := bbase (se 3 (by rfl) ⟨196124, by rfl⟩ : syracuseStep 1045997 = 392249) (by norm_num)
theorem B783877 : Blo 463784 783877 := bbase (se 4 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 783877 = 146977) (by norm_num)
theorem B882181 : Blo 463784 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B521761 : Blo 463784 521761 := bbase (se 2 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 521761 = 391321) (by norm_num)
theorem B1046069 : Blo 463784 1046069 := bbase (se 5 (by rfl) ⟨49034, by rfl⟩ : syracuseStep 1046069 = 98069) (by norm_num)
theorem B1570373 : Blo 463784 1570373 := bbase (se 4 (by rfl) ⟨147222, by rfl⟩ : syracuseStep 1570373 = 294445) (by norm_num)
theorem B521797 : Blo 463784 521797 := bbase (se 4 (by rfl) ⟨48918, by rfl⟩ : syracuseStep 521797 = 97837) (by norm_num)
theorem B587341 : Blo 463784 587341 := bbase (se 3 (by rfl) ⟨110126, by rfl⟩ : syracuseStep 587341 = 220253) (by norm_num)
theorem B2979413 : Blo 463784 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B783965 : Blo 463784 783965 := bbase (se 3 (by rfl) ⟨146993, by rfl⟩ : syracuseStep 783965 = 293987) (by norm_num)
theorem B521833 : Blo 463784 521833 := bbase (se 2 (by rfl) ⟨195687, by rfl⟩ : syracuseStep 521833 = 391375) (by norm_num)
theorem B1046141 : Blo 463784 1046141 := bbase (se 3 (by rfl) ⟨196151, by rfl⟩ : syracuseStep 1046141 = 392303) (by norm_num)
theorem B1177213 : Blo 463784 1177213 := bbase (se 3 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 1177213 = 441455) (by norm_num)
theorem B521869 : Blo 463784 521869 := bbase (se 3 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 521869 = 195701) (by norm_num)
theorem B521905 : Blo 463784 521905 := bbase (se 2 (by rfl) ⟨195714, by rfl⟩ : syracuseStep 521905 = 391429) (by norm_num)
theorem B2520757 : Blo 463784 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B1046213 : Blo 463784 1046213 := bbase (se 4 (by rfl) ⟨98082, by rfl⟩ : syracuseStep 1046213 = 196165) (by norm_num)
theorem B521941 : Blo 463784 521941 := bbase (se 7 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 521941 = 12233) (by norm_num)
theorem B784093 : Blo 463784 784093 := bbase (se 3 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 784093 = 294035) (by norm_num)
theorem B1177325 : Blo 463784 1177325 := bbase (se 3 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 1177325 = 441497) (by norm_num)
theorem B521977 : Blo 463784 521977 := bbase (se 2 (by rfl) ⟨195741, by rfl⟩ : syracuseStep 521977 = 391483) (by norm_num)
theorem B587513 : Blo 463784 587513 := bbase (se 2 (by rfl) ⟨220317, by rfl⟩ : syracuseStep 587513 = 440635) (by norm_num)
theorem B1046285 : Blo 463784 1046285 := bbase (se 3 (by rfl) ⟨196178, by rfl⟩ : syracuseStep 1046285 = 392357) (by norm_num)
theorem B522013 : Blo 463784 522013 := bbase (se 3 (by rfl) ⟨97877, by rfl⟩ : syracuseStep 522013 = 195755) (by norm_num)
theorem B849709 : Blo 463784 849709 := bbase (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) (by norm_num)
theorem B587569 : Blo 463784 587569 := bbase (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) (by norm_num)
theorem B784181 : Blo 463784 784181 := bbase (se 5 (by rfl) ⟨36758, by rfl⟩ : syracuseStep 784181 = 73517) (by norm_num)
theorem B882485 : Blo 463784 882485 := bbase (se 5 (by rfl) ⟨41366, by rfl⟩ : syracuseStep 882485 = 82733) (by norm_num)
theorem B522049 : Blo 463784 522049 := bbase (se 2 (by rfl) ⟨195768, by rfl⟩ : syracuseStep 522049 = 391537) (by norm_num)
theorem B1046357 : Blo 463784 1046357 := bbase (se 9 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 1046357 = 6131) (by norm_num)
theorem B522085 : Blo 463784 522085 := bbase (se 4 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 522085 = 97891) (by norm_num)
theorem B849773 : Blo 463784 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B522121 : Blo 463784 522121 := bbase (se 2 (by rfl) ⟨195795, by rfl⟩ : syracuseStep 522121 = 391591) (by norm_num)
theorem B587665 : Blo 463784 587665 := bbase (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) (by norm_num)
theorem B1046429 : Blo 463784 1046429 := bbase (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) (by norm_num)
theorem B522157 : Blo 463784 522157 := bbase (se 3 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 522157 = 195809) (by norm_num)
theorem B1177517 : Blo 463784 1177517 := bbase (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) (by norm_num)
theorem B784309 : Blo 463784 784309 := bbase (se 5 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 784309 = 73529) (by norm_num)
theorem B522193 : Blo 463784 522193 := bbase (se 2 (by rfl) ⟨195822, by rfl⟩ : syracuseStep 522193 = 391645) (by norm_num)
theorem B948181 : Blo 463784 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B1046501 : Blo 463784 1046501 := bbase (se 4 (by rfl) ⟨98109, by rfl⟩ : syracuseStep 1046501 = 196219) (by norm_num)
theorem B522229 : Blo 463784 522229 := bbase (se 5 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 522229 = 48959) (by norm_num)
theorem B1570805 : Blo 463784 1570805 := bbase (se 5 (by rfl) ⟨73631, by rfl⟩ : syracuseStep 1570805 = 147263) (by norm_num)
theorem B784397 : Blo 463784 784397 := bbase (se 3 (by rfl) ⟨147074, by rfl⟩ : syracuseStep 784397 = 294149) (by norm_num)
theorem B522265 : Blo 463784 522265 := bbase (se 2 (by rfl) ⟨195849, by rfl⟩ : syracuseStep 522265 = 391699) (by norm_num)
theorem B1046573 : Blo 463784 1046573 := bbase (se 3 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 1046573 = 392465) (by norm_num)
theorem B522301 : Blo 463784 522301 := bbase (se 3 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 522301 = 195863) (by norm_num)
theorem B587837 : Blo 463784 587837 := bbase (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) (by norm_num)
theorem B522337 : Blo 463784 522337 := bbase (se 2 (by rfl) ⟨195876, by rfl⟩ : syracuseStep 522337 = 391753) (by norm_num)
theorem B587893 : Blo 463784 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B1046645 : Blo 463784 1046645 := bbase (se 5 (by rfl) ⟨49061, by rfl⟩ : syracuseStep 1046645 = 98123) (by norm_num)
theorem B522373 : Blo 463784 522373 := bbase (se 4 (by rfl) ⟨48972, by rfl⟩ : syracuseStep 522373 = 97945) (by norm_num)
theorem B784525 : Blo 463784 784525 := bbase (se 3 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 784525 = 294197) (by norm_num)
theorem B522409 : Blo 463784 522409 := bbase (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) (by norm_num)
theorem B1046717 : Blo 463784 1046717 := bbase (se 3 (by rfl) ⟨196259, by rfl⟩ : syracuseStep 1046717 = 392519) (by norm_num)
theorem B522445 : Blo 463784 522445 := bbase (se 3 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 522445 = 195917) (by norm_num)
theorem B587989 : Blo 463784 587989 := bbase (se 7 (by rfl) ⟨6890, by rfl⟩ : syracuseStep 587989 = 13781) (by norm_num)
theorem B784613 : Blo 463784 784613 := bbase (se 4 (by rfl) ⟨73557, by rfl⟩ : syracuseStep 784613 = 147115) (by norm_num)
theorem B522481 : Blo 463784 522481 := bbase (se 2 (by rfl) ⟨195930, by rfl⟩ : syracuseStep 522481 = 391861) (by norm_num)
theorem B1046789 : Blo 463784 1046789 := bbase (se 4 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 1046789 = 196273) (by norm_num)
theorem B1177861 : Blo 463784 1177861 := bbase (se 4 (by rfl) ⟨110424, by rfl⟩ : syracuseStep 1177861 = 220849) (by norm_num)
theorem B522517 : Blo 463784 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B522553 : Blo 463784 522553 := bbase (se 2 (by rfl) ⟨195957, by rfl⟩ : syracuseStep 522553 = 391915) (by norm_num)
theorem B1046861 : Blo 463784 1046861 := bbase (se 3 (by rfl) ⟨196286, by rfl⟩ : syracuseStep 1046861 = 392573) (by norm_num)
theorem B522589 : Blo 463784 522589 := bbase (se 3 (by rfl) ⟨97985, by rfl⟩ : syracuseStep 522589 = 195971) (by norm_num)
theorem B784741 : Blo 463784 784741 := bbase (se 4 (by rfl) ⟨73569, by rfl⟩ : syracuseStep 784741 = 147139) (by norm_num)
theorem B1177973 : Blo 463784 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B522625 : Blo 463784 522625 := bbase (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) (by norm_num)
theorem B588161 : Blo 463784 588161 := bbase (se 2 (by rfl) ⟨220560, by rfl⟩ : syracuseStep 588161 = 441121) (by norm_num)
theorem B1046933 : Blo 463784 1046933 := bbase (se 6 (by rfl) ⟨24537, by rfl⟩ : syracuseStep 1046933 = 49075) (by norm_num)
theorem B2521493 : Blo 463784 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B522661 : Blo 463784 522661 := bbase (se 4 (by rfl) ⟨48999, by rfl⟩ : syracuseStep 522661 = 97999) (by norm_num)
theorem B1571237 : Blo 463784 1571237 := bbase (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) (by norm_num)
theorem B588217 : Blo 463784 588217 := bbase (se 2 (by rfl) ⟨220581, by rfl⟩ : syracuseStep 588217 = 441163) (by norm_num)
theorem B784829 : Blo 463784 784829 := bbase (se 3 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 784829 = 294311) (by norm_num)
theorem B522697 : Blo 463784 522697 := bbase (se 2 (by rfl) ⟨196011, by rfl⟩ : syracuseStep 522697 = 392023) (by norm_num)
theorem B1047005 : Blo 463784 1047005 := bbase (se 3 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 1047005 = 392627) (by norm_num)
theorem B522733 : Blo 463784 522733 := bbase (se 3 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 522733 = 196025) (by norm_num)
theorem B522769 : Blo 463784 522769 := bbase (se 2 (by rfl) ⟨196038, by rfl⟩ : syracuseStep 522769 = 392077) (by norm_num)
theorem B588313 : Blo 463784 588313 := bbase (se 2 (by rfl) ⟨220617, by rfl⟩ : syracuseStep 588313 = 441235) (by norm_num)
theorem B883237 : Blo 463784 883237 := bbase (se 4 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 883237 = 165607) (by norm_num)
theorem B1047077 : Blo 463784 1047077 := bbase (se 4 (by rfl) ⟨98163, by rfl⟩ : syracuseStep 1047077 = 196327) (by norm_num)
theorem B522805 : Blo 463784 522805 := bbase (se 5 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 522805 = 49013) (by norm_num)
theorem B1178165 : Blo 463784 1178165 := bbase (se 5 (by rfl) ⟨55226, by rfl⟩ : syracuseStep 1178165 = 110453) (by norm_num)
theorem B784957 : Blo 463784 784957 := bbase (se 3 (by rfl) ⟨147179, by rfl⟩ : syracuseStep 784957 = 294359) (by norm_num)
theorem B522841 : Blo 463784 522841 := bbase (se 2 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 522841 = 392131) (by norm_num)
theorem B1047149 : Blo 463784 1047149 := bbase (se 3 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 1047149 = 392681) (by norm_num)
theorem B522877 : Blo 463784 522877 := bbase (se 3 (by rfl) ⟨98039, by rfl⟩ : syracuseStep 522877 = 196079) (by norm_num)
theorem B785045 : Blo 463784 785045 := bbase (se 6 (by rfl) ⟨18399, by rfl⟩ : syracuseStep 785045 = 36799) (by norm_num)
theorem B2357909 : Blo 463784 2357909 := bbase (se 6 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 2357909 = 110527) (by norm_num)
theorem B522913 : Blo 463784 522913 := bbase (se 2 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 522913 = 392185) (by norm_num)
theorem B883381 : Blo 463784 883381 := bbase (se 5 (by rfl) ⟨41408, by rfl⟩ : syracuseStep 883381 = 82817) (by norm_num)
theorem B1047221 : Blo 463784 1047221 := bbase (se 5 (by rfl) ⟨49088, by rfl⟩ : syracuseStep 1047221 = 98177) (by norm_num)
theorem B522949 : Blo 463784 522949 := bbase (se 4 (by rfl) ⟨49026, by rfl⟩ : syracuseStep 522949 = 98053) (by norm_num)
theorem B588485 : Blo 463784 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B522985 : Blo 463784 522985 := bbase (se 2 (by rfl) ⟨196119, by rfl⟩ : syracuseStep 522985 = 392239) (by norm_num)
theorem B588541 : Blo 463784 588541 := bbase (se 3 (by rfl) ⟨110351, by rfl⟩ : syracuseStep 588541 = 220703) (by norm_num)
theorem B1047293 : Blo 463784 1047293 := bbase (se 3 (by rfl) ⟨196367, by rfl⟩ : syracuseStep 1047293 = 392735) (by norm_num)
theorem B523021 : Blo 463784 523021 := bbase (se 3 (by rfl) ⟨98066, by rfl⟩ : syracuseStep 523021 = 196133) (by norm_num)
theorem B785173 : Blo 463784 785173 := bbase (se 6 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 785173 = 36805) (by norm_num)
theorem B523057 : Blo 463784 523057 := bbase (se 2 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 523057 = 392293) (by norm_num)
theorem B1997621 : Blo 463784 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B1047365 : Blo 463784 1047365 := bbase (se 4 (by rfl) ⟨98190, by rfl⟩ : syracuseStep 1047365 = 196381) (by norm_num)
theorem B523093 : Blo 463784 523093 := bbase (se 9 (by rfl) ⟨1532, by rfl⟩ : syracuseStep 523093 = 3065) (by norm_num)
theorem B883541 : Blo 463784 883541 := bbase (se 9 (by rfl) ⟨2588, by rfl⟩ : syracuseStep 883541 = 5177) (by norm_num)
theorem B1571669 : Blo 463784 1571669 := bbase (se 9 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 1571669 = 9209) (by norm_num)
theorem B2653013 : Blo 463784 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B588637 : Blo 463784 588637 := bbase (se 3 (by rfl) ⟨110369, by rfl⟩ : syracuseStep 588637 = 220739) (by norm_num)
theorem B785261 : Blo 463784 785261 := bbase (se 3 (by rfl) ⟨147236, by rfl⟩ : syracuseStep 785261 = 294473) (by norm_num)
theorem B523129 : Blo 463784 523129 := bbase (se 2 (by rfl) ⟨196173, by rfl⟩ : syracuseStep 523129 = 392347) (by norm_num)
theorem B1047437 : Blo 463784 1047437 := bbase (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) (by norm_num)
theorem B1178509 : Blo 463784 1178509 := bbase (se 3 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 1178509 = 441941) (by norm_num)
theorem B523165 : Blo 463784 523165 := bbase (se 3 (by rfl) ⟨98093, by rfl⟩ : syracuseStep 523165 = 196187) (by norm_num)
theorem B523201 : Blo 463784 523201 := bbase (se 2 (by rfl) ⟨196200, by rfl⟩ : syracuseStep 523201 = 392401) (by norm_num)
theorem B1047509 : Blo 463784 1047509 := bbase (se 7 (by rfl) ⟨12275, by rfl⟩ : syracuseStep 1047509 = 24551) (by norm_num)
theorem B523237 : Blo 463784 523237 := bbase (se 4 (by rfl) ⟨49053, by rfl⟩ : syracuseStep 523237 = 98107) (by norm_num)
theorem B883685 : Blo 463784 883685 := bbase (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) (by norm_num)
theorem B785389 : Blo 463784 785389 := bbase (se 3 (by rfl) ⟨147260, by rfl⟩ : syracuseStep 785389 = 294521) (by norm_num)
theorem B1178621 : Blo 463784 1178621 := bbase (se 3 (by rfl) ⟨220991, by rfl⟩ : syracuseStep 1178621 = 441983) (by norm_num)
theorem B523273 : Blo 463784 523273 := bbase (se 2 (by rfl) ⟨196227, by rfl⟩ : syracuseStep 523273 = 392455) (by norm_num)
theorem B588809 : Blo 463784 588809 := bbase (se 2 (by rfl) ⟨220803, by rfl⟩ : syracuseStep 588809 = 441607) (by norm_num)
theorem B1047581 : Blo 463784 1047581 := bbase (se 3 (by rfl) ⟨196421, by rfl⟩ : syracuseStep 1047581 = 392843) (by norm_num)
theorem B523309 : Blo 463784 523309 := bbase (se 3 (by rfl) ⟨98120, by rfl⟩ : syracuseStep 523309 = 196241) (by norm_num)
theorem B588865 : Blo 463784 588865 := bbase (se 2 (by rfl) ⟨220824, by rfl⟩ : syracuseStep 588865 = 441649) (by norm_num)
theorem B785477 : Blo 463784 785477 := bbase (se 4 (by rfl) ⟨73638, by rfl⟩ : syracuseStep 785477 = 147277) (by norm_num)
theorem B523345 : Blo 463784 523345 := bbase (se 2 (by rfl) ⟨196254, by rfl⟩ : syracuseStep 523345 = 392509) (by norm_num)
theorem B1047653 : Blo 463784 1047653 := bbase (se 4 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 1047653 = 196435) (by norm_num)
theorem B523381 : Blo 463784 523381 := bbase (se 5 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 523381 = 49067) (by norm_num)
theorem B523417 : Blo 463784 523417 := bbase (se 2 (by rfl) ⟨196281, by rfl⟩ : syracuseStep 523417 = 392563) (by norm_num)
theorem B588961 : Blo 463784 588961 := bbase (se 2 (by rfl) ⟨220860, by rfl⟩ : syracuseStep 588961 = 441721) (by norm_num)
theorem B1047725 : Blo 463784 1047725 := bbase (se 3 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 1047725 = 392897) (by norm_num)
theorem B523453 : Blo 463784 523453 := bbase (se 3 (by rfl) ⟨98147, by rfl⟩ : syracuseStep 523453 = 196295) (by norm_num)
theorem B1178813 : Blo 463784 1178813 := bbase (se 3 (by rfl) ⟨221027, by rfl⟩ : syracuseStep 1178813 = 442055) (by norm_num)
theorem B785605 : Blo 463784 785605 := bbase (se 4 (by rfl) ⟨73650, by rfl⟩ : syracuseStep 785605 = 147301) (by norm_num)
theorem B1768661 : Blo 463784 1768661 := bbase (se 7 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 1768661 = 41453) (by norm_num)
theorem B523489 : Blo 463784 523489 := bbase (se 2 (by rfl) ⟨196308, by rfl⟩ : syracuseStep 523489 = 392617) (by norm_num)
theorem B1047797 : Blo 463784 1047797 := bbase (se 5 (by rfl) ⟨49115, by rfl⟩ : syracuseStep 1047797 = 98231) (by norm_num)
theorem B523525 : Blo 463784 523525 := bbase (se 4 (by rfl) ⟨49080, by rfl⟩ : syracuseStep 523525 = 98161) (by norm_num)
theorem B883973 : Blo 463784 883973 := bbase (se 4 (by rfl) ⟨82872, by rfl⟩ : syracuseStep 883973 = 165745) (by norm_num)
theorem B1572101 : Blo 463784 1572101 := bbase (se 4 (by rfl) ⟨147384, by rfl⟩ : syracuseStep 1572101 = 294769) (by norm_num)
theorem B785693 : Blo 463784 785693 := bbase (se 3 (by rfl) ⟨147317, by rfl⟩ : syracuseStep 785693 = 294635) (by norm_num)
theorem B523561 : Blo 463784 523561 := bbase (se 2 (by rfl) ⟨196335, by rfl⟩ : syracuseStep 523561 = 392671) (by norm_num)
theorem B1047869 : Blo 463784 1047869 := bbase (se 3 (by rfl) ⟨196475, by rfl⟩ : syracuseStep 1047869 = 392951) (by norm_num)
theorem B523597 : Blo 463784 523597 := bbase (se 3 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 523597 = 196349) (by norm_num)
theorem B589133 : Blo 463784 589133 := bbase (se 3 (by rfl) ⟨110462, by rfl⟩ : syracuseStep 589133 = 220925) (by norm_num)
theorem B523633 : Blo 463784 523633 := bbase (se 2 (by rfl) ⟨196362, by rfl⟩ : syracuseStep 523633 = 392725) (by norm_num)
theorem B589189 : Blo 463784 589189 := bbase (se 4 (by rfl) ⟨55236, by rfl⟩ : syracuseStep 589189 = 110473) (by norm_num)
theorem B1047941 : Blo 463784 1047941 := bbase (se 4 (by rfl) ⟨98244, by rfl⟩ : syracuseStep 1047941 = 196489) (by norm_num)
theorem B523669 : Blo 463784 523669 := bbase (se 6 (by rfl) ⟨12273, by rfl⟩ : syracuseStep 523669 = 24547) (by norm_num)
theorem B785821 : Blo 463784 785821 := bbase (se 3 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 785821 = 294683) (by norm_num)
theorem B884125 : Blo 463784 884125 := bbase (se 3 (by rfl) ⟨165773, by rfl⟩ : syracuseStep 884125 = 331547) (by norm_num)
theorem B523705 : Blo 463784 523705 := bbase (se 2 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 523705 = 392779) (by norm_num)
theorem B1048013 : Blo 463784 1048013 := bbase (se 3 (by rfl) ⟨196502, by rfl⟩ : syracuseStep 1048013 = 393005) (by norm_num)
theorem B523741 : Blo 463784 523741 := bbase (se 3 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 523741 = 196403) (by norm_num)
theorem B589285 : Blo 463784 589285 := bbase (se 4 (by rfl) ⟨55245, by rfl⟩ : syracuseStep 589285 = 110491) (by norm_num)
theorem B785909 : Blo 463784 785909 := bbase (se 5 (by rfl) ⟨36839, by rfl⟩ : syracuseStep 785909 = 73679) (by norm_num)
theorem B1768949 : Blo 463784 1768949 := bbase (se 5 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 1768949 = 165839) (by norm_num)
theorem B523777 : Blo 463784 523777 := bbase (se 2 (by rfl) ⟨196416, by rfl⟩ : syracuseStep 523777 = 392833) (by norm_num)
theorem B1048085 : Blo 463784 1048085 := bbase (se 6 (by rfl) ⟨24564, by rfl⟩ : syracuseStep 1048085 = 49129) (by norm_num)
theorem B1179157 : Blo 463784 1179157 := bbase (se 6 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 1179157 = 55273) (by norm_num)
theorem B523813 : Blo 463784 523813 := bbase (se 4 (by rfl) ⟨49107, by rfl⟩ : syracuseStep 523813 = 98215) (by norm_num)
theorem B523849 : Blo 463784 523849 := bbase (se 2 (by rfl) ⟨196443, by rfl⟩ : syracuseStep 523849 = 392887) (by norm_num)
theorem B1048157 : Blo 463784 1048157 := bbase (se 3 (by rfl) ⟨196529, by rfl⟩ : syracuseStep 1048157 = 393059) (by norm_num)
theorem B523885 : Blo 463784 523885 := bbase (se 3 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 523885 = 196457) (by norm_num)
theorem B786037 : Blo 463784 786037 := bbase (se 5 (by rfl) ⟨36845, by rfl⟩ : syracuseStep 786037 = 73691) (by norm_num)
theorem B1179269 : Blo 463784 1179269 := bbase (se 4 (by rfl) ⟨110556, by rfl⟩ : syracuseStep 1179269 = 221113) (by norm_num)
theorem B523921 : Blo 463784 523921 := bbase (se 2 (by rfl) ⟨196470, by rfl⟩ : syracuseStep 523921 = 392941) (by norm_num)
theorem B589457 : Blo 463784 589457 := bbase (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) (by norm_num)
theorem B1048229 : Blo 463784 1048229 := bbase (se 4 (by rfl) ⟨98271, by rfl⟩ : syracuseStep 1048229 = 196543) (by norm_num)
theorem B523957 : Blo 463784 523957 := bbase (se 5 (by rfl) ⟨24560, by rfl⟩ : syracuseStep 523957 = 49121) (by norm_num)
theorem B1572533 : Blo 463784 1572533 := bbase (se 5 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 1572533 = 147425) (by norm_num)
theorem B589513 : Blo 463784 589513 := bbase (se 2 (by rfl) ⟨221067, by rfl⟩ : syracuseStep 589513 = 442135) (by norm_num)
theorem B786125 : Blo 463784 786125 := bbase (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) (by norm_num)
theorem B884429 : Blo 463784 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B523993 : Blo 463784 523993 := bbase (se 2 (by rfl) ⟨196497, by rfl⟩ : syracuseStep 523993 = 392995) (by norm_num)
theorem B1048301 : Blo 463784 1048301 := bbase (se 3 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 1048301 = 393113) (by norm_num)
theorem B524029 : Blo 463784 524029 := bbase (se 3 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 524029 = 196511) (by norm_num)
theorem B524065 : Blo 463784 524065 := bbase (se 2 (by rfl) ⟨196524, by rfl⟩ : syracuseStep 524065 = 393049) (by norm_num)
theorem B589609 : Blo 463784 589609 := bbase (se 2 (by rfl) ⟨221103, by rfl⟩ : syracuseStep 589609 = 442207) (by norm_num)
theorem B1048373 : Blo 463784 1048373 := bbase (se 5 (by rfl) ⟨49142, by rfl⟩ : syracuseStep 1048373 = 98285) (by norm_num)
theorem B524101 : Blo 463784 524101 := bbase (se 4 (by rfl) ⟨49134, by rfl⟩ : syracuseStep 524101 = 98269) (by norm_num)
theorem B1179461 : Blo 463784 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B786253 : Blo 463784 786253 := bbase (se 3 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 786253 = 294845) (by norm_num)
theorem B524137 : Blo 463784 524137 := bbase (se 2 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 524137 = 393103) (by norm_num)
theorem B1048445 : Blo 463784 1048445 := bbase (se 3 (by rfl) ⟨196583, by rfl⟩ : syracuseStep 1048445 = 393167) (by norm_num)
theorem B524173 : Blo 463784 524173 := bbase (se 3 (by rfl) ⟨98282, by rfl⟩ : syracuseStep 524173 = 196565) (by norm_num)
theorem B786341 : Blo 463784 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B2359205 : Blo 463784 2359205 := bbase (se 4 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 2359205 = 442351) (by norm_num)
theorem B524209 : Blo 463784 524209 := bbase (se 2 (by rfl) ⟨196578, by rfl⟩ : syracuseStep 524209 = 393157) (by norm_num)
theorem B1048517 : Blo 463784 1048517 := bbase (se 4 (by rfl) ⟨98298, by rfl⟩ : syracuseStep 1048517 = 196597) (by norm_num)
theorem B5046229 : Blo 463784 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B524245 : Blo 463784 524245 := bbase (se 7 (by rfl) ⟨6143, by rfl⟩ : syracuseStep 524245 = 12287) (by norm_num)
theorem B589781 : Blo 463784 589781 := bbase (se 7 (by rfl) ⟨6911, by rfl⟩ : syracuseStep 589781 = 13823) (by norm_num)
theorem B786449 : Blo 463784 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B1048625 : Blo 463784 1048625 := bstep (se 2 (by rfl) ⟨393234, by rfl⟩ : syracuseStep 1048625 = 786469) B786469
theorem B1048643 : Blo 463784 1048643 := bstep (se 1 (by rfl) ⟨786482, by rfl⟩ : syracuseStep 1048643 = 1572965) B1572965
theorem B524371 : Blo 463784 524371 := bstep (se 1 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 524371 = 786557) B786557
theorem B786577 : Blo 463784 786577 := bstep (se 2 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 786577 = 589933) B589933
theorem B786611 : Blo 463784 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B1573073 : Blo 463784 1573073 := bstep (se 2 (by rfl) ⟨589902, by rfl⟩ : syracuseStep 1573073 = 1179805) B1179805
theorem B884945 : Blo 463784 884945 := bstep (se 2 (by rfl) ⟨331854, by rfl⟩ : syracuseStep 884945 = 663709) B663709
theorem B524515 : Blo 463784 524515 := bstep (se 1 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 524515 = 786773) B786773
theorem B1147139 : Blo 463784 1147139 := bstep (se 1 (by rfl) ⟨860354, by rfl⟩ : syracuseStep 1147139 = 1720709) B1720709
theorem B786739 : Blo 463784 786739 := bstep (se 1 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 786739 = 1180109) B1180109
theorem B1048913 : Blo 463784 1048913 := bstep (se 2 (by rfl) ⟨393342, by rfl⟩ : syracuseStep 1048913 = 786685) B786685
theorem B1048931 : Blo 463784 1048931 := bstep (se 1 (by rfl) ⟨786698, by rfl⟩ : syracuseStep 1048931 = 1573397) B1573397
theorem B524659 : Blo 463784 524659 := bstep (se 1 (by rfl) ⟨393494, by rfl⟩ : syracuseStep 524659 = 786989) B786989
theorem B786881 : Blo 463784 786881 := bstep (se 2 (by rfl) ⟨295080, by rfl⟩ : syracuseStep 786881 = 590161) B590161
theorem B590323 : Blo 463784 590323 := bstep (se 1 (by rfl) ⟨442742, by rfl⟩ : syracuseStep 590323 = 885485) B885485
theorem B524803 : Blo 463784 524803 := bstep (se 1 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 524803 = 787205) B787205
theorem B787009 : Blo 463784 787009 := bstep (se 2 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 787009 = 590257) B590257
theorem B1180241 : Blo 463784 1180241 := bstep (se 2 (by rfl) ⟨442590, by rfl⟩ : syracuseStep 1180241 = 885181) B885181
theorem B590419 : Blo 463784 590419 := bstep (se 1 (by rfl) ⟨442814, by rfl⟩ : syracuseStep 590419 = 885629) B885629
theorem B787043 : Blo 463784 787043 := bstep (se 1 (by rfl) ⟨590282, by rfl⟩ : syracuseStep 787043 = 1180565) B1180565
theorem B1049201 : Blo 463784 1049201 := bstep (se 2 (by rfl) ⟨393450, by rfl⟩ : syracuseStep 1049201 = 786901) B786901
theorem B1180291 : Blo 463784 1180291 := bstep (se 1 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 1180291 = 1770437) B1770437
theorem B1049219 : Blo 463784 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B524947 : Blo 463784 524947 := bstep (se 1 (by rfl) ⟨393710, by rfl⟩ : syracuseStep 524947 = 787421) B787421
theorem B6062789 : Blo 463784 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B787171 : Blo 463784 787171 := bstep (se 1 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 787171 = 1180757) B1180757
theorem B1573613 : Blo 463784 1573613 := bstep (se 3 (by rfl) ⟨295052, by rfl⟩ : syracuseStep 1573613 = 590105) B590105
theorem B1180433 : Blo 463784 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1573667 : Blo 463784 1573667 := bstep (se 1 (by rfl) ⟨1180250, by rfl⟩ : syracuseStep 1573667 = 2360501) B2360501
theorem B525091 : Blo 463784 525091 := bstep (se 1 (by rfl) ⟨393818, by rfl⟩ : syracuseStep 525091 = 787637) B787637
theorem B2360177 : Blo 463784 2360177 := bstep (se 2 (by rfl) ⟨885066, by rfl⟩ : syracuseStep 2360177 = 1770133) B1770133
theorem B787313 : Blo 463784 787313 := bstep (se 2 (by rfl) ⟨295242, by rfl⟩ : syracuseStep 787313 = 590485) B590485
theorem B1049489 : Blo 463784 1049489 := bstep (se 2 (by rfl) ⟨393558, by rfl⟩ : syracuseStep 1049489 = 787117) B787117
theorem B1049507 : Blo 463784 1049507 := bstep (se 1 (by rfl) ⟨787130, by rfl⟩ : syracuseStep 1049507 = 1574261) B1574261
theorem B885667 : Blo 463784 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B525235 : Blo 463784 525235 := bstep (se 1 (by rfl) ⟨393926, by rfl⟩ : syracuseStep 525235 = 787853) B787853
theorem B787441 : Blo 463784 787441 := bstep (se 2 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 787441 = 590581) B590581
theorem B787475 : Blo 463784 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B1573937 : Blo 463784 1573937 := bstep (se 2 (by rfl) ⟨590226, by rfl⟩ : syracuseStep 1573937 = 1180453) B1180453
theorem B590915 : Blo 463784 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B525379 : Blo 463784 525379 := bstep (se 1 (by rfl) ⟨394034, by rfl⟩ : syracuseStep 525379 = 788069) B788069
theorem B4457585 : Blo 463784 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B2393201 : Blo 463784 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B787603 : Blo 463784 787603 := bstep (se 1 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 787603 = 1181405) B1181405
theorem B1049777 : Blo 463784 1049777 := bstep (se 2 (by rfl) ⟨393666, by rfl⟩ : syracuseStep 1049777 = 787333) B787333
theorem B1049795 : Blo 463784 1049795 := bstep (se 1 (by rfl) ⟨787346, by rfl⟩ : syracuseStep 1049795 = 1574693) B1574693
theorem B525523 : Blo 463784 525523 := bstep (se 1 (by rfl) ⟨394142, by rfl⟩ : syracuseStep 525523 = 788285) B788285
theorem B1672433 : Blo 463784 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B787745 : Blo 463784 787745 := bstep (se 2 (by rfl) ⟨295404, by rfl⟩ : syracuseStep 787745 = 590809) B590809
theorem B1115473 : Blo 463784 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B886115 : Blo 463784 886115 := bstep (se 1 (by rfl) ⟨664586, by rfl⟩ : syracuseStep 886115 = 1329173) B1329173
theorem B525667 : Blo 463784 525667 := bstep (se 1 (by rfl) ⟨394250, by rfl⟩ : syracuseStep 525667 = 788501) B788501
theorem B1770893 : Blo 463784 1770893 := bstep (se 3 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 1770893 = 664085) B664085
theorem B787873 : Blo 463784 787873 := bstep (se 2 (by rfl) ⟨295452, by rfl⟩ : syracuseStep 787873 = 590905) B590905
theorem B787907 : Blo 463784 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B1050065 : Blo 463784 1050065 := bstep (se 2 (by rfl) ⟨393774, by rfl⟩ : syracuseStep 1050065 = 787549) B787549
theorem B1050083 : Blo 463784 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B525811 : Blo 463784 525811 := bstep (se 1 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 525811 = 788717) B788717
theorem B558659 : Blo 463784 558659 := bstep (se 1 (by rfl) ⟨418994, by rfl⟩ : syracuseStep 558659 = 837989) B837989
theorem B788035 : Blo 463784 788035 := bstep (se 1 (by rfl) ⟨591026, by rfl⟩ : syracuseStep 788035 = 1182053) B1182053
theorem B1574477 : Blo 463784 1574477 := bstep (se 3 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 1574477 = 590429) B590429
theorem B1574531 : Blo 463784 1574531 := bstep (se 1 (by rfl) ⟨1180898, by rfl⟩ : syracuseStep 1574531 = 2361797) B2361797
theorem B886403 : Blo 463784 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B525955 : Blo 463784 525955 := bstep (se 1 (by rfl) ⟨394466, by rfl⟩ : syracuseStep 525955 = 788933) B788933
theorem B788177 : Blo 463784 788177 := bstep (se 2 (by rfl) ⟨295566, by rfl⟩ : syracuseStep 788177 = 591133) B591133
theorem B1181425 : Blo 463784 1181425 := bstep (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) B886069
theorem B1050353 : Blo 463784 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B1050371 : Blo 463784 1050371 := bstep (se 1 (by rfl) ⟨787778, by rfl⟩ : syracuseStep 1050371 = 1575557) B1575557
theorem B591619 : Blo 463784 591619 := bstep (se 1 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 591619 = 887429) B887429
theorem B526099 : Blo 463784 526099 := bstep (se 1 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 526099 = 789149) B789149
theorem B788305 : Blo 463784 788305 := bstep (se 2 (by rfl) ⟨295614, by rfl⟩ : syracuseStep 788305 = 591229) B591229
theorem B591715 : Blo 463784 591715 := bstep (se 1 (by rfl) ⟨443786, by rfl⟩ : syracuseStep 591715 = 887573) B887573
theorem B788339 : Blo 463784 788339 := bstep (se 1 (by rfl) ⟨591254, by rfl⟩ : syracuseStep 788339 = 1182509) B1182509
theorem B1574801 : Blo 463784 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B526243 : Blo 463784 526243 := bstep (se 1 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 526243 = 789365) B789365
theorem B788467 : Blo 463784 788467 := bstep (se 1 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 788467 = 1182701) B1182701
theorem B1181699 : Blo 463784 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B4458509 : Blo 463784 4458509 := bstep (se 3 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 4458509 = 1671941) B1671941
theorem B1050641 : Blo 463784 1050641 := bstep (se 2 (by rfl) ⟨393990, by rfl⟩ : syracuseStep 1050641 = 787981) B787981
theorem B1050659 : Blo 463784 1050659 := bstep (se 1 (by rfl) ⟨787994, by rfl⟩ : syracuseStep 1050659 = 1575989) B1575989
theorem B788609 : Blo 463784 788609 := bstep (se 2 (by rfl) ⟨295728, by rfl⟩ : syracuseStep 788609 = 591457) B591457
theorem B1181891 : Blo 463784 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B788737 : Blo 463784 788737 := bstep (se 2 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 788737 = 591553) B591553
theorem B2361635 : Blo 463784 2361635 := bstep (se 1 (by rfl) ⟨1771226, by rfl⟩ : syracuseStep 2361635 = 3542453) B3542453
theorem B788771 : Blo 463784 788771 := bstep (se 1 (by rfl) ⟨591578, by rfl⟩ : syracuseStep 788771 = 1183157) B1183157
theorem B1050929 : Blo 463784 1050929 := bstep (se 2 (by rfl) ⟨394098, by rfl⟩ : syracuseStep 1050929 = 788197) B788197
theorem B1050947 : Blo 463784 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1411469 : Blo 463784 1411469 := bstep (se 3 (by rfl) ⟨264650, by rfl⟩ : syracuseStep 1411469 = 529301) B529301
theorem B788899 : Blo 463784 788899 := bstep (se 1 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 788899 = 1183349) B1183349
theorem B1575341 : Blo 463784 1575341 := bstep (se 3 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 1575341 = 590753) B590753
theorem B1575395 : Blo 463784 1575395 := bstep (se 1 (by rfl) ⟨1181546, by rfl⟩ : syracuseStep 1575395 = 2363093) B2363093
theorem B887345 : Blo 463784 887345 := bstep (se 2 (by rfl) ⟨332754, by rfl⟩ : syracuseStep 887345 = 665509) B665509
theorem B789041 : Blo 463784 789041 := bstep (se 2 (by rfl) ⟨295890, by rfl⟩ : syracuseStep 789041 = 591781) B591781
theorem B1051217 : Blo 463784 1051217 := bstep (se 2 (by rfl) ⟨394206, by rfl⟩ : syracuseStep 1051217 = 788413) B788413
theorem B1051235 : Blo 463784 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B789169 : Blo 463784 789169 := bstep (se 2 (by rfl) ⟨295938, by rfl⟩ : syracuseStep 789169 = 591877) B591877
theorem B11340485 : Blo 463784 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B789203 : Blo 463784 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B2755313 : Blo 463784 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B1575665 : Blo 463784 1575665 := bstep (se 2 (by rfl) ⟨590874, by rfl⟩ : syracuseStep 1575665 = 1181749) B1181749
theorem B789331 : Blo 463784 789331 := bstep (se 1 (by rfl) ⟨591998, by rfl⟩ : syracuseStep 789331 = 1183997) B1183997
theorem B1051505 : Blo 463784 1051505 := bstep (se 2 (by rfl) ⟨394314, by rfl⟩ : syracuseStep 1051505 = 788629) B788629
theorem B1051523 : Blo 463784 1051523 := bstep (se 1 (by rfl) ⟨788642, by rfl⟩ : syracuseStep 1051523 = 1577285) B1577285
theorem B2984845 : Blo 463784 2984845 := bstep (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) B1119317
theorem B2362445 : Blo 463784 2362445 := bstep (se 3 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 2362445 = 885917) B885917
theorem B1182833 : Blo 463784 1182833 := bstep (se 2 (by rfl) ⟨443562, by rfl⟩ : syracuseStep 1182833 = 887125) B887125
theorem B1051793 : Blo 463784 1051793 := bstep (se 2 (by rfl) ⟨394422, by rfl⟩ : syracuseStep 1051793 = 788845) B788845
theorem B1182883 : Blo 463784 1182883 := bstep (se 1 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 1182883 = 1774325) B1774325
theorem B1051811 : Blo 463784 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B756913 : Blo 463784 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B1576205 : Blo 463784 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B1183025 : Blo 463784 1183025 := bstep (se 2 (by rfl) ⟨443634, by rfl⟩ : syracuseStep 1183025 = 887269) B887269
theorem B1576259 : Blo 463784 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B1052081 : Blo 463784 1052081 := bstep (se 2 (by rfl) ⟨394530, by rfl⟩ : syracuseStep 1052081 = 789061) B789061
theorem B1052099 : Blo 463784 1052099 := bstep (se 1 (by rfl) ⟨789074, by rfl⟩ : syracuseStep 1052099 = 1578149) B1578149
theorem B1576529 : Blo 463784 1576529 := bstep (se 2 (by rfl) ⟨591198, by rfl⟩ : syracuseStep 1576529 = 1182397) B1182397
theorem B3346019 : Blo 463784 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B1052369 : Blo 463784 1052369 := bstep (se 2 (by rfl) ⟨394638, by rfl⟩ : syracuseStep 1052369 = 789277) B789277
theorem B1052387 : Blo 463784 1052387 := bstep (se 1 (by rfl) ⟨789290, by rfl⟩ : syracuseStep 1052387 = 1578581) B1578581
theorem B560947 : Blo 463784 560947 := bstep (se 1 (by rfl) ⟨420710, by rfl⟩ : syracuseStep 560947 = 841421) B841421
theorem B561043 : Blo 463784 561043 := bstep (se 1 (by rfl) ⟨420782, by rfl⟩ : syracuseStep 561043 = 841565) B841565
theorem B561091 : Blo 463784 561091 := bstep (se 1 (by rfl) ⟨420818, by rfl⟩ : syracuseStep 561091 = 841637) B841637
theorem B6033379 : Blo 463784 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B5050421 : Blo 463784 5050421 := bstep (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) B473477
theorem B1577069 : Blo 463784 1577069 := bstep (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) B591401
theorem B1577123 : Blo 463784 1577123 := bstep (se 1 (by rfl) ⟨1182842, by rfl⟩ : syracuseStep 1577123 = 2365685) B2365685
theorem B1675505 : Blo 463784 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B1773809 : Blo 463784 1773809 := bstep (se 2 (by rfl) ⟨665178, by rfl⟩ : syracuseStep 1773809 = 1330357) B1330357
theorem B1184017 : Blo 463784 1184017 := bstep (se 2 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 1184017 = 888013) B888013
theorem B1675619 : Blo 463784 1675619 := bstep (se 1 (by rfl) ⟨1256714, by rfl⟩ : syracuseStep 1675619 = 2513429) B2513429
theorem B1577393 : Blo 463784 1577393 := bstep (se 2 (by rfl) ⟨591522, by rfl⟩ : syracuseStep 1577393 = 1183045) B1183045
theorem B7934435 : Blo 463784 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B5968565 : Blo 463784 5968565 := bstep (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) B559553
theorem B4494149 : Blo 463784 4494149 := bstep (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) B842653
theorem B463795 : Blo 463784 463795 := bstep (se 1 (by rfl) ⟨347846, by rfl⟩ : syracuseStep 463795 = 695693) B695693
theorem B463811 : Blo 463784 463811 := bstep (se 1 (by rfl) ⟨347858, by rfl⟩ : syracuseStep 463811 = 695717) B695717
theorem B2266061 : Blo 463784 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B1577933 : Blo 463784 1577933 := bstep (se 3 (by rfl) ⟨295862, by rfl⟩ : syracuseStep 1577933 = 591725) B591725
theorem B463827 : Blo 463784 463827 := bstep (se 1 (by rfl) ⟨347870, by rfl⟩ : syracuseStep 463827 = 695741) B695741
theorem B463843 : Blo 463784 463843 := bstep (se 1 (by rfl) ⟨347882, by rfl⟩ : syracuseStep 463843 = 695765) B695765
theorem B463859 : Blo 463784 463859 := bstep (se 1 (by rfl) ⟨347894, by rfl⟩ : syracuseStep 463859 = 695789) B695789
theorem B463875 : Blo 463784 463875 := bstep (se 1 (by rfl) ⟨347906, by rfl⟩ : syracuseStep 463875 = 695813) B695813
theorem B1577987 : Blo 463784 1577987 := bstep (se 1 (by rfl) ⟨1183490, by rfl⟩ : syracuseStep 1577987 = 2366981) B2366981
theorem B463891 : Blo 463784 463891 := bstep (se 1 (by rfl) ⟨347918, by rfl⟩ : syracuseStep 463891 = 695837) B695837
theorem B463907 : Blo 463784 463907 := bstep (se 1 (by rfl) ⟨347930, by rfl⟩ : syracuseStep 463907 = 695861) B695861
theorem B463923 : Blo 463784 463923 := bstep (se 1 (by rfl) ⟨347942, by rfl⟩ : syracuseStep 463923 = 695885) B695885
theorem B463939 : Blo 463784 463939 := bstep (se 1 (by rfl) ⟨347954, by rfl⟩ : syracuseStep 463939 = 695909) B695909
theorem B2987077 : Blo 463784 2987077 := bstep (se 4 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 2987077 = 560077) B560077
theorem B463955 : Blo 463784 463955 := bstep (se 1 (by rfl) ⟨347966, by rfl⟩ : syracuseStep 463955 = 695933) B695933
theorem B660577 : Blo 463784 660577 := bstep (se 2 (by rfl) ⟨247716, by rfl⟩ : syracuseStep 660577 = 495433) B495433
theorem B463971 : Blo 463784 463971 := bstep (se 1 (by rfl) ⟨347978, by rfl⟩ : syracuseStep 463971 = 695957) B695957
theorem B463987 : Blo 463784 463987 := bstep (se 1 (by rfl) ⟨347990, by rfl⟩ : syracuseStep 463987 = 695981) B695981
theorem B464003 : Blo 463784 464003 := bstep (se 1 (by rfl) ⟨348002, by rfl⟩ : syracuseStep 464003 = 696005) B696005
theorem B464019 : Blo 463784 464019 := bstep (se 1 (by rfl) ⟨348014, by rfl⟩ : syracuseStep 464019 = 696029) B696029
theorem B464035 : Blo 463784 464035 := bstep (se 1 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 464035 = 696053) B696053
theorem B1119395 : Blo 463784 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B464051 : Blo 463784 464051 := bstep (se 1 (by rfl) ⟨348038, by rfl⟩ : syracuseStep 464051 = 696077) B696077
theorem B464067 : Blo 463784 464067 := bstep (se 1 (by rfl) ⟨348050, by rfl⟩ : syracuseStep 464067 = 696101) B696101
theorem B464083 : Blo 463784 464083 := bstep (se 1 (by rfl) ⟨348062, by rfl⟩ : syracuseStep 464083 = 696125) B696125
theorem B464099 : Blo 463784 464099 := bstep (se 1 (by rfl) ⟨348074, by rfl⟩ : syracuseStep 464099 = 696149) B696149
theorem B2528497 : Blo 463784 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B464115 : Blo 463784 464115 := bstep (se 1 (by rfl) ⟨348086, by rfl⟩ : syracuseStep 464115 = 696173) B696173
theorem B464131 : Blo 463784 464131 := bstep (se 1 (by rfl) ⟨348098, by rfl⟩ : syracuseStep 464131 = 696197) B696197
theorem B1578257 : Blo 463784 1578257 := bstep (se 2 (by rfl) ⟨591846, by rfl⟩ : syracuseStep 1578257 = 1183693) B1183693
theorem B464147 : Blo 463784 464147 := bstep (se 1 (by rfl) ⟨348110, by rfl⟩ : syracuseStep 464147 = 696221) B696221
theorem B464163 : Blo 463784 464163 := bstep (se 1 (by rfl) ⟨348122, by rfl⟩ : syracuseStep 464163 = 696245) B696245
theorem B464179 : Blo 463784 464179 := bstep (se 1 (by rfl) ⟨348134, by rfl⟩ : syracuseStep 464179 = 696269) B696269
theorem B464195 : Blo 463784 464195 := bstep (se 1 (by rfl) ⟨348146, by rfl⟩ : syracuseStep 464195 = 696293) B696293
theorem B1611085 : Blo 463784 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B464211 : Blo 463784 464211 := bstep (se 1 (by rfl) ⟨348158, by rfl⟩ : syracuseStep 464211 = 696317) B696317
theorem B464227 : Blo 463784 464227 := bstep (se 1 (by rfl) ⟨348170, by rfl⟩ : syracuseStep 464227 = 696341) B696341
theorem B464243 : Blo 463784 464243 := bstep (se 1 (by rfl) ⟨348182, by rfl⟩ : syracuseStep 464243 = 696365) B696365
theorem B464259 : Blo 463784 464259 := bstep (se 1 (by rfl) ⟨348194, by rfl⟩ : syracuseStep 464259 = 696389) B696389
theorem B464275 : Blo 463784 464275 := bstep (se 1 (by rfl) ⟨348206, by rfl⟩ : syracuseStep 464275 = 696413) B696413
theorem B464291 : Blo 463784 464291 := bstep (se 1 (by rfl) ⟨348218, by rfl⟩ : syracuseStep 464291 = 696437) B696437
theorem B464307 : Blo 463784 464307 := bstep (se 1 (by rfl) ⟨348230, by rfl⟩ : syracuseStep 464307 = 696461) B696461
theorem B464323 : Blo 463784 464323 := bstep (se 1 (by rfl) ⟨348242, by rfl⟩ : syracuseStep 464323 = 696485) B696485
theorem B464339 : Blo 463784 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B497107 : Blo 463784 497107 := bstep (se 1 (by rfl) ⟨372830, by rfl⟩ : syracuseStep 497107 = 745661) B745661
theorem B464355 : Blo 463784 464355 := bstep (se 1 (by rfl) ⟨348266, by rfl⟩ : syracuseStep 464355 = 696533) B696533
theorem B464371 : Blo 463784 464371 := bstep (se 1 (by rfl) ⟨348278, by rfl⟩ : syracuseStep 464371 = 696557) B696557
theorem B464387 : Blo 463784 464387 := bstep (se 1 (by rfl) ⟨348290, by rfl⟩ : syracuseStep 464387 = 696581) B696581
theorem B464403 : Blo 463784 464403 := bstep (se 1 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 464403 = 696605) B696605
theorem B464419 : Blo 463784 464419 := bstep (se 1 (by rfl) ⟨348314, by rfl⟩ : syracuseStep 464419 = 696629) B696629
theorem B464435 : Blo 463784 464435 := bstep (se 1 (by rfl) ⟨348326, by rfl⟩ : syracuseStep 464435 = 696653) B696653
theorem B464451 : Blo 463784 464451 := bstep (se 1 (by rfl) ⟨348338, by rfl⟩ : syracuseStep 464451 = 696677) B696677
theorem B464467 : Blo 463784 464467 := bstep (se 1 (by rfl) ⟨348350, by rfl⟩ : syracuseStep 464467 = 696701) B696701
theorem B464483 : Blo 463784 464483 := bstep (se 1 (by rfl) ⟨348362, by rfl⟩ : syracuseStep 464483 = 696725) B696725
theorem B2692721 : Blo 463784 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B464499 : Blo 463784 464499 := bstep (se 1 (by rfl) ⟨348374, by rfl⟩ : syracuseStep 464499 = 696749) B696749
theorem B464515 : Blo 463784 464515 := bstep (se 1 (by rfl) ⟨348386, by rfl⟩ : syracuseStep 464515 = 696773) B696773
theorem B464531 : Blo 463784 464531 := bstep (se 1 (by rfl) ⟨348398, by rfl⟩ : syracuseStep 464531 = 696797) B696797
theorem B464547 : Blo 463784 464547 := bstep (se 1 (by rfl) ⟨348410, by rfl⟩ : syracuseStep 464547 = 696821) B696821
theorem B1775267 : Blo 463784 1775267 := bstep (se 1 (by rfl) ⟨1331450, by rfl⟩ : syracuseStep 1775267 = 2662901) B2662901
theorem B661169 : Blo 463784 661169 := bstep (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) B495877
theorem B464563 : Blo 463784 464563 := bstep (se 1 (by rfl) ⟨348422, by rfl⟩ : syracuseStep 464563 = 696845) B696845
theorem B464579 : Blo 463784 464579 := bstep (se 1 (by rfl) ⟨348434, by rfl⟩ : syracuseStep 464579 = 696869) B696869
theorem B464595 : Blo 463784 464595 := bstep (se 1 (by rfl) ⟨348446, by rfl⟩ : syracuseStep 464595 = 696893) B696893
theorem B464611 : Blo 463784 464611 := bstep (se 1 (by rfl) ⟨348458, by rfl⟩ : syracuseStep 464611 = 696917) B696917
theorem B464627 : Blo 463784 464627 := bstep (se 1 (by rfl) ⟨348470, by rfl⟩ : syracuseStep 464627 = 696941) B696941
theorem B464643 : Blo 463784 464643 := bstep (se 1 (by rfl) ⟨348482, by rfl⟩ : syracuseStep 464643 = 696965) B696965
theorem B464659 : Blo 463784 464659 := bstep (se 1 (by rfl) ⟨348494, by rfl⟩ : syracuseStep 464659 = 696989) B696989
theorem B464675 : Blo 463784 464675 := bstep (se 1 (by rfl) ⟨348506, by rfl⟩ : syracuseStep 464675 = 697013) B697013
theorem B464691 : Blo 463784 464691 := bstep (se 1 (by rfl) ⟨348518, by rfl⟩ : syracuseStep 464691 = 697037) B697037
theorem B464707 : Blo 463784 464707 := bstep (se 1 (by rfl) ⟨348530, by rfl⟩ : syracuseStep 464707 = 697061) B697061
theorem B2561861 : Blo 463784 2561861 := bstep (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) B480349
theorem B464723 : Blo 463784 464723 := bstep (se 1 (by rfl) ⟨348542, by rfl⟩ : syracuseStep 464723 = 697085) B697085
theorem B464739 : Blo 463784 464739 := bstep (se 1 (by rfl) ⟨348554, by rfl⟩ : syracuseStep 464739 = 697109) B697109
theorem B464755 : Blo 463784 464755 := bstep (se 1 (by rfl) ⟨348566, by rfl⟩ : syracuseStep 464755 = 697133) B697133
theorem B464771 : Blo 463784 464771 := bstep (se 1 (by rfl) ⟨348578, by rfl⟩ : syracuseStep 464771 = 697157) B697157
theorem B497539 : Blo 463784 497539 := bstep (se 1 (by rfl) ⟨373154, by rfl⟩ : syracuseStep 497539 = 746309) B746309
theorem B464787 : Blo 463784 464787 := bstep (se 1 (by rfl) ⟨348590, by rfl⟩ : syracuseStep 464787 = 697181) B697181
theorem B464803 : Blo 463784 464803 := bstep (se 1 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 464803 = 697205) B697205
theorem B628643 : Blo 463784 628643 := bstep (se 1 (by rfl) ⟨471482, by rfl⟩ : syracuseStep 628643 = 942965) B942965
theorem B2365361 : Blo 463784 2365361 := bstep (se 2 (by rfl) ⟨887010, by rfl⟩ : syracuseStep 2365361 = 1774021) B1774021
theorem B464819 : Blo 463784 464819 := bstep (se 1 (by rfl) ⟨348614, by rfl⟩ : syracuseStep 464819 = 697229) B697229
theorem B464835 : Blo 463784 464835 := bstep (se 1 (by rfl) ⟨348626, by rfl⟩ : syracuseStep 464835 = 697253) B697253
theorem B464851 : Blo 463784 464851 := bstep (se 1 (by rfl) ⟨348638, by rfl⟩ : syracuseStep 464851 = 697277) B697277
theorem B464867 : Blo 463784 464867 := bstep (se 1 (by rfl) ⟨348650, by rfl⟩ : syracuseStep 464867 = 697301) B697301
theorem B464883 : Blo 463784 464883 := bstep (se 1 (by rfl) ⟨348662, by rfl⟩ : syracuseStep 464883 = 697325) B697325
theorem B464899 : Blo 463784 464899 := bstep (se 1 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 464899 = 697349) B697349
theorem B464915 : Blo 463784 464915 := bstep (se 1 (by rfl) ⟨348686, by rfl⟩ : syracuseStep 464915 = 697373) B697373
theorem B464931 : Blo 463784 464931 := bstep (se 1 (by rfl) ⟨348698, by rfl⟩ : syracuseStep 464931 = 697397) B697397
theorem B1153073 : Blo 463784 1153073 := bstep (se 2 (by rfl) ⟨432402, by rfl⟩ : syracuseStep 1153073 = 864805) B864805
theorem B464947 : Blo 463784 464947 := bstep (se 1 (by rfl) ⟨348710, by rfl⟩ : syracuseStep 464947 = 697421) B697421
theorem B464963 : Blo 463784 464963 := bstep (se 1 (by rfl) ⟨348722, by rfl⟩ : syracuseStep 464963 = 697445) B697445
theorem B464979 : Blo 463784 464979 := bstep (se 1 (by rfl) ⟨348734, by rfl⟩ : syracuseStep 464979 = 697469) B697469
theorem B464995 : Blo 463784 464995 := bstep (se 1 (by rfl) ⟨348746, by rfl⟩ : syracuseStep 464995 = 697493) B697493
theorem B465011 : Blo 463784 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B465027 : Blo 463784 465027 := bstep (se 1 (by rfl) ⟨348770, by rfl⟩ : syracuseStep 465027 = 697541) B697541
theorem B2660485 : Blo 463784 2660485 := bstep (se 4 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 2660485 = 498841) B498841
theorem B465043 : Blo 463784 465043 := bstep (se 1 (by rfl) ⟨348782, by rfl⟩ : syracuseStep 465043 = 697565) B697565
theorem B465059 : Blo 463784 465059 := bstep (se 1 (by rfl) ⟨348794, by rfl⟩ : syracuseStep 465059 = 697589) B697589
theorem B465075 : Blo 463784 465075 := bstep (se 1 (by rfl) ⟨348806, by rfl⟩ : syracuseStep 465075 = 697613) B697613
theorem B661699 : Blo 463784 661699 := bstep (se 1 (by rfl) ⟨496274, by rfl⟩ : syracuseStep 661699 = 992549) B992549
theorem B465091 : Blo 463784 465091 := bstep (se 1 (by rfl) ⟨348818, by rfl⟩ : syracuseStep 465091 = 697637) B697637
theorem B465107 : Blo 463784 465107 := bstep (se 1 (by rfl) ⟨348830, by rfl⟩ : syracuseStep 465107 = 697661) B697661
theorem B465123 : Blo 463784 465123 := bstep (se 1 (by rfl) ⟨348842, by rfl⟩ : syracuseStep 465123 = 697685) B697685
theorem B465139 : Blo 463784 465139 := bstep (se 1 (by rfl) ⟨348854, by rfl⟩ : syracuseStep 465139 = 697709) B697709
theorem B465155 : Blo 463784 465155 := bstep (se 1 (by rfl) ⟨348866, by rfl⟩ : syracuseStep 465155 = 697733) B697733
theorem B465171 : Blo 463784 465171 := bstep (se 1 (by rfl) ⟨348878, by rfl⟩ : syracuseStep 465171 = 697757) B697757
theorem B465187 : Blo 463784 465187 := bstep (se 1 (by rfl) ⟨348890, by rfl⟩ : syracuseStep 465187 = 697781) B697781
theorem B1906993 : Blo 463784 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B465203 : Blo 463784 465203 := bstep (se 1 (by rfl) ⟨348902, by rfl⟩ : syracuseStep 465203 = 697805) B697805
theorem B465219 : Blo 463784 465219 := bstep (se 1 (by rfl) ⟨348914, by rfl⟩ : syracuseStep 465219 = 697829) B697829
theorem B465235 : Blo 463784 465235 := bstep (se 1 (by rfl) ⟨348926, by rfl⟩ : syracuseStep 465235 = 697853) B697853
theorem B465251 : Blo 463784 465251 := bstep (se 1 (by rfl) ⟨348938, by rfl⟩ : syracuseStep 465251 = 697877) B697877
theorem B1120625 : Blo 463784 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B465267 : Blo 463784 465267 := bstep (se 1 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 465267 = 697901) B697901
theorem B465283 : Blo 463784 465283 := bstep (se 1 (by rfl) ⟨348962, by rfl⟩ : syracuseStep 465283 = 697925) B697925
theorem B465299 : Blo 463784 465299 := bstep (se 1 (by rfl) ⟨348974, by rfl⟩ : syracuseStep 465299 = 697949) B697949
theorem B465315 : Blo 463784 465315 := bstep (se 1 (by rfl) ⟨348986, by rfl⟩ : syracuseStep 465315 = 697973) B697973
theorem B465331 : Blo 463784 465331 := bstep (se 1 (by rfl) ⟨348998, by rfl⟩ : syracuseStep 465331 = 697997) B697997
theorem B465347 : Blo 463784 465347 := bstep (se 1 (by rfl) ⟨349010, by rfl⟩ : syracuseStep 465347 = 698021) B698021
theorem B465363 : Blo 463784 465363 := bstep (se 1 (by rfl) ⟨349022, by rfl⟩ : syracuseStep 465363 = 698045) B698045
theorem B465379 : Blo 463784 465379 := bstep (se 1 (by rfl) ⟨349034, by rfl⟩ : syracuseStep 465379 = 698069) B698069
theorem B4790755 : Blo 463784 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B465395 : Blo 463784 465395 := bstep (se 1 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 465395 = 698093) B698093
theorem B465411 : Blo 463784 465411 := bstep (se 1 (by rfl) ⟨349058, by rfl⟩ : syracuseStep 465411 = 698117) B698117
theorem B662035 : Blo 463784 662035 := bstep (se 1 (by rfl) ⟨496526, by rfl⟩ : syracuseStep 662035 = 993053) B993053
theorem B465427 : Blo 463784 465427 := bstep (se 1 (by rfl) ⟨349070, by rfl⟩ : syracuseStep 465427 = 698141) B698141
theorem B465443 : Blo 463784 465443 := bstep (se 1 (by rfl) ⟨349082, by rfl⟩ : syracuseStep 465443 = 698165) B698165
theorem B1120817 : Blo 463784 1120817 := bstep (se 2 (by rfl) ⟨420306, by rfl⟩ : syracuseStep 1120817 = 840613) B840613
theorem B596531 : Blo 463784 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B465459 : Blo 463784 465459 := bstep (se 1 (by rfl) ⟨349094, by rfl⟩ : syracuseStep 465459 = 698189) B698189
theorem B465475 : Blo 463784 465475 := bstep (se 1 (by rfl) ⟨349106, by rfl⟩ : syracuseStep 465475 = 698213) B698213
theorem B4528709 : Blo 463784 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B465491 : Blo 463784 465491 := bstep (se 1 (by rfl) ⟨349118, by rfl⟩ : syracuseStep 465491 = 698237) B698237
theorem B465507 : Blo 463784 465507 := bstep (se 1 (by rfl) ⟨349130, by rfl⟩ : syracuseStep 465507 = 698261) B698261
theorem B465523 : Blo 463784 465523 := bstep (se 1 (by rfl) ⟨349142, by rfl⟩ : syracuseStep 465523 = 698285) B698285
theorem B465539 : Blo 463784 465539 := bstep (se 1 (by rfl) ⟨349154, by rfl⟩ : syracuseStep 465539 = 698309) B698309
theorem B465555 : Blo 463784 465555 := bstep (se 1 (by rfl) ⟨349166, by rfl⟩ : syracuseStep 465555 = 698333) B698333
theorem B465571 : Blo 463784 465571 := bstep (se 1 (by rfl) ⟨349178, by rfl⟩ : syracuseStep 465571 = 698357) B698357
theorem B465587 : Blo 463784 465587 := bstep (se 1 (by rfl) ⟨349190, by rfl⟩ : syracuseStep 465587 = 698381) B698381
theorem B465603 : Blo 463784 465603 := bstep (se 1 (by rfl) ⟨349202, by rfl⟩ : syracuseStep 465603 = 698405) B698405
theorem B465619 : Blo 463784 465619 := bstep (se 1 (by rfl) ⟨349214, by rfl⟩ : syracuseStep 465619 = 698429) B698429
theorem B465635 : Blo 463784 465635 := bstep (se 1 (by rfl) ⟨349226, by rfl⟩ : syracuseStep 465635 = 698453) B698453
theorem B465651 : Blo 463784 465651 := bstep (se 1 (by rfl) ⟨349238, by rfl⟩ : syracuseStep 465651 = 698477) B698477
theorem B465667 : Blo 463784 465667 := bstep (se 1 (by rfl) ⟨349250, by rfl⟩ : syracuseStep 465667 = 698501) B698501
theorem B465683 : Blo 463784 465683 := bstep (se 1 (by rfl) ⟨349262, by rfl⟩ : syracuseStep 465683 = 698525) B698525
theorem B465699 : Blo 463784 465699 := bstep (se 1 (by rfl) ⟨349274, by rfl⟩ : syracuseStep 465699 = 698549) B698549
theorem B465715 : Blo 463784 465715 := bstep (se 1 (by rfl) ⟨349286, by rfl⟩ : syracuseStep 465715 = 698573) B698573
theorem B465731 : Blo 463784 465731 := bstep (se 1 (by rfl) ⟨349298, by rfl⟩ : syracuseStep 465731 = 698597) B698597
theorem B465747 : Blo 463784 465747 := bstep (se 1 (by rfl) ⟨349310, by rfl⟩ : syracuseStep 465747 = 698621) B698621
theorem B2235235 : Blo 463784 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B465763 : Blo 463784 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B465779 : Blo 463784 465779 := bstep (se 1 (by rfl) ⟨349334, by rfl⟩ : syracuseStep 465779 = 698669) B698669
theorem B465795 : Blo 463784 465795 := bstep (se 1 (by rfl) ⟨349346, by rfl⟩ : syracuseStep 465795 = 698693) B698693
theorem B465811 : Blo 463784 465811 := bstep (se 1 (by rfl) ⟨349358, by rfl⟩ : syracuseStep 465811 = 698717) B698717
theorem B465827 : Blo 463784 465827 := bstep (se 1 (by rfl) ⟨349370, by rfl⟩ : syracuseStep 465827 = 698741) B698741
theorem B465843 : Blo 463784 465843 := bstep (se 1 (by rfl) ⟨349382, by rfl⟩ : syracuseStep 465843 = 698765) B698765
theorem B465859 : Blo 463784 465859 := bstep (se 1 (by rfl) ⟨349394, by rfl⟩ : syracuseStep 465859 = 698789) B698789
theorem B465875 : Blo 463784 465875 := bstep (se 1 (by rfl) ⟨349406, by rfl⟩ : syracuseStep 465875 = 698813) B698813
theorem B465891 : Blo 463784 465891 := bstep (se 1 (by rfl) ⟨349418, by rfl⟩ : syracuseStep 465891 = 698837) B698837
theorem B465907 : Blo 463784 465907 := bstep (se 1 (by rfl) ⟨349430, by rfl⟩ : syracuseStep 465907 = 698861) B698861
theorem B465923 : Blo 463784 465923 := bstep (se 1 (by rfl) ⟨349442, by rfl⟩ : syracuseStep 465923 = 698885) B698885
theorem B465939 : Blo 463784 465939 := bstep (se 1 (by rfl) ⟨349454, by rfl⟩ : syracuseStep 465939 = 698909) B698909
theorem B465955 : Blo 463784 465955 := bstep (se 1 (by rfl) ⟨349466, by rfl⟩ : syracuseStep 465955 = 698933) B698933
theorem B465971 : Blo 463784 465971 := bstep (se 1 (by rfl) ⟨349478, by rfl⟩ : syracuseStep 465971 = 698957) B698957
theorem B5676085 : Blo 463784 5676085 := bstep (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) B532133
theorem B662593 : Blo 463784 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B465987 : Blo 463784 465987 := bstep (se 1 (by rfl) ⟨349490, by rfl⟩ : syracuseStep 465987 = 698981) B698981
theorem B2825293 : Blo 463784 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B466003 : Blo 463784 466003 := bstep (se 1 (by rfl) ⟨349502, by rfl⟩ : syracuseStep 466003 = 699005) B699005
theorem B662627 : Blo 463784 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B466019 : Blo 463784 466019 := bstep (se 1 (by rfl) ⟨349514, by rfl⟩ : syracuseStep 466019 = 699029) B699029
theorem B466035 : Blo 463784 466035 := bstep (se 1 (by rfl) ⟨349526, by rfl⟩ : syracuseStep 466035 = 699053) B699053
theorem B498803 : Blo 463784 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B466051 : Blo 463784 466051 := bstep (se 1 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 466051 = 699077) B699077
theorem B466067 : Blo 463784 466067 := bstep (se 1 (by rfl) ⟨349550, by rfl⟩ : syracuseStep 466067 = 699101) B699101
theorem B466083 : Blo 463784 466083 := bstep (se 1 (by rfl) ⟨349562, by rfl⟩ : syracuseStep 466083 = 699125) B699125
theorem B466099 : Blo 463784 466099 := bstep (se 1 (by rfl) ⟨349574, by rfl⟩ : syracuseStep 466099 = 699149) B699149
theorem B466115 : Blo 463784 466115 := bstep (se 1 (by rfl) ⟨349586, by rfl⟩ : syracuseStep 466115 = 699173) B699173
theorem B466131 : Blo 463784 466131 := bstep (se 1 (by rfl) ⟨349598, by rfl⟩ : syracuseStep 466131 = 699197) B699197
theorem B466147 : Blo 463784 466147 := bstep (se 1 (by rfl) ⟨349610, by rfl⟩ : syracuseStep 466147 = 699221) B699221
theorem B466163 : Blo 463784 466163 := bstep (se 1 (by rfl) ⟨349622, by rfl⟩ : syracuseStep 466163 = 699245) B699245
theorem B466179 : Blo 463784 466179 := bstep (se 1 (by rfl) ⟨349634, by rfl⟩ : syracuseStep 466179 = 699269) B699269
theorem B1121539 : Blo 463784 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B466195 : Blo 463784 466195 := bstep (se 1 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 466195 = 699293) B699293
theorem B466211 : Blo 463784 466211 := bstep (se 1 (by rfl) ⟨349658, by rfl⟩ : syracuseStep 466211 = 699317) B699317
theorem B466227 : Blo 463784 466227 := bstep (se 1 (by rfl) ⟨349670, by rfl⟩ : syracuseStep 466227 = 699341) B699341
theorem B466243 : Blo 463784 466243 := bstep (se 1 (by rfl) ⟨349682, by rfl⟩ : syracuseStep 466243 = 699365) B699365
theorem B466259 : Blo 463784 466259 := bstep (se 1 (by rfl) ⟨349694, by rfl⟩ : syracuseStep 466259 = 699389) B699389
theorem B466275 : Blo 463784 466275 := bstep (se 1 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 466275 = 699413) B699413
theorem B1023331 : Blo 463784 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B2366819 : Blo 463784 2366819 := bstep (se 1 (by rfl) ⟨1775114, by rfl⟩ : syracuseStep 2366819 = 3550229) B3550229
theorem B466291 : Blo 463784 466291 := bstep (se 1 (by rfl) ⟨349718, by rfl⟩ : syracuseStep 466291 = 699437) B699437
theorem B695681 : Blo 463784 695681 := bstep (se 2 (by rfl) ⟨260880, by rfl⟩ : syracuseStep 695681 = 521761) B521761
theorem B466307 : Blo 463784 466307 := bstep (se 1 (by rfl) ⟨349730, by rfl⟩ : syracuseStep 466307 = 699461) B699461
theorem B695699 : Blo 463784 695699 := bstep (se 1 (by rfl) ⟨521774, by rfl⟩ : syracuseStep 695699 = 1043549) B1043549
theorem B466323 : Blo 463784 466323 := bstep (se 1 (by rfl) ⟨349742, by rfl⟩ : syracuseStep 466323 = 699485) B699485
theorem B466339 : Blo 463784 466339 := bstep (se 1 (by rfl) ⟨349754, by rfl⟩ : syracuseStep 466339 = 699509) B699509
theorem B695729 : Blo 463784 695729 := bstep (se 2 (by rfl) ⟨260898, by rfl⟩ : syracuseStep 695729 = 521797) B521797
theorem B466355 : Blo 463784 466355 := bstep (se 1 (by rfl) ⟨349766, by rfl⟩ : syracuseStep 466355 = 699533) B699533
theorem B695747 : Blo 463784 695747 := bstep (se 1 (by rfl) ⟨521810, by rfl⟩ : syracuseStep 695747 = 1043621) B1043621
theorem B466371 : Blo 463784 466371 := bstep (se 1 (by rfl) ⟨349778, by rfl⟩ : syracuseStep 466371 = 699557) B699557
theorem B466387 : Blo 463784 466387 := bstep (se 1 (by rfl) ⟨349790, by rfl⟩ : syracuseStep 466387 = 699581) B699581
theorem B695777 : Blo 463784 695777 := bstep (se 2 (by rfl) ⟨260916, by rfl⟩ : syracuseStep 695777 = 521833) B521833
theorem B466403 : Blo 463784 466403 := bstep (se 1 (by rfl) ⟨349802, by rfl⟩ : syracuseStep 466403 = 699605) B699605
theorem B4267505 : Blo 463784 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B695795 : Blo 463784 695795 := bstep (se 1 (by rfl) ⟨521846, by rfl⟩ : syracuseStep 695795 = 1043693) B1043693
theorem B466419 : Blo 463784 466419 := bstep (se 1 (by rfl) ⟨349814, by rfl⟩ : syracuseStep 466419 = 699629) B699629
theorem B466435 : Blo 463784 466435 := bstep (se 1 (by rfl) ⟨349826, by rfl⟩ : syracuseStep 466435 = 699653) B699653
theorem B695825 : Blo 463784 695825 := bstep (se 2 (by rfl) ⟨260934, by rfl⟩ : syracuseStep 695825 = 521869) B521869
theorem B466451 : Blo 463784 466451 := bstep (se 1 (by rfl) ⟨349838, by rfl⟩ : syracuseStep 466451 = 699677) B699677
theorem B695843 : Blo 463784 695843 := bstep (se 1 (by rfl) ⟨521882, by rfl⟩ : syracuseStep 695843 = 1043765) B1043765
theorem B466467 : Blo 463784 466467 := bstep (se 1 (by rfl) ⟨349850, by rfl⟩ : syracuseStep 466467 = 699701) B699701
theorem B466483 : Blo 463784 466483 := bstep (se 1 (by rfl) ⟨349862, by rfl⟩ : syracuseStep 466483 = 699725) B699725
theorem B695873 : Blo 463784 695873 := bstep (se 2 (by rfl) ⟨260952, by rfl⟩ : syracuseStep 695873 = 521905) B521905
theorem B466499 : Blo 463784 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B695891 : Blo 463784 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B466515 : Blo 463784 466515 := bstep (se 1 (by rfl) ⟨349886, by rfl⟩ : syracuseStep 466515 = 699773) B699773
theorem B466531 : Blo 463784 466531 := bstep (se 1 (by rfl) ⟨349898, by rfl⟩ : syracuseStep 466531 = 699797) B699797
theorem B695921 : Blo 463784 695921 := bstep (se 2 (by rfl) ⟨260970, by rfl⟩ : syracuseStep 695921 = 521941) B521941
theorem B466547 : Blo 463784 466547 := bstep (se 1 (by rfl) ⟨349910, by rfl⟩ : syracuseStep 466547 = 699821) B699821
theorem B1384067 : Blo 463784 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B695939 : Blo 463784 695939 := bstep (se 1 (by rfl) ⟨521954, by rfl⟩ : syracuseStep 695939 = 1043909) B1043909
theorem B466563 : Blo 463784 466563 := bstep (se 1 (by rfl) ⟨349922, by rfl⟩ : syracuseStep 466563 = 699845) B699845
theorem B663185 : Blo 463784 663185 := bstep (se 2 (by rfl) ⟨248694, by rfl⟩ : syracuseStep 663185 = 497389) B497389
theorem B466579 : Blo 463784 466579 := bstep (se 1 (by rfl) ⟨349934, by rfl⟩ : syracuseStep 466579 = 699869) B699869
theorem B695969 : Blo 463784 695969 := bstep (se 2 (by rfl) ⟨260988, by rfl⟩ : syracuseStep 695969 = 521977) B521977
theorem B630433 : Blo 463784 630433 := bstep (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) B472825
theorem B466595 : Blo 463784 466595 := bstep (se 1 (by rfl) ⟨349946, by rfl⟩ : syracuseStep 466595 = 699893) B699893
theorem B695987 : Blo 463784 695987 := bstep (se 1 (by rfl) ⟨521990, by rfl⟩ : syracuseStep 695987 = 1043981) B1043981
theorem B466611 : Blo 463784 466611 := bstep (se 1 (by rfl) ⟨349958, by rfl⟩ : syracuseStep 466611 = 699917) B699917
theorem B466627 : Blo 463784 466627 := bstep (se 1 (by rfl) ⟨349970, by rfl⟩ : syracuseStep 466627 = 699941) B699941
theorem B696017 : Blo 463784 696017 := bstep (se 2 (by rfl) ⟨261006, by rfl⟩ : syracuseStep 696017 = 522013) B522013
theorem B466643 : Blo 463784 466643 := bstep (se 1 (by rfl) ⟨349982, by rfl⟩ : syracuseStep 466643 = 699965) B699965
theorem B663265 : Blo 463784 663265 := bstep (se 2 (by rfl) ⟨248724, by rfl⟩ : syracuseStep 663265 = 497449) B497449
theorem B696035 : Blo 463784 696035 := bstep (se 1 (by rfl) ⟨522026, by rfl⟩ : syracuseStep 696035 = 1044053) B1044053
theorem B466659 : Blo 463784 466659 := bstep (se 1 (by rfl) ⟨349994, by rfl⟩ : syracuseStep 466659 = 699989) B699989
theorem B466675 : Blo 463784 466675 := bstep (se 1 (by rfl) ⟨350006, by rfl⟩ : syracuseStep 466675 = 700013) B700013
theorem B696065 : Blo 463784 696065 := bstep (se 2 (by rfl) ⟨261024, by rfl⟩ : syracuseStep 696065 = 522049) B522049
theorem B466691 : Blo 463784 466691 := bstep (se 1 (by rfl) ⟨350018, by rfl⟩ : syracuseStep 466691 = 700037) B700037
theorem B696083 : Blo 463784 696083 := bstep (se 1 (by rfl) ⟨522062, by rfl⟩ : syracuseStep 696083 = 1044125) B1044125
theorem B466707 : Blo 463784 466707 := bstep (se 1 (by rfl) ⟨350030, by rfl⟩ : syracuseStep 466707 = 700061) B700061
theorem B466723 : Blo 463784 466723 := bstep (se 1 (by rfl) ⟨350042, by rfl⟩ : syracuseStep 466723 = 700085) B700085
theorem B696113 : Blo 463784 696113 := bstep (se 2 (by rfl) ⟨261042, by rfl⟩ : syracuseStep 696113 = 522085) B522085
theorem B466739 : Blo 463784 466739 := bstep (se 1 (by rfl) ⟨350054, by rfl⟩ : syracuseStep 466739 = 700109) B700109
theorem B696131 : Blo 463784 696131 := bstep (se 1 (by rfl) ⟨522098, by rfl⟩ : syracuseStep 696131 = 1044197) B1044197
theorem B466755 : Blo 463784 466755 := bstep (se 1 (by rfl) ⟨350066, by rfl⟩ : syracuseStep 466755 = 700133) B700133
theorem B466771 : Blo 463784 466771 := bstep (se 1 (by rfl) ⟨350078, by rfl⟩ : syracuseStep 466771 = 700157) B700157
theorem B696161 : Blo 463784 696161 := bstep (se 2 (by rfl) ⟨261060, by rfl⟩ : syracuseStep 696161 = 522121) B522121
theorem B4595555 : Blo 463784 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B466787 : Blo 463784 466787 := bstep (se 1 (by rfl) ⟨350090, by rfl⟩ : syracuseStep 466787 = 700181) B700181
theorem B696179 : Blo 463784 696179 := bstep (se 1 (by rfl) ⟨522134, by rfl⟩ : syracuseStep 696179 = 1044269) B1044269
theorem B466803 : Blo 463784 466803 := bstep (se 1 (by rfl) ⟨350102, by rfl⟩ : syracuseStep 466803 = 700205) B700205
theorem B466819 : Blo 463784 466819 := bstep (se 1 (by rfl) ⟨350114, by rfl⟩ : syracuseStep 466819 = 700229) B700229
theorem B991121 : Blo 463784 991121 := bstep (se 2 (by rfl) ⟨371670, by rfl⟩ : syracuseStep 991121 = 743341) B743341
theorem B696209 : Blo 463784 696209 := bstep (se 2 (by rfl) ⟨261078, by rfl⟩ : syracuseStep 696209 = 522157) B522157
theorem B466835 : Blo 463784 466835 := bstep (se 1 (by rfl) ⟨350126, by rfl⟩ : syracuseStep 466835 = 700253) B700253
theorem B696227 : Blo 463784 696227 := bstep (se 1 (by rfl) ⟨522170, by rfl⟩ : syracuseStep 696227 = 1044341) B1044341
theorem B466851 : Blo 463784 466851 := bstep (se 1 (by rfl) ⟨350138, by rfl⟩ : syracuseStep 466851 = 700277) B700277
theorem B892849 : Blo 463784 892849 := bstep (se 2 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 892849 = 669637) B669637
theorem B466867 : Blo 463784 466867 := bstep (se 1 (by rfl) ⟨350150, by rfl⟩ : syracuseStep 466867 = 700301) B700301
theorem B696257 : Blo 463784 696257 := bstep (se 2 (by rfl) ⟨261096, by rfl⟩ : syracuseStep 696257 = 522193) B522193
theorem B466883 : Blo 463784 466883 := bstep (se 1 (by rfl) ⟨350162, by rfl⟩ : syracuseStep 466883 = 700325) B700325
theorem B1679309 : Blo 463784 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B696275 : Blo 463784 696275 := bstep (se 1 (by rfl) ⟨522206, by rfl⟩ : syracuseStep 696275 = 1044413) B1044413
theorem B466899 : Blo 463784 466899 := bstep (se 1 (by rfl) ⟨350174, by rfl⟩ : syracuseStep 466899 = 700349) B700349
theorem B466915 : Blo 463784 466915 := bstep (se 1 (by rfl) ⟨350186, by rfl⟩ : syracuseStep 466915 = 700373) B700373
theorem B696305 : Blo 463784 696305 := bstep (se 2 (by rfl) ⟨261114, by rfl⟩ : syracuseStep 696305 = 522229) B522229
theorem B466931 : Blo 463784 466931 := bstep (se 1 (by rfl) ⟨350198, by rfl⟩ : syracuseStep 466931 = 700397) B700397
theorem B696323 : Blo 463784 696323 := bstep (se 1 (by rfl) ⟨522242, by rfl⟩ : syracuseStep 696323 = 1044485) B1044485
theorem B466947 : Blo 463784 466947 := bstep (se 1 (by rfl) ⟨350210, by rfl⟩ : syracuseStep 466947 = 700421) B700421
theorem B466963 : Blo 463784 466963 := bstep (se 1 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 466963 = 700445) B700445
theorem B696353 : Blo 463784 696353 := bstep (se 2 (by rfl) ⟨261132, by rfl⟩ : syracuseStep 696353 = 522265) B522265
theorem B598051 : Blo 463784 598051 := bstep (se 1 (by rfl) ⟨448538, by rfl⟩ : syracuseStep 598051 = 897077) B897077
theorem B466979 : Blo 463784 466979 := bstep (se 1 (by rfl) ⟨350234, by rfl⟩ : syracuseStep 466979 = 700469) B700469
theorem B696371 : Blo 463784 696371 := bstep (se 1 (by rfl) ⟨522278, by rfl⟩ : syracuseStep 696371 = 1044557) B1044557
theorem B466995 : Blo 463784 466995 := bstep (se 1 (by rfl) ⟨350246, by rfl⟩ : syracuseStep 466995 = 700493) B700493
theorem B467011 : Blo 463784 467011 := bstep (se 1 (by rfl) ⟨350258, by rfl⟩ : syracuseStep 467011 = 700517) B700517
theorem B2662469 : Blo 463784 2662469 := bstep (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) B499213
theorem B696401 : Blo 463784 696401 := bstep (se 2 (by rfl) ⟨261150, by rfl⟩ : syracuseStep 696401 = 522301) B522301
theorem B467027 : Blo 463784 467027 := bstep (se 1 (by rfl) ⟨350270, by rfl⟩ : syracuseStep 467027 = 700541) B700541
theorem B696419 : Blo 463784 696419 := bstep (se 1 (by rfl) ⟨522314, by rfl⟩ : syracuseStep 696419 = 1044629) B1044629
theorem B467043 : Blo 463784 467043 := bstep (se 1 (by rfl) ⟨350282, by rfl⟩ : syracuseStep 467043 = 700565) B700565
theorem B467059 : Blo 463784 467059 := bstep (se 1 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 467059 = 700589) B700589
theorem B696449 : Blo 463784 696449 := bstep (se 2 (by rfl) ⟨261168, by rfl⟩ : syracuseStep 696449 = 522337) B522337
theorem B467075 : Blo 463784 467075 := bstep (se 1 (by rfl) ⟨350306, by rfl⟩ : syracuseStep 467075 = 700613) B700613
theorem B2367629 : Blo 463784 2367629 := bstep (se 3 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 2367629 = 887861) B887861
theorem B696467 : Blo 463784 696467 := bstep (se 1 (by rfl) ⟨522350, by rfl⟩ : syracuseStep 696467 = 1044701) B1044701
theorem B467091 : Blo 463784 467091 := bstep (se 1 (by rfl) ⟨350318, by rfl⟩ : syracuseStep 467091 = 700637) B700637
theorem B467107 : Blo 463784 467107 := bstep (se 1 (by rfl) ⟨350330, by rfl⟩ : syracuseStep 467107 = 700661) B700661
theorem B696497 : Blo 463784 696497 := bstep (se 2 (by rfl) ⟨261186, by rfl⟩ : syracuseStep 696497 = 522373) B522373
theorem B467123 : Blo 463784 467123 := bstep (se 1 (by rfl) ⟨350342, by rfl⟩ : syracuseStep 467123 = 700685) B700685
theorem B696515 : Blo 463784 696515 := bstep (se 1 (by rfl) ⟨522386, by rfl⟩ : syracuseStep 696515 = 1044773) B1044773
theorem B467139 : Blo 463784 467139 := bstep (se 1 (by rfl) ⟨350354, by rfl⟩ : syracuseStep 467139 = 700709) B700709
theorem B467155 : Blo 463784 467155 := bstep (se 1 (by rfl) ⟨350366, by rfl⟩ : syracuseStep 467155 = 700733) B700733
theorem B696545 : Blo 463784 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B467171 : Blo 463784 467171 := bstep (se 1 (by rfl) ⟨350378, by rfl⟩ : syracuseStep 467171 = 700757) B700757
theorem B696563 : Blo 463784 696563 := bstep (se 1 (by rfl) ⟨522422, by rfl⟩ : syracuseStep 696563 = 1044845) B1044845
theorem B467187 : Blo 463784 467187 := bstep (se 1 (by rfl) ⟨350390, by rfl⟩ : syracuseStep 467187 = 700781) B700781
theorem B467203 : Blo 463784 467203 := bstep (se 1 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 467203 = 700805) B700805
theorem B696593 : Blo 463784 696593 := bstep (se 2 (by rfl) ⟨261222, by rfl⟩ : syracuseStep 696593 = 522445) B522445
theorem B467219 : Blo 463784 467219 := bstep (se 1 (by rfl) ⟨350414, by rfl⟩ : syracuseStep 467219 = 700829) B700829
theorem B696611 : Blo 463784 696611 := bstep (se 1 (by rfl) ⟨522458, by rfl⟩ : syracuseStep 696611 = 1044917) B1044917
theorem B467235 : Blo 463784 467235 := bstep (se 1 (by rfl) ⟨350426, by rfl⟩ : syracuseStep 467235 = 700853) B700853
theorem B467251 : Blo 463784 467251 := bstep (se 1 (by rfl) ⟨350438, by rfl⟩ : syracuseStep 467251 = 700877) B700877
theorem B696641 : Blo 463784 696641 := bstep (se 2 (by rfl) ⟨261240, by rfl⟩ : syracuseStep 696641 = 522481) B522481
theorem B467267 : Blo 463784 467267 := bstep (se 1 (by rfl) ⟨350450, by rfl⟩ : syracuseStep 467267 = 700901) B700901
theorem B696659 : Blo 463784 696659 := bstep (se 1 (by rfl) ⟨522494, by rfl⟩ : syracuseStep 696659 = 1044989) B1044989
theorem B467283 : Blo 463784 467283 := bstep (se 1 (by rfl) ⟨350462, by rfl⟩ : syracuseStep 467283 = 700925) B700925
theorem B467299 : Blo 463784 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B696689 : Blo 463784 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B467315 : Blo 463784 467315 := bstep (se 1 (by rfl) ⟨350486, by rfl⟩ : syracuseStep 467315 = 700973) B700973
theorem B696707 : Blo 463784 696707 := bstep (se 1 (by rfl) ⟨522530, by rfl⟩ : syracuseStep 696707 = 1045061) B1045061
theorem B467331 : Blo 463784 467331 := bstep (se 1 (by rfl) ⟨350498, by rfl⟩ : syracuseStep 467331 = 700997) B700997
theorem B467347 : Blo 463784 467347 := bstep (se 1 (by rfl) ⟨350510, by rfl⟩ : syracuseStep 467347 = 701021) B701021
theorem B696737 : Blo 463784 696737 := bstep (se 2 (by rfl) ⟨261276, by rfl⟩ : syracuseStep 696737 = 522553) B522553
theorem B467363 : Blo 463784 467363 := bstep (se 1 (by rfl) ⟨350522, by rfl⟩ : syracuseStep 467363 = 701045) B701045
theorem B696755 : Blo 463784 696755 := bstep (se 1 (by rfl) ⟨522566, by rfl⟩ : syracuseStep 696755 = 1045133) B1045133
theorem B467379 : Blo 463784 467379 := bstep (se 1 (by rfl) ⟨350534, by rfl⟩ : syracuseStep 467379 = 701069) B701069
theorem B467395 : Blo 463784 467395 := bstep (se 1 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 467395 = 701093) B701093
theorem B696785 : Blo 463784 696785 := bstep (se 2 (by rfl) ⟨261294, by rfl⟩ : syracuseStep 696785 = 522589) B522589
theorem B467411 : Blo 463784 467411 := bstep (se 1 (by rfl) ⟨350558, by rfl⟩ : syracuseStep 467411 = 701117) B701117
theorem B696803 : Blo 463784 696803 := bstep (se 1 (by rfl) ⟨522602, by rfl⟩ : syracuseStep 696803 = 1045205) B1045205
theorem B467427 : Blo 463784 467427 := bstep (se 1 (by rfl) ⟨350570, by rfl⟩ : syracuseStep 467427 = 701141) B701141
theorem B664051 : Blo 463784 664051 := bstep (se 1 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 664051 = 996077) B996077
theorem B467443 : Blo 463784 467443 := bstep (se 1 (by rfl) ⟨350582, by rfl⟩ : syracuseStep 467443 = 701165) B701165
theorem B696833 : Blo 463784 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B467459 : Blo 463784 467459 := bstep (se 1 (by rfl) ⟨350594, by rfl⟩ : syracuseStep 467459 = 701189) B701189
theorem B696851 : Blo 463784 696851 := bstep (se 1 (by rfl) ⟨522638, by rfl⟩ : syracuseStep 696851 = 1045277) B1045277
theorem B598547 : Blo 463784 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B467475 : Blo 463784 467475 := bstep (se 1 (by rfl) ⟨350606, by rfl⟩ : syracuseStep 467475 = 701213) B701213
theorem B467491 : Blo 463784 467491 := bstep (se 1 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 467491 = 701237) B701237
theorem B696881 : Blo 463784 696881 := bstep (se 2 (by rfl) ⟨261330, by rfl⟩ : syracuseStep 696881 = 522661) B522661
theorem B467507 : Blo 463784 467507 := bstep (se 1 (by rfl) ⟨350630, by rfl⟩ : syracuseStep 467507 = 701261) B701261
theorem B696899 : Blo 463784 696899 := bstep (se 1 (by rfl) ⟨522674, by rfl⟩ : syracuseStep 696899 = 1045349) B1045349
theorem B467523 : Blo 463784 467523 := bstep (se 1 (by rfl) ⟨350642, by rfl⟩ : syracuseStep 467523 = 701285) B701285
theorem B467539 : Blo 463784 467539 := bstep (se 1 (by rfl) ⟨350654, by rfl⟩ : syracuseStep 467539 = 701309) B701309
theorem B696929 : Blo 463784 696929 := bstep (se 2 (by rfl) ⟨261348, by rfl⟩ : syracuseStep 696929 = 522697) B522697
theorem B467555 : Blo 463784 467555 := bstep (se 1 (by rfl) ⟨350666, by rfl⟩ : syracuseStep 467555 = 701333) B701333
theorem B1254001 : Blo 463784 1254001 := bstep (se 2 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 1254001 = 940501) B940501
theorem B696947 : Blo 463784 696947 := bstep (se 1 (by rfl) ⟨522710, by rfl⟩ : syracuseStep 696947 = 1045421) B1045421
theorem B467571 : Blo 463784 467571 := bstep (se 1 (by rfl) ⟨350678, by rfl⟩ : syracuseStep 467571 = 701357) B701357
theorem B467587 : Blo 463784 467587 := bstep (se 1 (by rfl) ⟨350690, by rfl⟩ : syracuseStep 467587 = 701381) B701381
theorem B696977 : Blo 463784 696977 := bstep (se 2 (by rfl) ⟨261366, by rfl⟩ : syracuseStep 696977 = 522733) B522733
theorem B467603 : Blo 463784 467603 := bstep (se 1 (by rfl) ⟨350702, by rfl⟩ : syracuseStep 467603 = 701405) B701405
theorem B696995 : Blo 463784 696995 := bstep (se 1 (by rfl) ⟨522746, by rfl⟩ : syracuseStep 696995 = 1045493) B1045493
theorem B467619 : Blo 463784 467619 := bstep (se 1 (by rfl) ⟨350714, by rfl⟩ : syracuseStep 467619 = 701429) B701429
theorem B467635 : Blo 463784 467635 := bstep (se 1 (by rfl) ⟨350726, by rfl⟩ : syracuseStep 467635 = 701453) B701453
theorem B697025 : Blo 463784 697025 := bstep (se 2 (by rfl) ⟨261384, by rfl⟩ : syracuseStep 697025 = 522769) B522769
theorem B467651 : Blo 463784 467651 := bstep (se 1 (by rfl) ⟨350738, by rfl⟩ : syracuseStep 467651 = 701477) B701477
theorem B697043 : Blo 463784 697043 := bstep (se 1 (by rfl) ⟨522782, by rfl⟩ : syracuseStep 697043 = 1045565) B1045565
theorem B467667 : Blo 463784 467667 := bstep (se 1 (by rfl) ⟨350750, by rfl⟩ : syracuseStep 467667 = 701501) B701501
theorem B467683 : Blo 463784 467683 := bstep (se 1 (by rfl) ⟨350762, by rfl⟩ : syracuseStep 467683 = 701525) B701525
theorem B697073 : Blo 463784 697073 := bstep (se 2 (by rfl) ⟨261402, by rfl⟩ : syracuseStep 697073 = 522805) B522805
theorem B467699 : Blo 463784 467699 := bstep (se 1 (by rfl) ⟨350774, by rfl⟩ : syracuseStep 467699 = 701549) B701549
theorem B697091 : Blo 463784 697091 := bstep (se 1 (by rfl) ⟨522818, by rfl⟩ : syracuseStep 697091 = 1045637) B1045637
theorem B467715 : Blo 463784 467715 := bstep (se 1 (by rfl) ⟨350786, by rfl⟩ : syracuseStep 467715 = 701573) B701573
theorem B467731 : Blo 463784 467731 := bstep (se 1 (by rfl) ⟨350798, by rfl⟩ : syracuseStep 467731 = 701597) B701597
theorem B697121 : Blo 463784 697121 := bstep (se 2 (by rfl) ⟨261420, by rfl⟩ : syracuseStep 697121 = 522841) B522841
theorem B467747 : Blo 463784 467747 := bstep (se 1 (by rfl) ⟨350810, by rfl⟩ : syracuseStep 467747 = 701621) B701621
theorem B2237233 : Blo 463784 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B697139 : Blo 463784 697139 := bstep (se 1 (by rfl) ⟨522854, by rfl⟩ : syracuseStep 697139 = 1045709) B1045709
theorem B467763 : Blo 463784 467763 := bstep (se 1 (by rfl) ⟨350822, by rfl⟩ : syracuseStep 467763 = 701645) B701645
theorem B467779 : Blo 463784 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B697169 : Blo 463784 697169 := bstep (se 2 (by rfl) ⟨261438, by rfl⟩ : syracuseStep 697169 = 522877) B522877
theorem B631649 : Blo 463784 631649 := bstep (se 2 (by rfl) ⟨236868, by rfl⟩ : syracuseStep 631649 = 473737) B473737
theorem B697187 : Blo 463784 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B697217 : Blo 463784 697217 := bstep (se 2 (by rfl) ⟨261456, by rfl⟩ : syracuseStep 697217 = 522913) B522913
theorem B697235 : Blo 463784 697235 := bstep (se 1 (by rfl) ⟨522926, by rfl⟩ : syracuseStep 697235 = 1045853) B1045853
theorem B697265 : Blo 463784 697265 := bstep (se 2 (by rfl) ⟨261474, by rfl⟩ : syracuseStep 697265 = 522949) B522949
theorem B697283 : Blo 463784 697283 := bstep (se 1 (by rfl) ⟨522962, by rfl⟩ : syracuseStep 697283 = 1045925) B1045925
theorem B631747 : Blo 463784 631747 := bstep (se 1 (by rfl) ⟨473810, by rfl⟩ : syracuseStep 631747 = 947621) B947621
theorem B664529 : Blo 463784 664529 := bstep (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) B498397
theorem B697313 : Blo 463784 697313 := bstep (se 2 (by rfl) ⟨261492, by rfl⟩ : syracuseStep 697313 = 522985) B522985
theorem B697331 : Blo 463784 697331 := bstep (se 1 (by rfl) ⟨522998, by rfl⟩ : syracuseStep 697331 = 1045997) B1045997
theorem B697361 : Blo 463784 697361 := bstep (se 2 (by rfl) ⟨261510, by rfl⟩ : syracuseStep 697361 = 523021) B523021
theorem B697379 : Blo 463784 697379 := bstep (se 1 (by rfl) ⟨523034, by rfl⟩ : syracuseStep 697379 = 1046069) B1046069
theorem B17409077 : Blo 463784 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B697409 : Blo 463784 697409 := bstep (se 2 (by rfl) ⟨261528, by rfl⟩ : syracuseStep 697409 = 523057) B523057
theorem B664643 : Blo 463784 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B697427 : Blo 463784 697427 := bstep (se 1 (by rfl) ⟨523070, by rfl⟩ : syracuseStep 697427 = 1046141) B1046141
theorem B697457 : Blo 463784 697457 := bstep (se 2 (by rfl) ⟨261546, by rfl⟩ : syracuseStep 697457 = 523093) B523093
theorem B697475 : Blo 463784 697475 := bstep (se 1 (by rfl) ⟨523106, by rfl⟩ : syracuseStep 697475 = 1046213) B1046213
theorem B664723 : Blo 463784 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B697505 : Blo 463784 697505 := bstep (se 2 (by rfl) ⟨261564, by rfl⟩ : syracuseStep 697505 = 523129) B523129
theorem B697523 : Blo 463784 697523 := bstep (se 1 (by rfl) ⟨523142, by rfl⟩ : syracuseStep 697523 = 1046285) B1046285
theorem B697553 : Blo 463784 697553 := bstep (se 2 (by rfl) ⟨261582, by rfl⟩ : syracuseStep 697553 = 523165) B523165
theorem B697571 : Blo 463784 697571 := bstep (se 1 (by rfl) ⟨523178, by rfl⟩ : syracuseStep 697571 = 1046357) B1046357
theorem B697601 : Blo 463784 697601 := bstep (se 2 (by rfl) ⟨261600, by rfl⟩ : syracuseStep 697601 = 523201) B523201
theorem B697619 : Blo 463784 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B697649 : Blo 463784 697649 := bstep (se 2 (by rfl) ⟨261618, by rfl⟩ : syracuseStep 697649 = 523237) B523237
theorem B697667 : Blo 463784 697667 := bstep (se 1 (by rfl) ⟨523250, by rfl⟩ : syracuseStep 697667 = 1046501) B1046501
theorem B697697 : Blo 463784 697697 := bstep (se 2 (by rfl) ⟨261636, by rfl⟩ : syracuseStep 697697 = 523273) B523273
theorem B697715 : Blo 463784 697715 := bstep (se 1 (by rfl) ⟨523286, by rfl⟩ : syracuseStep 697715 = 1046573) B1046573
theorem B697745 : Blo 463784 697745 := bstep (se 2 (by rfl) ⟨261654, by rfl⟩ : syracuseStep 697745 = 523309) B523309
theorem B697763 : Blo 463784 697763 := bstep (se 1 (by rfl) ⟨523322, by rfl⟩ : syracuseStep 697763 = 1046645) B1046645
theorem B697793 : Blo 463784 697793 := bstep (se 2 (by rfl) ⟨261672, by rfl⟩ : syracuseStep 697793 = 523345) B523345
theorem B697811 : Blo 463784 697811 := bstep (se 1 (by rfl) ⟨523358, by rfl⟩ : syracuseStep 697811 = 1046717) B1046717
theorem B697841 : Blo 463784 697841 := bstep (se 2 (by rfl) ⟨261690, by rfl⟩ : syracuseStep 697841 = 523381) B523381
theorem B697859 : Blo 463784 697859 := bstep (se 1 (by rfl) ⟨523394, by rfl⟩ : syracuseStep 697859 = 1046789) B1046789
theorem B3974669 : Blo 463784 3974669 := bstep (se 3 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 3974669 = 1490501) B1490501
theorem B697889 : Blo 463784 697889 := bstep (se 2 (by rfl) ⟨261708, by rfl⟩ : syracuseStep 697889 = 523417) B523417
theorem B697907 : Blo 463784 697907 := bstep (se 1 (by rfl) ⟨523430, by rfl⟩ : syracuseStep 697907 = 1046861) B1046861
theorem B4531781 : Blo 463784 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B697937 : Blo 463784 697937 := bstep (se 2 (by rfl) ⟨261726, by rfl⟩ : syracuseStep 697937 = 523453) B523453
theorem B697955 : Blo 463784 697955 := bstep (se 1 (by rfl) ⟨523466, by rfl⟩ : syracuseStep 697955 = 1046933) B1046933
theorem B1680995 : Blo 463784 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B3548771 : Blo 463784 3548771 := bstep (se 1 (by rfl) ⟨2661578, by rfl⟩ : syracuseStep 3548771 = 5323157) B5323157
theorem B697985 : Blo 463784 697985 := bstep (se 2 (by rfl) ⟨261744, by rfl⟩ : syracuseStep 697985 = 523489) B523489
theorem B698003 : Blo 463784 698003 := bstep (se 1 (by rfl) ⟨523502, by rfl⟩ : syracuseStep 698003 = 1047005) B1047005
theorem B698033 : Blo 463784 698033 := bstep (se 2 (by rfl) ⟨261762, by rfl⟩ : syracuseStep 698033 = 523525) B523525
theorem B665281 : Blo 463784 665281 := bstep (se 2 (by rfl) ⟨249480, by rfl⟩ : syracuseStep 665281 = 498961) B498961
theorem B698051 : Blo 463784 698051 := bstep (se 1 (by rfl) ⟨523538, by rfl⟩ : syracuseStep 698051 = 1047077) B1047077
theorem B698081 : Blo 463784 698081 := bstep (se 2 (by rfl) ⟨261780, by rfl⟩ : syracuseStep 698081 = 523561) B523561
theorem B698099 : Blo 463784 698099 := bstep (se 1 (by rfl) ⟨523574, by rfl⟩ : syracuseStep 698099 = 1047149) B1047149
theorem B698129 : Blo 463784 698129 := bstep (se 2 (by rfl) ⟨261798, by rfl⟩ : syracuseStep 698129 = 523597) B523597
theorem B698147 : Blo 463784 698147 := bstep (se 1 (by rfl) ⟨523610, by rfl⟩ : syracuseStep 698147 = 1047221) B1047221
theorem B698177 : Blo 463784 698177 := bstep (se 2 (by rfl) ⟨261816, by rfl⟩ : syracuseStep 698177 = 523633) B523633
theorem B698195 : Blo 463784 698195 := bstep (se 1 (by rfl) ⟨523646, by rfl⟩ : syracuseStep 698195 = 1047293) B1047293
theorem B698225 : Blo 463784 698225 := bstep (se 2 (by rfl) ⟨261834, by rfl⟩ : syracuseStep 698225 = 523669) B523669
theorem B698243 : Blo 463784 698243 := bstep (se 1 (by rfl) ⟨523682, by rfl⟩ : syracuseStep 698243 = 1047365) B1047365
theorem B698273 : Blo 463784 698273 := bstep (se 2 (by rfl) ⟨261852, by rfl⟩ : syracuseStep 698273 = 523705) B523705
theorem B1255331 : Blo 463784 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B698291 : Blo 463784 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B8071109 : Blo 463784 8071109 := bstep (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) B1513333
theorem B698321 : Blo 463784 698321 := bstep (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) B523741
theorem B698339 : Blo 463784 698339 := bstep (se 1 (by rfl) ⟨523754, by rfl⟩ : syracuseStep 698339 = 1047509) B1047509
theorem B698369 : Blo 463784 698369 := bstep (se 2 (by rfl) ⟨261888, by rfl⟩ : syracuseStep 698369 = 523777) B523777
theorem B698387 : Blo 463784 698387 := bstep (se 1 (by rfl) ⟨523790, by rfl⟩ : syracuseStep 698387 = 1047581) B1047581
theorem B698417 : Blo 463784 698417 := bstep (se 2 (by rfl) ⟨261906, by rfl⟩ : syracuseStep 698417 = 523813) B523813
theorem B698435 : Blo 463784 698435 := bstep (se 1 (by rfl) ⟨523826, by rfl⟩ : syracuseStep 698435 = 1047653) B1047653
theorem B698465 : Blo 463784 698465 := bstep (se 2 (by rfl) ⟨261924, by rfl⟩ : syracuseStep 698465 = 523849) B523849
theorem B698483 : Blo 463784 698483 := bstep (se 1 (by rfl) ⟨523862, by rfl⟩ : syracuseStep 698483 = 1047725) B1047725
theorem B698513 : Blo 463784 698513 := bstep (se 2 (by rfl) ⟨261942, by rfl⟩ : syracuseStep 698513 = 523885) B523885
theorem B698531 : Blo 463784 698531 := bstep (se 1 (by rfl) ⟨523898, by rfl⟩ : syracuseStep 698531 = 1047797) B1047797
theorem B698561 : Blo 463784 698561 := bstep (se 2 (by rfl) ⟨261960, by rfl⟩ : syracuseStep 698561 = 523921) B523921
theorem B698579 : Blo 463784 698579 := bstep (se 1 (by rfl) ⟨523934, by rfl⟩ : syracuseStep 698579 = 1047869) B1047869
theorem B5056739 : Blo 463784 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B698609 : Blo 463784 698609 := bstep (se 2 (by rfl) ⟨261978, by rfl⟩ : syracuseStep 698609 = 523957) B523957
theorem B698627 : Blo 463784 698627 := bstep (se 1 (by rfl) ⟨523970, by rfl⟩ : syracuseStep 698627 = 1047941) B1047941
theorem B698657 : Blo 463784 698657 := bstep (se 2 (by rfl) ⟨261996, by rfl⟩ : syracuseStep 698657 = 523993) B523993
theorem B698675 : Blo 463784 698675 := bstep (se 1 (by rfl) ⟨524006, by rfl⟩ : syracuseStep 698675 = 1048013) B1048013
theorem B698705 : Blo 463784 698705 := bstep (se 2 (by rfl) ⟨262014, by rfl⟩ : syracuseStep 698705 = 524029) B524029
theorem B698723 : Blo 463784 698723 := bstep (se 1 (by rfl) ⟨524042, by rfl⟩ : syracuseStep 698723 = 1048085) B1048085
theorem B698753 : Blo 463784 698753 := bstep (se 2 (by rfl) ⟨262032, by rfl⟩ : syracuseStep 698753 = 524065) B524065
theorem B665987 : Blo 463784 665987 := bstep (se 1 (by rfl) ⟨499490, by rfl⟩ : syracuseStep 665987 = 998981) B998981
theorem B698771 : Blo 463784 698771 := bstep (se 1 (by rfl) ⟨524078, by rfl⟩ : syracuseStep 698771 = 1048157) B1048157
theorem B1321393 : Blo 463784 1321393 := bstep (se 2 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 1321393 = 991045) B991045
theorem B698801 : Blo 463784 698801 := bstep (se 2 (by rfl) ⟨262050, by rfl⟩ : syracuseStep 698801 = 524101) B524101
theorem B698819 : Blo 463784 698819 := bstep (se 1 (by rfl) ⟨524114, by rfl⟩ : syracuseStep 698819 = 1048229) B1048229
theorem B698849 : Blo 463784 698849 := bstep (se 2 (by rfl) ⟨262068, by rfl⟩ : syracuseStep 698849 = 524137) B524137
theorem B698867 : Blo 463784 698867 := bstep (se 1 (by rfl) ⟨524150, by rfl⟩ : syracuseStep 698867 = 1048301) B1048301
theorem B698897 : Blo 463784 698897 := bstep (se 2 (by rfl) ⟨262086, by rfl⟩ : syracuseStep 698897 = 524173) B524173
theorem B698915 : Blo 463784 698915 := bstep (se 1 (by rfl) ⟨524186, by rfl⟩ : syracuseStep 698915 = 1048373) B1048373
theorem B698945 : Blo 463784 698945 := bstep (se 2 (by rfl) ⟨262104, by rfl⟩ : syracuseStep 698945 = 524209) B524209
theorem B698963 : Blo 463784 698963 := bstep (se 1 (by rfl) ⟨524222, by rfl⟩ : syracuseStep 698963 = 1048445) B1048445
theorem B698993 : Blo 463784 698993 := bstep (se 2 (by rfl) ⟨262122, by rfl⟩ : syracuseStep 698993 = 524245) B524245
theorem B6728305 : Blo 463784 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B699011 : Blo 463784 699011 := bstep (se 1 (by rfl) ⟨524258, by rfl⟩ : syracuseStep 699011 = 1048517) B1048517
theorem B699041 : Blo 463784 699041 := bstep (se 2 (by rfl) ⟨262140, by rfl⟩ : syracuseStep 699041 = 524281) B524281
theorem B699059 : Blo 463784 699059 := bstep (se 1 (by rfl) ⟨524294, by rfl⟩ : syracuseStep 699059 = 1048589) B1048589
theorem B1321667 : Blo 463784 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B1190609 : Blo 463784 1190609 := bstep (se 2 (by rfl) ⟨446478, by rfl⟩ : syracuseStep 1190609 = 892957) B892957
theorem B699089 : Blo 463784 699089 := bstep (se 2 (by rfl) ⟨262158, by rfl⟩ : syracuseStep 699089 = 524317) B524317
theorem B699107 : Blo 463784 699107 := bstep (se 1 (by rfl) ⟨524330, by rfl⟩ : syracuseStep 699107 = 1048661) B1048661
theorem B699137 : Blo 463784 699137 := bstep (se 2 (by rfl) ⟨262176, by rfl⟩ : syracuseStep 699137 = 524353) B524353
theorem B699155 : Blo 463784 699155 := bstep (se 1 (by rfl) ⟨524366, by rfl⟩ : syracuseStep 699155 = 1048733) B1048733
theorem B699185 : Blo 463784 699185 := bstep (se 2 (by rfl) ⟨262194, by rfl⟩ : syracuseStep 699185 = 524389) B524389
theorem B699203 : Blo 463784 699203 := bstep (se 1 (by rfl) ⟨524402, by rfl⟩ : syracuseStep 699203 = 1048805) B1048805
theorem B699233 : Blo 463784 699233 := bstep (se 2 (by rfl) ⟨262212, by rfl⟩ : syracuseStep 699233 = 524425) B524425
theorem B699251 : Blo 463784 699251 := bstep (se 1 (by rfl) ⟨524438, by rfl⟩ : syracuseStep 699251 = 1048877) B1048877
theorem B1321859 : Blo 463784 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B699281 : Blo 463784 699281 := bstep (se 2 (by rfl) ⟨262230, by rfl⟩ : syracuseStep 699281 = 524461) B524461
theorem B699299 : Blo 463784 699299 := bstep (se 1 (by rfl) ⟨524474, by rfl⟩ : syracuseStep 699299 = 1048949) B1048949
theorem B699329 : Blo 463784 699329 := bstep (se 2 (by rfl) ⟨262248, by rfl⟩ : syracuseStep 699329 = 524497) B524497
theorem B1256401 : Blo 463784 1256401 := bstep (se 2 (by rfl) ⟨471150, by rfl⟩ : syracuseStep 1256401 = 942301) B942301
theorem B699347 : Blo 463784 699347 := bstep (se 1 (by rfl) ⟨524510, by rfl⟩ : syracuseStep 699347 = 1049021) B1049021
theorem B699377 : Blo 463784 699377 := bstep (se 2 (by rfl) ⟨262266, by rfl⟩ : syracuseStep 699377 = 524533) B524533
theorem B797681 : Blo 463784 797681 := bstep (se 2 (by rfl) ⟨299130, by rfl⟩ : syracuseStep 797681 = 598261) B598261
theorem B699395 : Blo 463784 699395 := bstep (se 1 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 699395 = 1049093) B1049093
theorem B1518605 : Blo 463784 1518605 := bstep (se 3 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 1518605 = 569477) B569477
theorem B1256465 : Blo 463784 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B699425 : Blo 463784 699425 := bstep (se 2 (by rfl) ⟨262284, by rfl⟩ : syracuseStep 699425 = 524569) B524569
theorem B699443 : Blo 463784 699443 := bstep (se 1 (by rfl) ⟨524582, by rfl⟩ : syracuseStep 699443 = 1049165) B1049165
theorem B699473 : Blo 463784 699473 := bstep (se 2 (by rfl) ⟨262302, by rfl⟩ : syracuseStep 699473 = 524605) B524605
theorem B699491 : Blo 463784 699491 := bstep (se 1 (by rfl) ⟨524618, by rfl⟩ : syracuseStep 699491 = 1049237) B1049237
theorem B699521 : Blo 463784 699521 := bstep (se 2 (by rfl) ⟨262320, by rfl⟩ : syracuseStep 699521 = 524641) B524641
theorem B1485965 : Blo 463784 1485965 := bstep (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) B557237
theorem B699539 : Blo 463784 699539 := bstep (se 1 (by rfl) ⟨524654, by rfl⟩ : syracuseStep 699539 = 1049309) B1049309
theorem B699569 : Blo 463784 699569 := bstep (se 2 (by rfl) ⟨262338, by rfl⟩ : syracuseStep 699569 = 524677) B524677
theorem B699587 : Blo 463784 699587 := bstep (se 1 (by rfl) ⟨524690, by rfl⟩ : syracuseStep 699587 = 1049381) B1049381
theorem B699617 : Blo 463784 699617 := bstep (se 2 (by rfl) ⟨262356, by rfl⟩ : syracuseStep 699617 = 524713) B524713
theorem B994531 : Blo 463784 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B699635 : Blo 463784 699635 := bstep (se 1 (by rfl) ⟨524726, by rfl⟩ : syracuseStep 699635 = 1049453) B1049453
theorem B699665 : Blo 463784 699665 := bstep (se 2 (by rfl) ⟨262374, by rfl⟩ : syracuseStep 699665 = 524749) B524749
theorem B699683 : Blo 463784 699683 := bstep (se 1 (by rfl) ⟨524762, by rfl⟩ : syracuseStep 699683 = 1049525) B1049525
theorem B699713 : Blo 463784 699713 := bstep (se 2 (by rfl) ⟨262392, by rfl⟩ : syracuseStep 699713 = 524785) B524785
theorem B699731 : Blo 463784 699731 := bstep (se 1 (by rfl) ⟨524798, by rfl⟩ : syracuseStep 699731 = 1049597) B1049597
theorem B699761 : Blo 463784 699761 := bstep (se 2 (by rfl) ⟨262410, by rfl⟩ : syracuseStep 699761 = 524821) B524821
theorem B699779 : Blo 463784 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B699809 : Blo 463784 699809 := bstep (se 2 (by rfl) ⟨262428, by rfl⟩ : syracuseStep 699809 = 524857) B524857
theorem B699827 : Blo 463784 699827 := bstep (se 1 (by rfl) ⟨524870, by rfl⟩ : syracuseStep 699827 = 1049741) B1049741
theorem B699857 : Blo 463784 699857 := bstep (se 2 (by rfl) ⟨262446, by rfl⟩ : syracuseStep 699857 = 524893) B524893
theorem B699875 : Blo 463784 699875 := bstep (se 1 (by rfl) ⟨524906, by rfl⟩ : syracuseStep 699875 = 1049813) B1049813
theorem B699905 : Blo 463784 699905 := bstep (se 2 (by rfl) ⟨262464, by rfl⟩ : syracuseStep 699905 = 524929) B524929
theorem B699923 : Blo 463784 699923 := bstep (se 1 (by rfl) ⟨524942, by rfl⟩ : syracuseStep 699923 = 1049885) B1049885
theorem B699953 : Blo 463784 699953 := bstep (se 2 (by rfl) ⟨262482, by rfl⟩ : syracuseStep 699953 = 524965) B524965
theorem B699971 : Blo 463784 699971 := bstep (se 1 (by rfl) ⟨524978, by rfl⟩ : syracuseStep 699971 = 1049957) B1049957
theorem B700001 : Blo 463784 700001 := bstep (se 2 (by rfl) ⟨262500, by rfl⟩ : syracuseStep 700001 = 525001) B525001
theorem B4763249 : Blo 463784 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B700019 : Blo 463784 700019 := bstep (se 1 (by rfl) ⟨525014, by rfl⟩ : syracuseStep 700019 = 1050029) B1050029
theorem B700049 : Blo 463784 700049 := bstep (se 2 (by rfl) ⟨262518, by rfl⟩ : syracuseStep 700049 = 525037) B525037
theorem B700067 : Blo 463784 700067 := bstep (se 1 (by rfl) ⟨525050, by rfl⟩ : syracuseStep 700067 = 1050101) B1050101
theorem B1322669 : Blo 463784 1322669 := bstep (se 3 (by rfl) ⟨248000, by rfl⟩ : syracuseStep 1322669 = 496001) B496001
theorem B700097 : Blo 463784 700097 := bstep (se 2 (by rfl) ⟨262536, by rfl⟩ : syracuseStep 700097 = 525073) B525073
theorem B700115 : Blo 463784 700115 := bstep (se 1 (by rfl) ⟨525086, by rfl⟩ : syracuseStep 700115 = 1050173) B1050173
theorem B700145 : Blo 463784 700145 := bstep (se 2 (by rfl) ⟨262554, by rfl⟩ : syracuseStep 700145 = 525109) B525109
theorem B700163 : Blo 463784 700163 := bstep (se 1 (by rfl) ⟨525122, by rfl⟩ : syracuseStep 700163 = 1050245) B1050245
theorem B700193 : Blo 463784 700193 := bstep (se 2 (by rfl) ⟨262572, by rfl⟩ : syracuseStep 700193 = 525145) B525145
theorem B700211 : Blo 463784 700211 := bstep (se 1 (by rfl) ⟨525158, by rfl⟩ : syracuseStep 700211 = 1050317) B1050317
theorem B700241 : Blo 463784 700241 := bstep (se 2 (by rfl) ⟨262590, by rfl⟩ : syracuseStep 700241 = 525181) B525181
theorem B1322851 : Blo 463784 1322851 := bstep (se 1 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 1322851 = 1984277) B1984277
theorem B3977059 : Blo 463784 3977059 := bstep (se 1 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 3977059 = 5965589) B5965589
theorem B700259 : Blo 463784 700259 := bstep (se 1 (by rfl) ⟨525194, by rfl⟩ : syracuseStep 700259 = 1050389) B1050389
theorem B1257329 : Blo 463784 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B700289 : Blo 463784 700289 := bstep (se 2 (by rfl) ⟨262608, by rfl⟩ : syracuseStep 700289 = 525217) B525217
theorem B1421201 : Blo 463784 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B700307 : Blo 463784 700307 := bstep (se 1 (by rfl) ⟨525230, by rfl⟩ : syracuseStep 700307 = 1050461) B1050461
theorem B700337 : Blo 463784 700337 := bstep (se 2 (by rfl) ⟨262626, by rfl⟩ : syracuseStep 700337 = 525253) B525253
theorem B700355 : Blo 463784 700355 := bstep (se 1 (by rfl) ⟨525266, by rfl⟩ : syracuseStep 700355 = 1050533) B1050533
theorem B700385 : Blo 463784 700385 := bstep (se 2 (by rfl) ⟨262644, by rfl⟩ : syracuseStep 700385 = 525289) B525289
theorem B700403 : Blo 463784 700403 := bstep (se 1 (by rfl) ⟨525302, by rfl⟩ : syracuseStep 700403 = 1050605) B1050605
theorem B700433 : Blo 463784 700433 := bstep (se 2 (by rfl) ⟨262662, by rfl⟩ : syracuseStep 700433 = 525325) B525325
theorem B536611 : Blo 463784 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B700451 : Blo 463784 700451 := bstep (se 1 (by rfl) ⟨525338, by rfl⟩ : syracuseStep 700451 = 1050677) B1050677
theorem B700481 : Blo 463784 700481 := bstep (se 2 (by rfl) ⟨262680, by rfl⟩ : syracuseStep 700481 = 525361) B525361
theorem B700499 : Blo 463784 700499 := bstep (se 1 (by rfl) ⟨525374, by rfl⟩ : syracuseStep 700499 = 1050749) B1050749
theorem B700529 : Blo 463784 700529 := bstep (se 2 (by rfl) ⟨262698, by rfl⟩ : syracuseStep 700529 = 525397) B525397
theorem B700547 : Blo 463784 700547 := bstep (se 1 (by rfl) ⟨525410, by rfl⟩ : syracuseStep 700547 = 1050821) B1050821
theorem B700577 : Blo 463784 700577 := bstep (se 2 (by rfl) ⟨262716, by rfl⟩ : syracuseStep 700577 = 525433) B525433
theorem B700595 : Blo 463784 700595 := bstep (se 1 (by rfl) ⟨525446, by rfl⟩ : syracuseStep 700595 = 1050893) B1050893
theorem B1257677 : Blo 463784 1257677 := bstep (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) B471629
theorem B700625 : Blo 463784 700625 := bstep (se 2 (by rfl) ⟨262734, by rfl⟩ : syracuseStep 700625 = 525469) B525469
theorem B700643 : Blo 463784 700643 := bstep (se 1 (by rfl) ⟨525482, by rfl⟩ : syracuseStep 700643 = 1050965) B1050965
theorem B700673 : Blo 463784 700673 := bstep (se 2 (by rfl) ⟨262752, by rfl⟩ : syracuseStep 700673 = 525505) B525505
theorem B700691 : Blo 463784 700691 := bstep (se 1 (by rfl) ⟨525518, by rfl⟩ : syracuseStep 700691 = 1051037) B1051037
theorem B700721 : Blo 463784 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B700739 : Blo 463784 700739 := bstep (se 1 (by rfl) ⟨525554, by rfl⟩ : syracuseStep 700739 = 1051109) B1051109
theorem B1323341 : Blo 463784 1323341 := bstep (se 3 (by rfl) ⟨248126, by rfl⟩ : syracuseStep 1323341 = 496253) B496253
theorem B700769 : Blo 463784 700769 := bstep (se 2 (by rfl) ⟨262788, by rfl⟩ : syracuseStep 700769 = 525577) B525577
theorem B700787 : Blo 463784 700787 := bstep (se 1 (by rfl) ⟨525590, by rfl⟩ : syracuseStep 700787 = 1051181) B1051181
theorem B700817 : Blo 463784 700817 := bstep (se 2 (by rfl) ⟨262806, by rfl⟩ : syracuseStep 700817 = 525613) B525613
theorem B700835 : Blo 463784 700835 := bstep (se 1 (by rfl) ⟨525626, by rfl⟩ : syracuseStep 700835 = 1051253) B1051253
theorem B700865 : Blo 463784 700865 := bstep (se 2 (by rfl) ⟨262824, by rfl⟩ : syracuseStep 700865 = 525649) B525649
theorem B700883 : Blo 463784 700883 := bstep (se 1 (by rfl) ⟨525662, by rfl⟩ : syracuseStep 700883 = 1051325) B1051325
theorem B700913 : Blo 463784 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B700931 : Blo 463784 700931 := bstep (se 1 (by rfl) ⟨525698, by rfl⟩ : syracuseStep 700931 = 1051397) B1051397
theorem B700961 : Blo 463784 700961 := bstep (se 2 (by rfl) ⟨262860, by rfl⟩ : syracuseStep 700961 = 525721) B525721
theorem B700979 : Blo 463784 700979 := bstep (se 1 (by rfl) ⟨525734, by rfl⟩ : syracuseStep 700979 = 1051469) B1051469
theorem B1421891 : Blo 463784 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B701009 : Blo 463784 701009 := bstep (se 2 (by rfl) ⟨262878, by rfl⟩ : syracuseStep 701009 = 525757) B525757
theorem B701027 : Blo 463784 701027 := bstep (se 1 (by rfl) ⟨525770, by rfl⟩ : syracuseStep 701027 = 1051541) B1051541
theorem B4239985 : Blo 463784 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B1684081 : Blo 463784 1684081 := bstep (se 2 (by rfl) ⟨631530, by rfl⟩ : syracuseStep 1684081 = 1263061) B1263061
theorem B701057 : Blo 463784 701057 := bstep (se 2 (by rfl) ⟨262896, by rfl⟩ : syracuseStep 701057 = 525793) B525793
theorem B10039949 : Blo 463784 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B701075 : Blo 463784 701075 := bstep (se 1 (by rfl) ⟨525806, by rfl⟩ : syracuseStep 701075 = 1051613) B1051613
theorem B701105 : Blo 463784 701105 := bstep (se 2 (by rfl) ⟨262914, by rfl⟩ : syracuseStep 701105 = 525829) B525829
theorem B1487555 : Blo 463784 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B701123 : Blo 463784 701123 := bstep (se 1 (by rfl) ⟨525842, by rfl⟩ : syracuseStep 701123 = 1051685) B1051685
theorem B2994893 : Blo 463784 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B701153 : Blo 463784 701153 := bstep (se 2 (by rfl) ⟨262932, by rfl⟩ : syracuseStep 701153 = 525865) B525865
theorem B1880803 : Blo 463784 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B701171 : Blo 463784 701171 := bstep (se 1 (by rfl) ⟨525878, by rfl⟩ : syracuseStep 701171 = 1051757) B1051757
theorem B701201 : Blo 463784 701201 := bstep (se 2 (by rfl) ⟨262950, by rfl⟩ : syracuseStep 701201 = 525901) B525901
theorem B701219 : Blo 463784 701219 := bstep (se 1 (by rfl) ⟨525914, by rfl⟩ : syracuseStep 701219 = 1051829) B1051829
theorem B701249 : Blo 463784 701249 := bstep (se 2 (by rfl) ⟨262968, by rfl⟩ : syracuseStep 701249 = 525937) B525937
theorem B701267 : Blo 463784 701267 := bstep (se 1 (by rfl) ⟨525950, by rfl⟩ : syracuseStep 701267 = 1051901) B1051901
theorem B701297 : Blo 463784 701297 := bstep (se 2 (by rfl) ⟨262986, by rfl⟩ : syracuseStep 701297 = 525973) B525973
theorem B701315 : Blo 463784 701315 := bstep (se 1 (by rfl) ⟨525986, by rfl⟩ : syracuseStep 701315 = 1051973) B1051973
theorem B701345 : Blo 463784 701345 := bstep (se 2 (by rfl) ⟨263004, by rfl⟩ : syracuseStep 701345 = 526009) B526009
theorem B701363 : Blo 463784 701363 := bstep (se 1 (by rfl) ⟨526022, by rfl⟩ : syracuseStep 701363 = 1052045) B1052045
theorem B701393 : Blo 463784 701393 := bstep (se 2 (by rfl) ⟨263022, by rfl⟩ : syracuseStep 701393 = 526045) B526045
theorem B5321699 : Blo 463784 5321699 := bstep (se 1 (by rfl) ⟨3991274, by rfl⟩ : syracuseStep 5321699 = 7982549) B7982549
theorem B701411 : Blo 463784 701411 := bstep (se 1 (by rfl) ⟨526058, by rfl⟩ : syracuseStep 701411 = 1052117) B1052117
theorem B701441 : Blo 463784 701441 := bstep (se 2 (by rfl) ⟨263040, by rfl⟩ : syracuseStep 701441 = 526081) B526081
theorem B701459 : Blo 463784 701459 := bstep (se 1 (by rfl) ⟨526094, by rfl⟩ : syracuseStep 701459 = 1052189) B1052189
theorem B1258541 : Blo 463784 1258541 := bstep (se 3 (by rfl) ⟨235976, by rfl⟩ : syracuseStep 1258541 = 471953) B471953
theorem B996401 : Blo 463784 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B701489 : Blo 463784 701489 := bstep (se 2 (by rfl) ⟨263058, by rfl⟩ : syracuseStep 701489 = 526117) B526117
theorem B701507 : Blo 463784 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B701537 : Blo 463784 701537 := bstep (se 2 (by rfl) ⟨263076, by rfl⟩ : syracuseStep 701537 = 526153) B526153
theorem B2012273 : Blo 463784 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B701555 : Blo 463784 701555 := bstep (se 1 (by rfl) ⟨526166, by rfl⟩ : syracuseStep 701555 = 1052333) B1052333
theorem B701585 : Blo 463784 701585 := bstep (se 2 (by rfl) ⟨263094, by rfl⟩ : syracuseStep 701585 = 526189) B526189
theorem B701603 : Blo 463784 701603 := bstep (se 1 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 701603 = 1052405) B1052405
theorem B701633 : Blo 463784 701633 := bstep (se 2 (by rfl) ⟨263112, by rfl⟩ : syracuseStep 701633 = 526225) B526225
theorem B2700485 : Blo 463784 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B1684685 : Blo 463784 1684685 := bstep (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) B631757
theorem B701651 : Blo 463784 701651 := bstep (se 1 (by rfl) ⟨526238, by rfl⟩ : syracuseStep 701651 = 1052477) B1052477
theorem B3880163 : Blo 463784 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B38352325 : Blo 463784 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B1324525 : Blo 463784 1324525 := bstep (se 3 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 1324525 = 496697) B496697
theorem B1488451 : Blo 463784 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B1259363 : Blo 463784 1259363 := bstep (se 1 (by rfl) ⟨944522, by rfl⟩ : syracuseStep 1259363 = 1889045) B1889045
theorem B997265 : Blo 463784 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B1620109 : Blo 463784 1620109 := bstep (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) B607541
theorem B1587725 : Blo 463784 1587725 := bstep (se 3 (by rfl) ⟨297698, by rfl⟩ : syracuseStep 1587725 = 595397) B595397
theorem B1325585 : Blo 463784 1325585 := bstep (se 2 (by rfl) ⟨497094, by rfl⟩ : syracuseStep 1325585 = 994189) B994189
theorem B1489553 : Blo 463784 1489553 := bstep (se 2 (by rfl) ⟨558582, by rfl⟩ : syracuseStep 1489553 = 1117165) B1117165
theorem B1489681 : Blo 463784 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B2243555 : Blo 463784 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B3783665 : Blo 463784 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B998563 : Blo 463784 998563 := bstep (se 1 (by rfl) ⟨748922, by rfl⟩ : syracuseStep 998563 = 1497845) B1497845
theorem B1326257 : Blo 463784 1326257 := bstep (se 2 (by rfl) ⟨497346, by rfl⟩ : syracuseStep 1326257 = 994693) B994693
theorem B2244017 : Blo 463784 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B1981901 : Blo 463784 1981901 := bstep (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) B743213
theorem B24592085 : Blo 463784 24592085 := bstep (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) B576377
theorem B1490669 : Blo 463784 1490669 := bstep (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) B559001
theorem B1883917 : Blo 463784 1883917 := bstep (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) B706469
theorem B1327043 : Blo 463784 1327043 := bstep (se 1 (by rfl) ⟨995282, by rfl⟩ : syracuseStep 1327043 = 1990565) B1990565
theorem B1327373 : Blo 463784 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B2244941 : Blo 463784 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B1327441 : Blo 463784 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B3523013 : Blo 463784 3523013 := bstep (se 4 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 3523013 = 660565) B660565
theorem B1327715 : Blo 463784 1327715 := bstep (se 1 (by rfl) ⟨995786, by rfl⟩ : syracuseStep 1327715 = 1991573) B1991573
theorem B672673 : Blo 463784 672673 := bstep (se 2 (by rfl) ⟨252252, by rfl⟩ : syracuseStep 672673 = 504505) B504505
theorem B1983473 : Blo 463784 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1492013 : Blo 463784 1492013 := bstep (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) B559505
theorem B1361197 : Blo 463784 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B1328557 : Blo 463784 1328557 := bstep (se 3 (by rfl) ⟨249104, by rfl⟩ : syracuseStep 1328557 = 498209) B498209
theorem B1328717 : Blo 463784 1328717 := bstep (se 3 (by rfl) ⟨249134, by rfl⟩ : syracuseStep 1328717 = 498269) B498269
theorem B1361549 : Blo 463784 1361549 := bstep (se 3 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 1361549 = 510581) B510581
theorem B1328899 : Blo 463784 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B8407153 : Blo 463784 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B3197069 : Blo 463784 3197069 := bstep (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) B1198901
theorem B3361009 : Blo 463784 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B1493603 : Blo 463784 1493603 := bstep (se 1 (by rfl) ⟨1120202, by rfl⟩ : syracuseStep 1493603 = 2240405) B2240405
theorem B1264241 : Blo 463784 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B707201 : Blo 463784 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B674659 : Blo 463784 674659 := bstep (se 1 (by rfl) ⟨505994, by rfl⟩ : syracuseStep 674659 = 1011989) B1011989
theorem B1330289 : Blo 463784 1330289 := bstep (se 2 (by rfl) ⟨498858, by rfl⟩ : syracuseStep 1330289 = 997717) B997717
theorem B838883 : Blo 463784 838883 := bstep (se 1 (by rfl) ⟨629162, by rfl⟩ : syracuseStep 838883 = 1258325) B1258325
theorem B1494371 : Blo 463784 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B1985933 : Blo 463784 1985933 := bstep (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) B744725
theorem B1887715 : Blo 463784 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B1986275 : Blo 463784 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B1494769 : Blo 463784 1494769 := bstep (se 2 (by rfl) ⟨560538, by rfl⟩ : syracuseStep 1494769 = 1121077) B1121077
theorem B1494883 : Blo 463784 1494883 := bstep (se 1 (by rfl) ⟨1121162, by rfl⟩ : syracuseStep 1494883 = 2242325) B2242325
theorem B2641805 : Blo 463784 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B1560493 : Blo 463784 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B16175045 : Blo 463784 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1331245 : Blo 463784 1331245 := bstep (se 3 (by rfl) ⟨249608, by rfl⟩ : syracuseStep 1331245 = 499217) B499217
theorem B1331473 : Blo 463784 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B1888589 : Blo 463784 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B1331633 : Blo 463784 1331633 := bstep (se 2 (by rfl) ⟨499362, by rfl⟩ : syracuseStep 1331633 = 998725) B998725
theorem B1331747 : Blo 463784 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1495601 : Blo 463784 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B3330629 : Blo 463784 3330629 := bstep (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) B624493
theorem B5034595 : Blo 463784 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B3232453 : Blo 463784 3232453 := bstep (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) B606085
theorem B5034851 : Blo 463784 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B807841 : Blo 463784 807841 := bstep (se 2 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 807841 = 605881) B605881
theorem B1496141 : Blo 463784 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B808177 : Blo 463784 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B2512453 : Blo 463784 2512453 := bstep (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) B471085
theorem B2840453 : Blo 463784 2840453 := bstep (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) B532585
theorem B743393 : Blo 463784 743393 := bstep (se 2 (by rfl) ⟨278772, by rfl⟩ : syracuseStep 743393 = 557545) B557545
theorem B743521 : Blo 463784 743521 := bstep (se 2 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 743521 = 557641) B557641
theorem B3528845 : Blo 463784 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B743905 : Blo 463784 743905 := bstep (se 2 (by rfl) ⟨278964, by rfl⟩ : syracuseStep 743905 = 557929) B557929
theorem B744161 : Blo 463784 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B2349809 : Blo 463784 2349809 := bstep (se 2 (by rfl) ⟨881178, by rfl⟩ : syracuseStep 2349809 = 1762357) B1762357
theorem B2644721 : Blo 463784 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B1498061 : Blo 463784 1498061 := bstep (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) B561773
theorem B1990307 : Blo 463784 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B909041 : Blo 463784 909041 := bstep (se 2 (by rfl) ⟨340890, by rfl⟩ : syracuseStep 909041 = 681781) B681781
theorem B2973773 : Blo 463784 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B745571 : Blo 463784 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B2351267 : Blo 463784 2351267 := bstep (se 1 (by rfl) ⟨1763450, by rfl⟩ : syracuseStep 2351267 = 3526901) B3526901
theorem B2646179 : Blo 463784 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B1565297 : Blo 463784 1565297 := bstep (se 2 (by rfl) ⟨586986, by rfl⟩ : syracuseStep 1565297 = 1173973) B1173973
theorem B2548493 : Blo 463784 2548493 := bstep (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) B955685
theorem B1991537 : Blo 463784 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B746417 : Blo 463784 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B2352077 : Blo 463784 2352077 := bstep (se 3 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 2352077 = 882029) B882029
theorem B1598413 : Blo 463784 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B3531761 : Blo 463784 3531761 := bstep (se 2 (by rfl) ⟨1324410, by rfl⟩ : syracuseStep 3531761 = 2648821) B2648821
theorem B1565837 : Blo 463784 1565837 := bstep (se 3 (by rfl) ⟨293594, by rfl⟩ : syracuseStep 1565837 = 587189) B587189
theorem B2647181 : Blo 463784 2647181 := bstep (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) B992693
theorem B1565891 : Blo 463784 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B746929 : Blo 463784 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B1566161 : Blo 463784 1566161 := bstep (se 2 (by rfl) ⟨587310, by rfl⟩ : syracuseStep 1566161 = 1174621) B1174621
theorem B1762829 : Blo 463784 1762829 := bstep (se 3 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 1762829 = 661061) B661061
theorem B3991139 : Blo 463784 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B20113109 : Blo 463784 20113109 := bstep (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) B471401
theorem B944003 : Blo 463784 944003 := bstep (se 1 (by rfl) ⟨708002, by rfl⟩ : syracuseStep 944003 = 1416005) B1416005
theorem B1566701 : Blo 463784 1566701 := bstep (se 3 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 1566701 = 587513) B587513
theorem B747539 : Blo 463784 747539 := bstep (se 1 (by rfl) ⟨560654, by rfl⟩ : syracuseStep 747539 = 1121309) B1121309
theorem B1566755 : Blo 463784 1566755 := bstep (se 1 (by rfl) ⟨1175066, by rfl⟩ : syracuseStep 1566755 = 2350133) B2350133
theorem B2517169 : Blo 463784 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B1567025 : Blo 463784 1567025 := bstep (se 2 (by rfl) ⟨587634, by rfl⟩ : syracuseStep 1567025 = 1175269) B1175269
theorem B1763633 : Blo 463784 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B1174115 : Blo 463784 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B1600163 : Blo 463784 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B1567565 : Blo 463784 1567565 := bstep (se 3 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 1567565 = 587837) B587837
theorem B1567619 : Blo 463784 1567619 := bstep (se 1 (by rfl) ⟨1175714, by rfl⟩ : syracuseStep 1567619 = 2351429) B2351429
theorem B1764301 : Blo 463784 1764301 := bstep (se 3 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 1764301 = 661613) B661613
theorem B748531 : Blo 463784 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B1567889 : Blo 463784 1567889 := bstep (se 2 (by rfl) ⟨587958, by rfl⟩ : syracuseStep 1567889 = 1175917) B1175917
theorem B1993997 : Blo 463784 1993997 := bstep (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) B747749
theorem B1043729 : Blo 463784 1043729 := bstep (se 2 (by rfl) ⟨391398, by rfl⟩ : syracuseStep 1043729 = 782797) B782797
theorem B1043747 : Blo 463784 1043747 := bstep (se 1 (by rfl) ⟨782810, by rfl⟩ : syracuseStep 1043747 = 1565621) B1565621
theorem B1175057 : Blo 463784 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B1044017 : Blo 463784 1044017 := bstep (se 2 (by rfl) ⟨391506, by rfl⟩ : syracuseStep 1044017 = 783013) B783013
theorem B1044035 : Blo 463784 1044035 := bstep (se 1 (by rfl) ⟨783026, by rfl⟩ : syracuseStep 1044035 = 1566053) B1566053
theorem B1175107 : Blo 463784 1175107 := bstep (se 1 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 1175107 = 1762661) B1762661
theorem B1568429 : Blo 463784 1568429 := bstep (se 3 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 1568429 = 588161) B588161
theorem B1175249 : Blo 463784 1175249 := bstep (se 2 (by rfl) ⟨440718, by rfl⟩ : syracuseStep 1175249 = 881437) B881437
theorem B1568483 : Blo 463784 1568483 := bstep (se 1 (by rfl) ⟨1176362, by rfl⟩ : syracuseStep 1568483 = 2352725) B2352725
theorem B1765091 : Blo 463784 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B716579 : Blo 463784 716579 := bstep (se 1 (by rfl) ⟨537434, by rfl⟩ : syracuseStep 716579 = 1074869) B1074869
theorem B2354993 : Blo 463784 2354993 := bstep (se 2 (by rfl) ⟨883122, by rfl⟩ : syracuseStep 2354993 = 1766245) B1766245
theorem B1044305 : Blo 463784 1044305 := bstep (se 2 (by rfl) ⟨391614, by rfl⟩ : syracuseStep 1044305 = 783229) B783229
theorem B1044323 : Blo 463784 1044323 := bstep (se 1 (by rfl) ⟨783242, by rfl⟩ : syracuseStep 1044323 = 1566485) B1566485
theorem B880625 : Blo 463784 880625 := bstep (se 2 (by rfl) ⟨330234, by rfl⟩ : syracuseStep 880625 = 660469) B660469
theorem B1568753 : Blo 463784 1568753 := bstep (se 2 (by rfl) ⟨588282, by rfl⟩ : syracuseStep 1568753 = 1176565) B1176565
theorem B2650097 : Blo 463784 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B19132469 : Blo 463784 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B1044593 : Blo 463784 1044593 := bstep (se 2 (by rfl) ⟨391722, by rfl⟩ : syracuseStep 1044593 = 783445) B783445
theorem B1044611 : Blo 463784 1044611 := bstep (se 1 (by rfl) ⟨783458, by rfl⟩ : syracuseStep 1044611 = 1566917) B1566917
theorem B782689 : Blo 463784 782689 := bstep (se 2 (by rfl) ⟨293508, by rfl⟩ : syracuseStep 782689 = 587017) B587017
theorem B1765745 : Blo 463784 1765745 := bstep (se 2 (by rfl) ⟨662154, by rfl⟩ : syracuseStep 1765745 = 1324309) B1324309
theorem B782723 : Blo 463784 782723 := bstep (se 1 (by rfl) ⟨587042, by rfl⟩ : syracuseStep 782723 = 1174085) B1174085
theorem B881027 : Blo 463784 881027 := bstep (se 1 (by rfl) ⟨660770, by rfl⟩ : syracuseStep 881027 = 1321541) B1321541
theorem B1044881 : Blo 463784 1044881 := bstep (se 2 (by rfl) ⟨391830, by rfl⟩ : syracuseStep 1044881 = 783661) B783661
theorem B1044899 : Blo 463784 1044899 := bstep (se 1 (by rfl) ⟨783674, by rfl⟩ : syracuseStep 1044899 = 1567349) B1567349
theorem B782851 : Blo 463784 782851 := bstep (se 1 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 782851 = 1174277) B1174277
theorem B1569293 : Blo 463784 1569293 := bstep (se 3 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 1569293 = 588485) B588485
theorem B1569347 : Blo 463784 1569347 := bstep (se 1 (by rfl) ⟨1177010, by rfl⟩ : syracuseStep 1569347 = 2354021) B2354021
theorem B6386245 : Blo 463784 6386245 := bstep (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) B1197421
theorem B782993 : Blo 463784 782993 := bstep (se 2 (by rfl) ⟨293622, by rfl⟩ : syracuseStep 782993 = 587245) B587245
theorem B1045169 : Blo 463784 1045169 := bstep (se 2 (by rfl) ⟨391938, by rfl⟩ : syracuseStep 1045169 = 783877) B783877
theorem B1176241 : Blo 463784 1176241 := bstep (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) B882181
theorem B1045187 : Blo 463784 1045187 := bstep (se 1 (by rfl) ⟨783890, by rfl⟩ : syracuseStep 1045187 = 1567781) B1567781
theorem B783121 : Blo 463784 783121 := bstep (se 2 (by rfl) ⟨293670, by rfl⟩ : syracuseStep 783121 = 587341) B587341
theorem B783155 : Blo 463784 783155 := bstep (se 1 (by rfl) ⟨587366, by rfl⟩ : syracuseStep 783155 = 1174733) B1174733
theorem B1569617 : Blo 463784 1569617 := bstep (se 2 (by rfl) ⟨588606, by rfl⟩ : syracuseStep 1569617 = 1177213) B1177213
theorem B783283 : Blo 463784 783283 := bstep (se 1 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 783283 = 1174925) B1174925
theorem B1176515 : Blo 463784 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B1045457 : Blo 463784 1045457 := bstep (se 2 (by rfl) ⟨392046, by rfl⟩ : syracuseStep 1045457 = 784093) B784093
theorem B1045475 : Blo 463784 1045475 := bstep (se 1 (by rfl) ⟨784106, by rfl⟩ : syracuseStep 1045475 = 1568213) B1568213
theorem B783425 : Blo 463784 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B2290801 : Blo 463784 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B1176707 : Blo 463784 1176707 := bstep (se 1 (by rfl) ⟨882530, by rfl⟩ : syracuseStep 1176707 = 1765061) B1765061
theorem B1537165 : Blo 463784 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B783553 : Blo 463784 783553 := bstep (se 2 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 783553 = 587665) B587665
theorem B4027589 : Blo 463784 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B783587 : Blo 463784 783587 := bstep (se 1 (by rfl) ⟨587690, by rfl⟩ : syracuseStep 783587 = 1175381) B1175381
theorem B2356451 : Blo 463784 2356451 := bstep (se 1 (by rfl) ⟨1767338, by rfl⟩ : syracuseStep 2356451 = 3534677) B3534677
theorem B1045745 : Blo 463784 1045745 := bstep (se 2 (by rfl) ⟨392154, by rfl⟩ : syracuseStep 1045745 = 784309) B784309
theorem B881923 : Blo 463784 881923 := bstep (se 1 (by rfl) ⟨661442, by rfl⟩ : syracuseStep 881923 = 1322885) B1322885
theorem B1045763 : Blo 463784 1045763 := bstep (se 1 (by rfl) ⟨784322, by rfl⟩ : syracuseStep 1045763 = 1568645) B1568645
theorem B587027 : Blo 463784 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B783715 : Blo 463784 783715 := bstep (se 1 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 783715 = 1175573) B1175573
theorem B1570157 : Blo 463784 1570157 := bstep (se 3 (by rfl) ⟨294404, by rfl⟩ : syracuseStep 1570157 = 588809) B588809
theorem B882083 : Blo 463784 882083 := bstep (se 1 (by rfl) ⟨661562, by rfl⟩ : syracuseStep 882083 = 1323125) B1323125
theorem B1570211 : Blo 463784 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B2651555 : Blo 463784 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B783857 : Blo 463784 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B1046033 : Blo 463784 1046033 := bstep (se 2 (by rfl) ⟨392262, by rfl⟩ : syracuseStep 1046033 = 784525) B784525
theorem B1046051 : Blo 463784 1046051 := bstep (se 1 (by rfl) ⟨784538, by rfl⟩ : syracuseStep 1046051 = 1569077) B1569077
theorem B521779 : Blo 463784 521779 := bstep (se 1 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 521779 = 782669) B782669
theorem B783985 : Blo 463784 783985 := bstep (se 2 (by rfl) ⟨293994, by rfl⟩ : syracuseStep 783985 = 587989) B587989
theorem B784019 : Blo 463784 784019 := bstep (se 1 (by rfl) ⟨588014, by rfl⟩ : syracuseStep 784019 = 1176029) B1176029
theorem B1570481 : Blo 463784 1570481 := bstep (se 2 (by rfl) ⟨588930, by rfl⟩ : syracuseStep 1570481 = 1177861) B1177861
theorem B5732021 : Blo 463784 5732021 := bstep (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) B537377
theorem B521923 : Blo 463784 521923 := bstep (se 1 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 521923 = 782885) B782885
theorem B784147 : Blo 463784 784147 := bstep (se 1 (by rfl) ⟨588110, by rfl⟩ : syracuseStep 784147 = 1176221) B1176221
theorem B1767203 : Blo 463784 1767203 := bstep (se 1 (by rfl) ⟨1325402, by rfl⟩ : syracuseStep 1767203 = 2650805) B2650805
theorem B1046321 : Blo 463784 1046321 := bstep (se 2 (by rfl) ⟨392370, by rfl⟩ : syracuseStep 1046321 = 784741) B784741
theorem B1767217 : Blo 463784 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B1046339 : Blo 463784 1046339 := bstep (se 1 (by rfl) ⟨784754, by rfl⟩ : syracuseStep 1046339 = 1569509) B1569509
theorem B522067 : Blo 463784 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B784289 : Blo 463784 784289 := bstep (se 2 (by rfl) ⟨294108, by rfl⟩ : syracuseStep 784289 = 588217) B588217
theorem B587731 : Blo 463784 587731 := bstep (se 1 (by rfl) ⟨440798, by rfl⟩ : syracuseStep 587731 = 881597) B881597
theorem B522211 : Blo 463784 522211 := bstep (se 1 (by rfl) ⟨391658, by rfl⟩ : syracuseStep 522211 = 783317) B783317
theorem B2357261 : Blo 463784 2357261 := bstep (se 3 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 2357261 = 883973) B883973
theorem B784417 : Blo 463784 784417 := bstep (se 2 (by rfl) ⟨294156, by rfl⟩ : syracuseStep 784417 = 588313) B588313
theorem B1177649 : Blo 463784 1177649 := bstep (se 2 (by rfl) ⟨441618, by rfl⟩ : syracuseStep 1177649 = 883237) B883237
theorem B587827 : Blo 463784 587827 := bstep (se 1 (by rfl) ⟨440870, by rfl⟩ : syracuseStep 587827 = 881741) B881741
theorem B784451 : Blo 463784 784451 := bstep (se 1 (by rfl) ⟨588338, by rfl⟩ : syracuseStep 784451 = 1176677) B1176677
theorem B1046609 : Blo 463784 1046609 := bstep (se 2 (by rfl) ⟨392478, by rfl⟩ : syracuseStep 1046609 = 784957) B784957
theorem B1046627 : Blo 463784 1046627 := bstep (se 1 (by rfl) ⟨784970, by rfl⟩ : syracuseStep 1046627 = 1569941) B1569941
theorem B1177699 : Blo 463784 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B522355 : Blo 463784 522355 := bstep (se 1 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 522355 = 783533) B783533
theorem B784579 : Blo 463784 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B1571021 : Blo 463784 1571021 := bstep (se 3 (by rfl) ⟨294566, by rfl⟩ : syracuseStep 1571021 = 589133) B589133
theorem B1177841 : Blo 463784 1177841 := bstep (se 2 (by rfl) ⟨441690, by rfl⟩ : syracuseStep 1177841 = 883381) B883381
theorem B522499 : Blo 463784 522499 := bstep (se 1 (by rfl) ⟨391874, by rfl⟩ : syracuseStep 522499 = 783749) B783749
theorem B1571075 : Blo 463784 1571075 := bstep (se 1 (by rfl) ⟨1178306, by rfl⟩ : syracuseStep 1571075 = 2356613) B2356613
theorem B3012869 : Blo 463784 3012869 := bstep (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) B564913
theorem B784721 : Blo 463784 784721 := bstep (se 2 (by rfl) ⟨294270, by rfl⟩ : syracuseStep 784721 = 588541) B588541
theorem B1046897 : Blo 463784 1046897 := bstep (se 2 (by rfl) ⟨392586, by rfl⟩ : syracuseStep 1046897 = 785173) B785173
theorem B1046915 : Blo 463784 1046915 := bstep (se 1 (by rfl) ⟨785186, by rfl⟩ : syracuseStep 1046915 = 1570373) B1570373
theorem B522643 : Blo 463784 522643 := bstep (se 1 (by rfl) ⟨391982, by rfl⟩ : syracuseStep 522643 = 783965) B783965
theorem B6355381 : Blo 463784 6355381 := bstep (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) B595817
theorem B784849 : Blo 463784 784849 := bstep (se 2 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 784849 = 588637) B588637
theorem B883153 : Blo 463784 883153 := bstep (se 2 (by rfl) ⟨331182, by rfl⟩ : syracuseStep 883153 = 662365) B662365
theorem B784883 : Blo 463784 784883 := bstep (se 1 (by rfl) ⟨588662, by rfl⟩ : syracuseStep 784883 = 1177325) B1177325
theorem B1571345 : Blo 463784 1571345 := bstep (se 2 (by rfl) ⟨589254, by rfl⟩ : syracuseStep 1571345 = 1178509) B1178509
theorem B522787 : Blo 463784 522787 := bstep (se 1 (by rfl) ⟨392090, by rfl⟩ : syracuseStep 522787 = 784181) B784181
theorem B588323 : Blo 463784 588323 := bstep (se 1 (by rfl) ⟨441242, by rfl⟩ : syracuseStep 588323 = 882485) B882485
theorem B785011 : Blo 463784 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B1047185 : Blo 463784 1047185 := bstep (se 2 (by rfl) ⟨392694, by rfl⟩ : syracuseStep 1047185 = 785389) B785389
theorem B1047203 : Blo 463784 1047203 := bstep (se 1 (by rfl) ⟨785402, by rfl⟩ : syracuseStep 1047203 = 1570805) B1570805
theorem B522931 : Blo 463784 522931 := bstep (se 1 (by rfl) ⟨392198, by rfl⟩ : syracuseStep 522931 = 784397) B784397
theorem B785153 : Blo 463784 785153 := bstep (se 2 (by rfl) ⟨294432, by rfl⟩ : syracuseStep 785153 = 588865) B588865
theorem B1211171 : Blo 463784 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B523075 : Blo 463784 523075 := bstep (se 1 (by rfl) ⟨392306, by rfl⟩ : syracuseStep 523075 = 784613) B784613
theorem B785281 : Blo 463784 785281 := bstep (se 2 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 785281 = 588961) B588961
theorem B785315 : Blo 463784 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B1047473 : Blo 463784 1047473 := bstep (se 2 (by rfl) ⟨392802, by rfl⟩ : syracuseStep 1047473 = 785605) B785605
theorem B1047491 : Blo 463784 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B523219 : Blo 463784 523219 := bstep (se 1 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 523219 = 784829) B784829
theorem B785443 : Blo 463784 785443 := bstep (se 1 (by rfl) ⟨589082, by rfl⟩ : syracuseStep 785443 = 1178165) B1178165
theorem B1571885 : Blo 463784 1571885 := bstep (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) B589457
theorem B523363 : Blo 463784 523363 := bstep (se 1 (by rfl) ⟨392522, by rfl⟩ : syracuseStep 523363 = 785045) B785045
theorem B1571939 : Blo 463784 1571939 := bstep (se 1 (by rfl) ⟨1178954, by rfl⟩ : syracuseStep 1571939 = 2357909) B2357909
theorem B785585 : Blo 463784 785585 := bstep (se 2 (by rfl) ⟨294594, by rfl⟩ : syracuseStep 785585 = 589189) B589189
theorem B1047761 : Blo 463784 1047761 := bstep (se 2 (by rfl) ⟨392910, by rfl⟩ : syracuseStep 1047761 = 785821) B785821
theorem B1178833 : Blo 463784 1178833 := bstep (se 2 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 1178833 = 884125) B884125
theorem B589027 : Blo 463784 589027 := bstep (se 1 (by rfl) ⟨441770, by rfl⟩ : syracuseStep 589027 = 883541) B883541
theorem B1047779 : Blo 463784 1047779 := bstep (se 1 (by rfl) ⟨785834, by rfl⟩ : syracuseStep 1047779 = 1571669) B1571669
theorem B1768675 : Blo 463784 1768675 := bstep (se 1 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 1768675 = 2653013) B2653013
theorem B523507 : Blo 463784 523507 := bstep (se 1 (by rfl) ⟨392630, by rfl⟩ : syracuseStep 523507 = 785261) B785261
theorem B785713 : Blo 463784 785713 := bstep (se 2 (by rfl) ⟨294642, by rfl⟩ : syracuseStep 785713 = 589285) B589285
theorem B589123 : Blo 463784 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B785747 : Blo 463784 785747 := bstep (se 1 (by rfl) ⟨589310, by rfl⟩ : syracuseStep 785747 = 1178621) B1178621
theorem B1572209 : Blo 463784 1572209 := bstep (se 2 (by rfl) ⟨589578, by rfl⟩ : syracuseStep 1572209 = 1179157) B1179157
theorem B523651 : Blo 463784 523651 := bstep (se 1 (by rfl) ⟨392738, by rfl⟩ : syracuseStep 523651 = 785477) B785477
theorem B785875 : Blo 463784 785875 := bstep (se 1 (by rfl) ⟨589406, by rfl⟩ : syracuseStep 785875 = 1178813) B1178813
theorem B1179107 : Blo 463784 1179107 := bstep (se 1 (by rfl) ⟨884330, by rfl⟩ : syracuseStep 1179107 = 1768661) B1768661
theorem B884209 : Blo 463784 884209 := bstep (se 2 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 884209 = 663157) B663157
theorem B1048049 : Blo 463784 1048049 := bstep (se 2 (by rfl) ⟨393018, by rfl⟩ : syracuseStep 1048049 = 786037) B786037
theorem B1048067 : Blo 463784 1048067 := bstep (se 1 (by rfl) ⟨786050, by rfl⟩ : syracuseStep 1048067 = 1572101) B1572101
theorem B523795 : Blo 463784 523795 := bstep (se 1 (by rfl) ⟨392846, by rfl⟩ : syracuseStep 523795 = 785693) B785693
theorem B786017 : Blo 463784 786017 := bstep (se 2 (by rfl) ⟨294756, by rfl⟩ : syracuseStep 786017 = 589513) B589513
theorem B4488803 : Blo 463784 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B523939 : Blo 463784 523939 := bstep (se 1 (by rfl) ⟨392954, by rfl⟩ : syracuseStep 523939 = 785909) B785909
theorem B1179299 : Blo 463784 1179299 := bstep (se 1 (by rfl) ⟨884474, by rfl⟩ : syracuseStep 1179299 = 1768949) B1768949
theorem B786145 : Blo 463784 786145 := bstep (se 2 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 786145 = 589609) B589609
theorem B786179 : Blo 463784 786179 := bstep (se 1 (by rfl) ⟨589634, by rfl⟩ : syracuseStep 786179 = 1179269) B1179269
theorem B1048337 : Blo 463784 1048337 := bstep (se 2 (by rfl) ⟨393126, by rfl⟩ : syracuseStep 1048337 = 786253) B786253
theorem B1048355 : Blo 463784 1048355 := bstep (se 1 (by rfl) ⟨786266, by rfl⟩ : syracuseStep 1048355 = 1572533) B1572533
theorem B524083 : Blo 463784 524083 := bstep (se 1 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 524083 = 786125) B786125
theorem B589619 : Blo 463784 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B786307 : Blo 463784 786307 := bstep (se 1 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 786307 = 1179461) B1179461
theorem B884611 : Blo 463784 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B1572749 : Blo 463784 1572749 := bstep (se 3 (by rfl) ⟨294890, by rfl⟩ : syracuseStep 1572749 = 589781) B589781
theorem B1343405 : Blo 463784 1343405 := bstep (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) B503777
theorem B884657 : Blo 463784 884657 := bstep (se 2 (by rfl) ⟨331746, by rfl⟩ : syracuseStep 884657 = 663493) B663493
theorem B524227 : Blo 463784 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B1572803 : Blo 463784 1572803 := bstep (se 1 (by rfl) ⟨1179602, by rfl⟩ : syracuseStep 1572803 = 2359205) B2359205
theorem B2981873 : Blo 463784 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B524299 : Blo 463784 524299 := bstep (se 1 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 524299 = 786449) B786449
theorem B524407 : Blo 463784 524407 := bstep (se 1 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 524407 = 786611) B786611
theorem B1048715 : Blo 463784 1048715 := bstep (se 1 (by rfl) ⟨786536, by rfl⟩ : syracuseStep 1048715 = 1573073) B1573073
theorem B884915 : Blo 463784 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B1048769 : Blo 463784 1048769 := bstep (se 2 (by rfl) ⟨393288, by rfl⟩ : syracuseStep 1048769 = 786577) B786577
theorem B7930061 : Blo 463784 7930061 := bstep (se 3 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 7930061 = 2973773) B2973773
theorem B524587 : Blo 463784 524587 := bstep (se 1 (by rfl) ⟨393440, by rfl⟩ : syracuseStep 524587 = 786881) B786881
theorem B786827 : Blo 463784 786827 := bstep (se 1 (by rfl) ⟨590120, by rfl⟩ : syracuseStep 786827 = 1180241) B1180241
theorem B885143 : Blo 463784 885143 := bstep (se 1 (by rfl) ⟨663857, by rfl⟩ : syracuseStep 885143 = 1327715) B1327715
theorem B524695 : Blo 463784 524695 := bstep (se 1 (by rfl) ⟨393521, by rfl⟩ : syracuseStep 524695 = 787043) B787043
theorem B1048985 : Blo 463784 1048985 := bstep (se 2 (by rfl) ⟨393369, by rfl⟩ : syracuseStep 1048985 = 786739) B786739
theorem B1769921 : Blo 463784 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B1049075 : Blo 463784 1049075 := bstep (se 1 (by rfl) ⟨786806, by rfl⟩ : syracuseStep 1049075 = 1573613) B1573613
theorem B786955 : Blo 463784 786955 := bstep (se 1 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 786955 = 1180433) B1180433
theorem B1049111 : Blo 463784 1049111 := bstep (se 1 (by rfl) ⟨786833, by rfl⟩ : syracuseStep 1049111 = 1573667) B1573667
theorem B2359853 : Blo 463784 2359853 := bstep (se 3 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 2359853 = 884945) B884945
theorem B1573451 : Blo 463784 1573451 := bstep (se 1 (by rfl) ⟨1180088, by rfl⟩ : syracuseStep 1573451 = 2360177) B2360177
theorem B524875 : Blo 463784 524875 := bstep (se 1 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 524875 = 787313) B787313
theorem B885401 : Blo 463784 885401 := bstep (se 2 (by rfl) ⟨332025, by rfl⟩ : syracuseStep 885401 = 664051) B664051
theorem B787097 : Blo 463784 787097 := bstep (se 2 (by rfl) ⟨295161, by rfl⟩ : syracuseStep 787097 = 590323) B590323
theorem B524983 : Blo 463784 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B1049291 : Blo 463784 1049291 := bstep (se 1 (by rfl) ⟨786968, by rfl⟩ : syracuseStep 1049291 = 1573937) B1573937
theorem B1049345 : Blo 463784 1049345 := bstep (se 2 (by rfl) ⟨393504, by rfl⟩ : syracuseStep 1049345 = 787009) B787009
theorem B787225 : Blo 463784 787225 := bstep (se 2 (by rfl) ⟨295209, by rfl⟩ : syracuseStep 787225 = 590419) B590419
theorem B1672001 : Blo 463784 1672001 := bstep (se 2 (by rfl) ⟨627000, by rfl⟩ : syracuseStep 1672001 = 1254001) B1254001
theorem B1114955 : Blo 463784 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1573721 : Blo 463784 1573721 := bstep (se 2 (by rfl) ⟨590145, by rfl⟩ : syracuseStep 1573721 = 1180291) B1180291
theorem B525163 : Blo 463784 525163 := bstep (se 1 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 525163 = 787745) B787745
theorem B590743 : Blo 463784 590743 := bstep (se 1 (by rfl) ⟨443057, by rfl⟩ : syracuseStep 590743 = 886115) B886115
theorem B1180595 : Blo 463784 1180595 := bstep (se 1 (by rfl) ⟨885446, by rfl⟩ : syracuseStep 1180595 = 1770893) B1770893
theorem B525271 : Blo 463784 525271 := bstep (se 1 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 525271 = 787907) B787907
theorem B1049561 : Blo 463784 1049561 := bstep (se 2 (by rfl) ⟨393585, by rfl⟩ : syracuseStep 1049561 = 787171) B787171
theorem B1049651 : Blo 463784 1049651 := bstep (se 1 (by rfl) ⟨787238, by rfl⟩ : syracuseStep 1049651 = 1574477) B1574477
theorem B885811 : Blo 463784 885811 := bstep (se 1 (by rfl) ⟨664358, by rfl⟩ : syracuseStep 885811 = 1328717) B1328717
theorem B2982977 : Blo 463784 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B1049687 : Blo 463784 1049687 := bstep (se 1 (by rfl) ⟨787265, by rfl⟩ : syracuseStep 1049687 = 1574531) B1574531
theorem B525451 : Blo 463784 525451 := bstep (se 1 (by rfl) ⟨394088, by rfl⟩ : syracuseStep 525451 = 788177) B788177
theorem B1180889 : Blo 463784 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B525559 : Blo 463784 525559 := bstep (se 1 (by rfl) ⟨394169, by rfl⟩ : syracuseStep 525559 = 788339) B788339
theorem B1049867 : Blo 463784 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B2131217 : Blo 463784 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B1049921 : Blo 463784 1049921 := bstep (se 2 (by rfl) ⟨393720, by rfl⟩ : syracuseStep 1049921 = 787441) B787441
theorem B787799 : Blo 463784 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B525739 : Blo 463784 525739 := bstep (se 1 (by rfl) ⟨394304, by rfl⟩ : syracuseStep 525739 = 788609) B788609
theorem B2131379 : Blo 463784 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B787927 : Blo 463784 787927 := bstep (se 1 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 787927 = 1181891) B1181891
theorem B1574423 : Blo 463784 1574423 := bstep (se 1 (by rfl) ⟨1180817, by rfl⟩ : syracuseStep 1574423 = 2361635) B2361635
theorem B525847 : Blo 463784 525847 := bstep (se 1 (by rfl) ⟨394385, by rfl⟩ : syracuseStep 525847 = 788771) B788771
theorem B1050137 : Blo 463784 1050137 := bstep (se 2 (by rfl) ⟨393801, by rfl⟩ : syracuseStep 1050137 = 787603) B787603
theorem B886297 : Blo 463784 886297 := bstep (se 2 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 886297 = 664723) B664723
theorem B1050227 : Blo 463784 1050227 := bstep (se 1 (by rfl) ⟨787670, by rfl⟩ : syracuseStep 1050227 = 1575341) B1575341
theorem B1050263 : Blo 463784 1050263 := bstep (se 1 (by rfl) ⟨787697, by rfl⟩ : syracuseStep 1050263 = 1575395) B1575395
theorem B591563 : Blo 463784 591563 := bstep (se 1 (by rfl) ⟨443672, by rfl⟩ : syracuseStep 591563 = 887345) B887345
theorem B526027 : Blo 463784 526027 := bstep (se 1 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 526027 = 789041) B789041
theorem B526135 : Blo 463784 526135 := bstep (se 1 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 526135 = 789203) B789203
theorem B1836875 : Blo 463784 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B1050443 : Blo 463784 1050443 := bstep (se 1 (by rfl) ⟨787832, by rfl⟩ : syracuseStep 1050443 = 1575665) B1575665
theorem B1050497 : Blo 463784 1050497 := bstep (se 2 (by rfl) ⟨393936, by rfl⟩ : syracuseStep 1050497 = 787873) B787873
theorem B1771409 : Blo 463784 1771409 := bstep (se 2 (by rfl) ⟨664278, by rfl⟩ : syracuseStep 1771409 = 1328557) B1328557
theorem B1574963 : Blo 463784 1574963 := bstep (se 1 (by rfl) ⟨1181222, by rfl⟩ : syracuseStep 1574963 = 2362445) B2362445
theorem B886859 : Blo 463784 886859 := bstep (se 1 (by rfl) ⟨665144, by rfl⟩ : syracuseStep 886859 = 1330289) B1330289
theorem B788555 : Blo 463784 788555 := bstep (se 1 (by rfl) ⟨591416, by rfl⟩ : syracuseStep 788555 = 1182833) B1182833
theorem B1050713 : Blo 463784 1050713 := bstep (se 2 (by rfl) ⟨394017, by rfl⟩ : syracuseStep 1050713 = 788035) B788035
theorem B1050803 : Blo 463784 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B788683 : Blo 463784 788683 := bstep (se 1 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 788683 = 1183025) B1183025
theorem B1050839 : Blo 463784 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B887041 : Blo 463784 887041 := bstep (se 2 (by rfl) ⟨332640, by rfl⟩ : syracuseStep 887041 = 665281) B665281
theorem B1575233 : Blo 463784 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B1771865 : Blo 463784 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B788825 : Blo 463784 788825 := bstep (se 2 (by rfl) ⟨295809, by rfl⟩ : syracuseStep 788825 = 591619) B591619
theorem B1051019 : Blo 463784 1051019 := bstep (se 1 (by rfl) ⟨788264, by rfl⟩ : syracuseStep 1051019 = 1576529) B1576529
theorem B2230679 : Blo 463784 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B1051073 : Blo 463784 1051073 := bstep (se 2 (by rfl) ⟨394152, by rfl⟩ : syracuseStep 1051073 = 788305) B788305
theorem B788953 : Blo 463784 788953 := bstep (se 2 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 788953 = 591715) B591715
theorem B1772077 : Blo 463784 1772077 := bstep (se 3 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 1772077 = 664529) B664529
theorem B10783363 : Blo 463784 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B1051289 : Blo 463784 1051289 := bstep (se 2 (by rfl) ⟨394233, by rfl⟩ : syracuseStep 1051289 = 788467) B788467
theorem B1051379 : Blo 463784 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B1051415 : Blo 463784 1051415 := bstep (se 1 (by rfl) ⟨788561, by rfl⟩ : syracuseStep 1051415 = 1577123) B1577123
theorem B2657069 : Blo 463784 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B11209537 : Blo 463784 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B1117003 : Blo 463784 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B1182539 : Blo 463784 1182539 := bstep (se 1 (by rfl) ⟨886904, by rfl⟩ : syracuseStep 1182539 = 1773809) B1773809
theorem B1772381 : Blo 463784 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B1575773 : Blo 463784 1575773 := bstep (se 3 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 1575773 = 590915) B590915
theorem B1117079 : Blo 463784 1117079 := bstep (se 1 (by rfl) ⟨837809, by rfl⟩ : syracuseStep 1117079 = 1675619) B1675619
theorem B1051595 : Blo 463784 1051595 := bstep (se 1 (by rfl) ⟨788696, by rfl⟩ : syracuseStep 1051595 = 1577393) B1577393
theorem B887755 : Blo 463784 887755 := bstep (se 1 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 887755 = 1331633) B1331633
theorem B1051649 : Blo 463784 1051649 := bstep (se 2 (by rfl) ⟨394368, by rfl⟩ : syracuseStep 1051649 = 788737) B788737
theorem B887831 : Blo 463784 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B4492493 : Blo 463784 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B1051865 : Blo 463784 1051865 := bstep (se 2 (by rfl) ⟨394449, by rfl⟩ : syracuseStep 1051865 = 788899) B788899
theorem B1051955 : Blo 463784 1051955 := bstep (se 1 (by rfl) ⟨788966, by rfl⟩ : syracuseStep 1051955 = 1577933) B1577933
theorem B1051991 : Blo 463784 1051991 := bstep (se 1 (by rfl) ⟨788993, by rfl⟩ : syracuseStep 1051991 = 1577987) B1577987
theorem B1052171 : Blo 463784 1052171 := bstep (se 1 (by rfl) ⟨789128, by rfl⟩ : syracuseStep 1052171 = 1578257) B1578257
theorem B1052225 : Blo 463784 1052225 := bstep (se 2 (by rfl) ⟨394584, by rfl⟩ : syracuseStep 1052225 = 789169) B789169
theorem B1183511 : Blo 463784 1183511 := bstep (se 1 (by rfl) ⟨887633, by rfl⟩ : syracuseStep 1183511 = 1775267) B1775267
theorem B1052441 : Blo 463784 1052441 := bstep (se 2 (by rfl) ⟨394665, by rfl⟩ : syracuseStep 1052441 = 789331) B789331
theorem B10030949 : Blo 463784 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B1707907 : Blo 463784 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B1675201 : Blo 463784 1675201 := bstep (se 2 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 1675201 = 1256401) B1256401
theorem B1576907 : Blo 463784 1576907 := bstep (se 1 (by rfl) ⟨1182680, by rfl⟩ : syracuseStep 1576907 = 2365361) B2365361
theorem B495595 : Blo 463784 495595 := bstep (se 1 (by rfl) ⟨371696, by rfl⟩ : syracuseStep 495595 = 743393) B743393
theorem B1577177 : Blo 463784 1577177 := bstep (se 2 (by rfl) ⟨591441, by rfl⟩ : syracuseStep 1577177 = 1182883) B1182883
theorem B7180589 : Blo 463784 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B2363741 : Blo 463784 2363741 := bstep (se 3 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 2363741 = 886403) B886403
theorem B3019139 : Blo 463784 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B1577879 : Blo 463784 1577879 := bstep (se 1 (by rfl) ⟨1183409, by rfl⟩ : syracuseStep 1577879 = 2366819) B2366819
theorem B463787 : Blo 463784 463787 := bstep (se 1 (by rfl) ⟨347840, by rfl⟩ : syracuseStep 463787 = 695681) B695681
theorem B463799 : Blo 463784 463799 := bstep (se 1 (by rfl) ⟨347849, by rfl⟩ : syracuseStep 463799 = 695699) B695699
theorem B463819 : Blo 463784 463819 := bstep (se 1 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 463819 = 695729) B695729
theorem B463831 : Blo 463784 463831 := bstep (se 1 (by rfl) ⟨347873, by rfl⟩ : syracuseStep 463831 = 695747) B695747
theorem B463851 : Blo 463784 463851 := bstep (se 1 (by rfl) ⟨347888, by rfl⟩ : syracuseStep 463851 = 695777) B695777
theorem B463863 : Blo 463784 463863 := bstep (se 1 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 463863 = 695795) B695795
theorem B463883 : Blo 463784 463883 := bstep (se 1 (by rfl) ⟨347912, by rfl⟩ : syracuseStep 463883 = 695825) B695825
theorem B463895 : Blo 463784 463895 := bstep (se 1 (by rfl) ⟨347921, by rfl⟩ : syracuseStep 463895 = 695843) B695843
theorem B463915 : Blo 463784 463915 := bstep (se 1 (by rfl) ⟨347936, by rfl⟩ : syracuseStep 463915 = 695873) B695873
theorem B463927 : Blo 463784 463927 := bstep (se 1 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 463927 = 695891) B695891
theorem B463947 : Blo 463784 463947 := bstep (se 1 (by rfl) ⟨347960, by rfl⟩ : syracuseStep 463947 = 695921) B695921
theorem B463959 : Blo 463784 463959 := bstep (se 1 (by rfl) ⟨347969, by rfl⟩ : syracuseStep 463959 = 695939) B695939
theorem B922711 : Blo 463784 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B1676381 : Blo 463784 1676381 := bstep (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) B628643
theorem B463979 : Blo 463784 463979 := bstep (se 1 (by rfl) ⟨347984, by rfl⟩ : syracuseStep 463979 = 695969) B695969
theorem B463991 : Blo 463784 463991 := bstep (se 1 (by rfl) ⟨347993, by rfl⟩ : syracuseStep 463991 = 695987) B695987
theorem B464011 : Blo 463784 464011 := bstep (se 1 (by rfl) ⟨348008, by rfl⟩ : syracuseStep 464011 = 696017) B696017
theorem B464023 : Blo 463784 464023 := bstep (se 1 (by rfl) ⟨348017, by rfl⟩ : syracuseStep 464023 = 696035) B696035
theorem B464043 : Blo 463784 464043 := bstep (se 1 (by rfl) ⟨348032, by rfl⟩ : syracuseStep 464043 = 696065) B696065
theorem B464055 : Blo 463784 464055 := bstep (se 1 (by rfl) ⟨348041, by rfl⟩ : syracuseStep 464055 = 696083) B696083
theorem B464075 : Blo 463784 464075 := bstep (se 1 (by rfl) ⟨348056, by rfl⟩ : syracuseStep 464075 = 696113) B696113
theorem B464087 : Blo 463784 464087 := bstep (se 1 (by rfl) ⟨348065, by rfl⟩ : syracuseStep 464087 = 696131) B696131
theorem B464107 : Blo 463784 464107 := bstep (se 1 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 464107 = 696161) B696161
theorem B464119 : Blo 463784 464119 := bstep (se 1 (by rfl) ⟨348089, by rfl⟩ : syracuseStep 464119 = 696179) B696179
theorem B464139 : Blo 463784 464139 := bstep (se 1 (by rfl) ⟨348104, by rfl⟩ : syracuseStep 464139 = 696209) B696209
theorem B464151 : Blo 463784 464151 := bstep (se 1 (by rfl) ⟨348113, by rfl⟩ : syracuseStep 464151 = 696227) B696227
theorem B464171 : Blo 463784 464171 := bstep (se 1 (by rfl) ⟨348128, by rfl⟩ : syracuseStep 464171 = 696257) B696257
theorem B1119539 : Blo 463784 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B464183 : Blo 463784 464183 := bstep (se 1 (by rfl) ⟨348137, by rfl⟩ : syracuseStep 464183 = 696275) B696275
theorem B464203 : Blo 463784 464203 := bstep (se 1 (by rfl) ⟨348152, by rfl⟩ : syracuseStep 464203 = 696305) B696305
theorem B464215 : Blo 463784 464215 := bstep (se 1 (by rfl) ⟨348161, by rfl⟩ : syracuseStep 464215 = 696323) B696323
theorem B464235 : Blo 463784 464235 := bstep (se 1 (by rfl) ⟨348176, by rfl⟩ : syracuseStep 464235 = 696353) B696353
theorem B464247 : Blo 463784 464247 := bstep (se 1 (by rfl) ⟨348185, by rfl⟩ : syracuseStep 464247 = 696371) B696371
theorem B1774979 : Blo 463784 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B464267 : Blo 463784 464267 := bstep (se 1 (by rfl) ⟨348200, by rfl⟩ : syracuseStep 464267 = 696401) B696401
theorem B1774993 : Blo 463784 1774993 := bstep (se 2 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 1774993 = 1331245) B1331245
theorem B464279 : Blo 463784 464279 := bstep (se 1 (by rfl) ⟨348209, by rfl⟩ : syracuseStep 464279 = 696419) B696419
theorem B464299 : Blo 463784 464299 := bstep (se 1 (by rfl) ⟨348224, by rfl⟩ : syracuseStep 464299 = 696449) B696449
theorem B1578419 : Blo 463784 1578419 := bstep (se 1 (by rfl) ⟨1183814, by rfl⟩ : syracuseStep 1578419 = 2367629) B2367629
theorem B464311 : Blo 463784 464311 := bstep (se 1 (by rfl) ⟨348233, by rfl⟩ : syracuseStep 464311 = 696467) B696467
theorem B464331 : Blo 463784 464331 := bstep (se 1 (by rfl) ⟨348248, by rfl⟩ : syracuseStep 464331 = 696497) B696497
theorem B464343 : Blo 463784 464343 := bstep (se 1 (by rfl) ⟨348257, by rfl⟩ : syracuseStep 464343 = 696515) B696515
theorem B464363 : Blo 463784 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B464375 : Blo 463784 464375 := bstep (se 1 (by rfl) ⟨348281, by rfl⟩ : syracuseStep 464375 = 696563) B696563
theorem B464395 : Blo 463784 464395 := bstep (se 1 (by rfl) ⟨348296, by rfl⟩ : syracuseStep 464395 = 696593) B696593
theorem B464407 : Blo 463784 464407 := bstep (se 1 (by rfl) ⟨348305, by rfl⟩ : syracuseStep 464407 = 696611) B696611
theorem B464427 : Blo 463784 464427 := bstep (se 1 (by rfl) ⟨348320, by rfl⟩ : syracuseStep 464427 = 696641) B696641
theorem B464439 : Blo 463784 464439 := bstep (se 1 (by rfl) ⟨348329, by rfl⟩ : syracuseStep 464439 = 696659) B696659
theorem B464459 : Blo 463784 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B464471 : Blo 463784 464471 := bstep (se 1 (by rfl) ⟨348353, by rfl⟩ : syracuseStep 464471 = 696707) B696707
theorem B464491 : Blo 463784 464491 := bstep (se 1 (by rfl) ⟨348368, by rfl⟩ : syracuseStep 464491 = 696737) B696737
theorem B464503 : Blo 463784 464503 := bstep (se 1 (by rfl) ⟨348377, by rfl⟩ : syracuseStep 464503 = 696755) B696755
theorem B464523 : Blo 463784 464523 := bstep (se 1 (by rfl) ⟨348392, by rfl⟩ : syracuseStep 464523 = 696785) B696785
theorem B464535 : Blo 463784 464535 := bstep (se 1 (by rfl) ⟨348401, by rfl⟩ : syracuseStep 464535 = 696803) B696803
theorem B464555 : Blo 463784 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B464567 : Blo 463784 464567 := bstep (se 1 (by rfl) ⟨348425, by rfl⟩ : syracuseStep 464567 = 696851) B696851
theorem B1775297 : Blo 463784 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B1578689 : Blo 463784 1578689 := bstep (se 2 (by rfl) ⟨592008, by rfl⟩ : syracuseStep 1578689 = 1184017) B1184017
theorem B464587 : Blo 463784 464587 := bstep (se 1 (by rfl) ⟨348440, by rfl⟩ : syracuseStep 464587 = 696881) B696881
theorem B464599 : Blo 463784 464599 := bstep (se 1 (by rfl) ⟨348449, by rfl⟩ : syracuseStep 464599 = 696899) B696899
theorem B464619 : Blo 463784 464619 := bstep (se 1 (by rfl) ⟨348464, by rfl⟩ : syracuseStep 464619 = 696929) B696929
theorem B464631 : Blo 463784 464631 := bstep (se 1 (by rfl) ⟨348473, by rfl⟩ : syracuseStep 464631 = 696947) B696947
theorem B464651 : Blo 463784 464651 := bstep (se 1 (by rfl) ⟨348488, by rfl⟩ : syracuseStep 464651 = 696977) B696977
theorem B464663 : Blo 463784 464663 := bstep (se 1 (by rfl) ⟨348497, by rfl⟩ : syracuseStep 464663 = 696995) B696995
theorem B464683 : Blo 463784 464683 := bstep (se 1 (by rfl) ⟨348512, by rfl⟩ : syracuseStep 464683 = 697025) B697025
theorem B464695 : Blo 463784 464695 := bstep (se 1 (by rfl) ⟨348521, by rfl⟩ : syracuseStep 464695 = 697043) B697043
theorem B464715 : Blo 463784 464715 := bstep (se 1 (by rfl) ⟨348536, by rfl⟩ : syracuseStep 464715 = 697073) B697073
theorem B464727 : Blo 463784 464727 := bstep (se 1 (by rfl) ⟨348545, by rfl⟩ : syracuseStep 464727 = 697091) B697091
theorem B464747 : Blo 463784 464747 := bstep (se 1 (by rfl) ⟨348560, by rfl⟩ : syracuseStep 464747 = 697121) B697121
theorem B464759 : Blo 463784 464759 := bstep (se 1 (by rfl) ⟨348569, by rfl⟩ : syracuseStep 464759 = 697139) B697139
theorem B464779 : Blo 463784 464779 := bstep (se 1 (by rfl) ⟨348584, by rfl⟩ : syracuseStep 464779 = 697169) B697169
theorem B464791 : Blo 463784 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B464811 : Blo 463784 464811 := bstep (se 1 (by rfl) ⟨348608, by rfl⟩ : syracuseStep 464811 = 697217) B697217
theorem B464823 : Blo 463784 464823 := bstep (se 1 (by rfl) ⟨348617, by rfl⟩ : syracuseStep 464823 = 697235) B697235
theorem B464843 : Blo 463784 464843 := bstep (se 1 (by rfl) ⟨348632, by rfl⟩ : syracuseStep 464843 = 697265) B697265
theorem B497611 : Blo 463784 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B464855 : Blo 463784 464855 := bstep (se 1 (by rfl) ⟨348641, by rfl⟩ : syracuseStep 464855 = 697283) B697283
theorem B464875 : Blo 463784 464875 := bstep (se 1 (by rfl) ⟨348656, by rfl⟩ : syracuseStep 464875 = 697313) B697313
theorem B464887 : Blo 463784 464887 := bstep (se 1 (by rfl) ⟨348665, by rfl⟩ : syracuseStep 464887 = 697331) B697331
theorem B464907 : Blo 463784 464907 := bstep (se 1 (by rfl) ⟨348680, by rfl⟩ : syracuseStep 464907 = 697361) B697361
theorem B8034317 : Blo 463784 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B464919 : Blo 463784 464919 := bstep (se 1 (by rfl) ⟨348689, by rfl⟩ : syracuseStep 464919 = 697379) B697379
theorem B11606051 : Blo 463784 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B464939 : Blo 463784 464939 := bstep (se 1 (by rfl) ⟨348704, by rfl⟩ : syracuseStep 464939 = 697409) B697409
theorem B464951 : Blo 463784 464951 := bstep (se 1 (by rfl) ⟨348713, by rfl⟩ : syracuseStep 464951 = 697427) B697427
theorem B8198213 : Blo 463784 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B464971 : Blo 463784 464971 := bstep (se 1 (by rfl) ⟨348728, by rfl⟩ : syracuseStep 464971 = 697457) B697457
theorem B464983 : Blo 463784 464983 := bstep (se 1 (by rfl) ⟨348737, by rfl⟩ : syracuseStep 464983 = 697475) B697475
theorem B465003 : Blo 463784 465003 := bstep (se 1 (by rfl) ⟨348752, by rfl⟩ : syracuseStep 465003 = 697505) B697505
theorem B465015 : Blo 463784 465015 := bstep (se 1 (by rfl) ⟨348761, by rfl⟩ : syracuseStep 465015 = 697523) B697523
theorem B465035 : Blo 463784 465035 := bstep (se 1 (by rfl) ⟨348776, by rfl⟩ : syracuseStep 465035 = 697553) B697553
theorem B465047 : Blo 463784 465047 := bstep (se 1 (by rfl) ⟨348785, by rfl⟩ : syracuseStep 465047 = 697571) B697571
theorem B465067 : Blo 463784 465067 := bstep (se 1 (by rfl) ⟨348800, by rfl⟩ : syracuseStep 465067 = 697601) B697601
theorem B465079 : Blo 463784 465079 := bstep (se 1 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 465079 = 697619) B697619
theorem B465099 : Blo 463784 465099 := bstep (se 1 (by rfl) ⟨348824, by rfl⟩ : syracuseStep 465099 = 697649) B697649
theorem B465111 : Blo 463784 465111 := bstep (se 1 (by rfl) ⟨348833, by rfl⟩ : syracuseStep 465111 = 697667) B697667
theorem B465131 : Blo 463784 465131 := bstep (se 1 (by rfl) ⟨348848, by rfl⟩ : syracuseStep 465131 = 697697) B697697
theorem B465143 : Blo 463784 465143 := bstep (se 1 (by rfl) ⟨348857, by rfl⟩ : syracuseStep 465143 = 697715) B697715
theorem B465163 : Blo 463784 465163 := bstep (se 1 (by rfl) ⟨348872, by rfl⟩ : syracuseStep 465163 = 697745) B697745
theorem B465175 : Blo 463784 465175 := bstep (se 1 (by rfl) ⟨348881, by rfl⟩ : syracuseStep 465175 = 697763) B697763
theorem B465195 : Blo 463784 465195 := bstep (se 1 (by rfl) ⟨348896, by rfl⟩ : syracuseStep 465195 = 697793) B697793
theorem B465207 : Blo 463784 465207 := bstep (se 1 (by rfl) ⟨348905, by rfl⟩ : syracuseStep 465207 = 697811) B697811
theorem B465227 : Blo 463784 465227 := bstep (se 1 (by rfl) ⟨348920, by rfl⟩ : syracuseStep 465227 = 697841) B697841
theorem B465239 : Blo 463784 465239 := bstep (se 1 (by rfl) ⟨348929, by rfl⟩ : syracuseStep 465239 = 697859) B697859
theorem B1775965 : Blo 463784 1775965 := bstep (se 3 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 1775965 = 665987) B665987
theorem B465259 : Blo 463784 465259 := bstep (se 1 (by rfl) ⟨348944, by rfl⟩ : syracuseStep 465259 = 697889) B697889
theorem B465271 : Blo 463784 465271 := bstep (se 1 (by rfl) ⟨348953, by rfl⟩ : syracuseStep 465271 = 697907) B697907
theorem B3021187 : Blo 463784 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B465291 : Blo 463784 465291 := bstep (se 1 (by rfl) ⟨348968, by rfl⟩ : syracuseStep 465291 = 697937) B697937
theorem B465303 : Blo 463784 465303 := bstep (se 1 (by rfl) ⟨348977, by rfl⟩ : syracuseStep 465303 = 697955) B697955
theorem B1120663 : Blo 463784 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B2660759 : Blo 463784 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B2365847 : Blo 463784 2365847 := bstep (se 1 (by rfl) ⟨1774385, by rfl⟩ : syracuseStep 2365847 = 3548771) B3548771
theorem B465323 : Blo 463784 465323 := bstep (se 1 (by rfl) ⟨348992, by rfl⟩ : syracuseStep 465323 = 697985) B697985
theorem B465335 : Blo 463784 465335 := bstep (se 1 (by rfl) ⟨349001, by rfl⟩ : syracuseStep 465335 = 698003) B698003
theorem B465355 : Blo 463784 465355 := bstep (se 1 (by rfl) ⟨349016, by rfl⟩ : syracuseStep 465355 = 698033) B698033
theorem B465367 : Blo 463784 465367 := bstep (se 1 (by rfl) ⟨349025, by rfl⟩ : syracuseStep 465367 = 698051) B698051
theorem B13408739 : Blo 463784 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B465387 : Blo 463784 465387 := bstep (se 1 (by rfl) ⟨349040, by rfl⟩ : syracuseStep 465387 = 698081) B698081
theorem B465399 : Blo 463784 465399 := bstep (se 1 (by rfl) ⟨349049, by rfl⟩ : syracuseStep 465399 = 698099) B698099
theorem B465419 : Blo 463784 465419 := bstep (se 1 (by rfl) ⟨349064, by rfl⟩ : syracuseStep 465419 = 698129) B698129
theorem B465431 : Blo 463784 465431 := bstep (se 1 (by rfl) ⟨349073, by rfl⟩ : syracuseStep 465431 = 698147) B698147
theorem B465451 : Blo 463784 465451 := bstep (se 1 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 465451 = 698177) B698177
theorem B465463 : Blo 463784 465463 := bstep (se 1 (by rfl) ⟨349097, by rfl⟩ : syracuseStep 465463 = 698195) B698195
theorem B465483 : Blo 463784 465483 := bstep (se 1 (by rfl) ⟨349112, by rfl⟩ : syracuseStep 465483 = 698225) B698225
theorem B465495 : Blo 463784 465495 := bstep (se 1 (by rfl) ⟨349121, by rfl⟩ : syracuseStep 465495 = 698243) B698243
theorem B629335 : Blo 463784 629335 := bstep (se 1 (by rfl) ⟨472001, by rfl⟩ : syracuseStep 629335 = 944003) B944003
theorem B465515 : Blo 463784 465515 := bstep (se 1 (by rfl) ⟨349136, by rfl⟩ : syracuseStep 465515 = 698273) B698273
theorem B465527 : Blo 463784 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B5380739 : Blo 463784 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B465547 : Blo 463784 465547 := bstep (se 1 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 465547 = 698321) B698321
theorem B465559 : Blo 463784 465559 := bstep (se 1 (by rfl) ⟨349169, by rfl⟩ : syracuseStep 465559 = 698339) B698339
theorem B465579 : Blo 463784 465579 := bstep (se 1 (by rfl) ⟨349184, by rfl⟩ : syracuseStep 465579 = 698369) B698369
theorem B465591 : Blo 463784 465591 := bstep (se 1 (by rfl) ⟨349193, by rfl⟩ : syracuseStep 465591 = 698387) B698387
theorem B498359 : Blo 463784 498359 := bstep (se 1 (by rfl) ⟨373769, by rfl⟩ : syracuseStep 498359 = 747539) B747539
theorem B465611 : Blo 463784 465611 := bstep (se 1 (by rfl) ⟨349208, by rfl⟩ : syracuseStep 465611 = 698417) B698417
theorem B465623 : Blo 463784 465623 := bstep (se 1 (by rfl) ⟨349217, by rfl⟩ : syracuseStep 465623 = 698435) B698435
theorem B465643 : Blo 463784 465643 := bstep (se 1 (by rfl) ⟨349232, by rfl⟩ : syracuseStep 465643 = 698465) B698465
theorem B465655 : Blo 463784 465655 := bstep (se 1 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 465655 = 698483) B698483
theorem B465675 : Blo 463784 465675 := bstep (se 1 (by rfl) ⟨349256, by rfl⟩ : syracuseStep 465675 = 698513) B698513
theorem B465687 : Blo 463784 465687 := bstep (se 1 (by rfl) ⟨349265, by rfl⟩ : syracuseStep 465687 = 698531) B698531
theorem B465707 : Blo 463784 465707 := bstep (se 1 (by rfl) ⟨349280, by rfl⟩ : syracuseStep 465707 = 698561) B698561
theorem B2988845 : Blo 463784 2988845 := bstep (se 3 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 2988845 = 1120817) B1120817
theorem B465719 : Blo 463784 465719 := bstep (se 1 (by rfl) ⟨349289, by rfl⟩ : syracuseStep 465719 = 698579) B698579
theorem B3054401 : Blo 463784 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B465739 : Blo 463784 465739 := bstep (se 1 (by rfl) ⟨349304, by rfl⟩ : syracuseStep 465739 = 698609) B698609
theorem B465751 : Blo 463784 465751 := bstep (se 1 (by rfl) ⟨349313, by rfl⟩ : syracuseStep 465751 = 698627) B698627
theorem B465771 : Blo 463784 465771 := bstep (se 1 (by rfl) ⟨349328, by rfl⟩ : syracuseStep 465771 = 698657) B698657
theorem B465783 : Blo 463784 465783 := bstep (se 1 (by rfl) ⟨349337, by rfl⟩ : syracuseStep 465783 = 698675) B698675
theorem B465803 : Blo 463784 465803 := bstep (se 1 (by rfl) ⟨349352, by rfl⟩ : syracuseStep 465803 = 698705) B698705
theorem B465815 : Blo 463784 465815 := bstep (se 1 (by rfl) ⟨349361, by rfl⟩ : syracuseStep 465815 = 698723) B698723
theorem B465835 : Blo 463784 465835 := bstep (se 1 (by rfl) ⟨349376, by rfl⟩ : syracuseStep 465835 = 698753) B698753
theorem B465847 : Blo 463784 465847 := bstep (se 1 (by rfl) ⟨349385, by rfl⟩ : syracuseStep 465847 = 698771) B698771
theorem B465867 : Blo 463784 465867 := bstep (se 1 (by rfl) ⟨349400, by rfl⟩ : syracuseStep 465867 = 698801) B698801
theorem B465879 : Blo 463784 465879 := bstep (se 1 (by rfl) ⟨349409, by rfl⟩ : syracuseStep 465879 = 698819) B698819
theorem B465899 : Blo 463784 465899 := bstep (se 1 (by rfl) ⟨349424, by rfl⟩ : syracuseStep 465899 = 698849) B698849
theorem B465911 : Blo 463784 465911 := bstep (se 1 (by rfl) ⟨349433, by rfl⟩ : syracuseStep 465911 = 698867) B698867
theorem B465931 : Blo 463784 465931 := bstep (se 1 (by rfl) ⟨349448, by rfl⟩ : syracuseStep 465931 = 698897) B698897
theorem B465943 : Blo 463784 465943 := bstep (se 1 (by rfl) ⟨349457, by rfl⟩ : syracuseStep 465943 = 698915) B698915
theorem B465963 : Blo 463784 465963 := bstep (se 1 (by rfl) ⟨349472, by rfl⟩ : syracuseStep 465963 = 698945) B698945
theorem B465975 : Blo 463784 465975 := bstep (se 1 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 465975 = 698963) B698963
theorem B465995 : Blo 463784 465995 := bstep (se 1 (by rfl) ⟨349496, by rfl⟩ : syracuseStep 465995 = 698993) B698993
theorem B466007 : Blo 463784 466007 := bstep (se 1 (by rfl) ⟨349505, by rfl⟩ : syracuseStep 466007 = 699011) B699011
theorem B466027 : Blo 463784 466027 := bstep (se 1 (by rfl) ⟨349520, by rfl⟩ : syracuseStep 466027 = 699041) B699041
theorem B466039 : Blo 463784 466039 := bstep (se 1 (by rfl) ⟨349529, by rfl⟩ : syracuseStep 466039 = 699059) B699059
theorem B793739 : Blo 463784 793739 := bstep (se 1 (by rfl) ⟨595304, by rfl⟩ : syracuseStep 793739 = 1190609) B1190609
theorem B466059 : Blo 463784 466059 := bstep (se 1 (by rfl) ⟨349544, by rfl⟩ : syracuseStep 466059 = 699089) B699089
theorem B466071 : Blo 463784 466071 := bstep (se 1 (by rfl) ⟨349553, by rfl⟩ : syracuseStep 466071 = 699107) B699107
theorem B466091 : Blo 463784 466091 := bstep (se 1 (by rfl) ⟨349568, by rfl⟩ : syracuseStep 466091 = 699137) B699137
theorem B466103 : Blo 463784 466103 := bstep (se 1 (by rfl) ⟨349577, by rfl⟩ : syracuseStep 466103 = 699155) B699155
theorem B466123 : Blo 463784 466123 := bstep (se 1 (by rfl) ⟨349592, by rfl⟩ : syracuseStep 466123 = 699185) B699185
theorem B466135 : Blo 463784 466135 := bstep (se 1 (by rfl) ⟨349601, by rfl⟩ : syracuseStep 466135 = 699203) B699203
theorem B466155 : Blo 463784 466155 := bstep (se 1 (by rfl) ⟨349616, by rfl⟩ : syracuseStep 466155 = 699233) B699233
theorem B466167 : Blo 463784 466167 := bstep (se 1 (by rfl) ⟨349625, by rfl⟩ : syracuseStep 466167 = 699251) B699251
theorem B466187 : Blo 463784 466187 := bstep (se 1 (by rfl) ⟨349640, by rfl⟩ : syracuseStep 466187 = 699281) B699281
theorem B466199 : Blo 463784 466199 := bstep (se 1 (by rfl) ⟨349649, by rfl⟩ : syracuseStep 466199 = 699299) B699299
theorem B466219 : Blo 463784 466219 := bstep (se 1 (by rfl) ⟨349664, by rfl⟩ : syracuseStep 466219 = 699329) B699329
theorem B466231 : Blo 463784 466231 := bstep (se 1 (by rfl) ⟨349673, by rfl⟩ : syracuseStep 466231 = 699347) B699347
theorem B466251 : Blo 463784 466251 := bstep (se 1 (by rfl) ⟨349688, by rfl⟩ : syracuseStep 466251 = 699377) B699377
theorem B531787 : Blo 463784 531787 := bstep (se 1 (by rfl) ⟨398840, by rfl⟩ : syracuseStep 531787 = 797681) B797681
theorem B466263 : Blo 463784 466263 := bstep (se 1 (by rfl) ⟨349697, by rfl⟩ : syracuseStep 466263 = 699395) B699395
theorem B466283 : Blo 463784 466283 := bstep (se 1 (by rfl) ⟨349712, by rfl⟩ : syracuseStep 466283 = 699425) B699425
theorem B466295 : Blo 463784 466295 := bstep (se 1 (by rfl) ⟨349721, by rfl⟩ : syracuseStep 466295 = 699443) B699443
theorem B466315 : Blo 463784 466315 := bstep (se 1 (by rfl) ⟨349736, by rfl⟩ : syracuseStep 466315 = 699473) B699473
theorem B466327 : Blo 463784 466327 := bstep (se 1 (by rfl) ⟨349745, by rfl⟩ : syracuseStep 466327 = 699491) B699491
theorem B695705 : Blo 463784 695705 := bstep (se 2 (by rfl) ⟨260889, by rfl⟩ : syracuseStep 695705 = 521779) B521779
theorem B466347 : Blo 463784 466347 := bstep (se 1 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 466347 = 699521) B699521
theorem B3349937 : Blo 463784 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B990643 : Blo 463784 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B466359 : Blo 463784 466359 := bstep (se 1 (by rfl) ⟨349769, by rfl⟩ : syracuseStep 466359 = 699539) B699539
theorem B466379 : Blo 463784 466379 := bstep (se 1 (by rfl) ⟨349784, by rfl⟩ : syracuseStep 466379 = 699569) B699569
theorem B466391 : Blo 463784 466391 := bstep (se 1 (by rfl) ⟨349793, by rfl⟩ : syracuseStep 466391 = 699587) B699587
theorem B466411 : Blo 463784 466411 := bstep (se 1 (by rfl) ⟨349808, by rfl⟩ : syracuseStep 466411 = 699617) B699617
theorem B466423 : Blo 463784 466423 := bstep (se 1 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 466423 = 699635) B699635
theorem B695819 : Blo 463784 695819 := bstep (se 1 (by rfl) ⟨521864, by rfl⟩ : syracuseStep 695819 = 1043729) B1043729
theorem B466443 : Blo 463784 466443 := bstep (se 1 (by rfl) ⟨349832, by rfl⟩ : syracuseStep 466443 = 699665) B699665
theorem B466455 : Blo 463784 466455 := bstep (se 1 (by rfl) ⟨349841, by rfl⟩ : syracuseStep 466455 = 699683) B699683
theorem B695831 : Blo 463784 695831 := bstep (se 1 (by rfl) ⟨521873, by rfl⟩ : syracuseStep 695831 = 1043747) B1043747
theorem B466475 : Blo 463784 466475 := bstep (se 1 (by rfl) ⟨349856, by rfl⟩ : syracuseStep 466475 = 699713) B699713
theorem B466487 : Blo 463784 466487 := bstep (se 1 (by rfl) ⟨349865, by rfl⟩ : syracuseStep 466487 = 699731) B699731
theorem B466507 : Blo 463784 466507 := bstep (se 1 (by rfl) ⟨349880, by rfl⟩ : syracuseStep 466507 = 699761) B699761
theorem B466519 : Blo 463784 466519 := bstep (se 1 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 466519 = 699779) B699779
theorem B695897 : Blo 463784 695897 := bstep (se 2 (by rfl) ⟨260961, by rfl⟩ : syracuseStep 695897 = 521923) B521923
theorem B466539 : Blo 463784 466539 := bstep (se 1 (by rfl) ⟨349904, by rfl⟩ : syracuseStep 466539 = 699809) B699809
theorem B466551 : Blo 463784 466551 := bstep (se 1 (by rfl) ⟨349913, by rfl⟩ : syracuseStep 466551 = 699827) B699827
theorem B466571 : Blo 463784 466571 := bstep (se 1 (by rfl) ⟨349928, by rfl⟩ : syracuseStep 466571 = 699857) B699857
theorem B466583 : Blo 463784 466583 := bstep (se 1 (by rfl) ⟨349937, by rfl⟩ : syracuseStep 466583 = 699875) B699875
theorem B466603 : Blo 463784 466603 := bstep (se 1 (by rfl) ⟨349952, by rfl⟩ : syracuseStep 466603 = 699905) B699905
theorem B466615 : Blo 463784 466615 := bstep (se 1 (by rfl) ⟨349961, by rfl⟩ : syracuseStep 466615 = 699923) B699923
theorem B696011 : Blo 463784 696011 := bstep (se 1 (by rfl) ⟨522008, by rfl⟩ : syracuseStep 696011 = 1044017) B1044017
theorem B466635 : Blo 463784 466635 := bstep (se 1 (by rfl) ⟨349976, by rfl⟩ : syracuseStep 466635 = 699953) B699953
theorem B696023 : Blo 463784 696023 := bstep (se 1 (by rfl) ⟨522017, by rfl⟩ : syracuseStep 696023 = 1044035) B1044035
theorem B466647 : Blo 463784 466647 := bstep (se 1 (by rfl) ⟨349985, by rfl⟩ : syracuseStep 466647 = 699971) B699971
theorem B466667 : Blo 463784 466667 := bstep (se 1 (by rfl) ⟨350000, by rfl⟩ : syracuseStep 466667 = 700001) B700001
theorem B466679 : Blo 463784 466679 := bstep (se 1 (by rfl) ⟨350009, by rfl⟩ : syracuseStep 466679 = 700019) B700019
theorem B466699 : Blo 463784 466699 := bstep (se 1 (by rfl) ⟨350024, by rfl⟩ : syracuseStep 466699 = 700049) B700049
theorem B466711 : Blo 463784 466711 := bstep (se 1 (by rfl) ⟨350033, by rfl⟩ : syracuseStep 466711 = 700067) B700067
theorem B696089 : Blo 463784 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B466731 : Blo 463784 466731 := bstep (se 1 (by rfl) ⟨350048, by rfl⟩ : syracuseStep 466731 = 700097) B700097
theorem B466743 : Blo 463784 466743 := bstep (se 1 (by rfl) ⟨350057, by rfl⟩ : syracuseStep 466743 = 700115) B700115
theorem B466763 : Blo 463784 466763 := bstep (se 1 (by rfl) ⟨350072, by rfl⟩ : syracuseStep 466763 = 700145) B700145
theorem B466775 : Blo 463784 466775 := bstep (se 1 (by rfl) ⟨350081, by rfl⟩ : syracuseStep 466775 = 700163) B700163
theorem B663385 : Blo 463784 663385 := bstep (se 2 (by rfl) ⟨248769, by rfl⟩ : syracuseStep 663385 = 497539) B497539
theorem B466795 : Blo 463784 466795 := bstep (se 1 (by rfl) ⟨350096, by rfl⟩ : syracuseStep 466795 = 700193) B700193
theorem B466807 : Blo 463784 466807 := bstep (se 1 (by rfl) ⟨350105, by rfl⟩ : syracuseStep 466807 = 700211) B700211
theorem B696203 : Blo 463784 696203 := bstep (se 1 (by rfl) ⟨522152, by rfl⟩ : syracuseStep 696203 = 1044305) B1044305
theorem B466827 : Blo 463784 466827 := bstep (se 1 (by rfl) ⟨350120, by rfl⟩ : syracuseStep 466827 = 700241) B700241
theorem B696215 : Blo 463784 696215 := bstep (se 1 (by rfl) ⟨522161, by rfl⟩ : syracuseStep 696215 = 1044323) B1044323
theorem B466839 : Blo 463784 466839 := bstep (se 1 (by rfl) ⟨350129, by rfl⟩ : syracuseStep 466839 = 700259) B700259
theorem B466859 : Blo 463784 466859 := bstep (se 1 (by rfl) ⟨350144, by rfl⟩ : syracuseStep 466859 = 700289) B700289
theorem B466871 : Blo 463784 466871 := bstep (se 1 (by rfl) ⟨350153, by rfl⟩ : syracuseStep 466871 = 700307) B700307
theorem B466891 : Blo 463784 466891 := bstep (se 1 (by rfl) ⟨350168, by rfl⟩ : syracuseStep 466891 = 700337) B700337
theorem B466903 : Blo 463784 466903 := bstep (se 1 (by rfl) ⟨350177, by rfl⟩ : syracuseStep 466903 = 700355) B700355
theorem B696281 : Blo 463784 696281 := bstep (se 2 (by rfl) ⟨261105, by rfl⟩ : syracuseStep 696281 = 522211) B522211
theorem B466923 : Blo 463784 466923 := bstep (se 1 (by rfl) ⟨350192, by rfl⟩ : syracuseStep 466923 = 700385) B700385
theorem B466935 : Blo 463784 466935 := bstep (se 1 (by rfl) ⟨350201, by rfl⟩ : syracuseStep 466935 = 700403) B700403
theorem B466955 : Blo 463784 466955 := bstep (se 1 (by rfl) ⟨350216, by rfl⟩ : syracuseStep 466955 = 700433) B700433
theorem B466967 : Blo 463784 466967 := bstep (se 1 (by rfl) ⟨350225, by rfl⟩ : syracuseStep 466967 = 700451) B700451
theorem B12754979 : Blo 463784 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B466987 : Blo 463784 466987 := bstep (se 1 (by rfl) ⟨350240, by rfl⟩ : syracuseStep 466987 = 700481) B700481
theorem B466999 : Blo 463784 466999 := bstep (se 1 (by rfl) ⟨350249, by rfl⟩ : syracuseStep 466999 = 700499) B700499
theorem B696395 : Blo 463784 696395 := bstep (se 1 (by rfl) ⟨522296, by rfl⟩ : syracuseStep 696395 = 1044593) B1044593
theorem B467019 : Blo 463784 467019 := bstep (se 1 (by rfl) ⟨350264, by rfl⟩ : syracuseStep 467019 = 700529) B700529
theorem B696407 : Blo 463784 696407 := bstep (se 1 (by rfl) ⟨522305, by rfl⟩ : syracuseStep 696407 = 1044611) B1044611
theorem B467031 : Blo 463784 467031 := bstep (se 1 (by rfl) ⟨350273, by rfl⟩ : syracuseStep 467031 = 700547) B700547
theorem B467051 : Blo 463784 467051 := bstep (se 1 (by rfl) ⟨350288, by rfl⟩ : syracuseStep 467051 = 700577) B700577
theorem B467063 : Blo 463784 467063 := bstep (se 1 (by rfl) ⟨350297, by rfl⟩ : syracuseStep 467063 = 700595) B700595
theorem B991361 : Blo 463784 991361 := bstep (se 2 (by rfl) ⟨371760, by rfl⟩ : syracuseStep 991361 = 743521) B743521
theorem B467083 : Blo 463784 467083 := bstep (se 1 (by rfl) ⟨350312, by rfl⟩ : syracuseStep 467083 = 700625) B700625
theorem B467095 : Blo 463784 467095 := bstep (se 1 (by rfl) ⟨350321, by rfl⟩ : syracuseStep 467095 = 700643) B700643
theorem B696473 : Blo 463784 696473 := bstep (se 2 (by rfl) ⟨261177, by rfl⟩ : syracuseStep 696473 = 522355) B522355
theorem B467115 : Blo 463784 467115 := bstep (se 1 (by rfl) ⟨350336, by rfl⟩ : syracuseStep 467115 = 700673) B700673
theorem B3547313 : Blo 463784 3547313 := bstep (se 2 (by rfl) ⟨1330242, by rfl⟩ : syracuseStep 3547313 = 2660485) B2660485
theorem B467127 : Blo 463784 467127 := bstep (se 1 (by rfl) ⟨350345, by rfl⟩ : syracuseStep 467127 = 700691) B700691
theorem B467147 : Blo 463784 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B467159 : Blo 463784 467159 := bstep (se 1 (by rfl) ⟨350369, by rfl⟩ : syracuseStep 467159 = 700739) B700739
theorem B467179 : Blo 463784 467179 := bstep (se 1 (by rfl) ⟨350384, by rfl⟩ : syracuseStep 467179 = 700769) B700769
theorem B467191 : Blo 463784 467191 := bstep (se 1 (by rfl) ⟨350393, by rfl⟩ : syracuseStep 467191 = 700787) B700787
theorem B696587 : Blo 463784 696587 := bstep (se 1 (by rfl) ⟨522440, by rfl⟩ : syracuseStep 696587 = 1044881) B1044881
theorem B467211 : Blo 463784 467211 := bstep (se 1 (by rfl) ⟨350408, by rfl⟩ : syracuseStep 467211 = 700817) B700817
theorem B696599 : Blo 463784 696599 := bstep (se 1 (by rfl) ⟨522449, by rfl⟩ : syracuseStep 696599 = 1044899) B1044899
theorem B467223 : Blo 463784 467223 := bstep (se 1 (by rfl) ⟨350417, by rfl⟩ : syracuseStep 467223 = 700835) B700835
theorem B467243 : Blo 463784 467243 := bstep (se 1 (by rfl) ⟨350432, by rfl⟩ : syracuseStep 467243 = 700865) B700865
theorem B467255 : Blo 463784 467255 := bstep (se 1 (by rfl) ⟨350441, by rfl⟩ : syracuseStep 467255 = 700883) B700883
theorem B467275 : Blo 463784 467275 := bstep (se 1 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 467275 = 700913) B700913
theorem B467287 : Blo 463784 467287 := bstep (se 1 (by rfl) ⟨350465, by rfl⟩ : syracuseStep 467287 = 700931) B700931
theorem B696665 : Blo 463784 696665 := bstep (se 2 (by rfl) ⟨261249, by rfl⟩ : syracuseStep 696665 = 522499) B522499
theorem B467307 : Blo 463784 467307 := bstep (se 1 (by rfl) ⟨350480, by rfl⟩ : syracuseStep 467307 = 700961) B700961
theorem B467319 : Blo 463784 467319 := bstep (se 1 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 467319 = 700979) B700979
theorem B467339 : Blo 463784 467339 := bstep (se 1 (by rfl) ⟨350504, by rfl⟩ : syracuseStep 467339 = 701009) B701009
theorem B467351 : Blo 463784 467351 := bstep (se 1 (by rfl) ⟨350513, by rfl⟩ : syracuseStep 467351 = 701027) B701027
theorem B467371 : Blo 463784 467371 := bstep (se 1 (by rfl) ⟨350528, by rfl⟩ : syracuseStep 467371 = 701057) B701057
theorem B6693299 : Blo 463784 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B467383 : Blo 463784 467383 := bstep (se 1 (by rfl) ⟨350537, by rfl⟩ : syracuseStep 467383 = 701075) B701075
theorem B696779 : Blo 463784 696779 := bstep (se 1 (by rfl) ⟨522584, by rfl⟩ : syracuseStep 696779 = 1045169) B1045169
theorem B467403 : Blo 463784 467403 := bstep (se 1 (by rfl) ⟨350552, by rfl⟩ : syracuseStep 467403 = 701105) B701105
theorem B991703 : Blo 463784 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B696791 : Blo 463784 696791 := bstep (se 1 (by rfl) ⟨522593, by rfl⟩ : syracuseStep 696791 = 1045187) B1045187
theorem B467415 : Blo 463784 467415 := bstep (se 1 (by rfl) ⟨350561, by rfl⟩ : syracuseStep 467415 = 701123) B701123
theorem B467435 : Blo 463784 467435 := bstep (se 1 (by rfl) ⟨350576, by rfl⟩ : syracuseStep 467435 = 701153) B701153
theorem B467447 : Blo 463784 467447 := bstep (se 1 (by rfl) ⟨350585, by rfl⟩ : syracuseStep 467447 = 701171) B701171
theorem B467467 : Blo 463784 467467 := bstep (se 1 (by rfl) ⟨350600, by rfl⟩ : syracuseStep 467467 = 701201) B701201
theorem B467479 : Blo 463784 467479 := bstep (se 1 (by rfl) ⟨350609, by rfl⟩ : syracuseStep 467479 = 701219) B701219
theorem B696857 : Blo 463784 696857 := bstep (se 2 (by rfl) ⟨261321, by rfl⟩ : syracuseStep 696857 = 522643) B522643
theorem B467499 : Blo 463784 467499 := bstep (se 1 (by rfl) ⟨350624, by rfl⟩ : syracuseStep 467499 = 701249) B701249
theorem B467511 : Blo 463784 467511 := bstep (se 1 (by rfl) ⟨350633, by rfl⟩ : syracuseStep 467511 = 701267) B701267
theorem B467531 : Blo 463784 467531 := bstep (se 1 (by rfl) ⟨350648, by rfl⟩ : syracuseStep 467531 = 701297) B701297
theorem B467543 : Blo 463784 467543 := bstep (se 1 (by rfl) ⟨350657, by rfl⟩ : syracuseStep 467543 = 701315) B701315
theorem B2237021 : Blo 463784 2237021 := bstep (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) B838883
theorem B467563 : Blo 463784 467563 := bstep (se 1 (by rfl) ⟨350672, by rfl⟩ : syracuseStep 467563 = 701345) B701345
theorem B467575 : Blo 463784 467575 := bstep (se 1 (by rfl) ⟨350681, by rfl⟩ : syracuseStep 467575 = 701363) B701363
theorem B991873 : Blo 463784 991873 := bstep (se 2 (by rfl) ⟨371952, by rfl⟩ : syracuseStep 991873 = 743905) B743905
theorem B696971 : Blo 463784 696971 := bstep (se 1 (by rfl) ⟨522728, by rfl⟩ : syracuseStep 696971 = 1045457) B1045457
theorem B467595 : Blo 463784 467595 := bstep (se 1 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 467595 = 701393) B701393
theorem B696983 : Blo 463784 696983 := bstep (se 1 (by rfl) ⟨522737, by rfl⟩ : syracuseStep 696983 = 1045475) B1045475
theorem B3547799 : Blo 463784 3547799 := bstep (se 1 (by rfl) ⟨2660849, by rfl⟩ : syracuseStep 3547799 = 5321699) B5321699
theorem B467607 : Blo 463784 467607 := bstep (se 1 (by rfl) ⟨350705, by rfl⟩ : syracuseStep 467607 = 701411) B701411
theorem B467627 : Blo 463784 467627 := bstep (se 1 (by rfl) ⟨350720, by rfl⟩ : syracuseStep 467627 = 701441) B701441
theorem B467639 : Blo 463784 467639 := bstep (se 1 (by rfl) ⟨350729, by rfl⟩ : syracuseStep 467639 = 701459) B701459
theorem B467659 : Blo 463784 467659 := bstep (se 1 (by rfl) ⟨350744, by rfl⟩ : syracuseStep 467659 = 701489) B701489
theorem B5317325 : Blo 463784 5317325 := bstep (se 3 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 5317325 = 1993997) B1993997
theorem B467671 : Blo 463784 467671 := bstep (se 1 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 467671 = 701507) B701507
theorem B697049 : Blo 463784 697049 := bstep (se 2 (by rfl) ⟨261393, by rfl⟩ : syracuseStep 697049 = 522787) B522787
theorem B467691 : Blo 463784 467691 := bstep (se 1 (by rfl) ⟨350768, by rfl⟩ : syracuseStep 467691 = 701537) B701537
theorem B467703 : Blo 463784 467703 := bstep (se 1 (by rfl) ⟨350777, by rfl⟩ : syracuseStep 467703 = 701555) B701555
theorem B467723 : Blo 463784 467723 := bstep (se 1 (by rfl) ⟨350792, by rfl⟩ : syracuseStep 467723 = 701585) B701585
theorem B467735 : Blo 463784 467735 := bstep (se 1 (by rfl) ⟨350801, by rfl⟩ : syracuseStep 467735 = 701603) B701603
theorem B467755 : Blo 463784 467755 := bstep (se 1 (by rfl) ⟨350816, by rfl⟩ : syracuseStep 467755 = 701633) B701633
theorem B467767 : Blo 463784 467767 := bstep (se 1 (by rfl) ⟨350825, by rfl⟩ : syracuseStep 467767 = 701651) B701651
theorem B697163 : Blo 463784 697163 := bstep (se 1 (by rfl) ⟨522872, by rfl⟩ : syracuseStep 697163 = 1045745) B1045745
theorem B697175 : Blo 463784 697175 := bstep (se 1 (by rfl) ⟨522881, by rfl⟩ : syracuseStep 697175 = 1045763) B1045763
theorem B697241 : Blo 463784 697241 := bstep (se 2 (by rfl) ⟨261465, by rfl⟩ : syracuseStep 697241 = 522931) B522931
theorem B697355 : Blo 463784 697355 := bstep (se 1 (by rfl) ⟨523016, by rfl⟩ : syracuseStep 697355 = 1046033) B1046033
theorem B697367 : Blo 463784 697367 := bstep (se 1 (by rfl) ⟨523025, by rfl⟩ : syracuseStep 697367 = 1046051) B1046051
theorem B697433 : Blo 463784 697433 := bstep (se 2 (by rfl) ⟨261537, by rfl⟩ : syracuseStep 697433 = 523075) B523075
theorem B697547 : Blo 463784 697547 := bstep (se 1 (by rfl) ⟨523160, by rfl⟩ : syracuseStep 697547 = 1046321) B1046321
theorem B697559 : Blo 463784 697559 := bstep (se 1 (by rfl) ⟨523169, by rfl⟩ : syracuseStep 697559 = 1046339) B1046339
theorem B664843 : Blo 463784 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B697625 : Blo 463784 697625 := bstep (se 2 (by rfl) ⟨261609, by rfl⟩ : syracuseStep 697625 = 523219) B523219
theorem B697739 : Blo 463784 697739 := bstep (se 1 (by rfl) ⟨523304, by rfl⟩ : syracuseStep 697739 = 1046609) B1046609
theorem B697751 : Blo 463784 697751 := bstep (se 1 (by rfl) ⟨523313, by rfl⟩ : syracuseStep 697751 = 1046627) B1046627
theorem B697817 : Blo 463784 697817 := bstep (se 2 (by rfl) ⟨261681, by rfl⟩ : syracuseStep 697817 = 523363) B523363
theorem B697931 : Blo 463784 697931 := bstep (se 1 (by rfl) ⟨523448, by rfl⟩ : syracuseStep 697931 = 1046897) B1046897
theorem B697943 : Blo 463784 697943 := bstep (se 1 (by rfl) ⟨523457, by rfl⟩ : syracuseStep 697943 = 1046915) B1046915
theorem B698009 : Blo 463784 698009 := bstep (se 2 (by rfl) ⟨261753, by rfl⟩ : syracuseStep 698009 = 523507) B523507
theorem B1058483 : Blo 463784 1058483 := bstep (se 1 (by rfl) ⟨793862, by rfl⟩ : syracuseStep 1058483 = 1587725) B1587725
theorem B993035 : Blo 463784 993035 := bstep (se 1 (by rfl) ⟨744776, by rfl⟩ : syracuseStep 993035 = 1489553) B1489553
theorem B698123 : Blo 463784 698123 := bstep (se 1 (by rfl) ⟨523592, by rfl⟩ : syracuseStep 698123 = 1047185) B1047185
theorem B698135 : Blo 463784 698135 := bstep (se 1 (by rfl) ⟨523601, by rfl⟩ : syracuseStep 698135 = 1047203) B1047203
theorem B698201 : Blo 463784 698201 := bstep (se 2 (by rfl) ⟨261825, by rfl⟩ : syracuseStep 698201 = 523651) B523651
theorem B698315 : Blo 463784 698315 := bstep (se 1 (by rfl) ⟨523736, by rfl⟩ : syracuseStep 698315 = 1047473) B1047473
theorem B698327 : Blo 463784 698327 := bstep (se 1 (by rfl) ⟨523745, by rfl⟩ : syracuseStep 698327 = 1047491) B1047491
theorem B698393 : Blo 463784 698393 := bstep (se 2 (by rfl) ⟨261897, by rfl⟩ : syracuseStep 698393 = 523795) B523795
theorem B698507 : Blo 463784 698507 := bstep (se 1 (by rfl) ⟨523880, by rfl⟩ : syracuseStep 698507 = 1047761) B1047761
theorem B698519 : Blo 463784 698519 := bstep (se 1 (by rfl) ⟨523889, by rfl⟩ : syracuseStep 698519 = 1047779) B1047779
theorem B698585 : Blo 463784 698585 := bstep (se 2 (by rfl) ⟨261969, by rfl⟩ : syracuseStep 698585 = 523939) B523939
theorem B3352877 : Blo 463784 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B1321267 : Blo 463784 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B698699 : Blo 463784 698699 := bstep (se 1 (by rfl) ⟨524024, by rfl⟩ : syracuseStep 698699 = 1048049) B1048049
theorem B698711 : Blo 463784 698711 := bstep (se 1 (by rfl) ⟨524033, by rfl⟩ : syracuseStep 698711 = 1048067) B1048067
theorem B2992535 : Blo 463784 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B698777 : Blo 463784 698777 := bstep (se 2 (by rfl) ⟨262041, by rfl⟩ : syracuseStep 698777 = 524083) B524083
theorem B3582413 : Blo 463784 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B16394723 : Blo 463784 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B993779 : Blo 463784 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B698891 : Blo 463784 698891 := bstep (se 1 (by rfl) ⟨524168, by rfl⟩ : syracuseStep 698891 = 1048337) B1048337
theorem B698903 : Blo 463784 698903 := bstep (se 1 (by rfl) ⟨524177, by rfl⟩ : syracuseStep 698903 = 1048355) B1048355
theorem B1190465 : Blo 463784 1190465 := bstep (se 2 (by rfl) ⟨446424, by rfl⟩ : syracuseStep 1190465 = 892849) B892849
theorem B698969 : Blo 463784 698969 := bstep (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) B524227
theorem B699083 : Blo 463784 699083 := bstep (se 1 (by rfl) ⟨524312, by rfl⟩ : syracuseStep 699083 = 1048625) B1048625
theorem B699095 : Blo 463784 699095 := bstep (se 1 (by rfl) ⟨524321, by rfl⟩ : syracuseStep 699095 = 1048643) B1048643
theorem B797401 : Blo 463784 797401 := bstep (se 2 (by rfl) ⟨299025, by rfl⟩ : syracuseStep 797401 = 598051) B598051
theorem B699161 : Blo 463784 699161 := bstep (se 2 (by rfl) ⟨262185, by rfl⟩ : syracuseStep 699161 = 524371) B524371
theorem B764759 : Blo 463784 764759 := bstep (se 1 (by rfl) ⟨573569, by rfl⟩ : syracuseStep 764759 = 1147139) B1147139
theorem B699275 : Blo 463784 699275 := bstep (se 1 (by rfl) ⟨524456, by rfl⟩ : syracuseStep 699275 = 1048913) B1048913
theorem B699287 : Blo 463784 699287 := bstep (se 1 (by rfl) ⟨524465, by rfl⟩ : syracuseStep 699287 = 1048931) B1048931
theorem B699353 : Blo 463784 699353 := bstep (se 2 (by rfl) ⟨262257, by rfl⟩ : syracuseStep 699353 = 524515) B524515
theorem B699467 : Blo 463784 699467 := bstep (se 1 (by rfl) ⟨524600, by rfl⟩ : syracuseStep 699467 = 1049201) B1049201
theorem B699479 : Blo 463784 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B4041859 : Blo 463784 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B699545 : Blo 463784 699545 := bstep (se 2 (by rfl) ⟨262329, by rfl⟩ : syracuseStep 699545 = 524659) B524659
theorem B699659 : Blo 463784 699659 := bstep (se 1 (by rfl) ⟨524744, by rfl⟩ : syracuseStep 699659 = 1049489) B1049489
theorem B699671 : Blo 463784 699671 := bstep (se 1 (by rfl) ⟨524753, by rfl⟩ : syracuseStep 699671 = 1049507) B1049507
theorem B1322315 : Blo 463784 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B699737 : Blo 463784 699737 := bstep (se 2 (by rfl) ⟨262401, by rfl⟩ : syracuseStep 699737 = 524803) B524803
theorem B994675 : Blo 463784 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B699851 : Blo 463784 699851 := bstep (se 1 (by rfl) ⟨524888, by rfl⟩ : syracuseStep 699851 = 1049777) B1049777
theorem B699863 : Blo 463784 699863 := bstep (se 1 (by rfl) ⟨524897, by rfl⟩ : syracuseStep 699863 = 1049795) B1049795
theorem B699929 : Blo 463784 699929 := bstep (se 2 (by rfl) ⟨262473, by rfl⟩ : syracuseStep 699929 = 524947) B524947
theorem B700043 : Blo 463784 700043 := bstep (se 1 (by rfl) ⟨525032, by rfl⟩ : syracuseStep 700043 = 1050065) B1050065
theorem B700055 : Blo 463784 700055 := bstep (se 1 (by rfl) ⟨525041, by rfl⟩ : syracuseStep 700055 = 1050083) B1050083
theorem B700121 : Blo 463784 700121 := bstep (se 2 (by rfl) ⟨262545, by rfl⟩ : syracuseStep 700121 = 525091) B525091
theorem B700235 : Blo 463784 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B700247 : Blo 463784 700247 := bstep (se 1 (by rfl) ⟨525185, by rfl⟩ : syracuseStep 700247 = 1050371) B1050371
theorem B896897 : Blo 463784 896897 := bstep (se 2 (by rfl) ⟨336336, by rfl⟩ : syracuseStep 896897 = 672673) B672673
theorem B700313 : Blo 463784 700313 := bstep (se 2 (by rfl) ⟨262617, by rfl⟩ : syracuseStep 700313 = 525235) B525235
theorem B700427 : Blo 463784 700427 := bstep (se 1 (by rfl) ⟨525320, by rfl⟩ : syracuseStep 700427 = 1050641) B1050641
theorem B700439 : Blo 463784 700439 := bstep (se 1 (by rfl) ⟨525329, by rfl⟩ : syracuseStep 700439 = 1050659) B1050659
theorem B700505 : Blo 463784 700505 := bstep (se 2 (by rfl) ⟨262689, by rfl⟩ : syracuseStep 700505 = 525379) B525379
theorem B700619 : Blo 463784 700619 := bstep (se 1 (by rfl) ⟨525464, by rfl⟩ : syracuseStep 700619 = 1050929) B1050929
theorem B700631 : Blo 463784 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B10170629 : Blo 463784 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B700697 : Blo 463784 700697 := bstep (se 2 (by rfl) ⟨262761, by rfl⟩ : syracuseStep 700697 = 525523) B525523
theorem B700811 : Blo 463784 700811 := bstep (se 1 (by rfl) ⟨525608, by rfl⟩ : syracuseStep 700811 = 1051217) B1051217
theorem B1814929 : Blo 463784 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B995735 : Blo 463784 995735 := bstep (se 1 (by rfl) ⟨746801, by rfl⟩ : syracuseStep 995735 = 1493603) B1493603
theorem B700823 : Blo 463784 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B471467 : Blo 463784 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B1487297 : Blo 463784 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B700889 : Blo 463784 700889 := bstep (se 2 (by rfl) ⟨262833, by rfl⟩ : syracuseStep 700889 = 525667) B525667
theorem B995905 : Blo 463784 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B701003 : Blo 463784 701003 := bstep (se 1 (by rfl) ⟨525752, by rfl⟩ : syracuseStep 701003 = 1051505) B1051505
theorem B701015 : Blo 463784 701015 := bstep (se 1 (by rfl) ⟨525761, by rfl⟩ : syracuseStep 701015 = 1051523) B1051523
theorem B701081 : Blo 463784 701081 := bstep (se 2 (by rfl) ⟨262905, by rfl⟩ : syracuseStep 701081 = 525811) B525811
theorem B701195 : Blo 463784 701195 := bstep (se 1 (by rfl) ⟨525896, by rfl⟩ : syracuseStep 701195 = 1051793) B1051793
theorem B701207 : Blo 463784 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B701273 : Blo 463784 701273 := bstep (se 2 (by rfl) ⟨262977, by rfl⟩ : syracuseStep 701273 = 525955) B525955
theorem B996247 : Blo 463784 996247 := bstep (se 1 (by rfl) ⟨747185, by rfl⟩ : syracuseStep 996247 = 1494371) B1494371
theorem B1684397 : Blo 463784 1684397 := bstep (se 3 (by rfl) ⟨315824, by rfl⟩ : syracuseStep 1684397 = 631649) B631649
theorem B1323955 : Blo 463784 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B701387 : Blo 463784 701387 := bstep (se 1 (by rfl) ⟨526040, by rfl⟩ : syracuseStep 701387 = 1052081) B1052081
theorem B701399 : Blo 463784 701399 := bstep (se 1 (by rfl) ⟨526049, by rfl⟩ : syracuseStep 701399 = 1052099) B1052099
theorem B701465 : Blo 463784 701465 := bstep (se 2 (by rfl) ⟨263049, by rfl⟩ : syracuseStep 701465 = 526099) B526099
theorem B701579 : Blo 463784 701579 := bstep (se 1 (by rfl) ⟨526184, by rfl⟩ : syracuseStep 701579 = 1052369) B1052369
theorem B1324183 : Blo 463784 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B701591 : Blo 463784 701591 := bstep (se 1 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 701591 = 1052387) B1052387
theorem B701657 : Blo 463784 701657 := bstep (se 2 (by rfl) ⟨263121, by rfl⟩ : syracuseStep 701657 = 526243) B526243
theorem B1259059 : Blo 463784 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B3356225 : Blo 463784 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B5289623 : Blo 463784 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B34059973 : Blo 463784 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B997067 : Blo 463784 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B3979043 : Blo 463784 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B2996099 : Blo 463784 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B3356567 : Blo 463784 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B997427 : Blo 463784 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B899545 : Blo 463784 899545 := bstep (se 2 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 899545 = 674659) B674659
theorem B3979793 : Blo 463784 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B1489757 : Blo 463784 1489757 := bstep (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) B558659
theorem B1326041 : Blo 463784 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B1326871 : Blo 463784 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B2080657 : Blo 463784 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B3063703 : Blo 463784 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B8044505 : Blo 463784 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B1327691 : Blo 463784 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B5653313 : Blo 463784 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B2245441 : Blo 463784 2245441 := bstep (se 2 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 2245441 = 1684081) B1684081
theorem B4309937 : Blo 463784 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B836887 : Blo 463784 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B3982769 : Blo 463784 3982769 := bstep (se 2 (by rfl) ⟨1493538, by rfl⟩ : syracuseStep 3982769 = 2987077) B2987077
theorem B1590749 : Blo 463784 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B2148113 : Blo 463784 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B1066775 : Blo 463784 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B1984429 : Blo 463784 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B51136433 : Blo 463784 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B837643 : Blo 463784 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B1984601 : Blo 463784 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B3229789 : Blo 463784 3229789 := bstep (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) B1211171
theorem B3524957 : Blo 463784 3524957 := bstep (se 3 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 3524957 = 1321859) B1321859
theorem B477719 : Blo 463784 477719 := bstep (se 1 (by rfl) ⟨358289, by rfl⟩ : syracuseStep 477719 = 716579) B716579
theorem B838451 : Blo 463784 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B1330141 : Blo 463784 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B8473841 : Blo 463784 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B839027 : Blo 463784 839027 := bstep (se 1 (by rfl) ⟨629270, by rfl⟩ : syracuseStep 839027 = 1258541) B1258541
theorem B3362309 : Blo 463784 3362309 := bstep (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) B630433
theorem B1986241 : Blo 463784 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B3821347 : Blo 463784 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B839575 : Blo 463784 839575 := bstep (se 1 (by rfl) ⟨629681, by rfl⟩ : syracuseStep 839575 = 1259363) B1259363
theorem B10047557 : Blo 463784 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B1331417 : Blo 463784 1331417 := bstep (se 2 (by rfl) ⟨499281, by rfl⟩ : syracuseStep 1331417 = 998563) B998563
theorem B1495385 : Blo 463784 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B1364441 : Blo 463784 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B1495703 : Blo 463784 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B24171317 : Blo 463784 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B1496011 : Blo 463784 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B2642989 : Blo 463784 2642989 := bstep (se 3 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 2642989 = 991121) B991121
theorem B1987915 : Blo 463784 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B1496627 : Blo 463784 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B1988189 : Blo 463784 1988189 := bstep (se 3 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 1988189 = 745571) B745571
theorem B2348675 : Blo 463784 2348675 := bstep (se 1 (by rfl) ⟨1761506, by rfl⟩ : syracuseStep 2348675 = 3523013) B3523013
theorem B2971723 : Blo 463784 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B1595467 : Blo 463784 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B907699 : Blo 463784 907699 := bstep (se 1 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 907699 = 1361549) B1361549
theorem B842329 : Blo 463784 842329 := bstep (se 2 (by rfl) ⟨315873, by rfl⟩ : syracuseStep 842329 = 631747) B631747
theorem B2972339 : Blo 463784 2972339 := bstep (se 1 (by rfl) ⟨2229254, by rfl⟩ : syracuseStep 2972339 = 4458509) B4458509
theorem B1596125 : Blo 463784 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B940979 : Blo 463784 940979 := bstep (se 1 (by rfl) ⟨705734, by rfl⟩ : syracuseStep 940979 = 1411469) B1411469
theorem B842827 : Blo 463784 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B7560323 : Blo 463784 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B1761203 : Blo 463784 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B3366947 : Blo 463784 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B4481345 : Blo 463784 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B2220419 : Blo 463784 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B1761857 : Blo 463784 1761857 := bstep (se 2 (by rfl) ⟨660696, by rfl⟩ : syracuseStep 1761857 = 1321393) B1321393
theorem B1565405 : Blo 463784 1565405 := bstep (se 3 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 1565405 = 587027) B587027
theorem B746263 : Blo 463784 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B8971073 : Blo 463784 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B1893635 : Blo 463784 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B2352401 : Blo 463784 2352401 := bstep (se 2 (by rfl) ⟨882150, by rfl⟩ : syracuseStep 2352401 = 1764301) B1764301
theorem B2352563 : Blo 463784 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B1009217 : Blo 463784 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B747083 : Blo 463784 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B1763117 : Blo 463784 1763117 := bstep (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) B661169
theorem B1566539 : Blo 463784 1566539 := bstep (se 1 (by rfl) ⟨1174904, by rfl⟩ : syracuseStep 1566539 = 2349809) B2349809
theorem B1763147 : Blo 463784 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B2516953 : Blo 463784 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B1566809 : Blo 463784 1566809 := bstep (se 2 (by rfl) ⟨587553, by rfl⟩ : syracuseStep 1566809 = 1175107) B1175107
theorem B1993025 : Blo 463784 1993025 := bstep (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) B1494769
theorem B2845003 : Blo 463784 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B747929 : Blo 463784 747929 := bstep (se 2 (by rfl) ⟨280473, by rfl⟩ : syracuseStep 747929 = 560947) B560947
theorem B1763801 : Blo 463784 1763801 := bstep (se 2 (by rfl) ⟨661425, by rfl⟩ : syracuseStep 1763801 = 1322851) B1322851
theorem B5302745 : Blo 463784 5302745 := bstep (se 2 (by rfl) ⟨1988529, by rfl⟩ : syracuseStep 5302745 = 3977059) B3977059
theorem B1993177 : Blo 463784 1993177 := bstep (se 2 (by rfl) ⟨747441, by rfl⟩ : syracuseStep 1993177 = 1494883) B1494883
theorem B748057 : Blo 463784 748057 := bstep (se 2 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 748057 = 561043) B561043
theorem B748121 : Blo 463784 748121 := bstep (se 2 (by rfl) ⟨280545, by rfl⟩ : syracuseStep 748121 = 561091) B561091
theorem B3992165 : Blo 463784 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B715481 : Blo 463784 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B1567511 : Blo 463784 1567511 := bstep (se 1 (by rfl) ⟨1175633, by rfl⟩ : syracuseStep 1567511 = 2351267) B2351267
theorem B1764119 : Blo 463784 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B3074861 : Blo 463784 3074861 := bstep (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) B1153073
theorem B1043531 : Blo 463784 1043531 := bstep (se 1 (by rfl) ⟨782648, by rfl⟩ : syracuseStep 1043531 = 1565297) B1565297
theorem B1043585 : Blo 463784 1043585 := bstep (se 2 (by rfl) ⟨391344, by rfl⟩ : syracuseStep 1043585 = 782689) B782689
theorem B1698995 : Blo 463784 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B1568051 : Blo 463784 1568051 := bstep (se 1 (by rfl) ⟨1176038, by rfl⟩ : syracuseStep 1568051 = 2352077) B2352077
theorem B2354507 : Blo 463784 2354507 := bstep (se 1 (by rfl) ⟨1765880, by rfl⟩ : syracuseStep 2354507 = 3531761) B3531761
theorem B1043801 : Blo 463784 1043801 := bstep (se 2 (by rfl) ⟨391425, by rfl⟩ : syracuseStep 1043801 = 782851) B782851
theorem B1043891 : Blo 463784 1043891 := bstep (se 1 (by rfl) ⟨782918, by rfl⟩ : syracuseStep 1043891 = 1565837) B1565837
theorem B1764787 : Blo 463784 1764787 := bstep (se 1 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 1764787 = 2647181) B2647181
theorem B1043927 : Blo 463784 1043927 := bstep (se 1 (by rfl) ⟨782945, by rfl⟩ : syracuseStep 1043927 = 1565891) B1565891
theorem B6712793 : Blo 463784 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B1568321 : Blo 463784 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B1044107 : Blo 463784 1044107 := bstep (se 1 (by rfl) ⟨783080, by rfl⟩ : syracuseStep 1044107 = 1566161) B1566161
theorem B1175219 : Blo 463784 1175219 := bstep (se 1 (by rfl) ⟨881414, by rfl⟩ : syracuseStep 1175219 = 1762829) B1762829
theorem B2649779 : Blo 463784 2649779 := bstep (se 1 (by rfl) ⟨1987334, by rfl⟩ : syracuseStep 2649779 = 3974669) B3974669
theorem B1044161 : Blo 463784 1044161 := bstep (se 2 (by rfl) ⟨391560, by rfl⟩ : syracuseStep 1044161 = 783121) B783121
theorem B1077121 : Blo 463784 1077121 := bstep (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) B807841
theorem B1044377 : Blo 463784 1044377 := bstep (se 2 (by rfl) ⟨391641, by rfl⟩ : syracuseStep 1044377 = 783283) B783283
theorem B1044467 : Blo 463784 1044467 := bstep (se 1 (by rfl) ⟨783350, by rfl⟩ : syracuseStep 1044467 = 1566701) B1566701
theorem B1044503 : Blo 463784 1044503 := bstep (se 1 (by rfl) ⟨783377, by rfl⟩ : syracuseStep 1044503 = 1566755) B1566755
theorem B1568861 : Blo 463784 1568861 := bstep (se 3 (by rfl) ⟨294161, by rfl⟩ : syracuseStep 1568861 = 588323) B588323
theorem B880769 : Blo 463784 880769 := bstep (se 2 (by rfl) ⟨330288, by rfl⟩ : syracuseStep 880769 = 660577) B660577
theorem B3371159 : Blo 463784 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B1044683 : Blo 463784 1044683 := bstep (se 1 (by rfl) ⟨783512, by rfl⟩ : syracuseStep 1044683 = 1567025) B1567025
theorem B1175755 : Blo 463784 1175755 := bstep (se 1 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 1175755 = 1763633) B1763633
theorem B1044737 : Blo 463784 1044737 := bstep (se 2 (by rfl) ⟨391776, by rfl⟩ : syracuseStep 1044737 = 783553) B783553
theorem B1077569 : Blo 463784 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B3371329 : Blo 463784 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B1175897 : Blo 463784 1175897 := bstep (se 2 (by rfl) ⟨440961, by rfl⟩ : syracuseStep 1175897 = 881923) B881923
theorem B782743 : Blo 463784 782743 := bstep (se 1 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 782743 = 1174115) B1174115
theorem B881111 : Blo 463784 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B1044953 : Blo 463784 1044953 := bstep (se 2 (by rfl) ⟨391857, by rfl⟩ : syracuseStep 1044953 = 783715) B783715
theorem B1045043 : Blo 463784 1045043 := bstep (se 1 (by rfl) ⟨783782, by rfl⟩ : syracuseStep 1045043 = 1567565) B1567565
theorem B1045079 : Blo 463784 1045079 := bstep (se 1 (by rfl) ⟨783809, by rfl⟩ : syracuseStep 1045079 = 1567619) B1567619
theorem B1766033 : Blo 463784 1766033 := bstep (se 2 (by rfl) ⟨662262, by rfl⟩ : syracuseStep 1766033 = 1324525) B1324525
theorem B1012403 : Blo 463784 1012403 := bstep (se 1 (by rfl) ⟨759302, by rfl⟩ : syracuseStep 1012403 = 1518605) B1518605
theorem B1045259 : Blo 463784 1045259 := bstep (se 1 (by rfl) ⟨783944, by rfl⟩ : syracuseStep 1045259 = 1567889) B1567889
theorem B1045313 : Blo 463784 1045313 := bstep (se 2 (by rfl) ⟨391992, by rfl⟩ : syracuseStep 1045313 = 783985) B783985
theorem B783371 : Blo 463784 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B1045529 : Blo 463784 1045529 := bstep (se 2 (by rfl) ⟨392073, by rfl⟩ : syracuseStep 1045529 = 784147) B784147
theorem B2356289 : Blo 463784 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B3175499 : Blo 463784 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B2651237 : Blo 463784 2651237 := bstep (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) B497107
theorem B881779 : Blo 463784 881779 := bstep (se 1 (by rfl) ⟨661334, by rfl⟩ : syracuseStep 881779 = 1322669) B1322669
theorem B1045619 : Blo 463784 1045619 := bstep (se 1 (by rfl) ⟨784214, by rfl⟩ : syracuseStep 1045619 = 1568429) B1568429
theorem B783499 : Blo 463784 783499 := bstep (se 1 (by rfl) ⟨587624, by rfl⟩ : syracuseStep 783499 = 1175249) B1175249
theorem B1045655 : Blo 463784 1045655 := bstep (se 1 (by rfl) ⟨784241, by rfl⟩ : syracuseStep 1045655 = 1568483) B1568483
theorem B1176727 : Blo 463784 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B1569995 : Blo 463784 1569995 := bstep (se 1 (by rfl) ⟨1177496, by rfl⟩ : syracuseStep 1569995 = 2354993) B2354993
theorem B3994829 : Blo 463784 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B947467 : Blo 463784 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B783641 : Blo 463784 783641 := bstep (se 2 (by rfl) ⟨293865, by rfl⟩ : syracuseStep 783641 = 587731) B587731
theorem B587083 : Blo 463784 587083 := bstep (se 1 (by rfl) ⟨440312, by rfl⟩ : syracuseStep 587083 = 880625) B880625
theorem B1045835 : Blo 463784 1045835 := bstep (se 1 (by rfl) ⟨784376, by rfl⟩ : syracuseStep 1045835 = 1568753) B1568753
theorem B1766731 : Blo 463784 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B1045889 : Blo 463784 1045889 := bstep (se 2 (by rfl) ⟨392208, by rfl⟩ : syracuseStep 1045889 = 784417) B784417
theorem B783769 : Blo 463784 783769 := bstep (se 2 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 783769 = 587827) B587827
theorem B1570265 : Blo 463784 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B2160145 : Blo 463784 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B882227 : Blo 463784 882227 := bstep (se 1 (by rfl) ⟨661670, by rfl⟩ : syracuseStep 882227 = 1323341) B1323341
theorem B1177163 : Blo 463784 1177163 := bstep (se 1 (by rfl) ⟨882872, by rfl⟩ : syracuseStep 1177163 = 1765745) B1765745
theorem B521815 : Blo 463784 521815 := bstep (se 1 (by rfl) ⟨391361, by rfl⟩ : syracuseStep 521815 = 782723) B782723
theorem B587351 : Blo 463784 587351 := bstep (se 1 (by rfl) ⟨440513, by rfl⟩ : syracuseStep 587351 = 881027) B881027
theorem B882265 : Blo 463784 882265 := bstep (se 2 (by rfl) ⟨330849, by rfl⟩ : syracuseStep 882265 = 661699) B661699
theorem B1046105 : Blo 463784 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B1767005 : Blo 463784 1767005 := bstep (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) B662627
theorem B1046195 : Blo 463784 1046195 := bstep (se 1 (by rfl) ⟨784646, by rfl⟩ : syracuseStep 1046195 = 1569293) B1569293
theorem B1046231 : Blo 463784 1046231 := bstep (se 1 (by rfl) ⟨784673, by rfl⟩ : syracuseStep 1046231 = 1569347) B1569347
theorem B947927 : Blo 463784 947927 := bstep (se 1 (by rfl) ⟨710945, by rfl⟩ : syracuseStep 947927 = 1421891) B1421891
theorem B521995 : Blo 463784 521995 := bstep (se 1 (by rfl) ⟨391496, by rfl⟩ : syracuseStep 521995 = 782993) B782993
theorem B1996595 : Blo 463784 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B522103 : Blo 463784 522103 := bstep (se 1 (by rfl) ⟨391577, by rfl⟩ : syracuseStep 522103 = 783155) B783155
theorem B1046411 : Blo 463784 1046411 := bstep (se 1 (by rfl) ⟨784808, by rfl⟩ : syracuseStep 1046411 = 1569617) B1569617
theorem B1046465 : Blo 463784 1046465 := bstep (se 2 (by rfl) ⟨392424, by rfl⟩ : syracuseStep 1046465 = 784849) B784849
theorem B1177537 : Blo 463784 1177537 := bstep (se 2 (by rfl) ⟨441576, by rfl⟩ : syracuseStep 1177537 = 883153) B883153
theorem B784343 : Blo 463784 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B6387673 : Blo 463784 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B882713 : Blo 463784 882713 := bstep (se 2 (by rfl) ⟨331017, by rfl⟩ : syracuseStep 882713 = 662035) B662035
theorem B522283 : Blo 463784 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B1341515 : Blo 463784 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B784471 : Blo 463784 784471 := bstep (se 1 (by rfl) ⟨588353, by rfl⟩ : syracuseStep 784471 = 1176707) B1176707
theorem B2685059 : Blo 463784 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1800323 : Blo 463784 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B522391 : Blo 463784 522391 := bstep (se 1 (by rfl) ⟨391793, by rfl⟩ : syracuseStep 522391 = 783587) B783587
theorem B1570967 : Blo 463784 1570967 := bstep (se 1 (by rfl) ⟨1178225, by rfl⟩ : syracuseStep 1570967 = 2356451) B2356451
theorem B1046681 : Blo 463784 1046681 := bstep (se 2 (by rfl) ⟨392505, by rfl⟩ : syracuseStep 1046681 = 785011) B785011
theorem B2586775 : Blo 463784 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B1046771 : Blo 463784 1046771 := bstep (se 1 (by rfl) ⟨785078, by rfl⟩ : syracuseStep 1046771 = 1570157) B1570157
theorem B588055 : Blo 463784 588055 := bstep (se 1 (by rfl) ⟨441041, by rfl⟩ : syracuseStep 588055 = 882083) B882083
theorem B1046807 : Blo 463784 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B1767703 : Blo 463784 1767703 := bstep (se 1 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 1767703 = 2651555) B2651555
theorem B522571 : Blo 463784 522571 := bstep (se 1 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 522571 = 783857) B783857
theorem B522679 : Blo 463784 522679 := bstep (se 1 (by rfl) ⟨392009, by rfl⟩ : syracuseStep 522679 = 784019) B784019
theorem B1046987 : Blo 463784 1046987 := bstep (se 1 (by rfl) ⟨785240, by rfl⟩ : syracuseStep 1046987 = 1570481) B1570481
theorem B2980313 : Blo 463784 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B1047041 : Blo 463784 1047041 := bstep (se 2 (by rfl) ⟨392640, by rfl⟩ : syracuseStep 1047041 = 785281) B785281
theorem B1178135 : Blo 463784 1178135 := bstep (se 1 (by rfl) ⟨883601, by rfl⟩ : syracuseStep 1178135 = 1767203) B1767203
theorem B522859 : Blo 463784 522859 := bstep (se 1 (by rfl) ⟨392144, by rfl⟩ : syracuseStep 522859 = 784289) B784289
theorem B1571507 : Blo 463784 1571507 := bstep (se 1 (by rfl) ⟨1178630, by rfl⟩ : syracuseStep 1571507 = 2357261) B2357261
theorem B785099 : Blo 463784 785099 := bstep (se 1 (by rfl) ⟨588824, by rfl⟩ : syracuseStep 785099 = 1177649) B1177649
theorem B522967 : Blo 463784 522967 := bstep (se 1 (by rfl) ⟨392225, by rfl⟩ : syracuseStep 522967 = 784451) B784451
theorem B1047257 : Blo 463784 1047257 := bstep (se 2 (by rfl) ⟨392721, by rfl⟩ : syracuseStep 1047257 = 785443) B785443
theorem B7568113 : Blo 463784 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B883457 : Blo 463784 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B3767057 : Blo 463784 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B1047347 : Blo 463784 1047347 := bstep (se 1 (by rfl) ⟨785510, by rfl⟩ : syracuseStep 1047347 = 1571021) B1571021
theorem B785227 : Blo 463784 785227 := bstep (se 1 (by rfl) ⟨588920, by rfl⟩ : syracuseStep 785227 = 1177841) B1177841
theorem B1047383 : Blo 463784 1047383 := bstep (se 1 (by rfl) ⟨785537, by rfl⟩ : syracuseStep 1047383 = 1571075) B1571075
theorem B523147 : Blo 463784 523147 := bstep (se 1 (by rfl) ⟨392360, by rfl⟩ : syracuseStep 523147 = 784721) B784721
theorem B1571777 : Blo 463784 1571777 := bstep (se 2 (by rfl) ⟨589416, by rfl⟩ : syracuseStep 1571777 = 1178833) B1178833
theorem B785369 : Blo 463784 785369 := bstep (se 2 (by rfl) ⟨294513, by rfl⟩ : syracuseStep 785369 = 589027) B589027
theorem B2358233 : Blo 463784 2358233 := bstep (se 2 (by rfl) ⟨884337, by rfl⟩ : syracuseStep 2358233 = 1768675) B1768675
theorem B523255 : Blo 463784 523255 := bstep (se 1 (by rfl) ⟨392441, by rfl⟩ : syracuseStep 523255 = 784883) B784883
theorem B883723 : Blo 463784 883723 := bstep (se 1 (by rfl) ⟨662792, by rfl⟩ : syracuseStep 883723 = 1325585) B1325585
theorem B1047563 : Blo 463784 1047563 := bstep (se 1 (by rfl) ⟨785672, by rfl⟩ : syracuseStep 1047563 = 1571345) B1571345
theorem B1768493 : Blo 463784 1768493 := bstep (se 3 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 1768493 = 663185) B663185
theorem B1047617 : Blo 463784 1047617 := bstep (se 2 (by rfl) ⟨392856, by rfl⟩ : syracuseStep 1047617 = 785713) B785713
theorem B785497 : Blo 463784 785497 := bstep (se 2 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 785497 = 589123) B589123
theorem B523435 : Blo 463784 523435 := bstep (se 1 (by rfl) ⟨392576, by rfl⟩ : syracuseStep 523435 = 785153) B785153
theorem B523543 : Blo 463784 523543 := bstep (se 1 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 523543 = 785315) B785315
theorem B1047833 : Blo 463784 1047833 := bstep (se 2 (by rfl) ⟨392937, by rfl⟩ : syracuseStep 1047833 = 785875) B785875
theorem B2424109 : Blo 463784 2424109 := bstep (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) B909041
theorem B1178945 : Blo 463784 1178945 := bstep (se 2 (by rfl) ⟨442104, by rfl⟩ : syracuseStep 1178945 = 884209) B884209
theorem B2522443 : Blo 463784 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B1047923 : Blo 463784 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B1047959 : Blo 463784 1047959 := bstep (se 1 (by rfl) ⟨785969, by rfl⟩ : syracuseStep 1047959 = 1571939) B1571939
theorem B523723 : Blo 463784 523723 := bstep (se 1 (by rfl) ⟨392792, by rfl⟩ : syracuseStep 523723 = 785585) B785585
theorem B884171 : Blo 463784 884171 := bstep (se 1 (by rfl) ⟨663128, by rfl⟩ : syracuseStep 884171 = 1326257) B1326257
theorem B1572317 : Blo 463784 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B523831 : Blo 463784 523831 := bstep (se 1 (by rfl) ⟨392873, by rfl⟩ : syracuseStep 523831 = 785747) B785747
theorem B1048139 : Blo 463784 1048139 := bstep (se 1 (by rfl) ⟨786104, by rfl⟩ : syracuseStep 1048139 = 1572209) B1572209
theorem B884353 : Blo 463784 884353 := bstep (se 2 (by rfl) ⟨331632, by rfl⟩ : syracuseStep 884353 = 663265) B663265
theorem B1048193 : Blo 463784 1048193 := bstep (se 2 (by rfl) ⟨393072, by rfl⟩ : syracuseStep 1048193 = 786145) B786145
theorem B786071 : Blo 463784 786071 := bstep (se 1 (by rfl) ⟨589553, by rfl⟩ : syracuseStep 786071 = 1179107) B1179107
theorem B524011 : Blo 463784 524011 := bstep (se 1 (by rfl) ⟨393008, by rfl⟩ : syracuseStep 524011 = 786017) B786017
theorem B786199 : Blo 463784 786199 := bstep (se 1 (by rfl) ⟨589649, by rfl⟩ : syracuseStep 786199 = 1179299) B1179299
theorem B524119 : Blo 463784 524119 := bstep (se 1 (by rfl) ⟨393089, by rfl⟩ : syracuseStep 524119 = 786179) B786179
theorem B1048409 : Blo 463784 1048409 := bstep (se 2 (by rfl) ⟨393153, by rfl⟩ : syracuseStep 1048409 = 786307) B786307
theorem B1179481 : Blo 463784 1179481 := bstep (se 2 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 1179481 = 884611) B884611
theorem B1048499 : Blo 463784 1048499 := bstep (se 1 (by rfl) ⟨786374, by rfl⟩ : syracuseStep 1048499 = 1572749) B1572749
theorem B589771 : Blo 463784 589771 := bstep (se 1 (by rfl) ⟨442328, by rfl⟩ : syracuseStep 589771 = 884657) B884657
theorem B884695 : Blo 463784 884695 := bstep (se 1 (by rfl) ⟨663521, by rfl⟩ : syracuseStep 884695 = 1327043) B1327043
theorem B1048535 : Blo 463784 1048535 := bstep (se 1 (by rfl) ⟨786401, by rfl⟩ : syracuseStep 1048535 = 1572803) B1572803
theorem B8978525 : Blo 463784 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B589943 : Blo 463784 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B524551 : Blo 463784 524551 := bstep (se 1 (by rfl) ⟨393413, by rfl⟩ : syracuseStep 524551 = 786827) B786827
theorem B590095 : Blo 463784 590095 := bstep (se 1 (by rfl) ⟨442571, by rfl⟩ : syracuseStep 590095 = 885143) B885143
theorem B1179947 : Blo 463784 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B1573235 : Blo 463784 1573235 := bstep (se 1 (by rfl) ⟨1179926, by rfl⟩ : syracuseStep 1573235 = 2359853) B2359853
theorem B1048967 : Blo 463784 1048967 := bstep (se 1 (by rfl) ⟨786725, by rfl⟩ : syracuseStep 1048967 = 1573451) B1573451
theorem B590267 : Blo 463784 590267 := bstep (se 1 (by rfl) ⟨442700, by rfl⟩ : syracuseStep 590267 = 885401) B885401
theorem B524731 : Blo 463784 524731 := bstep (se 1 (by rfl) ⟨393548, by rfl⟩ : syracuseStep 524731 = 787097) B787097
theorem B1114667 : Blo 463784 1114667 := bstep (se 1 (by rfl) ⟨836000, by rfl⟩ : syracuseStep 1114667 = 1672001) B1672001
theorem B3768875 : Blo 463784 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B1049147 : Blo 463784 1049147 := bstep (se 1 (by rfl) ⟨786860, by rfl⟩ : syracuseStep 1049147 = 1573721) B1573721
theorem B787063 : Blo 463784 787063 := bstep (se 1 (by rfl) ⟨590297, by rfl⟩ : syracuseStep 787063 = 1180595) B1180595
theorem B1049273 : Blo 463784 1049273 := bstep (se 2 (by rfl) ⟨393477, by rfl⟩ : syracuseStep 1049273 = 786955) B786955
theorem B787259 : Blo 463784 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B525199 : Blo 463784 525199 := bstep (se 1 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 525199 = 787799) B787799
theorem B2655179 : Blo 463784 2655179 := bstep (se 1 (by rfl) ⟨1991384, by rfl⟩ : syracuseStep 2655179 = 3982769) B3982769
theorem B1049615 : Blo 463784 1049615 := bstep (se 1 (by rfl) ⟨787211, by rfl⟩ : syracuseStep 1049615 = 1574423) B1574423
theorem B1049633 : Blo 463784 1049633 := bstep (se 2 (by rfl) ⟨393612, by rfl⟩ : syracuseStep 1049633 = 787225) B787225
theorem B787657 : Blo 463784 787657 := bstep (se 2 (by rfl) ⟨295371, by rfl⟩ : syracuseStep 787657 = 590743) B590743
theorem B1180939 : Blo 463784 1180939 := bstep (se 1 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 1180939 = 1771409) B1771409
theorem B1049975 : Blo 463784 1049975 := bstep (se 1 (by rfl) ⟨787481, by rfl⟩ : syracuseStep 1049975 = 1574963) B1574963
theorem B591239 : Blo 463784 591239 := bstep (se 1 (by rfl) ⟨443429, by rfl⟩ : syracuseStep 591239 = 886859) B886859
theorem B525703 : Blo 463784 525703 := bstep (se 1 (by rfl) ⟨394277, by rfl⟩ : syracuseStep 525703 = 788555) B788555
theorem B1181081 : Blo 463784 1181081 := bstep (se 2 (by rfl) ⟨442905, by rfl⟩ : syracuseStep 1181081 = 885811) B885811
theorem B3540509 : Blo 463784 3540509 := bstep (se 3 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 3540509 = 1327691) B1327691
theorem B1050155 : Blo 463784 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B1181243 : Blo 463784 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B525883 : Blo 463784 525883 := bstep (se 1 (by rfl) ⟨394412, by rfl⟩ : syracuseStep 525883 = 788825) B788825
theorem B886457 : Blo 463784 886457 := bstep (se 2 (by rfl) ⟨332421, by rfl⟩ : syracuseStep 886457 = 664843) B664843
theorem B1115849 : Blo 463784 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B1771379 : Blo 463784 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B558967 : Blo 463784 558967 := bstep (se 1 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 558967 = 838451) B838451
theorem B788359 : Blo 463784 788359 := bstep (se 1 (by rfl) ⟨591269, by rfl⟩ : syracuseStep 788359 = 1182539) B1182539
theorem B1181587 : Blo 463784 1181587 := bstep (se 1 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 1181587 = 1772381) B1772381
theorem B1050515 : Blo 463784 1050515 := bstep (se 1 (by rfl) ⟨787886, by rfl⟩ : syracuseStep 1050515 = 1575773) B1575773
theorem B1050569 : Blo 463784 1050569 := bstep (se 2 (by rfl) ⟨393963, by rfl⟩ : syracuseStep 1050569 = 787927) B787927
theorem B591887 : Blo 463784 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B1181729 : Blo 463784 1181729 := bstep (se 2 (by rfl) ⟨443148, by rfl⟩ : syracuseStep 1181729 = 886297) B886297
theorem B559351 : Blo 463784 559351 := bstep (se 1 (by rfl) ⟨419513, by rfl⟩ : syracuseStep 559351 = 839027) B839027
theorem B789007 : Blo 463784 789007 := bstep (se 1 (by rfl) ⟨591755, by rfl⟩ : syracuseStep 789007 = 1183511) B1183511
theorem B6687299 : Blo 463784 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B1051271 : Blo 463784 1051271 := bstep (se 1 (by rfl) ⟨788453, by rfl⟩ : syracuseStep 1051271 = 1576907) B1576907
theorem B1116857 : Blo 463784 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B1051451 : Blo 463784 1051451 := bstep (se 1 (by rfl) ⟨788588, by rfl⟩ : syracuseStep 1051451 = 1577177) B1577177
theorem B887611 : Blo 463784 887611 := bstep (se 1 (by rfl) ⟨665708, by rfl⟩ : syracuseStep 887611 = 1331417) B1331417
theorem B4787059 : Blo 463784 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B1575827 : Blo 463784 1575827 := bstep (se 1 (by rfl) ⟨1181870, by rfl⟩ : syracuseStep 1575827 = 2363741) B2363741
theorem B1051577 : Blo 463784 1051577 := bstep (se 2 (by rfl) ⟨394341, by rfl⟩ : syracuseStep 1051577 = 788683) B788683
theorem B1182721 : Blo 463784 1182721 := bstep (se 2 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 1182721 = 887041) B887041
theorem B5311493 : Blo 463784 5311493 := bstep (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) B995905
theorem B1051919 : Blo 463784 1051919 := bstep (se 1 (by rfl) ⟨788939, by rfl⟩ : syracuseStep 1051919 = 1577879) B1577879
theorem B2657569 : Blo 463784 2657569 := bstep (se 2 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 2657569 = 1993177) B1993177
theorem B1051937 : Blo 463784 1051937 := bstep (se 2 (by rfl) ⟨394476, by rfl⟩ : syracuseStep 1051937 = 788953) B788953
theorem B2362769 : Blo 463784 2362769 := bstep (se 2 (by rfl) ⟨886038, by rfl⟩ : syracuseStep 2362769 = 1772077) B1772077
theorem B2985437 : Blo 463784 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B1183319 : Blo 463784 1183319 := bstep (se 1 (by rfl) ⟨887489, by rfl⟩ : syracuseStep 1183319 = 1774979) B1774979
theorem B1052279 : Blo 463784 1052279 := bstep (se 1 (by rfl) ⟨789209, by rfl⟩ : syracuseStep 1052279 = 1578419) B1578419
theorem B14946049 : Blo 463784 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B1183531 : Blo 463784 1183531 := bstep (se 1 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 1183531 = 1775297) B1775297
theorem B1052459 : Blo 463784 1052459 := bstep (se 1 (by rfl) ⟨789344, by rfl⟩ : syracuseStep 1052459 = 1578689) B1578689
theorem B1183673 : Blo 463784 1183673 := bstep (se 2 (by rfl) ⟨443877, by rfl⟩ : syracuseStep 1183673 = 887755) B887755
theorem B1773521 : Blo 463784 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B7737367 : Blo 463784 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B2691245 : Blo 463784 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B1773839 : Blo 463784 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B1577231 : Blo 463784 1577231 := bstep (se 1 (by rfl) ⟨1182923, by rfl⟩ : syracuseStep 1577231 = 2365847) B2365847
theorem B2658845 : Blo 463784 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B1577501 : Blo 463784 1577501 := bstep (se 3 (by rfl) ⟨295781, by rfl⟩ : syracuseStep 1577501 = 591563) B591563
theorem B2036267 : Blo 463784 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B2527805 : Blo 463784 2527805 := bstep (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) B947927
theorem B627319 : Blo 463784 627319 := bstep (se 1 (by rfl) ⟨470489, by rfl⟩ : syracuseStep 627319 = 940979) B940979
theorem B14554037 : Blo 463784 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B463803 : Blo 463784 463803 := bstep (se 1 (by rfl) ⟨347852, by rfl⟩ : syracuseStep 463803 = 695705) B695705
theorem B463879 : Blo 463784 463879 := bstep (se 1 (by rfl) ⟨347909, by rfl⟩ : syracuseStep 463879 = 695819) B695819
theorem B463887 : Blo 463784 463887 := bstep (se 1 (by rfl) ⟨347915, by rfl⟩ : syracuseStep 463887 = 695831) B695831
theorem B463931 : Blo 463784 463931 := bstep (se 1 (by rfl) ⟨347948, by rfl⟩ : syracuseStep 463931 = 695897) B695897
theorem B464007 : Blo 463784 464007 := bstep (se 1 (by rfl) ⟨348005, by rfl⟩ : syracuseStep 464007 = 696011) B696011
theorem B464015 : Blo 463784 464015 := bstep (se 1 (by rfl) ⟨348011, by rfl⟩ : syracuseStep 464015 = 696023) B696023
theorem B464059 : Blo 463784 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B1119433 : Blo 463784 1119433 := bstep (se 2 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 1119433 = 839575) B839575
theorem B2233601 : Blo 463784 2233601 := bstep (se 2 (by rfl) ⟨837600, by rfl⟩ : syracuseStep 2233601 = 1675201) B1675201
theorem B464135 : Blo 463784 464135 := bstep (se 1 (by rfl) ⟨348101, by rfl⟩ : syracuseStep 464135 = 696203) B696203
theorem B464143 : Blo 463784 464143 := bstep (se 1 (by rfl) ⟨348107, by rfl⟩ : syracuseStep 464143 = 696215) B696215
theorem B660793 : Blo 463784 660793 := bstep (se 2 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 660793 = 495595) B495595
theorem B464187 : Blo 463784 464187 := bstep (se 1 (by rfl) ⟨348140, by rfl⟩ : syracuseStep 464187 = 696281) B696281
theorem B464263 : Blo 463784 464263 := bstep (se 1 (by rfl) ⟨348197, by rfl⟩ : syracuseStep 464263 = 696395) B696395
theorem B464271 : Blo 463784 464271 := bstep (se 1 (by rfl) ⟨348203, by rfl⟩ : syracuseStep 464271 = 696407) B696407
theorem B660907 : Blo 463784 660907 := bstep (se 1 (by rfl) ⟨495680, by rfl⟩ : syracuseStep 660907 = 991361) B991361
theorem B464315 : Blo 463784 464315 := bstep (se 1 (by rfl) ⟨348236, by rfl⟩ : syracuseStep 464315 = 696473) B696473
theorem B2364875 : Blo 463784 2364875 := bstep (se 1 (by rfl) ⟨1773656, by rfl⟩ : syracuseStep 2364875 = 3547313) B3547313
theorem B464391 : Blo 463784 464391 := bstep (se 1 (by rfl) ⟨348293, by rfl⟩ : syracuseStep 464391 = 696587) B696587
theorem B464399 : Blo 463784 464399 := bstep (se 1 (by rfl) ⟨348299, by rfl⟩ : syracuseStep 464399 = 696599) B696599
theorem B2987563 : Blo 463784 2987563 := bstep (se 1 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 2987563 = 4481345) B4481345
theorem B464443 : Blo 463784 464443 := bstep (se 1 (by rfl) ⟨348332, by rfl⟩ : syracuseStep 464443 = 696665) B696665
theorem B1480279 : Blo 463784 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B4462199 : Blo 463784 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B464519 : Blo 463784 464519 := bstep (se 1 (by rfl) ⟨348389, by rfl⟩ : syracuseStep 464519 = 696779) B696779
theorem B661135 : Blo 463784 661135 := bstep (se 1 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 661135 = 991703) B991703
theorem B464527 : Blo 463784 464527 := bstep (se 1 (by rfl) ⟨348395, by rfl⟩ : syracuseStep 464527 = 696791) B696791
theorem B464571 : Blo 463784 464571 := bstep (se 1 (by rfl) ⟨348428, by rfl⟩ : syracuseStep 464571 = 696857) B696857
theorem B4495105 : Blo 463784 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B464647 : Blo 463784 464647 := bstep (se 1 (by rfl) ⟨348485, by rfl⟩ : syracuseStep 464647 = 696971) B696971
theorem B464655 : Blo 463784 464655 := bstep (se 1 (by rfl) ⟨348491, by rfl⟩ : syracuseStep 464655 = 696983) B696983
theorem B2365199 : Blo 463784 2365199 := bstep (se 1 (by rfl) ⟨1773899, by rfl⟩ : syracuseStep 2365199 = 3547799) B3547799
theorem B3544883 : Blo 463784 3544883 := bstep (se 1 (by rfl) ⟨2658662, by rfl⟩ : syracuseStep 3544883 = 5317325) B5317325
theorem B464699 : Blo 463784 464699 := bstep (se 1 (by rfl) ⟨348524, by rfl⟩ : syracuseStep 464699 = 697049) B697049
theorem B464775 : Blo 463784 464775 := bstep (se 1 (by rfl) ⟨348581, by rfl⟩ : syracuseStep 464775 = 697163) B697163
theorem B464783 : Blo 463784 464783 := bstep (se 1 (by rfl) ⟨348587, by rfl⟩ : syracuseStep 464783 = 697175) B697175
theorem B464827 : Blo 463784 464827 := bstep (se 1 (by rfl) ⟨348620, by rfl⟩ : syracuseStep 464827 = 697241) B697241
theorem B464903 : Blo 463784 464903 := bstep (se 1 (by rfl) ⟨348677, by rfl⟩ : syracuseStep 464903 = 697355) B697355
theorem B464911 : Blo 463784 464911 := bstep (se 1 (by rfl) ⟨348683, by rfl⟩ : syracuseStep 464911 = 697367) B697367
theorem B464955 : Blo 463784 464955 := bstep (se 1 (by rfl) ⟨348716, by rfl⟩ : syracuseStep 464955 = 697433) B697433
theorem B465031 : Blo 463784 465031 := bstep (se 1 (by rfl) ⟨348773, by rfl⟩ : syracuseStep 465031 = 697547) B697547
theorem B465039 : Blo 463784 465039 := bstep (se 1 (by rfl) ⟨348779, by rfl⟩ : syracuseStep 465039 = 697559) B697559
theorem B465083 : Blo 463784 465083 := bstep (se 1 (by rfl) ⟨348812, by rfl⟩ : syracuseStep 465083 = 697625) B697625
theorem B465159 : Blo 463784 465159 := bstep (se 1 (by rfl) ⟨348869, by rfl⟩ : syracuseStep 465159 = 697739) B697739
theorem B465167 : Blo 463784 465167 := bstep (se 1 (by rfl) ⟨348875, by rfl⟩ : syracuseStep 465167 = 697751) B697751
theorem B465211 : Blo 463784 465211 := bstep (se 1 (by rfl) ⟨348908, by rfl⟩ : syracuseStep 465211 = 697817) B697817
theorem B465287 : Blo 463784 465287 := bstep (se 1 (by rfl) ⟨348965, by rfl⟩ : syracuseStep 465287 = 697931) B697931
theorem B465295 : Blo 463784 465295 := bstep (se 1 (by rfl) ⟨348971, by rfl⟩ : syracuseStep 465295 = 697943) B697943
theorem B465339 : Blo 463784 465339 := bstep (se 1 (by rfl) ⟨349004, by rfl⟩ : syracuseStep 465339 = 698009) B698009
theorem B662023 : Blo 463784 662023 := bstep (se 1 (by rfl) ⟨496517, by rfl⟩ : syracuseStep 662023 = 993035) B993035
theorem B465415 : Blo 463784 465415 := bstep (se 1 (by rfl) ⟨349061, by rfl⟩ : syracuseStep 465415 = 698123) B698123
theorem B465423 : Blo 463784 465423 := bstep (se 1 (by rfl) ⟨349067, by rfl⟩ : syracuseStep 465423 = 698135) B698135
theorem B465467 : Blo 463784 465467 := bstep (se 1 (by rfl) ⟨349100, by rfl⟩ : syracuseStep 465467 = 698201) B698201
theorem B465543 : Blo 463784 465543 := bstep (se 1 (by rfl) ⟨349157, by rfl⟩ : syracuseStep 465543 = 698315) B698315
theorem B465551 : Blo 463784 465551 := bstep (se 1 (by rfl) ⟨349163, by rfl⟩ : syracuseStep 465551 = 698327) B698327
theorem B465595 : Blo 463784 465595 := bstep (se 1 (by rfl) ⟨349196, by rfl⟩ : syracuseStep 465595 = 698393) B698393
theorem B465671 : Blo 463784 465671 := bstep (se 1 (by rfl) ⟨349253, by rfl⟩ : syracuseStep 465671 = 698507) B698507
theorem B465679 : Blo 463784 465679 := bstep (se 1 (by rfl) ⟨349259, by rfl⟩ : syracuseStep 465679 = 698519) B698519
theorem B465723 : Blo 463784 465723 := bstep (se 1 (by rfl) ⟨349292, by rfl⟩ : syracuseStep 465723 = 698585) B698585
theorem B2235251 : Blo 463784 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B465799 : Blo 463784 465799 := bstep (se 1 (by rfl) ⟨349349, by rfl⟩ : syracuseStep 465799 = 698699) B698699
theorem B465807 : Blo 463784 465807 := bstep (se 1 (by rfl) ⟨349355, by rfl⟩ : syracuseStep 465807 = 698711) B698711
theorem B465851 : Blo 463784 465851 := bstep (se 1 (by rfl) ⟨349388, by rfl⟩ : syracuseStep 465851 = 698777) B698777
theorem B498619 : Blo 463784 498619 := bstep (se 1 (by rfl) ⟨373964, by rfl⟩ : syracuseStep 498619 = 747929) B747929
theorem B662519 : Blo 463784 662519 := bstep (se 1 (by rfl) ⟨496889, by rfl⟩ : syracuseStep 662519 = 993779) B993779
theorem B465927 : Blo 463784 465927 := bstep (se 1 (by rfl) ⟨349445, by rfl⟩ : syracuseStep 465927 = 698891) B698891
theorem B465935 : Blo 463784 465935 := bstep (se 1 (by rfl) ⟨349451, by rfl⟩ : syracuseStep 465935 = 698903) B698903
theorem B793643 : Blo 463784 793643 := bstep (se 1 (by rfl) ⟨595232, by rfl⟩ : syracuseStep 793643 = 1190465) B1190465
theorem B465979 : Blo 463784 465979 := bstep (se 1 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 465979 = 698969) B698969
theorem B2661443 : Blo 463784 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B466055 : Blo 463784 466055 := bstep (se 1 (by rfl) ⟨349541, by rfl⟩ : syracuseStep 466055 = 699083) B699083
theorem B466063 : Blo 463784 466063 := bstep (se 1 (by rfl) ⟨349547, by rfl⟩ : syracuseStep 466063 = 699095) B699095
theorem B466107 : Blo 463784 466107 := bstep (se 1 (by rfl) ⟨349580, by rfl⟩ : syracuseStep 466107 = 699161) B699161
theorem B2366657 : Blo 463784 2366657 := bstep (se 2 (by rfl) ⟨887496, by rfl⟩ : syracuseStep 2366657 = 1774993) B1774993
theorem B466183 : Blo 463784 466183 := bstep (se 1 (by rfl) ⟨349637, by rfl⟩ : syracuseStep 466183 = 699275) B699275
theorem B466191 : Blo 463784 466191 := bstep (se 1 (by rfl) ⟨349643, by rfl⟩ : syracuseStep 466191 = 699287) B699287
theorem B466235 : Blo 463784 466235 := bstep (se 1 (by rfl) ⟨349676, by rfl⟩ : syracuseStep 466235 = 699353) B699353
theorem B695687 : Blo 463784 695687 := bstep (se 1 (by rfl) ⟨521765, by rfl⟩ : syracuseStep 695687 = 1043531) B1043531
theorem B466311 : Blo 463784 466311 := bstep (se 1 (by rfl) ⟨349733, by rfl⟩ : syracuseStep 466311 = 699467) B699467
theorem B466319 : Blo 463784 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B1678745 : Blo 463784 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B695723 : Blo 463784 695723 := bstep (se 1 (by rfl) ⟨521792, by rfl⟩ : syracuseStep 695723 = 1043585) B1043585
theorem B466363 : Blo 463784 466363 := bstep (se 1 (by rfl) ⟨349772, by rfl⟩ : syracuseStep 466363 = 699545) B699545
theorem B695753 : Blo 463784 695753 := bstep (se 2 (by rfl) ⟨260907, by rfl⟩ : syracuseStep 695753 = 521815) B521815
theorem B466439 : Blo 463784 466439 := bstep (se 1 (by rfl) ⟨349829, by rfl⟩ : syracuseStep 466439 = 699659) B699659
theorem B466447 : Blo 463784 466447 := bstep (se 1 (by rfl) ⟨349835, by rfl⟩ : syracuseStep 466447 = 699671) B699671
theorem B695867 : Blo 463784 695867 := bstep (se 1 (by rfl) ⟨521900, by rfl⟩ : syracuseStep 695867 = 1043801) B1043801
theorem B466491 : Blo 463784 466491 := bstep (se 1 (by rfl) ⟨349868, by rfl⟩ : syracuseStep 466491 = 699737) B699737
theorem B2039357 : Blo 463784 2039357 := bstep (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) B764759
theorem B3972685 : Blo 463784 3972685 := bstep (se 3 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 3972685 = 1489757) B1489757
theorem B695927 : Blo 463784 695927 := bstep (se 1 (by rfl) ⟨521945, by rfl⟩ : syracuseStep 695927 = 1043891) B1043891
theorem B466567 : Blo 463784 466567 := bstep (se 1 (by rfl) ⟨349925, by rfl⟩ : syracuseStep 466567 = 699851) B699851
theorem B695951 : Blo 463784 695951 := bstep (se 1 (by rfl) ⟨521963, by rfl⟩ : syracuseStep 695951 = 1043927) B1043927
theorem B466575 : Blo 463784 466575 := bstep (se 1 (by rfl) ⟨349931, by rfl⟩ : syracuseStep 466575 = 699863) B699863
theorem B695993 : Blo 463784 695993 := bstep (se 2 (by rfl) ⟨260997, by rfl⟩ : syracuseStep 695993 = 521995) B521995
theorem B466619 : Blo 463784 466619 := bstep (se 1 (by rfl) ⟨349964, by rfl⟩ : syracuseStep 466619 = 699929) B699929
theorem B696071 : Blo 463784 696071 := bstep (se 1 (by rfl) ⟨522053, by rfl⟩ : syracuseStep 696071 = 1044107) B1044107
theorem B466695 : Blo 463784 466695 := bstep (se 1 (by rfl) ⟨350021, by rfl⟩ : syracuseStep 466695 = 700043) B700043
theorem B466703 : Blo 463784 466703 := bstep (se 1 (by rfl) ⟨350027, by rfl⟩ : syracuseStep 466703 = 700055) B700055
theorem B696107 : Blo 463784 696107 := bstep (se 1 (by rfl) ⟨522080, by rfl⟩ : syracuseStep 696107 = 1044161) B1044161
theorem B466747 : Blo 463784 466747 := bstep (se 1 (by rfl) ⟨350060, by rfl⟩ : syracuseStep 466747 = 700121) B700121
theorem B696137 : Blo 463784 696137 := bstep (se 2 (by rfl) ⟨261051, by rfl⟩ : syracuseStep 696137 = 522103) B522103
theorem B466823 : Blo 463784 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B466831 : Blo 463784 466831 := bstep (se 1 (by rfl) ⟨350123, by rfl⟩ : syracuseStep 466831 = 700247) B700247
theorem B597931 : Blo 463784 597931 := bstep (se 1 (by rfl) ⟨448448, by rfl⟩ : syracuseStep 597931 = 896897) B896897
theorem B663481 : Blo 463784 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B696251 : Blo 463784 696251 := bstep (se 1 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 696251 = 1044377) B1044377
theorem B466875 : Blo 463784 466875 := bstep (se 1 (by rfl) ⟨350156, by rfl⟩ : syracuseStep 466875 = 700313) B700313
theorem B696311 : Blo 463784 696311 := bstep (se 1 (by rfl) ⟨522233, by rfl⟩ : syracuseStep 696311 = 1044467) B1044467
theorem B466951 : Blo 463784 466951 := bstep (se 1 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 466951 = 700427) B700427
theorem B696335 : Blo 463784 696335 := bstep (se 1 (by rfl) ⟨522251, by rfl⟩ : syracuseStep 696335 = 1044503) B1044503
theorem B466959 : Blo 463784 466959 := bstep (se 1 (by rfl) ⟨350219, by rfl⟩ : syracuseStep 466959 = 700439) B700439
theorem B696377 : Blo 463784 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B467003 : Blo 463784 467003 := bstep (se 1 (by rfl) ⟨350252, by rfl⟩ : syracuseStep 467003 = 700505) B700505
theorem B696455 : Blo 463784 696455 := bstep (se 1 (by rfl) ⟨522341, by rfl⟩ : syracuseStep 696455 = 1044683) B1044683
theorem B467079 : Blo 463784 467079 := bstep (se 1 (by rfl) ⟨350309, by rfl⟩ : syracuseStep 467079 = 700619) B700619
theorem B467087 : Blo 463784 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B696491 : Blo 463784 696491 := bstep (se 1 (by rfl) ⟨522368, by rfl⟩ : syracuseStep 696491 = 1044737) B1044737
theorem B467131 : Blo 463784 467131 := bstep (se 1 (by rfl) ⟨350348, by rfl⟩ : syracuseStep 467131 = 700697) B700697
theorem B696521 : Blo 463784 696521 := bstep (se 2 (by rfl) ⟨261195, by rfl⟩ : syracuseStep 696521 = 522391) B522391
theorem B3449033 : Blo 463784 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B467207 : Blo 463784 467207 := bstep (se 1 (by rfl) ⟨350405, by rfl⟩ : syracuseStep 467207 = 700811) B700811
theorem B663823 : Blo 463784 663823 := bstep (se 1 (by rfl) ⟨497867, by rfl⟩ : syracuseStep 663823 = 995735) B995735
theorem B467215 : Blo 463784 467215 := bstep (se 1 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 467215 = 700823) B700823
theorem B991531 : Blo 463784 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B696635 : Blo 463784 696635 := bstep (se 1 (by rfl) ⟨522476, by rfl⟩ : syracuseStep 696635 = 1044953) B1044953
theorem B467259 : Blo 463784 467259 := bstep (se 1 (by rfl) ⟨350444, by rfl⟩ : syracuseStep 467259 = 700889) B700889
theorem B696695 : Blo 463784 696695 := bstep (se 1 (by rfl) ⟨522521, by rfl⟩ : syracuseStep 696695 = 1045043) B1045043
theorem B467335 : Blo 463784 467335 := bstep (se 1 (by rfl) ⟨350501, by rfl⟩ : syracuseStep 467335 = 701003) B701003
theorem B696719 : Blo 463784 696719 := bstep (se 1 (by rfl) ⟨522539, by rfl⟩ : syracuseStep 696719 = 1045079) B1045079
theorem B467343 : Blo 463784 467343 := bstep (se 1 (by rfl) ⟨350507, by rfl⟩ : syracuseStep 467343 = 701015) B701015
theorem B696761 : Blo 463784 696761 := bstep (se 2 (by rfl) ⟨261285, by rfl⟩ : syracuseStep 696761 = 522571) B522571
theorem B467387 : Blo 463784 467387 := bstep (se 1 (by rfl) ⟨350540, by rfl⟩ : syracuseStep 467387 = 701081) B701081
theorem B2367953 : Blo 463784 2367953 := bstep (se 2 (by rfl) ⟨887982, by rfl⟩ : syracuseStep 2367953 = 1775965) B1775965
theorem B696839 : Blo 463784 696839 := bstep (se 1 (by rfl) ⟨522629, by rfl⟩ : syracuseStep 696839 = 1045259) B1045259
theorem B467463 : Blo 463784 467463 := bstep (se 1 (by rfl) ⟨350597, by rfl⟩ : syracuseStep 467463 = 701195) B701195
theorem B467471 : Blo 463784 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B696875 : Blo 463784 696875 := bstep (se 1 (by rfl) ⟨522656, by rfl⟩ : syracuseStep 696875 = 1045313) B1045313
theorem B467515 : Blo 463784 467515 := bstep (se 1 (by rfl) ⟨350636, by rfl⟩ : syracuseStep 467515 = 701273) B701273
theorem B696905 : Blo 463784 696905 := bstep (se 2 (by rfl) ⟨261339, by rfl⟩ : syracuseStep 696905 = 522679) B522679
theorem B1122931 : Blo 463784 1122931 := bstep (se 1 (by rfl) ⟨842198, by rfl⟩ : syracuseStep 1122931 = 1684397) B1684397
theorem B467591 : Blo 463784 467591 := bstep (se 1 (by rfl) ⟨350693, by rfl⟩ : syracuseStep 467591 = 701387) B701387
theorem B467599 : Blo 463784 467599 := bstep (se 1 (by rfl) ⟨350699, by rfl⟩ : syracuseStep 467599 = 701399) B701399
theorem B697019 : Blo 463784 697019 := bstep (se 1 (by rfl) ⟨522764, by rfl⟩ : syracuseStep 697019 = 1045529) B1045529
theorem B467643 : Blo 463784 467643 := bstep (se 1 (by rfl) ⟨350732, by rfl⟩ : syracuseStep 467643 = 701465) B701465
theorem B697079 : Blo 463784 697079 := bstep (se 1 (by rfl) ⟨522809, by rfl⟩ : syracuseStep 697079 = 1045619) B1045619
theorem B467719 : Blo 463784 467719 := bstep (se 1 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 467719 = 701579) B701579
theorem B697103 : Blo 463784 697103 := bstep (se 1 (by rfl) ⟨522827, by rfl⟩ : syracuseStep 697103 = 1045655) B1045655
theorem B467727 : Blo 463784 467727 := bstep (se 1 (by rfl) ⟨350795, by rfl⟩ : syracuseStep 467727 = 701591) B701591
theorem B1123105 : Blo 463784 1123105 := bstep (se 2 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 1123105 = 842329) B842329
theorem B2663219 : Blo 463784 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B697145 : Blo 463784 697145 := bstep (se 2 (by rfl) ⟨261429, by rfl⟩ : syracuseStep 697145 = 522859) B522859
theorem B467771 : Blo 463784 467771 := bstep (se 1 (by rfl) ⟨350828, by rfl⟩ : syracuseStep 467771 = 701657) B701657
theorem B697223 : Blo 463784 697223 := bstep (se 1 (by rfl) ⟨522917, by rfl⟩ : syracuseStep 697223 = 1045835) B1045835
theorem B697259 : Blo 463784 697259 := bstep (se 1 (by rfl) ⟨522944, by rfl⟩ : syracuseStep 697259 = 1045889) B1045889
theorem B697289 : Blo 463784 697289 := bstep (se 2 (by rfl) ⟨261483, by rfl⟩ : syracuseStep 697289 = 522967) B522967
theorem B2237483 : Blo 463784 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B697403 : Blo 463784 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B697463 : Blo 463784 697463 := bstep (se 1 (by rfl) ⟨523097, by rfl⟩ : syracuseStep 697463 = 1046195) B1046195
theorem B697487 : Blo 463784 697487 := bstep (se 1 (by rfl) ⟨523115, by rfl⟩ : syracuseStep 697487 = 1046231) B1046231
theorem B697529 : Blo 463784 697529 := bstep (se 2 (by rfl) ⟨261573, by rfl⟩ : syracuseStep 697529 = 523147) B523147
theorem B697607 : Blo 463784 697607 := bstep (se 1 (by rfl) ⟨523205, by rfl⟩ : syracuseStep 697607 = 1046411) B1046411
theorem B2237711 : Blo 463784 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B697643 : Blo 463784 697643 := bstep (se 1 (by rfl) ⟨523232, by rfl⟩ : syracuseStep 697643 = 1046465) B1046465
theorem B697673 : Blo 463784 697673 := bstep (se 2 (by rfl) ⟨261627, by rfl⟩ : syracuseStep 697673 = 523255) B523255
theorem B664951 : Blo 463784 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B894343 : Blo 463784 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B1123769 : Blo 463784 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B697787 : Blo 463784 697787 := bstep (se 1 (by rfl) ⟨523340, by rfl⟩ : syracuseStep 697787 = 1046681) B1046681
theorem B697847 : Blo 463784 697847 := bstep (se 1 (by rfl) ⟨523385, by rfl⟩ : syracuseStep 697847 = 1046771) B1046771
theorem B697871 : Blo 463784 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B697913 : Blo 463784 697913 := bstep (se 2 (by rfl) ⟨261717, by rfl⟩ : syracuseStep 697913 = 523435) B523435
theorem B697991 : Blo 463784 697991 := bstep (se 1 (by rfl) ⟨523493, by rfl⟩ : syracuseStep 697991 = 1046987) B1046987
theorem B698027 : Blo 463784 698027 := bstep (se 1 (by rfl) ⟨523520, by rfl⟩ : syracuseStep 698027 = 1047041) B1047041
theorem B698057 : Blo 463784 698057 := bstep (se 2 (by rfl) ⟨261771, by rfl⟩ : syracuseStep 698057 = 523543) B523543
theorem B698171 : Blo 463784 698171 := bstep (se 1 (by rfl) ⟨523628, by rfl⟩ : syracuseStep 698171 = 1047257) B1047257
theorem B698231 : Blo 463784 698231 := bstep (se 1 (by rfl) ⟨523673, by rfl⟩ : syracuseStep 698231 = 1047347) B1047347
theorem B698255 : Blo 463784 698255 := bstep (se 1 (by rfl) ⟨523691, by rfl⟩ : syracuseStep 698255 = 1047383) B1047383
theorem B1320857 : Blo 463784 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B698297 : Blo 463784 698297 := bstep (se 2 (by rfl) ⟨261861, by rfl⟩ : syracuseStep 698297 = 523723) B523723
theorem B698375 : Blo 463784 698375 := bstep (se 1 (by rfl) ⟨523781, by rfl⟩ : syracuseStep 698375 = 1047563) B1047563
theorem B698411 : Blo 463784 698411 := bstep (se 1 (by rfl) ⟨523808, by rfl⟩ : syracuseStep 698411 = 1047617) B1047617
theorem B698441 : Blo 463784 698441 := bstep (se 2 (by rfl) ⟨261915, by rfl⟩ : syracuseStep 698441 = 523831) B523831
theorem B698555 : Blo 463784 698555 := bstep (se 1 (by rfl) ⟨523916, by rfl⟩ : syracuseStep 698555 = 1047833) B1047833
theorem B698615 : Blo 463784 698615 := bstep (se 1 (by rfl) ⟨523961, by rfl⟩ : syracuseStep 698615 = 1047923) B1047923
theorem B698639 : Blo 463784 698639 := bstep (se 1 (by rfl) ⟨523979, by rfl⟩ : syracuseStep 698639 = 1047959) B1047959
theorem B698681 : Blo 463784 698681 := bstep (se 2 (by rfl) ⟨262005, by rfl⟩ : syracuseStep 698681 = 524011) B524011
theorem B698759 : Blo 463784 698759 := bstep (se 1 (by rfl) ⟨524069, by rfl⟩ : syracuseStep 698759 = 1048139) B1048139
theorem B698795 : Blo 463784 698795 := bstep (se 1 (by rfl) ⟨524096, by rfl⟩ : syracuseStep 698795 = 1048193) B1048193
theorem B698825 : Blo 463784 698825 := bstep (se 2 (by rfl) ⟨262059, by rfl⟩ : syracuseStep 698825 = 524119) B524119
theorem B698939 : Blo 463784 698939 := bstep (se 1 (by rfl) ⟨524204, by rfl⟩ : syracuseStep 698939 = 1048409) B1048409
theorem B698999 : Blo 463784 698999 := bstep (se 1 (by rfl) ⟨524249, by rfl⟩ : syracuseStep 698999 = 1048499) B1048499
theorem B699023 : Blo 463784 699023 := bstep (se 1 (by rfl) ⟨524267, by rfl⟩ : syracuseStep 699023 = 1048535) B1048535
theorem B699065 : Blo 463784 699065 := bstep (se 2 (by rfl) ⟨262149, by rfl⟩ : syracuseStep 699065 = 524299) B524299
theorem B699143 : Blo 463784 699143 := bstep (se 1 (by rfl) ⟨524357, by rfl⟩ : syracuseStep 699143 = 1048715) B1048715
theorem B699179 : Blo 463784 699179 := bstep (se 1 (by rfl) ⟨524384, by rfl⟩ : syracuseStep 699179 = 1048769) B1048769
theorem B5286707 : Blo 463784 5286707 := bstep (se 1 (by rfl) ⟨3965030, by rfl⟩ : syracuseStep 5286707 = 7930061) B7930061
theorem B699209 : Blo 463784 699209 := bstep (se 2 (by rfl) ⟨262203, by rfl⟩ : syracuseStep 699209 = 524407) B524407
theorem B699323 : Blo 463784 699323 := bstep (se 1 (by rfl) ⟨524492, by rfl⟩ : syracuseStep 699323 = 1048985) B1048985
theorem B699383 : Blo 463784 699383 := bstep (se 1 (by rfl) ⟨524537, by rfl⟩ : syracuseStep 699383 = 1049075) B1049075
theorem B699407 : Blo 463784 699407 := bstep (se 1 (by rfl) ⟨524555, by rfl⟩ : syracuseStep 699407 = 1049111) B1049111
theorem B699449 : Blo 463784 699449 := bstep (se 2 (by rfl) ⟨262293, by rfl⟩ : syracuseStep 699449 = 524587) B524587
theorem B699527 : Blo 463784 699527 := bstep (se 1 (by rfl) ⟨524645, by rfl⟩ : syracuseStep 699527 = 1049291) B1049291
theorem B699563 : Blo 463784 699563 := bstep (se 1 (by rfl) ⟨524672, by rfl⟩ : syracuseStep 699563 = 1049345) B1049345
theorem B699593 : Blo 463784 699593 := bstep (se 2 (by rfl) ⟨262347, by rfl⟩ : syracuseStep 699593 = 524695) B524695
theorem B699707 : Blo 463784 699707 := bstep (se 1 (by rfl) ⟨524780, by rfl⟩ : syracuseStep 699707 = 1049561) B1049561
theorem B699767 : Blo 463784 699767 := bstep (se 1 (by rfl) ⟨524825, by rfl⟩ : syracuseStep 699767 = 1049651) B1049651
theorem B699791 : Blo 463784 699791 := bstep (se 1 (by rfl) ⟨524843, by rfl⟩ : syracuseStep 699791 = 1049687) B1049687
theorem B699833 : Blo 463784 699833 := bstep (se 2 (by rfl) ⟨262437, by rfl⟩ : syracuseStep 699833 = 524875) B524875
theorem B1322497 : Blo 463784 1322497 := bstep (se 2 (by rfl) ⟨495936, by rfl⟩ : syracuseStep 1322497 = 991873) B991873
theorem B699911 : Blo 463784 699911 := bstep (se 1 (by rfl) ⟨524933, by rfl⟩ : syracuseStep 699911 = 1049867) B1049867
theorem B1420811 : Blo 463784 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B699947 : Blo 463784 699947 := bstep (se 1 (by rfl) ⟨524960, by rfl⟩ : syracuseStep 699947 = 1049921) B1049921
theorem B699977 : Blo 463784 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B1420919 : Blo 463784 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B1060499 : Blo 463784 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B700091 : Blo 463784 700091 := bstep (se 1 (by rfl) ⟨525068, by rfl⟩ : syracuseStep 700091 = 1050137) B1050137
theorem B995017 : Blo 463784 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B700151 : Blo 463784 700151 := bstep (se 1 (by rfl) ⟨525113, by rfl⟩ : syracuseStep 700151 = 1050227) B1050227
theorem B2993921 : Blo 463784 2993921 := bstep (se 2 (by rfl) ⟨1122720, by rfl⟩ : syracuseStep 2993921 = 2245441) B2245441
theorem B700175 : Blo 463784 700175 := bstep (se 1 (by rfl) ⟨525131, by rfl⟩ : syracuseStep 700175 = 1050263) B1050263
theorem B1257245 : Blo 463784 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B700217 : Blo 463784 700217 := bstep (se 2 (by rfl) ⟨262581, by rfl⟩ : syracuseStep 700217 = 525163) B525163
theorem B700295 : Blo 463784 700295 := bstep (se 1 (by rfl) ⟨525221, by rfl⟩ : syracuseStep 700295 = 1050443) B1050443
theorem B700331 : Blo 463784 700331 := bstep (se 1 (by rfl) ⟨525248, by rfl⟩ : syracuseStep 700331 = 1050497) B1050497
theorem B700361 : Blo 463784 700361 := bstep (se 2 (by rfl) ⟨262635, by rfl⟩ : syracuseStep 700361 = 525271) B525271
theorem B34090955 : Blo 463784 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B1323067 : Blo 463784 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B700475 : Blo 463784 700475 := bstep (se 1 (by rfl) ⟨525356, by rfl⟩ : syracuseStep 700475 = 1050713) B1050713
theorem B700535 : Blo 463784 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B700559 : Blo 463784 700559 := bstep (se 1 (by rfl) ⟨525419, by rfl⟩ : syracuseStep 700559 = 1050839) B1050839
theorem B700601 : Blo 463784 700601 := bstep (se 2 (by rfl) ⟨262725, by rfl⟩ : syracuseStep 700601 = 525451) B525451
theorem B700679 : Blo 463784 700679 := bstep (se 1 (by rfl) ⟨525509, by rfl⟩ : syracuseStep 700679 = 1051019) B1051019
theorem B1487119 : Blo 463784 1487119 := bstep (se 1 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 1487119 = 2230679) B2230679
theorem B700715 : Blo 463784 700715 := bstep (se 1 (by rfl) ⟨525536, by rfl⟩ : syracuseStep 700715 = 1051073) B1051073
theorem B700745 : Blo 463784 700745 := bstep (se 2 (by rfl) ⟨262779, by rfl⟩ : syracuseStep 700745 = 525559) B525559
theorem B700859 : Blo 463784 700859 := bstep (se 1 (by rfl) ⟨525644, by rfl⟩ : syracuseStep 700859 = 1051289) B1051289
theorem B2699741 : Blo 463784 2699741 := bstep (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) B1012403
theorem B700919 : Blo 463784 700919 := bstep (se 1 (by rfl) ⟨525689, by rfl⟩ : syracuseStep 700919 = 1051379) B1051379
theorem B700943 : Blo 463784 700943 := bstep (se 1 (by rfl) ⟨525707, by rfl⟩ : syracuseStep 700943 = 1051415) B1051415
theorem B700985 : Blo 463784 700985 := bstep (se 2 (by rfl) ⟨262869, by rfl⟩ : syracuseStep 700985 = 525739) B525739
theorem B701063 : Blo 463784 701063 := bstep (se 1 (by rfl) ⟨525797, by rfl⟩ : syracuseStep 701063 = 1051595) B1051595
theorem B701099 : Blo 463784 701099 := bstep (se 1 (by rfl) ⟨525824, by rfl⟩ : syracuseStep 701099 = 1051649) B1051649
theorem B701129 : Blo 463784 701129 := bstep (se 2 (by rfl) ⟨262923, by rfl⟩ : syracuseStep 701129 = 525847) B525847
theorem B9679621 : Blo 463784 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B2994995 : Blo 463784 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B701243 : Blo 463784 701243 := bstep (se 1 (by rfl) ⟨525932, by rfl⟩ : syracuseStep 701243 = 1051865) B1051865
theorem B5649227 : Blo 463784 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B701303 : Blo 463784 701303 := bstep (se 1 (by rfl) ⟨525977, by rfl⟩ : syracuseStep 701303 = 1051955) B1051955
theorem B701327 : Blo 463784 701327 := bstep (se 1 (by rfl) ⟨525995, by rfl⟩ : syracuseStep 701327 = 1051991) B1051991
theorem B701369 : Blo 463784 701369 := bstep (se 2 (by rfl) ⟨263013, by rfl⟩ : syracuseStep 701369 = 526027) B526027
theorem B2241539 : Blo 463784 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B701447 : Blo 463784 701447 := bstep (se 1 (by rfl) ⟨526085, by rfl⟩ : syracuseStep 701447 = 1052171) B1052171
theorem B701483 : Blo 463784 701483 := bstep (se 1 (by rfl) ⟨526112, by rfl⟩ : syracuseStep 701483 = 1052225) B1052225
theorem B701513 : Blo 463784 701513 := bstep (se 2 (by rfl) ⟨263067, by rfl⟩ : syracuseStep 701513 = 526135) B526135
theorem B701627 : Blo 463784 701627 := bstep (se 1 (by rfl) ⟨526220, by rfl⟩ : syracuseStep 701627 = 1052441) B1052441
theorem B3355937 : Blo 463784 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B6698371 : Blo 463784 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B4306385 : Blo 463784 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B996923 : Blo 463784 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B4470349 : Blo 463784 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B2012759 : Blo 463784 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B3356453 : Blo 463784 3356453 := bstep (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) B629335
theorem B997409 : Blo 463784 997409 := bstep (se 2 (by rfl) ⟨374028, by rfl⟩ : syracuseStep 997409 = 748057) B748057
theorem B1063201 : Blo 463784 1063201 := bstep (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) B797401
theorem B997751 : Blo 463784 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B1325459 : Blo 463784 1325459 := bstep (se 1 (by rfl) ⟨994094, by rfl⟩ : syracuseStep 1325459 = 1988189) B1988189
theorem B1489337 : Blo 463784 1489337 := bstep (se 2 (by rfl) ⟨558501, by rfl⟩ : syracuseStep 1489337 = 1117003) B1117003
theorem B5356211 : Blo 463784 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B5389145 : Blo 463784 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B3587159 : Blo 463784 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B1981559 : Blo 463784 1981559 := bstep (se 1 (by rfl) ⟨1486169, by rfl⟩ : syracuseStep 1981559 = 2972339) B2972339
theorem B1064083 : Blo 463784 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B1326233 : Blo 463784 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B4898333 : Blo 463784 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B2277209 : Blo 463784 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B8503319 : Blo 463784 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B5095669 : Blo 463784 5095669 := bstep (se 5 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 5095669 = 477719) B477719
theorem B1491347 : Blo 463784 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B5980715 : Blo 463784 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B1262423 : Blo 463784 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B705655 : Blo 463784 705655 := bstep (se 1 (by rfl) ⟨529241, by rfl⟩ : syracuseStep 705655 = 1058483) B1058483
theorem B1328329 : Blo 463784 1328329 := bstep (se 2 (by rfl) ⟨498123, by rfl⟩ : syracuseStep 1328329 = 996247) B996247
theorem B3523985 : Blo 463784 3523985 := bstep (se 2 (by rfl) ⟨1321494, by rfl⟩ : syracuseStep 3523985 = 2642989) B2642989
theorem B1230281 : Blo 463784 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B1328683 : Blo 463784 1328683 := bstep (se 1 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 1328683 = 1993025) B1993025
theorem B10929815 : Blo 463784 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B1263289 : Blo 463784 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B476987 : Blo 463784 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B1328957 : Blo 463784 1328957 := bstep (se 3 (by rfl) ⟨249179, by rfl⟩ : syracuseStep 1328957 = 498359) B498359
theorem B2049907 : Blo 463784 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B1132663 : Blo 463784 1132663 := bstep (se 1 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 1132663 = 1698995) B1698995
theorem B4475195 : Blo 463784 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B2247439 : Blo 463784 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B2116637 : Blo 463784 2116637 := bstep (se 3 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 2116637 = 793739) B793739
theorem B1494217 : Blo 463784 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B1199393 : Blo 463784 1199393 := bstep (se 2 (by rfl) ⟨449772, by rfl⟩ : syracuseStep 1199393 = 899545) B899545
theorem B2116999 : Blo 463784 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B3526415 : Blo 463784 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B8933165 : Blo 463784 8933165 := bstep (se 3 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 8933165 = 3349937) B3349937
theorem B1331063 : Blo 463784 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B1790039 : Blo 463784 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1200215 : Blo 463784 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B1986875 : Blo 463784 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B3232145 : Blo 463784 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B709049 : Blo 463784 709049 := bstep (se 2 (by rfl) ⟨265893, by rfl⟩ : syracuseStep 709049 = 531787) B531787
theorem B3363257 : Blo 463784 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B2511371 : Blo 463784 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B2774209 : Blo 463784 2774209 := bstep (se 2 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 2774209 = 2080657) B2080657
theorem B4084937 : Blo 463784 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B5363003 : Blo 463784 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B8509157 : Blo 463784 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B743303 : Blo 463784 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B2873291 : Blo 463784 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B1988651 : Blo 463784 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B87447605 : Blo 463784 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B1432075 : Blo 463784 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B2349971 : Blo 463784 2349971 := bstep (se 1 (by rfl) ⟨1762478, by rfl⟩ : syracuseStep 2349971 = 3524957) B3524957
theorem B3988541 : Blo 463784 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B744719 : Blo 463784 744719 := bstep (se 1 (by rfl) ⟨558539, by rfl⟩ : syracuseStep 744719 = 1117079) B1117079
theorem B2645905 : Blo 463784 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B1761689 : Blo 463784 1761689 := bstep (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) B1321267
theorem B3793337 : Blo 463784 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B16114211 : Blo 463784 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B14377817 : Blo 463784 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B1565783 : Blo 463784 1565783 := bstep (se 1 (by rfl) ⟨1174337, by rfl⟩ : syracuseStep 1565783 = 2348675) B2348675
theorem B1992221 : Blo 463784 1992221 := bstep (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) B747083
theorem B1566269 : Blo 463784 1566269 := bstep (se 3 (by rfl) ⟨293675, by rfl⟩ : syracuseStep 1566269 = 587351) B587351
theorem B8939159 : Blo 463784 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B1992563 : Blo 463784 1992563 := bstep (se 1 (by rfl) ⟨1494422, by rfl⟩ : syracuseStep 1992563 = 2988845) B2988845
theorem B2353049 : Blo 463784 2353049 := bstep (se 2 (by rfl) ⟨882393, by rfl⟩ : syracuseStep 2353049 = 1764787) B1764787
theorem B2844733 : Blo 463784 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B5040215 : Blo 463784 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B2648321 : Blo 463784 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B1436161 : Blo 463784 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B1174135 : Blo 463784 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B1567673 : Blo 463784 1567673 := bstep (se 2 (by rfl) ⟨587877, by rfl⟩ : syracuseStep 1567673 = 1175755) B1175755
theorem B1174571 : Blo 463784 1174571 := bstep (se 1 (by rfl) ⟨880928, by rfl⟩ : syracuseStep 1174571 = 1761857) B1761857
theorem B1043603 : Blo 463784 1043603 := bstep (se 1 (by rfl) ⟨782702, by rfl⟩ : syracuseStep 1043603 = 1565405) B1565405
theorem B1043657 : Blo 463784 1043657 := bstep (se 2 (by rfl) ⟨391371, by rfl⟩ : syracuseStep 1043657 = 782743) B782743
theorem B1568267 : Blo 463784 1568267 := bstep (se 1 (by rfl) ⟨1176200, by rfl⟩ : syracuseStep 1568267 = 2352401) B2352401
theorem B1568375 : Blo 463784 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B1175411 : Blo 463784 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B1044359 : Blo 463784 1044359 := bstep (se 1 (by rfl) ⟨783269, by rfl⟩ : syracuseStep 1044359 = 1566539) B1566539
theorem B1175431 : Blo 463784 1175431 := bstep (se 1 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 1175431 = 1763147) B1763147
theorem B1765273 : Blo 463784 1765273 := bstep (se 2 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 1765273 = 1323955) B1323955
theorem B1994681 : Blo 463784 1994681 := bstep (se 2 (by rfl) ⟨748005, by rfl⟩ : syracuseStep 1994681 = 1496011) B1496011
theorem B1044539 : Blo 463784 1044539 := bstep (se 1 (by rfl) ⟨783404, by rfl⟩ : syracuseStep 1044539 = 1566809) B1566809
theorem B1175705 : Blo 463784 1175705 := bstep (se 2 (by rfl) ⟨440889, by rfl⟩ : syracuseStep 1175705 = 881779) B881779
theorem B1044665 : Blo 463784 1044665 := bstep (se 2 (by rfl) ⟨391749, by rfl⟩ : syracuseStep 1044665 = 783499) B783499
theorem B1568969 : Blo 463784 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B1765577 : Blo 463784 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B1994989 : Blo 463784 1994989 := bstep (se 3 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 1994989 = 748121) B748121
theorem B1995023 : Blo 463784 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B2388275 : Blo 463784 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1175867 : Blo 463784 1175867 := bstep (se 1 (by rfl) ⟨881900, by rfl⟩ : syracuseStep 1175867 = 1763801) B1763801
theorem B3535163 : Blo 463784 3535163 := bstep (se 1 (by rfl) ⟨2651372, by rfl⟩ : syracuseStep 3535163 = 5302745) B5302745
theorem B782777 : Blo 463784 782777 := bstep (se 2 (by rfl) ⟨293541, by rfl⟩ : syracuseStep 782777 = 587083) B587083
theorem B2355641 : Blo 463784 2355641 := bstep (se 2 (by rfl) ⟨883365, by rfl⟩ : syracuseStep 2355641 = 1766731) B1766731
theorem B2650553 : Blo 463784 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B1045007 : Blo 463784 1045007 := bstep (se 1 (by rfl) ⟨783755, by rfl⟩ : syracuseStep 1045007 = 1567511) B1567511
theorem B1176079 : Blo 463784 1176079 := bstep (se 1 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 1176079 = 1764119) B1764119
theorem B1045025 : Blo 463784 1045025 := bstep (se 2 (by rfl) ⟨391884, by rfl⟩ : syracuseStep 1045025 = 783769) B783769
theorem B2880193 : Blo 463784 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B1176353 : Blo 463784 1176353 := bstep (se 2 (by rfl) ⟨441132, by rfl⟩ : syracuseStep 1176353 = 882265) B882265
theorem B1045367 : Blo 463784 1045367 := bstep (se 1 (by rfl) ⟨784025, by rfl⟩ : syracuseStep 1045367 = 1568051) B1568051
theorem B881543 : Blo 463784 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B1569671 : Blo 463784 1569671 := bstep (se 1 (by rfl) ⟨1177253, by rfl⟩ : syracuseStep 1569671 = 2354507) B2354507
theorem B45413297 : Blo 463784 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B1045547 : Blo 463784 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B783479 : Blo 463784 783479 := bstep (se 1 (by rfl) ⟨587609, by rfl⟩ : syracuseStep 783479 = 1175219) B1175219
theorem B1766519 : Blo 463784 1766519 := bstep (se 1 (by rfl) ⟨1324889, by rfl⟩ : syracuseStep 1766519 = 2649779) B2649779
theorem B1570049 : Blo 463784 1570049 := bstep (se 2 (by rfl) ⟨588768, by rfl⟩ : syracuseStep 1570049 = 1177537) B1177537
theorem B8516897 : Blo 463784 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1045907 : Blo 463784 1045907 := bstep (se 1 (by rfl) ⟨784430, by rfl⟩ : syracuseStep 1045907 = 1568861) B1568861
theorem B587179 : Blo 463784 587179 := bstep (se 1 (by rfl) ⟨440384, by rfl⟩ : syracuseStep 587179 = 880769) B880769
theorem B3962297 : Blo 463784 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B1045961 : Blo 463784 1045961 := bstep (se 2 (by rfl) ⟨392235, by rfl⟩ : syracuseStep 1045961 = 784471) B784471
theorem B6780419 : Blo 463784 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B718379 : Blo 463784 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B783931 : Blo 463784 783931 := bstep (se 1 (by rfl) ⟨587948, by rfl⟩ : syracuseStep 783931 = 1175897) B1175897
theorem B587407 : Blo 463784 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B784073 : Blo 463784 784073 := bstep (se 2 (by rfl) ⟨294027, by rfl⟩ : syracuseStep 784073 = 588055) B588055
theorem B2356937 : Blo 463784 2356937 := bstep (se 2 (by rfl) ⟨883851, by rfl⟩ : syracuseStep 2356937 = 1767703) B1767703
theorem B1177355 : Blo 463784 1177355 := bstep (se 1 (by rfl) ⟨883016, by rfl⟩ : syracuseStep 1177355 = 1766033) B1766033
theorem B4028249 : Blo 463784 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B1210265 : Blo 463784 1210265 := bstep (se 2 (by rfl) ⟨453849, by rfl⟩ : syracuseStep 1210265 = 907699) B907699
theorem B522247 : Blo 463784 522247 := bstep (se 1 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 522247 = 783371) B783371
theorem B1570859 : Blo 463784 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B1767491 : Blo 463784 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B1046663 : Blo 463784 1046663 := bstep (se 1 (by rfl) ⟨784997, by rfl⟩ : syracuseStep 1046663 = 1569995) B1569995
theorem B522427 : Blo 463784 522427 := bstep (se 1 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 522427 = 783641) B783641
theorem B1046843 : Blo 463784 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B10090817 : Blo 463784 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B588151 : Blo 463784 588151 := bstep (se 1 (by rfl) ⟨441113, by rfl⟩ : syracuseStep 588151 = 882227) B882227
theorem B784775 : Blo 463784 784775 := bstep (se 1 (by rfl) ⟨588581, by rfl⟩ : syracuseStep 784775 = 1177163) B1177163
theorem B1178003 : Blo 463784 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B1046969 : Blo 463784 1046969 := bstep (se 2 (by rfl) ⟨392613, by rfl⟩ : syracuseStep 1046969 = 785227) B785227
theorem B2652695 : Blo 463784 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B1997399 : Blo 463784 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B522895 : Blo 463784 522895 := bstep (se 1 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 522895 = 784343) B784343
theorem B1178297 : Blo 463784 1178297 := bstep (se 2 (by rfl) ⟨441861, by rfl⟩ : syracuseStep 1178297 = 883723) B883723
theorem B588475 : Blo 463784 588475 := bstep (se 1 (by rfl) ⟨441356, by rfl⟩ : syracuseStep 588475 = 882713) B882713
theorem B1047311 : Blo 463784 1047311 := bstep (se 1 (by rfl) ⟨785483, by rfl⟩ : syracuseStep 1047311 = 1570967) B1570967
theorem B1047329 : Blo 463784 1047329 := bstep (se 2 (by rfl) ⟨392748, by rfl⟩ : syracuseStep 1047329 = 785497) B785497
theorem B20380517 : Blo 463784 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B2653195 : Blo 463784 2653195 := bstep (se 1 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 2653195 = 3979793) B3979793
theorem B785423 : Blo 463784 785423 := bstep (se 1 (by rfl) ⟨589067, by rfl⟩ : syracuseStep 785423 = 1178135) B1178135
theorem B1047671 : Blo 463784 1047671 := bstep (se 1 (by rfl) ⟨785753, by rfl⟩ : syracuseStep 1047671 = 1571507) B1571507
theorem B523399 : Blo 463784 523399 := bstep (se 1 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 523399 = 785099) B785099
theorem B588971 : Blo 463784 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B1047851 : Blo 463784 1047851 := bstep (se 1 (by rfl) ⟨785888, by rfl⟩ : syracuseStep 1047851 = 1571777) B1571777
theorem B523579 : Blo 463784 523579 := bstep (se 1 (by rfl) ⟨392684, by rfl⟩ : syracuseStep 523579 = 785369) B785369
theorem B884027 : Blo 463784 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B1572155 : Blo 463784 1572155 := bstep (se 1 (by rfl) ⟨1179116, by rfl⟩ : syracuseStep 1572155 = 2358233) B2358233
theorem B1178995 : Blo 463784 1178995 := bstep (se 1 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 1178995 = 1768493) B1768493
theorem B1179137 : Blo 463784 1179137 := bstep (se 2 (by rfl) ⟨442176, by rfl⟩ : syracuseStep 1179137 = 884353) B884353
theorem B785963 : Blo 463784 785963 := bstep (se 1 (by rfl) ⟨589472, by rfl⟩ : syracuseStep 785963 = 1178945) B1178945
theorem B589447 : Blo 463784 589447 := bstep (se 1 (by rfl) ⟨442085, by rfl⟩ : syracuseStep 589447 = 884171) B884171
theorem B1048211 : Blo 463784 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B1048265 : Blo 463784 1048265 := bstep (se 2 (by rfl) ⟨393099, by rfl⟩ : syracuseStep 1048265 = 786199) B786199
theorem B1769161 : Blo 463784 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B524047 : Blo 463784 524047 := bstep (se 1 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 524047 = 786071) B786071
theorem B884513 : Blo 463784 884513 := bstep (se 2 (by rfl) ⟨331692, by rfl⟩ : syracuseStep 884513 = 663385) B663385
theorem B1572641 : Blo 463784 1572641 := bstep (se 2 (by rfl) ⟨589740, by rfl⟩ : syracuseStep 1572641 = 1179481) B1179481
theorem B786361 : Blo 463784 786361 := bstep (se 2 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 786361 = 589771) B589771
theorem B1179593 : Blo 463784 1179593 := bstep (se 2 (by rfl) ⟨442347, by rfl⟩ : syracuseStep 1179593 = 884695) B884695
theorem B5668879 : Blo 463784 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B786631 : Blo 463784 786631 := bstep (se 1 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 786631 = 1179947) B1179947
theorem B1048823 : Blo 463784 1048823 := bstep (se 1 (by rfl) ⟨786617, by rfl⟩ : syracuseStep 1048823 = 1573235) B1573235
theorem B1573181 : Blo 463784 1573181 := bstep (se 3 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 1573181 = 589943) B589943
theorem B885097 : Blo 463784 885097 := bstep (se 2 (by rfl) ⟨331911, by rfl⟩ : syracuseStep 885097 = 663823) B663823
theorem B786793 : Blo 463784 786793 := bstep (se 2 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 786793 = 590095) B590095
theorem B524839 : Blo 463784 524839 := bstep (se 1 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 524839 = 787259) B787259
theorem B932774453 : Blo 463784 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B1770119 : Blo 463784 1770119 := bstep (se 1 (by rfl) ⟨1327589, by rfl⟩ : syracuseStep 1770119 = 2655179) B2655179
theorem B1049417 : Blo 463784 1049417 := bstep (se 2 (by rfl) ⟨393531, by rfl⟩ : syracuseStep 1049417 = 787063) B787063
theorem B787387 : Blo 463784 787387 := bstep (se 1 (by rfl) ⟨590540, by rfl⟩ : syracuseStep 787387 = 1181081) B1181081
theorem B820187 : Blo 463784 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B2360339 : Blo 463784 2360339 := bstep (se 1 (by rfl) ⟨1770254, by rfl⟩ : syracuseStep 2360339 = 3540509) B3540509
theorem B787495 : Blo 463784 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B590971 : Blo 463784 590971 := bstep (se 1 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 590971 = 886457) B886457
theorem B1574045 : Blo 463784 1574045 := bstep (se 3 (by rfl) ⟨295133, by rfl⟩ : syracuseStep 1574045 = 590267) B590267
theorem B885971 : Blo 463784 885971 := bstep (se 1 (by rfl) ⟨664478, by rfl⟩ : syracuseStep 885971 = 1328957) B1328957
theorem B1180919 : Blo 463784 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B2983205 : Blo 463784 2983205 := bstep (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) B559351
theorem B787819 : Blo 463784 787819 := bstep (se 1 (by rfl) ⟨590864, by rfl⟩ : syracuseStep 787819 = 1181729) B1181729
theorem B2983463 : Blo 463784 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B1771105 : Blo 463784 1771105 := bstep (se 2 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 1771105 = 1328329) B1328329
theorem B1050209 : Blo 463784 1050209 := bstep (se 2 (by rfl) ⟨393828, by rfl⟩ : syracuseStep 1050209 = 787657) B787657
theorem B1574585 : Blo 463784 1574585 := bstep (se 2 (by rfl) ⟨590469, by rfl⟩ : syracuseStep 1574585 = 1180939) B1180939
theorem B886601 : Blo 463784 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B1050551 : Blo 463784 1050551 := bstep (se 1 (by rfl) ⟨787913, by rfl⟩ : syracuseStep 1050551 = 1575827) B1575827
theorem B3540995 : Blo 463784 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B1411091 : Blo 463784 1411091 := bstep (se 1 (by rfl) ⟨1058318, by rfl⟩ : syracuseStep 1411091 = 2116637) B2116637
theorem B1771577 : Blo 463784 1771577 := bstep (se 2 (by rfl) ⟨664341, by rfl⟩ : syracuseStep 1771577 = 1328683) B1328683
theorem B1575179 : Blo 463784 1575179 := bstep (se 1 (by rfl) ⟨1181384, by rfl⟩ : syracuseStep 1575179 = 2362769) B2362769
theorem B788879 : Blo 463784 788879 := bstep (se 1 (by rfl) ⟨591659, by rfl⟩ : syracuseStep 788879 = 1183319) B1183319
theorem B1051145 : Blo 463784 1051145 := bstep (se 2 (by rfl) ⟨394179, by rfl⟩ : syracuseStep 1051145 = 788359) B788359
theorem B1575449 : Blo 463784 1575449 := bstep (se 2 (by rfl) ⟨590793, by rfl⟩ : syracuseStep 1575449 = 1181587) B1181587
theorem B887375 : Blo 463784 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B789115 : Blo 463784 789115 := bstep (se 1 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 789115 = 1183673) B1183673
theorem B1182347 : Blo 463784 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B1510217 : Blo 463784 1510217 := bstep (se 2 (by rfl) ⟨566331, by rfl⟩ : syracuseStep 1510217 = 1132663) B1132663
theorem B1182559 : Blo 463784 1182559 := bstep (se 1 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 1182559 = 1773839) B1773839
theorem B1051487 : Blo 463784 1051487 := bstep (se 1 (by rfl) ⟨788615, by rfl⟩ : syracuseStep 1051487 = 1577231) B1577231
theorem B1772563 : Blo 463784 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B1051667 : Blo 463784 1051667 := bstep (se 1 (by rfl) ⟨788750, by rfl⟩ : syracuseStep 1051667 = 1577501) B1577501
theorem B1052009 : Blo 463784 1052009 := bstep (se 2 (by rfl) ⟨394503, by rfl⟩ : syracuseStep 1052009 = 789007) B789007
theorem B5967229 : Blo 463784 5967229 := bstep (se 3 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 5967229 = 2237711) B2237711
theorem B2723291 : Blo 463784 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B3575335 : Blo 463784 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1576583 : Blo 463784 1576583 := bstep (se 1 (by rfl) ⟨1182437, by rfl⟩ : syracuseStep 1576583 = 2364875) B2364875
theorem B1576637 : Blo 463784 1576637 := bstep (se 3 (by rfl) ⟨295619, by rfl⟩ : syracuseStep 1576637 = 591239) B591239
theorem B1183481 : Blo 463784 1183481 := bstep (se 2 (by rfl) ⟨443805, by rfl⟩ : syracuseStep 1183481 = 887611) B887611
theorem B5672771 : Blo 463784 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B1576799 : Blo 463784 1576799 := bstep (se 1 (by rfl) ⟨1182599, by rfl⟩ : syracuseStep 1576799 = 2365199) B2365199
theorem B2363255 : Blo 463784 2363255 := bstep (se 1 (by rfl) ⟨1772441, by rfl⟩ : syracuseStep 2363255 = 3544883) B3544883
theorem B1576961 : Blo 463784 1576961 := bstep (se 2 (by rfl) ⟨591360, by rfl⟩ : syracuseStep 1576961 = 1182721) B1182721
theorem B3543425 : Blo 463784 3543425 := bstep (se 2 (by rfl) ⟨1328784, by rfl⟩ : syracuseStep 3543425 = 2657569) B2657569
theorem B2659027 : Blo 463784 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B1774295 : Blo 463784 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1577771 : Blo 463784 1577771 := bstep (se 1 (by rfl) ⟨1183328, by rfl⟩ : syracuseStep 1577771 = 2366657) B2366657
theorem B463791 : Blo 463784 463791 := bstep (se 1 (by rfl) ⟨347843, by rfl⟩ : syracuseStep 463791 = 695687) B695687
theorem B463815 : Blo 463784 463815 := bstep (se 1 (by rfl) ⟨347861, by rfl⟩ : syracuseStep 463815 = 695723) B695723
theorem B463835 : Blo 463784 463835 := bstep (se 1 (by rfl) ⟨347876, by rfl⟩ : syracuseStep 463835 = 695753) B695753
theorem B2659301 : Blo 463784 2659301 := bstep (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) B498619
theorem B19928065 : Blo 463784 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B463911 : Blo 463784 463911 := bstep (se 1 (by rfl) ⟨347933, by rfl⟩ : syracuseStep 463911 = 695867) B695867
theorem B1578041 : Blo 463784 1578041 := bstep (se 2 (by rfl) ⟨591765, by rfl⟩ : syracuseStep 1578041 = 1183531) B1183531
theorem B463951 : Blo 463784 463951 := bstep (se 1 (by rfl) ⟨347963, by rfl⟩ : syracuseStep 463951 = 695927) B695927
theorem B463967 : Blo 463784 463967 := bstep (se 1 (by rfl) ⟨347975, by rfl⟩ : syracuseStep 463967 = 695951) B695951
theorem B463995 : Blo 463784 463995 := bstep (se 1 (by rfl) ⟨347996, by rfl⟩ : syracuseStep 463995 = 695993) B695993
theorem B464047 : Blo 463784 464047 := bstep (se 1 (by rfl) ⟨348035, by rfl⟩ : syracuseStep 464047 = 696071) B696071
theorem B464071 : Blo 463784 464071 := bstep (se 1 (by rfl) ⟨348053, by rfl⟩ : syracuseStep 464071 = 696107) B696107
theorem B464091 : Blo 463784 464091 := bstep (se 1 (by rfl) ⟨348068, by rfl⟩ : syracuseStep 464091 = 696137) B696137
theorem B464167 : Blo 463784 464167 := bstep (se 1 (by rfl) ⟨348125, by rfl⟩ : syracuseStep 464167 = 696251) B696251
theorem B464207 : Blo 463784 464207 := bstep (se 1 (by rfl) ⟨348155, by rfl⟩ : syracuseStep 464207 = 696311) B696311
theorem B464223 : Blo 463784 464223 := bstep (se 1 (by rfl) ⟨348167, by rfl⟩ : syracuseStep 464223 = 696335) B696335
theorem B464251 : Blo 463784 464251 := bstep (se 1 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 464251 = 696377) B696377
theorem B1578365 : Blo 463784 1578365 := bstep (se 3 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 1578365 = 591887) B591887
theorem B464303 : Blo 463784 464303 := bstep (se 1 (by rfl) ⟨348227, by rfl⟩ : syracuseStep 464303 = 696455) B696455
theorem B464327 : Blo 463784 464327 := bstep (se 1 (by rfl) ⟨348245, by rfl⟩ : syracuseStep 464327 = 696491) B696491
theorem B464347 : Blo 463784 464347 := bstep (se 1 (by rfl) ⟨348260, by rfl⟩ : syracuseStep 464347 = 696521) B696521
theorem B2299355 : Blo 463784 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B464423 : Blo 463784 464423 := bstep (se 1 (by rfl) ⟨348317, by rfl⟩ : syracuseStep 464423 = 696635) B696635
theorem B464463 : Blo 463784 464463 := bstep (se 1 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 464463 = 696695) B696695
theorem B464479 : Blo 463784 464479 := bstep (se 1 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 464479 = 696719) B696719
theorem B464507 : Blo 463784 464507 := bstep (se 1 (by rfl) ⟨348380, by rfl⟩ : syracuseStep 464507 = 696761) B696761
theorem B2528891 : Blo 463784 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B1578635 : Blo 463784 1578635 := bstep (se 1 (by rfl) ⟨1183976, by rfl⟩ : syracuseStep 1578635 = 2367953) B2367953
theorem B2659985 : Blo 463784 2659985 := bstep (se 2 (by rfl) ⟨997494, by rfl⟩ : syracuseStep 2659985 = 1994989) B1994989
theorem B464559 : Blo 463784 464559 := bstep (se 1 (by rfl) ⟨348419, by rfl⟩ : syracuseStep 464559 = 696839) B696839
theorem B464583 : Blo 463784 464583 := bstep (se 1 (by rfl) ⟨348437, by rfl⟩ : syracuseStep 464583 = 696875) B696875
theorem B464603 : Blo 463784 464603 := bstep (se 1 (by rfl) ⟨348452, by rfl⟩ : syracuseStep 464603 = 696905) B696905
theorem B464679 : Blo 463784 464679 := bstep (se 1 (by rfl) ⟨348509, by rfl⟩ : syracuseStep 464679 = 697019) B697019
theorem B464719 : Blo 463784 464719 := bstep (se 1 (by rfl) ⟨348539, by rfl⟩ : syracuseStep 464719 = 697079) B697079
theorem B464735 : Blo 463784 464735 := bstep (se 1 (by rfl) ⟨348551, by rfl⟩ : syracuseStep 464735 = 697103) B697103
theorem B1775479 : Blo 463784 1775479 := bstep (se 1 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 1775479 = 2663219) B2663219
theorem B464763 : Blo 463784 464763 := bstep (se 1 (by rfl) ⟨348572, by rfl⟩ : syracuseStep 464763 = 697145) B697145
theorem B464815 : Blo 463784 464815 := bstep (se 1 (by rfl) ⟨348611, by rfl⟩ : syracuseStep 464815 = 697223) B697223
theorem B464839 : Blo 463784 464839 := bstep (se 1 (by rfl) ⟨348629, by rfl⟩ : syracuseStep 464839 = 697259) B697259
theorem B464859 : Blo 463784 464859 := bstep (se 1 (by rfl) ⟨348644, by rfl⟩ : syracuseStep 464859 = 697289) B697289
theorem B464935 : Blo 463784 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B464975 : Blo 463784 464975 := bstep (se 1 (by rfl) ⟨348731, by rfl⟩ : syracuseStep 464975 = 697463) B697463
theorem B464991 : Blo 463784 464991 := bstep (se 1 (by rfl) ⟨348743, by rfl⟩ : syracuseStep 464991 = 697487) B697487
theorem B465019 : Blo 463784 465019 := bstep (se 1 (by rfl) ⟨348764, by rfl⟩ : syracuseStep 465019 = 697529) B697529
theorem B465071 : Blo 463784 465071 := bstep (se 1 (by rfl) ⟨348803, by rfl⟩ : syracuseStep 465071 = 697607) B697607
theorem B465095 : Blo 463784 465095 := bstep (se 1 (by rfl) ⟨348821, by rfl⟩ : syracuseStep 465095 = 697643) B697643
theorem B465115 : Blo 463784 465115 := bstep (se 1 (by rfl) ⟨348836, by rfl⟩ : syracuseStep 465115 = 697673) B697673
theorem B3840257 : Blo 463784 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B465191 : Blo 463784 465191 := bstep (se 1 (by rfl) ⟨348893, by rfl⟩ : syracuseStep 465191 = 697787) B697787
theorem B465231 : Blo 463784 465231 := bstep (se 1 (by rfl) ⟨348923, by rfl⟩ : syracuseStep 465231 = 697847) B697847
theorem B465247 : Blo 463784 465247 := bstep (se 1 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 465247 = 697871) B697871
theorem B465275 : Blo 463784 465275 := bstep (se 1 (by rfl) ⟨348956, by rfl⟩ : syracuseStep 465275 = 697913) B697913
theorem B465327 : Blo 463784 465327 := bstep (se 1 (by rfl) ⟨348995, by rfl⟩ : syracuseStep 465327 = 697991) B697991
theorem B465351 : Blo 463784 465351 := bstep (se 1 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 465351 = 698027) B698027
theorem B465371 : Blo 463784 465371 := bstep (se 1 (by rfl) ⟨349028, by rfl⟩ : syracuseStep 465371 = 698057) B698057
theorem B465447 : Blo 463784 465447 := bstep (se 1 (by rfl) ⟨349085, by rfl⟩ : syracuseStep 465447 = 698171) B698171
theorem B465487 : Blo 463784 465487 := bstep (se 1 (by rfl) ⟨349115, by rfl⟩ : syracuseStep 465487 = 698231) B698231
theorem B465503 : Blo 463784 465503 := bstep (se 1 (by rfl) ⟨349127, by rfl⟩ : syracuseStep 465503 = 698255) B698255
theorem B465531 : Blo 463784 465531 := bstep (se 1 (by rfl) ⟨349148, by rfl⟩ : syracuseStep 465531 = 698297) B698297
theorem B465583 : Blo 463784 465583 := bstep (se 1 (by rfl) ⟨349187, by rfl⟩ : syracuseStep 465583 = 698375) B698375
theorem B465607 : Blo 463784 465607 := bstep (se 1 (by rfl) ⟨349205, by rfl⟩ : syracuseStep 465607 = 698411) B698411
theorem B465627 : Blo 463784 465627 := bstep (se 1 (by rfl) ⟨349220, by rfl⟩ : syracuseStep 465627 = 698441) B698441
theorem B465703 : Blo 463784 465703 := bstep (se 1 (by rfl) ⟨349277, by rfl⟩ : syracuseStep 465703 = 698555) B698555
theorem B465743 : Blo 463784 465743 := bstep (se 1 (by rfl) ⟨349307, by rfl⟩ : syracuseStep 465743 = 698615) B698615
theorem B17832797 : Blo 463784 17832797 := bstep (se 3 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 17832797 = 6687299) B6687299
theorem B465759 : Blo 463784 465759 := bstep (se 1 (by rfl) ⟨349319, by rfl⟩ : syracuseStep 465759 = 698639) B698639
theorem B465787 : Blo 463784 465787 := bstep (se 1 (by rfl) ⟨349340, by rfl⟩ : syracuseStep 465787 = 698681) B698681
theorem B465839 : Blo 463784 465839 := bstep (se 1 (by rfl) ⟨349379, by rfl⟩ : syracuseStep 465839 = 698759) B698759
theorem B465863 : Blo 463784 465863 := bstep (se 1 (by rfl) ⟨349397, by rfl⟩ : syracuseStep 465863 = 698795) B698795
theorem B465883 : Blo 463784 465883 := bstep (se 1 (by rfl) ⟨349412, by rfl⟩ : syracuseStep 465883 = 698825) B698825
theorem B465959 : Blo 463784 465959 := bstep (se 1 (by rfl) ⟨349469, by rfl⟩ : syracuseStep 465959 = 698939) B698939
theorem B465999 : Blo 463784 465999 := bstep (se 1 (by rfl) ⟨349499, by rfl⟩ : syracuseStep 465999 = 698999) B698999
theorem B466015 : Blo 463784 466015 := bstep (se 1 (by rfl) ⟨349511, by rfl⟩ : syracuseStep 466015 = 699023) B699023
theorem B466043 : Blo 463784 466043 := bstep (se 1 (by rfl) ⟨349532, by rfl⟩ : syracuseStep 466043 = 699065) B699065
theorem B466095 : Blo 463784 466095 := bstep (se 1 (by rfl) ⟨349571, by rfl⟩ : syracuseStep 466095 = 699143) B699143
theorem B466119 : Blo 463784 466119 := bstep (se 1 (by rfl) ⟨349589, by rfl⟩ : syracuseStep 466119 = 699179) B699179
theorem B466139 : Blo 463784 466139 := bstep (se 1 (by rfl) ⟨349604, by rfl⟩ : syracuseStep 466139 = 699209) B699209
theorem B466215 : Blo 463784 466215 := bstep (se 1 (by rfl) ⟨349661, by rfl⟩ : syracuseStep 466215 = 699323) B699323
theorem B466255 : Blo 463784 466255 := bstep (se 1 (by rfl) ⟨349691, by rfl⟩ : syracuseStep 466255 = 699383) B699383
theorem B466271 : Blo 463784 466271 := bstep (se 1 (by rfl) ⟨349703, by rfl⟩ : syracuseStep 466271 = 699407) B699407
theorem B466299 : Blo 463784 466299 := bstep (se 1 (by rfl) ⟨349724, by rfl⟩ : syracuseStep 466299 = 699449) B699449
theorem B466351 : Blo 463784 466351 := bstep (se 1 (by rfl) ⟨349763, by rfl⟩ : syracuseStep 466351 = 699527) B699527
theorem B695735 : Blo 463784 695735 := bstep (se 1 (by rfl) ⟨521801, by rfl⟩ : syracuseStep 695735 = 1043603) B1043603
theorem B466375 : Blo 463784 466375 := bstep (se 1 (by rfl) ⟨349781, by rfl⟩ : syracuseStep 466375 = 699563) B699563
theorem B1973705 : Blo 463784 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B695771 : Blo 463784 695771 := bstep (se 1 (by rfl) ⟨521828, by rfl⟩ : syracuseStep 695771 = 1043657) B1043657
theorem B466395 : Blo 463784 466395 := bstep (se 1 (by rfl) ⟨349796, by rfl⟩ : syracuseStep 466395 = 699593) B699593
theorem B466471 : Blo 463784 466471 := bstep (se 1 (by rfl) ⟨349853, by rfl⟩ : syracuseStep 466471 = 699707) B699707
theorem B466511 : Blo 463784 466511 := bstep (se 1 (by rfl) ⟨349883, by rfl⟩ : syracuseStep 466511 = 699767) B699767
theorem B466527 : Blo 463784 466527 := bstep (se 1 (by rfl) ⟨349895, by rfl⟩ : syracuseStep 466527 = 699791) B699791
theorem B466555 : Blo 463784 466555 := bstep (se 1 (by rfl) ⟨349916, by rfl⟩ : syracuseStep 466555 = 699833) B699833
theorem B466607 : Blo 463784 466607 := bstep (se 1 (by rfl) ⟨349955, by rfl⟩ : syracuseStep 466607 = 699911) B699911
theorem B466631 : Blo 463784 466631 := bstep (se 1 (by rfl) ⟨349973, by rfl⟩ : syracuseStep 466631 = 699947) B699947
theorem B466651 : Blo 463784 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B466727 : Blo 463784 466727 := bstep (se 1 (by rfl) ⟨350045, by rfl⟩ : syracuseStep 466727 = 700091) B700091
theorem B466767 : Blo 463784 466767 := bstep (se 1 (by rfl) ⟨350075, by rfl⟩ : syracuseStep 466767 = 700151) B700151
theorem B466783 : Blo 463784 466783 := bstep (se 1 (by rfl) ⟨350087, by rfl⟩ : syracuseStep 466783 = 700175) B700175
theorem B466811 : Blo 463784 466811 := bstep (se 1 (by rfl) ⟨350108, by rfl⟩ : syracuseStep 466811 = 700217) B700217
theorem B466863 : Blo 463784 466863 := bstep (se 1 (by rfl) ⟨350147, by rfl⟩ : syracuseStep 466863 = 700295) B700295
theorem B696239 : Blo 463784 696239 := bstep (se 1 (by rfl) ⟨522179, by rfl⟩ : syracuseStep 696239 = 1044359) B1044359
theorem B466887 : Blo 463784 466887 := bstep (se 1 (by rfl) ⟨350165, by rfl⟩ : syracuseStep 466887 = 700331) B700331
theorem B466907 : Blo 463784 466907 := bstep (se 1 (by rfl) ⟨350180, by rfl⟩ : syracuseStep 466907 = 700361) B700361
theorem B696329 : Blo 463784 696329 := bstep (se 2 (by rfl) ⟨261123, by rfl⟩ : syracuseStep 696329 = 522247) B522247
theorem B696359 : Blo 463784 696359 := bstep (se 1 (by rfl) ⟨522269, by rfl⟩ : syracuseStep 696359 = 1044539) B1044539
theorem B466983 : Blo 463784 466983 := bstep (se 1 (by rfl) ⟨350237, by rfl⟩ : syracuseStep 466983 = 700475) B700475
theorem B467023 : Blo 463784 467023 := bstep (se 1 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 467023 = 700535) B700535
theorem B467039 : Blo 463784 467039 := bstep (se 1 (by rfl) ⟨350279, by rfl⟩ : syracuseStep 467039 = 700559) B700559
theorem B696443 : Blo 463784 696443 := bstep (se 1 (by rfl) ⟨522332, by rfl⟩ : syracuseStep 696443 = 1044665) B1044665
theorem B467067 : Blo 463784 467067 := bstep (se 1 (by rfl) ⟨350300, by rfl⟩ : syracuseStep 467067 = 700601) B700601
theorem B467119 : Blo 463784 467119 := bstep (se 1 (by rfl) ⟨350339, by rfl⟩ : syracuseStep 467119 = 700679) B700679
theorem B467143 : Blo 463784 467143 := bstep (se 1 (by rfl) ⟨350357, by rfl⟩ : syracuseStep 467143 = 700715) B700715
theorem B467163 : Blo 463784 467163 := bstep (se 1 (by rfl) ⟨350372, by rfl⟩ : syracuseStep 467163 = 700745) B700745
theorem B696569 : Blo 463784 696569 := bstep (se 2 (by rfl) ⟨261213, by rfl⟩ : syracuseStep 696569 = 522427) B522427
theorem B467239 : Blo 463784 467239 := bstep (se 1 (by rfl) ⟨350429, by rfl⟩ : syracuseStep 467239 = 700859) B700859
theorem B467279 : Blo 463784 467279 := bstep (se 1 (by rfl) ⟨350459, by rfl⟩ : syracuseStep 467279 = 700919) B700919
theorem B696671 : Blo 463784 696671 := bstep (se 1 (by rfl) ⟨522503, by rfl⟩ : syracuseStep 696671 = 1045007) B1045007
theorem B467295 : Blo 463784 467295 := bstep (se 1 (by rfl) ⟨350471, by rfl⟩ : syracuseStep 467295 = 700943) B700943
theorem B696683 : Blo 463784 696683 := bstep (se 1 (by rfl) ⟨522512, by rfl⟩ : syracuseStep 696683 = 1045025) B1045025
theorem B467323 : Blo 463784 467323 := bstep (se 1 (by rfl) ⟨350492, by rfl⟩ : syracuseStep 467323 = 700985) B700985
theorem B1417601 : Blo 463784 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B467375 : Blo 463784 467375 := bstep (se 1 (by rfl) ⟨350531, by rfl⟩ : syracuseStep 467375 = 701063) B701063
theorem B467399 : Blo 463784 467399 := bstep (se 1 (by rfl) ⟨350549, by rfl⟩ : syracuseStep 467399 = 701099) B701099
theorem B467419 : Blo 463784 467419 := bstep (se 1 (by rfl) ⟨350564, by rfl⟩ : syracuseStep 467419 = 701129) B701129
theorem B467495 : Blo 463784 467495 := bstep (se 1 (by rfl) ⟨350621, by rfl⟩ : syracuseStep 467495 = 701243) B701243
theorem B696911 : Blo 463784 696911 := bstep (se 1 (by rfl) ⟨522683, by rfl⟩ : syracuseStep 696911 = 1045367) B1045367
theorem B467535 : Blo 463784 467535 := bstep (se 1 (by rfl) ⟨350651, by rfl⟩ : syracuseStep 467535 = 701303) B701303
theorem B467551 : Blo 463784 467551 := bstep (se 1 (by rfl) ⟨350663, by rfl⟩ : syracuseStep 467551 = 701327) B701327
theorem B467579 : Blo 463784 467579 := bstep (se 1 (by rfl) ⟨350684, by rfl⟩ : syracuseStep 467579 = 701369) B701369
theorem B467631 : Blo 463784 467631 := bstep (se 1 (by rfl) ⟨350723, by rfl⟩ : syracuseStep 467631 = 701447) B701447
theorem B1909433 : Blo 463784 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B697031 : Blo 463784 697031 := bstep (se 1 (by rfl) ⟨522773, by rfl⟩ : syracuseStep 697031 = 1045547) B1045547
theorem B467655 : Blo 463784 467655 := bstep (se 1 (by rfl) ⟨350741, by rfl⟩ : syracuseStep 467655 = 701483) B701483
theorem B467675 : Blo 463784 467675 := bstep (se 1 (by rfl) ⟨350756, by rfl⟩ : syracuseStep 467675 = 701513) B701513
theorem B467751 : Blo 463784 467751 := bstep (se 1 (by rfl) ⟨350813, by rfl⟩ : syracuseStep 467751 = 701627) B701627
theorem B697193 : Blo 463784 697193 := bstep (se 2 (by rfl) ⟨261447, by rfl⟩ : syracuseStep 697193 = 522895) B522895
theorem B2237291 : Blo 463784 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B5677931 : Blo 463784 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B697271 : Blo 463784 697271 := bstep (se 1 (by rfl) ⟨522953, by rfl⟩ : syracuseStep 697271 = 1045907) B1045907
theorem B697307 : Blo 463784 697307 := bstep (se 1 (by rfl) ⟨522980, by rfl⟩ : syracuseStep 697307 = 1045961) B1045961
theorem B664615 : Blo 463784 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B2237635 : Blo 463784 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B664939 : Blo 463784 664939 := bstep (se 1 (by rfl) ⟨498704, by rfl⟩ : syracuseStep 664939 = 997409) B997409
theorem B697775 : Blo 463784 697775 := bstep (se 1 (by rfl) ⟨523331, by rfl⟩ : syracuseStep 697775 = 1046663) B1046663
theorem B697865 : Blo 463784 697865 := bstep (se 2 (by rfl) ⟨261699, by rfl⟩ : syracuseStep 697865 = 523399) B523399
theorem B1418777 : Blo 463784 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B697895 : Blo 463784 697895 := bstep (se 1 (by rfl) ⟨523421, by rfl⟩ : syracuseStep 697895 = 1046843) B1046843
theorem B6727211 : Blo 463784 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B665167 : Blo 463784 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B992891 : Blo 463784 992891 := bstep (se 1 (by rfl) ⟨744668, by rfl⟩ : syracuseStep 992891 = 1489337) B1489337
theorem B697979 : Blo 463784 697979 := bstep (se 1 (by rfl) ⟨523484, by rfl⟩ : syracuseStep 697979 = 1046969) B1046969
theorem B2827997 : Blo 463784 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B698105 : Blo 463784 698105 := bstep (se 2 (by rfl) ⟨261789, by rfl⟩ : syracuseStep 698105 = 523579) B523579
theorem B698207 : Blo 463784 698207 := bstep (se 1 (by rfl) ⟨523655, by rfl⟩ : syracuseStep 698207 = 1047311) B1047311
theorem B698219 : Blo 463784 698219 := bstep (se 1 (by rfl) ⟨523664, by rfl⟩ : syracuseStep 698219 = 1047329) B1047329
theorem B1321039 : Blo 463784 1321039 := bstep (se 1 (by rfl) ⟨990779, by rfl⟩ : syracuseStep 1321039 = 1981559) B1981559
theorem B698447 : Blo 463784 698447 := bstep (se 1 (by rfl) ⟨523835, by rfl⟩ : syracuseStep 698447 = 1047671) B1047671
theorem B698567 : Blo 463784 698567 := bstep (se 1 (by rfl) ⟨523925, by rfl⟩ : syracuseStep 698567 = 1047851) B1047851
theorem B3188965 : Blo 463784 3188965 := bstep (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) B597931
theorem B698729 : Blo 463784 698729 := bstep (se 2 (by rfl) ⟨262023, by rfl⟩ : syracuseStep 698729 = 524047) B524047
theorem B698807 : Blo 463784 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B698843 : Blo 463784 698843 := bstep (se 1 (by rfl) ⟨524132, by rfl⟩ : syracuseStep 698843 = 1048265) B1048265
theorem B1518139 : Blo 463784 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B699311 : Blo 463784 699311 := bstep (se 1 (by rfl) ⟨524483, by rfl⟩ : syracuseStep 699311 = 1048967) B1048967
theorem B994231 : Blo 463784 994231 := bstep (se 1 (by rfl) ⟨745673, by rfl⟩ : syracuseStep 994231 = 1491347) B1491347
theorem B6794225 : Blo 463784 6794225 := bstep (se 2 (by rfl) ⟨2547834, by rfl⟩ : syracuseStep 6794225 = 5095669) B5095669
theorem B699401 : Blo 463784 699401 := bstep (se 2 (by rfl) ⟨262275, by rfl⟩ : syracuseStep 699401 = 524551) B524551
theorem B699431 : Blo 463784 699431 := bstep (se 1 (by rfl) ⟨524573, by rfl⟩ : syracuseStep 699431 = 1049147) B1049147
theorem B699515 : Blo 463784 699515 := bstep (se 1 (by rfl) ⟨524636, by rfl⟩ : syracuseStep 699515 = 1049273) B1049273
theorem B699641 : Blo 463784 699641 := bstep (se 2 (by rfl) ⟨262365, by rfl⟩ : syracuseStep 699641 = 524731) B524731
theorem B699743 : Blo 463784 699743 := bstep (se 1 (by rfl) ⟨524807, by rfl⟩ : syracuseStep 699743 = 1049615) B1049615
theorem B699755 : Blo 463784 699755 := bstep (se 1 (by rfl) ⟨524816, by rfl⟩ : syracuseStep 699755 = 1049633) B1049633
theorem B699983 : Blo 463784 699983 := bstep (se 1 (by rfl) ⟨524987, by rfl⟩ : syracuseStep 699983 = 1049975) B1049975
theorem B700103 : Blo 463784 700103 := bstep (se 1 (by rfl) ⟨525077, by rfl⟩ : syracuseStep 700103 = 1050155) B1050155
theorem B7286543 : Blo 463784 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B700265 : Blo 463784 700265 := bstep (se 2 (by rfl) ⟨262599, by rfl⟩ : syracuseStep 700265 = 525199) B525199
theorem B700343 : Blo 463784 700343 := bstep (se 1 (by rfl) ⟨525257, by rfl⟩ : syracuseStep 700343 = 1050515) B1050515
theorem B700379 : Blo 463784 700379 := bstep (se 1 (by rfl) ⟨525284, by rfl⟩ : syracuseStep 700379 = 1050569) B1050569
theorem B6696989 : Blo 463784 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B5288165 : Blo 463784 5288165 := bstep (se 4 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 5288165 = 991531) B991531
theorem B700847 : Blo 463784 700847 := bstep (se 1 (by rfl) ⟨525635, by rfl⟩ : syracuseStep 700847 = 1051271) B1051271
theorem B1192457 : Blo 463784 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B700937 : Blo 463784 700937 := bstep (se 2 (by rfl) ⟨262851, by rfl⟩ : syracuseStep 700937 = 525703) B525703
theorem B700967 : Blo 463784 700967 := bstep (se 1 (by rfl) ⟨525725, by rfl⟩ : syracuseStep 700967 = 1051451) B1051451
theorem B701051 : Blo 463784 701051 := bstep (se 1 (by rfl) ⟨525788, by rfl⟩ : syracuseStep 701051 = 1051577) B1051577
theorem B701177 : Blo 463784 701177 := bstep (se 2 (by rfl) ⟨262941, by rfl⟩ : syracuseStep 701177 = 525883) B525883
theorem B701279 : Blo 463784 701279 := bstep (se 1 (by rfl) ⟨525959, by rfl⟩ : syracuseStep 701279 = 1051919) B1051919
theorem B799595 : Blo 463784 799595 := bstep (se 1 (by rfl) ⟨599696, by rfl⟩ : syracuseStep 799595 = 1199393) B1199393
theorem B701291 : Blo 463784 701291 := bstep (se 1 (by rfl) ⟨525968, by rfl⟩ : syracuseStep 701291 = 1051937) B1051937
theorem B1684385 : Blo 463784 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B701519 : Blo 463784 701519 := bstep (se 1 (by rfl) ⟨526139, by rfl⟩ : syracuseStep 701519 = 1052279) B1052279
theorem B38810765 : Blo 463784 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B2733209 : Blo 463784 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B701639 : Blo 463784 701639 := bstep (se 1 (by rfl) ⟨526229, by rfl⟩ : syracuseStep 701639 = 1052459) B1052459
theorem B1324583 : Blo 463784 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B2242171 : Blo 463784 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B472699 : Blo 463784 472699 := bstep (se 1 (by rfl) ⟨354524, by rfl⟩ : syracuseStep 472699 = 709049) B709049
theorem B1357511 : Blo 463784 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B1914881 : Blo 463784 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B1489067 : Blo 463784 1489067 := bstep (se 1 (by rfl) ⟨1116800, by rfl⟩ : syracuseStep 1489067 = 2233601) B2233601
theorem B2996585 : Blo 463784 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B1325767 : Blo 463784 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B1490167 : Blo 463784 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B1326689 : Blo 463784 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B1982141 : Blo 463784 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B1982825 : Blo 463784 1982825 := bstep (se 2 (by rfl) ⟨743559, by rfl⟩ : syracuseStep 1982825 = 1487119) B1487119
theorem B9585211 : Blo 463784 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B1491655 : Blo 463784 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B836425 : Blo 463784 836425 := bstep (se 2 (by rfl) ⟨313659, by rfl⟩ : syracuseStep 836425 = 627319) B627319
theorem B1328147 : Blo 463784 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B1328375 : Blo 463784 1328375 := bstep (se 1 (by rfl) ⟨996281, by rfl⟩ : syracuseStep 1328375 = 1992563) B1992563
theorem B3360143 : Blo 463784 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B1492577 : Blo 463784 1492577 := bstep (se 2 (by rfl) ⟨559716, by rfl⟩ : syracuseStep 1492577 = 1119433) B1119433
theorem B8931161 : Blo 463784 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B3524471 : Blo 463784 3524471 := bstep (se 1 (by rfl) ⟨2643353, by rfl⟩ : syracuseStep 3524471 = 5286707) B5286707
theorem B11290661 : Blo 463784 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B3983417 : Blo 463784 3983417 := bstep (se 2 (by rfl) ⟨1493781, by rfl⟩ : syracuseStep 3983417 = 2987563) B2987563
theorem B838163 : Blo 463784 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B1329787 : Blo 463784 1329787 := bstep (se 1 (by rfl) ⟨997340, by rfl⟩ : syracuseStep 1329787 = 1994681) B1994681
theorem B22727303 : Blo 463784 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B2116381 : Blo 463784 2116381 := bstep (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) B793643
theorem B1330015 : Blo 463784 1330015 := bstep (se 1 (by rfl) ⟨997511, by rfl⟩ : syracuseStep 1330015 = 1995023) B1995023
theorem B1592183 : Blo 463784 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B1494359 : Blo 463784 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B1985917 : Blo 463784 1985917 := bstep (se 3 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 1985917 = 744719) B744719
theorem B2641531 : Blo 463784 2641531 := bstep (se 1 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 2641531 = 3962297) B3962297
theorem B2870923 : Blo 463784 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B478919 : Blo 463784 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B4476653 : Blo 463784 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B806843 : Blo 463784 806843 := bstep (se 1 (by rfl) ⟨605132, by rfl⟩ : syracuseStep 806843 = 1210265) B1210265
theorem B13062221 : Blo 463784 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B1331599 : Blo 463784 1331599 := bstep (se 1 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 1331599 = 1997399) B1997399
theorem B3592763 : Blo 463784 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B13587011 : Blo 463784 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B5296913 : Blo 463784 5296913 := bstep (se 2 (by rfl) ⟨1986342, by rfl⟩ : syracuseStep 5296913 = 3972685) B3972685
theorem B3527873 : Blo 463784 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B5985683 : Blo 463784 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B4773437 : Blo 463784 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B3200573 : Blo 463784 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B743111 : Blo 463784 743111 := bstep (se 1 (by rfl) ⟨557333, by rfl⟩ : syracuseStep 743111 = 1114667) B1114667
theorem B2512583 : Blo 463784 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B3987143 : Blo 463784 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B1497241 : Blo 463784 1497241 := bstep (se 2 (by rfl) ⟨561465, by rfl⟩ : syracuseStep 1497241 = 1122931) B1122931
theorem B2349323 : Blo 463784 2349323 := bstep (se 1 (by rfl) ⟨1761992, by rfl⟩ : syracuseStep 2349323 = 3523985) B3523985
theorem B1497473 : Blo 463784 1497473 := bstep (se 2 (by rfl) ⟨561552, by rfl⟩ : syracuseStep 1497473 = 1123105) B1123105
theorem B743899 : Blo 463784 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B6740813 : Blo 463784 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B744571 : Blo 463784 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B3366461 : Blo 463784 3366461 := bstep (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) B1262423
theorem B1990291 : Blo 463784 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B2350781 : Blo 463784 2350781 := bstep (se 3 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 2350781 = 881543) B881543
theorem B745289 : Blo 463784 745289 := bstep (se 2 (by rfl) ⟨279483, by rfl⟩ : syracuseStep 745289 = 558967) B558967
theorem B2350943 : Blo 463784 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B5955443 : Blo 463784 5955443 := bstep (se 1 (by rfl) ⟨4466582, by rfl⟩ : syracuseStep 5955443 = 8933165) B8933165
theorem B3530789 : Blo 463784 3530789 := bstep (se 4 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 3530789 = 662023) B662023
theorem B3792977 : Blo 463784 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1794163 : Blo 463784 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B2154763 : Blo 463784 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B1565513 : Blo 463784 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B2974799 : Blo 463784 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B6382745 : Blo 463784 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1992289 : Blo 463784 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B1566647 : Blo 463784 1566647 := bstep (se 1 (by rfl) ⟨1174985, by rfl⟩ : syracuseStep 1566647 = 2349971) B2349971
theorem B1763329 : Blo 463784 1763329 := bstep (se 2 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 1763329 = 1322497) B1322497
theorem B1271965 : Blo 463784 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B10741997 : Blo 463784 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B1567241 : Blo 463784 1567241 := bstep (se 2 (by rfl) ⟨587715, by rfl⟩ : syracuseStep 1567241 = 1175431) B1175431
theorem B7662109 : Blo 463784 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B2353697 : Blo 463784 2353697 := bstep (se 2 (by rfl) ⟨882636, by rfl⟩ : syracuseStep 2353697 = 1765273) B1765273
theorem B10316489 : Blo 463784 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B1764089 : Blo 463784 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B1174459 : Blo 463784 1174459 := bstep (se 1 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 1174459 = 1761689) B1761689
theorem B10742807 : Blo 463784 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B3763493 : Blo 463784 3763493 := bstep (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) B705655
theorem B1568105 : Blo 463784 1568105 := bstep (se 2 (by rfl) ⟨588039, by rfl⟩ : syracuseStep 1568105 = 1176079) B1176079
theorem B1043855 : Blo 463784 1043855 := bstep (se 1 (by rfl) ⟨782891, by rfl⟩ : syracuseStep 1043855 = 1565783) B1565783
theorem B749179 : Blo 463784 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B12906161 : Blo 463784 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B1044179 : Blo 463784 1044179 := bstep (se 1 (by rfl) ⟨783134, by rfl⟩ : syracuseStep 1044179 = 1566269) B1566269
theorem B5959439 : Blo 463784 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B880571 : Blo 463784 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B1568699 : Blo 463784 1568699 := bstep (se 1 (by rfl) ⟨1176524, by rfl⟩ : syracuseStep 1568699 = 2353049) B2353049
theorem B1765547 : Blo 463784 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B3698945 : Blo 463784 3698945 := bstep (se 2 (by rfl) ⟨1387104, by rfl⟩ : syracuseStep 3698945 = 2774209) B2774209
theorem B881057 : Blo 463784 881057 := bstep (se 2 (by rfl) ⟨330396, by rfl⟩ : syracuseStep 881057 = 660793) B660793
theorem B14283229 : Blo 463784 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B782905 : Blo 463784 782905 := bstep (se 2 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 782905 = 587179) B587179
theorem B881209 : Blo 463784 881209 := bstep (se 2 (by rfl) ⟨330453, by rfl⟩ : syracuseStep 881209 = 660907) B660907
theorem B1045115 : Blo 463784 1045115 := bstep (se 1 (by rfl) ⟨783836, by rfl⟩ : syracuseStep 1045115 = 1567673) B1567673
theorem B783047 : Blo 463784 783047 := bstep (se 1 (by rfl) ⟨587285, by rfl⟩ : syracuseStep 783047 = 1174571) B1174571
theorem B1045241 : Blo 463784 1045241 := bstep (se 2 (by rfl) ⟨391965, by rfl⟩ : syracuseStep 1045241 = 783931) B783931
theorem B5960465 : Blo 463784 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B783209 : Blo 463784 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B881513 : Blo 463784 881513 := bstep (se 2 (by rfl) ⟨330567, by rfl⟩ : syracuseStep 881513 = 661135) B661135
theorem B5993473 : Blo 463784 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B1045511 : Blo 463784 1045511 := bstep (se 1 (by rfl) ⟨784133, by rfl⟩ : syracuseStep 1045511 = 1568267) B1568267
theorem B947207 : Blo 463784 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B1045583 : Blo 463784 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B947279 : Blo 463784 947279 := bstep (se 1 (by rfl) ⟨710459, by rfl⟩ : syracuseStep 947279 = 1420919) B1420919
theorem B1995947 : Blo 463784 1995947 := bstep (se 1 (by rfl) ⟨1496960, by rfl⟩ : syracuseStep 1995947 = 2993921) B2993921
theorem B783607 : Blo 463784 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B1766717 : Blo 463784 1766717 := bstep (se 3 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 1766717 = 662519) B662519
theorem B783803 : Blo 463784 783803 := bstep (se 1 (by rfl) ⟨587852, by rfl⟩ : syracuseStep 783803 = 1175705) B1175705
theorem B1045979 : Blo 463784 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B1177051 : Blo 463784 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B783911 : Blo 463784 783911 := bstep (se 1 (by rfl) ⟨587933, by rfl⟩ : syracuseStep 783911 = 1175867) B1175867
theorem B2356775 : Blo 463784 2356775 := bstep (se 1 (by rfl) ⟨1767581, by rfl⟩ : syracuseStep 2356775 = 3535163) B3535163
theorem B521851 : Blo 463784 521851 := bstep (se 1 (by rfl) ⟨391388, by rfl⟩ : syracuseStep 521851 = 782777) B782777
theorem B1570427 : Blo 463784 1570427 := bstep (se 1 (by rfl) ⟨1177820, by rfl⟩ : syracuseStep 1570427 = 2355641) B2355641
theorem B1767035 : Blo 463784 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B1799827 : Blo 463784 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B3536621 : Blo 463784 3536621 := bstep (se 3 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 3536621 = 1326233) B1326233
theorem B1570589 : Blo 463784 1570589 := bstep (se 3 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 1570589 = 588971) B588971
theorem B784201 : Blo 463784 784201 := bstep (se 2 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 784201 = 588151) B588151
theorem B784235 : Blo 463784 784235 := bstep (se 1 (by rfl) ⟨588176, by rfl⟩ : syracuseStep 784235 = 1176353) B1176353
theorem B1996663 : Blo 463784 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B3766151 : Blo 463784 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B1046447 : Blo 463784 1046447 := bstep (se 1 (by rfl) ⟨784835, by rfl⟩ : syracuseStep 1046447 = 1569671) B1569671
theorem B30275531 : Blo 463784 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B522319 : Blo 463784 522319 := bstep (se 1 (by rfl) ⟨391739, by rfl⟩ : syracuseStep 522319 = 783479) B783479
theorem B1177679 : Blo 463784 1177679 := bstep (se 1 (by rfl) ⟨883259, by rfl⟩ : syracuseStep 1177679 = 1766519) B1766519
theorem B1046699 : Blo 463784 1046699 := bstep (se 1 (by rfl) ⟨785024, by rfl⟩ : syracuseStep 1046699 = 1570049) B1570049
theorem B784633 : Blo 463784 784633 := bstep (se 2 (by rfl) ⟨294237, by rfl⟩ : syracuseStep 784633 = 588475) B588475
theorem B4520279 : Blo 463784 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B1341839 : Blo 463784 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B522715 : Blo 463784 522715 := bstep (se 1 (by rfl) ⟨392036, by rfl⟩ : syracuseStep 522715 = 784073) B784073
theorem B1571291 : Blo 463784 1571291 := bstep (se 1 (by rfl) ⟨1178468, by rfl⟩ : syracuseStep 1571291 = 2356937) B2356937
theorem B784903 : Blo 463784 784903 := bstep (se 1 (by rfl) ⟨588677, by rfl⟩ : syracuseStep 784903 = 1177355) B1177355
theorem B3537593 : Blo 463784 3537593 := bstep (se 2 (by rfl) ⟨1326597, by rfl⟩ : syracuseStep 3537593 = 2653195) B2653195
theorem B1047239 : Blo 463784 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B1178327 : Blo 463784 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B5438285 : Blo 463784 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B523183 : Blo 463784 523183 := bstep (se 1 (by rfl) ⟨392387, by rfl⟩ : syracuseStep 523183 = 784775) B784775
theorem B785335 : Blo 463784 785335 := bstep (se 1 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 785335 = 1178003) B1178003
theorem B883639 : Blo 463784 883639 := bstep (se 1 (by rfl) ⟨662729, by rfl⟩ : syracuseStep 883639 = 1325459) B1325459
theorem B1768463 : Blo 463784 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B785531 : Blo 463784 785531 := bstep (se 1 (by rfl) ⟨589148, by rfl⟩ : syracuseStep 785531 = 1178297) B1178297
theorem B1571993 : Blo 463784 1571993 := bstep (se 2 (by rfl) ⟨589497, by rfl⟩ : syracuseStep 1571993 = 1178995) B1178995
theorem B523615 : Blo 463784 523615 := bstep (se 1 (by rfl) ⟨392711, by rfl⟩ : syracuseStep 523615 = 785423) B785423
theorem B2391439 : Blo 463784 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B785929 : Blo 463784 785929 := bstep (se 2 (by rfl) ⟨294723, by rfl⟩ : syracuseStep 785929 = 589447) B589447
theorem B589351 : Blo 463784 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B1048103 : Blo 463784 1048103 := bstep (se 1 (by rfl) ⟨786077, by rfl⟩ : syracuseStep 1048103 = 1572155) B1572155
theorem B2358881 : Blo 463784 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B3538565 : Blo 463784 3538565 := bstep (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) B663481
theorem B786091 : Blo 463784 786091 := bstep (se 1 (by rfl) ⟨589568, by rfl⟩ : syracuseStep 786091 = 1179137) B1179137
theorem B523975 : Blo 463784 523975 := bstep (se 1 (by rfl) ⟨392981, by rfl⟩ : syracuseStep 523975 = 785963) B785963
theorem B589675 : Blo 463784 589675 := bstep (se 1 (by rfl) ⟨442256, by rfl⟩ : syracuseStep 589675 = 884513) B884513
theorem B1048427 : Blo 463784 1048427 := bstep (se 1 (by rfl) ⟨786320, by rfl⟩ : syracuseStep 1048427 = 1572641) B1572641
theorem B1048481 : Blo 463784 1048481 := bstep (se 2 (by rfl) ⟨393180, by rfl⟩ : syracuseStep 1048481 = 786361) B786361
theorem B786395 : Blo 463784 786395 := bstep (se 1 (by rfl) ⟨589796, by rfl⟩ : syracuseStep 786395 = 1179593) B1179593
theorem B2392217 : Blo 463784 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1048787 : Blo 463784 1048787 := bstep (se 1 (by rfl) ⟨786590, by rfl⟩ : syracuseStep 1048787 = 1573181) B1573181
theorem B1048841 : Blo 463784 1048841 := bstep (se 2 (by rfl) ⟨393315, by rfl⟩ : syracuseStep 1048841 = 786631) B786631
theorem B1180079 : Blo 463784 1180079 := bstep (se 1 (by rfl) ⟨885059, by rfl⟩ : syracuseStep 1180079 = 1770119) B1770119
theorem B1180129 : Blo 463784 1180129 := bstep (se 2 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 1180129 = 885097) B885097
theorem B1049057 : Blo 463784 1049057 := bstep (se 2 (by rfl) ⟨393396, by rfl⟩ : syracuseStep 1049057 = 786793) B786793
theorem B1573559 : Blo 463784 1573559 := bstep (se 1 (by rfl) ⟨1180169, by rfl⟩ : syracuseStep 1573559 = 2360339) B2360339
theorem B885431 : Blo 463784 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B12780281 : Blo 463784 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B1049363 : Blo 463784 1049363 := bstep (se 1 (by rfl) ⟨787022, by rfl⟩ : syracuseStep 1049363 = 1574045) B1574045
theorem B590647 : Blo 463784 590647 := bstep (se 1 (by rfl) ⟨442985, by rfl⟩ : syracuseStep 590647 = 885971) B885971
theorem B885583 : Blo 463784 885583 := bstep (se 1 (by rfl) ⟨664187, by rfl⟩ : syracuseStep 885583 = 1328375) B1328375
theorem B787279 : Blo 463784 787279 := bstep (se 1 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 787279 = 1180919) B1180919
theorem B1049723 : Blo 463784 1049723 := bstep (se 1 (by rfl) ⟨787292, by rfl⟩ : syracuseStep 1049723 = 1574585) B1574585
theorem B591067 : Blo 463784 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B1049849 : Blo 463784 1049849 := bstep (se 2 (by rfl) ⟨393693, by rfl⟩ : syracuseStep 1049849 = 787387) B787387
theorem B2360663 : Blo 463784 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B2655611 : Blo 463784 2655611 := bstep (se 1 (by rfl) ⟨1991708, by rfl⟩ : syracuseStep 2655611 = 3983417) B3983417
theorem B1181051 : Blo 463784 1181051 := bstep (se 1 (by rfl) ⟨885788, by rfl⟩ : syracuseStep 1181051 = 1771577) B1771577
theorem B1049993 : Blo 463784 1049993 := bstep (se 2 (by rfl) ⟨393747, by rfl⟩ : syracuseStep 1049993 = 787495) B787495
theorem B886153 : Blo 463784 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B787961 : Blo 463784 787961 := bstep (se 2 (by rfl) ⟨295485, by rfl⟩ : syracuseStep 787961 = 590971) B590971
theorem B1050119 : Blo 463784 1050119 := bstep (se 1 (by rfl) ⟨787589, by rfl⟩ : syracuseStep 1050119 = 1575179) B1575179
theorem B2983513 : Blo 463784 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B525919 : Blo 463784 525919 := bstep (se 1 (by rfl) ⟨394439, by rfl⟩ : syracuseStep 525919 = 788879) B788879
theorem B558775 : Blo 463784 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B1050299 : Blo 463784 1050299 := bstep (se 1 (by rfl) ⟨787724, by rfl⟩ : syracuseStep 1050299 = 1575449) B1575449
theorem B788231 : Blo 463784 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B1050425 : Blo 463784 1050425 := bstep (se 2 (by rfl) ⟨393909, by rfl⟩ : syracuseStep 1050425 = 787819) B787819
theorem B886889 : Blo 463784 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B2656385 : Blo 463784 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B2361473 : Blo 463784 2361473 := bstep (se 2 (by rfl) ⟨885552, by rfl⟩ : syracuseStep 2361473 = 1771105) B1771105
theorem B1051055 : Blo 463784 1051055 := bstep (se 1 (by rfl) ⟨788291, by rfl⟩ : syracuseStep 1051055 = 1576583) B1576583
theorem B1051091 : Blo 463784 1051091 := bstep (se 1 (by rfl) ⟨788318, by rfl⟩ : syracuseStep 1051091 = 1576637) B1576637
theorem B2984435 : Blo 463784 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B788987 : Blo 463784 788987 := bstep (se 1 (by rfl) ⟨591740, by rfl⟩ : syracuseStep 788987 = 1183481) B1183481
theorem B1051199 : Blo 463784 1051199 := bstep (se 1 (by rfl) ⟨788399, by rfl⟩ : syracuseStep 1051199 = 1576799) B1576799
theorem B1575503 : Blo 463784 1575503 := bstep (se 1 (by rfl) ⟨1181627, by rfl⟩ : syracuseStep 1575503 = 2363255) B2363255
theorem B1051307 : Blo 463784 1051307 := bstep (se 1 (by rfl) ⟨788480, by rfl⟩ : syracuseStep 1051307 = 1576961) B1576961
theorem B2362283 : Blo 463784 2362283 := bstep (se 1 (by rfl) ⟨1771712, by rfl⟩ : syracuseStep 2362283 = 3543425) B3543425
theorem B2395175 : Blo 463784 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B1182863 : Blo 463784 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B1051847 : Blo 463784 1051847 := bstep (se 1 (by rfl) ⟨788885, by rfl⟩ : syracuseStep 1051847 = 1577771) B1577771
theorem B1772867 : Blo 463784 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B1052027 : Blo 463784 1052027 := bstep (se 1 (by rfl) ⟨789020, by rfl⟩ : syracuseStep 1052027 = 1578041) B1578041
theorem B1773049 : Blo 463784 1773049 := bstep (se 2 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 1773049 = 1329787) B1329787
theorem B1052153 : Blo 463784 1052153 := bstep (se 2 (by rfl) ⟨394557, by rfl⟩ : syracuseStep 1052153 = 789115) B789115
theorem B1052243 : Blo 463784 1052243 := bstep (se 1 (by rfl) ⟨789182, by rfl⟩ : syracuseStep 1052243 = 1578365) B1578365
theorem B2821841 : Blo 463784 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B3182291 : Blo 463784 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B2133715 : Blo 463784 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B1052423 : Blo 463784 1052423 := bstep (se 1 (by rfl) ⟨789317, by rfl⟩ : syracuseStep 1052423 = 1578635) B1578635
theorem B1773323 : Blo 463784 1773323 := bstep (se 1 (by rfl) ⟨1329992, by rfl⟩ : syracuseStep 1773323 = 2659985) B2659985
theorem B1773353 : Blo 463784 1773353 := bstep (se 2 (by rfl) ⟨665007, by rfl⟩ : syracuseStep 1773353 = 1330015) B1330015
theorem B1576745 : Blo 463784 1576745 := bstep (se 2 (by rfl) ⟨591279, by rfl⟩ : syracuseStep 1576745 = 1182559) B1182559
theorem B495407 : Blo 463784 495407 := bstep (se 1 (by rfl) ⟨371555, by rfl⟩ : syracuseStep 495407 = 743111) B743111
theorem B1675055 : Blo 463784 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B2658095 : Blo 463784 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B2363417 : Blo 463784 2363417 := bstep (se 2 (by rfl) ⟨886281, by rfl⟩ : syracuseStep 2363417 = 1772563) B1772563
theorem B4460933 : Blo 463784 4460933 := bstep (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) B836425
theorem B4493875 : Blo 463784 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B463823 : Blo 463784 463823 := bstep (se 1 (by rfl) ⟨347867, by rfl⟩ : syracuseStep 463823 = 695735) B695735
theorem B463847 : Blo 463784 463847 := bstep (se 1 (by rfl) ⟨347885, by rfl⟩ : syracuseStep 463847 = 695771) B695771
theorem B496859 : Blo 463784 496859 := bstep (se 1 (by rfl) ⟨372644, by rfl⟩ : syracuseStep 496859 = 745289) B745289
theorem B3970295 : Blo 463784 3970295 := bstep (se 1 (by rfl) ⟨2977721, by rfl⟩ : syracuseStep 3970295 = 5955443) B5955443
theorem B464159 : Blo 463784 464159 := bstep (se 1 (by rfl) ⟨348119, by rfl⟩ : syracuseStep 464159 = 696239) B696239
theorem B464219 : Blo 463784 464219 := bstep (se 1 (by rfl) ⟨348164, by rfl⟩ : syracuseStep 464219 = 696329) B696329
theorem B464239 : Blo 463784 464239 := bstep (se 1 (by rfl) ⟨348179, by rfl⟩ : syracuseStep 464239 = 696359) B696359
theorem B2528651 : Blo 463784 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B464295 : Blo 463784 464295 := bstep (se 1 (by rfl) ⟨348221, by rfl⟩ : syracuseStep 464295 = 696443) B696443
theorem B464379 : Blo 463784 464379 := bstep (se 1 (by rfl) ⟨348284, by rfl⟩ : syracuseStep 464379 = 696569) B696569
theorem B464447 : Blo 463784 464447 := bstep (se 1 (by rfl) ⟨348335, by rfl⟩ : syracuseStep 464447 = 696671) B696671
theorem B464455 : Blo 463784 464455 := bstep (se 1 (by rfl) ⟨348341, by rfl⟩ : syracuseStep 464455 = 696683) B696683
theorem B464607 : Blo 463784 464607 := bstep (se 1 (by rfl) ⟨348455, by rfl⟩ : syracuseStep 464607 = 696911) B696911
theorem B464687 : Blo 463784 464687 := bstep (se 1 (by rfl) ⟨348515, by rfl⟩ : syracuseStep 464687 = 697031) B697031
theorem B1775465 : Blo 463784 1775465 := bstep (se 2 (by rfl) ⟨665799, by rfl⟩ : syracuseStep 1775465 = 1331599) B1331599
theorem B464795 : Blo 463784 464795 := bstep (se 1 (by rfl) ⟨348596, by rfl⟩ : syracuseStep 464795 = 697193) B697193
theorem B464847 : Blo 463784 464847 := bstep (se 1 (by rfl) ⟨348635, by rfl⟩ : syracuseStep 464847 = 697271) B697271
theorem B19044305 : Blo 463784 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B3971045 : Blo 463784 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B464871 : Blo 463784 464871 := bstep (se 1 (by rfl) ⟨348653, by rfl⟩ : syracuseStep 464871 = 697307) B697307
theorem B3545369 : Blo 463784 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B465183 : Blo 463784 465183 := bstep (se 1 (by rfl) ⟨348887, by rfl⟩ : syracuseStep 465183 = 697775) B697775
theorem B465243 : Blo 463784 465243 := bstep (se 1 (by rfl) ⟨348932, by rfl⟩ : syracuseStep 465243 = 697865) B697865
theorem B465263 : Blo 463784 465263 := bstep (se 1 (by rfl) ⟨348947, by rfl⟩ : syracuseStep 465263 = 697895) B697895
theorem B661927 : Blo 463784 661927 := bstep (se 1 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 661927 = 992891) B992891
theorem B465319 : Blo 463784 465319 := bstep (se 1 (by rfl) ⟨348989, by rfl⟩ : syracuseStep 465319 = 697979) B697979
theorem B465403 : Blo 463784 465403 := bstep (se 1 (by rfl) ⟨349052, by rfl⟩ : syracuseStep 465403 = 698105) B698105
theorem B465471 : Blo 463784 465471 := bstep (se 1 (by rfl) ⟨349103, by rfl⟩ : syracuseStep 465471 = 698207) B698207
theorem B465479 : Blo 463784 465479 := bstep (se 1 (by rfl) ⟨349109, by rfl⟩ : syracuseStep 465479 = 698219) B698219
theorem B465631 : Blo 463784 465631 := bstep (se 1 (by rfl) ⟨349223, by rfl⟩ : syracuseStep 465631 = 698447) B698447
theorem B465711 : Blo 463784 465711 := bstep (se 1 (by rfl) ⟨349283, by rfl⟩ : syracuseStep 465711 = 698567) B698567
theorem B2366333 : Blo 463784 2366333 := bstep (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) B887375
theorem B465819 : Blo 463784 465819 := bstep (se 1 (by rfl) ⟨349364, by rfl⟩ : syracuseStep 465819 = 698729) B698729
theorem B465871 : Blo 463784 465871 := bstep (se 1 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 465871 = 698807) B698807
theorem B465895 : Blo 463784 465895 := bstep (se 1 (by rfl) ⟨349421, by rfl⟩ : syracuseStep 465895 = 698843) B698843
theorem B3546341 : Blo 463784 3546341 := bstep (se 4 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 3546341 = 664939) B664939
theorem B466207 : Blo 463784 466207 := bstep (se 1 (by rfl) ⟨349655, by rfl⟩ : syracuseStep 466207 = 699311) B699311
theorem B4529483 : Blo 463784 4529483 := bstep (se 1 (by rfl) ⟨3397112, by rfl⟩ : syracuseStep 4529483 = 6794225) B6794225
theorem B466267 : Blo 463784 466267 := bstep (se 1 (by rfl) ⟨349700, by rfl⟩ : syracuseStep 466267 = 699401) B699401
theorem B466287 : Blo 463784 466287 := bstep (se 1 (by rfl) ⟨349715, by rfl⟩ : syracuseStep 466287 = 699431) B699431
theorem B466343 : Blo 463784 466343 := bstep (se 1 (by rfl) ⟨349757, by rfl⟩ : syracuseStep 466343 = 699515) B699515
theorem B110042549 : Blo 463784 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B695801 : Blo 463784 695801 := bstep (se 2 (by rfl) ⟨260925, by rfl⟩ : syracuseStep 695801 = 521851) B521851
theorem B630265 : Blo 463784 630265 := bstep (se 2 (by rfl) ⟨236349, by rfl⟩ : syracuseStep 630265 = 472699) B472699
theorem B466427 : Blo 463784 466427 := bstep (se 1 (by rfl) ⟨349820, by rfl⟩ : syracuseStep 466427 = 699641) B699641
theorem B2989561 : Blo 463784 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B466495 : Blo 463784 466495 := bstep (se 1 (by rfl) ⟨349871, by rfl⟩ : syracuseStep 466495 = 699743) B699743
theorem B466503 : Blo 463784 466503 := bstep (se 1 (by rfl) ⟨349877, by rfl⟩ : syracuseStep 466503 = 699755) B699755
theorem B695903 : Blo 463784 695903 := bstep (se 1 (by rfl) ⟨521927, by rfl⟩ : syracuseStep 695903 = 1043855) B1043855
theorem B466655 : Blo 463784 466655 := bstep (se 1 (by rfl) ⟨349991, by rfl⟩ : syracuseStep 466655 = 699983) B699983
theorem B466735 : Blo 463784 466735 := bstep (se 1 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 466735 = 700103) B700103
theorem B696119 : Blo 463784 696119 := bstep (se 1 (by rfl) ⟨522089, by rfl⟩ : syracuseStep 696119 = 1044179) B1044179
theorem B2662217 : Blo 463784 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B2367305 : Blo 463784 2367305 := bstep (se 2 (by rfl) ⟨887739, by rfl⟩ : syracuseStep 2367305 = 1775479) B1775479
theorem B4857695 : Blo 463784 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B3972959 : Blo 463784 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B466843 : Blo 463784 466843 := bstep (se 1 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 466843 = 700265) B700265
theorem B466895 : Blo 463784 466895 := bstep (se 1 (by rfl) ⟨350171, by rfl⟩ : syracuseStep 466895 = 700343) B700343
theorem B466919 : Blo 463784 466919 := bstep (se 1 (by rfl) ⟨350189, by rfl⟩ : syracuseStep 466919 = 700379) B700379
theorem B4464659 : Blo 463784 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B696425 : Blo 463784 696425 := bstep (se 2 (by rfl) ⟨261159, by rfl⟩ : syracuseStep 696425 = 522319) B522319
theorem B2465963 : Blo 463784 2465963 := bstep (se 1 (by rfl) ⟨1849472, by rfl⟩ : syracuseStep 2465963 = 3698945) B3698945
theorem B467231 : Blo 463784 467231 := bstep (se 1 (by rfl) ⟨350423, by rfl⟩ : syracuseStep 467231 = 700847) B700847
theorem B794971 : Blo 463784 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B467291 : Blo 463784 467291 := bstep (se 1 (by rfl) ⟨350468, by rfl⟩ : syracuseStep 467291 = 700937) B700937
theorem B467311 : Blo 463784 467311 := bstep (se 1 (by rfl) ⟨350483, by rfl⟩ : syracuseStep 467311 = 700967) B700967
theorem B696743 : Blo 463784 696743 := bstep (se 1 (by rfl) ⟨522557, by rfl⟩ : syracuseStep 696743 = 1045115) B1045115
theorem B467367 : Blo 463784 467367 := bstep (se 1 (by rfl) ⟨350525, by rfl⟩ : syracuseStep 467367 = 701051) B701051
theorem B696827 : Blo 463784 696827 := bstep (se 1 (by rfl) ⟨522620, by rfl⟩ : syracuseStep 696827 = 1045241) B1045241
theorem B467451 : Blo 463784 467451 := bstep (se 1 (by rfl) ⟨350588, by rfl⟩ : syracuseStep 467451 = 701177) B701177
theorem B3973643 : Blo 463784 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B467519 : Blo 463784 467519 := bstep (se 1 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 467519 = 701279) B701279
theorem B533063 : Blo 463784 533063 := bstep (se 1 (by rfl) ⟨399797, by rfl⟩ : syracuseStep 533063 = 799595) B799595
theorem B467527 : Blo 463784 467527 := bstep (se 1 (by rfl) ⟨350645, by rfl⟩ : syracuseStep 467527 = 701291) B701291
theorem B1122923 : Blo 463784 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B991865 : Blo 463784 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B696953 : Blo 463784 696953 := bstep (se 2 (by rfl) ⟨261357, by rfl⟩ : syracuseStep 696953 = 522715) B522715
theorem B697007 : Blo 463784 697007 := bstep (se 1 (by rfl) ⟨522755, by rfl⟩ : syracuseStep 697007 = 1045511) B1045511
theorem B631471 : Blo 463784 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B697055 : Blo 463784 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B631519 : Blo 463784 631519 := bstep (se 1 (by rfl) ⟨473639, by rfl⟩ : syracuseStep 631519 = 947279) B947279
theorem B467679 : Blo 463784 467679 := bstep (se 1 (by rfl) ⟨350759, by rfl⟩ : syracuseStep 467679 = 701519) B701519
theorem B467759 : Blo 463784 467759 := bstep (se 1 (by rfl) ⟨350819, by rfl⟩ : syracuseStep 467759 = 701639) B701639
theorem B697319 : Blo 463784 697319 := bstep (se 1 (by rfl) ⟨522989, by rfl⟩ : syracuseStep 697319 = 1045979) B1045979
theorem B697577 : Blo 463784 697577 := bstep (se 2 (by rfl) ⟨261591, by rfl⟩ : syracuseStep 697577 = 523183) B523183
theorem B697631 : Blo 463784 697631 := bstep (se 1 (by rfl) ⟨523223, by rfl⟩ : syracuseStep 697631 = 1046447) B1046447
theorem B992711 : Blo 463784 992711 := bstep (se 1 (by rfl) ⟨744533, by rfl⟩ : syracuseStep 992711 = 1489067) B1489067
theorem B697799 : Blo 463784 697799 := bstep (se 1 (by rfl) ⟨523349, by rfl⟩ : syracuseStep 697799 = 1046699) B1046699
theorem B894559 : Blo 463784 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B698153 : Blo 463784 698153 := bstep (se 2 (by rfl) ⟨261807, by rfl⟩ : syracuseStep 698153 = 523615) B523615
theorem B698159 : Blo 463784 698159 := bstep (se 1 (by rfl) ⟨523619, by rfl⟩ : syracuseStep 698159 = 1047239) B1047239
theorem B3188585 : Blo 463784 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B698633 : Blo 463784 698633 := bstep (se 2 (by rfl) ⟨261987, by rfl⟩ : syracuseStep 698633 = 523975) B523975
theorem B698735 : Blo 463784 698735 := bstep (se 1 (by rfl) ⟨524051, by rfl⟩ : syracuseStep 698735 = 1048103) B1048103
theorem B1321427 : Blo 463784 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B698951 : Blo 463784 698951 := bstep (se 1 (by rfl) ⟨524213, by rfl⟩ : syracuseStep 698951 = 1048427) B1048427
theorem B698987 : Blo 463784 698987 := bstep (se 1 (by rfl) ⟨524240, by rfl⟩ : syracuseStep 698987 = 1048481) B1048481
theorem B699215 : Blo 463784 699215 := bstep (se 1 (by rfl) ⟨524411, by rfl⟩ : syracuseStep 699215 = 1048823) B1048823
theorem B1321883 : Blo 463784 1321883 := bstep (se 1 (by rfl) ⟨991412, by rfl⟩ : syracuseStep 1321883 = 1982825) B1982825
theorem B621849635 : Blo 463784 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B699611 : Blo 463784 699611 := bstep (se 1 (by rfl) ⟨524708, by rfl⟩ : syracuseStep 699611 = 1049417) B1049417
theorem B699785 : Blo 463784 699785 := bstep (se 2 (by rfl) ⟨262419, by rfl⟩ : syracuseStep 699785 = 524839) B524839
theorem B995051 : Blo 463784 995051 := bstep (se 1 (by rfl) ⟨746288, by rfl⟩ : syracuseStep 995051 = 1492577) B1492577
theorem B700139 : Blo 463784 700139 := bstep (se 1 (by rfl) ⟨525104, by rfl⟩ : syracuseStep 700139 = 1050209) B1050209
theorem B700367 : Blo 463784 700367 := bstep (se 1 (by rfl) ⟨525275, by rfl⟩ : syracuseStep 700367 = 1050551) B1050551
theorem B700763 : Blo 463784 700763 := bstep (se 1 (by rfl) ⟨525572, by rfl⟩ : syracuseStep 700763 = 1051145) B1051145
theorem B15151535 : Blo 463784 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B700991 : Blo 463784 700991 := bstep (se 1 (by rfl) ⟨525743, by rfl⟩ : syracuseStep 700991 = 1051487) B1051487
theorem B701111 : Blo 463784 701111 := bstep (se 1 (by rfl) ⟨525833, by rfl⟩ : syracuseStep 701111 = 1051667) B1051667
theorem B996239 : Blo 463784 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B701339 : Blo 463784 701339 := bstep (se 1 (by rfl) ⟨526004, by rfl⟩ : syracuseStep 701339 = 1052009) B1052009
theorem B1815527 : Blo 463784 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B3781847 : Blo 463784 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B537895 : Blo 463784 537895 := bstep (se 1 (by rfl) ⟨403421, by rfl⟩ : syracuseStep 537895 = 806843) B806843
theorem B9058007 : Blo 463784 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B8960381 : Blo 463784 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B1685927 : Blo 463784 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B1325641 : Blo 463784 1325641 := bstep (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) B994231
theorem B998315 : Blo 463784 998315 := bstep (se 1 (by rfl) ⟨748736, by rfl⟩ : syracuseStep 998315 = 1497473) B1497473
theorem B4767113 : Blo 463784 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B21052853 : Blo 463784 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B3522041 : Blo 463784 3522041 := bstep (se 2 (by rfl) ⟨1320765, by rfl⟩ : syracuseStep 3522041 = 2641531) B2641531
theorem B998905 : Blo 463784 998905 := bstep (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) B749179
theorem B2244307 : Blo 463784 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B1491527 : Blo 463784 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B3785287 : Blo 463784 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B10240685 : Blo 463784 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B1983199 : Blo 463784 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B1885331 : Blo 463784 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B7947557 : Blo 463784 7947557 := bstep (se 4 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 7947557 = 1490167) B1490167
theorem B7161331 : Blo 463784 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B7161871 : Blo 463784 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B2508995 : Blo 463784 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B4245821 : Blo 463784 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B8604107 : Blo 463784 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B3525443 : Blo 463784 3525443 := bstep (se 1 (by rfl) ⟨2644082, by rfl⟩ : syracuseStep 3525443 = 5288165) B5288165
theorem B25873843 : Blo 463784 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B1822139 : Blo 463784 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B1330631 : Blo 463784 1330631 := bstep (se 1 (by rfl) ⟨997973, by rfl⟩ : syracuseStep 1330631 = 1995947) B1995947
theorem B2510767 : Blo 463784 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B3625523 : Blo 463784 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B2348189 : Blo 463784 2348189 := bstep (se 3 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 2348189 = 880571) B880571
theorem B7558505 : Blo 463784 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B2873017 : Blo 463784 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B546791 : Blo 463784 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B1988803 : Blo 463784 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B1988873 : Blo 463784 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B1988975 : Blo 463784 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B2349485 : Blo 463784 2349485 := bstep (se 3 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 2349485 = 881057) B881057
theorem B5954107 : Blo 463784 5954107 := bstep (se 1 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 5954107 = 8931161) B8931161
theorem B2349647 : Blo 463784 2349647 := bstep (se 1 (by rfl) ⟨1762235, by rfl⟩ : syracuseStep 2349647 = 3524471) B3524471
theorem B940727 : Blo 463784 940727 := bstep (se 1 (by rfl) ⟨705545, by rfl⟩ : syracuseStep 940727 = 1411091) B1411091
theorem B7527107 : Blo 463784 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1006811 : Blo 463784 1006811 := bstep (se 1 (by rfl) ⟨755108, by rfl⟩ : syracuseStep 1006811 = 1510217) B1510217
theorem B2351105 : Blo 463784 2351105 := bstep (se 2 (by rfl) ⟨881664, by rfl⟩ : syracuseStep 2351105 = 1763329) B1763329
theorem B8708147 : Blo 463784 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B1761385 : Blo 463784 1761385 := bstep (se 2 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 1761385 = 1321039) B1321039
theorem B1695953 : Blo 463784 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B4251953 : Blo 463784 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B3531275 : Blo 463784 3531275 := bstep (se 1 (by rfl) ⟨2648456, by rfl⟩ : syracuseStep 3531275 = 5296913) B5296913
theorem B10216145 : Blo 463784 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B2024185 : Blo 463784 2024185 := bstep (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) B1518139
theorem B2351915 : Blo 463784 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B3990455 : Blo 463784 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B1532903 : Blo 463784 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B1565945 : Blo 463784 1565945 := bstep (se 2 (by rfl) ⟨587229, by rfl⟩ : syracuseStep 1565945 = 1174459) B1174459
theorem B1566215 : Blo 463784 1566215 := bstep (se 1 (by rfl) ⟨1174661, by rfl⟩ : syracuseStep 1566215 = 2349323) B2349323
theorem B2647889 : Blo 463784 2647889 := bstep (se 2 (by rfl) ⟨992958, by rfl⟩ : syracuseStep 2647889 = 1985917) B1985917
theorem B7956305 : Blo 463784 7956305 := bstep (se 2 (by rfl) ⟨2983614, by rfl⟩ : syracuseStep 7956305 = 5967229) B5967229
theorem B11888531 : Blo 463784 11888531 := bstep (se 1 (by rfl) ⟨8916398, by rfl⟩ : syracuseStep 11888531 = 17832797) B17832797
theorem B3827897 : Blo 463784 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B1567187 : Blo 463784 1567187 := bstep (se 1 (by rfl) ⟨1175390, by rfl⟩ : syracuseStep 1567187 = 2350781) B2350781
theorem B1567295 : Blo 463784 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B5106349 : Blo 463784 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B2353859 : Blo 463784 2353859 := bstep (se 1 (by rfl) ⟨1765394, by rfl⟩ : syracuseStep 2353859 = 3530789) B3530789
theorem B945067 : Blo 463784 945067 := bstep (se 1 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 945067 = 1417601) B1417601
theorem B1272955 : Blo 463784 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B1043675 : Blo 463784 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B1043873 : Blo 463784 1043873 := bstep (se 2 (by rfl) ⟨391452, by rfl⟩ : syracuseStep 1043873 = 782905) B782905
theorem B1174945 : Blo 463784 1174945 := bstep (se 2 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 1174945 = 881209) B881209
theorem B4255163 : Blo 463784 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B945851 : Blo 463784 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B4484807 : Blo 463784 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B1044431 : Blo 463784 1044431 := bstep (se 1 (by rfl) ⟨783323, by rfl⟩ : syracuseStep 1044431 = 1566647) B1566647
theorem B26570753 : Blo 463784 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B7991297 : Blo 463784 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B1044809 : Blo 463784 1044809 := bstep (se 2 (by rfl) ⟨391803, by rfl⟩ : syracuseStep 1044809 = 783607) B783607
theorem B1044827 : Blo 463784 1044827 := bstep (se 1 (by rfl) ⟨783620, by rfl⟩ : syracuseStep 1044827 = 1567241) B1567241
theorem B1569131 : Blo 463784 1569131 := bstep (se 1 (by rfl) ⟨1176848, by rfl⟩ : syracuseStep 1569131 = 2353697) B2353697
theorem B1176059 : Blo 463784 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B1569401 : Blo 463784 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B14480117 : Blo 463784 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B1045403 : Blo 463784 1045403 := bstep (se 1 (by rfl) ⟨784052, by rfl⟩ : syracuseStep 1045403 = 1568105) B1568105
theorem B1045601 : Blo 463784 1045601 := bstep (se 2 (by rfl) ⟨392100, by rfl⟩ : syracuseStep 1045601 = 784201) B784201
theorem B1045799 : Blo 463784 1045799 := bstep (se 1 (by rfl) ⟨784349, by rfl⟩ : syracuseStep 1045799 = 1568699) B1568699
theorem B1177031 : Blo 463784 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B1996321 : Blo 463784 1996321 := bstep (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) B1497241
theorem B1046177 : Blo 463784 1046177 := bstep (se 2 (by rfl) ⟨392316, by rfl⟩ : syracuseStep 1046177 = 784633) B784633
theorem B522031 : Blo 463784 522031 := bstep (se 1 (by rfl) ⟨391523, by rfl⟩ : syracuseStep 522031 = 783047) B783047
theorem B522139 : Blo 463784 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B587675 : Blo 463784 587675 := bstep (se 1 (by rfl) ⟨440756, by rfl⟩ : syracuseStep 587675 = 881513) B881513
theorem B1046537 : Blo 463784 1046537 := bstep (se 2 (by rfl) ⟨392451, by rfl⟩ : syracuseStep 1046537 = 784903) B784903
theorem B9599077 : Blo 463784 9599077 := bstep (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) B1799827
theorem B1177811 : Blo 463784 1177811 := bstep (se 1 (by rfl) ⟨883358, by rfl⟩ : syracuseStep 1177811 = 1766717) B1766717
theorem B1767689 : Blo 463784 1767689 := bstep (se 2 (by rfl) ⟨662883, by rfl⟩ : syracuseStep 1767689 = 1325767) B1325767
theorem B522535 : Blo 463784 522535 := bstep (se 1 (by rfl) ⟨391901, by rfl⟩ : syracuseStep 522535 = 783803) B783803
theorem B522607 : Blo 463784 522607 := bstep (se 1 (by rfl) ⟨391955, by rfl⟩ : syracuseStep 522607 = 783911) B783911
theorem B883055 : Blo 463784 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B1571183 : Blo 463784 1571183 := bstep (se 1 (by rfl) ⟨1178387, by rfl⟩ : syracuseStep 1571183 = 2356775) B2356775
theorem B1046951 : Blo 463784 1046951 := bstep (se 1 (by rfl) ⟨785213, by rfl⟩ : syracuseStep 1046951 = 1570427) B1570427
theorem B1178023 : Blo 463784 1178023 := bstep (se 1 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 1178023 = 1767035) B1767035
theorem B2357747 : Blo 463784 2357747 := bstep (se 1 (by rfl) ⟨1768310, by rfl⟩ : syracuseStep 2357747 = 3536621) B3536621
theorem B1047059 : Blo 463784 1047059 := bstep (se 1 (by rfl) ⟨785294, by rfl⟩ : syracuseStep 1047059 = 1570589) B1570589
theorem B522823 : Blo 463784 522823 := bstep (se 1 (by rfl) ⟨392117, by rfl⟩ : syracuseStep 522823 = 784235) B784235
theorem B1047113 : Blo 463784 1047113 := bstep (se 2 (by rfl) ⟨392667, by rfl⟩ : syracuseStep 1047113 = 785335) B785335
theorem B1178185 : Blo 463784 1178185 := bstep (se 2 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 1178185 = 883639) B883639
theorem B20183687 : Blo 463784 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B785119 : Blo 463784 785119 := bstep (se 1 (by rfl) ⟨588839, by rfl⟩ : syracuseStep 785119 = 1177679) B1177679
theorem B3013519 : Blo 463784 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B1997723 : Blo 463784 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B1047527 : Blo 463784 1047527 := bstep (se 1 (by rfl) ⟨785645, by rfl⟩ : syracuseStep 1047527 = 1571291) B1571291
theorem B2358395 : Blo 463784 2358395 := bstep (se 1 (by rfl) ⟨1768796, by rfl⟩ : syracuseStep 2358395 = 3537593) B3537593
theorem B785551 : Blo 463784 785551 := bstep (se 1 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 785551 = 1178327) B1178327
theorem B1277117 : Blo 463784 1277117 := bstep (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) B478919
theorem B1178975 : Blo 463784 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B1047905 : Blo 463784 1047905 := bstep (se 2 (by rfl) ⟨392964, by rfl⟩ : syracuseStep 1047905 = 785929) B785929
theorem B785801 : Blo 463784 785801 := bstep (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) B589351
theorem B523687 : Blo 463784 523687 := bstep (se 1 (by rfl) ⟨392765, by rfl⟩ : syracuseStep 523687 = 785531) B785531
theorem B1047995 : Blo 463784 1047995 := bstep (se 1 (by rfl) ⟨785996, by rfl⟩ : syracuseStep 1047995 = 1571993) B1571993
theorem B2653721 : Blo 463784 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B1048121 : Blo 463784 1048121 := bstep (se 2 (by rfl) ⟨393045, by rfl⟩ : syracuseStep 1048121 = 786091) B786091
theorem B884459 : Blo 463784 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B1572587 : Blo 463784 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B2359043 : Blo 463784 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B786233 : Blo 463784 786233 := bstep (se 2 (by rfl) ⟨294837, by rfl⟩ : syracuseStep 786233 = 589675) B589675
theorem B524263 : Blo 463784 524263 := bstep (se 1 (by rfl) ⟨393197, by rfl⟩ : syracuseStep 524263 = 786395) B786395
theorem B786719 : Blo 463784 786719 := bstep (se 1 (by rfl) ⟨590039, by rfl⟩ : syracuseStep 786719 = 1180079) B1180079
theorem B1049039 : Blo 463784 1049039 := bstep (se 1 (by rfl) ⟨786779, by rfl⟩ : syracuseStep 1049039 = 1573559) B1573559
theorem B8520187 : Blo 463784 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B1573505 : Blo 463784 1573505 := bstep (se 2 (by rfl) ⟨590064, by rfl⟩ : syracuseStep 1573505 = 1180129) B1180129
theorem B5047049 : Blo 463784 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B1573775 : Blo 463784 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B1770407 : Blo 463784 1770407 := bstep (se 1 (by rfl) ⟨1327805, by rfl⟩ : syracuseStep 1770407 = 2655611) B2655611
theorem B787367 : Blo 463784 787367 := bstep (se 1 (by rfl) ⟨590525, by rfl⟩ : syracuseStep 787367 = 1181051) B1181051
theorem B525307 : Blo 463784 525307 := bstep (se 1 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 525307 = 787961) B787961
theorem B787529 : Blo 463784 787529 := bstep (se 2 (by rfl) ⟨295323, by rfl⟩ : syracuseStep 787529 = 590647) B590647
theorem B1180777 : Blo 463784 1180777 := bstep (se 2 (by rfl) ⟨442791, by rfl⟩ : syracuseStep 1180777 = 885583) B885583
theorem B1049705 : Blo 463784 1049705 := bstep (se 2 (by rfl) ⟨393639, by rfl⟩ : syracuseStep 1049705 = 787279) B787279
theorem B525487 : Blo 463784 525487 := bstep (se 1 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 525487 = 788231) B788231
theorem B1770923 : Blo 463784 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B1574315 : Blo 463784 1574315 := bstep (se 1 (by rfl) ⟨1180736, by rfl⟩ : syracuseStep 1574315 = 2361473) B2361473
theorem B1672663 : Blo 463784 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B788089 : Blo 463784 788089 := bstep (se 2 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 788089 = 591067) B591067
theorem B5736071 : Blo 463784 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B525991 : Blo 463784 525991 := bstep (se 1 (by rfl) ⟨394493, by rfl⟩ : syracuseStep 525991 = 788987) B788987
theorem B1050335 : Blo 463784 1050335 := bstep (se 1 (by rfl) ⟨787751, by rfl⟩ : syracuseStep 1050335 = 1575503) B1575503
theorem B2361149 : Blo 463784 2361149 := bstep (se 3 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 2361149 = 885431) B885431
theorem B1181537 : Blo 463784 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B1574855 : Blo 463784 1574855 := bstep (se 1 (by rfl) ⟨1181141, by rfl⟩ : syracuseStep 1574855 = 2362283) B2362283
theorem B788575 : Blo 463784 788575 := bstep (se 1 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 788575 = 1182863) B1182863
theorem B1181911 : Blo 463784 1181911 := bstep (se 1 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 1181911 = 1772867) B1772867
theorem B1214759 : Blo 463784 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B887087 : Blo 463784 887087 := bstep (se 1 (by rfl) ⟨665315, by rfl⟩ : syracuseStep 887087 = 1330631) B1330631
theorem B2656637 : Blo 463784 2656637 := bstep (se 3 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 2656637 = 996239) B996239
theorem B1182215 : Blo 463784 1182215 := bstep (se 1 (by rfl) ⟨886661, by rfl⟩ : syracuseStep 1182215 = 1773323) B1773323
theorem B1182235 : Blo 463784 1182235 := bstep (se 1 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 1182235 = 1773353) B1773353
theorem B1051163 : Blo 463784 1051163 := bstep (se 1 (by rfl) ⟨788372, by rfl⟩ : syracuseStep 1051163 = 1576745) B1576745
theorem B1116703 : Blo 463784 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B1772063 : Blo 463784 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B1575611 : Blo 463784 1575611 := bstep (se 1 (by rfl) ⟨1181708, by rfl⟩ : syracuseStep 1575611 = 2363417) B2363417
theorem B1183643 : Blo 463784 1183643 := bstep (se 1 (by rfl) ⟨887732, by rfl⟩ : syracuseStep 1183643 = 1775465) B1775465
theorem B2363579 : Blo 463784 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B627151 : Blo 463784 627151 := bstep (se 1 (by rfl) ⟨470363, by rfl⟩ : syracuseStep 627151 = 940727) B940727
theorem B24154685 : Blo 463784 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1577555 : Blo 463784 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B2364065 : Blo 463784 2364065 := bstep (se 2 (by rfl) ⟨886524, by rfl⟩ : syracuseStep 2364065 = 1773049) B1773049
theorem B2364227 : Blo 463784 2364227 := bstep (se 1 (by rfl) ⟨1773170, by rfl⟩ : syracuseStep 2364227 = 3546341) B3546341
theorem B3019655 : Blo 463784 3019655 := bstep (se 1 (by rfl) ⟨2264741, by rfl⟩ : syracuseStep 3019655 = 4529483) B4529483
theorem B463867 : Blo 463784 463867 := bstep (se 1 (by rfl) ⟨347900, by rfl⟩ : syracuseStep 463867 = 695801) B695801
theorem B463935 : Blo 463784 463935 := bstep (se 1 (by rfl) ⟨347951, by rfl⟩ : syracuseStep 463935 = 695903) B695903
theorem B464079 : Blo 463784 464079 := bstep (se 1 (by rfl) ⟨348059, by rfl⟩ : syracuseStep 464079 = 696119) B696119
theorem B1774811 : Blo 463784 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B1578203 : Blo 463784 1578203 := bstep (se 1 (by rfl) ⟨1183652, by rfl⟩ : syracuseStep 1578203 = 2367305) B2367305
theorem B3347689 : Blo 463784 3347689 := bstep (se 2 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 3347689 = 2510767) B2510767
theorem B5805431 : Blo 463784 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B464283 : Blo 463784 464283 := bstep (se 1 (by rfl) ⟨348212, by rfl⟩ : syracuseStep 464283 = 696425) B696425
theorem B1643975 : Blo 463784 1643975 := bstep (se 1 (by rfl) ⟨1232981, by rfl⟩ : syracuseStep 1643975 = 2465963) B2465963
theorem B2365037 : Blo 463784 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B464495 : Blo 463784 464495 := bstep (se 1 (by rfl) ⟨348371, by rfl⟩ : syracuseStep 464495 = 696743) B696743
theorem B464551 : Blo 463784 464551 := bstep (se 1 (by rfl) ⟨348413, by rfl⟩ : syracuseStep 464551 = 696827) B696827
theorem B464635 : Blo 463784 464635 := bstep (se 1 (by rfl) ⟨348476, by rfl⟩ : syracuseStep 464635 = 696953) B696953
theorem B464671 : Blo 463784 464671 := bstep (se 1 (by rfl) ⟨348503, by rfl⟩ : syracuseStep 464671 = 697007) B697007
theorem B464703 : Blo 463784 464703 := bstep (se 1 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 464703 = 697055) B697055
theorem B2660303 : Blo 463784 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B464879 : Blo 463784 464879 := bstep (se 1 (by rfl) ⟨348659, by rfl⟩ : syracuseStep 464879 = 697319) B697319
theorem B465051 : Blo 463784 465051 := bstep (se 1 (by rfl) ⟨348788, by rfl⟩ : syracuseStep 465051 = 697577) B697577
theorem B465087 : Blo 463784 465087 := bstep (se 1 (by rfl) ⟨348815, by rfl⟩ : syracuseStep 465087 = 697631) B697631
theorem B661807 : Blo 463784 661807 := bstep (se 1 (by rfl) ⟨496355, by rfl⟩ : syracuseStep 661807 = 992711) B992711
theorem B465199 : Blo 463784 465199 := bstep (se 1 (by rfl) ⟨348899, by rfl⟩ : syracuseStep 465199 = 697799) B697799
theorem B465435 : Blo 463784 465435 := bstep (se 1 (by rfl) ⟨349076, by rfl⟩ : syracuseStep 465435 = 698153) B698153
theorem B465439 : Blo 463784 465439 := bstep (se 1 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 465439 = 698159) B698159
theorem B465755 : Blo 463784 465755 := bstep (se 1 (by rfl) ⟨349316, by rfl⟩ : syracuseStep 465755 = 698633) B698633
theorem B465823 : Blo 463784 465823 := bstep (se 1 (by rfl) ⟨349367, by rfl⟩ : syracuseStep 465823 = 698735) B698735
theorem B465967 : Blo 463784 465967 := bstep (se 1 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 465967 = 698951) B698951
theorem B465991 : Blo 463784 465991 := bstep (se 1 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 465991 = 698987) B698987
theorem B466143 : Blo 463784 466143 := bstep (se 1 (by rfl) ⟨349607, by rfl⟩ : syracuseStep 466143 = 699215) B699215
theorem B2661761 : Blo 463784 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B695783 : Blo 463784 695783 := bstep (se 1 (by rfl) ⟨521837, by rfl⟩ : syracuseStep 695783 = 1043675) B1043675
theorem B466407 : Blo 463784 466407 := bstep (se 1 (by rfl) ⟨349805, by rfl⟩ : syracuseStep 466407 = 699611) B699611
theorem B466523 : Blo 463784 466523 := bstep (se 1 (by rfl) ⟨349892, by rfl⟩ : syracuseStep 466523 = 699785) B699785
theorem B695915 : Blo 463784 695915 := bstep (se 1 (by rfl) ⟨521936, by rfl⟩ : syracuseStep 695915 = 1043873) B1043873
theorem B696041 : Blo 463784 696041 := bstep (se 2 (by rfl) ⟨261015, by rfl⟩ : syracuseStep 696041 = 522031) B522031
theorem B2989871 : Blo 463784 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B466759 : Blo 463784 466759 := bstep (se 1 (by rfl) ⟨350069, by rfl⟩ : syracuseStep 466759 = 700139) B700139
theorem B696185 : Blo 463784 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B696287 : Blo 463784 696287 := bstep (se 1 (by rfl) ⟨522215, by rfl⟩ : syracuseStep 696287 = 1044431) B1044431
theorem B466911 : Blo 463784 466911 := bstep (se 1 (by rfl) ⟨350183, by rfl⟩ : syracuseStep 466911 = 700367) B700367
theorem B696539 : Blo 463784 696539 := bstep (se 1 (by rfl) ⟨522404, by rfl⟩ : syracuseStep 696539 = 1044809) B1044809
theorem B696551 : Blo 463784 696551 := bstep (se 1 (by rfl) ⟨522413, by rfl⟩ : syracuseStep 696551 = 1044827) B1044827
theorem B467175 : Blo 463784 467175 := bstep (se 1 (by rfl) ⟨350381, by rfl⟩ : syracuseStep 467175 = 700763) B700763
theorem B10101023 : Blo 463784 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B467327 : Blo 463784 467327 := bstep (se 1 (by rfl) ⟨350495, by rfl⟩ : syracuseStep 467327 = 700991) B700991
theorem B696713 : Blo 463784 696713 := bstep (se 2 (by rfl) ⟨261267, by rfl⟩ : syracuseStep 696713 = 522535) B522535
theorem B467407 : Blo 463784 467407 := bstep (se 1 (by rfl) ⟨350555, by rfl⟩ : syracuseStep 467407 = 701111) B701111
theorem B696809 : Blo 463784 696809 := bstep (se 2 (by rfl) ⟨261303, by rfl⟩ : syracuseStep 696809 = 522607) B522607
theorem B696935 : Blo 463784 696935 := bstep (se 1 (by rfl) ⟨522701, by rfl⟩ : syracuseStep 696935 = 1045403) B1045403
theorem B467559 : Blo 463784 467559 := bstep (se 1 (by rfl) ⟨350669, by rfl⟩ : syracuseStep 467559 = 701339) B701339
theorem B697067 : Blo 463784 697067 := bstep (se 1 (by rfl) ⟨522800, by rfl⟩ : syracuseStep 697067 = 1045601) B1045601
theorem B7938809 : Blo 463784 7938809 := bstep (se 2 (by rfl) ⟨2977053, by rfl⟩ : syracuseStep 7938809 = 5954107) B5954107
theorem B697097 : Blo 463784 697097 := bstep (se 2 (by rfl) ⟨261411, by rfl⟩ : syracuseStep 697097 = 522823) B522823
theorem B697199 : Blo 463784 697199 := bstep (se 1 (by rfl) ⟨522899, by rfl⟩ : syracuseStep 697199 = 1045799) B1045799
theorem B697451 : Blo 463784 697451 := bstep (se 1 (by rfl) ⟨523088, by rfl⟩ : syracuseStep 697451 = 1046177) B1046177
theorem B697691 : Blo 463784 697691 := bstep (se 1 (by rfl) ⟨523268, by rfl⟩ : syracuseStep 697691 = 1046537) B1046537
theorem B5973587 : Blo 463784 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B697967 : Blo 463784 697967 := bstep (se 1 (by rfl) ⟨523475, by rfl⟩ : syracuseStep 697967 = 1046951) B1046951
theorem B1123951 : Blo 463784 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B698039 : Blo 463784 698039 := bstep (se 1 (by rfl) ⟨523529, by rfl⟩ : syracuseStep 698039 = 1047059) B1047059
theorem B698075 : Blo 463784 698075 := bstep (se 1 (by rfl) ⟨523556, by rfl⟩ : syracuseStep 698075 = 1047113) B1047113
theorem B698249 : Blo 463784 698249 := bstep (se 2 (by rfl) ⟨261843, by rfl⟩ : syracuseStep 698249 = 523687) B523687
theorem B665543 : Blo 463784 665543 := bstep (se 1 (by rfl) ⟨499157, by rfl⟩ : syracuseStep 665543 = 998315) B998315
theorem B698351 : Blo 463784 698351 := bstep (se 1 (by rfl) ⟨523763, by rfl⟩ : syracuseStep 698351 = 1047527) B1047527
theorem B1321085 : Blo 463784 1321085 := bstep (se 3 (by rfl) ⟨247703, by rfl⟩ : syracuseStep 1321085 = 495407) B495407
theorem B698603 : Blo 463784 698603 := bstep (se 1 (by rfl) ⟨523952, by rfl⟩ : syracuseStep 698603 = 1047905) B1047905
theorem B2992409 : Blo 463784 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B14035235 : Blo 463784 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B698663 : Blo 463784 698663 := bstep (se 1 (by rfl) ⟨523997, by rfl⟩ : syracuseStep 698663 = 1047995) B1047995
theorem B698747 : Blo 463784 698747 := bstep (se 1 (by rfl) ⟨524060, by rfl⟩ : syracuseStep 698747 = 1048121) B1048121
theorem B699017 : Blo 463784 699017 := bstep (se 2 (by rfl) ⟨262131, by rfl⟩ : syracuseStep 699017 = 524263) B524263
theorem B699191 : Blo 463784 699191 := bstep (se 1 (by rfl) ⟨524393, by rfl⟩ : syracuseStep 699191 = 1048787) B1048787
theorem B699227 : Blo 463784 699227 := bstep (se 1 (by rfl) ⟨524420, by rfl⟩ : syracuseStep 699227 = 1048841) B1048841
theorem B699371 : Blo 463784 699371 := bstep (se 1 (by rfl) ⟨524528, by rfl⟩ : syracuseStep 699371 = 1049057) B1049057
theorem B994351 : Blo 463784 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B6827123 : Blo 463784 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B1059961 : Blo 463784 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B699575 : Blo 463784 699575 := bstep (se 1 (by rfl) ⟨524681, by rfl⟩ : syracuseStep 699575 = 1049363) B1049363
theorem B699815 : Blo 463784 699815 := bstep (se 1 (by rfl) ⟨524861, by rfl⟩ : syracuseStep 699815 = 1049723) B1049723
theorem B1256887 : Blo 463784 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B699899 : Blo 463784 699899 := bstep (se 1 (by rfl) ⟨524924, by rfl⟩ : syracuseStep 699899 = 1049849) B1049849
theorem B699995 : Blo 463784 699995 := bstep (se 1 (by rfl) ⟨524996, by rfl⟩ : syracuseStep 699995 = 1049993) B1049993
theorem B2698913 : Blo 463784 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B700079 : Blo 463784 700079 := bstep (se 1 (by rfl) ⟨525059, by rfl⟩ : syracuseStep 700079 = 1050119) B1050119
theorem B700199 : Blo 463784 700199 := bstep (se 1 (by rfl) ⟨525149, by rfl⟩ : syracuseStep 700199 = 1050299) B1050299
theorem B700283 : Blo 463784 700283 := bstep (se 1 (by rfl) ⟨525212, by rfl⟩ : syracuseStep 700283 = 1050425) B1050425
theorem B1421501 : Blo 463784 1421501 := bstep (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) B533063
theorem B2830547 : Blo 463784 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B700703 : Blo 463784 700703 := bstep (se 1 (by rfl) ⟨525527, by rfl⟩ : syracuseStep 700703 = 1051055) B1051055
theorem B700727 : Blo 463784 700727 := bstep (se 1 (by rfl) ⟨525545, by rfl⟩ : syracuseStep 700727 = 1051091) B1051091
theorem B700799 : Blo 463784 700799 := bstep (se 1 (by rfl) ⟨525599, by rfl⟩ : syracuseStep 700799 = 1051199) B1051199
theorem B700871 : Blo 463784 700871 := bstep (se 1 (by rfl) ⟨525653, by rfl⟩ : syracuseStep 700871 = 1051307) B1051307
theorem B9548441 : Blo 463784 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B3978017 : Blo 463784 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B1192745 : Blo 463784 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B701225 : Blo 463784 701225 := bstep (se 2 (by rfl) ⟨262959, by rfl⟩ : syracuseStep 701225 = 525919) B525919
theorem B701231 : Blo 463784 701231 := bstep (se 1 (by rfl) ⟨525923, by rfl⟩ : syracuseStep 701231 = 1051847) B1051847
theorem B701351 : Blo 463784 701351 := bstep (se 1 (by rfl) ⟨526013, by rfl⟩ : syracuseStep 701351 = 1052027) B1052027
theorem B701435 : Blo 463784 701435 := bstep (se 1 (by rfl) ⟨526076, by rfl⟩ : syracuseStep 701435 = 1052153) B1052153
theorem B701495 : Blo 463784 701495 := bstep (se 1 (by rfl) ⟨526121, by rfl⟩ : syracuseStep 701495 = 1052243) B1052243
theorem B1881227 : Blo 463784 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B701615 : Blo 463784 701615 := bstep (se 1 (by rfl) ⟨526211, by rfl⟩ : syracuseStep 701615 = 1052423) B1052423
theorem B9549161 : Blo 463784 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B1685767 : Blo 463784 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B1260089 : Blo 463784 1260089 := bstep (se 2 (by rfl) ⟨472533, by rfl⟩ : syracuseStep 1260089 = 945067) B945067
theorem B12696203 : Blo 463784 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B1325915 : Blo 463784 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B1325983 : Blo 463784 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B671207 : Blo 463784 671207 := bstep (se 1 (by rfl) ⟨503405, by rfl⟩ : syracuseStep 671207 = 1006811) B1006811
theorem B1458109 : Blo 463784 1458109 := bstep (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) B546791
theorem B1130635 : Blo 463784 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B2834635 : Blo 463784 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B20072285 : Blo 463784 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B414566423 : Blo 463784 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B2836775 : Blo 463784 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B17713835 : Blo 463784 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B5327531 : Blo 463784 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B12798769 : Blo 463784 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B9653411 : Blo 463784 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B4018025 : Blo 463784 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B13455791 : Blo 463784 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B1331815 : Blo 463784 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B840353 : Blo 463784 840353 := bstep (se 2 (by rfl) ⟨315132, by rfl⟩ : syracuseStep 840353 = 630265) B630265
theorem B3986081 : Blo 463784 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B1331873 : Blo 463784 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B2348027 : Blo 463784 2348027 := bstep (se 1 (by rfl) ⟨1761020, by rfl⟩ : syracuseStep 2348027 = 3522041) B3522041
theorem B1594811 : Blo 463784 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B2348513 : Blo 463784 2348513 := bstep (se 2 (by rfl) ⟨880692, by rfl⟩ : syracuseStep 2348513 = 1761385) B1761385
theorem B5298371 : Blo 463784 5298371 := bstep (se 1 (by rfl) ⟨3973778, by rfl⟩ : syracuseStep 5298371 = 7947557) B7947557
theorem B841961 : Blo 463784 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B2644265 : Blo 463784 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B2644973 : Blo 463784 2644973 := bstep (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) B991865
theorem B1989623 : Blo 463784 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B2350295 : Blo 463784 2350295 := bstep (se 1 (by rfl) ⟨1762721, by rfl⟩ : syracuseStep 2350295 = 3525443) B3525443
theorem B745033 : Blo 463784 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B5299829 : Blo 463784 5299829 := bstep (se 5 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 5299829 = 496859) B496859
theorem B2121527 : Blo 463784 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B4087741 : Blo 463784 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B2973955 : Blo 463784 2973955 := bstep (se 1 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 2973955 = 4460933) B4460933
theorem B2417015 : Blo 463784 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B10084925 : Blo 463784 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B1565459 : Blo 463784 1565459 := bstep (se 1 (by rfl) ⟨1174094, by rfl⟩ : syracuseStep 1565459 = 2348189) B2348189
theorem B2646863 : Blo 463784 2646863 := bstep (se 1 (by rfl) ⟨1985147, by rfl⟩ : syracuseStep 2646863 = 3970295) B3970295
theorem B6808465 : Blo 463784 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B5039003 : Blo 463784 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B3368101 : Blo 463784 3368101 := bstep (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) B631519
theorem B2647363 : Blo 463784 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B1697273 : Blo 463784 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1566323 : Blo 463784 1566323 := bstep (se 1 (by rfl) ⟨1174742, by rfl⟩ : syracuseStep 1566323 = 2349485) B2349485
theorem B1566431 : Blo 463784 1566431 := bstep (se 1 (by rfl) ⟨1174823, by rfl⟩ : syracuseStep 1566431 = 2349647) B2349647
theorem B1566593 : Blo 463784 1566593 := bstep (se 2 (by rfl) ⟨587472, by rfl⟩ : syracuseStep 1566593 = 1174945) B1174945
theorem B34498457 : Blo 463784 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B2844953 : Blo 463784 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B73361699 : Blo 463784 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B1567133 : Blo 463784 1567133 := bstep (se 3 (by rfl) ⟨293837, by rfl⟩ : syracuseStep 1567133 = 587675) B587675
theorem B2648639 : Blo 463784 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B3238463 : Blo 463784 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B1567403 : Blo 463784 1567403 := bstep (se 1 (by rfl) ⟨1175552, by rfl⟩ : syracuseStep 1567403 = 2351105) B2351105
theorem B2976439 : Blo 463784 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B2354183 : Blo 463784 2354183 := bstep (se 1 (by rfl) ⟨1765637, by rfl⟩ : syracuseStep 2354183 = 3531275) B3531275
theorem B2649095 : Blo 463784 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B748615 : Blo 463784 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B6810763 : Blo 463784 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B1567943 : Blo 463784 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B5991833 : Blo 463784 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B1043963 : Blo 463784 1043963 := bstep (se 1 (by rfl) ⟨782972, by rfl⟩ : syracuseStep 1043963 = 1565945) B1565945
theorem B1044143 : Blo 463784 1044143 := bstep (se 1 (by rfl) ⟨783107, by rfl⟩ : syracuseStep 1044143 = 1566215) B1566215
theorem B1765259 : Blo 463784 1765259 := bstep (se 1 (by rfl) ⟨1323944, by rfl⟩ : syracuseStep 1765259 = 2647889) B2647889
theorem B5304203 : Blo 463784 5304203 := bstep (se 1 (by rfl) ⟨3978152, by rfl⟩ : syracuseStep 5304203 = 7956305) B7956305
theorem B2125723 : Blo 463784 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B7925687 : Blo 463784 7925687 := bstep (se 1 (by rfl) ⟨5944265, by rfl⟩ : syracuseStep 7925687 = 11888531) B11888531
theorem B2551931 : Blo 463784 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B880951 : Blo 463784 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B1044791 : Blo 463784 1044791 := bstep (se 1 (by rfl) ⟨783593, by rfl⟩ : syracuseStep 1044791 = 1567187) B1567187
theorem B1044863 : Blo 463784 1044863 := bstep (se 1 (by rfl) ⟨783647, by rfl⟩ : syracuseStep 1044863 = 1567295) B1567295
theorem B717193 : Blo 463784 717193 := bstep (se 2 (by rfl) ⟨268947, by rfl⟩ : syracuseStep 717193 = 537895) B537895
theorem B1569239 : Blo 463784 1569239 := bstep (se 1 (by rfl) ⟨1176929, by rfl⟩ : syracuseStep 1569239 = 2353859) B2353859
theorem B881255 : Blo 463784 881255 := bstep (se 1 (by rfl) ⟨660941, by rfl⟩ : syracuseStep 881255 = 1321883) B1321883
theorem B3830689 : Blo 463784 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B6387133 : Blo 463784 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B1046087 : Blo 463784 1046087 := bstep (se 1 (by rfl) ⟨784565, by rfl⟩ : syracuseStep 1046087 = 1569131) B1569131
theorem B2651737 : Blo 463784 2651737 := bstep (se 2 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 2651737 = 1988803) B1988803
theorem B784039 : Blo 463784 784039 := bstep (se 1 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 784039 = 1176059) B1176059
theorem B1046267 : Blo 463784 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B882569 : Blo 463784 882569 := bstep (se 2 (by rfl) ⟨330963, by rfl⟩ : syracuseStep 882569 = 661927) B661927
theorem B1570697 : Blo 463784 1570697 := bstep (se 2 (by rfl) ⟨589011, by rfl⟩ : syracuseStep 1570697 = 1178023) B1178023
theorem B1210351 : Blo 463784 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B1570913 : Blo 463784 1570913 := bstep (se 2 (by rfl) ⟨589092, by rfl⟩ : syracuseStep 1570913 = 1178185) B1178185
theorem B1767521 : Blo 463784 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B1046825 : Blo 463784 1046825 := bstep (se 2 (by rfl) ⟨392559, by rfl⟩ : syracuseStep 1046825 = 785119) B785119
theorem B784687 : Blo 463784 784687 := bstep (se 1 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 784687 = 1177031) B1177031
theorem B12712301 : Blo 463784 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B785207 : Blo 463784 785207 := bstep (se 1 (by rfl) ⟨588905, by rfl⟩ : syracuseStep 785207 = 1177811) B1177811
theorem B1178459 : Blo 463784 1178459 := bstep (se 1 (by rfl) ⟨883844, by rfl⟩ : syracuseStep 1178459 = 1767689) B1767689
theorem B1047401 : Blo 463784 1047401 := bstep (se 2 (by rfl) ⟨392775, by rfl⟩ : syracuseStep 1047401 = 785551) B785551
theorem B588703 : Blo 463784 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B1047455 : Blo 463784 1047455 := bstep (se 1 (by rfl) ⟨785591, by rfl⟩ : syracuseStep 1047455 = 1571183) B1571183
theorem B1571831 : Blo 463784 1571831 := bstep (se 1 (by rfl) ⟨1178873, by rfl⟩ : syracuseStep 1571831 = 2357747) B2357747
theorem B2522269 : Blo 463784 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B2358557 : Blo 463784 2358557 := bstep (se 3 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 2358557 = 884459) B884459
theorem B2653469 : Blo 463784 2653469 := bstep (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) B995051
theorem B1572263 : Blo 463784 1572263 := bstep (se 1 (by rfl) ⟨1179197, by rfl⟩ : syracuseStep 1572263 = 2358395) B2358395
theorem B851411 : Blo 463784 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B785983 : Blo 463784 785983 := bstep (se 1 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 785983 = 1178975) B1178975
theorem B523867 : Blo 463784 523867 := bstep (se 1 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 523867 = 785801) B785801
theorem B1769147 : Blo 463784 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B1048391 : Blo 463784 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B1572695 : Blo 463784 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B524155 : Blo 463784 524155 := bstep (se 1 (by rfl) ⟨393116, by rfl⟩ : syracuseStep 524155 = 786233) B786233
theorem B1507513 : Blo 463784 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B524479 : Blo 463784 524479 := bstep (se 1 (by rfl) ⟨393359, by rfl⟩ : syracuseStep 524479 = 786719) B786719
theorem B3965273 : Blo 463784 3965273 := bstep (se 2 (by rfl) ⟨1486977, by rfl⟩ : syracuseStep 3965273 = 2973955) B2973955
theorem B1049003 : Blo 463784 1049003 := bstep (se 1 (by rfl) ⟨786752, by rfl⟩ : syracuseStep 1049003 = 1573505) B1573505
theorem B1049183 : Blo 463784 1049183 := bstep (se 1 (by rfl) ⟨786887, by rfl⟩ : syracuseStep 1049183 = 1573775) B1573775
theorem B1180271 : Blo 463784 1180271 := bstep (se 1 (by rfl) ⟨885203, by rfl⟩ : syracuseStep 1180271 = 1770407) B1770407
theorem B524911 : Blo 463784 524911 := bstep (se 1 (by rfl) ⟨393683, by rfl⟩ : syracuseStep 524911 = 787367) B787367
theorem B525019 : Blo 463784 525019 := bstep (se 1 (by rfl) ⟨393764, by rfl⟩ : syracuseStep 525019 = 787529) B787529
theorem B1180615 : Blo 463784 1180615 := bstep (se 1 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 1180615 = 1770923) B1770923
theorem B1049543 : Blo 463784 1049543 := bstep (se 1 (by rfl) ⟨787157, by rfl⟩ : syracuseStep 1049543 = 1574315) B1574315
theorem B9077953 : Blo 463784 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B1574099 : Blo 463784 1574099 := bstep (se 1 (by rfl) ⟨1180574, by rfl⟩ : syracuseStep 1574099 = 2361149) B2361149
theorem B787691 : Blo 463784 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B1049903 : Blo 463784 1049903 := bstep (se 1 (by rfl) ⟨787427, by rfl⟩ : syracuseStep 1049903 = 1574855) B1574855
theorem B1574369 : Blo 463784 1574369 := bstep (se 2 (by rfl) ⟨590388, by rfl⟩ : syracuseStep 1574369 = 1180777) B1180777
theorem B591391 : Blo 463784 591391 := bstep (se 1 (by rfl) ⟨443543, by rfl⟩ : syracuseStep 591391 = 887087) B887087
theorem B4490801 : Blo 463784 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B1771091 : Blo 463784 1771091 := bstep (se 1 (by rfl) ⟨1328318, by rfl⟩ : syracuseStep 1771091 = 2656637) B2656637
theorem B788143 : Blo 463784 788143 := bstep (se 1 (by rfl) ⟨591107, by rfl⟩ : syracuseStep 788143 = 1182215) B1182215
theorem B1181375 : Blo 463784 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B1050407 : Blo 463784 1050407 := bstep (se 1 (by rfl) ⟨787805, by rfl⟩ : syracuseStep 1050407 = 1575611) B1575611
theorem B2230217 : Blo 463784 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B1050785 : Blo 463784 1050785 := bstep (se 2 (by rfl) ⟨394044, by rfl⟩ : syracuseStep 1050785 = 788089) B788089
theorem B789095 : Blo 463784 789095 := bstep (se 1 (by rfl) ⟨591821, by rfl⟩ : syracuseStep 789095 = 1183643) B1183643
theorem B1575719 : Blo 463784 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B1051433 : Blo 463784 1051433 := bstep (se 2 (by rfl) ⟨394287, by rfl⟩ : syracuseStep 1051433 = 788575) B788575
theorem B1575881 : Blo 463784 1575881 := bstep (se 2 (by rfl) ⟨590955, by rfl⟩ : syracuseStep 1575881 = 1181911) B1181911
theorem B1051703 : Blo 463784 1051703 := bstep (se 1 (by rfl) ⟨788777, by rfl⟩ : syracuseStep 1051703 = 1577555) B1577555
theorem B2657387 : Blo 463784 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B1576043 : Blo 463784 1576043 := bstep (se 1 (by rfl) ⟨1182032, by rfl⟩ : syracuseStep 1576043 = 2364065) B2364065
theorem B887915 : Blo 463784 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B1576151 : Blo 463784 1576151 := bstep (se 1 (by rfl) ⟨1182113, by rfl⟩ : syracuseStep 1576151 = 2364227) B2364227
theorem B1576313 : Blo 463784 1576313 := bstep (se 2 (by rfl) ⟨591117, by rfl⟩ : syracuseStep 1576313 = 1182235) B1182235
theorem B1183207 : Blo 463784 1183207 := bstep (se 1 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 1183207 = 1774811) B1774811
theorem B1052135 : Blo 463784 1052135 := bstep (se 1 (by rfl) ⟨789101, by rfl⟩ : syracuseStep 1052135 = 1578203) B1578203
theorem B3968585 : Blo 463784 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B3870287 : Blo 463784 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B1576691 : Blo 463784 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1773535 : Blo 463784 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B1413281 : Blo 463784 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B9081017 : Blo 463784 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B1774507 : Blo 463784 1774507 := bstep (se 1 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 1774507 = 2661761) B2661761
theorem B463855 : Blo 463784 463855 := bstep (se 1 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 463855 = 695783) B695783
theorem B463943 : Blo 463784 463943 := bstep (se 1 (by rfl) ⟨347957, by rfl⟩ : syracuseStep 463943 = 695915) B695915
theorem B464027 : Blo 463784 464027 := bstep (se 1 (by rfl) ⟨348020, by rfl⟩ : syracuseStep 464027 = 696041) B696041
theorem B1774781 : Blo 463784 1774781 := bstep (se 3 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 1774781 = 665543) B665543
theorem B1414351 : Blo 463784 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B464123 : Blo 463784 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B464191 : Blo 463784 464191 := bstep (se 1 (by rfl) ⟨348143, by rfl⟩ : syracuseStep 464191 = 696287) B696287
theorem B464359 : Blo 463784 464359 := bstep (se 1 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 464359 = 696539) B696539
theorem B464367 : Blo 463784 464367 := bstep (se 1 (by rfl) ⟨348275, by rfl⟩ : syracuseStep 464367 = 696551) B696551
theorem B1611343 : Blo 463784 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B464475 : Blo 463784 464475 := bstep (se 1 (by rfl) ⟨348356, by rfl⟩ : syracuseStep 464475 = 696713) B696713
theorem B464539 : Blo 463784 464539 := bstep (se 1 (by rfl) ⟨348404, by rfl⟩ : syracuseStep 464539 = 696809) B696809
theorem B6723283 : Blo 463784 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B464623 : Blo 463784 464623 := bstep (se 1 (by rfl) ⟨348467, by rfl⟩ : syracuseStep 464623 = 696935) B696935
theorem B464711 : Blo 463784 464711 := bstep (se 1 (by rfl) ⟨348533, by rfl⟩ : syracuseStep 464711 = 697067) B697067
theorem B464731 : Blo 463784 464731 := bstep (se 1 (by rfl) ⟨348548, by rfl⟩ : syracuseStep 464731 = 697097) B697097
theorem B956257 : Blo 463784 956257 := bstep (se 2 (by rfl) ⟨358596, by rfl⟩ : syracuseStep 956257 = 717193) B717193
theorem B464799 : Blo 463784 464799 := bstep (se 1 (by rfl) ⟨348599, by rfl⟩ : syracuseStep 464799 = 697199) B697199
theorem B464967 : Blo 463784 464967 := bstep (se 1 (by rfl) ⟨348725, by rfl⟩ : syracuseStep 464967 = 697451) B697451
theorem B37427293 : Blo 463784 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B1775753 : Blo 463784 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B465127 : Blo 463784 465127 := bstep (se 1 (by rfl) ⟨348845, by rfl⟩ : syracuseStep 465127 = 697691) B697691
theorem B465311 : Blo 463784 465311 := bstep (se 1 (by rfl) ⟨348983, by rfl⟩ : syracuseStep 465311 = 697967) B697967
theorem B465359 : Blo 463784 465359 := bstep (se 1 (by rfl) ⟨349019, by rfl⟩ : syracuseStep 465359 = 698039) B698039
theorem B465383 : Blo 463784 465383 := bstep (se 1 (by rfl) ⟨349037, by rfl⟩ : syracuseStep 465383 = 698075) B698075
theorem B465499 : Blo 463784 465499 := bstep (se 1 (by rfl) ⟨349124, by rfl⟩ : syracuseStep 465499 = 698249) B698249
theorem B465567 : Blo 463784 465567 := bstep (se 1 (by rfl) ⟨349175, by rfl⟩ : syracuseStep 465567 = 698351) B698351
theorem B465735 : Blo 463784 465735 := bstep (se 1 (by rfl) ⟨349301, by rfl⟩ : syracuseStep 465735 = 698603) B698603
theorem B465775 : Blo 463784 465775 := bstep (se 1 (by rfl) ⟨349331, by rfl⟩ : syracuseStep 465775 = 698663) B698663
theorem B465831 : Blo 463784 465831 := bstep (se 1 (by rfl) ⟨349373, by rfl⟩ : syracuseStep 465831 = 698747) B698747
theorem B4463585 : Blo 463784 4463585 := bstep (se 2 (by rfl) ⟨1673844, by rfl⟩ : syracuseStep 4463585 = 3347689) B3347689
theorem B466011 : Blo 463784 466011 := bstep (se 1 (by rfl) ⟨349508, by rfl⟩ : syracuseStep 466011 = 699017) B699017
theorem B466127 : Blo 463784 466127 := bstep (se 1 (by rfl) ⟨349595, by rfl⟩ : syracuseStep 466127 = 699191) B699191
theorem B466151 : Blo 463784 466151 := bstep (se 1 (by rfl) ⟨349613, by rfl⟩ : syracuseStep 466151 = 699227) B699227
theorem B466247 : Blo 463784 466247 := bstep (se 1 (by rfl) ⟨349685, by rfl⟩ : syracuseStep 466247 = 699371) B699371
theorem B466383 : Blo 463784 466383 := bstep (se 1 (by rfl) ⟨349787, by rfl⟩ : syracuseStep 466383 = 699575) B699575
theorem B466543 : Blo 463784 466543 := bstep (se 1 (by rfl) ⟨349907, by rfl⟩ : syracuseStep 466543 = 699815) B699815
theorem B695975 : Blo 463784 695975 := bstep (se 1 (by rfl) ⟨521981, by rfl⟩ : syracuseStep 695975 = 1043963) B1043963
theorem B466599 : Blo 463784 466599 := bstep (se 1 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 466599 = 699899) B699899
theorem B466663 : Blo 463784 466663 := bstep (se 1 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 466663 = 699995) B699995
theorem B696095 : Blo 463784 696095 := bstep (se 1 (by rfl) ⟨522071, by rfl⟩ : syracuseStep 696095 = 1044143) B1044143
theorem B466719 : Blo 463784 466719 := bstep (se 1 (by rfl) ⟨350039, by rfl⟩ : syracuseStep 466719 = 700079) B700079
theorem B466799 : Blo 463784 466799 := bstep (se 1 (by rfl) ⟨350099, by rfl⟩ : syracuseStep 466799 = 700199) B700199
theorem B466855 : Blo 463784 466855 := bstep (se 1 (by rfl) ⟨350141, by rfl⟩ : syracuseStep 466855 = 700283) B700283
theorem B5283791 : Blo 463784 5283791 := bstep (se 1 (by rfl) ⟨3962843, by rfl⟩ : syracuseStep 5283791 = 7925687) B7925687
theorem B1613801 : Blo 463784 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B467135 : Blo 463784 467135 := bstep (se 1 (by rfl) ⟨350351, by rfl⟩ : syracuseStep 467135 = 700703) B700703
theorem B696527 : Blo 463784 696527 := bstep (se 1 (by rfl) ⟨522395, by rfl⟩ : syracuseStep 696527 = 1044791) B1044791
theorem B467151 : Blo 463784 467151 := bstep (se 1 (by rfl) ⟨350363, by rfl⟩ : syracuseStep 467151 = 700727) B700727
theorem B696575 : Blo 463784 696575 := bstep (se 1 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 696575 = 1044863) B1044863
theorem B467199 : Blo 463784 467199 := bstep (se 1 (by rfl) ⟨350399, by rfl⟩ : syracuseStep 467199 = 700799) B700799
theorem B467247 : Blo 463784 467247 := bstep (se 1 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 467247 = 700871) B700871
theorem B6365627 : Blo 463784 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B795163 : Blo 463784 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B467483 : Blo 463784 467483 := bstep (se 1 (by rfl) ⟨350612, by rfl⟩ : syracuseStep 467483 = 701225) B701225
theorem B467487 : Blo 463784 467487 := bstep (se 1 (by rfl) ⟨350615, by rfl⟩ : syracuseStep 467487 = 701231) B701231
theorem B467567 : Blo 463784 467567 := bstep (se 1 (by rfl) ⟨350675, by rfl⟩ : syracuseStep 467567 = 701351) B701351
theorem B467623 : Blo 463784 467623 := bstep (se 1 (by rfl) ⟨350717, by rfl⟩ : syracuseStep 467623 = 701435) B701435
theorem B467663 : Blo 463784 467663 := bstep (se 1 (by rfl) ⟨350747, by rfl⟩ : syracuseStep 467663 = 701495) B701495
theorem B1254151 : Blo 463784 1254151 := bstep (se 1 (by rfl) ⟨940613, by rfl⟩ : syracuseStep 1254151 = 1881227) B1881227
theorem B467743 : Blo 463784 467743 := bstep (se 1 (by rfl) ⟨350807, by rfl⟩ : syracuseStep 467743 = 701615) B701615
theorem B6366107 : Blo 463784 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B697391 : Blo 463784 697391 := bstep (se 1 (by rfl) ⟨523043, by rfl⟩ : syracuseStep 697391 = 1046087) B1046087
theorem B697511 : Blo 463784 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B2270429 : Blo 463784 2270429 := bstep (se 3 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 2270429 = 851411) B851411
theorem B697883 : Blo 463784 697883 := bstep (se 1 (by rfl) ⟨523412, by rfl⟩ : syracuseStep 697883 = 1046825) B1046825
theorem B8464135 : Blo 463784 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B698267 : Blo 463784 698267 := bstep (se 1 (by rfl) ⟨523700, by rfl⟩ : syracuseStep 698267 = 1047401) B1047401
theorem B698303 : Blo 463784 698303 := bstep (se 1 (by rfl) ⟨523727, by rfl⟩ : syracuseStep 698303 = 1047455) B1047455
theorem B993377 : Blo 463784 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B698489 : Blo 463784 698489 := bstep (se 2 (by rfl) ⟨261933, by rfl⟩ : syracuseStep 698489 = 523867) B523867
theorem B698873 : Blo 463784 698873 := bstep (se 2 (by rfl) ⟨262077, by rfl⟩ : syracuseStep 698873 = 524155) B524155
theorem B698927 : Blo 463784 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B5450321 : Blo 463784 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B1944145 : Blo 463784 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B3779513 : Blo 463784 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B699359 : Blo 463784 699359 := bstep (se 1 (by rfl) ⟨524519, by rfl⟩ : syracuseStep 699359 = 1049039) B1049039
theorem B699803 : Blo 463784 699803 := bstep (se 1 (by rfl) ⟨524852, by rfl⟩ : syracuseStep 699803 = 1049705) B1049705
theorem B700223 : Blo 463784 700223 := bstep (se 1 (by rfl) ⟨525167, by rfl⟩ : syracuseStep 700223 = 1050335) B1050335
theorem B13381523 : Blo 463784 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B700409 : Blo 463784 700409 := bstep (se 2 (by rfl) ⟨262653, by rfl⟩ : syracuseStep 700409 = 525307) B525307
theorem B276377615 : Blo 463784 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B700649 : Blo 463784 700649 := bstep (se 2 (by rfl) ⟨262743, by rfl⟩ : syracuseStep 700649 = 525487) B525487
theorem B700775 : Blo 463784 700775 := bstep (se 1 (by rfl) ⟨525581, by rfl⟩ : syracuseStep 700775 = 1051163) B1051163
theorem B2240941 : Blo 463784 2240941 := bstep (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) B840353
theorem B11809223 : Blo 463784 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B3551687 : Blo 463784 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B6435607 : Blo 463784 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B701321 : Blo 463784 701321 := bstep (se 2 (by rfl) ⟨262995, by rfl⟩ : syracuseStep 701321 = 525991) B525991
theorem B16103123 : Blo 463784 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B2013103 : Blo 463784 2013103 := bstep (se 1 (by rfl) ⟨1509827, by rfl⟩ : syracuseStep 2013103 = 3019655) B3019655
theorem B1488937 : Blo 463784 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B1063207 : Blo 463784 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B1095983 : Blo 463784 1095983 := bstep (se 1 (by rfl) ⟨821987, by rfl⟩ : syracuseStep 1095983 = 1643975) B1643975
theorem B1325801 : Blo 463784 1325801 := bstep (se 2 (by rfl) ⟨497175, by rfl⟩ : syracuseStep 1325801 = 994351) B994351
theorem B998153 : Blo 463784 998153 := bstep (se 2 (by rfl) ⟨374307, by rfl⟩ : syracuseStep 998153 = 748615) B748615
theorem B2834297 : Blo 463784 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B6734015 : Blo 463784 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B5292539 : Blo 463784 5292539 := bstep (se 1 (by rfl) ⟨3969404, by rfl⟩ : syracuseStep 5292539 = 7938809) B7938809
theorem B3359335 : Blo 463784 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B836201 : Blo 463784 836201 := bstep (se 2 (by rfl) ⟨313575, by rfl⟩ : syracuseStep 836201 = 627151) B627151
theorem B2245229 : Blo 463784 2245229 := bstep (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) B841961
theorem B13452101 : Blo 463784 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B1131515 : Blo 463784 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B3982391 : Blo 463784 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B8635901 : Blo 463784 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B48907799 : Blo 463784 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B6703397 : Blo 463784 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1887031 : Blo 463784 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B18205661 : Blo 463784 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B2247689 : Blo 463784 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B1789885 : Blo 463784 1789885 := bstep (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) B671207
theorem B8474867 : Blo 463784 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B840059 : Blo 463784 840059 := bstep (se 1 (by rfl) ⟨630044, by rfl⟩ : syracuseStep 840059 = 1260089) B1260089
theorem B11360249 : Blo 463784 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B3824047 : Blo 463784 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B1891183 : Blo 463784 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B3529817 : Blo 463784 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B15162677 : Blo 463784 15162677 := bstep (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) B1421501
theorem B13458797 : Blo 463784 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B1498601 : Blo 463784 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B2678683 : Blo 463784 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B8970527 : Blo 463784 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B1565351 : Blo 463784 1565351 := bstep (se 1 (by rfl) ⟨1174013, by rfl⟩ : syracuseStep 1565351 = 2348027) B2348027
theorem B1565675 : Blo 463784 1565675 := bstep (se 1 (by rfl) ⟨1174256, by rfl⟩ : syracuseStep 1565675 = 2348513) B2348513
theorem B17065025 : Blo 463784 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B3532247 : Blo 463784 3532247 := bstep (se 1 (by rfl) ⟨2649185, by rfl⟩ : syracuseStep 3532247 = 5298371) B5298371
theorem B1762843 : Blo 463784 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B1763315 : Blo 463784 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B1566863 : Blo 463784 1566863 := bstep (se 1 (by rfl) ⟨1175147, by rfl⟩ : syracuseStep 1566863 = 2350295) B2350295
theorem B3533219 : Blo 463784 3533219 := bstep (se 1 (by rfl) ⟨2649914, by rfl⟩ : syracuseStep 3533219 = 5299829) B5299829
theorem B1993247 : Blo 463784 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B1174601 : Blo 463784 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B1043639 : Blo 463784 1043639 := bstep (se 1 (by rfl) ⟨782729, by rfl⟩ : syracuseStep 1043639 = 1565459) B1565459
theorem B1764575 : Blo 463784 1764575 := bstep (se 1 (by rfl) ⟨1323431, by rfl⟩ : syracuseStep 1764575 = 2646863) B2646863
theorem B3239357 : Blo 463784 3239357 := bstep (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) B1214759
theorem B1044215 : Blo 463784 1044215 := bstep (se 1 (by rfl) ⟨783161, by rfl⟩ : syracuseStep 1044215 = 1566323) B1566323
theorem B1044287 : Blo 463784 1044287 := bstep (se 1 (by rfl) ⟨783215, by rfl⟩ : syracuseStep 1044287 = 1566431) B1566431
theorem B5107585 : Blo 463784 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B1044395 : Blo 463784 1044395 := bstep (se 1 (by rfl) ⟨783296, by rfl⟩ : syracuseStep 1044395 = 1566593) B1566593
theorem B22998971 : Blo 463784 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B880723 : Blo 463784 880723 := bstep (se 1 (by rfl) ⟨660542, by rfl⟩ : syracuseStep 880723 = 1321085) B1321085
theorem B1994939 : Blo 463784 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B1896635 : Blo 463784 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B1044755 : Blo 463784 1044755 := bstep (se 1 (by rfl) ⟨783566, by rfl⟩ : syracuseStep 1044755 = 1567133) B1567133
theorem B1765759 : Blo 463784 1765759 := bstep (se 1 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 1765759 = 2648639) B2648639
theorem B1044935 : Blo 463784 1044935 := bstep (se 1 (by rfl) ⟨783701, by rfl⟩ : syracuseStep 1044935 = 1567403) B1567403
theorem B8516177 : Blo 463784 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B1569455 : Blo 463784 1569455 := bstep (se 1 (by rfl) ⟨1177091, by rfl⟩ : syracuseStep 1569455 = 2354183) B2354183
theorem B1766063 : Blo 463784 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B3535649 : Blo 463784 3535649 := bstep (se 2 (by rfl) ⟨1325868, by rfl⟩ : syracuseStep 3535649 = 2651737) B2651737
theorem B1045295 : Blo 463784 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B1045385 : Blo 463784 1045385 := bstep (se 2 (by rfl) ⟨392019, by rfl⟩ : syracuseStep 1045385 = 784039) B784039
theorem B3994555 : Blo 463784 3994555 := bstep (se 1 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 3994555 = 5991833) B5991833
theorem B1799275 : Blo 463784 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B1176839 : Blo 463784 1176839 := bstep (se 1 (by rfl) ⟨882629, by rfl⟩ : syracuseStep 1176839 = 1765259) B1765259
theorem B3536135 : Blo 463784 3536135 := bstep (se 1 (by rfl) ⟨2652101, by rfl⟩ : syracuseStep 3536135 = 5304203) B5304203
theorem B5305661 : Blo 463784 5305661 := bstep (se 3 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 5305661 = 1989623) B1989623
theorem B1701287 : Blo 463784 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B1046159 : Blo 463784 1046159 := bstep (se 1 (by rfl) ⟨784619, by rfl⟩ : syracuseStep 1046159 = 1569239) B1569239
theorem B882409 : Blo 463784 882409 := bstep (se 2 (by rfl) ⟨330903, by rfl⟩ : syracuseStep 882409 = 661807) B661807
theorem B1046249 : Blo 463784 1046249 := bstep (se 2 (by rfl) ⟨392343, by rfl⟩ : syracuseStep 1046249 = 784687) B784687
theorem B587503 : Blo 463784 587503 := bstep (se 1 (by rfl) ⟨440627, by rfl⟩ : syracuseStep 587503 = 881255) B881255
theorem B2652011 : Blo 463784 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B784937 : Blo 463784 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B1767977 : Blo 463784 1767977 := bstep (se 2 (by rfl) ⟨662991, by rfl⟩ : syracuseStep 1767977 = 1325983) B1325983
theorem B588379 : Blo 463784 588379 := bstep (se 1 (by rfl) ⟨441284, by rfl⟩ : syracuseStep 588379 = 882569) B882569
theorem B1047131 : Blo 463784 1047131 := bstep (se 1 (by rfl) ⟨785348, by rfl⟩ : syracuseStep 1047131 = 1570697) B1570697
theorem B1047275 : Blo 463784 1047275 := bstep (se 1 (by rfl) ⟨785456, by rfl⟩ : syracuseStep 1047275 = 1570913) B1570913
theorem B1178347 : Blo 463784 1178347 := bstep (se 1 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 1178347 = 1767521) B1767521
theorem B523471 : Blo 463784 523471 := bstep (se 1 (by rfl) ⟨392603, by rfl⟩ : syracuseStep 523471 = 785207) B785207
theorem B785639 : Blo 463784 785639 := bstep (se 1 (by rfl) ⟨589229, by rfl⟩ : syracuseStep 785639 = 1178459) B1178459
theorem B883943 : Blo 463784 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B1047887 : Blo 463784 1047887 := bstep (se 1 (by rfl) ⟨785915, by rfl⟩ : syracuseStep 1047887 = 1571831) B1571831
theorem B1047977 : Blo 463784 1047977 := bstep (se 2 (by rfl) ⟨392991, by rfl⟩ : syracuseStep 1047977 = 785983) B785983
theorem B1572371 : Blo 463784 1572371 := bstep (se 1 (by rfl) ⟨1179278, by rfl⟩ : syracuseStep 1572371 = 2358557) B2358557
theorem B1768979 : Blo 463784 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B1048175 : Blo 463784 1048175 := bstep (se 1 (by rfl) ⟨786131, by rfl⟩ : syracuseStep 1048175 = 1572263) B1572263
theorem B1179431 : Blo 463784 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B1048463 : Blo 463784 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B4489343 : Blo 463784 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B786847 : Blo 463784 786847 := bstep (se 1 (by rfl) ⟨590135, by rfl⟩ : syracuseStep 786847 = 1180271) B1180271
theorem B754343 : Blo 463784 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B2654927 : Blo 463784 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B1049399 : Blo 463784 1049399 := bstep (se 1 (by rfl) ⟨787049, by rfl⟩ : syracuseStep 1049399 = 1574099) B1574099
theorem B525127 : Blo 463784 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B1049579 : Blo 463784 1049579 := bstep (se 1 (by rfl) ⟨787184, by rfl⟩ : syracuseStep 1049579 = 1574369) B1574369
theorem B1672201 : Blo 463784 1672201 := bstep (se 2 (by rfl) ⟨627075, by rfl⟩ : syracuseStep 1672201 = 1254151) B1254151
theorem B32605199 : Blo 463784 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B1180727 : Blo 463784 1180727 := bstep (se 1 (by rfl) ⟨885545, by rfl⟩ : syracuseStep 1180727 = 1771091) B1771091
theorem B787583 : Blo 463784 787583 := bstep (se 1 (by rfl) ⟨590687, by rfl⟩ : syracuseStep 787583 = 1181375) B1181375
theorem B1574153 : Blo 463784 1574153 := bstep (se 2 (by rfl) ⟨590307, by rfl⟩ : syracuseStep 1574153 = 1180615) B1180615
theorem B2229869 : Blo 463784 2229869 := bstep (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) B836201
theorem B526063 : Blo 463784 526063 := bstep (se 1 (by rfl) ⟨394547, by rfl⟩ : syracuseStep 526063 = 789095) B789095
theorem B1050479 : Blo 463784 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B1050587 : Blo 463784 1050587 := bstep (se 1 (by rfl) ⟨787940, by rfl⟩ : syracuseStep 1050587 = 1575881) B1575881
theorem B788521 : Blo 463784 788521 := bstep (se 2 (by rfl) ⟨295695, by rfl⟩ : syracuseStep 788521 = 591391) B591391
theorem B1771591 : Blo 463784 1771591 := bstep (se 1 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 1771591 = 2657387) B2657387
theorem B1050695 : Blo 463784 1050695 := bstep (se 1 (by rfl) ⟨788021, by rfl⟩ : syracuseStep 1050695 = 1576043) B1576043
theorem B591943 : Blo 463784 591943 := bstep (se 1 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 591943 = 887915) B887915
theorem B1050767 : Blo 463784 1050767 := bstep (se 1 (by rfl) ⟨788075, by rfl⟩ : syracuseStep 1050767 = 1576151) B1576151
theorem B1050857 : Blo 463784 1050857 := bstep (se 2 (by rfl) ⟨394071, by rfl⟩ : syracuseStep 1050857 = 788143) B788143
theorem B1050875 : Blo 463784 1050875 := bstep (se 1 (by rfl) ⟨788156, by rfl⟩ : syracuseStep 1050875 = 1576313) B1576313
theorem B1051127 : Blo 463784 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B560039 : Blo 463784 560039 := bstep (se 1 (by rfl) ⟨420029, by rfl⟩ : syracuseStep 560039 = 840059) B840059
theorem B1183187 : Blo 463784 1183187 := bstep (se 1 (by rfl) ⟨887390, by rfl⟩ : syracuseStep 1183187 = 1774781) B1774781
theorem B7573499 : Blo 463784 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B1183835 : Blo 463784 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B1577609 : Blo 463784 1577609 := bstep (se 2 (by rfl) ⟨591603, by rfl⟩ : syracuseStep 1577609 = 1183207) B1183207
theorem B463983 : Blo 463784 463983 := bstep (se 1 (by rfl) ⟨347987, by rfl⟩ : syracuseStep 463983 = 695975) B695975
theorem B464063 : Blo 463784 464063 := bstep (se 1 (by rfl) ⟨348047, by rfl⟩ : syracuseStep 464063 = 696095) B696095
theorem B2364713 : Blo 463784 2364713 := bstep (se 2 (by rfl) ⟨886767, by rfl⟩ : syracuseStep 2364713 = 1773535) B1773535
theorem B464351 : Blo 463784 464351 := bstep (se 1 (by rfl) ⟨348263, by rfl⟩ : syracuseStep 464351 = 696527) B696527
theorem B464383 : Blo 463784 464383 := bstep (se 1 (by rfl) ⟨348287, by rfl⟩ : syracuseStep 464383 = 696575) B696575
theorem B2987921 : Blo 463784 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B464927 : Blo 463784 464927 := bstep (se 1 (by rfl) ⟨348695, by rfl⟩ : syracuseStep 464927 = 697391) B697391
theorem B11376683 : Blo 463784 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B465007 : Blo 463784 465007 := bstep (se 1 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 465007 = 697511) B697511
theorem B1513619 : Blo 463784 1513619 := bstep (se 1 (by rfl) ⟨1135214, by rfl⟩ : syracuseStep 1513619 = 2270429) B2270429
theorem B465255 : Blo 463784 465255 := bstep (se 1 (by rfl) ⟨348941, by rfl⟩ : syracuseStep 465255 = 697883) B697883
theorem B7543205 : Blo 463784 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B2366009 : Blo 463784 2366009 := bstep (se 2 (by rfl) ⟨887253, by rfl⟩ : syracuseStep 2366009 = 1774507) B1774507
theorem B465511 : Blo 463784 465511 := bstep (se 1 (by rfl) ⟨349133, by rfl⟩ : syracuseStep 465511 = 698267) B698267
theorem B465535 : Blo 463784 465535 := bstep (se 1 (by rfl) ⟨349151, by rfl⟩ : syracuseStep 465535 = 698303) B698303
theorem B662251 : Blo 463784 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B465659 : Blo 463784 465659 := bstep (se 1 (by rfl) ⟨349244, by rfl⟩ : syracuseStep 465659 = 698489) B698489
theorem B2399033 : Blo 463784 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B465915 : Blo 463784 465915 := bstep (se 1 (by rfl) ⟨349436, by rfl⟩ : syracuseStep 465915 = 698873) B698873
theorem B465951 : Blo 463784 465951 := bstep (se 1 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 465951 = 698927) B698927
theorem B466239 : Blo 463784 466239 := bstep (se 1 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 466239 = 699359) B699359
theorem B695759 : Blo 463784 695759 := bstep (se 1 (by rfl) ⟨521819, by rfl⟩ : syracuseStep 695759 = 1043639) B1043639
theorem B466535 : Blo 463784 466535 := bstep (se 1 (by rfl) ⟨349901, by rfl⟩ : syracuseStep 466535 = 699803) B699803
theorem B696143 : Blo 463784 696143 := bstep (se 1 (by rfl) ⟨522107, by rfl⟩ : syracuseStep 696143 = 1044215) B1044215
theorem B696191 : Blo 463784 696191 := bstep (se 1 (by rfl) ⟨522143, by rfl⟩ : syracuseStep 696191 = 1044287) B1044287
theorem B466815 : Blo 463784 466815 := bstep (se 1 (by rfl) ⟨350111, by rfl⟩ : syracuseStep 466815 = 700223) B700223
theorem B8921015 : Blo 463784 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B696263 : Blo 463784 696263 := bstep (se 1 (by rfl) ⟨522197, by rfl⟩ : syracuseStep 696263 = 1044395) B1044395
theorem B466939 : Blo 463784 466939 := bstep (se 1 (by rfl) ⟨350204, by rfl⟩ : syracuseStep 466939 = 700409) B700409
theorem B467099 : Blo 463784 467099 := bstep (se 1 (by rfl) ⟨350324, by rfl⟩ : syracuseStep 467099 = 700649) B700649
theorem B696503 : Blo 463784 696503 := bstep (se 1 (by rfl) ⟨522377, by rfl⟩ : syracuseStep 696503 = 1044755) B1044755
theorem B467183 : Blo 463784 467183 := bstep (se 1 (by rfl) ⟨350387, by rfl⟩ : syracuseStep 467183 = 700775) B700775
theorem B696623 : Blo 463784 696623 := bstep (se 1 (by rfl) ⟨522467, by rfl⟩ : syracuseStep 696623 = 1044935) B1044935
theorem B7872815 : Blo 463784 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B2367791 : Blo 463784 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B1417609 : Blo 463784 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B5677451 : Blo 463784 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B696863 : Blo 463784 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B696923 : Blo 463784 696923 := bstep (se 1 (by rfl) ⟨522692, by rfl⟩ : syracuseStep 696923 = 1045385) B1045385
theorem B467547 : Blo 463784 467547 := bstep (se 1 (by rfl) ⟨350660, by rfl⟩ : syracuseStep 467547 = 701321) B701321
theorem B697439 : Blo 463784 697439 := bstep (se 1 (by rfl) ⟨523079, by rfl⟩ : syracuseStep 697439 = 1046159) B1046159
theorem B697499 : Blo 463784 697499 := bstep (se 1 (by rfl) ⟨523124, by rfl⟩ : syracuseStep 697499 = 1046249) B1046249
theorem B730655 : Blo 463784 730655 := bstep (se 1 (by rfl) ⟨547991, by rfl⟩ : syracuseStep 730655 = 1095983) B1095983
theorem B697961 : Blo 463784 697961 := bstep (se 2 (by rfl) ⟨261735, by rfl⟩ : syracuseStep 697961 = 523471) B523471
theorem B698087 : Blo 463784 698087 := bstep (se 1 (by rfl) ⟨523565, by rfl⟩ : syracuseStep 698087 = 1047131) B1047131
theorem B698183 : Blo 463784 698183 := bstep (se 1 (by rfl) ⟨523637, by rfl⟩ : syracuseStep 698183 = 1047275) B1047275
theorem B665435 : Blo 463784 665435 := bstep (se 1 (by rfl) ⟨499076, by rfl⟩ : syracuseStep 665435 = 998153) B998153
theorem B698591 : Blo 463784 698591 := bstep (se 1 (by rfl) ⟨523943, by rfl⟩ : syracuseStep 698591 = 1047887) B1047887
theorem B698651 : Blo 463784 698651 := bstep (se 1 (by rfl) ⟨523988, by rfl⟩ : syracuseStep 698651 = 1047977) B1047977
theorem B698783 : Blo 463784 698783 := bstep (se 1 (by rfl) ⟨524087, by rfl⟩ : syracuseStep 698783 = 1048175) B1048175
theorem B698975 : Blo 463784 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B4303469 : Blo 463784 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B2010017 : Blo 463784 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B699305 : Blo 463784 699305 := bstep (se 2 (by rfl) ⟨262239, by rfl⟩ : syracuseStep 699305 = 524479) B524479
theorem B699335 : Blo 463784 699335 := bstep (se 1 (by rfl) ⟨524501, by rfl⟩ : syracuseStep 699335 = 1049003) B1049003
theorem B699455 : Blo 463784 699455 := bstep (se 1 (by rfl) ⟨524591, by rfl⟩ : syracuseStep 699455 = 1049183) B1049183
theorem B699695 : Blo 463784 699695 := bstep (se 1 (by rfl) ⟨524771, by rfl⟩ : syracuseStep 699695 = 1049543) B1049543
theorem B1060217 : Blo 463784 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B699881 : Blo 463784 699881 := bstep (se 2 (by rfl) ⟨262455, by rfl⟩ : syracuseStep 699881 = 524911) B524911
theorem B699935 : Blo 463784 699935 := bstep (se 1 (by rfl) ⟨524951, by rfl⟩ : syracuseStep 699935 = 1049903) B1049903
theorem B700025 : Blo 463784 700025 := bstep (se 2 (by rfl) ⟨262509, by rfl⟩ : syracuseStep 700025 = 525019) B525019
theorem B2993867 : Blo 463784 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B700271 : Blo 463784 700271 := bstep (se 1 (by rfl) ⟨525203, by rfl⟩ : syracuseStep 700271 = 1050407) B1050407
theorem B1486811 : Blo 463784 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B700523 : Blo 463784 700523 := bstep (se 1 (by rfl) ⟨525392, by rfl⟩ : syracuseStep 700523 = 1050785) B1050785
theorem B4468931 : Blo 463784 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B12103937 : Blo 463784 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B700955 : Blo 463784 700955 := bstep (se 1 (by rfl) ⟨525716, by rfl⟩ : syracuseStep 700955 = 1051433) B1051433
theorem B701135 : Blo 463784 701135 := bstep (se 1 (by rfl) ⟨525851, by rfl⟩ : syracuseStep 701135 = 1051703) B1051703
theorem B701423 : Blo 463784 701423 := bstep (se 1 (by rfl) ⟨526067, by rfl⟩ : syracuseStep 701423 = 1052135) B1052135
theorem B11285513 : Blo 463784 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B5649911 : Blo 463784 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B10368773 : Blo 463784 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B10108451 : Blo 463784 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B999067 : Blo 463784 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B3522527 : Blo 463784 3522527 := bstep (se 1 (by rfl) ⟨2641895, by rfl⟩ : syracuseStep 3522527 = 5283791) B5283791
theorem B5980351 : Blo 463784 5980351 := bstep (se 1 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 5980351 = 8970527) B8970527
theorem B4243751 : Blo 463784 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B4244071 : Blo 463784 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B5326073 : Blo 463784 5326073 := bstep (se 2 (by rfl) ⟨1997277, by rfl⟩ : syracuseStep 5326073 = 3994555) B3994555
theorem B1328831 : Blo 463784 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B20400149 : Blo 463784 20400149 := bstep (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) B956257
theorem B2148457 : Blo 463784 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B8964377 : Blo 463784 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B48548429 : Blo 463784 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B1985249 : Blo 463784 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B1329959 : Blo 463784 1329959 := bstep (se 1 (by rfl) ⟨997469, by rfl⟩ : syracuseStep 1329959 = 1994939) B1994939
theorem B1264423 : Blo 463784 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B5098729 : Blo 463784 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B1134191 : Blo 463784 1134191 := bstep (se 1 (by rfl) ⟨850643, by rfl⟩ : syracuseStep 1134191 = 1701287) B1701287
theorem B10735415 : Blo 463784 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B8638285 : Blo 463784 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B1889531 : Blo 463784 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B2643515 : Blo 463784 2643515 := bstep (se 1 (by rfl) ⟨1982636, by rfl⟩ : syracuseStep 2643515 = 3965273) B3965273
theorem B3528359 : Blo 463784 3528359 := bstep (se 1 (by rfl) ⟨2646269, by rfl⟩ : syracuseStep 3528359 = 5292539) B5292539
theorem B1496819 : Blo 463784 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B8968067 : Blo 463784 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B4479113 : Blo 463784 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B2350457 : Blo 463784 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B2645723 : Blo 463784 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B2580191 : Blo 463784 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B942187 : Blo 463784 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B6054011 : Blo 463784 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B2516041 : Blo 463784 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B23029069 : Blo 463784 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B2975723 : Blo 463784 2975723 := bstep (se 1 (by rfl) ⟨2231792, by rfl⟩ : syracuseStep 2975723 = 4463585) B4463585
theorem B2353211 : Blo 463784 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B8972531 : Blo 463784 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B6810113 : Blo 463784 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B2386513 : Blo 463784 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B1174297 : Blo 463784 1174297 := bstep (se 2 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 1174297 = 880723) B880723
theorem B1043567 : Blo 463784 1043567 := bstep (se 1 (by rfl) ⟨782675, by rfl⟩ : syracuseStep 1043567 = 1565351) B1565351
theorem B2354345 : Blo 463784 2354345 := bstep (se 2 (by rfl) ⟨882879, by rfl⟩ : syracuseStep 2354345 = 1765759) B1765759
theorem B1043783 : Blo 463784 1043783 := bstep (se 1 (by rfl) ⟨782837, by rfl⟩ : syracuseStep 1043783 = 1565675) B1565675
theorem B2354831 : Blo 463784 2354831 := bstep (se 1 (by rfl) ⟨1766123, by rfl⟩ : syracuseStep 2354831 = 3532247) B3532247
theorem B8580809 : Blo 463784 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B1175543 : Blo 463784 1175543 := bstep (se 1 (by rfl) ⟨881657, by rfl⟩ : syracuseStep 1175543 = 1763315) B1763315
theorem B1044575 : Blo 463784 1044575 := bstep (se 1 (by rfl) ⟨783431, by rfl⟩ : syracuseStep 1044575 = 1566863) B1566863
theorem B2355479 : Blo 463784 2355479 := bstep (se 1 (by rfl) ⟨1766609, by rfl⟩ : syracuseStep 2355479 = 3533219) B3533219
theorem B3633547 : Blo 463784 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B2519675 : Blo 463784 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B783067 : Blo 463784 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B1176383 : Blo 463784 1176383 := bstep (se 1 (by rfl) ⟨882287, by rfl⟩ : syracuseStep 1176383 = 1764575) B1764575
theorem B1176545 : Blo 463784 1176545 := bstep (se 2 (by rfl) ⟨441204, by rfl⟩ : syracuseStep 1176545 = 882409) B882409
theorem B783337 : Blo 463784 783337 := bstep (se 2 (by rfl) ⟨293751, by rfl⟩ : syracuseStep 783337 = 587503) B587503
theorem B2684137 : Blo 463784 2684137 := bstep (se 2 (by rfl) ⟨1006551, by rfl⟩ : syracuseStep 2684137 = 2013103) B2013103
theorem B15332647 : Blo 463784 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B184251743 : Blo 463784 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B5993837 : Blo 463784 5993837 := bstep (se 3 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 5993837 = 2247689) B2247689
theorem B49903057 : Blo 463784 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B1046303 : Blo 463784 1046303 := bstep (se 1 (by rfl) ⟨784727, by rfl⟩ : syracuseStep 1046303 = 1569455) B1569455
theorem B1177375 : Blo 463784 1177375 := bstep (se 1 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 1177375 = 1766063) B1766063
theorem B2357099 : Blo 463784 2357099 := bstep (se 1 (by rfl) ⟨1767824, by rfl⟩ : syracuseStep 2357099 = 3535649) B3535649
theorem B784505 : Blo 463784 784505 := bstep (se 2 (by rfl) ⟨294189, by rfl⟩ : syracuseStep 784505 = 588379) B588379
theorem B784559 : Blo 463784 784559 := bstep (se 1 (by rfl) ⟨588419, by rfl⟩ : syracuseStep 784559 = 1176839) B1176839
theorem B2357423 : Blo 463784 2357423 := bstep (se 1 (by rfl) ⟨1768067, by rfl⟩ : syracuseStep 2357423 = 3536135) B3536135
theorem B3537107 : Blo 463784 3537107 := bstep (se 1 (by rfl) ⟨2652830, by rfl⟩ : syracuseStep 3537107 = 5305661) B5305661
theorem B1571129 : Blo 463784 1571129 := bstep (se 2 (by rfl) ⟨589173, by rfl⟩ : syracuseStep 1571129 = 1178347) B1178347
theorem B2521577 : Blo 463784 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B1768007 : Blo 463784 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B523291 : Blo 463784 523291 := bstep (se 1 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 523291 = 784937) B784937
theorem B1178651 : Blo 463784 1178651 := bstep (se 1 (by rfl) ⟨883988, by rfl⟩ : syracuseStep 1178651 = 1767977) B1767977
theorem B883867 : Blo 463784 883867 := bstep (se 1 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 883867 = 1325801) B1325801
theorem B523759 : Blo 463784 523759 := bstep (se 1 (by rfl) ⟨392819, by rfl⟩ : syracuseStep 523759 = 785639) B785639
theorem B589295 : Blo 463784 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B1048247 : Blo 463784 1048247 := bstep (se 1 (by rfl) ⟨786185, by rfl⟩ : syracuseStep 1048247 = 1572371) B1572371
theorem B1179319 : Blo 463784 1179319 := bstep (se 1 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 1179319 = 1768979) B1768979
theorem B786287 : Blo 463784 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B3571577 : Blo 463784 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B1769951 : Blo 463784 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B1049129 : Blo 463784 1049129 := bstep (se 2 (by rfl) ⟨393423, by rfl⟩ : syracuseStep 1049129 = 786847) B786847
theorem B787151 : Blo 463784 787151 := bstep (se 1 (by rfl) ⟨590363, by rfl⟩ : syracuseStep 787151 = 1180727) B1180727
theorem B525055 : Blo 463784 525055 := bstep (se 1 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 525055 = 787583) B787583
theorem B1049435 : Blo 463784 1049435 := bstep (se 1 (by rfl) ⟨787076, by rfl⟩ : syracuseStep 1049435 = 1574153) B1574153
theorem B885887 : Blo 463784 885887 := bstep (se 1 (by rfl) ⟨664415, by rfl⟩ : syracuseStep 885887 = 1328831) B1328831
theorem B2229601 : Blo 463784 2229601 := bstep (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) B1672201
theorem B13600099 : Blo 463784 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B30705425 : Blo 463784 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B886639 : Blo 463784 886639 := bstep (se 1 (by rfl) ⟨664979, by rfl⟩ : syracuseStep 886639 = 1329959) B1329959
theorem B788791 : Blo 463784 788791 := bstep (se 1 (by rfl) ⟨591593, by rfl⟩ : syracuseStep 788791 = 1183187) B1183187
theorem B756127 : Blo 463784 756127 := bstep (se 1 (by rfl) ⟨567095, by rfl⟩ : syracuseStep 756127 = 1134191) B1134191
theorem B5048999 : Blo 463784 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B1051361 : Blo 463784 1051361 := bstep (se 2 (by rfl) ⟨394260, by rfl⟩ : syracuseStep 1051361 = 788521) B788521
theorem B789223 : Blo 463784 789223 := bstep (se 1 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 789223 = 1183835) B1183835
theorem B2362121 : Blo 463784 2362121 := bstep (se 2 (by rfl) ⟨885795, by rfl⟩ : syracuseStep 2362121 = 1771591) B1771591
theorem B789257 : Blo 463784 789257 := bstep (se 2 (by rfl) ⟨295971, by rfl⟩ : syracuseStep 789257 = 591943) B591943
theorem B1051739 : Blo 463784 1051739 := bstep (se 1 (by rfl) ⟨788804, by rfl⟩ : syracuseStep 1051739 = 1577609) B1577609
theorem B3182017 : Blo 463784 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B1576475 : Blo 463784 1576475 := bstep (se 1 (by rfl) ⟨1182356, by rfl⟩ : syracuseStep 1576475 = 2364713) B2364713
theorem B2986075 : Blo 463784 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B1577339 : Blo 463784 1577339 := bstep (se 1 (by rfl) ⟨1183004, by rfl⟩ : syracuseStep 1577339 = 2366009) B2366009
theorem B1774493 : Blo 463784 1774493 := bstep (se 3 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 1774493 = 665435) B665435
theorem B463839 : Blo 463784 463839 := bstep (se 1 (by rfl) ⟨347879, by rfl⟩ : syracuseStep 463839 = 695759) B695759
theorem B464095 : Blo 463784 464095 := bstep (se 1 (by rfl) ⟨348071, by rfl⟩ : syracuseStep 464095 = 696143) B696143
theorem B464127 : Blo 463784 464127 := bstep (se 1 (by rfl) ⟨348095, by rfl⟩ : syracuseStep 464127 = 696191) B696191
theorem B464175 : Blo 463784 464175 := bstep (se 1 (by rfl) ⟨348131, by rfl⟩ : syracuseStep 464175 = 696263) B696263
theorem B4036007 : Blo 463784 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B464335 : Blo 463784 464335 := bstep (se 1 (by rfl) ⟨348251, by rfl⟩ : syracuseStep 464335 = 696503) B696503
theorem B464415 : Blo 463784 464415 := bstep (se 1 (by rfl) ⟨348311, by rfl⟩ : syracuseStep 464415 = 696623) B696623
theorem B5248543 : Blo 463784 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B1578527 : Blo 463784 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B464575 : Blo 463784 464575 := bstep (se 1 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 464575 = 696863) B696863
theorem B464615 : Blo 463784 464615 := bstep (se 1 (by rfl) ⟨348461, by rfl⟩ : syracuseStep 464615 = 696923) B696923
theorem B464959 : Blo 463784 464959 := bstep (se 1 (by rfl) ⟨348719, by rfl⟩ : syracuseStep 464959 = 697439) B697439
theorem B464999 : Blo 463784 464999 := bstep (se 1 (by rfl) ⟨348749, by rfl⟩ : syracuseStep 464999 = 697499) B697499
theorem B465307 : Blo 463784 465307 := bstep (se 1 (by rfl) ⟨348980, by rfl⟩ : syracuseStep 465307 = 697961) B697961
theorem B465391 : Blo 463784 465391 := bstep (se 1 (by rfl) ⟨349043, by rfl⟩ : syracuseStep 465391 = 698087) B698087
theorem B465455 : Blo 463784 465455 := bstep (se 1 (by rfl) ⟨349091, by rfl⟩ : syracuseStep 465455 = 698183) B698183
theorem B6724205 : Blo 463784 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B18160301 : Blo 463784 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B465727 : Blo 463784 465727 := bstep (se 1 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 465727 = 698591) B698591
theorem B465767 : Blo 463784 465767 := bstep (se 1 (by rfl) ⟨349325, by rfl⟩ : syracuseStep 465767 = 698651) B698651
theorem B465855 : Blo 463784 465855 := bstep (se 1 (by rfl) ⟨349391, by rfl⟩ : syracuseStep 465855 = 698783) B698783
theorem B3578849 : Blo 463784 3578849 := bstep (se 2 (by rfl) ⟨1342068, by rfl⟩ : syracuseStep 3578849 = 2684137) B2684137
theorem B465983 : Blo 463784 465983 := bstep (se 1 (by rfl) ⟨349487, by rfl⟩ : syracuseStep 465983 = 698975) B698975
theorem B466203 : Blo 463784 466203 := bstep (se 1 (by rfl) ⟨349652, by rfl⟩ : syracuseStep 466203 = 699305) B699305
theorem B466223 : Blo 463784 466223 := bstep (se 1 (by rfl) ⟨349667, by rfl⟩ : syracuseStep 466223 = 699335) B699335
theorem B466303 : Blo 463784 466303 := bstep (se 1 (by rfl) ⟨349727, by rfl⟩ : syracuseStep 466303 = 699455) B699455
theorem B695711 : Blo 463784 695711 := bstep (se 1 (by rfl) ⟨521783, by rfl⟩ : syracuseStep 695711 = 1043567) B1043567
theorem B466463 : Blo 463784 466463 := bstep (se 1 (by rfl) ⟨349847, by rfl⟩ : syracuseStep 466463 = 699695) B699695
theorem B695855 : Blo 463784 695855 := bstep (se 1 (by rfl) ⟨521891, by rfl⟩ : syracuseStep 695855 = 1043783) B1043783
theorem B466587 : Blo 463784 466587 := bstep (se 1 (by rfl) ⟨349940, by rfl⟩ : syracuseStep 466587 = 699881) B699881
theorem B466623 : Blo 463784 466623 := bstep (se 1 (by rfl) ⟨349967, by rfl⟩ : syracuseStep 466623 = 699935) B699935
theorem B466683 : Blo 463784 466683 := bstep (se 1 (by rfl) ⟨350012, by rfl⟩ : syracuseStep 466683 = 700025) B700025
theorem B466847 : Blo 463784 466847 := bstep (se 1 (by rfl) ⟨350135, by rfl⟩ : syracuseStep 466847 = 700271) B700271
theorem B991207 : Blo 463784 991207 := bstep (se 1 (by rfl) ⟨743405, by rfl⟩ : syracuseStep 991207 = 1486811) B1486811
theorem B696383 : Blo 463784 696383 := bstep (se 1 (by rfl) ⟨522287, by rfl⟩ : syracuseStep 696383 = 1044575) B1044575
theorem B467015 : Blo 463784 467015 := bstep (se 1 (by rfl) ⟨350261, by rfl⟩ : syracuseStep 467015 = 700523) B700523
theorem B8069291 : Blo 463784 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B467303 : Blo 463784 467303 := bstep (se 1 (by rfl) ⟨350477, by rfl⟩ : syracuseStep 467303 = 700955) B700955
theorem B1679783 : Blo 463784 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B467423 : Blo 463784 467423 := bstep (se 1 (by rfl) ⟨350567, by rfl⟩ : syracuseStep 467423 = 701135) B701135
theorem B467615 : Blo 463784 467615 := bstep (se 1 (by rfl) ⟨350711, by rfl⟩ : syracuseStep 467615 = 701423) B701423
theorem B697535 : Blo 463784 697535 := bstep (se 1 (by rfl) ⟨523151, by rfl⟩ : syracuseStep 697535 = 1046303) B1046303
theorem B697721 : Blo 463784 697721 := bstep (se 2 (by rfl) ⟨261645, by rfl⟩ : syracuseStep 697721 = 523291) B523291
theorem B698345 : Blo 463784 698345 := bstep (se 2 (by rfl) ⟨261879, by rfl⟩ : syracuseStep 698345 = 523759) B523759
theorem B698831 : Blo 463784 698831 := bstep (se 1 (by rfl) ⟨524123, by rfl⟩ : syracuseStep 698831 = 1048247) B1048247
theorem B2992895 : Blo 463784 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B1256249 : Blo 463784 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B2829167 : Blo 463784 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B7973801 : Blo 463784 7973801 := bstep (se 2 (by rfl) ⟨2990175, by rfl⟩ : syracuseStep 7973801 = 5980351) B5980351
theorem B502895 : Blo 463784 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B699599 : Blo 463784 699599 := bstep (se 1 (by rfl) ⟨524699, by rfl⟩ : syracuseStep 699599 = 1049399) B1049399
theorem B699719 : Blo 463784 699719 := bstep (se 1 (by rfl) ⟨524789, by rfl⟩ : syracuseStep 699719 = 1049579) B1049579
theorem B21736799 : Blo 463784 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B3550715 : Blo 463784 3550715 := bstep (se 1 (by rfl) ⟨2663036, by rfl⟩ : syracuseStep 3550715 = 5326073) B5326073
theorem B700169 : Blo 463784 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B700319 : Blo 463784 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B700391 : Blo 463784 700391 := bstep (se 1 (by rfl) ⟨525293, by rfl⟩ : syracuseStep 700391 = 1050587) B1050587
theorem B700463 : Blo 463784 700463 := bstep (se 1 (by rfl) ⟨525347, by rfl⟩ : syracuseStep 700463 = 1050695) B1050695
theorem B700511 : Blo 463784 700511 := bstep (se 1 (by rfl) ⟨525383, by rfl⟩ : syracuseStep 700511 = 1050767) B1050767
theorem B700571 : Blo 463784 700571 := bstep (se 1 (by rfl) ⟨525428, by rfl⟩ : syracuseStep 700571 = 1050857) B1050857
theorem B700583 : Blo 463784 700583 := bstep (se 1 (by rfl) ⟨525437, by rfl⟩ : syracuseStep 700583 = 1050875) B1050875
theorem B5976251 : Blo 463784 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B700751 : Blo 463784 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B701417 : Blo 463784 701417 := bstep (se 2 (by rfl) ⟨263031, by rfl⟩ : syracuseStep 701417 = 526063) B526063
theorem B7156943 : Blo 463784 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B2864609 : Blo 463784 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B1259687 : Blo 463784 1259687 := bstep (se 1 (by rfl) ⟨944765, by rfl⟩ : syracuseStep 1259687 = 1889531) B1889531
theorem B1685897 : Blo 463784 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B5978711 : Blo 463784 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B7584455 : Blo 463784 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B5028803 : Blo 463784 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B5946317 : Blo 463784 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B6798305 : Blo 463784 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B11517713 : Blo 463784 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B1720127 : Blo 463784 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B5947343 : Blo 463784 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B3784967 : Blo 463784 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B13418885 : Blo 463784 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B1983815 : Blo 463784 1983815 := bstep (se 1 (by rfl) ⟨1487861, by rfl⟩ : syracuseStep 1983815 = 2975723) B2975723
theorem B5981687 : Blo 463784 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B2868979 : Blo 463784 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B5293997 : Blo 463784 5293997 := bstep (se 3 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 5293997 = 1985249) B1985249
theorem B66537409 : Blo 463784 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B706811 : Blo 463784 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B1493437 : Blo 463784 1493437 := bstep (se 3 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 1493437 = 560039) B560039
theorem B5720539 : Blo 463784 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B7523675 : Blo 463784 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B122834495 : Blo 463784 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B1332089 : Blo 463784 1332089 := bstep (se 2 (by rfl) ⟨499533, by rfl⟩ : syracuseStep 1332089 = 999067) B999067
theorem B6738967 : Blo 463784 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B2381051 : Blo 463784 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B2348351 : Blo 463784 2348351 := bstep (se 1 (by rfl) ⟨1761263, by rfl⟩ : syracuseStep 2348351 = 3522527) B3522527
theorem B1890145 : Blo 463784 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B5658761 : Blo 463784 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B32365619 : Blo 463784 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B1565729 : Blo 463784 1565729 := bstep (se 2 (by rfl) ⟨587148, by rfl⟩ : syracuseStep 1565729 = 1174297) B1174297
theorem B1762343 : Blo 463784 1762343 := bstep (se 1 (by rfl) ⟨1321757, by rfl⟩ : syracuseStep 1762343 = 2643515) B2643515
theorem B2352239 : Blo 463784 2352239 := bstep (se 1 (by rfl) ⟨1764179, by rfl⟩ : syracuseStep 2352239 = 3528359) B3528359
theorem B1991947 : Blo 463784 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B1009079 : Blo 463784 1009079 := bstep (se 1 (by rfl) ⟨756809, by rfl⟩ : syracuseStep 1009079 = 1513619) B1513619
theorem B1599355 : Blo 463784 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B3991517 : Blo 463784 3991517 := bstep (se 3 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 3991517 = 1496819) B1496819
theorem B1566971 : Blo 463784 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B1763815 : Blo 463784 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B4844729 : Blo 463784 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1044089 : Blo 463784 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B487103 : Blo 463784 487103 := bstep (se 1 (by rfl) ⟨365327, by rfl⟩ : syracuseStep 487103 = 730655) B730655
theorem B1044449 : Blo 463784 1044449 := bstep (se 2 (by rfl) ⟨391668, by rfl⟩ : syracuseStep 1044449 = 783337) B783337
theorem B1568807 : Blo 463784 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B20443529 : Blo 463784 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B1340011 : Blo 463784 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B1569563 : Blo 463784 1569563 := bstep (se 1 (by rfl) ⟨1177172, by rfl⟩ : syracuseStep 1569563 = 2354345) B2354345
theorem B1569833 : Blo 463784 1569833 := bstep (se 2 (by rfl) ⟨588687, by rfl⟩ : syracuseStep 1569833 = 1177375) B1177375
theorem B1569887 : Blo 463784 1569887 := bstep (se 1 (by rfl) ⟨1177415, by rfl⟩ : syracuseStep 1569887 = 2354831) B2354831
theorem B1995911 : Blo 463784 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B783695 : Blo 463784 783695 := bstep (se 1 (by rfl) ⟨587771, by rfl⟩ : syracuseStep 783695 = 1175543) B1175543
theorem B2979287 : Blo 463784 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1570319 : Blo 463784 1570319 := bstep (se 1 (by rfl) ⟨1177739, by rfl⟩ : syracuseStep 1570319 = 2355479) B2355479
theorem B784255 : Blo 463784 784255 := bstep (se 1 (by rfl) ⟨588191, by rfl⟩ : syracuseStep 784255 = 1176383) B1176383
theorem B784363 : Blo 463784 784363 := bstep (se 1 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 784363 = 1176545) B1176545
theorem B3995891 : Blo 463784 3995891 := bstep (se 1 (by rfl) ⟨2996918, by rfl⟩ : syracuseStep 3995891 = 5993837) B5993837
theorem B883001 : Blo 463784 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B3766607 : Blo 463784 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B6912515 : Blo 463784 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B1571399 : Blo 463784 1571399 := bstep (se 1 (by rfl) ⟨1178549, by rfl⟩ : syracuseStep 1571399 = 2357099) B2357099
theorem B1571453 : Blo 463784 1571453 := bstep (se 3 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 1571453 = 589295) B589295
theorem B523003 : Blo 463784 523003 := bstep (se 1 (by rfl) ⟨392252, by rfl⟩ : syracuseStep 523003 = 784505) B784505
theorem B523039 : Blo 463784 523039 := bstep (se 1 (by rfl) ⟨392279, by rfl⟩ : syracuseStep 523039 = 784559) B784559
theorem B1571615 : Blo 463784 1571615 := bstep (se 1 (by rfl) ⟨1178711, by rfl⟩ : syracuseStep 1571615 = 2357423) B2357423
theorem B2358071 : Blo 463784 2358071 := bstep (se 1 (by rfl) ⟨1768553, by rfl⟩ : syracuseStep 2358071 = 3537107) B3537107
theorem B1178489 : Blo 463784 1178489 := bstep (se 2 (by rfl) ⟨441933, by rfl⟩ : syracuseStep 1178489 = 883867) B883867
theorem B1047419 : Blo 463784 1047419 := bstep (se 1 (by rfl) ⟨785564, by rfl⟩ : syracuseStep 1047419 = 1571129) B1571129
theorem B1178671 : Blo 463784 1178671 := bstep (se 1 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 1178671 = 1768007) B1768007
theorem B785767 : Blo 463784 785767 := bstep (se 1 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 785767 = 1178651) B1178651
theorem B1572425 : Blo 463784 1572425 := bstep (se 2 (by rfl) ⟨589659, by rfl⟩ : syracuseStep 1572425 = 1179319) B1179319
theorem B524191 : Blo 463784 524191 := bstep (se 1 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 524191 = 786287) B786287
theorem B2523311 : Blo 463784 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B8945923 : Blo 463784 8945923 := bstep (se 1 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 8945923 = 13418885) B13418885
theorem B1179967 : Blo 463784 1179967 := bstep (se 1 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 1179967 = 1769951) B1769951
theorem B524767 : Blo 463784 524767 := bstep (se 1 (by rfl) ⟨393575, by rfl⟩ : syracuseStep 524767 = 787151) B787151
theorem B590591 : Blo 463784 590591 := bstep (se 1 (by rfl) ⟨442943, by rfl⟩ : syracuseStep 590591 = 885887) B885887
theorem B2655929 : Blo 463784 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B1574747 : Blo 463784 1574747 := bstep (se 1 (by rfl) ⟨1181060, by rfl⟩ : syracuseStep 1574747 = 2362121) B2362121
theorem B526171 : Blo 463784 526171 := bstep (se 1 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 526171 = 789257) B789257
theorem B5015783 : Blo 463784 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B1050983 : Blo 463784 1050983 := bstep (se 1 (by rfl) ⟨788237, by rfl⟩ : syracuseStep 1050983 = 1576475) B1576475
theorem B81889663 : Blo 463784 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B1182185 : Blo 463784 1182185 := bstep (se 2 (by rfl) ⟨443319, by rfl⟩ : syracuseStep 1182185 = 886639) B886639
theorem B1051559 : Blo 463784 1051559 := bstep (se 1 (by rfl) ⟨788669, by rfl⟩ : syracuseStep 1051559 = 1577339) B1577339
theorem B1051721 : Blo 463784 1051721 := bstep (se 2 (by rfl) ⟨394395, by rfl⟩ : syracuseStep 1051721 = 788791) B788791
theorem B888059 : Blo 463784 888059 := bstep (se 1 (by rfl) ⟨666044, by rfl⟩ : syracuseStep 888059 = 1332089) B1332089
theorem B1182995 : Blo 463784 1182995 := bstep (se 1 (by rfl) ⟨887246, by rfl⟩ : syracuseStep 1182995 = 1774493) B1774493
theorem B2690671 : Blo 463784 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B1052297 : Blo 463784 1052297 := bstep (se 2 (by rfl) ⟨394611, by rfl⟩ : syracuseStep 1052297 = 789223) B789223
theorem B1052351 : Blo 463784 1052351 := bstep (se 1 (by rfl) ⟨789263, by rfl⟩ : syracuseStep 1052351 = 1578527) B1578527
theorem B3772507 : Blo 463784 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B463807 : Blo 463784 463807 := bstep (se 1 (by rfl) ⟨347855, by rfl⟩ : syracuseStep 463807 = 695711) B695711
theorem B463903 : Blo 463784 463903 := bstep (se 1 (by rfl) ⟨347927, by rfl⟩ : syracuseStep 463903 = 695855) B695855
theorem B464255 : Blo 463784 464255 := bstep (se 1 (by rfl) ⟨348191, by rfl⟩ : syracuseStep 464255 = 696383) B696383
theorem B5379527 : Blo 463784 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B465023 : Blo 463784 465023 := bstep (se 1 (by rfl) ⟨348767, by rfl⟩ : syracuseStep 465023 = 697535) B697535
theorem B465147 : Blo 463784 465147 := bstep (se 1 (by rfl) ⟨348860, by rfl⟩ : syracuseStep 465147 = 697721) B697721
theorem B2661011 : Blo 463784 2661011 := bstep (se 1 (by rfl) ⟨1995758, by rfl⟩ : syracuseStep 2661011 = 3991517) B3991517
theorem B465563 : Blo 463784 465563 := bstep (se 1 (by rfl) ⟨349172, by rfl⟩ : syracuseStep 465563 = 698345) B698345
theorem B8985289 : Blo 463784 8985289 := bstep (se 2 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 8985289 = 6738967) B6738967
theorem B465887 : Blo 463784 465887 := bstep (se 1 (by rfl) ⟨349415, by rfl⟩ : syracuseStep 465887 = 698831) B698831
theorem B5315867 : Blo 463784 5315867 := bstep (se 1 (by rfl) ⟨3986900, by rfl⟩ : syracuseStep 5315867 = 7973801) B7973801
theorem B466399 : Blo 463784 466399 := bstep (se 1 (by rfl) ⟨349799, by rfl⟩ : syracuseStep 466399 = 699599) B699599
theorem B3349997 : Blo 463784 3349997 := bstep (se 3 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 3349997 = 1256249) B1256249
theorem B466479 : Blo 463784 466479 := bstep (se 1 (by rfl) ⟨349859, by rfl⟩ : syracuseStep 466479 = 699719) B699719
theorem B14491199 : Blo 463784 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B2367143 : Blo 463784 2367143 := bstep (se 1 (by rfl) ⟨1775357, by rfl⟩ : syracuseStep 2367143 = 3550715) B3550715
theorem B696059 : Blo 463784 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B466779 : Blo 463784 466779 := bstep (se 1 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 466779 = 700169) B700169
theorem B466879 : Blo 463784 466879 := bstep (se 1 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 466879 = 700319) B700319
theorem B696299 : Blo 463784 696299 := bstep (se 1 (by rfl) ⟨522224, by rfl⟩ : syracuseStep 696299 = 1044449) B1044449
theorem B466927 : Blo 463784 466927 := bstep (se 1 (by rfl) ⟨350195, by rfl⟩ : syracuseStep 466927 = 700391) B700391
theorem B466975 : Blo 463784 466975 := bstep (se 1 (by rfl) ⟨350231, by rfl⟩ : syracuseStep 466975 = 700463) B700463
theorem B467007 : Blo 463784 467007 := bstep (se 1 (by rfl) ⟨350255, by rfl⟩ : syracuseStep 467007 = 700511) B700511
theorem B467047 : Blo 463784 467047 := bstep (se 1 (by rfl) ⟨350285, by rfl⟩ : syracuseStep 467047 = 700571) B700571
theorem B467055 : Blo 463784 467055 := bstep (se 1 (by rfl) ⟨350291, by rfl⟩ : syracuseStep 467055 = 700583) B700583
theorem B467167 : Blo 463784 467167 := bstep (se 1 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 467167 = 700751) B700751
theorem B12919277 : Blo 463784 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B467611 : Blo 463784 467611 := bstep (se 1 (by rfl) ⟨350708, by rfl⟩ : syracuseStep 467611 = 701417) B701417
theorem B1909739 : Blo 463784 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B697337 : Blo 463784 697337 := bstep (se 2 (by rfl) ⟨261501, by rfl⟩ : syracuseStep 697337 = 523003) B523003
theorem B697385 : Blo 463784 697385 := bstep (se 2 (by rfl) ⟨261519, by rfl⟩ : syracuseStep 697385 = 523039) B523039
theorem B2663927 : Blo 463784 2663927 := bstep (se 1 (by rfl) ⟨1997945, by rfl⟩ : syracuseStep 2663927 = 3995891) B3995891
theorem B1123931 : Blo 463784 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B5056303 : Blo 463784 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B698279 : Blo 463784 698279 := bstep (se 1 (by rfl) ⟨523709, by rfl⟩ : syracuseStep 698279 = 1047419) B1047419
theorem B3352535 : Blo 463784 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B8529893 : Blo 463784 8529893 := bstep (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) B1599355
theorem B4532203 : Blo 463784 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B7678475 : Blo 463784 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B698921 : Blo 463784 698921 := bstep (se 2 (by rfl) ⟨262095, by rfl⟩ : syracuseStep 698921 = 524191) B524191
theorem B1321609 : Blo 463784 1321609 := bstep (se 2 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 1321609 = 991207) B991207
theorem B699419 : Blo 463784 699419 := bstep (se 1 (by rfl) ⟨524564, by rfl⟩ : syracuseStep 699419 = 1049129) B1049129
theorem B699623 : Blo 463784 699623 := bstep (se 1 (by rfl) ⟨524717, by rfl⟩ : syracuseStep 699623 = 1049435) B1049435
theorem B1322543 : Blo 463784 1322543 := bstep (se 1 (by rfl) ⟨991907, by rfl⟩ : syracuseStep 1322543 = 1983815) B1983815
theorem B700073 : Blo 463784 700073 := bstep (se 2 (by rfl) ⟨262527, by rfl⟩ : syracuseStep 700073 = 525055) B525055
theorem B18133465 : Blo 463784 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B700907 : Blo 463784 700907 := bstep (se 1 (by rfl) ⟨525680, by rfl⟩ : syracuseStep 700907 = 1051361) B1051361
theorem B701159 : Blo 463784 701159 := bstep (se 1 (by rfl) ⟨525869, by rfl⟩ : syracuseStep 701159 = 1051739) B1051739
theorem B88716545 : Blo 463784 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B1587367 : Blo 463784 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B12106867 : Blo 463784 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B4242689 : Blo 463784 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B21577079 : Blo 463784 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B3981433 : Blo 463784 3981433 := bstep (se 2 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 3981433 = 2986075) B2986075
theorem B1884829 : Blo 463784 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B1786681 : Blo 463784 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B672719 : Blo 463784 672719 := bstep (se 1 (by rfl) ⟨504539, by rfl⟩ : syracuseStep 672719 = 1009079) B1009079
theorem B1886111 : Blo 463784 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B5195765 : Blo 463784 5195765 := bstep (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) B487103
theorem B6998057 : Blo 463784 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B3984167 : Blo 463784 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B1330607 : Blo 463784 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B4771295 : Blo 463784 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B1986191 : Blo 463784 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B839791 : Blo 463784 839791 := bstep (se 1 (by rfl) ⟨629843, by rfl⟩ : syracuseStep 839791 = 1259687) B1259687
theorem B2511071 : Blo 463784 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B4608343 : Blo 463784 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B3985807 : Blo 463784 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B10080773 : Blo 463784 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B3987791 : Blo 463784 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B4479421 : Blo 463784 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B20470283 : Blo 463784 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B3529331 : Blo 463784 3529331 := bstep (se 1 (by rfl) ⟨2646998, by rfl⟩ : syracuseStep 3529331 = 5293997) B5293997
theorem B3365999 : Blo 463784 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B2972801 : Blo 463784 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B3825305 : Blo 463784 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B1008169 : Blo 463784 1008169 := bstep (se 2 (by rfl) ⟨378063, by rfl⟩ : syracuseStep 1008169 = 756127) B756127
theorem B1991249 : Blo 463784 1991249 := bstep (se 2 (by rfl) ⟨746718, by rfl⟩ : syracuseStep 1991249 = 1493437) B1493437
theorem B7627385 : Blo 463784 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B2351753 : Blo 463784 2351753 := bstep (se 2 (by rfl) ⟨881907, by rfl⟩ : syracuseStep 2351753 = 1763815) B1763815
theorem B1565567 : Blo 463784 1565567 := bstep (se 1 (by rfl) ⟨1174175, by rfl⟩ : syracuseStep 1565567 = 2348351) B2348351
theorem B4482803 : Blo 463784 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B2385899 : Blo 463784 2385899 := bstep (se 1 (by rfl) ⟨1789424, by rfl⟩ : syracuseStep 2385899 = 3578849) B3578849
theorem B1043819 : Blo 463784 1043819 := bstep (se 1 (by rfl) ⟨782864, by rfl⟩ : syracuseStep 1043819 = 1565729) B1565729
theorem B1174895 : Blo 463784 1174895 := bstep (se 1 (by rfl) ⟨881171, by rfl⟩ : syracuseStep 1174895 = 1762343) B1762343
theorem B1568159 : Blo 463784 1568159 := bstep (se 1 (by rfl) ⟨1176119, by rfl⟩ : syracuseStep 1568159 = 2352239) B2352239
theorem B2354669 : Blo 463784 2354669 := bstep (se 3 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 2354669 = 883001) B883001
theorem B1044647 : Blo 463784 1044647 := bstep (se 1 (by rfl) ⟨783485, by rfl⟩ : syracuseStep 1044647 = 1566971) B1566971
theorem B1995263 : Blo 463784 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B1045673 : Blo 463784 1045673 := bstep (se 2 (by rfl) ⟨392127, by rfl⟩ : syracuseStep 1045673 = 784255) B784255
theorem B1045817 : Blo 463784 1045817 := bstep (se 2 (by rfl) ⟨392181, by rfl⟩ : syracuseStep 1045817 = 784363) B784363
theorem B1045871 : Blo 463784 1045871 := bstep (se 1 (by rfl) ⟨784403, by rfl⟩ : syracuseStep 1045871 = 1568807) B1568807
theorem B13629019 : Blo 463784 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B1341053 : Blo 463784 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B1046375 : Blo 463784 1046375 := bstep (se 1 (by rfl) ⟨784781, by rfl⟩ : syracuseStep 1046375 = 1569563) B1569563
theorem B1046555 : Blo 463784 1046555 := bstep (se 1 (by rfl) ⟨784916, by rfl⟩ : syracuseStep 1046555 = 1569833) B1569833
theorem B1046591 : Blo 463784 1046591 := bstep (se 1 (by rfl) ⟨784943, by rfl⟩ : syracuseStep 1046591 = 1569887) B1569887
theorem B522463 : Blo 463784 522463 := bstep (se 1 (by rfl) ⟨391847, by rfl⟩ : syracuseStep 522463 = 783695) B783695
theorem B1046879 : Blo 463784 1046879 := bstep (se 1 (by rfl) ⟨785159, by rfl⟩ : syracuseStep 1046879 = 1570319) B1570319
theorem B1571561 : Blo 463784 1571561 := bstep (se 2 (by rfl) ⟨589335, by rfl⟩ : syracuseStep 1571561 = 1178671) B1178671
theorem B1047599 : Blo 463784 1047599 := bstep (se 1 (by rfl) ⟨785699, by rfl⟩ : syracuseStep 1047599 = 1571399) B1571399
theorem B1047635 : Blo 463784 1047635 := bstep (se 1 (by rfl) ⟨785726, by rfl⟩ : syracuseStep 1047635 = 1571453) B1571453
theorem B1047689 : Blo 463784 1047689 := bstep (se 2 (by rfl) ⟨392883, by rfl⟩ : syracuseStep 1047689 = 785767) B785767
theorem B1047743 : Blo 463784 1047743 := bstep (se 1 (by rfl) ⟨785807, by rfl⟩ : syracuseStep 1047743 = 1571615) B1571615
theorem B1572047 : Blo 463784 1572047 := bstep (se 1 (by rfl) ⟨1179035, by rfl⟩ : syracuseStep 1572047 = 2358071) B2358071
theorem B785659 : Blo 463784 785659 := bstep (se 1 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 785659 = 1178489) B1178489
theorem B3964211 : Blo 463784 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B4587005 : Blo 463784 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B1048283 : Blo 463784 1048283 := bstep (se 1 (by rfl) ⟨786212, by rfl⟩ : syracuseStep 1048283 = 1572425) B1572425
theorem B3964895 : Blo 463784 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B5308577 : Blo 463784 5308577 := bstep (se 2 (by rfl) ⟨1990716, by rfl⟩ : syracuseStep 5308577 = 3981433) B3981433
theorem B11927897 : Blo 463784 11927897 := bstep (se 2 (by rfl) ⟨4472961, by rfl⟩ : syracuseStep 11927897 = 8945923) B8945923
theorem B1573289 : Blo 463784 1573289 := bstep (se 2 (by rfl) ⟨589983, by rfl⟩ : syracuseStep 1573289 = 1179967) B1179967
theorem B1770619 : Blo 463784 1770619 := bstep (se 1 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 1770619 = 2655929) B2655929
theorem B1049831 : Blo 463784 1049831 := bstep (se 1 (by rfl) ⟨787373, by rfl⟩ : syracuseStep 1049831 = 1574747) B1574747
theorem B3343855 : Blo 463784 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B788123 : Blo 463784 788123 := bstep (se 1 (by rfl) ⟨591092, by rfl⟩ : syracuseStep 788123 = 1182185) B1182185
theorem B2656111 : Blo 463784 2656111 := bstep (se 1 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 2656111 = 3984167) B3984167
theorem B1574909 : Blo 463784 1574909 := bstep (se 3 (by rfl) ⟨295295, by rfl⟩ : syracuseStep 1574909 = 590591) B590591
theorem B592039 : Blo 463784 592039 := bstep (se 1 (by rfl) ⟨444029, by rfl⟩ : syracuseStep 592039 = 888059) B888059
theorem B788663 : Blo 463784 788663 := bstep (se 1 (by rfl) ⟨591497, by rfl⟩ : syracuseStep 788663 = 1182995) B1182995
theorem B3180863 : Blo 463784 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B1674047 : Blo 463784 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B5376901 : Blo 463784 5376901 := bstep (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) B1008169
theorem B6720515 : Blo 463784 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B109186217 : Blo 463784 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B2658527 : Blo 463784 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B1774007 : Blo 463784 1774007 := bstep (se 1 (by rfl) ⟨1330505, by rfl⟩ : syracuseStep 1774007 = 2661011) B2661011
theorem B3543911 : Blo 463784 3543911 := bstep (se 1 (by rfl) ⟨2657933, by rfl⟩ : syracuseStep 3543911 = 5315867) B5315867
theorem B2233331 : Blo 463784 2233331 := bstep (se 1 (by rfl) ⟨1674998, by rfl⟩ : syracuseStep 2233331 = 3349997) B3349997
theorem B1578095 : Blo 463784 1578095 := bstep (se 1 (by rfl) ⟨1183571, by rfl⟩ : syracuseStep 1578095 = 2367143) B2367143
theorem B464039 : Blo 463784 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B464199 : Blo 463784 464199 := bstep (se 1 (by rfl) ⟨348149, by rfl⟩ : syracuseStep 464199 = 696299) B696299
theorem B5314409 : Blo 463784 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B464891 : Blo 463784 464891 := bstep (se 1 (by rfl) ⟨348668, by rfl⟩ : syracuseStep 464891 = 697337) B697337
theorem B464923 : Blo 463784 464923 := bstep (se 1 (by rfl) ⟨348692, by rfl⟩ : syracuseStep 464923 = 697385) B697385
theorem B1775951 : Blo 463784 1775951 := bstep (se 1 (by rfl) ⟨1331963, by rfl⟩ : syracuseStep 1775951 = 2663927) B2663927
theorem B465519 : Blo 463784 465519 := bstep (se 1 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 465519 = 698279) B698279
theorem B2235023 : Blo 463784 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B5118983 : Blo 463784 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B465947 : Blo 463784 465947 := bstep (se 1 (by rfl) ⟨349460, by rfl⟩ : syracuseStep 465947 = 698921) B698921
theorem B466279 : Blo 463784 466279 := bstep (se 1 (by rfl) ⟨349709, by rfl⟩ : syracuseStep 466279 = 699419) B699419
theorem B466415 : Blo 463784 466415 := bstep (se 1 (by rfl) ⟨349811, by rfl⟩ : syracuseStep 466415 = 699623) B699623
theorem B695879 : Blo 463784 695879 := bstep (se 1 (by rfl) ⟨521909, by rfl⟩ : syracuseStep 695879 = 1043819) B1043819
theorem B466715 : Blo 463784 466715 := bstep (se 1 (by rfl) ⟨350036, by rfl⟩ : syracuseStep 466715 = 700073) B700073
theorem B696431 : Blo 463784 696431 := bstep (se 1 (by rfl) ⟨522323, by rfl⟩ : syracuseStep 696431 = 1044647) B1044647
theorem B696617 : Blo 463784 696617 := bstep (se 2 (by rfl) ⟨261231, by rfl⟩ : syracuseStep 696617 = 522463) B522463
theorem B467271 : Blo 463784 467271 := bstep (se 1 (by rfl) ⟨350453, by rfl⟩ : syracuseStep 467271 = 700907) B700907
theorem B467439 : Blo 463784 467439 := bstep (se 1 (by rfl) ⟨350579, by rfl⟩ : syracuseStep 467439 = 701159) B701159
theorem B5972561 : Blo 463784 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B697115 : Blo 463784 697115 := bstep (se 1 (by rfl) ⟨522836, by rfl⟩ : syracuseStep 697115 = 1045673) B1045673
theorem B697211 : Blo 463784 697211 := bstep (se 1 (by rfl) ⟨522908, by rfl⟩ : syracuseStep 697211 = 1045817) B1045817
theorem B697247 : Blo 463784 697247 := bstep (se 1 (by rfl) ⟨522935, by rfl⟩ : syracuseStep 697247 = 1045871) B1045871
theorem B894035 : Blo 463784 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B3548285 : Blo 463784 3548285 := bstep (se 3 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 3548285 = 1330607) B1330607
theorem B697583 : Blo 463784 697583 := bstep (se 1 (by rfl) ⟨523187, by rfl⟩ : syracuseStep 697583 = 1046375) B1046375
theorem B697703 : Blo 463784 697703 := bstep (se 1 (by rfl) ⟨523277, by rfl⟩ : syracuseStep 697703 = 1046555) B1046555
theorem B697727 : Blo 463784 697727 := bstep (se 1 (by rfl) ⟨523295, by rfl⟩ : syracuseStep 697727 = 1046591) B1046591
theorem B697919 : Blo 463784 697919 := bstep (se 1 (by rfl) ⟨523439, by rfl⟩ : syracuseStep 697919 = 1046879) B1046879
theorem B698399 : Blo 463784 698399 := bstep (se 1 (by rfl) ⟨523799, by rfl⟩ : syracuseStep 698399 = 1047599) B1047599
theorem B698423 : Blo 463784 698423 := bstep (se 1 (by rfl) ⟨523817, by rfl⟩ : syracuseStep 698423 = 1047635) B1047635
theorem B698459 : Blo 463784 698459 := bstep (se 1 (by rfl) ⟨523844, by rfl⟩ : syracuseStep 698459 = 1047689) B1047689
theorem B698495 : Blo 463784 698495 := bstep (se 1 (by rfl) ⟨523871, by rfl⟩ : syracuseStep 698495 = 1047743) B1047743
theorem B2828459 : Blo 463784 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B3058003 : Blo 463784 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B698855 : Blo 463784 698855 := bstep (se 1 (by rfl) ⟨524141, by rfl⟩ : syracuseStep 698855 = 1048283) B1048283
theorem B1682207 : Blo 463784 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B699689 : Blo 463784 699689 := bstep (se 2 (by rfl) ⟨262383, by rfl⟩ : syracuseStep 699689 = 524767) B524767
theorem B1257407 : Blo 463784 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B4665371 : Blo 463784 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B700655 : Blo 463784 700655 := bstep (se 1 (by rfl) ⟨525491, by rfl⟩ : syracuseStep 700655 = 1050983) B1050983
theorem B701039 : Blo 463784 701039 := bstep (se 1 (by rfl) ⟨525779, by rfl⟩ : syracuseStep 701039 = 1051559) B1051559
theorem B701147 : Blo 463784 701147 := bstep (se 1 (by rfl) ⟨525860, by rfl⟩ : syracuseStep 701147 = 1051721) B1051721
theorem B701531 : Blo 463784 701531 := bstep (se 1 (by rfl) ⟨526148, by rfl⟩ : syracuseStep 701531 = 1052297) B1052297
theorem B1324127 : Blo 463784 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B701561 : Blo 463784 701561 := bstep (se 2 (by rfl) ⟨263085, by rfl⟩ : syracuseStep 701561 = 526171) B526171
theorem B701567 : Blo 463784 701567 := bstep (se 1 (by rfl) ⟨526175, by rfl⟩ : syracuseStep 701567 = 1052351) B1052351
theorem B6042937 : Blo 463784 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B13646855 : Blo 463784 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B2243999 : Blo 463784 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B1981867 : Blo 463784 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B3587561 : Blo 463784 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B5030009 : Blo 463784 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B1327499 : Blo 463784 1327499 := bstep (se 1 (by rfl) ⟨995624, by rfl⟩ : syracuseStep 1327499 = 1991249) B1991249
theorem B6144457 : Blo 463784 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B5686595 : Blo 463784 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B1590599 : Blo 463784 1590599 := bstep (se 1 (by rfl) ⟨1192949, by rfl⟩ : syracuseStep 1590599 = 2385899) B2385899
theorem B18172025 : Blo 463784 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B2116489 : Blo 463784 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B1330175 : Blo 463784 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B11980385 : Blo 463784 11980385 := bstep (se 2 (by rfl) ⟨4492644, by rfl⟩ : syracuseStep 11980385 = 8985289) B8985289
theorem B16142489 : Blo 463784 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B2642807 : Blo 463784 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B2643263 : Blo 463784 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B4478885 : Blo 463784 4478885 := bstep (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) B839791
theorem B2513105 : Blo 463784 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B3463843 : Blo 463784 3463843 := bstep (se 1 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 3463843 = 5195765) B5195765
theorem B20339693 : Blo 463784 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B6741737 : Blo 463784 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B1793917 : Blo 463784 1793917 := bstep (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) B672719
theorem B1762145 : Blo 463784 1762145 := bstep (se 2 (by rfl) ⟨660804, by rfl⟩ : syracuseStep 1762145 = 1321609) B1321609
theorem B14345405 : Blo 463784 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B9528965 : Blo 463784 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B2352887 : Blo 463784 2352887 := bstep (se 1 (by rfl) ⟨1764665, by rfl⟩ : syracuseStep 2352887 = 3529331) B3529331
theorem B11954141 : Blo 463784 11954141 := bstep (se 3 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 11954141 = 4482803) B4482803
theorem B9660799 : Blo 463784 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B2550203 : Blo 463784 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B8612851 : Blo 463784 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B1567835 : Blo 463784 1567835 := bstep (se 1 (by rfl) ⟨1175876, by rfl⟩ : syracuseStep 1567835 = 2351753) B2351753
theorem B1043711 : Blo 463784 1043711 := bstep (se 1 (by rfl) ⟨782783, by rfl⟩ : syracuseStep 1043711 = 1565567) B1565567
theorem B24177953 : Blo 463784 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B1273159 : Blo 463784 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B749287 : Blo 463784 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B783263 : Blo 463784 783263 := bstep (se 1 (by rfl) ⟨587447, by rfl⟩ : syracuseStep 783263 = 1174895) B1174895
theorem B1045439 : Blo 463784 1045439 := bstep (se 1 (by rfl) ⟨784079, by rfl⟩ : syracuseStep 1045439 = 1568159) B1568159
theorem B1569779 : Blo 463784 1569779 := bstep (se 1 (by rfl) ⟨1177334, by rfl⟩ : syracuseStep 1569779 = 2354669) B2354669
theorem B881695 : Blo 463784 881695 := bstep (se 1 (by rfl) ⟨661271, by rfl⟩ : syracuseStep 881695 = 1322543) B1322543
theorem B59144363 : Blo 463784 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B1047545 : Blo 463784 1047545 := bstep (se 2 (by rfl) ⟨392829, by rfl⟩ : syracuseStep 1047545 = 785659) B785659
theorem B1047707 : Blo 463784 1047707 := bstep (se 1 (by rfl) ⟨785780, by rfl⟩ : syracuseStep 1047707 = 1571561) B1571561
theorem B1048031 : Blo 463784 1048031 := bstep (se 1 (by rfl) ⟨786023, by rfl⟩ : syracuseStep 1048031 = 1572047) B1572047
theorem B14384719 : Blo 463784 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B3539051 : Blo 463784 3539051 := bstep (se 1 (by rfl) ⟨2654288, by rfl⟩ : syracuseStep 3539051 = 5308577) B5308577
theorem B884999 : Blo 463784 884999 := bstep (se 1 (by rfl) ⟨663749, by rfl⟩ : syracuseStep 884999 = 1327499) B1327499
theorem B1048859 : Blo 463784 1048859 := bstep (se 1 (by rfl) ⟨786644, by rfl⟩ : syracuseStep 1048859 = 1573289) B1573289
theorem B8192609 : Blo 463784 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B525415 : Blo 463784 525415 := bstep (se 1 (by rfl) ⟨394061, by rfl⟩ : syracuseStep 525415 = 788123) B788123
theorem B1049939 : Blo 463784 1049939 := bstep (se 1 (by rfl) ⟨787454, by rfl⟩ : syracuseStep 1049939 = 1574909) B1574909
theorem B525775 : Blo 463784 525775 := bstep (se 1 (by rfl) ⟨394331, by rfl⟩ : syracuseStep 525775 = 788663) B788663
theorem B2360825 : Blo 463784 2360825 := bstep (se 2 (by rfl) ⟨885309, by rfl⟩ : syracuseStep 2360825 = 1770619) B1770619
theorem B1116031 : Blo 463784 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B4458473 : Blo 463784 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B886783 : Blo 463784 886783 := bstep (se 1 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 886783 = 1330175) B1330175
theorem B3541481 : Blo 463784 3541481 := bstep (se 2 (by rfl) ⟨1328055, by rfl⟩ : syracuseStep 3541481 = 2656111) B2656111
theorem B1772351 : Blo 463784 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B789385 : Blo 463784 789385 := bstep (se 2 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 789385 = 592039) B592039
theorem B1182671 : Blo 463784 1182671 := bstep (se 1 (by rfl) ⟨887003, by rfl⟩ : syracuseStep 1182671 = 1774007) B1774007
theorem B12881065 : Blo 463784 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B2362607 : Blo 463784 2362607 := bstep (se 1 (by rfl) ⟨1771955, by rfl⟩ : syracuseStep 2362607 = 3543911) B3543911
theorem B1052063 : Blo 463784 1052063 := bstep (se 1 (by rfl) ⟨789047, by rfl⟩ : syracuseStep 1052063 = 1578095) B1578095
theorem B2821985 : Blo 463784 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B3542939 : Blo 463784 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B2985923 : Blo 463784 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B1675403 : Blo 463784 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B1183967 : Blo 463784 1183967 := bstep (se 1 (by rfl) ⟨887975, by rfl⟩ : syracuseStep 1183967 = 1775951) B1775951
theorem B3412655 : Blo 463784 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B463919 : Blo 463784 463919 := bstep (se 1 (by rfl) ⟨347939, by rfl⟩ : syracuseStep 463919 = 695879) B695879
theorem B4494491 : Blo 463784 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B464287 : Blo 463784 464287 := bstep (se 1 (by rfl) ⟨348215, by rfl⟩ : syracuseStep 464287 = 696431) B696431
theorem B464411 : Blo 463784 464411 := bstep (se 1 (by rfl) ⟨348308, by rfl⟩ : syracuseStep 464411 = 696617) B696617
theorem B464743 : Blo 463784 464743 := bstep (se 1 (by rfl) ⟨348557, by rfl⟩ : syracuseStep 464743 = 697115) B697115
theorem B464807 : Blo 463784 464807 := bstep (se 1 (by rfl) ⟨348605, by rfl⟩ : syracuseStep 464807 = 697211) B697211
theorem B464831 : Blo 463784 464831 := bstep (se 1 (by rfl) ⟨348623, by rfl⟩ : syracuseStep 464831 = 697247) B697247
theorem B2365523 : Blo 463784 2365523 := bstep (se 1 (by rfl) ⟨1774142, by rfl⟩ : syracuseStep 2365523 = 3548285) B3548285
theorem B465055 : Blo 463784 465055 := bstep (se 1 (by rfl) ⟨348791, by rfl⟩ : syracuseStep 465055 = 697583) B697583
theorem B465135 : Blo 463784 465135 := bstep (se 1 (by rfl) ⟨348851, by rfl⟩ : syracuseStep 465135 = 697703) B697703
theorem B465151 : Blo 463784 465151 := bstep (se 1 (by rfl) ⟨348863, by rfl⟩ : syracuseStep 465151 = 697727) B697727
theorem B465279 : Blo 463784 465279 := bstep (se 1 (by rfl) ⟨348959, by rfl⟩ : syracuseStep 465279 = 697919) B697919
theorem B7969427 : Blo 463784 7969427 := bstep (se 1 (by rfl) ⟨5977070, by rfl⟩ : syracuseStep 7969427 = 11954141) B11954141
theorem B465599 : Blo 463784 465599 := bstep (se 1 (by rfl) ⟨349199, by rfl⟩ : syracuseStep 465599 = 698399) B698399
theorem B465615 : Blo 463784 465615 := bstep (se 1 (by rfl) ⟨349211, by rfl⟩ : syracuseStep 465615 = 698423) B698423
theorem B465639 : Blo 463784 465639 := bstep (se 1 (by rfl) ⟨349229, by rfl⟩ : syracuseStep 465639 = 698459) B698459
theorem B465663 : Blo 463784 465663 := bstep (se 1 (by rfl) ⟨349247, by rfl⟩ : syracuseStep 465663 = 698495) B698495
theorem B465903 : Blo 463784 465903 := bstep (se 1 (by rfl) ⟨349427, by rfl⟩ : syracuseStep 465903 = 698855) B698855
theorem B1121471 : Blo 463784 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B695807 : Blo 463784 695807 := bstep (se 1 (by rfl) ⟨521855, by rfl⟩ : syracuseStep 695807 = 1043711) B1043711
theorem B466459 : Blo 463784 466459 := bstep (se 1 (by rfl) ⟨349844, by rfl⟩ : syracuseStep 466459 = 699689) B699689
theorem B467103 : Blo 463784 467103 := bstep (se 1 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 467103 = 700655) B700655
theorem B467359 : Blo 463784 467359 := bstep (se 1 (by rfl) ⟨350519, by rfl⟩ : syracuseStep 467359 = 701039) B701039
theorem B467431 : Blo 463784 467431 := bstep (se 1 (by rfl) ⟨350573, by rfl⟩ : syracuseStep 467431 = 701147) B701147
theorem B696959 : Blo 463784 696959 := bstep (se 1 (by rfl) ⟨522719, by rfl⟩ : syracuseStep 696959 = 1045439) B1045439
theorem B467687 : Blo 463784 467687 := bstep (se 1 (by rfl) ⟨350765, by rfl⟩ : syracuseStep 467687 = 701531) B701531
theorem B467707 : Blo 463784 467707 := bstep (se 1 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 467707 = 701561) B701561
theorem B467711 : Blo 463784 467711 := bstep (se 1 (by rfl) ⟨350783, by rfl⟩ : syracuseStep 467711 = 701567) B701567
theorem B39429575 : Blo 463784 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B698363 : Blo 463784 698363 := bstep (se 1 (by rfl) ⟨523772, by rfl⟩ : syracuseStep 698363 = 1047545) B1047545
theorem B698471 : Blo 463784 698471 := bstep (se 1 (by rfl) ⟨523853, by rfl⟩ : syracuseStep 698471 = 1047707) B1047707
theorem B19179625 : Blo 463784 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B698687 : Blo 463784 698687 := bstep (se 1 (by rfl) ⟨524015, by rfl⟩ : syracuseStep 698687 = 1048031) B1048031
theorem B3353339 : Blo 463784 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B699887 : Blo 463784 699887 := bstep (se 1 (by rfl) ⟨524915, by rfl⟩ : syracuseStep 699887 = 1049831) B1049831
theorem B1060399 : Blo 463784 1060399 := bstep (se 1 (by rfl) ⟨795299, by rfl⟩ : syracuseStep 1060399 = 1590599) B1590599
theorem B72790811 : Blo 463784 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B10761659 : Blo 463784 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B1488887 : Blo 463784 1488887 := bstep (se 1 (by rfl) ⟨1116665, by rfl⟩ : syracuseStep 1488887 = 2233331) B2233331
theorem B11483801 : Blo 463784 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B1490015 : Blo 463784 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B999049 : Blo 463784 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B3981707 : Blo 463784 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B1885639 : Blo 463784 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B838271 : Blo 463784 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B2642489 : Blo 463784 2642489 := bstep (se 2 (by rfl) ⟨990933, by rfl⟩ : syracuseStep 2642489 = 1981867) B1981867
theorem B9097903 : Blo 463784 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B1495999 : Blo 463784 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B12440989 : Blo 463784 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B7951931 : Blo 463784 7951931 := bstep (se 1 (by rfl) ⟨5963948, by rfl⟩ : syracuseStep 7951931 = 11927897) B11927897
theorem B3791063 : Blo 463784 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B12114683 : Blo 463784 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B2120575 : Blo 463784 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B16309349 : Blo 463784 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B4480343 : Blo 463784 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B7986923 : Blo 463784 7986923 := bstep (se 1 (by rfl) ⟨5990192, by rfl⟩ : syracuseStep 7986923 = 11980385) B11980385
theorem B2384093 : Blo 463784 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B1761871 : Blo 463784 1761871 := bstep (se 1 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 1761871 = 2642807) B2642807
theorem B1762175 : Blo 463784 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B7169201 : Blo 463784 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B1697545 : Blo 463784 1697545 := bstep (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) B1273159
theorem B13559795 : Blo 463784 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B1174763 : Blo 463784 1174763 := bstep (se 1 (by rfl) ⟨881072, by rfl⟩ : syracuseStep 1174763 = 1762145) B1762145
theorem B9563603 : Blo 463784 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B6352643 : Blo 463784 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1568591 : Blo 463784 1568591 := bstep (se 1 (by rfl) ⟨1176443, by rfl⟩ : syracuseStep 1568591 = 2352887) B2352887
theorem B1175593 : Blo 463784 1175593 := bstep (se 2 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 1175593 = 881695) B881695
theorem B1700135 : Blo 463784 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B8057249 : Blo 463784 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B1045223 : Blo 463784 1045223 := bstep (se 1 (by rfl) ⟨783917, by rfl⟩ : syracuseStep 1045223 = 1567835) B1567835
theorem B16118635 : Blo 463784 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B522175 : Blo 463784 522175 := bstep (se 1 (by rfl) ⟨391631, by rfl⟩ : syracuseStep 522175 = 783263) B783263
theorem B1046519 : Blo 463784 1046519 := bstep (se 1 (by rfl) ⟨784889, by rfl⟩ : syracuseStep 1046519 = 1569779) B1569779
theorem B882751 : Blo 463784 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B4618457 : Blo 463784 4618457 := bstep (se 2 (by rfl) ⟨1731921, by rfl⟩ : syracuseStep 4618457 = 3463843) B3463843
theorem B9567557 : Blo 463784 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B2391707 : Blo 463784 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B2359367 : Blo 463784 2359367 := bstep (se 1 (by rfl) ⟨1769525, by rfl⟩ : syracuseStep 2359367 = 3539051) B3539051
theorem B589999 : Blo 463784 589999 := bstep (se 1 (by rfl) ⟨442499, by rfl⟩ : syracuseStep 589999 = 884999) B884999
theorem B2654471 : Blo 463784 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B1573883 : Blo 463784 1573883 := bstep (se 1 (by rfl) ⟨1180412, by rfl⟩ : syracuseStep 1573883 = 2360825) B2360825
theorem B2360987 : Blo 463784 2360987 := bstep (se 1 (by rfl) ⟨1770740, by rfl⟩ : syracuseStep 2360987 = 3541481) B3541481
theorem B558847 : Blo 463784 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B1181567 : Blo 463784 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B788447 : Blo 463784 788447 := bstep (se 1 (by rfl) ⟨591335, by rfl⟩ : syracuseStep 788447 = 1182671) B1182671
theorem B1575071 : Blo 463784 1575071 := bstep (se 1 (by rfl) ⟨1181303, by rfl⟩ : syracuseStep 1575071 = 2362607) B2362607
theorem B2263393 : Blo 463784 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B2361959 : Blo 463784 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B1182377 : Blo 463784 1182377 := bstep (se 2 (by rfl) ⟨443391, by rfl⟩ : syracuseStep 1182377 = 886783) B886783
theorem B1116935 : Blo 463784 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B789311 : Blo 463784 789311 := bstep (se 1 (by rfl) ⟨591983, by rfl⟩ : syracuseStep 789311 = 1183967) B1183967
theorem B1052513 : Blo 463784 1052513 := bstep (se 2 (by rfl) ⟨394692, by rfl⟩ : syracuseStep 1052513 = 789385) B789385
theorem B1577015 : Blo 463784 1577015 := bstep (se 1 (by rfl) ⟨1182761, by rfl⟩ : syracuseStep 1577015 = 2365523) B2365523
theorem B2527375 : Blo 463784 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B17174753 : Blo 463784 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B5312951 : Blo 463784 5312951 := bstep (se 1 (by rfl) ⟨3984713, by rfl⟩ : syracuseStep 5312951 = 7969427) B7969427
theorem B1413865 : Blo 463784 1413865 := bstep (se 2 (by rfl) ⟨530199, by rfl⟩ : syracuseStep 1413865 = 1060399) B1060399
theorem B2986895 : Blo 463784 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B463871 : Blo 463784 463871 := bstep (se 1 (by rfl) ⟨347903, by rfl⟩ : syracuseStep 463871 = 695807) B695807
theorem B464639 : Blo 463784 464639 := bstep (se 1 (by rfl) ⟨348479, by rfl⟩ : syracuseStep 464639 = 696959) B696959
theorem B26286383 : Blo 463784 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B465575 : Blo 463784 465575 := bstep (se 1 (by rfl) ⟨349181, by rfl⟩ : syracuseStep 465575 = 698363) B698363
theorem B465647 : Blo 463784 465647 := bstep (se 1 (by rfl) ⟨349235, by rfl⟩ : syracuseStep 465647 = 698471) B698471
theorem B465791 : Blo 463784 465791 := bstep (se 1 (by rfl) ⟨349343, by rfl⟩ : syracuseStep 465791 = 698687) B698687
theorem B2235559 : Blo 463784 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B16587985 : Blo 463784 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B466591 : Blo 463784 466591 := bstep (se 1 (by rfl) ⟨349943, by rfl⟩ : syracuseStep 466591 = 699887) B699887
theorem B4235095 : Blo 463784 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B696233 : Blo 463784 696233 := bstep (se 2 (by rfl) ⟨261087, by rfl⟩ : syracuseStep 696233 = 522175) B522175
theorem B696815 : Blo 463784 696815 := bstep (se 1 (by rfl) ⟨522611, by rfl⟩ : syracuseStep 696815 = 1045223) B1045223
theorem B2827433 : Blo 463784 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B25502941 : Blo 463784 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B992591 : Blo 463784 992591 := bstep (se 1 (by rfl) ⟨744443, by rfl⟩ : syracuseStep 992591 = 1488887) B1488887
theorem B697679 : Blo 463784 697679 := bstep (se 1 (by rfl) ⟨523259, by rfl⟩ : syracuseStep 697679 = 1046519) B1046519
theorem B993343 : Blo 463784 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B699239 : Blo 463784 699239 := bstep (se 1 (by rfl) ⟨524429, by rfl⟩ : syracuseStep 699239 = 1048859) B1048859
theorem B699959 : Blo 463784 699959 := bstep (se 1 (by rfl) ⟨524969, by rfl⟩ : syracuseStep 699959 = 1049939) B1049939
theorem B700553 : Blo 463784 700553 := bstep (se 2 (by rfl) ⟨262707, by rfl⟩ : syracuseStep 700553 = 525415) B525415
theorem B701033 : Blo 463784 701033 := bstep (se 2 (by rfl) ⟨262887, by rfl⟩ : syracuseStep 701033 = 525775) B525775
theorem B701375 : Blo 463784 701375 := bstep (se 1 (by rfl) ⟨526031, by rfl⟩ : syracuseStep 701375 = 1052063) B1052063
theorem B1488041 : Blo 463784 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1881323 : Blo 463784 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B25572833 : Blo 463784 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B2275103 : Blo 463784 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B2996327 : Blo 463784 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B8076455 : Blo 463784 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B5324615 : Blo 463784 5324615 := bstep (se 1 (by rfl) ⟨3993461, by rfl⟩ : syracuseStep 5324615 = 7986923) B7986923
theorem B1589395 : Blo 463784 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B1133423 : Blo 463784 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B6377885 : Blo 463784 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B7655867 : Blo 463784 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B1332065 : Blo 463784 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B6378371 : Blo 463784 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B5461739 : Blo 463784 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B2349161 : Blo 463784 2349161 := bstep (se 2 (by rfl) ⟨880935, by rfl⟩ : syracuseStep 2349161 = 1761871) B1761871
theorem B2972315 : Blo 463784 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B2514185 : Blo 463784 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B1990615 : Blo 463784 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B1761659 : Blo 463784 1761659 := bstep (se 1 (by rfl) ⟨1321244, by rfl⟩ : syracuseStep 1761659 = 2642489) B2642489
theorem B48522149 : Blo 463784 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B5301287 : Blo 463784 5301287 := bstep (se 1 (by rfl) ⟨3975965, by rfl⟩ : syracuseStep 5301287 = 7951931) B7951931
theorem B10872899 : Blo 463784 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B747647 : Blo 463784 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B1567457 : Blo 463784 1567457 := bstep (se 2 (by rfl) ⟨587796, by rfl⟩ : syracuseStep 1567457 = 1175593) B1175593
theorem B1174783 : Blo 463784 1174783 := bstep (se 1 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 1174783 = 1762175) B1762175
theorem B4779467 : Blo 463784 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B21491513 : Blo 463784 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B1994665 : Blo 463784 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B9039863 : Blo 463784 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B783175 : Blo 463784 783175 := bstep (se 1 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 783175 = 1174763) B1174763
theorem B1045727 : Blo 463784 1045727 := bstep (se 1 (by rfl) ⟨784295, by rfl⟩ : syracuseStep 1045727 = 1568591) B1568591
theorem B1177001 : Blo 463784 1177001 := bstep (se 2 (by rfl) ⟨441375, by rfl⟩ : syracuseStep 1177001 = 882751) B882751
theorem B5371499 : Blo 463784 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B48527207 : Blo 463784 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B7174439 : Blo 463784 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B3078971 : Blo 463784 3078971 := bstep (se 1 (by rfl) ⟨2309228, by rfl⟩ : syracuseStep 3078971 = 4618457) B4618457
theorem B1572911 : Blo 463784 1572911 := bstep (se 1 (by rfl) ⟨1179683, by rfl⟩ : syracuseStep 1572911 = 2359367) B2359367
theorem B1769647 : Blo 463784 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B786665 : Blo 463784 786665 := bstep (se 2 (by rfl) ⟨294999, by rfl⟩ : syracuseStep 786665 = 589999) B589999
theorem B1049255 : Blo 463784 1049255 := bstep (se 1 (by rfl) ⟨786941, by rfl⟩ : syracuseStep 1049255 = 1573883) B1573883
theorem B1573991 : Blo 463784 1573991 := bstep (se 1 (by rfl) ⟨1180493, by rfl⟩ : syracuseStep 1573991 = 2360987) B2360987
theorem B787711 : Blo 463784 787711 := bstep (se 1 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 787711 = 1181567) B1181567
theorem B525631 : Blo 463784 525631 := bstep (se 1 (by rfl) ⟨394223, by rfl⟩ : syracuseStep 525631 = 788447) B788447
theorem B1050047 : Blo 463784 1050047 := bstep (se 1 (by rfl) ⟨787535, by rfl⟩ : syracuseStep 1050047 = 1575071) B1575071
theorem B1574639 : Blo 463784 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B788251 : Blo 463784 788251 := bstep (se 1 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 788251 = 1182377) B1182377
theorem B526207 : Blo 463784 526207 := bstep (se 1 (by rfl) ⟨394655, by rfl⟩ : syracuseStep 526207 = 789311) B789311
theorem B755615 : Blo 463784 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B7965053 : Blo 463784 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B1051343 : Blo 463784 1051343 := bstep (se 1 (by rfl) ⟨788507, by rfl⟩ : syracuseStep 1051343 = 1577015) B1577015
theorem B3541967 : Blo 463784 3541967 := bstep (se 1 (by rfl) ⟨2656475, by rfl⟩ : syracuseStep 3541967 = 5312951) B5312951
theorem B3017857 : Blo 463784 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B3641159 : Blo 463784 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B1676123 : Blo 463784 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B2659553 : Blo 463784 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B464155 : Blo 463784 464155 := bstep (se 1 (by rfl) ⟨348116, by rfl⟩ : syracuseStep 464155 = 696233) B696233
theorem B464543 : Blo 463784 464543 := bstep (se 1 (by rfl) ⟨348407, by rfl⟩ : syracuseStep 464543 = 696815) B696815
theorem B32348099 : Blo 463784 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B661727 : Blo 463784 661727 := bstep (se 1 (by rfl) ⟨496295, by rfl⟩ : syracuseStep 661727 = 992591) B992591
theorem B465119 : Blo 463784 465119 := bstep (se 1 (by rfl) ⟨348839, by rfl⟩ : syracuseStep 465119 = 697679) B697679
theorem B7248599 : Blo 463784 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B498431 : Blo 463784 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B466159 : Blo 463784 466159 := bstep (se 1 (by rfl) ⟨349619, by rfl⟩ : syracuseStep 466159 = 699239) B699239
theorem B3186311 : Blo 463784 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B466639 : Blo 463784 466639 := bstep (se 1 (by rfl) ⟨349979, by rfl⟩ : syracuseStep 466639 = 699959) B699959
theorem B14327675 : Blo 463784 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B467035 : Blo 463784 467035 := bstep (se 1 (by rfl) ⟨350276, by rfl⟩ : syracuseStep 467035 = 700553) B700553
theorem B467355 : Blo 463784 467355 := bstep (se 1 (by rfl) ⟨350516, by rfl⟩ : syracuseStep 467355 = 701033) B701033
theorem B467583 : Blo 463784 467583 := bstep (se 1 (by rfl) ⟨350687, by rfl⟩ : syracuseStep 467583 = 701375) B701375
theorem B992027 : Blo 463784 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B697151 : Blo 463784 697151 := bstep (se 1 (by rfl) ⟨522863, by rfl⟩ : syracuseStep 697151 = 1045727) B1045727
theorem B1254215 : Blo 463784 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B17048555 : Blo 463784 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B3580999 : Blo 463784 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B1516735 : Blo 463784 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B32351471 : Blo 463784 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B5384303 : Blo 463784 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B5646793 : Blo 463784 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B3549743 : Blo 463784 3549743 := bstep (se 1 (by rfl) ⟨2662307, by rfl⟩ : syracuseStep 3549743 = 5324615) B5324615
theorem B3552173 : Blo 463784 3552173 := bstep (se 3 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 3552173 = 1332065) B1332065
theorem B701675 : Blo 463784 701675 := bstep (se 1 (by rfl) ⟨526256, by rfl⟩ : syracuseStep 701675 = 1052513) B1052513
theorem B1324457 : Blo 463784 1324457 := bstep (se 2 (by rfl) ⟨496671, by rfl⟩ : syracuseStep 1324457 = 993343) B993343
theorem B11449835 : Blo 463784 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B1981543 : Blo 463784 1981543 := bstep (se 1 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 1981543 = 2972315) B2972315
theorem B1884955 : Blo 463784 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B1885153 : Blo 463784 1885153 := bstep (se 2 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 1885153 = 1413865) B1413865
theorem B2052647 : Blo 463784 2052647 := bstep (se 1 (by rfl) ⟨1539485, by rfl⟩ : syracuseStep 2052647 = 3078971) B3078971
theorem B2119193 : Blo 463784 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B34003921 : Blo 463784 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B744623 : Blo 463784 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B745129 : Blo 463784 745129 := bstep (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) B558847
theorem B4251923 : Blo 463784 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B5103911 : Blo 463784 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B4252247 : Blo 463784 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B1566107 : Blo 463784 1566107 := bstep (se 1 (by rfl) ⟨1174580, by rfl⟩ : syracuseStep 1566107 = 2349161) B2349161
theorem B17524255 : Blo 463784 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B1566377 : Blo 463784 1566377 := bstep (se 2 (by rfl) ⟨587391, by rfl⟩ : syracuseStep 1566377 = 1174783) B1174783
theorem B3369833 : Blo 463784 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B1174439 : Blo 463784 1174439 := bstep (se 1 (by rfl) ⟨880829, by rfl⟩ : syracuseStep 1174439 = 1761659) B1761659
theorem B3534191 : Blo 463784 3534191 := bstep (se 1 (by rfl) ⟨2650643, by rfl⟩ : syracuseStep 3534191 = 5301287) B5301287
theorem B1044233 : Blo 463784 1044233 := bstep (se 2 (by rfl) ⟨391587, by rfl⟩ : syracuseStep 1044233 = 783175) B783175
theorem B1044971 : Blo 463784 1044971 := bstep (se 1 (by rfl) ⟨783728, by rfl⟩ : syracuseStep 1044971 = 1567457) B1567457
theorem B6026575 : Blo 463784 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B784667 : Blo 463784 784667 := bstep (se 1 (by rfl) ⟨588500, by rfl⟩ : syracuseStep 784667 = 1177001) B1177001
theorem B1997551 : Blo 463784 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B4782959 : Blo 463784 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B2980745 : Blo 463784 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B22117313 : Blo 463784 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B2654153 : Blo 463784 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B1048607 : Blo 463784 1048607 := bstep (se 1 (by rfl) ⟨786455, by rfl⟩ : syracuseStep 1048607 = 1572911) B1572911
theorem B524443 : Blo 463784 524443 := bstep (se 1 (by rfl) ⟨393332, by rfl⟩ : syracuseStep 524443 = 786665) B786665
theorem B2359529 : Blo 463784 2359529 := bstep (se 2 (by rfl) ⟨884823, by rfl⟩ : syracuseStep 2359529 = 1769647) B1769647
theorem B1049327 : Blo 463784 1049327 := bstep (se 1 (by rfl) ⟨786995, by rfl⟩ : syracuseStep 1049327 = 1573991) B1573991
theorem B1049759 : Blo 463784 1049759 := bstep (se 1 (by rfl) ⟨787319, by rfl⟩ : syracuseStep 1049759 = 1574639) B1574639
theorem B5310035 : Blo 463784 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B1050281 : Blo 463784 1050281 := bstep (se 2 (by rfl) ⟨393855, by rfl⟩ : syracuseStep 1050281 = 787711) B787711
theorem B2361311 : Blo 463784 2361311 := bstep (se 1 (by rfl) ⟨1770983, by rfl⟩ : syracuseStep 2361311 = 3541967) B3541967
theorem B23365673 : Blo 463784 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B3344573 : Blo 463784 3344573 := bstep (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) B1254215
theorem B1051001 : Blo 463784 1051001 := bstep (se 2 (by rfl) ⟨394125, by rfl⟩ : syracuseStep 1051001 = 788251) B788251
theorem B1117415 : Blo 463784 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B1773035 : Blo 463784 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B1412795 : Blo 463784 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B496415 : Blo 463784 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B464767 : Blo 463784 464767 := bstep (se 1 (by rfl) ⟨348575, by rfl⟩ : syracuseStep 464767 = 697151) B697151
theorem B21567647 : Blo 463784 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B2366495 : Blo 463784 2366495 := bstep (se 1 (by rfl) ⟨1774871, by rfl⟩ : syracuseStep 2366495 = 3549743) B3549743
theorem B8035433 : Blo 463784 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B696155 : Blo 463784 696155 := bstep (se 1 (by rfl) ⟨522116, by rfl⟩ : syracuseStep 696155 = 1044233) B1044233
theorem B696647 : Blo 463784 696647 := bstep (se 1 (by rfl) ⟨522485, by rfl⟩ : syracuseStep 696647 = 1044971) B1044971
theorem B2368115 : Blo 463784 2368115 := bstep (se 1 (by rfl) ⟨1776086, by rfl⟩ : syracuseStep 2368115 = 3552173) B3552173
theorem B467783 : Blo 463784 467783 := bstep (se 1 (by rfl) ⟨350837, by rfl⟩ : syracuseStep 467783 = 701675) B701675
theorem B3974021 : Blo 463784 3974021 := bstep (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) B745129
theorem B2663401 : Blo 463784 2663401 := bstep (se 2 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 2663401 = 1997551) B1997551
theorem B8496829 : Blo 463784 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B3188639 : Blo 463784 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B9709757 : Blo 463784 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B699503 : Blo 463784 699503 := bstep (se 1 (by rfl) ⟨524627, by rfl⟩ : syracuseStep 699503 = 1049255) B1049255
theorem B700031 : Blo 463784 700031 := bstep (se 1 (by rfl) ⟨525023, by rfl⟩ : syracuseStep 700031 = 1050047) B1050047
theorem B503743 : Blo 463784 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B700841 : Blo 463784 700841 := bstep (se 2 (by rfl) ⟨262815, by rfl⟩ : syracuseStep 700841 = 525631) B525631
theorem B700895 : Blo 463784 700895 := bstep (se 1 (by rfl) ⟨525671, by rfl⟩ : syracuseStep 700895 = 1051343) B1051343
theorem B701609 : Blo 463784 701609 := bstep (se 2 (by rfl) ⟨263103, by rfl⟩ : syracuseStep 701609 = 526207) B526207
theorem B4832399 : Blo 463784 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B86261597 : Blo 463784 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B9551783 : Blo 463784 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B2834615 : Blo 463784 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B2834831 : Blo 463784 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B3589535 : Blo 463784 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B2246555 : Blo 463784 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B1329149 : Blo 463784 1329149 := bstep (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) B498431
theorem B45338561 : Blo 463784 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B2642057 : Blo 463784 2642057 := bstep (se 2 (by rfl) ⟨990771, by rfl⟩ : syracuseStep 2642057 = 1981543) B1981543
theorem B1987163 : Blo 463784 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B2513273 : Blo 463784 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B2513537 : Blo 463784 2513537 := bstep (se 2 (by rfl) ⟨942576, by rfl⟩ : syracuseStep 2513537 = 1885153) B1885153
theorem B2645405 : Blo 463784 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B1368431 : Blo 463784 1368431 := bstep (se 1 (by rfl) ⟨1026323, by rfl⟩ : syracuseStep 1368431 = 2052647) B2052647
theorem B7529057 : Blo 463784 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B4023809 : Blo 463784 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B3402607 : Blo 463784 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B19098661 : Blo 463784 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B1764605 : Blo 463784 1764605 := bstep (se 3 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 1764605 = 661727) B661727
theorem B11365703 : Blo 463784 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B1044071 : Blo 463784 1044071 := bstep (se 1 (by rfl) ⟨783053, by rfl⟩ : syracuseStep 1044071 = 1566107) B1566107
theorem B8089253 : Blo 463784 8089253 := bstep (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) B1516735
theorem B1044251 : Blo 463784 1044251 := bstep (se 1 (by rfl) ⟨783188, by rfl⟩ : syracuseStep 1044251 = 1566377) B1566377
theorem B782959 : Blo 463784 782959 := bstep (se 1 (by rfl) ⟨587219, by rfl⟩ : syracuseStep 782959 = 1174439) B1174439
theorem B2356127 : Blo 463784 2356127 := bstep (se 1 (by rfl) ⟨1767095, by rfl⟩ : syracuseStep 2356127 = 3534191) B3534191
theorem B882971 : Blo 463784 882971 := bstep (se 1 (by rfl) ⟨662228, by rfl⟩ : syracuseStep 882971 = 1324457) B1324457
theorem B7633223 : Blo 463784 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B523111 : Blo 463784 523111 := bstep (se 1 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 523111 = 784667) B784667
theorem B14744875 : Blo 463784 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B1769435 : Blo 463784 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B1573019 : Blo 463784 1573019 := bstep (se 1 (by rfl) ⟨1179764, by rfl⟩ : syracuseStep 1573019 = 2359529) B2359529
theorem B2393023 : Blo 463784 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B3540023 : Blo 463784 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B1574207 : Blo 463784 1574207 := bstep (se 1 (by rfl) ⟨1180655, by rfl⟩ : syracuseStep 1574207 = 2361311) B2361311
theorem B2229715 : Blo 463784 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B1182023 : Blo 463784 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B26808245 : Blo 463784 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B25464881 : Blo 463784 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1675691 : Blo 463784 1675691 := bstep (se 1 (by rfl) ⟨1256768, by rfl⟩ : syracuseStep 1675691 = 2513537) B2513537
theorem B1577663 : Blo 463784 1577663 := bstep (se 1 (by rfl) ⟨1183247, by rfl⟩ : syracuseStep 1577663 = 2366495) B2366495
theorem B464103 : Blo 463784 464103 := bstep (se 1 (by rfl) ⟨348077, by rfl⟩ : syracuseStep 464103 = 696155) B696155
theorem B3544397 : Blo 463784 3544397 := bstep (se 3 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 3544397 = 1329149) B1329149
theorem B464431 : Blo 463784 464431 := bstep (se 1 (by rfl) ⟨348323, by rfl⟩ : syracuseStep 464431 = 696647) B696647
theorem B5019371 : Blo 463784 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B1578743 : Blo 463784 1578743 := bstep (se 1 (by rfl) ⟨1184057, by rfl⟩ : syracuseStep 1578743 = 2368115) B2368115
theorem B57513725 : Blo 463784 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B466335 : Blo 463784 466335 := bstep (se 1 (by rfl) ⟨349751, by rfl⟩ : syracuseStep 466335 = 699503) B699503
theorem B7577135 : Blo 463784 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B696047 : Blo 463784 696047 := bstep (se 1 (by rfl) ⟨522035, by rfl⟩ : syracuseStep 696047 = 1044071) B1044071
theorem B466687 : Blo 463784 466687 := bstep (se 1 (by rfl) ⟨350015, by rfl⟩ : syracuseStep 466687 = 700031) B700031
theorem B696167 : Blo 463784 696167 := bstep (se 1 (by rfl) ⟨522125, by rfl⟩ : syracuseStep 696167 = 1044251) B1044251
theorem B467227 : Blo 463784 467227 := bstep (se 1 (by rfl) ⟨350420, by rfl⟩ : syracuseStep 467227 = 700841) B700841
theorem B467263 : Blo 463784 467263 := bstep (se 1 (by rfl) ⟨350447, by rfl⟩ : syracuseStep 467263 = 700895) B700895
theorem B12886397 : Blo 463784 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B467739 : Blo 463784 467739 := bstep (se 1 (by rfl) ⟨350804, by rfl⟩ : syracuseStep 467739 = 701609) B701609
theorem B697481 : Blo 463784 697481 := bstep (se 2 (by rfl) ⟨261555, by rfl⟩ : syracuseStep 697481 = 523111) B523111
theorem B5088815 : Blo 463784 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B25471421 : Blo 463784 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B699071 : Blo 463784 699071 := bstep (se 1 (by rfl) ⟨524303, by rfl⟩ : syracuseStep 699071 = 1048607) B1048607
theorem B699257 : Blo 463784 699257 := bstep (se 2 (by rfl) ⟨262221, by rfl⟩ : syracuseStep 699257 = 524443) B524443
theorem B699551 : Blo 463784 699551 := bstep (se 1 (by rfl) ⟨524663, by rfl⟩ : syracuseStep 699551 = 1049327) B1049327
theorem B699839 : Blo 463784 699839 := bstep (se 1 (by rfl) ⟨524879, by rfl⟩ : syracuseStep 699839 = 1049759) B1049759
theorem B700187 : Blo 463784 700187 := bstep (se 1 (by rfl) ⟨525140, by rfl⟩ : syracuseStep 700187 = 1050281) B1050281
theorem B3551201 : Blo 463784 3551201 := bstep (se 2 (by rfl) ⟨1331700, by rfl⟩ : syracuseStep 3551201 = 2663401) B2663401
theorem B15577115 : Blo 463784 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B700667 : Blo 463784 700667 := bstep (se 1 (by rfl) ⟨525500, by rfl⟩ : syracuseStep 700667 = 1051001) B1051001
theorem B1323773 : Blo 463784 1323773 := bstep (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) B496415
theorem B30225707 : Blo 463784 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B1324775 : Blo 463784 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B4536809 : Blo 463784 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B5356955 : Blo 463784 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B671657 : Blo 463784 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B6473171 : Blo 463784 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B5392835 : Blo 463784 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B1889743 : Blo 463784 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B1889887 : Blo 463784 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B1497703 : Blo 463784 1497703 := bstep (se 1 (by rfl) ⟨1123277, by rfl⟩ : syracuseStep 1497703 = 2246555) B2246555
theorem B11329105 : Blo 463784 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B941863 : Blo 463784 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B1761371 : Blo 463784 1761371 := bstep (se 1 (by rfl) ⟨1321028, by rfl⟩ : syracuseStep 1761371 = 2642057) B2642057
theorem B1763603 : Blo 463784 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B912287 : Blo 463784 912287 := bstep (se 1 (by rfl) ⟨684215, by rfl⟩ : syracuseStep 912287 = 1368431) B1368431
theorem B2649347 : Blo 463784 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B1043945 : Blo 463784 1043945 := bstep (se 2 (by rfl) ⟨391479, by rfl⟩ : syracuseStep 1043945 = 782959) B782959
theorem B2682539 : Blo 463784 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B2125759 : Blo 463784 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B1176403 : Blo 463784 1176403 := bstep (se 1 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 1176403 = 1764605) B1764605
theorem B2979773 : Blo 463784 2979773 := bstep (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) B1117415
theorem B1570751 : Blo 463784 1570751 := bstep (se 1 (by rfl) ⟨1178063, by rfl⟩ : syracuseStep 1570751 = 2356127) B2356127
theorem B588647 : Blo 463784 588647 := bstep (se 1 (by rfl) ⟨441485, by rfl⟩ : syracuseStep 588647 = 882971) B882971
theorem B19659833 : Blo 463784 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B57507731 : Blo 463784 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B1179623 : Blo 463784 1179623 := bstep (se 1 (by rfl) ⟨884717, by rfl⟩ : syracuseStep 1179623 = 1769435) B1769435
theorem B1048679 : Blo 463784 1048679 := bstep (se 1 (by rfl) ⟨786509, by rfl⟩ : syracuseStep 1048679 = 1573019) B1573019
theorem B2360015 : Blo 463784 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B1049471 : Blo 463784 1049471 := bstep (se 1 (by rfl) ⟨787103, by rfl⟩ : syracuseStep 1049471 = 1574207) B1574207
theorem B788015 : Blo 463784 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B16976587 : Blo 463784 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B1117127 : Blo 463784 1117127 := bstep (se 1 (by rfl) ⟨837845, by rfl⟩ : syracuseStep 1117127 = 1675691) B1675691
theorem B1051775 : Blo 463784 1051775 := bstep (se 1 (by rfl) ⟨788831, by rfl⟩ : syracuseStep 1051775 = 1577663) B1577663
theorem B2362931 : Blo 463784 2362931 := bstep (se 1 (by rfl) ⟨1772198, by rfl⟩ : syracuseStep 2362931 = 3544397) B3544397
theorem B3346247 : Blo 463784 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B1052495 : Blo 463784 1052495 := bstep (se 1 (by rfl) ⟨789371, by rfl⟩ : syracuseStep 1052495 = 1578743) B1578743
theorem B38342483 : Blo 463784 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B5051423 : Blo 463784 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B464031 : Blo 463784 464031 := bstep (se 1 (by rfl) ⟨348023, by rfl⟩ : syracuseStep 464031 = 696047) B696047
theorem B464111 : Blo 463784 464111 := bstep (se 1 (by rfl) ⟨348083, by rfl⟩ : syracuseStep 464111 = 696167) B696167
theorem B8590931 : Blo 463784 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B464987 : Blo 463784 464987 := bstep (se 1 (by rfl) ⟨348740, by rfl⟩ : syracuseStep 464987 = 697481) B697481
theorem B16980947 : Blo 463784 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B466047 : Blo 463784 466047 := bstep (se 1 (by rfl) ⟨349535, by rfl⟩ : syracuseStep 466047 = 699071) B699071
theorem B466171 : Blo 463784 466171 := bstep (se 1 (by rfl) ⟨349628, by rfl⟩ : syracuseStep 466171 = 699257) B699257
theorem B466367 : Blo 463784 466367 := bstep (se 1 (by rfl) ⟨349775, by rfl⟩ : syracuseStep 466367 = 699551) B699551
theorem B466559 : Blo 463784 466559 := bstep (se 1 (by rfl) ⟨349919, by rfl⟩ : syracuseStep 466559 = 699839) B699839
theorem B695963 : Blo 463784 695963 := bstep (se 1 (by rfl) ⟨521972, by rfl⟩ : syracuseStep 695963 = 1043945) B1043945
theorem B466791 : Blo 463784 466791 := bstep (se 1 (by rfl) ⟨350093, by rfl⟩ : syracuseStep 466791 = 700187) B700187
theorem B2367467 : Blo 463784 2367467 := bstep (se 1 (by rfl) ⟨1775600, by rfl⟩ : syracuseStep 2367467 = 3551201) B3551201
theorem B467111 : Blo 463784 467111 := bstep (se 1 (by rfl) ⟨350333, by rfl⟩ : syracuseStep 467111 = 700667) B700667
theorem B3024539 : Blo 463784 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B1255817 : Blo 463784 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B3190697 : Blo 463784 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B17872163 : Blo 463784 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B2834345 : Blo 463784 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B3392543 : Blo 463784 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B608191 : Blo 463784 608191 := bstep (se 1 (by rfl) ⟨456143, by rfl⟩ : syracuseStep 608191 = 912287) B912287
theorem B1788359 : Blo 463784 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B1986515 : Blo 463784 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B1791085 : Blo 463784 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B41538973 : Blo 463784 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B4315447 : Blo 463784 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B3595223 : Blo 463784 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B2972953 : Blo 463784 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B3532733 : Blo 463784 3532733 := bstep (se 3 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 3532733 = 1324775) B1324775
theorem B1174247 : Blo 463784 1174247 := bstep (se 1 (by rfl) ⟨880685, by rfl⟩ : syracuseStep 1174247 = 1761371) B1761371
theorem B1568537 : Blo 463784 1568537 := bstep (se 2 (by rfl) ⟨588201, by rfl⟩ : syracuseStep 1568537 = 1176403) B1176403
theorem B1175735 : Blo 463784 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B2519657 : Blo 463784 2519657 := bstep (se 2 (by rfl) ⟨944871, by rfl⟩ : syracuseStep 2519657 = 1889743) B1889743
theorem B2519849 : Blo 463784 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B1766231 : Blo 463784 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B1569725 : Blo 463784 1569725 := bstep (se 3 (by rfl) ⟨294323, by rfl⟩ : syracuseStep 1569725 = 588647) B588647
theorem B882515 : Blo 463784 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B1996937 : Blo 463784 1996937 := bstep (se 2 (by rfl) ⟨748851, by rfl⟩ : syracuseStep 1996937 = 1497703) B1497703
theorem B20150471 : Blo 463784 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B1047167 : Blo 463784 1047167 := bstep (se 1 (by rfl) ⟨785375, by rfl⟩ : syracuseStep 1047167 = 1570751) B1570751
theorem B13106555 : Blo 463784 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B15105473 : Blo 463784 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B3571303 : Blo 463784 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B38338487 : Blo 463784 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B786415 : Blo 463784 786415 := bstep (se 1 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 786415 = 1179623) B1179623
theorem B1573343 : Blo 463784 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B525343 : Blo 463784 525343 := bstep (se 1 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 525343 = 788015) B788015
theorem B1575287 : Blo 463784 1575287 := bstep (se 1 (by rfl) ⟨1181465, by rfl⟩ : syracuseStep 1575287 = 2362931) B2362931
theorem B2230831 : Blo 463784 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B25561655 : Blo 463784 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B9046781 : Blo 463784 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B463975 : Blo 463784 463975 := bstep (se 1 (by rfl) ⟨347981, by rfl⟩ : syracuseStep 463975 = 695963) B695963
theorem B1578311 : Blo 463784 1578311 := bstep (se 1 (by rfl) ⟨1183733, by rfl⟩ : syracuseStep 1578311 = 2367467) B2367467
theorem B55385297 : Blo 463784 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B1679771 : Blo 463784 1679771 := bstep (se 1 (by rfl) ⟨1259828, by rfl⟩ : syracuseStep 1679771 = 2519657) B2519657
theorem B1679899 : Blo 463784 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B698111 : Blo 463784 698111 := bstep (se 1 (by rfl) ⟨523583, by rfl⟩ : syracuseStep 698111 = 1047167) B1047167
theorem B4761737 : Blo 463784 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B10070315 : Blo 463784 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B699119 : Blo 463784 699119 := bstep (se 1 (by rfl) ⟨524339, by rfl⟩ : syracuseStep 699119 = 1048679) B1048679
theorem B699647 : Blo 463784 699647 := bstep (se 1 (by rfl) ⟨524735, by rfl⟩ : syracuseStep 699647 = 1049471) B1049471
theorem B701183 : Blo 463784 701183 := bstep (se 1 (by rfl) ⟨525887, by rfl⟩ : syracuseStep 701183 = 1051775) B1051775
theorem B701663 : Blo 463784 701663 := bstep (se 1 (by rfl) ⟨526247, by rfl⟩ : syracuseStep 701663 = 1052495) B1052495
theorem B1324343 : Blo 463784 1324343 := bstep (se 1 (by rfl) ⟨993257, by rfl⟩ : syracuseStep 1324343 = 1986515) B1986515
theorem B11320631 : Blo 463784 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B2016359 : Blo 463784 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B4768957 : Blo 463784 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B837211 : Blo 463784 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B9587261 : Blo 463784 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B5753929 : Blo 463784 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B11914775 : Blo 463784 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B1331291 : Blo 463784 1331291 := bstep (se 1 (by rfl) ⟨998468, by rfl⟩ : syracuseStep 1331291 = 1996937) B1996937
theorem B8737703 : Blo 463784 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B1889563 : Blo 463784 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B744751 : Blo 463784 744751 := bstep (se 1 (by rfl) ⟨558563, by rfl⟩ : syracuseStep 744751 = 1117127) B1117127
theorem B3367615 : Blo 463784 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B22635449 : Blo 463784 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B5727287 : Blo 463784 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B2353373 : Blo 463784 2353373 := bstep (se 3 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 2353373 = 882515) B882515
theorem B2355155 : Blo 463784 2355155 := bstep (se 1 (by rfl) ⟨1766366, by rfl⟩ : syracuseStep 2355155 = 3532733) B3532733
theorem B2388113 : Blo 463784 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B782831 : Blo 463784 782831 := bstep (se 1 (by rfl) ⟨587123, by rfl⟩ : syracuseStep 782831 = 1174247) B1174247
theorem B1045691 : Blo 463784 1045691 := bstep (se 1 (by rfl) ⟨784268, by rfl⟩ : syracuseStep 1045691 = 1568537) B1568537
theorem B2127131 : Blo 463784 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B783823 : Blo 463784 783823 := bstep (se 1 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 783823 = 1175735) B1175735
theorem B1177487 : Blo 463784 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B1046483 : Blo 463784 1046483 := bstep (se 1 (by rfl) ⟨784862, by rfl⟩ : syracuseStep 1046483 = 1569725) B1569725
theorem B12974741 : Blo 463784 12974741 := bstep (se 6 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 12974741 = 608191) B608191
theorem B13433647 : Blo 463784 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B3963937 : Blo 463784 3963937 := bstep (se 2 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 3963937 = 2972953) B2972953
theorem B25558991 : Blo 463784 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B1048553 : Blo 463784 1048553 := bstep (se 2 (by rfl) ⟨393207, by rfl⟩ : syracuseStep 1048553 = 786415) B786415
theorem B1048895 : Blo 463784 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B1344239 : Blo 463784 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B4490153 : Blo 463784 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B1050191 : Blo 463784 1050191 := bstep (se 1 (by rfl) ⟨787643, by rfl⟩ : syracuseStep 1050191 = 1575287) B1575287
theorem B6358609 : Blo 463784 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B17041103 : Blo 463784 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B6391507 : Blo 463784 6391507 := bstep (se 1 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 6391507 = 9587261) B9587261
theorem B6031187 : Blo 463784 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B1116281 : Blo 463784 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B887527 : Blo 463784 887527 := bstep (se 1 (by rfl) ⟨665645, by rfl⟩ : syracuseStep 887527 = 1331291) B1331291
theorem B1052207 : Blo 463784 1052207 := bstep (se 1 (by rfl) ⟨789155, by rfl⟩ : syracuseStep 1052207 = 1578311) B1578311
theorem B7671905 : Blo 463784 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B1119847 : Blo 463784 1119847 := bstep (se 1 (by rfl) ⟨839885, by rfl⟩ : syracuseStep 1119847 = 1679771) B1679771
theorem B465407 : Blo 463784 465407 := bstep (se 1 (by rfl) ⟨349055, by rfl⟩ : syracuseStep 465407 = 698111) B698111
theorem B466079 : Blo 463784 466079 := bstep (se 1 (by rfl) ⟨349559, by rfl⟩ : syracuseStep 466079 = 699119) B699119
theorem B466431 : Blo 463784 466431 := bstep (se 1 (by rfl) ⟨349823, by rfl⟩ : syracuseStep 466431 = 699647) B699647
theorem B467455 : Blo 463784 467455 := bstep (se 1 (by rfl) ⟨350591, by rfl⟩ : syracuseStep 467455 = 701183) B701183
theorem B697127 : Blo 463784 697127 := bstep (se 1 (by rfl) ⟨522845, by rfl⟩ : syracuseStep 697127 = 1045691) B1045691
theorem B467775 : Blo 463784 467775 := bstep (se 1 (by rfl) ⟨350831, by rfl⟩ : syracuseStep 467775 = 701663) B701663
theorem B1418087 : Blo 463784 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B697655 : Blo 463784 697655 := bstep (se 1 (by rfl) ⟨523241, by rfl⟩ : syracuseStep 697655 = 1046483) B1046483
theorem B5285249 : Blo 463784 5285249 := bstep (se 2 (by rfl) ⟨1981968, by rfl⟩ : syracuseStep 5285249 = 3963937) B3963937
theorem B993001 : Blo 463784 993001 := bstep (se 2 (by rfl) ⟨372375, by rfl⟩ : syracuseStep 993001 = 744751) B744751
theorem B7547087 : Blo 463784 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B699035 : Blo 463784 699035 := bstep (se 1 (by rfl) ⟨524276, by rfl⟩ : syracuseStep 699035 = 1048553) B1048553
theorem B2239865 : Blo 463784 2239865 := bstep (se 2 (by rfl) ⟨839949, by rfl⟩ : syracuseStep 2239865 = 1679899) B1679899
theorem B700457 : Blo 463784 700457 := bstep (se 2 (by rfl) ⟨262671, by rfl⟩ : syracuseStep 700457 = 525343) B525343
theorem B7943183 : Blo 463784 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B15090299 : Blo 463784 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B3818191 : Blo 463784 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B1592075 : Blo 463784 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B17911529 : Blo 463784 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B5825135 : Blo 463784 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B2974441 : Blo 463784 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B36923531 : Blo 463784 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B3174491 : Blo 463784 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B1568915 : Blo 463784 1568915 := bstep (se 1 (by rfl) ⟨1176686, by rfl⟩ : syracuseStep 1568915 = 2353373) B2353373
theorem B6713543 : Blo 463784 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B2519417 : Blo 463784 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B1045097 : Blo 463784 1045097 := bstep (se 2 (by rfl) ⟨391911, by rfl⟩ : syracuseStep 1045097 = 783823) B783823
theorem B1570103 : Blo 463784 1570103 := bstep (se 1 (by rfl) ⟨1177577, by rfl⟩ : syracuseStep 1570103 = 2355155) B2355155
theorem B521887 : Blo 463784 521887 := bstep (se 1 (by rfl) ⟨391415, by rfl⟩ : syracuseStep 521887 = 782831) B782831
theorem B882895 : Blo 463784 882895 := bstep (se 1 (by rfl) ⟨662171, by rfl⟩ : syracuseStep 882895 = 1324343) B1324343
theorem B784991 : Blo 463784 784991 := bstep (se 1 (by rfl) ⟨588743, by rfl⟩ : syracuseStep 784991 = 1177487) B1177487
theorem B8649827 : Blo 463784 8649827 := bstep (se 1 (by rfl) ⟨6487370, by rfl⟩ : syracuseStep 8649827 = 12974741) B12974741
theorem B17039327 : Blo 463784 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B10060199 : Blo 463784 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B3965921 : Blo 463784 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B15533693 : Blo 463784 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B8522009 : Blo 463784 8522009 := bstep (se 2 (by rfl) ⟨3195753, by rfl⟩ : syracuseStep 8522009 = 6391507) B6391507
theorem B5114603 : Blo 463784 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B1183369 : Blo 463784 1183369 := bstep (se 2 (by rfl) ⟨443763, by rfl⟩ : syracuseStep 1183369 = 887527) B887527
theorem B464751 : Blo 463784 464751 := bstep (se 1 (by rfl) ⟨348563, by rfl⟩ : syracuseStep 464751 = 697127) B697127
theorem B465103 : Blo 463784 465103 := bstep (se 1 (by rfl) ⟨348827, by rfl⟩ : syracuseStep 465103 = 697655) B697655
theorem B466023 : Blo 463784 466023 := bstep (se 1 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 466023 = 699035) B699035
theorem B695849 : Blo 463784 695849 := bstep (se 2 (by rfl) ⟨260943, by rfl⟩ : syracuseStep 695849 = 521887) B521887
theorem B466971 : Blo 463784 466971 := bstep (se 1 (by rfl) ⟨350228, by rfl⟩ : syracuseStep 466971 = 700457) B700457
theorem B1679611 : Blo 463784 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B696731 : Blo 463784 696731 := bstep (se 1 (by rfl) ⟨522548, by rfl⟩ : syracuseStep 696731 = 1045097) B1045097
theorem B699263 : Blo 463784 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B8465309 : Blo 463784 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B896159 : Blo 463784 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B2993435 : Blo 463784 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B5090921 : Blo 463784 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B700127 : Blo 463784 700127 := bstep (se 1 (by rfl) ⟨525095, by rfl⟩ : syracuseStep 700127 = 1050191) B1050191
theorem B3781565 : Blo 463784 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B1324001 : Blo 463784 1324001 := bstep (se 2 (by rfl) ⟨496500, by rfl⟩ : syracuseStep 1324001 = 993001) B993001
theorem B701471 : Blo 463784 701471 := bstep (se 1 (by rfl) ⟨526103, by rfl⟩ : syracuseStep 701471 = 1052207) B1052207
theorem B11941019 : Blo 463784 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B3523499 : Blo 463784 3523499 := bstep (se 1 (by rfl) ⟨2642624, by rfl⟩ : syracuseStep 3523499 = 5285249) B5285249
theorem B5031391 : Blo 463784 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B4245533 : Blo 463784 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B1493129 : Blo 463784 1493129 := bstep (se 2 (by rfl) ⟨559923, by rfl⟩ : syracuseStep 1493129 = 1119847) B1119847
theorem B1493243 : Blo 463784 1493243 := bstep (se 1 (by rfl) ⟨1119932, by rfl⟩ : syracuseStep 1493243 = 2239865) B2239865
theorem B4475695 : Blo 463784 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B5295455 : Blo 463784 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B45438205 : Blo 463784 45438205 := bstep (se 3 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 45438205 = 17039327) B17039327
theorem B11360735 : Blo 463784 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B4020791 : Blo 463784 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B8478145 : Blo 463784 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B2976749 : Blo 463784 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B98462749 : Blo 463784 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B1045943 : Blo 463784 1045943 := bstep (se 1 (by rfl) ⟨784457, by rfl⟩ : syracuseStep 1045943 = 1568915) B1568915
theorem B1177193 : Blo 463784 1177193 := bstep (se 2 (by rfl) ⟨441447, by rfl⟩ : syracuseStep 1177193 = 882895) B882895
theorem B1046735 : Blo 463784 1046735 := bstep (se 1 (by rfl) ⟨785051, by rfl⟩ : syracuseStep 1046735 = 1570103) B1570103
theorem B523327 : Blo 463784 523327 := bstep (se 1 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 523327 = 784991) B784991
theorem B5766551 : Blo 463784 5766551 := bstep (se 1 (by rfl) ⟨4324913, by rfl⟩ : syracuseStep 5766551 = 8649827) B8649827
theorem B10355795 : Blo 463784 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B3409735 : Blo 463784 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B5967593 : Blo 463784 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B7573823 : Blo 463784 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B1577825 : Blo 463784 1577825 := bstep (se 2 (by rfl) ⟨591684, by rfl⟩ : syracuseStep 1577825 = 1183369) B1183369
theorem B463899 : Blo 463784 463899 := bstep (se 1 (by rfl) ⟨347924, by rfl⟩ : syracuseStep 463899 = 695849) B695849
theorem B464487 : Blo 463784 464487 := bstep (se 1 (by rfl) ⟨348365, by rfl⟩ : syracuseStep 464487 = 696731) B696731
theorem B466175 : Blo 463784 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B5643539 : Blo 463784 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B597439 : Blo 463784 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B466751 : Blo 463784 466751 := bstep (se 1 (by rfl) ⟨350063, by rfl⟩ : syracuseStep 466751 = 700127) B700127
theorem B467647 : Blo 463784 467647 := bstep (se 1 (by rfl) ⟨350735, by rfl⟩ : syracuseStep 467647 = 701471) B701471
theorem B697295 : Blo 463784 697295 := bstep (se 1 (by rfl) ⟨522971, by rfl⟩ : syracuseStep 697295 = 1045943) B1045943
theorem B697769 : Blo 463784 697769 := bstep (se 2 (by rfl) ⟨261663, by rfl⟩ : syracuseStep 697769 = 523327) B523327
theorem B697823 : Blo 463784 697823 := bstep (se 1 (by rfl) ⟨523367, by rfl⟩ : syracuseStep 697823 = 1046735) B1046735
theorem B3844367 : Blo 463784 3844367 := bstep (se 1 (by rfl) ⟨2883275, by rfl⟩ : syracuseStep 3844367 = 5766551) B5766551
theorem B2239481 : Blo 463784 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B2830355 : Blo 463784 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B995419 : Blo 463784 995419 := bstep (se 1 (by rfl) ⟨746564, by rfl⟩ : syracuseStep 995419 = 1493129) B1493129
theorem B995495 : Blo 463784 995495 := bstep (se 1 (by rfl) ⟨746621, by rfl⟩ : syracuseStep 995495 = 1493243) B1493243
theorem B5681339 : Blo 463784 5681339 := bstep (se 1 (by rfl) ⟨4261004, by rfl⟩ : syracuseStep 5681339 = 8522009) B8522009
theorem B131283665 : Blo 463784 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B1984499 : Blo 463784 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B3393947 : Blo 463784 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B6706799 : Blo 463784 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B2348999 : Blo 463784 2348999 := bstep (se 1 (by rfl) ⟨1761749, by rfl⟩ : syracuseStep 2348999 = 3523499) B3523499
theorem B2643947 : Blo 463784 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B6708521 : Blo 463784 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B3530303 : Blo 463784 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B42888437 : Blo 463784 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B60584273 : Blo 463784 60584273 := bstep (se 2 (by rfl) ⟨22719102, by rfl⟩ : syracuseStep 60584273 = 45438205) B45438205
theorem B1995623 : Blo 463784 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B2521043 : Blo 463784 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B882667 : Blo 463784 882667 := bstep (se 1 (by rfl) ⟨662000, by rfl⟩ : syracuseStep 882667 = 1324001) B1324001
theorem B7960679 : Blo 463784 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B784795 : Blo 463784 784795 := bstep (se 1 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 784795 = 1177193) B1177193
theorem B11304193 : Blo 463784 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B2654653 : Blo 463784 2654653 := bstep (se 3 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 2654653 = 995495) B995495
theorem B5049215 : Blo 463784 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B1051883 : Blo 463784 1051883 := bstep (se 1 (by rfl) ⟨788912, by rfl⟩ : syracuseStep 1051883 = 1577825) B1577825
theorem B464863 : Blo 463784 464863 := bstep (se 1 (by rfl) ⟨348647, by rfl⟩ : syracuseStep 464863 = 697295) B697295
theorem B465179 : Blo 463784 465179 := bstep (se 1 (by rfl) ⟨348884, by rfl⟩ : syracuseStep 465179 = 697769) B697769
theorem B465215 : Blo 463784 465215 := bstep (se 1 (by rfl) ⟨348911, by rfl⟩ : syracuseStep 465215 = 697823) B697823
theorem B9050525 : Blo 463784 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B2562911 : Blo 463784 2562911 := bstep (se 1 (by rfl) ⟨1922183, by rfl⟩ : syracuseStep 2562911 = 3844367) B3844367
theorem B3186341 : Blo 463784 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B1680695 : Blo 463784 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B1322999 : Blo 463784 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B3978395 : Blo 463784 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B4471199 : Blo 463784 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B4472347 : Blo 463784 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B1327225 : Blo 463784 1327225 := bstep (se 2 (by rfl) ⟨497709, by rfl⟩ : syracuseStep 1327225 = 995419) B995419
theorem B1492987 : Blo 463784 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B28592291 : Blo 463784 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B1886903 : Blo 463784 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B3787559 : Blo 463784 3787559 := bstep (se 1 (by rfl) ⟨2840669, by rfl⟩ : syracuseStep 3787559 = 5681339) B5681339
theorem B40389515 : Blo 463784 40389515 := bstep (se 1 (by rfl) ⟨30292136, by rfl⟩ : syracuseStep 40389515 = 60584273) B60584273
theorem B1330415 : Blo 463784 1330415 := bstep (se 1 (by rfl) ⟨997811, by rfl⟩ : syracuseStep 1330415 = 1995623) B1995623
theorem B6903863 : Blo 463784 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B4546313 : Blo 463784 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B1565999 : Blo 463784 1565999 := bstep (se 1 (by rfl) ⟨1174499, by rfl⟩ : syracuseStep 1565999 = 2348999) B2348999
theorem B1762631 : Blo 463784 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B3762359 : Blo 463784 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B2353535 : Blo 463784 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B1176889 : Blo 463784 1176889 := bstep (se 2 (by rfl) ⟨441333, by rfl⟩ : syracuseStep 1176889 = 882667) B882667
theorem B1046393 : Blo 463784 1046393 := bstep (se 2 (by rfl) ⟨392397, by rfl⟩ : syracuseStep 1046393 = 784795) B784795
theorem B5307119 : Blo 463784 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B15072257 : Blo 463784 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B87522443 : Blo 463784 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B1769633 : Blo 463784 1769633 := bstep (se 2 (by rfl) ⟨663612, by rfl⟩ : syracuseStep 1769633 = 1327225) B1327225
theorem B3539537 : Blo 463784 3539537 := bstep (se 2 (by rfl) ⟨1327326, by rfl⟩ : syracuseStep 3539537 = 2654653) B2654653
theorem B2525039 : Blo 463784 2525039 := bstep (se 1 (by rfl) ⟨1893779, by rfl⟩ : syracuseStep 2525039 = 3787559) B3787559
theorem B886943 : Blo 463784 886943 := bstep (se 1 (by rfl) ⟨665207, by rfl⟩ : syracuseStep 886943 = 1330415) B1330415
theorem B6033683 : Blo 463784 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B1708607 : Blo 463784 1708607 := bstep (se 1 (by rfl) ⟨1281455, by rfl⟩ : syracuseStep 1708607 = 2562911) B2562911
theorem B1120463 : Blo 463784 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B697595 : Blo 463784 697595 := bstep (se 1 (by rfl) ⟨523196, by rfl⟩ : syracuseStep 697595 = 1046393) B1046393
theorem B1257935 : Blo 463784 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B701255 : Blo 463784 701255 := bstep (se 1 (by rfl) ⟨525941, by rfl⟩ : syracuseStep 701255 = 1051883) B1051883
theorem B4602575 : Blo 463784 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B3030875 : Blo 463784 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B2508239 : Blo 463784 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B10048171 : Blo 463784 10048171 := bstep (se 1 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 10048171 = 15072257) B15072257
theorem B58348295 : Blo 463784 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B19061527 : Blo 463784 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B3366143 : Blo 463784 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B26926343 : Blo 463784 26926343 := bstep (se 1 (by rfl) ⟨20194757, by rfl⟩ : syracuseStep 26926343 = 40389515) B40389515
theorem B1990649 : Blo 463784 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B2124227 : Blo 463784 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B1043999 : Blo 463784 1043999 := bstep (se 1 (by rfl) ⟨782999, by rfl⟩ : syracuseStep 1043999 = 1565999) B1565999
theorem B1175087 : Blo 463784 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B1569023 : Blo 463784 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B1569185 : Blo 463784 1569185 := bstep (se 2 (by rfl) ⟨588444, by rfl⟩ : syracuseStep 1569185 = 1176889) B1176889
theorem B881999 : Blo 463784 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B2652263 : Blo 463784 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B2980799 : Blo 463784 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B3538079 : Blo 463784 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B5963129 : Blo 463784 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B1179755 : Blo 463784 1179755 := bstep (se 1 (by rfl) ⟨884816, by rfl⟩ : syracuseStep 1179755 = 1769633) B1769633
theorem B2359691 : Blo 463784 2359691 := bstep (se 1 (by rfl) ⟨1769768, by rfl⟩ : syracuseStep 2359691 = 3539537) B3539537
theorem B1672159 : Blo 463784 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B591295 : Blo 463784 591295 := bstep (se 1 (by rfl) ⟨443471, by rfl⟩ : syracuseStep 591295 = 886943) B886943
theorem B38898863 : Blo 463784 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B465063 : Blo 463784 465063 := bstep (se 1 (by rfl) ⟨348797, by rfl⟩ : syracuseStep 465063 = 697595) B697595
theorem B1416151 : Blo 463784 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B695999 : Blo 463784 695999 := bstep (se 1 (by rfl) ⟨521999, by rfl⟩ : syracuseStep 695999 = 1043999) B1043999
theorem B467503 : Blo 463784 467503 := bstep (se 1 (by rfl) ⟨350627, by rfl⟩ : syracuseStep 467503 = 701255) B701255
theorem B3975419 : Blo 463784 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B3354493 : Blo 463784 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B1683359 : Blo 463784 1683359 := bstep (se 1 (by rfl) ⟨1262519, by rfl⟩ : syracuseStep 1683359 = 2525039) B2525039
theorem B2244095 : Blo 463784 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B1327099 : Blo 463784 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B25415369 : Blo 463784 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B3068383 : Blo 463784 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B1987199 : Blo 463784 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B2020583 : Blo 463784 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B4022455 : Blo 463784 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B1139071 : Blo 463784 1139071 := bstep (se 1 (by rfl) ⟨854303, by rfl⟩ : syracuseStep 1139071 = 1708607) B1708607
theorem B746975 : Blo 463784 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B17950895 : Blo 463784 17950895 := bstep (se 1 (by rfl) ⟨13463171, by rfl⟩ : syracuseStep 17950895 = 26926343) B26926343
theorem B13397561 : Blo 463784 13397561 := bstep (se 2 (by rfl) ⟨5024085, by rfl⟩ : syracuseStep 13397561 = 10048171) B10048171
theorem B783391 : Blo 463784 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B1046015 : Blo 463784 1046015 := bstep (se 1 (by rfl) ⟨784511, by rfl⟩ : syracuseStep 1046015 = 1569023) B1569023
theorem B1046123 : Blo 463784 1046123 := bstep (se 1 (by rfl) ⟨784592, by rfl⟩ : syracuseStep 1046123 = 1569185) B1569185
theorem B587999 : Blo 463784 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B1768175 : Blo 463784 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B2358719 : Blo 463784 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B786503 : Blo 463784 786503 := bstep (se 1 (by rfl) ⟨589877, by rfl⟩ : syracuseStep 786503 = 1179755) B1179755
theorem B1573127 : Blo 463784 1573127 := bstep (se 1 (by rfl) ⟨1179845, by rfl⟩ : syracuseStep 1573127 = 2359691) B2359691
theorem B2229545 : Blo 463784 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B788393 : Blo 463784 788393 := bstep (se 2 (by rfl) ⟨295647, by rfl⟩ : syracuseStep 788393 = 591295) B591295
theorem B16943579 : Blo 463784 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B463999 : Blo 463784 463999 := bstep (se 1 (by rfl) ⟨347999, by rfl⟩ : syracuseStep 463999 = 695999) B695999
theorem B497983 : Blo 463784 497983 := bstep (se 1 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 497983 = 746975) B746975
theorem B11967263 : Blo 463784 11967263 := bstep (se 1 (by rfl) ⟨8975447, by rfl⟩ : syracuseStep 11967263 = 17950895) B17950895
theorem B1122239 : Blo 463784 1122239 := bstep (se 1 (by rfl) ⟨841679, by rfl⟩ : syracuseStep 1122239 = 1683359) B1683359
theorem B697343 : Blo 463784 697343 := bstep (se 1 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 697343 = 1046015) B1046015
theorem B697415 : Blo 463784 697415 := bstep (se 1 (by rfl) ⟨523061, by rfl⟩ : syracuseStep 697415 = 1046123) B1046123
theorem B1518761 : Blo 463784 1518761 := bstep (se 2 (by rfl) ⟨569535, by rfl⟩ : syracuseStep 1518761 = 1139071) B1139071
theorem B25932575 : Blo 463784 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B1324799 : Blo 463784 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B5388221 : Blo 463784 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B4472657 : Blo 463784 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B8931707 : Blo 463784 8931707 := bstep (se 1 (by rfl) ⟨6698780, by rfl⟩ : syracuseStep 8931707 = 13397561) B13397561
theorem B1888201 : Blo 463784 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1496063 : Blo 463784 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B5363273 : Blo 463784 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B1567997 : Blo 463784 1567997 := bstep (se 3 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 1567997 = 587999) B587999
theorem B4091177 : Blo 463784 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B1044521 : Blo 463784 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B2650279 : Blo 463784 2650279 := bstep (se 1 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 2650279 = 3975419) B3975419
theorem B1178783 : Blo 463784 1178783 := bstep (se 1 (by rfl) ⟨884087, by rfl⟩ : syracuseStep 1178783 = 1768175) B1768175
theorem B1572479 : Blo 463784 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B1769465 : Blo 463784 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B524335 : Blo 463784 524335 := bstep (se 1 (by rfl) ⟨393251, by rfl⟩ : syracuseStep 524335 = 786503) B786503
theorem B1048751 : Blo 463784 1048751 := bstep (se 1 (by rfl) ⟨786563, by rfl⟩ : syracuseStep 1048751 = 1573127) B1573127
theorem B525595 : Blo 463784 525595 := bstep (se 1 (by rfl) ⟨394196, by rfl⟩ : syracuseStep 525595 = 788393) B788393
theorem B3575515 : Blo 463784 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B464895 : Blo 463784 464895 := bstep (se 1 (by rfl) ⟨348671, by rfl⟩ : syracuseStep 464895 = 697343) B697343
theorem B464943 : Blo 463784 464943 := bstep (se 1 (by rfl) ⟨348707, by rfl⟩ : syracuseStep 464943 = 697415) B697415
theorem B2727451 : Blo 463784 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B696347 : Blo 463784 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B663977 : Blo 463784 663977 := bstep (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) B497983
theorem B1486363 : Blo 463784 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B69153533 : Blo 463784 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B997375 : Blo 463784 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B7978175 : Blo 463784 7978175 := bstep (se 1 (by rfl) ⟨5983631, by rfl⟩ : syracuseStep 7978175 = 11967263) B11967263
theorem B14368589 : Blo 463784 14368589 := bstep (se 3 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 14368589 = 5388221) B5388221
theorem B5954471 : Blo 463784 5954471 := bstep (se 1 (by rfl) ⟨4465853, by rfl⟩ : syracuseStep 5954471 = 8931707) B8931707
theorem B11295719 : Blo 463784 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B2517601 : Blo 463784 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B748159 : Blo 463784 748159 := bstep (se 1 (by rfl) ⟨561119, by rfl⟩ : syracuseStep 748159 = 1122239) B1122239
theorem B3533705 : Blo 463784 3533705 := bstep (se 2 (by rfl) ⟨1325139, by rfl⟩ : syracuseStep 3533705 = 2650279) B2650279
theorem B1012507 : Blo 463784 1012507 := bstep (se 1 (by rfl) ⟨759380, by rfl⟩ : syracuseStep 1012507 = 1518761) B1518761
theorem B1045331 : Blo 463784 1045331 := bstep (se 1 (by rfl) ⟨783998, by rfl⟩ : syracuseStep 1045331 = 1567997) B1567997
theorem B883199 : Blo 463784 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B785855 : Blo 463784 785855 := bstep (se 1 (by rfl) ⟨589391, by rfl⟩ : syracuseStep 785855 = 1178783) B1178783
theorem B1048319 : Blo 463784 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B2981771 : Blo 463784 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B1179643 : Blo 463784 1179643 := bstep (se 1 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 1179643 = 1769465) B1769465
theorem B1770605 : Blo 463784 1770605 := bstep (se 3 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 1770605 = 663977) B663977
theorem B3969647 : Blo 463784 3969647 := bstep (se 1 (by rfl) ⟨2977235, by rfl⟩ : syracuseStep 3969647 = 5954471) B5954471
theorem B464231 : Blo 463784 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B696887 : Blo 463784 696887 := bstep (se 1 (by rfl) ⟨522665, by rfl⟩ : syracuseStep 696887 = 1045331) B1045331
theorem B5318783 : Blo 463784 5318783 := bstep (se 1 (by rfl) ⟨3989087, by rfl⟩ : syracuseStep 5318783 = 7978175) B7978175
theorem B698879 : Blo 463784 698879 := bstep (se 1 (by rfl) ⟨524159, by rfl⟩ : syracuseStep 698879 = 1048319) B1048319
theorem B9579059 : Blo 463784 9579059 := bstep (se 1 (by rfl) ⟨7184294, by rfl⟩ : syracuseStep 9579059 = 14368589) B14368589
theorem B699113 : Blo 463784 699113 := bstep (se 2 (by rfl) ⟨262167, by rfl⟩ : syracuseStep 699113 = 524335) B524335
theorem B699167 : Blo 463784 699167 := bstep (se 1 (by rfl) ⟨524375, by rfl⟩ : syracuseStep 699167 = 1048751) B1048751
theorem B700793 : Blo 463784 700793 := bstep (se 2 (by rfl) ⟨262797, by rfl⟩ : syracuseStep 700793 = 525595) B525595
theorem B3356801 : Blo 463784 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B1981817 : Blo 463784 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B4767353 : Blo 463784 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B1572857 : Blo 463784 1572857 := bstep (se 2 (by rfl) ⟨589821, by rfl⟩ : syracuseStep 1572857 = 1179643) B1179643
theorem B1329833 : Blo 463784 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B1987847 : Blo 463784 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B3990181 : Blo 463784 3990181 := bstep (se 4 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 3990181 = 748159) B748159
theorem B5400037 : Blo 463784 5400037 := bstep (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) B1012507
theorem B7530479 : Blo 463784 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B2355803 : Blo 463784 2355803 := bstep (se 1 (by rfl) ⟨1766852, by rfl⟩ : syracuseStep 2355803 = 3533705) B3533705
theorem B14546405 : Blo 463784 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B46102355 : Blo 463784 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B588799 : Blo 463784 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B523903 : Blo 463784 523903 := bstep (se 1 (by rfl) ⟨392927, by rfl⟩ : syracuseStep 523903 = 785855) B785855
theorem B1180403 : Blo 463784 1180403 := bstep (se 1 (by rfl) ⟨885302, by rfl⟩ : syracuseStep 1180403 = 1770605) B1770605
theorem B886555 : Blo 463784 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B464591 : Blo 463784 464591 := bstep (se 1 (by rfl) ⟨348443, by rfl⟩ : syracuseStep 464591 = 696887) B696887
theorem B5020319 : Blo 463784 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B3545855 : Blo 463784 3545855 := bstep (se 1 (by rfl) ⟨2659391, by rfl⟩ : syracuseStep 3545855 = 5318783) B5318783
theorem B465919 : Blo 463784 465919 := bstep (se 1 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 465919 = 698879) B698879
theorem B466075 : Blo 463784 466075 := bstep (se 1 (by rfl) ⟨349556, by rfl⟩ : syracuseStep 466075 = 699113) B699113
theorem B466111 : Blo 463784 466111 := bstep (se 1 (by rfl) ⟨349583, by rfl⟩ : syracuseStep 466111 = 699167) B699167
theorem B467195 : Blo 463784 467195 := bstep (se 1 (by rfl) ⟨350396, by rfl⟩ : syracuseStep 467195 = 700793) B700793
theorem B2237867 : Blo 463784 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B698537 : Blo 463784 698537 := bstep (se 2 (by rfl) ⟨261951, by rfl⟩ : syracuseStep 698537 = 523903) B523903
theorem B1321211 : Blo 463784 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B5320241 : Blo 463784 5320241 := bstep (se 2 (by rfl) ⟨1995090, by rfl⟩ : syracuseStep 5320241 = 3990181) B3990181
theorem B1325231 : Blo 463784 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B7200049 : Blo 463784 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B2646431 : Blo 463784 2646431 := bstep (se 1 (by rfl) ⟨1984823, by rfl⟩ : syracuseStep 2646431 = 3969647) B3969647
theorem B6386039 : Blo 463784 6386039 := bstep (se 1 (by rfl) ⟨4789529, by rfl⟩ : syracuseStep 6386039 = 9579059) B9579059
theorem B1570535 : Blo 463784 1570535 := bstep (se 1 (by rfl) ⟨1177901, by rfl⟩ : syracuseStep 1570535 = 2355803) B2355803
theorem B9697603 : Blo 463784 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B30734903 : Blo 463784 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B785065 : Blo 463784 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B3178235 : Blo 463784 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B1048571 : Blo 463784 1048571 := bstep (se 1 (by rfl) ⟨786428, by rfl⟩ : syracuseStep 1048571 = 1572857) B1572857
theorem B786935 : Blo 463784 786935 := bstep (se 1 (by rfl) ⟨590201, by rfl⟩ : syracuseStep 786935 = 1180403) B1180403
theorem B1182073 : Blo 463784 1182073 := bstep (se 2 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 1182073 = 886555) B886555
theorem B2363903 : Blo 463784 2363903 := bstep (se 1 (by rfl) ⟨1772927, by rfl⟩ : syracuseStep 2363903 = 3545855) B3545855
theorem B465691 : Blo 463784 465691 := bstep (se 1 (by rfl) ⟨349268, by rfl⟩ : syracuseStep 465691 = 698537) B698537
theorem B3546827 : Blo 463784 3546827 := bstep (se 1 (by rfl) ⟨2660120, by rfl⟩ : syracuseStep 3546827 = 5320241) B5320241
theorem B20489935 : Blo 463784 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B699047 : Blo 463784 699047 := bstep (se 1 (by rfl) ⟨524285, by rfl⟩ : syracuseStep 699047 = 1048571) B1048571
theorem B1491911 : Blo 463784 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B13387517 : Blo 463784 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B12930137 : Blo 463784 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B8475293 : Blo 463784 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B1764287 : Blo 463784 1764287 := bstep (se 1 (by rfl) ⟨1323215, by rfl⟩ : syracuseStep 1764287 = 2646431) B2646431
theorem B880807 : Blo 463784 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B4257359 : Blo 463784 4257359 := bstep (se 1 (by rfl) ⟨3193019, by rfl⟩ : syracuseStep 4257359 = 6386039) B6386039
theorem B1046753 : Blo 463784 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B1047023 : Blo 463784 1047023 := bstep (se 1 (by rfl) ⟨785267, by rfl⟩ : syracuseStep 1047023 = 1570535) B1570535
theorem B883487 : Blo 463784 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B9600065 : Blo 463784 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B524623 : Blo 463784 524623 := bstep (se 1 (by rfl) ⟨393467, by rfl⟩ : syracuseStep 524623 = 786935) B786935
theorem B8620091 : Blo 463784 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B1575935 : Blo 463784 1575935 := bstep (se 1 (by rfl) ⟨1181951, by rfl⟩ : syracuseStep 1575935 = 2363903) B2363903
theorem B1576097 : Blo 463784 1576097 := bstep (se 2 (by rfl) ⟨591036, by rfl⟩ : syracuseStep 1576097 = 1182073) B1182073
theorem B2364551 : Blo 463784 2364551 := bstep (se 1 (by rfl) ⟨1773413, by rfl⟩ : syracuseStep 2364551 = 3546827) B3546827
theorem B466031 : Blo 463784 466031 := bstep (se 1 (by rfl) ⟨349523, by rfl⟩ : syracuseStep 466031 = 699047) B699047
theorem B697835 : Blo 463784 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B698015 : Blo 463784 698015 := bstep (se 1 (by rfl) ⟨523511, by rfl⟩ : syracuseStep 698015 = 1047023) B1047023
theorem B6400043 : Blo 463784 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B994607 : Blo 463784 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B8925011 : Blo 463784 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B5650195 : Blo 463784 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B2838239 : Blo 463784 2838239 := bstep (se 1 (by rfl) ⟨2128679, by rfl⟩ : syracuseStep 2838239 = 4257359) B4257359
theorem B27319913 : Blo 463784 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B1174409 : Blo 463784 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B1176191 : Blo 463784 1176191 := bstep (se 1 (by rfl) ⟨882143, by rfl⟩ : syracuseStep 1176191 = 1764287) B1764287
theorem B2355965 : Blo 463784 2355965 := bstep (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) B883487
theorem B1050623 : Blo 463784 1050623 := bstep (se 1 (by rfl) ⟨787967, by rfl⟩ : syracuseStep 1050623 = 1575935) B1575935
theorem B1050731 : Blo 463784 1050731 := bstep (se 1 (by rfl) ⟨788048, by rfl⟩ : syracuseStep 1050731 = 1576097) B1576097
theorem B1576367 : Blo 463784 1576367 := bstep (se 1 (by rfl) ⟨1182275, by rfl⟩ : syracuseStep 1576367 = 2364551) B2364551
theorem B465223 : Blo 463784 465223 := bstep (se 1 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 465223 = 697835) B697835
theorem B465343 : Blo 463784 465343 := bstep (se 1 (by rfl) ⟨349007, by rfl⟩ : syracuseStep 465343 = 698015) B698015
theorem B4266695 : Blo 463784 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B663071 : Blo 463784 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B699497 : Blo 463784 699497 := bstep (se 2 (by rfl) ⟨262311, by rfl⟩ : syracuseStep 699497 = 524623) B524623
theorem B5746727 : Blo 463784 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B5950007 : Blo 463784 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B1892159 : Blo 463784 1892159 := bstep (se 1 (by rfl) ⟨1419119, by rfl⟩ : syracuseStep 1892159 = 2838239) B2838239
theorem B18213275 : Blo 463784 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B782939 : Blo 463784 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B7533593 : Blo 463784 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B784127 : Blo 463784 784127 := bstep (se 1 (by rfl) ⟨588095, by rfl⟩ : syracuseStep 784127 = 1176191) B1176191
theorem B1570643 : Blo 463784 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B3966671 : Blo 463784 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B1050911 : Blo 463784 1050911 := bstep (se 1 (by rfl) ⟨788183, by rfl⟩ : syracuseStep 1050911 = 1576367) B1576367
theorem B11377853 : Blo 463784 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B466331 : Blo 463784 466331 := bstep (se 1 (by rfl) ⟨349748, by rfl⟩ : syracuseStep 466331 = 699497) B699497
theorem B5022395 : Blo 463784 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B700415 : Blo 463784 700415 := bstep (se 1 (by rfl) ⟨525311, by rfl⟩ : syracuseStep 700415 = 1050623) B1050623
theorem B700487 : Blo 463784 700487 := bstep (se 1 (by rfl) ⟨525365, by rfl⟩ : syracuseStep 700487 = 1050731) B1050731
theorem B1261439 : Blo 463784 1261439 := bstep (se 1 (by rfl) ⟨946079, by rfl⟩ : syracuseStep 1261439 = 1892159) B1892159
theorem B12142183 : Blo 463784 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B3831151 : Blo 463784 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B521959 : Blo 463784 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B522751 : Blo 463784 522751 := bstep (se 1 (by rfl) ⟨392063, by rfl⟩ : syracuseStep 522751 = 784127) B784127
theorem B1047095 : Blo 463784 1047095 := bstep (se 1 (by rfl) ⟨785321, by rfl⟩ : syracuseStep 1047095 = 1570643) B1570643
theorem B1768189 : Blo 463784 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B16189577 : Blo 463784 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B3348263 : Blo 463784 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B695945 : Blo 463784 695945 := bstep (se 2 (by rfl) ⟨260979, by rfl⟩ : syracuseStep 695945 = 521959) B521959
theorem B466943 : Blo 463784 466943 := bstep (se 1 (by rfl) ⟨350207, by rfl⟩ : syracuseStep 466943 = 700415) B700415
theorem B466991 : Blo 463784 466991 := bstep (se 1 (by rfl) ⟨350243, by rfl⟩ : syracuseStep 466991 = 700487) B700487
theorem B697001 : Blo 463784 697001 := bstep (se 2 (by rfl) ⟨261375, by rfl⟩ : syracuseStep 697001 = 522751) B522751
theorem B698063 : Blo 463784 698063 := bstep (se 1 (by rfl) ⟨523547, by rfl⟩ : syracuseStep 698063 = 1047095) B1047095
theorem B700607 : Blo 463784 700607 := bstep (se 1 (by rfl) ⟨525455, by rfl⟩ : syracuseStep 700607 = 1050911) B1050911
theorem B7585235 : Blo 463784 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B840959 : Blo 463784 840959 := bstep (se 1 (by rfl) ⟨630719, by rfl⟩ : syracuseStep 840959 = 1261439) B1261439
theorem B2644447 : Blo 463784 2644447 := bstep (se 1 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 2644447 = 3966671) B3966671
theorem B5108201 : Blo 463784 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B2357585 : Blo 463784 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B560639 : Blo 463784 560639 := bstep (se 1 (by rfl) ⟨420479, by rfl⟩ : syracuseStep 560639 = 840959) B840959
theorem B463963 : Blo 463784 463963 := bstep (se 1 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 463963 = 695945) B695945
theorem B464667 : Blo 463784 464667 := bstep (se 1 (by rfl) ⟨348500, by rfl⟩ : syracuseStep 464667 = 697001) B697001
theorem B465375 : Blo 463784 465375 := bstep (se 1 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 465375 = 698063) B698063
theorem B467071 : Blo 463784 467071 := bstep (se 1 (by rfl) ⟨350303, by rfl⟩ : syracuseStep 467071 = 700607) B700607
theorem B5056823 : Blo 463784 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B10793051 : Blo 463784 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B8928701 : Blo 463784 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B3525929 : Blo 463784 3525929 := bstep (se 2 (by rfl) ⟨1322223, by rfl⟩ : syracuseStep 3525929 = 2644447) B2644447
theorem B3405467 : Blo 463784 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B1571723 : Blo 463784 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B2270311 : Blo 463784 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B7195367 : Blo 463784 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B1495037 : Blo 463784 1495037 := bstep (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) B560639
theorem B5952467 : Blo 463784 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B2350619 : Blo 463784 2350619 := bstep (se 1 (by rfl) ⟨1762964, by rfl⟩ : syracuseStep 2350619 = 3525929) B3525929
theorem B3371215 : Blo 463784 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B1047815 : Blo 463784 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B3968311 : Blo 463784 3968311 := bstep (se 1 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 3968311 = 5952467) B5952467
theorem B4494953 : Blo 463784 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B698543 : Blo 463784 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B4796911 : Blo 463784 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B12108325 : Blo 463784 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B3986765 : Blo 463784 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B1567079 : Blo 463784 1567079 := bstep (se 1 (by rfl) ⟨1175309, by rfl⟩ : syracuseStep 1567079 = 2350619) B2350619
theorem B2657843 : Blo 463784 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B465695 : Blo 463784 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B2996635 : Blo 463784 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B5291081 : Blo 463784 5291081 := bstep (se 2 (by rfl) ⟨1984155, by rfl⟩ : syracuseStep 5291081 = 3968311) B3968311
theorem B16144433 : Blo 463784 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B25583525 : Blo 463784 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B1044719 : Blo 463784 1044719 := bstep (se 1 (by rfl) ⟨783539, by rfl⟩ : syracuseStep 1044719 = 1567079) B1567079
theorem B1771895 : Blo 463784 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B696479 : Blo 463784 696479 := bstep (se 1 (by rfl) ⟨522359, by rfl⟩ : syracuseStep 696479 = 1044719) B1044719
theorem B10762955 : Blo 463784 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B17055683 : Blo 463784 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B3527387 : Blo 463784 3527387 := bstep (se 1 (by rfl) ⟨2645540, by rfl⟩ : syracuseStep 3527387 = 5291081) B5291081
theorem B3995513 : Blo 463784 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B1181263 : Blo 463784 1181263 := bstep (se 1 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 1181263 = 1771895) B1771895
theorem B464319 : Blo 463784 464319 := bstep (se 1 (by rfl) ⟨348239, by rfl⟩ : syracuseStep 464319 = 696479) B696479
theorem B2663675 : Blo 463784 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B2351591 : Blo 463784 2351591 := bstep (se 1 (by rfl) ⟨1763693, by rfl⟩ : syracuseStep 2351591 = 3527387) B3527387
theorem B7175303 : Blo 463784 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B11370455 : Blo 463784 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B1575017 : Blo 463784 1575017 := bstep (se 2 (by rfl) ⟨590631, by rfl⟩ : syracuseStep 1575017 = 1181263) B1181263
theorem B1775783 : Blo 463784 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B7580303 : Blo 463784 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B1567727 : Blo 463784 1567727 := bstep (se 1 (by rfl) ⟨1175795, by rfl⟩ : syracuseStep 1567727 = 2351591) B2351591
theorem B4783535 : Blo 463784 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B1050011 : Blo 463784 1050011 := bstep (se 1 (by rfl) ⟨787508, by rfl⟩ : syracuseStep 1050011 = 1575017) B1575017
theorem B1183855 : Blo 463784 1183855 := bstep (se 1 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 1183855 = 1775783) B1775783
theorem B5053535 : Blo 463784 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B3189023 : Blo 463784 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B1045151 : Blo 463784 1045151 := bstep (se 1 (by rfl) ⟨783863, by rfl⟩ : syracuseStep 1045151 = 1567727) B1567727
theorem B1578473 : Blo 463784 1578473 := bstep (se 2 (by rfl) ⟨591927, by rfl⟩ : syracuseStep 1578473 = 1183855) B1183855
theorem B696767 : Blo 463784 696767 := bstep (se 1 (by rfl) ⟨522575, by rfl⟩ : syracuseStep 696767 = 1045151) B1045151
theorem B700007 : Blo 463784 700007 := bstep (se 1 (by rfl) ⟨525005, by rfl⟩ : syracuseStep 700007 = 1050011) B1050011
theorem B3369023 : Blo 463784 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B2126015 : Blo 463784 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B1052315 : Blo 463784 1052315 := bstep (se 1 (by rfl) ⟨789236, by rfl⟩ : syracuseStep 1052315 = 1578473) B1578473
theorem B464511 : Blo 463784 464511 := bstep (se 1 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 464511 = 696767) B696767
theorem B466671 : Blo 463784 466671 := bstep (se 1 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 466671 = 700007) B700007
theorem B1417343 : Blo 463784 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B2246015 : Blo 463784 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B3779581 : Blo 463784 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B701543 : Blo 463784 701543 := bstep (se 1 (by rfl) ⟨526157, by rfl⟩ : syracuseStep 701543 = 1052315) B1052315
theorem B5989373 : Blo 463784 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B467695 : Blo 463784 467695 := bstep (se 1 (by rfl) ⟨350771, by rfl⟩ : syracuseStep 467695 = 701543) B701543
theorem B5039441 : Blo 463784 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B3992915 : Blo 463784 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B2661943 : Blo 463784 2661943 := bstep (se 1 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 2661943 = 3992915) B3992915
theorem B3359627 : Blo 463784 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B3549257 : Blo 463784 3549257 := bstep (se 2 (by rfl) ⟨1330971, by rfl⟩ : syracuseStep 3549257 = 2661943) B2661943
theorem B2239751 : Blo 463784 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B2366171 : Blo 463784 2366171 := bstep (se 1 (by rfl) ⟨1774628, by rfl⟩ : syracuseStep 2366171 = 3549257) B3549257
theorem B1493167 : Blo 463784 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1577447 : Blo 463784 1577447 := bstep (se 1 (by rfl) ⟨1183085, by rfl⟩ : syracuseStep 1577447 = 2366171) B2366171
theorem B1990889 : Blo 463784 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B1051631 : Blo 463784 1051631 := bstep (se 1 (by rfl) ⟨788723, by rfl⟩ : syracuseStep 1051631 = 1577447) B1577447
theorem B1327259 : Blo 463784 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B884839 : Blo 463784 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B701087 : Blo 463784 701087 := bstep (se 1 (by rfl) ⟨525815, by rfl⟩ : syracuseStep 701087 = 1051631) B1051631
theorem B1179785 : Blo 463784 1179785 := bstep (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) B884839
theorem B467391 : Blo 463784 467391 := bstep (se 1 (by rfl) ⟨350543, by rfl⟩ : syracuseStep 467391 = 701087) B701087
theorem B786523 : Blo 463784 786523 := bstep (se 1 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 786523 = 1179785) B1179785
theorem B1048697 : Blo 463784 1048697 := bstep (se 2 (by rfl) ⟨393261, by rfl⟩ : syracuseStep 1048697 = 786523) B786523
theorem B699131 : Blo 463784 699131 := bstep (se 1 (by rfl) ⟨524348, by rfl⟩ : syracuseStep 699131 = 1048697) B1048697
theorem B466087 : Blo 463784 466087 := bstep (se 1 (by rfl) ⟨349565, by rfl⟩ : syracuseStep 466087 = 699131) B699131

theorem C0 (j : ℕ) (h1 : 115946 ≤ j) (h2 : j ≤ 116645) : Blo 463784 (4 * j + 3) := by
  interval_cases j
  · exact B463787
  · exact B463791
  · exact B463795
  · exact B463799
  · exact B463803
  · exact B463807
  · exact B463811
  · exact B463815
  · exact B463819
  · exact B463823
  · exact B463827
  · exact B463831
  · exact B463835
  · exact B463839
  · exact B463843
  · exact B463847
  · exact B463851
  · exact B463855
  · exact B463859
  · exact B463863
  · exact B463867
  · exact B463871
  · exact B463875
  · exact B463879
  · exact B463883
  · exact B463887
  · exact B463891
  · exact B463895
  · exact B463899
  · exact B463903
  · exact B463907
  · exact B463911
  · exact B463915
  · exact B463919
  · exact B463923
  · exact B463927
  · exact B463931
  · exact B463935
  · exact B463939
  · exact B463943
  · exact B463947
  · exact B463951
  · exact B463955
  · exact B463959
  · exact B463963
  · exact B463967
  · exact B463971
  · exact B463975
  · exact B463979
  · exact B463983
  · exact B463987
  · exact B463991
  · exact B463995
  · exact B463999
  · exact B464003
  · exact B464007
  · exact B464011
  · exact B464015
  · exact B464019
  · exact B464023
  · exact B464027
  · exact B464031
  · exact B464035
  · exact B464039
  · exact B464043
  · exact B464047
  · exact B464051
  · exact B464055
  · exact B464059
  · exact B464063
  · exact B464067
  · exact B464071
  · exact B464075
  · exact B464079
  · exact B464083
  · exact B464087
  · exact B464091
  · exact B464095
  · exact B464099
  · exact B464103
  · exact B464107
  · exact B464111
  · exact B464115
  · exact B464119
  · exact B464123
  · exact B464127
  · exact B464131
  · exact B464135
  · exact B464139
  · exact B464143
  · exact B464147
  · exact B464151
  · exact B464155
  · exact B464159
  · exact B464163
  · exact B464167
  · exact B464171
  · exact B464175
  · exact B464179
  · exact B464183
  · exact B464187
  · exact B464191
  · exact B464195
  · exact B464199
  · exact B464203
  · exact B464207
  · exact B464211
  · exact B464215
  · exact B464219
  · exact B464223
  · exact B464227
  · exact B464231
  · exact B464235
  · exact B464239
  · exact B464243
  · exact B464247
  · exact B464251
  · exact B464255
  · exact B464259
  · exact B464263
  · exact B464267
  · exact B464271
  · exact B464275
  · exact B464279
  · exact B464283
  · exact B464287
  · exact B464291
  · exact B464295
  · exact B464299
  · exact B464303
  · exact B464307
  · exact B464311
  · exact B464315
  · exact B464319
  · exact B464323
  · exact B464327
  · exact B464331
  · exact B464335
  · exact B464339
  · exact B464343
  · exact B464347
  · exact B464351
  · exact B464355
  · exact B464359
  · exact B464363
  · exact B464367
  · exact B464371
  · exact B464375
  · exact B464379
  · exact B464383
  · exact B464387
  · exact B464391
  · exact B464395
  · exact B464399
  · exact B464403
  · exact B464407
  · exact B464411
  · exact B464415
  · exact B464419
  · exact B464423
  · exact B464427
  · exact B464431
  · exact B464435
  · exact B464439
  · exact B464443
  · exact B464447
  · exact B464451
  · exact B464455
  · exact B464459
  · exact B464463
  · exact B464467
  · exact B464471
  · exact B464475
  · exact B464479
  · exact B464483
  · exact B464487
  · exact B464491
  · exact B464495
  · exact B464499
  · exact B464503
  · exact B464507
  · exact B464511
  · exact B464515
  · exact B464519
  · exact B464523
  · exact B464527
  · exact B464531
  · exact B464535
  · exact B464539
  · exact B464543
  · exact B464547
  · exact B464551
  · exact B464555
  · exact B464559
  · exact B464563
  · exact B464567
  · exact B464571
  · exact B464575
  · exact B464579
  · exact B464583
  · exact B464587
  · exact B464591
  · exact B464595
  · exact B464599
  · exact B464603
  · exact B464607
  · exact B464611
  · exact B464615
  · exact B464619
  · exact B464623
  · exact B464627
  · exact B464631
  · exact B464635
  · exact B464639
  · exact B464643
  · exact B464647
  · exact B464651
  · exact B464655
  · exact B464659
  · exact B464663
  · exact B464667
  · exact B464671
  · exact B464675
  · exact B464679
  · exact B464683
  · exact B464687
  · exact B464691
  · exact B464695
  · exact B464699
  · exact B464703
  · exact B464707
  · exact B464711
  · exact B464715
  · exact B464719
  · exact B464723
  · exact B464727
  · exact B464731
  · exact B464735
  · exact B464739
  · exact B464743
  · exact B464747
  · exact B464751
  · exact B464755
  · exact B464759
  · exact B464763
  · exact B464767
  · exact B464771
  · exact B464775
  · exact B464779
  · exact B464783
  · exact B464787
  · exact B464791
  · exact B464795
  · exact B464799
  · exact B464803
  · exact B464807
  · exact B464811
  · exact B464815
  · exact B464819
  · exact B464823
  · exact B464827
  · exact B464831
  · exact B464835
  · exact B464839
  · exact B464843
  · exact B464847
  · exact B464851
  · exact B464855
  · exact B464859
  · exact B464863
  · exact B464867
  · exact B464871
  · exact B464875
  · exact B464879
  · exact B464883
  · exact B464887
  · exact B464891
  · exact B464895
  · exact B464899
  · exact B464903
  · exact B464907
  · exact B464911
  · exact B464915
  · exact B464919
  · exact B464923
  · exact B464927
  · exact B464931
  · exact B464935
  · exact B464939
  · exact B464943
  · exact B464947
  · exact B464951
  · exact B464955
  · exact B464959
  · exact B464963
  · exact B464967
  · exact B464971
  · exact B464975
  · exact B464979
  · exact B464983
  · exact B464987
  · exact B464991
  · exact B464995
  · exact B464999
  · exact B465003
  · exact B465007
  · exact B465011
  · exact B465015
  · exact B465019
  · exact B465023
  · exact B465027
  · exact B465031
  · exact B465035
  · exact B465039
  · exact B465043
  · exact B465047
  · exact B465051
  · exact B465055
  · exact B465059
  · exact B465063
  · exact B465067
  · exact B465071
  · exact B465075
  · exact B465079
  · exact B465083
  · exact B465087
  · exact B465091
  · exact B465095
  · exact B465099
  · exact B465103
  · exact B465107
  · exact B465111
  · exact B465115
  · exact B465119
  · exact B465123
  · exact B465127
  · exact B465131
  · exact B465135
  · exact B465139
  · exact B465143
  · exact B465147
  · exact B465151
  · exact B465155
  · exact B465159
  · exact B465163
  · exact B465167
  · exact B465171
  · exact B465175
  · exact B465179
  · exact B465183
  · exact B465187
  · exact B465191
  · exact B465195
  · exact B465199
  · exact B465203
  · exact B465207
  · exact B465211
  · exact B465215
  · exact B465219
  · exact B465223
  · exact B465227
  · exact B465231
  · exact B465235
  · exact B465239
  · exact B465243
  · exact B465247
  · exact B465251
  · exact B465255
  · exact B465259
  · exact B465263
  · exact B465267
  · exact B465271
  · exact B465275
  · exact B465279
  · exact B465283
  · exact B465287
  · exact B465291
  · exact B465295
  · exact B465299
  · exact B465303
  · exact B465307
  · exact B465311
  · exact B465315
  · exact B465319
  · exact B465323
  · exact B465327
  · exact B465331
  · exact B465335
  · exact B465339
  · exact B465343
  · exact B465347
  · exact B465351
  · exact B465355
  · exact B465359
  · exact B465363
  · exact B465367
  · exact B465371
  · exact B465375
  · exact B465379
  · exact B465383
  · exact B465387
  · exact B465391
  · exact B465395
  · exact B465399
  · exact B465403
  · exact B465407
  · exact B465411
  · exact B465415
  · exact B465419
  · exact B465423
  · exact B465427
  · exact B465431
  · exact B465435
  · exact B465439
  · exact B465443
  · exact B465447
  · exact B465451
  · exact B465455
  · exact B465459
  · exact B465463
  · exact B465467
  · exact B465471
  · exact B465475
  · exact B465479
  · exact B465483
  · exact B465487
  · exact B465491
  · exact B465495
  · exact B465499
  · exact B465503
  · exact B465507
  · exact B465511
  · exact B465515
  · exact B465519
  · exact B465523
  · exact B465527
  · exact B465531
  · exact B465535
  · exact B465539
  · exact B465543
  · exact B465547
  · exact B465551
  · exact B465555
  · exact B465559
  · exact B465563
  · exact B465567
  · exact B465571
  · exact B465575
  · exact B465579
  · exact B465583
  · exact B465587
  · exact B465591
  · exact B465595
  · exact B465599
  · exact B465603
  · exact B465607
  · exact B465611
  · exact B465615
  · exact B465619
  · exact B465623
  · exact B465627
  · exact B465631
  · exact B465635
  · exact B465639
  · exact B465643
  · exact B465647
  · exact B465651
  · exact B465655
  · exact B465659
  · exact B465663
  · exact B465667
  · exact B465671
  · exact B465675
  · exact B465679
  · exact B465683
  · exact B465687
  · exact B465691
  · exact B465695
  · exact B465699
  · exact B465703
  · exact B465707
  · exact B465711
  · exact B465715
  · exact B465719
  · exact B465723
  · exact B465727
  · exact B465731
  · exact B465735
  · exact B465739
  · exact B465743
  · exact B465747
  · exact B465751
  · exact B465755
  · exact B465759
  · exact B465763
  · exact B465767
  · exact B465771
  · exact B465775
  · exact B465779
  · exact B465783
  · exact B465787
  · exact B465791
  · exact B465795
  · exact B465799
  · exact B465803
  · exact B465807
  · exact B465811
  · exact B465815
  · exact B465819
  · exact B465823
  · exact B465827
  · exact B465831
  · exact B465835
  · exact B465839
  · exact B465843
  · exact B465847
  · exact B465851
  · exact B465855
  · exact B465859
  · exact B465863
  · exact B465867
  · exact B465871
  · exact B465875
  · exact B465879
  · exact B465883
  · exact B465887
  · exact B465891
  · exact B465895
  · exact B465899
  · exact B465903
  · exact B465907
  · exact B465911
  · exact B465915
  · exact B465919
  · exact B465923
  · exact B465927
  · exact B465931
  · exact B465935
  · exact B465939
  · exact B465943
  · exact B465947
  · exact B465951
  · exact B465955
  · exact B465959
  · exact B465963
  · exact B465967
  · exact B465971
  · exact B465975
  · exact B465979
  · exact B465983
  · exact B465987
  · exact B465991
  · exact B465995
  · exact B465999
  · exact B466003
  · exact B466007
  · exact B466011
  · exact B466015
  · exact B466019
  · exact B466023
  · exact B466027
  · exact B466031
  · exact B466035
  · exact B466039
  · exact B466043
  · exact B466047
  · exact B466051
  · exact B466055
  · exact B466059
  · exact B466063
  · exact B466067
  · exact B466071
  · exact B466075
  · exact B466079
  · exact B466083
  · exact B466087
  · exact B466091
  · exact B466095
  · exact B466099
  · exact B466103
  · exact B466107
  · exact B466111
  · exact B466115
  · exact B466119
  · exact B466123
  · exact B466127
  · exact B466131
  · exact B466135
  · exact B466139
  · exact B466143
  · exact B466147
  · exact B466151
  · exact B466155
  · exact B466159
  · exact B466163
  · exact B466167
  · exact B466171
  · exact B466175
  · exact B466179
  · exact B466183
  · exact B466187
  · exact B466191
  · exact B466195
  · exact B466199
  · exact B466203
  · exact B466207
  · exact B466211
  · exact B466215
  · exact B466219
  · exact B466223
  · exact B466227
  · exact B466231
  · exact B466235
  · exact B466239
  · exact B466243
  · exact B466247
  · exact B466251
  · exact B466255
  · exact B466259
  · exact B466263
  · exact B466267
  · exact B466271
  · exact B466275
  · exact B466279
  · exact B466283
  · exact B466287
  · exact B466291
  · exact B466295
  · exact B466299
  · exact B466303
  · exact B466307
  · exact B466311
  · exact B466315
  · exact B466319
  · exact B466323
  · exact B466327
  · exact B466331
  · exact B466335
  · exact B466339
  · exact B466343
  · exact B466347
  · exact B466351
  · exact B466355
  · exact B466359
  · exact B466363
  · exact B466367
  · exact B466371
  · exact B466375
  · exact B466379
  · exact B466383
  · exact B466387
  · exact B466391
  · exact B466395
  · exact B466399
  · exact B466403
  · exact B466407
  · exact B466411
  · exact B466415
  · exact B466419
  · exact B466423
  · exact B466427
  · exact B466431
  · exact B466435
  · exact B466439
  · exact B466443
  · exact B466447
  · exact B466451
  · exact B466455
  · exact B466459
  · exact B466463
  · exact B466467
  · exact B466471
  · exact B466475
  · exact B466479
  · exact B466483
  · exact B466487
  · exact B466491
  · exact B466495
  · exact B466499
  · exact B466503
  · exact B466507
  · exact B466511
  · exact B466515
  · exact B466519
  · exact B466523
  · exact B466527
  · exact B466531
  · exact B466535
  · exact B466539
  · exact B466543
  · exact B466547
  · exact B466551
  · exact B466555
  · exact B466559
  · exact B466563
  · exact B466567
  · exact B466571
  · exact B466575
  · exact B466579
  · exact B466583

theorem C1 (j : ℕ) (h1 : 116646 ≤ j) (h2 : j ≤ 116945) : Blo 463784 (4 * j + 3) := by
  interval_cases j
  · exact B466587
  · exact B466591
  · exact B466595
  · exact B466599
  · exact B466603
  · exact B466607
  · exact B466611
  · exact B466615
  · exact B466619
  · exact B466623
  · exact B466627
  · exact B466631
  · exact B466635
  · exact B466639
  · exact B466643
  · exact B466647
  · exact B466651
  · exact B466655
  · exact B466659
  · exact B466663
  · exact B466667
  · exact B466671
  · exact B466675
  · exact B466679
  · exact B466683
  · exact B466687
  · exact B466691
  · exact B466695
  · exact B466699
  · exact B466703
  · exact B466707
  · exact B466711
  · exact B466715
  · exact B466719
  · exact B466723
  · exact B466727
  · exact B466731
  · exact B466735
  · exact B466739
  · exact B466743
  · exact B466747
  · exact B466751
  · exact B466755
  · exact B466759
  · exact B466763
  · exact B466767
  · exact B466771
  · exact B466775
  · exact B466779
  · exact B466783
  · exact B466787
  · exact B466791
  · exact B466795
  · exact B466799
  · exact B466803
  · exact B466807
  · exact B466811
  · exact B466815
  · exact B466819
  · exact B466823
  · exact B466827
  · exact B466831
  · exact B466835
  · exact B466839
  · exact B466843
  · exact B466847
  · exact B466851
  · exact B466855
  · exact B466859
  · exact B466863
  · exact B466867
  · exact B466871
  · exact B466875
  · exact B466879
  · exact B466883
  · exact B466887
  · exact B466891
  · exact B466895
  · exact B466899
  · exact B466903
  · exact B466907
  · exact B466911
  · exact B466915
  · exact B466919
  · exact B466923
  · exact B466927
  · exact B466931
  · exact B466935
  · exact B466939
  · exact B466943
  · exact B466947
  · exact B466951
  · exact B466955
  · exact B466959
  · exact B466963
  · exact B466967
  · exact B466971
  · exact B466975
  · exact B466979
  · exact B466983
  · exact B466987
  · exact B466991
  · exact B466995
  · exact B466999
  · exact B467003
  · exact B467007
  · exact B467011
  · exact B467015
  · exact B467019
  · exact B467023
  · exact B467027
  · exact B467031
  · exact B467035
  · exact B467039
  · exact B467043
  · exact B467047
  · exact B467051
  · exact B467055
  · exact B467059
  · exact B467063
  · exact B467067
  · exact B467071
  · exact B467075
  · exact B467079
  · exact B467083
  · exact B467087
  · exact B467091
  · exact B467095
  · exact B467099
  · exact B467103
  · exact B467107
  · exact B467111
  · exact B467115
  · exact B467119
  · exact B467123
  · exact B467127
  · exact B467131
  · exact B467135
  · exact B467139
  · exact B467143
  · exact B467147
  · exact B467151
  · exact B467155
  · exact B467159
  · exact B467163
  · exact B467167
  · exact B467171
  · exact B467175
  · exact B467179
  · exact B467183
  · exact B467187
  · exact B467191
  · exact B467195
  · exact B467199
  · exact B467203
  · exact B467207
  · exact B467211
  · exact B467215
  · exact B467219
  · exact B467223
  · exact B467227
  · exact B467231
  · exact B467235
  · exact B467239
  · exact B467243
  · exact B467247
  · exact B467251
  · exact B467255
  · exact B467259
  · exact B467263
  · exact B467267
  · exact B467271
  · exact B467275
  · exact B467279
  · exact B467283
  · exact B467287
  · exact B467291
  · exact B467295
  · exact B467299
  · exact B467303
  · exact B467307
  · exact B467311
  · exact B467315
  · exact B467319
  · exact B467323
  · exact B467327
  · exact B467331
  · exact B467335
  · exact B467339
  · exact B467343
  · exact B467347
  · exact B467351
  · exact B467355
  · exact B467359
  · exact B467363
  · exact B467367
  · exact B467371
  · exact B467375
  · exact B467379
  · exact B467383
  · exact B467387
  · exact B467391
  · exact B467395
  · exact B467399
  · exact B467403
  · exact B467407
  · exact B467411
  · exact B467415
  · exact B467419
  · exact B467423
  · exact B467427
  · exact B467431
  · exact B467435
  · exact B467439
  · exact B467443
  · exact B467447
  · exact B467451
  · exact B467455
  · exact B467459
  · exact B467463
  · exact B467467
  · exact B467471
  · exact B467475
  · exact B467479
  · exact B467483
  · exact B467487
  · exact B467491
  · exact B467495
  · exact B467499
  · exact B467503
  · exact B467507
  · exact B467511
  · exact B467515
  · exact B467519
  · exact B467523
  · exact B467527
  · exact B467531
  · exact B467535
  · exact B467539
  · exact B467543
  · exact B467547
  · exact B467551
  · exact B467555
  · exact B467559
  · exact B467563
  · exact B467567
  · exact B467571
  · exact B467575
  · exact B467579
  · exact B467583
  · exact B467587
  · exact B467591
  · exact B467595
  · exact B467599
  · exact B467603
  · exact B467607
  · exact B467611
  · exact B467615
  · exact B467619
  · exact B467623
  · exact B467627
  · exact B467631
  · exact B467635
  · exact B467639
  · exact B467643
  · exact B467647
  · exact B467651
  · exact B467655
  · exact B467659
  · exact B467663
  · exact B467667
  · exact B467671
  · exact B467675
  · exact B467679
  · exact B467683
  · exact B467687
  · exact B467691
  · exact B467695
  · exact B467699
  · exact B467703
  · exact B467707
  · exact B467711
  · exact B467715
  · exact B467719
  · exact B467723
  · exact B467727
  · exact B467731
  · exact B467735
  · exact B467739
  · exact B467743
  · exact B467747
  · exact B467751
  · exact B467755
  · exact B467759
  · exact B467763
  · exact B467767
  · exact B467771
  · exact B467775
  · exact B467779
  · exact B467783

theorem solution (m : ℕ) (hlo : 463784 ≤ m) (hhi : m ≤ 467784) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 115946 ≤ j := by omega
    have hj2 : j ≤ 116945 := by omega
    have hb : Blo 463784 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 116646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
